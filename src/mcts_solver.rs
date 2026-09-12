use rand::Rng;

use crate::{
    hop_solver::{hop_solve_game, is_sure_lose, is_sure_win, HopResult},
    moves::Move,
    pruning::FullPruner,
    state::{Encode, Solitaire},
    tracking::TerminateSignal,
    traverse::{traverse, Callback, Control, TpTable},
};

extern crate alloc;
use alloc::vec;
use alloc::vec::Vec;

struct FindStatesCallback {
    his: Vec<Move>,
    state: Encode,
}

impl Callback for FindStatesCallback {
    type Pruner = FullPruner;
    fn on_win(&mut self, _: &Solitaire) -> Control {
        Control::Halt
    }

    fn on_visit(&mut self, _: &Solitaire, e: Encode) -> Control {
        if self.state == e {
            Control::Halt
        } else {
            Control::Ok
        }
    }

    fn on_do_move(&mut self, g: &Solitaire, m: Move, _: Encode, _: &FullPruner) -> Control {
        // the move itself must be undoable in one move to be part of a path
        let rev = g.reverse_move(m);
        let ok = match m {
            Move::Reveal(c) => c.mask() & g.get_hidden().first_layer_mask() == 0,
            _ => true,
        };

        if rev.is_none() && ok {
            Control::Skip
        } else {
            self.his.push(m);
            Control::Ok
        }
    }

    fn on_undo_move(&mut self, _: Move, _: Encode, res: &Control) {
        if *res == Control::Ok {
            self.his.pop();
        }
    }
}

struct ListStatesCallback {
    res: Vec<(Encode, Option<Move>)>,
}

impl Callback for ListStatesCallback {
    type Pruner = FullPruner;
    fn on_win(&mut self, game: &Solitaire) -> Control {
        self.res.clear();
        self.res.push((game.encode(), None));
        Control::Halt
    }

    fn on_do_move(&mut self, g: &Solitaire, m: Move, e: Encode, _: &FullPruner) -> Control {
        // a candidate is an irreversible move: doing it commits the game, so
        // the search stops there and the MCTS evaluates it separately.
        // (checking the arrival move here, like `pr.rev_move()` did, collapses
        // the enumeration to the root moves only)
        let rev = g.reverse_move(m);
        if rev.is_none() {
            self.res.push((e, Some(m)));
            Control::Skip
        } else {
            Control::Ok
        }
    }
}

pub type PotentialFn = fn(&HopResult, usize) -> f64;

/// Picking the best move using MCTS
///
/// # Panics
///
/// Maybe out of memory. Otherwise should not panic
pub fn pick_moves<R: Rng, T: TerminateSignal>(
    game: &mut Solitaire,
    rng: &mut R,
    n_times: usize,
    limit: usize,
    sign: &T,
    pot_fn: PotentialFn,
) -> Option<Vec<Move>> {
    const BATCH_SIZE: usize = 10;

    let mut callback = ListStatesCallback {
        res: Vec::default(),
    };

    let mut tp = TpTable::default();
    traverse(game, &FullPruner::default(), &mut tp, &mut callback);
    let states = callback.res;

    let mut org_g = game.clone();

    let mut find_state = move |state: Encode, m: Option<Move>| {
        let mut callback = FindStatesCallback {
            his: Vec::default(),
            state,
        };
        tp.clear();

        traverse(&mut org_g, &FullPruner::default(), &mut tp, &mut callback);
        if let Some(m) = m {
            callback.his.push(m);
        }
        callback.his
    };

    // the only candidate without a move is a state that already wins the
    // game within the reversible closure: no commit is needed at all
    if let Some(&(state, None)) = states.first() {
        return Some(find_state(state, None));
    }

    if states.len() <= 1 {
        // a single candidate leaves no choice: evaluating it cannot change
        // the decision, so return its path directly (this also covers the
        // no-candidate case, which means the game is lost)
        return states.last().map(|state| find_state(state.0, state.1));
    }

    let mut res: Vec<HopResult> = vec![HopResult::default(); states.len()];

    let mut n = 0;
    loop {
        // a candidate proven to win in every hidden arrangement: committing
        // it is optimal, stop the search right away
        if let Some(i) = res.iter().position(is_sure_win) {
            let (state, m) = states[i];
            return Some(find_state(state, m));
        }

        // pick the next candidate to evaluate; exhaustively evaluated
        // candidates are finished, never sample them again
        let best = (0..states.len())
            .filter(|&i| !res[i].exhaustive)
            .map(|i| (i, pot_fn(&res[i], n)))
            .max_by(|a, b| a.1.partial_cmp(&b.1).unwrap())
            .map(|x| x.0);

        let Some(best) = best else {
            // every candidate was evaluated exactly
            if res.iter().all(is_sure_lose) {
                // every commit loses in every arrangement: the game is lost
                return None;
            }
            // otherwise fall back to the best exact value
            let best = (0..states.len())
                .max_by(|a, b| res[*a].rate().partial_cmp(&res[*b].rate()).unwrap())
                .unwrap();
            let (state, m) = states[best];
            return Some(find_state(state, m));
        };

        let state = &states[best];

        //test
        game.decode(state.0);
        let new_res = hop_solve_game(
            game,
            state.1.unwrap(),
            rng,
            BATCH_SIZE,
            limit,
            n_times * limit,
            sign,
            &FullPruner::default(),
        );

        if new_res.played == 0 {
            // no playout finished (e.g. the search was terminated): return
            // the current plan instead of spinning forever
            return Some(find_state(state.0, state.1));
        }

        n += new_res.played;
        res[best] += new_res;

        #[cfg(feature = "hop_debug")]
        {
            extern crate std;
            std::eprintln!(
                "hopdbg buried={:>2} arms={:>2} sel wins={:>4} skips={:>4} played={:>5}",
                game.get_hidden().total_down_cards(),
                states.len(),
                res[best].wins,
                res[best].skips,
                res[best].played,
            );
        }

        if res[best].played > n_times {
            return Some(find_state(state.0, state.1));
        }
    }
}
