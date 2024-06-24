use rand::RngCore;

use crate::{
    hop_solver::hop_solve_game,
    moves::Move,
    pruning::FullPruner,
    state::{Encode, Solitaire},
    tracking::TerminateSignal,
    traverse::{traverse, Callback, Control, TpTable},
};

extern crate alloc;
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

    fn on_do_move(
        &mut self,
        g: &Solitaire,
        m: Move,
        _: Encode,
        prune_info: &FullPruner,
    ) -> Control {
        let rev = prune_info.rev_move();
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

    fn on_do_move(
        &mut self,
        _: &Solitaire,
        m: Move,
        e: Encode,
        prune_info: &FullPruner,
    ) -> Control {
        let rev = prune_info.rev_move();
        // if rev.is_none() && matches!(m, Move::Reveal(_) | Move::PileStack(_)) {
        if rev.is_none() {
            self.res.push((e, Some(m)));
            Control::Skip
        } else {
            Control::Ok
        }
    }
}

/// Picking the best move using MCTS
///
/// # Panics
///
/// Maybe out of memory. Otherwise should not panic
pub fn pick_moves<R: RngCore, T: TerminateSignal>(
    game: &mut Solitaire,
    rng: &mut R,
    n_times: usize,
    limit: usize,
    sign: &T,
) -> Option<Vec<Move>> {
    const BATCH_SIZE: usize = 10;
    const C: f64 = 0.5;

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

    if states.len() <= 1 {
        return states.last().map(|state| find_state(state.0, state.1));
    }

    let mut res: Vec<(usize, usize, usize)> = Vec::with_capacity(states.len());
    res.resize_with(states.len(), Default::default);

    let mut n = 0;
    loop {
        // here pick the best :)
        let best = res
            .iter()
            .map(|x| {
                #[allow(clippy::cast_precision_loss)]
                if x.2 == 0 {
                    f64::INFINITY
                } else {
                    x.0 as f64 / x.2 as f64 + C * ((n as f64).ln() / (x.2) as f64).sqrt()
                }
            })
            .enumerate()
            .max_by(|a, b| a.1.partial_cmp(&b.1).unwrap())
            .map(|x| x.0)
            .unwrap();

        let state = &states[best];

        //test
        game.decode(state.0);
        let new_res = hop_solve_game(
            game,
            state.1.unwrap(),
            rng,
            BATCH_SIZE,
            limit,
            sign,
            &FullPruner::default(),
        );

        n += BATCH_SIZE;

        res[best].0 += new_res.0;
        res[best].1 += new_res.1;
        res[best].2 += new_res.2;

        if res[best].2 > n_times {
            return Some(find_state(state.0, state.1));
        }

        // let &(win, _skip, max_n) = res.iter().max_by_key(|x| x.2).unwrap();

        // const ALPHA: f64 = 2.0;
        // const BETA: f64 = 2.0;

        // let var = {
        //     let alpha = ALPHA + win as f64;
        //     let beta = BETA + (max_n - win) as f64;
        //     alpha * beta / ((alpha + beta).powi(2) * (alpha + beta + 1.0))
        // };

        // if 4.0 * var * (n_times as f64) < 1.0 {
        //     break;
        // }
    }
}
