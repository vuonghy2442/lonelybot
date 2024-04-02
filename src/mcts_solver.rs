use rand::RngCore;

use crate::{
    engine::{Encode, Move, Solitaire},
    hop_solver::hop_solve_game,
    tracking::SearchSignal,
    traverse::{traverse_game, TpTable, TraverseCallback, TraverseResult},
};

extern crate alloc;
use alloc::vec::Vec;

struct FindStatesCallback {
    his: Vec<Move>,
    found: bool,
    state: Encode,
    skipped: bool,
}

impl TraverseCallback for FindStatesCallback {
    fn on_win(&mut self, _: &Solitaire, _: &Option<Move>) -> TraverseResult {
        self.found = true;
        TraverseResult::Halted
    }

    fn on_visit(&mut self, _: &Solitaire, e: Encode) -> TraverseResult {
        if self.state == e {
            self.found = true;
            TraverseResult::Halted
        } else if self.skipped {
            TraverseResult::Skip
        } else {
            TraverseResult::Ok
        }
    }

    fn on_move_gen(&mut self, _: &crate::engine::MoveVec, _: Encode) {}

    fn on_do_move(&mut self, _: &Solitaire, m: &Move, _: Encode, rev: &Option<Move>) {
        self.his.push(*m);
        self.skipped = rev.is_none();
    }

    fn on_undo_move(&mut self, _: &Move, _: Encode) {
        if !self.found {
            self.his.pop();
        }
    }

    fn on_start(&mut self) {}

    fn on_finish(&mut self, _: &TraverseResult) {}
}

struct ListStatesCallback {
    res: Vec<(Encode, Move)>,
    skipped: bool,
}

impl TraverseCallback for ListStatesCallback {
    fn on_win(&mut self, g: &Solitaire, _: &Option<Move>) -> TraverseResult {
        self.res.clear();
        self.res.push((g.encode(), Move::FAKE));
        TraverseResult::Halted
    }

    fn on_visit(&mut self, _: &Solitaire, _: Encode) -> TraverseResult {
        if self.skipped {
            TraverseResult::Skip
        } else {
            TraverseResult::Ok
        }
    }

    fn on_move_gen(&mut self, _: &crate::engine::MoveVec, _: Encode) {}

    fn on_do_move(&mut self, _: &Solitaire, m: &Move, e: Encode, rev: &Option<Move>) {
        // if rev.is_none() && matches!(m, Move::Reveal(_) | Move::PileStack(_)) {
        if rev.is_none() {
            self.skipped = true;
            self.res.push((e, *m));
        } else {
            self.skipped = false;
        }
    }

    fn on_undo_move(&mut self, _: &Move, _: Encode) {}

    fn on_start(&mut self) {}

    fn on_finish(&mut self, _: &TraverseResult) {}
}

pub fn mcts_moves_game<R: RngCore, T: SearchSignal>(
    g: &mut Solitaire,
    rng: &mut R,
    n_times: usize,
    limit: usize,
    sign: &T,
) -> Option<Vec<Move>> {
    const BATCH_SIZE: usize = 10;
    const C: f64 = 0.5;

    let mut callback = ListStatesCallback {
        res: Vec::default(),
        skipped: false,
    };

    let mut tp = TpTable::default();
    traverse_game(g, &mut tp, &mut callback, None);
    let states = callback.res;

    let mut org_g = g.clone();

    let mut find_state = move |state: (Encode, Move)| {
        let mut callback = FindStatesCallback {
            his: Vec::default(),
            state: state.0,
            skipped: false,
            found: false,
        };
        tp.clear();

        traverse_game(&mut org_g, &mut tp, &mut callback, None);
        if state.1 != Move::FAKE {
            callback.his.push(state.1);
        }
        callback.his
    };

    if states.len() <= 1 {
        return states.last().map(|state| find_state(*state));
    }

    let mut res: Vec<(usize, usize, usize)> = Vec::with_capacity(states.len());
    res.resize_with(states.len(), Default::default);

    let mut n = 0;
    loop {
        // here pick the best :)
        let best = res
            .iter()
            .map(|x| {
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
        g.decode(state.0);
        let new_res = hop_solve_game(g, &state.1, rng, BATCH_SIZE, limit, sign, None);

        n += BATCH_SIZE;

        res[best].0 += new_res.0;
        res[best].1 += new_res.1;
        res[best].2 += new_res.2;

        if res[best].2 > n_times {
            return Some(find_state(*state));
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
