use rand::RngCore;

use crate::{
    engine::{Encode, Move, Solitaire},
    hop_solver::hop_solve_game,
    tracking::SearchSignal,
    traverse::{traverse_game, GraphCallback, TpTable, TraverseResult},
};

extern crate alloc;
use alloc::vec::Vec;

struct ListStatesCallback {
    his: Vec<Move>,
    res: Vec<(Vec<Move>, Solitaire)>,
    skipped: bool,
}

impl GraphCallback for ListStatesCallback {
    fn on_win(&mut self, g: &Solitaire, _: &Option<Move>) -> TraverseResult {
        self.res.clear();
        self.res.push((self.his.clone(), g.clone()));
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

    fn on_do_move(&mut self, g: &Solitaire, m: &Move, _e: Encode, rev: &Option<Move>) {
        self.his.push(*m);
        // if rev.is_none() && matches!(m, Move::Reveal(_) | Move::PileStack(_)) {
        if rev.is_none() {
            self.skipped = true;
            self.res.push((self.his.clone(), g.clone()));
        } else {
            self.skipped = false;
        }
    }

    fn on_undo_move(&mut self, _: &Move, _: Encode) {
        self.his.pop();
    }

    fn on_start(&mut self) {}

    fn on_finish(&mut self, _: &TraverseResult) {}
}

pub fn mcts_moves_game(
    g: &mut Solitaire,
    rng: &mut impl RngCore,
    n_times: usize,
    limit: usize,
    sign: &impl SearchSignal,
) -> Option<Vec<Move>> {
    let mut callback = ListStatesCallback {
        his: Vec::default(),
        res: Vec::default(),
        skipped: false,
    };

    // let org_state = g.encode();

    let mut tp = TpTable::default();
    traverse_game(g, &mut tp, &mut callback, None);
    let states = callback.res;

    // println!("Nstates {}", states.len());

    if states.len() <= 1 {
        let mut states = states;
        return states.pop().map(|x| x.0);
    }

    let mut res: Vec<(usize, usize, usize)> = Vec::with_capacity(states.len());
    res.resize_with(states.len(), Default::default);

    // const C: f64 = 1.414;
    const C: f64 = 1.0;

    const BATCH_SIZE: usize = 10;

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
        // let code = state.1.encode();
        // g.decode(code);
        let new_res = hop_solve_game(
            // g,
            &state.1,
            state.0.last().unwrap(),
            rng,
            BATCH_SIZE,
            limit,
            sign,
            None,
        );

        n += BATCH_SIZE;

        res[best].0 += new_res.0;
        res[best].1 += new_res.1;
        res[best].2 += new_res.2;

        if res[best].2 > n_times {
            break;
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

    // print!("{:?}", res);

    // g.decode(org_state);

    res.iter()
        .zip(states)
        .max_by_key(|x| x.0 .2)
        .map(|x| x.1 .0)
}
