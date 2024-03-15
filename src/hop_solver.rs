use rand::RngCore;

use crate::{
    engine::{Encode, Move, Solitaire},
    solver::SearchResult,
    tracking::SearchSignal,
    traverse::{traverse_game, GraphCallback, TpTable, TraverseResult},
};

struct HOPSolverCallback<'a, T: SearchSignal> {
    sign: &'a T,
    result: SearchResult,
    limit: usize,
    n_visit: usize,
}

impl<'a, T: SearchSignal> GraphCallback for HOPSolverCallback<'a, T> {
    fn on_win(&mut self, _: &Solitaire, _: &Option<Move>) -> TraverseResult {
        self.result = SearchResult::Solved;
        TraverseResult::Halted
    }

    fn on_visit(&mut self, _: &Solitaire, _: &Option<Move>, _: Encode) -> TraverseResult {
        if self.sign.is_terminated() {
            self.result = SearchResult::Terminated;
            return TraverseResult::Halted;
        }

        self.n_visit += 1;
        if self.n_visit > self.limit {
            self.result = SearchResult::Terminated;
            TraverseResult::Halted
        } else {
            TraverseResult::Ok
        }
    }

    fn on_move_gen(&mut self, _: &crate::engine::MoveVec, _: Encode) {}

    fn on_do_move(&mut self, _: usize, _: &Move, _: Encode) {}

    fn on_undo_move(&mut self, _: usize, _: &Move, _: Encode) {}

    fn on_start(&mut self) {}

    fn on_finish(&mut self, _: &TraverseResult) {
        self.sign.search_finish();
    }
}

pub fn hop_solve_game(
    g: &Solitaire,
    rng: &mut impl RngCore,
    n_times: usize,
    limit: usize,
    sign: &impl SearchSignal,
) -> (usize, usize, usize) {
    let mut total_wins = 0;
    let mut total_skips = 0;
    let mut total_played = 0;

    let mut tp = TpTable::with_hasher(Default::default());

    // check if determinize
    let total_hidden: u8 = g.get_n_hidden().map(|x| x.saturating_sub(1)).iter().sum();
    if total_hidden <= 1 {
        // totally determinized
        let res = crate::solver::solve_game(&mut g.clone()).0;
        return if res == SearchResult::Solved {
            (!0, 0, !0)
        } else if res == SearchResult::Unsolvable {
            (0, 0, !0)
        } else {
            (0, !0, !0)
        };
    }

    for _ in 0..n_times {
        let mut gg = g.clone();
        gg.shuffle_hidden(rng);

        let mut callback = HOPSolverCallback {
            sign,
            result: SearchResult::Unsolvable,
            limit,
            n_visit: 0,
        };
        tp.clear();
        traverse_game(&mut gg, &mut tp, &mut callback);
        if sign.is_terminated() {
            break;
        }
        total_played += 1;
        let result = callback.result;
        match result {
            SearchResult::Solved => total_wins += 1,
            SearchResult::Terminated => total_skips += 1,
            _ => {}
        }
    }
    (total_wins, total_skips, total_played)
}

extern crate alloc;
use alloc::vec::Vec;

struct RevStatesCallback<'a, R: RngCore, S: SearchSignal> {
    his: Vec<Move>,
    rng: &'a mut R,
    n_times: usize,
    limit: usize,
    sign: &'a S,
    res: Vec<(Vec<Move>, (usize, usize, usize))>,
}

impl<'a, R: RngCore, S: SearchSignal> GraphCallback for RevStatesCallback<'a, R, S> {
    fn on_win(&mut self, _: &Solitaire, _: &Option<Move>) -> TraverseResult {
        self.res.push((self.his.clone(), (!0, 0, !0)));
        TraverseResult::Halted
    }

    fn on_visit(&mut self, g: &Solitaire, rev: &Option<Move>, _: Encode) -> TraverseResult {
        if rev.is_none() {
            self.res.push((
                self.his.clone(),
                hop_solve_game(g, self.rng, self.n_times, self.limit, self.sign),
            ));
            TraverseResult::Skip
        } else {
            TraverseResult::Ok
        }
    }

    fn on_move_gen(&mut self, _: &crate::engine::MoveVec, _: Encode) {}

    fn on_do_move(&mut self, _: usize, m: &Move, _: Encode) {
        self.his.push(*m);
    }

    fn on_undo_move(&mut self, _: usize, _: &Move, _: Encode) {
        self.his.pop();
    }

    fn on_start(&mut self) {}

    fn on_finish(&mut self, _: &TraverseResult) {}
}

pub fn hop_moves_game(
    g: &mut Solitaire,
    rng: &mut impl RngCore,
    n_times: usize,
    limit: usize,
    sign: &impl SearchSignal,
) -> Vec<(Vec<Move>, (usize, usize, usize))> {
    let mut callback = RevStatesCallback {
        his: Default::default(),
        rng,
        n_times,
        limit,
        sign,
        res: Default::default(),
    };

    let mut tp = TpTable::with_hasher(Default::default());
    traverse_game(g, &mut tp, &mut callback);
    callback.res
}
