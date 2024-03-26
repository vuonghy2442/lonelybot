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

    fn on_visit(&mut self, _: &Solitaire, _: Encode) -> TraverseResult {
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

    fn on_do_move(&mut self, _: &Solitaire, _: &Move, _: Encode, _: &Option<Move>) {}

    fn on_undo_move(&mut self, _: &Move, _: Encode) {}

    fn on_start(&mut self) {}

    fn on_finish(&mut self, _: &TraverseResult) {
        self.sign.search_finish();
    }
}

pub fn hop_solve_game(
    g: &Solitaire,
    m: &Move,
    rng: &mut impl RngCore,
    n_times: usize,
    limit: usize,
    sign: &impl SearchSignal,
    rev_move: Option<Move>,
) -> (usize, usize, usize) {
    let mut total_wins = 0;
    let mut total_skips = 0;
    let mut total_played = 0;

    let mut tp = TpTable::default();

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
        gg.do_move(m);

        let mut callback = HOPSolverCallback {
            sign,
            result: SearchResult::Unsolvable,
            limit,
            n_visit: 0,
        };
        tp.clear();
        traverse_game(&mut gg, &mut tp, &mut callback, rev_move);
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
    skipped: bool,
}

impl<'a, R: RngCore, S: SearchSignal> GraphCallback for RevStatesCallback<'a, R, S> {
    fn on_win(&mut self, _: &Solitaire, _: &Option<Move>) -> TraverseResult {
        self.res.push((self.his.clone(), (!0, 0, !0)));
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

    fn on_do_move(&mut self, g: &Solitaire, m: &Move, _: Encode, rev: &Option<Move>) {
        self.his.push(*m);
        // if rev.is_none() && (matches!(m, Move::Reveal(_)) || matches!(m, Move::PileStack(_))) {
        if rev.is_none() {
            self.skipped = true;
            self.res.push((
                self.his.clone(),
                hop_solve_game(g, m, self.rng, self.n_times, self.limit, self.sign, None),
            ));
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

pub fn hop_moves_game(
    g: &mut Solitaire,
    rng: &mut impl RngCore,
    n_times: usize,
    limit: usize,
    sign: &impl SearchSignal,
) -> Vec<(Vec<Move>, (usize, usize, usize))> {
    let mut callback = RevStatesCallback {
        his: Vec::default(),
        rng,
        n_times,
        limit,
        sign,
        res: Vec::default(),
        skipped: false,
    };

    let mut tp = TpTable::default();
    traverse_game(g, &mut tp, &mut callback, None);
    callback.res
}
