use rand::RngCore;

use crate::{
    engine::{Encode, Move, Solitaire},
    solver::SearchResult,
    tracking::SearchSignal,
    traverse::{traverse_game, TpTable, TraverseCallback, TraverseResult},
};

struct HOPSolverCallback<'a, T: SearchSignal> {
    sign: &'a T,
    result: SearchResult,
    limit: usize,
    n_visit: usize,
}

impl<'a, T: SearchSignal> TraverseCallback for HOPSolverCallback<'a, T> {
    fn on_win(&mut self, _: &Solitaire, _: &Option<Move>) -> TraverseResult {
        self.result = SearchResult::Solved;
        TraverseResult::Halted
    }

    fn on_visit(&mut self, g: &Solitaire, _: Encode) -> TraverseResult {
        if g.is_sure_win() {
            self.result = SearchResult::Solved;
            return TraverseResult::Halted;
        }

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

pub fn hop_solve_game<R: RngCore, T: SearchSignal>(
    g: &Solitaire,
    m: &Move,
    rng: &mut R,
    n_times: usize,
    limit: usize,
    sign: &T,
    rev_move: Option<Move>,
) -> (usize, usize, usize) {
    let mut total_wins = 0;
    let mut total_skips = 0;
    let mut total_played = 0;

    let mut tp = TpTable::default();

    // check if determinize
    let total_hidden: u8 = g.get_hidden().total_down_cards();
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
        gg.get_hidden_mut().shuffle(rng);
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

impl<'a, R: RngCore, S: SearchSignal> TraverseCallback for RevStatesCallback<'a, R, S> {
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

pub fn hop_moves_game<R: RngCore, T: SearchSignal>(
    g: &mut Solitaire,
    rng: &mut R,
    n_times: usize,
    limit: usize,
    sign: &T,
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
