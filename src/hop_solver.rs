use rand::RngCore;

use crate::{
    engine::{Encode, Move, Solitaire},
    pruning::PruneInfo,
    solver::SearchResult,
    tracking::TerminateSignal,
    traverse::{traverse, Callback, ControlFlow, TpTable},
};

struct HOPSolverCallback<'a, T: TerminateSignal> {
    sign: &'a T,
    result: SearchResult,
    limit: usize,
    n_visit: usize,
}

impl<'a, T: TerminateSignal> Callback for HOPSolverCallback<'a, T> {
    fn on_win(&mut self, _: &Solitaire) -> ControlFlow {
        self.result = SearchResult::Solved;
        ControlFlow::Halt
    }

    fn on_visit(&mut self, g: &Solitaire, _: Encode) -> ControlFlow {
        if g.is_sure_win() {
            self.result = SearchResult::Solved;
            return ControlFlow::Halt;
        }

        if self.sign.is_terminated() {
            self.result = SearchResult::Terminated;
            return ControlFlow::Halt;
        }

        self.n_visit += 1;
        if self.n_visit > self.limit {
            self.result = SearchResult::Terminated;
            ControlFlow::Halt
        } else {
            ControlFlow::Ok
        }
    }
}

pub fn hop_solve_game<R: RngCore, T: TerminateSignal>(
    g: &Solitaire,
    m: &Move,
    rng: &mut R,
    n_times: usize,
    limit: usize,
    sign: &T,
    prune_info: &PruneInfo,
) -> (usize, usize, usize) {
    let mut total_wins = 0;
    let mut total_skips = 0;
    let mut total_played = 0;

    let mut tp = TpTable::default();

    // check if determinize
    let total_hidden: u8 = g.get_hidden().total_down_cards();
    if total_hidden <= 1 {
        // totally determinized
        let res = crate::solver::solve(&mut g.clone()).0;
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
        traverse(&mut gg, &prune_info, &mut tp, &mut callback);
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

struct RevStatesCallback<'a, R: RngCore, T: TerminateSignal> {
    his: Vec<Move>,
    rng: &'a mut R,
    n_times: usize,
    limit: usize,
    sign: &'a T,
    res: Vec<(Vec<Move>, (usize, usize, usize))>,
}

impl<'a, R: RngCore, T: TerminateSignal> Callback for RevStatesCallback<'a, R, T> {
    fn on_win(&mut self, _: &Solitaire) -> ControlFlow {
        self.res.push((self.his.clone(), (!0, 0, !0)));
        ControlFlow::Halt
    }

    fn on_do_move(
        &mut self,
        g: &Solitaire,
        m: &Move,
        _: Encode,
        prune_info: &PruneInfo,
    ) -> ControlFlow {
        self.his.push(*m);
        let rev = prune_info.rev_move();
        // if rev.is_none() && (matches!(m, Move::Reveal(_)) || matches!(m, Move::PileStack(_))) {
        if rev.is_none() {
            self.res.push((
                self.his.clone(),
                hop_solve_game(
                    g,
                    m,
                    self.rng,
                    self.n_times,
                    self.limit,
                    self.sign,
                    prune_info,
                ),
            ));
            ControlFlow::Skip
        } else {
            ControlFlow::Ok
        }
    }

    fn on_undo_move(&mut self, _: &Move, _: Encode, _: &ControlFlow) {
        self.his.pop();
    }
}

pub fn list_moves<R: RngCore, T: TerminateSignal>(
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
    };

    let mut tp = TpTable::default();
    traverse(g, &Default::default(), &mut tp, &mut callback);
    callback.res
}
