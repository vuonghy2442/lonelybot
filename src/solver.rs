use crate::{
    moves::Move,
    pruning::{CyclePruner, FullPruner, Pruner},
    state::{Encode, Solitaire},
    tracking::{DefaultTerminateSignal, EmptySearchStats, SearchStatistics, TerminateSignal},
    traverse::{traverse, Callback, Control, TpTable},
};
use arrayvec::ArrayVec;
use core::marker::PhantomData;

// before every progress you'd do at most 2*N_RANKS move
// and there would only be N_FULL_DECK + N_HIDDEN progress step
const N_PLY_MAX: usize = 1024;

pub type HistoryVec = ArrayVec<Move, N_PLY_MAX>;

#[derive(Debug, PartialEq, Eq)]
pub enum SearchResult {
    Terminated,
    Solved,
    Unsolvable,
    Crashed,
}

struct SolverCallback<'a, S: SearchStatistics, T: TerminateSignal, P: Pruner> {
    history: HistoryVec,
    stats: &'a S,
    sign: &'a T,
    result: SearchResult,
    marker: PhantomData<P>,
}

impl<S: SearchStatistics, T: TerminateSignal, P: Pruner> Callback for SolverCallback<'_, S, T, P> {
    type Pruner = P;
    fn on_win(&mut self, _: &Solitaire) -> Control {
        self.result = SearchResult::Solved;
        Control::Halt
    }

    fn on_visit(&mut self, _: &Solitaire, _: Encode) -> Control {
        if self.sign.is_terminated() {
            self.result = SearchResult::Terminated;
            return Control::Halt;
        }

        self.stats.hit_a_state(self.history.len());
        Control::Ok
    }

    fn on_move_gen(&mut self, m: &crate::moves::MoveMask, _: Encode) -> Control {
        self.stats.hit_unique_state(self.history.len(), m.len());
        Control::Ok
    }

    fn on_do_move(&mut self, _: &Solitaire, m: Move, _: Encode, _: &P) -> Control {
        self.history.push(m);
        Control::Ok
    }

    fn on_undo_move(&mut self, _: Move, _: Encode, res: &Control) {
        if *res == Control::Ok {
            self.history.pop();
        }
        self.stats.finish_move(self.history.len());
    }
}

fn solve_with<S: SearchStatistics, T: TerminateSignal, P: Pruner + Default>(
    game: &mut Solitaire,
    stats: &S,
    sign: &T,
) -> (SearchResult, Option<HistoryVec>) {
    let mut tp = TpTable::default();

    let mut callback = SolverCallback {
        history: HistoryVec::new(),
        stats,
        sign,
        result: SearchResult::Unsolvable,
        marker: PhantomData,
    };

    traverse(game, &P::default(), &mut tp, &mut callback);

    let result = callback.result;

    if result == SearchResult::Solved {
        (result, Some(callback.history))
    } else {
        (result, None)
    }
}

/// The safe default: only the reversible-cycle filter runs, so the search
/// explores every move the dominance generator offers, and an `Unsolvable`
/// verdict does not depend on the path taken to reach a state.
pub fn solve_with_tracking<S: SearchStatistics, T: TerminateSignal>(
    game: &mut Solitaire,
    stats: &S,
    sign: &T,
) -> (SearchResult, Option<HistoryVec>) {
    solve_with::<S, T, CyclePruner>(game, stats, sign)
}

/// `solve_with_tracking` with the aggressive pruner: faster, but the
/// path-dependent rules (reveal-context, last-draw streak) can wrongly
/// refute winnable games, as in issue #15.
pub fn solve_risky_with_tracking<S: SearchStatistics, T: TerminateSignal>(
    game: &mut Solitaire,
    stats: &S,
    sign: &T,
) -> (SearchResult, Option<HistoryVec>) {
    solve_with::<S, T, FullPruner>(game, stats, sign)
}

pub fn solve(game: &mut Solitaire) -> (SearchResult, Option<HistoryVec>) {
    solve_with_tracking(game, &EmptySearchStats {}, &DefaultTerminateSignal {})
}

/// `solve` with the aggressive pruner — see `solve_risky_with_tracking`.
pub fn solve_risky(game: &mut Solitaire) -> (SearchResult, Option<HistoryVec>) {
    solve_risky_with_tracking(game, &EmptySearchStats {}, &DefaultTerminateSignal {})
}
