use crate::{
    engine::{Encode, Move, Solitaire},
    pruning::PruneInfo,
    tracking::{DefaultTerminateSignal, EmptySearchStats, SearchStatistics, TerminateSignal},
    traverse::{traverse, Callback, ControlFlow, TpTable},
};
use arrayvec::ArrayVec;

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

struct SolverCallback<'a, S: SearchStatistics, T: TerminateSignal> {
    history: HistoryVec,
    stats: &'a S,
    sign: &'a T,
    result: SearchResult,
}

impl<'a, S: SearchStatistics, T: TerminateSignal> Callback for SolverCallback<'a, S, T> {
    fn on_win(&mut self, _: &Solitaire) -> ControlFlow {
        self.result = SearchResult::Solved;
        ControlFlow::Halt
    }

    fn on_visit(&mut self, _: &Solitaire, _: Encode) -> ControlFlow {
        if self.sign.is_terminated() {
            self.result = SearchResult::Terminated;
            return ControlFlow::Halt;
        }

        self.stats.hit_a_state(self.history.len());
        ControlFlow::Ok
    }

    fn on_move_gen(&mut self, m: &crate::engine::MoveVec, _: Encode) -> ControlFlow {
        self.stats.hit_unique_state(self.history.len(), m.len());
        ControlFlow::Ok
    }

    fn on_do_move(&mut self, _: &Solitaire, m: &Move, _: Encode, _: &PruneInfo) -> ControlFlow {
        self.history.push(*m);
        ControlFlow::Ok
    }

    fn on_undo_move(&mut self, _: &Move, _: Encode, res: &ControlFlow) {
        if *res == ControlFlow::Ok {
            self.history.pop();
        }
        self.stats.finish_move(self.history.len());
    }
}

pub fn solve_with_tracking<S: SearchStatistics, T: TerminateSignal>(
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
    };

    traverse(game, &PruneInfo::default(), &mut tp, &mut callback);

    let result = callback.result;

    if result == SearchResult::Solved {
        (result, Some(callback.history))
    } else {
        (result, None)
    }
}

pub fn solve(game: &mut Solitaire) -> (SearchResult, Option<HistoryVec>) {
    solve_with_tracking(game, &EmptySearchStats {}, &DefaultTerminateSignal {})
}
