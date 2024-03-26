use crate::{
    engine::{Encode, Move, Solitaire},
    tracking::{DefaultSearchSignal, EmptySearchStats, SearchSignal, SearchStatistics},
    traverse::{traverse_game, GraphCallback, TpTable, TraverseResult},
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

struct SolverCallback<'a, S: SearchStatistics, T: SearchSignal> {
    history: HistoryVec,
    stats: &'a S,
    sign: &'a T,
    result: SearchResult,
}

impl<'a, S: SearchStatistics, T: SearchSignal> GraphCallback for SolverCallback<'a, S, T> {
    fn on_win(&mut self, _: &Solitaire, _: &Option<Move>) -> TraverseResult {
        self.result = SearchResult::Solved;
        TraverseResult::Halted
    }

    fn on_visit(&mut self, _: &Solitaire, _: Encode) -> TraverseResult {
        if self.sign.is_terminated() {
            self.result = SearchResult::Terminated;
            return TraverseResult::Halted;
        }

        self.stats.hit_a_state(self.history.len());
        TraverseResult::Ok
    }

    fn on_move_gen(&mut self, m: &crate::engine::MoveVec, _: Encode) {
        self.stats.hit_unique_state(self.history.len(), m.len());
    }

    fn on_do_move(&mut self, _: &Solitaire, m: &Move, _: Encode, _: &Option<Move>) {
        self.history.push(*m);
    }

    fn on_undo_move(&mut self, _: &Move, _: Encode) {
        if self.result != SearchResult::Solved {
            self.history.pop();
        }
        self.stats.finish_move(self.history.len());
    }

    fn on_start(&mut self) {}

    fn on_finish(&mut self, _: &TraverseResult) {
        self.sign.search_finish();
    }
}

pub fn solve_game_with_tracking(
    g: &mut Solitaire,
    stats: &impl SearchStatistics,
    sign: &impl SearchSignal,
) -> (SearchResult, Option<HistoryVec>) {
    let mut tp = TpTable::default();

    let mut callback = SolverCallback {
        history: HistoryVec::new(),
        stats,
        sign,
        result: SearchResult::Unsolvable,
    };

    traverse_game(g, &mut tp, &mut callback, None);
    let result = callback.result;

    if result == SearchResult::Solved {
        (result, Some(callback.history))
    } else {
        (result, None)
    }
}

pub fn solve_game(g: &mut Solitaire) -> (SearchResult, Option<HistoryVec>) {
    solve_game_with_tracking(g, &EmptySearchStats {}, &DefaultSearchSignal {})
}
