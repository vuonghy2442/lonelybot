use crate::{
    engine::{Encode, Move, Solitaire},
    tracking::{DefaultSearchSignal, EmptySearchStats, SearchSignal, SearchStatistics},
    traverse::{traverse_game, GraphCallback, TraverseResult},
};
use arrayvec::ArrayVec;
use quick_cache::{unsync::Cache, UnitWeighter};

pub type TpCache = Cache<Encode, (), UnitWeighter, nohash_hasher::BuildNoHashHasher<Encode>>;
impl crate::traverse::TranpositionTable for TpCache {
    fn insert(&mut self, value: Encode) -> bool {
        if self.get(&value).is_some() {
            false
        } else {
            self.insert(value, ());
            true
        }
    }
}

// before every progress you'd do at most 2*N_RANKS move
// and there would only be N_FULL_DECK + N_HIDDEN progress step
const TP_SIZE: usize = 256 * 1024 * 1024;
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
    fn on_win(&mut self, _: &Solitaire) -> TraverseResult {
        self.result = SearchResult::Solved;
        TraverseResult::Halted
    }

    fn on_visit(&mut self, _: &Solitaire, _: &Option<Move>, _: Encode) -> TraverseResult {
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

    fn on_do_move(&mut self, _: usize, m: &Move, _: Encode) {
        self.history.push(*m);
    }

    fn on_undo_move(&mut self, pos: usize, _: &Move, _: Encode) {
        self.history.pop();
        self.stats.finish_move(self.history.len(), pos);
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
    let mut tp = TpCache::with(
        TP_SIZE,
        TP_SIZE as u64,
        Default::default(),
        Default::default(),
        Default::default(),
    );

    let mut callback = SolverCallback {
        history: HistoryVec::new(),
        stats,
        sign,
        result: SearchResult::Unsolvable,
    };

    traverse_game(g, &mut tp, &mut callback);
    let result = callback.result;

    if let SearchResult::Solved = result {
        (result, Some(callback.history))
    } else {
        (result, None)
    }
}

pub fn solve_game(g: &mut Solitaire) -> (SearchResult, Option<HistoryVec>) {
    solve_game_with_tracking(g, &EmptySearchStats {}, &DefaultSearchSignal {})
}
