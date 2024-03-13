use crate::{
    engine::{Encode, Move, Solitaire},
    tracking::{DefaultSearchSignal, EmptySearchStats, SearchSignal, SearchStatistics},
    traverse::{traverse_game, GraphCallback, TpTable, TraverseResult},
};

extern crate alloc;
use alloc::vec::Vec;

pub type Edge = (Encode, Encode, bool);
pub type Graph = Vec<Edge>;

struct BuilderCallback<'a, S: SearchStatistics, T: SearchSignal> {
    graph: Graph,
    stats: &'a S,
    sign: &'a T,
    depth: usize,
    prev_enc: Encode,
}

impl<'a, S: SearchStatistics, T: SearchSignal> GraphCallback for BuilderCallback<'a, S, T> {
    fn on_win(&mut self, _: &Solitaire) -> TraverseResult {
        // win state
        self.graph.push((self.prev_enc, !0, true));
        TraverseResult::Ok
    }

    fn on_visit(&mut self, _: &Solitaire, rev: &Option<Move>, e: Encode) -> TraverseResult {
        if self.sign.is_terminated() {
            return TraverseResult::Halted;
        }

        self.stats.hit_a_state(self.depth);
        self.graph.push((self.prev_enc, e, rev.is_none()));

        TraverseResult::Ok
    }

    fn on_move_gen(&mut self, m: &crate::engine::MoveVec, _: Encode) {
        self.stats.hit_unique_state(self.depth, m.len());
    }

    fn on_do_move(&mut self, _: usize, _: &Move, e: Encode) {
        self.prev_enc = e;
        self.depth += 1;
    }

    fn on_undo_move(&mut self, pos: usize, _: &Move, _: Encode) {
        self.depth -= 1;
        self.stats.finish_move(self.depth, pos);
    }

    fn on_start(&mut self) {}

    fn on_finish(&mut self, _: &TraverseResult) {
        self.sign.search_finish();
    }
}

pub fn graph_game_with_tracking(
    g: &mut Solitaire,
    stats: &impl SearchStatistics,
    sign: &impl SearchSignal,
) -> (TraverseResult, Graph) {
    let mut tp = TpTable::with_hasher(Default::default());
    let mut callback = BuilderCallback {
        graph: Graph::new(),
        stats,
        sign,
        depth: 0,
        prev_enc: g.encode(),
    };

    let finished = traverse_game(g, &mut tp, &mut callback);
    (finished, callback.graph)
}

pub fn graph_game(g: &mut Solitaire) -> (TraverseResult, Graph) {
    graph_game_with_tracking(g, &EmptySearchStats {}, &DefaultSearchSignal {})
}
