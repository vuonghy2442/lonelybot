use crate::{
    engine::{Encode, Move, Solitaire},
    pruning::FullPruner,
    tracking::{DefaultTerminateSignal, EmptySearchStats, SearchStatistics, TerminateSignal},
    traverse::{traverse, Callback, ControlFlow, TpTable},
};

extern crate alloc;
use alloc::vec::Vec;

#[derive(Clone, Copy, Debug)]
pub enum EdgeType {
    DeckPile,
    DeckStack,
    PileStack,
    PileStackReveal,
    StackPile,
    Reveal,
}

pub type Edge = (Encode, Encode, EdgeType);
pub type Graph = Vec<Edge>;

struct BuilderCallback<'a, S: SearchStatistics, T: TerminateSignal> {
    graph: Graph,
    stats: &'a S,
    sign: &'a T,
    depth: usize,
    prev_enc: Encode,
    last_move: Move,
    rev_move: Option<Move>,
}

const fn get_edge_type(m: Move, rm: Option<Move>) -> EdgeType {
    match m {
        Move::DeckStack(_) => EdgeType::DeckStack,
        Move::PileStack(_) if rm.is_some() => EdgeType::PileStack,
        Move::PileStack(_) => EdgeType::PileStackReveal,
        Move::DeckPile(_) => EdgeType::DeckPile,
        Move::StackPile(_) => EdgeType::StackPile,
        Move::Reveal(_) => EdgeType::Reveal,
    }
}

impl<'a, S: SearchStatistics, T: TerminateSignal> Callback for BuilderCallback<'a, S, T> {
    type Pruner = FullPruner;

    fn on_win(&mut self, _: &Solitaire) -> ControlFlow {
        // win state
        self.graph.push((
            self.prev_enc,
            !0,
            get_edge_type(self.last_move, self.rev_move),
        ));
        ControlFlow::Ok
    }

    fn on_visit(&mut self, _: &Solitaire, e: Encode) -> ControlFlow {
        if self.sign.is_terminated() {
            return ControlFlow::Halt;
        }

        self.stats.hit_a_state(self.depth);
        self.graph.push((
            self.prev_enc,
            e,
            get_edge_type(self.last_move, self.rev_move),
        ));

        ControlFlow::Ok
    }

    fn on_move_gen(&mut self, m: &crate::engine::MoveVec, _: Encode) -> ControlFlow {
        self.stats.hit_unique_state(self.depth, m.len());
        ControlFlow::Ok
    }

    fn on_do_move(
        &mut self,
        _: &Solitaire,
        m: &Move,
        e: Encode,
        prune: &FullPruner,
    ) -> ControlFlow {
        self.last_move = *m;
        self.rev_move = prune.rev_move();
        self.prev_enc = e;
        self.depth += 1;
        ControlFlow::Ok
    }

    fn on_undo_move(&mut self, _: &Move, _: Encode, _: &ControlFlow) {
        self.depth -= 1;
        self.stats.finish_move(self.depth);
    }
}

pub fn graph_with_tracking<S: SearchStatistics, T: TerminateSignal>(
    g: &mut Solitaire,
    stats: &S,
    sign: &T,
) -> (ControlFlow, Graph) {
    let mut tp = TpTable::default();
    let mut callback = BuilderCallback {
        graph: Graph::new(),
        stats,
        sign,
        depth: 0,
        prev_enc: g.encode(),
        last_move: Move::FAKE,
        rev_move: None,
    };

    let finished = traverse(g, &FullPruner::default(), &mut tp, &mut callback);
    (finished, callback.graph)
}

pub fn graph(g: &mut Solitaire) -> (ControlFlow, Graph) {
    graph_with_tracking(g, &EmptySearchStats {}, &DefaultTerminateSignal {})
}
