use crate::{
    card::Card,
    moves::{Move, MoveMask},
    pruning::FullPruner,
    state::{Encode, Solitaire},
    tracking::{DefaultTerminateSignal, EmptySearchStats, SearchStatistics, TerminateSignal},
    traverse::{traverse, Callback, Control, TpTable},
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

impl<'a, S: SearchStatistics, T: TerminateSignal> BuilderCallback<'a, S, T> {
    fn new(g: &Solitaire, stats: &'a S, sign: &'a T) -> Self {
        Self {
            graph: Graph::new(),
            stats,
            sign,
            depth: 0,
            prev_enc: g.encode(),
            last_move: Move::DeckPile(Card::DEFAULT),
            rev_move: None,
        }
    }
}

impl<'a, S: SearchStatistics, T: TerminateSignal> Callback for BuilderCallback<'a, S, T> {
    type Pruner = FullPruner;

    fn on_win(&mut self, _: &Solitaire) -> Control {
        // win state
        self.graph.push((
            self.prev_enc,
            !0,
            get_edge_type(self.last_move, self.rev_move),
        ));
        Control::Ok
    }

    fn on_visit(&mut self, _: &Solitaire, e: Encode) -> Control {
        if self.sign.is_terminated() {
            return Control::Halt;
        }

        self.stats.hit_a_state(self.depth);
        self.graph.push((
            self.prev_enc,
            e,
            get_edge_type(self.last_move, self.rev_move),
        ));

        Control::Ok
    }

    fn on_move_gen(&mut self, m: &MoveMask, _: Encode) -> Control {
        self.stats.hit_unique_state(self.depth, m.len());
        Control::Ok
    }

    fn on_do_move(&mut self, _: &Solitaire, m: Move, e: Encode, prune: &FullPruner) -> Control {
        self.last_move = m;
        self.rev_move = prune.rev_move();
        self.prev_enc = e;
        self.depth += 1;
        Control::Ok
    }

    fn on_undo_move(&mut self, _: Move, _: Encode, _: &Control) {
        self.depth -= 1;
        self.stats.finish_move(self.depth);
    }
}

pub fn graph_with_tracking<S: SearchStatistics, T: TerminateSignal>(
    g: &mut Solitaire,
    stats: &S,
    sign: &T,
) -> (Control, Graph) {
    let mut tp = TpTable::default();
    let mut callback = BuilderCallback::new(g, stats, sign);

    let finished = traverse(g, &FullPruner::default(), &mut tp, &mut callback);
    (finished, callback.graph)
}

pub fn graph(g: &mut Solitaire) -> (Control, Graph) {
    graph_with_tracking(g, &EmptySearchStats {}, &DefaultTerminateSignal {})
}
