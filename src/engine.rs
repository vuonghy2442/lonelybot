use crate::{
    moves::{Move, MoveMask, N_MOVES_MAX},
    pruning::Pruner,
    state::{Encode, Solitaire, UndoInfo},
};
pub type MoveVec = ArrayVec<Move, N_MOVES_MAX>;

extern crate alloc;
use alloc::vec::Vec;
use arrayvec::ArrayVec;

pub struct SolitaireEngine<P: Pruner> {
    state: Solitaire,
    pruner: P,
    history: Vec<(Move, UndoInfo)>,
    valid_moves: MoveMask,
}

impl<P: Pruner + Default> From<Solitaire> for SolitaireEngine<P> {
    fn from(value: Solitaire) -> Self {
        Self::new(value)
    }
}

impl<P: Pruner + Default> SolitaireEngine<P> {
    #[must_use]
    pub fn new(state: Solitaire) -> Self {
        Self {
            valid_moves: state.gen_moves::<false>(),
            pruner: P::default(),
            state,
            history: Vec::default(),
        }
    }

    #[must_use]
    pub const fn state(&self) -> &Solitaire {
        &self.state
    }

    #[must_use]
    pub fn into_state(self) -> Solitaire {
        self.state
    }

    #[must_use]
    pub const fn pruner(&self) -> &P {
        &self.pruner
    }

    #[must_use]
    pub fn is_valid(&self, m: Move) -> bool {
        MoveMask::from(m).filter(&self.valid_moves).is_empty()
    }

    pub fn do_move(&mut self, m: Move) -> bool {
        if !self.is_valid(m) {
            return false;
        }

        let (rev_m, (undo, extra)) = self.state.do_move(m);
        self.pruner = Pruner::update(&self.pruner, m, rev_m, extra);
        self.history.push((m, undo));
        self.valid_moves = self.state.gen_moves::<false>();
        true
    }

    // undoing will reset the pruner :)
    pub fn undo_move(&mut self) -> bool {
        let Some((m, undo)) = self.history.pop() else {
            return false;
        };

        self.pruner = P::default();
        self.state.undo_move(m, undo);
        self.valid_moves = self.state.gen_moves::<false>();

        true
    }

    #[must_use]
    pub fn encode(&self) -> Encode {
        self.state.encode()
    }

    // it will reset everything :) so use carefully
    pub fn decode(&mut self, encode: u64) -> bool {
        let mut tmp = self.state.clone();
        tmp.decode(encode);

        if !tmp.is_valid() {
            return false;
        }

        self.state = tmp;
        self.history.clear();
        self.valid_moves = self.state.gen_moves::<false>();
        self.pruner = P::default();

        true
    }

    #[must_use]
    fn list_moves_generics<const DOMINANCE: bool>(&self) -> MoveVec {
        self.state
            .gen_moves::<DOMINANCE>()
            .filter(&self.pruner.prune_moves(&self.state))
            .to_vec()
    }

    #[must_use]
    pub fn list_moves_dom(&self) -> MoveVec {
        self.list_moves_generics::<true>()
    }

    #[must_use]
    pub fn list_moves(&self) -> MoveVec {
        self.list_moves_generics::<false>()
    }
}
