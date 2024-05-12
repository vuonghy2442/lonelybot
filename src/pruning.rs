use crate::{
    card::KING_MASK,
    engine::{Move, Solitaire},
};

pub struct PruneInfo {
    rev_move: Option<Move>,
    last_move: Move,
}

impl Default for PruneInfo {
    fn default() -> Self {
        Self {
            rev_move: None,
            last_move: Move::FAKE,
        }
    }
}

impl PruneInfo {
    pub fn new(game: &Solitaire, _prev: &PruneInfo, m: &Move) -> Self {
        Self {
            rev_move: game.get_rev_move(&m),
            last_move: *m,
        }
    }

    pub fn rev_move(&self) -> Option<Move> {
        return self.rev_move;
    }

    pub fn last_move(&self) -> Move {
        return self.last_move;
    }

    pub fn prune_moves(&self, game: &Solitaire) -> [u64; 5] {
        // [pile_stack, deck_stack, stack_pile, deck_pile, reveal]
        let mut filter = match self.last_move {
            Move::Reveal(c) => {
                if game.get_hidden().first_layer_mask() & c.mask() > 0 {
                    [!0, !0, !KING_MASK, !KING_MASK, !KING_MASK]
                } else {
                    [0; 5]
                }
            }
            _ => [0; 5],
        };

        match self.rev_move {
            Some(Move::PileStack(c)) => filter[0] |= c.mask(),
            Some(Move::DeckStack(c)) => filter[1] |= c.mask(),
            Some(Move::StackPile(c)) => filter[2] |= c.mask(),
            Some(Move::DeckPile(c)) => filter[3] |= c.mask(),
            Some(Move::Reveal(c)) => filter[4] |= c.mask(),
            None => {}
        }

        filter
    }
}
