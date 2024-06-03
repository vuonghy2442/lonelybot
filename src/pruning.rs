use crate::{
    card::{Card, ALT_MASK, KING_MASK},
    engine::{Move, MoveMask, Solitaire},
};

pub trait Pruner {
    #[must_use]
    fn new(game: &Solitaire, prev: &Self, m: &Move) -> Self;

    #[must_use]
    fn prune_moves(&self, game: &Solitaire) -> MoveMask;
}

#[derive(Default)]
pub struct CyclePruner {
    rev_move: Option<Move>,
}

impl Pruner for CyclePruner {
    fn new(game: &Solitaire, _: &Self, m: &Move) -> Self {
        Self {
            rev_move: game.get_rev_move(m),
        }
    }

    fn prune_moves(&self, _: &Solitaire) -> MoveMask {
        let mut filter = [0; 5];
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

pub struct FullPruner {
    cycle: CyclePruner,
    last_move: Move,
    last_draw: Option<Card>,
}

impl Default for FullPruner {
    fn default() -> Self {
        Self {
            cycle: CyclePruner::default(),
            last_move: Move::FAKE,
            last_draw: None,
        }
    }
}

fn combine_mask(a: &MoveMask, b: &MoveMask) -> MoveMask {
    core::array::from_fn(|i| a[i] | b[i])
}

impl Pruner for FullPruner {
    fn new(game: &Solitaire, prev: &Self, m: &Move) -> Self {
        Self {
            cycle: CyclePruner::new(game, &prev.cycle, m),
            last_move: *m,
            last_draw: match m {
                Move::DeckPile(c) => Some(*c),
                Move::StackPile(c) if !prev.last_draw.is_some_and(|cc| cc.go_before(c)) => {
                    prev.last_draw
                }
                _ => None,
            },
        }
    }

    fn prune_moves(&self, game: &Solitaire) -> MoveMask {
        let filter = {
            let first_layer = game.get_hidden().first_layer_mask();
            let mut filter = match self.last_move {
                Move::Reveal(c) if first_layer & c.mask() > 0 => {
                    [!0, !0, !KING_MASK, !KING_MASK, !KING_MASK]
                }
                _ => [0; 5],
            };

            if let Some(last_draw) = self.last_draw {
                // pruning deck :)
                let m = last_draw.mask();
                let mm = ((m | m >> 1) & ALT_MASK) * 0b11;
                filter[0] |= !mm | m;

                // need | first layer because of this case , DP 8♠, R 10♥, DP K♠,
                // if you reveal 10 first then you forced to get K, which might prevent you from getting 8
                // if you get 8 first, you can't reveal 10, because it expects you to reveal it before
                // to get the required card to put under 8, but since it doesn't reveal anything, it's not doing it``
                filter[4] |= !((mm >> 4) | first_layer);
            }
            filter
        };

        combine_mask(&filter, &self.cycle.prune_moves(game))
    }
}

impl FullPruner {
    #[must_use]
    pub const fn rev_move(&self) -> Option<Move> {
        self.cycle.rev_move
    }

    #[must_use]
    pub const fn last_move(&self) -> Move {
        self.last_move
    }
}
