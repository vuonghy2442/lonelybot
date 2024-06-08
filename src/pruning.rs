use crate::{
    card::{Card, ALT_MASK, KING_MASK},
    moves::{Move, MoveMask},
    state::Solitaire,
};

pub trait Pruner {
    #[must_use]
    // the game state is before doing the move `m`
    fn new(game: &Solitaire, prev: &Self, m: &Move) -> Self;

    #[must_use]
    fn prune_moves(&self, game: &Solitaire) -> MoveMask;
}

#[derive(Default)]
pub struct NoPruner {}

impl Pruner for NoPruner {
    fn new(_: &Solitaire, _: &Self, _: &Move) -> Self {
        Self {}
    }

    fn prune_moves(&self, _: &Solitaire) -> MoveMask {
        MoveMask::default()
    }
}

#[derive(Default)]
pub struct CyclePruner {
    rev_move: Option<Move>,
}

impl Pruner for CyclePruner {
    fn new(game: &Solitaire, _: &Self, m: &Move) -> Self {
        Self {
            rev_move: game.reverse_move(m),
        }
    }

    fn prune_moves(&self, _: &Solitaire) -> MoveMask {
        self.rev_move.map_or(MoveMask::default(), MoveMask::from)
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
            last_move: Move::DeckPile(Card::DEFAULT),
            last_draw: None,
        }
    }
}

impl Pruner for FullPruner {
    fn new(game: &Solitaire, prev: &Self, m: &Move) -> Self {
        Self {
            cycle: CyclePruner::new(game, &prev.cycle, m),
            last_move: *m,
            last_draw: match m {
                Move::DeckPile(c) => Some(*c),
                Move::StackPile(c) if !prev.last_draw.is_some_and(|cc| c.go_after(Some(&cc))) => {
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
                Move::Reveal(c) if first_layer & c.mask() > 0 => MoveMask {
                    pile_stack: !0,
                    deck_stack: !0,
                    stack_pile: !KING_MASK,
                    deck_pile: !KING_MASK,
                    reveal: !KING_MASK,
                },
                _ => MoveMask::default(),
            };

            if let Some(last_draw) = self.last_draw {
                // pruning deck :)
                let m = last_draw.mask();
                let mm = ((m | m >> 1) & ALT_MASK) * 0b11;
                filter.pile_stack |= !mm | m;

                // need | first layer because of this case , DP 8♠, R 10♥, DP K♠,
                // if you reveal 10 first then you forced to get K, which might prevent you from getting 8
                // if you get 8 first, you can't reveal 10, because it expects you to reveal it before
                // to get the required card to put under 8, but since it doesn't reveal anything, it's not doing it``
                filter.reveal |= !((mm >> 4) | first_layer);
            }
            filter
        };

        filter.combine(&self.cycle.prune_moves(game))
    }
}

impl FullPruner {
    #[must_use]
    pub(crate) const fn rev_move(&self) -> Option<Move> {
        self.cycle.rev_move
    }
}
