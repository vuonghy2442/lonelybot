use crate::{
    card::{Card, KING_MASK},
    moves::{Move, MoveMask},
    state::{ExtraInfo, Solitaire},
};

pub trait Pruner {
    #[must_use]
    // the game state is before doing the move `m`
    fn update(prev: &Self, m: Move, rev_m: Option<Move>, m: ExtraInfo) -> Self;

    #[must_use]
    fn prune_moves(&self, game: &Solitaire) -> MoveMask;
}

#[derive(Default)]
pub struct NoPruner {}

impl Pruner for NoPruner {
    fn update(_: &Self, _: Move, _: Option<Move>, _: ExtraInfo) -> Self {
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
    fn update(_: &Self, _: Move, rev_m: Option<Move>, _: ExtraInfo) -> Self {
        Self { rev_move: rev_m }
    }

    fn prune_moves(&self, _: &Solitaire) -> MoveMask {
        self.rev_move.map_or(MoveMask::default(), MoveMask::from)
    }
}

pub struct FullPruner {
    cycle: CyclePruner,
    last_move: Move,
    last_extra: ExtraInfo,
    last_draw: Option<Card>,
}

impl Default for FullPruner {
    fn default() -> Self {
        Self {
            cycle: CyclePruner::default(),
            last_move: Move::DeckPile(Card::DEFAULT),
            last_extra: ExtraInfo::None,
            last_draw: None,
        }
    }
}

impl Pruner for FullPruner {
    fn update(prev: &Self, m: Move, rev_m: Option<Move>, extra: ExtraInfo) -> Self {
        Self {
            cycle: CyclePruner::update(&prev.cycle, m, rev_m, extra),
            last_move: m,
            last_extra: extra,
            last_draw: match m {
                Move::DeckPile(c) => Some(c),
                Move::StackPile(c) if !prev.last_draw.is_some_and(|cc| c.go_after(Some(cc))) => {
                    prev.last_draw
                }
                _ => None,
            },
        }
    }
    fn prune_moves(&self, game: &Solitaire) -> MoveMask {
        let filter = {
            let mut filter = match (self.last_move, &self.last_extra) {
                // Moving the top layer card and leave the pile empty
                // => Must move another king to fill the empty spot, otherwise it doesn't make sense
                (Move::Reveal(_), ExtraInfo::None) => MoveMask {
                    pile_stack: !0,
                    deck_stack: !0,
                    stack_pile: !KING_MASK,
                    deck_pile: !KING_MASK,
                    reveal: !KING_MASK,
                },

                (Move::Reveal(_), &ExtraInfo::Card(c)) => {
                    let m = c.mask();
                    let other = c.swap_suit().mask();
                    let mm = m | other;

                    MoveMask {
                        pile_stack: !mm,
                        deck_stack: !0,
                        stack_pile: 0,
                        deck_pile: 0,
                        reveal: 0,
                    }
                }
                // TODO: another case of stack and reveal without dominances
                _ => MoveMask::default(),
            };

            if let Some(last_draw) = self.last_draw {
                let first_layer = game.get_hidden().first_layer_mask();

                // pruning deck :)
                let m = last_draw.mask();
                let other = last_draw.swap_suit().mask();
                let mm = m | other;
                filter.pile_stack |= !other;

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
