use crate::{
    card::{Card, KING_MASK},
    moves::{Move, MoveMask},
    state::{ExtraInfo, Solitaire},
};

pub trait Pruner {
    #[must_use]
    // the game state is before doing the move `m`
    fn update(&self, m: Move, rev_m: Option<Move>, m: ExtraInfo) -> Self;

    #[must_use]
    fn prune_moves(&self, game: &Solitaire) -> MoveMask;
}

#[derive(Default)]
pub struct NoPruner {}

impl Pruner for NoPruner {
    fn update(&self, _: Move, _: Option<Move>, _: ExtraInfo) -> Self {
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
    fn update(&self, _: Move, rev_m: Option<Move>, _: ExtraInfo) -> Self {
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
    fn update(&self, m: Move, rev_m: Option<Move>, extra: ExtraInfo) -> Self {
        Self {
            cycle: self.cycle.update(m, rev_m, extra),
            last_move: m,
            last_extra: extra,
            last_draw: match m {
                Move::DeckPile(c) => Some(c),
                Move::StackPile(c) if !self.last_draw.is_some_and(|cc| c.go_after(Some(cc))) => {
                    self.last_draw
                }
                _ => None,
            },
        }
    }
    fn prune_moves(&self, game: &Solitaire) -> MoveMask {
        let (rule, streak, cycle) = self.explain(game);
        rule.combine(&streak).combine(&cycle)
    }
}

impl FullPruner {
    /// The reveal-context rules (6.2/6.3 of method.md), as a remove-mask.
    fn reveal_rule_mask(&self) -> MoveMask {
        match (self.last_move, &self.last_extra) {
            // Moving the top layer card and leave the pile empty
            // => Must move another king to fill the empty spot, otherwise it doesn't make sense
            (Move::Reveal(_), ExtraInfo::RevealEmpty) => MoveMask {
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
        }
    }

    /// The draw-streak rules (6.4a/6.4b), as a remove-mask; identity outside
    /// a streak.
    fn streak_mask(&self, first_layer: u64) -> MoveMask {
        let Some(last_draw) = self.last_draw else {
            return MoveMask::default();
        };

        // pruning deck :)
        let m = last_draw.mask();
        let other = last_draw.swap_suit().mask();
        let mm = m | other;

        // need | first layer because of this case , DP 8♠, R 10♥, DP K♠,
        // if you reveal 10 first then you forced to get K, which might prevent you from getting 8
        // if you get 8 first, you can't reveal 10, because it expects you to reveal it before
        // to get the required card to put under 8, but since it doesn't reveal anything, it's not doing it
        MoveMask {
            pile_stack: !other,
            reveal: !((mm >> 4) | first_layer),
            ..MoveMask::default()
        }
    }

    /// Phase-0 decomposition for the falsifier harness: the three rule
    /// groups as separate remove-masks — (reveal-context, streak, cycle).
    /// `prune_moves` is their union; this exists so instrumentation can
    /// attribute each removed move to the rule that killed it.
    #[must_use]
    pub(crate) fn explain(&self, game: &Solitaire) -> (MoveMask, MoveMask, MoveMask) {
        let first_layer = game.get_hidden().first_layer_mask();
        (
            self.reveal_rule_mask(),
            self.streak_mask(first_layer),
            self.cycle.prune_moves(game),
        )
    }

    /// The current streak card (the drawn card guarding the rules), if any.
    /// Test instrumentation (traverse.rs's streak-witness audit).
    #[must_use]
    #[cfg(test)]
    pub(crate) const fn instrument_last_draw(&self) -> Option<Card> {
        self.last_draw
    }

    #[must_use]
    pub(crate) const fn rev_move(&self) -> Option<Move> {
        self.cycle.rev_move
    }
}
