use core::{fmt, ops::ControlFlow};

use crate::{
    card::{Card, N_SUITS},
    deck::N_PILES,
};
use arrayvec::ArrayVec;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Move {
    DeckStack(Card),
    PileStack(Card),
    DeckPile(Card),
    StackPile(Card),
    Reveal(Card),
}

impl Move {
    pub const FAKE: Self = Move::DeckPile(Card::FAKE);
}

impl fmt::Display for Move {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::DeckStack(c) => write!(f, "DS {c}"),
            Self::PileStack(c) => write!(f, "PS {c}"),
            Self::DeckPile(c) => write!(f, "DP {c}"),
            Self::StackPile(c) => write!(f, "SP {c}"),
            Self::Reveal(c) => write!(f, "R {c}"),
        }
    }
}

#[derive(Default)]
pub struct MoveMask {
    pub pile_stack: u64,
    pub deck_stack: u64,
    pub stack_pile: u64,
    pub deck_pile: u64,
    pub reveal: u64,
}

impl From<Move> for MoveMask {
    #[inline]
    fn from(value: Move) -> Self {
        let mut filter = Self::default();
        match value {
            Move::PileStack(c) => filter.pile_stack |= c.mask(),
            Move::DeckStack(c) => filter.deck_stack |= c.mask(),
            Move::StackPile(c) => filter.stack_pile |= c.mask(),
            Move::DeckPile(c) => filter.deck_pile |= c.mask(),
            Move::Reveal(c) => filter.reveal |= c.mask(),
        }
        filter
    }
}

fn iter_mask_opt<T>(mut m: u64, mut func: impl FnMut(Card) -> ControlFlow<T>) -> ControlFlow<T> {
    while m > 0 {
        let c = Card::from_mask(&m);
        func(c)?;
        m &= m.wrapping_sub(1);
    }
    ControlFlow::Continue(())
}

impl MoveMask {
    pub const fn only_pile_stack(pile_stack: u64) -> MoveMask {
        MoveMask {
            pile_stack,
            deck_stack: 0,
            stack_pile: 0,
            deck_pile: 0,
            reveal: 0,
        }
    }
    pub const fn only_deck_stack(deck_stack: u64) -> MoveMask {
        MoveMask {
            pile_stack: 0,
            deck_stack,
            stack_pile: 0,
            deck_pile: 0,
            reveal: 0,
        }
    }

    #[inline]
    fn binary_op<F: Fn(u64, u64) -> u64>(&self, other: &Self, op: F) -> Self {
        Self {
            pile_stack: op(self.pile_stack, other.pile_stack),
            deck_stack: op(self.deck_stack, other.deck_stack),
            stack_pile: op(self.stack_pile, other.stack_pile),
            deck_pile: op(self.deck_pile, other.deck_pile),
            reveal: op(self.reveal, other.reveal),
        }
    }

    pub fn filter(&self, remove: &Self) -> Self {
        self.binary_op(remove, |x, y| x & !y)
    }

    pub fn combine(&self, other: &Self) -> Self {
        self.binary_op(other, |x, y| x | y)
    }

    pub fn iter_moves<T, F: FnMut(Move) -> ControlFlow<T>>(&self, mut func: F) -> ControlFlow<T> {
        // the only case a card can be in two different moves
        // deck_to_stack/deck_to_pile (maximum duplicate N_SUITS cards)
        // reveal/pile_stack (maximum duplicate N_SUITS cards)
        // these two cases can't happen simultaneously (only max N_SUIT card can be move to a stack)
        // => Maximum moves <= N_CARDS + N_SUIT

        // maximum min(N_PILES - 1, N_CARDS) moves (can't have a cycle of reveal piles)
        iter_mask_opt::<T>(self.reveal, |c| func(Move::Reveal(c)))?;
        // maximum min(N_PILES, N_SUITS) moves
        iter_mask_opt::<T>(self.pile_stack, |c| func(Move::PileStack(c)))?;
        // maximum min(N_PILES, N_DECK) moves
        iter_mask_opt::<T>(self.deck_pile, |c| func(Move::DeckPile(c)))?;
        // maximum min(N_DECK, N_SUITS) moves
        // deck_stack and pile_stack can't happen simultaneously so both of the combine can't have more than
        // N_SUITS move
        iter_mask_opt::<T>(self.deck_stack, |c| func(Move::DeckStack(c)))?;
        // maximum min(N_PILES, N_SUIT) moves
        iter_mask_opt::<T>(self.stack_pile, |c| func(Move::StackPile(c)))

        // <= N_PILES * 2 + N_SUITS * 2 - 1 = 14 + 8 - 1 = 21 moves
    }
}

pub const N_MOVES_MAX: usize = (N_PILES * 2 + N_SUITS * 2 - 1) as usize;

pub type MoveVec = ArrayVec<Move, N_MOVES_MAX>;
