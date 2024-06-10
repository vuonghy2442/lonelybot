use core::fmt;

use crate::card::{Card, N_RANKS, N_SUITS};
use crate::standard::{Pos, StandardMove};

pub const SYMBOLS: [&str; N_SUITS as usize] = ["♥", "♦", "♣", "♠"];
pub const NUMBERS: [&str; N_RANKS as usize] = [
    "A", "2", "3", "4", "5", "6", "7", "8", "9", "10", "J", "Q", "K",
];

impl fmt::Display for Card {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let (u, v) = self.split();
        write!(f, "{}{}", NUMBERS[u as usize], SYMBOLS[v as usize])
    }
}

impl fmt::Display for Pos {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Pos::Deck => write!(f, "D"),
            Pos::Stack(p) => write!(f, "{}", SYMBOLS[*p as usize]),
            Pos::Pile(p) => write!(f, "{}", p + 1),
        }
    }
}

impl fmt::Display for StandardMove {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if *self == StandardMove::DRAW_NEXT {
            write!(f, "=")
        } else {
            write!(f, "{}:{}▸{}", self.card, self.from, self.to)
        }
    }
}
