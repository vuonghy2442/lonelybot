use core::fmt;

use crate::card::{Card, NUMBERS, N_RANKS, SYMBOLS};
use crate::deck::N_PILES;
use crate::engine::{Move, Solitaire};
use crate::shuffler::CardDeck;

impl fmt::Display for Card {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let (u, v) = self.split();
        return if u < N_RANKS {
            write!(f, "{}{}", NUMBERS[u as usize], SYMBOLS[v as usize])
        } else {
            write!(f, "  ")
        };
    }
}

impl fmt::Display for Move {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Move::DeckStack(c) => write!(f, "DS {}", c),
            Move::PileStack(c) => write!(f, "PS {}", c),
            Move::DeckPile(c) => write!(f, "DP {}", c),
            Move::StackPile(c) => write!(f, "SP {}", c),
            Move::Reveal(c) => write!(f, "R {}", c),
        }
    }
}

pub struct Solvitaire(Solitaire);
impl Solvitaire {
    pub fn new(deck: &CardDeck, draw_step: u8) -> Solvitaire {
        Solvitaire(Solitaire::new(deck, draw_step))
    }
}

impl fmt::Display for Solvitaire {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, r#"{{"tableau piles": ["#)?;

        for i in 0..N_PILES as usize {
            write!(f, "[")?;
            for j in 0..i as usize {
                // hidden cards
                self.0
                    .get_hidden(i as u8, j as u8)
                    .print_solvitaire::<true>(f)?;
                write!(f, ",")?;
            }
            self.0
                .get_hidden(i as u8, i as u8)
                .print_solvitaire::<false>(f)?;
            if i + 1 < N_PILES as usize {
                writeln!(f, "],")?;
            } else {
                writeln!(f, "]")?;
            }
        }

        write!(f, "],\"stock\": [")?;

        let tmp: Vec<(u8, Card)> = self.0.get_deck().iter_all().map(|x| (x.0, *x.1)).collect();

        for &(idx, c) in tmp.iter().rev() {
            c.print_solvitaire::<false>(f)?;
            if idx == 0 {
                write!(f, "]")?;
            } else {
                write!(f, ",")?;
            }
        }
        write!(f, "}}")?;

        Ok(())
    }
}
