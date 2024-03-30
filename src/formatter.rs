use core::fmt;

use arrayvec::ArrayVec;

use crate::card::{Card, NUMBERS, N_RANKS, N_SUITS, SYMBOLS};
use crate::deck::{N_FULL_DECK, N_PILES};
use crate::engine::Move;
use crate::standard::StandardSolitaire;

impl fmt::Display for Card {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let (u, v) = self.split();
        if u < N_RANKS {
            write!(f, "{}{}", NUMBERS[u as usize], SYMBOLS[v as usize])
        } else {
            write!(f, "  ")
        }
    }
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

pub struct Solvitaire(pub StandardSolitaire);

impl fmt::Display for Solvitaire {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, r#"{{"tableau piles": ["#)?;

        for i in 0..N_PILES as usize {
            write!(f, "[")?;
            for c in &self.0.hidden_piles[i] {
                // hidden cards
                c.print_solvitaire::<true>(f)?;
                write!(f, ",")?;
            }
            for (idx, c) in self.0.piles[i].iter().enumerate() {
                if idx != 0 {
                    write!(f, ",")?;
                }
                c.print_solvitaire::<false>(f)?;
            }
            if i + 1 < N_PILES as usize {
                writeln!(f, "],")?;
            } else {
                writeln!(f, "]")?;
            }
        }

        write!(f, "],\"stock\": [")?;

        let tmp: ArrayVec<Card, N_FULL_DECK> = self.0.get_deck().iter().copied().collect();

        for (idx, c) in tmp.iter().enumerate().rev() {
            c.print_solvitaire::<false>(f)?;
            if idx == 0 {
                write!(f, "]")?;
            } else {
                write!(f, ",")?;
            }
        }

        // foundation
        write!(f, ",\n\"foundation\": [")?;

        for suit in 0..N_SUITS {
            if suit > 0 {
                write!(f, ",")?;
            }

            write!(f, "[")?;
            for rank in 0..self.0.final_stack[suit as usize] {
                if rank > 0 {
                    write!(f, ",")?;
                }
                let c = Card::new(rank, suit);
                c.print_solvitaire::<false>(f)?;
            }
            write!(f, "]")?;
        }
        write!(f, "]}}")?;

        Ok(())
    }
}
