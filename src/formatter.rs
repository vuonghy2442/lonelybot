use core::fmt;

use arrayvec::ArrayVec;

use crate::card::{Card, NUMBERS, N_RANKS, N_SUITS, SYMBOLS};
use crate::deck::{N_FULL_DECK, N_PILES};
use crate::engine::Move;
use crate::standard::StandardSolitaire;

pub struct SolvitaireCard<const LOWER: bool>(pub Card);

impl<const LOWER: bool> fmt::Display for SolvitaireCard<LOWER> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let (rank, suit) = self.0.split();
        let s = match suit {
            0 => 'H',
            1 => 'D',
            2 => 'C',
            3 => 'S',
            _ => 'x',
        };
        write!(
            f,
            r#""{}{}""#,
            NUMBERS[rank as usize],
            if LOWER { s.to_ascii_lowercase() } else { s }
        )
    }
}

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
                write!(f, "{},", SolvitaireCard::<true>(*c))?;
            }
            for (idx, c) in self.0.piles[i].iter().enumerate() {
                if idx != 0 {
                    write!(f, ",")?;
                }
                write!(f, "{}", SolvitaireCard::<false>(*c))?;
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
            write!(f, "{}", SolvitaireCard::<false>(*c))?;
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
                write!(f, "{}", SolvitaireCard::<false>(c))?;
            }
            write!(f, "]")?;
        }
        write!(f, "]}}")?;

        Ok(())
    }
}
