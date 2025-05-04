use core::fmt;

use lonelybot::{
    card::{Card, N_SUITS},
    deck::N_PILES,
    formatter::NUMBERS,
    standard::StandardSolitaire,
};

pub(crate) struct SolvitaireCard<const LOWER: bool>(Card);

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

pub struct Solvitaire(pub StandardSolitaire);

impl fmt::Display for Solvitaire {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, r#"{{"tableau piles": ["#)?;

        for i in 0..N_PILES as usize {
            write!(f, "[")?;
            for c in &self.0.get_hidden()[i] {
                // hidden cards
                write!(f, "{},", SolvitaireCard::<true>(*c))?;
            }
            for (idx, c) in self.0.get_piles()[i].iter().enumerate() {
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

        for c in self.0.get_deck().deck_iter().rev().enumerate() {
            if c.0 > 0 {
                write!(f, ",")?;
            }
            write!(f, "{}", SolvitaireCard::<false>(c.1))?;
        }
        write!(f, "],\"waste\": [")?;

        for c in self.0.get_deck().waste_iter().enumerate() {
            if c.0 > 0 {
                write!(f, ",")?;
            }
            write!(f, "{}", SolvitaireCard::<false>(c.1))?;
        }
        write!(f, "]")?;

        // foundation
        write!(f, ",\n\"foundation\": [")?;

        for suit in 0..N_SUITS {
            if suit > 0 {
                write!(f, ",")?;
            }

            write!(f, "[")?;
            for rank in 0..self.0.get_stack().get(suit) {
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

#[cfg(test)]
mod tests {
    use std::num::NonZeroU8;

    use lonelybot::{shuffler, standard::StandardSolitaire};
    use serde_json::{json, Value};

    use super::Solvitaire;

    #[test]
    fn test_solvitaire_format() {
        let game = Solvitaire(StandardSolitaire::new(
            &shuffler::ks_shuffle(0),
            NonZeroU8::new(3).unwrap(),
        ));

        let obj: Value = serde_json::from_str(game.to_string().as_str()).unwrap();

        assert_eq!(
            obj,
            json!({"tableau piles": [
                ["3D"],
                ["Ad","8H"],
                ["Qs","9d","8C"],
                ["Jh","2c","3c","AC"],
                ["9c","As","10s","Qc","4S"],
                ["6d","6h","Qh","4d","6s","8D"],
                ["2h","Ks","Js","2s","5d","6c","4H"]
                ],"stock": ["QD","10H","3S","5S","8S","7D","KC","JD","9H","JC","4C","5H","10D","AH","7C","9S","3H","7H","5C","7S","10C","2D","KD","KH"],"waste": [],     
            "foundation": [[],[],[],[]]})
        );
    }
}
