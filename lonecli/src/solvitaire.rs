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

        for c in self.0.get_deck().get().iter().rev().enumerate() {
            if c.0 > 0 {
                write!(f, ",")?;
            }
            write!(f, "{}", SolvitaireCard::<false>(*c.1))?;
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
    use lonelybot::{shuffler, standard::StandardSolitaire};
    use serde_json::{json, Value};

    use crate::DRAW_STEP;

    use super::Solvitaire;

    #[test]
    fn test_solvitaire_format() {
        let game = Solvitaire(StandardSolitaire::new(
            &shuffler::default_shuffle(0),
            DRAW_STEP,
        ));
        let obj: Value = serde_json::from_str(game.to_string().as_str()).unwrap();

        assert_eq!(
            obj,
            json!({"tableau piles": [
            ["KC"],
            ["6s","8C"],
            ["9s","Ah","5S"],
            ["5d","Js","5h","QD"],
            ["Ac","7c","Jc","7h","KD"],
            ["10c","3h","4d","4h","6c","QS"],
            ["7d","3c","6h","5c","10h","9c","3S"]
            ],"stock": ["JD","10D","7S","10S","AD","8S","JH","2D","AS","3D","9D","9H","6D","KS","QH","2H","2S","4S","4C","KH","2C","8H","8D","QC"],
            "foundation": [[],[],[],[]]})
        );
    }
}
