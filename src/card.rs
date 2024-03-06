use core::fmt;

pub const N_SUITS: u8 = 4;
pub const N_RANKS: u8 = 13;
pub const N_CARDS: u8 = N_SUITS * N_RANKS;
pub const KING_RANK: u8 = N_RANKS - 1;

pub const SYMBOLS: [&'static str; N_SUITS as usize] = ["♥", "♦", "♣", "♠"];
pub const NUMBERS: [&'static str; N_RANKS as usize] = [
    "A", "2", "3", "4", "5", "6", "7", "8", "9", "10", "J", "Q", "K",
];

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Card(u8);

impl Card {
    // suit = 1 to make sure it turn on the first bit in suit for deck
    pub const FAKE: Card = Card::new(N_RANKS, 1);

    pub const fn new(rank: u8, suit: u8) -> Card {
        debug_assert!(rank <= N_RANKS && suit < N_SUITS);
        return Card(rank * N_SUITS + suit);
    }

    pub const fn rank(self: &Card) -> u8 {
        return self.0 / N_SUITS;
    }

    pub const fn suit(self: &Card) -> u8 {
        return self.0 % N_SUITS;
    }

    pub const fn value(self: &Card) -> u8 {
        return self.0;
    }

    pub const fn split(self: &Card) -> (u8, u8) {
        return (self.rank(), self.suit());
    }

    pub const fn xor_suit(self: &Card, other: &Card) -> u8 {
        let v = self.value() ^ other.value();
        return ((v / 2) ^ (v / N_SUITS)) & 1;
    }

    pub const fn go_before(self: &Card, other: &Card) -> bool {
        let card_a = self.split();
        let card_b = other.split();
        return card_a.0 == card_b.0 + 1 && ((card_a.1 ^ card_b.1) & 2 == 2 || card_a.0 == N_RANKS);
    }

    pub fn print_solvitaire<const LOWER: bool>(
        self: &Card,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result {
        let (rank, suit) = self.split();
        let s = match suit {
            0 => "H",
            1 => "D",
            2 => "C",
            3 => "S",
            _ => "x",
        };
        write!(
            f,
            r#""{}{}""#,
            NUMBERS[rank as usize],
            if LOWER {
                s.to_lowercase()
            } else {
                s.to_owned()
            }
        )
    }
}
