pub const N_SUITS: u8 = 4;
pub const N_RANKS: u8 = 13;
pub const N_CARDS: u8 = N_SUITS * N_RANKS;
pub const KING_RANK: u8 = N_RANKS - 1;

pub const SYMBOLS: [&str; N_SUITS as usize] = ["♥", "♦", "♣", "♠"];
pub const NUMBERS: [&str; N_RANKS as usize] = [
    "A", "2", "3", "4", "5", "6", "7", "8", "9", "10", "J", "Q", "K",
];

pub const SUIT_MASK: [u64; N_SUITS as usize] = [
    0x4141_4141_4141_4141,
    0x8282_8282_8282_8282,
    0x1414_1414_1414_1414,
    0x2828_2828_2828_2828,
];

pub const KING_MASK: u64 = 0xF << (N_SUITS * KING_RANK);

pub const HALF_MASK: u64 = 0x3333_3333_3333_3333;
pub const ALT_MASK: u64 = 0x5555_5555_5555_5555;
pub const RANK_MASK: u64 = 0x1111_1111_1111_1111;

pub const COLOR_MASK: [u64; 2] = [SUIT_MASK[0] | SUIT_MASK[1], SUIT_MASK[2] | SUIT_MASK[3]];

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Card(u8);

impl Card {
    // assume that its rank is larger than all others
    pub const FAKE: Self = Self::new(N_RANKS, 0);

    #[must_use]
    pub const fn new(rank: u8, suit: u8) -> Self {
        debug_assert!(rank <= N_RANKS && suit < N_SUITS);
        Self(rank * N_SUITS + suit)
    }

    #[must_use]
    pub const fn from_value(value: u8) -> Self {
        Self(value)
    }

    #[must_use]
    pub const fn rank(&self) -> u8 {
        self.0 / N_SUITS
    }

    // actually this function check if it is king or fake card
    #[must_use]
    pub const fn is_king(&self) -> bool {
        self.rank() >= KING_RANK
    }

    #[must_use]
    pub const fn suit(&self) -> u8 {
        self.0 % N_SUITS
    }

    #[must_use]
    pub const fn value(&self) -> u8 {
        self.0
    }

    #[must_use]
    pub const fn split(&self) -> (u8, u8) {
        (self.rank(), self.suit())
    }

    #[must_use]
    pub const fn swap_suit(&self) -> Self {
        // keeping the color of the suit and switch to the other type
        // also keeping the rank
        Self(self.0 ^ 1)
    }

    #[must_use]
    pub const fn swap_color(&self) -> Self {
        Self(self.0 ^ 2)
    }

    #[must_use]
    pub const fn reduce_rank(&self) -> Self {
        Self(self.0.saturating_sub(N_SUITS))
    }

    #[must_use]
    pub const fn go_before(&self, other: &Self) -> bool {
        let card_a = self.split();
        let card_b = other.split();
        card_a.0 == card_b.0 + 1 && ((card_a.1 ^ card_b.1) & 2 == 2 || card_a.0 == N_RANKS)
    }

    #[must_use]
    pub const fn mask(&self) -> u64 {
        let v = self.value();
        1u64 << (v ^ ((v >> 1) & 2))
    }

    #[must_use]
    pub const fn from_mask(v: &u64) -> Self {
        #[allow(clippy::cast_possible_truncation)]
        let v = v.trailing_zeros() as u8;
        let v = v ^ ((v >> 1) & 2);
        Self::from_value(v)
    }
}
