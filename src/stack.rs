use crate::{
    card::{Card, COLOR_MASK, N_RANKS, N_SUITS, SUIT_MASK},
    utils::{full_mask, min},
};

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct Stack([u8; N_SUITS as usize]);

impl Stack {
    #[must_use]
    pub const fn mask(&self) -> u64 {
        let s = &self.0;

        (SUIT_MASK[0] & (0b1111 << (s[0] * 4)))
            | (SUIT_MASK[1] & (0b1111 << (s[1] * 4)))
            | (SUIT_MASK[2] & (0b1111 << (s[2] * 4)))
            | (SUIT_MASK[3] & (0b1111 << (s[3] * 4)))
    }

    #[must_use]
    pub const fn dominance_mask(&self) -> u64 {
        let s = &self.0;
        let d = (min(s[0], s[1]), min(s[2], s[3]));
        let d = (min(d.0 + 1, d.1) + 2, min(d.0, d.1 + 1) + 2);

        (COLOR_MASK[0] & full_mask(d.0 * 4)) | (COLOR_MASK[1] & full_mask(d.1 * 4))
    }

    pub fn push(&mut self, suit: u8) {
        self.0[usize::from(suit)] += 1;
    }

    pub fn pop(&mut self, suit: u8) {
        self.0[usize::from(suit)] -= 1;
    }

    #[must_use]
    pub const fn get(&self, suit: u8) -> u8 {
        self.0[suit as usize]
    }

    #[must_use]
    pub const fn stackable(&self, card: &Card) -> bool {
        self.get(card.suit()) == card.rank()
    }

    #[must_use]
    pub const fn dominance(&self, card: &Card) -> bool {
        let stack = &self.0;
        let rank = card.rank();
        let suit = card.suit() as usize;
        // allowing worrying back :)
        rank <= stack[suit ^ 2] + 1
            && rank <= stack[suit ^ 2 ^ 1] + 1
            && rank <= stack[suit ^ 1] + 2
    }

    #[must_use]
    pub const fn dominance_stackable(&self, card: &Card) -> bool {
        self.stackable(card) && self.dominance(card)
    }

    #[must_use]
    pub fn is_full(&self) -> bool {
        // What a shame this is not a const function :(
        self.0 == [N_RANKS; N_SUITS as usize]
    }

    // can be made const fn
    #[must_use]
    pub fn encode(&self) -> u16 {
        // considering to make it incremental?
        self.0
            .iter()
            .rev()
            .fold(0u16, |res, cur| (res << 4) + u16::from(*cur))
    }

    #[must_use]
    pub fn decode(encode: u16) -> Self {
        #[allow(clippy::cast_possible_truncation)]
        Self(core::array::from_fn(|i| (encode >> (4 * i)) as u8 & 0xF))
    }

    #[must_use]
    pub fn len(&self) -> u8 {
        self.0.iter().sum::<u8>()
    }

    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.0 == [0; N_SUITS as usize]
    }
}
