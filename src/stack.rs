use crate::{
    card::{Card, COLOR_MASK, N_RANKS, N_SUITS, SUIT_MASK},
    utils::{full_mask, min},
};

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct Stack(u16);

impl Stack {
    #[must_use]
    const fn get_s(self) -> [u8; N_SUITS as usize] {
        [self.get(0), self.get(1), self.get(2), self.get(3)]
    }

    #[must_use]
    pub(crate) const fn mask(self) -> u64 {
        let s = self.get_s();

        (SUIT_MASK[0] & (0b1111 << (s[0] * 4)))
            | (SUIT_MASK[1] & (0b1111 << (s[1] * 4)))
            | (SUIT_MASK[2] & (0b1111 << (s[2] * 4)))
            | (SUIT_MASK[3] & (0b1111 << (s[3] * 4)))
    }

    #[must_use]
    pub(crate) const fn dominance_mask(self) -> u64 {
        let s = self.get_s();
        let d = (min(s[0], s[1]), min(s[2], s[3]));
        let d = (min(d.0 + 1, d.1) + 2, min(d.0, d.1 + 1) + 2);

        (COLOR_MASK[0] & full_mask(d.0 * 4)) | (COLOR_MASK[1] & full_mask(d.1 * 4))
    }

    pub(crate) fn push(&mut self, suit: u8) {
        self.0 += 1 << (suit * 4);
    }

    pub(crate) fn pop(&mut self, suit: u8) {
        self.0 -= 1 << (suit * 4);
    }

    #[must_use]
    pub const fn get(self, suit: u8) -> u8 {
        ((self.0 >> (4 * suit)) as u8) & 0xF
    }

    #[must_use]
    pub const fn stackable(self, card: Card) -> bool {
        self.get(card.suit()) == card.rank()
    }

    #[must_use]
    pub const fn dominance(self, card: Card) -> bool {
        self.dominance_mask() & card.mask() > 0
    }

    #[must_use]
    pub const fn dominance_stackable(self, card: Card) -> bool {
        self.stackable(card) && self.dominance(card)
    }

    pub(crate) fn is_valid(self) -> bool {
        self.get_s().iter().all(|x| *x <= N_RANKS)
    }

    #[must_use]
    pub const fn is_full(self) -> bool {
        self.0 == (N_RANKS as u16 * 0x1111u16)
    }

    #[must_use]
    pub const fn encode(self) -> u16 {
        self.0
    }

    #[must_use]
    pub(crate) const fn decode(encode: u16) -> Self {
        Self(encode)
    }

    #[must_use]
    pub fn len(self) -> u8 {
        self.get_s().iter().sum::<u8>()
    }

    #[must_use]
    pub fn is_empty(self) -> bool {
        self.0 == 0
    }
}
