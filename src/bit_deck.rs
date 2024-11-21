use core::num::NonZeroU8;

use arrayvec::ArrayVec;
use bitintr::Pdep;
use static_assertions::const_assert;

use crate::{
    card::{Card, N_CARDS},
    deck::{compute_map, Deck, N_DECK_CARDS},
    utils::full_mask,
};

#[derive(Debug, Clone)]
pub struct BitDeck {
    // fixed
    deck: [Card; N_DECK_CARDS as usize],
    draw_step: NonZeroU8,
    map: [u8; N_CARDS as usize],
    skip_mask: u32,

    // modifying
    draw_cur: u8,
    mask: u32,
}

const fn gap_bit_mask(gap: u8) -> u32 {
    let mut mask: u32 = 1 << gap;
    let mut shift = gap + 1;

    while shift < 32 {
        mask |= mask << shift;
        shift <<= 1;
    }

    mask
}

fn expand(mut x: u32, mut m: u32) -> u32 {
    let m0 = m; // Save original mask.
    let mut mk = !m << 1; // We will count 0's to right.
    let array: [u32; 5] = core::array::from_fn(|i| {
        let mp = mk ^ (mk << 1); // Parallel suffix.
        let mp = mp ^ (mp << 2);
        let mp = mp ^ (mp << 4);
        let mp = mp ^ (mp << 8);
        let mp = mp ^ (mp << 16);
        let mv = mp & m; // Bits to move.
        m = (m ^ mv) | (mv >> (1 << i)); // Compress m.
        mk = mk & !mp;
        mv
    });

    for (i, mv) in array.iter().enumerate().rev() {
        let t = x << (1 << i);
        x = (x & !mv) | (t & mv);
    }
    return x & m0; // Clear out extraneous bits.
}

#[derive(Debug, PartialEq, Eq)]
pub enum Drawable {
    None,
    Current,
    Next,
}

const fn pdep_(value: u32, mut mask: u32) -> u32 {
    let mut res = 0;
    let mut bb = 1;
    loop {
        if mask == 0 {
            break;
        }
        if (value & bb) != 0 {
            res |= mask & mask.wrapping_neg();
        }
        mask &= mask - 1;
        bb += bb;
    }
    res
}

impl BitDeck {
    #[must_use]
    pub fn new(deck: [Card; N_DECK_CARDS as usize], draw_step: NonZeroU8) -> Self {
        Self {
            map: compute_map(&deck),
            deck,
            draw_step,
            skip_mask: gap_bit_mask(draw_step.get() - 1),
            draw_cur: 0,
            mask: full_mask(N_DECK_CARDS) as u32,
        }
    }

    #[must_use]
    pub const fn draw_step(&self) -> NonZeroU8 {
        self.draw_step
    }

    #[must_use]
    pub const fn len(&self) -> u8 {
        self.mask.count_ones() as u8
    }

    #[must_use]
    pub const fn is_empty(&self) -> bool {
        self.mask == 0
    }

    #[must_use]
    pub(crate) const fn find_card(&self, card: Card) -> (bool, u8) {
        // return !0 if can't find :)
        let idx = self.map[card.mask_index() as usize];
        (idx < 32 && (self.mask >> idx) & 1 > 0, idx)
    }

    pub(crate) fn set_offset(&mut self, id: u8) {
        self.draw_cur = id;
    }

    pub(crate) fn pop_next(&mut self) {
        let m = (1 << self.draw_cur) >> 1;
        self.mask ^= m;
        self.draw_cur = (self.mask & (m.wrapping_sub(1))).count_ones() as u8; //it will be self.len when m == 0
    }

    pub(crate) fn push(&mut self, card: Card) {
        // or you can undo
        self.mask ^= 1 << self.find_card(card).1;
    }

    #[must_use]
    pub(crate) fn drawable_mask(&self, filter: bool) -> u32 {
        let mask =
            (self.skip_mask << self.draw_cur) | (((1 << self.draw_cur) | (1 << self.len())) >> 1);
        let mask = mask | if filter { 0 } else { self.skip_mask };

        // mask.pdep(self.mask)
        // expand(mask, self.mask)
        pdep_(mask, self.mask)
    }

    #[must_use]
    pub(crate) const fn get_card_mask(&self, mut mask: u32) -> u64 {
        let mut res = 0;
        while mask > 0 {
            let pos = mask.trailing_zeros();
            res |= self.deck[pos as usize].mask();
            mask &= mask - 1;
        }
        res
    }

    #[must_use]
    pub(crate) const fn full_card_mask(&self) -> u64 {
        self.get_card_mask(self.mask)
    }

    pub(crate) fn compute_mask(&self, filter: bool) -> u64 {
        self.get_card_mask(self.drawable_mask(filter))
    }

    #[must_use]
    pub const fn full_mask(&self) -> u32 {
        self.mask
    }

    #[must_use]
    pub const fn peek(&self, pos: u8) -> Card {
        self.deck[pos as usize]
    }

    pub(crate) const fn peek_last(&self) -> Option<Card> {
        if let Some(p) = self.mask.checked_ilog2() {
            Some(self.deck[p as usize])
        } else {
            None
        }
    }

    #[must_use]
    pub(crate) const fn get_offset(&self) -> u8 {
        self.draw_cur
    }

    #[must_use]
    pub const fn is_pure(&self) -> bool {
        // this will return true if the deck is pure (when deal repeated it will loop back to the current state)
        self.draw_cur % self.draw_step.get() == 0 || self.draw_cur == self.len()
    }

    #[must_use]
    pub(crate) const fn normalized_offset(&self) -> u8 {
        // this is the standardized version
        if self.is_pure() {
            self.len()
        } else {
            self.draw_cur
        }
    }

    #[must_use]
    pub const fn encode(&self) -> u32 {
        const_assert!(((N_DECK_CARDS - 1).ilog2() + 1 + N_DECK_CARDS as u32) <= 32);
        // assert the number of bits
        // 29 bits
        self.mask | ((self.normalized_offset() as u32) << N_DECK_CARDS)
    }

    pub(crate) fn decode(&mut self, encode: u32) {
        let mask = encode & ((1 << N_DECK_CARDS) - 1);
        let offset = (encode >> N_DECK_CARDS) as u8;

        self.mask = mask;
        self.set_offset(offset);
        self.mask = mask;
    }

    pub(crate) fn draw(&mut self, id: u8) {
        self.set_offset(id + 1);
        self.pop_next();
    }

    #[cfg(test)]
    #[must_use]
    pub fn equivalent_to(&self, other: &Self) -> bool {
        Into::<Deck>::into(self).equivalent_to(&other.into())
    }
}

impl From<&BitDeck> for Deck {
    fn from(value: &BitDeck) -> Self {
        let mut deck = ArrayVec::<Card, { N_DECK_CARDS as usize }>::new();

        let mut mask = value.mask;

        while mask > 0 {
            let pos = mask.trailing_zeros();
            deck.push(value.deck[pos as usize]);
            mask &= mask - 1;
        }

        let mut deck = Deck::new(&deck, value.draw_step);
        deck.set_offset(value.get_offset());
        deck
    }
}

impl From<&Deck> for BitDeck {
    fn from(value: &Deck) -> Self {
        // TODO: Fix this :))
        let mut deck: ArrayVec<Card, { N_DECK_CARDS as usize }> = value.iter().collect();
        let n_cards = deck.len();

        while !deck.is_full() {
            deck.push(Card::DEFAULT);
        }

        let draw_step = value.draw_step();
        Self {
            map: compute_map(&deck[..n_cards]),
            deck: deck.into_inner().unwrap(),
            draw_step,
            skip_mask: gap_bit_mask(draw_step.get() - 1),
            draw_cur: value.get_offset(),
            mask: full_mask(n_cards as u8) as u32,
        }
    }
}
