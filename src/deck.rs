use core::{num::NonZeroU8, ops::ControlFlow};

use arrayvec::ArrayVec;
use static_assertions::const_assert;

use crate::{
    card::{Card, N_CARDS},
    utils::min,
};

pub const N_PILES: u8 = 7;
pub const N_PILE_CARDS: u8 = N_PILES * (N_PILES + 1) / 2;
pub const N_DECK_CARDS: u8 = N_CARDS - N_PILE_CARDS;

#[derive(Debug, Clone)]
pub struct Deck {
    deck: ArrayVec<Card, { N_DECK_CARDS as usize }>,
    draw_step: NonZeroU8,
    draw_cur: u8, // size of the previous pile
    mask: u32,
    map: [u8; N_CARDS as usize],
}

#[derive(Debug, PartialEq, Eq)]
pub enum Drawable {
    None,
    Current,
    Next,
}

impl Deck {
    #[must_use]
    pub fn new(deck: &[Card; N_DECK_CARDS as usize], draw_step: NonZeroU8) -> Self {
        let mut map = [!0u8; N_CARDS as usize];
        #[allow(clippy::cast_possible_truncation)]
        for (i, c) in deck.iter().enumerate() {
            map[c.value() as usize] = i as u8;
        }

        Self {
            deck: ArrayVec::from(*deck),
            draw_step,
            draw_cur: draw_step.get(),
            mask: 0,
            map,
        }
    }

    #[must_use]
    pub const fn draw_step(&self) -> NonZeroU8 {
        self.draw_step
    }

    #[must_use]
    pub const fn len(&self) -> u8 {
        self.deck.len() as u8
    }

    #[must_use]
    pub const fn is_empty(&self) -> bool {
        self.deck.is_empty()
    }

    #[must_use]
    pub fn find_card(&self, card: Card) -> Option<u8> {
        #[allow(clippy::cast_possible_truncation)]
        self.deck.iter().position(|x| x == &card).map(|x| x as u8)
    }

    #[must_use]
    pub fn get_waste(&self) -> &[Card] {
        &self.deck[..self.draw_cur as usize]
    }

    #[must_use]
    pub fn get_deck(&self) -> &[Card] {
        &self.deck[self.draw_cur as usize..]
    }

    #[must_use]
    pub fn iter(&self) -> &[Card] {
        &self.deck[..]
    }

    #[must_use]
    pub fn iter_waste(
        &self,
    ) -> impl DoubleEndedIterator<Item = (u8, &Card, Drawable)> + ExactSizeIterator {
        self.get_waste().iter().enumerate().map(|x| {
            #[allow(clippy::cast_possible_truncation)]
            let pos = x.0 as u8;
            (
                pos,
                x.1,
                if pos + 1 == self.draw_cur {
                    Drawable::Current
                } else if (pos + 1) % self.draw_step == 0 {
                    Drawable::Next
                } else {
                    Drawable::None
                },
            )
        })
    }

    #[must_use]
    pub fn iter_deck(
        &self,
    ) -> impl DoubleEndedIterator<Item = (u8, &Card, Drawable)> + ExactSizeIterator {
        self.get_deck().iter().enumerate().map(|x| {
            #[allow(clippy::cast_possible_truncation)]
            let pos = x.0 as u8;
            let true_pos = self.draw_cur + pos;
            (
                true_pos,
                x.1,
                if true_pos + 1 == self.len() || (pos + 1) % self.draw_step == 0 {
                    Drawable::Current
                } else if (true_pos + 1) % self.draw_step == 0 {
                    Drawable::Next
                } else {
                    Drawable::None
                },
            )
        })
    }

    #[must_use]
    pub fn peek(&self, pos: u8) -> &Card {
        &self.deck[pos as usize]
    }

    #[must_use]
    pub fn iter_all(&self) -> impl DoubleEndedIterator<Item = (u8, &Card, Drawable)> {
        self.iter_waste().chain(self.iter_deck())
    }

    #[must_use]
    pub const fn offset(&self, n_step: u8) -> u8 {
        let next = self.get_offset();
        let len = self.len();
        let step = self.draw_step();

        let n_step_to_end = (len - next).div_ceil(step.get());

        min(
            if n_step <= n_step_to_end {
                next + step.get() * n_step
            } else {
                let total_step = len.div_ceil(step.get()) + 1;
                let n_step = (n_step - n_step_to_end - 1) % total_step;
                step.get() * n_step
            },
            len,
        )
    }

    #[must_use]
    pub const fn offset_once(&self, cur: u8) -> u8 {
        let len = self.len();
        if cur >= len {
            0
        } else {
            min(cur + self.draw_step().get(), len)
        }
    }

    pub fn iter_callback<T, F: FnMut(u8, &Card) -> ControlFlow<T>>(
        &self,
        filter: bool,
        mut func: F,
    ) -> ControlFlow<T> {
        {
            let mut i = self.draw_cur
                + if self.draw_cur == 0 {
                    self.draw_step.get()
                } else {
                    0
                }
                - 1;
            while i < self.len().saturating_sub(1) {
                func(i, &self.deck[i as usize])?;
                i += self.draw_step.get();
            }
        }

        if self.len() > 0 {
            func(self.len() - 1, &self.deck.last().unwrap())?;
        }

        if !filter {
            let mut i = self.draw_step.get() - 1;

            let offset = self.draw_cur % self.draw_step;
            let end = if offset != 0 {
                self.len()
            } else {
                self.draw_cur
            }
            .saturating_sub(1);

            while i < end {
                func(i, &self.deck[i as usize])?;
                i += self.draw_step.get();
            }
        }
        ControlFlow::Continue(())
    }

    #[must_use]
    pub fn peek_last(&self) -> Option<&Card> {
        self.deck.last()
    }

    pub(crate) fn set_offset(&mut self, id: u8) {
        self.draw_cur = id;
    }

    fn pop_next(&mut self) -> Card {
        self.draw_cur -= 1;
        let card = self.deck.remove(self.draw_cur as usize);
        self.mask ^= 1 << self.map[card.value() as usize];
        card
    }

    pub(crate) fn push(&mut self, card: Card) {
        // or you can undo
        self.mask ^= 1 << self.map[card.value() as usize];
        self.deck.insert(self.draw_cur as usize, card);
        self.draw_cur += 1;
    }

    pub(crate) fn draw(&mut self, id: u8) -> Card {
        self.set_offset(id + 1);
        self.pop_next()
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

        let mut rev_map = [None; N_DECK_CARDS as usize];

        for i in 0..N_CARDS {
            let val = self.map[i as usize];
            if val < N_DECK_CARDS && (encode >> val) & 1 == 0 {
                rev_map[val as usize] = Some(Card::from_value(i));
            }
        }

        let mut pos: u8 = 0;

        for c in rev_map.into_iter().flatten() {
            self.deck[pos as usize] = c;
            pos += 1;
        }

        self.deck.truncate(pos as usize);

        self.set_offset(offset);
        self.mask = mask;
    }

    #[must_use]
    pub fn equivalent_to(&self, other: &Self) -> bool {
        return self
            .iter_all()
            .zip(other.iter_all())
            .all(|x| x.0 .1 == x.1 .1 && (x.0 .2 == Drawable::None) == (x.1 .2 == Drawable::None));
    }

    pub fn deal_once(&mut self) {
        self.set_offset(self.offset_once(self.get_offset()));
    }

    #[must_use]
    pub fn peek_waste<const N: usize>(&self) -> ArrayVec<Card, N> {
        let draw_cur = self.get_offset();
        #[allow(clippy::cast_possible_truncation)]
        self.get_waste()
            .split_at(draw_cur.saturating_sub(N as u8).into())
            .1
            .iter()
            .copied()
            .collect()
    }

    #[must_use]
    pub fn peek_current(&self) -> Option<&Card> {
        if self.draw_cur == 0 {
            None
        } else {
            Some(&self.deck[self.draw_cur as usize - 1])
        }
    }

    pub fn draw_current(&mut self) -> Option<Card> {
        let offset = self.get_offset();
        if offset == 0 {
            None
        } else {
            Some(self.draw(offset - 1))
        }
    }
}

#[cfg(test)]
mod tests {
    use rand::{rngs::StdRng, Rng, SeedableRng};

    use crate::shuffler::default_shuffle;

    use super::*;

    #[test]
    fn test_draw() {
        let mut rng = StdRng::seed_from_u64(14);

        for i in 0..100 {
            let deck = default_shuffle(12 + i);
            let deck = deck[..N_DECK_CARDS as usize].try_into().unwrap();

            let draw_step = NonZeroU8::new(rng.gen_range(1..5)).unwrap();
            let mut deck = Deck::new(deck, draw_step);

            while !deck.is_empty() {
                let mut cur = deck.get_offset();
                for i in 0..N_DECK_CARDS {
                    assert_eq!(cur, deck.offset(i));
                    cur = deck.offset_once(cur);
                }
                let step = rng.gen_range(1..100);
                let offset = deck.offset(step);

                for _ in 0..step {
                    deck.deal_once();
                }

                assert_eq!(offset, deck.get_offset());

                for (pos, card, _) in deck.iter_all() {
                    assert_eq!(deck.peek(pos), card);
                }

                for filter in [false, true] {
                    deck.iter_callback(filter, |pos, card| {
                        assert_eq!(deck.peek(pos), card);
                        ControlFlow::<()>::Continue(())
                    });
                }

                if deck.get_offset() > 0 && rng.gen_bool(0.5) {
                    deck.pop_next();
                }
            }
        }
    }
}
