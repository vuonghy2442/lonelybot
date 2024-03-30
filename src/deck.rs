use static_assertions::const_assert;

use crate::card::{Card, N_CARDS};

pub const N_PILES: u8 = 7;
pub const N_HIDDEN_CARDS: u8 = N_PILES * (N_PILES + 1) / 2;
pub const N_FULL_DECK: usize = (N_CARDS - N_HIDDEN_CARDS) as usize;

#[derive(Debug, Clone)]
pub struct Deck {
    deck: [Card; N_FULL_DECK],
    draw_step: u8,
    draw_next: u8, // start position of next pile
    draw_cur: u8,  // size of the previous pile
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
    pub fn new(deck: &[Card; N_FULL_DECK], draw_step: u8) -> Self {
        let draw_step = core::cmp::min(N_FULL_DECK as u8, draw_step);
        let mut map = [!0u8; N_CARDS as usize];
        for (i, c) in deck.iter().enumerate() {
            map[c.value() as usize] = i as u8;
        }

        Self {
            deck: *deck,
            draw_step,
            draw_next: draw_step,
            draw_cur: draw_step,
            mask: 0,
            map,
        }
    }

    #[must_use]
    pub const fn draw_step(&self) -> u8 {
        self.draw_step
    }

    #[must_use]
    pub const fn len(&self) -> u8 {
        N_FULL_DECK as u8 - self.draw_next + self.draw_cur
    }

    #[must_use]
    pub const fn is_empty(&self) -> bool {
        self.draw_cur == 0 && self.draw_next == N_FULL_DECK as u8
    }

    #[must_use]
    pub fn find_card(&self, card: Card) -> Option<u8> {
        self.deck[..self.draw_cur as usize]
            .iter()
            .chain(self.deck[self.draw_next as usize..].iter())
            .position(|x| x == &card)
            .map(|x| x as u8)
    }

    #[must_use]
    pub fn get_waste(&self) -> &[Card] {
        &self.deck[..self.draw_cur as usize]
    }

    #[must_use]
    pub fn get_deck(&self) -> &[Card] {
        &self.deck[self.draw_next as usize..]
    }

    #[must_use]
    pub fn iter(&self) -> impl DoubleEndedIterator<Item = &Card> {
        self.get_waste().iter().chain(self.get_deck().iter())
    }

    #[must_use]
    pub fn iter_all(&self) -> impl DoubleEndedIterator<Item = (u8, &Card, Drawable)> {
        let head = self.get_waste().iter().enumerate().map(|x| {
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
        });

        let tail = self.get_deck().iter().enumerate().map(|x| {
            let pos = x.0 as u8;
            (
                self.draw_cur + pos,
                x.1,
                if pos + 1 == N_FULL_DECK as u8 - self.draw_next || (pos + 1) % self.draw_step == 0
                {
                    Drawable::Current
                } else if (self.draw_cur + pos + 1) % self.draw_step == 0 {
                    Drawable::Next
                } else {
                    Drawable::None
                },
            )
        });
        head.chain(tail)
    }

    pub fn iter_callback(&self, filter: bool, mut push: impl FnMut(u8, &Card) -> bool) -> bool {
        // if self.draw_step() == 1 {
        //     if !filter {
        //         for (pos, card) in self.get_waste().iter().enumerate() {
        //             if push(pos as u8, card) {
        //                 return true;
        //             }
        //         }
        //     }

        //     for (pos, card) in self.get_deck().iter().enumerate() {
        //         if push((pos as u8) + self.draw_cur, card) {
        //             return true;
        //         }
        //     }
        //     return false;
        // }

        if !filter {
            let mut i = self.draw_step - 1;
            while i + 1 < self.draw_cur {
                if push(i, &self.deck[i as usize]) {
                    return true;
                }
                i += self.draw_step;
            }
        }

        if self.draw_cur > 0 && push(self.draw_cur - 1, &self.deck[self.draw_cur as usize - 1]) {
            return true;
        }

        let gap = self.draw_next - self.draw_cur;

        if self.draw_next < N_FULL_DECK as u8
            && push(N_FULL_DECK as u8 - 1 - gap, &self.deck[N_FULL_DECK - 1])
        {
            return true;
        }

        {
            let mut i = self.draw_next + self.draw_step - 1;
            while i + 1 < N_FULL_DECK as u8 {
                if push(i - gap, &self.deck[i as usize]) {
                    return true;
                }
                i += self.draw_step;
            }
        }

        {
            let offset = self.draw_cur % self.draw_step;
            if !filter && offset != 0 {
                let mut i = self.draw_next + self.draw_step - 1 - offset;

                while i + 1 < N_FULL_DECK as u8 {
                    if push(i - gap, &self.deck[i as usize]) {
                        return true;
                    }
                    i += self.draw_step;
                }
            }
        }
        false
    }

    #[must_use]
    pub const fn peek_last(&self) -> Option<&Card> {
        if self.draw_next < N_FULL_DECK as u8 {
            Some(&self.deck[N_FULL_DECK - 1])
        } else if self.draw_cur > 0 {
            Some(&self.deck[self.draw_cur as usize - 1])
        } else {
            None
        }
    }

    pub fn set_offset(&mut self, id: u8) {
        // after this the deck will have structure
        // [.... id-1 <empty> id....]
        //   draw_cur ^       ^ draw_next

        let step = if id < self.draw_cur {
            let step = self.draw_cur - id;
            // moving stuff
            self.deck.copy_within(
                (self.draw_cur - step) as usize..(self.draw_cur as usize),
                (self.draw_next - step) as usize,
            );
            step.wrapping_neg()
        } else {
            let step = id - self.draw_cur;

            self.deck.copy_within(
                (self.draw_next) as usize..(self.draw_next + step) as usize,
                self.draw_cur as usize,
            );
            step
        };

        self.draw_cur = self.draw_cur.wrapping_add(step);
        self.draw_next = self.draw_next.wrapping_add(step);
    }

    fn pop_next(&mut self) -> Card {
        let card = self.deck[self.draw_next as usize];
        self.mask ^= 1 << self.map[card.value() as usize];
        self.draw_next += 1;
        card
    }

    pub fn push(&mut self, card: Card) {
        // or you can undo
        self.mask ^= 1 << self.map[card.value() as usize];
        self.deck[self.draw_cur as usize] = card;
        self.draw_cur += 1;

        //
        // self.draw_next -= 1;
        // self.deck[self.draw_next as usize] = c;
    }

    pub fn draw(&mut self, id: u8) -> Card {
        debug_assert!(
            self.draw_cur <= self.draw_next
                && (id < N_FULL_DECK as u8 - self.draw_next + self.draw_cur)
        );
        self.set_offset(id);
        self.pop_next()
    }

    #[must_use]
    pub const fn get_offset(&self) -> u8 {
        self.draw_cur
    }

    #[must_use]
    pub const fn is_pure(&self) -> bool {
        // this will return true if the deck is pure (when deal repeated it will loop back to the current state)
        self.draw_cur % self.draw_step == 0 || self.draw_next == N_FULL_DECK as u8
    }

    #[must_use]
    pub const fn normalized_offset(&self) -> u8 {
        // this is the standardized version
        if self.draw_cur % self.draw_step == 0 {
            // matched so offset is free
            debug_assert!(self.len() <= N_FULL_DECK as u8);
            self.len()
        } else {
            self.draw_cur
        }
    }

    #[must_use]
    pub const fn encode(&self) -> u32 {
        const_assert!(((N_FULL_DECK - 1).ilog2() + 1 + N_FULL_DECK as u32) <= 32);
        // assert the number of bits
        // 29 bits
        self.mask | ((self.normalized_offset() as u32) << N_FULL_DECK)
    }

    pub fn decode(&mut self, encode: u32) {
        let mask = encode & ((1 << N_FULL_DECK) - 1);
        let offset = (encode >> N_FULL_DECK) as u8;

        let mut rev_map = [Card::FAKE; N_FULL_DECK];

        for i in 0..N_CARDS {
            let val = self.map[i as usize];
            if val < N_FULL_DECK as u8 && (encode >> val) & 1 == 0 {
                rev_map[val as usize] = Card::from_value(i);
            }
        }

        let mut pos = 0;

        for c in rev_map {
            if c != Card::FAKE {
                self.deck[pos] = c;
                pos += 1;
            }
        }

        self.draw_cur = pos as u8;
        self.draw_next = N_FULL_DECK as u8;

        self.set_offset(offset);
        self.mask = mask;
    }

    pub fn equivalent_to(&self, other: &Self) -> bool {
        return self
            .iter_all()
            .zip(other.iter_all())
            .all(|x| x.0 .1 == x.1 .1 && (x.0 .2 == Drawable::None) == (x.1 .2 == Drawable::None));
    }
}
