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
    pub fn new(deck: &[Card; N_FULL_DECK], draw_step: u8) -> Deck {
        let draw_step = core::cmp::min(N_FULL_DECK as u8, draw_step);
        let mut map = [0u8; N_CARDS as usize];
        for (i, c) in deck.iter().enumerate() {
            map[c.value() as usize] = i as u8;
        }

        Deck {
            deck: *deck,
            draw_step,
            draw_next: draw_step,
            draw_cur: draw_step,
            mask: 0,
            map,
        }
    }

    pub const fn draw_step(self: &Deck) -> u8 {
        self.draw_step
    }

    pub const fn len(self: &Deck) -> u8 {
        N_FULL_DECK as u8 - self.draw_next + self.draw_cur
    }

    pub fn find_card(self: &Deck, card: Card) -> Option<u8> {
        self.deck[..self.draw_cur as usize]
            .iter()
            .chain(self.deck[self.draw_next as usize..].iter())
            .enumerate()
            .find(|x| x.1.value() == card.value())
            .map(|x| x.0 as u8)
    }

    pub fn iter_all(self: &Deck) -> impl DoubleEndedIterator<Item = (u8, &Card, Drawable)> {
        let head = self.deck[..self.draw_cur as usize]
            .iter()
            .enumerate()
            .map(|x| {
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

        let tail = self.deck[self.draw_next as usize..]
            .iter()
            .enumerate()
            .map(|x| {
                let pos = x.0 as u8;
                (
                    self.draw_cur + pos,
                    x.1,
                    if pos + 1 == N_FULL_DECK as u8 - self.draw_next
                        || (pos + 1) % self.draw_step == 0
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

    pub fn iter_callback(
        self: &Deck,
        filter: bool,
        mut push: impl FnMut(u8, &Card) -> bool,
    ) -> bool {
        if self.draw_step() == 1 {
            if !filter {
                for (pos, card) in self.deck[..self.draw_cur as usize].iter().enumerate() {
                    if push(pos as u8, card) {
                        return true;
                    }
                }
            }

            for (pos, card) in self.deck[self.draw_next as usize..].iter().enumerate() {
                if push((pos as u8) + self.draw_cur, card) {
                    return true;
                }
            }
            return false;
        }

        if !filter {
            let mut i = self.draw_step - 1;
            while i + 1 < self.draw_cur {
                if push(i, &self.deck[i as usize]) {
                    return true;
                }
                i += self.draw_step;
            }
        }

        if self.draw_cur > 0 {
            if push(self.draw_cur - 1, &self.deck[self.draw_cur as usize - 1]) {
                return true;
            }
        }

        let gap = self.draw_next - self.draw_cur;

        if self.draw_next < N_FULL_DECK as u8 {
            if push(
                N_FULL_DECK as u8 - 1 - gap,
                &self.deck[N_FULL_DECK as usize - 1],
            ) {
                return true;
            }
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

    pub const fn peek_last(self: &Deck) -> Option<&Card> {
        if self.draw_next < N_FULL_DECK as u8 {
            Some(&self.deck[N_FULL_DECK - 1])
        } else if self.draw_cur > 0 {
            Some(&self.deck[self.draw_cur as usize - 1])
        } else {
            None
        }
    }

    pub const fn peek(self: &Deck, id: u8) -> Card {
        debug_assert!(
            self.draw_cur <= self.draw_next
                && (id < N_FULL_DECK as u8 - self.draw_next + self.draw_cur)
        );

        self.deck[if id < self.draw_cur {
            id
        } else {
            id - self.draw_cur + self.draw_next
        } as usize]
    }

    pub fn set_offset(self: &mut Deck, id: u8) {
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

    fn pop_next(self: &mut Deck) -> Card {
        let card = self.deck[self.draw_next as usize];
        self.mask ^= 1 << self.map[card.value() as usize];
        self.draw_next += 1;
        card
    }

    pub fn push(self: &mut Deck, card: Card) {
        // or you can undo
        self.mask ^= 1 << self.map[card.value() as usize];
        self.deck[self.draw_cur as usize] = card;
        self.draw_cur += 1;

        //
        // self.draw_next -= 1;
        // self.deck[self.draw_next as usize] = c;
    }

    pub fn draw(self: &mut Deck, id: u8) -> Card {
        debug_assert!(
            self.draw_cur <= self.draw_next
                && (id < N_FULL_DECK as u8 - self.draw_next + self.draw_cur)
        );
        self.set_offset(id);
        self.pop_next()
    }

    pub const fn get_offset(self: &Deck) -> u8 {
        self.draw_cur
    }

    pub const fn encode(self: &Deck) -> u32 {
        self.mask
    }

    pub const fn is_pure(self: &Deck) -> bool {
        // this will return true if the deck is pure (when deal repeated it will loop back to the current state)
        self.draw_cur % self.draw_step == 0 || self.draw_next == N_FULL_DECK as u8
    }

    pub const fn normalized_offset(self: &Deck) -> u8 {
        // this is the standardized version
        if self.draw_cur % self.draw_step == 0 {
            // matched so offset is free
            0
        } else {
            self.draw_cur
        }
    }
}
