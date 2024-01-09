use crate::card::{Card, N_CARDS};

pub const N_PILES: u8 = 7;
pub const N_HIDDEN_CARDS: u8 = N_PILES * (N_PILES - 1) / 2;
pub const N_FULL_DECK: usize = (N_CARDS - N_HIDDEN_CARDS - N_PILES) as usize;

#[derive(Debug)]
struct CardEncoder {
    map_arr: [u32; N_CARDS as usize],
}

impl CardEncoder {
    fn new(deck: &[Card; N_FULL_DECK]) -> CardEncoder {
        let mut map_arr = [0u32; N_CARDS as usize];
        for (i, c) in deck.iter().enumerate() {
            map_arr[c.value() as usize] = 1u32 << i;
        }
        return CardEncoder { map_arr };
    }

    pub fn map(&self, id: Card) -> u32 {
        return self.map_arr[id.value() as usize];
    }
}

#[derive(Debug)]
pub struct Deck {
    deck: [Card; N_FULL_DECK],
    n_deck: u8,
    draw_step: u8,
    draw_next: u8, // start position of next pile
    draw_cur: u8,  // size of the previous pile
    encoder: CardEncoder,
    encoded: u32,
}

fn optional_split_last<T>(slice: &[T]) -> (&[T], Option<&T>) {
    if slice.len() > 0 {
        let (s, v) = slice.split_last().unwrap();
        return (v, Some(s));
    } else {
        return (slice, None);
    }
}

pub enum Drawable {
    None,
    Current,
    Next,
}

fn index_of_unchecked<T>(slice: &[T], item: &T) -> usize {
    if ::std::mem::size_of::<T>() == 0 {
        return 0; // do what you will with this case
    }
    (item as *const _ as usize - slice.as_ptr() as usize) / std::mem::size_of::<T>()
}

impl Deck {
    pub fn new(deck: &[Card; N_FULL_DECK], draw_step: u8) -> Deck {
        assert!(deck.len() == N_FULL_DECK);
        let draw_step = std::cmp::min(N_FULL_DECK as u8, draw_step);

        return Deck {
            deck: *deck,
            n_deck: deck.len() as u8,
            draw_step,
            draw_next: draw_step,
            draw_cur: draw_step,
            encoder: CardEncoder::new(deck),
            encoded: 0,
        };
    }

    pub const fn draw_step(self: &Deck) -> u8 {
        self.draw_step
    }

    pub fn iter(self: &Deck) -> impl Iterator<Item = (usize, &Card)> {
        let n_deck = self.n_deck as usize;
        let draw_cur = self.draw_cur as usize;
        let draw_next = self.draw_next as usize;
        let draw_step = self.draw_step as usize;
        let (head, cur) = optional_split_last(&self.deck[0..draw_cur]);
        let (tail, last) = optional_split_last(&self.deck[draw_next..n_deck]);

        // non redealt

        let offset = draw_step - 1 - (draw_cur % draw_step);

        // filter out if repeat :)
        let offset = if offset == draw_step - 1 {
            n_deck
        } else {
            offset
        };

        return cur
            .into_iter()
            .chain(tail.iter().skip(draw_step - 1).step_by(draw_step))
            .chain(last.into_iter())
            .chain(head.iter().skip(draw_step - 1).step_by(draw_step))
            .chain(tail.iter().skip(offset).step_by(draw_step))
            .map(move |x| {
                let pos = index_of_unchecked(&self.deck, x);
                (
                    if pos >= draw_next {
                        pos - draw_next + draw_cur
                    } else {
                        pos
                    },
                    x,
                )
            });
    }

    pub fn iter_all(self: &Deck) -> impl Iterator<Item = (u8, &Card, Drawable)> {
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

        let tail = self.deck[self.draw_next as usize..self.n_deck as usize]
            .iter()
            .enumerate()
            .map(|x| {
                let pos = x.0 as u8;
                (
                    self.draw_cur + pos,
                    x.1,
                    if pos + 1 == self.n_deck - self.draw_next || (pos + 1) % self.draw_step == 0 {
                        Drawable::Current
                    } else if (self.draw_cur + pos + 1) % self.draw_step == 0 {
                        Drawable::Next
                    } else {
                        Drawable::None
                    },
                )
            });
        return head.chain(tail);
    }

    pub fn peek(self: &Deck, id: u8) -> Card {
        assert!(
            self.draw_cur <= self.draw_next && (id < self.n_deck - self.draw_next + self.draw_cur)
        );

        self.deck[if id < self.draw_cur {
            id
        } else {
            id - self.draw_cur + self.draw_next
        } as usize]
    }

    pub fn draw(self: &mut Deck, id: u8) -> Card {
        assert!(
            self.draw_cur <= self.draw_next && (id < self.n_deck - self.draw_next + self.draw_cur)
        );

        let draw_card = self.peek(id);
        self.encoded ^= self.encoder.map(draw_card);

        let step = if id < self.draw_cur {
            let step = self.draw_cur - id;
            if self.draw_cur != self.draw_next {
                // moving stuff
                self.deck.copy_within(
                    (self.draw_cur - step) as usize..(self.draw_cur as usize),
                    (self.draw_next - step) as usize,
                );
            }
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
        self.draw_next = self.draw_next.wrapping_add(step.wrapping_add(1));
        draw_card
    }

    pub fn encode(self: &Deck) -> u32 {
        let offset = if self.draw_cur % self.draw_step == 0 {
            // matched so offset is free
            0
        } else {
            self.draw_cur
        };
        // this only takes 5 bit <= 32
        return (self.encoded << 5) | (offset as u32);
    }
}
