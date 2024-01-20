use crate::card::{Card, N_CARDS};

pub const N_PILES: u8 = 7;
pub const N_HIDDEN_CARDS: u8 = N_PILES * (N_PILES - 1) / 2;
pub const N_FULL_DECK: usize = (N_CARDS - N_HIDDEN_CARDS - N_PILES) as usize;

#[derive(Debug)]
pub struct Deck {
    deck: [Card; N_FULL_DECK],
    draw_step: u8,
    draw_next: u8, // start position of next pile
    draw_cur: u8,  // size of the previous pile
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
        let draw_step = std::cmp::min(N_FULL_DECK as u8, draw_step);

        return Deck {
            deck: *deck,
            draw_step,
            draw_next: draw_step,
            draw_cur: draw_step,
        };
    }

    pub const fn draw_step(self: &Deck) -> u8 {
        self.draw_step
    }

    pub fn iter(self: &Deck) -> impl Iterator<Item = (usize, &Card)> {
        let draw_cur = self.draw_cur as usize;
        let draw_next = self.draw_next as usize;
        let draw_step = self.draw_step as usize;
        let (head, cur) = optional_split_last(&self.deck[..draw_cur]);
        let (tail, last) = optional_split_last(&self.deck[draw_next..]);

        // non redealt

        let offset = draw_step - 1 - (draw_cur % draw_step);

        // filter out if repeat :)
        let offset = if offset == draw_step - 1 {
            N_FULL_DECK
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

    pub const fn len(self: &Deck) -> u8 {
        N_FULL_DECK as u8 - self.draw_next + self.draw_cur
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
        return head.chain(tail);
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

    pub fn pop_next(self: &mut Deck) -> Card {
        let card = self.deck[self.draw_next as usize];
        self.draw_next += 1;
        card
    }

    pub fn push(self: &mut Deck, c: Card) {
        // or you can undo
        self.deck[self.draw_cur as usize] = c;
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

    pub const fn encode_offset(self: &Deck) -> u8 {
        // this is the standardized version
        if (self.draw_cur + 1) % self.draw_step == 0 {
            // matched so offset is free
            self.draw_step - 1
        } else {
            self.draw_cur
        }
    }
}
