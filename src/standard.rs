use arrayvec::ArrayVec;

use crate::card::{Card, KING_RANK, N_RANKS, N_SUITS};
use crate::deck::{Deck, N_FULL_DECK, N_PILES};
use crate::shuffler::CardDeck;

pub type PileVec = ArrayVec<Card, { N_RANKS as usize }>;

#[derive(Debug)]
pub enum Pos {
    Deck,
    Stack(u8),
    Pile(u8),
}

pub type StandardMove = (Pos, Pos, Card);

pub const DRAW_NEXT: StandardMove = (Pos::Deck, Pos::Deck, Card::FAKE);

const N_HIDDEN_MAX: usize = (N_PILES - 1) as usize;

const N_PLY_MAX: usize = 1024;

pub type HiddenVec = ArrayVec<Card, N_HIDDEN_MAX>;
pub type StandardHistoryVec = ArrayVec<StandardMove, N_PLY_MAX>;

#[derive(Debug)]
pub struct StandardSolitaire {
    pub final_stack: [u8; N_SUITS as usize],
    pub deck: Deck,
    pub hidden_piles: [HiddenVec; N_PILES as usize],
    pub piles: [PileVec; N_PILES as usize],
}

impl StandardSolitaire {
    pub fn new(cards: &CardDeck, draw_step: u8) -> Self {
        let mut hidden_piles: [HiddenVec; N_PILES as usize] = Default::default();

        for i in 0..N_PILES {
            for j in 0..i {
                let c = cards[(i * (i + 1) / 2 + j) as usize];
                hidden_piles[i as usize].push(c);
            }
        }

        Self {
            hidden_piles,
            final_stack: [0; N_SUITS as usize],
            deck: Deck::new(
                cards[(crate::deck::N_HIDDEN_CARDS) as usize..]
                    .try_into()
                    .unwrap(),
                draw_step,
            ),
            piles: core::array::from_fn(|i| {
                let mut tmp = PileVec::new();
                tmp.push(cards[i * (i + 1) / 2 + i]);
                tmp
            }),
        }
    }

    pub fn is_win(&self) -> bool {
        // What a shame this is not a const function :(
        self.final_stack == [N_RANKS; N_SUITS as usize]
    }

    pub fn peek_waste(&self, n_top: u8) -> ArrayVec<Card, N_FULL_DECK> {
        let mut res = ArrayVec::<Card, N_FULL_DECK>::new();
        let draw_cur = self.deck.get_offset();
        for i in draw_cur.saturating_sub(n_top)..draw_cur {
            res.push(self.deck.peek(i));
        }
        res
    }

    // shouldn't be used in real engine
    #[must_use]
    pub const fn peek_cur(&self) -> Option<Card> {
        if self.deck.get_offset() == 0 {
            None
        } else {
            Some(self.deck.peek(self.deck.get_offset() - 1))
        }
    }

    // shouldn't be used in real engine
    pub fn draw_cur(&mut self) -> Option<Card> {
        if self.deck.get_offset() == 0 {
            None
        } else {
            Some(self.deck.draw(self.deck.get_offset() - 1))
        }
    }

    // shouldn't be used in real engine
    pub fn draw_next(&mut self) {
        let next = self.deck.get_offset();
        let len = self.deck.len();
        let next = if next >= len {
            0
        } else {
            core::cmp::min(next + self.deck.draw_step(), len)
        };
        self.deck.set_offset(next);
    }

    #[must_use]
    pub const fn get_deck(&self) -> &Deck {
        &self.deck
    }

    #[must_use]
    pub const fn get_stack(&self) -> &[u8; N_SUITS as usize] {
        &self.final_stack
    }

    #[must_use]
    pub const fn get_piles(&self) -> &[PileVec; N_PILES as usize] {
        &self.piles
    }

    #[must_use]
    pub const fn get_hidden(&self) -> &[HiddenVec; N_PILES as usize] {
        &self.hidden_piles
    }

    pub fn find_deck_card(&mut self, c: &Card) -> Option<u8> {
        for i in 0..N_FULL_DECK {
            if self.peek_cur() == Some(*c) {
                return Some(i as u8);
            }
            self.draw_next();
        }
        None
    }

    pub fn find_free_pile(&self, c: &Card) -> Option<u8> {
        self.piles
            .iter()
            .position(|p| {
                p.last()
                    .map_or_else(|| c.rank() == KING_RANK, |cc| cc.go_before(c))
            })
            .map(|pos| pos as u8)
    }

    #[must_use]
    pub fn find_top_card(&self, c: &Card) -> Option<u8> {
        self.piles
            .iter()
            .position(|p| p.first() == Some(c))
            .map(|pos| pos as u8)
    }

    #[must_use]
    pub fn find_card(&self, c: &Card) -> Option<(u8, usize)> {
        for i in 0..N_PILES {
            for (j, cc) in self.piles[i as usize].iter().enumerate() {
                if cc == c {
                    return Some((i, j));
                }
            }
        }
        None
    }
}
