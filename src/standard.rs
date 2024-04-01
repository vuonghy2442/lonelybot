use arrayvec::ArrayVec;

use crate::card::{Card, N_RANKS, N_SUITS};
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
    #[must_use]
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

    #[must_use]
    pub fn is_win(&self) -> bool {
        // What a shame this is not a const function :(
        self.final_stack == [N_RANKS; N_SUITS as usize]
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

    pub fn find_deck_card(&self, c: &Card) -> Option<u8> {
        for i in 0..N_FULL_DECK as u8 {
            let offset = self.deck.offset(i);
            if offset > 0 && self.deck.peek(offset - 1) == c {
                return Some(i);
            }
        }
        None
    }

    #[must_use]
    pub fn find_free_pile(&self, c: &Card) -> Option<u8> {
        self.piles
            .iter()
            .position(|p| p.last().unwrap_or(&Card::FAKE).go_before(c))
            .map(|pos| pos as u8)
    }

    #[must_use]
    pub fn find_top_card(&self, c: &Card) -> Option<u8> {
        self.piles
            .iter()
            .position(|p| p.first() == Some(c))
            .map(|pos| pos as u8)
    }

    pub fn find_card_pile(&self, pos: u8, c: &Card) -> Option<usize> {
        self.piles[pos as usize].iter().position(|cc| *c == *cc)
    }

    #[must_use]
    pub fn find_card(&self, c: &Card) -> Option<(u8, usize)> {
        for i in 0..N_PILES {
            let pos = self.find_card_pile(i, c).map(|j| (i, j));
            if pos.is_some() {
                return pos;
            }
        }
        None
    }

    pub fn validate_move(&self, m: &StandardMove) -> bool {
        match *m {
            (Pos::Deck, Pos::Deck, Card::FAKE) => true,
            (_, Pos::Deck, _) => false,
            (Pos::Stack(_), Pos::Stack(_), _) => false,

            (Pos::Deck, Pos::Pile(pos), c) => {
                pos < N_PILES
                    && self.deck.peek_current() == Some(&c)
                    && self.piles[pos as usize]
                        .last()
                        .unwrap_or(&Card::FAKE)
                        .go_before(&c)
            }
            (Pos::Deck, Pos::Stack(pos), c) => {
                pos < N_SUITS
                    && self.deck.peek_current() == Some(&c)
                    && c.suit() == pos
                    && self.final_stack[pos as usize] == c.rank()
            }
            (Pos::Pile(from), Pos::Pile(to), c) => {
                from != to
                    && from < N_PILES
                    && to < N_PILES
                    && self.piles[to as usize]
                        .last()
                        .unwrap_or(&Card::FAKE)
                        .go_before(&c)
                    && self.find_card_pile(from, &c).is_some()
            }
            (Pos::Pile(from), Pos::Stack(to), c) => {
                from < N_PILES
                    && to < N_SUITS
                    && self.piles[from as usize].last() == Some(&c)
                    && c.suit() == to
                    && c.rank() == self.final_stack[to as usize]
            }

            (Pos::Stack(from), Pos::Pile(to), c) => {
                from < N_SUITS
                    && to < N_PILES
                    && c.suit() == from
                    && c.rank() + 1 == self.final_stack[from as usize]
                    && self.piles[to as usize]
                        .last()
                        .unwrap_or(&Card::FAKE)
                        .go_before(&c)
            }
        }
    }

    // this will execute the move the move
    // this should never panic
    // if the move is illegal then it won't do anything (the game state will be preserved)
    pub fn do_move(&mut self, m: &StandardMove) -> bool {
        if !self.validate_move(m) {
            return false;
        }
        match *m {
            (Pos::Deck, Pos::Deck, _) => {
                self.deck.deal_once();
            }
            (_, Pos::Deck, _) => {}

            (Pos::Deck, Pos::Pile(pos), c) => {
                self.deck.draw_current().unwrap();
                self.piles[pos as usize].push(c);
            }
            (Pos::Deck, Pos::Stack(pos), _) => {
                self.deck.draw_current().unwrap();
                self.final_stack[pos as usize] += 1;
            }
            (Pos::Pile(from), Pos::Pile(to), c) => {
                let pos = self.find_card_pile(from, &c).unwrap();
                let tmp: PileVec = self.piles[from as usize][pos..].iter().copied().collect();
                self.piles[to as usize].extend(tmp);
                self.piles[from as usize].truncate(pos);

                if self.piles[from as usize].is_empty() {
                    if let Some(c) = self.hidden_piles[from as usize].pop() {
                        self.piles[from as usize].push(c);
                    }
                }
            }
            (Pos::Pile(from), Pos::Stack(to), _) => {
                self.piles[from as usize].pop();
                self.final_stack[to as usize] += 1;

                if self.piles[from as usize].is_empty() {
                    if let Some(c) = self.hidden_piles[from as usize].pop() {
                        self.piles[from as usize].push(c);
                    }
                }
            }

            (Pos::Stack(from), Pos::Pile(to), c) => {
                self.final_stack[from as usize] -= 1;
                self.piles[to as usize].push(c);
            }

            (Pos::Stack(_), Pos::Stack(_), _) => {}
        };
        true
    }
}
