use arrayvec::ArrayVec;

use crate::card::{Card, N_RANKS, N_SUITS};
use crate::deck::{Deck, N_FULL_DECK, N_HIDDEN_CARDS, N_PILES};
use crate::shuffler::CardDeck;
use crate::stack::Stack;

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
    pub final_stack: Stack,
    pub deck: Deck,
    pub hidden_piles: [HiddenVec; N_PILES as usize],
    pub piles: [PileVec; N_PILES as usize],
}

pub type MoveResult<T> = core::result::Result<T, InvalidMove>;

// Define our error types. These may be customized for our error handling cases.
// Now we will be able to write our own errors, defer to an underlying error
// implementation, or do something in between.
#[derive(Debug, Clone, Copy)]
pub struct InvalidMove;

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
            final_stack: Stack::default(),
            deck: Deck::new(
                cards[N_HIDDEN_CARDS as usize..].try_into().unwrap(),
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
        self.final_stack.is_full()
    }

    #[must_use]
    pub const fn get_deck(&self) -> &Deck {
        &self.deck
    }

    #[must_use]
    pub const fn get_stack(&self) -> &Stack {
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

    #[must_use]
    pub fn find_deck_card(&self, card: &Card) -> Option<u8> {
        for i in 0..N_FULL_DECK as u8 {
            let offset = self.deck.offset(i);
            if offset > 0 && self.deck.peek(offset - 1) == card {
                return Some(i);
            }
        }
        None
    }

    #[must_use]
    pub fn find_free_pile(&self, card: &Card) -> Option<u8> {
        self.piles
            .iter()
            .position(|p| p.last().unwrap_or(&Card::FAKE).go_before(card))
            .map(|pos| pos as u8)
    }

    #[must_use]
    pub fn find_top_card(&self, card: &Card) -> Option<u8> {
        self.piles
            .iter()
            .position(|p| p.first() == Some(card))
            .map(|pos| pos as u8)
    }

    #[must_use]
    pub fn find_card_pile(&self, pos: u8, card: &Card) -> Option<usize> {
        self.piles[pos as usize]
            .iter()
            .position(|pile_card| card == pile_card)
    }

    #[must_use]
    pub fn find_card(&self, card: &Card) -> Option<(u8, usize)> {
        for i in 0..N_PILES {
            let pos = self.find_card_pile(i, card).map(|j| (i, j));
            if pos.is_some() {
                return pos;
            }
        }
        None
    }

    #[must_use]
    pub fn validate_move(&self, m: &StandardMove) -> bool {
        match *m {
            (Pos::Deck, Pos::Deck, Card::FAKE) => true,
            (_, Pos::Deck, _) | (Pos::Stack(_), Pos::Stack(_), _) => false,

            (Pos::Deck, Pos::Pile(pos), card) => {
                pos < N_PILES
                    && self.deck.peek_current() == Some(&card)
                    && self.piles[pos as usize]
                        .last()
                        .unwrap_or(&Card::FAKE)
                        .go_before(&card)
            }
            (Pos::Deck, Pos::Stack(suit), card) => {
                suit < N_SUITS
                    && self.deck.peek_current() == Some(&card)
                    && card.suit() == suit
                    && self.final_stack.get(suit) == card.rank()
            }
            (Pos::Pile(from), Pos::Pile(to), card) => {
                from != to
                    && from < N_PILES
                    && to < N_PILES
                    && self.piles[to as usize]
                        .last()
                        .unwrap_or(&Card::FAKE)
                        .go_before(&card)
                    && self.find_card_pile(from, &card).is_some()
            }
            (Pos::Pile(from), Pos::Stack(suit), card) => {
                from < N_PILES
                    && suit < N_SUITS
                    && self.piles[from as usize].last() == Some(&card)
                    && card.suit() == suit
                    && card.rank() == self.final_stack.get(suit)
            }

            (Pos::Stack(suit), Pos::Pile(to), card) => {
                suit < N_SUITS
                    && to < N_PILES
                    && card.suit() == suit
                    && card.rank() + 1 == self.final_stack.get(suit)
                    && self.piles[to as usize]
                        .last()
                        .unwrap_or(&Card::FAKE)
                        .go_before(&card)
            }
        }
    }

    // this will execute the move the move
    // this should never panic
    // if the move is illegal then it won't do anything (the game state will be preserved)
    pub fn do_move(&mut self, m: &StandardMove) -> MoveResult<()> {
        if !self.validate_move(m) {
            return Err(InvalidMove {});
        }
        match *m {
            (Pos::Deck, Pos::Deck, _) => {
                self.deck.deal_once();
            }
            (_, Pos::Deck, _) | (Pos::Stack(_), Pos::Stack(_), _) => {
                unreachable!()
            }

            (Pos::Deck, Pos::Pile(pos), card) => {
                self.deck.draw_current().unwrap();
                self.piles[usize::from(pos)].push(card);
            }
            (Pos::Deck, Pos::Stack(suit), _) => {
                self.deck.draw_current().unwrap();
                self.final_stack.push(suit);
            }
            (Pos::Pile(from), Pos::Pile(to), card) => {
                let pos = self.find_card_pile(from, &card).unwrap();
                let (from, to) = (usize::from(from), usize::from(to));
                let tmp: PileVec = self.piles[from][pos..].iter().copied().collect();
                self.piles[to].extend(tmp);
                self.piles[from].truncate(pos);
            }
            (Pos::Pile(from), Pos::Stack(suit), _) => {
                self.piles[usize::from(from)].pop();
                self.final_stack.push(suit);
            }

            (Pos::Stack(suit), Pos::Pile(to), card) => {
                self.final_stack.pop(suit);
                self.piles[usize::from(to)].push(card);
            }
        };

        // revealing
        if let Pos::Pile(from) = m.0 {
            let from = usize::from(from);
            if self.piles[from].is_empty() {
                if let Some(card) = self.hidden_piles[from].pop() {
                    self.piles[from].push(card);
                }
            }
        }
        Ok(())
    }
}
