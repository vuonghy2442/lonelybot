use core::mem::swap;

use crate::{
    card::{Card, N_CARDS, N_SUITS},
    deck::N_PILES,
    moves::{Move, MoveMask},
    state::{ExtraInfo, Solitaire},
};

extern crate alloc;
use alloc::vec::Vec;
use arrayvec::ArrayVec;

pub struct DependencyEngine {
    state: Solitaire,
    cards_from: [usize; N_CARDS as usize],
    cards_to: [usize; N_CARDS as usize],
    has_upper: [bool; N_CARDS as usize],
    emptying: ArrayVec<usize, { N_PILES as usize }>,
    last_draw: usize,
    n_moves: usize,
    dep: Vec<(usize, usize)>,
}

impl From<Solitaire> for DependencyEngine {
    fn from(value: Solitaire) -> Self {
        Self::new(value)
    }
}

impl DependencyEngine {
    #[must_use]
    pub fn new(state: Solitaire) -> Self {
        let mut cards = [usize::MAX; N_CARDS as usize];

        let vis = state.compute_visible_piles();
        let mut emptying = ArrayVec::<usize, { N_PILES as usize }>::new();

        let mut has_upper = [false; N_CARDS as usize];

        for pile in vis {
            if pile.is_empty() {
                emptying.push(0);
            }

            let mut prev = false;
            for card in pile {
                has_upper[card.mask_index() as usize] = prev;
                cards[card.mask_index() as usize] = 0;
                prev = true;
            }
        }
        for suit in 0..N_SUITS {
            let rank = state.get_stack().get(suit);
            if rank > 0 {
                cards[Card::new(rank - 1, suit).mask_index() as usize] = 0;
            }
        }

        Self {
            state,
            cards_from: cards,
            cards_to: cards,
            has_upper,
            emptying,
            last_draw: 0,
            n_moves: 0,
            dep: Vec::default(),
        }
    }

    #[must_use]
    pub const fn state(&self) -> &Solitaire {
        &self.state
    }

    #[must_use]
    pub fn into_state(self) -> Solitaire {
        self.state
    }

    #[must_use]
    pub fn is_valid(&self, m: Move) -> bool {
        let moves = self.state.gen_moves::<false>();
        MoveMask::from(m).filter(&moves).is_empty()
    }

    pub fn add_dep(&mut self, from: usize) {
        self.dep.push((from, self.n_moves));
    }

    pub fn get_move_lock(&mut self, card: Card) -> usize {
        if self.has_upper[card.mask_index() as usize] {
            let mut upper = card.increase_rank_swap_color();
            let mut other_upper = upper.swap_suit();
            let mut m_upper = self.cards_to[upper.mask_index() as usize];
            let mut m_other_upper = self.cards_to[other_upper.mask_index() as usize];

            if m_upper < m_other_upper {
                swap(&mut upper, &mut other_upper);
                swap(&mut m_upper, &mut m_other_upper);
            }

            self.cards_to[upper.mask_index() as usize] = self.n_moves;
        }

        let val = self.cards_from[card.mask_index() as usize];
        if val == usize::MAX {
            let other = card.swap_suit();

            self.cards_from
                .swap(card.mask_index() as usize, other.mask_index() as usize);
        }

        self.cards_from[card.mask_index() as usize]
    }

    pub fn get_move_lock_to(&mut self, card: Card) -> usize {
        if card.is_king() {
            self.emptying.pop_at(0).unwrap()
        } else {
            let mut upper = card.increase_rank_swap_color();
            let mut other_upper = upper.swap_suit();
            let mut m_upper = self.cards_to[upper.mask_index() as usize];
            let mut m_other_upper = self.cards_to[other_upper.mask_index() as usize];

            if m_upper > m_other_upper {
                swap(&mut upper, &mut other_upper);
                swap(&mut m_upper, &mut m_other_upper);
            }

            self.cards_to[upper.mask_index() as usize] = usize::MAX;
            self.has_upper[card.mask_index() as usize] = true;

            m_upper
        }
    }

    pub fn do_move(&mut self, m: Move) -> bool {
        if !self.is_valid(m) {
            return false;
        }

        self.n_moves += 1;

        let (_, (_, extra)) = self.state.do_move(m);

        match extra {
            ExtraInfo::Card(new) => {
                self.cards_from[new.mask_index() as usize] = self.n_moves;
                self.cards_to[new.mask_index() as usize] = self.n_moves;
            }
            ExtraInfo::RevealEmpty => {
                self.emptying.push(self.n_moves);
            }
            ExtraInfo::None => {}
        }

        match m {
            Move::DeckStack(card) => {
                self.add_dep(self.last_draw);
                self.last_draw = self.n_moves;

                if card.rank() > 0 {
                    let other = Card::new(card.rank() - 1, card.suit());
                    self.add_dep(self.cards_to[other.mask_index() as usize]);
                    self.cards_to[other.mask_index() as usize] = usize::MAX;
                    self.cards_from[other.mask_index() as usize] = usize::MAX;
                }
                self.cards_to[card.mask_index() as usize] = self.n_moves;
                self.cards_from[card.mask_index() as usize] = self.n_moves;
            }
            Move::PileStack(card) => {
                let from = self.get_move_lock(card);
                self.add_dep(from);

                if card.rank() > 0 {
                    let other = Card::new(card.rank() - 1, card.suit());
                    self.add_dep(self.cards_to[other.mask_index() as usize]);
                    self.cards_to[other.mask_index() as usize] = usize::MAX;
                    self.cards_from[other.mask_index() as usize] = usize::MAX;
                }
                self.cards_to[card.mask_index() as usize] = self.n_moves;
                self.cards_from[card.mask_index() as usize] = self.n_moves;
            }
            Move::DeckPile(card) => {
                self.add_dep(self.last_draw);
                self.last_draw = self.n_moves;

                let from = self.get_move_lock_to(card);
                self.add_dep(from);

                self.cards_to[card.mask_index() as usize] = self.n_moves;
                self.cards_from[card.mask_index() as usize] = self.n_moves;
            }
            Move::StackPile(card) => {
                if card.rank() > 0 {
                    let lower = Card::new(card.rank() - 1, card.suit());
                    self.cards_from[lower.mask_index() as usize] = self.n_moves;
                    self.cards_to[lower.mask_index() as usize] = self.n_moves;
                }

                // from stack
                self.add_dep(self.cards_from[card.mask_index() as usize]);
                let from = self.get_move_lock_to(card);
                // has to have place to put
                self.add_dep(from);

                self.cards_from[card.mask_index() as usize] = self.n_moves;
                self.cards_to[card.mask_index() as usize] = self.n_moves;
            }
            Move::Reveal(card) => {
                let from = self.get_move_lock_to(card);
                self.add_dep(from);

                let from = self.get_move_lock(card);

                self.add_dep(from);
                // self.cards_from[card.mask_index() as usize] = self.n_moves;
                // self.cards_from[card.mask_index() as usize] = self.n_moves;
            }
        }
        true
    }

    #[must_use]
    pub fn get(&self) -> &Vec<(usize, usize)> {
        &self.dep
    }
}
