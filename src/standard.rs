use crate::card::{Card, KING_RANK, N_SUITS};
use crate::deck::{Deck, N_FULL_DECK, N_PILES};
use crate::engine::{Move, Solitaire};

#[derive(Debug)]
pub enum Pos {
    Deck,
    Stack(u8),
    Pile(u8),
}

pub type StandardMove = (Pos, Pos, Card);

pub const DRAW_NEXT: StandardMove = (Pos::Deck, Pos::Deck, Card::FAKE);

#[derive(Debug)]
pub struct StandardSolitaire {
    final_stack: [u8; N_SUITS as usize],
    deck: Deck,
    hidden_piles: [Vec<Card>; N_PILES as usize],
    piles: [Vec<Card>; N_PILES as usize],
}

impl StandardSolitaire {
    pub fn new(game: &Solitaire) -> StandardSolitaire {
        let mut hidden_piles: [Vec<Card>; N_PILES as usize] = Default::default();

        for i in 0..N_PILES {
            let n_hid = game.get_n_hidden()[i as usize] - 1;
            for j in 0..n_hid {
                hidden_piles[i as usize].push(game.get_hidden(i, j));
            }
        }

        StandardSolitaire {
            hidden_piles,
            final_stack: *game.get_stack(),
            deck: game.get_deck().clone(),
            piles: game.get_normal_piles(),
        }
    }

    pub fn peek_waste(&self, n_top: u8) -> Vec<Card> {
        let mut res = Vec::<Card>::new();
        let draw_cur = self.deck.get_offset();
        for i in draw_cur.saturating_sub(n_top)..draw_cur {
            res.push(self.deck.peek(i));
        }
        res
    }

    // shouldn't be used in real engine
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
            std::cmp::min(next + self.deck.draw_step(), len)
        };
        self.deck.set_offset(next);
    }

    pub const fn get_deck(&self) -> &Deck {
        &self.deck
    }

    pub const fn get_stack(&self) -> &[u8; N_SUITS as usize] {
        &self.final_stack
    }

    pub const fn get_piles(&self) -> &[Vec<Card>; N_PILES as usize] {
        &self.piles
    }

    pub const fn get_hidden(&self) -> &[Vec<Card>; N_PILES as usize] {
        &self.hidden_piles
    }

    fn find_deck_card(&mut self, c: &Card) -> u8 {
        for i in 0..N_FULL_DECK {
            if self.peek_cur() == Some(*c) {
                return i as u8;
            }
            self.draw_next();
        }
        unreachable!();
    }

    fn find_free_pile(&self, c: &Card) -> u8 {
        for i in 0..N_PILES {
            if let Some(cc) = self.piles[i as usize].last() {
                if cc.go_before(&c) {
                    return i;
                }
            } else if c.rank() == KING_RANK {
                return i;
            }
        }
        unreachable!();
    }

    fn find_top_card(&self, c: &Card) -> u8 {
        for i in 0..N_PILES {
            if Some(c) == self.piles[i as usize].first() {
                return i;
            }
        }
        unreachable!();
    }

    fn find_card(&self, c: &Card) -> (u8, usize) {
        for i in 0..N_PILES {
            for (j, cc) in self.piles[i as usize].iter().enumerate() {
                if cc == c {
                    return (i, j);
                }
            }
        }
        unreachable!();
    }

    pub fn do_move(&mut self, m: &Move, move_seq: &mut Vec<StandardMove>) {
        match m {
            Move::DeckPile(c) => {
                let cnt = self.find_deck_card(c);
                for _ in 0..cnt {
                    move_seq.push(DRAW_NEXT)
                }
                assert_eq!(self.draw_cur(), Some(*c));

                let pile = self.find_free_pile(c);
                self.piles[pile as usize].push(*c);
                move_seq.push((Pos::Deck, Pos::Pile(pile), *c));
            }
            Move::DeckStack(c) => {
                let cnt = self.find_deck_card(c);
                for _ in 0..cnt {
                    move_seq.push(DRAW_NEXT)
                }
                assert_eq!(self.draw_cur(), Some(*c));

                assert!(c.rank() == self.final_stack[c.suit() as usize]);
                self.final_stack[c.suit() as usize] += 1;
                move_seq.push((Pos::Deck, Pos::Stack(c.suit()), *c));
            }
            Move::StackPile(c) => {
                assert!(c.rank() + 1 == self.final_stack[c.suit() as usize]);
                self.final_stack[c.suit() as usize] -= 1;

                let pile = self.find_free_pile(c);
                self.piles[pile as usize].push(*c);
                move_seq.push((Pos::Stack(c.suit()), Pos::Pile(pile), *c));
            }
            Move::Reveal(c) => {
                let pile_from = self.find_top_card(c);
                let pile_to = self.find_free_pile(c);

                assert!(pile_to != pile_from);

                // lazy fix for the borrow checker :)
                self.piles[pile_to as usize].append(&mut self.piles[pile_from as usize].clone());
                self.piles[pile_from as usize].clear();

                if let Some(c) = self.hidden_piles[pile_from as usize].pop() {
                    self.piles[pile_from as usize].push(c);
                }

                move_seq.push((Pos::Pile(pile_from), Pos::Pile(pile_to), *c));
            }
            Move::PileStack(c) => {
                assert!(c.rank() == self.final_stack[c.suit() as usize]);
                let (pile, pos) = self.find_card(c);
                if pos + 1 != self.piles[pile as usize].len() {
                    let pile_other = self.find_free_pile(&self.piles[pile as usize][pos + 1]);

                    assert!(pile != pile_other);

                    self.piles[pile_other as usize]
                        .extend(self.piles[pile as usize].clone()[pos + 1..].iter());
                    move_seq.push((Pos::Pile(pile), Pos::Pile(pile_other), *c));
                }
                self.piles[pile as usize].truncate(pos);

                if pos == 0 {
                    if let Some(c) = self.hidden_piles[pile as usize].pop() {
                        self.piles[pile as usize].push(c);
                    }
                }

                self.final_stack[c.suit() as usize] += 1;
                move_seq.push((Pos::Pile(pile), Pos::Stack(c.suit()), *c));
            }
        }
    }

    pub fn do_moves(&mut self, m: &[Move]) -> Vec<StandardMove> {
        let mut move_seq = Vec::<StandardMove>::new();
        for mm in m {
            self.do_move(mm, &mut move_seq);
        }
        move_seq
    }
}
