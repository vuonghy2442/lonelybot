use core::fmt;

use crate::card::{Card, N_CARDS, N_RANKS, N_SUITS};
use crate::deck::{Deck, Drawable, N_HIDDEN_CARDS, N_PILES};
use crate::pile::Pile;

use concat_arrays::concat_arrays;

use colored::Colorize;
use rand::prelude::*;

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Copy)]
pub enum Pos {
    Deck(u8),
    Stack(u8),
    Pile(u8),
}

pub type CardDeck = [Card; N_CARDS as usize];
pub type MoveType = (Pos, Pos);

pub struct UndoInfo {
    offset: u8,
    hidden: Option<Pile>,
}

#[derive(Debug)]
pub struct Solitaire {
    hidden_piles: [Card; N_HIDDEN_CARDS as usize],
    n_hidden: [u8; N_PILES as usize],

    // start card ends card and flags
    visible_piles: [Pile; N_PILES as usize],
    final_stack: [u8; N_SUITS as usize],
    deck: Deck,
}

pub fn generate_shuffled_deck(seed: u64) -> CardDeck {
    let mut rng = StdRng::seed_from_u64(seed);
    let mut cards: [Card; N_CARDS as usize] =
        core::array::from_fn(|i| Card::new(i as u8 / N_SUITS, i as u8 % N_SUITS));
    cards.shuffle(&mut rng);
    return cards;
}
pub type Encode = [u16; N_PILES as usize + 2];

impl Solitaire {
    pub fn new(cards: &CardDeck, draw_step: u8) -> Solitaire {
        let hidden_piles: [Card; N_HIDDEN_CARDS as usize] =
            cards[0..N_HIDDEN_CARDS as usize].try_into().unwrap();
        let n_hidden: [u8; N_PILES as usize] = core::array::from_fn(|i| i as u8);

        let visible_cards: &[Card; N_PILES as usize] = cards
            [N_HIDDEN_CARDS as usize..(N_HIDDEN_CARDS + N_PILES) as usize]
            .try_into()
            .unwrap();

        let visible_piles: [Pile; N_PILES as usize] = visible_cards.map(|c| Pile::from_card(c));

        let deck: Deck = Deck::new(
            cards[(N_HIDDEN_CARDS + N_PILES) as usize..]
                .try_into()
                .unwrap(),
            draw_step,
        );

        let final_stack: [u8; 4] = [0u8; 4];

        return Solitaire {
            hidden_piles,
            n_hidden,
            visible_piles,
            final_stack,
            deck,
        };
    }

    pub fn is_win(self: &Solitaire) -> bool {
        // What a shame this is not a const function :(
        return self.final_stack == [N_RANKS; N_SUITS as usize];
    }

    fn push_pile(self: &mut Solitaire, id: u8, card: Card) {
        self.visible_piles[id as usize].push(card);
    }

    fn pop_pile(self: &mut Solitaire, id: u8, step: u8) {
        self.visible_piles[id as usize].pop(step);
    }

    fn move_pile(self: &mut Solitaire, from: u8, to: u8) {
        let (from, to) = (from as usize, to as usize);
        let (new_from, new_to) = self.visible_piles[from].move_to_(&self.visible_piles[to]);
        self.visible_piles[from] = new_from;
        self.visible_piles[to] = new_to;
    }

    fn pop_hidden(self: &mut Solitaire, pos: u8) -> Card {
        let ref mut n_hid = self.n_hidden[pos as usize];
        if *n_hid == 0 {
            return Card::FAKE;
        } else {
            *n_hid -= 1;
            return self.hidden_piles[(pos * (pos - 1) / 2 + *n_hid) as usize];
        }
    }

    const fn stack_dominance(self: &Solitaire, rank: u8, suit: u8) -> bool {
        let stack = &self.final_stack;
        let suit = suit as usize;
        // allowing worring back :)
        rank <= stack[suit ^ 2] + 2 && rank <= stack[suit ^ 2 ^ 1] + 2 && rank <= stack[suit ^ 1]
    }

    pub fn gen_moves_(self: &Solitaire, moves: &mut Vec<MoveType>) {
        let start_len = moves.len();
        // src = src.Deck
        for (pos, card) in self.deck.iter() {
            let (rank, suit) = card.split();
            if rank < N_RANKS && self.final_stack[suit as usize] == rank {
                moves.push((Pos::Deck(pos as u8), Pos::Stack(suit)));
            }
            for (id, pile) in self.visible_piles.iter().enumerate() {
                let dst_card = pile.end();
                if dst_card.go_before(card) {
                    moves.push((Pos::Deck(pos as u8), Pos::Pile(id as u8)));
                }
            }
        }

        // move to deck
        for (id, pile) in self.visible_piles.iter().enumerate() {
            let dst_card = pile.end();

            let (rank, suit) = dst_card.split();
            if self.final_stack[suit as usize] == rank && rank < N_RANKS {
                // check if dominances
                let is_domiance = self.stack_dominance(rank, suit);
                if is_domiance {
                    moves.truncate(start_len);
                }
                moves.push((Pos::Pile(id as u8), Pos::Stack(suit)));
                if is_domiance {
                    return;
                }
            }
            for (other_id, other_pile) in self.visible_piles.iter().enumerate() {
                if id != other_id && other_pile.movable_to(pile) {
                    moves.push((Pos::Pile(other_id as u8), Pos::Pile(id as u8)));
                }
            }
            for i in 1..2u8 {
                if rank > 0 && self.final_stack[(suit ^ i ^ 2) as usize] == rank {
                    moves.push((Pos::Stack(suit ^ i ^ 2), Pos::Pile(id as u8)));
                }
            }
        }
    }

    // pub fn gen_moves_(self: &Solitaire, moves: &mut Vec<MoveType>) {
    //     // move to deck
    //     for (id, pile) in self.visible_piles.iter().enumerate() {
    //         let dst_card = pile.end();

    //         let (rank, suit) = dst_card.split();
    //         if self.final_stack[suit as usize] == rank && rank < N_RANKS {
    //             moves.push((Pos::Pile(id as u8), Pos::Stack(suit)));
    //         }
    //     }
    //     for (id, pile) in self.visible_piles.iter().enumerate() {
    //         for (other_id, other_pile) in self.visible_piles.iter().enumerate() {
    //             if id != other_id
    //                 && other_pile.movable_to(pile)
    //                 && other_pile.start_rank() + 1 == pile.end().rank()
    //             {
    //                 moves.push((Pos::Pile(other_id as u8), Pos::Pile(id as u8)));
    //             }
    //         }
    //     }
    //     // src = src.Deck
    //     for (pos, card) in self.deck.iter() {
    //         let (rank, suit) = card.split();
    //         if rank < N_RANKS && self.final_stack[suit as usize] == rank {
    //             moves.push((Pos::Deck(pos as u8), Pos::Stack(suit)));
    //         }
    //         for (id, pile) in self.visible_piles.iter().enumerate() {
    //             let dst_card = pile.end();
    //             if dst_card.go_before(card) {
    //                 moves.push((Pos::Deck(pos as u8), Pos::Pile(id as u8)));
    //             }
    //         }
    //     }

    //     for (id, pile) in self.visible_piles.iter().enumerate() {
    //         let dst_card = pile.end();
    //         let (rank, suit) = dst_card.split();
    //         for i in 1..2u8 {
    //             if rank > 0 && self.final_stack[(suit ^ i ^ 2) as usize] == rank {
    //                 moves.push((Pos::Stack(suit ^ i ^ 2), Pos::Pile(id as u8)));
    //             }
    //         }
    //     }

    //     for (id, pile) in self.visible_piles.iter().enumerate() {
    //         for (other_id, other_pile) in self.visible_piles.iter().enumerate() {
    //             if id != other_id
    //                 && other_pile.movable_to(pile)
    //                 && other_pile.start_rank() + 1 != pile.end().rank()
    //             {
    //                 moves.push((Pos::Pile(other_id as u8), Pos::Pile(id as u8)));
    //             }
    //         }
    //     }
    // }

    pub fn gen_moves(self: &Solitaire) -> Vec<MoveType> {
        let mut moves = Vec::<MoveType>::new();
        self.gen_moves_(&mut moves);
        return moves;
    }

    // this is unsafe gotta check it is valid move before
    pub fn do_move(self: &mut Solitaire, m: &MoveType) -> (i32, UndoInfo) {
        let (src, dst) = m;
        // handling final stack
        if let &Pos::Stack(id) = src {
            debug_assert!(self.final_stack[id as usize] > 0);
            self.final_stack[id as usize] -= 1;
        }
        if let &Pos::Stack(id) = dst {
            debug_assert!(self.final_stack[id as usize] < N_RANKS);
            self.final_stack[id as usize] += 1;
        }
        // handling deck

        let offset = self.deck.get_offset();
        let default_info = UndoInfo {
            hidden: None,
            offset,
        };

        match src {
            &Pos::Deck(id) => {
                let deck_card = self.deck.draw(id);

                // not dealing with redealt yet :)
                match dst {
                    Pos::Deck(_) => unreachable!(),
                    Pos::Stack(_) => (20, default_info),
                    &Pos::Pile(id_pile) => {
                        self.push_pile(id_pile, deck_card);
                        (5, default_info)
                    }
                }
            }
            &Pos::Stack(id) => match dst {
                &Pos::Pile(id_pile) => {
                    let card: Card = Card::new(self.final_stack[id as usize], id);
                    self.push_pile(id_pile, card);
                    (-15, default_info)
                }
                _ => unreachable!(),
            },
            &Pos::Pile(id) => {
                let prev = self.visible_piles[id as usize];
                let reward = match dst {
                    Pos::Stack(_) => {
                        self.pop_pile(id, 1);
                        15
                    }
                    &Pos::Pile(id_pile) => {
                        self.move_pile(id, id_pile);
                        0
                    }
                    Pos::Deck(_) => unreachable!(),
                };

                // unlocking hidden cards
                if self.visible_piles[id as usize].is_empty() {
                    self.visible_piles[id as usize] = Pile::from_card(self.pop_hidden(id));
                    (
                        reward + 5,
                        UndoInfo {
                            hidden: Some(prev),
                            offset,
                        },
                    )
                } else {
                    (reward, default_info)
                }
            }
        }
    }

    pub fn undo_move(self: &mut Solitaire, m: &MoveType, undo_info: &UndoInfo) {
        let (src, dst) = m;
        // handling final stack

        match src {
            &Pos::Deck(_) => {
                // not dealing with redealt yet :)
                let card = match dst {
                    Pos::Deck(_) => unreachable!(),
                    &Pos::Stack(id) => Card::new(self.final_stack[id as usize] - 1, id),
                    &Pos::Pile(id_pile) => {
                        let card = self.visible_piles[id_pile as usize].end();
                        self.pop_pile(id_pile, 1);
                        card
                    }
                };
                self.deck.push(card);
                self.deck.set_offset(undo_info.offset);
            }
            &Pos::Stack(_) => {
                match dst {
                    &Pos::Pile(id_pile) => {
                        self.pop_pile(id_pile, 1);
                    }
                    _ => unreachable!(),
                };
            }
            &Pos::Pile(id) => {
                match undo_info.hidden {
                    Some(p) => {
                        if self.visible_piles[id as usize].end().rank() < N_RANKS {
                            self.n_hidden[id as usize] += 1; //push back hidden
                        }
                        self.visible_piles[id as usize] = p;
                        match dst {
                            &Pos::Pile(id_pile) => {
                                self.pop_pile(id_pile, p.len());
                            }
                            Pos::Stack(_) => {}
                            _ => unreachable!(),
                        }
                    }
                    None => {
                        match dst {
                            &Pos::Stack(id_stack) => {
                                let card =
                                    Card::new(self.final_stack[id_stack as usize] - 1, id_stack);
                                self.push_pile(id, card);
                            }
                            &Pos::Pile(id_pile) => {
                                self.move_pile(id_pile, id);
                            }
                            Pos::Deck(_) => unreachable!(),
                        };
                    }
                }
            }
        }
        if let &Pos::Stack(id) = src {
            debug_assert!(self.final_stack[id as usize] < N_RANKS);
            self.final_stack[id as usize] += 1;
        }
        if let &Pos::Stack(id) = dst {
            debug_assert!(self.final_stack[id as usize] > 0);
            self.final_stack[id as usize] -= 1;
        }
        // handling deck
    }

    fn encode_stack(self: &Solitaire) -> u16 {
        // considering to make it incremental?
        return self
            .final_stack
            .iter()
            .enumerate()
            .map(|x| (*x.1 as u16) << (x.0 * 4))
            .sum();
    }
    fn encode_piles(self: &Solitaire) -> [u16; N_PILES as usize] {
        // a bit slow maybe optimize later :(
        let mut res = self.visible_piles.map(|p| p.encode()); // you can always ignore 0 since it's not a valid state
        let mut i: usize = 0;
        for k in 0..N_PILES as usize {
            if self.n_hidden[k] != 0 {
                res.swap(i, k);
                i += 1;
            }
        }
        res[i..].sort_unstable();
        res
    }

    pub fn encode(self: &Solitaire) -> Encode {
        // we don't need to encode the number of hidden cards since we can infer it from the piles.
        // since the pile + stack will contain all the unlocked cards
        // We also don't need to encode which cards is in the deck since the pile + stack has all the cards that not in the deck

        // considering to make it incremental?
        // maximum 24 (N_FULL_DECK)
        // only need u8, but whatever :<
        let pile_encode = self.encode_piles();
        let stack_encode = self.encode_stack();
        let deck_encode = self.deck.encode_offset() as u16; //a bit wasteful

        return concat_arrays!(pile_encode, [stack_encode], [deck_encode]);
    }
}

impl fmt::Display for Solitaire {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for (pos, card, t) in self.deck.iter_all() {
            let s = format!("{} ", pos);
            let prefix = match t {
                Drawable::None => s.bright_black(),
                Drawable::Current => s.on_blue(),
                Drawable::Next => s.on_bright_blue(),
            };
            write!(f, "{}{} ", prefix, card)?;
        }
        writeln!(f)?;

        write!(f, "\t\t")?;

        for i in 0u8..4u8 {
            let card = self.final_stack[i as usize];
            let card = if card == 0 {
                Card::FAKE
            } else {
                Card::new(card - 1, i)
            };
            write!(f, "{}.{} ", i + 1, card)?;
        }
        writeln!(f)?;

        for i in 0..N_PILES {
            write!(f, "{}\t", i + 5)?;
        }
        writeln!(f)?;

        let mut i = 0; // skip the hidden layer

        loop {
            let mut is_print = false;
            for j in 0..N_PILES {
                let ref cur_pile = self.visible_piles[j as usize];

                let n_hidden = self.n_hidden[j as usize];
                let n_visible = cur_pile.len();
                if n_hidden > i {
                    write!(f, "**\t")?;
                    is_print = true;
                } else if i < n_hidden + n_visible {
                    write!(f, "{}\t", cur_pile.top(i - n_hidden))?;
                    is_print = true;
                } else {
                    write!(f, "  \t")?;
                }
            }
            writeln!(f)?;
            i += 1;
            if !is_print {
                break;
            }
        }
        Ok(())
    }
}

pub struct Solvitaire(Solitaire);
impl Solvitaire {
    pub fn new(deck: &CardDeck, draw_step: u8) -> Solvitaire {
        Solvitaire {
            0: Solitaire::new(deck, draw_step),
        }
    }
}

impl fmt::Display for Solvitaire {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, r#"{{ "tableau piles": ["#)?;

        for i in 0..N_PILES as usize {
            write!(f, "[")?;
            for j in 0..i as usize {
                // hidden cards
                self.0.hidden_piles[i * (i - 1) / 2 + j].print_solvitaire(f)?;
                write!(f, ",")?;
            }
            self.0.visible_piles[i].end().print_solvitaire(f)?;
            if i + 1 < N_PILES as usize {
                writeln!(f, "],")?;
            } else {
                writeln!(f, "]")?;
            }
        }

        write!(f, "],\n\"stock\": [")?;

        let tmp: Vec<(u8, Card)> = self.0.deck.iter_all().map(|x| (x.0, *x.1)).collect();

        for &(idx, c) in tmp.iter().rev() {
            c.print_solvitaire(f)?;
            if idx == 0 {
                write!(f, "]")?;
            } else {
                write!(f, ",")?;
            }
        }
        write!(f, "}}")?;

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    // Note this useful idiom: importing names from outer (for mod tests) scope.
    use super::*;

    fn assert_moves(mut a: Vec<MoveType>, mut b: Vec<MoveType>) {
        a.sort();
        b.sort();

        assert_eq!(a, b);
    }

    #[test]
    fn test_game() {
        let cards = [
            30, 33, 41, 13, 28, 11, 16, 36, 9, 39, 17, 37, 21, 10, 1, 38, 0, 50, 14, 31, 20, 46,
            18, 32, 7, 49, 3, 19, 8, 44, 4, 51, 2, 15, 40, 35, 43, 22, 12, 42, 26, 23, 24, 5, 6,
            48, 27, 45, 47, 29, 34, 25,
        ]
        .map(|i| Card::new(i / N_SUITS, i % N_SUITS));
        let mut game = Solitaire::new(&cards, 3);
        assert_moves(
            game.gen_moves(),
            vec![
                (Pos::Deck(20), Pos::Pile(4)),
                (Pos::Pile(0), Pos::Pile(4)),
                (Pos::Pile(5), Pos::Stack(3)),
            ],
        );

        assert_eq!(game.do_move(&(Pos::Pile(0), Pos::Pile(4))).0, 5);

        assert_moves(
            game.gen_moves(),
            vec![
                (Pos::Deck(17), Pos::Pile(0)),
                (Pos::Pile(4), Pos::Pile(0)),
                (Pos::Pile(5), Pos::Stack(3)),
            ],
        );

        assert_eq!(game.do_move(&(Pos::Pile(4), Pos::Pile(0))).0, 5);
        assert_moves(
            game.gen_moves(),
            vec![(Pos::Pile(2), Pos::Pile(4)), (Pos::Pile(5), Pos::Stack(3))],
        );

        assert_eq!(game.do_move(&(Pos::Pile(2), Pos::Pile(4))).0, 5);

        assert_moves(
            game.gen_moves(),
            vec![
                (Pos::Pile(2), Pos::Pile(0)),
                (Pos::Pile(4), Pos::Pile(2)),
                (Pos::Pile(5), Pos::Stack(3)),
            ],
        );

        assert_eq!(game.do_move(&(Pos::Pile(2), Pos::Pile(0))).0, 5);

        assert_moves(
            game.gen_moves(),
            vec![(Pos::Pile(4), Pos::Pile(0)), (Pos::Pile(5), Pos::Stack(3))],
        );

        assert_eq!(game.do_move(&(Pos::Pile(4), Pos::Pile(0))).0, 5);

        assert_moves(
            game.gen_moves(),
            vec![(Pos::Pile(3), Pos::Pile(4)), (Pos::Pile(5), Pos::Stack(3))],
        );

        assert_eq!(game.do_move(&(Pos::Pile(3), Pos::Pile(4))).0, 5);

        assert_moves(
            game.gen_moves(),
            vec![(Pos::Deck(2), Pos::Pile(3)), (Pos::Pile(5), Pos::Stack(3))],
        );
    }

    #[test]
    fn test_draw_unrolling() {
        let mut rng = StdRng::seed_from_u64(14);

        let mut moves = Vec::<MoveType>::new();

        for i in 0..100 {
            let mut game = Solitaire::new(&generate_shuffled_deck(12 + i), 3);
            for _ in 0..100 {
                let iter_org = game.deck.iter();
                let check_cur = game
                    .deck
                    .iter_all()
                    .filter(|x| matches!(x.2, Drawable::Current))
                    .map(|x| x.1);
                let check_next = game
                    .deck
                    .iter_all()
                    .filter(|x| matches!(x.2, Drawable::Next))
                    .map(|x| x.1);

                assert!(iter_org.map(|x| x.1).eq(check_cur.chain(check_next)));

                moves.clear();
                game.gen_moves_(&mut moves);
                if moves.len() == 0 {
                    break;
                }
                game.do_move(moves.choose(&mut rng).unwrap());
            }
        }
    }

    #[test]
    fn test_undoing() {
        let mut rng = StdRng::seed_from_u64(14);

        let mut moves = Vec::<MoveType>::new();

        for i in 0..100 {
            let mut game = Solitaire::new(&generate_shuffled_deck(12 + i), 3);
            for _ in 0..100 {
                moves.clear();
                game.gen_moves_(&mut moves);
                if moves.len() == 0 {
                    break;
                }

                let state = game.encode();
                let ids: Vec<(usize, Card)> = game.deck.iter().map(|x| (x.0, *x.1)).collect();

                let m = moves.choose(&mut rng).unwrap();
                let (_, undo) = game.do_move(m);
                let next_state = game.encode();
                // assert_ne!(next_state, state); // could to do unmeaningful moves
                game.undo_move(m, &undo);
                let new_ids: Vec<(usize, Card)> = game.deck.iter().map(|x| (x.0, *x.1)).collect();

                assert_eq!(ids, new_ids);
                let undo_state = game.encode();
                if undo_state != state {
                    assert_eq!(undo_state, state);
                }
                game.do_move(m);
                assert_eq!(game.encode(), next_state);
            }
        }
    }

    #[test]
    fn test_deep_undoing() {
        let mut rng = StdRng::seed_from_u64(14);

        let mut moves = Vec::<MoveType>::new();

        for i in 0..100 {
            let mut game = Solitaire::new(&generate_shuffled_deck(12 + i), 3);
            let mut history = Vec::<(MoveType, UndoInfo)>::new();
            let mut enc = Vec::<Encode>::new();

            for _ in 0..100 {
                moves.clear();
                game.gen_moves_(&mut moves);
                if moves.len() == 0 {
                    break;
                }

                enc.push(game.encode());

                let m = moves.choose(&mut rng).unwrap();
                let (_, undo) = game.do_move(m);
                history.push((*m, undo));
            }

            for _ in 0..history.len() {
                let (m, undo) = history.pop().unwrap();
                game.undo_move(&m, &undo);
                assert_eq!(game.encode(), enc.pop().unwrap());
            }
        }
    }
}
