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

pub enum Move {
    AddCard(Card),
    ToStack(Card),
    Reveal(u8),
}

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

    visible_mask: u64,
    top_mask: u64,
}

pub fn generate_shuffled_deck(seed: u64) -> CardDeck {
    let mut rng = StdRng::seed_from_u64(seed);
    let mut cards: [Card; N_CARDS as usize] =
        core::array::from_fn(|i| Card::new(i as u8 / N_SUITS, i as u8 % N_SUITS));
    cards.shuffle(&mut rng);
    return cards;
}
pub type Encode = [u16; N_PILES as usize + 2];

const HALF_MASK: u64 = 0x33333333_3333333;
const ALT_MASK: u64 = 0x55555555_5555555;

const SUIT_MASK: [u64; 4] = [
    0x41414141_41414141,
    0x82828282_82828282,
    0x14141414_14141414,
    0x28282828_28282828,
];

const fn swap_pair(a: u64) -> u64 {
    let half = (a & HALF_MASK) << 2;
    (a >> 2) ^ half ^ (half << 4)
}

const fn card_mask(c: &Card) -> u64 {
    let v = c.value();
    1u64 << (v ^ ((v >> 1) & 2))
}

const fn min(a: u8, b: u8) -> u8 {
    if a < b {
        a
    } else {
        b
    }
}

const fn mask(i: u8) -> u64 {
    (1 << i) - 1
}

impl Solitaire {
    pub fn new(cards: &CardDeck, draw_step: u8) -> Solitaire {
        let hidden_piles: [Card; N_HIDDEN_CARDS as usize] =
            cards[0..N_HIDDEN_CARDS as usize].try_into().unwrap();
        let n_hidden: [u8; N_PILES as usize] = core::array::from_fn(|i| i as u8);

        let visible_cards: &[Card; N_PILES as usize] = cards
            [N_HIDDEN_CARDS as usize..(N_HIDDEN_CARDS + N_PILES) as usize]
            .try_into()
            .unwrap();

        let visible_mask = visible_cards
            .map(|c| card_mask(&c))
            .iter()
            .fold(0u64, |a, b| a | *b);

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
            visible_mask,
            top_mask: visible_mask,
        };
    }

    pub const fn get_visible_mask(self: &Solitaire) -> u64 {
        self.visible_mask
    }

    pub const fn get_top_mask(self: &Solitaire) -> u64 {
        self.top_mask
    }

    pub const fn get_bottom_mask(self: &Solitaire) -> u64 {
        let vm = self.get_visible_mask();
        let tm = self.get_top_mask();
        let tm = tm | (tm >> 1);
        let sum_mask = vm ^ (vm >> 1);
        let or_mask = vm | (vm >> 1);
        let bottom_mask = ((sum_mask ^ (sum_mask << 4)) | !(or_mask << 4) | (tm << 4)) & ALT_MASK; //shared rank
        bottom_mask | (bottom_mask << 1) // & vm
    }
    pub const fn get_stack_mask(self: &Solitaire) -> (u64, u64) {
        let s = self.final_stack;
        let ss = [
            card_mask(&Card::new(s[0], 0)),
            card_mask(&Card::new(s[1], 1)),
            card_mask(&Card::new(s[2], 2)),
            card_mask(&Card::new(s[3], 3)),
        ];
        let d = (min(s[0], s[1]), min(s[2], s[3]));
        let d = (min(d.0 + 2, d.1 + 1), min(d.0 + 1, d.1 + 2));
        let dd = ((SUIT_MASK[0] | SUIT_MASK[1]) & mask(d.0))
            | ((SUIT_MASK[2] | SUIT_MASK[3]) & mask(d.1));

        let ss = ss[0] | ss[1] | ss[2] | ss[3];
        (dd, ss)
    }

    pub fn get_deck_mask(self: &Solitaire, filter: bool) -> u64 {
        let mut mask = 0;
        self.deck.iter_callback(filter, |pos, card| -> bool {
            mask |= card_mask(card);
            false
        });
        mask
    }

    pub fn new_gen_moves(self: &Solitaire) -> [u64; 3] {
        let vm = self.get_visible_mask();
        let tm = self.get_top_mask();
        let bm = self.get_bottom_mask();

        let (dsm, sm) = self.get_stack_mask();

        let filter = self.deck.draw_step() > 1
            && self.deck.peek_last().is_some_and(|&x| {
                let (rank, suit) = x.split();
                self.stackable(rank, suit) && self.stack_dominance(rank, suit)
            });

        let deck_mask = self.get_deck_mask(filter);

        let rm_mask = bm & vm & sm; // remove mask
        let dom_mask = rm_mask & dsm;
        if dom_mask != 0 {
            // dominances
            return [dom_mask.wrapping_neg() & dom_mask, 0, 0];
        }

        let add_mask = (bm >> 4) & swap_pair(sm >> 4) & !dsm;
        let hidden_mask = tm & (bm >> 4);
        // deck to stack, deck to pile :)
        let ds_mask = deck_mask & sm;
        let dp_mask = deck_mask & (bm >> 4) & !dsm;
        return [rm_mask | ds_mask, add_mask | dp_mask, hidden_mask];
    }

    pub fn make_stack(self: &Solitaire) {
        
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

    const fn stackable(self: &Solitaire, rank: u8, suit: u8) -> bool {
        self.final_stack[suit as usize] == rank && rank < N_RANKS
    }

    // minimal number of move left to win (can't use sum :()
    pub fn min_move(self: &Solitaire) -> u8 {
        N_CARDS - self.final_stack.iter().sum::<u8>()
    }

    const fn stack_dominance(self: &Solitaire, rank: u8, suit: u8) -> bool {
        let stack = &self.final_stack;
        let suit = suit as usize;
        // allowing worring back :)
        rank <= stack[suit ^ 2] + 1
            && rank <= stack[suit ^ 2 ^ 1] + 1
            && rank <= stack[suit ^ 1] + 2
    }

    pub fn gen_pile_stack<const DOMINANCES: bool>(
        self: &Solitaire,
        moves: &mut Vec<MoveType>,
    ) -> bool {
        // move to deck
        for (id, pile) in self.visible_piles.iter().enumerate() {
            let dst_card = pile.end();

            let (rank, suit) = dst_card.split();
            if self.stackable(rank, suit) {
                // check if dominances
                moves.push((Pos::Pile(id as u8), Pos::Stack(suit)));

                if DOMINANCES && self.stack_dominance(rank, suit) {
                    return true;
                }
            }
        }
        false
    }

    pub fn gen_deck_stack<const DOMINANCES: bool>(
        self: &Solitaire,
        moves: &mut Vec<MoveType>,
        filter: bool,
    ) -> bool {
        if self.deck.draw_step() == 1 {
            self.deck.iter_callback(false, |pos, card| -> bool {
                let (rank, suit) = card.split();
                if self.stackable(rank, suit) {
                    moves.push((Pos::Deck(pos as u8), Pos::Stack(suit)));
                    if DOMINANCES && self.stack_dominance(rank, suit) {
                        return true;
                    }
                }
                false
            })
        } else {
            self.deck.iter_callback(filter, |pos, card| -> bool {
                let (rank, suit) = card.split();
                if self.stackable(rank, suit) {
                    moves.push((Pos::Deck(pos), Pos::Stack(suit)));
                }
                false
            })
        }
    }

    pub fn gen_deck_pile<const DOMINANCES: bool>(
        self: &Solitaire,
        moves: &mut Vec<MoveType>,
        filter: bool,
    ) -> bool {
        self.deck.iter_callback(filter, |pos, card| -> bool {
            for (id, pile) in self.visible_piles.iter().enumerate() {
                let dst_card = pile.end();
                if dst_card.go_before(card) {
                    moves.push((Pos::Deck(pos as u8), Pos::Pile(id as u8)));
                }
            }
            false
        });
        false
    }

    pub fn gen_stack_pile<const DOMINANCES: bool>(
        self: &Solitaire,
        moves: &mut Vec<MoveType>,
    ) -> bool {
        for (id, pile) in self.visible_piles.iter().enumerate() {
            let dst_card = pile.end();

            let (rank, suit) = dst_card.split();

            for i in 2..4u8 {
                let s = suit ^ i;
                if rank > 0
                    && self.final_stack[s as usize] == rank
                    && !(DOMINANCES && self.stack_dominance(rank - 1, s))
                {
                    moves.push((Pos::Stack(s), Pos::Pile(id as u8)));
                }
            }
        }
        false
    }

    pub fn gen_pile_pile<const DOMINANCES: bool>(
        self: &Solitaire,
        moves: &mut Vec<MoveType>,
    ) -> bool {
        for (id, pile) in self.visible_piles.iter().enumerate().skip(1) {
            for (other_id, other_pile) in self.visible_piles.iter().enumerate().take(id) {
                let (a, b, a_id, b_id) = if other_pile.movable_to(pile) {
                    (other_pile, pile, other_id, id)
                } else if pile.movable_to(other_pile) {
                    (pile, other_pile, id, other_id)
                } else {
                    continue;
                };

                let n_moved = a.n_move(b);
                if DOMINANCES && n_moved != a.len() {
                    //partial move only made when it's possible to move the card to the stack
                    //this also stop you from moving from one empty pile to another pile
                    let (rank, suit) = a.bottom(n_moved).split();
                    if !self.stackable(rank, suit) {
                        continue;
                    }
                }

                moves.push((Pos::Pile(a_id as u8), Pos::Pile(b_id as u8)));
            }
        }
        false
    }

    pub fn gen_moves_<const DOMINANCES: bool>(self: &Solitaire, moves: &mut Vec<MoveType>) {
        let start_len = moves.len();
        let filter = DOMINANCES
            && self.deck.draw_step() > 1
            && self.deck.peek_last().is_some_and(|&x| {
                let (rank, suit) = x.split();
                self.stackable(rank, suit) && self.stack_dominance(rank, suit)
            });

        let found_dominance = false
            || self.gen_deck_stack::<DOMINANCES>(moves, filter)
            || self.gen_deck_pile::<DOMINANCES>(moves, filter)
            || self.gen_pile_stack::<DOMINANCES>(moves)
            || self.gen_pile_pile::<DOMINANCES>(moves)
            || self.gen_stack_pile::<DOMINANCES>(moves);
        if found_dominance {
            let m = moves.pop().unwrap();
            moves.truncate(start_len);
            moves.push(m);
        }
    }

    pub fn gen_moves<const DOMINANCES: bool>(self: &Solitaire) -> Vec<MoveType> {
        let mut moves = Vec::<MoveType>::new();
        self.gen_moves_::<DOMINANCES>(&mut moves);
        return moves;
    }

    // this is unsafe gotta check it is valid move before
    pub fn do_move(self: &mut Solitaire, m: &MoveType) -> UndoInfo {
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
                    Pos::Stack(_) => default_info,
                    &Pos::Pile(id_pile) => {
                        self.push_pile(id_pile, deck_card);
                        default_info
                    }
                }
            }
            &Pos::Stack(id) => match dst {
                &Pos::Pile(id_pile) => {
                    let card: Card = Card::new(self.final_stack[id as usize], id);
                    self.push_pile(id_pile, card);
                    default_info
                }
                _ => unreachable!(),
            },
            &Pos::Pile(id) => {
                let prev = self.visible_piles[id as usize];
                match dst {
                    Pos::Stack(_) => {
                        self.pop_pile(id, 1);
                    }
                    &Pos::Pile(id_pile) => {
                        self.move_pile(id, id_pile);
                    }
                    Pos::Deck(_) => unreachable!(),
                };

                // unlocking hidden cards
                if self.visible_piles[id as usize].is_empty() {
                    self.visible_piles[id as usize] = Pile::from_card(self.pop_hidden(id));
                    UndoInfo {
                        hidden: Some(prev),
                        offset,
                    }
                } else {
                    default_info
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
            if self.n_hidden[k] == 0 {
                res.swap(i, k);
                i += 1;
            }
        }
        res[..i].sort_unstable();
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
        writeln!(f, r#"{{"tableau piles": ["#)?;

        for i in 0..N_PILES as usize {
            write!(f, "[")?;
            for j in 0..i as usize {
                // hidden cards
                self.0.hidden_piles[i * (i - 1) / 2 + j].print_solvitaire::<true>(f)?;
                write!(f, ",")?;
            }
            self.0.visible_piles[i].end().print_solvitaire::<false>(f)?;
            if i + 1 < N_PILES as usize {
                writeln!(f, "],")?;
            } else {
                writeln!(f, "]")?;
            }
        }

        write!(f, "],\"stock\": [")?;

        let tmp: Vec<(u8, Card)> = self.0.deck.iter_all().map(|x| (x.0, *x.1)).collect();

        for &(idx, c) in tmp.iter().rev() {
            c.print_solvitaire::<false>(f)?;
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
            game.gen_moves::<false>(),
            vec![
                (Pos::Deck(20), Pos::Pile(4)),
                (Pos::Pile(0), Pos::Pile(4)),
                (Pos::Pile(5), Pos::Stack(3)),
            ],
        );

        assert_moves(
            game.gen_moves::<true>(),
            vec![(Pos::Pile(5), Pos::Stack(3))],
        );

        game.do_move(&(Pos::Pile(0), Pos::Pile(4)));

        assert_moves(
            game.gen_moves::<false>(),
            vec![
                (Pos::Deck(17), Pos::Pile(0)),
                (Pos::Pile(4), Pos::Pile(0)),
                (Pos::Pile(5), Pos::Stack(3)),
            ],
        );

        assert_moves(
            game.gen_moves::<true>(),
            vec![(Pos::Pile(5), Pos::Stack(3))],
        );

        game.do_move(&(Pos::Pile(4), Pos::Pile(0)));
        assert_moves(
            game.gen_moves::<false>(),
            vec![(Pos::Pile(2), Pos::Pile(4)), (Pos::Pile(5), Pos::Stack(3))],
        );

        assert_moves(
            game.gen_moves::<true>(),
            vec![(Pos::Pile(5), Pos::Stack(3))],
        );

        game.do_move(&(Pos::Pile(2), Pos::Pile(4)));

        assert_moves(
            game.gen_moves::<false>(),
            vec![
                (Pos::Pile(2), Pos::Pile(0)),
                (Pos::Pile(4), Pos::Pile(2)),
                (Pos::Pile(5), Pos::Stack(3)),
            ],
        );

        assert_moves(
            game.gen_moves::<true>(),
            vec![(Pos::Pile(5), Pos::Stack(3))],
        );

        game.do_move(&(Pos::Pile(2), Pos::Pile(0)));

        assert_moves(
            game.gen_moves::<false>(),
            vec![(Pos::Pile(4), Pos::Pile(0)), (Pos::Pile(5), Pos::Stack(3))],
        );

        assert_moves(
            game.gen_moves::<true>(),
            vec![(Pos::Pile(5), Pos::Stack(3))],
        );

        game.do_move(&(Pos::Pile(4), Pos::Pile(0)));

        assert_moves(
            game.gen_moves::<false>(),
            vec![(Pos::Pile(3), Pos::Pile(4)), (Pos::Pile(5), Pos::Stack(3))],
        );

        assert_moves(
            game.gen_moves::<true>(),
            vec![(Pos::Pile(5), Pos::Stack(3))],
        );

        game.do_move(&(Pos::Pile(3), Pos::Pile(4)));

        assert_moves(
            game.gen_moves::<false>(),
            vec![(Pos::Deck(2), Pos::Pile(3)), (Pos::Pile(5), Pos::Stack(3))],
        );

        assert_moves(
            game.gen_moves::<true>(),
            vec![(Pos::Pile(5), Pos::Stack(3))],
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

                assert!(game.deck.peek_last() == game.deck.iter_all().last().map(|x| x.1));

                moves.clear();
                game.gen_moves_::<true>(&mut moves);
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
                game.gen_moves_::<true>(&mut moves);
                if moves.len() == 0 {
                    break;
                }

                let state = game.encode();
                let ids: Vec<(usize, Card)> = game.deck.iter().map(|x| (x.0, *x.1)).collect();

                let m = moves.choose(&mut rng).unwrap();
                let undo = game.do_move(m);
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
                game.gen_moves_::<true>(&mut moves);
                if moves.len() == 0 {
                    break;
                }

                enc.push(game.encode());

                let m = moves.choose(&mut rng).unwrap();
                let undo = game.do_move(m);
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
