use core::fmt;

use crate::card::{Card, N_CARDS, N_RANKS, N_SUITS};
use crate::deck::{Deck, Drawable, N_HIDDEN_CARDS, N_PILES};

use colored::Colorize;
use rand::prelude::*;

pub type CardDeck = [Card; N_CARDS as usize];

#[derive(Debug, Clone, Copy)]
pub enum Move {
    DeckStack(Card),
    PileStack(Card),
    DeckPile(Card),
    StackPile(Card),
    Reveal(Card),
}

impl fmt::Display for Move {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Move::DeckStack(c) => write!(f, "DS {}", c),
            Move::PileStack(c) => write!(f, "PS {}", c),
            Move::DeckPile(c) => write!(f, "DP {}", c),
            Move::StackPile(c) => write!(f, "SP {}", c),
            Move::Reveal(c) => write!(f, "R {}", c),
        }
    }
}

#[derive(Debug)]
pub struct Solitaire {
    hidden_piles: [Card; N_HIDDEN_CARDS as usize],
    n_hidden: [u8; N_PILES as usize],
    hidden: [u8; N_CARDS as usize],

    final_stack: [u8; N_SUITS as usize],
    pub deck: Deck,

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
pub type Encode = u64;

const HALF_MASK: u64 = 0x33333333_3333333;
const ALT_MASK: u64 = 0x55555555_5555555;

const KING_MASK: u64 = 0xF << (4 * 12);

const SUIT_MASK: [u64; 4] = [
    0x41414141_41414141,
    0x82828282_82828282,
    0x14141414_14141414,
    0x28282828_28282828,
];

const fn swap_pair(a: u64) -> u64 {
    let half = (a & HALF_MASK) << 2;
    ((a >> 2) & HALF_MASK) | half
}

const fn card_mask(c: &Card) -> u64 {
    let v = c.value();
    1u64 << (v ^ ((v >> 1) & 2))
}

pub const fn from_mask(v: &u64) -> Card {
    let v = v.trailing_zeros() as u8;
    let v = v ^ ((v >> 1) & 2);
    Card::new(v / N_SUITS, v % N_SUITS)
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

fn iter_mask(mut m: u64, mut func: impl FnMut(&Card) -> ()) {
    while m > 0 {
        let bit = m.wrapping_neg() & m;
        let c = from_mask(&bit);
        func(&c);
        m -= bit;
    }
}

pub fn to_cards(mask: u64) -> Vec<Card> {
    let mut card = Vec::<Card>::new();
    iter_mask(mask, |c| card.push(*c));
    card
}

pub fn print_cards(cards: &Vec<Card>) {
    for c in cards {
        print!("{} ", c);
    }
    print!("\n");
}

type UndoInfo = (Card, u8);

impl Solitaire {
    pub fn new(cards: &CardDeck, draw_step: u8) -> Solitaire {
        let hidden_piles: [Card; N_HIDDEN_CARDS as usize] =
            cards[0..N_HIDDEN_CARDS as usize].try_into().unwrap();

        let mut visible_mask = 0;
        let mut hidden = [0; N_CARDS as usize];

        for i in 0..N_PILES {
            let start = i * (i + 1) / 2;
            let end = (i + 2) * (i + 1) / 2;

            let p = &hidden_piles[start as usize..end as usize];
            for c in p {
                hidden[c.value() as usize] = i;
            }
            visible_mask |= card_mask(p.last().unwrap());
        }

        let n_hidden: [u8; N_PILES as usize] = core::array::from_fn(|i| (i + 1) as u8);

        let deck: Deck = Deck::new(
            cards[(N_HIDDEN_CARDS) as usize..].try_into().unwrap(),
            draw_step,
        );

        let final_stack: [u8; 4] = [0u8; 4];

        return Solitaire {
            hidden_piles,
            n_hidden,
            final_stack,
            deck,
            visible_mask,
            top_mask: visible_mask,
            hidden,
        };
    }

    pub const fn get_visible_mask(self: &Solitaire) -> u64 {
        self.visible_mask
    }

    pub const fn get_top_mask(self: &Solitaire) -> u64 {
        self.top_mask
    }

    // const here
    pub fn get_bottom_mask(self: &Solitaire) -> u64 {
        let vm = self.get_visible_mask();
        let ntm = vm ^ self.get_top_mask();
        let sum_ntm = ntm ^ (ntm >> 1);
        let sum_vm = vm ^ (vm >> 1);
        let or_ntn = ntm | (ntm >> 1);
        let or_vm = vm | (vm >> 1);

        let sm = sum_vm ^ (sum_ntm << 4);
        // print_cards(&to_cards(vm));
        // print_cards(&to_cards(sm & ALT_MASK));

        let bottom_mask = (sm | !(or_ntn << 4)) & or_vm & ALT_MASK; //shared rank
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
        let d = (min(d.0 + 3, d.1 + 2), min(d.0 + 2, d.1 + 3));

        let dd = ((SUIT_MASK[0] | SUIT_MASK[1]) & mask(d.0 * 4))
            | ((SUIT_MASK[2] | SUIT_MASK[3]) & mask(d.1 * 4));

        let ss = ss[0] | ss[1] | ss[2] | ss[3];
        (dd, ss)
    }

    pub fn get_deck_mask<const DOMINANCES: bool>(self: &Solitaire) -> u64 {
        let filter = DOMINANCES
            && self.deck.draw_step() > 1
            && self.deck.peek_last().is_some_and(|&x| {
                let (rank, suit) = x.split();
                self.stackable(rank, suit) && self.stack_dominance(rank, suit)
            });

        let mut mask = 0;
        self.deck.iter_callback(filter, |_, card| -> bool {
            mask |= card_mask(card);
            false
        });
        mask
    }

    pub fn list_moves<const DOMINANCES: bool>(self: &Solitaire, moves: &mut Vec<Move>) {
        let [to_stack, to_pile, reveal, deck] = self.new_gen_moves::<DOMINANCES>();

        iter_mask(to_stack & deck, |c| moves.push(Move::DeckStack(*c)));
        iter_mask(to_stack & !deck, |c| moves.push(Move::PileStack(*c)));
        iter_mask(to_pile & deck, |c| moves.push(Move::DeckPile(*c)));
        iter_mask(to_pile & !deck, |c| moves.push(Move::StackPile(*c)));
        iter_mask(reveal, |c| moves.push(Move::Reveal(*c)));
    }

    pub fn new_gen_moves<const DOMINANCES: bool>(self: &Solitaire) -> [u64; 4] {
        let vm = self.get_visible_mask();
        let tm = self.get_top_mask();
        let bm = self.get_bottom_mask();

        let (dsm, sm) = self.get_stack_mask();
        let dsm = if DOMINANCES { dsm } else { 0 };

        let rm_mask = bm & vm & sm; // remove mask
        let dom_mask = rm_mask & dsm;
        if dom_mask != 0 {
            // dominances
            return [dom_mask.wrapping_neg() & dom_mask, 0, 0, 0];
        }

        let deck_mask = self.get_deck_mask::<DOMINANCES>();

        let ds_mask = deck_mask & sm;

        let free_pile = (((vm ^ tm) & KING_MASK).count_ones() + tm.count_ones()) < N_PILES as u32;
        let king_mask = if free_pile { KING_MASK } else { 0 };

        // println!("Yolo: {} {}", free_pile, dsm);

        // not yet add the king cards :(
        let tmp = (bm >> 4) | king_mask;

        let good_pos = tmp & !dsm;
        let add_mask = swap_pair(sm >> 4) & good_pos;
        let dp_mask = deck_mask & good_pos;
        // deck to stack, deck to pile :)
        let hidden_mask = tm & tmp;

        // print_cards(&to_cards(bm));

        // print_cards(&to_cards(tm));
        // print_cards(&to_cards(tmp));

        return [
            rm_mask | ds_mask,
            add_mask | dp_mask,
            hidden_mask,
            deck_mask,
        ];
    }

    pub fn make_stack<const DECK: bool>(self: &mut Solitaire, mask: &u64) -> UndoInfo {
        let card = from_mask(&mask);
        self.final_stack[card.suit() as usize] += 1;

        if DECK {
            let offset = self.deck.get_offset();
            let pos = self.deck.find_card(card).unwrap();
            self.deck.draw(pos);
            (card, offset)
        } else {
            let hidden = (self.top_mask & mask) != 0;
            self.visible_mask ^= mask;
            if hidden {
                self.make_reveal(mask);
            }
            (card, hidden as u8)
        }
    }

    pub fn unmake_stack<const DECK: bool>(self: &mut Solitaire, mask: &u64, info: &UndoInfo) {
        let card = info.0;
        self.final_stack[card.suit() as usize] -= 1;

        if DECK {
            self.deck.push(card);
            self.deck.set_offset(info.1);
        } else {
            self.visible_mask |= mask;
            if info.1 != 0 {
                self.unmake_reveal(mask, info);
            }
        }
    }

    pub fn make_pile<const DECK: bool>(self: &mut Solitaire, mask: &u64) -> UndoInfo {
        let card = from_mask(&mask);

        self.visible_mask |= mask;

        if DECK {
            let offset = self.deck.get_offset();
            let pos = self.deck.find_card(card).unwrap();
            self.deck.draw(pos);
            (card, offset)
        } else {
            self.final_stack[card.suit() as usize] -= 1;
            (card, 0)
        }
    }

    pub fn unmake_pile<const DECK: bool>(self: &mut Solitaire, mask: &u64, info: &UndoInfo) {
        let card = from_mask(&mask);

        self.visible_mask &= !mask;

        if DECK {
            self.deck.push(card);
            self.deck.set_offset(info.1);
        } else {
            self.final_stack[card.suit() as usize] += 1;
        }
    }

    const fn get_hidden(self: &Solitaire, pos: u8, n_hid: u8) -> Card {
        return self.hidden_piles[(pos * (pos + 1) / 2 + n_hid) as usize];
    }

    pub fn make_reveal(self: &mut Solitaire, m: &u64) -> UndoInfo {
        let card = from_mask(&m);
        let pos = self.hidden[card.value() as usize];
        self.top_mask &= !m;

        self.n_hidden[pos as usize] -= 1;
        if self.n_hidden[pos as usize] > 0 {
            let new_card = self.get_hidden(pos, self.n_hidden[pos as usize] - 1);
            let revealed = card_mask(&new_card);
            self.visible_mask |= revealed;
            self.top_mask |= revealed;
        }

        (Card::FAKE, 0)
    }

    pub fn unmake_reveal(self: &mut Solitaire, m: &u64, _info: &UndoInfo) {
        let card = from_mask(&m);
        let pos = self.hidden[card.value() as usize];
        self.top_mask |= m;

        if self.n_hidden[pos as usize] > 0 {
            let new_card = self.get_hidden(pos, self.n_hidden[pos as usize] - 1);
            let revealed = card_mask(&new_card);
            self.visible_mask ^= revealed;
            self.top_mask ^= revealed;
        }
        self.n_hidden[pos as usize] += 1;
    }

    pub fn do_move(self: &mut Solitaire, m: &Move) -> UndoInfo {
        match m {
            Move::DeckStack(c) => self.make_stack::<true>(&card_mask(c)),
            Move::PileStack(c) => self.make_stack::<false>(&card_mask(c)),
            Move::DeckPile(c) => self.make_pile::<true>(&card_mask(c)),
            Move::StackPile(c) => self.make_pile::<false>(&card_mask(c)),
            Move::Reveal(c) => self.make_reveal(&card_mask(c)),
        }
    }

    pub fn undo_move(self: &mut Solitaire, m: &Move, undo: &UndoInfo) {
        match m {
            Move::DeckStack(c) => self.unmake_stack::<true>(&card_mask(c), undo),
            Move::PileStack(c) => self.unmake_stack::<false>(&card_mask(c), undo),
            Move::DeckPile(c) => self.unmake_pile::<true>(&card_mask(c), undo),
            Move::StackPile(c) => self.unmake_pile::<false>(&card_mask(c), undo),
            Move::Reveal(c) => self.unmake_reveal(&card_mask(c), undo),
        }
    }

    pub fn is_win(self: &Solitaire) -> bool {
        // What a shame this is not a const function :(
        return self.final_stack == [N_RANKS; N_SUITS as usize];
    }

    const fn stackable(self: &Solitaire, rank: u8, suit: u8) -> bool {
        self.final_stack[suit as usize] == rank && rank < N_RANKS
    }

    const fn stack_dominance(self: &Solitaire, rank: u8, suit: u8) -> bool {
        let stack = &self.final_stack;
        let suit = suit as usize;
        // allowing worring back :)
        rank <= stack[suit ^ 2] + 1
            && rank <= stack[suit ^ 2 ^ 1] + 1
            && rank <= stack[suit ^ 1] + 2
    }

    fn encode_stack(self: &Solitaire) -> u16 {
        // considering to make it incremental?
        self.final_stack
            .iter()
            .enumerate()
            .map(|x| (*x.1 as u16) << (x.0 * 4))
            .sum()
    }

    fn encode_hidden(self: &Solitaire) -> u32 {
        self.n_hidden
            .iter()
            .rev()
            .enumerate()
            .fold(0u32, |res, cur| res * (cur.0 as u32) + *cur.1 as u32)
    }

    pub fn encode(self: &Solitaire) -> Encode {
        let deck_encode = self.deck.encode(); // 24 bits (can be reduced to 20)
        let stack_encode = self.encode_stack(); // 16 bits (can be reduce to 15)
        let hidden_encode = self.encode_hidden(); // 19 bits
        let offset_encode = self.deck.encode_offset(); // 5 bits

        return (deck_encode as u64)
            | (stack_encode as u64) << 24
            | (hidden_encode as u64) << (24 + 16)
            | (offset_encode as u64) << (24 + 16 + 19);
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

        let mut piles: [Vec<Card>; N_PILES as usize] = Default::default();

        let mut king_suit = 0;

        for i in 0..N_PILES {
            let mut cards = Vec::<Card>::new();
            let n_hid = self.n_hidden[i as usize];
            let mut start_card = if n_hid == 0 {
                while king_suit < 4
                    && (self.visible_mask ^ self.top_mask) & card_mask(&Card::new(12, king_suit))
                        == 0
                {
                    king_suit += 1;
                }
                if king_suit < 4 {
                    Card::new(12, king_suit)
                } else {
                    continue;
                }
            } else {
                self.get_hidden(i, n_hid - 1)
            };

            loop {
                // push start card
                cards.push(start_card);

                if start_card.rank() == 0 {
                    break;
                }
                let has_both = card_mask(&Card::new(start_card.rank(), start_card.suit() ^ 1))
                    & self.visible_mask
                    != 0;

                start_card = Card::new(start_card.rank() - 1, start_card.suit() ^ 2);
                let mask = card_mask(&start_card);
                if !has_both && (self.visible_mask & mask == 0 || self.top_mask & mask != 0) {
                    start_card = Card::new(start_card.rank(), start_card.suit() ^ 1);
                }
                let mask = card_mask(&start_card);

                if self.visible_mask & mask == 0 || self.top_mask & mask != 0 {
                    break;
                }
            }
            piles[i as usize] = cards;
        }

        // printing
        let mut i = 1; // skip the hidden layer

        loop {
            let mut is_print = false;
            for j in 0..N_PILES {
                let ref cur_pile = piles[j as usize];

                let n_hidden = self.n_hidden[j as usize];
                let n_visible = cur_pile.len() as u8;
                if n_hidden > i {
                    write!(f, "**\t")?;
                    is_print = true;
                } else if i < n_hidden + n_visible {
                    write!(f, "{}\t", cur_pile[(i - n_hidden) as usize])?;
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
                self.0
                    .get_hidden(i as u8, j as u8)
                    .print_solvitaire::<true>(f)?;
                write!(f, ",")?;
            }
            self.0
                .get_hidden(i as u8, i as u8)
                .print_solvitaire::<false>(f)?;
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

    // fn assert_moves(mut a: Vec<MoveType>, mut b: Vec<MoveType>) {
    //     a.sort();
    //     b.sort();

    //     assert_eq!(a, b);
    // }

    // #[test]
    // fn test_game() {
    //     let cards = [
    //         30, 33, 41, 13, 28, 11, 16, 36, 9, 39, 17, 37, 21, 10, 1, 38, 0, 50, 14, 31, 20, 46,
    //         18, 32, 7, 49, 3, 19, 8, 44, 4, 51, 2, 15, 40, 35, 43, 22, 12, 42, 26, 23, 24, 5, 6,
    //         48, 27, 45, 47, 29, 34, 25,
    //     ]
    //     .map(|i| Card::new(i / N_SUITS, i % N_SUITS));
    //     let mut game = Solitaire::new(&cards, 3);
    //     assert_moves(
    //         game.gen_moves::<false>(),
    //         vec![
    //             (Pos::Deck(20), Pos::Pile(4)),
    //             (Pos::Pile(0), Pos::Pile(4)),
    //             (Pos::Pile(5), Pos::Stack(3)),
    //         ],
    //     );

    //     assert_moves(
    //         game.gen_moves::<true>(),
    //         vec![(Pos::Pile(5), Pos::Stack(3))],
    //     );

    //     game.do_move(&(Pos::Pile(0), Pos::Pile(4)));

    //     assert_moves(
    //         game.gen_moves::<false>(),
    //         vec![
    //             (Pos::Deck(17), Pos::Pile(0)),
    //             (Pos::Pile(4), Pos::Pile(0)),
    //             (Pos::Pile(5), Pos::Stack(3)),
    //         ],
    //     );

    //     assert_moves(
    //         game.gen_moves::<true>(),
    //         vec![(Pos::Pile(5), Pos::Stack(3))],
    //     );

    //     game.do_move(&(Pos::Pile(4), Pos::Pile(0)));
    //     assert_moves(
    //         game.gen_moves::<false>(),
    //         vec![(Pos::Pile(2), Pos::Pile(4)), (Pos::Pile(5), Pos::Stack(3))],
    //     );

    //     assert_moves(
    //         game.gen_moves::<true>(),
    //         vec![(Pos::Pile(5), Pos::Stack(3))],
    //     );

    //     game.do_move(&(Pos::Pile(2), Pos::Pile(4)));

    //     assert_moves(
    //         game.gen_moves::<false>(),
    //         vec![
    //             (Pos::Pile(2), Pos::Pile(0)),
    //             (Pos::Pile(4), Pos::Pile(2)),
    //             (Pos::Pile(5), Pos::Stack(3)),
    //         ],
    //     );

    //     assert_moves(
    //         game.gen_moves::<true>(),
    //         vec![(Pos::Pile(5), Pos::Stack(3))],
    //     );

    //     game.do_move(&(Pos::Pile(2), Pos::Pile(0)));

    //     assert_moves(
    //         game.gen_moves::<false>(),
    //         vec![(Pos::Pile(4), Pos::Pile(0)), (Pos::Pile(5), Pos::Stack(3))],
    //     );

    //     assert_moves(
    //         game.gen_moves::<true>(),
    //         vec![(Pos::Pile(5), Pos::Stack(3))],
    //     );

    //     game.do_move(&(Pos::Pile(4), Pos::Pile(0)));

    //     assert_moves(
    //         game.gen_moves::<false>(),
    //         vec![(Pos::Pile(3), Pos::Pile(4)), (Pos::Pile(5), Pos::Stack(3))],
    //     );

    //     assert_moves(
    //         game.gen_moves::<true>(),
    //         vec![(Pos::Pile(5), Pos::Stack(3))],
    //     );

    //     game.do_move(&(Pos::Pile(3), Pos::Pile(4)));

    //     assert_moves(
    //         game.gen_moves::<false>(),
    //         vec![(Pos::Deck(2), Pos::Pile(3)), (Pos::Pile(5), Pos::Stack(3))],
    //     );

    //     assert_moves(
    //         game.gen_moves::<true>(),
    //         vec![(Pos::Pile(5), Pos::Stack(3))],
    //     );
    // }

    #[test]
    fn test_draw_unrolling() {
        let mut rng = StdRng::seed_from_u64(14);

        let mut moves = Vec::<Move>::new();

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
                game.list_moves::<false>(&mut moves);
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

        let mut moves = Vec::<Move>::new();

        for i in 0..100 {
            let mut game = Solitaire::new(&generate_shuffled_deck(12 + i), 3);
            for _ in 0..100 {
                moves.clear();
                game.list_moves::<false>(&mut moves);
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

        let mut moves = Vec::<Move>::new();

        for i in 0..100 {
            let mut game = Solitaire::new(&generate_shuffled_deck(12 + i), 3);
            let mut history = Vec::<(Move, UndoInfo)>::new();
            let mut enc = Vec::<Encode>::new();

            for _ in 0..100 {
                moves.clear();
                game.list_moves::<false>(&mut moves);
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
