use core::fmt;

use crate::card::{Card, KING_RANK, N_CARDS, N_RANKS, N_SUITS};
use crate::deck::{Deck, Drawable, N_HIDDEN_CARDS, N_PILES};
use crate::shuffler::CardDeck;

use colored::Colorize;

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
    deck: Deck,

    visible_mask: u64,
    top_mask: u64,

    sp_mask: u8,
    last_sp: Option<Card>,
}

pub type Encode = u64;

const HALF_MASK: u64 = 0x33333333_3333333;
const ALT_MASK: u64 = 0x55555555_5555555;

const KING_MASK: u64 = 0xF << (N_SUITS * KING_RANK);

const SUIT_MASK: [u64; N_SUITS as usize] = [
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

const fn full_mask(i: u8) -> u64 {
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

pub fn print_cards(mask: u64) {
    iter_mask(mask, |c| print!("{} ", c));
    print!("\n");
}

pub type UndoInfo = (u16, Option<Card>);

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

        let deck: Deck = Deck::new(
            cards[(N_HIDDEN_CARDS) as usize..].try_into().unwrap(),
            draw_step,
        );

        return Solitaire {
            hidden_piles,
            n_hidden: core::array::from_fn(|i| (i + 1) as u8),
            final_stack: [0u8; 4],
            deck,
            visible_mask,
            top_mask: visible_mask,
            hidden,
            sp_mask: 0,
            last_sp: None,
        };
    }

    pub const fn get_visible_mask(self: &Solitaire) -> u64 {
        self.visible_mask
    }

    pub const fn get_top_mask(self: &Solitaire) -> u64 {
        self.top_mask
    }

    pub const fn get_bottom_mask(self: &Solitaire) -> u64 {
        let vis = self.get_visible_mask();
        let non_top = vis ^ self.get_top_mask();
        let xor_non_top = non_top ^ (non_top >> 1);
        let xor_vis = vis ^ (vis >> 1);
        let or_non_top = non_top | (non_top >> 1);
        let or_vis = vis | (vis >> 1);

        let xor_all = xor_vis ^ (xor_non_top << 4);

        let bottom_mask = (xor_all | !(or_non_top << 4)) & or_vis & ALT_MASK;

        //shared rank
        bottom_mask | (bottom_mask << 1)
    }
    pub const fn get_stack_mask(self: &Solitaire) -> u64 {
        let s = self.final_stack;
        card_mask(&Card::new(s[0], 0))
            | card_mask(&Card::new(s[1], 1))
            | card_mask(&Card::new(s[2], 2))
            | card_mask(&Card::new(s[3], 3))
    }

    pub const fn get_stack_dominances_mask(self: &Solitaire) -> u64 {
        let s = self.final_stack;
        let d = (min(s[0], s[1]), min(s[2], s[3]));
        let d = (min(d.0 + 1, d.1) + 2, min(d.0, d.1 + 1) + 2);

        ((SUIT_MASK[0] | SUIT_MASK[1]) & full_mask(d.0 * 4))
            | ((SUIT_MASK[2] | SUIT_MASK[3]) & full_mask(d.1 * 4))
    }

    pub fn get_deck_mask<const DOMINANCES: bool>(self: &Solitaire) -> (u64, bool) {
        let filter = DOMINANCES
            && self.deck.peek_last().is_some_and(|&x| {
                let (rank, suit) = x.split();
                self.stackable(rank, suit) && self.stack_dominance(rank, suit)
            });

        if filter && self.deck.is_pure() {
            return (card_mask(self.deck.peek_last().unwrap()), true);
        }

        let mut mask = 0;
        self.deck.iter_callback(filter, |_, card| -> bool {
            mask |= card_mask(card);
            false
        });

        // TODO: dominances for draw_step == 1
        (mask, false)
    }

    pub fn list_moves<const DOMINANCES: bool>(self: &Solitaire, moves: &mut Vec<Move>) {
        let [to_stack, to_pile, reveal, deck] = self.gen_moves::<DOMINANCES>();

        iter_mask(to_stack & deck, |c| moves.push(Move::DeckStack(*c)));
        iter_mask(to_stack & !deck, |c| moves.push(Move::PileStack(*c)));
        iter_mask(reveal, |c| moves.push(Move::Reveal(*c)));
        iter_mask(to_pile & deck, |c| moves.push(Move::DeckPile(*c)));
        iter_mask(to_pile & !deck, |c| moves.push(Move::StackPile(*c)));
    }

    pub fn gen_moves<const DOMINANCES: bool>(self: &Solitaire) -> [u64; 4] {
        let vis = self.get_visible_mask();
        let top = self.get_top_mask();
        let bm = self.get_bottom_mask();

        let sm = self.get_stack_mask();
        let dsm = if DOMINANCES {
            self.get_stack_dominances_mask()
        } else {
            0
        };

        let (super_mask, super_mask2, super_mask3) = if let Some(c) = self.last_sp {
            let mo = card_mask(&c);
            let m = (mo | (mo >> 1)) & ALT_MASK;
            let m = m | (m << 1);
            (m >> 4, 0, (m ^ mo))
        } else {
            (full_mask(N_CARDS), full_mask(N_CARDS), full_mask(N_CARDS))
        };

        // let (super_mask, super_mask2) = (full_mask(N_CARDS), full_mask(N_CARDS));

        let pile_stack = bm & vis & sm & super_mask3; // remove mask
        let pile_stack_dom = pile_stack & dsm;
        if pile_stack_dom != 0 {
            // dominances
            return [pile_stack_dom.wrapping_neg() & pile_stack_dom, 0, 0, 0];
        }

        let (deck_mask, dom) = self.get_deck_mask::<DOMINANCES>();
        // no dominances for draw_step = 1 yet
        if dom {
            // not very useful as dominance
            return [deck_mask, 0, 0, deck_mask];
        }

        let deck_stack = deck_mask & sm;

        let free_pile = ((vis & KING_MASK) | top).count_ones() < N_PILES as u32;
        let king_mask = if free_pile { KING_MASK } else { 0 };

        let free_slot = (bm >> 4) | king_mask;

        let stack_pile = swap_pair(sm >> 4) & free_slot & !dsm;

        let stack_pile_1 = if self.sp_mask & 3 != 0 {
            stack_pile & SUIT_MASK[((self.sp_mask & 3) - 1) as usize]
        } else {
            stack_pile & (SUIT_MASK[0] | SUIT_MASK[1])
        };

        let stack_pile_2 = if self.sp_mask & (3 * 4) != 0 {
            stack_pile & SUIT_MASK[1 + ((self.sp_mask / 4) & 3) as usize]
        } else {
            stack_pile & (SUIT_MASK[2] | SUIT_MASK[3])
        };

        let stack_pile = stack_pile_1 | stack_pile_2;

        let deck_pile = deck_mask & free_slot & !(dsm & sm);
        // deck to stack, deck to pile :)
        let reveal = top & free_slot;

        // if DOMINANCES {
        //     /*
        //     Case 1:
        //     9x 9_
        //     __
        //     8y 8z _ _
        //     _ _ 7y(*) 7z(*)

        //     ->

        //      __
        //      8 8
        //      7 _ 7
        //      . _ .
        //      */
        //     let and_mask = vis & (vis >> 1);
        //     let non_top = vis ^ top;
        //     let nand_mask = non_top & (non_top >> 1);
        //     let and_mask = and_mask >> 4 & and_mask & swap_pair((and_mask & nand_mask) << 4);
        //     let and_mask = and_mask & ALT_MASK;
        //     // case 1 only now :)
        //     let dom_mask = and_mask | (and_mask << 1);
        //     let reveal_dom = reveal & dom_mask;
        //     if reveal_dom != 0 {
        //         return [0, 0, reveal_dom.wrapping_neg() & reveal_dom, 0];
        //     }
        // }

        return [
            pile_stack | (deck_stack & super_mask2),
            stack_pile | (deck_pile & super_mask),
            reveal & super_mask,
            deck_mask,
        ];
    }

    pub fn make_stack<const DECK: bool>(self: &mut Solitaire, mask: &u64) -> UndoInfo {
        let card = from_mask(&mask);
        self.final_stack[card.suit() as usize] += 1;

        let sp_mask = self.sp_mask;
        self.sp_mask = 0; //reset
        let last_sp = self.last_sp;
        self.last_sp = None;

        (
            if DECK {
                let offset = self.deck.get_offset();
                let pos = self.deck.find_card(card).unwrap();
                self.deck.draw(pos);
                offset as u16 | (sp_mask as u16) << 5
            } else {
                let hidden = (self.top_mask & mask) != 0;
                self.visible_mask ^= mask;
                if hidden {
                    self.make_reveal(mask);
                }
                hidden as u16 | (sp_mask as u16) << 5
            },
            last_sp,
        )
    }

    pub fn unmake_stack<const DECK: bool>(self: &mut Solitaire, mask: &u64, info: &UndoInfo) {
        let card = from_mask(&mask);
        self.final_stack[card.suit() as usize] -= 1;
        self.last_sp = info.1;

        let org_info = info;
        let info = &info.0;

        if DECK {
            self.deck.push(card);
            self.deck.set_offset((*info & 31) as u8);
        } else {
            self.visible_mask |= mask;
            if *info & 1 != 0 {
                self.unmake_reveal(mask, org_info);
            }
        }
        self.sp_mask = (*info >> 5) as u8;
    }

    pub fn make_pile<const DECK: bool>(self: &mut Solitaire, mask: &u64) -> UndoInfo {
        let card = from_mask(&mask);

        let last_sp = self.last_sp;

        self.visible_mask |= mask;
        let sp_mask = self.sp_mask;

        (
            if DECK {
                self.last_sp = None;
                self.sp_mask = 0; //reset
                let offset = self.deck.get_offset();
                let pos = self.deck.find_card(card).unwrap();
                self.deck.draw(pos);
                offset as u16 | ((sp_mask as u16) << 5)
            } else {
                self.last_sp = Some(card);
                self.sp_mask |= 1 << card.suit();
                self.final_stack[card.suit() as usize] -= 1;
                (sp_mask as u16) << 5
            },
            last_sp,
        )
    }

    pub fn unmake_pile<const DECK: bool>(self: &mut Solitaire, mask: &u64, info: &UndoInfo) {
        let card = from_mask(&mask);

        self.last_sp = info.1;
        let info = &info.0;

        self.visible_mask &= !mask;
        self.sp_mask = (*info >> 5) as u8;

        if DECK {
            self.deck.push(card);
            self.deck.set_offset((*info & 31) as u8);
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

        let last_sp = self.last_sp;
        self.last_sp = None;

        let sp_mask = self.sp_mask;
        self.sp_mask = 0;

        self.n_hidden[pos as usize] -= 1;
        if self.n_hidden[pos as usize] > 0 {
            let new_card = self.get_hidden(pos, self.n_hidden[pos as usize] - 1);
            let revealed = card_mask(&new_card);
            self.visible_mask |= revealed;
            if new_card.rank() < N_RANKS - 1 || self.n_hidden[pos as usize] != 1 {
                self.top_mask |= revealed;
            }
        }
        ((sp_mask as u16) << 5, last_sp)
    }

    pub fn unmake_reveal(self: &mut Solitaire, m: &u64, info: &UndoInfo) {
        let card = from_mask(&m);
        let pos = self.hidden[card.value() as usize];

        self.last_sp = info.1;
        let info = &info.0;

        self.top_mask |= m;
        self.sp_mask = (*info >> 5) as u8;

        if self.n_hidden[pos as usize] > 0 {
            let new_card = self.get_hidden(pos, self.n_hidden[pos as usize] - 1);
            let unrevealed = !card_mask(&new_card);
            self.visible_mask &= unrevealed;
            self.top_mask &= unrevealed;
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

    fn encode_hidden(self: &Solitaire) -> u16 {
        self.n_hidden
            .iter()
            .enumerate()
            .rev()
            .fold(0u16, |res, cur| res * (cur.0 as u16 + 2) + *cur.1 as u16)
    }

    pub fn encode(self: &Solitaire) -> Encode {
        let stack_encode = self.encode_stack(); // 16 bits (can be reduce to 15)
        let hidden_encode = self.encode_hidden(); // 16 bits
        let deck_encode = self.deck.encode(); // 24 bits (can be reduced to 20)
        let offset_encode = self.deck.normalized_offset(); // 5 bits

        return (stack_encode as u64)
            | (hidden_encode as u64) << (16)
            | (deck_encode as u64) << (16 + 16)
            | (offset_encode as u64) << (24 + 16 + 16);
    }
}

impl fmt::Display for Solitaire {
    // this function is too long but, it's not important to performance so i'm lazy
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

        for i in 0..N_SUITS {
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
                    && (self.visible_mask ^ self.top_mask)
                        & card_mask(&Card::new(KING_RANK, king_suit))
                        == 0
                {
                    king_suit += 1;
                }
                if king_suit < 4 {
                    king_suit += 1;
                    Card::new(KING_RANK, king_suit - 1)
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
        let mut i = 0; // skip the hidden layer

        loop {
            let mut is_print = false;
            for j in 0..N_PILES {
                let ref cur_pile = piles[j as usize];

                let n_hidden = self.n_hidden[j as usize].saturating_sub(1);
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
    use rand::prelude::*;

    use crate::shuffler::shuffled_deck;

    // Note this useful idiom: importing names from outer (for mod tests) scope.
    use super::*;

    #[test]
    fn test_draw_unrolling() {
        let mut rng = StdRng::seed_from_u64(14);

        let mut moves = Vec::<Move>::new();

        let mut test = Vec::<(u8, Card)>::new();
        for i in 0..100 {
            let mut game = Solitaire::new(&shuffled_deck(12 + i), 3);
            for _ in 0..100 {
                let mut truth = game
                    .deck
                    .iter_all()
                    .filter(|x| !matches!(x.2, Drawable::None))
                    .map(|x| (x.0, *x.1))
                    .collect::<Vec<(u8, Card)>>();

                test.clear();
                game.deck.iter_callback(false, |pos, x| {
                    test.push((pos, *x));
                    false
                });

                test.sort_by_key(|x| x.0);
                truth.sort_by_key(|x| x.0);

                assert_eq!(test, truth);

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

        for i in 0..1000 {
            let mut game = Solitaire::new(&shuffled_deck(12 + i), 3);
            for _ in 0..100 {
                moves.clear();
                game.list_moves::<false>(&mut moves);
                if moves.len() == 0 {
                    break;
                }

                let state = game.encode();
                let ids: Vec<(u8, Card, Drawable)> =
                    game.deck.iter_all().map(|x| (x.0, *x.1, x.2)).collect();

                let m = moves.choose(&mut rng).unwrap();
                let undo = game.do_move(m);
                let next_state = game.encode();
                assert_ne!(next_state, state);
                game.undo_move(m, &undo);
                let new_ids: Vec<(u8, Card, Drawable)> =
                    game.deck.iter_all().map(|x| (x.0, *x.1, x.2)).collect();

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

        for i in 0..1000 {
            let mut game = Solitaire::new(&shuffled_deck(12 + i), 3);
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
