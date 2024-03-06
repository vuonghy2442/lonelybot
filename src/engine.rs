use crate::card::{Card, KING_RANK, N_CARDS, N_RANKS, N_SUITS};
use crate::deck::{Deck, N_HIDDEN_CARDS, N_PILES};
use crate::shuffler::CardDeck;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Move {
    DeckStack(Card),
    PileStack(Card),
    DeckPile(Card),
    StackPile(Card),
    Reveal(Card),
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
}

pub type Encode = u64;

const HALF_MASK: u64 = 0x33333333_3333333;
const ALT_MASK: u64 = 0x55555555_5555555;
// const RANK_MASK: u64 = 0x11111111_11111111;

const KING_MASK: u64 = 0xF << (N_SUITS * KING_RANK);

const SUIT_MASK: [u64; N_SUITS as usize] = [
    0x41414141_41414141,
    0x82828282_82828282,
    0x14141414_14141414,
    0x28282828_28282828,
];

const COLOR_MASK: [u64; 2] = [SUIT_MASK[0] | SUIT_MASK[1], SUIT_MASK[2] | SUIT_MASK[3]];

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

pub type UndoInfo = u8;

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
        bottom_mask * 3
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

        (COLOR_MASK[0] & full_mask(d.0 * 4)) | (COLOR_MASK[1] & full_mask(d.1 * 4))
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
        let [pile_stack, deck_stack, stack_pile, deck_pile, reveal] =
            self.gen_moves::<DOMINANCES>();

        iter_mask(deck_stack, |c| moves.push(Move::DeckStack(*c)));
        iter_mask(pile_stack, |c| moves.push(Move::PileStack(*c)));
        iter_mask(reveal, |c| moves.push(Move::Reveal(*c)));
        iter_mask(deck_pile, |c| moves.push(Move::DeckPile(*c)));
        iter_mask(stack_pile, |c| moves.push(Move::StackPile(*c)));
    }

    pub fn gen_moves<const DOMINANCES: bool>(self: &Solitaire) -> [u64; 5] {
        let vis = self.get_visible_mask();
        let top = self.get_top_mask();

        // this mask represent the rank & even^red type to be movable
        let bm = self.get_bottom_mask();

        let sm = self.get_stack_mask();
        let dsm = if DOMINANCES {
            self.get_stack_dominances_mask()
        } else {
            0
        };

        // moving pile to stack can result in revealing the hidden card
        let pile_stack = bm & vis & sm; // remove mask
        let pile_stack_dom = pile_stack & dsm;

        if pile_stack_dom != 0 {
            // if there is some card that is guarantee to be fine to stack do it
            return [pile_stack_dom.wrapping_neg() & pile_stack_dom, 0, 0, 0, 0];
        }
        // getting the stackable cards without revealing
        // since revealing won't be undoable unless in the rare case that the card is stackable to that hidden card
        let unnessary_stack = pile_stack & !top;

        // unnessarily stackable pair of same-colored cards with lowest value
        let least = {
            let ustack = (unnessary_stack | (unnessary_stack >> 1)) & ALT_MASK;
            (ustack & ustack.wrapping_neg()) * 0b11
        };

        if DOMINANCES && unnessary_stack.count_ones() >= 3 {
            return [unnessary_stack & least, 0, 0, 0, 0];
        }

        // computing which card can be accessible from the deck (K+ representation) and if the last card can stack dominantly
        let (deck_mask, dom) = self.get_deck_mask::<DOMINANCES>();
        // no dominances for draw_step = 1 yet
        if dom {
            // not very useful as dominance
            return [0, deck_mask, 0, 0, 0];
        }

        // free slot will compute the empty position that a card can be put into (can be king)
        let free_slot = {
            // counting how many piles are occupied (having a top card/being a king card)
            let free_pile = ((vis & KING_MASK) | top).count_ones() < N_PILES as u32;
            let king_mask = if free_pile { KING_MASK } else { 0 };
            (bm >> 4) | king_mask
        };

        // compute which card can be move to pile from stack (without being immediately move back ``!dsm``)
        let stack_pile = swap_pair(sm >> 4) & free_slot & !dsm;

        // map the card mask of lowest rank to its card
        // from mask will take the lowest bit
        // this will disallow having 2 move-to-stack-able suits of same color
        let filter_sp = if !DOMINANCES || unnessary_stack == 0 {
            !0
        } else if unnessary_stack & (unnessary_stack >> 1) & ALT_MASK > 0 {
            // is same check when the two stackable card of same color and same rank exists
            // if there is a pair of same card you can only move the card up or reveal something
            0
        } else {
            // seperate the stackable cards by color
            let ss: [u64; 2] = std::array::from_fn(|i| unnessary_stack & COLOR_MASK[i]);
            // the new stacked card should be decreasing :)
            (if ss[0] == 0 {
                // don't change this to 0
                // there is a case where even though there's no unncessary stackable card with color 0
                // but there's still a stackable card
                COLOR_MASK[0]
            } else {
                SUIT_MASK[from_mask(&ss[0]).suit() as usize]
            } | if ss[1] == 0 {
                COLOR_MASK[1]
            } else {
                SUIT_MASK[from_mask(&ss[1]).suit() as usize]
            })
        };

        // moving directly from deck to stack
        let deck_stack = deck_mask & sm;
        // moving from deck to pile without immediately to to stack ``!(dsm & sm)``
        let deck_pile = deck_mask & free_slot & !(dsm & sm);

        // revealing a card by moving the top card to another pile (not to stack)
        let reveal = top & free_slot;

        let (filter_ps, filter_new, filter_ds) = if DOMINANCES && least > 0 {
            // only stack to the least lexigraphically card (or 2 cards if same color)
            // do not use the deck stack when have unnecessary stackable cards
            (least, least >> 4, 0)
        } else {
            // can do anything :)
            (!0, !0, !0)
        };
        return [
            // only return the least lexicographically card
            pile_stack & filter_ps,
            deck_stack & filter_ds,
            stack_pile & filter_sp,
            deck_pile & filter_new,
            reveal & filter_new,
        ];
    }

    pub const fn get_rev_move(&self, m: &Move) -> Option<Move> {
        // check if this move can be undo using a legal move in the game
        match m {
            Move::PileStack(c) => {
                if self.top_mask & card_mask(c) == 0 {
                    Some(Move::StackPile(*c))
                } else {
                    None
                }
            }
            Move::StackPile(c) => Some(Move::PileStack(*c)),
            _ => None,
        }
    }

    pub fn make_stack<const DECK: bool>(self: &mut Solitaire, mask: &u64) -> UndoInfo {
        let card = from_mask(&mask);
        self.final_stack[card.suit() as usize] += 1;

        if DECK {
            let offset = self.deck.get_offset();
            let pos = self.deck.find_card(card).unwrap();
            self.deck.draw(pos);
            offset
        } else {
            let hidden = (self.top_mask & mask) != 0;
            self.visible_mask ^= mask;
            if hidden {
                self.make_reveal(mask);
            }
            hidden as u8
        }
    }

    pub fn unmake_stack<const DECK: bool>(self: &mut Solitaire, mask: &u64, info: &UndoInfo) {
        let card = from_mask(&mask);
        self.final_stack[card.suit() as usize] -= 1;

        if DECK {
            self.deck.push(card);
            self.deck.set_offset((*info & 31) as u8);
        } else {
            self.visible_mask |= mask;
            if *info & 1 != 0 {
                self.unmake_reveal(mask, &Default::default());
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
            offset
        } else {
            self.final_stack[card.suit() as usize] -= 1;
            Default::default()
        }
    }

    pub fn unmake_pile<const DECK: bool>(self: &mut Solitaire, mask: &u64, info: &UndoInfo) {
        let card = from_mask(&mask);

        self.visible_mask &= !mask;

        if DECK {
            self.deck.push(card);
            self.deck.set_offset((*info & 31) as u8);
        } else {
            self.final_stack[card.suit() as usize] += 1;
        }
    }

    pub const fn get_deck(self: &Solitaire) -> &Deck {
        &self.deck
    }

    pub const fn get_stack(self: &Solitaire) -> &[u8; N_SUITS as usize] {
        &self.final_stack
    }

    pub const fn get_n_hidden(self: &Solitaire) -> &[u8; N_PILES as usize] {
        &self.n_hidden
    }

    pub const fn get_hidden(self: &Solitaire, pos: u8, n_hid: u8) -> Card {
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
            if new_card.rank() < N_RANKS - 1 || self.n_hidden[pos as usize] != 1 {
                self.top_mask |= revealed;
            }
        }
        Default::default()
    }

    pub fn unmake_reveal(self: &mut Solitaire, m: &u64, _info: &UndoInfo) {
        let card = from_mask(&m);
        let pos = self.hidden[card.value() as usize];

        self.top_mask |= m;

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

    // can be made const fn
    fn encode_stack(self: &Solitaire) -> u16 {
        // considering to make it incremental?
        self.final_stack
            .iter()
            .fold(0u16, |res, cur| (res << 4) + (*cur as u16))
    }

    // can be made const fn
    fn encode_hidden(self: &Solitaire) -> u16 {
        self.n_hidden
            .iter()
            .enumerate()
            .rev()
            .fold(0u16, |res, cur| res * (cur.0 as u16 + 2) + *cur.1 as u16)
    }

    // can be made const fn
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

    pub fn get_normal_piles(self: &Solitaire) -> [Vec<Card>; N_PILES as usize] {
        let mut king_suit = 0;
        std::array::from_fn(|i| {
            let n_hid = self.n_hidden[i];
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
                    return Vec::new();
                }
            } else {
                self.get_hidden(i as u8, n_hid - 1)
            };

            let mut cards = Vec::<Card>::new();
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
            cards
        })
    }
}

#[cfg(test)]
mod tests {
    use rand::prelude::*;

    use crate::deck::Drawable;
    use crate::shuffler::default_shuffle;

    // Note this useful idiom: importing names from outer (for mod tests) scope.
    use super::*;

    #[test]
    fn test_draw_unrolling() {
        let mut rng = StdRng::seed_from_u64(14);

        let mut moves = Vec::<Move>::new();

        let mut test = Vec::<(u8, Card)>::new();
        for i in 0..100 {
            let mut game = Solitaire::new(&default_shuffle(12 + i), 3);
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
            let mut game = Solitaire::new(&default_shuffle(12 + i), 3);
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
            let mut game = Solitaire::new(&default_shuffle(12 + i), 3);
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
