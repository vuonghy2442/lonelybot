use core::array;

use arrayvec::ArrayVec;

use crate::card::{card_mask, from_mask, Card, KING_RANK, N_CARDS, N_RANKS, N_SUITS};
use crate::deck::{Deck, N_HIDDEN_CARDS, N_PILES};

use crate::hidden::Hidden;
use crate::shuffler::CardDeck;
use crate::standard::{PileVec, StandardSolitaire};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Move {
    DeckStack(Card),
    PileStack(Card),
    DeckPile(Card),
    StackPile(Card),
    Reveal(Card),
}

impl Move {
    pub const FAKE: Self = Move::DeckPile(Card::FAKE);
}

#[derive(Debug, Clone)]
pub struct Solitaire {
    hidden: Hidden,
    final_stack: [u8; N_SUITS as usize],
    deck: Deck,

    visible_mask: u64,
    top_mask: u64,
}

pub type Encode = u64;

const HALF_MASK: u64 = 0x3333_3333_3333_3333;
const ALT_MASK: u64 = 0x5555_5555_5555_5555;
const RANK_MASK: u64 = 0x1111_1111_1111_1111;

const KING_MASK: u64 = 0xF << (N_SUITS * KING_RANK);

const SUIT_MASK: [u64; N_SUITS as usize] = [
    0x4141_4141_4141_4141,
    0x8282_8282_8282_8282,
    0x1414_1414_1414_1414,
    0x2828_2828_2828_2828,
];

const COLOR_MASK: [u64; 2] = [SUIT_MASK[0] | SUIT_MASK[1], SUIT_MASK[2] | SUIT_MASK[3]];

pub const N_MOVES_MAX: usize = (N_PILES * 2 + N_SUITS * 2 - 1) as usize;

pub type MoveVec = ArrayVec<Move, N_MOVES_MAX>;

#[must_use]
const fn swap_pair(a: u64) -> u64 {
    let half = (a & HALF_MASK) << 2;
    ((a >> 2) & HALF_MASK) | half
}

#[must_use]
const fn min(a: u8, b: u8) -> u8 {
    if a < b {
        a
    } else {
        b
    }
}

#[must_use]
const fn full_mask(i: u8) -> u64 {
    (1 << i) - 1
}

fn iter_mask_opt<T>(mut m: u64, mut func: impl FnMut(Card) -> Option<T>) -> Option<T> {
    while m > 0 {
        let c = from_mask(&m);
        let r = func(c);
        if r.is_some() {
            return r;
        };
        m &= m.wrapping_sub(1);
    }
    None
}

pub fn iter_moves<T>(moves: [u64; 5], mut func: impl FnMut(Move) -> Option<T>) -> Option<T> {
    // the only case a card can be in two different moves
    // deck_to_stack/deck_to_pile (maximum duplicate N_SUITS cards)
    // reveal/pile_stack (maximum duplicate N_SUITS cards)
    // these two cases can't happen simultaneously (only max N_SUIT card can be move to a stack)
    // => Maximum moves <= N_CARDS + N_SUIT
    let [pile_stack, deck_stack, stack_pile, deck_pile, reveal] = moves;

    if let Some(r) = iter_mask_opt::<T>(reveal, |c| func(Move::Reveal(c))) {
        // maximum min(N_PILES - 1, N_CARDS) moves (can't have a cycle of reveal piles)
        Some(r)
    } else if let Some(r) = iter_mask_opt::<T>(pile_stack, |c| func(Move::PileStack(c))) {
        // maximum min(N_PILES, N_SUITS) moves
        Some(r)
    } else if let Some(r) = iter_mask_opt::<T>(deck_pile, |c| func(Move::DeckPile(c))) {
        // maximum min(N_PILES, N_DECK) moves
        Some(r)
    } else if let Some(r) = iter_mask_opt::<T>(deck_stack, |c| func(Move::DeckStack(c))) {
        // maximum min(N_DECK, N_SUITS) moves
        // deck_stack and pile_stack can't happen simultaneously so both of the combine can't have more than
        // N_SUITS move
        Some(r)
    } else {
        // maximum min(N_PILES, N_SUIT) moves
        iter_mask_opt::<T>(stack_pile, |c| func(Move::StackPile(c)))
    }
    // <= N_PILES * 2 + N_SUITS * 2 - 1 = 14 + 8 - 1 = 21 moves
}

pub type UndoInfo = u8;

impl Solitaire {
    #[must_use]
    pub fn new(cards: &CardDeck, draw_step: u8) -> Self {
        let hidden_piles: [Card; N_HIDDEN_CARDS as usize] =
            cards[0..N_HIDDEN_CARDS as usize].try_into().unwrap();

        let mut visible_mask = 0;

        for i in 0..N_PILES {
            let pos = (i + 2) * (i + 1) / 2 - 1;
            visible_mask |= card_mask(&hidden_piles[pos as usize]);
        }

        let deck: Deck = Deck::new(
            cards[(N_HIDDEN_CARDS) as usize..].try_into().unwrap(),
            draw_step,
        );

        let mut res = Self {
            hidden: Hidden::new(hidden_piles),
            final_stack: [0u8; 4],
            deck,
            visible_mask,
            top_mask: Default::default(),
        };
        res.top_mask = res.compute_top_mask();
        res
    }

    #[must_use]
    fn compute_top_mask(&self) -> u64 {
        let mut top_mask = 0;
        for pos in 0..N_PILES {
            if let Some((card, rest)) = self.hidden.get(pos).split_last() {
                if !rest.is_empty() || card.rank() < KING_RANK {
                    top_mask |= card_mask(card);
                }
            }
        }
        top_mask
    }

    #[must_use]
    pub const fn get_visible_mask(&self) -> u64 {
        self.visible_mask
    }

    #[must_use]
    pub const fn get_top_mask(&self) -> u64 {
        self.top_mask
    }

    #[must_use]
    pub const fn get_extended_top_mask(&self) -> u64 {
        // also consider the kings to be the top cards
        self.top_mask | (self.visible_mask & KING_MASK)
        // (self.top_mask | KING_MASK) & self.visible_mask
    }

    #[must_use]
    pub const fn get_bottom_mask(&self) -> u64 {
        let vis = self.get_visible_mask();
        let non_top = vis ^ self.get_top_mask();
        let xor_non_top = non_top ^ (non_top >> 1);
        let xor_vis = vis ^ (vis >> 1);
        let or_non_top = non_top | (non_top >> 1);
        let or_vis = vis | (vis >> 1);

        let xor_all = xor_vis ^ (xor_non_top << 4);

        let bottom_mask = (xor_all | !(or_non_top << 4)) & or_vis & ALT_MASK;

        //shared rank
        bottom_mask * 0b11
    }

    #[must_use]
    pub const fn get_stack_mask(&self) -> u64 {
        let s = self.final_stack;

        (SUIT_MASK[0] & (0b1111 << (s[0] * 4)))
            | (SUIT_MASK[1] & (0b1111 << (s[1] * 4)))
            | (SUIT_MASK[2] & (0b1111 << (s[2] * 4)))
            | (SUIT_MASK[3] & (0b1111 << (s[3] * 4)))
    }

    #[must_use]
    pub const fn get_stack_dominance_mask(&self) -> u64 {
        let s = self.final_stack;
        let d = (min(s[0], s[1]), min(s[2], s[3]));
        let d = (min(d.0 + 1, d.1) + 2, min(d.0, d.1 + 1) + 2);

        (COLOR_MASK[0] & full_mask(d.0 * 4)) | (COLOR_MASK[1] & full_mask(d.1 * 4))
    }

    #[must_use]
    pub fn get_deck_mask<const DOMINANCE: bool>(&self) -> (u64, bool) {
        let filter = DOMINANCE
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

        // TODO: dominance for draw_step == 1
        (mask, false)
    }

    #[must_use]
    pub fn list_moves<const DOMINANCE: bool>(&self) -> MoveVec {
        let mut moves = MoveVec::new();

        iter_moves(self.gen_moves::<DOMINANCE>(), |m| {
            moves.push(m);
            None::<()>
        });

        moves
    }

    #[must_use]
    pub fn gen_moves<const DOMINANCE: bool>(&self) -> [u64; 5] {
        let vis = self.get_visible_mask();
        let top = self.get_top_mask();

        // this mask represent the rank & even^red type to be movable
        let bm = self.get_bottom_mask();

        let sm = self.get_stack_mask();
        let dsm = if DOMINANCE {
            self.get_stack_dominance_mask()
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
        let redundant_stack = pile_stack & !top;
        let least_stack = redundant_stack & redundant_stack.wrapping_neg();

        if DOMINANCE && redundant_stack.count_ones() >= 3 {
            return [least_stack, 0, 0, 0, 0];
        }

        // computing which card can be accessible from the deck (K+ representation) and if the last card can stack dominantly
        let (deck_mask, dom) = self.get_deck_mask::<DOMINANCE>();
        // no dominance for draw_step = 1 yet
        if dom {
            // not very useful as dominance
            return [0, deck_mask, 0, 0, 0];
        }

        // free slot will compute the empty position that a card can be put into (can be king)
        let free_slot = {
            // counting how many piles are occupied (having a top card/being a king card)
            let free_pile = self.get_extended_top_mask().count_ones() < u32::from(N_PILES);
            let king_mask = if free_pile { KING_MASK } else { 0 };
            (bm >> 4) | king_mask
        };

        // compute which card can be move to pile from stack (without being immediately move back ``!dsm``)
        let stack_pile = swap_pair(sm >> 4) & free_slot & !dsm;

        // moving directly from deck to stack
        let deck_stack = deck_mask & sm;

        let paired_stack = pile_stack & (pile_stack >> 1) & ALT_MASK;
        // map the card mask of lowest rank to its card
        // from mask will take the lowest bit
        // this will disallow having 2 move-to-stack-able suits of same color
        // only return the least lexicographically card (stack_pile)
        let (stack_pile, pile_stack, deck_stack, free_slot) = if !DOMINANCE || least_stack == 0 {
            (stack_pile, pile_stack, deck_stack, free_slot)
        } else if paired_stack > 0 {
            // is same check when the two stackable card of same color and same rank exists
            // if there is a pair of same card you can only move the card up or reveal something
            // unnecessarily stackable pair of same-colored cards with lowest value
            // only stack to the least lexicographically card (or 2 cards if same color)
            // do not use the deck stack when have unnecessary stackable cards
            let rm = paired_stack * 0b11;
            (0, rm, 0, rm >> 4)
        } else {
            // getting the stackable stuff when unstack the lowest one :)
            let least = least_stack | (least_stack >> 1);
            let least = (least & ALT_MASK) * 0b11;
            let extra = redundant_stack | (vis & sm & (least << 4));
            // check if unstackable by suit
            let suit_unstack: [bool; 4] = core::array::from_fn(|i| extra & SUIT_MASK[i] == 0);

            if (suit_unstack[0] || suit_unstack[1]) && (suit_unstack[2] || suit_unstack[3]) {
                // this filter is to prevent making a double same color, inturn make 3 unnecessary stackable card
                // though it can make triple stackable cards in some case but in those case it will be revert immediately
                // i.e. the last card stack is the smallest one

                let triple_stackable = {
                    // finding card that can potentially become stackable in the next move
                    let pot_stack = (vis ^ top) & sm;
                    let pot_stack = pot_stack | (pot_stack >> 1);

                    // if one of them is a top card then, the next turn will be not reversible

                    // due to both of the card should be stackable and not being a top card
                    // they would have both color of their parents hence (their parent surely not stackable)
                    // the only way they are stackable is the same rank (and larger color)
                    let stack_rank = (least >> 2) & RANK_MASK;

                    (pot_stack & stack_rank) * 0b11
                };

                let suit_filter = (if suit_unstack[0] { SUIT_MASK[1] } else { 0 }
                    | if suit_unstack[1] { SUIT_MASK[0] } else { 0 }
                    | if suit_unstack[2] { SUIT_MASK[3] } else { 0 }
                    | if suit_unstack[3] { SUIT_MASK[2] } else { 0 });

                (
                    // the new stacked card should be decreasing :)
                    stack_pile & suit_filter & (least_stack - 1) & !triple_stackable,
                    least_stack,
                    0,
                    // only unlocking new stuff when doesn't have both color in the same rank
                    if (least << 2) & redundant_stack > 0 {
                        0
                    } else {
                        least >> 4
                    },
                )
            } else {
                // double card color
                (0, least_stack, 0, 0)
            }
        };

        // moving from deck to pile without immediately to to stack ``!(dsm & sm)``
        let deck_pile = deck_mask & free_slot & !(dsm & sm);

        // revealing a card by moving the top card to another pile (not to stack)
        let reveal = top & free_slot;

        [pile_stack, deck_stack, stack_pile, deck_pile, reveal]
    }

    #[must_use]
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

    pub fn make_stack<const DECK: bool>(&mut self, mask: &u64) -> UndoInfo {
        let card = from_mask(mask);
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
            u8::from(hidden)
        }
    }

    pub fn unmake_stack<const DECK: bool>(&mut self, mask: &u64, info: &UndoInfo) {
        let card = from_mask(mask);
        self.final_stack[card.suit() as usize] -= 1;

        if DECK {
            self.deck.push(card);
            self.deck.set_offset(*info & 31);
        } else {
            self.visible_mask |= mask;
            if *info & 1 != 0 {
                self.unmake_reveal(mask, &Default::default());
            }
        }
    }

    pub fn make_pile<const DECK: bool>(&mut self, mask: &u64) -> UndoInfo {
        let card = from_mask(mask);
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

    pub fn unmake_pile<const DECK: bool>(&mut self, mask: &u64, info: &UndoInfo) {
        let card = from_mask(mask);

        self.visible_mask &= !mask;

        if DECK {
            self.deck.push(card);
            self.deck.set_offset(*info & 31);
        } else {
            self.final_stack[card.suit() as usize] += 1;
        }
    }

    #[must_use]
    pub const fn get_deck(&self) -> &Deck {
        &self.deck
    }

    #[must_use]
    pub const fn get_stack(&self) -> &[u8; N_SUITS as usize] {
        &self.final_stack
    }

    pub fn make_reveal(&mut self, m: &u64) -> UndoInfo {
        let card = from_mask(m);
        let pos = self.hidden.find(&card);
        self.top_mask &= !m;

        let new_card = self.hidden.pop(pos);
        if let Some(&new_card) = new_card {
            let revealed = card_mask(&new_card);
            self.visible_mask |= revealed;
            if new_card.rank() < KING_RANK || self.hidden.len(pos) > 1 {
                // if it's not the king mask or there's some hidden cards then set it as the top card
                self.top_mask |= revealed;
            }
        }
        Default::default()
    }

    pub fn unmake_reveal(&mut self, m: &u64, _info: &UndoInfo) {
        let card = from_mask(m);
        let pos = self.hidden.find(&card);

        self.top_mask |= m;

        if let Some(new_card) = self.hidden.peek(pos) {
            let unrevealed = !card_mask(new_card);
            self.visible_mask &= unrevealed;
            self.top_mask &= unrevealed;
        }
        self.hidden.unpop(pos);
    }

    pub fn do_move(&mut self, m: &Move) -> UndoInfo {
        match m {
            Move::DeckStack(c) => self.make_stack::<true>(&card_mask(c)),
            Move::PileStack(c) => self.make_stack::<false>(&card_mask(c)),
            Move::DeckPile(c) => self.make_pile::<true>(&card_mask(c)),
            Move::StackPile(c) => self.make_pile::<false>(&card_mask(c)),
            Move::Reveal(c) => self.make_reveal(&card_mask(c)),
        }
    }

    pub fn undo_move(&mut self, m: &Move, undo: &UndoInfo) {
        match m {
            Move::DeckStack(c) => self.unmake_stack::<true>(&card_mask(c), undo),
            Move::PileStack(c) => self.unmake_stack::<false>(&card_mask(c), undo),
            Move::DeckPile(c) => self.unmake_pile::<true>(&card_mask(c), undo),
            Move::StackPile(c) => self.unmake_pile::<false>(&card_mask(c), undo),
            Move::Reveal(c) => self.unmake_reveal(&card_mask(c), undo),
        }
    }

    #[must_use]
    pub fn is_win(&self) -> bool {
        // What a shame this is not a const function :(
        self.final_stack == [N_RANKS; N_SUITS as usize]
    }

    #[must_use]
    pub fn is_sure_win(&self) -> bool {
        self.deck.len() <= 1 && self.hidden.all_turn_up()
    }

    #[must_use]
    const fn stackable(&self, rank: u8, suit: u8) -> bool {
        self.final_stack[suit as usize] == rank && rank < N_RANKS
    }

    #[must_use]
    const fn stack_dominance(&self, rank: u8, suit: u8) -> bool {
        let stack = &self.final_stack;
        let suit = suit as usize;
        // allowing worrying back :)
        rank <= stack[suit ^ 2] + 1
            && rank <= stack[suit ^ 2 ^ 1] + 1
            && rank <= stack[suit ^ 1] + 2
    }

    // can be made const fn
    #[must_use]
    fn encode_stack(&self) -> u16 {
        // considering to make it incremental?
        self.final_stack
            .iter()
            .rev()
            .fold(0u16, |res, cur| (res << 4) + u16::from(*cur))
    }

    // can be made const fn
    #[must_use]
    pub fn encode(&self) -> Encode {
        let stack_encode = self.encode_stack(); // 16 bits (can be reduce to 15)
        let hidden_encode = self.hidden.encode(); // 16 bits
        let deck_encode = self.deck.encode(); // 29 bits (can be reduced to 25)

        u64::from(stack_encode)
            | u64::from(hidden_encode) << 16
            | u64::from(deck_encode) << (16 + 16)
    }

    #[must_use]
    fn compute_visible_mask(&self) -> u64 {
        let mut nonvis_mask = 0;
        // final stack
        for suit in 0..N_SUITS {
            for rank in 0..self.final_stack[suit as usize] {
                nonvis_mask |= card_mask(&Card::new(rank, suit));
            }
        }

        // hidden
        nonvis_mask |= self.hidden.mask();

        for c in self.deck.iter() {
            nonvis_mask |= card_mask(c);
        }

        full_mask(N_CARDS) ^ nonvis_mask
    }

    pub fn decode(&mut self, encode: Encode) {
        let (stack_encode, hidden_encode, deck_encode) =
            (encode as u16, (encode >> 16) as u16, (encode >> 32) as u32);
        // decode stack
        self.final_stack = array::from_fn(|i| (stack_encode >> (4 * i)) as u8 & 0xF);
        // decode hidden
        self.hidden.decode(hidden_encode);
        // decode visible
        self.deck.decode(deck_encode);

        self.visible_mask = self.compute_visible_mask();
        self.top_mask = self.compute_top_mask();
    }
    #[must_use]
    pub fn get_hidden(&self) -> &Hidden {
        &self.hidden
    }

    #[must_use]
    pub fn get_hidden_mut(&mut self) -> &mut Hidden {
        &mut self.hidden
    }

    #[must_use]
    pub fn get_visible_piles(&self) -> [PileVec; N_PILES as usize] {
        let mut king_suit = 0;
        core::array::from_fn(|pos| {
            let pos = pos as u8;
            let last_card = self.hidden.peek(pos).unwrap_or(&Card::FAKE);

            let mut start_card = if self.hidden.len(pos) <= 1 && last_card.rank() >= KING_RANK {
                while king_suit < N_SUITS
                    && (self.visible_mask ^ self.top_mask)
                        & card_mask(&Card::new(KING_RANK, king_suit))
                        == 0
                {
                    king_suit += 1;
                }
                if king_suit < N_SUITS {
                    king_suit += 1;
                    Card::new(KING_RANK, king_suit - 1)
                } else {
                    return PileVec::new();
                }
            } else {
                *last_card
            };

            let mut cards = PileVec::new();
            loop {
                // push start card
                cards.push(start_card);

                if start_card.rank() == 0 {
                    break;
                }

                let has_both = card_mask(&start_card.swap_suit()) & self.visible_mask != 0;
                let next_card = start_card.reduce_rank().swap_color();

                let possible_cards = self.top_mask ^ self.visible_mask;
                start_card = if !has_both && possible_cards & card_mask(&next_card) == 0 {
                    // not a possible cards => switch suit
                    next_card.swap_suit()
                } else {
                    next_card
                };

                if possible_cards & card_mask(&start_card) == 0 {
                    // if it's not good then break
                    break;
                }
            }
            cards
        })
    }

    #[must_use]
    pub fn is_valid(&self) -> bool {
        // TODO: test for if visible mask and top_mask make sense to build bottom mask
        if self.top_mask | self.visible_mask != self.visible_mask {
            return false;
        }

        if self.compute_top_mask() != self.top_mask
            || self.get_extended_top_mask().count_ones() > N_PILES.into()
        {
            return false;
        }

        if !self.hidden.is_valid() {
            return false;
        }

        let total_cards = self.visible_mask.count_ones() as u8
            + self.final_stack.iter().sum::<u8>()
            + self.deck.len()
            + self.hidden.total_down_cards();

        if total_cards != N_CARDS {
            return false;
        }

        if self.compute_visible_mask() != self.visible_mask {
            return false;
        }

        true
    }

    #[must_use]
    pub fn equivalent_to(&self, other: &Self) -> bool {
        // check equivalent states
        self.deck.equivalent_to(&other.deck)
            && self.final_stack == other.final_stack
            && self.top_mask == other.top_mask
            && self.visible_mask == other.visible_mask
            && self.hidden.normalize() == other.hidden.normalize()
    }
}

impl From<&StandardSolitaire> for Solitaire {
    fn from(game: &StandardSolitaire) -> Self {
        let mut visible_mask: u64 = 0;

        for i in 0..N_PILES as usize {
            for c in &game.piles[i] {
                visible_mask |= card_mask(c);
            }
        }
        let mut top_mask: u64 = 0;

        for (p_vis, p_hid) in game.piles.iter().zip(game.hidden_piles.iter()) {
            if let Some(c) = p_vis.first() {
                if c.rank() < KING_RANK || p_hid.len() > 0 {
                    top_mask |= card_mask(c);
                }
            }
        }

        Self {
            hidden: Hidden::from_piles(
                &game.hidden_piles,
                &core::array::from_fn(|i| game.piles[i].first().copied()),
            ),
            final_stack: game.final_stack,
            deck: game.deck.clone(),
            visible_mask,
            top_mask,
        }
    }
}

#[cfg(test)]
mod tests {
    use rand::prelude::*;

    use crate::deck::{Drawable, N_FULL_DECK};
    use crate::shuffler::default_shuffle;

    // Note this useful idiom: importing names from outer (for mod tests) scope.
    use super::*;

    #[test]
    fn test_draw_unrolling() {
        let mut rng = StdRng::seed_from_u64(14);

        let mut test = ArrayVec::<(u8, Card), N_FULL_DECK>::new();
        for i in 0..100 {
            let mut game = Solitaire::new(&default_shuffle(12 + i), 3);
            for _ in 0..100 {
                let mut stack_mask: u64 = 0;
                // fill in final stack
                for suit in 0..N_SUITS {
                    let rank = game.final_stack[suit as usize];
                    stack_mask |= card_mask(&Card::new(rank, suit));
                }
                assert_eq!(stack_mask, game.get_stack_mask());

                let mut truth = game
                    .deck
                    .iter_all()
                    .filter(|x| !matches!(x.2, Drawable::None))
                    .map(|x| (x.0, *x.1))
                    .collect::<ArrayVec<(u8, Card), N_FULL_DECK>>();

                test.clear();
                game.deck.iter_callback(false, |pos, x| {
                    test.push((pos, *x));
                    false
                });

                test.sort_by_key(|x| x.0);
                truth.sort_by_key(|x| x.0);

                assert_eq!(test, truth);

                let moves = game.list_moves::<false>();
                if moves.is_empty() {
                    break;
                }
                game.do_move(moves.choose(&mut rng).unwrap());
            }
        }
    }

    #[test]
    fn test_undoing() {
        let mut rng = StdRng::seed_from_u64(14);

        for i in 0..1000 {
            let mut game = Solitaire::new(&default_shuffle(12 + i), 3);
            for _ in 0..100 {
                let moves = game.list_moves::<false>();
                if moves.is_empty() {
                    break;
                }

                let state = game.encode();
                game.decode(state);
                assert!(game.is_valid());

                let mut gg = game.clone();
                gg.hidden.clear();
                assert!(gg.is_valid());

                assert_eq!(game.encode(), state);

                let ids: ArrayVec<(u8, Card, Drawable), N_FULL_DECK> =
                    game.deck.iter_all().map(|x| (x.0, *x.1, x.2)).collect();

                let m = moves.choose(&mut rng).unwrap();
                let undo = game.do_move(m);
                let next_state = game.encode();
                assert_ne!(next_state, state);
                game.undo_move(m, &undo);
                let new_ids: ArrayVec<(u8, Card, Drawable), N_FULL_DECK> =
                    game.deck.iter_all().map(|x| (x.0, *x.1, x.2)).collect();

                assert_eq!(ids, new_ids);
                let undo_state = game.encode();
                assert_eq!(undo_state, state);
                game.decode(state);
                assert_eq!(game.encode(), state);
                assert!(game.equivalent_to(&gg));

                game.do_move(m);
                assert_eq!(game.encode(), next_state);
            }
        }
    }

    #[test]
    fn test_deep_undoing() {
        let mut rng = StdRng::seed_from_u64(14);

        for i in 0..1000 {
            const N_STEP: usize = 100;
            let mut game = Solitaire::new(&default_shuffle(12 + i), 3);
            let mut history = ArrayVec::<(Move, UndoInfo), N_STEP>::new();
            let mut enc = ArrayVec::<Encode, N_STEP>::new();
            let mut states = ArrayVec::<Solitaire, N_STEP>::new();

            assert!(game.is_valid());
            for _ in 0..N_STEP {
                let moves = game.list_moves::<false>();
                if moves.is_empty() {
                    break;
                }

                assert!(game.is_valid());
                enc.push(game.encode());
                states.push(game.clone());

                let m = moves.choose(&mut rng).unwrap();
                let undo = game.do_move(m);
                history.push((*m, undo));
            }

            let new_enc = enc.clone();

            for _ in 0..history.len() {
                let (m, undo) = history.pop().unwrap();
                game.undo_move(&m, &undo);
                assert_eq!(game.encode(), enc.pop().unwrap());
            }

            for (e, state) in new_enc.iter().zip(states) {
                let mut g = game.clone();
                g.decode(*e);
                assert!(g.is_valid());
                assert!(g.equivalent_to(&state));
            }
        }
    }

    #[test]
    fn shuffle_hidden() {
        let mut rng = StdRng::seed_from_u64(14);

        for i in 0..1000 {
            let mut game = Solitaire::new(&default_shuffle(12 + i), 3);
            for _ in 0..100 {
                let moves = game.list_moves::<false>();
                if moves.is_empty() {
                    break;
                }

                game.do_move(moves.choose(&mut rng).unwrap());

                game.hidden.shuffle(&mut rng);
                assert!(game.is_valid());
                game.hidden.clear();
                assert!(game.is_valid());
            }
        }
    }
}
