use core::num::NonZeroU8;

use rand::RngCore;

use crate::card::{
    Card, ALT_MASK, HALF_MASK, KING_MASK, KING_RANK, N_CARDS, N_SUITS, RANK_MASK, SUIT_MASK,
};
use crate::deck::{Deck, N_PILES, N_PILE_CARDS};
use crate::moves::{Move, MoveMask};
use crate::stack::Stack;
use crate::utils::full_mask;

use crate::hidden::Hidden;
use crate::shuffler::CardDeck;
use crate::standard::{PileVec, StandardSolitaire};

#[derive(Debug, Clone)]
pub struct Solitaire {
    hidden: Hidden,
    final_stack: Stack,
    deck: Deck,

    visible_mask: u64,
    locked_mask: u64,
}

pub type Encode = u64;

#[must_use]
const fn swap_pair(a: u64) -> u64 {
    let half = (a & HALF_MASK) << 2;
    ((a >> 2) & HALF_MASK) | half
}

pub type UndoInfo = u8;

impl Solitaire {
    #[must_use]
    /// # Panics
    ///
    /// Never (unless buggy)
    pub fn new(cards: &CardDeck, draw_step: NonZeroU8) -> Self {
        let hidden_piles: [Card; N_PILE_CARDS as usize] =
            cards[0..N_PILE_CARDS as usize].try_into().unwrap();

        let mut visible_mask = 0;

        for i in 0..N_PILES {
            let pos = (i + 2) * (i + 1) / 2 - 1;
            visible_mask |= hidden_piles[pos as usize].mask();
        }

        let deck: Deck = Deck::new(
            cards[(N_PILE_CARDS) as usize..].try_into().unwrap(),
            draw_step,
        );

        let hidden = Hidden::new(hidden_piles);

        Self {
            locked_mask: hidden.compute_locked_mask(),
            hidden,
            final_stack: Stack::default(),
            deck,
            visible_mask,
        }
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
    pub const fn get_hidden(&self) -> &Hidden {
        &self.hidden
    }

    pub fn hidden_shuffle<R: RngCore>(&mut self, rng: &mut R) {
        self.hidden.shuffle(rng);
    }

    pub fn hidden_clear(&mut self) {
        self.hidden.clear();
    }

    #[must_use]
    const fn get_visible_mask(&self) -> u64 {
        self.visible_mask
    }

    #[must_use]
    const fn get_locked_mask(&self) -> u64 {
        self.locked_mask
    }

    #[must_use]
    const fn get_extended_top_mask(&self) -> u64 {
        // also consider the kings to be the top cards
        self.visible_mask & (self.get_locked_mask() | KING_MASK)
    }

    #[must_use]
    const fn get_bottom_mask(&self) -> u64 {
        let vis = self.get_visible_mask();
        let free = vis & !self.get_locked_mask(); //maybe no need to & TODO: check later
        let xor_all = {
            let xor_free = free ^ (free >> 1);
            let xor_vis = vis ^ (vis >> 1);
            xor_vis ^ (xor_free << 4)
        };

        let bottom_mask = {
            let or_free = free | (free >> 1);
            let or_vis = vis | (vis >> 1);
            (xor_all | !(or_free << 4)) & or_vis & ALT_MASK
        };

        //shared rank
        bottom_mask * 0b11
    }

    #[must_use]
    fn get_deck_mask(&self, dom_stackable: u64) -> (u64, bool) {
        if self.deck.draw_step().get() == 1 {
            let mask = self.deck.compute_mask(false);
            let mask_dom = mask & dom_stackable;
            if mask_dom > 0 {
                (mask_dom & mask_dom.wrapping_neg(), true)
            } else {
                (mask, false)
            }
        } else {
            let Some(last_card) = self.deck.peek_last() else {
                return (0, false);
            };

            let filter = dom_stackable & last_card.mask() > 0;

            if filter && self.deck.is_pure() {
                (last_card.mask(), true)
            } else {
                (self.deck.compute_mask(filter), false)
            }
        }
    }

    #[must_use]
    pub fn gen_moves<const DOMINANCE: bool>(&self) -> MoveMask {
        let vis = self.get_visible_mask();
        let locked = self.get_locked_mask();

        // this mask represent the rank & even^red type to be movable
        let bm = self.get_bottom_mask();

        let sm = self.final_stack.mask();
        let dom_sm = if DOMINANCE {
            self.final_stack.dominance_mask()
        } else {
            0
        };

        // moving pile to stack can result in revealing the hidden card
        let pile_stack = bm & vis & sm; // remove mask
        let pile_stack_dom = pile_stack & dom_sm;

        if pile_stack_dom != 0 {
            // if there is some card that is guarantee to be fine to stack do it
            return MoveMask {
                pile_stack: pile_stack_dom.wrapping_neg() & pile_stack_dom,
                ..Default::default()
            };
        }
        // getting the stackable cards without revealing
        // since revealing won't be undoable unless in the rare case that the card is stackable to that hidden card
        let redundant_stack = pile_stack & !locked;
        let least_stack = redundant_stack & redundant_stack.wrapping_neg();

        if DOMINANCE && redundant_stack.count_ones() >= 3 {
            return MoveMask {
                pile_stack: least_stack,
                ..Default::default()
            };
        }

        // computing which card can be accessible from the deck (K+ representation) and if the last card can stack dominantly
        let (deck_mask, dom) = self.get_deck_mask(dom_sm & sm);
        // no dominance for draw_step = 1 yet
        if dom {
            // not very useful as dominance
            return MoveMask {
                deck_stack: deck_mask,
                ..Default::default()
            };
        }

        // free slot will compute the empty position that a card can be put into (can be king)
        let free_slot = {
            // counting how many piles are occupied (having a top card/being a king card)
            let free_pile = self.get_extended_top_mask().count_ones() < u32::from(N_PILES);
            let king_mask = if free_pile { KING_MASK } else { 0 };
            (bm >> 4) | king_mask
        };

        // compute which card can be move to pile from stack (without being immediately move back ``!dom_sm``)
        let stack_pile = swap_pair(sm >> 4) & free_slot & !dom_sm;

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
                    let pot_stack = !locked & vis & sm;
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

        // moving from deck to pile without immediately to to stack ``!(dom_sm & sm)``
        let deck_pile = deck_mask & free_slot & !(dom_sm & sm);

        // revealing a card by moving the top card to another pile (not to stack)
        // do not reveal king cards
        let reveal = vis & locked & free_slot & !(self.hidden.first_layer_mask() & KING_MASK);

        MoveMask {
            pile_stack,
            deck_stack,
            stack_pile,
            deck_pile,
            reveal,
        }
    }

    #[must_use]
    pub(crate) const fn reverse_move(&self, m: Move) -> Option<Move> {
        // check if this move can be undo using a legal move in the game
        match m {
            Move::PileStack(c) if self.get_locked_mask() & c.mask() == 0 => {
                Some(Move::StackPile(c))
            }
            Move::StackPile(c) => Some(Move::PileStack(c)),
            _ => None,
        }
    }

    /// # Panics
    ///
    /// Panic when the card mask is not a card in the deck
    /// It doesn't check if the card is drawable
    fn make_stack<const DECK: bool>(&mut self, card: Card) -> UndoInfo {
        let mask = card.mask();
        self.final_stack.push(card.suit());

        if DECK {
            let (found, pos) = self.deck.find_card(card);
            debug_assert!(found);

            let old_offset = self.deck.get_offset();
            self.deck.draw(pos);
            old_offset
        } else {
            let locked = (self.locked_mask & mask) != 0;
            self.visible_mask ^= mask;
            if locked {
                self.make_reveal(card);
            }
            u8::from(locked)
        }
    }

    fn unmake_stack<const DECK: bool>(&mut self, card: Card, info: UndoInfo) {
        let mask = card.mask();
        self.final_stack.pop(card.suit());

        if DECK {
            self.deck.push(card);
            self.deck.set_offset(info);
        } else {
            self.visible_mask |= mask;
            if info > 0 {
                self.unmake_reveal(card);
            }
        }
    }

    fn make_pile<const DECK: bool>(&mut self, card: Card) -> UndoInfo {
        let mask = card.mask();
        self.visible_mask |= mask;
        if DECK {
            let (found, pos) = self.deck.find_card(card);
            debug_assert!(found);

            let old_offset = self.deck.get_offset();
            self.deck.draw(pos);
            old_offset
        } else {
            self.final_stack.pop(card.suit());
            Default::default()
        }
    }

    fn unmake_pile<const DECK: bool>(&mut self, card: Card, info: UndoInfo) {
        self.visible_mask &= !card.mask();

        if DECK {
            self.deck.push(card);
            self.deck.set_offset(info);
        } else {
            self.final_stack.push(card.suit());
        }
    }

    fn make_reveal(&mut self, card: Card) {
        let pos = self.hidden.find(card);
        self.locked_mask &= !card.mask(); // should i use ^ or & !

        let new_card = self.hidden.pop(pos);
        if let Some(&new_card) = new_card {
            self.visible_mask |= new_card.mask();
        }
    }

    fn unmake_reveal(&mut self, card: Card) {
        let pos = self.hidden.find(card);
        self.locked_mask |= card.mask();

        if let Some(new_card) = self.hidden.peek(pos) {
            self.visible_mask &= !new_card.mask();
        }
        self.hidden.unpop(pos);
    }

    /// # Panics
    ///
    /// May panic when the move is invalid
    /// But it may do the move even when it's invalid so be careful for using this function
    pub(crate) fn do_move(&mut self, m: Move) -> UndoInfo {
        match m {
            Move::DeckStack(c) => self.make_stack::<true>(c),
            Move::PileStack(c) => self.make_stack::<false>(c),
            Move::DeckPile(c) => self.make_pile::<true>(c),
            Move::StackPile(c) => self.make_pile::<false>(c),
            Move::Reveal(c) => {
                self.make_reveal(c);
                UndoInfo::default()
            }
        }
    }

    /// It may leave the game in an invalid state with illegal move or wrong undo info
    pub(crate) fn undo_move(&mut self, m: Move, undo: UndoInfo) {
        match m {
            Move::DeckStack(c) => self.unmake_stack::<true>(c, undo),
            Move::PileStack(c) => self.unmake_stack::<false>(c, undo),
            Move::DeckPile(c) => self.unmake_pile::<true>(c, undo),
            Move::StackPile(c) => self.unmake_pile::<false>(c, undo),
            Move::Reveal(c) => self.unmake_reveal(c),
        }
    }

    #[must_use]
    pub fn is_win(&self) -> bool {
        // What a shame this is not a const function :(
        self.final_stack.is_full()
    }

    #[must_use]
    pub fn is_sure_win(&self) -> bool {
        self.deck.len() <= 1 && self.hidden.is_all_up()
    }

    // can be made const fn
    #[must_use]
    pub fn encode(&self) -> Encode {
        let stack_encode = self.final_stack.encode(); // 16 bits (can be reduce to 15)
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
            for rank in 0..self.final_stack.get(suit) {
                nonvis_mask |= Card::new(rank, suit).mask();
            }
        }

        // hidden
        nonvis_mask |= self.hidden.mask();

        for c in self.deck.iter() {
            nonvis_mask |= c.mask();
        }

        full_mask(N_CARDS) ^ nonvis_mask
    }

    pub(crate) fn decode(&mut self, encode: Encode) {
        #[allow(clippy::cast_possible_truncation)]
        let (stack_encode, hidden_encode, deck_encode) =
            (encode as u16, (encode >> 16) as u16, (encode >> 32) as u32);
        // decode stack
        self.final_stack = Stack::decode(stack_encode);
        // decode hidden
        self.hidden.decode(hidden_encode);
        // decode visible
        self.deck.decode(deck_encode);

        self.visible_mask = self.compute_visible_mask();
        self.locked_mask = self.hidden.compute_locked_mask();
    }

    #[must_use]
    pub fn compute_visible_piles(&self) -> [PileVec; N_PILES as usize] {
        // TODO: should add more comprehensive test for this
        let non_top = !self.get_locked_mask() & self.get_visible_mask();
        let mut king_suit = 0;
        core::array::from_fn(|pos| {
            #[allow(clippy::cast_possible_truncation)]
            let pos = pos as u8;

            let mut start_card = match self.hidden.peek(pos) {
                Some(&card) => card,
                None => {
                    while king_suit < N_SUITS
                        && non_top & Card::new(KING_RANK, king_suit).mask() == 0
                    {
                        king_suit += 1;
                    }

                    if king_suit >= N_SUITS {
                        return PileVec::default();
                    }

                    king_suit += 1;
                    Card::new(KING_RANK, king_suit - 1)
                }
            };

            let mut cards = PileVec::new();
            loop {
                // push start card
                cards.push(start_card);

                if start_card.rank() == 0 {
                    break;
                }

                let has_both = start_card.swap_suit().mask() & self.visible_mask != 0;
                let next_card = start_card.reduce_rank_swap_color();

                start_card = if !has_both && non_top & next_card.mask() == 0 {
                    // not a possible cards => switch suit
                    next_card.swap_suit()
                } else {
                    next_card
                };

                if non_top & start_card.mask() == 0 {
                    // if it's not good then break
                    break;
                }
            }
            cards
        })
    }

    #[must_use]
    pub(crate) fn is_valid(&self) -> bool {
        // TODO: test for if visible mask and free mask make sense to build bottom mask
        if self.hidden.compute_locked_mask() != self.locked_mask
            || self.get_extended_top_mask().count_ones() > N_PILES.into()
        {
            return false;
        }

        if !self.hidden.is_valid() && self.final_stack.is_valid() {
            return false;
        }

        #[allow(clippy::cast_possible_truncation)]
        let total_cards = self.visible_mask.count_ones() as u8
            + self.final_stack.len()
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
            && self.get_extended_top_mask() == other.get_extended_top_mask()
            && self.visible_mask == other.visible_mask
            && self.hidden.normalize() == other.hidden.normalize()
    }
}

impl From<&StandardSolitaire> for Solitaire {
    fn from(game: &StandardSolitaire) -> Self {
        let mut visible_mask: u64 = 0;

        for i in 0..N_PILES as usize {
            for c in &game.get_piles()[i] {
                visible_mask |= c.mask();
            }
        }

        let hidden = Hidden::from_piles(
            game.get_hidden(),
            &core::array::from_fn(|i| game.get_piles()[i].first().copied()),
        );

        let locked_mask = hidden.compute_locked_mask();

        Self {
            hidden,
            final_stack: *game.get_stack(),
            deck: game.get_deck().clone(),
            visible_mask,
            locked_mask,
        }
    }
}

#[cfg(test)]
mod tests {
    use arrayvec::ArrayVec;
    use core::ops::ControlFlow;
    use rand::prelude::*;

    use crate::deck::{Drawable, N_DECK_CARDS};
    use crate::moves::N_MOVES_MAX;
    use crate::shuffler::default_shuffle;

    // Note this useful idiom: importing names from outer (for mod tests) scope.
    use super::*;

    #[test]
    fn test_draw_unrolling() {
        let mut rng = StdRng::seed_from_u64(14);

        let mut test = ArrayVec::<(u8, Card), { N_DECK_CARDS as usize }>::new();
        for i in 0..100 {
            let mut game = Solitaire::new(&default_shuffle(12 + i), NonZeroU8::new(3).unwrap());
            for _ in 0..100 {
                let mut stack_mask: u64 = 0;
                // fill in final stack
                for suit in 0..N_SUITS {
                    let rank = game.final_stack.get(suit);
                    stack_mask |= Card::new(rank, suit).mask();
                }
                assert_eq!(stack_mask, game.final_stack.mask());

                let mut truth = game
                    .deck
                    .iter_all()
                    .filter(|x| !matches!(x.2, Drawable::None))
                    .map(|x| (x.0, x.1))
                    .collect::<ArrayVec<(u8, Card), { N_DECK_CARDS as usize }>>();

                test.clear();
                game.deck.iter_callback(false, |pos, x| {
                    test.push((pos, Card::from_mask_index(x)));
                    ControlFlow::<()>::Continue(())
                });

                test.sort_by_key(|x| x.0);
                truth.sort_by_key(|x| x.0);

                assert_eq!(test, truth);

                let moves = game.gen_moves::<false>().to_vec::<N_MOVES_MAX>();
                if moves.is_empty() {
                    break;
                }
                game.do_move(*moves.choose(&mut rng).unwrap());
            }
        }
    }

    #[test]
    fn test_undoing() {
        let mut rng = StdRng::seed_from_u64(14);

        for i in 0..1000 {
            let mut game = Solitaire::new(&default_shuffle(12 + i), NonZeroU8::new(3).unwrap());
            for _ in 0..100 {
                let moves = game.gen_moves::<false>().to_vec::<N_MOVES_MAX>();
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

                let ids: ArrayVec<(u8, Card, Drawable), { N_DECK_CARDS as usize }> =
                    game.deck.iter_all().map(|x| (x.0, x.1, x.2)).collect();

                let m = *moves.choose(&mut rng).unwrap();
                let undo = game.do_move(m);
                let next_state = game.encode();
                assert_ne!(next_state, state);
                game.undo_move(m, undo);
                let new_ids: ArrayVec<(u8, Card, Drawable), { N_DECK_CARDS as usize }> =
                    game.deck.iter_all().map(|x| (x.0, x.1, x.2)).collect();

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
            let mut game = Solitaire::new(&default_shuffle(12 + i), NonZeroU8::new(3).unwrap());
            let mut history = ArrayVec::<(Move, UndoInfo), N_STEP>::new();
            let mut enc = ArrayVec::<Encode, N_STEP>::new();
            let mut states = ArrayVec::<Solitaire, N_STEP>::new();

            assert!(game.is_valid());
            for _ in 0..N_STEP {
                let moves = game.gen_moves::<false>().to_vec::<N_MOVES_MAX>();
                if moves.is_empty() {
                    break;
                }

                assert!(game.is_valid());
                enc.push(game.encode());
                states.push(game.clone());

                let m = *moves.choose(&mut rng).unwrap();
                let undo = game.do_move(m);
                history.push((m, undo));
            }

            let new_enc = enc.clone();

            for _ in 0..history.len() {
                let (m, undo) = history.pop().unwrap();
                game.undo_move(m, undo);
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
            let mut game = Solitaire::new(&default_shuffle(12 + i), NonZeroU8::new(3).unwrap());
            for _ in 0..100 {
                let moves = game.gen_moves::<false>().to_vec::<N_MOVES_MAX>();
                if moves.is_empty() {
                    break;
                }

                game.do_move(*moves.choose(&mut rng).unwrap());

                game.hidden.shuffle(&mut rng);
                assert!(game.is_valid());
                game.hidden.clear();
                assert!(game.is_valid());
            }
        }
    }
}
