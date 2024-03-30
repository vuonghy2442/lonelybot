use rand::seq::SliceRandom;
use rand::RngCore;

use arrayvec::ArrayVec;

use crate::card::{card_mask, from_mask, Card, KING_RANK, N_CARDS};
use crate::deck::{N_HIDDEN_CARDS, N_PILES};

use crate::standard::HiddenVec;

#[derive(Debug, Clone)]
pub struct Hidden {
    hidden_piles: [Card; N_HIDDEN_CARDS as usize],
    n_hidden: [u8; N_PILES as usize],
    pile_map: [u8; N_CARDS as usize],
}

impl Hidden {
    #[must_use]
    pub fn new(hidden_piles: [Card; N_HIDDEN_CARDS as usize]) -> Self {
        let mut pile_map = [0; N_CARDS as usize];

        for i in 0..N_PILES {
            let start = i * (i + 1) / 2;
            let end = (i + 2) * (i + 1) / 2;

            let p = &hidden_piles[start as usize..end as usize];
            for c in p {
                pile_map[usize::from(c.value())] = i;
            }
        }

        Self {
            hidden_piles,
            n_hidden: core::array::from_fn(|i| (i + 1) as u8),
            pile_map,
        }
    }

    #[must_use]
    pub fn from_piles(
        piles: &[HiddenVec; N_PILES as usize],
        top: &[Option<Card>; N_PILES as usize],
    ) -> Self {
        let mut hidden_piles = [Card::FAKE; N_HIDDEN_CARDS as usize];
        let mut pile_map = [0u8; N_CARDS as usize];

        [0u8; N_PILES as usize];

        for i in 0..N_PILES as usize {
            for (j, c) in piles[i].iter().chain(top[i].iter()).enumerate() {
                hidden_piles[(i * (i + 1) / 2) + j] = *c;
                pile_map[c.value() as usize] = i as u8;
            }
        }

        Self {
            hidden_piles,
            pile_map,
            n_hidden: core::array::from_fn(|i| piles[i].len() as u8 + top[i].is_some() as u8),
        }
    }

    #[must_use]
    pub fn to_piles(&self) -> [HiddenVec; N_PILES as usize] {
        let mut hidden_piles: [HiddenVec; N_PILES as usize] = Default::default();

        for i in 0..N_PILES {
            let Some((_, pile_map)) = self.get(i).split_last() else {
                continue;
            };
            for c in pile_map {
                hidden_piles[i as usize].push(*c);
            }
        }
        hidden_piles
    }

    #[must_use]
    pub const fn lens(&self) -> &[u8; N_PILES as usize] {
        &self.n_hidden
    }

    const fn get_range(&self, pos: u8) -> core::ops::Range<usize> {
        let start = (pos * (pos + 1) / 2) as usize;
        let end = start + self.n_hidden[pos as usize] as usize;
        start..end
    }

    #[must_use]
    pub fn get(&self, pos: u8) -> &[Card] {
        &self.hidden_piles[self.get_range(pos)]
    }

    #[must_use]
    pub fn get_mut(&mut self, pos: u8) -> &mut [Card] {
        let range = self.get_range(pos);
        &mut self.hidden_piles[range]
    }

    #[must_use]
    pub fn peek(&self, pos: u8) -> Option<&Card> {
        self.get(pos).last()
    }

    pub fn pop(&mut self, pos: u8) -> Option<&Card> {
        self.n_hidden[usize::from(pos)] -= 1;
        self.peek(pos)
    }

    pub fn unpop(&mut self, pos: u8) {
        self.n_hidden[usize::from(pos)] += 1;
    }

    #[must_use]
    pub const fn find(&self, c: &Card) -> u8 {
        self.pile_map[c.value() as usize]
    }

    #[must_use]
    pub fn all_turn_up(&self) -> bool {
        self.lens().iter().all(|x| *x <= 1)
    }

    pub fn total_down_cards(&self) -> u8 {
        self.n_hidden
            .iter()
            .map(|x| x.saturating_sub(1))
            .sum::<u8>()
    }

    // can be made const fn
    #[must_use]
    pub fn encode(&self) -> u16 {
        self.n_hidden
            .iter()
            .enumerate()
            .rev()
            .fold(0u16, |res, cur| {
                res * (cur.0 as u16 + 2) + u16::from(*cur.1)
            })
    }

    pub fn decode(&mut self, mut hidden_encode: u16) {
        for i in 0..N_PILES {
            let n_options = u16::from(i) + 2;
            self.n_hidden[i as usize] = (hidden_encode % n_options) as u8;
            hidden_encode /= n_options;
        }
    }

    fn update_map(&mut self) {
        for pos in 0..N_PILES {
            for c in &self.hidden_piles[self.get_range(pos)] {
                self.pile_map[c.value() as usize] = pos;
            }
        }
    }

    pub fn mask(&self) -> u64 {
        let mut mask = 0;
        for pos in 0..N_PILES {
            if let Some((_, pile_map)) = self.get(pos).split_last() {
                for c in pile_map {
                    mask |= card_mask(c);
                }
            }
        }
        mask
    }

    // reset all pile_map card into lexicalgraphic order
    pub fn clear(&mut self) {
        let mut hidden_cards = self.mask();

        for pos in 0..N_PILES {
            if let Some((_, pile_map)) = self.get_mut(pos).split_last_mut() {
                for h in pile_map {
                    debug_assert_ne!(hidden_cards, 0);
                    *h = from_mask(&hidden_cards);
                    hidden_cards &= hidden_cards.wrapping_sub(1);
                }
            }
        }
        debug_assert_eq!(hidden_cards, 0);
        self.update_map();
    }

    pub fn shuffle(&mut self, rng: &mut impl RngCore) {
        let mut all_stuff = ArrayVec::<Card, { N_HIDDEN_CARDS as usize }>::new();
        for pos in 0..N_PILES {
            if let Some((_, pile_map)) = self.get(pos).split_last() {
                all_stuff.extend(pile_map.iter().copied());
            }
        }
        all_stuff.shuffle(rng);

        let mut start = 0;

        for pos in 0..N_PILES {
            if let Some((_, pile_map)) = self.get_mut(pos).split_last_mut() {
                pile_map.copy_from_slice(&all_stuff[start..start + pile_map.len()]);
                start += pile_map.len();
            }
        }
        self.update_map();
    }

    pub fn is_valid(&self) -> bool {
        for pos in 0..N_PILES {
            for c in self.get(pos) {
                if self.pile_map[c.value() as usize] != pos {
                    return false;
                }
            }
        }
        true
    }

    #[must_use]
    pub fn normalize(&self) -> [u8; N_PILES as usize] {
        core::array::from_fn(|pos| {
            if self.n_hidden[pos] > 1 {
                self.n_hidden[pos]
            } else if self.n_hidden[pos] == 1 {
                (self.get(pos as u8)[0].rank() < KING_RANK) as u8
            } else {
                0
            }
        })
    }
}
