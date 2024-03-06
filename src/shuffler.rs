use crate::card::{Card, N_CARDS, N_RANKS, N_SUITS};
use crate::deck::{N_HIDDEN_CARDS, N_PILES};
use rand::prelude::*;
use rand_mt::Mt;

pub type CardDeck = [Card; N_CARDS as usize];

pub fn to_legacy(cards: &CardDeck) -> CardDeck {
    let mut new_deck = *cards;

    const OLD_HIDDEN: u8 = N_PILES * (N_PILES - 1) / 2;

    for i in 0..N_PILES {
        for j in 0..i {
            new_deck[(i * (i + 1) / 2 + j) as usize] = cards[(i * (i - 1) / 2 + j) as usize];
        }
        new_deck[(i * (i + 1) / 2 + i) as usize] = cards[(OLD_HIDDEN + i) as usize];
    }
    new_deck
}

pub fn default_shuffle(seed: u64) -> CardDeck {
    let mut rng = StdRng::seed_from_u64(seed);
    let mut cards: CardDeck =
        core::array::from_fn(|i| Card::new(i as u8 / N_SUITS, i as u8 % N_SUITS));
    cards.shuffle(&mut rng);
    cards
}

pub fn legacy_shuffle(seed: u64) -> CardDeck {
    to_legacy(&default_shuffle(seed))
}

pub fn ks_shuffle(seed: u64) -> CardDeck {
    let mut rng = KSRandom::new(seed as u32);
    const M: [u8; N_SUITS as usize] = [2, 1, 3, 0];
    let mut cards: CardDeck =
        core::array::from_fn(|i| Card::new(i as u8 % N_RANKS, M[i / N_RANKS as usize]));

    for _ in 0..269 {
        let k = rng.next_u32() % (N_CARDS as u32);
        let j = rng.next_u32() % (N_CARDS as u32);
        cards.swap(k as usize, j as usize);
    }

    // convert to standard form

    let mut new_cards: CardDeck = cards;

    let mut pos_from = 0;
    for i in 0..N_PILES {
        for j in i..N_PILES {
            let pos_to = j * (j + 1) / 2 + i;
            new_cards[pos_to as usize] = cards[pos_from as usize];
            pos_from += 1;
        }
    }

    new_cards
}

pub struct KSRandom {
    value: u32,
    mix: u32,
    twist: u32,
}

impl KSRandom {
    pub fn new(seed: u32) -> Self {
        let mut rng = KSRandom {
            value: seed,
            mix: 51651237,
            twist: 895213268,
        };

        for _ in 0..50 {
            rng.next_u32();
        }

        rng.value = 0x9417B3AF ^ seed ^ (((seed as i32) >> 15) as u32);

        for _ in 0..950 {
            rng.next_u32();
        }

        rng
    }
}

impl RngCore for KSRandom {
    fn next_u32(&mut self) -> u32 {
        let mut y = self.value ^ (self.twist.wrapping_sub(self.mix)) ^ self.value;
        y ^= self.twist ^ self.value ^ self.mix;
        self.mix ^= self.twist ^ self.value;
        self.value ^= self.twist.wrapping_sub(self.mix);
        self.twist ^= self.value ^ y;
        self.value ^= (self.twist << 7) ^ (((self.mix as i32) >> 16) as u32) ^ (y << 8);

        self.value & 0x7fffffff
    }

    fn next_u64(&mut self) -> u64 {
        unimplemented!()
    }

    fn fill_bytes(&mut self, _dest: &mut [u8]) {
        unimplemented!()
    }

    fn try_fill_bytes(&mut self, _dest: &mut [u8]) -> Result<(), rand::Error> {
        unimplemented!()
    }
}

pub struct GreenRandom {
    seed: u32,
}

impl RngCore for GreenRandom {
    fn next_u32(&mut self) -> u32 {
        self.seed = (((self.seed as u64) * 16807) % 0x7fffffff) as u32;
        self.seed
    }

    fn next_u64(&mut self) -> u64 {
        unimplemented!()
    }

    fn fill_bytes(&mut self, _dest: &mut [u8]) {
        unimplemented!()
    }

    fn try_fill_bytes(&mut self, _dest: &mut [u8]) -> Result<(), rand::Error> {
        unimplemented!()
    }
}

impl GreenRandom {
    pub fn new(seed: u32) -> Self {
        GreenRandom { seed }
    }
}

pub fn greenfelt_shuffle(seed: u64) -> CardDeck {
    let mut rng = GreenRandom::new(seed as u32);
    const M: [u8; N_SUITS as usize] = [2, 1, 3, 0];
    let mut cards: CardDeck = [Card::FAKE; N_CARDS as usize];

    for i in 0..26 {
        cards[i] = Card::new(i as u8 % N_RANKS, M[i / N_RANKS as usize]);
    }
    for i in 0..13 {
        let j = i + 39;
        cards[i + 26] = Card::new(j as u8 % N_RANKS, M[j / N_RANKS as usize]);
    }
    for i in 0..13 {
        let j = i + 26;
        cards[i + 39] = Card::new(j as u8 % N_RANKS, M[j / N_RANKS as usize]);
    }

    for _ in 0..7 {
        for j in 0..N_CARDS {
            let k = rng.next_u32() % (N_CARDS as u32);
            cards.swap(j as usize, k as usize);
        }
    }

    let cards = {
        let mut new_cards = cards;
        new_cards[28..28 + 24].copy_from_slice(&cards[0..24]);
        new_cards[0..28].copy_from_slice(&cards[24..24 + 28]);
        new_cards[0..N_HIDDEN_CARDS as usize].reverse();
        new_cards
    };
    // convert to standard form

    let mut new_cards: CardDeck = cards;

    let mut pos_from = 0;
    for i in 0..N_PILES {
        for j in i..N_PILES {
            let pos_to = j * (j + 1) / 2 + i;
            new_cards[pos_to as usize] = cards[pos_from as usize];
            pos_from += 1;
        }
    }

    new_cards
}

pub fn uniform_int(a: u32, b: u32, rng: &mut impl RngCore) -> u32 {
    const B_RANGE: u32 = u32::MAX;

    let range = b - a;
    let bucket_size = B_RANGE / (range + 1) + (B_RANGE % (range + 1) == range) as u32;
    loop {
        let rnd = rng.next_u32() / bucket_size;
        if rnd <= range {
            return rnd + a;
        }
    }
}

pub fn solvitaire_shuffle(seed: u64) -> CardDeck {
    const M: [u8; N_SUITS as usize] = [2, 0, 3, 1];
    let mut cards: CardDeck =
        core::array::from_fn(|i| Card::new(i as u8 / N_SUITS, M[i % N_SUITS as usize]));

    let mut rng: Mt = Mt::new(seed as u32);

    for i in (1..cards.len()).rev() {
        let val = uniform_int(0, i as u32, &mut rng);
        cards.swap(i, val as usize);
    }

    //stock is in the back :))
    let mut new_cards: CardDeck = cards;

    let mut pos_from = 0;
    for i in 0..N_PILES {
        for j in (i..N_PILES).rev() {
            let pos_to = j * (j + 1) / 2 + i;
            new_cards[pos_to as usize] = cards[(N_HIDDEN_CARDS - 1 - pos_from) as usize];
            pos_from += 1;
        }
    }

    new_cards
}
