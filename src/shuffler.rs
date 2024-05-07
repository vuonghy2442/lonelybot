use crate::card::{Card, N_CARDS, N_RANKS, N_SUITS};
use crate::deck::{N_HIDDEN_CARDS, N_PILES};
use rand::prelude::*;
use rand_mt::Mt;
use uint::construct_uint;
construct_uint! {
    pub struct U256(4);
}

pub type CardDeck = [Card; N_CARDS as usize];

#[must_use]
pub fn to_legacy(cards: &CardDeck) -> CardDeck {
    const OLD_HIDDEN: u8 = N_PILES * (N_PILES - 1) / 2;
    let mut new_deck = *cards;

    for i in 0..N_PILES {
        for j in 0..i {
            new_deck[(i * (i + 1) / 2 + j) as usize] = cards[(i * (i - 1) / 2 + j) as usize];
        }
        new_deck[(i * (i + 1) / 2 + i) as usize] = cards[(OLD_HIDDEN + i) as usize];
    }
    new_deck
}

#[must_use]
pub fn default_shuffle(seed: u64) -> CardDeck {
    let mut rng = StdRng::seed_from_u64(seed);
    let mut cards: CardDeck =
        core::array::from_fn(|i| Card::new(i as u8 / N_SUITS, i as u8 % N_SUITS));
    cards.shuffle(&mut rng);
    cards
}

#[must_use]
pub fn legacy_shuffle(seed: u64) -> CardDeck {
    to_legacy(&default_shuffle(seed))
}

#[must_use]
pub fn ks_shuffle(seed: u32) -> CardDeck {
    const M: [u8; N_SUITS as usize] = [2, 1, 3, 0];
    let mut rng = KSRandom::new(seed);
    let mut cards: CardDeck =
        core::array::from_fn(|i| Card::new(i as u8 % N_RANKS, M[i / N_RANKS as usize]));

    for _ in 0..269 {
        let k = rng.next_u32() % u32::from(N_CARDS);
        let j = rng.next_u32() % u32::from(N_CARDS);
        cards.swap(k as usize, j as usize);
    }

    // convert to standard form

    let mut new_cards: CardDeck = cards;

    let mut pos_from: usize = 0;
    for i in 0..N_PILES {
        for j in i..N_PILES {
            let pos_to = j * (j + 1) / 2 + i;
            new_cards[pos_to as usize] = cards[pos_from];
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
    #[must_use]
    pub fn new(seed: u32) -> Self {
        let mut rng = Self {
            value: seed,
            mix: 51_651_237,
            twist: 895_213_268,
        };

        for _ in 0..50 {
            rng.next_u32();
        }

        rng.value = 0x9417_b3af ^ seed ^ (((seed as i32) >> 15) as u32);

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

        self.value & 0x7fff_ffff
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
        self.seed = ((u64::from(self.seed) * 16807) % 0x7fff_ffff) as u32;
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
    #[must_use]
    pub const fn new(seed: u32) -> Self {
        Self { seed }
    }
}

#[must_use]
pub fn greenfelt_shuffle(seed: u32) -> CardDeck {
    const M: [u8; N_SUITS as usize] = [2, 1, 3, 0];

    let mut rng = GreenRandom::new(seed);
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
            let k = rng.next_u32() % u32::from(N_CARDS);
            cards.swap(j as usize, k as usize);
        }
    }

    let cards = {
        let mut new_cards = cards;
        new_cards[28..28 + 24].copy_from_slice(&cards[0..24]);
        new_cards[0..28].copy_from_slice(&cards[24..24 + 28]);
        new_cards[0..N_HIDDEN_CARDS as usize].reverse();
        new_cards[N_HIDDEN_CARDS as usize..].reverse();
        new_cards
    };
    // convert to standard form

    let mut new_cards: CardDeck = cards;

    let mut pos_from = 0usize;
    for i in 0..N_PILES {
        for j in i..N_PILES {
            let pos_to = (j * (j + 1) / 2 + i) as usize;
            new_cards[pos_to] = cards[pos_from];
            pos_from += 1;
        }
    }

    new_cards
}

pub fn uniform_int<R: RngCore>(a: u32, b: u32, rng: &mut R) -> u32 {
    const B_RANGE: u32 = u32::MAX;

    let range = b - a;
    let bucket_size = B_RANGE / (range + 1) + u32::from(B_RANGE % (range + 1) == range);
    loop {
        let val = rng.next_u32() / bucket_size;
        if val <= range {
            return val + a;
        }
    }
}

#[must_use]
pub fn solvitaire_shuffle(seed: u32) -> CardDeck {
    const M: [u8; N_SUITS as usize] = [2, 0, 3, 1];
    let mut cards: CardDeck =
        core::array::from_fn(|i| Card::new(i as u8 / N_SUITS, M[i % N_SUITS as usize]));

    let mut rng: Mt = Mt::new(seed);

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

#[must_use]
fn factorial(n: u8) -> U256 {
    match n {
        0 | 1 => U256::one(),
        _ => factorial(n - 1) * n,
    }
}

#[must_use]
pub fn exact_shuffle(mut seed: U256) -> Option<CardDeck> {
    if seed >= factorial(N_CARDS) {
        return None;
    }
    let mut cards: CardDeck =
        core::array::from_fn(|i| Card::new(i as u8 / N_SUITS, i as u8 % N_SUITS));

    for i in 1..N_CARDS as usize {
        let j = (seed % U256::from(i + 1)).as_usize();
        seed /= (i + 1) as u128;
        cards.swap(i, j);
    }

    Some(cards)
}

#[must_use]
pub fn encode_shuffle(mut cards: CardDeck) -> U256 {
    let mut encode = U256::zero();
    for i in (1..N_CARDS as usize).rev() {
        let card = Card::new(i as u8 / N_SUITS, i as u8 % N_SUITS);
        let pos = cards[..=i].iter().position(|c| c == &card).unwrap();
        encode = encode * (i + 1) + pos;
        cards.swap(pos, i);
    }
    encode
}

#[cfg(test)]
mod tests {
    use rand::prelude::*;

    use super::*;

    #[test]
    fn test_encode() {
        let mut rng = StdRng::seed_from_u64(14);

        for _ in 0..1000 {
            let encode: u128 = rng.gen();
            let deck = exact_shuffle(encode.into()).unwrap();
            assert_eq!(encode, encode_shuffle(deck).as_u128());
        }
    }

    #[test]
    fn test_encode2() {
        let mut rng = StdRng::seed_from_u64(14);

        // for _ in 0..1000 {
        let seed: u64 = rng.gen();
        let deck = default_shuffle(seed);
        let encode = encode_shuffle(deck.clone());
        let deck_2 = exact_shuffle(encode).unwrap();

        let encode2 = encode_shuffle(deck_2.clone());
        assert_eq!(encode, encode2);
        assert_eq!(deck, deck_2);
        // }
    }

    #[test]
    fn test_exact() {
        assert_eq!(
            encode_shuffle(default_shuffle(0)),
            U256::from_dec_str(
                "58951431144029615328972203965306300108857513542935373524517649274867"
            )
            .unwrap()
        );

        assert_eq!(
            encode_shuffle(legacy_shuffle(0)),
            U256::from_dec_str(
                "58984888198769686684640833699869084205119854744931998784527271197475"
            )
            .unwrap()
        );

        assert_eq!(
            encode_shuffle(solvitaire_shuffle(0)),
            U256::from_dec_str(
                "12954810653509400169295621394006691876957783508183809583464865425989"
            )
            .unwrap()
        );

        assert_eq!(
            encode_shuffle(ks_shuffle(0)),
            U256::from_dec_str(
                "35511235380175238168226668580770214465574563740067205469369780560069"
            )
            .unwrap()
        );

        assert_eq!(
            encode_shuffle(greenfelt_shuffle(0)),
            U256::from_dec_str(
                "54175677138559480155411779209903877761694750384126798297802324102022"
            )
            .unwrap()
        );
    }
}
