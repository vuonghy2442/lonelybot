use crate::card::{Card, N_CARDS, N_RANKS, N_SUITS};
use crate::deck::{N_PILES, N_PILE_CARDS};
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

    #[allow(clippy::cast_possible_truncation)]
    let mut cards: CardDeck =
        core::array::from_fn(|i| Card::new(i as u8 / N_SUITS, i as u8 % N_SUITS));
    cards.shuffle(&mut rng);
    cards
}

#[must_use]
pub fn legacy_shuffle(seed: u64) -> CardDeck {
    to_legacy(&default_shuffle(seed))
}

fn layer_to_pile(cards: &CardDeck) -> CardDeck {
    let mut new_cards: CardDeck = *cards;

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

#[must_use]
pub fn ks_shuffle(seed: u32) -> CardDeck {
    const M: [u8; N_SUITS as usize] = [2, 1, 3, 0];
    let mut rng = KSRandom::new(seed);

    #[allow(clippy::cast_possible_truncation)]
    let mut cards: CardDeck =
        core::array::from_fn(|i| Card::new(i as u8 % N_RANKS, M[i / N_RANKS as usize]));

    for _ in 0..269 {
        let k = rng.next_u32() % u32::from(N_CARDS);
        let j = rng.next_u32() % u32::from(N_CARDS);
        cards.swap(k as usize, j as usize);
    }

    // convert to standard form
    layer_to_pile(&cards)
}

pub struct KSRandom {
    value: u32,
    mix: u32,
    twist: u32,
}

const fn to_signed(x: u32) -> i32 {
    0_i32.wrapping_add_unsigned(x)
}
const fn to_unsigned(x: i32) -> u32 {
    0_u32.wrapping_add_signed(x)
}

const fn signed_shr(x: u32, shr: u32) -> u32 {
    to_unsigned(to_signed(x) >> shr)
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

        rng.value = 0x9417_b3af ^ seed ^ signed_shr(seed, 15);

        for _ in 0..950 {
            rng.next_u32();
        }

        rng
    }
}

impl KSRandom {
    fn next_u32(&mut self) -> u32 {
        let mut y = self.value ^ (self.twist.wrapping_sub(self.mix)) ^ self.value;
        y ^= self.twist ^ self.value ^ self.mix;
        self.mix ^= self.twist ^ self.value;
        self.value ^= self.twist.wrapping_sub(self.mix);
        self.twist ^= self.value ^ y;
        self.value ^= (self.twist << 7) ^ signed_shr(self.mix, 16) ^ (y << 8);

        self.value & 0x7fff_ffff
    }
}

pub struct GreenRandom {
    seed: u32,
}

impl GreenRandom {
    fn next_u32(&mut self) -> u32 {
        self.seed = ((u64::from(self.seed) * 16807) % 0x7fff_ffff) as u32;
        self.seed
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
    let mut cards: CardDeck = [Card::DEFAULT; N_CARDS as usize];

    for i in 0..26u8 {
        cards[i as usize] = Card::new(i % N_RANKS, M[(i / N_RANKS) as usize]);
    }
    for i in 0..13u8 {
        let j = i + 39;
        cards[i as usize + 26] = Card::new(j % N_RANKS, M[(j / N_RANKS) as usize]);
    }
    for i in 0..13u8 {
        let j = i + 26;
        cards[i as usize + 39] = Card::new(j % N_RANKS, M[(j / N_RANKS) as usize]);
    }

    for _ in 0..7 {
        for j in 0..N_CARDS {
            let k = rng.next_u32() % u32::from(N_CARDS);
            cards.swap(j as usize, k as usize);
        }
    }

    cards.reverse();
    // convert to standard form

    layer_to_pile(&cards)
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

    #[allow(clippy::cast_possible_truncation)]
    let mut cards: CardDeck =
        core::array::from_fn(|i| Card::new(i as u8 / N_SUITS, M[i % N_SUITS as usize]));

    let mut rng: Mt = Mt::new(seed);

    for i in (1..N_CARDS).rev() {
        let val = uniform_int(0, i.into(), &mut rng);
        cards.swap(i as usize, val as usize);
    }

    //stock is in the back :))
    let mut new_cards: CardDeck = cards;

    let mut pos_from = 0;
    for i in 0..N_PILES {
        for j in (i..N_PILES).rev() {
            let pos_to = j * (j + 1) / 2 + i;
            new_cards[pos_to as usize] = cards[(N_PILE_CARDS - 1 - pos_from) as usize];
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

    #[allow(clippy::cast_possible_truncation)]
    let mut cards: CardDeck =
        core::array::from_fn(|i| Card::new(i as u8 / N_SUITS, i as u8 % N_SUITS));

    for i in 1..N_CARDS as usize {
        let j = (seed % (i + 1)).as_usize();
        seed /= i + 1;
        cards.swap(i, j);
    }

    Some(cards)
}

/// Return None when the `cards` is not a valid `CardDeck` (not a permutation of the valid cards)
#[must_use]
pub fn encode_shuffle(mut cards: CardDeck) -> Option<U256> {
    let mut encode = U256::zero();
    for i in (1..N_CARDS).rev() {
        let card = Card::new(i / N_SUITS, i % N_SUITS);
        let pos = cards[..=i as usize].iter().position(|c| c == &card)?;
        encode = encode * (i + 1) + pos;
        cards.swap(pos, i as usize);
    }
    Some(encode)
}

#[must_use]
pub fn microsoft_shuffle(mut seed: U256) -> Option<CardDeck> {
    const M: [u8; N_SUITS as usize] = [3, 0, 2, 1];
    if seed >= factorial(N_CARDS) {
        return None;
    }

    #[allow(clippy::cast_possible_truncation)]
    let mut cards: CardDeck =
        core::array::from_fn(|i| Card::new(i as u8 % N_RANKS, M[i / N_RANKS as usize]));

    for i in (1..N_CARDS as usize).rev() {
        let j = (seed % (i + 1)).as_usize();
        seed /= i + 1;
        cards.swap(i, j);
    }

    cards.reverse();
    // convert to standard form

    Some(layer_to_pile(&cards))
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
            assert_eq!(encode, encode_shuffle(deck).unwrap().as_u128());
        }
    }

    #[test]
    fn test_encode2() {
        let mut rng = StdRng::seed_from_u64(14);

        // for _ in 0..1000 {
        let seed: u64 = rng.gen();
        let deck = default_shuffle(seed);
        let encode = encode_shuffle(deck.clone()).unwrap();
        let deck_2 = exact_shuffle(encode).unwrap();

        let encode2 = encode_shuffle(deck_2.clone()).unwrap();
        assert_eq!(encode, encode2);
        assert_eq!(deck, deck_2);
        // }
    }

    #[test]
    fn test_exact() {
        assert_eq!(
            encode_shuffle(default_shuffle(0)).unwrap(),
            U256::from_dec_str(
                "58951431144029615328972203965306300108857513542935373524517649274867"
            )
            .unwrap()
        );

        assert_eq!(
            encode_shuffle(legacy_shuffle(0)).unwrap(),
            U256::from_dec_str(
                "58984888198769686684640833699869084205119854744931998784527271197475"
            )
            .unwrap()
        );

        assert_eq!(
            encode_shuffle(solvitaire_shuffle(0)).unwrap(),
            U256::from_dec_str(
                "12954810653509400169295621394006691876957783508183809583464865425989"
            )
            .unwrap()
        );

        assert_eq!(
            encode_shuffle(ks_shuffle(0)).unwrap(),
            U256::from_dec_str(
                "35511235380175238168226668580770214465574563740067205469369780560069"
            )
            .unwrap()
        );

        assert_eq!(
            encode_shuffle(greenfelt_shuffle(0)).unwrap(),
            U256::from_dec_str(
                "70781775317263119030027683441491840945148374294523658484644048341783"
            )
            .unwrap()
        );

        assert_eq!(
            encode_shuffle(
                microsoft_shuffle(
                    U256::from_dec_str(
                        "37529377358585594134454298882350599254635682470701937210952436445911"
                    )
                    .unwrap()
                )
                .unwrap()
            )
            .unwrap(),
            U256::from_dec_str(
                "6555618124709432518914756628087920429793617258659043425228908599455"
            )
            .unwrap()
        );
    }
}
