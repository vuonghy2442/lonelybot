use crate::card::{Card, N_CARDS, N_SUITS};
use crate::deck::N_PILES;
use rand::prelude::*;

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

pub fn shuffled_deck(seed: u64) -> CardDeck {
    let mut rng = StdRng::seed_from_u64(seed);
    let mut cards: [Card; N_CARDS as usize] =
        core::array::from_fn(|i| Card::new(i as u8 / N_SUITS, i as u8 % N_SUITS));
    cards.shuffle(&mut rng);
    cards
}

pub fn shuffled_deck_legacy(seed: u64) -> CardDeck {
    to_legacy(&shuffled_deck(seed))
}
