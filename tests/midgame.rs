use std::num::NonZeroU8;

use arrayvec::ArrayVec;
use lonelybot::solvitaire::Solvitaire;
use lonelybot::{
    card::Card,
    deck::{Deck, N_PILES},
    solver::{solve, SearchResult},
    standard::{StandardSolitaire, N_HIDDEN_MAX, N_OPEN_MAX},
    state::Solitaire,
};
use serde_json::{json, Value};

#[test]
fn test_from_custom_piles_initialization() {
    let mut hidden_piles: [ArrayVec<Card, N_HIDDEN_MAX>; N_PILES as usize] = Default::default();
    hidden_piles[6].push(Card::new(12, 3));
    let mut open_piles: [ArrayVec<Card, N_OPEN_MAX>; N_PILES as usize] = Default::default();
    open_piles[6].push(Card::new(11, 3));
    let deck = Deck::from_midgame(
        &[Card::new(12, 2), Card::new(11, 2)],
        0,
        NonZeroU8::new(1).unwrap(),
        &[
            Card::new(12, 2),
            Card::new(11, 2),
            Card::new(10, 2),
            Card::new(9, 2),
            Card::new(8, 2),
            Card::new(7, 2),
            Card::new(6, 2),
            Card::new(5, 2),
            Card::new(4, 2),
            Card::new(3, 2),
            Card::new(2, 2),
            Card::new(1, 2),
            Card::new(0, 2),
            Card::new(12, 1),
            Card::new(11, 1),
            Card::new(10, 1),
            Card::new(9, 1),
            Card::new(8, 1),
            Card::new(7, 1),
            Card::new(6, 1),
            Card::new(5, 1),
            Card::new(4, 1),
            Card::new(3, 1),
            Card::new(2, 1),
        ],
    );
    let stack = [13, 13, 11, 11];
    let game = StandardSolitaire::from_midgame(hidden_piles, open_piles, stack, deck, true);
    let mut solitaire = Solitaire::from(&game);
    let solvitaire = Solvitaire(game);
    let obj: Value = serde_json::from_str(solvitaire.to_string().as_str()).unwrap();
    assert_eq!(
        obj,
        json!({
            "tableau piles": [[], [], [], [],[], [], ["Ks", "QS"]],
            "stock": ["QC", "KC"], "waste": [],
            "foundation": [["AH","2H","3H","4H","5H","6H","7H","8H","9H","10H","JH","QH", "KH"],["AD","2D","3D","4D","5D","6D","7D","8D","9D","10D","JD","QD", "KD"],["AC","2C","3C","4C","5C","6C","7C","8C","9C","10C", "JC"],["AS","2S","3S","4S","5S","6S","7S","8S","9S","10S", "JS"]]
        })
    );
    let (result, _) = solve(&mut solitaire);
    assert_eq!(result, SearchResult::Solved);
}
