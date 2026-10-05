//! Issue #15 regression witnesses (github.com/vuonghy2442/lonelybot#15).
//!
//! Two independent defects produced wrong `Unsolvable` verdicts on winnable
//! standard Klondike (draw three) positions:
//!
//! 1. `gen_moves::<true>`'s least-stack cascade (C7) withheld worry-backs
//!    while a card waited for the foundation — the `(least_stack - 1)`
//!    mask-order filter (src/state.rs). Deal D is the whole-deal witness:
//!    even a pruner-free search exhausted the crippled move graph and
//!    concluded `Unsolvable`. The fix removes that one term; the γ probe
//!    (widening the window to the least card's rank) was measured and does
//!    NOT fix D — D's scaffold worry-backs (`SP K♥`, `SP Q♣`) sit at ranks
//!    above the least pending card.
//! 2. `FullPruner`'s path-dependent rules (reveal-context, last-draw
//!    streak) wrongly refuted X/Y-class positions. The safe default
//!    (`solver::solve`) now runs the cycle filter only; `solve_risky`
//!    keeps the aggressive rules for speed and accepts their risk.
//!
//! These tests pin the witnesses: the winnable deal/positions must solve
//! under the default, the genuinely unwinnable successor (Y after `R Q♦`,
//! confirmed by Solvitaire) must stay `Unsolvable`, and the dominance
//! generator must keep the worry-back (Z's `SP J♣`) that D's scaffold
//! was killed by.

use std::num::NonZeroU8;

use lonelybot::card::Card;
use lonelybot::engine::SolitaireEngine;
use lonelybot::moves::Move;
use lonelybot::pruning::NoPruner;
use lonelybot::shuffler::CardDeck;
use lonelybot::solver::{solve, solve_risky, SearchResult};
use lonelybot::state::Solitaire;

const DEAL_X: &str = "10♣ 9♦ 8♣ 8♥ 9♥ Q♣ 9♣ K♣ J♣ 10♥ K♠ K♦ J♥ 10♦ Q♥ J♠ 8♠ 9♠ Q♠ Q♦ 8♦ 7♥ 7♦ 7♣ 7♠ 6♠ 6♣ 6♦ A♥ A♦ A♣ A♠ 2♥ 2♦ 2♣ 2♠ 3♥ 3♦ 3♣ 3♠ 4♥ 4♦ 4♣ 4♠ 5♥ 5♦ 5♣ 5♠ 6♥ 10♠ K♥ J♦";
const TO_X: &str = "DS A♣,DS A♦,DS A♥,DS 2♦,DS 2♥,DS A♠,DS 3♥,DS 2♠,DS 2♣,DS 3♠,DS 3♣,DS 3♦,DS 4♣,DS 4♦,DS 4♥,DS 5♦,DS 5♥,DS 4♠,DS 6♥,DS 5♠,DS 5♣,PS 6♦,PS 6♣,PS 6♠,PS 7♠,PS 7♣,PS 7♦,PS 7♥,PS 8♦,PS 8♣,PS 9♦,DP J♦,DP K♥,R Q♣,R 9♥,PS 8♥,PS 9♥,PS 10♥,R J♣,R K♣";
const TO_Y: &str = "PS 9♣,PS 10♣,PS J♣";
const TO_M: &str = "R Q♥,PS 10♦,PS J♥,PS Q♥,PS K♥,R Q♦,PS Q♣,R Q♠,R K♦,SP K♥";
const TO_Z: &str = "R Q♥,PS 10♦,PS J♥,PS Q♥,PS K♥,R Q♦,PS Q♣,R Q♠,R K♦,SP K♥,SP Q♣";
const DEAL_D: &str = "9♣ 9♦ 8♣ 9♥ 8♥ Q♣ K♣ 10♣ J♣ 10♥ K♠ K♦ J♥ 10♦ Q♥ J♠ 10♠ 8♠ 9♠ Q♠ Q♦ 7♥ 7♦ 7♣ 7♠ 6♠ 6♣ 6♦ K♥ J♦ 5♣ 8♦ 6♥ 5♠ 5♥ 5♦ A♥ A♦ A♣ A♠ 2♥ 2♦ 2♣ 2♠ 3♥ 3♦ 3♣ 3♠ 4♥ 4♦ 4♣ 4♠";

fn parse_card(t: &str) -> Card {
    let suits = ["♥", "♦", "♣", "♠"] as [&str; 4];
    let s = suits.iter().position(|x| t.ends_with(x)).unwrap();
    let r = &t[..t.len() - suits[s].len()];
    let ranks = ["A", "2", "3", "4", "5", "6", "7", "8", "9", "10", "J", "Q", "K"];
    Card::new(ranks.iter().position(|x| *x == r).unwrap() as u8, s as u8)
}

fn deck(deal: &str) -> CardDeck {
    deal.split(' ').map(parse_card).collect::<Vec<_>>().try_into().unwrap()
}

fn engine(deal: &str) -> SolitaireEngine<NoPruner> {
    Solitaire::new(&deck(deal), NonZeroU8::new(3).unwrap()).into()
}

fn play(e: &mut SolitaireEngine<NoPruner>, m: &str) {
    let mv = *e
        .list_moves()
        .iter()
        .find(|x| x.to_string() == m)
        .unwrap_or_else(|| panic!("{m} not legal"));
    assert!(e.do_move(mv), "do_move failed for {m}");
}

fn replay(deal: &str, moves: &str) -> Solitaire {
    let mut e = engine(deal);
    for m in moves.split(',') {
        play(&mut e, m);
    }
    e.state().clone()
}

fn assert_solves(game: &Solitaire) {
    let (res, hist) = solve(&mut game.clone());
    assert_eq!(res, SearchResult::Solved, "default solver must solve the witness");
    let hist = hist.expect("Solved must return a winning line");
    let mut e: SolitaireEngine<NoPruner> = game.clone().into();
    for m in hist.iter() {
        assert!(e.do_move(*m), "winning line move {m} must be legal");
    }
    assert!(e.state().is_win(), "returned history must win when replayed");
}

#[test]
fn deal_d_solves_under_the_default() {
    assert_solves(&Solitaire::new(&deck(DEAL_D), NonZeroU8::new(3).unwrap()));
}

#[test]
fn deal_d_also_solves_under_risky() {
    let mut d = Solitaire::new(&deck(DEAL_D), NonZeroU8::new(3).unwrap());
    let (res, _) = solve_risky(&mut d);
    assert_eq!(res, SearchResult::Solved);
}

#[test]
fn position_x_solves() {
    assert_solves(&replay(DEAL_X, TO_X));
}

#[test]
fn position_y_solves() {
    assert_solves(&replay(DEAL_X, &format!("{TO_X},{TO_Y}")));
}

#[test]
fn midpoint_m_solves() {
    assert_solves(&replay(DEAL_X, &format!("{TO_X},{TO_Y},{TO_M}")));
}

#[test]
fn position_z_solves() {
    assert_solves(&replay(DEAL_X, &format!("{TO_X},{TO_Y},{TO_Z}")));
}

#[test]
fn y_after_r_qd_stays_unsolvable() {
    let mut e = engine(DEAL_X);
    for m in TO_X.split(',').chain(TO_Y.split(',')) {
        play(&mut e, m);
    }
    play(&mut e, "R Q♦");
    let (res, _) = solve(&mut e.state().clone());
    assert_eq!(
        res,
        SearchResult::Unsolvable,
        "the one unwinnable successor must not become solvable (Solvitaire agrees)"
    );
}

#[test]
fn z_dominance_generator_offers_the_worry_back() {
    let mut e = engine(DEAL_X);
    for m in TO_X.split(',').chain(TO_Y.split(',')).chain(TO_Z.split(',')) {
        play(&mut e, m);
    }
    let jc = parse_card("J♣");
    assert!(
        e.list_moves_dom()
            .iter()
            .any(|m| matches!(m, Move::StackPile(c) if *c == jc)),
        "the least-branch fix must keep SP J♣ visible to the dominance search"
    );
}
