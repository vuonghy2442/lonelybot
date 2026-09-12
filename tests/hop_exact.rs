use lonelybot::engine::SolitaireEngine;
use lonelybot::hop_solver::hop_solve_game;
use lonelybot::moves::Move;
use lonelybot::mcts_solver::pick_moves;
use lonelybot::pruning::FullPruner;
use lonelybot::shuffler::default_shuffle;
use lonelybot::state::Solitaire;
use lonelybot::tracking::DefaultTerminateSignal;
use rand::{rngs::SmallRng, seq::IndexedRandom, SeedableRng};
use std::num::NonZeroU8;

fn fact(n: usize) -> usize {
    (1..=n).product()
}

fn ucb1(r: &lonelybot::hop_solver::HopResult, n_total: usize) -> f64 {
    if r.played == 0 {
        f64::INFINITY
    } else {
        r.rate() + 2.0 * ((n_total as f64).ln() / r.played as f64).sqrt()
    }
}

#[test]
fn exact_branch_enumerates_all_arrangements() {
    let mut rng = SmallRng::seed_from_u64(7);

    for seed in 0..30u64 {
        // walk a game randomly until the buried-card count is small
        let mut game: SolitaireEngine<FullPruner> =
            Solitaire::new(&default_shuffle(seed), NonZeroU8::new(3).unwrap()).into();

        for _ in 0..200 {
            if game.state().is_win() {
                break;
            }
            let buried = game.state().get_hidden().total_down_cards() as usize;
            let mut moves = game.list_moves_dom();
            if moves.is_empty() {
                break;
            }

            if buried > 0 && buried <= 5 {
                // find an irreversible candidate (deck draws always commit)
                let mut gg = game.state().clone();
                gg.hidden_clear();
                if let Some(&m) = moves
                    .iter()
                    .find(|m| matches!(m, Move::DeckPile(_) | Move::DeckStack(_)))
                {
                    let res = hop_solve_game(
                        &gg,
                        m,
                        &mut rng,
                        3,
                        50,
                        10_000,
                        &DefaultTerminateSignal {},
                        &FullPruner::default(),
                    );
                    assert!(res.exhaustive, "seed {seed}: expected exhaustive result");
                    assert_eq!(
                        res.played,
                        fact(buried),
                        "seed {seed}: expected {buried}! arrangements evaluated"
                    );
                }
            }

            game.do_move(*moves.choose(&mut rng).unwrap());
        }
    }
}

/// The exact evaluation must not depend on which arrangement the state
/// currently holds: every arrangement is enumerated with equal weight, so
/// two states that differ only in their buried-card arrangement must
/// evaluate a candidate move identically. If not, the evaluation would be
/// leaking the real arrangement.
#[test]
fn evaluation_is_arrangement_symmetric() {
    let mut rng = SmallRng::seed_from_u64(11);

    for seed in 0..40u64 {
        let mut game: SolitaireEngine<FullPruner> =
            Solitaire::new(&default_shuffle(seed), NonZeroU8::new(3).unwrap()).into();

        for _ in 0..200 {
            if game.state().is_win() {
                break;
            }
            let buried = game.state().get_hidden().total_down_cards() as usize;
            let mut moves = game.list_moves_dom();
            if moves.is_empty() {
                break;
            }

            if (2..=5).contains(&buried) {
                let Some(&m) = moves
                    .iter()
                    .find(|m| matches!(m, Move::DeckPile(_) | Move::DeckStack(_)))
                else {
                    game.do_move(*moves.choose(&mut rng).unwrap());
                    continue;
                };

                // same structure, two different buried arrangements
                let s1 = game.state().clone();
                let mut s2 = game.state().clone();
                let mut cards = s2.get_hidden().buried_cards();
                cards.reverse();
                s2.apply_buried(&cards);

                let r1 = hop_solve_game(
                    &s1,
                    m,
                    &mut SmallRng::seed_from_u64(1),
                    3,
                    50,
                    10_000,
                    &DefaultTerminateSignal {},
                    &FullPruner::default(),
                );
                let r2 = hop_solve_game(
                    &s2,
                    m,
                    &mut SmallRng::seed_from_u64(2),
                    3,
                    50,
                    10_000,
                    &DefaultTerminateSignal {},
                    &FullPruner::default(),
                );
                assert_eq!(
                    r1, r2,
                    "seed {seed}: evaluation depends on the real arrangement"
                );
            }

            game.do_move(*moves.choose(&mut rng).unwrap());
        }
    }
}

/// Planning must not see the real hidden arrangement: after
/// `hidden_clear`, two states that differed only in their buried
/// arrangement become identical, so the planner must return identical plans.
#[test]
fn planning_is_arrangement_blind() {
    let mut rng = SmallRng::seed_from_u64(13);

    for seed in 0..20u64 {
        let mut game: SolitaireEngine<FullPruner> =
            Solitaire::new(&default_shuffle(seed), NonZeroU8::new(3).unwrap()).into();

        for _ in 0..100 {
            if game.state().is_win() {
                break;
            }
            let mut moves = game.list_moves_dom();
            if moves.is_empty() {
                break;
            }

            // two copies with different buried arrangements, then both cleared
            let mut g1 = game.state().clone();
            let mut g2 = game.state().clone();
            g2.hidden_shuffle(&mut rng);

            // the arrangement differs but the encoded structure stays equal
            let c1 = g1.get_hidden().buried_cards();
            let c2 = g2.get_hidden().buried_cards();
            if c1 == c2 {
                // the shuffle happened to keep this arrangement (or nothing
                // is buried): nothing to check here
                game.do_move(*moves.choose(&mut rng).unwrap());
                continue;
            }
            assert_eq!(g1.encode(), g2.encode());

            g1.hidden_clear();
            g2.hidden_clear();
            assert_eq!(g1.encode(), g2.encode());

            let p1 = pick_moves(
                &mut g1,
                &mut SmallRng::seed_from_u64(77),
                30,
                50,
                &DefaultTerminateSignal {},
                ucb1,
            );
            let p2 = pick_moves(
                &mut g2,
                &mut SmallRng::seed_from_u64(77),
                30,
                50,
                &DefaultTerminateSignal {},
                ucb1,
            );
            assert_eq!(
                p1, p2,
                "seed {seed}: plan differs depending on the real arrangement"
            );

            game.do_move(*moves.choose(&mut rng).unwrap());
        }
    }
}
