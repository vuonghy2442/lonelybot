use lonelybot::engine::SolitaireEngine;
use lonelybot::mcts_solver::pick_moves;
use lonelybot::pruning::NoPruner;
use lonelybot::shuffler::default_shuffle;
use lonelybot::state::Solitaire;
use lonelybot::tracking::DefaultTerminateSignal;
use rand::{rngs::SmallRng, SeedableRng};
use std::num::NonZeroU8;

fn ucb1(n_sucess: usize, n_visit: usize, n_total: usize) -> f64 {
    const C: f64 = 2.;

    #[allow(clippy::cast_precision_loss)]
    if n_visit == 0 {
        f64::INFINITY
    } else {
        n_sucess as f64 / n_visit as f64 + C * ((n_total as f64).ln() / n_visit as f64).sqrt()
    }
}

/// Plays a full hop game, like `lonecli hop`, but with a reduced search
/// effort and a hard turn limit.
///
/// Returns `Some(win)` when the game finished and `None` when the turn limit
/// was hit, i.e. the solver kept playing without making progress (the
/// dead-loop bug).
fn run_hop(seed: u64, draw_step: u8, n_times: usize, limit: usize, max_turns: usize) -> Option<bool> {
    let mut game: SolitaireEngine<NoPruner> =
        Solitaire::new(&default_shuffle(seed), NonZeroU8::new(draw_step).unwrap()).into();
    let mut rng = SmallRng::seed_from_u64(seed);

    for _ in 0..max_turns {
        if game.state().is_win() {
            return Some(true);
        }

        let mut gg = game.state().clone();
        let Some(best) = pick_moves(
            &mut gg,
            &mut rng,
            n_times,
            limit,
            &DefaultTerminateSignal {},
            ucb1,
        ) else {
            return Some(false); // no move left: lost
        };

        for m in best {
            // a move planned on the canonicalized game must stay legal in the
            // real game; if not, the search is broken
            assert!(game.do_move(m), "planned move {m} is illegal in the real game");
        }
    }

    if game.state().is_win() {
        Some(true)
    } else {
        None
    }
}

#[test]
fn hop_terminates_on_dead_loop_seeds() {
    // these seeds used to loop forever with draw 1 (the PS/SP ping-pong bug)
    for seed in [6u64, 666_666, 2_007_112_002] {
        let res = run_hop(seed, 1, 20, 100, 200);
        assert!(res.is_some(), "seed {seed} draw 1 dead loops");
    }
}

#[test]
fn hop_terminates_draw3() {
    for seed in 0..5u64 {
        let res = run_hop(seed, 3, 20, 100, 200);
        assert!(res.is_some(), "seed {seed} draw 3 dead loops");
    }
}

#[test]
fn hop_terminates_draw1() {
    for seed in 0..5u64 {
        let res = run_hop(seed, 1, 20, 100, 200);
        assert!(res.is_some(), "seed {seed} draw 1 dead loops");
    }
}

#[test]
#[ignore] // full-strength search, takes a few seconds: cargo test -- --ignored
fn hop_solves_reported_seed() {
    let res = run_hop(6, 1, 3000, 1000, 200);
    assert_eq!(res, Some(true), "seed 6 draw 1 should be solved");
}
