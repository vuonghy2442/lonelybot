use lonelybot::engine::SolitaireEngine;
use lonelybot::hop_solver::HopResult;
use lonelybot::mcts_solver::pick_moves;
use lonelybot::pruning::NoPruner;
use lonelybot::shuffler::default_shuffle;
use lonelybot::state::Solitaire;
use lonelybot::tracking::DefaultTerminateSignal;
use rand::{rngs::SmallRng, SeedableRng};
use std::num::NonZeroU8;

fn ucb1(r: &HopResult, n_total: usize) -> f64 {
    const C: f64 = 2.;

    if r.played == 0 {
        f64::INFINITY
    } else {
        #[allow(clippy::cast_precision_loss)]
        {
            r.rate() + C * ((n_total as f64).ln() / r.played as f64).sqrt()
        }
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
    // decorrelate the playout rng from the deck shuffle, like lonecli's do_hop
    let mixed = {
        let mut z = seed.wrapping_add(0x9E37_79B9_7F4A_7C15);
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    };
    let mut rng = SmallRng::seed_from_u64(mixed);

    for _ in 0..max_turns {
        if game.state().is_win() {
            return Some(true);
        }

        // plan on the canonicalized game so the search never sees the real
        // hidden cards, like lonecli's do_hop
        let mut gg = game.state().clone();
        gg.hidden_clear();
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
