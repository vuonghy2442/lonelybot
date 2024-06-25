use std::num::NonZeroU8;

use criterion::{black_box, criterion_group, criterion_main, Criterion};
use lonelybot::{
    deck::{Deck, N_PILE_CARDS},
    engine::SolitaireEngine,
    pruning::{CyclePruner, NoPruner},
    shuffler::{self, default_shuffle},
    state::Solitaire,
};
use rand::prelude::*;

fn criterion_benchmark(c: &mut Criterion) {
    let seed = 51;
    let draw_step = NonZeroU8::new(3).unwrap();

    let mut game: SolitaireEngine<NoPruner> =
        Solitaire::new(&shuffler::default_shuffle(seed), draw_step).into();

    let sample_deck: Deck = Deck::new(
        shuffler::default_shuffle(seed)[N_PILE_CARDS as usize..]
            .try_into()
            .unwrap(),
        draw_step,
    );

    let mut rng = StdRng::seed_from_u64(seed);

    for _ in 0..21 {
        let moves = game.list_moves_dom();

        if moves.is_empty() {
            break;
        }
        game.do_move(*moves.choose(&mut rng).unwrap());
    }

    let moves = game.list_moves();

    let m = *moves.choose(&mut rng).unwrap();

    let card = game.state().get_deck().iter().next().unwrap();

    c.bench_function("gen_moves", |b| {
        b.iter(|| {
            let moves = game.list_moves();

            black_box(moves.len());
        })
    });

    c.bench_function("gen_moves_dom", |b| {
        b.iter(|| {
            let moves = game.list_moves_dom();
            black_box(moves.len());
        })
    });

    c.bench_function("find_card", |b| {
        b.iter(|| {
            black_box(sample_deck.find_card_fast(card));
        })
    });

    // c.bench_function("deck_mask", |b| {
    //     b.iter(|| {
    //         black_box(game.get_deck_mask::<true>());
    //     })
    // });

    c.bench_function("pure_gen_moves", |b| {
        b.iter(|| {
            black_box(game.state().gen_moves::<true>());
        })
    });

    c.bench_function("move_undo", |b| {
        b.iter(|| {
            game.do_move(m);
            game.undo_move();
        })
    });

    const TOTAL_GAME: u64 = 1000;

    c.bench_function("random_playout", |b| {
        b.iter(|| {
            let mut total_win = 0;
            for i in 0..TOTAL_GAME {
                let mut game: SolitaireEngine<CyclePruner> =
                    Solitaire::new(&default_shuffle(i), draw_step).into();

                loop {
                    if game.state().is_win() {
                        total_win += 1;
                        break;
                    }
                    let moves = game.list_moves_dom();

                    if moves.is_empty() {
                        break;
                    }

                    let m = &moves[0];

                    game.do_move(*m);
                }
            }
            black_box(total_win);
        })
    });

    // let mm = pile_stack.wrapping_neg() & pile_stack;

    // if mm != 0 {
    //     c.bench_function("make_stack", |b| {
    //         b.iter(|| {
    //             let undo = game.make_stack::<false>(&mm);
    //             game.unmake_stack::<false>(&mm, &undo);
    //         })
    //     });
    // }

    // let mm = deck_stack.wrapping_neg() & deck_stack;

    // if mm != 0 {
    //     c.bench_function("make_deck_stack", |b| {
    //         b.iter(|| {
    //             let undo = game.make_stack::<true>(&mm);
    //             game.unmake_stack::<true>(&mm, &undo);
    //         })
    //     });
    // }
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
