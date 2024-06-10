use std::num::NonZeroU8;

use criterion::{black_box, criterion_group, criterion_main, Criterion};
use lonelybot::{
    deck::{Deck, N_PILE_CARDS},
    engine::SolitaireEngine,
    pruning::NoPruner,
    shuffler,
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

    let card = game.state().get_deck().iter().iter().next().unwrap();

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
            sample_deck.find_card(*card).expect("okay");
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
