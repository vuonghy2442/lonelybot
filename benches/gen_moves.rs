use criterion::{black_box, criterion_group, criterion_main, Criterion};
use lonelybot::{
    deck::{Deck, N_HIDDEN_CARDS},
    engine::{self, Move, Solitaire},
};
use rand::prelude::*;

fn criterion_benchmark(c: &mut Criterion) {
    let seed = 51;
    let mut game = Solitaire::new(&engine::generate_shuffled_deck(seed), 3);

    let sample_deck: Deck = Deck::new(
        engine::generate_shuffled_deck(seed)[N_HIDDEN_CARDS as usize..]
            .try_into()
            .unwrap(),
        3,
    );

    let mut rng = StdRng::seed_from_u64(seed);

    let mut moves = Vec::<Move>::new();
    for _ in 0..21 {
        moves.clear();
        game.list_moves::<true>(&mut moves);
        if moves.len() == 0 {
            break;
        }
        game.do_move(moves.choose(&mut rng).unwrap());
    }

    moves.clear();
    game.list_moves::<false>(&mut moves);

    let m: Move = *moves.choose(&mut rng).unwrap();

    let deck = game.get_deck_mask::<false>();
    let card = (deck.wrapping_neg() & deck).trailing_zeros() as u8;
    let card = card ^ ((card >> 1) & 2);
    println!("Card: {}", card);

    moves.clear();
    game.list_moves::<true>(&mut moves);

    c.bench_function("gen_moves", |b| {
        b.iter(|| {
            moves.clear();
            game.list_moves::<false>(&mut moves);
            black_box(moves.len());
        })
    });

    c.bench_function("gen_moves_dom", |b| {
        b.iter(|| {
            moves.clear();
            game.list_moves::<true>(&mut moves);
            black_box(moves.len());
        })
    });

    c.bench_function("find_card", |b| {
        b.iter(|| {
            sample_deck
                .find_card(lonelybot::card::Card::new(card / 4, card % 4))
                .expect("okay");
        })
    });

    c.bench_function("deck_mask", |b| {
        b.iter(|| {
            black_box(game.get_deck_mask::<true>());
        })
    });

    c.bench_function("pure_gen_moves", |b| {
        b.iter(|| {
            black_box(game.gen_moves::<true>());
        })
    });

    c.bench_function("move_undo", |b| {
        b.iter(|| {
            let undo = game.do_move(&m);
            game.undo_move(&m, &undo);
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
