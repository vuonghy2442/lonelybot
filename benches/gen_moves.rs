use criterion::{black_box, criterion_group, criterion_main, Criterion};
use lonelybot::engine::{self, MoveType, Solitaire};
use rand::prelude::*;

fn criterion_benchmark(c: &mut Criterion) {
    let seed = 51;
    let mut game = Solitaire::new(&engine::generate_shuffled_deck(seed), 3);
    let mut rng = StdRng::seed_from_u64(seed);

    let mut moves = Vec::<MoveType>::new();
    for _ in 0..21 {
        moves.clear();
        game.gen_moves_::<true>(&mut moves);
        if moves.len() == 0 {
            break;
        }
        moves.sort();
        game.do_move(moves.choose(&mut rng).unwrap());
    }

    game.gen_moves_::<false>(&mut moves);

    println!("N moves: {:?}", moves);

    moves.clear();
    game.gen_moves_::<true>(&mut moves);
    println!("N moves (filtered): {:?}", moves);

    c.bench_function("gen_moves", |b| {
        b.iter(|| {
            moves.clear();
            game.gen_moves_::<false>(&mut moves);
            black_box(moves.len());
        })
    });

    c.bench_function("new_gen_moves", |b| {
        b.iter(|| {
            black_box(game.new_gen_moves());
        })
    });


    c.bench_function("gen_moves_dom", |b| {
        b.iter(|| {
            moves.clear();
            game.gen_moves_::<true>(&mut moves);
            black_box(moves.len());
        })
    });

    c.bench_function("gen_deck_pile", |b| {
        b.iter(|| {
            moves.clear();
            game.gen_deck_pile::<true>(&mut moves, false);
        })
    });

    c.bench_function("gen_deck_stack", |b| {
        b.iter(|| {
            moves.clear();
            game.gen_deck_stack::<true>(&mut moves, false);
        })
    });

    c.bench_function("gen_pile_pile", |b| {
        b.iter(|| {
            moves.clear();
            game.gen_pile_pile::<true>(&mut moves);
        })
    });

    c.bench_function("gen_pile_stack", |b| {
        b.iter(|| {
            moves.clear();
            game.gen_pile_stack::<true>(&mut moves);
        })
    });

    c.bench_function("gen_stack_pile", |b| {
        b.iter(|| {
            moves.clear();
            game.gen_stack_pile::<true>(&mut moves);
        })
    });
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
