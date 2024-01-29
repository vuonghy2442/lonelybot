use criterion::{black_box, criterion_group, criterion_main, Criterion};
use lonelybot::engine::{self, MoveType, Solitaire};
use rand::prelude::*;

fn criterion_benchmark(c: &mut Criterion) {
    let seed = 51;
    let mut game = Solitaire::new(&engine::generate_shuffled_deck(seed), 3);
    let mut rng = StdRng::seed_from_u64(seed);

    let mut moves = Vec::<MoveType>::new();
    let mut poses = Vec::<u8>::new();
    // for _ in 0..21 {
    //     moves.clear();
    //     game.gen_moves_::<true>(&mut moves);
    //     if moves.len() == 0 {
    //         break;
    //     }
    //     moves.sort();
    //     game.do_move(moves.choose(&mut rng).unwrap());
    // }

    // game.gen_moves_::<false>(&mut moves);

    // let m = *moves.choose(&mut rng).unwrap();

    let deck = game.get_deck_mask(false);
    let card = (deck.wrapping_neg() & deck).trailing_zeros() as u8;
    let card = card ^ ((card >> 1) & 2);
    println!("Card: {}", card);

    println!("N moves: {:?}", moves);

    moves.clear();
    // game.gen_moves_::<true>(&mut moves);

    // let [pile_stack, deck_stack, stack_pile, deck_pile, hidden_mask] = game.new_gen_moves();


    println!("N moves (filtered): {:?}", moves);

    // c.bench_function("gen_moves", |b| {
    //     b.iter(|| {
    //         moves.clear();
    //         game.gen_moves_::<false>(&mut moves);
    //         black_box(moves.len());
    //     })
    // });

    c.bench_function("find_card", |b| {
        b.iter(|| {
            game.deck
                .find_card(lonelybot::card::Card::new(card / 4, card % 4))
                .expect("okay");
        })
    });

    c.bench_function("new_gen_moves", |b| {
        b.iter(|| {
            black_box(game.new_gen_moves::<true>());
        })
    });

    // c.bench_function("move_undo", |b| {
    //     b.iter(|| {
    //         let undo = game.do_move(&m);
    //         game.undo_move(&m, &undo);
    //     })
    // });

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

    // c.bench_function("gen_moves_dom", |b| {
    //     b.iter(|| {
    //         moves.clear();
    //         game.gen_moves_::<true>(&mut moves);
    //         black_box(moves.len());
    //     })
    // });

    // c.bench_function("gen_deck_pile", |b| {
    //     b.iter(|| {
    //         moves.clear();
    //         game.gen_deck_pile::<true>(&mut moves, false);
    //     })
    // });

    // c.bench_function("gen_deck_stack", |b| {
    //     b.iter(|| {
    //         moves.clear();
    //         game.gen_deck_stack::<true>(&mut moves, false);
    //     })
    // });

    // c.bench_function("gen_pile_pile", |b| {
    //     b.iter(|| {
    //         moves.clear();
    //         game.gen_pile_pile::<true>(&mut moves);
    //     })
    // });

    // c.bench_function("gen_pile_stack", |b| {
    //     b.iter(|| {
    //         moves.clear();
    //         game.gen_pile_stack::<true>(&mut moves);
    //     })
    // });

    // c.bench_function("gen_stack_pile", |b| {
    //     b.iter(|| {
    //         moves.clear();
    //         game.gen_stack_pile::<true>(&mut moves);
    //     })
    // });
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
