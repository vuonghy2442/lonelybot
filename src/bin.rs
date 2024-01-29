use bpci::{Interval, NSuccessesSample, WilsonScore};
use lonelybot::card::Card;
use rand::prelude::*;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;
use std::thread;
use std::time::Duration;
use std::{io::Write, time::Instant};

use lonelybot::engine::{self, *};

use lonelybot::solver::SearchResult;

const fn num_to_pos(num: i8) -> Pos {
    if num <= 0 {
        return Pos::Deck((-num) as u8);
    } else if num < 5 {
        return Pos::Stack(num as u8 - 1);
    } else {
        return Pos::Pile(num as u8 - 5);
    }
}
const fn pos_to_num(p: &Pos) -> i8 {
    return match p {
        Pos::Deck(id) => -(*id as i8),
        Pos::Stack(id) => 1 + (*id as i8),
        Pos::Pile(id) => 5 + (*id as i8),
    };
}

// fn benchmark(seed: u64) {
//     let mut rng = StdRng::seed_from_u64(seed);

//     let mut moves = Vec::<MoveType>::new();

//     let mut total_moves = 0;
//     let now = Instant::now();
//     for i in 0..100 {
//         let mut game = Solitaire::new(&generate_shuffled_deck(seed + i), 3);
//         for _ in 0..100 {
//             moves.clear();
//             game.gen_moves_::<true>(&mut moves);
//             if moves.len() == 0 {
//                 break;
//             }
//             game.do_move(moves.choose(&mut rng).unwrap());
//             std::hint::black_box(game.encode());
//             total_moves += 1;
//         }
//     }
//     println!(
//         "{} {} op/s",
//         total_moves,
//         (total_moves as f64) / now.elapsed().as_secs_f64()
//     );
// }

// fn test_solve(seed: u64, terminated: &Arc<AtomicBool>) {
//     let shuffled_deck = generate_shuffled_deck(seed);
//     println!("{}", Solvitaire::new(&shuffled_deck, 3));

//     let g = Solitaire::new(&shuffled_deck, 3);

//     let now = Instant::now();
//     let res = lonelybot::solver::run_solve(g, true, terminated);
//     println!("Run in {} ms", now.elapsed().as_secs_f64() * 1000f64);
//     println!("Statistic\n{}", res.1);
//     match res.0 {
//         SearchResult::Solved => {
//             let m = res.2.unwrap();
//             println!("Solvable in {} moves", m.len());
//             println!("{:?}", m);
//         }
//         SearchResult::Unsolvable => println!("Impossible"),
//         SearchResult::Terminated => println!("Terminated"),
//     }
// }

fn gen_moves(game: &Solitaire) {
    let [to_stack, from_stack, reveal, deck] = game.new_gen_moves::<false>();

    print_cards(&to_cards(to_stack));
    print_cards(&to_cards(from_stack));
    print_cards(&to_cards(reveal));
    print_cards(&to_cards(deck));
}

fn game_loop(seed: u64) {
    let shuffled_deck = generate_shuffled_deck(seed);

    println!("{}", Solvitaire::new(&shuffled_deck, 3));
    let mut game = Solitaire::new(&shuffled_deck, 3);

    let mut line = String::new();
    loop {
        print!("{}", game);

        gen_moves(&game);
        print!("Hash: {:?}\n", game.encode());
        // let moves = game.gen_moves::<true>();

        // println!(
        //     "{:?}",
        //     moves
        //         .iter()
        //         .map(|x| (pos_to_num(&x.0), pos_to_num(&x.1)))
        //         .collect::<Vec<(i8, i8)>>()
        // );
        print!("Move: ");
        std::io::stdout().flush().unwrap();
        line.clear();
        let b1 = std::io::stdin().read_line(&mut line);
        if let Result::Err(_) = b1 {
            println!("Can't read");
            continue;
        }
        let res: Option<Vec<i8>> = line
            .trim()
            .split(' ')
            .map(|x| x.parse::<i8>().ok())
            .collect();
        if let Some([src, dst]) = res.as_deref() {
            // game.do_move(&(num_to_pos(*src), num_to_pos(*dst)));
        } else {
            println!("Invalid move");
        }
    }
}

// fn solve_loop(seed: u64, terminated: &Arc<AtomicBool>) {
//     let mut cnt_terminated = 0;
//     let mut cnt_solve = 0;
//     let mut cnt_total = 0;

//     let start = Instant::now();

//     for seed in seed.. {
//         let shuffled_deck = generate_shuffled_deck(seed);
//         let g = Solitaire::new(&shuffled_deck, 3);

//         let now = Instant::now();
//         let res = lonelybot::solver::run_solve(g, false, terminated).0;
//         match res {
//             SearchResult::Solved => cnt_solve += 1 as usize,
//             SearchResult::Terminated => cnt_terminated += 1 as usize,
//             _ => {}
//         };

//         cnt_total += 1 as usize;

//         let lower = NSuccessesSample::new(cnt_total as u32, cnt_solve as u32)
//             .unwrap()
//             .wilson_score(1.960)
//             .lower(); //95%
//         let higher = NSuccessesSample::new(cnt_total as u32, (cnt_solve + cnt_terminated) as u32)
//             .unwrap()
//             .wilson_score(1.960)
//             .upper(); //95%
//         println!(
//             "Run {} in {:.2} ms. {:?}: ({}-{}/{} ~ {:.4}<={:.4}<={:.4})",
//             seed,
//             now.elapsed().as_secs_f64() * 1000f64,
//             res,
//             cnt_solve,
//             cnt_terminated,
//             cnt_total,
//             lower,
//             cnt_solve as f64 / cnt_total as f64,
//             higher,
//         );

//         if terminated.load(Ordering::Relaxed) {
//             thread::sleep(Duration::from_millis(500));
//             terminated.store(false, Ordering::Relaxed)
//         }
//     }

//     println!("Total run time: {:?}", Instant::now() - start);
// }

fn main() {
    let terminated = Arc::new(AtomicBool::new(false));

    signal_hook::flag::register_conditional_shutdown(
        signal_hook::consts::signal::SIGINT,
        1,
        Arc::clone(&terminated),
    )
    .expect("Can't register hook");

    signal_hook::flag::register(signal_hook::consts::signal::SIGINT, Arc::clone(&terminated))
        .expect("Can't register hook");

    let method = std::env::args().nth(1).expect("no seed given");
    let seed = std::env::args().nth(2).expect("no seed given");
    let seed: u64 = seed.parse().expect("uint 64");
    match method.as_ref() {
        "print" => {
            let shuffled_deck = generate_shuffled_deck(seed);

            println!("{}", Solvitaire::new(&shuffled_deck, 3));
        }
        "solve" => {
            // test_solve(seed, &terminated);
        }
        "play" => {
            game_loop(seed);
        }
        "bench" => {
            // benchmark(seed);
        }
        "rate" => {
            // solve_loop(seed, &terminated);
        }
        _ => {
            panic!("Wrong method")
        }
    }
}
