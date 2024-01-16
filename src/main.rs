pub mod card;
pub mod deck;
pub mod engine;
pub mod pile;
pub mod solver;

use bpci::{Interval, NSuccessesSample, WilsonScore};
use rand::prelude::*;
use std::{io::Write, time::Instant};

use engine::*;

use crate::solver::SearchResult;

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

fn benchmark(seed: u64) {
    let mut rng = StdRng::seed_from_u64(seed);

    let mut moves = Vec::<MoveType>::new();

    let mut total_moves = 0;
    let now = Instant::now();
    for i in 0..100 {
        let mut game = Solitaire::new(&generate_shuffled_deck(seed + i), 3);
        for _ in 0..100 {
            moves.clear();
            game.gen_moves_::<true>(&mut moves);
            if moves.len() == 0 {
                break;
            }
            game.do_move(moves.choose(&mut rng).unwrap());
            std::hint::black_box(game.encode());
            total_moves += 1;
        }
    }
    println!(
        "{} {} op/s",
        total_moves,
        (total_moves as f64) / now.elapsed().as_secs_f64()
    );
}

fn test_solve(seed: u64) {
    let shuffled_deck = generate_shuffled_deck(seed);
    println!("{}", Solvitaire::new(&shuffled_deck, 3));

    let g = Solitaire::new(&shuffled_deck, 3);

    let now = Instant::now();
    let res = solver::run_solve(g, true);
    println!("Solved in {} ms", now.elapsed().as_secs_f64() * 1000f64);
    println!("Statistic\n{}", res.1);
    match res.0 {
        SearchResult::Solved => {
            let m = res.2.unwrap();
            println!("Solvable in {} moves", m.len());
            println!("{:?}", m);
        }
        SearchResult::Unsolvable => println!("Impossible"),
        SearchResult::Terminated => println!("Terminated"),
    }
}

fn game_loop(seed: u64) {
    let shuffled_deck = generate_shuffled_deck(seed);

    println!("{}", Solvitaire::new(&shuffled_deck, 3));
    let mut game = Solitaire::new(&shuffled_deck, 3);

    let mut line = String::new();
    loop {
        print!("{}", game);

        print!("{:?}", game.encode());
        let moves = game.gen_moves::<true>();

        println!(
            "{:?}",
            moves
                .iter()
                .map(|x| (pos_to_num(&x.0), pos_to_num(&x.1)))
                .collect::<Vec<(i8, i8)>>()
        );
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
            game.do_move(&(num_to_pos(*src), num_to_pos(*dst)));
        } else {
            println!("Invalid move");
        }
    }
}

fn solve_loop(seed: u64) {
    let mut cnt_terminated = 0;
    let mut cnt_solve = 0;
    let mut cnt_total = 0;

    let start = Instant::now();

    for seed in seed.. {
        let shuffled_deck = generate_shuffled_deck(seed);
        let g = Solitaire::new(&shuffled_deck, 3);

        let now = Instant::now();
        let res = solver::run_solve(g, false).0;
        match res {
            SearchResult::Solved => cnt_solve += 1 as usize,
            SearchResult::Terminated => cnt_terminated += 1 as usize,
            _ => {}
        };

        cnt_total += 1 as usize;

        let lower = NSuccessesSample::new(cnt_total as u32, cnt_solve as u32)
            .unwrap()
            .wilson_score(1.960)
            .lower(); //95%
        let higher = NSuccessesSample::new(cnt_total as u32, (cnt_solve + cnt_terminated) as u32)
            .unwrap()
            .wilson_score(1.960)
            .upper(); //95%
        println!(
            "Solved {} in {} ms. {:?}: ({}-{}/{} ~  {}<={}<={})",
            seed,
            now.elapsed().as_secs_f64() * 1000f64,
            res,
            cnt_solve,
            cnt_terminated,
            cnt_total,
            lower,
            cnt_solve as f64 / cnt_total as f64,
            higher,
        );
    }

    println!("Total run time: {:?}", Instant::now() - start);
}

fn main() {
    let method = std::env::args().nth(1).expect("no seed given");
    let seed = std::env::args().nth(2).expect("no seed given");
    let seed: u64 = seed.parse().expect("uint 64");
    match method.as_ref() {
        "print" => {
            let shuffled_deck = generate_shuffled_deck(seed);

            println!("{}", Solvitaire::new(&shuffled_deck, 3));
        }
        "solve" => {
            test_solve(seed);
        }
        "play" => {
            game_loop(seed);
        }
        "bench" => {
            benchmark(seed);
        }
        "rate" => {
            solve_loop(seed);
        }
        _ => {
            panic!("Wrong method")
        }
    }
}
