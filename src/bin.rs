use bpci::{Interval, NSuccessesSample, WilsonScore};
use lonelybot::engine::{generate_shuffled_deck, Encode, Move, Solitaire, Solvitaire, UndoInfo};
use rand::prelude::*;
use std::collections::HashSet;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;
use std::thread;
use std::time::Duration;
use std::{io::Write, time::Instant};

use lonelybot::solver::SearchResult;

fn benchmark(seed: u64) {
    let mut rng = StdRng::seed_from_u64(seed);

    let mut moves = Vec::<Move>::new();

    let mut total_moves = 0;
    let now = Instant::now();
    for i in 0..100 {
        let mut game = Solitaire::new(&generate_shuffled_deck(seed + i), 3);
        for _ in 0..100 {
            moves.clear();
            game.list_moves::<true>(&mut moves);
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

fn test_solve(seed: u64, terminated: &Arc<AtomicBool>) {
    let shuffled_deck = generate_shuffled_deck(seed);
    println!("{}", Solvitaire::new(&shuffled_deck, 3));

    let g = Solitaire::new(&shuffled_deck, 3);

    let now = Instant::now();
    let res = lonelybot::solver::run_solve(g, true, terminated);
    println!("Run in {} ms", now.elapsed().as_secs_f64() * 1000f64);
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
    let mut moves = Vec::<Move>::new();

    let mut move_hist = Vec::<(Move, UndoInfo)>::new();

    let mut game_state = HashSet::<Encode>::new();

    loop {
        print!("{}", game);
        if !game_state.insert(game.encode()) {
            println!("Already existed state");
        }

        moves.clear();
        game.list_moves::<true>(&mut moves);

        for (i, m) in moves.iter().enumerate() {
            print!("{}.{}, ", i, m);
        }
        println!();

        print!("Hash: {:?}\n", game.encode());
        print!("Move: ");
        std::io::stdout().flush().unwrap();
        line.clear();
        let b1 = std::io::stdin().read_line(&mut line);
        if let Result::Err(_) = b1 {
            println!("Can't read");
            continue;
        }
        let res: Option<i8> = line.trim().parse::<i8>().ok();
        if let Some(id) = res {
            if (id as usize) < moves.len() {
                let info = game.do_move(&moves[id as usize]);
                move_hist.push((moves[id as usize], info));
            } else {
                let (m, info) = &move_hist.pop().unwrap();
                game.undo_move(m, info);
                println!("Undo!!");
            }
        } else {
            println!("Invalid move");
        }
    }
}

fn solve_loop(seed: u64, terminated: &Arc<AtomicBool>) {
    let mut cnt_terminated = 0;
    let mut cnt_solve = 0;
    let mut cnt_total = 0;

    let start = Instant::now();

    for seed in seed.. {
        let shuffled_deck = generate_shuffled_deck(seed);
        let g = Solitaire::new(&shuffled_deck, 3);

        let now = Instant::now();
        let res = lonelybot::solver::run_solve(g, false, terminated).0;
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
            "Run {} in {:.2} ms. {:?}: ({}-{}/{} ~ {:.4}<={:.4}<={:.4})",
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

        if terminated.load(Ordering::Relaxed) {
            thread::sleep(Duration::from_millis(500));
            terminated.store(false, Ordering::Relaxed)
        }
    }

    println!("Total run time: {:?}", Instant::now() - start);
}

fn handling_signal() -> Arc<AtomicBool> {
    let terminated = Arc::new(AtomicBool::new(false));

    signal_hook::flag::register_conditional_shutdown(
        signal_hook::consts::signal::SIGINT,
        1,
        Arc::clone(&terminated),
    )
    .expect("Can't register hook");

    signal_hook::flag::register(signal_hook::consts::signal::SIGINT, Arc::clone(&terminated))
        .expect("Can't register hook");
    terminated
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
            test_solve(seed, &handling_signal());
        }
        "play" => {
            game_loop(seed);
        }
        "bench" => {
            benchmark(seed);
        }
        "rate" => {
            solve_loop(seed, &handling_signal());
        }
        _ => {
            panic!("Wrong method")
        }
    }
}
