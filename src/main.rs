pub mod card;
pub mod deck;
pub mod engine;
pub mod pile;
pub mod solver;

use rand::prelude::*;
use std::hint::black_box;
use std::io::Write;
use std::time::Instant;

use engine::*;

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

fn benchmark() {
    let mut rng = StdRng::seed_from_u64(14);

    let mut moves = Vec::<MoveType>::new();

    let mut total_moves = 0;
    let now = Instant::now();
    for i in 0..100 {
        let mut game = Solitaire::new(&generate_shuffled_deck(12 + i), 3);
        for _ in 0..100 {
            moves.clear();
            game.gen_moves_(&mut moves);
            if moves.len() == 0 {
                break;
            }
            game.do_move(moves.choose(&mut rng).unwrap());
            black_box(game.encode());
            total_moves += 1;
        }
    }
    println!(
        "{} {} op/s",
        total_moves,
        (total_moves as f64) / now.elapsed().as_secs_f64()
    );
}

fn test_solve() {
    let shuffled_deck = generate_shuffled_deck(22);
    println!("{}", Solvitaire::new(&shuffled_deck, 3));

    let mut g = Solitaire::new(&shuffled_deck, 3);

    let now = Instant::now();
    let res = solver::solve_game(&mut g);
    println!("Solved in {} ms", now.elapsed().as_secs_f64() * 1000f64);
    match res {
        Some(moves) => {
            println!("Solvable in {} moves", moves.len());
            println!("{:?}", moves);
        }
        None => println!("Impossible"),
    }
}

fn run() {
    test_solve();
    benchmark();

    let shuffled_deck = generate_shuffled_deck(12);

    println!("{}", Solvitaire::new(&shuffled_deck, 3));
    let mut game = Solitaire::new(&shuffled_deck, 3);

    let mut line = String::new();
    loop {
        print!("{}", game);

        print!("{:?}", game.encode());
        let moves = game.gen_moves();

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

fn main() {
    run();
}

// use std::thread;

// const STACK_SIZE: usize = 4 * 1024 * 1024;

// fn main() {
//     // Spawn thread with explicit stack size
//     let child = thread::Builder::new()
//         .stack_size(STACK_SIZE)
//         .spawn(run)
//         .unwrap();

//     // Wait for thread to join
//     child.join().unwrap();
// }
