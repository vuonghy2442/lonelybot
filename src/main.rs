pub mod engine;

use rand::prelude::*;
use std::io::Write;
use std::time::Instant;

use engine::*;

const fn num_to_pos(num: u8) -> Pos {
    if num == 0 {
        return Pos::Deck;
    } else if num < 5 {
        return Pos::Stack(num - 1);
    } else {
        return Pos::Pile(num - 5);
    }
}
const fn pos_to_num(p: &Pos) -> u8 {
    return match p {
        Pos::Deck => 0u8,
        Pos::Stack(id) => 1 + *id,
        Pos::Pile(id) => 5 + *id,
    };
}

fn benchmark() {
    let mut game = generate_game(&generate_random_deck(12), 3);
    let mut rng = StdRng::seed_from_u64(14);

    let mut moves = Vec::<MoveType>::new();

    let now = Instant::now();
    for _ in 0..1000 {
        gen_moves_(&game, &mut moves);
        do_move(&mut game, moves.choose(&mut rng).unwrap());
    }
    println!("{} op/s", 1000f64 / now.elapsed().as_secs_f64());
    display(&game);
}

fn main() {
    benchmark();

    println!("Hello, world!");
    let mut game = generate_game(&generate_random_deck(12), 3);
    let mut line = String::new();
    loop {
        display(&game);
        let moves = gen_moves(&game);
        println!(
            "{:?}",
            moves
                .iter()
                .map(|x| (pos_to_num(&x.0), pos_to_num(&x.1)))
                .collect::<Vec<(u8, u8)>>()
        );
        print!("Move: ");
        std::io::stdout().flush().unwrap();
        line.clear();
        let b1 = std::io::stdin().read_line(&mut line);
        if let Result::Err(_) = b1 {
            println!("Can't read");
            continue;
        }
        let res: Option<Vec<u8>> = line
            .trim()
            .split(' ')
            .map(|x| x.parse::<u8>().ok())
            .collect();
        if let Some([src, dst]) = res.as_deref() {
            do_move(&mut game, &(num_to_pos(*src), num_to_pos(*dst)));
        } else {
            println!("Invalid move");
        }
    }
}
