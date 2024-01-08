pub mod engine;

use rand::prelude::*;
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
    let mut game = Solitaire::new(&generate_shuffled_deck(12), 3);
    let mut rng = StdRng::seed_from_u64(14);

    let mut moves = Vec::<MoveType>::new();

    let now = Instant::now();
    for _ in 0..1000 {
        game.gen_moves_(&mut moves);
        game.do_move(moves.choose(&mut rng).unwrap());
    }
    println!("{} op/s", 1000f64 / now.elapsed().as_secs_f64());
    game.display();
}

fn main() {
    benchmark();

    println!("Hello, world!");
    let mut game = Solitaire::new(&generate_shuffled_deck(12), 3);
    let mut line = String::new();
    loop {
        game.display();
        let moves = game.gen_moves();

        // {
        //     let (current_deal, next_deal) = iter_deck(&game);
        //     for (pos, card) in current_deal {
        //         print!("{}-", pos);
        //         print_card(*card, " ")
        //     }
        //     println!();
        //     for (pos, card) in next_deal {
        //         print!("{}-", pos);
        //         print_card(*card, " ")
        //     }
        //     println!();
        // }
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
