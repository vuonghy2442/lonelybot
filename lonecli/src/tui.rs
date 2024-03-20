use core::fmt;

use lonelybot::card::{Card, NUMBERS, N_RANKS, N_SUITS, SYMBOLS};
use lonelybot::deck::{Drawable, N_PILES};
use lonelybot::engine::Solitaire;
use lonelybot::standard::StandardSolitaire;

use colored::{Color, Colorize};

pub const COLOR: [Color; N_SUITS as usize] = [Color::Red, Color::Red, Color::Black, Color::Black];

pub struct ColoredCard(Card);

impl fmt::Display for ColoredCard {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let (u, v) = self.0.split();
        if u < N_RANKS {
            write!(
                f,
                "{}{}",
                NUMBERS[u as usize].black().on_white(),
                SYMBOLS[v as usize].on_white().color(COLOR[v as usize])
            )
        } else {
            write!(f, "  ")
        }
    }
}

fn color(c: Card) -> ColoredCard {
    ColoredCard(c)
}

pub fn print_game(game: &Solitaire) {
    // print out the deck
    for (pos, card, t) in game.get_deck().iter_all() {
        let s = format!("{pos} ");
        let prefix = match t {
            Drawable::None => format!(" {}", s.bright_black()),
            Drawable::Current => format!(">{}", s.on_blue()),
            Drawable::Next => format!("+{}", s.on_bright_blue()),
        };
        print!("{}{} ", prefix, color(*card));
    }
    println!();

    print!("\t\t");

    // print out the foundation stack
    for i in 0..N_SUITS {
        let card = game.get_stack()[i as usize];
        let card = if card == 0 {
            Card::FAKE
        } else {
            Card::new(card - 1, i)
        };
        print!("{}.{} ", i + 1, color(card));
    }
    println!();

    for i in 0..N_PILES {
        print!("{}\t", i + 5);
    }
    println!();

    let piles = game.get_normal_piles();

    // printing
    for i in 0.. {
        let mut is_print = false;
        for j in 0..N_PILES {
            let cur_pile = &piles[j as usize];

            let n_hidden = game.get_n_hidden()[j as usize].saturating_sub(1);
            let n_visible = cur_pile.len() as u8;
            if n_hidden > i {
                print!("**\t");
                is_print = true;
            } else if i < n_hidden + n_visible {
                print!("{}\t", color(cur_pile[(i - n_hidden) as usize]));
                is_print = true;
            } else {
                print!("  \t");
            }
        }
        println!();
        if !is_print {
            break;
        }
    }
}

pub fn _print_standard_game(game: &StandardSolitaire) {
    // print out the deck
    print!("0. ");
    for card in game.peek_waste(3) {
        print!("{} ", color(card));
    }

    print!("\t\t");

    // print out the foundation stack
    for i in 0..N_SUITS {
        let card = game.get_stack()[i as usize];
        let card = if card == 0 {
            Card::FAKE
        } else {
            Card::new(card - 1, i)
        };
        print!("{}.{} ", i + 1, color(card));
    }
    println!();

    for i in 0..N_PILES {
        print!("{}\t", i + 5);
    }
    println!();

    let piles = game.get_piles();
    let hiddens = game.get_hidden();

    // printing
    for i in 0.. {
        let mut is_print = false;
        for j in 0..N_PILES {
            let  cur_pile = &piles[j as usize];

            let n_visible = cur_pile.len() as u8;
            let n_hidden = hiddens[j as usize].len() as u8;
            if n_hidden > i {
                print!("**\t");
                is_print = true;
            } else if i < n_hidden + n_visible {
                print!("{}\t", color(cur_pile[(i - n_hidden) as usize]));
                is_print = true;
            } else {
                print!("  \t");
            }
        }
        println!();
        if !is_print {
            break;
        }
    }
}
