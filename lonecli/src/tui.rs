use core::fmt;

use lonelybot::card::{Card, N_SUITS};
use lonelybot::deck::{Drawable, N_PILES};
use lonelybot::formatter::{NUMBERS, SYMBOLS};
use lonelybot::stack::Stack;
use lonelybot::standard::{HiddenVec, PileVec, StandardSolitaire};
use lonelybot::state::Solitaire;

use colored::{Color, Colorize};

pub(crate) const COLOR: [Color; N_SUITS as usize] =
    [Color::Red, Color::Red, Color::Black, Color::Black];

pub(crate) struct ColoredCard(Option<Card>);

impl fmt::Display for ColoredCard {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if let Some(c) = self.0 {
            let (u, v) = c.split();
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

fn color(c: Option<Card>) -> ColoredCard {
    ColoredCard(c)
}

pub(crate) fn print_foundation(stack: &Stack) {
    print!("\t\t");
    // print out the foundation stack
    for i in 0..N_SUITS {
        let card = stack.get(i);
        let card = if card == 0 {
            None
        } else {
            Some(Card::new(card - 1, i))
        };
        print!("{}.{} ", i + 1, color(card));
    }
    println!();
}

pub(crate) fn print_piles(
    piles: &[PileVec; N_PILES as usize],
    hidden: &[HiddenVec; N_PILES as usize],
) {
    for i in 0..N_PILES {
        print!("{}\t", i + 5);
    }
    println!();

    // printing
    for i in 0.. {
        let mut is_print = false;
        for j in 0..N_PILES {
            let cur_pile = &piles[j as usize];

            let n_visible = cur_pile.len() as u8;
            let n_hidden = hidden[j as usize].len() as u8;
            if n_hidden > i {
                print!("**\t");
                is_print = true;
            } else if i < n_hidden + n_visible {
                print!("{}\t", color(Some(cur_pile[(i - n_hidden) as usize])));
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

pub(crate) fn print_game(game: &Solitaire) {
    // print out the deck
    for (pos, card, t) in game.get_deck().iter_all() {
        let s = format!("{pos} ");
        let prefix = match t {
            Drawable::None => format!(" {}", s.bright_black()),
            Drawable::Current => format!(">{}", s.on_blue()),
            Drawable::Next => format!("+{}", s.on_bright_blue()),
        };
        print!("{}{} ", prefix, color(Some(card)));
    }
    println!();

    print_foundation(game.get_stack());

    let piles: [PileVec; N_PILES as usize] = game.compute_visible_piles();
    let hidden: [HiddenVec; N_PILES as usize] = game.get_hidden().to_piles();
    print_piles(&piles, &hidden);
}

pub(crate) fn _print_standard_game(game: &StandardSolitaire) {
    // print out the deck
    print!("0. ");
    for card in game.get_deck().peek_waste::<3>() {
        print!("{} ", color(Some(card)));
    }

    print_foundation(game.get_stack());

    let piles = game.get_piles();
    let hidden = game.get_hidden();
    print_piles(piles, hidden);
}
