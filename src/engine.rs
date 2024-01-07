use colored::{Color, Colorize};
use rand::prelude::*;

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Pos {
    Deck,
    Stack(u8),
    Pile(u8),
}

pub type CardType = u8;
pub type MoveType = (Pos, Pos);

const COLOR: [Color; 5] = [
    Color::Red,
    Color::Red,
    Color::Black,
    Color::Black,
    Color::White,
];

const SYMBOLS: [&'static str; 5] = ["♥", "♦", "♣", "♠", "X"];
const NUMBERS: [&'static str; 14] = [
    "A", "2", "3", "4", "5", "6", "7", "8", "9", "10", "J", "Q", "K", "X",
];

const N_SUITS: u8 = 4;
const N_RANKS: u8 = 13;
const N_CARDS: u8 = N_SUITS * N_RANKS;

type CardDeck = [CardType; N_CARDS as usize];

const fn split_card(card: CardType) -> (u8, u8) {
    return (card / N_SUITS, card % N_SUITS);
}

const fn make_card(rank: u8, suit: u8) -> u8 {
    assert!(rank <= N_RANKS && suit < N_SUITS);
    return (rank * N_SUITS + suit) as CardType;
}

const fn fit_after(card_a: CardType, card_b: CardType) -> bool {
    let card_a = split_card(card_a);
    let card_b = split_card(card_b);
    return card_a.0 == card_b.0 + 1 && (card_a.1 ^ card_b.1 >= 2 || card_a.0 >= N_RANKS);
}

const FAKE_CARD: CardType = make_card(N_RANKS, 0);

const N_PILES: u8 = 7;
const N_HIDDEN_CARDS: u8 = N_PILES * (N_PILES - 1) / 2;

#[derive(Debug)]
pub struct Pile {
    start_rank: u8,
    end: CardType,
    suit: u16,
}

#[derive(Debug)]
pub struct Solitaire {
    hidden_piles: [CardType; N_HIDDEN_CARDS as usize],
    n_hidden: [u8; N_PILES as usize],

    // start card ends card and flags
    visible_piles: [Pile; N_PILES as usize],
    final_stack: [u8; 4],
    deck: [u8; (N_CARDS - N_HIDDEN_CARDS - N_PILES) as usize],
    draw_step: u8,
    draw_next: u8, // start position of next pile
    draw_cur: u8,  // size of the previous pile
    n_deck: u8,
}

const fn create_pile(c: CardType) -> Pile {
    return Pile {
        start_rank: split_card(c).0,
        end: c,
        suit: (c & 1) as u16,
    };
}

pub fn generate_random_deck(seed: u64) -> CardDeck {
    let mut rng = StdRng::seed_from_u64(seed);
    let mut cards: [CardType; N_CARDS as usize] = core::array::from_fn(|i| i as CardType);
    cards.shuffle(&mut rng);
    return cards;
}

pub fn generate_game(cards: &CardDeck, draw_step: u8) -> Solitaire {
    let hidden_piles: [CardType; N_HIDDEN_CARDS as usize] =
        cards[0..N_HIDDEN_CARDS as usize].try_into().unwrap();
    let n_hidden: [u8; N_PILES as usize] = core::array::from_fn(|i| i as CardType);

    let visible_cards: &[CardType; N_PILES as usize] = cards
        [N_HIDDEN_CARDS as usize..(N_HIDDEN_CARDS + N_PILES) as usize]
        .try_into()
        .unwrap();

    let visible_piles: [Pile; N_PILES as usize] = visible_cards.map(|c| create_pile(c));

    const N_FULL_DECK: u8 = N_CARDS - N_HIDDEN_CARDS - N_PILES;

    let deck: [u8; N_FULL_DECK as usize] = cards[(N_HIDDEN_CARDS + N_PILES) as usize..]
        .try_into()
        .unwrap();

    let draw_step = std::cmp::min(N_FULL_DECK, draw_step);

    let final_stack: [u8; 4] = [0u8; 4];

    return Solitaire {
        hidden_piles,
        n_hidden,
        visible_piles,
        deck,
        final_stack,
        draw_step,
        draw_cur: draw_step,
        draw_next: draw_step,
        n_deck: N_CARDS - N_HIDDEN_CARDS - N_PILES,
    };
}

const fn peek_deck(game: &Solitaire) -> CardType {
    return if game.draw_cur == 0 {
        FAKE_CARD
    } else {
        game.deck[game.draw_cur as usize - 1]
    };
}

fn pop_deck(game: &mut Solitaire) {
    assert!(game.draw_cur > 0);
    game.draw_cur -= 1;
}

fn pop_hidden(g: &mut Solitaire, pos: u8) -> CardType {
    let ref mut n_hid = g.n_hidden[pos as usize];
    if *n_hid == 0 {
        return FAKE_CARD;
    } else {
        *n_hid -= 1;
        return g.hidden_piles[(pos * (pos - 1) / 2 + *n_hid) as usize];
    }
}

const fn is_empty(p: &Pile) -> bool {
    return p.start_rank < split_card(p.end).0;
}

const fn pile_type(p: &Pile) -> u8 {
    let (rank, suit) = split_card(p.end);
    return (rank & 1) ^ (suit / 2);
}

const fn pile_length(p: &Pile) -> u8 {
    return p.start_rank - split_card(p.end).0 + 1;
}

const fn get_card_bottom(p: &Pile, pos: u8) -> u8 {
    return (((p.end + pos * N_SUITS) & !1) ^ ((pos & 1) * 2))
        | (((p.suit >> pos) & 1) as CardType);
}

const fn get_card_top(p: &Pile, pos: u8) -> u8 {
    let len = pile_length(p);
    assert!(pos < len);
    return get_card_bottom(p, len - pos - 1);
}

const fn pop_card(p: &Pile, step: u8) -> Pile {
    assert!(pile_length(p) >= step);

    return Pile {
        start_rank: p.start_rank,
        end: get_card_bottom(p, step),
        suit: p.suit >> step,
    };
}

const fn push_card(p: &Pile, c: CardType) -> Pile {
    assert!(fit_after(p.end, c));

    return Pile {
        start_rank: p.start_rank,
        end: c,
        suit: (p.suit << 1) | ((c & 1) as u16),
    };
}

const fn movable(from: &Pile, to: &Pile) -> bool {
    let start_rank = from.start_rank;
    let (end_rank, _) = split_card(from.end);
    let (dst_rank, _) = split_card(to.end);
    return (pile_type(from) == pile_type(to) || dst_rank >= N_RANKS)
        && end_rank < dst_rank
        && dst_rank <= start_rank + 1;
}

const fn move_pile(from: &Pile, to: &Pile) -> (Pile, Pile) {
    assert!(movable(from, to));
    let (src_rank, _) = split_card(from.end);
    let (dst_rank, _) = split_card(to.end);

    let n_moved = dst_rank - src_rank;

    return (
        pop_card(from, n_moved),
        Pile {
            start_rank: to.start_rank,
            end: from.end,
            suit: (to.suit << n_moved) | (from.suit & ((1 << n_moved) - 1)),
        },
    );
}

pub fn gen_moves_(game: &Solitaire, moves: &mut Vec<MoveType>) {
    // let mut moves = vec![(Pos::Deck, Pos::Deck)];
    moves.clear();
    moves.push((Pos::Deck, Pos::Deck));

    // src = src.Deck
    let deck_card = peek_deck(&game);

    {
        let (rank, suit) = split_card(deck_card);
        if rank < N_RANKS && game.final_stack[suit as usize] == rank {
            moves.push((Pos::Deck, Pos::Stack(suit)));
        }
    }

    // move to deck
    for (id, pile) in game.visible_piles.iter().enumerate() {
        // source = 0
        let dst_card = pile.end;
        if fit_after(dst_card, deck_card) {
            moves.push((Pos::Deck, Pos::Pile(id as u8)));
        }

        let (rank, suit) = split_card(dst_card);
        if game.final_stack[suit as usize] == rank {
            moves.push((Pos::Pile(id as u8), Pos::Stack(suit)));
        }

        for i in 1..2u8 {
            if rank > 0 && game.final_stack[(suit ^ i ^ 2) as usize] == rank {
                moves.push((Pos::Stack(suit ^ i ^ 2), Pos::Pile(id as u8)));
            }
        }

        for (other_id, other_pile) in game.visible_piles.iter().enumerate() {
            if id != other_id && movable(other_pile, pile) {
                moves.push((Pos::Pile(other_id as u8), Pos::Pile(id as u8)));
            }
        }
    }
}

pub fn gen_moves(game: &Solitaire) -> Vec<MoveType> {
    let mut moves = Vec::<MoveType>::new();
    gen_moves_(game, &mut moves);
    return moves;
}

// this is unsafe gotta check it is valid move before
pub fn do_move(game: &mut Solitaire, m: &MoveType) -> i32 {
    let (src, dst) = m;
    // handling final stack
    if let &Pos::Stack(id) = src {
        assert!(game.final_stack[id as usize] > 0);
        game.final_stack[id as usize] -= 1;
    }
    if let &Pos::Stack(id) = dst {
        assert!(game.final_stack[id as usize] < N_RANKS);
        game.final_stack[id as usize] += 1;
    }
    // handling deck

    let deck_card = peek_deck(game);

    match src {
        Pos::Deck => match dst {
            Pos::Deck => {
                assert!(game.draw_cur <= game.draw_next);
                let redealt = game.draw_next >= game.n_deck;

                if redealt {
                    game.n_deck = game.draw_cur;
                    game.draw_next = 0;
                    game.draw_cur = 0;
                }

                let step = std::cmp::min(game.n_deck - game.draw_next, game.draw_step);

                if game.draw_cur != game.draw_next {
                    // moving stuff
                    for i in 0..step {
                        game.deck[(game.draw_cur + i) as usize] =
                            game.deck[(game.draw_next + i) as usize];
                    }
                }

                game.draw_cur += step;
                game.draw_next += step;
                return if redealt { -2 } else { 0 };
            }
            Pos::Stack(_) => {
                pop_deck(game);
                return 20;
            }
            &Pos::Pile(id_pile) => {
                pop_deck(game);
                let ref mut pile = game.visible_piles[id_pile as usize];
                *pile = push_card(&pile, deck_card);
                return 5;
            }
        },
        &Pos::Stack(id) => {
            match dst {
                &Pos::Pile(id_pile) => {
                    let card: u8 = make_card(game.final_stack[id as usize], id);
                    let ref mut pile = game.visible_piles[id_pile as usize];
                    *pile = push_card(pile, card);
                    return -15;
                }
                _ => unreachable!(),
            };
        }
        &Pos::Pile(id) => {
            let mut reward = match dst {
                Pos::Stack(_) => {
                    let ref mut pile = game.visible_piles[id as usize];
                    *pile = pop_card(pile, 1);
                    15
                }
                &Pos::Pile(id_pile) => {
                    let (new_from, new_to) = move_pile(
                        &game.visible_piles[id as usize],
                        &game.visible_piles[id_pile as usize],
                    );
                    game.visible_piles[id as usize] = new_from;
                    game.visible_piles[id_pile as usize] = new_to;
                    0
                }
                Pos::Deck => unreachable!(),
            };

            // unlocking hidden cards
            if is_empty(&game.visible_piles[id as usize]) {
                game.visible_piles[id as usize] = create_pile(pop_hidden(game, id));
                reward += 5;
            }

            return reward;
        }
    }
}

pub fn print_card(card: CardType, end: &str) {
    let (u, v) = split_card(card);
    if u < N_RANKS {
        print!(
            "{}{}{}",
            NUMBERS[u as usize].on_white(),
            SYMBOLS[v as usize].on_white().color(COLOR[v as usize]),
            end
        );
    } else {
        print!("  {}", end);
    }
}

pub fn display(game: &Solitaire) {
    print!("Deck 0: ");

    for card in &game.deck[game.draw_cur.saturating_sub(3) as usize..game.draw_cur as usize] {
        print_card(*card, " ");
    }

    print!("\t\t");

    for i in 0u8..4u8 {
        print!("{}.", i + 1);
        let card = game.final_stack[i as usize];
        let card = if card == 0 {
            FAKE_CARD
        } else {
            make_card(card - 1, i)
        };
        print_card(card, " ");
    }
    println!();

    for i in 0..N_PILES {
        print!("{}\t", i + 5)
    }
    println!();

    let mut i = 0; // skip the hidden layer

    loop {
        let mut is_print = false;
        for j in 0..N_PILES {
            let ref cur_pile = game.visible_piles[j as usize];

            let n_hidden = game.n_hidden[j as usize];
            let n_visible = pile_length(cur_pile);
            if n_hidden > i {
                print!("**\t");
                is_print = true;
            } else if i < n_hidden + n_visible {
                print_card(get_card_top(cur_pile, i - n_hidden), "\t");
                is_print = true;
            } else {
                print!("  \t");
            }
        }
        println!();
        i += 1;
        if !is_print {
            break;
        }
    }
}

#[cfg(test)]
mod tests {
    // Note this useful idiom: importing names from outer (for mod tests) scope.
    use super::*;

    fn assert_moves(mut a: Vec<MoveType>, mut b: Vec<MoveType>) {
        b.push((Pos::Deck, Pos::Deck));
        a.sort();
        b.sort();

        assert_eq!(a, b);
    }

    #[test]
    fn test_game() {
        let cards = [
            30, 33, 41, 13, 28, 11, 16, 36, 9, 39, 17, 37, 21, 10, 1, 38, 0, 50, 14, 31, 20, 46,
            18, 32, 7, 49, 3, 19, 8, 44, 4, 51, 2, 15, 40, 35, 43, 22, 12, 42, 26, 23, 24, 5, 6,
            48, 27, 45, 47, 29, 34, 25,
        ];
        let mut game = generate_game(&cards, 3);
        assert_moves(
            gen_moves(&game),
            vec![(Pos::Pile(0), Pos::Pile(4)), (Pos::Pile(5), Pos::Stack(3))],
        );

        assert_eq!(do_move(&mut game, &(Pos::Pile(0), Pos::Pile(4))), 5);

        assert_moves(
            gen_moves(&game),
            vec![(Pos::Pile(4), Pos::Pile(0)), (Pos::Pile(5), Pos::Stack(3))],
        );

        assert_eq!(do_move(&mut game, &(Pos::Pile(4), Pos::Pile(0))), 5);
        assert_moves(
            gen_moves(&game),
            vec![(Pos::Pile(2), Pos::Pile(4)), (Pos::Pile(5), Pos::Stack(3))],
        );

        assert_eq!(do_move(&mut game, &(Pos::Pile(2), Pos::Pile(4))), 5);

        assert_moves(
            gen_moves(&game),
            vec![
                (Pos::Pile(2), Pos::Pile(0)),
                (Pos::Pile(4), Pos::Pile(2)),
                (Pos::Pile(5), Pos::Stack(3)),
            ],
        );

        assert_eq!(do_move(&mut game, &(Pos::Pile(2), Pos::Pile(0))), 5);

        assert_moves(
            gen_moves(&game),
            vec![(Pos::Pile(4), Pos::Pile(0)), (Pos::Pile(5), Pos::Stack(3))],
        );

        assert_eq!(do_move(&mut game, &(Pos::Pile(4), Pos::Pile(0))), 5);

        assert_moves(
            gen_moves(&game),
            vec![(Pos::Pile(3), Pos::Pile(4)), (Pos::Pile(5), Pos::Stack(3))],
        );

        assert_eq!(do_move(&mut game, &(Pos::Pile(5), Pos::Stack(3))), 20);
    }
}
