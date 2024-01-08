use colored::{Color, Colorize};
use rand::prelude::*;

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Pos {
    Deck(u8),
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
const N_FULL_DECK: usize = (N_CARDS - N_HIDDEN_CARDS - N_PILES) as usize;

#[derive(Debug)]
pub struct Pile {
    start_rank: u8,
    end: CardType,
    suit: u16,
}

impl Pile {
    const fn from_card(c: CardType) -> Pile {
        return Pile {
            start_rank: split_card(c).0,
            end: c,
            suit: (c & 1) as u16,
        };
    }

    const fn is_empty(self: &Pile) -> bool {
        return self.start_rank < split_card(self.end).0;
    }

    const fn suit_type(self: &Pile) -> u8 {
        let (rank, suit) = split_card(self.end);
        return (rank & 1) ^ (suit / 2);
    }

    const fn len(self: &Pile) -> u8 {
        return self.start_rank - split_card(self.end).0 + 1;
    }

    const fn bottom(self: &Pile, pos: u8) -> u8 {
        return (((self.end + pos * N_SUITS) & !1) ^ ((pos & 1) * 2))
            | (((self.suit >> pos) & 1) as CardType);
    }

    const fn top(self: &Pile, pos: u8) -> u8 {
        let len = self.len();
        assert!(pos < len);
        return self.bottom(len - pos - 1);
    }

    const fn pop(self: &Pile, step: u8) -> Pile {
        assert!(self.len() >= step);

        return Pile {
            start_rank: self.start_rank,
            end: self.bottom(step),
            suit: self.suit >> step,
        };
    }

    const fn push(self: &Pile, c: CardType) -> Pile {
        assert!(fit_after(self.end, c));

        return Pile {
            start_rank: self.start_rank,
            end: c,
            suit: (self.suit << 1) | ((c & 1) as u16),
        };
    }

    const fn movable_to(self: &Pile, to: &Pile) -> bool {
        let start_rank = self.start_rank;
        let (end_rank, _) = split_card(self.end);
        let (dst_rank, _) = split_card(to.end);
        return (self.suit_type() == to.suit_type() || dst_rank >= N_RANKS)
            && end_rank < dst_rank
            && dst_rank <= start_rank + 1;
    }

    const fn move_to(self: &Pile, to: &Pile) -> (Pile, Pile) {
        assert!(self.movable_to(to));
        let (src_rank, _) = split_card(self.end);
        let (dst_rank, _) = split_card(to.end);

        let n_moved = dst_rank - src_rank;

        return (
            self.pop(n_moved),
            Pile {
                start_rank: to.start_rank,
                end: self.end,
                suit: (to.suit << n_moved) | (self.suit & ((1 << n_moved) - 1)),
            },
        );
    }
}

#[derive(Debug)]
pub struct Deck {
    deck: [u8; N_FULL_DECK],
    n_deck: u8,
    draw_step: u8,
    draw_next: u8, // start position of next pile
    draw_cur: u8,  // size of the previous pile
}

fn optional_split_last<T>(
    slice: &[T],
    start: usize,
    end: usize,
) -> (
    impl Iterator<Item = (usize, &T)> + Clone,
    Option<(usize, &T)>,
) {
    return (
        slice[..end.saturating_sub(1)]
            .iter()
            .enumerate()
            .skip(start),
        slice[start..end].last().map(|x| (end - 1, x)),
    );
}

impl Deck {
    pub fn new(deck: &[CardType], draw_step: u8) -> Deck {
        assert!(deck.len() == N_FULL_DECK);
        let draw_step = std::cmp::min(N_FULL_DECK as u8, draw_step);

        return Deck {
            deck: deck.try_into().unwrap(),
            n_deck: deck.len() as u8,
            draw_step,
            draw_next: draw_step,
            draw_cur: draw_step,
        };
    }

    pub fn iters(
        self: &Deck,
    ) -> (
        impl Iterator<Item = (usize, &CardType)>,
        impl Iterator<Item = (usize, &CardType)>,
    ) {
        let n_deck = self.n_deck as usize;
        let draw_cur = self.draw_cur as usize;
        let draw_next = self.draw_next as usize;
        let draw_step = self.draw_step as usize;
        let (head, cur) = optional_split_last(&self.deck, 0, draw_cur);
        let (tail, last) = optional_split_last(&self.deck, draw_next, n_deck);

        // non redealt

        let offset = draw_step - 1 - (draw_cur % draw_step);

        // filter out if repeat :)
        let offset = if offset == draw_step - 1 {
            n_deck
        } else {
            offset
        };

        return (
            cur.into_iter()
                .chain(tail.clone().skip(draw_step - 1).step_by(draw_step))
                .chain(last.into_iter()),
            head.skip(draw_step - 1)
                .step_by(draw_step)
                .chain(tail.skip(offset).step_by(draw_step)),
        );
    }
}

#[derive(Debug)]
pub struct Solitaire {
    hidden_piles: [CardType; N_HIDDEN_CARDS as usize],
    n_hidden: [u8; N_PILES as usize],

    // start card ends card and flags
    visible_piles: [Pile; N_PILES as usize],
    final_stack: [u8; 4],
    deck: Deck,
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

    let visible_piles: [Pile; N_PILES as usize] = visible_cards.map(|c| Pile::from_card(c));

    let deck: Deck = Deck::new(&cards[(N_HIDDEN_CARDS + N_PILES) as usize..], draw_step);

    let final_stack: [u8; 4] = [0u8; 4];

    return Solitaire {
        hidden_piles,
        n_hidden,
        visible_piles,
        final_stack,
        deck,
    };
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

pub fn gen_moves_(game: &Solitaire, moves: &mut Vec<MoveType>) {
    // let mut moves = vec![(Pos::Deck, Pos::Deck)];
    moves.clear();

    // src = src.Deck
    {
        let (current_deal, next_deal) = game.deck.iters();
        for (pos, card) in current_deal.chain(next_deal) {
            let (rank, suit) = split_card(*card);
            if rank < N_RANKS && game.final_stack[suit as usize] == rank {
                moves.push((Pos::Deck(pos as u8), Pos::Stack(suit)));
            }
            for (id, pile) in game.visible_piles.iter().enumerate() {
                let dst_card = pile.end;
                if fit_after(dst_card, *card) {
                    moves.push((Pos::Deck(pos as u8), Pos::Pile(id as u8)));
                }
            }
        }
    }

    // move to deck
    for (id, pile) in game.visible_piles.iter().enumerate() {
        let dst_card = pile.end;

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
            if id != other_id && other_pile.movable_to(pile) {
                moves.push((Pos::Pile(other_id as u8), Pos::Pile(id as u8)));
            }
        }
    }
}

pub fn peek_deck(d: &Deck, id: u8) -> CardType {
    assert!(d.draw_cur <= d.draw_next && id < d.draw_cur || id >= d.draw_next && id < d.n_deck);
    return d.deck[id as usize];
}

pub fn draw_deck(d: &mut Deck, id: u8) {
    assert!(d.draw_cur <= d.draw_next && id < d.draw_cur || id >= d.draw_next && id < d.n_deck);

    let step = if id < d.draw_cur {
        let step = d.draw_cur - id;
        if d.draw_cur != d.draw_next {
            // moving stuff
            d.deck.copy_within(
                (d.draw_cur - step) as usize..(d.draw_cur as usize),
                (d.draw_next - step) as usize,
            );
        }
        step.wrapping_neg()
    } else {
        let step = id - d.draw_next;

        d.deck.copy_within(
            (d.draw_next) as usize..(d.draw_next + step) as usize,
            d.draw_cur as usize,
        );
        step
    };

    d.draw_cur = d.draw_cur.wrapping_add(step);
    d.draw_next = d.draw_next.wrapping_add(step.wrapping_add(1));
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

    match src {
        &Pos::Deck(id) => {
            let deck_card = peek_deck(&game.deck, id);
            draw_deck(&mut game.deck, id);

            // not dealing with redealt yet :)
            match dst {
                Pos::Deck(_) => unreachable!(),
                Pos::Stack(_) => return 20,
                &Pos::Pile(id_pile) => {
                    let ref mut pile = game.visible_piles[id_pile as usize];
                    *pile = pile.push(deck_card);
                    return 5;
                }
            }
        }
        &Pos::Stack(id) => {
            match dst {
                &Pos::Pile(id_pile) => {
                    let card: u8 = make_card(game.final_stack[id as usize], id);
                    let ref mut pile = game.visible_piles[id_pile as usize];
                    *pile = pile.push(card);
                    return -15;
                }
                _ => unreachable!(),
            };
        }
        &Pos::Pile(id) => {
            let mut reward = match dst {
                Pos::Stack(_) => {
                    let ref mut pile = game.visible_piles[id as usize];
                    *pile = pile.pop(1);
                    15
                }
                &Pos::Pile(id_pile) => {
                    let (new_from, new_to) = game.visible_piles[id as usize]
                        .move_to(&game.visible_piles[id_pile as usize]);
                    game.visible_piles[id as usize] = new_from;
                    game.visible_piles[id_pile as usize] = new_to;
                    0
                }
                Pos::Deck(_) => unreachable!(),
            };

            // unlocking hidden cards
            if game.visible_piles[id as usize].is_empty() {
                game.visible_piles[id as usize] = Pile::from_card(pop_hidden(game, id));
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
            let n_visible = cur_pile.len();
            if n_hidden > i {
                print!("**\t");
                is_print = true;
            } else if i < n_hidden + n_visible {
                print_card(cur_pile.top(i - n_hidden), "\t");
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
            vec![
                (Pos::Deck(20), Pos::Pile(4)),
                (Pos::Pile(0), Pos::Pile(4)),
                (Pos::Pile(5), Pos::Stack(3)),
            ],
        );

        assert_eq!(do_move(&mut game, &(Pos::Pile(0), Pos::Pile(4))), 5);

        assert_moves(
            gen_moves(&game),
            vec![
                (Pos::Deck(17), Pos::Pile(0)),
                (Pos::Pile(4), Pos::Pile(0)),
                (Pos::Pile(5), Pos::Stack(3)),
            ],
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

        assert_eq!(do_move(&mut game, &(Pos::Pile(3), Pos::Pile(4))), 5);

        assert_moves(
            gen_moves(&game),
            vec![(Pos::Deck(2), Pos::Pile(3)), (Pos::Pile(5), Pos::Stack(3))],
        );
    }
}
