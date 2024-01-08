use core::fmt;

use colored::{Color, Colorize};
use rand::prelude::*;

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Pos {
    Deck(u8),
    Stack(u8),
    Pile(u8),
}

#[derive(Debug, Clone, Copy)]
pub struct Card(u8);

pub type MoveType = (Pos, Pos);

const N_SUITS: u8 = 4;
const N_RANKS: u8 = 13;
const N_CARDS: u8 = N_SUITS * N_RANKS;

const COLOR: [Color; N_SUITS as usize] = [Color::Red, Color::Red, Color::Black, Color::Black];

const SYMBOLS: [&'static str; N_SUITS as usize] = ["♥", "♦", "♣", "♠"];
const NUMBERS: [&'static str; N_RANKS as usize] = [
    "A", "2", "3", "4", "5", "6", "7", "8", "9", "10", "J", "Q", "K",
];

type CardDeck = [Card; N_CARDS as usize];

impl fmt::Display for Card {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let (u, v) = self.split();
        return if u < N_RANKS {
            write!(
                f,
                "{}{}",
                NUMBERS[u as usize].on_white(),
                SYMBOLS[v as usize].on_white().color(COLOR[v as usize])
            )
        } else {
            write!(f, "  ")
        };
    }
}

impl Card {
    const FAKE: Card = Card::new(N_RANKS, 0);

    pub const fn new(rank: u8, suit: u8) -> Card {
        assert!(rank <= N_RANKS && suit < N_SUITS);
        return Card {
            0: rank * N_SUITS + suit,
        };
    }

    pub const fn rank(self: &Card) -> u8 {
        return self.0 / N_SUITS;
    }

    pub const fn suit(self: &Card) -> u8 {
        return self.0 % N_SUITS;
    }

    pub const fn split(self: &Card) -> (u8, u8) {
        return (self.rank(), self.suit());
    }

    const fn go_before(self: &Card, other: &Card) -> bool {
        let card_a = self.split();
        let card_b = other.split();
        return card_a.0 == card_b.0 + 1 && (card_a.1 ^ card_b.1 >= 2 || card_a.0 >= N_RANKS);
    }
}

const N_PILES: u8 = 7;
const N_HIDDEN_CARDS: u8 = N_PILES * (N_PILES - 1) / 2;
const N_FULL_DECK: usize = (N_CARDS - N_HIDDEN_CARDS - N_PILES) as usize;

#[derive(Debug)]
pub struct Pile {
    start_rank: u8,
    end: Card,
    suit: u16,
}

impl Pile {
    const fn from_card(c: Card) -> Pile {
        return Pile {
            start_rank: c.rank(),
            end: c,
            suit: (c.suit() & 1) as u16,
        };
    }

    const fn is_empty(self: &Pile) -> bool {
        return self.start_rank < self.end.rank();
    }

    const fn suit_type(self: &Pile) -> u8 {
        let (rank, suit) = self.end.split();
        return (rank & 1) ^ (suit / 2);
    }

    const fn len(self: &Pile) -> u8 {
        return self.start_rank - self.end.rank() + 1;
    }

    const fn bottom(self: &Pile, pos: u8) -> Card {
        let (rank, suit) = self.end.split();
        return Card::new(
            rank + pos,
            (((suit / 2) ^ (pos & 1)) * 2) | (((self.suit >> pos) & 1) as u8),
        );
    }

    const fn top(self: &Pile, pos: u8) -> Card {
        let len = self.len();
        assert!(pos < len);
        return self.bottom(len - pos - 1);
    }

    const fn pop_(self: &Pile, step: u8) -> Pile {
        assert!(self.len() >= step);

        return Pile {
            start_rank: self.start_rank,
            end: self.bottom(step),
            suit: self.suit >> step,
        };
    }

    fn pop(self: &mut Pile, step: u8) {
        *self = self.pop_(step);
    }

    const fn push_(self: &Pile, c: Card) -> Pile {
        assert!(self.end.go_before(&c));

        return Pile {
            start_rank: self.start_rank,
            end: c,
            suit: (self.suit << 1) | ((c.suit() & 1) as u16),
        };
    }

    fn push(self: &mut Pile, c: Card) {
        *self = self.push_(c);
    }

    const fn movable_to(self: &Pile, to: &Pile) -> bool {
        let start_rank = self.start_rank;
        let end_rank = self.end.rank();
        let dst_rank = to.end.rank();
        return (self.suit_type() == to.suit_type() || dst_rank >= N_RANKS)
            && end_rank < dst_rank
            && dst_rank <= start_rank + 1;
    }

    const fn move_to_(self: &Pile, to: &Pile) -> (Pile, Pile) {
        assert!(self.movable_to(to));
        let src_rank = self.end.rank();
        let dst_rank = to.end.rank();

        let n_moved = dst_rank - src_rank;

        return (
            self.pop_(n_moved),
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
    deck: [Card; N_FULL_DECK],
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

enum Drawable {
    None,
    Current,
    Next,
}

impl Deck {
    pub fn new(deck: &[Card], draw_step: u8) -> Deck {
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
        impl Iterator<Item = (usize, &Card)>,
        impl Iterator<Item = (usize, &Card)>,
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

    pub fn iter_all(self: &Deck) -> impl Iterator<Item = (u8, &Card, Drawable)> {
        let head = self.deck[..self.draw_cur as usize]
            .iter()
            .enumerate()
            .map(|x| {
                let pos = x.0 as u8;
                (
                    pos,
                    x.1,
                    if pos + 1 == self.draw_cur {
                        Drawable::Current
                    } else if (pos + 1) % self.draw_step == 0 {
                        Drawable::Next
                    } else {
                        Drawable::None
                    },
                )
            });

        let tail = self.deck[self.draw_next as usize..self.n_deck as usize]
            .iter()
            .enumerate()
            .map(|x| {
                let pos = x.0 as u8;
                (
                    self.draw_next + pos,
                    x.1,
                    if pos + 1 == self.n_deck - self.draw_next || (pos + 1) % self.draw_step == 0 {
                        Drawable::Current
                    } else if (self.draw_cur + pos + 1) % self.draw_step == 0 {
                        Drawable::Next
                    } else {
                        Drawable::None
                    },
                )
            });
        return head.chain(tail);
    }

    pub fn peek(self: &Deck, id: u8) -> Card {
        assert!(
            self.draw_cur <= self.draw_next && id < self.draw_cur
                || id >= self.draw_next && id < self.n_deck
        );
        return self.deck[id as usize];
    }

    pub fn draw(self: &mut Deck, id: u8) {
        assert!(
            self.draw_cur <= self.draw_next && id < self.draw_cur
                || id >= self.draw_next && id < self.n_deck
        );

        let step = if id < self.draw_cur {
            let step = self.draw_cur - id;
            if self.draw_cur != self.draw_next {
                // moving stuff
                self.deck.copy_within(
                    (self.draw_cur - step) as usize..(self.draw_cur as usize),
                    (self.draw_next - step) as usize,
                );
            }
            step.wrapping_neg()
        } else {
            let step = id - self.draw_next;

            self.deck.copy_within(
                (self.draw_next) as usize..(self.draw_next + step) as usize,
                self.draw_cur as usize,
            );
            step
        };

        self.draw_cur = self.draw_cur.wrapping_add(step);
        self.draw_next = self.draw_next.wrapping_add(step.wrapping_add(1));
    }
}

#[derive(Debug)]
pub struct Solitaire {
    hidden_piles: [Card; N_HIDDEN_CARDS as usize],
    n_hidden: [u8; N_PILES as usize],

    // start card ends card and flags
    visible_piles: [Pile; N_PILES as usize],
    final_stack: [u8; 4],
    deck: Deck,
}

pub fn generate_shuffled_deck(seed: u64) -> CardDeck {
    let mut rng = StdRng::seed_from_u64(seed);
    let mut cards: [Card; N_CARDS as usize] =
        core::array::from_fn(|i| Card::new(i as u8 / N_SUITS, i as u8 % N_SUITS));
    cards.shuffle(&mut rng);
    return cards;
}

impl Solitaire {
    pub fn new(cards: &CardDeck, draw_step: u8) -> Solitaire {
        let hidden_piles: [Card; N_HIDDEN_CARDS as usize] =
            cards[0..N_HIDDEN_CARDS as usize].try_into().unwrap();
        let n_hidden: [u8; N_PILES as usize] = core::array::from_fn(|i| i as u8);

        let visible_cards: &[Card; N_PILES as usize] = cards
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

    fn push_pile(self: &mut Solitaire, id: u8, card: Card) {
        self.visible_piles[id as usize].push(card);
    }

    fn pop_pile(self: &mut Solitaire, id: u8, step: u8) {
        self.visible_piles[id as usize].pop(step);
    }

    fn move_pile(self: &mut Solitaire, from: u8, to: u8) {
        let (from, to) = (from as usize, to as usize);
        let (new_from, new_to) = self.visible_piles[from].move_to_(&self.visible_piles[to]);
        self.visible_piles[from] = new_from;
        self.visible_piles[to] = new_to;
    }

    fn pop_hidden(self: &mut Solitaire, pos: u8) -> Card {
        let ref mut n_hid = self.n_hidden[pos as usize];
        if *n_hid == 0 {
            return Card::FAKE;
        } else {
            *n_hid -= 1;
            return self.hidden_piles[(pos * (pos - 1) / 2 + *n_hid) as usize];
        }
    }

    pub fn gen_moves_(self: &Solitaire, moves: &mut Vec<MoveType>) {
        moves.clear();

        // src = src.Deck
        {
            let (current_deal, next_deal) = self.deck.iters();
            for (pos, card) in current_deal.chain(next_deal) {
                let (rank, suit) = card.split();
                if rank < N_RANKS && self.final_stack[suit as usize] == rank {
                    moves.push((Pos::Deck(pos as u8), Pos::Stack(suit)));
                }
                for (id, pile) in self.visible_piles.iter().enumerate() {
                    let dst_card = pile.end;
                    if dst_card.go_before(card) {
                        moves.push((Pos::Deck(pos as u8), Pos::Pile(id as u8)));
                    }
                }
            }
        }

        // move to deck
        for (id, pile) in self.visible_piles.iter().enumerate() {
            let dst_card = pile.end;

            let (rank, suit) = dst_card.split();
            if self.final_stack[suit as usize] == rank {
                moves.push((Pos::Pile(id as u8), Pos::Stack(suit)));
            }

            for i in 1..2u8 {
                if rank > 0 && self.final_stack[(suit ^ i ^ 2) as usize] == rank {
                    moves.push((Pos::Stack(suit ^ i ^ 2), Pos::Pile(id as u8)));
                }
            }

            for (other_id, other_pile) in self.visible_piles.iter().enumerate() {
                if id != other_id && other_pile.movable_to(pile) {
                    moves.push((Pos::Pile(other_id as u8), Pos::Pile(id as u8)));
                }
            }
        }
    }

    pub fn gen_moves(self: &Solitaire) -> Vec<MoveType> {
        let mut moves = Vec::<MoveType>::new();
        self.gen_moves_(&mut moves);
        return moves;
    }

    // this is unsafe gotta check it is valid move before
    pub fn do_move(self: &mut Solitaire, m: &MoveType) -> i32 {
        let (src, dst) = m;
        // handling final stack
        if let &Pos::Stack(id) = src {
            assert!(self.final_stack[id as usize] > 0);
            self.final_stack[id as usize] -= 1;
        }
        if let &Pos::Stack(id) = dst {
            assert!(self.final_stack[id as usize] < N_RANKS);
            self.final_stack[id as usize] += 1;
        }
        // handling deck

        match src {
            &Pos::Deck(id) => {
                let deck_card = self.deck.peek(id);
                self.deck.draw(id);

                // not dealing with redealt yet :)
                match dst {
                    Pos::Deck(_) => unreachable!(),
                    Pos::Stack(_) => return 20,
                    &Pos::Pile(id_pile) => {
                        self.push_pile(id_pile, deck_card);
                        return 5;
                    }
                }
            }
            &Pos::Stack(id) => {
                match dst {
                    &Pos::Pile(id_pile) => {
                        let card: Card = Card::new(self.final_stack[id as usize], id);
                        self.push_pile(id_pile, card);
                        return -15;
                    }
                    _ => unreachable!(),
                };
            }
            &Pos::Pile(id) => {
                let mut reward = match dst {
                    Pos::Stack(_) => {
                        self.pop_pile(id, 1);
                        15
                    }
                    &Pos::Pile(id_pile) => {
                        self.move_pile(id, id_pile);
                        0
                    }
                    Pos::Deck(_) => unreachable!(),
                };

                // unlocking hidden cards
                if self.visible_piles[id as usize].is_empty() {
                    self.visible_piles[id as usize] = Pile::from_card(self.pop_hidden(id));
                    reward += 5;
                }

                return reward;
            }
        }
    }

    pub fn display(self: &Solitaire) {
        for (pos, card, t) in self.deck.iter_all() {
            let (c1, c2) = match t {
                Drawable::None => (' ', ' '),
                Drawable::Current => ('(', ')'),
                Drawable::Next => ('[', ']'),
            };
            print!(" {}.{}{}{}", pos, c1, card, c2);
        }
        println!();

        print!("\t\t");

        for i in 0u8..4u8 {
            let card = self.final_stack[i as usize];
            let card = if card == 0 {
                Card::FAKE
            } else {
                Card::new(card - 1, i)
            };
            print!("{}.{} ", i + 1, card);
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
                let ref cur_pile = self.visible_piles[j as usize];

                let n_hidden = self.n_hidden[j as usize];
                let n_visible = cur_pile.len();
                if n_hidden > i {
                    print!("**\t");
                    is_print = true;
                } else if i < n_hidden + n_visible {
                    print!("{}\t", cur_pile.top(i - n_hidden));
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
        ]
        .map(|i| Card { 0: i });
        let mut game = Solitaire::new(&cards, 3);
        assert_moves(
            game.gen_moves(),
            vec![
                (Pos::Deck(20), Pos::Pile(4)),
                (Pos::Pile(0), Pos::Pile(4)),
                (Pos::Pile(5), Pos::Stack(3)),
            ],
        );

        assert_eq!(game.do_move(&(Pos::Pile(0), Pos::Pile(4))), 5);

        assert_moves(
            game.gen_moves(),
            vec![
                (Pos::Deck(17), Pos::Pile(0)),
                (Pos::Pile(4), Pos::Pile(0)),
                (Pos::Pile(5), Pos::Stack(3)),
            ],
        );

        assert_eq!(game.do_move(&(Pos::Pile(4), Pos::Pile(0))), 5);
        assert_moves(
            game.gen_moves(),
            vec![(Pos::Pile(2), Pos::Pile(4)), (Pos::Pile(5), Pos::Stack(3))],
        );

        assert_eq!(game.do_move(&(Pos::Pile(2), Pos::Pile(4))), 5);

        assert_moves(
            game.gen_moves(),
            vec![
                (Pos::Pile(2), Pos::Pile(0)),
                (Pos::Pile(4), Pos::Pile(2)),
                (Pos::Pile(5), Pos::Stack(3)),
            ],
        );

        assert_eq!(game.do_move(&(Pos::Pile(2), Pos::Pile(0))), 5);

        assert_moves(
            game.gen_moves(),
            vec![(Pos::Pile(4), Pos::Pile(0)), (Pos::Pile(5), Pos::Stack(3))],
        );

        assert_eq!(game.do_move(&(Pos::Pile(4), Pos::Pile(0))), 5);

        assert_moves(
            game.gen_moves(),
            vec![(Pos::Pile(3), Pos::Pile(4)), (Pos::Pile(5), Pos::Stack(3))],
        );

        assert_eq!(game.do_move(&(Pos::Pile(3), Pos::Pile(4))), 5);

        assert_moves(
            game.gen_moves(),
            vec![(Pos::Deck(2), Pos::Pile(3)), (Pos::Pile(5), Pos::Stack(3))],
        );
    }
}
