use crate::card::{Card, N_RANKS};

#[derive(Debug, Clone, Copy)]
pub struct Pile {
    start_rank: u8,
    end: Card,
    suit: u16,
}

impl Pile {
    pub const fn from_card(c: Card) -> Pile {
        return Pile {
            start_rank: c.rank(),
            end: c,
            suit: (c.suit() & 1) as u16 + 2, // this is just for easier encoding
        };
    }

    pub const fn is_empty(self: &Pile) -> bool {
        return self.start_rank < self.end.rank();
    }

    pub const fn suit_type(self: &Pile) -> u8 {
        let (rank, suit) = self.end.split();
        // TODO: is there any better way to handle this
        // This cause by encoding different suit for the empty stack (maybe not using fake card?)
        return ((rank >= N_RANKS) as u8) | (rank & 1) ^ (suit / 2);
    }

    pub const fn len(self: &Pile) -> u8 {
        return self.start_rank - self.end.rank() + 1;
    }

    pub const fn bottom(self: &Pile, pos: u8) -> Card {
        let (rank, suit) = self.end.split();
        return Card::new(
            rank + pos,
            (((suit / 2) ^ (pos & 1)) * 2) | (((self.suit >> pos) & 1) as u8),
        );
    }

    pub const fn end(self: &Pile) -> Card {
        return self.end;
    }

    pub const fn top(self: &Pile, pos: u8) -> Card {
        let len = self.len();
        debug_assert!(pos < len);
        return self.bottom(len - pos - 1);
    }

    pub const fn pop_(self: &Pile, step: u8) -> Pile {
        debug_assert!(self.len() >= step);

        return Pile {
            start_rank: self.start_rank,
            end: self.bottom(step),
            suit: self.suit >> step,
        };
    }

    pub fn pop(self: &mut Pile, step: u8) {
        *self = self.pop_(step);
    }

    pub const fn push_(self: &Pile, c: Card) -> Pile {
        debug_assert!(self.end.go_before(&c));

        return Pile {
            start_rank: self.start_rank,
            end: c,
            suit: (self.suit << 1) | ((c.suit() & 1) as u16),
        };
    }

    pub fn push(self: &mut Pile, c: Card) {
        *self = self.push_(c);
    }

    pub const fn movable_to(self: &Pile, to: &Pile) -> bool {
        let start_rank = self.start_rank;
        let end_rank = self.end.rank();
        let dst_rank = to.end.rank();
        return (self.suit_type() == to.suit_type() || dst_rank >= N_RANKS)
            && end_rank < dst_rank
            && dst_rank <= start_rank + 1;
    }

    pub const fn move_to_(self: &Pile, to: &Pile) -> (Pile, Pile) {
        debug_assert!(self.movable_to(to));
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

    pub const fn encode(self: &Pile) -> u16 {
        // the encoding is use 15 bits encoding the suit and the cards
        // the format is like this
        // 00001(marking start)..(suit max 13 bit)..1(marking end)000|<suit type>
        let end_rank = self.end.rank();
        let suit = ((self.suit << 1) | 1) << end_rank;
        return (suit << 1) | (self.suit_type() as u16);
    }
}
