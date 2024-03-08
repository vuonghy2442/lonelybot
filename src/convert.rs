use crate::{
    deck::N_PILES,
    engine::{Move, Solitaire},
    standard::{HiddenVec, Pos, StandardHistoryVec, StandardSolitaire, DRAW_NEXT},
};

impl From<&Solitaire> for StandardSolitaire {
    fn from(game: &Solitaire) -> Self {
        let mut hidden_piles: [HiddenVec; N_PILES as usize] = Default::default();

        for i in 0..N_PILES {
            let n_hid = game.get_n_hidden()[i as usize] - 1;
            for j in 0..n_hid {
                hidden_piles[i as usize].push(game.get_hidden(i, j));
            }
        }

        StandardSolitaire {
            hidden_piles,
            final_stack: *game.get_stack(),
            deck: game.get_deck().clone(),
            piles: game.get_normal_piles(),
        }
    }
}

pub fn convert_move(game: &mut StandardSolitaire, m: &Move, move_seq: &mut StandardHistoryVec) {
    match m {
        Move::DeckPile(c) => {
            let cnt = game.find_deck_card(c).unwrap();
            for _ in 0..cnt {
                move_seq.push(DRAW_NEXT)
            }
            assert_eq!(game.draw_cur(), Some(*c));

            let pile = game.find_free_pile(c).unwrap();
            game.piles[pile as usize].push(*c);
            move_seq.push((Pos::Deck, Pos::Pile(pile), *c));
        }
        Move::DeckStack(c) => {
            let cnt = game.find_deck_card(c).unwrap();
            for _ in 0..cnt {
                move_seq.push(DRAW_NEXT)
            }
            assert_eq!(game.draw_cur(), Some(*c));

            assert!(c.rank() == game.final_stack[c.suit() as usize]);
            game.final_stack[c.suit() as usize] += 1;
            move_seq.push((Pos::Deck, Pos::Stack(c.suit()), *c));
        }
        Move::StackPile(c) => {
            assert!(c.rank() + 1 == game.final_stack[c.suit() as usize]);
            game.final_stack[c.suit() as usize] -= 1;

            let pile = game.find_free_pile(c).unwrap();
            game.piles[pile as usize].push(*c);
            move_seq.push((Pos::Stack(c.suit()), Pos::Pile(pile), *c));
        }
        Move::Reveal(c) => {
            let pile_from = game.find_top_card(c).unwrap();
            let pile_to = game.find_free_pile(c).unwrap();

            assert!(pile_to != pile_from);

            // lazy fix for the borrow checker :)
            game.piles[pile_to as usize].extend(game.piles[pile_from as usize].clone());
            game.piles[pile_from as usize].clear();

            if let Some(c) = game.hidden_piles[pile_from as usize].pop() {
                game.piles[pile_from as usize].push(c);
            }

            move_seq.push((Pos::Pile(pile_from), Pos::Pile(pile_to), *c));
        }
        Move::PileStack(c) => {
            assert!(c.rank() == game.final_stack[c.suit() as usize]);
            let (pile, pos) = game.find_card(c).unwrap();
            if pos + 1 != game.piles[pile as usize].len() {
                let pile_other = game
                    .find_free_pile(&game.piles[pile as usize][pos + 1])
                    .unwrap();

                assert!(pile != pile_other);

                game.piles[pile_other as usize]
                    .extend(game.piles[pile as usize].clone()[pos + 1..].iter().cloned());
                move_seq.push((Pos::Pile(pile), Pos::Pile(pile_other), *c));
            }
            game.piles[pile as usize].truncate(pos);

            if pos == 0 {
                if let Some(c) = game.hidden_piles[pile as usize].pop() {
                    game.piles[pile as usize].push(c);
                }
            }

            game.final_stack[c.suit() as usize] += 1;
            move_seq.push((Pos::Pile(pile), Pos::Stack(c.suit()), *c));
        }
    }
}

pub fn convert_moves(game: &mut StandardSolitaire, m: &[Move]) -> StandardHistoryVec {
    let mut move_seq = StandardHistoryVec::new();
    for mm in m {
        convert_move(game, mm, &mut move_seq);
    }
    move_seq
}
