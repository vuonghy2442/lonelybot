use crate::{
    engine::{Move, Solitaire},
    standard::{Pos, StandardHistoryVec, StandardSolitaire, DRAW_NEXT},
};

impl From<&Solitaire> for StandardSolitaire {
    fn from(game: &Solitaire) -> Self {
        StandardSolitaire {
            hidden_piles: game.get_hidden().to_piles(),
            final_stack: *game.get_stack(),
            deck: game.get_deck().clone(),
            piles: game.get_visible_piles(),
        }
    }
}

// making it never panic :(
// this will convert and execute the move
pub fn convert_move(game: &StandardSolitaire, m: &Move, move_seq: &mut StandardHistoryVec) {
    match m {
        Move::DeckPile(c) => {
            let cnt = game.find_deck_card(c).unwrap();
            for _ in 0..cnt {
                move_seq.push(DRAW_NEXT);
            }
            // assert_eq!(game.get_deck().peek_last(), Some(c));

            let pile = game.find_free_pile(c).unwrap();
            move_seq.push((Pos::Deck, Pos::Pile(pile), *c));
        }
        Move::DeckStack(c) => {
            let cnt = game.find_deck_card(c).unwrap();
            for _ in 0..cnt {
                move_seq.push(DRAW_NEXT);
            }
            // assert_eq!(game.get_deck().peek_last(), Some(c));

            assert!(c.rank() == game.final_stack[c.suit() as usize]);
            move_seq.push((Pos::Deck, Pos::Stack(c.suit()), *c));
        }
        Move::StackPile(c) => {
            // assert!(c.rank() + 1 == game.final_stack[c.suit() as usize]);
            let pile = game.find_free_pile(c).unwrap();
            move_seq.push((Pos::Stack(c.suit()), Pos::Pile(pile), *c));
        }
        Move::Reveal(c) => {
            let pile_from = game.find_top_card(c).unwrap();
            let pile_to = game.find_free_pile(c).unwrap();

            assert!(pile_to != pile_from);

            move_seq.push((Pos::Pile(pile_from), Pos::Pile(pile_to), *c));
        }
        Move::PileStack(c) => {
            assert!(c.rank() == game.final_stack[c.suit() as usize]);
            let (pile, pos) = game.find_card(c).unwrap();
            if pos + 1 < game.piles[pile as usize].len() {
                let move_card = game.piles[pile as usize][pos + 1];
                let pile_other = game.find_free_pile(&move_card).unwrap();

                // assert!(pile != pile_other);

                move_seq.push((Pos::Pile(pile), Pos::Pile(pile_other), move_card));
            }
            move_seq.push((Pos::Pile(pile), Pos::Stack(c.suit()), *c));
        }
    }
}

// this will convert and execute the moves
pub fn convert_moves(game: &mut StandardSolitaire, m: &[Move]) -> StandardHistoryVec {
    let mut move_seq = StandardHistoryVec::new();
    for mm in m {
        let start = move_seq.len();
        convert_move(game, mm, &mut move_seq);

        for m in move_seq[start..].iter() {
            assert!(game.do_move(m));
        }
    }
    move_seq
}

#[cfg(test)]
mod tests {

    use crate::{shuffler::default_shuffle, solver::solve_game};

    // Note this useful idiom: importing names from outer (for mod tests) scope.
    use super::*;

    fn do_test_convert(seed: u64) {
        const DRAW_STEP: u8 = 3;
        let cards = default_shuffle(seed);
        let mut game = StandardSolitaire::new(&cards, DRAW_STEP);

        let res = {
            let mut game_1: Solitaire = From::from(&game);
            let mut game_2: Solitaire = Solitaire::new(&cards, DRAW_STEP);

            let res1 = solve_game(&mut game_1);
            let res2 = solve_game(&mut game_2);

            assert_eq!(res1, res2);
            res1
        };

        let Some(moves) = res.1 else {
            return;
        };

        let mut his = StandardHistoryVec::new();

        let mut game_x: Solitaire = From::from(&game);
        for pos in 0..moves.len() {
            his.clear();
            convert_move(&mut game, &moves[pos], &mut his);
            for m in &his {
                assert!(game.do_move(m));
            }

            game_x.do_move(&moves[pos]);
            let mut game_c: Solitaire = From::from(&game);
            assert!(game_c.is_valid());
            assert!(game_x.equivalent_to(&game_c));

            let mut game_cc: StandardSolitaire = From::from(&game_c);

            // let res_c = solve_game(&mut game_c);
            // assert_eq!(res_c.0, res.0);
            for m in moves[pos + 1..].iter() {
                game_c.do_move(m);
            }
            convert_moves(&mut game_cc, &moves[pos + 1..]);
            assert!(game_c.is_win());
            assert!(game_cc.is_win());
        }
    }

    #[test]
    fn test_convert() {
        for seed in 12..20 {
            do_test_convert(seed);
        }
    }
}
