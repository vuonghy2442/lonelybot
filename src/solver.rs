use crate::engine::{Encode, Solitaire};
use std::collections::HashSet;

fn solve(g: &mut Solitaire, tp: &mut HashSet<Encode>) -> bool {
    if g.is_win() {
        return true;
    }
    if !tp.insert(g.encode()) {
        return false;
    }

    let moves = g.gen_moves();
    for m in moves {
        let (_, undo) = g.do_move(&m);
        if solve(g, tp) {
            return true;
        }
        g.undo_move(&m, &undo);
    }
    false
}

pub fn solve_game(g: &mut Solitaire) -> bool {
    let mut tp = HashSet::<Encode>::new();
    return solve(g, &mut tp);
}
