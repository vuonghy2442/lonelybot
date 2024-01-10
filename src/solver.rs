use crate::engine::{Encode, MoveType, Solitaire};
use std::collections::HashSet;

fn solve(g: &mut Solitaire, tp: &mut HashSet<Encode>, history: &mut Vec<MoveType>) -> bool {
    if g.is_win() {
        return true;
    }
    if !tp.insert(g.encode()) {
        return false;
    }

    let moves = g.gen_moves();
    for m in moves {
        let (_, undo) = g.do_move(&m);
        history.push(m);
        if solve(g, tp, history) {
            return true;
        }
        history.pop();
        g.undo_move(&m, &undo);
    }
    false
}

pub fn solve_game(g: &mut Solitaire) -> Option<Vec<MoveType>> {
    let mut tp = HashSet::<Encode>::new();
    let mut history = Vec::<MoveType>::new();
    let res = solve(g, &mut tp, &mut history);
    if res {
        Some(history)
    } else {
        None
    }
}
