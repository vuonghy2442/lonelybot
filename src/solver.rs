use crate::engine::{Encode, MoveType, Solitaire};
use std::collections::HashSet;

fn solve(
    g: &mut Solitaire,
    tp: &mut HashSet<Encode>,
    history: &mut Vec<MoveType>,
    move_list: &mut Vec<MoveType>,
) -> bool {
    if g.is_win() {
        return true;
    }
    if !tp.insert(g.encode()) {
        return false;
    }

    let start = move_list.len();
    g.gen_moves_(move_list);
    let end = move_list.len();

    for pos in start..end {
        let m = move_list[pos];
        let (_, undo) = g.do_move(&m);
        history.push(m);
        if solve(g, tp, history, move_list) {
            return true;
        }
        history.pop();
        g.undo_move(&m, &undo);
    }
    move_list.truncate(start);

    false
}

pub fn solve_game(g: &mut Solitaire) -> Option<Vec<MoveType>> {
    let mut tp = HashSet::<Encode>::new();
    let mut move_list = Vec::<MoveType>::new();
    let mut history = Vec::<MoveType>::new();

    let res = solve(g, &mut tp, &mut history, &mut move_list);

    println!(
        "Visited state {}, max depth cap {}",
        tp.len(),
        history.capacity()
    );
    if res {
        Some(history)
    } else {
        None
    }
}
