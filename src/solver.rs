use std::collections::HashSet;

use crate::engine::{Encode, MoveType, Solitaire};

fn solve(
    g: &mut Solitaire,
    tp: &mut lru::LruCache<Encode, ()>,
    tp_hist: &mut HashSet<Encode>,
    history: &mut Vec<MoveType>,
    move_list: &mut Vec<MoveType>,
    total_visit: &mut usize,
) -> bool {
    *total_visit += 1;
    if g.is_win() {
        return true;
    }
    let encode = g.encode();
    if tp.put(encode, ()).is_some() || !tp_hist.insert(encode) {
        return false;
    }

    let start = move_list.len();
    g.gen_moves_(move_list);
    let end = move_list.len();

    for pos in start..end {
        let m = move_list[pos];
        let (_, undo) = g.do_move(&m);
        history.push(m);
        if solve(g, tp, tp_hist, history, move_list, total_visit) {
            return true;
        }
        history.pop();
        g.undo_move(&m, &undo);
    }
    move_list.truncate(start);
    tp_hist.remove(&encode);

    false
}

pub fn solve_game(g: &mut Solitaire) -> Option<Vec<MoveType>> {
    let mut tp_hist = HashSet::<Encode>::new();
    let mut tp = lru::LruCache::<Encode, ()>::new(std::num::NonZeroUsize::new(1024).unwrap());
    let mut move_list = Vec::<MoveType>::new();
    let mut history = Vec::<MoveType>::new();
    let mut total_visit: usize = 0;
    let res = solve(
        g,
        &mut tp,
        &mut tp_hist,
        &mut history,
        &mut move_list,
        &mut total_visit,
    );

    println!(
        "Visited state {}, max depth cap {}",
        total_visit,
        history.capacity()
    );
    if res {
        Some(history)
    } else {
        None
    }
}
