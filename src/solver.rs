use quick_cache::sync::Cache;
use std::collections::HashSet;

use crate::engine::{Encode, MoveType, Solitaire};

#[derive(Debug)]
pub struct SearchStats {
    total_visit: usize,
    tp_hit: usize,
    max_depth: usize,
    cur_move: Vec<u8>,
    total_move: Vec<u8>,
}

impl SearchStats {
    pub const fn new() -> SearchStats {
        SearchStats {
            total_visit: 0,
            tp_hit: 0,
            max_depth: 0,
            cur_move: Vec::new(),
            total_move: Vec::new(),
        }
    }
}

fn solve(
    g: &mut Solitaire,
    tp: &mut Cache<Encode, ()>,
    tp_hist: &mut HashSet<Encode>,
    history: &mut Vec<MoveType>,
    move_list: &mut Vec<MoveType>,
    stats: &mut SearchStats,
) -> bool {
    stats.max_depth = std::cmp::max(stats.max_depth, history.len());
    stats.total_visit += 1;

    // if history.len() + (g.min_move() as usize) > 70 {
    //     return false;
    // }

    if g.is_win() {
        return true;
    }
    let encode = g.encode();
    if tp.get(&encode).is_some() || !tp_hist.insert(encode) {
        stats.tp_hit += 1;
        return false;
    } else {
        tp.insert(encode, ());
    }

    let start = move_list.len();
    g.gen_moves_::<true>(move_list);

    let end = move_list.len();
    stats.total_move.push((end - start) as u8);
    stats.cur_move.push(0);

    for pos in start..end {
        let m = move_list[pos];
        let (_, undo) = g.do_move(&m);
        history.push(m);
        if solve(g, tp, tp_hist, history, move_list, stats) {
            return true;
        }
        history.pop();
        g.undo_move(&m, &undo);
        *stats.cur_move.last_mut().unwrap() = (pos - start) as u8;
    }
    stats.total_move.pop();
    stats.cur_move.pop();
    move_list.truncate(start);
    tp_hist.remove(&encode);

    false
}

pub fn solve_game(g: &mut Solitaire, stats: &mut SearchStats) -> Option<Vec<MoveType>> {
    let mut tp_hist = HashSet::<Encode>::new();
    let mut tp = Cache::<Encode, ()>::new(1024 * 1024 * 32);
    let mut move_list = Vec::<MoveType>::new();
    let mut history = Vec::<MoveType>::new();
    let res = solve(
        g,
        &mut tp,
        &mut tp_hist,
        &mut history,
        &mut move_list,
        stats,
    );

    if res {
        Some(history)
    } else {
        None
    }
}
