use std::collections::HashSet;

use crate::engine::{Encode, MoveType, Solitaire};

#[derive(Debug)]
pub struct SearchStats {
    total_visit: usize,
    tp_hit: usize,
    max_depth: usize,
}

impl SearchStats {
    pub const fn new() -> SearchStats {
        SearchStats {
            total_visit: 0,
            tp_hit: 0,
            max_depth: 0,
        }
    }
}

fn solve(
    g: &mut Solitaire,
    tp: &mut lru::LruCache<Encode, ()>,
    tp_hist: &mut HashSet<Encode>,
    history: &mut Vec<MoveType>,
    move_list: &mut Vec<MoveType>,
    stats: &mut SearchStats,
) -> bool {
    stats.max_depth = std::cmp::max(stats.max_depth, history.len());
    stats.total_visit += 1;
    if g.is_win() {
        return true;
    }
    let encode = g.encode();
    if tp.put(encode, ()).is_some() || !tp_hist.insert(encode) {
        stats.tp_hit += 1;
        return false;
    }

    let start = move_list.len();
    g.gen_moves_(move_list);
    let end = move_list.len();

    for pos in start..end {
        let m = move_list[pos];
        let (_, undo) = g.do_move(&m);
        history.push(m);
        if solve(g, tp, tp_hist, history, move_list, stats) {
            return true;
        }
        history.pop();
        g.undo_move(&m, &undo);
    }
    move_list.truncate(start);
    tp_hist.remove(&encode);

    false
}

pub fn solve_game(g: &mut Solitaire) -> (Option<Vec<MoveType>>, SearchStats) {
    let mut tp_hist = HashSet::<Encode>::new();
    let mut tp = lru::LruCache::<Encode, ()>::new(std::num::NonZeroUsize::new(1024*1024*16).unwrap());
    let mut move_list = Vec::<MoveType>::new();
    let mut history = Vec::<MoveType>::new();
    let mut stats = SearchStats::new();
    let res = solve(
        g,
        &mut tp,
        &mut tp_hist,
        &mut history,
        &mut move_list,
        &mut stats,
    );

    (if res { Some(history) } else { None }, stats)
}
