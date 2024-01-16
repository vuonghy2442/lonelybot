use quick_cache::unsync::Cache;
use std::{collections::HashSet, fmt::Display, iter::zip, sync::Mutex};

use crate::engine::{Encode, MoveType, Solitaire};

#[derive(Debug)]
pub struct SearchStats {
    total_visit: usize,
    tp_hit: usize,
    max_depth: usize,
    cur_move: Vec<u8>,
    total_move: Vec<u8>,
}

#[derive(Debug)]
pub enum SearchResult {
    Terminated,
    Solved,
    Unsolvable,
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

impl Display for SearchStats {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "Total visit: {}\nTransposition hit: {}\nNon-cache state: {}\nMax depth search: {}\nCurrent progress:",
            self.total_visit, self.tp_hit, self.total_visit - self.tp_hit, self.max_depth,
        )?;

        for (cur, total) in zip(self.cur_move.iter(), self.total_move.iter()) {
            write!(f, " {}/{}", cur, total)?;
        }
        Ok(())
    }
}

fn solve(
    g: &mut Solitaire,
    tp: &mut Cache<Encode, ()>,
    tp_hist: &mut HashSet<Encode>,
    move_list: &mut Vec<MoveType>,
    stats: &Mutex<SearchStats>,
) -> SearchResult {
    {
        let mut stats = stats.lock().unwrap();
        stats.max_depth = std::cmp::max(stats.max_depth, stats.cur_move.len());
        stats.total_visit += 1;
    }

    if g.is_win() {
        return SearchResult::Solved;
    }
    let encode = g.encode();
    if tp.get(&encode).is_some() || !tp_hist.insert(encode) {
        stats.lock().unwrap().tp_hit += 1;
        return SearchResult::Unsolvable;
    } else {
        tp.insert(encode, ());
    }

    let start = move_list.len();
    g.gen_moves_::<true>(move_list);

    let end = move_list.len();

    {
        let mut stats = stats.lock().unwrap();
        stats.total_move.push((end - start) as u8);
        stats.cur_move.push(0);
    }

    for pos in start..end {
        let m = move_list[pos];
        let undo = g.do_move(&m);
        let res = solve(g, tp, tp_hist, move_list, stats);
        if !matches!(res, SearchResult::Unsolvable) {
            return res;
        }
        g.undo_move(&m, &undo);

        *stats.lock().unwrap().cur_move.last_mut().unwrap() = (pos - start + 1) as u8;
    }

    {
        let mut stats = stats.lock().unwrap();
        stats.total_move.pop();
        stats.cur_move.pop();
    }

    move_list.truncate(start);
    tp_hist.remove(&encode);

    SearchResult::Unsolvable
}

pub fn solve_game(
    g: &mut Solitaire,
    stats: &Mutex<SearchStats>,
) -> (SearchResult, Option<Vec<MoveType>>) {
    let mut tp_hist = HashSet::<Encode>::new();
    let mut tp = Cache::<Encode, ()>::new(1024 * 1024 * 32);
    let mut move_list = Vec::<MoveType>::new();
    let search_res = solve(g, &mut tp, &mut tp_hist, &mut move_list, stats);

    if let SearchResult::Solved = search_res {
        let stats = stats.lock().unwrap();
        let history = zip(
            stats.cur_move.iter(),
            stats.total_move.iter().scan(0, |acc, &x| {
                let res = Some(*acc);
                *acc += x;
                res
            }),
        )
        .map(|x| move_list[(x.0 + x.1) as usize])
        .collect();
        (search_res, Some(history))
    } else {
        (search_res, None)
    }
}
