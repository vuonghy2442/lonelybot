use quick_cache::unsync::Cache;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, Mutex};
use std::time::Duration;
use std::{collections::HashSet, fmt::Display};

use crate::engine::{Encode, MoveType, Solitaire};

use std::thread;

#[derive(Debug)]
pub struct SearchStats {
    total_visit: AtomicUsize,
    tp_hit: AtomicUsize,
    max_depth: AtomicUsize,
    move_state: Mutex<Vec<(u8, u8)>>,
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
            total_visit: AtomicUsize::new(0),
            tp_hit: AtomicUsize::new(0),
            max_depth: AtomicUsize::new(0),
            move_state: Mutex::new(Vec::new()),
        }
    }
}

impl Display for SearchStats {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let (total, hit) = (
            self.total_visit.load(Ordering::Relaxed),
            self.tp_hit.load(Ordering::Relaxed),
        );
        write!(
            f,
            "Total visit: {}\nTransposition hit: {}\nNon-cache state: {}\nMax depth search: {}\nCurrent progress:",
            total, hit, total - hit, self.max_depth.load(Ordering::Relaxed),
        )?;

        for (cur, total) in self.move_state.lock().unwrap().iter() {
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
    history: &mut Vec<MoveType>,
    stats: &SearchStats,
) -> SearchResult {
    stats.max_depth.fetch_max(history.len(), Ordering::Relaxed);
    stats.total_visit.fetch_add(1, Ordering::Relaxed);

    if g.is_win() {
        return SearchResult::Solved;
    }
    let encode = g.encode();
    if tp.get(&encode).is_some() || !tp_hist.insert(encode) {
        stats.tp_hit.fetch_add(1, Ordering::Relaxed);
        return SearchResult::Unsolvable;
    } else {
        tp.insert(encode, ());
    }

    let start = move_list.len();
    g.gen_moves_::<true>(move_list);

    let end = move_list.len();

    stats
        .move_state
        .lock()
        .unwrap()
        .push((0, (end - start) as u8));

    for pos in start..end {
        let m = move_list[pos];
        let undo = g.do_move(&m);
        history.push(m);
        let res = solve(g, tp, tp_hist, move_list, history, stats);
        if !matches!(res, SearchResult::Unsolvable) {
            return res;
        }
        history.pop();

        g.undo_move(&m, &undo);

        stats.move_state.lock().unwrap().last_mut().unwrap().0 = (pos - start + 1) as u8;
    }

    stats.move_state.lock().unwrap().pop();

    move_list.truncate(start);
    tp_hist.remove(&encode);

    SearchResult::Unsolvable
}

fn solve_game(g: &mut Solitaire, stats: &SearchStats) -> (SearchResult, Option<Vec<MoveType>>) {
    let mut tp_hist = HashSet::<Encode>::new();
    let mut tp = Cache::<Encode, ()>::new(1024 * 1024 * 32);
    let mut move_list = Vec::<MoveType>::new();
    let mut history = Vec::<MoveType>::new();

    let search_res = solve(
        g,
        &mut tp,
        &mut tp_hist,
        &mut move_list,
        &mut history,
        stats,
    );

    if let SearchResult::Solved = search_res {
        (search_res, Some(history))
    } else {
        (search_res, None)
    }
}

const STACK_SIZE: usize = 4 * 1024 * 1024;

pub fn run_solve(
    mut g: Solitaire,
    verbose: bool,
) -> (SearchResult, SearchStats, Option<Vec<MoveType>>) {
    let ss = Arc::new(SearchStats::new());

    let child = {
        // Spawn thread with explicit stack size
        let ss_clone = ss.clone();
        thread::Builder::new()
            .stack_size(STACK_SIZE)
            .spawn(move || solve_game(&mut g, ss_clone.as_ref()))
            .unwrap()
    };

    if verbose {
        while !child.is_finished() {
            std::thread::sleep(Duration::from_millis(1000));
            println!("{}", ss);
        }
    }

    let (res, hist) = child.join().unwrap();
    return (res, Arc::try_unwrap(ss).unwrap(), hist);
}
