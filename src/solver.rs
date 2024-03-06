use quick_cache::unsync::Cache;
use std::fmt::Display;
use std::sync::atomic::{AtomicBool, AtomicU8, AtomicUsize, Ordering};
use std::sync::mpsc::{channel, RecvTimeoutError, Sender};
use std::sync::Arc;
use std::time::Duration;

use crate::engine::{Encode, Move, Solitaire};

use std::thread;

const TRACK_DEPTH: usize = 8;
const TP_SIZE: usize = 256 * 1024 * 1024;
const STACK_SIZE: usize = 4 * 1024 * 1024;

pub trait SearchStatistics {
    fn hit_a_state(&self, depth: usize);
    fn hit_unique_state(&self, depth: usize, n_moves: usize);
    fn finish_move(&self, depth: usize, move_pos: usize);

    fn total_visit(&self) -> usize;
    fn unique_visit(&self) -> usize;
    fn max_depth(&self) -> usize;
}

#[derive(Debug)]
pub struct AtomicSearchStats {
    total_visit: AtomicUsize,
    unique_visit: AtomicUsize,
    max_depth: AtomicUsize,
    move_state: [(AtomicU8, AtomicU8); TRACK_DEPTH],
}

#[derive(Debug)]
pub enum SearchResult {
    Terminated,
    Solved,
    Unsolvable,
    Crashed,
}
impl AtomicSearchStats {
    pub fn new() -> AtomicSearchStats {
        AtomicSearchStats {
            total_visit: AtomicUsize::new(0),
            unique_visit: AtomicUsize::new(0),
            max_depth: AtomicUsize::new(0),
            move_state: Default::default(),
        }
    }
}

impl SearchStatistics for AtomicSearchStats {
    fn total_visit(&self) -> usize {
        self.total_visit.load(Ordering::Relaxed)
    }

    fn unique_visit(&self) -> usize {
        self.unique_visit.load(Ordering::Relaxed)
    }

    fn max_depth(&self) -> usize {
        self.max_depth.load(Ordering::Relaxed)
    }

    fn hit_a_state(&self, depth: usize) {
        self.max_depth.fetch_max(depth, Ordering::Relaxed);
        self.total_visit.fetch_add(1, Ordering::Relaxed);
    }

    fn hit_unique_state(&self, depth: usize, n_moves: usize) {
        self.unique_visit.fetch_add(1, Ordering::Relaxed);

        if depth < TRACK_DEPTH {
            self.move_state[depth].0.store(0, Ordering::Relaxed);
            self.move_state[depth]
                .1
                .store(n_moves as u8, Ordering::Relaxed);
        }
    }

    fn finish_move(&self, depth: usize, move_pos: usize) {
        if depth < TRACK_DEPTH {
            self.move_state[depth]
                .0
                .store(move_pos as u8, Ordering::Relaxed);
        }
    }
}

impl Display for AtomicSearchStats {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let (total, unique, depth) = (self.total_visit(), self.unique_visit(), self.max_depth());
        let hit = total - unique;
        write!(
            f,
            "Total visit: {}\nTransposition hit: {} (rate {})\nMiss state: {}\nMax depth search: {}\nCurrent progress:",
            total, hit, (hit as f64)/(total as f64), unique, depth,
        )?;

        for (cur, total) in &self.move_state {
            write!(
                f,
                " {}/{}",
                cur.load(Ordering::Relaxed),
                total.load(Ordering::Relaxed)
            )?;
        }
        Ok(())
    }
}

fn solve(
    g: &mut Solitaire,
    rev_move: Option<Move>,
    tp: &mut Cache<Encode, ()>,
    move_list: &mut Vec<Move>,
    history: &mut Vec<Move>,
    stats: &impl SearchStatistics,
    terminated: &AtomicBool,
) -> SearchResult {
    // no need for history caching since the graph is mostly acyclic already, just prevent going to their own parent

    if terminated.load(Ordering::Relaxed) {
        return SearchResult::Terminated;
    }

    let depth = history.len();
    stats.hit_a_state(depth);

    if g.is_win() {
        return SearchResult::Solved;
    }
    let encode = g.encode();
    if tp.get(&encode).is_some() {
        return SearchResult::Unsolvable;
    }

    tp.insert(encode, ());

    let start = move_list.len();
    g.list_moves::<true>(move_list);

    let end = move_list.len();

    stats.hit_unique_state(depth, end - start);

    for pos in start..end {
        let m = move_list[pos];

        if Some(m) == rev_move {
            continue;
        }

        let undo = g.do_move(&m);
        history.push(m);

        let res = solve(
            g,
            g.get_rev_move(&m),
            tp,
            move_list,
            history,
            stats,
            terminated,
        );
        if !matches!(res, SearchResult::Unsolvable) {
            return res;
        }
        history.pop();

        g.undo_move(&m, &undo);

        stats.finish_move(depth, pos - start + 1);
    }

    move_list.truncate(start);

    SearchResult::Unsolvable
}

fn solve_game(
    g: &mut Solitaire,
    stats: &impl SearchStatistics,
    terminated: &AtomicBool,
    done: &Sender<()>,
) -> (SearchResult, Option<Vec<Move>>) {
    let mut tp = Cache::<Encode, ()>::new(TP_SIZE);
    let mut move_list = Vec::<Move>::new();
    let mut history = Vec::<Move>::new();

    let search_res = solve(
        g,
        None,
        &mut tp,
        &mut move_list,
        &mut history,
        stats,
        terminated,
    );

    done.send(()).ok();

    if let SearchResult::Solved = search_res {
        (search_res, Some(history))
    } else {
        (search_res, None)
    }
}

pub fn run_solve(
    mut g: Solitaire,
    verbose: bool,
    term_signal: &Arc<AtomicBool>,
) -> (SearchResult, AtomicSearchStats, Option<Vec<Move>>) {
    let ss = Arc::new(AtomicSearchStats::new());

    let (send, recv) = channel::<()>();

    let child = {
        // Spawn thread with explicit stack size
        let ss_clone = ss.clone();
        let term = term_signal.clone();
        thread::Builder::new()
            .stack_size(STACK_SIZE)
            .spawn(move || solve_game(&mut g, ss_clone.as_ref(), term.as_ref(), &send))
            .unwrap()
    };

    if verbose {
        loop {
            match recv.recv_timeout(Duration::from_millis(1000)) {
                Ok(()) => break,
                Err(RecvTimeoutError::Timeout) => println!("{}", ss),
                Err(RecvTimeoutError::Disconnected) => break,
            };
        }
    }

    let (res, hist) = child.join().unwrap_or((SearchResult::Crashed, None));

    (res, Arc::try_unwrap(ss).unwrap(), hist)
}
