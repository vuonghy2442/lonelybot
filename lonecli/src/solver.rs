use core::time::Duration;
use lonelybot::{
    engine::Solitaire,
    graph::{graph_with_tracking, Graph},
    solver::{solve_with_tracking, HistoryVec, SearchResult},
    tracking::TerminateSignal,
    traverse::ControlFlow,
};
use std::{
    sync::{
        atomic::{AtomicBool, Ordering},
        mpsc::{channel, RecvTimeoutError},
        Arc,
    },
    thread,
};

use crate::tracking::AtomicSearchStats;

const STACK_SIZE: usize = 4 * 1024 * 1024;

struct Signal<'a> {
    term_signal: &'a AtomicBool,
}

impl<'a> TerminateSignal for Signal<'a> {
    fn terminate(&self) {
        self.term_signal.store(true, Ordering::Relaxed);
    }

    fn is_terminated(&self) -> bool {
        self.term_signal.load(Ordering::Relaxed)
    }
}

pub fn run_solve(
    mut g: Solitaire,
    verbose: bool,
    term_signal: &Arc<AtomicBool>,
) -> (SearchResult, AtomicSearchStats, Option<HistoryVec>) {
    let ss = Arc::new(AtomicSearchStats::new());

    let (send, recv) = channel::<()>();

    let child = {
        // Spawn thread with explicit stack size
        let ss_clone = ss.clone();
        let term = term_signal.clone();
        thread::Builder::new()
            .stack_size(STACK_SIZE)
            .spawn(move || {
                let res = solve_with_tracking(
                    &mut g,
                    ss_clone.as_ref(),
                    &Signal {
                        term_signal: term.as_ref(),
                    },
                );
                send.send(()).ok();
                res
            })
            .unwrap()
    };

    if verbose {
        loop {
            match recv.recv_timeout(Duration::from_millis(1000)) {
                Err(RecvTimeoutError::Disconnected) | Ok(()) => break,
                Err(RecvTimeoutError::Timeout) => println!("{ss}"),
            };
        }
    }

    let (res, hist) = child.join().unwrap_or((SearchResult::Crashed, None));

    (res, Arc::try_unwrap(ss).unwrap(), hist)
}

pub fn run_graph(
    mut g: Solitaire,
    verbose: bool,
    term_signal: &Arc<AtomicBool>,
) -> (Option<(ControlFlow, Graph)>, AtomicSearchStats) {
    let ss = Arc::new(AtomicSearchStats::new());

    let (send, recv) = channel::<()>();

    let child = {
        // Spawn thread with explicit stack size
        let ss_clone = ss.clone();
        let term = term_signal.clone();
        thread::Builder::new()
            .stack_size(STACK_SIZE)
            .spawn(move || {
                let res = graph_with_tracking(
                    &mut g,
                    ss_clone.as_ref(),
                    &Signal {
                        term_signal: term.as_ref(),
                    },
                );
                send.send(()).ok();
                res
            })
            .unwrap()
    };

    if verbose {
        loop {
            match recv.recv_timeout(Duration::from_millis(1000)) {
                Err(RecvTimeoutError::Disconnected) | Ok(()) => break,
                Err(RecvTimeoutError::Timeout) => println!("{ss}"),
            };
        }
    }

    let res = child.join().ok();
    (res, Arc::try_unwrap(ss).unwrap())
}
