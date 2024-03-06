use core::time::Duration;
use lonelybot::{
    engine::Solitaire,
    solver::{solve_game, AtomicSearchStats, HistoryVec, SearchResult, SearchSignal},
};
use std::{
    sync::{
        atomic::{AtomicBool, Ordering},
        mpsc::{channel, RecvTimeoutError, Sender},
        Arc,
    },
    thread,
};

const STACK_SIZE: usize = 4 * 1024 * 1024;

struct Signal<'a> {
    term_signal: &'a AtomicBool,
    done_channel: Sender<()>,
}

impl<'a> SearchSignal for Signal<'a> {
    fn terminate(&self) {
        self.term_signal.store(true, Ordering::Relaxed);
    }

    fn is_terminated(&self) -> bool {
        self.term_signal.load(Ordering::Relaxed)
    }

    fn search_finished(&self) {
        self.done_channel.send(()).ok();
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
                solve_game(
                    &mut g,
                    ss_clone.as_ref(),
                    &Signal {
                        term_signal: term.as_ref(),
                        done_channel: send,
                    },
                )
            })
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
