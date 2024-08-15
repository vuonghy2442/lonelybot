use core::sync::atomic::{AtomicU8, AtomicUsize, Ordering};

use lonelybot::tracking::SearchStatistics;

const TRACK_DEPTH: usize = 8;

#[derive(Debug, Default)]
pub(crate) struct AtomicSearchStats {
    total_visit: AtomicUsize,
    unique_visit: AtomicUsize,
    max_depth: AtomicUsize,
    move_state: [(AtomicU8, AtomicU8); TRACK_DEPTH],
}

impl AtomicSearchStats {
    #[must_use]
    pub(crate) fn new() -> Self {
        Self::default()
    }

    #[must_use]
    pub(crate) fn total_visit(&self) -> usize {
        self.total_visit.load(Ordering::Relaxed)
    }

    #[must_use]
    pub(crate) fn unique_visit(&self) -> usize {
        self.unique_visit.load(Ordering::Relaxed)
    }

    #[must_use]
    pub(crate) fn max_depth(&self) -> usize {
        self.max_depth.load(Ordering::Relaxed)
    }
}

impl SearchStatistics for AtomicSearchStats {
    fn hit_a_state(&self, depth: usize) {
        self.max_depth.fetch_max(depth, Ordering::Relaxed);
        self.total_visit.fetch_add(1, Ordering::Relaxed);
    }

    fn hit_unique_state(&self, depth: usize, n_moves: u32) {
        self.unique_visit.fetch_add(1, Ordering::Relaxed);

        if depth < TRACK_DEPTH {
            self.move_state[depth].0.store(0, Ordering::Relaxed);
            self.move_state[depth]
                .1
                .store(n_moves as u8, Ordering::Relaxed);
        }
    }

    fn finish_move(&self, depth: usize) {
        if depth < TRACK_DEPTH {
            self.move_state[depth].0.fetch_add(1, Ordering::Relaxed);
        }
    }
}

impl core::fmt::Display for AtomicSearchStats {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        let (total, unique, depth) = (self.total_visit(), self.unique_visit(), self.max_depth());
        let hit = total - unique;
        #[allow(clippy::cast_precision_loss)]
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
