pub trait SearchStatistics {
    fn hit_a_state(&self, depth: usize);
    fn hit_unique_state(&self, depth: usize, n_moves: usize);
    fn finish_move(&self, depth: usize);
}

pub struct EmptySearchStats;

impl SearchStatistics for EmptySearchStats {
    fn hit_a_state(&self, _: usize) {}
    fn hit_unique_state(&self, _: usize, _: usize) {}
    fn finish_move(&self, _: usize) {}
}

pub trait SearchSignal {
    fn terminate(&self);
    fn is_terminated(&self) -> bool;
    fn search_finish(&self);
}

pub struct DefaultSearchSignal;

impl SearchSignal for DefaultSearchSignal {
    fn terminate(&self) {}

    fn is_terminated(&self) -> bool {
        false
    }

    fn search_finish(&self) {}
}
