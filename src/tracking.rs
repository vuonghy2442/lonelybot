pub trait SearchStatistics {
    fn hit_a_state(&self, depth: usize);
    fn hit_unique_state(&self, depth: usize, n_moves: u32);
    fn finish_move(&self, depth: usize);
}

pub struct EmptySearchStats;

impl SearchStatistics for EmptySearchStats {
    fn hit_a_state(&self, _: usize) {}
    fn hit_unique_state(&self, _: usize, _: u32) {}
    fn finish_move(&self, _: usize) {}
}

pub trait TerminateSignal {
    fn terminate(&self) {}
    fn is_terminated(&self) -> bool {
        false
    }
}

pub struct DefaultTerminateSignal;

impl TerminateSignal for DefaultTerminateSignal {}
