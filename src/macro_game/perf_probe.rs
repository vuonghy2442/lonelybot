    use core::cell::Cell;

    std::thread_local! {
        static WALK_STATES: Cell<u64> = Cell::new(0);
        static CLS_CALLS: Cell<u64> = Cell::new(0);
        static CLS_STATES: Cell<u64> = Cell::new(0);
        static BFS_CALLS: Cell<u64> = Cell::new(0);
        static BFS_STATES: Cell<u64> = Cell::new(0);
        static BFS_NANOS: Cell<u64> = Cell::new(0);
        static POST_CALLS: Cell<u64> = Cell::new(0);
        static POST_STEPS: Cell<u64> = Cell::new(0);
        static CANON_SWEEPS: Cell<u64> = Cell::new(0);
        static GEN_MOVES: Cell<u64> = Cell::new(0);
        static DO_MOVES: Cell<u64> = Cell::new(0);
        static UNDO_MOVES: Cell<u64> = Cell::new(0);
        static ENCODES: Cell<u64> = Cell::new(0);
        static REG_FIRES: Cell<u64> = Cell::new(0);
        static ACTIVE_CT: Cell<u64> = Cell::new(0);
        static QUIET_SKIP: Cell<u64> = Cell::new(0);
        static CORE_NANOS: Cell<u64> = Cell::new(0);
        static BRANCH_NANOS: Cell<u64> = Cell::new(0);
        static TP_NANOS: Cell<u64> = Cell::new(0);
    }

    pub fn reset() {
        WALK_STATES.with(|c| c.set(0));
        REG_FIRES.with(|c| c.set(0));
        CORE_NANOS.with(|c| c.set(0));
        BRANCH_NANOS.with(|c| c.set(0));
        TP_NANOS.with(|c| c.set(0));
        CLS_CALLS.with(|c| c.set(0));
        CLS_STATES.with(|c| c.set(0));
        BFS_CALLS.with(|c| c.set(0));
        BFS_STATES.with(|c| c.set(0));
        BFS_NANOS.with(|c| c.set(0));
        POST_CALLS.with(|c| c.set(0));
        POST_STEPS.with(|c| c.set(0));
        CANON_SWEEPS.with(|c| c.set(0));
        GEN_MOVES.with(|c| c.set(0));
        DO_MOVES.with(|c| c.set(0));
        UNDO_MOVES.with(|c| c.set(0));
        ENCODES.with(|c| c.set(0));
    }

    #[must_use]
    pub fn read() -> [u64; 19] {
        [
            WALK_STATES.with(Cell::get),
            CLS_CALLS.with(Cell::get),
            CLS_STATES.with(Cell::get),
            BFS_CALLS.with(Cell::get),
            BFS_STATES.with(Cell::get),
            BFS_NANOS.with(Cell::get),
            POST_CALLS.with(Cell::get),
            POST_STEPS.with(Cell::get),
            CANON_SWEEPS.with(Cell::get),
            GEN_MOVES.with(Cell::get),
            DO_MOVES.with(Cell::get),
            UNDO_MOVES.with(Cell::get),
            ENCODES.with(Cell::get),
            REG_FIRES.with(Cell::get),
            ACTIVE_CT.with(Cell::get),
            QUIET_SKIP.with(Cell::get),
            CORE_NANOS.with(Cell::get),
            BRANCH_NANOS.with(Cell::get),
            TP_NANOS.with(Cell::get),
        ]
    }

    /// Count the offset-dominance registry's skips (test-only).
    pub fn bump_reg() {
        REG_FIRES.with(|c| c.set(c.get() + 1));
    }

    /// The active-mask enumeration split (test-only): active
    /// commitments entering the emission loop vs quiet ones skipped.
    pub fn bump_quiet_split(active: u32, quiet: u32) {
        ACTIVE_CT.with(|c| c.set(c.get() + u64::from(active)));
        QUIET_SKIP.with(|c| c.set(c.get() + u64::from(quiet)));
    }

    /// Section timers for the shipped search path (test-only; the
    /// Instant::now overhead inflates all sections equally).
    pub fn bump_core_time(d: std::time::Duration) {
        #[allow(clippy::cast_possible_truncation)]
        CORE_NANOS.with(|c| c.set(c.get() + d.as_nanos() as u64));
    }

    pub fn bump_branch_time(d: std::time::Duration) {
        #[allow(clippy::cast_possible_truncation)]
        BRANCH_NANOS.with(|c| c.set(c.get() + d.as_nanos() as u64));
    }

    pub fn bump_tp_time(d: std::time::Duration) {
        #[allow(clippy::cast_possible_truncation)]
        TP_NANOS.with(|c| c.set(c.get() + d.as_nanos() as u64));
    }

    pub fn bump_walk() {
        WALK_STATES.with(|c| c.set(c.get() + 1));
    }
    pub fn bump_cls_call() {
        CLS_CALLS.with(|c| c.set(c.get() + 1));
    }
    pub fn bump_cls_state() {
        CLS_STATES.with(|c| c.set(c.get() + 1));
    }
    pub fn bump_bfs_call() {
        BFS_CALLS.with(|c| c.set(c.get() + 1));
    }
    pub fn bump_bfs_state() {
        BFS_STATES.with(|c| c.set(c.get() + 1));
    }
    pub fn bump_bfs_time(d: std::time::Duration) {
        #[allow(clippy::cast_possible_truncation)]
        BFS_NANOS.with(|c| c.set(c.get() + d.as_nanos() as u64));
    }
    pub fn bump_post(steps: u64) {
        POST_CALLS.with(|c| c.set(c.get() + 1));
        POST_STEPS.with(|c| c.set(c.get() + steps));
    }
    pub fn bump_canon() {
        CANON_SWEEPS.with(|c| c.set(c.get() + 1));
    }
    pub fn bump_gen() {
        GEN_MOVES.with(|c| c.set(c.get() + 1));
    }
    pub fn bump_do() {
        DO_MOVES.with(|c| c.set(c.get() + 1));
    }
    pub fn bump_undo() {
        UNDO_MOVES.with(|c| c.set(c.get() + 1));
    }
    pub fn bump_enc() {
        ENCODES.with(|c| c.set(c.get() + 1));
    }

    // --- crease grammar (the BFS-elimination question) ---
    // Thread-local histogram of what the shared accommodation BFS actually
    // answers on the path it runs: witness shuffle-length (capped at 15),
    // the alternating shape (a witness mixing PileStack and StackPile
    // before the commit — the chained crease the named channels cannot
    // express as a single probe), answered/missed goals.
    std::thread_local! {
        static CREASE_HIST: [Cell<u64>; 16] = [
            Cell::new(0), Cell::new(0), Cell::new(0), Cell::new(0),
            Cell::new(0), Cell::new(0), Cell::new(0), Cell::new(0),
            Cell::new(0), Cell::new(0), Cell::new(0), Cell::new(0),
            Cell::new(0), Cell::new(0), Cell::new(0), Cell::new(0),
        ];
        static CREASE_ALT: Cell<u64> = Cell::new(0);
        static CREASE_ANS: Cell<u64> = Cell::new(0);
        static CREASE_MISS: Cell<u64> = Cell::new(0);
        static SEL_BFS: Cell<u64> = Cell::new(0);
        static SEL_FIX: Cell<u64> = Cell::new(0);
    }

    pub fn bump_sel(bfs: bool) {
        if bfs {
            SEL_BFS.with(|c| c.set(c.get() + 1));
        } else {
            SEL_FIX.with(|c| c.set(c.get() + 1));
        }
    }

    /// `[len 0..=15][alt][answered][missed][sel_bfs][sel_fix]`
    #[must_use]
    pub fn crease_read() -> [u64; 21] {
        let mut out = [0u64; 21];
        CREASE_HIST.with(|h| {
            for (i, c) in h.iter().enumerate() {
                out[i] = c.get();
            }
        });
        out[16] = CREASE_ALT.with(Cell::get);
        out[17] = CREASE_ANS.with(Cell::get);
        out[18] = CREASE_MISS.with(Cell::get);
        out[19] = SEL_BFS.with(Cell::get);
        out[20] = SEL_FIX.with(Cell::get);
        out
    }

    pub fn crease_reset() {
        CREASE_HIST.with(|h| {
            for c in h.iter() {
                c.set(0);
            }
        });
        CREASE_ALT.with(|c| c.set(0));
        CREASE_ANS.with(|c| c.set(0));
        CREASE_MISS.with(|c| c.set(0));
        SEL_BFS.with(|c| c.set(0));
        SEL_FIX.with(|c| c.set(0));
    }

    pub fn bump_crease(shuffles: usize, alternating: bool) {
        CREASE_HIST.with(|h| h[shuffles.min(15)].set(h[shuffles.min(15)].get() + 1));
        if alternating {
            CREASE_ALT.with(|c| c.set(c.get() + 1));
        }
        CREASE_ANS.with(|c| c.set(c.get() + 1));
    }

    pub fn bump_crease_miss() {
        CREASE_MISS.with(|c| c.set(c.get() + 1));
    }

    /// Missed-goal kind split for the BFS-elimination question:
    /// `[stack-climb, stack-descent, tableau]` — which residual miss
    /// population a stronger kill would have to address.
    std::thread_local! {
        static MISS_KIND: [Cell<u64>; 3] = [Cell::new(0), Cell::new(0), Cell::new(0)];
    }

    /// `climb` = stack goal with `h₀ < rank(X)` (K1's jurisdiction),
    /// `desc` = stack goal with `h₀ > rank(X)` (K3's), `tab` = tableau.
    pub fn bump_miss_kind(kind: usize) {
        MISS_KIND.with(|h| h[kind.min(2)].set(h[kind.min(2)].get() + 1));
    }

    pub fn miss_kind_read() -> [u64; 3] {
        [
            MISS_KIND.with(|h| h[0].get()),
            MISS_KIND.with(|h| h[1].get()),
            MISS_KIND.with(|h| h[2].get()),
        ]
    }

    pub fn miss_kind_reset() {
        MISS_KIND.with(|h| {
            for c in h.iter() {
                c.set(0);
            }
        });
    }
