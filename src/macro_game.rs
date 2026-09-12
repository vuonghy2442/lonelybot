//! The macro (commitment) game — early scaffold for the rework described in
//! docs/macro_formalization.md.
//!
//! The old game has five moves; the macro game regroups any play as
//! "shuffle, commit, shuffle, commit, ..." (Lemma A3) where a *commitment*
//! is the first irreversible move after a reversible accommodation
//! (Lemma A1: only `DeckPile`/`DeckStack` introduce a deck card, and only
//! `Reveal`/`PileStack`-on-locked touch the hidden structure — both
//! irreversible).
//!
//! This module provides, for now:
//!
//! - `Commitment` — the macro move identity (target card driven);
//! - the reversible-closure walker: DFS over states reachable by reversible
//!   moves only (`PileStack` unlocked / `StackPile`);
//! - `enumerate_commitments`: the closure-crossed commitment set with a
//!   witness path each (the accommodation witness of Lemma A3);
//! - per-commitment outcome witnesses for the two C2 shapes (target lands
//!   on the tableau / on the foundation), measured across the closure.
//!
//! What is deliberately NOT here yet: the *canonical* accommodation
//! (open item O6 — which shuffle, and why the outcomes then collapse to
//! ≤2 distinct abstract states). The recorded counts of distinct
//! post-encodes per commitment are the raw material for that question.

use arrayvec::ArrayVec;

extern crate alloc;
use alloc::vec::Vec;

use crate::moves::{Move, N_MOVES_MAX};
use crate::state::{Encode, Solitaire};
use crate::traverse::TpTable;
use crate::card::Card;

/// cfg(test)-only perf instrumentation: thread-local counters bumped by
/// the hot paths (closure walk, closure clustering, accommodation BFS,
/// post_state, sweep). Thread-local so parallel tests never cross-
/// contaminate; never compiled into non-test builds.
#[cfg(test)]
pub(crate) mod perf_probe {
    use core::cell::Cell;

    std::thread_local! {
        static WALK_STATES: Cell<u64> = Cell::new(0);
        static CLS_CALLS: Cell<u64> = Cell::new(0);
        static CLS_STATES: Cell<u64> = Cell::new(0);
        static BFS_CALLS: Cell<u64> = Cell::new(0);
        static BFS_STATES: Cell<u64> = Cell::new(0);
        static POST_CALLS: Cell<u64> = Cell::new(0);
        static POST_STEPS: Cell<u64> = Cell::new(0);
        static CANON_SWEEPS: Cell<u64> = Cell::new(0);
        static GEN_MOVES: Cell<u64> = Cell::new(0);
        static DO_MOVES: Cell<u64> = Cell::new(0);
        static UNDO_MOVES: Cell<u64> = Cell::new(0);
        static ENCODES: Cell<u64> = Cell::new(0);
    }

    pub fn reset() {
        WALK_STATES.with(|c| c.set(0));
        CLS_CALLS.with(|c| c.set(0));
        CLS_STATES.with(|c| c.set(0));
        BFS_CALLS.with(|c| c.set(0));
        BFS_STATES.with(|c| c.set(0));
        POST_CALLS.with(|c| c.set(0));
        POST_STEPS.with(|c| c.set(0));
        CANON_SWEEPS.with(|c| c.set(0));
        GEN_MOVES.with(|c| c.set(0));
        DO_MOVES.with(|c| c.set(0));
        UNDO_MOVES.with(|c| c.set(0));
        ENCODES.with(|c| c.set(0));
    }

    #[must_use]
    pub fn read() -> [u64; 12] {
        [
            WALK_STATES.with(Cell::get),
            CLS_CALLS.with(Cell::get),
            CLS_STATES.with(Cell::get),
            BFS_CALLS.with(Cell::get),
            BFS_STATES.with(Cell::get),
            POST_CALLS.with(Cell::get),
            POST_STEPS.with(Cell::get),
            CANON_SWEEPS.with(Cell::get),
            GEN_MOVES.with(Cell::get),
            DO_MOVES.with(Cell::get),
            UNDO_MOVES.with(Cell::get),
            ENCODES.with(Cell::get),
        ]
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
}

/// A macro move: commit to a deck card or to revealing a surface card.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Commitment {
    Draw(Card),
    Reveal(Card),
}

impl Commitment {
    /// Reveal sorts before Draw (both card-lowest-first): the measured
    /// search order — the mirror of the old engine's raw move order,
    /// which tries `Reveal` before any deck move. Draw-first buries
    /// reveal-led winning lines under draw-subgame refutations; see
    /// `macro_verdict_perf_probe` for the before/after node counts.
    fn sort_key(self) -> (u8, u8) {
        let (tag, c) = match self {
            Commitment::Reveal(c) => (0, c),
            Commitment::Draw(c) => (1, c),
        };
        (tag, c.mask_index())
    }
}

/// Which of the two C2 outcomes an irreversible old-game move realizes.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum OutcomeKind {
    /// The target card lands on the tableau.
    Tableau,
    /// The target card lands on the foundation.
    Stack,
}

/// Distinct post-state witnesses found for one commitment across the
/// reversible closure. Bounded storage; `overflowed` flags the cap being
/// hit so multiplicity readings stay honest.
#[derive(Debug, Default)]
pub struct OutcomeWitnesses {
    pub tableau: ArrayVec<Encode, 4>,
    pub stack: ArrayVec<Encode, 4>,
    pub overflowed: bool,
    /// Same measurement after the safe-sweep canonicalization; the C2
    /// claim is about these counts, not the raw ones. Kept alongside the
    /// states themselves (dedup by encode) for the closure-quotient probe.
    pub canon_tableau: ArrayVec<(Encode, Solitaire), 8>,
    pub canon_stack: ArrayVec<(Encode, Solitaire), 8>,
    pub canon_overflowed: bool,
}

impl OutcomeWitnesses {
    fn record(&mut self, kind: OutcomeKind, enc: Encode) {
        let slot = match kind {
            OutcomeKind::Tableau => &mut self.tableau,
            OutcomeKind::Stack => &mut self.stack,
        };
        if !slot.contains(&enc) {
            if slot.try_push(enc).is_err() {
                self.overflowed = true;
            }
        }
    }

    fn record_canonical(&mut self, kind: OutcomeKind, enc: Encode, state: &Solitaire) {
        let slot = match kind {
            OutcomeKind::Tableau => &mut self.canon_tableau,
            OutcomeKind::Stack => &mut self.canon_stack,
        };
        if !slot.iter().any(|(e, _)| *e == enc) {
            if slot.try_push((enc, state.clone())).is_err() {
                self.canon_overflowed = true;
            }
        }
    }
}

/// One commitment reachable from the searched state, with witnesses.
#[derive(Debug)]
pub struct CommitmentInfo {
    pub commitment: Commitment,
    /// A reversible shuffle path from the root to a state where this
    /// commitment is offered (first found), followed by the commitment move
    /// itself as the last element.
    pub witness_path: Vec<Move>,
    /// the first-known witness path per outcome kind (the missing-channel
    /// forensics ask for these)
    pub kind_witnesses: [Option<Vec<Move>>; 2],
    pub outcomes: OutcomeWitnesses,
}

impl Commitment {
    /// The irreversible old moves that realize this commitment, with the
    /// outcome kind each produces.
    fn realize(kind: Commitment) -> [(MoveKind, OutcomeKind); 2] {
        match kind {
            Commitment::Draw(c) => [
                (MoveKind::DeckPile(c), OutcomeKind::Tableau),
                (MoveKind::DeckStack(c), OutcomeKind::Stack),
            ],
            Commitment::Reveal(c) => [
                (MoveKind::Reveal(c), OutcomeKind::Tableau),
                // PileStack on a locked card is reveal-by-stacking.
                (MoveKind::PileStack(c), OutcomeKind::Stack),
            ],
        }
    }
}

type MoveKind = Move;

fn commitment_of(m: Move) -> Option<Commitment> {
    Some(match m {
        Move::DeckPile(c) | Move::DeckStack(c) => Commitment::Draw(c),
        Move::Reveal(c) => Commitment::Reveal(c),
        Move::PileStack(c) => Commitment::Reveal(c), // only when locked; checked by caller
        Move::StackPile(_) => return None,           // always reversible
    })
}

/// The sweep candidate rule, single source of truth for the sweep used by
/// `canonicalize` and the confluence test: any safely-stackable, movable,
/// unlocked tableau card. Locked cards are excluded because stacking one is
/// a reveal — a commitment, not an accommodation.
fn sweep_candidates(g: &Solitaire) -> u64 {
    // the raw cascade-free set, shared by `canonicalize` and the
    // confluence test
    g.safe_sweep_candidates()
}

/// Canonicalize to the safe-sweep fixed point: stack every safely-stackable
/// movable unlocked card, deterministically lowest-first.
///
/// Confluence (order-independence of the terminal encode) is argued by
/// monotonicity of all three enablers (stackability, safety, movability)
/// and measured by `sweep_is_confluent`.
fn canonicalize(g: &mut Solitaire) {
    loop {
        let cands = sweep_candidates(g);
        if cands == 0 {
            break;
        }
        #[cfg(test)]
        perf_probe::bump_canon();
        let cm = cands & cands.wrapping_neg();
        let c = Card::from_mask_index(u8::try_from(cm.trailing_zeros()).unwrap());

        // Ambiguous-twin tie-break: if both twins of c's type are visible,
        // the type-level mask names both as stackable, but concretely only
        // one is movable. Abstract simulation of either stacking is
        // defensible; prefer the variant that keeps the survivor movable,
        // which is the one that does not freeze the type's future
        // candidacy. (The unchosen twin cannot be told apart from the
        // chosen one at state level — this is the twin-expansion case of
        // the reshape lemma operating inside the sweep.)
        let _ = &c; // deterministic lower-index resolution of ambiguous twins
        let m = Move::PileStack(c);
        let (_, (undo, _)) = g.do_move(m);
        let _ = undo; // the sweep only goes forward
    }
}

fn find_slot<'a>(
    out: &'a mut Vec<CommitmentInfo>,
    commitment: Commitment,
) -> &'a mut CommitmentInfo {
    if let Some(pos) = out.iter().position(|x| x.commitment == commitment) {
        &mut out[pos]
    } else {
        out.push(CommitmentInfo {
            commitment,
            witness_path: Vec::new(),
            kind_witnesses: [None, None],
            outcomes: OutcomeWitnesses::default(),
        });
        out.last_mut().unwrap()
    }
}

fn walk(
    g: &mut Solitaire,
    tp: &mut TpTable,
    hist: &mut Vec<Move>,
    out: &mut Vec<CommitmentInfo>,
) {
    #[cfg(test)]
    perf_probe::bump_walk();
    if g.is_win() || !tp.insert(g.encode()) {
        return;
    }
    let moves = g.gen_moves::<false>().to_vec::<N_MOVES_MAX>();
    for m in moves {
        let rev = g.reverse_move(m);
        let (_, (undo, _)) = g.do_move(m);
        let enc = g.encode();
        match rev {
            None => {
                let commitment = commitment_of(m).expect("irreversible move must map");
                let first = out
                    .iter()
                    .all(|x: &CommitmentInfo| x.commitment != commitment);
                let slot = find_slot(out, commitment);
                if first {
                    slot.witness_path = hist.clone();
                    slot.witness_path.push(m);
                }
                if let Some(kind) = Commitment::realize(commitment)
                    .iter()
                    .find(|(mk, _)| *mk == m)
                {
                    slot.outcomes.record(kind.1, enc);
                    let k = match kind.1 {
                        OutcomeKind::Tableau => 0,
                        OutcomeKind::Stack => 1,
                    };
                    if slot.kind_witnesses[k].is_none() {
                        let mut p = hist.clone();
                        p.push(m);
                        slot.kind_witnesses[k] = Some(p);
                    }

                    // canonicalized reading of the same outcome (C2 probe)
                    let mut canon = g.clone();
                    canonicalize(&mut canon);
                    slot.outcomes
                        .record_canonical(kind.1, canon.encode(), &canon);
                }
            }
            Some(_) => {
                hist.push(m);
                walk(g, tp, hist, out);
                hist.pop();
            }
        }
        g.undo_move(m, undo);
    }
}

/// Is `target` in the reversible closure of `a`? Reversible moves are
/// symmetric, so membership is mutual: this tests closure-class equality.
fn closure_contains(a: &Solitaire, target: Encode) -> bool {
    fn rec(g: &mut Solitaire, tp: &mut TpTable, target: Encode) -> bool {
        #[cfg(test)]
        perf_probe::bump_cls_state();
        let enc = g.encode();
        if enc == target {
            return true;
        }
        if !tp.insert(enc) {
            return false;
        }
        let moves = g.gen_moves::<false>().to_vec::<N_MOVES_MAX>();
        for m in moves {
            if g.reverse_move(m).is_some() {
                let (_, (undo, _)) = g.do_move(m);
                let hit = rec(g, tp, target);
                g.undo_move(m, undo);
                if hit {
                    return true;
                }
            }
        }
        false
    }
    let mut g = a.clone();
    let mut tp = TpTable::default();
    #[cfg(test)]
    perf_probe::bump_cls_call();
    rec(&mut g, &mut tp, target)
}

/// Number of distinct reversible-closure classes among sampled post-states.
/// The C2 claim is that this is at most 2 per commitment (target on
/// tableau / on foundation), i.e. all free-float variation collapses.
fn closure_classes(samples: &[(Encode, Solitaire)]) -> usize {
    let mut reps: Vec<&Solitaire> = Vec::new();
    'next: for (_, st) in samples {
        for rep in &reps {
            if closure_contains(rep, st.encode()) {
                continue 'next;
            }
        }
        reps.push(st);
    }
    reps.len()
}

/// Enumerate all macro commitments from `g`: every commitment realizable by
/// some reversible accommodation of `g`, with a witness path and the
/// distinct abstract post-states observed across the whole closure.
///
/// Runs on the raw move generator (dominances off, no pruner) on purpose:
/// the reduction claim C1 is about the raw game; filtered variants are
/// exactly what the differential checker (macro doc §5) compares against.
#[must_use]
pub fn enumerate_commitments(g: &Solitaire) -> Vec<CommitmentInfo> {
    let mut game = g.clone();
    canonicalize(&mut game);
    let mut tp = TpTable::default();
    let mut hist = Vec::new();
    let mut out = Vec::new();
    walk(&mut game, &mut tp, &mut hist, &mut out);
    out.sort_by_key(|x| x.commitment.sort_key());
    out
}

/// The macro transitions out of `g`: one representative post-state per
/// (commitment, reversible-closure class). All outcome samples of a
/// commitment are clustered by mutual reversible reachability; the first
/// sample of each class is the representative.
///
/// Within-class sampling is lost on purpose: downstream commitment
/// enumeration walks the closure itself, so any representative of a class
/// offers the full class repertoire. Soundness of the macro search never
/// rests on the class count being ≤ 2 — that is C2's separate content.
#[must_use]
pub fn enumerate_transitions(g: &Solitaire) -> Vec<(Commitment, Solitaire)> {
    let mut out: Vec<(Commitment, Solitaire)> = Vec::new();
    for c in enumerate_commitments(g) {
        let mut reps: Vec<Solitaire> = Vec::new();
        for samples in [&c.outcomes.canon_tableau, &c.outcomes.canon_stack] {
            for (enc, st) in samples.iter() {
                if !reps.iter().any(|r| closure_contains(r, *enc)) {
                    reps.push(st.clone());
                }
            }
        }
        out.extend(reps.into_iter().map(|r| (c.commitment, r)));
    }
    out
}

/// Successor-selection policy for the canonical-scar experiment (O6):
/// when a commitment's post-states fall into several closure classes
/// (different irreversible dig scars), can a *fixed height policy* choose
/// the class without losing wins?
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SuccSelect {
    /// Keep every closure class (the sound default; ≤ 2 empirically).
    All,
    /// Per commitment, keep only the class with the largest total
    /// foundation height — "dig tall" (the proxy for "pick the tallest
    /// same-color suit").
    TallestOnly,
    /// Dual: the shallowest scar survives.
    ShortestOnly,
}

fn stack_total(s: &Solitaire) -> u32 {
    let st = s.get_stack();
    (0..crate::card::N_SUITS)
        .map(|i| u32::from(st.get(i)))
        .sum()
}

fn apply_select(succs: &mut Vec<(Commitment, Solitaire)>, sel: SuccSelect) {
    if sel == SuccSelect::All {
        return;
    }
    // successors arrive grouped per commitment (enumeration order)
    let mut kept: Vec<(Commitment, Solitaire)> = Vec::new();
    let mut i = 0;
    while i < succs.len() {
        let comm = succs[i].0;
        let mut best = i;
        let mut j = i;
        while j < succs.len() && succs[j].0 == comm {
            let h = stack_total(&succs[j].1);
            let hb = stack_total(&succs[best].1);
            let better = match sel {
                SuccSelect::TallestOnly => h > hb,
                SuccSelect::ShortestOnly => h < hb,
                SuccSelect::All => unreachable!(),
            };
            if better {
                best = j;
            }
            j += 1;
        }
        kept.push((comm, succs[best].1.clone()));
        i = j;
    }
    *succs = kept;
}

/// Is `g` winnable in the commitment game under successor policy `sel`?
/// Plain DFS over canonical (safe-swept) states with insert-once dedup.
/// Deliberately naive: this is the semantics checker for the rework, not
/// the speed version.
#[must_use]
pub fn macro_solvable_sel(g: &Solitaire, sel: SuccSelect) -> bool {
    fn rec(g: &Solitaire, sel: SuccSelect, tp: &mut TpTable) -> bool {
        let mut s = g.clone();
        canonicalize(&mut s);
        if s.is_win() || !tp.insert(s.encode()) {
            return s.is_win();
        }
        let mut succs = enumerate_transitions(&s);
        apply_select(&mut succs, sel);
        succs.iter().any(|(_, succ)| rec(succ, sel, tp))
    }
    rec(g, sel, &mut TpTable::default())
}

/// The policy-free variant: all closure classes kept.
#[must_use]
pub fn macro_solvable(g: &Solitaire) -> bool {
    macro_solvable_sel(g, SuccSelect::All)
}

/// Transitions sourced from the rule-driven generator (the fast path):
/// one representative per (commitment, outcome kind), materialized only
/// after the fold, plus the F3 dominance drop. The scar-choice policies
/// of the oracle variant do not apply here — the direct generator's
/// per-kind representative is the canonical one by §6.4's priority order,
/// and anything beyond that would reintroduce the closure walk this
/// exists to avoid.
///
/// Two search policies beyond `macro_transitions_direct`'s raw emission:
/// - per-(commitment, kind) collapse: theoretically under-emissive
///   (macro doc §6.7: same-kind scar classes can have different futures;
///   P2's absorption is what makes per-kind collapse safe). Deduping by
///   encode instead visits every float-noise member of a class (§6.3,
///   unbounded multiplicity), multiplying the search tree — the
///   original seed-18 blowup; the loss is measured by the class-coverage
///   metric in macro_direct_matches_oracle.
/// - F3 (macro doc §4 "additional collapsing"): when X is dominantly
///   stackable, its tableau outcome is dominated and is dropped. Measured
///   5-6% of branches on the deep seeds, 16% elsewhere.
///
/// Both are search policies: `macro_transitions_direct` keeps full
/// semantics for the differential, and the verdict gate judges soundness.
#[must_use]
pub fn macro_transitions_fast(g: &Solitaire) -> Vec<(Commitment, Solitaire)> {
    let mut scratch = DirectScratch::new();
    macro_transitions_fast_into(g, &mut scratch);
    scratch.out
}

/// The search-facing fold into `scratch.out` (reused across nodes).
fn macro_transitions_fast_into(g: &Solitaire, scratch: &mut DirectScratch) {
    let root = macro_transitions_core(g, scratch);
    // F3 mask: commitments with a direct stack outcome now (X stackable),
    // of a dominantly safe type
    let dom = root.get_stack().dominance_mask();
    let mut f3: u64 = 0;
    for group in &scratch.groups {
        for (c, k, _, ch) in group {
            if *k == OutcomeKind::Stack && *ch == "stack-direct" {
                f3 |= match c {
                    Commitment::Draw(x) | Commitment::Reveal(x) => x.mask(),
                };
            }
        }
    }
    f3 &= dom;
    scratch.fold_seen.clear();
    scratch.out.clear();
    for group in &scratch.groups {
        for (c, k, steps, _) in group {
            if *k == OutcomeKind::Tableau
                && f3
                    & match c {
                        Commitment::Draw(x) | Commitment::Reveal(x) => x.mask(),
                    }
                    != 0
            {
                continue;
            }
            if scratch.fold_seen.contains(&(*c, *k)) {
                continue;
            }
            scratch.fold_seen.push((*c, *k));
            scratch
                .out
                .push((*c, post_state(&root, steps)));
        }
    }
}

/// Solve the macro game on the direct transition function. Same recursive
/// shape as `macro_solvable`, different transition semantics source — the
/// two must agree on solvability or the fast generator is wrong.
///
/// Successors arrive canonicalized from `post_state`, so the recursion does
/// not resweep them; entry canonicalizes the start state once. The
/// transition working buffers live in one `DirectScratch` for the whole
/// search: cleared per node, not reallocated (the profiled per-node cost
/// of fresh buffers was ~35 heap allocs).
#[must_use]
pub fn macro_solvable_direct(g: &Solitaire) -> bool {
    fn rec(s: &Solitaire, tp: &mut TpTable, scratch: &mut DirectScratch) -> bool {
        if s.is_win() || !tp.insert(s.encode()) {
            return s.is_win();
        }
        macro_transitions_fast_into(s, scratch);
        // take the successor vec out so recursion can reuse the scratch
        let succs = core::mem::take(&mut scratch.out);
        let mut result = false;
        for (_, succ) in &succs {
            if rec(succ, tp, scratch) {
                result = true;
                break;
            }
        }
        // hand the allocation back for the next node
        let mut succs = succs;
        succs.clear();
        scratch.out = succs;
        result
    }
    let mut root = g.clone();
    canonicalize(&mut root);
    rec(&root, &mut TpTable::default(), &mut DirectScratch::new())
}

/// One accommodation goal the fixed channels left open: make `x`'s
/// `kind`-placement legal via a bounded reversible shuffle.
struct AccommodationGoal {
    commitment: Commitment,
    kind: OutcomeKind,
    xmask: u64,
    /// the irreversible move realizing the commitment once accommodated
    commit_move: Move,
    /// openings at pop-depth >= cap do not count (the depth bound)
    cap: usize,
}

/// Bounded local search for the accommodations the constant-work
/// channels missed (chained borrows/digs — the §6.4 crease), answering
/// *every* pending goal with one shared traversal. This is the honest
/// fallback the differential test measures: the rule list
/// (direct/dig/borrow) converges exactly when this rarely answers.
///
/// BFS, not DFS, because level order is the semantics: each goal's
/// witness is the *shortest* opening shuffle (the depth-ordered scar the
/// §7 absorption argument works with), and a goal is provably dead the
/// moment level `cap` starts popping — which is what lets one traversal
/// serve all goals with per-goal caps. Expansion order is goal-independent
/// (mask order + insert-once dedup), so each goal's first opening is
/// exactly the state its dedicated per-goal BFS would have returned.
///
/// The shared form replaces one BFS *per commitment*: those all started
/// from the same root and re-explored the same closure (~16 probes per
/// node on the verdict corpus, 96%+ failing; see macro_verdict_perf_probe).
/// States are cloned only when actually enqueued (do/undo on the popped
/// state otherwise), and witnesses are reconstructed from the
/// parent-pointer arena, not carried as per-state move lists.
/// Reusable working buffers for the BFS — cleared, not reallocated, per
/// node (the profile showed ~35 heap allocs per node across these).
pub(crate) struct BfsScratch {
    arena: Vec<(usize, Move, u16)>,
    queue: alloc::collections::VecDeque<(Solitaire, usize)>,
    seen: crate::traverse::TpTable,
}

/// Reusable working buffers for the whole direct-transition machinery:
/// one set per search instead of one per node.
pub(crate) struct DirectScratch {
    groups: Vec<Vec<StepTransition>>,
    goals: Vec<AccommodationGoal>,
    bfs: BfsScratch,
    fold_seen: Vec<(Commitment, OutcomeKind)>,
    out: Vec<(Commitment, Solitaire)>,
}

impl DirectScratch {
    #[must_use]
    pub fn new() -> Self {
        Self {
            groups: Vec::new(),
            goals: Vec::new(),
            bfs: BfsScratch {
                arena: Vec::new(),
                queue: alloc::collections::VecDeque::new(),
                seen: crate::traverse::TpTable::default(),
            },
            fold_seen: Vec::new(),
            out: Vec::new(),
        }
    }
}

fn accommodations_shared(
    g: &Solitaire,
    root_mv: crate::moves::MoveMask,
    goals: &[AccommodationGoal],
    scratch: &mut BfsScratch,
) -> Vec<Option<Vec<Move>>> {
    #[cfg(test)]
    perf_probe::bump_bfs_call();
    // answers[gi] = arena index of the shallowest state where goal gi opened
    let mut answers: Vec<Option<usize>> = (0..goals.len()).map(|_| None).collect();
    let mut pending: Vec<usize> = (0..goals.len()).collect();
    // parent-pointer arena: entry i = (parent index, reaching move, depth);
    // entry 0 is the root sentinel
    let arena = &mut scratch.arena;
    let queue = &mut scratch.queue;
    let seen = &mut scratch.seen;
    arena.clear();
    queue.clear();
    seen.clear();
    arena.push((usize::MAX, Move::PileStack(Card::DEFAULT), 0));
    queue.push_back((g.clone(), 0));
    let mut first_pop = true;
    seen.insert(g.encode());

    while let Some((mut state, idx)) = queue.pop_front() {
        #[cfg(test)]
        perf_probe::bump_bfs_state();
        // the root pop reuses the caller's move mask (same state)
        let mv = if first_pop {
            first_pop = false;
            root_mv
        } else {
            state.gen_moves::<false>()
        };
        let depth = usize::from(arena[idx].2);
        // a cap this level exceeds can no longer open
        pending.retain(|&gi| goals[gi].cap > depth);
        if pending.is_empty() {
            break;
        }
        let mut opened = false;
        for &gi in &pending {
            let goal = &goals[gi];
            // does the goal kind become legal here?
            let opens = match (goal.commitment, goal.kind) {
                (Commitment::Draw(_), OutcomeKind::Tableau) => mv.deck_pile & goal.xmask != 0,
                (Commitment::Reveal(_), OutcomeKind::Tableau) => mv.reveal & goal.xmask != 0,
                (Commitment::Draw(_), OutcomeKind::Stack) => mv.deck_stack & goal.xmask != 0,
                (Commitment::Reveal(_), OutcomeKind::Stack) => mv.pile_stack & goal.xmask != 0,
            };
            if opens {
                answers[gi] = Some(idx);
                opened = true;
            }
        }
        if opened {
            pending.retain(|&gi| answers[gi].is_none());
            if pending.is_empty() {
                break;
            }
        }
        // children can only serve goals whose cap exceeds their depth
        let max_cap = pending.iter().map(|&gi| goals[gi].cap).max().unwrap_or(0);
        if depth + 1 >= max_cap {
            continue;
        }
        // accommodations are shuffles: reversible moves only — exactly
        // PileStack of unlocked cards (the locked variant is a reveal,
        // a commitment) plus StackPile. Iterated straight from the two
        // masks in the same card order `to_vec` would produce, skipping
        // the full move-list materialization and per-move `reverse_move`
        // lookups.
        let locked_now = state.get_hidden().get_locked_mask();
        let mut edges = mv.pile_stack & !locked_now;
        let mut is_pile = true;
        loop {
            if edges == 0 {
                if is_pile {
                    edges = mv.stack_pile;
                    is_pile = false;
                    continue;
                }
                break;
            }
            let bit = edges & edges.wrapping_neg();
            edges &= !bit;
            let c = Card::from_mask_index(u8::try_from(bit.trailing_zeros()).unwrap());
            let m = if is_pile {
                Move::PileStack(c)
            } else {
                Move::StackPile(c)
            };
            let (_, (undo, _)) = state.do_move(m);
            let enc = state.encode();
            if seen.insert(enc) {
                let child = arena.len();
                arena.push((idx, m, (depth + 1) as u16));
                queue.push_back((state.clone(), child));
            }
            state.undo_move(m, undo);
        }
    }
    answers
        .into_iter()
        .map(|ans| {
            ans.map(|idx| {
                let mut steps = Vec::new();
                let mut i = idx;
                while i != 0 {
                    let (parent, mv, _) = arena[i];
                    steps.push(mv);
                    i = parent;
                }
                steps.reverse();
                steps
            })
        })
        .collect()
}

/// Apply `m`, canonicalize the result, and return the successor state.
/// All inputs come from legality checks against the same pre-state — those
/// checks are type-level, and where a twin is ambiguous the move is legal
/// in the arrangement-existential sense (no_pile_to_pile.md §3/§6.5:
/// a set bit means *some* realizing arrangement has the card uncovered).
/// Note `do_move` itself carries no validity guard, so the mask checks at
/// the call sites are the only guard.
fn post_state(g: &Solitaire, steps: &[Move]) -> Solitaire {
    #[cfg(test)]
    perf_probe::bump_post(steps.len() as u64);
    let mut next = g.clone();
    for &m in steps {
        let _ = next.do_move(m);
    }
    canonicalize(&mut next);
    next
}

/// The §6.4 rule list, probed directly (no closure search). For each
/// commitment, try in order: direct placement, dig (vacate `twin(X)`), and
/// borrow (worry a foundation-top parent back). Each successful channel
/// produces one canonical post-state via `post_state`.
///
/// v1 deliberate gaps, surfaced by the differential test below: chained
/// borrows (borrow chains of depth > 1) and prefix-raising for the stack
/// outcome (§6.4's stack-side analogue of the dig).
/// The channel that produced a direct outcome — recorded for the
/// differential test's failure forensics.
pub type DirectTransition = (Commitment, OutcomeKind, Solitaire, &'static str);

/// The §6.4 rule list evaluated to *steps*: (commitment, outcome kind,
/// accommodation steps + the realizing commit move, channel). Steps, not
/// states, so the search-facing fold (`macro_transitions_fast`) can drop
/// dominated outcomes before paying for a `post_state` clone.
type StepTransition = (Commitment, OutcomeKind, ArrayVec<Move, 14>, &'static str);

fn steps(ms: &[Move]) -> ArrayVec<Move, 14> {
    let mut a = ArrayVec::new();
    for &m in ms {
        a.push(m);
    }
    a
}

/// The rule list proper: one entry per (commitment, channel) that opens,
/// grouped per commitment (adjacent in the flattened vec — the
/// differential's kind-fold relies on it). See `macro_transitions_direct`
/// for the channel documentation. Working buffers come from `scratch`
/// (reused across nodes, cleared not reallocated).
fn macro_transitions_core(g: &Solitaire, scratch: &mut DirectScratch) -> Solitaire {
    let mut game = g.clone();
    canonicalize(&mut game);
    let mv = game.gen_moves::<false>();
    let deck_mask = game.get_deck().compute_mask(false);
    let locked = game.get_hidden().get_locked_mask();
    let locked_surfaces = game.get_visible_mask() & locked;

    // enumerate commitments: every locked surface first, then every
    // drawable deck card — reveal before draw, mirroring the old engine's
    // raw move order (`MoveMask::iter_moves` tries `Reveal` before any
    // deck move). Measured search order, not just aesthetics: draw-first
    // buries reveal-led winning lines under draw-subgame refutations
    // (seed 18 draw 1: 96k nodes draw-first vs 84 reveal-first, see
    // `macro_verdict_perf_probe`).
    let mut commitments: Vec<Commitment> = Vec::new();
    let mut bits = locked_surfaces;
    while bits != 0 {
        let bit = bits & bits.wrapping_neg();
        bits &= !bit;
        commitments.push(Commitment::Reveal(Card::from_mask_index(
            u8::try_from(bit.trailing_zeros()).unwrap(),
        )));
    }
    let mut bits = deck_mask;
    while bits != 0 {
        let bit = bits & bits.wrapping_neg();
        bits &= !bit;
        commitments.push(Commitment::Draw(Card::from_mask_index(
            u8::try_from(bit.trailing_zeros()).unwrap(),
        )));
    }

    // reset the reused buffers: per-commitment groups, goal list
    let n_groups = commitments.len();
    scratch.groups.truncate(n_groups);
    while scratch.groups.len() < n_groups {
        scratch.groups.push(Vec::new());
    }
    for grp in &mut scratch.groups {
        grp.clear();
    }
    scratch.goals.clear();
    let groups = &mut scratch.groups;
    let goals = &mut scratch.goals;
    for (ci, &commitment) in commitments.iter().enumerate() {
        let (x, stack_move, direct_move) = match commitment {
            Commitment::Draw(x) => (x, Move::DeckStack(x), Move::DeckPile(x)),
            Commitment::Reveal(x) => (x, Move::PileStack(x), Move::Reveal(x)),
        };
        let xmask = x.mask();

        // stack outcome
        let stack_now = match commitment {
            Commitment::Draw(_) => mv.deck_stack & xmask != 0,
            Commitment::Reveal(_) => mv.pile_stack & xmask != 0,
        };
        // channel order matters: every channel is independent,
        // and no channel is allowed to skip the tableau channels
        if stack_now {
            groups[ci].push((
                commitment,
                OutcomeKind::Stack,
                steps(&[stack_move]),
                "stack-direct",
            ));
        }

        // tableau outcome, direct channel
        let direct_now = match commitment {
            Commitment::Draw(_) => mv.deck_pile & xmask != 0,
            Commitment::Reveal(_) => mv.reveal & xmask != 0,
        };
        if direct_now {
            groups[ci].push((
                commitment,
                OutcomeKind::Tableau,
                steps(&[direct_move]),
                "tableau-direct",
            ));
        }

        // stack-side channels. Prefix-raise: stack the missing same-suit
        // prefix cards until X becomes stackable. If the prefix is already
        // complete, the BFS fallback handles the "X needs an unrelated
        // shuffle to unblock" cases (e.g. a buried surface king).
        // Per-commitment scratch state: one clone, with do/undo inside —
        // no per-step state copies.
        let suit = x.suit();
        let mut stack_produced = stack_now;
        if !stack_now && game.get_stack().get(suit) < x.rank() {
            // the probe dies on its first iteration unless the first
            // missing prefix card is stackable and unlocked at the root —
            // check that before paying for the clone + gen_moves (the
            // profiled gen_moves hot spot: most probes die here)
            let first = Card::new(game.get_stack().get(suit), suit);
            if mv.pile_stack & first.mask() != 0 && locked & first.mask() == 0 {
                let mut probe = game.clone();
                let mut steps: Vec<Move> = Vec::new();
                let mut undos: Vec<crate::state::UndoInfo> = Vec::new();
                let mut reachable = true;
                loop {
                    let need = probe.get_stack().get(suit);
                    if need >= x.rank() {
                        break;
                    }
                    let c2 = Card::new(need, suit);
                    let c2m = c2.mask();
                    let pmv = probe.gen_moves::<false>();
                    let locked_now = probe.get_hidden().get_locked_mask();
                    if pmv.pile_stack & c2m != 0 && locked_now & c2m == 0 {
                        let m2 = Move::PileStack(c2);
                        let (_, (undo, _)) = probe.do_move(m2);
                        steps.push(m2);
                        undos.push(undo);
                    } else {
                        reachable = false;
                        break;
                    }
                }
                if reachable {
                    let pmv = probe.gen_moves::<false>();
                    let stack_ok = match commitment {
                        Commitment::Draw(_) => pmv.deck_stack & xmask != 0,
                        Commitment::Reveal(_) => pmv.pile_stack & xmask != 0,
                    };
                    if stack_ok {
                        // rebuild from the untouched base: probe is dirty
                        steps.push(stack_move);
                        groups[ci].push((
                            commitment,
                            OutcomeKind::Stack,
                            steps.into_iter().collect(),
                            "stack-prefix-raise",
                        ));
                        stack_produced = true;
                    }
                }
                // probe is discarded whole; `game` was never touched
                let _ = undos;
            }
        }
        if !stack_produced && !stack_now {
            // (the blockers of X are two twins and each may need its own
            // dig; the shared bounded BFS below catches the chains the
            // fixed rules don't name. Gate: only when no fixed channel
            // produced a stack outcome — running it after a successful
            // prefix-raise would hunt for the *second* stack scar class
            // (the same-kind splits of §6.7) but multiplies the per-node
            // cost badly. The residual under-emission is measured instead:
            // the class-coverage metric in macro_direct_matches_oracle.)
            goals.push(AccommodationGoal {
                commitment,
                kind: OutcomeKind::Stack,
                xmask,
                commit_move: stack_move,
                cap: 12,
            });
        }

        // dig/borrow only make sense with a parent class: skip for kings
        if x.rank() == crate::card::KING_RANK {
            continue;
        }

        // dig channel: vacate twin(X) onto a foundation if it is the
        // (uniquely possible) coverer of a parent top. do/undo on the base
        // state; only produce a fresh clone when the channel opens.
        let twin = x.swap_suit();
        let twin_mask = twin.mask();
        if locked & twin_mask == 0 && mv.pile_stack & twin_mask != 0 {
            let mv_twin = Move::PileStack(twin);
            let (_, (undo, _)) = game.do_move(mv_twin);
            let pmv = game.gen_moves::<false>();
            let opens = match commitment {
                Commitment::Draw(_) => pmv.deck_pile & xmask != 0,
                Commitment::Reveal(_) => pmv.reveal & xmask != 0,
            };
            game.undo_move(mv_twin, undo);
            if opens {
                groups[ci].push((
                    commitment,
                    OutcomeKind::Tableau,
                    steps(&[mv_twin, direct_move]),
                    "tableau-dig",
                ));
            }
        }

        // borrow channel(s): a parent on its foundation top, worry-back-able.
        // do/undo on the base state; produce only when the channel opens.
        let r = x.rank();
        let s = x.suit();
        for p in [Card::new(r + 1, s ^ 2), Card::new(r + 1, s ^ 3)] {
            let on_foundation_top = game.get_stack().get(p.suit()) == p.rank().saturating_add(1);
            if !(on_foundation_top
                && locked & p.mask() == 0
                && mv.stack_pile & p.mask() != 0)
            {
                continue;
            }
            let mv_b = Move::StackPile(p);
            let (_, (undo, _)) = game.do_move(mv_b);
            let pmv = game.gen_moves::<false>();
            let opens = match commitment {
                Commitment::Draw(_) => pmv.deck_pile & xmask != 0,
                Commitment::Reveal(_) => pmv.reveal & xmask != 0,
            };
            game.undo_move(mv_b, undo);
            if opens {
                groups[ci].push((
                    commitment,
                    OutcomeKind::Tableau,
                    steps(&[mv_b, direct_move]),
                    "tableau-borrow",
                ));
            }
        }

        // fallback channel: the shared bounded BFS below (catches the
        // chained borrow/dig crease; the differential reports how often
        // it fires)
        if !direct_now {
            goals.push(AccommodationGoal {
                commitment,
                kind: OutcomeKind::Tableau,
                xmask,
                commit_move: direct_move,
                cap: 10,
            });
        }
    }

    // pass 2: one shared BFS from the same root answers every goal the
    // fixed channels left open (the per-commitment BFS's this replaces
    // re-explored the same closure ~16x per node, 96%+ of calls failing;
    // witness choice is unchanged — first opening in level order). Each
    // result is appended to its commitment's group, keeping every
    // commitment's emissions adjacent in the flattened output.
    if !goals.is_empty() {
        for (goal, witness) in goals
            .iter()
            .zip(accommodations_shared(&game, mv, goals, &mut scratch.bfs))
        {
            if let Some(mut steps) = witness {
                steps.push(goal.commit_move);
                let channel = match goal.kind {
                    OutcomeKind::Stack => "stack-bfs",
                    OutcomeKind::Tableau => "tableau-bfs",
                };
                let ci = commitments
                    .iter()
                    .position(|c| *c == goal.commitment)
                    .expect("goal commitment comes from the enumeration");
                groups[ci].push((goal.commitment, goal.kind, steps.into_iter().collect(), channel));
            }
        }
    }
    game
}

/// The §6.4 rule list, probed directly (no closure search). For each
/// commitment, try in order: direct placement, dig (vacate `twin(X)`), and
/// borrow (worry a foundation-top parent back). Each successful channel
/// produces one canonical post-state via `post_state`.
///
/// v1 deliberate gaps, surfaced by the differential test below: chained
/// borrows (borrow chains of depth > 1) and prefix-raising for the stack
/// outcome (§6.4's stack-side analogue of the dig).
/// The channel that produced a direct outcome — recorded for the
/// differential test's failure forensics.
#[must_use]
pub fn macro_transitions_direct(g: &Solitaire) -> Vec<DirectTransition> {
    let mut scratch = DirectScratch::new();
    let game = macro_transitions_core(g, &mut scratch);
    // materialize per group with the (commitment, kind, encode) dedup
    let mut out: Vec<DirectTransition> = Vec::new();
    for group in &scratch.groups {
        for (commitment, kind, steps, channel) in group {
            let state = post_state(&game, steps);
            let enc = state.encode();
            if !out.iter().any(|(c, k, s, _)| {
                *c == *commitment && *k == *kind && s.encode() == enc
            }) {
                out.push((*commitment, *kind, state, *channel));
            }
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::shuffler::default_shuffle;
    use crate::solver::{solve, SearchResult};
    use core::num::NonZeroU8;
    use crate::pruning::{FullPruner, NoPruner, Pruner};
    use crate::traverse::{traverse, Callback, Control};

    /// A/B the shared multi-goal BFS against the old per-goal BFS at the
    /// differential's first-missing states: any witness divergence is a
    /// bug in the shared version.
    #[test]
    #[ignore = "forensic A/B; run with --ignored --nocapture"]
    fn debug_shared_bfs_ab() {
        // the old per-goal BFS, verbatim, for comparison
        fn bfs_old(
            g: &Solitaire,
            commitment: Commitment,
            x: Card,
            goal_kind: OutcomeKind,
            max_depth: usize,
        ) -> Option<Vec<Move>> {
            use alloc::collections::VecDeque;
            let xmask = x.mask();
            let mut queue: VecDeque<(Solitaire, Vec<Move>)> = VecDeque::new();
            queue.push_back((g.clone(), Vec::new()));
            let mut seen = TpTable::default();
            seen.insert(g.encode());
            while let Some((state, steps)) = queue.pop_front() {
                if steps.len() >= max_depth {
                    continue;
                }
                let mv = state.gen_moves::<false>();
                let opens = match (commitment, goal_kind) {
                    (Commitment::Draw(_), OutcomeKind::Tableau) => mv.deck_pile & xmask != 0,
                    (Commitment::Reveal(_), OutcomeKind::Tableau) => mv.reveal & xmask != 0,
                    (Commitment::Draw(_), OutcomeKind::Stack) => mv.deck_stack & xmask != 0,
                    (Commitment::Reveal(_), OutcomeKind::Stack) => mv.pile_stack & xmask != 0,
                };
                if opens {
                    return Some(steps);
                }
                for m in mv.to_vec::<N_MOVES_MAX>() {
                    if state.reverse_move(m).is_none() {
                        continue;
                    }
                    let mut next = state.clone();
                    let _ = next.do_move(m);
                    let enc = next.encode();
                    if seen.insert(enc) {
                        let mut s2 = steps.clone();
                        s2.push(m);
                        queue.push_back((next, s2));
                    }
                }
            }
            None
        }
        for (seed, turn, draw_step, card_idx, is_draw) in [
            (34u64, 17usize, 1u8, 3u8, false),
            (34, 17, 3, 3, false),
            (12, 38, 1, 38, true),
            (12, 38, 3, 38, true),
            (40, 20, 1, 1, true),
            (40, 20, 3, 1, true),
        ] {
            let mut game = Solitaire::new(
                &default_shuffle(seed),
                NonZeroU8::new(draw_step).unwrap(),
            );
            for _ in 0..turn {
                if game.is_win() {
                    break;
                }
                canonicalize(&mut game);
                let oracle = enumerate_commitments(&game);
                if oracle.is_empty() {
                    break;
                }
                for &m in &oracle[0].witness_path {
                    let _ = game.do_move(m);
                }
            }
            canonicalize(&mut game);
            let x = Card::from_mask_index(card_idx);
            let commitment = if is_draw {
                Commitment::Draw(x)
            } else {
                Commitment::Reveal(x)
            };
            if !enumerate_commitments(&game)
                .iter()
                .any(|c| c.commitment == commitment)
            {
                println!("seed={seed} draw={draw_step} turn={turn}: {commitment:?} not offered here");
                continue;
            }
            let old = bfs_old(&game, commitment, x, OutcomeKind::Tableau, 10);
            let goal = [AccommodationGoal {
                commitment,
                kind: OutcomeKind::Tableau,
                xmask: x.mask(),
                commit_move: Move::Reveal(x),
                cap: 10,
            }];
            let root_mv = game.gen_moves::<false>();
            let mut bfs_scratch = DirectScratch::new();
            let new = accommodations_shared(&game, root_mv, &goal, &mut bfs_scratch.bfs);
            let direct_channels: Vec<&'static str> = macro_transitions_direct(&game)
                .iter()
                .filter(|(c, _, _, _)| *c == commitment)
                .map(|(_, _, _, ch)| *ch)
                .collect();
            println!(
                "seed={seed} draw={draw_step} turn={turn} {commitment:?}: old={old:?} new={new:?} channels={direct_channels:?}"
            );
        }
    }

    /// Hang forensics for the big verdict sweep: characterize a seed the
    /// sweep stalls on. All macro runs are node-capped (capped=true means
    /// "at least this many nodes", not a verdict).
    #[test]
    #[ignore = "hang forensics; run with --ignored --release --nocapture"]
    fn debug_big_sweep_hang() {
        const NODE_CAP: usize = 3_000_000;
        for (seed, draw_step) in [(32u64, 1u8), (32, 3)] {
            let cards = default_shuffle(seed);
            let step = NonZeroU8::new(draw_step).unwrap();

            // direct first (it is the sweep's path), node-capped
            {
                fn rec(
                    s: &Solitaire,
                    tp: &mut TpTable,
                    nodes: &mut usize,
                    branches: &mut usize,
                    capped: &mut bool,
                ) -> bool {
                    if s.is_win() || !tp.insert(s.encode()) {
                        return s.is_win();
                    }
                    *nodes += 1;
                    if *nodes > NODE_CAP {
                        *capped = true;
                        return false;
                    }
                    let succs = macro_transitions_fast(s);
                    *branches += succs.len();
                    succs
                        .into_iter()
                        .any(|(_, succ)| rec(&succ, tp, nodes, branches, capped))
                }
                perf_probe::reset();
                let t = std::time::Instant::now();
                let mut tp = TpTable::default();
                let (mut n, mut b) = (0usize, 0usize);
                let mut capped = false;
                let mut root = Solitaire::new(&cards, step);
                canonicalize(&mut root);
                let w = rec(&root, &mut tp, &mut n, &mut b, &mut capped);
                println!(
                    "seed={seed} draw={draw_step} DIRECT win={w} nodes={n} branches={b} avg_branch={:5.2} capped={} total={:?} probes={:?}",
                    b as f64 / n.max(1) as f64,
                    capped,
                    t.elapsed(),
                    perf_probe::read()
                );
            }

            // oracle, node-capped
            {
                fn rec(
                    g: &Solitaire,
                    tp: &mut TpTable,
                    nodes: &mut usize,
                    branches: &mut usize,
                    capped: &mut bool,
                ) -> bool {
                    let mut s = g.clone();
                    canonicalize(&mut s);
                    if s.is_win() || !tp.insert(s.encode()) {
                        return s.is_win();
                    }
                    *nodes += 1;
                    if *nodes > NODE_CAP {
                        *capped = true;
                        return false;
                    }
                    let succs = enumerate_transitions(&s);
                    *branches += succs.len();
                    succs
                        .into_iter()
                        .any(|(_, succ)| rec(&succ, tp, nodes, branches, capped))
                }
                let t = std::time::Instant::now();
                let mut tp = TpTable::default();
                let (mut n, mut b) = (0usize, 0usize);
                let mut capped = false;
                let w = rec(&Solitaire::new(&cards, step), &mut tp, &mut n, &mut b, &mut capped);
                println!(
                    "seed={seed} draw={draw_step} ORACLE win={w} nodes={n} branches={b} avg_branch={:5.2} capped={} total={:?}",
                    b as f64 / n.max(1) as f64,
                    capped,
                    t.elapsed()
                );
            }

            // old engine reference
            {
                let t = std::time::Instant::now();
                let mut game = Solitaire::new(&cards, step);
                let (res, hist) = solve(&mut game);
                let len = hist.map_or(0, |h| h.len());
                println!(
                    "seed={seed} draw={draw_step} OLD win={res:?} winline={len} total={:?}",
                    t.elapsed()
                );
            }
        }
    }

    /// Structural characterization of a seed: root commitment surface and
    /// the old engine's 2x2 refutation cost.
    #[test]
    #[ignore = "forensics; run with --ignored --release --nocapture"]
    fn debug_seed_types() {
        const BUDGET: u64 = 20_000_000;
        struct P {
            won: bool,
            visits: u64,
            nodes: u64,
            budget: bool,
        }
        fn run_old<const DOM: bool, PR: Pruner + Default>(cards: &[Card; 52], step: NonZeroU8) -> P {
            struct C<P2: Pruner + Default> {
                won: bool,
                visits: u64,
                nodes: u64,
                budget: bool,
                m: core::marker::PhantomData<P2>,
            }
            impl<P2: Pruner + Default> Callback for C<P2> {
                type Pruner = P2;
                fn on_win(&mut self, _: &Solitaire) -> Control {
                    self.won = true;
                    Control::Halt
                }
                fn on_visit(&mut self, _: &Solitaire, _: Encode) -> Control {
                    self.visits += 1;
                    if self.visits > BUDGET {
                        self.budget = true;
                        return Control::Halt;
                    }
                    Control::Ok
                }
                fn on_move_gen(&mut self, m: &crate::moves::MoveMask, _: Encode) -> Control {
                    self.nodes += 1;
                    let _ = m.len();
                    Control::Ok
                }
            }
            let mut game = Solitaire::new(cards, step);
            let mut tp = TpTable::default();
            let mut c = C::<PR> {
                won: false,
                visits: 0,
                nodes: 0,
                budget: false,
                m: core::marker::PhantomData,
            };
            traverse::<_, _, DOM>(&mut game, &PR::default(), &mut tp, &mut c);
            P { won: c.won, visits: c.visits, nodes: c.nodes, budget: c.budget }
        }
        for seed in [12u64, 21, 22, 32] {
            for draw_step in [1u8, 3] {
                let cards = default_shuffle(seed);
                let step = NonZeroU8::new(draw_step).unwrap();
                let mut g = Solitaire::new(&cards, step);
                canonicalize(&mut g);
                let mv = g.gen_moves::<false>();
                let deck = g.get_deck().compute_mask(false).count_ones();
                let locked_surfaces = (g.get_visible_mask() & g.get_hidden().get_locked_mask()).count_ones();
                println!(
                    "seed={seed} draw={draw_step}: root drawables={deck} locked_surfaces={locked_surfaces} stack={:x} raw_moves={}",
                    g.get_stack().encode(),
                    mv.len()
                );
                let t = std::time::Instant::now();
                let p = run_old::<true, FullPruner>(&cards, step);
                println!("  dom+pruner  win={} visits={:>10} nodes={:>10} budget={} {:?}", p.won, p.visits, p.nodes, p.budget, t.elapsed());
                let t = std::time::Instant::now();
                let p = run_old::<true, NoPruner>(&cards, step);
                println!("  dom-only    win={} visits={:>10} nodes={:>10} budget={} {:?}", p.won, p.visits, p.nodes, p.budget, t.elapsed());
                let t = std::time::Instant::now();
                let p = run_old::<false, FullPruner>(&cards, step);
                println!("  pruner-only win={} visits={:>10} nodes={:>10} budget={} {:?}", p.won, p.visits, p.nodes, p.budget, t.elapsed());
                let t = std::time::Instant::now();
                let p = run_old::<false, NoPruner>(&cards, step);
                println!("  raw         win={} visits={:>10} nodes={:>10} budget={} {:?}", p.won, p.visits, p.nodes, p.budget, t.elapsed());
            }
        }
    }

    /// F3 measurement: over the direct search's first N nodes, what
    /// fraction of folded successors are tableau outcomes of
    /// dominantly-stackable commitments (the §4 "additional collapsing"
    /// drop candidate)?
    #[test]
    #[ignore = "measurement; run with --ignored --release --nocapture"]
    fn debug_f3_potential() {
        const N: usize = 200_000;
        fn rec(
            s: &Solitaire,
            tp: &mut TpTable,
            nodes: &mut usize,
            branches: &mut usize,
            droppable: &mut usize,
        ) -> bool {
            if s.is_win() || !tp.insert(s.encode()) {
                return s.is_win();
            }
            *nodes += 1;
            if *nodes > N {
                return false;
            }
            let mut root = s.clone();
            canonicalize(&mut root);
            let dom = root.get_stack().dominance_mask();
            let all = macro_transitions_direct(&root);
            // commitments with a direct stack outcome now: X stackable
            let stack_now: u64 = all
                .iter()
                .filter(|(_, _, _, ch)| *ch == "stack-direct")
                .map(|(c, _, _, _)| match c {
                    Commitment::Draw(x) | Commitment::Reveal(x) => x.mask(),
                })
                .fold(0u64, |a, b| a | b);
            let f3_mask = stack_now & dom;
            let mut seen: Vec<(Commitment, OutcomeKind)> = Vec::new();
            let mut succs: Vec<&Solitaire> = Vec::new();
            for (c, k, st, _) in &all {
                if !seen.contains(&(*c, *k)) {
                    seen.push((*c, *k));
                    succs.push(st);
                }
            }
            *branches += succs.len();
            for (c, k, _, _) in &all {
                let _ = c;
                if *k == OutcomeKind::Tableau {
                    let x = match c {
                        Commitment::Draw(x) | Commitment::Reveal(x) => *x,
                    };
                    if x.mask() & f3_mask != 0 {
                        *droppable += 1;
                    }
                }
            }
            succs
                .into_iter()
                .any(|succ| rec(succ, tp, nodes, branches, droppable))
        }
        for (seed, draw_step) in [(32u64, 1u8), (32, 3), (14, 1), (13, 3), (21, 3)] {
            let cards = default_shuffle(seed);
            let step = NonZeroU8::new(draw_step).unwrap();
            let mut root = Solitaire::new(&cards, step);
            canonicalize(&mut root);
            let mut tp = TpTable::default();
            let (mut n, mut b, mut d) = (0usize, 0usize, 0usize);
            let t = std::time::Instant::now();
            let w = rec(&root, &mut tp, &mut n, &mut b, &mut d);
            println!(
                "seed={seed} draw={draw_step} win={w} nodes={n} branches={b} f3_droppable={d} ({:5.1}%) total={:?}",
                100.0 * d as f64 / b.max(1) as f64,
                t.elapsed()
            );
        }
    }

    /// Deterministic replay harness: bring a specific game to a specific
    /// turn by the same greedy play policy as the differential test, then
    /// dump the direct generator's per-channel evaluation per commitment.
    #[cfg(test)]
    fn debug_replay(seed: u64, draw_step: u8, turns: usize) {
        let mut game = Solitaire::new(&default_shuffle(seed), NonZeroU8::new(draw_step).unwrap());
        for _ in 0..turns {
            canonicalize(&mut game);
            let oracle = enumerate_commitments(&game);
            if oracle.is_empty() {
                break;
            }
            for &m in &oracle[0].witness_path {
                let _ = game.do_move(m);
            }
        }
        canonicalize(&mut game);
        let mv = game.gen_moves::<false>();
        println!("root encode: {:x}", game.encode());
        println!(
            "masks: pile_stack={:#x} deck_pile={:#x} reveal={:#x} deck_stack={:#x} stack_pile={:#x}",
            mv.pile_stack, mv.deck_pile, mv.reveal, mv.deck_stack, mv.stack_pile
        );
        let direct = macro_transitions_direct(&game);
        println!(
            "direct: {:?}",
            direct.iter().map(|(c, k, _, ch)| (c, k, ch)).collect::<Vec<_>>()
        );
        // specific check
        let x = Card::from_mask_index(8);
        let locked = game.get_hidden().get_locked_mask();
        println!(
            "card8: locked={} visible={} reveal_bit={}",
            locked & x.mask() != 0,
            game.get_visible_mask() & x.mask() != 0,
            mv.reveal & x.mask() != 0
        );
    }

    /// Trace `macro_transitions_direct` for one commitment at the replayed
    /// state: prints every channel's guard evaluation so the exact failed
    /// conjunct is visible.
    #[cfg(test)]
    fn debug_trace(game0: &Solitaire, target: Card) {
        let mut game = game0.clone();
        canonicalize(&mut game);
        let mv = game.gen_moves::<false>();
        let xmask = target.mask();
        println!("TRACE for {target:?} (mask {:#x}):", xmask);
        println!("  masks: pile_stack={:#x} deck_pile={:#x} reveal={:#x} deck_stack={:#x} stack_pile={:#x}", 
            mv.pile_stack, mv.deck_pile, mv.reveal, mv.deck_stack, mv.stack_pile);
        println!("  stack_now={} direct_now={}", 
            mv.pile_stack & xmask != 0, mv.reveal & xmask != 0);
        println!("  stack heights: {:?}", [game.get_stack().get(0), game.get_stack().get(1), game.get_stack().get(2), game.get_stack().get(3)]);
        println!("  x.suit()={} x.rank()={}", target.suit(), target.rank());
        let locked = game.get_hidden().get_locked_mask();

        // pile anatomy: which pile holds target, what's under it
        let hidden = game.get_hidden();
        for pos in 0..crate::deck::N_PILES {
            let pile = hidden.get(pos);
            for (i, c) in pile.iter().enumerate() {
                if *c == target || c.swap_suit() == target {
                    println!(
                        "  pile {pos} card {i}/{}: {c:?} {} (locked_mask has {})",
                        pile.len(),
                        if *c == target { "<-- target" } else { "(twin)" },
                        locked & target.mask() != 0
                    );
                }
            }
        }
        for pos in 0..crate::deck::N_PILES {
            let pile = hidden.get(pos);
            if pile.contains(&target) {
                let idx = pile.iter().position(|c| *c == target).unwrap();
                println!(
                    "  pile {pos}: target at depth {}/{}; cards above: {:?}",
                    idx,
                    pile.len() - 1,
                    &pile[idx + 1..]
                );
            }
        }

        // prefix raise probe
        let suit = target.suit();
        let mut probe = game.clone();
        let mut steps = 0;
        loop {
            let need = probe.get_stack().get(suit);
            if need >= target.rank() { break; }
            let c2 = Card::new(need, suit);
            let pmv = probe.gen_moves::<false>();
            let locked_now = probe.get_hidden().get_locked_mask();
            println!("  prefix step {}: c2={:?} in_pile_stack={} locked={} visible={}", 
                steps, c2,
                pmv.pile_stack & c2.mask() != 0,
                locked_now & c2.mask() != 0,
                probe.get_visible_mask() & c2.mask() != 0);
            if !(pmv.pile_stack & c2.mask() != 0 && locked_now & c2.mask() == 0) {
                println!("  prefix chain breaks here"); break;
            }
            let _ = probe.do_move(Move::PileStack(c2));
            steps += 1;
            if steps > 13 { break; }
        }
        let pmv = probe.gen_moves::<false>();
        println!("  after prefix: pile_stack_has_x={}", pmv.pile_stack & xmask != 0);
        // decompose pile_stack conjuncts for the target
        let bm = game.get_bottom_mask();
        let vis = game.get_visible_mask();
        let sm = game.get_stack().mask();
        println!(
            "  pile_stack conjuncts for {target:?}: bm({:#x})={} sm({:#x})={} vis={} locked={}",
            bm,
            bm & xmask != 0,
            sm,
            sm & xmask != 0,
            vis & xmask != 0,
            locked & xmask != 0,
        );
    }

    #[test]
    #[ignore = "forensic print harness: run only when diagnosing a differential miss"]
    fn debug_trace_reveal51() {
        // seed 26, turn 49's failing state: replay it, then trace
        let mut game = Solitaire::new(&default_shuffle(26), NonZeroU8::new(1).unwrap());
        for _turn in 0..49 {
            canonicalize(&mut game);
            let oracle = enumerate_commitments(&game);
            if oracle.is_empty() { break; }
            for &m in &oracle[0].witness_path {
                let _ = game.do_move(m);
            }
        }
        debug_trace(&game, Card::from_mask_index(51));
    }

    #[test]
    #[ignore = "forensic print harness: run only when diagnosing a differential miss"]
    fn debug_replay_seed12_turn5() {
        debug_replay(12, 1, 5);
    }

    #[test]
    #[ignore = "forensic print harness: run only when diagnosing a differential miss"]
    fn debug_replay_seed26_turn49() {
        debug_replay(26, 1, 49);
        // Where is the K of suit 0 (mask index 48) in this state, and why
        // did the direct generator produce nothing for it?
        let mut game = Solitaire::new(&default_shuffle(26), NonZeroU8::new(1).unwrap());
        for _ in 0..49 {
            canonicalize(&mut game);
            let oracle = enumerate_commitments(&game);
            if oracle.is_empty() {
                break;
            }
            for &m in &oracle[0].witness_path {
                let _ = game.do_move(m);
            }
        }
        canonicalize(&mut game);
        let x = Card::from_mask_index(48);
        let xq = Card::from_mask_index(46);
        let locked = game.get_hidden().get_locked_mask();
        println!(
            "card48: locked={} visible={} ; card46: locked={} visible={}",
            locked & x.mask() != 0,
            game.get_visible_mask() & x.mask() != 0,
            locked & xq.mask() != 0,
            game.get_visible_mask() & xq.mask() != 0,
        );
        let hidden = game.get_hidden();
        for pos in 0..crate::deck::N_PILES {
            let pile = hidden.get(pos);
            if pile.contains(&x) || pile.contains(&xq) {
                println!(
                    "  pile {pos}: surface={:?} buried contains target={} prefix={}",
                    pile.last(),
                    pile.contains(&x),
                    pile.contains(&xq)
                );
            }
        }
    }

    /// Reproduce the prefix-raise probe with full legality diagnostics:
    /// for each step, print the needed card, the raw pile_stack bit, the
    /// locked bit, and whether the move validated.
    #[cfg(test)]
    fn debug_prefix_probe(g: &Solitaire, x: Card) {
        let suit = x.suit();
        let mut probe = g.clone();
        println!("    prefix probe for {x:?}: suit f0={}", probe.get_stack().get(suit));
        loop {
            let need = probe.get_stack().get(suit);
            if need >= x.rank() {
                println!("    reached rank({need})");
                break;
            }
            let c2 = Card::new(need, suit);
            let pmv = probe.gen_moves::<false>();
            let locked_now = probe.get_hidden().get_locked_mask();
            let in_ps = pmv.pile_stack & c2.mask() != 0;
            let is_locked = locked_now & c2.mask() != 0;
            let twin_in_vis = probe.get_visible_mask() & c2.swap_suit().mask() != 0;
            println!(
                "    need={need} c2={c2:?} in_ps={in_ps} locked={is_locked} twin_visible={twin_in_vis} stack_before={:#x}",
                probe.get_stack().mask()
            );
            if !(in_ps && !is_locked) {
                println!("    stop: unreachable prefix card");
                break;
            }
            let _ = probe.do_move(Move::PileStack(c2));
        }
    }

    /// The design falsifier of §6.6: per commitment, the direct rule-driven
    /// generator must offer exactly the outcome kinds the closure oracle
    /// finds. Divergences; assert none in either direction.
    #[test]
    fn macro_direct_matches_oracle() {
        std::thread::Builder::new()
            .stack_size(256 * 1024 * 1024)
            .spawn(|| {
                let mut checked = 0usize;
                let mut missing = 0usize; // oracle has, direct lacks
                let mut extra = 0usize; // direct has, oracle lacks (a legality bug by construction)
                let mut extra_merged = 0usize; // extra, but closure-connected to oracle samples (benign)
                let mut extra_separate = 0usize; // extra and disconnected (a real soundness question)
                let mut class_uncovered = 0usize; // oracle closure classes no direct post-state covers
                let mut first_missing: Option<String> = None;
                let mut first_extra: Option<String> = None;
                let mut missing_cases: Vec<String> = Vec::new();
                let mut first_missing_state: Option<(Solitaire, Commitment)> = None;
                let mut channel_histogram: std::collections::BTreeMap<&'static str, usize> =
                    std::collections::BTreeMap::new();
                for draw_step in [1u8, 3] {
                    for i in 0..30u64 {
                        let mut game = Solitaire::new(
                            &default_shuffle(12 + i),
                            NonZeroU8::new(draw_step).unwrap(),
                        );
                        for _turn in 0..200 {
                            if game.is_win() {
                                break;
                            }
                            canonicalize(&mut game);
                            let oracle = enumerate_commitments(&game);
                            if oracle.is_empty() {
                                break;
                            }
                            let direct = macro_transitions_direct(&game);

                            let mut oracle_kinds: Vec<(Commitment, bool, bool)> = oracle
                                .iter()
                                .map(|c| {
                                    (
                                        c.commitment,
                                        !c.outcomes.canon_tableau.is_empty(),
                                        !c.outcomes.canon_stack.is_empty(),
                                    )
                                })
                                .collect();
                            oracle_kinds.sort_by_key(|(c, ..)| c.sort_key());
                            let mut direct_kinds: Vec<(Commitment, bool, bool)> = direct
                                .iter()
                                .map(|(c, k, _, _)| (*c, *k == OutcomeKind::Tableau, *k == OutcomeKind::Stack))
                                .collect();
                            for (_, _, _, ch) in &direct {
                                *channel_histogram.entry(*ch).or_insert(0) += 1;
                            }
                            // fold per commitment
                            let mut folded: Vec<(Commitment, bool, bool)> = Vec::new();
                            for (c, tab, stak) in direct_kinds.drain(..) {
                                match folded.last_mut() {
                                    Some(last) if last.0 == c => {
                                        last.1 |= tab;
                                        last.2 |= stak;
                                    }
                                    _ => folded.push((c, tab, stak)),
                                }
                            }
                            let mut direct_kinds = folded;
                            direct_kinds.sort_by_key(|(c, ..)| c.sort_key());

                            if oracle_kinds != direct_kinds {
                                // classify first divergence
                                for (c, o_tab, o_stak) in &oracle_kinds {
                                    let d = direct_kinds.iter().find(|(dc, ..)| dc == c);
                                    let (d_tab, d_stak) =
                                        d.map_or((false, false), |(_, t, s)| (*t, *s));
                                    if (*o_tab, *o_stak) != (d_tab, d_stak) {
                                        let witness = oracle
                                            .iter()
                                            .find(|i| i.commitment == *c)
                                            .map(|i| i.kind_witnesses.clone());
                                        let root_mv = game.gen_moves::<false>();
                                        let xx = match c {
                                            Commitment::Draw(xx) | Commitment::Reveal(xx) => xx,
                                        };
                                        let msg = format!(
                                            "commitment {c:?}: oracle=({o_tab},{o_stak}) direct=({d_tab},{d_stak}) at draw={draw_step} seed={} turn={_turn} root={:x}, witness={witness:?}, root masks: pile_stack={:#x} deck_pile={:#x} reveal={:#x} deck_stack={:#x} stack={:#x} stack_pile={:#x} locked={:#x} X_suit_height={} X_rank={}",
                                            12 + i,
                                            game.encode(),
                                            root_mv.pile_stack,
                                            root_mv.deck_pile,
                                            root_mv.reveal,
                                            root_mv.deck_stack,
                                            game.get_stack().mask(),
                                            root_mv.stack_pile,
                                            game.get_hidden().get_locked_mask(),
                                            game.get_stack().get(xx.suit()),
                                            xx.rank(),
                                        );
                                        if d.map_or(true, |_| false) || (!d_tab && !d_stak) || (!d_tab && *o_tab) || (!d_stak && *o_stak) {
                                            missing += 1;
                                            let [wit_t, wit_s] = &witness.clone().unwrap_or([None, None]);
                                            missing_cases.push(format!(
                                                "seed={} turn={_turn} {:?}(r{},s{}) o=({o_tab},{o_stak}) d=({d_tab},{d_stak}) tab_wit={:?} stack_wit={:?}",
                                                12 + i,
                                                c,
                                                xx.rank(),
                                                xx.suit(),
                                                wit_t,
                                                wit_s
                                            ));
                                            if first_missing.is_none() {
                                                first_missing = Some(msg);
                                            }
                                            if first_missing_state.is_none() {
                                                first_missing_state = Some((game.clone(), *c));
                                            }
                                        } else {
                                            extra += 1;
                                            if first_extra.is_none() {
                                                first_extra = Some(msg);
                                            }
                                        }
                                    }
                                }
                                for (c, d_tab, d_stak) in &direct_kinds {
                                    if !oracle_kinds.iter().any(|(oc, ..)| oc == c) {
                                        extra += 1;
                                        if first_extra.is_none() {
                                            first_extra = Some(format!(
                                                "commitment {c:?}: oracle=(false,false) direct=({d_tab},{d_stak}) at draw={draw_step} seed={}",
                                                12 + i
                                            ));
                                        }
                                    }
                                }
                            }
                            checked += oracle.len();

                            // two questions per extra event: (a) benign
                            // extras are closure-connected to the same
                            // commitment's oracle samples (merged classes,
                            // no unfound successor); (b) genuinely separate
                            // classes would be a real overreach of the rule
                            let mut merged = 0usize;
                            let mut separate = 0usize;
                            for (c, _, st, channel) in &direct {
                                let info = match oracle.iter().find(|i| i.commitment == *c) {
                                    Some(info) => info,
                                    None => continue,
                                };
                                let st_enc = st.encode();
                                let in_any = info
                                    .outcomes
                                    .canon_tableau
                                    .iter()
                                    .chain(info.outcomes.canon_stack.iter())
                                    .any(|(_, rep)| closure_contains(rep, st_enc));
                                if !in_any {
                                    // classify: is it at least closure-connected to *some*
                                    // oracle sample of the same commitment?
                                    separate += 1;
                                    if separate <= 6 {
                                        println!(
                                            "  EXTRA-SEPARATE draw={draw_step} seed={} commitment {c:?} channel={channel} direct-enc={st_enc:x}",
                                            12 + i
                                        );
                                        if *channel == "stack-prefix-raise" {
                                            let x = match c {
                                                Commitment::Draw(x) | Commitment::Reveal(x) => *x,
                                            };
                                            debug_prefix_probe(&game, x);
                                        }
                                    }
                                } else {
                                    merged += 1;
                                }
                            }
                            let _ = (merged, separate);
                            extra_merged += merged;
                            extra_separate += separate;

                            // class coverage: oracle closure classes that no
                            // direct post-state covers — the measured form
                            // of the under-emission the fixed gates accept
                            // (e.g. the second stack scar class when
                            // prefix-raise already fired). Target: zero.
                            for info in &oracle {
                                let mut reps: Vec<&Solitaire> = Vec::new();
                                for samples in
                                    [&info.outcomes.canon_tableau, &info.outcomes.canon_stack]
                                {
                                    for (enc, st) in samples.iter() {
                                        if !reps.iter().any(|r| closure_contains(r, *enc)) {
                                            reps.push(st);
                                        }
                                    }
                                }
                                let direct_states: Vec<&Solitaire> = direct
                                    .iter()
                                    .filter(|(c, _, _, _)| *c == info.commitment)
                                    .map(|(_, _, st, _)| st)
                                    .collect();
                                for rep in reps {
                                    let enc = rep.encode();
                                    if !direct_states.iter().any(|d| {
                                        d.encode() == enc || closure_contains(d, enc)
                                    }) {
                                        class_uncovered += 1;
                                    }
                                }
                            }

                            let before = game.encode();
                            for &m in &oracle[0].witness_path {
                                let _ = game.do_move(m);
                            }
                            assert_ne!(game.encode(), before);
                            assert!(game.is_valid());
                        }
                    }
                }
                println!("direct-vs-oracle: {checked} commitments checked; availability mismatches: missing={missing} extra={extra} (merged={extra_merged}, separate={extra_separate}); oracle classes uncovered by direct: {class_uncovered}");
                if let Some(m) = &first_missing {
                    println!("first missing: {m}");
                }
                if let Some(e) = &first_extra {
                    println!("first extra: {e}");
                }
                // extras are diagnosed not asserted here: an extra that is
                // closure-connected to oracle samples of the same commitment
                // is a benign duplicate-classes case; a separate one would
                // be a direct-generator overreach bug.
                //
                // `missing` is a corpus metric: the residual misses are the
                // declared §6.4 crease (chained digs/borrows of depth > 1),
                // whose witnesses the BFS fallback catches with increasing
                // depth — the number must trend to zero as the rule list
                // converges, and stays printed until it does.
                println!("availability-miss metric: {missing} (target 0; rule-list gap, not a search unsoundness)");
                println!("channel histogram (direct generator output share): {channel_histogram:?}");
                println!("all missing cases:");
                for case in &missing_cases {
                    println!("  MISS {case}");
                }
                if let Some((g, c)) = &first_missing_state {
                    let x = match c { Commitment::Draw(x) | Commitment::Reveal(x) => *x };
                    let suit = x.suit();
                    let mut probe = g.clone();
                    println!("first missing: commitment={c:?} suit={suit} x_rank={}", x.rank());
                    loop {
                        let need = probe.get_stack().get(suit);
                        if need >= x.rank() {
                            println!("  prefix loop reached rank {need} >= {}", x.rank());
                            break;
                        }
                        let c2 = Card::new(need, suit);
                        let pmv = probe.gen_moves::<false>();
                        let lnow = probe.get_hidden().get_locked_mask();
                        println!(
                            "  need={need} c2={c2:?} c2_in_pile_stack={} c2_locked={} c2_visible={}",
                            pmv.pile_stack & c2.mask() != 0,
                            lnow & c2.mask() != 0,
                            probe.get_visible_mask() & c2.mask() != 0,
                        );
                        if !(pmv.pile_stack & c2.mask() != 0 && lnow & c2.mask() == 0) {
                            break;
                        }
                        let _ = probe.do_move(Move::PileStack(c2));
                    }
                }
                assert_eq!(extra_separate, 0, "direct generator produced a class the Oracle could not reach");
            })
            .unwrap()
            .join()
            .unwrap();
    }

    /// Sweep canonicalization: determinism/idempotency hold trivially;
    /// *order-independence* provably fails when an ambiguous twin type
    /// (both twins visible, one covered) is stacked — the type-level masks
    /// know the count, not the identity, and the two readings differ by a
    /// per-suit foundation height (a real part of the state). Measured as
    /// a divergence counter at such types instead of asserted as full
    /// equality; the semantic-safety obligation is recorded in the docs
    /// (macro doc §6.5) as the ambiguous-twin lift.
    #[test]
    fn sweep_is_confluent() {
        let mut rng_state = 0x243F6A8885A308D3u64;
        let mut divergence_count = 0usize;
        let mut rand = move || {
            rng_state ^= rng_state << 13;
            rng_state ^= rng_state >> 7;
            rng_state ^= rng_state << 17;
            rng_state
        };
        for draw_step in [1u8, 3] {
            for i in 0..64u64 {
                let cards = default_shuffle(12 + i);
                let step = NonZeroU8::new(draw_step).unwrap();
                // sample a few mid-game states by random macro play
                let mut game = Solitaire::new(&cards, step);
                for _turn in 0..40 {
                    let mut reference = game.clone();
                    canonicalize(&mut reference);
                    let want = reference.encode();
                    for _trial in 0..4 {
                        let mut g2 = game.clone();
                        loop {
                            let cands = sweep_candidates(&g2);
                            if cands == 0 {
                                break;
                            }
                            let n = cands.count_ones() as usize;
                            let pick = (rand() as usize) % n;
                            let mut cm = cands;
                            let mut mask = 0u64;
                            for _ in 0..=pick {
                                mask = cm & cm.wrapping_neg();
                                cm &= !mask;
                            }
                            let m = Move::PileStack(Card::from_mask_index(
                                u8::try_from(mask.trailing_zeros()).unwrap(),
                            ));
                            let _ = g2.do_move(m);
                        }
                        let got = g2.encode();
                        if got != want {
                            divergence_count += 1;
                            // the divergence must be pure stack noise: hidden
                            // and deck are sweep-invariant, and any nontrivial
                            // divergence there is a bug, not an ambiguity
                            assert_eq!(
                                (got >> 16),
                                (want >> 16),
                                "divergence outside the stack component: draw={draw_step} seed={} turn={_turn} got={got:x} want={want:x}",
                                12 + i
                            );
                            println!(
                                "  LIFT draw={draw_step} seed={} turn={_turn}: stack got={:#x} want={:#x}",
                                12 + i,
                                got & 0xFFFF,
                                want & 0xFFFF,
                            );
                        }
                    }
                    if game.is_win() {
                        break;
                    }
                    let cands = enumerate_commitments(&game);
                    if cands.is_empty() {
                        break;
                    }
                    for &m in &cands[(rand() as usize) % cands.len()].witness_path {
                        let _ = game.do_move(m);
                    }
                }
            }
        }
        println!(
            "sweep determinism: 128 games x 40 turns x 4 random orders; ambiguous-twin lifts diverged in {divergence_count} orderings"
        );
    }

    /// The acceptance gate, in miniature: macro-game verdicts under each
    /// successor policy must equal the (full-dominance, full-pruner) old
    /// solver's verdict on every game. A `TallestOnly`/`ShortestOnly`
    /// mismatch means a scar choice the single-class policy would lose.
    #[test]
    fn macro_verdict_matches_engine() {
        std::thread::Builder::new()
            .stack_size(256 * 1024 * 1024)
            .spawn(|| {
                for draw_step in [1u8, 3] {
                    for i in 0..16u64 {
                        let cards = default_shuffle(12 + i);
                        let step = NonZeroU8::new(draw_step).unwrap();
                        let t0 = std::time::Instant::now();
                        let (res, _) = solve(&mut Solitaire::new(&cards, step));
                        let old_win = matches!(res, SearchResult::Solved);
                        let t_old = t0.elapsed();
                        let g = Solitaire::new(&cards, step);
                        let t1 = std::time::Instant::now();
                        let all = macro_solvable_sel(&g, SuccSelect::All);
                        let t_all = t1.elapsed();
                        let t2 = std::time::Instant::now();
                        let fast = macro_solvable_direct(&g);
                        let t_fast = t2.elapsed();
                        // report per-config details when slow
                        let slow = t_old.max(t_all).max(t_fast);
                        println!(
                            "seed={} draw={draw_step} verdict={}/{} old={:?} oracle={:?} direct={:?}",
                            12 + i, if old_win == all && all == fast { "OK" } else { "MISMATCH" },
                            if slow > std::time::Duration::from_millis(200) { "SLOW" } else { "" },
                            t_old, t_all, t_fast
                        );
                        assert_eq!(
                            (all, fast),
                            (old_win, old_win),
                            "verdict mismatch: draw={draw_step} seed={} old={old_win} oracle={all} direct={fast}",
                            12 + i
                        );
                    }
                }
                println!("macro verdicts match the engine (oracle + direct paths)");
            })
            .unwrap()
            .join()
            .unwrap();
    }

    /// The heavy version: draw-1 plus the full greedy corpus, run manually.
    /// Kept #[ignore] because the oracle walk makes it take minutes in
    /// release; it's the acceptance harness when the direct path changes.
    #[test]
    #[ignore = "expensive verdict sweep; run with --ignored --nocapture"]
    fn macro_verdict_sweep_big() {
        std::thread::Builder::new()
            .stack_size(256 * 1024 * 1024)
            .spawn(|| {
                let mut n = 0usize;
                let mut mismatches = 0usize;
                for draw_step in [1u8, 3] {
                    for i in 0..64u64 {
                        let cards = default_shuffle(12 + i);
                        let step = NonZeroU8::new(draw_step).unwrap();
                        let (res, _) = solve(&mut Solitaire::new(&cards, step));
                        let old_win = matches!(res, SearchResult::Solved);
                        let g = Solitaire::new(&cards, step);
                        let fast = macro_solvable_direct(&g);
                        n += 1;
                        let ok = old_win == fast;
                        if !ok { mismatches += 1; }
                        println!("seed={} draw={draw_step} old={old_win} direct={fast} {}", 12 + i, if ok { "OK" } else { "** MISMATCH **" });
                    }
                }
                assert_eq!(mismatches, 0, "macro direct path verdict sweep found mismatches");
                println!("big verdict sweep: {n} games, {mismatches} mismatches");
            })
            .unwrap()
            .join()
            .unwrap();
    }

    /// Perf attribution for the verdict test's SLOW rows: runs the oracle
    /// and direct recursions side by side with node/branch counters, the
    /// direct generator's channel histogram, and the cfg(test) probe
    /// counters (walk/cluster/BFS/post/sweep). The old engine is run in
    /// its full 2x2 (dominance x pruner) to attribute its speed: the
    /// macro game deliberately searches the *raw* game, so the gap to
    /// `solve` is exactly the filter layers the raw search runs without.
    #[test]
    #[ignore = "perf probe; run with --ignored --release --nocapture"]
    fn macro_verdict_perf_probe() {
        /// old-engine traversal counter: visits (incl. tp hits), unique
        /// nodes, and the filtered branching factor, with an honest budget
        const OLD_VISIT_BUDGET: u64 = 10_000_000;
        struct OldProbe<P: Pruner + Default> {
            won: bool,
            visits: u64,
            nodes: u64,
            branches: u64,
            budget: bool,
            marker: core::marker::PhantomData<P>,
        }
        impl<P: Pruner + Default> OldProbe<P> {
            fn new() -> Self {
                Self {
                    won: false,
                    visits: 0,
                    nodes: 0,
                    branches: 0,
                    budget: false,
                    marker: core::marker::PhantomData,
                }
            }
        }
        impl<P: Pruner + Default> Callback for OldProbe<P> {
            type Pruner = P;
            fn on_win(&mut self, _: &Solitaire) -> Control {
                self.won = true;
                Control::Halt
            }
            fn on_visit(&mut self, _: &Solitaire, _: Encode) -> Control {
                self.visits += 1;
                if self.visits > OLD_VISIT_BUDGET {
                    self.budget = true;
                    return Control::Halt;
                }
                Control::Ok
            }
            fn on_move_gen(&mut self, m: &crate::moves::MoveMask, _: Encode) -> Control {
                self.nodes += 1;
                self.branches += u64::from(m.len());
                Control::Ok
            }
        }
        fn run_old<const DOM: bool, P: Pruner + Default>(
            cards: &[Card; 52],
            step: NonZeroU8,
        ) -> OldProbe<P> {
            let mut game = Solitaire::new(cards, step);
            let mut tp = TpTable::default();
            let mut probe = OldProbe::<P>::new();
            traverse::<_, _, DOM>(&mut game, &P::default(), &mut tp, &mut probe);
            probe
        }
        std::thread::Builder::new()
            .stack_size(256 * 1024 * 1024)
            .spawn(|| {
                for (seed, draw_step) in
                    [(17u64, 1u8), (18, 1), (22, 1), (14, 3), (21, 3), (18, 3)]
                {
                    let cards = default_shuffle(seed);
                    let step = NonZeroU8::new(draw_step).unwrap();
                    let g = Solitaire::new(&cards, step);

                    // old engine, the full 2x2 (dominance x pruner)
                    let t = std::time::Instant::now();
                    let p = run_old::<true, FullPruner>(&cards, step);
                    println!(
                        "seed={seed} draw={draw_step} OLD dom+pruner    win={:>5} visits={:>9} nodes={:>9} branches={:>10} avg_branch={:5.2} budget={} total={:?}",
                        p.won, p.visits, p.nodes, p.branches,
                        p.branches as f64 / p.nodes.max(1) as f64,
                        p.budget, t.elapsed()
                    );
                    let t = std::time::Instant::now();
                    let p = run_old::<true, NoPruner>(&cards, step);
                    println!(
                        "seed={seed} draw={draw_step} OLD dom-only      win={:>5} visits={:>9} nodes={:>9} branches={:>10} avg_branch={:5.2} budget={} total={:?}",
                        p.won, p.visits, p.nodes, p.branches,
                        p.branches as f64 / p.nodes.max(1) as f64,
                        p.budget, t.elapsed()
                    );
                    let t = std::time::Instant::now();
                    let p = run_old::<false, FullPruner>(&cards, step);
                    println!(
                        "seed={seed} draw={draw_step} OLD pruner-only    win={:>5} visits={:>9} nodes={:>9} branches={:>10} avg_branch={:5.2} budget={} total={:?}",
                        p.won, p.visits, p.nodes, p.branches,
                        p.branches as f64 / p.nodes.max(1) as f64,
                        p.budget, t.elapsed()
                    );
                    let t = std::time::Instant::now();
                    let p = run_old::<false, NoPruner>(&cards, step);
                    println!(
                        "seed={seed} draw={draw_step} OLD raw           win={:>5} visits={:>9} nodes={:>9} branches={:>10} avg_branch={:5.2} budget={} total={:?}",
                        p.won, p.visits, p.nodes, p.branches,
                        p.branches as f64 / p.nodes.max(1) as f64,
                        p.budget, t.elapsed()
                    );

                    // what the old engine's winning line looks like:
                    // length and per-move-type counts (is the win a
                    // near-forced stacking cascade the raw DFS walks
                    // straight into?)
                    {
                        let mut game = Solitaire::new(&cards, step);
                        let (res, hist) = solve(&mut game);
                        if let Some(h) = &hist {
                            let mut counts = [0usize; 5];
                            for m in h.iter() {
                                match m {
                                    Move::DeckStack(_) => counts[0] += 1,
                                    Move::PileStack(_) => counts[1] += 1,
                                    Move::DeckPile(_) => counts[2] += 1,
                                    Move::StackPile(_) => counts[3] += 1,
                                    Move::Reveal(_) => counts[4] += 1,
                                }
                            }
                            println!(
                                "seed={seed} draw={draw_step} OLD-WINLINE {res:?} len={} DS/PS/DP/SP/R={counts:?}",
                                h.len()
                            );
                        }
                    }

                    // oracle under three successor orders: natural
                    // (reveal-first, the shipped order), draw-first (the
                    // legacy order), and reversed — how much of the node
                    // count is commitment-order refutation?
                    for (policy_name, policy) in
                        [("natural    ", 0u8), ("draw-first  ", 1), ("reversed    ", 2)]
                    {
                        const NODE_CAP: usize = 3_000_000;
                        fn rec(
                            g: &Solitaire,
                            policy: u8,
                            tp: &mut TpTable,
                            nodes: &mut usize,
                            branches: &mut usize,
                            capped: &mut bool,
                        ) -> bool {
                            let mut s = g.clone();
                            canonicalize(&mut s);
                            if s.is_win() || !tp.insert(s.encode()) {
                                return s.is_win();
                            }
                            *nodes += 1;
                            if *nodes > NODE_CAP {
                                *capped = true;
                                return false;
                            }
                            let mut succs = enumerate_transitions(&s);
                            if policy == 1 {
                                succs.sort_by_key(|(c, _)| match c {
                                    Commitment::Draw(_) => 0,
                                    Commitment::Reveal(_) => 1,
                                });
                            }
                            *branches += succs.len();
                            let hit = match policy {
                                2 => succs
                                    .iter()
                                    .rev()
                                    .any(|(_, succ)| rec(succ, policy, tp, nodes, branches, capped)),
                                _ => succs
                                    .iter()
                                    .any(|(_, succ)| rec(succ, policy, tp, nodes, branches, capped)),
                            };
                            hit
                        }
                        let t = std::time::Instant::now();
                        let mut tp = TpTable::default();
                        let (mut n, mut b) = (0usize, 0usize);
                        let mut capped = false;
                        let w = rec(&g, policy, &mut tp, &mut n, &mut b, &mut capped);
                        println!(
                            "seed={seed} draw={draw_step} ORACLE/{policy_name} win={w} nodes={n} branches={b} capped={} total={:?}",
                            capped,
                            t.elapsed()
                        );
                    }

                    // oracle: same shape as macro_solvable_sel(All), counted
                    perf_probe::reset();
                    let t0 = std::time::Instant::now();
                    let o_win = {
                        fn rec(
                            g: &Solitaire,
                            tp: &mut TpTable,
                            nodes: &mut usize,
                            branches: &mut usize,
                            t_trans: &mut std::time::Duration,
                        ) -> bool {
                            let mut s = g.clone();
                            canonicalize(&mut s);
                            if s.is_win() || !tp.insert(s.encode()) {
                                return s.is_win();
                            }
                            *nodes += 1;
                            let t = std::time::Instant::now();
                            let succs = enumerate_transitions(&s);
                            *t_trans += t.elapsed();
                            *branches += succs.len();
                            succs
                                .iter()
                                .any(|(_, succ)| rec(succ, tp, nodes, branches, t_trans))
                        }
                        let mut tp = TpTable::default();
                        let (mut n, mut b) = (0usize, 0usize);
                        let mut t = std::time::Duration::ZERO;
                        let w = rec(&g, &mut tp, &mut n, &mut b, &mut t);
                        println!(
                            "seed={seed} draw={draw_step} ORACLE win={w} nodes={n} branches={b} trans={t:?} total={:?} walk/cls_c/cls_s/bfs_c/bfs_s/post_c/post_s/canon/gen/do/undo/enc={:?}",
                            t0.elapsed(),
                            perf_probe::read()
                        );
                        w
                    };

                    // direct: same shape as macro_solvable_direct, counted;
                    // channels kept visible by folding macro_transitions_direct
                    // by hand (same per-(commitment, kind) first-wins rule as
                    // macro_transitions_fast)
                    perf_probe::reset();
                    let t1 = std::time::Instant::now();
                    let d_win = {
                        fn rec(
                            s: &Solitaire,
                            tp: &mut TpTable,
                            nodes: &mut usize,
                            branches: &mut usize,
                            emissions: &mut usize,
                            t_trans: &mut std::time::Duration,
                            channels: &mut std::collections::BTreeMap<&'static str, usize>,
                        ) -> bool {
                            if s.is_win() || !tp.insert(s.encode()) {
                                return s.is_win();
                            }
                            *nodes += 1;
                            let t = std::time::Instant::now();
                            let all = macro_transitions_direct(s);
                            *t_trans += t.elapsed();
                            *emissions += all.len();
                            let mut seen: Vec<(Commitment, OutcomeKind)> = Vec::new();
                            let mut succs: Vec<&Solitaire> = Vec::new();
                            for (c, k, st, ch) in &all {
                                *channels.entry(*ch).or_insert(0) += 1;
                                if !seen.contains(&(*c, *k)) {
                                    seen.push((*c, *k));
                                    succs.push(st);
                                }
                            }
                            *branches += succs.len();
                            succs.into_iter().any(|succ| {
                                rec(succ, tp, nodes, branches, emissions, t_trans, channels)
                            })
                        }
                        let mut tp = TpTable::default();
                        let mut root = g.clone();
                        canonicalize(&mut root);
                        let (mut n, mut b, mut e) = (0usize, 0usize, 0usize);
                        let mut t = std::time::Duration::ZERO;
                        let mut ch: std::collections::BTreeMap<&'static str, usize> =
                            Default::default();
                        let w = rec(&root, &mut tp, &mut n, &mut b, &mut e, &mut t, &mut ch);
                        println!(
                            "seed={seed} draw={draw_step} DIRECT win={w} nodes={n} branches={b} emissions={e} trans={t:?} total={:?} walk/cls_c/cls_s/bfs_c/bfs_s/post_c/post_s/canon/gen/do/undo/enc={:?} channels={ch:?}",
                            t1.elapsed(),
                            perf_probe::read()
                        );
                        w
                    };
                    assert_eq!(o_win, d_win, "probe recursions disagree at seed={seed}");
                }
            })
            .unwrap()
            .join()
            .unwrap();
    }

    /// Greedy macro play: enumerate commitments, apply one witness path,
    /// repeat. Asserts the state stays valid and the play makes progress
    /// (every commitment changes the encode). Prints the observed
    /// multiplicity of post-states per commitment kind — the input data
    /// for open item O6 (when does the accommodation collapse to ≤2).
    ///
    /// Note: the state-level canonical multiplicity is *not* capped — free
    /// floats form product lattices (observed up to 8). The claim under
    /// test is the quotient one (C2): after quotienting post-states by the
    /// reversible closure, at most 2 classes per commitment survive.
    #[test]
    fn macro_scaffold_smoke() {
        // the closure DFS is deep on some games; give it solver-grade stack
        std::thread::Builder::new()
            .stack_size(256 * 1024 * 1024)
            .spawn(macro_scaffold_smoke_inner)
            .unwrap()
            .join()
            .unwrap();
    }

    /// The (Y, Ȳ) parent configuration of a commitment at the canonical
    /// root — the finite table's row. Detection is by derivation only
    /// (deck contains / foundation prefix / hidden-structure slice /
    /// complement), which is exact because placement-blockage of a parent
    /// is already subsumed by `direct`.
    #[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
    struct ParentSig {
        direct: bool,     // the generator offers X a landing at the root
        dig: bool,        // twin(X) is a placed tableau card (covers a parent)
        borrowable: u8,   // parents that are foundation tops
        f_buried: u8,     // parents on the foundation but not the suit top
        dead: u8,         // parents in stock or buried in a structure
        locked_surf: u8,  // parents that are locked surfaces
        kings: bool,      // X is a king (no parent types exist)
        stackable: bool,  // X stackable at the root
    }

    fn is_hidden_buried(g: &Solitaire, c: Card) -> bool {
        let hidden = g.get_hidden();
        (0..crate::deck::N_PILES).any(|pos| {
            let pile = hidden.get(pos);
            !pile.is_empty() && pile[..pile.len() - 1].contains(&c)
        })
    }

    fn is_locked_surface(g: &Solitaire, c: Card) -> bool {
        let hidden = g.get_hidden();
        (0..crate::deck::N_PILES).any(|pos| hidden.get(pos).last() == Some(&c))
    }

    fn in_deck(g: &Solitaire, c: Card) -> bool {
        g.get_deck().iter().any(|card| card == c)
    }

    fn parent_sig(g: &Solitaire, x: Card) -> ParentSig {
        use crate::card::KING_RANK;
        let mv = g.gen_moves::<false>();
        let stackable =
            (mv.pile_stack | mv.deck_stack) & x.mask() != 0;
        if x.rank() == KING_RANK {
            return ParentSig {
                direct: mv.deck_pile & x.mask() != 0 || mv.reveal & x.mask() != 0,
                dig: false,
                borrowable: 0,
                f_buried: 0,
                dead: 0,
                locked_surf: 0,
                kings: true,
                stackable,
            };
        }
        let s = x.suit();
        let parents = [Card::new(x.rank() + 1, s ^ 2), Card::new(x.rank() + 1, s ^ 3)];
        let mut sig = ParentSig {
            direct: false,
            dig: false,
            borrowable: 0,
            f_buried: 0,
            dead: 0,
            locked_surf: 0,
            kings: false,
            stackable,
        };
        for p in parents {
            let f = g.get_stack().get(p.suit());
            if f > p.rank() {
                if f == p.rank() + 1 {
                    sig.borrowable += 1;
                } else {
                    sig.f_buried += 1;
                }
            } else if in_deck(g, p) {
                sig.dead += 1;
            } else if is_hidden_buried(g, p) {
                sig.dead += 1;
            } else if is_locked_surface(g, p) {
                sig.locked_surf += 1;
            }
            // the remaining option (visible & placed) is where direct lives;
            // per-card coverage is intentionally not distinguished here
        }
        // direct = the root generator offers a placement of X
        let place_masks = mv.deck_pile | mv.stack_pile | mv.reveal;
        sig.direct = place_masks & x.mask() != 0;
        // dig channel: twin(X) is placed on the tableau (the only possible
        // parent-coverer, by the locality lemma)
        let twin = Card::new(x.rank(), s ^ 1);
        let twin_on_stack = g.get_stack().get(twin.suit()) > twin.rank();
        let twin_hidden_or_deck = in_deck(g, twin) || is_hidden_buried(g, twin);
        sig.dig = !twin_on_stack && !twin_hidden_or_deck && !is_locked_surface(g, twin);
        sig
    }

    fn macro_scaffold_smoke_inner() {
        let mut histogram = [0usize; 6];
        let mut macro_classes = 0usize;
        let mut sig_table: std::collections::BTreeMap<ParentSig, [usize; 2]> =
            std::collections::BTreeMap::new();
        // structural measurements for the closure theory:
        // - class_histogram[k]: commitments whose post-states form k classes
        // - mixed_kind_classes: classes containing both outcome kinds
        //   (predicted when X is stackable: tableau and stack are
        //   closure-connected via a late PileStack(X))
        // - same_kind_multi: commitments whose *single-kind* samples still
        //   split into several classes (would falsify "one class per kind")
        let mut class_histogram = [0usize; 5];
        let mut mixed_kind_classes = 0usize;
        let mut same_kind_multi = 0usize;
        let mut same_kind_multi_detail: Vec<(Commitment, u64, u64, bool)> = Vec::new();
        for draw_step in [1u8, 3] {
            for i in 0..100u64 {
                let mut game =
                    Solitaire::new(&default_shuffle(12 + i), NonZeroU8::new(draw_step).unwrap());
                let mut max_multiplicity = 0usize;
                let mut max_canon_multiplicity = 0usize;
                let mut overflowed = false;
                let mut canon_overflowed = false;
                for _turn in 0..200 {
                    if game.is_win() {
                        break;
                    }
                    // witness paths are relative to the canonicalized root:
                    // sweep first (reversible moves only), then enumerate
                    canonicalize(&mut game);
                    let cands = enumerate_commitments(&game);
                    if cands.is_empty() {
                        break; // dead-ended macro state
                    }
                    let mut turn_max = 0usize;
                    for c in &cands {
                        max_multiplicity = max_multiplicity
                            .max(c.outcomes.tableau.len())
                            .max(c.outcomes.stack.len());
                        max_canon_multiplicity = max_canon_multiplicity
                            .max(c.outcomes.canon_tableau.len())
                            .max(c.outcomes.canon_stack.len());
                        overflowed |= c.outcomes.overflowed;
                        canon_overflowed |= c.outcomes.canon_overflowed;
                        turn_max = turn_max
                            .max(c.outcomes.canon_tableau.len().min(5))
                            .max(c.outcomes.canon_stack.len().min(5));

                        // the real C2 content: after quotienting post-states
                        // by the reversible closure, at most 2 classes remain;
                        // check ALL multi-sample clusters, not just >2
                        for encs in [&c.outcomes.canon_tableau, &c.outcomes.canon_stack] {
                            if encs.len() > 1 {
                                let k = closure_classes(encs);
                                macro_classes = macro_classes.max(k);
                                if k > 1 {
                                    same_kind_multi += 1;
                                    same_kind_multi_detail.push((
                                        c.commitment,
                                        encs[0].0 >> 32,
                                        encs[0].0 & 0xFFFF,
                                        encs.len() > c.outcomes.canon_tableau.len(),
                                    ));
                                }
                            }
                        }

                        // combined class structure: cluster both kinds
                        // together and see whether classes are kind-pure
                        {
                            let combined = c
                                .outcomes
                                .canon_tableau
                                .iter()
                                .map(|s| (false, s))
                                .chain(c.outcomes.canon_stack.iter().map(|s| (true, s)));
                            let mut reps: Vec<(bool, Encode, &Solitaire)> = Vec::new();
                            let mut any_mixed = false;
                            'samples: for (is_stack, (enc, st)) in combined {
                                for (rep_kind, rep_enc, rep_st) in &mut reps {
                                    if closure_contains(rep_st, *enc) {
                                        any_mixed |= *rep_kind != is_stack;
                                        let _ = rep_enc;
                                        continue 'samples;
                                    }
                                }
                                reps.push((is_stack, *enc, st));
                            }
                            if !reps.is_empty() {
                                class_histogram[reps.len().min(4)] += 1;
                                if any_mixed {
                                    mixed_kind_classes += 1;
                                }
                                // finite configuration table: which (Y,Ȳ)
                                // configs at the canonical root ever
                                // produce 2 classes?
                                let sig = parent_sig(&game, match c.commitment {
                                    Commitment::Draw(x) | Commitment::Reveal(x) => x,
                                });
                                let entry = sig_table.entry(sig).or_default();
                                entry[usize::from(reps.len() > 1)] += 1;
                                // anomaly dump: two kind-pure classes —
                                // check where the cross-kind flip died
                                if reps.len() == 2 && !any_mixed {
                                    let x = match c.commitment {
                                        Commitment::Draw(x) | Commitment::Reveal(x) => x,
                                    };
                                    for (is_stack, enc, st) in &reps {
                                        let mv = st.gen_moves::<false>();
                                        let up = mv.pile_stack & x.mask() != 0;
                                        let down = mv.stack_pile & x.mask() != 0;
                                        println!(
                                            "  TWOPURE draw={draw_step} seed={} {:?} kind_stack={is_stack} enc={enc:x} X_stackable_now={} X_worryback_now={}",
                                            12 + i,
                                            c.commitment,
                                            up,
                                            down
                                        );
                                    }
                                }
                                assert!(
                                    reps.len() <= 2,
                                    "commitment {:?} has {} combined closure classes \
                                     (C2 violation): draw={draw_step} seed={}",
                                    c.commitment,
                                    reps.len(),
                                    12 + i
                                );
                            }
                        }

                        // residue anatomy: when the canonical count exceeds
                        // the structural 4-cap conjecture, show which
                        // encode components float
                        for (kind, encs) in
                            [("tab", &c.outcomes.canon_tableau), ("stak", &c.outcomes.canon_stack)]
                        {
                            if encs.len() > 4 {
                                let stacks: Vec<u16> =
                                    encs.iter().map(|(e, _)| *e as u16).collect();
                                let hiddens: Vec<u16> =
                                    encs.iter().map(|(e, _)| (*e >> 16) as u16).collect();
                                let decks: Vec<u32> =
                                    encs.iter().map(|(e, _)| (*e >> 32) as u32).collect();
                                println!(
                                    "  MULTI draw={draw_step} seed={} {:?} {kind} stacks={stacks:x?} hidden={hiddens:x?} decks={decks:x?}",
                                    12 + i,
                                    c.commitment,
                                );
                            }
                        }
                    }
                    let before = game.encode();
                    for &m in &cands[0].witness_path {
                        let _ = game.do_move(m); // witness paths are legal by construction
                    }
                    assert_ne!(game.encode(), before);
                    assert!(game.is_valid());
                    histogram[turn_max] += 1;
                }
                let _ = (max_multiplicity, max_canon_multiplicity, overflowed, canon_overflowed);
            }
        }
        println!("state-level multiplicity histogram (per turn, capped at 5+): {histogram:?}");
        println!("max distinct post-state closure classes per kind: {macro_classes} (C2 claim: <= 2)");
        println!("combined class histogram (1/2/3/4+): {class_histogram:?}");
        println!("parent-configuration table (sig -> [single_class, multi_class]):");
        for (sig, counts) in &sig_table {
            println!("  {sig:?} -> {counts:?}");
        }
        println!("commitments with mixed-kind classes (predicted iff X stackable): {mixed_kind_classes}");
        println!("same-kind multi-class commitments (should be 0 for one-class-per-kind): {same_kind_multi}");
        for (c, deck, stack, is_stack) in &same_kind_multi_detail {
            println!("  SAMESPLIT {c:?} deck={deck:x} stack={stack:x} kind_stack={is_stack}");
        }
    }
}
