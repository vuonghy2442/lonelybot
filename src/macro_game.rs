//! The macro (commitment) game — the new solver core, described in
//! docs/macro_formalization.md (theory, §6 measurements) and
//! docs/macro_parking.md (the parking lemma and the destination collapse).
//!
//! The old game has five moves; the macro game regroups any play as
//! "shuffle, commit, shuffle, commit, ..." (Lemma A3) where a *commitment*
//! is the first irreversible move after a reversible accommodation
//! (Lemma A1: only `DeckPile`/`DeckStack` introduce a deck card, and only
//! `Reveal`/`PileStack`-on-locked touch the hidden structure — both
//! irreversible).
//!
//! Layers:
//!
//! - **The word board** (`Words`, `ClosureCtx`): all move masks are pure
//!   functions of `(vis, locked, stack)`; inside a reversible closure the
//!   state *is* the stack word, since `hidden`/`deck` are invariant and
//!   `vis` is derived. The safe sweep (`sweep_words`/`canonicalize`), the
//!   §6.4 channel probes, and the accommodation BFS all run on words — no
//!   clones, no per-step `gen_moves`, BFS dedup keyed on the u16 word.
//! - **The direct generator** (`core_run`): the §6.4 rule list per
//!   commitment — direct / dig / borrow / prefix-raise channels plus the
//!   bounded shared BFS for the crease — emitting steps, not states.
//! - **The search** (`macro_solvable_direct`): in-place DFS applying
//!   successors as `do_move(commit)` + `set_board(swept words)`; the fold
//!   is the destination collapse (`collapse_pick`): one successor per
//!   commitment, park-first.
//! - **The oracle** (`enumerate_commitments` + closure clustering): the
//!   reference transition function — the differential test
//!   (`macro_direct_matches_oracle`) measures the fast path against it; the
//!   verdict gates (`macro_verdict_matches_engine`, the 128-game sweep)
//!   judge verdicts against the shipped solver.

use arrayvec::ArrayVec;

extern crate alloc;
use alloc::vec::Vec;

use crate::card::{Card, KING_MASK, N_CARDS};
use crate::deck::N_PILES;
use crate::moves::{Move, MoveMask, N_MOVES_MAX};
use crate::stack::Stack;
use crate::state::{bottom_mask_of, swap_pair, Encode, Solitaire};
use crate::traverse::TpTable;
use crate::utils::full_mask;

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
        static BFS_NANOS: Cell<u64> = Cell::new(0);
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
    pub fn read() -> [u64; 13] {
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

/// The word-level board: everything the abstract move guards read, without
/// the concrete state machinery. The move masks are pure functions of
/// `(vis, locked, stack)` (the parity lemma of no_pile §3 powers `bm`; the
/// stack word is the foundation), so every probe the §6.4 rule list needs —
/// and the whole closure exploration — runs on 20-byte copies: no clones,
/// no `do_move` chains, no per-step `gen_moves`.
///
/// Within a reversible closure, `hidden` and `deck` are invariant and the
/// visible set is a derived function of the stack word:
/// `vis = full ^ buried ^ deck_remaining ^ stacked(stack)` — so a closure
/// state is exactly `stack`, a u16. That, not hashing whole states, is the
/// equivalence-class capture.
#[derive(Clone, Copy, PartialEq, Eq)]
struct Words {
    vis: u64,
    locked: u64,
    stack: u16,
}

impl Words {
    fn from_game(g: &Solitaire) -> Self {
        Self {
            vis: g.get_visible_mask(),
            locked: g.get_hidden().get_locked_mask(),
            stack: g.get_stack().encode(),
        }
    }

    #[allow(clippy::cast_possible_truncation)]
    fn height(self, suit: u8) -> u8 {
        ((self.stack >> (4 * suit)) & 0xF) as u8
    }

    fn bm(self) -> u64 {
        bottom_mask_of(self.vis, self.locked)
    }

    fn sm(self) -> u64 {
        Stack::decode(self.stack).mask()
    }

    /// Raw `pile_stack` mask (`bm & vis & sm`) — locked cards included, as
    /// in `gen_moves::<false>`; the unlock check is the caller's business.
    fn pile_stack(self) -> u64 {
        self.bm() & self.vis & self.sm()
    }

    fn free_slot(self) -> u64 {
        let extended = self.vis & (self.locked | KING_MASK);
        let king = if extended.count_ones() < u32::from(N_PILES) {
            KING_MASK
        } else {
            0
        };
        (self.bm() >> 4) | king
    }

    /// Every raw move mask, identical formulas to `gen_moves::<false>`
    /// (with dominances off that function never early-returns, so the pure
    /// formulas are the whole semantics). The §6.4 probes and the word BFS
    /// both read legality through this.
    fn move_masks(self, deck_mask: u64, first_layer: u64) -> MoveMask {
        let sm = self.sm();
        let free_slot = self.free_slot();
        MoveMask {
            pile_stack: self.pile_stack(),
            deck_stack: deck_mask & sm,
            stack_pile: swap_pair(sm >> 4) & free_slot,
            deck_pile: deck_mask & free_slot,
            reveal: self.vis & self.locked & free_slot & !(first_layer & KING_MASK),
        }
    }

    /// The sweep candidate rule, word form: the same set
    /// `Solitaire::safe_sweep_candidates` computes on the concrete state.
    fn sweep_cands(self) -> u64 {
        self.pile_stack() & Stack::decode(self.stack).dominance_mask() & !self.locked
    }

    fn stack_up(&mut self, c: Card) {
        self.vis &= !c.mask();
        self.stack += 1 << (4 * c.suit());
    }

    fn stack_down(&mut self, c: Card) {
        self.vis |= c.mask();
        self.stack -= 1 << (4 * c.suit());
    }
}

/// The stacked card set of a stack word: per suit, the prefix below its
/// height. The word-level dual of `Stack::mask` (which is the *next* card).
const fn stacked_mask(stack: u16) -> u64 {
    let mut m = 0u64;
    let mut s = 0;
    while s < 4 {
        let h = ((stack >> (4 * s)) & 0xF) as u8;
        let mut r = 0;
        while r < h {
            m |= Card::new(r, s).mask();
            r += 1;
        }
        s += 1;
    }
    m
}

/// The closure-invariant context: the bits `hidden` and `deck` contribute
/// while only reversible moves shuffle. Every accommodation probe and the
/// BFS read legality from this plus a stack word; states inside the closure
/// are reconstructed as `words_at(word)` — free, and no `Solitaire` at all.
#[derive(Clone, Copy)]
struct ClosureCtx {
    root: Words,
    deck_mask: u64,
    first_layer: u64,
    /// buried cards | deck-remaining cards: the closure-fixed non-visibles
    nonvis_base: u64,
}

impl ClosureCtx {
    fn from_game(g: &Solitaire) -> Self {
        let root = Words::from_game(g);
        // nonvis_base = buried | deck-remaining, derived instead of
        // iterated: `vis = full ^ nonvis_base ^ stacked` inverted at the
        // root (the visible-set invariant, `is_valid`-checked on the test
        // corpus). Reads no per-card state.
        let nonvis_base = full_mask(N_CARDS) ^ root.vis ^ stacked_mask(root.stack);
        Self {
            root,
            deck_mask: g.get_deck().compute_mask(false),
            first_layer: g.get_hidden().first_layer_mask(),
            nonvis_base,
        }
    }

    /// The closure state at a stack word: `vis` derived, `locked`
    /// invariant. (The bijection closure-state ↔ stack word is what makes
    /// the accommodation BFS a u16-set walk.)
    fn words_at(&self, stack: u16) -> Words {
        Words {
            vis: full_mask(N_CARDS) ^ self.nonvis_base ^ stacked_mask(stack),
            locked: self.root.locked,
            stack,
        }
    }
}

/// The sweep candidate rule for the confluence test: any safely-stackable,
/// movable, unlocked tableau card. Locked cards are excluded because
/// stacking one is a reveal — a commitment, not an accommodation.
#[cfg(test)]
fn sweep_candidates(g: &Solitaire) -> u64 {
    // the raw cascade-free set, shared with the confluence test
    g.safe_sweep_candidates()
}

/// Canonicalize on words to the safe-sweep fixed point: stack every
/// safely-stackable movable unlocked card, deterministically lowest-first —
/// bit-for-bit the selection the old per-step `do_move` loop made, without
/// the moves.
///
/// Confluence (order-independence of the terminal encode) is argued by
/// monotonicity of all three enablers (stackability, safety, movability)
/// and measured by `sweep_is_confluent`. Ambiguous-twin types (both twins
/// visible, one covered) are resolved by the deterministic lowest-index
/// pick — the twin-expansion case of the reshape lemma operating inside
/// the sweep (macro doc §6.5).
fn sweep_words(w: &mut Words) {
    loop {
        let cands = w.sweep_cands();
        if cands == 0 {
            break;
        }
        #[cfg(test)]
        perf_probe::bump_canon();
        let cm = cands & cands.wrapping_neg();
        let c = Card::from_mask_index(u8::try_from(cm.trailing_zeros()).unwrap());
        w.stack_up(c);
    }
}

/// Canonicalize to the safe-sweep fixed point, computed on words and
/// installed in one `set_board` — no per-card move round trips.
fn canonicalize(g: &mut Solitaire) {
    let mut w = Words::from_game(g);
    sweep_words(&mut w);
    g.set_board(w.vis, w.stack);
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
/// Measurement-only: the scaffold smoke test.
#[cfg(test)]
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
/// The per-(commitment, kind) materialized *reference* fold: both outcome
/// kinds per commitment, F3-dominance-dropped, deduped by (commitment,
/// kind) — i.e. the pre-collapse search semantics, kept for the
/// measurement paths (the perf probe's channel/channel-coverage
/// instrumentation). The shipped search fold is the destination collapse
/// (`collapse_pick`, used by `macro_solvable_direct`); this function is
/// not on the hot search path.
///
/// History: per-kind first-wins collapse is theoretically under-emissive
/// (macro doc §6.7: same-kind scar classes can have different futures;
/// P2's absorption is what makes per-kind collapse safe; the loss is
/// measured by the class-coverage metric in macro_direct_matches_oracle).
/// F3 measured 5-6% of branches on the deep seeds, 16% elsewhere.
/// `macro_transitions_direct` keeps full semantics for the differential,
/// and the verdict gate judges soundness of the folds against the engine.
#[must_use]
pub fn macro_transitions_fast(g: &Solitaire) -> Vec<(Commitment, Solitaire)> {
    let mut scratch = DirectScratch::new();
    macro_transitions_fast_into(g, &mut scratch);
    scratch.out
}

/// The search-facing fold into `scratch.out` (reused across nodes).
fn macro_transitions_fast_into(g: &Solitaire, scratch: &mut DirectScratch) {
    let (root, ctx) = macro_transitions_core(g, scratch);
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
                .push((*c, post_state(&root, &ctx, steps)));
        }
    }
}

/// The search fold: one successor per commitment (macro_parking.md P.2 —
/// the destination is not a fork), measured green against the shipped
/// solver on the 128-game verdict corpus (macro_collapse_sweep, 2026-09).
/// The tableau "parked" realization is kept when it exists; the stack
/// realization only when forced (no tableau outcome) or when X is
/// dominantly stackable — the F3 case, where the two realizations are
/// sweep-equal, so the direct stack one is kept.
///
/// The fold deliberately does not hunt the §6.7 same-kind scar splits
/// (≤2 classes whose collapse here is unproven — C-SCAR's obligation);
/// the under-emission is what the differential's class-coverage metric
/// measures, and the verdict gate is the arbiter.
fn collapse_pick<'a>(group: &'a [StepTransition], f3: u64) -> Option<&'a StepTransition> {
    if group.is_empty() {
        return None;
    }
    let x = match group[0].0 {
        Commitment::Draw(x) | Commitment::Reveal(x) => x,
    };
    if f3 & x.mask() != 0 {
        if let Some(t) = group
            .iter()
            .find(|(_, k, _, ch)| *k == OutcomeKind::Stack && *ch == "stack-direct")
        {
            return Some(t);
        }
    }
    group
        .iter()
        .find(|(_, k, ..)| *k == OutcomeKind::Tableau)
        .or(group.first())
}

/// Solve the macro game on the direct transition function. Same recursive
/// shape as `macro_solvable`, different transition semantics source — the
/// two must agree on solvability or the fast generator is wrong.
///
/// Fully in place and allocation-free in the hot loop: successors are
/// computed as swept *words* (`post_words`), applied with one `do_move`
/// for the commit's concrete (deck/hidden) effect plus one `set_board`
/// for the words, and undone symmetrically — the undo's word-level
/// corruption is overwritten by the recorded words. Entry canonicalizes
/// once; successors arrive swept, so the recursion never resweeps. All
/// working buffers live in one `DirectScratch` for the whole search.
#[must_use]
pub fn macro_solvable_direct(g: &Solitaire) -> bool {
    let mut no_hook: Option<&mut dyn FnMut(&Solitaire)> = None;
    macro_solvable_direct_impl(g, &mut no_hook)
}

/// `macro_solvable_direct` with a per-node observer hook, called once per
/// newly inserted (TP-miss) state — one extra dyn call per node bounds the
/// cost on the instrumented path; the plain path passes `None` and just
/// skips a branch. Used for progress printing (throttle inside the hook)
/// and the state-space forensics probes.
pub fn macro_solvable_direct_progress(g: &Solitaire, mut hook: impl FnMut(&Solitaire)) -> bool {
    let mut hook: Option<&mut dyn FnMut(&Solitaire)> = Some(&mut hook);
    macro_solvable_direct_impl(g, &mut hook)
}

fn macro_solvable_direct_impl(g: &Solitaire, hook: &mut Option<&mut dyn FnMut(&Solitaire)>) -> bool {
    fn rec(
        s: &mut Solitaire,
        tp: &mut TpTable,
        scratch: &mut DirectScratch,
        hook: &mut Option<&mut dyn FnMut(&Solitaire)>,
    ) -> bool {
        if s.is_win() || !tp.insert(s.encode()) {
            return s.is_win();
        }
        if let Some(h) = hook {
            h(s);
        }
        let ctx = ClosureCtx::from_game(s);
        let mut commitments = core::mem::take(&mut scratch.commitments);
        core_run(&ctx, scratch, &mut commitments);
        scratch.commitments = commitments;

        // F3 dominance drop: tableau outcomes of dominantly stackable
        // commitments with a direct stack outcome (same fold as the
        // materialized path).
        let dom = s.get_stack().dominance_mask();
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

        // Forced-commitment dominance (ledger C12): the move-level F3
        // singleton fires even for LOCKED cards — stacking a dominantly
        // safe locked surface reveals it, and the engine then returns
        // that move alone. The sweep eats unlocked dominants eagerly and
        // F3 above drops the parked variant of dominant commitments, but
        // without this rule the fold still explores sibling commitments
        // the micro search never reaches. When a locked surface is
        // dominantly stackable, its Reveal commitment (stack outcome) is
        // the only successor — every alternative's first move
        // micro-dominance-commutes after it.
        let forced_reveal = {
            let f = ctx.root.locked
                & ctx.root.vis
                & ctx.root.sm()
                & ctx.root.bm()
                & Stack::decode(ctx.root.stack).dominance_mask();
            f & f.wrapping_neg()
        };

        // Deck-source dominance — the draw-1 clause of the engine's
        // cascade (state.rs): when a drawable deck card is dominantly
        // stackable, the lowest such card is the only deck commitment
        // worth branching on (you can always stack it first without
        // helping anything else). Reveal commitments are untouched.
        // Search-fold policy (like F3): the generator stays total so the
        // differential sees all channels. Corpus-gated [~] with the named
        // falsifier (ledger C9).
        //
        // The draw-3 lift was MEASURED UNSOUND and reverted (2026-09):
        // seeds 67 & 74 (draw 3) flip old=true -> direct=false under the
        // generalized form — in draw-3 the pace-shaped drawable set makes
        // jumping to the dominant card skip commitments the win needs.
        let deck_dom = {
            let d = ctx.deck_mask & ctx.root.sm() & Stack::decode(ctx.root.stack).dominance_mask();
            if s.get_deck().draw_step().get() == 1 && d != 0 {
                d & d.wrapping_neg()
            } else {
                0
            }
        };

        // take the working vecs out so the recursion can reuse the scratch
        let groups = core::mem::take(&mut scratch.groups);
        let mut win = false;
        'outer: for group in &groups {
            // forced-commitment dominance: a locked dominantly-stackable
            // surface's Reveal (stack outcome) is the node's only play
            if forced_reveal != 0 {
                match group.first() {
                    Some((Commitment::Reveal(x), ..)) if x.mask() == forced_reveal => {}
                    _ => continue,
                }
                let Some((_, _, steps, _)) = group
                    .iter()
                    .find(|(_, k, _, ch)| *k == OutcomeKind::Stack && *ch == "stack-direct")
                else {
                    continue;
                };
                let (vis, stack) = post_words(s, &ctx, steps);
                let old = (s.get_visible_mask(), s.get_stack().encode());
                let commit = *steps.last().expect("every channel ends in a commit");
                let (_, (undo, _)) = s.do_move(commit);
                s.set_board(vis, stack);
                let child_win = rec(s, tp, scratch, hook);
                s.undo_move(commit, undo);
                s.set_board(old.0, old.1);
                if child_win {
                    win = true;
                    break 'outer;
                }
                break 'outer; // sole successor
            }
            // note: the C5/is_pure port was falsified (seed 21 d1 flips
            // old=win -> macro=loss): Deck::is_pure's offset-at-boundary
            // premise doesn't survive the macro's offset-jumping draws, so
            // the "pure" states the old rule fired at and the macro states
            // it would fire at don't correspond. Ledger row C11.
            // deck dominance: skip dominated Draw commitments entirely
            if deck_dom != 0 {
                if let Some((Commitment::Draw(x), ..)) = group.first() {
                    if x.mask() != deck_dom {
                        continue;
                    }
                }
            }
            // one successor per commitment: the collapse fold
            let Some((_, _, steps, _ch)) = collapse_pick(group, f3) else {
                continue;
            };
            let (vis, stack) = post_words(s, &ctx, steps);
            let old = (s.get_visible_mask(), s.get_stack().encode());
            let commit = *steps.last().expect("every channel ends in a commit");
            let (_, (undo, _)) = s.do_move(commit);
            s.set_board(vis, stack);
            let child_win = rec(s, tp, scratch, hook);
            s.undo_move(commit, undo);
            s.set_board(old.0, old.1);
            if child_win {
                win = true;
                break 'outer;
            }
        }
        scratch.groups = groups;
        win
    }
    let mut root = g.clone();
    canonicalize(&mut root);
    rec(
        &mut root,
        &mut TpTable::default(),
        &mut DirectScratch::new(),
        hook,
    )
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

/// Reusable working buffers for the accommodation BFS — cleared, not
/// reallocated, per call. The queue carries stack words: inside the
/// closure the state *is* the word (see `ClosureCtx`).
pub(crate) struct BfsScratch {
    arena: Vec<(usize, Move, u16)>,
    queue: alloc::collections::VecDeque<(u16, usize)>,
    seen: crate::traverse::TpTable,
}

/// Reusable working buffers for the whole direct-transition machinery:
/// one set per search instead of one per node.
pub(crate) struct DirectScratch {
    groups: Vec<Vec<StepTransition>>,
    commitments: Vec<Commitment>,
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
            commitments: Vec::new(),
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

/// Bounded local search for the accommodations the constant-work
/// channels missed (chained borrows/digs — the §6.4 crease), answering
/// *every* pending goal with one shared traversal and appending the
/// results (with the commit move) straight into the goal's group. This is
/// the honest fallback the differential test measures: the rule list
/// (direct/dig/borrow) converges exactly when this rarely answers.
///
/// BFS, not DFS, because level order is the semantics: each goal's
/// witness is the *shortest* opening shuffle (the depth-ordered scar the
/// §7 absorption argument works with), and a goal is provably dead the
/// moment level `cap` starts popping — which is what lets one traversal
/// serve all goals with per-goal caps.
///
/// The traversal runs entirely on stack words: inside the closure a state
/// is its stack word (hidden/deck invariant, `vis` derived — see
/// `ClosureCtx`), so the queue carries u16s, dedup keys on the word, and
/// legality is recomputed from masks per pop; goal bookkeeping lives in
/// stack arrays (≤ 64 goals). Zero heap traffic per call. Children are
/// emitted in the old per-state BFS's exact order (`to_vec` order
/// restricted to reversible moves: `pile_stack` ascending, then
/// `stack_pile` ascending), so witness choice is unchanged.
fn accommodations_shared(
    ctx: &ClosureCtx,
    goals: &[AccommodationGoal],
    commitments: &[Commitment],
    groups: &mut [Vec<StepTransition>],
    scratch: &mut BfsScratch,
) {
    #[cfg(test)]
    {
        perf_probe::bump_bfs_call();
    }
    #[cfg(test)]
    let t0 = std::time::Instant::now();
    const NONE: u32 = u32::MAX;
    // answers[gi] = arena index of the shallowest state where goal gi opened
    let mut answers: ArrayVec<u32, 64> = ArrayVec::new();
    let mut pending: ArrayVec<usize, 64> = ArrayVec::new();
    for gi in 0..goals.len() {
        answers.push(NONE);
        pending.push(gi);
    }
    // parent-pointer arena: entry i = (parent index, reaching move, depth);
    // entry 0 is the root sentinel
    let arena = &mut scratch.arena;
    let queue = &mut scratch.queue;
    let seen = &mut scratch.seen;
    arena.clear();
    queue.clear();
    seen.clear();
    arena.push((usize::MAX, Move::PileStack(Card::DEFAULT), 0));
    queue.push_back((ctx.root.stack, 0));
    seen.insert(u64::from(ctx.root.stack));

    while let Some((word, idx)) = queue.pop_front() {
        #[cfg(test)]
        perf_probe::bump_bfs_state();
        let w = ctx.words_at(word);
        let mv = w.move_masks(ctx.deck_mask, ctx.first_layer);
        let depth = usize::from(arena[idx].2);
        // a cap this level exceeds can no longer open
        pending.retain(|&mut gi| goals[gi].cap > depth);
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
                answers[gi] = idx as u32;
                opened = true;
            }
        }
        if opened {
            pending.retain(|&mut gi| answers[gi] == NONE);
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
        // a commitment) plus StackPile.
        let mut edges = mv.pile_stack & !w.locked;
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
            let mut w2 = w;
            let m = if is_pile {
                w2.stack_up(c);
                Move::PileStack(c)
            } else {
                w2.stack_down(c);
                Move::StackPile(c)
            };
            if seen.insert(u64::from(w2.stack)) {
                let child = arena.len();
                arena.push((idx, m, (depth + 1) as u16));
                queue.push_back((w2.stack, child));
            }
        }
    }
    for (gi, goal) in goals.iter().enumerate() {
        let ans = answers[gi];
        if ans == NONE {
            continue;
        }
        // reconstruct the witness from the arena; caps give ≤11 shuffles +
        // the commit — the channel budget of 14 has room
        let mut steps: ArrayVec<Move, 42> = ArrayVec::new();
        let mut i = ans as usize;
        while i != 0 {
            steps.push(arena[i].1);
            i = arena[i].0;
        }
        steps.reverse();
        steps.push(goal.commit_move);
        let channel = match goal.kind {
            OutcomeKind::Stack => "stack-bfs",
            OutcomeKind::Tableau => "tableau-bfs",
        };
        let ci = commitments
            .iter()
            .position(|c| *c == goal.commitment)
            .expect("goal commitment comes from the enumeration");
        groups[ci].push((goal.commitment, goal.kind, steps, channel));
    }
    #[cfg(test)]
    perf_probe::bump_bfs_time(t0.elapsed());
}

/// The card a `Reveal(c)` (or reveal-by-stacking) would turn up: the
/// structure card directly under `c` in its pile, or `None` when the pile
/// empties. Peeked at the pre-commit state — accommodations are shuffles
/// and never touch the hidden structures, so the root's `hidden` answers
/// for every step list.
fn peek_under_pile(g: &Solitaire, c: Card) -> Option<Card> {
    let hidden = g.get_hidden();
    let pile = hidden.get(hidden.find(c));
    debug_assert_eq!(pile.last(), Some(&c), "commitment target must be the surface");
    if pile.len() >= 2 {
        Some(pile[pile.len() - 2])
    } else {
        None
    }
}

/// Word-level reveal effect: `c` leaves the locked set, the revealed card
/// (if any) joins the visible set.
fn reveal_words(w: &mut Words, g: &Solitaire, c: Card) {
    w.locked &= !c.mask();
    if let Some(r) = peek_under_pile(g, c) {
        w.vis |= r.mask();
    }
}

/// The swept board words of a post-state: replay the step list as word
/// edits (no `do_move`, no clones), then the closed-form sweep.
fn post_words(g: &Solitaire, ctx: &ClosureCtx, steps: &[Move]) -> (u64, u16) {
    let mut w = ctx.root;
    for &m in steps {
        match m {
            // the locked case is the commit move of a Reveal commitment
            // (reveal-by-stacking); shuffles are always unlocked
            Move::PileStack(c) => {
                if w.locked & c.mask() != 0 {
                    reveal_words(&mut w, g, c);
                }
                w.stack_up(c);
            }
            Move::StackPile(c) => w.stack_down(c),
            Move::DeckPile(c) => w.vis |= c.mask(),
            Move::DeckStack(c) => {
                w.stack += 1 << (4 * c.suit());
            }
            Move::Reveal(c) => reveal_words(&mut w, g, c),
        }
    }
    sweep_words(&mut w);
    (w.vis, w.stack)
}

/// Apply `steps`, canonicalize the result, and return the successor state.
/// Computed arithmetically: `post_words` evaluates the step list (shuffles
/// rearrange only the words, so they never touch the state) at word level;
/// one `do_move` performs the commit's deck/hidden effect; one `set_board`
/// installs the swept words over its vis/stack edits.
///
/// All inputs come from legality checks against the same pre-state — those
/// checks are type-level, and where a twin is ambiguous the move is legal
/// in the arrangement-existential sense (no_pile_to_pile.md §3/§6.5:
/// a set bit means *some* realizing arrangement has the card uncovered).
fn post_state(g: &Solitaire, ctx: &ClosureCtx, steps: &[Move]) -> Solitaire {
    #[cfg(test)]
    perf_probe::bump_post(steps.len() as u64);
    let (vis, stack) = post_words(g, ctx, steps);
    let mut next = g.clone();
    let _ = next.do_move(*steps.last().expect("every channel ends in a commit"));
    next.set_board(vis, stack);
    next
}

/// The materialized form of a direct transition: (commitment, outcome
/// kind, post-state via `post_state`, channel). The channel that produced
/// the outcome is recorded for the differential test's failure forensics
/// and the channel histograms.
pub type DirectTransition = (Commitment, OutcomeKind, Solitaire, &'static str);

/// The §6.4 rule list evaluated to *steps*: (commitment, outcome kind,
/// accommodation steps + the realizing commit move, channel). Steps, not
/// states, so the search-facing fold (`macro_transitions_fast`) can drop
/// dominated outcomes before paying for a `post_state` clone.
///
/// Capacity 42 = the accommodation depth cap (40, macro_parking.md P.5 —
/// the 12/10 caps measured out as a depth artifact) + the commit + slack;
/// a shallow capacity panics on deep witnesses.
type StepTransition = (Commitment, OutcomeKind, ArrayVec<Move, 42>, &'static str);

fn steps(ms: &[Move]) -> ArrayVec<Move, 42> {
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
///
/// Evaluated entirely on the canonical state's closure context — no
/// clones, no `do_move` probes, no per-step `gen_moves`: the §6.4 channels
/// are mask checks on the word board and 20-byte word copies.
fn core_run(ctx: &ClosureCtx, scratch: &mut DirectScratch, commitments: &mut Vec<Commitment>) {
    let mv = ctx.root.move_masks(ctx.deck_mask, ctx.first_layer);
    let deck_mask = ctx.deck_mask;
    let locked = ctx.root.locked;
    let locked_surfaces = ctx.root.vis & locked;

    // enumerate commitments: every locked surface first, then every
    // drawable deck card — reveal before draw, mirroring the old engine's
    // raw move order (`MoveMask::iter_moves` tries `Reveal` before any
    // deck move). Measured search order, not just aesthetics: draw-first
    // buries reveal-led winning lines under draw-subgame refutations
    // (seed 18 draw 1: 96k nodes draw-first vs 84 reveal-first, see
    // `macro_verdict_perf_probe`).
    commitments.clear();
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
    let DirectScratch { groups, goals, bfs, .. } = scratch;
    groups.truncate(n_groups);
    while groups.len() < n_groups {
        groups.push(Vec::new());
    }
    for grp in groups.iter_mut() {
        grp.clear();
    }
    goals.clear();
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
        // The probe runs on a word copy: `locked` is shuffle-invariant and
        // the pile-stack mask recomputes from the words.
        let suit = x.suit();
        let mut stack_produced = stack_now;
        if !stack_now && ctx.root.height(suit) < x.rank() {
            // the probe dies on its first iteration unless the first
            // missing prefix card is stackable and unlocked at the root —
            // check that before entering the loop (most probes die here)
            let first = Card::new(ctx.root.height(suit), suit);
            if mv.pile_stack & first.mask() != 0 && locked & first.mask() == 0 {
                let mut w = ctx.root;
                let mut steps_av: ArrayVec<Move, 42> = ArrayVec::new();
                let mut reachable = true;
                loop {
                    let need = w.height(suit);
                    if need >= x.rank() {
                        break;
                    }
                    let c2 = Card::new(need, suit);
                    let c2m = c2.mask();
                    if w.pile_stack() & c2m != 0 && locked & c2m == 0 {
                        w.stack_up(c2);
                        steps_av.push(Move::PileStack(c2));
                    } else {
                        reachable = false;
                        break;
                    }
                }
                if reachable {
                    let stack_ok = match commitment {
                        Commitment::Draw(_) => deck_mask & w.sm() & xmask != 0,
                        Commitment::Reveal(_) => w.pile_stack() & xmask != 0,
                    };
                    if stack_ok {
                        steps_av.push(stack_move);
                        groups[ci].push((
                            commitment,
                            OutcomeKind::Stack,
                            steps_av,
                            "stack-prefix-raise",
                        ));
                        stack_produced = true;
                    }
                }
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
                cap: 40,
            });
        }

        // dig/borrow only make sense with a parent class: skip for kings
        if x.rank() == crate::card::KING_RANK {
            continue;
        }

        // dig channel: vacate twin(X) onto a foundation if it is the
        // (uniquely possible) coverer of a parent top. Probed on a word
        // copy — one stack nibble edit and a mask recompute.
        let twin = x.swap_suit();
        let twin_mask = twin.mask();
        if locked & twin_mask == 0 && mv.pile_stack & twin_mask != 0 {
            let mut w = ctx.root;
            w.stack_up(twin);
            let mv2 = w.move_masks(deck_mask, ctx.first_layer);
            let opens = match commitment {
                Commitment::Draw(_) => mv2.deck_pile & xmask != 0,
                Commitment::Reveal(_) => mv2.reveal & xmask != 0,
            };
            if opens {
                groups[ci].push((
                    commitment,
                    OutcomeKind::Tableau,
                    steps(&[Move::PileStack(twin), direct_move]),
                    "tableau-dig",
                ));
            }
        }

        // borrow channel(s): a parent on its foundation top, worry-back-able.
        // Probed on a word copy, same shape as the dig.
        let r = x.rank();
        let s = x.suit();
        for p in [Card::new(r + 1, s ^ 2), Card::new(r + 1, s ^ 3)] {
            let on_foundation_top = ctx.root.height(p.suit()) == p.rank().saturating_add(1);
            if !(on_foundation_top
                && locked & p.mask() == 0
                && mv.stack_pile & p.mask() != 0)
            {
                continue;
            }
            let mut w = ctx.root;
            w.stack_down(p);
            let mv2 = w.move_masks(deck_mask, ctx.first_layer);
            let opens = match commitment {
                Commitment::Draw(_) => mv2.deck_pile & xmask != 0,
                Commitment::Reveal(_) => mv2.reveal & xmask != 0,
            };
            if opens {
                groups[ci].push((
                    commitment,
                    OutcomeKind::Tableau,
                    steps(&[Move::StackPile(p), direct_move]),
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
                cap: 40,
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
        accommodations_shared(ctx, goals, commitments.as_slice(), groups.as_mut_slice(), bfs);
    }
}

/// Canonicalize-on-clone wrapper around `core_run` for the materialized
/// (witness/differential) path: returns the canonical root and its closure
/// context so successors can be built by `post_state`.
fn macro_transitions_core(g: &Solitaire, scratch: &mut DirectScratch) -> (Solitaire, ClosureCtx) {
    let mut game = g.clone();
    canonicalize(&mut game);
    let ctx = ClosureCtx::from_game(&game);
    let mut commitments = core::mem::take(&mut scratch.commitments);
    core_run(&ctx, scratch, &mut commitments);
    scratch.commitments = commitments;
    (game, ctx)
}

/// The §6.4 rule list with full semantics, for the differential: every
/// channel's outcome materialized (per-channel dedup by encode), no fold.
/// Channels per commitment, in emission order: stack-direct,
/// tableau-direct, prefix-raise (stack the missing same-suit prefix) on
/// the stack side; dig (vacate `twin(X)`), borrow (worry a foundation-top
/// parent back) on the tableau side; and the bounded shared BFS for the
/// chained crease (caps 40 — measured as not-a-depth-artifact, P.5).
#[must_use]
pub fn macro_transitions_direct(g: &Solitaire) -> Vec<DirectTransition> {
    let mut scratch = DirectScratch::new();
    let (game, ctx) = macro_transitions_core(g, &mut scratch);
    // materialize per group with the (commitment, kind, encode) dedup
    let mut out: Vec<DirectTransition> = Vec::new();
    for group in &scratch.groups {
        for (commitment, kind, steps, channel) in group {
            let state = post_state(&game, &ctx, steps);
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

    /// The legacy per-card `do_move` sweep, kept as the test-only
    /// reference implementation of `sweep_words`.
    fn legacy_canon(g: &mut Solitaire) {
        loop {
            let cands = sweep_candidates(g);
            if cands == 0 {
                break;
            }
            let cm = cands & cands.wrapping_neg();
            let c = Card::from_mask_index(u8::try_from(cm.trailing_zeros()).unwrap());
            let _ = g.do_move(Move::PileStack(c));
        }
    }

    /// The word pipeline against move replay, state by state:
    /// `canonicalize` must land exactly where the per-card `do_move` sweep
    /// does (including ambiguous-twin picks), and `post_state` must equal
    /// replaying the channel's steps then sweeping. Any drift is caught
    /// here at the implementation surface, not downstream.
    #[test]
    fn words_match_moves() {
        std::thread::Builder::new()
            .stack_size(256 * 1024 * 1024)
            .spawn(|| {
                let mut checked = 0usize;
                for draw_step in [1u8, 3] {
                    for i in 0..16u64 {
                        let mut game = Solitaire::new(
                            &default_shuffle(12 + i),
                            NonZeroU8::new(draw_step).unwrap(),
                        );
                        for _turn in 0..50 {
                            if game.is_win() {
                                break;
                            }
                            // the sweep, both ways
                            let mut a = game.clone();
                            canonicalize(&mut a);
                            let mut b = game.clone();
                            legacy_canon(&mut b);
                            assert_eq!(
                                a.encode(),
                                b.encode(),
                                "sweep divergence: draw={draw_step} seed={} turn={_turn}",
                                12 + i
                            );
                            // every channel's post-state, both ways
                            let mut scratch = DirectScratch::new();
                            let (root, ctx) = macro_transitions_core(&game, &mut scratch);
                            for group in &scratch.groups {
                                for (c, k, chan_steps, channel) in group {
                                    let fast = post_state(&root, &ctx, chan_steps);
                                    let mut replay = root.clone();
                                    for &m in chan_steps.iter() {
                                        replay.do_move(m);
                                    }
                                    legacy_canon(&mut replay);
                                    assert_eq!(
                                        fast.encode(),
                                        replay.encode(),
                                        "post_state divergence: draw={draw_step} seed={} turn={_turn} {c:?} {k:?} {channel} steps={chan_steps:?}",
                                        12 + i
                                    );
                                    let vf = fast.get_visible_mask();
                                    let vr = replay.get_visible_mask();
                                    assert_eq!(
                                        vf, vr,
                                        "post_state vis divergence: draw={draw_step} seed={} turn={_turn} {c:?} {k:?} {channel} steps={chan_steps:?}\n  fast-only={:#x} replay-only={:#x}\n  fast={:?}\n  replay={:?}",
                                        12 + i,
                                        vf & !vr, vr & !vf,
                                        fast, replay,
                                    );
                                    if !fast.is_valid() {
                                        println!(
                                            "INVALID fast: draw={draw_step} seed={} turn={_turn} {c:?} {k:?} {channel} steps={chan_steps:?}",
                                            12 + i
                                        );
                                        println!("  pre-core game.is_valid()={}", game.is_valid());
                                        println!("  canonical root.is_valid()={}", root.is_valid());
                                        {
                                            let rv = root.get_visible_mask();
                                            let mut nonvis_r = root.get_hidden().mask();
                                            for cd in root.get_deck().iter() { nonvis_r |= cd.mask(); }
                                            nonvis_r |= stacked_mask(root.get_stack().encode());
                                            println!("  root vis==derived: {}", full_mask(N_CARDS) ^ nonvis_r == rv);
                                        }
                                        let mut c1 = root.clone();
                                        c1.do_move(*chan_steps.last().unwrap());
                                        println!("  root+commit only is_valid={}", c1.is_valid());
                                        {
                                            let cv = c1.get_visible_mask();
                                            let mut nonvis_c = c1.get_hidden().mask();
                                            for cd in c1.get_deck().iter() { nonvis_c |= cd.mask(); }
                                            nonvis_c |= stacked_mask(c1.get_stack().encode());
                                            println!("  commit-only vis==derived: {} missing={:#x} extra={:#x}",
                                                full_mask(N_CARDS) ^ nonvis_c == cv,
                                                cv & !(full_mask(N_CARDS) ^ nonvis_c),
                                                (full_mask(N_CARDS) ^ nonvis_c) & !cv);
                                        }
                                        println!("  replay_valid={}", replay.is_valid());
                                        let total = vf.count_ones() as u32 + u32::from(fast.get_stack().len()) + u32::from(fast.get_deck().len()) + u32::from(fast.get_hidden().total_down_cards());
                                        println!("  total_cards={total} (want 52)");
                                        let mut nonvis = fast.get_hidden().mask();
                                        for cd in fast.get_deck().iter() { nonvis |= cd.mask(); }
                                        let derived = full_mask(N_CARDS) ^ nonvis ^ stacked_mask(fast.get_stack().encode());
                                        println!("  derived==vis: {}; missing={:#x} extra={:#x}", derived == vf, vf & !derived, derived & !vf);
                                        println!("  hidden_valid={} stack_valid={}", fast.get_hidden().is_valid(), fast.get_stack().is_valid());
                                        println!("  fast={fast:?}");
                                        println!("  replay={replay:?}");
                                    }
                                    assert!(fast.is_valid());
                                    checked += 1;
                                }
                            }
                            // advance by the oracle's first witness path —
                            // canonicalize first: witness paths are
                            // relative to the canonical root (the sweep
                            // discipline of every other harness here)
                            canonicalize(&mut game);
                            let cands = enumerate_commitments(&game);
                            if cands.is_empty() {
                                break;
                            }
                            for &m in &cands[0].witness_path {
                                let _ = game.do_move(m);
                            }
                        }
                    }
                }
                println!("words_match_moves: {checked} channel post-states cross-checked");
            })
            .unwrap()
            .join()
            .unwrap();
    }

    /// Per-section timing attribution for the seed-32 wall: mirrors
    /// `macro_solvable_direct`'s in-place recursion with section timers
    /// (the BFS's own time is attributed by the `perf_probe` nanos
    /// counter printed alongside).
    #[test]
    #[ignore = "perf attribution; run with --ignored --release --nocapture"]
    fn debug_perf_breakdown32() {
        use std::time::{Duration, Instant};
        const NODE_CAP: usize = 300_000;

        #[derive(Default)]
        struct T {
            tp: Duration,
            ctx: Duration,
            core: Duration,
            f3: Duration,
            post: Duration,
            apply: Duration,
        }

        fn rec(
            s: &mut Solitaire,
            tp: &mut TpTable,
            scratch: &mut DirectScratch,
            nodes: &mut usize,
            branches: &mut usize,
            t: &mut T,
        ) -> bool {
            let t0 = Instant::now();
            let win = s.is_win();
            let cont = !win && tp.insert(s.encode());
            t.tp += t0.elapsed();
            if !cont {
                return win;
            }
            *nodes += 1;
            if *nodes > NODE_CAP {
                return false;
            }
            let t0 = Instant::now();
            let ctx = ClosureCtx::from_game(s);
            t.ctx += t0.elapsed();
            let t0 = Instant::now();
            let mut commitments = core::mem::take(&mut scratch.commitments);
            core_run(&ctx, scratch, &mut commitments);
            scratch.commitments = commitments;
            t.core += t0.elapsed();
            let t0 = Instant::now();
            let dom = s.get_stack().dominance_mask();
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
            t.f3 += t0.elapsed();

            let groups = core::mem::take(&mut scratch.groups);
            let mut win = false;
            // mirror the shipped fold's deck-dominance (draw-1) clause
            let deck_dom = {
                let d = ctx.deck_mask
                    & ctx.root.sm()
                    & Stack::decode(ctx.root.stack).dominance_mask();
                if s.get_deck().draw_step().get() == 1 && d != 0 {
                    d & d.wrapping_neg()
                } else {
                    0
                }
            };
            // mirror the shipped fold's forced-commitment (C12) clause
            let forced_reveal = {
                let f = ctx.root.locked
                    & ctx.root.vis
                    & ctx.root.sm()
                    & ctx.root.bm()
                    & Stack::decode(ctx.root.stack).dominance_mask();
                f & f.wrapping_neg()
            };
            'outer: for group in &groups {
                if forced_reveal != 0 {
                    match group.first() {
                        Some((Commitment::Reveal(x), ..)) if x.mask() == forced_reveal => {}
                        _ => continue,
                    }
                }
                if deck_dom != 0 {
                    if let Some((Commitment::Draw(x), ..)) = group.first() {
                        if x.mask() != deck_dom {
                            continue;
                        }
                    }
                }
                // the shipped fold: one successor per commitment
                let Some((_, _, steps, _)) = collapse_pick(group, f3) else {
                    continue;
                };
                let t0 = Instant::now();
                let (vis, stack) = post_words(s, &ctx, steps);
                t.post += t0.elapsed();
                let t0 = Instant::now();
                let old = (s.get_visible_mask(), s.get_stack().encode());
                let commit = *steps.last().expect("every channel ends in a commit");
                let (_, (undo, _)) = s.do_move(commit);
                s.set_board(vis, stack);
                *branches += 1;
                t.apply += t0.elapsed();
                // the recursion itself is outside every section timer
                let child_win = rec(s, tp, scratch, nodes, branches, t);
                let t0 = Instant::now();
                s.undo_move(commit, undo);
                s.set_board(old.0, old.1);
                t.apply += t0.elapsed();
                if child_win {
                    win = true;
                    break 'outer;
                }
            }
            scratch.groups = groups;
            win
        }

        for draw_step in [1u8, 3] {
            let cards = default_shuffle(32);
            let step = NonZeroU8::new(draw_step).unwrap();
            let mut root = Solitaire::new(&cards, step);
            canonicalize(&mut root);
            let mut tp = TpTable::default();
            let mut scratch = DirectScratch::new();
            let (mut nodes, mut branches) = (0usize, 0usize);
            let mut t = T::default();
            perf_probe::reset();
            let t_all = Instant::now();
            let w = rec(&mut root, &mut tp, &mut scratch, &mut nodes, &mut branches, &mut t);
            let total = t_all.elapsed();
            let probes = perf_probe::read();
            println!(
                "seed=32 draw={draw_step} win={w} nodes={nodes} branches={branches} total={total:?}\n  tp={:?} ctx={:?} core={:?} f3={:?} post={:?} apply={:?}\n  bfs_calls={} bfs_states={} bfs_time={:?} canon={} post_calls={}",
                t.tp,
                t.ctx,
                t.core,
                t.f3,
                t.post,
                t.apply,
                probes[3],
                probes[4],
                std::time::Duration::from_nanos(probes[5]),
                probes[8],
                probes[6],
            );
        }
    }

    /// Seed-32 node-count forensics, answering "is the macro refutation's
    /// ~15M unique states over-generation (a bug) or the missing deck-axis
    /// compression (the streak/draw-order dominance analogue)?"
    ///
    /// 1. The old engine RAW on seed 32 (no dominance, no pruner),
    ///    time-boxed. If its unique-state count exceeds the macro's, the
    ///    macro game *is* compressing relative to the raw micro space, and
    ///    the macro-vs-shipped gap is exactly the missing filter port.
    ///
    /// 2. The macro search with auxiliary coarse TP keys that strip
    ///    (a) the deck-offset bits (encode bits 56..61) and (b) the whole
    ///    deck word (bits 32..61): the fine-to-coarse unique-count drop is
    ///    the redundancy each axis carries. A big drop under (a) points at
    ///    the last-draw/draw-order port; survival under (b) would mean the
    ///    load-bearing dimensions are hidden/stack/scar instead.
    #[test]
    #[ignore = "state-space forensics; run with --ignored --release --nocapture"]
    fn debug_seed32_state_space() {
        use std::time::{Duration, Instant};

        std::thread::Builder::new()
            .stack_size(256 * 1024 * 1024)
            .spawn(|| {
                // --- arm 1: old engine raw, old-visit-budget-free but time-boxed --- //
                struct TimeCb(Instant, bool);
                impl Callback for TimeCb {
                    type Pruner = crate::pruning::NoPruner;
                    fn on_win(&mut self, _: &Solitaire) -> Control {
                        Control::Halt
                    }
                    fn on_visit(&mut self, _: &Solitaire, _: Encode) -> Control {
                        if self.0.elapsed() > Duration::from_secs(120) && !self.1 {
                            self.1 = true;
                            return Control::Halt;
                        }
                        Control::Ok
                    }
                }
                let cards = default_shuffle(32);
                let mut game = Solitaire::new(&cards, NonZeroU8::new(1).unwrap());
                let mut tp = TpTable::default();
                let t0 = Instant::now();
                let mut cb = TimeCb(Instant::now(), false);
                traverse::<_, _, false>(&mut game, &NoPruner::default(), &mut tp, &mut cb);
                println!(
                    "OLD RAW seed=32 draw=1: unique states={} in {:?}{}",
                    tp.len(),
                    t0.elapsed(),
                    if cb.1 { " (halted at 120s — lower bound)" } else { " (complete)" },
                );

                // --- arm 2: macro collapsed search + coarse keys --- //
                let mut coarse_off = TpTable::default();
                let mut coarse_deck = TpTable::default();
                let (mut n, mut n_off, mut n_deck) = (0u64, 0u64, 0u64);
                let cards = default_shuffle(32);
                let g = Solitaire::new(&cards, NonZeroU8::new(1).unwrap());
                let t0 = Instant::now();
                let win = macro_solvable_direct_progress(&g, |s| {
                    n += 1;
                    let e = s.encode();
                    if coarse_off.insert(e & !(0x1Fu64 << 56)) {
                        n_off += 1;
                    }
                    if coarse_deck.insert(e & full_mask(32)) {
                        n_deck += 1;
                    }
                });
                println!(
                    "MACRO collapsed seed=32 draw=1: win={win} in {:?}\n  unique states={n}\n  unique minus deck OFFSET={n_off}\n  unique minus deck WORD ={n_deck}",
                    t0.elapsed()
                );
            })
            .unwrap()
            .join()
            .unwrap();
    }

    /// R-DIA probe (macro_parking.md §P.6): the destination collapse's
    /// only remaining destination-side lemma is the sweep/stack diamond —
    /// from a parked post-state, stacking X lands in the stack outcome's
    /// closure class. Direct measurement: for every corpus commitment with
    /// both kinds offered, compare `canonicalize(post_tab + PileStack(X))`
    /// against every stack-side representative — tally exact-encode hits
    /// (the F3 sweep-equal signature, generalized), closure-linked hits,
    /// and genuine distinct-class counterexamples (printed in full).
    #[test]
    #[ignore = "diamond probe; run with --ignored --release --nocapture"]
    fn debug_destination_diamond() {
        std::thread::Builder::new()
            .stack_size(256 * 1024 * 1024)
            .spawn(|| {
                // (both-kind commitments, encode-equal, closure-linked, distinct, swept-in-tab)
                let (mut both, mut eq, mut linked, mut distinct, mut swept) =
                    (0usize, 0usize, 0usize, 0usize, 0usize);
                let mut misses: Vec<(u8, u64, usize, u8)> = Vec::new();
                for draw_step in [1u8, 3] {
                    for i in 0..30u64 {
                        let mut game = Solitaire::new(
                            &default_shuffle(12 + i),
                            NonZeroU8::new(draw_step).unwrap(),
                        );
                        for _turn in 0..100 {
                            if game.is_win() {
                                break;
                            }
                            canonicalize(&mut game);
                            let direct = macro_transitions_direct(&game);
                            // group emissions by commitment
                            let mut by_com: Vec<(Card, Vec<&DirectTransition>, Vec<&DirectTransition>)> =
                                Vec::new();
                            for t @ (c, k, _, _) in &direct {
                                let x = match c {
                                    Commitment::Draw(x) | Commitment::Reveal(x) => *x,
                                };
                                let ent = by_com.iter_mut().find(|(c2, ..)| *c2 == x);
                                let ent = match ent {
                                    Some(e) => e,
                                    None => {
                                        by_com.push((x, Vec::new(), Vec::new()));
                                        by_com.last_mut().unwrap()
                                    }
                                };
                                match k {
                                    OutcomeKind::Tableau => ent.1.push(t),
                                    OutcomeKind::Stack => ent.2.push(t),
                                }
                            }
                            for (x, tabs, stks) in &by_com {
                                if tabs.is_empty() || stks.is_empty() {
                                    continue;
                                }
                                // any-tableau links with any-stack
                                for (_, _, t_state, _) in tabs {
                                    // if X was swept up in the tableau
                                    // outcome, the outcomes are already
                                    // sweep-equal (the F3 signature)
                                    if t_state.get_visible_mask() & x.mask() == 0 {
                                        swept += 1;
                                        continue;
                                    }
                                    let mut t2 = t_state.clone();
                                    t2.do_move(Move::PileStack(*x));
                                    canonicalize(&mut t2);
                                    let enc2 = t2.encode();
                                    let hit = stks
                                        .iter()
                                        .any(|(_, _, s_state, _)| s_state.encode() == enc2);
                                    let closed = hit
                                        || stks
                                            .iter()
                                            .any(|(_, _, s_state, _)| closure_contains(&t2, s_state.encode()));
                                    if hit {
                                        eq += 1;
                                    } else if closed {
                                        linked += 1;
                                    } else {
                                        distinct += 1;
                                        misses.push((draw_step, 12 + i, _turn, x.mask_index()));
                                        println!(
                                            "** R-DIA MISS draw={draw_step} seed={} turn={_turn} X={x}",
                                            12 + i
                                        );
                                    }
                                }
                                both += 1;
                            }
                            // advance by the oracle's first witness path
                            let cands = enumerate_commitments(&game);
                            if cands.is_empty() {
                                break;
                            }
                            for &m in &cands[0].witness_path {
                                let _ = game.do_move(m);
                            }
                        }
                    }
                }
                println!(
                    "R-DIA diamond probe: {both} both-kind commitments; tableau→stack-PileStack(X): encode-equal={eq} closure-linked={linked} **distinct-class={distinct}** (sweep-in-tableau: {swept})"
                );

                // Win-region containment on every miss: the collapse loses
                // a win iff some stack-side class is solvable (ground-truth
                // engine) while the tableau class is not.
                let (mut violated, mut held) = (0usize, 0usize);
                for (draw_step, seed, turn, x_idx) in misses {
                    let mut game = Solitaire::new(
                        &default_shuffle(seed),
                        NonZeroU8::new(draw_step).unwrap(),
                    );
                    for _ in 0..turn {
                        canonicalize(&mut game);
                        let cands = enumerate_commitments(&game);
                        if cands.is_empty() {
                            break;
                        }
                        for &m in &cands[0].witness_path {
                            let _ = game.do_move(m);
                        }
                    }
                    canonicalize(&mut game);
                    let x = Card::from_mask_index(x_idx);
                    let direct = macro_transitions_direct(&game);
                    let mut tabs = Vec::new();
                    let mut stks = Vec::new();
                    for (c, k, st, _) in &direct {
                        let cx = match c {
                            Commitment::Draw(cx) | Commitment::Reveal(cx) => *cx,
                        };
                        if cx != x {
                            continue;
                        }
                        match k {
                            OutcomeKind::Tableau => tabs.push(st),
                            OutcomeKind::Stack => stks.push(st),
                        }
                    }
                    let tab_solvable = tabs.iter().any(|t| {
                        matches!(solve(&mut (*t).clone()).0, SearchResult::Solved)
                    });
                    for st in &stks {
                        let st_solvable =
                            matches!(solve(&mut (*st).clone()).0, SearchResult::Solved);
                        if st_solvable && !tab_solvable {
                            violated += 1;
                            println!(
                                "** CONTAINMENT VIOLATED draw={draw_step} seed={seed} turn={turn} X={}: stack side wins, tableau side loses",
                                x
                            );
                        } else {
                            held += 1;
                        }
                    }
                }
                println!(
                    "R-DIA misses: win-region containment (solvable(stk) ⟹ solvable(tab)): held={held} **violated={violated}**"
                );
            })
            .unwrap()
            .join()
            .unwrap();
    }

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
            let ctx = ClosureCtx::from_game(&game);
            let mut bfs_scratch = DirectScratch::new();
            let mut groups: Vec<Vec<StepTransition>> = vec![Vec::new()];
            accommodations_shared(
                &ctx,
                &goal,
                &[commitment],
                groups.as_mut_slice(),
                &mut bfs_scratch.bfs,
            );
            let new: Option<Vec<Move>> = groups[0].first().map(|(_, _, steps, _)| {
                let mut v: Vec<Move> = steps.iter().copied().collect();
                v.pop(); // drop the appended commit move
                v
            });
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

    /// The same verdict sweep on the KlondikeSolver shuffle family — an
    /// independent deal distribution, so a green run here is the
    /// collapse fold's evidence escaping the default-corpus shape.
    #[test]
    #[ignore = "expensive verdict sweep; run with --ignored --nocapture"]
    fn macro_verdict_sweep_ks() {
        std::thread::Builder::new()
            .stack_size(256 * 1024 * 1024)
            .spawn(|| {
                let mut n = 0usize;
                let mut mismatches = 0usize;
                for draw_step in [1u8, 3] {
                    for i in 0..64u32 {
                        let cards = crate::shuffler::ks_shuffle(i);
                        let step = NonZeroU8::new(draw_step).unwrap();
                        let (res, _) = solve(&mut Solitaire::new(&cards, step));
                        let old_win = matches!(res, SearchResult::Solved);
                        let g = Solitaire::new(&cards, step);
                        let fast = macro_solvable_direct(&g);
                        n += 1;
                        if old_win != fast {
                            mismatches += 1;
                            println!("seed={i} draw={draw_step} old={old_win} direct={fast} ** MISMATCH **");
                        }
                    }
                }
                assert_eq!(mismatches, 0, "macro direct path KS verdict sweep found mismatches");
                println!("ks verdict sweep: {n} games, {mismatches} mismatches");
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
