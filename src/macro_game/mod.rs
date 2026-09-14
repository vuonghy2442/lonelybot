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
//!   bounded shared BFS for the crease — emitting steps, not states. The
//!   goal set is trimmed two ways: the fold-mode cut (search path only,
//!   provably selection-neutral — ledger C14) and the `goal_dead` kills
//!   (necessary conditions from the closure algebra — ledger C15, both
//!   derived in macro_formalization.md §8).
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

use crate::card::{Card, KING_MASK, N_CARDS, SUIT_MASK};
use crate::deck::{Deck, N_PILES};
use crate::moves::{Move, MoveMask, N_MOVES_MAX};
use crate::stack::Stack;
use crate::state::{bottom_mask_of, swap_pair, Encode, Solitaire};
use crate::traverse::TpTable;
use crate::utils::full_mask;


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

/// Per-suit single-bit table: `SUIT_NEXT[s][h]` is exactly the bit
/// `Stack::mask` contributes for suit `s` at height `h` — the next
/// stackable card's position (a phantom bit ≥ 52 when the suit is
/// complete, matching `Stack::mask`'s arithmetic). Table lookups instead
/// of nibble arithmetic on the hot path (BFS states, probes, sweeps).
const SUIT_NEXT: [[u64; 16]; 4] = {
    let mut t = [[0u64; 16]; 4];
    let mut s = 0;
    while s < 4 {
        let mut h = 0;
        while h < 16 {
            t[s][h] = SUIT_MASK[s] & (0xFu64 << (4 * h));
            h += 1;
        }
        s += 1;
    }
    t
};

/// Per-suit stacked-prefix masks: `SUIT_PREFIX[s][h]` = the cards of suit
/// `s` with rank `< h`. The table form of the old per-card loop — a
/// closure state's `vis` derivation (`words_at`) reads it four times per
/// BFS state.
const SUIT_PREFIX: [[u64; 16]; 4] = {
    let mut t = [[0u64; 16]; 4];
    let mut s = 0;
    while s < 4 {
        let mut r = 0;
        while r < 13 {
            t[s][r + 1] = t[s][r] | Card::new(r as u8, s as u8).mask();
            r += 1;
        }
        // heights 14/15 are unreachable on a valid board; mirror 13 so the
        // table stays total without fabricating card bits
        t[s][14] = t[s][13];
        t[s][15] = t[s][13];
        s += 1;
    }
    t
};

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

    /// `Stack::mask` table-driven: four single-bit lookups instead of the
    /// nibble arithmetic (the table reproduces it bit-for-bit, including
    /// the ≥13 phantom-bit sentinels).
    fn sm(self) -> u64 {
        let s = self.stack;
        SUIT_NEXT[0][usize::from(s & 0xF)]
            | SUIT_NEXT[1][usize::from((s >> 4) & 0xF)]
            | SUIT_NEXT[2][usize::from((s >> 8) & 0xF)]
            | SUIT_NEXT[3][usize::from((s >> 12) & 0xF)]
    }

    /// Raw `pile_stack` mask (`bm & vis & sm`) — locked cards included, as
    /// in `gen_moves::<false>`; the unlock check is the caller's business.
    fn pile_stack(self) -> u64 {
        self.bm() & self.vis & self.sm()
    }

    /// Every raw move mask, identical formulas to `gen_moves::<false>`
    /// (with dominances off that function never early-returns, so the pure
    /// formulas are the whole semantics). The §6.4 probes and the word BFS
    /// both read legality through this.
    ///
    /// `bm`/`sm` are computed once here — the old shape rederived them via
    /// `free_slot`/`pile_stack` (two extra `bm`s and one `sm` per call).
    fn move_masks(self, deck_mask: u64, first_layer: u64) -> MoveMask {
        let bm = self.bm();
        let sm = self.sm();
        let extended = self.vis & (self.locked | KING_MASK);
        let king = if extended.count_ones() < u32::from(N_PILES) {
            KING_MASK
        } else {
            0
        };
        let free_slot = (bm >> 4) | king;
        MoveMask {
            pile_stack: bm & self.vis & sm,
            deck_stack: deck_mask & sm,
            stack_pile: swap_pair(sm >> 4) & free_slot,
            deck_pile: deck_mask & free_slot,
            reveal: self.vis & self.locked & free_slot & !(first_layer & KING_MASK),
        }
    }

    /// The sweep candidate rule, word form: the same set
    /// `Solitaire::safe_sweep_candidates` computes on the concrete state.
    fn sweep_cands(self) -> u64 {
        let bm = self.bm();
        (bm & self.vis & self.sm()) & Stack::decode(self.stack).dominance_mask() & !self.locked
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
/// Table form: four lookups instead of the per-card construction loop —
/// `words_at` pays this once per BFS state.
const fn stacked_mask(stack: u16) -> u64 {
    #[allow(clippy::cast_possible_truncation)]
    let (n0, n1, n2, n3) = (
        (stack & 0xF) as usize,
        ((stack >> 4) & 0xF) as usize,
        ((stack >> 8) & 0xF) as usize,
        ((stack >> 12) & 0xF) as usize,
    );
    SUIT_PREFIX[0][n0] | SUIT_PREFIX[1][n1] | SUIT_PREFIX[2][n2] | SUIT_PREFIX[3][n3]
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
    /// the per-suit climb frontier: the first rank `r ≥ h₀(s)` whose
    /// card `(r, s)` is NOT root-visible-and-unlocked (13 when the
    /// whole climb is open). K1's first-passage blockedness and K6's
    /// climb-blocked twin test are `frontier[s] < rank(c)` — one
    /// comparison instead of the per-goal prefix walk.
    frontier: [u8; 4],
}

impl ClosureCtx {
    fn from_game(g: &Solitaire) -> Self {
        let root = Words::from_game(g);
        // nonvis_base = buried | deck-remaining, derived instead of
        // iterated: `vis = full ^ nonvis_base ^ stacked` inverted at the
        // root (the visible-set invariant, `is_valid`-checked on the test
        // corpus). Reads no per-card state.
        let nonvis_base = full_mask(N_CARDS) ^ root.vis ^ stacked_mask(root.stack);
        // the per-suit climb frontier: the first rank at or above the
        // foundation height whose card is not root-visible-and-unlocked
        // (13 = the climb is open). K1's blockedness test and K6's
        // twin test are `frontier[s] < rank(c)` — O(1) per goal.
        let mut frontier = [13u8; 4];
        for s in 0..4u8 {
            let h0 = root.height(s);
            let mut r = h0;
            while r < 13 {
                let m = Card::new(r, s).mask();
                if root.vis & m == 0 || root.locked & m != 0 {
                    frontier[usize::from(s)] = r;
                    break;
                }
                r += 1;
            }
        }
        Self {
            root,
            deck_mask: g.get_deck().compute_mask(false),
            first_layer: g.get_hidden().first_layer_mask(),
            nonvis_base,
            frontier,
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
    /// The offset-dominance registry (the pace-dominance rules R1/R2,
    /// the 2026-09 family filed in lean-model Macro.lean): per
    /// `(state-sans-offset-bits, residue class)`, the minimal refuted
    /// impure offset. The soundness is the pace-dominance theorem
    /// (`pace_dominance`): within an impure residue class the earlier
    /// cursor accesses a superset (block-1 monotone) and a common draw
    /// merges the lines (the successor offset is the drawn position,
    /// parent-invariant) — so a refuted offset kills every later one
    /// in its class (R1), and any impure refutation kills the pure
    /// sibling (R2: the pure accessible set is contained in every
    /// impure one). Pinned by `pace_dominance_order` (100 random decks
    /// × all offsets) and the deck-lattice measurement: the ceiling is
    /// 43.8% of seed-32 draw-3 states. Pure offsets need no
    /// self-entries — the deck encode already normalizes them — so
    /// class 0 is written only as the R2 mark and read only by pure
    /// states; draw-1 is exempt entirely (all its offsets are pure).
    /// Corpus-gated [~]: the falsifiers are the verdict sweeps and the
    /// KS-shuffle sweep.
    fn rec(
        s: &mut Solitaire,
        tp: &mut TpTable,
        scratch: &mut DirectScratch,
        hook: &mut Option<&mut dyn FnMut(&Solitaire)>,
    ) -> bool {
        #[cfg(test)]
        let t_tp = std::time::Instant::now();
        let enc = s.encode();
        if s.is_win() || !tp.insert(enc) {
            return s.is_win();
        }
        if let Some(h) = hook {
            h(s);
        }
        #[cfg(test)]
        perf_probe::bump_tp_time(t_tp.elapsed());
        let step = s.get_deck().draw_step().get();
        if step == 1 {
            return rec_go(s, tp, scratch, hook, enc);
        }
        let off = s.get_deck().get_offset();
        let n = s.get_deck().len();
        let sans = (enc & !(0x1Fu64 << 56)) << 2;
        if off % step == 0 || off == n {
            // pure: dominated by ANY refuted impure sibling (R2)
            if scratch.offset_registry.contains_key(&sans) {
                #[cfg(test)]
                perf_probe::bump_reg();
                return false;
            }
            rec_go(s, tp, scratch, hook, enc)
        } else {
            let key = sans | u64::from(off % step);
            if scratch.offset_registry.get(&key).is_some_and(|&m| m <= off) {
                #[cfg(test)]
                perf_probe::bump_reg();
                return false;
            }
            let res = rec_go(s, tp, scratch, hook, enc);
            if !res {
                scratch
                    .offset_registry
                    .entry(key)
                    .and_modify(|m| *m = (*m).min(off))
                    .or_insert(off);
                // R2's mark: the pure sibling is dominated too
                scratch
                    .offset_registry
                    .entry(sans)
                    .and_modify(|m| *m = (*m).min(off))
                    .or_insert(off);
            }
            res
        }
    }
    fn rec_go(
        s: &mut Solitaire,
        tp: &mut TpTable,
        scratch: &mut DirectScratch,
        hook: &mut Option<&mut dyn FnMut(&Solitaire)>,
        enc: Encode,
    ) -> bool {
        let ctx = ClosureCtx::from_game(s);

        // forced-commitment dominance (ledger C12), hoisted above the
        // generator: a locked dominantly-stackable surface's Reveal
        // (stack outcome) is the node's only explored successor, and its
        // stack-direct channel provably exists — the forced mask is a
        // subset of `bm & vis & sm = pile_stack` — so at these nodes the
        // whole rule list, the shared BFS, and the group loop are dead
        // work. Measured on the search path (probe
        // `debug_forced_and_deck_dom_rate`): fires at ~11% of draw-1 /
        // ~15% of draw-3 nodes.
        let forced_reveal = {
            let f = ctx.root.locked
                & ctx.root.vis
                & ctx.root.sm()
                & ctx.root.bm()
                & Stack::decode(ctx.root.stack).dominance_mask();
            f & f.wrapping_neg()
        };
        if forced_reveal != 0 {
            let x = Card::from_mask_index(
                u8::try_from(forced_reveal.trailing_zeros()).unwrap(),
            );
            let steps = [Move::PileStack(x)];
            let (vis, stack) = post_words(s, &ctx, &steps);
            // TP pre-probe: on a hit the sole successor contributes
            // false — exactly what the recursive call would return
            if tp.contains(&successor_encode(s, steps[0], stack, enc)) {
                return false;
            }
            let old = (s.get_visible_mask(), s.get_stack().encode());
            let undo = apply_commit(s, steps[0]);
            s.set_board(vis, stack);
            let child_win = rec(s, tp, scratch, hook);
            undo_commit(s, steps[0], undo);
            s.set_board(old.0, old.1);
            return child_win;
        }

        // Deck-source dominance — the draw-1 clause of the engine's
        // cascade (state.rs): when a drawable deck card is dominantly
        // stackable, the lowest such card is the only deck commitment
        // worth branching on (you can always stack it first without
        // helping anything else). Reveal commitments are untouched.
        // Search-fold policy (like F3): the generator stays total so the
        // differential sees all channels. Corpus-gated [~] with the named
        // falsifier (ledger C9).
        //
        // note: the C5/is_pure port was falsified (seed 21 d1 flips
        // old=win -> macro=loss): Deck::is_pure's offset-at-boundary
        // premise doesn't survive the macro's offset-jumping draws, so
        // the "pure" states the old rule fired at and the macro states
        // it would fire at don't correspond. Ledger row C11.
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

        let mut commitments = core::mem::take(&mut scratch.commitments);
        #[cfg(test)]
        let t_core = std::time::Instant::now();
        core_run(&ctx, scratch, &mut commitments, true, s.get_deck());
        #[cfg(test)]
        perf_probe::bump_core_time(t_core.elapsed());
        scratch.commitments = commitments;

        // F3 dominance drop: tableau outcomes of dominantly stackable
        // commitments with a direct stack outcome (same fold as the
        // materialized path). `core_run` derives it from the raw masks —
        // bits of (pile_stack ∩ locked surfaces) ∪ deck_stack under
        // dominance, exactly the commitments carrying a stack-direct
        // entry — so no post-hoc group scan.
        let f3 = scratch.f3;

        // take the working vecs out so the recursion can reuse the scratch
        let groups = core::mem::take(&mut scratch.groups);
        let mut win = false;
        'outer: for group in &groups {
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
            #[cfg(test)]
            perf_probe::bump_sel(_ch.ends_with("bfs"));
            #[cfg(test)]
            let t_branch = std::time::Instant::now();
            let (vis, stack) = post_words(s, &ctx, steps);
            let commit = *steps.last().expect("every channel ends in a commit");
            // TP pre-probe: compute the successor's encode without
            // applying — on a hit (75% of branches on the hard
            // refutations) the apply/undo pair is dead work
            if tp.contains(&successor_encode(s, commit, stack, enc)) {
                #[cfg(test)]
                perf_probe::bump_branch_time(t_branch.elapsed());
                continue;
            }
            let old = (s.get_visible_mask(), s.get_stack().encode());
            let undo = apply_commit(s, commit);
            s.set_board(vis, stack);
            #[cfg(test)]
            perf_probe::bump_branch_time(t_branch.elapsed());
            let child_win = rec(s, tp, scratch, hook);
            #[cfg(test)]
            let t_undo = std::time::Instant::now();
            undo_commit(s, commit, undo);
            s.set_board(old.0, old.1);
            #[cfg(test)]
            perf_probe::bump_branch_time(t_undo.elapsed());
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
    /// Dedup over closure states. A closure state *is* its u16 stack word,
    /// so dedup is a generation stamp over the whole u16 range:
    /// `seen[w] == seen_gen` marks `w` visited this call. Direct indexing
    /// instead of hashing, and the generation bump replaces clearing
    /// 256 KB per call.
    seen: Vec<u32>,
    seen_gen: u32,
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
    /// the offset-dominance registry (rules R1/R2, see `rec` in
    /// `macro_solvable_direct_impl`): key = (encode with the offset
    /// bits masked out, shifted) | residue class — class 0 is the pure
    /// sibling's R2 mark; value = the minimal refuted impure offset.
    offset_registry: hashbrown::HashMap<u64, u8, crate::utils::MixHasherBuilder>,
    /// the F3 mask (dominantly stackable commitments with a stack-direct
    /// outcome), derived by `core_run` from the raw masks; the search
    /// fold reads it instead of rescanning the emitted groups.
    f3: u64,
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
                seen: alloc::vec![0; 1 << 16],
                seen_gen: 0,
            },
            fold_seen: Vec::new(),
            out: Vec::new(),
            offset_registry: hashbrown::HashMap::default(),
            f3: 0,
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
    let gen = {
        let g = scratch.seen_gen.wrapping_add(1);
        scratch.seen_gen = if g == 0 {
            scratch.seen.fill(0);
            1
        } else {
            g
        };
        scratch.seen_gen
    };
    let arena = &mut scratch.arena;
    let queue = &mut scratch.queue;
    let seen = &mut scratch.seen;
    arena.clear();
    queue.clear();
    arena.push((usize::MAX, Move::PileStack(Card::DEFAULT), 0));
    queue.push_back((ctx.root.stack, 0));
    seen[usize::from(ctx.root.stack)] = gen;

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
            let wi = usize::from(w2.stack);
            if seen[wi] != gen {
                seen[wi] = gen;
                let child = arena.len();
                arena.push((idx, m, (depth + 1) as u16));
                queue.push_back((w2.stack, child));
            }
        }
    }
    for (gi, goal) in goals.iter().enumerate() {
        let ans = answers[gi];
        if ans == NONE {
            #[cfg(test)]
            {
                perf_probe::bump_crease_miss();
                let x = match goal.commitment {
                    Commitment::Draw(x) | Commitment::Reveal(x) => x,
                };
                let s = x.suit();
                let k = match goal.kind {
                    OutcomeKind::Stack => {
                        if ctx.root.height(s) < x.rank() {
                            0
                        } else {
                            1
                        }
                    }
                    OutcomeKind::Tableau => 2,
                };
                perf_probe::bump_miss_kind(k);
            }
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
        #[cfg(test)]
        {
            let n = steps.len();
            let shuffles = &steps[..n - 1];
            let alt = shuffles.iter().any(|m| matches!(m, Move::PileStack(_)))
                && shuffles.iter().any(|m| matches!(m, Move::StackPile(_)));
            perf_probe::bump_crease(n - 1, alt);
        }
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

/// The per-pile weights of the hidden encode's positional fold: the
/// encode is `Σ n_hidden[i] · Π_{j<i}(j+2)`, so a pile count decrement
/// (a reveal commit) is a subtraction of one weight — O(1) instead of
/// the fold.
const HIDDEN_WEIGHT: [u16; 7] = [1, 2, 6, 24, 120, 720, 5040];

/// The commit application, deck/hidden effects only. `do_move` computes
/// `reverse_move` (the search discards it) and performs board edits
/// that the immediately-following `set_board` overwrites — this pair
/// applies only the lasting effects (the deck draw with its offset,
/// the hidden pop) and undoes them. Bit-identical successors: the
/// board is carried by the word pipeline (`post_words` + `set_board`),
/// not by the state's own edit path.
fn apply_commit(s: &mut Solitaire, m: Move) -> u8 {
    match m {
        Move::DeckPile(c) | Move::DeckStack(c) => {
            let (_, pos) = s.get_deck().find_card(c);
            let old = s.get_deck().get_offset();
            let _ = s.get_deck_mut().draw(pos);
            old
        }
        // Reveal commits and reveal-by-stacking (PileStack on a locked
        // card — the only PileStack that is a commit): pop the surface
        Move::Reveal(c) | Move::PileStack(c) => {
            let _ = s.get_hidden_mut().pop_card(c);
            0
        }
        // a StackPile is always a reversible shuffle step, never a commit
        Move::StackPile(_) => unreachable!("commit moves are irreversible"),
    }
}

fn undo_commit(s: &mut Solitaire, m: Move, undo: u8) {
    match m {
        Move::DeckPile(c) | Move::DeckStack(c) => {
            s.get_deck_mut().push(c);
            s.get_deck_mut().set_offset(undo);
        }
        Move::Reveal(c) | Move::PileStack(c) => {
            let _ = s.get_hidden_mut().unpop_card(c);
        }
        Move::StackPile(_) => unreachable!("commit moves are irreversible"),
    }
}

/// The successor's full encode, computed WITHOUT applying the commit:
/// the swept stack word from `post_words`, the hidden word as the
/// parent's minus the reveal's pile-weight delta, and the deck word as
/// the parent's with the drawn card's position-bit cleared and the
/// offset set to the drawn position (with `is_pure` normalization —
/// `normalized_offset`'s rule, post-draw: the new length when the
/// position is aligned or is the last).  The TP pre-probe's key: on a
/// hit, the whole apply/undo pair is dead work — the branch
/// contributes `false` exactly as the recursive `rec` on the TP-hit
/// state would (win states never enter the table — `rec` returns
/// before inserting them — and no macro-game cycle can put an
/// in-progress state on the hit path, commitments being irreversible).
fn successor_encode(s: &Solitaire, commit: Move, stack: u16, enc: Encode) -> Encode {
    let hidden = ((enc >> 16) & 0xFFFF) as u16;
    let deck = (enc >> 32) as u32;
    match commit {
        // reveal commits (plain reveal or reveal-by-stacking): the
        // hidden pile under `c` shrinks by one, the deck is untouched
        Move::Reveal(c) | Move::PileStack(c) => {
            let pos = s.get_hidden().find(c);
            let hidden = hidden.wrapping_sub(HIDDEN_WEIGHT[usize::from(pos)]);
            u64::from(stack) | (u64::from(hidden) << 16) | (u64::from(deck) << 32)
        }
        // draw commits: the deck loses the card, the offset jumps to
        // the drawn position
        Move::DeckPile(c) | Move::DeckStack(c) => {
            let (_, pos) = s.get_deck().find_card(c);
            let v = s.get_deck().position_bit(c);
            let mask = (deck & !v) & 0xFF_FFFF;
            let new_len = mask.count_ones();
            let step = u8::from(s.get_deck().draw_step().get());
            let off = if pos % step == 0 || pos == new_len as u8 {
                new_len
            } else {
                u32::from(pos)
            };
            u64::from(stack)
                | (u64::from(hidden) << 16)
                | (u64::from(mask | (off << 24)) << 32)
        }
        // a StackPile is always a reversible shuffle step, never a commit
        Move::StackPile(_) => unreachable!("commit moves are irreversible"),
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

/// Cheap necessary conditions for an accommodation goal to open anywhere
/// in the reversible closure — the mathematical BFS kill.
///
/// Inside the closure `vis(w) ⊆ root.vis ∪ worried-back(w)`, and a
/// worry-back can only surface a card that is on the foundation at the
/// root — i.e. a card of rank `< h₀(suit)` (the foundation is a prefix).
/// Deck cards and buried cards never enter `vis` at all. Therefore:
///
/// * **Stack goal on X** (needs `sm ∋ X`, i.e. the suit climbs from `h₀`
///   to `rank(X)`): every missing prefix card is stacked exactly once on
///   the way up, and at that moment it must be visible — which for ranks
///   `≥ h₀` can only mean *root-visible and unlocked* (worry-backs only
///   surface ranks `< h₀`; locked cards cannot stack in the closure).
///   A missing prefix card that is buried, in the deck, or locked kills
///   the goal. Descent (`h₀ > rank(X)`) takes no cheap kill.
/// * **Tableau goal on X** (non-king: X opens through a receiver *type*
///   at `rank(X)+1`, opposite color — `free_slot = (bm >> 4) | king`
///   spreads the receiver type to X's bit): the type needs a visible
///   member at the opening state — root-visible or worried back from the
///   root foundation. Neither twin qualifying kills the goal. Kings only
///   open through the empty-pile gate, which has no receiver — no
///   receiver-side kill, but two conjunct-side ones:
/// * **K4 (tableau goal on a first-layer king, Reveal commitments).** A
///   Reveal commitment's tableau goal opens only through the reveal
///   mask, whose `!(first_layer & KING_MASK)` conjunct permanently
///   excludes locked surface kings at the bottom of their pile (a lone
///   king has nothing under it to reveal — surfacing it is not a reveal).
///   The first layer is closure-invariant (Lemma A1: shuffles never
///   touch the hidden structures), and a locked card can never leave
///   `vis` inside the closure (locked cards never shuffle-stack), so the
///   conjunct kills the bit at *every* closure word. Draw commitments are
///   exempt: deck kings open through `deck_pile`'s empty-pile gate,
///   which the exclusion does not touch. Measured (probe
///   `debug_crease_cases`): 3% of missed goals but 17.3% of the miss
///   cost — the lone-king endgame boards carry the corpus's largest
///   closures (2.2k–2.8k states).
/// * **K5 (tableau goal on any king, saturated boards).** The empty-pile
///   gate reads `extended = vis & (locked | KING)` with `count_ones() <
///   N_PILES`; inside the closure the `vis ∩ locked` part — the locked
///   surfaces — is exactly invariant (a locked card never stacks, that
///   is a reveal commitment, and no other closure move removes a visible
///   card). When all N_PILES piles still carry a locked surface, the
///   count is pinned ≥ N_PILES at every closure word (the free-king and
///   worry-back terms only add), so the gate never opens and every king
///   tableau goal — deck or locked, first-layer or not — is dead without
///   the walk. Every root qualifies; this is the early-game mass.
///
/// * **K5 (tableau goal on any king, saturated boards)** (see the arm —
///   the empty-pile gate's surface count is pinned).
/// * **K6 (the four-card ball)**: X deck or locked means
///   `free[X] ≡ 0` in the closure, and the receivers' under-pair is
///   `{X, twin(X)}` — §8.1's receiver movability reduces to
///   `(vis[R] ∨ vis[R']) ∧ (¬free[twin] ∨ (vis[R] ⊕ vis[R'] ⊕
///   free[twin]))`. One dead receiver (never enters `vis`) plus a
///   root-free climb-blocked twin(X) (never stacks — K1's
///   first-passage test on twin's suit — so `free[twin] ≡ 1`) makes
///   both disjunct branches self-cancel. Measured coverage: 76% of
///   the tableau miss mass surviving K1–K5 (probe `debug_k6_signature`).
///
/// A killed goal provably has no BFS answer, so skipping it changes no
/// successor in either mode — pure search cost. Gates:
/// `macro_direct_matches_oracle` (the differential would count a wrong
/// kill as a missing outcome) and the verdict sweeps.
fn goal_dead(ctx: &ClosureCtx, commitment: Commitment, kind: OutcomeKind) -> bool {
    let x = match commitment {
        Commitment::Draw(x) | Commitment::Reveal(x) => x,
    };
    match kind {
        OutcomeKind::Stack => {
            let s = x.suit();
            let h0 = ctx.root.height(s);
            if h0 >= x.rank() {
                return false;
            }
            // K1: some prefix card in [h₀, rank) is not root-visible and
            // unlocked — the first-passage argument (worry-backs surface
            // only ranks < h₀; locked cards never stack in the closure)
            ctx.frontier[usize::from(s)] < x.rank()
        }
        OutcomeKind::Tableau => {
            // K4: the reveal mask's first-layer king exclusion is
            // closure-invariant, so a lone locked surface king's tableau
            // goal never opens anywhere
            if let Commitment::Reveal(r) = commitment {
                if r.rank() == crate::card::KING_RANK && ctx.first_layer & r.mask() != 0 {
                    return true;
                }
            }
            if x.rank() == crate::card::KING_RANK {
                // K5: kings park only through the empty-pile gate, which
                // reads `extended = vis & (locked | KING)` with count <
                // N_PILES. Inside the closure `vis ∩ locked` — the set of
                // locked surfaces — is exactly invariant: a locked card
                // never stacks (that is a reveal commitment), no other
                // closure move removes a visible card, and buried cards
                // never surface. The free-king and worry-back terms of the
                // count are non-negative, so with all N_PILES piles still
                // carrying a locked surface the count is pinned ≥ N_PILES
                // at every closure word — the gate never opens, and every
                // king tableau goal (deck or locked, any pile shape) is
                // dead without the walk.
                return (ctx.root.vis & ctx.root.locked).count_ones() >= u32::from(N_PILES);
            }
            // K6: the four-card ball {X, twin(X), R1, R2}. X is deck or
            // locked (every commitment target is), so `free[X] ≡ 0` in
            // the closure, and the receivers' under-pair IS {X, twin(X)}
            // — §8.1's movability of a receiver reduces to
            // `(vis[R] ∨ vis[R']) ∧ (¬free[twin(X)] ∨
            // (vis[R] ⊕ vis[R'] ⊕ free[twin(X)]))`. When one receiver is
            // dead (buried or deck — never enters `vis`) and twin(X) is
            // root-free but climb-blocked (K1's first-passage test on
            // twin's suit: a missing prefix card not root-visible and
            // unlocked — so twin never stacks, `free[twin(X)] ≡ 1`
            // forever, and it never leaves `vis` either), the condition
            // collapses to `vis[R₂] ∧ ¬vis[R₂]` — self-cancelling in
            // both branches, regardless of the surviving receiver's
            // status. Measured (debug_k6_signature): 76% of the tableau
            // miss mass surviving K1–K5.
            {
                let twin = x.swap_suit();
                let tm = twin.mask();
                let twin_free =
                    ctx.root.vis & tm != 0 && ctx.root.locked & tm == 0;
                if twin_free && ctx.frontier[usize::from(twin.suit())] < twin.rank() {
                    let r = x.rank() + 1;
                    let s = x.suit();
                    let stacked_now = stacked_mask(ctx.root.stack);
                    let dead = |p: Card| {
                        let m = p.mask();
                        ctx.root.vis & m == 0 && stacked_now & m == 0
                    };
                    if dead(Card::new(r, s ^ 2)) || dead(Card::new(r, s ^ 3)) {
                        return true;
                    }
                }
            }
            let r = x.rank() + 1;
            let s = x.suit();
            let stacked_now = stacked_mask(ctx.root.stack);
            [Card::new(r, s ^ 2), Card::new(r, s ^ 3)].into_iter().all(|p| {
                let m = p.mask();
                ctx.root.vis & m == 0 && stacked_now & m == 0
            })
        }
    }
}

/// The adjacent-bit twin swap (`swap_suit` = index ^ 1): maps a mask to
/// the cards whose TWIN is in it — the dig-candidate spread.
const EVEN_MASK: u64 = 0x5555_5555_5555_5555;
fn twin_swap(m: u64) -> u64 {
    ((m & !EVEN_MASK) >> 1) | ((m & EVEN_MASK) << 1)
}

/// The sit-on spread: the cards that sit on P's cards — `go_after` says
/// x sits on y iff (x + 4) ^ y < 2 (the layout's rank-parity interleave
/// absorbed by the XOR form), so the sitters are P's bits shifted down 4
/// and twin-duplicated. The receiver/borrow/kill spreads.
fn sit_on_spread(p: u64) -> u64 {
    let d = p >> 4;
    d | twin_swap(d)
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
///
/// `fold` selects the search-facing goal set. The shipped fold
/// (`collapse_pick`) picks the *first* tableau-kind entry per commitment —
/// tableau-direct, then dig, then borrow, then tableau-bfs — and BFS
/// answers append after every fixed channel. So a tableau goal whose
/// commitment already has a dig/borrow outcome, and a stack goal whose
/// commitment already has any tableau outcome, can never be selected:
/// `fold` skips pushing exactly those. Provably the same successor per
/// commitment (gated by `fold_goal_cut_matches_total`); the materialized
/// path passes `false` and stays total for the differential.
fn core_run(
    ctx: &ClosureCtx,
    scratch: &mut DirectScratch,
    commitments: &mut Vec<Commitment>,
    fold: bool,
    deck: &Deck,
) {
    let mv = ctx.root.move_masks(ctx.deck_mask, ctx.first_layer);
    let deck_mask = ctx.deck_mask;
    let locked = ctx.root.locked;
    let locked_surfaces = ctx.root.vis & locked;

    // F3 mask, derived from the raw masks instead of the emitted groups:
    // a stack-direct entry exists exactly for the commitments whose card
    // sits in `pile_stack` (the locked surfaces — reveal-by-stacking) or
    // `deck_stack`, so `f3 = those ∩ dominance` needs no per-commitment
    // scan. Stored on the scratch for the search fold to read.
    let f3_bits = ((mv.pile_stack & locked_surfaces) | mv.deck_stack)
        & Stack::decode(ctx.root.stack).dominance_mask();
    scratch.f3 = f3_bits;

    // The guard battery, lifted to bulk masks — the engine's own
    // `gen_moves` idiom applied to the macro channels: every per-
    // commitment guard is a whole-mask set question, so the ~20
    // commitments' channel decisions (the "quiet 16" confirmations
    // included) read as bit tests against six masks computed once
    // per node (~25 mask ops total). Verified bit-exact against the
    // scalar guards on 36,927 commitments / 2,310 corpus states (probe
    // `debug_mask_lift`; the scalar `goal_dead` stays as the
    // falsifier's reference implementation).
    let stack_direct = (deck_mask & mv.deck_stack) | (locked_surfaces & mv.pile_stack);
    let tableau_direct = (deck_mask & mv.deck_pile) | (locked_surfaces & mv.reveal);
    let dig_cand = (deck_mask | locked_surfaces)
        & !KING_MASK
        & twin_swap(mv.pile_stack & !locked);
    let borrow_cand = {
        let mut ftop = 0u64;
        for s in 0..4u8 {
            let h0 = ctx.root.height(s);
            if h0 > 0 {
                ftop |= Card::new(h0 - 1, s).mask();
            }
        }
        (deck_mask | locked_surfaces)
            & !KING_MASK
            & sit_on_spread(ftop & !locked & mv.stack_pile)
    };
    // the kills: K1's climb-blocked mask (the open climb per suit is
    // `SUIT_PREFIX[s][frontier[s]+1]`), the tableau kill disjunction
    // (K4/K5 kings, K6's four-card ball, K2's dead receivers — kings
    // excluded from K2/K6: their phantom rank-13 receivers read dead,
    // but the scalar's king branch exits before those kills)
    let stacked_now = stacked_mask(ctx.root.stack);
    let commit_mask = deck_mask | locked_surfaces;
    let k1_dead = {
        let mut open = 0u64;
        for s in 0..4u8 {
            open |= SUIT_PREFIX[usize::from(s)][usize::from(ctx.frontier[usize::from(s)]) + 1];
        }
        commit_mask & !open
    };
    let tableau_dead = {
        let receiver_live = sit_on_spread(ctx.root.vis | stacked_now);
        let k2_dead = commit_mask & !KING_MASK & !receiver_live;
        let king_dead = if (ctx.root.vis & locked).count_ones() >= u32::from(N_PILES) {
            commit_mask & KING_MASK
        } else {
            locked_surfaces & KING_MASK & ctx.first_layer
        };
        let k6_dead =
            commit_mask & twin_swap(ctx.root.vis & !locked) & k1_dead & k2_dead;
        king_dead | k6_dead | k2_dead
    };

    // enumerate commitments: every locked surface first, then every
    // drawable deck card — reveal before draw, mirroring the old engine's
    // raw move order (`MoveMask::iter_moves` tries `Reveal` before any
    // deck move). Measured search order, not just aesthetics: draw-first
    // buries reveal-led winning lines under draw-subgame refutations
    // (seed 18 draw 1: 96k nodes draw-first vs 84 reveal-first, see
    // `macro_verdict_perf_probe`).
    //
    // The draw commitments enumerate by deck position DESCENDING (a
    // reverse pass over the array, filtered by the K+ mask): the
    // successor's offset after a draw is the drawn card's position, so
    // the last-drawn card determines a line's final offset — exploring
    // high positions first explores the permutations that END on low
    // positions (small offsets) first, i.e. the *dominating* states of
    // the offset-dominance classes first, so the refuted-offset
    // registry fires on arrival instead of after the fact. Mask-ascending
    // order is an uncorrelated coin flip per same-class pair (~half the
    // dominated explored before their dominators are refuted — the
    // measured 6.9% realized vs the 43.8% ceiling); ascending position
    // order is systematically the worst (dominated always first).
    commitments.clear();
    let mut bits = locked_surfaces;
    while bits != 0 {
        let bit = bits & bits.wrapping_neg();
        bits &= !bit;
        commitments.push(Commitment::Reveal(Card::from_mask_index(
            u8::try_from(bit.trailing_zeros()).unwrap(),
        )));
    }
    for c in deck.iter().rev() {
        if deck_mask & c.mask() != 0 {
            commitments.push(Commitment::Draw(c));
        }
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

        // stack outcome (the lifted mask)
        let stack_now = stack_direct & xmask != 0;
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

        // tableau outcome, direct channel (the lifted mask)
        let direct_now = tableau_direct & xmask != 0;
        if direct_now {
            groups[ci].push((
                commitment,
                OutcomeKind::Tableau,
                steps(&[direct_move]),
                "tableau-direct",
            ));
        }

        // the F3 fold for this commitment: dominantly stackable now with
        // a direct stack outcome — `collapse_pick` then takes that
        // stack-direct entry and no later channel of either kind is
        // reachable. Only meaningful in fold mode (the total generator
        // must keep emitting everything).
        let f3_sel = fold && f3_bits & xmask != 0;

        // stack-side channels. Prefix-raise: stack the missing same-suit
        // prefix cards until X becomes stackable. If the prefix is already
        // complete, the BFS fallback handles the "X needs an unrelated
        // shuffle to unblock" cases (e.g. a buried surface king).
        // The probe runs on a word copy: `locked` is shuffle-invariant and
        // the pile-stack mask recomputes from the words.
        //
        // (Moved after dig/borrow — the group's emission order between the
        // fixed Stack channel and the fixed Tableau channels is selection-
        // immaterial: `collapse_pick` takes the first Tableau entry or
        // `.first()`, and prefix-raise can only be `.first()` when no
        // Tableau channel fired at all. In fold mode the probe is skipped
        // entirely when any such entry exists or the commitment is
        // dominantly stackable now (f3): the outcome it would emit is then
        // unselectable.)
        let suit = x.suit();
        let is_king = x.rank() == crate::card::KING_RANK;

        // dig channel: vacate twin(X) onto a foundation if it is the
        // (uniquely possible) coverer of a parent top. Probed on a word
        // copy — one stack nibble edit and a mask recompute. The guard
        // is the lifted dig-candidate mask (twin unlocked & stackable).
        let mut dig_fired = false;
        if !is_king && dig_cand & xmask != 0 && !(fold && (direct_now || f3_sel)) {
            let twin = x.swap_suit();
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
                dig_fired = true;
            }
        }

        // borrow channel(s): a parent on its foundation top, worry-back-able.
        // Probed on a word copy, same shape as the dig. Gated by the
        // lifted borrow-candidate mask (some parent worry-backable); fold
        // mode skips the probe when an earlier Tableau entry (direct,
        // dig) already exists or f3 selects the stack-direct outcome.
        let mut borrow_fired = false;
        if !is_king
            && borrow_cand & xmask != 0
            && !(fold && (direct_now || dig_fired || f3_sel))
        {
            let r = x.rank();
            let s = x.suit();
            for p in [Card::new(r + 1, s ^ 2), Card::new(r + 1, s ^ 3)] {
                let on_foundation_top =
                    ctx.root.height(p.suit()) == p.rank().saturating_add(1);
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
                    borrow_fired = true;
                }
            }
        }

        let mut stack_produced = stack_now;
        if !stack_now
            && ctx.root.height(suit) < x.rank()
            && !(fold && (direct_now || dig_fired || borrow_fired))
        {
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

        // (the blockers of X are two twins and each may need its own dig;
        // the shared bounded BFS below catches the chains the fixed rules
        // don't name. Gate: only when no fixed channel produced a stack
        // outcome — running it after a successful prefix-raise would hunt
        // for the *second* stack scar class (the same-kind splits of
        // §6.7) but multiplies the per-node cost badly. The residual
        // under-emission is measured instead: the class-coverage metric in
        // macro_direct_matches_oracle.)
        //
        // fold mode: a stack-bfs answer can only be selected when the
        // commitment has no tableau outcome at all (collapse_pick takes
        // the first tableau entry, and every fixed tableau channel
        // precedes the BFS appends) — skip the goal otherwise.
        if !stack_produced
            && !stack_now
            && k1_dead & xmask == 0
            && !(fold && (direct_now || dig_fired || borrow_fired))
        {
            goals.push(AccommodationGoal {
                commitment,
                kind: OutcomeKind::Stack,
                xmask,
                commit_move: stack_move,
                cap: 40,
            });
        }

        // fallback channel: the shared bounded BFS below (catches the
        // chained borrow/dig crease; the differential reports how often
        // it fires)
        //
        // fold mode: with a dig/borrow outcome already in the group the
        // tableau-bfs answer appends after it and can never be picked
        // (collapse_pick takes the first tableau entry) — and under f3
        // the selection is the stack-direct entry outright — skip the
        // goal in both cases.
        if !direct_now
            && tableau_dead & xmask == 0
            && !(fold && (dig_fired || borrow_fired || f3_sel))
        {
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
    core_run(&ctx, scratch, &mut commitments, false, game.get_deck());
    scratch.commitments = commitments;
    (game, ctx)
}

/// The §6.4 rule list with full semantics, for the differential: every
/// channel's outcome materialized (per-channel dedup by encode), no fold.
/// Channels per commitment, in emission order: stack-direct,
/// tableau-direct; dig (vacate `twin(X)`), borrow (worry a foundation-top
/// parent back) on the tableau side; prefix-raise (stack the missing
/// same-suit prefix) on the stack side (the fixed Stack channel sits
/// after the fixed Tableau channels — selection-immaterial, see
/// `core_run`); and the bounded shared BFS for the
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
pub(crate) mod perf_probe;

#[cfg(test)]
mod tests;
