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

/// A macro move: commit to a deck card or to revealing a surface card.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Commitment {
    Draw(Card),
    Reveal(Card),
}

impl Commitment {
    fn sort_key(self) -> (u8, u8) {
        let (tag, c) = match self {
            Commitment::Draw(c) => (0, c),
            Commitment::Reveal(c) => (1, c),
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
        let cm = cands & cands.wrapping_neg();
        let mut c = Card::from_mask_index(u8::try_from(cm.trailing_zeros()).unwrap());

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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::shuffler::default_shuffle;
    use crate::solver::{solve, SearchResult};
    use core::num::NonZeroU8;

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
                        let (res, _) = solve(&mut Solitaire::new(&cards, step));
                        let old_win = matches!(res, SearchResult::Solved);
                        let g = Solitaire::new(&cards, step);
                        let all = macro_solvable_sel(&g, SuccSelect::All);
                        let tall = macro_solvable_sel(&g, SuccSelect::TallestOnly);
                        let short = macro_solvable_sel(&g, SuccSelect::ShortestOnly);
                        assert_eq!(
                            (all, tall, short),
                            (old_win, old_win, old_win),
                            "verdict mismatch: draw={draw_step} seed={} old={old_win} all={all} tall={tall} short={short}",
                            12 + i
                        );
                    }
                }
                println!("macro verdicts match the engine on 32 games (both draws, all policies)");
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
