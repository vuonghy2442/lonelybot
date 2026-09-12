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

/// Canonicalize to the safe-sweep fixed point: apply the forced
/// safe-stack rule (5.1 / F3 — the lowest dominantly-stackable movable
/// card) repeatedly. Cards that are *locked* are excluded: stacking one is
/// a reveal, which is a commitment in its own right, not an accommodation.
///
/// Unconditional for measurement purposes only: whether the sweep is the
/// right normal form (open item O6) is exactly what the multiplicity
/// counts this scaffolding produces are meant to inform.
fn canonicalize(g: &mut Solitaire) {
    loop {
        let moves = g.gen_moves::<true>();
        let vec = moves.to_vec::<N_MOVES_MAX>();
        // The forced branch returns exactly one PileStack; anything else
        // stops the sweep.
        let [Move::PileStack(c)] = vec[..] else {
            break;
        };
        // Never reveal inside an accommodation.
        if g.reverse_move(Move::PileStack(c)).is_none() {
            break;
        }
        let (_, (undo, _)) = g.do_move(Move::PileStack(c));
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

/// Is `g` winnable in the commitment game? Plain DFS over canonical
/// (safe-swept) states with insert-once dedup. Deliberately naive: this is
/// the semantics checker for the rework, not the speed version.
#[must_use]
pub fn macro_solvable(g: &Solitaire) -> bool {
    fn rec(g: &Solitaire, tp: &mut TpTable) -> bool {
        let mut s = g.clone();
        canonicalize(&mut s);
        if s.is_win() || !tp.insert(s.encode()) {
            return s.is_win();
        }
        enumerate_transitions(&s)
            .iter()
            .any(|(_, succ)| rec(succ, tp))
    }
    let _ = g;
    rec(g, &mut TpTable::default())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::shuffler::default_shuffle;
    use core::num::NonZeroU8;

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

    fn macro_scaffold_smoke_inner() {
        let mut histogram = [0usize; 6];
        let mut macro_classes = 0usize;
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
                        // by the reversible closure, at most 2 classes remain
                        for encs in [&c.outcomes.canon_tableau, &c.outcomes.canon_stack] {
                            if encs.len() > 2 {
                                let k = closure_classes(encs);
                                macro_classes = macro_classes.max(k);
                                assert!(
                                    k <= 2,
                                    "commitment {:?} has {k} distinct post-state closure classes \
                                     (C2 violation): draw={draw_step} seed={} encodes={:?}",
                                    c.commitment,
                                    12 + i,
                                    encs.iter().map(|(e, _)| *e).collect::<Vec<_>>()
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
        println!("max distinct post-state closure classes per commitment: {macro_classes} (C2 claim: <= 2)");
    }
}
