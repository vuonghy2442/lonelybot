# RankFront_licensed — report

File: `Temp/RankFront_licensed.lean` (compiles clean; no `sorry`, no `Classical`,
no `noncomputable`).

Build prerequisites (already built):

```
lake env lean -o .lake/build/lib/lean/Temp/RankFront_final.olean Temp/RankFront_final.lean
lake env lean Temp/RankFront_licensed.lean
```

## Axiom profile

`#print axioms` on every theorem is at the tail of the file.  Every declaration
comes out `[propext]` or `[propext, Quot.sound]`; nothing depends on
`Classical.choice`, `Classical.em`, or `sorryAx`.  Selected lines:

```
'OneColourClosure.RaiseSSeqL.toSeq'                          [propext]
'OneColourClosure.RaiseSSeqL.wf'                             [propext, Quot.sound]
'OneColourClosure.RaiseSSeqL.canRaiseS_persist_of_rank_ne'   [propext, Quot.sound]
'OneColourClosure.swap_of_licensed'                          [propext, Quot.sound]
'OneColourClosure.canRaiseS_inert_tabToFound_of_low_rank'    [propext, Quot.sound]
'OneColourClosure.canRaiseS_inert_of_canRaiseStep'           [propext, Quot.sound]
'OneColourClosure.unraise_probe_refutes'                     [propext, Quot.sound]
'OneColourClosure.canRaiseS_unraise_word'                    [propext, Quot.sound]
'OneColourClosure.canRaiseS_of_min_rank'                     [propext, Quot.sound]
'OneColourClosure.cover_must_be_raised'                      [propext, Quot.sound]
'OneColourClosure.cover_must_be_raised_L'                    [propext, Quot.sound]
'OneColourClosure.t2_rankfront_L'                            [propext]
'OneColourClosure.t6_rankfront_L'                            [propext]
```

## Job A — the licensed play relation

```lean
inductive RaiseSSeqL : State → List Card → State → Prop
  | nil (s) : RaiseSSeqL s [] s
  | cons : RaiseSSeqL s ws z → CargoPath z z₀ → CanRaise z₀ c →
           State.step z₀ (Move.tabToFound c) = some z' →
           RaiseSSeqL s (c :: ws) z'
```

Proved: `toSeq` (`RaiseSSeqL ⊆ RaiseSSeq`), `step_s`, `cargoPath`,
`canRaiseS_head`, `wf`, `append`, `drop_suffix`, R1
(`canRaiseS_persist_of_rank_ne`), and the **adequacy triple**:

* `toSeq` — every licensed play is a play;
* `canRaiseS_of_raiseSSeqL_head` — every licensed step's raised card is
  `CanRaiseS` at its origin;
* `raiseSSeqL_step_of_canRaiseS` — every `CanRaiseS` licence is realisable as one
  licensed step.

**Is `RaiseSSeqL` exactly the real raise plays?**  It is exactly the sub-relation
of `RaiseSSeq` in which every raise is a *reversible* (splice-then-raise) raise:
the three facts above say a `RaiseSSeqL` step and a `CanRaiseS` licence determine
each other.  It is **strictly smaller** than `RaiseSSeq`, which also admits
commit raises (`t4a_fires` + `t4a_not_canRaise` in `Temp/RankFront_proof.lean`).
In the full Klondike move graph, plays may contain commits, so `RaiseSSeqL` is the
reversible/`CanRaiseS` grade, not literally all plays; within that grade it is
exact, not a superset.

## Job B — census verdict at the licensed level

Model: `Temp/RankFront_licensed_census.py` (+ `RankFront_fast.py`,
`RankFront_canonical_test.py`).  A step is licensed iff the raised card is
`direct_can_raise` at a cargo mate (next-up + pile top + seat).  Commits and
hidden reveals are excluded.

Probe states T1–T6, all licensed plays of length ≤ 3:

| shape | valid / tested |
|---|---|
| rank-front `[c] ++ sortByRank (P.erase c)` | **91 / 91** |
| unsorted front `[c] ++ P.erase c` | 89 / 91 (both failures in T1, as before) |
| rank-sorted play `sortByRank P` | **91 / 91** |
| adjacent rank-swap in context | **9 / 9** |
| bubble-chain intermediate words | **9 / 9** |

Structured random sweep (no kings; valid descending runs, 7 anchors; plays ≤ 4):
about 8,000 rank-front tests over about 4,400 states — **0 failures**.
Kernel-checked `RaiseSSeqL` witnesses: `t2_rankfront_L` (3 steps), `t3_two_L`,
`t5_two_L`, `t5_two_L'`, `t6_rankfront_L` (3 steps).

Note the licensed level is genuinely smaller than the earlier census: `t3`'s third
card `10♦` and `t5`'s `J♣` are commit raises (a bare non-king top over an empty
hidden deck), so their long plays are in `RaiseSSeq` but not in `RaiseSSeqL`.
`t4`'s second step is the commit that reveals `10♥`, so `t4` has licensed plays
only of length 1.

**Verdict: no licensed-level counterexample to rank-front was found.**  The
licensed level is consistent with the general rank-front theorem; nothing here
shows it false.

## H1 — closed

`RaiseSSeqL` carries `CanRaise z₀ c` at the firing state, so the licence is a
first-class part of the play relation.  R1 is re-proved for it
(`RaiseSSeqL.canRaiseS_persist_of_rank_ne`).  H1 is closed.

## H2 — the un-raise transfer: `(P)` as stated is FALSE; the licensed version is TRUE

The parent's Route P proposed

```lean
theorem canRaiseS_unraise_of_rank_lt (z z' e d)
  (hz : z.WF) (hstep : RaiseStepS z z' e) (hr : d.rank < e.rank) :
  CanRaiseS z' d → CanRaiseS z d
```

**This is false with `RaiseStepS`** (the weak step).  Kernel-checked refutation
`unraise_probe_refutes`, state `urState`:

* `p0.hidden = [7♠]`, `p0.faceUp = [8♥]` (so `8♥` is the sole face-up card);
* `p1.faceUp = [8♦, 7♣, 6♦]` (`7♣` seated on `8♦`, `6♦` above it);
* foundations `♠` A..6, `♥` A..7, `♦` none, `♣` A..6.

The weak raise of `8♥` (rank 7) fires (next-up, pile top) but is **not** licensed
(`ur_not_canRaise`): `chop` is empty and the hidden deck is non-empty, so it is a
commit that reveals `7♠`.  The revealed `7♠` is `7♣.twin` and becomes a pile top,
which supplies the twin landing site for `7♣`.  Hence
`¬ CanRaiseS urState 7♣` (`ur_not_canRaiseS`) but
`CanRaiseS urAfter 7♣` (`ur_canRaiseS_after`), while
`7♣.rank (6) < 8♥.rank (7)`.  The parent's imagined refutation via *slides* is
impossible (`freeCardS` is cargo-invariant); the real obstruction is the
**hidden reveal of a commit raise**, and it is exactly why the licence is
load-bearing.

**The corrected statement is true.**

```lean
theorem canRaiseS_inert_tabToFound_of_low_rank (z z') (e d)
  (hz : z.WF) (hstep : State.step z (Move.tabToFound e) = some z')
  (hcr : CanRaise z e) (hr : d.rank.toIdx < e.rank.toIdx) :
  CanRaiseS z' d ↔ CanRaiseS z d
```

(one licensed raise, both directions), and at the step level

```lean
theorem canRaiseS_inert_of_canRaiseStep (z z₀ z') (e d)
  (hz : z.WF) (hpath : CargoPath z z₀) (hcr : CanRaise z₀ e)
  (hstep : State.step z₀ (Move.tabToFound e) = some z')
  (hr : d.rank.toIdx < e.rank.toIdx) :
  CanRaiseS z' d ↔ CanRaiseS z d
```

Proof: a licensed raise of `e` never reveals hidden cards, so the pile holding `d`
and the pile holding `d.twin` are untouched (`freeCardS` inert), and `nextUp d` is
untouched because a same-suit `e` with `e.rank > d.rank` makes `nextUp d` false on
both sides.

Consequences proved from it:

* `canRaiseS_unraise_word` — licences transfer backwards across a licensed word all
  of whose cards have strictly higher rank;
* `canRaiseS_of_prefix_rank_gt` — the least-rank raised card is licensed at the
  start of the play;
* `canRaiseS_of_min_rank` — the globally least-rank card of a licensed word is
  licensed at the start (stated on the first-occurrence split).

So Route P is **half closed**: the higher-rank transfer is done; what remains is
not a rank statement at all (see the residual).

## `swap_up`, corrected

Per the parent's correction, the sharp adjacent swap is licence-based, not
cover-based:

```lean
theorem swap_of_licensed (s u : State) (A : List Card) (d e : Card)
  (hpre : RaiseSSeqL s A.reverse u) (hu : u.WF)
  (hd : CanRaiseS u d) (he : CanRaiseS u e)
  (hr : d.rank.toIdx < e.rank.toIdx) :
  ∃ z', RaiseSSeqL s (e :: d :: A.reverse) z'
```

(`A · d · e` in chronological order.)  This is the form `t5_bare_swap_false`
forces: `havoid` is insufficient; the prefix-end licences are the correct
hypothesis.  It is proved by firing `d`, then `e` whose licence survives by R1
(`rank e ≠ rank d`).

## R3 — `CoverMustBeRaised`: closed

```lean
theorem cover_must_be_raised : CoverMustBeRaised
```

i.e. for a `RaiseSSeq` play from a `WF` state, if `x` is seated on `t` and `t.twin`
is founded, then `t ∈ ws → x ∈ ws`.  Also `cover_must_be_raised_L` for
`RaiseSSeqL`.

Proof shape (a genuine induction over the play, not a semantic argument):

* `seatOf_tabToFound_of_seated_ne` — a raise of a different card keeps a seated
  card's seat;
* `seatOf_cargoLeg_of_seated` / `seatOf_cargoPath_of_seated` — a cargo slide keeps
  a seated card's seat (the mover cannot be the seated card: its only possible
  bases are `t` and `t.twin`, and `t` is not a top while `t.twin` is founded);
* `seat_invariant_of_not_mem` — if `x` is not in the word, then at every prefix
  state `x` is still seated on `t` and `t.twin` is still founded;
* the step that raises `t` then contradicts `twin_covered_persists` (in the cargo
  class of the pre-state, `t` is never a pile top, so the step is `none`).

This closes the play-level R3 left open in `Temp/RankFront_final.lean`.

## The exact residual

With `(P)` and R1 both proved, the only missing input is the **sorted-prefix
bridge**: the sorted prefix is built at states that also differ from the original
play's prefix by *which slides were taken*.  `(P)` removes the higher-rank
difference and R1 adds the extra lower-rank raises, but neither identifies the
cargo/slide history.  The residual is stated as a Lean `Prop`:

```lean
def SortedPrefixLicence : Prop :=
  ∀ {s z u : State} {R P : List Card} {x : Card},
    s.WF →
    R.Pairwise (fun a b => a.rank.toIdx ≤ b.rank.toIdx) →   -- sorted prefix
    (∀ r ∈ R, r ∈ P) →
    (∀ p ∈ P, p.rank.toIdx < x.rank.toIdx → p ∈ R) →
    RaiseSSeqL s R.reverse u →                               -- sorted prefix played
    RaiseSSeqL s P.reverse z →                               -- original play
    x ∈ P →
    CanRaiseS u x
```

Proof obligations:

1. undo the missing higher-rank raises — **done** (`canRaiseS_inert_of_canRaiseStep`);
2. add the extra lower-rank raised cards — **done**
   (`RaiseSSeqL.canRaiseS_persist_of_rank_ne`);
3. the tie block, once both same-rank cards are tops — **available**
   (`twin_raise_square`, `Orig2/Fork/Local/ForkCriticalPair.lean:241`);
4. **open**: the cargo/slide identification between the sorted-prefix endpoint and
   the original prefix state after (1) and (2).  This is the residual and is *not*
   proved here.

## Bottom line

* H1: **closed** (`RaiseSSeqL`, adequacy, R1).
* H2: `(P)` as proposed with `RaiseStepS` is **false** — kernel-checked
  counterexample `unraise_probe_refutes`; the corrected licensed
  `(P)` is **true and proved**.  The sorted-replay induction is **still open**,
  reduced to the single `SortedPrefixLicence` bridge above.
* R3 (`CoverMustBeRaised`): **closed**.
* The general `raiseS_rankfront` statement is **still open**: not proved, and no
  licensed-level counterexample was found (91/91 probes, ~8,000 random tests).
  The earlier commit-raise successes (`t3`, `t5`, `t4`) do not transfer to
  `RaiseSSeqL`, so they are not evidence for the licensed theorem.
