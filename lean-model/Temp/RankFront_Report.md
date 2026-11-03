# RankFront probe — answers to Q1/Q2/Q3

File: `Temp/RankFront_probe.lean` (imports `Temp.Reorder_front_proof` and
`Orig2.Fork.Class.ForkOneColourClosure`).  Compiles: **yes**
(`lake env lean Temp\RankFront_probe.lean`), no `sorry`, no `Classical`.

Build prerequisites (once each):
```
lake env lean -o .lake/build/lib/lean/Temp/SpecShift_sem.olean Temp/SpecShift_sem.lean
lake env lean -o .lake/build/lib/lean/Temp/Reorder_front_proof.olean Temp/Reorder_front_proof.lean
```

## Q1 — the parent's composition **is legal** on this probe

```lean
theorem probe_rankfront_exists : ∃ z', RaiseSSeq probeState [cKD, cQS, cKH] z'
-- [propext]
```

Word `[K♦, Q♠, K♥]` = chronological **K♥, then Q♠, then K♦** = the parent's
`P' = [K♥, Q♠, K♦]`.  All three raises fire with the trivial cargo path:

| step | card | why it fires |
|---|---|---|
| 1 | `K♥` | bare king, top of `p0`, `nextUp` (♥ rung 12) |
| 2 | `Q♠` | **top of `p1`** (`K♦` beneath), `nextUp` (♠ rung 11) |
| 3 | `K♦` | exposed by step 2; bare king on `p1`, `nextUp` (♦ rung 12) |

The predicted obstruction ("after `K♥` is founded, `Q♠` has no seat") **does not
apply to this word**: `Q♠` does not have to *move*, it is *raised* in step 2 —
and it is the pile top, so raising it needs no seat.  The obstruction applies
to the *other* word `[Q♠, K♦, K♥]` (chronological `K♥`, `K♦`, `Q♠`), where
`K♦` is the card that must be raised while `Q♠` still covers it; that is the
word refuted in `Temp/Reorder_front_proof.lean`
(`probe_not_raiseSeq_front`).  So the probe does **not** refute "rank-sort the
play, then move `c` to the front".

## Q2 — fork status of `probeState`

Kernel-checked (with `ForkWitness` = the ↔ reading of
`Orig2/Substrate/Vocab.lean:592`, i.e. spectrum *exactly* `{x, x.twin}`):

```lean
theorem probe_three_live :
    CanRaiseS probeState cKH ∧ CanRaiseS probeState cKD ∧ CanRaiseS probeState cQS
-- [propext, Quot.sound]   (three distinct live cards)

theorem probe_not_forkWitness (x : Card) : ¬ ForkWitness probeState x
-- [propext]               (spectrum ⊇ {K♥,Q♠} kills every candidate pair)

theorem probe_not_forkState : ¬ forkState probeState
-- [propext]

theorem probe_forkLive : ∃ x c, (c = x ∨ c = x.twin) ∧ CanRaiseS probeState c
-- [propext, Quot.sound]
```

The spectrum at the probe is `{K♥, K♦, Q♠}` (three cards: `Q♠` is live because
it is the pile top of `p1`; `K♦` is live via the slide `Q♠ : K♦ → K♥`).  A twin
pair has two elements, so no `x` works — the probe state itself is **not** a
fork.

**Not settled (stated explicitly in the file):** the class-level alternative
`Fork probeState` / `Forkless probeState`.  `Forkless` quantifies over every
orbit mate at *any* rungs (`sameOrbitSetoid` does not fix the ledger), so it
needs the state-space invariant

    (Ih) all piles have hidden = [];   (I2) face-up ⊆ {K♥,K♦,Q♠};
    (I3) rungs ♠∈{11,12}, ♥∈{12,13}, ♦∈{12,13}, ♣=0,

carried along witness shuffles (draw: no tableau change; slide: the face-up set
is preserved; raise: `foundTop_rank_succ` + `nextUp` keep the rung in range;
pull: `foundTop_rank_succ` + `canPlace` + (I2) leave only `Q♠,K♥,K♦` as
pullable tops — `J♠` needs a red-queen top, `Q♥,Q♦` need a black-king top,
`Q♣,K♠,K♣` never leave the stock).  Under (Ih)–(I3) no class mate is a fork:
live ⟹ held ⟹ in `{K♥,K♦,Q♠}`; the only twin pair there is `{K♥,K♦}`; and the
pin fails since the uncovered king is a bare king with `hidden = []`
(vanilla-raisable) while the covered one can only be covered by `Q♠`, which is
then itself live and breaks "spectrum = pair".  **I did not machine-check
(Ih)–(I3)**, so neither `probe_fork` nor `probe_forkless` is claimed.  My
analysis says the class is forkless.

## Q2-side consequence that *is* kernel-checked, and it matters

```lean
theorem gated_front_statement_false :
    ¬ (∀ {s : State} {c : Card}, s.WF → ¬ forkState s → CanRaiseS s c →
        ∀ {ws : List Card} {z : State}, RaiseSSeq s ws z → c ∈ ws →
          ∃ z', RaiseSSeq s (ws.erase c ++ [c]) z')
-- [propext, Quot.sound]
```

`probeState` is not a fork state, yet it refutes the front-reordering word.  So
gating the statement by the *state-level* hypothesis `¬ forkState s` does not
repair it.

## Q3

Conditional on `Forkless probeState`, which I did not close, so I do not claim
the probe is forkless and I do not run the second forkless state.  What is
settled regardless: the **state-level** gate is dead (§ above), and the
rank-sort-then-front composition is *not* refuted by this probe (Q1).

## One sentence for the parent

The rank-sort-then-front composition survives this probe (it is legal here);
the earlier refutations were of the *unsorted*-tail words, and the only gate
this probe kills is the state-level `¬ forkState` one — the class-level
`¬ Fork` gate remains untested because the class-level invariant was not
formalized.
