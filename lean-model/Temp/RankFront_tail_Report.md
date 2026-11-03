# RankFront_tail — `TailExists` **proved**, hence `raiseS_rankfront_L`

File: `Temp/RankFront_tail.lean` (new file; no earlier `Temp` file and nothing
under `Orig2/` was modified).
Report: this file.

Build (from `lean-model`):

```
lake env lean Temp/RankFront_tail.lean
```

Clean: no `sorry`, no `Classical`, no `noncomputable`, no `native_decide`, no
warnings, no errors.  Axiom battery at the tail of the file: every declaration is
`[propext]` or `[propext, Quot.sound]`; **nothing** depends on `Classical.choice`.

## Headline

```lean
theorem tail_exists : TailExists
theorem raiseS_rankfront_L {s z : State} {c : Card} {ws : List Card}
    (hs : s.WF) (hc : CanRaiseS s c) (hplay : RaiseSSeqL s ws z) (hmem : c ∈ ws) :
    ∃ z', RaiseSSeqL s (rankFront c ws) z'
```

Both are unconditional (`TailExists` had no hypotheses left) and kernel-checked:

```
'OneColourClosure.tail_exists'       depends on axioms: [propext, Quot.sound]
'OneColourClosure.raiseS_rankfront_L' depends on axioms: [propext, Quot.sound]
```

The general rank-front theorem **at the licensed grade is now proved**: from any
`WF` state, any `CanRaiseS` card `c`, and any licensed play whose word contains
`c`, the rank-front word `(sortRank (ws.erase c)).reverse ++ [c]` is realisable.

## Why I did not use the proposed decomposition

The parent's step 1 compares the endpoint of `[c] · R` with the interior state
of the original play at which `x` is raised.  Those two states are not endpoints
of two plays of the *same* multiset from a common start, so `(S)`
(`canRaiseS_of_raise_perm`) cannot compare them — that step is an actual gap, not
a presentation issue.  I did not patch it; I changed the route.

## The route that works

Everything rests on the **flat characterization** of the licence
(`canRaiseS_iff`, `Orig2/Substrate/CargoRaise.lean:706`), which is a local read
of the current piles (no existential cargo path):

> `CanRaiseS st c` iff `nextUp c` and `c` sits in a pile as `bs ++ c :: run`
> with (`bs ≠ []` or bare king) and (`run = []` or `c.twin` tops some pile).

Consequences proved in §1:

* `freeCardS_unpack` / `freeCardS_of_data`: the exact data of `freeCardS`.
* **same rank, non-twin**: the licence transfers **both ways** across a licensed
  raise (`canRaiseS_tabToFound_iff_of_rank_eq_notTwin`, step form
  `canRaiseS_rankEq_notTwin_step_iff`), because the raised card's pile neither
  holds `c` nor `c.twin` and a licensed raise never reveals.
* **same rank, twin**: the licence transfers **backwards unconditionally**
  (`canRaiseS_tabToFound_bwd_of_twin`); forwards only if `c` is exposed
  (`freeCardS_tabToFound_fwd_of_twin`).
* `canRaise_of_canRaiseS_of_exposed`: exposed + S-licensed ⇒ vanilla licensed
  (this is what lets `twin_raise_square` be applied later).
* `canRaise_of_raise_sameRank`: a *vanilla* licence survives a vanilla raise of a
  different card of the same rank.

Then (§2–§4):

* `tie_swap`: an **adjacent equal-rank transposition inside a licensed play**,
  with the tail replayed.  Non-twin case: the flat transfer both ways + `(S)`.
  **Twin case (the hard one):** un-raise the twin to the *vanilla* witness `z₀`
  of the first card's step; the existence of the play (specifically, the second
  card's licence at the landing) forces the tracked twin to be exposed at `z₀`
  (`exposed_bwd_of_twin_step`), hence both raises are vanilla at `z₀` and
  `twin_raise_square` commutes them *exactly*.
* `asc_swap`: passing a strictly lower-rank card, using
  `canRaiseS_inert_of_canRaiseStep` (proved earlier).
* `bubble_tie` / `bubble_front`: in an ascending play, the front card `c` can be
  moved to the very front of a prefix whose ranks are `≤ c.rank`; the equal-rank
  part uses `tie_swap` (no licence needed), the strictly-lower part uses
  `asc_swap` with `c`'s licence kept by R1.

For the tie **order** (§5–§7):

* `Asc`, `asc_erase`, `asc_erase_append`, `asc_append_left`;
* `insRank_perm`, `insRank_asc`, `sortRank_perm`, `sortRank_asc`, `reverse_perm`;
* `perm_erase`: a **constructive** replacement for `List.Perm.erase` (the core
  lemma is `Classical.choice`-tainted and would have broken the axiom budget);
* `tieFree`: any two ascending orders of the same multiset are interchangeable
  as licensed plays (induction on length: bubble the target head to the front
  with `bubble_tie`, split it off, recurse).

Assembly (§8): sort the given play (`sortable`), split at `c`, bubble `c` to the
front, split off `c`, then `tieFree` converts the resulting ascending tail into
`sortRank (ws.erase c)`.

## The parent's probe, and step 2

The probe `p0 = [7♣,6♦]`, `p1 = [7♠,6♥,5♠]`, rungs `(3,5,5,0)` is **not** a
counterexample to the route above.  In it, `6♦` is exposed (`run = []`) while
`6♥` is not (`run = [5♠]`); each is licensed only via the *other* topping a pile,
so after one raise the other has neither `run = []` nor a twin-top.  This is
exactly the state-level tie step being false.  The proof never uses a state-level
tie step: it uses `tie_swap`, whose hypothesis is the *play* `a then c`.  In the
twin case that play forces exposure (as above), and in the non-twin case no
exposure is needed because the flat transfer is an iff.

What I could **not** do is the parent's step 1, for the reason in the section
above; the decomposition delivered in its place is the one above.

## Probes (independent of the kernel proof)

New probe scripts (no earlier file modified):

* `Temp/RankFront_tail_probe.py` — the **exact** `TailExists` statement, with the
  *reverse-chronological* tie order that the Lean `sortRank (ws.erase c)` really
  produces.  1 876 instances on T1–T6 (plays ≤ 4) plus random states: **0
  violations**.
* `Temp/RankFront_tie_probe.py`, `Temp/RankFront_tie_search.py` — adjacent
  equal-rank transposition, full equal-rank block permutations, and the exact
  tail statement: 13 296 states / 173 025 licensed plays, **0 violations**.

So the mathematical content is not a lucky Lean accident: the exact statement
(including the tie order) was model-checked, and the proof matches.

## Axiom lines (selected)

```
'OneColourClosure.tie_swap'                  [propext, Quot.sound]
'OneColourClosure.bubble_front'              [propext, Quot.sound]
'OneColourClosure.tieFree'                   [propext, Quot.sound]
'OneColourClosure.tail_exists'               [propext, Quot.sound]
'OneColourClosure.raiseS_rankfront_L'        [propext, Quot.sound]
```

Full battery: the 45 `#print axioms` lines at the end of `Temp/RankFront_tail.lean`.

## Status of the general rank-front theorem (blunt)

The **licensed** rank-front theorem (`RaiseSSeqL`, every raise reversible /
`CanRaiseS`) is **proved** in full, unconditional and axiom-clean; `TailExists`
is closed, not reduced.  The weak-step (`RaiseSSeq`) version remains false as
stated, for the reason already recorded earlier in this lane (`t4a_fires` vs
`t4a_not_canRaise`): a commit raise is not reversible, so the sorted replay need
not exist.
