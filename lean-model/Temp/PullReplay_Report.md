# `Temp/PullReplay` — the pull case by hoist-and-cancel; the block-end licence

Date: 2026-11-03.  Root `B:\code\lonelybot\lean-model`.
New files only (`Temp/PullReplay.lean`, `Temp/PullReplay_Counter.lean`,
`Temp/PullReplay_Report.md`, and the two `*_out.txt` logs); nothing under
`Orig2/` and no existing `Temp/*.lean` modified.

**Verdict.**  `block_end_licensed` is **closed in the non-twin case**
(`c.twin ∉ ws`) and the block-boundary dichotomy is closed unconditionally
(`block_end_licensed_or_dichotomy`).  The composition
`block_end_licensed` → (append `c`) → `raiseS_rankfront_L` → 
`cancel_prefix_is_play_from_source` is **closed** and gives the endpoint
licence and the rung statement `v + e_c`.  The only case that resists is
`c.twin ∈ ws` with `c` buried under a cover that is not a letter of the
word; the exact residual is `block_end_dead_dichotomy`'s `CoveredAt`
branch (Lean syntax below), and the unconditional twin version is
**kernel-refuted** (`Temp/PullReplay_Counter.lean`).  **The obstruction is
the twin, not a parked-on-`c` slide.**

`lake env lean Temp/PullReplay.lean` → `EXIT=0`; no `sorry`, no
`Classical`, no `noncomputable`, no `native_decide`.  The residual is
**kernel-refuted** in `Temp/PullReplay_Counter.lean` (also `EXIT=0`).

---

## 1. Axiom lines (verbatim)

`Temp/PullReplay.lean`:

```
'OneColourClosure.append_raise_of_live' depends on axioms: [propext]
'OneColourClosure.canRaiseS_persist_of_word_no_twin' depends on axioms: [propext, Quot.sound]
'OneColourClosure.countP_eq_zero_of_forall_not' depends on axioms: [propext]
'OneColourClosure.block_end_licensed' depends on axioms: [propext, Quot.sound]
'OneColourClosure.faceUp_mem_of_raiseSSeqLicensed' depends on axioms: [propext, Quot.sound]
'OneColourClosure.block_end_dead_dichotomy' depends on axioms: [propext, Quot.sound]
'OneColourClosure.block_end_licensed_or_dichotomy' depends on axioms: [propext, Quot.sound]
'OneColourClosure.pull_case_of_end_live' depends on axioms: [propext, Quot.sound]
'OneColourClosure.pull_case_sorted' depends on axioms: [propext, Quot.sound]
'OneColourClosure.pull_case_sorted_rungLe' depends on axioms: [propext, Quot.sound]
```

`Temp/PullReplay_Counter.lean`:

```
'PullReplayCounter.u_wf' depends on axioms: [propext]
'PullReplayCounter.play' depends on axioms: [propext, Quot.sound]
'PullReplayCounter.u_live_H5' depends on axioms: [propext, Quot.sound]
'PullReplayCounter.bnd_dead_H5' depends on axioms: [propext, Quot.sound]
'PullReplayCounter.block_end_licensed_twin_refuted' depends on axioms: [propext, Quot.sound]
```

---

## 2. The statement closed (the requested job)

```lean
theorem OneColourClosure.block_end_licensed
    {u bnd z : State} {c : Card} {low high : List Card}
    (hu : u.WF)
    (hlow : RaiseSSeqLicensed u (playWord low) bnd)
    (_hhigh : RaiseSSeqLicensed bnd (playWord high) z)
    (hc : CanRaiseS u c)
    (_hlowRank : ∀ d ∈ low, d.rank.toIdx ≤ c.rank.toIdx)
    (hlowNoSuit : ∀ d ∈ low, d.suit ≠ c.suit)
    (hlowNoTwin : c.twin ∉ low) :
    CanRaiseS bnd c
```

It is the whole-word persistence

```lean
theorem OneColourClosure.canRaiseS_persist_of_word_no_twin
    {u z : State} {ws : List Card} {c : Card}
    (h : RaiseSSeqLicensed u ws z) (hu : u.WF) (hc : CanRaiseS u c)
    (hnosuit : ∀ d ∈ ws, d.suit ≠ c.suit) (htwin : c.twin ∉ ws) :
    CanRaiseS z c
```

which is `canRaiseS_of_word_notMem` (`Temp/RaisesOrFork.lean`) with
`c ∉ ws` derived from `hnosuit c … rfl`.  Every letter is inert: rank
`≠ c.rank` by R1 (`canRaiseS_step_of_rank_ne`), rank `= c.rank` other than
`c`, `c.twin` by `SatDifferConfig.licence_lost_only_by_twin`, and `c` is
excluded by the suit hypothesis.  No rank-block bookkeeping is needed, so
`_hlowRank` is not consulted.

---

## 3. The composition (also closed)

```lean
theorem OneColourClosure.pull_case_of_end_live
    {s u v : State} {c : Card} {b : Base} {ws : List Card}
    (hs : s.WF) (hpull : State.step s (Move.foundToTab c b) = some u)
    (hρ : RaiseSSeqLicensed u ws v) (hno : ∀ d ∈ ws, d.suit ≠ c.suit)
    (hcz : CanRaiseS v c) :
    ∃ v', RaiseSSeqLicensed s (playWord (sortByRank ws)) v' ∧
      (∀ σ, σ ≠ c.suit → rungAt v' σ = rungAt v σ) ∧
      rungAt v' c.suit = rungAt u c.suit + 1
```

Route (exactly the parent's):

1. `append_raise_of_live` (`= exists_append_raise`) appends the final raise
   of `c`, giving the word `c :: ws`;
2. `raiseS_rankfront_L` hoists `c` to the first chronological raise, giving
   `rankFrontWord c (c :: ws) = playWord (c :: sortByRank ws)`;
3. `cancel_prefix_is_play_from_source` cancels the leading `raise c`
   against `pull c`, leaving the word `playWord (sortByRank ws)` from `s`;
4. rungs: `sortByRank ws ~ ws`, `s` and `u` differ by `-e_c`, and `ws` has
   no `c`-suit letter, so the endpoint is `v + e_c`.

The unconditional non-twin pull case is the corollary

```lean
theorem OneColourClosure.pull_case_sorted
    {s u v : State} {c : Card} {b : Base} {ws : List Card}
    (hs : s.WF) (hpull : State.step s (Move.foundToTab c b) = some u)
    (hρ : RaiseSSeqLicensed u ws v) (hno : ∀ d ∈ ws, d.suit ≠ c.suit)
    (htwin : c.twin ∉ ws) :
    ∃ v', RaiseSSeqLicensed s (playWord (sortByRank ws)) v' ∧
      (∀ σ, σ ≠ c.suit → rungAt v' σ = rungAt v σ) ∧
      rungAt v' c.suit = rungAt u c.suit + 1
```

Its endpoint licence is `block_end_licensed` (whole-word form).

The **rung-domination form** matching the parent's "≥ s, ≥ t" note is

```lean
theorem OneColourClosure.pull_case_sorted_rungLe
    {s u v t : State} {c : Card} {b : Base} {ws : List Card}
    (hs : s.WF) (hpull : State.step s (Move.foundToTab c b) = some u)
    (hρ : RaiseSSeqLicensed u ws v) (hno : ∀ d ∈ ws, d.suit ≠ c.suit)
    (htwin : c.twin ∉ ws) (ht : RungLe t v) :
    ∃ v', RaiseSSeqLicensed s (playWord (sortByRank ws)) v' ∧
      RungLe s v' ∧ RungLe t v'
```

`RungLe s v'` is `RungMono.rungAt_le`; `RungLe t v'` follows from
`RungLe t v` and the exact endpoint `v + e_c`.

---

## 4. Transport: none needed

**Confirmed: no new transport lemma is needed, and none was added.**  The
chain uses only `append_raise_of_live`, `raiseS_rankfront_L` and
`cancel_prefix_is_play_from_source`.  The state relation that would
otherwise have to be proved is

```
endpoint of the hoisted play's first (chronological) `[c]` letter  =  s
```

and it is **false in general** when that letter's `CargoPath` is nonempty
(the split endpoint `y` depends on the chosen slides, while `hstep` fixes
only the vanilla raise).  `cancel_prefix_is_play_from_source` bypasses it by
inserting the canonical empty-slide `[c]` letter and moving the tail with
the library's `RaiseSSeqLicensed.tail_transport`, which uses equal-rung
licence invariance (`canRaiseS_of_raise_perm`), not state equality.  So the
main proof obtains the tail without ever transporting `ws` across the pull.

---

## 5. The precise residual: the twin case

`block_end_licensed` is **false** without `c.twin ∉ ws`.  The
mechanism is `licence_lost_only_by_twin`: at equal rank the only card whose
raise can destroy `c`'s licence is `c` or `c.twin`.  Since `ws` is
`c.suit`-silent, `c` itself cannot occur, so only `c.twin` remains.  `c`
survives a raise of `c.twin` iff it is exposed (`run = []`); if it is buried
and `c.twin` topped the pile that kept it alive, the raise kills it.  The
cover of `c` may be a card of rank `c.rank - 1` that is *not* a letter of
`ws`, so it is never raised and `c` never re-emerges.

The unconditional dichotomy proved here is

```lean
theorem OneColourClosure.block_end_licensed_or_dichotomy
    {u bnd : State} {c : Card} {low : List Card}
    (hu : u.WF) (hlow : RaiseSSeqLicensed u (playWord low) bnd)
    (hc : CanRaiseS u c) (hnosuit : ∀ d ∈ low, d.suit ≠ c.suit) :
    CanRaiseS bnd c ∨ CoveredAt bnd c ∨
      ∃ a, bnd.pileHolding c = some a ∧ below c (bnd.piles a).faceUp = [] ∧
        ((bnd.piles a).hidden ≠ [] ∨ c.rank ≠ Rank.king)
```

and the dead-case refinement is

```lean
theorem OneColourClosure.block_end_dead_dichotomy
    {u bnd : State} {c : Card} {low : List Card}
    (hu : u.WF) (hlow : RaiseSSeqLicensed u (playWord low) bnd)
    (hc : CanRaiseS u c) (hnosuit : ∀ d ∈ low, d.suit ≠ c.suit)
    (hdead : ¬ CanRaiseS bnd c) :
    CoveredAt bnd c ∨
      ∃ a, bnd.pileHolding c = some a ∧ below c (bnd.piles a).faceUp = [] ∧
        ((bnd.piles a).hidden ≠ [] ∨ c.rank ≠ Rank.king)
```

(the first two clauses of `not_canRaiseS_cases` are discharged by
`faceUp_mem_of_raiseSSeqLicensed` and by `RungMono.rungAt_eq_of_no_letter`).

**The missing lemma (the exact residual), in Lean syntax — and it is FALSE:**

```lean
-- FALSE (kernel witness in Temp/PullReplay_Counter.lean).
theorem block_end_licensed_twin {u bnd : State} {c : Card} {low : List Card}
    (hu : u.WF) (hlow : RaiseSSeqLicensed u (playWord low) bnd)
    (hc : CanRaiseS u c) (hnosuit : ∀ d ∈ low, d.suit ≠ c.suit) :
    CanRaiseS bnd c
```

The kernel refutation is

```lean
theorem PullReplayCounter.block_end_licensed_twin_refuted :
    ∃ (u bnd : State) (c : Card) (low : List Card),
      u.WF ∧ RaiseSSeqLicensed u (playWord low) bnd ∧
        CanRaiseS u c ∧ (∀ d ∈ low, d.suit ≠ c.suit) ∧ ¬ CanRaiseS bnd c
```

with the board

```
found ♥ = A..4,  found ♦ = A..4,  found ♠ = found ♣ = []
p0 = ⟨[], [6♣, 5♥, 4♠]⟩      -- 5♥ buried under 4♠, company 6♣ below
p1 = ⟨[], [6♠, 5♦]⟩          -- 5♦ = (5♥).twin tops p1, company 6♠ below
rest in the stock
c = 5♥,  low = [5♦]
```

`CanRaiseS u 5♥` holds by the buried/twin-top disjunct; `raise 5♦` is the
one-letter play; at the landing `5♦` is on the foundation, so `5♥` (still
buried under `4♠`) is dead: `4♠`'s only card seats are `5♥`, `5♦`
(`cover_seats`) and it cannot go to an empty pile.  The cover `4♠` is not a
letter of `ws`, so it is never raised.

The covering shape is therefore

```
c buried under y  (y.rank.toIdx = c.rank.toIdx - 1),  y ∉ ws,
c.twin ∈ ws,   below c ≠ [],   run above c ≠ [],
CanRaiseS u c  via the twin-top disjunct  pileOfTop c.twin ≠ none,
raise c.twin in the low block
⟹ ¬ CanRaiseS (block end) c     -- and CoveredAt (block end) c (the cover y)
```

Closing it requires one of:

* raising the cover `y` too, at *its* own (strictly lower) rank boundary —
  an extra letter, so the resulting word is larger than `playWord (sortByRank ws)`;
* or the fork branch of `raises_or_fork`.

One sentence: **the obstruction is the twin (`c.twin` raised while `c` is
buried under a cover that is not in `ws`), not a parked-on-`c` slide** —
the hoist-and-cancel route never transports slides, and the parked-on-`c`
case that worried the earlier plan is rank/colour-forced to expose
`c.twin` itself, so it folds into the same twin obstruction.

---

## 6. Notes on the sibling pieces

* `RaiseSSeqLicensed.split_head` (`Orig2/Fork/Class/ForkRaiseReorderProof.lean:229`)
  already provides the snoc split from the previous plan; it was not
  reproved.
* `insert_at_block_end` / `insert_at_block_end_split` /
  `cancel_prefix_is_play_from_source` (`Temp/BlockHousing.lean`) are used as
  supplied; `cancel_prefix_is_play_from_source` is the only place the
  internal `tail_transport` is invoked.
* Prerequisite oleans built before this card:
  `Temp/BlockHousing.olean` (then `Temp.RaisesOrFork`, `Temp.PullRaiseId`,
  `Temp.RungMono`, `Temp.SpecShift_sem` were already present).

## 7. Reproduce

```
cd B:\code\lonelybot\lean-model
lake env lean -o .lake/build/lib/lean/Temp/BlockHousing.olean Temp/BlockHousing.lean
lake env lean -o .lake/build/lib/lean/Temp/PullReplay.olean Temp/PullReplay.lean
lake env lean Temp/PullReplay.lean          # EXIT=0
lake env lean Temp/PullReplay_Counter.lean  # EXIT=0 (kernel refutation)
```
