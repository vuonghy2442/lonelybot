import Orig2.Fork.Class.ForkRaiseReorderProof
import Temp.SatDiffer_config
import Temp.Fork_producer
import Temp.RungMono
import Temp.PullRaiseId
import Temp.Obstruction
import Temp.FrozenSuit

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

/-!
# Temp/RaisesOrFork - the raise-or-fork route, split at the branches

Scratch card (`Temp/`), READ-ONLY on `Orig2/`; nothing committed.

The target (stated exactly in `Temp/RaisesOrFork_Report.md`):

```lean
theorem raises_or_fork {s t : State} (hs : s.WF) (h : sameOrbitSetoid.r s t) :
    (∃ ws v, RaiseSSeqLicensed s ws v ∧ RungLe s v ∧ RungLe t v) ∨ Fork s
```

This file contains **no `sorry`** and does not state the target: it closes the
two branches that can be closed with the current library, plus the assembly
that shows the target implies `FullJoinAtLeastOrFork` with **no residue**.

## 1. The pull branch, easy case (the plan's "insert a raise" step)

`RaiseSSeqLicensed` words are in **reverse play order** (the head is the last
raise, `ForkRaiseReorder.lean`), so `c :: ws` is the play `ws` followed by a
raise of `c`.  Appending a raise of `c` at the *end* of a licensed play is legal
as soon as `c` is still `CanRaiseS` at the endpoint.  That licence survives a
word which raises neither `c` nor `c.twin`:

* a letter of rank `≠ c.rank` is licence-inert (`canRaiseS_step_of_rank_ne`, R1);
* a letter of rank `= c.rank` other than `c`, `c.twin` is inert
  (`SatDifferConfig.licence_lost_only_by_twin`).

`exists_append_raise_of_word_notMem` below is the exact statement.  NOTE: the
plan's additional inference "hence, by `pull c ; raise c = id`, a raiseS play
**from `s`**" does **not** follow from these lemmas - see the report; the
endpoint here is a play from the *pull's landing*, not from the pull's source.

## 2. The fork branch

`ForkWitness st x` is *spectrum equality* `(∀ c, CanRaiseS st c ↔ c = x ∨ c =
x.twin)` plus the vanilla block `¬ CanRaise st x.twin`.  A drain that collapses
the spectrum to a twin pair therefore gives `Fork st` outright, with no
invariant and no rank floor (`fork_of_collapsed_spectrum`).

## 3. The route implies the join

`fullJoinAtLeastOrFork_of_raises_or_fork`: the target - as a hypothesis, so no
new predicate is introduced - yields `FullJoinAtLeastOrFork` with `w := v`.

House rules: no `sorry`, no `Classical`, no `noncomputable`, no `native_decide`.
-/

namespace OneColourClosure

/-! ## 1. Licence persistence through a word that avoids `c` and `c.twin` -/

/-- **Licence persistence (word form).**  If `c` is `S`-live at `s` and a
licensed play raises neither `c` nor `c.twin`, then `c` is still `S`-live at the
endpoint.  This is the "`c` stays raisable throughout" half of the pull branch.

The two inertness rows are R1 (`canRaiseS_step_of_rank_ne`) for a letter of a
different rank, and `SatDifferConfig.licence_lost_only_by_twin` for a letter of
the *same* rank other than `c`/`c.twin`. -/
theorem canRaiseS_of_word_notMem {s z : State} {ws : List Card} {c : Card}
    (h : RaiseSSeqLicensed s ws z) (hwf : s.WF) (hc : CanRaiseS s c)
    (hself : c ∉ ws) (htwin : c.twin ∉ ws) :
    CanRaiseS z c := by
  revert hwf hc hself htwin
  induction h with
  | nil =>
      intro _ hc _ _
      exact hc
  | cons htail hS hp hstep ih =>
      rename_i z z0 z' cc wws
      intro hwf hc hself htwin
      have hzwf : z.WF := htail.wf hwf
      have hcself : c ∉ wws := fun hm => hself (List.mem_cons_of_mem _ hm)
      have hctwin : c.twin ∉ wws := fun hm => htwin (List.mem_cons_of_mem _ hm)
      have hc_z : CanRaiseS z c := ih hwf hc hcself hctwin
      have hne_self : cc ≠ c := by
        intro hh
        exact hself (hh ▸ List.mem_cons_self)
      have hne_twin : cc ≠ c.twin := by
        intro hh
        exact htwin (hh ▸ List.mem_cons_self)
      by_cases hrank : cc.rank = c.rank
      · exact SatDifferConfig.licence_lost_only_by_twin hzwf ⟨z0, hp, hstep⟩
          hrank hne_self hne_twin hc_z
      · exact canRaiseS_step_of_rank_ne hzwf ⟨z0, hp, hstep⟩ hrank hc_z

/-- **Appending one licensed raise.**  A `CanRaiseS` card at the endpoint of a
licensed play can be raised as the next (last) letter. -/
theorem exists_append_raise {s z : State} {ws : List Card} {c : Card}
    (h : RaiseSSeqLicensed s ws z) (hc : CanRaiseS z c) :
    ∃ z', RaiseSSeqLicensed s (c :: ws) z' := by
  have hc' : CanRaiseS z c := hc
  obtain ⟨z0, hp, hcan⟩ := hc
  obtain ⟨z', hs⟩ := step_tabToFound_of_canRaise hcan
  exact ⟨z', RaiseSSeqLicensed.cons h hc' hp hs⟩

/-- **THE EASY (NON-TWIN) PULL BRANCH, closed.**  If a licensed play from `s`
raises neither `c` nor `c.twin`, and `c` is `S`-live at `s`, then the word
`c :: ws` (play `ws`, then raise `c`) is licensed, its endpoint dominates the
old endpoint rungwise, and `c`'s suit climbed by exactly one. -/
theorem exists_append_raise_of_word_notMem {s z : State} {ws : List Card}
    {c : Card} (h : RaiseSSeqLicensed s ws z) (hwf : s.WF) (hc : CanRaiseS s c)
    (hself : c ∉ ws) (htwin : c.twin ∉ ws) :
    ∃ z', RaiseSSeqLicensed s (c :: ws) z' ∧ RungLe z z' ∧
      rungAt z' c.suit = rungAt z c.suit + 1 := by
  have hc_z : CanRaiseS z c := canRaiseS_of_word_notMem h hwf hc hself htwin
  have hc_z' : CanRaiseS z c := hc_z
  obtain ⟨z0, hp, hcan⟩ := hc_z
  obtain ⟨z', hs⟩ := step_tabToFound_of_canRaise hcan
  refine ⟨z', RaiseSSeqLicensed.cons h hc_z' hp hs, ?_, ?_⟩
  · intro σ
    rw [rungAt_tabToFound hs σ, rungAt_cargoPath hp σ]
    split <;> omega
  · rw [rungAt_tabToFound hs c.suit, rungAt_cargoPath hp c.suit, ite_eq_left rfl]

/-! ## 1b. Rungs climb along a licensed raiseS play

The pointwise monotone row and the guarded no-letter row are `Temp/RungMono.lean`
(`RungMono.rungAt_le`, `RungMono.rungAt_le_of_raiseSSeqLicensed`); they are not
reproved here.  The `RungLe`-shaped corollary below is the form the target's
join branch consumes. -/

/-- The `RungLe` form: `RungLe s v` is **automatic** for any raiseS play from
`s`.  So in the target's join branch the conjunct `RungLe s v` costs nothing,
and the only content is `RungLe t v`. -/
theorem rungLe_of_raiseSSeqLicensed {s z : State} {ws : List Card}
    (h : RaiseSSeqLicensed s ws z) : RungLe s z :=
  fun σ => RungMono.rungAt_le h σ

/-! ## 1c. The both-vanilla twin square (the plan's tie case, packaged) -/

/-- **Both orders fire when both twins are vanilla-raisable.**  If `c` and
`c.twin` are both `CanRaise` at a `WF` state, raising them in either order is
legal and the two two-letter plays share their landing state
(`twin_raise_square`, `Orig2/Fork/Local/ForkCriticalPair.lean:241`).

This is the state-level input the tie case needs; it does not by itself say how
to insert `c` into an existing play. -/
theorem twin_raise_square_both {z : State} {c : Card} (hz : z.WF)
    (hc : CanRaise z c) (hct : CanRaise z c.twin) :
    ∃ zt zc z2,
      State.step z (Move.tabToFound c.twin) = some zt ∧
      State.step zt (Move.tabToFound c) = some z2 ∧
      State.step z (Move.tabToFound c) = some zc ∧
      State.step zc (Move.tabToFound c.twin) = some z2 := by
  obtain ⟨zt, ht⟩ := step_tabToFound_of_canRaise hct
  obtain ⟨zc, hc'⟩ := step_tabToFound_of_canRaise hc
  have hsu : c.twin.suit ≠ c.suit := Suit.twin_ne c.suit
  obtain ⟨w, hw1, hw2⟩ := twin_raise_square (u := z) (v := zt) (u' := zc)
    (c := c.twin) (d := c) hz hsu ht hc'
  exact ⟨zt, zc, w, ht, hw1, hc', hw2⟩

/-! ## 2. The obstruction at a deficit point: buried cover, or frozen suit

This is the shape the refined plan's "cover/nextUp descent" starts from, built
on the sibling card `Temp/Obstruction.lean` (`not_canRaiseS_cases`) and
`Temp/FrozenSuit.lean` (`commitLocked_rung_le`).  At a point where `c` is
next-up (`z.nextUp c = true`, i.e. the rung of `c`'s suit is exactly `c.rank`)
and `c` is a tableau card, the four-way obstruction collapses to two:

* `c` is **buried** under a nonempty run and its twin tops no pile (so the
  only way up is a cover); or
* `c` is a **lone face-up card** at the bottom of its run and either the pile
  has a hidden deck (commit lock, suit frozen) or `c` is not a king.

The first two disjuncts of `not_canRaiseS_cases` (`nextUp = false`,
`pileHolding = none`) are exactly what the deficit data excludes. -/
theorem obstruction_at_deficit {z : State} (hz : z.WF) {c : Card}
    (hnext : z.nextUp c = true) {a : Anchor} (hhold : z.pileHolding c = some a)
    (h : ¬ CanRaiseS z c) :
    (∃ bs run, (z.piles a).faceUp = bs ++ c :: run ∧ run ≠ [] ∧
        z.pileOfTop c.twin = none)
      ∨ (below c (z.piles a).faceUp = [] ∧
          ((z.piles a).hidden ≠ [] ∨ c.rank ≠ Rank.king)) := by
  rcases not_canRaiseS_cases hz h with h1 | h1 | h1 | h1
  · rw [hnext] at h1
    exact absurd h1 (by simp)
  · rw [hhold] at h1
    exact absurd h1 (by simp)
  · rcases h1 with ⟨a', bs, run, hpa, hface, hrun, htwin⟩
    rw [hhold] at hpa
    obtain rfl := Option.some.inj hpa
    exact Or.inl ⟨bs, run, hface, hrun, htwin⟩
  · rcases h1 with ⟨a', hpa, hbel, hhid⟩
    rw [hhold] at hpa
    obtain rfl := Option.some.inj hpa
    exact Or.inr ⟨hbel, hhid⟩

/-- **The buried obstruction is a cover.**  `CoveredAt z c` (some card sits on
`c`), the first step of the descent. -/
theorem covered_at_of_buried {z : State} (hz : z.WF) {c : Card} {a : Anchor}
    {bs run : List Card} (hhold : z.pileHolding c = some a)
    (hface : (z.piles a).faceUp = bs ++ c :: run) (hrun : run ≠ []) :
    CoveredAt z c :=
  covered_of_not_canRaiseS hz hhold hface hrun

/-- **The commit-lock obstruction freezes the suit.**  A lone face-up card at
the bottom of its run cannot be passed by its suit's rung anywhere in the
orbit: `Temp/FrozenSuit.lean` covers both lock sub-cases (a hidden deck under
the card, or a non-king).

This is the "harmless deadlock" row: for a class-mate `t`, `rungAt t c.suit`
never exceeds `rungAt z c.suit`, so the frozen suit can never be the reason a
rung comparison fails. -/
theorem frozen_of_deficit_lock {z w : State} {c : Card} {a : Anchor}
    (hz : z.WF) (horb : sameOrbitSetoid.r z w)
    (hnext : z.nextUp c = true) (htop : z.pileOfTop c = some a)
    (hbel : below c (z.piles a).faceUp = [])
    (hlk : (z.piles a).hidden ≠ [] ∨ c.rank ≠ Rank.king) :
    rungAt w c.suit ≤ rungAt z c.suit := by
  rcases hlk with hh | hk
  · exact FrozenSuit.commitLocked_rung_le hz horb hnext htop hbel hh
  · exact FrozenSuit.commitLocked_rung_le_of_not_king hz horb hnext htop hbel hk

/-- **THE DEADLOCK DICHOTOMY.**  At a deficit point (`c` next-up and on the
board) a `¬ CanRaiseS z c` is either a cover above `c` (continue the descent)
or a commit lock (the suit is frozen, so harmless).  This is the exact
`obstruction_at_deficit` + `CoveredAt` form the refined plan's descent wants. -/
theorem obstruction_dichotomy {z : State} (hz : z.WF) {c : Card}
    (hnext : z.nextUp c = true) {a : Anchor} (hhold : z.pileHolding c = some a)
    (h : ¬ CanRaiseS z c) :
    CoveredAt z c ∨
      (below c (z.piles a).faceUp = [] ∧
        ((z.piles a).hidden ≠ [] ∨ c.rank ≠ Rank.king)) := by
  rcases obstruction_at_deficit hz hnext hhold h with hb | hlk
  · obtain ⟨bs, run, hface, hrun, -⟩ := hb
    exact Or.inl (covered_at_of_buried hz hhold hface hrun)
  · exact Or.inr hlk

/-! ## 3. The fork branch: a collapsed spectrum is a fork -/

/-- **DRAIN-TO-FORK, closed.**  If the `S`-live set of `st` has collapsed onto
the twin pair `{x, x.twin}` (written as the implication `CanRaiseS st d → d = x
∨ d = x.twin`, with both members live), and `x.twin` is vanilla-blocked, then
`st` is a `ForkWitness` and hence the class of `st` is `Fork`.

No invariant, no rank floor: this is `forkWitness_of_spectrum` plus the
definitional closure of `Fork`. -/
theorem fork_of_collapsed_spectrum {st : State} {x : Card}
    (hx : CanRaiseS st x) (hxt : CanRaiseS st x.twin)
    (honly : ∀ d, CanRaiseS st d → d = x ∨ d = x.twin)
    (hblocked : ¬ CanRaise st x.twin) :
    Fork st := by
  have hspec : ∀ c : Card, (c = x ∨ c = x.twin) ↔ CanRaiseS st c := by
    intro c
    constructor
    · rintro (rfl | rfl)
      · exact hx
      · exact hxt
    · exact honly c
  exact ⟨st, x, RevEqW_refl st, forkWitness_of_spectrum hspec hblocked⟩

/-- The same, from the exact spectrum equality that a drain produces. -/
theorem fork_of_spectrum {st : State} {x : Card}
    (hspec : ∀ c : Card, (c = x ∨ c = x.twin) ↔ CanRaiseS st c)
    (hblocked : ¬ CanRaise st x.twin) :
    Fork st :=
  ⟨st, x, RevEqW_refl st, forkWitness_of_spectrum hspec hblocked⟩

/-! ## 3. The trivial cases of the target -/

/-- The target is immediate (empty play at `s`) whenever `t`'s rungs are below
`s`'s.  The whole content of the target is the strictly-upward case. -/
theorem raisesOrFork_of_rungLe_rev {s t : State} (h : RungLe t s) :
    (∃ ws v, RaiseSSeqLicensed s ws v ∧ RungLe s v ∧ RungLe t v) ∨ Fork s :=
  Or.inl ⟨[], s, RaiseSSeqLicensed.nil s, fun _ => Nat.le_refl _, h⟩

/-- Equal rungs likewise (a special case of the previous row, recorded because
the induction's base case is exactly this). -/
theorem raisesOrFork_of_rungEq {s t : State} (h : ∀ σ : Suit, rungAt s σ = rungAt t σ) :
    (∃ ws v, RaiseSSeqLicensed s ws v ∧ RungLe s v ∧ RungLe t v) ∨ Fork s :=
  raisesOrFork_of_rungLe_rev (fun σ => Nat.le_of_eq (h σ).symm)

/-! ## 4. The route implies `FullJoinAtLeastOrFork`, residue-free -/

/-- **THE ROUTE'S PAYOFF.**  If the target holds (supplied as a hypothesis, so
no new predicate is introduced), then `FullJoinAtLeastOrFork` holds with the
join witness `w := v` produced by the raiseS play itself.

The only content is transitivity of the orbit (`RaiseSSeqLicensed.revEqW`) and
`Nat.max_le`.  No `SatDifferForkWF`, no saturation, no top. -/
theorem fullJoinAtLeastOrFork_of_raises_or_fork
    (h : ∀ s t : State, s.WF → sameOrbitSetoid.r s t →
      (∃ ws v, RaiseSSeqLicensed s ws v ∧ RungLe s v ∧ RungLe t v) ∨ Fork s) :
    FullJoinAtLeastOrFork := by
  intro s s' hs hs' hcls
  rcases h s s' hs hcls with ⟨ws, v, hplay, hsv, hs'v⟩ | hfork
  · refine Or.inl ⟨v, ?_, ?_⟩
    · exact RevEqW_symm (RaiseSSeqLicensed.revEqW hplay hs)
    · intro σ
      exact Nat.max_le.mpr ⟨hsv σ, hs'v σ⟩
  · exact Or.inr hfork

end OneColourClosure

#print axioms OneColourClosure.canRaiseS_of_word_notMem
#print axioms OneColourClosure.exists_append_raise
#print axioms OneColourClosure.exists_append_raise_of_word_notMem
#print axioms OneColourClosure.twin_raise_square_both
#print axioms OneColourClosure.rungLe_of_raiseSSeqLicensed
#print axioms OneColourClosure.obstruction_at_deficit
#print axioms OneColourClosure.covered_at_of_buried
#print axioms OneColourClosure.frozen_of_deficit_lock
#print axioms OneColourClosure.obstruction_dichotomy
#print axioms OneColourClosure.fork_of_collapsed_spectrum
#print axioms OneColourClosure.fork_of_spectrum
#print axioms OneColourClosure.raisesOrFork_of_rungLe_rev
#print axioms OneColourClosure.raisesOrFork_of_rungEq
#print axioms OneColourClosure.fullJoinAtLeastOrFork_of_raises_or_fork
