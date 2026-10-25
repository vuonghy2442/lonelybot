import Orig2.TwinSuffixCancel
import Orig2.TwinPairFreeRev
import Orig2.TwinPreludeFunctor
import Orig2.TwinAbstractLadder

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-!
# Orig2.TwinLastPull — the last-pull residual: recipe blocks and postludes

This card attacks the last-letter residual `LastPullCancellation` of
`Orig2/TwinSuffixCancel.lean`, starting from the canonical recipe block.

## What is proved here

* `seat_eq_of_pairFree_step` / `seat_eq_of_pairFree_play`: a pair-free
  witness shuffle out of a both-`.inr` state fixes both twins' seat
  values **exactly** (public form of the private rows of
  `TwinSuffixCancel`).

* `pairFreeOrbit_splice_of_pairFree`: the splice functor at the
  `PairFreeOrbit` grade — a pair-free witness shuffle `s → t` maps to a
  pair-free witness shuffle `splice s → splice t` (the existing
  `splice_play_hom` only records the `RevEqW` shadow).  The reverse
  orientation `pairFreeOrbit_splice_rev` follows by `PairFreeReversal`.

* **`pairFreeOrbit_of_recipe_postlude`** (the mandatory subcase): a
  canonical recipe block whose endpoint is the run splice
  `u.spliceTwinRuns x`, followed by a pair-free postlude, is pair-free
  orbit from its endpoint back to the splice.  The postlude is reversed
  at the splice, where both twins are `.inr`-seated.

* **`pairFreeOrbit_of_raise_postlude`**: the canonical recipe block is
  *built* by `selfSwapSeg_of_raise`; the `SelfSwapSeg` witness supplies
  the play to the splice, and the postlude is then the same reversal.

* **`pairFreeOrbit_of_prefix_recipe_postlude`** and
  **`pairFreeOrbit_of_prefix_raise_postlude`**: the same statements with
  an arbitrary pair-free prefix before the recipe.  The prefix is
  transported through the splice functor, so the endpoint is pair-free
  orbit to the splice of the *prefix source*.

* `lastPullCancellation_singleDetourIdentity`: the single-detour
  identity shape (pair-free prefix, raise, immediate pull back onto the
  source parent) is a subcase of `LastPullCancellation`.

* `lastPullCancellation_ladderSwap` / `_twin`: the two canonical
  three-leg swap ladders with an arbitrary pair-free prefix are subcases
  of `LastPullCancellation`; both conclude the disjunction with the
  splice.

## The exact remaining goal

The uncovered case is the **arbitrary-prefix, arbitrary-balanced
pair-foundation word** case.  `last_pairFound_is_pull` reduces the full
last-letter statement to the pull-shaped residual below
(`LastPullCancellationPull`), and `lastPullCancellation_of_pullResidual`
proves the reduction.  No counterexample is known; the obstruction to
the present commutation route is the same-suit / source-pile /
exposed-target non-commutation recorded in `TwinRaiseCommute`.  The exact
Lean statement is reproduced at the end of the file.

Zero `sorry`, zero `Classical.choice`, no new axioms.
-/

open State

namespace TwinLastPull

/-! ## §1. Basic kit -/

/-- A pair-free move stays pair-free after relabelling its mover. -/
theorem notFoundPair_relabelMover {x : Card} {m : Move}
    (h : NotFoundPair x m) : NotFoundPair x (Move.relabelMover x m) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  cases m with
  | draw => simp [Move.relabelMover, NotFoundPair]
  | wasteToFound c => simp [Move.relabelMover, NotFoundPair]
  | wasteToTab c b => simp [Move.relabelMover, NotFoundPair]
  | tabToFound c =>
      have hcx : c ≠ x := fun hc => h1 (by rw [hc])
      have hct : c ≠ x.twin := fun hc => h2 (by rw [hc])
      rw [Move.relabelMover, card_relabelTwin_ne hcx hct]
      exact ⟨h1, h2, h3, h4⟩
  | foundToTab c b =>
      have hcx : c ≠ x := fun hc => h3 b (by rw [hc])
      have hct : c ≠ x.twin := fun hc => h4 b (by rw [hc])
      rw [Move.relabelMover, card_relabelTwin_ne hcx hct]
      exact ⟨h1, h2, h3, h4⟩
  | tabToTab c b =>
      simp [Move.relabelMover, NotFoundPair]

/-- Splitting a witness walk at a list prefix. -/
theorem walk_split {P : State → Move → Prop} :
    ∀ {s s' : State} {A B : List Move},
      Walk P s (A ++ B) s' → ∃ u, Walk P s A u ∧ Walk P u B s' := by
  intro s s' A B
  induction A generalizing s with
  | nil =>
      intro h
      exact ⟨s, .nil s, by simpa using h⟩
  | cons m rest ih =>
      intro h
      cases h with
      | cons hlet hstep hrest =>
          obtain ⟨u, hA, hB⟩ := ih hrest
          exact ⟨u, .cons hlet hstep hA, hB⟩

/-- Expose the first letter of a witness walk. -/
theorem walk_cons_inv {P : State → Move → Prop} {st s' : State}
    {m : Move} {ρ : List Move} (h : Walk P st (m :: ρ) s') :
    ∃ s1, P st m ∧ State.step st m = some s1 ∧ Walk P s1 ρ s' := by
  cases h with
  | cons hlet hstep hrest => exact ⟨_, hlet, hstep, hrest⟩

/-! ## §2. Pair-free moves preserve the exact `.inr` seats -/

/-- A pair-free reversible letter at a both-seated `WF` state fixes both
twins' seat values exactly. -/
theorem seat_eq_of_pairFree_step {u v : State} {x : Card} {m : Move}
    (hwf : u.WF) (hstep : State.step u m = some v)
    (hrev : reversibleAtW u m) (hno : NotFoundPair x m)
    (hx : ∃ z, seatOf u x = some (Sum.inr z))
    (hxt : ∃ z : Card, seatOf u x.twin = some (Sum.inr z.twin)) :
    seatOf v x = seatOf u x ∧ seatOf v x.twin = seatOf u x.twin := by
  have hse_x : seatOf u x ≠ none := by
    obtain ⟨z, hz⟩ := hx
    rw [hz]; simp
  have hse_xt : seatOf u x.twin ≠ none := by
    obtain ⟨z, hz⟩ := hxt
    rw [hz]; simp
  have hxEq : seatOf v x = seatOf u x := by
    cases m with
    | draw => exact (chart_draw hstep).1 x
    | wasteToFound y => exact absurd hrev (wasteToFound_not_reversibleAtW u y)
    | wasteToTab y base => exact absurd hrev (wasteToTab_not_reversibleAtW u y base)
    | tabToFound y =>
        have hyx : y ≠ x := fun h => hno.1 (by rw [h])
        exact raise_seat_change_of_seated hstep hrev hse_x (Ne.symm hyx)
    | foundToTab y base =>
        have hyx : y ≠ x := fun h => hno.2.2.1 base (by rw [h])
        exact pull_seat_change hstep x (Ne.symm hyx)
    | tabToTab y base =>
        obtain ⟨hyx, -⟩ := TwinSpliceComm.tabToTab_mover_off hwf hx hxt hstep
        have h := tfc_seat_point_edit hwf hstep hrev x
        rwa [ite_eq_right (Ne.symm hyx)] at h
  have hxtEq : seatOf v x.twin = seatOf u x.twin := by
    cases m with
    | draw => exact (chart_draw hstep).1 x.twin
    | wasteToFound y => exact absurd hrev (wasteToFound_not_reversibleAtW u y)
    | wasteToTab y base => exact absurd hrev (wasteToTab_not_reversibleAtW u y base)
    | tabToFound y =>
        have hyt : y ≠ x.twin := fun h => hno.2.1 (by rw [h])
        exact raise_seat_change_of_seated hstep hrev hse_xt (Ne.symm hyt)
    | foundToTab y base =>
        have hyt : y ≠ x.twin := fun h => hno.2.2.2 base (by rw [h])
        exact pull_seat_change hstep x.twin (Ne.symm hyt)
    | tabToTab y base =>
        obtain ⟨-, hyt⟩ := TwinSpliceComm.tabToTab_mover_off hwf hx hxt hstep
        have h := tfc_seat_point_edit hwf hstep hrev x.twin
        rwa [ite_eq_right (Ne.symm hyt)] at h
  exact ⟨hxEq, hxtEq⟩

/-- A pair-free witness shuffle out of a both-seated `WF` state fixes
both twins' seat values exactly. -/
theorem seat_eq_of_pairFree_play {x : Card} :
    ∀ {s w : State} {seg : List Move},
      s.WF → ShufflePlayW s seg w →
      (∀ m ∈ seg, NotFoundPair x m) →
      (∃ z, seatOf s x = some (Sum.inr z)) →
      (∃ z : Card, seatOf s x.twin = some (Sum.inr z.twin)) →
      seatOf w x = seatOf s x ∧ seatOf w x.twin = seatOf s x.twin := by
  intro s w seg
  induction seg generalizing s with
  | nil =>
      intro _ hplay _ _ _
      cases hplay
      exact ⟨rfl, rfl⟩
  | cons m rest ih =>
      intro hwf hplay hno hx hxt
      obtain ⟨s₁, hrev, hstep, hrest⟩ := walk_cons_inv hplay
      have hm : NotFoundPair x m := hno m (by simp)
      have hstepEq := seat_eq_of_pairFree_step hwf hstep hrev hm hx hxt
      have hx₁ : ∃ z, seatOf s₁ x = some (Sum.inr z) := by
        obtain ⟨z, hz⟩ := hx
        exact ⟨z, by rw [hstepEq.1, hz]⟩
      have hxt₁ : ∃ z : Card, seatOf s₁ x.twin = some (Sum.inr z.twin) := by
        obtain ⟨z, hz⟩ := hxt
        exact ⟨z, by rw [hstepEq.2, hz]⟩
      have hwf₁ : s₁.WF := step_wf hwf hstep
      have ih' := ih hwf₁ hrest
        (fun n hn => hno n (List.mem_cons_of_mem m hn)) hx₁ hxt₁
      exact ⟨ih'.1.trans hstepEq.1, ih'.2.trans hstepEq.2⟩

/-! ## §3. The pair-free splice functor -/

/-- **The splice functor on pair-free plays.**  A pair-free witness
shuffle `s → t` maps to a pair-free witness shuffle of the run splices. -/
theorem pairFreeOrbit_splice_of_pairFree {x : Card} {s t : State} {play : List Move}
    (hwf : s.WF) (hx : ∃ z, seatOf s x = some (Sum.inr z))
    (hxt : ∃ z : Card, seatOf s x.twin = some (Sum.inr z.twin))
    (hplay : ShufflePlayW s play t)
    (hno : ∀ m ∈ play, NotFoundPair x m) :
    PairFreeOrbit x (s.spliceTwinRuns x) (t.spliceTwinRuns x) := by
  revert hwf hx hxt hno
  induction hplay with
  | nil st =>
      intro _ _ _ _
      exact pairFreeOrbit_refl x (st.spliceTwinRuns x)
  | @cons st s₁ W m ρ hrev hstep hrest ih =>
      intro hwf hx hxt hno
      have hm : NotFoundPair x m := hno m (by simp)
      have hstepS :=
        TwinSpliceComm.splice_step_comm_rev hwf hx hxt hstep hrev hm
      have hrevS := reversibleAtW_splice_relabelMover hwf hx hxt hrev hm
      have hnoS := notFoundPair_relabelMover hm
      have hseats := seat_inr_of_pairFree_step hwf hstep hrev hm hx hxt
      have hwf₁ : s₁.WF := step_wf hwf hstep
      have hsingle : PairFreeOrbit x (st.spliceTwinRuns x) (s₁.spliceTwinRuns x) := by
        refine pairFreeOrbit_of_play (Walk.cons hrevS hstepS (Walk.nil _)) ?_
        intro n hn
        rw [List.mem_singleton] at hn
        subst hn
        exact hnoS
      have htail : PairFreeOrbit x (s₁.spliceTwinRuns x) (W.spliceTwinRuns x) :=
        ih hwf₁ hseats.1 hseats.2
          (fun n hn => hno n (List.mem_cons_of_mem m hn))
      exact PairFreeOrbit.trans hsingle htail

/-- The splice functor in the reverse orientation. -/
theorem pairFreeOrbit_splice_rev {x : Card} {s t : State} {play : List Move}
    (hwf : s.WF) (hx : ∃ z, seatOf s x = some (Sum.inr z))
    (hxt : ∃ z : Card, seatOf s x.twin = some (Sum.inr z.twin))
    (hplay : ShufflePlayW s play t)
    (hno : ∀ m ∈ play, NotFoundPair x m) :
    PairFreeOrbit x (t.spliceTwinRuns x) (s.spliceTwinRuns x) := by
  obtain ⟨play', hplay', hno'⟩ :=
    pairFreeOrbit_splice_of_pairFree hwf hx hxt hplay hno
  have hwfS : (s.spliceTwinRuns x).WF := wf_spliceTwinRuns hwf hx hxt
  obtain ⟨a, b, zs, ha, hb, hab, _, _⟩ := TwinSpliceComm.splice_setup hwf hx hxt
  obtain ⟨zx, hxse⟩ := hx
  obtain ⟨zt, hxtse⟩ := hxt
  have hztz : zt = zx := twin_parent_eq_of_seats hwf hxse hxtse
  have hxtse' : seatOf s x.twin = some (Sum.inr zx.twin) := by
    rw [hztz] at hxtse
    exact hxtse
  have hxS : seatOf (s.spliceTwinRuns x) x = some (Sum.inr zx.twin) := by
    rw [seatOf_splice_self hwf ha hb hab]
    exact hxtse'
  have hxtS : seatOf (s.spliceTwinRuns x) x.twin = some (Sum.inr (zx.twin).twin) := by
    rw [seatOf_splice_twin hwf ha hb hab, hxse, card_twin_twin]
  exact TwinPairFreeRev.pairFreeReversal (x := x) hwfS hxS hxtS hplay' hno'

/-! ## §4. The canonical recipe block and its pair-free postlude -/

/-- **The mandatory subcase.**  A witness shuffle consists of a canonical
recipe block ending at the run splice `u.spliceTwinRuns x`, followed by a
pair-free suffix.  The suffix is reversed by `PairFreeReversal` at the
splice, where both twins are `.inr`-seated. -/
theorem pairFreeOrbit_of_recipe_postlude
    {u v w : State} {x : Card} {recipe suf : List Move}
    (hwf : u.WF)
    (hx : ∃ z, seatOf u x = some (Sum.inr z))
    (hxt : ∃ z : Card, seatOf u x.twin = some (Sum.inr z.twin))
    (hraise : reversibleAtW u (Move.tabToFound x) ∨
      reversibleAtW u (Move.tabToFound x.twin))
    (hrecipe : ShufflePlayW u recipe w)
    (hw : w = u.spliceTwinRuns x)
    (hsuf : ShufflePlayW w suf v)
    (hnoSuf : ∀ m ∈ suf, NotFoundPair x m) :
    PairFreeOrbit x v (u.spliceTwinRuns x) := by
  have hwfW : w.WF := by
    rw [hw]
    exact wf_spliceTwinRuns hwf hx hxt
  obtain ⟨zx, hxse⟩ := hx
  obtain ⟨zt, hxtse⟩ := hxt
  have hzt : zt = zx := twin_parent_eq_of_seats hwf hxse hxtse
  have hxtse' : seatOf u x.twin = some (Sum.inr zx.twin) := by
    rw [hzt] at hxtse
    exact hxtse
  obtain ⟨a, b, zs, ha, hb, hab, _, _⟩ :=
    TwinSpliceComm.splice_setup hwf ⟨zx, hxse⟩ ⟨zx, hxtse'⟩
  have hxw : seatOf w x = some (Sum.inr zx.twin) := by
    rw [hw, seatOf_splice_self hwf ha hb hab]
    exact hxtse'
  have hxtw : seatOf w x.twin = some (Sum.inr (zx.twin).twin) := by
    rw [hw, seatOf_splice_twin hwf ha hb hab, hxse, card_twin_twin]
  have hback : PairFreeOrbit x v w :=
    TwinPairFreeRev.pairFreeReversal (x := x) hwfW hxw hxtw hsuf hnoSuf
  rw [← hw]
  exact hback

/-- **The canonical recipe block, built by `selfSwapSeg_of_raise`.**  The
first reversible raise of either twin supplies a `SelfSwapSeg` from `u`
to `u.spliceTwinRuns x`; the pair-free postlude is then reversed at that
splice. -/
theorem pairFreeOrbit_of_raise_postlude
    {u v : State} {x : Card} {suf : List Move}
    (hwf : u.WF)
    (hx : ∃ z, seatOf u x = some (Sum.inr z))
    (hxt : ∃ z : Card, seatOf u x.twin = some (Sum.inr z.twin))
    (hraise : reversibleAtW u (Move.tabToFound x) ∨
      reversibleAtW u (Move.tabToFound x.twin))
    (hsuf : ShufflePlayW (u.spliceTwinRuns x) suf v)
    (hnoSuf : ∀ m ∈ suf, NotFoundPair x m) :
    PairFreeOrbit x v (u.spliceTwinRuns x) := by
  obtain ⟨zx, hxse⟩ := hx
  obtain ⟨zt, hxtse⟩ := hxt
  have hzt : zt = zx := twin_parent_eq_of_seats hwf hxse hxtse
  have hxtse' : seatOf u x.twin = some (Sum.inr zx.twin) := by
    rw [hzt] at hxtse
    exact hxtse
  obtain ⟨seg, w, hself⟩ :=
    selfSwapSeg_of_raise (x := x) (z := zx) hwf hxse hxtse' hraise
  obtain ⟨hwfu, hxu, hxtu, hplay, hw⟩ := hself
  have hsuf' : ShufflePlayW w suf v := by
    rw [hw]
    exact hsuf
  exact pairFreeOrbit_of_recipe_postlude hwfu hxu hxtu hraise hplay hw hsuf' hnoSuf

/-- **The recipe block with a pair-free prefix.**  The prefix is pushed
through the splice functor, so the endpoint is pair-free orbit to the run
splice of the *prefix source*. -/
theorem pairFreeOrbit_of_prefix_recipe_postlude
    {u0 u v w : State} {x : Card} {pre recipe suf : List Move}
    (hwf0 : u0.WF)
    (hx0 : ∃ z, seatOf u0 x = some (Sum.inr z))
    (hxt0 : ∃ z : Card, seatOf u0 x.twin = some (Sum.inr z.twin))
    (hpre : ShufflePlayW u0 pre u)
    (hnoPre : ∀ m ∈ pre, NotFoundPair x m)
    (hx : ∃ z, seatOf u x = some (Sum.inr z))
    (hxt : ∃ z : Card, seatOf u x.twin = some (Sum.inr z.twin))
    (hraise : reversibleAtW u (Move.tabToFound x) ∨
      reversibleAtW u (Move.tabToFound x.twin))
    (hrecipe : ShufflePlayW u recipe w)
    (hw : w = u.spliceTwinRuns x)
    (hsuf : ShufflePlayW w suf v)
    (hnoSuf : ∀ m ∈ suf, NotFoundPair x m) :
    PairFreeOrbit x v (u0.spliceTwinRuns x) := by
  have hwf : u.WF := run_wf hwf0 (Walk_run _ hpre)
  have hrecipeBack : PairFreeOrbit x v (u.spliceTwinRuns x) :=
    pairFreeOrbit_of_recipe_postlude hwf hx hxt hraise hrecipe hw hsuf hnoSuf
  have hpreSplice : PairFreeOrbit x (u.spliceTwinRuns x) (u0.spliceTwinRuns x) :=
    pairFreeOrbit_splice_rev (x := x) hwf0 hx0 hxt0 hpre hnoPre
  exact PairFreeOrbit.trans hrecipeBack hpreSplice

/-- **The `selfSwapSeg_of_raise` recipe with a pair-free prefix.** -/
theorem pairFreeOrbit_of_prefix_raise_postlude
    {u0 u v : State} {x : Card} {pre suf : List Move}
    (hwf0 : u0.WF)
    (hx0 : ∃ z, seatOf u0 x = some (Sum.inr z))
    (hxt0 : ∃ z : Card, seatOf u0 x.twin = some (Sum.inr z.twin))
    (hpre : ShufflePlayW u0 pre u)
    (hnoPre : ∀ m ∈ pre, NotFoundPair x m)
    (hx : ∃ z, seatOf u x = some (Sum.inr z))
    (hxt : ∃ z : Card, seatOf u x.twin = some (Sum.inr z.twin))
    (hraise : reversibleAtW u (Move.tabToFound x) ∨
      reversibleAtW u (Move.tabToFound x.twin))
    (hsuf : ShufflePlayW (u.spliceTwinRuns x) suf v)
    (hnoSuf : ∀ m ∈ suf, NotFoundPair x m) :
    PairFreeOrbit x v (u0.spliceTwinRuns x) := by
  have hwf : u.WF := run_wf hwf0 (Walk_run _ hpre)
  have hrecipeBack : PairFreeOrbit x v (u.spliceTwinRuns x) :=
    pairFreeOrbit_of_raise_postlude hwf hx hxt hraise hsuf hnoSuf
  have hpreSplice : PairFreeOrbit x (u.spliceTwinRuns x) (u0.spliceTwinRuns x) :=
    pairFreeOrbit_splice_rev (x := x) hwf0 hx0 hxt0 hpre hnoPre
  exact PairFreeOrbit.trans hrecipeBack hpreSplice

/-! ## §5. The canonical swap ladders as `LastPullCancellation` subcases -/

/-- **The canonical swap arm of `LastPullCancellation`.**  A pair-free
prefix followed by the three-leg ladder `raise x, slide x.twin onto z,
pull x onto z.twin`; the endpoint is pair-free orbit to the run splice
of the source. -/
theorem lastPullCancellation_ladderSwap {x : Card} {u v : State} {z : Card}
    {pre : List Move}
    (hwf : u.WF)
    (hx : seatOf u x = some (Sum.inr z))
    (hxt : seatOf u x.twin = some (Sum.inr z.twin))
    (hplay : ShufflePlayW u
      (pre ++ [Move.tabToFound x, Move.tabToTab x.twin (Sum.inr z),
        Move.foundToTab x (Sum.inr z.twin)]) v)
    (hnoPre : ∀ m ∈ pre, NotFoundPair x m)
    (hvx : ∃ w, seatOf v x = some (Sum.inr w))
    (hvt : ∃ w', seatOf v x.twin = some (Sum.inr w')) :
    PairFreeOrbit x v u ∨ PairFreeOrbit x v (u.spliceTwinRuns x) := by
  obtain ⟨u1, hpre, htail⟩ := walk_split hplay
  have hwf1 : u1.WF := run_wf hwf (Walk_run _ hpre)
  have hseats := seat_eq_of_pairFree_play (x := x) hwf hpre hnoPre
    ⟨z, hx⟩ ⟨z, hxt⟩
  have hx1 : seatOf u1 x = some (Sum.inr z) := hseats.1.trans hx
  have hxt1 : seatOf u1 x.twin = some (Sum.inr z.twin) := hseats.2.trans hxt
  have htail' : ShufflePlayW u1 (ladderPlay x z []) v := by
    simpa [ladderPlay, ladderPlayRev] using htail
  rcases pairFree_endpoint_classification_of_ladder hwf1 hx1 hxt1 htail' hvx hvt
    with hleft | hright
  · have hback : PairFreeOrbit x u1 u :=
      TwinPairFreeRev.pairFreeReversal (x := x) hwf hx hxt hpre hnoPre
    exact Or.inl (PairFreeOrbit.trans hleft hback)
  · have hback : PairFreeOrbit x (u1.spliceTwinRuns x) (u.spliceTwinRuns x) :=
      pairFreeOrbit_splice_rev (x := x) hwf ⟨z, hx⟩ ⟨z, hxt⟩ hpre hnoPre
    exact Or.inr (PairFreeOrbit.trans hright hback)

/-- **The mirror swap arm of `LastPullCancellation`.**  The ladder named
by `x.twin`: raise the twin, slide `x` onto `z.twin`, pull the twin onto
`z`. -/
theorem lastPullCancellation_ladderSwap_twin {x : Card} {u v : State} {z : Card}
    {pre : List Move}
    (hwf : u.WF)
    (hx : seatOf u x = some (Sum.inr z))
    (hxt : seatOf u x.twin = some (Sum.inr z.twin))
    (hplay : ShufflePlayW u
      (pre ++ [Move.tabToFound x.twin, Move.tabToTab x (Sum.inr z.twin),
        Move.foundToTab x.twin (Sum.inr z)]) v)
    (hnoPre : ∀ m ∈ pre, NotFoundPair x m)
    (hvx : ∃ w, seatOf v x = some (Sum.inr w))
    (hvt : ∃ w', seatOf v x.twin = some (Sum.inr w')) :
    PairFreeOrbit x v u ∨ PairFreeOrbit x v (u.spliceTwinRuns x) := by
  obtain ⟨u1, hpre, htail⟩ := walk_split hplay
  have hwf1 : u1.WF := run_wf hwf (Walk_run _ hpre)
  have hseats := seat_eq_of_pairFree_play (x := x) hwf hpre hnoPre
    ⟨z, hx⟩ ⟨z, hxt⟩
  have hx1 : seatOf u1 x = some (Sum.inr z) := hseats.1.trans hx
  have hxt1 : seatOf u1 x.twin = some (Sum.inr z.twin) := hseats.2.trans hxt
  have htail' : ShufflePlayW u1 (ladderPlay x.twin z.twin []) v := by
    simpa [ladderPlay, ladderPlayRev, card_twin_twin] using htail
  rcases pairFree_endpoint_classification_of_ladder_twin hwf1 hx1 hxt1 htail' hvx hvt
    with hleft | hright
  · have hback : PairFreeOrbit x u1 u :=
      TwinPairFreeRev.pairFreeReversal (x := x) hwf hx hxt hpre hnoPre
    exact Or.inl (PairFreeOrbit.trans hleft hback)
  · have hback : PairFreeOrbit x (u1.spliceTwinRuns x) (u.spliceTwinRuns x) :=
      pairFreeOrbit_splice_rev (x := x) hwf ⟨z, hx⟩ ⟨z, hxt⟩ hpre hnoPre
    exact Or.inr (PairFreeOrbit.trans hright hback)

/-! ## §6. A single-detour identity subcase of `LastPullCancellation` -/

/-- The canonical single-detour identity shape is a subcase of
`LastPullCancellation`: the play raises one twin and pulls it straight
back onto its source parent, with an arbitrary pair-free prefix. -/
theorem lastPullCancellation_singleDetourIdentity
    {x : Card} {u v : State} {z p : Card} {pre : List Move} {y : Card}
    (hwf : u.WF)
    (hx : seatOf u x = some (Sum.inr z))
    (hxt : seatOf u x.twin = some (Sum.inr z.twin))
    (hy : y = x ∨ y = x.twin)
    (hseatY : seatOf u y = some (Sum.inr p))
    (hplay : ShufflePlayW u
      (pre ++ Move.tabToFound y :: [Move.foundToTab y (Sum.inr p)]) v)
    (hnoPre : ∀ m ∈ pre, NotFoundPair x m)
    (hvx : ∃ w, seatOf v x = some (Sum.inr w))
    (hvt : ∃ w', seatOf v x.twin = some (Sum.inr w')) :
    PairFreeOrbit x v u ∨ PairFreeOrbit x v (u.spliceTwinRuns x) := by
  obtain ⟨w', hw'⟩ := hvt
  have hvt' : ∃ w' : Card, seatOf v x.twin = some (Sum.inr w'.twin) :=
    ⟨w'.twin, by simpa [card_twin_twin] using hw'⟩
  have h := pairFree_singleDetour_identity (x := x) (z := z) (p := p)
    (u := u) (v := v) (pre := pre) (suf := []) (y := y)
    (TwinPairFreeRev.pairFreeReversal (x := x)) hwf hx hxt hy hseatY
    (by simpa using hplay) hnoPre (by simp) hvx hvt'
  simpa using h

/-! ## §7. The exact residual -/

/-- **The pull-shaped residual.**  By `last_pairFound_is_pull`, every
instance of `LastPullCancellation` has its last letter in this shape.
This is the exact remaining obligation: an arbitrary prefix whose
pair-foundation word may contain several balanced raise/pull detours. -/
def LastPullCancellationPull (x : Card) : Prop :=
  ∀ {u v : State} {z : Card} {pre : List Move} {y : Card} {b : Base},
    u.WF →
    seatOf u x = some (Sum.inr z) →
    seatOf u x.twin = some (Sum.inr z.twin) →
    ShufflePlayW u (pre ++ [Move.foundToTab y b]) v →
    (y = x ∨ y = x.twin) →
    (∃ w, seatOf v x = some (Sum.inr w)) →
    (∃ w' : Card, seatOf v x.twin = some (Sum.inr w')) →
    PairFreeOrbit x v u ∨ PairFreeOrbit x v (u.spliceTwinRuns x)

/-- **Reduction of the last-letter residual to the pull shape.**  This is
the exact Lean form of the remaining goal after `last_pairFound_is_pull`. -/
theorem lastPullCancellation_of_pullResidual {x : Card}
    (h : LastPullCancellationPull x) : LastPullCancellation x := by
  intro u v z pre m hwf hx hxt hplay hm hvx hvt
  obtain ⟨y, b, hy, hmEq⟩ := last_pairFound_is_pull (x := x)
    (pre := pre) (m := m) (suf := []) hwf hx hxt hplay hm (by simp) hvx hvt
  subst hmEq
  exact h hwf hx hxt (by simpa using hplay) hy hvx hvt

/-! ## §8. Audit -/

#print axioms notFoundPair_relabelMover
#print axioms walk_split
#print axioms walk_cons_inv
#print axioms seat_eq_of_pairFree_step
#print axioms seat_eq_of_pairFree_play
#print axioms pairFreeOrbit_splice_of_pairFree
#print axioms pairFreeOrbit_splice_rev
#print axioms pairFreeOrbit_of_recipe_postlude
#print axioms pairFreeOrbit_of_raise_postlude
#print axioms pairFreeOrbit_of_prefix_recipe_postlude
#print axioms pairFreeOrbit_of_prefix_raise_postlude
#print axioms lastPullCancellation_ladderSwap
#print axioms lastPullCancellation_ladderSwap_twin
#print axioms lastPullCancellation_singleDetourIdentity
#print axioms lastPullCancellation_of_pullResidual

/-! ## §9. Report

### File

`Orig2/TwinLastPull.lean` (this file).  It does not import
`Orig2.TwinSingleDetour`, so no duplicate `PairFreeOrbit` is introduced.

### Proved subcases

1. **Recipe postlude** (`pairFreeOrbit_of_recipe_postlude`): a canonical
   recipe block ending at `u.spliceTwinRuns x`, followed by any pair-free
   witness suffix, is pair-free orbit from the endpoint to the splice.
   The suffix is reversed at the splice by the unconditional
   `PairFreeReversal`.

2. **Prefix + recipe postlude** (`pairFreeOrbit_of_prefix_recipe_postlude`):
   the same with an arbitrary pair-free prefix before the recipe.  The
   prefix is transported to the splice of its own source by the new
   `PairFreeOrbit`-grade splice functor
   (`pairFreeOrbit_splice_of_pairFree`, `pairFreeOrbit_splice_rev`).

3. **Canonical swap ladders** (`lastPullCancellation_ladderSwap`,
   `lastPullCancellation_ladderSwap_twin`): the two three-leg swap
   ladders with an arbitrary pair-free prefix are subcases of
   `LastPullCancellation`, concluding the disjunction with the splice.

4. **Single-detour identity** (`lastPullCancellation_singleDetourIdentity`):
   a pair-free prefix, a raise of either twin, and the immediate pull
   back onto the source parent.

### Exact remaining goal

```
def LastPullCancellationPull (x : Card) : Prop :=
  ∀ {u v : State} {z : Card} {pre : List Move} {y : Card} {b : Base},
    u.WF →
    seatOf u x = some (Sum.inr z) →
    seatOf u x.twin = some (Sum.inr z.twin) →
    ShufflePlayW u (pre ++ [Move.foundToTab y b]) v →
    (y = x ∨ y = x.twin) →
    (∃ w, seatOf v x = some (Sum.inr w)) →
    (∃ w' : Card, seatOf v x.twin = some (Sum.inr w')) →
    PairFreeOrbit x v u ∨ PairFreeOrbit x v (u.spliceTwinRuns x)
```

`lastPullCancellation_of_pullResidual` proves
`LastPullCancellationPull x → LastPullCancellation x`.  What remains is
the case where the prefix contains a non-canonical balanced
pair-foundation word: several alternating raise/pull detours of the two
twins, interleaved with pair-free letters.  The canonical recipe (item 1)
and the two swap ladders (item 3) are the matched cases proved here; the
non-canonical interleavings are exactly where the same-suit,
source-pile, and exposed-target non-commutation of `TwinRaiseCommute`
blocks a direct letter-by-letter re-association.

### Axioms

Every exported theorem is audited below.  The expected footprint is the
Lean kernel's standard `propext` / `Quot.sound` (and no
`Classical.choice`); no new axioms are introduced.
-/
