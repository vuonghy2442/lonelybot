import Orig2.Fork.Local.ForkStraddle

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-!
# Orig2/ForkLandResReduction — from the net-zero pair to `LandingResidual`

READ-ONLY scratch card.  No `sorry`, no `Classical.choice`, no `native_decide`.

## Contents

* §1 `interior_not_raise` — the straddle interior contains NO raise at all.
  (`SplitHyp` says `post` is free and the left leg is raise-free; `FreeOrPull`
  then excludes `tabToFound`.)
* §2 `UncoverResidual` — the **exact residual** left after the state-level
  net-zero of `Temp/LandRes_NetZero.lean`: *if the interior contains a landing
  on `d`, then a strictly shorter witness play exists.*  This is the play-level
  form of "delete the covering slide and re-run the interior."
* §3 `landingResidual_of_uncover` — that residual gives
  `StradKit.LandingResidual` outright, by shortestness.
* §4 the pin: `StradKit.splitTwinRungGe_of_landing_twin` consumes the result.
* §5 the adjacent instance of the residual is discharged (`slide_pair_shortens`).

The point of §1 is that the brief's "uncover by `raise x`" case **cannot occur
inside the interior**: the raise is not in the interior's alphabet.  So the only
surviving uncover is a slide, which is what `Temp/LandRes_NetZero.lean` cancels.
-/

namespace LandRes

open SplitKit

/-! ## §1. The interior is raise-free -/

/-- **THE INTERIOR HAS NO RAISE.**  `FreeOrPull` is `draw | slide | pull`, none
of which is a `tabToFound`. -/
theorem interior_not_raise
    {u v : State} {ρ : List Move} {F : State} {left right : List Move}
    {c d : Card} {b : Base} {pre post tail : List Move}
    (hs : SplitKit.SplitHyp u v ρ F left right c d b pre post tail)
    (hraiseFree : ∀ m ∈ left, ¬ Bubble.IsRaise m)
    {α β : List Move} {bz : Base}
    (hpre : pre = α ++ Move.foundToTab d bz :: β) :
    ∀ m ∈ (β ++ Move.foundToTab c b :: post), ¬ Bubble.IsRaise m := by
  intro m hm hr
  have hall := StradKit.interior_freeOrPull hs hraiseFree hpre
  rcases hall m hm with hfree | ⟨x, bb, hx⟩
  · rcases hfree with rfl | ⟨y, bb, hy⟩
    · obtain ⟨z, hz⟩ := hr
      cases hz
    · obtain ⟨z, hz⟩ := hr
      rw [hy] at hz
      cases hz
  · obtain ⟨z, hz⟩ := hr
    rw [hx] at hz
    cases hz

/-! ## §2. The exact residual -/

/-- **`UncoverResidual` — THE PLAY-LEVEL NET-ZERO, STATED EXACTLY.**  At a
`SplitHyp` whose left leg is raise-free, if the interior carries a landing on
the raise card, then some strictly shorter witness play exists.  By
`StradKit.straddle_no_landing_false` the self-slide shape is already dead, so
this is the whole of `LandingResidual` after the state-level cancellation
`LandRes.slideSt_slideSt_self`. -/
def UncoverResidual : Prop :=
  ∀ (u v : State) (ρ : List Move) (F : State) (left right : List Move)
    (c d : Card) (b : Base) (pre post tail : List Move),
    SplitKit.SplitHyp u v ρ F left right c d b pre post tail →
    (∀ m ∈ left, ¬ Bubble.IsRaise m) →
    ∀ (bz : Base) (α β : List Move),
      pre = α ++ Move.foundToTab d bz :: β →
      (∃ q ∈ (β ++ Move.foundToTab c b :: post), StradKit.LandsOn d q) →
      ∃ ρ' : List Move, ShufflePlayW u ρ' v ∧ ρ'.length < ρ.length

/-- **THE RESIDUAL GIVES `LandingResidual`.**  A landing would shorten the
shortest witness play. -/
theorem landingResidual_of_uncover (h : UncoverResidual) :
    StradKit.LandingResidual := by
  intro u v ρ F left right c d b pre post tail hs hrf bz α β hpre q hq hland
  have hsk := hs
  obtain ⟨huwf, -, -, hplay, -, hmin, -, -, -, -, -, -⟩ := hs
  obtain ⟨ρ', hρ'play, hlen⟩ :=
    h u v ρ F left right c d b pre post tail hsk hrf bz α β hpre ⟨q, hq, hland⟩
  exact absurd hlen (Nat.not_lt.mpr (hmin ρ' hρ'play))

/-- **THE NO-STRADDLE FORM.** -/
theorem noStraddlingBracket_of_uncover (h : UncoverResidual) :
    StradKit.NoStraddlingBracket :=
  StradKit.noStraddlingBracket_of_landingResidual (landingResidual_of_uncover h)

/-- **THE RESIDUAL IS EXACT (converse).**  `LandingResidual` makes the
antecedent of `UncoverResidual` vacuous. -/
theorem uncoverResidual_of_landingResidual (hl : StradKit.LandingResidual) :
    UncoverResidual := by
  intro u v ρ F left right c d b pre post tail hs hrf bz α β hpre hland
  obtain ⟨q, hq, hqland⟩ := hland
  exact absurd hqland
    (hl u v ρ F left right c d b pre post tail hs hrf bz α β hpre q hq)

/-- **`UncoverResidual` IS `LandingResidual`.**  The net-zero form of the
residual loses nothing: each implies the other. -/
theorem uncoverResidual_iff_landingResidual :
    UncoverResidual ↔ StradKit.LandingResidual :=
  ⟨landingResidual_of_uncover, uncoverResidual_of_landingResidual⟩

/-- **THE PIN FROM THE TWO RESIDUALS.**  `UncoverResidual` (this card) plus
`StradKit.NoTwinPullOfRaise` (the cross-twin half, untouched) give the
campaign's one-sided clause. -/
theorem splitTwinRungGe_of_uncover_twin
    (h : UncoverResidual) (htwin : StradKit.NoTwinPullOfRaise)
    (hms : ∀ (u v : State) (ρ : List Move) (F : State) (left right : List Move)
      (c d : Card) (b : Base) (pre post tail : List Move),
      SplitKit.SplitHyp u v ρ F left right c d b pre post tail →
      MountainKit.MountainSplit left right)
    (hb : SplitKit.SplitBlock) : PairRungKit.SplitTwinRungGe :=
  StradKit.splitTwinRungGe_of_landing_twin (landingResidual_of_uncover h) htwin hms hb

/-! ## §3. The adjacent instance: the net-zero pair at play level -/

/-- **THE ADJACENT NET-ZERO PAIR SHORTENS.**  A play in which `x` is slid onto
`d` and immediately slid off again is replaced by the single slide, strictly
shorter, with the same endpoint.  (`hstep0` is the direct step, which
`LandRes.slideSt_slideSt_self` identifies with the endpoint of the pair.) -/
theorem slide_pair_shortens
    {G W s2 : State} {x d : Card} {b'' : Base} {tail : List Move}
    (hrev0 : reversibleAtW G (Move.tabToTab x b''))
    (hstep0 : State.step G (Move.tabToTab x b'') = some s2)
    (hrest : ShufflePlayW s2 tail W) :
    ∃ ρ' : List Move, ShufflePlayW G ρ' W ∧
      ρ'.length < (Move.tabToTab x (Sum.inr d) ::
        Move.tabToTab x b'' :: tail).length := by
  refine ⟨Move.tabToTab x b'' :: tail, Walk.cons hrev0 hstep0 hrest, ?_⟩
  simp only [List.length_cons]
  omega

/-- The same with an arbitrary prefix, which is how it is used inside the
straddle package. -/
theorem slide_pair_shortens_prefix
    {u G W s2 : State} {α : List Move} {x d : Card} {b'' : Base} {tail : List Move}
    (hα : ShufflePlayW u α G)
    (hrev0 : reversibleAtW G (Move.tabToTab x b''))
    (hstep0 : State.step G (Move.tabToTab x b'') = some s2)
    (hrest : ShufflePlayW s2 tail W) :
    ∃ ρ' : List Move, ShufflePlayW u ρ' W ∧
      ρ'.length < (α ++ Move.tabToTab x (Sum.inr d) ::
        Move.tabToTab x b'' :: tail).length := by
  refine ⟨α ++ Move.tabToTab x b'' :: tail,
    ShufflePlayW_append hα (Walk.cons hrev0 hstep0 hrest), ?_⟩
  simp only [List.length_append, List.length_cons]
  omega

/-! ## §4. Battery -/

#print axioms LandRes.interior_not_raise
#print axioms LandRes.landingResidual_of_uncover
#print axioms LandRes.uncoverResidual_of_landingResidual
#print axioms LandRes.uncoverResidual_iff_landingResidual
#print axioms LandRes.noStraddlingBracket_of_uncover
#print axioms LandRes.splitTwinRungGe_of_uncover_twin
#print axioms LandRes.slide_pair_shortens
#print axioms LandRes.slide_pair_shortens_prefix

end LandRes
