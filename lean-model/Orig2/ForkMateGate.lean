import Orig2.ForkGatedTower
import Orig2.ForkNoMate

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option linter.unusedVariables false

/-!
# Orig2/ForkMateGate — the `MateRaiseFree` residual: probe reduction, gate decomposition

READ-ONLY scratch (no source edit, no commit).  Zero `sorry`, zero
`Classical.choice`, zero `native_decide`; axiom battery at the tail.

## What this card establishes

1. **Canonical splits.**  Under `MountainSplit left right` a `SplitHyp`'s split
   is *canonical*: `left` is raise-free, `post` is free, `right` is pull-free,
   so `pull c b` is the **last** pull of the whole play and every raise of the
   play sits in `right`.  (This is what makes the probe
   `Temp/Mate_probe.py` exhaustive: it only inspects the first-raise /
   last-pull split of each shortest play.)

2. **The equal-rung corner is a self-bracket of the split card.**  If the two
   endpoints have the SAME rung vector, then at any `MountainSplit` split the
   pull card `c` is **raised again in the right leg**
   (`raise_c_mem_right_of_equalRung`).  Proof is the rung ledger: the pull of
   `c` is in `left`, so `pullsOf left c.suit ≥ 1`, and the mountain accounting
   makes `raisesOf right c.suit = pullsOf left c.suit`; a positive raise count
   of `c.suit` over a pull-free leg is `raise c` itself
   (`Direct.sigma_raise_of_raise_e_mem`).

   So the equal-rung stratum carries exactly the `pull c ; … ; raise c`
   bracket shape — the mechanism `Orig2/ForkPermRefute.lean` shows is *not*
   forbidden by minimality in general.

3. **The gate decomposition (the exact smaller residual).**  The un-gated
   `Direct.MateRaiseFree` is *literally* the conjunction

       Gated.MateRaiseFreeDiffering  ∧  EqualRungMateRaiseFree

   (`mateRaiseFree_iff_differing_and_equalRung`); and the extra content is
   vacuous once no equal-rung `MountainSplit` exists
   (`mateRaiseFree_iff_differing_of_noEqualRung`).  Since
   `Gated.MateRaiseFreeDiffering ↔ Gated.LandingThirdSuitFreeDiffering`
   (`Gated.mateRaiseFreeDiffering_iff_containmentDiffering`), the gated form is
   not a new residual: it is the gated containment.

4. **Verdict on the un-gated form.**  `Direct.MateRaiseFree` is *implied* by
   the containment with no mountain hypothesis at all
   (`NoMate.mateRaiseFree_of_containment`), so it cannot be strictly smaller
   than `LandingThirdSuitFree`; and the containment is on the critical path
   while `MateRaiseFree` itself is not cited by `ForkFrontier`/`ForkMtnExists`.
-/

namespace MateGate

open ValleyElim

/-! ## §1. Canonical-split facts under `MountainSplit` -/

/-- A free letter is never a pull. -/
theorem not_isPull_of_freeMove {m : Move} (h : ValleyElim.FreeMove m) :
    ¬ Bubble.IsPull m := by
  rintro ⟨c, b, hc⟩
  rcases h with h | ⟨c', b', h'⟩
  · rw [h] at hc; cases hc
  · rw [h'] at hc; cases hc

/-- A free letter is never a raise. -/
theorem not_isRaise_of_freeMove {m : Move} (h : ValleyElim.FreeMove m) :
    ¬ Bubble.IsRaise m := by
  rintro ⟨c, hc⟩
  rcases h with h | ⟨c', b', h'⟩
  · rw [h] at hc; cases hc
  · rw [h'] at hc; cases hc

/-- **NOTHING AFTER THE SPLIT IS A PULL.**  The free tail `post` and the frozen
right leg `right` are both pull-free. -/
theorem no_pull_in_post_right
    {u v : State} {ρ : List Move} {F : State} {left right : List Move}
    {c d : Card} {b : Base} {pre post tail : List Move}
    (hs : SplitKit.SplitHyp u v ρ F left right c d b pre post tail)
    (hms : MountainKit.MountainSplit left right) :
    ∀ m ∈ post ++ right, ¬ Bubble.IsPull m := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hfree, -⟩ := hs
  intro m hm
  rcases List.mem_append.mp hm with hp | hr
  · exact not_isPull_of_freeMove (hfree m hp)
  · exact hms.2 m hr

/-- **`pull c b` IS THE LAST PULL OF THE PLAY.**  Any pull in `ρ` either lies
in `pre` or *is* the split's own pull. -/
theorem pull_mem_pre_or_eq
    {u v : State} {ρ : List Move} {F : State} {left right : List Move}
    {c d : Card} {b : Base} {pre post tail : List Move}
    (hs : SplitKit.SplitHyp u v ρ F left right c d b pre post tail)
    (hms : MountainKit.MountainSplit left right)
    {c' : Card} {b' : Base} (hmem : Move.foundToTab c' b' ∈ ρ) :
    Move.foundToTab c' b' ∈ pre ∨ (c' = c ∧ b' = b) := by
  have hsk := hs
  obtain ⟨-, -, -, -, -, -, hρ, -, -, hshape, -, hrightShape⟩ := hs
  have hρ' : ρ = pre ++ Move.foundToTab c b :: (post ++ right) := by
    rw [hρ, hshape, hrightShape]
    simp only [List.cons_append, List.append_assoc]
  rw [hρ'] at hmem
  rcases List.mem_append.mp hmem with h1 | h1
  · exact Or.inl h1
  · rcases List.mem_cons.mp h1 with h2 | h2
    · injection h2 with hc hb
      exact Or.inr ⟨hc, hb⟩
    · exact absurd ⟨c', b', rfl⟩ (no_pull_in_post_right hsk hms _ h2)

/-- **EVERY RAISE OF THE PLAY IS IN THE RIGHT LEG.**  `left` is raise-free. -/
theorem raise_mem_right_of_mem
    {u v : State} {ρ : List Move} {F : State} {left right : List Move}
    {c d : Card} {b : Base} {pre post tail : List Move}
    (hs : SplitKit.SplitHyp u v ρ F left right c d b pre post tail)
    (hms : MountainKit.MountainSplit left right)
    {x : Card} (hmem : Move.tabToFound x ∈ ρ) :
    Move.tabToFound x ∈ right := by
  obtain ⟨-, -, -, -, -, -, hρ, -, -, -, -, -⟩ := hs
  rcases List.mem_append.mp (hρ ▸ hmem) with h1 | h1
  · exact absurd ⟨x, rfl⟩ (hms.1 _ h1)
  · exact h1

/-! ## §2. The equal-rung corner is a self-bracket of the split card -/

/-- **AT EQUAL RUNG VECTORS THE SPLIT CARD IS RAISED IN THE RIGHT LEG.**

The pull of `c` is in `left`, hence `pullsOf left c.suit ≥ 1`.  The mountain
accounting (`pullsOf_eq_sub_of_no_raise` on `left`, `raisesOf_eq_sub_of_no_pull`
on `right`) gives `raisesOf right c.suit = pullsOf left c.suit` once the endpoint
rungs agree, so the right leg raises some card of `c.suit`; over a pull-free leg
starting at rung `c.rank` that card must be `c` itself
(`Direct.sigma_raise_of_raise_e_mem`). -/
theorem raise_c_mem_right_of_equalRung
    {u v : State} {ρ : List Move} {F : State} {left right : List Move}
    {c d : Card} {b : Base} {pre post tail : List Move}
    (heq : ∀ σ : Suit, rungAt u σ = rungAt v σ)
    (hs : SplitKit.SplitHyp u v ρ F left right c d b pre post tail)
    (hms : MountainKit.MountainSplit left right)
    {A' B : State} (hpre : ShufflePlayW u pre A')
    (hstep : State.step A' (Move.foundToTab c b) = some B) :
    Direct.Occurs (Move.tabToFound c) right := by
  have hsk := hs
  obtain ⟨huwf, -, -, -, -, -, -, hleft, hright, hshape, hfree, -⟩ := hs
  have hA' : A'.WF := SatDifferCensus.ShufflePlayW.wf_end hpre huwf
  have hB : B.WF := step_wf hA' hstep
  obtain ⟨hpost, -⟩ := Landing.post_play_of_landing hsk hpre hstep
  have hF : F.WF := SatDifferCensus.ShufflePlayW.wf_end hleft huwf
  have hcanB : CanRaise B c := ValleyStep.pull_card_canRaise hA' hstep
  have hrungB : rungAt B c.suit = c.rank.toIdx :=
    (ThirdLive.rank_eq_rungAt_of_canRaiseS hB (CanRaiseS.now c hcanB)).symm
  have hrungF : rungAt F c.suit = c.rank.toIdx := by
    rw [ValleyElim.rungAt_eq_of_free_play hpost hfree c.suit, hrungB]
  -- the split's own pull of `c` is a `c.suit` pull of `left`
  have hpullmem : Move.foundToTab c b ∈ left := by
    rw [hshape]
    exact List.mem_append_right _ (List.mem_cons_self ..)
  have hposL : 0 < pullsOf left c.suit :=
    LedgerKit.pullsOf_pos_iff.mpr ⟨c, b, rfl, hpullmem⟩
  have haccL : pullsOf left c.suit = rungAt u c.suit - rungAt F c.suit :=
    MountainKit.pullsOf_eq_sub_of_no_raise hleft hms.1
  have haccR : raisesOf right c.suit = rungAt v c.suit - rungAt F c.suit :=
    MountainKit.raisesOf_eq_sub_of_no_pull hright hms.2
  have hposR : 0 < raisesOf right c.suit := by
    rw [haccR, ← heq c.suit, ← haccL]
    exact hposL
  obtain ⟨x, hxs, hxmem⟩ := LedgerKit.raisesOf_pos_iff.mp hposR
  exact Direct.sigma_raise_of_raise_e_mem hright hF hms.2 hrungF
    ⟨x, NoMate.occurs_of_mem hxmem, hxs⟩

/-! ## §3. The gate decomposition -/

/-- **`EqualRungMateRaiseFree`** — the raise-exclusion restricted to endpoints
with the *same* rung vector: precisely the part of `Direct.MateRaiseFree` that
`Gated.MateRaiseFreeDiffering` does not see. -/
def EqualRungMateRaiseFree : Prop :=
  ∀ (u v : State) (ρ : List Move) (F : State)
    (left right : List Move) (c d : Card) (b : Base)
    (pre post tail : List Move),
    (∀ σ : Suit, rungAt u σ = rungAt v σ) →
    SplitKit.SplitHyp u v ρ F left right c d b pre post tail →
    MountainKit.MountainSplit left right →
    ∀ (A' B : State), ShufflePlayW u pre A' →
      State.step A' (Move.foundToTab c b) = some B →
      ∀ e : Card, CanRaiseS B e → e.suit ≠ c.suit → e.suit ≠ c.twin.suit →
        ¬ Direct.Occurs (Move.tabToFound e) right ∧
          ¬ Direct.Occurs (Move.tabToFound e.twin) right

/-- **`NoEqualRungMountainSplit`** — the exact geometric statement that makes
the gate (and hence the un-gated form) equivalent to the gated one: no
`SplitHyp` between equal-rung endpoints carries a `MountainSplit`. -/
def NoEqualRungMountainSplit : Prop :=
  ∀ (u v : State) (ρ : List Move) (F : State)
    (left right : List Move) (c d : Card) (b : Base)
    (pre post tail : List Move),
    (∀ σ : Suit, rungAt u σ = rungAt v σ) →
    SplitKit.SplitHyp u v ρ F left right c d b pre post tail →
    ¬ MountainKit.MountainSplit left right

/-- Rung vectors either differ or agree componentwise.  Constructive (the
decision is on `Nat` equality). -/
theorem rungDiffers_or_equalRung {u v : State} :
    MountainGate.RungDiffers u v ∨ (∀ σ : Suit, rungAt u σ = rungAt v σ) := by
  by_cases h : ∃ σ : Suit, rungAt u σ ≠ rungAt v σ
  · exact Or.inl h
  · refine Or.inr (fun σ => ?_)
    by_cases hσ : rungAt u σ = rungAt v σ
    · exact hσ
    · exact absurd ⟨σ, hσ⟩ h

/-- **THE UN-GATED FORM IS THE GATED FORM PLUS THE EQUAL-RUNG CLAUSE.** -/
theorem mateRaiseFree_iff_differing_and_equalRung :
    Direct.MateRaiseFree ↔
      Gated.MateRaiseFreeDiffering ∧ EqualRungMateRaiseFree := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro u v ρ F left right c d b pre post tail _ hs hms A' B hpre hstep e he h1 h2
      exact h u v ρ F left right c d b pre post tail hs hms A' B hpre hstep e he h1 h2
    · intro u v ρ F left right c d b pre post tail _ hs hms A' B hpre hstep e he h1 h2
      exact h u v ρ F left right c d b pre post tail hs hms A' B hpre hstep e he h1 h2
  · rintro ⟨hd, heeq⟩ u v ρ F left right c d b pre post tail hs hms A' B hpre hstep e he h1 h2
    rcases rungDiffers_or_equalRung (u := u) (v := v) with h | h
    · exact hd u v ρ F left right c d b pre post tail h hs hms A' B hpre hstep e he h1 h2
    · exact heeq u v ρ F left right c d b pre post tail h hs hms A' B hpre hstep e he h1 h2

/-- **THE GATED FORM PLUS NO EQUAL-RUNG MOUNTAIN GIVES THE UN-GATED FORM.** -/
theorem mateRaiseFree_of_differing_of_noEqualRung
    (hd : Gated.MateRaiseFreeDiffering) (he : NoEqualRungMountainSplit) :
    Direct.MateRaiseFree := by
  rw [mateRaiseFree_iff_differing_and_equalRung]
  refine ⟨hd, ?_⟩
  intro u v ρ F left right c d b pre post tail heq hs hms
  exact absurd hms (he u v ρ F left right c d b pre post tail heq hs)

/-- **WITH `NoEqualRungMountainSplit` THE GATE IS FREE.**  The un-gated
`MateRaiseFree` is then *exactly* `Gated.MateRaiseFreeDiffering`. -/
theorem mateRaiseFree_iff_differing_of_noEqualRung
    (he : NoEqualRungMountainSplit) :
    Direct.MateRaiseFree ↔ Gated.MateRaiseFreeDiffering :=
  ⟨fun h => (mateRaiseFree_iff_differing_and_equalRung.mp h).1,
    fun h => mateRaiseFree_of_differing_of_noEqualRung h he⟩

/-- **THE GATED FORM IS THE GATED CONTAINMENT.**  Restatement of
`Gated.mateRaiseFreeDiffering_iff_containmentDiffering`. -/
theorem mateRaiseFreeDiffering_iff_containmentDiffering
    (hmt : MountainGate.MountainAtSplitsDiffering) :
    Gated.MateRaiseFreeDiffering ↔ Gated.LandingThirdSuitFreeDiffering :=
  Gated.mateRaiseFreeDiffering_iff_containmentDiffering hmt

/-- **THE FULL DECOMPOSITION.**  Under the gated mountain, the un-gated
raise-exclusion is the gated *containment* plus the equal-rung clause. -/
theorem mateRaiseFree_iff_gatedContainment_and_equalRung
    (hmt : MountainGate.MountainAtSplitsDiffering) :
    Direct.MateRaiseFree ↔
      Gated.LandingThirdSuitFreeDiffering ∧ EqualRungMateRaiseFree := by
  rw [mateRaiseFree_iff_differing_and_equalRung,
    Gated.mateRaiseFreeDiffering_iff_containmentDiffering hmt]

/-- The equal-rung clause is *free* once the containment holds: the raise
exclusions are vacuous at any third-suit survivor. -/
theorem equalRungMateRaiseFree_of_containment
    (h : Landing.LandingThirdSuitFree) : EqualRungMateRaiseFree := by
  intro u v ρ F left right c d b pre post tail _ hs hms A' B hpre hstep e he h1 h2
  exact ⟨fun _ => h u v ρ F left right c d b pre post tail hs A' B hpre hstep e he h1 h2,
    fun _ => h u v ρ F left right c d b pre post tail hs A' B hpre hstep e he h1 h2⟩

/-- **THE UN-GATED FORM IS IMPLIED BY THE TARGET — NO MOUNTAIN NEEDED.**  So it
cannot be a strictly smaller residual than `LandingThirdSuitFree`. -/
theorem mateRaiseFree_of_containment (h : Landing.LandingThirdSuitFree) :
    Direct.MateRaiseFree :=
  NoMate.mateRaiseFree_of_containment h

end MateGate

/-! ## §4. Axiom battery -/

#print axioms MateGate.not_isPull_of_freeMove
#print axioms MateGate.not_isRaise_of_freeMove
#print axioms MateGate.no_pull_in_post_right
#print axioms MateGate.pull_mem_pre_or_eq
#print axioms MateGate.raise_mem_right_of_mem
#print axioms MateGate.raise_c_mem_right_of_equalRung
#print axioms MateGate.rungDiffers_or_equalRung
#print axioms MateGate.EqualRungMateRaiseFree
#print axioms MateGate.NoEqualRungMountainSplit
#print axioms MateGate.mateRaiseFree_iff_differing_and_equalRung
#print axioms MateGate.mateRaiseFree_of_differing_of_noEqualRung
#print axioms MateGate.mateRaiseFree_iff_differing_of_noEqualRung
#print axioms MateGate.mateRaiseFreeDiffering_iff_containmentDiffering
#print axioms MateGate.mateRaiseFree_iff_gatedContainment_and_equalRung
#print axioms MateGate.equalRungMateRaiseFree_of_containment
#print axioms MateGate.mateRaiseFree_of_containment
