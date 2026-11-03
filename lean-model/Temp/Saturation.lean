import Orig2.Fork.Class.ForkRaiseReorderProof
import Orig2.Fork.Split.ForkDrainInduction

set_option autoImplicit false

/-!
# Saturation exists, unconditionally

A `WF` state is driven to an `SSaturated` class-mate by a `raiseS`-only
licensed play (`RaiseSSeqLicensed`: a reversible cargo slide-star followed by a
licensed raise, repeated).  Every letter climbs the rank sum by exactly one
(`Drain.rungSum_tabToFound`), the rank sum is at most `52`
(`Drain.rungSum_le_52`), so the recursion terminates on `52 - rungSum`.

The result is stated in the strong, path-carrying form
(`saturation_exists_strong`): the endpoint is reached by an actual
`RaiseSSeqLicensed` word, so the consumer can read both the orbit relation and
the rung domination off the play.  `saturation_exists` is the projection asked
for by the join assembly.

No `Classical`, no `noncomputable`.  The only search is the decidable
saturation test: the pre-existing certified probe `rankSatB` (a `Bool` census,
`rankSatB_iff`) and `Drain.exists_of_all_false`, the constructive witness
extractor from a failed `List.all` (the core `List.all_eq_false` would drag
`Classical.choice`).  The raisable card is then *eliminated* from the failed
probe, and the next state comes from `RaiseStepS`'s firing lemma.
-/

namespace OneColourClosure

/-- The well-founded recursion on `52 - rungSum`. -/
theorem saturation_aux (n : Nat) :
    ∀ s : State, s.WF → 52 - Drain.rungSum s ≤ n →
      ∃ ws z, RaiseSSeqLicensed s ws z ∧ SSaturated z ∧
        ∀ σ : Suit, rungAt s σ ≤ rungAt z σ := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro s hs hle
    -- decidability of saturation, from the certified Bool census
    have hiff : rankSatB 12 s = true ↔ SSaturated s := by
      rw [rankSatB_iff hs 12]
      constructor
      · intro h c
        exact h c (by have := Rank.toIdx_lt c.rank; omega)
      · intro h c _
        exact h c
    haveI : Decidable (SSaturated s) :=
      decidable_of_iff (rankSatB 12 s = true) hiff
    by_cases hsat : SSaturated s
    · exact ⟨[], s, RaiseSSeqLicensed.nil s, hsat, fun σ => Nat.le_refl _⟩
    · -- saturation fails: read a raisable card off the failed probe
      have hb : rankSatB 12 s = false := by
        cases h : rankSatB 12 s with
        | false => rfl
        | true => exact absurd (hiff.mp h) hsat
      have hb' : Card.universe.all
          (fun c => !(decide (c.rank.toIdx ≤ 12) && canRaiseSB s c)) = false := by
        simpa only [rankSatB] using hb
      obtain ⟨c, -, hcf⟩ := Drain.exists_of_all_false hb'
      have h2 : (decide (c.rank.toIdx ≤ 12) && canRaiseSB s c) = true := by
        cases h : (decide (c.rank.toIdx ≤ 12) && canRaiseSB s c) with
        | false => rw [h] at hcf; exact absurd hcf (by simp)
        | true => rfl
      have hcb : canRaiseSB s c = true := (Bool.and_eq_true_iff.mp h2).2
      have hcs : CanRaiseS s c := (canRaiseSB_iff hs).mp hcb
      -- one licensed letter: slide-star, then the raise
      obtain ⟨z, hpath, hcan⟩ := hcs
      obtain ⟨z', hstep⟩ := step_tabToFound_of_canRaise hcan
      have hletter : RaiseSSeqLicensed s [c] z' :=
        RaiseSSeqLicensed.cons (RaiseSSeqLicensed.nil s) ⟨z, hpath, hcan⟩ hpath hstep
      have hz'wf : z'.WF := RaiseSSeqLicensed.wf hletter hs
      -- the letter climbs the rank sum by exactly one
      have hsumPath : Drain.rungSum z = Drain.rungSum s := by
        unfold Drain.rungSum
        congr 1
        apply List.map_congr_left
        intro σ _
        exact (rungAt_cargoPath hpath σ).symm
      have hsumStep : Drain.rungSum z' = Drain.rungSum z + 1 :=
        Drain.rungSum_tabToFound hstep
      have hlt : 52 - Drain.rungSum z' < 52 - Drain.rungSum s := by
        have h1 := Drain.rungSum_le_52 hz'wf
        have h2' := Drain.rungSum_le_52 hs
        omega
      obtain ⟨ws, w, hpath2, hsat2, hr2⟩ :=
        ih (52 - Drain.rungSum z') (Nat.lt_of_lt_of_le hlt hle) z' hz'wf
          (Nat.le_refl _)
      refine ⟨ws ++ [c], w, RaiseSSeqLicensed.append hletter hpath2, hsat2,
        fun σ => ?_⟩
      refine Nat.le_trans ?_ (hr2 σ)
      have h := RaiseSSeqLicensed.rungAt_eq hletter σ
      omega

/-- **The strong saturation statement**: a `raiseS`-licensed word reaches an
`SSaturated` state at or above the start's rungs. -/
theorem saturation_exists_strong :
    ∀ s : State, s.WF → ∃ ws z, RaiseSSeqLicensed s ws z ∧ SSaturated z ∧
      ∀ σ : Suit, rungAt s σ ≤ rungAt z σ := by
  intro s hs
  exact saturation_aux (52 - Drain.rungSum s) s hs (Nat.le_refl _)

/-- **Saturation exists, unconditionally.**  Every `WF` state has an
`SSaturated` class-mate whose rungs dominate it. -/
theorem saturation_exists :
    ∀ s : State, s.WF → ∃ u, sameOrbitSetoid.r s u ∧ SSaturated u ∧
      ∀ σ : Suit, rungAt s σ ≤ rungAt u σ := by
  intro s hs
  obtain ⟨ws, u, hpath, hsat, hr⟩ := saturation_exists_strong s hs
  exact ⟨u, RevEqW_symm (RaiseSSeqLicensed.revEqW hpath hs), hsat, hr⟩

end OneColourClosure

#print axioms OneColourClosure.saturation_exists_strong
#print axioms OneColourClosure.saturation_exists
