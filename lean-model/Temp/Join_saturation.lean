import Orig2.Fork.Class.ForkOneColourClosure
import Orig2.Fiber.FreeOrbit

set_option autoImplicit false

/-!
# The constructive assembly: saturation + the residue

`FullJoinAtLeastOrFork` restated so that **nothing is decided by search** and no
class-wide predicate is branched on.

* Saturation is an `∃`-statement, proved by induction on the measure `Σ rungAt`
  (each raise founds one card), never by enumerating `Card.universe`.
* The residue `SatDifferForkWF` *produces* a fork witness; the witness is
  extracted from the data, not searched for.
* The only case splits below are on `Nat` equalities of rung values — decidable
  data.  In particular there is no `Decidable (Fork u)` and no `Forkless`.

The single unproved ingredient is the inline saturation hypothesis.
-/

namespace OneColourClosure

/-- **`FullJoinAtLeastOrFork` from saturation + the residue.** -/
theorem fullJoinAtLeastOrFork_of_saturation
    (hsat : ∀ s : State, s.WF →
      ∃ u, sameOrbitSetoid.r s u ∧ SSaturated u ∧ ∀ σ : Suit, rungAt s σ ≤ rungAt u σ)
    (hres : SatDifferForkWF) :
    FullJoinAtLeastOrFork := by
  intro s s' hs hs' hcls
  obtain ⟨u, hsu, hsu_sat, hsu_r⟩ := hsat s hs
  obtain ⟨v, hsv, hsv_sat, hsv_r⟩ := hsat s' hs'
  have hu_wf : u.WF := by
    obtain ⟨ρ, -, τ, hτ⟩ := hsu
    exact walk_wf hs hτ
  have hv_wf : v.WF := by
    obtain ⟨ρ, -, τ, hτ⟩ := hsv
    exact walk_wf hs' hτ
  have huv : sameOrbitSetoid.r u v :=
    RevEqW_trans hsv (RevEqW_trans hcls (RevEqW_symm hsu))
  -- the fork branch: the residue produces the witness, the class lift is definitional
  have key : (∃ σ : Suit, rungAt u σ ≠ rungAt v σ) → Fork s := by
    rintro ⟨σ, hσ⟩
    obtain ⟨F, x, hF, hwit⟩ := hres u v hu_wf hsu_sat hsv_sat huv ⟨σ, hσ⟩
    exact ⟨F, x, RevEqW_trans hF hsu, hwit⟩
  -- four-way split on decidable `Nat` data (no `Decidable (Fork s)`)
  by_cases h1 : rungAt u Suit.spade = rungAt v Suit.spade
  · by_cases h2 : rungAt u Suit.heart = rungAt v Suit.heart
    · by_cases h3 : rungAt u Suit.diamond = rungAt v Suit.diamond
      · by_cases h4 : rungAt u Suit.club = rungAt v Suit.club
        · -- rungs agree: the saturated class-mate is the join
          have hEq : ∀ σ : Suit, rungAt u σ = rungAt v σ := by
            intro σ
            cases σ <;> assumption
          refine Or.inl ⟨u, hsu, fun σ => ?_⟩
          exact Nat.max_le.mpr ⟨hsu_r σ, by rw [hEq σ]; exact hsv_r σ⟩
        · exact Or.inr (key ⟨Suit.club, h4⟩)
      · exact Or.inr (key ⟨Suit.diamond, h3⟩)
    · exact Or.inr (key ⟨Suit.heart, h2⟩)
  · exact Or.inr (key ⟨Suit.spade, h1⟩)

/-- The same, as a data-carrying disjunction: the proof returns either the join
witness or an explicit fork witness. -/
theorem fullJoinAtLeast_or_forkWitness_of_saturation
    (hsat : ∀ s : State, s.WF →
      ∃ u, sameOrbitSetoid.r s u ∧ SSaturated u ∧ ∀ σ : Suit, rungAt s σ ≤ rungAt u σ)
    (hres : SatDifferForkWF) :
    ∀ s s', s.WF → s'.WF → sameOrbitSetoid.r s s' →
      (∃ w, FullJoinAtLeast s s' w) ∨
      (∃ F x, sameOrbitSetoid.r s F ∧ ForkWitness F x) := by
  intro s s' hs hs' hcls
  rcases fullJoinAtLeastOrFork_of_saturation hsat hres s s' hs hs' hcls with
    hjoin | hfork
  · exact Or.inl hjoin
  · exact Or.inr hfork

end OneColourClosure

#print axioms OneColourClosure.fullJoinAtLeastOrFork_of_saturation
#print axioms OneColourClosure.fullJoinAtLeast_or_forkWitness_of_saturation
