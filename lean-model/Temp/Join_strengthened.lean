import Temp.Join_raiseS
import Temp.Saturation

set_option autoImplicit false

/-!
# The strengthened join from the residue

`FullJoinAtLeastRaiseSOrFork` follows from the ceiling campaign's single
residue `SatDifferForkWF`, with no other input.

The assembly is exactly two saturations plus one elimination:

* saturate `s` to `u` and `s'` to `v` (`saturation_exists_strong`), so both are
  `SSaturated`, both are reached from their starts by a `raiseS`-licensed word,
  and the rungs only climb;
* the two endpoints are class-mates (`RevEqW_trans` of the two paths and
  `sameOrbitSetoid.r s s'`);
* apply `SatDifferForkWF u v`: a fork witness lifts to `Fork s` because the
  class relation is transitive and `Fork` is its existential closure;
* otherwise the rungs agree.  This is read off a four-way split on the *decidable*
  `Nat` equalities, never a `by_cases` on `∃ σ, rungAt u σ ≠ rungAt v σ`
  (that would inject `Classical.choice`);
* in the agreeing branch `w := u` works: `FullJoinAtLeast s s' u` is the two
  saturation inequalities against the equal rungs, `RungReachableAtLeast s u` is
  the saturation path to `u`, and `RungReachableAtLeast s' u` is the saturation
  path to `v` transported across `rungs v = rungs u`.

Nothing here needs `ForklessHasTop`, `ForklessOrFork` or
`ForklessOneColourClosure`: the only class statement consumed is the residue.
-/

namespace OneColourClosure

/-- **The strengthened join-or-fork theorem from the residue.** -/
theorem fullJoinAtLeastRaiseSOrFork_of_residue (hres : SatDifferForkWF) :
    FullJoinAtLeastRaiseSOrFork := by
  intro s s' hs hs' hcls
  obtain ⟨ws, u, hpathu, hsu_sat, hsu_r⟩ := saturation_exists_strong s hs
  obtain ⟨ws', v, hpathv, hsv_sat, hsv_r⟩ := saturation_exists_strong s' hs'
  have hsu : sameOrbitSetoid.r s u :=
    RevEqW_symm (RaiseSSeqLicensed.revEqW hpathu hs)
  have hsv : sameOrbitSetoid.r s' v :=
    RevEqW_symm (RaiseSSeqLicensed.revEqW hpathv hs')
  have hu_wf : u.WF := RaiseSSeqLicensed.wf hpathu hs
  have huv : sameOrbitSetoid.r u v :=
    sameOrbitSetoid.iseqv.trans
      (sameOrbitSetoid.iseqv.trans (sameOrbitSetoid.iseqv.symm hsu) hcls) hsv
  -- the residue's fork branch, lifted to the class of `s`
  have key : (∃ σ : Suit, rungAt u σ ≠ rungAt v σ) → Fork s := by
    rintro ⟨σ, hσ⟩
    obtain ⟨F, x, hF, hwit⟩ := hres u v hu_wf hsu_sat hsv_sat huv ⟨σ, hσ⟩
    exact ⟨F, x, sameOrbitSetoid.iseqv.trans hsu hF, hwit⟩
  -- the only splits are on decidable `Nat` data
  by_cases h1 : rungAt u Suit.spade = rungAt v Suit.spade
  · by_cases h2 : rungAt u Suit.heart = rungAt v Suit.heart
    · by_cases h3 : rungAt u Suit.diamond = rungAt v Suit.diamond
      · by_cases h4 : rungAt u Suit.club = rungAt v Suit.club
        · -- rungs agree: `u` is the join
          have hEq : ∀ σ : Suit, rungAt u σ = rungAt v σ := by
            intro σ
            cases σ <;> assumption
          have hjoin : FullJoinAtLeast s s' u := by
            refine ⟨hsu, fun σ => ?_⟩
            exact Nat.max_le.mpr ⟨hsu_r σ, by rw [hEq σ]; exact hsv_r σ⟩
          refine Or.inl ⟨u, hjoin, ?_, ?_⟩
          · exact ⟨ws, u, hpathu, fun σ => Nat.le_refl _⟩
          · exact ⟨ws', v, hpathv, fun σ => Nat.le_of_eq (hEq σ)⟩
        · exact Or.inr (key ⟨Suit.club, h4⟩)
      · exact Or.inr (key ⟨Suit.diamond, h3⟩)
    · exact Or.inr (key ⟨Suit.heart, h2⟩)
  · exact Or.inr (key ⟨Suit.spade, h1⟩)

end OneColourClosure

#print axioms OneColourClosure.fullJoinAtLeastRaiseSOrFork_of_residue
