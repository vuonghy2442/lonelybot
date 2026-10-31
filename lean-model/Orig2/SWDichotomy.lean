import Orig2.ArmSplit
import Orig2.Boundary

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

/-!
# Orig2.SWDichotomy — the flat-fiber arm dichotomy

THE DRAW REPAIR AT THE FIBER LEVEL.  `BareCargoEquiv` fixes `stock` and
`waste`, so it cannot absorb the SW (stock–waste) draw cycle.  The
correct first branch is the **flat fiber**:

```lean
BareFlatEquiv u v := FlatPath u v ∧ FlatPath v u
```

`FlatStep` is exactly the two reversible letters — `tabToTab` (cargo)
and `draw` — so `BareFlatEquiv` is the two-way closure of the flat
alphabet, i.e. “allow draw + tabToTab in any order”.  The quotient
hierarchy is:

```text
BareCargoEquiv  ⊂  BareFlatEquiv  ⊂  sameOrbitSetoid
(cargo slides)     (+ draws)          (+ raises/pulls)
```

The SW interpretation is exactly `BareFlatEquiv`; there is no separate
alias.  The dichotomy instances are `ArmDichotomySW` and
`SatEqualCargoSW` in the registry.

The card defines `ArmDichotomySW` and `SatEqualCargoSW`, proves the
split, and shows the draw counterexample of `Orig2/Boundary.lean` is
a POSITIVE flat-fiber instance.  It also proves the campaign theorem
from `ArmDichotomySW`: forkless saturated class-mates share their
`found` tuple.

House compliance: additive leaf (`Orig2.ArmSplit`,
`Orig2.Boundary`); zero `sorry`, zero `Classical.choice` (the
split's case analysis uses a four-suit decidable enumeration); battery
at tail.
-/

/-! ## §1. The flat fiber -/


/-- The flat fiber is reflexive. -/
theorem bareFlatEquiv_refl (u : State) : BareFlatEquiv u u :=
  ⟨Steps.refl u, Steps.refl u⟩

/-- The flat fiber is symmetric. -/
theorem bareFlatEquiv_symm {u v : State} (h : BareFlatEquiv u v) :
    BareFlatEquiv v u :=
  ⟨h.2, h.1⟩

/-- The flat fiber is transitive. -/
theorem bareFlatEquiv_trans {a b c : State}
    (h1 : BareFlatEquiv a b) (h2 : BareFlatEquiv b c) :
    BareFlatEquiv a c :=
  ⟨steps_trans h1.1 h2.1, steps_trans h2.2 h1.2⟩

/-- Cargo is a flat-fiber subrelation. -/
theorem bareCargo_bareFlat {u v : State} (h : BareCargoEquiv u v) :
    BareFlatEquiv u v :=
  ⟨cargoPath_flatPath h.1, cargoPath_flatPath h.2⟩


/-! ## §2. Flat invariance -/

/-- A flat path realizes as a witness shuffle (both flat letters carry
`reversibleAtW`). -/
theorem flatPath_shuffle {a b : State} (h : FlatPath a b) :
    ∃ play, ShufflePlayW a play b := by
  induction h with
  | refl s => exact ⟨[], Walk.nil s⟩
  | cons hstep _ ih =>
      obtain ⟨play, hplay⟩ := ih
      cases hstep with
      | cargo c b hstep hrev =>
          exact ⟨Move.tabToTab c b :: play, Walk.cons hrev hstep hplay⟩
      | draw hstep hrev =>
          exact ⟨Move.draw :: play, Walk.cons hrev hstep hplay⟩

/-- The flat fiber is a witness equivalence. -/
theorem bareFlat_revEqW {u v : State} (h : BareFlatEquiv u v) : RevEqW u v := by
  obtain ⟨h1, h2⟩ := h
  obtain ⟨p, hp⟩ := flatPath_shuffle h1
  obtain ⟨q, hq⟩ := flatPath_shuffle h2
  exact ⟨p, hp, q, hq⟩

/-- The flat fiber is a class membership. -/
theorem bareFlat_sameOrbit {u v : State} (h : BareFlatEquiv u v) :
    sameOrbitSetoid.r u v :=
  RevEqW_symm (bareFlat_revEqW h)

/-- A flat-fiber pair has the same rung vector. -/
theorem bareFlat_rung {u v : State} (h : BareFlatEquiv u v) : RungEq u v :=
  fun σ => rungAt_flatPath h.1 σ

/-- A flat-fiber pair has the same `found` tuple at `WF`. -/
theorem bareFlat_found {u v : State} (hu : u.WF) (hv : v.WF)
    (h : BareFlatEquiv u v) : u.found = v.found := by
  funext σ
  exact found_congr_of_rungs hu hv (bareFlat_rung h σ)


/-! ## §3. The corrected dichotomy -/


/- The rung-mismatch decidability instance is ArmSplit's public
`instDecidableExistsRungNe` since the 2026-10-31 shared-kit strike —
the local copy (a documented "local copy of Orig2/ArmSplit.lean's
instance") is struck; the split's `by_cases` resolves through the
import. -/

/-- **THE SW SPLIT** — the flat-fiber dichotomy is the conjunction of
the differing-rung residue and the equal-rung flat-fiber half.  A
one-line delegate to the generic split at the flat instance (since
2026-10-31; the body lives at `armDichotomyFor_iff_split`,
`Orig2/ArmSplit.lean`, the flat rung pin at `bareFlat_rung`). -/
theorem armDichotomySW_iff_split :
    ArmDichotomySW ↔ SatDifferFork ∧ SatEqualCargoSW :=
  armDichotomyFor_iff_split bareFlat_rung

/-- **THE FLAT DICHOTOMY IMPLIES THE RUNG REPAIR.** -/
theorem armDichotomyRung_of_SW (h : ArmDichotomySW) : ArmDichotomyRung := by
  intro u v hu hv horb
  rcases h u v hu hv horb with hcs | hfork
  · exact Or.inl (bareFlat_rung hcs)
  · exact Or.inr hfork

/-- The flat dichotomy implies the campaign residue. -/
theorem armDichotomySW_to_satDifferFork (h : ArmDichotomySW) : SatDifferFork :=
  armDichotomyRung_iff_satDifferFork.mp (armDichotomyRung_of_SW h)

/-- **THE CAMPAIGN THEOREM FROM THE FLAT DICHOTOMY** — in a forkless
class, two saturated class-mates share the `found` tuple. -/
theorem forkless_found_unique_SW (h : ArmDichotomySW) {s s' : State}
    (hwf : s.WF) (hwf' : s'.WF)
    (hclass : sameOrbitSetoid.r s s')
    (hfrk : ∀ u, sameOrbitSetoid.r s u → ¬ forkState u)
    (hsat : SSaturated s) (hsat' : SSaturated s') :
    s.found = s'.found := by
  rcases h s s' hsat hsat' hclass with hcs | ⟨F, x, hF, hfx⟩
  · exact bareFlat_found hwf hwf' hcs
  · exact absurd (forkState_iff.mpr ⟨x, hfx⟩) (hfrk F hF)


/-! ## §4. Audit battery -/

#print axioms bareFlatEquiv_refl
#print axioms bareFlatEquiv_trans
#print axioms bareCargo_bareFlat
#print axioms flatPath_shuffle
#print axioms bareFlat_sameOrbit
#print axioms bareFlat_rung
#print axioms bareFlat_found
#print axioms armDichotomySW_iff_split
#print axioms armDichotomyRung_of_SW
#print axioms armDichotomySW_to_satDifferFork
#print axioms forkless_found_unique_SW