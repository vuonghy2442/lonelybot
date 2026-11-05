import Orig2.Fiber.ArmFiber
import Orig2.Fork.Class.CeilingBridge

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# Orig2.ArmSplit — the arm-dichotomy split and the forkless-normal route

THE ARM RESIDUE'S EXACT DECOMPOSITION.  `ArmDichotomy`
(`Orig2/Substrate/Vocab.lean`) splits into two independently attackable halves:

* `SatDifferFork` — differing-rung saturated class-mates force a fork
  (the campaign's existing residue);
* `SatEqualFork` — equal-rung saturated class-mates are one cargo fiber
  or the class contains a fork (the `vcS/vcT` half).

`armDichotomy_iff_split` proves the split constructively.  NOTE: the cargo
`ArmDichotomy` is FALSE, refuted by the draw counterexample
(`Orig2/Boundary.lean`, `armDichotomy_draw_false`); the flat-fiber repair
`ArmDichotomySW` is the live target (`Orig2/Fiber/SWDichotomy.lean`).  This
card records the draw obstruction — `BareCargoEquiv` fixes `stock`/`waste`,
so a reversible draw can connect different cargo fibers — and keeps the
generic `ArmDichotomyFor R` split that the SW repair uses.

House compliance: additive leaf (`Orig2.ArmFiber` for the fiber/arm
rows, `Orig2.CeilingBridge` for the forkless rung agreement); the split
itself is constructive; zero `sorry`.
-/

/-! ## §1. The equal-rung half and the split -/

/-- The rung-mismatch existential is decidable by the four-suit
enumeration — no `Fintype`/`Classical` machinery.  PUBLIC since the
2026-10-31 shared-kit strike (SWDichotomy's local copy struck; the
`by_cases` cites resolve to this instance through the import). -/
instance instDecidableExistsRungNe (u v : State) :
    Decidable (∃ σ : Suit, rungAt u σ ≠ rungAt v σ) :=
  decidable_of_iff
    (rungAt u .spade ≠ rungAt v .spade ∨
     rungAt u .heart ≠ rungAt v .heart ∨
     rungAt u .diamond ≠ rungAt v .diamond ∨
     rungAt u .club ≠ rungAt v .club)
    (by
      constructor
      · rintro (h | h | h | h)
        · exact ⟨.spade, h⟩
        · exact ⟨.heart, h⟩
        · exact ⟨.diamond, h⟩
        · exact ⟨.club, h⟩
      · rintro ⟨σ, hσ⟩
        cases σ
        · exact Or.inl hσ
        · exact Or.inr (Or.inl hσ)
        · exact Or.inr (Or.inr (Or.inl hσ))
        · exact Or.inr (Or.inr (Or.inr hσ)))

/-- The decidable mismatch's complement is the pointwise ledger
equality.  This is the only place the split needs the enumeration. -/
theorem rungEq_of_no_differing {u v : State}
    (h : ¬ ∃ σ : Suit, rungAt u σ ≠ rungAt v σ) :
    ∀ σ : Suit, rungAt u σ = rungAt v σ := by
  intro σ
  by_cases hσ : rungAt u σ = rungAt v σ
  · exact hσ
  · exact absurd ⟨σ, hσ⟩ h

/-- **THE GENERIC SPLIT** — for any subrelation `R` that pins the rung
vector, the arm residue at `R` is the conjunction of the differing-rung
residue and the `R` equal-rung half.  Constructive: the case split is on
the decidable rung-mismatch existential.  FACTORED 2026-10-31 out of the
two instance proofs (`armDichotomy_iff_split` here, `armDichotomySW_iff_split`
at `Orig2/Fiber/SWDichotomy.lean`) — one body, the instances are one-line
delegates supplying their rung pin. -/
theorem armDichotomyFor_iff_split {R : State → State → Prop}
    (hrung : ∀ {u v : State}, R u v → RungEq u v) :
    ArmDichotomyFor R ↔ SatDifferFork ∧ SatEqualFor R := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro u v hu hv horb hdiff
      rcases h u v hu hv horb with hR | hfork
      · obtain ⟨σ, hσ⟩ := hdiff
        exact absurd (hrung hR σ) hσ
      · exact hfork
    · intro u v hu hv horb _hrung
      exact h u v hu hv horb
  · rintro ⟨hD, hE⟩
    intro u v hu hv horb
    by_cases hdiff : ∃ σ : Suit, rungAt u σ ≠ rungAt v σ
    · exact Or.inr (hD u v hu hv horb hdiff)
    · exact hE u v hu hv horb (rungEq_of_no_differing hdiff)

/-- **THE EXACT SPLIT** — the arm residue is the conjunction of the
differing-rung residue and the equal-rung half.  A one-line delegate to
the generic split at the cargo instance (since 2026-10-31; the body
lives at `armDichotomyFor_iff_split`, the cargo rung pin at
`bareCargo_rungs`, `Orig2/Fiber/ArmFiber.lean`). -/
theorem armDichotomy_iff_split :
    ArmDichotomy ↔ SatDifferFork ∧ SatEqualFork :=
  armDichotomyFor_iff_split bareCargo_rungs

/-- The equal-rung half follows from the full residue. -/
theorem satEqualFork_of_armDichotomy (h : ArmDichotomy) : SatEqualFork :=
  (armDichotomy_iff_split.mp h).2

/-- A `ForkWitness` is a `forkState`. -/
theorem forkWitness_forkState {F : State} {x : Card} (h : ForkWitness F x) :
    forkState F :=
  forkState_iff.mpr ⟨x, h⟩

/-! ## §2. The draw obstruction

`CargoLeg` is a `tabToTab` step, and `tabToTab` never touches the stock
or the waste.  Hence a `BareCargoEquiv` pair agrees on both zones.  A
reversible draw, by contrast, moves a card between them, so an orbit
pair differing by a reversible draw can never be `BareCargoEquiv`.  The
draw-free probes hide this; any full normalization statement must either
exclude draws (`NoDrawPlayW`/`SWRotW`) or quotient by `Position`. -/

theorem cargoLeg_stock {a b : State} (h : CargoLeg a b) : a.stock = b.stock := by
  obtain ⟨c, bs, hstep, _hrev⟩ := h
  obtain ⟨a0, _hhold, _hcp, _hfr, hs⟩ := step_tabToTab_inv hstep
  rw [hs, putRun_stock, setPile_stock]

theorem cargoLeg_waste {a b : State} (h : CargoLeg a b) : a.waste = b.waste := by
  obtain ⟨c, bs, hstep, _hrev⟩ := h
  obtain ⟨a0, _hhold, _hcp, _hfr, hs⟩ := step_tabToTab_inv hstep
  rw [hs, putRun_waste, setPile_waste]

theorem cargoPath_stock {a b : State} (h : CargoPath a b) : a.stock = b.stock := by
  induction h with
  | refl _ => rfl
  | cons hleg _ ih => exact (cargoLeg_stock hleg).trans ih

theorem cargoPath_waste {a b : State} (h : CargoPath a b) : a.waste = b.waste := by
  induction h with
  | refl _ => rfl
  | cons hleg _ ih => exact (cargoLeg_waste hleg).trans ih

theorem bareCargo_stock {a b : State} (h : BareCargoEquiv a b) :
    a.stock = b.stock :=
  cargoPath_stock h.1

theorem bareCargo_waste {a b : State} (h : BareCargoEquiv a b) :
    a.waste = b.waste :=
  cargoPath_waste h.1

/-- A stock difference refutes the cargo fiber outright. -/
theorem not_bareCargo_of_stock_ne {a b : State} (h : a.stock ≠ b.stock) :
    ¬ BareCargoEquiv a b :=
  fun hbc => h (bareCargo_stock hbc)

/-- A waste difference refutes the cargo fiber outright. -/
theorem not_bareCargo_of_waste_ne {a b : State} (h : a.waste ≠ b.waste) :
    ¬ BareCargoEquiv a b :=
  fun hbc => h (bareCargo_waste hbc)

/-! ## §3. Audit battery -/

#print axioms rungEq_of_no_differing
#print axioms armDichotomyFor_iff_split
#print axioms armDichotomy_iff_split
#print axioms satEqualFork_of_armDichotomy
#print axioms cargoLeg_stock
#print axioms cargoLeg_waste
#print axioms cargoPath_stock
#print axioms cargoPath_waste
#print axioms bareCargo_stock
#print axioms bareCargo_waste
#print axioms not_bareCargo_of_stock_ne