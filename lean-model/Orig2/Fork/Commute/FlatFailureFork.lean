import Orig2.Fork.Commute.FlatNormal

set_option autoImplicit false

open OneColourClosure

/-!
# Orig2.Fork.Commute.FlatFailureFork - the explicit-witness form

The class-global explicit-witness companion of
`Orig2/Fork/Commute/FlatNormal.lean`: a saturated same-orbit pair outside the
flat fiber exhibits a `ForkWitness` somewhere in its class.

Constructivity is isolated to one place.  The data extraction
`flat_failure_fork_of_exists_fork` is choice-free, and
`flat_failure_fork_of_decidable` is fully constructive once the class-level
fork existential is decidable.  The unrestricted version needs the classical
`¬∀ → ∃` bridge `classical_exists_fork_of_not_forkless` (via
`Classical.choice` through `Classical.propDecidable`), since neither
`sameOrbitSetoid.r` nor `forkState` carries a decidable instance.
-/

/-- The only classical step: `¬ Forkless u` gives a concrete class fork. -/
theorem classical_exists_fork_of_not_forkless {u : State}
    (h : ¬ Forkless u) :
    ∃ F, sameOrbitSetoid.r u F ∧ forkState F := by
  apply Classical.byContradiction
  intro hcon
  exact h (fun F hF hfs => hcon (Exists.intro F (And.intro hF hfs)))

/-- The constructive core: once the class-global fork existential is
available, the per-card witness is pure unpacking. -/
theorem flat_failure_fork_of_exists_fork
    {u : State} (h : ∃ F, sameOrbitSetoid.r u F ∧ forkState F) :
    ∃ F x, sameOrbitSetoid.r u F ∧ ForkWitness F x := by
  obtain ⟨F, hF, x, hx⟩ := h
  exact ⟨F, x, hF, hx⟩

/-- Fully constructive version, given decidability of the class-level fork
existential. -/
theorem flat_failure_fork_of_decidable
    {u v : State}
    [Decidable (∃ F, sameOrbitSetoid.r u F ∧ forkState F)]
    (hu : u.WF) (hsu : SSaturated u) (hsv : SSaturated v)
    (horb : sameOrbitSetoid.r u v)
    (hnf : ¬ BareFlatEquiv u v) :
    ∃ F x, sameOrbitSetoid.r u F ∧ ForkWitness F x := by
  by_cases hfork : ∃ F, sameOrbitSetoid.r u F ∧ forkState F
  · exact flat_failure_fork_of_exists_fork hfork
  · exfalso
    have hno : Forkless u :=
      fun F hF hfs => hfork ⟨F, hF, hfs⟩
    exact hnf (forklessFlatNormalWF_proved u v hu hsu hsv horb hno)

/-- **`SatFlatFiberFork`, explicit-witness / class-global form.** -/
theorem flat_failure_fork
    {u v : State}
    (hu : u.WF) (hsu : SSaturated u) (hsv : SSaturated v)
    (horb : sameOrbitSetoid.r u v)
    (hnf : ¬ BareFlatEquiv u v) :
    ∃ F x, sameOrbitSetoid.r u F ∧ ForkWitness F x := by
  apply flat_failure_fork_of_exists_fork
  apply classical_exists_fork_of_not_forkless
  intro hfork
  exact hnf (forklessFlatNormalWF_proved u v hu hsu hsv horb hfork)

/-- `ForklessFlatNormalWF` implies the class-global witness form. -/
theorem satFlatFiberFork_of_forklessFlatNormalWF
    (h : ForklessFlatNormalWF) : SatFlatFiberFork := by
  intro u v hu hsu hsv horb hnf
  apply flat_failure_fork_of_exists_fork
  apply classical_exists_fork_of_not_forkless
  intro hfork
  exact hnf (h u v hu hsu hsv horb hfork)

/-- The unconditional instance of the class-global invariant. -/
theorem satFlatFiberFork_proved : SatFlatFiberFork :=
  satFlatFiberFork_of_forklessFlatNormalWF forklessFlatNormalWF_proved

/-! ## Audit battery -/

#print axioms classical_exists_fork_of_not_forkless
#print axioms flat_failure_fork_of_exists_fork
#print axioms flat_failure_fork_of_decidable
#print axioms flat_failure_fork
#print axioms satFlatFiberFork_of_forklessFlatNormalWF
#print axioms satFlatFiberFork_proved
