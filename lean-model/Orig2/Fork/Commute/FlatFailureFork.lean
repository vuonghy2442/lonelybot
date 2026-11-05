import Orig2.Fork.Commute.FlatNormal

set_option autoImplicit false

/-!
# Orig2.Fork.Commute.FlatFailureFork - the explicit-witness form

The class-global explicit-witness companion of
`Orig2/Fork/Commute/FlatNormal.lean`: a saturated same-orbit pair outside the
flat fiber exhibits a `ForkWitness` somewhere in its class.

The final `¬∀ → ∃` step is classical (and uses `Classical.choice` through
`Classical.propDecidable`), as neither `sameOrbitSetoid.r` nor `forkState`
carries a decidability instance.  The constructive core
`flat_failure_fork_of_exists_fork` shows that, once the class-global fork
existential is supplied, unpacking the per-card witness is choice-free.
-/

/-- **`SatFlatFiberFork`, explicit-witness / class-global form.** -/
theorem flat_failure_fork
    {u v : State}
    (hu : u.WF) (hsu : SSaturated u) (hsv : SSaturated v)
    (horb : sameOrbitSetoid.r u v)
    (hnf : ¬ BareFlatEquiv u v) :
    ∃ F x, sameOrbitSetoid.r u F ∧ ForkWitness F x := by
  apply Classical.byContradiction
  intro h
  have hno : ∀ F, sameOrbitSetoid.r u F → ¬ forkState F := by
    intro F hF hfork
    obtain ⟨x, hx⟩ := hfork
    exact h ⟨F, x, hF, hx⟩
  exact hnf (forklessFlatNormalWF_proved u v hu hsu hsv horb hno)

/-- `ForklessFlatNormalWF` implies the class-global witness form. -/
theorem satFlatFiberFork_of_forklessFlatNormalWF
    (h : ForklessFlatNormalWF) : SatFlatFiberFork := by
  intro u v hu hsu hsv horb hnf
  apply Classical.byContradiction
  intro hcon
  have hno : ∀ F, sameOrbitSetoid.r u F → ¬ forkState F := by
    intro F hF hfork
    obtain ⟨x, hx⟩ := hfork
    exact hcon ⟨F, x, hF, hx⟩
  exact hnf (h u v hu hsu hsv horb hno)

/-- The unconditional instance of the class-global invariant. -/
theorem satFlatFiberFork_proved : SatFlatFiberFork :=
  satFlatFiberFork_of_forklessFlatNormalWF forklessFlatNormalWF_proved

/-- The constructive core: once the class-global fork existential is
available, the per-card witness is pure unpacking. -/
theorem flat_failure_fork_of_exists_fork
    {u : State} (h : ∃ F, sameOrbitSetoid.r u F ∧ forkState F) :
    ∃ F x, sameOrbitSetoid.r u F ∧ ForkWitness F x := by
  obtain ⟨F, hF, x, hx⟩ := h
  exact ⟨F, x, hF, hx⟩

/-! ## Audit battery -/

#print axioms flat_failure_fork
#print axioms satFlatFiberFork_of_forklessFlatNormalWF
#print axioms satFlatFiberFork_proved
#print axioms flat_failure_fork_of_exists_fork
