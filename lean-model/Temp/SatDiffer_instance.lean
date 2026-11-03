import Orig2.Boundary.BoundaryMinPath

set_option autoImplicit false
set_option maxHeartbeats 4000000

/-!
# Temp/SatDiffer_instance — the residue's hypothesis is INHABITED

Scratch card (not a library leaf).  It records, against
`Orig2/Substrate/Vocab.lean`'s `SatDifferForkWF`, that the residue is **not
vacuous**:

* `s1` (`(5,0,4,2)`) and `t1` (`(5,0,2,5)`) are `WF`, `SSaturated`, mutual
  `sameOrbitSetoid` mates, with different rungs — the whole hypothesis of
  `SatDifferForkWF` at the pair `(s1,t1)`.
* `N6` (the campaign's `(3,0,2,2)` dip, `BoundaryMinPath.lean`) is in the
  orbit of `s1` and *is* a fork (`ForkWitness N6 (spade three)`), so the
  residue's conclusion also holds on this component.

Everything below is discharged by the kernel: the two endpoints by the
existing boundary cards, the orbit membership of `N6` by the six explicit
reverse legs of `prefix6` (each `by decide` on the computable state
comparison of `BoundaryForkFree`).
-/

open ForkFree
open SatDifferMin9P

namespace SatDifferInstance

/-! ## §1. The hypothesis of `SatDifferForkWF` is inhabited -/

/-- **The residue's hypothesis has a witness.**  `s1`/`t1` are both `WF`,
both `SSaturated`, mutual orbit mates, with a differing rung. -/
theorem hypothesis_instance :
    ∃ u v : State,
      u.WF ∧ SSaturated u ∧ SSaturated v ∧
        sameOrbitSetoid.r u v ∧ (∃ σ : Suit, rungAt u σ ≠ rungAt v σ) :=
  ⟨s1, t1, s1_wf, s1_sat, t1_sat, sameOrbit_s1_t1, differing_rungs⟩

/-- Hence the residue is **not vacuous**: its hypothesis is satisfiable. -/
theorem not_vacuous :
    ¬ (∀ u v : State, u.WF → SSaturated u → SSaturated v →
        sameOrbitSetoid.r u v → (∃ σ : Suit, rungAt u σ ≠ rungAt v σ) → False) := by
  intro h
  obtain ⟨u, v, hw, hu, hv, ho, hr⟩ := hypothesis_instance
  exact h u v hw hu hv ho hr

/-! ## §2. The explicit reverse legs of `prefix6` (`N6 → N5 → … → N0 = s1`) -/

def q6 : Move := Move.tabToFound (crd .spade .three)
def q5 : Move := Move.tabToFound (crd .spade .four)
def q4 : Move := Move.tabToTab (crd .club .four) (Sum.inr (crd .diamond .five))
def q3 : Move := Move.tabToTab (crd .club .three) (Sum.inr (crd .diamond .four))
def q2 : Move := Move.tabToFound (crd .heart .four)
def q1 : Move := Move.tabToFound (crd .heart .five)

theorem ret_6 : State.step N6 q6 = some N5 := sameOptB_true (by decide)
theorem ret_5 : State.step N5 q5 = some N4 := sameOptB_true (by decide)
theorem ret_4 : State.step N4 q4 = some N3 := sameOptB_true (by decide)
theorem ret_3 : State.step N3 q3 = some N2 := sameOptB_true (by decide)
theorem ret_2 : State.step N2 q2 = some N1 := sameOptB_true (by decide)
theorem ret_1 : State.step N1 q1 = some N0 := sameOptB_true (by decide)

theorem rev_6 : reversibleAtW N5 a6 :=
  ⟨N6, [q6], SatDifferMin9P.step_6, run_one ret_6⟩
theorem rev_5 : reversibleAtW N4 a5 :=
  ⟨N5, [q5], SatDifferMin9P.step_5, run_one ret_5⟩
theorem rev_4 : reversibleAtW N3 a4 :=
  ⟨N4, [q4], SatDifferMin9P.step_4, run_one ret_4⟩
theorem rev_3 : reversibleAtW N2 a3 :=
  ⟨N3, [q3], SatDifferMin9P.step_3, run_one ret_3⟩
theorem rev_2 : reversibleAtW N1 a2 :=
  ⟨N2, [q2], SatDifferMin9P.step_2, run_one ret_2⟩
theorem rev_1 : reversibleAtW N0 a1 :=
  ⟨N1, [q1], SatDifferMin9P.step_1, run_one ret_1⟩

/-- The first six moves of the 9-bracket play, as a reversible shuffle. -/
theorem shuffle_prefix6 : ShufflePlayW s1 prefix6 N6 :=
  .cons rev_1 SatDifferMin9P.step_1 (.cons rev_2 SatDifferMin9P.step_2
    (.cons rev_3 SatDifferMin9P.step_3 (.cons rev_4 SatDifferMin9P.step_4
      (.cons rev_5 SatDifferMin9P.step_5 (.cons rev_6 SatDifferMin9P.step_6
        (.nil N6))))))

/-- `N6` is in the `s1`-orbit. -/
theorem sameOrbit_s1_N6 : sameOrbitSetoid.r s1 N6 :=
  RevEqW_symm (shufflePlayW_revEqW shuffle_prefix6)

/-! ## §3. The residue's conclusion holds on the same component -/

/-- **A fork in the orbit of `s1`.**  `N6` — the campaign's own `(3,0,2,2)`
dip — is reachable reversibly from `s1` and carries `ForkWitness` at the
spade three.  So for the witness pair `(s1,t1)` the residue's existential
`∃ F x, sameOrbitSetoid.r s1 F ∧ ForkWitness F x` is *true*. -/
theorem conclusion_instance :
    ∃ F x, sameOrbitSetoid.r s1 F ∧ ForkWitness F x :=
  ⟨N6, crd .spade .three, sameOrbit_s1_N6, forkWitness_N6⟩

end SatDifferInstance

#print axioms SatDifferInstance.hypothesis_instance
#print axioms SatDifferInstance.not_vacuous
#print axioms SatDifferInstance.rev_6
#print axioms SatDifferInstance.shuffle_prefix6
#print axioms SatDifferInstance.sameOrbit_s1_N6
#print axioms SatDifferInstance.conclusion_instance
