import Orig2.Fork.Class.ForkOneColourClosure
import Orig2.Fork.Class.ForkRaiseReorder
import Orig2.Fork.Class.ForkRaiseReorderProof

set_option autoImplicit false

/-!
# Strengthening `FullJoinAtLeast`: raiseS-reachability, allowing overshoot

The plain join says *there exists* a class-mate `w` whose rungs dominate both
endpoints.  The strengthening says each endpoint **reaches** rungs that dominate
`w`'s by a `raiseS`-only licensed path (slide-star, then a raise; no pulls, no
draws).

Two design choices matter:

* **overshoot is allowed.**  The path's endpoint only has to *dominate* `w`'s
  rungs, not equal them.  This is what the join actually needs
  (`max (rungAt s) (rungAt s') ≤ rungAt w` composes with `≤`), and it removes
  the "don't raise a card the target lacks" cap from the induction: the proof
  may simply saturate.
* with overshoot the only remaining input is: **a class-mate can be reached from
  the raise-closure of another**, i.e. saturation dominates the class.  That is
  the statement the probes have not refuted.
-/

namespace OneColourClosure

/-- `s` reaches, by a `raiseS`-only licensed path, rungs that dominate `w`'s. -/
def RungReachableAtLeast (s w : State) : Prop :=
  ∃ ws z, RaiseSSeqLicensed s ws z ∧ ∀ σ : Suit, rungAt w σ ≤ rungAt z σ

/-- **The strengthened join** (overshoot form). -/
def FullJoinAtLeastRaiseS (s s' w : State) : Prop :=
  FullJoinAtLeast s s' w ∧ RungReachableAtLeast s w ∧ RungReachableAtLeast s' w

/-- The strengthened join-or-fork target. -/
def FullJoinAtLeastRaiseSOrFork : Prop :=
  ∀ s s', s.WF → s'.WF → sameOrbitSetoid.r s s' →
    (∃ w, FullJoinAtLeastRaiseS s s' w) ∨ Fork s

/-- **Assembly.**  The only input is "from a class-mate, `raiseS` reaches at
least its rungs" — no rank comparison, no cap, no fork hypothesis. -/
theorem fullJoinAtLeastRaiseS_of_reach
    (hR : ∀ {s w : State}, sameOrbitSetoid.r s w → RungReachableAtLeast s w)
    {s s' w : State} (hcls : sameOrbitSetoid.r s s') (hjoin : FullJoinAtLeast s s' w) :
    FullJoinAtLeastRaiseS s s' w := by
  refine ⟨hjoin, hR hjoin.1, hR ?_⟩
  exact RevEqW_trans hjoin.1 (RevEqW_symm hcls)

/-- **The target from join-or-fork plus reachability.** -/
theorem fullJoinAtLeastRaiseSOrFork_of_reach
    (hR : ∀ {s w : State}, sameOrbitSetoid.r s w → RungReachableAtLeast s w)
    (hjoin : FullJoinAtLeastOrFork) :
    FullJoinAtLeastRaiseSOrFork := by
  intro s s' hs hs' hcls
  rcases hjoin s s' hs hs' hcls with ⟨w, hw⟩ | hfork
  · exact Or.inl ⟨w, fullJoinAtLeastRaiseS_of_reach (s := s) (s' := s') hR hcls hw⟩
  · exact Or.inr hfork

/-- Sanity: the overshoot form implies the exact-rung form whenever the path's
endpoint happens to sit at `w`'s rungs. -/
theorem rungReachableAtLeast_of_eq {s w : State}
    (h : ∃ ws z, RaiseSSeqLicensed s ws z ∧ ∀ σ : Suit, rungAt z σ = rungAt w σ) :
    RungReachableAtLeast s w := by
  obtain ⟨ws, z, hpath, heq⟩ := h
  exact ⟨ws, z, hpath, fun σ => Nat.le_of_eq (heq σ).symm⟩

end OneColourClosure

#print axioms OneColourClosure.fullJoinAtLeastRaiseS_of_reach
#print axioms OneColourClosure.fullJoinAtLeastRaiseSOrFork_of_reach
#print axioms OneColourClosure.rungReachableAtLeast_of_eq
