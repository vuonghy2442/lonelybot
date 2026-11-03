import Orig2.Fork.Class.ForkOneColourClosure
import Orig2.Fork.Class.ForkRaiseReorder
import Orig2.Fork.Class.ForkRaiseReorderProof

set_option autoImplicit false

/-!
# Strengthening `FullJoinAtLeast`: raiseS-reachability from both ends

The plain join only says *there exists* a class-mate `w` whose rungs dominate
both endpoints.  The strengthening says each endpoint **reaches** those rungs by
a `raiseS`-only licensed path (the campaign's notion: slide-star, then a raise;
pulls and draws do not occur).

The only new input is rung-reachability inside a class:

```
(RungReach)   sameOrbit s w  ->  RungLe s w  ->  raiseS-reachable rungs of w
```

which is the statement the probe (`Temp/Falsify_sat_below_orbit.py`,
`Temp/Falsify_rungreach.py`) has so far failed to refute: ~700 orbit components,
~5400 saturated states, 0 hits.
-/

namespace OneColourClosure

/-- `s` reaches `w`'s rung tuple by a `raiseS`-only licensed path. -/
def RungReachable (s w : State) : Prop :=
  ∃ ws z, RaiseSSeqLicensed s ws z ∧ ∀ σ : Suit, rungAt z σ = rungAt w σ

/-- **The strengthened join.**  The plain join, plus raiseS-reachability of its
rungs from each endpoint. -/
def FullJoinAtLeastRaiseS (s s' w : State) : Prop :=
  FullJoinAtLeast s s' w ∧ RungReachable s w ∧ RungReachable s' w

/-- The strengthened join-or-fork target. -/
def FullJoinAtLeastRaiseSOrFork : Prop :=
  ∀ s s', s.WF → s'.WF → sameOrbitSetoid.r s s' →
    (∃ w, FullJoinAtLeastRaiseS s s' w) ∨ Fork s

/-- **The assembly.**  Plain join + rung-reachability gives the strengthened
join.  Note that no fork hypothesis is used: the strengthening is orthogonal to
the residue. -/
theorem fullJoinAtLeastRaiseS_of_rungReach
    (hR : ∀ {s w : State}, sameOrbitSetoid.r s w → RungLe s w → RungReachable s w)
    {s s' w : State} (hcls : sameOrbitSetoid.r s s') (hjoin : FullJoinAtLeast s s' w) :
    FullJoinAtLeastRaiseS s s' w := by
  refine ⟨hjoin, ?_, ?_⟩
  · exact hR hjoin.1 (fun σ => Nat.le_trans (Nat.le_max_left _ _) (hjoin.2 σ))
  · refine hR ?_ (fun σ => Nat.le_trans (Nat.le_max_right _ _) (hjoin.2 σ))
    exact RevEqW_trans hjoin.1 (RevEqW_symm hcls)

/-- The target, from plain join-or-fork and rung-reachability. -/
theorem fullJoinAtLeastRaiseSOrFork_of_rungReach
    (hR : ∀ {s w : State}, sameOrbitSetoid.r s w → RungLe s w → RungReachable s w)
    (hjoin : FullJoinAtLeastOrFork) :
    FullJoinAtLeastRaiseSOrFork := by
  intro s s' hs hs' hcls
  rcases hjoin s s' hs hs' hcls with ⟨w, hw⟩ | hfork
  · exact Or.inl ⟨w, fullJoinAtLeastRaiseS_of_rungReach (s := s) (s' := s') hR hcls hw⟩
  · exact Or.inr hfork

end OneColourClosure

#print axioms OneColourClosure.fullJoinAtLeastRaiseS_of_rungReach
#print axioms OneColourClosure.fullJoinAtLeastRaiseSOrFork_of_rungReach
