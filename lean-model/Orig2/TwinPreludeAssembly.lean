import Orig2.TwinPreludeFunctor
import Orig2.TwinPairFreeClass
import Orig2.TwinPairFreeRev
import Orig2.TwinSuffixCancel

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# Orig2.TwinPreludeAssembly — the endgame reduction

This card instantiates the assembly theorem of `TwinPreludeFunctor` with
the two residuals isolated by `TwinPairFreeClass`:

* `PairFreeReversal` — pair-free plays are pair-free reversible;
* `PairFoundSuffixCancellation` — a play split at its last
  pair-foundation letter with a pair-free suffix already has the
  endpoint classification.

The result is `FirstRaiseNormalization`, hence `PairFoundNormalization`,
hence `PreludeNormalizationWF`, conditional exactly on those two rows.

Zero `sorry`, zero `Classical.choice`, no new axioms.
-/

open State

/-- The two pair-free reachability carriers are the same relation. -/
theorem pairFreeReach_iff_orbit {x : Card} {u v : State} :
    PairFreeReach x u v ↔ PairFreeOrbit x u v :=
  Iff.rfl

/-- `FirstRaiseNormalization` from the two residuals of
`TwinPairFreeClass`. -/
theorem firstRaiseNormalization_of_residuals {x : Card}
    (hrev : PairFreeReversal x) (hsuf : PairFoundSuffixCancellation x) :
    FirstRaiseNormalization x := by
  refine firstRaiseNormalization_of_pairFreeClass (x := x) ?_ ?_
  · intro u v z play hwf hx hxt hplay hvx hvt
    obtain ⟨w', hw'⟩ := hvt
    have h :=
      pairFree_endpoint_classification_of_residuals hrev hsuf hwf hx hxt
        hplay hvx ⟨w'.twin, hw'⟩
    simpa [PairFreeReach, PairFreeOrbit] using h
  · intro s t z play hwf hx hxt hplay hno
    have h : PairFreeOrbit x t s := hrev hwf hx hxt hplay hno
    simpa [PairFreeReach, PairFreeOrbit] using h

/-- `PairFoundNormalization` from the two residuals. -/
theorem pairFoundNormalization_of_residuals {x : Card}
    (hrev : PairFreeReversal x) (hsuf : PairFoundSuffixCancellation x) :
    PairFoundNormalization x :=
  pairFoundNormalization_of_firstRaise
    (firstRaiseNormalization_of_residuals hrev hsuf)

/-- **The WF-gated prelude normalization from the two residuals.** -/
theorem preludeNormalizationWF_of_residuals {x : Card}
    (hrev : PairFreeReversal x) (hsuf : PairFoundSuffixCancellation x) :
    PreludeNormalizationWF x :=
  preludeNormalizationWF_of_pairFound
    (pairFoundNormalization_of_residuals hrev hsuf)

/-- **The full fiber transfer from the two residuals.**  The king arm is
unconditional; the non-king arm is the functor chain. -/
theorem fiber_transfer_corrected_of_residuals
    (hrev : ∀ x : Card, PairFreeReversal x)
    (hsuf : ∀ x : Card, PairFoundSuffixCancellation x)
    {s s' : State} (hwf : s.WF) (hwf' : s'.WF) {x : Card}
    (hclass : sameOrbitSetoid.r s s') (hfound : s.found = s'.found)
    (hswap : SwappableIn s x) (hdata : FiberSeatData s s' x) :
    SwappableIn s' x :=
  fiber_transfer_corrected_viaFunctor
    (fun y => preludeNormalizationWF_of_residuals (hrev y) (hsuf y))
    hwf hwf' hclass hfound hswap hdata

/-- **The suffix cancellation from the last-pull residual.**  Pair-free
reversal is now unconditional (`TwinPairFreeRev.pairFreeReversal`), so
the two-residual reduction collapses to `LastPullCancellation`. -/
theorem pairFoundSuffixCancellation_of_lastPull
    (hlast : ∀ x : Card, LastPullCancellation x) :
    ∀ x : Card, PairFoundSuffixCancellation x :=
  fun x =>
    pairFoundSuffixCancellation_of_reversal_of_lastPull
      (TwinPairFreeRev.pairFreeReversal (x := x)) (hlast x)

/-- `FirstRaiseNormalization` from the single last-pull residual. -/
theorem firstRaiseNormalization_of_lastPull
    (hlast : ∀ x : Card, LastPullCancellation x) :
    ∀ x : Card, FirstRaiseNormalization x :=
  fun x =>
    firstRaiseNormalization_of_residuals
      (TwinPairFreeRev.pairFreeReversal (x := x))
      (pairFoundSuffixCancellation_of_lastPull hlast x)

/-- `PairFoundNormalization` from the single last-pull residual. -/
theorem pairFoundNormalization_of_lastPull
    (hlast : ∀ x : Card, LastPullCancellation x) :
    ∀ x : Card, PairFoundNormalization x :=
  fun x =>
    pairFoundNormalization_of_firstRaise
      (firstRaiseNormalization_of_lastPull hlast x)

/-- **The WF-gated prelude normalization from the single last-pull
residual.** -/
theorem preludeNormalizationWF_of_lastPull
    (hlast : ∀ x : Card, LastPullCancellation x) :
    ∀ x : Card, PreludeNormalizationWF x :=
  fun x =>
    preludeNormalizationWF_of_pairFound
      (pairFoundNormalization_of_lastPull hlast x)

/-- **The full fiber transfer from the single last-pull residual.** -/
theorem fiber_transfer_corrected_of_lastPull
    (hlast : ∀ x : Card, LastPullCancellation x)
    {s s' : State} (hwf : s.WF) (hwf' : s'.WF) {x : Card}
    (hclass : sameOrbitSetoid.r s s') (hfound : s.found = s'.found)
    (hswap : SwappableIn s x) (hdata : FiberSeatData s s' x) :
    SwappableIn s' x :=
  fiber_transfer_corrected_viaFunctor
    (fun y => preludeNormalizationWF_of_lastPull hlast y)
    hwf hwf' hclass hfound hswap hdata

#print axioms pairFreeReach_iff_orbit
#print axioms firstRaiseNormalization_of_residuals
#print axioms pairFoundNormalization_of_residuals
#print axioms preludeNormalizationWF_of_residuals
#print axioms fiber_transfer_corrected_of_residuals
#print axioms pairFoundSuffixCancellation_of_lastPull
#print axioms firstRaiseNormalization_of_lastPull
#print axioms pairFoundNormalization_of_lastPull
#print axioms preludeNormalizationWF_of_lastPull
#print axioms fiber_transfer_corrected_of_lastPull
