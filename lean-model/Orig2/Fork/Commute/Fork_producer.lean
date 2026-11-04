import Orig2.Fork.Class.ForkOneColourClosure
import Orig2.Fork.Split.ForkDrainInduction
import Orig2.Substrate.CargoKit

set_option autoImplicit false

/-!
# The natural fork producer

`ForkWitness F x` is **spectrum equality** plus a vanilla block:

```lean
def ForkWitness (st : State) (x : Card) : Prop :=
  (∀ c, (c = x ∨ c = x.twin) ↔ CanRaiseS st c) ∧ ¬ CanRaise st x.twin
```

i.e. the S-live set of `st` is **exactly** `{x, x.twin}`, and `x.twin` is not
vanilla-raisable.

So the fork is not produced by finding a live pair — it is produced by a state
whose live set has *collapsed onto* the pair.  That is a saturation statement:
everything else must be blocked.  The producer itself is then definitional; the
content is the spectrum equality.
-/

namespace OneColourClosure

/-- **Spectrum equality + vanilla block = fork witness.**  Definitional. -/
theorem forkWitness_of_spectrum {F : State} {x : Card}
    (hspec : ∀ c, (c = x ∨ c = x.twin) ↔ CanRaiseS F c)
    (hblocked : ¬ CanRaise F x.twin) :
    ForkWitness F x :=
  ⟨hspec, hblocked⟩

/-- **The vanilla block comes free from a seat**: if `y` sits on `x.twin` at a
well-formed state, `x.twin` is not a pile top, hence not vanilla-raisable. -/
theorem not_canRaise_of_seated {F : State} (hF : F.WF) {y x : Card}
    (hseat : seatOf F y = some (Sum.inr x.twin)) :
    ¬ CanRaise F x.twin := by
  have hnone : F.pileOfTop x.twin = none := no_top_of_seat hF hseat
  intro hcan
  obtain ⟨-, a, ha, -⟩ := hcan
  rw [hnone] at ha
  exact absurd ha (by simp)

/-- **The natural producer**: a collapsed spectrum with the twin seated under a
cover.  No search: the spectrum equality is the hypothesis the drain analysis
supplies, and the block is `not_canRaise_of_seated`. -/
theorem forkWitness_of_spectrum_of_seated {F : State} (hF : F.WF) {y x : Card}
    (hspec : ∀ c, (c = x ∨ c = x.twin) ↔ CanRaiseS F c)
    (hseat : seatOf F y = some (Sum.inr x.twin)) :
    ForkWitness F x :=
  forkWitness_of_spectrum hspec (not_canRaise_of_seated hF hseat)

/-- **Concluding the class has a fork** — this is definitional in `Fork`
(`Orig2/Fork/Class/ForkOneColourClosure.lean:59`). -/
theorem fork_of_spectrum_of_seated {u F : State} (hF : F.WF) {y x : Card}
    (horb : sameOrbitSetoid.r u F)
    (hspec : ∀ c, (c = x ∨ c = x.twin) ↔ CanRaiseS F c)
    (hseat : seatOf F y = some (Sum.inr x.twin)) :
    Fork u :=
  ⟨F, x, horb, forkWitness_of_spectrum_of_seated hF hspec hseat⟩

/-- The `forkState` grade for consumers that want it. -/
theorem forkState_of_spectrum_of_seated {F : State} (hF : F.WF) {y x : Card}
    (hspec : ∀ c, (c = x ∨ c = x.twin) ↔ CanRaiseS F c)
    (hseat : seatOf F y = some (Sum.inr x.twin)) :
    forkState F :=
  Drain.forkState_of_forkWitness (forkWitness_of_spectrum_of_seated hF hspec hseat)

end OneColourClosure

#print axioms OneColourClosure.forkWitness_of_spectrum
#print axioms OneColourClosure.not_canRaise_of_seated
#print axioms OneColourClosure.forkWitness_of_spectrum_of_seated
#print axioms OneColourClosure.fork_of_spectrum_of_seated
#print axioms OneColourClosure.forkState_of_spectrum_of_seated
