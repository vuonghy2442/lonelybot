import Orig2.ForkTwinJoin

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# Orig2.ForkOneColourClosure — the one-colour closure law and its reduction

This card formalizes the forkless one-colour closure normal form and reduces
it to the full overshoot join target.  The closure law is measured on every
sampled forkless component: every bounded target has an upper-bound
class-mate which is exact on one twin pair.  The reduction is choice-free;
the fork/forkless split is an explicit hypothesis, not a classical choice.

Definitions:

* `Forkless u` — no `forkState` in the class of `u`.
* `Fork u` — a `ForkWitness` somewhere in the class.
* `ForklessOrFork u` — the fork/forkless split (kept as an explicit
  hypothesis so the reduction stays choice-free).
* `UpperTarget u z w` — `w` is a class-mate of `u` above the target `z`.
* `OneColourExactTarget z w` — `w` matches `z` exactly on one twin pair.
* `ForklessOneColourClosure` — every bounded target has a one-colour-exact
  upper bound.
* `ForklessHasTop` — a forkless class has a rung top.

The reduction proves:

`ForklessHasTop + ForklessOneColourClosure + ForklessOrFork`
  `⇒ FullJoinAtLeastOneColourOrFork`
  `⇒ FullJoinAtLeastOrFork`.

The closure/top hypotheses remain the structural residual; this card only
compiles the reduction.  No `sorry`, no `Classical.choice`.
-/

namespace OneColourClosure

open TwinJoin

/-- No `forkState` in the class of `u`. -/
def Forkless (u : State) : Prop :=
  ∀ F, sameOrbitSetoid.r u F → ¬ forkState F

/-- A `ForkWitness` somewhere in the class of `u`. -/
def Fork (u : State) : Prop :=
  ∃ F x, sameOrbitSetoid.r u F ∧ ForkWitness F x

/-- The choice-free fork/forkless split. -/
def ForklessOrFork (u : State) : Prop :=
  Forkless u ∨ Fork u

/-- `w` is a class-mate of `u` above the target `z`. -/
def UpperTarget (u : State) (z : Suit → Nat) (w : State) : Prop :=
  sameOrbitSetoid.r u w ∧ ∀ σ : Suit, z σ ≤ rungAt w σ

/-- `w` matches `z` exactly on one twin pair. -/
def OneColourExactTarget (z : Suit → Nat) (w : State) : Prop :=
  ∃ t : Suit,
    rungAt w t = z t ∧ rungAt w t.twin = z t.twin

/-- **THE ONE-COLOUR CLOSURE LAW.**  In a forkless class, every bounded
target has an upper-bound class-mate which is exact on one colour. -/
def ForklessOneColourClosure : Prop :=
  ∀ (u : State),
    u.WF →
    Forkless u →
    ∀ z : Suit → Nat,
      (∃ w, UpperTarget u z w) →
      ∃ w, UpperTarget u z w ∧ OneColourExactTarget z w

/-- A rung top of the class of `u`. -/
def HasTopRung (u w : State) : Prop :=
  sameOrbitSetoid.r u w ∧
    ∀ x, sameOrbitSetoid.r u x → ∀ σ : Suit, rungAt x σ ≤ rungAt w σ

/-- Every forkless class has a rung top. -/
def ForklessHasTop : Prop :=
  ∀ u, u.WF → Forkless u → ∃ w, HasTopRung u w

/-- The full four-suit overshoot join. -/
def FullJoinAtLeast (s s' w : State) : Prop :=
  sameOrbitSetoid.r s w ∧
    ∀ σ : Suit,
      Nat.max (rungAt s σ) (rungAt s' σ) ≤ rungAt w σ

/-- The full overshoot join with one colour exact. -/
def FullJoinAtLeastOneColour (s s' w : State) : Prop :=
  FullJoinAtLeast s s' w ∧
    ∃ t : Suit,
      rungAt w t = Nat.max (rungAt s t) (rungAt s' t) ∧
      rungAt w t.twin = Nat.max (rungAt s t.twin) (rungAt s' t.twin)

/-- The target: full overshoot join or fork. -/
def FullJoinAtLeastOrFork : Prop :=
  ∀ s s', s.WF → s'.WF → sameOrbitSetoid.r s s' →
    (∃ w, FullJoinAtLeast s s' w) ∨ Fork s

/-- The stronger target: one-colour-exact overshoot join or fork. -/
def FullJoinAtLeastOneColourOrFork : Prop :=
  ∀ s s', s.WF → s'.WF → sameOrbitSetoid.r s s' →
    (∃ w, FullJoinAtLeastOneColour s s' w) ∨ Fork s

/-- **THE REDUCTION.**  Top + one-colour closure + fork split gives the
one-colour-exact overshoot target. -/
theorem fullJoinAtLeastOneColourOrFork_of_top_and_closure
    (htop : ForklessHasTop)
    (hcl : ForklessOneColourClosure)
    (hdich : ∀ u, u.WF → ForklessOrFork u) :
    FullJoinAtLeastOneColourOrFork := by
  intro s s' hs hs' hcls
  rcases hdich s hs with hforkless | hfork
  · -- forkless branch: use the top, then the one-colour closure
    have hs'cls : sameOrbitSetoid.r s s' := hcls
    obtain ⟨w, hwtop⟩ := htop s hs hforkless
    let z : Suit → Nat := fun σ => Nat.max (rungAt s σ) (rungAt s' σ)
    have hbounded : ∃ w, UpperTarget s z w := by
      refine ⟨w, hwtop.1, ?_⟩
      intro σ
      exact Nat.max_le.mpr
        ⟨hwtop.2 s (RevEqW_refl s) σ, hwtop.2 s' hcls σ⟩
    -- the closure produces a one-colour-exact upper bound
    obtain ⟨w', hw'upper, hw'exact⟩ := hcl s hs hforkless z hbounded
    have hjoin : FullJoinAtLeastOneColour s s' w' := by
      refine ⟨?_, hw'exact⟩
      refine ⟨hw'upper.1, ?_⟩
      intro σ
      exact hw'upper.2 σ
    exact Or.inl ⟨w', hjoin⟩
  · exact Or.inr hfork

/-- The weaker target follows. -/
theorem fullJoinAtLeastOrFork_of_top_and_closure
    (htop : ForklessHasTop)
    (hcl : ForklessOneColourClosure)
    (hdich : ∀ u, u.WF → ForklessOrFork u) :
    FullJoinAtLeastOrFork := by
  intro s s' hs hs' hcls
  rcases fullJoinAtLeastOneColourOrFork_of_top_and_closure htop hcl hdich
      s s' hs hs' hcls with hjoin | hfork
  · obtain ⟨w, hw, -⟩ := hjoin
    exact Or.inl ⟨w, hw⟩
  · exact Or.inr hfork

end OneColourClosure

#print axioms OneColourClosure.fullJoinAtLeastOneColourOrFork_of_top_and_closure
#print axioms OneColourClosure.fullJoinAtLeastOrFork_of_top_and_closure
