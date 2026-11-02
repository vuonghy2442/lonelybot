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

/-- A least upper bound of the target `z` in the class of `u`. -/
def IsLUBTarget (u : State) (z : Suit → Nat) (w : State) : Prop :=
  UpperTarget u z w ∧
    ∀ v, UpperTarget u z v → ∀ σ : Suit, rungAt w σ ≤ rungAt v σ

/-- The **minimal** full overshoot join for `s,s'`: the least class-mate
above the componentwise maximum. -/
def MinimalFullJoin (s s' w : State) : Prop :=
  IsLUBTarget s (fun σ => Nat.max (rungAt s σ) (rungAt s' σ)) w

/-- **THE EXACT MINIMAL OVERSHOOT IS ONE-COLOUR EXACT.**  In a forkless
class, the least upper bound of the componentwise maximum is exact on at
least one twin pair.  Consequently all strict overshoot is confined to the
other twin pair, so the overshoot support has size at most two. -/
theorem minimalFullJoin_oneColourExact
    (hcl : ForklessOneColourClosure)
    {s s' w : State}
    (hs : s.WF) (hfl : Forkless s) (hmin : MinimalFullJoin s s' w) :
    OneColourExactTarget
      (fun σ => Nat.max (rungAt s σ) (rungAt s' σ)) w := by
  let z : Suit → Nat := fun σ => Nat.max (rungAt s σ) (rungAt s' σ)
  have hbounded : ∃ e, UpperTarget s z e :=
    ⟨w, hmin.1.1, hmin.1.2⟩
  obtain ⟨e, he_upper, he_exact⟩ := hcl s hs hfl z hbounded
  have hwle : ∀ σ : Suit, rungAt w σ ≤ rungAt e σ :=
    hmin.2 e he_upper
  obtain ⟨t, ht, htt⟩ := he_exact
  refine ⟨t, ?_, ?_⟩
  · have hge : z t ≤ rungAt w t := hmin.1.2 t
    have hle : rungAt w t ≤ z t := by
      have := hwle t
      rwa [ht] at this
    exact Nat.le_antisymm hle hge
  · have hge : z t.twin ≤ rungAt w t.twin := hmin.1.2 t.twin
    have hle : rungAt w t.twin ≤ z t.twin := by
      have := hwle t.twin
      rwa [htt] at this
    exact Nat.le_antisymm hle hge

/-- The support form: all strict overshoot lies outside the exact twin
pair, hence in the other colour. -/
theorem minimalFullJoin_overshoot_oneColour
    (hcl : ForklessOneColourClosure)
    {s s' w : State}
    (hs : s.WF) (hfl : Forkless s) (hmin : MinimalFullJoin s s' w) :
    ∃ t : Suit,
      (rungAt w t = Nat.max (rungAt s t) (rungAt s' t) ∧
       rungAt w t.twin =
         Nat.max (rungAt s t.twin) (rungAt s' t.twin)) ∧
      (∀ σ : Suit,
        Nat.max (rungAt s σ) (rungAt s' σ) < rungAt w σ →
          σ ≠ t ∧ σ ≠ t.twin) := by
  obtain ⟨t, ht, htt⟩ :=
    minimalFullJoin_oneColourExact hcl hs hfl hmin
  have ht' : rungAt w t = Nat.max (rungAt s t) (rungAt s' t) := by
    simpa using ht
  have htt' : rungAt w t.twin =
      Nat.max (rungAt s t.twin) (rungAt s' t.twin) := by
    simpa using htt
  refine ⟨t, ⟨ht', htt'⟩, ?_⟩
  intro σ hgt
  constructor
  · intro hσt
    rw [hσt, ht'] at hgt
    exact Nat.lt_irrefl _ hgt
  · intro hσtw
    rw [hσtw, htt'] at hgt
    exact Nat.lt_irrefl _ hgt

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
#print axioms OneColourClosure.minimalFullJoin_oneColourExact
#print axioms OneColourClosure.minimalFullJoin_overshoot_oneColour
