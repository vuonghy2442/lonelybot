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

/-- An upper bound exact on the twin pair of `t`. -/
def OneColourExactUpper (u : State) (z : Suit → Nat) (t : Suit)
    (w : State) : Prop :=
  UpperTarget u z w ∧
    rungAt w t = z t ∧ rungAt w t.twin = z t.twin

/-- The least exact-`t` upper bound: a purely one-colour (2D) LUB. -/
def SliceLUB (u : State) (z : Suit → Nat) (t : Suit)
    (w : State) : Prop :=
  OneColourExactUpper u z t w ∧
    ∀ v, OneColourExactUpper u z t v →
      ∀ σ : Suit, rungAt w σ ≤ rungAt v σ

/-- **THE ONE-COLOUR SLICE THEOREM (PAIR TARGETS).**  If the componentwise
maximum of two class-mates has an exact-`t` upper bound, then it has a least
exact-`t` upper bound.  This is a 2D statement: the exact pair is fixed and
only the other pair is minimised.

The arbitrary-target version is FALSE: a fixed exact pair can have a
non-principal upper set.  The height prediction only needs pair targets. -/
def ForklessSliceLUB : Prop :=
  ∀ u, u.WF → Forkless u →
    ∀ s s', sameOrbitSetoid.r u s → sameOrbitSetoid.r u s' →
      ∀ t : Suit,
        (∃ w, OneColourExactUpper u
          (fun σ => Nat.max (rungAt s σ) (rungAt s' σ)) t w) →
        ∃ w, SliceLUB u
          (fun σ => Nat.max (rungAt s σ) (rungAt s' σ)) t w

/-- **THE EXACT NUMERIC HEIGHT REDUCES TO ONE COLOUR.**  The full minimal
join is itself the one-colour slice LUB on an exact colour. -/
theorem minimalFullJoin_is_sliceLUB
    (hslice : ForklessSliceLUB)
    (hcl : ForklessOneColourClosure)
    {s s' w : State}
    (hs : s.WF) (hfl : Forkless s)
    (hcls : sameOrbitSetoid.r s s')
    (hmin : MinimalFullJoin s s' w) :
    ∃ t : Suit,
      SliceLUB s
        (fun σ => Nat.max (rungAt s σ) (rungAt s' σ)) t w := by
  let z : Suit → Nat := fun σ => Nat.max (rungAt s σ) (rungAt s' σ)
  obtain ⟨t, ht, htt⟩ :=
    minimalFullJoin_oneColourExact hcl hs hfl hmin
  have hex : ∃ v, OneColourExactUpper s z t v :=
    ⟨w, hmin.1, ht, htt⟩
  obtain ⟨wt, hwt⟩ := hslice s hs hfl s s' (RevEqW_refl s) hcls t hex
  have hwt_upper : UpperTarget s z wt := hwt.1.1
  have hw_le_wt : ∀ σ : Suit, rungAt w σ ≤ rungAt wt σ :=
    hmin.2 wt hwt_upper
  have hwt_le_w : ∀ σ : Suit, rungAt wt σ ≤ rungAt w σ :=
    hwt.2 w ⟨hmin.1, ht, htt⟩
  have hrung_eq : ∀ σ : Suit, rungAt w σ = rungAt wt σ :=
    fun σ => Nat.le_antisymm (hw_le_wt σ) (hwt_le_w σ)
  refine ⟨t, ?_, ?_⟩
  · exact ⟨hmin.1, ht, htt⟩
  · intro v hv σ
    rw [hrung_eq σ]
    exact hwt.2 v hv σ

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

/-! ## The 2D meet form of the pair-target slice law

`ForklessSliceLUB` is witness-extracting: it asks for a *least* exact-`t`
upper bound.  Its local, choice-free content is that the exact-`t` upper bounds
of a pair target are **down-directed**: any two have a common exact-`t` lower
bound.  This is the statement measured on every sampled forkless pair-target
slice (meet-closed in all of them); the arbitrary-target version is FALSE.

Two reductions are proved here, both choice-free:

* `forklessSliceMeet_of_sliceLUB` — a slice LUB is a meet witness;
* `forklessSliceLUB_of_meet_and_finite` — a down-directed slice with an
  explicit finite enumeration has a least element, by a fold along the list.

So `ForklessSliceLUB` is precisely *2D meet + finite enumeration*: the
combinatorial content is the meet law, and the residual finiteness is the
game's own finite state space.
-/

/-- Pointwise rung domination. -/
def RungLe (v w : State) : Prop := ∀ σ : Suit, rungAt v σ ≤ rungAt w σ

theorem rungLe_refl (w : State) : RungLe w w := fun _ => Nat.le_refl _

theorem rungLe_trans {u v w : State} (h1 : RungLe u v) (h2 : RungLe v w) :
    RungLe u w := fun σ => Nat.le_trans (h1 σ) (h2 σ)

/-- **THE DOWN-DIRECTED MEET FORM (PAIR TARGETS).**  Two exact-`t` upper
bounds of the componentwise maximum of two class-mates have a common
exact-`t` lower bound. -/
def ForklessSliceMeet : Prop :=
  ∀ u, u.WF → Forkless u →
    ∀ s s', sameOrbitSetoid.r u s → sameOrbitSetoid.r u s' →
      ∀ t : Suit, ∀ v1 v2,
        OneColourExactUpper u
          (fun σ => Nat.max (rungAt s σ) (rungAt s' σ)) t v1 →
        OneColourExactUpper u
          (fun σ => Nat.max (rungAt s σ) (rungAt s' σ)) t v2 →
        ∃ v, OneColourExactUpper u
            (fun σ => Nat.max (rungAt s σ) (rungAt s' σ)) t v ∧
          RungLe v v1 ∧ RungLe v v2

/-- A slice LUB is a meet witness: it lies below both exact upper bounds. -/
theorem sliceLUB_meet {u : State} {z : Suit → Nat} {t : Suit} {w v1 v2 : State}
    (hw : SliceLUB u z t w)
    (h1 : OneColourExactUpper u z t v1)
    (h2 : OneColourExactUpper u z t v2) :
    ∃ v, OneColourExactUpper u z t v ∧ RungLe v v1 ∧ RungLe v v2 :=
  ⟨w, hw.1, hw.2 v1 h1, hw.2 v2 h2⟩

/-- **THE FIRST HALF OF THE EQUIVALENCE.**  The slice LUB law implies the
2D meet law on pair targets. -/
theorem forklessSliceMeet_of_sliceLUB (h : ForklessSliceLUB) :
    ForklessSliceMeet := by
  intro u hu hfl s s' hs hs' t v1 v2 h1 h2
  obtain ⟨w, hw⟩ := h u hu hfl s s' hs hs' t ⟨v1, h1⟩
  exact sliceLUB_meet hw h1 h2

/-- **THE FOLD.**  Starting from an exact upper bound, folding the meet law
along a list of further exact upper bounds produces a common lower bound of
the whole list — still an exact upper bound.  Constructive: each step
eliminates a `∃`, never chooses one. -/
theorem fold_lower_bound (S : State → Prop)
    (hdd : ∀ v1 v2, S v1 → S v2 → ∃ v, S v ∧ RungLe v v1 ∧ RungLe v v2) :
    ∀ (rest : List State) (m : State), S m → (∀ y ∈ rest, S y) →
      ∃ m', S m' ∧ RungLe m' m ∧ ∀ y ∈ rest, RungLe m' y := by
  intro rest
  induction rest with
  | nil =>
      intro m hm _
      exact ⟨m, hm, rungLe_refl m, by simp⟩
  | cons x xs ih =>
      intro m hm hrest
      obtain ⟨v, hvS, hvm, hvx⟩ := hdd m x hm (hrest x (by simp))
      obtain ⟨m', hm'S, hm'v, hm'xs⟩ :=
        ih v hvS (fun y hy => hrest y (by simp [hy]))
      refine ⟨m', hm'S, rungLe_trans hm'v hvm, ?_⟩
      intro y hy
      rcases List.mem_cons.mp hy with rfl | hyxs
      · exact rungLe_trans hm'v hvx
      · exact hm'xs y hyxs

/-- A finite enumeration of the slice.  In the real game this is just the
finiteness of the state space: finitely many cards, finitely many seats. -/
def SliceFinite (u : State) (z : Suit → Nat) (t : Suit) : Prop :=
  ∃ L : List State, ∀ w, OneColourExactUpper u z t w ↔ w ∈ L

/-- **THE SECOND HALF OF THE EQUIVALENCE.**  Meet + a finite enumeration of
the slice gives the slice LUB.  The least element is the fold's common lower
bound. -/
theorem forklessSliceLUB_of_meet_and_finite
    (hmeet : ForklessSliceMeet)
    (hfin : ∀ u z t, SliceFinite u z t) : ForklessSliceLUB := by
  intro u hu hfl s s' hs hs' t hex
  have hdd : ∀ v1 v2,
      OneColourExactUpper u
        (fun σ => Nat.max (rungAt s σ) (rungAt s' σ)) t v1 →
      OneColourExactUpper u
        (fun σ => Nat.max (rungAt s σ) (rungAt s' σ)) t v2 →
      ∃ v, OneColourExactUpper u
          (fun σ => Nat.max (rungAt s σ) (rungAt s' σ)) t v ∧
        RungLe v v1 ∧ RungLe v v2 :=
    hmeet u hu hfl s s' hs hs' t
  obtain ⟨L, hL⟩ := hfin u
    (fun σ => Nat.max (rungAt s σ) (rungAt s' σ)) t
  have hLne : L ≠ [] := by
    intro hnil
    obtain ⟨w, hw⟩ := hex
    have hmem : w ∈ L := (hL w).mp hw
    rw [hnil] at hmem
    exact absurd hmem (List.not_mem_nil)
  obtain ⟨x, hxL⟩ := List.exists_mem_of_ne_nil L hLne
  obtain ⟨m, hmS, _, hmle⟩ :=
    fold_lower_bound _ hdd L x ((hL x).mpr hxL)
      (fun y hy => (hL y).mpr hy)
  refine ⟨m, hmS, ?_⟩
  intro v hv σ
  exact hmle v ((hL v).mp hv) σ

/-- **THE EXACT HEIGHT PREDICTION FROM THE 2D MEET LAW.**  Meet + finite slice
+ one-colour closure give the exact numeric height: the full minimal join is
the one-colour slice LUB. -/
theorem minimalFullJoin_is_sliceLUB_of_meet
    (hmeet : ForklessSliceMeet)
    (hfin : ∀ u z t, SliceFinite u z t)
    (hcl : ForklessOneColourClosure)
    {s s' w : State}
    (hs : s.WF) (hfl : Forkless s)
    (hcls : sameOrbitSetoid.r s s')
    (hmin : MinimalFullJoin s s' w) :
    ∃ t : Suit,
      SliceLUB s
        (fun σ => Nat.max (rungAt s σ) (rungAt s' σ)) t w :=
  minimalFullJoin_is_sliceLUB (forklessSliceLUB_of_meet_and_finite hmeet hfin)
    hcl hs hfl hcls hmin

/-- **THE SLICE LUB IS THE FULL LUB.**  Every pair-target slice LUB dominates
every upper bound of the target, not only the exact ones.  Measured on the
whole corpus (99 716 candidate checks: core, t1, random8/10, greedy,
twinswap; 0 failures).  This is the content of the converse direction of the
height prediction. -/
def ForklessSliceDominatesUpper : Prop :=
  ∀ u, u.WF → Forkless u →
    ∀ s s', sameOrbitSetoid.r u s → sameOrbitSetoid.r u s' →
      ∀ t w,
        SliceLUB u (fun σ => Nat.max (rungAt s σ) (rungAt s' σ)) t w →
        ∀ v,
          UpperTarget u (fun σ => Nat.max (rungAt s σ) (rungAt s' σ)) v →
          RungLe w v

/-- **THE HEIGHT PREDICTION (CONVERSE DIRECTION).**  Top supplies a bound, the
one-colour closure selects an exact colour, the slice LUB exists on it, and
because it dominates every upper bound it is the full minimal join.  So the
exact numeric height is achieved by the slice LUB, not merely bounded by it. -/
theorem minimalFullJoin_of_sliceLUB_and_dominates
    (htop : ForklessHasTop)
    (hcl : ForklessOneColourClosure)
    (hslice : ForklessSliceLUB)
    (hdom : ForklessSliceDominatesUpper)
    {s s' : State}
    (hs : s.WF) (hfl : Forkless s) (hcls : sameOrbitSetoid.r s s') :
    ∃ w, MinimalFullJoin s s' w := by
  let z : Suit → Nat := fun σ => Nat.max (rungAt s σ) (rungAt s' σ)
  obtain ⟨top, htopr⟩ := htop s hs hfl
  have hbounded : ∃ top', UpperTarget s z top' := by
    refine ⟨top, htopr.1, ?_⟩
    intro σ
    exact Nat.max_le.mpr
      ⟨htopr.2 s (RevEqW_refl s) σ, htopr.2 s' hcls σ⟩
  obtain ⟨e, he_upper, he_exact⟩ := hcl s hs hfl z hbounded
  obtain ⟨t, ht, htt⟩ := he_exact
  have hex : ∃ v, OneColourExactUpper s z t v := ⟨e, he_upper, ht, htt⟩
  obtain ⟨w, hw⟩ := hslice s hs hfl s s' (RevEqW_refl s) hcls t hex
  refine ⟨w, hw.1.1, ?_⟩
  intro v hv σ
  exact hdom s hs hfl s s' (RevEqW_refl s) hcls t w hw v hv σ

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
#print axioms OneColourClosure.minimalFullJoin_is_sliceLUB
#print axioms OneColourClosure.forklessSliceMeet_of_sliceLUB
#print axioms OneColourClosure.fold_lower_bound
#print axioms OneColourClosure.forklessSliceLUB_of_meet_and_finite
#print axioms OneColourClosure.minimalFullJoin_is_sliceLUB_of_meet
#print axioms OneColourClosure.minimalFullJoin_of_sliceLUB_and_dominates
