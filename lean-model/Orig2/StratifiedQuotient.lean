import Orig2.FiberTransfer

/-!
# Orig2.StratifiedQuotient - THE UNIVERSAL PROPERTY (2026-10-26, the owner's ask)

The fiber transfer, generalized into the universal property of the
stratified quotient.  The §15 result (`fiber_transfer_twin_membership`)
says: swappability transfers along the reversible class whenever the
twins' foundation-membership is preserved.  Read as invariance:
within a fiber of the map
    WF-state ↦ (its reversible class, its twins' membership profile),
swappability is CONSTANT.  That is precisely the well-definedness
the quotient's universal property consumes: `SwappableIn` descends
to the stratified quotient, uniquely - and so does every
stratum-invariant predicate.

The two axioms the house batteries always printed become
load-bearing by design: `Quot.sound` IS the quotient's universal
property; `propext` is the glue that turns the invariance iff into
the lift's equality.  This discharges the campaign's honest-residue
"quotient formalization" note - the torseur story's missing
capstone.  (The archived `Archive/TwinFiberQuotient.lean` chased the
same corollary-of-structure goal through splice normal forms; this
card rides the certified transfer directly instead.)

## The map
* `stratOrbit` - the stratified orbit setoid on WF states (the
  §15 premise set as an equivalence relation)
* `swappable_stratum_invariant` - the transfer as an iff: within a
  stratum, swappability is constant
* `SwappableStratum` - the descended predicate (via `Quotient.lift`)
* `swappableStratum_mk` - the computation rule: the descent agrees
  with swappability at every point
* `stratOrbit_universal` - THE UNIVERSAL PROPERTY: every
  stratum-invariant predicate descends, uniquely
* `swappableStratum_unique` - swappability factors through the
  stratum, uniquely
-/

open State

/-- A well-formed state - the carrier of the stratified quotient
(the transfer is stated between WF endpoints). -/
abbrev WFState : Type := {s : State // s.WF}

/-- **The stratified orbit**: the reversible class, stratified by the
twins' foundation-membership profile - exactly the coinducing data of
the §15 transfer.  Its fibers are the strata on which swappability is
constant. -/
def stratOrbit (x : Card) : Setoid WFState where
  r s s' :=
    sameOrbitSetoid.r s.val s'.val ∧
    (x ∈ s.val.found x.suit ↔ x ∈ s'.val.found x.suit) ∧
    (x.twin ∈ s.val.found x.twin.suit ↔ x.twin ∈ s'.val.found x.twin.suit)
  iseqv :=
    { refl := fun s => ⟨sameOrbitSetoid.iseqv.refl s.val, Iff.rfl, Iff.rfl⟩
      symm := fun h => ⟨sameOrbitSetoid.iseqv.symm h.1,
        Iff.symm h.2.1, Iff.symm h.2.2⟩
      trans := fun h h' => ⟨sameOrbitSetoid.iseqv.trans h.1 h'.1,
        Iff.trans h.2.1 h'.2.1, Iff.trans h.2.2 h'.2.2⟩ }

/-- **The transfer as invariance**: within a stratum, swappability is
constant - the §15 theorem run both ways (the class relation and the
membership profile are symmetric data). -/
theorem swappable_stratum_invariant (x : Card) {s s' : WFState}
    (h : (stratOrbit x).r s s') : SwappableIn s.val x ↔ SwappableIn s'.val x := by
  constructor
  · intro hswap
    exact fiber_transfer_twin_membership s.val s'.val x s.2 s'.2
      h.1 h.2.1 h.2.2 hswap
  · intro hswap
    exact fiber_transfer_twin_membership s'.val s.val x s'.2 s.2
      (sameOrbitSetoid.iseqv.symm h.1) (Iff.symm h.2.1) (Iff.symm h.2.2) hswap

/-- **The descended predicate**: swappability on the stratified
quotient - well-defined BY the invariance, the quotient's universal
property doing the work. -/
def SwappableStratum (x : Card) : Quotient (stratOrbit x) → Prop :=
  Quotient.lift (fun s => SwappableIn s.val x)
    (fun _ _ h => propext (swappable_stratum_invariant x h))

/-- The computation rule: the descent agrees with swappability at
every point. -/
theorem swappableStratum_mk (x : Card) (s : WFState) :
    SwappableStratum x (Quotient.mk (stratOrbit x) s) = SwappableIn s.val x := rfl

/-- Unique existence, defined locally - the card stays Mathlib-free
by house discipline (the batteries must stay `[propext,
Quot.sound]`). -/
def ExistsUnique {α : Sort u} (p : α → Prop) : Prop :=
  ∃ w, p w ∧ ∀ y, p y → y = w

/-- **THE UNIVERSAL PROPERTY** of the stratified quotient: every
stratum-invariant predicate descends to the quotient, UNIQUELY.
Swappability is the instance; the fiber transfer is the invariance
that feeds it. -/
theorem stratOrbit_universal (x : Card) (P : WFState → Prop)
    (hP : ∀ s s', (stratOrbit x).r s s' → P s = P s') :
    ExistsUnique (fun Q : Quotient (stratOrbit x) → Prop =>
      ∀ s, Q (Quotient.mk (stratOrbit x) s) = P s) := by
  refine ⟨Quotient.lift P hP, fun _ => rfl, ?_⟩
  intro Q' hQ'
  funext q
  refine Quotient.inductionOn q ?_
  intro s
  exact hQ' s

/-- Swappability factors through the stratum, uniquely -
`SwappableStratum` is THE predicate on the quotient reproducing
swappability at every point. -/
theorem swappableStratum_unique (x : Card) :
    ExistsUnique (fun Q : Quotient (stratOrbit x) → Prop =>
      ∀ s, Q (Quotient.mk (stratOrbit x) s) = SwappableIn s.val x) :=
  stratOrbit_universal x (fun s => SwappableIn s.val x)
    (fun _ _ h => propext (swappable_stratum_invariant x h))

#print axioms swappable_stratum_invariant
#print axioms SwappableStratum
#print axioms swappableStratum_mk
#print axioms stratOrbit_universal
#print axioms swappableStratum_unique
