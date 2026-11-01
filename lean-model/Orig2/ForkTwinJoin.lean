import Orig2.ForkMeetCover

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# TwinJoin - the sign-swap / dip / join formulation of T

This file states the theorem the campaign's T half is aiming at, without
claiming it.  The two pieces are:

* `DipExists` - the IVT: a twin-pair order flip on a play gives a dual dip.
  This is PROVABLE from the unit-step rung lemmas; it is stated here as a
  `def` so the open part is not confused with it.

* `TwinJoinOrForkTarget` - T: at the componentwise maximum of the twin-pair
  columns, either a class-mate joins both columns, or the class carries a
  `ForkWitness`.  This is OPEN.  The `3c` case (both covered) is inside the
  join disjunct: the join must be constructed there.

The `SignSwap` hypothesis is the *pairwise* order flip, NOT the crossed
endpoint values (`rungAt s t > rungAt s' t`, `rungAt s t.twin < rungAt s' t.twin`).
The crossed values are the trade-off (V); the sign swap is what the IVT needs.
-/

namespace TwinJoin

/-- The pairwise order flip on the twin pair `{t, t.twin}`: at one endpoint
`t` is at least its twin, at the other the reverse.  This is the IVT's
hypothesis, not the crossed/trade-off hypothesis. -/
def SignSwap (s s' : State) (t : Suit) : Prop :=
  (rungAt s t.twin ≤ rungAt s t ∧ rungAt s' t ≤ rungAt s' t.twin) ∨
  (rungAt s' t.twin ≤ rungAt s' t ∧ rungAt s t ≤ rungAt s t.twin)

/-- The join: a class-mate of `s` carrying both twin-pair columns at their
componentwise maximum. -/
def JoinAt (s s' s''' : State) (t : Suit) : Prop :=
  sameOrbitSetoid.r s s''' ∧
    rungAt s''' t = Nat.max (rungAt s t) (rungAt s' t) ∧
    rungAt s''' t.twin = Nat.max (rungAt s t.twin) (rungAt s' t.twin)

/-- The IVT conclusion on a fixed play: some prefix state has equal twin-pair
rungs.  `s.run (ρ.take i) = some x` names the prefix state. -/
def DipExists (s s' : State) (t : Suit) (ρ : List Move) : Prop :=
  ∃ (i : Nat) (x : State),
    s.run (ρ.take i) = some x ∧ rungAt x t = rungAt x t.twin

/-- **THE IVT STEP (provable).**  A sign swap on a play gives a dip.  The
proof is the unit-step integer walk on `d = rungAt · t - rungAt · t.twin`:
every letter changes one rung by at most 1, so `d` steps by `-1`, `0`, or `+1`
and cannot jump over zero.  Stated as a `def` so it is not mistaken for the
open content. -/
def DipLemma : Prop :=
  ∀ (s s' : State) (t : Suit) (ρ : List Move),
    s.WF → SSaturated s' →
    ShufflePlayW s ρ s' → SignSwap s s' t → DipExists s s' t ρ

/-- **THE TARGET (one-sided in `s`).**  A saturated target endpoint `s'` and
a class-mate `s` with a twin-pair sign swap: either the componentwise maximum
is joined by a class-mate, or the class carries a fork witness.  `SSaturated s`
is deliberately NOT assumed.  OPEN: the `3c` case (both twins covered at the
dip) lives inside the join disjunct. -/
def TwinJoinOrForkTarget : Prop :=
  ∀ (s s' : State) (t : Suit),
    s.WF → s'.WF → sameOrbitSetoid.r s s' →
    SSaturated s' → SignSwap s s' t →
    (∃ s''', JoinAt s s' s''' t) ∨
    (∃ F x, sameOrbitSetoid.r s F ∧ ForkWitness F x)

/-- The local engine at a dip, with the three cases explicit.  `CoveredStall`
is the `3c` residual, named here as a `Prop` over the dip state.  The target
above is the iterate-to-the-max of this step; the join branch of `3c` is what
must be built. -/
def CoveredStall (x : State) (c : Card) : Prop :=
  rungAt x c.suit = c.rank.toIdx ∧ rungAt x c.twin.suit = c.rank.toIdx ∧
    ¬ CanRaise x c ∧ ¬ CanRaise x c.twin

/-- The local step: at a dip where both twin suits sit at the rank of the
card `c`, either one level of join (raise `c` and `c.twin`), or a fork, or the
covered/covered stall.  OPEN only at the stall; 3a/3b are assembly of
`fork_exists_of_asymmetry` / the raise-both step. -/
def DipStepOrFork : Prop :=
  ∀ (x : State) (c : Card),
    x.WF →
    rungAt x c.suit = c.rank.toIdx ∧ rungAt x c.twin.suit = c.rank.toIdx →
    (∃ y, sameOrbitSetoid.r x y ∧
        rungAt y c.suit = c.rank.toIdx + 1 ∧
        rungAt y c.twin.suit = c.rank.toIdx + 1)
    ∨ (∃ F w, sameOrbitSetoid.r x F ∧ ForkWitness F w)
    ∨ CoveredStall x c

/-- The reduction: the local step plus termination of the climb gives the
target.  Termination is `rungAt ≤ 13` (the deck); the proof is an induction
on the remaining distance to the maximum.  This is the assembly, not the
open case. -/
def TargetOfStep : Prop :=
  DipStepOrFork → TwinJoinOrForkTarget

end TwinJoin
