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

/-- `Dominates s s'`: `s` is at least `s'` on every rung coordinate.  In this
case the join is trivial: `s` itself is the componentwise maximum. -/
def Dominates (s s' : State) : Prop := ∀ σ : Suit, rungAt s' σ ≤ rungAt s σ

/-- If `s` dominates `s'`, `s` is the join. -/
theorem joinAt_self_of_dominates {s s' : State} {t : Suit}
    (h : Dominates s s') : JoinAt s s' s t := by
  refine ⟨RevEqW_refl s, ?_, ?_⟩
  · exact (Nat.max_eq_left (h t)).symm
  · exact (Nat.max_eq_left (h t.twin)).symm

/-- If `s'` dominates `s`, `s'` is the join (given the class relation). -/
theorem joinAt_other_of_dominates {s s' : State} {t : Suit}
    (hcls : sameOrbitSetoid.r s s') (h : Dominates s' s) :
    JoinAt s s' s' t := by
  refine ⟨hcls, ?_, ?_⟩
  · exact (Nat.max_eq_right (h t)).symm
  · exact (Nat.max_eq_right (h t.twin)).symm

/-- **THE DOMINATION CASE IS TRIVIAL.**  If one endpoint dominates the other
on every coordinate, the join is that endpoint. -/
theorem join_or_fork_of_dominates {s s' : State} {t : Suit}
    (hcls : sameOrbitSetoid.r s s') (h : Dominates s s' ∨ Dominates s' s) :
    (∃ s''', JoinAt s s' s''' t) ∨
    (∃ F x, sameOrbitSetoid.r s F ∧ ForkWitness F x) := by
  rcases h with h | h
  · exact Or.inl ⟨s, joinAt_self_of_dominates h⟩
  · exact Or.inl ⟨s', joinAt_other_of_dominates hcls h⟩

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
    s.WF →
    ShufflePlayW s ρ s' → SignSwap s s' t → DipExists s s' t ρ

/-- **THE TARGET (SATURATION-FREE).**  Two WF class-mates with a twin-pair
sign swap: either the componentwise maximum is joined by a class-mate, or the
class carries a fork witness.  NO `SSaturated` at either endpoint.  OPEN: the
`3c` case (both twins covered at the dip) lives inside the join disjunct. -/
def TwinJoinOrForkTarget : Prop :=
  ∀ (s s' : State) (t : Suit),
    s.WF → s'.WF → sameOrbitSetoid.r s s' →
    SignSwap s s' t →
    (∃ s''', JoinAt s s' s''' t) ∨
    (∃ F x, sameOrbitSetoid.r s F ∧ ForkWitness F x)

/-- The **overshoot join**: a class-mate whose twin-pair columns are at least
the componentwise maximum (not exactly equal to it).  This is the relaxation
that makes the overshoot case trivial. -/
def JoinAtLeast (s s' s''' : State) (t : Suit) : Prop :=
  sameOrbitSetoid.r s s''' ∧
    Nat.max (rungAt s t) (rungAt s' t) ≤ rungAt s''' t ∧
    Nat.max (rungAt s t.twin) (rungAt s' t.twin) ≤ rungAt s''' t.twin

/-- The exact join is an overshoot join. -/
theorem joinAt_imp_joinAtLeast {s s' s''' : State} {t : Suit}
    (h : JoinAt s s' s''' t) : JoinAtLeast s s' s''' t := by
  obtain ⟨horb, h1, h2⟩ := h
  refine ⟨horb, ?_, ?_⟩
  · rw [h1]; exact Nat.le_refl _
  · rw [h2]; exact Nat.le_refl _

/-- **THE OVERSHOOT CASE IS IMMEDIATE.**  If the dip level is already at least
both endpoint colour maxima, the dip itself is the overshoot join.  So the
bounded-dip lemma is not needed on this side. -/
theorem joinAtLeast_of_dip_above {s s' x : State} {t : Suit} {r : Nat}
    (hclass : sameOrbitSetoid.r s x)
    (hdip : rungAt x t = r ∧ rungAt x t.twin = r)
    (habove : Nat.max (rungAt s t) (rungAt s' t) ≤ r ∧
      Nat.max (rungAt s t.twin) (rungAt s' t.twin) ≤ r) :
    JoinAtLeast s s' x t := by
  refine ⟨hclass, ?_, ?_⟩
  · rw [hdip.1]; exact habove.1
  · rw [hdip.2]; exact habove.2

/-- **THE RELAXED TARGET.**  Sign swap ⇒ an overshoot join or a fork.  This is
weaker than `TwinJoinOrForkTarget` (the exact join), and it is what to prove
first: the dip-above-goal case is already a theorem, and the remaining case is
the dip below the goal. -/
def TwinJoinOrForkOvershoot : Prop :=
  ∀ (s s' : State) (t : Suit),
    s.WF → s'.WF → sameOrbitSetoid.r s s' →
    SignSwap s s' t →
    (∃ s''', JoinAtLeast s s' s''' t) ∨
    (∃ F x, sameOrbitSetoid.r s F ∧ ForkWitness F x)

/-- The exact target implies the relaxed one. -/
theorem overshoot_of_exact (h : TwinJoinOrForkTarget) : TwinJoinOrForkOvershoot := by
  intro s s' t hs hs' hcls hswap
  rcases h s s' t hs hs' hcls hswap with hjoin | hfork
  · obtain ⟨z, hz⟩ := hjoin
    exact Or.inl ⟨z, joinAt_imp_joinAtLeast hz⟩
  · exact Or.inr hfork

/-- **THE ARGMIN STEP (game level).**  From a state strictly below a class-mate
on both twin suits, some class-mate has the smaller twin rung increased by one
and the other twin rung unchanged.  The rung-level staircase is trivial; the
content is that the game step exists.  The intended proof is `prepare_neutral`:
prepare the argmin's next card with rung-neutral moves, then raise it.

OPEN — the AS probe is testing it. -/
def ArgminStepGame : Prop :=
  ∀ (s s' : State) (t : Suit),
    sameOrbitSetoid.r s s' →
    rungAt s t < rungAt s' t →
    rungAt s t.twin < rungAt s' t.twin →
    ∃ s'', sameOrbitSetoid.r s s'' ∧
      ((rungAt s t ≤ rungAt s t.twin ∧
          rungAt s'' t = rungAt s t + 1 ∧
          rungAt s'' t.twin = rungAt s t.twin)
       ∨ (rungAt s t.twin ≤ rungAt s t ∧
          rungAt s'' t = rungAt s t ∧
          rungAt s'' t.twin = rungAt s t.twin + 1))

/-- **The join is symmetric under swapping the endpoints** (given the class
relation). -/
theorem joinAt_swap {s s' s''' : State} {t : Suit}
    (hcls : sameOrbitSetoid.r s s') (h : JoinAt s s' s''' t) :
    JoinAt s' s s''' t := by
  obtain ⟨horbit, h1, h2⟩ := h
  refine ⟨RevEqW_trans horbit (RevEqW_symm hcls), ?_, ?_⟩
  · calc
      rungAt s''' t = Nat.max (rungAt s t) (rungAt s' t) := h1
      _ = Nat.max (rungAt s' t) (rungAt s t) := by
        simpa using Nat.max_comm (rungAt s t) (rungAt s' t)
  · calc
      rungAt s''' t.twin = Nat.max (rungAt s t.twin) (rungAt s' t.twin) := h2
      _ = Nat.max (rungAt s' t.twin) (rungAt s t.twin) := by
        simpa using Nat.max_comm (rungAt s t.twin) (rungAt s' t.twin)

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
