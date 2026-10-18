import Orig.PairClass
import Orig.ForkDescent

/-!
# Orig.PairClassRead — the capstone's descent-side addenda

THE CONTEXT (the descent program's full-head attack, the no-re-arm
flank): `Orig/ForkDescentProbe.lean`'s ladder is split by the probe
rounds — the corpus form (pull-play landings) is rung-monotone by its
own banked deltas, the equality draft is refuted twice over by
independent boards, and the surviving `≤` head's honest remainder is
the mint-survival weave (G2′) over raise-riding witness journeys.
THIS LEAF banks the two class-grade rows that close that weave's
adversary's cheapest refuels — the RE-ARM moves — off
`Orig.PairClass.lean`'s capstone `forkState_pairClass`:

* **THE FORK-INDEX CLASS INVARIANT** `fork_index_class_invariant`
  — any class-mate hosting ANY fork reads the twin suit at the fork
  point EXACTLY.  The capstone pins the mate's witness into the pair
  (`y = x ∨ y = x.twin`), and since `x.twin` is a member of the
  mate's pair EITHER WAY, the pair's own saturation pins the twin
  suit's rung at the pair rank — the fork index is a CLASS
  INVARIANT, orientation-stable (both legal orientations of the one
  pair read the same twin frontier; `forkState_orientationUnique`
  already bars ambivalence within a single member).

* **THE OFF-INDEX EXCLUSION** `class_no_fork_off_index` — a
  class-mate reading the twin suit anywhere OFF the fork point hosts
  NO fork at all.  THE LADDER'S USE: every member of the crossing
  ladder's tail — from the first raised target (`j + 1`) to the
  elevated stall itself (`k' > j`) — is FORK-FREE, so the interleave
  adversary's refuels reduce to the letter-confined
  ordinary-arrangement moves: a same-pair re-fork needs the twin
  read back AT `j`; a higher-pair fork is barred by the capstone's
  own rank sandwich (`forkState_family_pairClass`);
  the other color family is barred by `forkState_familyRigid`.  This
  is the class-grade form of the meddler laws the probe rounds
  verified board-by-board (§2R2/§2R3: any would-be second pair
  develops an unavoidable S-live singleton).

G2′ HONESTY NOTE: these rows constrain FORK-BEARING members only;
the mint-survival ledger at the fork-free tail members is the named
open weave and is not touched here — the fdR expose-raise family
refilled with NO fork present, so the no-re-arm lemma is a flank of
the kill, never the kill.  The sibling leaf `Orig.PairClassZones`
(fork-grade per-zone residency agreement) carries the complementary
profile-invariance the weave wants.

House compliance: additive leaf (`Orig.PairClass` +
`Orig.ForkDescent` consumed — the capstone for the pin, the descent
side for the member-WF grade `descent_class_wf`; nothing below this
file imports it); BOLD names; every fresh head audited below; zero
`sorry`, zero `Classical.choice`. -/

/-! ## §1. The addenda -/

set_option linter.unusedVariables false in
/-- **THE FORK-INDEX CLASS INVARIANT** — within one macro class, any
fork-bearing member reads the twin suit at the fork point `x.rank.toIdx`
exactly, whatever pair orientation its own fork carries: the capstone
pins its witness into `{x, x.twin}`, and `x.twin` then saturates in ITS
pair (the twin slot if the witness is `x`, the witness slot itself if
the witness is `x.twin`), so `canRaiseS_rung` pins the rung — the
`fork_self_low` computation, broadcast from the host to every
fork-bearing class-mate by the capstone. -/
theorem fork_index_class_invariant {st m : State}
    (hwf₁ : st.WF) (hwf₂ : m.WF)
    (hcls : sameOrbitSetoid.r st m)
    (x : Card) (hx : ForkWitness st x)
    {y : Card} (hy : ForkWitness m y) :
    rungAt m x.twin.suit = x.rank.toIdx := by
  have hS : CanRaiseS m x.twin := by
    rcases forkState_pairClass st m hwf₁ hwf₂ hcls x hx hy with hyx | hyt
    · exact (hy.1 x.twin).mp (Or.inr (by rw [hyx]))
    · exact (hy.1 x.twin).mp (Or.inl hyt.symm)
  have h2 := canRaiseS_rung hS
  rw [Card.twin_rank] at h2
  exact h2

/-- **THE OFF-INDEX EXCLUSION** — a class-mate reading the twin suit
anywhere OFF the fork point hosts NO fork: the member's WF grade rides
the banked class row (`descent_class_wf`), and the invariant above then
forces the read back to the fork point.  The crossing ladder's tail
(reading strictly above `j`) is therefore fork-free — the route
lemma's no-re-arm lemma, class-grade: the interleave may not re-fuel
on a fresh forkUi anywhere past the crossing. -/
theorem class_no_fork_off_index {st m : State}
    (hwf : st.WF)
    (hcls : sameOrbitSetoid.r st m)
    (x : Card) (hx : ForkWitness st x)
    (hread : rungAt m x.twin.suit ≠ x.rank.toIdx) :
    ¬ ∃ y, ForkWitness m y := by
  rintro ⟨y, hy⟩
  have hmwf : m.WF := descent_class_wf hwf hcls
  exact hread (fork_index_class_invariant hwf hmwf hcls x hx hy)

/-! ## The audit battery

Both fresh heads read zero-sorry: the capstone's own battery
(`[propext, Quot.sound]`) carries through the fork-index broadcast,
and `descent_class_wf`'s grade through the exclusion — no
`Classical.choice` inflow at any depth. -/

#print axioms fork_index_class_invariant
#print axioms class_no_fork_off_index
