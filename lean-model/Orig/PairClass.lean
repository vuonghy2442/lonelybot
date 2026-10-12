import Orig.OriginLock
import Orig.CrossFamily

/-!
# Orig.PairClass — THE NO-LOCK PAIRCLASS THEOREM

The program's CAPSTONE: within one macro class, ANY two forks agree as
pairs — the second fork's witness is the first's or its twin.  The
family assembly row `forkState_family_pairClass` (`Orig.OriginLock`)
proves the pair agreement UNDER a family premise
(`y.suit = x.suit ∨ y.suit = x.twin.suit`); the capstone DERIVES that
premise — a class can never host forks of both color families — and
so closes the pairClass story with NO family hypothesis assumed.
The assembly, piece by piece:

* **THE CROSS-FAMILY HALF** — `forkState_familyRigid`
  (`Orig.CrossFamily`): within one class a fork cannot witness the
  OTHER color family; its conclusion is carried in the falsifier-facing
  form `¬ (y.suit.color ≠ x.suit.color)`, since the negated family
  flip is what the feed proof falsifies.
* **THE CONSTRUCTIVE COLOR RECOVERY** — the falsifier-facing form is
  a double negation, and `Color` is a two-constructor enum carrying
  `deriving DecidableEq` (`Orig/Basic.lean`), so CORE's
  `Decidable.not_not` — a theorem of the decidability instance; this
  project carries NO Mathlib and needs none for this step — recovers
  the positive form `y.suit.color = x.suit.color` constructively.
* **THE SUIT-FAMILY SPLIT** — same COLOR means the same SUIT or twin
  suits (the sixteen-cell suit enumeration, carried below as the
  private per-file copy `pc_suit_family`, per the house dedup
  discipline): exactly the shape of the family row's premise.
* **THE FAMILY PAIRCLASS HALF** — `forkState_family_pairClass`
  (`Orig.OriginLock`) consumes the disjunction: the family
  floor/ceiling sandwich forces `y.rank.toIdx = x.rank.toIdx`, and
  `forkState_sameFamily_samePair` reads the twin flip — that
  conclusion's twin-flip disjunct IS the capstone's answer.

Premise cards: the capstone's binders mirror the family assembly
row's witness-only shape (`hwf₁`/`hwf₂`, the class relation, and the
two `ForkWitness` premises); the cross-family half additionally
demands explicit `forkState st₁`/`forkState st₂` grades, minted here
from the witnesses through the trivial bridge `forkState_iff` —
neither half is weakened and no hypothesis is smuggled in.

House compliance: additive leaf (imports `Orig.OriginLock` and
`Orig.CrossFamily`, edits nothing); fresh private kit copy per the
dedup discipline; the fresh head audited (`#print axioms`).  The
`sorryAx` in the battery is INHERITED whole through the two halves'
named residues — the capstone itself adds none, and carries zero
`Classical.choice`.
-/

/-! ## §0. The private kit (per-file copy, the house dedup discipline) -/

/-- A same-color suit is the suit or its twin (the copy of
`Orig/CrossFamily.lean`'s private `xfam_suit_family`, itself the copy
of `Orig/PairConfine.lean`'s private `conf_suit_family`) — the
suit-family split backing the color recovery. -/
private theorem pc_suit_family {s t : Suit} (h : s.color = t.color) :
    s = t ∨ s = t.twin := by
  cases s <;> cases t <;> simp_all [Suit.color, Suit.twin]

/-! ## §1. The capstone -/

/-- **THE NO-LOCK PAIRCLASS THEOREM** (the program capstone) — within
one macro class ANY two forks agree as pairs: the second fork's
witness is the first's witness or its twin, with NO family hypothesis
assumed.  ROUTE (the assembly, three moves over the proved halves):
1. THE CLASS LOCK — `forkState_familyRigid` bars the other color
   family within the class, in the falsifier-facing form
   `¬ (y.suit.color ≠ x.suit.color)` (its explicit `forkState`
   premises minted from the witnesses via the trivial bridge
   `forkState_iff`).
2. THE CONSTRUCTIVE COLOR RECOVERY — the falsifier-facing read is a
   double negation; `Color` carries a derived `DecidableEq`, so
   core's `Decidable.not_not` recovers `y.suit.color = x.suit.color`
   with no classical expense.
3. THE FAMILY ROW — `pc_suit_family` splits the color into the
   suit-or-twin-suit disjunction, exactly the family premise of
   `forkState_family_pairClass`, whose conclusion's twin-flip
   disjunct is the capstone's answer. -/
theorem forkState_pairClass (st₁ st₂ : State) (hwf₁ : st₁.WF) (hwf₂ : st₂.WF)
    (hcls : sameOrbitSetoid.r st₁ st₂)
    (x : Card) (hx : ForkWitness st₁ x) {y : Card} (hy : ForkWitness st₂ y) :
    y = x ∨ y = x.twin := by
  have hf₁ : forkState st₁ := (forkState_iff).mpr ⟨x, hx⟩
  have hf₂ : forkState st₂ := (forkState_iff).mpr ⟨y, hy⟩
  have hrigid : ¬ (y.suit.color ≠ x.suit.color) :=
    forkState_familyRigid st₁ st₂ hwf₁ hwf₂ hf₁ hf₂ hcls hx hy
  have hcol : y.suit.color = x.suit.color :=
    (Decidable.not_not (p := _)).1 hrigid
  have hfam : y.suit = x.suit ∨ y.suit = x.twin.suit := by
    rcases pc_suit_family hcol with h | h
    · exact Or.inl h
    · exact Or.inr (h.trans (Card.twin_suit x).symm)
  exact (forkState_family_pairClass st₁ st₂ hwf₁ hwf₂ hcls x hx hy hfam).2

/-! ## The audit battery

`#print axioms forkState_pairClass` reads the expected capstone grade
`[propext, sorryAx, Quot.sound]`: the `sorryAx` is inherited whole
through the two proved halves' named residues and NOTHING fresh begins
here — the capstone's own glue (the `forkState_iff` bridge, core's
`Decidable.not_not` recovery, the private `pc_suit_family` copy, the
`Card.twin_suit` twin-flip transpose) adds no axiom — and there is NO
`Classical.choice` at any depth.  The private copy audits clean on its
own, `[propext]`-grade. -/

#print axioms pc_suit_family
#print axioms forkState_pairClass
