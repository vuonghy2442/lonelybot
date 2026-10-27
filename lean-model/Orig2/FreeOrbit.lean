import Orig2.CargoRaise
import Orig2.SeatMateStack
import Orig2.Integrity

/-!
# Orig2.FreeOrbit — THE FREE-CARD ORBIT INVARIANCE (the campaign card)

THE MISSION (owner line 2026-10-27): the tableau-readiness probe
`freeCardS` is an (orbit, rung-tuple) invariant:

  `sameOrbitSetoid.r s s' → (∀ σ, rungAt s σ = rungAt s' σ) →
   ∀ c, freeCardS s c = freeCardS s' c`

— the strongest invariance row in the campaign.  With
`canRaiseS_split` (the license = foundation-gate ∧ readiness) and
`nextUp`'s tuple-determination, the CanRaiseS SETS then agree at
equal rungs — the residue (`SatDifferFork`) is thereby confined to
the rung ledger, exactly as its route (the LIFO exodus, the
first-passage twin-raise) assumes.

THE LETTER TABLE (the per-step induction substrate): a `ShufflePlayW`
is a `Walk` at `reversibleAtW`, and the two waste letters are never
reversible (in-tree), so the induction splits over four letters:

* `draw` — the pool set is preserved (recycle reverses, dealing
  splits); no pile is touched.
* `tabToTab` — the cargo oracle `tabToTabR`: below ≠ [] ∨ bare-king;
  the step's `afterRunRemoved` reveals only at an empty prefix, so
  no letter of this shape reveals; run members keep their parents,
  the head lands on a parent.
* `tabToFound` — the raise oracle `tabToFoundR`: nextUp ∧ top ∧
  (chop ≠ [] ∨ hidden = [] ∧ king); the step writes
  `afterRunRemoved p (chop p.faceUp)` — reveals fire only at
  chop = [], and both oracle arms exclude that with hidden ≠ [].
* `foundToTab` — the pull oracle `foundToTabR`; `putCard` touches no
  hidden deck; a non-king landing is `inr` (`canPlace_inl` requires
  king).

THE ARCHITECTURE (the four sections, landing in proof order):

* THE SEAT ROWS (landed first) — parented-ness (non-kings: sits on
  something) and bareness (kings: the face-up bottom, seat-arm
  `hidden = []`) are invariants.  Bare non-king bottoms are frozen
  (the cargo oracle's king-check; the raise oracle's bare-non-king
  bar); parented cards stay parented (run slides keep members
  parented, excursion returns are `inr` for non-kings).  The
  TWO-SEAT LEMMA is the cornerstone: a card's legal parents are one
  twin pair, so SEATED = PARENTED and no move takes a card to a
  parent outside the pair it started in.
* THE ZONE ROWS — the face-up set is (orbit, tuple)-invariant:
  `found` from the tuple and canonical prefixes (`found_prefix`),
  the hidden decks per pile from `rev_step_hidden_eq`
  (SeatMateStack, public), the pool set from the draw row, the zone
  census from `mem_pile_unique`.  This row also delivers the
  EXCURSION CLOSURE: every card raised mid-journey returns (its
  face-up membership is an endpoint fact).
* THE HATCH FACTORIZATION — `freeCardS`'s last clause is
  ¬(covered c ∧ covered c.twin) on the twin-face-up slice and
  ¬covered(c) on the other; both reduce to the PARENTED-COUNT of
  the sitter pair (two-seat again — the sitters of a parent pair
  are themselves one twin pair).
* THE ASSEMBLY — the theorem and the CanRaiseS-set corollary.

House compliance: additive leaf (`Orig2.CargoRaise` for the probe
and the split, `Orig2.SeatMateStack` for the fit arithmetic and the
hidden ledger, `Orig2.Integrity` for the census); zero `sorry`, zero
`Classical.choice`; the battery at the tail.
-/

/-! ## §1. The seat rows — the two-seat lemma (the cornerstone) -/

/-- The two-color pigeonhole.  Lineage: `Orig2/SeatMateStack.lean`'s
private `color_eq_of_ne` — restated here per the kit rule rather
than widening that card's surface. -/
private theorem color_eq_of_ne {a b z : Color} (h1 : a ≠ z) (h2 : b ≠ z) :
    a = b := by
  cases a <;> cases b <;> cases z <;> simp_all

/-- **THE TWO-SEAT LEMMA, PAIR-CLOSURE FORM** — any two legal parents
of one card are equal or twins: a card's sitting options are exactly
one twin pair.  The campaign's cornerstone — SEATED = PARENTED (a
parented card sits somewhere in ITS pair), and no move can take a
card to a parent outside the pair it started in.  Lineage: the
arithmetic over `canSitOn_eq` (Orig/Basic, the seam) +
`card_eq_twin_of_rank_color` (SeatMateStack, public). -/
theorem canSitOn_twin_pair {u z z' : Card}
    (hz : canSitOn u z = true) (hz' : canSitOn u z' = true) :
    z' = z ∨ z' = z.twin := by
  obtain ⟨hrank, hcol⟩ := (canSitOn_eq u z).mp hz
  obtain ⟨hrank', hcol'⟩ := (canSitOn_eq u z').mp hz'
  have hr : z'.rank = z.rank := Rank.toIdx_inj (by omega)
  have hc : z'.suit.color = z.suit.color :=
    color_eq_of_ne hcol'.symm hcol.symm
  exact card_eq_twin_of_rank_color hr hc

/-! ## §9. The battery -/

#print axioms canSitOn_twin_pair
