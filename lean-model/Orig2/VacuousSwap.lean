import Orig2.Vocab

set_option linter.unusedSectionVars false

/-!
# Orig2.VacuousSwap — the degenerate case of `SwappableIn`

When BOTH twins are unseated (hidden, foundation, stock, or waste —
any mix), `SwappableIn` holds TRIVIALLY: the seat-exchange fields of
`twinPairSwapStrict` (Vocab.lean) compare `none = none`, and the
swap state is `s` itself, with every "fixed" field reflexive.

This is NOT a real exchange — it is the letter of the definition,
which was designed for seated pairs.  What the observation certifies:

1. CORRECTION 2026-10-25 (owner: "revealed is not reversible"): an
   earlier draft of this docstring offered the vacuous case as the
   hinge of a refutation of the original `fiber_transfer_corrected`
   (ClaimsScrutiny.lean:249) — twins dealt hidden (premise vacuous),
   revealed to `.inl` pile-bottoms (conclusion failing by anchor
   invariance).  That channel is DEAD: the hidden deck only ever
   shrinks (`revealTop` is its only writer, Orig/State.lean:277),
   a reveal is never exactly undone, and no `sameOrbit` journey
   contains one — the hidden-twins construction cannot satisfy the
   `sameOrbit` premise at all.
2. What the vacuous case actually certifies: `SwappableIn` at a
   both-unseated pair is EMPTY evidence — the witness is `s` itself,
   nothing is exchanged.  In the transfer statement's picture this
   is the both-off-board corner: the premise holds for free there,
   but no reversible journey can seat the pair (a foundation twin
   is pinned by the founds-equality row; stock/waste/hidden
   boarding requires an irreversible step) — the corner is
   vacuous, not failing.
3. It locates the repair: the `.inr`-seat amendment to the transfer
   statement keeps this vacuous case out of the premise by
   demanding seated card-parent witnesses at both ends.

Whether `SwappableIn` itself should ask for seats (a definitional
patch) remains an owner decision; what is off the table, by the
reveal ratchet, is the refutation reading.
-/

open State

/-- **The vacuous swap.**  Both twins unseated ⟹ `SwappableIn`
holds trivially — witness `s` itself; the exchange is `none = none`.
A definition-level observation, zero content. -/
theorem swappableIn_of_both_unseated {s : State} {x : Card}
    (h1 : seatOf s x = none) (h2 : seatOf s x.twin = none) :
    SwappableIn s x :=
  ⟨s, ⟨h1.trans h2.symm, h2.trans h1.symm, fun y _ _ => rfl,
    ⟨fun _ => rfl, rfl⟩, fun _ => rfl, rfl, rfl, rfl⟩,
    sameOrbitSetoid.iseqv.refl s⟩

#print axioms swappableIn_of_both_unseated
