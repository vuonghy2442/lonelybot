import Orig2.Vocab

set_option linter.unusedSectionVars false

/-!
# Orig2.VacuousSwap — the degenerate case of `SwappableIn`

When BOTH twins are unseated (hidden, foundation, stock, or waste —
any mix), `SwappableIn` holds TRIVIALLY: the seat-exchange fields of
`twinPairSwapStrict` (Vocab.lean) compare `none = none`, and the
swap state is `s` itself, with every "fixed" field reflexive.

This is NOT a real exchange — it is the letter of the definition,
which was designed for seated pairs.  The observation matters twice:

1. it is the hinge of the proposed refutation of the original
   `fiber_transfer_corrected` (ClaimsScrutiny.lean:249): the premise
   holds vacuously where the twins are off the board (e.g. dealt
   hidden), while the conclusion — at a state where the twins are
   revealed `.inl` pile-bottoms — fails by the anchor-invariance
   argument (a non-king seated at a pile bottom never moves to a
   DIFFERENT bottom: re-entering an anchor is king-gated);
2. it locates the repair: the `.inr`-seat amendment to the transfer
   statement exists precisely to keep this vacuous case out of the
   premise (the amended version requires both twins seated on card
   parents at both ends).

Whether the vacuous case is read as a refutation of the statement
(the definition is the library's ground truth) or as a definition
bug (`SwappableIn` was meant for seated pairs) is an owner decision;
this card certifies the mechanism either way.
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
