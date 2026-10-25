import Orig2.TwinPointTransfer
import Orig2.TwinLastPull

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false

/-!
# Orig2.TwinPairFreeTransfer — the pair-free transfer, DISCHARGED

The owner's stepping-stone toward the corrected fiber transfer
(`fiber_transfer_corrected`, `Orig2/ClaimsScrutiny.lean:248`): prove the
transfer FIRST under the added condition that the class journey can be
traversed without touching the twin — a `NotFoundPair` witness play
(`Orig2/TwinEquivariance.lean:800`: never a `tabToFound`/`foundToTab` of
either twin).

The two grades already in-tree, and this card's delta:

* `Orig2/TwinTransferRiderFree.lean` — the RIDER-FREE instance: the
  strict-swap target is the relabeling (`TwinSwapUnique`), the transfer
  rides the relabeling equivariance.  Its docstring leaves the
  rider-general case as "the next card's content".
* `Orig2/TwinPointTransfer.lean` — the RIDER-GENERAL chain, but with the
  point-hom square `sameOrbitSetoid.r (s.spliceTwinRuns x)
  (t.spliceTwinRuns x)` as a HYPOTHESIS (`hpoint`).
* THIS CARD — the square is discharged from the play itself: the splice
  functor on pair-free plays
  `TwinLastPull.pairFreeOrbit_splice_of_pairFree`
  (`Orig2/TwinLastPull.lean:201`) transports the witness play to the run
  splices, and its class-read IS `hpoint`.

Assembly only — three landed rows, zero new content:

```
hplay' : ShufflePlayW (s.spliceTwinRuns x) play' (t.spliceTwinRuns x)  (the functor)
hpoint := sameOrbitSetoid.symm (shufflePlayW_revEqW hplay')             (the class-read)
swappableIn_transfer_point_pairFree … hpoint hswap                       (the chain)
```

HONEST SCOPE: this banks the AWAY half of the transfer at the
rider-general grade.  The full `fiber_transfer_corrected` still owes
exactly the touching letters (the pair-foundation excursions of
`TwinExcursionClosure` / `LastPullCancellation`): a class journey that
raises or pulls a twin is NOT covered.  Note the founds row of the
ledger stub is NOT needed here — the pair-free splice functor never
reads founds, so the journey may change them via other cards'
`wasteToFound` letters.

Zero `sorry`, zero `Classical.choice`.
-/

open State

/-- **The pair-free transfer, discharged (the owner's stepping-stone).**
If the twins are seated on `.inr` parents at both ends of a `NotFoundPair`
witness play `s → t`, then `SwappableIn` transfers — the point-hom
square of `swappableIn_transfer_point_pairFree` follows from the play by
the splice functor. -/
theorem swappableIn_transfer_of_pairFreePath
    {s t : State} {x : Card} {play : List Move}
    (hwf : s.WF) (hwf' : t.WF)
    (hxs : ∃ z, seatOf s x = some (Sum.inr z))
    (hxts : ∃ z : Card, seatOf s x.twin = some (Sum.inr z.twin))
    (hxt : ∃ z, seatOf t x = some (Sum.inr z))
    (hxtt : ∃ z : Card, seatOf t x.twin = some (Sum.inr z.twin))
    (hplay : ShufflePlayW s play t)
    (hno : ∀ m ∈ play, NotFoundPair x m)
    (hswap : SwappableIn s x) :
    SwappableIn t x := by
  obtain ⟨play', hplay', -⟩ :=
    TwinLastPull.pairFreeOrbit_splice_of_pairFree hwf hxs hxts hplay hno
  exact swappableIn_transfer_point_pairFree hwf hwf' hxs hxts hxt hxtt hplay hno
    (sameOrbitSetoid.symm (shufflePlayW_revEqW hplay')) hswap

#print axioms swappableIn_transfer_of_pairFreePath

/-- **The ledger-stub shape, restricted to pair-free journeys.**  The
corrected fiber transfer's statement with the class row STRENGTHENED to
`PairFreeOrbit x s s'` (a witness play that never raises or pulls either
twin); the founds row is dropped — the proof does not read it, so the
journey may change founds via other cards' letters.  `SwappableIn` is
definitionally the stub's existential shape (`Orig2/Vocab.lean`), so the
conclusion is the stub's verbatim. -/
theorem fiber_transfer_corrected_of_pairFreePath :
    ∀ (s s' : State) (x : Card), s.WF → s'.WF →
      PairFreeOrbit x s s' →
      (∃ z, seatOf s x = some (Sum.inr z)) →
      (∃ z : Card, seatOf s x.twin = some (Sum.inr z.twin)) →
      (∃ z, seatOf s' x = some (Sum.inr z)) →
      (∃ z : Card, seatOf s' x.twin = some (Sum.inr z.twin)) →
      (∃ v, twinPairSwapStrict s v x ∧ sameOrbitSetoid.r s v) →
      (∃ v', twinPairSwapStrict s' v' x ∧ sameOrbitSetoid.r s' v') := by
  intro s s' x hwf hwf' hfree hxs hxts hxt hxtt hswap
  obtain ⟨play, hplay, hno⟩ := hfree
  exact swappableIn_transfer_of_pairFreePath hwf hwf' hxs hxts hxt hxtt
    hplay hno hswap

#print axioms fiber_transfer_corrected_of_pairFreePath
