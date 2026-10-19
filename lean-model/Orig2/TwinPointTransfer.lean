import Orig2.TwinPointFunctor
import Orig2.TwinSpliceUnique
import Orig2.DetourKit

set_option linter.unusedSectionVars false

/-!
# Temp/TwinPointTransfer — the pair-free transfer of `SwappableIn`

The point object `s.spliceTwinRuns x` carries the swap of `x` and
`x.twin`; by `swappableIn_iff_orbit_splice`, `SwappableIn s x` is
exactly the orbit of that object at `s`.  A witness play `s → t` gives
`sameOrbitSetoid.r t s`, and the point-hom hypothesis
`sameOrbitSetoid.r (s.spliceTwinRuns x) (t.spliceTwinRuns x)` supplies
the corresponding orbit at `t`.  Transitivity of the reversible quotient
then yields `SwappableIn t x`.

Zero `sorry`, zero `Classical.choice`.
-/

open State

/-- **The pair-free point transfer.**  `SwappableIn` transfers along a
pair-free reversible play, given that the two run splices are in the
same orbit. -/
theorem swappableIn_transfer_point_pairFree
    {s t : State} {x : Card} {play : List Move}
    (hwf : s.WF) (hwf' : t.WF)
    (hxs : ∃ z, seatOf s x = some (Sum.inr z))
    (hxts : ∃ z : Card, seatOf s x.twin = some (Sum.inr z.twin))
    (hxt : ∃ z, seatOf t x = some (Sum.inr z))
    (hxtt : ∃ z : Card, seatOf t x.twin = some (Sum.inr z.twin))
    (hplay : ShufflePlayW s play t)
    (_hno : ∀ m ∈ play, NotFoundPair x m)
    (hpoint : sameOrbitSetoid.r (s.spliceTwinRuns x) (t.spliceTwinRuns x))
    (hswap : SwappableIn s x) :
    SwappableIn t x := by
  have h1 : sameOrbitSetoid.r s (s.spliceTwinRuns x) :=
    (swappableIn_iff_orbit_splice hwf hxs hxts).mp hswap
  have h2 : sameOrbitSetoid.r t s := shufflePlayW_revEqW hplay
  have h3 : sameOrbitSetoid.r t (s.spliceTwinRuns x) :=
    RevEqW_trans h1 h2
  have h4 : sameOrbitSetoid.r t (t.spliceTwinRuns x) :=
    RevEqW_trans hpoint h3
  exact (swappableIn_iff_orbit_splice hwf' hxt hxtt).mpr h4

#print axioms swappableIn_transfer_point_pairFree
