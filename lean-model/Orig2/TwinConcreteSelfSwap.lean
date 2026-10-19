import Orig2.TwinBothCovered
import Orig2.TwinPreludePath

/-!
# Temp/TwinConcreteSelfSwap — the concrete world-B self-swap segment

The private five-leg play `TwinBothCovered.play5` runs from world B to
the strict twin run splice at `Q♠` (`TwinBothCovered.v5_eq_splice`).
Through the public aliases this is exactly a `SelfSwapSeg`, so the
self-swap transfer applies.

The only axioms are `propext` and `Quot.sound`.
-/

open State
open TwinBothCovered

/-- **The concrete 5L self-swap block at world B.**  The five legs are a
play from `uBpub` to `uBpub.spliceTwinRuns cQSpub`, and both twins are
`.inr`-seated at the source. -/
theorem selfSwapSeg_uB :
    SelfSwapSeg cQSpub uBpub (uBpub.spliceTwinRuns cQSpub) play5pub :=
  ⟨uBpub_wf, uBpub_seats.1, uBpub_seats.2,
   by simpa [v5pub_eq_splice] using play5pub_shuffle, rfl⟩

/-- The concrete swap at world B, through the public alias. -/
theorem swappableIn_uBpub : SwappableIn uBpub cQSpub :=
  swappableIn_uB_cQSpub

/-- Consistency check against `swappableIn_transfer_selfSwap`: the
concrete swap transported along the self-swap segment lands at the
spliced endpoint. -/
theorem swappableIn_splice_uBpub :
    SwappableIn (uBpub.spliceTwinRuns cQSpub) cQSpub :=
  swappableIn_transfer_selfSwap selfSwapSeg_uB swappableIn_uBpub

#print axioms selfSwapSeg_uB
#print axioms swappableIn_uBpub
#print axioms swappableIn_splice_uBpub
