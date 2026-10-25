import Orig2.TwinRiderPath
import Orig2.TwinBothCovered
import Orig2.TwinSpliceUnique
import Orig2.TwinSplicePlay

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# Temp/TwinPreludePath — the both-covered self-swap prelude

The rider-general `RiderPath` exposes one twin as a pile top before the
frozen 3-leg recipe fires.  The remaining both-covered block has neither
twin on top, so it is not a recipe end.  Its geometric content is a
self-swap segment: a play whose endpoint is the run splice `splice s x`
itself.

Only the endpoint matters for `SwappableIn` transport.  By
`swappableIn_iff_orbit_splice`, the point swap at `s` is the orbit class
`sameOrbitSetoid.r s (s.spliceTwinRuns x)`.  At `w = s.spliceTwinRuns x`
the splice is an involution, so the same class read at `w` is the
symmetry of the class read at `s`; the moves inside the block are
irrelevant.

The `PreludePath` grammar duplicates `RiderPath` and adds the
`selfSwap` segment.  The producer at the end packages the abstract 5L
template (rider raise prelude, one-raise 3-leg recipe, physical
postlude).  The concrete `TwinBothCovered.v5_eq_splice` is private to
its module, so the endpoint equality is supplied as the postlude's
codomain here.

Zero `sorry`, zero `Classical.choice`.
-/

open State

/-! ## §1. The self-swap segment -/

/-- **`SelfSwapSeg x s w seg`** — a block played from `s` to
`w = s.spliceTwinRuns x`, with both twins `.inr`-seated at `s`.  The
moves `seg` are recorded but never inspected by the transfer. -/
def SelfSwapSeg (x : Card) (s w : State) (seg : List Move) : Prop :=
  s.WF ∧ (∃ z, seatOf s x = some (Sum.inr z)) ∧
  (∃ z : Card, seatOf s x.twin = some (Sum.inr z.twin)) ∧
  ShufflePlayW s seg w ∧ w = s.spliceTwinRuns x

/-! ## §2. The segment transfer -/

/-- **A strict-swap block is a self-swap segment.**  Rider-general uniqueness
identifies the block's endpoint with the run splice of its start, so any
`ShufflePlayW` block whose endpoint is a strict twin-swap target is a
`SelfSwapSeg`. -/
theorem selfSwapSeg_of_strict {s w : State} {x : Card} {seg : List Move}
    (hwf : s.WF) (hwf' : w.WF)
    (hx : ∃ z, seatOf s x = some (Sum.inr z))
    (hxt : ∃ z : Card, seatOf s x.twin = some (Sum.inr z.twin))
    (hstrict : twinPairSwapStrict s w x) (hplay : ShufflePlayW s seg w) :
    SelfSwapSeg x s w seg :=
  ⟨hwf, hx, hxt, hplay, eq_splice_of_twinPairSwapStrict hwf hwf' hx hxt hstrict⟩

/-- **The self-swap transfer.**  If `seg` ends at the run splice of `s`,
then `SwappableIn s x` transports to the endpoint.  The orbit row at
`s` reverses direction through the setoid symmetry; the endpoint's
splice is `s` by `spliceTwinRuns_invol`. -/
theorem swappableIn_transfer_selfSwap {s w : State} {x : Card} {seg : List Move}
    (h : SelfSwapSeg x s w seg) (hswap : SwappableIn s x) : SwappableIn w x := by
  obtain ⟨hwf, hx, hxt, _hplay, hw⟩ := h
  have hsw : sameOrbitSetoid.r s (s.spliceTwinRuns x) :=
    (swappableIn_iff_orbit_splice hwf hx hxt).mp hswap
  have hwf_w : w.WF := by
    rw [hw]
    exact wf_spliceTwinRuns hwf hx hxt
  have hinvol : w.spliceTwinRuns x = s := by
    rw [hw]
    exact spliceTwinRuns_invol hwf hx hxt
  obtain ⟨z, hz⟩ := hx
  obtain ⟨zt, hzt⟩ := hxt
  obtain ⟨a, ha, -, -⟩ := tfc_seatOf_of_inr hz
  obtain ⟨b, hb, -, -⟩ := tfc_seatOf_of_inr hzt
  have hab : a ≠ b := by
    intro hab
    rw [hab] at ha
    have hxmem : x ∈ (s.piles b).faceUp := pileHolding_mem ha
    have htmem : x.twin ∈ (s.piles b).faceUp := pileHolding_mem hb
    have heq : x = x.twin :=
      runOK_rank_distinct (hwf.runOK_of b) hxmem htmem rfl
    exact (card_twin_ne x) heq.symm
  have hw_x : ∃ z, seatOf w x = some (Sum.inr z) := by
    refine ⟨zt.twin, ?_⟩
    rw [hw, seatOf_splice_self hwf ha hb hab, hzt]
  have hw_xt : ∃ z : Card, seatOf w x.twin = some (Sum.inr z.twin) := by
    refine ⟨z.twin, ?_⟩
    rw [hw, seatOf_splice_twin hwf ha hb hab, hz, card_twin_twin]
  have htarget : sameOrbitSetoid.r w (w.spliceTwinRuns x) := by
    rw [hinvol]
    rw [hw]
    exact sameOrbitSetoid.symm hsw
  exact (swappableIn_iff_orbit_splice hwf_w hw_x hw_xt).mpr htarget

/-! ## §3. The prelude grammar -/

/-- **`PreludePath x s play s'`** — the rider-general point path with a
self-swap prelude segment.  The constructors mirror `RiderPath`
(`nil`, `pairFree`, `recipeTwin`, `recipeSelf`, `trans`) and add
`selfSwap` for both-covered blocks. -/
inductive PreludePath (x : Card) : State → List Move → State → Prop
  | nil (s : State) : PreludePath x s [] s
  | pairFree {s u : State} {seg : List Move} :
      s.WF → (∃ z, seatOf s x = some (Sum.inr z)) →
      (∃ z : Card, seatOf s x.twin = some (Sum.inr z.twin)) →
      (∃ z, seatOf u x = some (Sum.inr z)) →
      (∃ z : Card, seatOf u x.twin = some (Sum.inr z.twin)) →
      ShufflePlayW s seg u → (∀ m ∈ seg, NotFoundPair x m) →
      PreludePath x s seg u
  | recipeTwin {u w : State} {seg : List Move} :
      RiderRecipeTwin x u w seg → PreludePath x u seg w
  | recipeSelf {u w : State} {seg : List Move} :
      RiderRecipeSelf x u w seg → PreludePath x u seg w
  | selfSwap {u w : State} {seg : List Move} :
      SelfSwapSeg x u w seg → PreludePath x u seg w
  | trans {s u v : State} {l₁ l₂ : List Move} :
      PreludePath x s l₁ u → PreludePath x u l₂ v →
      PreludePath x s (l₁ ++ l₂) v

/-! ## §4. The prelude transfer -/

/-- **The prelude transfer.**  `SwappableIn` at `x` transports along a
`PreludePath`.  The `RiderPath` constructors use the existing row; the
new `selfSwap` constructor uses the segment transfer above. -/
theorem swappableIn_transfer_preludePath {s s' : State} {x : Card}
    {play : List Move} (h : PreludePath x s play s') (hswap : SwappableIn s x) :
    SwappableIn s' x := by
  revert hswap
  induction h with
  | nil st =>
      intro hswap
      exact hswap
  | pairFree hwf hxs hxts hxu hxtu hplay hno =>
      intro hswap
      exact swappableIn_transfer_riderPath
        (RiderPath.pairFree hwf hxs hxts hxu hxtu hplay hno) hswap
  | recipeTwin h =>
      intro hswap
      exact swappableIn_transfer_riderPath (RiderPath.recipeTwin h) hswap
  | recipeSelf h =>
      intro hswap
      exact swappableIn_transfer_riderPath (RiderPath.recipeSelf h) hswap
  | selfSwap h =>
      intro hswap
      exact swappableIn_transfer_selfSwap h hswap
  | trans _h₁ _h₂ ih₁ ih₂ =>
      intro hswap
      exact ih₂ (ih₁ hswap)

/-! ## §5. The abstract 5L producer -/

/-- **The abstract 5L prelude producer.**  `pre` raises the rider `y`
off `x`; `recipe` is the frozen one-raise 3-leg segment (raise `x`,
slide `x.twin` onto `z`, pull `x` onto `z.twin`); `post` is the
physical postlude and its codomain is the strict twin run splice at
`s`.

The concrete world B plays exactly these five legs, with
`post = [Move.foundToTab cJH (Sum.inr cQS)]` and endpoint
`v5 = uB.spliceTwinRuns cQS` (`TwinBothCovered.v5_eq_splice`).  That
row is private to `TwinBothCovered`, so the endpoint equality is
stated here as the postlude's target. -/
theorem selfSwapSeg_of_rider_raise
    {s u v : State} {x y z : Card}
    (hwf_s : s.WF)
    (hxs : ∃ z, seatOf s x = some (Sum.inr z))
    (hxts : ∃ z : Card, seatOf s x.twin = some (Sum.inr z.twin))
    (hpre : ShufflePlayW s [Move.tabToFound y] u)
    (hrecipe : ShufflePlayW u
      [Move.tabToFound x, Move.tabToTab x.twin (Sum.inr z),
        Move.foundToTab x (Sum.inr z.twin)] v)
    (hpost : ShufflePlayW v [Move.foundToTab y (Sum.inr x)]
      (s.spliceTwinRuns x)) :
    SelfSwapSeg x s (s.spliceTwinRuns x)
      [Move.tabToFound y, Move.tabToFound x,
       Move.tabToTab x.twin (Sum.inr z),
       Move.foundToTab x (Sum.inr z.twin),
       Move.foundToTab y (Sum.inr x)] := by
  refine ⟨hwf_s, hxs, hxts, ?_, rfl⟩
  simpa using ShufflePlayW_append hpre (ShufflePlayW_append hrecipe hpost)

/-! ## §6. Audit -/

#print axioms swappableIn_transfer_selfSwap
#print axioms selfSwapSeg_of_strict
#print axioms swappableIn_transfer_preludePath
#print axioms selfSwapSeg_of_rider_raise

/-! ## §7. Report

The remaining geometric obligation is the recognition row:

  an arbitrary both-covered block `ShufflePlayW s seg s'` whose endpoints
  are both `.inr`-seated must be proved to end at `s' = s.spliceTwinRuns x`.

Equivalently, the 5L/7L prelude (clear riders until one twin is a top),
the frozen 3-leg recipe, and the physical postlude (re-seat the cleared
riders) must be assembled into a play whose endpoint is the splice.
`selfSwapSeg_of_rider_raise` packages the 5L instance once the postlude's
endpoint is known; the 7L and ladder cases add more prelude raises before
the same recipe.  Once this recognition row holds for every both-covered
block, `PreludePath` covers the full draw-free board play and
`swappableIn_transfer_preludePath` discharges `RiderNormalization`.
-/
