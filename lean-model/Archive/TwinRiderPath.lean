import Orig2.TwinRecipeRiders
import Orig2.TwinSplicePlay
import Orig2.TwinSpliceUnique
import Orig2.TwinPointTransfer

/-!
# Temp/TwinRiderPath — the rider-general `PointPath` transfer

A rider-general path grammar for `SwappableIn` transfer at a card `x`.
Where the rider-free point path required both twins to be pile tops at
a recipe block, the recipe here needs only **one** twin to be a top:
the other twin may carry riders.  The recipe segment endpoints are
both `.inr`-seated, and the 3-leg recipe moves the raised twin's ride
across while leaving every rider on its parent.

`RiderPath` closes the two recipe orientations against arbitrary
pair-free reversible shuffles.  The remaining gap is the block where
**both** twins carry riders (neither is a pile top): such a block is
not a recipe end, and it needs the 5L/7L prelude/ladder layer to
expose a top first.

House compliance: new file only; zero `sorry`; zero `Classical.choice`.
-/

/-! ## §1. The two recipe segments -/

/-- **The rider-general recipe block, primary orientation.**  Raise
`x.twin`, slide `x` onto the exposed twin target, pull the raised twin
onto `x`'s vacated parent.  The strong existential names the two
`.inr` parents that the segment acts on; only `x.twin` must be a pile
top (`u.pileOfTop x.twin = some a`). -/
def RiderRecipeTwin (x : Card) (u w : State) (seg : List Move) : Prop :=
  u.WF ∧ (∃ z, seatOf u x = some (Sum.inr z)) ∧
  (∃ z : Card, seatOf u x.twin = some (Sum.inr z.twin)) ∧
  (∃ z, seatOf w x = some (Sum.inr z)) ∧
  (∃ z : Card, seatOf w x.twin = some (Sum.inr z.twin)) ∧
  ∃ z : Card, ∃ a : Anchor,
    seatOf u x = some (Sum.inr z) ∧
    seatOf u x.twin = some (Sum.inr z.twin) ∧
    u.pileOfTop x.twin = some a ∧
    reversibleAtW u (Move.tabToFound x.twin) ∧
    seg = [Move.tabToFound x.twin, Move.tabToTab x (Sum.inr z.twin),
      Move.foundToTab x.twin (Sum.inr z)] ∧
    ShufflePlayW u seg w

/-- **The rider-general recipe block, mirror orientation.**  Raise
`x`, slide `x.twin` onto `z`, pull `x` onto `z.twin`; only `x` must be
a pile top. -/
def RiderRecipeSelf (x : Card) (u w : State) (seg : List Move) : Prop :=
  u.WF ∧ (∃ z, seatOf u x = some (Sum.inr z)) ∧
  (∃ z : Card, seatOf u x.twin = some (Sum.inr z.twin)) ∧
  (∃ z, seatOf w x = some (Sum.inr z)) ∧
  (∃ z : Card, seatOf w x.twin = some (Sum.inr z.twin)) ∧
  ∃ z : Card, ∃ a : Anchor,
    seatOf u x = some (Sum.inr z) ∧
    seatOf u x.twin = some (Sum.inr z.twin) ∧
    u.pileOfTop x = some a ∧
    reversibleAtW u (Move.tabToFound x) ∧
    seg = [Move.tabToFound x, Move.tabToTab x.twin (Sum.inr z),
      Move.foundToTab x (Sum.inr z.twin)] ∧
    ShufflePlayW u seg w

/-! ## §2. The path grammar -/

/-- **`RiderPath x s play s'`** — the rider-general point path: a
concatenation of pair-free reversible shuffles and rider-general
recipe blocks, both orientations.  Every recipe block needs one pile
top; the twin beneath it may carry riders. -/
inductive RiderPath (x : Card) : State → List Move → State → Prop
  | nil (s : State) : RiderPath x s [] s
  | pairFree {s u : State} {seg : List Move} :
      s.WF → (∃ z, seatOf s x = some (Sum.inr z)) →
      (∃ z : Card, seatOf s x.twin = some (Sum.inr z.twin)) →
      (∃ z, seatOf u x = some (Sum.inr z)) →
      (∃ z : Card, seatOf u x.twin = some (Sum.inr z.twin)) →
      ShufflePlayW s seg u → (∀ m ∈ seg, NotFoundPair x m) →
      RiderPath x s seg u
  | recipeTwin {u w : State} {seg : List Move} :
      RiderRecipeTwin x u w seg → RiderPath x u seg w
  | recipeSelf {u w : State} {seg : List Move} :
      RiderRecipeSelf x u w seg → RiderPath x u seg w
  | trans {s u v : State} {l₁ l₂ : List Move} :
      RiderPath x s l₁ u → RiderPath x u l₂ v →
      RiderPath x s (l₁ ++ l₂) v

/-! ## §3. The transfer -/

/-- **The rider-general `PointPath` transfer.**  `SwappableIn` at `x`
transfers along a `RiderPath`.  Pair-free legs use the point play
transfer; recipe legs use the rider-general 3-leg segment (one twin a
pile top suffices). -/
theorem swappableIn_transfer_riderPath {s s' : State} {x : Card} {play : List Move}
    (h : RiderPath x s play s') (hswap : SwappableIn s x) :
    SwappableIn s' x := by
  revert hswap
  induction h with
  | nil st =>
      intro hswap
      exact hswap
  | pairFree hwf hxs hxts hxu hxtu hplay hno =>
      intro hswap
      exact swappableIn_transfer_point_play hwf
        (run_wf hwf (Walk_run _ hplay)) hxs hxts hxu hxtu hplay hno hswap
  | recipeTwin h =>
      intro hswap
      obtain ⟨hwfu, _hxu, _hxtu, _hxw, _hxtw, z, a, hc, hct, hpa, hraise,
        hseg, hplay⟩ := h
      rw [hseg] at hplay
      exact (swappableIn_recipe_segment_riders (x := x) (z := z) (a := a)
        hwfu (run_wf hwfu (Walk_run _ hplay)) hc hct hpa hraise hplay).mp hswap
  | recipeSelf h =>
      intro hswap
      obtain ⟨hwfu, _hxu, _hxtu, _hxw, _hxtw, z, a, hc, hct, hpa, hraise,
        hseg, hplay⟩ := h
      rw [hseg] at hplay
      exact (swappableIn_recipe_segment_riders_mirror (x := x) (z := z) (a := a)
        hwfu (run_wf hwfu (Walk_run _ hplay)) hc hct hpa hraise hplay).mp hswap
  | trans _h₁ _h₂ ih₁ ih₂ =>
      intro hswap
      exact ih₂ (ih₁ hswap)

/-! ## §4. Audit -/

#print axioms swappableIn_transfer_riderPath
