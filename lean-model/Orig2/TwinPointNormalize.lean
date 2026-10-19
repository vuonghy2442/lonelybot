import Orig2.TwinPointOrbit
import Orig2.DetourKit
import Orig2.TwinSplicePlay

/-!
# Temp/TwinPointNormalize — the segmented assembly to `PointPath`

The point-grade path grammar `PointPath` (`Orig2/TwinPointOrbit.lean`)
is re-expressed here as a segmented grammar `SegPath`:

* `PointSeg` is exactly the payload of `PointPath.pairFree` — the
  source `WF`, the four `.inr` seat witnesses, the witness shuffle,
  and the pair-foundation exclusion list;
* `RecipeSeg` is exactly the payload of `PointPath.recipe` — the
  source `WF`, the two `TwinReady` boundaries, the recipe seats, the
  pile top, the raise witness, the exact 3-leg block, and its shuffle
  play;
* `SegPath.trans` composes.

The translation `pointPath_of_segPath` is purely structural, and
`swappableIn_transfer_segPath` is its `SwappableIn` corollary.

The normalization obligation is *reported only* in §4: an arbitrary
draw-free board play is not yet segmented into `SegPath`; the missing
recognition step is the pair-foundation block analysis.

Zero `sorry`, zero `Classical.choice`.
-/

/-! ## §1. The segment predicates -/

/-- A point-grade pair-free segment: the exact payload of
`PointPath.pairFree`. -/
def PointSeg (x : Card) (s u : State) (seg : List Move) : Prop :=
  s.WF ∧ (∃ z, seatOf s x = some (Sum.inr z)) ∧
  (∃ z : Card, seatOf s x.twin = some (Sum.inr z.twin)) ∧
  (∃ z, seatOf u x = some (Sum.inr z)) ∧
  (∃ z : Card, seatOf u x.twin = some (Sum.inr z.twin)) ∧
  ShufflePlayW s seg u ∧ ∀ m ∈ seg, NotFoundPair x m

/-- A recipe segment: the exact payload of `PointPath.recipe`.  The
source `u.WF` is included because `PointPath.recipe` stores it
explicitly. -/
def RecipeSeg (x : Card) (u w : State) (seg : List Move) : Prop :=
  u.WF ∧ TwinReady u x ∧ TwinReady w x ∧
  ∃ z : Card, ∃ a : Anchor,
    seatOf u x = some (Sum.inr z) ∧
    seatOf u x.twin = some (Sum.inr z.twin) ∧
    u.pileOfTop x.twin = some a ∧
    reversibleAtW u (Move.tabToFound x.twin) ∧
    seg = [Move.tabToFound x.twin, Move.tabToTab x (Sum.inr z.twin),
      Move.foundToTab x.twin (Sum.inr z)] ∧
    ShufflePlayW u seg w

/-! ## §2. The segmented grammar -/

/-- A play segmented into point-grade pair-free blocks and exact
3-leg recipe detours. -/
inductive SegPath (x : Card) : State → List Move → State → Prop
  | nil (s : State) : SegPath x s [] s
  | point {s u seg} : PointSeg x s u seg → SegPath x s seg u
  | recipe {u w seg} : RecipeSeg x u w seg → SegPath x u seg w
  | trans {s u v l₁ l₂} : SegPath x s l₁ u → SegPath x u l₂ v →
      SegPath x s (l₁ ++ l₂) v

/-! ## §3. The translation and the transfer -/

/-- **Structural assembly.**  A segmented play is a `PointPath`; the
`point` and `recipe` blocks carry exactly the corresponding
constructor payloads. -/
theorem pointPath_of_segPath {s s' : State} {x : Card} {play : List Move}
    (h : SegPath x s play s') : PointPath x s play s' := by
  induction h with
  | nil s =>
      exact PointPath.nil s
  | point hseg =>
      obtain ⟨hwf, hxs, hxts, hxu, hxtu, hplay, hno⟩ := hseg
      exact PointPath.pairFree hwf hxs hxts hxu hxtu hplay hno
  | recipe hseg =>
      obtain ⟨hwf, hready_s, hready_u, z, a, hc, hct, hpa, hraise,
        hsegEq, hplay⟩ := hseg
      rw [hsegEq] at hplay ⊢
      exact PointPath.recipe hwf hready_s hready_u hc hct hpa hraise hplay
  | trans h₁ h₂ ih₁ ih₂ =>
      exact PointPath.trans ih₁ ih₂

/-- **The `SwappableIn` transfer along a segmented play.** -/
theorem swappableIn_transfer_segPath {s s' : State} {x : Card} {play : List Move}
    (h : SegPath x s play s') (hswap : SwappableIn s x) : SwappableIn s' x :=
  swappableIn_transfer_pointPath (pointPath_of_segPath h) hswap

/-! ## §4. The normalization frontier (reported, not proved)

The remaining normalization obligation is

```
-- NoDrawPlayW s s' → ∃ play, SegPath x s play s'
```

It is *not* proved here.  The exact missing recognition step is the
pair-foundation block analysis of an arbitrary draw-free play:
`Orig2.DetourKit.exists_pairFound_split` supplies the first
pair-foundation letter, but the block around that letter must be
recognized as *exactly* the 3-leg recipe

```
[Move.tabToFound x.twin, Move.tabToTab x (Sum.inr z.twin),
  Move.foundToTab x.twin (Sum.inr z)]
```

with `TwinReady` at both of its boundaries (and the recipe seats, the
pile top, and the raise witness at its source).  Pair-free prefixes
and suffixes then fall into `PointSeg`.  Riders at the segment
boundaries and non-recipe pair-foundation blocks (longer 5L/7L
detours, or blocks that raise/pull the pair in another order) are
**not covered** by `SegPath` and remain outside this card.

Zero `sorry`, zero `Classical.choice`.
-/

#print axioms pointPath_of_segPath
#print axioms swappableIn_transfer_segPath
