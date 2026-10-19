import Orig2.TwinPointNormalize
import Orig2.DetourKit
import Orig2.TwinSplicePlay

/-!
# Temp/TwinNormalizeSplit — the exact-recipe half of `SegNormalization`

`Orig2/TwinPointNormalize.lean` reduces the point transfer to the
segmented grammar `SegPath`, whose two segment grades are `PointSeg`
(a pair-free witness shuffle with the twins seated on `.inr` parents
at both endpoints) and `RecipeSeg` (the exact 3-leg recipe detour).
That card reports the recognition of an arbitrary draw-free play as
the open normalization obligation.

This card closes the half of the obligation where the *first*
pair-foundation block is exactly the 3-leg recipe:

* §1 defines `ExactRecipe`, the field-for-field copy of `RecipeSeg`
  as an independent predicate;
* §2 proves the pair-free prefix segment `pointSeg_of_pairFree` by
  iterating the (public) landing-seat row
  `seat_inr_of_pairFree_step` of `Orig2/TwinSplicePlay.lean`;
* §3 proves the first-detour split and its assembly into `SegPath`;
* §4 derives the `SwappableIn` transfer along such a split;
* §5 reports the remaining gap: an arbitrary pair-foundation block
  need not be the exact 3-leg recipe (riders, longer 5L/7L blocks,
  different raise/pull orders), so `SegNormalization` stays open.

Zero `sorry`, zero `Classical.choice`.
-/

/-! ## §1. The exact recipe -/

/-- `ExactRecipe x u w block` — the field-for-field copy of
`RecipeSeg`: source `WF`, `TwinReady` at both boundaries, the recipe
seats (`x` under `z`, `x.twin` under `z.twin`), the pile top, the
raise witness, the literal 3-leg block, and its witness shuffle. -/
def ExactRecipe (x : Card) (u w : State) (block : List Move) : Prop :=
  u.WF ∧ TwinReady u x ∧ TwinReady w x ∧
  ∃ z : Card, ∃ a : Anchor,
    seatOf u x = some (Sum.inr z) ∧
    seatOf u x.twin = some (Sum.inr z.twin) ∧
    u.pileOfTop x.twin = some a ∧
    reversibleAtW u (Move.tabToFound x.twin) ∧
    block = [Move.tabToFound x.twin, Move.tabToTab x (Sum.inr z.twin),
      Move.foundToTab x.twin (Sum.inr z)] ∧
    ShufflePlayW u block w

/-- `ExactRecipe` is definitionally `RecipeSeg`; this row is the
interface between the two grammars. -/
theorem exactRecipe_iff_recipeSeg (x : Card) (u w : State)
    (block : List Move) :
    ExactRecipe x u w block ↔ RecipeSeg x u w block :=
  Iff.rfl

/-! ## §2. Pair-free prefixes are point segments -/

/-- A pair-free witness shuffle keeps both twins seated on `.inr`
parents at its landing.  This is the play-level iteration of
`seat_inr_of_pairFree_step`. -/
private theorem seats_of_pairFree_play {x : Card} (seg : List Move) :
    ∀ {s u : State}, s.WF → ShufflePlayW s seg u →
      (∀ m ∈ seg, NotFoundPair x m) →
      (∃ z, seatOf s x = some (Sum.inr z)) →
      (∃ z : Card, seatOf s x.twin = some (Sum.inr z.twin)) →
      (∃ z, seatOf u x = some (Sum.inr z)) ∧
        (∃ z : Card, seatOf u x.twin = some (Sum.inr z.twin)) := by
  induction seg with
  | nil =>
      intro s u _ hplay _ hx hxt
      cases hplay
      exact ⟨hx, hxt⟩
  | cons m rest ih =>
      intro s u hwf hplay hno hx hxt
      cases hplay with
      | cons hrev hstep hrest =>
          have hm : NotFoundPair x m := hno m (by simp)
          obtain ⟨hx₁, hxt₁⟩ :=
            seat_inr_of_pairFree_step hwf hstep hrev hm hx hxt
          have hwf₁ := step_wf hwf hstep
          exact ih hwf₁ hrest
            (fun n hn => hno n (List.mem_cons_of_mem m hn)) hx₁ hxt₁

/-- **The pair-free prefix segment.**  A pair-free witness shuffle
out of a `WF` state with both twins seated on `.inr` parents is a
`PointSeg`; the landing seats are the play iteration of the
per-letter row. -/
theorem pointSeg_of_pairFree
    {s u : State} {x : Card} {seg : List Move}
    (hwf : s.WF) (hplay : ShufflePlayW s seg u)
    (hno : ∀ m ∈ seg, NotFoundPair x m)
    (hxs : ∃ z, seatOf s x = some (Sum.inr z))
    (hxts : ∃ z : Card, seatOf s x.twin = some (Sum.inr z.twin)) :
    PointSeg x s u seg := by
  obtain ⟨hxu, hxtu⟩ := seats_of_pairFree_play seg hwf hplay hno hxs hxts
  exact ⟨hwf, hxs, hxts, hxu, hxtu, hplay, hno⟩

/-! ## §3. The first-detour split and its assembly -/

/-- **The exact-recipe split.**  A pair-free prefix, an exact 3-leg
recipe block, and a segmented suffix compose into a `SegPath`.

The requested existential `hsplit` form does not tie the recipe
source `u` to the prefix `pre` (it stores no `ShufflePlayW s pre u`),
so the theorem is stated with the split exposed: the prefix play
`hpre`, the recipe `hrecipe`, the suffix path `hpost`, and the
factorization `hplayEq`.  Each missing link is a genuine hypothesis,
not a definitional unfolding. -/
theorem segPath_of_exactRecipeSplit
    {s s' u w : State} {x : Card} {play pre block post : List Move}
    (_hplay : ShufflePlayW s play s')
    (hplayEq : play = pre ++ block ++ post)
    (hpre : ShufflePlayW s pre u)
    (hrecipe : ExactRecipe x u w block)
    (hpost : SegPath x w post s')
    (hno : ∀ m ∈ pre, NotFoundPair x m)
    (hxs : ∃ z, seatOf s x = some (Sum.inr z))
    (hxts : ∃ z : Card, seatOf s x.twin = some (Sum.inr z.twin))
    (hwf : s.WF) :
    SegPath x s play s' := by
  have hpoint : PointSeg x s u pre :=
    pointSeg_of_pairFree hwf hpre hno hxs hxts
  have hrec : RecipeSeg x u w block :=
    (exactRecipe_iff_recipeSeg x u w block).mp hrecipe
  have h₁ : SegPath x s pre u := SegPath.point hpoint
  have h₂ : SegPath x u block w := SegPath.recipe hrec
  have h₃ : SegPath x s (pre ++ block) w := SegPath.trans h₁ h₂
  have h₄ : SegPath x s ((pre ++ block) ++ post) s' := SegPath.trans h₃ hpost
  rw [hplayEq]
  simpa [List.append_assoc] using h₄

/-! ## §4. The transfer along an exact-recipe split -/

/-- **The `SwappableIn` transfer along an exact-recipe split.** -/
theorem swappableIn_transfer_exactRecipeSplit
    {s s' u w : State} {x : Card} {play pre block post : List Move}
    (hplay : ShufflePlayW s play s')
    (hplayEq : play = pre ++ block ++ post)
    (hpre : ShufflePlayW s pre u)
    (hrecipe : ExactRecipe x u w block)
    (hpost : SegPath x w post s')
    (hno : ∀ m ∈ pre, NotFoundPair x m)
    (hxs : ∃ z, seatOf s x = some (Sum.inr z))
    (hxts : ∃ z : Card, seatOf s x.twin = some (Sum.inr z.twin))
    (hwf : s.WF) :
    SwappableIn s x → SwappableIn s' x := by
  intro hswap
  exact swappableIn_transfer_segPath
    (segPath_of_exactRecipeSplit hplay hplayEq hpre hrecipe hpost hno
      hxs hxts hwf) hswap

/-! ## §5. The remaining normalization gap

The results above cover exactly one shape of the first
pair-foundation detour: the 3-leg block

```
[Move.tabToFound x.twin, Move.tabToTab x (Sum.inr z.twin),
  Move.foundToTab x.twin (Sum.inr z)]
```

with `TwinReady` at both boundaries and the recipe seats, pile top,
and raise witness at its source.  An arbitrary pair-foundation block
of an arbitrary draw-free play need not have this shape:

* riders may occupy the segment boundaries, so `TwinReady` can fail
  even when the 3 legs themselves occur;
* a detour may be a longer 5L/7L block (extra slides or a drawn-out
  cargo route around the raise/pull);
* the raise and pull may occur in another order, or the twins may be
  exchanged before the pair returns to its seat.

Such blocks are not `ExactRecipe`, hence not `RecipeSeg`, and the
theorem here does not recognize them.  Therefore the full
`SegNormalization` obligation (`NoDrawPlayW s s' → ∃ play,
SegPath x s play s'`) is **not** closed by this card: the
arbitrary-block recognition step remains open.

Zero `sorry`, zero `Classical.choice`.
-/

#print axioms pointSeg_of_pairFree
#print axioms segPath_of_exactRecipeSplit
#print axioms swappableIn_transfer_exactRecipeSplit
