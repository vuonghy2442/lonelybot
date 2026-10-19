import Orig2.TwinAbstractLadder
import Orig2.TwinRiderPath
import Orig2.TwinPreludePath
import Orig2.TwinConcreteSelfSwap

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# Temp/TwinBothCoveredPath — the concrete 5L block as a `RiderPath`

The both-covered block at world B is not a `SelfSwapSeg` only: it is
literally

```
pair-free raise J♥  ++  exact 3-leg recipe at Q♠  ++  pair-free pull J♥
```

so it is a `RiderPath` at `Q♠`.  This file records both the concrete
factorization and the abstract prelude/recipe/postlude producer.

## Statement adjustments

* The abstract producer cannot take the recipe hypothesis as a bare
  `ShufflePlayW u block w0`: that does not constrain `block` to the
  frozen recipe, nor does it provide the pile-top and raise rows.  The
  hypothesis is therefore the disjunction of the two rider-general
  recipe predicates, `RiderRecipeTwin` and `RiderRecipeSelf`.
* `ShufflePlayW s pre u` carries no source `WF`, and the pair-free
  block constructor needs both twins `.inr`-seated at its source.  The
  producer therefore also takes `hwf_s : s.WF` and `hs` at `s`.

The remaining gap is reported at the end of the file.

House compliance: new file only; zero `sorry`; zero `Classical.choice`.
-/

open State
open TwinBothCovered

namespace TwinBothCoveredPath

/-! ## §1. Local concrete card names and intermediate states -/

private def cQCb : Card := ⟨Suit.club, Rank.queen⟩
private def cJHb : Card := ⟨Suit.heart, Rank.jack⟩
private def cJDb : Card := ⟨Suit.diamond, Rank.jack⟩
private def kDb : Card := ⟨Suit.diamond, Rank.king⟩
private def kHb : Card := ⟨Suit.heart, Rank.king⟩

/-- The state after raising `J♥` (the prelude). -/
private def w1 : State :=
  { uBpub.setFound Suit.heart (uBpub.found Suit.heart ++ [cJHb]) with
    piles := fun a' =>
      if a' = Anchor.p0 then
        Pile.afterRunRemoved (uBpub.piles Anchor.p0)
          (chop (uBpub.piles Anchor.p0).faceUp)
      else uBpub.piles a' }

/-- The state after raising `Q♠`. -/
private def w2 : State :=
  { w1.setFound Suit.spade (w1.found Suit.spade ++ [cQSpub]) with
    piles := fun a' =>
      if a' = Anchor.p0 then
        Pile.afterRunRemoved (w1.piles Anchor.p0)
          (chop (w1.piles Anchor.p0).faceUp)
      else w1.piles a' }

/-- The state after sliding the `Q♣` run onto `K♦`. -/
private def w3 : State :=
  (w2.setPile Anchor.p1 (Pile.afterRunRemoved (w2.piles Anchor.p1)
    (below cQCb (w2.piles Anchor.p1).faceUp))).putRun
    (fromCard cQCb (w2.piles Anchor.p1).faceUp) (Sum.inr kDb)

/-- The state after pulling `Q♠` onto `K♥` (the recipe endpoint). -/
private def w4 : State :=
  (w3.setFound Suit.spade (chop (w3.found Suit.spade))).putCard cQSpub
    (Sum.inr kHb)

/-- The state after re-seating `J♥` on `Q♠`. -/
private def w5 : State :=
  (w4.setFound Suit.heart (chop (w4.found Suit.heart))).putCard cJHb
    (Sum.inr cQSpub)

/-! ## §2. The concrete step rows -/

private theorem stepW1 : State.step uBpub (Move.tabToFound cJHb) = some w1 :=
  step_tabToFound_splice (by decide) (by decide)

private theorem stepW2 : State.step w1 (Move.tabToFound cQSpub) = some w2 :=
  step_tabToFound_splice (by decide) (by decide)

private theorem stepW3 :
    State.step w2 (Move.tabToTab cQCb (Sum.inr kDb)) = some w3 := by
  rw [step_tabToTab_eq]
  have hhold : w2.pileHolding cQCb = some Anchor.p1 := by decide
  have hcp : w2.canPlace cQCb (Sum.inr kDb) = true := by decide
  have hfrom : fromCard cQCb (w2.piles Anchor.p1).faceUp = [cQCb, cJDb] := by
    decide
  rw [hhold]
  simp only [hcp, ite_true]
  rw [hfrom]
  rfl

private theorem stepW4 :
    State.step w3 (Move.foundToTab cQSpub (Sum.inr kHb)) = some w4 :=
  step_foundToTab_splice (by decide) (by decide)

private theorem stepW5 :
    State.step w4 (Move.foundToTab cJHb (Sum.inr cQSpub)) = some w5 :=
  step_foundToTab_splice (by decide) (by decide)

/-! ## §3. WF of the concrete intermediates -/

private theorem w1_wf : w1.WF := step_wf uBpub_wf stepW1
private theorem w2_wf : w2.WF := step_wf w1_wf stepW2
private theorem w3_wf : w3.WF := step_wf w2_wf stepW3
private theorem w4_wf : w4.WF := step_wf w3_wf stepW4
private theorem w5_wf : w5.WF := step_wf w4_wf stepW5

/-! ## §4. The three concrete factors -/

/-- The prelude: the rider raise `J♥`. -/
private def preBlock : List Move := [Move.tabToFound cJHb]

/-- The exact frozen 3-leg recipe at `Q♠` (self/primary orientation:
raise `Q♠`, slide `Q♣` onto `K♦`, pull `Q♠` onto `K♥`). -/
private def recipeBlock : List Move :=
  [Move.tabToFound cQSpub, Move.tabToTab cQCb (Sum.inr kDb),
   Move.foundToTab cQSpub (Sum.inr kHb)]

/-- The postlude: the rider pull back onto `Q♠`. -/
private def postBlock : List Move := [Move.foundToTab cJHb (Sum.inr cQSpub)]

private theorem prePlay : ShufflePlayW uBpub preBlock w1 :=
  .cons ((reversibleOf_iff_reversibleAtW uBpub_wf _).mp (by decide)) stepW1
    (.nil w1)

private theorem recipePlay : ShufflePlayW w1 recipeBlock w4 :=
  .cons ((reversibleOf_iff_reversibleAtW w1_wf _).mp (by decide)) stepW2
    (.cons ((reversibleOf_iff_reversibleAtW w2_wf _).mp (by decide)) stepW3
      (.cons ((reversibleOf_iff_reversibleAtW w3_wf _).mp (by decide)) stepW4
        (.nil w4)))

private theorem postPlay : ShufflePlayW w4 postBlock w5 :=
  .cons ((reversibleOf_iff_reversibleAtW w4_wf _).mp (by decide)) stepW5
    (.nil w5)

/-! ## §5. Pair-freeness of the rider legs -/

private theorem hnoPre : ∀ m ∈ preBlock, NotFoundPair cQSpub m := by
  intro m hm
  simp only [preBlock, List.mem_singleton] at hm
  subst hm
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h
    injection h with hc
    exact (by decide : cJHb ≠ cQSpub) hc
  · intro h
    injection h with hc
    exact (by decide : cJHb ≠ cQSpub.twin) hc
  · intro b h
    nomatch h
  · intro b h
    nomatch h

private theorem hnoPost : ∀ m ∈ postBlock, NotFoundPair cQSpub m := by
  intro m hm
  simp only [postBlock, List.mem_singleton] at hm
  subst hm
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h
    nomatch h
  · intro h
    nomatch h
  · intro b h
    injection h with hc _
    exact (by decide : cJHb ≠ cQSpub) hc
  · intro b h
    injection h with hc _
    exact (by decide : cJHb ≠ cQSpub.twin) hc

/-! ## §6. Seats at the block boundaries -/

private theorem seatsW1 :
    (∃ z, seatOf w1 cQSpub = some (Sum.inr z)) ∧
      (∃ z : Card, seatOf w1 cQSpub.twin = some (Sum.inr z.twin)) :=
  ⟨⟨kDb, by decide⟩, ⟨kDb, by decide⟩⟩

private theorem seatsW4 :
    (∃ z, seatOf w4 cQSpub = some (Sum.inr z)) ∧
      (∃ z : Card, seatOf w4 cQSpub.twin = some (Sum.inr z.twin)) :=
  ⟨⟨kHb, by decide⟩, ⟨kHb, by decide⟩⟩

private theorem seatsSplice :
    (∃ z, seatOf (uBpub.spliceTwinRuns cQSpub) cQSpub = some (Sum.inr z)) ∧
      (∃ z : Card,
        seatOf (uBpub.spliceTwinRuns cQSpub) cQSpub.twin =
          some (Sum.inr z.twin)) :=
  ⟨⟨kHb, by decide⟩, ⟨kHb, by decide⟩⟩

/-! ## §7. The middle block is the rider-general recipe -/

private theorem recipeSelfW1W4 :
    RiderRecipeSelf cQSpub w1 w4 recipeBlock :=
  ⟨w1_wf,
   ⟨kDb, by decide⟩,
   ⟨kDb, by decide⟩,
   ⟨kHb, by decide⟩,
   ⟨kHb, by decide⟩,
   kDb, Anchor.p0,
   (by decide),
   (by decide),
   (by decide),
   (reversibleOf_iff_reversibleAtW w1_wf _).mp (by decide),
   rfl,
   recipePlay⟩

/-! ## §8. The abstract prelude/recipe/postlude producer -/

/-- **The abstract factorization.**  A pair-free prelude, the exact
rider-general 3-leg recipe (either orientation), and a pair-free
postlude compose into a `RiderPath`.  The recipe is supplied as
`RiderRecipeTwin ∨ RiderRecipeSelf`; a bare `ShufflePlayW` hypothesis
does not determine the block.

`hwf_s` and `hs` are needed because a witness shuffle carries no
source `WF` and no source seat data. -/
theorem riderPath_of_prelude_recipe_postlude
    {s u w0 w : State} {x : Card} {pre block post : List Move}
    (hwf_s : s.WF)
    (hs : (∃ z, seatOf s x = some (Sum.inr z)) ∧
          (∃ z : Card, seatOf s x.twin = some (Sum.inr z.twin)))
    (hpre : ShufflePlayW s pre u) (hnoPre : ∀ m ∈ pre, NotFoundPair x m)
    (hu : (∃ z, seatOf u x = some (Sum.inr z)) ∧
          (∃ z : Card, seatOf u x.twin = some (Sum.inr z.twin)))
    (hw0 : (∃ z, seatOf w0 x = some (Sum.inr z)) ∧
           (∃ z : Card, seatOf w0 x.twin = some (Sum.inr z.twin)))
    (hrecipe : RiderRecipeTwin x u w0 block ∨
      RiderRecipeSelf x u w0 block)
    (hpost : ShufflePlayW w0 post w) (hnoPost : ∀ m ∈ post, NotFoundPair x m)
    (hw : (∃ z, seatOf w x = some (Sum.inr z)) ∧
          (∃ z : Card, seatOf w x.twin = some (Sum.inr z.twin)))
    (hplay : ShufflePlayW s (pre ++ block ++ post) w) :
    RiderPath x s (pre ++ block ++ post) w := by
  have hw0_wf : w0.WF := by
    rcases hrecipe with h | h
    · obtain ⟨huwf, _hxu, _hxtu, _hxw, _hxtw, _z, _a,
        _hc, _hct, _hpa, _hraise, _hseg, hsegPlay⟩ := h
      exact run_wf huwf (Walk_run _ hsegPlay)
    · obtain ⟨huwf, _hxu, _hxtu, _hxw, _hxtw, _z, _a,
        _hc, _hct, _hpa, _hraise, _hseg, hsegPlay⟩ := h
      exact run_wf huwf (Walk_run _ hsegPlay)
  have hblock : RiderPath x u block w0 := by
    rcases hrecipe with h | h
    · exact RiderPath.recipeTwin h
    · exact RiderPath.recipeSelf h
  have hprePath : RiderPath x s pre u :=
    RiderPath.pairFree hwf_s hs.1 hs.2 hu.1 hu.2 hpre hnoPre
  have hpostPath : RiderPath x w0 post w :=
    RiderPath.pairFree hw0_wf hw0.1 hw0.2 hw.1 hw.2 hpost hnoPost
  have hhead : RiderPath x s (pre ++ block) w0 :=
    RiderPath.trans (l₁ := pre) (l₂ := block) hprePath hblock
  exact RiderPath.trans (l₁ := pre ++ block) (l₂ := post) hhead hpostPath

/-! ## §9. The concrete world-B rider path -/

private theorem play5pub_parts :
    play5pub = preBlock ++ recipeBlock ++ postBlock := rfl

/-- **The concrete 5L both-covered block is a `RiderPath` at `Q♠`.** -/
theorem riderPath_play5pub :
    RiderPath cQSpub uBpub play5pub (uBpub.spliceTwinRuns cQSpub) := by
  have hplay : ShufflePlayW uBpub (preBlock ++ recipeBlock ++ postBlock)
      (uBpub.spliceTwinRuns cQSpub) := by
    have h := play5pub_shuffle
    rw [play5pub_parts, v5pub_eq_splice] at h
    exact h
  have hpostSplice : ShufflePlayW w4 postBlock
      (uBpub.spliceTwinRuns cQSpub) := by
    rw [← v5pub_eq_splice]
    exact postPlay
  have hpath : RiderPath cQSpub uBpub
      (preBlock ++ recipeBlock ++ postBlock)
      (uBpub.spliceTwinRuns cQSpub) :=
    riderPath_of_prelude_recipe_postlude
      (s := uBpub) (u := w1) (w0 := w4)
      (w := uBpub.spliceTwinRuns cQSpub) (x := cQSpub)
      (pre := preBlock) (block := recipeBlock) (post := postBlock)
      uBpub_wf uBpub_seats prePlay hnoPre seatsW1 seatsW4
      (Or.inr recipeSelfW1W4) hpostSplice hnoPost seatsSplice hplay
  rw [play5pub_parts]
  exact hpath

/-- **The concrete swap transports along the rider path.** -/
theorem swappableIn_uBpub_via_riderPath :
    SwappableIn uBpub cQSpub →
      SwappableIn (uBpub.spliceTwinRuns cQSpub) cQSpub :=
  swappableIn_transfer_riderPath riderPath_play5pub

/-! ## §10. Audit and remaining gap -/

#print axioms riderPath_of_prelude_recipe_postlude
#print axioms riderPath_play5pub
#print axioms swappableIn_uBpub_via_riderPath

/-!
## §11. Report

The concrete block factors exactly as

```
[raise J♥] ++ [raise Q♠, slide Q♣ -> K♦, pull Q♠ -> K♥] ++ [pull J♥ -> Q♠]
```

and the middle three legs are `RiderRecipeSelf cQSpub` at `w1`: `Q♠`
sits on `K♦`, `Q♣` on `K♥`, and `Q♠` is a pile top (its rider was
cleared by the prelude).  Both outer legs are pair-free with respect
to `Q♠` (`NotFoundPair cQSpub`).

Remaining gap: the abstract producer still requires the middle block
to be the **exact** 3-leg recipe in one of the two rider-general
orientations.  Longer `x`/`x.twin` detours (multi-rider ladders, or
blocks that move the pair outside the frozen recipe while staying
both-covered) are not generated by `RiderPath`; they need the
prelude/ladder layer to expose a top and a subsequent exact recipe
block before this factorization applies.
-/

end TwinBothCoveredPath
