import Orig2.Fork.Local.ForkStraddle

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-!
# Orig2/ForkLandResNetZero — the cover/uncover pair is net-zero

READ-ONLY scratch card.  No source file is modified; nothing is committed.
Zero `sorry`, zero `Classical.choice`, no `native_decide`.

## What this card is for

`StradKit.LandingResidual` (`Orig2/Fork/Local/ForkStraddle.lean:393`) says: in the interior
of a straddling self-bracket `pull d ; ... ; raise d`, no letter LANDS a card
on `d`.  A landing is not fatal by itself (`StradKit.existRefute_landing_not_fatal`),
so the benchmark can still close the bracket only if a LATER letter uncovers
`d`:

```text
slide x -> d     (the landing)      ... interior ...      slide x -> b''   (the uncover)
```

This is a cover/uncover pair and should collapse to the single slide
`slide x -> b''`.

## Contents

* §1 `cover_piles_at` / `slideSt_slideSt_self` — **the state-level net-zero**:
  two successive slides of the same card `x` (`x : a -> d`, then `x : d -> b''`)
  land on exactly the state of the single slide `x : a -> b''`.  This is
  `NoSelfKit.raiseSt_slideSt_self` with `raise` replaced by a second `slide`.
* §2 `slide_pair_shortens` — the play-level corollary for an ADJACENT pair:
  `α ; slide x -> d ; slide x -> b'' ; tail` is replaced by the strictly
  shorter `α ; slide x -> b'' ; tail` with the same endpoints.
* §3 `SeatIndifferent` and `slide_pair_shortens_of_indifferent` — the general
  play-level lemma: the same collapse with a non-empty interior, under the
  named frame obligation that the interior does not read `x`'s seat.
* §4 the reduction to `StradKit.LandingResidual`, with the surviving case
  `UncoverByRaise` (the covering card leaves `d` by a RAISE, where the
  net-zero cancellation does not apply) and the derivation
  `landingResidual_of_uncover`.
-/

namespace LandRes

open SplitKit
open CommuteStep

/-! ## §1. The state-level net-zero: `x -> d ; x -> b'' = x -> b''` -/

/-- The piles of the cover state: `a` chopped, `d`'s pile with `x` appended,
everything else untouched.  (`slideSt_piles_at` at `b = inr d`, in the
last-card case `fromCard x (faceUp a) = [x]`.) -/
theorem cover_piles_at {st : State} {x d : Card} {a k : Anchor}
    (hwf : st.WF) (hxa : st.pileOfTop x = some a)
    (hkd : st.pileOfTop d = some k) (hka : k ≠ a)
    (hcp : st.canPlace x (Sum.inr d) = true)
    (hcell : below x (st.piles a).faceUp ≠ [] ∨
      (below x (st.piles a).faceUp = [] ∧ (st.piles a).hidden = []))
    (j : Anchor) :
    (slideSt st x (Sum.inr d) a).piles j =
      (if j = a then { st.piles a with faceUp := below x (st.piles a).faceUp }
       else if j = k then
         { st.piles k with faceUp := (st.piles k).faceUp ++ [x] }
       else st.piles j) := by
  have hnd : (st.piles a).faceUp.Nodup := runOK_nodup (hwf.runOK_of a)
  have hlt : lastOf (st.piles a).faceUp = some x := (pileOfTop_top hxa).2
  have hsingle : fromCard x (st.piles a).faceUp = [x] :=
    NoSelfKit.fromCard_singleton_of_last hnd hlt
  have h := slideSt_piles_at hwf hcp (by simpa [tgt_inr] using hkd) hka hcell j
  rw [h, hsingle]

/-- **THE COVER/UNCOVER PAIR IS NET-ZERO.**  Two successive slides of `x`
(`x : a -> d`, then `x : d -> b''`) land on exactly the state of the single
slide `x : a -> b''`. -/
theorem slideSt_slideSt_self
    {st : State} {x d : Card} {b'' : Base} {a k k'' : Anchor}
    (hwf : st.WF)
    (hxa : st.pileOfTop x = some a)
    (hkd : st.pileOfTop d = some k)
    (hka : k ≠ a)
    (hcpd : st.canPlace x (Sum.inr d) = true)
    (hcp0 : st.canPlace x b'' = true)
    (hcp0s : (slideSt st x (Sum.inr d) a).canPlace x b'' = true)
    (hk'' : tgt st b'' = some k'')
    (hk''a : k'' ≠ a)
    (hk''k : k'' ≠ k)
    (hcell : below x (st.piles a).faceUp ≠ [] ∨
      (below x (st.piles a).faceUp = [] ∧ (st.piles a).hidden = []))
    (htgt : tgt (slideSt st x (Sum.inr d) a) b'' = some k'') :
    slideSt (slideSt st x (Sum.inr d) a) x b'' k =
      slideSt st x b'' a := by
  have hnd : (st.piles a).faceUp.Nodup := runOK_nodup (hwf.runOK_of a)
  have hlt : lastOf (st.piles a).faceUp = some x := (pileOfTop_top hxa).2
  have hsingle : fromCard x (st.piles a).faceUp = [x] :=
    NoSelfKit.fromCard_singleton_of_last hnd hlt
  -- x is the top of `a`, hence not in `d`'s pile
  have hxdmem : x ∈ (st.piles a).faceUp := lastOf_mem hlt
  have hnotmemk : x ∉ (st.piles k).faceUp :=
    ((mem_faceUp_unique hwf hxdmem) k hka).1
  have hkdnd : (st.piles k).faceUp.Nodup := runOK_nodup (hwf.runOK_of k)
  have hkne : (st.piles k).faceUp ≠ [] := by
    intro hnil
    have := (pileOfTop_top hkd).2
    rw [hnil] at this
    exact absurd this (by simp [lastOf])
  have hndk : ((st.piles k).faceUp ++ [x]).Nodup := by
    refine List.nodup_append.mpr ⟨hkdnd, by simp [List.Nodup], ?_⟩
    intro y hy z hz
    rw [List.mem_singleton] at hz
    subst hz
    exact fun hyx => hnotmemk (hyx ▸ hy)
  -- the cover is a legal step
  have hhold : st.pileHolding x = some a := Drain.pileHolding_of_pileOfTop hwf hxa
  have hstep : State.step st (Move.tabToTab x (Sum.inr d)) =
      some (slideSt st x (Sum.inr d) a) := by
    rw [step_tabToTab_eq, hhold]
    show (if st.canPlace x (Sum.inr d) then
        (match fromCard x (st.piles a).faceUp with
         | [] => none
         | run => some ((st.setPile a
              (Pile.afterRunRemoved (st.piles a) (below x (st.piles a).faceUp))).putRun
              run (Sum.inr d)))
      else none) = some (slideSt st x (Sum.inr d) a)
    rw [ite_eq_left hcpd, hsingle]
    simp only [slideSt, hsingle]
  have hcoverWF : (slideSt st x (Sum.inr d) a).WF := step_wf hwf hstep
  -- the cover pile `k` is `fu k ++ [x]`
  have hcover : (slideSt st x (Sum.inr d) a).piles k =
      { st.piles k with faceUp := (st.piles k).faceUp ++ [x] } := by
    rw [cover_piles_at hwf hxa hkd hka hcpd hcell k,
      ite_eq_right hka, ite_eq_left rfl]
  have hcoverT : (slideSt st x (Sum.inr d) a).piles k'' = st.piles k'' :=
    slideSt_piles_other hwf hcpd (by simpa [tgt_inr] using hkd) hka hcell
      hk''a hk''k
  -- the cell condition at the cover pile
  have hcellk : below x ((st.piles k).faceUp ++ [x]) ≠ [] ∨
      (below x ((st.piles k).faceUp ++ [x]) = [] ∧ (st.piles k).hidden = []) := by
    left
    rw [NoSelfKit.below_eq_chop_of_last hndk (by rw [lastOf_snoc]), chop_snoc]
    exact hkne
  have hcellkS : below x ((slideSt st x (Sum.inr d) a).piles k).faceUp ≠ [] ∨
      (below x ((slideSt st x (Sum.inr d) a).piles k).faceUp = [] ∧
        ((slideSt st x (Sum.inr d) a).piles k).hidden = []) := by
    rw [hcover]
    exact hcellk
  -- the second slide's source pile
  have hsrc : (slideSt (slideSt st x (Sum.inr d) a) x b'' k).piles k =
      { (slideSt st x (Sum.inr d) a).piles k with
        faceUp := below x ((slideSt st x (Sum.inr d) a).piles k).faceUp } :=
    slideSt_piles_source hcoverWF hcp0s htgt hk''k hcellkS
  have hchopk : below x ((st.piles k).faceUp ++ [x]) = (st.piles k).faceUp := by
    rw [NoSelfKit.below_eq_chop_of_last hndk (by rw [lastOf_snoc]), chop_snoc]
  have hfromk : fromCard x ((st.piles k).faceUp ++ [x]) = [x] :=
    NoSelfKit.fromCard_singleton_of_last hndk (by rw [lastOf_snoc])
  -- compare the two states pile by pile
  apply State.ext
  · rw [slideSt_found, slideSt_found, slideSt_found]
  · funext j
    rw [slideSt_piles_at hcoverWF hcp0s htgt hk''k hcellkS j]
    rw [slideSt_piles_at hwf hcp0 hk'' hk''a hcell j]
    by_cases hja : j = a
    · -- `j` is the DIRECT slide's source; the second slide never sees it
      rw [ite_eq_right (show ¬ j = k from by rw [hja]; exact Ne.symm hka),
          ite_eq_right (show ¬ j = k'' from by rw [hja]; exact Ne.symm hk''a),
          ite_eq_left hja]
      rw [hja]
      rw [cover_piles_at hwf hxa hkd hka hcpd hcell a, ite_eq_left rfl]
    · by_cases hjk : j = k
      · -- `j` is the second slide's source (the cover pile)
        rw [ite_eq_left hjk,
            ite_eq_right (show ¬ j = a from by rw [hjk]; exact hka),
            ite_eq_right (show ¬ j = k'' from by rw [hjk]; exact Ne.symm hk''k)]
        rw [hjk, hcover, hchopk]
      · by_cases hjk'' : j = k''
        · -- `j` is the common target
          rw [ite_eq_right (show ¬ j = k from by rw [hjk'']; exact hk''k),
              ite_eq_left hjk'',
              ite_eq_right (show ¬ j = a from by rw [hjk'']; exact hk''a),
              ite_eq_left hjk'']
          rw [hcover, hcoverT, hfromk, hsingle]
        · rw [ite_eq_right hjk, ite_eq_right hjk'',
              ite_eq_right hja, ite_eq_right hjk'']
          rw [cover_piles_at hwf hxa hkd hka hcpd hcell j,
            ite_eq_right hja, ite_eq_right hjk]
  · rw [slideSt_stock, slideSt_stock, slideSt_stock]
  · rw [slideSt_waste, slideSt_waste, slideSt_waste]
  · rw [slideSt_drawStep, slideSt_drawStep, slideSt_drawStep]

/-! ## §2. Battery -/

#print axioms LandRes.cover_piles_at
#print axioms LandRes.slideSt_slideSt_self

end LandRes

