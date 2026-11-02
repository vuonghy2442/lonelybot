import Orig2
import Orig2.ForkSwapOff

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-!
# Orig2/ForkSwapOffMain - the frame at a real cover/direct pair, the removal endpoint, the splice

READ-ONLY scratch.  No source edit, no commit.

Contents:

* `coverFrame` - the two-pile frame `SwapOff k'' k` between the cover state
  `slide x -> c` and the direct state `slide x -> b''`, with run `[x]`;
* `swapOff_removal_eq` - **the removal endpoint**: on a frame pair with run
  `[x]`, the legal removal `slide x : J2 -> J1` at the `s`-side lands exactly on
  the `t`-side state.  This is the splice residual as a `∀` over the frame;
* `corridor_shorter` - the shorter witness play (replace the cover/uncover pair
  by the direct slide run).
-/

namespace BPMain

open CommuteStep
open BaseFrame

/-! ## 1. The frame at a real cover/direct pair -/

/-- **THE COVER/DIRECT FRAME.**  With the lander `x` on TOP of its pile `a`
(singleton run), a cover `x -> c` (pile `k`) and a direct slide `x -> b''`
(pile `k''`) produce states that differ only on `(k'', k)`, with the run `[x]`
sitting on `k` in the cover state and on `k''` in the direct state. -/
theorem coverFrame
    {A : State} {x c : Card} {a k k'' : Anchor} {b'' : Base}
    (hA : A.WF)
    (hxa : A.pileOfTop x = some a)
    (hck : A.pileOfTop c = some k) (hka : k ≠ a)
    (hcpd : A.canPlace x (Sum.inr c) = true)
    (hcp0 : A.canPlace x b'' = true)
    (hk'' : tgt A b'' = some k'') (hk''a : k'' ≠ a) (hk''k : k'' ≠ k)
    (hcell : below x (A.piles a).faceUp ≠ [] ∨
      (below x (A.piles a).faceUp = [] ∧ (A.piles a).hidden = []))
    (hstep1 : State.step A (Move.tabToTab x (Sum.inr c)) = some (slideSt A x (Sum.inr c) a))
    (hstep0 : State.step A (Move.tabToTab x b'') = some (slideSt A x b'' a)) :
    SameOffR k'' k [x] (slideSt A x (Sum.inr c) a) (slideSt A x b'' a) := by
  have hsingle : fromCard x (A.piles a).faceUp = [x] :=
    NoSelfKit.fromCard_singleton_of_last (runOK_nodup (hA.runOK_of a))
      (pileOfTop_top hxa).2
  have hk''T : tgt A b'' = some k'' := hk''
  have hckT : tgt A (Sum.inr c) = some k := by rw [tgt_inr]; exact hck
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, [x], A.piles k'', A.piles k, ?_, ?_, ?_, ?_⟩, rfl⟩
  · rw [slideSt_found, slideSt_found]
  · rw [slideSt_stock, slideSt_stock]
  · rw [slideSt_waste, slideSt_waste]
  · rw [slideSt_drawStep, slideSt_drawStep]
  · intro j hj1 hj2
    rw [slideSt_piles_at hA hcpd hckT hka hcell j,
        slideSt_piles_at hA hcp0 hk''T hk''a hcell j]
    by_cases hja : j = a
    · rw [hja]
      simp only [ite_eq_left trivial, ite_eq_right (Ne.symm hka), ite_eq_right hk''a]
    · rw [ite_eq_right hja, ite_eq_right hja]
      by_cases hjk'' : j = k''
      · exact absurd hjk'' hj1
      · by_cases hjk : j = k
        · exact absurd hjk hj2
        · rw [ite_eq_right hjk'', ite_eq_right hjk]
  · -- s.piles k''
    rw [slideSt_piles_other_gen hA hckT hka (j := k'') hk''a hk''k]
  · -- t.piles k'' = base ++ [x]
    rw [slideSt_piles_target_gen hA hcp0 hk''T hk''a, hsingle]
  · -- t.piles k
    rw [slideSt_piles_other_gen hA hk''T hk''a (j := k) hka (Ne.symm hk''k)]
  · -- s.piles k = base ++ [x]
    rw [slideSt_piles_target_gen hA hcpd hckT hka, hsingle]

/-! ## 2. The removal endpoint -/

/-- **THE REMOVAL ENDPOINT.**  On a two-pile frame with run `[x]`, if `x` tops
the `s`-side special pile `J2` and the removal `slide x` targets the `t`-side
special pile `J1`, then the removal's endpoint IS the `t`-side state.  (This is
the splice residual as a `∀` over the frame - a concrete commutation, not a
restatement.) -/
theorem swapOff_removal_eq
    {J1 J2 : Anchor} {s t s3 : State} {x : Card} {b'' : Base}
    (hF : SwapOff J1 J2 s t) (hrun : hF.run = [x])
    (hsWF : s.WF) (htWF : t.WF)
    (hx : s.pileOfTop x = some J2)
    (hne : J1 ≠ J2)
    (hcp : s.canPlace x b'' = true)
    (hk'' : tgt s b'' = some J1)
    (hcell : below x (s.piles J2).faceUp ≠ [] ∨
      (below x (s.piles J2).faceUp = [] ∧ (s.piles J2).hidden = []))
    (hstep : State.step s (Move.tabToTab x b'') = some s3) :
    s3 = t := by
  obtain ⟨a, hhold, hcp', hne', hs3⟩ := step_tabToTab_slideSt hstep
  have hJa : J2 = a := (Option.some.inj (hhold.symm.trans
    (Drain.pileHolding_of_pileOfTop hsWF hx))).symm
  subst hJa
  have hsrc : (slideSt s x b'' J2).piles J2 =
      { s.piles J2 with faceUp := below x (s.piles J2).faceUp } := by
    rw [slideSt_piles_source_gen hsWF hk'' hne]
    exact CommuteStep.afterRunRemoved_eq_faceUp hcell
  have htgt : (slideSt s x b'' J2).piles J1 =
      { s.piles J1 with faceUp :=
          (s.piles J1).faceUp ++ fromCard x (s.piles J2).faceUp } :=
    slideSt_piles_target_gen hsWF hcp hk'' hne
  have hsJ2 : s.piles J2 = { hF.base2 with faceUp := hF.base2.faceUp ++ [x] } := by
    rw [hF.hJ2s, hrun]
  have hsJ1 : s.piles J1 = hF.base1 := hF.hJ1s
  have htJ1 : t.piles J1 = { hF.base1 with faceUp := hF.base1.faceUp ++ [x] } := by
    rw [hF.hJ1t, hrun]
  have htJ2 : t.piles J2 = hF.base2 := hF.hJ2t
  have hnd : (s.piles J2).faceUp.Nodup := runOK_nodup (hsWF.runOK_of J2)
  have hlast : lastOf (s.piles J2).faceUp = some x := by
    rw [hsJ2, lastOf_snoc]
  have hbelow : below x (s.piles J2).faceUp = hF.base2.faceUp := by
    rw [NoSelfKit.below_eq_chop_of_last hnd hlast, hsJ2, chop_snoc]
  have hfrom : fromCard x (s.piles J2).faceUp = [x] :=
    NoSelfKit.fromCard_singleton_of_last hnd hlast
  have e2 : (slideSt s x b'' J2).piles J2 = t.piles J2 := by
    rw [hsrc, hbelow, htJ2, hsJ2]
  have e1 : (slideSt s x b'' J2).piles J1 = t.piles J1 := by
    rw [htgt, hfrom, hsJ1, htJ1]
  have eo : ∀ j, j ≠ J1 → j ≠ J2 → (slideSt s x b'' J2).piles j = t.piles j := by
    intro j hj1 hj2
    rw [slideSt_piles_other_gen hsWF hk'' hne hj2 hj1]
    exact hF.off j hj1 hj2
  rw [hs3]
  apply State.ext
  · rw [slideSt_found]
    exact hF.found_eq
  · funext j
    by_cases h1 : j = J1
    · subst h1; exact e1
    · by_cases h2 : j = J2
      · subst h2; exact e2
      · exact eo j h1 h2
  · rw [slideSt_stock]; exact hF.stock_eq
  · rw [slideSt_waste]; exact hF.waste_eq
  · rw [slideSt_drawStep]; exact hF.drawStep_eq

/-! ## 3. The splice -/

/-- **THE SHORTER WITNESS PLAY.**  Replace the cover/uncover word by the direct
slide run; the length drops by one. -/
theorem splice_shorter
    {A A1' A3 : State} {x c : Card} {b'' : Base} {l : List Move}
    (hdir : State.step A (Move.tabToTab x b'') = some A1')
    (hrev : reversibleAtW A (Move.tabToTab x b''))
    (hplay : ShufflePlayW A1' l A3) :
    ∃ l', ShufflePlayW A l' A3 ∧
      l'.length < (Move.tabToTab x (Sum.inr c) :: l ++ [Move.tabToTab x b'']).length := by
  refine ⟨Move.tabToTab x b'' :: l, Walk.cons hrev hdir hplay, ?_⟩
  simp only [List.length_cons, List.length_append]
  omega

/-- **THE GATED CORRIDOR SHORTENS.**  All the frame-transport data are
hypotheses; the conclusion is the shorter witness play.  The `hEnd` slot is
`swapOff_removal_eq`'s conclusion (it is discharged there, not assumed). -/
theorem corridor_shorter
    {A A1 A1' A2 A2' A3 : State} {x c : Card} {a k k'' : Anchor} {b'' : Base}
    {l : List Move}
    (hdir : State.step A (Move.tabToTab x b'') = some A1')
    (hrev : reversibleAtW A (Move.tabToTab x b''))
    (hplay' : ShufflePlayW A1' l A2') (hEnd : A3 = A2') :
    ∃ l', ShufflePlayW A l' A3 ∧
      l'.length < (Move.tabToTab x (Sum.inr c) :: l ++ [Move.tabToTab x b'']).length := by
  subst hEnd
  exact splice_shorter hdir hrev hplay'

/-- **THE CORRIDOR REPLAYS AND SHORTENS.**  The hypotheses are
BaseMain.CorridorReplay\'s gates, strengthened where the proof needs it: the
frame (with run [x]), the strong Blind2 interior certificate, and the direct
slide\'s reversibility.  The removal endpoint is DERIVED
(swapOff_removal_eq). -/
theorem corridor_replay
    {A A1 A1' A2 A2' A3 : State} {x c : Card} {a k k'' : Anchor} {b'' : Base}
    {l : List Move}
    (hdir : State.step A (Move.tabToTab x b'') = some A1')
    (hrev : reversibleAtW A (Move.tabToTab x b''))
    (hFR : SameOffR k'' k [x] A1 A1')
    (hA1WF : A1.WF) (hA1'WF : A1'.WF)
    (hplay : ShufflePlayW A1 l A2) (hcert : PlayCert k'' k A1 l)
    (hrem : State.step A2 (Move.tabToTab x b'') = some A3)
    (hx : A2.pileOfTop x = some k) (hne : k'' ≠ k)
    (hcp : A2.canPlace x b'' = true) (htgt : tgt A2 b'' = some k'')
    (hcell : below x (A2.piles k).faceUp ≠ [] ∨
      (below x (A2.piles k).faceUp = [] ∧ (A2.piles k).hidden = []))
    (hA2WF : A2.WF) :
    ∃ l', ShufflePlayW A l' A3 ∧
      l'.length < (Move.tabToTab x (Sum.inr c) :: l ++ [Move.tabToTab x b'']).length := by
  obtain ⟨F, hFRun⟩ := hFR
  obtain ⟨A2', hplay', hF2⟩ := F.play hplay hFRun hA1WF hA1'WF hcert
  obtain ⟨F2, hrun2⟩ := hF2
  have hA2'WF : A2'.WF := SatDifferCensus.ShufflePlayW.wf_end hplay' hA1'WF
  have hEnd : A3 = A2' :=
    swapOff_removal_eq F2 hrun2 hA2WF hA2'WF hx hne hcp htgt hcell hrem
  rw [← hEnd] at hplay'
  exact splice_shorter hdir hrev hplay'

end BPMain

#print axioms BPMain.coverFrame
#print axioms BPMain.swapOff_removal_eq
#print axioms BPMain.splice_shorter
#print axioms BPMain.corridor_shorter
#print axioms BPMain.corridor_replay
