import Orig2.TwinAbstract5L
import Orig2.TwinPreludePath
import Orig2.TwinSwapRecipe
import Orig2.TwinSpliceUnique

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open State
open TwinSpliceComm

private theorem walk_cons_inv7 {P : State → Move → Prop}
    {st s' : State} {m : Move} {ρ : List Move}
    (h : Walk P st (m :: ρ) s') :
    ∃ s1, P st m ∧ State.step st m = some s1 ∧ Walk P s1 ρ s' := by
  cases h with
  | cons hlet hstep hrest => exact ⟨_, hlet, hstep, hrest⟩

private theorem raise_seat_change_all7 {u v : State} {d c : Card}
    (hwf : u.WF) (hstep : State.step u (Move.tabToFound d) = some v)
    (hrev : reversibleAtW u (Move.tabToFound d)) (hcd : c ≠ d) :
    seatOf v c = seatOf u c := by
  by_cases hnone : seatOf u c = none
  · obtain ⟨-, a, hpa, -⟩ := step_tabToFound_inv hstep
    rw [raise_seat_none hwf hstep hrev hpa hnone hcd, hnone]
  · exact raise_seat_change_of_seated hstep hrev hnone hcd

private theorem seat_ne_none_of_pileOfTop7 {st : State} {c : Card} {a : Anchor}
    (hwf : st.WF) (hpa : st.pileOfTop c = some a) : seatOf st c ≠ none := by
  have hmem : c ∈ (st.piles a).faceUp := lastOf_mem (tfc_pileOfTop_top hpa).2
  have hhold : st.pileHolding c = some a := (pileHolding_eq_some_iff hwf).mpr hmem
  rw [tfc_seatOf_pair hhold]
  cases hg : List.getLast? (below c (st.piles a).faceUp) <;> simp

private theorem seat_ne_none_of_pileHolding7 {st : State} {c : Card} {a : Anchor}
    (hhold : st.pileHolding c = some a) : seatOf st c ≠ none := by
  rw [tfc_seatOf_pair hhold]
  cases hg : List.getLast? (below c (st.piles a).faceUp) <;> simp

theorem twinPairSwapStrict_abstract7L
    {s w : State} {x y1 y2 z : Card}
    (hwf : s.WF) (hwf' : w.WF)
    (hx : seatOf s x = some (Sum.inr z))
    (hxt : seatOf s x.twin = some (Sum.inr z.twin))
    (hy1 : seatOf s y1 = some (Sum.inr x))
    (hy2 : seatOf s y2 = some (Sum.inr y1))
    (hplay : ShufflePlayW s
      [Move.tabToFound y2, Move.tabToFound y1, Move.tabToFound x,
        Move.tabToTab x.twin (Sum.inr z), Move.foundToTab x (Sum.inr z.twin),
        Move.foundToTab y1 (Sum.inr x), Move.foundToTab y2 (Sum.inr y1)] w) :
    twinPairSwapStrict s w x := by
  obtain ⟨s1, hrev1, hstep1, rest1⟩ := walk_cons_inv7 hplay
  obtain ⟨s2, hrev2, hstep2, rest2⟩ := walk_cons_inv7 rest1
  obtain ⟨s3, hrev3, hstep3, rest3⟩ := walk_cons_inv7 rest2
  obtain ⟨s4, hrev4, hstep4, rest4⟩ := walk_cons_inv7 rest3
  obtain ⟨s5, hrev5, hstep5, rest5⟩ := walk_cons_inv7 rest4
  obtain ⟨s6, hrev6, hstep6, rest6⟩ := walk_cons_inv7 rest5
  obtain ⟨s7, hrev7, hstep7, rest7⟩ := walk_cons_inv7 rest6
  have h7w : s7 = w := Option.some.inj (by simpa [State.run] using Walk_run _ rest7)
  subst s7
  have hwf1 : s1.WF := step_wf hwf hstep1
  have hwf2 : s2.WF := step_wf hwf1 hstep2
  have hwf3 : s3.WF := step_wf hwf2 hstep3
  have hwf4 : s4.WF := step_wf hwf3 hstep4
  have hwf5 : s5.WF := step_wf hwf4 hstep5
  have hwf6 : s6.WF := step_wf hwf5 hstep6
  obtain ⟨-, a1, hpa1, hshape1⟩ := step_tabToFound_inv hstep1
  obtain ⟨-, a2, hpa2, hshape2⟩ := step_tabToFound_inv hstep2
  obtain ⟨-, a3, hpa3, hshape3⟩ := step_tabToFound_inv hstep3
  obtain ⟨b4, hhold4, hcp4, hfr4, hshape4⟩ := step_tabToTab_inv hstep4
  obtain ⟨c5, htop5, hc5, hcp5, hshape5⟩ := step_foundToTab_inv hstep5
  obtain ⟨c6, htop6, hc6, hcp6, hshape6⟩ := step_foundToTab_inv hstep6
  obtain ⟨c7, htop7, hc7, hcp7, hshape7⟩ := step_foundToTab_inv hstep7
  subst c5
  subst c6
  subst c7
  have hy2y1 : y2 ≠ y1 := by
    intro h
    have hnone : seatOf s1 y1 = none := by
      rw [← h]
      exact seatOf_tabToFound_mover_none hwf hstep1
    exact seat_ne_none_of_pileOfTop7 hwf1 hpa2 hnone
  have hy1x : y1 ≠ x := by
    intro h
    have hnone : seatOf s2 x = none := by
      rw [← h]
      exact seatOf_tabToFound_mover_none hwf1 hstep2
    exact seat_ne_none_of_pileOfTop7 hwf2 hpa3 hnone
  have hy1xt : y1 ≠ x.twin := by
    intro h
    have hnone2 : seatOf s2 x.twin = none := by
      rw [← h]
      exact seatOf_tabToFound_mover_none hwf1 hstep2
    have hnone3 : seatOf s3 x.twin = none :=
      raise_seat_none hwf2 hstep3 hrev3 hpa3 hnone2 (card_twin_ne x)
    exact seat_ne_none_of_pileHolding7 hhold4 hnone3
  have hy2x : y2 ≠ x := by
    intro h
    have hnone1 : seatOf s1 x = none := by
      rw [← h]
      exact seatOf_tabToFound_mover_none hwf hstep1
    have hnone2 : seatOf s2 x = none :=
      raise_seat_none hwf1 hstep2 hrev2 hpa2 hnone1 (fun h' => hy1x h'.symm)
    exact seat_ne_none_of_pileOfTop7 hwf2 hpa3 hnone2
  have hy2xt : y2 ≠ x.twin := by
    intro h
    have hnone1 : seatOf s1 x.twin = none := by
      rw [← h]
      exact seatOf_tabToFound_mover_none hwf hstep1
    have hnone2 : seatOf s2 x.twin = none :=
      raise_seat_none hwf1 hstep2 hrev2 hpa2 hnone1 (fun h' => hy1xt h'.symm)
    have hnone3 : seatOf s3 x.twin = none :=
      raise_seat_none hwf2 hstep3 hrev3 hpa3 hnone2 (card_twin_ne x)
    exact seat_ne_none_of_pileHolding7 hhold4 hnone3
  have hx1 : seatOf s1 x = some (Sum.inr z) :=
    (raise_seat_change_of_seated hstep1 hrev1 (by rw [hx]; simp)
      (fun h => hy2x h.symm)).trans hx
  have hxt1 : seatOf s1 x.twin = some (Sum.inr z.twin) :=
    (raise_seat_change_of_seated hstep1 hrev1 (by rw [hxt]; simp)
      (fun h => hy2xt h.symm)).trans hxt
  have hy1_1 : seatOf s1 y1 = some (Sum.inr x) :=
    (raise_seat_change_of_seated hstep1 hrev1 (by rw [hy1]; simp)
      (fun h => hy2y1 h.symm)).trans hy1
  have hpre5 : ShufflePlayW s1 [Move.tabToFound y1] s2 :=
    Walk.cons hrev2 hstep2 (Walk.nil s2)
  have hblock5 : ShufflePlayW s2
      [Move.tabToFound x, Move.tabToTab x.twin (Sum.inr z),
        Move.foundToTab x (Sum.inr z.twin)] s5 :=
    Walk.cons hrev3 hstep3 (Walk.cons hrev4 hstep4
      (Walk.cons hrev5 hstep5 (Walk.nil s5)))
  have hpost5 : ShufflePlayW s5 [Move.foundToTab y1 (Sum.inr x)] s6 :=
    Walk.cons hrev6 hstep6 (Walk.nil s6)
  have hmid : ShufflePlayW s1
      [Move.tabToFound y1, Move.tabToFound x, Move.tabToTab x.twin (Sum.inr z),
        Move.foundToTab x (Sum.inr z.twin), Move.foundToTab y1 (Sum.inr x)] s6 :=
    Walk.cons hrev2 hstep2 (Walk.cons hrev3 hstep3 (Walk.cons hrev4 hstep4
      (Walk.cons hrev5 hstep5 (Walk.cons hrev6 hstep6 (Walk.nil s6)))))
  have h5 := twinPairSwapStrict_abstract5L (s := s1) (u := s2) (w0 := s5)
    (w := s6) (x := x) (y := y1) (z := z)
    hwf1 hwf6 hx1 hxt1 hy1_1 hpre5 hblock5 hpost5 hmid
  obtain ⟨h5x, h5xt, h5other, h5board, h5found, h5stock, h5waste, -⟩ := h5
  have hw_x : seatOf w x = some (Sum.inr z.twin) := by
    rw [pull_seat_change hstep7 x (fun h => hy2x h.symm), h5x, hxt1]
  have hw_xt : seatOf w x.twin = some (Sum.inr z) := by
    rw [pull_seat_change hstep7 x.twin (fun h => hy2xt h.symm), h5xt, hx1]
  have hother : ∀ c, c ≠ x → c ≠ x.twin → seatOf w c = seatOf s c := by
    intro c hcx hcxt
    by_cases hcy : c = y2
    · subst c
      rw [seatOf_foundToTab_mover hwf6 hstep7, hy2]
    · rw [pull_seat_change hstep7 c hcy, h5other c hcx hcxt,
        raise_seat_change_all7 hwf hstep1 hrev1 hcy]
  have hhidden : ∀ a, (s.piles a).hidden = (w.piles a).hidden := by
    intro a
    have h1 : (s1.piles a).hidden = (s.piles a).hidden :=
      hidden_eq_of_rev_step hwf hstep1 hrev1 a
    have hb : (s1.piles a).hidden = (s6.piles a).hidden := h5board.1 a
    have h7 : (w.piles a).hidden = (s6.piles a).hidden :=
      hidden_eq_of_rev_step hwf6 hstep7 hrev7 a
    exact (h1.symm.trans hb).trans h7.symm
  have hdraw : s.drawStep = w.drawStep := by
    have hd1 : s1.drawStep = s.drawStep := by rw [hshape1]; rfl
    have hd7 : w.drawStep = s6.drawStep := by
      rw [hshape7, putCard_drawStep, setFound_drawStep]
    exact (hd1.symm.trans h5board.2).trans hd7.symm
  have hfound : foundsFixed s w := by
    intro σ
    by_cases hσ : σ = y2.suit
    · subst σ
      have hf6 : s6.found y2.suit = s1.found y2.suit := (h5found y2.suit).symm
      have hf1 : s1.found y2.suit = s.found y2.suit ++ [y2] := by
        rw [hshape1]; exact setFound_found_self
      have hf7 : w.found y2.suit = chop (s6.found y2.suit) := by
        rw [hshape7, putCard_found]; exact setFound_found_self
      rw [hf7, hf6, hf1, chop_snoc]
    · have hf1 : s1.found σ = s.found σ := by
        rw [hshape1]; exact setFound_found_ne hσ
      have hf7 : w.found σ = s6.found σ := by
        rw [hshape7, putCard_found]; exact setFound_found_ne hσ
      rw [hf7, ← h5found σ, ← hf1]
  have hstock : s.stock = w.stock := by
    have hs1 : s1.stock = s.stock := by rw [hshape1]; rfl
    have hs7 : w.stock = s6.stock := by rw [hshape7, putCard_stock, setFound_stock]
    exact hs1.symm.trans (h5stock.trans hs7.symm)
  have hwaste : s.waste = w.waste := by
    have hs1 : s1.waste = s.waste := by rw [hshape1]; rfl
    have hs7 : w.waste = s6.waste := by rw [hshape7, putCard_waste, setFound_waste]
    exact hs1.symm.trans (h5waste.trans hs7.symm)
  refine ⟨?_, ?_, hother, ⟨hhidden, hdraw⟩, hfound, hstock, hwaste, ?_⟩
  · rw [hw_x, hxt]
  · rw [hw_xt, hx]
  · unfold cutOf
    rw [hstock]

theorem selfSwapSeg_abstract7L
    {s w : State} {x y1 y2 z : Card}
    (hwf : s.WF) (hwf' : w.WF)
    (hx : seatOf s x = some (Sum.inr z))
    (hxt : seatOf s x.twin = some (Sum.inr z.twin))
    (hy1 : seatOf s y1 = some (Sum.inr x))
    (hy2 : seatOf s y2 = some (Sum.inr y1))
    (hplay : ShufflePlayW s
      [Move.tabToFound y2, Move.tabToFound y1, Move.tabToFound x,
        Move.tabToTab x.twin (Sum.inr z), Move.foundToTab x (Sum.inr z.twin),
        Move.foundToTab y1 (Sum.inr x), Move.foundToTab y2 (Sum.inr y1)] w) :
    SelfSwapSeg x s w
      [Move.tabToFound y2, Move.tabToFound y1, Move.tabToFound x,
        Move.tabToTab x.twin (Sum.inr z), Move.foundToTab x (Sum.inr z.twin),
        Move.foundToTab y1 (Sum.inr x), Move.foundToTab y2 (Sum.inr y1)] :=
  selfSwapSeg_of_strict hwf hwf' ⟨z, hx⟩ ⟨z, hxt⟩
    (twinPairSwapStrict_abstract7L hwf hwf' hx hxt hy1 hy2 hplay) hplay

#print axioms twinPairSwapStrict_abstract7L
#print axioms selfSwapSeg_abstract7L
