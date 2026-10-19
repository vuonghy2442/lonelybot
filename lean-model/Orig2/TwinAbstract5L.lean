import Orig2.TwinBothCovered
import Orig2.TwinPreludePath
import Orig2.TwinSwapRecipe
import Orig2.TwinSpliceUnique

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# Temp/TwinAbstract5L — the abstract one-rider both-covered 5L block

The concrete world-B route (`TwinBothCovered.play5`) clears the rider
`J♥` off `Q♠`, runs the frozen one-raise 3-leg recipe at the exposed
`Q♠`, and re-seats `J♥` on `Q♠` at its new parent.  This card isolates
the state computation: no pile decomposition is needed.  Each of the
five letters is a reversible step, so the seat footprint of each letter
is read off the step inversions alone.

The endpoint is the strict twin swap of the source, hence a
`SelfSwapSeg` by `selfSwapSeg_of_strict`.  The remaining hypotheses are
exactly the two source seats, the rider's source seat, and the five
witness shuffles.  The split `hpre`/`hblock`/`hpost` binders are retained
for interface compatibility with the suggested statement; the proof
consumes the concatenated five-move witness `hplay` directly.  In
particular the rider on `x.twin` is never inspected: it rides the slide.

Zero `sorry`, zero `Classical.choice`.
-/

open State
open TwinSpliceComm

/-! ## §0. Walk rider and seat-footprint helpers -/

/-- Expose the first step of a walk. -/
private theorem walk_cons_inv {P : State → Move → Prop}
    {st s' : State} {m : Move} {ρ : List Move}
    (h : Walk P st (m :: ρ) s') :
    ∃ s1, P st m ∧ State.step st m = some s1 ∧ Walk P s1 ρ s' := by
  cases h with
  | cons hlet hstep hrest => exact ⟨_, hlet, hstep, hrest⟩

/-- A raise changes every other card's seat only if that card is the
raised one; this is the two-case seat footprint (`raise_seat_change_of_seated`
for seated cards, `raise_seat_none` for unseated ones). -/
private theorem raise_seat_change_all {u v : State} {d c : Card}
    (hwf : u.WF) (hstep : State.step u (Move.tabToFound d) = some v)
    (hrev : reversibleAtW u (Move.tabToFound d)) (hcd : c ≠ d) :
    seatOf v c = seatOf u c := by
  by_cases hnone : seatOf u c = none
  · obtain ⟨-, a, hpa, -⟩ := step_tabToFound_inv hstep
    rw [raise_seat_none hwf hstep hrev hpa hnone hcd, hnone]
  · exact raise_seat_change_of_seated hstep hrev hnone hcd

/-- A card which is the top of a pile has a nonempty seat. -/
private theorem seat_ne_none_of_pileOfTop {st : State} {c : Card} {a : Anchor}
    (hwf : st.WF) (hpa : st.pileOfTop c = some a) : seatOf st c ≠ none := by
  have hmem : c ∈ (st.piles a).faceUp := lastOf_mem (tfc_pileOfTop_top hpa).2
  have hhold : st.pileHolding c = some a := (pileHolding_eq_some_iff hwf).mpr hmem
  rw [tfc_seatOf_pair hhold]
  cases hg : List.getLast? (below c (st.piles a).faceUp) <;> simp

/-- A card held in a pile has a nonempty seat. -/
private theorem seat_ne_none_of_pileHolding {st : State} {c : Card} {a : Anchor}
    (hhold : st.pileHolding c = some a) : seatOf st c ≠ none := by
  rw [tfc_seatOf_pair hhold]
  cases hg : List.getLast? (below c (st.piles a).faceUp) <;> simp

/-! ## §1. The abstract strict endpoint -/

/-- **The abstract one-rider both-covered 5L endpoint.**  The five
letters raise the rider `y`, raise `x`, slide `x.twin` onto `x`'s
vacated parent `z`, pull `x` onto `x.twin`'s vacated parent `z.twin`,
and finally re-seat `y` on `x`.  The endpoint is the strict twin swap
of the source.

The pile layout is not constrained beyond the two source seats and the
rider's source seat: the seat footprint of each letter is entirely
determined by the step shapes. -/
theorem twinPairSwapStrict_abstract5L
    {s u w0 w : State} {x y z : Card}
    (hwf : s.WF) (_hwf' : w.WF)
    (hx : seatOf s x = some (Sum.inr z))
    (hxt : seatOf s x.twin = some (Sum.inr z.twin))
    (hy : seatOf s y = some (Sum.inr x))
    (_hpre : ShufflePlayW s [Move.tabToFound y] u)
    (_hblock : ShufflePlayW u
      [Move.tabToFound x, Move.tabToTab x.twin (Sum.inr z),
        Move.foundToTab x (Sum.inr z.twin)] w0)
    (_hpost : ShufflePlayW w0 [Move.foundToTab y (Sum.inr x)] w)
    (hplay : ShufflePlayW s
      [Move.tabToFound y, Move.tabToFound x, Move.tabToTab x.twin (Sum.inr z),
        Move.foundToTab x (Sum.inr z.twin), Move.foundToTab y (Sum.inr x)] w) :
    twinPairSwapStrict s w x := by
  -- §1.0 Expose the five steps.
  obtain ⟨s1, hrev1, hstep1, rest1⟩ := walk_cons_inv hplay
  obtain ⟨s2, hrev2, hstep2, rest2⟩ := walk_cons_inv rest1
  obtain ⟨s3, hrev3, hstep3, rest3⟩ := walk_cons_inv rest2
  obtain ⟨s4, hrev4, hstep4, rest4⟩ := walk_cons_inv rest3
  obtain ⟨s5, hrev5, hstep5, rest5⟩ := walk_cons_inv rest4
  have h5w : s5 = w :=
    Option.some.inj (by simpa [State.run] using Walk_run _ rest5)
  subst s5
  have hwf1 : s1.WF := step_wf hwf hstep1
  have hwf2 : s2.WF := step_wf hwf1 hstep2
  have hwf3 : s3.WF := step_wf hwf2 hstep3
  have hwf4 : s4.WF := step_wf hwf3 hstep4
  -- §1.1 Step inversions: the raised tops and the slide's donor.
  obtain ⟨hnext1, a1, hpa1, hs1⟩ := step_tabToFound_inv hstep1
  obtain ⟨hnext2, a2, hpa2, hs2⟩ := step_tabToFound_inv hstep2
  obtain ⟨b3, hhold3, hcp3, hfr3, hs3⟩ := step_tabToTab_inv hstep3
  obtain ⟨c4, htop4, hc4, hcp4, hs4⟩ := step_foundToTab_inv hstep4
  obtain ⟨c5, htop5, hc5, hcp5, hs5⟩ := step_foundToTab_inv hstep5
  subst c4
  subst c5
  -- §1.2 The rider, the two twins, and the two raised tops are distinct.
  have hyx : y ≠ x := by
    intro hxy
    have hnone : seatOf s1 x = none := by
      simpa [hxy] using seatOf_tabToFound_mover_none hwf hstep1
    exact seat_ne_none_of_pileOfTop hwf1 hpa2 hnone
  have hyt : y ≠ x.twin := by
    intro hxy
    have hnone1 : seatOf s1 x.twin = none := by
      simpa [hxy] using seatOf_tabToFound_mover_none hwf hstep1
    have hnone2 : seatOf s2 x.twin = none :=
      raise_seat_none hwf1 hstep2 hrev2 hpa2 hnone1 (card_twin_ne x)
    exact seat_ne_none_of_pileHolding hhold3 hnone2
  -- §1.3 The seat trajectory of the pair and the rider.
  have hs1_xt : seatOf s1 x.twin = some (Sum.inr z.twin) :=
    (raise_seat_change_of_seated hstep1 hrev1 (by rw [hxt]; simp) hyt.symm).trans hxt
  have hs1_y : seatOf s1 y = none := seatOf_tabToFound_mover_none hwf hstep1
  have hs2_x : seatOf s2 x = none := seatOf_tabToFound_mover_none hwf1 hstep2
  have hs2_xt : seatOf s2 x.twin = seatOf s1 x.twin :=
    raise_seat_change_of_seated hstep2 hrev2 (by rw [hs1_xt]; simp) (card_twin_ne x)
  have hs2_y : seatOf s2 y = none :=
    raise_seat_none hwf1 hstep2 hrev2 hpa2 hs1_y hyx
  have hs3_x : seatOf s3 x = none := by
    rw [tfc_seat_point_edit hwf2 hstep3 hrev3 x]
    rw [ite_eq_right (fun h => card_twin_ne x h.symm), hs2_x]
  have hs3_xt : seatOf s3 x.twin = some (Sum.inr z) := by
    rw [tfc_seat_point_edit hwf2 hstep3 hrev3 x.twin, ite_eq_left rfl]
  have hs3_y : seatOf s3 y = none := by
    rw [tfc_seat_point_edit hwf2 hstep3 hrev3 y]
    rw [ite_eq_right hyt, hs2_y]
  have hs4_x : seatOf s4 x = some (Sum.inr z.twin) :=
    seatOf_foundToTab_mover hwf3 hstep4
  have hs4_xt : seatOf s4 x.twin = some (Sum.inr z) :=
    (pull_seat_change hstep4 x.twin (card_twin_ne x)).trans hs3_xt
  have hs4_y : seatOf s4 y = none :=
    (pull_seat_change hstep4 y hyx).trans hs3_y
  have hw_x : seatOf w x = some (Sum.inr z.twin) :=
    (pull_seat_change hstep5 x hyx.symm).trans hs4_x
  have hw_xt : seatOf w x.twin = some (Sum.inr z) :=
    (pull_seat_change hstep5 x.twin hyt.symm).trans hs4_xt
  have hw_y : seatOf w y = some (Sum.inr x) :=
    seatOf_foundToTab_mover hwf4 hstep5
  -- §1.4 Every other seat is unchanged.
  have hother : ∀ c, c ≠ x → c ≠ x.twin → seatOf w c = seatOf s c := by
    intro c hcx hcxt
    by_cases hcy : c = y
    · subst c
      rw [hw_y, hy]
    · have h1 : seatOf s1 c = seatOf s c :=
        raise_seat_change_all hwf hstep1 hrev1 hcy
      have h2 : seatOf s2 c = seatOf s1 c :=
        raise_seat_change_all hwf1 hstep2 hrev2 hcx
      have h3 : seatOf s3 c = seatOf s2 c := by
        rw [tfc_seat_point_edit hwf2 hstep3 hrev3 c]
        rw [ite_eq_right hcxt]
      have h4 : seatOf s4 c = seatOf s3 c := pull_seat_change hstep4 c hcx
      have h5 : seatOf w c = seatOf s4 c := pull_seat_change hstep5 c hcy
      exact h5.trans (h4.trans (h3.trans (h2.trans h1)))
  -- §1.5 The hidden decks and draw step.
  have hhidden : boardFixed s w := by
    refine ⟨?_, ?_⟩
    · intro a
      have h1 := hidden_eq_of_rev_step hwf hstep1 hrev1 a
      have h2 := hidden_eq_of_rev_step hwf1 hstep2 hrev2 a
      have h3 := hidden_eq_of_rev_step hwf2 hstep3 hrev3 a
      have h4 := hidden_eq_of_rev_step hwf3 hstep4 hrev4 a
      have h5 := hidden_eq_of_rev_step hwf4 hstep5 hrev5 a
      exact (h5.trans (h4.trans (h3.trans (h2.trans h1)))).symm
    · -- drawStep: each of the five successor shapes keeps it.
      have hd1 : s1.drawStep = s.drawStep := by
        rw [hs1]; rfl
      have hd2 : s2.drawStep = s1.drawStep := by
        rw [hs2]; rfl
      have hd3 : s3.drawStep = s2.drawStep := by
        rw [hs3, putRun_drawStep, setPile_drawStep]
      have hd4 : s4.drawStep = s3.drawStep := by
        rw [hs4, putCard_drawStep, setFound_drawStep]
      have hd5 : w.drawStep = s4.drawStep := by
        rw [hs5, putCard_drawStep, setFound_drawStep]
      rw [hd5, hd4, hd3, hd2, hd1]
  -- §1.6 Foundations round-trip.
  have hf1_self : s1.found y.suit = s.found y.suit ++ [y] := by
    rw [hs1]; exact setFound_found_self
  have hf1_other : ∀ σ, σ ≠ y.suit → s1.found σ = s.found σ := by
    intro σ hσ
    rw [hs1]; exact setFound_found_ne hσ
  have hf2_self : s2.found x.suit = s1.found x.suit ++ [x] := by
    rw [hs2]; exact setFound_found_self
  have hf2_other : ∀ σ, σ ≠ x.suit → s2.found σ = s1.found σ := by
    intro σ hσ
    rw [hs2]; exact setFound_found_ne hσ
  have hf3 : s3.found = s2.found := by
    rw [hs3, putRun_found, setPile_found]
  have hf4_self : s4.found x.suit = chop (s3.found x.suit) := by
    rw [hs4, putCard_found]; exact setFound_found_self
  have hf4_other : ∀ σ, σ ≠ x.suit → s4.found σ = s3.found σ := by
    intro σ hσ
    rw [hs4, putCard_found]; exact setFound_found_ne hσ
  have hf5_self : w.found y.suit = chop (s4.found y.suit) := by
    rw [hs5, putCard_found]; exact setFound_found_self
  have hf5_other : ∀ σ, σ ≠ y.suit → w.found σ = s4.found σ := by
    intro σ hσ
    rw [hs5, putCard_found]; exact setFound_found_ne hσ
  have hfound : foundsFixed s w := by
    intro σ
    by_cases hsame : x.suit = y.suit
    · -- Both raised cards share a suit: the pulls undo the raises in reverse.
      by_cases hσ : σ = x.suit
      · subst σ
        have hf1x : s1.found x.suit = s.found x.suit ++ [y] := by
          simpa [← hsame] using hf1_self
        have h4y : s4.found x.suit = s.found x.suit ++ [y] := by
          rw [hf4_self, hf3, hf2_self, hf1x, chop_snoc]
        have h5y : w.found x.suit = chop (s4.found x.suit) := by
          simpa [← hsame] using hf5_self
        rw [h5y, h4y, chop_snoc]
      · have hσy : σ ≠ y.suit := fun h => hσ (h.trans hsame.symm)
        rw [hf5_other σ hσy, hf4_other σ hσ, hf3,
          hf2_other σ hσ, hf1_other σ hσy]
    · -- Different suits: each foundation row is restored separately.
      have hysx : y.suit ≠ x.suit := fun h => hsame h.symm
      by_cases hσx : σ = x.suit
      · subst σ
        rw [hf5_other x.suit hsame, hf4_self, hf3, hf2_self,
          hf1_other x.suit hsame, chop_snoc]
      · by_cases hσy : σ = y.suit
        · subst σ
          have h4y : s4.found y.suit = s.found y.suit ++ [y] := by
            rw [hf4_other y.suit hysx, hf3,
              hf2_other y.suit hysx, hf1_self]
          rw [hf5_self, h4y, chop_snoc]
        · rw [hf5_other σ hσy, hf4_other σ hσx, hf3,
            hf2_other σ hσx, hf1_other σ hσy]
  -- §1.7 Stock, waste, and the cut.
  have hstock1 : s1.stock = s.stock := by rw [hs1]; rfl
  have hstock2 : s2.stock = s1.stock := by rw [hs2]; rfl
  have hstock3 : s3.stock = s2.stock := by rw [hs3, putRun_stock, setPile_stock]
  have hstock4 : s4.stock = s3.stock := by rw [hs4, putCard_stock, setFound_stock]
  have hstock5 : w.stock = s4.stock := by rw [hs5, putCard_stock, setFound_stock]
  have hstock : s.stock = w.stock := by
    rw [hstock5, hstock4, hstock3, hstock2, hstock1]
  have hwaste1 : s1.waste = s.waste := by rw [hs1]; rfl
  have hwaste2 : s2.waste = s1.waste := by rw [hs2]; rfl
  have hwaste3 : s3.waste = s2.waste := by rw [hs3, putRun_waste, setPile_waste]
  have hwaste4 : s4.waste = s3.waste := by rw [hs4, putCard_waste, setFound_waste]
  have hwaste5 : w.waste = s4.waste := by rw [hs5, putCard_waste, setFound_waste]
  have hwaste : s.waste = w.waste := by
    rw [hwaste5, hwaste4, hwaste3, hwaste2, hwaste1]
  -- §1.8 Assemble the strict letter.
  refine ⟨?_, ?_, hother, hhidden, hfound, hstock, hwaste, ?_⟩
  · rw [hw_x, hxt]
  · rw [hw_xt, hx]
  · unfold cutOf
    rw [hstock]

/-! ## §2. The self-swap segment -/

/-- **The abstract one-rider both-covered 5L `SelfSwapSeg`.**  The strict
endpoint above feeds `selfSwapSeg_of_strict`; the five moves are exactly
the concrete world-B `play5pub`. -/
theorem selfSwapSeg_abstract5L
    {s u w0 w : State} {x y z : Card}
    (hwf : s.WF) (hwf' : w.WF)
    (hx : seatOf s x = some (Sum.inr z))
    (hxt : seatOf s x.twin = some (Sum.inr z.twin))
    (hy : seatOf s y = some (Sum.inr x))
    (hpre : ShufflePlayW s [Move.tabToFound y] u)
    (hblock : ShufflePlayW u
      [Move.tabToFound x, Move.tabToTab x.twin (Sum.inr z),
        Move.foundToTab x (Sum.inr z.twin)] w0)
    (hpost : ShufflePlayW w0 [Move.foundToTab y (Sum.inr x)] w)
    (hplay : ShufflePlayW s
      [Move.tabToFound y, Move.tabToFound x, Move.tabToTab x.twin (Sum.inr z),
        Move.foundToTab x (Sum.inr z.twin), Move.foundToTab y (Sum.inr x)] w) :
    SelfSwapSeg x s w
      [Move.tabToFound y, Move.tabToFound x, Move.tabToTab x.twin (Sum.inr z),
        Move.foundToTab x (Sum.inr z.twin), Move.foundToTab y (Sum.inr x)] :=
  selfSwapSeg_of_strict hwf hwf' ⟨z, hx⟩ ⟨z, hxt⟩
    (twinPairSwapStrict_abstract5L hwf hwf' hx hxt hy hpre hblock hpost hplay)
    hplay

#print axioms twinPairSwapStrict_abstract5L
#print axioms selfSwapSeg_abstract5L
