import Orig2

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-!
# Orig2/ForkSwapOff - the two-pile frame (`SameOff`) and its transport

READ-ONLY scratch.  No source edit, no commit.  Zero `sorry`, zero
`Classical.choice`, zero `native_decide`; `#print axioms` battery at the tail.

## What this card does

`Temp/Base_Report.md` section 6(1) names the one genuinely new induction of the
base clause: the **two-pile frame**.  A cover of `c` by the lander `x` moves the
run headed by `x` from `x`'s pile onto `c`'s pile; the *direct* slide moves the
same run onto the removal's pile.  The two resulting states differ only on the
pair `(cover pile, landing pile)`: the same run `R` sits atop the first in one
state and atop the second in the other, everything else is *literally* equal.
See `Temp/BP_Report.md` for the whole card.
-/

namespace BaseFrame

open CommuteStep

/-! ## 1. The two-pile frame -/

/-- **THE TWO-PILE FRAME `SwapOff J1 J2 s t`.**  `s` and `t` agree on the
foundations, the stock, the waste and the draw step, agree on *every* pile
outside `{J1, J2}`, and differ on the pair exactly by the same run `R`: `R`
sits atop `J2` in `s` and atop `J1` in `t`. -/
structure SwapOff (J1 J2 : Anchor) (s t : State) where
  found_eq : s.found = t.found
  stock_eq : s.stock = t.stock
  waste_eq : s.waste = t.waste
  drawStep_eq : s.drawStep = t.drawStep
  off : ∀ j, j ≠ J1 → j ≠ J2 → s.piles j = t.piles j
  run : List Card
  base1 : Pile
  base2 : Pile
  hJ1s : s.piles J1 = base1
  hJ1t : t.piles J1 = { base1 with faceUp := base1.faceUp ++ run }
  hJ2t : t.piles J2 = base2
  hJ2s : s.piles J2 = { base2 with faceUp := base2.faceUp ++ run }

/-- The `Prop`-level form of the frame. -/
abbrev SameOff (J1 J2 : Anchor) (s t : State) : Prop := Nonempty (SwapOff J1 J2 s t)

/-- The frame with its run PINNED: the transport preserves the run witness. -/
abbrev SameOffR (J1 J2 : Anchor) (R : List Card) (s t : State) : Prop :=
  ∃ F : SwapOff J1 J2 s t, F.run = R

/-- **`R = []` IS THE NET-ZERO.**  With the run empty the frame is equality. -/
theorem SwapOff.collapse {J1 J2 : Anchor} {s t : State} (h : SwapOff J1 J2 s t)
    (hR : h.run = []) : s = t := by
  have hpiles : s.piles = t.piles := by
    funext j
    by_cases h1 : j = J1
    · subst h1
      rw [h.hJ1s, h.hJ1t, hR, List.append_nil]
    · by_cases h2 : j = J2
      · subst h2
        rw [h.hJ2s, h.hJ2t, hR, List.append_nil]
      · exact h.off j h1 h2
  cases s with
  | mk f p st w d =>
    cases t with
    | mk f' p' st' w' d' =>
      have hp : p = p' := hpiles
      have hf : f = f' := h.found_eq
      have hst : st = st' := h.stock_eq
      have hw : w = w' := h.waste_eq
      have hd : d = d' := h.drawStep_eq
      subst hp; subst hf; subst hst; subst hw; subst hd
      rfl

/-- The frame from literal agreement (the `R = []` direction, usable before the
run witness is fixed). -/
theorem sameOff_of_eq {J1 J2 : Anchor} {s t : State}
    (hf : s.found = t.found) (hst : s.stock = t.stock) (hw : s.waste = t.waste)
    (hd : s.drawStep = t.drawStep) (hp : ∀ j, s.piles j = t.piles j) :
    SameOff J1 J2 s t :=
  ⟨{ found_eq := hf, stock_eq := hst, waste_eq := hw, drawStep_eq := hd
     off := fun j _ _ => hp j
     run := []
     base1 := s.piles J1
     base2 := s.piles J2
     hJ1s := rfl
     hJ1t := by rw [hp J1, List.append_nil]
     hJ2t := (hp J2).symm
     hJ2s := by rw [hp J2, List.append_nil] }⟩

theorem SwapOff.faceUp_J1s {J1 J2 : Anchor} {s t : State} (h : SwapOff J1 J2 s t) :
    (s.piles J1).faceUp = h.base1.faceUp := by rw [h.hJ1s]

theorem SwapOff.faceUp_J1t {J1 J2 : Anchor} {s t : State} (h : SwapOff J1 J2 s t) :
    (t.piles J1).faceUp = h.base1.faceUp ++ h.run := by rw [h.hJ1t]

theorem SwapOff.faceUp_J2s {J1 J2 : Anchor} {s t : State} (h : SwapOff J1 J2 s t) :
    (s.piles J2).faceUp = h.base2.faceUp ++ h.run := by rw [h.hJ2s]

theorem SwapOff.faceUp_J2t {J1 J2 : Anchor} {s t : State} (h : SwapOff J1 J2 s t) :
    (t.piles J2).faceUp = h.base2.faceUp := by rw [h.hJ2t]

/-! ## 2. Membership in the special piles -/

theorem SwapOff.notMem_all {J1 J2 : Anchor} {s t : State} (h : SwapOff J1 J2 s t)
    {w : Card} (h1 : w ∉ (s.piles J1).faceUp) (h2 : w ∉ (s.piles J2).faceUp) :
    w ∉ (t.piles J1).faceUp ∧ w ∉ (t.piles J2).faceUp := by
  constructor
  · intro hw
    rw [h.faceUp_J1t] at hw
    rcases List.mem_append.mp hw with hh | hh
    · exact h1 (by rw [h.faceUp_J1s]; exact hh)
    · exact h2 (by rw [h.faceUp_J2s]; exact List.mem_append_right _ hh)
  · intro hw
    rw [h.faceUp_J2t] at hw
    exact h2 (by rw [h.faceUp_J2s]; exact List.mem_append_left _ hw)

/-! ## 3. The letter predicates -/

/-- **`Blind2 J1 J2 st q`** - the letter `q` reads and writes no card of either
special pile at `st`. -/
def Blind2 (J1 J2 : Anchor) (st : State) : Move → Prop
  | Move.draw => True
  | Move.wasteToFound _ => True
  | Move.wasteToTab _ _ => True
  | Move.tabToFound w => w ∉ (st.piles J1).faceUp ∧ w ∉ (st.piles J2).faceUp
  | Move.foundToTab _ b =>
      b ≠ Sum.inl J1 ∧ b ≠ Sum.inl J2 ∧
        (∀ z, b = Sum.inr z → z ∉ (st.piles J1).faceUp ∧ z ∉ (st.piles J2).faceUp)
  | Move.tabToTab y b =>
      y ∉ (st.piles J1).faceUp ∧ y ∉ (st.piles J2).faceUp ∧
      b ≠ Sum.inl J1 ∧ b ≠ Sum.inl J2 ∧
        (∀ z, b = Sum.inr z → z ∉ (st.piles J1).faceUp ∧ z ∉ (st.piles J2).faceUp)

/-- **`NoSelfAt st q`** - the letter is not a same-pile slide (a self-slide is
the identity on the piles and is excluded so the slide frame stays clean). -/
def NoSelfAt (st : State) : Move → Prop
  | Move.tabToTab y b =>
      ∀ a K, st.pileHolding y = some a → tgt st b = some K → K ≠ a
  | _ => True

theorem SwapOff.blind2_transfer {J1 J2 : Anchor} {s t : State}
    (h : SwapOff J1 J2 s t) {q : Move} (hq : Blind2 J1 J2 s q) :
    Blind2 J1 J2 t q := by
  cases q with
  | draw => exact trivial
  | wasteToFound c => exact trivial
  | wasteToTab c b => exact trivial
  | tabToFound w =>
      obtain ⟨h1, h2⟩ := hq
      exact h.notMem_all h1 h2
  | foundToTab c b =>
      obtain ⟨hb1, hb2, hz⟩ := hq
      refine ⟨hb1, hb2, ?_⟩
      intro z hz'
      exact h.notMem_all (hz z hz').1 (hz z hz').2
  | tabToTab y b =>
      obtain ⟨hy1, hy2, hb1, hb2, hz⟩ := hq
      refine ⟨(h.notMem_all hy1 hy2).1, (h.notMem_all hy1 hy2).2, hb1, hb2, ?_⟩
      intro z hz'
      exact h.notMem_all (hz z hz').1 (hz z hz').2

/-- The certificate along a play: each letter is blind to the two piles and is
not a self-slide, at the state where it fires. -/
def PlayCert (J1 J2 : Anchor) : State → List Move → Prop
  | _, [] => True
  | st, q :: t =>
      Blind2 J1 J2 st q ∧ NoSelfAt st q ∧
        ∀ s', State.step st q = some s' → PlayCert J1 J2 s' t

/-! ## 4. Search congruence across the frame -/

theorem lastOf_ne_some_of_not_mem {l : List Card} {w : Card} (h : w ∉ l) :
    lastOf l ≠ some w := by
  intro hl
  exact h (lastOf_mem hl)

theorem SwapOff.pileOfTop_congr {J1 J2 : Anchor} {s t : State}
    (h : SwapOff J1 J2 s t) {w : Card}
    (h1 : w ∉ (s.piles J1).faceUp) (h2 : w ∉ (s.piles J2).faceUp) :
    s.pileOfTop w = t.pileOfTop w := by
  obtain ⟨ht1, ht2⟩ := h.notMem_all h1 h2
  unfold State.pileOfTop
  apply SplitKit.firstWhere_congr_local
  intro a
  by_cases ha1 : a = J1
  · rw [ha1]
    show decide (lastOf (s.piles J1).faceUp = some w) =
      decide (lastOf (t.piles J1).faceUp = some w)
    rw [decide_false_of_not (lastOf_ne_some_of_not_mem h1),
      decide_false_of_not (lastOf_ne_some_of_not_mem ht1)]
  · by_cases ha2 : a = J2
    · rw [ha2]
      show decide (lastOf (s.piles J2).faceUp = some w) =
        decide (lastOf (t.piles J2).faceUp = some w)
      rw [decide_false_of_not (lastOf_ne_some_of_not_mem h2),
        decide_false_of_not (lastOf_ne_some_of_not_mem ht2)]
    · show decide (lastOf (s.piles a).faceUp = some w) =
        decide (lastOf (t.piles a).faceUp = some w)
      rw [show (s.piles a).faceUp = (t.piles a).faceUp from by
        rw [h.off a ha1 ha2]]

theorem SwapOff.pileHolding_congr {J1 J2 : Anchor} {s t : State}
    (h : SwapOff J1 J2 s t) {w : Card}
    (h1 : w ∉ (s.piles J1).faceUp) (h2 : w ∉ (s.piles J2).faceUp) :
    s.pileHolding w = t.pileHolding w := by
  obtain ⟨ht1, ht2⟩ := h.notMem_all h1 h2
  unfold State.pileHolding
  apply SplitKit.firstWhere_congr_local
  intro a
  by_cases ha1 : a = J1
  · rw [ha1]
    rw [decide_false_of_not h1, decide_false_of_not ht1]
  · by_cases ha2 : a = J2
    · rw [ha2]
      rw [decide_false_of_not h2, decide_false_of_not ht2]
    · rw [show s.piles a = t.piles a from h.off a ha1 ha2]

theorem nextUp_congr {s t : State} (h : s.found = t.found) (c : Card) :
    s.nextUp c = t.nextUp c := by
  unfold State.nextUp State.foundHeight
  rw [h]

theorem wasteIs_congr {s t : State} (h : s.waste = t.waste) (c : Card) :
    s.wasteIs c = t.wasteIs c := by
  unfold State.wasteIs
  rw [h]

theorem SwapOff.canPlace_congr {J1 J2 : Anchor} {s t : State}
    (h : SwapOff J1 J2 s t) {c : Card} {b : Base}
    (hb1 : b ≠ Sum.inl J1) (hb2 : b ≠ Sum.inl J2)
    (hz : ∀ z, b = Sum.inr z → z ∉ (s.piles J1).faceUp ∧ z ∉ (s.piles J2).faceUp) :
    s.canPlace c b = t.canPlace c b := by
  cases b with
  | inl a =>
      have ha1 : a ≠ J1 := fun hh => hb1 (by rw [hh])
      have ha2 : a ≠ J2 := fun hh => hb2 (by rw [hh])
      show ((s.piles a).isEmpty && decide (c.rank = Rank.king)) =
        ((t.piles a).isEmpty && decide (c.rank = Rank.king))
      rw [h.off a ha1 ha2]
  | inr z =>
      show (match s.pileOfTop z with | some _ => canSitOn c z | none => false) =
        (match t.pileOfTop z with | some _ => canSitOn c z | none => false)
      rw [h.pileOfTop_congr (hz z rfl).1 (hz z rfl).2]

theorem SwapOff.tgt_congr {J1 J2 : Anchor} {s t : State}
    (h : SwapOff J1 J2 s t) {b : Base}
    (hb1 : b ≠ Sum.inl J1) (hb2 : b ≠ Sum.inl J2)
    (hz : ∀ z, b = Sum.inr z → z ∉ (s.piles J1).faceUp ∧ z ∉ (s.piles J2).faceUp) :
    tgt s b = tgt t b := by
  cases b with
  | inl a => rfl
  | inr z => exact h.pileOfTop_congr (hz z rfl).1 (hz z rfl).2

/-! ## 5. The slide's three pile formulas, without the cell condition -/

theorem slideSt_piles_source_gen {st : State} {c : Card} {b : Base} {a k : Anchor}
    (hwf : st.WF) (hk : tgt st b = some k) (hak : k ≠ a) :
    (slideSt st c b a).piles a =
      Pile.afterRunRemoved (st.piles a) (below c (st.piles a).faceUp) := by
  cases b with
  | inl k' =>
      obtain rfl : k = k' := (Option.some.inj hk).symm
      rw [slideSt, putRun_piles_inl]
      show (if a = k then ({ hidden := [], faceUp := fromCard c (st.piles a).faceUp } : Pile)
        else (st.setPile a ((st.piles a).afterRunRemoved
          (below c (st.piles a).faceUp))).piles a) = _
      rw [ite_eq_right (Ne.symm hak), setPile_piles_self]
  | inr z =>
      have hz : st.pileOfTop z = some k := hk
      rw [slideSt, putRun_piles_inr _ _ _ _
        (setPile_afterRunRemoved_pileOfTop hwf hz hak c)]
      show (if a = k then ({(st.setPile a ((st.piles a).afterRunRemoved
          (below c (st.piles a).faceUp))).piles k with
            faceUp := ((st.setPile a ((st.piles a).afterRunRemoved
              (below c (st.piles a).faceUp))).piles k).faceUp
                ++ fromCard c (st.piles a).faceUp} : Pile)
        else (st.setPile a ((st.piles a).afterRunRemoved
          (below c (st.piles a).faceUp))).piles a) = _
      rw [ite_eq_right (Ne.symm hak), setPile_piles_self]

theorem slideSt_piles_target_gen {st : State} {c : Card} {b : Base} {a k : Anchor}
    (hwf : st.WF) (hcp : st.canPlace c b = true) (hk : tgt st b = some k)
    (hak : k ≠ a) :
    (slideSt st c b a).piles k =
      { st.piles k with faceUp := (st.piles k).faceUp ++ fromCard c (st.piles a).faceUp } := by
  cases b with
  | inl k' =>
      obtain rfl : k = k' := (Option.some.inj hk).symm
      rw [slideSt, putRun_piles_inl]
      show (if k = k then ({ hidden := [], faceUp := fromCard c (st.piles a).faceUp } : Pile)
        else (st.setPile a ((st.piles a).afterRunRemoved
          (below c (st.piles a).faceUp))).piles k) =
        { st.piles k with faceUp := (st.piles k).faceUp ++ fromCard c (st.piles a).faceUp }
      rw [ite_eq_left rfl]
      obtain ⟨hhid, hfu⟩ := (Pile.isEmpty_eq _).mp ((canPlace_inl hcp).1)
      show ({ hidden := [], faceUp := fromCard c (st.piles a).faceUp } : Pile) =
        ({ hidden := (st.piles k).hidden,
           faceUp := (st.piles k).faceUp ++ fromCard c (st.piles a).faceUp } : Pile)
      rw [hhid, hfu, List.nil_append]
  | inr z =>
      have hz : st.pileOfTop z = some k := hk
      rw [slideSt, putRun_piles_inr _ _ _ _
        (setPile_afterRunRemoved_pileOfTop hwf hz hak c)]
      show (if k = k then _ else
        (st.setPile a ((st.piles a).afterRunRemoved
          (below c (st.piles a).faceUp))).piles k) = _
      rw [ite_eq_left rfl]
      rw [show (st.setPile a ((st.piles a).afterRunRemoved
            (below c (st.piles a).faceUp))).piles k = st.piles k from
        setPile_piles_ne hak]

theorem slideSt_piles_other_gen {st : State} {c : Card} {b : Base} {a k : Anchor}
    (hwf : st.WF) (hk : tgt st b = some k) (hak : k ≠ a)
    {j : Anchor} (hja : j ≠ a) (hjk : j ≠ k) :
    (slideSt st c b a).piles j = st.piles j := by
  cases b with
  | inl k' =>
      obtain rfl : k = k' := (Option.some.inj hk).symm
      rw [slideSt, putRun_piles_inl]
      show (if j = k then _ else
        (st.setPile a ((st.piles a).afterRunRemoved
          (below c (st.piles a).faceUp))).piles j) = st.piles j
      rw [ite_eq_right hjk, setPile_piles_ne hja]
  | inr z =>
      have hz : st.pileOfTop z = some k := hk
      rw [slideSt, putRun_piles_inr _ _ _ _
        (setPile_afterRunRemoved_pileOfTop hwf hz hak c)]
      show (if j = k then _ else
        (st.setPile a ((st.piles a).afterRunRemoved
          (below c (st.piles a).faceUp))).piles j) = st.piles j
      rw [ite_eq_right hjk, setPile_piles_ne hja]

/-! ## 6. The draw's pool transfer -/

theorem recycle_pool {s t : State} (hs : s.stock = t.stock) (hw : s.waste = t.waste)
    (hd : s.drawStep = t.drawStep) :
    t.recycle.stock = s.recycle.stock ∧ t.recycle.waste = s.recycle.waste ∧
    t.recycle.drawStep = s.recycle.drawStep := by
  have h1 : t.stock = s.stock := hs.symm
  have h2 : t.waste = s.waste := hw.symm
  have h3 : t.drawStep = s.drawStep := hd.symm
  cases hst : s.stock with
  | nil =>
      cases hwa : s.waste with
      | nil => simp only [State.recycle, hst, hwa, h1, h2, h3]; exact ⟨trivial, trivial, trivial⟩
      | cons w ws => simp only [State.recycle, hst, hwa, h1, h2, h3]; exact ⟨trivial, trivial, trivial⟩
  | cons x xs => simp only [State.recycle, hst, h1, h2, h3]; exact ⟨trivial, trivial, trivial⟩

/-! ## 7. The oracle is frame-invariant -/

theorem SwapOff.reversibleOf_congr {J1 J2 : Anchor} {s t : State}
    (h : SwapOff J1 J2 s t) {q : Move} (hq : Blind2 J1 J2 s q) :
    reversibleOf s q = reversibleOf t q := by
  cases q with
  | draw =>
      show drawR s = drawR t
      unfold drawR
      rw [h.stock_eq, h.waste_eq, h.drawStep_eq]
  | wasteToFound c => rfl
  | wasteToTab c b => rfl
  | tabToFound c =>
      obtain ⟨hc1, hc2⟩ := hq
      show tabToFoundR s c = tabToFoundR t c
      cases hp : s.pileOfTop c with
      | none =>
          have htp : t.pileOfTop c = none := by
            rw [← h.pileOfTop_congr hc1 hc2, hp]
          simp only [tabToFoundR, nextUp_congr h.found_eq c, hp, htp]
      | some a =>
          have hca : c ∈ (s.piles a).faceUp := lastOf_mem (pileOfTop_top hp).2
          have ha1 : a ≠ J1 := fun hh => hc1 (by rw [hh] at hca; exact hca)
          have ha2 : a ≠ J2 := fun hh => hc2 (by rw [hh] at hca; exact hca)
          have htp : t.pileOfTop c = some a := by
            rw [← h.pileOfTop_congr hc1 hc2, hp]
          simp only [tabToFoundR, nextUp_congr h.found_eq c, hp, htp,
            h.off a ha1 ha2]
  | foundToTab c b =>
      obtain ⟨hb1, hb2, hz⟩ := hq
      show foundToTabR s c b = foundToTabR t c b
      have hft : t.foundTop c.suit = s.foundTop c.suit := by
        unfold State.foundTop; rw [h.found_eq]
      simp only [foundToTabR, hft, h.canPlace_congr hb1 hb2 hz]
  | tabToTab c b =>
      obtain ⟨hc1, hc2, hb1, hb2, hz⟩ := hq
      show tabToTabR s c b = tabToTabR t c b
      have hph : t.pileHolding c = s.pileHolding c :=
        (h.pileHolding_congr hc1 hc2).symm
      cases hs : s.pileHolding c with
      | none =>
          have htp : t.pileHolding c = none := by rw [hph, hs]
          simp only [tabToTabR, hs, htp]
      | some a =>
          have hca : c ∈ (s.piles a).faceUp := pileHolding_mem hs
          have ha1 : a ≠ J1 := fun hh => hc1 (by rw [hh] at hca; exact hca)
          have ha2 : a ≠ J2 := fun hh => hc2 (by rw [hh] at hca; exact hca)
          have htp : t.pileHolding c = some a := by rw [hph, hs]
          simp only [tabToTabR, hs, htp, h.canPlace_congr hb1 hb2 hz,
            h.off a ha1 ha2]

/-! ## 8. Reversibility transports -/

theorem SwapOff.rev_transfer {J1 J2 : Anchor} {s t : State} (h : SwapOff J1 J2 s t)
    (hsWF : s.WF) (htWF : t.WF) {q : Move} (hq : Blind2 J1 J2 s q)
    (hrev : reversibleAtW s q) : reversibleAtW t q := by
  have h1 : reversibleOf s q = true := (reversibleOf_iff_reversibleAtW hsWF q).mpr hrev
  have h2 : reversibleOf t q = true := by
    rw [← h.reversibleOf_congr hq]; exact h1
  exact (reversibleOf_iff_reversibleAtW htWF q).mp h2

/-! ## 9. The step transport -/

/-- **A DRAW PRESERVES THE FRAME** (with the same run witness). -/
theorem SwapOff.draw {J1 J2 : Anchor} {s t s' : State} (hF : SwapOff J1 J2 s t)
    (h : s.stepDraw = some s') :
    ∃ t', t.stepDraw = some t' ∧ SameOffR J1 J2 hF.run s' t' := by
  obtain ⟨r, hr, hrne, hs'⟩ := draw_unfold h
  obtain ⟨hst, hwa, hdr⟩ := recycle_pool hF.stock_eq hF.waste_eq hF.drawStep_eq
  have htne : t.recycle.stock ≠ [] := by rw [hst, hr]; exact hrne
  let t' : State := { t.recycle with
      stock := (State.dealUpTo t.recycle.drawStep t.recycle.stock).2,
      waste := (State.dealUpTo t.recycle.drawStep t.recycle.stock).1.reverse
        ++ t.recycle.waste }
  have htst : State.dealStock t.recycle = some t' :=
    dealStock_eq_of_ne_nil _ htne
  have hrp : r.piles = s.piles := by rw [← hr]; exact _root_.recycle_piles s
  have htp : t.recycle.piles = t.piles := _root_.recycle_piles t
  refine ⟨t', htst, ⟨?_, ?_, ?_, ?_, ?_, hF.run, hF.base1, hF.base2, ?_, ?_, ?_, ?_⟩, rfl⟩
  · rw [hs']
    show r.found = t'.found
    show r.found = t.recycle.found
    rw [← hr]
    show s.recycle.found = t.recycle.found
    rw [_root_.recycle_found s, _root_.recycle_found t]
    exact hF.found_eq
  · rw [hs']
    show (State.dealUpTo r.drawStep r.stock).2 = t'.stock
    show (State.dealUpTo r.drawStep r.stock).2 =
      (State.dealUpTo t.recycle.drawStep t.recycle.stock).2
    rw [hst, hdr, hr]
  · rw [hs']
    show (State.dealUpTo r.drawStep r.stock).1.reverse ++ r.waste = t'.waste
    show (State.dealUpTo r.drawStep r.stock).1.reverse ++ r.waste =
      (State.dealUpTo t.recycle.drawStep t.recycle.stock).1.reverse ++ t.recycle.waste
    rw [hst, hdr, hwa, hr]
  · rw [hs']
    show r.drawStep = t'.drawStep
    show r.drawStep = t.recycle.drawStep
    rw [← hr, hdr]
  · intro j hj1 hj2
    rw [hs']
    show r.piles j = t'.piles j
    show r.piles j = t.recycle.piles j
    rw [hrp, htp]
    exact hF.off j hj1 hj2
  · rw [hs']
    show r.piles J1 = hF.base1
    rw [hrp]
    exact hF.hJ1s
  · show t'.piles J1 = _
    show t.recycle.piles J1 = _
    rw [htp]
    exact hF.hJ1t
  · show t'.piles J2 = hF.base2
    show t.recycle.piles J2 = hF.base2
    rw [htp]
    exact hF.hJ2t
  · rw [hs']
    show r.piles J2 = _
    rw [hrp]
    exact hF.hJ2s

/-- **THE LEGAL STEP TRANSPORTS.**  A legal, reversible `Blind2` non-self-slide
letter at `s` is legal at `t`, and the frame survives the step with the *same*
run witness.  (The two waste letters are excluded by reversibility.) -/
theorem SwapOff.step {J1 J2 : Anchor} {s t s' : State} {q : Move}
    (hF : SwapOff J1 J2 s t)
    (hsWF : s.WF) (htWF : t.WF)
    (hq : Blind2 J1 J2 s q)
    (hns : NoSelfAt s q)
    (hrev : reversibleAtW s q)
    (hstep : State.step s q = some s') :
    ∃ t', State.step t q = some t' ∧ SameOffR J1 J2 hF.run s' t' := by
  cases q with
  | draw =>
      have hd : s.stepDraw = some s' := hstep
      exact hF.draw hd
  | wasteToFound c => exact absurd hrev (wasteToFound_not_reversibleAtW s c)
  | wasteToTab c b => exact absurd hrev (wasteToTab_not_reversibleAtW s c b)
  | tabToFound w =>
      obtain ⟨hn, a, htop, hs⟩ := step_tabToFound_inv hstep
      obtain ⟨hw1, hw2⟩ := hq
      have ha1 : a ≠ J1 := by
        intro hh
        exact hw1 (lastOf_mem (pileOfTop_top (by rw [htop, hh])).2)
      have ha2 : a ≠ J2 := by
        intro hh
        exact hw2 (lastOf_mem (pileOfTop_top (by rw [htop, hh])).2)
      have htnext : t.nextUp w = true := by
        rw [← nextUp_congr hF.found_eq w]; exact hn
      have httop : t.pileOfTop w = some a := (hF.pileOfTop_congr hw1 hw2).symm.trans htop
      let t' : State := { t.setFound w.suit (t.found w.suit ++ [w]) with
          piles := fun a' => if a' = a then
            Pile.afterRunRemoved (t.piles a) (chop (t.piles a).faceUp) else t.piles a' }
      have htstep : State.step t (Move.tabToFound w) = some t' := by
        rw [step_tabToFound_eq, htnext, httop, ite_eq_left rfl]
      refine ⟨t', htstep, ⟨?_, ?_, ?_, ?_, ?_, hF.run, hF.base1, hF.base2, ?_, ?_, ?_, ?_⟩, rfl⟩
      · rw [hs]
        show (fun sf => if sf = w.suit then s.found w.suit ++ [w] else s.found sf)
          = (fun sf => if sf = w.suit then t.found w.suit ++ [w] else t.found sf)
        funext sf
        rw [hF.found_eq]
      · rw [hs]; exact hF.stock_eq
      · rw [hs]; exact hF.waste_eq
      · rw [hs]; exact hF.drawStep_eq
      · intro j hj1 hj2
        rw [hs]
        show (if j = a then Pile.afterRunRemoved (s.piles a) (chop (s.piles a).faceUp)
            else s.piles j) =
          (if j = a then Pile.afterRunRemoved (t.piles a) (chop (t.piles a).faceUp)
            else t.piles j)
        by_cases hja : j = a
        · rw [ite_eq_left hja, ite_eq_left hja, hF.off a ha1 ha2]
        · rw [ite_eq_right hja, ite_eq_right hja]; exact hF.off j hj1 hj2
      · rw [hs]
        show (if J1 = a then Pile.afterRunRemoved (s.piles a) (chop (s.piles a).faceUp)
            else s.piles J1) = hF.base1
        rw [ite_eq_right (Ne.symm ha1)]
        exact hF.hJ1s
      · show (if J1 = a then Pile.afterRunRemoved (t.piles a) (chop (t.piles a).faceUp)
            else t.piles J1) = _
        rw [ite_eq_right (Ne.symm ha1)]
        exact hF.hJ1t
      · show (if J2 = a then Pile.afterRunRemoved (t.piles a) (chop (t.piles a).faceUp)
            else t.piles J2) = hF.base2
        rw [ite_eq_right (Ne.symm ha2)]
        exact hF.hJ2t
      · rw [hs]
        show (if J2 = a then Pile.afterRunRemoved (s.piles a) (chop (s.piles a).faceUp)
            else s.piles J2) = { hF.base2 with faceUp := hF.base2.faceUp ++ hF.run }
        rw [ite_eq_right (Ne.symm ha2)]
        exact hF.hJ2s
  | foundToTab c b =>
      obtain ⟨c', hftop, hc, hcp, hs⟩ := step_foundToTab_pullSt hstep
      obtain ⟨hb1, hb2, hz⟩ := hq
      obtain ⟨K, hK⟩ := CommuteStep.exists_tgt_of_canPlace (u := s) (c := c) hcp
      have hK1 : K ≠ J1 := by
        intro hh
        cases b with
        | inl a => exact hb1 (by rw [Option.some.inj hK, hh])
        | inr z =>
            have hKz : s.pileOfTop z = some K := hK
            exact (hz z rfl).1 (lastOf_mem (pileOfTop_top (by rw [hKz, hh])).2)
      have hK2 : K ≠ J2 := by
        intro hh
        cases b with
        | inl a => exact hb2 (by rw [Option.some.inj hK, hh])
        | inr z =>
            have hKz : s.pileOfTop z = some K := hK
            exact (hz z rfl).2 (lastOf_mem (pileOfTop_top (by rw [hKz, hh])).2)
      have hcpt : t.canPlace c b = true := by
        rw [← hF.canPlace_congr hb1 hb2 hz]; exact hcp
      have hftopt : t.foundTop c.suit = some c' := by
        unfold State.foundTop at hftop ⊢
        rw [← hF.found_eq]; exact hftop
      have httgt : tgt t b = some K := (hF.tgt_congr hb1 hb2 hz).symm.trans hK
      let t' : State := pullSt t c b
      have htstep : State.step t (Move.foundToTab c b) = some t' := by
        show State.step t (Move.foundToTab c b) = some (pullSt t c b)
        rw [step_foundToTab_eq, hftopt]
        simp only [hc, hcpt, decide_true, Bool.true_and]
        rw [ite_eq_left trivial]
        rfl
      refine ⟨t', htstep, ⟨?_, ?_, ?_, ?_, ?_, hF.run, hF.base1, hF.base2, ?_, ?_, ?_, ?_⟩, rfl⟩
      · rw [hs]; exact CommuteStep.pullSt_found_congr hF.found_eq c b
      · rw [hs]
        change (pullSt s c b).stock = (pullSt t c b).stock
        rw [pullSt_stock, pullSt_stock]
        exact hF.stock_eq
      · rw [hs]
        change (pullSt s c b).waste = (pullSt t c b).waste
        rw [pullSt_waste, pullSt_waste]
        exact hF.waste_eq
      · rw [hs]
        change (pullSt s c b).drawStep = (pullSt t c b).drawStep
        rw [pullSt_drawStep, pullSt_drawStep]
        exact hF.drawStep_eq
      · intro j hj1 hj2
        rw [hs, pullSt_piles_at hK, pullSt_piles_at httgt]
        dsimp only
        by_cases hjk : j = K
        · rw [ite_eq_left hjk, ite_eq_left hjk]
          cases b with
          | inl a => rfl
          | inr z => rw [hF.off K hK1 hK2]
        · rw [ite_eq_right hjk, ite_eq_right hjk]; exact hF.off j hj1 hj2
      · rw [hs, pullSt_piles_ne hK (Ne.symm hK1)]; exact hF.hJ1s
      · rw [ pullSt_piles_ne httgt (Ne.symm hK1)]; exact hF.hJ1t
      · rw [ pullSt_piles_ne httgt (Ne.symm hK2)]; exact hF.hJ2t
      · rw [hs, pullSt_piles_ne hK (Ne.symm hK2)]; exact hF.hJ2s
  | tabToTab y b =>
      obtain ⟨a, hhold, hcp, hne, hs⟩ := step_tabToTab_slideSt hstep
      obtain ⟨hy1, hy2, hb1, hb2, hz⟩ := hq
      have hya : y ∈ (s.piles a).faceUp := pileHolding_mem hhold
      have ha1 : a ≠ J1 := fun hh => hy1 (by rw [hh] at hya; exact hya)
      have ha2 : a ≠ J2 := fun hh => hy2 (by rw [hh] at hya; exact hya)
      obtain ⟨K, hK⟩ := CommuteStep.exists_tgt_of_canPlace (u := s) (c := y) hcp
      have hK1 : K ≠ J1 := by
        intro hh
        cases b with
        | inl a' => exact hb1 (by rw [Option.some.inj hK, hh])
        | inr z =>
            have hKz : s.pileOfTop z = some K := hK
            exact (hz z rfl).1 (lastOf_mem (pileOfTop_top (by rw [hKz, hh])).2)
      have hK2 : K ≠ J2 := by
        intro hh
        cases b with
        | inl a' => exact hb2 (by rw [Option.some.inj hK, hh])
        | inr z =>
            have hKz : s.pileOfTop z = some K := hK
            exact (hz z rfl).2 (lastOf_mem (pileOfTop_top (by rw [hKz, hh])).2)
      have hKa : K ≠ a := hns a K hhold hK
      have hholdt : t.pileHolding y = some a := (hF.pileHolding_congr hy1 hy2).symm.trans hhold
      have hcpt : t.canPlace y b = true := by
        rw [← hF.canPlace_congr hb1 hb2 hz]; exact hcp
      have httgt : tgt t b = some K := (hF.tgt_congr hb1 hb2 hz).symm.trans hK
      have hpa : s.piles a = t.piles a := hF.off a ha1 ha2
      have hrun : fromCard y (t.piles a).faceUp = fromCard y (s.piles a).faceUp := by
        rw [hpa]
      have hne' : fromCard y (t.piles a).faceUp ≠ [] := by rw [hrun]; exact hne
      let t' : State := slideSt t y b a
      have htstep : State.step t (Move.tabToTab y b) = some t' := by
        show State.step t (Move.tabToTab y b) = some (slideSt t y b a)
        rw [step_tabToTab_eq, hholdt]
        simp only [hcpt]
        rw [ite_eq_left trivial]
        cases hf : fromCard y (t.piles a).faceUp with
        | nil => rw [hf] at hne'; exact absurd rfl hne'
        | cons x xs => rw [slideSt, hf]
      refine ⟨t', htstep, ⟨?_, ?_, ?_, ?_, ?_, hF.run, hF.base1, hF.base2, ?_, ?_, ?_, ?_⟩, rfl⟩
      · rw [hs, slideSt_found, slideSt_found]; exact hF.found_eq
      · rw [hs, slideSt_stock, slideSt_stock]; exact hF.stock_eq
      · rw [hs, slideSt_waste, slideSt_waste]; exact hF.waste_eq
      · rw [hs, slideSt_drawStep, slideSt_drawStep]; exact hF.drawStep_eq
      · intro j hj1 hj2
        rw [hs]
        by_cases hja : j = a
        · -- the source pile; `a = K` is excluded by `hKa`
          rw [hja]
          rw [slideSt_piles_source_gen hsWF hK hKa,
            slideSt_piles_source_gen htWF httgt hKa]
          rw [hpa]
        · by_cases hjk : j = K
          · rw [hjk]
            rw [slideSt_piles_target_gen hsWF hcp hK hKa,
              slideSt_piles_target_gen htWF hcpt httgt hKa,
              hF.off K hK1 hK2, hpa]
          · rw [slideSt_piles_other_gen hsWF hK hKa hja hjk,
              slideSt_piles_other_gen htWF httgt hKa hja hjk]
            exact hF.off j hj1 hj2
      · rw [hs, slideSt_piles_other_gen hsWF hK hKa (Ne.symm ha1) (Ne.symm hK1)]
        exact hF.hJ1s
      · rw [ slideSt_piles_other_gen htWF httgt hKa (Ne.symm ha1) (Ne.symm hK1)]
        exact hF.hJ1t
      · rw [ slideSt_piles_other_gen htWF httgt hKa (Ne.symm ha2) (Ne.symm hK2)]
        exact hF.hJ2t
      · rw [hs, slideSt_piles_other_gen hsWF hK hKa (Ne.symm ha2) (Ne.symm hK2)]
        exact hF.hJ2s

/-! ## 10. The whole-play replay -/

/-- **THE PLAY TRANSPORTS.**  A certified ShufflePlayW at s replays at 	
with the same letter list; the endpoints stay frame-related. -/
theorem SwapOff.play {J1 J2 : Anchor} {R : List Card} {s s' : State} {l : List Move}
    (hplay : ShufflePlayW s l s') {t : State} (hF : SwapOff J1 J2 s t) (hRun : hF.run = R)
    (hsWF : s.WF) (htWF : t.WF) (hcert : PlayCert J1 J2 s l) :
    ∃ t', ShufflePlayW t l t' ∧ SameOffR J1 J2 R s' t' := by
  induction hplay generalizing t with
  | nil st => exact ⟨t, Walk.nil t, ⟨hF, hRun⟩⟩
  | @cons st s1 W m ρ hrev hstep hrest ih =>
      obtain ⟨hb, hns, htail⟩ := hcert
      obtain ⟨t1, htstep, hF1⟩ := hF.step hsWF htWF hb hns hrev hstep
      obtain ⟨F1, hrun1⟩ := hF1
      have hs1 : s1.WF := step_wf hsWF hstep
      have ht1 : t1.WF := step_wf htWF htstep
      have hrev1 : reversibleAtW t m := hF.rev_transfer hsWF htWF hb hrev
      have hcert1 : PlayCert J1 J2 s1 ρ := htail s1 hstep
      obtain ⟨t2, hplay2, hF2⟩ := ih F1 (hrun1.trans hRun) hs1 ht1 hcert1
      exact ⟨t2, Walk.cons hrev1 htstep hplay2, hF2⟩


/-! ## 11. Run bookkeeping and the run version of the net-zero -/

theorem fromCard_append_not_mem {x : Card} {l m : List Card} (h : x ∉ l) :
    fromCard x (l ++ m) = fromCard x m := by
  induction l with
  | nil => rfl
  | cons y ys ih =>
      have hy : y ≠ x := fun hh => h (by rw [hh]; exact List.mem_cons_self ..)
      have hys : x ∉ ys := fun hm => h (List.mem_cons_of_mem _ hm)
      rw [List.cons_append, fromCard, ite_eq_right hy, ih hys]

theorem below_append_not_mem {x : Card} {l m : List Card} (h : x ∉ l) :
    below x (l ++ m) = l ++ below x m := by
  induction l with
  | nil => rfl
  | cons y ys ih =>
      have hy : y ≠ x := fun hh => h (by rw [hh]; exact List.mem_cons_self ..)
      have hys : x ∉ ys := fun hm => h (List.mem_cons_of_mem _ hm)
      rw [List.cons_append, below_cons, ite_eq_right hy, ih hys, List.cons_append]

theorem below_fromCard_self (x : Card) : ∀ l : List Card, below x (fromCard x l) = [] := by
  intro l
  induction l with
  | nil => rfl
  | cons y ys ih =>
      by_cases hy : y = x
      · subst hy
        rw [fromCard_head_eq, below_cons, ite_eq_left rfl]
      · rw [fromCard, ite_eq_right hy]
        exact ih

theorem fromCard_fromCard (x : Card) {l : List Card} (h : x ∈ l) :
    fromCard x (fromCard x l) = fromCard x l := by
  obtain ⟨t, ht⟩ := fromCard_eq_head_of_mem h
  rw [ht, fromCard_head_eq]

theorem mem_fromCard_of_mem {x : Card} {l : List Card} (h : x ∈ l) :
    x ∈ fromCard x l := by
  obtain ⟨t, ht⟩ := fromCard_eq_head_of_mem h
  rw [ht]
  exact List.mem_cons_self ..

/-! ## 12. The run version of the net-zero -/

/-- **THE RUN NET-ZERO.**  Cover with the whole run `R = fromCard x fu_a`, then
slide the same run off: the two-slide word lands on exactly the single direct
slide.  (The singleton case is `LandRes.slideSt_slideSt_self`.) -/
theorem slideSt_slideSt_run
    {st : State} {x d : Card} {b'' : Base} {a k k'' : Anchor} {R : List Card}
    (hwf : st.WF)
    (hhold : st.pileHolding x = some a)
    (hR : fromCard x (st.piles a).faceUp = R)
    (hk : st.pileOfTop d = some k) (hka : k ≠ a)
    (hcpd : st.canPlace x (Sum.inr d) = true)
    (hcp0 : st.canPlace x b'' = true)
    (hcp0s : (slideSt st x (Sum.inr d) a).canPlace x b'' = true)
    (hk'' : tgt st b'' = some k'') (hk''a : k'' ≠ a) (hk''k : k'' ≠ k)
    (hxnotk : x ∉ (st.piles k).faceUp)
    (hcell : below x (st.piles a).faceUp ≠ [] ∨
      (below x (st.piles a).faceUp = [] ∧ (st.piles a).hidden = []))
    (htgt : tgt (slideSt st x (Sum.inr d) a) b'' = some k'') :
    slideSt (slideSt st x (Sum.inr d) a) x b'' k = slideSt st x b'' a := by
  have hmem : x ∈ (st.piles a).faceUp := pileHolding_mem hhold
  have hRmem : x ∈ fromCard x (st.piles a).faceUp := mem_fromCard_of_mem hmem
  have hRne : R ≠ [] := by
    intro h0
    rw [hR, h0] at hRmem
    exact List.not_mem_nil hRmem
  have hstepc : State.step st (Move.tabToTab x (Sum.inr d)) =
      some (slideSt st x (Sum.inr d) a) := by
    rw [step_tabToTab_eq, hhold]
    simp only [hcpd]
    rw [ite_eq_left trivial]
    rw [show fromCard x (st.piles a).faceUp = R from hR]
    cases hc : R with
    | nil => exact absurd hc hRne
    | cons y ys => rw [slideSt, hR, hc]
  have hcwf : (slideSt st x (Sum.inr d) a).WF := step_wf hwf hstepc
  have hkT : tgt st (Sum.inr d) = some k := by rw [tgt_inr]; exact hk
  have hck : (slideSt st x (Sum.inr d) a).piles k =
      { st.piles k with faceUp := (st.piles k).faceUp ++ R } := by
    rw [slideSt_piles_at hwf hcpd hkT hka hcell k]
    rw [ite_eq_right hka, ite_eq_left rfl, hR]
  have hbelowk : below x ((st.piles k).faceUp ++ R) = (st.piles k).faceUp := by
    rw [below_append_not_mem hxnotk, ← hR, below_fromCard_self, List.append_nil]
  have hfromk : fromCard x ((st.piles k).faceUp ++ R) = R := by
    rw [fromCard_append_not_mem hxnotk, ← hR]
    exact fromCard_fromCard x hmem
  have hdk : d ∈ (st.piles k).faceUp := lastOf_mem (pileOfTop_top hk).2
  have hkne : (st.piles k).faceUp ≠ [] := by
    intro h0
    rw [h0] at hdk
    exact List.not_mem_nil hdk
  have hcellk : below x ((slideSt st x (Sum.inr d) a).piles k).faceUp ≠ [] ∨
      (below x ((slideSt st x (Sum.inr d) a).piles k).faceUp = [] ∧
        ((slideSt st x (Sum.inr d) a).piles k).hidden = []) := by
    left
    rw [hck]
    show below x ((st.piles k).faceUp ++ R) ≠ []
    rw [hbelowk]
    exact hkne
  have hca : (slideSt st x (Sum.inr d) a).piles a =
      { st.piles a with faceUp := below x (st.piles a).faceUp } := by
    rw [slideSt_piles_source_gen hwf hkT hka]
    exact CommuteStep.afterRunRemoved_eq_faceUp hcell
  have hck'' : (slideSt st x (Sum.inr d) a).piles k'' = st.piles k'' := by
    exact slideSt_piles_other_gen hwf hkT hka hk''a hk''k
  apply State.ext
  · rw [slideSt_found, slideSt_found, slideSt_found]
  · funext j
    rw [slideSt_piles_at hcwf hcp0s htgt hk''k hcellk j]
    rw [slideSt_piles_at hwf hcp0 hk'' hk''a hcell j]
    by_cases hja : j = a
    · rw [hja]
      simp only [ite_eq_left trivial, ite_eq_right (Ne.symm hka),
        ite_eq_right (Ne.symm hk''a), hca]
    · by_cases hjk : j = k
      · rw [hjk]
        simp only [ite_eq_left trivial, ite_eq_right hka,
          ite_eq_right hk''k, ite_eq_right (Ne.symm hk''k), hck]
        show { st.piles k with faceUp := below x ((st.piles k).faceUp ++ R) } = st.piles k
        rw [hbelowk]
      · by_cases hjk'' : j = k''
        · rw [hjk'']
          simp only [ite_eq_right hk''k, ite_eq_left trivial, ite_eq_right hk''a,
            hck'', hck, hfromk, hR]
        · have hj1 : j ≠ a := hja
          have hj2 : j ≠ k := hjk
          have hj3 : j ≠ k'' := hjk''
          simp only [ite_eq_right hj2, ite_eq_right hj3, ite_eq_right hj1,
            slideSt_piles_other_gen hwf hk'' hk''a hj1 hj3,
            slideSt_piles_other_gen hwf hkT hka hj1 hj2]
  · rw [slideSt_stock, slideSt_stock, slideSt_stock]
  · rw [slideSt_waste, slideSt_waste, slideSt_waste]
  · rw [slideSt_drawStep, slideSt_drawStep, slideSt_drawStep]

end BaseFrame


/-! ## 12. Axiom battery -/

#print axioms BaseFrame.SwapOff.collapse
#print axioms BaseFrame.sameOff_of_eq
#print axioms BaseFrame.SwapOff.notMem_all
#print axioms BaseFrame.SwapOff.blind2_transfer
#print axioms BaseFrame.SwapOff.pileOfTop_congr
#print axioms BaseFrame.SwapOff.pileHolding_congr
#print axioms BaseFrame.SwapOff.canPlace_congr
#print axioms BaseFrame.SwapOff.tgt_congr
#print axioms BaseFrame.slideSt_piles_source_gen
#print axioms BaseFrame.slideSt_piles_target_gen
#print axioms BaseFrame.slideSt_piles_other_gen
#print axioms BaseFrame.recycle_pool
#print axioms BaseFrame.SwapOff.reversibleOf_congr
#print axioms BaseFrame.SwapOff.rev_transfer
#print axioms BaseFrame.SwapOff.draw
#print axioms BaseFrame.SwapOff.step
#print axioms BaseFrame.SwapOff.play
#print axioms BaseFrame.fromCard_append_not_mem
#print axioms BaseFrame.below_append_not_mem
#print axioms BaseFrame.below_fromCard_self
#print axioms BaseFrame.mem_fromCard_of_mem
#print axioms BaseFrame.fromCard_fromCard
#print axioms BaseFrame.slideSt_slideSt_run
