import Orig2.DetourKit
import Orig2.Kit

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-!
# Orig2.TwinRaiseCommute — local commutation squares for the twin raise and pull

The pair-foundation moves of `FirstRaiseNormalization` — raising `x`, raising
`x.twin`, and pulling either twin — interact with the pair-free moves of a
no-draw prelude.  This card isolates the local squares:

* a raise of `x` commutes with a disjoint slide, a raise of another card, a
  pull to a disjoint empty seat, and a waste-to-foundation move in another
  suit (`raise_*_comm`);
* a pull of `x` commutes with a raise, a disjoint slide, and a waste-to-foundation
  move when the two foundation rows and landing piles are disjoint
  (`pull_*_comm`);
* the naive square fails exactly when the two moves compete for one
  foundation row or one pile; the `*_disabled` theorems record the sharp
  no-go conditions (`sameSuit`, the raised source pile, and an exposed
  card target).

All statements are in terms of `State.step`; the state combinators below are
only the literal successors read back by `step_tabToFound_inv`,
`step_tabToTab_inv`, and `step_foundToTab_inv`.  Zero `sorry`, zero
`Classical.choice`; every exported theorem is audited at the end.
-/

open State

namespace TwinRaiseCommute


/-! ### Raise state -/

def raisedAt (st : State) (c : Card) (a : Anchor) : State :=
  { st.setFound c.suit (st.found c.suit ++ [c]) with
    piles := fun a' =>
      if a' = a then Pile.afterRunRemoved (st.piles a) (chop (st.piles a).faceUp)
      else st.piles a' }

@[simp] theorem raisedAt_found_self (st : State) (c : Card) (a : Anchor) :
    (raisedAt st c a).found c.suit = st.found c.suit ++ [c] := by
  simp [raisedAt, State.setFound]

@[simp] theorem raisedAt_found_ne (st : State) (c : Card) (a : Anchor) (s : Suit)
    (hs : s ≠ c.suit) :
    (raisedAt st c a).found s = st.found s := by
  simp [raisedAt, State.setFound, hs]

@[simp] theorem raisedAt_piles_self (st : State) (c : Card) (a : Anchor) :
    (raisedAt st c a).piles a =
      Pile.afterRunRemoved (st.piles a) (chop (st.piles a).faceUp) := by
  simp [raisedAt, State.setFound]

@[simp] theorem raisedAt_piles_ne (st : State) (c : Card) (a a' : Anchor) (h : a' ≠ a) :
    (raisedAt st c a).piles a' = st.piles a' := by
  simp [raisedAt, h]

@[simp] theorem raisedAt_stock (st : State) (c : Card) (a : Anchor) :
    (raisedAt st c a).stock = st.stock := rfl

@[simp] theorem raisedAt_waste (st : State) (c : Card) (a : Anchor) :
    (raisedAt st c a).waste = st.waste := rfl

@[simp] theorem raisedAt_drawStep (st : State) (c : Card) (a : Anchor) :
    (raisedAt st c a).drawStep = st.drawStep := rfl

theorem step_tabToFound_raisedAt {st : State} {c : Card} {a : Anchor}
    (hnext : st.nextUp c = true) (hpo : st.pileOfTop c = some a) :
    State.step st (Move.tabToFound c) = some (raisedAt st c a) := by
  rw [step_tabToFound_eq]
  rw [ite_eq_left hnext]
  rw [hpo]
  rfl

/-! ### Slide state -/

def slidAt (st : State) (y : Card) (b : Base) (asrc : Anchor) : State :=
  (st.setPile asrc
    (Pile.afterRunRemoved (st.piles asrc) (below y (st.piles asrc).faceUp))).putRun
      (fromCard y (st.piles asrc).faceUp) b

@[simp] theorem slidAt_found (st : State) (y : Card) (b : Base) (asrc : Anchor) :
    (slidAt st y b asrc).found = st.found := by
  simp [slidAt, putRun_found, setPile_found]

@[simp] theorem slidAt_stock (st : State) (y : Card) (b : Base) (asrc : Anchor) :
    (slidAt st y b asrc).stock = st.stock := by
  simp [slidAt, putRun_stock, setPile_stock]

@[simp] theorem slidAt_waste (st : State) (y : Card) (b : Base) (asrc : Anchor) :
    (slidAt st y b asrc).waste = st.waste := by
  simp [slidAt, putRun_waste, setPile_waste]

@[simp] theorem slidAt_drawStep (st : State) (y : Card) (b : Base) (asrc : Anchor) :
    (slidAt st y b asrc).drawStep = st.drawStep := by
  simp [slidAt, putRun_drawStep, setPile_drawStep]

theorem fromCard_ne_nil_of_mem {c : Card} {l : List Card} (h : c ∈ l) :
    fromCard c l ≠ [] := by
  obtain ⟨t, ht⟩ := fromCard_eq_head_of_mem h
  rw [ht]
  simp

theorem step_tabToTab_some {st : State} {c : Card} {b : Base} {a : Anchor}
    (hh : st.pileHolding c = some a) (hcp : st.canPlace c b = true) :
    State.step st (Move.tabToTab c b) = some (slidAt st c b a) := by
  have hmem : c ∈ (st.piles a).faceUp := pileHolding_mem hh
  have hne : fromCard c (st.piles a).faceUp ≠ [] := fromCard_ne_nil_of_mem hmem
  simp only [State.step, hh, hcp, slidAt]
  cases hList : fromCard c (st.piles a).faceUp with
  | nil => exact absurd hList hne
  | cons w r => rfl

/-! ### Congruence helpers -/

theorem nextUp_congr_found {u v : State} (h : v.found = u.found) (c : Card) :
    v.nextUp c = u.nextUp c := by
  unfold State.nextUp State.foundHeight
  rw [h]

theorem pileOfTop_congr_piles {u v : State} (h : v.piles = u.piles) (z : Card) :
    v.pileOfTop z = u.pileOfTop z := by
  unfold State.pileOfTop State.topOf
  rw [h]

/-! ### Raising does not move another pile's top search -/

theorem pileOfTop_raisedAt_ne {u : State} {x z : Card} {a k : Anchor}
    (hwf : (raisedAt u x a).WF) (hpo : u.pileOfTop x = some a)
    (hzx : z ≠ x) (htop : (raisedAt u x a).pileOfTop z = some k) (hka : k ≠ a) :
    u.pileOfTop z = some k := by
  unfold State.pileOfTop at htop ⊢
  have htopU : u.topOf a = some x := by
    simpa [State.topOf, Pile.top] using (pileOfTop_top hpo).2
  have htopR : (raisedAt u x a).topOf a ≠ some z := by
    intro hcon
    have hzmem : z ∈ ((raisedAt u x a).piles a).faceUp := by
      exact lastOf_mem hcon
    have hzmemK : z ∈ ((raisedAt u x a).piles k).faceUp := by
      exact lastOf_mem (pileOfTop_top htop).2
    exact (mem_faceUp_unique hwf hzmem k hka).1 hzmemK
  rw [← htop]
  refine firstWhere_congr (fun a' => ?_) Anchor.all
  by_cases ha' : a' = a
  · subst a'
    rw [show u.topOf a = some x from htopU]
    rw [decide_false_of_not (fun h => hzx (Option.some.inj h).symm)]
    rw [decide_false_of_not htopR]
  · rw [show (raisedAt u x a).topOf a' = u.topOf a' from by
      simp [State.topOf, raisedAt_piles_ne u x a a' ha']]


/-! ### The empty-base slide commutes with the raise -/

theorem raisedAt_slidAt_inl_comm {u : State} {x y : Card} {a asrc c : Anchor}
    (hsrc : asrc ≠ a) (hca : c ≠ a) :
    raisedAt (slidAt u y (Sum.inl c) asrc) x a =
      slidAt (raisedAt u x a) y (Sum.inl c) asrc := by
  apply State.ext
  · simp [raisedAt, slidAt, putRun_found, setPile_found, State.setFound]
  · funext a'
    by_cases ha : a' = a
    · subst a'
      simp [raisedAt, slidAt, State.setPile, State.putRun, hsrc, hca, Ne.symm hsrc, Ne.symm hca]
    · by_cases hc : a' = c
      · subst a'
        simp [raisedAt, slidAt, State.setPile, State.putRun, hsrc, hca, Ne.symm hsrc, Ne.symm hca]
      · by_cases hs : a' = asrc
        · subst a'
          simp [raisedAt, slidAt, State.setPile, State.putRun, ha, hc, hsrc, hca, Ne.symm hsrc, Ne.symm hca]
        · simp [raisedAt, slidAt, State.setPile, State.putRun, ha, hc, hs]
  · rfl
  · rfl
  · rfl


theorem slidAt_piles_inl_of_ne (st : State) (y : Card) (c asrc a : Anchor)
    (hsrc : asrc ≠ a) (hca : c ≠ a) :
    (slidAt st y (Sum.inl c) asrc).piles a = st.piles a := by
  unfold slidAt
  rw [putRun_piles_inl_ne _ _ _ _ (Ne.symm hca)]
  exact setPile_piles_ne (Ne.symm hsrc)

theorem raise_tabToTab_inl_comm {u u1 u2 : State} {x y : Card} {a c : Anchor}
    (hwf : u.WF)
    (hpo : u.pileOfTop x = some a)
    (hraise : State.step u (Move.tabToFound x) = some u1)
    (hslide : State.step u1 (Move.tabToTab y (Sum.inl c)) = some u2)
    (hyx : y ≠ x) (hyt : y ≠ x.twin)
    (hsrc : u1.pileHolding y ≠ some a)
    (hca : c ≠ a) :
    ∃ u1', State.step u (Move.tabToTab y (Sum.inl c)) = some u1' ∧
      State.step u1' (Move.tabToFound x) = some u2 := by
  obtain ⟨hnext, a', hpo', hu1⟩ := step_tabToFound_inv hraise
  have ha' : a' = a := by
    have h := hpo'
    rw [hpo] at h
    exact (Option.some.inj h).symm
  subst a'
  have hu1' : u1 = raisedAt u x a := hu1
  subst u1
  obtain ⟨asrc, hhold1, hcp1, hrun1, hu2⟩ := step_tabToTab_inv hslide
  have hhold1R : (raisedAt u x a).pileHolding y = some asrc := hhold1
  have hcp1R : (raisedAt u x a).canPlace y (Sum.inl c) = true := hcp1
  have hsrcR : (raisedAt u x a).pileHolding y ≠ some a := hsrc
  have hasrc : asrc ≠ a := by
    intro h
    apply hsrcR
    rw [h] at hhold1R
    exact hhold1R
  have hwfR : (raisedAt u x a).WF := step_wf hwf hraise
  have hholdU : u.pileHolding y = some asrc := by
    apply (pileHolding_eq_some_iff hwf).mpr
    have hmem1 : y ∈ ((raisedAt u x a).piles asrc).faceUp := pileHolding_mem hhold1R
    rwa [raisedAt_piles_ne u x a asrc hasrc] at hmem1
  have hcpU : u.canPlace y (Sum.inl c) = true := by
    rw [canPlace_inl_unfold] at hcp1R ⊢
    rw [raisedAt_piles_ne u x a c hca] at hcp1R
    exact hcp1R
  have hstepU : State.step u (Move.tabToTab y (Sum.inl c)) =
      some (slidAt u y (Sum.inl c) asrc) :=
    step_tabToTab_some hholdU hcpU
  have hnextS : (slidAt u y (Sum.inl c) asrc).nextUp x = true := by
    rw [nextUp_congr_found (slidAt_found u y (Sum.inl c) asrc) x]
    exact hnext
  have hwfSlide : (slidAt u y (Sum.inl c) asrc).WF := step_wf hwf hstepU
  have htopS : (slidAt u y (Sum.inl c) asrc).pileOfTop x = some a := by
    apply (pileOfTop_eq_some_iff hwfSlide).mpr
    show ((slidAt u y (Sum.inl c) asrc).piles a).top = some x
    rw [slidAt_piles_inl_of_ne u y c asrc a hasrc hca]
    exact (pileOfTop_eq_some_iff hwf).mp hpo
  have hstepRaise : State.step (slidAt u y (Sum.inl c) asrc) (Move.tabToFound x) =
      some (raisedAt (slidAt u y (Sum.inl c) asrc) x a) :=
    step_tabToFound_raisedAt hnextS htopS
  refine ⟨slidAt u y (Sum.inl c) asrc, hstepU, ?_⟩
  rw [hstepRaise]
  congr 1
  rw [hu2]
  exact raisedAt_slidAt_inl_comm hasrc hca


theorem pileOfTop_raisedAt_other {u : State} {x z : Card} {a k : Anchor}
    (hwf : u.WF) (hwfR : (raisedAt u x a).WF)
    (hpo : u.pileOfTop x = some a)
    (htopU : u.pileOfTop z = some k) (hka : k ≠ a) :
    (raisedAt u x a).pileOfTop z = some k := by
  apply (pileOfTop_eq_some_iff hwfR).mpr
  show ((raisedAt u x a).piles k).top = some z
  rw [raisedAt_piles_ne u x a k hka]
  exact (pileOfTop_eq_some_iff hwf).mp htopU

theorem raisedAt_raisedAt_comm {u : State} {x y : Card} {a b : Anchor}
    (hxy : x ≠ y) (hsuit : y.suit ≠ x.suit) (hba : b ≠ a) :
    raisedAt (raisedAt u x a) y b = raisedAt (raisedAt u y b) x a := by
  apply State.ext
  · funext s
    by_cases hsx : s = x.suit
    · subst s
      simp [raisedAt, State.setFound, hsuit, Ne.symm hsuit]
    · by_cases hsy : s = y.suit
      · subst s
        simp [raisedAt, State.setFound, hsuit, Ne.symm hsuit]
      · simp [raisedAt, State.setFound, hsx, hsy]
  · funext a'
    by_cases haa : a' = a
    · subst a'
      simp [raisedAt, State.setPile, hba, Ne.symm hba]
    · by_cases hab : a' = b
      · subst a'
        simp [raisedAt, State.setPile, hba, Ne.symm hba]
      · simp [raisedAt, State.setPile, haa, hab]
  · rfl
  · rfl
  · rfl

theorem raise_raise_comm {u u1 u2 : State} {x y : Card} {a b : Anchor}
    (hwf : u.WF)
    (hpoX : u.pileOfTop x = some a)
    (hraiseX : State.step u (Move.tabToFound x) = some u1)
    (hraiseY : State.step u1 (Move.tabToFound y) = some u2)
    (hno : NotFoundPair x (Move.tabToFound y))
    (hsuit : y.suit ≠ x.suit)
    (hpoY : u.pileOfTop y = some b)
    (hba : b ≠ a) :
    ∃ u1', State.step u (Move.tabToFound y) = some u1' ∧
      State.step u1' (Move.tabToFound x) = some u2 := by
  have hyx : y ≠ x := fun h => hno.1 (by rw [h])
  have hyt : y ≠ x.twin := fun h => hno.2.1 (by rw [h])
  obtain ⟨hnextX, a', hpoX', hu1⟩ := step_tabToFound_inv hraiseX
  have ha' : a' = a := by
    have h := hpoX'
    rw [hpoX] at h
    exact (Option.some.inj h).symm
  subst a'
  have hu1' : u1 = raisedAt u x a := hu1
  subst u1
  obtain ⟨hnextY, b', hpoY', hu2⟩ := step_tabToFound_inv hraiseY
  have hnextYR : (raisedAt u x a).nextUp y = true := hnextY
  have hpoY'R : (raisedAt u x a).pileOfTop y = some b' := hpoY'
  have hwfR : (raisedAt u x a).WF := step_wf hwf hraiseX
  have hpoYR : (raisedAt u x a).pileOfTop y = some b :=
    pileOfTop_raisedAt_other (x := x) (z := y) (a := a) (k := b)
      hwf hwfR hpoX hpoY hba
  have hb' : b' = b := by
    rw [hpoYR] at hpoY'R
    exact (Option.some.inj hpoY'R).symm
  subst b'
  have hnextYU : u.nextUp y = true := by
    unfold State.nextUp State.foundHeight at hnextYR ⊢
    rwa [raisedAt_found_ne u x a y.suit hsuit] at hnextYR
  have htopYU : u.pileOfTop y = some b := hpoY
  have hstepYU : State.step u (Move.tabToFound y) = some (raisedAt u y b) :=
    step_tabToFound_raisedAt hnextYU htopYU
  have hwfY : (raisedAt u y b).WF := step_wf hwf hstepYU
  have hnextX' : (raisedAt u y b).nextUp x = true := by
    unfold State.nextUp State.foundHeight at hnextX ⊢
    rw [raisedAt_found_ne u y b x.suit (Ne.symm hsuit)]
    exact hnextX
  have htopXR : (raisedAt u y b).pileOfTop x = some a :=
    pileOfTop_raisedAt_other (x := y) (z := x) (a := b) (k := a)
      hwf hwfY hpoY hpoX (Ne.symm hba)
  have hstepXR : State.step (raisedAt u y b) (Move.tabToFound x) =
      some (raisedAt (raisedAt u y b) x a) :=
    step_tabToFound_raisedAt hnextX' htopXR
  refine ⟨raisedAt u y b, hstepYU, ?_⟩
  rw [hstepXR]
  congr 1
  rw [hu2]
  exact (raisedAt_raisedAt_comm (Ne.symm hyx) hsuit hba).symm


/-! ### Pull state -/

def pulledAt (st : State) (y : Card) (b : Base) : State :=
  (st.setFound y.suit (chop (st.found y.suit))).putCard y b

@[simp] theorem pulledAt_waste (st : State) (y : Card) (b : Base) :
    (pulledAt st y b).waste = st.waste := by
  simp [pulledAt, putCard_waste, setFound_waste]

@[simp] theorem pulledAt_found (st : State) (y : Card) (b : Base) (s : Suit) :
    (pulledAt st y b).found s =
      (if s = y.suit then chop (st.found y.suit) else st.found s) := by
  unfold pulledAt
  rw [putCard_found]
  simp [State.setFound]

theorem pulledAt_piles_inl_of_ne (st : State) (y : Card) (c a : Anchor) (hca : c ≠ a) :
    (pulledAt st y (Sum.inl c)).piles a = st.piles a := by
  unfold pulledAt
  rw [putCard_piles_inl]
  simp only []
  rw [ite_eq_right (Ne.symm hca), setFound_piles]

theorem raisedAt_pulledAt_inl_comm {u : State} {x y : Card} {a c : Anchor}
    (hsuit : y.suit ≠ x.suit) (hca : c ≠ a) :
    raisedAt (pulledAt u y (Sum.inl c)) x a =
      pulledAt (raisedAt u x a) y (Sum.inl c) := by
  apply State.ext
  · funext s
    by_cases hsx : s = x.suit
    · subst s
      simp [raisedAt, pulledAt, State.setFound, State.putCard, State.setPile,
        hsuit, Ne.symm hsuit, hca]
    · by_cases hsy : s = y.suit
      · subst s
        simp [raisedAt, pulledAt, State.setFound, State.putCard, State.setPile,
          hsuit, Ne.symm hsuit, hca]
      · simp [raisedAt, pulledAt, State.setFound, State.putCard, State.setPile,
          hsx, hsy]
  · funext a'
    by_cases haa : a' = a
    · subst a'
      simp [raisedAt, pulledAt, State.setFound, State.putCard, State.setPile,
        hca, Ne.symm hca]
    · by_cases hac : a' = c
      · subst a'
        simp [raisedAt, pulledAt, State.setFound, State.putCard, State.setPile,
          hca, Ne.symm hca]
      · simp [raisedAt, pulledAt, State.setFound, State.putCard, State.setPile,
          haa, hac]
  · rfl
  · rfl
  · rfl

theorem raise_foundToTab_inl_comm {u u1 u2 : State} {x y : Card} {a c : Anchor}
    (hwf : u.WF)
    (hpo : u.pileOfTop x = some a)
    (hraise : State.step u (Move.tabToFound x) = some u1)
    (hpull : State.step u1 (Move.foundToTab y (Sum.inl c)) = some u2)
    (hno : NotFoundPair x (Move.foundToTab y (Sum.inl c)))
    (hsuit : y.suit ≠ x.suit)
    (hca : c ≠ a) :
    ∃ u1', State.step u (Move.foundToTab y (Sum.inl c)) = some u1' ∧
      State.step u1' (Move.tabToFound x) = some u2 := by
  obtain ⟨hnext, a', hpo', hu1⟩ := step_tabToFound_inv hraise
  have ha' : a' = a := by
    have h := hpo'
    rw [hpo] at h
    exact (Option.some.inj h).symm
  subst a'
  have hu1' : u1 = raisedAt u x a := hu1
  subst u1
  obtain ⟨c', htop1, hc'c, hcp1, hu2⟩ := step_foundToTab_inv hpull
  subst c'
  have htop1R : (raisedAt u x a).foundTop y.suit = some y := htop1
  have hcp1R : (raisedAt u x a).canPlace y (Sum.inl c) = true := hcp1
  have htopU : u.foundTop y.suit = some y := by
    unfold State.foundTop at htop1R ⊢
    rwa [raisedAt_found_ne u x a y.suit hsuit] at htop1R
  have hcpU : u.canPlace y (Sum.inl c) = true := by
    rw [canPlace_inl_unfold] at hcp1R ⊢
    rw [raisedAt_piles_ne u x a c hca] at hcp1R
    exact hcp1R
  have hstepU : State.step u (Move.foundToTab y (Sum.inl c)) =
      some (pulledAt u y (Sum.inl c)) :=
    step_foundToTab_splice htopU hcpU
  have hnextPull : (pulledAt u y (Sum.inl c)).nextUp x = true := by
    unfold State.nextUp State.foundHeight at hnext ⊢
    rw [pulledAt_found]
    rw [ite_eq_right (Ne.symm hsuit)]
    exact hnext
  have hwfPull : (pulledAt u y (Sum.inl c)).WF := step_wf hwf hstepU
  have htopPull : (pulledAt u y (Sum.inl c)).pileOfTop x = some a := by
    apply (pileOfTop_eq_some_iff hwfPull).mpr
    show ((pulledAt u y (Sum.inl c)).piles a).top = some x
    rw [pulledAt_piles_inl_of_ne u y c a hca]
    exact (pileOfTop_eq_some_iff hwf).mp hpo
  have hstepRaise : State.step (pulledAt u y (Sum.inl c)) (Move.tabToFound x) =
      some (raisedAt (pulledAt u y (Sum.inl c)) x a) :=
    step_tabToFound_raisedAt hnextPull htopPull
  refine ⟨pulledAt u y (Sum.inl c), hstepU, ?_⟩
  rw [hstepRaise]
  congr 1
  rw [hu2]
  exact raisedAt_pulledAt_inl_comm hsuit hca


theorem pulledAt_raisedAt_inl_comm {u : State} {x y : Card} {b c : Anchor}
    (hsuit : y.suit ≠ x.suit) (hcb : c ≠ b) :
    pulledAt (raisedAt u y b) x (Sum.inl c) =
      raisedAt (pulledAt u x (Sum.inl c)) y b := by
  apply State.ext
  · funext s
    by_cases hsx : s = x.suit
    · subst s
      simp [raisedAt, pulledAt, State.setFound, State.putCard, State.setPile,
        hsuit, Ne.symm hsuit, hcb]
    · by_cases hsy : s = y.suit
      · subst s
        simp [raisedAt, pulledAt, State.setFound, State.putCard, State.setPile,
          hsuit, Ne.symm hsuit, hcb]
      · simp [raisedAt, pulledAt, State.setFound, State.putCard, State.setPile,
          hsx, hsy]
  · funext a'
    by_cases hab : a' = b
    · subst a'
      simp [raisedAt, pulledAt, State.setFound, State.putCard, State.setPile,
        hcb, Ne.symm hcb]
    · by_cases hac : a' = c
      · subst a'
        simp [raisedAt, pulledAt, State.setFound, State.putCard, State.setPile,
          hcb, Ne.symm hcb]
      · simp [raisedAt, pulledAt, State.setFound, State.putCard, State.setPile,
          hab, hac]
  · rfl
  · rfl
  · rfl

theorem pull_tabToFound_comm {u u1 u2 : State} {x y : Card} {c bsrc : Anchor}
    (hwf : u.WF)
    (hpull : State.step u (Move.foundToTab x (Sum.inl c)) = some u1)
    (hraise : State.step u1 (Move.tabToFound y) = some u2)
    (hno : NotFoundPair x (Move.tabToFound y))
    (hsuit : y.suit ≠ x.suit)
    (htopY : u.pileOfTop y = some bsrc)
    (hcb : c ≠ bsrc) :
    ∃ u1', State.step u (Move.tabToFound y) = some u1' ∧
      State.step u1' (Move.foundToTab x (Sum.inl c)) = some u2 := by
  obtain ⟨c', hxTop, hc'x, hcpX, hu1⟩ := step_foundToTab_inv hpull
  subst c'
  have hpullEq : u1 = pulledAt u x (Sum.inl c) := hu1
  subst u1
  obtain ⟨hnextY, b', htopY', hu2⟩ := step_tabToFound_inv hraise
  have hnextYR : (pulledAt u x (Sum.inl c)).nextUp y = true := hnextY
  have htopY'R : (pulledAt u x (Sum.inl c)).pileOfTop y = some b' := htopY'
  have hwfP : (pulledAt u x (Sum.inl c)).WF := step_wf hwf hpull
  have htopY_P : (pulledAt u x (Sum.inl c)).pileOfTop y = some bsrc := by
    apply (pileOfTop_eq_some_iff hwfP).mpr
    show ((pulledAt u x (Sum.inl c)).piles bsrc).top = some y
    rw [pulledAt_piles_inl_of_ne u x c bsrc hcb]
    exact (pileOfTop_eq_some_iff hwf).mp htopY
  have hb' : b' = bsrc := by
    rw [htopY_P] at htopY'R
    exact (Option.some.inj htopY'R).symm
  subst b'
  have hnextY_U : u.nextUp y = true := by
    unfold State.nextUp State.foundHeight at hnextYR ⊢
    rw [pulledAt_found] at hnextYR
    rwa [ite_eq_right hsuit] at hnextYR
  have hstepYU : State.step u (Move.tabToFound y) = some (raisedAt u y bsrc) :=
    step_tabToFound_raisedAt hnextY_U htopY
  have htopXR : (raisedAt u y bsrc).foundTop x.suit = some x := by
    unfold State.foundTop at hxTop ⊢
    rw [raisedAt_found_ne u y bsrc x.suit (Ne.symm hsuit)]
    exact hxTop
  have hcpXR : (raisedAt u y bsrc).canPlace x (Sum.inl c) = true := by
    rw [canPlace_inl_unfold] at hcpX ⊢
    rw [raisedAt_piles_ne u y bsrc c hcb]
    exact hcpX
  have hstepPull : State.step (raisedAt u y bsrc) (Move.foundToTab x (Sum.inl c)) =
      some (pulledAt (raisedAt u y bsrc) x (Sum.inl c)) :=
    step_foundToTab_splice htopXR hcpXR
  refine ⟨raisedAt u y bsrc, hstepYU, ?_⟩
  rw [hstepPull]
  congr 1
  rw [hu2]
  exact pulledAt_raisedAt_inl_comm hsuit hcb


theorem pulledAt_slidAt_inl_comm {u : State} {x y : Card} {c asrc e : Anchor}
    (hsrc : asrc ≠ c) (hec : e ≠ c) :
    pulledAt (slidAt u y (Sum.inl e) asrc) x (Sum.inl c) =
      slidAt (pulledAt u x (Sum.inl c)) y (Sum.inl e) asrc := by
  apply State.ext
  · funext s
    by_cases hsx : s = x.suit
    · subst s
      simp [raisedAt, pulledAt, slidAt, State.setFound, State.putCard, State.setPile,
        State.putRun, hsrc, hec, Ne.symm hsrc, Ne.symm hec]
    · simp [raisedAt, pulledAt, slidAt, State.setFound, State.putCard, State.setPile,
        State.putRun, hsx]
  · funext a'
    by_cases haa : a' = c
    · subst a'
      simp [raisedAt, pulledAt, slidAt, State.setFound, State.putCard, State.setPile,
        State.putRun, hsrc, hec, Ne.symm hsrc, Ne.symm hec]
    · by_cases hasrc : a' = asrc
      · subst a'
        simp [raisedAt, pulledAt, slidAt, State.setFound, State.putCard, State.setPile,
          State.putRun, hsrc, hec, Ne.symm hsrc, Ne.symm hec]
      · by_cases he : a' = e
        · subst a'
          simp [raisedAt, pulledAt, slidAt, State.setFound, State.putCard, State.setPile,
            State.putRun, hsrc, hec, Ne.symm hsrc, Ne.symm hec]
        · simp [raisedAt, pulledAt, slidAt, State.setFound, State.putCard, State.setPile,
            State.putRun, haa, hasrc, he, hsrc, hec, Ne.symm hsrc, Ne.symm hec]
  · rfl
  · rfl
  · rfl

theorem pull_tabToTab_inl_comm {u u1 u2 : State} {x y : Card} {c asrc e : Anchor}
    (hwf : u.WF)
    (hpull : State.step u (Move.foundToTab x (Sum.inl c)) = some u1)
    (hslide : State.step u1 (Move.tabToTab y (Sum.inl e)) = some u2)
    (hyx : y ≠ x) (hyt : y ≠ x.twin)
    (hsrc : u1.pileHolding y ≠ some c)
    (hec : e ≠ c) :
    ∃ u1', State.step u (Move.tabToTab y (Sum.inl e)) = some u1' ∧
      State.step u1' (Move.foundToTab x (Sum.inl c)) = some u2 := by
  obtain ⟨c', hxTop, hc'x, hcpX, hu1⟩ := step_foundToTab_inv hpull
  subst c'
  have hpullEq : u1 = pulledAt u x (Sum.inl c) := hu1
  subst u1
  obtain ⟨asrc', hhold1, hcp1, hrun1, hu2⟩ := step_tabToTab_inv hslide
  have hhold1R : (pulledAt u x (Sum.inl c)).pileHolding y = some asrc' := hhold1
  have hcp1R : (pulledAt u x (Sum.inl c)).canPlace y (Sum.inl e) = true := hcp1
  have hsrcR : (pulledAt u x (Sum.inl c)).pileHolding y ≠ some c := hsrc
  have hasrc : asrc' ≠ c := by
    intro h
    apply hsrcR
    rw [h] at hhold1R
    exact hhold1R
  have hholdU : u.pileHolding y = some asrc' := by
    apply (pileHolding_eq_some_iff hwf).mpr
    have hmem1 : y ∈ ((pulledAt u x (Sum.inl c)).piles asrc').faceUp :=
      pileHolding_mem hhold1R
    rwa [pulledAt_piles_inl_of_ne u x c asrc' (Ne.symm hasrc)] at hmem1
  have hcpU : u.canPlace y (Sum.inl e) = true := by
    rw [canPlace_inl_unfold] at hcp1R ⊢
    rw [pulledAt_piles_inl_of_ne u x c e (Ne.symm hec)] at hcp1R
    exact hcp1R
  have hstepU : State.step u (Move.tabToTab y (Sum.inl e)) =
      some (slidAt u y (Sum.inl e) asrc') :=
    step_tabToTab_some hholdU hcpU
  have hwfS : (slidAt u y (Sum.inl e) asrc').WF := step_wf hwf hstepU
  have hxTopS : (slidAt u y (Sum.inl e) asrc').foundTop x.suit = some x := by
    unfold State.foundTop at hxTop ⊢
    rw [slidAt_found]
    exact hxTop
  have hcpXS : (slidAt u y (Sum.inl e) asrc').canPlace x (Sum.inl c) = true := by
    rw [canPlace_inl_unfold] at hcpX ⊢
    rw [slidAt_piles_inl_of_ne u y e asrc' c hasrc hec]
    exact hcpX
  have hstepPull : State.step (slidAt u y (Sum.inl e) asrc')
      (Move.foundToTab x (Sum.inl c)) =
      some (pulledAt (slidAt u y (Sum.inl e) asrc') x (Sum.inl c)) :=
    step_foundToTab_splice hxTopS hcpXS
  refine ⟨slidAt u y (Sum.inl e) asrc', hstepU, ?_⟩
  rw [hstepPull]
  congr 1
  rw [hu2]
  exact pulledAt_slidAt_inl_comm hasrc hec


/-! ### Failure: a same-suit raise chain is not confluent -/

theorem tabToFound_tabToFound_sameSuit_disabled
    {u u1 u2 : State} {x y : Card}
    (hraiseX : State.step u (Move.tabToFound x) = some u1)
    (hraiseY : State.step u1 (Move.tabToFound y) = some u2)
    (hneq : y ≠ x) (hsuit : y.suit = x.suit) :
    State.step u (Move.tabToFound y) = none := by
  obtain ⟨hnextX, a, hpoX, hu1⟩ := step_tabToFound_inv hraiseX
  obtain ⟨hnextY, b, hpoY, hu2⟩ := step_tabToFound_inv hraiseY
  have hu1' : u1 = raisedAt u x a := hu1
  have hnextYR : (raisedAt u x a).nextUp y = true := by
    rwa [hu1'] at hnextY
  unfold State.nextUp State.foundHeight at hnextX hnextYR
  have hxidx : x.rank.toIdx = (u.found x.suit).length := of_decide_eq_true hnextX
  have hyidx : y.rank.toIdx = ((raisedAt u x a).found y.suit).length :=
    of_decide_eq_true hnextYR
  rw [hsuit, raisedAt_found_self] at hyidx
  simp only [List.length_append, List.length_singleton] at hyidx
  have hnextFalse : u.nextUp y = false := by
    unfold State.nextUp State.foundHeight
    apply decide_false_of_not
    intro hcon
    rw [hsuit] at hcon
    omega
  simp [State.step, hnextFalse]

theorem wasteToFound_sameSuit_disabled
    {u u1 u2 : State} {x y : Card}
    (hraiseX : State.step u (Move.tabToFound x) = some u1)
    (hwaste : State.step u1 (Move.wasteToFound y) = some u2)
    (hneq : y ≠ x) (hsuit : y.suit = x.suit) :
    State.step u (Move.wasteToFound y) = none := by
  obtain ⟨hnextX, a, hpoX, hu1⟩ := step_tabToFound_inv hraiseX
  obtain ⟨hguard, c, cs, hw, hu2⟩ := step_wasteToFound_inv hwaste
  rw [Bool.and_eq_true] at hguard
  obtain ⟨-, hnextY⟩ := hguard
  have hu1' : u1 = raisedAt u x a := hu1
  have hnextYR : (raisedAt u x a).nextUp y = true := by
    rwa [hu1'] at hnextY
  unfold State.nextUp State.foundHeight at hnextX hnextYR
  have hxidx : x.rank.toIdx = (u.found x.suit).length := of_decide_eq_true hnextX
  have hyidx : y.rank.toIdx = ((raisedAt u x a).found y.suit).length :=
    of_decide_eq_true hnextYR
  rw [hsuit, raisedAt_found_self] at hyidx
  simp only [List.length_append, List.length_singleton] at hyidx
  have hnextFalse : u.nextUp y = false := by
    unfold State.nextUp State.foundHeight
    apply decide_false_of_not
    intro hcon
    rw [hsuit] at hcon
    omega
  simp [State.step, hnextFalse]


theorem tabToTab_into_raise_source_disabled
    {u : State} {x y : Card} {a : Anchor}
    (hpo : u.pileOfTop x = some a) :
    State.step u (Move.tabToTab y (Sum.inl a)) = none := by
  have hmem : x ∈ (u.piles a).faceUp := lastOf_mem (pileOfTop_top hpo).2
  have hnotempty : (u.piles a).isEmpty = false := Pile.isEmpty_eq_false_of_mem hmem
  have hcp : u.canPlace y (Sum.inl a) = false := by
    rw [canPlace_inl_unfold, hnotempty]
    rfl
  cases h : u.pileHolding y <;> simp [State.step, hcp, h]

theorem tabToTab_into_exposed_target_disabled
    {u : State} {y z : Card} :
    u.pileOfTop z = none → State.step u (Move.tabToTab y (Sum.inr z)) = none := by
  intro hz
  have hcp : u.canPlace y (Sum.inr z) = false := by
    show (match u.pileOfTop z with
      | some _ => canSitOn y z
      | none => false) = false
    rw [hz]
  cases h : u.pileHolding y <;> simp [State.step, hcp, h]


/-! ### Waste-to-foundation commutations -/

def wasteFoundAt (st : State) (c : Card) (cs : List Card) : State :=
  { st.setFound c.suit (st.found c.suit ++ [c]) with waste := cs }

theorem step_wasteToFound_splice {st : State} {c : Card} {cs : List Card}
    (hw : st.waste = c :: cs) (hwis : st.wasteIs c = true)
    (hnext : st.nextUp c = true) :
    State.step st (Move.wasteToFound c) = some (wasteFoundAt st c cs) := by
  simp [State.step, wasteFoundAt, hw, hwis, hnext]

theorem raisedAt_wasteFoundAt_comm {u : State} {x y : Card} {a : Anchor} {cs : List Card}
    (hsuit : y.suit ≠ x.suit) :
    raisedAt (wasteFoundAt u y cs) x a = wasteFoundAt (raisedAt u x a) y cs := by
  apply State.ext
  · funext s
    by_cases hsx : s = x.suit
    · subst s
      simp [raisedAt, wasteFoundAt, State.setFound, hsuit, Ne.symm hsuit]
    · by_cases hsy : s = y.suit
      · subst s
        simp [raisedAt, wasteFoundAt, State.setFound, hsuit, Ne.symm hsuit]
      · simp [raisedAt, wasteFoundAt, State.setFound, hsx, hsy]
  · funext a'
    simp [raisedAt, wasteFoundAt, State.setFound]
  · rfl
  · rfl
  · rfl

theorem raise_wasteToFound_comm {u u1 u2 : State} {x y : Card} {a : Anchor}
    (hwf : u.WF)
    (hpo : u.pileOfTop x = some a)
    (hraise : State.step u (Move.tabToFound x) = some u1)
    (hwaste : State.step u1 (Move.wasteToFound y) = some u2)
    (hno : NotFoundPair x (Move.wasteToFound y))
    (hsuit : y.suit ≠ x.suit) :
    ∃ u1', State.step u (Move.wasteToFound y) = some u1' ∧
      State.step u1' (Move.tabToFound x) = some u2 := by
  obtain ⟨hnextX, a', hpoX, hu1⟩ := step_tabToFound_inv hraise
  have ha' : a' = a := by
    have h := hpoX
    rw [hpo] at h
    exact (Option.some.inj h).symm
  subst a'
  have hu1' : u1 = raisedAt u x a := hu1
  subst u1
  obtain ⟨hguard, c, cs, hwaste1, hu2⟩ := step_wasteToFound_inv hwaste
  rw [Bool.and_eq_true] at hguard
  obtain ⟨hwis1, hnext1⟩ := hguard
  have hwaste1R : (raisedAt u x a).waste = c :: cs := hwaste1
  have hwis1R : (raisedAt u x a).wasteIs y = true := hwis1
  have hnext1R : (raisedAt u x a).nextUp y = true := hnext1
  have hcy : c = y := by
    rw [State.wasteIs_cons hwaste1R y] at hwis1R
    exact of_decide_eq_true hwis1R
  have hwasteU : u.waste = y :: cs := by
    rw [raisedAt_waste u x a] at hwaste1R
    rwa [hcy] at hwaste1R
  have hwisU : u.wasteIs y = true := by
    unfold State.wasteIs at hwis1R ⊢
    rwa [raisedAt_waste u x a] at hwis1R
  have hnextU : u.nextUp y = true := by
    unfold State.nextUp State.foundHeight at hnext1R ⊢
    rwa [raisedAt_found_ne u x a y.suit hsuit] at hnext1R
  have hstepU : State.step u (Move.wasteToFound y) = some (wasteFoundAt u y cs) :=
    step_wasteToFound_splice hwasteU hwisU hnextU
  have hnextX' : (wasteFoundAt u y cs).nextUp x = true := by
    unfold State.nextUp State.foundHeight at hnextX ⊢
    rw [show (wasteFoundAt u y cs).found x.suit = u.found x.suit from by
      simp [wasteFoundAt, State.setFound, hsuit, Ne.symm hsuit]]
    exact hnextX
  have htopX' : (wasteFoundAt u y cs).pileOfTop x = some a := by
    apply (pileOfTop_eq_some_iff (step_wf hwf hstepU)).mpr
    show ((wasteFoundAt u y cs).piles a).top = some x
    rw [show (wasteFoundAt u y cs).piles a = u.piles a from rfl]
    exact (pileOfTop_eq_some_iff hwf).mp hpo
  have hstepX : State.step (wasteFoundAt u y cs) (Move.tabToFound x) =
      some (raisedAt (wasteFoundAt u y cs) x a) :=
    step_tabToFound_raisedAt hnextX' htopX'
  refine ⟨wasteFoundAt u y cs, hstepU, ?_⟩
  rw [hstepX]
  congr 1
  rw [hu2]
  exact raisedAt_wasteFoundAt_comm hsuit


theorem pulledAt_wasteFoundAt_comm {u : State} {x y : Card} {c : Anchor} {cs : List Card}
    (hsuit : y.suit ≠ x.suit) :
    pulledAt (wasteFoundAt u y cs) x (Sum.inl c) =
      wasteFoundAt (pulledAt u x (Sum.inl c)) y cs := by
  apply State.ext
  · funext s
    by_cases hsx : s = x.suit
    · subst s
      simp [pulledAt, wasteFoundAt, State.setFound, State.putCard, State.setPile,
        hsuit, Ne.symm hsuit]
    · by_cases hsy : s = y.suit
      · subst s
        simp [pulledAt, wasteFoundAt, State.setFound, State.putCard, State.setPile,
          hsuit, Ne.symm hsuit]
      · simp [pulledAt, wasteFoundAt, State.setFound, State.putCard, State.setPile,
          hsx, hsy]
  · funext a'
    by_cases hac : a' = c
    · subst a'
      simp [pulledAt, wasteFoundAt, State.setFound, State.putCard, State.setPile]
    · simp [pulledAt, wasteFoundAt, State.setFound, State.putCard, State.setPile,
        hac]
  · rfl
  · rfl
  · rfl

theorem pull_wasteToFound_comm {u u1 u2 : State} {x y : Card} {c : Anchor}
    (hwf : u.WF)
    (hpull : State.step u (Move.foundToTab x (Sum.inl c)) = some u1)
    (hwaste : State.step u1 (Move.wasteToFound y) = some u2)
    (hno : NotFoundPair x (Move.wasteToFound y))
    (hsuit : y.suit ≠ x.suit) :
    ∃ u1', State.step u (Move.wasteToFound y) = some u1' ∧
      State.step u1' (Move.foundToTab x (Sum.inl c)) = some u2 := by
  obtain ⟨c', hxTop, hc'x, hcpX, hu1⟩ := step_foundToTab_inv hpull
  subst c'
  have hu1' : u1 = pulledAt u x (Sum.inl c) := hu1
  subst u1
  obtain ⟨hguard, c0, cs, hwaste1, hu2⟩ := step_wasteToFound_inv hwaste
  rw [Bool.and_eq_true] at hguard
  obtain ⟨hwis1, hnext1⟩ := hguard
  have hwaste1R : (pulledAt u x (Sum.inl c)).waste = c0 :: cs := hwaste1
  have hwis1R : (pulledAt u x (Sum.inl c)).wasteIs y = true := hwis1
  have hnext1R : (pulledAt u x (Sum.inl c)).nextUp y = true := hnext1
  have hcy : c0 = y := by
    rw [State.wasteIs_cons hwaste1R y] at hwis1R
    exact of_decide_eq_true hwis1R
  have hwasteU : u.waste = y :: cs := by
    rw [pulledAt_waste] at hwaste1R
    rw [hcy] at hwaste1R
    exact hwaste1R
  have hwisU : u.wasteIs y = true := by
    unfold State.wasteIs at hwis1R ⊢
    rwa [pulledAt_waste] at hwis1R
  have hnextU : u.nextUp y = true := by
    unfold State.nextUp State.foundHeight at hnext1R ⊢
    simpa [pulledAt_found, hsuit] using hnext1R
  have hstepU : State.step u (Move.wasteToFound y) = some (wasteFoundAt u y cs) :=
    step_wasteToFound_splice hwasteU hwisU hnextU
  have hxTopW : (wasteFoundAt u y cs).foundTop x.suit = some x := by
    unfold State.foundTop at hxTop ⊢
    rw [show (wasteFoundAt u y cs).found x.suit = u.found x.suit from by
      simp [wasteFoundAt, State.setFound, hsuit, Ne.symm hsuit]]
    exact hxTop
  have hcpXW : (wasteFoundAt u y cs).canPlace x (Sum.inl c) = true := by
    rw [canPlace_inl_unfold] at hcpX ⊢
    rw [show (wasteFoundAt u y cs).piles c = u.piles c from by
      simp [wasteFoundAt, State.setFound]]
    exact hcpX
  have hstepPull : State.step (wasteFoundAt u y cs) (Move.foundToTab x (Sum.inl c)) =
      some (pulledAt (wasteFoundAt u y cs) x (Sum.inl c)) :=
    step_foundToTab_splice hxTopW hcpXW
  refine ⟨wasteFoundAt u y cs, hstepU, ?_⟩
  rw [hstepPull]
  congr 1
  rw [hu2]
  exact pulledAt_wasteFoundAt_comm hsuit


end TwinRaiseCommute
/-! ## Audit -/

#print axioms TwinRaiseCommute.raisedAt_found_self
#print axioms TwinRaiseCommute.raisedAt_found_ne
#print axioms TwinRaiseCommute.raisedAt_piles_self
#print axioms TwinRaiseCommute.raisedAt_piles_ne
#print axioms TwinRaiseCommute.raisedAt_stock
#print axioms TwinRaiseCommute.raisedAt_waste
#print axioms TwinRaiseCommute.raisedAt_drawStep
#print axioms TwinRaiseCommute.step_tabToFound_raisedAt
#print axioms TwinRaiseCommute.slidAt_found
#print axioms TwinRaiseCommute.slidAt_stock
#print axioms TwinRaiseCommute.slidAt_waste
#print axioms TwinRaiseCommute.slidAt_drawStep
#print axioms TwinRaiseCommute.fromCard_ne_nil_of_mem
#print axioms TwinRaiseCommute.step_tabToTab_some
#print axioms TwinRaiseCommute.nextUp_congr_found
#print axioms TwinRaiseCommute.pileOfTop_congr_piles
#print axioms TwinRaiseCommute.pileOfTop_raisedAt_ne
#print axioms TwinRaiseCommute.raisedAt_slidAt_inl_comm
#print axioms TwinRaiseCommute.slidAt_piles_inl_of_ne
#print axioms TwinRaiseCommute.raise_tabToTab_inl_comm
#print axioms TwinRaiseCommute.pileOfTop_raisedAt_other
#print axioms TwinRaiseCommute.raisedAt_raisedAt_comm
#print axioms TwinRaiseCommute.raise_raise_comm
#print axioms TwinRaiseCommute.pulledAt_waste
#print axioms TwinRaiseCommute.pulledAt_found
#print axioms TwinRaiseCommute.pulledAt_piles_inl_of_ne
#print axioms TwinRaiseCommute.raisedAt_pulledAt_inl_comm
#print axioms TwinRaiseCommute.raise_foundToTab_inl_comm
#print axioms TwinRaiseCommute.pulledAt_raisedAt_inl_comm
#print axioms TwinRaiseCommute.pull_tabToFound_comm
#print axioms TwinRaiseCommute.pulledAt_slidAt_inl_comm
#print axioms TwinRaiseCommute.pull_tabToTab_inl_comm
#print axioms TwinRaiseCommute.tabToFound_tabToFound_sameSuit_disabled
#print axioms TwinRaiseCommute.wasteToFound_sameSuit_disabled
#print axioms TwinRaiseCommute.tabToTab_into_raise_source_disabled
#print axioms TwinRaiseCommute.tabToTab_into_exposed_target_disabled
#print axioms TwinRaiseCommute.step_wasteToFound_splice
#print axioms TwinRaiseCommute.raisedAt_wasteFoundAt_comm
#print axioms TwinRaiseCommute.raise_wasteToFound_comm
#print axioms TwinRaiseCommute.pulledAt_wasteFoundAt_comm
#print axioms TwinRaiseCommute.pull_wasteToFound_comm
