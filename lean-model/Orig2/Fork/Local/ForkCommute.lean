import Orig2.Fork.Local.ForkCriticalPair
import Orig2.Fiber.AnchorRelabel

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-!
# Orig2/ForkCommute — the local commutation squares (source card)

Self-contained promotion of the proven scratch kit: the pull/pull,
raise/raise, pull/raise, raise/pull and draw squares, the slide-free
diamond, and the adjacent-swap corollary.  No `sorry`, no
`Classical.choice`, no `native_decide`.
-/

namespace CommuteStep

-- ===== from Temp/Commute_Step_Kit.lean =====


/-! ## 0. WF uniqueness of pile tops -/

/-- Two piles of a `WF` state cannot share a top card. -/
theorem top_unique {st : State} (hwf : st.WF) {z : Card} {a a' : Anchor}
    (h : (st.piles a).top = some z) (h' : (st.piles a').top = some z) : a = a' := by
  by_cases hne : a = a'
  · exact hne
  · exfalso
    exact (mem_faceUp_unique hwf (Pile.mem_of_top h) a' (fun hc => hne hc.symm)).1
      (Pile.mem_of_top h')

theorem not_top_of_found {st : State} (hwf : st.WF) {c : Card}
    (h : c ∈ st.found c.suit) : ∀ a, (st.piles a).top ≠ some c := by
  intro a ht
  exact ((mem_found_unique hwf h).1 a).2 (Pile.mem_of_top ht)

/-! ## 1. The target-pile map of a base -/

/-- The pile a `Base` writes at state `u`. -/
def tgt (u : State) (b : Base) : Option Anchor :=
  match b with
  | .inl a => some a
  | .inr z => u.pileOfTop z

@[simp] theorem tgt_inr (u : State) (z : Card) : tgt u (.inr z) = u.pileOfTop z := rfl

theorem putCard_piles_at {u : State} {c : Card} {b : Base} {k : Anchor}
    (hk : tgt u b = some k) :
    (u.putCard c b).piles =
      (fun a' => if a' = k then
        (match b with
          | .inl _ => Pile.mk [] [c]
          | .inr _ => { u.piles k with faceUp := (u.piles k).faceUp ++ [c] })
        else u.piles a') := by
  cases b with
  | inl a =>
      have hka : k = a :=
        (Option.some.inj (show (some a : Option Anchor) = some k from hk)).symm
      subst hka
      rw [putCard_piles_inl]
  | inr z =>
      have hz : u.pileOfTop z = some k := hk
      rw [putCard_piles_inr _ _ _ _ hz]

/-- The top of the pile `putCard` writes is the placed card. -/
theorem putCard_top_written {u : State} {c : Card} {b : Base} {k : Anchor}
    (hk : tgt u b = some k) : ((u.putCard c b).piles k).top = some c := by
  cases b with
  | inl a =>
      have hka : k = a :=
        (Option.some.inj (show (some a : Option Anchor) = some k from hk)).symm
      rw [hka]
      show lastOf ((u.putCard c (Sum.inl a)).piles a).faceUp = some c
      rw [putCard_piles_inl]
      dsimp only
      rw [ite_eq_left rfl]
      rfl
  | inr z =>
      have hz : u.pileOfTop z = some k := hk
      show lastOf ((u.putCard c (Sum.inr z)).piles k).faceUp = some c
      rw [putCard_piles_inr _ _ _ _ hz]
      simp [lastOf_snoc]

/-- `putCard` only writes its target pile. -/
theorem putCard_piles_ne {u : State} {c : Card} {b : Base} {k a : Anchor}
    (hk : tgt u b = some k) (hne : a ≠ k) :
    (u.putCard c b).piles a = u.piles a := by
  rw [putCard_piles_at hk]
  exact ite_eq_right hne

/-! ## 2. The canonical pull successor -/

/-- The canonical `.foundToTab` successor at a legal pull. -/
def pullSt (u : State) (c : Card) (b : Base) : State :=
  (u.setFound c.suit (chop (u.found c.suit))).putCard c b

/-- The pull normal form: place first, then chop the foundation. -/
theorem pullSt_eq (u : State) (c : Card) (b : Base) :
    pullSt u c b = (u.putCard c b).setFound c.suit (chop (u.found c.suit)) :=
  State.setFound_putCard u c.suit (chop (u.found c.suit)) c b

theorem pullSt_found_apply (u : State) (c : Card) (b : Base) (s : Suit) :
    (pullSt u c b).found s =
      if s = c.suit then chop (u.found c.suit) else u.found s := by
  rw [pullSt_eq]
  by_cases h : s = c.suit
  · rw [ite_eq_left h, h]; exact setFound_found_self
  · rw [ite_eq_right h, setFound_found_ne h, putCard_found]

theorem pullSt_piles (u : State) (c : Card) (b : Base) :
    (pullSt u c b).piles = (u.putCard c b).piles := by
  rw [pullSt_eq, setFound_piles]

theorem pullSt_stock (u : State) (c : Card) (b : Base) :
    (pullSt u c b).stock = u.stock := by
  rw [pullSt_eq, setFound_stock, putCard_stock]

theorem pullSt_waste (u : State) (c : Card) (b : Base) :
    (pullSt u c b).waste = u.waste := by
  rw [pullSt_eq, setFound_waste, putCard_waste]

theorem pullSt_drawStep (u : State) (c : Card) (b : Base) :
    (pullSt u c b).drawStep = u.drawStep := by
  rw [pullSt_eq, setFound_drawStep, putCard_drawStep]

theorem pullSt_piles_ne {u : State} {c : Card} {b : Base} {k a : Anchor}
    (hk : tgt u b = some k) (hne : a ≠ k) :
    (pullSt u c b).piles a = u.piles a := by
  rw [pullSt_piles, putCard_piles_ne hk hne]

/-- The pull's piles at an empty-seat base, pointwise. -/
theorem pullSt_piles_inl_apply (u : State) (c : Card) (a1 a : Anchor) :
    (pullSt u c (.inl a1)).piles a =
      if a = a1 then Pile.mk [] [c] else u.piles a := by
  rw [pullSt_piles, putCard_piles_inl]

/-- The pull's piles at a card base, pointwise. -/
theorem pullSt_piles_inr_apply (u : State) (c : Card) (z : Card) (k : Anchor)
    (hz : u.pileOfTop z = some k) (a : Anchor) :
    (pullSt u c (.inr z)).piles a =
      if a = k then
        { u.piles k with faceUp := (u.piles k).faceUp ++ [c] }
      else u.piles a := by
  rw [pullSt_piles, putCard_piles_inr _ _ _ _ hz]

/-- The pull's target-pile top is the pulled card. -/
theorem pullSt_top_written {u : State} {c : Card} {b : Base} {k : Anchor}
    (hk : tgt u b = some k) : ((pullSt u c b).piles k).top = some c := by
  rw [pullSt_piles]
  exact putCard_top_written hk

/-! ## 3. The pull's step shape -/

/-- A legal `.foundToTab` lands on `pullSt`. -/
theorem step_foundToTab_pullSt {u s : State} {c : Card} {b : Base}
    (hs : State.step u (Move.foundToTab c b) = some s) :
    ∃ c', u.foundTop c.suit = some c' ∧ c' = c ∧ u.canPlace c b = true ∧
      s = pullSt u c b := by
  obtain ⟨c', htop, hc, hcp, hs'⟩ := step_foundToTab_inv hs
  exact ⟨c', htop, hc, hcp, by rw [hs']; rfl⟩

/-- The pull's target is located at a legal pull. -/
theorem exists_tgt_of_canPlace {u : State} {c : Card} {b : Base}
    (h : u.canPlace c b = true) : ∃ k, tgt u b = some k := by
  cases b with
  | inl a => exact ⟨a, rfl⟩
  | inr z =>
      obtain ⟨k, hk, -⟩ := canPlace_inr h
      exact ⟨k, hk⟩


-- ===== from Temp/Commute_Step_Pull.lean =====


/-! ## 1. Search stability under a pull -/

/-- A pull at `u` leaves every other base's target alone. -/
theorem tgt_pull_stable {u : State} (hwf : u.WF) {c : Card} {b b' : Base}
    {k1 : Anchor} (htop : u.foundTop c.suit = some c) (hcp : u.canPlace c b = true)
    (hk1 : tgt u b = some k1) {k : Anchor} (hk : tgt u b' = some k) (hne : k ≠ k1) :
    tgt (pullSt u c b) b' = some k := by
  cases b' with
  | inl a =>
      have hak : a = k := Option.some.inj (show (some a : Option Anchor) = some k from hk)
      show some a = some k
      rw [hak]
  | inr z =>
      show (pullSt u c b).pileOfTop z = some k
      have hs : State.step u (Move.foundToTab c b) = some (pullSt u c b) := by
        rw [step_foundToTab_splice htop hcp]; rfl
      have hwfS : (pullSt u c b).WF := step_wf hwf hs
      have htopk : ((pullSt u c b).piles k).top = some z := by
        rw [pullSt_piles_ne hk1 hne]
        exact (pileOfTop_eq_some_iff hwf).mp hk
      exact (pileOfTop_eq_some_iff hwfS).mpr htopk

/-! ## 2. The two targets differ -/

/-- Two pulls cannot share a target pile when the second is legal after
the first. -/
theorem pull_pull_tgt_ne {u s1 s12 : State} (hwf : u.WF) {c1 c2 : Card} {b1 b2 : Base}
    {k1 k2 : Anchor}
    (htop1 : u.foundTop c1.suit = some c1) (hcp1 : u.canPlace c1 b1 = true)
    (hk1 : tgt u b1 = some k1) (hk2 : tgt u b2 = some k2)
    (hs1 : s1 = pullSt u c1 b1)
    (h12 : State.step s1 (Move.foundToTab c2 b2) = some s12) :
    k1 ≠ k2 := by
  intro hEq
  have hwfS : s1.WF := by
    rw [hs1]
    exact step_wf hwf (by rw [step_foundToTab_splice htop1 hcp1]; rfl)
  obtain ⟨-, -, -, hcpS2, -⟩ := step_foundToTab_inv h12
  cases b2 with
  | inl a2 =>
      have hk2a : k2 = a2 :=
        (Option.some.inj (show (some a2 : Option Anchor) = some k2 from hk2)).symm
      obtain ⟨hemp, -⟩ := canPlace_inl hcpS2
      obtain ⟨-, hfu⟩ := (Pile.isEmpty_eq (s1.piles a2)).mp hemp
      have htopW : ((s1.piles k1).top) = some c1 := by
        rw [hs1]; exact pullSt_top_written hk1
      have hk1a : k1 = a2 := hEq.trans hk2a
      have hnone : ((s1.piles k1).top) = none := by
        rw [hk1a]
        show lastOf ((s1.piles a2).faceUp) = none
        rw [hfu]; rfl
      rw [htopW] at hnone
      cases hnone
  | inr z2 =>
      have hpk2 : u.pileOfTop z2 = some k2 := hk2
      obtain ⟨k', hpk', -⟩ := canPlace_inr hcpS2
      have htopk' : ((s1.piles k').top) = some z2 := (pileOfTop_eq_some_iff hwfS).mp hpk'
      have htopk2u : ((u.piles k2).top) = some z2 := (pileOfTop_eq_some_iff hwf).mp hpk2
      have hc1mem : c1 ∈ u.found c1.suit := lastOf_mem htop1
      have hc1z : c1 ≠ z2 := by
        intro hcz
        have hcon : (u.piles k2).top = some c1 := by rw [htopk2u, hcz]
        exact not_top_of_found hwf hc1mem k2 hcon
      by_cases hk' : k' = k1
      · have htopW : ((s1.piles k1).top) = some c1 := by
          rw [hs1]; exact pullSt_top_written hk1
        rw [hk'] at htopk'
        rw [htopW] at htopk'
        exact hc1z (Option.some.inj htopk')
      · have hpile : s1.piles k' = u.piles k' := by
          rw [hs1]; exact pullSt_piles_ne hk1 hk'
        have htopk'u : ((u.piles k').top) = some z2 := by
          rw [hpile] at htopk'; exact htopk'
        have hEqk : k' = k2 := top_unique hwf htopk'u htopk2u
        exact hk' (hEqk.trans hEq.symm)

/-! ## 3. The piles of the two orders agree -/

theorem pull_pull_piles {u : State} (hwf : u.WF) {c1 c2 : Card} {b1 b2 : Base}
    (htop1 : u.foundTop c1.suit = some c1) (hcp1 : u.canPlace c1 b1 = true)
    (htop2 : u.foundTop c2.suit = some c2) (hcp2 : u.canPlace c2 b2 = true)
    {k1 k2 : Anchor} (hk1 : tgt u b1 = some k1) (hk2 : tgt u b2 = some k2)
    (hne : k1 ≠ k2) :
    (pullSt (pullSt u c1 b1) c2 b2).piles = (pullSt (pullSt u c2 b2) c1 b1).piles := by
  have hstab2 : tgt (pullSt u c1 b1) b2 = some k2 :=
    tgt_pull_stable hwf htop1 hcp1 hk1 hk2 (Ne.symm hne)
  have hstab1 : tgt (pullSt u c2 b2) b1 = some k1 :=
    tgt_pull_stable hwf htop2 hcp2 hk2 hk1 hne
  funext a
  cases b1 with
  | inl a1 =>
    cases b2 with
    | inl a2 =>
      have hk1a : k1 = a1 :=
        (Option.some.inj (show (some a1 : Option Anchor) = some k1 from hk1)).symm
      have hk2a : k2 = a2 :=
        (Option.some.inj (show (some a2 : Option Anchor) = some k2 from hk2)).symm
      have h12 : a1 ≠ a2 := fun h => hne (hk1a.trans (h.trans hk2a.symm))
      simp only [pullSt_piles_inl_apply]
      by_cases h1 : a = a1
      · have h2 : ¬ a = a2 := fun h => h12 (h1.symm.trans h)
        simp only [ite_eq_left h1, ite_eq_right h2]
      · by_cases h2 : a = a2
        · simp only [ite_eq_left h2, ite_eq_right h1]
        · simp only [ite_eq_right h2, ite_eq_right h1]
    | inr z2 =>
      have hk1a : k1 = a1 :=
        (Option.some.inj (show (some a1 : Option Anchor) = some k1 from hk1)).symm
      have hz2 : u.pileOfTop z2 = some k2 := hk2
      have ha1k2 : a1 ≠ k2 := fun h => hne (hk1a.trans h)
      simp only [pullSt_piles_inr_apply _ _ _ _ hstab2, pullSt_piles_inl_apply,
        pullSt_piles_inr_apply _ _ _ _ hz2,
        ite_eq_right (show ¬ (k2 = a1) from fun h => ha1k2 h.symm)]
      by_cases h2 : a = k2
      · have h1 : ¬ a = a1 := fun h => ha1k2 (h.symm.trans h2)
        simp only [ite_eq_left h2, ite_eq_right h1]
      · by_cases h1 : a = a1
        · simp only [ite_eq_left h1, ite_eq_right h2]
        · simp only [ite_eq_right h1, ite_eq_right h2]
  | inr z1 =>
    cases b2 with
    | inl a2 =>
      have hk2a : k2 = a2 :=
        (Option.some.inj (show (some a2 : Option Anchor) = some k2 from hk2)).symm
      have hz1 : u.pileOfTop z1 = some k1 := hk1
      have ha2k1 : a2 ≠ k1 := fun h => hne (h.symm.trans hk2a.symm)
      simp only [pullSt_piles_inr_apply _ _ _ _ hstab1, pullSt_piles_inl_apply,
        pullSt_piles_inr_apply _ _ _ _ hz1,
        ite_eq_right (show ¬ (k1 = a2) from fun h => ha2k1 h.symm)]
      by_cases h1 : a = k1
      · have h2 : ¬ a = a2 := fun h => ha2k1 (h.symm.trans h1)
        simp only [ite_eq_left h1, ite_eq_right h2]
      · by_cases h2 : a = a2
        · simp only [ite_eq_left h2, ite_eq_right h1]
        · simp only [ite_eq_right h2, ite_eq_right h1]
    | inr z2 =>
      have hz1 : u.pileOfTop z1 = some k1 := hk1
      have hz2 : u.pileOfTop z2 = some k2 := hk2
      simp only [pullSt_piles_inr_apply _ _ _ _ hstab2, pullSt_piles_inr_apply _ _ _ _ hstab1,
        pullSt_piles_inr_apply _ _ _ _ hz1, pullSt_piles_inr_apply _ _ _ _ hz2,
        ite_eq_right (show ¬ (k2 = k1) from hne.symm),
        ite_eq_right (show ¬ (k1 = k2) from hne)]
      by_cases h2 : a = k2
      · have h1 : ¬ a = k1 := fun h => hne (h.symm.trans h2)
        simp only [ite_eq_left h2, ite_eq_right h1]
      · by_cases h1 : a = k1
        · simp only [ite_eq_left h1, ite_eq_right h2]
        · simp only [ite_eq_right h1, ite_eq_right h2]

/-! ## 4. The foundations of the two orders agree -/

theorem pull_pull_found_ne {u : State} {c1 c2 : Card} {b1 b2 : Base}
    (hsu : c1.suit ≠ c2.suit) :
    (pullSt (pullSt u c1 b1) c2 b2).found =
      (pullSt (pullSt u c2 b2) c1 b1).found := by
  funext s
  simp only [pullSt_found_apply,
    ite_eq_right (show ¬ (c2.suit = c1.suit) from fun h => hsu h.symm),
    ite_eq_right (show ¬ (c1.suit = c2.suit) from hsu)]
  by_cases h1 : s = c1.suit
  · have h2 : ¬ s = c2.suit := fun h => hsu (h1.symm.trans h)
    simp only [ite_eq_left h1, ite_eq_right h2]
  · by_cases h2 : s = c2.suit
    · simp only [ite_eq_left h2, ite_eq_right h1]
    · simp only [ite_eq_right h1, ite_eq_right h2]

/-! ## 5. Same-suit pulls cannot commute (the second order is dead) -/

/-- The foundation-prefix `nodup` row. -/
theorem found_nodup_local {st : State} (hwf : st.WF) (s : Suit) :
    (st.found s).Nodup := by
  obtain ⟨n, hn⟩ := hwf.1 s
  rw [hn]
  exact List.Pairwise.take (i := n) (by cases s <;> decide : (s.upCards).Nodup)

/-- The last foundation card is not in the chop (the `nodup` row). -/
theorem not_mem_chop_of_last {l : List Card} {c : Card} (hnd : l.Nodup)
    (hlast : lastOf l = some c) : c ∉ chop l := by
  obtain ⟨front, hfe⟩ := lastOf_eq_snoc hlast
  rw [hfe, chop_snoc]
  exact List.snoc_nodup_notMem front c (by rw [← hfe]; exact hnd)

/-- Two same-suit pulls cannot both fire in both orders. -/
theorem pull_pull_suit_contra {u s2 s21 : State} (hwf : u.WF) {c1 c2 : Card}
    {b1 b2 : Base}
    (htop1 : u.foundTop c1.suit = some c1)
    (hs2 : s2 = pullSt u c2 b2)
    (h21 : State.step s2 (Move.foundToTab c1 b1) = some s21)
    (hsu : c1.suit = c2.suit) : False := by
  obtain ⟨c1', htop21, hc1', -, -⟩ := step_foundToTab_inv h21
  have hmem : c1 ∈ s2.found c1.suit := by
    rw [hc1'] at htop21
    exact lastOf_mem htop21
  have hchop : s2.found c1.suit = chop (u.found c1.suit) := by
    rw [hs2, pullSt_found_apply, ite_eq_left hsu]
    rw [← hsu]
  have hmemChop : c1 ∈ chop (u.found c1.suit) := by
    rw [← hchop]
    exact hmem
  exact not_mem_chop_of_last (found_nodup_local hwf c1.suit)
    (show lastOf (u.found c1.suit) = some c1 from htop1) hmemChop

/-! ## 6. THE SQUARE -/

/-- Two pulls: both legal at `st` and each legal after the other imply
the same landing state. -/
theorem step_comm_pull_pull {st s1 s2 s12 s21 : State} {c1 c2 : Card} {b1 b2 : Base}
    (hwf : st.WF)
    (hrev1 : reversibleAtW st (Move.foundToTab c1 b1))
    (hrev2 : reversibleAtW st (Move.foundToTab c2 b2))
    (h1 : State.step st (Move.foundToTab c1 b1) = some s1)
    (h2 : State.step st (Move.foundToTab c2 b2) = some s2)
    (h12 : State.step s1 (Move.foundToTab c2 b2) = some s12)
    (h21 : State.step s2 (Move.foundToTab c1 b1) = some s21) :
    s12 = s21 := by
  obtain ⟨c1', htop1', hc1', hcp1, hs1⟩ := step_foundToTab_pullSt h1
  obtain ⟨c2', htop2', hc2', hcp2, hs2⟩ := step_foundToTab_pullSt h2
  rw [hc1'] at htop1'
  rw [hc2'] at htop2'
  obtain ⟨k1, hk1⟩ := exists_tgt_of_canPlace hcp1
  obtain ⟨k2, hk2⟩ := exists_tgt_of_canPlace hcp2
  by_cases hsu : c1.suit = c2.suit
  · exfalso
    exact pull_pull_suit_contra hwf htop1' hs2 h21 hsu
  · obtain ⟨-, -, -, -, hs12⟩ := step_foundToTab_pullSt h12
    obtain ⟨-, -, -, -, hs21⟩ := step_foundToTab_pullSt h21
    have hne : k1 ≠ k2 := pull_pull_tgt_ne hwf htop1' hcp1 hk1 hk2 hs1 h12
    rw [hs12, hs21, hs1, hs2]
    apply State.ext
    · exact pull_pull_found_ne hsu
    · exact pull_pull_piles hwf htop1' hcp1 htop2' hcp2 hk1 hk2 hne
    · rw [pullSt_stock, pullSt_stock, pullSt_stock, pullSt_stock]
    · rw [pullSt_waste, pullSt_waste, pullSt_waste, pullSt_waste]
    · rw [pullSt_drawStep, pullSt_drawStep, pullSt_drawStep, pullSt_drawStep]


-- ===== from Temp/Commute_Step_Raise.lean =====


/-- Two raises, both legal at `st` and each legal after the other, land
on the same state. -/
theorem step_comm_raise_raise {st s1 s2 s12 s21 : State} {c1 c2 : Card}
    (hwf : st.WF)
    (hrev1 : reversibleAtW st (Move.tabToFound c1))
    (hrev2 : reversibleAtW st (Move.tabToFound c2))
    (h1 : State.step st (Move.tabToFound c1) = some s1)
    (h2 : State.step st (Move.tabToFound c2) = some s2)
    (h12 : State.step s1 (Move.tabToFound c2) = some s12)
    (h21 : State.step s2 (Move.tabToFound c1) = some s21) :
    s12 = s21 := by
  by_cases hsu : c1.suit = c2.suit
  · exfalso
    exact raise_same_suit_contra hwf h1 h2 hsu h12
  · obtain ⟨w, hw12, hw21⟩ := twin_raise_square hwf hsu h1 h2
    have e1 : s12 = w := by
      rw [h12] at hw12
      exact Option.some.inj hw12
    have e2 : s21 = w := by
      rw [h21] at hw21
      exact Option.some.inj hw21
    rw [e1, e2]


-- ===== from Temp/Commute_Step_PullRaise.lean =====


/-! ## 0. `setFound` commutation at different suits -/

theorem tgt_raise_stable {u r : State} (hwf : u.WF) {d : Card} {a : Anchor} {b : Base}
    {k : Anchor} (hs : State.step u (Move.tabToFound d) = some r)
    (hda : u.pileOfTop d = some a)
    (hk : tgt u b = some k) (hne : k ≠ a) :
    tgt r b = some k := by
  obtain ⟨-, a', hpa', hs'⟩ := step_tabToFound_inv hs
  have haa : a' = a := by rw [hpa'] at hda; exact Option.some.inj hda
  have hr : r = raiseSt u d a := by rw [hs', haa]; rfl
  have hwfR : r.WF := step_wf hwf hs
  cases b with
  | inl a0 =>
      have ha0 : a0 = k := Option.some.inj (show (some a0 : Option Anchor) = some k from hk)
      show some a0 = some k
      rw [ha0]
  | inr z =>
      show r.pileOfTop z = some k
      have htopk : (r.piles k).top = some z := by
        have hpile : r.piles k = u.piles k := by
          rw [hr, raiseSt_piles_apply]
          exact ite_eq_right hne
        rw [hpile]
        exact (pileOfTop_eq_some_iff hwf).mp hk
      exact (pileOfTop_eq_some_iff hwfR).mpr htopk

/-! ## 2. The raised pile is not the pulled pile -/

/-- If a pull places `c` on pile `k` and a raise of `d` fires afterwards,
then `k` is not the raised pile `a`. -/
theorem pull_raise_pile_ne {u p s12 : State} (hwf : u.WF) {c d : Card} {b : Base}
    {k a : Anchor}
    (htop : u.foundTop c.suit = some c) (hcp : u.canPlace c b = true)
    (hk : tgt u b = some k) (hda : u.pileOfTop d = some a)
    (hp : p = pullSt u c b)
    (h12 : State.step p (Move.tabToFound d) = some s12) :
    k ≠ a := by
  intro hEq
  have hwfP : p.WF := by
    rw [hp]
    exact step_wf hwf (by rw [step_foundToTab_splice htop hcp]; rfl)
  obtain ⟨-, a', hpa', -⟩ := step_tabToFound_inv h12
  have htopa' : ((p.piles a').top) = some d := (pileOfTop_eq_some_iff hwfP).mp hpa'
  have htopa : ((p.piles a).top) = some c := by
    rw [← hEq, hp]
    exact pullSt_top_written hk
  have hc_found : c ∈ u.found c.suit := lastOf_mem htop
  have hd_pile : d ∈ (u.piles a).faceUp := lastOf_mem (pileOfTop_top hda).2
  by_cases haa : a' = a
  · rw [haa] at htopa'
    rw [htopa] at htopa'
    have hcd : c = d := Option.some.inj htopa'
    exact ((mem_found_unique hwf hc_found).1 a).2 (hcd ▸ hd_pile)
  · have hpile : p.piles a' = u.piles a' := by
      rw [hp]
      exact pullSt_piles_ne hk (fun hh => haa (hh.trans hEq))
    have htop_u : ((u.piles a').top) = some d := by
      rw [hpile] at htopa'; exact htopa'
    have htop_a_u : ((u.piles a).top) = some d := (pileOfTop_eq_some_iff hwf).mp hda
    exact haa (top_unique hwf htop_u htop_a_u)

/-! ## 3. The foundations agree -/

theorem pull_raise_found_ne {u p r : State} {c d : Card} {b : Base} {a : Anchor}
    (hp : p = pullSt u c b)
    (hr : r = raiseSt u d a)
    (hsu : c.suit ≠ d.suit) :
    (raiseSt p d a).found = (pullSt r c b).found := by
  rw [hp, hr]
  funext s
  simp only [raiseSt_found_apply, pullSt_found_apply,
    ite_eq_right (show ¬ (d.suit = c.suit) from fun h => hsu h.symm),
    ite_eq_right (show ¬ (c.suit = d.suit) from hsu)]
  by_cases hs1 : s = c.suit
  · simp only [hs1, ite_eq_right hsu, ite_eq_left rfl]
  · by_cases hs2 : s = d.suit
    · simp only [hs2, ite_eq_right (show ¬ (d.suit = c.suit) from fun h => hsu h.symm),
        ite_eq_left rfl]
    · simp only [ite_eq_right hs1, ite_eq_right hs2]

/-! ## 4. The piles agree -/

theorem pull_raise_piles {u p r : State} (hwf : u.WF) {c d : Card} {b : Base}
    {k a : Anchor}
    (htop : u.foundTop c.suit = some c) (hcp : u.canPlace c b = true)
    (hk : tgt u b = some k) (hda : u.pileOfTop d = some a)
    (hstep : State.step u (Move.tabToFound d) = some r)
    (hp : p = pullSt u c b)
    (hne : k ≠ a) :
    (raiseSt p d a).piles = (pullSt r c b).piles := by
  have hr : r = raiseSt u d a := by
    obtain ⟨-, a', hpa', hs'⟩ := step_tabToFound_inv hstep
    have haa : a' = a := by rw [hpa'] at hda; exact Option.some.inj hda
    rw [hs', haa]; rfl
  have hstabr : tgt r b = some k := tgt_raise_stable hwf hstep hda hk hne
  have hrk : r.piles k = u.piles k := by
    rw [hr, raiseSt_piles_apply]
    exact ite_eq_right hne
  rw [hr] at hstabr hrk
  have hpa : p.piles a = u.piles a := by
    rw [hp]
    exact pullSt_piles_ne hk (fun h => hne h.symm)
  have haQ : Pile.afterRunRemoved (p.piles a) (chop (p.piles a).faceUp)
      = Pile.afterRunRemoved (u.piles a) (chop (u.piles a).faceUp) := by
    rw [hpa]
  rw [hp, hr]
  funext a'
  cases b with
  | inl a0 =>
      have hk0 : k = a0 :=
        (Option.some.inj (show (some a0 : Option Anchor) = some k from hk)).symm
      have hne0 : a0 ≠ a := fun h => hne (hk0.trans h)
      simp only [raiseSt_piles_apply, pullSt_piles_inl_apply, haQ]
      by_cases h1 : a' = a
      · have h2 : ¬ a' = a0 := fun h => hne0 (h.symm.trans h1)
        simp only [ite_eq_left h1, ite_eq_right h2,
          ite_eq_right (show ¬ (a = a0) from fun h => hne0 h.symm)]
      · by_cases h2 : a' = a0
        · simp only [ite_eq_left h2, ite_eq_right h1]
        · simp only [ite_eq_right h2, ite_eq_right h1]
  | inr z =>
      have hz : u.pileOfTop z = some k := hk
      simp only [raiseSt_piles_apply, pullSt_piles_inr_apply _ _ _ _ hstabr,
        pullSt_piles_inr_apply _ _ _ _ hz, haQ, hrk]
      by_cases h1 : a' = a
      · have h2 : ¬ a' = k := fun h => hne (h.symm.trans h1)
        simp only [ite_eq_left h1, ite_eq_right h2,
          ite_eq_right (show ¬ (a = k) from fun h => hne h.symm)]
      · by_cases h2 : a' = k
        · simp only [ite_eq_left h2, ite_eq_right h1, ite_eq_right hne]
        · simp only [ite_eq_right h2, ite_eq_right h1]

/-! ## 5. THE SQUARE (pull then raise) -/

theorem step_comm_pull_raise {st s1 s2 s12 s21 : State} {c d : Card} {b : Base}
    (hwf : st.WF)
    (hrev1 : reversibleAtW st (Move.foundToTab c b))
    (hrev2 : reversibleAtW st (Move.tabToFound d))
    (h1 : State.step st (Move.foundToTab c b) = some s1)
    (h2 : State.step st (Move.tabToFound d) = some s2)
    (h12 : State.step s1 (Move.tabToFound d) = some s12)
    (h21 : State.step s2 (Move.foundToTab c b) = some s21) :
    s12 = s21 := by
  obtain ⟨c', htop', hc', hcp, hs1⟩ := step_foundToTab_pullSt h1
  rw [hc'] at htop'
  obtain ⟨hnext, a, hda, hs2⟩ := step_tabToFound_inv h2
  obtain ⟨k, hk⟩ := exists_tgt_of_canPlace hcp
  by_cases hsu : c.suit = d.suit
  · exfalso
    obtain ⟨hnextS, -⟩ := step_tabToFound_inv h12
    have hpull : s1.found d.suit = chop (st.found c.suit) := by
      rw [hs1, pullSt_found_apply, ite_eq_left hsu.symm]
    have hst_next : d.rank.toIdx = (st.found d.suit).length := by
      have h := of_decide_eq_true hnext
      simpa [State.nextUp, State.foundHeight] using h
    have hs1_next : d.rank.toIdx = (s1.found d.suit).length := by
      have h := of_decide_eq_true hnextS
      simpa [State.nextUp, State.foundHeight] using h
    have hchop : (chop (st.found c.suit)).length + 1 = (st.found c.suit).length := by
      have hlast : lastOf (st.found c.suit) = some c := htop'
      have h := lastOf_chop hlast
      rw [h, chop_snoc]
      simp
    rw [← hsu] at hst_next
    rw [hpull] at hs1_next
    omega
  · obtain ⟨-, a12, hpa12, hs12⟩ := step_tabToFound_inv h12
    have hne : k ≠ a := pull_raise_pile_ne hwf htop' hcp hk hda hs1 h12
    have ha12 : a12 = a := by
      have hwfS : s1.WF := step_wf hwf h1
      have htopa12 : ((s1.piles a12).top) = some d := (pileOfTop_eq_some_iff hwfS).mp hpa12
      by_cases ha : a12 = a
      · exact ha
      · exfalso
        by_cases hak : a12 = k
        · have htopk : ((s1.piles k).top) = some c := by
            rw [hs1]; exact pullSt_top_written hk
          rw [← hak] at htopk
          rw [htopa12] at htopk
          have hcd : c = d := (Option.some.inj htopk).symm
          have hc_found : c ∈ st.found c.suit := lastOf_mem htop'
          have hd_pile : d ∈ (st.piles a).faceUp :=
            lastOf_mem (pileOfTop_top hda).2
          exact ((mem_found_unique hwf hc_found).1 a).2 (hcd ▸ hd_pile)
        · have hpile : s1.piles a12 = st.piles a12 := by
            rw [hs1]; exact pullSt_piles_ne hk hak
          have htop_u : ((st.piles a12).top) = some d := by
            rw [hpile] at htopa12; exact htopa12
          have htop_a_u : ((st.piles a).top) = some d := (pileOfTop_eq_some_iff hwf).mp hda
          exact ha (top_unique hwf htop_u htop_a_u)
    rw [ha12] at hs12
    obtain ⟨-, -, -, -, hs21⟩ := step_foundToTab_pullSt h21
    have hr : s2 = raiseSt st d a := by rw [hs2]; rfl
    rw [hr] at h2
    have hs12' : s12 = raiseSt s1 d a := by rw [hs12]; rfl
    rw [hs12', hs21, hs1, hr]
    apply State.ext
    · exact pull_raise_found_ne rfl rfl hsu
    · exact pull_raise_piles hwf htop' hcp hk hda h2 rfl hne
    · rw [raiseSt_stock, pullSt_stock, pullSt_stock, raiseSt_stock]
    · rw [raiseSt_waste, pullSt_waste, pullSt_waste, raiseSt_waste]
    · rw [raiseSt_drawStep, pullSt_drawStep, pullSt_drawStep, raiseSt_drawStep]

/-- The converse order: a raise then a pull. -/
theorem step_comm_raise_pull {st s1 s2 s12 s21 : State} {c d : Card} {b : Base}
    (hwf : st.WF)
    (hrev1 : reversibleAtW st (Move.tabToFound d))
    (hrev2 : reversibleAtW st (Move.foundToTab c b))
    (h1 : State.step st (Move.tabToFound d) = some s1)
    (h2 : State.step st (Move.foundToTab c b) = some s2)
    (h12 : State.step s1 (Move.foundToTab c b) = some s12)
    (h21 : State.step s2 (Move.tabToFound d) = some s21) :
    s12 = s21 := by
  exact (step_comm_pull_raise hwf hrev2 hrev1 h2 h1 h21 h12).symm


-- ===== from Temp/Commute_Step_Draw.lean =====


/-! ## 0. The draw's field determinism -/

/-- `recycle`'s stock, closed form. -/
theorem recycle_stock (st : State) :
    (State.recycle st).stock =
      (if st.stock = [] then st.waste.reverse else st.stock) := by
  unfold State.recycle
  split
  · split <;> simp_all
  · simp_all

/-- `recycle`'s waste, closed form. -/
theorem recycle_waste (st : State) :
    (State.recycle st).waste = (if st.stock = [] then [] else st.waste) := by
  unfold State.recycle
  split
  · split <;> simp_all
  · simp_all

/-- `recycle`'s stock reads only the stock and waste. -/
theorem recycle_stock_eq {u v : State} (hs : u.stock = v.stock) (hw : u.waste = v.waste) :
    (State.recycle u).stock = (State.recycle v).stock := by
  rw [recycle_stock, recycle_stock, hs, hw]

/-- `recycle`'s waste reads only the stock. -/
theorem recycle_waste_eq {u v : State} (hs : u.stock = v.stock) (hw : u.waste = v.waste) :
    (State.recycle u).waste = (State.recycle v).waste := by
  rw [recycle_waste, recycle_waste, hs, hw]

/-- Two draws from positions with the same stock, waste and draw step
produce the same stock and waste. -/
theorem stepDraw_stock_waste {u v a b : State}
    (hs : u.stock = v.stock) (hw : u.waste = v.waste) (hd : u.drawStep = v.drawStep)
    (ha : u.stepDraw = some a) (hb : v.stepDraw = some b) :
    a.stock = b.stock ∧ a.waste = b.waste := by
  obtain ⟨ru, hru, -, hau⟩ := draw_unfold ha
  obtain ⟨rv, hrv, -, hbv⟩ := draw_unfold hb
  subst hru
  subst hrv
  have hst : (State.recycle u).stock = (State.recycle v).stock := recycle_stock_eq hs hw
  have hwa : (State.recycle u).waste = (State.recycle v).waste := recycle_waste_eq hs hw
  have hdr : (State.recycle u).drawStep = (State.recycle v).drawStep := by
    rw [recycle_drawStep, recycle_drawStep, hd]
  rw [hau, hbv]
  constructor <;>
    rw [dealUpTo_eq_take_drop, dealUpTo_eq_take_drop, hst, hwa, hdr]

/-! ## 1. Pile-map congruence helpers -/

/-- `putCard`'s pile map reads only the input piles. -/
theorem putCard_piles_congr {u v : State} (hp : u.piles = v.piles) (c : Card) (b : Base) :
    (u.putCard c b).piles = (v.putCard c b).piles := by
  cases b with
  | inl a => rw [putCard_piles_inl, putCard_piles_inl, hp]
  | inr z =>
      have hpq : u.pileOfTop z = v.pileOfTop z := pileOfTop_piles hp z
      cases hz : u.pileOfTop z with
      | none =>
          have hz' : v.pileOfTop z = none := by rw [← hpq]; exact hz
          simp only [State.putCard, hz, hz', hp]
      | some k =>
          have hz' : v.pileOfTop z = some k := by rw [← hpq]; exact hz
          rw [putCard_piles_inr _ _ _ _ hz, putCard_piles_inr _ _ _ _ hz', hp]

/-- The pull's foundations read only the input foundations. -/
theorem pullSt_found_congr {u v : State} (hf : u.found = v.found) (c : Card) (b : Base) :
    (pullSt u c b).found = (pullSt v c b).found := by
  funext s
  rw [pullSt_found_apply, pullSt_found_apply, hf]

/-- The pull's piles read only the input piles. -/
theorem pullSt_piles_congr {u v : State} (hp : u.piles = v.piles) (c : Card) (b : Base) :
    (pullSt u c b).piles = (pullSt v c b).piles := by
  rw [pullSt_piles, pullSt_piles, putCard_piles_congr hp]

/-- `raiseSt`'s foundations read only the input foundations. -/
theorem raiseSt_found_congr {u v : State} (hf : u.found = v.found) (c : Card) (a : Anchor) :
    (raiseSt u c a).found = (raiseSt v c a).found := by
  funext s
  rw [raiseSt_found_apply, raiseSt_found_apply, hf]

/-- `raiseSt`'s piles read only the input piles. -/
theorem raiseSt_piles_congr {u v : State} (hp : u.piles = v.piles) (c : Card) (a : Anchor) :
    (raiseSt u c a).piles = (raiseSt v c a).piles := by
  funext a'
  rw [raiseSt_piles_apply, raiseSt_piles_apply, hp]

/-! ## 2. draw / draw -/

theorem step_comm_draw_draw {st s1 s2 s12 s21 : State}
    (hwf : st.WF)
    (hrev1 : reversibleAtW st Move.draw)
    (hrev2 : reversibleAtW st Move.draw)
    (h1 : State.step st Move.draw = some s1)
    (h2 : State.step st Move.draw = some s2)
    (h12 : State.step s1 Move.draw = some s12)
    (h21 : State.step s2 Move.draw = some s21) :
    s12 = s21 := by
  have h12' : s1 = s2 := by
    rw [h1] at h2
    exact Option.some.inj h2
  rw [h12'] at h12
  rw [h12] at h21
  exact Option.some.inj h21

/-! ## 3. draw / raise -/

theorem step_comm_draw_raise {st s1 s2 s12 s21 : State} {c : Card}
    (hwf : st.WF)
    (hrev1 : reversibleAtW st Move.draw)
    (hrev2 : reversibleAtW st (Move.tabToFound c))
    (h1 : State.step st Move.draw = some s1)
    (h2 : State.step st (Move.tabToFound c) = some s2)
    (h12 : State.step s1 (Move.tabToFound c) = some s12)
    (h21 : State.step s2 Move.draw = some s21) :
    s12 = s21 := by
  obtain ⟨-, a, hda, hs2⟩ := step_tabToFound_inv h2
  obtain ⟨-, a1, hda1, hs12⟩ := step_tabToFound_inv h12
  have h1f : s1.found = st.found := stepDraw_found h1
  have h1p : s1.piles = st.piles := stepDraw_piles h1
  have hpq : s1.pileOfTop c = st.pileOfTop c := pileOfTop_piles h1p c
  rw [hpq, hda] at hda1
  have ha1 : a1 = a := by injection hda1 with h; exact h.symm
  rw [ha1] at hs12
  have hs12' : s12 = raiseSt s1 c a := by rw [hs12]; rfl
  have hs2' : s2 = raiseSt st c a := by rw [hs2]; rfl
  have h2s : s2.stock = st.stock := by rw [hs2', raiseSt_stock]
  have h2w : s2.waste = st.waste := by rw [hs2', raiseSt_waste]
  have h2d : s2.drawStep = st.drawStep := by rw [hs2', raiseSt_drawStep]
  have hsw := stepDraw_stock_waste h2s h2w h2d h21 h1
  apply State.ext
  · rw [hs12', stepDraw_found h21, hs2']
    exact raiseSt_found_congr h1f c a
  · rw [hs12', stepDraw_piles h21, hs2']
    exact raiseSt_piles_congr h1p c a
  · rw [hs12', raiseSt_stock, hsw.1]
  · rw [hs12', raiseSt_waste, hsw.2]
  · rw [hs12', raiseSt_drawStep, draw_drawStep h21, h2d,
      ← draw_drawStep h1]

/-! ## 4. draw / pull -/

theorem step_comm_draw_pull {st s1 s2 s12 s21 : State} {c : Card} {b : Base}
    (hwf : st.WF)
    (hrev1 : reversibleAtW st Move.draw)
    (hrev2 : reversibleAtW st (Move.foundToTab c b))
    (h1 : State.step st Move.draw = some s1)
    (h2 : State.step st (Move.foundToTab c b) = some s2)
    (h12 : State.step s1 (Move.foundToTab c b) = some s12)
    (h21 : State.step s2 Move.draw = some s21) :
    s12 = s21 := by
  obtain ⟨-, htop2, hc2, hcp2, hs2⟩ := step_foundToTab_pullSt h2
  obtain ⟨-, htop1, hc1, hcp1, hs12⟩ := step_foundToTab_pullSt h12
  have h1f : s1.found = st.found := stepDraw_found h1
  have h1p : s1.piles = st.piles := stepDraw_piles h1
  have h2s : s2.stock = st.stock := by rw [hs2, pullSt_stock]
  have h2w : s2.waste = st.waste := by rw [hs2, pullSt_waste]
  have h2d : s2.drawStep = st.drawStep := by rw [hs2, pullSt_drawStep]
  have hsw := stepDraw_stock_waste h2s h2w h2d h21 h1
  apply State.ext
  · rw [hs12, stepDraw_found h21, hs2]
    exact pullSt_found_congr h1f c b
  · rw [hs12, stepDraw_piles h21, hs2]
    exact pullSt_piles_congr h1p c b
  · rw [hs12, pullSt_stock, hsw.1]
  · rw [hs12, pullSt_waste, hsw.2]
  · rw [hs12, pullSt_drawStep, draw_drawStep h21, h2d,
      ← draw_drawStep h1]


-- ===== from Temp/Commute_Step_Assembly.lean =====


/-- The letter is not a slide. -/
def NoSlide (m : Move) : Prop :=
  ∀ (c : Card) (b : Base), m ≠ Move.tabToTab c b

/-- **THE LOCAL DIAMOND** over the slide-free reversible letters. -/
theorem diamond_noslide {st s1 s2 s12 s21 : State} {m1 m2 : Move}
    (hwf : st.WF)
    (hrev1 : reversibleAtW st m1) (hrev2 : reversibleAtW st m2)
    (hn1 : NoSlide m1) (hn2 : NoSlide m2)
    (h1 : State.step st m1 = some s1)
    (h2 : State.step st m2 = some s2)
    (h12 : State.step s1 m2 = some s12)
    (h21 : State.step s2 m1 = some s21) :
    s12 = s21 := by
  cases m1 with
  | wasteToFound c => exact absurd hrev1 (wasteToFound_not_reversibleAtW st c)
  | wasteToTab c b => exact absurd hrev1 (wasteToTab_not_reversibleAtW st c b)
  | tabToTab c b => exact absurd rfl (hn1 c b)
  | draw =>
      cases m2 with
      | wasteToFound c => exact absurd hrev2 (wasteToFound_not_reversibleAtW st c)
      | wasteToTab c b => exact absurd hrev2 (wasteToTab_not_reversibleAtW st c b)
      | tabToTab c b => exact absurd rfl (hn2 c b)
      | draw => exact step_comm_draw_draw hwf hrev1 hrev2 h1 h2 h12 h21
      | tabToFound c => exact step_comm_draw_raise hwf hrev1 hrev2 h1 h2 h12 h21
      | foundToTab c b => exact step_comm_draw_pull hwf hrev1 hrev2 h1 h2 h12 h21
  | tabToFound c =>
      cases m2 with
      | wasteToFound c' => exact absurd hrev2 (wasteToFound_not_reversibleAtW st c')
      | wasteToTab c' b' => exact absurd hrev2 (wasteToTab_not_reversibleAtW st c' b')
      | tabToTab c' b' => exact absurd rfl (hn2 c' b')
      | draw => exact (step_comm_draw_raise hwf hrev2 hrev1 h2 h1 h21 h12).symm
      | tabToFound d => exact step_comm_raise_raise hwf hrev1 hrev2 h1 h2 h12 h21
      | foundToTab d b => exact step_comm_raise_pull hwf hrev1 hrev2 h1 h2 h12 h21
  | foundToTab c b =>
      cases m2 with
      | wasteToFound c' => exact absurd hrev2 (wasteToFound_not_reversibleAtW st c')
      | wasteToTab c' b' => exact absurd hrev2 (wasteToTab_not_reversibleAtW st c' b')
      | tabToTab c' b' => exact absurd rfl (hn2 c' b')
      | draw => exact (step_comm_draw_pull hwf hrev2 hrev1 h2 h1 h21 h12).symm
      | tabToFound d => exact step_comm_pull_raise hwf hrev1 hrev2 h1 h2 h12 h21
      | foundToTab d b' => exact step_comm_pull_pull hwf hrev1 hrev2 h1 h2 h12 h21

/-- **ADJACENT-SWAP**: an adjacent independent pair of the slide-free
reversible letters can be exchanged in a play (the path-normalization
step). -/
theorem swap_adjacent_noslide {st mid e mid2 e2 : State} {m1 m2 : Move}
    (hwf : st.WF)
    (hrev1 : reversibleAtW st m1) (hrev2 : reversibleAtW st m2)
    (hn1 : NoSlide m1) (hn2 : NoSlide m2)
    (h1 : State.step st m1 = some mid)
    (h12 : State.step mid m2 = some e)
    (h2 : State.step st m2 = some mid2)
    (h21 : State.step mid2 m1 = some e2) :
    ∃ mid', State.step st m2 = some mid' ∧ State.step mid' m1 = some e := by
  have hEq : e = e2 :=
    diamond_noslide hwf hrev1 hrev2 hn1 hn2 h1 h2 h12 h21
  refine ⟨mid2, h2, ?_⟩
  rw [hEq]
  exact h21


end CommuteStep

#print axioms CommuteStep.step_comm_pull_pull
#print axioms CommuteStep.step_comm_raise_raise
#print axioms CommuteStep.step_comm_pull_raise
#print axioms CommuteStep.step_comm_raise_pull
#print axioms CommuteStep.step_comm_draw_draw
#print axioms CommuteStep.step_comm_draw_raise
#print axioms CommuteStep.step_comm_draw_pull
#print axioms CommuteStep.diamond_noslide
#print axioms CommuteStep.swap_adjacent_noslide
