import Orig2.FloatFiber

namespace KingFuel

theorem kf_pileOfTop_top {st : State} {z : Card} {k : Anchor}
    (h : st.pileOfTop z = some k) :
    lastOf (st.piles k).faceUp = some z := by
  have hd := firstWhere_sound (p := fun a => decide (st.topOf a = some z)) h
  exact of_decide_eq_true hd

theorem kf_setFound_putCard_piles (st : State) (s : Suit) (l : List Card)
    (c : Card) (b : Base) :
    ((st.setFound s l).putCard c b).piles = (st.putCard c b).piles := by
  cases b with
  | inl a => rfl
  | inr z =>
      simp only [State.putCard]
      rw [show (st.setFound s l).pileOfTop z = st.pileOfTop z from rfl]
      cases hz : st.pileOfTop z <;> rfl

theorem kf_putCard_isEmpty_false {s : State} {c : Card} {b : Base} {a : Anchor}
    (h : (s.piles a).isEmpty = false) :
    ((s.putCard c b).piles a).isEmpty = false := by
  cases b with
  | inl a0 =>
      rw [putCard_piles_inl]
      change (if a = a0 then (⟨[], [c]⟩ : Pile) else s.piles a).isEmpty = false
      by_cases ha : a = a0
      · rw [ite_eq_left ha]
        simp [Pile.isEmpty]
      · rw [ite_eq_right ha]
        exact h
  | inr z =>
      cases hz : s.pileOfTop z with
      | none =>
          rw [show s.putCard c (Sum.inr z) = s from by
            simp only [State.putCard, hz]]
          exact h
      | some k =>
          rw [putCard_inr_eq hz]
          by_cases hak : a = k
          · rw [hak, setPile_piles_self]
            rcases s.piles k with ⟨hd, fu⟩
            cases hd <;> simp [Pile.isEmpty]
          · rw [setPile_piles_ne hak]
            exact h

theorem kf_afterRunRemoved_chop_isEmpty_iff {p : Pile} {x : Card}
    (htop : lastOf p.faceUp = some x) :
    (Pile.afterRunRemoved p (chop p.faceUp)).isEmpty = true ↔
      p.faceUp = [x] ∧ p.hidden = [] := by
  obtain ⟨front, hfront⟩ := lastOf_eq_snoc htop
  have hchop : chop p.faceUp = front := by rw [hfront, chop_snoc]
  rw [hchop]
  rcases p with ⟨hd, fu⟩
  simp only at hfront
  cases front with
  | nil =>
      simp only [List.nil_append] at hfront
      subst hfront
      cases hd <;> simp [Pile.afterRunRemoved, Pile.revealTop, Pile.isEmpty]
  | cons g gs =>
      simp [Pile.afterRunRemoved, Pile.isEmpty, hfront]

theorem raise_empties_iff {u v : State} {x : Card} {a : Anchor}
    (hstep : State.step u (Move.tabToFound x) = some v)
    (hpa : u.pileOfTop x = some a) :
    (v.piles a).isEmpty = true ↔
      (u.piles a).faceUp = [x] ∧ (u.piles a).hidden = [] := by
  obtain ⟨-, a', hpa', hv⟩ := step_tabToFound_inv hstep
  have haa : a' = a := Option.some.inj (hpa'.symm.trans hpa)
  subst a'
  rw [hv]
  change (if a = a then
      Pile.afterRunRemoved (u.piles a) (chop (u.piles a).faceUp)
      else u.piles a).isEmpty = true ↔
    (u.piles a).faceUp = [x] ∧ (u.piles a).hidden = []
  rw [ite_eq_left rfl]
  exact kf_afterRunRemoved_chop_isEmpty_iff (kf_pileOfTop_top hpa)

theorem pull_empties_iff {u v : State} {x : Card} {b : Base}
    (hstep : State.step u (Move.foundToTab x b) = some v) :
    ∀ a : Anchor, (v.piles a).isEmpty = true ↔
      (u.piles a).isEmpty = true ∧ b ≠ Sum.inl a := by
  obtain ⟨c', -, -, -, hv⟩ := step_foundToTab_inv hstep
  intro a
  rw [hv]
  have hpiles :
      ((u.setFound x.suit (chop (u.found x.suit))).putCard x b).piles
        = (u.putCard x b).piles :=
    kf_setFound_putCard_piles u x.suit (chop (u.found x.suit)) x b
  rw [hpiles]
  cases b with
  | inl a0 =>
      rw [putCard_piles_inl]
      by_cases ha : a = a0
      · subst ha
        simp [Pile.isEmpty]
      · simp [Pile.isEmpty, ha, Ne.symm ha]
  | inr z =>
      cases hz : u.pileOfTop z with
      | none =>
          rw [show u.putCard x (Sum.inr z) = u from by
            simp only [State.putCard, hz]]
          simp
      | some k =>
          rw [putCard_inr_eq hz]
          by_cases hak : a = k
          · rw [hak]
            rw [setPile_piles_self]
            have htop : lastOf (u.piles k).faceUp = some z := kf_pileOfTop_top hz
            have hne : (u.piles k).faceUp ≠ [] := by
              intro hnil
              rw [hnil] at htop
              simp [lastOf] at htop
            have hnk : (u.piles k).isEmpty = false := by
              cases h : (u.piles k).isEmpty with
              | false => rfl
              | true => exact absurd ((Pile.isEmpty_eq _).mp h).2 hne
            have hnew :
                ({ u.piles k with
                    faceUp := (u.piles k).faceUp ++ [x] } : Pile).isEmpty = false := by
              rcases u.piles k with ⟨hd, fu⟩
              cases hd <;> simp [Pile.isEmpty]
            simp [hnew, hnk]
          · rw [setPile_piles_ne hak]
            simp

theorem empty_gain_step_is_raise_or_slide {u v : State} {m : Move}
    (hstep : State.step u m = some v)
    (hne : ∀ a : Anchor, (u.piles a).isEmpty = false)
    (hve : ∃ a : Anchor, (v.piles a).isEmpty = true) :
    (∃ x : Card, ∃ a : Anchor, m = Move.tabToFound x ∧
      u.pileOfTop x = some a ∧ (v.piles a).isEmpty = true) ∨
    (∃ x : Card, ∃ b : Base, m = Move.tabToTab x b) := by
  cases m with
  | draw =>
      obtain ⟨a, ha⟩ := hve
      have hp : v.piles = u.piles := stepDraw_piles hstep
      rw [hp] at ha
      exact absurd (hne a) (by rw [ha]; simp)
  | wasteToFound c =>
      obtain ⟨-, x, xs, -, hs⟩ := step_wasteToFound_inv hstep
      obtain ⟨a, ha⟩ := hve
      have hp : v.piles = u.piles := by rw [hs]; rfl
      rw [hp] at ha
      exact absurd (hne a) (by rw [ha]; simp)
  | wasteToTab c b =>
      obtain ⟨-, x, xs, -, hs⟩ := step_wasteToTab_inv hstep
      obtain ⟨a, ha⟩ := hve
      have hp : (v.piles a) = (u.putCard c b).piles a := by rw [hs]
      rw [hp] at ha
      exact absurd (kf_putCard_isEmpty_false (hne a)) (by rw [ha]; simp)
  | foundToTab c b =>
      obtain ⟨c', -, -, -, hs⟩ := step_foundToTab_inv hstep
      obtain ⟨a, ha⟩ := hve
      have hp : (v.piles a) = (u.putCard c b).piles a := by
        rw [hs]
        exact congrFun
          (kf_setFound_putCard_piles u c.suit (chop (u.found c.suit)) c b) a
      rw [hp] at ha
      exact absurd (kf_putCard_isEmpty_false (hne a)) (by rw [ha]; simp)
  | tabToFound x =>
      obtain ⟨-, a, hpa, hs⟩ := step_tabToFound_inv hstep
      obtain ⟨a0, ha0⟩ := hve
      by_cases hEq : a0 = a
      · subst a0
        exact Or.inl ⟨x, a, rfl, hpa, ha0⟩
      · have hfalse : (v.piles a0).isEmpty = false := by
          have hp : (v.piles a0) =
              (if a0 = a then
                Pile.afterRunRemoved (u.piles a) (chop (u.piles a).faceUp)
                else u.piles a0) := by rw [hs]
          rw [hp, ite_eq_right hEq]
          exact hne a0
        exact absurd hfalse (by rw [ha0]; simp)
  | tabToTab x b =>
      exact Or.inr ⟨x, b, rfl⟩
def kf_KingAnchor (p : Pile) : Prop :=
  p.hidden = [] ∧
    (p.faceUp = [] ∨
      ∃ y : Card, p.faceUp.head? = some y ∧ y.rank = Rank.king)

theorem kf_head?_append_of_ne_nil {l r : List Card} (h : l ≠ []) :
    (l ++ r).head? = l.head? := by
  cases l with
  | nil => exact absurd rfl h
  | cons x xs => rfl

theorem kf_head?_chop_of_ne_nil {l : List Card} (h : chop l ≠ []) :
    (chop l).head? = l.head? := by
  cases l with
  | nil => simp [chop] at h
  | cons x xs =>
      cases xs with
      | nil => simp [chop] at h
      | cons y ys => rfl

theorem kf_head?_below_of_ne_nil (c : Card) {l : List Card}
    (h : below c l ≠ []) :
    (below c l).head? = l.head? := by
  cases l with
  | nil => simp [below] at h
  | cons x xs =>
      rw [below_cons] at h ⊢
      by_cases hx : x = c
      · rw [ite_eq_left hx] at h ⊢
        exact absurd rfl h
      · rw [ite_eq_right hx]
        rfl

theorem kf_afterRunRemoved_chop_KingAnchor {p : Pile}
    (h : kf_KingAnchor p) :
    kf_KingAnchor (Pile.afterRunRemoved p (chop p.faceUp)) := by
  obtain ⟨hhd, hfu⟩ := h
  by_cases hc : chop p.faceUp = []
  · rw [hc]
    rw [Pile.afterRunRemoved_bare hhd]
    exact ⟨rfl, Or.inl rfl⟩
  · rw [afterRunRemoved_ne hc]
    refine ⟨hhd, Or.inr ?_⟩
    rcases hfu with hnil | ⟨y, hy, hky⟩
    · rw [hnil] at hc
      simp [chop] at hc
    · exact ⟨y, (kf_head?_chop_of_ne_nil hc).trans hy, hky⟩

theorem kf_afterRunRemoved_below_KingAnchor {p : Pile} {c : Card}
    (h : kf_KingAnchor p) :
    kf_KingAnchor (Pile.afterRunRemoved p (below c p.faceUp)) := by
  obtain ⟨hhd, hfu⟩ := h
  by_cases hb : below c p.faceUp = []
  · rw [hb]
    rw [Pile.afterRunRemoved_bare hhd]
    exact ⟨rfl, Or.inl rfl⟩
  · rw [afterRunRemoved_ne hb]
    refine ⟨hhd, Or.inr ?_⟩
    rcases hfu with hnil | ⟨y, hy, hky⟩
    · rw [hnil] at hb
      simp [below] at hb
    · exact ⟨y, (kf_head?_below_of_ne_nil c hb).trans hy, hky⟩

theorem kf_append_KingAnchor {p : Pile} {run : List Card}
    (h : kf_KingAnchor p) (hne : p.faceUp ≠ []) :
    kf_KingAnchor { p with faceUp := p.faceUp ++ run } := by
  obtain ⟨hhd, hfu⟩ := h
  refine ⟨hhd, Or.inr ?_⟩
  rcases hfu with hnil | ⟨y, hy, hky⟩
  · exact absurd hnil hne
  · have hfne : p.faceUp ≠ [] := by
      intro hf
      rw [hf] at hy
      simp at hy
    exact ⟨y, (kf_head?_append_of_ne_nil hfne).trans hy, hky⟩

theorem kf_putCard_KingAnchor {s : State} {c : Card} {b : Base} {a : Anchor}
    (hcp : s.canPlace c b = true) (h : kf_KingAnchor (s.piles a)) :
    kf_KingAnchor ((s.putCard c b).piles a) := by
  cases b with
  | inl k =>
      rw [putCard_piles_inl]
      change kf_KingAnchor (if a = k then (⟨[], [c]⟩ : Pile) else s.piles a)
      by_cases hak : a = k
      · rw [ite_eq_left hak]
        obtain ⟨-, hkng⟩ := canPlace_inl hcp
        exact ⟨rfl, Or.inr ⟨c, rfl, hkng⟩⟩
      · rw [ite_eq_right hak]
        exact h
  | inr z =>
      cases hz : s.pileOfTop z with
      | none =>
          rw [show s.putCard c (Sum.inr z) = s from by
            simp only [State.putCard, hz]]
          exact h
      | some k =>
          rw [putCard_inr_eq hz]
          change kf_KingAnchor (if a = k then
            { s.piles k with faceUp := (s.piles k).faceUp ++ [c] }
            else s.piles a)
          by_cases hak : a = k
          · rw [ite_eq_left hak]
            have hbase : kf_KingAnchor (s.piles k) := by
              rw [← hak]; exact h
            have hfne : (s.piles k).faceUp ≠ [] := by
              have htop := kf_pileOfTop_top hz
              intro hnil
              rw [hnil] at htop
              simp [lastOf] at htop
            exact kf_append_KingAnchor hbase hfne
          · rw [ite_eq_right hak]
            exact h

theorem kf_step_KingAnchor {s s' : State} {m : Move} {a : Anchor}
    (hstep : State.step s m = some s')
    (h : kf_KingAnchor (s.piles a)) :
    kf_KingAnchor (s'.piles a) := by
  cases m with
  | draw =>
      rw [stepDraw_piles hstep]
      exact h
  | wasteToFound c =>
      obtain ⟨-, x, xs, -, hs⟩ := step_wasteToFound_inv hstep
      rw [hs]
      exact h
  | wasteToTab c b =>
      obtain ⟨hg, x, xs, -, hs⟩ := step_wasteToTab_inv hstep
      rw [Bool.and_eq_true] at hg
      rw [hs]
      change kf_KingAnchor ((s.putCard c b).piles a)
      exact kf_putCard_KingAnchor hg.2 h
  | foundToTab c b =>
      obtain ⟨c', ht, hce, hcp, hs⟩ := step_foundToTab_inv hstep
      rw [hs]
      rw [show ((s.setFound c.suit (chop (s.found c.suit))).putCard c b).piles a
            = (s.putCard c b).piles a from
          congrFun (kf_setFound_putCard_piles s c.suit
            (chop (s.found c.suit)) c b) a]
      exact kf_putCard_KingAnchor hcp h
  | tabToFound c =>
      obtain ⟨-, a0, hp, hs⟩ := step_tabToFound_inv hstep
      rw [hs]
      change kf_KingAnchor (if a = a0 then
          Pile.afterRunRemoved (s.piles a0) (chop (s.piles a0).faceUp)
          else s.piles a)
      by_cases ha : a = a0
      · rw [ite_eq_left ha]
        have hbase : kf_KingAnchor (s.piles a0) := by
          rw [← ha]; exact h
        exact kf_afterRunRemoved_chop_KingAnchor hbase
      · rw [ite_eq_right ha]
        exact h
  | tabToTab c b =>
      obtain ⟨a0, hh, hcp, hne, hs⟩ := step_tabToTab_inv hstep
      rw [hs]
      let w : State := s.setPile a0
        (Pile.afterRunRemoved (s.piles a0) (below c (s.piles a0).faceUp))
      let run : List Card := fromCard c (s.piles a0).faceUp
      change kf_KingAnchor ((w.putRun run b).piles a)
      have hmid : kf_KingAnchor (w.piles a) := by
        dsimp [w]
        by_cases ha : a = a0
        · rw [ha]
          rw [setPile_piles_self]
          have hbase : kf_KingAnchor (s.piles a0) := by
            rw [← ha]; exact h
          exact kf_afterRunRemoved_below_KingAnchor hbase
        · rw [setPile_piles_ne ha]
          exact h
      cases b with
      | inl k =>
          by_cases hak : a = k
          · rw [hak]
            rw [putRun_piles_inl_self]
            dsimp [run]
            obtain ⟨-, hkng⟩ := canPlace_inl hcp
            have hmem : c ∈ (s.piles a0).faceUp := pileHolding_mem hh
            obtain ⟨tr, hrun⟩ := tfc_fromCard_cons_head (c := c)
              (s.piles a0).faceUp hmem
            rw [hrun]
            exact ⟨rfl, Or.inr ⟨c, rfl, hkng⟩⟩
          · rw [putRun_piles_inl_ne w run k a hak]
            exact hmid
      | inr z =>
          cases hz : w.pileOfTop z with
          | none =>
              rw [putRun_inr_none_piles hz a]
              exact hmid
          | some k =>
              by_cases hak : a = k
              · rw [hak]
                rw [putRun_piles_inr_self w run z k hz]
                have hbase : kf_KingAnchor (w.piles k) := by
                  rw [← hak]; exact hmid
                have hfne : (w.piles k).faceUp ≠ [] := by
                  have htop := kf_pileOfTop_top hz
                  intro hnil
                  rw [hnil] at htop
                  simp [lastOf] at htop
                exact kf_append_KingAnchor hbase hfne
              · rw [putRun_piles_inr_ne w run z k hz hak]
                exact hmid

theorem kf_run_KingAnchor {s t : State} {a : Anchor} {ms : List Move}
    (hrun : s.run ms = some t) (h : kf_KingAnchor (s.piles a)) :
    kf_KingAnchor (t.piles a) := by
  induction ms generalizing s with
  | nil =>
      have hst : s = t := Option.some.inj hrun
      subst t
      exact h
  | cons m rest ih =>
      obtain ⟨s', hstep', hrest⟩ := State.run_cons hrun
      exact ih hrest (kf_step_KingAnchor hstep' h)

theorem empty_gain_step_is_raise {u v : State} {m : Move}
    (hstep : State.step u m = some v)
    (hne : ∀ a : Anchor, (u.piles a).isEmpty = false)
    (hve : ∃ a : Anchor, (v.piles a).isEmpty = true)
    (hnotab : ∀ x b, m ≠ Move.tabToTab x b) :
    ∃ x : Card, ∃ a : Anchor, m = Move.tabToFound x ∧
      u.pileOfTop x = some a ∧ (v.piles a).isEmpty = true := by
  rcases empty_gain_step_is_raise_or_slide hstep hne hve with h | ⟨x, b, hm⟩
  · exact h
  · exact absurd hm (hnotab x b)

theorem emptying_raise_is_king {u v : State} {x : Card} {a : Anchor}
    (hstep : State.step u (Move.tabToFound x) = some v)
    (hrev : reversibleAtW u (Move.tabToFound x))
    (hpa : u.pileOfTop x = some a)
    (hempty : (v.piles a).isEmpty = true) :
    x.rank = Rank.king := by
  obtain ⟨hface, hhidden⟩ := (raise_empties_iff hstep hpa).mp hempty
  have hudonor : u.piles a = (⟨[], [x]⟩ : Pile) := by
    apply Pile.ext
    · exact hhidden
    · exact hface
  obtain ⟨hvhd, hvfu⟩ := (Pile.isEmpty_eq _).mp hempty
  have hvKing : kf_KingAnchor (v.piles a) := ⟨hvhd, Or.inl hvfu⟩
  obtain ⟨s1, play, hs1, hrun⟩ := hrev
  have hs1v : s1 = v := Option.some.inj (hs1.symm.trans hstep)
  subst s1
  have huKing : kf_KingAnchor (u.piles a) := kf_run_KingAnchor hrun hvKing
  obtain ⟨-, hfu⟩ := huKing
  rw [hface] at hfu
  rcases hfu with hnil | ⟨y, hy, hky⟩
  · simp at hnil
  · have hxy : x = y := Option.some.inj (by simpa using hy)
    rw [hxy]
    exact hky

end KingFuel

#print axioms KingFuel.raise_empties_iff
#print axioms KingFuel.pull_empties_iff
#print axioms KingFuel.empty_gain_step_is_raise_or_slide
#print axioms KingFuel.empty_gain_step_is_raise
#print axioms KingFuel.emptying_raise_is_king
