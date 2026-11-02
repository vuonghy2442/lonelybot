import Orig2.Fork.ForkNonfork

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-!
# R12 — the read-invariance induction for `NonforkKit.RaiseSwaps`

Scratch only.  No source touched, no commit.
-/

namespace R12

open NonforkKit
open ValleyElim

/-- If a state agrees with `st` on `nextUp z`, on the pile-top search of `z`,
and on the pile where `z` sits, then `CanRaise` transfers. -/
theorem canRaise_preserve_of_pile {st s' : State} {z : Card}
    (hnext : s'.nextUp z = st.nextUp z)
    (hfind : s'.pileOfTop z = st.pileOfTop z)
    (hpile : ∀ a, st.pileOfTop z = some a → s'.piles a = st.piles a)
    (h : CanRaise st z) : CanRaise s' z := by
  obtain ⟨hn, a, hpa, hseat⟩ := h
  exact ⟨by rw [hnext]; exact hn, a, by rw [hfind]; exact hpa, by
    rw [hpile a hpa]; exact hseat⟩

/-! ## §2. `CanRaise` survives a raise in another suit -/

theorem canRaise_survives_raise {st s' : State} {z w : Card}
    (hst : st.WF)
    (hstep : State.step st (Move.tabToFound w) = some s')
    (hsu : w.suit ≠ z.suit) (hzw : w ≠ z)
    (h : CanRaise st z) : CanRaise s' z := by
  obtain ⟨hnz, b, hpb, hseat⟩ := h
  obtain ⟨hnw, b', hpb', hs'⟩ := step_tabToFound_inv hstep
  have hs2 : s' = raiseSt st w b' := hs'
  have hbb' : b ≠ b' := by
    intro hb
    have hz1 : st.pileOfTop z = some b' := by rw [← hb]; exact hpb
    have t1 := (pileOfTop_top hz1).2
    have t2 := (pileOfTop_top hpb').2
    exact hzw (Option.some.inj (t1.symm.trans t2)).symm
  have hnext : s'.nextUp z = st.nextUp z := by
    rw [hs2]
    exact raiseSt_nextUp_ne hsu
  have hfind : s'.pileOfTop z = st.pileOfTop z := by
    rw [hs2, hpb]
    exact raiseSt_pileOfTop_ne hst hpb (Ne.symm hbb')
  have hpile : ∀ a, st.pileOfTop z = some a → s'.piles a = st.piles a := by
    intro a ha
    have hab : a ≠ b' := by
      intro hae
      rw [hae] at ha
      have hb'b : b' = b := Option.some.inj (ha.symm.trans hpb)
      exact hbb' hb'b.symm
    rw [hs2, raiseSt_piles_apply, ite_eq_right hab]
  exact canRaise_preserve_of_pile hnext hfind hpile ⟨hnz, b, hpb, hseat⟩

/-! ## §3. `CanRaise` survives a pull -/

theorem not_mem_pile_of_top_ne {st : State} (hst : st.WF) {z : Card} {a k : Anchor}
    (hpa : st.pileOfTop z = some a) (hak : a ≠ k) : z ∉ (st.piles k).faceUp := by
  have hz : z ∈ (st.piles a).faceUp :=
    lastOf_mem (pileOfTop_top hpa).2
  exact (mem_faceUp_unique hst hz k (Ne.symm hak)).1

theorem canRaise_survives_pull {st s' : State} {z c : Card} {b : Base}
    (hst : st.WF)
    (hstep : State.step st (Move.foundToTab c b) = some s')
    (hsu : c.suit ≠ z.suit) (hbz : b ≠ Sum.inr z)
    (h : CanRaise st z) : CanRaise s' z := by
  obtain ⟨hnz, a, hpa, hseat⟩ := h
  obtain ⟨c', htop, hc'c, hcp, hs⟩ := CommuteStep.step_foundToTab_pullSt hstep
  obtain ⟨kk, hk⟩ := CommuteStep.exists_tgt_of_canPlace hcp
  -- the target pile is not `z`'s pile
  have hka : a ≠ kk := by
    cases b with
    | inl j =>
        intro haj
        have hkj : kk = j := by
          have h1 : CommuteStep.tgt st (Sum.inl j) = some j := rfl
          rw [hk] at h1
          exact Option.some.inj h1
        have hemp := (canPlace_inl hcp).1
        have hz : z ∈ (st.piles a).faceUp :=
          lastOf_mem (pileOfTop_top hpa).2
        rw [haj, hkj] at hz
        obtain ⟨-, hface⟩ := (Pile.isEmpty_eq _).mp hemp
        rw [hface] at hz
        exact List.not_mem_nil hz
    | inr w =>
        intro haw
        obtain ⟨k, hkw, hfit⟩ := canPlace_inr hcp
        have hkk : kk = k := by
          have h1 : CommuteStep.tgt st (Sum.inr w) = some kk := hk
          simp only [CommuteStep.tgt_inr] at h1
          exact Option.some.inj (h1.symm.trans hkw)
        have htopw : (st.piles kk).top = some w := by
          rw [hkk]
          exact (pileOfTop_top hkw).2
        have htopz : (st.piles a).top = some z := (pileOfTop_top hpa).2
        rw [haw] at htopz
        have hwz : w = z := Option.some.inj (htopw.symm.trans htopz)
        exact hbz (by rw [hwz])
  have hpiles : s'.piles = (st.putCard c b).piles := by rw [hs, CommuteStep.pullSt_piles]
  have hfound : s'.found z.suit = st.found z.suit := by
    rw [hs, CommuteStep.pullSt_found_apply, ite_eq_right (Ne.symm hsu)]
  have hnext : s'.nextUp z = st.nextUp z := by
    unfold State.nextUp State.foundHeight
    rw [hfound]
  -- the written pile's new top is `c`, so it cannot be `z`
  have hnew : z ∉ (match b, hk with
      | Sum.inl val, hk => ({ hidden := [], faceUp := [c] } : Pile)
      | Sum.inr val, hk =>
        { hidden := (st.piles kk).hidden, faceUp := (st.piles kk).faceUp ++ [c] }).faceUp := by
    have hcz : c ≠ z := by intro hh; exact hsu (by rw [hh])
    cases b with
    | inl j =>
        intro hmem
        rw [List.mem_singleton] at hmem
        exact hcz hmem.symm
    | inr w =>
        intro hmem
        rw [List.mem_append] at hmem
        rcases hmem with hmem | hmem
        · exact not_mem_pile_of_top_ne hst hpa hka hmem
        · rw [List.mem_singleton] at hmem
          exact hcz hmem.symm
  have hold : z ∉ (st.piles kk).faceUp :=
    not_mem_pile_of_top_ne hst hpa hka
  have hcz : c ≠ z := by intro hh; exact hsu (by rw [hh])
  have hzmem : z ∈ (st.piles a).faceUp :=
    lastOf_mem (pileOfTop_top hpa).2
  have hfind : s'.pileOfTop z = st.pileOfTop z := by
    rw [CommuteStep.pileOfTop_congr_piles hpiles z, hpa]
    unfold State.pileOfTop State.topOf
    apply firstWhere_find (Anchor.mem_all a)
    · show decide (((st.putCard c b).piles a).top = some z) = true
      rw [CommuteStep.putCard_piles_ne (u := st) (c := c) (b := b) (k := kk) (a := a)
        hk hka]
      exact decide_eq_true (pileOfTop_top hpa).2
    · intro x hx hxa
      apply decide_false_of_not
      intro htop
      by_cases hxk : x = kk
      · subst hxk
        rw [CommuteStep.putCard_top_written hk] at htop
        exact hcz (Option.some.inj htop)
      · rw [CommuteStep.putCard_piles_ne hk hxk] at htop
        have hxmem : z ∈ (st.piles x).faceUp := Pile.mem_of_top htop
        exact (mem_faceUp_unique hst hzmem x hxa).1 hxmem
  have hpile : ∀ a', st.pileOfTop z = some a' → s'.piles a' = st.piles a' := by
    intro a' ha'
    have haa : a' = a := Option.some.inj (ha'.symm.trans hpa)
    rw [hpiles, CommuteStep.putCard_piles_ne hk (by rw [haa]; exact hka)]
  exact canRaise_preserve_of_pile hnext hfind hpile ⟨hnz, a, hpa, hseat⟩

/-! ## §3b. `CanRaise` survives a slide -/

theorem mem_fromCard_self {c : Card} : ∀ {l : List Card}, c ∈ l → c ∈ fromCard c l
  | [], h => absurd h (by simp)
  | x :: t, h => by
      by_cases hx : x = c
      · subst hx
        rw [tfc_fromCard_cons, ite_eq_left rfl]
        exact List.mem_cons_self ..
      · rw [tfc_fromCard_cons, ite_eq_right hx]
        exact mem_fromCard_self ((List.mem_cons.mp h).resolve_left (fun hh => hx hh.symm))

theorem canRaise_survives_slide {st s' : State} {z c : Card} {b : Base}
    (hst : st.WF)
    (hstep : State.step st (Move.tabToTab c b) = some s')
    (hrev : reversibleAtW st (Move.tabToTab c b))
    (hcz : c ≠ z) (hbz : b ≠ Sum.inr z)
    (h : CanRaise st z) : CanRaise s' z := by
  obtain ⟨hnz, a, hpa, hseat⟩ := h
  obtain ⟨a0, hhold0, hcp0, hrunv0, hs0⟩ := CommuteStep.step_tabToTab_slideSt hstep
  obtain ⟨aD, k, hholdD, hcpD, hk, hkne, hface, hrunvD, hcell⟩ :=
    CommuteStep.slide_data hst hrev
  have haD : aD = a0 := Option.some.inj (hholdD.symm.trans hhold0)
  have hcp : st.canPlace c b = true := hcpD
  have hs : s' = CommuteStep.slideSt st c b aD := hs0.trans (by rw [haD])
  -- `z`'s pile is not the target pile
  have hmk : a ≠ k := by
    intro hak
    cases b with
    | inl j =>
        have hkj : k = j := by
          have h1 : CommuteStep.tgt st (Sum.inl j) = some j := rfl
          rw [hk] at h1
          exact Option.some.inj h1
        have hemp := (canPlace_inl hcp).1
        have hz : z ∈ (st.piles a).faceUp :=
          lastOf_mem (pileOfTop_top hpa).2
        rw [hak, hkj] at hz
        obtain ⟨-, hfaceE⟩ := (Pile.isEmpty_eq _).mp hemp
        rw [hfaceE] at hz
        exact List.not_mem_nil hz
    | inr w =>
        have hkw : st.pileOfTop w = some k := by
          have h1 : CommuteStep.tgt st (Sum.inr w) = some k := hk
          simpa only [CommuteStep.tgt_inr] using h1
        have htopw : (st.piles k).top = some w := (pileOfTop_top hkw).2
        have htopz : (st.piles a).top = some z := (pileOfTop_top hpa).2
        rw [hak] at htopz
        have hwz : w = z := Option.some.inj (htopw.symm.trans htopz)
        exact hbz (by rw [hwz])
  have hnext : s'.nextUp z = st.nextUp z := by
    rw [hs]
    unfold State.nextUp State.foundHeight
    rw [CommuteStep.slideSt_found]
  by_cases hma : a = aD
  · -- the source pile is `z`'s pile: `z` rides to the target pile `k`
    have hpaD : st.pileOfTop z = some aD := by rw [← hma]; exact hpa
    have hzpile : (CommuteStep.slideSt st c b aD).pileOfTop z = some k :=
      CommuteStep.slideSt_pileOfTop_source hst hcp hk hkne hrunvD hcell hpaD
    have htarget : (CommuteStep.slideSt st c b aD).piles k =
        { st.piles k with faceUp := (st.piles k).faceUp ++ fromCard c (st.piles aD).faceUp } :=
      CommuteStep.slideSt_piles_target hst hcp hk hkne hcell
    -- the moved run ends at `z`, and contains `c`
    have hcmem : c ∈ (st.piles aD).faceUp := pileHolding_mem hholdD
    have hlastz : lastOf (st.piles aD).faceUp = some z := (pileOfTop_top hpaD).2
    have hrunends : lastOf (fromCard c (st.piles aD).faceUp) = some z := by
      have hsplit := CommuteStep.fromCard_eq_fromCard_chop_append (c := c) (w := z)
        hcmem hlastz hcz
      rw [hsplit, lastOf_snoc]
    have hcrun : c ∈ fromCard c (st.piles aD).faceUp := mem_fromCard_self hcmem
    have hnewmem : c ∈ ({ st.piles k with
        faceUp := (st.piles k).faceUp ++ fromCard c (st.piles aD).faceUp } : Pile).faceUp := by
      rw [List.mem_append]
      exact Or.inr hcrun
    have hnewlast : lastOf ({ st.piles k with
        faceUp := (st.piles k).faceUp ++ fromCard c (st.piles aD).faceUp } : Pile).faceUp = some z := by
      have := lastOf_chop hrunends
      rw [this]
      rw [← List.append_assoc]
      exact lastOf_snoc
    have hchopne : ({ st.piles k with
        faceUp := (st.piles k).faceUp ++ fromCard c (st.piles aD).faceUp } : Pile).faceUp ≠ [] :=
      List.ne_nil_of_mem hnewmem
    have hseat' : chop ((CommuteStep.slideSt st c b aD).piles k).faceUp ≠ [] := by
      rw [htarget]
      exact List.ne_nil_of_mem
        (CommuteStep.mem_chop_of_mem_of_ne_last hnewmem hnewlast hcz)
    refine ⟨by rw [hnext]; exact hnz, k, by rw [hs]; exact hzpile, ?_⟩
    rw [hs]
    exact Or.inl hseat'
  · -- `z`'s pile is neither source nor target: it is untouched
    have hzfind : (CommuteStep.slideSt st c b aD).pileOfTop z = some a :=
      CommuteStep.slideSt_pileOfTop_third hst hcp hk hkne hrunvD hcell hpa hma hmk
    have hpile : ∀ a', st.pileOfTop z = some a' →
        (CommuteStep.slideSt st c b aD).piles a' = st.piles a' := by
      intro a' ha'
      have haa : a' = a := Option.some.inj (ha'.symm.trans hpa)
      subst haa
      exact CommuteStep.slideSt_piles_other hst hcp hk hkne hcell hma hmk
    refine ⟨by rw [hnext]; exact hnz, a, by rw [hs]; exact hzfind, ?_⟩
    rw [hs, hpile a hpa]
    exact hseat

/-! ## §3c. Frames for the raise state -/

theorem foundTop_raiseSt_ne {st : State} {z c : Card} {a : Anchor}
    (hsu : c.suit ≠ z.suit) :
    (raiseSt st z a).foundTop c.suit = st.foundTop c.suit := by
  unfold State.foundTop
  rw [raiseSt_found_apply, ite_eq_right hsu]

theorem canPlace_raiseSt {st : State} {z c : Card} {a : Anchor} {b : Base}
    (hst : st.WF) (hpa : st.pileOfTop z = some a) (hbz : b ≠ Sum.inr z)
    (hcp : st.canPlace c b = true) :
    (raiseSt st z a).canPlace c b = st.canPlace c b := by
  cases b with
  | inl j =>
      have hemp := (canPlace_inl hcp).1
      have hz : z ∈ (st.piles a).faceUp :=
        lastOf_mem (pileOfTop_top hpa).2
      have hja : j ≠ a := by
        intro hja
        obtain ⟨-, hface⟩ := (Pile.isEmpty_eq _).mp hemp
        rw [hja] at hface
        rw [hface] at hz
        exact List.not_mem_nil hz
      rw [canPlace_inl_unfold, canPlace_inl_unfold]
      rw [raiseSt_piles_apply, ite_eq_right hja]
  | inr w =>
      obtain ⟨k, hkw, hfit⟩ := canPlace_inr hcp
      have hka : k ≠ a := by
        intro hka
        have htopw : (st.piles k).top = some w := (pileOfTop_top hkw).2
        have htopz : (st.piles a).top = some z := (pileOfTop_top hpa).2
        rw [hka] at htopw
        have hwz : w = z := Option.some.inj (htopw.symm.trans htopz)
        exact hbz (by rw [hwz])
      rw [canPlace_inr_eq, canPlace_inr_eq]
      rw [raiseSt_pileOfTop_ne hst hkw (Ne.symm hka), hkw]

theorem reversibleAtW_pull_after_raise {st : State} {z c : Card} {b : Base} {a : Anchor}
    (hst : st.WF) (hpa : st.pileOfTop z = some a) (hz : CanRaise st z)
    (hsu : c.suit ≠ z.suit) (hbz : b ≠ Sum.inr z)
    (hrev : reversibleAtW st (Move.foundToTab c b)) :
    reversibleAtW (raiseSt st z a) (Move.foundToTab c b) := by
  obtain ⟨s1, play, h1, hund⟩ := hrev
  obtain ⟨c', htop, hc'c, hcp, hs1⟩ := step_foundToTab_inv h1
  have hwfS : (raiseSt st z a).WF := by
    obtain ⟨v, hv⟩ := step_tabToFound_of_canRaise hz
    have hv' : st.step (Move.tabToFound z) = some (raiseSt st z a) := by
      obtain ⟨hnz, a', hpa', hseat'⟩ := hz
      have haa : a' = a := Option.some.inj (hpa'.symm.trans hpa)
      rw [haa] at hpa'
      rw [step_tabToFound_splice hnz hpa']
      rfl
    rw [hv'] at hv
    have hveq : raiseSt st z a = v := Option.some.inj hv
    subst hveq
    exact step_wf hst hv'
  have htop' : (raiseSt st z a).foundTop c.suit = some c := by
    rw [foundTop_raiseSt_ne (z := z) hsu]
    rw [hc'c] at htop
    exact htop
  have hcp' : (raiseSt st z a).canPlace c b = true := by
    rw [canPlace_raiseSt hst hpa hbz hcp]
    exact hcp
  have hR : foundToTabR (raiseSt st z a) c b = true := by
    unfold foundToTabR
    rw [htop']
    simp only [hcp']
    rfl
  exact (foundToTabR_iff_reversibleAtW hwfS c b).mp hR

/-! ## §3d. Slide-side frames -/

theorem pileHolding_raiseSt_self {st : State} {z c : Card} {a : Anchor}
    (hst : st.WF) (hpa : st.pileOfTop z = some a)
    (hcmem : c ∈ (st.piles a).faceUp) (hcz : c ≠ z) :
    (raiseSt st z a).pileHolding c = some a := by
  have hlastz : lastOf (st.piles a).faceUp = some z := (pileOfTop_top hpa).2
  have hcchop : c ∈ chop (st.piles a).faceUp :=
    CommuteStep.mem_chop_of_mem_of_ne_last hcmem hlastz hcz
  have hne : chop (st.piles a).faceUp ≠ [] := List.ne_nil_of_mem hcchop
  have hnew : (raiseSt st z a).piles a =
      { st.piles a with faceUp := chop (st.piles a).faceUp } := by
    rw [raiseSt_piles_apply, ite_eq_left rfl, afterRunRemoved_ne hne]
  refine tfc_pileHolding_pin ?_ ?_
  · rw [hnew]
    exact hcchop
  · intro j hj
    rw [raiseSt_piles_apply]
    intro hmem
    by_cases hja : j = a
    · exact absurd hja hj
    · rw [ite_eq_right hja] at hmem
      exact (mem_faceUp_unique hst hcmem j hja).1 hmem

theorem below_raiseSt_source {st : State} {z c : Card} {a : Anchor}
    (hpa : st.pileOfTop z = some a)
    (hcmem : c ∈ (st.piles a).faceUp) (hcz : c ≠ z) :
    below c ((raiseSt st z a).piles a).faceUp = below c (st.piles a).faceUp := by
  have hlastz : lastOf (st.piles a).faceUp = some z := (pileOfTop_top hpa).2
  have hcchop : c ∈ chop (st.piles a).faceUp :=
    CommuteStep.mem_chop_of_mem_of_ne_last hcmem hlastz hcz
  have hne : chop (st.piles a).faceUp ≠ [] := List.ne_nil_of_mem hcchop
  rw [raiseSt_piles_apply, ite_eq_left rfl, afterRunRemoved_ne hne]
  exact (CommuteStep.below_eq_below_chop hcmem hlastz hcz).symm

theorem hidden_raiseSt_source {st : State} {z c : Card} {a : Anchor}
    (hpa : st.pileOfTop z = some a)
    (hcmem : c ∈ (st.piles a).faceUp) (hcz : c ≠ z) :
    ((raiseSt st z a).piles a).hidden = (st.piles a).hidden := by
  have hlastz : lastOf (st.piles a).faceUp = some z := (pileOfTop_top hpa).2
  have hcchop : c ∈ chop (st.piles a).faceUp :=
    CommuteStep.mem_chop_of_mem_of_ne_last hcmem hlastz hcz
  have hne : chop (st.piles a).faceUp ≠ [] := List.ne_nil_of_mem hcchop
  rw [raiseSt_piles_apply, ite_eq_left rfl, afterRunRemoved_ne hne]

theorem tabToTabR_true_of {s : State} {c : Card} {b : Base} {ac : Anchor}
    (hhold : s.pileHolding c = some ac) (hcp : s.canPlace c b = true)
    (hcell : below c (s.piles ac).faceUp ≠ [] ∨
      below c (s.piles ac).faceUp = [] ∧ (s.piles ac).hidden = [] ∧ c.rank = Rank.king) :
    tabToTabR s c b = true := by
  unfold tabToTabR
  rw [hhold, hcp]
  change (match below c (s.piles ac).faceUp with
    | [] => match (s.piles ac).hidden with
      | [] => decide (c.rank = Rank.king)
      | _ :: _ => false
    | _ :: _ => true) = true
  rcases hcell with hb | ⟨hb, hhid, hking⟩
  · cases hbl : below c (s.piles ac).faceUp with
    | nil => exact absurd hbl hb
    | cons x xs => rfl
  · rw [hb, hhid]
    exact decide_eq_true hking

theorem reversibleAtW_slide_after_raise {st : State} {z c : Card} {b : Base} {a : Anchor}
    (hst : st.WF) (hpa : st.pileOfTop z = some a) (hz : CanRaise st z)
    (hcz : c ≠ z) (hbz : b ≠ Sum.inr z)
    (hrev : reversibleAtW st (Move.tabToTab c b)) :
    reversibleAtW (raiseSt st z a) (Move.tabToTab c b) := by
  obtain ⟨ac, k, hhold, hcp, hk, hkne, hface, hrunv, hcell⟩ :=
    CommuteStep.slide_data hst hrev
  have hwfS : (raiseSt st z a).WF := by
    obtain ⟨v, hv⟩ := step_tabToFound_of_canRaise hz
    have hv' : st.step (Move.tabToFound z) = some (raiseSt st z a) := by
      obtain ⟨hnz, a', hpa', hseat'⟩ := hz
      have haa : a' = a := Option.some.inj (hpa'.symm.trans hpa)
      rw [haa] at hpa'
      rw [step_tabToFound_splice hnz hpa']
      rfl
    rw [hv'] at hv
    have hveq : raiseSt st z a = v := Option.some.inj hv
    subst hveq
    exact step_wf hst hv'
  have hcmem : c ∈ (st.piles ac).faceUp := pileHolding_mem hhold
  have hhold' : (raiseSt st z a).pileHolding c = some ac := by
    by_cases hac : ac = a
    · subst hac
      exact pileHolding_raiseSt_self hst hpa hcmem hcz
    · exact CommuteStep.pileHolding_raiseSt_ne hst hpa hcmem hac
  have hcp' : (raiseSt st z a).canPlace c b = true := by
    rw [canPlace_raiseSt hst hpa hbz hcp]
    exact hcp
  have hbelow' : below c ((raiseSt st z a).piles ac).faceUp =
      below c (st.piles ac).faceUp := by
    by_cases hac : ac = a
    · subst hac
      exact below_raiseSt_source hpa hcmem hcz
    · rw [raiseSt_piles_apply, ite_eq_right hac]
  have hhidden' : ((raiseSt st z a).piles ac).hidden = (st.piles ac).hidden := by
    by_cases hac : ac = a
    · subst hac
      exact hidden_raiseSt_source hpa hcmem hcz
    · rw [raiseSt_piles_apply, ite_eq_right hac]
  have hking : below c (st.piles ac).faceUp = [] → (st.piles ac).hidden = [] →
      c.rank = Rank.king := by
    intro hb hhid
    have hRold : tabToTabR st c b = true :=
      (tabToTabR_iff_reversibleAtW hst c b).mpr hrev
    unfold tabToTabR at hRold
    rw [hhold, hcp] at hRold
    change (match below c (st.piles ac).faceUp with
      | [] => match (st.piles ac).hidden with
        | [] => decide (c.rank = Rank.king)
        | _ :: _ => false
      | _ :: _ => true) = true at hRold
    rw [hb, hhid] at hRold
    exact of_decide_eq_true hRold
  have hcell' : below c ((raiseSt st z a).piles ac).faceUp ≠ [] ∨
      below c ((raiseSt st z a).piles ac).faceUp = [] ∧
        ((raiseSt st z a).piles ac).hidden = [] ∧ c.rank = Rank.king := by
    rcases hcell with hb | ⟨hb, hhid⟩
    · left
      rw [hbelow']
      exact hb
    · right
      refine ⟨?_, ?_, ?_⟩
      · rw [hbelow', hb]
      · rw [hhidden', hhid]
      · exact hking hb hhid
  exact (tabToTabR_iff_reversibleAtW hwfS c b).mp
    (tabToTabR_true_of hhold' hcp' hcell')

/-! ## §4. `CanRaise` survives a draw -/

theorem canRaise_survives_draw {st s' : State} {z : Card}
    (hstep : State.step st Move.draw = some s') (h : CanRaise st z) :
    CanRaise s' z := by
  have hf : s'.found = st.found := stepDraw_found hstep
  have hp : s'.piles = st.piles := stepDraw_piles hstep
  exact canRaise_preserve_of_pile
    (by unfold State.nextUp State.foundHeight; rw [hf])
    (by unfold State.pileOfTop State.topOf; rw [hp])
    (fun a _ => by rw [hp]) h

/-! ## §5. The local swap lemmas (the per-letter certificate) -/

theorem drawR_raiseSt (u : State) (z : Card) (a : Anchor) :
    drawR (raiseSt u z a) = drawR u := by
  unfold drawR
  rw [raiseSt_stock, raiseSt_waste, raiseSt_drawStep]

theorem reversibleAtW_draw_after_raise {u : State} {z : Card} {a : Anchor}
    (hu : u.WF) (hpa : u.pileOfTop z = some a) (hz : CanRaise u z)
    (hrev : reversibleAtW u Move.draw) :
    reversibleAtW (raiseSt u z a) Move.draw := by
  have hRwf : (raiseSt u z a).WF := by
    obtain ⟨hnz, a', hpa', hseat'⟩ := hz
    have haa : a' = a := Option.some.inj (hpa'.symm.trans hpa)
    rw [haa] at hpa'
    have hv' : u.step (Move.tabToFound z) = some (raiseSt u z a) := by
      rw [step_tabToFound_splice hnz hpa']
      rfl
    exact step_wf hu hv'
  have hRtrue : drawR (raiseSt u z a) = true := by
    rw [drawR_raiseSt]
    exact (drawR_iff_reversibleAtW hu).mpr hrev
  exact (drawR_iff_reversibleAtW hRwf).mp hRtrue

theorem raise_swap_draw {mid : State} {z : Card}
    (hmid : mid.WF) (hcan : CanRaise mid z)
    (hrev : reversibleAtW mid Move.draw) :
    ∃ e, ShufflePlayW mid [Move.tabToFound z, Move.draw] e ∧
         mid.run [Move.draw, Move.tabToFound z] = some e := by
  obtain ⟨hnz, a, hpa, hseat⟩ := hcan
  have hcan' : CanRaise mid z := ⟨hnz, a, hpa, hseat⟩
  have hrevR : reversibleAtW mid (Move.tabToFound z) :=
    DrainClose.reversibleAtW_tabToFound_of_canRaise hmid hcan'
  have hrevKeep : reversibleAtW mid Move.draw := hrev
  obtain ⟨s1, play, hdraw, hund⟩ := hrev
  have hcanAfter : CanRaise s1 z := canRaise_survives_draw hdraw hcan'
  obtain ⟨s12, hstep12⟩ := step_tabToFound_of_canRaise hcanAfter
  have hstepR : State.step mid (Move.tabToFound z) = some (raiseSt mid z a) := by
    rw [step_tabToFound_splice hnz hpa]
    rfl
  have hrevDrawR : reversibleAtW (raiseSt mid z a) Move.draw :=
    reversibleAtW_draw_after_raise hmid hpa hcan' hrevKeep
  have hrevDrawR' : reversibleAtW (raiseSt mid z a) Move.draw := hrevDrawR
  obtain ⟨s21, p21, hstep21, hund21⟩ := hrevDrawR
  have hsq : s12 = s21 :=
    CommuteStep.step_comm_draw_raise hmid hrevKeep hrevR hdraw hstepR hstep12 hstep21
  refine ⟨s21, Walk.cons hrevR hstepR
    (Walk.cons hrevDrawR' hstep21 (Walk.nil s21)), ?_⟩
  simp only [State.run, hdraw, hstep12, hsq]

theorem raise_swap_pull {mid : State} {z c : Card} {b : Base}
    (hmid : mid.WF) (hcan : CanRaise mid z)
    (hsu : c.suit ≠ z.suit) (hbz : b ≠ Sum.inr z)
    (hrev : reversibleAtW mid (Move.foundToTab c b)) :
    ∃ e, ShufflePlayW mid [Move.tabToFound z, Move.foundToTab c b] e ∧
         mid.run [Move.foundToTab c b, Move.tabToFound z] = some e := by
  obtain ⟨hnz, a, hpa, hseat⟩ := hcan
  have hcan' : CanRaise mid z := ⟨hnz, a, hpa, hseat⟩
  have hrevR : reversibleAtW mid (Move.tabToFound z) :=
    DrainClose.reversibleAtW_tabToFound_of_canRaise hmid hcan'
  have hrevKeep : reversibleAtW mid (Move.foundToTab c b) := hrev
  obtain ⟨s1, play, hpull, hund⟩ := hrev
  have hcanAfter : CanRaise s1 z :=
    canRaise_survives_pull hmid hpull hsu hbz hcan'
  obtain ⟨s12, hstep12⟩ := step_tabToFound_of_canRaise hcanAfter
  have hstepR : State.step mid (Move.tabToFound z) = some (raiseSt mid z a) := by
    rw [step_tabToFound_splice hnz hpa]
    rfl
  have hrevPullR : reversibleAtW (raiseSt mid z a) (Move.foundToTab c b) :=
    reversibleAtW_pull_after_raise hmid hpa hcan' hsu hbz hrevKeep
  have hrevPullR' : reversibleAtW (raiseSt mid z a) (Move.foundToTab c b) := hrevPullR
  obtain ⟨s21, p21, hstep21, hund21⟩ := hrevPullR
  have hsq : s12 = s21 :=
    CommuteStep.step_comm_pull_raise hmid hrevKeep hrevR hpull hstepR hstep12 hstep21
  refine ⟨s21, Walk.cons hrevR hstepR
    (Walk.cons hrevPullR' hstep21 (Walk.nil s21)), ?_⟩
  simp only [State.run, hpull, hstep12, hsq]

theorem raise_swap_slide {mid : State} {z c : Card} {b : Base}
    (hmid : mid.WF) (hcan : CanRaise mid z)
    (hcz : c ≠ z) (hbz : b ≠ Sum.inr z)
    (hrev : reversibleAtW mid (Move.tabToTab c b)) :
    ∃ e, ShufflePlayW mid [Move.tabToFound z, Move.tabToTab c b] e ∧
         mid.run [Move.tabToTab c b, Move.tabToFound z] = some e := by
  obtain ⟨hnz, a, hpa, hseat⟩ := hcan
  have hcan' : CanRaise mid z := ⟨hnz, a, hpa, hseat⟩
  have hrevR : reversibleAtW mid (Move.tabToFound z) :=
    DrainClose.reversibleAtW_tabToFound_of_canRaise hmid hcan'
  have hrevKeep : reversibleAtW mid (Move.tabToTab c b) := hrev
  obtain ⟨s1, play, hslide, hund⟩ := hrev
  have hcanAfter : CanRaise s1 z :=
    canRaise_survives_slide hmid hslide hrevKeep hcz hbz hcan'
  obtain ⟨s12, hstep12⟩ := step_tabToFound_of_canRaise hcanAfter
  have hstepR : State.step mid (Move.tabToFound z) = some (raiseSt mid z a) := by
    rw [step_tabToFound_splice hnz hpa]
    rfl
  have hrevSlideR : reversibleAtW (raiseSt mid z a) (Move.tabToTab c b) :=
    reversibleAtW_slide_after_raise hmid hpa hcan' hcz hbz hrevKeep
  have hrevSlideR' : reversibleAtW (raiseSt mid z a) (Move.tabToTab c b) := hrevSlideR
  obtain ⟨s21, p21, hstep21, hund21⟩ := hrevSlideR
  have hsq : s12 = s21 :=
    CommuteStep.step_comm_slide_raise hmid hrevKeep hrevR hslide hstepR hstep12 hstep21
  refine ⟨s21, Walk.cons hrevR hstepR
    (Walk.cons hrevSlideR' hstep21 (Walk.nil s21)), ?_⟩
  simp only [State.run, hslide, hstep12, hsq]

/-! ## §6. The syntactic read-invariance predicate -/

/-- A letter is *read-safe* for the pending raise of `z`: it is not a
pull/raise in `z`'s suit, it does not land on `z`, and it is not a slide
whose moving head is `z` itself. -/
def ReadOK (z : Card) (q : Move) : Prop :=
  match q with
  | Move.draw => True
  | Move.wasteToFound _ => False
  | Move.wasteToTab _ _ => False
  | Move.tabToFound w => w.suit ≠ z.suit
  | Move.foundToTab c b => c.suit ≠ z.suit ∧ b ≠ Sum.inr z
  | Move.tabToTab c b => c ≠ z ∧ b ≠ Sum.inr z

theorem readOK_raise_of_ne {z w : Card} (h : w.suit ≠ z.suit) :
    ReadOK z (Move.tabToFound w) := h

theorem readOK_pull_of_ne {z c : Card} {b : Base}
    (hsu : c.suit ≠ z.suit) (hbz : b ≠ Sum.inr z) :
    ReadOK z (Move.foundToTab c b) := ⟨hsu, hbz⟩

theorem readOK_slide_of_ne {z c : Card} {b : Base}
    (hcz : c ≠ z) (hbz : b ≠ Sum.inr z) :
    ReadOK z (Move.tabToTab c b) := ⟨hcz, hbz⟩

theorem readOK_draw (z : Card) : ReadOK z Move.draw := trivial

theorem local_swap_of_read {st : State} {z : Card} {q : Move}
    (hst : st.WF) (hcan : CanRaise st z)
    (hrev : reversibleAtW st q) (hread : ReadOK z q) :
    ∃ e, ShufflePlayW st [Move.tabToFound z, q] e ∧
         st.run [q, Move.tabToFound z] = some e := by
  cases q with
  | draw => exact raise_swap_draw hst hcan hrev
  | wasteToFound c => exact absurd hread (by simp [ReadOK])
  | wasteToTab c b => exact absurd hread (by simp [ReadOK])
  | tabToFound w =>
      have hcw : CanRaise st w := Bridge.canRaise_of_reversible_raise hst hrev
      exact raise_swap_raise hst hcan hcw (Ne.symm hread)
  | foundToTab c b =>
      exact raise_swap_pull hst hcan hread.1 hread.2 hrev
  | tabToTab c b =>
      exact raise_swap_slide hst hcan hread.1 hread.2 hrev

theorem canRaise_survives_read {st s' : State} {z : Card} {q : Move}
    (hst : st.WF) (hstep : State.step st q = some s')
    (hrev : reversibleAtW st q)
    (hread : ReadOK z q) (h : CanRaise st z) : CanRaise s' z := by
  cases q with
  | draw => exact canRaise_survives_draw hstep h
  | wasteToFound c => exact absurd hread (by simp [ReadOK])
  | wasteToTab c b => exact absurd hread (by simp [ReadOK])
  | tabToFound w =>
      exact canRaise_survives_raise hst hstep hread
        (fun hwz => hread (by rw [hwz])) h
  | foundToTab c b =>
      exact canRaise_survives_pull hst hstep hread.1 hread.2 h
  | tabToTab c b =>
      exact canRaise_survives_slide hst hstep hrev hread.1 hread.2 h

/-! ## §7. The arbitrary-length induction -/

theorem raiseSwaps_cons {Q R : State} {z : Card} {q : Move} {γ : List Move}
    (hstep : State.step Q q = some R)
    (hhead : ∃ e, ShufflePlayW Q [Move.tabToFound z, q] e ∧
      Q.run [q, Move.tabToFound z] = some e)
    (hrest : RaiseSwaps R z γ) : RaiseSwaps Q z (q :: γ) := by
  intro pre mid q' rest hsplit hpre
  cases pre with
  | nil =>
      simp only [List.nil_append] at hsplit
      injection hsplit with hq htail
      subst hq
      subst htail
      have hmid : mid = Q := by
        have h := Walk_run _ hpre
        simp only [State.run] at h
        exact (Option.some.inj h).symm
      subst hmid
      exact hhead
  | cons a as =>
      have hcons : a :: (as ++ q' :: rest) = q :: γ := by
        simpa only [List.cons_append] using hsplit
      have haq : a = q := (List.cons.inj hcons).1
      have htail : as ++ q' :: rest = γ := (List.cons.inj hcons).2
      obtain ⟨s1, hrev_a, hstep_a, hpre'⟩ := Bubble.walk_cons_inv hpre
      rw [haq] at hstep_a
      have hs1 : s1 = R := Option.some.inj (hstep_a.symm.trans hstep)
      subst hs1
      exact hrest as mid q' rest htail hpre'

theorem raiseSwaps_of_read {Q v : State} {z : Card} {γ β : List Move}
    (hQwf : Q.WF)
    (hplay : ShufflePlayW Q (γ ++ Move.tabToFound z :: β) v)
    (hcan : CanRaise Q z)
    (hread : ∀ q ∈ γ, ReadOK z q) : RaiseSwaps Q z γ := by
  induction γ generalizing Q v β with
  | nil => exact raiseSwaps_nil Q z
  | cons q γ' ih =>
      rw [List.cons_append] at hplay
      obtain ⟨R, hrevq, hstepq, hplayR⟩ := Bubble.walk_cons_inv hplay
      have hreadq : ReadOK z q := hread q (List.mem_cons_self ..)
      have hcanR : CanRaise R z :=
        canRaise_survives_read hQwf hstepq hrevq hreadq hcan
      have hhead := local_swap_of_read hQwf hcan hrevq hreadq
      have hrest : RaiseSwaps R z γ' :=
        ih (step_wf hQwf hstepq) hplayR hcanR
          (fun x hx => hread x (List.mem_cons_of_mem q hx))
      exact raiseSwaps_cons hstepq hhead hrest

/-! ## §8. The bracket-level residual and its reduction -/

/-- **`ReadBracketElim` — WITHDRAWN, FALSE AS STATED.**  The ungated
quantifier includes witness LOOPS; the four-letter loop
(`pull 5H -> 6C ; slide 4C -> 5H ; slide 4C -> 5D ; raise 5H`) refutes it
(kernel-checked by `ExistRefute.not_readBracketElim`).  The minimality-gated
form is `ExistKit.ReadBracketElimMin`, equivalent to
`ExistKit.ValleyForkAtMin` (every minimal valley bottom is a fork). -/
def ReadBracketElim : Prop :=
  ∀ (u v : State) (ρ : List Move) (F : State),
    u.WF → SSaturated u → SSaturated v →
    ShufflePlayW u ρ v →
    ValleySplitAt u v ρ F →
    (∃ x : Card, ForkWitness F x) ∨
    (∃ (α γ β : List Move) (z : Card) (bz : Base) (P Q : State),
      ρ = α ++ Move.foundToTab z bz :: γ ++ Move.tabToFound z :: β ∧
      ShufflePlayW u α P ∧
      State.step P (Move.foundToTab z bz) = some Q ∧
      CanRaise Q z ∧
      (∀ q ∈ γ, ReadOK z q))

/-- The play from the bracket's pull landing, recovered from the bracket
decomposition. -/
theorem bracket_landing_play {u v : State} {ρ α γ β : List Move}
    {z : Card} {bz : Base} {P Q : State}
    (hplay : ShufflePlayW u ρ v)
    (hρ : ρ = α ++ Move.foundToTab z bz :: γ ++ Move.tabToFound z :: β)
    (hα : ShufflePlayW u α P)
    (hstep : State.step P (Move.foundToTab z bz) = some Q) :
    ShufflePlayW Q (γ ++ Move.tabToFound z :: β) v := by
  have hρ' : ρ = (α ++ [Move.foundToTab z bz]) ++
      (γ ++ Move.tabToFound z :: β) := by
    rw [hρ]; simp only [List.cons_append, List.append_assoc, List.nil_append]
  obtain ⟨Q', hplay1, hplay2⟩ := ShufflePlayW_split hplay _ _ hρ'
  obtain ⟨P1, hpre1, hlast1⟩ := ShufflePlayW_split hplay1 α [Move.foundToTab z bz] rfl
  have hstep1 : State.step P1 (Move.foundToTab z bz) = some Q' :=
    Elim.step_of_singleton hlast1
  have hP : P1 = P := by
    have h1 := Walk_run (fun st m => reversibleAtW st m) hpre1
    have h2 := Walk_run (fun st m => reversibleAtW st m) hα
    exact Option.some.inj (h1.symm.trans h2)
  subst hP
  have hQ : Q' = Q := Option.some.inj (hstep1.symm.trans hstep)
  subst hQ
  exact hplay2

/-- **READ-SAFE BRACKET IMPLIES THE LOCAL RESIDUAL.** -/
theorem nonforkBracketLocal_of_readBracket (h : ReadBracketElim) :
    NonforkBracketLocal := by
  intro u v ρ F huwf hsu hsv hplay hsplit
  rcases h u v ρ F huwf hsu hsv hplay hsplit with
    hf | ⟨α, γ, β, z, bz, P, Q, hρ, hα, hstep, hcan, hread⟩
  · exact Or.inl hf
  · have hPwf : P.WF := SatDifferCensus.ShufflePlayW.wf_end hα huwf
    have hQwf : Q.WF := step_wf hPwf hstep
    have hplayQ : ShufflePlayW Q (γ ++ Move.tabToFound z :: β) v :=
      bracket_landing_play hplay hρ hα hstep
    exact Or.inr ⟨α, γ, β, z, bz, P, Q, hρ, hα, hstep,
      raiseSwaps_of_read hQwf hplayQ hcan hread⟩

/-- **THE CAMPAIGN REDUCTION FROM THE READ-SAFE BRACKET RESIDUAL.** -/
theorem valleyElimNonfork_of_readBracket (h : ReadBracketElim) :
    ValleyElimNonfork :=
  NonforkKit.valleyElimNonfork_of_local (nonforkBracketLocal_of_readBracket h)

/-! ### The third syntactic condition is forced, not assumed

`ReadOK` also forbids a slide whose moving head is `z`.  This is not an extra
geometric assumption: a `RaiseSwaps` certificate can never contain such a
letter, because after `raise z` fires, `z` is on the foundation and is no
longer a pile-held card, so the slide is illegal. -/

theorem no_slide_self_at {Q : State} {z : Card} {b : Base}
    (hQwf : Q.WF) :
    ¬ ∃ e, ShufflePlayW Q [Move.tabToFound z, Move.tabToTab z b] e := by
  rintro ⟨e, h⟩
  obtain ⟨s1, hrevR, hstepR, hrest⟩ := Bubble.walk_cons_inv h
  obtain ⟨e', hrevS, hstepS, _⟩ := Bubble.walk_cons_inv hrest
  obtain ⟨hnz, a, hpa, hseat⟩ :=
    Bridge.canRaise_of_reversible_raise hQwf hrevR
  have hsp : Q.step (Move.tabToFound z) = some (raiseSt Q z a) := by
    rw [step_tabToFound_splice hnz hpa]
    rfl
  have hs1 : s1 = raiseSt Q z a := Option.some.inj (hstepR.symm.trans hsp)
  subst hs1
  have hwf1 : (raiseSt Q z a).WF := step_wf hQwf hsp
  have hzfound : z ∈ (raiseSt Q z a).found z.suit := by
    rw [raiseSt_found_apply, ite_eq_left rfl]
    exact List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl))
  have hznot : ∀ a' : Anchor, z ∉ ((raiseSt Q z a).piles a').faceUp :=
    fun a' => ((mem_found_unique hwf1 hzfound).1 a').2
  have hhold : (raiseSt Q z a).pileHolding z = none := by
    cases hh : (raiseSt Q z a).pileHolding z with
    | none => rfl
    | some a' =>
        exact absurd (pileHolding_mem hh) (hznot a')
  have hnone : State.step (raiseSt Q z a) (Move.tabToTab z b) = none := by
    simp only [State.step, hhold]
  rw [hnone] at hstepS
  exact absurd hstepS (by simp)

theorem slide_self_not_mem_of_raiseSwaps {Q mid : State} {z : Card} {γ : List Move}
    {pre : List Move} {b : Base} {rest : List Move}
    (hQwf : Q.WF) (hsw : RaiseSwaps Q z γ)
    (hsplit : γ = pre ++ Move.tabToTab z b :: rest)
    (hpre : ShufflePlayW Q pre mid) : False := by
  obtain ⟨e, hplay, hrun⟩ := hsw pre mid (Move.tabToTab z b) rest hsplit.symm hpre
  exact no_slide_self_at (SatDifferCensus.ShufflePlayW.wf_end hpre hQwf) ⟨e, hplay⟩

/-! ### R1 / R2 as instances of the same induction

The two census families differ only in which same-card pair is used; both are
instances of `raiseSwaps_of_read`.  `R1` is the valley pull card's own pair and
`R2` the enclosing raise card's pair.  We state each with its exact bracket
decomposition. -/

/-- **R1 — the valley pull card's own bracket (`z = c`).**  Given the bracket
`pull c ; γ ; raise c` and the per-letter `ReadOK c` conditions, the
`RaiseSwaps` certificate is produced by the induction. -/
theorem R1_raiseSwaps {Q v : State} {c : Card} {γ β : List Move}
    (hQwf : Q.WF) (hcan : CanRaise Q c)
    (hplay : ShufflePlayW Q (γ ++ Move.tabToFound c :: β) v)
    (hread : ∀ q ∈ γ, ReadOK c q) :
    RaiseSwaps Q c γ :=
  raiseSwaps_of_read hQwf hplay hcan hread

/-- **R2 — the enclosing raise card's bracket (`z = d`).**  The interior may
contain slides (W2's `pull 3D ; slide 2S→3D`); the slide branch of
`ReadOK`/`reversibleAtW_slide_after_raise` is what admits it. -/
theorem R2_raiseSwaps {Q v : State} {d : Card} {γ β : List Move}
    (hQwf : Q.WF) (hcan : CanRaise Q d)
    (hplay : ShufflePlayW Q (γ ++ Move.tabToFound d :: β) v)
    (hread : ∀ q ∈ γ, ReadOK d q) :
    RaiseSwaps Q d γ :=
  raiseSwaps_of_read hQwf hplay hcan hread

end R12

#print axioms R12.canRaise_preserve_of_pile
#print axioms R12.canRaise_survives_raise
#print axioms R12.canRaise_survives_pull
#print axioms R12.canRaise_survives_slide
#print axioms R12.canRaise_survives_draw
#print axioms R12.reversibleAtW_pull_after_raise
#print axioms R12.reversibleAtW_slide_after_raise
#print axioms R12.reversibleAtW_draw_after_raise
#print axioms R12.raise_swap_draw
#print axioms R12.raise_swap_pull
#print axioms R12.raise_swap_slide
#print axioms R12.canRaise_survives_read
#print axioms R12.local_swap_of_read
#print axioms R12.raiseSwaps_cons
#print axioms R12.raiseSwaps_of_read
#print axioms R12.bracket_landing_play
#print axioms R12.nonforkBracketLocal_of_readBracket
#print axioms R12.valleyElimNonfork_of_readBracket
#print axioms R12.R1_raiseSwaps
#print axioms R12.R2_raiseSwaps
#print axioms R12.no_slide_self_at
#print axioms R12.slide_self_not_mem_of_raiseSwaps
