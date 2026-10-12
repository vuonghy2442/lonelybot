import Orig.ForkStateUniqGate

/-! # Orig.RunOrTwin — the run-or-twin necessity, isolated import -/

/-! ## §0. The private kit -/

private theorem fromCard_eq_nil_of_not_mem (t : Card) :
    ∀ (l : List Card), t ∉ l → fromCard t l = []
  | [], _ => rfl
  | x :: xs, h => by
      have hxt : x ≠ t := by
        intro hc
        exact h (by rw [hc]; exact List.mem_cons_self ..)
      rw [fromCard_cons_ne xs hxt]
      exact fromCard_eq_nil_of_not_mem t xs (fun hm => h (List.mem_cons_of_mem _ hm))

private theorem lastOf_cons_ne {w : Card} {L : List Card} (h : L ≠ []) :
    lastOf (w :: L) = lastOf L := by
  cases L with
  | nil => exact absurd rfl h
  | cons y t => rfl

private theorem lastOf_append_nonempty {t : List Card} (ht : t ≠ []) :
    ∀ (bs : List Card), lastOf (bs ++ t) = lastOf t := by
  intro bs
  induction bs with
  | nil => rfl
  | cons w ws ih =>
      have hne : ws ++ t ≠ [] := by
        intro hcon
        apply ht
        cases ws with
        | nil => rw [List.nil_append] at hcon; exact hcon
        | cons v vs => exact absurd hcon (by simp)
      rw [List.cons_append, lastOf_cons_ne hne, ih]

private theorem afterRunRemoved_faceUp_barred {p : Pile} {pre : List Card}
    (hbar : pre = [] → p.hidden = []) :
    (Pile.afterRunRemoved p pre).faceUp = pre := by
  cases pre with
  | nil =>
      cases p with
      | mk hs fs =>
          have hh : hs = [] := hbar rfl
          subst hh
          rfl
  | cons u us =>
      rw [afterRunRemoved_ne (by simp)]

private theorem color_pair {a u v : Color} (h1 : a ≠ u) (h2 : a ≠ v) : u = v := by
  rcases a <;> rcases u <;> rcases v <;> simp_all

private theorem rankColor_pair {c z : Card}
    (hr : z.rank.toIdx = c.rank.toIdx) (hc : z.suit.color = c.suit.color) :
    z = c ∨ z = c.twin := by
  rcases z with ⟨zs, zr⟩
  rcases c with ⟨cs, cr⟩
  have hrank : zr = cr := Rank.toIdx_inj hr
  subst hrank
  cases cs <;> cases zs <;> simp_all [Suit.color, Suit.twin, Card.twin]

private theorem runOK_adjacent_fit (c d : Card) :
    ∀ (X R : List Card), runOK (X ++ c :: d :: R) = true → canSitOn d c := by
  intro X
  induction X with
  | nil =>
      intro R h
      have h2 : runOK (c :: d :: R) = true := h
      rw [runOK, Bool.and_eq_true] at h2
      exact h2.1
  | cons w ws ih =>
      intro R h
      have h2 : runOK (w :: (ws ++ c :: d :: R)) = true := h
      cases hxs : (ws ++ c :: d :: R) with
      | nil =>
          cases ws with
          | nil => rw [List.nil_append] at hxs; exact absurd hxs (by simp)
          | cons v vs => rw [List.cons_append] at hxs; exact absurd hxs (by simp)
      | cons y ys =>
          rw [hxs] at h2
          rw [runOK, Bool.and_eq_true] at h2
          have htail : runOK (ws ++ c :: d :: R) = true := by
            rw [hxs]
            exact h2.2
          exact ih R htail

private theorem inl_gate_kill {x e : Card} (hking : e.rank = Rank.king)
    (hfitx : canSitOn e x = true) : False := by
  obtain ⟨hr, -⟩ := (canSitOn_eq e x).mp hfitx
  rw [hking] at hr
  have hk12 : Rank.king.toIdx = 12 := rfl
  have hlt := Rank.toIdx_lt x.rank
  omega

private theorem inr_gate_kill {s : State} {x e z : Card} {k : Anchor}
    (hfitz : canSitOn e z = true)
    (hz : s.pileOfTop z = some k)
    (hx : s.pileOfTop x = none) (hxt : s.pileOfTop x.twin = none)
    (hfitx : canSitOn e x = true) : False := by
  obtain ⟨hr1, hc1⟩ := (canSitOn_eq e x).mp hfitx
  obtain ⟨hr2, hc2⟩ := (canSitOn_eq e z).mp hfitz
  have hcol : z.suit.color = x.suit.color :=
    (color_pair (a := e.suit.color) hc1 hc2).symm
  rcases rankColor_pair (c := x) (by omega) hcol with hzx | hzx
  · rw [hzx] at hz
    rw [hz] at hx
    exact absurd hx (by simp)
  · rw [hzx] at hz
    rw [hz] at hxt
    exact absurd hxt (by simp)

private theorem uncover_kill {x e : Card} {init rest : List Card}
    (hok : runOK ((init ++ [x]) ++ e :: rest) = true)
    (hgate : canSitOn e x → False) : False := by
  have hconv : (init ++ [x]) ++ e :: rest = init ++ x :: e :: rest := by
    rw [List.append_assoc]
    rfl
  rw [hconv] at hok
  exact hgate (runOK_adjacent_fit x e init rest hok)

private theorem landing_top_tops_source {s : State} {x : Card} {A : Anchor}
    {pre run : List Card} (hwf : s.WF)
    (hface : (s.piles A).faceUp = pre ++ run) (hrunne : run ≠ [])
    (hlast : lastOf run = some x) :
    s.pileOfTop x = some A := by
  refine (pileOfTop_eq_some_iff hwf).2 ?_
  show lastOf (s.piles A).faceUp = some x
  rw [hface, lastOf_append_nonempty hrunne]
  exact hlast

/-! ## §1a. The located-pile kill: the shared case tree -/

private theorem located_kill {s s' : State} {x e : Card} {A k : Anchor}
    (hwf : s.WF) (hwfs' : s'.WF) (hx : s.pileOfTop x = none)
    (hemem : e ∈ (s.piles A).faceUp)
    (hfaceup : (s.piles A).faceUp
      = below e (s.piles A).faceUp ++ fromCard e (s.piles A).faceUp)
    (hrunne : fromCard e (s.piles A).faceUp ≠ [])
    (hK : (s'.piles k).top = lastOf (fromCard e (s.piles A).faceUp))
    (hA : A ≠ k → (s'.piles A).faceUp = below e (s.piles A).faceUp)
    (hrest : ∀ y, y ≠ A → y ≠ k → (s'.piles y).top = (s.piles y).top)
    (hgate : canSitOn e x → False) :
    s'.pileOfTop x = none := by
  cases hpin : s'.pileOfTop x with
  | none => rfl
  | some y =>
      exfalso
      have htopY : (s'.piles y).top = some x := (pileOfTop_eq_some_iff hwfs').mp hpin
      rcases Decidable.em (y = k) with hyk | hyk
      · rw [hyk] at htopY
        rw [hK] at htopY
        have htop := landing_top_tops_source hwf hfaceup hrunne htopY
        rw [htop] at hx
        exact absurd hx (by simp)
      · rcases Decidable.em (y = A) with hyA | hyA
        · subst y
          have hta : (s'.piles A).faceUp = below e (s.piles A).faceUp := hA hyk
          have hlpre : lastOf (below e (s.piles A).faceUp) = some x := by
            have hl : lastOf (s'.piles A).faceUp = some x := htopY
            rw [hta] at hl
            exact hl
          obtain ⟨init, hinit⟩ := lastOf_eq_snoc hlpre
          have hsuf : fromCard e (s.piles A).faceUp
              = e :: aboveIn e (s.piles A).faceUp := fromCard_eq_of_mem hemem
          have hfaceup2 := hfaceup
          rw [hinit, hsuf] at hfaceup2
          have hok : runOK ((init ++ [x]) ++ e :: aboveIn e (s.piles A).faceUp)
              = true := by
            rw [← hfaceup2]
            exact hwf.runOK_of A
          exact uncover_kill hok hgate
        · rw [hrest y hyA hyk] at htopY
          rw [(pileOfTop_eq_some_iff hwf).2 htopY] at hx
          exact absurd hx (by simp)

/-! ## §1b. The freeze -/

private theorem freeze {s s' : State} {x e : Card} {b : Base}
    (hwf : s.WF) (hxt : s.pileOfTop x.twin = none)
    (hstep : State.step s (Move.tabToTab e b) = some s')
    (hrev : reversibleAtW s (Move.tabToTab e b))
    (hx : s.pileOfTop x = none) :
    s'.pileOfTop x = none := by
  obtain ⟨A, hhold, hcp, hfr, hs⟩ := step_tabToTab_inv hstep
  have hwfs' : s'.WF := step_wf hwf hstep
  have hemem : e ∈ (s.piles A).faceUp := by
    rcases Decidable.em (e ∈ (s.piles A).faceUp) with h | h
    · exact h
    · exact absurd hfr (by rw [fromCard_eq_nil_of_not_mem e _ h]; simp)
  have hfaceup : (s.piles A).faceUp
      = below e (s.piles A).faceUp ++ fromCard e (s.piles A).faceUp := by
    have h1 := below_aboveIn_split hemem
    rw [← fromCard_eq_of_mem hemem] at h1
    exact h1
  have hnr : below e (s.piles A).faceUp ≠ [] ∨ (s.piles A).hidden = [] := by
    rcases Decidable.em (below e (s.piles A).faceUp = []) with hbl | hbl
    · rcases Decidable.em ((s.piles A).hidden = []) with hh | hh
      · exact Or.inr hh
      · exact absurd hrev (journey_tabToTab_never_reveal hstep hhold hbl hh)
    · exact Or.inl hbl
  have hbar : below e (s.piles A).faceUp = [] → (s.piles A).hidden = [] := by
    intro hbl
    rcases hnr with hne | hhe
    · exact absurd hbl hne
    · exact hhe
  cases b with
  | inl k =>
      obtain ⟨-, hking⟩ := canPlace_inl hcp
      have hs' : s' = (s.setPile A
          (Pile.afterRunRemoved (s.piles A) (below e (s.piles A).faceUp))).setPile k
          (⟨[], fromCard e (s.piles A).faceUp⟩ : Pile) := by
        rw [hs, putRun_eq_inl]
      have hK : (s'.piles k).top = lastOf (fromCard e (s.piles A).faceUp) := by
        rw [hs', setPile_piles_self]
        rfl
      have hA : A ≠ k → (s'.piles A).faceUp = below e (s.piles A).faceUp := by
        intro hkA
        rw [hs', setPile_piles_ne hkA, setPile_piles_self,
          afterRunRemoved_faceUp_barred hbar]
      have hrest : ∀ y, y ≠ A → y ≠ k → (s'.piles y).top = (s.piles y).top := by
        intro y hyA hyk
        rw [hs', setPile_piles_ne hyk, setPile_piles_ne hyA]
      exact located_kill hwf hwfs' hx hemem hfaceup hfr hK hA hrest
        (fun hfit => inl_gate_kill hking hfit)
  | inr z =>
      obtain ⟨k₀, hz, hfitz⟩ := canPlace_inr hcp
      have hk₀A : k₀ ≠ A := by
        intro hcon
        rw [hcon] at hz
        exact canPlace_inr_target_pile_ne hwf hcp hemem hz
      cases hz₁ : (s.setPile A
          (Pile.afterRunRemoved (s.piles A) (below e (s.piles A).faceUp))).pileOfTop z with
      | none =>
          have hs' : s' = s.setPile A
              (Pile.afterRunRemoved (s.piles A) (below e (s.piles A).faceUp)) := by
            rw [hs, putRun_inr_none hz₁]
          cases hpin : s'.pileOfTop x with
          | none => rfl
          | some y =>
              exfalso
              have htopY : (s'.piles y).top = some x :=
                (pileOfTop_eq_some_iff hwfs').mp hpin
              rcases Decidable.em (y = A) with hyA | hyA
              · subst y
                have hta : (s'.piles A).faceUp = below e (s.piles A).faceUp := by
                  rw [hs', setPile_piles_self, afterRunRemoved_faceUp_barred hbar]
                have hlpre : lastOf (below e (s.piles A).faceUp) = some x := by
                  have hl : lastOf (s'.piles A).faceUp = some x := htopY
                  rw [hta] at hl
                  exact hl
                obtain ⟨init, hinit⟩ := lastOf_eq_snoc hlpre
                have hsuf : fromCard e (s.piles A).faceUp
                    = e :: aboveIn e (s.piles A).faceUp := fromCard_eq_of_mem hemem
                have hfaceup2 := hfaceup
                rw [hinit, hsuf] at hfaceup2
                have hok : runOK ((init ++ [x]) ++ e
                    :: aboveIn e (s.piles A).faceUp) = true := by
                  rw [← hfaceup2]
                  exact hwf.runOK_of A
                exact uncover_kill hok (fun hfit => inr_gate_kill hfitz hz hx hxt hfit)
              · rw [hs', setPile_piles_ne hyA] at htopY
                rw [(pileOfTop_eq_some_iff hwf).2 htopY] at hx
                exact absurd hx (by simp)
      | some k =>
          have hksound : (s.setPile A
              (Pile.afterRunRemoved (s.piles A) (below e (s.piles A).faceUp))).topOf k
              = some z :=
            of_decide_eq_true (firstWhere_sound (p := fun y => decide
              ((s.setPile A
                (Pile.afterRunRemoved (s.piles A) (below e (s.piles A).faceUp))).topOf y
                  = some z)) hz₁)
          have hkA : k ≠ A := by
            intro hcon
            rw [hcon] at hksound
            have hpa : ((s.setPile A
                (Pile.afterRunRemoved (s.piles A) (below e (s.piles A).faceUp))).piles A)
                = Pile.afterRunRemoved (s.piles A) (below e (s.piles A).faceUp) :=
              setPile_piles_self
            have hks2 : Pile.top (Pile.afterRunRemoved (s.piles A)
                (below e (s.piles A).faceUp)) = some z := by
              have hks3 : Pile.top (((s.setPile A
                  (Pile.afterRunRemoved (s.piles A) (below e (s.piles A).faceUp))).piles A))
                  = some z := hksound
              rw [hpa] at hks3
              exact hks3
            have hl : lastOf (Pile.afterRunRemoved (s.piles A)
                (below e (s.piles A).faceUp)).faceUp = some z := hks2
            rw [afterRunRemoved_faceUp_barred hbar] at hl
            have hzmem : z ∈ below e (s.piles A).faceUp := lastOf_mem hl
            have hzin : z ∈ (s.piles A).faceUp := mem_below _ hzmem
            have hzk : z ∈ (s.piles k₀).faceUp :=
              Pile.mem_of_top ((pileOfTop_eq_some_iff hwf).mp hz)
            exact (mem_faceUp_unique hwf hzin k₀ hk₀A).1 hzk
          have hs' : s' = (s.setPile A
              (Pile.afterRunRemoved (s.piles A) (below e (s.piles A).faceUp))).setPile k
              { ((s.setPile A
                  (Pile.afterRunRemoved (s.piles A) (below e (s.piles A).faceUp))).piles k)
                with faceUp := ((s.setPile A
                  (Pile.afterRunRemoved (s.piles A) (below e (s.piles A).faceUp))).piles k).faceUp
                  ++ fromCard e (s.piles A).faceUp } := by
            rw [hs, putRun_inr_eq hz₁]
          have hK : (s'.piles k).top = lastOf (fromCard e (s.piles A).faceUp) := by
            rw [hs', setPile_piles_self]
            show lastOf (((s.setPile A
                (Pile.afterRunRemoved (s.piles A)
                  (below e (s.piles A).faceUp))).piles k).faceUp
                ++ fromCard e (s.piles A).faceUp) = _
            rw [lastOf_append_nonempty hfr]
          have hA : A ≠ k → (s'.piles A).faceUp = below e (s.piles A).faceUp := by
            intro hAk
            rw [hs', setPile_piles_ne hAk, setPile_piles_self,
              afterRunRemoved_faceUp_barred hbar]
          have hrest : ∀ y, y ≠ A → y ≠ k → (s'.piles y).top = (s.piles y).top := by
            intro y hyA hyk
            rw [hs', setPile_piles_ne hyk, setPile_piles_ne hyA]
          exact located_kill hwf hwfs' hx hemem hfaceup hfr hK hA hrest
            (fun hfit => inr_gate_kill hfitz hz hx hxt hfit)

/-! ## §2. The main induction -/

/-- The mutual-freeze conjunction form (the chain's per-leg read). -/
private theorem mutualFreeze {s s' : State} {c e : Card} {b : Base}
    (hwf : s.WF)
    (hstep : State.step s (Move.tabToTab e b) = some s')
    (hrev : reversibleAtW s (Move.tabToTab e b))
    (hcov : s.pileOfTop c = none) (htwin : s.pileOfTop c.twin = none) :
    s'.pileOfTop c = none ∧ s'.pileOfTop c.twin = none := by
  have hgt : s.pileOfTop (c.twin).twin = none := by
    rw [Card.twin_twin]
    exact hcov
  exact ⟨freeze hwf htwin hstep hrev hcov, freeze hwf hgt hstep hrev htwin⟩

/-- The chained freeze: an S-license with both c and c.twin un-topped
is impossible — the now-leg tops at once, and every reversible via-leg
carries the non-topping pair forward. -/
private theorem chained_freeze {st : State} {c : Card} (h : CanRaiseS st c) :
    st.WF → st.pileOfTop c = none → st.pileOfTop c.twin = none → False := by
  induction h with
  | now c hcan =>
      intro _hwf hcov _
      obtain ⟨-, a, hpa, -⟩ := hcan
      rw [hpa] at hcov
      exact absurd hcov (by simp)
  | via c hl _hrest ih =>
      intro hwf hcov htwin
      obtain ⟨d, b, hstep, hrev⟩ := hl
      obtain ⟨hf1, hf2⟩ := mutualFreeze hwf hstep hrev hcov htwin
      exact ih (step_wf hwf hstep) hf1 hf2

/-- **THE RUN-OR-TWIN NECESSITY** — the S-license at a card with the
flat position forces the run-or-twin read: either the card itself
tops (the vanilla now-leg would fire) or the twin tops somewhere (at
a covered card every reversible cascade keeps both family cards
un-topped, so the license's raising end cannot be reached). -/
theorem canRaiseS_runOrTwin {st : State} {c : Card} (hwf : st.WF)
    (h : CanRaiseS st c) :
    ∀ a bs run, (st.piles a).faceUp = bs ++ c :: run →
      run = [] ∨ st.pileOfTop c.twin ≠ none := by
  intro a bs run hshape
  rcases Decidable.em (run = []) with hrun | hrun
  · exact Or.inl hrun
  · refine Or.inr ?_
    intro hcon
    exfalso
    have hcmem : c ∈ (st.piles a).faceUp := by
      rw [hshape]
      exact List.mem_append.mpr (Or.inr (List.mem_cons_self ..))
    have hok : runOK (bs ++ c :: run) = true := by
      rw [← hshape]
      exact hwf.runOK_of a
    have hcov : st.pileOfTop c = none := by
      cases hpin : st.pileOfTop c with
      | none => rfl
      | some y =>
          exfalso
          have htyc : c ∈ (st.piles y).faceUp :=
            Pile.mem_of_top ((pileOfTop_eq_some_iff hwf).mp hpin)
          rcases Decidable.em (y = a) with hya | hya
          · obtain ⟨d, rest, hrunne⟩ := list_cons_of_ne_nil hrun
            rw [hya] at hpin
            have hlast : lastOf (bs ++ c :: d :: rest) = some c := by
              have htt : lastOf (st.piles a).faceUp = some c :=
                (pileOfTop_eq_some_iff hwf).mp hpin
              rw [hshape, hrunne] at htt
              exact htt
            rw [lastOf_append_nonempty (by simp)] at hlast
            have hlast2 : lastOf (d :: rest) = some c := hlast
            have hcrun : c ∈ d :: rest := lastOf_mem hlast2
            have hok2 : runOK (bs ++ c :: d :: rest) = true := by
              rw [← hrunne]
              exact hok
            have hdesc : c.rank.toIdx < c.rank.toIdx :=
              runOK_desc (P := bs ++ [c]) (S := d :: rest)
                (by rw [show (bs ++ [c]) ++ (d :: rest)
                        = bs ++ c :: d :: rest from by
                      rw [List.append_assoc]; rfl]
                    exact hok2)
                (by simp) hcrun
            omega
          · exact (mem_faceUp_unique hwf hcmem y hya).1 htyc
    exact chained_freeze h hwf hcov hcon

/-! ## The audit battery -/

#print axioms canRaiseS_runOrTwin



