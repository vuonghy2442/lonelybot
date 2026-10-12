import Orig.ForkStateUniqGate

/-! ## §0. The private kit -/

private theorem card_twin_ne (c : Card) : c.twin ≠ c :=
  fun h => Suit.twin_ne c.suit (congrArg Card.suit h)

private theorem nodup_mid_notmem (d : Card) :
    ∀ (l rest : List Card), (l ++ d :: rest).Nodup → d ∉ l := by
  intro l
  induction l with
  | nil => intro rest _ hm; exact absurd hm (by simp)
  | cons x xs ih =>
      intro rest hnd hm
      rcases List.mem_cons.mp hm with rfl | hin
      · exact absurd (List.mem_append.mpr (Or.inr (List.mem_cons_self ..)))
          ((List.nodup_cons.mp hnd).1)
      · exact ih rest (List.nodup_cons.mp hnd).2 hin

private theorem fromCard_run_head (e : Card) :
    ∀ (l : List Card), fromCard e l ≠ [] → ∃ tr, fromCard e l = e :: tr := by
  intro l
  induction l with
  | nil => intro h; exact absurd h (by simp [fromCard])
  | cons x xs ih =>
      intro h
      by_cases hxe : x = e
      · exact ⟨xs, by rw [hxe, fromCard_cons_self]⟩
      · rw [fromCard_cons_ne xs hxe] at h
        obtain ⟨tr, htr⟩ := ih h
        exact ⟨tr, by rw [fromCard_cons_ne xs hxe]; exact htr⟩

private theorem afterRunRemoved_bare {p : Pile} (hh : p.hidden = []) :
    Pile.afterRunRemoved p ([] : List Card) = (⟨[], []⟩ : Pile) := by
  show Pile.revealTop { p with faceUp := [] } = _
  rcases p with ⟨hl, fl⟩
  cases hl with
  | nil => rfl
  | cons g gs => exact absurd hh (by simp)

private theorem afterRunRemoved_cons {p : Pile} {x : Card} {xs : List Card} :
    Pile.afterRunRemoved p (x :: xs) = (⟨p.hidden, x :: xs⟩ : Pile) := rfl

private theorem below_nil_shape (x : Card) :
    ∀ (l : List Card), x ∈ l → below x l = [] → ∃ t, l = x :: t := by
  intro l
  induction l with
  | nil => intro hmem; cases hmem
  | cons y ys ih =>
      intro hmem h
      by_cases hyx : y = x
      · exact ⟨ys, by rw [hyx]⟩
      · rw [below_cons_ne ys hyx] at h
        exact absurd h (by simp)

private theorem canPlace_inl_king {s : State} {w : Card} {k : Anchor}
    (h : s.canPlace w (Sum.inl k) = true) : w.rank = Rank.king := by
  rw [State.canPlace, Bool.and_eq_true] at h
  exact of_decide_eq_true h.2

private theorem pileOfTop_of_piles {s t : State} (z : Card)
    (hp : s.piles = t.piles) : s.pileOfTop z = t.pileOfTop z := by
  show (firstWhere (fun a' => decide ((s.piles a').top = some z)) Anchor.all) =
    (firstWhere (fun a' => decide ((t.piles a').top = some z)) Anchor.all)
  rw [hp]

/-! ## §1. The pillar one-step -/

private theorem arr_Q {P : Pile} {e : Card}
    (hmemE : e ∈ P.faceUp)
    (hQ : (P.faceUp = [] ∧ P.hidden = []) ∨
      ∃ K t, P.faceUp = K :: t ∧ K.rank = Rank.king ∧ P.hidden = []) :
    (Pile.afterRunRemoved P (below e P.faceUp)).faceUp = [] ∧
      (Pile.afterRunRemoved P (below e P.faceUp)).hidden = [] ∨
      ∃ K t, (Pile.afterRunRemoved P (below e P.faceUp)).faceUp = K :: t ∧
        K.rank = Rank.king ∧ (Pile.afterRunRemoved P (below e P.faceUp)).hidden = [] := by
  by_cases hpre : below e P.faceUp = []
  · have hhQ : P.hidden = [] := by
      rcases hQ with ⟨-, hh⟩ | ⟨-, -, -, -, hh⟩
      · exact hh
      · exact hh
    rw [hpre, afterRunRemoved_bare hhQ]
    exact Or.inl ⟨rfl, rfl⟩
  · obtain ⟨w, ws, hpc⟩ := list_cons_of_ne_nil hpre
    rw [hpc, afterRunRemoved_cons]
    rcases hQ with ⟨hfup, -⟩ | ⟨K, t, hfup, hK, hhA⟩
    · exfalso
      rw [hfup] at hmemE
      exact absurd hmemE (by simp)
    · by_cases hE : e = K
      · exfalso
        rw [hfup, hE, below_cons_self] at hpc
        exact absurd hpc (by simp)
      · rw [hfup, below_cons_ne t (fun hc => hE hc.symm)] at hpc
        injection hpc with hw hws
        rw [← hw, ← hws]
        exact Or.inr ⟨K, below e t, rfl, hK, hhA⟩

private theorem oneStep_pileInv {A : Anchor} {s s' : State} {m : Move}
    (hstep : State.step s m = some s')
    (hQ : ((s.piles A).faceUp = [] ∧ (s.piles A).hidden = []) ∨
      ∃ K t, (s.piles A).faceUp = K :: t ∧ K.rank = Rank.king ∧
        (s.piles A).hidden = []) :
    ((s'.piles A).faceUp = [] ∧ (s'.piles A).hidden = []) ∨
      ∃ K t, (s'.piles A).faceUp = K :: t ∧ K.rank = Rank.king ∧
        (s'.piles A).hidden = [] := by
  cases m with
  | draw =>
      have hd : s.stepDraw = some s' := hstep
      rw [stepDraw_piles hd]
      exact hQ
  | wasteToFound c =>
      obtain ⟨-, x, xs, hw, hs⟩ := step_wasteToFound_inv hstep
      rw [hs]
      have hp : (({s.setFound c.suit (s.found c.suit ++ [c]) with waste := xs} : State).piles A)
          = s.piles A := rfl
      rw [hp]
      exact hQ
  | wasteToTab c b =>
      obtain ⟨hg, x, xs, hw, hs⟩ := step_wasteToTab_inv hstep
      rw [Bool.and_eq_true] at hg
      rw [hs]
      cases b with
      | inl k =>
          have hp : (({s.putCard c (Sum.inl k) with waste := xs} : State).piles A)
              = (if A = k then (⟨[], [c]⟩ : Pile) else s.piles A) := rfl
          rw [hp]
          by_cases hAk : A = k
          · rw [ite_eq_left hAk]
            rcases hQ with ⟨hfup, -⟩ | ⟨K, t, hfup, -, hhA⟩
            · exact Or.inr ⟨c, [], rfl, canPlace_inl_king hg.2, rfl⟩
            · exfalso
              obtain ⟨hemp, -⟩ := canPlace_inl hg.2
              rw [← hAk] at hemp
              have hfupE := ((Pile.isEmpty_eq _).mp hemp).2
              rw [hfup] at hfupE
              exact absurd hfupE (by simp)
          · rw [ite_eq_right hAk]
            exact hQ
      | inr z =>
          obtain ⟨kk, hpin, -⟩ := canPlace_inr hg.2
          have hp : (({s.putCard c (Sum.inr z) with waste := xs} : State).piles A)
              = (if A = kk then { s.piles kk with faceUp := (s.piles kk).faceUp ++ [c] }
                 else s.piles A) := by
            simp only [putCard_piles_inr _ _ _ _ hpin]
          rw [hp]
          by_cases hAk : A = kk
          · rw [ite_eq_left hAk]
            rw [hAk] at hQ
            rcases hQ with ⟨hfup, -⟩ | ⟨K, t, hfup, hK, hhA⟩
            · exfalso
              have hne := (pileOfTop_top hpin).1
              rw [hfup] at hne
              exact absurd hne (by simp)
            · refine Or.inr ⟨K, t ++ [c], ?_, hK, hhA⟩
              show (s.piles kk).faceUp ++ [c] = K :: (t ++ [c])
              rw [hfup, List.cons_append]
          · rw [ite_eq_right hAk]
            exact hQ
  | tabToFound c =>
      obtain ⟨-, k, hpod, hs⟩ := step_tabToFound_inv hstep
      have hpileEq : s'.piles A = (if A = k then
          Pile.afterRunRemoved (s.piles k) (chop (s.piles k).faceUp)
          else s.piles A) := by rw [hs]
      rw [hpileEq]
      by_cases hAk : A = k
      · rw [hAk] at hQ
        have hself : (if A = k then Pile.afterRunRemoved (s.piles k) (chop (s.piles k).faceUp)
            else s.piles A) = Pile.afterRunRemoved (s.piles k) (chop (s.piles k).faceUp) :=
          ite_eq_left hAk
        rw [hself]
        rcases hQ with ⟨hfup, hhA⟩ | ⟨K, t, hfup, hK, hhA⟩
        · have hch : chop (s.piles k).faceUp = [] := by rw [hfup]; rfl
          rw [hch, afterRunRemoved_bare hhA]
          exact Or.inl ⟨rfl, rfl⟩
        · cases t with
          | nil =>
              have hch : chop (s.piles k).faceUp = [] := by rw [hfup]; rfl
              rw [hch, afterRunRemoved_bare hhA]
              exact Or.inl ⟨rfl, rfl⟩
          | cons y ys =>
              have hch : chop (s.piles k).faceUp = K :: chop (y :: ys) := by rw [hfup]; rfl
              rw [hch, afterRunRemoved_cons]
              exact Or.inr ⟨K, chop (y :: ys), rfl, hK, hhA⟩
      · have helse : (if A = k then Pile.afterRunRemoved (s.piles k) (chop (s.piles k).faceUp)
            else s.piles A) = s.piles A := ite_eq_right hAk
        rw [helse]
        exact hQ
  | foundToTab c b =>
      obtain ⟨c', ht, heqc, hg, hs⟩ := step_foundToTab_inv hstep
      rw [hs]
      have hmidp : (s.setFound c.suit (chop (s.found c.suit))).piles = s.piles :=
        setFound_piles s c.suit (chop (s.found c.suit))
      cases b with
      | inl k =>
          have hp : (((s.setFound c.suit (chop (s.found c.suit))).putCard c (Sum.inl k)).piles A)
              = (if A = k then (⟨[], [c]⟩ : Pile) else s.piles A) := rfl
          rw [hp]
          by_cases hAk : A = k
          · rw [ite_eq_left hAk]
            rcases hQ with ⟨hfup, -⟩ | ⟨K, t, hfup, -, hhA⟩
            · exact Or.inr ⟨c, [], rfl, canPlace_inl_king hg, rfl⟩
            · exfalso
              obtain ⟨hemp, -⟩ := canPlace_inl hg
              rw [← hAk] at hemp
              have hfupE := ((Pile.isEmpty_eq _).mp hemp).2
              rw [hfup] at hfupE
              exact absurd hfupE (by simp)
          · rw [ite_eq_right hAk]
            exact hQ
      | inr z =>
          obtain ⟨kk, hpin, -⟩ := canPlace_inr hg
          have hmidpin : (s.setFound c.suit (chop (s.found c.suit))).pileOfTop z = some kk := by
            rw [pileOfTop_of_piles z hmidp]
            exact hpin
          have hp : (((s.setFound c.suit (chop (s.found c.suit))).putCard c (Sum.inr z)).piles A)
              = (if A = kk then { s.piles kk with faceUp := (s.piles kk).faceUp ++ [c] }
                 else s.piles A) := by
            simp only [putCard_piles_inr _ _ _ _ hmidpin]
            rw [hmidp]
          rw [hp]
          by_cases hAk : A = kk
          · rw [ite_eq_left hAk]
            rw [hAk] at hQ
            rcases hQ with ⟨hfup, -⟩ | ⟨K, t, hfup, hK, hhA⟩
            · exfalso
              have hne := (pileOfTop_top hpin).1
              rw [hfup] at hne
              exact absurd hne (by simp)
            · refine Or.inr ⟨K, t ++ [c], ?_, hK, hhA⟩
              show (s.piles kk).faceUp ++ [c] = K :: (t ++ [c])
              rw [hfup, List.cons_append]
          · rw [ite_eq_right hAk]
            exact hQ
  | tabToTab e b =>
      obtain ⟨Asrc, hhold, hcp, hfr, hs'⟩ := step_tabToTab_inv hstep
      have hmemE : e ∈ (s.piles Asrc).faceUp := pileHolding_mem hhold
      rw [hs']
      cases b with
      | inl k =>
          have hp : (((s.setPile Asrc (Pile.afterRunRemoved (s.piles Asrc)
                (below e ((s.piles Asrc).faceUp)))).putRun
              (fromCard e ((s.piles Asrc).faceUp)) (Sum.inl k)).piles A)
              = (if A = k then (⟨[], fromCard e ((s.piles Asrc).faceUp)⟩ : Pile)
                 else (s.setPile Asrc (Pile.afterRunRemoved (s.piles Asrc)
                   (below e ((s.piles Asrc).faceUp)))).piles A) := rfl
          rw [hp]
          by_cases hAk : A = k
          · rw [ite_eq_left hAk]
            obtain ⟨tr, hrun⟩ := fromCard_run_head e ((s.piles Asrc).faceUp) hfr
            rcases hQ with ⟨hfup, -⟩ | ⟨K, t, hfup, -, hhA⟩
            · exact Or.inr ⟨e, tr, by rw [hrun], canPlace_inl_king hcp, rfl⟩
            · exfalso
              obtain ⟨hemp, -⟩ := canPlace_inl hcp
              rw [← hAk] at hemp
              have hfupE := ((Pile.isEmpty_eq _).mp hemp).2
              rw [hfup] at hfupE
              exact absurd hfupE (by simp)
          · rw [ite_eq_right hAk]
            by_cases hAs : A = Asrc
            · rw [hAs] at hQ
              rw [hAs, setPile_afterRunRemoved_piles_self s Asrc e]
              exact arr_Q hmemE hQ
            · rw [setPile_afterRunRemoved_piles_ne s Asrc e A hAs]
              exact hQ
      | inr z =>
          cases hz : (s.setPile Asrc (Pile.afterRunRemoved (s.piles Asrc)
              (below e ((s.piles Asrc).faceUp)))).pileOfTop z with
          | none =>
              rw [putRun_inr_none hz]
              by_cases hAs : A = Asrc
              · rw [hAs] at hQ
                rw [hAs, setPile_afterRunRemoved_piles_self s Asrc e]
                exact arr_Q hmemE hQ
              · rw [setPile_afterRunRemoved_piles_ne s Asrc e A hAs]
                exact hQ
          | some kk =>
              rw [putRun_inr_eq hz]
              by_cases hAk : A = kk
              · rw [hAk, setPile_piles_self]
                have hneMid := (pileOfTop_top hz).1
                by_cases hAs : A = Asrc
                · rw [hAs] at hQ
                  have hka : kk = Asrc := hAk.symm.trans hAs
                  rw [hka, setPile_afterRunRemoved_piles_self s Asrc e] at hneMid ⊢
                  rcases arr_Q hmemE hQ with ⟨h1, h2⟩ | ⟨K, tm, h1, hK, h2⟩
                  · exact absurd h1 hneMid
                  · refine Or.inr ⟨K, tm ++ fromCard e ((s.piles Asrc).faceUp), ?_, hK, h2⟩
                    rw [h1, List.cons_append]
                · have hmidA : (s.setPile Asrc (Pile.afterRunRemoved (s.piles Asrc)
                        (below e ((s.piles Asrc).faceUp)))).piles kk = s.piles A := by
                    rw [← hAk]
                    exact setPile_afterRunRemoved_piles_ne s Asrc e A hAs
                  rw [hmidA] at hneMid ⊢
                  rcases hQ with ⟨hfup, -⟩ | ⟨K, t, hfup, hK, hhA⟩
                  · exfalso
                    rw [hfup] at hneMid
                    exact absurd hneMid (by simp)
                  · refine Or.inr ⟨K, t ++ fromCard e ((s.piles Asrc).faceUp), ?_, hK, hhA⟩
                    rw [hfup, List.cons_append]
              · rw [setPile_piles_ne hAk]
                by_cases hAs : A = Asrc
                · rw [hAs] at hQ
                  rw [hAs, setPile_afterRunRemoved_piles_self s Asrc e]
                  exact arr_Q hmemE hQ
                · rw [setPile_afterRunRemoved_piles_ne s Asrc e A hAs]
                  exact hQ

/-! ## §2. The play lift -/

private theorem emptyOrKingHead_play {A : Anchor} :
    ∀ (s : State) (play : List Move) (s' : State),
      ((s.piles A).faceUp = [] ∧ (s.piles A).hidden = [] ∨
        ∃ K t, (s.piles A).faceUp = K :: t ∧ K.rank = Rank.king ∧
          (s.piles A).hidden = []) →
      State.run s play = some s' →
      ((s'.piles A).faceUp = [] ∧ (s'.piles A).hidden = [] ∨
        ∃ K t, (s'.piles A).faceUp = K :: t ∧ K.rank = Rank.king ∧
          (s'.piles A).hidden = []) := by
  intro s play
  revert s
  induction play with
  | nil =>
      intro s s' hQ hrun
      have hred : (some s : Option State) = some s' := hrun
      injection hred with hcon
      rw [← hcon]
      exact hQ
  | cons p rest ih =>
      intro s s' hQ hrun
      obtain ⟨s₁, hstep, hrest⟩ := State.run_cons hrun
      exact ih s₁ s' (oneStep_pileInv hstep hQ) hrest

/-! ## §3. The bare-departure consume -/

private theorem bareDeparture_not_reversible {s : State} {c : Card} {b : Base}
    {a : Anchor} {rest : List Card}
    (hhold : s.pileHolding c = some a)
    (hshape : (s.piles a).faceUp = c :: rest)
    (hhid : (s.piles a).hidden = [])
    (hK : c.rank ≠ Rank.king) :
    ¬ reversibleAtW s (Move.tabToTab c b) := by
  rintro ⟨s₁, pl, hstep, hret⟩
  obtain ⟨Asrc, hhold', hcp, hfr, hs₁⟩ := step_tabToTab_inv hstep
  have hA : Asrc = a := Option.some.inj (hhold'.symm.trans hhold)
  rw [hA] at hs₁
  have hmidP : (s.setPile a (Pile.afterRunRemoved (s.piles a)
      (below c ((s.piles a).faceUp)))).piles a = (⟨[], []⟩ : Pile) := by
    rw [show below c ((s.piles a).faceUp) = [] from by
        rw [hshape, below_cons_self],
      afterRunRemoved_bare hhid, setPile_piles_self]
  have hs₁pa : s₁.piles a = (⟨[], []⟩ : Pile) := by
    rw [hs₁]
    cases b with
    | inl k =>
        obtain ⟨hemp, -⟩ := canPlace_inl hcp
        have hkna : k ≠ a := by
          intro hcon
          rw [hcon] at hemp
          have hfupE := ((Pile.isEmpty_eq _).mp hemp).2
          rw [hshape] at hfupE
          exact absurd hfupE (by simp)
        have hank : a ≠ k := fun hcon => hkna hcon.symm
        simp only [putRun_piles_inl]
        rw [ite_eq_right hank]
        exact hmidP
    | inr z =>
        cases hz : (s.setPile a (Pile.afterRunRemoved (s.piles a)
            (below c ((s.piles a).faceUp)))).pileOfTop z with
        | none =>
            rw [putRun_inr_none hz]
            exact hmidP
        | some kk =>
            simp only [putRun_piles_inr _ _ _ _ hz]
            by_cases hak : a = kk
            · exfalso
              have hne := (pileOfTop_top hz).1
              rw [← hak] at hne
              rw [hmidP] at hne
              exact absurd hne (by simp)
            · rw [ite_eq_right hak]
              exact hmidP
  have hQend := emptyOrKingHead_play (A := a) s₁ pl s
    (Or.inl ⟨by rw [hs₁pa], by rw [hs₁pa]⟩) hret
  rcases hQend with ⟨hfupE, -⟩ | ⟨K0, t0, hfupE, hK0, -⟩
  · exfalso
    rw [hshape] at hfupE
    exact absurd hfupE (by simp)
  · exfalso
    rw [hshape] at hfupE
    injection hfupE with hK0c _
    rw [← hK0c] at hK0
    exact absurd hK0 hK

/-! ## §4. The seat-survival leg lemma -/

private theorem seat_bad_survives {s s' : State} {c e : Card} {b : Base}
    {a : Anchor} {rest : List Card}
    (hstep : State.step s (Move.tabToTab e b) = some s')
    (hrev : reversibleAtW s (Move.tabToTab e b))
    (hshape : (s.piles a).faceUp = c :: rest)
    (hbad : ¬ ((s.piles a).hidden = [] ∧ c.rank = Rank.king)) :
    ∃ rest', (s'.piles a).faceUp = c :: rest' ∧
      ((s'.piles a).hidden = (s.piles a).hidden) := by
  obtain ⟨Asrc, hhold, hcp, hfr, hs'⟩ := step_tabToTab_inv hstep
  have hmemE : e ∈ (s.piles Asrc).faceUp := pileHolding_mem hhold
  have hmidF : ∃ mw, ((s.setPile Asrc (Pile.afterRunRemoved (s.piles Asrc)
        (below e ((s.piles Asrc).faceUp)))).piles a).faceUp = c :: mw ∧
      ((s.setPile Asrc (Pile.afterRunRemoved (s.piles Asrc)
        (below e ((s.piles Asrc).faceUp)))).piles a).hidden = (s.piles a).hidden := by
    by_cases hAs : a = Asrc
    · rw [← hAs] at hmemE
      by_cases hEc : e = c
      · exfalso
        have hholdC : s.pileHolding c = some a := by rw [← hEc, hAs]; exact hhold
        have hbel : below e ((s.piles Asrc).faceUp) = [] := by
          rw [← hAs, hEc, hshape, below_cons_self]
        by_cases hh : (s.piles Asrc).hidden = []
        · have hh' : (s.piles a).hidden = [] := by rw [hAs]; exact hh
          have hK : c.rank ≠ Rank.king := fun hcon => hbad ⟨hh', hcon⟩
          rw [hEc] at hrev
          exact absurd hrev (bareDeparture_not_reversible hholdC hshape hh' hK)
        · exact absurd hrev (journey_tabToTab_never_reveal hstep hhold hbel hh)
      · rw [hshape] at hmemE
        have herest : e ∈ rest := (List.mem_cons.mp hmemE).resolve_left hEc
        refine ⟨below e rest, ?_, ?_⟩
        · rw [hAs, setPile_afterRunRemoved_piles_self s Asrc e]
          have hpc : below e ((s.piles Asrc).faceUp) = c :: below e rest := by
            rw [← hAs, hshape, below_cons_ne rest (fun hcc => hEc hcc.symm)]
          rw [hpc, afterRunRemoved_cons]
        · rw [hAs, setPile_afterRunRemoved_piles_self s Asrc e]
          have hpc : below e ((s.piles Asrc).faceUp) = c :: below e rest := by
            rw [← hAs, hshape, below_cons_ne rest (fun hcc => hEc hcc.symm)]
          rw [hpc, afterRunRemoved_cons]
    · refine ⟨rest, ?_, ?_⟩
      · rw [setPile_afterRunRemoved_piles_ne s Asrc e a hAs]
        exact hshape
      · rw [setPile_afterRunRemoved_piles_ne s Asrc e a hAs]
  obtain ⟨mw, hmfup, hmhid⟩ := hmidF
  cases b with
  | inl k =>
      obtain ⟨hemp, -⟩ := canPlace_inl hcp
      have hank : a ≠ k := by
        intro hcon
        rw [← hcon] at hemp
        have hfupE := ((Pile.isEmpty_eq _).mp hemp).2
        rw [hshape] at hfupE
        exact absurd hfupE (by simp)
      rw [hs']
      simp only [putRun_piles_inl]
      rw [ite_eq_right hank]
      exact ⟨mw, hmfup, hmhid⟩
  | inr z =>
      cases hz : (s.setPile Asrc (Pile.afterRunRemoved (s.piles Asrc)
          (below e ((s.piles Asrc).faceUp)))).pileOfTop z with
      | none =>
          rw [hs', putRun_inr_none hz]
          exact ⟨mw, hmfup, hmhid⟩
      | some kk =>
          rw [hs']
          simp only [putRun_piles_inr _ _ _ _ hz]
          by_cases hak : a = kk
          · rw [ite_eq_left hak]
            refine ⟨mw ++ fromCard e ((s.piles Asrc).faceUp), ?_, ?_⟩
            · rw [← hak, hmfup, List.cons_append]
            · rw [← hak]
              exact hmhid
          · rw [ite_eq_right hak]
            exact ⟨mw, hmfup, hmhid⟩

/-! ## §5. The main theorem -/

private theorem onBoard_back {s s' : State} {c e : Card} {b : Base}
    (hstep : State.step s (Move.tabToTab e b) = some s')
    (hrev : reversibleAtW s (Move.tabToTab e b)) :
    ∀ j : Anchor, c ∈ (s'.piles j).faceUp → ∃ a₀, c ∈ (s.piles a₀).faceUp := by
  intro j hcm
  obtain ⟨Asrc, hhold, hcp, hfr, hs'⟩ := step_tabToTab_inv hstep
  have hmemE : e ∈ (s.piles Asrc).faceUp := pileHolding_mem hhold
  have hnr : below e ((s.piles Asrc).faceUp) ≠ [] ∨ (s.piles Asrc).hidden = [] := by
    by_cases hpre : below e ((s.piles Asrc).faceUp) = []
    · right
      by_cases hh : (s.piles Asrc).hidden = []
      · exact hh
      · exact absurd hrev (journey_tabToTab_never_reveal hstep hhold hpre hh)
    · exact Or.inl hpre
  have hmid : ∀ j' : Anchor, ∀ x : Card, x ∈ ((s.setPile Asrc (Pile.afterRunRemoved
        (s.piles Asrc) (below e ((s.piles Asrc).faceUp)))).piles j').faceUp →
      x ∈ (s.piles j').faceUp ∨ x ∈ (s.piles Asrc).faceUp := by
    intro j' x hx
    by_cases hAs : j' = Asrc
    · rw [hAs, setPile_afterRunRemoved_piles_self s Asrc e] at hx
      by_cases hpre2 : below e ((s.piles Asrc).faceUp) = []
      · have hhpre : (s.piles Asrc).hidden = [] := by
          rcases hnr with hne | hh
          · exact absurd hpre2 hne
          · exact hh
        rw [hpre2, afterRunRemoved_bare hhpre] at hx
        exact absurd hx (by simp)
      · obtain ⟨w, ws, hpc⟩ := list_cons_of_ne_nil hpre2
        rw [hpc, afterRunRemoved_cons] at hx
        have hx' : x ∈ below e ((s.piles Asrc).faceUp) := by rw [hpc]; exact hx
        exact Or.inr (mem_below _ hx')
    · rw [setPile_afterRunRemoved_piles_ne s Asrc e j' hAs] at hx
      exact Or.inl hx
  rw [hs'] at hcm
  cases b with
  | inl k =>
      simp only [putRun_piles_inl] at hcm
      by_cases hAk : j = k
      · rw [hAk, ite_eq_left rfl] at hcm
        exact ⟨Asrc, fromCard_subset_mem hcm⟩
      · rw [ite_eq_right hAk] at hcm
        rcases hmid j c hcm with h | h
        · exact ⟨j, h⟩
        · exact ⟨Asrc, h⟩
  | inr z =>
      cases hz : (s.setPile Asrc (Pile.afterRunRemoved (s.piles Asrc)
          (below e ((s.piles Asrc).faceUp)))).pileOfTop z with
      | none =>
          rw [putRun_inr_none hz] at hcm
          rcases hmid j c hcm with h | h
          · exact ⟨j, h⟩
          · exact ⟨Asrc, h⟩
      | some kk =>
          simp only [putRun_piles_inr _ _ _ _ hz] at hcm
          by_cases hhj : j = kk
          · rw [hhj, ite_eq_left rfl] at hcm
            have hcm2 : c ∈ ((s.setPile Asrc (Pile.afterRunRemoved (s.piles Asrc)
                (below e ((s.piles Asrc).faceUp)))).piles kk).faceUp ++
                fromCard e ((s.piles Asrc).faceUp) := hcm
            rcases List.mem_append.mp hcm2 with hold' | hrun'
            · rcases hmid kk c hold' with h | h
              · exact ⟨kk, h⟩
              · exact ⟨Asrc, h⟩
            · exact ⟨Asrc, fromCard_subset_mem hrun'⟩
          · rw [ite_eq_right hhj] at hcm
            rcases hmid j c hcm with h | h
            · exact ⟨j, h⟩
            · exact ⟨Asrc, h⟩

private theorem canRaiseS_positionbelow {st : State} {c : Card} (hwf : st.WF)
    (h : CanRaiseS st c) :
    ∃ a, c ∈ (st.piles a).faceUp ∧
      (below c ((st.piles a).faceUp) ≠ [] ∨
        ((st.piles a).hidden = [] ∧ c.rank = Rank.king)) := by
  induction h with
  | @now stN cN hcan =>
      obtain ⟨-, a, hpa, hseat⟩ := hcan
      have hmem : cN ∈ (stN.piles a).faceUp := Pile.mem_of_top (pileOfTop_top hpa).2
      rcases hseat with hchop | ⟨hhid, hk⟩
      · by_cases hbel : below cN ((stN.piles a).faceUp) = []
        · exfalso
          obtain ⟨tx, htx⟩ := below_nil_shape cN ((stN.piles a).faceUp) hmem hbel
          have hlast : lastOf (stN.piles a).faceUp = some cN := (pileOfTop_top hpa).2
          have hnd : ((stN.piles a).faceUp).Nodup := runOK_nodup (hwf.runOK_of a)
          cases tx with
          | nil =>
              exact hchop (show chop (stN.piles a).faceUp = [] from by rw [htx]; rfl)
          | cons y ys =>
              rw [htx] at hlast hnd
              have hLy : lastOf (y :: ys) = some cN := hlast
              exact absurd (lastOf_mem hLy) ((List.nodup_cons.mp hnd).1)
        · exact ⟨a, hmem, Or.inl hbel⟩
      · exact ⟨a, hmem, Or.inr ⟨hhid, hk⟩⟩
  | @via st0 st1 c0 hl0 hrest ih =>
      obtain ⟨d, bk, hstep, hrev⟩ := hl0
      have hwf1 : st1.WF := step_wf hwf hstep
      obtain ⟨a', hmem', hseat'⟩ := ih hwf1
      obtain ⟨a₀, hmem₀⟩ := onBoard_back hstep hrev a' hmem'
      rcases Decidable.em (below c0 ((st0.piles a₀).faceUp) = []) with hbel | hbel
      · obtain ⟨rest, hshape⟩ := below_nil_shape c0 ((st0.piles a₀).faceUp) hmem₀ hbel
        rcases Decidable.em ((st0.piles a₀).hidden = []) with hh | hh
        · rcases Decidable.em (c0.rank = Rank.king) with hk | hk
          · exact ⟨a₀, hmem₀, Or.inr ⟨hh, hk⟩⟩
          · exfalso
            obtain ⟨rest', hhead', hhid'⟩ := seat_bad_survives hstep hrev hshape
              (fun hcon => hk hcon.2)
            have hmem1 : c0 ∈ (st1.piles a₀).faceUp := by
              rw [hhead']; exact List.mem_cons_self ..
            have ha' : a' = a₀ := pileHolding_inj ((pileHolding_eq_some_iff hwf1).2 hmem')
              ((pileHolding_eq_some_iff hwf1).2 hmem1)
            rw [ha'] at hseat'
            have hbel1' : below c0 ((st1.piles a₀).faceUp) = [] := by
              rw [hhead', below_cons_self]
            rcases hseat' with hne' | ⟨hh', hk'⟩
            · exact absurd hbel1' hne'
            · have hhs : (st0.piles a₀).hidden = [] := by rw [← hhid']; exact hh'
              exact hk hk'
        · exfalso
          obtain ⟨rest', hhead', hhid'⟩ := seat_bad_survives hstep hrev hshape
            (fun hcon => hh hcon.1)
          have hmem1 : c0 ∈ (st1.piles a₀).faceUp := by
            rw [hhead']; exact List.mem_cons_self ..
          have ha' : a' = a₀ := pileHolding_inj ((pileHolding_eq_some_iff hwf1).2 hmem')
            ((pileHolding_eq_some_iff hwf1).2 hmem1)
          rw [ha'] at hseat'
          have hbel1' : below c0 ((st1.piles a₀).faceUp) = [] := by
            rw [hhead', below_cons_self]
          rcases hseat' with hne' | ⟨hh', hk'⟩
          · exact absurd hbel1' hne'
          · have hhs : (st0.piles a₀).hidden = [] := by rw [← hhid']; exact hh'
            exact hh hhs
      · exact ⟨a₀, hmem₀, Or.inl hbel⟩

/-- **THE POSITION-SEAT NECESSITY** — the S-license at `c` forces the flat
form's position and seat reads: the card is on-board in some pile, seated
either on face-up content below it or as the bare king over an empty
hidden deck. -/
theorem canRaiseS_positionSeat {st : State} {c : Card} (hwf : st.WF)
    (h : CanRaiseS st c) :
    ∃ a bs run, (st.piles a).faceUp = bs ++ c :: run ∧
      (bs ≠ [] ∨ ((st.piles a).hidden = [] ∧ c.rank = Rank.king)) := by
  obtain ⟨a, hmem, hseat⟩ := canRaiseS_positionbelow hwf h
  refine ⟨a, below c ((st.piles a).faceUp), aboveIn c ((st.piles a).faceUp), ?_, ?_⟩
  · exact below_aboveIn_split hmem
  · rcases hseat with hne | ⟨hhid, hk⟩
    · exact Or.inl hne
    · exact Or.inr ⟨hhid, hk⟩

#print axioms canRaiseS_positionSeat
