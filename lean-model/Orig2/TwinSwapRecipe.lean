import Orig2.SeatMateStack

/-!
# Orig2.TwinSwapRecipe - the ordinary 3-leg twin-swap recipe

`twinPairSwapStrict_of_twin_raise`: a reversible raise of the seated
blocker `c.twin`, followed by the slide of `c` onto the exposed twin
target, followed by the pull of the raised twin onto `c`'s vacated
parent.  The three legs are the ordinary twin-pair interchange, and
the whole play is a witness reversible loop.

House compliance: zero `sorry`, zero `Classical.choice`; born as a
scratch card under `Temp/` (the scratch original remains there,
gitignored), consolidated into `Orig2/` at the shared-kit pass and
imported by `Orig2.FiberTransfer` - the either-side and interface
forms live there (`swappableIn_of_raise`,
`swappableIn_of_raiseLicensed`).
-/

/-! ## Private list and twin arithmetic -/

/-! ## Private twin arithmetic -/

private theorem tsr_canSitOn_twin_target (c z : Card) :
    canSitOn c z.twin = canSitOn c z := by
  rcases z with ⟨s, r⟩
  cases s <;> rfl

private theorem tsr_canSitOn_twin_mover (c z : Card) :
    canSitOn c.twin z = canSitOn c.twin z.twin := by
  rcases c with ⟨s, r⟩
  rcases z with ⟨s', r'⟩
  cases s <;> cases s' <;> rfl

theorem twinPairSwapStrict_of_twin_raise
    {st : State} {c z : Card} {a : Anchor}
    (hwf : st.WF)
    (hc : seatOf st c = some (Sum.inr z))
    (hct : seatOf st c.twin = some (Sum.inr z.twin))
    (hpa : st.pileOfTop c.twin = some a)
    (hraise : reversibleAtW st (Move.tabToFound c.twin)) :
    ∃ v, twinPairSwapStrict st v c ∧ sameOrbitSetoid.r st v := by
  -- The two seats and the raise's preconditions
  obtain ⟨a0, hhold0, hb0ne, hlast0⟩ := tfc_seatOf_of_inr hc
  obtain ⟨at0, hholdt, hbtne, hlastt0⟩ := tfc_seatOf_of_inr hct
  have hmemt : c.twin ∈ (st.piles a).faceUp :=
    lastOf_mem (tfc_pileOfTop_top hpa).2
  have hat : at0 = a := pileHolding_inj hholdt ((pileHolding_eq_some_iff hwf).mpr hmemt)
  rw [hat] at hlastt0
  have htopa : lastOf (st.piles a).faceUp = some c.twin := (tfc_pileOfTop_top hpa).2
  have hfaceA : (st.piles a).faceUp = chop (st.piles a).faceUp ++ [c.twin] :=
    lastOf_chop htopa
  have hnodupA : (st.piles a).faceUp.Nodup := runOK_nodup (hwf.runOK_of a)
  have hctNotChop : c.twin ∉ chop (st.piles a).faceUp := by
    rw [hfaceA] at hnodupA
    exact List.snoc_nodup_notMem _ _ hnodupA
  have hbelowT : below c.twin (st.piles a).faceUp = chop (st.piles a).faceUp := by
    conv =>
      lhs
      rw [hfaceA]
    exact below_snoc_not_mem hctNotChop
  have hlastChopT : lastOf (chop (st.piles a).faceUp) = some z.twin := by
    rw [← hbelowT]
    exact hlastt0
  have hchopNe : chop (st.piles a).faceUp ≠ [] := by
    intro h
    rw [h] at hlastChopT
    nomatch hlastChopT
  -- `c` sits in a different pile than the donor
  have ha0a : a0 ≠ a := by
    intro h
    have hmemC : c ∈ (st.piles a).faceUp := by
      rw [← h]
      exact pileHolding_mem hhold0
    rw [hfaceA] at hmemC
    rcases List.mem_append.mp hmemC with h1 | h2
    · have hrokA : runOK (chop (st.piles a).faceUp ++ [c.twin]) = true := by
        rw [← hfaceA]
        exact hwf.runOK_of a
      have hlt := runOK_desc hrokA h1 (List.mem_singleton.mpr rfl)
      have hrank : c.twin.rank.toIdx = c.rank.toIdx := rfl
      omega
    · rcases List.mem_singleton.mp h2 with hceq
      exact card_twin_ne c hceq.symm
  -- the two fit facts
  have hfit0 : canSitOn c z = true := (tfc_seat_parent hwf hhold0 hlast0).1
  have hfitT : canSitOn c z.twin = true := by
    rwa [tsr_canSitOn_twin_target c z]
  have hholdta : st.pileHolding c.twin = some a := by
    rw [← hat]
    exact hholdt
  have hfitTwin : canSitOn c.twin z.twin = true := (tfc_seat_parent hwf hholdta hlastt0).1
  have hfitTwin' : canSitOn c.twin z = true := by
    rwa [tsr_canSitOn_twin_mover c z]
  -- the raise's license and successor
  have hraise' : reversibleAtW st (Move.tabToFound c.twin) := hraise
  obtain ⟨u1₀, play1, hstep1₀, hrun1⟩ := hraise
  obtain ⟨hnx1, a', hpa', -⟩ := step_tabToFound_inv hstep1₀
  have ha'a : a' = a := pileOfTop_inj hpa' hpa
  let st1 : State :=
    { st.setFound c.twin.suit (st.found c.twin.suit ++ [c.twin]) with
      piles := fun a' => if a' = a then
          Pile.afterRunRemoved (st.piles a) (chop (st.piles a).faceUp)
        else st.piles a' }
  have hstep1 : State.step st (Move.tabToFound c.twin) = some st1 :=
    step_tabToFound_splice hnx1 hpa
  have hwf1 : st1.WF := step_wf hwf hstep1
  have hst1_pa : st1.piles a = Pile.afterRunRemoved (st.piles a) (chop (st.piles a).faceUp) := by
    simp only [st1, ite_true]
  have hst1_pne : ∀ a' ≠ a, st1.piles a' = st.piles a' := by
    intro a' ha'
    simp only [st1, ite_eq_right ha']
  have hst1_pa0 : st1.piles a0 = st.piles a0 := hst1_pne a0 ha0a
  have hst1_face : (st1.piles a).faceUp = chop (st.piles a).faceUp := by
    rw [hst1_pa, afterRunRemoved_faceUp_ne hchopNe]
  have hst1_top : st1.pileOfTop z.twin = some a := by
    rw [pileOfTop_eq_some_iff hwf1]
    show lastOf (st1.piles a).faceUp = some z.twin
    rw [hst1_face]
    exact hlastChopT
  have hst1_hold : st1.pileHolding c = some a0 := by
    rw [pileHolding_eq_some_iff hwf1, hst1_pa0]
    exact pileHolding_mem hhold0
  have hst1_cp : st1.canPlace c (Sum.inr z.twin) = true := by
    rw [canPlace_inr_located hst1_top]
    exact hfitT
  have hrunNe : fromCard c (st1.piles a0).faceUp ≠ [] := by
    rw [hst1_pa0]
    obtain ⟨t, ht⟩ := tfc_fromCard_cons_head (st.piles a0).faceUp (pileHolding_mem hhold0)
    rw [ht]
    exact List.cons_ne_nil _ _
  -- the slide's successor
  let u2 : State :=
    (st1.setPile a0
      (Pile.afterRunRemoved (st1.piles a0) (below c (st1.piles a0).faceUp))).putRun
        (fromCard c (st1.piles a0).faceUp) (Sum.inr z.twin)
  have hstep2 : State.step st1 (Move.tabToTab c (Sum.inr z.twin)) = some u2 := by
    rw [step_tabToTab_eq, hst1_hold, hst1_cp]
    simp only [ite_true]
    cases hfr : fromCard c (st1.piles a0).faceUp with
    | nil => exact absurd hfr hrunNe
    | cons run tail =>
        rw [← hfr]
  have hwf2 : u2.WF := step_wf hwf1 hstep2
  obtain ⟨tr, hrun0⟩ := tfc_fromCard_cons_head (st.piles a0).faceUp (pileHolding_mem hhold0)
  -- `c` is not in the donor run, so it is not in the chop either
  have hcNotA : c ∉ (st.piles a).faceUp :=
    (mem_faceUp_unique hwf (pileHolding_mem hhold0) a (fun h => ha0a h.symm)).1
  have hcNotPreA : c ∉ chop (st.piles a).faceUp := fun hm => hcNotA (chop_mem hm)
  -- the slide's exact step shape
  obtain ⟨a0', hhold2, hcp2, hfr2, hu2eq⟩ := step_tabToTab_inv hstep2
  have ha0'a0 : a0' = a0 := by
    have hx : some a0 = some a0' := hst1_hold.symm.trans hhold2
    exact (Option.some.inj hx).symm
  rw [ha0'a0] at hu2eq
  -- the slide's target search stays at `a`
  have hQtop : (Pile.afterRunRemoved (st1.piles a0)
      (below c (st1.piles a0).faceUp)).top = some z := by
    show lastOf (Pile.afterRunRemoved (st1.piles a0)
      (below c (st1.piles a0).faceUp)).faceUp = some z
    rw [hst1_pa0, afterRunRemoved_faceUp_ne hb0ne]
    exact hlast0
  have hQne : (Pile.afterRunRemoved (st1.piles a0)
      (below c (st1.piles a0).faceUp)).top ≠ some z.twin := by
    rw [hQtop]
    intro h
    exact card_twin_ne z (Option.some.inj h).symm
  have hset1_top : (st1.setPile a0
      (Pile.afterRunRemoved (st1.piles a0) (below c (st1.piles a0).faceUp))).pileOfTop z.twin
      = some a :=
    pileOfTop_setPile_ne hwf1 hst1_top ha0a hQne
  have hu2_pa0 : u2.piles a0 =
      Pile.afterRunRemoved (st1.piles a0) (below c (st1.piles a0).faceUp) := by
    rw [hu2eq]
    rw [putRun_piles_inr_ne _ _ _ _ hset1_top ha0a, setPile_piles_self]
  have hu2_face_a0 : (u2.piles a0).faceUp = below c (st.piles a0).faceUp := by
    rw [hu2_pa0, hst1_pa0, afterRunRemoved_ne hb0ne]
  have hu2_hidden_a0 : (u2.piles a0).hidden = (st.piles a0).hidden := by
    rw [hu2_pa0, hst1_pa0, afterRunRemoved_ne hb0ne]
  have hu2_face_a : (u2.piles a).faceUp
      = chop (st.piles a).faceUp ++ fromCard c (st.piles a0).faceUp := by
    rw [hu2eq]
    rw [putRun_piles_inr_self _ _ _ _ hset1_top, setPile_piles_ne (Ne.symm ha0a),
      hst1_face, hst1_pa0]
  have hu2_hidden_a : (u2.piles a).hidden = (st.piles a).hidden := by
    rw [hu2eq]
    rw [putRun_piles_inr_self _ _ _ _ hset1_top, setPile_piles_ne (Ne.symm ha0a),
      hst1_pa, afterRunRemoved_ne hchopNe]
  have hu2_piles_other : ∀ a' ≠ a0, a' ≠ a → u2.piles a' = st.piles a' := by
    intro a' ha0' ha'
    rw [hu2eq]
    rw [putRun_piles_inr_ne _ _ _ _ hset1_top ha', setPile_piles_ne ha0', hst1_pne a' ha']
  have hu2_top : u2.pileOfTop z = some a0 := by
    rw [pileOfTop_eq_some_iff hwf2]
    show lastOf (u2.piles a0).faceUp = some z
    rw [hu2_face_a0]
    exact hlast0
  have hu2_cp : u2.canPlace c.twin (Sum.inr z) = true := by
    rw [canPlace_inr_located hu2_top]
    exact hfitTwin'
  have hu2_found_eq : u2.found = st1.found := by
    rw [hu2eq, putRun_found, setPile_found]
  have hu2_found_self : u2.found c.twin.suit = st.found c.twin.suit ++ [c.twin] := by
    rw [hu2_found_eq]
    simp only [st1, setFound_found_self]
  have hu2_found_other : ∀ s ≠ c.twin.suit, u2.found s = st.found s := by
    intro s hs
    rw [hu2_found_eq]
    simp only [st1, setFound_found_ne hs]
  have hu2_stock : u2.stock = st.stock := by
    rw [hu2eq, putRun_stock, setPile_stock]
    rfl
  have hu2_waste : u2.waste = st.waste := by
    rw [hu2eq, putRun_waste, setPile_waste]
    rfl
  have hu2_drawStep : u2.drawStep = st.drawStep := by
    rw [hu2eq, putRun_drawStep, setPile_drawStep]
    rfl
  have hu2_foundTop : u2.foundTop c.twin.suit = some c.twin := by
    unfold State.foundTop
    rw [hu2_found_self]
    exact lastOf_snoc
  -- the pull's successor
  let v : State :=
    (u2.setFound c.twin.suit (chop (u2.found c.twin.suit))).putCard c.twin (Sum.inr z)
  have hstep3 : State.step u2 (Move.foundToTab c.twin (Sum.inr z)) = some v := by
    rw [step_foundToTab_splice hu2_foundTop hu2_cp]
  have hwf3 : v.WF := step_wf hwf2 hstep3
  obtain ⟨c3, htop3, hc3, hcp3, hv3⟩ := step_foundToTab_inv hstep3
  have hv_found : ∀ s, v.found s = st.found s := by
    intro s
    rw [hv3, putCard_found]
    by_cases hs : s = c.twin.suit
    · rw [hs, setFound_found_self, hu2_found_self, chop_snoc]
    · rw [setFound_found_ne hs, hu2_found_other s hs]
  have hv_stock : v.stock = st.stock := by
    rw [hv3, putCard_stock, setFound_stock]
    exact hu2_stock
  have hv_waste : v.waste = st.waste := by
    rw [hv3, putCard_waste, setFound_waste]
    exact hu2_waste
  have hv_drawStep : v.drawStep = st.drawStep := by
    rw [hv3, putCard_drawStep, setFound_drawStep]
    exact hu2_drawStep
  have hv_pa0 : v.piles a0 =
      { hidden := (u2.piles a0).hidden, faceUp := (u2.piles a0).faceUp ++ [c.twin] } := by
    have hloc : (u2.setFound c.twin.suit (chop (u2.found c.twin.suit))).pileOfTop z
        = some a0 := by
      unfold State.pileOfTop State.topOf
      rw [setFound_piles]
      exact hu2_top
    rw [hv3, putCard_piles_inr _ _ _ a0 hloc]
    dsimp only
    rw [ite_eq_left rfl, setFound_piles]
  have hv_face_a0 : (v.piles a0).faceUp = below c (st.piles a0).faceUp ++ [c.twin] := by
    rw [hv_pa0, hu2_face_a0]
  have hv_hidden_a0 : (v.piles a0).hidden = (st.piles a0).hidden := by
    rw [hv_pa0, hu2_hidden_a0]
  have hv_pa : v.piles a = u2.piles a := by
    have hloc : (u2.setFound c.twin.suit (chop (u2.found c.twin.suit))).pileOfTop z
        = some a0 := by
      unfold State.pileOfTop State.topOf
      rw [setFound_piles]
      exact hu2_top
    rw [hv3, putCard_piles_inr _ _ _ a0 hloc]
    dsimp only
    rw [ite_eq_right (fun h => ha0a h.symm), setFound_piles]
  have hv_piles_other : ∀ a' ≠ a0, a' ≠ a → v.piles a' = st.piles a' := by
    intro a' ha0' ha'
    have hloc : (u2.setFound c.twin.suit (chop (u2.found c.twin.suit))).pileOfTop z
        = some a0 := by
      unfold State.pileOfTop State.topOf
      rw [setFound_piles]
      exact hu2_top
    rw [hv3, putCard_piles_inr _ _ _ a0 hloc]
    dsimp only
    rw [ite_eq_right ha0', setFound_piles]
    exact hu2_piles_other a' ha0' ha'
  have hv_nextUp : v.nextUp c.twin = true := by
    unfold State.nextUp State.foundHeight
    rw [hv_found]
    exact hnx1
  have hv_top_twin : v.pileOfTop c.twin = some a0 := by
    rw [pileOfTop_eq_some_iff hwf3]
    show lastOf (v.piles a0).faceUp = some c.twin
    rw [hv_face_a0]
    exact lastOf_snoc
  -- §R3: the pull's undo is the raise of `c.twin` at `v`
  have hstepR3 : State.step v (Move.tabToFound c.twin) = some u2 := by
    rw [step_tabToFound_splice hv_nextUp hv_top_twin]
    rw [Option.some.injEq]
    refine State.ext ?_ ?_ ?_ ?_ ?_
    · funext s
      by_cases hs : s = c.twin.suit
      · rw [hs, setFound_found_self, hv_found, hu2_found_eq]
        simp only [st1, setFound_found_self]
      · rw [setFound_found_ne hs, hv_found, hu2_found_eq]
        simp only [st1, setFound_found_ne hs]
    · funext a'
      by_cases ha0' : a' = a0
      · rw [ha0']
        dsimp only
        rw [ite_eq_left rfl, hv_face_a0, chop_snoc, afterRunRemoved_ne hb0ne]
        apply Pile.ext
        · rw [hv_hidden_a0, hu2_hidden_a0]
        · exact hu2_face_a0.symm
      · dsimp only
        rw [ite_eq_right ha0']
        by_cases ha' : a' = a
        · rw [ha', hv_pa]
        · rw [hv_piles_other a' ha0' ha', hu2_piles_other a' ha0' ha']
    · rw [setFound_stock, hv_stock]
      exact hu2_stock.symm
    · rw [setFound_waste, hv_waste]
      exact hu2_waste.symm
    · rw [setFound_drawStep, hv_drawStep]
      exact hu2_drawStep.symm
  -- §R2: the slide's undo is the slide back onto `z` at `u2`
  have hQa_top : (Pile.afterRunRemoved (u2.piles a) (chop (st.piles a).faceUp)).top
      = some z.twin := by
    show lastOf (Pile.afterRunRemoved (u2.piles a)
      (chop (st.piles a).faceUp)).faceUp = some z.twin
    rw [afterRunRemoved_faceUp_ne hchopNe]
    exact hlastChopT
  have hQa_ne : (Pile.afterRunRemoved (u2.piles a) (chop (st.piles a).faceUp)).top
      ≠ some z := by
    rw [hQa_top]
    intro h
    exact card_twin_ne z (Option.some.inj h)
  have hseta_top : (u2.setPile a
      (Pile.afterRunRemoved (u2.piles a) (chop (st.piles a).faceUp))).pileOfTop z
      = some a0 :=
    pileOfTop_setPile_ne hwf2 hu2_top ha0a.symm hQa_ne
  have hmemc_u2 : c ∈ (u2.piles a).faceUp := by
    rw [hu2_face_a, hrun0]
    exact List.mem_append_right _ (List.mem_cons.mpr (Or.inl rfl))
  have hu2_hold_c : u2.pileHolding c = some a :=
    (pileHolding_eq_some_iff hwf2).mpr hmemc_u2
  have hu2_cp_z : u2.canPlace c (Sum.inr z) = true := by
    rw [canPlace_inr_located hu2_top]
    exact hfit0
  have hfr_u2 : fromCard c (u2.piles a).faceUp = c :: tr := by
    rw [hu2_face_a, hrun0]
    rw [(tfc_below_fromCard_excl c (chop (st.piles a).faceUp) (c :: tr) hcNotPreA).2]
    exact fromCard_head_eq
  have hbelow_u2 : below c (u2.piles a).faceUp = chop (st.piles a).faceUp := by
    rw [hu2_face_a, hrun0]
    rw [(tfc_below_fromCard_excl c (chop (st.piles a).faceUp) (c :: tr) hcNotPreA).1]
    rw [below_cons, ite_eq_left rfl, List.append_nil]
  have hfa0 : below c (st.piles a0).faceUp ++ (c :: tr) = (st.piles a0).faceUp := by
    rw [← hrun0]
    exact tfc_below_fromCard c (st.piles a0).faceUp
  have hstepR2 : State.step u2 (Move.tabToTab c (Sum.inr z)) = some st1 := by
    rw [step_tabToTab_eq, hu2_hold_c, hu2_cp_z]
    simp only [ite_true]
    rw [hbelow_u2, hfr_u2]
    rw [Option.some.injEq]
    refine State.ext ?_ ?_ ?_ ?_ ?_
    · rw [putRun_found, setPile_found]
      exact hu2_found_eq
    · funext a'
      by_cases ha0' : a' = a0
      · rw [ha0']
        rw [putRun_piles_inr_self _ _ _ _ hseta_top,
          setPile_piles_ne ha0a, hst1_pa0]
        apply Pile.ext
        · rw [hu2_hidden_a0]
        · rw [hu2_face_a0, hfa0]
      · rw [putRun_piles_inr_ne _ _ _ _ hseta_top ha0']
        by_cases ha' : a' = a
        · rw [ha']
          rw [setPile_piles_self, hst1_pa,
            show Pile.afterRunRemoved (u2.piles a) (chop (st.piles a).faceUp)
                = { hidden := (u2.piles a).hidden, faceUp := chop (st.piles a).faceUp }
              from afterRunRemoved_ne hchopNe,
            show Pile.afterRunRemoved (st.piles a) (chop (st.piles a).faceUp)
                = { hidden := (st.piles a).hidden, faceUp := chop (st.piles a).faceUp }
              from afterRunRemoved_ne hchopNe,
            hu2_hidden_a]
        · rw [setPile_piles_ne ha']
          exact (hu2_piles_other a' ha0' ha').trans (hst1_pne a' ha').symm
    · rw [putRun_stock, setPile_stock, hu2_stock]
      rfl
    · rw [putRun_waste, setPile_waste, hu2_waste]
      rfl
    · rw [putRun_drawStep, setPile_drawStep, hu2_drawStep]
      rfl
  -- §R1: the raise's undo is the pull back onto `z.twin` at `st1`
  have hst1_foundTop : st1.foundTop c.twin.suit = some c.twin := by
    unfold State.foundTop
    rw [show st1.found c.twin.suit = st.found c.twin.suit ++ [c.twin] by
      simp only [st1, setFound_found_self]]
    exact lastOf_snoc
  have hst1_cp_twin : st1.canPlace c.twin (Sum.inr z.twin) = true := by
    rw [canPlace_inr_located hst1_top]
    exact hfitTwin
  have hloc1 : (st1.setFound c.twin.suit (chop (st1.found c.twin.suit))).pileOfTop z.twin
      = some a := by
    unfold State.pileOfTop State.topOf
    rw [setFound_piles]
    exact hst1_top
  have hstepR1 : State.step st1 (Move.foundToTab c.twin (Sum.inr z.twin)) = some st := by
    rw [step_foundToTab_splice hst1_foundTop hst1_cp_twin]
    rw [Option.some.injEq]
    refine State.ext ?_ ?_ ?_ ?_ ?_
    · funext s
      rw [putCard_found]
      by_cases hs : s = c.twin.suit
      · rw [hs, setFound_found_self,
          show st1.found c.twin.suit = st.found c.twin.suit ++ [c.twin] by
            simp only [st1, setFound_found_self],
          chop_snoc]
      · rw [setFound_found_ne hs]
        simp only [st1, setFound_found_ne hs]
    · funext a'
      rw [putCard_piles_inr _ _ _ a hloc1]
      dsimp only
      by_cases ha' : a' = a
      · rw [ha']
        rw [ite_eq_left rfl, setFound_piles]
        apply Pile.ext
        · rw [hst1_pa, afterRunRemoved_ne hchopNe]
        · rw [hst1_face]
          exact hfaceA.symm
      · rw [ite_eq_right ha', setFound_piles, hst1_pne a' ha']
    · rw [putCard_stock, setFound_stock]
      rfl
    · rw [putCard_waste, setFound_waste]
      rfl
    · rw [putCard_drawStep, setFound_drawStep]
      rfl
  -- §W. The three moves and their exact undos are reversible
  have hrev2 : reversibleAtW st1 (Move.tabToTab c (Sum.inr z.twin)) :=
    ⟨u2, [Move.tabToTab c (Sum.inr z)], hstep2, by rw [run_one hstepR2]⟩
  have hrev3 : reversibleAtW u2 (Move.foundToTab c.twin (Sum.inr z)) :=
    ⟨v, [Move.tabToFound c.twin], hstep3, by rw [run_one hstepR3]⟩
  have hrevR3 : reversibleAtW v (Move.tabToFound c.twin) :=
    ⟨u2, [Move.foundToTab c.twin (Sum.inr z)], hstepR3, by rw [run_one hstep3]⟩
  have hrevR2 : reversibleAtW u2 (Move.tabToTab c (Sum.inr z)) :=
    ⟨st1, [Move.tabToTab c (Sum.inr z.twin)], hstepR2, by rw [run_one hstep2]⟩
  have hrevR1 : reversibleAtW st1 (Move.foundToTab c.twin (Sum.inr z.twin)) :=
    ⟨st, [Move.tabToFound c.twin], hstepR1, by rw [run_one hstep1]⟩
  -- §S. The two pair seats
  have hv_seat_c : seatOf v c = some (Sum.inr z.twin) := by
    have h1 : seatOf v c = seatOf u2 c :=
      pull_seat_change hstep3 c (fun h => card_twin_ne c h.symm)
    have h2 : seatOf u2 c = some (Sum.inr z.twin) := by
      have h := tfc_seat_point_edit hwf1 hstep2 hrev2 c
      rw [h]
      simp
    rw [h1, h2]
  have hv_seat_twin : seatOf v c.twin = some (Sum.inr z) := by
    have hctNotPre0 : c.twin ∉ below c (st.piles a0).faceUp := by
      intro hm
      exact (mem_faceUp_unique hwf hmemt a0 ha0a).1 (mem_below _ hm)
    have hbel : below c.twin (v.piles a0).faceUp = below c (st.piles a0).faceUp := by
      rw [hv_face_a0]
      exact below_snoc_not_mem hctNotPre0
    have hholdv : v.pileHolding c.twin = some a0 := by
      rw [pileHolding_eq_some_iff hwf3, hv_face_a0]
      exact List.mem_append_right _ (List.mem_cons.mpr (Or.inl rfl))
    exact tfc_seatOf_inr_intro hholdv (by rw [hbel]; exact hlast0)
  -- §O. Every other seat is untouched
  have hv_other : ∀ y, y ≠ c → y ≠ c.twin → seatOf v y = seatOf st y := by
    intro y hyc hyt
    have h1 : seatOf v y = seatOf u2 y := pull_seat_change hstep3 y hyt
    have h2 : seatOf u2 y = seatOf st1 y := by
      have h := tfc_seat_point_edit hwf1 hstep2 hrev2 y
      rw [h]
      simp only [ite_eq_right hyc]
    have h3 : seatOf st1 y = seatOf st y := by
      by_cases hs : seatOf st y = none
      · rw [hs]
        exact raise_none_of_chop_ne hstep1 hpa hchopNe hs
      ·       exact raise_seat_change_of_seated hstep1 hraise' hs hyt
    rw [h1, h2, h3]
  -- §F. The fixed readouts
  have hbf : boardFixed st v := by
    refine ⟨?_, ?_⟩
    · intro a'
      by_cases ha0' : a' = a0
      · rw [ha0']
        exact hv_hidden_a0.symm
      · by_cases ha' : a' = a
        · rw [ha']
          rw [hv_pa, hu2_hidden_a]
        · rw [hv_piles_other a' ha0' ha']
    · rw [hv_drawStep]
  have hff : foundsFixed st v := fun s => (hv_found s).symm
  have hstock : st.stock = v.stock := hv_stock.symm
  have hwaste : st.waste = v.waste := hv_waste.symm
  have hcut : cutOf st = cutOf v := by
    show st.stock.length = v.stock.length
    rw [hstock]
  -- §C. The two witness shuffles
  have hforward : ShufflePlayW st
      [Move.tabToFound c.twin, Move.tabToTab c (Sum.inr z.twin),
        Move.foundToTab c.twin (Sum.inr z)] v :=
    Walk.cons hraise' hstep1
      (Walk.cons hrev2 hstep2 (Walk.cons hrev3 hstep3 (Walk.nil v)))
  have hback : ShufflePlayW v
      [Move.tabToFound c.twin, Move.tabToTab c (Sum.inr z),
        Move.foundToTab c.twin (Sum.inr z.twin)] st :=
    Walk.cons hrevR3 hstepR3
      (Walk.cons hrevR2 hstepR2 (Walk.cons hrevR1 hstepR1 (Walk.nil st)))
  have horbit : sameOrbitSetoid.r st v := ⟨_, hback, _, hforward⟩
  refine ⟨v, ⟨?_, ?_, hv_other, hbf, hff, hstock, hwaste, hcut⟩, horbit⟩
  · rw [hv_seat_c, hct]
  · rw [hv_seat_twin, hc]

/-- **The `SwappableIn` form of the recipe**: a reversible raise of the twin
supplies the strict twin swap inside the orbit. -/
theorem swappableIn_of_twin_raise
    {st : State} {c z : Card}
    (hwf : st.WF)
    (hc : seatOf st c = some (Sum.inr z))
    (hct : seatOf st c.twin = some (Sum.inr z.twin))
    (hraise : reversibleAtW st (Move.tabToFound c.twin)) :
    SwappableIn st c := by
  rcases hraise with ⟨u1, play, hstep, hrun⟩
  obtain ⟨-, a, hpa, -⟩ := step_tabToFound_inv hstep
  exact twinPairSwapStrict_of_twin_raise hwf hc hct hpa ⟨u1, play, hstep, hrun⟩

#print axioms twinPairSwapStrict_of_twin_raise
#print axioms swappableIn_of_twin_raise
