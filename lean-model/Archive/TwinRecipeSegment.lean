import Orig2.TwinTransferRiderFree
import Orig2.TwinSwapRecipe
import Orig2.TwinSwapUnique
import Orig2.TwinDrawTransfer

/-!
# Temp/TwinRecipeSegment — the recipe segment is a `SwappableIn` equivalence

The exact 3-leg pair-foundation detour
`[tabToFound x.twin, tabToTab x (inr z.twin), foundToTab x.twin (inr z)]`
is a strict twin swap from its origin to its endpoint.  Since the endpoint
is also in the origin's reversible orbit, `SwappableIn` transfers both ways.

House compliance: new file only; no admitted goals, no choice principle.
-/

/-! ## §0. Exposing a walk's first step -/

private theorem walk_cons_inv {P : State → Move → Prop}
    {st s' : State} {m : Move} {ρ : List Move}
    (h : Walk P st (m :: ρ) s') :
    ∃ s1, P st m ∧ State.step st m = some s1 ∧ Walk P s1 ρ s' := by
  cases h with
  | cons hlet hstep hrest => exact ⟨_, hlet, hstep, hrest⟩

/-! ## §1. Private list and twin arithmetic -/

/-- **The recipe's endpoint is a strict swap of its origin.** -/
private theorem twinPairSwapStrict_recipe_endpoint
    {u w : State} {x z : Card} {a : Anchor}
    (hwfu : u.WF) (hwfw : w.WF)
    (hc : seatOf u x = some (Sum.inr z))
    (hct : seatOf u x.twin = some (Sum.inr z.twin))
    (hpa : u.pileOfTop x.twin = some a)
    (hraise : reversibleAtW u (Move.tabToFound x.twin))
    (hrecipe : ShufflePlayW u
      [Move.tabToFound x.twin, Move.tabToTab x (Sum.inr z.twin),
        Move.foundToTab x.twin (Sum.inr z)] w) :
    twinPairSwapStrict u w x := by
  -- Unpack the three recipe steps.
  obtain ⟨s1, _, hstep1, rest1⟩ := walk_cons_inv hrecipe
  obtain ⟨s2, hrev2, hstep2, rest2⟩ := walk_cons_inv rest1
  obtain ⟨s3, hrev3, hstep3, rest3⟩ := walk_cons_inv rest2
  have hrest3run : s3.run ([] : List Move) = some w := Walk_run _ rest3
  have hw3 : s3 = w := Option.some.inj (by simpa [State.run] using hrest3run)
  subst s3
  -- The two origin seats.
  obtain ⟨a0, hhold0, hb0ne, hlast0⟩ := tfc_seatOf_of_inr hc
  obtain ⟨at0, hholdt, hbtne, hlastt0⟩ := tfc_seatOf_of_inr hct
  -- The raise's successor shape.
  obtain ⟨hnx1, a1, hpa1, hs1eq⟩ := step_tabToFound_inv hstep1
  have ha1 : a1 = a := pileOfTop_inj hpa1 hpa
  subst a1
  let st1 : State :=
    { u.setFound x.twin.suit (u.found x.twin.suit ++ [x.twin]) with
      piles := fun a' => if a' = a then
          Pile.afterRunRemoved (u.piles a) (chop (u.piles a).faceUp)
        else u.piles a' }
  have hs1 : s1 = st1 := hs1eq
  subst s1
  have hwf1 : st1.WF := step_wf hwfu hstep1
  -- The raised twin is the donor top and its chop is nonempty.
  have hmemt : x.twin ∈ (u.piles a).faceUp :=
    lastOf_mem (tfc_pileOfTop_top hpa).2
  have hat : at0 = a := pileHolding_inj hholdt ((pileHolding_eq_some_iff hwfu).mpr hmemt)
  subst at0
  have htopa : lastOf (u.piles a).faceUp = some x.twin := (tfc_pileOfTop_top hpa).2
  have hfaceA : (u.piles a).faceUp = chop (u.piles a).faceUp ++ [x.twin] :=
    lastOf_chop htopa
  have hnodupA : (u.piles a).faceUp.Nodup := runOK_nodup (hwfu.runOK_of a)
  have hctNotChop : x.twin ∉ chop (u.piles a).faceUp := by
    rw [hfaceA] at hnodupA
    exact List.snoc_nodup_notMem _ _ hnodupA
  have hbelowT : below x.twin (u.piles a).faceUp = chop (u.piles a).faceUp := by
    conv =>
      lhs
      rw [hfaceA]
    exact below_snoc_not_mem hctNotChop
  have hlastChopT : lastOf (chop (u.piles a).faceUp) = some z.twin := by
    rw [← hbelowT]
    exact hlastt0
  have hchopNe : chop (u.piles a).faceUp ≠ [] := by
    intro h
    rw [h] at hlastChopT
    nomatch hlastChopT
  -- `x` does not sit in the donor pile.
  have ha0a : a0 ≠ a := by
    intro h
    have hmemX : x ∈ (u.piles a).faceUp := by
      rw [← h]
      exact pileHolding_mem hhold0
    rw [hfaceA] at hmemX
    rcases List.mem_append.mp hmemX with h1 | h2
    · have hrokA : runOK (chop (u.piles a).faceUp ++ [x.twin]) = true := by
        rw [← hfaceA]
        exact hwfu.runOK_of a
      have hlt := runOK_desc hrokA h1 (List.mem_singleton.mpr rfl)
      have hrank : x.twin.rank.toIdx = x.rank.toIdx := rfl
      omega
    · rcases List.mem_singleton.mp h2 with hxeq
      exact card_twin_ne x hxeq.symm
  -- The raise's field rows at `st1`.
  have hst1_pa : st1.piles a =
      Pile.afterRunRemoved (u.piles a) (chop (u.piles a).faceUp) := by
    simp only [st1, ite_true]
  have hst1_pne : ∀ a' ≠ a, st1.piles a' = u.piles a' := by
    intro a' ha'
    simp only [st1, ite_eq_right ha']
  have hst1_pa0 : st1.piles a0 = u.piles a0 := hst1_pne a0 ha0a
  have hst1_face : (st1.piles a).faceUp = chop (u.piles a).faceUp := by
    rw [hst1_pa, afterRunRemoved_faceUp_ne hchopNe]
  have hst1_top : st1.pileOfTop z.twin = some a := by
    rw [pileOfTop_eq_some_iff hwf1]
    show lastOf (st1.piles a).faceUp = some z.twin
    rw [hst1_face]
    exact hlastChopT
  have hst1_hold : st1.pileHolding x = some a0 := by
    rw [pileHolding_eq_some_iff hwf1, hst1_pa0]
    exact pileHolding_mem hhold0
  -- The slide's successor shape.
  obtain ⟨a0', hhold2, hcp2, hfr2, hs2eq⟩ := step_tabToTab_inv hstep2
  have ha0'a0 : a0' = a0 :=
    (Option.some.inj (hst1_hold.symm.trans hhold2)).symm
  subst a0'
  have hs2 : s2 = (st1.setPile a0
      (Pile.afterRunRemoved (st1.piles a0) (below x (st1.piles a0).faceUp))).putRun
        (fromCard x (st1.piles a0).faceUp) (Sum.inr z.twin) := hs2eq
  have hwf2 : s2.WF := step_wf hwf1 hstep2
  -- The slide's target set keeps the raised twin's top at `a` on top.
  have hQne : (Pile.afterRunRemoved (st1.piles a0)
      (below x (st1.piles a0).faceUp)).top ≠ some z.twin := by
    have hne : below x (st1.piles a0).faceUp ≠ [] := by
      rw [hst1_pa0]
      exact hb0ne
    have hQtop : (Pile.afterRunRemoved (st1.piles a0)
        (below x (st1.piles a0).faceUp)).top = some z := by
      show lastOf (Pile.afterRunRemoved (st1.piles a0)
        (below x (st1.piles a0).faceUp)).faceUp = some z
      rw [afterRunRemoved_faceUp_ne hne, hst1_pa0]
      exact hlast0
    rw [hQtop]
    intro h
    exact card_twin_ne z (Option.some.inj h).symm
  have hset_top : (st1.setPile a0
      (Pile.afterRunRemoved (st1.piles a0) (below x (st1.piles a0).faceUp))).pileOfTop z.twin
      = some a :=
    pileOfTop_setPile_ne hwf1 hst1_top ha0a hQne
  -- The slide leaves `x`'s base `z` on top at `a0`.
  have hs2_pa0 : s2.piles a0 = Pile.afterRunRemoved (st1.piles a0)
      (below x (st1.piles a0).faceUp) := by
    rw [hs2, putRun_piles_inr_ne _ _ _ _ hset_top ha0a, setPile_piles_self]
  have hs2_top : s2.pileOfTop z = some a0 := by
    rw [pileOfTop_eq_some_iff hwf2]
    show lastOf (s2.piles a0).faceUp = some z
    rw [hs2_pa0, hst1_pa0, afterRunRemoved_faceUp_ne hb0ne]
    exact hlast0
  -- The pull's successor shape.
  obtain ⟨c3, htop3, hc3, hcp3, hw3eq⟩ := step_foundToTab_inv hstep3
  subst c3
  have hloc3 : (s2.setFound x.twin.suit (chop (s2.found x.twin.suit))).pileOfTop z
      = some a0 := by
    unfold State.pileOfTop State.topOf
    rw [setFound_piles]
    exact hs2_top
  have hw_pa0 : w.piles a0 =
      { s2.piles a0 with faceUp := (s2.piles a0).faceUp ++ [x.twin] } := by
    rw [hw3eq, putCard_piles_inr _ _ _ a0 hloc3]
    dsimp only
    rw [ite_eq_left rfl, setFound_piles]
  -- The raised twin is absent from the slide's board.
  have hst1_seat_twin_none : seatOf st1 x.twin = none := by
    apply tfc_seatOf_none
    apply tfc_pileHolding_none
    intro a' hmem
    by_cases ha' : a' = a
    · subst ha'
      rw [hst1_face] at hmem
      exact hctNotChop hmem
    · rw [hst1_pne a' ha'] at hmem
      exact (mem_faceUp_unique hwfu hmemt a' ha').1 hmem
  have hs2_seat_twin_none : seatOf s2 x.twin = none := by
    have h := tfc_seat_point_edit hwf1 hstep2 hrev2 x.twin
    rw [h, ite_eq_right (card_twin_ne x), hst1_seat_twin_none]
  have hxt_notin_s2 : x.twin ∉ (s2.piles a0).faceUp :=
    tfc_not_mem_faceUp_of_holdNone (holdNone_of_seatNone hs2_seat_twin_none) a0
  -- The two exchanged seats.
  have hw_seat_x : seatOf w x = some (Sum.inr z.twin) := by
    have h1 : seatOf w x = seatOf s2 x :=
      pull_seat_change hstep3 x (fun h => card_twin_ne x h.symm)
    have h2 : seatOf s2 x = some (Sum.inr z.twin) := by
      have h := tfc_seat_point_edit hwf1 hstep2 hrev2 x
      rw [h]
      simp
    rw [h1, h2]
  have hw_seat_twin : seatOf w x.twin = some (Sum.inr z) := by
    have hbel : below x.twin (w.piles a0).faceUp = (s2.piles a0).faceUp := by
      rw [hw_pa0]
      exact below_snoc_not_mem hxt_notin_s2
    have hholdw : w.pileHolding x.twin = some a0 := by
      rw [pileHolding_eq_some_iff hwfw, hw_pa0]
      exact List.mem_append_right _ (List.mem_cons.mpr (Or.inl rfl))
    exact tfc_seatOf_inr_intro hholdw (by
      rw [hbel]
      exact (tfc_pileOfTop_top hs2_top).2)
  -- Every other seat is untouched.
  have hst1_hidden : ∀ a', (st1.piles a').hidden = (u.piles a').hidden := by
    intro a'
    by_cases ha' : a' = a
    · subst ha'
      rw [hst1_pa, afterRunRemoved_ne hchopNe]
    · rw [hst1_pne a' ha']
  have hs2_hidden : ∀ a', (s2.piles a').hidden = (u.piles a').hidden := by
    intro a'
    by_cases ha0' : a' = a0
    · subst ha0'
      rw [hs2, putRun_piles_inr_ne _ _ _ _ hset_top ha0a,
        setPile_piles_self, hst1_pa0, afterRunRemoved_ne hb0ne]
    · by_cases ha' : a' = a
      · subst ha'
        rw [hs2, putRun_piles_inr_self _ _ _ _ hset_top,
          setPile_piles_ne (Ne.symm ha0a), hst1_pa, afterRunRemoved_ne hchopNe]
      · rw [hs2, putRun_piles_inr_ne _ _ _ _ hset_top ha',
          setPile_piles_ne ha0', hst1_pne a' ha']
  have hw_hidden : ∀ a', (w.piles a').hidden = (u.piles a').hidden := by
    intro a'
    rw [hw3eq]
    rw [putCard_piles_inr _ _ _ a0 hloc3]
    dsimp only
    rw [setFound_piles]
    by_cases ha' : a' = a0
    · rw [ite_eq_left ha', ha']
      exact hs2_hidden a0
    · rw [ite_eq_right ha']
      exact hs2_hidden a'
  have hw_other : ∀ y, y ≠ x → y ≠ x.twin → seatOf w y = seatOf u y := by
    intro y hyx hyt
    have h1 : seatOf w y = seatOf s2 y := pull_seat_change hstep3 y hyt
    have h2 : seatOf s2 y = seatOf st1 y := by
      have h := tfc_seat_point_edit hwf1 hstep2 hrev2 y
      rw [h, ite_eq_right hyx]
    have h3 : seatOf st1 y = seatOf u y := by
      by_cases hs : seatOf u y = none
      · rw [hs]
        exact raise_none_of_chop_ne hstep1 hpa hchopNe hs
      · exact raise_seat_change_of_seated hstep1 hraise hs hyt
    rw [h1, h2, h3]
  -- The fixed readouts.
  have hs2_found : s2.found = st1.found := by
    rw [hs2, putRun_found, setPile_found]
  have hst1_found_self : st1.found x.twin.suit = u.found x.twin.suit ++ [x.twin] := by
    simp only [st1, setFound_found_self]
  have hst1_found_other : ∀ s ≠ x.twin.suit, st1.found s = u.found s := by
    intro s hs
    simp only [st1, setFound_found_ne hs]
  have hw_found : ∀ s, w.found s = u.found s := by
    intro s
    rw [hw3eq, putCard_found]
    by_cases hs : s = x.twin.suit
    · rw [hs, setFound_found_self, hs2_found, hst1_found_self, chop_snoc]
    · rw [setFound_found_ne hs, hs2_found, hst1_found_other s hs]
  have hs2_stock : s2.stock = u.stock := by
    rw [hs2, putRun_stock, setPile_stock]
    rfl
  have hs2_waste : s2.waste = u.waste := by
    rw [hs2, putRun_waste, setPile_waste]
    rfl
  have hs2_drawStep : s2.drawStep = u.drawStep := by
    rw [hs2, putRun_drawStep, setPile_drawStep]
    rfl
  have hw_stock : w.stock = u.stock := by
    rw [hw3eq, putCard_stock, setFound_stock, hs2_stock]
  have hw_waste : w.waste = u.waste := by
    rw [hw3eq, putCard_waste, setFound_waste, hs2_waste]
  have hw_drawStep : w.drawStep = u.drawStep := by
    rw [hw3eq, putCard_drawStep, setFound_drawStep, hs2_drawStep]
  -- Assemble the strict letter.
  refine ⟨?_, ?_, hw_other, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · rw [hw_seat_x, hct]
  · rw [hw_seat_twin, hc]
  · intro a'
    exact (hw_hidden a').symm
  · exact hw_drawStep.symm
  · intro s
    exact (hw_found s).symm
  · exact hw_stock.symm
  · exact hw_waste.symm
  · unfold cutOf
    rw [hw_stock]

/-- The strict twin-swap target is symmetric. -/
private theorem twinPairSwapStrict_symm {u v : State} {c : Card}
    (h : twinPairSwapStrict u v c) : twinPairSwapStrict v u c := by
  obtain ⟨h1, h2, h3, ⟨hhid, hds⟩, hf, hst, hwa, hcut⟩ := h
  refine ⟨h2.symm, h1.symm, ?_, ⟨fun a => (hhid a).symm, hds.symm⟩, ?_,
    hst.symm, hwa.symm, hcut.symm⟩
  · intro y hyc hyt
    exact (h3 y hyc hyt).symm
  · intro s
    exact (hf s).symm

theorem swappableIn_recipe_segment
    {u w : State} {x z : Card} {a : Anchor}
    (hwfu : u.WF) (hwfw : w.WF)
    (hc : seatOf u x = some (Sum.inr z))
    (hct : seatOf u x.twin = some (Sum.inr z.twin))
    (hpa : u.pileOfTop x.twin = some a)
    (hraise : reversibleAtW u (Move.tabToFound x.twin))
    (hrecipe : ShufflePlayW u
      [Move.tabToFound x.twin, Move.tabToTab x (Sum.inr z.twin),
        Move.foundToTab x.twin (Sum.inr z)] w)
    (_hrx : ∀ y, y ≠ x → seatOf u y ≠ some (Sum.inr x))
    (_hrt : ∀ y, y ≠ x.twin → seatOf u y ≠ some (Sum.inr x.twin))
    (_hrxw : ∀ y, y ≠ x → seatOf w y ≠ some (Sum.inr x))
    (_hrtw : ∀ y, y ≠ x.twin → seatOf w y ≠ some (Sum.inr x.twin)) :
    SwappableIn u x ↔ SwappableIn w x := by
  have hstrict : twinPairSwapStrict u w x :=
    twinPairSwapStrict_recipe_endpoint hwfu hwfw hc hct hpa hraise hrecipe
  have horb : RevEqW u w := shufflePlayW_revEqW hrecipe
  constructor
  · intro _
    exact ⟨u, twinPairSwapStrict_symm hstrict, horb⟩
  · intro _
    exact ⟨w, hstrict, RevEqW_symm horb⟩

#print axioms swappableIn_recipe_segment
