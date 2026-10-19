import Orig2.FloatOrbit
import Orig2.AnchorRelabel
import Orig2.SeatMateStack
import Orig2.StepWF

/-!
# Orig2.KingOrbitFull — the full-orbit king-assignment card

The bare-cargo card (`FloatOrbit` §M11) proves assignment completeness on
`BareCargoEquiv`.  This card lifts the readouts to the full reversible class:
`VKSet` is pointwise invariant along every reversible step (`vk_step_rev`),
hence along `ShufflePlayW`/`RevEqW`/`sameOrbit`; the vacancy trace and the
pending-king endgame then land the full `king_assignment_sameOrbit` row.
-/

/-- `VKSet` depends only on the piles. -/
theorem vk_congr_piles {u v : State} (hp : v.piles = u.piles) :
    ∀ j, VKSet u j ↔ VKSet v j := by
  intro j
  simp only [VKSet, VacantSpot, KingBottom, seatOf, State.pileHolding, hp]

/-- The bottom card of a pile is the head of its face-up run. -/
theorem kingBottom_iff_head {st : State} {a : Anchor} :
    KingBottom st a ↔
      (st.piles a).hidden = [] ∧
        ∃ c t, (st.piles a).faceUp = c :: t ∧ c.rank = Rank.king ∧
          st.pileHolding c = some a := by
  constructor
  · rintro ⟨c, hse, hk, hhid⟩
    obtain ⟨hhold, hbelow⟩ := tfc_seatOf_of_inl hse
    have hmem : c ∈ (st.piles a).faceUp := pileHolding_mem hhold
    have hhead : ∃ t, (st.piles a).faceUp = c :: t := by
      cases hf : (st.piles a).faceUp with
      | nil => rw [hf] at hmem; exact absurd hmem (by simp)
      | cons y t =>
          by_cases hyc : y = c
          · subst hyc; exact ⟨t, rfl⟩
          · exfalso
            have hb : below c (y :: t) = y :: below c t := by
              rw [below_cons, ite_eq_right hyc]
            rw [hf] at hbelow
            rw [hb] at hbelow
            exact absurd hbelow (by simp)
    obtain ⟨t, ht⟩ := hhead
    exact ⟨hhid, c, t, ht, hk, hhold⟩
  · rintro ⟨hhid, c, t, hface, hk, hhold⟩
    have hbelow : below c (st.piles a).faceUp = [] := by
      rw [hface, below_cons, ite_eq_left rfl]
    exact ⟨c, tfc_seatOf_inl_intro hhold hbelow, hk, hhid⟩

/-- Placing a card that is off the tableau preserves `VKSet` pointwise. -/
theorem vk_putCard {u v : State} {x : Card} {b : Base}
    (hwf : u.WF) (hwfv : v.WF)
    (hpiles : v.piles = (u.putCard x b).piles)
    (hcp : u.canPlace x b = true)
    (_hx_npile : ∀ j, x ∉ (u.piles j).faceUp) :
    ∀ j, VKSet u j ↔ VKSet (u.putCard x b) j := by
  have hpileHolding : (u.putCard x b).pileHolding = v.pileHolding := by
    funext c
    simp [State.pileHolding, hpiles]
  have hsearch_all : ∀ c a, (u.putCard x b).pileHolding c = some a ↔
      c ∈ ((u.putCard x b).piles a).faceUp := by
    intro c a
    rw [hpileHolding, ← hpiles]
    exact pileHolding_eq_some_iff hwfv
  intro j
  cases b with
  | inl a =>
      obtain ⟨hiso, hk⟩ := canPlace_inl hcp
      have hnewpile : (u.putCard x (Sum.inl a)).piles a = ⟨[], [x]⟩ := by
        rw [putCard_piles_inl]
        dsimp only
        rw [ite_eq_left rfl]
      by_cases hja : j = a
      · rw [hja]
        have hkb : KingBottom (u.putCard x (Sum.inl a)) a := by
          rw [kingBottom_iff_head]
          refine ⟨?_, x, [], ?_, hk, ?_⟩
          · rw [hnewpile]
          · rw [hnewpile]
          · exact (hsearch_all x a).mpr (by rw [hnewpile]; simp)
        constructor
        · intro _; exact Or.inr hkb
        · intro _; exact Or.inl hiso
      · have hpj : (u.putCard x (Sum.inl a)).piles j = u.piles j := by
          rw [putCard_piles_inl]
          dsimp only
          rw [ite_eq_right hja]
        have hne : (u.piles a).isEmpty = true := hiso
        constructor
        · rintro (hiso_j | hkb)
          · refine Or.inl ?_
            change ((u.putCard x (Sum.inl a)).piles j).isEmpty = true
            rw [hpj]
            exact hiso_j
          · obtain ⟨hhid, d, t, hdface, hdk, hdhold⟩ := (kingBottom_iff_head).mp hkb
            have hmem : d ∈ ((u.putCard x (Sum.inl a)).piles j).faceUp := by
              rw [hpj, hdface]; exact List.mem_cons_self ..
            have hhidden : ((u.putCard x (Sum.inl a)).piles j).hidden = [] := by
              rw [hpj]; exact hhid
            refine Or.inr ?_
            rw [kingBottom_iff_head]
            exact ⟨hhidden, d, t, by rw [hpj]; exact hdface, hdk,
              (hsearch_all d j).mpr hmem⟩
        · rintro (hiso_j | hkb)
          · refine Or.inl ?_
            change (u.piles j).isEmpty = true
            rw [← hpj]
            exact hiso_j
          · obtain ⟨hhid, d, t, hdface, hdk, hdhold⟩ := (kingBottom_iff_head).mp hkb
            have hmem : d ∈ (u.piles j).faceUp := by
              rw [← hpj, hdface]; exact List.mem_cons_self ..
            have hhidden : (u.piles j).hidden = [] := by rw [← hpj]; exact hhid
            refine Or.inr ?_
            rw [kingBottom_iff_head]
            exact ⟨hhidden, d, t, by rw [← hpj]; exact hdface, hdk,
              (pileHolding_eq_some_iff hwf).mpr hmem⟩
  | inr z =>
      obtain ⟨k, hz, hfit⟩ := canPlace_inr hcp
      have hnewpile : (u.putCard x (Sum.inr z)).piles k =
          { u.piles k with faceUp := (u.piles k).faceUp ++ [x] } := by
        rw [putCard_piles_inr u x z k hz]
        dsimp only
        rw [ite_eq_left rfl]
      by_cases hjk : j = k
      · rw [hjk]
        have hne : (u.piles k).faceUp ≠ [] := by
          have ht := (tfc_pileOfTop_top hz).1
          intro hnil; rw [hnil] at ht; simp at ht
        obtain ⟨d, t, hdface⟩ : ∃ d t, (u.piles k).faceUp = d :: t := by
          cases hf : (u.piles k).faceUp with
          | nil => exact absurd hf hne
          | cons d t => exact ⟨d, t, rfl⟩
        have hnewface : ((u.putCard x (Sum.inr z)).piles k).faceUp = d :: (t ++ [x]) := by
          rw [hnewpile, hdface]; rfl
        have hnewhidden : ((u.putCard x (Sum.inr z)).piles k).hidden = (u.piles k).hidden := by
          rw [hnewpile]
        have hne_new : ((u.putCard x (Sum.inr z)).piles k).faceUp ≠ [] := by
          rw [hnewface]; simp
        constructor
        · rintro (hiso | hkb)
          · exfalso
            change (u.piles k).isEmpty = true at hiso
            rw [Pile.isEmpty_eq] at hiso
            exact hne hiso.2
          · obtain ⟨hhid, d', t', hdface', hdk, hdhold⟩ := (kingBottom_iff_head).mp hkb
            have hdd : d' = d := by
              rw [hdface] at hdface'
              injection hdface' with h1 h2
              exact h1.symm
            have htt : t' = t := by
              rw [hdface] at hdface'
              injection hdface' with h1 h2
              exact h2.symm
            refine Or.inr ?_
            rw [kingBottom_iff_head]
            refine ⟨?_, d', t' ++ [x], ?_, hdk, ?_⟩
            · rw [hnewhidden, hhid]
            · rw [hnewface, ← hdd, ← htt]
            · exact (hsearch_all d' k).mpr (by
                rw [hnewface, ← hdd, ← htt]
                exact List.mem_cons_self ..)
        · rintro (hiso | hkb)
          · exfalso
            change ((u.putCard x (Sum.inr z)).piles k).isEmpty = true at hiso
            rw [Pile.isEmpty_eq] at hiso
            exact hne_new hiso.2
          · obtain ⟨hhid, d', t', hdface', hdk, hdhold⟩ := (kingBottom_iff_head).mp hkb
            have hdd : d' = d := by
              rw [hnewface] at hdface'
              injection hdface' with h1 h2
              exact h1.symm
            have htt : t' = t ++ [x] := by
              rw [hnewface] at hdface'
              injection hdface' with h1 h2
              exact h2.symm
            have hhidden : (u.piles k).hidden = [] := by
              rw [← hnewhidden]; exact hhid
            have hmem : d' ∈ (u.piles k).faceUp := by
              rw [hdface, ← hdd]; exact List.mem_cons_self ..
            refine Or.inr ?_
            rw [kingBottom_iff_head]
            refine ⟨hhidden, d', t, ?_, hdk, ?_⟩
            · rw [hdface, ← hdd]
            · exact (pileHolding_eq_some_iff hwf).mpr hmem
      · have hpj : (u.putCard x (Sum.inr z)).piles j = u.piles j := by
          rw [putCard_piles_inr u x z k hz]
          dsimp only
          rw [ite_eq_right hjk]
        constructor
        · rintro (hiso_j | hkb)
          · refine Or.inl ?_
            change ((u.putCard x (Sum.inr z)).piles j).isEmpty = true
            rw [hpj]
            exact hiso_j
          · obtain ⟨hhid, d, t, hdface, hdk, hdhold⟩ := (kingBottom_iff_head).mp hkb
            have hmem : d ∈ ((u.putCard x (Sum.inr z)).piles j).faceUp := by
              rw [hpj, hdface]; exact List.mem_cons_self ..
            have hhidden : ((u.putCard x (Sum.inr z)).piles j).hidden = [] := by
              rw [hpj]; exact hhid
            refine Or.inr ?_
            rw [kingBottom_iff_head]
            exact ⟨hhidden, d, t, by rw [hpj]; exact hdface, hdk,
              (hsearch_all d j).mpr hmem⟩
        · rintro (hiso_j | hkb)
          · refine Or.inl ?_
            change (u.piles j).isEmpty = true
            rw [← hpj]
            exact hiso_j
          · obtain ⟨hhid, d, t, hdface, hdk, hdhold⟩ := (kingBottom_iff_head).mp hkb
            have hmem : d ∈ (u.piles j).faceUp := by
              rw [← hpj, hdface]; exact List.mem_cons_self ..
            have hhidden : (u.piles j).hidden = [] := by rw [← hpj]; exact hhid
            refine Or.inr ?_
            rw [kingBottom_iff_head]
            exact ⟨hhidden, d, t, by rw [← hpj]; exact hdface, hdk,
              (pileHolding_eq_some_iff hwf).mpr hmem⟩


theorem chop_cons_of_tail_ne_nil {c : Card} {t : List Card} (ht : t ≠ []) :
    chop (c :: t) = c :: chop t := by
  cases t with
  | nil => exact absurd rfl ht
  | cons y ys => rfl

theorem mem_of_mem_chop {d : Card} : ∀ {l : List Card}, d ∈ chop l → d ∈ l := by
  intro l
  induction l with
  | nil => intro h; simp [chop] at h
  | cons x xs ih =>
      cases xs with
      | nil => intro h; simp [chop] at h
      | cons y ys =>
          intro h
          simp only [chop] at h
          rcases List.mem_cons.mp h with h | h
          · rw [h]; exact List.mem_cons_self ..
          · exact List.mem_cons_of_mem x (ih h)

theorem below_chop_eq_of_mem {d : Card} : ∀ {l : List Card}, d ∈ chop l →
    below d (chop l) = below d l := by
  intro l
  induction l with
  | nil => intro h; simp [chop] at h
  | cons x xs ih =>
      cases xs with
      | nil => intro h; simp [chop] at h
      | cons y ys =>
          intro h
          simp only [chop] at h ⊢
          by_cases hdx : d = x
          · subst hdx
            simp [below]
          · rw [below_cons, below_cons, ite_eq_right (fun h => hdx h.symm), ite_eq_right (fun h => hdx h.symm)]
            congr 1
            exact ih (by
              rcases List.mem_cons.mp h with h | h
              · exact absurd h hdx
              · exact h)


/-- A pile-local change that leaves pile `j` untouched leaves `KingBottom j`
untouched. -/
theorem kingBottom_congr_of_pile_eq {u v : State} {j : Anchor}
    (hwf : u.WF) (hwf' : v.WF) (hp : v.piles j = u.piles j) :
    KingBottom u j ↔ KingBottom v j := by
  rw [kingBottom_iff_head, kingBottom_iff_head]
  constructor
  · rintro ⟨hhid, d, t, hdface, hdk, hdhold⟩
    have hmem : d ∈ (v.piles j).faceUp := by
      rw [hp, hdface]; exact List.mem_cons_self ..
    refine ⟨?_, d, t, ?_, hdk, ?_⟩
    · rw [hp]; exact hhid
    · rw [hp]; exact hdface
    · exact (pileHolding_eq_some_iff hwf').mpr hmem
  · rintro ⟨hhid, d, t, hdface, hdk, hdhold⟩
    have hmem : d ∈ (u.piles j).faceUp := by
      rw [← hp, hdface]; exact List.mem_cons_self ..
    refine ⟨?_, d, t, ?_, hdk, ?_⟩
    · rw [← hp]; exact hhid
    · rw [← hp]; exact hdface
    · exact (pileHolding_eq_some_iff hwf).mpr hmem

set_option maxHeartbeats 1200000 in
/-- A reversible raise preserves `VKSet` pointwise. -/
theorem mem_chop_of_below_nil {d : Card} : ∀ {l : List Card},
    d ∈ l → below d l = [] → chop l ≠ [] → d ∈ chop l := by
  intro l
  induction l with
  | nil => intro h; simp at h
  | cons x xs ih =>
      cases xs with
      | nil => intro _ _ hchop; simp [chop] at hchop
      | cons y ys =>
          intro hmem hbelow hchop
          simp only [chop]
          by_cases hdx : d = x
          · rw [hdx]; exact List.mem_cons_self ..
          · exfalso
            rw [below_cons, ite_eq_right (fun h => hdx h.symm)] at hbelow
            exact absurd hbelow (by simp)

theorem vk_raise {u v : State} {x : Card} (hwf : u.WF)
    (hstep : State.step u (Move.tabToFound x) = some v)
    (hrev : reversibleAtW u (Move.tabToFound x)) :
    ∀ j, VKSet u j ↔ VKSet v j := by
  obtain ⟨hn, a, hp, hv⟩ := step_tabToFound_inv hstep
  have hwfv : v.WF := step_wf hwf hstep
  have hR : tabToFoundR u x = true := (tabToFoundR_iff_reversibleAtW hwf x).mpr hrev
  have hnewpile : v.piles a = Pile.afterRunRemoved (u.piles a) (chop (u.piles a).faceUp) := by
    rw [hv]
    dsimp only
    rw [ite_eq_left rfl]
  have hpj_all : ∀ j, j ≠ a → v.piles j = u.piles j := by
    intro j hj
    rw [hv]
    dsimp only
    rw [ite_eq_right hj]
  by_cases hempty : (v.piles a).isEmpty = true
  · -- bare-king raise: KingBottom at the donor becomes VacantSpot
    obtain ⟨hface, hhidden⟩ := (KingFuel.raise_empties_iff hstep hp).mp hempty
    have hking : x.rank = Rank.king :=
      KingFuel.emptying_raise_is_king hstep hrev hp hempty
    have hmem : x ∈ (u.piles a).faceUp := by rw [hface]; simp
    have hhold : u.pileHolding x = some a :=
      (pileHolding_eq_some_iff hwf).mpr hmem
    have hbelow : below x (u.piles a).faceUp = [] := by rw [hface]; simp [below]
    have hkb : KingBottom u a := ⟨x, tfc_seatOf_inl_intro hhold hbelow, hking, hhidden⟩
    intro j
    by_cases hja : j = a
    · rw [hja]
      constructor
      · intro _; exact Or.inl hempty
      · intro _; exact Or.inr hkb
    · have hpj : v.piles j = u.piles j := hpj_all j hja
      constructor
      · rintro (hiso | hkb')
        · exact Or.inl (by
            change (v.piles j).isEmpty = true
            rw [hpj]; exact hiso)
        · exact Or.inr ((kingBottom_congr_of_pile_eq hwf hwfv hpj).mp hkb')
      · rintro (hiso | hkb')
        · exact Or.inl (by
            change (u.piles j).isEmpty = true
            rw [← hpj]; exact hiso)
        · exact Or.inr ((kingBottom_congr_of_pile_eq hwf hwfv hpj).mpr hkb')
  · -- nonempty raise: the donor's bottom king, if any, is unchanged
    have hchop_ne : chop (u.piles a).faceUp ≠ [] := by
      intro hchop
      have hR' : tabToFoundR u x = false := by
        rw [tabToFoundR, hn, hp]
        dsimp only
        rw [hchop]
        cases hh : (u.piles a).hidden with
        | nil =>
            have hempty' : (v.piles a).isEmpty = true := by
              rw [hnewpile, hchop]
              simp [Pile.afterRunRemoved, Pile.revealTop, Pile.isEmpty, hh]
            exfalso
            exact hempty hempty'
        | cons h t => rfl
      rw [hR'] at hR
      exact Bool.noConfusion hR
    clear hR
    have hnewpile' : v.piles a = { u.piles a with faceUp := chop (u.piles a).faceUp } := by
      rw [hnewpile]
      cases hc : chop (u.piles a).faceUp with
      | nil => exact absurd hc hchop_ne
      | cons c cs => rfl
    intro j
    by_cases hja : j = a
    · rw [hja]
      have hnewface : (v.piles a).faceUp = chop (u.piles a).faceUp := by rw [hnewpile']
      constructor
      · rintro (hiso | hkb)
        · exfalso
          have hne : (u.piles a).faceUp ≠ [] := by
            have ht := (tfc_pileOfTop_top hp).1
            intro hnil; rw [hnil] at ht; simp at ht
          change (u.piles a).isEmpty = true at hiso
          rw [Pile.isEmpty_eq] at hiso
          exact hne hiso.2
        · obtain ⟨d, hse, hdk, hhid⟩ := hkb
          obtain ⟨hhold_old, hbelow_old⟩ := tfc_seatOf_of_inl hse
          have hd_mem_old : d ∈ (u.piles a).faceUp := pileHolding_mem hhold_old
          have hd_mem_chop : d ∈ chop (u.piles a).faceUp :=
            mem_chop_of_below_nil hd_mem_old hbelow_old hchop_ne
          have hbelow_chop : below d (chop (u.piles a).faceUp) = [] := by
            rw [below_chop_eq_of_mem hd_mem_chop]; exact hbelow_old
          have hmem : d ∈ (v.piles a).faceUp := by rw [hnewface]; exact hd_mem_chop
          have hhold_new : v.pileHolding d = some a :=
            (pileHolding_eq_some_iff hwfv).mpr hmem
          have hbelow_new : below d (v.piles a).faceUp = [] := by
            rw [hnewface]; exact hbelow_chop
          have hhidden_new : (v.piles a).hidden = [] := by
            rw [hnewpile']; exact hhid
          exact Or.inr ⟨d, tfc_seatOf_inl_intro hhold_new hbelow_new, hdk, hhidden_new⟩
      · rintro (hiso | hkb)
        · exfalso
          have hne : (v.piles a).faceUp ≠ [] := by
            rw [hnewface]; exact fun h => hchop_ne h
          change (v.piles a).isEmpty = true at hiso
          rw [Pile.isEmpty_eq] at hiso
          exact hne hiso.2
        · obtain ⟨d, hse, hdk, hhid⟩ := hkb
          obtain ⟨hhold_new, hbelow_new⟩ := tfc_seatOf_of_inl hse
          have hd_mem_new : d ∈ (v.piles a).faceUp := pileHolding_mem hhold_new
          have hd_mem_chop : d ∈ chop (u.piles a).faceUp := by
            rw [← hnewface]; exact hd_mem_new
          have hbelow_chop : below d (chop (u.piles a).faceUp) = [] := by
            rw [← hnewface]; exact hbelow_new
          have hbelow_old : below d (u.piles a).faceUp = [] := by
            rw [← below_chop_eq_of_mem hd_mem_chop]; exact hbelow_chop
          have hd_mem_old : d ∈ (u.piles a).faceUp := mem_of_mem_chop hd_mem_chop
          have hhold_old : u.pileHolding d = some a :=
            (pileHolding_eq_some_iff hwf).mpr hd_mem_old
          have hhidden_old : (u.piles a).hidden = [] := by
            rw [hnewpile'] at hhid; exact hhid
          exact Or.inr ⟨d, tfc_seatOf_inl_intro hhold_old hbelow_old, hdk, hhidden_old⟩
    · have hpj : v.piles j = u.piles j := hpj_all j hja
      constructor
      · rintro (hiso | hkb')
        · exact Or.inl (by
            change (v.piles j).isEmpty = true
            rw [hpj]; exact hiso)
        · exact Or.inr ((kingBottom_congr_of_pile_eq hwf hwfv hpj).mp hkb')
      · rintro (hiso | hkb')
        · exact Or.inl (by
            change (u.piles j).isEmpty = true
            rw [← hpj]; exact hiso)
        · exact Or.inr ((kingBottom_congr_of_pile_eq hwf hwfv hpj).mpr hkb')


#print axioms vk_congr_piles
#print axioms kingBottom_iff_head
#print axioms vk_putCard
#print axioms vk_raise

set_option maxHeartbeats 1200000 in
/-- `VKSet` is pointwise invariant along every reversible step. -/
theorem vk_step_rev {u v : State} {m : Move} (hwf : u.WF)
    (hstep : State.step u m = some v) (hrev : reversibleAtW u m) :
    ∀ j, VKSet u j ↔ VKSet v j := by
  intro j
  cases m with
  | draw =>
      have hsd : u.stepDraw = some v := by
        have h0 : State.step u Move.draw = u.stepDraw := rfl
        rw [h0] at hstep
        exact hstep
      have hp : v.piles = u.piles := (draw_footprint hsd).2.2.1
      exact vk_congr_piles hp j
  | wasteToFound x =>
      obtain ⟨-, y, ys, hw, hs⟩ := step_wasteToFound_inv hstep
      have hp : v.piles = u.piles := by rw [hs]; rfl
      exact vk_congr_piles hp j
  | wasteToTab x b =>
      exact absurd hrev (wasteToTab_not_reversibleAtW u x b)
  | tabToFound x =>
      exact vk_raise hwf hstep hrev j
  | foundToTab x b =>
      obtain ⟨c', htop, hc'c, hcp, hs⟩ := step_foundToTab_inv hstep
      subst c'
      have hxfound : x ∈ u.found x.suit := lastOf_mem htop
      have hx_npile : ∀ j, x ∉ (u.piles j).faceUp := fun j =>
        ((mem_found_unique hwf hxfound).1 j).2
      rw [hs]
      have hwfv : ((u.setFound x.suit (chop (u.found x.suit))).putCard x b).WF := by
        rw [← hs]
        exact step_wf hwf hstep
      have hpiles : ((u.setFound x.suit (chop (u.found x.suit))).putCard x b).piles
          = (u.putCard x b).piles :=
        KingFuel.kf_setFound_putCard_piles u x.suit (chop (u.found x.suit)) x b
      have h1 : VKSet u j ↔ VKSet (u.putCard x b) j :=
        vk_putCard hwf hwfv hpiles hcp hx_npile j
      have h2 : VKSet (u.putCard x b) j ↔
          VKSet ((u.setFound x.suit (chop (u.found x.suit))).putCard x b) j :=
        vk_congr_piles hpiles j
      exact h1.trans h2
  | tabToTab x b =>
      exact orbit_vk_step hwf hstep hrev j

/-- `VKSet` is pointwise invariant along a witness shuffle. -/
theorem vk_walk_invariant {u v : State} {ρ : List Move}
    (h : ShufflePlayW u ρ v) :
    u.WF → ∀ j, VKSet u j ↔ VKSet v j := by
  induction h with
  | nil s => intro _ j; rfl
  | @cons st s1 W m ρ hrev hstep hrest ih =>
      intro hwf j
      have hwf1 : s1.WF := step_wf hwf hstep
      exact (vk_step_rev hwf hstep hrev j).trans (ih hwf1 j)

/-- `VKSet` is pointwise invariant along a witness-reversible pair. -/
theorem vk_revEqW_invariant {a b : State} (hwf : a.WF) (h : RevEqW a b) :
    ∀ j, VKSet a j ↔ VKSet b j := by
  obtain ⟨ρ, hρ, τ, hτ⟩ := h
  exact vk_walk_invariant hρ hwf

/-- `VKSet` is pointwise invariant along a `sameOrbitSetoid` class pair. -/
theorem vk_sameOrbit_invariant {a b : State} (hwf : a.WF)
    (h : sameOrbitSetoid.r a b) : ∀ j, VKSet a j ↔ VKSet b j := by
  obtain ⟨ρ, hρ, τ, hτ⟩ := h
  exact vk_walk_invariant hτ hwf

/-- The full-orbit assignment when the chosen class member `w` already carries
a vacant spot: the bare-cargo assignment runs at `w`, and the vacancy is the
same one the class supplies. -/
theorem king_assignment_sameOrbit_of_vacancy {st w : State} (hwfst : st.WF)
    (hclass : sameOrbitSetoid.r st w) (hvac : HasVacancy w)
    {τ : Card → Anchor} (hτ : KingInjection w τ) :
    ∃ w', sameOrbitSetoid.r st w' ∧
      ∀ c, KingBottomCard w c → seatOf w' c = some (Sum.inl (τ c)) := by
  have hwfw : w.WF := by
    obtain ⟨ρ, hρ, σ, hσ⟩ := hclass
    exact run_wf hwfst
      (Walk_run (P := fun st m => reversibleAtW st m) (st := st) (W := w) hσ)
  obtain ⟨w', hw'class, hseats⟩ :=
    king_assignment_class_all hwfw ⟨Steps.refl w, Steps.refl w⟩ hvac hτ
  refine ⟨w', ?_, hseats⟩
  show RevEqW w' st
  exact RevEqW_trans hw'class hclass

#print axioms vk_step_rev
#print axioms vk_walk_invariant
#print axioms vk_revEqW_invariant
#print axioms vk_sameOrbit_invariant
#print axioms king_assignment_sameOrbit_of_vacancy

/-- With no vacancy, the fuel set is exactly the bottomed-king set. -/
theorem vkSet_kingBottom_of_no_vacancy {st : State}
    (hne : ∀ a, ¬ (st.piles a).isEmpty = true) (j : Anchor) :
    VKSet st j ↔ KingBottom st j := by
  constructor
  · rintro (hiso | hkb)
    · exact absurd hiso (hne j)
    · exact hkb
  · exact Or.inr

#print axioms vkSet_kingBottom_of_no_vacancy

/-- Class vacancy is a class invariant. -/
theorem sameOrbitVacant_iff {st w : State} (h : sameOrbitSetoid.r st w) :
    SameOrbitVacant st ↔ SameOrbitVacant w := by
  constructor
  · rintro ⟨u, hsu, hv⟩
    exact ⟨u, sameOrbitSetoid.iseqv.trans (sameOrbitSetoid.iseqv.symm h) hsu, hv⟩
  · rintro ⟨u, hwu, hv⟩
    exact ⟨u, sameOrbitSetoid.iseqv.trans h hwu, hv⟩

/-- The assignment property at a member that already carries a vacancy. -/
theorem kingAssignmentAt_of_vacancy {st w : State} (hwf : st.WF)
    (hclass : sameOrbitSetoid.r st w) (hvac : HasVacancy w) :
    KingAssignmentAt w := by
  intro τ hτ
  obtain ⟨w', hst', hseats⟩ :=
    king_assignment_sameOrbit_of_vacancy hwf hclass hvac hτ
  refine ⟨w', ?_, hseats⟩
  exact sameOrbitSetoid.iseqv.trans (sameOrbitSetoid.iseqv.symm hclass) hst'

#print axioms sameOrbitVacant_iff
#print axioms kingAssignmentAt_of_vacancy

/-- A vacancy at the reference state makes its class vacant. -/
theorem sameOrbitVacant_of_vacancy {st : State} (h : HasVacancy st) :
    SameOrbitVacant st :=
  ⟨st, sameOrbitSetoid.iseqv.refl st, h⟩

#print axioms sameOrbitVacant_of_vacancy

/-- `NoVacancy` is the negation of `HasVacancy`. -/
theorem noVacancy_iff_not_hasVacancy (st : State) :
    NoVacancy st ↔ ¬ HasVacancy st := by
  constructor
  · intro h hv
    obtain ⟨a, ha⟩ := hv
    exact h a ha
  · intro h a ha
    exact h ⟨a, ha⟩

/-- A king can never be placed on a card. -/
theorem canSitOn_king_false {c z : Card} (hk : c.rank = Rank.king) :
    canSitOn c z = false := by
  rw [canSitOn]
  have hkidx : c.rank.toIdx = 12 := by rw [hk]; rfl
  have hzlt : z.rank.toIdx < 13 := Rank.toIdx_lt z.rank
  have h13 : decide (13 = z.rank.toIdx) = false :=
    decide_eq_false (by omega)
  simp [hkidx, h13]

/-- A bottom card that is also the last card of a nodup run is the whole run. -/
theorem eq_singleton_of_below_nil_lastOf {l : List Card} {x : Card}
    (hnd : l.Nodup) (hbelow : below x l = []) (hlast : lastOf l = some x) :
    l = [x] := by
  cases l with
  | nil => simp [lastOf] at hlast
  | cons y t =>
      have hyx : y = x := by
        by_cases h : y = x
        · exact h
        · exfalso
          have hb : below x (y :: t) = y :: below x t := by
            rw [below_cons, ite_eq_right h]
          rw [hb] at hbelow
          exact absurd hbelow (by simp)
      rw [hyx] at hlast hnd ⊢
      cases t with
      | nil => rfl
      | cons z t' =>
          exfalso
          have hlast' : lastOf (z :: t') = some x := by
            simpa [lastOf] using hlast
          have hxmem : x ∈ z :: t' := lastOf_mem hlast'
          have hxnot : x ∉ z :: t' := (List.nodup_cons.mp hnd).1
          exact hxnot hxmem

/-- `seatOf` depends only on the piles. -/
theorem seatOf_congr_piles {u v : State} (hp : v.piles = u.piles) (c : Card) :
    seatOf v c = seatOf u c := by
  simp [seatOf, State.pileHolding, hp]

/-- Along a reversible step between two no-vacancy states, a bottomed king
keeps its seat. -/
theorem seatOf_no_vacancy_step {u v : State} {m : Move} (hwf : u.WF)
    (hstep : State.step u m = some v) (hrev : reversibleAtW u m)
    (hne_u : NoVacancy u) (hne_v : NoVacancy v)
    {c : Card} (hc : KingBottomCard u c) :
    seatOf v c = seatOf u c := by
  obtain ⟨a, hkb, hseat⟩ := hc
  obtain ⟨d, hse_d, hk_d, hhid⟩ := hkb
  have hc_d : c = d := king_seat_injective hseat hse_d
  have hk_c : c.rank = Rank.king := by rw [hc_d, hk_d]
  cases m with
  | draw =>
      have hsd : u.stepDraw = some v := by
        have h0 : State.step u Move.draw = u.stepDraw := rfl
        rw [h0] at hstep
        exact hstep
      have hp : v.piles = u.piles := (draw_footprint hsd).2.2.1
      exact seatOf_congr_piles hp c
  | wasteToFound x =>
      obtain ⟨-, y, ys, hw, hs⟩ := step_wasteToFound_inv hstep
      have hp : v.piles = u.piles := by rw [hs]; rfl
      exact seatOf_congr_piles hp c
  | wasteToTab x b =>
      exact absurd hrev (wasteToTab_not_reversibleAtW u x b)
  | tabToFound x =>
      have hset : seatOf u c ≠ none := by rw [hseat]; simp
      have hcx : c ≠ x := by
        intro hcx
        obtain ⟨-, a', hp, hv⟩ := step_tabToFound_inv hstep
        obtain ⟨hhold, hbelow⟩ := tfc_seatOf_of_inl hseat
        have hx_seated : x ∈ (u.piles a).faceUp := by
          rw [hcx] at hseat
          exact pileHolding_mem (tfc_seatOf_of_inl hseat).1
        have hx_top : x ∈ (u.piles a').faceUp :=
          lastOf_mem (tfc_pileOfTop_top hp).2
        have haa : a' = a := by
          by_cases h : a' = a
          · exact h
          · exfalso
            exact ((mem_faceUp_unique hwf hx_seated a' h).1 hx_top)
        have hp_a : u.pileOfTop x = some a := by
          rw [← haa]
          exact hp
        have hlast : lastOf (u.piles a).faceUp = some c := by
          rw [hcx]
          exact (tfc_pileOfTop_top hp_a).2
        have hnd : (u.piles a).faceUp.Nodup := runOK_nodup (hwf.2.1 a)
        have hface : (u.piles a).faceUp = [c] :=
          eq_singleton_of_below_nil_lastOf hnd hbelow hlast
        have hface_x : (u.piles a).faceUp = [x] := by
          rw [hface, hcx]
        have hempty : (v.piles a).isEmpty = true :=
          (KingFuel.raise_empties_iff hstep hp_a).mpr ⟨hface_x, hhid⟩
        exact hne_v a hempty
      exact raise_seat_change_of_seated hstep hrev hset hcx
  | foundToTab x b =>
      have hcx : c ≠ x := by
        intro hcx
        obtain ⟨c', htop, hc'c, hcp, hs⟩ := step_foundToTab_inv hstep
        subst c'
        have hxfound : x ∈ u.found x.suit := lastOf_mem htop
        have hx_seated : x ∈ (u.piles a).faceUp := by
          rw [hcx] at hseat
          exact pileHolding_mem (tfc_seatOf_of_inl hseat).1
        exact ((mem_found_unique hwf hxfound).1 a).2 hx_seated
      exact pull_seat_change hstep c hcx
  | tabToTab x b =>
      have hcx : c ≠ x := by
        intro hcx
        obtain ⟨a0, hh, hcp, hfr, hs⟩ := step_tabToTab_inv hstep
        cases b with
        | inl k =>
            exact hne_u k (canPlace_inl hcp).1
        | inr z =>
            obtain ⟨k, hz, hfit⟩ := canPlace_inr hcp
            have hfit_c : canSitOn c z = true := by
              rw [hcx]
              exact hfit
            rw [canSitOn_king_false hk_c] at hfit_c
            exact absurd hfit_c (by simp)
      have h := tfc_seat_point_edit hwf hstep hrev c
      rw [h, ite_eq_right hcx]

#print axioms noVacancy_iff_not_hasVacancy
#print axioms canSitOn_king_false
#print axioms eq_singleton_of_below_nil_lastOf
#print axioms seatOf_congr_piles
#print axioms seatOf_no_vacancy_step

set_option maxHeartbeats 1200000 in
/-- In a vacancy-free class, a bottomed king keeps its seat along any witness
shuffle whose start is in the class. -/
theorem seatOf_walk_noVacant {base s v : State} {ρ ρrev : List Move}
    (hno : ∀ x, sameOrbitSetoid.r base x → NoVacancy x)
    (hs : sameOrbitSetoid.r base s)
    (h : ShufflePlayW s ρ v)
    (hrev : ShufflePlayW v ρrev base)
    (hwf : s.WF) {c : Card} (hc : KingBottomCard s c) :
    seatOf v c = seatOf s c := by
  revert base hno hrev c hwf hs hc
  induction h with
  | nil s =>
      intro base hno hs hrev hwf c hc
      rfl
  | @cons st s1 W m ρ hrev_step hstep hrest ih =>
      intro base hno hs hrev hwf c hc
      have hno_st : NoVacancy st := hno st hs
      obtain ⟨ρ_st, h_st, σ_st, hσ_st⟩ := hs
      have hstep_w : ShufflePlayW st [m] s1 :=
        Walk.cons hrev_step hstep (Walk.nil s1)
      have hfwd : ShufflePlayW base (σ_st ++ [m]) s1 :=
        ShufflePlayW_append hσ_st hstep_w
      have hrev_s1 : ShufflePlayW s1 (ρ ++ ρrev) base :=
        ShufflePlayW_append hrest hrev
      have hs1 : sameOrbitSetoid.r base s1 :=
        ⟨ρ ++ ρrev, hrev_s1, σ_st ++ [m], hfwd⟩
      have hno_s1 : NoVacancy s1 := hno s1 hs1
      have hwf1 : s1.WF := step_wf hwf hstep
      have hseat1 : seatOf s1 c = seatOf st c :=
        seatOf_no_vacancy_step hwf hstep hrev_step hno_st hno_s1 hc
      have hc1 : KingBottomCard s1 c := by
        obtain ⟨a, hkb, hseat⟩ := hc
        have hvk : VKSet s1 a :=
          (vk_step_rev hwf hstep hrev_step a).mp (Or.inr hkb)
        have hkb1 : KingBottom s1 a :=
          (vkSet_kingBottom_of_no_vacancy hno_s1 a).mp hvk
        exact ⟨a, hkb1, by rw [hseat1]; exact hseat⟩
      have ih' := ih (base := base) hno hs1 hrev hwf1 hc1
      exact ih'.trans hseat1

/-- The no-vacancy half of the king-orbit dichotomy. -/
theorem kingAssignmentFixed_of_not_vacant {st : State} (hwf : st.WF)
    (hno : ¬ SameOrbitVacant st) : KingAssignmentFixed st := by
  unfold KingAssignmentFixed
  intro w hw w' hw' τ hτ hseat c hc
  have hno_all : ∀ x, sameOrbitSetoid.r st x → NoVacancy x := by
    intro x hx
    rw [noVacancy_iff_not_hasVacancy]
    intro hvac
    exact hno ⟨x, hx, hvac⟩
  have hw_keep : sameOrbitSetoid.r st w := hw
  obtain ⟨ρw, hw_st, σw, hst_w⟩ := hw
  obtain ⟨ρw', hw'_st, σw', hst_w'⟩ := hw'
  have hwfw : w.WF := run_wf hwf
    (Walk_run (P := fun st m => reversibleAtW st m) (st := st) (W := w) hst_w)
  have hforward : ShufflePlayW w (ρw ++ σw') w' :=
    ShufflePlayW_append hw_st hst_w'
  have hseat_eq : seatOf w' c = seatOf w c :=
    @seatOf_walk_noVacant st w w' (ρw ++ σw') ρw' hno_all hw_keep hforward hw'_st hwfw c hc
  exact hseat_eq




#print axioms seatOf_walk_noVacant
#print axioms kingAssignmentFixed_of_not_vacant
