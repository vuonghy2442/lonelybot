import Orig2.FloatFiber
import Orig2.CargoKit

/-!
# Orig2.FloatOrbit — THE ORBIT-INVARIANCE CARD (the floater set is
a class invariant)

PROMOTION PROVENANCE (2026-10-17): dry-ran as the §H6 card of
`Temp/float_agent_check.lean` (the agent dry-run that certified the
floater claim book; compiled green with every head at
[propext, Quot.sound] — zero sorry, zero `Classical.choice`), and
installed at owner request ("create a new file for the new claim
floater_orbit_invariant").

THE CLAIM: along a reversible cargo leg — and hence along the whole
bare-cargo orbit — floater-hood per card is FIXED.  The twin-fiber
forcing pins a leg's target to the parent's twin; the only
top-flips per leg are the mover's parent (gains) and its twin
(loses) while every other top is preserved by relocation or
untouched; riders keep seats and targets; a bare king's leg permutes
the empty-pile set one-for-one.  Consequently the FLOATER SET —
which cards are floaters — is an invariant of the entire
`BareCargoEquiv` class: no sequence of reversible cargo plays can
create or destroy a floater.  This is the conservation law over the
orbit (the fiber card's characterization rows are the dynamics
laws; this row is the class invariant that makes the flat
class-characterization derivable).

KIT (2026-10-17 consolidation, owner call "full extraction"): the
per-file kit this card carried — the occurrence-count, list/run,
search, conservation-fence, seat, twin-algebra and leg-shape rows,
the one-point-edit row, the per-leg seat-relation chain kit (the
whole `tfc_*`/`tfa_*` family) — moved VERBATIM, per-row source
cites kept, to the shared home `Orig2/CargoKit.lean`, byte-identical
with the certified copy this card dry-ran as
(`Temp/float_agent_check.lean`); the 2026-10-17 cleanup pass first
pruned three never-referenced rows at every home
(`tfc_cnt_singleton`, `tfc_cntFlat_map_congr`, and the fresh
`fli_cnt_append_left`).  This card's OWN fresh rows stay here:
the three calculus rows (`fli_below_last_absurd`,
`fli_belownil_head`, `fli_twin_inj`) and the §L0 placement
constructors (`tfa_canPlace_inl`/`tfa_canPlace_inr`/`tfa_fit_twin`).
-/


/-! ### §H6. THE ORBIT-INVARIANCE CARD — along a reversible cargo leg
(and hence along the whole bare-cargo orbit), floater-hood per card
is FIXED: the twin-fiber forcing pins the leg's target to the
parent's twin, the only top-flips are the mover's parent (gains) and
its twin (loses) while every other top is preserved by relocation or
untouched, riders keep seats and targets, and a bare king's leg
merely permutes the empty-pile set one-for-one.  The calculus row
behind the seating facts: a card directly on the LAST occurrence of a
once-only card, while that card is the list's last, doubles the
count. -/

/-- The end-position uniqueness (fresh): if y occurs at most once in
L, y is L's last element, and c sits directly on y (c's below ends
y), then y occurs twice — once below c, once in c's own run. -/
private theorem fli_below_last_absurd {L : List Card} {y c : Card}
    (hcount : tfc_cnt y L ≤ 1) (hmem : c ∈ L)
    (habove : lastOf (below c L) = some y) (hlast : lastOf L = some y) :
    False := by
  obtain ⟨R, hR⟩ := tfc_fromCard_cons_head _ hmem
  have hsplit : L = below c L ++ (c :: R) := by
    have h0 := tfc_below_fromCard c L
    rw [hR] at h0
    exact h0.symm
  have hc1 : 1 ≤ tfc_cnt y (below c L) :=
    tfc_mem_le_cnt _ (lastOf_mem habove)
  have hne : (c :: R : List Card) ≠ [] := by simp
  have hlast2 : lastOf (c :: R) = some y := by
    rw [← tfc_lastOf_append_ne (below c L) hne, ← hsplit]
    exact hlast
  have hc2 : 1 ≤ tfc_cnt y (c :: R) := tfc_mem_le_cnt _ (lastOf_mem hlast2)
  rw [hsplit] at hcount
  have h4 : tfc_cnt y (below c L ++ (c :: R))
      = tfc_cnt y (below c L) + tfc_cnt y (c :: R) := tfc_cnt_app y _ _
  omega

/-- A card whose below is empty inside a cons run is the run head
(the below prefix stops at the head). -/
private theorem fli_belownil_head {m : Card} {tr : List Card} {c : Card}
    (hbl : below c (m :: tr) = []) : c = m := by
  by_cases hmc : m = c
  · exact hmc.symm
  · rw [below_cons, ite_eq_right hmc] at hbl
    exact absurd hbl (by simp)

/-- Twin labeling is injective (the involution applied twice). -/
private theorem fli_twin_inj (p q : Card) (hh : p.twin = q.twin) : p = q := by
  rw [← tfc_card_twin_twin p, ← tfc_card_twin_twin q, hh]

/-- **floater_leg_invariant** — a single reversible cargo leg fixes
floater-hood: every card is as much a floater after the leg as
before. -/
theorem floater_leg_invariant {u v : State} (hwfu : u.WF)
    (hleg : CargoLeg u v) (c : Card) : Floater u c ↔ Floater v c := by
  obtain ⟨m, β, hstep, hrev⟩ := hleg
  have hwfv : v.WF := tfc_tabToTab_wf hwfu hstep
  have hcardU : ∀ x, u.cardCount x = 1 :=
    fun x => hwfu.2.2.1 x (Card.mem_universe x)
  have hcardV : ∀ x, v.cardCount x = 1 :=
    fun x => hwfv.2.2.1 x (Card.mem_universe x)
  have hexist : ∀ (s : State) (x : Card) (j : Anchor),
      lastOf ((s.piles j).faceUp) = some x → ∃ j', s.pileOfTop x = some j' := by
    intro s x j htop
    have h1 := tfc_firstWhere_mem_true
      (p := fun j' => decide (s.topOf j' = some x)) Anchor.all j
      (Anchor.mem_all j) (decide_eq_true (show s.topOf j = some x from htop))
    have h2 : s.pileOfTop x ≠ none := h1
    cases hq : s.pileOfTop x with
    | none => rw [hq] at h2; exact (h2 rfl).elim
    | some j' => exact ⟨j', rfl⟩
  obtain ⟨a, hholdm, hcpm, hbcell⟩ :=
    tfc_tabToTabR_inv ((tabToTabR_iff_reversibleAtW hwfu m β).mpr hrev)
  obtain ⟨a0, hhold0, -, -, hs1shape⟩ := step_tabToTab_inv hstep
  have ha0 : a0 = a := Option.some.inj (hhold0.symm.trans hholdm)
  rw [ha0] at hs1shape
  obtain ⟨tr, hcrr⟩ := tfc_fromCard_cons_head _ (pileHolding_mem hholdm)
  rw [hcrr] at hs1shape
  have hsplit : (u.piles a).faceUp
      = below m ((u.piles a).faceUp) ++ (m :: tr) := by
    have h0 := tfc_below_fromCard m ((u.piles a).faceUp)
    rw [hcrr] at h0
    exact h0.symm
  have hed := tfc_seat_point_edit hwfu hstep hrev
  obtain ⟨hbfUV, -, -, -⟩ := tfa_slide_conserves hwfu hstep hrev
  have hhidUV : ∀ j, (u.piles j).hidden = (v.piles j).hidden := hbfUV.1
  rw [floater_classification u hwfu c, floater_classification v hwfv c]
  rcases hbcell with hbne | ⟨hb0, hhid, hkng⟩
  · -- THE COMPANY CELL: m sits on z, the target is forced to z.twin
    obtain ⟨z, hlz⟩ := lastOf_exists hbne
    obtain ⟨hsit, htopNone⟩ := tfc_seat_parent hwfu hholdm hlz
    have hmnk : m.rank ≠ Rank.king := by
      obtain ⟨hidx, -⟩ := (canSitOn_eq m z).mp hsit
      have hzlt := Rank.toIdx_lt z.rank
      intro hk
      have h12 : m.rank.toIdx = 12 := by rw [hk]; rfl
      omega
    have hneRun : (m :: tr : List Card) ≠ [] := by simp
    cases β with
    | inl a' =>
        exfalso
        obtain ⟨-, hking⟩ := canPlace_inl hcpm
        exact (hmnk hking).elim
    | inr w₀ =>
        obtain ⟨k, hlocw, hfitw⟩ := canPlace_inr hcpm
        rcases tfc_fitting_parent hfitw hsit with heq | heq
        · exfalso
          rw [heq] at hlocw
          rw [htopNone] at hlocw
          nomatch hlocw
        · rw [heq] at hlocw hfitw hs1shape
          have hka : k ≠ a := tfc_mover_pile_not_target hwfu hholdm hlocw hfitw
          have hak : a ≠ k := fun hh => hka hh.symm
          have hktop : lastOf ((u.piles k).faceUp) = some z.twin :=
            (tfc_pileOfTop_top hlocw).2
          have hczBm : tfc_cnt z (below m ((u.piles a).faceUp)) ≤ 1 := by
            have h2 := tfc_cnt_app z (below m ((u.piles a).faceUp)) (m :: tr)
            rw [← hsplit] at h2
            have h3 : tfc_cnt z ((u.piles a).faceUp) ≤ u.cardCount z :=
              tfc_faceUp_cnt_le_cardCount
            have h4 : u.cardCount z = 1 := hcardU z
            omega
          have hccZTX : tfc_cnt z.twin ((u.piles k).faceUp) ≤ 1 := by
            have h3 : tfc_cnt z.twin ((u.piles k).faceUp) ≤ u.cardCount z.twin :=
              tfc_faceUp_cnt_le_cardCount
            have h4 : u.cardCount z.twin = 1 := hcardU z.twin
            omega
          have hMk : (u.setPile a (Pile.afterRunRemoved (u.piles a)
              (below m ((u.piles a).faceUp)))).piles k = u.piles k :=
            setPile_piles_ne hka
          have hlocM : (u.setPile a (Pile.afterRunRemoved (u.piles a)
              (below m ((u.piles a).faceUp)))).pileOfTop z.twin = some k := by
            have hmidk : (u.setPile a (Pile.afterRunRemoved (u.piles a)
                (below m ((u.piles a).faceUp)))).topOf k = some z.twin := by
              show lastOf ((u.setPile a (Pile.afterRunRemoved (u.piles a)
                (below m ((u.piles a).faceUp)))).piles k).faceUp = some z.twin
              rw [hMk]
              exact hktop
            refine firstWhere_find (Anchor.mem_all k) (decide_eq_true hmidk) ?_
            intro j _ hjk
            by_cases hja : j = a
            · rw [hja]
              refine decide_false_of_not ?_
              intro hcon
              have hset : (u.setPile a (Pile.afterRunRemoved (u.piles a)
                  (below m ((u.piles a).faceUp)))).piles a
                  = Pile.afterRunRemoved (u.piles a)
                      (below m ((u.piles a).faceUp)) :=
                setPile_piles_self
              have hcon0 : lastOf (Pile.afterRunRemoved (u.piles a)
                  (below m ((u.piles a).faceUp))).faceUp = some z.twin := by
                have hp : ((u.setPile a (Pile.afterRunRemoved (u.piles a)
                    (below m ((u.piles a).faceUp)))).piles a).top = some z.twin := hcon
                rw [hset] at hp
                exact hp
              have hznew : z.twin ∈ (Pile.afterRunRemoved (u.piles a)
                  (below m ((u.piles a).faceUp))).faceUp := lastOf_mem hcon0
              have hzone : z.twin ∈ (Pile.afterRunRemoved (u.piles a)
                  (below m ((u.piles a).faceUp))).hidden
                  ++ (Pile.afterRunRemoved (u.piles a)
                    (below m ((u.piles a).faceUp))).faceUp :=
                List.mem_append.mpr (Or.inr hznew)
              have hzold : z.twin ∈ (u.piles a).hidden ++ (u.piles a).faceUp :=
                tfc_mem_afterRunRemoved_below_zone hzone
              have hzk : z.twin ∈ (u.piles k).hidden ++ (u.piles k).faceUp :=
                List.mem_append.mpr (Or.inr (lastOf_mem hktop))
              exact tfc_two_pile_zone_absurd hak (hcardU z.twin) hzold hzk
            · refine decide_false_of_not ?_
              intro hcon
              have hcon2 : u.topOf j = some z.twin := by
                have hp : ((u.setPile a (Pile.afterRunRemoved (u.piles a)
                    (below m ((u.piles a).faceUp)))).piles j).top = some z.twin := hcon
                rw [setPile_piles_ne hja] at hp
                exact hp
              exact hjk (tfc_top_search_unique (hcardU z.twin) hcon2 hktop)
          rw [putRun_inr_eq hlocM] at hs1shape
          have hAface : (v.piles a).faceUp = below m ((u.piles a).faceUp) := by
            rw [hs1shape, setPile_piles_ne hak, setPile_piles_self,
              afterRunRemoved_ne hbne]
          have hKface : (v.piles k).faceUp
              = (u.piles k).faceUp ++ (m :: tr) := by
            rw [hs1shape, setPile_piles_self, hMk]
          have hOther : ∀ j, j ≠ a → j ≠ k →
              (v.piles j).faceUp = (u.piles j).faceUp := by
            intro j hja hjk
            rw [hs1shape, setPile_piles_ne hjk, setPile_piles_ne hja]
          have hT1 : ∀ (x : Card) (j : Anchor), x ≠ z.twin →
              u.pileOfTop x = some j → ∃ j', v.pileOfTop x = some j' := by
            intro x j hxzt hlocx
            have htopj : lastOf ((u.piles j).faceUp) = some x :=
              (tfc_pileOfTop_top hlocx).2
            rcases Decidable.em (j = a) with hja | hja
            · rw [hja, hsplit, tfc_lastOf_append_ne _ hneRun] at htopj
              have hvtop : lastOf ((v.piles k).faceUp) = some x := by
                rw [hKface, tfc_lastOf_append_ne _ hneRun]
                exact htopj
              exact hexist v x k hvtop
            · rcases Decidable.em (j = k) with hjk | hjk
              · rw [hjk] at htopj
                exact absurd (Option.some.inj (htopj.symm.trans hktop)) hxzt
              · have hvtop : lastOf ((v.piles j).faceUp) = some x := by
                  rw [hOther j hja hjk]
                  exact htopj
                exact hexist v x j hvtop
          have hT2 : ∀ (x : Card) (j : Anchor), x ≠ z →
              v.pileOfTop x = some j → ∃ j', u.pileOfTop x = some j' := by
            intro x j hxz hlocx
            have htopj : lastOf ((v.piles j).faceUp) = some x :=
              (tfc_pileOfTop_top hlocx).2
            rcases Decidable.em (j = a) with hja | hja
            · rw [hja] at htopj
              have hzv : lastOf ((v.piles a).faceUp) = some z := by
                rw [hAface]
                exact hlz
              exact absurd (Option.some.inj (htopj.symm.trans hzv)) hxz
            · rcases Decidable.em (j = k) with hjk | hjk
              · rw [hjk, hKface, tfc_lastOf_append_ne _ hneRun] at htopj
                have hutop : lastOf ((u.piles a).faceUp) = some x := by
                  rw [hsplit, tfc_lastOf_append_ne _ hneRun]
                  exact htopj
                exact hexist u x a hutop
              · rw [hOther j hja hjk] at htopj
                exact hexist u x j htopj
          have hsitZU : ∀ c', c' ≠ m →
              seatOf u c' = some (Sum.inr z) → False := by
            intro c' hcm hse
            obtain ⟨q, hhq, -, hlc⟩ := tfc_seatOf_of_inr hse
            have hza : u.pileHolding z = some a := by
              have hzmem : z ∈ (u.piles a).faceUp :=
                mem_below _ (lastOf_mem hlz)
              refine tfc_pileHolding_pin hzmem ?_
              intro j hja
              exact tfc_faceUp_uniq_other hwfu hzmem hja
            have hzq : z ∈ (u.piles q).faceUp := mem_below _ (lastOf_mem hlc)
            have hqk : q = a := tfc_holding_pin' hwfu hza hzq
            rw [hqk] at hhq hlc
            have hcmema : c' ∈ (u.piles a).faceUp := pileHolding_mem hhq
            rw [hsplit] at hcmema
            rcases List.mem_append.mp hcmema with hm1 | hrun
            · rw [hsplit, tfc_below_mem_append_left _ _ hm1] at hlc
              exact fli_below_last_absurd hczBm hm1 hlc hlz
            · have hcnotBm : c' ∉ below m ((u.piles a).faceUp) := by
                intro hmem2
                exact tfc_two_mem_faceUp_absurd hwfu hsplit hmem2 hrun
              rw [hsplit] at hlc
              rw [(tfc_below_fromCard_excl c'
                (below m ((u.piles a).faceUp)) (m :: tr) hcnotBm).1] at hlc
              by_cases hbl2 : below c' (m :: tr) = []
              · exact hcm (fli_belownil_head hbl2)
              · rw [tfc_lastOf_append_ne _ hbl2] at hlc
                have h1 : z ∈ m :: tr := mem_below _ (lastOf_mem hlc)
                have h2 : z ∈ below m ((u.piles a).faceUp) := lastOf_mem hlz
                exact tfc_two_mem_faceUp_absurd hwfu hsplit h2 h1
          have hsitZTV : ∀ c', c' ≠ m →
              seatOf v c' = some (Sum.inr z.twin) → False := by
            intro c' hcm hse
            obtain ⟨q, hhq, -, hlc⟩ := tfc_seatOf_of_inr hse
            have hzmem : z.twin ∈ (v.piles k).faceUp := by
              rw [hKface]
              exact List.mem_append.mpr (Or.inl (lastOf_mem hktop))
            have hzk : v.pileHolding z.twin = some k := by
              refine tfc_pileHolding_pin hzmem ?_
              intro j hjk
              exact tfc_faceUp_uniq_other hwfv hzmem hjk
            have hzq : z.twin ∈ (v.piles q).faceUp :=
              mem_below _ (lastOf_mem hlc)
            have hqk : q = k := tfc_holding_pin' hwfv hzk hzq
            rw [hqk] at hhq hlc
            rw [hKface] at hlc
            have hcmem : c' ∈ (v.piles k).faceUp := pileHolding_mem hhq
            rw [hKface] at hcmem
            rcases List.mem_append.mp hcmem with hX | hrun
            · rw [tfc_below_mem_append_left _ _ hX] at hlc
              exact fli_below_last_absurd hccZTX hX hlc hktop
            · have hcnotX : c' ∉ (u.piles k).faceUp := by
                intro hmemX
                exact tfc_two_mem_faceUp_absurd hwfv hKface hmemX hrun
              have hdecomp : below c' ((u.piles k).faceUp ++ (m :: tr))
                  = (u.piles k).faceUp ++ below c' (m :: tr) :=
                (tfc_below_fromCard_excl c' (u.piles k).faceUp (m :: tr) hcnotX).1
              rw [hdecomp] at hlc
              by_cases hbl2 : below c' (m :: tr) = []
              · exact hcm (fli_belownil_head hbl2)
              · rw [tfc_lastOf_append_ne _ hbl2] at hlc
                have h1 : z.twin ∈ m :: tr := mem_below _ (lastOf_mem hlc)
                have h2 : z.twin ∈ (u.piles k).faceUp := lastOf_mem hktop
                exact tfc_two_mem_faceUp_absurd hwfv hKface h2 h1
          have hholdVm : v.pileHolding m = some k := by
            have hmem : m ∈ (v.piles k).faceUp := by
              rw [hKface]
              exact List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))
            refine tfc_pileHolding_pin hmem ?_
            intro j hjk
            rcases Decidable.em (j = a) with hja | hja
            · rw [hja, hAface]
              exact tfc_below_not_mem_self m _
            · rw [hOther j hja hjk]
              exact tfc_faceUp_uniq_other hwfu (pileHolding_mem hholdm) hja
          have hbelowmV : lastOf (below m ((v.piles k).faceUp)) = some z.twin := by
            have h1 : below m ((v.piles k).faceUp)
                = (u.piles k).faceUp ++ below m (m :: tr) := by
              rw [hKface]
              refine (tfc_below_fromCard_excl m (u.piles k).faceUp (m :: tr) ?_).1
              exact tfc_faceUp_uniq_other hwfu (pileHolding_mem hholdm) hka
            have h2 : below m (m :: tr) = [] := by
              rw [below_cons, ite_eq_left rfl]
            rw [h1, h2, List.append_nil]
            exact hktop
          have hlocVz : v.pileOfTop z = some a := by
            have hmidk : v.topOf a = some z := by
              show lastOf ((v.piles a).faceUp) = some z
              rw [hAface]
              exact hlz
            refine firstWhere_find (Anchor.mem_all a) (decide_eq_true hmidk) ?_
            intro j _ hja0
            rcases Decidable.em (j = k) with hjk | hjk
            · rw [hjk]
              refine decide_false_of_not ?_
              intro hcon
              have hcon0 : lastOf ((v.piles k).faceUp) = some z := hcon
              rw [hKface, tfc_lastOf_append_ne _ hneRun] at hcon0
              have hzrun : z ∈ m :: tr := lastOf_mem hcon0
              have hzv1 : z ∈ (v.piles a).faceUp := by
                rw [hAface]
                exact lastOf_mem hlz
              have hzv2 : z ∈ (v.piles k).faceUp := by
                rw [hKface]
                exact List.mem_append.mpr (Or.inr hzrun)
              exact tfc_two_pile_zone_absurd hak (hcardV z)
                (List.mem_append.mpr (Or.inr hzv1))
                (List.mem_append.mpr (Or.inr hzv2))
            · refine decide_false_of_not ?_
              intro hjj
              have hp0 : lastOf ((v.piles j).faceUp) = some z := hjj
              rw [hOther j hja0 hjk] at hp0
              have h1 := tfc_firstWhere_mem_true
                (p := fun a' => decide (u.topOf a' = some z)) Anchor.all j
                (Anchor.mem_all j)
                (decide_eq_true (show u.topOf j = some z from hp0))
              rw [show u.pileOfTop z
                    = firstWhere (fun a' => decide (u.topOf a' = some z)) Anchor.all
                  from rfl] at htopNone
              rw [htopNone] at h1
              exact h1 rfl
          by_cases hcm : c = m
          · rw [hcm]
            constructor
            · intro _
              rw [← tfc_card_twin_twin z] at hlocVz
              exact Or.inl ⟨z.twin, k, tfc_seatOf_inr_intro hholdVm hbelowmV,
                hholdVm, Or.inl ⟨a, hlocVz⟩⟩
            · intro _
              exact Or.inl ⟨z, a, tfc_seatOf_inr_intro hholdm hlz, hholdm,
                Or.inl ⟨k, hlocw⟩⟩
          · have hseVl : seatOf v c = seatOf u c := by
              have h := hed c
              rw [ite_eq_right (fun hh => hcm hh)] at h
              exact h
            have hseUl : seatOf u c = seatOf v c := hseVl.symm
            constructor
            · intro hspecU
              rcases hspecU with ⟨zp, ap, hseU, hholdU, harm⟩ |
                ⟨b, hseU, hking, hhid, aeq, hempty⟩
              · rcases harm with ⟨k0, hlocT0⟩ | ⟨hking2, -⟩
                · have hzpne : zp ≠ z := by
                    intro hh
                    rw [hh] at hseU
                    exact hsitZU c hcm hseU
                  have hxzt : zp.twin ≠ z.twin := fun hh =>
                    hzpne (fli_twin_inj zp z hh)
                  obtain ⟨j', hj'⟩ := hT1 zp.twin k0 hxzt hlocT0
                  have hholdVu : ∃ q, v.pileHolding c = some q := by
                    cases hq : v.pileHolding c with
                    | none =>
                        exfalso
                        have hnone := tfc_seatOf_none hq
                        rw [hseVl, hseU] at hnone
                        nomatch hnone
                    | some q => exact ⟨q, rfl⟩
                  obtain ⟨q0, hq0⟩ := hholdVu
                  exact Or.inl ⟨zp, q0, hseVl.trans hseU, hq0,
                    Or.inl ⟨j', hj'⟩⟩
                · exfalso
                  obtain ⟨q1, hhq1, -, hlc1⟩ := tfc_seatOf_of_inr hseU
                  obtain ⟨hsit1, -⟩ := tfc_seat_parent hwfu hhq1 hlc1
                  obtain ⟨hidx, -⟩ := (canSitOn_eq c zp).mp hsit1
                  have hzlt := Rank.toIdx_lt zp.rank
                  have h12 : c.rank.toIdx = 12 := by rw [hking2]; rfl
                  omega
              · obtain ⟨hhid', hfu'⟩ := (Pile.isEmpty_eq _).mp hempty
                have haeqa : aeq ≠ a := by
                  intro hh
                  rw [hh] at hempty
                  have hf := Pile.isEmpty_eq_false_of_mem (pileHolding_mem hholdm)
                  exact Bool.noConfusion (hf.symm.trans hempty)
                have haeqk : aeq ≠ k := by
                  intro hh
                  rw [hh] at hempty
                  have hf := Pile.isEmpty_eq_false_of_mem (lastOf_mem hktop)
                  exact Bool.noConfusion (hf.symm.trans hempty)
                refine Or.inr ⟨b, hseVl.trans hseU, hking, ?_, aeq, ?_⟩
                · rw [← hhidUV b]
                  exact hhid
                · exact (Pile.isEmpty_eq _).mpr
                    ⟨by rw [← hhidUV aeq]; exact hhid',
                     by rw [hOther aeq haeqa haeqk]; exact hfu'⟩
            · intro hspecV
              rcases hspecV with ⟨zp, ap, hseV, hholdV, harm⟩ |
                ⟨b, hseV, hking, hhid, aeq, hempty⟩
              · rcases harm with ⟨k0, hlocT0⟩ | ⟨hking2, -⟩
                · have hzpne : zp ≠ z.twin := by
                    intro hh
                    rw [hh] at hseV
                    exact hsitZTV c hcm hseV
                  have hxz : zp.twin ≠ z := fun hh =>
                    hzpne (by rw [← tfc_card_twin_twin zp, hh])
                  obtain ⟨j', hj'⟩ := hT2 zp.twin k0 hxz hlocT0
                  have hholdUu : ∃ q, u.pileHolding c = some q := by
                    cases hq : u.pileHolding c with
                    | none =>
                        exfalso
                        have hnone := tfc_seatOf_none hq
                        rw [hseUl, hseV] at hnone
                        nomatch hnone
                    | some q => exact ⟨q, rfl⟩
                  obtain ⟨q0, hq0⟩ := hholdUu
                  exact Or.inl ⟨zp, q0, hseUl.trans hseV, hq0,
                    Or.inl ⟨j', hj'⟩⟩
                · exfalso
                  obtain ⟨q1, hhq1, -, hlc1⟩ := tfc_seatOf_of_inr hseV
                  obtain ⟨hsit1, -⟩ := tfc_seat_parent hwfv hhq1 hlc1
                  obtain ⟨hidx, -⟩ := (canSitOn_eq c zp).mp hsit1
                  have hzlt := Rank.toIdx_lt zp.rank
                  have h12 : c.rank.toIdx = 12 := by rw [hking2]; rfl
                  omega
              · obtain ⟨hhid', hfu'⟩ := (Pile.isEmpty_eq _).mp hempty
                have haeqa : aeq ≠ a := by
                  intro hh
                  rw [hh] at hempty
                  have hf := Pile.isEmpty_eq_false_of_mem
                    (by rw [hAface]; exact lastOf_mem hlz)
                  exact Bool.noConfusion (hf.symm.trans hempty)
                have haeqk : aeq ≠ k := by
                  intro hh
                  rw [hh] at hempty
                  have hf := Pile.isEmpty_eq_false_of_mem
                    (by rw [hKface]; exact List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))
                  exact Bool.noConfusion (hf.symm.trans hempty)
                refine Or.inr ⟨b, hseUl.trans hseV, hking, ?_, aeq, ?_⟩
                · rw [hhidUV b]
                  exact hhid
                · exact (Pile.isEmpty_eq _).mpr
                    ⟨by rw [hhidUV aeq]; exact hhid',
                     by rw [← hOther aeq haeqa haeqk]; exact hfu'⟩
  · -- THE BARE CELL: a lone king vacates a fully-empty-hidden pile
    cases β with
    | inr w₀ =>
        exfalso
        obtain ⟨k, -, hfitw⟩ := canPlace_inr hcpm
        obtain ⟨hidx, -⟩ := (canSitOn_eq m w₀).mp hfitw
        have hlt := Rank.toIdx_lt w₀.rank
        have h12 : m.rank.toIdx = 12 := by rw [hkng]; rfl
        omega
    | inl a' =>
        have hA0a' : a ≠ a' := by
          intro heq
          rw [heq] at hholdm
          have hmem : m ∈ (u.piles a').faceUp := pileHolding_mem hholdm
          have hemp : (u.piles a').isEmpty = true := (canPlace_inl hcpm).1
          have hf := Pile.isEmpty_eq_false_of_mem hmem
          exact Bool.noConfusion (hf.symm.trans hemp)
        rw [putRun_eq_inl] at hs1shape
        have hfaceB : (u.piles a).faceUp = m :: tr := by
          have h0 := hsplit
          rw [hb0, List.nil_append] at h0
          exact h0
        have hpeqA : (v.piles a) = ⟨[], ([] : List Card)⟩ := by
          rw [hs1shape, setPile_piles_ne hA0a', setPile_piles_self, hb0,
            Pile.afterRunRemoved_bare hhid]
        have hWface : (v.piles a').faceUp = m :: tr := by
          rw [hs1shape, setPile_piles_self]
        have hOtherB : ∀ j, j ≠ a → j ≠ a' →
            (v.piles j).faceUp = (u.piles j).faceUp := by
          intro j hja hja'
          rw [hs1shape, setPile_piles_ne hja', setPile_piles_ne hja]
        have hTB1 : ∀ (x : Card) (j : Anchor),
            u.pileOfTop x = some j → ∃ j', v.pileOfTop x = some j' := by
          intro x j hlocx
          have htopj : lastOf ((u.piles j).faceUp) = some x :=
            (tfc_pileOfTop_top hlocx).2
          rcases Decidable.em (j = a) with hja | hja
          · rw [hja, hfaceB] at htopj
            have hvtop : lastOf ((v.piles a').faceUp) = some x := by
              rw [hWface]
              exact htopj
            exact hexist v x a' hvtop
          · rcases Decidable.em (j = a') with hja' | hja'
            · rw [hja'] at htopj
              exfalso
              rw [((Pile.isEmpty_eq _).mp (canPlace_inl hcpm).1).2] at htopj
              nomatch htopj
            · have hvtop : lastOf ((v.piles j).faceUp) = some x := by
                rw [hOtherB j hja hja']
                exact htopj
              exact hexist v x j hvtop
        have hTB2 : ∀ (x : Card) (j : Anchor),
            v.pileOfTop x = some j → ∃ j', u.pileOfTop x = some j' := by
          intro x j hlocx
          have htopj : lastOf ((v.piles j).faceUp) = some x :=
            (tfc_pileOfTop_top hlocx).2
          rcases Decidable.em (j = a) with hja | hja
          · rw [hja] at htopj
            exfalso
            rw [congrArg Pile.faceUp hpeqA] at htopj
            nomatch htopj
          · rcases Decidable.em (j = a') with hja' | hja'
            · rw [hja', hWface] at htopj
              have hutop : lastOf ((u.piles a).faceUp) = some x := by
                rw [hfaceB]
                exact htopj
              exact hexist u x a hutop
            · rw [hOtherB j hja hja'] at htopj
              exact hexist u x j htopj
        by_cases hcm : c = m
        · rw [hcm]
          constructor
          · intro _
            have hholdVm : v.pileHolding m = some a' := by
              have hmem : m ∈ (v.piles a').faceUp := by
                rw [hWface]
                exact List.mem_cons_self
              refine tfc_pileHolding_pin hmem ?_
              intro j hjk
              rcases Decidable.em (j = a) with hja | hja
              · rw [hja]
                intro hmemj
                rw [congrArg Pile.faceUp hpeqA] at hmemj
                exact absurd hmemj (by simp)
              · rw [hOtherB j hja hjk]
                exact tfc_faceUp_uniq_other hwfu (pileHolding_mem hholdm) hja
            refine Or.inr ⟨a', tfc_seatOf_inl_intro hholdVm
              (by rw [hWface, below_cons, ite_eq_left rfl]), hkng, ?_, a, ?_⟩
            · rw [hs1shape, setPile_piles_self]
            · rw [hpeqA]
              rfl
          · intro _
            exact Or.inr ⟨a, tfc_seatOf_inl_intro hholdm hb0, hkng, hhid, a',
              (canPlace_inl hcpm).1⟩
        · have hseVl : seatOf v c = seatOf u c := by
            have h := hed c
            rw [ite_eq_right (fun hh => hcm hh)] at h
            exact h
          have hseUl : seatOf u c = seatOf v c := hseVl.symm
          constructor
          · intro hspecU
            rcases hspecU with ⟨zp, ap, hseU, hholdU, harm⟩ |
              ⟨b, hseU, hking, hhid, aeq, hempty⟩
            · rcases harm with ⟨k0, hlocT0⟩ | ⟨hking2, -⟩
              · obtain ⟨j', hj'⟩ := hTB1 zp.twin k0 hlocT0
                have hholdVu : ∃ q, v.pileHolding c = some q := by
                  cases hq : v.pileHolding c with
                  | none =>
                      exfalso
                      have hnone := tfc_seatOf_none hq
                      rw [hseVl, hseU] at hnone
                      nomatch hnone
                  | some q => exact ⟨q, rfl⟩
                obtain ⟨q0, hq0⟩ := hholdVu
                exact Or.inl ⟨zp, q0, hseVl.trans hseU, hq0,
                  Or.inl ⟨j', hj'⟩⟩
              · exfalso
                obtain ⟨q1, hhq1, -, hlc1⟩ := tfc_seatOf_of_inr hseU
                obtain ⟨hsit1, -⟩ := tfc_seat_parent hwfu hhq1 hlc1
                obtain ⟨hidx, -⟩ := (canSitOn_eq c zp).mp hsit1
                have hzlt := Rank.toIdx_lt zp.rank
                have h12 : c.rank.toIdx = 12 := by rw [hking2]; rfl
                omega
            · obtain ⟨hhq2U, hbE2U⟩ := tfc_seatOf_of_inl hseU
              have hba : b ≠ a := by
                intro hh
                rw [hh] at hhq2U hbE2U
                exact hcm (fli_belownil_head (by rw [← hfaceB]; exact hbE2U))
              have hba' : b ≠ a' := by
                intro hh
                rw [hh] at hhq2U
                have hmem : c ∈ (u.piles a').faceUp := pileHolding_mem hhq2U
                have hemp : (u.piles a').isEmpty = true := (canPlace_inl hcpm).1
                have hf := Pile.isEmpty_eq_false_of_mem hmem
                exact Bool.noConfusion (hf.symm.trans hemp)
              refine Or.inr ⟨b, hseVl.trans hseU, hking, ?_, ?_⟩
              · rw [← hhidUV b]
                exact hhid
              · rcases Decidable.em (aeq = a') with haeq | haeq
                · exact ⟨a, by rw [hpeqA]; rfl⟩
                · have haeqa : aeq ≠ a := by
                    intro hh
                    rw [hh] at hempty
                    have hf := Pile.isEmpty_eq_false_of_mem
                      (by rw [hfaceB]; exact List.mem_cons_self)
                    exact Bool.noConfusion (hf.symm.trans hempty)
                  have hpq : (v.piles aeq) = (u.piles aeq) :=
                    Pile.ext (hhidUV aeq).symm (hOtherB aeq haeqa haeq)
                  exact ⟨aeq, by rw [hpq]; exact hempty⟩
          · intro hspecV
            rcases hspecV with ⟨zp, ap, hseV, hholdV, harm⟩ |
              ⟨b, hseV, hking, hhid, aeq, hempty⟩
            · rcases harm with ⟨k0, hlocT0⟩ | ⟨hking2, -⟩
              · obtain ⟨j', hj'⟩ := hTB2 zp.twin k0 hlocT0
                have hholdUu : ∃ q, u.pileHolding c = some q := by
                  cases hq : u.pileHolding c with
                  | none =>
                      exfalso
                      have hnone := tfc_seatOf_none hq
                      rw [hseUl, hseV] at hnone
                      nomatch hnone
                  | some q => exact ⟨q, rfl⟩
                obtain ⟨q0, hq0⟩ := hholdUu
                exact Or.inl ⟨zp, q0, hseUl.trans hseV, hq0,
                  Or.inl ⟨j', hj'⟩⟩
              · exfalso
                obtain ⟨q1, hhq1, -, hlc1⟩ := tfc_seatOf_of_inr hseV
                obtain ⟨hsit1, -⟩ := tfc_seat_parent hwfv hhq1 hlc1
                obtain ⟨hidx, -⟩ := (canSitOn_eq c zp).mp hsit1
                have hzlt := Rank.toIdx_lt zp.rank
                have h12 : c.rank.toIdx = 12 := by rw [hking2]; rfl
                omega
            · obtain ⟨hhq2, hbE2⟩ := tfc_seatOf_of_inl hseV
              have hba : b ≠ a := by
                intro hh
                rw [hh] at hhq2 hbE2
                have hmem : c ∈ (v.piles a).faceUp := pileHolding_mem hhq2
                rw [congrArg Pile.faceUp hpeqA] at hmem
                exact absurd hmem (by simp)
              have hba' : b ≠ a' := by
                intro hh
                rw [hh] at hhq2 hbE2
                exact hcm (fli_belownil_head (by rw [← hWface]; exact hbE2))
              refine Or.inr ⟨b, hseUl.trans hseV, hking, ?_, ?_⟩
              · rw [hhidUV b]
                exact hhid
              · rcases Decidable.em (aeq = a) with haeq | haeq
                · exact ⟨a', (canPlace_inl hcpm).1⟩
                · have haeqa' : aeq ≠ a' := by
                    intro hh
                    rw [hh] at hempty
                    have hf := Pile.isEmpty_eq_false_of_mem
                      (by rw [hWface]; exact List.mem_cons_self)
                    exact Bool.noConfusion (hf.symm.trans hempty)
                  have hpq : (v.piles aeq) = (u.piles aeq) :=
                    Pile.ext (hhidUV aeq).symm (hOtherB aeq haeq haeqa')
                  exact ⟨aeq, by rw [← hpq]; exact hempty⟩

/-- The chain lift of the leg row: one cargo direction suffices
(each leg is an iff). -/
private theorem floater_chain_invariant : ∀ {x y : State},
    Steps CargoLeg x y → x.WF → ∀ c, Floater x c ↔ Floater y c := by
  intro x y h
  induction h with
  | refl s =>
      intro _
      exact fun _ => Iff.rfl
  | @cons x0 x1 x2 hleg _ ih =>
      intro hwf0 c
      obtain ⟨m₀, b₀, hstep₀, hrev₀⟩ := hleg
      rw [floater_leg_invariant hwf0 ⟨m₀, b₀, hstep₀, hrev₀⟩ c]
      exact ih (tfc_tabToTab_wf hwf0 hstep₀) c

/-- **floater_orbit_invariant** — the bare-cargo orbit fixes the
floater SET, card by card: a card is a floater at one end of the
class exactly when it is a floater at the other. -/
theorem floater_orbit_invariant {st w : State} {c : Card}
    (hpair : BareCargoEquiv st w) (hwf : st.WF) : Floater st c ↔ Floater w c :=
  floater_chain_invariant hpair.1 hwf c


/-! ### §J. THE FLAT CLASS-CHARACTERIZATION DIRECTION — Stage 2 of
the reformulation plan: every class-mate's chart difference and its
readouts, with the st-side licensing DERIVED, not assumed (no round
trip, no hypothesis — one cargo direction suffices). -/

/-- **floater_path_invariant** — the one-way companion: a single
cargo DIRECTION already fixes floater-hood per card (each leg is an
iff, so the return path adds nothing). -/
theorem floater_path_invariant {st u : State} (hpath : Steps CargoLeg st u)
    (hwf : st.WF) (c : Card) : Floater st c ↔ Floater u c :=
  floater_chain_invariant hpath hwf c

/-- Conserved readouts along a reversible cargo journey (the
per-leg conservation row composed by chain induction). -/
private theorem orbit_readout_conserves : ∀ {x0 y : State},
    Steps CargoLeg x0 y → x0.WF →
    boardFixed x0 y ∧ foundsFixed x0 y ∧
      drawPool x0 = drawPool y ∧ cutOf x0 = cutOf y := by
  intro x0 y hpath
  induction hpath with
  | refl s =>
      intro _
      exact ⟨⟨fun _ => rfl, rfl⟩, fun _ => rfl, rfl, rfl⟩
  | @cons x1 x2 x3 hleg hrest ih =>
      intro hwf0
      obtain ⟨m, b, hstep, hrev⟩ := hleg
      have hwf2 := tfc_tabToTab_wf hwf0 hstep
      obtain ⟨bf1, ff1, dp1, co1⟩ := tfa_slide_conserves hwf0 hstep hrev
      obtain ⟨h1, h2⟩ := bf1
      obtain ⟨bf2, ff2, dp2, co2⟩ := ih hwf2
      obtain ⟨g1, g2⟩ := bf2
      exact ⟨⟨fun j => (h1 j).trans (g1 j), h2.trans g2⟩,
        fun s0 => (ff1 s0).trans (ff2 s0), dp1.trans dp2, co1.trans co2⟩

/-- THE MOVERS WITNESS: a card whose seat differs between a journey's
ends was some prefix-endpoint's mover (riders keep seats at every
leg, so the unequal seat pins the card to the leg that moved it):
some prefix of the journey ends at a state from which the card's
own reversible leg fires. -/
private theorem orbit_changed_moverWitness : ∀ {x0 y : State},
    Steps CargoLeg x0 y → x0.WF → ∀ c,
    seatOf x0 c ≠ seatOf y c →
    ∃ (u : State) (b : Base), Steps CargoLeg x0 u ∧
      reversibleAtW u (Move.tabToTab c b) := by
  intro x0 y hpath
  induction hpath with
  | refl s =>
      intro _ c hc
      exact absurd rfl hc
  | @cons x1 x2 x3 hleg hrest ih =>
      intro hwf0 c hc
      obtain ⟨m, b, hstep, hrev⟩ := id hleg
      have hwf2 := tfc_tabToTab_wf hwf0 hstep
      have hed := tfc_seat_point_edit hwf0 hstep hrev
      by_cases hcm : c = m
      · exact ⟨x1, b, Steps.refl x1, by rw [hcm]; exact hrev⟩
      · have hx2 := hed c
        rw [ite_eq_right hcm] at hx2
        obtain ⟨u, b', hpathU, hrevU⟩ :=
          ih hwf2 c (fun heq => hc (hx2.symm.trans heq))
        exact ⟨u, b', Steps.cons hleg hpathU, hrevU⟩

/-- THE DERIVED ST LICENSING: with the movers witness above, the
changed card's reversible leg fires at the end of some prefix, and
the one-way path invariance transports its floater-hood back to the
journey origin — the classification re-exports the spec at st: the
twin-pile or empty-pile target existence LITERALLY at the origin. -/
private theorem orbit_changed_is_stFloater : ∀ {x0 y : State},
    Steps CargoLeg x0 y → x0.WF → ∀ c,
    seatOf x0 c ≠ seatOf y c → FloaterSpec x0 c := by
  intro x0 y hpath hwf0 c hc
  obtain ⟨u, b, hpathU, hrevU⟩ := orbit_changed_moverWitness hpath hwf0 c hc
  exact (floater_classification x0 hwf0 c).mp
    ((floater_path_invariant hpathU hwf0 c).mpr ⟨b, hrevU⟩)

/-- **bareCargo_to_chartDiff** — Stage 2 of the flat reformulation:
every bare-cargo class-mate differs from the origin by (i) the
per-card three-way net seat relation (carried, one twin-hop, or a
bare king's empty-seat change — the chain invariant), (ii) conserved
readouts (hidden decks and deal quantum, foundation rows, pool,
cut), and (iii) DERIVED st-side licensing: every net-changed card
satisfies the FloaterSpec LITERALLY at the origin.  The flat
"condition at st" RHS of the planned class iff is sound from here
on; only the reconstruction (Stage 3, the safe-order commutation
card) remains priced. -/
theorem bareCargo_to_chartDiff {st w : State} (hwf : st.WF)
    (hpair : BareCargoEquiv st w) :
    (∀ c, (seatOf w c = seatOf st c) ∨
      (∃ z, seatOf st c = some (Sum.inr z) ∧ seatOf w c = some (Sum.inr z.twin)) ∨
      (c.rank = Rank.king ∧ ∃ a a', seatOf st c = some (Sum.inl a) ∧
         seatOf w c = some (Sum.inl a'))) ∧
    (boardFixed st w ∧ foundsFixed st w ∧
       drawPool st = drawPool w ∧ cutOf st = cutOf w) ∧
    (∀ c, seatOf st c ≠ seatOf w c → FloaterSpec st c) := by
  obtain ⟨hpath, -⟩ := hpair
  obtain ⟨-, hrel⟩ := tfc_chain_inv hpath hwf
  exact ⟨hrel, orbit_readout_conserves hpath hwf,
    fun c hc => orbit_changed_is_stFloater hpath hwf c hc⟩

/-! ### §K. StAGE 3A — THE SINGLE-EDIT RECONSTRUCTION (the flat
iff's reconstruction half at one point: when the flat condition's
entire change is ONE card's point edit — every other seat carried,
the edit value pinned, the mover licensed at a live cell, the
readouts agreed — the mate is genuine.  The reverse-layer row does
the work behind the SeatEdit assembly; this row makes the
flat-to-cash conversion explicit, and is the compose-unit the
ordered multi-hop reconstruction (Stage 3B, the safe-order
commutation card) will compose. -/

/-- **bareCargo_reconstruct_singleEdit** — Stage 3a of the flat
reformulation: the single-edit reconstruction. -/
theorem bareCargo_reconstruct_singleEdit {st w : State} (hwf : st.WF)
    (hroundtrip : ∀ A B, chartAgree A B → A = B)
    {c : Card} {β : Base}
    (hcarried : ∀ x, x ≠ c → seatOf w x = seatOf st x)
    (hval : seatOf w c = some β)
    (hmove : st.canPlace c β = true)
    (hcell : FloaterCell st c)
    (hread : boardFixed st w ∧ foundsFixed st w ∧
      drawPool st = drawPool w ∧ cutOf st = cutOf w) :
    BareCargoEquiv st w := by
  obtain ⟨hbf, hff, hdp, hco⟩ := hread
  refine floater_seat_to_equiv' hwf hroundtrip ⟨?_, hbf, hff, hdp, hco⟩ hmove hcell
  intro x
  by_cases hxc : x = c
  · rw [hxc, if_pos rfl]
    exact hval
  · rw [if_neg hxc]
    exact hcarried x hxc

/-! ### §L. StAGE 3B — THE TWO-HOP DISJOINT RECONSTRUCTION (the flat
iff's reconstruction half for two movers in disjoint twin-fibers;
the compose-unit and the license-preservation embryo of the
safe-order commutation card) -/

/-! ### §L0. The placement constructors, the twin fit, and the class
transitivity (PORT of `Orig2/FloatFiber.lean` §H1's three tiny
constructors; per the per-file restatement, their sources stand) -/

/-- The empty-seat placement, constructed. -/
private theorem tfa_canPlace_inl {st : State} {c : Card} {a : Anchor}
    (hemp : (st.piles a).isEmpty = true) (hkng : c.rank = Rank.king) :
    st.canPlace c (Sum.inl a) = true := by
  simp only [State.canPlace, Bool.and_eq_true]
  exact ⟨hemp, decide_eq_true hkng⟩

/-- The located card-on-card placement, constructed. -/
private theorem tfa_canPlace_inr {st : State} {c z : Card} {k : Anchor}
    (hloc : st.pileOfTop z = some k) (hfit : canSitOn c z = true) :
    st.canPlace c (Sum.inr z) = true := by
  simp only [State.canPlace, hloc]
  exact hfit

/-- The twin relabeling keeps the fit. -/
private theorem tfa_fit_twin {c z : Card} (hfit : canSitOn c z = true) :
    canSitOn c z.twin = true := by
  have hz : z.twin = { z with suit := z.suit.twin } := rfl
  rw [hz, canSitOn_twin_right]
  exact hfit

/-- Chains of the generic pair closure concatenate (PORT of
`Orig2/FloatFiber.lean` §H5's private `steps_append`, verbatim). -/
private theorem orbit_steps_append {Q : State → State → Prop} : ∀ {a b : State},
    Steps Q a b → ∀ {c : State}, Steps Q b c → Steps Q a c := by
  intro a b h
  induction h with
  | refl s => intro c h₂; exact h₂
  | @cons s0 s1 s2 hl _ ih =>
      intro c h₂
      exact .cons hl (ih h₂)

/-- The bare-cargo class is transitive (PORT of `Orig2/FloatFiber.lean`
§H5's private `bareCargo_trans`, verbatim). -/
private theorem orbit_bareCargo_trans {a b c : State}
    (h₁ : BareCargoEquiv a b) (h₂ : BareCargoEquiv b c) :
    BareCargoEquiv a c := by
  obtain ⟨p1, p2⟩ := h₁
  obtain ⟨q1, q2⟩ := h₂
  exact ⟨orbit_steps_append p1 q1, orbit_steps_append q2 p2⟩

/-! ### §L1. THE COMPANY-LEG SUCCESSOR PILE READOUTS — the §H6
machinery extracted as a standalone row: a company reversible
slide (the mover seated on z in pile a, licensed to z.twin whose
pile k is located) rewrites exactly two piles — the donor keeps
the below prefix, the target pile gains the run — every other
pile's faceUp carried verbatim; the run is the mover's fromCard. -/

/-- THE SUCCESSOR PILE READOUTS for one company reversible slide.
The located pile k is pinned by the leg's own license; the WF
fence and the donor's cell come from the caller. -/
private theorem orbit_succ_piles {A M : State} {m z : Card}
    {a k : Anchor}
    (hwf : A.WF)
    (hhold : A.pileHolding m = some a)
    (hbne : below m ((A.piles a).faceUp) ≠ [])
    (hlast : lastOf (below m ((A.piles a).faceUp)) = some z)
    (hloc : A.pileOfTop z.twin = some k)
    (hstep : A.step (Move.tabToTab m (Sum.inr z.twin)) = some M) :
    ∃ tr, (m :: tr) = fromCard m ((A.piles a).faceUp) ∧
      (M.piles a).faceUp = below m ((A.piles a).faceUp) ∧
      (M.piles k).faceUp = (A.piles k).faceUp ++ (m :: tr) ∧
      (∀ j, j ≠ a → j ≠ k →
         (M.piles j).faceUp = (A.piles j).faceUp) := by
  obtain ⟨hsit, -⟩ := tfc_seat_parent hwf hhold hlast
  have hfit : canSitOn m z.twin = true := tfa_fit_twin hsit
  have hcc : A.cardCount z.twin = 1 :=
    hwf.2.2.1 z.twin (Card.mem_universe z.twin)
  have hktop : lastOf ((A.piles k).faceUp) = some z.twin :=
    (tfc_pileOfTop_top hloc).2
  have hka : k ≠ a := tfc_mover_pile_not_target hwf hhold hloc hfit
  have hak : a ≠ k := fun hh => hka hh.symm
  obtain ⟨a0, hhold0, -, -, hs1shape⟩ := step_tabToTab_inv hstep
  have ha0 : a0 = a := Option.some.inj (hhold0.symm.trans hhold)
  rw [ha0] at hs1shape
  obtain ⟨tr, hcrr⟩ := tfc_fromCard_cons_head _ (pileHolding_mem hhold)
  rw [hcrr] at hs1shape
  have hMk : (A.setPile a (Pile.afterRunRemoved (A.piles a)
      (below m ((A.piles a).faceUp)))).piles k = A.piles k :=
    setPile_piles_ne hka
  have hlocM : (A.setPile a (Pile.afterRunRemoved (A.piles a)
      (below m ((A.piles a).faceUp)))).pileOfTop z.twin = some k := by
    have hmidk : (A.setPile a (Pile.afterRunRemoved (A.piles a)
        (below m ((A.piles a).faceUp)))).topOf k = some z.twin := by
      show lastOf ((A.setPile a (Pile.afterRunRemoved (A.piles a)
        (below m ((A.piles a).faceUp)))).piles k).faceUp = some z.twin
      rw [hMk]
      exact hktop
    refine firstWhere_find (Anchor.mem_all k) (decide_eq_true hmidk) ?_
    intro j _ hjk
    by_cases hja : j = a
    · rw [hja]
      refine decide_false_of_not ?_
      intro hcon
      have hset : (A.setPile a (Pile.afterRunRemoved (A.piles a)
          (below m ((A.piles a).faceUp)))).piles a
          = Pile.afterRunRemoved (A.piles a)
              (below m ((A.piles a).faceUp)) :=
        setPile_piles_self
      have hcon0 : lastOf (Pile.afterRunRemoved (A.piles a)
          (below m ((A.piles a).faceUp))).faceUp = some z.twin := by
        have hp : ((A.setPile a (Pile.afterRunRemoved (A.piles a)
            (below m ((A.piles a).faceUp)))).piles a).top = some z.twin := hcon
        rw [hset] at hp
        exact hp
      have hznew : z.twin ∈ (Pile.afterRunRemoved (A.piles a)
          (below m ((A.piles a).faceUp))).faceUp := lastOf_mem hcon0
      have hzone : z.twin ∈ (Pile.afterRunRemoved (A.piles a)
          (below m ((A.piles a).faceUp))).hidden
          ++ (Pile.afterRunRemoved (A.piles a)
            (below m ((A.piles a).faceUp))).faceUp :=
        List.mem_append.mpr (Or.inr hznew)
      have hzold : z.twin ∈ (A.piles a).hidden ++ (A.piles a).faceUp :=
        tfc_mem_afterRunRemoved_below_zone hzone
      have hzk : z.twin ∈ (A.piles k).hidden ++ (A.piles k).faceUp :=
        List.mem_append.mpr (Or.inr (lastOf_mem hktop))
      exact tfc_two_pile_zone_absurd hak hcc hzold hzk
    · refine decide_false_of_not ?_
      intro hcon
      have hcon2 : A.topOf j = some z.twin := by
        have hp : ((A.setPile a (Pile.afterRunRemoved (A.piles a)
            (below m ((A.piles a).faceUp)))).piles j).top = some z.twin := hcon
        rw [setPile_piles_ne hja] at hp
        exact hp
      exact hjk (tfc_top_search_unique hcc hcon2 hktop)
  rw [putRun_inr_eq hlocM] at hs1shape
  refine ⟨tr, hcrr.symm, ?_, ?_, ?_⟩
  · rw [hs1shape, setPile_piles_ne hak, setPile_piles_self,
    afterRunRemoved_ne hbne]
  · rw [hs1shape, setPile_piles_self, hMk]
  · intro j hja hjk
    rw [hs1shape, setPile_piles_ne hjk, setPile_piles_ne hja]

/-! ### §L2. THE LICENSE PRESERVATION ACROSS A DISJOINT COMPANY HOP —
after the first mover's hop, a second mover's located twin-pile —
untouched by the hop (k₂ ∉ {a, k}) — still witnesses the same
search at the successor: the only top-flips the hop can cause are
the vacated parent z and the run's last card, and pile
disjointness plus occurrence counting kill both relocations of
the second mover's twin target. -/

/-- The located twin-pile search is preserved by a disjoint company
hop's successor state. -/
private theorem orbit_license_preserved {A M : State} {m z c₂ z₂ : Card}
    {a k k₂ : Anchor}
    (hwf : A.WF)
    (hhold : A.pileHolding m = some a)
    (hbne : below m ((A.piles a).faceUp) ≠ [])
    (hlast : lastOf (below m ((A.piles a).faceUp)) = some z)
    (hloc1 : A.pileOfTop z.twin = some k)
    (hstep : A.step (Move.tabToTab m (Sum.inr z.twin)) = some M)
    (hloc2 : A.pileOfTop z₂.twin = some k₂)
    (hdk2a : k₂ ≠ a) (hdk2k : k₂ ≠ k) :
    M.pileOfTop z₂.twin = some k₂ := by
  obtain ⟨tr, hrunEq, hAface, hKface, hOther⟩ :=
    orbit_succ_piles hwf hhold hbne hlast hloc1 hstep
  have hcc2 : A.cardCount z₂.twin = 1 :=
    hwf.2.2.1 z₂.twin (Card.mem_universe z₂.twin)
  have hzmem : z₂.twin ∈ (A.piles k₂).faceUp :=
    lastOf_mem (tfc_pileOfTop_top hloc2).2
  have htopK2 : lastOf ((M.piles k₂).faceUp) = some z₂.twin := by
    rw [hOther k₂ hdk2a hdk2k]
    exact (tfc_pileOfTop_top hloc2).2
  refine firstWhere_find (Anchor.mem_all k₂)
    (decide_eq_true (show M.topOf k₂ = some z₂.twin from htopK2)) ?_
  intro j _ hjk2
  by_cases hja : j = a
  · rw [hja]
    refine decide_false_of_not ?_
    intro hcon
    have hMa : lastOf ((M.piles a).faceUp) = some z := by
      rw [hAface]
      exact hlast
    have hzz : z₂.twin = z := Option.some.inj (hcon.symm.trans hMa)
    have hzmema : z ∈ (A.piles a).faceUp :=
      mem_below _ (lastOf_mem hlast)
    have hnocross : z₂.twin ∉ (A.piles a).faceUp :=
      tfc_faceUp_uniq_other hwf hzmem hdk2a.symm
    rw [hzz] at hnocross
    exact absurd hzmema hnocross
  · rcases Decidable.em (j = k) with hjk | hjk
    · rw [hjk]
      refine decide_false_of_not ?_
      intro hcon
      have hneRun : (m :: tr : List Card) ≠ [] := by simp
      have hcon0 : lastOf ((A.piles k).faceUp ++ (m :: tr))
          = some z₂.twin := by
        have hp : lastOf ((M.piles k).faceUp) = some z₂.twin := hcon
        rw [hKface] at hp
        exact hp
      rw [tfc_lastOf_append_ne _ hneRun] at hcon0
      have hrun : z₂.twin ∈ m :: tr := lastOf_mem hcon0
      rw [hrunEq] at hrun
      have hrunA : z₂.twin ∈ (A.piles a).faceUp := tfc_mem_fromCard _ hrun
      exact absurd hrunA (tfc_faceUp_uniq_other hwf hzmem hdk2a.symm)
    · refine decide_false_of_not ?_
      intro hcon
      have hp0 : lastOf ((M.piles j).faceUp) = some z₂.twin := hcon
      rw [hOther j hja hjk] at hp0
      exact hjk2 (tfc_top_search_unique hcc2 hp0
        (tfc_pileOfTop_top hloc2).2)


/-! ## The audit battery -/

#print axioms floater_leg_invariant
#print axioms floater_orbit_invariant
#print axioms floater_path_invariant
#print axioms bareCargo_to_chartDiff
#print axioms bareCargo_reconstruct_singleEdit
