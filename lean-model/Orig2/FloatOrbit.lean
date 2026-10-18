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
`fli_belownil_head`, `fli_twin_inj`); the placement constructors
and the class-algebra pair joined the shared kit in the same day's
second pass (see CargoKit's history — the re-landed Stage-3B rows
consume `tfa_canPlace_*`, `tfa_fit_twin`, `tfa_steps_append`,
`tfa_bareCargo_trans` from the import).
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
  · rw [hxc, ite_eq_left rfl]
    exact hval
  · rw [ite_eq_right hxc]
    exact hcarried x hxc

/-! ### §L. StAGE 3B — THE TWO-HOP DISJOINT RECONSTRUCTION (the flat
iff's reconstruction half for two movers in disjoint twin-fibers;
the compose-unit and the license-preservation embryo of the
safe-order commutation card) -/

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
private theorem orbit_license_preserved {A M : State} {m z z₂ : Card}
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


/-- **floater_orbit_wf_prsv** — the WF fence rides the whole cargo
orbit: every bare-cargo class-mate of a WF state is WF (per-leg
fence by the tabToTab conservation row, closed by chain induction
— the ← direction's readout-and-fence clause, one cargo
direction suffices as ever). -/
theorem floater_orbit_wf_prsv {x0 y : State} (hpath : Steps CargoLeg x0 y)
    (hwf : x0.WF) : y.WF := by
  induction hpath with
  | refl s => exact hwf
  | @cons x1 x2 x3 hleg hrest ih =>
      obtain ⟨m, b, hstep, hrev⟩ := id hleg
      exact ih (tfc_tabToTab_wf hwf hstep)

/-! ### §M. THE MIRROR PROGRAM — foundations: the seating uniqueness
calculus (extracted standalone from the invariance card's internal
machinery; the license rows for the ← direction ride these). -/

/-- THE UNIQUE SITTER: at a WF state exactly one card sits directly
on any given card (two seat witnesses of one parent coincide — the
below-prefix occurrence calculus: both witnesses' belows end at the
parent's single occurrence). -/
private theorem orbit_sitter_unique {s : State} {x y z : Card}
    (hwf : s.WF) (hx : seatOf s x = some (Sum.inr z))
    (hy : seatOf s y = some (Sum.inr z)) : x = y := by
  by_cases hxy : y = x
  · exact hxy.symm
  · exfalso
    obtain ⟨px, hholdx, -, hlastx⟩ := tfc_seatOf_of_inr hx
    obtain ⟨py, hholdy, -, hlasty⟩ := tfc_seatOf_of_inr hy
    have hcc : s.cardCount z = 1 := hwf.2.2.1 z (Card.mem_universe z)
    have hzx : z ∈ (s.piles px).faceUp := mem_below _ (lastOf_mem hlastx)
    have hzy : z ∈ (s.piles py).faceUp := mem_below _ (lastOf_mem hlasty)
    have hp : px = py := by
      by_cases hpq : px = py
      · exact hpq
      · exact (tfc_two_pile_zone_absurd hpq hcc
          (List.mem_append.mpr (Or.inr hzx))
          (List.mem_append.mpr (Or.inr hzy))).elim
    subst hp
    obtain ⟨Rx, hcx⟩ := tfc_fromCard_cons_head _ (pileHolding_mem hholdx)
    have hspl : (s.piles px).faceUp
        = below x ((s.piles px).faceUp) ++ (x :: Rx) := by
      have h0 := tfc_below_fromCard x ((s.piles px).faceUp)
      rw [hcx] at h0
      exact h0.symm
    have hyin : y ∈ (s.piles px).faceUp := pileHolding_mem hholdy
    rw [hspl] at hyin
    rcases List.mem_append.mp hyin with hyleft | hyright
    · rw [hspl] at hlasty
      rw [tfc_below_mem_append_left _ _ hyleft] at hlasty
      have hcnt : tfc_cnt z (below x ((s.piles px).faceUp)) ≤ 1 := by
        have h2 := tfc_cnt_app z (below x ((s.piles px).faceUp)) (x :: Rx)
        rw [← hspl] at h2
        have h3 : tfc_cnt z ((s.piles px).faceUp) ≤ s.cardCount z :=
          tfc_faceUp_cnt_le_cardCount
        omega
      exact fli_below_last_absurd hcnt hyleft hlasty hlastx
    · rcases List.mem_cons.mp hyright with heq | hyride
      · exact hxy heq
      · have hynbl : y ∉ below x ((s.piles px).faceUp) := by
          intro hmem
          exact (tfc_two_mem_faceUp_absurd hwf hspl hmem
            (List.mem_cons.mpr (Or.inr hyride))).elim
        rw [hspl] at hlasty
        rw [(tfc_below_fromCard_excl y _ _ hynbl).1] at hlasty
        by_cases hbe : below y (x :: Rx) = []
        · exact hxy (fli_belownil_head hbe)
        · rw [tfc_lastOf_append_ne _ hbe] at hlasty
          have hzride : z ∈ (x :: Rx) := mem_below _ (lastOf_mem hlasty)
          exact (tfc_two_mem_faceUp_absurd hwf hspl
            (lastOf_mem hlastx) hzride).elim

/-- A located top admits no sitter: the search's top card has
nothing directly on it (sitting on a top would double the top's
occurrence — the below-prefix calculus row again). -/
private theorem orbit_no_sitter_on_top {s : State} {x z : Card} {k : Anchor}
    (hwf : s.WF) (hloc : s.pileOfTop z = some k)
    (hx : seatOf s x = some (Sum.inr z)) : False := by
  obtain ⟨px, hholdx, -, hlastx⟩ := tfc_seatOf_of_inr hx
  have hktop : lastOf ((s.piles k).faceUp) = some z :=
    (tfc_pileOfTop_top hloc).2
  have hcc : s.cardCount z = 1 := hwf.2.2.1 z (Card.mem_universe z)
  have hzx : z ∈ (s.piles px).faceUp := mem_below _ (lastOf_mem hlastx)
  have hzk : z ∈ (s.piles k).faceUp := lastOf_mem hktop
  have hp : px = k := by
    by_cases hpq : px = k
    · exact hpq
    · exact (tfc_two_pile_zone_absurd hpq hcc
        (List.mem_append.mpr (Or.inr hzx))
        (List.mem_append.mpr (Or.inr hzk))).elim
  subst hp
  have hxin : x ∈ (s.piles px).faceUp := pileHolding_mem hholdx
  have hcnt : tfc_cnt z ((s.piles px).faceUp) ≤ 1 := by
    have h3 : tfc_cnt z ((s.piles px).faceUp) ≤ s.cardCount z :=
      tfc_faceUp_cnt_le_cardCount
    omega
  exact fli_below_last_absurd hcnt hxin hlastx hktop

/-- One bottomer per pile: two inl-seat witnesses of one anchor
coincide (the faceUp head position is unique). -/
private theorem orbit_bottom_unique {s : State} {x y : Card} {a : Anchor}
    (hx : seatOf s x = some (Sum.inl a)) (hy : seatOf s y = some (Sum.inl a)) :
    x = y := by
  obtain ⟨hholdx, hbEx⟩ := tfc_seatOf_of_inl hx
  obtain ⟨hholdy, hbEy⟩ := tfc_seatOf_of_inl hy
  obtain ⟨Rx, hcx⟩ := tfc_fromCard_cons_head _ (pileHolding_mem hholdx)
  obtain ⟨Ry, hcy⟩ := tfc_fromCard_cons_head _ (pileHolding_mem hholdy)
  have hLx : (s.piles a).faceUp = x :: Rx := by
    have h0 := tfc_below_fromCard x ((s.piles a).faceUp)
    rw [hcx, hbEx, List.nil_append] at h0
    exact h0.symm
  have hLy : (s.piles a).faceUp = y :: Ry := by
    have h0 := tfc_below_fromCard y ((s.piles a).faceUp)
    rw [hcy, hbEy, List.nil_append] at h0
    exact h0.symm
  rw [hLy] at hLx
  injection hLx with h
  exact h.symm

/-- THE EXPOSED TOPS ROW: a card in a pile's faceUp with no sitter
atop it IS that pile's top — the directly-following run-head (if
any) would have to sit on it, and the occurrence calculus forbids a
second occurrence of the card itself straight after. -/
private theorem orbit_exposed_tops {s : State} {z : Card} {q : Anchor}
    (hwf : s.WF) (hmem : z ∈ (s.piles q).faceUp)
    (hno : ∀ x, seatOf s x ≠ some (Sum.inr z)) :
    lastOf ((s.piles q).faceUp) = some z := by
  obtain ⟨Rx, hcx⟩ := tfc_fromCard_cons_head _ hmem
  have hspl : (s.piles q).faceUp
      = below z ((s.piles q).faceUp) ++ (z :: Rx) := by
    have h0 := tfc_below_fromCard z ((s.piles q).faceUp)
    rw [hcx] at h0
    exact h0.symm
  have hccz : s.cardCount z = 1 := hwf.2.2.1 z (Card.mem_universe z)
  have hbcnt : tfc_cnt z ((s.piles q).faceUp) ≤ 1 := by
    have h3 : tfc_cnt z ((s.piles q).faceUp) ≤ s.cardCount z :=
      tfc_faceUp_cnt_le_cardCount
    omega
  cases Rx with
  | nil =>
      have hne : (z :: [] : List Card) ≠ [] := by simp
      rw [hspl, tfc_lastOf_append_ne _ hne]
      rfl
  | cons y ys =>
      have hzne : z ≠ y := by
        intro heq
        have h2 : tfc_cnt z ((s.piles q).faceUp)
            = tfc_cnt z (below z ((s.piles q).faceUp))
              + tfc_cnt z (z :: y :: ys) := by
          have h2b := tfc_cnt_app z (below z ((s.piles q).faceUp)) (z :: y :: ys)
          rw [← hspl] at h2b
          exact h2b
        have h3 : tfc_cnt z (z :: y :: ys)
            = 1 + tfc_cnt z (y :: ys) := by
          rw [tfc_cnt_def, ite_eq_left rfl]
        have h4 : 1 ≤ tfc_cnt z (y :: ys) :=
          tfc_mem_le_cnt _ (by rw [heq]; exact List.mem_cons_self)
        omega
      have hyL : y ∈ (s.piles q).faceUp := by
        rw [hspl]
        exact List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inr List.mem_cons_self)))
      have hynbl : y ∉ below z ((s.piles q).faceUp) := by
        intro hmem2
        exact (tfc_two_mem_faceUp_absurd hwf hspl hmem2
          (List.mem_cons.mpr (Or.inr List.mem_cons_self))).elim
      have hlasty : lastOf (below y ((s.piles q).faceUp)) = some z := by
        have heqA : below y ((s.piles q).faceUp)
            = below y (below z ((s.piles q).faceUp) ++ (z :: y :: ys)) :=
          congrArg (below y) hspl
        have heqB : below y (below z ((s.piles q).faceUp) ++ (z :: y :: ys))
            = below z ((s.piles q).faceUp) ++ below y (z :: y :: ys) :=
          (tfc_below_fromCard_excl y _ _ hynbl).1
        have heq2 : below y (z :: y :: ys) = z :: [] := by
          rw [below_cons, ite_eq_right hzne, below_cons, ite_eq_left rfl]
        rw [heqA.trans heqB, heq2, tfc_lastOf_append_ne _ (by simp)]
        rfl
      have hdecl : ∀ j, j ≠ q → y ∉ (s.piles j).faceUp := by
        intro j hjq hmemj
        have hccy : s.cardCount y = 1 := hwf.2.2.1 y (Card.mem_universe y)
        exact (tfc_two_pile_zone_absurd hjq hccy
          (List.mem_append.mpr (Or.inr hmemj))
          (List.mem_append.mpr (Or.inr hyL))).elim
      have hholdy : s.pileHolding y = some q :=
        tfc_pileHolding_pin hyL hdecl
      exact (hno y (tfc_seatOf_inr_intro hholdy hlasty)).elim

/-! ### §M1. THE FLAT-GRADE SINGLE RECONSTRUCTIONS — n = 1 with
the movers' licenses DERIVED from the flat data itself (the spec's
located target, the seating arithmetic), no operational license
assumed. -/

/-- **bareCargo_reconstruct_companyFlat** — the flat single-company-hop
reconstruction: one company hop's net data plus the st-side spec
suffices (the changed card's license is unpacked from its
FloaterSpec — the seat-pin names the parent, the located target is
the spec's own pile, the seated-king arm dies on the fit
arithmetic — and the single-edit unit closes). -/
theorem bareCargo_reconstruct_companyFlat {st w : State} (hwf : st.WF)
    (hroundtrip : ∀ A B, chartAgree A B → A = B)
    {c z : Card}
    (hsec : seatOf st c = some (Sum.inr z))
    (hsew : seatOf w c = some (Sum.inr z.twin))
    (hlic : FloaterSpec st c)
    (hcar : ∀ x, x ≠ c → seatOf w x = seatOf st x)
    (hread : boardFixed st w ∧ foundsFixed st w ∧
      drawPool st = drawPool w ∧ cutOf st = cutOf w) :
    BareCargoEquiv st w := by
  rcases hlic with ⟨z₀, a₀, hse₀, hhold₀, harm₀⟩ |
    ⟨a₁, hse₁, hking, -, hempty⟩
  · have hp : z₀ = z := by
      have h2 : some (Sum.inr z₀) = some (Sum.inr z) :=
        hse₀.symm.trans hsec
      have h3 : Sum.inr z₀ = Sum.inr z := Option.some.inj h2
      injection h3
    rw [hp] at harm₀
    rcases harm₀ with ⟨k₁, hloc⟩ | ⟨hking, -⟩
    · obtain ⟨a₂, hhold₂, hbne₂, hlast₂⟩ := tfc_seatOf_of_inr hsec
      obtain ⟨hsit, -⟩ := tfc_seat_parent hwf hhold₂ hlast₂
      have hfit : canSitOn c z.twin = true := tfa_fit_twin hsit
      have hcell : FloaterCell st c := Or.inl ⟨z, hsec⟩
      have hmove : st.canPlace c (Sum.inr z.twin) = true :=
        tfa_canPlace_inr hloc hfit
      exact bareCargo_reconstruct_singleEdit hwf hroundtrip hcar hsew hmove hcell hread
    · exfalso
      obtain ⟨a₂, hhold₂, hbne₂, hlast₂⟩ := tfc_seatOf_of_inr hsec
      obtain ⟨hsit, -⟩ := tfc_seat_parent hwf hhold₂ hlast₂
      obtain ⟨hidx, -⟩ := (canSitOn_eq c z).mp hsit
      have hzlt := Rank.toIdx_lt z.rank
      have h12 : c.rank.toIdx = 12 := by rw [hking]; rfl
      omega
  · exfalso
    have hcruz : some (Sum.inl a₁) = some (Sum.inr z) :=
      hse₁.symm.trans hsec
    nomatch hcruz

/-- THE SPEC'S LOCATED TARGET, unpacked: with the seat pin, the
FloaterSpec's first disjunct names the seated parent and its
target pile (the king arm of the disjunct is dead — a seated king
violates the fit arithmetic). -/
private theorem orbit_spec_target {st : State} {c z : Card}
    (hwf : st.WF) (hse : seatOf st c = some (Sum.inr z))
    (hlic : FloaterSpec st c) :
    ∃ k, st.pileOfTop z.twin = some k := by
  rcases hlic with ⟨z₀, a₀, hse₀, hhold₀, harm₀⟩ |
    ⟨a₁, hse₁, hking, -, -⟩
  · have hp : z₀ = z := by
      have h2 : some (Sum.inr z₀) = some (Sum.inr z) :=
        hse₀.symm.trans hse
      have h3 : Sum.inr z₀ = Sum.inr z := Option.some.inj h2
      injection h3
    rw [hp] at harm₀
    rcases harm₀ with ⟨k₁, hloc⟩ | ⟨hking, -⟩
    · exact ⟨k₁, hloc⟩
    · exfalso
      obtain ⟨a₂, hhold₂, hbne₂, hlast₂⟩ := tfc_seatOf_of_inr hse
      obtain ⟨hsit, -⟩ := tfc_seat_parent hwf hhold₂ hlast₂
      obtain ⟨hidx, -⟩ := (canSitOn_eq c z).mp hsit
      have hzlt := Rank.toIdx_lt z.rank
      have h12 : c.rank.toIdx = 12 := by rw [hking]; rfl
      omega
  · exfalso
    have hcruz : some (Sum.inl a₁) = some (Sum.inr z) :=
      hse₁.symm.trans hse
    nomatch hcruz

/-- THE LOCATED-MIRROR ROW: a faceUp card with no sitter at the
current state is located by the search in its own holding pile
(the exposed tops row plus the per-pile occurrence declines). -/
private theorem orbit_located_mirror {u : State} {z : Card} {j₀ : Anchor}
    (hwu : u.WF) (hhold : u.pileHolding z = some j₀)
    (hno : ∀ x, seatOf u x ≠ some (Sum.inr z)) :
    u.pileOfTop z = some j₀ := by
  have hmem : z ∈ (u.piles j₀).faceUp := pileHolding_mem hhold
  have htop : lastOf ((u.piles j₀).faceUp) = some z :=
    orbit_exposed_tops hwu hmem hno
  have hcc : u.cardCount z = 1 := hwu.2.2.1 z (Card.mem_universe z)
  refine firstWhere_find (Anchor.mem_all j₀)
    (decide_eq_true (show u.topOf j₀ = some z from htop)) ?_
  intro j _ hjj
  refine decide_false_of_not ?_
  intro hcon
  have hzj : z ∈ (u.piles j).faceUp := lastOf_mem hcon
  exact (tfc_two_pile_zone_absurd hjj hcc
    (List.mem_append.mpr (Or.inr hzj))
    (List.mem_append.mpr (Or.inr hmem))).elim

/-! ### §M2. THE MIRROR LICENSE — the undo leg for a company mover at
a consistent neighbor (the chart st-shaped on done cards, w-shaped
on pending cards): the return-to-parent license is derived from the
flat data itself. -/

/-- THE COMPANY UNDO LICENSE at a consistent neighbor: with c's net
hop (st-parent z, w-parent z.twin, c genuinely changed) and c's
FloaterSpec at st, at any neighbor state whose every card's seat is
its st-seat or its w-seat (the induction's split invariant) and
where c is still w-shaped, c's return leg onto z is licensed — the
fit is state-free (the st-side seat-parent), and z is located by
the no-sitter calculus: a done-shaped sitter sits at st and dies on
uniqueness (it would be c, and c is w-shaped with the twin parent);
a pending-shaped sitter dies arm by arm (the carried sitter is c
again; the hop-sitter would sit on z.twin at st, where the spec's
located target forbids sitters; the king arm mismatches the sum). -/
private theorem orbit_company_undo_license {st w u : State}
    {c z : Card}
    (hwfst : st.WF) (hwu : u.WF)
    (hsplit : ∀ x, seatOf u x = seatOf st x ∨ seatOf u x = seatOf w x)
    (hcu : seatOf u c = seatOf w c)
    (harm : seatOf st c = some (Sum.inr z) ∧
      seatOf w c = some (Sum.inr z.twin))
    (hchg : seatOf st c ≠ seatOf w c)
    (hlic : FloaterSpec st c)
    (hrel : ∀ x, (seatOf w x = seatOf st x) ∨
      (∃ z', seatOf st x = some (Sum.inr z') ∧
        seatOf w x = some (Sum.inr z'.twin)) ∨
      (x.rank = Rank.king ∧ ∃ a a', seatOf st x = some (Sum.inl a) ∧
        seatOf w x = some (Sum.inl a'))) :
    u.canPlace c (Sum.inr z) = true := by
  obtain ⟨hcst, hcw⟩ := harm
  -- the state-free fit: c sat on z at st
  obtain ⟨a₂, hhold₂, hbne₂, hlast₂⟩ := tfc_seatOf_of_inr hcst
  obtain ⟨hsit, -⟩ := tfc_seat_parent hwfst hhold₂ hlast₂
  -- z is seated at st (it sits under c in c's pile)
  have hzmem : z ∈ (st.piles a₂).faceUp := mem_below _ (lastOf_mem hlast₂)
  have hzhq : ∃ q₂, st.pileHolding z = some q₂ := by
    have hdecl : ∀ j, j ≠ a₂ → z ∉ (st.piles j).faceUp := by
      intro j hjq hmemj
      have hccz : st.cardCount z = 1 :=
        hwfst.2.2.1 z (Card.mem_universe z)
      exact (tfc_two_pile_zone_absurd hjq hccz
        (List.mem_append.mpr (Or.inr hmemj))
        (List.mem_append.mpr (Or.inr hzmem))).elim
    exact ⟨a₂, tfc_pileHolding_pin hzmem hdecl⟩
  have hzne : seatOf st z ≠ none := by
    obtain ⟨q₂, hhq₂⟩ := hzhq
    rw [tfc_seatOf_pair hhq₂]
    intro hq
    cases hg : (below z ((st.piles q₂).faceUp)).getLast? with
    | none => rw [hg] at hq; nomatch hq
    | some y => rw [hg] at hq; nomatch hq
  -- z stays seated at u (either shape; the w-side arms are all
  -- seat-preserving)
  have hzune : seatOf u z ≠ none := by
    rcases hsplit z with hu | hu
    · rw [hu]
      exact hzne
    · rw [hu]
      rcases hrel z with e | ⟨z', h1z, h2z⟩ | ⟨hk, b1, b2, h1', h2'⟩
      · rw [e]
        exact hzne
      · intro hq
        rw [h2z] at hq
        nomatch hq
      · intro hq
        rw [h2'] at hq
        nomatch hq
  -- nobody sits on z at u
  have hno : ∀ x, seatOf u x ≠ some (Sum.inr z) := by
    intro x hx
    rcases hsplit x with hu | hu
    · -- done-shaped: the sitter sits on z at st; uniqueness pins it
      -- to c; then c's two shapes agree — contradicting the change
      rw [hu] at hx
      have hxc : x = c := orbit_sitter_unique hwfst hx hcst
      rw [hxc] at hu
      exact hchg (hu.symm.trans hcu)
    · -- pending-shaped: the sitter sits on z at w; walk its net arm
      rw [hu] at hx
      rcases hrel x with e | ⟨z', h1x, h2x⟩ | ⟨hk, b1, b2, h1', h2'⟩
      · -- carried: the st-sitter is c again; c's two shapes agree
        rw [e] at hx
        have hxc : x = c := orbit_sitter_unique hwfst hx hcst
        rw [hxc] at e
        exact hchg e.symm
      · -- hop: x's w-parent is z, so x's st-parent is z.twin — the
        -- spec's located target at st forbids any such sitter
        have hzz : z'.twin = z := by
          have hq : some (Sum.inr z'.twin) = some (Sum.inr z) :=
            h2x.symm.trans hx
          have h3 : Sum.inr z'.twin = Sum.inr z := Option.some.inj hq
          injection h3
        have hz₀ : z' = z.twin := by
          rw [← tfc_card_twin_twin z', hzz]
        rw [hz₀] at h1x
        obtain ⟨k₁, hmloc⟩ := orbit_spec_target hwfst hcst hlic
        exact orbit_no_sitter_on_top hwfst hmloc h1x
      · -- king: the w-seat is inl, the sitter claim is inr
        exfalso
        have hcruz : some (Sum.inl b2) = some (Sum.inr z) :=
          h2'.symm.trans hx
        nomatch hcruz
  -- locate z at u and construct the license
  cases hqz : u.pileHolding z with
  | none =>
      exfalso
      rw [tfc_seatOf_none hqz] at hzune
      exact hzune rfl
  | some j₀ =>
      have hloc : u.pileOfTop z = some j₀ :=
        orbit_located_mirror hwu hqz hno
      exact tfa_canPlace_inr hloc hsit

/-- THE COMPANY REDO LICENSE at the undo's successor: after c's
return leg, at the crate where c is st-shaped and every other card
keeps its shape, c's forward hop is licensed again — the twin
parent is located by the symmetric no-sitter calculus: st-shaped
sitters die on the spec's located target (it forbids sitters on
the twin pile), w-shaped sitters die on being carried (again the
spec's target) or hopped (their st-parent would be z, the unique
st-sitter is c, and c's two shapes now disagree on the change). -/
private theorem orbit_company_redo_license {st w u : State}
    {c z : Card}
    (hwfst : st.WF) (hwu : u.WF)
    (hsplit : ∀ x, seatOf u x = seatOf st x ∨ seatOf u x = seatOf w x)
    (hcu : seatOf u c = seatOf st c)
    (harm : seatOf st c = some (Sum.inr z) ∧
      seatOf w c = some (Sum.inr z.twin))
    (hchg : seatOf st c ≠ seatOf w c)
    (hlic : FloaterSpec st c)
    (hrel : ∀ x, (seatOf w x = seatOf st x) ∨
      (∃ z', seatOf st x = some (Sum.inr z') ∧
        seatOf w x = some (Sum.inr z'.twin)) ∨
      (x.rank = Rank.king ∧ ∃ a a', seatOf st x = some (Sum.inl a) ∧
        seatOf w x = some (Sum.inl a'))) :
    u.canPlace c (Sum.inr z.twin) = true := by
  obtain ⟨hcst, hcw⟩ := harm
  obtain ⟨a₂, hhold₂, hbne₂, hlast₂⟩ := tfc_seatOf_of_inr hcst
  obtain ⟨hsit, -⟩ := tfc_seat_parent hwfst hhold₂ hlast₂
  have hfit : canSitOn c z.twin = true := tfa_fit_twin hsit
  -- the twin parent sits under the spec's located target at st
  obtain ⟨k₁, hmloc⟩ := orbit_spec_target hwfst hcst hlic
  have htmem : z.twin ∈ (st.piles k₁).faceUp :=
    lastOf_mem (tfc_pileOfTop_top hmloc).2
  have hthq : ∃ q₂, st.pileHolding z.twin = some q₂ := by
    have hdecl : ∀ j, j ≠ k₁ → z.twin ∉ (st.piles j).faceUp := by
      intro j hjq hmemj
      have hcct : st.cardCount z.twin = 1 :=
        hwfst.2.2.1 z.twin (Card.mem_universe z.twin)
      exact (tfc_two_pile_zone_absurd hjq hcct
        (List.mem_append.mpr (Or.inr hmemj))
        (List.mem_append.mpr (Or.inr htmem))).elim
    exact ⟨k₁, tfc_pileHolding_pin htmem hdecl⟩
  have htne : seatOf st z.twin ≠ none := by
    obtain ⟨q₂, hhq₂⟩ := hthq
    rw [tfc_seatOf_pair hhq₂]
    intro hq
    cases hg : (below z.twin ((st.piles q₂).faceUp)).getLast? with
    | none => rw [hg] at hq; nomatch hq
    | some y => rw [hg] at hq; nomatch hq
  have htune : seatOf u z.twin ≠ none := by
    rcases hsplit z.twin with hu | hu
    · rw [hu]
      exact htne
    · rw [hu]
      rcases hrel z.twin with e | ⟨z', h1t, h2t⟩ | ⟨hk, b1, b2, h1', h2'⟩
      · rw [e]
        exact htne
      · intro hq
        rw [h2t] at hq
        nomatch hq
      · intro hq
        rw [h2'] at hq
        nomatch hq
  -- nobody sits on z.twin at u
  have hno : ∀ x, seatOf u x ≠ some (Sum.inr z.twin) := by
    intro x hx
    rcases hsplit x with hu | hu
    · -- st-shaped sitter: the spec's located target forbids it
      rw [hu] at hx
      exact orbit_no_sitter_on_top hwfst hmloc hx
    · -- w-shaped sitter: walk its net arm
      rw [hu] at hx
      rcases hrel x with e | ⟨z', h1x, h2x⟩ | ⟨hk, b1, b2, h1', h2'⟩
      · rw [e] at hx
        exact orbit_no_sitter_on_top hwfst hmloc hx
      · -- hop: x's st-parent is z; the unique st-sitter on z is c;
        -- c's two shapes disagree — contradiction
        have hz' : z' = z := by
          have hq : some (Sum.inr z'.twin) = some (Sum.inr z.twin) :=
            h2x.symm.trans hx
          have h3 : Sum.inr z'.twin = Sum.inr z.twin := Option.some.inj hq
          injection h3 with h4
          exact fli_twin_inj z' z h4
        rw [hz'] at h1x
        have hxc : x = c := orbit_sitter_unique hwfst h1x hcst
        rw [hxc] at hu
        exact hchg (hcu.symm.trans hu)
      · -- king: the w-seat is inl, the sitter claim is inr
        exfalso
        have hcruz : some (Sum.inl b2) = some (Sum.inr z.twin) :=
          h2'.symm.trans hx
        nomatch hcruz
  -- locate z.twin at u; construct the license
  cases hqz : u.pileHolding z.twin with
  | none =>
      exfalso
      rw [tfc_seatOf_none hqz] at htune
      exact htune rfl
  | some j₀ =>
      have hloc : u.pileOfTop z.twin = some j₀ :=
        orbit_located_mirror hwu hqz hno
      exact tfa_canPlace_inr hloc hfit

/-! ### §M3. THE MASTER INDUCTION AND THE COMPANY-GRADE IFF — the ←
direction for orbits whose changed cards all move company (twin
hops): the queue carries the changed cards (with duplicates
harmless — a stale entry whose card is already st-shaped skips);
each process-step fires the undo leg (w-shape restored to the
st-parent) and the redo leg (the point edit reversed), the chart
round trip pins the redo's successor back onto the current crate,
and the accumulated leg pairs close the class both ways. -/

/-- Chains of the generic pair closure concatenate (re-landed; PORT
of `Orig2/FloatFiber.lean` §H5's private `steps_append`, verbatim). -/
private theorem orbit_steps_append {Q : State → State → Prop} : ∀ {a b : State},
    Steps Q a b → ∀ {c : State}, Steps Q b c → Steps Q a c := by
  intro a b h
  induction h with
  | refl s => intro c h₂; exact h₂
  | @cons s0 s1 s2 hl _ ih =>
      intro c h₂
      exact .cons hl (ih h₂)

/-- The class transitivity (re-landed; PORT of `Orig2/FloatFiber.lean`
§H5's private `bareCargo_trans`, verbatim). -/
private theorem orbit_bareCargo_trans {a b c : State}
    (h₁ : BareCargoEquiv a b) (h₂ : BareCargoEquiv b c) :
    BareCargoEquiv a c := by
  obtain ⟨p1, p2⟩ := h₁
  obtain ⟨q1, q2⟩ := h₂
  exact ⟨orbit_steps_append p1 q1, orbit_steps_append q2 p2⟩

/-- THE MASTER INDUCTION (company grade): over the changed-card
queue, with the skip-case carrying stale entries.  Invariants at
the current crate u with queue R: queued cards are w-shaped or
already st-shaped (P1); everything outside the queue is st-shaped
(P2); the readouts agree with st (P3); the fence holds (P4); every
queued card is genuinely changed (P5).  The base is the chart round
trip itself; the step processes the head when pending and skips it
when stale. -/
private theorem orbit_company_mirror_induct {st w : State}
    (hwfst : st.WF)
    (hroundtrip : ∀ A B, chartAgree A B → A = B)
    (hrel : ∀ x, (seatOf w x = seatOf st x) ∨
      (∃ z', seatOf st x = some (Sum.inr z') ∧
        seatOf w x = some (Sum.inr z'.twin)) ∨
      (x.rank = Rank.king ∧ ∃ a a', seatOf st x = some (Sum.inl a) ∧
        seatOf w x = some (Sum.inl a')))
    (hcomp : ∀ x, seatOf st x ≠ seatOf w x →
      ∃ z, seatOf st x = some (Sum.inr z) ∧
        seatOf w x = some (Sum.inr z.twin))
    (hlic : ∀ x, seatOf st x ≠ seatOf w x → FloaterSpec st x) :
    ∀ (R : List Card) (u : State),
      (∀ x, x ∈ R →
        seatOf u x = seatOf w x ∨ seatOf u x = seatOf st x) →
      (∀ x, x ∉ R → seatOf u x = seatOf st x) →
      (boardFixed st u ∧ foundsFixed st u ∧
         drawPool st = drawPool u ∧ cutOf st = cutOf u) →
      u.WF →
      (∀ x, x ∈ R → seatOf st x ≠ seatOf w x) →
      BareCargoEquiv st u := by
  intro R
  induction R with
  | nil =>
      intro u hP1 hP2 hP3 hwu hP5
      have hchart : chartAgree u st := by
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · intro x
          exact hP2 x (by simp)
        · obtain ⟨h1, h2⟩ := hP3.1
          exact ⟨fun j => (h1 j).symm, h2.symm⟩
        · intro s0
          exact (hP3.2.1 s0).symm
        · exact hP3.2.2.1.symm
        · exact hP3.2.2.2.symm
      rw [hroundtrip u st hchart]
      exact ⟨Steps.refl st, Steps.refl st⟩
  | cons c R' ih =>
      intro u hP1 hP2 hP3 hwu hP5
      rcases hP1 c List.mem_cons_self with hcu | hcu
      · -- PENDING: process c's undo and redo
        have hcc := hP5 c List.mem_cons_self
        obtain ⟨z, hcs, hcw⟩ := hcomp c hcc
        have hlicc := hlic c hcc
        have hsplit : ∀ x, seatOf u x = seatOf st x ∨
            seatOf u x = seatOf w x := by
          intro x
          by_cases hxR : x ∈ c :: R'
          · rcases hP1 x hxR with hw | hst
            · exact Or.inr hw
            · exact Or.inl hst
          · exact Or.inl (hP2 x hxR)
        have hcell_u : FloaterCell u c :=
          Or.inl ⟨z.twin, by rw [hcu, hcw]⟩
        have hmove_u : u.canPlace c (Sum.inr z) = true :=
          orbit_company_undo_license hwfst hwu hsplit hcu ⟨hcs, hcw⟩ hcc
            hlicc hrel
        obtain ⟨u', hstep, hrev, ⟨hed, hbf, hff, hdp, hco⟩⟩ :=
          floater_cargo_lift hwu hmove_u hcell_u
        have hwu' := tfc_tabToTab_wf hwu hstep
        -- the redo license at the successor
        have hcat : seatOf u' c = some (Sum.inr z) := by
          have h0 := hed c
          rwa [ite_eq_left rfl] at h0
        have hcst_u' : seatOf u' c = seatOf st c :=
          hcat.trans hcs.symm
        have hsplit' : ∀ x, seatOf u' x = seatOf st x ∨
            seatOf u' x = seatOf w x := by
          intro x
          by_cases hxc : x = c
          · rw [hxc]
            exact Or.inl hcst_u'
          · have h0 := hed x
            rw [ite_eq_right hxc] at h0
            rw [h0]
            rcases hsplit x with hs | hs
            · exact Or.inl hs
            · exact Or.inr hs
        have hcell_u' : FloaterCell u' c :=
          Or.inl ⟨z, by rw [hcst_u', hcs]⟩
        have hmove_u' : u'.canPlace c (Sum.inr z.twin) = true :=
          orbit_company_redo_license hwfst hwu' hsplit' hcst_u'
            ⟨hcs, hcw⟩ hcc hlicc hrel
        obtain ⟨u'', hstep2, hrev2, ⟨hed2, hbf2, hff2, hdp2, hco2⟩⟩ :=
          floater_cargo_lift (tfc_tabToTab_wf hwu hstep) hmove_u' hcell_u'
        -- the redo lands back on the current crate
        have hchart2 : chartAgree u'' u := by
          refine ⟨?_, ?_, ?_, ?_, ?_⟩
          · intro x
            by_cases hxc : x = c
            · rw [hxc]
              have h0 := hed2 c
              rw [ite_eq_left rfl] at h0
              exact h0.trans (hcu.trans hcw).symm
            · have h0 := hed2 x
              rw [ite_eq_right hxc] at h0
              have h1 := hed x
              rw [ite_eq_right hxc] at h1
              exact h0.trans h1
          · obtain ⟨h1, h2⟩ := hbf2
            obtain ⟨h3, h4⟩ := hbf
            exact ⟨fun j => (h1 j).symm.trans (h3 j).symm,
              h2.symm.trans h4.symm⟩
          · exact fun s0 => (hff2 s0).symm.trans (hff s0).symm
          · exact hdp2.symm.trans hdp.symm
          · exact hco2.symm.trans hco.symm
        have hu'' : u'' = u := hroundtrip u'' u hchart2
        -- recurse on the tail at the successor
        rw [hu''] at hstep2
        have hP1' : ∀ x, x ∈ R' →
            seatOf u' x = seatOf w x ∨ seatOf u' x = seatOf st x := by
          intro x hxR'
          by_cases hxc : x = c
          · rw [hxc]
            exact Or.inr hcst_u'
          · have h0 := hed x
            rw [ite_eq_right hxc] at h0
            rw [h0]
            rcases hsplit x with hs | hs
            · exact Or.inr hs
            · exact Or.inl hs
        have hP2' : ∀ x, x ∉ R' → seatOf u' x = seatOf st x := by
          intro x hxR'
          by_cases hxc : x = c
          · rw [hxc]
            exact hcst_u'
          · have hxR : x ∉ c :: R' := by
              intro hmem
              rcases List.mem_cons.mp hmem with h | h
              · exact hxc h
              · exact hxR' h
            have h0 := hed x
            rw [ite_eq_right hxc] at h0
            rw [h0]
            exact hP2 x hxR
        have hP3' : boardFixed st u' ∧ foundsFixed st u' ∧
            drawPool st = drawPool u' ∧ cutOf st = cutOf u' := by
          obtain ⟨hb1, hb2⟩ := hP3.1
          obtain ⟨h1, h2⟩ := hbf
          refine ⟨⟨fun j => (hb1 j).trans (h1 j), hb2.trans h2⟩,
            fun s0 => (hP3.2.1 s0).trans (hff s0),
            hP3.2.2.1.trans hdp, hP3.2.2.2.trans hco⟩
        have hP5' : ∀ x, x ∈ R' → seatOf st x ≠ seatOf w x :=
          fun x hxR' => hP5 x (List.mem_cons.mpr (Or.inr hxR'))
        have hclas_u' := ih u' hP1' hP2' hP3' hwu' hP5'
        -- the fired pair closes the u'↔u class
        have hpair' : BareCargoEquiv u' u :=
          ⟨Steps.cons ⟨c, Sum.inr z.twin, hstep2, hrev2⟩ (Steps.refl u),
            Steps.cons ⟨c, Sum.inr z, hstep, hrev⟩ (Steps.refl u')⟩
        exact orbit_bareCargo_trans hclas_u' hpair'
      · -- stale: c is already st-shaped; skip
        have hP1' : ∀ x, x ∈ R' →
            seatOf u x = seatOf w x ∨ seatOf u x = seatOf st x :=
          fun x hxR' => hP1 x (List.mem_cons.mpr (Or.inr hxR'))
        have hP2' : ∀ x, x ∉ R' → seatOf u x = seatOf st x := by
          intro x hxR'
          by_cases hxc : x = c
          · rw [hxc]
            exact hcu
          · have hxR : x ∉ c :: R' := by
              intro hmem
              rcases List.mem_cons.mp hmem with h | h
              · exact hxc h
              · exact hxR' h
            exact hP2 x hxR
        exact ih u hP1' hP2' hP3 hwu
          (fun x hxR' => hP5 x (List.mem_cons.mpr (Or.inr hxR')))

/-- **bareCargo_of_seatchart_company** — the ← direction, company
grade, ACTIVATED: the queue is the universe filtered over the
changed cards (a duplicate, should one ever arise, skips); every
membership obligation discharges by the filter's decision, and the
induction closes the class. -/
theorem bareCargo_of_seatchart_company {st w : State}
    (hwfst : st.WF) (hw : w.WF)
    (hroundtrip : ∀ A B, chartAgree A B → A = B)
    (hrel : ∀ x, (seatOf w x = seatOf st x) ∨
      (∃ z', seatOf st x = some (Sum.inr z') ∧
        seatOf w x = some (Sum.inr z'.twin)) ∨
      (x.rank = Rank.king ∧ ∃ a a', seatOf st x = some (Sum.inl a) ∧
        seatOf w x = some (Sum.inl a')))
    (hcomp : ∀ x, seatOf st x ≠ seatOf w x →
      ∃ z, seatOf st x = some (Sum.inr z) ∧
        seatOf w x = some (Sum.inr z.twin))
    (hlic : ∀ x, seatOf st x ≠ seatOf w x → FloaterSpec st x)
    (hread : boardFixed st w ∧ foundsFixed st w ∧
      drawPool st = drawPool w ∧ cutOf st = cutOf w) :
    BareCargoEquiv st w :=
  orbit_company_mirror_induct hwfst hroundtrip hrel hcomp hlic
    (Card.universe.filter
      (fun x => decide (seatOf st x ≠ seatOf w x))) w
    (fun x _ => Or.inl rfl)
    (fun x hx => by
      by_cases hxE : seatOf st x = seatOf w x
      · exact hxE.symm
      · exfalso
        refine hx (List.mem_filter.mpr ⟨Card.mem_universe x,
          decide_eq_true (fun hEq => hxE hEq)⟩))
    hread
    hw
    (fun x hx => of_decide_eq_true (List.mem_filter.mp hx).2)

/-- **bareCargo_iff_seatchart_company** — THE SEAT-CHART IFF,
COMPANY GRADE: over orbits whose changed cards all move company
(the twin hops), the bare-cargo class is EXACTLY the flat seat data
— the three-way net relation, the readouts, the st-side licensing
— with the WF fence at both ends as ever.  The unrestricted
statement's king arm stays priced in the ledger (the hidden-
emptiness upgrade and the king-ordering content); this promoted
grade covers every twin-hop orbit. -/
theorem bareCargo_iff_seatchart_company {st w : State}
    (hwfst : st.WF) (hw : w.WF)
    (hroundtrip : ∀ A B, chartAgree A B → A = B)
    (hcomp : ∀ x, seatOf st x ≠ seatOf w x →
      ∃ z, seatOf st x = some (Sum.inr z) ∧
        seatOf w x = some (Sum.inr z.twin)) :
    BareCargoEquiv st w ↔
      ((∀ x, (seatOf w x = seatOf st x) ∨
        (∃ z', seatOf st x = some (Sum.inr z') ∧
          seatOf w x = some (Sum.inr z'.twin)) ∨
        (x.rank = Rank.king ∧ ∃ a a', seatOf st x = some (Sum.inl a) ∧
          seatOf w x = some (Sum.inl a'))) ∧
       (boardFixed st w ∧ foundsFixed st w ∧
          drawPool st = drawPool w ∧ cutOf st = cutOf w) ∧
       (∀ x, seatOf st x ≠ seatOf w x → FloaterSpec st x)) := by
  constructor
  · intro hpair
    exact bareCargo_to_chartDiff hwfst hpair
  · intro ⟨hrel, hro, hlic⟩
    exact bareCargo_of_seatchart_company hwfst hw hroundtrip hrel
      hcomp hlic hro

/-- **bareCargo_reconstruct_kingFlat** — the flat single-king-move
reconstruction, licenses DERIVED: the king's net vacate data (with
the ledger's upgraded clause — the w-target pile's hidden deck is
empty at st) unpacks to a canPlace without any operational
assumption: the target pile's faceUp is empty because a resident
bottomer would double-bottom with the king at w (the carried
invariant), and the source cell rides the spec's own king arm.  The
degenerate equal-anchor corner is the trivial class (the chart round
trip pins st = w directly). -/
theorem bareCargo_reconstruct_kingFlat {st w : State} (hwf : st.WF)
    (_hw : w.WF)
    (hroundtrip : ∀ A B, chartAgree A B → A = B)
    {c : Card} {a a' : Anchor}
    (hking : c.rank = Rank.king)
    (hsec : seatOf st c = some (Sum.inl a))
    (hsew : seatOf w c = some (Sum.inl a'))
    (hlic : FloaterSpec st c)
    (hhid' : (st.piles a').hidden = [])
    (hcar : ∀ x, x ≠ c → seatOf w x = seatOf st x)
    (hread : boardFixed st w ∧ foundsFixed st w ∧
      drawPool st = drawPool w ∧ cutOf st = cutOf w) :
    BareCargoEquiv st w := by
  by_cases haa' : a = a'
  · -- the degenerate corner: every seat carried, the round trip closes
    subst haa'
    have hchart : chartAgree st w := by
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro x
        by_cases hxc : x = c
        · rw [hxc]
          exact hsec.trans hsew.symm
        · exact (hcar x hxc).symm
      · exact hread.1
      · exact hread.2.1
      · exact hread.2.2.1
      · exact hread.2.2.2
    have hwst : st = w := hroundtrip st w hchart
    rw [← hwst]
    exact ⟨Steps.refl st, Steps.refl st⟩
  · -- the real case: derive both licenses, apply the single-edit unit
    have hface' : (st.piles a').faceUp = [] := by
      cases hL : (st.piles a').faceUp with
      | nil => rfl
      | cons y ys =>
          exfalso
          have hyin : y ∈ (st.piles a').faceUp := by
            rw [hL]
            exact List.mem_cons_self
          have hdecl : ∀ j, j ≠ a' → y ∉ (st.piles j).faceUp := by
            intro j hjq hmemj
            have hccy : st.cardCount y = 1 :=
              hwf.2.2.1 y (Card.mem_universe y)
            exact (tfc_two_pile_zone_absurd hjq hccy
              (List.mem_append.mpr (Or.inr hmemj))
              (List.mem_append.mpr (Or.inr hyin))).elim
          have hholdy : st.pileHolding y = some a' :=
            tfc_pileHolding_pin hyin hdecl
          have hby : below y ((st.piles a').faceUp) = [] := by
            rw [hL, below_cons, ite_eq_left rfl]
          have hseyst : seatOf st y = some (Sum.inl a') :=
            tfc_seatOf_inl_intro hholdy hby
          have hyne : y ≠ c := by
            intro heq
            rw [heq] at hseyst
            have hcruz : some (Sum.inl a') = some (Sum.inl a) :=
              hseyst.symm.trans hsec
            injection hcruz with h1
            injection h1 with h2
            exact haa' h2.symm
          have hseyw : seatOf w y = some (Sum.inl a') :=
            (hcar y hyne).trans hseyst
          exact (hyne (orbit_bottom_unique hseyw hsew)).elim
    have hiso : (st.piles a').isEmpty = true :=
      (Pile.isEmpty_eq _).mpr ⟨hhid', by rw [hface']⟩
    have hmove : st.canPlace c (Sum.inl a') = true :=
      tfa_canPlace_inl hiso hking
    have hcell : FloaterCell st c := by
      rcases hlic with ⟨z₀, a₀, hse₀, -, -⟩ | ⟨a₁, hse₁, hking₁, hhid₁, -⟩
      · exfalso
        have hcruz : some (Sum.inr z₀) = some (Sum.inl a) :=
          hse₀.symm.trans hsec
        nomatch hcruz
      · have hp : a₁ = a := by
          have h2 : some (Sum.inl a₁) = some (Sum.inl a) :=
            hse₁.symm.trans hsec
          have h3 : Sum.inl a₁ = Sum.inl a := Option.some.inj h2
          injection h3
        rw [hp] at hhid₁
        exact Or.inr ⟨a, hsec, hking, hhid₁⟩
    exact bareCargo_reconstruct_singleEdit hwf hroundtrip hcar hsew hmove hcell hread

/-! ### §M4. THE KING-ARM HIDDEN DERIVATION (the → upgrade) — the
last-mover locator over a cargo journey, and with it the king's
vacate-target hidden-emptiness at the origin: the last hop into a′
rode the license (the target pile's emptiness at the hop state),
and the reversible legs conserve hidden decks all the way back. -/

/-- THE LAST-MOVER LOCATOR: along any cargo journey, a card whose
seats differ between the two ends has a LAST leg — a fired,
reversible hop by that card after whose successor the card's seat
never changes again down the remaining path. -/
private theorem orbit_last_mover_locator : ∀ {x0 y : State},
    Steps CargoLeg x0 y →
    ∀ (_hwf : x0.WF), ∀ (c : Card), seatOf x0 c ≠ seatOf y c →
    ∃ u ū, Steps CargoLeg x0 u ∧ ∃ b : Base,
      State.step u (Move.tabToTab c b) = some ū ∧
      reversibleAtW u (Move.tabToTab c b) ∧
      Steps CargoLeg ū y ∧ seatOf ū c = seatOf y c := by
  intro x0 y hpath
  induction hpath with
  | refl s =>
      intro _ c hc
      exact absurd rfl hc
  | @cons x1 x2 x3 hleg tail ih =>
      intro hwf0 c hc
      obtain ⟨m, b, hstep, hrev⟩ := hleg
      have hwf2 := tfc_tabToTab_wf hwf0 hstep
      by_cases hmv : seatOf x2 c = seatOf x1 c
      · -- stable at this leg: the change is in the tail
        obtain ⟨u, ū, hpre, b', hstep', hrev', hsuf, hsU⟩ :=
          ih hwf2 c (fun h => hc (hmv.symm.trans h))
        refine ⟨u, ū, orbit_steps_append
          (Steps.cons ⟨m, b, hstep, hrev⟩ (Steps.refl x2)) hpre,
          b', hstep', hrev', hsuf, hsU⟩
      · -- moved at this leg: c is the mover (the point edit)
        have hcm : c = m := by
          rcases Decidable.em (c = m) with hcmm | hnc
          · exact hcmm
          · exfalso
            have hed := tfc_seat_point_edit hwf0 hstep hrev
            have hx := hed c
            rw [ite_eq_right hnc] at hx
            exact hmv hx
        subst hcm
        by_cases hs : seatOf x3 c = seatOf x2 c
        · -- this leg is the last by c
          refine ⟨x1, x2, Steps.refl x1, b, hstep, hrev, tail, hs.symm⟩
        · -- c moves again: recurse on the tail
          obtain ⟨u, ū, hpre, b', hstep', hrev', hsuf, hsU⟩ :=
            ih hwf2 c (fun h => hs h.symm)
          refine ⟨u, ū, orbit_steps_append
            (Steps.cons ⟨c, b, hstep, hrev⟩ (Steps.refl x2)) hpre,
            b', hstep', hrev', hsuf, hsU⟩

/-- THE KING-ARM HIDDEN-[] DERIVATION (the → upgrade): a king
whose vacate-destination a′ differs from its st-bottom across a
class journey finds a′'s hidden deck empty at st — the last hop
into a′ rode the license (the target pile was empty at the hop
state), and the reversible legs conserve hidden decks back to the
origin. -/
theorem orbit_king_hidden_vacate {st w : State}
    (hwfst : st.WF) (hpair : BareCargoEquiv st w)
    {c : Card} {a a' : Anchor}
    (hchg : seatOf st c ≠ seatOf w c)
    (_hsec : seatOf st c = some (Sum.inl a))
    (hsew : seatOf w c = some (Sum.inl a')) :
    (st.piles a').hidden = [] := by
  obtain ⟨u, ū, hpre, b, hstep, hrev, hsuf, hsU⟩ :=
    orbit_last_mover_locator hpair.1 hwfst c hchg
  have hwfu := floater_orbit_wf_prsv hpre hwfst
  -- the last leg's landing is a′
  have hed := tfc_seat_point_edit hwfu hstep hrev
  have hx := hed c
  rw [ite_eq_left rfl] at hx
  have hbla : b = Sum.inl a' := by
    have hch : seatOf ū c = some (Sum.inl a') := hsU.trans hsew
    have hcruz : some b = some (Sum.inl a') := hx.symm.trans hch
    exact Option.some.inj hcruz
  subst hbla
  -- license: canPlace carried the target-pile emptiness
  have hR : tabToTabR u c (Sum.inl a') = true :=
    (tabToTabR_iff_reversibleAtW hwfu c (Sum.inl a')).mpr hrev
  obtain ⟨a₁, hhold, hcp, hbcell⟩ := tfc_tabToTabR_inv hR
  obtain ⟨hiso, -⟩ := canPlace_inl hcp
  have hempty : (u.piles a').hidden = [] :=
    ((Pile.isEmpty_eq _).mp hiso).1
  -- the reversible prefix conserves hidden decks
  obtain ⟨⟨h1, -⟩, -, -, -⟩ := orbit_readout_conserves hpre hwfst
  exact (h1 a').trans hempty

/-! ### §M5. THE KING MIRROR LICENSES — under the strengthened flat
king clause (the changed bottom-to-bottom mover's TARGET PILE IS
EMPTY AT ST — the unmediated-journey upgrade), the king undo and
redo legs derive their licenses from the flat data alone: the
source pile's crate-emptiness follows from the spec's own source
cell plus the anchor-elimination (st-shaped claimants co-anchor
with the mover; w-shaped claimants collapse into the mover or
contradict their own strengthened clause), and the target's
successor-emptiness holds because no st-anchor exists and any
w-anchor collapses into the mover by bottom-uniqueness. -/

/-- THE KING UNDO LICENSE at a consistent neighbor: with c's net
king vacate (st-anchor s, w-anchor t, genuinely changed, target
empty at st per the strengthened clause), the spec at st, and the
readout conservation to the crate, c's return leg onto s is
licensed and its cell is live. -/
private theorem orbit_king_undo_license {st w u : State}
    {c : Card} {s t : Anchor}
    (_hwfst : st.WF) (hwu : u.WF)
    (hsplit : ∀ x, seatOf u x = seatOf st x ∨
      seatOf u x = seatOf w x)
    (hcu : seatOf u c = seatOf w c)
    (harm : seatOf st c = some (Sum.inl s) ∧
      seatOf w c = some (Sum.inl t))
    (hchg : seatOf st c ≠ seatOf w c)
    (hlic : FloaterSpec st c)
    (hkt : (st.piles t).isEmpty = true)
    (hktall : ∀ x a a', seatOf st x = some (Sum.inl a) ∧
      seatOf w x = some (Sum.inl a') ∧ seatOf st x ≠ seatOf w x →
      (st.piles a').isEmpty = true)
    (hbf : boardFixed st u)
    (hrel : ∀ x, (seatOf w x = seatOf st x) ∨
      (∃ z', seatOf st x = some (Sum.inr z') ∧
        seatOf w x = some (Sum.inr z'.twin)) ∨
      (x.rank = Rank.king ∧ ∃ a a', seatOf st x = some (Sum.inl a) ∧
        seatOf w x = some (Sum.inl a'))) :
    u.canPlace c (Sum.inl s) = true ∧ FloaterCell u c := by
  obtain ⟨hcs, hcw⟩ := harm
  obtain ⟨hholdc, hbEc⟩ := tfc_seatOf_of_inl hcs
  have hsen : c ∈ (st.piles s).faceUp := pileHolding_mem hholdc
  -- the spec's own source cell (the king arm, seat-pinned)
  have hsrc : c.rank = Rank.king ∧ (st.piles s).hidden = [] := by
    rcases hlic with ⟨z₀, a₀, hse₀, hhold₀, harm₀⟩ |
      ⟨a₁, hse₁, hking₁, hhid₁, hemp⟩
    · exfalso
      have hcruz : some (Sum.inr z₀) = some (Sum.inl s) :=
        hse₀.symm.trans hcs
      nomatch hcruz
    · have hp : a₁ = s := by
        have h2 : some (Sum.inl a₁) = some (Sum.inl s) :=
          hse₁.symm.trans hcs
        have h3 : Sum.inl a₁ = Sum.inl s := Option.some.inj h2
        injection h3
      rw [hp] at hhid₁
      exact ⟨hking₁, hhid₁⟩
  obtain ⟨hking, hhids⟩ := hsrc
  -- the source pile's hidden deck at the crate
  have hhidu : (u.piles s).hidden = [] :=
    (hbf.1 s).symm.trans hhids
  -- nobody anchors the source pile at the crate
  have hnoanch : ∀ x, seatOf u x ≠ some (Sum.inl s) := by
    intro x hx
    rcases hsplit x with hu | hu
    · -- st-shaped claimant: co-anchors with c at st
      have hxst : seatOf st x = some (Sum.inl s) := by
        rw [← hu]; exact hx
      have hxc : x = c := orbit_bottom_unique hxst hcs
      rw [hxc] at hu
      exact hchg (hu.symm.trans hcu)
    · -- w-shaped claimant: its w-seat anchors s
      have hxw : seatOf w x = some (Sum.inl s) := by
        rw [← hu]; exact hx
      rcases hrel x with e | ⟨z', h1x, h2x⟩ | ⟨hk, b1, b2, h1', h2'⟩
      · -- carried: the st-anchor co-anchors with c
        have hxst : seatOf st x = some (Sum.inl s) := by
          rw [← e]; exact hxw
        have hxc : x = c := orbit_bottom_unique hxst hcs
        rw [hxc] at hxw
        have hcruz : some (Sum.inl s) = some (Sum.inl t) :=
          hxw.symm.trans hcw
        injection hcruz with h1
        injection h1 with h2
        rw [h2] at hcs
        exact hchg (hcs.trans hcw.symm)
      · -- hop claimant: the w-seat is inr, the claim is inl
        exfalso
        have hcruz : some (Sum.inr z'.twin) = some (Sum.inl s) :=
          h2x.symm.trans hxw
        nomatch hcruz
      · -- king claimant: its target is s — its own strengthened
        -- clause empties pile s at st, but c resides there
        exfalso
        have hssame : b2 = s := by
          have hcruz : some (Sum.inl b2) = some (Sum.inl s) :=
            h2'.symm.trans hxw
          have h3 : Sum.inl b2 = Sum.inl s := Option.some.inj hcruz
          injection h3
        have hchg' : seatOf st x ≠ seatOf w x := by
          intro h0
          have hb12 : b1 = b2 := by
            have hcruz2 : some (Sum.inl b1) = some (Sum.inl b2) :=
              h1'.symm.trans (h0.trans h2')
            have h3 : Sum.inl b1 = Sum.inl b2 :=
              Option.some.inj hcruz2
            injection h3
          have hstx : seatOf st x = some (Sum.inl s) := by
            rw [h1', hb12, hssame]
          have hxc : x = c := orbit_bottom_unique hstx hcs
          rw [hxc] at hxw
          have hcruz : some (Sum.inl s) = some (Sum.inl t) :=
            hxw.symm.trans hcw
          injection hcruz with h1
          injection h1 with h2
          rw [h2] at hcs
          exact hchg (hcs.trans hcw.symm)
        obtain ⟨hhid₂, hface₂⟩ :=
          (Pile.isEmpty_eq _).mp (hktall x b1 b2 ⟨h1', h2', hchg'⟩)
        rw [← hssame] at hsen
        rw [hface₂] at hsen
        exact absurd hsen (by simp)
  -- the source pile's faceUp at the crate
  have hfaceu : (u.piles s).faceUp = [] := by
    cases hL : (u.piles s).faceUp with
    | nil => rfl
    | cons y ys =>
        exfalso
        have hyin : y ∈ (u.piles s).faceUp := by
          rw [hL]
          exact List.mem_cons_self
        have hdecl : ∀ j, j ≠ s → y ∉ (u.piles j).faceUp := by
          intro j hjq hmemj
          have hccy : u.cardCount y = 1 :=
            hwu.2.2.1 y (Card.mem_universe y)
          exact (tfc_two_pile_zone_absurd hjq hccy
            (List.mem_append.mpr (Or.inr hmemj))
            (List.mem_append.mpr (Or.inr hyin))).elim
        have hholdy : u.pileHolding y = some s :=
          tfc_pileHolding_pin hyin hdecl
        have hby : below y ((u.piles s).faceUp) = [] := by
          rw [hL, below_cons, ite_eq_left rfl]
        exact (hnoanch y (tfc_seatOf_inl_intro hholdy hby)).elim
  -- assemble: license and cell
  have hiso : (u.piles s).isEmpty = true :=
    (Pile.isEmpty_eq _).mpr ⟨hhidu, hfaceu⟩
  have hhidt : (u.piles t).hidden = [] :=
    (hbf.1 t).symm.trans ((Pile.isEmpty_eq _).mp hkt).1
  exact ⟨tfa_canPlace_inl hiso hking,
    Or.inr ⟨t, by rw [hcu, hcw], hking, hhidt⟩⟩

/-- THE KING REDO LICENSE at the undo's successor: with c's net king
vacate (st-anchor s, w-anchor t, genuinely changed, target empty at
st), the spec at st, and the readout conservation to the successor,
c's forward leg back onto t is licensed and its cell is live — any
claimant of pile t either st-anchors (impossible: the strengthened
clause left the target empty at st) or w-anchors (collapsing into
the mover by bottom-uniqueness, whose two chart shapes disagree). -/
private theorem orbit_king_redo_license {st w u' : State}
    {c : Card} {s t : Anchor}
    (_hwfst : st.WF) (hwu' : u'.WF)
    (hsplit : ∀ x, seatOf u' x = seatOf st x ∨
      seatOf u' x = seatOf w x)
    (hcu : seatOf u' c = seatOf st c)
    (harm : seatOf st c = some (Sum.inl s) ∧
      seatOf w c = some (Sum.inl t))
    (hchg : seatOf st c ≠ seatOf w c)
    (hlic : FloaterSpec st c)
    (hkt : (st.piles t).isEmpty = true)
    (_hktall : ∀ x a a', seatOf st x = some (Sum.inl a) ∧
      seatOf w x = some (Sum.inl a') ∧ seatOf st x ≠ seatOf w x →
      (st.piles a').isEmpty = true)
    (hbf : boardFixed st u')
    (_hrel : ∀ x, (seatOf w x = seatOf st x) ∨
      (∃ z', seatOf st x = some (Sum.inr z') ∧
        seatOf w x = some (Sum.inr z'.twin)) ∨
      (x.rank = Rank.king ∧ ∃ a a', seatOf st x = some (Sum.inl a) ∧
        seatOf w x = some (Sum.inl a'))) :
    u'.canPlace c (Sum.inl t) = true ∧ FloaterCell u' c := by
  obtain ⟨hcs, hcw⟩ := harm
  -- t cannot equal s (the change would collapse)
  have hts : t = s → False := by
    intro heq
    rw [heq] at hcw
    exact hchg (hcs.trans hcw.symm)
  -- the target pile's hidden deck at the successor
  have hhidt : (u'.piles t).hidden = [] :=
    (hbf.1 t).symm.trans ((Pile.isEmpty_eq _).mp hkt).1
  have hfaceT : (st.piles t).faceUp = [] :=
    ((Pile.isEmpty_eq _).mp hkt).2
  -- the spec's own source cell (the king arm, seat-pinned)
  have hsrc : c.rank = Rank.king ∧ (st.piles s).hidden = [] := by
    rcases hlic with ⟨z₀, a₀, hse₀, hhold₀, harm₀⟩ |
      ⟨a₁, hse₁, hking₁, hhid₁, hemp⟩
    · exfalso
      have hcruz : some (Sum.inr z₀) = some (Sum.inl s) :=
        hse₀.symm.trans hcs
      nomatch hcruz
    · have hp : a₁ = s := by
        have h2 : some (Sum.inl a₁) = some (Sum.inl s) :=
          hse₁.symm.trans hcs
        have h3 : Sum.inl a₁ = Sum.inl s := Option.some.inj h2
        injection h3
      rw [hp] at hhid₁
      exact ⟨hking₁, hhid₁⟩
  obtain ⟨hking, hhids⟩ := hsrc
  have hhidu' : (u'.piles s).hidden = [] :=
    (hbf.1 s).symm.trans hhids
  -- nobody anchors the target pile at the successor
  have hnoanch : ∀ x, seatOf u' x ≠ some (Sum.inl t) := by
    intro x hx
    rcases hsplit x with hu | hu
    · -- st-shaped claimant: it would anchor t at st — the
      -- strengthened clause left pile t empty there
      have hxst : seatOf st x = some (Sum.inl t) := by
        rw [← hu]; exact hx
      obtain ⟨hholdx, hbEx⟩ := tfc_seatOf_of_inl hxst
      have hxmem : x ∈ (st.piles t).faceUp := pileHolding_mem hholdx
      rw [hfaceT] at hxmem
      exact absurd hxmem (by simp)
    · -- w-shaped claimant: its w-seat anchors t at w —
      -- bottom-uniqueness collapses it into c, whose two chart
      -- shapes disagree (t = s would kill the change)
      have hxw : seatOf w x = some (Sum.inl t) := by
        rw [← hu]; exact hx
      have hxc : x = c := orbit_bottom_unique hxw hcw
      rw [hxc] at hx
      have hcruz2 : some (Sum.inl t) = some (Sum.inl s) :=
        hx.symm.trans (hcu.trans hcs)
      have h3 : Sum.inl t = Sum.inl s := Option.some.inj hcruz2
      injection h3
      exact hts ‹t = s›
  -- the target pile's faceUp at the successor
  have hfaceu' : (u'.piles t).faceUp = [] := by
    cases hL : (u'.piles t).faceUp with
    | nil => rfl
    | cons y ys =>
        exfalso
        have hyin : y ∈ (u'.piles t).faceUp := by
          rw [hL]
          exact List.mem_cons_self
        have hdecl : ∀ j, j ≠ t → y ∉ (u'.piles j).faceUp := by
          intro j hjq hmemj
          have hccy : u'.cardCount y = 1 :=
            hwu'.2.2.1 y (Card.mem_universe y)
          exact (tfc_two_pile_zone_absurd hjq hccy
            (List.mem_append.mpr (Or.inr hmemj))
            (List.mem_append.mpr (Or.inr hyin))).elim
        have hholdy : u'.pileHolding y = some t :=
          tfc_pileHolding_pin hyin hdecl
        have hby : below y ((u'.piles t).faceUp) = [] := by
          rw [hL, below_cons, ite_eq_left rfl]
        exact (hnoanch y (tfc_seatOf_inl_intro hholdy hby)).elim
  -- assemble: license and cell
  have hiso : (u'.piles t).isEmpty = true :=
    (Pile.isEmpty_eq _).mpr ⟨hhidt, hfaceu'⟩
  exact ⟨tfa_canPlace_inl hiso hking,
    Or.inr ⟨s, by rw [hcu, hcs], hking, hhidu'⟩⟩


/-! ### §M6. THE MIXED MASTER INDUCTION AND THE FULL SEAT-CHART IFF —
the ← direction for mixed rosters (company twin hops plus king
vacates under the strengthened target-emptiness clause), the
activation at the filtered universe, and the public iff at full
grade. -/

/-- THE MIXED MASTER INDUCTION: the changed queue processes each
pending card by its own arm — company hops through the twin license
rows, king vacates through the king license rows (the strengthened
clause carrying the target-pile emptiness, both directions
derived); stale entries skip as ever. -/
private theorem orbit_mixed_mirror_induct {st w : State}
    (hwfst : st.WF)
    (hroundtrip : ∀ A B, chartAgree A B → A = B)
    (hrel : ∀ x, (seatOf w x = seatOf st x) ∨
      (∃ z', seatOf st x = some (Sum.inr z') ∧
        seatOf w x = some (Sum.inr z'.twin)) ∨
      (x.rank = Rank.king ∧ ∃ a a', seatOf st x = some (Sum.inl a) ∧
        seatOf w x = some (Sum.inl a')))
    (hktall : ∀ x a a', seatOf st x = some (Sum.inl a) ∧
      seatOf w x = some (Sum.inl a') ∧ seatOf st x ≠ seatOf w x →
      (st.piles a').isEmpty = true)
    (hlic : ∀ x, seatOf st x ≠ seatOf w x → FloaterSpec st x) :
    ∀ (R : List Card) (u : State),
      (∀ x, x ∈ R →
        seatOf u x = seatOf w x ∨ seatOf u x = seatOf st x) →
      (∀ x, x ∉ R → seatOf u x = seatOf st x) →
      (boardFixed st u ∧ foundsFixed st u ∧
         drawPool st = drawPool u ∧ cutOf st = cutOf u) →
      u.WF →
      (∀ x, x ∈ R → seatOf st x ≠ seatOf w x) →
      BareCargoEquiv st u := by
  intro R
  induction R with
  | nil =>
      intro u hP1 hP2 hP3 hwu hP5
      have hchart : chartAgree u st := by
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · intro x
          exact hP2 x (by simp)
        · obtain ⟨h1, h2⟩ := hP3.1
          exact ⟨fun j => (h1 j).symm, h2.symm⟩
        · intro s0
          exact (hP3.2.1 s0).symm
        · exact hP3.2.2.1.symm
        · exact hP3.2.2.2.symm
      rw [hroundtrip u st hchart]
      exact ⟨Steps.refl st, Steps.refl st⟩
  | cons c R' ih =>
      intro u hP1 hP2 hP3 hwu hP5
      rcases hP1 c List.mem_cons_self with hcu | hcu
      · -- PENDING: process c by its own arm
        have hcc := hP5 c List.mem_cons_self
        have hlicc := hlic c hcc
        have hsplit : ∀ x, seatOf u x = seatOf st x ∨
            seatOf u x = seatOf w x := by
          intro x
          by_cases hxR : x ∈ c :: R'
          · rcases hP1 x hxR with hw | hst
            · exact Or.inr hw
            · exact Or.inl hst
          · exact Or.inl (hP2 x hxR)
        rcases hrel c with hcarr | ⟨z, hcs, hcw⟩ |
          ⟨hkingc, a0, a'0, hcs, hcw⟩
        · exfalso
          exact hcc hcarr.symm
        · -- COMPANY hop: the twin license rows
          have hcell_u : FloaterCell u c :=
            Or.inl ⟨z.twin, by rw [hcu, hcw]⟩
          have hmove_u : u.canPlace c (Sum.inr z) = true :=
            orbit_company_undo_license hwfst hwu hsplit hcu
              ⟨hcs, hcw⟩ hcc hlicc hrel
          obtain ⟨u', hstep, hrev, ⟨hed, hbf, hff, hdp, hco⟩⟩ :=
            floater_cargo_lift hwu hmove_u hcell_u
          have hwu' := tfc_tabToTab_wf hwu hstep
          have hcat : seatOf u' c = some (Sum.inr z) := by
            have h0 := hed c
            rwa [ite_eq_left rfl] at h0
          have hcst_u' : seatOf u' c = seatOf st c :=
            hcat.trans hcs.symm
          have hsplit' : ∀ x, seatOf u' x = seatOf st x ∨
              seatOf u' x = seatOf w x := by
            intro x
            by_cases hxc : x = c
            · rw [hxc]
              exact Or.inl hcst_u'
            · have h0 := hed x
              rw [ite_eq_right hxc] at h0
              rw [h0]
              rcases hsplit x with hs | hs
              · exact Or.inl hs
              · exact Or.inr hs
          have hcell_u' : FloaterCell u' c :=
            Or.inl ⟨z, by rw [hcst_u', hcs]⟩
          have hmove_u' : u'.canPlace c (Sum.inr z.twin) = true :=
            orbit_company_redo_license hwfst hwu' hsplit' hcst_u'
              ⟨hcs, hcw⟩ hcc hlicc hrel
          obtain ⟨u'', hstep2, hrev2, ⟨hed2, hbf2, hff2, hdp2, hco2⟩⟩ :=
            floater_cargo_lift (tfc_tabToTab_wf hwu hstep) hmove_u'
              hcell_u'
          have hchart2 : chartAgree u'' u := by
            refine ⟨?_, ?_, ?_, ?_, ?_⟩
            · intro x
              by_cases hxc : x = c
              · rw [hxc]
                have h0 := hed2 c
                rw [ite_eq_left rfl] at h0
                exact h0.trans (hcu.trans hcw).symm
              · have h0 := hed2 x
                rw [ite_eq_right hxc] at h0
                have h1 := hed x
                rw [ite_eq_right hxc] at h1
                exact h0.trans h1
            · obtain ⟨h1, h2⟩ := hbf2
              obtain ⟨h3, h4⟩ := hbf
              exact ⟨fun j => (h1 j).symm.trans (h3 j).symm,
                h2.symm.trans h4.symm⟩
            · exact fun s0 => (hff2 s0).symm.trans (hff s0).symm
            · exact hdp2.symm.trans hdp.symm
            · exact hco2.symm.trans hco.symm
          have hu'' : u'' = u := hroundtrip u'' u hchart2
          rw [hu''] at hstep2
          have hP1' : ∀ x, x ∈ R' →
              seatOf u' x = seatOf w x ∨ seatOf u' x = seatOf st x := by
            intro x hxR'
            by_cases hxc : x = c
            · rw [hxc]
              exact Or.inr hcst_u'
            · have h0 := hed x
              rw [ite_eq_right hxc] at h0
              rw [h0]
              rcases hsplit x with hs | hs
              · exact Or.inr hs
              · exact Or.inl hs
          have hP2' : ∀ x, x ∉ R' → seatOf u' x = seatOf st x := by
            intro x hxR'
            by_cases hxc : x = c
            · rw [hxc]
              exact hcst_u'
            · have hxR : x ∉ c :: R' := by
                intro hmem
                rcases List.mem_cons.mp hmem with h | h
                · exact hxc h
                · exact hxR' h
              have h0 := hed x
              rw [ite_eq_right hxc] at h0
              rw [h0]
              exact hP2 x hxR
          have hP3' : boardFixed st u' ∧ foundsFixed st u' ∧
              drawPool st = drawPool u' ∧ cutOf st = cutOf u' := by
            obtain ⟨hb1, hb2⟩ := hP3.1
            obtain ⟨h1, h2⟩ := hbf
            refine ⟨⟨fun j => (hb1 j).trans (h1 j), hb2.trans h2⟩,
              fun s0 => (hP3.2.1 s0).trans (hff s0),
              hP3.2.2.1.trans hdp, hP3.2.2.2.trans hco⟩
          have hP5' : ∀ x, x ∈ R' → seatOf st x ≠ seatOf w x :=
            fun x hxR' => hP5 x (List.mem_cons.mpr (Or.inr hxR'))
          have hclas_u' := ih u' hP1' hP2' hP3' hwu' hP5'
          have hpair' : BareCargoEquiv u' u :=
            ⟨Steps.cons ⟨c, Sum.inr z.twin, hstep2, hrev2⟩ (Steps.refl u),
              Steps.cons ⟨c, Sum.inr z, hstep, hrev⟩ (Steps.refl u')⟩
          exact orbit_bareCargo_trans hclas_u' hpair'
        · -- KING vacate: the king license rows
          have hktc : (st.piles a'0).isEmpty = true :=
            hktall c a0 a'0 ⟨hcs, hcw, hcc⟩
          obtain ⟨hmove_u, hcell_u⟩ :=
            orbit_king_undo_license hwfst hwu hsplit hcu
              ⟨hcs, hcw⟩ hcc hlicc hktc hktall hP3.1 hrel
          obtain ⟨u', hstep, hrev, ⟨hed, hbf, hff, hdp, hco⟩⟩ :=
            floater_cargo_lift hwu hmove_u hcell_u
          have hwu' := tfc_tabToTab_wf hwu hstep
          have hcat : seatOf u' c = some (Sum.inl a0) := by
            have h0 := hed c
            rwa [ite_eq_left rfl] at h0
          have hcst_u' : seatOf u' c = seatOf st c :=
            hcat.trans hcs.symm
          have hsplit' : ∀ x, seatOf u' x = seatOf st x ∨
              seatOf u' x = seatOf w x := by
            intro x
            by_cases hxc : x = c
            · rw [hxc]
              exact Or.inl hcst_u'
            · have h0 := hed x
              rw [ite_eq_right hxc] at h0
              rw [h0]
              rcases hsplit x with hs | hs
              · exact Or.inl hs
              · exact Or.inr hs
          obtain ⟨hmove_u', hcell_u'⟩ :=
            orbit_king_redo_license hwfst hwu' hsplit' hcst_u'
              ⟨hcs, hcw⟩ hcc hlicc hktc hktall
              (by
                obtain ⟨hb1, hb2⟩ := hP3.1
                obtain ⟨h1, h2⟩ := hbf
                exact ⟨fun j => (hb1 j).trans (h1 j), hb2.trans h2⟩)
              hrel
          obtain ⟨u'', hstep2, hrev2, ⟨hed2, hbf2, hff2, hdp2, hco2⟩⟩ :=
            floater_cargo_lift (tfc_tabToTab_wf hwu hstep) hmove_u'
              hcell_u'
          have hchart2 : chartAgree u'' u := by
            refine ⟨?_, ?_, ?_, ?_, ?_⟩
            · intro x
              by_cases hxc : x = c
              · rw [hxc]
                have h0 := hed2 c
                rw [ite_eq_left rfl] at h0
                exact h0.trans (hcu.trans hcw).symm
              · have h0 := hed2 x
                rw [ite_eq_right hxc] at h0
                have h1 := hed x
                rw [ite_eq_right hxc] at h1
                exact h0.trans h1
            · obtain ⟨h1, h2⟩ := hbf2
              obtain ⟨h3, h4⟩ := hbf
              exact ⟨fun j => (h1 j).symm.trans (h3 j).symm,
                h2.symm.trans h4.symm⟩
            · exact fun s0 => (hff2 s0).symm.trans (hff s0).symm
            · exact hdp2.symm.trans hdp.symm
            · exact hco2.symm.trans hco.symm
          have hu'' : u'' = u := hroundtrip u'' u hchart2
          rw [hu''] at hstep2
          have hP1' : ∀ x, x ∈ R' →
              seatOf u' x = seatOf w x ∨ seatOf u' x = seatOf st x := by
            intro x hxR'
            by_cases hxc : x = c
            · rw [hxc]
              exact Or.inr hcst_u'
            · have h0 := hed x
              rw [ite_eq_right hxc] at h0
              rw [h0]
              rcases hsplit x with hs | hs
              · exact Or.inr hs
              · exact Or.inl hs
          have hP2' : ∀ x, x ∉ R' → seatOf u' x = seatOf st x := by
            intro x hxR'
            by_cases hxc : x = c
            · rw [hxc]
              exact hcst_u'
            · have hxR : x ∉ c :: R' := by
                intro hmem
                rcases List.mem_cons.mp hmem with h | h
                · exact hxc h
                · exact hxR' h
              have h0 := hed x
              rw [ite_eq_right hxc] at h0
              rw [h0]
              exact hP2 x hxR
          have hP3' : boardFixed st u' ∧ foundsFixed st u' ∧
              drawPool st = drawPool u' ∧ cutOf st = cutOf u' := by
            obtain ⟨hb1, hb2⟩ := hP3.1
            obtain ⟨h1, h2⟩ := hbf
            refine ⟨⟨fun j => (hb1 j).trans (h1 j), hb2.trans h2⟩,
              fun s0 => (hP3.2.1 s0).trans (hff s0),
              hP3.2.2.1.trans hdp, hP3.2.2.2.trans hco⟩
          have hP5' : ∀ x, x ∈ R' → seatOf st x ≠ seatOf w x :=
            fun x hxR' => hP5 x (List.mem_cons.mpr (Or.inr hxR'))
          have hclas_u' := ih u' hP1' hP2' hP3' hwu' hP5'
          have hpair' : BareCargoEquiv u' u :=
            ⟨Steps.cons ⟨c, Sum.inl a'0, hstep2, hrev2⟩ (Steps.refl u),
              Steps.cons ⟨c, Sum.inl a0, hstep, hrev⟩ (Steps.refl u')⟩
          exact orbit_bareCargo_trans hclas_u' hpair'
      · -- stale: c is already st-shaped; skip
        have hP1' : ∀ x, x ∈ R' →
            seatOf u x = seatOf w x ∨ seatOf u x = seatOf st x :=
          fun x hxR' => hP1 x (List.mem_cons.mpr (Or.inr hxR'))
        have hP2' : ∀ x, x ∉ R' → seatOf u x = seatOf st x := by
          intro x hxR'
          by_cases hxc : x = c
          · rw [hxc]
            exact hcu
          · have hxR : x ∉ c :: R' := by
              intro hmem
              rcases List.mem_cons.mp hmem with h | h
              · exact hxc h
              · exact hxR' h
            exact hP2 x hxR
        exact ih u hP1' hP2' hP3 hwu
          (fun x hxR' => hP5 x (List.mem_cons.mpr (Or.inr hxR')))

/-- **bareCargo_of_seatchart** — the ← direction, FULL grade,
ACTIVATED: the mixed induction at the filtered universe; the
hktall-clause is exactly the RHS's strengthened king arm with
nothing extra assumed. -/
theorem bareCargo_of_seatchart {st w : State}
    (hwfst : st.WF) (hw : w.WF)
    (hroundtrip : ∀ A B, chartAgree A B → A = B)
    (hrel : ∀ x, (seatOf w x = seatOf st x) ∨
      (∃ z', seatOf st x = some (Sum.inr z') ∧
        seatOf w x = some (Sum.inr z'.twin)) ∨
      (x.rank = Rank.king ∧ ∃ a a', seatOf st x = some (Sum.inl a) ∧
        seatOf w x = some (Sum.inl a') ∧
        (st.piles a').isEmpty = true))
    (hlic : ∀ x, seatOf st x ≠ seatOf w x → FloaterSpec st x)
    (hread : boardFixed st w ∧ foundsFixed st w ∧
      drawPool st = drawPool w ∧ cutOf st = cutOf w) :
    BareCargoEquiv st w := by
  -- the strengthened third arm feeds hktall by exact shape match
  have hktall : ∀ x a a', seatOf st x = some (Sum.inl a) ∧
      seatOf w x = some (Sum.inl a') ∧ seatOf st x ≠ seatOf w x →
      (st.piles a').isEmpty = true := by
    intro x a a' ⟨hxa, hx'a, hxchg⟩
    rcases hrel x with e | ⟨z, h1, h2⟩ |
      ⟨hk, b1, b2, h1', h2', hempty⟩
    · exfalso
      exact hxchg e.symm
      -- st-seat = w-seat via carried, contradicting changedness
    · exfalso
      have hcruz : some (Sum.inr z) = some (Sum.inl a) :=
        h1.symm.trans hxa
      nomatch hcruz
    · have hb1 : b1 = a := by
        have hcruz : some (Sum.inl b1) = some (Sum.inl a) :=
          h1'.symm.trans hxa
        have h3 : Sum.inl b1 = Sum.inl a := Option.some.inj hcruz
        injection h3
      have hb2 : b2 = a' := by
        have hcruz : some (Sum.inl b2) = some (Sum.inl a') :=
          h2'.symm.trans hx'a
        have h3 : Sum.inl b2 = Sum.inl a' := Option.some.inj hcruz
        injection h3
      rw [← hb2]
      exact hempty
  have hrel' : ∀ x, (seatOf w x = seatOf st x) ∨
      (∃ z', seatOf st x = some (Sum.inr z') ∧
        seatOf w x = some (Sum.inr z'.twin)) ∨
      (x.rank = Rank.king ∧ ∃ a a', seatOf st x = some (Sum.inl a) ∧
        seatOf w x = some (Sum.inl a')) := by
    intro x
    rcases hrel x with e | ⟨z, h1, h2⟩ |
      ⟨hk, b1, b2, h1', h2', hempty⟩
    · exact Or.inl e
    · exact Or.inr (Or.inl ⟨z, h1, h2⟩)
    · exact Or.inr (Or.inr ⟨hk, b1, b2, h1', h2'⟩)
  exact orbit_mixed_mirror_induct hwfst hroundtrip hrel' hktall hlic
    (Card.universe.filter
      (fun x => decide (seatOf st x ≠ seatOf w x))) w
    (fun x _ => Or.inl rfl)
    (fun x hx => by
      by_cases hxE : seatOf st x = seatOf w x
      · exact hxE.symm
      · exfalso
        refine hx (List.mem_filter.mpr ⟨Card.mem_universe x,
          decide_eq_true (fun hEq => hxE hEq)⟩))
    hread
    hw
    (fun x hx => of_decide_eq_true (List.mem_filter.mp hx).2)

/-! ### §M7. THE STRENGTHENED → DIRECTION — the full derivable
emission plus the mediate delimitation: the hidden-emptiness of the
king's target is derivable for every changed bottom-to-bottom
mover (folded into one master → row), and the FULL target-emptiness
(hidden and faceUp) is derivable whenever no OTHER changed card is
seated on the target at st — delimiting exactly the mediated cases
(the token-sliding card's content). -/


/-- **bareCargo_to_chartDiff_full** — the → direction at its FULL
derivable strength: the three-way net relation, the readouts, the
st-side licensing, and the king-target hidden-emptiness for every
changed bottom-to-bottom mover.  (The faceUp half is the fuel-set
membership `VKSet`, which the orbit invariant supplies — see
`bareCargo_to_chartDiff_vk`.) -/
theorem bareCargo_to_chartDiff_full {st w : State} (hwf : st.WF)
    (hpair : BareCargoEquiv st w) :
    (∀ c, (seatOf w c = seatOf st c) ∨
      (∃ z, seatOf st c = some (Sum.inr z) ∧
        seatOf w c = some (Sum.inr z.twin)) ∨
      (c.rank = Rank.king ∧ ∃ a a', seatOf st c = some (Sum.inl a) ∧
        seatOf w c = some (Sum.inl a'))) ∧
    (boardFixed st w ∧ foundsFixed st w ∧
       drawPool st = drawPool w ∧ cutOf st = cutOf w) ∧
    (∀ c, seatOf st c ≠ seatOf w c → FloaterSpec st c) ∧
    (∀ c a a', seatOf st c = some (Sum.inl a) ∧
       seatOf w c = some (Sum.inl a') ∧ seatOf st c ≠ seatOf w c →
       (st.piles a').hidden = []) := by
  obtain ⟨hrelX, hroX, hlicX⟩ := bareCargo_to_chartDiff hwf hpair
  exact ⟨hrelX, hroX, hlicX,
    fun c a a' ⟨h1', h2', hchg⟩ =>
      orbit_king_hidden_vacate hwf hpair hchg h1' h2'⟩
/-! ### §M9. THE SPARE-EMPTY INVARIANT (the token card's foundation
stone, extracted standalone): a reversible cargo leg either touches
NO empty pile (a company hop — the mover is seated, hence not a
king, hence its only licensed target is card-on-card, and neither
its donor nor the landing pile is empty) or swaps the consumed
target for the freshly-vacated donor (a bare king vacate — the
whole faceUp run leaves a hidden-empty pile behind).  Hence the
EXISTENCE of an empty pile is preserved along every orbit leg —
the reconstruction protocol's spare slot never disappears. -/

/-! ### §M9a. THE GENERALIZED PER-LEG READOUTS — the spare-empty
row's per-point facts, upgraded from ONE surviving witness to EVERY
empty seat and graded as cell DATA (the §M9B bijection and count
upgrades consume exactly this; the untouching/case work is the same
witness argument, now for arbitrary `j` instead of the single `e`). -/

/-- A nonempty faceUp run refutes pile-emptiness (fresh; rides the
Kit's membership row). -/
private theorem fli_isEmpty_false_of_faceUp {p : Pile}
    (h : p.faceUp ≠ []) : p.isEmpty = false := by
  obtain ⟨x, xs, hx⟩ := list_cons_of_ne_nil h
  exact Pile.isEmpty_eq_false_of_mem (by rw [hx]; exact List.mem_cons_self)

/-- An append onto a nonempty run is never nil (fresh; rides the
membership row). -/
private theorem fli_append_ne {X : List Card} {R : List Card} (hR : R ≠ []) :
    X ++ R ≠ [] := by
  cases hR2 : R with
  | nil => exact absurd hR2 hR
  | cons y R' =>
      have hmem : y ∈ X ++ y :: R' :=
        List.mem_append.mpr (Or.inr List.mem_cons_self)
      intro hc
      rw [hc] at hmem
      exact absurd hmem (by simp)

/-- The `decide` read-off of a refuted proposition (the trivia kit's
`decide_false_of_not` shape, private here). -/
private theorem fli_decide_false {p : Prop} [Decidable p] (h : ¬p) :
    decide p = false := by
  cases hdec : decide p with
  | false => rfl
  | true => exact absurd (of_decide_eq_true hdec) h

/-- The certified cell facts, REPACKAGED ANCHORED at the type-graded
`pileHolding` reading (fresh; the certificate row's `∃ a` witness is
data, so this row restates its content at the anchor the caller
already holds — the Prop-to-Type discipline: no witness is
extracted below). -/
private theorem fli_tab_cell_facts {u : State} {c : Card} {b : Base} {a : Anchor}
    (hwfu : u.WF) (hrev : reversibleAtW u (Move.tabToTab c b))
    (hpl : u.pileHolding c = some a) :
    u.canPlace c b = true ∧
      (below c (u.piles a).faceUp ≠ [] ∨
        (below c (u.piles a).faceUp = [] ∧ (u.piles a).hidden = [] ∧
          c.rank = Rank.king)) := by
  have hcell := (tabToTabR_iff_reversibleAtW hwfu c b).mpr hrev
  obtain ⟨a0, hhold0, hcp0, hb0cell⟩ := tfc_tabToTabR_inv hcell
  have h0 : a0 = a := Option.some.inj (hhold0.symm.trans hpl)
  subst h0
  exact ⟨hcp0, hb0cell⟩

/-- The honest leg shape, REPACKAGED ANCHORED the same way (fresh;
rides `step_tabToTab_inv`'s row with its witness identified to the
caller's anchor). -/
private theorem fli_step_shape {u u' : State} {c : Card} {b : Base} {a : Anchor}
    (hstep : State.step u (Move.tabToTab c b) = some u')
    (hpl : u.pileHolding c = some a) :
    u.canPlace c b = true ∧
      fromCard c (u.piles a).faceUp ≠ [] ∧
      u' = (u.setPile a
          (Pile.afterRunRemoved (u.piles a)
            (below c (u.piles a).faceUp))).putRun
        (fromCard c (u.piles a).faceUp) b := by
  obtain ⟨a0, hhold0, hcp0, hfr0, hs1⟩ := step_tabToTab_inv hstep
  have h0 : a0 = a := Option.some.inj (hhold0.symm.trans hpl)
  subst h0
  exact ⟨hcp0, hfr0, hs1⟩

/-- **OrbitEmptyCellData u u'** — THE GENERALIZED PER-LEG READOUTS at
TYPE GRADE: every reversible cargo leg either leaves the empty-seat
set UNCHANGED pointwise (the company hop), or performs the explicit
TWO-POINT SWAP on it (the bare king vacate).  Graded as data (not a
Prop disjunction) so the bijection construction below can eliminate
into `Type` without `Classical.choice`. -/
inductive OrbitEmptyCellData (u u' : State) : Type where
  /-- company hop: the empty set is pointwise unchanged -/
  | pointwise : (∀ j, (u.piles j).isEmpty = (u'.piles j).isEmpty) →
      OrbitEmptyCellData u u'
  /-- bare king vacate: the donor `a` is the fresh empty seat, the
  consumed target `a'` takes the run and stops being one, every
  other pile is carried verbatim -/
  | swap : (a a' : Anchor) → a ≠ a' →
      (u'.piles a).isEmpty = true → (u.piles a').isEmpty = true →
      (u.piles a).isEmpty = false → (u'.piles a').isEmpty = false →
      (∀ j, j ≠ a → j ≠ a' → u'.piles j = u.piles j) →
      OrbitEmptyCellData u u'

/-- THE PER-LEG CELL, EXTRACTED STANDALONE: the spare-empty row's
per-point content, generalized from one surviving witness to EVERY
empty seat — the single grunt row that the existence statement, the
bijection card and the count readout below all ride.  (The witness
anchor comes from the type-graded `pileHolding` option — the
Prop-inversion rows above are repackaged at it, so no Prop witness
is ever extracted into this data construction; the cell `Or` is
likewise consumed by a Prop-typed repackaging, never by a data
elimination.) -/
private def orbit_empty_celldata {u u' : State} {c : Card} {b : Base}
    (hwfu : u.WF)
    (hstep : State.step u (Move.tabToTab c b) = some u')
    (hrev : reversibleAtW u (Move.tabToTab c b)) :
    OrbitEmptyCellData u u' := by
  have hcell := (tabToTabR_iff_reversibleAtW hwfu c b).mpr hrev
  cases hpl : u.pileHolding c with
  | none =>
      exfalso
      rw [show tabToTabR u c b = false by simp only [tabToTabR, hpl]] at hcell
      exact Bool.noConfusion hcell
  | some a =>
      obtain ⟨hcp, hbcell⟩ := fli_tab_cell_facts hwfu hrev hpl
      obtain ⟨-, hfr, hs1shape⟩ := fli_step_shape hstep hpl
      have hmem : c ∈ (u.piles a).faceUp := pileHolding_mem hpl
      cases hbl : below c (u.piles a).faceUp with
      | nil =>
          -- BARE cell: the mover is a bottomed king; the faceUp run IS
          -- the pile and the hidden deck is empty, so the vacated donor
          -- is the fresh empty seat while the consumed target takes the
          -- run and stops being one.
          have hbare : (u.piles a).hidden = [] ∧ c.rank = Rank.king := by
            rcases hbcell with hbne | ⟨hb0, hhid, hkng⟩
            · exact absurd hbl hbne
            · exact ⟨hhid, hkng⟩
          obtain ⟨hhid, hkng⟩ := hbare
          cases b with
          | inr w₀ =>
              exfalso
              obtain ⟨k, -, hfit⟩ := canPlace_inr hcp
              obtain ⟨hidx, -⟩ := (canSitOn_eq c w₀).mp hfit
              have hlt := Rank.toIdx_lt w₀.rank
              have h12 : c.rank.toIdx = 12 := by rw [hkng]; rfl
              omega
          | inl a' =>
              obtain ⟨hiso, -⟩ := canPlace_inl hcp
              have haa' : a ≠ a' := by
                intro heq
                obtain ⟨-, hface_e⟩ := (Pile.isEmpty_eq _).mp hiso
                rw [heq] at hmem
                rw [hface_e] at hmem
                exact absurd hmem (by simp)
              refine OrbitEmptyCellData.swap a a' haa' ?_ hiso ?_ ?_ ?_
              · rw [hs1shape, putRun_eq_inl, setPile_piles_ne haa',
                  setPile_piles_self, hbl, Pile.afterRunRemoved_bare hhid]
                rfl
              · exact Pile.isEmpty_eq_false_of_mem hmem
              · rw [hs1shape, putRun_eq_inl, setPile_piles_self]
                exact fli_isEmpty_false_of_faceUp hfr
              · intro j hja hja'
                rw [hs1shape, putRun_eq_inl, setPile_piles_ne hja',
                  setPile_piles_ne hja]
      | cons z zs =>
          -- COMPANY cell: the mover is seated, hence not a king (the
          -- below tail has a top the mover must fit on), so the only
          -- licensed target is card-on-card; the donor keeps its below
          -- run at both ends, the landing gains the run on an existing
          -- top, and every other pile is untouched.
          have hbne : below c (u.piles a).faceUp ≠ [] := by rw [hbl]; simp
          have hnonking : c.rank ≠ Rank.king := by
            obtain ⟨w, hlz⟩ := lastOf_exists hbne
            obtain ⟨hsit, -⟩ := tfc_seat_parent hwfu hpl hlz
            obtain ⟨hidx, -⟩ := (canSitOn_eq c w).mp hsit
            have hwlt := Rank.toIdx_lt w.rank
            intro hk
            have h12 : c.rank.toIdx = 12 := by rw [hk]; rfl
            omega
          cases b with
          | inl a' =>
              exfalso
              obtain ⟨-, hking⟩ := canPlace_inl hcp
              exact hnonking hking
          | inr w₀ =>
              refine OrbitEmptyCellData.pointwise ?_
              intro j
              cases hptX : ((u.setPile a
                  (Pile.afterRunRemoved (u.piles a)
                    (below c ((u.piles a).faceUp)))).pileOfTop w₀) with
              | none =>
                  rw [hs1shape, putRun_inr_none hptX]
                  by_cases hja : j = a
                  · rw [hja, setPile_piles_self]
                    have h2 : (Pile.afterRunRemoved (u.piles a)
                        (below c (u.piles a).faceUp)).faceUp ≠ [] := by
                      rw [afterRunRemoved_ne hbne]
                      exact hbne
                    rw [Pile.isEmpty_eq_false_of_mem hmem,
                      fli_isEmpty_false_of_faceUp h2]
                  · rw [setPile_piles_ne hja]
              | some k2 =>
                  rw [hs1shape, putRun_inr_eq hptX]
                  by_cases hja : j = a
                  · rw [hja]
                    by_cases hka : k2 = a
                    · rw [hka, setPile_piles_self]
                      rw [Pile.isEmpty_eq_false_of_mem hmem,
                        fli_isEmpty_false_of_faceUp (fli_append_ne hfr)]
                    · rw [setPile_piles_ne (fun h => hka h.symm),
                        setPile_piles_self]
                      have h2 : (Pile.afterRunRemoved (u.piles a)
                          (below c (u.piles a).faceUp)).faceUp ≠ [] := by
                        rw [afterRunRemoved_ne hbne]
                        exact hbne
                      rw [Pile.isEmpty_eq_false_of_mem hmem,
                        fli_isEmpty_false_of_faceUp h2]
                  · by_cases hjk : j = k2
                    · rw [hjk, setPile_piles_self]
                      have hk2ne : k2 ≠ a := fun h => hja (hjk ▸ h)
                      have h1 : (u.piles k2).faceUp ≠ [] := by
                        have h3 := (tfc_pileOfTop_top hptX).1
                        rw [setPile_piles_ne hk2ne] at h3
                        exact h3
                      rw [fli_isEmpty_false_of_faceUp h1,
                        fli_isEmpty_false_of_faceUp (fli_append_ne hfr)]
                    · rw [setPile_piles_ne hjk, setPile_piles_ne hja]

/-- Per-leg preservation: one reversible slide preserves the
existence of an empty pile (now riding the generalized cell data —
the witness-grade internals moved up into
`orbit_empty_celldata`). -/
private theorem orbit_empty_exists_step {u u' : State} {c : Card} {b : Base}
    (hwfu : u.WF)
    (hstep : State.step u (Move.tabToTab c b) = some u')
    (hrev : reversibleAtW u (Move.tabToTab c b))
    (hemp : ∃ j, (u.piles j).isEmpty = true) :
    ∃ j', (u'.piles j').isEmpty = true := by
  rcases orbit_empty_celldata hwfu hstep hrev with
    hco | ⟨a, a', -, hd_t, -, -, -, -⟩
  · obtain ⟨e, he⟩ := hemp
    exact ⟨e, by rw [← hco e]; exact he⟩
  · exact ⟨a, hd_t⟩

/-- Chain-grade preservation along one cargo direction. -/
private theorem orbit_empty_exists_chain : ∀ {x y : State},
    Steps CargoLeg x y → x.WF →
    (∃ j, (x.piles j).isEmpty = true) →
    (∃ j, (y.piles j).isEmpty = true) := by
  intro x y h
  induction h with
  | refl s =>
      intro _ hsp
      exact hsp
  | @cons x1 x2 x3 hleg _ ih =>
      intro hwf0 hsp
      obtain ⟨m, b, hstep, hrev⟩ := id hleg
      exact ih (tfc_tabToTab_wf hwf0 hstep)
        (orbit_empty_exists_step hwf0 hstep hrev hsp)

/-- **bareCargo_orbit_spare_empty** — THE SPARE-EMPTY INVARIANT at
orbit grade: if some pile is empty at one end of a bare-cargo
class, some pile is empty at the other end.  (The foundation stone
for the token-sliding reconstruction: its intermediate-hop
protocol always has a spare slot to park through.) -/
theorem bareCargo_orbit_spare_empty {st w : State} (hwfst : st.WF)
    (hpair : BareCargoEquiv st w)
    (hemp : ∃ j, (st.piles j).isEmpty = true) :
    ∃ j, (w.piles j).isEmpty = true :=
  orbit_empty_exists_chain hpair.1 hwfst hemp

/-- **HasVacancy st** — the state carries a vacant spot (the king orbit's
fuel).  The predicate the king-orbit dichotomy is stated in. -/
def HasVacancy (st : State) : Prop := ∃ j, (st.piles j).isEmpty = true

/-- **vacuity_orbit_iff** — VACANCY IS AN ORBIT CONSTANT: the two ends of a
bare-cargo class agree on whether they carry a vacant spot.  This is the
characterization the king orbit rides — a state HAS vacancies in its orbit
exactly when it has one, so the king-shuffle regime is enabled uniformly on
one side of the class.  (`→` is the spare-empty row; `←` runs it along the
return direction from the mate's own WF, which the WF fence supplies.) -/
theorem vacuity_orbit_iff {st w : State} (hwfst : st.WF)
    (hpair : BareCargoEquiv st w) : HasVacancy st ↔ HasVacancy w := by
  have hwfw : w.WF := floater_orbit_wf_prsv hpair.1 hwfst
  constructor
  · intro h
    exact bareCargo_orbit_spare_empty hwfst hpair h
  · intro h
    exact bareCargo_orbit_spare_empty hwfw ⟨hpair.2, hpair.1⟩ h
/-! ### §M9B. THE SPARE-EMPTY UPGRADE — THE BIJECTION PAIR AND THE
EXACT COUNT (the owner's upgrade ask, 2026-10-18: "upgrade the
vacant theorem with bijection idea"): the generalized readouts expose
a genuine BIJECTION per leg — two functions between the empty-pile
subtypes whose composite is the identity on BOTH sides, the
composite-identity certificate of equinumerosity at pair grade, no
Mathlib.  The company cell's maps are the identity (the empty set is
literally unchanged, pointwise); the bare cell's maps are the
two-point swap — the consumed seat `a'` leaves the empty set, the
vacated donor `a` enters it, everything else fixed.  Composed along
the orbit this is the clean foundation for the numeric readout: THE
EMPTY-SEAT CARDINALITY IS AN ORBIT CONSTANT, and the spare-empty
row is exactly its count-at-least-one shadow. -/

/-- **EmptyEquiv u u'** — the equinumerosity witness between two
states' empty-pile subtypes: two functions whose composite is the
identity on BOTH sides (the repo's bijection certificate; a
structure, not a Prop, so the maps are inspectable data). -/
structure EmptyEquiv (u u' : State) : Type where
  /-- the forward map: u-empties land in u'-empties -/
  fwd : {j : Anchor // (u.piles j).isEmpty = true} →
      {j : Anchor // (u'.piles j).isEmpty = true}
  /-- the backward map: u'-empties land in u-empties -/
  bwd : {j : Anchor // (u'.piles j).isEmpty = true} →
      {j : Anchor // (u.piles j).isEmpty = true}
  /-- the composite is the identity on the u-side -/
  left_inv : ∀ j, bwd (fwd j) = j
  /-- and on the u'-side -/
  right_inv : ∀ j, fwd (bwd j) = j

/-- The identity equivalence. -/
def EmptyEquiv.refl (s : State) : EmptyEquiv s s where
  fwd j := j
  bwd j := j
  left_inv _ := rfl
  right_inv _ := rfl

/-- Equivalences compose: the composite maps' identities are the
two given ones stacked. -/
def EmptyEquiv.trans {x y z : State} (h1 : EmptyEquiv x y)
    (h2 : EmptyEquiv y z) : EmptyEquiv x z where
  fwd j := h2.fwd (h1.fwd j)
  bwd j := h1.bwd (h2.bwd j)
  left_inv j := by
    have h := h2.left_inv (h1.fwd j)
    rw [h]
    exact h1.left_inv j
  right_inv j := by
    have h := h1.right_inv (h2.bwd j)
    rw [h]
    exact h2.right_inv j

/-- **orbit_empty_equiv_step** — THE PER-LEG BIJECTION: one
reversible slide carries an explicit equinumerosity witness between
the origin's and the successor's empty-pile subtypes — in the company
cell the identity (the empty set is pointwise unchanged), in the
bare cell the two-point swap (the consumed seat exchanged for the
vacated donor). -/
def orbit_empty_equiv_step {u u' : State} {c : Card} {b : Base}
    (hwfu : u.WF)
    (hstep : State.step u (Move.tabToTab c b) = some u')
    (hrev : reversibleAtW u (Move.tabToTab c b)) :
    EmptyEquiv u u' := by
  rcases orbit_empty_celldata hwfu hstep hrev with
    hco | ⟨a, a', hne, hd_t, hl_t, hd_f, hl_f, hfix⟩
  · -- COMPANY: the empty set is literally unchanged — both maps
    -- are the underlying seat, transported by the pointwise equality.
    exact ⟨fun j => ⟨j.val, by rw [← hco j.val]; exact j.property⟩,
      fun j => ⟨j.val, by rw [hco j.val]; exact j.property⟩,
      fun _ => Subtype.ext rfl, fun _ => Subtype.ext rfl⟩
  · -- BARE: the two-point swap — no u-empty sits on the donor, no
    -- u'-empty sits on the consumed seat, so both maps send the
    -- special seat across and fix the rest verbatim.
    have hnea : ∀ k, (u.piles k).isEmpty = true → k ≠ a := by
      intro k hk heq
      rw [heq] at hk
      rw [hd_f] at hk
      exact absurd hk (by simp)
    have hnea' : ∀ k, (u'.piles k).isEmpty = true → k ≠ a' := by
      intro k hk heq
      rw [heq] at hk
      rw [hl_f] at hk
      exact absurd hk (by simp)
    -- the anchor-level involutions: each composite fixes every seat
    -- that is not the OTHER cell's special point
    have hcomp : ∀ k : Anchor, k ≠ a →
        (if (if k = a' then a else k) = a then a' else
          (if k = a' then a else k)) = k := by
      intro k hka
      by_cases hka' : k = a'
      · rw [ite_eq_left hka', ite_eq_left (rfl : a = a)]
        exact hka'.symm
      · have hinner : (if k = a' then a else k) = k := ite_eq_right hka'
        by_cases hkea : k = a
        · exact absurd hkea hka
        · rw [hinner, ite_eq_right hkea]
    have hcomp' : ∀ k : Anchor, k ≠ a' →
        (if (if k = a then a' else k) = a' then a else
          (if k = a then a' else k)) = k := by
      intro k hka'
      by_cases hka : k = a
      · rw [ite_eq_left hka, ite_eq_left (rfl : a' = a')]
        exact hka.symm
      · have hinner : (if k = a then a' else k) = k := ite_eq_right hka
        by_cases hkea : k = a'
        · exact absurd hkea hka'
        · rw [hinner, ite_eq_right hkea]
    exact ⟨
      fun j => ⟨if j.val = a' then a else j.val, by
        by_cases hj : j.val = a'
        · rw [ite_eq_left hj]
          exact hd_t
        · rw [ite_eq_right hj]
          rw [hfix j.val (hnea j.val j.property) hj]
          exact j.property⟩,
      fun j => ⟨if j.val = a then a' else j.val, by
        by_cases hj : j.val = a
        · rw [ite_eq_left hj]
          exact hl_t
        · rw [ite_eq_right hj]
          rw [← hfix j.val hj (hnea' j.val j.property)]
          exact j.property⟩,
      fun j => Subtype.ext (hcomp j.val (hnea j.val j.property)),
      fun j => Subtype.ext (hcomp' j.val (hnea' j.val j.property))⟩

/-- Chain-grade existence along one cargo direction: composing the
per-leg witnesses through the orbit (the `Steps` spine is
Prop-graded, so the orbit-side claim is the genuine `Nonempty` of
the composite-identity witness — no data is extracted from the path,
`Classical.choice` stays unbuilt). -/
private theorem orbit_empty_iso_chain : ∀ {x y : State},
    Steps CargoLeg x y → x.WF → Nonempty (EmptyEquiv x y) := by
  intro x y h
  induction h with
  | refl s => intro _; exact ⟨EmptyEquiv.refl s⟩
  | @cons x1 x2 x3 hleg _ ih =>
      intro hwf0
      obtain ⟨m, b, hstep, hrev⟩ := id hleg
      exact (ih (tfc_tabToTab_wf hwf0 hstep)).elim
        (fun e2 =>
          ⟨(orbit_empty_equiv_step hwf0 hstep hrev).trans e2⟩)

/-- **bareCargo_orbit_empty_iso** — THE EMPTY-SET AT ORBIT GRADE:
the two ends of a bare-cargo class pair carry an equinumerosity
witness between their empty-pile subtypes (the composite-identity
certificate composed along the whole orbit; a `Nonempty` claim —
the orbit spine is a Prop, so this is the honest existence grade,
and the per-leg def above is the inspectable data). -/
theorem bareCargo_orbit_empty_iso {st w : State} (hwfst : st.WF)
    (hpair : BareCargoEquiv st w) : Nonempty (EmptyEquiv st w) :=
  orbit_empty_iso_chain hpair.1 hwfst

/-! #### §M9b-list. THE LAST MILE — the elementary list kit: a
filter's cons reads as the head's Bool indicator plus the tail, so
both the pointwise case and the two-point swap close by `omega`
once the point facts are in.  (Deliberately elementary — no
pigeonhole, no permutation algebra: the composite-identity pair
supplies the CONTENT, the indicator arithmetic supplies the
NUMBER.) -/

/-- The Bool-to-indicator bridge (fresh). -/
private def fli_b2n : Bool → Nat
  | true => 1
  | false => 0

private theorem fli_b2n_true : fli_b2n true = 1 := rfl

private theorem fli_b2n_false : fli_b2n false = 0 := rfl

/-- A filter's cons: the head contributes its indicator. -/
private theorem fli_len_cons {α : Type} (p : α → Bool) (z : α) (zs : List α) :
    ((z :: zs).filter p).length = fli_b2n (p z) + (zs.filter p).length := by
  rw [List.filter_cons]
  by_cases hp : p z = true
  · have e1 : (if p z = true then z :: zs.filter p else zs.filter p)
      = z :: zs.filter p := ite_eq_left hp
    rw [e1, List.length_cons, hp, fli_b2n_true]
    omega
  · have hpf : p z = false := by
      cases hp2 : p z with
      | false => rfl
      | true => exact absurd hp2 hp
    have e1 : (if p z = true then z :: zs.filter p else zs.filter p)
        = zs.filter p := ite_eq_right (by rw [hpf]; simp)
    rw [e1, hpf, fli_b2n_false]
    omega

/-- Pointwise-equal predicates give equal filter lengths. -/
private theorem fli_filter_pointwise {α : Type} : ∀ {L : List α} {p q : α → Bool},
    (∀ j ∈ L, p j = q j) → (L.filter p).length = (L.filter q).length := by
  intro L
  induction L with
  | nil => intro p q _; rfl
  | cons z zs ih =>
      intro p q h
      have hz : p z = q z := h z (List.mem_cons_self)
      have hzs : ∀ j ∈ zs, p j = q j :=
        fun j hj => h j (List.mem_cons_of_mem _ hj)
      have he := ih hzs
      rw [fli_len_cons p z zs, fli_len_cons q z zs, hz]
      omega

/-- THE TWO-POINT SWAP AT LENGTH GRADE: predicates that agree off
the two special points, flip `false→true` at `x` and `true→false`
at `y`, have filter lengths differing by the count of `x` against
`y` — the strengthened bookkeeping that stays inductive down the
tails. -/
private theorem fli_filter_two_swap {α : Type} [DecidableEq α] :
    ∀ {L : List α} {p q : α → Bool} {x y : α}, x ≠ y →
      p x = false → q x = true → p y = true → q y = false →
      (∀ z ∈ L, z ≠ x → z ≠ y → p z = q z) →
      (L.filter p).length + ((L.filter (fun z => decide (z = x))).length)
        = (L.filter q).length + ((L.filter (fun z => decide (z = y))).length) := by
  intro L
  induction L with
  | nil => intro p q x y hxy hpx hqx hpy hqy hrest; rfl
  | cons z zs ih =>
      intro p q x y hxy hpx hqx hpy hqy hrest
      have hzs : ∀ w ∈ zs, w ≠ x → w ≠ y → p w = q w :=
        fun w hw => hrest w (List.mem_cons_of_mem _ hw)
      have he := ih (p := p) (q := q) (x := x) (y := y)
        hxy hpx hqx hpy hqy hzs
      by_cases hzx : z = x
      · rw [hzx]
        have hdx : decide (x = x) = true := decide_eq_true rfl
        have hdy : decide (x = y) = false := fli_decide_false (fun h => hxy h)
        rw [fli_len_cons p x zs, fli_len_cons q x zs,
          fli_len_cons (fun w => decide (w = x)) x zs,
          fli_len_cons (fun w => decide (w = y)) x zs]
        rw [hpx, hqx, hdx, hdy]
        omega
      · by_cases hzy : z = y
        · rw [hzy]
          have hdx : decide (y = x) = false :=
            fli_decide_false (fun h => hxy h.symm)
          have hdy : decide (y = y) = true := decide_eq_true rfl
          rw [fli_len_cons p y zs, fli_len_cons q y zs,
            fli_len_cons (fun w => decide (w = x)) y zs,
            fli_len_cons (fun w => decide (w = y)) y zs]
          rw [hpy, hqy, hdx, hdy]
          omega
        · have hzp : p z = q z := hrest z (List.mem_cons_self) hzx hzy
          have hdx : decide (z = x) = false := fli_decide_false hzx
          have hdy : decide (z = y) = false := fli_decide_false hzy
          rw [fli_len_cons p z zs, fli_len_cons q z zs,
            fli_len_cons (fun w => decide (w = x)) z zs,
            fli_len_cons (fun w => decide (w = y)) z zs]
          rw [hzp, hdx, hdy]
          omega

/-- The singleton count over the all-list: every anchor is filtered
exactly once (decided on the literal). -/
private theorem fli_one_count (x : Anchor) :
    (Anchor.all.filter (fun z => decide (z = x))).length = 1 := by
  cases x <;> rfl

/-- **emptyCount st** — the number of empty tableau seats: THE
NUMERIC SHAPE of the spare-empty invariant. -/
def emptyCount (st : State) : Nat :=
  (Anchor.all.filter (fun j => (st.piles j).isEmpty)).length

/-- Per-leg count preservation (the last-mile arithmetic). -/
private theorem orbit_empty_count_step {u u' : State} {c : Card} {b : Base}
    (hwfu : u.WF)
    (hstep : State.step u (Move.tabToTab c b) = some u')
    (hrev : reversibleAtW u (Move.tabToTab c b)) :
    emptyCount u = emptyCount u' := by
  rcases orbit_empty_celldata hwfu hstep hrev with
    hco | ⟨a, a', hne, hd_t, hl_t, hd_f, hl_f, hfix⟩
  · show (Anchor.all.filter (fun j => (u.piles j).isEmpty)).length
        = (Anchor.all.filter (fun j => (u'.piles j).isEmpty)).length
    exact fli_filter_pointwise (fun j _ => hco j)
  · have h1 := fli_filter_two_swap (L := Anchor.all) hne hd_f hd_t hl_t hl_f
      (fun z _ hza hza' => (congrArg Pile.isEmpty (hfix z hza hza')).symm)
    have h2 := fli_one_count a
    have h3 := fli_one_count a'
    show (Anchor.all.filter (fun j => (u.piles j).isEmpty)).length
        = (Anchor.all.filter (fun j => (u'.piles j).isEmpty)).length
    omega

/-- Chain-grade count preservation along one cargo direction. -/
private theorem orbit_empty_count_chain : ∀ {x y : State},
    Steps CargoLeg x y → x.WF → emptyCount x = emptyCount y := by
  intro x y h
  induction h with
  | refl s => intro _; rfl
  | @cons x1 x2 x3 hleg _ ih =>
      intro hwf0
      obtain ⟨m, b, hstep, hrev⟩ := id hleg
      exact (orbit_empty_count_step hwf0 hstep hrev).trans
        (ih (tfc_tabToTab_wf hwf0 hstep))

/-- **bareCargo_orbit_empty_count** — THE EMPTY-SEAT CARDINALITY IS
AN ORBIT CONSTANT: the number of empty piles is the same at both
ends of a bare-cargo class pair — the exact-count upgrade of the
spare-empty invariant (which is its count-at-least-one shadow). -/
theorem bareCargo_orbit_empty_count {st w : State} (hwfst : st.WF)
    (hpair : BareCargoEquiv st w) :
    emptyCount st = emptyCount w :=
  orbit_empty_count_chain hpair.1 hwfst

/-- **vacuity_count_orbit_iff** — the COUNT-grade companion of
`vacuity_orbit_iff`: the two ends of a class agree on whether the vacancy
count is zero, i.e. the "no vacant spot at all" states form one side of the
orbit and every vacancy-carrying state the other. -/
theorem vacuity_count_orbit_iff {st w : State} (hwfst : st.WF)
    (hpair : BareCargoEquiv st w) : emptyCount st = 0 ↔ emptyCount w = 0 := by
  have h := bareCargo_orbit_empty_count hwfst hpair
  constructor
  · intro h0; rw [← h]; exact h0
  · intro h0; rw [h]; exact h0

/-! ### §M11. THE VACANT ⊎ KING-BOTTOM FUEL SET — the king orbit's node set
is POINTWISE fixed along the bare-cargo class (the §M9a/§M9B machinery one
level up: what the empty-set bijection does for vacancies, the two-point
readout below does for `vacant ∨ king-bottom`), and INSIDE the set only
kings move: a node that stops being vacant is a king-bottom, and one that
stops being a king-bottom is vacant.  With it the cardinality trichotomy of
the king card is three rows — the set is constant, no vacancy stops the
shuffle, a vacancy enables it — and the Z/2Z company hop touches no node of
the set at all. -/

/-- **VacantSpot st j** — the pile at `j` is empty (a vacant spot). -/
abbrev VacantSpot (st : State) (j : Anchor) : Prop := (st.piles j).isEmpty = true

/-- **KingBottom st j** — a bare bottomed king: the pile has no hidden cards
and a king bottoms its face-up run (so the king can be shuffled out of it). -/
def KingBottom (st : State) (j : Anchor) : Prop :=
  ∃ c, seatOf st c = some (Sum.inl j) ∧ c.rank = Rank.king ∧
    (st.piles j).hidden = []

/-- **VKSet st j** — the king orbit's fuel set: vacant, or filled by a
bottomed king. -/
abbrev VKSet (st : State) (j : Anchor) : Prop :=
  VacantSpot st j ∨ KingBottom st j

/-- The `putRun` literal's emptiness: appending a nonempty run never leaves a
pile empty.  (The `have`-shaped statement is what `putRun_inr_eq` produces;
`Pile.isEmpty_eq_false_of_mem` at the run's head closes it.) -/
private theorem fli_append_let_isEmpty_false {q : Pile} {run : List Card}
    (h : run ≠ []) :
    (have __src := q;
      { hidden := __src.hidden, faceUp := q.faceUp ++ run } : Pile).isEmpty = false := by
  obtain ⟨x, xs, hx⟩ := list_cons_of_ne_nil h
  subst hx
  exact Pile.isEmpty_eq_false_of_mem (c := x)
    (p := (have __src := q;
      { hidden := __src.hidden, faceUp := q.faceUp ++ (x :: xs) } : Pile))
    (List.mem_append_right _ (List.mem_cons_self ..))

/-- **orbit_vk_step** — THE PER-LEG FUEL READOUT: one reversible cargo leg
fixes `vacant ∨ king-bottom` pointwise.  Company hop: no empty pile and no
bottomed king changes (the empty set is pointwise fixed, the hidden decks
ride `boardFixed`, and no `inl` seat is created or destroyed — the mover
stays `inr`).  Bare-king hop: the donor and the consumed target swap roles —
the donor becomes vacant, the target gains the bare king — and every other
pile is carried verbatim. -/
private theorem orbit_vk_step {u u' : State} {c : Card} {b : Base}
    (hwf : u.WF)
    (hstep : State.step u (Move.tabToTab c b) = some u')
    (hrev : reversibleAtW u (Move.tabToTab c b)) :
    ∀ j, VKSet u j ↔ VKSet u' j := by
  have hed := tfc_seat_point_edit hwf hstep hrev
  have hhid : ∀ j, (u.piles j).hidden = (u'.piles j).hidden :=
    (tfa_slide_conserves hwf hstep hrev).1.1
  obtain ⟨a, hhold, hcp, hcell⟩ :=
    tfc_tabToTabR_inv ((tabToTabR_iff_reversibleAtW hwf c b).mpr hrev)
  obtain ⟨hcp0, hfr, hs1shape⟩ := fli_step_shape hstep hhold
  have hmem : c ∈ (u.piles a).faceUp := pileHolding_mem hhold
  intro j
  cases b with
  | inr w₀ =>
      have hbne : below c (u.piles a).faceUp ≠ [] := by
        intro hb0
        have hkng : c.rank = Rank.king := by
          rcases hcell with hbne | ⟨-, -, hk⟩
          · exact absurd hb0 hbne
          · exact hk
        obtain ⟨k, -, hfit⟩ := canPlace_inr hcp
        obtain ⟨hidx, -⟩ := (canSitOn_eq c w₀).mp hfit
        have hlt := Rank.toIdx_lt w₀.rank
        have h12 : c.rank.toIdx = 12 := by rw [hkng]; rfl
        omega
      obtain ⟨z, hz⟩ := lastOf_exists hbne
      have hse_c : seatOf u c = some (Sum.inr z) := tfc_seatOf_inr_intro hhold hz
      have hseat_inl : ∀ x j', seatOf u' x = some (Sum.inl j') ↔
          seatOf u x = some (Sum.inl j') := by
        intro x j'
        rw [hed x]
        by_cases hxc : x = c
        · subst x
          rw [ite_eq_left rfl, hse_c]
          simp
        · rw [ite_eq_right hxc]
      have hks : ∀ j', KingBottom u j' ↔ KingBottom u' j' := by
        intro j'
        constructor
        · rintro ⟨x, hse, hk, hhd⟩
          exact ⟨x, (hseat_inl x j').mpr hse, hk, by rw [← hhid j']; exact hhd⟩
        · rintro ⟨x, hse, hk, hhd⟩
          exact ⟨x, (hseat_inl x j').mp hse, hk, by rw [hhid j']; exact hhd⟩
      have hco : ∀ j', (u.piles j').isEmpty = (u'.piles j').isEmpty := by
        intro j'
        cases hptX : ((u.setPile a
            (Pile.afterRunRemoved (u.piles a)
              (below c ((u.piles a).faceUp)))).pileOfTop w₀) with
        | none =>
            rw [hs1shape, putRun_inr_none hptX]
            by_cases hja : j' = a
            · rw [hja, setPile_piles_self]
              have h2 : (Pile.afterRunRemoved (u.piles a)
                  (below c (u.piles a).faceUp)).faceUp ≠ [] := by
                rw [afterRunRemoved_ne hbne]
                exact hbne
              rw [Pile.isEmpty_eq_false_of_mem hmem,
                fli_isEmpty_false_of_faceUp h2]
            · rw [setPile_piles_ne hja]
        | some k2 =>
            rw [hs1shape, putRun_inr_eq hptX]
            by_cases hja : j' = a
            · rw [hja]
              by_cases hka : k2 = a
              · rw [hka, setPile_piles_self]
                rw [Pile.isEmpty_eq_false_of_mem hmem]
                exact (fli_append_let_isEmpty_false
                  (q := (u.setPile a (Pile.afterRunRemoved (u.piles a)
                    (below c (u.piles a).faceUp))).piles a) hfr).symm
              · rw [setPile_piles_ne (fun h => hka h.symm),
                  setPile_piles_self]
                have h2 : (Pile.afterRunRemoved (u.piles a)
                    (below c (u.piles a).faceUp)).faceUp ≠ [] := by
                  rw [afterRunRemoved_ne hbne]
                  exact hbne
                rw [Pile.isEmpty_eq_false_of_mem hmem,
                  fli_isEmpty_false_of_faceUp h2]
            · by_cases hjk : j' = k2
              · rw [hjk, setPile_piles_self]
                have hk2ne : k2 ≠ a := fun h => hja (hjk ▸ h)
                have h1 : (u.piles k2).faceUp ≠ [] := by
                  have h3 := (tfc_pileOfTop_top hptX).1
                  rw [setPile_piles_ne hk2ne] at h3
                  exact h3
                rw [fli_isEmpty_false_of_faceUp h1]
                exact (fli_append_let_isEmpty_false
                  (q := (u.setPile a (Pile.afterRunRemoved (u.piles a)
                    (below c (u.piles a).faceUp))).piles k2) hfr).symm
              · rw [setPile_piles_ne hjk, setPile_piles_ne hja]
      constructor
      · rintro (h | h)
        · have hv : (u'.piles j).isEmpty = true := by rw [← hco j]; exact h
          exact Or.inl hv
        · exact Or.inr ((hks j).mp h)
      · rintro (h | h)
        · have hv : (u.piles j).isEmpty = true := by rw [hco j]; exact h
          exact Or.inl hv
        · exact Or.inr ((hks j).mpr h)
  | inl a' =>
      have hiso : (u.piles a').isEmpty = true := (canPlace_inl hcp).1
      have hkng : c.rank = Rank.king := (canPlace_inl hcp).2
      have hb0 : below c (u.piles a).faceUp = [] := by
        rcases hcell with hbne | ⟨hb0, -, -⟩
        · exfalso
          obtain ⟨z, hlast⟩ := lastOf_exists hbne
          obtain ⟨hsit, -⟩ := tfc_seat_parent hwf hhold hlast
          obtain ⟨hidx, -⟩ := (canSitOn_eq c z).mp hsit
          have hzlt := Rank.toIdx_lt z.rank
          have h12 : c.rank.toIdx = 12 := by rw [hkng]; rfl
          omega
        · exact hb0
      have hhidA : (u.piles a).hidden = [] := by
        rcases hcell with hbne | ⟨-, hhid, -⟩
        · exact absurd hb0 hbne
        · exact hhid
      have haa' : a ≠ a' := by
        intro heq
        rw [heq, ((Pile.isEmpty_eq _).mp hiso).2] at hmem
        exact absurd hmem (by simp)
      have hse_u : seatOf u c = some (Sum.inl a) :=
        tfc_seatOf_inl_intro hhold hb0
      have hse_v : seatOf u' c = some (Sum.inl a') := by
        have h := hed c
        rwa [ite_eq_left rfl] at h
      have hks_u_a : KingBottom u a := ⟨c, hse_u, hkng, hhidA⟩
      have hpa' : u'.piles a' = ⟨[], fromCard c (u.piles a).faceUp⟩ := by
        rw [hs1shape, putRun_eq_inl, setPile_piles_self]
      have hks_v_a' : KingBottom u' a' :=
        ⟨c, hse_v, hkng, by rw [hpa']⟩
      have hva : (u'.piles a).isEmpty = true := by
        rw [hs1shape, putRun_eq_inl, setPile_piles_ne haa',
          setPile_piles_self, hb0, Pile.afterRunRemoved_bare hhidA]
        rfl
      have hfix : ∀ j', j' ≠ a → j' ≠ a' → u'.piles j' = u.piles j' := by
        intro j' hja hja'
        rw [hs1shape, putRun_eq_inl, setPile_piles_ne hja',
          setPile_piles_ne hja]
      have hseat_other : ∀ x, x ≠ c → seatOf u' x = seatOf u x := by
        intro x hx
        rw [hed x, ite_eq_right hx]
      have hks_other : ∀ j', j' ≠ a → j' ≠ a' →
          (KingBottom u j' ↔ KingBottom u' j') := by
        intro j' hja hja'
        constructor
        · rintro ⟨x, hse, hk, hhd⟩
          have hxc : x ≠ c := by
            rintro rfl
            rw [hse_u] at hse
            exact hja (Sum.inl.inj (Option.some.inj hse)).symm
          refine ⟨x, ?_, hk, ?_⟩
          · rw [hseat_other x hxc]; exact hse
          · rw [hfix j' hja hja']; exact hhd
        · rintro ⟨x, hse, hk, hhd⟩
          have hxc : x ≠ c := by
            rintro rfl
            rw [hse_v] at hse
            exact hja' (Sum.inl.inj (Option.some.inj hse)).symm
          refine ⟨x, ?_, hk, ?_⟩
          · rw [← hseat_other x hxc]; exact hse
          · rw [hfix j' hja hja'] at hhd; exact hhd
      by_cases hja : j = a
      · subst j
        exact ⟨fun _ => Or.inl hva, fun _ => Or.inr hks_u_a⟩
      · by_cases hja' : j = a'
        · subst j
          exact ⟨fun _ => Or.inr hks_v_a', fun _ => Or.inl hiso⟩
        · constructor
          · rintro (h | h)
            · have hv : (u'.piles j).isEmpty = true := by
                rw [hfix j hja hja']; exact h
              exact Or.inl hv
            · exact Or.inr ((hks_other j hja hja').mp h)
          · rintro (h | h)
            · have hv : (u.piles j).isEmpty = true := by
                rw [← hfix j hja hja']; exact h
              exact Or.inl hv
            · exact Or.inr ((hks_other j hja hja').mpr h)

/-- Chain grade: the fuel set is pointwise fixed along one cargo direction. -/
private theorem orbit_vk_chain : ∀ {x y : State},
    Steps CargoLeg x y → x.WF → ∀ j, VKSet x j ↔ VKSet y j := by
  intro x y h
  induction h with
  | refl s => intro _ j; exact Iff.rfl
  | @cons x1 x2 x3 hleg _ ih =>
      intro hwf0 j
      obtain ⟨m, b, hstep, hrev⟩ := id hleg
      exact (orbit_vk_step hwf0 hstep hrev j).trans
        (ih (tfc_tabToTab_wf hwf0 hstep) j)

/-- **bareCargo_orbit_vk** — THE FUEL SET IS FIXED: at both ends of a
bare-cargo class pair the anchors are vacant or king-bottomed at exactly the
same nodes.  So `{vacant} ⊎ {king-bottom}` is an orbit constant POINTWISE,
not merely up to cardinality — the set the king shuffle moves inside. -/
theorem bareCargo_orbit_vk {st w : State} (hwfst : st.WF)
    (hpair : BareCargoEquiv st w) : ∀ j, VKSet st j ↔ VKSet w j :=
  orbit_vk_chain hpair.1 hwfst

/-- **bareCargo_orbit_vk_transfer** — INSIDE THE SET, ONLY KINGS MOVE: a node
that stops being vacant is a king-bottom, and a node that stops being a
king-bottom is vacant.  (This is the per-node content of the king shuffle;
the Z/2Z company hop touches no node of the set at all.) -/
theorem bareCargo_orbit_vk_transfer {st w : State} (hwfst : st.WF)
    (hpair : BareCargoEquiv st w) (j : Anchor) :
    (VacantSpot st j ∧ ¬ VacantSpot w j → KingBottom w j) ∧
    (KingBottom st j ∧ ¬ KingBottom w j → VacantSpot w j) := by
  have h := bareCargo_orbit_vk hwfst hpair j
  constructor
  · rintro ⟨h1, h2⟩
    rcases h.mp (Or.inl h1) with h3 | h3
    · exact absurd h3 h2
    · exact h3
  · rintro ⟨h1, h2⟩
    rcases h.mp (Or.inr h1) with h3 | h3
    · exact h3
    · exact absurd h3 h2

/-! ### §M10. THE KING-SHUFFLE CARD — "if the state has a vacant
spot, you can shuffle the kings all you want": a bottomed bare king
swaps into the vacancy reversibly, THE VACANCY TRAVELS to the king's
old pile (the chain's fuel — every hop re-creates the next
vacancy), and the whole crate stays bare-cargo-equivalent to the
start.  The leg closes via the chart activation row directly: the
lift's own SeatEdit IS the carried-arm chart, the readouts are the
SeatEdit's fixed components, and the licensing is the shuffle's own
hypotheses (the mover's bare cell — the spec's king-arm shape —
with the vacancy as the spec's empty-pile existential). -/

/-- **king_shuffle_vacancy** — THE SHUFFLE LEG: a bottomed bare
king and a vacant spot exchange reversibly; the vacancy lands on the
king's old pile, and the successor is a genuine bare-cargo
class-mate of the origin. -/
theorem king_shuffle_vacancy {u : State} {c : Card} {a e : Anchor}
    (hwf : u.WF)
    (hroundtrip : ∀ A B, chartAgree A B → A = B)
    (hseat : seatOf u c = some (Sum.inl a))
    (hking : c.rank = Rank.king)
    (hhid : (u.piles a).hidden = [])
    (hvac : (u.piles e).isEmpty = true) :
    ∃ v, State.step u (Move.tabToTab c (Sum.inl e)) = some v ∧
      BareCargoEquiv u v ∧ (v.piles a).isEmpty = true := by
  -- the license and the cell are the hypotheses verbatim
  have hcell : FloaterCell u c :=
    Or.inr ⟨a, hseat, hking, hhid⟩
  have hmove : u.canPlace c (Sum.inl e) = true :=
    tfa_canPlace_inl hvac hking
  obtain ⟨v, hstep, hrev, ⟨hed, hbf, hff, hdp, hco⟩⟩ :=
    floater_cargo_lift hwf hmove hcell
  have hwv : v.WF := tfc_tabToTab_wf hwf hstep
  -- the successor's chart, from the lift's own point edit
  have hseatv : seatOf v c = some (Sum.inl e) := by
    have h0 := hed c
    rwa [ite_eq_left rfl] at h0
  have hcar : ∀ x, x ≠ c → seatOf v x = seatOf u x := by
    intro x hxc
    have h0 := hed x
    rwa [ite_eq_right (fun h => hxc h)] at h0
  -- the net relation is the shuffle verbatim; the licensing is
  -- the hypotheses verbatim (only the mover changed)
  have hrel : ∀ x, (seatOf v x = seatOf u x) ∨
      (∃ z', seatOf u x = some (Sum.inr z') ∧
        seatOf v x = some (Sum.inr z'.twin)) ∨
      (x.rank = Rank.king ∧ ∃ a' a'', seatOf u x = some (Sum.inl a') ∧
        seatOf v x = some (Sum.inl a'') ∧
        (u.piles a'').isEmpty = true) := by
    intro x
    by_cases hxc : x = c
    · rw [hxc]
      exact Or.inr (Or.inr ⟨hking, a, e, hseat, hseatv, hvac⟩)
    · exact Or.inl (hcar x hxc)
  have hlic : ∀ x, seatOf u x ≠ seatOf v x → FloaterSpec u x := by
    intro x hchg
    by_cases hxc : x = c
    · rw [hxc]
      exact Or.inr ⟨a, hseat, hking, hhid, e, hvac⟩
    · exfalso
      exact hchg (hcar x hxc).symm
  refine ⟨v, hstep, ?_, ?_⟩
  · exact bareCargo_of_seatchart hwf hwv hroundtrip hrel hlic
      ⟨hbf, hff, hdp, hco⟩
  · -- the vacancy travels: the donor pile is vacated whole
    obtain ⟨hhold, hbE⟩ := tfc_seatOf_of_inl hseat
    obtain ⟨a0, hhold0, -, -, hs1shape⟩ := step_tabToTab_inv hstep
    have ha0 : a0 = a := Option.some.inj (hhold0.symm.trans hhold)
    rw [ha0] at hs1shape
    obtain ⟨tr, hcrr⟩ := tfc_fromCard_cons_head _ (pileHolding_mem hhold)
    rw [hcrr] at hs1shape
    have haa' : a ≠ e := by
      intro heq
      obtain ⟨-, hface_e⟩ := (Pile.isEmpty_eq _).mp hvac
      have hmem : c ∈ (u.piles a).faceUp := pileHolding_mem hhold
      rw [heq] at hmem
      rw [hface_e] at hmem
      exact absurd hmem (by simp)
    rw [hs1shape, putRun_eq_inl, setPile_piles_ne haa', setPile_piles_self,
      hbE, Pile.afterRunRemoved_bare hhid]
    rfl

/-- **KingShuffle u w** — the shuffle reachability: w is reached
from u by any sequence of bare-king trades, each INTO the state's
current vacancy (the prior hop's donor pile or the original). -/
inductive KingShuffle : State → State → Prop
  | refl (u : State) : KingShuffle u u
  | hop {u v w : State} (c : Card) (a e : Anchor)
      (hseat : seatOf u c = some (Sum.inl a))
      (hking : c.rank = Rank.king)
      (hhid : (u.piles a).hidden = [])
      (hvac : (u.piles e).isEmpty = true)
      (hfired : State.step u (Move.tabToTab c (Sum.inl e)) = some v)
      (hrest : KingShuffle v w) : KingShuffle u w

/-- **king_shuffle_closure** — SHUFFLING THE KINGS ALL YOU WANT:
every state reached from u by any sequence of vacancy-swapping
bare-king trades is a bare-cargo class-mate of u (the closure
carries the fence and the priced round trip along the chain — each
hop's WF and chart facts are the leg row's own outputs). -/
theorem king_shuffle_closure {u w : State} (hwf : u.WF)
    (hroundtrip : ∀ A B, chartAgree A B → A = B)
    (h : KingShuffle u w) :
    BareCargoEquiv u w := by
  have aux : ∀ {u' w' : State}, KingShuffle u' w' →
      u'.WF → BareCargoEquiv u' w' := by
    intro u' w' h'
    induction h' with
    | refl s =>
        intro _
        exact ⟨Steps.refl s, Steps.refl s⟩
    | @hop u1 u2 w0 c a e hseat hking hhid hvac hfired hrest ih =>
        intro hwf1
        obtain ⟨v', hfired', hcls, -⟩ :=
          king_shuffle_vacancy hwf1 hroundtrip hseat hking hhid hvac
        have hu2 : u2 = v' :=
          Option.some.inj (hfired.symm.trans hfired')
        subst hu2
        exact orbit_bareCargo_trans hcls
          (ih (tfc_tabToTab_wf hwf1 hfired))
  exact aux h hwf

/-- **king_shuffle_trivial_of_no_vacancy** — NO VACANCY, NO SHUFFLE: with no
empty pile at the start, the only vacancy-swapping shuffle is the empty one.
(The "disabled" side of the king card: the shuffle needs a spot to park
through.) -/
theorem king_shuffle_trivial_of_no_vacancy :
    ∀ {u w : State}, KingShuffle u w → ¬ HasVacancy u → u = w := by
  intro u w h
  induction h with
  | refl s => intro _; rfl
  | @hop u1 u2 w0 c a e hseat hking hhid hvac hfired hrest ih =>
      intro hno
      exact absurd ⟨e, hvac⟩ hno

/-! #### §M11a. KING POSITIONS ARE FREE ON VK — one bottomed king, one hop
(or two, parking an occupant), onto any node of the fuel set. -/

/-- **king_hop_step** — one bare-king hop, fully unpacked: the mover lands on the vacancy, its
donor becomes vacant, all other seats and all untouched piles are carried, the
fuel set is pointwise fixed, and every OTHER bottomed king stays one (at a
possibly new anchor). -/
private theorem king_hop_step {u : State} (hwf : u.WF) {c : Card} {a e : Anchor}
    (hse : seatOf u c = some (Sum.inl a)) (hkb : KingBottom u a)
    (hvac : VacantSpot u e) :
    ∃ v, KingShuffle u v ∧ seatOf v c = some (Sum.inl e) ∧ KingBottom v e ∧
      VacantSpot v a ∧
      (∀ x, x ≠ c → seatOf v x = seatOf u x) ∧
      (∀ j, j ≠ a → j ≠ e → v.piles j = u.piles j) ∧ v.WF ∧
      (∀ j, VKSet u j ↔ VKSet v j) ∧
      (∀ x, x ≠ c → (∃ a', KingBottom u a' ∧ seatOf u x = some (Sum.inl a')) →
        ∃ a', KingBottom v a' ∧ seatOf v x = some (Sum.inl a')) ∧
      State.step u (Move.tabToTab c (Sum.inl e)) = some v ∧
      CargoLeg u v ∧
      (∀ j, (u.piles j).hidden = (v.piles j).hidden) := by
  obtain ⟨c0, hse0, hkng, hhid⟩ := hkb
  have hc0 : c0 = c := orbit_bottom_unique hse0 hse
  subst c0
  have hhold : u.pileHolding c = some a := (tfc_seatOf_of_inl hse).1
  have hae : a ≠ e := by
    intro heq
    have hmem : c ∈ (u.piles a).faceUp := pileHolding_mem hhold
    rw [heq, ((Pile.isEmpty_eq _).mp hvac).2] at hmem
    exact absurd hmem (by simp)
  have hcell : FloaterCell u c := Or.inr ⟨a, hse, hkng, hhid⟩
  have hmove : u.canPlace c (Sum.inl e) = true := tfa_canPlace_inl hvac hkng
  obtain ⟨v, hstep, hrev, hed, hbf, hff, hdp, hco⟩ :=
    floater_cargo_lift hwf hmove hcell
  have hwv : v.WF := tfc_tabToTab_wf hwf hstep
  have hse_v : seatOf v c = some (Sum.inl e) := by
    have h := hed c
    rwa [ite_eq_left rfl] at h
  have hseat_other : ∀ x, x ≠ c → seatOf v x = seatOf u x := by
    intro x hx
    have h := hed x
    rwa [ite_eq_right hx] at h
  obtain ⟨-, hbE⟩ := tfc_seatOf_of_inl hse
  obtain ⟨hcp0, hfr, hs1shape⟩ := fli_step_shape hstep hhold
  have hva : (v.piles a).isEmpty = true := by
    rw [hs1shape, putRun_eq_inl, setPile_piles_ne hae, setPile_piles_self,
      hbE, Pile.afterRunRemoved_bare hhid]
    rfl
  have hpa : v.piles e = ⟨[], fromCard c (u.piles a).faceUp⟩ := by
    rw [hs1shape, putRun_eq_inl, setPile_piles_self]
  have hkb_v : KingBottom v e := ⟨c, hse_v, hkng, by rw [hpa]⟩
  have hpile_other : ∀ j, j ≠ a → j ≠ e → v.piles j = u.piles j := by
    intro j hja hje
    rw [hs1shape, putRun_eq_inl, setPile_piles_ne hje, setPile_piles_ne hja]
  have hvk : ∀ j, VKSet u j ↔ VKSet v j := orbit_vk_step hwf hstep hrev
  have hkeeps : ∀ x, x ≠ c →
      (∃ a', KingBottom u a' ∧ seatOf u x = some (Sum.inl a')) →
      ∃ a', KingBottom v a' ∧ seatOf v x = some (Sum.inl a') := by
    intro x hx hkbx
    obtain ⟨ax, hkbx', hse_x⟩ := hkbx
    obtain ⟨xk, hse_xk, hkng_x, hhid_x⟩ := hkbx'
    have hxx : xk = x := orbit_bottom_unique hse_xk hse_x
    rw [hxx] at hkng_x
    have hax_a : ax ≠ a := by
      intro h
      exact hx (orbit_bottom_unique (h ▸ hse_x) hse)
    have hax_e : ax ≠ e := by
      intro h
      have hmem : x ∈ (u.piles ax).faceUp :=
        pileHolding_mem (tfc_seatOf_of_inl hse_x).1
      rw [h, ((Pile.isEmpty_eq _).mp hvac).2] at hmem
      exact absurd hmem (by simp)
    have hseat_v : seatOf v x = some (Sum.inl ax) := by
      rw [hseat_other x hx]; exact hse_x
    exact ⟨ax, ⟨x, hseat_v, hkng_x, by rw [hpile_other ax hax_a hax_e]; exact hhid_x⟩,
      hseat_v⟩
  exact ⟨v, KingShuffle.hop c a e hse hkng hhid hvac hstep (KingShuffle.refl v),
    hse_v, hkb_v, hva, hseat_other, hpile_other, hwv, hvk, hkeeps,
    hstep, ⟨c, Sum.inl e, hstep, hrev⟩,
    (tfa_slide_conserves hwf hstep hrev).1.1⟩

/-- KingShuffle composes. -/
private theorem king_shuffle_append {a b c : State} (h1 : KingShuffle a b)
    (h2 : KingShuffle b c) : KingShuffle a c := by
  induction h1 with
  | refl _ => exact h2
  | hop c a e hseat hking hhid hvac hfired hrest ih =>
      exact KingShuffle.hop c a e hseat hking hhid hvac hfired (ih h2)

/-- **king_reaches_vk** — with a vacancy, a bottomed king can be put on ANY
node of the fuel set VK; and the move keeps the cage: the state stays WF and
vacant, the fuel set is pointwise fixed, and every OTHER bottomed king is
still a bottomed king (at a possibly new anchor). -/
theorem king_reaches_vk {u : State} (hwf : u.WF) (hvac : HasVacancy u)
    {c : Card} {a : Anchor} (hse : seatOf u c = some (Sum.inl a))
    (hkb : KingBottom u a) {e : Anchor} (hsrc : VKSet u e) :
    ∃ w, KingShuffle u w ∧ seatOf w c = some (Sum.inl e) ∧ KingBottom w e ∧
      w.WF ∧ HasVacancy w ∧ (∀ j, VKSet u j ↔ VKSet w j) ∧
      (∀ x, x ≠ c → (∃ a', KingBottom u a' ∧ seatOf u x = some (Sum.inl a')) →
        ∃ a', KingBottom w a' ∧ seatOf w x = some (Sum.inl a')) := by
  have hkb' := hkb
  obtain ⟨ck, hse_k, hkng_c, hhid_a⟩ := hkb'
  have hck : ck = c := orbit_bottom_unique hse_k hse
  rw [hck] at hkng_c
  by_cases hea : e = a
  · subst hea
    exact ⟨u, KingShuffle.refl u, hse, hkb, hwf, hvac, fun _ => Iff.rfl,
      fun x _ h => h⟩
  · have hae : a ≠ e := fun h => hea h.symm
    rcases hsrc with hv | hkb_e
    · obtain ⟨v, hks, hsv, hkbv, hva, -, -, hwv, hvk, hkeeps, -, -, -⟩ :=
        king_hop_step hwf hse hkb hv
      exact ⟨v, hks, hsv, hkbv, hwv, ⟨a, hva⟩, hvk, hkeeps⟩
    · obtain ⟨d, hse_d, hkng_d, hhid_d⟩ := hkb_e
      have hhold_d : u.pileHolding d = some e := (tfc_seatOf_of_inl hse_d).1
      have hhold_c : u.pileHolding c = some a := (tfc_seatOf_of_inl hse).1
      have hdc : d ≠ c := by
        intro hEq
        subst hEq
        have hcruz : some (Sum.inl e) = some (Sum.inl a) := hse_d.symm.trans hse
        exact hea (Sum.inl.inj (Option.some.inj hcruz))
      have hne_e : (u.piles e).isEmpty = false :=
        Pile.isEmpty_eq_false_of_mem (pileHolding_mem hhold_d)
      have hne_a : (u.piles a).isEmpty = false :=
        Pile.isEmpty_eq_false_of_mem (pileHolding_mem hhold_c)
      obtain ⟨v0, hv0⟩ := hvac
      have hve : v0 ≠ e := by
        intro hEq
        rw [hEq, hne_e] at hv0
        exact Bool.noConfusion hv0
      have hav0 : a ≠ v0 := by
        intro hEq
        rw [← hEq, hne_a] at hv0
        exact Bool.noConfusion hv0
      obtain ⟨w1, hks1, hse_d1, hkb_d1, hvac_e, hseat_d_other, hpile_other, hw1,
        hvk1, hkeeps1, -, -, -⟩ :=
        king_hop_step hwf hse_d ⟨d, hse_d, hkng_d, hhid_d⟩ hv0
      have hse_w1 : seatOf w1 c = some (Sum.inl a) := by
        rw [hseat_d_other c (fun h => hdc h.symm)]; exact hse
      have hhid_w1 : (w1.piles a).hidden = [] := by
        rw [hpile_other a hae hav0]; exact hhid_a
      obtain ⟨w2, hks2, hse2, hkb2, hva2, -, -, hw2, hvk2, hkeeps2, -, -, -⟩ :=
        king_hop_step hw1 hse_w1 ⟨c, hse_w1, hkng_c, hhid_w1⟩ hvac_e
      refine ⟨w2, king_shuffle_append hks1 hks2, hse2, hkb2, hw2, ⟨a, hva2⟩,
        fun j => (hvk1 j).trans (hvk2 j), ?_⟩
      intro x hx hkbx
      have hkb1 : ∃ a', KingBottom w1 a' ∧ seatOf w1 x = some (Sum.inl a') := by
        by_cases hxd : x = d
        · subst hxd
          exact ⟨v0, hkb_d1, hse_d1⟩
        · exact hkeeps1 x hxd hkbx
      exact hkeeps2 x hx hkb1
/-! #### §M11b. ASSIGNMENT COMPLETENESS — the multi-king form of §M11a: with a
vacancy, EVERY injective placement of distinct bottomed kings on distinct nodes
of the fuel set is reachable.  The induction is the greedy cycle-fixer: take a
misplaced king, land it on its target (parking the occupant on any vacancy if
the target is held), and recurse — already-placed kings are never the mover
(nodup) nor the parked occupant (target injectivity), so the accumulator is
preserved.  `king_reaches_vk` is the one-king core. -/

/-- `done` is placed at `w` according to `τ`. -/
abbrev PlacedBy (τ : Card → Anchor) (done : List Card) (w : State) : Prop :=
  ∀ c ∈ done, seatOf w c = some (Sum.inl (τ c))

private theorem king_solve : ∀ (cs ds : List Card) (u : State),
    u.WF → HasVacancy u →
    (∀ c ∈ cs, ∃ a, KingBottom u a ∧ seatOf u c = some (Sum.inl a)) →
    (∀ c ∈ cs, VKSet u (τ c)) →
    PlacedBy τ ds u →
    cs.Nodup → ds.Nodup → (∀ c ∈ cs, c ∉ ds) →
    (∀ c ∈ cs, ∀ c' ∈ cs ++ ds, τ c = τ c' → c = c') →
    ∃ w, KingShuffle u w ∧ PlacedBy τ cs w ∧ PlacedBy τ ds w := by
  intro cs
  induction cs with
  | nil =>
      intro ds u hwf hvac hk ht hp hnd hnds hdisj hinj
      exact ⟨u, KingShuffle.refl u, (fun x hx => absurd hx (by simp)), hp⟩
  | cons c rest ih =>
      intro ds u hwf hvac hk ht hp hnd hnds hdisj hinj
      have hnd' : rest.Nodup := (List.nodup_cons.mp hnd).2
      have hc_rest : c ∉ rest := (List.nodup_cons.mp hnd).1
      have hfilled : c ∉ ds := hdisj c (by simp)
      have hdisj' : ∀ x ∈ rest, x ∉ c :: ds := by
        intro x hx hmem
        rw [List.mem_cons] at hmem
        rcases hmem with hxc | hxds
        · rw [hxc] at hx; exact hc_rest hx
        · exact hdisj x (List.mem_cons_of_mem c hx) hxds
      have hinj' : ∀ x ∈ rest, ∀ y ∈ rest ++ (c :: ds), τ x = τ y → x = y := by
        intro x hx y hy hxy
        have hx' : x ∈ c :: rest := List.mem_cons_of_mem c hx
        rcases List.mem_append.mp hy with hy | hy
        · exact hinj x hx' y (List.mem_append_left _ (List.mem_cons_of_mem c hy)) hxy
        · rcases List.mem_cons.mp hy with hyc | hyds
          · rw [hyc] at hxy ⊢
            exact hinj x hx' c (by simp) hxy
          · exact hinj x hx' y (List.mem_append_right _ hyds) hxy
      have hk' : ∀ x ∈ rest, ∃ a, KingBottom u a ∧ seatOf u x = some (Sum.inl a) :=
        fun x hx => hk x (List.mem_cons_of_mem c hx)
      have ht' : ∀ x ∈ rest, VKSet u (τ x) :=
        fun x hx => ht x (List.mem_cons_of_mem c hx)
      obtain ⟨a, hkb, hse⟩ := hk c (by simp)
      have hkb_c := hkb
      obtain ⟨ck, hse_k, hkng_c, hhid_c⟩ := hkb_c
      have hck : ck = c := orbit_bottom_unique hse_k hse
      rw [hck] at hkng_c
      have hsrc : VKSet u (τ c) := ht c (by simp)
      by_cases hfixed : seatOf u c = some (Sum.inl (τ c))
      · have hp' : PlacedBy τ (c :: ds) u := by
          intro x hx
          rcases List.mem_cons.mp hx with hxc | hx
          · rw [hxc]; exact hfixed
          · exact hp x hx
        obtain ⟨w, hks, hcs, hds⟩ :=
          ih (c :: ds) u hwf hvac hk' ht' hp' hnd'
            (List.nodup_cons.mpr ⟨hfilled, hnds⟩) hdisj' hinj'
        refine ⟨w, hks, ?_, fun x hx => hds x (List.mem_cons_of_mem c hx)⟩
        intro x hx
        rcases List.mem_cons.mp hx with hxc | hx
        · rw [hxc]; exact hds c (by simp)
        · exact hcs x hx
      · rcases hsrc with hv | hkb_e
        · obtain ⟨w1, hks1, hse_c1, hkb_c1, hva, hseat_other, hpile_other, hw1,
            hvk1, hkeeps1, -, -, -⟩ := king_hop_step hwf hse hkb hv
          have hp' : PlacedBy τ (c :: ds) w1 := by
            intro x hx
            rcases List.mem_cons.mp hx with hxc | hx
            · rw [hxc]; exact hse_c1
            · have hxc : x ≠ c := fun h => hfilled (h ▸ hx)
              rw [hseat_other x hxc]; exact hp x hx
          have hk1 : ∀ x ∈ rest, ∃ a', KingBottom w1 a' ∧ seatOf w1 x = some (Sum.inl a') := by
            intro x hx
            exact hkeeps1 x (fun h => hc_rest (h ▸ hx)) (hk' x hx)
          have ht1 : ∀ x ∈ rest, VKSet w1 (τ x) := by
            intro x hx
            exact (hvk1 (τ x)).mp (ht' x hx)
          obtain ⟨w2, hks2, hcs2, hds2⟩ :=
            ih (c :: ds) w1 hw1 ⟨a, hva⟩ hk1 ht1 hp' hnd'
              (List.nodup_cons.mpr ⟨hfilled, hnds⟩) hdisj' hinj'
          refine ⟨w2, king_shuffle_append hks1 hks2, ?_,
            fun x hx => hds2 x (List.mem_cons_of_mem c hx)⟩
          intro x hx
          rcases List.mem_cons.mp hx with hxc | hx
          · rw [hxc]; exact hds2 c (by simp)
          · exact hcs2 x hx
        · obtain ⟨d, hse_d, hkng_d, hhid_d⟩ := hkb_e
          have hhold_d : u.pileHolding d = some (τ c) := (tfc_seatOf_of_inl hse_d).1
          have hhold_c : u.pileHolding c = some a := (tfc_seatOf_of_inl hse).1
          have hdc : d ≠ c := by
            intro hEq
            rw [hEq] at hse_d
            exact hfixed hse_d
          have hne_e : (u.piles (τ c)).isEmpty = false :=
            Pile.isEmpty_eq_false_of_mem (pileHolding_mem hhold_d)
          have hne_a : (u.piles a).isEmpty = false :=
            Pile.isEmpty_eq_false_of_mem (pileHolding_mem hhold_c)
          obtain ⟨v0, hv0⟩ := hvac
          have hve : v0 ≠ τ c := by
            intro hEq
            rw [hEq, hne_e] at hv0
            exact Bool.noConfusion hv0
          have hav0 : a ≠ v0 := by
            intro hEq
            rw [← hEq, hne_a] at hv0
            exact Bool.noConfusion hv0
          obtain ⟨w1, hks1, hse_d1, hkb_d1, hvac_e, hseat_d_other, hpile_other, hw1,
            hvk1, hkeeps1, -, -, -⟩ :=
            king_hop_step hwf hse_d ⟨d, hse_d, hkng_d, hhid_d⟩ hv0
          have hse_w1 : seatOf w1 c = some (Sum.inl a) := by
            rw [hseat_d_other c (fun h => hdc h.symm)]; exact hse
          have hhid_w1 : (w1.piles a).hidden = [] := by
            rw [hpile_other a (fun h => hfixed (by rw [← h]; exact hse)) hav0]; exact hhid_c
          obtain ⟨w2, hks2, hse_c2, hkb_c2, hva2, hseat_c_other, hpile2, hw2,
            hvk2, hkeeps2, -, -, -⟩ :=
            king_hop_step hw1 hse_w1 ⟨c, hse_w1, hkng_c, hhid_w1⟩ hvac_e
          have hd_ds : d ∉ ds := by
            intro hdmem
            have hpd : seatOf u d = some (Sum.inl (τ d)) := hp d hdmem
            have hτ : τ d = τ c := by
              have h1 : some (Sum.inl (τ d)) = some (Sum.inl (τ c)) := hpd.symm.trans hse_d
              exact Sum.inl.inj (Option.some.inj h1)
            exact hdc (hinj c (by simp) d (List.mem_append_right _ hdmem) hτ.symm).symm
          have hp' : PlacedBy τ (c :: ds) w2 := by
            intro x hx
            rcases List.mem_cons.mp hx with hxc | hx
            · rw [hxc]; exact hse_c2
            · have hxc : x ≠ c := fun h => hfilled (h ▸ hx)
              have hxd : x ≠ d := fun h => hd_ds (h ▸ hx)
              rw [hseat_c_other x hxc, hseat_d_other x hxd]
              exact hp x hx
          have hk1 : ∀ x ∈ rest, ∃ a', KingBottom w1 a' ∧ seatOf w1 x = some (Sum.inl a') := by
            intro x hx
            by_cases hxd : x = d
            · rw [hxd]; exact ⟨v0, hkb_d1, hse_d1⟩
            · exact hkeeps1 x hxd (hk' x hx)
          have hk2 : ∀ x ∈ rest, ∃ a', KingBottom w2 a' ∧ seatOf w2 x = some (Sum.inl a') := by
            intro x hx
            exact hkeeps2 x (fun h => hc_rest (h ▸ hx)) (hk1 x hx)
          have ht2 : ∀ x ∈ rest, VKSet w2 (τ x) := by
            intro x hx
            exact ((hvk1 (τ x)).trans (hvk2 (τ x))).mp (ht' x hx)
          obtain ⟨w3, hks3, hcs3, hds3⟩ :=
            ih (c :: ds) w2 hw2 ⟨a, hva2⟩ hk2 ht2 hp' hnd'
              (List.nodup_cons.mpr ⟨hfilled, hnds⟩) hdisj' hinj'
          refine ⟨w3, king_shuffle_append hks1 (king_shuffle_append hks2 hks3), ?_,
            fun x hx => hds3 x (List.mem_cons_of_mem c hx)⟩
          intro x hx
          rcases List.mem_cons.mp hx with hxc | hx
          · rw [hxc]; exact hds3 c (by simp)
          · exact hcs3 x hx

/-- **king_assignment_reachable** — THE POSITIONS ARE FREE ON VK: with a
vacancy, any injective assignment `τ` of distinct bare kings to distinct nodes
of the fuel set is realized by a shuffle — every king ends on its assigned
node, and (since the king count and `VKSet` are orbit invariants) the leftover
nodes are exactly the vacancies. -/
theorem king_assignment_reachable {u : State} (hwf : u.WF) (hvac : HasVacancy u)
    (τ : Card → Anchor) (cs : List Card)
    (hk : ∀ c ∈ cs, ∃ a, KingBottom u a ∧ seatOf u c = some (Sum.inl a))
    (ht : ∀ c ∈ cs, VKSet u (τ c))
    (hnd : cs.Nodup)
    (hinj : ∀ c ∈ cs, ∀ c' ∈ cs, τ c = τ c' → c = c') :
    ∃ w, KingShuffle u w ∧ ∀ c ∈ cs, seatOf w c = some (Sum.inl (τ c)) := by
  obtain ⟨w, hks, hcs, -⟩ :=
    king_solve cs [] u hwf hvac hk ht (fun c hc => absurd hc (by simp)) hnd
      (by simp) (fun c hc => by simp)
      (fun c hc c' hc' h => hinj c hc c' (by simpa using hc') h)
  exact ⟨w, hks, hcs⟩
/-! #### §M11c. THE STRONG KING HALF AND THE PRODUCT SOUNDNESS — a king is
never seated on a card at WF; the strong king half (targets FULLY empty at the
origin) is a reachable assignment; and a KingShuffle composed with any
class-mate journey stays in the class. -/

/-- A king is never seated on a card at WF (the fit arithmetic). -/
private theorem king_seat_inr_absurd {st : State} (hwf : st.WF) {c : Card} {z : Card}
    (hk : c.rank = Rank.king) (hse : seatOf st c = some (Sum.inr z)) : False := by
  obtain ⟨a, hhold, hbne, hlast⟩ := tfc_seatOf_of_inr hse
  obtain ⟨hsit, -⟩ := tfc_seat_parent hwf hhold hlast
  obtain ⟨hidx, -⟩ := (canSitOn_eq c z).mp hsit
  have hzlt := Rank.toIdx_lt z.rank
  have h12 : c.rank.toIdx = 12 := by rw [hk]; rfl
  omega


/-- **king_half_shuffle** — THE KING HALF IS A SHUFFLE: if the kings of `st`
sit at the assignment `τ` in `w` and each target is the origin's seat or a spot
empty at `st`, then some KingShuffle realizes that assignment. -/
theorem king_half_shuffle {st w : State} (hwf : st.WF) (hvac : HasVacancy st)
    (cs : List Card) (τ : Card → Anchor)
    (hk : ∀ c ∈ cs, ∃ a, KingBottom st a ∧ seatOf st c = some (Sum.inl a))
    (hnd : cs.Nodup)
    (hinj : ∀ c ∈ cs, ∀ c' ∈ cs, τ c = τ c' → c = c')
    (hagree : ∀ c ∈ cs, seatOf w c = some (Sum.inl (τ c)))
    (hhalf : ∀ c ∈ cs, seatOf w c = seatOf st c ∨
      ∃ a a', seatOf st c = some (Sum.inl a) ∧
        seatOf w c = some (Sum.inl a') ∧ (st.piles a').isEmpty = true) :
    ∃ u, KingShuffle st u ∧ ∀ c ∈ cs, seatOf u c = some (Sum.inl (τ c)) := by
  refine king_assignment_reachable hwf hvac τ cs hk ?_ hnd hinj
  intro c hc
  rcases hhalf c hc with hsame | ⟨a, a', hse_st, hse_w, hemp⟩
  · obtain ⟨a0, hkb, hse0⟩ := hk c hc
    have h1 : some (Sum.inl a0) = some (Sum.inl (τ c)) :=
      hse0.symm.trans (hsame.symm.trans (hagree c hc))
    have hτ : τ c = a0 := (Sum.inl.inj (Option.some.inj h1)).symm
    rw [hτ]; exact Or.inr hkb
  · have h2 : some (Sum.inl (τ c)) = some (Sum.inl a') :=
      (hagree c hc).symm.trans hse_w
    have hτ : τ c = a' := Sum.inl.inj (Option.some.inj h2)
    rw [hτ]; exact Or.inl hemp

/-- **bareCargo_king_then** — the product is SOUND: a KingShuffle followed by
any class-mate journey is itself a class-mate (the king component composes with
the rest of the orbit by transitivity). -/
theorem bareCargo_king_then {st u w : State} (hwf : st.WF)
    (hroundtrip : ∀ A B, chartAgree A B → A = B)
    (hks : KingShuffle st u) (hpair : BareCargoEquiv u w) :
    BareCargoEquiv st w :=
  orbit_bareCargo_trans (king_shuffle_closure hwf hroundtrip hks) hpair
/-! #### §M11d. THE UN-MEDIATED KING ARM: `VKSet` instead of emptiness.  The
target of a changed king is in the fuel set at the ORIGIN — free from the
orbit invariant, because the king sits on that target at `w`, hence it is a
king-bottom there, hence in `VKSet w`, hence (pointwise invariance) in
`VKSet st`.  So the `→` side no longer needs `hnomed`, and the king-seat map
into `VKSet` is automatically INJECTIVE (two cards never bottom one pile).
The matching `←` (the schedule: `FloaterSpec`'s king cell carries a vacancy, so
licensing already supplies the fuel; `king_assignment_reachable` fires the
kings first and the residual chart is reconstructed) is §M11f. -/

/-- The king-seat map is automatically injective (two cards cannot bottom the
same pile). -/
theorem king_seat_injective {s : State} {c c' : Card} {a' : Anchor}
    (h1 : seatOf s c = some (Sum.inl a'))
    (h2 : seatOf s c' = some (Sum.inl a')) : c = c' :=
  orbit_bottom_unique h1 h2

/-- **bareCargo_to_chartDiff_vk** — the `→` direction with the UN-MEDIATED
king arm: a changed king's target is vacant-or-king-bottom at the origin (not
necessarily empty).  No `hnomed`. -/
theorem bareCargo_to_chartDiff_vk {st w : State} (hwfst : st.WF)
    (hpair : BareCargoEquiv st w) :
    (∀ x, (seatOf w x = seatOf st x) ∨
        (∃ z', seatOf st x = some (Sum.inr z') ∧
          seatOf w x = some (Sum.inr z'.twin)) ∨
        (x.rank = Rank.king ∧ ∃ a a', seatOf st x = some (Sum.inl a) ∧
          seatOf w x = some (Sum.inl a') ∧ VKSet st a')) ∧
      (boardFixed st w ∧ foundsFixed st w ∧
        drawPool st = drawPool w ∧ cutOf st = cutOf w) ∧
      (∀ x, seatOf st x ≠ seatOf w x → FloaterSpec st x) := by
  obtain ⟨hrel, hro, hlic⟩ := bareCargo_to_chartDiff_full hwfst hpair
  have hstep : ∀ (x : Card) (hk : x.rank = Rank.king),
      seatOf st x ≠ seatOf w x →
      (∃ a a', seatOf st x = some (Sum.inl a) ∧
        seatOf w x = some (Sum.inl a')) →
      ∃ a a', seatOf st x = some (Sum.inl a) ∧
        seatOf w x = some (Sum.inl a') ∧ VKSet st a' := by
    intro x hk hchg h
    obtain ⟨a, a', hse, hse_w⟩ := h
    have hhid : (st.piles a').hidden = [] := hlic.2 x a a' ⟨hse, hse_w, hchg⟩
    have hhid_w : (w.piles a').hidden = [] := by
      rw [← hro.1.1 a']; exact hhid
    exact ⟨a, a', hse, hse_w,
      (bareCargo_orbit_vk hwfst hpair a').mpr (Or.inr ⟨x, hse_w, hk, hhid_w⟩)⟩
  refine ⟨?_, hro, hlic.1⟩
  intro x
  by_cases hsame : seatOf w x = seatOf st x
  · exact Or.inl hsame
  · rcases hrel x with h1 | h2 | h3
    · exact absurd h1 hsame
    · exact Or.inr (Or.inl h2)
    · exact Or.inr (Or.inr ⟨h3.1, hstep x h3.1 (fun heq => hsame heq.symm) h3.2⟩)
/-! #### §M11e. THE KING ENUMERATION — a computable list of bottomed kings,
so the assignment theorem (§M11b) can be applied without a `Fintype`
instance. -/

/-- Bool form: `c` bottoms a bare king pile at `st`. -/
private def kingCardB (st : State) (c : Card) : Bool :=
  decide (c.rank = Rank.king) &&
    (match seatOf st c with
     | some (Sum.inl a) => decide ((st.piles a).hidden = [])
     | _ => false)

/-- The bottomed kings of `st`, as a computable list. -/
private def kingsOf (st : State) : List Card :=
  Card.universe.filter (kingCardB st)

/-- The enumeration is exact. -/
private theorem mem_kingsOf {st : State} (_hwf : st.WF) {c : Card} :
    c ∈ kingsOf st ↔ ∃ a, KingBottom st a ∧ seatOf st c = some (Sum.inl a) := by
  unfold kingsOf
  rw [List.mem_filter]
  constructor
  · rintro ⟨-, hb⟩
    unfold kingCardB at hb
    rw [Bool.and_eq_true] at hb
    obtain ⟨hr, hs⟩ := hb
    have hr' : c.rank = Rank.king := of_decide_eq_true hr
    cases hse : seatOf st c with
    | none => rw [hse] at hs; exact absurd hs (by simp)
    | some b =>
        cases b with
        | inr z => rw [hse] at hs; exact absurd hs (by simp)
        | inl a =>
            rw [hse] at hs
            exact ⟨a, ⟨⟨c, hse, hr', of_decide_eq_true hs⟩, rfl⟩⟩
  · rintro ⟨a, hkb, hse⟩
    refine ⟨Card.mem_universe c, ?_⟩
    obtain ⟨c0, hse0, hk0, hhid0⟩ := hkb
    have hc0 : c = c0 := king_seat_injective hse hse0
    rw [hc0]
    unfold kingCardB
    rw [hse0]
    rw [Bool.and_eq_true]
    exact ⟨decide_eq_true hk0, decide_eq_true hhid0⟩

private theorem universe_nodup : Card.universe.Nodup := by decide

private theorem kingsOf_nodup (st : State) : (kingsOf st).Nodup :=
  universe_nodup.filter (kingCardB st)
/-! #### §M11f. THE UN-MEDIATED IFF — the `←` assembly.  With a vacancy the
schedule exists (§M11b); the shuffle fixes every non-bottomed card's seat, the
fuel set, the readouts and the licensing; the residual chart (identity on the
kings, twin half on the rest) is reconstructed by the existing machinery. -/

/-- KingShuffle preserves WF. -/
private theorem king_shuffle_wf {u v : State} (h : KingShuffle u v) (hwf : u.WF) : v.WF := by
  induction h with
  | refl _ => exact hwf
  | @hop u1 u2 u3 c a e hseat hking hhid hvac hfired hrest ih =>
      exact ih (tfc_tabToTab_wf hwf hfired)

/-- Per hop, the SET of bottomed-king cards is invariant. -/
private theorem king_hop_kingcards {u v : State} (hwf : u.WF) {c : Card} {a e : Anchor}
    (hseat : seatOf u c = some (Sum.inl a)) (hkb : KingBottom u a)
    (hvac : VacantSpot u e)
    (hstep : State.step u (Move.tabToTab c (Sum.inl e)) = some v) :
    ∀ x, (∃ a', KingBottom u a' ∧ seatOf u x = some (Sum.inl a')) ↔
         (∃ a', KingBottom v a' ∧ seatOf v x = some (Sum.inl a')) := by
  obtain ⟨v', hks, hse_v, hkb_v, hva, hseat_other, hpile_other, hwv, hvk, hkeeps,
    hstep', -, hhidden⟩ := king_hop_step hwf hseat hkb hvac
  have hvv : v' = v := Option.some.inj (hstep'.symm.trans hstep)
  subst v'
  intro x
  by_cases hxc : x = c
  · subst x
    exact ⟨fun _ => ⟨e, hkb_v, hse_v⟩, fun _ => ⟨a, hkb, hseat⟩⟩
  · constructor
    · exact hkeeps x hxc
    · intro h
      obtain ⟨a', hkb', hse'⟩ := h
      obtain ⟨c0, hse0, hk0, hhid0⟩ := hkb'
      have hc0 : c0 = x := king_seat_injective hse0 hse'
      rw [hc0] at hk0
      have hse_u : seatOf u x = some (Sum.inl a') := by
        rw [← hseat_other x hxc]; exact hse'
      have hhid_u : (u.piles a').hidden = [] := by
        rw [hhidden a']; exact hhid0
      exact ⟨a', ⟨x, hse_u, hk0, hhid_u⟩, hse_u⟩


/-- Cards that do not bottom a king at the source keep their seat. -/
private theorem king_shuffle_seat_of_not_bottomed : ∀ {u v : State},
    KingShuffle u v → u.WF →
    ∀ x, (¬ ∃ a', KingBottom u a' ∧ seatOf u x = some (Sum.inl a')) →
      seatOf v x = seatOf u x := by
  intro u v h
  induction h with
  | refl s => intro _ x _; rfl
  | @hop u1 u2 u3 c a e hseat hking hhid hvac hfired hrest ih =>
      intro hwf1 x hx
      obtain ⟨v', hks, hse_v, hkb_v, hva, hseat_other, hpile_other, hwv, hvk, hkeeps,
        hstep', -, -⟩ := king_hop_step hwf1 hseat ⟨c, hseat, hking, hhid⟩ hvac
      have hvu2 : v' = u2 := Option.some.inj (hstep'.symm.trans hfired)
      subst v'
      have hxc : x ≠ c := by
        intro hxc
        exact hx ⟨a, ⟨c, hseat, hking, hhid⟩, by rw [hxc]; exact hseat⟩
      have hs2 : seatOf u2 x = seatOf u1 x := hseat_other x hxc
      have hx2 : ¬ ∃ a', KingBottom u2 a' ∧ seatOf u2 x = some (Sum.inl a') := by
        intro h
        exact hx ((king_hop_kingcards hwf1 hseat ⟨c, hseat, hking, hhid⟩ hvac hfired x).mpr h)
      rw [ih (tfc_tabToTab_wf hwf1 hfired) x hx2]
      exact hs2

/-- Per hop, the readouts are conserved. -/
private theorem king_hop_readouts {u v : State} (hwf : u.WF) {c : Card} {a e : Anchor}
    (hseat : seatOf u c = some (Sum.inl a)) (hking : c.rank = Rank.king)
    (hhid : (u.piles a).hidden = []) (hvac : VacantSpot u e)
    (hfired : State.step u (Move.tabToTab c (Sum.inl e)) = some v) :
    boardFixed u v ∧ foundsFixed u v ∧ drawPool u = drawPool v ∧ cutOf u = cutOf v := by
  have hmove : u.canPlace c (Sum.inl e) = true := tfa_canPlace_inl hvac hking
  have hcell : FloaterCell u c := Or.inr ⟨a, hseat, hking, hhid⟩
  obtain ⟨v', hstep, hrev, -, hbf, hff, hdp, hco⟩ := floater_cargo_lift hwf hmove hcell
  have hvv : v' = v := Option.some.inj (hstep.symm.trans hfired)
  subst v'
  exact ⟨hbf, hff, hdp, hco⟩

/-- Chain: the readouts are conserved along a shuffle. -/
private theorem king_shuffle_readouts : ∀ {u v : State}, KingShuffle u v → u.WF →
    boardFixed u v ∧ foundsFixed u v ∧ drawPool u = drawPool v ∧ cutOf u = cutOf v := by
  intro u v h
  induction h with
  | refl s => intro _; exact ⟨⟨fun _ => rfl, rfl⟩, fun _ => rfl, rfl, rfl⟩
  | @hop u1 u2 u3 c a e hseat hking hhid hvac hfired hrest ih =>
      intro hwf1
      obtain ⟨hb1, hf1, hd1, hc1⟩ :=
        king_hop_readouts hwf1 hseat hking hhid hvac hfired
      obtain ⟨hb2, hf2, hd2, hc2⟩ := ih (tfc_tabToTab_wf hwf1 hfired)
      exact ⟨⟨fun j => (hb1.1 j).trans (hb2.1 j), hb1.2.trans hb2.2⟩,
        fun j => (hf1 j).trans (hf2 j), hd1.trans hd2, hc1.trans hc2⟩

/-- Chain: FloaterSpec is invariant along a shuffle. -/
private theorem king_shuffle_floaterSpec : ∀ {u v : State}, KingShuffle u v → u.WF →
    ∀ c, FloaterSpec u c ↔ FloaterSpec v c := by
  intro u v h
  induction h with
  | refl s => intro _ c; exact Iff.rfl
  | @hop u1 u2 u3 c a e hseat hking hhid hvac hfired hrest ih =>
      intro hwf1 x
      obtain ⟨v', hks, hse_v, hkb_v, hva, hseat_other, hpile_other, hwv, hvk, hkeeps,
        hstep', hleg, -⟩ := king_hop_step hwf1 hseat ⟨c, hseat, hking, hhid⟩ hvac
      have hvu2 : v' = u2 := Option.some.inj (hstep'.symm.trans hfired)
      subst v'
      have hwf2 : u2.WF := tfc_tabToTab_wf hwf1 hfired
      exact ((floater_classification u1 hwf1 x).symm.trans
        ((floater_leg_invariant hwf1 hleg x).trans
          (floater_classification u2 hwf2 x))).trans (ih hwf2 x)
/-- Bool: every bottomed king of `st` keeps its seat in `w`. -/
private def allFixedB (st w : State) : Bool :=
  (kingsOf st).all (fun c => decide (seatOf w c = seatOf st c))

/-- The seat of `w` read back as an anchor (junk off the king's inl-seat). -/
private def wAnchor (w : State) (c : Card) : Anchor :=
  match seatOf w c with
  | some (Sum.inl a) => a
  | _ => Anchor.p0

private theorem all_eq_false' {l : List Card} {p : Card → Bool} (h : l.all p = false) :
    ∃ c, c ∈ l ∧ p c = false := by
  induction l with
  | nil => exact absurd h (by simp)
  | cons x xs ih =>
      cases hpx : p x with
      | false => exact ⟨x, List.mem_cons_self .., hpx⟩
      | true =>
          have h2 : (p x && xs.all p) = false := h
          rw [hpx] at h2
          obtain ⟨c, hc, hp⟩ := ih h2
          exact ⟨c, List.mem_cons_of_mem x hc, hp⟩
/-- **bareCargo_of_chartVK** — the `←` direction for the un-mediated relation:
a chart with the VK king arm, the readouts and the licensing is a class-mate.
No `hnomed`. -/
theorem bareCargo_of_chartVK {st w : State} (hwfst : st.WF) (hw : w.WF)
    (hroundtrip : ∀ A B, chartAgree A B → A = B)
    (hrel : ∀ x, (seatOf w x = seatOf st x) ∨
        (∃ z', seatOf st x = some (Sum.inr z') ∧
          seatOf w x = some (Sum.inr z'.twin)) ∨
        (x.rank = Rank.king ∧ ∃ a a', seatOf st x = some (Sum.inl a) ∧
          seatOf w x = some (Sum.inl a') ∧ VKSet st a'))
    (hro : boardFixed st w ∧ foundsFixed st w ∧
      drawPool st = drawPool w ∧ cutOf st = cutOf w)
    (hlic : ∀ x, seatOf st x ≠ seatOf w x → FloaterSpec st x) :
    BareCargoEquiv st w := by
  cases hb : allFixedB st w with
  | true =>
      have hfixed : ∀ c ∈ kingsOf st, seatOf w c = seatOf st c := by
        intro c hc
        exact of_decide_eq_true (List.all_eq_true.mp hb c hc)
      refine bareCargo_of_seatchart hwfst hw hroundtrip ?_ hlic hro
      intro x
      by_cases hk : x.rank = Rank.king
      · by_cases hmem : x ∈ kingsOf st
        · exact Or.inl (hfixed x hmem)
        · rcases hrel x with h1 | h2 | h3
          · exact Or.inl h1
          · obtain ⟨z', hz, -⟩ := h2
            exact absurd hz (fun h => king_seat_inr_absurd hwfst hk h)
          · obtain ⟨-, a, a', hse, hse_w, -⟩ := h3
            by_cases haa : a = a'
            · exact Or.inl (by rw [hse, hse_w, haa])
            · exfalso
              have hchg : seatOf st x ≠ seatOf w x := by
                rw [hse, hse_w]
                exact fun h => haa (Sum.inl.inj (Option.some.inj h))
              have hfs := hlic x hchg
              rcases hfs with ⟨z, a0, hse_inr, -, -⟩ |
                ⟨a0, hse_inl0, hkr, hhid0, a1, -⟩
              · rw [hse] at hse_inr
                exact absurd hse_inr (by simp)
              · have hmem' : x ∈ kingsOf st :=
                  (mem_kingsOf hwfst).mpr ⟨a0, ⟨x, hse_inl0, hkr, hhid0⟩, hse_inl0⟩
                have hcontra := hfixed x hmem'
                rw [hse, hse_w] at hcontra
                exact haa (Sum.inl.inj (Option.some.inj hcontra)).symm
      · rcases hrel x with h1 | h2 | h3
        · exact Or.inl h1
        · exact Or.inr (Or.inl h2)
        · exact absurd h3.1 hk
  | false =>
      obtain ⟨xm, hxmmem, hd⟩ := all_eq_false' hb
      have hchgm : seatOf w xm ≠ seatOf st xm := of_decide_eq_false hd
      obtain ⟨a0, hkb0, hse0⟩ := (mem_kingsOf hwfst).mp hxmmem
      obtain ⟨c0, hse_c0, hk_c0, hhid_c0⟩ := hkb0
      have hc0 : c0 = xm := king_seat_injective hse_c0 hse0
      have hkm : xm.rank = Rank.king := by rw [← hc0]; exact hk_c0
      have hvac : HasVacancy st := by
        have hfs := hlic xm (fun h => hchgm h.symm)
        rcases hfs with ⟨z, a, hse_inr, -, -⟩ | ⟨a, hse_inl, hkr, hhid, a', hiso⟩
        · exact absurd hse_inr (fun h => king_seat_inr_absurd hwfst hkm h)
        · exact ⟨a', hiso⟩
      have hτ_eq : ∀ {c : Card} {a : Anchor},
          seatOf w c = some (Sum.inl a) → wAnchor w c = a := by
        intro c a ha
        show (match seatOf w c with
              | some (Sum.inl a) => a
              | _ => Anchor.p0) = a
        rw [ha]
      have hk_inl : ∀ c ∈ kingsOf st, ∃ a, seatOf w c = some (Sum.inl a) := by
        intro c hc
        obtain ⟨a0, hkb0, hse0⟩ := (mem_kingsOf hwfst).mp hc
        obtain ⟨c0, hse_c0, hk_c0, hhid_c0⟩ := hkb0
        have hcc0 : c0 = c := king_seat_injective hse_c0 hse0
        have hkc : c.rank = Rank.king := by rw [← hcc0]; exact hk_c0
        rcases hrel c with h1 | h2 | h3
        · exact ⟨a0, by rw [h1]; exact hse0⟩
        · obtain ⟨z', hz, -⟩ := h2
          exact absurd hz (fun h => king_seat_inr_absurd hwfst hkc h)
        · obtain ⟨-, a, a', hse, hse_w, -⟩ := h3
          exact ⟨a', hse_w⟩
      have hagree : ∀ c ∈ kingsOf st,
          seatOf w c = some (Sum.inl (wAnchor w c)) := by
        intro c hc
        obtain ⟨a, ha⟩ := hk_inl c hc
        rw [hτ_eq ha]
        exact ha
      have ht : ∀ c ∈ kingsOf st, VKSet st (wAnchor w c) := by
        intro c hc
        obtain ⟨a0, hkb0, hse0⟩ := (mem_kingsOf hwfst).mp hc
        obtain ⟨c0, hse_c0, hk_c0, hhid_c0⟩ := hkb0
        have hcc0 : c0 = c := king_seat_injective hse_c0 hse0
        have hkc : c.rank = Rank.king := by rw [← hcc0]; exact hk_c0
        rcases hrel c with h1 | h2 | h3
        · have ha : seatOf w c = some (Sum.inl a0) := by rw [h1]; exact hse0
          rw [hτ_eq ha]
          exact Or.inr ⟨c, hse0, hkc, hhid_c0⟩
        · obtain ⟨z', hz, -⟩ := h2
          exact absurd hz (fun h => king_seat_inr_absurd hwfst hkc h)
        · obtain ⟨-, a, a', hse, hse_w, hvk⟩ := h3
          rw [hτ_eq hse_w]
          exact hvk
      have hinj : ∀ c ∈ kingsOf st, ∀ c' ∈ kingsOf st,
          wAnchor w c = wAnchor w c' → c = c' := by
        intro c hc c' hc' heq
        have h1 := hagree c hc
        have h2 := hagree c' hc'
        rw [heq] at h1
        exact king_seat_injective h1 h2
      obtain ⟨u, hks, hkings⟩ :=
        king_assignment_reachable hwfst hvac (wAnchor w) (kingsOf st)
          (fun c hc => (mem_kingsOf hwfst).mp hc) ht (kingsOf_nodup st) hinj
      have hwfu : u.WF := king_shuffle_wf hks hwfst
      -- the residual chart, with full emptiness on the (vacuous) king arm
      have hrel_u : ∀ x, (seatOf w x = seatOf u x) ∨
          (∃ z', seatOf u x = some (Sum.inr z') ∧
            seatOf w x = some (Sum.inr z'.twin)) ∨
          (x.rank = Rank.king ∧ ∃ a a', seatOf u x = some (Sum.inl a) ∧
            seatOf w x = some (Sum.inl a') ∧ (u.piles a').isEmpty = true) := by
        intro x
        by_cases hk : x.rank = Rank.king
        · left
          by_cases hmem : x ∈ kingsOf st
          · rw [hkings x hmem, hagree x hmem]
          · have hnot : ¬ ∃ a', KingBottom st a' ∧ seatOf st x = some (Sum.inl a') :=
              fun h => hmem ((mem_kingsOf hwfst).mpr h)
            have hsu : seatOf u x = seatOf st x :=
              king_shuffle_seat_of_not_bottomed hks hwfst x hnot
            have hsw : seatOf w x = seatOf st x := by
              rcases hrel x with h1 | h2 | h3
              · exact h1
              · obtain ⟨z', hz, -⟩ := h2
                exact absurd hz (fun h => king_seat_inr_absurd hwfst hk h)
              · obtain ⟨-, a, a', hse, hse_w, -⟩ := h3
                by_cases haa : a = a'
                · rw [hse_w, hse, ← haa]
                · exfalso
                  have hchg : seatOf st x ≠ seatOf w x := by
                    rw [hse, hse_w]
                    exact fun h => haa (Sum.inl.inj (Option.some.inj h))
                  have hfs := hlic x hchg
                  rcases hfs with ⟨z, a0, hse_inr, -, -⟩ | ⟨a0, hse_inl0, hkr, hhid0, a1, -⟩
                  · rw [hse] at hse_inr
                    exact absurd hse_inr (by simp)
                  · exact hmem ((mem_kingsOf hwfst).mpr
                      ⟨a0, ⟨x, hse_inl0, hkr, hhid0⟩, hse_inl0⟩)
            rw [hsu, hsw]
        · rcases hrel x with h1 | h2 | h3
          · left
            have hnot : ¬ ∃ a', KingBottom st a' ∧ seatOf st x = some (Sum.inl a') := by
              rintro ⟨a', ⟨c9, hse9, hk9, -⟩, hse9'⟩
              have hcc : c9 = x := king_seat_injective hse9 hse9'
              exact hk (by rw [← hcc]; exact hk9)
            rw [h1, king_shuffle_seat_of_not_bottomed hks hwfst x hnot]
          · right; left
            obtain ⟨z', hz, hzw⟩ := h2
            have hnot : ¬ ∃ a', KingBottom st a' ∧ seatOf st x = some (Sum.inl a') := by
              rintro ⟨a', ⟨c9, hse9, hk9, -⟩, hse9'⟩
              have hcc : c9 = x := king_seat_injective hse9 hse9'
              exact hk (by rw [← hcc]; exact hk9)
            exact ⟨z', by rw [king_shuffle_seat_of_not_bottomed hks hwfst x hnot]; exact hz, hzw⟩
          · exact absurd h3.1 hk
      have hlic_u : ∀ x, seatOf u x ≠ seatOf w x → FloaterSpec u x := by
        intro x hchg
        by_cases hk : x.rank = Rank.king
        · exfalso
          by_cases hmem : x ∈ kingsOf st
          · rw [hkings x hmem, hagree x hmem] at hchg
            exact hchg rfl
          · have hnot : ¬ ∃ a', KingBottom st a' ∧ seatOf st x = some (Sum.inl a') :=
              fun h => hmem ((mem_kingsOf hwfst).mpr h)
            have hsu : seatOf u x = seatOf st x :=
              king_shuffle_seat_of_not_bottomed hks hwfst x hnot
            rcases hrel x with h1 | h2 | h3
            · rw [hsu, h1] at hchg
              exact hchg rfl
            · obtain ⟨z', hz, -⟩ := h2
              exact absurd hz (fun h => king_seat_inr_absurd hwfst hk h)
            · obtain ⟨-, a, a', hse, hse_w, -⟩ := h3
              by_cases haa : a = a'
              · rw [hsu, hse, hse_w, haa] at hchg
                exact hchg rfl
              · have hchgst : seatOf st x ≠ seatOf w x := by
                  rw [hse, hse_w]
                  exact fun h => haa (Sum.inl.inj (Option.some.inj h))
                have hfs := hlic x hchgst
                rcases hfs with ⟨z, a0, hse_inr, -, -⟩ | ⟨a0, hse_inl0, hkr, hhid0, a1, -⟩
                · rw [hse] at hse_inr
                  exact absurd hse_inr (by simp)
                · exact hmem ((mem_kingsOf hwfst).mpr
                    ⟨a0, ⟨x, hse_inl0, hkr, hhid0⟩, hse_inl0⟩)
        · have hnot : ¬ ∃ a', KingBottom st a' ∧ seatOf st x = some (Sum.inl a') := by
            rintro ⟨a', ⟨c9, hse9, hk9, -⟩, hse9'⟩
            have hcc : c9 = x := king_seat_injective hse9 hse9'
            exact hk (by rw [← hcc]; exact hk9)
          have hsu : seatOf u x = seatOf st x :=
            king_shuffle_seat_of_not_bottomed hks hwfst x hnot
          have hchgst : seatOf st x ≠ seatOf w x := by
            rw [← hsu]
            exact hchg
          exact (king_shuffle_floaterSpec hks hwfst x).mp (hlic x hchgst)
      obtain ⟨hb_u, hf_u, hd_u, hc_u⟩ := king_shuffle_readouts hks hwfst
      obtain ⟨hb0, hf0, hd0, hc0⟩ := hro
      have hro_u : boardFixed u w ∧ foundsFixed u w ∧
          drawPool u = drawPool w ∧ cutOf u = cutOf w :=
        ⟨⟨fun j => (hb_u.1 j).symm.trans (hb0.1 j), hb_u.2.symm.trans hb0.2⟩,
          fun j => (hf_u j).symm.trans (hf0 j), hd_u.symm.trans hd0, hc_u.symm.trans hc0⟩
      exact orbit_bareCargo_trans (king_shuffle_closure hwfst hroundtrip hks)
        (bareCargo_of_seatchart hwfu hw hroundtrip hrel_u hlic_u hro_u)
/-- **bareCargo_iff_vk** — THE UN-MEDIATED CLASS IFF, with NO `hnomed`: the
class relation is exactly the per-card chart (identity / twin edge / a king
landing on a node of the fuel set) together with the readouts and the
st-side licensing.  The king seats are an injective map into `VKSet` (the map
is `seatOf w`, functional by construction and injective by
`king_seat_injective`), and the licensing's king cell carries the vacancy the
schedule needs. -/
theorem bareCargo_iff_vk {st w : State} (hwfst : st.WF) (hw : w.WF)
    (hroundtrip : ∀ A B, chartAgree A B → A = B) :
    BareCargoEquiv st w ↔
      ((∀ x, (seatOf w x = seatOf st x) ∨
          (∃ z', seatOf st x = some (Sum.inr z') ∧
            seatOf w x = some (Sum.inr z'.twin)) ∨
          (x.rank = Rank.king ∧ ∃ a a', seatOf st x = some (Sum.inl a) ∧
            seatOf w x = some (Sum.inl a') ∧ VKSet st a')) ∧
      (boardFixed st w ∧ foundsFixed st w ∧
        drawPool st = drawPool w ∧ cutOf st = cutOf w) ∧
      (∀ x, seatOf st x ≠ seatOf w x → FloaterSpec st x)) := by
  constructor
  · intro hpair
    exact bareCargo_to_chartDiff_vk hwfst hpair
  · rintro ⟨hrel, hro, hlic⟩
    exact bareCargo_of_chartVK hwfst hw hroundtrip hrel hro hlic

/-! #### §M11g. THE FACTORED FORM — the class iff with the per-card relation
split by rank into the KING half (fuel-set targets) and the TWIN half. -/

/-- **king_twin_split** — the per-card net relation factors into a KING half
(kings: fixed or moved onto a node of the fuel set at `st`) and a TWIN half
(non-kings: fixed or carried to the twin of their parent). -/
theorem king_twin_split {st w : State} (hwfst : st.WF) :
    (∀ x, (seatOf w x = seatOf st x) ∨
        (∃ z', seatOf st x = some (Sum.inr z') ∧
          seatOf w x = some (Sum.inr z'.twin)) ∨
        (x.rank = Rank.king ∧ ∃ a a', seatOf st x = some (Sum.inl a) ∧
          seatOf w x = some (Sum.inl a') ∧ VKSet st a'))
      ↔
    (∀ x, x.rank = Rank.king →
        (seatOf w x = seatOf st x ∨
          ∃ a a', seatOf st x = some (Sum.inl a) ∧
            seatOf w x = some (Sum.inl a') ∧ VKSet st a')) ∧
    (∀ x, x.rank ≠ Rank.king →
        (seatOf w x = seatOf st x ∨
          ∃ z', seatOf st x = some (Sum.inr z') ∧
            seatOf w x = some (Sum.inr z'.twin))) := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro x hk
      rcases h x with hsame | htwin | ⟨-, a, a', hse, hse_w, hvk⟩
      · exact Or.inl hsame
      · obtain ⟨z', hse, -⟩ := htwin
        exact (king_seat_inr_absurd hwfst hk hse).elim
      · exact Or.inr ⟨a, a', hse, hse_w, hvk⟩
    · intro x hnk
      rcases h x with hsame | htwin | ⟨hkk, -⟩
      · exact Or.inl hsame
      · exact Or.inr htwin
      · exact absurd hkk hnk
  · rintro ⟨hking, hnon⟩ x
    by_cases hk : x.rank = Rank.king
    · rcases hking x hk with hsame | ⟨a, a', hse, hse_w, hvk⟩
      · exact Or.inl hsame
      · exact Or.inr (Or.inr ⟨hk, a, a', hse, hse_w, hvk⟩)
    · rcases hnon x hk with hsame | htwin
      · exact Or.inl hsame
      · exact Or.inr (Or.inl htwin)

/-- **bareCargo_iff_split** — the class iff with the relation factored into
the king half (fuel-set targets) and the twin half. -/
theorem bareCargo_iff_split {st w : State}
    (hwfst : st.WF) (hw : w.WF)
    (hroundtrip : ∀ A B, chartAgree A B → A = B) :
    BareCargoEquiv st w ↔
      ((∀ x, x.rank = Rank.king →
          (seatOf w x = seatOf st x ∨
            ∃ a a', seatOf st x = some (Sum.inl a) ∧
              seatOf w x = some (Sum.inl a') ∧ VKSet st a')) ∧
       (∀ x, x.rank ≠ Rank.king →
          (seatOf w x = seatOf st x ∨
            ∃ z', seatOf st x = some (Sum.inr z') ∧
              seatOf w x = some (Sum.inr z'.twin)))) ∧
      (boardFixed st w ∧ foundsFixed st w ∧
        drawPool st = drawPool w ∧ cutOf st = cutOf w) ∧
      (∀ x, seatOf st x ≠ seatOf w x → FloaterSpec st x) := by
  rw [bareCargo_iff_vk hwfst hw hroundtrip]
  constructor
  · rintro ⟨hrel, hr, hl⟩
    exact ⟨(king_twin_split hwfst).mp hrel, hr, hl⟩
  · rintro ⟨hsplit, hr, hl⟩
    exact ⟨(king_twin_split hwfst).mpr hsplit, hr, hl⟩

/-! ## The audit battery -/

#print axioms bareCargo_to_chartDiff_full
#print axioms bareCargo_orbit_spare_empty
#print axioms vacuity_orbit_iff
#print axioms orbit_empty_equiv_step
#print axioms bareCargo_orbit_empty_iso
#print axioms bareCargo_orbit_empty_count
#print axioms vacuity_count_orbit_iff
#print axioms bareCargo_orbit_vk
#print axioms bareCargo_orbit_vk_transfer
#print axioms king_reaches_vk
#print axioms king_assignment_reachable
#print axioms king_twin_split
#print axioms bareCargo_iff_split
#print axioms king_half_shuffle
#print axioms bareCargo_king_then
#print axioms king_seat_injective
#print axioms bareCargo_to_chartDiff_vk
#print axioms bareCargo_of_chartVK
#print axioms bareCargo_iff_vk
#print axioms king_shuffle_vacancy
#print axioms king_shuffle_closure
#print axioms king_shuffle_trivial_of_no_vacancy
#print axioms floater_leg_invariant
#print axioms floater_orbit_invariant
#print axioms floater_path_invariant
#print axioms floater_orbit_wf_prsv
#print axioms bareCargo_to_chartDiff
#print axioms bareCargo_reconstruct_singleEdit
#print axioms bareCargo_reconstruct_companyFlat
#print axioms bareCargo_reconstruct_kingFlat
#print axioms bareCargo_of_seatchart_company
#print axioms bareCargo_iff_seatchart_company
#print axioms bareCargo_of_seatchart
#print axioms orbit_king_hidden_vacate

