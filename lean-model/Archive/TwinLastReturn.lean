import Orig2.TwinPairFreeTransfer
import Orig2.TwinFirstTouchReduction
import Orig2.TwinSelfArm
import Orig2.TwinSwapRecipe
import Orig2.TwinBothCovered
import Orig2.TwinFoundationRow
import Orig2.TwinSpliceComm
import Orig2.Chart
import Orig2.StepWF

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 2000000

/-!
# Orig2.TwinLastReturn — `FirstTouchRestart` proved: the last-return route

The owner's route, completed: the transfer is NOT carried through the
excursion — it is RECONSTRUCTED at the last return.

## The factorization

For the witness journey of `FirstTouchRestart` (first touch = a raise of
a twin `T` at `w`, suffix `w' ⇝ v`):

1. the suffix must contain a touching letter (the raised twin must
   come back for `v`'s seats to hold — the found-membership walk row);
2. split the suffix at its LAST touching letter `r`: it must be a
   RETURN (`foundToTab R b`) — a raise would strand its twin on the
   foundation through the pair-free tail;
3. at the post-return state `s` the recipe's conditions are
   self-satisfied: the returned twin is BARE and its foundation is
   re-armed (`TwinSelfArm.reversibleAtW_tabToFound_of_foundToTab`),
   and both twins are `.inr`-seated (the seat tracker below; a twin on
   the foundation would stay there through the pair-free tail);
4. the recipe (`TwinSwapRecipe.swappableIn_of_twin_raise`) fires at
   `s`; the pair-free tail transports to `v` by the landed pair-free
   transfer.

The excursion's middle never matters: the swap is rebuilt at the end.

## Kit notes (house norm)

The two foundation-membership transport rows this card needs are
restated here as private copies with their sources cited, per the
per-file private-kit norm: `found_mem_step` (per letter; from
`TwinAttShapes.found_mem_step_of_not_pullOf`,
`Orig2/TwinAttShapes.lean:1026`) and `found_mem_play_of_not_pull`
(per play; from `TwinExcursionClosure.found_mem_play_of_not_pull`,
`Orig2/TwinExcursionClosure.lean:832`).  No attachment-world module
is imported for a single row.
-/

open State

/-! ## 1. The per-letter pair-foundation dichotomy (choice-free) -/

private theorem isPairFound_or_not {x : Card} {m : Move} :
    IsPairFound x m ∨ ¬ IsPairFound x m := by
  cases m with
  | draw => exact Or.inr (fun h => by
    rcases h with h | h | ⟨b, h⟩ | ⟨b, h⟩ <;> exact Move.noConfusion h)
  | wasteToFound y => exact Or.inr (fun h => by
    rcases h with h | h | ⟨b, h⟩ | ⟨b, h⟩ <;> exact Move.noConfusion h)
  | wasteToTab y b => exact Or.inr (fun h => by
    rcases h with h | h | ⟨b', h⟩ | ⟨b', h⟩ <;> exact Move.noConfusion h)
  | tabToFound y =>
      by_cases hy : y = x
      · exact Or.inl (Or.inl (congrArg Move.tabToFound hy))
      · by_cases hyt : y = x.twin
        · exact Or.inl (Or.inr (Or.inl (congrArg Move.tabToFound hyt)))
        · exact Or.inr (fun h => by
            rcases h with h | h | ⟨b, h⟩ | ⟨b, h⟩
            · exact hy (Move.tabToFound.inj h)
            · exact hyt (Move.tabToFound.inj h)
            · exact Move.noConfusion h
            · exact Move.noConfusion h)
  | foundToTab y b =>
      by_cases hy : y = x
      · exact Or.inl (Or.inr (Or.inr (Or.inl
          ⟨b, congrArg (fun y => Move.foundToTab y b) hy⟩)))
      · by_cases hyt : y = x.twin
        · exact Or.inl (Or.inr (Or.inr (Or.inr
            ⟨b, congrArg (fun y => Move.foundToTab y b) hyt⟩)))
        · exact Or.inr (fun h => by
            rcases h with h | h | ⟨b', h⟩ | ⟨b', h⟩
            · exact Move.noConfusion h
            · exact Move.noConfusion h
            · exact hy (Move.foundToTab.inj h).1
            · exact hyt (Move.foundToTab.inj h).1)
  | tabToTab y b => exact Or.inr (fun h => by
    rcases h with h | h | ⟨b', h⟩ | ⟨b', h⟩ <;> exact Move.noConfusion h)

private theorem isPairFound_of_not_notFoundPair {x : Card} {m : Move}
    (h : ¬ NotFoundPair x m) : IsPairFound x m := by
  rcases isPairFound_or_not (x := x) (m := m) with hc | hc
  · exact hc
  · exact absurd hc (fun hip' => h ((notFoundPair_iff_not_isPairFound x m).mpr hip'))

/-! ## 2. The last-touch split -/

private theorem exists_lastPairFound_split (x : Card) (play : List Move) :
    (∀ n ∈ play, ¬ IsPairFound x n) ∨
    ∃ pre r post, play = pre ++ r :: post ∧ IsPairFound x r ∧
      (∀ n ∈ post, ¬ IsPairFound x n) := by
  induction play with
  | nil => exact Or.inl (by simp)
  | cons k t ih =>
      rcases isPairFound_or_not (x := x) (m := k) with hk | hk
      · rcases ih with hall | ⟨pre, r, post, hsplit, hr, hpost⟩
        · exact Or.inr ⟨[], k, t, rfl, hk, hall⟩
        · exact Or.inr ⟨k :: pre, r, post, by
            rw [List.cons_append, hsplit], hr, hpost⟩
      · rcases ih with hall | ⟨pre, r, post, hsplit, hr, hpost⟩
        · exact Or.inl (by
            intro n hn
            rcases List.mem_cons.mp hn with rfl | hn
            · exact hk
            · exact hall n hn)
        · exact Or.inr ⟨k :: pre, r, post, by
            rw [List.cons_append, hsplit], hr, hpost⟩

/-! ## 3. The not-pull read of pair-freeness -/

private theorem not_pull_play_of_notFoundPair {x : Card} {play : List Move}
    (hno : ∀ n ∈ play, NotFoundPair x n) {y : Card} (hy : y = x ∨ y = x.twin) :
    ∀ k ∈ play, ∀ b : Base, k ≠ Move.foundToTab y b := by
  intro k hk b hb
  rcases hy with rfl | rfl
  · exact (hno k hk).2.2.1 b hb
  · exact (hno k hk).2.2.2 b hb

/-- Pair-freeness is twin-symmetric: the predicate names the pair, and
`x` and `x.twin` name the same pair. -/
private theorem notFoundPair_twin' {x : Card} {m : Move}
    (h : NotFoundPair x m) : NotFoundPair x.twin m := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact ⟨h2, fun hb => h1 (by rw [hb, card_twin_twin]),
    h4, fun b hb => h3 b (by rw [hb, card_twin_twin])⟩

/-! ## 3b. The foundation-membership rows (restated kit)

Two private kit rows restated in-card, per the house norm, with their
sources cited — this card carries no attachment-world import for a
single row. -/

/-- Foundation membership survives every letter except the pull of
that very card.  Restated private port of
`TwinAttShapes.found_mem_step_of_not_pullOf`
(`Orig2/TwinAttShapes.lean:1026`). -/
private theorem found_mem_step {u v : State} {m : Move} {y : Card}
    (hstep : State.step u m = some v)
    (hmem : y ∈ u.found y.suit)
    (hnot : ∀ b : Base, m ≠ Move.foundToTab y b) :
    y ∈ v.found y.suit := by
  cases m with
  | draw =>
      rw [← (chart_draw hstep).2.1 y.suit]
      exact hmem
  | wasteToFound c =>
      obtain ⟨-, z, zs, hw, hs⟩ := step_wasteToFound_inv hstep
      rw [hs]
      by_cases hys : c.suit = y.suit
      · rw [← hys]
        rw [← hys] at hmem
        rw [setFound_found_self]
        exact List.mem_append_left _ hmem
      · rw [setFound_found_ne (fun h => hys h.symm)]
        exact hmem
  | wasteToTab c b =>
      obtain ⟨-, z, zs, hw, hs⟩ := step_wasteToTab_inv hstep
      rw [hs]
      cases b with
      | inl t => rw [putCard_inl_found]; exact hmem
      | inr z => rw [putCard_inr_found]; exact hmem
  | tabToFound c =>
      obtain ⟨-, a, hpa, hs⟩ := step_tabToFound_inv hstep
      rw [hs]
      by_cases hys : c.suit = y.suit
      · rw [← hys]
        rw [← hys] at hmem
        rw [setFound_found_self]
        exact List.mem_append_left _ hmem
      · rw [setFound_found_ne (fun h => hys h.symm)]
        exact hmem
  | foundToTab c b =>
      obtain ⟨c', htop, hc'c, hcp, hs⟩ := step_foundToTab_inv hstep
      rw [hs]
      have hfound : ((u.setFound c.suit (chop (u.found c.suit))).putCard c b).found
          = (u.setFound c.suit (chop (u.found c.suit))).found := by
        cases b with
        | inl t => rw [putCard_inl_found]
        | inr z => rw [putCard_inr_found]
      rw [hfound]
      by_cases hys : c.suit = y.suit
      · rw [← hys]
        rw [← hys] at hmem
        have hlast : lastOf (u.found c.suit) = some c := by
          unfold State.foundTop at htop
          rw [hc'c] at htop
          exact htop
        have hyc : y ≠ c := by
          intro hyc
          exact hnot b (by rw [hyc])
        have hsnoc : u.found c.suit = chop (u.found c.suit) ++ [c] :=
          lastOf_chop hlast
        have hchop : y ∈ chop (u.found c.suit) := by
          rw [hsnoc, List.mem_append] at hmem
          rcases hmem with h | h
          · exact h
          · rw [List.mem_singleton] at h
            exact False.elim (hyc h)
        rw [setFound_found_self]
        exact hchop
      · rw [setFound_found_ne (fun h => hys h.symm)]
        exact hmem
  | tabToTab c b =>
      obtain ⟨a, hhold, hcp, -, hs⟩ := step_tabToTab_inv hstep
      rw [hs]
      rw [putRun_found, setPile_found]
      exact hmem

/-- A card on its foundation row stays there across any play that never
pulls it.  Restated private port of
`TwinExcursionClosure.found_mem_play_of_not_pull`
(`Orig2/TwinExcursionClosure.lean:832`), proved from the step row above. -/
private theorem found_mem_play_of_not_pull {u t : State} {play : List Move} {y : Card}
    (hplay : ShufflePlayW u play t)
    (hmem : y ∈ u.found y.suit)
    (hno : ∀ k ∈ play, ∀ b : Base, k ≠ Move.foundToTab y b) :
    y ∈ t.found y.suit := by
  induction play generalizing u t with
  | nil => cases hplay; exact hmem
  | cons k rest ih =>
      obtain ⟨u1, hrevK, hstepK, hrest⟩ := TwinForcedCancel.walk_cons_inv hplay
      have hmem1 : y ∈ u1.found y.suit :=
        found_mem_step hstepK hmem (hno k (by simp))
      exact ih hrest hmem1
        (fun n hn => hno n (List.mem_cons_of_mem k hn))

/-! ## 4. The seat tracker -/

/-- A non-royal card that is `.inr`-seated or on its foundation row
stays so through any reversible letter. -/
private theorem seat_track_step {u v : State} {m : Move} {c : Card}
    (hwf : u.WF) (hstep : State.step u m = some v) (hrev : reversibleAtW u m)
    (hking : c.rank ≠ Rank.king)
    (h : (∃ z, seatOf u c = some (Sum.inr z)) ∨ c ∈ u.found c.suit) :
    (∃ z, seatOf v c = some (Sum.inr z)) ∨ c ∈ v.found c.suit := by
  cases m with
  | draw =>
      have hse := (chart_draw hstep).1
      have hfo := (chart_draw hstep).2.1 c.suit
      rcases h with ⟨z, hz⟩ | hmem
      · exact Or.inl ⟨z, by rw [hse c]; exact hz⟩
      · exact Or.inr (by rw [← hfo]; exact hmem)
  | wasteToFound y => exact absurd hrev (wasteToFound_not_reversibleAtW u y)
  | wasteToTab y b => exact absurd hrev (wasteToTab_not_reversibleAtW u y b)
  | tabToFound d =>
      by_cases hcd : c = d
      · subst hcd
        refine Or.inr ?_
        rw [TwinFoundationRow.raise_found_self hstep]
        exact List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl))
      · rcases h with ⟨z, hz⟩ | hmem
        · refine Or.inl ⟨z, ?_⟩
          rw [raise_seat_change_of_seated hstep hrev (by rw [hz]; simp) hcd]
          exact hz
        · exact Or.inr (found_mem_step hstep hmem
            (fun b hb => Move.noConfusion hb))
  | foundToTab y b =>
      by_cases hcy : c = y
      · subst hcy
        obtain ⟨-, -, -, hcp, -⟩ := step_foundToTab_inv hstep
        cases b with
        | inl a => exact absurd (canPlace_inl hcp).2 hking
        | inr z => exact Or.inl ⟨z, TwinSpliceComm.seatOf_foundToTab_mover hwf hstep⟩
      · rcases h with ⟨z, hz⟩ | hmem
        · refine Or.inl ⟨z, ?_⟩
          rw [pull_seat_change hstep c hcy]
          exact hz
        · exact Or.inr (found_mem_step hstep hmem
            (fun b' hb' => hcy (by injection hb' with h1 h2; exact h1.symm)))
  | tabToTab y b =>
      obtain ⟨a, hhold, hcp, -, hs⟩ := step_tabToTab_inv hstep
      have hfound : ∀ s', v.found s' = u.found s' := by
        rw [hs]
        intro s'
        rw [putRun_found, setPile_found]
      by_cases hcy : c = y
      · subst hcy
        cases b with
        | inl a' => exact absurd (canPlace_inl hcp).2 hking
        | inr z' =>
            refine Or.inl ⟨z', ?_⟩
            rw [tfc_seat_point_edit hwf hstep hrev c, if_pos rfl]
      · rcases h with ⟨z, hz⟩ | hmem
        · refine Or.inl ⟨z, ?_⟩
          rw [tfc_seat_point_edit hwf hstep hrev c, if_neg hcy]
          exact hz
        · exact Or.inr (by rw [hfound c.suit]; exact hmem)

private theorem seat_track_play {u v : State} {c : Card} {play : List Move}
    (hwf : u.WF) (hplay : ShufflePlayW u play v)
    (hking : c.rank ≠ Rank.king)
    (h : (∃ z, seatOf u c = some (Sum.inr z)) ∨ c ∈ u.found c.suit) :
    (∃ z, seatOf v c = some (Sum.inr z)) ∨ c ∈ v.found c.suit := by
  revert hwf h
  induction hplay with
  | nil st =>
      intro hwf h
      exact h
  | @cons st s1 W m rest' hrev hstep hrest ih =>
      intro hwf h
      exact ih (step_wf hwf hstep) (seat_track_step hwf hstep hrev hking h)

/-! ## 5. The main theorem -/

private theorem firstTouchRestart_aux {w w' v : State} {x T : Card}
    {rest : List Move}
    (hwf : w.WF) (hvfv : v.WF)
    (hpair : T = x ∨ T = x.twin)
    (hseatTw : ∃ z, seatOf w T = some (Sum.inr z))
    (hseatTw' : ∃ z, seatOf w T.twin = some (Sum.inr z))
    (hseatTv : ∃ z, seatOf v T = some (Sum.inr z))
    (hseatTv' : ∃ z, seatOf v T.twin = some (Sum.inr z))
    (hrev : reversibleAtW w (Move.tabToFound T))
    (hstep : State.step w (Move.tabToFound T) = some w')
    (hrest : ShufflePlayW w' rest v) :
    SwappableIn v T := by
  -- the four plain seat facts for the pair, hoisted
  have hxw : ∃ z, seatOf w x = some (Sum.inr z) := by
    rcases hpair with rfl | rfl
    · exact hseatTw
    · obtain ⟨z, hz⟩ := hseatTw'
      rw [card_twin_twin] at hz
      exact ⟨z, hz⟩
  have hxtw : ∃ z, seatOf w x.twin = some (Sum.inr z) := by
    rcases hpair with rfl | rfl
    · obtain ⟨z, hz⟩ := hseatTw'
      exact ⟨z, hz⟩
    · obtain ⟨z, hz⟩ := hseatTw
      exact ⟨z, hz⟩
  have hxv : ∃ z, seatOf v x = some (Sum.inr z) := by
    rcases hpair with rfl | rfl
    · exact hseatTv
    · obtain ⟨z, hz⟩ := hseatTv'
      rw [card_twin_twin] at hz
      exact ⟨z, hz⟩
  have hxtv : ∃ z, seatOf v x.twin = some (Sum.inr z) := by
    rcases hpair with rfl | rfl
    · obtain ⟨z, hz⟩ := hseatTv'
      exact ⟨z, hz⟩
    · obtain ⟨z, hz⟩ := hseatTv
      exact ⟨z, hz⟩
  have ⟨zx, hzx⟩ := hxw
  have hxnr : x.rank ≠ Rank.king :=
    TwinFoundationRow.seated_inr_rank_ne_king hwf hzx
  have hTfound : T ∈ w'.found T.suit := by
    rw [TwinFoundationRow.raise_found_self hstep]
    exact List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl))
  rcases exists_lastPairFound_split x rest with hall | ⟨pre, r, post, hsplit, hr, hpost⟩
  · exfalso
    have hstays : T ∈ v.found T.suit :=
      found_mem_play_of_not_pull hrest hTfound
        (not_pull_play_of_notFoundPair
          (fun n hn => (notFoundPair_iff_not_isPairFound x n).mpr (hall n hn)) hpair)
    obtain ⟨z, hz⟩ := hseatTv
    exact absurd (TwinForcedCancel.seatOf_none_of_mem_found hvfv hstays) (by rw [hz]; simp)
  · subst hsplit
    obtain ⟨sm, hpre, hrpost⟩ := walk_append_split hrest
    obtain ⟨s, hrevr, hrstep, hpostw⟩ := TwinForcedCancel.walk_cons_inv hrpost
    have hwfw' : w'.WF := step_wf hwf hstep
    have hwfsm : sm.WF := run_wf hwfw'
      (Walk_run (P := fun st m => reversibleAtW st m) (st := w') (W := sm) hpre)
    have hwfs : s.WF := step_wf hwfsm hrstep
    have hpost' : ∀ n ∈ post, NotFoundPair x n :=
      fun n hn => (notFoundPair_iff_not_isPairFound x n).mpr (hpost n hn)
    rcases hr with rfl | rfl | ⟨b, hb⟩ | ⟨b, hb⟩
    · exfalso
      have hxstay : x ∈ v.found x.suit :=
        found_mem_play_of_not_pull hpostw (by
          rw [TwinFoundationRow.raise_found_self hrstep]
          exact List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl)))
          (not_pull_play_of_notFoundPair hpost' (Or.inl rfl))
      obtain ⟨z, hz⟩ := hxv
      exact absurd (TwinForcedCancel.seatOf_none_of_mem_found hvfv hxstay) (by rw [hz]; simp)
    · exfalso
      have hxtstay : x.twin ∈ v.found x.twin.suit :=
        found_mem_play_of_not_pull hpostw (by
          rw [TwinFoundationRow.raise_found_self hrstep]
          exact List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl)))
          (not_pull_play_of_notFoundPair hpost' (Or.inr rfl))
      obtain ⟨z, hz⟩ := hxtv
      exact absurd (TwinForcedCancel.seatOf_none_of_mem_found hvfv hxtstay) (by rw [hz]; simp)
    · -- r = foundToTab x b
      subst hb
      obtain ⟨-, -, -, hcp, -⟩ := step_foundToTab_inv hrstep
      cases b with
      | inl a => exact absurd (canPlace_inl hcp).2 hxnr
      | inr q =>
          have hRseat : seatOf s x = some (Sum.inr q) :=
            TwinSpliceComm.seatOf_foundToTab_mover hwfsm hrstep
          have hw2 : ShufflePlayW w
              ([Move.tabToFound T] ++ pre ++ [Move.foundToTab x (Sum.inr q)]) s :=
            ShufflePlayW_append
              (ShufflePlayW_append (Walk.cons hrev hstep (Walk.nil w')) hpre)
              (Walk.cons hrevr hrstep (Walk.nil s))
          have htrack := seat_track_play (c := x.twin) hwf hw2 hxnr (Or.inl hxtw)
          rcases htrack with ⟨z2, hxtseat⟩ | hxtfound
          · have halign : q.twin = z2 :=
              twin_parent_eq_of_seats hwfs hxtseat
                (show seatOf s x.twin.twin = some (Sum.inr q.twin.twin) from by
                  rw [card_twin_twin, card_twin_twin]
                  exact hRseat)
            have hct : seatOf s x.twin.twin = some (Sum.inr z2.twin) := by
              rw [card_twin_twin, ← halign, card_twin_twin]
              exact hRseat
            have hraise : reversibleAtW s (Move.tabToFound x.twin.twin) := by
              rw [card_twin_twin]
              exact reversibleAtW_tabToFound_of_foundToTab hwfsm hrstep
            have hswapO : SwappableIn s x.twin :=
              swappableIn_of_twin_raise hwfs hxtseat hct hraise
            have hxvT : ∃ z : Card, seatOf v x.twin.twin = some (Sum.inr z.twin) := by
              obtain ⟨z, hz⟩ := hxv
              exact ⟨z.twin, by rw [card_twin_twin, card_twin_twin]; exact hz⟩
            have hswapv : SwappableIn v x.twin :=
              swappableIn_transfer_of_pairFreePath hwfs hvfv ⟨z2, hxtseat⟩
                ⟨z2, hct⟩ hxtv hxvT hpostw
                (fun n hn => notFoundPair_twin' (hpost' n hn)) hswapO
            rcases hpair with rfl | rfl
            · rw [← card_twin_twin T]
              exact TwinBothCovered.swappableIn_twin_comm.mp hswapv
            · exact hswapv
          · exfalso
            have hxtstay : x.twin ∈ v.found x.twin.suit :=
              found_mem_play_of_not_pull hpostw hxtfound
                (not_pull_play_of_notFoundPair hpost' (Or.inr rfl))
            obtain ⟨z, hz⟩ := hxtv
            exact absurd (TwinForcedCancel.seatOf_none_of_mem_found hvfv hxtstay)
              (by rw [hz]; simp)
    · -- r = foundToTab x.twin b
      subst hb
      obtain ⟨-, -, -, hcp, -⟩ := step_foundToTab_inv hrstep
      cases b with
      | inl a => exact absurd (canPlace_inl hcp).2 hxnr
      | inr q =>
          have hRseat : seatOf s x.twin = some (Sum.inr q) :=
            TwinSpliceComm.seatOf_foundToTab_mover hwfsm hrstep
          have hw2 : ShufflePlayW w
              ([Move.tabToFound T] ++ pre ++ [Move.foundToTab x.twin (Sum.inr q)]) s :=
            ShufflePlayW_append
              (ShufflePlayW_append (Walk.cons hrev hstep (Walk.nil w')) hpre)
              (Walk.cons hrevr hrstep (Walk.nil s))
          have htrack := seat_track_play (c := x) hwf hw2 hxnr (Or.inl hxw)
          rcases htrack with ⟨z2, hxseat⟩ | hxfound
          · have halign : q.twin = z2 :=
              twin_parent_eq_of_seats hwfs hxseat
                (show seatOf s x.twin = some (Sum.inr q.twin.twin) from by
                  rw [card_twin_twin]
                  exact hRseat)
            have hct : seatOf s x.twin = some (Sum.inr z2.twin) := by
              rw [← halign, card_twin_twin]
              exact hRseat
            have hraise : reversibleAtW s (Move.tabToFound x.twin) :=
              reversibleAtW_tabToFound_of_foundToTab hwfsm hrstep
            have hswapO : SwappableIn s x :=
              swappableIn_of_twin_raise hwfs hxseat hct hraise
            have hxtvT : ∃ z : Card, seatOf v x.twin = some (Sum.inr z.twin) := by
              obtain ⟨z, hz⟩ := hxtv
              exact ⟨z.twin, by rw [card_twin_twin]; exact hz⟩
            have hswapv : SwappableIn v x :=
              swappableIn_transfer_of_pairFreePath hwfs hvfv ⟨z2, hxseat⟩
                ⟨z2, hct⟩ hxv hxtvT hpostw hpost' hswapO
            rcases hpair with rfl | rfl
            · exact hswapv
            · exact TwinBothCovered.swappableIn_twin_comm.mp hswapv
          · exfalso
            have hxstay : x ∈ v.found x.suit :=
              found_mem_play_of_not_pull hpostw hxfound
                (not_pull_play_of_notFoundPair hpost' (Or.inl rfl))
            obtain ⟨z, hz⟩ := hxv
            exact absurd (TwinForcedCancel.seatOf_none_of_mem_found hvfv hxstay)
              (by rw [hz]; simp)

theorem firstTouchRestart : FirstTouchRestart := by
  intro w w' v x rest hwf hvf hsx hstx htx httx hswap htouch
  obtain ⟨m, hm, hrev, hstep, hrest⟩ := htouch
  have hip : IsPairFound x m := isPairFound_of_not_notFoundPair hm
  have hsx' : ∃ z, seatOf w x = some (Sum.inr z) := hsx
  have hstx' : ∃ z, seatOf w x.twin = some (Sum.inr z) := by
    obtain ⟨z, hz⟩ := hstx
    exact ⟨z.twin, hz⟩
  have htx' : ∃ z, seatOf v x = some (Sum.inr z) := htx
  have httx' : ∃ z, seatOf v x.twin = some (Sum.inr z) := by
    obtain ⟨z, hz⟩ := httx
    exact ⟨z.twin, hz⟩
  rcases firstTouch_is_raise hwf hsx hstx hstep hip with rfl | rfl
  · exact firstTouchRestart_aux hwf hvf (Or.inl rfl) hsx' hstx' htx' httx'
      hrev hstep hrest
  · rw [← card_twin_twin x]
    exact TwinBothCovered.swappableIn_twin_comm.mp (firstTouchRestart_aux hwf hvf (Or.inr rfl)
      hstx' (by obtain ⟨z, hz⟩ := hsx'; exact ⟨z, by rw [card_twin_twin]; exact hz⟩)
      httx' (by obtain ⟨z, hz⟩ := htx'; exact ⟨z, by rw [card_twin_twin]; exact hz⟩)
      hrev hstep hrest)

/-- **THE CORRECTED FIBER TRANSFER** (the `.inr`-seat grade): swap
availability transfers along the class. -/
theorem fiber_transfer_corrected_of_lastReturn :
    ∀ (s s' : State) (x : Card), s.WF → s'.WF →
      sameOrbitSetoid.r s s' →
      (∃ z, seatOf s x = some (Sum.inr z)) →
      (∃ z : Card, seatOf s x.twin = some (Sum.inr z.twin)) →
      (∃ z, seatOf s' x = some (Sum.inr z)) →
      (∃ z : Card, seatOf s' x.twin = some (Sum.inr z.twin)) →
      SwappableIn s x → SwappableIn s' x := by
  intro s s' x hwf hwf' hclass hsx hstx htx httx hswap
  obtain ⟨π, hπ, -⟩ := sameOrbitSetoid.iseqv.symm hclass
  exact swappableIn_transfer_of_firstTouchRestart firstTouchRestart hwf hwf'
    hsx hstx htx httx hπ hswap

#print axioms firstTouchRestart
#print axioms fiber_transfer_corrected_of_lastReturn
