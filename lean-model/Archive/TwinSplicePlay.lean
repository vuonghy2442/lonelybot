import Orig2.TwinSpliceComm
import Orig2.TwinPointTransfer
import Orig2.TwinSpliceUnique

set_option linter.unusedSectionVars false

open State
open TwinSpliceComm

/-!
# Temp/TwinSplicePlay — the companion play hom and the point transfer

The step commutation `TwinSpliceComm.splice_step_comm_rev` has a
reversibility companion: a pair-free reversible letter stays
reversible after the run splice, at the relabeled mover.  The
companion assembles the play hom: a pair-free witness shuffle
`s → t` maps to an orbit `splice s ≃ splice t`, which is exactly the
point-hom hypothesis of `swappableIn_transfer_point_pairFree`.

Zero `sorry`, zero `Classical.choice`.
-/

/-! ## §1. Pair-free letters preserve the `.inr` seats -/

/-- A pair-free reversible letter keeps both twins' `.inr` seats
exactly; the mover-off rows and the one-point-edit rows supply the
per-letter preservation. -/
theorem seat_inr_of_pairFree_step {u v : State} {x : Card} {m : Move}
    (hwf : u.WF) (hstep : State.step u m = some v)
    (hrev : reversibleAtW u m) (hno : NotFoundPair x m)
    (hx : ∃ z, seatOf u x = some (Sum.inr z))
    (hxt : ∃ z : Card, seatOf u x.twin = some (Sum.inr z.twin)) :
    (∃ z, seatOf v x = some (Sum.inr z)) ∧
      (∃ z : Card, seatOf v x.twin = some (Sum.inr z.twin)) := by
  have hse_x : seatOf u x ≠ none := by
    obtain ⟨z, hz⟩ := hx
    rw [hz]
    simp
  have hse_xt : seatOf u x.twin ≠ none := by
    obtain ⟨z, hz⟩ := hxt
    rw [hz]
    simp
  have hxEq : seatOf v x = seatOf u x := by
    cases m with
    | draw => exact (chart_draw hstep).1 x
    | wasteToFound y => exact absurd hrev (wasteToFound_not_reversibleAtW u y)
    | wasteToTab y base => exact absurd hrev (wasteToTab_not_reversibleAtW u y base)
    | tabToFound y =>
        have hyx : y ≠ x := fun h => hno.1 (by rw [h])
        exact raise_seat_change_of_seated hstep hrev hse_x (Ne.symm hyx)
    | foundToTab y base =>
        have hyx : y ≠ x := fun h => hno.2.2.1 base (by rw [h])
        exact pull_seat_change hstep x (Ne.symm hyx)
    | tabToTab y base =>
        obtain ⟨hyx, -⟩ := tabToTab_mover_off hwf hx hxt hstep
        have h := tfc_seat_point_edit hwf hstep hrev x
        rwa [ite_eq_right (Ne.symm hyx)] at h
  have hxtEq : seatOf v x.twin = seatOf u x.twin := by
    cases m with
    | draw => exact (chart_draw hstep).1 x.twin
    | wasteToFound y => exact absurd hrev (wasteToFound_not_reversibleAtW u y)
    | wasteToTab y base => exact absurd hrev (wasteToTab_not_reversibleAtW u y base)
    | tabToFound y =>
        have hyt : y ≠ x.twin := fun h => hno.2.1 (by rw [h])
        exact raise_seat_change_of_seated hstep hrev hse_xt (Ne.symm hyt)
    | foundToTab y base =>
        have hyt : y ≠ x.twin := fun h => hno.2.2.2 base (by rw [h])
        exact pull_seat_change hstep x.twin (Ne.symm hyt)
    | tabToTab y base =>
        obtain ⟨-, hyt⟩ := tabToTab_mover_off hwf hx hxt hstep
        have h := tfc_seat_point_edit hwf hstep hrev x.twin
        rwa [ite_eq_right (Ne.symm hyt)] at h
  exact ⟨by rw [hxEq]; exact hx, by rw [hxtEq]; exact hxt⟩

/-! ## §2. The companion reversibility -/

/-- **The companion row** — a pair-free reversible letter stays
reversible after the run splice, at the relabeled mover. -/
theorem reversibleAtW_splice_relabelMover {s : State} {x : Card} {m : Move}
    (hwf : s.WF)
    (hx : ∃ z, seatOf s x = some (Sum.inr z))
    (hxt : ∃ z : Card, seatOf s x.twin = some (Sum.inr z.twin))
    (hrev : reversibleAtW s m) (hno : NotFoundPair x m) :
    reversibleAtW (s.spliceTwinRuns x) (Move.relabelMover x m) := by
  obtain ⟨a, b, _z, ha, hb, hab, _hza, _hzb⟩ := splice_setup hwf hx hxt
  cases m with
  | draw =>
      show reversibleAtW (s.spliceTwinRuns x) Move.draw
      have hwfS : (s.spliceTwinRuns x).WF := wf_spliceTwinRuns hwf hx hxt
      have hdrawR : drawR (s.spliceTwinRuns x) = drawR s := by
        unfold drawR
        rw [spliceTwinRuns_stock ha hb hab, spliceTwinRuns_waste ha hb hab,
          spliceTwinRuns_drawStep ha hb hab]
      have hR : drawR (s.spliceTwinRuns x) = true := by
        rw [hdrawR]
        exact (drawR_iff_reversibleAtW hwf).mpr hrev
      exact (drawR_iff_reversibleAtW hwfS).mp hR
  | wasteToFound y =>
      exact absurd hrev (wasteToFound_not_reversibleAtW s y)
  | wasteToTab y base =>
      exact absurd hrev (wasteToTab_not_reversibleAtW s y base)
  | tabToFound y =>
      have hnoI := (notFoundPair_iff_not_isPairFound x (Move.tabToFound y)).mp hno
      have hyx : y ≠ x := fun h => hnoI (Or.inl (by rw [h]))
      have hyt : y ≠ x.twin := fun h => hnoI (Or.inr (Or.inl (by rw [h])))
      have hrel : Move.relabelMover x (Move.tabToFound y) = Move.tabToFound y := by
        simp [Move.relabelMover, card_relabelTwin_ne hyx hyt]
      rw [hrel]
      exact reversibleAtW_splice_tabToFound hwf hx hxt ha hb hab hyx hyt hrev
  | foundToTab y base =>
      have hnoI := (notFoundPair_iff_not_isPairFound x (Move.foundToTab y base)).mp hno
      have hyx : y ≠ x := fun h => hnoI (Or.inr (Or.inr (Or.inl ⟨base, by rw [h]⟩)))
      have hyt : y ≠ x.twin :=
        fun h => hnoI (Or.inr (Or.inr (Or.inr ⟨base, by rw [h]⟩)))
      have hrel : Move.relabelMover x (Move.foundToTab y base) =
          Move.foundToTab y base := by
        simp [Move.relabelMover, card_relabelTwin_ne hyx hyt]
      rw [hrel]
      exact reversibleAtW_splice_foundToTab hwf hx hxt ha hb hab hrev
  | tabToTab y base =>
      obtain ⟨s₁, play, hstep, hrun⟩ := hrev
      obtain ⟨hyx, hyt⟩ := tabToTab_mover_off hwf hx hxt hstep
      have hrel : Move.relabelMover x (Move.tabToTab y base) = Move.tabToTab y base := by
        simp [Move.relabelMover, card_relabelTwin_ne hyx hyt]
      rw [hrel]
      exact reversibleAtW_splice_tabToTab hwf hx hxt ha hb hab hyx hyt
        ⟨s₁, play, hstep, hrun⟩

/-! ## §3. The play hom -/

/-- **The play hom** — a pair-free witness shuffle maps to an orbit of
the run splices. -/
theorem splice_play_hom {s t : State} {x : Card} {play : List Move}
    (hwf : s.WF)
    (hx : ∃ z, seatOf s x = some (Sum.inr z))
    (hxt : ∃ z : Card, seatOf s x.twin = some (Sum.inr z.twin))
    (hplay : ShufflePlayW s play t)
    (hno : ∀ m ∈ play, NotFoundPair x m) :
    sameOrbitSetoid.r (s.spliceTwinRuns x) (t.spliceTwinRuns x) := by
  revert hwf hx hxt hno
  induction hplay with
  | nil st =>
      intro _ _ _ _
      show RevEqW (st.spliceTwinRuns x) (st.spliceTwinRuns x)
      exact RevEqW_refl _
  | @cons st s₁ W m ρ hrev hstep hrest ih =>
      intro hwf hx hxt hno
      have hm : NotFoundPair x m := hno m (by simp)
      obtain ⟨hx₁, hxt₁⟩ :=
        seat_inr_of_pairFree_step hwf hstep hrev hm hx hxt
      have hwf₁ : s₁.WF := step_wf hwf hstep
      have hstepS : State.step (st.spliceTwinRuns x) (Move.relabelMover x m) =
          some (s₁.spliceTwinRuns x) :=
        splice_step_comm_rev hwf hx hxt hstep hrev hm
      have hrevS : reversibleAtW (st.spliceTwinRuns x) (Move.relabelMover x m) :=
        reversibleAtW_splice_relabelMover hwf hx hxt hrev hm
      have hstepEq : RevEqW (st.spliceTwinRuns x) (s₁.spliceTwinRuns x) :=
        shufflePlayW_revEqW
          (Walk.cons hrevS hstepS (Walk.nil (s₁.spliceTwinRuns x)))
      have ih' := ih hwf₁ hx₁ hxt₁
        (fun n hn => hno n (List.mem_cons_of_mem m hn))
      show RevEqW (W.spliceTwinRuns x) (st.spliceTwinRuns x)
      exact RevEqW_trans ih' (RevEqW_symm hstepEq)

/-! ## §4. The point transfer along a play -/

/-- **The play transfer** — `SwappableIn` transfers along a pair-free
witness play whose two run splices lie in one orbit. -/
theorem swappableIn_transfer_point_play
    {s t : State} {x : Card} {play : List Move}
    (hwf : s.WF) (hwf' : t.WF)
    (hxs : ∃ z, seatOf s x = some (Sum.inr z))
    (hxts : ∃ z : Card, seatOf s x.twin = some (Sum.inr z.twin))
    (hxt : ∃ z, seatOf t x = some (Sum.inr z))
    (hxtt : ∃ z : Card, seatOf t x.twin = some (Sum.inr z.twin))
    (hplay : ShufflePlayW s play t)
    (hno : ∀ m ∈ play, NotFoundPair x m)
    (hswap : SwappableIn s x) :
    SwappableIn t x :=
  swappableIn_transfer_point_pairFree hwf hwf' hxs hxts hxt hxtt hplay hno
    (splice_play_hom hwf hxs hxts hplay hno) hswap

/-! ## §5. Audit -/

#print axioms reversibleAtW_splice_relabelMover
#print axioms splice_play_hom
#print axioms swappableIn_transfer_point_play
