import Orig2.TwinPreludePath
import Orig2.TwinRecipeRiders
import Orig2.TwinBothCovered
import Orig2.TwinDrawTransfer
import Orig2.OrbitFactor
import Orig2.DetourKit
import Orig2.FiberTransferCapstonePrelude

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# Orig2.TwinPreludeFunctor — the run-splice naturality on the prelude grammar

The object map `F s = s.spliceTwinRuns x` is an involution.  The missing
half of the rider-general twin-flip functor is the morphism map: a
reversible play `s → s'` must induce a reversible play `F s → F s'`.

This card builds that map on the segmented grammar `PreludePath`: every
block's endpoint relation is already a `RevEqW` row.

* `pairFree` is `splice_play_hom`;
* `recipeTwin` / `recipeSelf` use the fact that the recipe endpoint is a
  strict swap, so `SwappableIn` holds at the source and transfers;
* `selfSwap` is definitionally a splice endpoint, and the splice is an
  involution;
* `trans` composes.

The top-level naturality for the full same-orbit relation is then
conditional on `PreludeNormalization` (`revEqW_splice_of_sameOrbit`),
because the draw-free board play still has to be segmented.  The
`SwappableIn` transfer is recovered as a corollary, reproducing the
Prelude capstone through the functor route.

Zero `sorry`, zero `Classical.choice`.
-/

open State

/-! ## §0. Anchors of the pair -/

/-- The two twins sit in distinct piles, so the run splice has the anchor
pair it expects. -/
private theorem splice_anchor_pair {u : State} {x : Card}
    (hwf : u.WF)
    (hx : ∃ z, seatOf u x = some (Sum.inr z))
    (hxt : ∃ z : Card, seatOf u x.twin = some (Sum.inr z.twin)) :
    ∃ a b : Anchor, u.pileHolding x = some a ∧
      u.pileHolding x.twin = some b ∧ a ≠ b := by
  obtain ⟨z, hz⟩ := hx
  obtain ⟨a, ha, -, -⟩ := tfc_seatOf_of_inr hz
  obtain ⟨zt, hzt⟩ := hxt
  obtain ⟨b, hb, -, -⟩ := tfc_seatOf_of_inr hzt
  refine ⟨a, b, ha, hb, ?_⟩
  intro hab
  rw [hab] at ha
  have hxmem : x ∈ (u.piles b).faceUp := pileHolding_mem ha
  have htmem : x.twin ∈ (u.piles b).faceUp := pileHolding_mem hb
  have heq : x = x.twin :=
    runOK_rank_distinct (hwf.runOK_of b) hxmem htmem rfl
  exact (card_twin_ne x) heq.symm

/-! ## §1. Target readiness along a prelude path -/

/-- A `PreludePath` from a ready source keeps the target ready. -/
theorem preludePath_target_wf_seats {x : Card} :
    ∀ {s s' : State} {play : List Move}, PreludePath x s play s' →
      s.WF →
      (∃ z, seatOf s x = some (Sum.inr z)) →
      (∃ z : Card, seatOf s x.twin = some (Sum.inr z.twin)) →
      s'.WF ∧ (∃ z, seatOf s' x = some (Sum.inr z)) ∧
        (∃ z : Card, seatOf s' x.twin = some (Sum.inr z.twin))
  | _, _, _, .nil _, hwf, hx, hxt => ⟨hwf, hx, hxt⟩
  | _, _, _, .pairFree hwf' _hxs _hxts hxu hxtu hplay _hno, _, _, _ =>
      ⟨run_wf hwf' (Walk_run _ hplay), hxu, hxtu⟩
  | _, _, _, .recipeTwin h, _, _, _ => by
      obtain ⟨hwfu, _hxu, _hxtu, hxw, hxtw, _z, _a, _hc, _hct, _hpa,
        _hraise, _hseg, hplay⟩ := h
      exact ⟨run_wf hwfu (Walk_run _ hplay), hxw, hxtw⟩
  | _, _, _, .recipeSelf h, _, _, _ => by
      obtain ⟨hwfu, _hxu, _hxtu, hxw, hxtw, _z, _a, _hc, _hct, _hpa,
        _hraise, _hseg, hplay⟩ := h
      exact ⟨run_wf hwfu (Walk_run _ hplay), hxw, hxtw⟩
  | _, _, _, @PreludePath.selfSwap _ u w seg h, _, _, _ => by
      obtain ⟨hwfu, hxu, hxtu, _hplay, hw⟩ := h
      obtain ⟨a, b, ha, hb, hab⟩ := splice_anchor_pair hwfu hxu hxtu
      have hxw : ∃ z, seatOf w x = some (Sum.inr z) := by
        obtain ⟨zt, hzt⟩ := hxtu
        refine ⟨zt.twin, ?_⟩
        rw [hw, seatOf_splice_self hwfu ha hb hab]
        exact hzt
      have hxtw : ∃ z : Card, seatOf w x.twin = some (Sum.inr z.twin) := by
        obtain ⟨z, hz⟩ := hxu
        refine ⟨z.twin, ?_⟩
        rw [hw, seatOf_splice_twin hwfu ha hb hab, hz, card_twin_twin]
      exact ⟨by rw [hw]; exact wf_spliceTwinRuns hwfu hxu hxtu, hxw, hxtw⟩
  | _, _, _, @PreludePath.trans _ s u v l₁ l₂ h₁ h₂, hwf, hx, hxt => by
      have hmid := preludePath_target_wf_seats h₁ hwf hx hxt
      exact preludePath_target_wf_seats h₂ hmid.1 hmid.2.1 hmid.2.2

/-! ## §2. Naturality on the prelude grammar -/

/-- **The functor square on `PreludePath`.**  Every prelude path lifts to
an orbit between the run splices of its endpoints. -/
theorem revEqW_splice_of_preludePath {x : Card} :
    ∀ {s s' : State} {play : List Move}, PreludePath x s play s' →
      s.WF →
      (∃ z, seatOf s x = some (Sum.inr z)) →
      (∃ z : Card, seatOf s x.twin = some (Sum.inr z.twin)) →
      RevEqW (s.spliceTwinRuns x) (s'.spliceTwinRuns x)
  | _, _, _, .nil _, _, _, _ => RevEqW_refl _
  | _, _, _, .pairFree hwf' hxs hxts _hxu _hxtu hplay hno, _, _, _ =>
      RevEqW_symm (splice_play_hom hwf' hxs hxts hplay hno)
  | _, _, _, @PreludePath.recipeTwin _ u w seg h, _, _, _ => by
      obtain ⟨hwfu, hxu, hxtu, hxw, hxtw, z, a, hc, hct, hpa, hraise,
        hseg, hplay⟩ := h
      have hwfw : w.WF := run_wf hwfu (Walk_run _ hplay)
      have hsu : SwappableIn u x :=
        swappableIn_of_twin_raise (c := x) (z := z) hwfu hc hct hraise
      rw [hseg] at hplay
      have hsw : SwappableIn w x :=
        (swappableIn_recipe_segment_riders hwfu hwfw hc hct hpa hraise hplay).mp hsu
      have hu : RevEqW (u.spliceTwinRuns x) u :=
        (swappableIn_iff_orbit_splice hwfu hxu hxtu).mp hsu
      have hw : RevEqW (w.spliceTwinRuns x) w :=
        (swappableIn_iff_orbit_splice hwfw hxw hxtw).mp hsw
      exact RevEqW_trans (RevEqW_trans hu (shufflePlayW_revEqW hplay))
        (RevEqW_symm hw)
  | _, _, _, @PreludePath.recipeSelf _ u w seg h, _, _, _ => by
      obtain ⟨hwfu, hxu, hxtu, hxw, hxtw, z, a, hc, hct, hpa, hraise,
        hseg, hplay⟩ := h
      have hwfw : w.WF := run_wf hwfu (Walk_run _ hplay)
      have hsuT : SwappableIn u x.twin :=
        swappableIn_of_twin_raise (c := x.twin) (z := z.twin) hwfu hct
          (by simpa [card_twin_twin] using hc)
          (by simpa [card_twin_twin] using hraise)
      have hsu : SwappableIn u x :=
        (TwinBothCovered.swappableIn_twin_comm (s := u) (x := x)).mpr hsuT
      rw [hseg] at hplay
      have hsw : SwappableIn w x :=
        (swappableIn_recipe_segment_riders_mirror hwfu hwfw hc hct hpa hraise hplay).mp hsu
      have hu : RevEqW (u.spliceTwinRuns x) u :=
        (swappableIn_iff_orbit_splice hwfu hxu hxtu).mp hsu
      have hw : RevEqW (w.spliceTwinRuns x) w :=
        (swappableIn_iff_orbit_splice hwfw hxw hxtw).mp hsw
      exact RevEqW_trans (RevEqW_trans hu (shufflePlayW_revEqW hplay))
        (RevEqW_symm hw)
  | _, _, _, @PreludePath.selfSwap _ u w seg h, _, _, _ => by
      obtain ⟨hwfu, hxu, hxtu, hplay, hw⟩ := h
      have huw : RevEqW u (u.spliceTwinRuns x) := by
        rw [← hw]
        exact shufflePlayW_revEqW hplay
      rw [hw]
      rw [spliceTwinRuns_invol hwfu hxu hxtu]
      exact RevEqW_symm huw
  | _, _, _, @PreludePath.trans _ s u v l₁ l₂ h₁ h₂, hwf, hx, hxt => by
      have hmid := preludePath_target_wf_seats h₁ hwf hx hxt
      exact RevEqW_trans
        (revEqW_splice_of_preludePath h₁ hwf hx hxt)
        (revEqW_splice_of_preludePath h₂ hmid.1 hmid.2.1 hmid.2.2)

/-! ## §3. Draws-only naturality -/

/-- A draws-only witness shuffle lifts to the run splices. -/
theorem revEqW_splice_of_drawPlayW {u v : State} {x : Card} {play : List Move}
    (h : DrawPlayW u play v) (hwf : u.WF)
    (hx : ∃ z, seatOf u x = some (Sum.inr z))
    (hxt : ∃ z : Card, seatOf u x.twin = some (Sum.inr z.twin)) :
    RevEqW (u.spliceTwinRuns x) (v.spliceTwinRuns x) := by
  obtain ⟨hplay, hdraw⟩ := h
  revert hwf hx hxt hdraw
  induction hplay with
  | nil st =>
      intro _ _ _ _
      exact RevEqW_refl _
  | @cons st mid stEnd m rest hrev hstep hrest ih =>
      intro hwf hx hxt hdraw
      have hm : m = Move.draw := hdraw m (by simp)
      subst hm
      obtain ⟨a, b, ha, hb, hab⟩ := splice_anchor_pair hwf hx hxt
      have hstepS : State.step (st.spliceTwinRuns x) Move.draw =
          some (mid.spliceTwinRuns x) :=
        TwinSpliceComm.stepDraw_splice ha hb hab hstep
      have hrevS : reversibleAtW (st.spliceTwinRuns x) Move.draw := by
        have hno : NotFoundPair x Move.draw := by simp [NotFoundPair]
        have h := reversibleAtW_splice_relabelMover hwf hx hxt hrev hno
        simpa [Move.relabelMover] using h
      have hstepEq : RevEqW (st.spliceTwinRuns x) (mid.spliceTwinRuns x) :=
        shufflePlayW_revEqW (Walk.cons hrevS hstepS (Walk.nil _))
      have hmidwf : mid.WF := step_wf hwf hstep
      have hxmid : ∃ z, seatOf mid x = some (Sum.inr z) := by
        obtain ⟨z, hz⟩ := hx
        exact ⟨z, ((chart_draw hstep).1 x).trans hz⟩
      have hxtmid : ∃ z : Card, seatOf mid x.twin = some (Sum.inr z.twin) := by
        obtain ⟨z, hz⟩ := hxt
        exact ⟨z, ((chart_draw hstep).1 x.twin).trans hz⟩
      have hdraw' : ∀ m' ∈ rest, m' = Move.draw :=
        fun m' hm' => hdraw m' (List.mem_cons_of_mem _ hm')
      exact RevEqW_trans hstepEq (ih hmidwf hxmid hxtmid hdraw')

/-! ## §4. Seats are constant along a draws-only play -/

/-- A draws-only witness play keeps every seat verbatim. -/
private theorem seatOf_drawPlayW {u v : State} {play : List Move}
    (h : ShufflePlayW u play v) (hdraw : ∀ m ∈ play, m = Move.draw)
    (c : Card) : seatOf v c = seatOf u c := by
  induction h with
  | nil s => rfl
  | @cons st mid stEnd m rest hrev hstep hrest ih =>
      have hm : m = Move.draw := hdraw m (List.mem_cons_self ..)
      subst hm
      have hmid : seatOf mid c = seatOf st c := (chart_draw hstep).1 c
      have htail : seatOf stEnd c = seatOf mid c :=
        ih (fun m' hm' => hdraw m' (List.mem_cons_of_mem _ hm'))
      exact htail.trans hmid

/-! ## §5. Naturality for a draw-free board play -/

/-- The functor square for a draw-free board play, conditional on the
prelude normalization of its endpoints. -/
theorem revEqW_splice_of_noDrawPlayW {s s' : State} {x : Card}
    (hnorm : PreludeNormalization x) (hwf : s.WF)
    (hx : ∃ z, seatOf s x = some (Sum.inr z))
    (hxt : ∃ z : Card, seatOf s x.twin = some (Sum.inr z.twin))
    (hx' : ∃ z, seatOf s' x = some (Sum.inr z))
    (hxt' : ∃ z : Card, seatOf s' x.twin = some (Sum.inr z.twin))
    (h : NoDrawPlayW s s') :
    RevEqW (s.spliceTwinRuns x) (s'.spliceTwinRuns x) := by
  obtain ⟨play, hpath⟩ := hnorm h hx hxt hx' hxt'
  exact revEqW_splice_of_preludePath hpath hwf hx hxt

/-! ## §6. Naturality for the full same-orbit relation -/

/-- **The functor square for `sameOrbitSetoid`, conditional on prelude
normalization.**  The orbit factor splits the class membership into a
draw-free board play and a draws-only rotation; the board play is
segmented by `PreludeNormalization`, and draws commute with the splice. -/
theorem revEqW_splice_of_sameOrbit {x : Card} (hnorm : PreludeNormalization x)
    {s s' : State} (hwf : s.WF) (hwf' : s'.WF)
    (hx : ∃ z, seatOf s x = some (Sum.inr z))
    (hxt : ∃ z : Card, seatOf s x.twin = some (Sum.inr z.twin))
    (hx' : ∃ z, seatOf s' x = some (Sum.inr z))
    (hxt' : ∃ z : Card, seatOf s' x.twin = some (Sum.inr z.twin))
    (hclass : sameOrbitSetoid.r s s') :
    RevEqW (s.spliceTwinRuns x) (s'.spliceTwinRuns x) := by
  obtain ⟨z, hnd, hrot⟩ := (sameOrbit_factor hwf hwf').mp hclass
  obtain ⟨σ, _τ, hσ, _hτ⟩ := hrot
  obtain ⟨hσW, hσdraw⟩ := hσ
  have hzwf : z.WF := by
    obtain ⟨p, hp, -, -⟩ := hnd
    exact run_wf hwf (Walk_run _ hp)
  have hzx : ∃ z', seatOf z x = some (Sum.inr z') := by
    obtain ⟨z', hz'⟩ := hx'
    exact ⟨z', (seatOf_drawPlayW hσW hσdraw x).symm.trans hz'⟩
  have hzxt : ∃ z' : Card, seatOf z x.twin = some (Sum.inr z'.twin) := by
    obtain ⟨z', hz'⟩ := hxt'
    exact ⟨z', (seatOf_drawPlayW hσW hσdraw x.twin).symm.trans hz'⟩
  have hboard : RevEqW (s.spliceTwinRuns x) (z.spliceTwinRuns x) :=
    revEqW_splice_of_noDrawPlayW hnorm hwf hx hxt hzx hzxt hnd
  have hdraws : RevEqW (z.spliceTwinRuns x) (s'.spliceTwinRuns x) :=
    revEqW_splice_of_drawPlayW ⟨hσW, hσdraw⟩ hzwf hzx hzxt
  exact RevEqW_trans hboard hdraws

/-! ## §7. The `SwappableIn` transfer through the functor -/

/-- **The non-king transfer via naturality.**  This is the functor route to
the Prelude capstone's non-king arm: the chain is
`s' ~ s ~ splice(s) ~ splice(s')`, with the middle naturality supplied by
`revEqW_splice_of_sameOrbit`. -/
theorem swappableIn_transfer_nonKing_viaFunctor {s s' : State} {x : Card}
    (hnorm : PreludeNormalization x)
    (hwf : s.WF) (hwf' : s'.WF)
    (hclass : sameOrbitSetoid.r s s')
    (_hfound : s.found = s'.found)
    (hx : ∃ z, seatOf s x = some (Sum.inr z))
    (hxt : ∃ z : Card, seatOf s x.twin = some (Sum.inr z.twin))
    (hx' : ∃ z, seatOf s' x = some (Sum.inr z))
    (hxt' : ∃ z : Card, seatOf s' x.twin = some (Sum.inr z.twin))
    (hswap : SwappableIn s x) :
    SwappableIn s' x := by
  have hnat : RevEqW (s.spliceTwinRuns x) (s'.spliceTwinRuns x) :=
    revEqW_splice_of_sameOrbit hnorm hwf hwf' hx hxt hx' hxt' hclass
  have hs : RevEqW (s.spliceTwinRuns x) s :=
    (swappableIn_iff_orbit_splice hwf hx hxt).mp hswap
  have hs' : RevEqW (s'.spliceTwinRuns x) s' :=
    RevEqW_trans (RevEqW_trans (RevEqW_symm hnat) hs) (RevEqW_symm hclass)
  exact (swappableIn_iff_orbit_splice hwf' hx' hxt').mpr hs'

/-! ## §8. The WF-gated normalization target and its first reduction -/

/-- **`PreludeNormalizationWF x`** — the provable form of the prelude
normalization.  The source readiness `s.WF` is supplied by the consumer
(the capstone always has it); without it the unrestricted
`PreludeNormalization` is not provable, because every non-`nil`
`PreludePath` constructor demands `WF` at its source. -/
def PreludeNormalizationWF (x : Card) : Prop :=
  ∀ {s s' : State}, s.WF → NoDrawPlayW s s' →
    (∃ z, seatOf s x = some (Sum.inr z)) →
    (∃ z : Card, seatOf s x.twin = some (Sum.inr z.twin)) →
    (∃ z, seatOf s' x = some (Sum.inr z)) →
    (∃ z : Card, seatOf s' x.twin = some (Sum.inr z.twin)) →
    ∃ play : List Move, PreludePath x s play s'

/-- **`PairFoundNormalization x`** — the residue of the normalization
after stripping an arbitrary pair-free prefix.  Every no-draw play whose
**first** move is pair-foundation must be segmentable. -/
def PairFoundNormalization (x : Card) : Prop :=
  ∀ {u v : State}, u.WF →
    (∃ z, seatOf u x = some (Sum.inr z)) →
    (∃ z : Card, seatOf u x.twin = some (Sum.inr z.twin)) →
    (∃ z, seatOf v x = some (Sum.inr z)) →
    (∃ z : Card, seatOf v x.twin = some (Sum.inr z.twin)) →
    ∀ {m : Move} {post : List Move}, IsPairFound x m →
      ShufflePlayW u (m :: post) v →
      (∀ n ∈ m :: post, n ≠ Move.draw) →
      ∃ play : List Move, PreludePath x u play v

/-- **`FirstRaiseNormalization x`** — the residue after the first-letter
analysis: every no-draw play whose first move raises one of the twins. -/
def FirstRaiseNormalization (x : Card) : Prop :=
  ∀ {u v : State}, u.WF →
    (∃ z, seatOf u x = some (Sum.inr z)) →
    (∃ z : Card, seatOf u x.twin = some (Sum.inr z.twin)) →
    (∃ z, seatOf v x = some (Sum.inr z)) →
    (∃ z : Card, seatOf v x.twin = some (Sum.inr z.twin)) →
    ∀ {m : Move} {post : List Move},
      (m = Move.tabToFound x ∨ m = Move.tabToFound x.twin) →
      ShufflePlayW u (m :: post) v →
      (∀ n ∈ m :: post, n ≠ Move.draw) →
      ∃ play : List Move, PreludePath x u play v

/-- **The first pair-foundation letter is a raise.**  From a state with both
twins on `.inr` parents, neither `foundToTab x _` nor `foundToTab x.twin _`
can fire: the mover would have to be on the foundation, hence off the
tableau, contradicting its `.inr` seat. -/
theorem pairFound_first_move_raise {u u1 : State} {x : Card} {m : Move}
    (hwf : u.WF)
    (hx : ∃ z, seatOf u x = some (Sum.inr z))
    (hxt : ∃ z : Card, seatOf u x.twin = some (Sum.inr z.twin))
    (hm : IsPairFound x m)
    (hstep : State.step u m = some u1) :
    m = Move.tabToFound x ∨ m = Move.tabToFound x.twin := by
  rcases hm with rfl | rfl | ⟨b, rfl⟩ | ⟨b, rfl⟩
  · exact Or.inl rfl
  · exact Or.inr rfl
  · obtain ⟨c', htop, hc', _hcp, _hs⟩ := step_foundToTab_inv hstep
    have hlast : lastOf (u.found x.suit) = some x := by
      simpa [State.foundTop, hc'] using htop
    have hxmem : x ∈ u.found x.suit := lastOf_mem hlast
    have hhold : u.pileHolding x = none := by
      by_cases hh : u.pileHolding x = none
      · exact hh
      · obtain ⟨a, ha⟩ := option_some_of_ne_none hh
        exfalso
        have hnot : x ∉ (u.piles a).faceUp :=
          ((mem_found_unique hwf hxmem).1 a).2
        exact hnot (pileHolding_mem ha)
    have hseat : seatOf u x = none := tfc_seatOf_none hhold
    obtain ⟨z, hz⟩ := hx
    rw [hseat] at hz
    cases hz
  · obtain ⟨c', htop, hc', _hcp, _hs⟩ := step_foundToTab_inv hstep
    have hlast : lastOf (u.found x.twin.suit) = some x.twin := by
      simpa [State.foundTop, hc'] using htop
    have hmem : x.twin ∈ u.found x.twin.suit := lastOf_mem hlast
    have hhold : u.pileHolding x.twin = none := by
      by_cases hh : u.pileHolding x.twin = none
      · exact hh
      · obtain ⟨a, ha⟩ := option_some_of_ne_none hh
        exfalso
        have hnot : x.twin ∉ (u.piles a).faceUp :=
          ((mem_found_unique hwf hmem).1 a).2
        exact hnot (pileHolding_mem ha)
    have hseat : seatOf u x.twin = none := tfc_seatOf_none hhold
    obtain ⟨z, hz⟩ := hxt
    rw [hseat] at hz
    cases hz

/-- **The first reduction, sharpened.**  It suffices to normalize plays whose
first letter is a raise. -/
theorem pairFoundNormalization_of_firstRaise
    (h : FirstRaiseNormalization x) : PairFoundNormalization x := by
  intro u v hwf hxu hxtu hxv hxtv m post hm hplay hnd
  cases hplay with
  | cons hrev hstep hrest =>
      exact h hwf hxu hxtu hxv hxtv
        (pairFound_first_move_raise hwf hxu hxtu hm hstep)
        (Walk.cons hrev hstep hrest) hnd

/-- **Forced pull targets.**  Once `x` sits on a card parent `z`, every
card-parent base that legally accepts `x` is `z` or its twin.  This is the
fitting-parent arithmetic `tfc_fitting_parent`. -/
theorem canSitOn_target_eq_parent_or_twin {u : State} {x z v : Card}
    (hwf : u.WF)
    (hx : seatOf u x = some (Sum.inr z))
    (hv : canSitOn x v = true) :
    v = z ∨ v = z.twin := by
  obtain ⟨a, hhold, -, hlast⟩ := tfc_seatOf_of_inr hx
  have hz : canSitOn x z = true := (tfc_seat_parent hwf hhold hlast).1
  exact tfc_fitting_parent hv hz

/-- **Forced twin parents.**  If the twin is `.inr`-seated on `z.twin` at
`u` and again `.inr`-seated at `v`, its new parent is `z.twin` or `z`. -/
theorem twin_parent_eq_old_or_twin {u v : State} {x z w : Card}
    (hwf : u.WF) (hwf' : v.WF)
    (hu : seatOf u x.twin = some (Sum.inr z.twin))
    (hv : seatOf v x.twin = some (Sum.inr w)) :
    w = z.twin ∨ w = z := by
  obtain ⟨a, hhold, -, hlast⟩ := tfc_seatOf_of_inr hu
  have hz : canSitOn x.twin z.twin = true := (tfc_seat_parent hwf hhold hlast).1
  obtain ⟨a', hhold', -, hlast'⟩ := tfc_seatOf_of_inr hv
  have hw : canSitOn x.twin w = true := (tfc_seat_parent hwf' hhold' hlast').1
  rcases tfc_fitting_parent hw hz with h | h
  · exact Or.inl h
  · exact Or.inr (by simpa [card_twin_twin] using h)

/-- **Endpoint parent invariance.**  If `x` sits on the card parent `z`
at one `WF` both-seated state and on the card parent `w` at another,
then `w` is `z` or `z.twin` — regardless of the play between them.  Two
`canSitOn` facts plus `tfc_fitting_parent` suffice. -/
theorem endpoint_parent_eq_initial_or_twin {u v : State} {x z w : Card}
    (hwf : u.WF)
    (hx : seatOf u x = some (Sum.inr z))
    (hwf' : v.WF)
    (hv : seatOf v x = some (Sum.inr w)) :
    w = z ∨ w = z.twin := by
  obtain ⟨a, hhold, -, hlast⟩ := tfc_seatOf_of_inr hv
  have hw : canSitOn x w = true := (tfc_seat_parent hwf' hhold hlast).1
  exact canSitOn_target_eq_parent_or_twin hwf hx hw

/-- The twin-left fitting law, copied from the seam-private rows: the
mover's suit twin does not change the pile-fit predicate. -/
private theorem canSitOn_twin_left' (c b : Card) :
    canSitOn c.twin b = canSitOn c b := by
  rcases c with ⟨s, r⟩
  rcases b with ⟨s', r'⟩
  cases s <;> cases s' <;> rfl

/-- Two distinct twins cannot share the same direct parent: both would sit
at the same successor position in one legal run, contradicting the strict
rank descent. -/
private theorem not_twin_same_parent {u : State} {x z : Card}
    (hwf : u.WF)
    (hx : seatOf u x = some (Sum.inr z))
    (hxt : seatOf u x.twin = some (Sum.inr z)) : False := by
  obtain ⟨a, hhold, -, hlast⟩ := tfc_seatOf_of_inr hx
  obtain ⟨a', hhold', -, hlast'⟩ := tfc_seatOf_of_inr hxt
  have hz_a : z ∈ (u.piles a).faceUp := mem_below _ (lastOf_mem hlast)
  have hz_a' : z ∈ (u.piles a').faceUp := mem_below _ (lastOf_mem hlast')
  have haa' : a = a' := by
    by_cases h : a = a'
    · exact h
    · exact absurd hz_a'
        ((mem_faceUp_unique hwf hz_a a' (fun hh => h hh.symm)).1)
  have hxmem : x ∈ (u.piles a).faceUp := pileHolding_mem hhold
  have htmem : x.twin ∈ (u.piles a).faceUp := by
    simpa [haa'] using pileHolding_mem hhold'
  have heq : x = x.twin :=
    runOK_rank_distinct (hwf.runOK_of a) hxmem htmem (by rfl)
  exact (card_twin_ne x) heq.symm

/-- **The two parent witnesses align.**  If `x` is on `z` and `x.twin` is
on `zt.twin`, then `zt = z`: the only other fitting parent is the twin of
the first, and the same-parent alternative is impossible. -/
theorem twin_parent_eq_of_seats {u : State} {x z zt : Card}
    (hwf : u.WF)
    (hx : seatOf u x = some (Sum.inr z))
    (hxt : seatOf u x.twin = some (Sum.inr zt.twin)) :
    zt = z := by
  have hz : canSitOn x z = true := by
    obtain ⟨a, hhold, -, hlast⟩ := tfc_seatOf_of_inr hx
    exact (tfc_seat_parent hwf hhold hlast).1
  have hzt : canSitOn x zt.twin = true := by
    obtain ⟨a, hhold, -, hlast⟩ := tfc_seatOf_of_inr hxt
    have h := (tfc_seat_parent hwf hhold hlast).1
    simpa [canSitOn_twin_left'] using h
  rcases tfc_fitting_parent hzt hz with h | h
  · exfalso
    exact not_twin_same_parent hwf hx (by simpa [h] using hxt)
  · have := congrArg Card.twin h
    simpa [card_twin_twin] using this

/-- **The endpoint configuration is identity or swapped.**  At any two
both-`.inr` `WF` states, the two twins occupy the same twin-parent pair
`{z, z.twin}`, so the only possibilities at the endpoint are
`(x@z, twin@z.twin)` or `(x@z.twin, twin@z)`. -/
theorem endpoint_config_identity_or_swap {u v : State} {x z w w' : Card}
    (hwf : u.WF)
    (hx : seatOf u x = some (Sum.inr z))
    (hxt : seatOf u x.twin = some (Sum.inr z.twin))
    (hwf' : v.WF)
    (hx' : seatOf v x = some (Sum.inr w))
    (hxt' : seatOf v x.twin = some (Sum.inr w')) :
    (w = z ∧ w' = z.twin) ∨ (w = z.twin ∧ w' = z) := by
  have hw : w = z ∨ w = z.twin :=
    endpoint_parent_eq_initial_or_twin hwf hx hwf' hx'
  have hwt : w' = z.twin ∨ w' = z := by
    simpa [card_twin_twin] using
      endpoint_parent_eq_initial_or_twin hwf hxt hwf' hxt'
  have hne : w ≠ w' := by
    intro hww
    exact not_twin_same_parent hwf'
      (by simpa [hww] using hx') (by simpa [hww] using hxt')
  rcases hw with rfl | rfl
  · rcases hwt with hwt' | hwt'
    · exact Or.inl ⟨rfl, hwt'⟩
    · exact absurd hwt'.symm hne
  · rcases hwt with hwt' | hwt'
    · exact absurd hwt'.symm hne
    · exact Or.inr ⟨rfl, hwt'⟩

/-- **Every first raise yields a `SelfSwapSeg` block.**  A reversible
raise of either twin gives `SwappableIn u x`; uniqueness then identifies
the strict target with the run splice, and the orbit witness supplies the
segment play.  In particular the exact 3-leg recipe play need not be
constructed. -/
theorem selfSwapSeg_of_raise {u : State} {x z : Card}
    (hwf : u.WF)
    (hx : seatOf u x = some (Sum.inr z))
    (hxt : seatOf u x.twin = some (Sum.inr z.twin))
    (hraise : reversibleAtW u (Move.tabToFound x) ∨
      reversibleAtW u (Move.tabToFound x.twin)) :
    ∃ seg w, SelfSwapSeg x u w seg := by
  have hswap : SwappableIn u x := by
    rcases hraise with hr | hr
    · have hsuT : SwappableIn u x.twin :=
        swappableIn_of_twin_raise (c := x.twin) (z := z.twin) hwf hxt
          (by simpa [card_twin_twin] using hx)
          (by simpa [card_twin_twin] using hr)
      exact (TwinBothCovered.swappableIn_twin_comm (s := u) (x := x)).mpr hsuT
    · exact swappableIn_of_twin_raise (c := x) (z := z) hwf hx hxt hr
  obtain ⟨w, hstrict, horb⟩ := hswap
  obtain ⟨σ, hσ, τ, hτ⟩ := horb
  have hwwf : w.WF := run_wf hwf (Walk_run _ hτ)
  have hw_eq : w = u.spliceTwinRuns x :=
    eq_splice_of_twinPairSwapStrict hwf hwwf ⟨z, hx⟩ ⟨z, hxt⟩ hstrict
  exact ⟨τ, w, hwf, ⟨z, hx⟩, ⟨z, hxt⟩, hτ, hw_eq⟩

/-- Splitting a witness walk at a list prefix. -/
private theorem walk_split {P : State → Move → Prop} :
    ∀ {s s' : State} {A B : List Move},
      Walk P s (A ++ B) s' → ∃ u, Walk P s A u ∧ Walk P u B s' := by
  intro s s' A B
  induction A generalizing s with
  | nil =>
      intro h
      exact ⟨s, .nil s, by simpa using h⟩
  | cons m rest ih =>
      intro h
      cases h with
      | cons hlet hstep hrest =>
          obtain ⟨u, hA, hB⟩ := ih hrest
          exact ⟨u, .cons hlet hstep hA, hB⟩

/-- A pair-free witness shuffle keeps both twins `.inr`-seated at its
landing.  Private copy of the exact-recipe card's row. -/
private theorem seats_of_pairFree_play {x : Card} (seg : List Move) :
    ∀ {s u : State}, s.WF → ShufflePlayW s seg u →
      (∀ m ∈ seg, NotFoundPair x m) →
      (∃ z, seatOf s x = some (Sum.inr z)) →
      (∃ z : Card, seatOf s x.twin = some (Sum.inr z.twin)) →
      (∃ z, seatOf u x = some (Sum.inr z)) ∧
        (∃ z : Card, seatOf u x.twin = some (Sum.inr z.twin)) := by
  induction seg with
  | nil =>
      intro s u _ hplay _ hx hxt
      cases hplay
      exact ⟨hx, hxt⟩
  | cons m rest ih =>
      intro s u hwf hplay hno hx hxt
      cases hplay with
      | cons hrev hstep hrest =>
          have hm : NotFoundPair x m := hno m (by simp)
          obtain ⟨hx₁, hxt₁⟩ :=
            seat_inr_of_pairFree_step hwf hstep hrev hm hx hxt
          have hwf₁ := step_wf hwf hstep
          exact ih hwf₁ hrest
            (fun n hn => hno n (List.mem_cons_of_mem m hn)) hx₁ hxt₁

/-- **The first reduction of the normalization obligation.**  It suffices
to normalize plays whose first move is pair-foundation: an arbitrary
no-draw play either is pair-free (then it is a `pairFree` segment), or it
splits into a pair-free prefix and a pair-foundation-headed suffix. -/
theorem preludeNormalizationWF_of_pairFound (hpf : PairFoundNormalization x) :
    PreludeNormalizationWF x := by
  intro s s' hwf hnd hxs hxts hxs' hxts'
  obtain ⟨play, hplay, hndraw, _back, _hback, _hbndraw⟩ := hnd
  rcases exists_pairFound_split x play with hno | ⟨pre, m, post, rfl, hm, hnopre⟩
  · have hno' : ∀ m ∈ play, NotFoundPair x m :=
      fun m hm => (notFoundPair_iff_not_isPairFound x m).mpr (hno m hm)
    obtain ⟨hxu, hxtu⟩ := seats_of_pairFree_play play hwf hplay hno' hxs hxts
    exact ⟨play, PreludePath.pairFree hwf hxs hxts hxu hxtu hplay hno'⟩
  · have hnopre' : ∀ m ∈ pre, NotFoundPair x m :=
      fun m hm => (notFoundPair_iff_not_isPairFound x m).mpr (hnopre m hm)
    obtain ⟨u, hpre, hrest⟩ := walk_split hplay
    have huwf : u.WF := run_wf hwf (Walk_run _ hpre)
    obtain ⟨hxu, hxtu⟩ := seats_of_pairFree_play pre hwf hpre hnopre' hxs hxts
    have hndraw' : ∀ n ∈ m :: post, n ≠ Move.draw := by
      intro n hn
      exact hndraw n (List.mem_append_right (as := pre) hn)
    obtain ⟨suf, hpath⟩ := hpf huwf hxu hxtu hxs' hxts' hm hrest hndraw'
    exact ⟨pre ++ suf,
      PreludePath.trans (PreludePath.pairFree hwf hxs hxts hxu hxtu hpre hnopre') hpath⟩

/-! ### §8.1. The functor square at the WF-gated hypothesis -/

/-- The board-play square from `PreludeNormalizationWF`. -/
theorem revEqW_splice_of_noDrawPlayW_WF {s s' : State} {x : Card}
    (hnorm : PreludeNormalizationWF x) (hwf : s.WF)
    (hx : ∃ z, seatOf s x = some (Sum.inr z))
    (hxt : ∃ z : Card, seatOf s x.twin = some (Sum.inr z.twin))
    (hx' : ∃ z, seatOf s' x = some (Sum.inr z))
    (hxt' : ∃ z : Card, seatOf s' x.twin = some (Sum.inr z.twin))
    (h : NoDrawPlayW s s') :
    RevEqW (s.spliceTwinRuns x) (s'.spliceTwinRuns x) := by
  obtain ⟨play, hpath⟩ := hnorm hwf h hx hxt hx' hxt'
  exact revEqW_splice_of_preludePath hpath hwf hx hxt

/-- The same-orbit square from `PreludeNormalizationWF`. -/
theorem revEqW_splice_of_sameOrbit_WF {x : Card}
    (hnorm : PreludeNormalizationWF x)
    {s s' : State} (hwf : s.WF) (hwf' : s'.WF)
    (hx : ∃ z, seatOf s x = some (Sum.inr z))
    (hxt : ∃ z : Card, seatOf s x.twin = some (Sum.inr z.twin))
    (hx' : ∃ z, seatOf s' x = some (Sum.inr z))
    (hxt' : ∃ z : Card, seatOf s' x.twin = some (Sum.inr z.twin))
    (hclass : sameOrbitSetoid.r s s') :
    RevEqW (s.spliceTwinRuns x) (s'.spliceTwinRuns x) := by
  obtain ⟨z, hnd, hrot⟩ := (sameOrbit_factor hwf hwf').mp hclass
  obtain ⟨σ, _τ, hσ, _hτ⟩ := hrot
  obtain ⟨hσW, hσdraw⟩ := hσ
  have hzwf : z.WF := by
    obtain ⟨p, hp, -, -⟩ := hnd
    exact run_wf hwf (Walk_run _ hp)
  have hzx : ∃ z', seatOf z x = some (Sum.inr z') := by
    obtain ⟨z', hz'⟩ := hx'
    exact ⟨z', (seatOf_drawPlayW hσW hσdraw x).symm.trans hz'⟩
  have hzxt : ∃ z' : Card, seatOf z x.twin = some (Sum.inr z'.twin) := by
    obtain ⟨z', hz'⟩ := hxt'
    exact ⟨z', (seatOf_drawPlayW hσW hσdraw x.twin).symm.trans hz'⟩
  have hboard : RevEqW (s.spliceTwinRuns x) (z.spliceTwinRuns x) :=
    revEqW_splice_of_noDrawPlayW_WF hnorm hwf hx hxt hzx hzxt hnd
  have hdraws : RevEqW (z.spliceTwinRuns x) (s'.spliceTwinRuns x) :=
    revEqW_splice_of_drawPlayW ⟨hσW, hσdraw⟩ hzwf hzx hzxt
  exact RevEqW_trans hboard hdraws

/-- The `SwappableIn` transfer from the WF-gated normalization. -/
theorem swappableIn_transfer_nonKing_viaFunctor_WF {s s' : State} {x : Card}
    (hnorm : PreludeNormalizationWF x)
    (hwf : s.WF) (hwf' : s'.WF)
    (hclass : sameOrbitSetoid.r s s')
    (_hfound : s.found = s'.found)
    (hx : ∃ z, seatOf s x = some (Sum.inr z))
    (hxt : ∃ z : Card, seatOf s x.twin = some (Sum.inr z.twin))
    (hx' : ∃ z, seatOf s' x = some (Sum.inr z))
    (hxt' : ∃ z : Card, seatOf s' x.twin = some (Sum.inr z.twin))
    (hswap : SwappableIn s x) :
    SwappableIn s' x := by
  have hnat : RevEqW (s.spliceTwinRuns x) (s'.spliceTwinRuns x) :=
    revEqW_splice_of_sameOrbit_WF hnorm hwf hwf' hx hxt hx' hxt' hclass
  have hs : RevEqW (s.spliceTwinRuns x) s :=
    (swappableIn_iff_orbit_splice hwf hx hxt).mp hswap
  have hs' : RevEqW (s'.spliceTwinRuns x) s' :=
    RevEqW_trans (RevEqW_trans (RevEqW_symm hnat) hs) (RevEqW_symm hclass)
  exact (swappableIn_iff_orbit_splice hwf' hx' hxt').mpr hs'

/-- **The full fiber transfer via the functor, conditional on the
WF-gated normalization.**  Same dispatch as
`fiber_transfer_corrected_of_preludeNormalization`; the non-king arm is
the naturality chain, the king arm is the capstone's unconditional
`swappableIn_transfer_king`. -/
theorem fiber_transfer_corrected_viaFunctor
    (hnorm : ∀ x : Card, PreludeNormalizationWF x)
    {s s' : State} (hwf : s.WF) (hwf' : s'.WF) {x : Card}
    (hclass : sameOrbitSetoid.r s s') (hfound : s.found = s'.found)
    (hswap : SwappableIn s x) (hdata : FiberSeatData s s' x) :
    SwappableIn s' x := by
  by_cases hking : x.rank = Rank.king
  · rcases hdata with ⟨hnk, -⟩ |
      ⟨-, ⟨a, a', hx, hxt, hne, hhidA, hhidB⟩, b, b', hx', hxt', hne', hfa, hha, hfb, hhb⟩
    · exact absurd hking hnk
    · exact swappableIn_transfer_king hwf hwf' hclass hking
        hx hxt hne hhidA hhidB hx' hxt' hne' ⟨hfa, hha⟩ ⟨hfb, hhb⟩ hswap
  · rcases hdata with ⟨-, hxs, hxts, hxs', hxts'⟩ | ⟨hking', -⟩
    · exact swappableIn_transfer_nonKing_viaFunctor_WF (hnorm x) hwf hwf'
        hclass hfound hxs hxts hxs' hxts' hswap
    · exact absurd hking' hking

/-- Pair-free forward reachability, the relation consumed by the endpoint
classification. -/
def PairFreeReach (x : Card) (u v : State) : Prop :=
  ∃ play : List Move, ShufflePlayW u play v ∧ ∀ m ∈ play, NotFoundPair x m

/-- **Assembly of `FirstRaiseNormalization` from the two remaining rows.**
`hclass` is the pair-free endpoint classification, `hrev` is pair-free
reversal.  The first raise supplies a `SelfSwapSeg` block to the splice;
the classification says the endpoint is pair-free-reachable from the
source (identity) or from the splice (exchange); reversal orients the
pair-free leg for the `PreludePath` concatenation. -/
theorem firstRaiseNormalization_of_pairFreeClass {x : Card}
    (hclass : ∀ {u v : State} {z : Card} {play : List Move},
      u.WF →
      seatOf u x = some (Sum.inr z) →
      seatOf u x.twin = some (Sum.inr z.twin) →
      ShufflePlayW u play v →
      (∃ w, seatOf v x = some (Sum.inr w)) →
      (∃ w' : Card, seatOf v x.twin = some (Sum.inr w'.twin)) →
      PairFreeReach x v u ∨ PairFreeReach x v (u.spliceTwinRuns x))
    (hrev : ∀ {s t : State} {z : Card} {play : List Move},
      s.WF →
      seatOf s x = some (Sum.inr z) →
      seatOf s x.twin = some (Sum.inr z.twin) →
      ShufflePlayW s play t →
      (∀ m ∈ play, NotFoundPair x m) →
      PairFreeReach x t s) :
    FirstRaiseNormalization x := by
  intro u v hwf hxu hxtu hxv hxtv m post hm hplay _hnd
  obtain ⟨z, hz⟩ := hxu
  obtain ⟨zt, hzt⟩ := hxtu
  have hztz : zt = z := twin_parent_eq_of_seats hwf hz hzt
  have hzt' : seatOf u x.twin = some (Sum.inr z.twin) := by
    simpa [hztz] using hzt
  have hvWF : v.WF := run_wf hwf (Walk_run _ hplay)
  obtain ⟨w, hw⟩ := hxv
  obtain ⟨wt, hwt⟩ := hxtv
  have hwtw : wt = w := twin_parent_eq_of_seats hvWF hw hwt
  have hwt' : seatOf v x.twin = some (Sum.inr w.twin) := by
    simpa [hwtw] using hwt
  rcases hclass hwf hz hzt' hplay ⟨w, hw⟩ ⟨w, hwt'⟩ with hleft | hright
  · obtain ⟨π, hπ, hno⟩ := hleft
    obtain ⟨σ, hσ, hnoσ⟩ := hrev hvWF hw hwt' hπ hno
    exact ⟨σ, PreludePath.pairFree hwf ⟨z, hz⟩ ⟨z, hzt'⟩
      ⟨w, hw⟩ ⟨w, hwt'⟩ hσ hnoσ⟩
  · obtain ⟨π, hπ, hno⟩ := hright
    obtain ⟨ρ, hρ, hnoρ⟩ := hrev hvWF hw hwt' hπ hno
    have hraise : reversibleAtW u (Move.tabToFound x) ∨
        reversibleAtW u (Move.tabToFound x.twin) := by
      cases hplay with
      | cons hrevStep hstep hrest =>
          rcases hm with h | h
          · rw [h] at hrevStep; exact Or.inl hrevStep
          · rw [h] at hrevStep; exact Or.inr hrevStep
    obtain ⟨seg, ws, hself⟩ := selfSwapSeg_of_raise hwf hz hzt' hraise
    have hsu_eq : ws = u.spliceTwinRuns x := hself.2.2.2.2
    rw [← hsu_eq] at hρ
    obtain ⟨a, b, ha, hb, hab⟩ := splice_anchor_pair hwf ⟨z, hz⟩ ⟨z, hzt'⟩
    have hswf : ws.WF := by
      rw [hsu_eq]
      exact wf_spliceTwinRuns hwf ⟨z, hz⟩ ⟨z, hzt'⟩
    have hsx : ∃ z', seatOf ws x = some (Sum.inr z') := by
      refine ⟨z.twin, ?_⟩
      rw [hsu_eq, seatOf_splice_self hwf ha hb hab]
      exact hzt'
    have hsxt : ∃ z' : Card, seatOf ws x.twin = some (Sum.inr z'.twin) := by
      refine ⟨z.twin, ?_⟩
      rw [hsu_eq, seatOf_splice_twin hwf ha hb hab, hz, card_twin_twin]
    exact ⟨seg ++ ρ, PreludePath.trans (PreludePath.selfSwap hself)
      (PreludePath.pairFree hswf hsx hsxt ⟨w, hw⟩ ⟨w, hwt'⟩ hρ hnoρ)⟩

/-! ## §9. Audit -/

#print axioms preludePath_target_wf_seats
#print axioms revEqW_splice_of_preludePath
#print axioms revEqW_splice_of_drawPlayW
#print axioms revEqW_splice_of_noDrawPlayW
#print axioms revEqW_splice_of_sameOrbit
#print axioms swappableIn_transfer_nonKing_viaFunctor
#print axioms pairFound_first_move_raise
#print axioms pairFoundNormalization_of_firstRaise
#print axioms canSitOn_target_eq_parent_or_twin
#print axioms twin_parent_eq_old_or_twin
#print axioms endpoint_parent_eq_initial_or_twin
#print axioms endpoint_config_identity_or_swap
#print axioms selfSwapSeg_of_raise
#print axioms twin_parent_eq_of_seats
#print axioms firstRaiseNormalization_of_pairFreeClass
#print axioms preludeNormalizationWF_of_pairFound
#print axioms revEqW_splice_of_noDrawPlayW_WF
#print axioms revEqW_splice_of_sameOrbit_WF
#print axioms swappableIn_transfer_nonKing_viaFunctor_WF
#print axioms fiber_transfer_corrected_viaFunctor



