import Orig2.SeatMateStack
import Orig2.TwinRelabel

/-!
# Orig2.TwinDrawTransfer — draws commute with the strict twin swap

The draw letter reads only the draw zone (`stock`, `waste`, `drawStep`)
and inherits the board (`piles`, `found`) from its source.  The strict
twin swap fixes exactly those readouts (the board's hidden decks and
deal quantum through `boardFixed`, the foundations through
`foundsFixed`, and the pool through its stock/waste clauses), and
exchanges the pair's two seats.  Therefore a draw at `s` mirrors to a
draw at `v`, the two successors remain strictly twin-swapped, a whole
draws-only play transports, and `SwappableIn` is invariant across the
`SWRotW` draw-rotation phase.

House compliance: additive temp card; zero `sorry`, zero
`Classical.choice`.
-/

/-! ## §1. The draw-zone congruence (the Dominance kit, restated) -/

/-- The recycle's branch catalogue. -/
private theorem recycle_fields (x : State) :
    (x.stock = [] → x.waste = [] → State.recycle x = x) ∧
    (x.stock = [] → x.waste ≠ [] →
      State.recycle x = { x with stock := x.waste.reverse, waste := [] }) ∧
    (x.stock ≠ [] → State.recycle x = x) := by
  refine ⟨fun h1 h2 => ?_, fun h1 h2 => ?_, fun h1 => ?_⟩
  · show (match x.stock with
        | [] => match x.waste with
          | [] => x
          | w => { x with stock := w.reverse, waste := ([] : List Card) }
        | _ => x) = x
    rw [h1, h2]
  · show (match x.stock with
        | [] => match x.waste with
          | [] => x
          | w => { x with stock := w.reverse, waste := ([] : List Card) }
        | _ => x)
      = { x with stock := x.waste.reverse, waste := [] }
    rw [h1]
    show (match x.waste with
      | [] => x
      | w => { x with stock := w.reverse, waste := ([] : List Card) })
      = { x with stock := x.waste.reverse, waste := [] }
    cases hcon : x.waste with
    | nil =>
        rw [hcon] at h2
        exact absurd rfl h2
    | cons a as =>
        rfl
  · obtain ⟨a, as, hcon⟩ := list_cons_of_ne_nil h1
    show (match x.stock with
      | [] => match x.waste with
        | [] => x
        | w => { x with stock := w.reverse, waste := ([] : List Card) }
      | _ => x) = x
    rw [hcon]

/-- Two states with equal draw zones draw to the same dealt stock and
waste, each keeping its own found and tableau.  (Restated from the
private `Orig/Dominance.lean:812` row; the public readers are
`Orig/Play.lean`'s `draw_unfold`/`dealStock_eq_of_ne_nil`.) -/
private theorem stepDraw_congr {x y : State}
    (hx1 : y.stock = x.stock) (hx2 : y.waste = x.waste)
    (hx3 : y.drawStep = x.drawStep)
    {s' : State} (hstep : State.step x Move.draw = some s') :
    State.step y Move.draw = some { s' with found := y.found, piles := y.piles } := by
  obtain ⟨r, hru, hrne, hshape⟩ := draw_unfold hstep
  have hrr : (State.recycle y).stock = (State.recycle x).stock ∧
      (State.recycle y).waste = (State.recycle x).waste ∧
      (State.recycle y).drawStep = (State.recycle x).drawStep ∧
      (State.recycle y).found = y.found ∧ (State.recycle y).piles = y.piles := by
    cases hs : y.stock with
    | nil =>
        cases hw : y.waste with
        | nil =>
            have hxs : x.stock = [] := hx1.symm.trans hs
            have hxw : x.waste = [] := hx2.symm.trans hw
            rw [(recycle_fields y).1 hs hw, (recycle_fields x).1 hxs hxw]
            exact ⟨hx1, hx2, hx3, rfl, rfl⟩
        | cons w ws =>
            have hxs : x.stock = [] := hx1.symm.trans hs
            have hxw : x.waste = w :: ws := hx2.symm.trans hw
            have hxr : State.recycle x =
                { x with stock := x.waste.reverse, waste := [] } :=
              (recycle_fields x).2.1 hxs (by rw [hxw]; simp)
            have hyr : State.recycle y =
                { y with stock := y.waste.reverse, waste := [] } :=
              (recycle_fields y).2.1 hs (by rw [hw]; simp)
            rw [hyr, hxr, hxw, hw]
            exact ⟨rfl, rfl, hx3, rfl, rfl⟩
    | cons a as =>
        have hxs : x.stock = a :: as := hx1.symm.trans hs
        have hxr : State.recycle x = x := (recycle_fields x).2.2 (by rw [hxs]; simp)
        have hyr : State.recycle y = y := (recycle_fields y).2.2 (by rw [hs]; simp)
        rw [hyr, hxr]
        exact ⟨hx1, hx2, hx3, rfl, rfl⟩
  have hvne : (State.recycle y).stock ≠ [] := by
    rw [hrr.1, hru]
    exact hrne
  show State.dealStock (State.recycle y) = _
  rw [dealStock_eq_of_ne_nil _ hvne]
  rw [hshape]
  rw [hrr.2.2.1, hrr.1, hrr.2.1, hrr.2.2.2.1, hrr.2.2.2.2, hru]

/-! ## §2. The draw-step and stock footprints of a letter -/

/-- No letter changes the deal quantum. -/
private theorem step_drawStep {u u' : State} {m : Move}
    (h : State.step u m = some u') : u'.drawStep = u.drawStep := by
  cases m with
  | draw => exact draw_drawStep h
  | wasteToFound c =>
      obtain ⟨-, x, xs, hw, hs⟩ := step_wasteToFound_inv h
      rw [hs]
      rfl
  | wasteToTab c b =>
      obtain ⟨-, x, xs, hw, hs⟩ := step_wasteToTab_inv h
      rw [hs]
      exact (putCard_keep (st := u) (c := c) (b := b)).2.2.2
  | tabToFound c =>
      obtain ⟨-, a, hp, hs⟩ := step_tabToFound_inv h
      rw [hs]
      rfl
  | foundToTab c b =>
      obtain ⟨c', ht, hc', hcp, hs⟩ := step_foundToTab_inv h
      rw [hs]
      exact (putCard_keep (st := u.setFound c.suit (chop (u.found c.suit)))
        (c := c) (b := b)).2.2.2
  | tabToTab c b =>
      obtain ⟨a, hh, hcp, hne, hs⟩ := step_tabToTab_inv h
      rw [hs]
      exact (putRun_keep (st := u.setPile a
        (Pile.afterRunRemoved (u.piles a) (below c (u.piles a).faceUp)))
        (run := fromCard c (u.piles a).faceUp) (b := b)).2.2.2

/-- Every non-draw letter leaves the stock verbatim. -/
private theorem step_stock_eq_of_ne_draw {u u' : State} {m : Move}
    (hm : m ≠ Move.draw) (h : State.step u m = some u') :
    u'.stock = u.stock := by
  cases m with
  | draw => exact absurd rfl hm
  | wasteToFound c =>
      obtain ⟨-, x, xs, hw, hs⟩ := step_wasteToFound_inv h
      rw [hs]
      rfl
  | wasteToTab c b =>
      obtain ⟨-, x, xs, hw, hs⟩ := step_wasteToTab_inv h
      rw [hs]
      exact (putCard_keep (st := u) (c := c) (b := b)).2.1
  | tabToFound c =>
      obtain ⟨-, a, hp, hs⟩ := step_tabToFound_inv h
      rw [hs]
      rfl
  | foundToTab c b =>
      obtain ⟨c', ht, hc', hcp, hs⟩ := step_foundToTab_inv h
      rw [hs]
      exact (putCard_keep (st := u.setFound c.suit (chop (u.found c.suit)))
        (c := c) (b := b)).2.1
  | tabToTab c b =>
      obtain ⟨a, hh, hcp, hne, hs⟩ := step_tabToTab_inv h
      rw [hs]
      exact (putRun_keep (st := u.setPile a
        (Pile.afterRunRemoved (u.piles a) (below c (u.piles a).faceUp)))
        (run := fromCard c (u.piles a).faceUp) (b := b)).2.1

/-- With `drawStep = 0`, a nonempty stock survives every legal play. -/
private theorem run_stock_ne_of_drawStep_zero :
    ∀ (ρ : List Move) {u z : State},
      u.drawStep = 0 → u.stock ≠ [] → u.run ρ = some z → z.stock ≠ []
  | [], u, z, hds, hs, h => by
      simp only [State.run] at h
      injection h with hEq
      subst hEq
      exact hs
  | m :: rest, u, z, hds, hs, h => by
      obtain ⟨u1, hstep, hrest⟩ := State.run_cons h
      have hds1 : u1.drawStep = 0 := (step_drawStep hstep).trans hds
      have hs1 : u1.stock ≠ [] := by
        by_cases hmd : m = Move.draw
        · subst hmd
          obtain ⟨r, hru, hrne, hshape⟩ := draw_unfold hstep
          have hrds : r.drawStep = 0 := by
            rw [← hru, recycle_drawStep u]
            exact hds
          rw [hshape]
          rw [hrds]
          exact hrne
        · rw [step_stock_eq_of_ne_draw hmd hstep]
          exact hs
      exact run_stock_ne_of_drawStep_zero rest hds1 hs1 hrest

/-! ## §3. Draw reversibility is a draw-zone property -/

/-- At a positive deal quantum, a reversible draw stays reversible at
any state sharing the draw zone.  (Restatement of the private
`Orig2/OrbitFactor.lean:659` census, whose mint and denial rows are the
public `Orig2/Kit.lean` rows.) -/
private theorem draw_revTransfer_pos {x y : State} (hpos : 0 < x.drawStep)
    (hs : x.stock = y.stock) (hw : x.waste = y.waste)
    (hds : x.drawStep = y.drawStep)
    (h : reversibleAtW x Move.draw) : reversibleAtW y Move.draw := by
  have hypos : 0 < y.drawStep := by rw [← hds]; exact hpos
  cases hst : x.stock with
  | nil =>
      cases hws : x.waste with
      | nil =>
          exfalso
          have hdead : x.stepDraw = none := by
            rw [show x.stepDraw = State.dealStock (State.recycle x) from rfl,
              recycle_allEmpty x hst hws, dealStock_nil x hst]
          obtain ⟨_s1o, _P0, hstep', _hrn⟩ := h
          rw [show State.step x Move.draw = x.stepDraw from rfl, hdead] at hstep'
          exact absurd hstep' (by simp)
      | cons w ws =>
          have hyw : y.waste = w :: ws := by rw [← hw]; exact hws
          have hys : y.stock = [] := by rw [← hs]; exact hst
          exact draw_passBase_reversibleW hys
            (by rw [hyw]; exact fun hc => absurd hc (by simp)) hypos
  | cons c cs =>
      have hys : y.stock ≠ [] := by
        intro hc
        rw [← hs] at hc
        rw [hst] at hc
        exact nomatch hc
      by_cases hpr : x.waste = []
      · exact absurd h (draw_notW_of_pristine hpos
          (by rw [hst]; exact fun hc => absurd hc (by simp)) hpr)
      · by_cases hres : x.waste.length % x.drawStep = 0
        · obtain ⟨c', t', hcon'⟩ := list_cons_of_ne_nil hys
          have hph' : inPhase y = true := by
            rw [inPhase_eq_decide_of_cons hcon']
            refine decide_eq_true ?_
            rw [← hds, ← hw]
            exact hres
          exact draw_inphase_reversibleW hypos hys
            (by intro hc; exact hpr (hw.trans hc)) hph'
        · exact absurd h (draw_notW_of_offset hpos
            (by rw [hst]; exact fun hc => absurd hc (by simp)) hres)

/-- A reversible draw stays reversible at any state sharing the draw
zone, with the zero-quantum corner handled separately (there a draw
with cards in the stock is the identity). -/
private theorem draw_revTransfer {x y : State}
    (hs : x.stock = y.stock) (hw : x.waste = y.waste)
    (hds : x.drawStep = y.drawStep)
    (h : reversibleAtW x Move.draw) : reversibleAtW y Move.draw := by
  by_cases hpos : 0 < x.drawStep
  · exact draw_revTransfer_pos hpos hs hw hds h
  · have hds0 : x.drawStep = 0 := by omega
    have hxne : x.stock ≠ [] := by
      intro hx0
      obtain ⟨x1, play, hstep, hrun⟩ := h
      obtain ⟨r, hru, hrne, hshape⟩ := draw_unfold hstep
      have hrds : r.drawStep = 0 := by
        rw [← hru, recycle_drawStep x]
        exact hds0
      have hx1ne : x1.stock ≠ [] := by
        rw [hshape]
        rw [hrds]
        exact hrne
      have hx1ds : x1.drawStep = 0 := (draw_drawStep hstep).trans hds0
      exact (run_stock_ne_of_drawStep_zero play hx1ds hx1ne hrun) hx0
    have hyne : y.stock ≠ [] := by rw [← hs]; exact hxne
    have hy0 : y.drawStep = 0 := hds.symm.trans hds0
    have hystep : State.step y Move.draw = some y := by
      show State.dealStock (State.recycle y) = some y
      rw [recycle_keep y hyne, dealStock_eq_of_ne_nil y hyne]
      have h0 : State.dealUpTo y.drawStep y.stock = ([], y.stock) := by
        rw [hy0]
        rfl
      rw [h0]
      rfl
    exact ⟨y, [], hystep, rfl⟩

/-! ## §5. The step and play commutation squares -/

/-- **Draws commute with the strict twin swap.** -/
theorem stepDraw_swap {s v s1 : State} {x : Card}
    (hswap : twinPairSwapStrict s v x)
    (hstep : State.step s Move.draw = some s1) :
    ∃ v1, State.step v Move.draw = some v1 ∧ twinPairSwapStrict s1 v1 x := by
  obtain ⟨hseat1, hseat2, hother, hboard, hfounds, hstock, hwaste, hcut⟩ := hswap
  obtain ⟨hhidden, hdstep⟩ := hboard
  have hvstep : State.step v Move.draw =
      some { s1 with found := v.found, piles := v.piles } :=
    stepDraw_congr hstock.symm hwaste.symm hdstep.symm hstep
  refine ⟨{ s1 with found := v.found, piles := v.piles }, hvstep, ?_⟩
  have hs1p : s1.piles = s.piles := stepDraw_piles hstep
  have hs1f : s1.found = s.found := stepDraw_found hstep
  have hv1p : ({ s1 with found := v.found, piles := v.piles } : State).piles = v.piles := rfl
  have hs1_seat : ∀ c, seatOf s1 c = seatOf s c := fun c =>
    seatOf_congr_piles hs1p c
  have hv1_seat : ∀ c,
      seatOf ({ s1 with found := v.found, piles := v.piles } : State) c = seatOf v c :=
    fun c => seatOf_congr_piles hv1p c
  refine ⟨?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl⟩
  · rw [hv1_seat x, hseat1, ← hs1_seat x.twin]
  · rw [hv1_seat x.twin, hseat2, ← hs1_seat x]
  · intro y hyx hyt
    rw [hv1_seat y, hother y hyx hyt, ← hs1_seat y]
  · refine ⟨fun a => ?_, ?_⟩
    · rw [show (s1.piles a).hidden = (s.piles a).hidden from
            congrArg Pile.hidden (congrFun hs1p a),
          show (({ s1 with found := v.found, piles := v.piles } : State).piles a).hidden
              = (v.piles a).hidden from rfl]
      exact hhidden a
    · rfl
  · intro suit
    rw [show s1.found suit = s.found suit from congrArg (fun f => f suit) hs1f,
          show ({ s1 with found := v.found, piles := v.piles } : State).found suit
              = v.found suit from rfl]
    exact hfounds suit

/-- **A whole draws-only play commutes with the strict twin swap.** -/
theorem drawPlay_swap {s s' v : State} {x : Card} {play : List Move}
    (hswap : twinPairSwapStrict s v x)
    (hplay : DrawPlayW s play s') :
    ∃ v', ShufflePlayW v play v' ∧ twinPairSwapStrict s' v' x := by
  have aux : ∀ {u u' : State} {ρ : List Move},
      ShufflePlayW u ρ u' → (∀ m ∈ ρ, m = Move.draw) →
      ∀ {v : State}, twinPairSwapStrict u v x →
      ∃ v', ShufflePlayW v ρ v' ∧ twinPairSwapStrict u' v' x := by
    intro u u' ρ hwalk
    induction hwalk with
    | nil u =>
        intro _ v hswap
        exact ⟨v, Walk.nil v, hswap⟩
    | @cons st s1 W m ρ hlet hstep hrest ih =>
        intro hdraw v hswap
        have hm : m = Move.draw := hdraw m (List.mem_cons_self)
        subst hm
        have hdraw_tail : ∀ m' ∈ ρ, m' = Move.draw :=
          fun m' hm' => hdraw m' (List.mem_cons_of_mem _ hm')
        obtain ⟨v1, hvstep, hswap1⟩ := stepDraw_swap hswap hstep
        obtain ⟨-, -, -, hboard, -, hstock, hwaste, -⟩ := hswap
        obtain ⟨-, hdstep⟩ := hboard
        have hletv : reversibleAtW v Move.draw :=
          draw_revTransfer hstock hwaste hdstep hlet
        obtain ⟨v', hwalk', hswap'⟩ := ih hdraw_tail hswap1
        exact ⟨v', Walk.cons hletv hvstep hwalk', hswap'⟩
  obtain ⟨hwalk, hdraw⟩ := hplay
  exact aux hwalk hdraw hswap

/-! ## §6. The invariant across the draw-rotation phase -/

/-- A draw-only run keeps the board and the foundations of its source. -/
private theorem run_draw_piles_found :
    ∀ (ρ : List Move) {u u' : State}, u.run ρ = some u' →
      (∀ m ∈ ρ, m = Move.draw) → u'.piles = u.piles ∧ u'.found = u.found
  | [], u, u', h, _ => by
      simp only [State.run] at h
      injection h with hEq
      subst hEq
      exact ⟨rfl, rfl⟩
  | m :: rest, u, u', h, hdr => by
      obtain ⟨u1, hstep, hrest⟩ := State.run_cons h
      have hm : m = Move.draw := hdr m (List.mem_cons_self)
      subst hm
      have hp1 : u1.piles = u.piles := stepDraw_piles hstep
      have hf1 : u1.found = u.found := stepDraw_found hstep
      have hdr' : ∀ m' ∈ rest, m' = Move.draw :=
        fun m' hm' => hdr m' (List.mem_cons_of_mem _ hm')
      obtain ⟨hp2, hf2⟩ := run_draw_piles_found rest hrest hdr'
      exact ⟨hp2.trans hp1, hf2.trans hf1⟩

/-- One direction of the phase invariance. -/
private theorem swappableIn_draw_transfer_fwd {s s' v : State} {x : Card}
    (h : SWRotW s s') (hswap : twinPairSwapStrict s v x)
    (horb : sameOrbitSetoid.r s v) : SwappableIn s' x := by
  obtain ⟨σ, τ, hσ, hτ⟩ := h
  obtain ⟨α, hα, β, hβ⟩ := horb
  obtain ⟨v', hvσ, hswap'⟩ := drawPlay_swap hswap hσ
  obtain ⟨w, hwτ, hsw⟩ := drawPlay_swap hswap' hτ
  obtain ⟨-, -, -, hboard, -, hstock, hwaste, -⟩ := hswap
  obtain ⟨-, -, -, wboard, -, wstock, wwaste, -⟩ := hsw
  obtain ⟨-, hdstep⟩ := hboard
  obtain ⟨-, wdstep⟩ := wboard
  have hσrun : v.run σ = some v' := Walk_run _ hvσ
  have hτrun : v'.run τ = some w := Walk_run _ hwτ
  obtain ⟨hpσ, hfσ⟩ := run_draw_piles_found σ hσrun hσ.2
  obtain ⟨hpτ, hfτ⟩ := run_draw_piles_found τ hτrun hτ.2
  have hwv : w = v := by
    refine State.ext ?_ ?_ ?_ ?_ ?_
    · exact hfτ.trans hfσ
    · exact hpτ.trans hpσ
    · exact wstock.symm.trans hstock
    · exact wwaste.symm.trans hwaste
    · exact wdstep.symm.trans hdstep
  rw [hwv] at hwτ
  have hback : ShufflePlayW v' (τ ++ α ++ σ) s' :=
    ShufflePlayW_append (ShufflePlayW_append hwτ hα) hσ.1
  have hfwd : ShufflePlayW s' (τ ++ β ++ σ) v' :=
    ShufflePlayW_append (ShufflePlayW_append hτ.1 hβ) hvσ
  exact ⟨v', hswap', ⟨τ ++ α ++ σ, hback, τ ++ β ++ σ, hfwd⟩⟩

/-- **`SwappableIn` is invariant across the draw-rotation phase.** -/
theorem swappableIn_draw_transfer {s s' : State} {x : Card}
    (h : SWRotW s s') :
    SwappableIn s x ↔ SwappableIn s' x := by
  constructor
  · rintro ⟨v, hswap, horb⟩
    exact swappableIn_draw_transfer_fwd h hswap horb
  · intro hs'
    have h' : SWRotW s' s := by
      obtain ⟨σ, τ, hσ, hτ⟩ := h
      exact ⟨τ, σ, hτ, hσ⟩
    obtain ⟨v, hswap, horb⟩ := hs'
    exact swappableIn_draw_transfer_fwd h' hswap horb

#print axioms stepDraw_swap
#print axioms drawPlay_swap
#print axioms swappableIn_draw_transfer
