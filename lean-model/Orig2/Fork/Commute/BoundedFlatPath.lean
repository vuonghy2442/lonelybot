import Orig2.Fork.Commute.FlatNormal
import Orig2.Boundary
import Orig2.Fork.Split.ForkSplit
import Orig2.Fork.Local.ForkBubble

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# Orig2.Fork.Commute.BoundedFlatPath - bounded-path flat normal form

This is the stronger per-pair form of the flat normal theorem: it replaces
the global rung maximum `IsRungMax u` by a rung bound on one connecting play.
No `Forkless` and no `SSaturated` hypothesis is required.  The legacy
class-global form remains in `Orig2/Fork/Commute/FlatNormal.lean`.
-/

open OneColourClosure

/-- A state `z` occurs on the play (at a prefix). -/
def StateOnPlay (start : State) (play : List Move) (z : State) : Prop :=
  ∃ pre post, play = pre ++ post ∧ start.run pre = some z

/-- There is an equal-rung connecting play whose every visited state lies
below the source rung. -/
def RungBoundedPath (u v : State) : Prop :=
  ∃ play,
    ShufflePlayW u play v ∧
    (∀ z, StateOnPlay u play z → RungLe z u)

/-- The rung-bound carried along an arbitrary suffix of a play. -/
def BoundedFrom (u s : State) (l : List Move) : Prop :=
  ∀ pre post, l = pre ++ post → ∀ z, s.run pre = some z → RungLe z u

/-- `BoundedFrom` for the whole play is exactly the pointwise bound. -/
theorem boundedFrom_of_onPlay {u : State} {play : List Move}
    (h : ∀ z, StateOnPlay u play z → RungLe z u) :
    BoundedFrom u u play := by
  intro pre post hspl z hrun
  exact h z ⟨pre, post, hspl, hrun⟩

/-- The bound at the first state of a nonempty suffix. -/
theorem BoundedFrom.head {u s s1 : State} {m : Move} {rest : List Move}
    (h : BoundedFrom u s (m :: rest))
    (hstep : State.step s m = some s1) :
    RungLe s1 u := by
  have hrun : s.run [m] = some s1 := run_one hstep
  exact h [m] rest (by simp) s1 hrun

/-- The bound carried to the tail of a nonempty suffix. -/
theorem BoundedFrom.tail {u s s1 : State} {m : Move} {rest : List Move}
    (h : BoundedFrom u s (m :: rest))
    (hstep : State.step s m = some s1) :
    BoundedFrom u s1 rest := by
  intro pre post hspl z hrun
  have hspl' : m :: rest = (m :: pre) ++ post := by
    rw [hspl]; rfl
  have hrun' : s.run (m :: pre) = some z := by
    simp only [State.run, hstep]
    exact hrun
  exact h (m :: pre) post hspl' z hrun'

/-- A `tabToFound` of a card seated at `u` cannot occur on a play bounded by
`u`: the landing rung is the card's rank plus one, but a seated card has rung
at most its rank. -/
theorem raise_on_bounded_play_false
    {u s s1 : State} {x : Card} {b : Base} {m : Move}
    (hu : u.WF)
    (hstep : State.step s m = some s1)
    (hb : RungLe s1 u)
    (hseat_u : seatOf u x = some b)
    (hm : m = Move.tabToFound x) :
    False := by
  subst hm
  obtain ⟨hnext, _a, _htop, _hrest⟩ := step_tabToFound_inv hstep
  have hpin : rungAt s x.suit = x.rank.toIdx :=
    TwinKit.nextUp_true_iff.mp hnext
  have hland : rungAt s1 x.suit = rungAt s x.suit + 1 := by
    rw [rungAt_tabToFound hstep x.suit]
    simp
  have hle : rungAt s1 x.suit ≤ rungAt u x.suit := hb x.suit
  have hseat : rungAt u x.suit ≤ x.rank.toIdx :=
    le_rung_of_seated hu ⟨b, hseat_u⟩
  omega

/-! ## Twin-pair rigidity along a bounded play -/

/-- The fitting class of a card is a twin pair (local copy of the private
`FiberTransfer` row). -/
theorem fit_z_or_ztwin_b {x z w : Card}
    (hxz : canSitOn x z = true) (hxw : canSitOn x w = true) :
    w = z ∨ w = z.twin := by
  obtain ⟨hr1, hc1⟩ := (canSitOn_eq x z).mp hxz
  obtain ⟨hr2, hc2⟩ := (canSitOn_eq x w).mp hxw
  rcases w with ⟨ws, wr⟩
  rcases z with ⟨zs, zr⟩
  rcases x with ⟨xs, xr⟩
  have h0 : (Card.mk zs zr).rank.toIdx = (Card.mk ws wr).rank.toIdx := by omega
  have hrw : zr = wr := Rank.toIdx_inj h0
  have hcc : (Card.mk ws wr).suit.color = (Card.mk zs zr).suit.color := by
    cases xs <;> cases ws <;> cases zs <;> simp [Suit.color] at hc1 hc2 ⊢
  by_cases hsz : ws = zs
  · left
    rw [hsz, hrw]
  · right
    have hwt : ws = zs.twin := by
      cases xs <;> cases ws <;> cases zs <;>
        simp [Suit.color, Suit.twin] at hcc hsz ⊢
    rw [hwt, hrw]
    rfl

/-- A non-king twin cannot slide away while both twins sit on their parents
(local copy of the private `FiberTransfer` row). -/
theorem no_twin_slide_b {u u' : State} {x z : Card} {b : Base}
    (hwf : u.WF)
    (hx : seatOf u x = some (Sum.inr z))
    (hxt : seatOf u x.twin = some (Sum.inr z.twin))
    (hstep : State.step u (Move.tabToTab x b) = some u') : False := by
  have hnk : x.rank ≠ Rank.king := tfc_seatOf_inr_rank_ne_king hwf hx
  obtain ⟨-, -, hcp, -, -⟩ := step_tabToTab_inv hstep
  cases b with
  | inl a =>
      obtain ⟨-, hking⟩ := canPlace_inl hcp
      exact hnk hking
  | inr w =>
      obtain ⟨k, hptop, hfit⟩ := canPlace_inr hcp
      obtain ⟨a, hhold, -, hlast⟩ := tfc_seatOf_of_inr hx
      obtain ⟨hfitz, hburial⟩ := tfc_seat_parent hwf hhold hlast
      rcases fit_z_or_ztwin_b hfitz hfit with rfl | rfl
      · simp [hburial] at hptop
      · obtain ⟨b', hholdt, -, hlastt⟩ := tfc_seatOf_of_inr hxt
        obtain ⟨-, hburialt⟩ := tfc_seat_parent hwf hholdt hlastt
        simp [hburialt] at hptop

/-- Auxiliary induction: both twins keep their twin parents along a bounded
suffix. -/
theorem twin_seats_fixed_aux
    {u : State} (hu : u.WF) {x z : Card}
    (hx_u : seatOf u x = some (Sum.inr z))
    (hxt_u : seatOf u x.twin = some (Sum.inr z.twin)) :
    ∀ {s W : State} {l : List Move},
      ShufflePlayW s l W → BoundedFrom u s l → s.WF →
      seatOf s x = some (Sum.inr z) →
      seatOf s x.twin = some (Sum.inr z.twin) →
      seatOf W x = some (Sum.inr z) ∧
        seatOf W x.twin = some (Sum.inr z.twin) := by
  intro s W l hplay
  induction hplay with
  | nil s =>
      intro _ _ hx hxt
      exact ⟨hx, hxt⟩
  | @cons st s1 W m rest hrev hstep hrest ih =>
      intro hb hwf_st hx hxt
      have hb_head : RungLe s1 u := hb.head hstep
      have hb_tail : BoundedFrom u s1 rest := hb.tail hstep
      have hwf1 : s1.WF := step_wf hwf_st hstep
      have hpair :
          seatOf s1 x = some (Sum.inr z) ∧
            seatOf s1 x.twin = some (Sum.inr z.twin) := by
        cases m with
        | draw =>
            have hse := (chart_draw hstep).1
            exact ⟨by rw [hse, hx], by rw [hse, hxt]⟩
        | wasteToFound y =>
            exact absurd hrev (wasteToFound_not_reversibleAtW st y)
        | wasteToTab y b =>
            exact absurd hrev (wasteToTab_not_reversibleAtW st y b)
        | tabToFound d =>
            by_cases hdx : d = x
            · subst d
              exact (raise_on_bounded_play_false hu hstep hb_head hx_u rfl).elim
            · by_cases hdt : d = x.twin
              · subst d
                exact (raise_on_bounded_play_false hu hstep hb_head hxt_u rfl).elim
              · have hxne : seatOf st x ≠ none := by rw [hx]; simp
                have hxtne : seatOf st x.twin ≠ none := by rw [hxt]; simp
                have hsel : seatOf s1 x = seatOf st x :=
                  raise_seat_change_of_seated hstep hrev hxne
                    (fun h => hdx h.symm)
                have hselt : seatOf s1 x.twin = seatOf st x.twin :=
                  raise_seat_change_of_seated hstep hrev hxtne
                    (fun h => hdt h.symm)
                exact ⟨by rw [hsel, hx], by rw [hselt, hxt]⟩
        | foundToTab d b =>
            by_cases hdx : d = x
            · subst d
              exfalso
              obtain ⟨c', htop, hc'c, _hcp, _hs⟩ := step_foundToTab_inv hstep
              have hlast : lastOf (st.found x.suit) = some x := by
                unfold State.foundTop at htop
                rw [hc'c] at htop
                exact htop
              exact (cover_not_found hwf_st hx) (lastOf_mem hlast)
            · by_cases hdt : d = x.twin
              · subst d
                exfalso
                obtain ⟨c', htop, hc'c, _hcp, _hs⟩ := step_foundToTab_inv hstep
                have hlast : lastOf (st.found x.twin.suit) = some x.twin := by
                  unfold State.foundTop at htop
                  rw [hc'c] at htop
                  exact htop
                exact (cover_not_found hwf_st hxt) (lastOf_mem hlast)
              · have hsel : seatOf s1 x = seatOf st x :=
                  pull_seat_change hstep x (fun h => hdx h.symm)
                have hselt : seatOf s1 x.twin = seatOf st x.twin :=
                  pull_seat_change hstep x.twin (fun h => hdt h.symm)
                exact ⟨by rw [hsel, hx], by rw [hselt, hxt]⟩
        | tabToTab d b =>
            by_cases hdx : d = x
            · subst d
              exact (no_twin_slide_b hwf_st hx hxt hstep).elim
            · by_cases hdt : d = x.twin
              · subst d
                have hxt' : seatOf st x.twin = some (Sum.inr z.twin) := hxt
                have hx'' : seatOf st x.twin.twin = some (Sum.inr z.twin.twin) := by
                  rw [card_twin_twin, card_twin_twin]
                  exact hx
                exact (no_twin_slide_b hwf_st hxt' hx'' hstep).elim
              · have hpt := tfc_seat_point_edit hwf_st hstep hrev
                have hsel : seatOf s1 x = seatOf st x := by
                  rw [hpt x, ite_eq_right (fun h => hdx h.symm)]
                have hselt : seatOf s1 x.twin = seatOf st x.twin := by
                  rw [hpt x.twin, ite_eq_right (fun h => hdt h.symm)]
                exact ⟨by rw [hsel, hx], by rw [hselt, hxt]⟩
      exact ih hb_tail hwf1 hpair.1 hpair.2

/-- Both twins keep their twin parents along the whole bounded play. -/
theorem twin_seats_fixed_of_bounded
    {u v : State} {play : List Move} {x z : Card}
    (hu : u.WF)
    (hplay : ShufflePlayW u play v)
    (hb : BoundedFrom u u play)
    (hx : seatOf u x = some (Sum.inr z))
    (hxt : seatOf u x.twin = some (Sum.inr z.twin)) :
    seatOf v x = some (Sum.inr z) ∧
      seatOf v x.twin = some (Sum.inr z.twin) :=
  twin_seats_fixed_aux hu hx hxt hplay hb hu hx hxt

/-! ## The `.inr` parent stays in the twin pair -/

/-- Auxiliary induction: an `.inr`-seated card's parent stays in the twin
pair `{z0, z0.twin}` along a bounded suffix. -/
theorem inr_parent_mem_aux
    {u : State} (hu : u.WF) {x z0 : Card}
    (hseat_u : seatOf u x = some (Sum.inr z0)) :
    ∀ {s W : State} {l : List Move},
      ShufflePlayW s l W → BoundedFrom u s l → s.WF →
      (∃ z, seatOf s x = some (Sum.inr z) ∧ (z = z0 ∨ z = z0.twin)) →
      ∃ z, seatOf W x = some (Sum.inr z) ∧ (z = z0 ∨ z = z0.twin) := by
  intro s W l hplay
  induction hplay with
  | nil s =>
      intro _ _ h
      exact h
  | @cons st s1 W m rest hrev hstep hrest ih =>
      intro hb hwf_st hcur
      have hb_head : RungLe s1 u := hb.head hstep
      have hb_tail : BoundedFrom u s1 rest := hb.tail hstep
      have hwf1 : s1.WF := step_wf hwf_st hstep
      have hnext : ∃ z, seatOf s1 x = some (Sum.inr z) ∧
          (z = z0 ∨ z = z0.twin) := by
        cases m with
        | draw =>
            obtain ⟨z, hz, hzp⟩ := hcur
            have hse := (chart_draw hstep).1
            exact ⟨z, by rw [hse, hz], hzp⟩
        | wasteToFound y =>
            exact absurd hrev (wasteToFound_not_reversibleAtW st y)
        | wasteToTab y b =>
            exact absurd hrev (wasteToTab_not_reversibleAtW st y b)
        | tabToFound d =>
            by_cases hdx : d = x
            · subst d
              exact (raise_on_bounded_play_false hu hstep hb_head hseat_u rfl).elim
            · obtain ⟨z, hz, hzp⟩ := hcur
              have hxne : seatOf st x ≠ none := by rw [hz]; simp
              have hsel : seatOf s1 x = seatOf st x :=
                raise_seat_change_of_seated hstep hrev hxne
                  (fun h => hdx h.symm)
              exact ⟨z, by rw [hsel, hz], hzp⟩
        | foundToTab d b =>
            by_cases hdx : d = x
            · subst d
              exfalso
              obtain ⟨z, hz, _⟩ := hcur
              obtain ⟨c', htop, hc'c, _hcp, _hs⟩ := step_foundToTab_inv hstep
              have hlast : lastOf (st.found x.suit) = some x := by
                unfold State.foundTop at htop
                rw [hc'c] at htop
                exact htop
              exact (cover_not_found hwf_st hz) (lastOf_mem hlast)
            · obtain ⟨z, hz, hzp⟩ := hcur
              have hsel : seatOf s1 x = seatOf st x :=
                pull_seat_change hstep x (fun h => hdx h.symm)
              exact ⟨z, by rw [hsel, hz], hzp⟩
        | tabToTab d b =>
            by_cases hdx : d = x
            · subst d
              obtain ⟨z, hz, hzp⟩ := hcur
              obtain ⟨hsed, htarget⟩ :=
                floater_seat_change_spec hwf_st hstep hrev
              have hnew : seatOf s1 x = some b := by
                simpa using hsed.1 x
              rcases htarget with ⟨z₁, z', hz₁, hb, hz'p⟩ | ⟨a, a', hzinl, _hb, _hk, _hh⟩
              · have hzz : z₁ = z := Sum.inr.inj (Option.some.inj (hz₁.symm.trans hz))
                subst z₁
                subst b
                have hz'zp : z' = z0 ∨ z' = z0.twin := by
                  rcases hz'p with rfl | rfl
                  · exact hzp
                  · rcases hzp with rfl | rfl
                    · exact Or.inr rfl
                    · exact Or.inl (by simp [card_twin_twin])
                exact ⟨z', by rw [hnew], hz'zp⟩
              · rw [hz] at hzinl
                nomatch hzinl
            · by_cases hdt : d = x
              · exact absurd hdt hdx
              · obtain ⟨z, hz, hzp⟩ := hcur
                have hpt := tfc_seat_point_edit hwf_st hstep hrev
                have hsel : seatOf s1 x = seatOf st x := by
                  rw [hpt x, ite_eq_right (fun h => hdx h.symm)]
                exact ⟨z, by rw [hsel, hz], hzp⟩
      exact ih hb_tail hwf1 hnext

/-- The `.inr` parent stays in the twin pair along the whole bounded play. -/
theorem inr_parent_mem_of_bounded
    {u v : State} {play : List Move} {x z0 : Card}
    (hu : u.WF)
    (hplay : ShufflePlayW u play v)
    (hb : BoundedFrom u u play)
    (hseat_u : seatOf u x = some (Sum.inr z0)) :
    ∃ z, seatOf v x = some (Sum.inr z) ∧ (z = z0 ∨ z = z0.twin) :=
  inr_parent_mem_aux hu hseat_u hplay hb hu ⟨z0, hseat_u, Or.inl rfl⟩

/-- A non-floater seated on a twin parent keeps its seat along a bounded play. -/
theorem inr_seat_fixed_of_nonFloater_bounded
    {u v : State} {play : List Move} {x z0 : Card}
    (hu : u.WF)
    (hplay : ShufflePlayW u play v)
    (hb : BoundedFrom u u play)
    (hrung : RungEq u v)
    (hseat : seatOf u x = some (Sum.inr z0))
    (hnf : ¬ FloaterSpec u x) :
    seatOf u x = seatOf v x := by
  by_cases hct : seatOf u x.twin = some (Sum.inr z0.twin)
  · exact hseat.trans (twin_seats_fixed_of_bounded hu hplay hb hseat hct).1.symm
  · obtain ⟨z, hz, hzp⟩ := inr_parent_mem_of_bounded hu hplay hb hseat
    rcases hzp with rfl | rfl
    · exact hseat.trans hz.symm
    · exfalso
      have hnotface_u := not_faceUp_target_of_twin_not_seated hu hseat hnf hct
      have hvface : ∃ a, z0.twin ∈ (v.piles a).faceUp := by
        obtain ⟨a, _hhold, _hpos, hlast⟩ := tfc_seatOf_of_inr hz
        exact ⟨a, mem_below _ (lastOf_mem hlast)⟩
      have horb : sameOrbitSetoid.r u v :=
        RevEqW_symm (shufflePlayW_revEqW hplay)
      exact hnotface_u ((faceUp_iff hu horb hrung z0.twin).mpr hvface)

/-! ## Non-king bottomed cards are frozen -/

/-- The `bottom_seat_step_nonKing` step lemma, with the global no-raise
hypothesis weakened to "the present move is not the raise of `c`". -/
theorem bottom_seat_step_nonKing_bounded
    {st s1 : State} {m : Move} {c : Card} {a0 : Anchor}
    (hwf : st.WF) (hstep : State.step st m = some s1)
    (hrev : reversibleAtW st m)
    (hse : seatOf st c = some (Sum.inl a0))
    (hnk : c.rank ≠ Rank.king)
    (hnoRaise : m = Move.tabToFound c → False) :
    seatOf s1 c = some (Sum.inl a0) := by
  cases m with
  | draw =>
      rw [(chart_draw hstep).1 c]
      exact hse
  | wasteToFound x =>
      obtain ⟨_, y, ys, _hw, hs⟩ := step_wasteToFound_inv hstep
      have hp : s1.piles = st.piles := by rw [hs]; rfl
      rw [seatOf_congr_piles hp c]
      exact hse
  | wasteToTab x b =>
      exact absurd hrev (wasteToTab_not_reversibleAtW st x b)
  | tabToFound x =>
      by_cases hxc : x = c
      · subst x
        exact (hnoRaise rfl).elim
      · rw [raise_seat_change_of_seated hstep hrev (by rw [hse]; simp)
          (fun hcon => hxc hcon.symm)]
        exact hse
  | foundToTab x b =>
      by_cases hxc : x = c
      · subst x
        exfalso
        obtain ⟨c', htop, hc'c, _hcp, _hs⟩ := step_foundToTab_inv hstep
        have hlast : lastOf (st.found c.suit) = some c := by
          unfold State.foundTop at htop
          rw [hc'c] at htop
          exact htop
        have hcfin : c ∈ st.found c.suit := lastOf_mem hlast
        have hcface : ∃ a, c ∈ (st.piles a).faceUp :=
          mem_faceUp_of_seat' (by rw [hse]; simp)
        obtain ⟨a, ha⟩ := hcface
        exact ((mem_found_unique hwf hcfin).1 a).2 ha
      · rw [pull_seat_change hstep c (fun hcon => hxc hcon.symm)]
        exact hse
  | tabToTab x b =>
      by_cases hxc : x = c
      · subst x
        exfalso
        have hR : tabToTabR st c b = true :=
          (tabToTabR_iff_reversibleAtW hwf c b).mpr hrev
        obtain ⟨a, hhold, _hcp, hcell⟩ := tfc_tabToTabR_inv hR
        obtain ⟨hhold0, hbelow0⟩ := tfc_seatOf_of_inl hse
        have ha : a = a0 := by
          rw [hhold0] at hhold
          injection hhold with h
          exact h.symm
        rw [ha] at hcell
        rcases hcell with hne | ⟨hbelow, _hhid, hk⟩
        · exact absurd hbelow0 hne
        · exact hnk hk
      · have hpt := tfc_seat_point_edit hwf hstep hrev
        have hsel : seatOf s1 c = seatOf st c := by
          rw [hpt c, ite_eq_right (fun hcon => hxc hcon.symm)]
        rw [hsel]
        exact hse

/-- Auxiliary induction: a non-king bottomed card keeps its anchor along a
bounded suffix. -/
theorem inl_nonKing_fixed_aux
    {u : State} (hu : u.WF) {c : Card} {a0 : Anchor}
    (hseat_u : seatOf u c = some (Sum.inl a0))
    (hnk : c.rank ≠ Rank.king) :
    ∀ {s W : State} {l : List Move},
      ShufflePlayW s l W → BoundedFrom u s l → s.WF →
      seatOf s c = some (Sum.inl a0) →
      seatOf W c = some (Sum.inl a0) := by
  intro s W l hplay
  induction hplay with
  | nil s =>
      intro _ _ h
      exact h
  | @cons st s1 W m rest hrev hstep hrest ih =>
      intro hb hwf_st hse
      have hb_head : RungLe s1 u := hb.head hstep
      have hb_tail : BoundedFrom u s1 rest := hb.tail hstep
      have hwf1 : s1.WF := step_wf hwf_st hstep
      have hnoRaise : m = Move.tabToFound c → False :=
        fun hm => raise_on_bounded_play_false hu hstep hb_head hseat_u hm
      have hse1 : seatOf s1 c = some (Sum.inl a0) :=
        bottom_seat_step_nonKing_bounded hwf_st hstep hrev hse hnk hnoRaise
      exact ih hb_tail hwf1 hse1

/-- A non-king bottomed card keeps its anchor along the whole bounded play. -/
theorem inl_nonKing_fixed_of_bounded
    {u v : State} {play : List Move} {c : Card} {a0 : Anchor}
    (hu : u.WF)
    (hplay : ShufflePlayW u play v)
    (hb : BoundedFrom u u play)
    (hnk : c.rank ≠ Rank.king)
    (hseat_u : seatOf u c = some (Sum.inl a0)) :
    seatOf v c = some (Sum.inl a0) :=
  inl_nonKing_fixed_aux hu hseat_u hnk hplay hb hu hseat_u

/-! ## A bare bottomed king lands in the fuel set -/

/-- Auxiliary induction: a king whose hidden deck is empty stays on `VK`
anchors, and any vacating cargo move lands on a fuel-set anchor. -/
theorem inl_king_VK_aux
    {u : State} (hu : u.WF) {x : Card} {a0 : Anchor}
    (hseat_u : seatOf u x = some (Sum.inl a0))
    (hk : x.rank = Rank.king)
    (_hhid_u : (u.piles a0).hidden = []) :
    ∀ {s W : State} {l : List Move},
      ShufflePlayW s l W → BoundedFrom u s l → s.WF →
      sameOrbitSetoid.r u s →
      (∃ a, seatOf s x = some (Sum.inl a) ∧ VKSet u a) →
      ∃ a, seatOf W x = some (Sum.inl a) ∧ VKSet u a := by
  intro s W l hplay
  induction hplay with
  | nil s =>
      intro _ _ _ h
      exact h
  | @cons st s1 W m rest hrev hstep hrest ih =>
      intro hb hwf_st hcls_st hcur
      have hb_head : RungLe s1 u := hb.head hstep
      have hb_tail : BoundedFrom u s1 rest := hb.tail hstep
      have hwf1 : s1.WF := step_wf hwf_st hstep
      have hcls1 : sameOrbitSetoid.r u s1 :=
        sameOrbitSetoid.iseqv.trans hcls_st (Drain.sameOrbit_of_step hrev hstep)
      have hnext : ∃ a, seatOf s1 x = some (Sum.inl a) ∧ VKSet u a := by
        cases m with
        | draw =>
            obtain ⟨a, hsea, hvk⟩ := hcur
            have hse := (chart_draw hstep).1
            exact ⟨a, by rw [hse, hsea], hvk⟩
        | wasteToFound y =>
            exact absurd hrev (wasteToFound_not_reversibleAtW st y)
        | wasteToTab y b =>
            exact absurd hrev (wasteToTab_not_reversibleAtW st y b)
        | tabToFound d =>
            by_cases hdx : d = x
            · subst d
              exact (raise_on_bounded_play_false hu hstep hb_head hseat_u rfl).elim
            · obtain ⟨a, hsea, hvk⟩ := hcur
              have hxne : seatOf st x ≠ none := by rw [hsea]; simp
              have hsel : seatOf s1 x = seatOf st x :=
                raise_seat_change_of_seated hstep hrev hxne
                  (fun h => hdx h.symm)
              exact ⟨a, by rw [hsel, hsea], hvk⟩
        | foundToTab d b =>
            by_cases hdx : d = x
            · subst d
              exfalso
              obtain ⟨a, hsea, _⟩ := hcur
              obtain ⟨c', htop, hc'c, _hcp, _hs⟩ := step_foundToTab_inv hstep
              have hlast : lastOf (st.found x.suit) = some x := by
                unfold State.foundTop at htop
                rw [hc'c] at htop
                exact htop
              have hcfin : x ∈ st.found x.suit := lastOf_mem hlast
              have hcface : ∃ a, x ∈ (st.piles a).faceUp :=
                mem_faceUp_of_seat hsea
              obtain ⟨a', ha'⟩ := hcface
              exact ((mem_found_unique hwf_st hcfin).1 a').2 ha'
            · obtain ⟨a, hsea, hvk⟩ := hcur
              have hsel : seatOf s1 x = seatOf st x :=
                pull_seat_change hstep x (fun h => hdx h.symm)
              exact ⟨a, by rw [hsel, hsea], hvk⟩
        | tabToTab d b =>
            by_cases hdx : d = x
            · subst d
              obtain ⟨a, hsea, _hvk⟩ := hcur
              obtain ⟨hsed, htarget⟩ :=
                floater_seat_change_spec hwf_st hstep hrev
              have hnew : seatOf s1 x = some b := by
                simpa using hsed.1 x
              obtain ⟨a_hold, hhold, hcp, hfr, hs⟩ := step_tabToTab_inv hstep
              rcases htarget with ⟨z, z', hzinr, _hb, _hzp⟩ |
                  ⟨a₂, a', hsinl, hb, _hk2, _hhid2⟩
              · rw [hsea] at hzinr
                nomatch hzinr
              · subst b
                have hempty : (st.piles a').isEmpty = true :=
                  (canPlace_inl hcp).1
                obtain ⟨hbf, _hff, _hdp, _hco⟩ :=
                  tfa_slide_conserves hwf_st hstep hrev
                have hhidden : (s1.piles a').hidden = [] := by
                  rw [← hbf.1 a']
                  exact (Pile.isEmpty_eq _).mp hempty |>.1
                have hkb : KingBottom s1 a' := ⟨x, by rw [hnew], hk, hhidden⟩
                have hvk1 : VKSet s1 a' := Or.inr hkb
                have hvku : VKSet u a' :=
                  (vk_sameOrbit_invariant hu hcls1 a').mpr hvk1
                exact ⟨a', by rw [hnew], hvku⟩
            · obtain ⟨a, hsea, hvk⟩ := hcur
              have hpt := tfc_seat_point_edit hwf_st hstep hrev
              have hsel : seatOf s1 x = seatOf st x := by
                rw [hpt x, ite_eq_right (fun h => hdx h.symm)]
              exact ⟨a, by rw [hsel, hsea], hvk⟩
      exact ih hb_tail hwf1 hcls1 hnext

/-- A bare bottomed king ends on a fuel-set anchor along the bounded play. -/
theorem inl_king_VK_of_bounded
    {u v : State} {play : List Move} {x : Card} {a0 : Anchor}
    (hu : u.WF)
    (hplay : ShufflePlayW u play v)
    (hb : BoundedFrom u u play)
    (hk : x.rank = Rank.king)
    (hhid : (u.piles a0).hidden = [])
    (hseat_u : seatOf u x = some (Sum.inl a0)) :
    ∃ a, seatOf v x = some (Sum.inl a) ∧ VKSet u a := by
  have hkb : KingBottom u a0 := ⟨x, hseat_u, hk, hhid⟩
  exact inl_king_VK_aux hu hseat_u hk hhid hplay hb hu
    (sameOrbitSetoid.iseqv.refl u) ⟨a0, hseat_u, Or.inr hkb⟩

/-! ## Vacancy-freeness along a bounded play -/

/-- No state reachable by a prefix of `l` from `s` has a vacancy. -/
def NoVacancyFrom (s : State) (l : List Move) : Prop :=
  ∀ z, StateOnPlay s l z → NoVacancy z

theorem NoVacancyFrom.head {s s1 : State} {m : Move} {rest : List Move}
    (h : NoVacancyFrom s (m :: rest))
    (hstep : State.step s m = some s1) :
    NoVacancy s1 :=
  h s1 ⟨[m], rest, rfl, run_one hstep⟩

theorem NoVacancyFrom.tail {s s1 : State} {m : Move} {rest : List Move}
    (h : NoVacancyFrom s (m :: rest))
    (hstep : State.step s m = some s1) :
    NoVacancyFrom s1 rest := by
  intro z hz
  obtain ⟨pre, post, hspl, hrun⟩ := hz
  have hspl' : m :: rest = (m :: pre) ++ post := by rw [hspl]; rfl
  have hrun' : s.run (m :: pre) = some z := by
    simp only [State.run, hstep]
    exact hrun
  exact h z ⟨m :: pre, post, hspl', hrun'⟩

/-- The first-vacancy split with the explicit prefix decomposition. -/
theorem first_vacancy_split_decomp {w u : State} {play : List Move}
    (hwf : w.WF) (h : ShufflePlayW w play u)
    (hne : NoVacancy w) (hve : HasVacancy u) :
    ∃ (pre : List Move) (x : Card) (a : Anchor) (s0 s1 : State)
      (suffix : List Move),
      play = pre ++ Move.tabToFound x :: suffix ∧
      NVWalk w pre s0 ∧
      State.step s0 (Move.tabToFound x) = some s1 ∧
      s0.pileOfTop x = some a ∧
      NoVacancy s0 ∧
      (s1.piles a).isEmpty = true ∧
      reversibleAtW s0 (Move.tabToFound x) ∧
      ShufflePlayW s1 suffix u := by
  induction h with
  | nil st =>
      obtain ⟨a, ha⟩ := hve
      exact absurd ha (hne a)
  | @cons st s1 W m rest hrev hstep hrest ih =>
      by_cases hv1 : hasVacancyB s1 = true
      · have hv1' : HasVacancy s1 := hasVacancyB_eq_true.mp hv1
        have hne_false : ∀ a, (st.piles a).isEmpty = false :=
          fun a => bool_eq_false_of_not_true (hne a)
        rcases KingFuel.empty_gain_step_is_raise_or_slide hstep hne_false hv1' with
          ⟨x, a, hm, hp, hvac⟩ | ⟨x, b, hm⟩
        · refine ⟨[], x, a, st, s1, rest, ?_, NVWalk.nil st, ?_, hp, hne,
            hvac, ?_, hrest⟩
          · simp [hm]
          · rw [hm] at hstep; exact hstep
          · rwa [hm] at hrev
        · exfalso
          rw [hm] at hstep
          have hrev' : reversibleAtW st (Move.tabToTab x b) := by
            rwa [hm] at hrev
          have hvno := no_vacancy_after_reversible_slide hwf hstep hrev' hne
          obtain ⟨a, ha⟩ := hv1'
          exact hvno a ha
      · have hv1' : ¬ HasVacancy s1 := fun h => hv1 (hasVacancyB_eq_true.mpr h)
        have hno1 : NoVacancy s1 :=
          (noVacancy_iff_not_hasVacancy s1).mpr hv1'
        have hwf1 : s1.WF := step_wf hwf hstep
        obtain ⟨pre, x, a, s0, s1', suffix, hspl, hpre, hstep', hp, hno0,
          hvac, hrev_raise, hsuffix⟩ := ih hwf1 hno1 hve
        refine ⟨m :: pre, x, a, s0, s1', suffix, ?_,
          NVWalk.cons hrev hne hno1 hstep hpre, hstep', hp, hno0, hvac,
          hrev_raise, hsuffix⟩
        simp [hspl]

/-- No vacancy appears on a play bounded by a vacancy-free source. -/
theorem noVacancyFrom_of_bounded
    {u v : State} {play : List Move}
    (hu : u.WF) (hplay : ShufflePlayW u play v)
    (hb : BoundedFrom u u play) (hne : NoVacancy u) :
    NoVacancyFrom u play := by
  intro z hz
  obtain ⟨pre, post, hspl, hrun⟩ := hz
  obtain ⟨z', hpre, hpost⟩ := ValleyElim.ShufflePlayW_split hplay pre post hspl
  have hz' : z' = z := Option.some.inj ((Walk_run _ hpre).symm.trans hrun)
  subst hz'
  rw [noVacancy_iff_not_hasVacancy]
  intro hvac
  obtain ⟨pre', x, a, s0, s1, suffix, hspl2, hNV, hstep, hp, _hno0,
    hempty, hrev, _hsuffix⟩ :=
    first_vacancy_split_decomp hu hpre hne hvac
  have hwfs0 : s0.WF := NVWalk_wf hNV hu
  have hface_hid := (KingFuel.raise_empties_iff hstep hp).mp hempty
  have hhold : s0.pileHolding x = some a :=
    (pileHolding_eq_some_iff hwfs0).mpr (by rw [hface_hid.1]; simp)
  have hbelow : below x (s0.piles a).faceUp = [] := by
    rw [hface_hid.1]
    simp [below]
  have hseat0 : seatOf s0 x = some (Sum.inl a) :=
    tfc_seatOf_inl_intro hhold hbelow
  have hrank : x.rank = Rank.king :=
    KingFuel.emptying_raise_is_king hstep hrev hp hempty
  have hkb0 : KingBottom s0 a := ⟨x, hseat0, hrank, hface_hid.2⟩
  have hx0 : KingBottomCard s0 x := ⟨a, hkb0, hseat0⟩
  have hseat_back : seatOf s0 x = seatOf u x :=
    NVWalk_seat_back hNV hu hne hx0
  have hseat_u_x : seatOf u x = some (Sum.inl a) := by
    rw [← hseat_back]
    exact hseat0
  have hrun_pre : u.run pre' = some s0 :=
    Walk_run (P := fun st m => reversibleAtW st m) hNV.to_shuffle
  have hrun_s1 : u.run (pre' ++ [Move.tabToFound x]) = some s1 :=
    run_append u pre' [Move.tabToFound x] s0 s1 hrun_pre (run_one hstep)
  have hspl_play : play = (pre' ++ [Move.tabToFound x]) ++ (suffix ++ post) := by
    rw [hspl, hspl2]
    simp [List.append_assoc]
  have hb_s1 : RungLe s1 u := hb _ _ hspl_play s1 hrun_s1
  exact raise_on_bounded_play_false hu hstep hb_s1 hseat_u_x rfl

/-- A bare king is frozen along a bounded play whenever no visited state has a
vacancy: a king's only cargo landing is an empty pile, and raising it would
break the bound. -/
theorem inl_king_fixed_aux
    {u : State} {x : Card} {a0 : Anchor}
    (hu : u.WF)
    (hseat_u : seatOf u x = some (Sum.inl a0))
    (hk : x.rank = Rank.king) :
    ∀ {s W : State} {l : List Move},
      ShufflePlayW s l W → BoundedFrom u s l → NoVacancyFrom s l → s.WF →
      seatOf s x = some (Sum.inl a0) → (s.piles a0).hidden = [] →
      seatOf W x = some (Sum.inl a0) ∧ (W.piles a0).hidden = [] := by
  intro s W l hplay
  induction hplay with
  | nil s =>
      intro _ _ _ hse hhid
      exact ⟨hse, hhid⟩
  | @cons st s1 W m rest hrev hstep hrest ih =>
      intro hb hno hwf_st hse hhid
      have hb_head : RungLe s1 u := hb.head hstep
      have hno_s1 : NoVacancy s1 := hno.head hstep
      have hno_tail : NoVacancyFrom s1 rest := hno.tail hstep
      have hno_st : NoVacancy st := hno st ⟨[], m :: rest, rfl, rfl⟩
      have hb_tail : BoundedFrom u s1 rest := hb.tail hstep
      have hwf1 : s1.WF := step_wf hwf_st hstep
      have hhid1 : (s1.piles a0).hidden = [] := by
        rw [rev_step_hidden_eq hwf_st hstep hrev a0]
        exact hhid
      have hpair : seatOf s1 x = some (Sum.inl a0) ∧
          (s1.piles a0).hidden = [] := by
        cases m with
        | draw =>
            have hse' := (chart_draw hstep).1
            exact ⟨by rw [hse', hse], hhid1⟩
        | wasteToFound y =>
            exact absurd hrev (wasteToFound_not_reversibleAtW st y)
        | wasteToTab y b =>
            exact absurd hrev (wasteToTab_not_reversibleAtW st y b)
        | tabToFound d =>
            by_cases hdx : d = x
            · subst d
              exact (raise_on_bounded_play_false hu hstep hb_head hseat_u rfl).elim
            · have hne : seatOf st x ≠ none := by rw [hse]; simp
              have hsel : seatOf s1 x = seatOf st x :=
                raise_seat_change_of_seated hstep hrev hne
                  (fun h => hdx h.symm)
              exact ⟨by rw [hsel, hse], hhid1⟩
        | foundToTab d b =>
            by_cases hdx : d = x
            · subst d
              exfalso
              obtain ⟨c', htop, hc'c, _hcp, _hs⟩ := step_foundToTab_inv hstep
              have hlast : lastOf (st.found x.suit) = some x := by
                unfold State.foundTop at htop
                rw [hc'c] at htop
                exact htop
              have hcfin : x ∈ st.found x.suit := lastOf_mem hlast
              have hcface : ∃ a, x ∈ (st.piles a).faceUp :=
                mem_faceUp_of_seat hse
              obtain ⟨a', ha'⟩ := hcface
              exact ((mem_found_unique hwf_st hcfin).1 a').2 ha'
            · have hsel : seatOf s1 x = seatOf st x :=
                pull_seat_change hstep x (fun h => hdx h.symm)
              exact ⟨by rw [hsel, hse], hhid1⟩
        | tabToTab d b =>
            by_cases hdx : d = x
            · subst d
              exfalso
              obtain ⟨a_hold, hhold, hcp, hfr, hs⟩ := step_tabToTab_inv hstep
              cases b with
              | inl a' =>
                  exact hno_st a' (canPlace_inl hcp).1
              | inr z =>
                  obtain ⟨k, hloc, hfit⟩ := canPlace_inr hcp
                  rw [canSitOn_king_false hk] at hfit
                  exact absurd hfit (by simp)
            · have hpt := tfc_seat_point_edit hwf_st hstep hrev
              have hsel : seatOf s1 x = seatOf st x := by
                rw [hpt x, ite_eq_right (fun h => hdx h.symm)]
              exact ⟨by rw [hsel, hse], hhid1⟩
      exact ih hb_tail hno_tail hwf1 hpair.1 hpair.2

/-- A bare king with an empty hidden deck is frozen along the whole bounded
play when the source is vacancy-free. -/
theorem inl_king_fixed_of_noVacancy
    {u v : State} {play : List Move} {x : Card} {a0 : Anchor}
    (hu : u.WF)
    (hplay : ShufflePlayW u play v)
    (hb : BoundedFrom u u play)
    (hno_u : NoVacancy u)
    (hk : x.rank = Rank.king)
    (hhid : (u.piles a0).hidden = [])
    (hseat_u : seatOf u x = some (Sum.inl a0)) :
    seatOf u x = seatOf v x := by
  have hno := noVacancyFrom_of_bounded hu hplay hb hno_u
  have hpair := inl_king_fixed_aux hu hseat_u hk hplay hb hno hu hseat_u hhid
  exact hseat_u.trans hpair.1.symm

/-! ## The per-card dichotomy along a bounded play -/

/-- The strong per-card clause with the global maximum replaced by the bounded
path. -/
theorem changed_card_bounded
    {u v : State} {play : List Move} {x : Card}
    (hu : u.WF) (_hv : v.WF)
    (hplay : ShufflePlayW u play v)
    (hb : BoundedFrom u u play)
    (hrung : RungEq u v)
    (hfounds : foundsFixed u v)
    (hchg : seatOf u x ≠ seatOf v x) :
    (((∃ z', seatOf u x = some (Sum.inr z') ∧
        seatOf v x = some (Sum.inr z'.twin)) ∨
      (x.rank = Rank.king ∧ ∃ a',
        seatOf v x = some (Sum.inl a') ∧ VKSet u a')) ∧
     FloaterSpec u x) := by
  have horb : sameOrbitSetoid.r u v :=
    RevEqW_symm (shufflePlayW_revEqW hplay)
  by_cases hnone : seatOf u x = none
  · exact (unseated_change_false hu horb hfounds hnone hchg).elim
  · obtain ⟨b, hb_seat⟩ : ∃ b, seatOf u x = some b := by
      cases h : seatOf u x with
      | none => exact absurd h hnone
      | some b => exact ⟨b, rfl⟩
    cases b with
    | inr z0 =>
        by_cases hnf : FloaterSpec u x
        · obtain ⟨z, hz, hzp⟩ := inr_parent_mem_of_bounded hu hplay hb hb_seat
          rcases hzp with hzz | hzz
          · subst z
            exact absurd (hb_seat.trans hz.symm) hchg
          · have htwin : ∃ z', seatOf u x = some (Sum.inr z') ∧
                seatOf v x = some (Sum.inr z'.twin) :=
              ⟨z0, hb_seat, by rw [hz, hzz]⟩
            exact ⟨Or.inl htwin, hnf⟩
        · exact absurd
            (inr_seat_fixed_of_nonFloater_bounded hu hplay hb hrung hb_seat hnf)
            hchg
    | inl a =>
        by_cases hk : x.rank = Rank.king
        · by_cases hhid : (u.piles a).hidden = []
          · by_cases hnf : FloaterSpec u x
            · obtain ⟨a', hse_v, hvk⟩ :=
                inl_king_VK_of_bounded hu hplay hb hk hhid hb_seat
              exact ⟨Or.inr ⟨hk, a', hse_v, hvk⟩, hnf⟩
            · exfalso
              have hno_u : NoVacancy u :=
                (noVacancy_iff_not_hasVacancy u).mpr (by
                  intro hvac
                  exact hnf (Or.inr ⟨a, hb_seat, hk, hhid, hvac⟩))
              exact hchg
                (inl_king_fixed_of_noVacancy hu hplay hb hno_u hk hhid hb_seat)
          · exfalso
            exact hchg (king_seat_fixed_of_hidden_ne hu hplay hb_seat hhid)
        · exfalso
          exact hchg (hb_seat.trans
            (inl_nonKing_fixed_of_bounded hu hplay hb hk hb_seat).symm)

/-! ## The main theorem -/

/-- **Bounded-path flat normal form.**  A single equal-rung connecting play
whose visited rungs stay below the source's rungs suffices for flat-fiber
connectivity; no global rung maximum, forklessness, or saturation is needed. -/
theorem bareFlatEquiv_of_rungBoundedPath
    {u v : State}
    (hu : u.WF) (hv : v.WF)
    (hpath : RungBoundedPath u v)
    (hrung : RungEq u v) :
    BareFlatEquiv u v := by
  obtain ⟨play, hplay, hbound⟩ := hpath
  have hb : BoundedFrom u u play := boundedFrom_of_onPlay hbound
  have horb : sameOrbitSetoid.r u v :=
    RevEqW_symm (shufflePlayW_revEqW hplay)
  have hfounds : foundsFixed u v :=
    fun s => found_congr_of_rungs hu hv (hrung s)
  have hper : ∀ x, seatOf u x ≠ seatOf v x →
      (((∃ z', seatOf u x = some (Sum.inr z') ∧
          seatOf v x = some (Sum.inr z'.twin)) ∨
       (x.rank = Rank.king ∧ ∃ a',
          seatOf v x = some (Sum.inl a') ∧ VKSet u a')) ∧
       FloaterSpec u x) :=
    fun x hchg => changed_card_bounded hu hv hplay hb hrung hfounds hchg
  exact bareFlat_of_vk hu hv horb hper (boardFixed_of_sameOrbit hu horb) hfounds

/-- At a both-empty draw zone a flat letter is a cargo letter, and the zone
stays both-empty. -/
theorem flatStep_cargo_of_bothEmpty {w u : State}
    (hs : w.stock = []) (hw : w.waste = []) (h : FlatStep w u) :
    CargoLeg w u ∧ u.stock = [] ∧ u.waste = [] := by
  cases h with
  | cargo c b hstep hrev =>
      have hleg : CargoLeg w u := ⟨c, b, hstep, hrev⟩
      exact ⟨hleg, (cargoLeg_stock hleg).symm.trans hs,
        (cargoLeg_waste hleg).symm.trans hw⟩
  | draw hstep _hrev =>
      exfalso
      have hdead : w.stepDraw = none := by
        rw [show w.stepDraw = State.dealStock (State.recycle w) from rfl,
          recycle_allEmpty w hs hw, dealStock_nil w hs]
      have hstep' : State.step w Move.draw = some u := hstep
      rw [show State.step w Move.draw = w.stepDraw from rfl, hdead] at hstep'
      exact absurd hstep' (by simp)

/-- A flat path from a both-empty draw zone is a cargo path. -/
theorem flatPath_cargoPath_of_bothEmpty {a b : State}
    (hs : a.stock = []) (hw : a.waste = [])
    (h : FlatPath a b) : CargoPath a b := by
  induction h with
  | refl => exact Steps.refl _
  | cons hstep _ ih =>
      obtain ⟨hleg, hs', hw'⟩ := flatStep_cargo_of_bothEmpty hs hw hstep
      exact Steps.cons hleg (ih hs' hw')

/-- The boundary pair `vcS/vcT` is not flat. -/
theorem vc_not_bareFlat_local : ¬ BareFlatEquiv vcS vcT := by
  intro h
  exact vc_not_cargoPath (flatPath_cargoPath_of_bothEmpty rfl rfl h.1)

/-- The boundary pair `vcS/vcT` admits **no** rung-bounded path: otherwise the
main theorem would put it in one flat fiber, contradicting the boundary
separation. -/
theorem vcS_vcT_not_rungBounded : ¬ RungBoundedPath vcS vcT := by
  intro h
  exact vc_not_bareFlat_local
    (bareFlatEquiv_of_rungBoundedPath vcS_wf vcT_wf h vc_rungs)

/-- A state on a witness play is a class-mate of the play's start. -/
theorem sameOrbit_of_onPlay {u v : State} {play : List Move}
    (hplay : ShufflePlayW u play v) {z : State}
    (hz : StateOnPlay u play z) : sameOrbitSetoid.r u z := by
  obtain ⟨pre, post, hspl, hrun⟩ := hz
  obtain ⟨mid, hpre, _hpost⟩ :=
    Bubble.walk_split pre (st := u) (B := v) (rest := post)
      (by simpa [hspl] using hplay)
  have hmid : mid = z :=
    Option.some.inj ((Walk_run _ hpre).symm.trans hrun)
  subst mid
  exact sameOrbitSetoid.iseqv.symm (shufflePlayW_revEqW hpre)

/-- **The forkless flat normal form via the bounded-path theorem.** -/
theorem forklessFlatNormalWF_proved : ForklessFlatNormalWF := by
  intro u v hu hsu hsv horb hfrk
  have huv : RungEq u v :=
    forkless_rungs_agree_proved hu horb hfrk hsu hsv
  have hmax : ∀ z, sameOrbitSetoid.r u z → RungLe z u := by
    intro z huz σ
    by_cases hle : rungAt z σ ≤ rungAt u σ
    · exact hle
    · exfalso
      have hlt : rungAt u σ < rungAt z σ := Nat.lt_of_not_ge hle
      have hzwf : z.WF := wf_of_sameOrbit huz hu
      obtain ⟨w, hzw, _hwf, hwsat, hzle⟩ :=
        ForklessTop.exists_saturated_above z hzwf
      have huw : sameOrbitSetoid.r u w :=
        sameOrbitSetoid.iseqv.trans huz hzw
      have hruw : RungEq u w :=
        forkless_rungs_agree_proved hu huw hfrk hsu hwsat
      have hltw : rungAt u σ < rungAt w σ :=
        Nat.lt_of_lt_of_le hlt (hzle σ)
      have heq : rungAt u σ = rungAt w σ := hruw σ
      omega
  have horb_keep := horb
  obtain ⟨-, -, play, hplay⟩ := horb
  have hpath : RungBoundedPath u v := by
    refine ⟨play, hplay, ?_⟩
    intro z hz
    exact hmax z (sameOrbit_of_onPlay hplay hz)
  exact bareFlatEquiv_of_rungBoundedPath hu
    (wf_of_sameOrbit horb_keep hu) hpath huv

#print axioms sameOrbit_of_onPlay
#print axioms forklessFlatNormalWF_proved
#print axioms bareFlatEquiv_of_rungBoundedPath
#print axioms changed_card_bounded
#print axioms noVacancyFrom_of_bounded
#print axioms inl_king_fixed_of_noVacancy
#print axioms vcS_vcT_not_rungBounded
