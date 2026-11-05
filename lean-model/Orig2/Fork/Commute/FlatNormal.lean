import Orig2.Fork.Class.ForkOneColourClosure
import Orig2.Fork.Class.ForkRaiseReorder
import Orig2.Fiber.FloatFiber
import Orig2.Fiber.SeatMateStack
import Orig2.Fiber.FiberTransfer
import Orig2.Fiber.LockRung
import Orig2.Fiber.FreeOrbit
import Orig2.Fiber.OrbitFactor
import Orig2.Fiber.FloatOrbit
import Orig2.Fiber.SWDichotomy
import Orig2.Claims.Chart
import Orig2.Fork.Commute.ForklessTop
import Orig2.Fork.Commute.Campaign
import Orig2.Fork.Class.ForkTwinAt
import Orig2.Fork.Class.ForkPosition
import Orig2.Fork.Local.ForkCriticalPair


/-!
# Orig2.Fork.Commute.FlatNormal - flat-fiber support kit

Draw/readout kit, `bareFlat_of_vk`, `NVWalk_seat_back`, and
`boardFixed_of_sameOrbit`.  The flat-normal capstone now lives in
`Orig2/Fork/Commute/BoundedFlatPath.lean`.
-/

set_option autoImplicit false
set_option linter.unnecessarySimpa false

open OneColourClosure

/-- A draw-only witness play is a flat path. -/
theorem drawPlayW_flatPath {u v : State} {play : List Move}
    (h : DrawPlayW u play v) : FlatPath u v := by
  obtain ⟨hplay, hdraw⟩ := h
  revert hdraw
  induction hplay with
  | nil st =>
      intro _hdraw
      exact Steps.refl st
  | @cons st s1 W m rest hrev hstep hrest ih =>
      intro hdraw
      have hm : m = Move.draw := hdraw m (by simp)
      subst m
      have hrestDraw : ∀ x ∈ rest, x = Move.draw := by
        intro x hx
        exact hdraw x (by simp [hx])
      exact Steps.cons (FlatStep.draw hstep hrev) (ih hrestDraw)

/-- A draw-only play preserves seats, foundations, board readouts and the
draw pool. -/
theorem drawPlayW_readouts {u v : State} {play : List Move}
    (h : DrawPlayW u play v) :
    (∀ c : Card, seatOf v c = seatOf u c) ∧
      foundsFixed u v ∧ boardFixed u v ∧ drawPool u = drawPool v := by
  obtain ⟨hplay, hdraw⟩ := h
  revert hdraw
  induction hplay with
  | nil st =>
      intro _hdraw
      exact ⟨fun _ => rfl, fun _ => rfl, ⟨fun _ => rfl, rfl⟩, rfl⟩
  | @cons st s1 W m rest hrev hstep hrest ih =>
      intro hdraw
      have hm : m = Move.draw := hdraw m (by simp)
      subst m
      have hrestDraw : ∀ x ∈ rest, x = Move.draw := by
        intro x hx
        exact hdraw x (by simp [hx])
      obtain ⟨hseat1, hfound1, hboard1, hpool1⟩ := chart_draw hstep
      obtain ⟨hseat2, hfound2, hboard2, hpool2⟩ := ih hrestDraw
      refine ⟨fun c => (hseat2 c).trans (hseat1 c), ?_, ?_, hpool1.trans hpool2⟩
      · intro s
        exact (hfound1 s).trans (hfound2 s)
      · exact ⟨fun a => (hboard1.1 a).trans (hboard2.1 a),
          hboard1.2.trans hboard2.2⟩

/-- Flat paths compose. -/
theorem flatPath_trans {a b c : State} (h1 : FlatPath a b) (h2 : FlatPath b c) :
    FlatPath a c := by
  induction h1 with
  | refl _ => exact h2
  | cons h _ ih => exact Steps.cons h (ih h2)

/-- A non-draw reversible step preserves the pool, the cut and the board
readouts. -/
theorem boardStep_readouts
    {st s1 : State} {m : Move}
    (hwf : st.WF) (hstep : State.step st m = some s1)
    (hrev : reversibleAtW st m) (hm : m ≠ Move.draw) :
    drawPool st = drawPool s1 ∧ cutOf st = cutOf s1 ∧ boardFixed st s1 := by
  cases m with
  | draw => exact absurd rfl hm
  | wasteToFound x => exact absurd hrev (wasteToFound_not_reversibleAtW st x)
  | wasteToTab x b => exact absurd hrev (wasteToTab_not_reversibleAtW st x b)
  | tabToFound c =>
      obtain ⟨_hn, a, hpa, hs⟩ := step_tabToFound_inv hstep
      subst s1
      refine ⟨rfl, rfl, ⟨fun a' => ?_, rfl⟩⟩
      exact (rev_step_hidden_eq hwf hstep hrev a').symm
  | foundToTab c b =>
      obtain ⟨x, htop, hxc, hcp, hs⟩ := step_foundToTab_inv hstep
      subst s1
      refine ⟨?_, ?_, ⟨fun a' => ?_, ?_⟩⟩
      · simp [drawPool, putCard_stock, setFound_stock, putCard_waste, setFound_waste]
      · simp [cutOf, putCard_stock, setFound_stock]
      · exact (rev_step_hidden_eq hwf hstep hrev a').symm
      · rw [putCard_drawStep, setFound_drawStep]
  | tabToTab c b =>
      obtain ⟨hbf, _hff, hdp, hco⟩ := tfa_slide_conserves hwf hstep hrev
      exact ⟨hdp, hco, hbf⟩

/-- A draw-free shuffle play preserves the pool, the cut and the board readouts. -/
theorem noDrawPlay_readouts
    {u v : State} {play : List Move}
    (hwf : u.WF) (hplay : ShufflePlayW u play v)
    (hno : ∀ m ∈ play, m ≠ Move.draw) :
    drawPool u = drawPool v ∧ cutOf u = cutOf v ∧ boardFixed u v := by
  revert hwf hno
  induction hplay with
  | nil st =>
      intro _hwf _hno
      exact ⟨rfl, rfl, ⟨fun _ => rfl, rfl⟩⟩
  | @cons st s1 W m rest hrev hstep hrest ih =>
      intro hwf hno
      have hm : m ≠ Move.draw := hno m (by simp)
      obtain ⟨hdp1, hcut1, hbf1⟩ := boardStep_readouts hwf hstep hrev hm
      have hwf1 : s1.WF := step_wf hwf hstep
      have hnoRest : ∀ x ∈ rest, x ≠ Move.draw := by
        intro x hx
        exact hno x (by simp [hx])
      obtain ⟨hdp2, hcut2, hbf2⟩ := ih hwf1 hnoRest
      refine ⟨hdp1.trans hdp2, hcut1.trans hcut2, ?_⟩
      exact ⟨fun a => (hbf1.1 a).trans (hbf2.1 a),
        hbf1.2.trans hbf2.2⟩

/-- `NoDrawPlayW` readouts. -/
theorem noDrawPlayW_readouts {u v : State} (hu : u.WF) (h : NoDrawPlayW u v) :
    drawPool u = drawPool v ∧ cutOf u = cutOf v ∧ boardFixed u v := by
  obtain ⟨play, hplay, hno, _back, _hback, _hnoback⟩ := h
  exact noDrawPlay_readouts hu hplay hno


theorem le_rung_of_seated
    {st : State} {c : Card}
    (hwf : st.WF) (h : ∃ b : Base, seatOf st c = some b) :
    rungAt st c.suit ≤ c.rank.toIdx := by
  rcases h with ⟨b, hb⟩
  cases b with
  | inr z => exact le_rung_of_not_found hwf (cover_not_found hwf hb)
  | inl a =>
      have hmem : c ∈ (st.piles a).faceUp :=
        pileHolding_mem (tfc_seatOf_of_inl hb).1
      have hnotfound : c ∉ st.found c.suit := by
        intro hf
        exact ((mem_found_unique hwf hf).1 a).2 hmem
      exact le_rung_of_not_found hwf hnotfound

/-- A member that is not the last element has an immediate successor. -/
private theorem exists_succ_of_mem_of_last_ne {l : List Card} {z : Card}
    (hz : z ∈ l) (hlast : lastOf l ≠ some z) :
    ∃ pre d post, l = pre ++ z :: d :: post := by
  rcases List.mem_iff_append.mp hz with ⟨pre, post, rfl⟩
  cases post with
  | nil =>
      exfalso
      apply hlast
      simpa using lastOf_snoc (front := pre) (c := z)
  | cons d post =>
      exact ⟨pre, d, post, rfl⟩

/-- A face-up card with no sitter is the top of its pile. -/
theorem top_of_faceUp_no_sitter
    {st : State} {z : Card} {a : Anchor}
    (hwf : st.WF)
    (hmem : z ∈ (st.piles a).faceUp)
    (hno : ¬ ∃ d, seatOf st d = some (Sum.inr z)) :
    st.pileOfTop z = some a := by
  by_cases hlast : lastOf (st.piles a).faceUp = some z
  · exact (pileOfTop_eq_some_iff hwf).mpr hlast
  · obtain ⟨pre, d, post, hdecomp⟩ :=
      exists_succ_of_mem_of_last_ne hmem hlast
    have hdmem : d ∈ (st.piles a).faceUp := by
      rw [hdecomp]
      simp
    have hhold : st.pileHolding d = some a :=
      (pileHolding_eq_some_iff hwf).mpr hdmem
    have hdpre : d ∉ pre := by
      intro hd
      have hnd : (st.piles a).faceUp.Nodup := runOK_nodup (hwf.2.1 a)
      rw [hdecomp] at hnd
      exact (List.nodup_append.mp hnd).2.2 d hd d (by simp) rfl
    have hzne : z ≠ d := by
      have hndall : (pre ++ z :: d :: post).Nodup := by
        rw [← hdecomp]
        exact runOK_nodup (hwf.2.1 a)
      rcases List.nodup_append.mp hndall with ⟨_, hnd, _⟩
      have hznot : z ∉ d :: post := (List.nodup_cons.mp hnd).1
      intro hzd
      exact hznot (by rw [hzd]; simp)
    have hbelow : below d (st.piles a).faceUp = pre ++ [z] := by
      rw [hdecomp, below_append_notmem hdpre]
      rw [below_cons d z (d :: post), ite_eq_right hzne, below_cons_self]
    have hseat : seatOf st d = some (Sum.inr z) := by
      have hlastz : (pre ++ [z]).getLast? = some z := by
        simpa [lastOf] using lastOf_snoc (front := pre) (c := z)
      rw [tfc_seatOf_pair hhold, hbelow, hlastz]
    exact absurd ⟨d, hseat⟩ hno

theorem not_faceUp_target_of_twin_not_seated
    {u : State} {c z0 : Card}
    (hu : u.WF)
    (hseat_c : seatOf u c = some (Sum.inr z0))
    (hnfu : ¬ FloaterSpec u c)
    (hct : seatOf u c.twin ≠ some (Sum.inr z0.twin)) :
    ¬ ∃ a, z0.twin ∈ (u.piles a).faceUp := by
  rintro ⟨a, hmema⟩
  have hno : ¬ ∃ d, seatOf u d = some (Sum.inr z0.twin) := by
    rintro ⟨d, hd⟩
    have hdt : d = c.twin := blocker_eq_twin hu hseat_c hd
    subst hdt
    exact hct hd
  have htop : u.pileOfTop z0.twin = some a :=
    top_of_faceUp_no_sitter hu hmema hno
  obtain ⟨a0, hhold, -, -⟩ := tfc_seatOf_of_inr hseat_c
  exact hnfu (Or.inl ⟨z0, a0, hseat_c, hhold, Or.inl ⟨a, htop⟩⟩)

theorem pileHolding_none_of_seatOf_noneT {s : State} {c : Card}
    (h : seatOf s c = none) : s.pileHolding c = none := by
  cases hph : s.pileHolding c with
  | none => rfl
  | some k =>
      rw [tfc_seatOf_pair hph] at h
      cases hg : List.getLast? (below c (s.piles k).faceUp) with
      | none => rw [hg] at h; exact absurd h (by simp)
      | some z => rw [hg] at h; exact absurd h (by simp)

/-- A face-up member is seated. -/
theorem seatOf_ne_none_of_mem_faceUpT {s : State} {c : Card} {a : Anchor}
    (h : c ∈ (s.piles a).faceUp) : seatOf s c ≠ none := by
  intro hse
  exact (tfc_not_mem_faceUp_of_holdNone (pileHolding_none_of_seatOf_noneT hse) a) h

/-- A card held by a pile is seated. -/
theorem seatOf_ne_none_of_pileHoldingT {s : State} {c : Card} {a : Anchor}
    (h : s.pileHolding c = some a) : seatOf s c ≠ none := by
  rw [tfc_seatOf_pair h]
  split <;> exact Option.some_ne_none _

/-- An unseated card is in no face-up pile. -/
theorem not_mem_faceUp_of_seatOf_noneT {s : State} {c : Card}
    (h : seatOf s c = none) (a : Anchor) : c ∉ (s.piles a).faceUp :=
  tfc_not_mem_faceUp_of_holdNone (pileHolding_none_of_seatOf_noneT h) a

/-- **The boarding step lemma.**  Through a reversible letter, an
off-board card that is not on its foundation row stays off the
board: every boarding route except the pull is irreversible (the
waste routes never undo; a reveal strictly drops `hiddenTotal`, and
`not_W_of_desc` kills it), and the pull needs foundation membership,
which only the raise of that very card could grant — and the raise
needs the card seated. -/
theorem unseated_track_stepT {u v : State} {m : Move} {c : Card}
    (hwf : u.WF) (hstep : State.step u m = some v) (hrev : reversibleAtW u m)
    (hseat : seatOf u c = none) (hnotfound : c ∉ u.found c.suit) :
    seatOf v c = none ∧ c ∉ v.found c.suit := by
  cases m with
  | draw =>
      have hse := (chart_draw hstep).1
      have hfo := (chart_draw hstep).2.1
      refine ⟨by rw [hse c]; exact hseat, ?_⟩
      intro hmem
      exact hnotfound (by rw [hfo c.suit]; exact hmem)
  | wasteToFound y => exact absurd hrev (wasteToFound_not_reversibleAtW u y)
  | wasteToTab y b => exact absurd hrev (wasteToTab_not_reversibleAtW u y b)
  | tabToFound y =>
      obtain ⟨-, a, hpa, hs⟩ := step_tabToFound_inv hstep
      have hcy : c ≠ y := by
        intro hcy
        subst hcy
        obtain ⟨-, hlast⟩ := tfc_pileOfTop_top hpa
        exact (seatOf_ne_none_of_mem_faceUpT (lastOf_mem hlast)) hseat
      refine ⟨?_, ?_⟩
      · apply tfc_seatOf_none
        apply tfc_pileHolding_none
        intro a'
        by_cases haa' : a' = a
        · rw [haa']
          have hpilea : v.piles a =
              Pile.afterRunRemoved (u.piles a) (chop (u.piles a).faceUp) := by
            rw [hs]
            show (if a = a then
                Pile.afterRunRemoved (u.piles a) (chop (u.piles a).faceUp)
              else u.piles a) =
              Pile.afterRunRemoved (u.piles a) (chop (u.piles a).faceUp)
            rw [ite_eq_left rfl]
          cases hchop : chop (u.piles a).faceUp with
          | cons z zs =>
              have hcchop : c ∉ z :: zs := by
                have hmchop : c ∉ chop (u.piles a).faceUp := fun hc =>
                  not_mem_faceUp_of_seatOf_noneT hseat a (chop_mem hc)
                rw [hchop] at hmchop
                exact hmchop
              rw [hpilea, hchop]
              exact hcchop
          | nil =>
              cases hhidden : (u.piles a).hidden with
              | cons h t =>
                  exfalso
                  have hdrop : hiddenTotal v + 1 ≤ hiddenTotal u :=
                    hiddenTotal_step_tabToFound_reveal hstep hpa hchop
                      (by rw [hhidden]; simp)
                  exact absurd hrev (not_W_of_desc hiddenTotal
                    (fun s m s' hst => hiddenTotal_step hst) hstep
                    (Nat.lt_of_succ_le hdrop))
              | nil =>
                  rw [hpilea, hchop]
                  simp [Pile.afterRunRemoved, Pile.revealTop, hhidden]
        · rw [hs]
          show c ∉ (if a' = a then
              Pile.afterRunRemoved (u.piles a) (chop (u.piles a).faceUp)
            else u.piles a').faceUp
          rw [ite_eq_right haa']
          exact not_mem_faceUp_of_seatOf_noneT hseat a'
      · intro hmem
        rw [hs] at hmem
        by_cases hys : c.suit = y.suit
        · rw [hys] at hmem hnotfound
          rw [setFound_found_self] at hmem
          rcases List.mem_append.mp hmem with h' | h'
          · exact hnotfound h'
          · exact hcy (List.mem_singleton.mp h')
        · rw [setFound_found_ne hys] at hmem
          exact hnotfound hmem
  | foundToTab y b =>
      have hcy : c ≠ y := by
        intro hcy
        obtain ⟨c', htop, hc'c, -, -⟩ := step_foundToTab_inv hstep
        rw [hc'c] at htop
        subst hcy
        exact hnotfound (by simpa [State.foundTop] using lastOf_mem htop)
      refine ⟨by rw [pull_seat_change hstep c hcy]; exact hseat, ?_⟩
      intro hmem
      obtain ⟨-, -, -, -, hs⟩ := step_foundToTab_inv hstep
      rw [hs] at hmem
      have hfound : ((u.setFound y.suit (chop (u.found y.suit))).putCard y b).found
          = (u.setFound y.suit (chop (u.found y.suit))).found := by
        cases b with
        | inl t => rw [putCard_inl_found]
        | inr z => rw [putCard_inr_found]
      rw [hfound] at hmem
      by_cases hys : c.suit = y.suit
      · rw [hys] at hmem hnotfound
        rw [setFound_found_self] at hmem
        exact hnotfound (chop_mem hmem)
      · rw [setFound_found_ne hys] at hmem
        exact hnotfound hmem
  | tabToTab y b =>
      obtain ⟨a0, hhold, -, -, hs⟩ := step_tabToTab_inv hstep
      have hcy : c ≠ y := by
        intro hcon
        subst hcon
        exact (seatOf_ne_none_of_mem_faceUpT (pileHolding_mem hhold)) hseat
      refine ⟨by
          rw [tfc_seat_point_edit hwf hstep hrev c, ite_eq_right hcy]
          exact hseat, ?_⟩
      intro hmem
      rw [hs, putRun_found, setPile_found] at hmem
      exact hnotfound hmem

/-- **The boarding play lemma.**  Along a whole reversible play, an
off-board card that is not on its foundation row stays off the
board. -/
theorem unseated_track_playT {u v : State} {c : Card} {play : List Move}
    (hwf : u.WF) (hplay : ShufflePlayW u play v)
    (hseat : seatOf u c = none) (hnotfound : c ∉ u.found c.suit) :
    seatOf v c = none ∧ c ∉ v.found c.suit := by
  revert hwf hseat hnotfound
  induction hplay with
  | nil st =>
      intro _ hseat hnotfound
      exact ⟨hseat, hnotfound⟩
  | @cons st s1 W m rest' hrev hstep hrest ih =>
      intro hwf hseat hnotfound
      obtain ⟨hseat1, hnotfound1⟩ := unseated_track_stepT hwf hstep hrev hseat hnotfound
      exact ih (step_wf hwf hstep) hseat1 hnotfound1

/-- A foundation card is unseated. -/
theorem seatOf_none_of_mem_foundT {s : State} (hwf : s.WF) {c : Card}
    (h : c ∈ s.found c.suit) : seatOf s c = none := by
  apply tfc_seatOf_none
  apply tfc_pileHolding_none
  intro a hmem
  exact ((mem_found_unique hwf h).1 a).2 hmem

/-- An unseated origin cannot become seated under foundation agreement. -/
theorem unseated_change_false
    {w u : State} {x : Card}
    (hw : w.WF)
    (horb : sameOrbitSetoid.r w u)
    (hfounds : foundsFixed w u)
    (hseat : seatOf w x = none)
    (hchg : seatOf w x ≠ seatOf u x) :
    False := by
  have hu : u.WF := wf_of_sameOrbit horb hw
  obtain ⟨_play_uw, _h_uw, _play_wu, h_wu⟩ := horb
  by_cases hf : x ∈ w.found x.suit
  · have huf : x ∈ u.found x.suit := by
      rw [← hfounds x.suit]
      exact hf
    have hnone := seatOf_none_of_mem_foundT hu huf
    exact hchg (hseat.trans hnone.symm)
  · have hnone := (unseated_track_playT hw h_wu hseat hf).1
    exact hchg (hseat.trans hnone.symm)

/-- **The flat iff-vk assembly.**  Under the same orbit, the per-card
twin/king/floater clause, `boardFixed`, and `foundsFixed` already give
`BareFlatEquiv`; `drawPool` and `cutOf` are automatic. -/
theorem bareFlat_of_vk
    {u v : State}
    (hu : u.WF) (hv : v.WF)
    (horb : sameOrbitSetoid.r u v)
    (hper : ∀ x, seatOf u x ≠ seatOf v x →
      (((∃ z', seatOf u x = some (Sum.inr z') ∧
          seatOf v x = some (Sum.inr z'.twin)) ∨
       (x.rank = Rank.king ∧ ∃ a',
          seatOf v x = some (Sum.inl a') ∧ VKSet u a')) ∧
       FloaterSpec u x))
    (_hboard : boardFixed u v)
    (hfounds : foundsFixed u v) :
    BareFlatEquiv u v := by
  obtain ⟨z, hnoDraw, hsw⟩ := (sameOrbit_factor hu hv).mp horb
  obtain ⟨hpool_uz, hcut_uz, hboard_uz⟩ := noDrawPlayW_readouts hu hnoDraw
  obtain ⟨play, hplay, hno, _back, _hback, _hnoback⟩ := hnoDraw
  have huz_orbit : sameOrbitSetoid.r u z :=
    RevEqW_symm (shufflePlayW_revEqW hplay)
  have hzwf : z.WF := wf_of_sameOrbit huz_orbit hu
  obtain ⟨p, q, hdp, hdq⟩ := hsw
  obtain ⟨hseatZV, hfound_zv, _hboard_zv, _hpool_zv⟩ := drawPlayW_readouts hdp
  have hfound_uz : foundsFixed u z := by
    intro s
    exact (hfounds s).trans (hfound_zv s).symm
  have hper_uz : ∀ x, seatOf u x ≠ seatOf z x →
      (((∃ z', seatOf u x = some (Sum.inr z') ∧
          seatOf z x = some (Sum.inr z'.twin)) ∨
       (x.rank = Rank.king ∧ ∃ a',
          seatOf z x = some (Sum.inl a') ∧ VKSet u a')) ∧
       FloaterSpec u x) := by
    intro x hchg
    have hchgv : seatOf u x ≠ seatOf v x := by
      intro h
      exact hchg (h.trans (hseatZV x))
    have h := hper x hchgv
    simpa [hseatZV x] using h
  have hbc : BareCargoEquiv u z :=
    (bareCargo_iff_vk hu hzwf).mpr
      ⟨hper_uz, hboard_uz, hfound_uz, hpool_uz, hcut_uz⟩
  have hzv : BareFlatEquiv z v :=
    ⟨drawPlayW_flatPath hdp, drawPlayW_flatPath hdq⟩
  exact bareFlatEquiv_trans (bareCargo_bareFlat hbc) hzv

/-- Along a no-vacancy `NVWalk`, a card bare-bottomed at the end was already
bare-bottomed at the start, and its seat is unchanged. -/
theorem NVWalk_seat_back
    {w s0 : State} {pre : List Move} {x : Card}
    (h : NVWalk w pre s0)
    (hwf : w.WF)
    (hno : NoVacancy w)
    (hx : KingBottomCard s0 x) :
    seatOf s0 x = seatOf w x := by
  obtain ⟨a, hkb0, hseat0⟩ := hx
  have hvk0 : VKSet s0 a := Or.inr hkb0
  have hvkw : VKSet w a := (vk_NVWalk h hwf a).mpr hvk0
  have hkbw : KingBottom w a :=
    (vkSet_kingBottom_of_no_vacancy hno a).mp hvkw
  obtain ⟨y, hseat_w_y, hyrank, hyhid⟩ := hkbw
  have hkbw' : KingBottom w a := ⟨y, hseat_w_y, hyrank, hyhid⟩
  have hyw : KingBottomCard w y := ⟨a, hkbw', hseat_w_y⟩
  have hseat_y : seatOf s0 y = seatOf w y :=
    seatOf_NVWalk h hwf hyw
  have hseat_s0_y : seatOf s0 y = some (Sum.inl a) := by
    rw [hseat_y, hseat_w_y]
  have hxy : x = y := king_seat_injective hseat0 hseat_s0_y
  subst x
  exact seatOf_NVWalk h hwf hyw

/-- `boardFixed` is invariant under the whole orbit. -/
theorem boardFixed_of_sameOrbit
    {u v : State} (hu : u.WF) (h : sameOrbitSetoid.r u v) :
    boardFixed u v := by
  have hv : v.WF := wf_of_sameOrbit h hu
  obtain ⟨z, hno, hsw⟩ := (sameOrbit_factor hu hv).mp h
  obtain ⟨_pool_uz, _cut_uz, hboard_uz⟩ := noDrawPlayW_readouts hu hno
  obtain ⟨p, q, hdp, _hdq⟩ := hsw
  obtain ⟨_seat_zv, _found_zv, hboard_zv, _pool_zv⟩ := drawPlayW_readouts hdp
  exact ⟨fun a => (hboard_uz.1 a).trans (hboard_zv.1 a),
    hboard_uz.2.trans hboard_zv.2⟩



/-- Boolean form of `FloaterSpec`, used to keep the flat-normal proof
choice-free. -/
def floaterSpecB (st : State) (c : Card) : Bool :=
  match seatOf st c with
  | none => false
  | some (Sum.inl a) =>
      decide (c.rank = Rank.king) && decide ((st.piles a).hidden = []) &&
        hasVacancyB st
  | some (Sum.inr z) =>
      match st.pileHolding c with
      | none => false
      | some _ =>
          decide (st.pileOfTop z.twin ≠ none) ||
            (decide (c.rank = Rank.king) && hasVacancyB st)

theorem floaterSpecB_eq_true {st : State} {c : Card} :
    floaterSpecB st c = true ↔ FloaterSpec st c := by
  unfold floaterSpecB FloaterSpec
  cases hseat : seatOf st c with
  | none => simp_all
  | some b =>
      cases b with
      | inl a =>
          simp_all [Bool.and_eq_true, hasVacancyB_eq_true, HasVacancy,
            and_assoc]
      | inr z =>
          cases hhold : st.pileHolding c with
          | none => simp_all
          | some a =>
              simp_all [Bool.or_eq_true, Bool.and_eq_true,
                hasVacancyB_eq_true, Option.ne_none_iff_exists, HasVacancy]
              constructor
              · rintro (⟨x, hx⟩ | h)
                · exact Or.inl ⟨x, hx.symm⟩
                · exact Or.inr h
              · rintro (⟨k, hk⟩ | h)
                · exact Or.inl ⟨k, hk.symm⟩
                · exact Or.inr h

instance floaterSpecDecidable (st : State) (c : Card) :
    Decidable (FloaterSpec st c) :=
  decidable_of_iff (floaterSpecB st c = true) floaterSpecB_eq_true

/-! ## Audit battery -/

#print axioms bareFlat_of_vk
#print axioms NVWalk_seat_back
#print axioms boardFixed_of_sameOrbit
