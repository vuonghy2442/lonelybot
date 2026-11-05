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
# Orig2.Fork.Commute.FlatNormal - the forkless flat normal form

The per-card seat analysis and the `bareFlat_of_vk` bridge for the flat-fiber
normal form.  The capstone `forklessFlatNormalWF_proved` now lives in
`Orig2/Fork/Commute/BoundedFlatPath.lean`, where it is derived from the
stronger bounded-path theorem.
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

/-- `u` is a componentwise rung maximum of its orbit. -/
def IsRungMax (u : State) : Prop :=
  ∀ w, sameOrbitSetoid.r u w → RungLe w u

/-- If `u` is a maximum and `u,v` have equal rungs, then `v` is a maximum. -/
theorem isRungMax_of_rungEq {u v : State}
    (huv : sameOrbitSetoid.r u v) (hr : RungEq u v)
    (h : IsRungMax u) : IsRungMax v := by
  intro w hvw σ
  have huw : sameOrbitSetoid.r u w :=
    sameOrbitSetoid.iseqv.trans huv hvw
  calc
    rungAt w σ ≤ rungAt u σ := h w huw σ
    _ = rungAt v σ := hr σ

/-- Two maxima in one orbit are rung-equal: each is below the other, so
`Nat.le_antisymm` gives componentwise equality. -/
theorem rungEq_of_isRungMax_pair {u v : State}
    (huv : sameOrbitSetoid.r u v)
    (hu : IsRungMax u) (hv : IsRungMax v) : RungEq u v := by
  intro σ
  exact Nat.le_antisymm
    (hv u (sameOrbitSetoid.iseqv.symm huv) σ)
    (hu v huv σ)

/-- Symmetric maxima hypothesis.  `RungEq u v` is derived, not assumed. -/
def IsRungMaxPair (u v : State) : Prop :=
  sameOrbitSetoid.r u v ∧ IsRungMax u ∧ IsRungMax v

/-- Both are maxima, and no other class-mate attains the maximum. -/
def IsStrictRungMax (u v : State) : Prop :=
  IsRungMaxPair u v ∧
  (∀ w, sameOrbitSetoid.r u w → RungEq w u → w = u ∨ w = v)

/-- **Symmetric twin-raise transfer.**  If `c.twin` is S-live, `c` is
next-up, and `c.twin` is sited (equivalently `c` is face-up with company below,
or a bare king), then `c` is S-live too.  This is
`TwinAt.canRaiseS_twin_of_pin_and_sited` applied at `c.twin`. -/
theorem canRaiseS_of_twin_raise_sited
    {F : State} {c : Card}
    (hF : F.WF)
    (hS : CanRaiseS F c.twin)
    (hpin : F.nextUp c = true)
    (hsit : TwinKit.TwinSited F c.twin) :
    CanRaiseS F c := by
  have hpin' : F.nextUp c.twin.twin = true := by
    simpa [card_twin_twin] using hpin
  simpa [card_twin_twin] using
    (TwinAt.canRaiseS_twin_of_pin_and_sited hF hS hpin' hsit)


/-- **The `SwappableIn` arm, rank form.**  At a rung top, a strict twin swap
of a seated pair is impossible when both twins are above the top in their
suits: `swappableIn_iff_raise_reachable` would produce a class-mate where one
twin is raisable, and `canRaiseS_rung` pins that mate's suit rung at the twin's
rank, contradicting the top. -/
theorem not_swappableIn_of_rank_gt_rungMax
    {u : State} {c z : Card}
    (hu : u.WF)
    (hmax : IsRungMax u)
    (hx : seatOf u c = some (Sum.inr z))
    (hxt : seatOf u c.twin = some (Sum.inr z.twin))
    (hrank : rungAt u c.suit < c.rank.toIdx)
    (hrankt : rungAt u c.twin.suit < c.twin.rank.toIdx) :
    ¬ SwappableIn u c := by
  intro hswap
  obtain ⟨u', _w, hcls, _hu'x, _hu'xt, hlic⟩ :=
    (swappableIn_iff_raise_reachable hu hx hxt).mp hswap
  have hu' : u'.WF := wf_of_sameOrbit hcls hu
  have hle_c : rungAt u' c.suit ≤ rungAt u c.suit := hmax u' hcls c.suit
  have hle_t : rungAt u' c.twin.suit ≤ rungAt u c.twin.suit :=
    hmax u' hcls c.twin.suit
  rcases hlic with hrev | hrev
  · have hcan : CanRaise u' c :=
      OneColourClosure.canRaise_of_reversibleAtW hu' hrev
    have hpin : rungAt u' c.suit = c.rank.toIdx :=
      canRaiseS_rung (CanRaiseS.now c hcan)
    omega
  · have hcan : CanRaise u' c.twin :=
      OneColourClosure.canRaise_of_reversibleAtW hu' hrev
    have hpin : rungAt u' c.twin.suit = c.twin.rank.toIdx :=
      canRaiseS_rung (CanRaiseS.now c.twin hcan)
    omega

/-- A seated card is never founded, so its suit rung is at most its rank. -/
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

/-- **Nothing seated at the top can be S-live at any class-mate.**  A seated
card is at or below its own rank in the rung; a raise at a class-mate pins the
rung at the rank, forcing the top to have that rank, and the raise landing then
exceeds the top. -/
theorem not_canRaiseS_of_seated_rungMax
    {u F : State} {x : Card}
    (hu : u.WF)
    (hmax : IsRungMax u)
    (hcls : sameOrbitSetoid.r u F)
    (hx : ∃ b : Base, seatOf u x = some b) :
    ¬ CanRaiseS F x := by
  intro hS
  have hF : F.WF := wf_of_sameOrbit hcls hu
  have hpin : rungAt F x.suit = x.rank.toIdx := canRaiseS_rung hS
  have hle : rungAt F x.suit ≤ rungAt u x.suit := hmax F hcls x.suit
  have hfound : rungAt u x.suit ≤ x.rank.toIdx :=
    le_rung_of_seated hu hx
  have heq : rungAt u x.suit = x.rank.toIdx := by omega
  obtain ⟨A, _hArm, hclsA, _hAwf, hrung⟩ :=
    ForklessTop.exists_armRaise_sameOrbit hF hS
  have hclsA' : sameOrbitSetoid.r u A :=
    sameOrbitSetoid.iseqv.trans hcls hclsA
  have hleA : rungAt A x.suit ≤ rungAt u x.suit := hmax A hclsA' x.suit
  have hA : rungAt A x.suit = x.rank.toIdx + 1 := by
    simpa [hpin] using hrung x.suit
  omega

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

/-- If `c` sits on `z0`, `c` is not a floater, and `c.twin` is founded, then
`c.twin` cannot be pulled down while `z0.twin` is not founded: neither fitting
parent (`z0`, `z0.twin`) is a pile top. -/
theorem no_pull_twin_of_seated_parent
    {u : State} {c z0 : Card} {b : Base}
    (hwf : u.WF)
    (hseat : seatOf u c = some (Sum.inr z0))
    (hnf : ¬ FloaterSpec u c)
    (_hz0 : z0.twin ∉ u.found z0.twin.suit) :
    State.step u (Move.foundToTab c.twin b) = none := by
  cases hstep : State.step u (Move.foundToTab c.twin b) with
  | none => rfl
  | some v =>
      exfalso
      obtain ⟨a0, hhold, -, hlast⟩ := tfc_seatOf_of_inr hseat
      have hnk : c.rank ≠ Rank.king :=
        tfc_seatOf_inr_rank_ne_king hwf hseat
      have hztop : u.pileOfTop z0.twin = none := by
        cases h : u.pileOfTop z0.twin with
        | none => rfl
        | some k =>
            exact absurd (Or.inl ⟨z0, a0, hseat, hhold, Or.inl ⟨k, h⟩⟩) hnf
      have hz0top : u.pileOfTop z0 = none := no_top_of_seat hwf hseat
      have hfitc : canSitOn c z0 = true :=
        (tfc_seat_parent hwf hhold hlast).1
      obtain ⟨x, htop, hxc, hcp, hs⟩ := step_foundToTab_inv hstep
      cases b with
      | inl t =>
          obtain ⟨-, hking⟩ := canPlace_inl hcp
          exact hnk (by simpa [Card.twin_rank] using hking)
      | inr w =>
          obtain ⟨k, htopw, hfitw⟩ := canPlace_inr hcp
          have hfitz : canSitOn c.twin z0.twin = true := by
            rw [canSitOn_twin_left c z0.twin, canSitOn_twin_target c z0]
            exact hfitc
          rcases tfc_fitting_parent hfitw hfitz with hw | hw
          · subst w
            rw [hztop] at htopw
            nomatch htopw
          · rw [card_twin_twin] at hw
            subst w
            rw [hz0top] at htopw
            nomatch htopw

/-- One step of the twin-pair parent invariant. -/
theorem seat_parent_step
    {st s1 : State} {m : Move} {c z0 : Card}
    (hwf : st.WF)
    (hstep : State.step st m = some s1)
    (hrev : reversibleAtW st m)
    (hseat : ∃ z, seatOf st c = some (Sum.inr z) ∧ (z = z0 ∨ z = z0.twin))
    (hnoRaise : ¬ CanRaiseS st c) :
    ∃ z, seatOf s1 c = some (Sum.inr z) ∧ (z = z0 ∨ z = z0.twin) := by
  obtain ⟨z1, hz1, hz1p⟩ := hseat
  have hcne : seatOf st c ≠ none := by rw [hz1]; simp
  cases m with
  | draw =>
      have hse := (chart_draw hstep).1
      exact ⟨z1, by rw [hse, hz1], hz1p⟩
  | wasteToFound x =>
      exact absurd hrev (wasteToFound_not_reversibleAtW st x)
  | wasteToTab x b =>
      exact absurd hrev (wasteToTab_not_reversibleAtW st x b)
  | tabToFound d =>
      by_cases hdc : d = c
      · subst d
        have hcan : CanRaise st c :=
          OneColourClosure.canRaise_of_reversibleAtW hwf hrev
        exact absurd (CanRaiseS.now c hcan) hnoRaise
      · have hsame : seatOf s1 c = seatOf st c :=
          raise_seat_change_of_seated hstep hrev hcne (fun h => hdc h.symm)
        exact ⟨z1, by rw [hsame, hz1], hz1p⟩
  | foundToTab d b =>
      by_cases hdc : d = c
      · subst d
        obtain ⟨x, htop, hxc, _hcp, _hs⟩ := step_foundToTab_inv hstep
        have hmem : c ∈ st.found c.suit := by
          simpa [State.foundTop, hxc] using lastOf_mem htop
        exact absurd hmem (cover_not_found hwf hz1)
      · have hsame : seatOf s1 c = seatOf st c :=
          pull_seat_change hstep c (fun h => hdc h.symm)
        exact ⟨z1, by rw [hsame, hz1], hz1p⟩
  | tabToTab d b =>
      by_cases hdc : d = c
      · subst d
        obtain ⟨hsed, htarget⟩ := floater_seat_change_spec hwf hstep hrev
        rcases htarget with ⟨z, z', hz, hb, hzp⟩ | ⟨a, a', hzinl, _hb, _hk, _hh⟩
        · have hzz1 : z = z1 := by
            rw [hz1] at hz
            exact (Sum.inr.inj (Option.some.inj hz)).symm
          subst z
          have hz'p : z' = z0 ∨ z' = z0.twin := by
            rcases hzp with rfl | rfl
            · exact hz1p
            · rcases hz1p with rfl | rfl
              · exact Or.inr rfl
              · exact Or.inl (by simp [card_twin_twin])
          refine ⟨z', ?_, hz'p⟩
          rw [show seatOf s1 c = some b from by simpa using hsed.1 c, hb]
        · rw [hz1] at hzinl
          nomatch hzinl
      · have hx := tfc_seat_point_edit hwf hstep hrev
        have hsame : seatOf s1 c = seatOf st c := by
          rw [hx c, ite_eq_right (fun h => hdc h.symm)]
        exact ⟨z1, by rw [hsame, hz1], hz1p⟩

/-- The parent stays inside the twin pair along any play, under the rung top. -/
theorem seat_parent_mem_twinPair_aux
    {u w v : State} {play : List Move} {c z0 : Card}
    (hu : u.WF) (hmax : IsRungMax u)
    (hseat_u : seatOf u c = some (Sum.inr z0))
    (hplay : ShufflePlayW w play v) :
    sameOrbitSetoid.r u w → w.WF →
    (∃ z, seatOf w c = some (Sum.inr z) ∧ (z = z0 ∨ z = z0.twin)) →
    ∃ z, seatOf v c = some (Sum.inr z) ∧ (z = z0 ∨ z = z0.twin) := by
  induction hplay with
  | nil st =>
      intro _ _ hseat
      exact hseat
  | @cons st s1 W m rest hrev hstep hrest ih =>
      intro hwcls hwwf hseat
      have hnoRaise : ¬ CanRaiseS st c :=
        not_canRaiseS_of_seated_rungMax hu hmax hwcls ⟨Sum.inr z0, hseat_u⟩
      obtain ⟨z1, hz1, hz1p⟩ :=
        seat_parent_step hwwf hstep hrev hseat hnoRaise
      have hstWF : s1.WF := step_wf hwwf hstep
      have hcls1 : sameOrbitSetoid.r u s1 :=
        sameOrbitSetoid.iseqv.trans hwcls (Drain.sameOrbit_of_step hrev hstep)
      exact ih hcls1 hstWF ⟨z1, hz1, hz1p⟩

/-- **The parent invariant.**  If `c` is seated on `z0` at the top, then at any
same-orbit endpoint its parent is still `z0` or `z0.twin`. -/
theorem seat_parent_mem_twinPair
    {u v : State} {play : List Move} {c z0 : Card}
    (hu : u.WF)
    (hmax : IsRungMax u)
    (hplay : ShufflePlayW u play v)
    (hseat_u : seatOf u c = some (Sum.inr z0)) :
    ∃ z : Card, seatOf v c = some (Sum.inr z) ∧ (z = z0 ∨ z = z0.twin) :=
  seat_parent_mem_twinPair_aux hu hmax hseat_u hplay
    (sameOrbitSetoid.iseqv.refl u) hu ⟨z0, hseat_u, Or.inl rfl⟩

/-- If `c.twin` is not on `z0.twin`, then `z0.twin` cannot be face-up: any
sitter would be `c.twin` by `blocker_eq_twin`, and a face-up card with no
sitter would be a top, making `c` a floater. -/
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

/-- **The `c.twin`-founded case.**  If `c.twin` is in the foundation, then the
target parent `z0.twin` cannot be face-up: if it were, it would have to be a
top, making `c` a floater.  Hence `z0.twin` is not face-up at `v` either, and
the parent invariant forces `c` back onto `z0`. -/
theorem seat_eq_of_twin_founded
    {u v : State} {c z0 : Card}
    (hu : u.WF)
    (hmax : IsRungMax u)
    (horb : sameOrbitSetoid.r u v)
    (hrung : RungEq u v)
    (hseat_u : seatOf u c = some (Sum.inr z0))
    (hnfu : ¬ FloaterSpec u c)
    (htwin : c.twin ∈ u.found c.twin.suit) :
    seatOf u c = seatOf v c := by
  have hv : v.WF := wf_of_sameOrbit horb hu
  have hnotface_u : ¬ ∃ a, z0.twin ∈ (u.piles a).faceUp := by
    rintro ⟨a, hmema⟩
    have hno : ¬ ∃ d, seatOf u d = some (Sum.inr z0.twin) := by
      rintro ⟨d, hd⟩
      have hdt : d = c.twin := blocker_eq_twin hu hseat_u hd
      subst hdt
      exact (cover_not_found hu hd) htwin
    have htop : u.pileOfTop z0.twin = some a :=
      top_of_faceUp_no_sitter hu hmema hno
    obtain ⟨a0, hhold, -, -⟩ := tfc_seatOf_of_inr hseat_u
    exact hnfu (Or.inl ⟨z0, a0, hseat_u, hhold, Or.inl ⟨a, htop⟩⟩)
  have hnotface_v : ¬ ∃ a, z0.twin ∈ (v.piles a).faceUp := by
    intro hvface
    exact hnotface_u ((faceUp_iff hu horb hrung z0.twin).mpr hvface)
  obtain ⟨-, -, play, hplay⟩ := horb
  obtain ⟨z, hzseat, hzp⟩ :=
    seat_parent_mem_twinPair hu hmax hplay hseat_u
  have hz0 : z = z0 := by
    rcases hzp with rfl | rfl
    · rfl
    · exfalso
      apply hnotface_v
      obtain ⟨a, hhold, -, hlast⟩ := tfc_seatOf_of_inr hzseat
      exact ⟨a, mem_below _ (lastOf_mem hlast)⟩
  rw [hz0] at hzseat
  exact hseat_u.trans hzseat.symm


/-- **No strict twin swap at a rung top, with no rank side condition.**  A
seated card is never founded, so `rungAt u ≤ c.rank`; a reachable raise at a
class-mate `u' ≤ u` pins `rungAt u' = c.rank`, forcing `rungAt u = c.rank`;
the raise landing then exceeds the top. -/
theorem not_swappableIn_of_seated_rungMax
    {u : State} {c z : Card}
    (hu : u.WF)
    (hmax : IsRungMax u)
    (hx : seatOf u c = some (Sum.inr z))
    (hxt : seatOf u c.twin = some (Sum.inr z.twin)) :
    ¬ SwappableIn u c := by
  intro hswap
  obtain ⟨u', _w, hcls', _hu'x, _hu'xt, hlic⟩ :=
    (swappableIn_iff_raise_reachable hu hx hxt).mp hswap
  have hu' : u'.WF := wf_of_sameOrbit hcls' hu
  have hle_c : rungAt u' c.suit ≤ rungAt u c.suit := hmax u' hcls' c.suit
  have hle_t : rungAt u' c.twin.suit ≤ rungAt u c.twin.suit :=
    hmax u' hcls' c.twin.suit
  have hfound_c : rungAt u c.suit ≤ c.rank.toIdx :=
    le_rung_of_not_found hu (cover_not_found hu hx)
  have hfound_t : rungAt u c.twin.suit ≤ c.twin.rank.toIdx :=
    le_rung_of_not_found hu (cover_not_found hu hxt)
  rcases hlic with hrev | hrev
  · have hcan : CanRaise u' c :=
      OneColourClosure.canRaise_of_reversibleAtW hu' hrev
    have hpin : rungAt u' c.suit = c.rank.toIdx :=
      canRaiseS_rung (CanRaiseS.now c hcan)
    have heq : rungAt u c.suit = c.rank.toIdx := by omega
    obtain ⟨A, _hArm, hclsA, _hAwf, hrung⟩ :=
      ForklessTop.exists_armRaise_sameOrbit hu' (CanRaiseS.now c hcan)
    have hclsA' : sameOrbitSetoid.r u A :=
      sameOrbitSetoid.iseqv.trans hcls' hclsA
    have hleA : rungAt A c.suit ≤ rungAt u c.suit := hmax A hclsA' c.suit
    have hA : rungAt A c.suit = c.rank.toIdx + 1 := by
      simpa [hpin] using hrung c.suit
    omega
  · have hcan : CanRaise u' c.twin :=
      OneColourClosure.canRaise_of_reversibleAtW hu' hrev
    have hpin : rungAt u' c.twin.suit = c.twin.rank.toIdx :=
      canRaiseS_rung (CanRaiseS.now c.twin hcan)
    have heq : rungAt u c.twin.suit = c.twin.rank.toIdx := by omega
    obtain ⟨A, _hArm, hclsA, _hAwf, hrung⟩ :=
      ForklessTop.exists_armRaise_sameOrbit hu' (CanRaiseS.now c.twin hcan)
    have hclsA' : sameOrbitSetoid.r u A :=
      sameOrbitSetoid.iseqv.trans hcls' hclsA
    have hleA : rungAt A c.twin.suit ≤ rungAt u c.twin.suit :=
      hmax A hclsA' c.twin.suit
    have hA : rungAt A c.twin.suit = c.twin.rank.toIdx + 1 := by
      simpa [hpin] using hrung c.twin.suit
    omega

/-- **The non-king seated case.**  At a rung top, a non-floater non-king
seated on `z0` cannot change its seat. -/
theorem seat_eq_of_nonKing
    {u v : State} {c z0 : Card}
    (hu : u.WF)
    (hmax : IsRungMax u)
    (horb : sameOrbitSetoid.r u v)
    (hrung : RungEq u v)
    (hseat_u : seatOf u c = some (Sum.inr z0))
    (hnfu : ¬ FloaterSpec u c) :
    seatOf u c = seatOf v c := by
  have hv : v.WF := wf_of_sameOrbit horb hu
  have horb' := horb
  obtain ⟨-, -, play, hplay⟩ := horb
  obtain ⟨z, hzseat, hzp⟩ := seat_parent_mem_twinPair hu hmax hplay hseat_u
  have hz0 : z = z0 := by
    rcases hzp with rfl | rfl
    · rfl
    · exfalso
      by_cases hct : seatOf u c.twin = some (Sum.inr z0.twin)
      · obtain ⟨zt, hztseat, hztp⟩ :=
          seat_parent_mem_twinPair hu hmax hplay hct
        rcases hztp with rfl | rfl
        · exact (card_twin_ne c) (seat_inr_inj hv hzseat hztseat).symm
        · have hzt : seatOf v c.twin = some (Sum.inr z0) := by
            simpa [card_twin_twin] using hztseat
          have hweak : twinPairSwap u v c :=
            ⟨hzseat.trans hct.symm, hzt.trans hseat_u.symm⟩
          exact (not_swappableIn_of_seated_rungMax hu hmax hseat_u hct)
            (swappableIn_of_twinPairSwap hu hseat_u hct hweak horb')
      · have hnotface_u :=
          not_faceUp_target_of_twin_not_seated hu hseat_u hnfu hct
        have hnotface_v : ¬ ∃ a, z0.twin ∈ (v.piles a).faceUp := by
          intro hvface
          exact hnotface_u ((faceUp_iff hu horb' hrung z0.twin).mpr hvface)
        obtain ⟨a, hhold, -, hlast⟩ := tfc_seatOf_of_inr hzseat
        exact hnotface_v ⟨a, mem_below _ (lastOf_mem hlast)⟩
  rw [hz0] at hzseat
  exact hseat_u.trans hzseat.symm

/-- **The class-mate form of the rank contradiction.**  The rank comparison
may be read at the top `u` while `SwappableIn` is stated at any class-mate `F`:
`swappableIn_iff_raise_reachable` moves the raise to a class-mate `u'`, and
`IsRungMax u` bounds `u'`'s rungs by `u`'s. -/
theorem not_swappableIn_of_class_rank_gt_rungMax
    {u F : State} {c z : Card}
    (hu : u.WF)
    (hmax : IsRungMax u)
    (hcls : sameOrbitSetoid.r u F)
    (hx : seatOf F c = some (Sum.inr z))
    (hxt : seatOf F c.twin = some (Sum.inr z.twin))
    (hrank : rungAt u c.suit < c.rank.toIdx)
    (hrankt : rungAt u c.twin.suit < c.twin.rank.toIdx) :
    ¬ SwappableIn F c := by
  have hF : F.WF := wf_of_sameOrbit hcls hu
  intro hswap
  obtain ⟨u', _w, hcls', _hu'x, _hu'xt, hlic⟩ :=
    (swappableIn_iff_raise_reachable hF hx hxt).mp hswap
  have hcls_u : sameOrbitSetoid.r u u' :=
    sameOrbitSetoid.iseqv.trans hcls hcls'
  have hle_c : rungAt u' c.suit ≤ rungAt u c.suit := hmax u' hcls_u c.suit
  have hle_t : rungAt u' c.twin.suit ≤ rungAt u c.twin.suit :=
    hmax u' hcls_u c.twin.suit
  rcases hlic with hrev | hrev
  · have hcan : CanRaise u' c :=
      OneColourClosure.canRaise_of_reversibleAtW
        (wf_of_sameOrbit hcls' hF) hrev
    have hpin : rungAt u' c.suit = c.rank.toIdx :=
      canRaiseS_rung (CanRaiseS.now c hcan)
    omega
  · have hcan : CanRaise u' c.twin :=
      OneColourClosure.canRaise_of_reversibleAtW
        (wf_of_sameOrbit hcls' hF) hrev
    have hpin : rungAt u' c.twin.suit = c.twin.rank.toIdx :=
      canRaiseS_rung (CanRaiseS.now c.twin hcan)
    omega

/-- A reversible raise at a class-mate where the twins sit on twin parents
contradicts the rank-over-max condition at `u`. -/
theorem not_raise_class_of_rank_gt_rungMax
    {u F : State} {c z : Card}
    (hu : u.WF)
    (hmax : IsRungMax u)
    (hcls : sameOrbitSetoid.r u F)
    (hx : seatOf F c = some (Sum.inr z))
    (hxt : seatOf F c.twin = some (Sum.inr z.twin))
    (hrank : rungAt u c.suit < c.rank.toIdx)
    (hrankt : rungAt u c.twin.suit < c.twin.rank.toIdx)
    (hlic : reversibleAtW F (Move.tabToFound c) ∨
      reversibleAtW F (Move.tabToFound c.twin)) :
    False :=
  not_swappableIn_of_class_rank_gt_rungMax hu hmax hcls hx hxt hrank hrankt
    (swappableIn_of_raise (wf_of_sameOrbit hcls hu) hx hxt hlic)

/-- **No weak twin swap over the top.**  At a rung maximum, a seated
twin pair whose ranks both exceed the top cannot swap at all, even allowing
the rest of the board to move: the weak swap is upgraded to strict
`SwappableIn`, then refuted by `not_swappableIn_of_rank_gt_rungMax`. -/
theorem not_weakTwinSwap_of_rungMax
    {u : State} {c z : Card}
    (hu : u.WF)
    (hmax : IsRungMax u)
    (hx : seatOf u c = some (Sum.inr z))
    (hxt : seatOf u c.twin = some (Sum.inr z.twin)) :
    ¬ ∃ v : State, twinPairSwap u v c ∧ sameOrbitSetoid.r u v := by
  rintro ⟨v, hweak, horb⟩
  exact not_swappableIn_of_seated_rungMax hu hmax hx hxt
    (swappableIn_of_twinPairSwap hu hx hxt hweak horb)

/-- **The weak-twin-swap conditional.**  Once a non-floater seat change is
shown to produce a bare twin swap in the orbit, `swappableIn_of_twinPairSwap`
upgrades it to strict `SwappableIn`, and the rank-over-max corollary refutes
it. -/
theorem seatOf_change_floater_of_rungMax_of_weakBridge
    {u v : State} {c z : Card}
    (hu : u.WF)
    (hmax : IsRungMax u)
    (hx : seatOf u c = some (Sum.inr z))
    (hxt : seatOf u c.twin = some (Sum.inr z.twin))
    (hbridge : ¬ FloaterSpec u c → seatOf u c ≠ seatOf v c →
      ∃ v' : State, twinPairSwap u v' c ∧ sameOrbitSetoid.r u v')
    (hchg : seatOf u c ≠ seatOf v c) :
    FloaterSpec u c := by
  by_cases hnf : FloaterSpec u c
  · exact hnf
  · obtain ⟨v', hweak, horb'⟩ := hbridge hnf hchg
    exfalso
    exact not_swappableIn_of_seated_rungMax hu hmax hx hxt
      (swappableIn_of_twinPairSwap hu hx hxt hweak horb')

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

/-- A no-vacancy rung maximum has no vacancy anywhere in its orbit. -/
theorem noVacancy_class_of_noVacancy
    {w u : State}
    (hwf : w.WF)
    (hmax : IsRungMax w)
    (hcls : sameOrbitSetoid.r w u)
    (hno : ¬ HasVacancy w) :
    ¬ HasVacancy u := by
  intro hvac
  have hne : NoVacancy w := (noVacancy_iff_not_hasVacancy w).mpr hno
  obtain ⟨_back, _hback, play, hplay⟩ := hcls
  obtain ⟨pre, x, a, s0, s1, suffix,
    hpre, hstep, hp, _hno0, hempty, hrev, _hsuffix⟩ :=
    first_vacancy_split hwf hplay hne hvac
  have hwfs0 : s0.WF := NVWalk_wf hpre hwf
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
  have hseat_back : seatOf s0 x = seatOf w x :=
    NVWalk_seat_back hpre hwf hne hx0
  have hseat_w : seatOf w x = some (Sum.inl a) := by
    rw [← hseat_back]
    exact hseat0
  have hcls_ws0 : sameOrbitSetoid.r w s0 :=
    RevEqW_symm (shufflePlayW_revEqW hpre.to_shuffle)
  have hcan : CanRaise s0 x := by
    obtain ⟨hnext, a', hp', _⟩ := step_tabToFound_inv hstep
    have haa : a' = a := Option.some.inj (hp'.symm.trans hp)
    subst a'
    exact ⟨hnext, a, hp, Or.inr ⟨hface_hid.2, hrank⟩⟩
  have hcanS : CanRaiseS s0 x := CanRaiseS.now x hcan
  exact not_canRaiseS_of_seated_rungMax hwf hmax hcls_ws0
    ⟨Sum.inl a, hseat_w⟩ hcanS

/-- A card seated on a parent at the rung top can change its seat only if it is
a floater: the contrapositive of `seat_eq_of_nonKing`. -/
theorem changed_inr_floater
    {w u : State} {x z0 : Card}
    (hw : w.WF)
    (hmax : IsRungMax w)
    (hcls : sameOrbitSetoid.r w u)
    (hrung : RungEq w u)
    (hseat : seatOf w x = some (Sum.inr z0))
    (hchg : seatOf w x ≠ seatOf u x) :
    FloaterSpec w x := by
  by_cases hnf : FloaterSpec w x
  · exact hnf
  · exact absurd (seat_eq_of_nonKing hw hmax hcls hrung hseat hnf) hchg

/-- A non-floater king bottomed at a rung maximum keeps its seat at every
equal-rung class-mate.  If its hidden deck is nonempty it is frozen; otherwise
non-floater rules out a vacancy, and `noVacancy_class_of_noVacancy` makes the
whole orbit vacancy-free, so `seatOf_walk_noVacant` applies. -/
theorem king_seat_fixed_of_rungMax
    {u v : State} {c : Card} {a : Anchor}
    (hu : u.WF)
    (hmax : IsRungMax u)
    (horb : sameOrbitSetoid.r u v)
    (hrank : c.rank = Rank.king)
    (hseat : seatOf u c = some (Sum.inl a))
    (hnf : ¬ FloaterSpec u c) :
    seatOf u c = seatOf v c := by
  by_cases hhid : (u.piles a).hidden = []
  · have hno_u : ¬ HasVacancy u := by
      intro hvac
      obtain ⟨a', ha'⟩ := hvac
      exact hnf (Or.inr ⟨a, hseat, hrank, hhid, ⟨a', ha'⟩⟩)
    have hno_all : ∀ x, sameOrbitSetoid.r u x → NoVacancy x := by
      intro x hx
      exact (noVacancy_iff_not_hasVacancy x).mpr
        (noVacancy_class_of_noVacancy hu hmax hx hno_u)
    obtain ⟨play_vu, h_vu, play_uv, h_uv⟩ := horb
    have hkb : KingBottomCard u c := ⟨a, ⟨c, hseat, hrank, hhid⟩, hseat⟩
    have hwalk := seatOf_walk_noVacant (base := u) (s := u) (v := v)
      hno_all (sameOrbitSetoid.iseqv.refl u) h_uv h_vu hu hkb
    exact hwalk.symm
  · obtain ⟨_play_vu, _h_vu, _play_uv, h_uv⟩ := horb
    exact king_seat_fixed_of_hidden_ne hu h_uv hseat hhid

/-- A non-king bottomed card cannot move under a reversible step that is not an
S-raise at its start. -/
theorem bottom_seat_step_nonKing
    {st s1 : State} {m : Move} {c : Card} {a0 : Anchor}
    (hwf : st.WF) (hstep : State.step st m = some s1)
    (hrev : reversibleAtW st m)
    (hse : seatOf st c = some (Sum.inl a0))
    (hnk : c.rank ≠ Rank.king)
    (hnoRaise : ¬ CanRaiseS st c) :
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
        exfalso
        exact hnoRaise (CanRaiseS.now c
          (OneColourClosure.canRaise_of_reversibleAtW hwf hrev))
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
      · have h := tfc_seat_point_edit hwf hstep hrev c
        rw [ite_eq_right (fun hcon => hxc hcon.symm)] at h
        rw [h]
        exact hse

/-- Along a whole reversible play from a rung maximum, a non-king bottomed card
keeps its anchor. -/
theorem seat_inl_nonKing_fixed_play
    {u v : State} {play : List Move} {c : Card} {a0 : Anchor}
    (hu : u.WF)
    (hmax : IsRungMax u)
    (_hcls : sameOrbitSetoid.r u v)
    (hplay : ShufflePlayW u play v)
    (hnk : c.rank ≠ Rank.king)
    (hseat_u : seatOf u c = some (Sum.inl a0)) :
    seatOf v c = some (Sum.inl a0) := by
  have aux : ∀ {st W : State} {play : List Move},
      ShufflePlayW st play W →
      sameOrbitSetoid.r u st →
      seatOf st c = some (Sum.inl a0) →
      W = v →
      seatOf W c = some (Sum.inl a0) := by
    intro st W play hplay
    induction hplay with
    | nil st =>
        intro _ hseat _
        exact hseat
    | @cons st s1 W m rest hrev hstep hrest ih =>
        intro hcls_st hseat_st hW
        have hnoRaise : ¬ CanRaiseS st c :=
          not_canRaiseS_of_seated_rungMax hu hmax hcls_st
            ⟨Sum.inl a0, hseat_u⟩
        have hseat1 : seatOf s1 c = some (Sum.inl a0) :=
          bottom_seat_step_nonKing (wf_of_sameOrbit hcls_st hu)
            hstep hrev hseat_st hnk hnoRaise
        have hcls1 : sameOrbitSetoid.r u s1 :=
          sameOrbitSetoid.iseqv.trans hcls_st
            (Drain.sameOrbit_of_step hrev hstep)
        exact ih hcls1 hseat1 hW
  exact aux hplay (sameOrbitSetoid.iseqv.refl u) hseat_u rfl

/-- The bundled seat-invariance statement: at equal-rung class-mates, every
card that is seated at both ends and is a non-floater at both ends keeps its
seat. -/
def SeatFixedExceptFloater (u v : State) : Prop :=
  ∀ c : Card,
    (∃ b : Base, seatOf u c = some b) →
    (∃ b : Base, seatOf v c = some b) →
    ¬ FloaterSpec u c →
    ¬ FloaterSpec v c →
    seatOf u c = seatOf v c

/-- **THE CORRECTED MAIN TARGET.**  At a rung-maximal `u`, two equal-rung
class-mates cannot move a card that is a non-floater at both ends.  The
non-floater hypothesis at `v` is what excludes the foundation twin pull. -/
theorem seatOf_eq_of_rungMax_of_nonfloater_both
    {u v : State} {c : Card}
    (hu : u.WF)
    (hmax : IsRungMax u)
    (horb : sameOrbitSetoid.r u v)
    (hrung : RungEq u v)
    (hnfu : ¬ FloaterSpec u c)
    (_hnfv : ¬ FloaterSpec v c)
    (hseat_u : ∃ b : Base, seatOf u c = some b)
    (_hseat_v : ∃ b : Base, seatOf v c = some b) :
    seatOf u c = seatOf v c := by
  obtain ⟨b, hb⟩ := hseat_u
  cases b with
  | inr z0 =>
      exact seat_eq_of_nonKing hu hmax horb hrung hb hnfu
  | inl a =>
      by_cases hk : c.rank = Rank.king
      · exact king_seat_fixed_of_rungMax hu hmax horb hk hb hnfu
      · have horb_keep := horb
        obtain ⟨_play_vu, _h_vu, play_uv, h_uv⟩ := horb
        exact hb.trans (seat_inl_nonKing_fixed_play hu hmax horb_keep h_uv hk hb).symm

/-- **The bundled form of the corrected target.** -/
theorem seat_fixed_except_floater_of_rungMax
    {u v : State}
    (hu : u.WF)
    (hmax : IsRungMax u)
    (horb : sameOrbitSetoid.r u v)
    (hrung : RungEq u v) :
    SeatFixedExceptFloater u v := by
  intro c hseat_u hseat_v hnfu hnfv
  exact seatOf_eq_of_rungMax_of_nonfloater_both
    hu hmax horb hrung hnfu hnfv hseat_u hseat_v

/-- The `FloaterSpec` form, conditional on the endpoint also being a
non-floater with a tableau seat. -/
theorem seatOf_change_floater_of_rungMax
    {u v : State} {c : Card}
    (hu : u.WF)
    (horb : sameOrbitSetoid.r u v)
    (hrung : RungEq u v)
    (htop : IsRungMax u)
    (hseat_u : ∃ b : Base, seatOf u c = some b)
    (hnfv : ¬ FloaterSpec v c)
    (hseat_v : ∃ b : Base, seatOf v c = some b)
    (hchg : seatOf u c ≠ seatOf v c) :
    FloaterSpec u c := by
  by_cases hnf : FloaterSpec u c
  · exact hnf
  · exact absurd
      (seatOf_eq_of_rungMax_of_nonfloater_both hu htop horb hrung hnf hnfv hseat_u hseat_v)
      hchg

/-- Symmetric form: both are rung maxima, so `RungEq` is automatic. -/
theorem seatOf_change_floater_of_rungMaxPair
    {u v : State} {c : Card}
    (hu : u.WF)
    (hmax : IsRungMaxPair u v)
    (hseat_u : ∃ b : Base, seatOf u c = some b)
    (hnfv : ¬ FloaterSpec v c)
    (hseat_v : ∃ b : Base, seatOf v c = some b)
    (hchg : seatOf u c ≠ seatOf v c) :
    FloaterSpec u c := by
  obtain ⟨horb, htopu, htopv⟩ := hmax
  exact seatOf_change_floater_of_rungMax hu horb
    (rungEq_of_isRungMax_pair horb htopu htopv) htopu hseat_u hnfv hseat_v hchg

theorem seatOf_change_floater_of_strictRungMax
    {u v : State} {c : Card}
    (hu : u.WF)
    (hmax : IsStrictRungMax u v)
    (hseat_u : ∃ b : Base, seatOf u c = some b)
    (hnfv : ¬ FloaterSpec v c)
    (hseat_v : ∃ b : Base, seatOf v c = some b)
    (hchg : seatOf u c ≠ seatOf v c) :
    FloaterSpec u c := by
  obtain ⟨hpair, _honly⟩ := hmax
  exact seatOf_change_floater_of_rungMaxPair hu hpair hseat_u hnfv hseat_v hchg

/-- The per-card `bareCargo_iff_vk` clause for cards seated at the origin. -/
theorem changed_seated_clause
    {w u : State} {x : Card}
    (hw : w.WF)
    (hmax : IsRungMax w)
    (horb : sameOrbitSetoid.r w u)
    (hrung : RungEq w u)
    (hseat : ∃ b : Base, seatOf w x = some b)
    (hchg : seatOf w x ≠ seatOf u x) :
    (((∃ z', seatOf w x = some (Sum.inr z') ∧
        seatOf u x = some (Sum.inr z'.twin)) ∨
      (x.rank = Rank.king ∧
        ∃ a', seatOf u x = some (Sum.inl a') ∧ VKSet w a')) ∨
     FloaterSpec w x) := by
  obtain ⟨b, hb⟩ := hseat
  cases b with
  | inr z0 =>
      exact Or.inr (changed_inr_floater hw hmax horb hrung hb hchg)
  | inl a =>
      by_cases hnf : FloaterSpec w x
      · exact Or.inr hnf
      · exfalso
        by_cases hk : x.rank = Rank.king
        · exact hchg (king_seat_fixed_of_rungMax hw hmax horb hk hb hnf)
        · have horb_keep := horb
          obtain ⟨_play_vu, _h_vu, play_uv, h_uv⟩ := horb
          exact hchg
            (hb.trans
              (seat_inl_nonKing_fixed_play hw hmax horb_keep h_uv hk hb).symm)


/-- The none-seat pins the holding search: an unseated card is held
by no pile. -/
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

/-- With foundation agreement, an unseated origin cannot become a seated
endpoint. -/
theorem changed_unseated_clause
    {w u : State} {x : Card}
    (hw : w.WF)
    (horb : sameOrbitSetoid.r w u)
    (hfounds : foundsFixed w u)
    (hseat : seatOf w x = none)
    (hchg : seatOf w x ≠ seatOf u x) :
    (((∃ z', seatOf w x = some (Sum.inr z') ∧
        seatOf u x = some (Sum.inr z'.twin)) ∨
      (x.rank = Rank.king ∧
        ∃ a', seatOf u x = some (Sum.inl a') ∧ VKSet w a')) ∨
     FloaterSpec w x) := by
  exfalso
  have hu : u.WF := wf_of_sameOrbit horb hw
  obtain ⟨_play_vu, _h_vu, play_uv, h_uv⟩ := horb
  by_cases hf : x ∈ w.found x.suit
  · have huf : x ∈ u.found x.suit := by
      rw [← hfounds x.suit]
      exact hf
    have hnone := seatOf_none_of_mem_foundT hu huf
    exact hchg (hseat.trans hnone.symm)
  · have hnone := (unseated_track_playT hw h_uv hseat hf).1
    exact hchg (hseat.trans hnone.symm)

/-- The full per-card clause, for seated or unseated origins. -/
theorem changed_card_clause
    {w u : State} {x : Card}
    (hw : w.WF)
    (hmax : IsRungMax w)
    (horb : sameOrbitSetoid.r w u)
    (hrung : RungEq w u)
    (hfounds : foundsFixed w u)
    (hchg : seatOf w x ≠ seatOf u x) :
    (((∃ z', seatOf w x = some (Sum.inr z') ∧
        seatOf u x = some (Sum.inr z'.twin)) ∨
      (x.rank = Rank.king ∧
        ∃ a', seatOf u x = some (Sum.inl a') ∧ VKSet w a')) ∨
     FloaterSpec w x) := by
  by_cases hnone : seatOf w x = none
  · exact changed_unseated_clause hw horb hfounds hnone hchg
  · have hsome : ∃ b, seatOf w x = some b := by
      cases h : seatOf w x with
      | none => exact absurd h hnone
      | some b => exact ⟨b, rfl⟩
    obtain ⟨b, hb⟩ := hsome
    exact changed_seated_clause hw hmax horb hrung ⟨b, hb⟩ hchg

/-- The per-card clause in the form consumed by `bareFlat_of_vk`. -/
theorem forkless_changed_king_floater
    {w u : State} {x : Card}
    (hw : w.WF)
    (hmax : IsRungMax w)
    (horb : sameOrbitSetoid.r w u)
    (hrung : RungEq w u)
    (hfounds : foundsFixed w u)
    (hchg : seatOf w x ≠ seatOf u x) :
    (((∃ z', seatOf w x = some (Sum.inr z') ∧
        seatOf u x = some (Sum.inr z'.twin)) ∨
      (x.rank = Rank.king ∧
        ∃ a', seatOf u x = some (Sum.inl a') ∧ VKSet w a')) ∨
     FloaterSpec w x) :=
  changed_card_clause hw hmax horb hrung hfounds hchg

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

/-- **The flat normal form, assembled from the strong per-card clause.** -/
theorem forklessFlatNormalWF_of_perCard
    (hperStrong : ∀ {w u : State} {x : Card},
      w.WF → IsRungMax w → sameOrbitSetoid.r w u → RungEq w u →
      foundsFixed w u →
      seatOf w x ≠ seatOf u x →
      (((∃ z', seatOf w x = some (Sum.inr z') ∧
          seatOf u x = some (Sum.inr z'.twin)) ∨
        (x.rank = Rank.king ∧
          ∃ a', seatOf u x = some (Sum.inl a') ∧ VKSet w a')) ∧
       FloaterSpec w x)) :
    ForklessFlatNormalWF := by
  intro u v hu hsu hsv horb hfrk
  have hv : v.WF := wf_of_sameOrbit horb hu
  obtain ⟨w, huw, htop⟩ := forklessHasTop_proved u hu hfrk
  have hw : w.WF := wf_of_sameOrbit huw hu
  have hwu : sameOrbitSetoid.r w u := sameOrbitSetoid.iseqv.symm huw
  have hwv : sameOrbitSetoid.r w v :=
    sameOrbitSetoid.iseqv.trans hwu horb
  have htop_ww : HasTopRung w w := by
    refine ⟨sameOrbitSetoid.iseqv.refl w, ?_⟩
    intro x hwx suit
    exact htop x
      (sameOrbitSetoid.iseqv.trans huw hwx) suit
  have hwsat : SSaturated w := ForklessTop.hasTopRung_ssaturated hw htop_ww
  have hmax : IsRungMax w := htop_ww.2
  have hfrk_w : ∀ F, sameOrbitSetoid.r w F → ¬ forkState F := by
    intro F hwF
    exact hfrk F (sameOrbitSetoid.iseqv.trans huw hwF)
  have hru : RungEq w u :=
    forkless_rungs_agree_proved hw hwu hfrk_w hwsat hsu
  have hrv : RungEq w v :=
    forkless_rungs_agree_proved hw hwv hfrk_w hwsat hsv
  have hfounds_wu : foundsFixed w u :=
    fun s => found_congr_of_rungs hw hu (hru s)
  have hfounds_wv : foundsFixed w v :=
    fun s => found_congr_of_rungs hw hv (hrv s)
  have hboard_wu : boardFixed w u := boardFixed_of_sameOrbit hw hwu
  have hboard_wv : boardFixed w v := boardFixed_of_sameOrbit hw hwv
  have hper_wu := fun x hchg =>
    hperStrong (w := w) (u := u) (x := x)
      hw hmax hwu hru hfounds_wu hchg
  have hper_wv := fun x hchg =>
    hperStrong (w := w) (u := v) (x := x)
      hw hmax hwv hrv hfounds_wv hchg
  have hflat_wu : BareFlatEquiv w u :=
    bareFlat_of_vk hw hu hwu hper_wu hboard_wu hfounds_wu
  have hflat_wv : BareFlatEquiv w v :=
    bareFlat_of_vk hw hv hwv hper_wv hboard_wv hfounds_wv
  exact bareFlatEquiv_trans (bareFlatEquiv_symm hflat_wu) hflat_wv

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

/-- The strong per-card clause: a changed card carries both a structural
twin/king arm and the floater license. -/
theorem changed_card_both
    {w u : State} {x : Card}
    (hw : w.WF)
    (hmax : IsRungMax w)
    (horb : sameOrbitSetoid.r w u)
    (hrung : RungEq w u)
    (hfounds : foundsFixed w u)
    (hchg : seatOf w x ≠ seatOf u x) :
    (((∃ z', seatOf w x = some (Sum.inr z') ∧
        seatOf u x = some (Sum.inr z'.twin)) ∨
      (x.rank = Rank.king ∧
        ∃ a', seatOf u x = some (Sum.inl a') ∧ VKSet w a')) ∧
     FloaterSpec w x) := by
  have horb_keep := horb
  obtain ⟨_play_uw, h_uw, play_wu, h_wu⟩ := horb
  by_cases hnone : seatOf w x = none
  · exact (unseated_change_false hw horb_keep hfounds hnone hchg).elim
  · have hsome : ∃ b, seatOf w x = some b := by
      cases h : seatOf w x with
      | none => exact absurd h hnone
      | some b => exact ⟨b, rfl⟩
    obtain ⟨b, hb⟩ := hsome
    cases b with
    | inr z0 =>
        obtain ⟨z, hzu, hzp⟩ :=
          seat_parent_mem_twinPair hw hmax h_wu hb
        have hz : z = z0.twin := by
          rcases hzp with h | h
          · exfalso
            exact hchg (hb.trans (by rw [hzu, h]))
          · exact h
        have htwin : ∃ z', seatOf w x = some (Sum.inr z') ∧
            seatOf u x = some (Sum.inr z'.twin) :=
          ⟨z0, hb, by rw [hzu, hz]⟩
        exact ⟨Or.inl htwin,
          changed_inr_floater hw hmax horb_keep hrung hb hchg⟩
    | inl a =>
        by_cases hnf : FloaterSpec w x
        · have hk : x.rank = Rank.king := by
            rcases hnf with ⟨z, a0, hse_inr, _hhold, _hrest⟩ |
              ⟨a0, hse_inl, hk, _hhid, _hempty⟩
            · rw [hb] at hse_inr
              nomatch hse_inr
            · exact hk
          have hhid_w : (w.piles a).hidden = [] := by
            rcases hnf with ⟨z, a0, hse_inr, _hhold, _hrest⟩ |
              ⟨a0, hse_inl, _hk, hhid0, _hempty⟩
            · rw [hb] at hse_inr
              nomatch hse_inr
            · have haa : a0 = a :=
                Sum.inl.inj (Option.some.inj (hse_inl.symm.trans hb))
              subst a0
              exact hhid0
          have hu : u.WF := wf_of_sameOrbit horb_keep hw
          have hnotnone_u : seatOf u x ≠ none := by
            intro hnone_u
            by_cases huf : x ∈ u.found x.suit
            · have hwf_found : x ∈ w.found x.suit := by
                rw [hfounds x.suit]
                exact huf
              have hnone_w := seatOf_none_of_mem_foundT hw hwf_found
              exact hchg (hnone_w.trans hnone_u.symm)
            · have htrack := unseated_track_playT hu h_uw hnone_u huf
              exact hchg (htrack.1.trans hnone_u.symm)
          obtain ⟨a', hse_u_inl⟩ :=
            seat_inl_of_seated_king hu hk hnotnone_u
          have hbase : seatOf w x ≠ none →
              ∃ a0, seatOf w x = some (Sum.inl a0) ∧
                (w.piles a0).hidden = [] :=
            fun _ => ⟨a, hb, hhid_w⟩
          obtain ⟨a'', hse'', hhid''⟩ :=
            king_pile_hidden_empty_play hw h_wu hk hbase hnotnone_u
          have haa : a'' = a' :=
            Sum.inl.inj (Option.some.inj (hse''.symm.trans hse_u_inl))
          subst a''
          have hkbu : KingBottom u a' := ⟨x, hse_u_inl, hk, hhid''⟩
          have hvku : VKSet u a' := Or.inr hkbu
          have hvkw : VKSet w a' :=
            (vk_sameOrbit_invariant hw horb_keep a').mpr hvku
          exact ⟨Or.inr ⟨hk, ⟨a', hse_u_inl, hvkw⟩⟩, hnf⟩
        · by_cases hk : x.rank = Rank.king
          · exact absurd
              (king_seat_fixed_of_rungMax hw hmax horb_keep hk hb hnf) hchg
          · have hfixed := seat_inl_nonKing_fixed_play hw hmax horb_keep
              h_wu hk hb
            exact absurd (hb.trans hfixed.symm) hchg


/-! ## Audit battery -/

#print axioms forklessFlatNormalWF_of_perCard
#print axioms changed_card_both
#print axioms changed_card_clause
#print axioms seatOf_eq_of_rungMax_of_nonfloater_both
#print axioms king_seat_fixed_of_rungMax
#print axioms noVacancy_class_of_noVacancy
#print axioms NVWalk_seat_back
