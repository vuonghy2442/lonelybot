import Orig2.Fork.ForkPin
import Orig2.Fork.ForkTailHead
import Orig2.Fork.ForkSplitResidual
import Orig2.Fork.ForkLivePair

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-!
# Temp/Both — the `pre = []` corner of `Pin.BottomNotBothRaisable`

READ-ONLY scratch card.  No source file is modified; nothing is committed.
Zero `sorry`, zero `Classical.choice`, zero `native_decide`; the axiom
battery is at the tail.

## Headline

1. **The `gAce` gadget is OUTSIDE the gate.**  The both-raisable landing
   `Pin.gAce` is the landing of the pull `AD → 2C` from `Pin.gAceMid`, and
   `Pin.gAceMid` is NOT saturated (`gAceMid_not_saturated`: `AH` is already
   vanilla-raisable there).  `SplitHyp` requires the play's origin `u` to be
   `SSaturated`, and the pull origin at `pre = []` is `u` itself.

2. **The `pre = []` corner is TRUE, kernel-checked.**
   `bottomNotBothRaisableNil` proves the `pre = []` restriction of
   `Pin.BottomNotBothRaisable` outright.  The proof is the direct-cover
   (`seatOf`) pin:

   at the pull landing `B` the twin `c.twin` is S-live, so
   `canRaise_or_covered` says it is either vanilla-raisable (then the
   saturation of the origin `u`, read through the pull's pile edit,
   transfers the licence back to `u` — `top_case_false`) or covered by a
   card `d`.  That `d` fits `c.twin`, hence its only possible parents are
   `c` and `c.twin` (`tfc_fitting_parent`, twin-blind); a free letter can
   only move `d` onto one of those two parents, and every other card keeps
   its seat (`tfc_seat_point_edit`).  So at the bottom `F` the card `d`
   still sits directly on `c` or directly on `c.twin`: one of the twins is
   covered, hence not vanilla-raisable.

   **The lift is card arithmetic, not geometry**: the cover card `d` has
   rank `c.rank - 1` and opposite colour, so the only cards it can sit on
   are the two twins `c`, `c.twin`.

3. **Consumers.**  `nilPreTwinBlock` derives the `d = c.twin` branch of the
   `pre = []` block lane from `bottomNotBothRaisableNil`; the same-card
   (`d = c`) branch is `TailHead.sameCard_turn_has_cover` plus the open
   no-undo, and is NOT supplied by the vacuity.  The global
   `Pin.BottomNotBothRaisable` remains open exactly on `pre ≠ []`
   (`BottomNotBothPullPre` / `BottomNotBothFreePre`), the
   `ForkPinRight` `PrePullPair` lane.
-/

namespace Both

open SplitKit
open BlockMin

/-! ## §1. The gadget audit -/

/-- The `AD → 2C` pull's origin `gAceMid` already carries a vanilla-raisable
`AH`: it is NOT saturated. -/
theorem gAceMid_canRaise_AH : CanRaise Pin.gAceMid Pin.AH := by
  refine ⟨by decide, .p0, by decide, Or.inl (by decide)⟩

theorem gAceMid_not_saturated : ¬ SSaturated Pin.gAceMid :=
  fun h => h Pin.AH (CanRaiseS.now Pin.AH gAceMid_canRaise_AH)

theorem gAce_not_saturated : ¬ SSaturated Pin.gAce :=
  fun h => h Pin.AH (CanRaiseS.now Pin.AH Pin.gAce_canRaise_AH)

/-- The pre-state of the first pull IS saturated (computable scan). -/
theorem gAcePre_liveB_false :
    (Card.universe.all (fun c => decide (canRaiseSB Pin.gAcePre c = false))) = true := by
  decide

theorem gAcePre_not_live (c : Card) : ¬ CanRaiseS Pin.gAcePre c := by
  intro h
  have h1 : canRaiseSB Pin.gAcePre c = true := (canRaiseSB_iff Pin.gAcePre_wf).mpr h
  have h2 : canRaiseSB Pin.gAcePre c = false :=
    of_decide_eq_true (List.all_eq_true.mp gAcePre_liveB_false c (Card.mem_universe c))
  rw [h1] at h2
  exact Bool.noConfusion h2

theorem gAcePre_saturated : SSaturated Pin.gAcePre :=
  fun c => gAcePre_not_live c

/-! ## §2. Pull bookkeeping: the pile edit is a single append -/

/-- A pull does not touch the foundations. -/
theorem putCard_found' (st : State) (c : Card) (b : Base) :
    (st.putCard c b).found = st.found := by
  cases b with
  | inl a => rfl
  | inr z =>
      dsimp only [State.putCard, State.setPile]
      cases st.pileOfTop z with
      | none => rfl
      | some k => rfl

/-- `setFound` does not change the placement guard (it reads piles only). -/
theorem canPlace_setFound (st : State) (s : Suit) (l : List Card) (c : Card) (b : Base) :
    (st.setFound s l).canPlace c b = st.canPlace c b := by
  cases b with
  | inl a => rfl
  | inr z => rfl

/-- A placement appends the card to exactly one pile's face-up run. -/
theorem putCard_faceUp_cases {st : State} {c : Card} {b : Base}
    (hcp : st.canPlace c b = true) :
    ∀ a, ((st.putCard c b).piles a).faceUp = (st.piles a).faceUp ∨
      ((st.putCard c b).piles a).faceUp = (st.piles a).faceUp ++ [c] := by
  intro a
  cases b with
  | inl a0 =>
      obtain ⟨hemp, -⟩ := canPlace_inl hcp
      obtain ⟨-, hfF⟩ := (Pile.isEmpty_eq _).mp hemp
      dsimp only [State.putCard, State.setPile]
      by_cases ha : a = a0
      · subst ha
        simp [hfF]
      · rw [ite_eq_right ha]
        simp
  | inr z =>
      obtain ⟨k, hpod, -⟩ := canPlace_inr hcp
      dsimp only [State.putCard, State.setPile]
      rw [hpod]
      by_cases ha : a = k
      · subst ha
        simp
      · simp [ha]

/-- The pull's foundation edit is confined to the pulled card's suit. -/
theorem pull_found_other_suit {A B : State} {c e : Card} {b : Base}
    (hstep : State.step A (Move.foundToTab c b) = some B)
    (hne : e.suit ≠ c.suit) : B.found e.suit = A.found e.suit := by
  obtain ⟨c', htop, hc', hcp, heq⟩ := step_foundToTab_inv hstep
  rw [heq, putCard_found']
  exact setFound_found_ne hne

/-- The pull preserves `nextUp` of every card in another suit. -/
theorem nextUp_of_step_pull_ne_suit {A B : State} {c e : Card} {b : Base}
    (hstep : State.step A (Move.foundToTab c b) = some B)
    (hne : e.suit ≠ c.suit) (h : B.nextUp e = true) : A.nextUp e = true := by
  unfold State.nextUp State.foundHeight at h ⊢
  rw [pull_found_other_suit hstep hne] at h
  exact h

/-- The pull's face-up edit is `∅` or one trailing `c`. -/
theorem pull_faceUp_cases {A B : State} {c : Card} {b : Base}
    (hstep : State.step A (Move.foundToTab c b) = some B) :
    ∀ a, (B.piles a).faceUp = (A.piles a).faceUp ∨
      (B.piles a).faceUp = (A.piles a).faceUp ++ [c] := by
  obtain ⟨c', htop, hc', hcp, heq⟩ := step_foundToTab_inv hstep
  have hcp' : (A.setFound c.suit (chop (A.found c.suit))).canPlace c b = true := by
    rwa [canPlace_setFound]
  intro a
  rw [heq]
  exact putCard_faceUp_cases hcp' a

/-- The pull never touches a hidden deck. -/
theorem pull_hidden_eq {A B : State} {c : Card} {b : Base}
    (hstep : State.step A (Move.foundToTab c b) = some B) :
    ∀ a, (B.piles a).hidden = (A.piles a).hidden := by
  obtain ⟨c', htop, hc', hcp, heq⟩ := step_foundToTab_inv hstep
  have hcp' : (A.setFound c.suit (chop (A.found c.suit))).canPlace c b = true := by
    rwa [canPlace_setFound]
  rw [heq]
  intro a
  rw [putCard_hidden_eq hcp' a]
  rfl

/-! ## §3. The `pre = []` top case: saturation transfers across the pull -/

/-- If the twin is a pile top at the landing (`CanRaise` at `B`), then it was
already S-live at the saturated origin `u` — impossible. -/
theorem top_case_false {u B : State} {c : Card} {b : Base}
    (huwf : u.WF) (hsu : SSaturated u)
    (hstep : State.step u (Move.foundToTab c b) = some B)
    (hcanB : CanRaise B c.twin) : False := by
  obtain ⟨hnextB, a, hpodB, hseatB⟩ := hcanB
  have htopB : lastOf (B.piles a).faceUp = some c.twin := (pileOfTop_top hpodB).2
  have hnextU : u.nextUp c.twin = true :=
    nextUp_of_step_pull_ne_suit hstep (Suit.twin_ne c.suit) hnextB
  have hface := pull_faceUp_cases hstep a
  have hhid := pull_hidden_eq hstep a
  rcases hface with hface | hface
  · have htopU : u.topOf a = some c.twin := by
      show lastOf (u.piles a).faceUp = some c.twin
      rw [← hface]
      exact htopB
    have hpodU : u.pileOfTop c.twin = some a :=
      (pileOfTop_eq_some_iff huwf).mpr htopU
    have hseatU : chop (u.piles a).faceUp ≠ [] ∨
        ((u.piles a).hidden = [] ∧ c.twin.rank = Rank.king) := by
      rcases hseatB with h | ⟨hh, hk⟩
      · exact Or.inl (by rw [← hface]; exact h)
      · exact Or.inr ⟨by rw [← hhid]; exact hh, hk⟩
    exact hsu c.twin (CanRaiseS.now c.twin ⟨hnextU, a, hpodU, hseatU⟩)
  · have hlast : lastOf (B.piles a).faceUp = some c := by
      rw [hface]
      exact lastOf_snoc
    have hct : c.twin = c := Option.some.inj (htopB.symm.trans hlast)
    exact _root_.card_twin_ne c hct

/-! ## §4. The seat invariant of the direct cover card -/

/-- **ONE FREE LETTER KEEPS THE DIRECT COVER CARD ON `{c, c.twin}`.** -/
theorem seat_inv_step {st st' : State} {m : Move} {d c : Card}
    (hwf : st.WF) (hrev : reversibleAtW st m)
    (hstep : State.step st m = some st')
    (hfree : ValleyElim.FreeMove m)
    (hfit : canSitOn d c.twin = true) (hnk : d.rank ≠ Rank.king)
    (hinv : seatOf st d = some (Sum.inr c.twin) ∨ seatOf st d = some (Sum.inr c)) :
    seatOf st' d = some (Sum.inr c.twin) ∨ seatOf st' d = some (Sum.inr c) := by
  rcases hfree with rfl | ⟨x, bb, rfl⟩
  · -- draw: piles unchanged
    have hd : st.stepDraw = some st' := by simpa only [State.step] using hstep
    rw [seatOf_congr_piles (stepDraw_piles hd) d]
    exact hinv
  · -- slide
    have hse := tfc_seat_point_edit hwf hstep hrev d
    by_cases hdx : d = x
    · subst hdx
      have hseD : seatOf st' d = some bb := by
        rw [hse]
        exact ite_eq_left rfl
      rw [hseD]
      obtain ⟨-, -, hcp, -, -⟩ := step_tabToTab_inv hstep
      cases bb with
      | inl a =>
          obtain ⟨-, hking⟩ := canPlace_inl hcp
          exact absurd hking hnk
      | inr y =>
          obtain ⟨-, -, hfitY⟩ := canPlace_inr hcp
          rcases LiveKit.parent_eq_or_twin hfit hfitY with hy | hy
          · exact Or.inl (by rw [hy])
          · rw [card_twin_twin] at hy
            exact Or.inr (by rw [hy])
    · rw [hse, ite_eq_right hdx]
      exact hinv

/-- **THE SEAT INVARIANT OVER THE WHOLE FREE TAIL.** -/
theorem seat_inv_play {d c : Card}
    (hfit : canSitOn d c.twin = true) (hnk : d.rank ≠ Rank.king) :
    ∀ {st st' : State} {γ : List Move}, ShufflePlayW st γ st' →
      st.WF →
      (seatOf st d = some (Sum.inr c.twin) ∨ seatOf st d = some (Sum.inr c)) →
      (∀ m ∈ γ, ValleyElim.FreeMove m) →
      seatOf st' d = some (Sum.inr c.twin) ∨ seatOf st' d = some (Sum.inr c) := by
  intro st st' γ hplay
  induction hplay with
  | nil st => intro _ hinv _; exact hinv
  | @cons st s₁ W m ρ hrev hstep hrest ih =>
      intro hwf hinv hfree
      have hwf₁ : s₁.WF := step_wf hwf hstep
      have hhead : ValleyElim.FreeMove m := hfree m (List.mem_cons_self ..)
      have htail : ∀ x ∈ ρ, ValleyElim.FreeMove x :=
        fun x hx => hfree x (List.mem_cons_of_mem m hx)
      exact ih hwf₁ (seat_inv_step hwf hrev hstep hhead hfit hnk hinv) htail

/-! ## §5. The core: no both-raisable twin pair at a `pre = []` bottom -/

/-- The rank pin: the cover card `d` is not a king (it is one rank below the
twin). -/
theorem rank_ne_king_of_fit {d c : Card} (hfit : canSitOn d c.twin = true) :
    d.rank ≠ Rank.king := by
  intro hk
  have h2 : d.rank.toIdx + 1 = c.twin.rank.toIdx := (canSitOn_eq d c.twin).mp hfit |>.1
  rw [hk] at h2
  have h3 : (Rank.king).toIdx = 12 := rfl
  rw [h3] at h2
  have h4 : c.twin.rank.toIdx < 13 := Rank.toIdx_lt c.twin.rank
  omega

/-- **THE CORE.**  At a `pre = []` split bottom the pull card `c` and its
twin cannot both be vanilla-raisable. -/
theorem no_both_nil {u v : State} {ρ : List Move} {F : State}
    {left right : List Move} {c d : Card} {b : Base} {post tail : List Move}
    (h : SplitHyp u v ρ F left right c d b [] post tail)
    (hcanC : CanRaise F c) (hcanT : CanRaise F c.twin) : False := by
  have hF : F.WF := (splitHyp_green h).1
  -- the pull's landing
  obtain ⟨A', B, hpre, hrevP, hstepP, hpost, hA', hB, hcanB, hfreeB⟩ :=
    TailHead.split_pull_landing h
  obtain ⟨huwf, hsu, -, -, -, -, -, hleft, -, hshape, hfree, -⟩ := h
  have hA'u : A' = u := by cases hpre with | nil => rfl
  subst hA'u
  -- the twin is S-live at B
  have hSB : CanRaiseS B c.twin :=
    (Bridge.canRaiseS_of_free_play_iff hpost hfree hB c.twin).mpr
      (CanRaiseS.now c.twin hcanT)
  rcases canRaise_or_covered hB hSB with hvanB | hcovB
  · exact top_case_false huwf hsu hstepP hvanB
  · -- the cover card `d` and its seat invariant
    obtain ⟨d, hd⟩ := hcovB
    have hfit : canSitOn d c.twin = true := LiveKit.canSitOn_of_seat hB hd
    have hnk : d.rank ≠ Rank.king := rank_ne_king_of_fit hfit
    have hinvF : seatOf F d = some (Sum.inr c.twin) ∨ seatOf F d = some (Sum.inr c) :=
      seat_inv_play hfit hnk hpost hB (Or.inl hd) hfree
    rcases hinvF with hseat | hseat
    · exact not_canRaise_of_covered hF ⟨d, hseat⟩ hcanT
    · exact not_canRaise_of_covered hF ⟨d, hseat⟩ hcanC

/-! ## §6. The main `pre = []` theorem -/

/-- `BottomNotBothRaisableNil` — the `pre = []` restriction of
`Pin.BottomNotBothRaisable`. -/
def BottomNotBothRaisableNil : Prop :=
  ∀ (u v : State) (ρ : List Move) (F : State)
    (left right : List Move) (c d : Card) (b : Base)
    (post tail : List Move),
    SplitHyp u v ρ F left right c d b [] post tail →
    ∀ x : Card, F.WF → TwinLivePair F x →
      ¬ (CanRaise F x ∧ CanRaise F x.twin)

/-- **THE `pre = []` CORNER OF `Pin.BottomNotBothRaisable` IS TRUE.** -/
theorem bottomNotBothRaisableNil : BottomNotBothRaisableNil := by
  intro u v ρ F left right c d b post tail h x hF hl hboth
  obtain ⟨hcx, hctx⟩ := hboth
  have hxS : CanRaiseS F x := CanRaiseS.now x hcx
  have hxc : x = c ∨ x = c.twin := TailHead.pre_nil_live_subset h hxS
  rcases hxc with hxc | hxc
  · subst hxc
    exact no_both_nil h hcx hctx
  · subst hxc
    have hc : CanRaise F c := by
      rw [card_twin_twin] at hctx
      exact hctx
    exact no_both_nil h hc hcx

/-- The global statement implies its `pre = []` restriction. -/
theorem bottomNotBothRaisableNil_of_global (h : Pin.BottomNotBothRaisable) :
    BottomNotBothRaisableNil := by
  intro u v ρ F left right c d b post tail hs
  exact h u v ρ F left right c d b [] post tail hs

/-! ### §6b. The exact three-lane decomposition of the global statement -/

/-- The `pre` pull-headed lane (the `ForkPinRight` `PrePullPair` lane). -/
def BottomNotBothPullPre : Prop :=
  ∀ (u v : State) (ρ : List Move) (F : State)
    (left right : List Move) (c d : Card) (b : Base)
    (pre post tail : List Move),
    SplitHyp u v ρ F left right c d b pre post tail →
    (∃ (m : Move) (pre2 : List Move), pre = m :: pre2 ∧
      ¬ ValleyElim.FreeMove m) →
    ∀ x : Card, F.WF → TwinLivePair F x →
      ¬ (CanRaise F x ∧ CanRaise F x.twin)

/-- The free-headed `pre` lane (consumed by the joint induction). -/
def BottomNotBothFreePre : Prop :=
  ∀ (u v : State) (ρ : List Move) (F : State)
    (left right : List Move) (c d : Card) (b : Base)
    (pre post tail : List Move),
    SplitHyp u v ρ F left right c d b pre post tail →
    (∃ (m : Move) (pre2 : List Move), pre = m :: pre2 ∧
      ValleyElim.FreeMove m) →
    ∀ x : Card, F.WF → TwinLivePair F x →
      ¬ (CanRaise F x ∧ CanRaise F x.twin)

theorem bottomNotBothPullPre_of_global (h : Pin.BottomNotBothRaisable) :
    BottomNotBothPullPre :=
  fun u v ρ F left right c d b pre post tail hs _ x hF hl =>
    h u v ρ F left right c d b pre post tail hs x hF hl

theorem bottomNotBothFreePre_of_global (h : Pin.BottomNotBothRaisable) :
    BottomNotBothFreePre :=
  fun u v ρ F left right c d b pre post tail hs _ x hF hl =>
    h u v ρ F left right c d b pre post tail hs x hF hl

/-- **THE GLOBAL STATEMENT IS EXACTLY THE THREE LANES.**  The `pre = []` lane
is PROVED here (`bottomNotBothRaisableNil`); the other two are named. -/
theorem bottomNotBoth_of_parts (hn : BottomNotBothRaisableNil)
    (hp : BottomNotBothPullPre) (hf : BottomNotBothFreePre) :
    Pin.BottomNotBothRaisable := by
  intro u v ρ F left right c d b pre post tail hs x hF hl
  cases pre with
  | nil => exact hn u v ρ F left right c d b post tail hs x hF hl
  | cons m pre2 =>
      cases hv : ValleyElim.isFreeB m with
      | true =>
          exact hf u v ρ F left right c d b (m :: pre2) post tail hs
            ⟨m, pre2, rfl, ValleyElim.isFreeB_eq_true_iff.mp hv⟩ x hF hl
      | false =>
          exact hp u v ρ F left right c d b (m :: pre2) post tail hs
            ⟨m, pre2, rfl, ValleyElim.isFreeB_eq_false_iff.mp hv⟩ x hF hl

theorem bottomNotBoth_iff_parts :
    Pin.BottomNotBothRaisable ↔
      BottomNotBothRaisableNil ∧ BottomNotBothPullPre ∧ BottomNotBothFreePre :=
  ⟨fun h => ⟨bottomNotBothRaisableNil_of_global h,
      bottomNotBothPullPre_of_global h,
      bottomNotBothFreePre_of_global h⟩,
    fun ⟨h1, h2, h3⟩ => bottomNotBoth_of_parts h1 h2 h3⟩

/-- `SplitBlock` supplies the whole global statement (so also all three lanes). -/
theorem bottomNotBothRaisableNil_of_splitBlock (hb : SplitBlock) :
    BottomNotBothRaisableNil :=
  bottomNotBothRaisableNil_of_global (Pin.bottomNotBoth_of_splitBlock hb)

/-! ## §7. The gadget is outside the gate -/

/-- **`gAce` IS NOT A `pre = []` SPLIT BOTTOM.**  Its both-raisable twin pair
would violate `bottomNotBothRaisableNil`. -/
theorem gAce_not_nil_bottom :
    ¬ ∃ (u v : State) (ρ : List Move)
        (left right : List Move) (c d : Card) (b : Base) (post tail : List Move),
      SplitHyp u v ρ Pin.gAce left right c d b [] post tail := by
  rintro ⟨u, v, ρ, left, right, c, d, b, post, tail, h⟩
  exact bottomNotBothRaisableNil u v ρ Pin.gAce left right c d b post tail h
    Pin.AH Pin.gAce_wf Pin.gAce_twinLivePair
    ⟨Pin.gAce_canRaise_AH, Pin.gAce_canRaise_AD⟩

/-! ## §8. Consumers: what the vacuity buys -/

/-- **THE `d = c.twin` BRANCH OF THE `pre = []` BLOCK LANE.**  If the raise
card at a `pre = []` split is the pull card's twin, the pull card is NOT
vanilla-raisable. -/
theorem nilPreTwinBlock {u v : State} {ρ : List Move} {F : State}
    {left right : List Move} {c d : Card} {b : Base} {post tail : List Move}
    (h : SplitHyp u v ρ F left right c d b [] post tail) (hdt : d = c.twin) :
    ¬ CanRaise F c := by
  intro hc
  obtain ⟨hF, -, hcanD, -⟩ := splitHyp_green h
  have hcanT : CanRaise F c.twin := by rw [← hdt]; exact hcanD
  have hl : TwinLivePair F c := by
    intro e
    constructor
    · intro he
      exact TailHead.pre_nil_live_subset h he
    · intro hd
      rcases hd with hd | hd
      · rw [hd]
        exact CanRaiseS.now c hc
      · rw [hd]
        exact CanRaiseS.now c.twin hcanT
  exact bottomNotBothRaisableNil u v ρ F left right c d b post tail h c hF hl
    ⟨hc, hcanT⟩

/-- The `pre = []` block lane, conditional on the same-card half.  The
`d = c.twin` branch is `nilPreTwinBlock`; the `d = c` branch is the named
`SameCardNilBlock` residual (TailHead's cover/no-undo lane). -/
def SameCardNilBlock : Prop :=
  ∀ (u v : State) (ρ : List Move) (F : State)
    (left right : List Move) (c d : Card) (b : Base)
    (post tail : List Move),
    SplitHyp u v ρ F left right c d b [] post tail → d = c →
      ¬ CanRaise F c

/-- **THE `pre = []` LANE OF `PullFirstBlock` FROM THE TWO HALVES.** -/
theorem nilPreBlock_of_parts (hsame : SameCardNilBlock) :
    ∀ (u v : State) (ρ : List Move) (F : State)
      (left right : List Move) (c d : Card) (b : Base)
      (post tail : List Move),
      SplitHyp u v ρ F left right c d b [] post tail →
      post ≠ [] → ¬ CanRaise F c := by
  intro u v ρ F left right c d b post tail h _
  rcases TailHead.pre_nil_turn_dichotomy h with hdc | hdt
  · exact hsame u v ρ F left right c d b post tail h hdc
  · exact nilPreTwinBlock h hdt

/-- **THE FULL CAMPAIGN CHAIN FROM THE THREE LANES** (via
`Pin.satDifferForkWF_of_notBoth`). -/
theorem satDifferForkWF_of_parts (hn : BottomNotBothRaisableNil)
    (hp : BottomNotBothPullPre) (hf : BottomNotBothFreePre)
    (hl : SplitLivePair) (hmin : ValleyElim.ShortestPlayExists) :
    SatDifferForkWF :=
  Pin.satDifferForkWF_of_notBoth hl (bottomNotBoth_of_parts hn hp hf) hmin

end Both

/-! ## §9. Axiom battery -/

#print axioms Both.gAceMid_canRaise_AH
#print axioms Both.gAceMid_not_saturated
#print axioms Both.gAce_not_saturated
#print axioms Both.gAcePre_liveB_false
#print axioms Both.gAcePre_saturated
#print axioms Both.putCard_found'
#print axioms Both.canPlace_setFound
#print axioms Both.putCard_faceUp_cases
#print axioms Both.pull_found_other_suit
#print axioms Both.nextUp_of_step_pull_ne_suit
#print axioms Both.pull_faceUp_cases
#print axioms Both.pull_hidden_eq
#print axioms Both.top_case_false
#print axioms Both.seat_inv_step
#print axioms Both.seat_inv_play
#print axioms Both.rank_ne_king_of_fit
#print axioms Both.no_both_nil
#print axioms Both.bottomNotBothRaisableNil
#print axioms Both.bottomNotBothRaisableNil_of_global
#print axioms Both.bottomNotBothPullPre_of_global
#print axioms Both.bottomNotBothFreePre_of_global
#print axioms Both.bottomNotBoth_of_parts
#print axioms Both.bottomNotBoth_iff_parts
#print axioms Both.bottomNotBothRaisableNil_of_splitBlock
#print axioms Both.gAce_not_nil_bottom
#print axioms Both.nilPreTwinBlock
#print axioms Both.nilPreBlock_of_parts
#print axioms Both.satDifferForkWF_of_parts
