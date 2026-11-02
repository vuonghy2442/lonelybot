import Orig2.Fork.Third.ForkThirdResidual
import Orig2.Fork.Third.ForkThirdCrossing
import Orig2.Fork.Split.ForkLandingLocal
import Orig2.Fork.Local.ForkCriticalPair
import Orig2.Fork.Class.ForkReadBracket
import Orig2.Fork.Class.ForkExistRefute

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

/-!
# Orig2/ForkSurvivor -- the third-suit survivor: gates, kill taxonomy, residual

READ-ONLY scratch (no source touched, no commit).  Zero `sorry`, zero
`Classical.choice`, zero `native_decide`; axiom battery at the tail.

This card attacks `ThirdLive.ThirdBracketRead` (`Orig2/Fork/Third/ForkThirdResidual.lean:93`)
with the tools the brief names: the rank narrowing, the crossing silence, the
frozen `nextUp` at `v`, the saturation of `v`, and `SplitHyp`'s shortest-play
conjunct.  It does **not** prove the residual (the residual is equivalent to the
whole containment, `ThirdLive.thirdBracketRead_iff_landingThirdSuitFree`); it
does the following.

## 1. The gate (kernel)

`SplitHyp` minus its shortest-play conjunct is `SplitHypNoMin`.  The refutation
loop of `Orig2/Fork/Class/ForkExistRefute.lean` (the four letters
`pull 5H->6C ; slide 4C->5H ; slide 4C->5D ; raise 5H`, which returns to its
start) satisfies **every** conjunct of `SplitHyp` except minimality:
`loop_splitHypNoMin`.  Hence `loop_not_splitHyp`: the loop is excluded by the
*hmin* conjunct alone (`splitHyp_not_u_eq_v`).  So the answer to "which gate
excludes the loop" is: `SplitHyp`'s shortest-play clause, applied to the empty
competing play (which exists because the loop's endpoints coincide).

Moreover the loop is not a counterexample to the residual *even ungated*: its
pull landing carries **no** third-suit S-live card at all
(`loop_no_third_survivor`; the only live card there is the pull card itself,
`loop_B_H5_live`).  What the loop *does* refute is the version with the
third-suit hypotheses dropped (`not_landingBracketAllLive`): the third-suit
restriction is load-bearing, and this is the only level at which it can be
tested cheaply.

## 2. The kill taxonomy (kernel)

A play all of whose letters are `R12.ReadOK` for `e` preserves `CanRaise e`
(`canRaise_of_read_play`).  Hence in the frozen branch, where `e` is raisable at
the bottom `F` but dead at the saturated far endpoint `v`, some letter of the
right leg is **not** read-safe for `e` (`frozen_survivor_not_all_read`).  Under
the frozen hypotheses the right leg has no `e.suit` letter
(`crossing_noSigma`-shaped silence) and no pull, so that bad letter is a slide
either headed by `e` or landing on `e` (`frozen_kill_shape`).  A slide landing
on `e` gives an immediate cover whose card *fits* `e`: rank one above, opposite
colour (`kill_card_fits`).  This is exactly the brief's "the kill of `e` is a
seat event".

## 3. The residual, sharpened (kernel)

`SurvivorMateBracket`: the bracket card is pinned to the survivor's rank-mate
(`z = e` or `z = e.twin`) -- the brief's suggested missing lemma ("the cover of
the survivor has a third-suit rank-mate that is pulled and re-raised").
`survivorMateBracket_thirdBracketRead` proves the implication to the residual,
and `survivorMateBracket_card_third` records that the pinned bracket card is a
third-suit card of `e`'s rank (`ThirdLive.bracket_card_third`).  The unpinned
`ThirdBracketRead` does *not* force this pin, so the pinned form is strictly
stronger and is the honest frontier.

## 4. Honest boundary

`ThirdBracketRead` is equivalent to `Landing.LandingThirdSuitFree`, so proving it
is proving the containment.  Any *gated* strengthening is vacuously true on the
same class (if the containment holds, no split carries a survivor), so a cheap
counterexample to a gated strengthening cannot exist without refuting the
containment itself.  This card therefore claims no proof and no counterexample
of the residual; the exact residual and the loop/gate verdict are in
`Temp/Surv_Report.md`.
-/

namespace Surv

open ValleyElim

/-! ## 1. The minimality gate -/

/-- **`SplitHypNoMin`** -- `SplitKit.SplitHyp` with the shortest-play conjunct
removed. -/
def SplitHypNoMin (u v : State) (rho : List Move) (F : State)
    (left right : List Move) (c d : Card) (b : Base)
    (pre post tail : List Move) : Prop :=
  u.WF ∧ SSaturated u ∧ SSaturated v ∧ ShufflePlayW u rho v ∧
  ValleyElim.ValleySplitAt u v rho F ∧
  rho = left ++ right ∧
  ShufflePlayW u left F ∧
  ShufflePlayW F right v ∧
  left = pre ++ Move.foundToTab c b :: post ∧
  (∀ m ∈ post, ValleyElim.FreeMove m) ∧
  right = Move.tabToFound d :: tail

/-- `SplitHyp` is `SplitHypNoMin` plus the shortest-play conjunct. -/
theorem splitHyp_iff_noMin {u v : State} {rho : List Move} {F : State}
    {left right : List Move} {c d : Card} {b : Base}
    {pre post tail : List Move} :
    SplitKit.SplitHyp u v rho F left right c d b pre post tail ↔
      SplitHypNoMin u v rho F left right c d b pre post tail ∧
        (∀ rho' : List Move, ShufflePlayW u rho' v → rho.length ≤ rho'.length) := by
  unfold SplitKit.SplitHyp SplitHypNoMin
  constructor
  · rintro ⟨a, b, c1, d1, e1, f1, g1, h1, i1, j1, k1, l1⟩
    exact ⟨⟨a, b, c1, d1, e1, g1, h1, i1, j1, k1, l1⟩, f1⟩
  · rintro ⟨⟨a, b, c1, d1, e1, g1, h1, i1, j1, k1, l1⟩, f1⟩
    exact ⟨a, b, c1, d1, e1, f1, g1, h1, i1, j1, k1, l1⟩

/-- **NO SPLIT IS A LOOP.**  `SplitHyp`'s shortest-play conjunct kills every
split whose endpoints coincide: the empty play is a competitor. -/
theorem splitHyp_not_u_eq_v {u : State} {rho : List Move} {F : State}
    {left right : List Move} {c d : Card} {b : Base}
    {pre post tail : List Move}
    (h : SplitKit.SplitHyp u u rho F left right c d b pre post tail) : False := by
  obtain ⟨-, -, -, -, -, hmin, hrho, -, -, hshape, -, -⟩ := h
  have hlen : rho.length ≤ 0 := by
    have h0 := hmin [] (Walk.nil u)
    simpa using h0
  have hnil : rho = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp hlen)
  have hleftnil : left = [] := by
    have h' : left ++ right = [] := by rw [← hrho]; exact hnil
    exact (List.append_eq_nil_iff.mp h').1
  rw [hleftnil] at hshape
  have h2 : Move.foundToTab c b :: post = [] :=
    (List.append_eq_nil_iff.mp hshape.symm).2
  exact List.cons_ne_nil _ _ h2

/-- A split play is never empty (it contains the valley pull). -/
theorem splitHyp_rho_ne_nil {u v : State} {rho : List Move} {F : State}
    {left right : List Move} {c d : Card} {b : Base}
    {pre post tail : List Move}
    (h : SplitKit.SplitHyp u v rho F left right c d b pre post tail) :
    rho ≠ [] := by
  obtain ⟨-, -, -, -, -, -, hrho, -, -, hshape, -, -⟩ := h
  intro hnil
  have hl : left = [] := by
    have h' : left ++ right = [] := by rw [← hrho]; exact hnil
    exact (List.append_eq_nil_iff.mp h').1
  rw [hl] at hshape
  exact List.cons_ne_nil _ _
    ((List.append_eq_nil_iff.mp hshape.symm).2)

/-- **THE LOOP `Orig2/Fork/Class/ForkExistRefute.lean` SATISFIES EVERY CONJUNCT OF
`SplitHyp` EXCEPT MINIMALITY.** -/
theorem loop_splitHypNoMin :
    SplitHypNoMin ExistRefute.u ExistRefute.V ExistRefute.rho ExistRefute.F
      [ExistRefute.mPull, ExistRefute.mS1, ExistRefute.mS2] [ExistRefute.mRaise]
      ExistRefute.H5 ExistRefute.H5 (Sum.inr ExistRefute.C6) []
      [ExistRefute.mS1, ExistRefute.mS2] [] := by
  refine ⟨ExistRefute.u_wf, ExistRefute.u_sat, ExistRefute.V_sat,
    ExistRefute.play, ExistRefute.split, rfl, ExistRefute.play_u_B,
    ExistRefute.play_F_V, rfl, ?_, rfl⟩
  intro m hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl
  · exact free_slide ExistRefute.C4 (Sum.inr ExistRefute.H5)
  · exact free_slide ExistRefute.C4 (Sum.inr ExistRefute.D5)

/-- **THE LOOP IS EXCLUDED BY THE MINIMALITY GATE ALONE.** -/
theorem loop_not_splitHyp :
    ¬ SplitKit.SplitHyp ExistRefute.u ExistRefute.V ExistRefute.rho ExistRefute.F
      [ExistRefute.mPull, ExistRefute.mS1, ExistRefute.mS2] [ExistRefute.mRaise]
      ExistRefute.H5 ExistRefute.H5 (Sum.inr ExistRefute.C6) []
      [ExistRefute.mS1, ExistRefute.mS2] [] := by
  intro h
  rw [ExistRefute.V_eq_u] at h
  exact splitHyp_not_u_eq_v h

/-! ### 1b. The loop's landing carries no third-suit survivor -/

/-- The only S-live card at the loop's pull landing `B` is `5H` itself. -/
theorem loop_B_liveB :
    (Card.universe.all
      (fun c => !(canRaiseSB ExistRefute.B c) || decide (c = ExistRefute.H5))) = true := by
  decide

/-- Hence every S-live card at `B` is the pull card. -/
theorem loop_B_live_eq {c : Card} (h : CanRaiseS ExistRefute.B c) :
    c = ExistRefute.H5 := by
  have h1 : canRaiseSB ExistRefute.B c = true :=
    (canRaiseSB_iff ExistRefute.B_wf).mpr h
  have h2 := (List.all_eq_true.mp loop_B_liveB) c (Card.mem_universe c)
  cases hc : canRaiseSB ExistRefute.B c with
  | false =>
      exfalso
      rw [hc] at h1
      exact Bool.false_ne_true h1
  | true =>
      simp only [hc, Bool.not_true, Bool.false_or] at h2
      exact of_decide_eq_true h2

/-- The pull card itself is S-live at the loop's landing. -/
theorem loop_B_H5_live : CanRaiseS ExistRefute.B ExistRefute.H5 :=
  (canRaiseSB_iff ExistRefute.B_wf).mp (by decide)

/-- **THE LOOP HAS NO THIRD-SUIT SURVIVOR AT ITS LANDING.**  So the loop is not
a counterexample to the residual even without the minimality gate. -/
theorem loop_no_third_survivor :
    ¬ ∃ e : Card, CanRaiseS ExistRefute.B e ∧
      e.suit ≠ ExistRefute.H5.suit ∧ e.suit ≠ ExistRefute.H5.twin.suit := by
  rintro ⟨e, he, h1, -⟩
  have hE : e = ExistRefute.H5 := loop_B_live_eq he
  subst hE
  exact h1 rfl

/-! ### 1c. The third-suit hypotheses are load-bearing (necessity) -/

/-- The residual's syntactic shape **without** the `SplitHyp` gate and
**without** the third-suit hypotheses. -/
def LandingBracketAllLive : Prop :=
  ∀ (u v : State) (rho : List Move) (F : State)
    (left right : List Move) (c d : Card) (b : Base)
    (pre post tail : List Move),
    u.WF → SSaturated u → SSaturated v → ShufflePlayW u rho v →
    ValleyElim.ValleySplitAt u v rho F →
    rho = left ++ right →
    left = pre ++ Move.foundToTab c b :: post →
    (∀ m ∈ post, ValleyElim.FreeMove m) →
    right = Move.tabToFound d :: tail →
    ∀ (A' B : State), ShufflePlayW u pre A' →
      State.step A' (Move.foundToTab c b) = some B →
      ∀ e : Card, CanRaiseS B e →
      ∃ (α γ β : List Move) (z : Card) (bz : Base) (P Q : State),
        rho = α ++ Move.foundToTab z bz :: γ ++ Move.tabToFound z :: β ∧
        (∀ q ∈ γ, R12.ReadOK z q)

/-- **THE THIRD-SUIT HYPOTHESES CANNOT BE DROPPED** (at the ungated level): the
loop is a valley split whose landing has the S-live card `5H` but no read-safe
same-card bracket anywhere (`ExistRefute.no_bracket_data`). -/
theorem not_landingBracketAllLive : ¬ LandingBracketAllLive := by
  intro h
  have hb := h ExistRefute.u ExistRefute.V ExistRefute.rho ExistRefute.F
    [ExistRefute.mPull, ExistRefute.mS1, ExistRefute.mS2] [ExistRefute.mRaise]
    ExistRefute.H5 ExistRefute.H5 (Sum.inr ExistRefute.C6) []
    [ExistRefute.mS1, ExistRefute.mS2] []
    ExistRefute.u_wf ExistRefute.u_sat ExistRefute.V_sat ExistRefute.play
    ExistRefute.split rfl rfl ?_ rfl
    ExistRefute.u ExistRefute.B (Walk.nil ExistRefute.u) ExistRefute.step_pull
    ExistRefute.H5 loop_B_H5_live
  · obtain ⟨α, γ, β, z, bz, P, Q, hρ, hread⟩ := hb
    exact ExistRefute.no_bracket_data ⟨α, γ, β, z, bz, hρ, hread⟩
  · intro m hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl
    · exact free_slide ExistRefute.C4 (Sum.inr ExistRefute.H5)
    · exact free_slide ExistRefute.C4 (Sum.inr ExistRefute.D5)

/-! ## 2. The kill taxonomy -/

/-- `R12.ReadOK` is decidable: all its clauses are decidable equalities on the
finite card/suit/base types.  This keeps the kill search constructive. -/
instance readOKDecidable (z : Card) (q : Move) : Decidable (R12.ReadOK z q) := by
  cases q <;> simp only [R12.ReadOK] <;> infer_instance

/-- A play whose every letter is read-safe for `e` preserves `CanRaise e`. -/
theorem canRaise_of_read_play {F v : State} {play : List Move} {e : Card}
    (hplay : ShufflePlayW F play v) (hF : F.WF)
    (hread : ∀ q ∈ play, R12.ReadOK e q) (hcan : CanRaise F e) :
    CanRaise v e := by
  induction hplay generalizing e with
  | nil => exact hcan
  | @cons st s1 W m rest hrev hstep hrest ih =>
      have hswf : s1.WF := step_wf hF hstep
      have hm : R12.ReadOK e m := hread m (List.mem_cons_self ..)
      have htail : ∀ q ∈ rest, R12.ReadOK e q :=
        fun q hq => hread q (List.mem_cons_of_mem m hq)
      exact ih hswf htail (R12.canRaise_survives_read hF hstep hrev hm hcan)

/-- **A DEAD SURVIVOR FORCES A BAD LETTER.**  If `e` is raisable at `F` and not
at the end of `right`, some letter of `right` is not read-safe for `e`. -/
theorem frozen_survivor_not_all_read {F v : State} {right : List Move} {e : Card}
    (hplay : ShufflePlayW F right v) (hF : F.WF)
    (hcan : CanRaise F e) (hdead : ¬ CanRaise v e) :
    ¬ ∀ q ∈ right, R12.ReadOK e q :=
  fun hread => hdead (canRaise_of_read_play hplay hF hread hcan)

/-- Constructive finite extraction: a failed universal over a list yields a
counterexample. -/
theorem exists_bad_of_not_all {play : List Move} {e : Card}
    (h : ¬ ∀ q, q ∈ play → R12.ReadOK e q) :
    ∃ q, q ∈ play ∧ ¬ R12.ReadOK e q := by
  induction play with
  | nil =>
      exact absurd (fun q hq => by cases hq) h
  | cons a t ih =>
      by_cases ha : R12.ReadOK e a
      · have ht : ¬ ∀ q, q ∈ t → R12.ReadOK e q := by
          intro htall
          exact h (fun q hq => by
            rcases List.mem_cons.mp hq with rfl | hq'
            · exact ha
            · exact htall q hq')
        obtain ⟨q, hq, hnq⟩ := ih ht
        exact ⟨q, List.mem_cons_of_mem a hq, hnq⟩
      · exact ⟨a, List.mem_cons_self .., ha⟩

/-- Every letter of a witness play is reversible at *some* origin. -/
theorem walk_exists_reversible {u v : State} {play : List Move}
    (h : ShufflePlayW u play v) :
    ∀ q ∈ play, ∃ st : State, reversibleAtW st q := by
  induction h with
  | nil => intro q hq; exact absurd hq (by cases hq)
  | @cons st s1 W m rest hrev hstep hrest ih =>
      intro q hq
      rcases List.mem_cons.mp hq with rfl | hq'
      · exact ⟨st, hrev⟩
      · exact ih q hq'

/-- A letter of a witness play fires somewhere. -/
theorem exists_step_of_mem {u v : State} {play : List Move} {q : Move}
    (hplay : ShufflePlayW u play v) (hq : q ∈ play) :
    ∃ st st', State.step st q = some st' := by
  obtain ⟨s, t, rfl⟩ := List.mem_iff_append.mp hq
  obtain ⟨mid, -, hrest⟩ := ValleyElim.ShufflePlayW_split hplay s (q :: t) rfl
  obtain ⟨st', -, hstep, -⟩ := Bubble.walk_cons_inv hrest
  exact ⟨mid, st', hstep⟩

/-- **THE SHAPE OF THE BAD LETTER.**  A non-read-safe letter of a reversible
play that is neither an `e.suit` letter (`NoSigmaLetter`) nor a pull is a slide
either headed by `e` or landing on `e`. -/
theorem bad_letter_shape {play : List Move} {e : Card}
    (hrev : ∀ q ∈ play, ∃ st : State, reversibleAtW st q)
    (hbad : ∃ q, q ∈ play ∧ ¬ R12.ReadOK e q)
    (hno : ∀ m ∈ play, ThirdLive.NoSigmaLetter e.suit m)
    (hnp : ∀ m ∈ play, ¬ Bubble.IsPull m) :
    ∃ c b, Move.tabToTab c b ∈ play ∧ (c = e ∨ b = Sum.inr e) := by
  obtain ⟨q, hq, hbadq⟩ := hbad
  obtain ⟨st, hrevq⟩ := hrev q hq
  cases q with
  | draw => exact absurd trivial hbadq
  | wasteToFound w =>
      exact absurd hrevq (wasteToFound_not_reversibleAtW st w)
  | wasteToTab w b =>
      exact absurd hrevq (wasteToTab_not_reversibleAtW st w b)
  | tabToFound w =>
      have hws : w.suit = e.suit := by
        by_cases h : w.suit = e.suit
        · exact h
        · exact absurd h hbadq
      exact absurd hws ((hno (Move.tabToFound w) hq).2 w rfl)
  | foundToTab c b =>
      exact absurd ⟨c, b, rfl⟩ (hnp (Move.foundToTab c b) hq)
  | tabToTab c b =>
      refine ⟨c, b, hq, ?_⟩
      by_cases hc : c = e
      · exact Or.inl hc
      · right
        by_cases hb : b = Sum.inr e
        · exact hb
        · exact absurd ⟨hc, hb⟩ hbadq

/-- **THE KILL OF A FROZEN SURVIVOR IS A SLIDE HEADED BY `e` OR LANDING ON `e`.**
The frozen hypotheses supply both the `e.suit`-silence and the pull-freeness of
the right leg. -/
theorem frozen_kill_shape {F v : State} {right : List Move} {e : Card}
    (hplay : ShufflePlayW F right v) (hF : F.WF)
    (hcan : CanRaise F e) (hdead : ¬ CanRaise v e)
    (hno : ∀ m ∈ right, ThirdLive.NoSigmaLetter e.suit m)
    (hnp : ∀ m ∈ right, ¬ Bubble.IsPull m) :
    ∃ c b, Move.tabToTab c b ∈ right ∧ (c = e ∨ b = Sum.inr e) :=
  bad_letter_shape (walk_exists_reversible hplay)
    (exists_bad_of_not_all (frozen_survivor_not_all_read hplay hF hcan hdead))
    hno hnp

/-- A slide landing on `e` fits: its head is one rank above `e` and of the
opposite colour. -/
theorem kill_card_fits {st st' : State} {c e : Card}
    (hstep : State.step st (Move.tabToTab c (Sum.inr e)) = some st') :
    canSitOn c e = true ∧ c.rank.toIdx + 1 = e.rank.toIdx ∧
      c.suit.color ≠ e.suit.color := by
  obtain ⟨-, -, hcp, -, -⟩ := step_tabToTab_inv hstep
  obtain ⟨k, -, hfit⟩ := canPlace_inr hcp
  obtain ⟨hr, hcol⟩ := (canSitOn_eq c e).mp hfit
  exact ⟨hfit, hr, hcol⟩

/-- **THE FROZEN COVER DICHOTOMY.**  If `e` is vanilla-raisable at the bottom,
its death in the frozen right leg is caused by a slide that either moves `e` as
a run head or covers it with a card that fits (`rank` one above, opposite
colour). -/
theorem frozen_cover_fit {F v : State} {right : List Move} {e : Card}
    (hplay : ShufflePlayW F right v) (hF : F.WF)
    (hcan : CanRaise F e) (hdead : ¬ CanRaise v e)
    (hno : ∀ m ∈ right, ThirdLive.NoSigmaLetter e.suit m)
    (hnp : ∀ m ∈ right, ¬ Bubble.IsPull m) :
    (∃ c b, Move.tabToTab c b ∈ right ∧ c = e) ∨
      (∃ c, Move.tabToTab c (Sum.inr e) ∈ right ∧ canSitOn c e = true ∧
        c.rank.toIdx + 1 = e.rank.toIdx ∧ c.suit.color ≠ e.suit.color) := by
  obtain ⟨c, b, hmem, hdisj⟩ := frozen_kill_shape hplay hF hcan hdead hno hnp
  rcases hdisj with rfl | rfl
  · exact Or.inl ⟨c, b, hmem, rfl⟩
  · right
    obtain ⟨st, st', hstep⟩ := exists_step_of_mem hplay hmem
    obtain ⟨hfit, hr, hcol⟩ := kill_card_fits hstep
    exact ⟨c, hmem, hfit, hr, hcol⟩

/-- **THE SURVIVOR'S MECHANISM AT A VIOLATING SPLIT.**  A third-suit card that
is S-live at the bottom `F` of a split and dead at the saturated far endpoint
`v` is in one of three local configurations: already covered at `F`; moved as a
run head by a right-leg slide; or covered by a right-leg slide whose head fits
it (`rank` one above, opposite colour).  Every case carries the fitting card
that the brief's mechanism wants. -/
theorem frozen_survivor_mechanism
    {F v : State} {right : List Move} {e : Card}
    (hplay : ShufflePlayW F right v) (hF : F.WF)
    (hsF : CanRaiseS F e) (hdead : ¬ CanRaise v e)
    (hno : ∀ m ∈ right, ThirdLive.NoSigmaLetter e.suit m)
    (hnp : ∀ m ∈ right, ¬ Bubble.IsPull m) :
    (∃ d, seatOf F d = some (Sum.inr e) ∧ canSitOn d e = true ∧
        d.rank.toIdx + 1 = e.rank.toIdx ∧ d.suit.color ≠ e.suit.color) ∨
      (∃ c b, Move.tabToTab c b ∈ right ∧ c = e) ∨
      (∃ c, Move.tabToTab c (Sum.inr e) ∈ right ∧ canSitOn c e = true ∧
        c.rank.toIdx + 1 = e.rank.toIdx ∧ c.suit.color ≠ e.suit.color) := by
  rcases canRaise_or_covered hF hsF with hcan | hcov
  · rcases frozen_cover_fit hplay hF hcan hdead hno hnp with h1 | h2
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr h2)
  · obtain ⟨d, hd⟩ := hcov
    have hfit : canSitOn d e = true := LiveKit.canSitOn_of_seat hF hd
    obtain ⟨hr, hcol⟩ := (canSitOn_eq d e).mp hfit
    exact Or.inl ⟨d, hd, hfit, hr, hcol⟩

/-- **THE SPLIT'S OWN RAISE IS OUTSIDE THE SURVIVOR'S SUIT.**  In the frozen
branch the right leg carries no `e.suit` letter, so the split's raise card `d`
is not in `e`'s suit; in particular, a pinned bracket for `z = e` cannot close
on the split's own `raise d`. -/
theorem frozen_split_raise_suit_ne
    {right : List Move} {d : Card} {tail : List Move} {e : Card}
    (hright : right = Move.tabToFound d :: tail)
    (hno : ∀ m ∈ right, ThirdLive.NoSigmaLetter e.suit m) :
    d.suit ≠ e.suit :=
  (hno (Move.tabToFound d) (by rw [hright]; exact List.mem_cons_self ..)).2 d rfl

/-- **THE FROZEN SELF-BRACKET LIVES IN THE PREFIX.**  In the frozen branch the
whole play after `pre` is `e.suit`-letter-free for pulls and raises (`post` is
free, `right` is `σ`-silent and pull-free, and the valley pull is `c`'s).  Hence
both letters of any same-card bracket of `e` itself lie in `pre`: a bracket for
`z = e` can only be a bracket **inside the split's prefix**. -/
theorem frozen_self_bracket_letters_in_pre
    {u v : State} {rho : List Move} {F : State} {left right : List Move}
    {c d : Card} {b : Base} {pre post tail : List Move}
    (hs : SplitKit.SplitHyp u v rho F left right c d b pre post tail)
    {e : Card} (h1 : e.suit ≠ c.suit)
    {α γ β : List Move} {bz : Base}
    (hbr : rho = α ++ Move.foundToTab e bz :: γ ++ Move.tabToFound e :: β)
    (hno : ∀ m ∈ right, ThirdLive.NoSigmaLetter e.suit m) :
    Move.foundToTab e bz ∈ pre ∧ Move.tabToFound e ∈ pre := by
  obtain ⟨-, -, -, -, -, -, hρlr, -, -, hshape, hfree, hright⟩ := hs
  have hpre : rho = pre ++ (Move.foundToTab c b :: (post ++ right)) := by
    rw [hρlr, hshape, hright]
    simp only [List.cons_append, List.append_assoc]
  have hmem1 : Move.foundToTab e bz ∈ rho := by
    rw [hbr]; simp
  have hmem2 : Move.tabToFound e ∈ rho := by
    rw [hbr]; simp
  have hnot1 : Move.foundToTab e bz ∉ (Move.foundToTab c b :: (post ++ right)) := by
    intro hm
    rcases List.mem_cons.mp hm with heq | hm
    · injection heq with he _
      exact h1 (by rw [he])
    · rcases List.mem_append.mp hm with hp | hr
      · rcases hfree _ hp with hd | ⟨cc, bb, ht⟩
        · exact absurd hd (by simp)
        · exact absurd ht (by simp)
      · exact ((hno _ hr).1 e bz rfl) rfl
  have hnot2 : Move.tabToFound e ∉ (Move.foundToTab c b :: (post ++ right)) := by
    intro hm
    rcases List.mem_cons.mp hm with heq | hm
    · exact absurd heq (by simp)
    · rcases List.mem_append.mp hm with hp | hr
      · rcases hfree _ hp with hd | ⟨cc, bb, ht⟩
        · exact absurd hd (by simp)
        · exact absurd ht (by simp)
      · exact ((hno _ hr).2 e rfl) rfl
  constructor
  · have h := hmem1
    rw [hpre] at h
    rcases List.mem_append.mp h with h' | h'
    · exact h'
    · exact absurd h' hnot1
  · have h := hmem2
    rw [hpre] at h
    rcases List.mem_append.mp h with h' | h'
    · exact h'
    · exact absurd h' hnot2

/-! ## 3. The residual, sharpened to the survivor's rank-mate -/

/-- **`SurvivorMateBracket` -- THE PINNED RESIDUAL.**  The bracket's card is a
rank-mate of the survivor (`z = e` or `z = e.twin`), i.e. the brief's missing
lemma "the cover of the survivor has a third-suit rank-mate that is pulled and
re-raised".  This is strictly stronger than `ThirdLive.ThirdBracketRead`, whose
`z` is unconstrained. -/
def SurvivorMateBracket : Prop :=
  ∀ (u v : State) (rho : List Move) (F : State)
    (left right : List Move) (c d : Card) (b : Base)
    (pre post tail : List Move),
    SplitKit.SplitHyp u v rho F left right c d b pre post tail →
    ∀ (A' B : State), ShufflePlayW u pre A' →
      State.step A' (Move.foundToTab c b) = some B →
      ∀ e : Card, CanRaiseS B e → e.suit ≠ c.suit → e.suit ≠ c.twin.suit →
      ∃ (α γ β : List Move) (z : Card) (bz : Base) (P Q : State),
        (e = z ∨ e = z.twin) ∧
        rho = α ++ Move.foundToTab z bz :: γ ++ Move.tabToFound z :: β ∧
        ShufflePlayW u α P ∧
        State.step P (Move.foundToTab z bz) = some Q ∧
        (∀ q ∈ γ, R12.ReadOK z q)

/-- **THE PINNED RESIDUAL IMPLIES `ThirdBracketRead`.** -/
theorem survivorMateBracket_thirdBracketRead (h : SurvivorMateBracket) :
    ThirdLive.ThirdBracketRead := by
  intro u v rho F left right c d b pre post tail hs A' B hpre hstep e he h1 h2
  obtain ⟨α, γ, β, z, bz, P, Q, -, hρ, hα, hstepP, hread⟩ :=
    h u v rho F left right c d b pre post tail hs A' B hpre hstep e he h1 h2
  exact ⟨α, γ, β, z, bz, P, Q, hρ, hα, hstepP, hread⟩

/-- **THE PINNED BRACKET CARD IS ITSELF A THIRD-SUIT CARD OF `e`'s RANK** (the
geometry row `ThirdLive.bracket_card_third` applied to the pin). -/
theorem survivorMateBracket_card_third (h : SurvivorMateBracket)
    {u v : State} {rho : List Move} {F : State} {left right : List Move}
    {c d : Card} {b : Base} {pre post tail : List Move}
    (hs : SplitKit.SplitHyp u v rho F left right c d b pre post tail)
    {A' B : State} (hpre : ShufflePlayW u pre A')
    (hstep : State.step A' (Move.foundToTab c b) = some B)
    {e : Card} (he : CanRaiseS B e) (h1 : e.suit ≠ c.suit)
    (h2 : e.suit ≠ c.twin.suit) :
    ∃ (z : Card) (bz : Base),
      (e = z ∨ e = z.twin) ∧ z.suit ≠ c.suit ∧ z.suit ≠ c.twin.suit ∧
        z.rank = e.rank := by
  obtain ⟨α, γ, β, z, bz, P, Q, hmem, -, -, -, -⟩ :=
    h u v rho F left right c d b pre post tail hs A' B hpre hstep e he h1 h2
  obtain ⟨⟨hz1, hz2⟩, hzr⟩ := ThirdLive.bracket_card_third hmem h1 h2
  exact ⟨z, bz, hmem, hz1, hz2, hzr⟩

/-- **THE PIN IS REALIZABLE IN `pre`.**  The split data already supplies an
earlier pull of a card in `{e, e.twin}` inside `pre`
(`LandKit.landing_third_suit_earlier_pull`), so `SurvivorMateBracket`'s pin is
exactly the shape the crossing gives -- what is missing is only the returning
raise and the read-safety of its interior. -/
theorem survivor_earlier_mate_pull
    {u v : State} {rho : List Move} {F : State} {left right : List Move}
    {c d : Card} {b : Base} {pre post tail : List Move}
    (hs : SplitKit.SplitHyp u v rho F left right c d b pre post tail)
    (hall : ∀ m ∈ pre, LandKit.FreeOrPull m)
    {A' B : State} (hpre : ShufflePlayW u pre A')
    (hstep : State.step A' (Move.foundToTab c b) = some B)
    {e : Card} (he : CanRaiseS B e) (h1 : e.suit ≠ c.suit)
    (h2 : e.suit ≠ c.twin.suit) :
    ∃ (α : List Move) (z : Card) (bz : Base) (β : List Move),
      pre = α ++ Move.foundToTab z bz :: β ∧ (e = z ∨ e = z.twin) := by
  obtain ⟨huwf, hsu, -, -, -, -, -, -, -, -, -, -⟩ := hs
  exact LandKit.landing_third_suit_earlier_pull hpre huwf hsu hall hstep he
    (fun hc => h1 (by rw [hc]))
    (fun ht => h2 (by rw [ht]))

end Surv

#print axioms Surv.splitHyp_iff_noMin
#print axioms Surv.splitHyp_not_u_eq_v
#print axioms Surv.splitHyp_rho_ne_nil
#print axioms Surv.loop_splitHypNoMin
#print axioms Surv.loop_not_splitHyp
#print axioms Surv.loop_B_liveB
#print axioms Surv.loop_B_live_eq
#print axioms Surv.loop_B_H5_live
#print axioms Surv.loop_no_third_survivor
#print axioms Surv.not_landingBracketAllLive
#print axioms Surv.readOKDecidable
#print axioms Surv.canRaise_of_read_play
#print axioms Surv.frozen_survivor_not_all_read
#print axioms Surv.exists_bad_of_not_all
#print axioms Surv.walk_exists_reversible
#print axioms Surv.exists_step_of_mem
#print axioms Surv.bad_letter_shape
#print axioms Surv.frozen_kill_shape
#print axioms Surv.kill_card_fits
#print axioms Surv.frozen_cover_fit
#print axioms Surv.frozen_survivor_mechanism
#print axioms Surv.frozen_split_raise_suit_ne
#print axioms Surv.frozen_self_bracket_letters_in_pre
#print axioms Surv.SurvivorMateBracket
#print axioms Surv.survivorMateBracket_thirdBracketRead
#print axioms Surv.survivorMateBracket_card_third
#print axioms Surv.survivor_earlier_mate_pull

