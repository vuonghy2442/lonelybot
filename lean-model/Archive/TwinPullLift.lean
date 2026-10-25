import Orig2.TwinForcedCancel

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 1000000

/-!
# Orig2.TwinPullLift — the attachment lift, corrected

`TwinForcedCancel.PullLift x y p` asks that attaching `y` on the pile
topped by `p` be functorial along a pair-free play `s2 → s1`:

```
pulledAt s2 y (inr p)  →  pulledAt s1 y (inr p)
```

The definition only assumes `y ∈ s.found y.suit` at the two endpoints.
That hypothesis is too weak: `pulledAt` is `setFound y.suit (chop ...)`
followed by `putCard y (inr p)`, so it always removes the **last** card
of `y`'s foundation row, whether or not that card is `y`.  If `y` is not
the foundation top at both ends, the two attached states can have
different card multisets, and no play can join them.  This file

* proves that the stated `PullLift` is false by a concrete counterexample
  (the missing hypothesis is `foundTop y.suit = some y`);
* states the corrected lift `PullLiftTop`, where `y` is the foundation
  top at both ends (exactly the hypothesis available in the detour
  application: `s1` is immediately after `tabToFound y`, and `s2` is
  immediately before `foundToTab y`, so `foundTop y.suit = some y` in
  both);
* proves the attachment API (`Att_found`, `Att_piles`, `Att_wf`) and the
  away-letter context invariant `Ctx.step_away`: a pair-free letter that
  neither moves `y`, nor touches the foundation row of `y`, nor raises
  or targets `p`, carries the whole attachment context (`WF`, `y`
  unseated and foundation-top, `p` a pile top, the static fit);
* records the precise obstruction rows at the attached state (a letter
  that raises `p`, or targets `p`, cannot fire because `p` is covered by
  `y`);
* isolates the exact remaining local squares as
  `RaiseSquareResidual` (the raise letter), `PullSquareResidual` (the
  pull letter), and `SlideSquareResidual` (the slide letter), and
  combines them in `AttSquareResidual`.

The corrected global lift remains open at the raise/pull/slide step
squares.  The draw row is proved (`pulledAt_step_comm`); the context
invariant and the obstruction rows are proved; the literal target is
refuted.  No `sorry` is used anywhere.

Everything here is `sorry`-free, `Classical.choice`-free, and uses no
new axioms.

## Main results

* `pullLift_false` — the literal `TwinForcedCancel.PullLift` is false.
* `pullLift_of_pullLiftTop` — the corrected lift supplies the literal
  one whenever the two foundation-top hypotheses are available.
* `pulledAt_step_comm` — the draw commutation square.
* `Ctx.step_away` — the away-letter context invariant.
* `Att_pileOfTop_p_none`, `Att_step_tabToFound_p_none`,
  `Att_step_tabToTab_target_p_none`, `Att_step_foundToTab_target_p_none`,
  `Att_step_wasteToTab_target_p_none` — the obstruction rows.
* `RaiseSquareResidual`, `PullSquareResidual`, `SlideSquareResidual`,
  `AttSquareResidual` — the exact remaining local obligations.
-/

open State

namespace TwinPullLift

/-! ## §0. The counterexample: why the literal `PullLift` fails -/

/-- The pulled card: `5♠`. -/
private def y5S : Card := ⟨Suit.spade, Rank.five⟩

/-- The card raised by the witness play: `6♠`. -/
private def s6 : Card := ⟨Suit.spade, Rank.six⟩

/-- The attachment card (the pile top): `6♥`. -/
private def h6 : Card := ⟨Suit.heart, Rank.six⟩

/-- The chop card under `6♠`: `7♥`. -/
private def h7 : Card := ⟨Suit.heart, Rank.seven⟩

/-- A card of the pair that is never touched: `9♣`. -/
private def x9C : Card := ⟨Suit.club, Rank.nine⟩

/-- The union of the foundation and tableau cards of the witness states.
Both witness states have the same union (the raise only moves `6♠` from
the pile to the spade foundation), so they can share one stock. -/
private def placed : List Card :=
  (Suit.upCards Suit.spade).take 6 ++
  ((Suit.upCards Suit.heart).take 5 ++ [h6, h7]) ++
  (Suit.upCards Suit.diamond).take 5 ++
  (Suit.upCards Suit.club).take 5

/-- The 29 cards left after `placed`. -/
private def stockList : List Card :=
  Card.universe.filter (fun c => decide (¬ c ∈ placed))

/-- The witness-state builder: `nS` spade foundation cards, the given
pile at `p1`, five cards in each other foundation, `6♥` alone at `p0`. -/
private def mkSt (nS : Nat) (p1 : Pile) : State :=
  { found := fun s =>
      match s with
      | .spade => (Suit.upCards .spade).take nS
      | .heart => (Suit.upCards .heart).take 5
      | .diamond => (Suit.upCards .diamond).take 5
      | .club => (Suit.upCards .club).take 5
    piles := fun a =>
      match a with
      | .p0 => ⟨[], [h6]⟩
      | .p1 => p1
      | _ => ⟨[], []⟩
    stock := stockList
    waste := []
    drawStep := 1 }

/-- The source: `5♠` is the top of the spade foundation and `6♠` sits
on `7♥`. -/
private def s2c : State := mkSt 5 ⟨[], [h7, s6]⟩

/-- The target: `6♠` has been raised, so `5♠` is no longer the spade
foundation top (but is still in the foundation and unseated). -/
private def s1c : State := mkSt 6 ⟨[], [h7]⟩

private def allTrue (l : List Card) (p : Card → Bool) : Bool :=
  match l with
  | [] => true
  | x :: t => (p x && allTrue t p)

private theorem allTrue_forall {l : List Card} {p : Card → Bool}
    (h : allTrue l p = true) : ∀ x ∈ l, p x = true := by
  induction l with
  | nil => intro x hx; cases hx
  | cons y t ih =>
      intro x hx
      rw [allTrue, Bool.and_eq_true] at h
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact h.1
      · exact ih h.2 x hx'

private theorem s2c_wf : s2c.WF := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s
    cases s with
    | spade => exact ⟨5, rfl⟩
    | heart => exact ⟨5, rfl⟩
    | diamond => exact ⟨5, rfl⟩
    | club => exact ⟨5, rfl⟩
  · intro a
    cases a with
    | p0 => decide
    | p1 => decide
    | p2 => decide
    | p3 => decide
    | p4 => decide
    | p5 => decide
    | p6 => decide
  · intro c hc
    exact of_decide_eq_true
      (allTrue_forall (l := Card.universe) (p := fun c =>
        decide (s2c.cardCount c = 1)) (by decide) c hc)
  · decide

private theorem s1c_wf : s1c.WF := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s
    cases s with
    | spade => exact ⟨6, rfl⟩
    | heart => exact ⟨5, rfl⟩
    | diamond => exact ⟨5, rfl⟩
    | club => exact ⟨5, rfl⟩
  · intro a
    cases a with
    | p0 => decide
    | p1 => decide
    | p2 => decide
    | p3 => decide
    | p4 => decide
    | p5 => decide
    | p6 => decide
  · intro c hc
    exact of_decide_eq_true
      (allTrue_forall (l := Card.universe) (p := fun c =>
        decide (s1c.cardCount c = 1)) (by decide) c hc)
  · decide

/-- The witness raise fires. -/
private theorem s2c_step_raise :
    State.step s2c (Move.tabToFound s6) = some s1c := by
  rw [step_tabToFound_splice (k := Anchor.p1) (by decide) (by decide)]
  apply congrArg some
  apply State.ext
  · funext s
    cases s <;> rfl
  · funext a
    cases a <;> rfl
  · rfl
  · rfl
  · rfl

/-- The witness raise is reversible (the chop under `6♠` is `7♥`). -/
private theorem s2c_rev_raise : reversibleAtW s2c (Move.tabToFound s6) :=
  (tabToFoundR_iff_reversibleAtW s2c_wf s6).mp (by decide)

/-- The witness play. -/
private theorem s2c_play : ShufflePlayW s2c [Move.tabToFound s6] s1c :=
  Walk.cons s2c_rev_raise s2c_step_raise (Walk.nil s1c)

/-- The witness play is pair-free for `9♣`. -/
private theorem s2c_play_pairFree :
    ∀ m ∈ [Move.tabToFound s6], NotFoundPair x9C m := by
  intro m hm
  rw [List.mem_singleton] at hm
  subst hm
  refine ⟨by decide, by decide, ?_, ?_⟩
  · intro b h
    cases h
  · intro b h
    cases h

/-- `5♠` is unseated at both witness endpoints. -/
private theorem s2c_seatY_none : seatOf s2c y5S = none := by decide
private theorem s1c_seatY_none : seatOf s1c y5S = none := by decide

/-- `5♠` is in the spade foundation at both witness endpoints. -/
private theorem s2c_foundY : y5S ∈ s2c.found y5S.suit := by decide
private theorem s1c_foundY : y5S ∈ s1c.found y5S.suit := by decide

/-- `6♥` is a pile top at both witness endpoints. -/
private theorem s2c_pTop : ∃ a, s2c.pileOfTop h6 = some a := ⟨Anchor.p0, by decide⟩
private theorem s1c_pTop : ∃ a, s1c.pileOfTop h6 = some a := ⟨Anchor.p0, by decide⟩

/-- `5♠` fits on `6♥`. -/
private theorem canSit_y5S_h6 : canSitOn y5S h6 = true := by decide

/-- The attached source `pulledAt s2c 5♠ (inr 6♥)` is well-formed: it is
exactly the pull of `5♠` from the top of the spade foundation onto `6♥`. -/
private theorem pulledAt_s2c_wf :
    (TwinRaiseCommute.pulledAt s2c y5S (Sum.inr h6)).WF := by
  have htop : s2c.foundTop y5S.suit = some y5S := by decide
  have hcp : s2c.canPlace y5S (Sum.inr h6) = true := by
    rw [canPlace_inr_located (k := Anchor.p0) (by decide)]
    exact canSit_y5S_h6
  have hstep : State.step s2c (Move.foundToTab y5S (Sum.inr h6)) =
      some (TwinRaiseCommute.pulledAt s2c y5S (Sum.inr h6)) := by
    simpa [TwinRaiseCommute.pulledAt] using
      step_foundToTab_splice (st := s2c) (c := y5S) (b := Sum.inr h6) htop hcp
  exact step_wf s2c_wf hstep

/-- The attached target has **two** copies of `5♠`: one still in the
spade foundation (the chop removed `6♠`, not `5♠`) and one on `6♥`. -/
private theorem pulledAt_s1c_cardCount :
    (TwinRaiseCommute.pulledAt s1c y5S (Sum.inr h6)).cardCount y5S = 2 := by
  decide

/-- **The literal `PullLift` is false.**  The witness uses the same
states and play as the attached-source argument of the detour, except
that the target pull has not happened yet: `5♠` is below `6♠` in the
spade foundation at `s1c`.  `pulledAt` then chops `6♠` and leaves `5♠`
in the foundation while also placing it on `6♥`.  A legal play preserves
the card multiset, so the two attached states cannot be joined; in
particular `PairFreeOrbit` would transport well-formedness from the
attached source to the non-well-formed attached target. -/
theorem pullLift_false : ¬ TwinForcedCancel.PullLift x9C y5S h6 := by
  intro h
  have horbit := h s1c_wf s2c_wf s1c_seatY_none s2c_seatY_none
    s1c_foundY s2c_foundY s1c_pTop s2c_pTop canSit_y5S_h6
    s2c_play s2c_play_pairFree
  obtain ⟨play, hplay, -⟩ := horbit
  have hrun : (TwinRaiseCommute.pulledAt s2c y5S (Sum.inr h6)).run play =
      some (TwinRaiseCommute.pulledAt s1c y5S (Sum.inr h6)) :=
    Walk_run _ hplay
  have hwfTarget : (TwinRaiseCommute.pulledAt s1c y5S (Sum.inr h6)).WF :=
    run_wf pulledAt_s2c_wf hrun
  have hcount := hwfTarget.cardCount_eq (Card.mem_universe y5S)
  rw [pulledAt_s1c_cardCount] at hcount
  omega

/-! ## §1. The corrected lift -/

/-- **`PullLiftTop x y p`** — the attachment lift with the missing
hypothesis: `y` is the top of its foundation row at **both** endpoints,
so `pulledAt` really removes `y` and only `y`.  This is exactly what the
detour application supplies: the raise of `y` makes `y` the foundation
top, and the final pull can fire only when `y` is the foundation top. -/
def PullLiftTop (x y p : Card) : Prop :=
  ∀ {s1 s2 : State} {ρ : List Move},
    s1.WF → s2.WF →
    seatOf s1 y = none → seatOf s2 y = none →
    s1.foundTop y.suit = some y → s2.foundTop y.suit = some y →
    (∃ a, s1.pileOfTop p = some a) →
    (∃ b, s2.pileOfTop p = some b) →
    canSitOn y p = true →
    ShufflePlayW s2 ρ s1 →
    (∀ m ∈ ρ, NotFoundPair x m) →
    PairFreeOrbit x (TwinRaiseCommute.pulledAt s2 y (Sum.inr p))
      (TwinRaiseCommute.pulledAt s1 y (Sum.inr p))

/-- The corrected lift implies the literal one whenever the two extra
foundation-top hypotheses hold. -/
theorem pullLift_of_pullLiftTop {x y p : Card} (h : PullLiftTop x y p)
    {s1 s2 : State} {ρ : List Move}
    (hwf1 : s1.WF) (hwf2 : s2.WF)
    (hse1 : seatOf s1 y = none) (hse2 : seatOf s2 y = none)
    (hft1 : s1.foundTop y.suit = some y)
    (hft2 : s2.foundTop y.suit = some y)
    (hp1 : ∃ a, s1.pileOfTop p = some a)
    (hp2 : ∃ b, s2.pileOfTop p = some b)
    (hfit : canSitOn y p = true)
    (hplay : ShufflePlayW s2 ρ s1)
    (hno : ∀ m ∈ ρ, NotFoundPair x m) :
    PairFreeOrbit x (TwinRaiseCommute.pulledAt s2 y (Sum.inr p))
      (TwinRaiseCommute.pulledAt s1 y (Sum.inr p)) :=
  h hwf1 hwf2 hse1 hse2 hft1 hft2 hp1 hp2 hfit hplay hno

/-! ## §2. The attachment API -/

/-- The attached state: `y` on the pile topped by `p`, with `y` removed
from the top of its foundation row. -/
abbrev Att (s : State) (y p : Card) : State :=
  TwinRaiseCommute.pulledAt s y (Sum.inr p)

@[simp] theorem Att_found (s : State) (y p : Card) (σ : Suit) :
    (Att s y p).found σ =
      (if σ = y.suit then chop (s.found y.suit) else s.found σ) :=
  TwinRaiseCommute.pulledAt_found s y (Sum.inr p) σ

@[simp] theorem Att_stock (s : State) (y p : Card) :
    (Att s y p).stock = s.stock := by
  simp [Att, TwinRaiseCommute.pulledAt, putCard_stock, setFound_stock]

@[simp] theorem Att_waste (s : State) (y p : Card) :
    (Att s y p).waste = s.waste := by
  simp [Att, TwinRaiseCommute.pulledAt, putCard_waste, setFound_waste]

@[simp] theorem Att_drawStep (s : State) (y p : Card) :
    (Att s y p).drawStep = s.drawStep := by
  simp [Att, TwinRaiseCommute.pulledAt, putCard_drawStep, setFound_drawStep]

/-- The pile edit of the attachment: exactly the pile topped by `p`
receives `y` at its top. -/
theorem Att_piles (s : State) (y p : Card) {k : Anchor}
    (hk : s.pileOfTop p = some k) :
    (Att s y p).piles =
      (fun a' => if a' = k then
        { s.piles k with faceUp := (s.piles k).faceUp ++ [y] }
      else s.piles a') := by
  unfold Att TwinRaiseCommute.pulledAt
  have hk' : (s.setFound y.suit (chop (s.found y.suit))).pileOfTop p = some k := by
    unfold State.pileOfTop State.topOf
    rw [setFound_piles]
    exact hk
  rw [putCard_piles_inr _ _ _ _ hk']
  simp only [setFound_piles]

/-- The attachment leaves every pile except the one topped by `p`
unchanged. -/
theorem Att_piles_ne (s : State) (y p : Card) {k a' : Anchor}
    (hk : s.pileOfTop p = some k) (ha : a' ≠ k) :
    (Att s y p).piles a' = s.piles a' := by
  rw [Att_piles s y p hk]
  exact ite_eq_right ha

/-- At the pile topped by `p`, the attachment appends `y`. -/
theorem Att_piles_self (s : State) (y p : Card) {k : Anchor}
    (hk : s.pileOfTop p = some k) :
    (Att s y p).piles k =
      { s.piles k with faceUp := (s.piles k).faceUp ++ [y] } := by
  rw [Att_piles s y p hk]
  exact ite_eq_left rfl

/-- The attachment is the pull of `y` from the foundation top: it is a
legal step at every `WF` state where `y` is the foundation top, `p` is a
pile top, and `y` fits `p`. -/
theorem Att_wf {s : State} {y p : Card} (hwf : s.WF)
    (hft : s.foundTop y.suit = some y)
    (hp : ∃ k, s.pileOfTop p = some k) (hfit : canSitOn y p = true) :
    (Att s y p).WF := by
  obtain ⟨k, hk⟩ := hp
  have hcp : s.canPlace y (Sum.inr p) = true := by
    rw [canPlace_inr_located hk]
    exact hfit
  have hstep : State.step s (Move.foundToTab y (Sum.inr p)) = some (Att s y p) := by
    simpa [Att, TwinRaiseCommute.pulledAt] using
      step_foundToTab_splice (st := s) (c := y) (b := Sum.inr p) hft hcp
  exact step_wf hwf hstep

/-- The attached state stays `WF` along an away letter; used to carry the
induction. -/
theorem Att_pileOfTop_of_ne {s : State} {y p c : Card} {kp kc : Anchor}
    (hwf : s.WF) (hft : s.foundTop y.suit = some y)
    (hp : s.pileOfTop p = some kp) (hfit : canSitOn y p = true)
    (hc : s.pileOfTop c = some kc) (hcp : c ≠ p) (hcy : c ≠ y) :
    (Att s y p).pileOfTop c = some kc := by
  have hAwf : (Att s y p).WF :=
    Att_wf hwf hft ⟨kp, hp⟩ hfit
  rw [pileOfTop_eq_some_iff hAwf]
  have hkc_top : (s.piles kc).top = some c :=
    (pileOfTop_eq_some_iff hwf).mp hc
  have hkc_ne : kc ≠ kp := by
    intro hEq
    have hp_top : (s.piles kc).top = some p := by
      rw [hEq]
      exact (pileOfTop_eq_some_iff hwf).mp hp
    rw [hkc_top] at hp_top
    exact hcp (Option.some.inj hp_top)
  show ((Att s y p).piles kc).top = some c
  rw [Att_piles_ne s y p hp hkc_ne]
  exact hkc_top

/-- At the attached state, `y` tops the pile that `p` topped. -/
theorem Att_pileOfTop_y {s : State} {y p : Card} {k : Anchor}
    (hAwf : (Att s y p).WF) (hk : s.pileOfTop p = some k) :
    (Att s y p).pileOfTop y = some k := by
  have htop : ((Att s y p).piles k).top = some y := by
    rw [Att_piles_self s y p hk]
    show lastOf ((s.piles k).faceUp ++ [y]) = some y
    exact lastOf_snoc
  exact (pileOfTop_eq_some_iff hAwf).mpr htop

/-- A located pile top is a top. -/
theorem topOf_of_pileOfTop {st : State} {z : Card} {k : Anchor}
    (h : st.pileOfTop z = some k) : st.topOf k = some z := by
  unfold State.pileOfTop at h
  exact of_decide_eq_true (firstWhere_sound (p := fun a => decide (st.topOf a = some z)) h)

/-- With no pile topped by `p`, the attachment edits only the
foundation. -/
theorem Att_piles_of_none {s : State} {y p : Card}
    (h : s.pileOfTop p = none) : (Att s y p).piles = s.piles := by
  unfold Att TwinRaiseCommute.pulledAt
  have h' : (s.setFound y.suit (chop (s.found y.suit))).pileOfTop p = none := by
    unfold State.pileOfTop State.topOf
    rw [setFound_piles]
    exact h
  simp only [State.putCard, h']
  exact setFound_piles s y.suit (chop (s.found y.suit))

/-- The attachment does not change the top search of any card that is
neither `p` nor `y`. -/
theorem Att_pileOfTop_of_ne' {s : State} {y p z : Card} {kp : Anchor}
    (hkp : s.pileOfTop p = some kp) (hzp : z ≠ p) (hzy : z ≠ y) :
    (Att s y p).pileOfTop z = s.pileOfTop z := by
  have hsp : (s.piles kp).top = some p := by
    simpa [State.topOf] using topOf_of_pileOfTop hkp
  have hay : ((Att s y p).piles kp).top = some y := by
    rw [Att_piles_self s y p hkp]
    exact lastOf_snoc
  unfold State.pileOfTop State.topOf
  apply firstWhere_congr
  intro a
  by_cases ha : a = kp
  · subst ha
    rw [hay, hsp]
    simp [Ne.symm hzy, Ne.symm hzp]
  · rw [Att_piles_ne s y p hkp ha]

/-- `nextUp` is blind to the attachment when the suit is not `y.suit`. -/
theorem Att_nextUp {s : State} {y p c : Card} (hc : c.suit ≠ y.suit) :
    (Att s y p).nextUp c = s.nextUp c := by
  unfold State.nextUp State.foundHeight
  rw [Att_found, ite_eq_right hc]

/-- The attachment does not move the holding search of any card other
than `y`. -/
theorem Att_pileHolding_of_ne {s : State} {y p c : Card} (hcy : c ≠ y) :
    (Att s y p).pileHolding c = s.pileHolding c := by
  unfold State.pileHolding
  apply firstWhere_congr
  intro a
  cases hk : s.pileOfTop p with
  | none =>
      rw [Att_piles_of_none hk]
  | some kp =>
      by_cases ha : a = kp
      · subst a
        rw [Att_piles_self s y p hk]
        by_cases hmem : c ∈ (s.piles kp).faceUp
        · rw [decide_eq_true (List.mem_append.mpr (Or.inl hmem)),
            decide_eq_true hmem]
        · have hnot : c ∉ (s.piles kp).faceUp ++ [y] := by
            intro hcon
            rcases List.mem_append.mp hcon with h | h
            · exact hmem h
            · exact hcy (List.mem_singleton.mp h)
          rw [decide_eq_false hnot, decide_eq_false hmem]
      · rw [Att_piles_ne s y p hk ha]

/-- The attachment passes through a stock/waste update. -/
theorem Att_update_sw (s : State) (y p : Card) (st wa : List Card) :
    Att { s with stock := st, waste := wa } y p =
      { Att s y p with stock := st, waste := wa } := by
  have hfound : (Att { s with stock := st, waste := wa } y p).found =
      (Att s y p).found := by
    funext σ
    rw [Att_found, Att_found]
  have hpiles : (Att { s with stock := st, waste := wa } y p).piles =
      (Att s y p).piles := by
    cases hk : s.pileOfTop p with
    | none =>
        have hk' : ({ s with stock := st, waste := wa } : State).pileOfTop p = none := hk
        rw [Att_piles_of_none hk, Att_piles_of_none hk']
    | some k =>
        have hk' : ({ s with stock := st, waste := wa } : State).pileOfTop p = some k := hk
        rw [Att_piles s y p hk, Att_piles { s with stock := st, waste := wa } y p hk']
  have hstock : (Att { s with stock := st, waste := wa } y p).stock = st :=
    Att_stock ..
  have hwaste : (Att { s with stock := st, waste := wa } y p).waste = wa :=
    Att_waste ..
  have hds : (Att { s with stock := st, waste := wa } y p).drawStep = s.drawStep :=
    Att_drawStep ..
  apply State.ext
  · exact hfound
  · exact hpiles
  · simpa using hstock
  · simpa using hwaste
  · simpa using hds

/-- Anonymous-constructor form of `Att_update_sw`, matching the record
produced by `dealStock`. -/
theorem Att_update_sw_mk (s : State) (y p : Card) (st wa : List Card) :
    Att (⟨s.found, s.piles, st, wa, s.drawStep⟩ : State) y p =
      { found := (Att s y p).found, piles := (Att s y p).piles,
        stock := st, waste := wa, drawStep := (Att s y p).drawStep } := by
  have h : (⟨s.found, s.piles, st, wa, s.drawStep⟩ : State) =
      { s with stock := st, waste := wa } := rfl
  rw [h]
  simpa [Att_waste] using Att_update_sw s y p st wa

/-- Recycling commutes with the attachment. -/
theorem Att_recycle (s : State) (y p : Card) :
    Att s.recycle y p = (Att s y p).recycle := by
  cases hs : s.stock with
  | cons c cs => simp [State.recycle, hs]
  | nil =>
      cases hw : s.waste with
      | nil => simp [State.recycle, hs, hw]
      | cons w ws =>
          rw [show s.recycle = { s with stock := (w :: ws).reverse, waste := [] } by
            simp [State.recycle, hs, hw]]
          rw [show (Att s y p).recycle =
              { Att s y p with stock := ((w :: ws).reverse), waste := [] } by
            simp [State.recycle, hs, hw, Att_stock, Att_waste]]
          exact Att_update_sw s y p _ _

/-- One deal step commutes with the attachment. -/
theorem Att_dealStock (s : State) (y p : Card) :
    (Att s y p).dealStock = (s.dealStock).map (fun t => Att t y p) := by
  cases hs : s.stock with
  | nil => simp [State.dealStock, hs]
  | cons c cs =>
      have hstock : (Att s y p).stock = c :: cs := by rw [Att_stock, hs]
      have hds : (Att s y p).drawStep = s.drawStep := Att_drawStep s y p
      simp only [State.dealStock, hs, hstock, hds, Option.map_some]
      apply congrArg some
      simpa [Att_waste, Att_drawStep] using (Att_update_sw_mk s y p
        ((dealUpTo s.drawStep (c :: cs)).snd)
        ((dealUpTo s.drawStep (c :: cs)).fst.reverse ++ (Att s y p).waste)).symm

/-- A draw commutes with the attachment. -/
theorem Att_stepDraw (s : State) (y p : Card) :
    (Att s y p).stepDraw = (s.stepDraw).map (fun t => Att t y p) := by
  unfold State.stepDraw
  rw [← Att_recycle]
  exact Att_dealStock (s.recycle) y p

/-- **Attachment commutation for a draw.**  A draw touches neither the
pile of `p` nor the foundation row of `y`, so it commutes with the
attachment. -/
theorem pulledAt_step_comm
    {s t : State} {y p : Card} {kp kt : Anchor}
    (hstep : State.step s Move.draw = some t)
    (hkp : s.pileOfTop p = some kp) (hkt : t.pileOfTop p = some kt)
    (hseatY : seatOf s y = none) (hseatY' : seatOf t y = none)
    (hftY : s.foundTop y.suit = some y) (hftY' : t.foundTop y.suit = some y) :
    State.step (Att s y p) Move.draw = some (Att t y p) := by
  have hsd : s.stepDraw = some t := hstep
  rw [show State.step (Att s y p) Move.draw = (Att s y p).stepDraw from rfl,
    Att_stepDraw, hsd]
  rfl

/-! ### §2.2. Foundation and pile edits -/

/-- A foundation edit in a suit other than `y.suit` commutes past the
attachment (orientation: attach after editing). -/
theorem Att_setFound {s : State} {y p : Card} {σ : Suit} (l : List Card)
    (hσ : σ ≠ y.suit) :
    Att (s.setFound σ l) y p = (Att s y p).setFound σ l := by
  apply State.ext
  · funext τ
    by_cases hτσ : τ = σ
    · subst hτσ
      rw [Att_found, ite_eq_right hσ, setFound_found_self, setFound_found_self]
    · by_cases hτy : τ = y.suit
      · subst hτy
        rw [Att_found, ite_eq_left rfl, setFound_found_ne (Ne.symm hσ),
          setFound_found_ne (Ne.symm hσ), Att_found, ite_eq_left rfl]
      · rw [Att_found, ite_eq_right hτy, setFound_found_ne hτσ,
          setFound_found_ne hτσ, Att_found, ite_eq_right hτy]
  · funext a'
    cases hk : s.pileOfTop p with
    | none =>
        have hk' : (s.setFound σ l).pileOfTop p = none := by
          have hcongr : firstWhere
              (fun a => decide (((s.setFound σ l).piles a).top = some p)) Anchor.all =
              firstWhere (fun a => decide ((s.piles a).top = some p)) Anchor.all := by
            apply firstWhere_congr
            intro a
            simp only [setFound_piles]
            rfl
          have hs_eq : firstWhere (fun a => decide ((s.piles a).top = some p)) Anchor.all = none := by
            change s.pileOfTop p = none
            exact hk
          change firstWhere (fun a => decide (((s.setFound σ l).piles a).top = some p)) Anchor.all = none
          exact hcongr.trans hs_eq
        rw [setFound_piles, Att_piles_of_none hk, Att_piles_of_none hk',
          setFound_piles]
    | some kp =>
        have hk' : (s.setFound σ l).pileOfTop p = some kp := by
          have hcongr : firstWhere
              (fun a => decide (((s.setFound σ l).piles a).top = some p)) Anchor.all =
              firstWhere (fun a => decide ((s.piles a).top = some p)) Anchor.all := by
            apply firstWhere_congr
            intro a
            simp only [setFound_piles]
            rfl
          have hs_eq : firstWhere (fun a => decide ((s.piles a).top = some p)) Anchor.all = some kp := by
            change s.pileOfTop p = some kp
            exact hk
          change firstWhere (fun a => decide (((s.setFound σ l).piles a).top = some p)) Anchor.all = some kp
          exact hcongr.trans hs_eq
        rw [setFound_piles, Att_piles s y p hk, Att_piles (s.setFound σ l) y p hk']
        simp only [setFound_piles]
  · simp [Att_stock, setFound_stock]
  · simp [Att_waste, setFound_waste]
  · simp [Att_drawStep, setFound_drawStep]

/-- A pile overwrite at an anchor other than `p`'s commutes past the
attachment (orientation: attach after editing). -/
theorem Att_setPile {s : State} {y p : Card} {kp k : Anchor}
    (hkp : s.pileOfTop p = some kp) (hk : k ≠ kp)
    (hsk : (s.piles k).top ≠ some p) (q : Pile) (hq : q.top ≠ some p) :
    Att (s.setPile k q) y p = (Att s y p).setPile k q := by
  have hk' : (s.setPile k q).pileOfTop p = some kp := by
    have hcongr : firstWhere
        (fun a => decide ((s.setPile k q).topOf a = some p)) Anchor.all =
        firstWhere (fun a => decide (s.topOf a = some p)) Anchor.all := by
      apply firstWhere_congr
      intro a
      by_cases ha : a = k
      · subst a
        simp [State.topOf, setPile_piles_self, hq, hsk]
      · rw [setPile_topOf_ne (st := s) (k := a) (b := k) (Q := q) ha]
    have hs_eq : firstWhere (fun a => decide (s.topOf a = some p)) Anchor.all
        = some kp := hkp
    change (s.setPile k q).pileOfTop p = some kp
    exact hcongr.trans hs_eq
  apply State.ext
  · funext σ
    simp [Att_found, setPile_found]
  · funext a'
    rw [Att_piles (s.setPile k q) y p hk']
    by_cases ha : a' = k
    · subst a'
      dsimp only
      rw [ite_eq_right hk, setPile_piles_self, setPile_piles_self]
    · by_cases ha' : a' = kp
      · subst a'
        dsimp only
        rw [ite_eq_left rfl,
          setPile_piles_ne (st := s) (k := kp) (b := k) (Q := q) (Ne.symm hk),
          setPile_piles_ne (st := Att s y p) (k := kp) (b := k) (Q := q) (Ne.symm hk),
          Att_piles_self s y p hkp]
      · dsimp only
        rw [ite_eq_right ha',
          setPile_piles_ne (st := s) (k := a') (b := k) (Q := q) ha,
          setPile_piles_ne (st := Att s y p) (k := a') (b := k) (Q := q) ha,
          Att_piles_ne s y p hkp ha']
  · simp [Att_stock, setPile_stock]
  · simp [Att_waste, setPile_waste]
  · simp [Att_drawStep, setPile_drawStep]

/-- A card topping the pile left after removing the face-up run up to
the top comes from the original pile. -/
theorem afterRunRemoved_chop_top_mem {p : Pile} {c : Card}
    (h : (Pile.afterRunRemoved p (chop p.faceUp)).top = some c) :
    c ∈ p.hidden ++ p.faceUp := by
  cases hpre : chop p.faceUp with
  | nil =>
      rw [hpre] at h
      unfold Pile.afterRunRemoved at h
      cases hhid : p.hidden with
      | nil =>
          rw [hhid] at h
          simp [Pile.revealTop, Pile.top] at h
          cases h
      | cons y t =>
          rw [hhid] at h
          have hmem_face : c ∈ (Pile.revealTop { hidden := y :: t, faceUp := [] }).faceUp :=
            lastOf_mem (by simpa [Pile.top] using h)
          have hcy : c = y := by
            simpa [Pile.revealTop] using hmem_face
          subst hcy
          simp [hhid]
  | cons w ws =>
      rw [hpre] at h
      unfold Pile.afterRunRemoved at h
      have hmem : c ∈ w :: ws :=
        lastOf_mem (by simpa [Pile.top] using h)
      have hmem' : c ∈ chop p.faceUp := by
        rw [hpre]
        exact hmem
      exact List.mem_append.mpr (Or.inr (chop_mem hmem'))

/-! ### §2.1. The away letters -/

/-- A letter is **away** from the attachment `(y, p)` when it neither
moves the mover `y`, nor touches the foundation row of `y`, nor raises
`p`, nor targets `p` (or `y`).  These are exactly the letters whose step
squares with `pulledAt`; the remaining letters are the obstruction rows
of §4. -/
def Away (y p : Card) : Move → Prop
  | .draw => True
  | .wasteToFound _ => False
  | .wasteToTab _ _ => False
  | .tabToFound c => c ≠ p ∧ c ≠ y ∧ c ≠ y.twin ∧ c.suit ≠ y.suit
  | .foundToTab c b =>
      c ≠ y ∧ c ≠ y.twin ∧ c.suit ≠ y.suit ∧
        b ≠ Sum.inr p ∧ b ≠ Sum.inr y
  | .tabToTab c b => False

/-- The away letters for which the literal `State.step` square is
proved in this card: draws and raises.  (`Away` also permits pulls, but
the pull square is still open.) -/
def AwayBasic (y p : Card) : Move → Prop
  | .draw => True
  | .tabToFound c => c ≠ p ∧ c ≠ y ∧ c ≠ y.twin ∧ c.suit ≠ y.suit
  | _ => False

theorem AwayBasic.toAway {y p : Card} {m : Move} (hm : AwayBasic y p m) :
    Away y p m := by
  cases m with
  | draw => trivial
  | wasteToFound c => cases hm
  | wasteToTab c b => cases hm
  | tabToFound c => exact hm
  | foundToTab c b => cases hm
  | tabToTab c b => cases hm

/-- An away letter is pair-free for the attached card `y`. -/
theorem Away.notFoundPair_y {y p : Card} {m : Move} (hm : Away y p m) :
    NotFoundPair y m := by
  cases m with
  | draw => exact ⟨by simp, by simp, fun b => by simp, fun b => by simp⟩
  | wasteToFound c => cases hm
  | wasteToTab c b => cases hm
  | tabToFound c =>
      refine ⟨?_, ?_, fun b => by simp, fun b => by simp⟩
      · intro h
        injection h with h1
        exact hm.2.1 h1
      · intro h
        injection h with h1
        exact hm.2.2.1 h1
  | foundToTab c b =>
      exact ⟨by simp, by simp, fun b' => by
        intro h
        injection h with h1 h2
        exact hm.1 h1, fun b' => by
        intro h
        injection h with h1 h2
        exact hm.2.1 h1⟩
  | tabToTab c b => cases hm

/-- The last card of the `fromCard` run is the last card of the whole
run. -/
theorem lastOf_fromCard {c : Card} :
    ∀ {l : List Card}, c ∈ l → lastOf (fromCard c l) = lastOf l := by
  intro l
  induction l with
  | nil => intro h; cases h
  | cons x t ih =>
      intro h
      rw [fromCard]
      by_cases hxc : x = c
      · rw [ite_eq_left hxc]
      · rw [ite_eq_right hxc]
        have hct : c ∈ t := by
          rcases List.mem_cons.mp h with h' | h'
          · exact absurd h'.symm hxc
          · exact h'
        cases t with
        | nil => cases hct
        | cons z t' => exact ih hct

/-- The induction context of the attachment: `WF`, `y` unseated and the
foundation top, `p` a pile top, and the static fit. -/
def Ctx (s : State) (y p : Card) : Prop :=
  s.WF ∧ seatOf s y = none ∧ s.foundTop y.suit = some y ∧
    (∃ k, s.pileOfTop p = some k) ∧ canSitOn y p = true

theorem Ctx.wf {s : State} {y p : Card} (h : Ctx s y p) : s.WF := h.1
theorem Ctx.unseated {s : State} {y p : Card} (h : Ctx s y p) :
    seatOf s y = none := h.2.1
theorem Ctx.topY {s : State} {y p : Card} (h : Ctx s y p) :
    s.foundTop y.suit = some y := h.2.2.1
theorem Ctx.topP {s : State} {y p : Card} (h : Ctx s y p) :
    ∃ k, s.pileOfTop p = some k := h.2.2.2.1
theorem Ctx.fit {s : State} {y p : Card} (h : Ctx s y p) :
    canSitOn y p = true := h.2.2.2.2

/-- The heart of the away analysis: an away letter keeps the context. -/
theorem Ctx.step_away {s s' : State} {y p : Card} {m : Move}
    (h : Ctx s y p) (hrev : reversibleAtW s m)
    (hstep : State.step s m = some s') (hm : Away y p m) :
    Ctx s' y p := by
  obtain ⟨hwf, hseat, htopY, ⟨kp, hkp⟩, hfit⟩ := h
  have hwf' : s'.WF := step_wf hwf hstep
  have hseat' : seatOf s' y = none :=
    pairFree_step_seat_none hwf hstep hrev (Away.notFoundPair_y hm) (Or.inl rfl) hseat
  -- the foundation row of `y` is untouched by an away letter
  have hfoundY : s'.found y.suit = s.found y.suit := by
    cases m with
    | draw =>
        have hsd : s.stepDraw = some s' := hstep
        exact (draw_footprint hsd).2.1 ▸ rfl
    | wasteToFound c => cases hm
    | wasteToTab c b => cases hm
    | tabToFound c =>
        obtain ⟨-, kc, hkc, hs'⟩ := step_tabToFound_inv hstep
        rw [hs']
        exact setFound_found_ne (Ne.symm hm.2.2.2)
    | foundToTab c b =>
        obtain ⟨-, -, -, hcp0, hs'⟩ := step_foundToTab_inv hstep
        rw [hs', putCard_found]
        exact setFound_found_ne (Ne.symm hm.2.2.1)
    | tabToTab c b => cases hm
  have htopY' : s'.foundTop y.suit = some y := by
    unfold State.foundTop
    rw [hfoundY]
    exact htopY
  -- locate the pile carrying `p` at the successor
  have htopP' : ∃ k', s'.pileOfTop p = some k' := by
    cases m with
    | draw =>
        have hsd : s.stepDraw = some s' := hstep
        have hpiles : s'.piles = s.piles := (draw_footprint hsd).2.2.1
        exact ⟨kp, by
          unfold State.pileOfTop State.topOf
          rw [hpiles]
          exact hkp⟩
    | wasteToFound c => cases hm
    | wasteToTab c b => cases hm
    | tabToFound c =>
        obtain ⟨-, kc, hkc, hs'⟩ := step_tabToFound_inv hstep
        have hckp : kc ≠ kp := by
          intro hEq
          have hkc_top : (s.piles kc).top = some c :=
            (pileOfTop_eq_some_iff hwf).mp hkc
          have hkp_top : (s.piles kp).top = some p :=
            (pileOfTop_eq_some_iff hwf).mp hkp
          rw [hEq] at hkc_top
          exact hm.1 (Option.some.inj (hkc_top.symm.trans hkp_top))
        refine ⟨kp, ?_⟩
        rw [pileOfTop_eq_some_iff hwf']
        show (s'.piles kp).top = some p
        rw [hs']
        show (if kp = kc then _ else s.piles kp).top = some p
        rw [ite_eq_right (Ne.symm hckp)]
        exact (pileOfTop_eq_some_iff hwf).mp hkp
    | foundToTab c b =>
        obtain ⟨-, -, -, hcp, hs'⟩ := step_foundToTab_inv hstep
        -- `p`'s pile is untouched by the pull's single placement
        have hpiles : s'.piles kp = s.piles kp := by
          rw [hs']
          cases b with
          | inl a =>
              have hempty : (s.piles a).isEmpty = true := (canPlace_inl hcp).1
              have hakp : a ≠ kp := by
                intro hEq
                have hnonempty : (s.piles kp).isEmpty = false :=
                  Pile.isEmpty_eq_false_of_mem
                    (lastOf_mem ((pileOfTop_eq_some_iff hwf).mp hkp))
                rw [hEq] at hempty
                rw [hnonempty] at hempty
                exact absurd hempty (by simp)
              rw [putCard_piles_inl]
              simp only []
              rw [ite_eq_right (Ne.symm hakp), setFound_piles]
          | inr z =>
              have hzp : z ≠ p := by
                intro hEq
                exact hm.2.2.2.1 (by rw [hEq])
              cases hloc : (s.setFound c.suit (chop (s.found c.suit))).pileOfTop z with
              | none =>
                  have hset : (s.setFound c.suit (chop (s.found c.suit))).putCard c (Sum.inr z)
                      = s.setFound c.suit (chop (s.found c.suit)) := by
                    simp only [State.putCard, hloc]
                  rw [hset, setFound_piles]
              | some kz =>
                  have htopz : ((s.setFound c.suit (chop (s.found c.suit))).piles kz).top
                      = some z := by
                    unfold State.pileOfTop State.topOf at hloc
                    exact of_decide_eq_true
                      (firstWhere_sound
                        (p := fun a => decide
                          (((s.setFound c.suit (chop (s.found c.suit))).topOf a) = some z))
                        hloc)
                  have hkzkp : kz ≠ kp := by
                    intro hEq
                    rw [hEq, setFound_piles] at htopz
                    have htopp : (s.piles kp).top = some p :=
                      (pileOfTop_eq_some_iff hwf).mp hkp
                    rw [htopp] at htopz
                    exact hzp (Option.some.inj htopz).symm
                  rw [putCard_piles_inr _ _ _ _ hloc]
                  simp only []
                  rw [ite_eq_right (Ne.symm hkzkp), setFound_piles]
        refine ⟨kp, ?_⟩
        rw [pileOfTop_eq_some_iff hwf']
        show (s'.piles kp).top = some p
        rw [hpiles]
        exact (pileOfTop_eq_some_iff hwf).mp hkp
    | tabToTab c b => cases hm
  exact ⟨hwf', hseat', htopY', htopP', hfit⟩


/-! ### §2.25. Reversibility transfer -/

/-- A draw or raise that is reversible at `s` stays reversible at the
attached state. -/
theorem Att_reversible_awayBasic {s : State} {y p : Card} {m : Move}
    (h : Ctx s y p) (hm : AwayBasic y p m) (hrev : reversibleAtW s m) :
    reversibleAtW (Att s y p) m := by
  have hAwf : (Att s y p).WF := Att_wf h.wf h.topY h.topP h.fit
  have hsrev : reversibleOf s m = true :=
    (reversibleOf_iff_reversibleAtW h.wf m).mpr hrev
  apply (reversibleOf_iff_reversibleAtW hAwf m).mp
  cases m with
  | draw =>
      simpa [reversibleOf, drawR, Att_stock, Att_waste, Att_drawStep] using hsrev
  | wasteToFound c => cases hm
  | wasteToTab c b => cases hm
  | tabToFound c =>
      obtain ⟨hcp, hcy, hcyT, hcs⟩ := hm
      obtain ⟨kp, hkp⟩ := h.topP
      simp only [reversibleOf] at hsrev ⊢
      cases hnext : s.nextUp c with
      | false =>
          have hR : tabToFoundR s c = false := by
            simp [tabToFoundR, hnext]
          rw [hR] at hsrev
          cases hsrev
      | true =>
          cases hloc : s.pileOfTop c with
          | none =>
              have hR : tabToFoundR s c = false := by
                simp [tabToFoundR, hnext, hloc]
              rw [hR] at hsrev
              cases hsrev
          | some kc =>
              have hckp : kc ≠ kp := by
                intro hEq
                have hkc_top : (s.piles kc).top = some c :=
                  (pileOfTop_eq_some_iff h.wf).mp hloc
                have hkp_top : (s.piles kp).top = some p :=
                  (pileOfTop_eq_some_iff h.wf).mp hkp
                rw [hEq] at hkc_top
                exact hcp (Option.some.inj (hkc_top.symm.trans hkp_top))
              have hlocA : (Att s y p).pileOfTop c = some kc :=
                Att_pileOfTop_of_ne h.wf h.topY hkp h.fit hloc hcp hcy
              have hpile : (Att s y p).piles kc = s.piles kc :=
                Att_piles_ne s y p hkp hckp
              have hnextA : (Att s y p).nextUp c = true := by
                rw [Att_nextUp hcs]
                exact hnext
              have hR : tabToFoundR (Att s y p) c = tabToFoundR s c := by
                simp [tabToFoundR, hnext, hloc, hlocA, hnextA, hpile]
              rw [hR]
              exact hsrev
  | foundToTab c b => cases hm
  | tabToTab c b => cases hm

/-! ### §2.3. The raise square -/

/-- **The raise attachment square.**  An away raise commutes with the
attachment. -/
theorem raiseSquareResidual (y p : Card) :
    ∀ {s s' : State} {c : Card}, Ctx s y p → Ctx s' y p →
      Away y p (Move.tabToFound c) →
      State.step s (Move.tabToFound c) = some s' →
      State.step (Att s y p) (Move.tabToFound c) = some (Att s' y p) := by
  intro s t c hCtx hCtx' hAway hstep
  obtain ⟨hwf, hseatY, hftY, ⟨kp, hkp⟩, hfit⟩ := hCtx
  obtain ⟨hcp, hcy, hcyT, hcs⟩ := hAway
  obtain ⟨hnext, kc, hkc, hs⟩ := step_tabToFound_inv hstep
  have hckp : kc ≠ kp := by
    intro hEq
    have hkc_top : (s.piles kc).top = some c :=
      (pileOfTop_eq_some_iff hwf).mp hkc
    have hkp_top : (s.piles kp).top = some p :=
      (pileOfTop_eq_some_iff hwf).mp hkp
    rw [hEq] at hkc_top
    exact hcp (Option.some.inj (hkc_top.symm.trans hkp_top))
  have hnextA : (Att s y p).nextUp c = true := by
    rw [Att_nextUp hcs]
    exact hnext
  have hkcA : (Att s y p).pileOfTop c = some kc :=
    Att_pileOfTop_of_ne hwf hftY hkp hfit hkc hcp hcy
  have hq : (Pile.afterRunRemoved (s.piles kc) (chop (s.piles kc).faceUp)).top
      ≠ some p := by
    intro htop
    have hmem := afterRunRemoved_chop_top_mem htop
    have hmem_kp : p ∈ (s.piles kp).faceUp :=
      lastOf_mem ((pileOfTop_eq_some_iff hwf).mp hkp)
    have huniq := mem_faceUp_only hwf hmem_kp
    rcases List.mem_append.mp hmem with h | h
    · exact (huniq.1 kc hckp).1 h
    · exact (huniq.1 kc hckp).2 h
  have hq' : ((Att s y p).piles kc).afterRunRemoved
        (chop ((Att s y p).piles kc).faceUp) =
      (s.piles kc).afterRunRemoved (chop (s.piles kc).faceUp) := by
    rw [Att_piles_ne s y p hkp hckp]
  rw [step_tabToFound_splice (k := kc) hnextA hkcA]
  apply congrArg some
  change ((Att s y p).setFound c.suit
      ((Att s y p).found c.suit ++ [c])).setPile kc
        (((Att s y p).piles kc).afterRunRemoved
          (chop ((Att s y p).piles kc).faceUp)) = Att t y p
  rw [hq']
  rw [show (Att s y p).found c.suit = s.found c.suit from by
    rw [Att_found, ite_eq_right hcs]]
  rw [← Att_setFound (s := s) (y := y) (p := p) (σ := c.suit)
    (s.found c.suit ++ [c]) hcs]
  rw [← Att_setPile (s := s.setFound c.suit (s.found c.suit ++ [c]))
    (y := y) (p := p) (kp := kp) (k := kc)
    (by
      change (s.setFound c.suit (s.found c.suit ++ [c])).pileOfTop p = some kp
      have hcongr : firstWhere
          (fun a => decide ((s.setFound c.suit (s.found c.suit ++ [c])).topOf a = some p))
          Anchor.all =
          firstWhere (fun a => decide (s.topOf a = some p)) Anchor.all := by
        apply firstWhere_congr
        intro a
        simp [State.topOf, setFound_piles]
        change decide ((s.piles a).top = some p) = decide ((s.piles a).top = some p)
        rfl
      exact hcongr.trans hkp)
    hckp
    (by
      intro htop
      have hmem_kp : p ∈ (s.piles kp).faceUp :=
        lastOf_mem ((pileOfTop_eq_some_iff hwf).mp hkp)
      have htop' : (s.piles kc).top = some p := by
        simpa [setFound_piles] using htop
      exact (tfc_faceUp_uniq_other hwf hmem_kp hckp) (lastOf_mem htop'))
    ((s.piles kc).afterRunRemoved (chop (s.piles kc).faceUp)) hq]
  rw [hs]
  change Att ((s.setFound c.suit (s.found c.suit ++ [c])).setPile kc
      ((s.piles kc).afterRunRemoved (chop (s.piles kc).faceUp))) y p =
    Att ((s.setFound c.suit (s.found c.suit ++ [c])).setPile kc
      ((s.piles kc).afterRunRemoved (chop (s.piles kc).faceUp))) y p
  rfl

/-! ### §2.4. The away-letter attachment functor -/

/-- **The attachment functor for away plays.**  One induction on the
play builds the lifted walk at the attached states; every letter is a
draw or raise, so `Ctx.step_away`, `pulledAt_step_comm`,
`raiseSquareResidual`, and `Att_reversible_awayBasic` close the step. -/
theorem pulledAt_functor_away
    {s t : State} {x y p : Card} {play : List Move}
    (hCtx : Ctx s y p)
    (hplay : ShufflePlayW s play t)
    (haway : ∀ m ∈ play, AwayBasic y p m)
    (hno : ∀ m ∈ play, NotFoundPair x m)
    (hCtx' : Ctx t y p) :
    PairFreeOrbit x (Att s y p) (Att t y p) := by
  revert hCtx hCtx' haway hno
  induction play generalizing s t with
  | nil =>
      intro hCtx haway hno hCtx'
      cases hplay
      exact pairFreeOrbit_refl x (Att s y p)
  | cons m rest ih =>
      intro hCtx haway hno hCtx'
      obtain ⟨u, hrev, hstep, hrest⟩ := TwinForcedCancel.walk_cons_inv hplay
      have hm : AwayBasic y p m := haway m (by simp)
      have hmAway : Away y p m := hm.toAway
      have hCtxu : Ctx u y p := Ctx.step_away hCtx hrev hstep hmAway
      have hstepL : State.step (Att s y p) m = some (Att u y p) := by
        cases m with
        | draw =>
            obtain ⟨kp, hkp⟩ := hCtx.topP
            obtain ⟨kt, hkt⟩ := hCtxu.topP
            exact pulledAt_step_comm (y := y) (p := p) hstep hkp hkt
              hCtx.unseated hCtxu.unseated hCtx.topY hCtxu.topY
        | wasteToFound c => cases hm
        | wasteToTab c b => cases hm
        | tabToFound c =>
            exact raiseSquareResidual y p hCtx hCtxu hmAway hstep
        | foundToTab c b => cases hm
        | tabToTab c b => cases hm
      have hrevL : reversibleAtW (Att s y p) m :=
        Att_reversible_awayBasic hCtx hm hrev
      have hsingle : PairFreeOrbit x (Att s y p) (Att u y p) :=
        pairFreeOrbit_of_play
          (Walk.cons hrevL hstepL (Walk.nil (Att u y p)))
          (by
            intro k hk
            rw [List.mem_singleton] at hk
            subst hk
            exact hno k (by simp))
      have htail : PairFreeOrbit x (Att u y p) (Att t y p) :=
        ih hrest hCtxu
          (fun n hn => haway n (by simp [hn]))
          (fun n hn => hno n (by simp [hn]))
          hCtx'
      exact PairFreeOrbit.trans hsingle htail

/-- The corrected lift for plays whose letters are all draws or raises
away from `p` (`AwayBasic`).  This is the away case of `PullLiftTop`. -/
theorem pullLiftTop_away
    {x y p : Card} {s1 s2 : State} {ρ : List Move}
    (hwf1 : s1.WF) (hwf2 : s2.WF)
    (hse1 : seatOf s1 y = none) (hse2 : seatOf s2 y = none)
    (hft1 : s1.foundTop y.suit = some y)
    (hft2 : s2.foundTop y.suit = some y)
    (hp1 : ∃ a, s1.pileOfTop p = some a)
    (hp2 : ∃ b, s2.pileOfTop p = some b)
    (hfit : canSitOn y p = true)
    (hplay : ShufflePlayW s2 ρ s1)
    (hno : ∀ m ∈ ρ, NotFoundPair x m)
    (haway : ∀ m ∈ ρ, AwayBasic y p m) :
    PairFreeOrbit x (Att s2 y p) (Att s1 y p) := by
  have hCtx2 : Ctx s2 y p := ⟨hwf2, hse2, hft2, hp2, hfit⟩
  have hCtx1 : Ctx s1 y p := ⟨hwf1, hse1, hft1, hp1, hfit⟩
  exact pulledAt_functor_away hCtx2 hplay haway hno hCtx1

/-! ## §3. The obstruction rows at the attached state -/

/-- Once `y` sits on `p`'s pile, `p` is no longer a pile top (at a
well-formed origin). -/
theorem Att_pileOfTop_p_none {s : State} {y p : Card}
    (hwf : s.WF) (hft : s.foundTop y.suit = some y)
    (hp : ∃ k, s.pileOfTop p = some k) (hfit : canSitOn y p = true) :
    (Att s y p).pileOfTop p = none := by
  obtain ⟨kp, hkp⟩ := hp
  have hAwf : (Att s y p).WF := Att_wf hwf hft ⟨kp, hkp⟩ hfit
  cases hloc : (Att s y p).pileOfTop p with
  | none => rfl
  | some k' =>
      exfalso
      have htop' : ((Att s y p).piles k').top = some p :=
        (pileOfTop_eq_some_iff hAwf).mp hloc
      have htopkp : ((Att s y p).piles kp).top = some y := by
        rw [Att_piles_self s y p hkp]
        exact lastOf_snoc
      have hk'ne : k' ≠ kp := by
        intro hEq
        rw [hEq, htopkp] at htop'
        have hpy_ne : p ≠ y := by
          intro hpy
          have hlt : y.rank.toIdx + 1 = p.rank.toIdx :=
            ((canSitOn_eq y p).mp hfit).1
          rw [hpy] at hlt
          omega
        exact hpy_ne (Option.some.inj htop').symm
      have htop_s : (s.piles k').top = some p := by
        rw [← Att_piles_ne s y p hkp hk'ne]
        exact htop'
      have hmem_kp : p ∈ (s.piles kp).faceUp :=
        lastOf_mem ((pileOfTop_eq_some_iff hwf).mp hkp)
      have hmem_k' : p ∈ (s.piles k').faceUp := lastOf_mem htop_s
      exact (tfc_faceUp_uniq_other hwf hmem_kp hk'ne) hmem_k'

/-- The `p`-raise cannot fire at the attached state. -/
theorem Att_step_tabToFound_p_none {s : State} {y p : Card}
    (hwf : s.WF) (hft : s.foundTop y.suit = some y)
    (hp : ∃ k, s.pileOfTop p = some k) (hfit : canSitOn y p = true) :
    State.step (Att s y p) (Move.tabToFound p) = none := by
  have hn := Att_pileOfTop_p_none hwf hft hp hfit
  cases h : (Att s y p).nextUp p <;> simp [State.step, hn, h]

/-- No card can be placed on `p` at the attached state. -/
theorem Att_canPlace_target_p_false {s : State} {y p c : Card}
    (hwf : s.WF) (hft : s.foundTop y.suit = some y)
    (hp : ∃ k, s.pileOfTop p = some k) (hfit : canSitOn y p = true) :
    (Att s y p).canPlace c (Sum.inr p) = false := by
  have hn := Att_pileOfTop_p_none hwf hft hp hfit
  simp [State.canPlace, hn]

/-- A slide targeting `p` cannot fire at the attached state. -/
theorem Att_step_tabToTab_target_p_none {s : State} {y p c : Card} {b : Base}
    (hwf : s.WF) (hft : s.foundTop y.suit = some y)
    (hp : ∃ k, s.pileOfTop p = some k) (hfit : canSitOn y p = true)
    (hb : b = Sum.inr p) :
    State.step (Att s y p) (Move.tabToTab c b) = none := by
  subst hb
  have hcp := Att_canPlace_target_p_false (s := s) (y := y) (p := p) (c := c)
    hwf hft hp hfit
  cases h : (Att s y p).pileHolding c <;> simp [State.step, h, hcp]

/-- A foundation pull targeting `p` cannot fire at the attached state. -/
theorem Att_step_foundToTab_target_p_none {s : State} {y p c : Card} {b : Base}
    (hwf : s.WF) (hft : s.foundTop y.suit = some y)
    (hp : ∃ k, s.pileOfTop p = some k) (hfit : canSitOn y p = true)
    (hb : b = Sum.inr p) :
    State.step (Att s y p) (Move.foundToTab c b) = none := by
  subst hb
  have hcp := Att_canPlace_target_p_false (s := s) (y := y) (p := p) (c := c)
    hwf hft hp hfit
  cases htop : (Att s y p).foundTop c.suit <;>
    simp [State.step, htop, hcp]

/-- A waste slide targeting `p` cannot fire at the attached state. -/
theorem Att_step_wasteToTab_target_p_none {s : State} {y p c : Card} {b : Base}
    (hwf : s.WF) (hft : s.foundTop y.suit = some y)
    (hp : ∃ k, s.pileOfTop p = some k) (hfit : canSitOn y p = true)
    (hb : b = Sum.inr p) :
    State.step (Att s y p) (Move.wasteToTab c b) = none := by
  subst hb
  have hcp := Att_canPlace_target_p_false (s := s) (y := y) (p := p) (c := c)
    hwf hft hp hfit
  simp [State.step, hcp]

/-! ### §3.1. The target-`p` cancellation row -/

/-- **Target-`p` excursion cancellation.**  If `p` is raised from a card
parent `r` and later pulled back to `r` or `r.twin`, the whole excursion
is a pair-free orbit back to its source.  This is the local segment used
by stage (2) of the attachment lift; it is the `p_excursion_cancels`
row of `TwinForcedCancel`, restated for the lift. -/
theorem p_excursion_cancels_local
    {x p r : Card} {s s1 t : State} {b : Base}
    (hwf : s.WF) (hseat : seatOf s p = some (Sum.inr r))
    (hraise : State.step s (Move.tabToFound p) = some s1)
    (hpull : State.step s1 (Move.foundToTab p b) = some t)
    (hb : b = Sum.inr r ∨ b = Sum.inr r.twin) :
    PairFreeOrbit x t s :=
  TwinForcedCancel.p_excursion_cancels hwf hseat hraise hpull hb

/-- The return case of the target-`p` excursion: pulling back to the
original parent is a state-level identity. -/
theorem p_excursion_return_eq_local
    {p r : Card} {s s1 t : State}
    (hwf : s.WF) (hseat : seatOf s p = some (Sum.inr r))
    (hraise : State.step s (Move.tabToFound p) = some s1)
    (hpull : State.step s1 (Move.foundToTab p (Sum.inr r)) = some t) :
    t = s :=
  TwinForcedCancel.p_excursion_return_eq hwf hseat hraise hpull

/-! ## §4. The exact residual -/

/-- The **raise square residual**: context preservation is proved in
`Ctx.step_away`, but the literal step equality at the attached states is
the remaining row. -/
def RaiseSquareResidual (y p : Card) : Prop :=
  ∀ {s s' : State} {c : Card}, Ctx s y p → Ctx s' y p →
    Away y p (Move.tabToFound c) →
    State.step s (Move.tabToFound c) = some s' →
    State.step (Att s y p) (Move.tabToFound c) = some (Att s' y p)

/-- The **pull square residual**: with the context carried at both ends,
a pair-free foundation pull away from `p` must lift to a step at the
attached states.  This is exactly the row not proved in this card. -/
def PullSquareResidual (y p : Card) : Prop :=
  ∀ {s s' : State} {c : Card} {b : Base},
    Ctx s y p → Ctx s' y p →
    Away y p (Move.foundToTab c b) →
    State.step s (Move.foundToTab c b) = some s' →
    State.step (Att s y p) (Move.foundToTab c b) = some (Att s' y p)

/-- The slide shape admitted by the attachment: the mover is not `y` and
the target is neither `p` nor `y`. -/
def AwaySlide (y p : Card) (c : Card) (b : Base) : Prop :=
  c ≠ y ∧ c ≠ y.twin ∧ b ≠ Sum.inr p ∧ b ≠ Sum.inr y

/-- The **slide square residual**: a slide away from `p` and `y` must lift
to the attached states.  This includes the `p`-carrying slides, whose run
picks `y` up at the attached state. -/
def SlideSquareResidual (y p : Card) : Prop :=
  ∀ {s s' : State} {c : Card} {b : Base},
    Ctx s y p → Ctx s' y p →
    AwaySlide y p c b →
    State.step s (Move.tabToTab c b) = some s' →
    State.step (Att s y p) (Move.tabToTab c b) = some (Att s' y p)

/-- The exact remaining obligation for the corrected attachment lift is
the conjunction of the draw, raise, pull, and slide step squares
(together with the corresponding reversibility transfer, which follows
from the same four rows by the oracle). -/
def AttSquareResidual (y p : Card) : Prop :=
  RaiseSquareResidual y p ∧ PullSquareResidual y p ∧ SlideSquareResidual y p

/-- **The exact general functor residual.**  This is the statement of
`pulledAt_functor` after the away-letter induction: every pair-free play,
including pulls, slides, waste moves, and `p`-targeting excursions. -/
def PullLiftFunctorResidual (x y p : Card) : Prop :=
  ∀ {s t : State} {play : List Move},
    Ctx s y p → ShufflePlayW s play t →
    (∀ m ∈ play, NotFoundPair x m) → Ctx t y p →
    PairFreeOrbit x (Att s y p) (Att t y p)

/-- The raise conjunct of `AttSquareResidual` is proved. -/
theorem raiseSquare_proved (y p : Card) : RaiseSquareResidual y p :=
  raiseSquareResidual y p

/-- **The identity detour from the corrected lift.**  This is the
repaired consumer of `PullLiftTop`: the two foundation-top hypotheses
are supplied by the outer raise (`s1` is right after `tabToFound y`) and
by the final pull (`s2` is right before `foundToTab y`).  The rest of
the argument is the same as
`TwinForcedCancel.singleDetour_identity_arbitraryMid_of_pullLift`. -/
theorem singleDetour_identity_arbitraryMid_of_pullLiftTop
    {u v : State} {x y : Card} {p : Card} {mid : List Move}
    (hlift : PullLiftTop x y p)
    (hwf : u.WF)
    (hy : y = x ∨ y = x.twin)
    (hseatY : seatOf u y = some (Sum.inr p))
    (hplay : ShufflePlayW u
      (Move.tabToFound y :: mid ++ [Move.foundToTab y (Sum.inr p)]) v)
    (hnoMid : ∀ m ∈ mid, NotFoundPair x m) :
    PairFreeOrbit x v u := by
  obtain ⟨s1, hrevR, hraise, hrest⟩ := TwinForcedCancel.walk_cons_inv hplay
  obtain ⟨s2, hmid, hpullwalk⟩ := TwinForcedCancel.walk_split hrest
  obtain ⟨v', hrevP, hpull, hnil⟩ := TwinForcedCancel.walk_cons_inv hpullwalk
  cases hnil
  have hwf1 : s1.WF := step_wf hwf hraise
  have hwf2 : s2.WF := run_wf hwf1 (Walk_run _ hmid)
  have hseatY1 : seatOf s1 y = none :=
    TwinSpliceComm.seatOf_tabToFound_mover_none hwf hraise
  have hseatY2 : seatOf s2 y = none :=
    pairFree_play_seat_none hwf1 hmid hnoMid hy hseatY1
  obtain ⟨a0, hhold0, -, hlast0⟩ := tfc_seatOf_of_inr hseatY
  have hfit : canSitOn y p = true := (tfc_seat_parent hwf hhold0 hlast0).1
  have hpTop1 : ∃ a, s1.pileOfTop p = some a :=
    TwinForcedCancel.raise_makes_parent_top hwf hseatY hraise
  have hpTop2 : ∃ a, s2.pileOfTop p = some a := by
    obtain ⟨c', htop, hc', hcp, hshape⟩ := step_foundToTab_inv hpull
    obtain ⟨k, hloc, hfitq⟩ := canPlace_inr hcp
    exact ⟨k, hloc⟩
  have hft1 : s1.foundTop y.suit = some y := by
    obtain ⟨-, aR, hpaR, hs1shape⟩ := step_tabToFound_inv hraise
    exact (tabToFound_found_trio (st := u) (s₁ := s1) (c := y) (a := aR)
      hs1shape).2.2
  have hft2 : s2.foundTop y.suit = some y := by
    obtain ⟨c', htop, hc'c, -, -⟩ := step_foundToTab_inv hpull
    rw [hc'c] at htop
    exact htop
  obtain ⟨ρ, hρ, hnoρ⟩ :=
    TwinDetourArbitraryMid.pairFreeReversal_unseated hwf1 hmid hnoMid
  have hL := hlift hwf1 hwf2 hseatY1 hseatY2 hft1 hft2
    hpTop1 hpTop2 hfit hρ hnoρ
  have hv : v = TwinRaiseCommute.pulledAt s2 y (Sum.inr p) := by
    obtain ⟨c', htop, hc', hcp, hshape⟩ := step_foundToTab_inv hpull
    simpa [TwinRaiseCommute.pulledAt] using hshape
  obtain ⟨aP, hs1_top⟩ := hpTop1
  have hcp1 : s1.canPlace y (Sum.inr p) = true :=
    tfa_canPlace_inr (st := s1) (c := y) (z := p) (k := aP) hs1_top hfit
  have hstep1 : State.step s1 (Move.foundToTab y (Sum.inr p)) =
      some (TwinRaiseCommute.pulledAt s1 y (Sum.inr p)) := by
    simpa [TwinRaiseCommute.pulledAt] using
      step_foundToTab_splice (st := s1) (c := y) (b := Sum.inr p)
        hft1 hcp1
  have hu' : TwinRaiseCommute.pulledAt s1 y (Sum.inr p) = u :=
    TwinCargoKernel.raise_pull_self_eq hwf hseatY hraise hstep1
  have hu : u = TwinRaiseCommute.pulledAt s1 y (Sum.inr p) := hu'.symm
  simpa [hv, hu] using hL

/-- The arbitrary-middle identity residual follows from the corrected
lift for **all** `y, p`. -/
theorem singleDetourIdentityArbitraryMid_of_pullLiftTop
    {x : Card} (h : ∀ y p : Card, PullLiftTop x y p) :
    TwinDetourArbitraryMid.SingleDetourIdentityArbitraryMid x := by
  intro u v y p mid hwf hxu hxtu hy hseat hplay hnoMid hvx hvt
  exact singleDetour_identity_arbitraryMid_of_pullLiftTop (h y p) hwf hy hseat
    hplay hnoMid

end TwinPullLift

/-! ## §5. Audit -/

#print axioms TwinPullLift.pullLift_false
#print axioms TwinPullLift.pullLift_of_pullLiftTop
#print axioms TwinPullLift.Att_found
#print axioms TwinPullLift.Att_piles
#print axioms TwinPullLift.Att_wf
#print axioms TwinPullLift.Att_pileOfTop_of_ne
#print axioms TwinPullLift.Ctx.step_away
#print axioms TwinPullLift.Att_pileOfTop_p_none
#print axioms TwinPullLift.Att_step_tabToFound_p_none
#print axioms TwinPullLift.Att_canPlace_target_p_false
#print axioms TwinPullLift.Att_step_tabToTab_target_p_none
#print axioms TwinPullLift.Att_step_foundToTab_target_p_none
#print axioms TwinPullLift.Att_step_wasteToTab_target_p_none


#print axioms TwinPullLift.singleDetour_identity_arbitraryMid_of_pullLiftTop

/-! ## §6. Report

### The literal target is false

`TwinForcedCancel.PullLift x y p` cannot be proved: its endpoint
hypothesis `y ∈ s.found y.suit` does not say that `y` is the *top* of
that foundation row, while `pulledAt` always chops the row's last card.
The compiled counterexample `pullLift_false` uses

* `x = 9♣`, `y = 5♠`, `p = 6♥`;
* `s2`: spades founded through `5♠`, `6♠` on top of `7♥` at `p1`,
  `6♥` alone at `p0`;
* `s1`: the same state after the reversible pair-free raise
  `tabToFound 6♠`, so the spade row is founded through `6♠`;
* the play `[tabToFound 6♠]`.

At `s2`, `pulledAt` chops `5♠` and puts it on `6♥`, producing a WF
state.  At `s1`, `pulledAt` chops `6♠` and leaves `5♠` in the
foundation while also putting it on `6♥`, producing a state with two
copies of `5♠` (hence not WF).  A witness shuffle preserves WF by
`run_wf`, so no `PairFreeOrbit` from the attached source to the
attached target exists.

### The corrected lift

`PullLiftTop x y p` adds `foundTop y.suit = some y` at both endpoints.
This is exactly the hypothesis available in the detour application:

* `s1` is right after `tabToFound y`, so
  `tabToFound_found_trio` gives `s1.foundTop y.suit = some y`;
* `s2` is right before `foundToTab y`, so `step_foundToTab_inv` gives
  `s2.foundTop y.suit = some y`.

The repaired consumer
`singleDetour_identity_arbitraryMid_of_pullLiftTop` proves that
`PullLiftTop` implies the mandatory identity row
`PairFreeOrbit x v u`, using the same reduction as
`TwinForcedCancel.singleDetour_identity_arbitraryMid_of_pullLift`.

### Proved unconditionally in this card

* `pullLift_false` — the literal `PullLift` is false.
* `pullLift_of_pullLiftTop` — the corrected lift supplies the literal
  one under the two foundation-top hypotheses.
* `singleDetour_identity_arbitraryMid_of_pullLiftTop` — the detour
  identity follows from the corrected lift.
* `Att_found`, `Att_piles`, `Att_stock`, `Att_waste`, `Att_drawStep`,
  `Att_piles_ne`, `Att_piles_self`, `Att_piles_of_none` — the
  attachment API.
* `Att_wf` — the attachment is WF at a WF origin when `y` is the
  foundation top, `p` is a pile top, and `y` fits `p`.
* `Att_pileOfTop_of_ne`, `Att_pileOfTop_of_ne'` — the attachment does
  not change the top search of any card other than `p` and `y`.
* `Att_pileOfTop_y` — at the attached state, `y` tops the pile that
  `p` topped.
* `topOf_of_pileOfTop`, `lastOf_fromCard`.
* `Ctx.step_away` — every away letter (draw, or a raise of a card other
  than `p, y, y.twin` in a suit other than `y.suit`) preserves the whole
  attachment context.
* `Att_pileOfTop_p_none` — `p` is no longer a pile top after the
  attachment.
* `Att_step_tabToFound_p_none`,
  `Att_step_tabToTab_target_p_none`,
  `Att_step_foundToTab_target_p_none`,
  `Att_step_wasteToTab_target_p_none` — the four obstruction rows: a
  letter that raises `p`, or targets `p`, cannot fire at the attached
  state.

### Exact remaining local obligations

The draw row is `pulledAt_step_comm` and the raise row is
`raiseSquareResidual` (packaged as `raiseSquare_proved`).  The pull row
is the remaining `PullSquareResidual y p`:

```
∀ {s s'} {c b},
  Ctx s y p → Ctx s' y p →
  Away y p (Move.foundToTab c b) →
  State.step s (Move.foundToTab c b) = some s' →
  State.step (Att s y p) (Move.foundToTab c b) = some (Att s' y p)
```

`SlideSquareResidual y p` is the remaining slide square:

```
∀ {s s'} {c b},
  Ctx s y p → Ctx s' y p →
  AwaySlide y p c b →
  State.step s (Move.tabToTab c b) = some s' →
  State.step (Att s y p) (Move.tabToTab c b) = some (Att s' y p)
```

Their conjunction with the proved raise conjunct is
`AttSquareResidual y p`.  The corrected global lift `PullLiftTop` is
therefore open exactly at the pull and slide step squares; the draw,
raise, point-seat, context-preservation, and obstruction rows are proved
here.

### Axioms

Every `#print axioms` line above reports only `[propext]` or
`[propext, Quot.sound]`.  There is no `sorryAx`, no `Classical.choice`,
and no new axiom.
-/



#print axioms TwinPullLift.p_excursion_cancels_local
#print axioms TwinPullLift.p_excursion_return_eq_local

/-! ## §7. Staged status

1. **Attachment squares.** The draw row and the raise row are proved:
   `pulledAt_step_comm` (draw, with supporting `Att_update_sw`,
   `Att_update_sw_mk`, `Att_recycle`, `Att_dealStock`, `Att_stepDraw`)
   and `raiseSquareResidual` (raise, via the edit-commutation lemmas
   `Att_setFound` and `Att_setPile`).  `raiseSquare_proved` is the
   packaged `RaiseSquareResidual`.  The pull and slide rows remain the
   exact residual local rows `PullSquareResidual`,
   `SlideSquareResidual`, and their conjunction with the proved raise
   conjunct is `AttSquareResidual`.  The API needed to state them
   (`Att_found`, `Att_piles`, `Att_piles_ne`, `Att_piles_self`,
   `Att_piles_of_none`, `Att_pileOfTop_of_ne`, `Att_pileOfTop_of_ne'`,
   `Att_pileOfTop_y`, `Att_pileHolding_of_ne`, `Att_nextUp`) is proved.

2. **Target-`p` cancellation.** Proved as
   `p_excursion_cancels_local` (the `p_excursion_cancels` row) and
   `p_excursion_return_eq_local` (the return identity), together with
   the four obstruction rows
   `Att_step_tabToFound_p_none`,
   `Att_step_tabToTab_target_p_none`,
   `Att_step_foundToTab_target_p_none`,
   `Att_step_wasteToTab_target_p_none` and
   `Att_pileOfTop_p_none`.

3. **`PullLift`.** The literal `TwinForcedCancel.PullLift x y p` is
   **false**: `pullLift_false` is a compiled counterexample.  The exact
   repair is `PullLiftTop` (add `foundTop y.suit = some y` at both
   ends), and `singleDetour_identity_arbitraryMid_of_pullLiftTop` shows
   that the repaired lift suffices for the detour application.  A proof
   of `PullLiftTop` itself is open at the pull and slide step squares in
   stage 1.

### The remaining interface

`AttSquareResidual → PullLiftTop` is not yet proved.  Beyond closing
`PullSquareResidual` and `SlideSquareResidual`, the induction needs

* context preservation for pull and slide letters (the squares as stated
  take `Ctx s'` as an input, so the induction must produce it from the
  placement commutation), and
* a waste row: `Away` currently excludes `wasteToFound` and
  `wasteToTab`, while a pair-free play may use them.  The slide residual
  likewise needs the source-pile condition `pileHolding c ≠ some kp`
  (a slide of a card below `p` carries `p` and `y` together and is the
  `p`-excursion case, not the AwaySlide case).
-/



#print axioms TwinPullLift.pulledAt_step_comm
#print axioms TwinPullLift.Att_stepDraw
#print axioms TwinPullLift.Att_dealStock
#print axioms TwinPullLift.Att_update_sw




















#print axioms TwinPullLift.Att_setFound
#print axioms TwinPullLift.Att_setPile
#print axioms TwinPullLift.raiseSquareResidual
#print axioms TwinPullLift.raiseSquare_proved










#print axioms TwinPullLift.Att_reversible_awayBasic
#print axioms TwinPullLift.pulledAt_functor_away
#print axioms TwinPullLift.pullLiftTop_away
#print axioms TwinPullLift.singleDetourIdentityArbitraryMid_of_pullLiftTop

/-! ## §8. The generic attachment functor

`pulledAt_functor_away` is the one-induction attachment functor for the
away class `AwayBasic` (draws and raises):

```
Ctx s y p → ShufflePlayW s play t →
  (∀ m ∈ play, AwayBasic y p m) → (∀ m ∈ play, NotFoundPair x m) →
  Ctx t y p → PairFreeOrbit x (Att s) (Att t)
```

The induction builds the lifted play letter by letter using
`Ctx.step_away`, `pulledAt_step_comm`, `raiseSquareResidual`, and
`Att_reversible_awayBasic`; the tail is composed with
`PairFreeOrbit.trans`.

`PullLiftFunctorResidual x y p` is the exact statement of the requested
general `pulledAt_functor` without the `AwayBasic` restriction.  The
missing letters are:

* `foundToTab` (the pull square `PullSquareResidual`, blocked on
  `Att_putCard`), and
* `tabToTab` (the slide square `SlideSquareResidual`, blocked on an
  `Att_putRun` analogue and the source-pile condition), and
* `wasteToFound`/`wasteToTab` (no away row at present), and
* the target-`p` excursion splicing (`p_excursion_cancels_local` plus a
  blocked-step replacement in the induction).

`AttSquareResidual y p` is not yet derived from the functor, because the
functor itself does not yet cover pull or slide; only its raise conjunct
is proved (`raiseSquare_proved`).
-/
