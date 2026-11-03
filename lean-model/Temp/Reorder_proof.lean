import Orig2.Fork.Class.ForkRaiseReorder

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# Orig2.Fork.Class.ForkRaiseReorder — the reordering target is FALSE

The brief `Temp/RAISE_BRIEF.md` names two obligations:

* `SpecShift`  — "raising one card never changes another card's readiness"
* `RaiseSReorder` — "a raiseS word containing `c` can be reordered so that `c`
  is raised last"

**Both are false**, and for the same structural reason: a raise removes the
pile top and *exposes the card beneath it*.  So a raise can *enable* another
card's `CanRaiseS` license (breaking the backward half of `SpecShift`), and a
card can be raisable *only after* another card has been raised (breaking the
reordering: that card cannot be moved earlier).

This file machine-checks both refutations on one concrete, well-formed state
(`probeState`), and then records the true local mechanisms (the
`CanRaiseS`/`RaiseStepS` bridge, word composition, WF transport, twin-free
persistence of `CanRaiseS`, and the one-swap lemmas) — all with the shift
hypothesis carried explicitly, as the brief asks.

House compliance: no `sorry`, no `Classical.choice`, no `noncomputable`;
battery at the tail (`[propext]` only).

## The probe state

The tableau holds one stack on pile `p0`:

    10♦  (bottom)
     9♠
     8♥  (top)

Foundations: `♠ ↦ A..8`, `♥ ↦ A..7`, `♦ ↦ []`, `♣ ↦ []`; everything else is
in the stock.

Two facts drive everything:

* `8♥` has **no legal seat** (it needs a black 9 on top of a pile; `9♠` is
  buried, `9♣` is in the stock), and neither has anything else in the
  tableau.  So *no cargo slide fires at all*, and hence the only cargo path
  from `probeState` is the trivial one (`probe_no_tabToTab`).
* `9♠` is buried under `8♥`, so it is not a pile top and cannot be raised
  (`probe_not_canRaiseS_c9S`); after `8♥` is raised it *is* the top and is
  legally raisable with a card beneath it (`probe_canRaiseS_afterC_c9S`).

Consequences:

* `¬ SpecShift`     — raising `8♥` turns `CanRaiseS · 9♠` from false to true;
* `¬ RaiseSReorder` — the legal word `[9♠, 8♥]` (i.e. `8♥` first, then `9♠`)
  contains `8♥` and `8♥` is raisableS at the start, but the reordered word
  `[8♥, 9♠]` would have to raise `9♠` first, which is impossible.
-/

namespace OneColourClosure

/-! ## §0. The retired forms (declared HERE, not in the card)

Both are **false**; the card keeps only the forward / rank-sorted statements.
The theorems below are the kernel-checked refutations of these exact forms. -/

/-- The retired `SpecShift` `↔` form.  **FALSE** (`specShift_false`). -/
def SpecShift : Prop :=
  ∀ {u z z' : State} {c d : Card},
    z.WF →
    RaiseStepS z z' c →
    d ≠ c →
    d ≠ c.twin →
    (CanRaiseS z d ↔ CanRaiseS z' d)

/-- The retired reordering target: `c` to the front, tail **as-is**.
**FALSE** (`raiseSReorder_false`). -/
def RaiseSReorder : Prop :=
  ∀ {s : State} {c : Card},
    CanRaiseS s c →
    ∀ {ws : List Card} {z : State},
      RaiseSSeq s ws z → c ∈ ws →
      ∃ z', RaiseSSeq s (c :: ws.erase c) z'

/-! ## §1. The concrete probe state -/

/-- The card `10♦`. -/
def c10D : Card := ⟨Suit.diamond, Rank.ten⟩

/-- The card `9♠`. -/
def c9S : Card := ⟨Suit.spade, Rank.nine⟩

/-- The card `8♥`. -/
def c8H : Card := ⟨Suit.heart, Rank.eight⟩

/-- The probe state: `p0` holds the stack `[10♦, 9♠, 8♥]` (8♥ on top),
foundations `♠ ↦ A..8`, `♥ ↦ A..7`, `♦ ↦ []`, `♣ ↦ []`, the rest stock. -/
def probeState : State where
  found := fun su =>
    match su with
    | .spade => (Suit.upCards .spade).take 8
    | .heart => (Suit.upCards .heart).take 7
    | .diamond => []
    | .club => []
  piles := fun a =>
    match a with
    | .p0 => ⟨[], [c10D, c9S, c8H]⟩
    | _ => ⟨[], []⟩
  stock := (Suit.upCards .spade).drop 9 ++ (Suit.upCards .heart).drop 8
    ++ ((Suit.upCards .diamond).take 9 ++ (Suit.upCards .diamond).drop 10)
    ++ Suit.upCards .club
  waste := []
  drawStep := 1

/-- The probe state is well formed (a genuine game position). -/
theorem probeState_WF : probeState.WF := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro su
    match su with
    | .spade => exact ⟨8, by decide⟩
    | .heart => exact ⟨7, by decide⟩
    | .diamond => exact ⟨0, by decide⟩
    | .club => exact ⟨0, by decide⟩
  · intro a
    match a with
    | .p0 => decide
    | .p1 => decide
    | .p2 => decide
    | .p3 => decide
    | .p4 => decide
    | .p5 => decide
    | .p6 => decide
  · intro c _
    rcases c with ⟨su, r⟩
    cases su <;> cases r <;> decide
  · decide

/-! ## §2. The two raises, concretely -/

theorem probe_nextUp_c8H : probeState.nextUp c8H = true := by decide

theorem probe_pileOfTop_c8H : probeState.pileOfTop c8H = some Anchor.p0 := by decide

theorem probe_pileOfTop_c9S : probeState.pileOfTop c9S = none := by decide

/-- The landing state of raising `8♥` at the probe state. -/
def afterC : State :=
  { probeState.setFound c8H.suit (probeState.found c8H.suit ++ [c8H]) with
    piles := fun a' =>
      if a' = Anchor.p0 then
        Pile.afterRunRemoved (probeState.piles Anchor.p0)
          (chop (probeState.piles Anchor.p0).faceUp)
      else probeState.piles a' }

theorem probe_step_c8H : State.step probeState (Move.tabToFound c8H) = some afterC :=
  step_tabToFound_splice probe_nextUp_c8H probe_pileOfTop_c8H

theorem afterC_nextUp_c9S : afterC.nextUp c9S = true := by decide

theorem afterC_pileOfTop_c9S : afterC.pileOfTop c9S = some Anchor.p0 := by decide

/-- The landing state of raising `9♠` at `afterC`. -/
def afterD : State :=
  { afterC.setFound c9S.suit (afterC.found c9S.suit ++ [c9S]) with
    piles := fun a' =>
      if a' = Anchor.p0 then
        Pile.afterRunRemoved (afterC.piles Anchor.p0)
          (chop (afterC.piles Anchor.p0).faceUp)
      else afterC.piles a' }

theorem afterC_step_c9S : State.step afterC (Move.tabToFound c9S) = some afterD :=
  step_tabToFound_splice afterC_nextUp_c9S afterC_pileOfTop_c9S

/-- **`8♥` then `9♠` is a legal raiseS word** — the word `[9♠, 8♥]` (the head
of a `RaiseSSeq` word is the *last* raise). -/
theorem probe_raiseSeq : RaiseSSeq probeState [c9S, c8H] afterD :=
  RaiseSSeq.cons
    (RaiseSSeq.cons (RaiseSSeq.nil probeState) (Steps.refl probeState) probe_step_c8H)
    (Steps.refl afterC) afterC_step_c9S

/-- `8♥` is raisableS at the probe state (top of `p0`, with `9♠` beneath). -/
theorem probe_canRaiseS_c8H : CanRaiseS probeState c8H :=
  CanRaiseS.now c8H
    ⟨probe_nextUp_c8H, ⟨Anchor.p0, probe_pileOfTop_c8H, Or.inl (by decide)⟩⟩

/-! ## §3. No cargo slide fires at the probe state -/

/-- The forward (WF-free) half of `pileOfTop_eq_some_iff`. -/
theorem pileOfTop_top_of_eq_some {st : State} {z : Card} {a : Anchor}
    (h : st.pileOfTop z = some a) : (st.piles a).top = some z :=
  of_decide_eq_true
    (firstWhere_sound (p := fun a' => decide (st.topOf a' = some z)) h)

/-- The only pile top at the probe state is `8♥`. -/
theorem probe_top_some_eq {a : Anchor} {y : Card}
    (h : (probeState.piles a).top = some y) : y = c8H := by
  match a with
  | .p0 =>
      have h' : some c8H = some y := h
      exact (Option.some.inj h').symm
  | .p1 => simp [probeState, Pile.top, lastOf] at h
  | .p2 => simp [probeState, Pile.top, lastOf] at h
  | .p3 => simp [probeState, Pile.top, lastOf] at h
  | .p4 => simp [probeState, Pile.top, lastOf] at h
  | .p5 => simp [probeState, Pile.top, lastOf] at h
  | .p6 => simp [probeState, Pile.top, lastOf] at h

/-- A non-king with no seat on the unique pile top has no seat at all. -/
theorem probe_canPlace_false_of {x : Card} (hnk : x.rank ≠ Rank.king)
    (hx : canSitOn x c8H = false) : ∀ b : Base, probeState.canPlace x b = false := by
  intro b
  cases b with
  | inl a => simp [State.canPlace, hnk]
  | inr y =>
      cases h : probeState.pileOfTop y with
      | none => simp [State.canPlace, h]
      | some a =>
          have hy : y = c8H := probe_top_some_eq (pileOfTop_top_of_eq_some h)
          subst hy
          simp only [State.canPlace, h]
          exact hx

theorem probe_no_seat_c8H : ∀ b : Base, probeState.canPlace c8H b = false :=
  probe_canPlace_false_of (by decide) (by decide)

theorem probe_no_seat_c9S : ∀ b : Base, probeState.canPlace c9S b = false :=
  probe_canPlace_false_of (by decide) (by decide)

theorem probe_no_seat_c10D : ∀ b : Base, probeState.canPlace c10D b = false :=
  probe_canPlace_false_of (by decide) (by decide)

/-- Only `10♦`, `9♠` and `8♥` are held face up at the probe state. -/
theorem probe_pileHolding_none {x : Card} (h10 : x ≠ c10D) (h9 : x ≠ c9S)
    (h8 : x ≠ c8H) : probeState.pileHolding x = none := by
  cases h : probeState.pileHolding x with
  | none => rfl
  | some a =>
      exfalso
      have hmem := pileHolding_mem h
      match a with
      | .p0 =>
          simp only [probeState, List.mem_cons, List.not_mem_nil, or_false] at hmem
          rcases hmem with h' | h' | h'
          · exact h10 h'
          · exact h9 h'
          · exact h8 h'
      | .p1 => simp [probeState] at hmem
      | .p2 => simp [probeState] at hmem
      | .p3 => simp [probeState] at hmem
      | .p4 => simp [probeState] at hmem
      | .p5 => simp [probeState] at hmem
      | .p6 => simp [probeState] at hmem

/-- **No tableau slide fires at the probe state**, for any card and any base. -/
theorem probe_no_tabToTab (x : Card) (b : Base) :
    State.step probeState (Move.tabToTab x b) = none := by
  rw [step_tabToTab_eq]
  by_cases h10 : x = c10D
  · subst h10
    have hph : probeState.pileHolding c10D = some Anchor.p0 := by decide
    rw [hph]
    simp [probe_no_seat_c10D b]
  · by_cases h8 : x = c8H
    · subst h8
      have hph : probeState.pileHolding c8H = some Anchor.p0 := by decide
      rw [hph]
      simp [probe_no_seat_c8H b]
    · by_cases h9 : x = c9S
      · subst h9
        have hph : probeState.pileHolding c9S = some Anchor.p0 := by decide
        rw [hph]
        simp [probe_no_seat_c9S b]
      · rw [probe_pileHolding_none h10 h9 h8]

/-- A cargo path whose source admits no slide is trivial. -/
theorem cargoPath_eq_of_noLeg {a b : State}
    (hno : ∀ (x : Card) (bb : Base), State.step a (Move.tabToTab x bb) = none)
    (h : CargoPath a b) : b = a := by
  cases h with
  | refl => rfl
  | cons hl _ =>
      obtain ⟨x, bb, hstep, -⟩ := hl
      rw [hno x bb] at hstep
      exact absurd hstep (by simp)

/-! ## §4. `9♠` is not raisableS now, but is raisableS after `8♥` is raised -/

/-- **`9♠` is not raisableS at the probe state**: it is buried and no cargo
slide is available to expose it. -/
theorem probe_not_canRaiseS_c9S : ¬ CanRaiseS probeState c9S := by
  rintro ⟨z₀, hp, hcr⟩
  have hz₀ : z₀ = probeState := cargoPath_eq_of_noLeg probe_no_tabToTab hp
  subst hz₀
  obtain ⟨-, a, hpa, -⟩ := hcr
  rw [probe_pileOfTop_c9S] at hpa
  exact absurd hpa (by simp)

/-- **`9♠` IS raisableS after `8♥` is raised** (it is now on top with `10♦`
beneath it). -/
theorem probe_canRaiseS_afterC_c9S : CanRaiseS afterC c9S :=
  CanRaiseS.now c9S
    ⟨afterC_nextUp_c9S, ⟨Anchor.p0, afterC_pileOfTop_c9S, Or.inl (by decide)⟩⟩

/-! ## §5. `SpecShift` is false -/

/-- **THE SHIFT OBLIGATION IS FALSE**: raising `8♥` changes `9♠`'s
`CanRaiseS` license (from false to true).  All the side conditions of
`SpecShift` hold: the state is `WF`, the step is a `RaiseStepS`, and `9♠` is
neither `8♥` nor its twin (`8♦`). -/
theorem specShift_false : ¬ SpecShift := by
  intro hS
  have hstepS : RaiseStepS probeState afterC c8H :=
    ⟨probeState, Steps.refl probeState, probe_step_c8H⟩
  have hiff := hS (u := probeState) probeState_WF hstepS
    (by decide : c9S ≠ c8H) (by decide : c9S ≠ c8H.twin)
  exact probe_not_canRaiseS_c9S (hiff.mpr probe_canRaiseS_afterC_c9S)

/-! ## §6. The reordering target is false -/

/-- **The reordered word `[8♥, 9♠]` is not legal**: its first raise would be
`9♠`, which is not raisableS at the probe state (nor at any cargo mate). -/
theorem probe_not_raiseSeq_swapped : ¬ ∃ z', RaiseSSeq probeState [c8H, c9S] z' := by
  rintro ⟨z', hz'⟩
  cases hz' with
  | cons htail hp hstep =>
      cases htail with
      | cons hnil hp2 hstep2 =>
          cases hnil
          have hu : _ = probeState := cargoPath_eq_of_noLeg probe_no_tabToTab hp2
          subst hu
          obtain ⟨-, a, hpa, -⟩ := step_tabToFound_inv hstep2
          rw [probe_pileOfTop_c9S] at hpa
          exact absurd hpa (by simp)

/-- **THE REORDERING PRINCIPLE IS FALSE.**

At `probeState`: `8♥` is raisableS, the word `[9♠, 8♥]` is a legal raiseS word
(raise `8♥`, then `9♠`), and `8♥` occurs in it — but the word with `8♥`
moved to the head, `[8♥, 9♠]`, is *not* legal.  So no reordering principle of
this shape can hold: the card that *exposes* `9♠` cannot be postponed past
it. -/
theorem raiseSReorder_false : ¬ RaiseSReorder := by
  intro hR
  have hmem : c8H ∈ [c9S, c8H] := by simp
  obtain ⟨z', hz'⟩ := hR probe_canRaiseS_c8H probe_raiseSeq hmem
  have hw : c8H :: [c9S, c8H].erase c8H = [c8H, c9S] := by decide
  rw [hw] at hz'
  exact probe_not_raiseSeq_swapped ⟨z', hz'⟩

/-! ## §7. The mechanisms, in their true (corrected) form

Everything *local* in the brief's plan is sound.  Below: the shift hypothesis
as a named bundle, its equivalence with `SpecShift`, the
`CanRaiseS`/`RaiseStepS` bridge, sequence composition, WF transport, the
twin-free persistence of `CanRaiseS` across a raiseS word (the correct form of
"the covers move forward"), and the two one-swap lemmas (the brief's stated
fallback).  Each takes the shift hypothesis explicitly, as asked.
-/

/-- The shift hypothesis (`SpecShift` without its unused `u` binder). -/
abbrev ShiftHyp : Prop :=
  ∀ {z z' : State} {c d : Card},
    z.WF → RaiseStepS z z' c → d ≠ c → d ≠ c.twin →
      (CanRaiseS z d ↔ CanRaiseS z' d)

theorem shiftHyp_iff_specShift : ShiftHyp ↔ SpecShift := by
  constructor
  · intro h u z z' c d hwf hst hdc hdt
    exact h hwf hst hdc hdt
  · intro h z z' c d hwf hst hdc hdt
    exact h (u := z) hwf hst hdc hdt

/-- **`SpecShift` fails even in the shift-only bundle** (corollary). -/
theorem shiftHyp_false : ¬ ShiftHyp := by
  intro h
  have hstepS : RaiseStepS probeState afterC c8H :=
    ⟨probeState, Steps.refl probeState, probe_step_c8H⟩
  exact probe_not_canRaiseS_c9S
    ((h probeState_WF hstepS
      (by decide : c9S ≠ c8H) (by decide : c9S ≠ c8H.twin)).mpr
        probe_canRaiseS_afterC_c9S)

/-- A `CanRaiseS` license fires a `RaiseStepS`. -/
theorem raiseStepS_of_canRaiseS {z : State} {c : Card} (h : CanRaiseS z c) :
    ∃ z', RaiseStepS z z' c := by
  obtain ⟨z₀, hp, hcr⟩ := h
  obtain ⟨z', hs⟩ := step_tabToFound_of_canRaise hcr
  exact ⟨z', z₀, hp, hs⟩

/-- Append one raise to a raiseS sequence. -/
theorem raiseSSeq_snoc {s z : State} {ws : List Card} {c : Card}
    (h : RaiseSSeq s ws z) (hz : ∃ z', RaiseStepS z z' c) :
    ∃ z', RaiseSSeq s (c :: ws) z' := by
  obtain ⟨z', z₀, hp, hs⟩ := hz
  exact ⟨z', RaiseSSeq.cons h hp hs⟩

/-- Sequence composition: playing `w₁` then `w₂` is the word `w₂ ++ w₁`
(the head of a word is the *last* raise). -/
theorem raiseSSeq_append {s u v : State} {w₁ w₂ : List Card}
    (h₁ : RaiseSSeq s w₁ u) (h₂ : RaiseSSeq u w₂ v) :
    RaiseSSeq s (w₂ ++ w₁) v := by
  induction h₂ generalizing s with
  | nil => exact h₁
  | cons _ hp hs ih =>
      rw [List.cons_append]
      exact RaiseSSeq.cons (ih h₁) hp hs

/-- A raiseS word transports well-formedness. -/
theorem raiseSSeq_wf {s z : State} {ws : List Card} (h : RaiseSSeq s ws z)
    (hwf : s.WF) : z.WF := by
  revert hwf
  induction h with
  | nil => exact id
  | cons _ hp hs ih => exact fun hwf => step_wf (cargoPath_wf (ih hwf) hp) hs

/-- **TWIN-FREE PERSISTENCE** — the correct form of "the covers move
forward": a raiseS word avoiding `c` and `c.twin` never disturbs `c`'s
`CanRaiseS` license.  (`c.twin` is exactly the obstruction: raising the twin
founds the alternative seat of `c`'s cover.) -/
theorem canRaiseS_persist (hshift : ShiftHyp) {s z : State} {ws : List Card}
    {x : Card} (h : RaiseSSeq s ws z) (hwf : s.WF)
    (hx : x ∉ ws) (hxt : x.twin ∉ ws) (hcan : CanRaiseS s x) :
    CanRaiseS z x := by
  revert hwf hx hxt hcan
  induction h with
  | nil => intro _ _ _ hcan; exact hcan
  | cons htail hp hs ih =>
      rename_i zz zz0 zz' cc wws
      intro hwf hx hxt hcan
      have hx' : x ∉ wws := fun hmem => hx (List.mem_cons_of_mem _ hmem)
      have hxt' : x.twin ∉ wws := fun hmem => hxt (List.mem_cons_of_mem _ hmem)
      have hxd : x ≠ cc := fun hcon => hx (by rw [hcon]; exact List.mem_cons_self ..)
      have hxtd : x ≠ cc.twin := by
        intro hcon
        have hmem : x.twin ∈ cc :: wws := by
          rw [hcon]
          exact List.mem_cons.mpr (Or.inl (card_twin_twin cc))
        exact hxt hmem
      have hzwf : zz.WF := raiseSSeq_wf htail hwf
      have hz : CanRaiseS zz x := ih hwf hx' hxt' hcan
      exact (hshift hzwf ⟨zz0, hp, hs⟩ hxd hxtd).mp hz

/-- **DEFER PAST A TWIN-FREE WORD** — a true special case of reordering: a card
whose word-raise (and twin) do not occur in `ws` can always be appended to the
end of `ws` chronologically. -/
theorem raiseSSeq_defer (hshift : ShiftHyp) {s z : State} {ws : List Card}
    {x : Card} (h : RaiseSSeq s ws z) (hwf : s.WF)
    (hx : x ∉ ws) (hxt : x.twin ∉ ws) (hcan : CanRaiseS s x) :
    ∃ z', RaiseSSeq s (x :: ws) z' :=
  raiseSSeq_snoc h (raiseStepS_of_canRaiseS (canRaiseS_persist hshift h hwf hx hxt hcan))

/-- **ONE-SWAP, `c` FIRST** (the brief's fallback statement, verbatim apart from
the `s.WF` that `SpecShift` itself requires): two licenses of different suits
fire in the given order. -/
theorem swap_of_ne_twin (hshift : ShiftHyp) {s : State} {c d : Card}
    (hs : s.WF) (hc : CanRaiseS s c) (hd : CanRaiseS s d)
    (hne : d ≠ c.twin) (hsu : d.suit ≠ c.suit) :
    ∃ s₂, RaiseStepS s s₂ c ∧ ∃ s₃, RaiseStepS s₂ s₃ d := by
  have hdc : d ≠ c := fun h => hsu (by rw [h])
  obtain ⟨s₂, hs₂⟩ := raiseStepS_of_canRaiseS hc
  have hd₂ : CanRaiseS s₂ d := (hshift hs hs₂ hdc hne).mp hd
  obtain ⟨s₃, hs₃⟩ := raiseStepS_of_canRaiseS hd₂
  exact ⟨s₂, hs₂, s₃, hs₃⟩

/-- **ONE-SWAP, `d` FIRST** — the mirror direction, the one a bubbling argument
needs (let a deferred card pass a block). -/
theorem swap_of_ne_twin' (hshift : ShiftHyp) {s : State} {c d : Card}
    (hs : s.WF) (hc : CanRaiseS s c) (hd : CanRaiseS s d)
    (hne : c ≠ d.twin) (hsu : d.suit ≠ c.suit) :
    ∃ s₂, RaiseStepS s s₂ d ∧ ∃ s₃, RaiseStepS s₂ s₃ c := by
  have hcd : c ≠ d := fun h => hsu (by rw [h])
  obtain ⟨s₂, hs₂⟩ := raiseStepS_of_canRaiseS hd
  have hc₂ : CanRaiseS s₂ c := (hshift hs hs₂ hcd hne).mp hc
  obtain ⟨s₃, hs₃⟩ := raiseStepS_of_canRaiseS hc₂
  exact ⟨s₂, hs₂, s₃, hs₃⟩

end OneColourClosure

#print axioms OneColourClosure.probeState_WF
#print axioms OneColourClosure.probe_raiseSeq
#print axioms OneColourClosure.probe_canRaiseS_c8H
#print axioms OneColourClosure.probe_not_canRaiseS_c9S
#print axioms OneColourClosure.probe_canRaiseS_afterC_c9S
#print axioms OneColourClosure.specShift_false
#print axioms OneColourClosure.raiseSReorder_false
#print axioms OneColourClosure.shiftHyp_false
#print axioms OneColourClosure.raiseSSeq_append
#print axioms OneColourClosure.raiseSSeq_wf
#print axioms OneColourClosure.canRaiseS_persist
#print axioms OneColourClosure.raiseSSeq_defer
#print axioms OneColourClosure.swap_of_ne_twin
#print axioms OneColourClosure.swap_of_ne_twin'
