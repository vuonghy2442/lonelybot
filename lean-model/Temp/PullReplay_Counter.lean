import Temp.PullReplay

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

/-!
# Temp/PullReplay_Counter — `block_end_licensed` is false in the twin case

A kernel witness for the residual recorded in `Temp/PullReplay_Report.md`.
The board:

* hearts `A..4` and diamonds `A..4` founded;
* `p0 = [6♣, 5♥, 4♠]` (so `5♥` is buried under `4♠`, with `6♣` below it);
* `p1 = [6♠, 5♦]` (so `5♦ = (5♥).twin` tops a pile);
* everything else in the stock.

At `u`, `CanRaiseS u 5♥` holds: `5♥` is next-up, has `6♣` below, and its
twin `5♦` tops `p1` (the buried-card disjunct).  The one-letter play
`raise 5♦` fires.  At the landing `bnd`, `5♦` is on the foundation, so the
twin-top disjunct is gone; `5♥` is still buried under `4♠`, whose only card
seats are `5♥` and `5♦` (`cover_seats`) and which cannot move to an empty
pile (it is not a king).  Hence `¬ CanRaiseS bnd 5♥`.

This shows the unconditional `block_end_licensed` (without
`c.twin ∉ ws`) is false, so the twin case is a genuine residual.
-/

namespace PullReplayCounter

open OneColourClosure

/-- `A♥`. -/
def H1 : Card := ⟨.heart, .ace⟩
/-- `2♥`. -/
def H2 : Card := ⟨.heart, .two⟩
/-- `3♥`. -/
def H3 : Card := ⟨.heart, .three⟩
/-- `4♥`. -/
def H4 : Card := ⟨.heart, .four⟩
/-- `5♥` — the card `c`. -/
def H5 : Card := ⟨.heart, .five⟩
/-- `A♦`. -/
def D1 : Card := ⟨.diamond, .ace⟩
/-- `2♦`. -/
def D2 : Card := ⟨.diamond, .two⟩
/-- `3♦`. -/
def D3 : Card := ⟨.diamond, .three⟩
/-- `4♦`. -/
def D4 : Card := ⟨.diamond, .four⟩
/-- `5♦ = (5♥).twin`. -/
def D5 : Card := ⟨.diamond, .five⟩
/-- `6♣` — directly below `5♥`. -/
def C6 : Card := ⟨.club, .six⟩
/-- `4♠` — the cover of `5♥`. -/
def S4 : Card := ⟨.spade, .four⟩
/-- `6♠` — directly below `5♦` (gives `5♦` the company to be raised). -/
def S6 : Card := ⟨.spade, .six⟩

/-- The 13 placed cards. -/
def placed : List Card :=
  [H1, H2, H3, H4, D1, D2, D3, D4, H5, D5, C6, S4, S6]

/-- Everything else sits in the stock. -/
def rest : List Card :=
  Card.universe.filter (fun x => decide (x ∉ placed))

/-- The counterexample board. -/
def u : State :=
  { found := fun s => match s with
      | .heart => [H1, H2, H3, H4]
      | .diamond => [D1, D2, D3, D4]
      | _ => []
    piles := fun a => match a with
      | .p0 => ⟨[], [C6, H5, S4]⟩
      | .p1 => ⟨[], [S6, D5]⟩
      | _ => ⟨[], []⟩
    stock := rest
    waste := []
    drawStep := 1 }

/-- The landing of the one-letter play: raise `5♦`. -/
def bnd : State :=
  { u.setFound .diamond (u.found .diamond ++ [D5]) with
      piles := fun a' =>
        if a' = Anchor.p1 then
          Pile.afterRunRemoved (u.piles Anchor.p1)
            (chop (u.piles Anchor.p1).faceUp)
        else u.piles a' }

/-! ## §0. Well-formedness -/

theorem u_wf_found : ∀ s : Suit, ∃ n, u.found s = s.upCards.take n := by
  intro s
  cases s with
  | heart => exact ⟨4, by decide⟩
  | diamond => exact ⟨4, by decide⟩
  | spade => exact ⟨0, rfl⟩
  | club => exact ⟨0, rfl⟩

theorem u_wf_runs : ∀ a : Anchor, runOK (u.piles a).faceUp = true := by
  intro a
  cases a <;> decide

theorem u_wf_count : ∀ c ∈ Card.universe, u.cardCount c = 1 := by
  intro c _
  rcases c with ⟨s, r⟩
  cases s <;> cases r <;> decide

theorem u_wf : u.WF := ⟨u_wf_found, u_wf_runs, u_wf_count, by decide⟩

/-! ## §1. The step `raise 5♦` -/

theorem u_nextUp_D5 : u.nextUp D5 = true := by
  unfold State.nextUp State.foundHeight
  decide

theorem u_pileOfTop_D5 : u.pileOfTop D5 = some Anchor.p1 := by decide

theorem step_raise : State.step u (Move.tabToFound D5) = some bnd := by
  rw [step_tabToFound_splice u_nextUp_D5 u_pileOfTop_D5]
  rfl

theorem bnd_wf : bnd.WF := step_wf u_wf step_raise

theorem u_live_D5 : CanRaiseS u D5 :=
  (canRaiseSB_iff u_wf).mp (by decide)

/-- **The one-letter licensed play.** -/
theorem play : RaiseSSeqLicensed u [D5] bnd :=
  RaiseSSeqLicensed.cons (RaiseSSeqLicensed.nil u) u_live_D5 (Steps.refl u)
    step_raise

/-! ## §2. `5♥` is alive before and dead after -/

theorem u_live_H5 : CanRaiseS u H5 :=
  (canRaiseSB_iff u_wf).mp (by decide)

theorem bnd_dead_H5 : ¬ CanRaiseS bnd H5 := by
  intro h
  have hSB : canRaiseSB bnd H5 = true := (canRaiseSB_iff bnd_wf).mpr h
  have hfalse : canRaiseSB bnd H5 = false := by decide
  rw [hfalse] at hSB
  exact Bool.noConfusion hSB

theorem hnosuit : ∀ d ∈ [D5], d.suit ≠ H5.suit := by
  intro d hd
  rw [List.mem_singleton] at hd
  subst hd
  decide

/-- **THE RESIDUAL IS REAL.**  The unconditional block-end licence (without
`c.twin ∉ ws`) is false: `u` licenses `5♥`, the word `[5♦]` is licensed from
`u` and avoids `5♥`'s suit, yet the landing does not license `5♥`. -/
theorem block_end_licensed_twin_refuted :
    ∃ (u bnd : State) (c : Card) (low : List Card),
      u.WF ∧ RaiseSSeqLicensed u (playWord low) bnd ∧
        CanRaiseS u c ∧ (∀ d ∈ low, d.suit ≠ c.suit) ∧ ¬ CanRaiseS bnd c :=
  ⟨u, bnd, H5, [D5], u_wf, by simpa [playWord] using play, u_live_H5, hnosuit,
    bnd_dead_H5⟩

end PullReplayCounter

#print axioms PullReplayCounter.u_wf
#print axioms PullReplayCounter.play
#print axioms PullReplayCounter.u_live_H5
#print axioms PullReplayCounter.bnd_dead_H5
#print axioms PullReplayCounter.block_end_licensed_twin_refuted
