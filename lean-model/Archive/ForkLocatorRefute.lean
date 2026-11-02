import Orig2.Fork.Split.ForkSplit
import Orig2.Fork.Local.ForkCommute

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

/-!
# Orig2/ForkLocatorRefute — `ValleyCrossingLocator` is FALSE (SCRATCH)

READ-ONLY scratch (no existing source touched; no commit).  Zero
`sorry`, zero `Classical.choice`, zero `native_decide`; battery at the
tail.

## Headline

`ValleyElim.ValleyCrossingLocator` (`Orig2/Fork/Split/ForkSplit.lean:912`) is
**refutable in the kernel**.  The statement demands that every witness
play containing an adjacent crossing turn `pull c ; raise d` contain a
contiguous four-letter crossing block.  But a two-letter play *is* such
a turn and cannot contain a four-letter block: the partner letters
(`pull d` before and `raise c` after) need not exist in the play at
all, and no commutation square can conjure them.

The witness board is the smallest legal one: `A♠` founded, `2♥` alone
on `p1`, `2♣ ; A♦` on `p2`, everything else in the stock.  The play
`pull A♠ (inr 2♥) ; raise A♦` is a complete `ShufflePlayW` from `u`
to `v`; the turn is a genuine crossing (`A♠ ≠ A♦`, different suits);
and `ρ` has length 2, so `CrossingBlock u v ρ` is impossible.
-/

namespace LocatorRefute

/-- Ace of spades. -/
def AS : Card := ⟨.spade, .ace⟩
/-- Ace of diamonds. -/
def AD : Card := ⟨.diamond, .ace⟩
/-- Two of hearts. -/
def H2 : Card := ⟨.heart, .two⟩
/-- Two of clubs. -/
def C2 : Card := ⟨.club, .two⟩

/-- The 48 cards left over. -/
def rest : List Card :=
  Card.universe.filter (fun x => decide (x ≠ AS ∧ x ≠ H2 ∧ x ≠ C2 ∧ x ≠ AD))

/-- The counterexample board. -/
def u : State :=
  { found := fun s => match s with
      | .spade => [AS]
      | _ => []
    piles := fun a => match a with
      | .p1 => ⟨[], [H2]⟩
      | .p2 => ⟨[], [C2, AD]⟩
      | _ => ⟨[], []⟩
    stock := rest
    waste := []
    drawStep := 1 }

/-- The pull landing. -/
def F : State := (u.setFound .spade (chop (u.found .spade))).putCard AS (Sum.inr H2)

/-- The play landing. -/
def v : State := (F.setFound .diamond (F.found .diamond ++ [AD])).setPile
  (Anchor.p2) (Pile.afterRunRemoved (F.piles .p2) (chop (F.piles .p2).faceUp))

/-! ## §0. The branch data -/

theorem u_wf_found : ∀ s : Suit, ∃ n, u.found s = s.upCards.take n := by
  intro s
  cases s with
  | spade => exact ⟨1, rfl⟩
  | heart => exact ⟨0, rfl⟩
  | diamond => exact ⟨0, rfl⟩
  | club => exact ⟨0, rfl⟩

theorem u_wf_runs : ∀ a : Anchor, runOK (u.piles a).faceUp = true := by
  intro a
  cases a <;> rfl

theorem u_wf_count : ∀ c ∈ Card.universe, u.cardCount c = 1 := by
  intro c _
  rcases c with ⟨s, r⟩
  cases s <;> cases r <;> decide

theorem u_wf : u.WF := ⟨u_wf_found, u_wf_runs, u_wf_count, by decide⟩

theorem step_pull : State.step u (Move.foundToTab AS (Sum.inr H2)) = some F := by rfl
theorem step_raise : State.step F (Move.tabToFound AD) = some v := by rfl

theorem F_wf : F.WF := step_wf u_wf step_pull

theorem pull_rev : reversibleAtW u (Move.foundToTab AS (Sum.inr H2)) :=
  (foundToTabR_iff_reversibleAtW u_wf AS (Sum.inr H2)).mp (by decide)

theorem raise_rev : reversibleAtW F (Move.tabToFound AD) :=
  (tabToFoundR_iff_reversibleAtW F_wf AD).mp (by decide)

/-- **THE COMPLETE CROSSING-TURN PLAY.** -/
theorem play :
    ShufflePlayW u [Move.foundToTab AS (Sum.inr H2), Move.tabToFound AD] v :=
  Walk.cons pull_rev step_pull (Walk.cons raise_rev step_raise (Walk.nil v))

theorem c_ne_d : AS ≠ AD := by decide
theorem suit_ne : AS.suit ≠ AD.suit := by decide

/-! ## §1. Structural obstructions on `CrossingBlock` -/

/-- A crossing block occupies four letters. -/
theorem crossingBlock_length {u v : State} {ρ : List Move}
    (h : ValleyElim.CrossingBlock u v ρ) : 4 ≤ ρ.length := by
  obtain ⟨α, β, c, d, bd, bc, A, B, C, D, E, hρ, -, -, -, -, -, -⟩ := h
  rw [hρ]
  simp only [List.length_append, List.length_cons, List.length_nil]
  omega

/-- Pull count is additive. -/
theorem pullTotal_append : ∀ a b : List Move, pullTotal (a ++ b) = pullTotal a + pullTotal b
  | [], b => by simp [pullTotal]
  | m :: t, b => by
      cases m <;> simp [pullTotal, pullTotal_append t b] <;> omega

/-- Raise count is additive. -/
theorem raiseTotal_append : ∀ a b : List Move, raiseTotal (a ++ b) = raiseTotal a + raiseTotal b
  | [], b => by simp [raiseTotal]
  | m :: t, b => by
      cases m <;> simp [raiseTotal, raiseTotal_append t b] <;> omega

/-- A crossing block contains two pulls. -/
theorem crossingBlock_pullTotal {u v : State} {ρ : List Move}
    (h : ValleyElim.CrossingBlock u v ρ) : 2 ≤ pullTotal ρ := by
  obtain ⟨α, β, c, d, bd, bc, A, B, C, D, E, hρ, -, -, -, -, -, -⟩ := h
  rw [hρ, pullTotal_append, pullTotal_append]
  simp [pullTotal]
  omega

/-- A crossing block contains two raises. -/
theorem crossingBlock_raiseTotal {u v : State} {ρ : List Move}
    (h : ValleyElim.CrossingBlock u v ρ) : 2 ≤ raiseTotal ρ := by
  obtain ⟨α, β, c, d, bd, bc, A, B, C, D, E, hρ, -, -, -, -, -, -⟩ := h
  rw [hρ, raiseTotal_append, raiseTotal_append]
  simp [raiseTotal]
  omega

/-- **NO BLOCK IN THE TWO-LETTER PLAY.** -/
theorem not_block :
    ¬ ValleyElim.CrossingBlock u v
        [Move.foundToTab AS (Sum.inr H2), Move.tabToFound AD] := by
  intro h
  have h4 := crossingBlock_length h
  simp only [List.length_cons, List.length_nil] at h4
  omega

/-- **NO BLOCK, PULL-COUNT FORM** (usable for longer plays too). -/
theorem not_block_of_pullTotal {ρ : List Move}
    (h : pullTotal ρ ≤ 1) : ¬ ValleyElim.CrossingBlock u v ρ := by
  intro hb
  have := crossingBlock_pullTotal hb
  omega

/-! ## §2. The refutation -/

/-- **`ValleyCrossingLocator` IS FALSE.** -/
theorem valleyCrossingLocator_false : ¬ ValleyElim.ValleyCrossingLocator := by
  intro hloc
  have hblock : ValleyElim.CrossingBlock u v
      [Move.foundToTab AS (Sum.inr H2), Move.tabToFound AD] :=
    hloc u v [Move.foundToTab AS (Sum.inr H2), Move.tabToFound AD] u [] []
      AS AD (Sum.inr H2) [] u_wf play
      (by simp only [List.append_nil, List.nil_append]) (Walk.nil u) c_ne_d suit_ne
  exact not_block hblock

end LocatorRefute

#print axioms LocatorRefute.u_wf
#print axioms LocatorRefute.play
#print axioms LocatorRefute.crossingBlock_length
#print axioms LocatorRefute.crossingBlock_pullTotal
#print axioms LocatorRefute.not_block
#print axioms LocatorRefute.valleyCrossingLocator_false
