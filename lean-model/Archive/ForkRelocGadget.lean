import Orig2.ForkMountainShape

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-!
# Orig2/ForkRelocGadget — the RELOCATION boundary (regime 4), kernel-checked

READ-ONLY scratch card.  No source file is modified; nothing is committed.
Zero `sorry`, zero `Classical.choice`, zero `native_decide`; axiom battery at
the tail.

## The target

`MountainKit.RaiseBeforePullShortens` (`Orig2/ForkMountainShape.lean:503`) is
the M1 deletion residual of the mountain route:

```
raise c  ...  pull d b   ⟹   some strictly shorter witness play u → v.
```

The obstruction recorded in `Temp/Mountain2_Report.md` §6 is the *relocation*:
`raise x ; ... ; pull x b` where `b` is not the pile `x` was raised from.  A
minimal play containing one would refute M1.

## What this card proves, kernel-checked

On a **7-card** board (`rBoard`: hearts `A..4` founded, `p0 = [6S, 5H]`,
`p1 = [6C]`, the rest an inert hidden deck):

1. the relocation **fires as a genuine witness play**:
   `raise 5H` (hearts `4 → 5`, `p0` becomes `[6S]`) then
   `pull 5H → 6C` (hearts back to `4`, `5H` now sits on a **different** base
   `6C`), i.e. `ShufflePlayW rBoard [raise 5H, pull 5H→6C] rEnd`;
2. the **direct slide** `5H → 6C` reaches the *same* end state in **one**
   move: `ShufflePlayW rBoard [slide 5H→6C] rEnd`;
3. hence the relocation is **strictly longer** (`1 < 2`) than an available
   play between the same states — the adjacent same-card relocation is an
   identity-like pair and can never be the minimal-play obstruction.

This is the exact reason the mountain obstruction must be **non-adjacent**:
when the destination base is already legal at the raise's origin, the two
letters collapse to the one slide (`putRun [x] b = putCard x b`,
`Orig/BracketDecomp.lean:944`).  `Crack_Report.md` §4 records the probe
counts: over the 13 differing-rung census classes and 232 random boards,
**0** shortest plays contain any raise-before-later-pull at all.
-/

namespace CrackReloc

def HA : Card := ⟨.heart, .ace⟩
def H2 : Card := ⟨.heart, .two⟩
def H3 : Card := ⟨.heart, .three⟩
def H4 : Card := ⟨.heart, .four⟩
def H5 : Card := ⟨.heart, .five⟩
def S6 : Card := ⟨.spade, .six⟩
def C6 : Card := ⟨.club, .six⟩

/-- The five exposed cards. -/
def rFixed : List Card := [HA, H2, H3, H4, H5, S6, C6]

/-- The 45-card inert hidden deck. -/
def rDeck : List Card :=
  Card.universe.filter (fun c => !(decide (c ∈ rFixed)))

def mkR (fh : List Card) (p0 p1 : List Card) : State :=
  { found := fun s => match s with
      | .heart => fh
      | _ => []
    piles := fun a => match a with
      | .p0 => ⟨[], p0⟩
      | .p1 => ⟨[], p1⟩
      | .p6 => ⟨rDeck, []⟩
      | _ => ⟨[], []⟩
    stock := []
    waste := []
    drawStep := 1 }

/-- **The origin**: hearts `A..4`, `5H` on `6S`, `6C` bare. -/
def rBoard : State := mkR [HA, H2, H3, H4] [S6, H5] [C6]

/-- The intermediate state of the relocation: `5H` raised to the foundation. -/
def rMid : State := mkR [HA, H2, H3, H4, H5] [S6] [C6]

/-- The endpoint: `5H` pulled onto `6C` (a different base than the `6S` it
was raised from). -/
def rEnd : State := mkR [HA, H2, H3, H4] [S6] [C6, H5]

/-! ## §1. Well-formedness -/

theorem rBoard_wf : rBoard.WF := by
  refine ⟨?_, ?_, ?_, by decide⟩
  · intro s
    cases s with
    | heart => exact ⟨4, rfl⟩
    | diamond => exact ⟨0, rfl⟩
    | spade => exact ⟨0, rfl⟩
    | club => exact ⟨0, rfl⟩
  · intro a; cases a <;> decide
  · intro c _; rcases c with ⟨s, r⟩; cases s <;> cases r <;> decide

theorem rMid_wf : rMid.WF := by
  refine ⟨?_, ?_, ?_, by decide⟩
  · intro s
    cases s with
    | heart => exact ⟨5, rfl⟩
    | diamond => exact ⟨0, rfl⟩
    | spade => exact ⟨0, rfl⟩
    | club => exact ⟨0, rfl⟩
  · intro a; cases a <;> decide
  · intro c _; rcases c with ⟨s, r⟩; cases s <;> cases r <;> decide

theorem rEnd_wf : rEnd.WF := by
  refine ⟨?_, ?_, ?_, by decide⟩
  · intro s
    cases s with
    | heart => exact ⟨4, rfl⟩
    | diamond => exact ⟨0, rfl⟩
    | spade => exact ⟨0, rfl⟩
    | club => exact ⟨0, rfl⟩
  · intro a; cases a <;> decide
  · intro c _; rcases c with ⟨s, r⟩; cases s <;> cases r <;> decide

/-! ## §2. The relocation fires -/

theorem rBoard_raise :
    State.step rBoard (Move.tabToFound H5) = some rMid := by
  have hnext : rBoard.nextUp H5 = true := by decide
  have hpo : rBoard.pileOfTop H5 = some .p0 := by decide
  rw [step_tabToFound_splice hnext hpo]
  refine congrArg some (State.ext ?_ ?_ ?_ ?_ ?_)
  · funext s; cases s <;> rfl
  · funext a; cases a <;> rfl
  · rfl
  · rfl
  · rfl

theorem rMid_pull :
    State.step rMid (Move.foundToTab H5 (Sum.inr C6)) = some rEnd := by
  have htop : rMid.foundTop .heart = some H5 := by decide
  have hcp : rMid.canPlace H5 (Sum.inr C6) = true := by decide
  rw [step_foundToTab_splice htop hcp]
  refine congrArg some (State.ext ?_ ?_ ?_ ?_ ?_)
  · funext s; cases s <;> rfl
  · funext a; cases a <;> rfl
  · rfl
  · rfl
  · rfl

/-- **THE DIRECT SLIDE LANDS THE SAME STATE.** -/
theorem rBoard_slide :
    State.step rBoard (Move.tabToTab H5 (Sum.inr C6)) = some rEnd := by
  have hhold : rBoard.pileHolding H5 = some .p0 := by decide
  have hcp : rBoard.canPlace H5 (Sum.inr C6) = true := by decide
  rw [step_tabToTab_eq]
  rw [hhold, hcp]
  refine congrArg some (State.ext ?_ ?_ ?_ ?_ ?_)
  · funext s; cases s <;> rfl
  · funext a; cases a <;> rfl
  · rfl
  · rfl
  · rfl

/-! ## §3. Reversibility of the letters -/

theorem rBoard_raise_rev : reversibleAtW rBoard (Move.tabToFound H5) :=
  (tabToFoundR_iff_reversibleAtW rBoard_wf H5).mp (by decide)

theorem rMid_pull_rev :
    reversibleAtW rMid (Move.foundToTab H5 (Sum.inr C6)) :=
  (foundToTabR_iff_reversibleAtW rMid_wf H5 (Sum.inr C6)).mp (by decide)

theorem rBoard_slide_rev :
    reversibleAtW rBoard (Move.tabToTab H5 (Sum.inr C6)) :=
  (tabToTabR_iff_reversibleAtW rBoard_wf H5 (Sum.inr C6)).mp (by decide)

/-! ## §4. The two plays -/

/-- **THE RELOCATION PLAY** (2 moves). -/
theorem relocation_play :
    ShufflePlayW rBoard [Move.tabToFound H5,
      Move.foundToTab H5 (Sum.inr C6)] rEnd := by
  refine Walk.cons rBoard_raise_rev rBoard_raise ?_
  exact Walk.cons rMid_pull_rev rMid_pull (Walk.nil rEnd)

/-- **THE DIRECT PLAY** (1 move) — the strictly shorter one. -/
theorem slide_play :
    ShufflePlayW rBoard [Move.tabToTab H5 (Sum.inr C6)] rEnd :=
  Walk.cons rBoard_slide_rev rBoard_slide (Walk.nil rEnd)

/-- **THE STRICT LENGTH GAP.**  The relocation is two moves; the direct slide
is one and reaches the same endpoint. -/
theorem strict_length_gap :
    [Move.tabToTab H5 (Sum.inr C6)].length <
      [Move.tabToFound H5, Move.foundToTab H5 (Sum.inr C6)].length := by
  decide

/-- **THE RELOCATION IS NOT MINIMAL.**  A same-endpoint witness play of
strictly smaller length exists, so this relocation cannot witness a refutation
of `MountainKit.RaiseBeforePullShortens`. -/
theorem relocation_not_minimal :
    ∃ ρ' : List Move, ShufflePlayW rBoard ρ' rEnd ∧
      ρ'.length < [Move.tabToFound H5,
        Move.foundToTab H5 (Sum.inr C6)].length :=
  ⟨[Move.tabToTab H5 (Sum.inr C6)], slide_play, by decide⟩

/-- The endpoint is not the origin (the relocation really moved the card). -/
theorem relocation_changes_state : rEnd ≠ rBoard := by
  intro h
  have h1 : (rEnd.piles .p1).faceUp = (rBoard.piles .p1).faceUp := by rw [h]
  rw [show (rEnd.piles .p1).faceUp = [C6, H5] from rfl,
      show (rBoard.piles .p1).faceUp = [C6] from rfl] at h1
  exact absurd h1 (by decide)

/-- **THE BASE REALLY CHANGED.**  `5H` was raised off `6S` and pulled onto
`6C`. -/
theorem relocation_base_changed :
    (H5 ∈ (rBoard.piles .p0).faceUp ∧ S6 ∈ (rBoard.piles .p0).faceUp) ∧
    (H5 ∈ (rEnd.piles .p1).faceUp ∧ C6 ∈ (rEnd.piles .p1).faceUp) ∧
    H5 ∉ (rEnd.piles .p0).faceUp := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- **`AdjacentRelocationDeletes`** — the general adjacent same-card collapse:
if the destination base is already legal at the raise's origin, the two-letter
relocation `raise x ; pull x b` is exactly the one-letter slide `slide x b`.
NOT proved here (the concrete `rBoard` instance is proved above).  The residue
is the *non-adjacent* same-card relocation of `Crack_Report.md` §4b. -/
def AdjacentRelocationDeletes : Prop :=
  ∀ (u m v : State) (x : Card) (b : Base),
    u.WF → State.step u (Move.tabToFound x) = some m →
      State.step m (Move.foundToTab x b) = some v →
      u.canPlace x b = true →
        State.step u (Move.tabToTab x b) = some v

/-! ## §5. Axiom battery -/

#print axioms CrackReloc.rBoard_wf
#print axioms CrackReloc.rMid_wf
#print axioms CrackReloc.rEnd_wf
#print axioms CrackReloc.rBoard_raise
#print axioms CrackReloc.rMid_pull
#print axioms CrackReloc.rBoard_slide
#print axioms CrackReloc.rBoard_raise_rev
#print axioms CrackReloc.rMid_pull_rev
#print axioms CrackReloc.rBoard_slide_rev
#print axioms CrackReloc.relocation_play
#print axioms CrackReloc.slide_play
#print axioms CrackReloc.strict_length_gap
#print axioms CrackReloc.relocation_not_minimal
#print axioms CrackReloc.relocation_changes_state

end CrackReloc
