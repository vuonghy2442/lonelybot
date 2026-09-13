import Klondike.Macro

/-! Scratch witness: `macroStep_engine_play` is UNSOUND as stated.

`State.applyDrawTo` attaches `c` at `b` guarded only by `Board.attach`
(base free, card unplaced) — NOT by `st.canPlace c b`.  So the macro
game admits a Draw commitment whose landing no physical move set can
ever produce (deckPile/stackPile/pilePile all demand canPlace; reveal
attaches only hidden deal cards).  Witness: ♠7 visible as the sole
card of pile 0, ♥5 the last stock card (cursor at the pass end, so it
is reachable), landing base `inr ♠7` — canSitOn ♥5 ♠7 is false. -/

open State Cycle

def spade7 : Card := ⟨Suit.spade, Rank.seven⟩
def heart5 : Card := ⟨Suit.heart, Rank.five⟩

def W : State where
  deal := { piles := fun a => if a = Anchor.p0 then [spade7] else [], stock := [heart5] }
  board := (Board.empty.attach (Sum.inl Anchor.p0) spade7).getD Board.empty
  heights := fun _ => 0
  depths := fun _ => 0
  stock := ⟨[heart5], 1⟩
  drawStep := 1

-- the macro step's accommodation half: the empty play
example : accommodates W W := ⟨[], rfl, by intro m hm; cases hm⟩

-- the Draw commitment half: the guard admits the jump, the attach succeeds
#eval (W.applyDrawTo heart5 (Sum.inr spade7)).isSome          -- true
#eval (W.applyDrawTo heart5 (Sum.inr spade7)).map
  fun s => s.board.topOf (Sum.inr spade7) == some heart5        -- some true: the illegal edge exists
#eval (W.applyDrawTo heart5 (Sum.inr spade7)).map fun s => s.stock.cursor -- some 0
#eval (W.applyDrawTo heart5 (Sum.inr spade7)).map fun s => s.stock.cards.length -- some 0 (♥5 consumed)
#eval W.reachablePos heart5                                    -- some 0

-- ...but the landing violates the physical placement rule (pure, state-independent):
#eval W.canPlace heart5 (Sum.inr spade7)                       -- false
#eval canSitOn heart5 spade7                                    -- false (5 ≠ 7−1 = 6)

-- and no move from W can create that edge (every edge-creating guard fails):
#eval W.legal (Move.deckPile heart5 (Sum.inr spade7))          -- false (canPlace)
#eval W.legal (Move.deckStack heart5)                           -- false (rank ≠ height 0)
#eval W.legal (Move.stackPile heart5 (Sum.inr spade7))          -- false (rank+1 ≠ 0)
#eval W.legal (Move.pilePile heart5 (Sum.inr spade7))           -- false (canPlace)
#eval W.legal (Move.pileStack spade7)                            -- false (rank ≠ height 0)
#eval W.legal (Move.reveal spade7)                              -- false (no hidden cards)
#eval W.legal (Move.reveal heart5)                              -- false (not visible)
-- the only legal move is `.draw` (toggles the cursor), so the successor is unreachable.
