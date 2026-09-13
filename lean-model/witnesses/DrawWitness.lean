import Klondike.Move

open State

/-! Counterexample candidate for `drawTo_comm_modAdjacent`:
    step 1, len 3, wrap (i = 2 = len-1, j = 0): (i+1) % len = 3 % 3 = 0 = j.
    Both orders succeed; end cursors 0 vs 1. -/

def cA : Card := ⟨Suit.heart, Rank.ace⟩
def cB : Card := ⟨Suit.heart, Rank.two⟩
def cC : Card := ⟨Suit.heart, Rank.three⟩

def stX : State where
  deal := { piles := fun _ => [], stock := [cA, cB, cC] }
  board := Board.empty
  heights := fun _ => 0
  depths := fun _ => 0
  stock := { cards := [cA, cB, cC], cursor := 0 }
  drawStep := 1

/-- info: some 2 -/
#guard_msgs in
#eval stX.stock.posOf cC   -- i = 2

/-- info: some 0 -/
#guard_msgs in
#eval stX.stock.posOf cA   -- j = 0

/-- info: 0 -/
#guard_msgs in
#eval ((2 + 1) % 3 : Nat)  -- (i+1) % len = j (hadj holds)

/-- info: true -/
#guard_msgs in
#eval (stX.applyDrawTo cC (Sum.inl Anchor.p0) >>= fun s => s.applyDrawTo cA (Sum.inl Anchor.p1)).isSome

/-- info: true -/
#guard_msgs in
#eval (stX.applyDrawTo cA (Sum.inl Anchor.p1) >>= fun s => s.applyDrawTo cC (Sum.inl Anchor.p0)).isSome

/-- info: some 0 -/
#guard_msgs in
#eval (stX.applyDrawTo cC (Sum.inl Anchor.p0) >>= fun s => s.applyDrawTo cA (Sum.inl Anchor.p1)).map fun s => s.stock.cursor

/-- info: some 1 -/
#guard_msgs in
#eval (stX.applyDrawTo cA (Sum.inl Anchor.p1) >>= fun s => s.applyDrawTo cC (Sum.inl Anchor.p0)).map fun s => s.stock.cursor

/-- info: some 1 -/
#guard_msgs in
#eval (stX.applyDrawTo cC (Sum.inl Anchor.p0) >>= fun s => s.applyDrawTo cA (Sum.inl Anchor.p1)).map fun s => s.stock.cards.length

/-- info: some 1 -/
#guard_msgs in
#eval (stX.applyDrawTo cA (Sum.inl Anchor.p1) >>= fun s => s.applyDrawTo cC (Sum.inl Anchor.p0)).map fun s => s.stock.cards.length
