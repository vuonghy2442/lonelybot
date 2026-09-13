import Klondike.Move

open State

def cA : Card := ⟨Suit.heart, Rank.ace⟩
def cB : Card := ⟨Suit.heart, Rank.two⟩
def cC : Card := ⟨Suit.heart, Rank.three⟩
def cD : Card := ⟨Suit.heart, Rank.four⟩

def mkSt (cards : List Card) (cur step : Nat) : State where
  deal := { piles := fun _ => [], stock := cards }
  board := Board.empty
  heights := fun _ => 0
  depths := fun _ => 0
  stock := { cards := cards, cursor := cur }
  drawStep := step

/-! NON-wrap sanity: i=1, j=2, len=4, step=1 — adjacent, expect EQUAL end
cursors (both orders: `some (1, 2)`). -/

/-- info: some (1, 2) -/
#guard_msgs in
#eval (mkSt [cA, cB, cC, cD] 0 1).applyDrawTo cB (Sum.inl Anchor.p0) >>= fun s => s.applyDrawTo cC (Sum.inl Anchor.p1) |>.map fun s => (s.stock.cursor, s.stock.cards.length)

/-- info: some (1, 2) -/
#guard_msgs in
#eval (mkSt [cA, cB, cC, cD] 0 1).applyDrawTo cC (Sum.inl Anchor.p1) >>= fun s => s.applyDrawTo cB (Sum.inl Anchor.p0) |>.map fun s => (s.stock.cursor, s.stock.cards.length)

/-! WRAP at step 3, len 3, cursor 1: order 1 (cC at 2 first) — the SECOND
move FAILS (position 0 unreachable from the saturated cursor). -/

/-- info: false -/
#guard_msgs in
#eval ((mkSt [cA, cB, cC] 1 3).applyDrawTo cC (Sum.inl Anchor.p0) >>= fun s => s.applyDrawTo cA (Sum.inl Anchor.p1)).isSome

/-! order 2 (cA at 0 first) — SUCCESS (leading lane), end cursor 1 = len-2. -/

/-- info: some (1, 1) -/
#guard_msgs in
#eval (mkSt [cA, cB, cC] 1 3).applyDrawTo cA (Sum.inl Anchor.p1) >>= fun s => s.applyDrawTo cC (Sum.inl Anchor.p0) |>.map fun s => (s.stock.cursor, s.stock.cards.length)

/-! WRAP at len 2, step 2, cursor 1: both orders — expect EQUAL (cursor 0). -/

/-- info: some (0, 0) -/
#guard_msgs in
#eval (mkSt [cA, cB] 1 2).applyDrawTo cB (Sum.inl Anchor.p0) >>= fun s => s.applyDrawTo cA (Sum.inl Anchor.p1) |>.map fun s => (s.stock.cursor, s.stock.cards.length)

/-- info: some (0, 0) -/
#guard_msgs in
#eval (mkSt [cA, cB] 1 2).applyDrawTo cA (Sum.inl Anchor.p1) >>= fun s => s.applyDrawTo cB (Sum.inl Anchor.p0) |>.map fun s => (s.stock.cursor, s.stock.cards.length)

/-! NON-adjacent divergence sanity: i=0, j=2, len 3, step 1 — expect
cursors j-1=1 vs i=0. -/

/-- info: some 1 -/
#guard_msgs in
#eval (mkSt [cA, cB, cC] 0 1).applyDrawTo cA (Sum.inl Anchor.p0) >>= fun s => s.applyDrawTo cC (Sum.inl Anchor.p1) |>.map fun s => s.stock.cursor

/-- info: some 0 -/
#guard_msgs in
#eval (mkSt [cA, cB, cC] 0 1).applyDrawTo cC (Sum.inl Anchor.p1) >>= fun s => s.applyDrawTo cA (Sum.inl Anchor.p0) |>.map fun s => s.stock.cursor
