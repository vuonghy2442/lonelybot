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

#eval stX.stock.posOf cC   -- expect some 2  (i = 2)
#eval stX.stock.posOf cA   -- expect some 0  (j = 0)
#eval ((2 + 1) % 3 : Nat)  -- expect 0       (hadj holds)

#eval (stX.applyDrawTo cC (Sum.inl Anchor.p0) >>= fun s => s.applyDrawTo cA (Sum.inl Anchor.p1)).isSome
#eval (stX.applyDrawTo cA (Sum.inl Anchor.p1) >>= fun s => s.applyDrawTo cC (Sum.inl Anchor.p0)).isSome
#eval (stX.applyDrawTo cC (Sum.inl Anchor.p0) >>= fun s => s.applyDrawTo cA (Sum.inl Anchor.p1)).map fun s => s.stock.cursor
#eval (stX.applyDrawTo cA (Sum.inl Anchor.p1) >>= fun s => s.applyDrawTo cC (Sum.inl Anchor.p0)).map fun s => s.stock.cursor
#eval (stX.applyDrawTo cC (Sum.inl Anchor.p0) >>= fun s => s.applyDrawTo cA (Sum.inl Anchor.p1)).map fun s => s.stock.cards.length
#eval (stX.applyDrawTo cA (Sum.inl Anchor.p1) >>= fun s => s.applyDrawTo cC (Sum.inl Anchor.p0)).map fun s => s.stock.cards.length
