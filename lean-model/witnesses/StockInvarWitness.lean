import Klondike.Theorems

/-! Witness: `apply_nonConsuming_stock_invar` is FALSE for `m = Move.draw`
(draw is non-consuming — `consumesStock = false` — but `applyDraw` writes the
stock cursor).  From cursor 0 with a nonempty stock and step 1, the deal lands
the cursor at 1, so the successor's stock differs from the source's. -/

def wCard1 : Card := ⟨Suit.heart, Rank.two⟩
def wCard2 : Card := ⟨Suit.spade, Rank.three⟩

def wSt : State :=
  { deal := ⟨fun _ => [], []⟩,
    board := Board.empty,
    heights := fun _ => 0,
    depths := fun _ => 0,
    stock := ⟨[wCard1, wCard2], 0⟩,
    drawStep := 1 }

theorem wDraw : wSt.apply Move.draw
    = some { wSt with stock := ⟨[wCard1, wCard2], 1⟩ } := rfl

theorem wNe : ¬ ({ wSt with stock := ⟨[wCard1, wCard2], 1⟩ } : State).stock = wSt.stock := by
  intro heq
  have hc := congrArg Cycle.cursor heq
  simp only [wSt] at hc
  omega

theorem stock_invar_false : False := by
  have h := apply_nonConsuming_stock_invar (m := Move.draw) rfl wDraw
  exact wNe h

#print axioms stock_invar_false
