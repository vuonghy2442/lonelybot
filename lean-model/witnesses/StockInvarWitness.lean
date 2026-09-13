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

/-! ## The refutation (HISTORICAL)

`stock_invar_false : False` (the first version of this file) cited the
pre-repair `apply_nonConsuming_stock_invar (m := Move.draw) rfl wDraw`
— the non-consuming-but-cursor-writing draw is exactly the countermodel
`wDraw` + `wNe` above.  The same-session repair added
`(hm : m ≠ Move.draw)` and the theorem is PROVEN; the old citation no
longer typechecks and has been removed.  The countermodel facts (draw
is non-consuming yet lands the cursor at 1, so the successor's stock
differs) remain, axiom-clean. -/
