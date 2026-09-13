import Klondike.Initial

/-!
# `apply_wf` witness #5 — the membership conjunct does not subsume noDup

WF's membership conjunct (`∀ c ∈ st.stock.cards, c ∈ st.deal.stock`,
added for witness #4) sees *where* stock cards come from, not *how many
times*: a state stock listing a deal-stock card TWICE satisfies it.
`deckPile` splices out one copy and turns the card visible — the second
copy stays in the cycle, breaking `isVis → posOf = none`.  Witness
`st5`: standard deal, depths 1, board {inr ♠3 ↦ ♠4} (deal-adjacent
edge of pile p5), stock ⟨[♢3, ♢3], 2⟩; `deckPile ♢3 (inr ♠4)` was
legal and the successor had ♢3 visible with `posOf ♢3 = some 0`.

The repair (2026-09-13): `noDupCards st.stock.cards` was RESTORED in
addition to membership (both conjuncts are needed — neither subsumes
the other), and `apply_wf` is PROVEN.  The old
`apply_wf_unsound_dup_stock : False` theorem is now a false statement
and has been removed.  What remains is the positive regression: the
duplicated-cycle state is rejected outright by `stock_wf`'s noDup half
(`st5_not_wf`).
-/

/-- ♠3: pile p5's bottom card. -/
def s3 : Card := ⟨Suit.spade, Rank.three⟩

/-- ♠4: dealt directly on ♠3. -/
def s4 : Card := ⟨Suit.spade, Rank.four⟩

def s5c : Card := ⟨Suit.spade, Rank.five⟩
def s6c : Card := ⟨Suit.spade, Rank.six⟩
def s7c : Card := ⟨Suit.spade, Rank.seven⟩
def s8c : Card := ⟨Suit.spade, Rank.eight⟩

/-- ♢3: a deal-stock card. -/
def d3 : Card := ⟨Suit.diamond, Rank.three⟩

/-- ♠4 visible, sitting on its dealt parent ♠3. -/
def bd5 : Board where
  topOf := Board.update Board.empty.topOf (Sum.inr s3) (some s4)
  inj := Board.attach_inj Board.empty (Sum.inr s3) s4 (Board.empty_bottomOf s4)

/-- The old witness: the stock lists ♢3 twice (membership holds). -/
def st5 : State where
  deal := Deal.standard
  board := bd5
  heights := fun _ => 0
  depths := fun _ => 1
  stock := ⟨[d3, d3], 2⟩
  drawStep := 1

/-- The deckPile successor (computed by the kernel; kept as the
countermodel record). -/
def st51 : State := (st5.apply (Move.deckPile d3 (Sum.inr s4))).getD st5

theorem st5_topOf_self : st5.board.topOf (Sum.inr s3) = some s4 :=
  Board.update_self Board.empty.topOf (Sum.inr s3) (some s4)

theorem st5_topOf_ne {b : Base} (h : b ≠ Sum.inr s3) : st5.board.topOf b = none :=
  (Board.update_ne Board.empty.topOf (Sum.inr s3) b (some s4) h).trans (Board.empty_topOf b)

/-- KILLED BY THE `noDupCards` RESTORATION: the duplicated cycle is
rejected outright — a duplicated ♢3 fails the noDup half of `stock_wf`
even though the membership half holds (♢3 is a deal-stock card). -/
theorem st5_not_wf : ¬ st5.WF := by
  intro hwf
  have hnd : noDupCards [d3, d3] := hwf.stock_wf.1
  exact absurd (hnd 0 1 (by decide) (by decide) rfl) (by decide)

/-- The countermodel's premise still holds (by the kernel) — only the
WF side of the old refutation is gone. -/
example : (st5.apply (Move.deckPile d3 (Sum.inr s4))).isSome = true := by decide

/-- info: 'st5_not_wf' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms st5_not_wf
