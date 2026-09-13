import Klondike.Theorems

/-! Witness: `commute_of_disjoint_touch` is FALSE as staged.  `.draw`'s
touch set is ([], []) — disjoint from EVERYTHING — but the deck moves'
legality reads the waste top (cursor-sensitive), which the deal changes:
with a duplicated stock card both orders succeed and land on different
stocks.  stW: stock [cK, h2, cK, h4] cursor 1, step 2, empty board,
cK a king; m = deckPile cK (inl p0), m' = draw.
- Order A (deckPile then draw): removes index 0, deals 2 — stock
  [h2, cK, h4] cursor 2.
- Order B (draw then deckPile): deals 2 (cursor 3), removes index 2 —
  stock [cK, h2, h4] cursor 2. -/

def cK : Card := ⟨Suit.club, Rank.king⟩
def h2 : Card := ⟨Suit.heart, Rank.two⟩
def h4 : Card := ⟨Suit.heart, Rank.four⟩

def stW : State :=
  { deal := ⟨fun _ => [], []⟩,
    board := Board.empty,
    heights := fun _ => 0,
    depths := fun _ => 0,
    stock := ⟨[cK, h2, cK, h4], 1⟩,
    drawStep := 2 }

def wM : Move := Move.deckPile cK (Sum.inl Anchor.p0)

def wComp₁ : Option State :=
  stW.apply wM >>= fun s => s.apply Move.draw
def wComp₂ : Option State :=
  stW.apply Move.draw >>= fun s => s.apply wM

theorem wSome₁ : wComp₁.isSome = true := by decide
theorem wSome₂ : wComp₂.isSome = true := by decide

theorem wCards₁ : Option.map (fun s => s.stock.cards) wComp₁
    = some [h2, cK, h4] := by decide
theorem wCards₂ : Option.map (fun s => s.stock.cards) wComp₂
    = some [cK, h2, h4] := by decide

theorem wDisj : disjointTouch (wM.touch stW) (Move.draw.touch stW) := by
  show (∀ b ∈ [Sum.inl Anchor.p0], b ∉ ([] : List Base)) ∧
       (∀ c ∈ [cK], c ∉ ([] : List Card))
  refine ⟨?_, ?_⟩
  · intro b _ hin; exact nomatch hin
  · intro c _ hin; exact nomatch hin

theorem commute_false : False := by
  have hS1 : wComp₁.isSome = true := by decide
  have hS2 : wComp₂.isSome = true := by decide
  have hC1 : Option.map (fun s => s.stock.cards) wComp₁ = some [h2, cK, h4] := by decide
  have hC2 : Option.map (fun s => s.stock.cards) wComp₂ = some [cK, h2, h4] := by decide
  cases hA : wComp₁ with
  | none =>
      rw [hA] at hS1
      simp at hS1
  | some wA =>
      cases hB : wComp₂ with
      | none =>
          rw [hB] at hS2
          simp at hS2
      | some wB =>
          have heq := commute_of_disjoint_touch wDisj hA hB
          have hc := congrArg (fun s => s.stock.cards) heq
          rw [hA] at hC1
          rw [hB] at hC2
          simp only [Option.map_some, Option.some.injEq] at hC1 hC2
          simp only [] at hc
          rw [hC1, hC2] at hc
          exact absurd hc (by decide)

#print axioms commute_false
