/-
Klondike.SuitSymmetry — The suit-swap invariance theorem.

Main Theorem: For any rank r and color C, if both cards (r, suit₀) and
(r, suit₁) are not yet on the foundation, then swapping them throughout
the game state preserves solvability.

This is proved using the XOR encoding: swapSuit = XOR 1, which
exchanges the two suits within a color pair while preserving rank
and color (and hence the "goes on top of" relation).

The key lemma is that swapSuit preserves goesOnTopOf:
  c.goesOnTopOf c'  ⟹  c.swapSuit.goesOnTopOf c'.swapSuit
-/

namespace Klondike

/--
swapSuit (XOR 1) preserves the goesOnTopOf relation.

Proof: goesOnTopOf checks ((c + 4) ^^^ c') < 2.
Since swapSuit = XOR 1, we have:
  ((c ⊕ 1 + 4) ^^^ (c' ⊕ 1))
  = ((c + 4) ⊕ 1 ^^^ (c' ⊕ 1))   [since +4 and XOR 1 commute]
  = ((c + 4) ^^^ c') ⊕ (1 ^^^ 1)  [XOR distributes]
  = (c + 4) ^^^ c'                  [1 ^^^ 1 = 0]
  < 2                                [by assumption]

So the relation is preserved.
-/
theorem swapSuit_preserves_goesOnTopOf (c c' : Card)
    (h : Card.goesOnTopOf c c') :
    Card.goesOnTopOf c.swapSuit c'.swapSuit := by
  simp [Card.goesOnTopOf, Card.swapSuit] at *
  -- ((c + 4) ^^^ c') < 2 implies ((c ⊕ 1 + 4) ^^^ (c' ⊕ 1)) < 2
  -- Need: ((c.val + 4) ^^^ c'.val) < 2 → ((c.val ^^^ 1 + 4) ^^^ (c'.val ^^^ 1)) < 2
  -- Since +4 doesn't change the low 2 bits: (c + 4) ⊕ 1 = (c ⊕ 1) + 4
  -- So (c⊕1 + 4) ⊕⊕ (c'⊕1) = (c+4)⊕1 ⊕⊕ (c'⊕1) = (c+4) ⊕⊕ c'
  sorry  -- TODO: bit-level reasoning

/--
If both cards of rank r and color C have not been stacked to the
foundation past rank r, then swapping them (swapSuit) preserves
the canStackTo predicate.

This is because:
- canStackTo checks f(suit) = rank
- If f(suit₀) ≤ r and f(suit₁) ≤ r, then swapping f(suit₀) and f(suit₁)
  preserves the canStackTo predicate for rank r
  (since both suits allow stacking at rank r or below)
-/
theorem swapSuit_preserves_canStackTo (c : Card) (f : Fin N_SUITS → Nat)
    (h : f c.suit ≤ c.rank.val + 1) (h_swap : f c.swapSuit.suit ≤ c.swapSuit.rank.val + 1) :
    Card.canStackTo c f ↔ Card.canStackTo c.swapSuit (fun s => if s = c.swapSuit.suit then f c.suit else if s = c.suit then f c.swapSuit.suit else f s) := by
  sorry

/--
THE MAIN THEOREM: Suit symmetry preserves solvability.

If both cards of rank r and color C are not yet on the foundation
(foundation(suit₀) ≤ r and foundation(suit₁) ≤ r), then swapping
them throughout the game state preserves solvability.

Proof strategy:
1. swapSuit preserves goesOnTopOf (the tableau stacking relation)
2. swapSuit preserves canStackTo under the foundation constraint
3. Therefore, any winning path can be "swapped" to produce another
   winning path in the swapped state
4. Since swapSuit is an involution, the converse also holds
-/
theorem suit_symmetry_preserves_solvability (s : Solitaire) (c : Card)
    (h_foundation : s.finalStack.get c.suit ≤ c.rank.val + 1)
    (h_foundation_swap : s.finalStack.get c.swapSuit.suit ≤ c.swapSuit.rank.val + 1) :
    Solvable s ↔ Solvable (swapState s c) := by
  sorry

where
  /-- Swap card c and c.swapSuit throughout the game state. -/
  swapState (s : Solitaire) (c : Card) : Solitaire :=
    { s with
      finalStack := swapFoundation s.finalStack c
      visibleMask := swapBits s.visibleMask c
      hidden := swapHidden s.hidden c
      deck := swapDeck s.deck c }

  swapFoundation (f : Stack) (c : Card) : Stack :=
    let v0 := f.get c.suit
    let v1 := f.get c.swapSuit.suit
    let f' := if v0 > 0 then f.pop c.suit else f
    let f' := if v1 > 0 then f'.pop c.swapSuit.suit else f'
    let f' := if v0 > 0 then f'.push c.swapSuit.suit else f'
    let f' := if v1 > 0 then f'.push c.suit else f'
    f'

  swapBits (mask : Nat) (c : Card) : Nat :=
    let bit0 := 1 <<< c.val
    let bit1 := 1 <<< c.swapSuit.val
    let has0 := mask &&& bit0
    let has1 := mask &&& bit1
    let mask' := mask &&& ~~~bit0 &&& ~~~bit1
    if has0 > 0 then mask' ||| bit1
    else if has1 > 0 then mask' ||| bit0
    else mask'

  swapHidden (h : Hidden) (c : Card) : Hidden := h  -- TODO
  swapDeck (d : Deck) (c : Card) : Deck := d  -- TODO

/--
Corollary: paired_stack soundness.
When both c and c.swapSuit are stackable, PileStack c dominates
PileStack c.swapSuit (by suit symmetry).
-/
theorem paired_stack_sound (s : Solitaire) (c : Card)
    (h_both : c ∈ (genMoves true s).pileStack ∧ c.swapSuit ∈ (genMoves false s).pileStack) :
    Dominates s (Move.pileStack c) (Move.pileStack c.swapSuit) := by
  sorry

/--
A move m dominates m' if for every winning path through m',
there's a winning path through m.
-/
def Dominates (s : Solitaire) (m m' : Move) : Prop :=
  ∀ s' s'', (s.doMove m').2.2 = s' → (s.doMove m).2.2 = s'' →
    Solvable s' → Solvable s''

end Klondike
