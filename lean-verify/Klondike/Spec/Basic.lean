/-
Klondike.Basic — Card, Suit, Rank, and color definitions.

This file defines the fundamental types for Klondike Solitaire:
- Suit (Hearts, Diamonds, Clubs, Spades)
- Rank (Ace through King)
- Card (a Rank + Suit pair)
- Color (Red / Black) and the alternation property
- The "goes on top of" relation for tableau stacking

The XOR encoding from the Rust implementation is abstracted away;
we work with the mathematical structure directly.
-/

namespace Klondike

/-- The four suits, grouped by color. Hearts/Diamonds are red, Clubs/Spades are black. -/
inductive Suit where
  | hearts   : Suit
  | diamonds : Suit
  | clubs    : Suit
  | spades   : Suit
  deriving DecidableEq, Repr, BEq

/-- The color of a suit. -/
def Suit.color : Suit → Color where
  color hearts   := Color.red
  color diamonds := Color.red
  color clubs    := Color.black
  color spades   := Color.black

/-- Swap to the other suit of the same color. -/
def Suit.swapSuit : Suit → Suit
  | hearts   => diamonds
  | diamonds => hearts
  | clubs    => spades
  | spades   => clubs

theorem Suit.swapSuit_involution (s : Suit) : s.swapSuit.swapSuit = s := by
  cases s <;> rfl

theorem Suit.swapSuit_same_color (s : Suit) : s.swapSuit.color = s.color := by
  cases s <;> rfl

/-- Card ranks: Ace = 0, 2 = 1, ..., King = 12 -/
abbrev Rank := Fin 13

namespace Rank
def ace : Rank := 0
def two : Rank := 1
def king : Rank := 12

instance : OfNat Rank n where
  ofNat := ⟨n, by omega⟩

/-- A rank is the predecessor of another if they differ by 1. -/
def predOf (r r' : Rank) : Prop := r' = r + 1
end Rank

/-- A card is a rank and a suit. -/
structure Card where
  rank : Rank
  suit : Suit
  deriving DecidableEq, Repr, BEq

namespace Card

/-- The color of a card is determined by its suit. -/
def color (c : Card) : Color := c.suit.color

/-- Two cards have opposite colors. -/
def oppositeColor (c₁ c₂ : Card) : Bool :=
  c₁.color ≠ c₂.color

/-- Card c can be placed on top of card c' in the tableau:
    c has rank one less than c' and opposite color. -/
def goesOnTopOf (c c' : Card) : Prop :=
  c.rank + 1 = c'.rank ∧ c.color ≠ c'.color

/-- A card can go to the foundation on top of the given foundation rank for its suit,
    or directly if it's an Ace. -/
def canStackTo (c : Card) (foundationRank : Suit → Option Rank) : Prop :=
  match foundationRank c.suit with
  | some r => c.rank = r + 1
  | none   => c.rank = 0

/-- A card is a King. -/
def isKing (c : Card) : Bool := c.rank = 12

/-- Swap to the same-color alternate suit. -/
def swapSuit (c : Card) : Card := { c with suit := c.suit.swapSuit }

theorem swapSuit_preserves_rank (c : Card) : (c.swapSuit).rank = c.rank := rfl

theorem swapSuit_preserves_color (c : Card) : (c.swapSuit).color = c.color :=
  Suit.swapSuit_same_color c.suit

theorem swapSuit_involution (c : Card) : c.swapSuit.swapSuit = c := by
  simp [swapSuit, Suit.swapSuit_involution]

/-- If c goes on top of c', then c.swapSuit also goes on top of c'
    (since it has the same rank and same color = opposite to c'). -/
theorem goesOnTopOf_swapSuit_left {c c' : Card} (h : c.goesOnTopOf c') :
    c.swapSuit.goesOnTopOf c' := by
  obtain ⟨hr, hc⟩ := h
  constructor
  · rw [swapSuit_preserves_rank]; omega
  · rw [swapSuit_preserves_color]; exact hc

end Card

end Klondike
