namespace Klondike.Spec

inductive Suit where
  | hearts | diamonds | clubs | spades
  deriving DecidableEq, Repr, BEq

inductive Color where
  | red | black
  deriving DecidableEq, Repr

def Suit.color : Suit → Color
  | .hearts | .diamonds => .red
  | .clubs | .spades => .black

def Suit.swapSuit : Suit → Suit
  | .hearts => .diamonds | .diamonds => .hearts
  | .clubs => .spades | .spades => .clubs

theorem Suit.swapSuit_involution (s : Suit) : s.swapSuit.swapSuit = s := by cases s <;> rfl
theorem Suit.swapSuit_same_color (s : Suit) : s.swapSuit.color = s.color := by cases s <;> rfl

abbrev Rank := Fin 13

structure Card where
  rank : Rank
  suit : Suit
  deriving DecidableEq, Repr, BEq

namespace Card

def color (c : Card) : Color := c.suit.color
def isKing (c : Card) : Bool := c.rank = 12
def swapSuit (c : Card) : Card := { c with suit := c.suit.swapSuit }
def goesOnTopOf (c c' : Card) : Prop := c.rank + 1 = c'.rank ∧ c.color ≠ c'.color

theorem swapSuit_preserves_rank (c : Card) : c.swapSuit.rank = c.rank := rfl
theorem swapSuit_preserves_color (c : Card) : c.swapSuit.color = c.color := Suit.swapSuit_same_color c.suit
theorem swapSuit_involution (c : Card) : c.swapSuit.swapSuit = c := by simp [swapSuit, Suit.swapSuit_involution]

end Card

end Klondike.Spec
