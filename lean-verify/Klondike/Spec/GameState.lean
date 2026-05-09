/-
Klondike.State — Game state representation.

This file defines the Klondike Solitaire game state in a form suitable
for formal reasoning about move pruning. We use explicit per-pile card
lists (matching the "StandardSolitaire" representation from the Rust code)
rather than the bitmask representation, since correctness is about the
game rules, not the encoding.

A game state consists of:
- 7 tableau piles, each with hidden (face-down) and visible (face-up) cards
- 4 foundation stacks (one per suit)
- A stock/waste pile (the deck)
- A draw step (1 or 3)
-/

namespace Klondike

open Basic

/-- A non-empty list of face-up cards in a tableau pile.
    The head is the top (most recently played) card. -/
abbrev Pile := List Card

/-- The hidden (face-down) cards in a tableau pile.
    The head is the topmost hidden card (closest to face-up). -/
abbrev HiddenCards := List Card

/-- A tableau pile has hidden cards (face-down) and visible cards (face-up). -/
structure TableauPile where
  hidden : HiddenCards
  visible : Pile
  deriving DecidableEq, Repr

/-- Foundation rank per suit: how many cards have been stacked (0 = none). -/
abbrev Foundation := Suit → Fin 14

/-- The deck: a list of cards with a current position for dealing.
    `stock` is the undealt portion, `waste` is the dealt-but-playable portion.
    In draw-N mode, N cards are dealt at a time. -/
structure Deck where
  stock : List Card
  waste : List Card
  drawStep : Fin 14  -- 1 or 3 (stored as Nat for generality)
  deriving DecidableEq, Repr

/-- The full Klondike game state. -/
structure GameState where
  piles : Fin 7 → TableauPile
  foundation : Foundation
  deck : Deck
  deriving DecidableEq, Repr

namespace GameState

/-- The top card of a tableau pile (if any). -/
def pileTop (s : GameState) (i : Fin 7) : Option Card :=
  (s.piles i).visible.head?

/-- Whether a pile is empty (no visible cards). -/
def pileIsEmpty (s : GameState) (i : Fin 7) : Bool :=
  (s.piles i).visible.isEmpty

/-- The foundation rank for a given suit. -/
def foundationRank (s : GameState) (suit : Suit) : Option Rank :=
  let r := s.foundation suit
  if r = 0 then none
  else some ⟨r - 1, by omega⟩

/-- Whether a card can be moved to the foundation. -/
def canMoveToFoundation (s : GameState) (c : Card) : Bool :=
  c.canStackTo (s.foundationRank ·)

/-- Whether card c can be placed on top of pile i.
    If the pile is empty, only Kings can go there.
    If non-empty, c must go on top of the current top card. -/
def canMoveToPile (s : GameState) (i : Fin 7) (c : Card) : Bool :=
  match s.piles i with
  | ⟨_, []⟩    => c.isKing
  | ⟨_, t :: _⟩ => c.goesOnTopOf t

/-- Find which pile a visible card is on top of (if any). -/
def findCardPile (s : GameState) (c : Card) : Option (Fin 7) :=
  List.finFind? 7 fun i =>
    match s.piles i with
    | ⟨_, []⟩    => false
    | ⟨_, t :: _⟩ => t = c

/-- A card is "locked" if it has hidden cards underneath it in its pile.
    (Revealing these hidden cards is one of the goals.) -/
def isLockedCard (s : GameState) (c : Card) : Bool :=
  List.finFind? 7 fun i =>
    match s.piles i with
    | ⟨h, t :: _⟩ => t = c && !h.isEmpty
    | _ => false
  |>.isSome

/-- The first-layer hidden cards: the topmost hidden card in each pile. -/
def firstLayerHidden (s : GameState) : List Card :=
  List.finRange 7 |>.filterMap fun i =>
    match s.piles i with
    | ⟨h :: _, _⟩ => some h
    | _ => none

/-- Check if the game is won: all 4 foundations are full (rank 13). -/
def isWin (s : GameState) : Bool :=
  ∀ suit : Suit, s.foundation suit = 13

end GameState

end Klondike
