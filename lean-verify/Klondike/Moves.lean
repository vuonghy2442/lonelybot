/-
Klondike.Moves — Move type and MoveMask, matching src/moves.rs.

The 5 move types and their bitmask representation for efficient
move generation, filtering, and combination.
-/

namespace Klondike

/--
The five move types, matching `Move` enum in src/moves.rs.

- DeckStack(c): Move card c from stock to foundation
- PileStack(c): Move card c from tableau to foundation
- DeckPile(c):  Move card c from stock to tableau
- StackPile(c): Move card c from foundation to tableau
- Reveal(c):    Move top card c from one pile to another, revealing hidden card
-/
inductive Move where
  | deckStack : Card → Move
  | pileStack : Card → Move
  | deckPile  : Card → Move
  | stackPile : Card → Move
  | reveal    : Card → Move
  deriving DecidableEq, Repr

namespace Move

/-- Get the card involved in a move. -/
def card : Move → Card
  | deckStack c | pileStack c | deckPile c | stackPile c | reveal c => c

/-- Maximum number of moves from any state. -/
abbrev N_MOVES_MAX : Nat := 24

end Move

/--
Move mask: 5 bitmasks representing the set of available moves.
Matches `MoveMask` in src/moves.rs.

Each field is a u64 bitmask where each set bit corresponds to a card
that can be the subject of that move type.
-/
structure MoveMask where
  pileStack : Nat  -- bitmask of PileStack-able cards
  deckStack : Nat  -- bitmask of DeckStack-able cards
  stackPile  : Nat  -- bitmask of StackPile-able cards
  deckPile   : Nat  -- bitmask of DeckPile-able cards
  reveal     : Nat  -- bitmask of Reveal-able cards
  deriving DecidableEq, Repr

namespace MoveMask

/-- Empty move mask (no moves). -/
def empty : MoveMask := ⟨0, 0, 0, 0, 0⟩

/-- Count total number of moves in the mask. -/
def len (m : MoveMask) : Nat :=
  m.pileStack.popCount + m.deckStack.popCount + m.stackPile.popCount
  + m.deckPile.popCount + m.reveal.popCount

/-- Whether the mask is empty (no moves). -/
def isEmpty (m : MoveMask) : Bool := m = empty

/-- Filter out (remove) moves present in another mask. -/
def filter (m remove : MoveMask) : MoveMask :=
  ⟨m.pileStack &&& ~~~ remove.pileStack,
   m.deckStack &&& ~~~ remove.deckStack,
   m.stackPile  &&& ~~~ remove.stackPile,
   m.deckPile   &&& ~~~ remove.deckPile,
   m.reveal     &&& ~~~ remove.reveal⟩

/-- Combine (union) two move masks. -/
def combine (m other : MoveMask) : MoveMask :=
  ⟨m.pileStack ||| other.pileStack,
   m.deckStack ||| other.deckStack,
   m.stackPile  ||| other.stackPile,
   m.deckPile   ||| other.deckPile,
   m.reveal     ||| other.reveal⟩

/-- Create a MoveMask from a single move. -/
def fromMove : Move → MoveMask
  | Move.deckStack c => ⟨0, 1 <<< c.val, 0, 0, 0⟩
  | Move.pileStack c => ⟨1 <<< c.val, 0, 0, 0, 0⟩
  | Move.deckPile c  => ⟨0, 0, 0, 1 <<< c.val, 0⟩
  | Move.stackPile c  => ⟨0, 0, 1 <<< c.val, 0, 0⟩
  | Move.reveal c     => ⟨0, 0, 0, 0, 1 <<< c.val⟩

end MoveMask

end Klondike
