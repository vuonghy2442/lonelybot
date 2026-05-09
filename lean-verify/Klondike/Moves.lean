import Klondike.Card

namespace Klondike

inductive Move where
  | deckStack : Card → Move
  | pileStack : Card → Move
  | deckPile  : Card → Move
  | stackPile : Card → Move
  | reveal    : Card → Move
  deriving DecidableEq, Repr

namespace Move

def card : Move → Card
  | .deckStack c | .pileStack c | .deckPile c | .stackPile c | .reveal c => c

abbrev N_MOVES_MAX : Nat := 24

end Move

structure MoveMask where
  pileStack : Nat
  deckStack : Nat
  stackPile : Nat
  deckPile : Nat
  reveal : Nat
  deriving DecidableEq, Repr

namespace MoveMask

def empty : MoveMask := ⟨0, 0, 0, 0, 0⟩
def len (m : MoveMask) : Nat :=
  (m.pileStack + m.deckStack + m.stackPile + m.deckPile + m.reveal)
def isEmpty (m : MoveMask) : Bool := m = empty

def filter (m remove : MoveMask) : MoveMask :=
  ⟨m.pileStack &&& (fullMask 64 - remove.pileStack),
   m.deckStack &&& (fullMask 64 - remove.deckStack),
   m.stackPile &&& (fullMask 64 - remove.stackPile),
   m.deckPile &&& (fullMask 64 - remove.deckPile),
   m.reveal &&& (fullMask 64 - remove.reveal)⟩

def combine (m other : MoveMask) : MoveMask :=
  ⟨m.pileStack ||| other.pileStack,
   m.deckStack ||| other.deckStack,
   m.stackPile ||| other.stackPile,
   m.deckPile ||| other.deckPile,
   m.reveal ||| other.reveal⟩

end MoveMask

end Klondike
