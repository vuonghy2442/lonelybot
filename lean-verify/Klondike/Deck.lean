import Klondike.Card

namespace Klondike

structure Deck where
  cards : Array Card
  drawCur : Nat
  drawStep : Nat
  mask : Nat
  map : Array Nat
  deriving DecidableEq, Repr

namespace Deck

def len (d : Deck) : Nat := d.cards.size
def isEmpty (d : Deck) : Bool := d.cards.isEmpty
def isPure (d : Deck) : Bool := d.drawCur % d.drawStep = 0 || d.drawCur = d.len

def normalizedOffset (d : Deck) : Nat :=
  if d.isPure then d.len else d.drawCur

def encode (d : Deck) : Nat :=
  d.mask ||| (d.normalizedOffset <<< N_DECK_CARDS)

def decode (n : Nat) : Deck :=
  let maskPart := n &&& fullMask N_DECK_CARDS
  let offset := n >>> N_DECK_CARDS
  ⟨#[], offset, 1, maskPart, Array.replicate N_CARDS 0⟩

def computeMask (d : Deck) (filter : Bool) : Nat := sorry

def peekLast (d : Deck) : Option Card := if d.cards.isEmpty then none else d.cards.back?

def peek (d : Deck) (pos : Nat) : Card :=
  if h : pos < d.cards.size then d.cards[pos]'h else Card.default

def getOffset (d : Deck) : Nat := d.drawCur

end Deck

end Klondike
