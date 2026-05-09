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
def peekLast (d : Deck) : Option Card := if d.cards.isEmpty then none else d.cards.back?
def peek (d : Deck) (pos : Nat) : Card :=
  if h : pos < d.cards.size then d.cards[pos]'h else Card.default
def getOffset (d : Deck) : Nat := d.drawCur

def normalizedOffset (d : Deck) : Nat :=
  if d.isPure then d.len else d.drawCur

def encode (d : Deck) : Nat :=
  d.mask ||| (d.normalizedOffset <<< N_DECK_CARDS)

def decode (n : Nat) : Deck :=
  let maskPart := n &&& fullMask N_DECK_CARDS
  let offset := n >>> N_DECK_CARDS
  ⟨#[], offset, 1, maskPart, Array.replicate N_CARDS 0⟩

private def maskOfIdx (d : Deck) : List Nat → Nat
  | [] => 0
  | i :: is => Card.mask (d.peek i) ||| d.maskOfIdx is

def computeMask (d : Deck) (filter : Bool) : Nat :=
  let step := if d.drawStep = 0 then 1 else d.drawStep
  let wasteStart := d.drawCur + (if d.drawCur = 0 then step else 0) - 1
  let wasteLimit := if d.len ≤ 1 then 0 else d.len - 1
  let wasteIdxs := List.range' wasteStart wasteLimit step
  let lastIdxs := if d.cards.isEmpty then [] else [d.len - 1]
  let deckIdxs :=
    if filter then [] else
      let offset := d.drawCur % step
      let endIdx := if offset ≠ 0 then d.len else d.drawCur
      let deckLimit := if endIdx ≤ 1 then 0 else endIdx - 1
      let start := if step ≤ 1 then 0 else step - 1
      List.range' start deckLimit step
  d.maskOfIdx (wasteIdxs ++ lastIdxs ++ deckIdxs)

end Deck

end Klondike
