import Klondike.Card

namespace Klondike

structure Hidden where
  hiddenPiles : Array Card
  nHidden : Array Nat
  pileMap : Array Nat
  firstLayerMask : Nat
  lockedMask : Nat
  deriving DecidableEq, Repr

namespace Hidden

def getLockedMask (h : Hidden) : Nat := h.lockedMask
def getFirstLayerMask (h : Hidden) : Nat := h.firstLayerMask
def isAllUp (h : Hidden) : Bool := h.lockedMask = 0

def totalDownCards (h : Hidden) : Nat :=
  (h.nHidden.map fun n => if n ≤ 1 then 0 else n - 1).sum

def encode (h : Hidden) : Nat :=
  let rec go (acc : Nat) (idx : Nat) : List Nat → Nat
    | [] => acc
    | n :: ns => go (acc * (idx + 2) + n) (idx - 1) ns
  go 0 (N_PILES - 1) h.nHidden.toList.reverse

def decode (n : Nat) : Hidden :=
  let rec go (i : Nat) (acc : Nat) : Array Nat × Nat :=
    if i ≥ N_PILES then (Array.replicate N_PILES 0, acc)
    else
      let nOpts := i + 2
      let nh := acc % nOpts
      let rest := go (i + 1) (acc / nOpts)
      (rest.1.set! i nh, rest.2)
  let pair := go 0 n
  ⟨Array.replicate N_PILE_CARDS Card.default, pair.1, Array.replicate N_CARDS 0, 0, 0⟩

def isValid (h : Hidden) : Bool :=
  h.nHidden.all (fun n => n ≤ N_RANKS)

def find (h : Hidden) (c : Card) : Nat :=
  if c.maskIndex < h.pileMap.size then h.pileMap[c.maskIndex]! else 0

def peek (h : Hidden) (pos : Nat) : Option Card :=
  let nh := if pos < h.nHidden.size then h.nHidden[pos]! else 0
  let start := pos * (pos + 1) / 2
  let endIdx := start + nh
  if endIdx > 0 && endIdx ≤ h.hiddenPiles.size then
    h.hiddenPiles[endIdx - 1]?
  else none

def popCard (h : Hidden) (c : Card) : Hidden × Option Card :=
  let pos := h.find c
  let nh := if pos < h.nHidden.size then h.nHidden[pos]! else 0
  let newNHidden := if pos < h.nHidden.size then h.nHidden.set! pos (nh - 1) else h.nHidden
  let newLockedMask := h.lockedMask &&& Nat.complement64 (Card.mask c)
  let revealed := h.peek pos
  let newHidden : Hidden := ⟨h.hiddenPiles, newNHidden, h.pileMap, h.firstLayerMask, newLockedMask⟩
  (newHidden, revealed)

def unpopCard (h : Hidden) (c : Card) : Option Card → Hidden :=
  fun revealed =>
    let pos := h.find c
    let nh := if pos < h.nHidden.size then h.nHidden[pos]! else 0
    let newNHidden := if pos < h.nHidden.size then h.nHidden.set! pos (nh + 1) else h.nHidden
    let newLockedMask := h.lockedMask ||| Card.mask c
    match revealed with
    | some rc => ⟨h.hiddenPiles, newNHidden, h.pileMap, h.firstLayerMask, newLockedMask⟩
    | none => ⟨h.hiddenPiles, newNHidden, h.pileMap, h.firstLayerMask, newLockedMask⟩

end Hidden

end Klondike
