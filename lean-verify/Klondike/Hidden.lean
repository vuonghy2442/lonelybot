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
  h.nHidden.toList.reverse.foldl (fun res n => res * (n + 2)) 0

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

end Hidden

end Klondike
