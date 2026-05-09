import Klondike.Card

namespace Klondike

structure Stack where
  val : Nat
  deriving DecidableEq, Repr

namespace Stack

def empty : Stack := ⟨0⟩
def get (s : Stack) (suit : Nat) : Nat := (s.val >>> (4 * suit)) &&& 0xF
def push (s : Stack) (suit : Nat) : Stack := ⟨s.val + (1 <<< (4 * suit))⟩
def pop (s : Stack) (suit : Nat) : Stack :=
  if s.get suit > 0 then ⟨s.val - (1 <<< (4 * suit))⟩ else s
def isFull (s : Stack) : Bool := s.val = (N_RANKS * 0x1111)
def isEmpty (s : Stack) : Bool := s.val = 0
def len (s : Stack) : Nat := s.get 0 + s.get 1 + s.get 2 + s.get 3

def mask (s : Stack) : Nat :=
  (SUIT_MASK[0]! &&& (0xF <<< (s.get 0 * 4)))
  ||| (SUIT_MASK[1]! &&& (0xF <<< (s.get 1 * 4)))
  ||| (SUIT_MASK[2]! &&& (0xF <<< (s.get 2 * 4)))
  ||| (SUIT_MASK[3]! &&& (0xF <<< (s.get 3 * 4)))

def dominanceMask (s : Stack) : Nat :=
  let dRed := min (s.get 0) (s.get 1)
  let dBlack := min (s.get 2) (s.get 3)
  let d0 := min (dRed + 1) dBlack + 2
  let d1 := min dRed (dBlack + 1) + 2
  (COLOR_MASK[0]! &&& fullMask (d0 * 4)) ||| (COLOR_MASK[1]! &&& fullMask (d1 * 4))

def isValid (s : Stack) : Bool :=
  s.get 0 ≤ N_RANKS && s.get 1 ≤ N_RANKS && s.get 2 ≤ N_RANKS && s.get 3 ≤ N_RANKS

def encode (s : Stack) : Nat := s.val
def decode (n : Nat) : Stack := ⟨n⟩

end Stack

end Klondike
