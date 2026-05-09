/-
Klondike.Stack — Foundation stack representation, matching src/stack.rs.

The Stack is a compact u16 encoding: 4 bits per suit, value = rank count.
Stack.push(suit) increments the 4-bit field for that suit.
Stack.pop(suit) decrements it.
Stack.mask() computes the bitmask of next-stackable cards.
Stack.dominance_mask() computes the safe-to-auto-stack mask.
Stack.encode() / Stack.decode() for serialization.
-/

namespace Klondike

/--
Foundation stack: 4 bits per suit (values 0..13), packed into a Nat.
Matches `Stack(u16)` in Rust.
-/
def Stack := Nat

namespace Stack

/-- The empty stack. -/
def empty : Stack := 0

/-- Get the foundation rank for a suit (0..13). -/
def get (s : Stack) (suit : Nat) : Nat :=
  (s >>> (4 * suit)) &&& 0xF

/-- Push a card of the given suit onto the foundation. -/
def push (s : Stack) (suit : Nat) : Stack :=
  s + (1 <<< (4 * suit))

/-- Pop a card of the given suit from the foundation. -/
def pop (s : Stack) (suit : Nat) : Stack :=
  s - (1 <<< (4 * suit))

/-- Whether the foundation is full (all suits at rank 13). -/
def isFull (s : Stack) : Bool :=
  s = (N_RANKS * 0x1111)

/-- Whether the foundation is empty. -/
def isEmpty (s : Stack) : Bool :=
  s = 0

/-- Compute the bitmask of cards that can be stacked next.
    For each suit, the next card has rank = get(suit) at the suit's bit positions.
    Matches `Stack::mask()` in src/stack.rs:16-23. -/
def mask (s : Stack) : Nat :=
  let s0 := s.get 0
  let s1 := s.get 1
  let s2 := s.get 2
  let s3 := s.get 3
  (SUIT_MASK ⟨0, by omega⟩ &&& (0xF <<< (s0 * 4)))
  ||| (SUIT_MASK ⟨1, by omega⟩ &&& (0xF <<< (s1 * 4)))
  ||| (SUIT_MASK ⟨2, by omega⟩ &&& (0xF <<< (s2 * 4)))
  ||| (SUIT_MASK ⟨3, by omega⟩ &&& (0xF <<< (s3 * 4)))

/-- Compute the dominance mask: cards that are safe to auto-stack.
    Uses `min` within each color pair.
    Matches `Stack::dominance_mask()` in src/stack.rs:26-31.

    dominance_mask = (COLOR_MASK[0] & full_mask(d0 * 4))
                   | (COLOR_MASK[1] & full_mask(d1 * 4))
    where d0 = min(min(s0, s1) + 1, s2) + 2  -- red vs black min
          d1 = min(min(s0, s1), s2 + 1) + 2   -- black vs red min

    Wait, looking at the Rust more carefully:
      let d = (min(s[0], s[1]), min(s[2], s[3]));
      let d = (min(d.0 + 1, d.1) + 2, min(d.0, d.1 + 1) + 2);

    So:
      d_red = min(s_hearts, s_diamonds)
      d_black = min(s_clubs, s_spades)
      d0 = min(d_red + 1, d_black) + 2
      d1 = min(d_red, d_black + 1) + 2

    This computes: for each color, the maximum rank where auto-stacking
    is safe (because both suits of that color are at least that high,
    AND the other color's minimum is also sufficient for the card to
    be useful on the tableau).
-/
def dominanceMask (s : Stack) : Nat :=
  let s0 := s.get 0
  let s1 := s.get 1
  let s2 := s.get 2
  let s3 := s.get 3
  let dRed := min s0 s1
  let dBlack := min s2 s3
  let d0 := min (dRed + 1) dBlack + 2
  let d1 := min dRed (dBlack + 1) + 2
  (COLOR_MASK[0]! &&& fullMask (d0 * 4))
  ||| (COLOR_MASK[1]! &&& fullMask (d1 * 4))
where
  fullMask (i : Nat) : Nat := (1 <<< i) - 1

/-- Encode the stack as a u16. -/
def encode (s : Stack) : Nat := s

/-- Decode a u16 as a stack. -/
def decode (n : Nat) : Stack := n

theorem push_get_same (s : Stack) (suit : Nat) (h : suit < N_SUITS) :
    (s.push suit).get suit = s.get suit + 1 := by
  simp [push, get]
  omega

theorem pop_get_same (s : Stack) (suit : Nat) (h : s.get suit > 0) :
    (s.pop suit).get suit = s.get suit - 1 := by
  simp [pop, get]
  omega

end Stack

end Klondike
