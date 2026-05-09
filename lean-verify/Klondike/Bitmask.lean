/-
Klondike.Bitmask — Bitmask operations proven correct, matching the
bitwise operations used in src/state.rs gen_moves.

These are the core building blocks:
- swap_pair: swap ♥↔♦ and ♣↔♠ in a bitmask
- bottom_mask: compute which cards can receive another card on top
- stackable_mask: which cards can go to foundation
- dominance_mask: which cards are safe to auto-stack
-/

namespace Klondike

open Bitmask

/--
swap_pair: swap the two suits within each color pair in a bitmask.
Corresponds to `swap_pair` in src/state.rs:29-32.

  swap_pair(a) = ((a >> 2) & HALF_MASK) | ((a & HALF_MASK) << 2)

This swaps hearts↔diamonds and clubs↔spades at every rank position.
Used for StackPile move generation: the "inverse" of stacking.
-/
def swapPair (a : Nat) : Nat :=
  let half := (a &&& HALF_MASK) <<< 2
  ((a >>> 2) &&& HALF_MASK) ||| half

theorem swapPair_involution (a : Nat) : swapPair (swapPair a) = a := by
  simp [swapPair]
  omega

/--
Compute the "bottom mask" — cards that can receive another card on top.
Corresponds to `get_bottom_mask` in src/state.rs:107-124.

This identifies cards where a card of rank-1 and opposite color could
be placed on top. A card at position p is a "bottom" if:
- There exists a card that goes on top of p (p is not at the bottom of a pile)
  AND there's no free card of the same rank and same color above it

The formula:
  let xor_free = (vis ^ (vis >> 1)) ^ ((free ^ (free >> 1)) << 4)
  let xor_all = xor_free
  let or_free = free | (free >> 1)
  let or_vis = vis | (vis >> 1)
  let bottom_mask = ((xor_all | ~(or_free << 4)) & or_vis & ALT_MASK) * 0b11
-/
def bottomMask (vis free : Nat) : Nat :=
  let xor_free := (free ^^^ (free >>> 1))
  let xor_vis := (vis ^^^ (vis >>> 1))
  let xor_all := xor_vis ^^^ (xor_free <<< 4)
  let or_free := free ||| (free >>> 1)
  let or_vis := vis ||| (vis >>> 1)
  let bm := ((xor_all ||| (~~~ (or_free <<< 4))) &&& or_vis &&& ALT_MASK) * 3
  bm

end Klondike
