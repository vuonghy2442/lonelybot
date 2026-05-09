import Klondike.Card

namespace Klondike

def swapPair (a : Nat) : Nat :=
  let half := (a &&& HALF_MASK) <<< 2
  ((a >>> 2) &&& HALF_MASK) ||| half

def bottomMask (vis free : Nat) : Nat :=
  let xorFree := free ^^^ (free >>> 1)
  let xorVis := vis ^^^ (vis >>> 1)
  let xorAll := xorVis ^^^ (xorFree <<< 4)
  let orFree := free ||| (free >>> 1)
  let orVis := vis ||| (vis >>> 1)
  ((xorAll ||| fullMask 64 - (orFree <<< 4)) &&& orVis &&& ALT_MASK) * 3

end Klondike
