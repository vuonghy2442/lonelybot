/-
Klondike.Encode — State encoding for cross-validation with Rust.

The 61-bit encoding (16 stack + 16 hidden + 29 deck) must match
exactly what the Rust code produces. This file defines the encoding
and provides a way to extract it for comparison.

Testing strategy:
1. Run the Rust solver on a seed, dumping (encode, move) pairs
2. Run the Lean implementation on the same seed
3. Compare that both visit the same set of encoded states
4. If they agree on all states, the implementations are equivalent
-/

namespace Klondike

namespace Solitaire

/--
The full 61-bit encoding, matching `Solitaire::encode()` in Rust.

Format:
- Bits 0-15:  Stack.encode (16 bits)
- Bits 16-31: Hidden.encode (16 bits)
- Bits 32-60: Deck.encode (29 bits)
- Bit 61:     unused

This must match the Rust encoding exactly for cross-validation.
-/
def encode61 (s : Solitaire) : Nat :=
  Stack.encode s.finalStack
  ||| (Hidden.encode s.hidden <<< 16)
  ||| (Deck.encode s.deck <<< 32)

/--
Decode from 61-bit encoding.
-/
def decode61 (n : Nat) : Solitaire :=
  let stackBits := n &&& 0xFFFF
  let hiddenBits := (n >>> 16) &&& 0xFFFF
  let deckBits := n >>> 32
  {
    finalStack := Stack.decode stackBits
    hidden := Hidden.decode hiddenBits
    deck := Deck.decode deckBits
    visibleMask := 0  -- must be recomputed from hidden + deck
  }

/--
Encode and decode are inverse (assuming valid state).
-/
theorem encode_decode_inverse (s : Solitaire) :
    decode61 (encode61 s) = s := by
  sorry

end Solitaire

/--
A trace of the solver: sequence of (encoded_state, move) pairs.
Used for cross-validation with the Rust solver.
-/
def SolverTrace := List (Nat × Move)

/--
Convert a solver trace to a list of encoded states.
-/
def traceStates (t : SolverTrace) : List Nat :=
  t.map Prod.fst

/--
Two traces visit the same set of states.
-/
def tracesAgree (t1 t2 : SolverTrace) : Bool :=
  t1.traceStates.toPFinset = t2.traceStates.toPFinset

end Klondike
