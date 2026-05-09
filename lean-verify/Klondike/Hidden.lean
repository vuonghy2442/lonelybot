/-
Klondike.Hidden — Hidden card management, matching src/hidden.rs.

The Hidden structure tracks face-down cards in the 7 tableau piles.
It uses a dense array + reverse map + bitmasks for efficient operations.
Provides:
- pop_card / unpop_card: reveal and undo
- first_layer_mask: bitmask of topmost hidden card per pile
- get_locked_mask: bitmask of all still-hidden cards
- encode/decode: 16-bit mixed-radix serialization
- shuffle: random reassignment for HOP/MCTS
-/

namespace Klondike

/--
Hidden card representation matching `Hidden` in src/hidden.rs.

Fields:
- hidden_piles: flat array of all hidden cards (28 entries)
- n_hidden: count of hidden+top cards per pile
- pile_map: reverse map from card to pile index
- first_layer_mask: bitmask of topmost hidden card per pile
- locked_mask: bitmask of all still-hidden cards
-/
structure Hidden where
  hiddenPiles : Array Card  -- 28 entries (padded with default)
  nHidden : Array Nat       -- 7 entries: count per pile
  pileMap : Array Nat        -- 52 entries: card → pile index
  firstLayerMask : Nat       -- bitmask
  lockedMask : Nat           -- bitmask
  deriving DecidableEq, Repr

namespace Hidden

/-- Construct Hidden from a flat array of pile cards. -/
def new (cards : Array Card) : Hidden :=
  ⟨cards, #[0,0,0,0,0,0,0], Array.mkArray 52 0, 0, 0⟩  -- simplified

/-- Pop (reveal) the hidden card below the given top card.
    Returns the newly revealed card, or indicates empty pile. -/
def popCard (h : Hidden) (c : Card) : Option Card × Hidden :=
  (none, h)  -- TODO: implement

/-- Unpop (undo reveal) a hidden card. -/
def unpopCard (h : Hidden) (c : Card) : Option Card × Hidden :=
  (none, h)  -- TODO: implement

/-- Whether all hidden cards have been revealed. -/
def isAllUp (h : Hidden) : Bool :=
  h.lockedMask = 0

/-- Total number of face-down cards. -/
def totalDownCards (h : Hidden) : Nat :=
  (h.nHidden.map (· - 1)).foldl (· + ·) 0  -- nHidden includes top visible card

/-- Get the first layer mask. -/
def getFirstLayerMask (h : Hidden) : Nat := h.firstLayerMask

/-- Get the locked mask (all hidden cards). -/
def getLockedMask (h : Hidden) : Nat := h.lockedMask

/-- Encode as 16-bit mixed-radix.
    Matches `Hidden::encode()` in src/hidden.rs. -/
def encode (h : Hidden) : Nat := 0  -- TODO

/-- Decode from 16-bit mixed-radix. -/
def decode (n : Nat) : Hidden := ⟨Array.mkArray 28 Card.default, #[0,0,0,0,0,0,0], Array.mkArray 52 0, 0, 0⟩

/-- Shuffle hidden cards randomly (for HOP/MCTS). -/
def shuffle (h : Hidden) (rng : Nat) : Hidden := h  -- TODO

/-- Reset to canonical form. -/
def clear (h : Hidden) : Hidden := h  -- TODO

end Hidden

end Klondike
