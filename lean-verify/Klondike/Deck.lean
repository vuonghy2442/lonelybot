/-
Klondike.Deck — Stock/waste deck representation, matching src/deck.rs.

The deck holds 24 cards in stock + waste, with a draw cursor position
and a draw step (1 or 3). Provides:
- find_card: locate a card in the deck
- compute_mask: bitmask of drawable cards
- offset / draw: advance the draw cursor
- encode/decode: compact 29-bit serialization
- is_pure: whether the deck cycles back to the current position
-/

namespace Klondike

/--
The deck representation matching `Deck` in src/deck.rs.

Fields:
- cards: the 24 cards in deal order
- draw_cur: current position in the draw cycle (0..len)
- draw_step: draw step (1 or 3)
-/
structure Deck where
  cards : Array Card  -- 24 cards
  drawCur : Nat       -- current draw position
  drawStep : Nat      -- 1 or 3
  deriving DecidableEq, Repr

namespace Deck

/-- Number of cards in the deck. -/
def len (d : Deck) : Nat := d.cards.size

/-- Whether the deck is empty. -/
def isEmpty (d : Deck) : Bool := d.cards.isEmpty

/-- Get the draw step as a nonzero value. -/
def drawStep (d : Deck) : Nat := d.drawStep

/-- Get the current draw offset. -/
def offset (d : Deck) : Nat := d.drawCur

/-- Peek at a card at a given position in the deck. -/
def peek (d : Deck) (pos : Nat) : Option Card :=
  d.cards[pos]?

/-- Peek at the last card in the deck. -/
def peekLast (d : Deck) : Option Card :=
  d.cards.getLast?

/-- Whether the deck is "pure" — dealing cycles back to current state.
    Matches `Deck::is_pure()` in src/deck.rs:254. -/
def isPure (d : Deck) : Bool :=
  d.drawCur % d.drawStep = 0 || d.drawCur = d.len

/-- Find a card in the deck. Returns (found, position). -/
def findCard (d : Deck) (c : Card) : Bool × Nat :=
  match d.cards.findIdx? (· = c) with
  | some i => (true, i)
  | none   => (false, 0)

/-- Compute the bitmask of currently drawable cards from the deck.
    In draw-N mode, iterates through waste positions.
    Matches `Deck::compute_mask()` in src/deck.rs:211. -/
def computeMask (d : Deck) (filter : Bool) : Nat :=
  0  -- TODO: implement matching Rust logic

/-- Advance the draw offset by one step. -/
def dealOnce (d : Deck) : Deck :=
  let next := d.drawCur + 1
  { d with drawCur := if next >= d.cards.size then 0 else next }

/-- Draw a card at the given position (remove from deck). -/
def draw (d : Deck) (pos : Nat) : Deck :=
  let newCur := if pos < d.drawCur && pos >= d.drawCur - d.drawStep then
    if d.drawCur = d.cards.size then 0 else d.drawCur - 1
  else d.drawCur
  { d with drawCur := newCur }  -- simplified; Rust does more complex tracking

/-- Encode the deck as a compact Nat.
    Matches `Deck::encode()` in src/deck.rs.
    Format: 24-bit card bitmap + 5-bit offset = 29 bits. -/
def encode (d : Deck) : Nat :=
  0  -- TODO: implement matching Rust serialization

/-- Decode a compact Nat as a deck. -/
def decode (n : Nat) : Deck :=
  ⟨#[], 0, 1⟩  -- TODO: implement

end Deck

end Klondike
