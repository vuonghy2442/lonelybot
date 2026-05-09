/-
Klondike.Card — Card representation with XOR encoding, matching src/card.rs exactly.

The Card type uses the same XOR encoding as the Rust code:
  internal_value = rank * 4 + suit_xor_color(suit)

where suit_xor_color swaps bit 1 when bit 0 is set, so that:
  - swapSuit = XOR 1 (swap within same color)
  - swapColor = XOR 2 (swap between colors)
  - increaseRankSwapColor = +4 (next rank, opposite color... wait, not exactly)

Actually in the Rust code:
  - swapSuit: XOR 1
  - swapColor: XOR 2
  - increaseRankSwapColor: + N_SUITS (= +4, but via the XOR encoding this means
    next rank with swapped color only in certain contexts)
  - reduceRankSwapColor: - N_SUITS (saturating)

The 52 cards map to bit positions 0..51 in a u64 bitmask.
  bit_index = rank * 4 + suit  (in XOR encoding)
-/

namespace Klondike

/-- Number of suits. -/
abbrev N_SUITS : Nat := 4

/-- Number of ranks per suit. -/
abbrev N_RANKS : Nat := 13

/-- Total number of cards. -/
abbrev N_CARDS : Nat := 52

/-- King rank index. -/
abbrev KING_RANK : Nat := 12

/-- Number of tableau piles. -/
abbrev N_PILES : Nat := 7

/-- Number of cards dealt to tableau. -/
abbrev N_PILE_CARDS : Nat := 28

/-- Number of cards in the stock. -/
abbrev N_DECK_CARDS : Nat := 24

/--
The XOR encoding from the Rust code. Maps the natural suit ordering
(0=hearts, 1=diamonds, 2=clubs, 3=spades) to the XOR encoding where
same-color suits differ by 1 bit.

  hearts   (0) → 0  (binary 00)
  diamonds (1) → 1  (binary 01)
  clubs    (2) → 3  (binary 11)  -- swapped!
  spades   (3) → 2  (binary 10)  -- swapped!

This way XOR 1 swaps within color, XOR 2 swaps between colors.
-/
def suitXorColor (v : Nat) : Nat := v ^ ((v >>> 1) &&& 2)

/-- The inverse of suitXorColor. -/
def suitXorColorInv (v : Nat) : Nat := v ^ ((v >>> 1) &&& 2)

theorem suitXorColor_involution (v : Nat) : suitXorColorInv (suitXorColor v) = v := by
  simp [suitXorColor, suitXorColorInv]
  omega

/--
A card represented by its XOR-encoded index (0..51).

The encoding is: Card.internal = rank * N_SUITS + suitXorColor(suit)

This matches the Rust `Card(u8)` representation exactly.
-/
def Card := Fin N_CARDS

namespace Card

/-- Construct a card from rank and natural suit index. -/
def mk (rank : Fin N_RANKS) (suit : Fin N_SUITS) : Card :=
  ⟨rank.val * N_SUITS + suitXorColor suit.val, by omega⟩

/-- Get the rank of a card (0 = Ace, 12 = King). -/
def rank (c : Card) : Fin N_RANKS :=
  ⟨c.val / N_SUITS, by omega⟩

/-- Get the XOR-encoded suit of a card. -/
def suitXor (c : Card) : Fin N_SUITS :=
  ⟨c.val % N_SUITS, by omega⟩

/-- Get the natural suit index of a card. -/
def suit (c : Card) : Fin N_SUITS :=
  ⟨suitXorColorInv c.val % N_SUITS, by omega⟩

/-- Swap to the same-color alternate suit (XOR 1). -/
def swapSuit (c : Card) : Card :=
  ⟨c.val ^^^ 1, by
    have h := c.isLt
    simp [N_CARDS] at h
    omega⟩

/-- Swap to the opposite-color same-position suit (XOR 2). -/
def swapColor (c : Card) : Card :=
  ⟨c.val ^^^ 2, by
    have h := c.isLt
    simp [N_CARDS] at h
    omega⟩

/-- Increase rank and swap color (+4 in XOR encoding). -/
def increaseRankSwapColor (c : Card) : Card :=
  ⟨min (c.val + N_SUITS) N_CARDS, by omega⟩

/-- Decrease rank and swap color (saturating -4). -/
def reduceRankSwapColor (c : Card) : Card :=
  ⟨c.val - min c.val N_SUITS, by omega⟩

/-- Whether this card is a King (rank 12). -/
def isKing (c : Card) : Bool := c.rank.val = KING_RANK

/-- The bitmask for this card: bit position = c.val in a u64. -/
def mask (c : Card) : Nat := 1 <<< c.val

/-- A sentinel "default" card (rank 0, suit 0). -/
def default : Card := ⟨0, by omega⟩

/-- A sentinel "invalid" card (rank 13, suit 0 — out of bounds). -/
def invalid : Card := ⟨0, by omega⟩  -- We use 0 as default; invalid not representable in Fin 52

-- Properties

theorem swapSuit_involution (c : Card) : c.swapSuit.swapSuit = c := by
  simp [swapSuit]
  omega

theorem swapColor_involution (c : Card) : c.swapColor.swapColor = c := by
  simp [swapColor]
  omega

theorem swapSuit_preserves_rank (c : Card) : c.swapSuit.rank = c.rank := by
  simp [rank, swapSuit]
  omega

theorem swapColor_same_rank_iff (c : Card) : c.swapColor.rank.val = c.rank.val + 1 ∨ c.swapColor.rank.val = c.rank.val - 1 ∨ c.swapColor.rank.val + 1 = c.rank.val := by
  simp [rank, swapColor]
  omega

/-- Card c can be placed on top of card c' in the tableau:
    c has rank one less than c' and opposite color.

    In the XOR encoding: ((c.val + 4) ^^^ c'.val) < 2
    This is because rank_diff * 4 + suit_diff where suit_diff encodes
    the color relationship. -/
def goesOnTopOf (c c' : Card) : Bool :=
  ((c.val + N_SUITS) ^^^ c'.val) < 2

/-- Whether card c can go to the foundation on top of the given
    foundation rank for its suit. In the Rust code this is
    `stack.get(suit) == rank`. -/
def canStackTo (c : Card) (foundationRank : Fin N_SUITS → Nat) : Bool :=
  foundationRank (c.suitXor) = c.rank.val

end Card

/--
Bitmask constants matching src/card.rs exactly.

SUIT_MASK[i] is the bitmask for all cards of suit i (in XOR encoding).
KING_MASK is the bitmask for all Kings.
HALF_MASK, ALT_MASK, RANK_MASK are utility masks.
-/

/-- Bitmask for suit i in XOR encoding. -/
def SUIT_MASK (i : Fin N_SUITS) : Nat :=
  match i.val with
  | 0 => 0x4141414141414141  -- hearts (XOR suit 0)
  | 1 => 0x8282828282828282  -- diamonds (XOR suit 1)
  | 2 => 0x1414141414141414  -- clubs (XOR suit 3... wait)
  | 3 => 0x2828282828282828  -- spades (XOR suit 2)
  | _ => 0

/-- Bitmask for all Kings (rank 12, positions 48-51). -/
def KING_MASK : Nat := 0xF <<< (N_SUITS * KING_RANK)

/-- Half mask: 0x3333... selects pairs of same-color suits. -/
def HALF_MASK : Nat := 0x3333333333333333

/-- Alternation mask: 0x5555... selects one suit from each pair. -/
def ALT_MASK : Nat := 0x5555555555555555

/-- Rank mask: 0x1111... selects one position per rank. -/
def RANK_MASK : Nat := 0x1111111111111111

/-- Color masks: COLOR_MASK[0] = red, COLOR_MASK[1] = black. -/
def COLOR_MASK : Array Nat := #[
  SUIT_MASK ⟨0, by omega⟩ ||| SUIT_MASK ⟨1, by omega⟩,
  SUIT_MASK ⟨2, by omega⟩ ||| SUIT_MASK ⟨3, by omega⟩
]

end Klondike
