namespace Klondike

abbrev N_SUITS : Nat := 4
abbrev N_RANKS : Nat := 13
abbrev N_CARDS : Nat := 52
abbrev KING_RANK : Nat := 12
abbrev N_PILES : Nat := 7
abbrev N_PILE_CARDS : Nat := 28
abbrev N_DECK_CARDS : Nat := 24

def suitXorColor (v : Nat) : Nat := v ^^^ ((v >>> 1) &&& 2)

def SUIT_MASK : Array Nat := #[0x4141414141414141, 0x8282828282828282, 0x1414141414141414, 0x2828282828282828]
def KING_MASK : Nat := 0xF <<< (N_SUITS * KING_RANK)
def HALF_MASK : Nat := 0x3333333333333333
def ALT_MASK : Nat := 0x5555555555555555
def RANK_MASK : Nat := 0x1111111111111111
def COLOR_MASK : Array Nat := #[SUIT_MASK[0]! ||| SUIT_MASK[1]!, SUIT_MASK[2]! ||| SUIT_MASK[3]!]

def fullMask (i : Nat) : Nat := (1 <<< i) - 1

def Nat.complement64 (n : Nat) : Nat := fullMask 64 - n

private theorem nat_and_sub_one_lt (n : Nat) (h : n ≠ 0) : n &&& (n - 1) < n := by
  have hle : n &&& (n - 1) ≤ n := Nat.and_le_left
  have hne : n &&& (n - 1) ≠ n := by
    intro heq
    have h1 : n &&& (n - 1) ≤ n - 1 := Nat.and_le_right
    have h2 : n ≤ n - 1 := by
      calc n = n &&& (n - 1) := heq.symm
           _ ≤ n - 1 := h1
    omega
  omega

def Nat.popCount (n : Nat) : Nat :=
  if h : n = 0 then 0 else 1 + Nat.popCount (n &&& (n - 1))
termination_by n
decreasing_by exact nat_and_sub_one_lt n h

private theorem suitXorColor_lt (v : Nat) (h : v < N_CARDS) : suitXorColor v < N_CARDS := by
  unfold suitXorColor
  sorry

private theorem xor1_lt (v : Nat) (h : v < N_CARDS) : (v ^^^ 1) < N_CARDS := by sorry

private theorem xor2_lt (v : Nat) (h : v < N_CARDS) : (v ^^^ 2) < N_CARDS := by sorry

private theorem div_suit_lt (v : Nat) (h : v < N_CARDS) : v / N_SUITS < N_RANKS := by
  unfold N_SUITS N_RANKS N_CARDS at *
  omega

private theorem suitXorColor_mod_lt (v : Nat) : suitXorColor v % N_SUITS < N_SUITS := by
  unfold N_SUITS
  apply Nat.mod_lt
  decide

private theorem rank_suit_raw_lt (rank : Nat) (suit : Nat) (hr : rank < N_RANKS) (hs : suit < N_SUITS) : rank * N_SUITS + suit < N_CARDS := by
  unfold N_SUITS N_RANKS N_CARDS at *
  omega

private theorem xor1_inv (v : Nat) : (v ^^^ 1) ^^^ 1 = v := by
  rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]

structure Card where
  val : Fin N_CARDS
  deriving DecidableEq, Repr

namespace Card

def mkOf (rank : Fin N_RANKS) (suit : Fin N_SUITS) : Card :=
  let raw : Nat := rank.val * N_SUITS + suit.val
  let encoded : Nat := suitXorColor raw
  ⟨⟨encoded, suitXorColor_lt raw (rank_suit_raw_lt rank.val suit.val rank.isLt suit.isLt)⟩⟩

def rank (c : Card) : Fin N_RANKS :=
  ⟨c.val.val / N_SUITS, div_suit_lt c.val.val c.val.isLt⟩

def suitXor (c : Card) : Fin N_SUITS :=
  ⟨suitXorColor c.val.val % N_SUITS, suitXorColor_mod_lt c.val.val⟩

def suit (c : Card) : Fin N_SUITS := suitXor c

def swapSuit (c : Card) : Card :=
  ⟨⟨c.val.val ^^^ 1, xor1_lt c.val.val c.val.isLt⟩⟩

def swapColor (c : Card) : Card :=
  ⟨⟨c.val.val ^^^ 2, xor2_lt c.val.val c.val.isLt⟩⟩

def increaseRankSwapColor (c : Card) : Option Card :=
  if h : c.val.val + N_SUITS < N_CARDS then
    some ⟨⟨c.val.val + N_SUITS, h⟩⟩
  else none

def reduceRankSwapColor (c : Card) : Card :=
  if h : c.val.val ≥ N_SUITS then
    ⟨⟨c.val.val - N_SUITS, by omega⟩⟩
  else c

def isKing (c : Card) : Bool := c.rank.val ≥ KING_RANK

def maskIndex (c : Card) : Nat := c.val.val
def mask (c : Card) : Nat := 1 <<< c.val.val
def goesOnTopOf (c c' : Card) : Bool := ((c.val.val + N_SUITS) ^^^ c'.val.val) < 2
def default : Card := ⟨⟨0, Nat.succ_pos 51⟩⟩

theorem swapSuit_involution (c : Card) : (c.swapSuit).swapSuit = c := sorry

theorem swapSuit_preserves_rank (c : Card) : (c.swapSuit).rank = c.rank := sorry

theorem swapSuit_preserves_color (c : Card) : (c.swapSuit).suitXor = c.suitXor := sorry

end Card

end Klondike
