/-
Klondike.SuitSymmetry — The suit-swap invariance of Klondike Solitaire.

This file formalizes the key symmetry exploited by the lonelybot solver:

**Main Theorem (rank-color swap invariance):**
If two cards share the same rank and color (e.g., 5♥ and 5♦), and neither
is on the foundation, then swapping them throughout the game state
(piles, hidden cards, and stock/waste) produces a state that is solvable
if and only if the original was solvable.

This is THE foundational result that justifies:
1. `dominance_mask` in `stack.rs` — using `min(s[0], s[1])` per color pair
2. `paired_stack` in `gen_moves` — when both same-color suits have
   stackable cards of the same rank, only keep one
3. `suit_filter` in `gen_moves` — restricting which suit within a color
   can receive a StackPile move
4. `swap_pair` in `state.rs` — the bitmask-level ♥↔♦ and ♣↔♠ swap
5. The `pile_stack = least_stack` dominance (only stack the lowest-rank
   card within each color pair)

The intuition: Klondike's tableau rules only care about rank and color,
not specific suit. The only place suit matters is the foundation — but
if both cards of a color/rank are still in play (not on the foundation),
they're fungible: either one can go to its foundation first, and the
other can follow.

More precisely: for any rank r and color C, if BOTH cards (r, suit_C_0)
and (r, suit_C_1) are in the tableau (not on the foundation), then:
- They stack identically (same rank + same color → same "goes on top of")
- They receive cards identically (same rank + same color → same "can receive")
- They compete for the same foundation slot, but since neither has claimed
  it yet, the order doesn't matter

Therefore, we can freely choose which one to stack first, which one to
move from the foundation, etc. — as long as we don't create an
inconsistency with the foundation.
-/

namespace Klondike

open Basic

/-
=========================================================================
  Definition: The suit-swap permutation on cards
=========================================================================

For a given rank r and color C, the swap exchanges the two suits of
that color at rank r. For example, swap(5, red) exchanges 5♥ ↔ 5♦.
-/

/-- A specific rank-color swap: for rank r and color C, swap the two
    cards (r, suit₀) ↔ (r, suit₁) where suit₀ and suit₁ are the two
    suits of color C. -/
def rankColorSwap (r : Rank) (C : Color) : Card → Card
  | ⟨r', s⟩ =>
    if r' = r ∧ s.color = C then { rank := r', suit := s.swapSuit }
    else ⟨r', s⟩

/-- The rank-color swap is an involution (applying it twice returns the
    original card). -/
theorem rankColorSwap_involution (r : Rank) (C : Color) (c : Card) :
    rankColorSwap r C (rankColorSwap r C c) = c := by
  simp [rankColorSwap]
  split <;> split <;> simp [Card.swapSuit_involution]
  · rfl
  · rfl

/-- The rank-color swap preserves rank. -/
theorem rankColorSwap_preserves_rank (r : Rank) (C : Color) (c : Card) :
    (rankColorSwap r C c).rank = c.rank := by
  simp [rankColorSwap]
  split <;> rfl

/-- The rank-color swap preserves color. -/
theorem rankColorSwap_preserves_color (r : Rank) (C : Color) (c : Card) :
    (rankColorSwap r C c).color = c.color := by
  simp [rankColorSwap]
  split
  · exact Card.swapSuit_preserves_color _
  · rfl

/--
KEY LEMMA: The rank-color swap preserves the "goes on top of" relation.

If c goes on top of c', then (swap c) goes on top of (swap c').

This is because "goes on top of" only depends on rank and color:
  c.goesOnTopOf c'  ⟺  c.rank + 1 = c'.rank ∧ c.color ≠ c'.color

The swap preserves both rank and color, so it preserves the relation.
-/
theorem rankColorSwap_preserves_goesOnTopOf (r : Rank) (C : Color)
    {c c' : Card} (h : c.goesOnTopOf c') :
    (rankColorSwap r C c).goesOnTopOf (rankColorSwap r C c') := by
  obtain ⟨hr, hc⟩ := h
  constructor
  · rw [rankColorSwap_preserves_rank, rankColorSwap_preserves_rank]; omega
  · rw [rankColorSwap_preserves_color, rankColorSwap_preserves_color]; exact hc

/--
KEY LEMMA: The rank-color swap preserves "can stack to foundation"
IF the two swapped cards are both NOT on the foundation.

If neither card (r, suit₀) nor (r, suit₁) has been stacked to the
foundation yet, then the foundation state for both suits is the same
(or one ahead by exactly the card in question), and swapping which
one goes first doesn't change solvability.

Precisely: if both (r, s₀) and (r, s₁) are not on the foundation
(meaning foundation(s₀) ≤ r and foundation(s₁) ≤ r), then applying
the swap to the game state preserves the "can stack" predicate.
-/
theorem rankColorSwap_preserves_canStackTo (r : Rank) (C : Color)
    (f : Foundation)
    (h_both_not_stacked : f (Suit.ofColor C 0) ≤ r ∧ f (Suit.ofColor C 1) ≤ r) :
    ∀ c, (rankColorSwap r C c).canStackTo (rankColorSwap_foundation r C f) ↔
      c.canStackTo f := by
  sorry -- TODO: Requires defining Suit.ofColor and the foundation swap

/-
=========================================================================
  Definition: Applying the swap to an entire game state
=========================================================================

We lift the card-level swap to the game state level, swapping all
occurrences of the two target cards in piles, hidden cards, and deck.
-/

/-- Apply the rank-color swap to a list of cards. -/
def List.rankColorSwap (r : Rank) (C : Color) : List Card → List Card :=
  List.map (rankColorSwap r C)

/-- Apply the rank-color swap to a tableau pile. -/
def TableauPile.rankColorSwap (r : Rank) (C : Color) (p : TableauPile) : TableauPile :=
  ⟨p.hidden.rankColorSwap r C, p.visible.rankColorSwap r C⟩

/-- Apply the rank-color swap to the foundation.

If both suits of color C have foundation rank ≤ r, then the swap just
exchanges the two foundation values (since neither card has been stacked
yet, and the order in which they get stacked doesn't affect solvability).

If one of the suits has foundation rank > r, the swap may not apply
directly (one card has already been stacked past the swap point).
-/
def Foundation.rankColorSwap (r : Rank) (C : Color) (f : Foundation) : Foundation :=
  fun s =>
    if s.color = C then f s.swapSuit  -- swap the foundation values for same-color suits
    else f s

/-- Apply the rank-color swap to the deck. -/
def Deck.rankColorSwap (r : Rank) (C : Color) (d : Deck) : Deck :=
  { d with
    stock := d.stock.rankColorSwap r C
    waste := d.waste.rankColorSwap r C }

/-- Apply the rank-color swap to the entire game state. -/
def GameState.rankColorSwap (r : Rank) (C : Color) (s : GameState) : GameState :=
  { piles := fun i => (s.piles i).rankColorSwap r C
    foundation := s.foundation.rankColorSwap r C
    deck := s.deck.rankColorSwap r C }

/-
=========================================================================
  The Main Suit Symmetry Theorem
=========================================================================

If both cards of rank r and color C are "in play" (not yet on the
foundation), then the rank-color swap preserves solvability.

"In play" means:
1. Foundation(suit₀) ≤ r and Foundation(suit₁) ≤ r
   (neither card has been stacked to the foundation past rank r)
2. Both cards appear somewhere in the game state
   (in piles, hidden cards, or deck)

Under these conditions:
  Solvable s  ⟺  Solvable (s.rankColorSwap r C)
-/

/-- The rank-color swap is an involution on game states. -/
theorem GameState.rankColorSwap_involution (r : Rank) (C : Color) (s : GameState) :
    (s.rankColorSwap r C).rankColorSwap r C = s := by
  simp [GameState.rankColorSwap, TableauPile.rankColorSwap, List.rankColorSwap]
  -- Need to show that map (swap r C) ∘ map (swap r C) = id
  -- This follows from rankColorSwap_involution at the card level
  sorry -- TODO: map_comp + rankColorSwap_involution

/--
THE MAIN THEOREM: Suit symmetry preserves solvability.

If both cards of rank r and color C are not yet on the foundation
(i.e., foundation(suit₀) ≤ r and foundation(suit₁) ≤ r), then:

  Solvable s  ⟺  Solvable (s.rankColorSwap r C)

Proof strategy:
1. Show that the swap is a bijection on game states (involution).
2. Show that the swap preserves move legality: if move m is legal
   in state s, then the "swapped move" is legal in the swapped state.
3. Show that the swap commutes with doMove: applying the swap after
   a move is the same as applying the swapped move in the swapped state.
4. Therefore, any winning path in s can be translated to a winning
   path in (s.rankColorSwap r C) by swapping each move.
5. Since the swap is an involution, the converse also holds.
-/
theorem suit_symmetry_preserves_solvability (r : Rank) (C : Color) (s : GameState)
    (h_in_play : s.foundation (Suit.ofColor C 0) ≤ r ∧
                 s.foundation (Suit.ofColor C 1) ≤ r) :
    Solvable s ↔ Solvable (s.rankColorSwap r C) := by
  constructor
  · -- Forward direction: translate winning path from s to swapped state
    intro hs
    induction hs with
    | win hw =>
      -- A winning state in s maps to a winning state in the swapped state
      -- because the swap preserves the "is win" predicate
      sorry -- TODO: show rankColorSwap preserves isWin
    | step m hm hs' =>
      -- If s →_m s' and s' is solvable in swapped world,
      -- then s is solvable in swapped world
      sorry -- TODO: show move correspondence under swap
  · -- Reverse direction: by involution
    intro h
    have := suit_symmetry_preserves_solvability r C (s.rankColorSwap r C) _
    · exact this.mp h
    · -- Need to show the foundation condition holds for the swapped state
      sorry -- TODO: the swap exchanges foundation values, so ≤ is preserved

/-
=========================================================================
  Corollaries: How suit symmetry justifies specific pruning rules
=========================================================================

Each of the following corollaries connects the main suit symmetry
theorem to a specific optimization in the Rust code.
-/

/--
Corollary 1: `dominance_mask` in `stack.rs`.

The dominance mask computes `min(f[hearts], f[diamonds])` and
`min(f[clubs], f[spades])` per color pair. Any card with rank below
this minimum is guaranteed safe to stack because:

If card (r, suit₀) is stackable and r < min(f[suit₀], f[suit₁]),
then (r, suit₁) is also stackable (or already stacked). By suit
symmetry, it doesn't matter which one we stack first — both will
eventually be stacked. So we can safely auto-stack (r, suit₀).

Formally: if PileStack c is legal and c.rank < min(f[c₀.suit], c₁.suit])
where c₀ and c₁ are the same-color pair, then PileStack c is dominated
by (i.e., at least as good as) any other move.
-/
theorem dominance_mask_sound (s : GameState) (c : Card)
    (h_stackable : s.canMoveToFoundation c)
    (h_below_min : (c.rank : ℕ) < min (s.foundation c.suit) (s.foundation c.suit.swapSuit)) :
    Dominates s (Move.pileStack c) m' →
      Solvable (s.doMove m' |>.get _) → Solvable (s.doMove (Move.pileStack c) |>.get _) := by
  sorry -- TODO: Derive from suit_symmetry_preserves_solvability

/--
Corollary 2: `paired_stack` in `gen_moves`.

When both cards of the same color and rank are stackable to the
foundation (e.g., both 5♥ and 5♦ can go to their foundations), we
only need to consider one of them. By suit symmetry, stacking 5♥ is
equivalent to stacking 5♦ — if one leads to a win, the other does too.

The code picks the lexicographically smaller one (the one with the
smaller mask index in the XOR encoding).

Formally: if both PileStack c and PileStack c.swapSuit are legal,
then PileStack c dominates PileStack c.swapSuit (and vice versa).
-/
theorem paired_stack_sound (s : GameState) (c : Card)
    (h_both : s.canMoveToFoundation c ∧ s.canMoveToFoundation c.swapSuit) :
    Dominates s (Move.pileStack c) (Move.pileStack c.swapSuit) := by
  sorry -- TODO: Derive from suit_symmetry_preserves_solvability

/--
Corollary 3: `suit_filter` in `gen_moves`.

When choosing which card to move from the foundation to a pile
(StackPile), the code restricts which suit within a color pair can
be used. This is sound because:

If card c is on the foundation and c.swapSuit is available in the
same position, moving c.swapSuit instead leads to an equivalent game
(by suit symmetry). So we only need to consider one direction.

Formally: StackPile c and StackPile c.swapSuit are equivalent under
the suit symmetry, so pruning one is safe.
-/
theorem suit_filter_sound (s : GameState) (c : Card)
    (h_both_legal : s.doMove (Move.stackPile c) |>.isSome ∧
                    s.doMove (Move.stackPile c.swapSuit) |>.isSome) :
    Dominates s (Move.stackPile c) (Move.stackPile c.swapSuit) := by
  sorry -- TODO: Derive from suit_symmetry_preserves_solvability

/--
Corollary 4: `least_stack` dominance — only stack the lowest-rank
card within each color pair.

When there are multiple stackable cards of the same color, the code
only keeps the one with the lowest rank. This is sound because:

Stacking a lower-rank card is always at least as good as stacking a
higher-rank card of the same color. The lower-rank card "unlocks"
more future moves (you can always stack the higher-rank one later).

Combined with suit symmetry: if the lowest-rank stackable card of
each color is c, then PileStack c dominates any other PileStack move.
-/
theorem least_stack_dominance (s : GameState) (c : Card)
    (h_lowest : ∀ c', c'.color = c.color → c'.rank ≥ c.rank →
                  s.canMoveToFoundation c' → c' = c ∨ c'.rank = c.rank) :
    ∀ c', c'.color = c.color → c'.rank > c.rank →
      s.canMoveToFoundation c' →
      Dominates s (Move.pileStack c) (Move.pileStack c') := by
  sorry -- TODO: Stacking the lower card is always at least as good

end Klondike
