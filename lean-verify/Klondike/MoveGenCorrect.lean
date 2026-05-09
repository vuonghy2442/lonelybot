/-
Klondike.MoveGenCorrect — Correctness of gen_moves w.r.t. the specification.

This is the central correctness result. We define:
1. A specification `legal_moves` that lists all mathematically legal moves
2. A theorem that `gen_moves(false)` produces exactly the legal moves
3. A theorem that `gen_moves(true)` produces a subset of legal moves
   where every removed move is dominated by a remaining move

The specification is written in terms of the abstract game rules
(pile tops, foundation ranks, card positions), while the implementation
uses bitmask operations. The correctness proof bridges the gap.
-/

namespace Klondike

/--
SPECIFICATION: List all mathematically legal moves from a state.

A move is legal if:
- DeckStack(c): c is the current waste card AND c can stack to foundation
- PileStack(c): c is a top card of some pile AND c can stack to foundation
- DeckPile(c):  c is a drawable waste card AND c can go on some pile
- StackPile(c): c is on the foundation AND c can go on some pile
- Reveal(c):    c is a locked top card AND c can go on some non-empty pile
-/
def legalMoves (s : Solitaire) : MoveMask :=
  -- This is the ground truth specification
  MoveMask.empty  -- TODO: implement from game rules

namespace MoveGenCorrect

/--
THEOREM 1 (Soundness): Every move in gen_moves(false) is legal.

gen_moves(false) ⊆ legalMoves
-/
theorem gen_moves_sound (s : Solitaire) :
    ∀ m, m ∈ genMoves false s → m ∈ legalMoves s := by
  sorry

/--
THEOREM 2 (Completeness): Every legal move appears in gen_moves(false).

legalMoves ⊆ genMoves(false)
-/
theorem gen_moves_complete (s : Solitaire) :
    ∀ m, m ∈ legalMoves s → m ∈ genMoves false s := by
  sorry

/--
THEOREM 3 (Exactness): gen_moves(false) = legalMoves.

This is the composition of soundness and completeness.
-/
theorem gen_moves_exact (s : Solitaire) :
    genMoves false s = legalMoves s := by
  sorry

/--
THEOREM 4 (Dominance soundness): gen_moves(true) ⊆ legalMoves.

Every move produced by gen_moves with dominance is still legal.
-/
theorem gen_moves_dom_sound (s : Solitaire) :
    ∀ m, m ∈ genMoves true s → m ∈ legalMoves s := by
  sorry

/--
THEOREM 5 (Dominance preserves solvability):
For every move m in legalMoves but NOT in genMoves(true),
there exists a move m' in genMoves(true) that dominates m.

This is the key theorem for proving the solver correct.
If a pruned move leads to a win, some non-pruned move also leads to a win.
-/
theorem gen_moves_dom_preserves_solvability (s : Solitaire) :
    ∀ m, m ∈ legalMoves s → m ∉ genMoves true s →
      ∃ m', m' ∈ genMoves true s ∧
        ∀ s', s.doMove m |>.2 |>.2 = s' →
          Solvable s' →
            ∃ s'', s.doMove m' |>.2 |>.2 = s'' ∧ Solvable s'' := by
  sorry

end MoveGenCorrect

/--
SPECIFICATION: A game state is solvable if there exists a finite
sequence of legal moves reaching a win.
-/
inductive Solvable : Solitaire → Prop where
  | win : s.isWin → Solvable s
  | step (m : Move) (h : m ∈ legalMoves s) :
      Solvable (s.doMove m |>.2 |>.2) → Solvable s

end Klondike
