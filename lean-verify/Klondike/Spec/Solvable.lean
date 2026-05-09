/-
Klondike.Solvable — Solvability definition, reachability, and the
fundamental soundness property that pruning preserves solvability.

This file defines:
- What it means for a game state to be solvable (exists a sequence of
  legal moves reaching a win)
- The set of reachable states from a given state
- The core theorem schema: if a pruned move is taken, the resulting
  state is also reachable via non-pruned moves

The key insight for proving pruning correct is:

  **Pruning Soundness**: If state s is solvable and move m is pruned,
  then s remains solvable without using m. Equivalently, for every
  winning path that uses m, there exists a winning path that doesn't.

This is proved by case analysis on each pruning rule.
-/

namespace Klondike

open Basic

/--
A game state is solvable if there exists a finite sequence of legal moves
that reaches a winning state. We formalize this as an inductive predicate.

This is the "ground truth" — pruning is correct iff it never changes
the solvability of any state.
-/
inductive Solvable : GameState → Prop where
  | win : GameState.isWin s → Solvable s
  | step (m : Move) (h : (s.doMove m).isSome) :
      Solvable (s.doMove m |>.get h) → Solvable s

namespace Solvable

/--
The fundamental soundness theorem for move pruning.

If `prunedMoves` is a set of moves that are "safe to prune" (i.e.,
for every pruned move m and every winning path through m, there exists
an alternative winning path not using m), then pruning those moves
preserves solvability.

This is the master theorem. Each individual pruning rule needs to
prove the hypothesis.
-/
theorem pruning_soundness (s : GameState)
    (prunedMoves : Set Move)
    (h_prune : ∀ m ∈ prunedMoves, ∀ s',
      s.doMove m = some s' → Solvable s' →
        ∃ m' ∉ prunedMoves, ∃ s'', s.doMove m' = some s'' ∧ Solvable s'') :
    Solvable s ↔ ∃ m ∉ prunedMoves, ∃ s', s.doMove m = some s' ∧ Solvable s' := by
  constructor
  · intro h
    cases h with
    | win hw =>
      -- If s is already won, any legal non-pruned move works (or there are no moves)
      -- Actually, a won state has no moves needed, so we need a different approach
      -- For a won state, solvability is trivially preserved
      exfalso
      -- A won state should not have any moves that need to be considered
      sorry -- TODO: handle the already-won case
    | step m hm hs' =>
      -- Move m leads to a solvable state
      by_cases hmem : m ∈ prunedMoves
      · -- m is pruned: use h_prune to find an alternative
        obtain ⟨m', hm'not, s'', hm's'', hs''⟩ := h_prune m hmem _ hm hs'
        exact ⟨m', hm'not, s'', hm's'', hs''⟩
      · -- m is not pruned: it's already a valid witness
        exact ⟨m, hmem, _, hm, hs'⟩
  · intro ⟨m, _, s', hm, hs'⟩
    exact Solvable.step m hm hs'

/--
Helper: solvability is monotone with respect to reachable states.
If s can reach s' and s' is solvable, then s is solvable.
-/
theorem solvable_of_reachable (h : ∃ ms : List Move, reaches s ms s') :
    Solvable s' → Solvable s := by
  intro hs'
  induction h with
  | nil => exact hs'
  | cons m _ hm ih => exact Solvable.step m hm ih

/--
A sequence of moves reaches a state. We define this relationally.
-/
inductive reaches : GameState → List Move → GameState → Prop where
  | nil : reaches s [] s
  | cons (m : Move) (ms : List Move) :
      s.doMove m = some s' → reaches s' ms s'' → reaches s (m :: ms) s''

end Solvable

/--
A move m "dominates" a move m' if for every winning path that starts
with m', there is a winning path that starts with m (and doesn't use m').

This is the formal counterpart of the "dominance" concept from the
Solvitaire paper and the `gen_moves::<true>` optimization in the Rust code.
-/
def Dominates (s : GameState) (m m' : Move) : Prop :=
  ∀ s' s'', s.doMove m' = some s' → s.doMove m = some s'' →
    Solvable s' → Solvable s''

namespace Dominates

/--
If m dominates m', then pruning m' preserves solvability.
-/
theorem prunes_dominated (s : GameState) (m m' : Move)
    (h : Dominates s m m') :
    ∀ s', s.doMove m' = some s' → Solvable s' →
      ∃ m'' ∉ ({m'} : Set Move), ∃ s'', s.doMove m'' = some s'' ∧ Solvable s'' := by
  intro s' hm' hs'
  obtain ⟨s'', hm''⟩ := s.doMove m
  refine' ⟨m, by simp, s'', hm'', _⟩
  exact h s' s'' hm' hm'' hs'

end Dominates

end Klondike
