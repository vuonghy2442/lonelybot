/-
Klondike.Dominance — Formal verification of the move pruning rules.

This file contains the main results: formal statements and proofs that
each pruning rule used in the lonelybot solver preserves solvability.

The pruning rules (from src/pruning.rs) are:

1. **CyclePruner** — After doing move m, prune the immediately-reverse move.
   Correctness: undoing a move just got us back to where we started.
   Since we're doing DFS with a transposition table, we already visited
   the original state, so the reverse move leads to a dead end.

2. **RevealEmpty dominance** — After a Reveal that empties a pile,
   only King moves (to fill the empty pile) are allowed.
   Correctness: an empty pile can only be usefully filled by a King.
   Any other move is wasted because you'd need to fill the empty pile
   eventually anyway, and Kings can only go to empty piles.

3. **RevealCard dominance** (new in more_dominances branch) — After a
   Reveal that uncovers card c, only moves involving c or c.swapSuit
   are allowed for PileStack; StackPile, DeckPile, and Reveal are
   completely blocked.
   Correctness: the newly revealed card c is the only "new information"
   from this move. Any other move could have been done before the reveal.
   The c.swapSuit exception follows from suit symmetry (see SuitSymmetry.lean):
   since c and c.swapSuit are interchangeable, stacking c.swapSuit first
   is equivalent to stacking c first via the rank-color swap.

4. **DeckPile dominance** — After a DeckPile of card c (drawing from
   stock to tableau), prune PileStack of cards other than c.swapSuit,
   and prune Reveal of certain cards.
   Correctness: drawing c from the deck is "forced" (the deck cycles
   deterministically). The main new option is placing c or its
   same-color twin. Other PileStack moves could have been done before
   the draw. The c.swapSuit exception again follows from suit symmetry.

5. **Suit symmetry dominances** (in gen_moves with DOMINANCE=true) —
   These are the most powerful pruning rules, formalized in
   SuitSymmetry.lean. They include:
   - dominance_mask: auto-stack cards below min rank of each color pair
   - paired_stack: when both same-color cards of a rank are stackable,
     only keep the lexicographically smaller one
   - suit_filter: restrict which suit can receive a StackPile move
   - least_stack: only stack the lowest-rank card of each color

Each rule is stated as a theorem below, with a proof sketch.
Where full proofs require significant game-state reasoning, we state
the theorem as a `sorry` and provide the proof strategy.
-/

namespace Klondike

open Basic

/-
=========================================================================
  Rule 1: CyclePruner — Pruning the immediately-reverse move
=========================================================================

After executing move m in state s to reach state s', if m has a reverse
move m⁻¹ in s', we prune m⁻¹ from the legal moves in s'.

Correctness argument:
  The DFS traversal visits states via `traverse()` in traverse.rs.
  The transposition table ensures each state is visited at most once.
  If m is the move from s → s', then m⁻¹ is the move from s' → s.
  But s was already inserted into the transposition table before
  we recursed into s'. So doing m⁻¹ would lead to s, which is
  already in the TP table, and would be immediately skipped.

  Therefore, m⁻¹ cannot lead to any new state that hasn't been
  visited, so pruning it never loses solvability.

This argument depends on the DFS + transposition table structure,
not just the game rules. We formalize it as a property of the
search algorithm.
-/

/-- After move m from state s, if m⁻¹ is the reverse move leading back
    to s, then s is already in the transposition table, so m⁻¹ is
    pruned without losing solvability. -/
theorem cycle_pruner_sound (s s' : GameState) (m : Move)
    (h_do : s.doMove m = some s')
    (h_rev : s'.reverseMove m |>.isSome = true) :
    ∃ s'', s'.doMove (s'.reverseMove m |>.get _) = some s'' ∧ s'' = s := by
  sorry -- TODO: This requires formalizing the reverse move semantics

/-
The above theorem says: the reverse move leads back to the original
state. Since the transposition table already contains s, this move
would be a no-op in the DFS. Hence pruning it is correct.

To complete this, we need:
1. A formal specification of the transposition table
2. A proof that the DFS never re-visits a state in the TP table
3. The composition: "if reverse move leads to already-visited state,
   then pruning it preserves solvability"
-/

/-
=========================================================================
  Rule 2: RevealEmpty — After reveal empties a pile, only Kings allowed
=========================================================================

When a Reveal move empties a pile (the revealed card was the only
visible card and there were no hidden cards underneath), the FullPruner
allows only King moves for StackPile, DeckPile, and Reveal.

The intuition: an empty pile is a resource. In Klondike, the only way
to start a new pile is by placing a King. Any non-King move "wastes"
the empty pile — you'll eventually need to fill it, and Kings can ONLY
go to empty piles. So it's always at least as good to fill the empty
pile with a King first.

Formally: if there's a winning path from s that uses a non-King move
before filling the empty pile with a King, we can reorder the King
move to come first (since placing a King on an empty pile doesn't
interfere with other moves).
-/

/-- After a Reveal that empties a pile, any winning path starting with
    a non-King move can be transformed into a winning path that starts
    by placing a King on the empty pile. -/
theorem reveal_empty_dominance (s : GameState) (c : Card)
    (h_reveal : s.doMove (Move.reveal c) = some s')
    (h_empty : Extra info = ExtraInfo.revealEmpty) :
    ∀ m ≠ Move.reveal c, ∃ m', Card.isKing m'.card = true ∧
      Dominates s m' m := by
  sorry -- TODO: Requires game-state transformation proof

/-
Proof strategy for reveal_empty_dominance:
1. Let pile i be the empty pile after the reveal.
2. Consider any winning path P that starts with non-King move m.
3. In path P, there must eventually be a King placed on pile i
   (otherwise pile i stays empty, but Klondike requires all cards
   on the foundation to win, and Kings can only go to empty piles).
4. Let move K = "place a King on pile i" be the first such move in P.
5. Swap K with the moves between the reveal and K:
   - K doesn't depend on any of those intermediate moves
     (Kings can go on any empty pile, and placing a King doesn't
     affect the legality of other moves)
6. The reordered path is still winning.
7. Therefore, starting with a King move dominates starting with m.
-/

/-
=========================================================================
  Rule 3: RevealCard — After revealing card c, prune irrelevant moves
=========================================================================

When a Reveal move uncovers a specific card c (ExtraInfo.revealCard c),
the FullPruner (from the more_dominances branch) prunes:
- PileStack: only c and c.swapSuit are allowed
- StackPile, DeckPile, Reveal: completely blocked (0 mask)

The c.swapSuit exception comes from suit symmetry (SuitSymmetry.lean):
if PileStack c is useful, then PileStack c.swapSuit is equally useful
(because they are interchangeable via the rank-color swap at c's rank
and color, as long as neither is on the foundation yet).

Any other PileStack/StackPile/DeckPile/Reveal move that doesn't involve
c or c.swapSuit could have been done BEFORE the reveal, since the game
state for those moves hasn't changed. The reveal is the only source of
new information. And doing the reveal first is at least as good (you
might get to use the reveal information earlier in the search).
-/

/-- After a Reveal that uncovers card c, any move not involving c or
    c.swapSuit was also legal before the reveal. -/
theorem reveal_card_moves_available_before (s : GameState) (c : Card)
    (h_reveal : s.doMove (Move.reveal c) = some s')
    (h_extra : (s.doMove (Move.reveal c)).map Prod.snd = some (ExtraInfo.revealCard c)) :
    ∀ m, m ≠ Move.pileStack c → m ≠ Move.pileStack c.swapSuit →
      m ≠ Move.reveal c →
      s'.doMove m = some s'' → s.doMove m = some s''' := by
  sorry -- TODO: Requires game state reasoning

/--
The key theorem: after revealing card c, any winning path starting
with a move not involving c or c.swapSuit can be reordered so the
reveal comes first.

This means pruning those moves is safe: if they lead to a win,
the same win is achievable via a different order.
-/
theorem reveal_card_dominance (s : GameState) (c : Card)
    (h_reveal : s.doMove (Move.reveal c) = some s')
    (h_extra : ExtraInfo.revealCard c) :
    ∀ m, m.card ≠ c → m.card ≠ c.swapSuit → m ≠ Move.reveal c →
      Dominates s (Move.reveal c) m := by
  sorry -- TODO: The main proof

/-
Proof strategy for reveal_card_dominance:
1. The Reveal of c changes the game state only by:
   a. Moving the revealed top card from pile i to pile j
   b. Uncovering c at the bottom of pile i
2. Any move m not involving c or c.swapSuit:
   - Doesn't move c (since c is at the bottom of pile i, it's not
     the top card, so m can't be PileStack c or Reveal c)
   - Doesn't affect c's pile (since m moves cards from other piles)
   - Therefore, m is also legal before the reveal
   - AND the reveal is also legal after m
3. So m and the reveal commute: do m first, then reveal c, and you
   reach the same state as doing reveal c first, then m.
4. Therefore, the reveal dominates m (doing the reveal first is
   at least as good, since it reveals information sooner).
-/

/-
=========================================================================
  Rule 4: DeckPile dominance — After drawing from stock to tableau
=========================================================================

After a DeckPile move (drawing card c from the stock to a tableau pile),
the FullPruner prunes:
- PileStack: only c.swapSuit is kept (in addition to what's already
  pruned by other rules)
- Reveal: prunes cards not in (c ∪ c.swapSuit) shifted by one rank,
  unless they're first-layer hidden cards

The intuition for PileStack: after drawing c, the only NEW thing you
can do is move c or interact with c. Moving c.swapSuit to the foundation
is relevant because c.swapSuit has the same rank and color as c — they
are interchangeable by suit symmetry (SuitSymmetry.lean). But any other
PileStack was available before the draw and commutes with it.

For Reveal: revealing a card that doesn't interact with c's rank
is less important than making use of the drawn card. The drawn card
is a "forced" event (the deck cycles deterministically), so you
should make use of it before it becomes buried again.
-/

/-- After a DeckPile of card c, any PileStack move not involving
    c.swapSuit was also available before the draw. -/
theorem deck_pile_pilestack_dominance (s : GameState) (c : Card)
    (h_dp : s.doMove (Move.deckPile c) = some s') :
    ∀ c', c' ≠ c.swapSuit →
      s'.doMove (Move.pileStack c') = some s'' →
      ∃ s''', s.doMove (Move.pileStack c') = some s''' := by
  sorry -- TODO: Requires game state reasoning

/-
Proof strategy:
1. DeckPile c moves card c from the waste to a tableau pile.
2. Any PileStack c' (c' ≠ c.swapSuit) moves c' from its pile
   to the foundation. This move:
   - Doesn't involve the drawn card c (since c' ≠ c and c' ≠ c.swapSuit)
   - Doesn't affect c's new pile position
   - Was available before the draw (the draw only changes the deck,
     not the piles that c' is on)
3. Wait — actually, the draw might have changed which pile c' goes on,
   if c' was the card we drew. But we assumed c' ≠ c.swapSuit, so
   this doesn't apply. Hmm, actually c' could have been on the pile
   where c was placed... but PileStack moves c' from its CURRENT pile
   to the foundation, which is independent of where c was placed.
4. So PileStack c' commutes with DeckPile c when c' ≠ c.swapSuit.
   Therefore, doing PileStack c' first and then DeckPile c reaches
   the same state (modulo the draw timing, but since the deck is
   deterministic, the same card c is drawn).
-/

/-
=========================================================================
  Summary: Composition of all pruning rules
=========================================================================

The FullPruner combines all four rules. Since each rule independently
preserves solvability, and the rules are composed by union (MoveMask
OR), the combined pruner also preserves solvability.
-/

/-- The full pruner (combining cycle + reveal_empty + reveal_card +
    deck_pile dominances) preserves solvability. -/
theorem full_pruner_sound (s : GameState) :
    ∀ m, FullPruner.shouldPrune s m = true →
      Solvable (s.doMove m |>.get _) →
        ∃ m', FullPruner.shouldPrune s m' = false ∧
          Solvable (s.doMove m' |>.get _) := by
  sorry -- TODO: Compose the individual soundness proofs

end Klondike
