# Macro (commitment) formalization — proof notes

Working document for replacing the 5-move engine game with a commitment game of
two moves, together with the theorems needed to prove it exact.

Legend: [x] established / [~] claimed & cross-validated, proof pending / [ ] open

Line references are pinned to commit `5146b98` and *will* drift — prefer
searching by function name.

Build sequencing (recorded): Phase 0 — falsifiers on the *current*
engine; Phase 1 — the architecture-independent spine (the reshape lemma,
T, L1/L2, the safe-stack port); Phase 2 — this game, gated on verdict
equality with the current engine. See the interaction doc's §8 and the
soundness ledger's migration plan.

## 0. Claims

- **C1 (Reduction).** The old game can be replaced by a commitment game with two
  moves — `Draw(d)` and `Reveal(c)` — where all reversible pile↔stack shuffling
  is absorbed into a computed *accommodation* per commitment. Solvability is
  preserved (both directions).
- **C2 (Bound).** Each commitment, applied to a state, yields at most **2**
  distinct post-states (in the engine's state abstraction):
  {target card lands on the tableau, target card lands on the stack}.
  (Sharpened and measured in §6: the true form is ≤2 *reversible-closure
  classes* per commitment; state-level multiplicity is unbounded.)

Supporting theorems:

- **T (Twin swap).** Local shuffling of same-color suits within the piles
  preserves solvability.
- **A (Accommodation reduction).** Accommodating a commitment requires only
  stack↔pile shuffling.

## 1. Preliminaries: the engine's state abstraction

A state records (src/state.rs:451-459):

- the stack (foundation) height of each suit (16 bits),
- the size of each pile's *hidden structure* — the dealt cards not yet revealed
  (16 bits, per-pile counts only; identities are *not* encoded),
- the deck order and draw offset (29 bits),
- the set of visible tableau cards — kept in the runtime struct, but not
  part of the encode (re-derived as the complement on decode).

Two things are deliberately **not** recorded:

1. *Where* a visible card sits (which pile, in which run). Moves mutate only the
   visible set: `DeckPile`/`StackPile` just add to `visible_mask`
   (src/state.rs:365-393), `PileStack` removes from it, and `Reveal(c)` pops
   the structure under `c` while `c` stays in the visible set (src/state.rs:395-402).
2. *Which* cards remain in each pile's hidden structure (only the sizes are
   encoded, src/hidden.rs:195-204).

Rules facts used throughout:

- Tableau stacking depends only on (rank, color): a card of rank r, color c̄
  lands on a card of rank r+1, opposite color. Suit-within-color matters only to
  the stack (foundation prefixes are per-suit).
- The stack per suit is always a prefix A..f(s), so "card is stackable" =
  `f(suit(card)) == rank(card)` (src/stack.rs:48-50; ranks are 0-indexed —
  height f means ranks 0..f−1 are stacked, so the next acceptable card has
  rank exactly f).
- There are no tableau↔tableau moves except the surface reveal
  (gen_moves emits none; the reveal mask is `vis & locked & free_slot`,
  src/state.rs:293). Call this inherited fact **A1**; it is cross-validated
  (README: 1M Solvitaire seeds, Klondike-solver seeds 0..50k).

## 2. Lemma A — the accommodation reduction [x]

**Lemma A1 (commitment partition).** Every irreversible move introduces either
a deck card (`DeckPile`, `DeckStack`) or a hidden card (`Reveal`,
`PileStack`-on-locked = reveal-by-stacking). This is exactly the classification
of `reverse_move` (src/state.rs:312-321): only `PileStack` (unlocked) and
`StackPile` are reversible.

**Lemma A2 (reversible fragment).** A move sequence with no commitment in it
consists solely of `PileStack`(unlocked)/`StackPile`. Such shuffles preserve
the deck and the hidden structures, and change only pile tops and stack tops.
Pops are allowed only from pile tops that are stackable; pushes only land on
compatible tops (or king→empty).

**Lemma A3 (accommodation reduction).** Fix a state s and a commitment m:

- `Draw(d)`: the target card is X = d;
- `Reveal(c)`: the target card is X = c — the *departing* surface card. (The
  newly revealed card r inherits c's place and needs no destination of its own.)

Then m is executable from s iff some shuffle σ of the reversible closure of s
gives X a legal destination (compatible tableau top, king→empty, or stackable).
Any old-game play therefore regroups as
shuffle, commit, shuffle, commit, ..., which is precisely the macro game.

*Proof.* (⇐) shuffles are legal moves, and m is legal at σ(s). (⇒) between two
consecutive commitments of any play, every move is reversible (A1), hence is a
shuffle (A2); the commitment's legality is evaluated at the state where it is
made. Completeness of "shuffling is the only accommodation mechanism" rests on
A1. ∎

Consequence: macro search = for each candidate commitment (each drawable d,
each surface c), decide whether an accommodating shuffle exists, and
characterize the post-states.

### Structural facts for reasoning about accommodations

- **(F1) Two twins only.** For target X of rank r, color c̄, the tableau
  destinations are exactly the two cards of rank r+1, opposite color — the
  twins Y, Ȳ. Each is in exactly one of: pile top (ready), buried in a pile,
  on the stack, in the deck, or still hidden.
- **(F2) Segment transfer.** Unstacking a deep card from the stack forces
  unstacking everything above it in that suit first; that foundation segment
  forms a valid run, and landing the whole segment on a single compatible top
  is one composite action. Any *split* of the segment needs at least the same
  destination for its top card, which the whole-segment landing also uses.
  (The claim that whole-segment landing dominates all splits still needs a
  proof — see O5.)
- **(F3) Forced sweep.** When a dominantly-safe stack move exists, the engine
  already treats stacking as forced and returns it as the only move
  (`pile_stack_dom`, src/state.rs:176-183; safety = min over same-color twin
  suit heights, `Stack::dominance_mask`, src/stack.rs:26-32).

## 3. Theorem T — twin swap (local same-color suit shuffling) [~]

**Statement (to be confirmed, see O1/O2).** Let X and X̄ be two cards of the
same rank and same color, different suits (e.g. 8♠ and 8♣). If **both** reside
in the tableau piles (anywhere: visible runs, surfaces, or hidden in
structures), then the two games differing by exchanging the positions of X and
X̄ are solvability-equivalent. Equivalently: local shuffling of same-color
suits within the piles preserves solvability.

**Why the hypothesis has force.** If both twins are in the piles then neither
is on the stack, so both foundation heights of that color are < rank(X) — there
is room to re-interleave the two suits' foundation prefixes. The deck is
untouched by the swap, so the draw order is identical in both games.

**Roles in the engine today.**

1. Exactness of the state abstraction: the encode forgets arrangement and
   hidden identities; same-encode concrete positions are related by local
   suit shuffles, which T says are solvability-equivalent. Without T the
   transposition table (src/traverse.rs:81) could skip a winning state.
2. Dominance pruning of twin choices: the `paired_stack` / `least_stack` /
   `suit_filter` block (src/state.rs:222-286) only searches the canonical
   twin; the post-reveal filter allows stacking {c, twin(c)}
   (src/pruning.rs:90-102).
3. Foundation safety dominance: `Stack::dominance_mask` (src/stack.rs:26-32).

**Proof strategy (to write out).**

Take a winning play P for the game with X at position p, X̄ at position q;
build a winning play P' for the swapped game. Transform P by *position-based
relabeling*: whenever P moves the card at position p (which is X), P' moves the
card at the same position (which is X̄), and vice versa; all other moves are
unchanged. Legality of non-twin moves is unaffected:

- tableau legality is (rank, color)-based, and twins agree on both;
- stackability of a non-twin card depends only on its own suit's foundation
  height, which is untouched by the relabeling while both twins remain
  un-stacked.

The only obstruction is the *stack asymmetry*: when P stacks X (say X♠, needing
f(♠) = r−1 at that moment), P' wants to stack X♣ at the same position, needing
f(♣) = r−1 — which may not hold yet. Bridge it with the interleaving lemma:

- **(L1, interleaving).** The tableau is color-blind, so the order in which the
  two same-color suits climb their foundations can be exchanged arbitrarily,
  subject only to per-card accessibility, and accessibility of a card does not
  depend on the interleaving (its blockers are removed by their own stacking
  or by reveals, in an order that can be carried along).
  ⇒ P' can first raise the ♣ prefix to r−1 (replaying, in its own suit, the
  "unbury" structure P used to raise the ♠ prefix), then stack X♣, and
  continue.

Proof obligations / open items:

- **O1.** Locality: is the swap restricted to *within one pile*, or between any
  two pile positions? (C2 needs the destination-collapse version: placing X on
  twin top Y vs Ȳ — but note both yield the same `Encode`, so this may not
  even need a cross-pile swap; see §4.)
- **O2. Hidden twins — discharged** (no_pile_to_pile.md §1): within a
  game, a pile's hidden structure is always a prefix of the original deal,
  so the per-pile counts pin the hidden identities. The encode's hidden
  amnesia therefore never conflates different hidden arrangements within
  a game, and T is not needed for hidden cards. What remains of O2 is the
  *cross-game* question (two deals differing by a hidden twin swap), which
  is the local-shuffling statement of T itself.
- **O3.** Boundary case: f(♠) = r−1 but f(♣) < r−1 (one twin stackable now,
  the other not) — the interleaving lemma must cover it.
- **O4.** Formalize in Lean (lean-verify/), next to the existing Klondike
  model; brute-check against the ref_graph CSVs.
- **O5.** Segment-split dominance (F2).

## 4. C2 via T — at most 2 outcomes per commitment [~]

Let m be a commitment with target card X (rank r, color c̄). The outcomes:

1. **Tableau outcome.** X lands on a tableau pile. By F1 there are at most two
   destination cards (the twins Y, Ȳ), and:
   - both landings produce the *same engine state* (same visible set, same
     structure sizes, same stack, same deck) — the placement position is not
     part of the state;
   - T guarantees that merging these two concrete landings is exact.
2. **Stack outcome.** X is stackable and is stacked instead (`Reveal(c)` via
   stacking c = the old `PileStackReveal`; `Draw(d)` straight to the stack = the
   old `DeckStack`). This is a genuinely different state (stack height +1,
   X leaves the visible set).

Hence at most 2 distinct post-states per commitment, matching the "two possible
choices for the stack configuration". Additional collapsing:

- If X is *dominantly* stackable (F3), the tableau outcome is dominated and the
  commitment has a single outcome.
- Accommodation-side choices (which twin to unbury, where a worried-back
  segment lands) collapse the same way: each accommodation chain targets one
  specific twin card, and by T the twin choice is WLOG.

Open: prove that the accommodation itself contributes no extra state choice
(minimality of the forced stacking set — see O6), and the terminal sweep:

- **O6.** Minimality/uniqueness of the accommodation: two different minimal
  accommodating shuffles must yield the same post-state, or be dominated.
  (Resolved into §6.3–6.5: an operational canonical form + an in-tree
  falsifier.)
- **O7.** Terminal handling: the last commitments do not empty the tableau by
  themselves; specify the `Finish` pseudo-macro (stack sweep until stuck, win
  iff all 52 stacked) and its interaction with `is_sure_win`
  (src/state.rs:444-447).

## 5. Empirical companion (runs alongside the proofs)

- **Differential checker.** For states sampled from real games and solver
  runs: enumerate the old-formalism candidates (the `ListStatesCallback`
  traversal, src/mcts_solver.rs:58-83) and assert every candidate end-state is
  `equivalent_to` one of its commitment's ≤2 outcomes, and every macro script
  is legal in the old game. Any mismatch is a hole in T, A, or the old
  dominance rules.
- **Full-corpus verdict cross-check.** Old solver vs macro solver on the
  Solvitaire 1..1M sample and Klondike-solver 0..50k; verdicts must match
  exactly.

## 6. The closure algebra and the efficient transition
(derived 2026-09, with the first in-tree measurements; probe code
`src/macro_game.rs`, branch `macro-game`)

This section turns the scaffold measurements into the design theory for a
*direct* transition function: the point of the rework is that macro move
generation and state transition must be constant-work-per-commitment, not a
closure exploration. The algebra shows that this is possible.

### 6.1 The closure, algebraically [~; shape measured]

By A2, the reversible closure of `s` consists exactly of the states obtained
from `s` by shuttling *unlocked* cards between tableau and foundation; deck
order+offset and the hidden structures are invariant. Therefore, in a
closure state:

- deck and hidden are fixed;
- per suit, the foundation content ranges over a **height interval** (only
  prefix digs are possible — F2);
- the visible/top changes come only from worried-back cards (a worried-back
  card becomes a top, and covers the top it landed on).

Measurement confirming the shape (probe `macro_scaffold_smoke`): outcome
post-states of one commitment vary only in the *stack* component, forming
per-suit interval lattices (e.g. `[2000, 1000, 0]`, `[320, 220, 120, 210]`
— nibble-lattices over two suits), with hidden and deck parts constant.
State-level multiplicity is **not bounded by 2 or 4** — floating worry-back
coordinates multiply out (an 8-state grid was observed) — which forces the
corrected C2 of §6.3.

### 6.2 Locality lemma [x — formula arithmetic]

For commitment target `X` (rank `r`, color χ): covering a destination twin
`Y` requires a card of type `Y − 4`, which is rank `r`, color χ — i.e. the
type of `X` itself: `{X, twin(X)}`. As `X` is in flight during its own
commitment, **the only pre-existing blocker of `X`'s landing in the whole
deck is `twin(X)`**. This is the "never a third suit" observation in exact
form: a commitment's interference zone is one type.

### 6.3 C2, corrected and measured [~]

- **State-level ≤ 2 is false, and the two-twin-neighborhood "≤ 4" is not
  the right level either** — free floats form products. The true claim:
  *each commitment has at most 2 post-state **closure classes***
  (tableau-kind, stack-kind).
- **Free-float collapse.** A float outside the commitment's type
  neighborhood (type `X`, `X±4`) has its flip-legality masks untouched by
  the commitment's placement, so the shuffle separating two accommodation
  variants remains legal after the commitment: free variants are mutually
  reachable post-commitment, hence one closure class. (Modulo the same
  type-neighborhood mask check as L1/L2 — mechanical; pending.)
- **Measurement.** Quotienting post-states by mutual reversible
  reachability (`closure_classes`, `closure_contains`): across 200 games of
  greedy macro play (default_shuffle seeds 12..111, draw 1 and 3),
  ≈4.5k commitment points, **max distinct closure classes per commitment =
  2 — zero violations**. The probe asserts this in-tree; a value ≥ 3 is the
  falsifier.
- **What is left of C2.** The interacting corner: only `twin(X)` can be
  frozen by the commitment (e.g. on a stack outcome, `f(suit(X))` moves past
  `r`, killing `twin(X)`'s own stackability). The remaining case list —
  `twin(X)` ∈ {stacked, on `Y`, on `Ȳ`, free} — is where the dominance
  eliminations (5.1/5.4: "a dominant card is never available for worrying
  back"; minimality of the accommodation) remove the extra configurations.

### 6.4 The availability algebra [~]

Whether an outcome shape exists for target `X` at the raw state reduces to
a **well-founded recursion over types**, not a search. Cases for the tableau
outcome (need an uncovered top of type `X+4`):

1. **Direct** — `bm[X+4]` holds (type-level, already `X ∈ free_slot`).
2. **Dig** — `Y` is covered; its coverer is `twin(X)` (forced by §6.2),
   which is then a top; vacating it = stacking it (`sm[twin(X)]` — a
   foundation prefix fact) or, if a king, moving to an empty pile.
3. **Borrow** — a `P`-twin sits on its suit's foundation top; worry it back
   (`SP` needs an uncovered top of type `X+8` — the same question one rank
   up, same color).
4. **Deeper dig** — `twin(X)` itself is covered; coverers descend in rank
   and flip color per level; the recursion bottoms out at **aces**, which
   are never coverable.

Borrows ascend toward kings (which terminate at holes); digs descend
toward aces. So availability is a monotone, rank-bounded AND-OR computation
over ≤ 26 types — no closure exploration. The stack outcome is the same
machinery: `X` is stackable now, or becomes so after raising the prefix —
each missing prefix card needs the very same one-card dig, descending to
aces.

**Completeness is the open part**: that these four cases exhaust the
closure's ways of producing a landing is conjectured from §6.1 + §6.2;
chained borrows are the untested crease. This is exactly the falsifier of
§6.6.

### 6.5 The representation fact [x — engine invariant]

The abstract moves are total, arrangement-free functions of the abstract
state; their preconditions are answered at type level by the masks (§3 of
`no_pile_to_pile.md`); and the type level is *per-card exact* exactly where
it matters: while `X` is off-tableau (deck, hidden), `bm[type(X)]` says
whether `twin(X)` specifically is an uncovered top, the parity over a single
visible twin being exact. Hence:

> The transition function needs no new state: the 61-bit encode plus the
> existing runtime arrays suffice. A macro transition is a short
> deterministic program of ordinary abstract moves (the dig/borrow sequence
> from §6.4) followed by the safe-sweep canonicalization (F3 repeatedly —
> already what `canonicalize` does in `src/macro_game.rs`). No closure DFS,
> no closure-class clustering, no per-card arrangement at generation time.
> Per-node expansion cost: `#drawables + #surfaces` times constant-bounded
> rule work.

### 6.6 The falsifier for the design

`macro_transitions_direct` (to implement: rules of §6.4 producing the
post-state by executing the short move sequence + sweeping) differentially
against the closure-oracle `enumerate_commitments` (already in-tree):
availability and canonical post-state must agree per commitment per state
over the corpus; log the first divergence — that is either a missing rule
case (extend §6.4) or a defeat of the design, in which case the closure
torus is semantically necessary and the fast path is refuted.

### 6.7 What §6 implies for the open items

- **O6** has an operational answer already measured: canonical form = safe
  sweep + closure-quotient; uniqueness of the canonical post-state per
  commitment-kind is the confluence of the §6.4 priority order (direct >
  dig > borrow > king-hole) — testable by the §6.6 differential.
- **O5** (can every accommodation be reduced to the sweep?) is replaced by
  the sharper question: is the §6.4 rule list complete? The same §6.6 test
  decides.
- The remaining open items here (O1/O3/O5, and O7's terminal sweep) become
  boundary cases to encode into the §6.4 rule list rather than separate
  hazards; the interaction doc's register keeps the cross-cutting ones.
