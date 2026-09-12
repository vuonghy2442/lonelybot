# The method behind lonelybot (informal notes)

This is the detailed description of the *current* method — the one behind the
published results — written down before the macro/commitment rework (see
[macro_formalization.md](macro_formalization.md) for that work in progress).
Everything here refers to the code as of version 0.2.x.

It is informal on purpose: statements are precise, proofs are sketches, and a
few places I could not fully reconstruct from code alone are marked
`TODO(vuong)` for the author to fill in.

Line references are pinned to commit `5146b98` and *will* drift — when in
doubt, search for the function name. The companion docs
[macro_formalization.md](macro_formalization.md) and
[pruning_dominance_interaction.md](pruning_dominance_interaction.md) follow
the same convention.

## Contents

1. [The two problems being solved](#1-the-two-problems-being-solved)
2. [State representation](#2-state-representation)
3. [Moves and legality](#3-moves-and-legality)
4. [The twin-swap theorem](#4-the-twin-swap-theorem)
5. [Dominance rules in move generation](#5-dominance-rules-in-move-generation)
6. [Path-dependent pruning (the pruners)](#6-path-dependent-pruning-the-pruners)
7. [The search](#7-the-search)
8. [The random (no-undo) player](#8-the-random-no-undo-player)
9. [Why it all works — the informal argument](#9-why-it-all-works--the-informal-argument)
10. [Verification status](#10-verification-status)
11. [File map](#11-file-map)

## 1. The two problems being solved

- **Thoughtful Klondike** (full information): every card is visible,
  including the order of the stock and the face-down tableau cards. Question:
  *is the deal solvable?* Solved exactly by exhaustive search
  (`src/solver.rs`). Result: 81.95% ± 0.03 of 3-card games are solvable
  (5.9M-game Klondike-Solver-seed run; the 1M-game Solvitaire-seed run gives
  81.93% ± 0.075), state of the art.
- **Random Klondike** (hidden information, no undo): you only see what a
  real player sees; moves cannot be taken back. Question: *play to maximize
  win rate.* Solved with determinized search + a bandit
  (`src/hop_solver.rs`, `src/mcts_solver.rs`). Result: 47.58% ± 0.80 win rate
  over 15,024 games, vs 36.97% ± 1.92 previously published.

Both run on the same board representation and the same optimized move
generator, which is where most of the speed comes from.

## 2. State representation

### 2.1 Cards: one bit each, in a trick layout

A card is a 6-bit index into a 64-bit "card set" mask (`src/card.rs`). The
index is not `rank * 4 + suit`; it is that value with the color bit XORed
with the low bit of the rank:

```
let v = rank * 4 + suit;      // (parenthesized to avoid precedence confusion)
index(card) = v ^ ((v >> 1) & 2)
```

Consequences of this layout (all verified against `SUIT_MASK` etc.):

- **bit 0** selects between the two suits of the *same color and rank* — the
  *twin*. `swap_suit() = index ^ 1`.
- **bit 1** is the color, flipped by rank parity. `swap_color() = index ^ 2`.
- `index − 4` is the card this one sits on in a valid run (one rank lower,
  opposite color): `reduce_rank_swap_color()`. This makes "is X stackable on
  Y" a one-instruction test: `((x + 4) ^ y) < 2` (`Card::go_after` — `< 2`
  tolerates either twin of the destination color).
- The four cards of a rank occupy one nibble; `RANK_MASK = 0x1111…` selects
  one bit per rank; `* 0b11` duplicates a per-type bit into its twin bit.

Almost every set operation in move generation is a shift/mask/xor on these
u64 card sets. That is the source of the ~10M move-gens/sec single-core rate.

### 2.2 The four components (`src/state.rs`, `src/stack.rs`, `src/deck.rs`, `src/hidden.rs`)

- **Stack** (foundation): `u16`, four nibbles = per-suit height. Always a
  prefix `A..f(suit)` per suit, so "card is stackable" is
  `f(suit) == rank(card)`.
- **Hidden structure** (`Hidden`): for each pile, the dealt cards not yet
  revealed, bottom-to-surface. Stores identities at runtime (plus a
  card→pile map, the locked mask = all structure cards, and the first-layer
  mask = deepest card of each pile), but **encodes only the per-pile
  counts**.
- **Deck**: the 24 stock cards in order, plus `draw_cur` (how many have been
  dealt to the waste), a live bitmap of which positions remain, and a
  card→position map. Drawing pops from the waste end; `iter_callback`
  enumerates the positions a card could be drawn from *given repeated
  dealing* (every `draw_step`-th position of the current pass, the last card,
  and — without the filter — the previous pass); `compute_mask` turns that
  into the set of drawable cards. `is_pure` says the offset is aligned so a
  full deal cycle returns to the same partition.
- **Visible set**: a u64 mask of tableau-visible cards — stored as the fourth
  field of `Solitaire` (src/state.rs:24) and maintained incrementally by
  do/undo, but deliberately excluded from `Encode` and re-derived via
  `compute_visible_mask` on `decode`.

### 2.3 What is deliberately *not* in the state

This is the big design decision. The state does **not** record:

1. **Where a visible card sits** (which pile, which position in the run).
   `DeckPile`/`StackPile` just add the card to `visible_mask`
   (`make_pile`, src/state.rs:365); `PileStack` removes it; `Reveal(c)` pops
   the structure under `c` and leaves `c` in the visible set.
2. **Which cards are still hidden in which pile** (only the per-pile counts
   are encoded, `Hidden::encode`).

Two concrete positions that differ only by such details get the same
`Encode` — a 61-bit key: stack (16) | hidden counts (16) | deck (24-bit
bitmap + 5-bit offset, src/deck.rs:271). The transposition table is a
`HashSet<Encode>` with a bijective fasthash64-style mixer
(`MixHasher`, src/utils.rs) — a u64-to-u64 bijection, so zero hash
collisions.

Why forgetting is *sound* is the content of §4 (twin swap) and §5
(dominance); see also §9.

## 3. Moves and legality

### 3.1 The five moves (`src/moves.rs`)

| Move | Meaning | Reversible? |
|---|---|---|
| `PileStack(c)` | tableau card → foundation | iff `c` is *not* in the hidden structure (unlocking a locked card reveals, and reveals cannot be undone) |
| `StackPile(c)` | foundation top → tableau | yes |
| `DeckStack(c)` | drawn card → foundation | no (the draw cannot be undone) |
| `DeckPile(c)` | drawn card → tableau | no |
| `Reveal(c)` | move surface card `c` away, flip the card under it | no |

At most 24 moves per state (`N_MOVES_MAX`).

Two consequences of this move set are load-bearing for everything else:

- **The only pile↔pile move is `Reveal`, and only for surface cards.** A
  *placed* card (one that came from the deck or the foundation) can only ever
  leave its pile by going to the foundation. This is the engine's biggest
  dominance bet; it is cross-validated (§10) but not formally proven.
  TODO(vuong): this deserves its own writeup — it is the theorem that makes
  the state graph finite/small.
- **Reversibility partitions moves into "shuffles" and "commitments"**
  (`Solitaire::reverse_move`, src/state.rs:312). Every irreversible move
  either introduces a deck card (`DeckPile`, `DeckStack`) or flips a hidden
  card (`Reveal`, `PileStack`-on-locked). The random player and the planned
  macro rework are both organized around this partition.

### 3.2 Set-based legality (`gen_moves`, src/state.rs:160)

Because positions are not tracked, legality is computed from *sets*. The
central derived quantity is `bm` (`get_bottom_mask`, src/state.rs:115):

> `bm` = the set of (rank, color) types that have an *uncovered* card — a
> card that nothing is placed on — i.e. a card that can be picked up.

For a type `t`, "covered" means a *placed* card of the rank-below type (rank−1,
opposite color) sits on top of it — placed cards are the only coverers, and a
placed card of type `t−4` covers exactly one card of type `t`, so counting
mod 2 per twin pair does the job:

- `xor_vis ^ (xor_free << 4)` per type compares the parity of present twins
  of `t` with the parity of *placed* cards of the rank-below type;
- `| !(or_free << 4)` handles the "nothing placed below at all" case;
- `& or_vis` requires a visible card of the type at all (without it, an
  absent type with nothing placed below would look movable);
- `& ALT_MASK * 0b11` picks a canonical twin and re-expands to the pair.

Worked micro-example: type `t` has one visible twin, and one placed card of
the rank-below type exists → parity says the only `t` card is covered → `bm`
excludes `t`. Two visible twins, one placed rank-below card → one twin is
covered, one is free → `bm` includes `t` (the mask does not say *which* twin —
that is the arrangement abstraction again). Note that adding placed cards can
only *reduce* movability of the type they cover — a monotonicity fact that
the interaction analysis leans on (see
[pruning_dominance_interaction.md](pruning_dominance_interaction.md)).

The rest of move generation composes `bm` with:

- `sm` = the four "next" foundation cards (`Stack::mask`);
- `dom_sm` = the safely-auto-stackable ones (`Stack::dominance_mask`, §5.1);
- `free_slot = (bm >> 4) | king_mask` = the set of cards that have a landing
  spot (their run-parent is uncovered), plus kings if any pile is empty;
- `deck_mask` = drawable cards (`Deck::compute_mask`).

and produces the five masks:

```
pile_stack = bm & vis & sm                 // movable & stackable
deck_stack = deck_mask & sm                 // drawable & stackable
stack_pile = swap_pair(sm >> 4) & free_slot & !dom_sm   // foundation tops with a landing spot
deck_pile  = deck_mask & free_slot & !(dom_sm & sm)
reveal     = vis & locked & free_slot & !(first_layer & KING_MASK)
```

(`swap_pair(sm >> 4)` maps each suit's next card to the current foundation
*top* of the same suit — the unstackable card.)

### 3.3 Concretizing for display/compat (`src/convert.rs`)

Engine moves are legal iff *some* concrete arrangement realizes them. To print
or export a solution in standard notation, `convert_move` reconciles with a
concrete board: a `Reveal` becomes a pile→pile move; a `DeckPile` becomes
`k` draw-nexts plus a placement; a `PileStack(c)` whose card has something on
it in the concrete layout first moves that card to another pile, then stacks
`c`. `StandardSolitaire` (`src/standard.rs`) is the explicit-piles facade used
for this and for the Solvitaire-format printer.

## 4. The twin-swap theorem

> **Theorem (twin swap, informal).** Let X and X̄ be two cards of the same
> rank and same color (e.g. 8♠ and 8♣). If **both** are in the tableau
> piles, then exchanging their positions preserves solvability. Equivalently:
> local shuffling of same-color suits within the piles is exact.

Why it is plausible (informal argument, to be written out properly — see the
proof notes in [macro_formalization.md](macro_formalization.md) §3):

- The tableau subsystem is color-blind: run validity, destinations, and
  reveal legality only depend on (rank, color). Twins are indistinguishable
  to the tableau.
- If both twins are in the piles, neither is on the foundation, so both
  foundation heights of that color are below `rank(X)` — there is room to
  re-interleave how the two suits of a color climb their foundations.
- The deck is untouched by the swap, so the draw order is identical.

Given a winning play for one position, relabel the twins position-wise and
exchange the interleaving of the two same-color foundation prefixes where the
stacked suit differs; tableau legality is preserved because it never looked
at the suit-within-color in the first place.

Roles in the engine:

1. **Exactness of the state abstraction.** The `Encode` conflates concrete
   positions that differ by hidden identities and (via the set-based
   legality of §3.2) by arrangement; twin swap is what makes "same Encode ⇒
   same solvability" true, which the transposition table relies on.
2. **Canonical twin choices.** When two twins are both options (stack either,
   place on either), the dominance rules of §5 only explore the canonical
   one.
3. **Safe stacking.** The threshold's twin-suit `r−2` conjunct is the
   classical condition for worry-back games (§5.1 and
   [pruning_dominance_interaction.md](pruning_dominance_interaction.md)
   §2.5) — not an engine relaxation; the twin-swap machinery is what makes
   the engine's arrangement-free port of it plausible.

## 5. Dominance rules in move generation

`gen_moves::<true>` (src/state.rs:160) applies the following cascade. Each
rule replaces the move set with a subset that is provably (or
cross-validated-ly) sufficient. This is where most of the state-space
reduction lives — roughly an order of magnitude versus the naive generator.

### 5.1 Forced safe stacking

```
dominance_mask (src/stack.rs:26):
  a card of rank r and color c is safe ⟺ min over suits of c  ≥ r−2
                                     and  min over suits of c̄ ≥ r−1
```

If any visible, movable card is in `dominance_mask`, *stack it* — the
generator returns only that move (lowest bit). Informal argument: a safe
card can always be brought back ("worried back") later, so stacking it
loses nothing that is not reachable again by shuffling; stacking it also
strictly grows the foundation, so it is progress. The threshold itself is
the classical safe-automove condition for worry-back games (Blake & Gent,
JAIR 85, 2026 — see
[pruning_dominance_interaction.md](pruning_dominance_interaction.md) §2.5:
the twin-suit `r−2` conjunct is *not* an engine relaxation; the stronger
`f_opp ≥ r` variant applies only without worry-back). Solvitaire implements
this same rule (the paper proves it correct in Appendix B.1), so the
engine's edge over it comes from the other layers — the suit symmetry,
the arrangement abstraction, the pruners — not from this threshold.
Engine-specific and still
open (TODO(vuong)): the port to the arrangement-free state — the shape is
channels A/B in the interaction doc §4.

### 5.2 Three-or-more redundant stackables

`redundant_stack = pile_stack & !locked` = stackable cards that do not reveal
anything (not in the structure). If ≥3 of them exist, only the lowest is
generated. Idea: with that many interchangeable "free" stacks available in
both colors, stacking the lowest one is a canonical representative; the
others remain available later (stack moves into the foundation commute, and
what is safe is recoverable by §5.1's argument).

### 5.3 Deck dominance

If the *last* card of the waste (the one the deal cycle ends on) can be
stacked safely and the deck is `is_pure` (the offset aligns so dealing
cycles back to the same partition), only that draw-and-stack is generated.
Idea: with a pure deck, drawing around the cycle to reach that card does not
lose any draw-order information, and the safe stack is free progress.

For `draw_step == 1` there is a separate, simpler case (`get_deck_mask`,
src/state.rs:136): if *any* drawable card is dominantly stackable, only the
lowest such card is returned — with one card per draw every card is equally
reachable, which is why the code itself comments that this is "not very
useful as dominance".

### 5.4 Unstack only what is not safe to restack

`stack_pile &= !dom_sm`: never worry back a card that is *dominantly
stackable* — it would (or could) immediately go back up; the shuffle is
pointless. (This is also why `deck_pile` excludes `dom_sm & sm`: never draw a
card to the tableau if it could safely go to the foundation.)

### 5.5 Twin-pair collapse

If a stackable card and its twin are both unnecessarily stackable
(`paired_stack`), the generator keeps only the pair (both bits — the twin
choice inside the pair is exactly the twin-swap equivalence), zeroes
`deck_stack` (no drawing while free stacks are pending), and restricts
`free_slot` to placements *onto* the pair cards (`free_slot = rm >> 4` — the
cards that can sit on the pair). This is the direct application of §4 as a
dominance rule.

### 5.6 The least-stack cascade

When there are stackable non-revealing cards but no pair, only the lowest
one (canonical twin) is kept, and:

- `stack_pile` is restricted to lower-ranked, cross-colored suits filtered to
  avoid creating a third unnecessary stackable of the same rank
  (`triple_stackable` = cards that could *become* stackable next move);
- `deck_stack` is zeroed;
- `free_slot` only unlocks new placements (onto the least card) when the
  opposite-color cards of the least card's rank are not themselves redundant
  (`(least << 2) & redundant_stack == 0` — `<< 2` is the same rank,
  opposite color).

If neither color has an "unstackable" stackable suit (`suit_unstack` fails
for one of the colors), the branch is more aggressive still: `stack_pile`,
`deck_stack` *and* `free_slot` are all zeroed, leaving only the least stack —
the "double card color" case (src/state.rs:282-285).

The in-code comments (src/state.rs:222-286) narrate the intent: prevent
making "double same color", which would in turn create three unnecessary
stackables. TODO(vuong): the full informal argument for this cascade —
it is the most intricate dominance in the file.

### 5.7 King and empty-pile rules

- Kings only enter `free_slot` when a pile is actually free
  (`get_extended_top_mask` counts "tops or kings").
- `reveal` excludes first-layer kings: moving a king that sits at the very
  bottom of its pile to another empty pile is a pure empty-pile shuffle.

## 6. Path-dependent pruning (the pruners)

On top of the dominance rules (which are functions of the state alone), the
`Pruner` (src/pruning.rs) carries the last move's context and removes more
moves. This makes the successor relation *path-dependent* — the price paid
for cutting the state graph down to "a DAG modulo 2-cycles".

### 6.1 CyclePruner

Remove the immediate reverse of the last move (breaks all 2-cycles — the
`PileStack`/`StackPile` flip-flops).

### 6.2 After a pile-emptying reveal

`(Reveal(_), RevealEmpty)`: the reveal emptied a pile. The next move must be
a king placement (unstack a king, draw a king, or reveal-move a king into
the hole); all foundation moves are removed. Argument: a non-king move after
the emptying cannot use the new empty pile (only kings land on empties), so
it commutes with the reveal — reorder it before the reveal. Hence either a
king follows immediately, or the emptying reveal is deferred/never made.

### 6.3 After any other reveal

`(Reveal(_), Card(r))` where `r` is the freshly revealed card: the only
allowed foundation move is stacking `r` or its twin; `deck_stack` is removed.
Argument: foundation moves commute with each other (stacking `r` exposes
nothing that buries another stackable), so if the revealed card is going to
be stacked at all, stack it first; if it is not stackable, no foundation move
is available until the position changes — which the search then explores
from a different path.

### 6.4 After a draw-to-pile

`last_draw` tracks the most recently drawn card placed on the tableau. It is
kept across `StackPile`s that land *elsewhere*, and is cleared by any other
foundation move, by any reveal, and — notably — by a `StackPile` that lands
*directly on top of* the drawn card: once something is built on the fresh
card, the draw-order window the rule guards is closed. While it is set:

- the only allowed `pile_stack` is the *twin of the drawn card*
  (src/pruning.rs:114). The general principle is that any other stack could
  have been done *before* the draw (drawing changes neither foundation
  heights nor other piles' tops), so reordering makes it explored elsewhere;
  why the twin is exempted from that reordering is the subtle part
  (TODO(vuong) — please fill in).
- `reveal` is restricted to cards that the drawn card (or its twin) can sit
  on, or first-layer cards. The in-code comment gives the motivating line:
  `DP 8♠, R 10♥, DP K♠` — if you reveal the 10 first you are then forced to
  draw the K which might prevent you from getting the 8; if you draw the 8
  first you can no longer reveal the 10 because the reveal expects to happen
  *before* its pile is built over. The rule forces reveals to happen in the
  order the draw sequence can still accommodate.

## 7. The search

`traverse` (src/traverse.rs) is a shared recursive DFS: visit, insert into
the transposition table (skip if already present — insert-once), generate
dominance-filtered moves, prune with the path pruner, recurse, undo. Callbacks
implement: the solver (history + stats + termination, src/solver.rs), the
graph builder (edge list, src/graph.rs), the hop candidate enumerator, and
the path finder. Everything in the hot path is stack-allocated
(`ArrayVec`); the only allocation is the TP itself.

Claimed structural property: with the pruners applied, the reachable state
graph is a DAG up to the 2-cycles broken in §6.1 — checked exhaustively *per
game* by `tests/no_cycle.rs` (a path-local set that halts if a state repeats
on the current DFS path; slow, `#[ignore]`d, run manually — and so far only
on two Klondike-Solver seeds).

Stats and progress reporting (`tracking.rs`, `SearchStatistics`) and Ctrl-C
termination (`TerminateSignal`) are threaded through the same callback
interface.

## 8. The random (no-undo) player

The player maintains the real game but *plans* on a canonicalized copy:

1. **Canonicalize**: `hidden_clear()` resets the still-hidden cards to
   lexicographic order. This is the belief state — the `Encode` is invariant
   under determinization, so this costs nothing and leaks no information.
2. **Enumerate candidates**: full traversal of the reversible closure from
   the current state; every first-irreversible-move reachable through
   reversible play is a candidate (`ListStatesCallback`,
   src/mcts_solver.rs:58). Each candidate is a *commitment* — exactly the
   partition of §3.1.
3. **Evaluate by determinized Monte Carlo**: `hop_solve_game`
   (src/hop_solver.rs:95) shuffles the hidden cards uniformly across the
   still-hidden slots (preserving per-pile counts — the only thing known
   about them), replays the commitment, and runs the *exact* thoughtful
   solver with a visit limit (default 1000). Win / lose / limit-exceeded is
   one sample. Shortcut: with ≤1 hidden card the determinization is forced,
   so it just solves exactly.
4. **Bandit over candidates**: UCB1 (C=2) over candidates, batches of 10
   determinizations, until the leader has 3000 plays; then the path to the
   chosen candidate is reconstructed by another traversal
   (`FindStatesCallback`) and replayed on the *real* game with assertions
   that every planned move is still legal (it must be — candidate paths only
   contain moves whose legality does not depend on the hidden order).

Known bias: each determinized evaluation is solved with full information
(the classic determinization/PIMC "strategy fusion" optimism). The bandit
chooses among commitments, which mitigates but does not remove it. The macro
rework (see the other doc) is aimed at this among other things.

## 9. Why it all works — the informal argument

The whole engine stands on four legs:

1. **The move set is complete.** The only nontrivial claim is that dropping
   general tableau↔tableau moves (keeping only surface reveals) preserves
   solvability — a card that would be moved pile-to-pile can instead have
   been placed where it is needed, when it was drawn or unstacked. This is
   the biggest unproven-but-validated assumption.
2. **Forgetting is sound.** Position and hidden-identity information is not
   needed because (a) legality at the set level is realized by *some*
   concrete arrangement, and (b) the concrete arrangements in the same
   equivalence class are solvability-equivalent by twin swap (§4) and by the
   reordering arguments behind the pruners (§6). The composition of these
   two is what the cross-validation actually tests.
3. **The dominances lose no solutions.** Each rule of §5 replaces a move set
   with a subset; soundness is the twin-swap equivalence (for canonical
   choices), the worry-back argument (for safe stacking), and commuting/
   reordering arguments (for the forced-order rules). Where the argument is
   hard, the rule is at least *tested* (§10).
4. **The graph is (essentially) a DAG.** With 2-cycles broken and the
   dominances forcing progress (foundation growth, reveals, draws), states do
   not repeat on a path, so a plain visited-set is a sound search strategy —
   the no_cycle test walks entire games checking exactly this.

Failure of any leg would produce a wrong *solvable/unsolvable* verdict, which
is considered a bug — hence the amount of cross-validation.

**The skeptical reader should stop here**: the legs above are argued
*individually*, but the search runs the dominances, the path pruners and the
visited-once transposition table **composed**, and individually-sound filters
can be jointly unsound (a rescue "do it earlier" can land in a position where
another filter blocks it). This interaction — the main open soundness
question of the current method — is analyzed in
[pruning_dominance_interaction.md](pruning_dominance_interaction.md),
including the rule-by-rule audit, the collision cases, and the differential
experiments that would test the composition directly.

## 10. Verification status

- Cross-checked against Solvitaire's published results on Klondike-Solver
  seeds 0..50k and Solvitaire seeds 1..1M; self-cross-checked across engine
  versions on 100k–2M games. No known disagreements.
- `tests/no_cycle.rs`: full-game DAG check (manual, slow; exhaustive per
  game, but so far run on two Klondike-Solver seeds only).
- `tests/hop_no_dead_loop.rs`: regression for the hop candidate gate.
- `lean-verify/`: a Lean 4 formalization of the rules with differential test
  harnesses (`ref_graph_*.csv`) — the long-term home for proving the legs of
  §9, including the twin-swap theorem.

## 11. File map

| File | Role |
|---|---|
| `src/card.rs` | card indexing + bit-layout constants |
| `src/state.rs` | the board, set-based `gen_moves`, encode/decode, do/undo |
| `src/moves.rs` | move types, `MoveMask` algebra |
| `src/stack.rs` | foundation + `dominance_mask` |
| `src/hidden.rs` | hidden structure, shuffle (determinization), canonicalize |
| `src/deck.rs` | stock/waste, draw cycles, drawability masks |
| `src/pruning.rs` | `CyclePruner`, `FullPruner` (§6) |
| `src/traverse.rs` | the shared DFS + transposition table |
| `src/solver.rs` | thoughtful solver (callbacks → result + history) |
| `src/graph.rs` | full edge-list builder for analysis/verification |
| `src/hop_solver.rs` | determinized Monte Carlo evaluation of a commitment |
| `src/mcts_solver.rs` | candidate enumeration + UCB1 bandit player |
| `src/engine.rs` | stateful wrapper with pruner + undo for interactive use |
| `src/standard.rs`, `src/convert.rs`, `src/formatter.rs` | explicit-piles facade, notation conversion, display |
| `src/dependencies.rs` | card-dependency tracker for analysis/viz |
| `src/tracking.rs` | search statistics + termination signal traits |
| `src/utils.rs` | small helpers + the `MixHasher` |
| `src/shuffler.rs` | the 6 seed shuffles (default, Solvitaire, Klondike-Solver, Greenfelt, exact, Microsoft) + 256-bit exact permutation encoding; the README's 7th (`legacy`) is not implemented |
| `lonecli/` | CLI: solve, rate, hop, hop-loop, graph, play, bench, … |
| `lean-verify/` | Lean 4 formalization + differential harness |

The map is a selection — `src/lib.rs` is the full module tree, and
`src/bit_deck_no_bmi2.rs` (present on disk, untracked) is not part of it.
