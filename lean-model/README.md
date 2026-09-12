# Klondike (lean-model)

The clean formal model of the lonelybot Klondike solver.  Lean 4,
**core only** — no mathlib, no Batteries, no network.

Replaces the `lean-verify` branch approach (Rust-mirroring
implementation layer + spec layer + correspondence grind).  The design
that emerged (see the repo conversations and the ledger):

## Representation

One executable model that is both the theorem subject and the
reference implementation for cross-validating against Rust.

**The state is what history chose and the rules don't determine** — the
free parameters only:

| region        | free (stored)            | canonical (derived)                 |
|---------------|--------------------------|-------------------------------------|
| tableau visible | the matching `topOf`   | —                                   |
| tableau hidden | depths (per pile)        | deal edges below depth              |
| foundation    | heights (per suit)       | suit-prefix edges                   |
| stock/waste   | cursor                   | cyclic order + contents            |

Everything else is a view: `up : Card → Bool`, the total board
`totalTopOf` (image = all 52 cards), the Rust-bridge encode.

## Encoding decisions

- **Suit is factored**: `Suit = Color × pair` (a structure with `color`
  and `pair : Bool`).  The tableau rules see only `(rank, color)`, so
  twin-swap (T) is the `pair` flip and preserves color *definitionally*
  (`Suit.flipPair_color := rfl`).  Foundations see the full four-way
  suit.
- **Bool-first**: primary definitions executable (`Bool`, `Option`,
  `List`, `Fin`, `Nat` on finite enums); readable characterizations as
  lemmas; `decide` grinds the finite case splits.
- **One semantic function** (planned): `apply : Move → State → Option
  State`, with `legal`/`genMoves` derived from it — desync impossible.
- **Witness-as-data** (planned): `Solvable s := ∃ play : List Move, …`
  — plays as constructible data, since every hard theorem (compression,
  reshape, T, C13) is a play-rewriting proof.
- **Cycles are not forests**: the stock is a pointed cycle, its own
  structure; tableau matchings are forests; foundations are heights.

## Status

- `Klondike/Basic.lean` — Color/Suit(factored)/Rank/Card, twin-swap
  (`flipPair`/`flipSuit` — T's relabeling, color-preservation `rfl`),
  `canSitOn` + rank-grading antisymmetry, the 52-card universe.
- `Klondike/Cycle.lean` — the pointed cycle: `rotate`, `removeIdx`,
  **`removeIdx_comm`** (C13's list-level core), `drawTo`, `posOf`,
  `passed`.  One TODO: `removeAt_comm` (cursor arithmetic over
  `removeIdx_comm`).
- `Klondike/Board.lean` — `Base = Anchor ⊕ Card`, the matching
  (`topOf` + `inj`), derived `bottomOf` by search over the complete
  enumeration, `attach`/`detach`, `aboveOf` (run walk — the
  `pilePile` self-landing guard), `mapBy` (T's conjugation).
  Eight TODOs, all marked `TODO(proof)`.
- `Klondike/State.lean` — the deal, the four free parameters
  (`board`, `heights`, `depths`, `stock` cursor), the derived views
  (`hidden`, `topHidden`, `up`, `canPlace`), the `WF` predicate,
  `flipAll`.  All definitions — no proofs owed.
- `Klondike/Move.lean` — the full physical game (7 moves including
  `pilePile`), **`apply` — the one semantic function** (real code, no
  sorry), `legal`/`run`/`isWin`/`solvableFrom` derived from it,
  `solvableEngine` (the engine's restricted move-set version), and
  the farmable statements: `legal_pileStack_iff`,
  **`apply_flipAll` + `solvable_flipAll`** (T),
  **`solvable_engine_iff`** (the B-legs, as a move-subset equivalence
  of ONE model), `apply_wf`, **`drawTo_comm_adjacent`** (C13 pilot).

- `Klondike/Theorems.lean` — the statement farm, all `sorry` with
  `TODO(proof)`: the **relabeling group** (`Relabel`, `solvable_relabel`
  — T generalized to all 8 coherent suit relabelings), the
  **reversibility/commitment structure** (roundtrip lemmas,
  `irreversibleAt` + the three A1 commitments, `accommodates` and the
  reshape-flavored direction), **commutation** (`Move.comps` +
  component-disjoint commutation, `Move.touch` + `disjointTouch` —
  the type-ball interaction lemma, C13 mod-adjacent commutation and
  the non-adjacent divergence), and **run acyclicity**
  (`aboveOf_rank_grading`).

- `Klondike/Dominance.lean` — the dominance layer (method.md §5):
  `dominantAt`/`prunableAt`/`dominates`/`solvableWith`, the exact
  **safe-to-stack condition** (§5.1, Blake & Gent), `isLocked`/
  `isRedundantStack` (§5.2), `applyDrawStackTo` (§5.3's commitment),
  and the statements: safe-stacking dominance, the redundant-stack
  cascade, deck dominance (draw-1 + the `is_pure` caveat), the
  worry-back and deck-to-tableau pruning rules (§5.4), the
  twin-pair placement equivalence (§5.5), `cascade_sound` (the
  composed filter theorem, carrying the interaction doc's warning),
  and **`dominant_of_commutesWithAll`** — the POR bridge: full
  commutation implies dominance, one direction only (the engine's
  dominances run on worry-back reversibility, safe-irrelevance, and
  canonical representatives, not commutation).

- `Klondike/Progress.lean` — the progress/decidability layer: the two
  monotone measures (`totalDepth`, stock length), **`play_self_is_shuffle`**
  (their §9.4 DAG argument — every cycle is commitment-free, the
  visited-list soundness), `run_append`/`State.trace`/`allDistinct`/
  `play_cut_loop` (loop-cutting), and the decidability chain
  `solvable_iff_distinctTrace → solvable_iff_boundedPlay →
  solvable_decidable` with the crude `stateSpaceBound`.

- `Klondike/Realizability.lean` — **B1** (no_pile §3): the type
  machinery (`Card.typeOf`, `Rank.pred`, `belowType`), the four counts
  (`presentType`, `placedBelow`, `uncovered`, `freeType`), `legalEdges`,
  **`uncovered_eq_freeType`** (the parity lemma: `present − placed` =
  the free count, via matching injectivity + edge legality),
  `Board.Fits` + `Realizable` + `realizable_of_wf` +
  `apply_realizable` (the maintenance table's statement).  The
  engine-side `bm` XOR algebra is deferred to the bridge milestone.

- `Klondike/Macro.lean` — **the macro (commitment) game**: `MacroMove`
  (`drawCommit`/`revealCommit`), `commitApplies`, `macroStep`
  (accommodation + commitment), `macroSteps`/`State.macroSolvable`,
  **`solvableEngine_iff_macro`** (C1 — with A3's regrouping route
  documented: draws commute with shuffles by component disjointness,
  trailing draws drop), `macroStep_engine_play`, and
  **`drawTo_tableau_outcomes_agree`** (C2's model seed — tableau
  outcomes agree on everything but the board).  Deferred and
  recorded: C12 (needs §6.5b's exact statement), the full sleep-set
  layer, and the parking lemma (B4-adjacent).

- `Klondike/Bridge.lean` — **the engine bridge**: `EState` (vis set,
  depths, heights, order/offset — the 61-bit encode's shape), `EMove`
  (the five engine moves, rotate-then-play), `eStep` with
  *witness-existential* legality over realizing boards (the spec the
  engine's masks implement), `toEngine` (the Cycle unpacks into
  order/offset), and the crown statements: `engine_iff`
  (model-engine ↔ abstract), `toEngine_simulates`/`toEngine_lifts`,
  the C2 uniqueness quartet, `esolvable_offset_irrel` (the sweep's
  license at draw-1).  Deferred: the bm XOR algebra, the encode.

- `Klondike/Initial.lean` — **the exhibit**: `Anchor.start`,
  `Deal.ofList`/`Deal.standard` (the triangular split),
  `initialBoard`/`State.initial` (each pile's top dealt card face-up
  on the boundary), `initial_wf` — the WF hypotheses are
  non-vacuous.  Plus runnable `by decide` sanity checks — the oracle
  seed; the first one caught a Nat-truncation bug in `initialBoard`
  on its maiden run.

**`FARM.md`** — the proof-farm handoff: all `sorry`s in
dependency-ordered waves with difficulty tags and proof routes.

All `sorry`s carry a `TODO(proof)` comment — they are the work items
for proof-farming; every definition is final code.

## Next steps

1. `Board.lean`: `Base = Anchor ⊕ Card`, `Board = topOf + inj`,
   derived `bottomOf` + characterization.
2. `State.lean`: deal parameter + the four free parameters; derived
   views (`up`, `totalTopOf`).
3. `Move/apply`: the five engine moves; `legal`/`run`/`Solvable`.
4. The C13 pilot at cursor level: when do `Draw(x); Draw(y)` and
   `Draw(y); Draw(x)` land on the same cycle.
5. The Rust bridge: `toEngine`, encode injectivity, cross-validation
   against the shipped solver's verdicts.

The old `lean-verify` branch remains a source of theorem statements
and cross-validation harnesses.
