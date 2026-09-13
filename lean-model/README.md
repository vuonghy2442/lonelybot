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

The proof farm is at **7 `sorry`s** (pinned by `../script/lean-census.ps1`):
Theorems 1 (the B4 crux `solvable_of_pileStack`), Macro 1 (C1,
`solvableEngine_iff_macro`), Dominance 5 (the N-half, C4, §5.4 first
half, C6, the least-redundant repair).  Every definition is final code;
the refuted statements (`solvable_engine_iff`, `toEngine_lifts`,
`engine_iff`) are removed from the library — their witnesses live in
[witnesses/](witnesses/) and FARM.md's REFUTED section archives the
statements.  **FARM.md** is the handoff: the wave table, the routes,
and the case ledger for the crux.

- `Klondike/Basic.lean` — Color/Suit(factored)/Rank/Card, twin-swap
  (`flipPair`/`flipSuit` — T's relabeling, color-preservation `rfl`),
  `canSitOn` + rank-grading antisymmetry, the 52-card universe.
- `Klondike/Cycle.lean` — the pointed cycle: `dealOnce`, `removeAt`,
  `drawTo`, `posOf`, `findFirstIdx`, **`removeIdx_comm`** (C13's
  list-level core) and the draw-commitment splice kit
  (`removeAt_drawTo`, `findFirstIdx_removeIdx_shift/keep`,
  `posOf_removeIdx_shift/keep`) — the canonical home of that kit.
- `Klondike/Kit.lean` — the shared list/counting machinery: the
  NoDupP kit (`length_eq_of_bijection`), the allDistinct/pigeonhole
  kit, the idxOf/take/count kits, the splice kit, the radix kit.
- `Klondike/Board.lean` — the matching (`topOf` + `inj`), `attach`/
  `detach`/`bottomOf`/`aboveOf`, `ext_topOf`,
  `bottomOf_detach_self`, `attach_attach_comm`.  Fully proven.
- `Klondike/State.lean` — the deal, the free parameters, the derived
  views, the 11-conjunct `WF` (with the named accessors and the
  `WF.intro` constructor lemma), `isLocked`, the heights combinators
  (`bumpHeight`/`dropHeight` + the ± composition kit), `flipAll`.
- `Klondike/Pace.lean` — the draw-pacing machine (deck.rs
  `compute_mask`): `maskPos`, `maskPos_mem_iff`,
  `drawCard_cursor_indep`, `pos_shift`, `cursor_after`,
  **`realizes_iff_stepsOK`** (G4's model-level soundness, with the
  `hpure` repair).  Sorry-free.
- `Klondike/Move.lean` — **`apply` — the one semantic function** (7
  moves), the shape lemmas (`apply_*_iff`), `applyDrawTo_eq`,
  `apply_wf` (the invariant maintenance, via `WF.intro`),
  `drawTo_comm_adjacent` (C13 pilot), the take/append/board kits.
- `Klondike/Relabel.lean` — the relabeling group (split from
  Theorems): `Relabel.cardInv` and the matching law, `relabelBy`
  transfer kit, `apply_relabel` + `solvable_relabel` (axiom-clean).
- `Klondike/Commutation.lean` — the commutation layer (split from
  Theorems): the blindness lemmas, `commute_of_compsDisjoint`,
  `commute_of_disjoint_touch` (the 16 fine pair-lemmas),
  `drawTo_comm_modAdjacent` (repaired `+hstep`),
  `drawTo_nonadjacent_diverge`.
- `Klondike/Theorems.lean` — the farm's facade: the B4 decomposition
  (`solvable_of_stackPile`, `solvable_of_pileStack_return`,
  `solvable_of_accomm_step`, the commute squares), the jump-soundness
  theorems `applyDrawTo_eq_dealPlay` (repaired `+canPlace`) /
  `applyDrawStackTo_eq_dealPlay`, the `dealIter`/`dealChain`/
  `draw_full_pass` machinery, `cascade`-supporting kit — and the one
  sorry: the crux.
- `Klondike/Progress.lean` — `run_append`, `play_self_is_shuffle`,
  `play_cut_loop`, `solvable_iff_distinctTrace`,
  **`solvable_iff_boundedPlay`** (the verdict is bounded-search
  decidable, via the injective state encode + pigeonhole),
  `solvable_em`.  Fully proven.
- `Klondike/Realizability.lean` — **B1**: the type machinery, the
  four counts, **`uncovered_eq_freeType`** (the parity lemma),
  `realizable_of_wf`, `apply_realizable`.  Fully proven.
- `Klondike/Dominance.lean` — the dominance layer: the POR bridge
  (`dominant_of_commutesWithAll`, repaired to every-state exchange),
  `safe_pileStack_dominant_of_return` (the R-half),
  `stackPile_pileStack_cancel`, `deckPile_safe_prunable`,
  **`cascade_sound`** (repaired: strict `cascadeMeasure` decrease),
  `vis_base_of_notLocked`.  5 sorries: the open dominances.
- `Klondike/Macro.lean` — the macro (commitment) game:
  `macroStep_engine_play`, `drawTo_tableau_outcomes_agree` (C2's
  model seed), the five pace dominances (repaired `+hstep`), the
  physical reachability family (`deal_chain_reaches`,
  `dealOnce_iterate_add`, `dealOnce_reach_end(_any)`),
  `solvable_iff_pure_cursors`, `window_firstDraw(_macro)`.  1 sorry:
  C1.
- `Klondike/Bridge.lean` — the engine bridge: `EState`/`EMove`/
  `eStep`, `toEngine_simulates` (repaired `+hwf`; the refuted
  `engine_iff`/`toEngine_lifts` are archived, not in-tree).  The
  C2 uniqueness quartet, `eRun_offset`.
- `Klondike/Initial.lean` — the exhibit: `Deal.standard`,
  `State.initial`, `initial_wf` (WF is non-vacuous) + the `by decide`
  oracle seeds.  Fully proven.

**`FARM.md`** — the proof-farm handoff: the open wave table with
routes, the refutation archive, the consolidation queues.  All
remaining `sorry`s carry a plan note; the census script pins the
count.

## Next steps

FARM.md's wave-11 table is the work list (the crux's case ledger is
the long pole); the design decisions pending are listed there too.

(The old `lean-verify` branch was deleted 2026-09-13 — unbuildable
after the model rework; its durable refutation witnesses live in
`witnesses/`, and FARM.md's REFUTED section archives the statements.)
