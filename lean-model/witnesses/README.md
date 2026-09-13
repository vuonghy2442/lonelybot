# The witness archive — the regression layer

Each file is a machine-checked counterexample (or machine-checked
crux) produced during the proof-farm sessions.  `witnesses/` is the
`Witnesses` lean_lib (see lakefile.toml and the root facade
`Witnesses.lean`, which anchors the glob and imports the gate module):

- build the whole layer: `lake build Klondike Witnesses` (from
  `lean-model/`; compiles every `witnesses/*.lean` against the main
  `Klondike` lib),
- verify one file: `lake env lean witnesses/<Name>.lean`.

Farm agents append new witnesses here as they refute; the lib picks
them up automatically (the lib's glob scans the directory — no
facade import needed; the witness files deliberately do NOT import
each other, so several reuse the same top-level helper names).
Lifecycle: a fresh witness cites the still-open/sorry'd statement it
constrains (citing a sorry'd constant is safe — only embedding a
sorry'd *literal* propagates `sorryAx`); when the statement is
repaired or deleted, the citing corollary goes and the
self-contained countermodel facts stay as the regression record, with
a note pointing at FARM.md's REFUTED section.

## Gates

- **Axioms.lean** — `#print axioms` under `#guard_msgs` for the crown
  theorems (`cascade_sound`, the `pace_dominance` family,
  `window_firstDraw(_macro)`, `solvable_relabel`/`_flipAll`,
  `Pace.realizes_iff_stepsOK`, `applyDrawTo(StackTo)_eq_dealPlay`,
  `solvable_of_stackPile`, `solvable_of_pileStack_return`,
  `dominant_of_commutesWithAll`, `deckPile_safe_prunable`,
  `safe_pileStack_dominant_of_return`, `cascade_escape_progress`,
  `solvable_em`, and C1's `engine_of_macro`/`macro_of_engine`/
  `macroSteps_engine_run`/`engine_macro_lift`).  Allowed: `propext`,
  `Quot.sound`, `Classical.choice` (marked per-theorem where used).
  Anything else — `sorryAx` especially — fails the gate: that is a
  FINDING, not a baseline; record it and escalate, never bless it.
- `#guard_msgs` pins on the deterministic `#eval` probes (the farms'
  probe batteries: DrawWitness(2), MacroWitness, CascadeWitness,
  PaceStepZero-, PaceStepsOKWitness, EngineWitness, MacroC1Witness)
  and on the witnesses' own `#print axioms` (where the names are
  public — the `private`-mangled ones in B4LockedWitness/
  DeadPileWitness/MacroC1Witness are left informational: the mangled
  prefix differs between `lake build` (`Witnesses.`) and
  `lake env lean` (`witnesses.`) invocations, so a pinned expectation
  would be invocation-dependent).
- Everything here must stay axiom-clean: `propext`, `Quot.sound`
  (`Classical.choice` where classical reasoning is genuinely used).

## Status (2026-09-13, post laundering disposal)

- **LIVE** (self-contained, axiom-clean countermodel facts; no deleted
  or sorry'd constant cited): AboveIrreflWitness, B4LockedWitness,
  CascadeWitness, CommuteWitness, DeadPileWitness, DrawWitness,
  DrawWitness2, EngineWitness, LiftWitness, LiftWitness2,
  MacroWitness, NoPassingWitness, PaceStepZeroWitness,
  PaceStepsOKWitness, RefuteCommutesAll, RevealCrux, SimWitness,
  StockInvarWitness, TwinSwapWitness (the local twin swap needs equal
  heights — liveness alone lets one twin be stackable while the other
  isn't), MacroC1Witness (the macro game's post-commit win check —
  landed mid-session 2026-09-13), Axioms (the gate module).
- **LIVE with repaired-history anchors** (their refutation targets
  were repaired same-session; the files now prove the *repair holds*
  instead): ApplyWfCounter (witness #1/#2 — `st0.WF` + the reveal
  successor is WF again via the proven `apply_wf`; the duplicated
  cycle rejected by `noDupCards`), ApplyWfCounter2 (witnesses #3/#4 —
  both states now rejected outright by `board_edges`/`stock_wf`),
  ApplyWfCounter3 (witness #5 — the duplicated cycle rejected).
- **Corollaries removed, facts kept** (the `*_refuted`/`*_false`
  derivations of `False` that cited pre-repair or deleted statements;
  each replaced by an in-file note): EngineWitness's
  `engine_iff_refuted` (deleted `solvable_engine_iff`), LiftWitness2's
  `lift_false` (deleted `toEngine_lifts`), CascadeWitness's
  `cascade_refuted` (pre-progress `cascade_sound`), PaceStepZero's
  three `*_refuted` (pre-`hstep` pace family), PaceStepsOK's `broken`
  (pre-`hpure` `realizes_iff_stepsOK`), CommuteWitness's
  `commute_false` (pre-`hnc` `commute_of_disjoint_touch`),
  StockInvarWitness's `stock_invar_false` (pre-`hm`
  `apply_nonConsuming_stock_invar`), the ApplyWfCounter(2,3) unsound
  theorems (`apply_wf` is now PROVEN — those negations are false
  statements).
- **LOST**: B4Witness.lean (the phantom-tenant refutation of
  `solvable_accommodates`) was destroyed in an over-eager directory
  cleanup during archiving.  The finding is fully recorded in
  FARM_MEMORY.md (a won state — heights 13, empty stock/deal, junk
  rank-7/9 cards on p1..p6 — accommodating via [stackPile ♠K p0] to
  total deadlock; ♠2 seated on unplaced ♠K, exactly what board_edges
  forbids) and is rebuildable from that description.

The evidence for every adjudicated refutation in FARM_MEMORY.md that
names a witness file lives here (the `Temp\opencode` paths in older
entries referred to the ephemeral system temp and resolve to this
archive).
