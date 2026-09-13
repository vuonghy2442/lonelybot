# The witness archive

Each file is a machine-checked counterexample (or machine-checked
crux) produced during the proof-farm sessions. Verify with
`lake env lean witnesses/<Name>.lean` from `lean-model/`.

## Status

- **PASS** (compiles against the current tree): the refutation target
  is still present, either as a repaired statement carrying its new
  hypothesis, or as a still-open sorry the witness constrains.
  Includes: AboveIrreflWitness, B4LockedWitness (the locked-pile
  refutation of `solvable_of_pileStack`/`solvable_accommodates` — both
  repaired the same session, 2026-09-13: `hnotlock` on the crux,
  `safeAccommodates` on the main; the file now records that the guard
  is tight), DeadPileWitness, DrawWitness(2), EngineWitness,
  LiftWitness(2), MacroWitness, NoPassingWitness, RefuteCommutesAll,
  RevealCrux, SimWitness.
- **PASS, GOING HISTORICAL**: PaceStepZeroWitness (2026-09-13) —
  refutes the three physical-game pace statements at `drawStep = 0`
  (deal_passEnd_reaches, pace_dominance_phys_passEnd,
  solvable_iff_pure_cursors all gained `hstep : 0 < st.drawStep` the
  same session). Compiles while the pre-repair Macro.olean is on disk;
  once the oleans refresh, the three `*_refuted` corollaries fail on
  the missing `hstep` — by design, the ApplyWfCounter lifecycle. The
  core facts (`stZ_dead`, `stZ_run_fix`, `stZ_notReach`,
  `stZ_notSolvable`, `stN_solvable`, all axiom-clean) cite no sorry'd
  constant.
- **HISTORICAL** (2026-09-13, olean-refreshed): PaceStepsOKWitness —
  refuted `realizes_iff_stepsOK` at an impure initial cursor (deck
  [♥A,♥2], step 2, cursor 1: σ = [♥A,♥2] realizes through the initial
  leading lane, stepsOK fails at pre = []). Repair the same session: the
  theorem gained `(hpure : c.cursor % step = 0 ∨ c.cursor =
  c.cards.length)` and was then PROVEN. `broken` fails on the missing
  `hpure` (the designed ApplyWfCounter lifecycle); the core facts
  `realizes_true`/`stepsOK_false` are axiom-clean.
- **PASS, GOING HISTORICAL** (2026-09-13): CascadeWitness — refutes
  `cascade_sound` as staged (escape = `dominantAt` alone): a WF state
  one `pileStack ♦K` from the win with the stock exhausted makes
  `draw` the identity (`dealOnce` on the empty cycle is `rfl`), hence
  *trivially dominant* — the draw-only filter satisfies the hypothesis
  at every reachable solvable state while no all-draw play can win.
  Repair the same session: the escape gained the `cascadeMeasure`
  strict-decrease conjunct. `cascade_refuted` cites the pre-repair
  statement (compiles while the stale Dominance olean is on disk; it
  fails on the missing progress conjunct once they refresh); the core
  facts (`stW_wf`, `stW_solvable`, `h_W`, `stW_notSolvableWith`, all
  axiom-clean) cite no sorry'd constant.
- **HISTORICAL** (no longer compiles — by design): ApplyWfCounter(2,3),
  CommuteWitness, StockInvarWitness target the PRE-repair statements
  (the old WF shape; disjoint_touch without the hnc guard;
  nonConsuming without the m ≠ draw guard). Their refutations did
  their job — the statements were repaired — so the files fail only
  because the old constants no longer exist. Kept as the design
  record; do not "fix" them.
- **LOST**: B4Witness.lean (the phantom-tenant refutation of
  solvable_accommodates) was destroyed in an over-eager directory
  cleanup during archiving. The finding is fully recorded in
  FARM_MEMORY.md (a won state — heights 13, empty stock/deal, junk
  rank-7/9 cards on p1..p6 — accommodating via [stackPile ♠K p0] to
  total deadlock; ♠2 seated on unplaced ♠K, exactly what board_edges
  forbids) and is rebuildable from that description.

The evidence for every adjudicated refutation in FARM_MEMORY.md that
names a witness file lives here (the `Temp\opencode` paths in older
entries referred to the ephemeral system temp and resolve to this
archive).
