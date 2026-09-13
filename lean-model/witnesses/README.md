# The witness archive

Each file is a machine-checked counterexample (or machine-checked
crux) produced during the proof-farm sessions. Verify with
`lake env lean witnesses/<Name>.lean` from `lean-model/`.

## Status

- **PASS** (compiles against the current tree): the refutation target
  is still present, either as a repaired statement carrying its new
  hypothesis, or as a still-open sorry the witness constrains.
  Includes: AboveIrreflWitness, DeadPileWitness, DrawWitness(2),
  EngineWitness, LiftWitness(2), MacroWitness, NoPassingWitness,
  RefuteCommutesAll, RevealCrux, SimWitness.
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
