# MAP — the repository map (2026-10-13)

The navigation layer. Modules live flat in `Orig/` by import-DAG
stratum; this map is the stratum diagram, the probe yard, the doc
system, and the deferred physical re-tree proposal. Placement ground
truth = each file's import lines; headers quoted as each file states
them.

## The strata (bottom → top)

**S0 — kernel & state physics** (the deck, the piles, conservation,
symmetry calculi):
`Basic` `State` `Play` `Fate` `Integrity` `Twin` `TwinExchange`
`PileSwap` `Phase`
Key rows: zone exclusivity (`mem_faceUp_only`), the twin
conjugation (`State.twin_step`, `twin_fate`), WF fences (`step_wf`).

**S1 — measures, doctrine & combinatorics**:
`Mono` `Macro` `Irreversible` `Combine` `Classify` `Encode` `Reach`
`Progress`
Key rows: `irr_of_desc` (measure→commit converter), the measure
tables, `pigeonhole_le`, `win_iff_macro`, `RevEqW_sameFate`,
`reversibleAtW_iff_reversible`, `invariant_of_initialReachable`.

**S2 — journey & macro machinery** (the census/canon spine):
`Shuttle` `BracketDecomp` `SFlatTransfer` `Canonical` `Vacate`
`EdgeLabel` `TwinExchangeBoth` `TwinExchangeQuotient` `Decompress`
`MacroInternal` `CanV3` `OrbitFactor` `OrbitFactorC` `MergeWalls`
`Dominance`
Key rows: `witness_rung_census`, `canon_class`, `orbit_data`,
`rung_found_congr`, `draw_landings_sameOrbit`, the residue ledger
(N-nesting in BracketDecomp, the worry chip in Dominance — see
CHALLENGES.md).

**S3 — fork-cell algebra & detection**:
`PositionSeat` `RunOrTwin` `ForkStateSB` `ForkStateS` `ForkWeaker`
`PairName` `ForkStateUniq` `ForkStateUniqGate` `ForkDossier`
(`ForkDossier` = the fork-point program's 2026-10-17 archive leaf;
`ForkSpectrumProof` retired at the same cleanup)
`ConeCrossarm` `SConjugate` `SWRotInert` `ConjugateProof`
Key rows: `canRaiseS_iff`, the witness pins, intra-state uniqueness
in both strengths, the cargo-transport fixity family, the decidable
faces. `SeedKit` lives in RunOrTwin; `FoundKit` in PairConfine.

**S4 — class reads & zone censuses**:
`SlabEquiv` `SlabForms` `PairClassZones` `HostCensus`
Key rows: the census zone loop (`mates_cycleZone_pin` /
`class_zoneAgree_iff` / `wf_foundRung_iff`), `twin_slab_tableau`,
`interleave_phase_align`, the mint/burn ledger.

**S5 — the certified pairClass arc** (the program's main sequence,
all `[propext, Quot.sound]`):
`OrphanSeat` (the exile laws: `cross_orphan_seat`, `Below_stable`)
`PairConfine` (the upward axis, `FoundKit`) `CrossFamilyStatic` /
`CrossFamily` (the cross-family lock) `OriginLock` (the origin lock,
`ForkKit.fork_nextUpExile_crash`, `exodus_seating_census`)
`PairClass` (the no-lock capstone).

**S6 — frontier (hot missions, hands off while sessions own them)**:
`LowSlab` (THE LOW-SLAB SUFFICIENCY — six `[H]` open),
`ForkFloor` (THE FORK-FLOOR CONJECTURE), `ForkAscent` (THE GREEDY
SLIDE-STACK ASCENT).

## The probe & exhibit yard (decide-graded boards, no proof content
consumed by the spine)

- In `Orig/`: `CrossFamilyProbe` `LowSlabProbe` `ForkFloorProbe`
  `PhaseClipProbe` `EpochProbe` `EpochProbeVis` `SProbe`.
- `probes/` — the campaign probe battery (26 boards: CanLaw*,
  CanonDecompress, CanonV3, Conjugate, Determinism, ExchCanLaw,
  ForkUniq, detour/rhoreplay/w15 families, etc.; see its README).
- `Temp/` — the active-session scratch pen (`door_carrier_probe`,
  `rethread_audit_probe`, `upward_orphan_probe`, `scratch_names`);
  owner-managed; harvest decisions belong to the owning session.

## The doc system

| file | role | lines |
|---|---|---|
| `README.md` | the entry point | 125 |
| `MAP.md` | this file — strata, probes, docs | — |
| `THEOREM-INDEX.md` | the PROVED library (agent-facing: names, quick routes) | 544 |
| `CHALLENGES.md` | the OPEN ledger ([H]/[M]/HOT/REFUTED, with routes) | 101 |
| `ENDGAME.md` | the reshape endgame route (B4 / §5.1 N-half) | 585 |
| `FARM.md` | the farm/spawn ledger | 2,752 |
| `FARM_MEMORY.md` | the session journal (append-only; TOC at top) | 4,037 |
| `FUTURES-ORIG.md` | the strategic mission cards (TOC at top) | 3,719 |

Reading order for a new agent: README → MAP (this) → THEOREM-INDEX
§0-§0.5 → CHALLENGES → then the mission card of interest in
FUTURES-ORIG, with FARM_MEMORY searched by topic.

## The deferred physical re-tree proposal (needs a farm freeze)

Target: `Orig/{Kernel,Journey,Fork,Missions,Frontier,Exhibits}/`
subdirectories over the strata above.  Costs: ~60 module paths, every
`import Orig.X` rewritten (~200 sites), full olean rebuild, one
atomic commit during a quiet window, and a MAP.md rename table for
FARM_MEMORY/FUTURES line references (policy: journals stay
append-only, stale `Orig/X.lean:NNN` refs are dated history, the
rename table translates).  Benefit over the current flat layout:
discovery by directory; benefit over MAP.md alone: marginal — most
of the findability is this navigation layer.  Recommendation: defer
until the frontier missions pause; do the `ZoneAgree.lean` census
leaf and the shared-kit leaf first (both owner-endorsed, both
additive, no renames).
