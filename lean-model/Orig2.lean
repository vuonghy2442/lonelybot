import Orig2.Model
import Orig2.Vocab
import Orig2.Kit
import Orig2.Integrity
import Orig2.PairClassSeed
import Orig2.Chart
import Orig2.Classification
import Orig2.CargoKit
import Orig2.StepWF
import Orig2.FloaterLadder
import Orig2.RevSteps
import Orig2.FloatFiber
import Orig2.FloatOrbit
import Orig2.AnchorRelabel
import Orig2.KingOrbitFull
import Orig2.KingTrace
import Orig2.KingSwapStrict
import Orig2.KingSwapAssembly
import Orig2.Claims
import Orig2.ClaimsScrutiny
import Orig2.OrbitFactor
import Orig2.SeatMateStack
import Orig2.TwinRelabel
import Orig2.TwinSplice
import Orig2.TwinSpliceWF
import Orig2.TwinSuffixExchange
import Orig2.TwinParentShift
import Orig2.TwinSwapRecipe
import Orig2.TwinDrawTransfer
import Orig2.TwinEquivariance
import Orig2.TwinSwapUnique
import Orig2.TwinTransferRiderFree
import Orig2.TwinRecipeSegment
import Orig2.TwinRecipeRiders
import Orig2.TwinRiderPath
import Orig2.DetourKit
import Orig2.TwinReroute
import Orig2.TwinRerouteMulti
import Orig2.TwinGroupoid
import Orig2.TwinFunctor
import Orig2.TwinPointFunctor
import Orig2.TwinSpliceUnique
import Orig2.TwinPointTransfer
import Orig2.TwinSpliceComm
import Orig2.TwinSplicePlay
import Orig2.TwinPointOrbit
import Orig2.TwinPointNormalize
import Orig2.TwinNormalizeSplit
import Orig2.FiberTransferCapstone
import Orig2.FiberTransferCapstoneRider
import Orig2.FlagShip

/-!
# Orig2 — THE REBUILD LIBRARY

Chartered 2026-10-17 (the owner's reset decision).  The macro-state
program is being rebuilt from scratch here, in a clean namespace,
because the old tier's vocabulary drifted from the owner's design
intent (the 2026-10-17 archaeology: shape-guessed definitions landed
by fast sessions without sign-off — `below_fork` being the live
specimen — and retired interface vocabulary stayed load-bearing by
default).

## THE SEAM POLICY (OWNER-DECREED CLOSED, 2026-10-17)

`Orig2` imports the GAME-MODEL CORE ONLY:

* `Orig.Basic`, `Orig.State`, `Orig.Play` — the board, the cards,
  the moves, the step relation.

That is the certified substrate beneath all class-grade content;
from it upward, `Orig2` defines everything fresh — and it is the
ENTIRE permanent import surface.  **No other `Orig` module may ever
be imported by any `Orig2` module** (owner decree, 2026-10-17):
the override table below is CLOSED — an entry requires the owner
plus a registry decision, and the expected answer is no.  The
`Orig` macro tier is FROZEN; the physics tier beyond the core
(Integrity, Irreversible, Mono, Phase and kin) transitively imports
`Orig.Fate`, whose root-level `reversibleAtW` collides with the
registry-owned carrier — so every physics row a card needs is
PER-FILE PRIVATE KIT restated in the consuming card with its source
line cited (the house dedup discipline), never an import:

```
-- overrides (each with a ledger reason and a migration-out plan)
-- (none — table closed by owner decree 2026-10-17)
```

## THE MIGRATION CAKE (the order content lands here)

1. **substrate** — the class-grade foundations, defined fresh to
   the intent lines: the state-class notion, witness journeys, the
   rung ledger, the LIFO discipline.
2. **detection chain** — the fork-detection iff family and its
   witness parcel.
3. **capstones** — the pair-unique-class theorem family (the
   pairClass spine: the FIRST migration wave by owner directive
   2026-10-17).
4. **census & labels** — the fork-in-class detector, the
   decidability composites.
5. **the programs** — low-slab, descent, ceiling, ascent: one per
   card, restated at the new vocabulary.

Migration honest method: a theorem enters `Orig2` either by
RESTATEMENT at the new definitions (real work, batched per layer,
never copy-paste hoped) or by an explicit bridge import (recorded
in the override table, with a migration-out line).  Layers retire
from `Orig` last, per-layer, when their `Orig2` replacements are
green.

## THE FOUNDING LEDGER (2026-10-17 adjudications, binding)

* **KEEP (first migration wave, priority)** — the pairClass spine,
  by owner directive: `Orig/PairClass` capstones, `Orig/PairConfine`
  (`pair_cover_pins`, the door complex), `Orig/ForkCensus`,
  `Orig/OriginLock`, `Orig/CrossFamily`, the read tier, the
  detector chain, with their substrate (`Orig/BracketDecomp`'s
  `sameOrbit_forward`, `witness_rung_census`, LIFO; `Orig/SlabEquiv`,
  `Orig/SlabForms`).
* **DEAD (retired this day, never re-land as stated)** — the
  fork-spectrum family (`1dc82fd`); the descent
  stall-certifies-floor residue (`4184488`); the seat-less
  conjugate closure stub (`c3294ea`).  LowSlab's raise/reseat
  unconditionals: refuted and HELD (entangled with the live hlow
  repair chain — their honest completion is the ratified hlow swap,
  owner's to write).
* **BINDING CONSTRAINTS** — every `CHALLENGES.md` REFUTED-tier
  fence binds `Orig2` definitions from day one: no new def may
  re-enable a fenced statement.  The falsity archive
  (`witnesses/`, `probes/`) is the constraint set's evidence and is
  never cleaned.

## INTENT LINES (the vocabulary registry — DRAFT, owner's edit pass)

The registry rule: NO program-wide definition lands without an
owner-approved line here first.  Seeded from the owner's own words
(2026-10-17 chat):

* `below_fork st x` — DRAFT: `ForkWitness st x ∧ (x.twin face-up or
  covered-hidden in some pile)` — "below_fork also means we have to
  have a forkState witness at x".  PENDING OWNER RATIFICATION.
* `weakForkState` fate — OPEN: does the weak grade appear in the
  new interface at all, or live only inside the G2 falsifier
  records?
* `forkState`/`ForkWitness` — carried in spirit (the S-grade
  detection and the per-witness parcel); the new formalization
  restates to the intent lines once written.
* (next lines here — the owner's twenty are the target)

## HOUSE COMPLIANCE (unchanged)

Per-file batteries (`#print axioms`, zero `Classical.choice` by the
canonical-order discipline), REFUTED-first probing for open rows,
frozen statements never force-premised, CHALLENGES fences global,
per-file private kits by the dedup discipline, and the sign-off
rule above for shared vocabulary.

The vocabulary registry is `Orig2.Vocab` (definitions only, under
owner intent lines); the import seam is `Orig2.Model`; claim-banking
lives in `Orig2.Claims`; the shared cargo-tier kit (the `tfc_*`/`tfa_*`
family, consolidated 2026-10-17 from the per-file copies) is
`Orig2.CargoKit`; the flagship export door (the adjudicated headline
re-exported at citable names) is `Orig2.FlagShip`; the search-integrity
chapter's rebuild home (the `Orig/Integrity.lean` occurrence census,
the search exactness rows, and the `canPlace` self-safety pack,
split out of the classification card 2026-10-18) is `Orig2.Integrity`;
and the WF conservation fence (the `step_wf` step-wise capstone and its
play lift `run_wf`, ported from `Orig/Reach.lean`'s fence chapter
2026-10-18 over CargoKit's `tfc_tabToTab_wf` case) is `Orig2.StepWF`.
-/
