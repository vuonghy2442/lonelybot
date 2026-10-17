import Orig.Basic
import Orig.State
import Orig.Play

/-!
# Orig2.Model — THE SEAM

The rebuild library's only sanctioned import surface (the
`Orig2.lean` root charter's seam policy): the GAME-MODEL FOUNDATION
— the board, the cards, the piles, the moves, the step relation,
the run algebra (`Orig.Play`) — everything beneath the
class-grade content, certified and shared with the frozen `Orig`
tier.  The reversibility carrier was seam-carried from `Orig.Fate`
until the 2026-10-17 review: it is now registry-owned
(`Orig2/Vocab.lean` §1.5, ported verbatim from `Orig/Fate.lean:92`).
`Card.twin` joins it at §4.5 (the twin module `Orig.Twin` is NOT
seam-carried — its transitive imports would collide with the
registry's carrier; the one-line involution is registry-owned
instead), so the seam is exactly the certified game core.

Everything above this file (the class notion, witness journeys,
detection, censuses, the programs) is defined FRESH inside `Orig2`
to the owner-approved intent lines (see the root charter's
registry).  The frozen `Orig` macro tier imports only via
explicitly recorded override entries in the root — none yet.

SEAM EXTENSION (2026-10-17, the classification card's ticket): four
game-physics modules admitted, each ONE tier above the core and
importing nothing above the fate tier — line notes:

* `Orig.Integrity` — the `WF` search-integrity rows: occurrence
  uniqueness, the `WF` accessors (`found_prefix`, `cardCount_eq`,
  `runOK_of`, `drawStep_pos`), the placement-target pins.
* `Orig.Irreversible` — the step-guard tables, the measures
  (`cycleCount`, `hiddenTotal`), and the constructive undos of the
  raise/pull letters (`tabToFound_undo_under`/`_bare`, the
  `foundToTab_undo` family).
* `Orig.Mono` — the monotone-bridge kit (`mono_run`, `irr_of_desc`).
* `Orig.Phase` — the draw loop algebra (`plain_draw_shape`,
  `base_draw_shape`, the pristine/offset commit rows, the in-phase
  and selfRecycle round trips).

The forbidden macro tier stays out of bounds (Combine, Canonical,
MacroInternal, Classify, FoundKit — the last of these transitively
imports Combine — and everything SameOrbit/class-graded); their rows
enter `Orig2` cards only as per-file private restatements, never as
imports.

OWNER DECREE (2026-10-17, minutes after the ticket above): THE SEAM
IS CLOSED — `Orig.Basic`/`Orig.State`/`Orig.Play` are the ENTIRE
permanent import surface; the four-module extension ticket above is
VOID.  Every physics row the cards need (the Integrity/Irreversible
step tables, the Phase loop algebra, the Mono bridges) is per-file
PRIVATE KIT restated in the consuming card with its source line
cited — never a seam import.  Rationale: the physics tier
transitively imports `Orig.Fate`, whose root-level `reversibleAtW`
collides with the registry-owned carrier; the owner chooses the
closed seam.

House compliance: additive file below the certified foundation;
no fresh heads here (a pure seam), so no battery section; zero
`sorry`; zero `Classical.choice`.
-/
