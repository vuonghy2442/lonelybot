import Orig.Basic
import Orig.State
import Orig.Play
import Orig.Fate
import Orig.Integrity
import Orig.Twin
import Orig.TwinExchange
import Orig.TwinExchangeQuotient
import Orig.Macro
import Orig.Mono
import Orig.Irreversible
import Orig.Phase
import Orig.Combine
import Orig.Shuttle
import Orig.Encode
import Orig.Classify
import Orig.Reach
import Orig.Canonical
import Orig.MergeWalls
import Orig.Progress

/-!
# Orig — the original game

`Orig` is the physical game of Klondike, stated directly and with no
restrictions: pile-to-pile run moves are first-class, the reveal is
automatic, and the stock is a stock.  Every later layer of the
program — the arrangement-blind engine state, the restricted move
set, the macro (commitment) game, the futures counts — must be
*derived* as a chapter on top of these files and licensed by a
theorem, with the proof library in `Klondike/` cited through
bridges, never baked into the definitions here.

**THE SETOID FLIP (user decision, 2026-10-10)**: `sameOrbitSetoid`
is the REV-CLOSURE (`RevEqW b a`), not the twin-blended 4-disjunct
join. The wanted twin-blindness is local and move-achievable: every
licensed twin exchange is one reversible `tabToTab` each way, already
inside `RevEqW` — the game's own moves contain the local swap. The
flip removes the GLOBAL relabeling identification (`A ~ twinMap A`),
which no play can ever relate (moves do not relabel suits) — the
count program's witnesses never used it. The conjugation survives
as the AUTOMORPHISM (`RevEqW_twin_pair` on classes, `canon_twinMap`
on canonical forms); conjugate positions sit in distinct macro
classes with equal verdicts (`twin_fate` — external symmetry, not
folded identity).

Chapter plan (each later chapter is a derived construction):

1. `Orig.Basic`, `Orig.State`, `Orig.Play` — the game: cards, piles,
   the deal, the full move set, the conservation invariant
   `State.WF`, plays and the win condition.
2. `Orig.Fate` — the notions the program is *about*: reachability,
   winnability (`WinFrom`), same-verdict positions (`sameFate`, the
   primitive "same future"), and the semantic `irreversibleAt`.
   No syntactic commitment split exists at this layer.
3. `Orig.Twin` — the twin relabeling and its theorems: the step
   conjugation `State.twin_step`, the twin swap theorem in
   solvability (`twin_fate`), and the twin quotient
   (`twinSetoid`, `WinFromQ`, `twin_quotient`).
4. `Orig.Macro` — the macro game through the semantic
   irreversibility: `ShufflePlay`, `MacroStep`, `MacroWin`, and the
   correspondence `win_iff_macro` (every winning play regroups as
   shuffle / commit / … / shuffle, with commitments picked by
   `irreversibleAt` — no move-set restriction anywhere).
5. `Orig.Mono` — the monotone bridge, "immediately irreversible ⇒
   fully irreversible": `mono_run` walks a measure along arbitrary
   plays, and `irr_of_desc` / `irr_of_asc` convert a strict
   one-step measure move into the full `irreversibleAt`.  The
   `runIn P` / `irreversibleAtIn` fragment machinery restricts the
   undo player to a permitted-move regime (for the later
   no-worry-back fragment).
6. `Orig.Phase` — the draw rows of the classification:
   `draw_irreversible_offset` (offset/misaligned waste, stock
   nonempty) proved twice — by the two-case origin/phase-alignment
   trap, and by the lexicographic measure route (`D`/`QPair` via
   the descent bridge); `draw_irreversible_pristine` (the
   source-class: an empty waste is never re-entered without a
   cycle-count drop); the packaging
   `draw_irreversible_of_wasteShape`; the constructive base
   `draw_reversible_selfRecycle`; `drawStep_zero_reversible` — the
    `0 < drawStep` premise proven genuinely necessary (WF-free
    statements: draws are the identity at zero).  The in-phase
    round trip and the head classification are banked: the witness
    `draw_reversible_inphaseW` with `draw_reversible_inphase`, and
    the classification pair `draw_irreversibility_class` (whose
    `st.stock ≠ []` premise is load-bearing — the iff degenerates
    at empty stock, the degeneration documented in the docstring)
    and `drawStep_one_class`.
7. Tickets, in dependency order:
   - `step` preserves `State.WF` (the conservation invariant, all
     six move kinds);
   - `State.initial` of a `Deal.WF` deal is `WF`;
   - ~~search integrity at `WF` states~~ — **done**: banked in
     `Orig.Integrity` (`pileOfTop`/`pileHolding` exactness and
     injectivity, the occurrence-uniqueness bundles, the `runOK`
     descent kit, `canPlace` self-safety);
   - the irreversibility classification: tabulating each move
     against the three measures and instantiating the bridge.  The
     measure tables are banked in `Orig.Irreversible` (the three
     per-move tables with the reveal/noreveal rigor legs, the
     `foundTotal` no-worry row, and the undo witnesses —
     `foundToTab_undo`, `tabToFound_undo_under`,
     `tabToFound_undo_bare` — with their `reversibleAt` twins);
     the draw rows are `Orig.Phase` above.  The remaining work: the
     classification assembly — the decidable per-move oracle, and
     the scrub of `win_iff_macro`'s single `by_cases` through it;
   - the arrangement-blind abstraction `α` and its replay license —
     the bridge to `Klondike.*`;
   - the futures count: a commitment leaves at most two
     `sameFate`-distinct successors, per accommodation window —
     restated on the original game, with the `Klondike` witness
     corpus re-derived here first (the formulation route map and
     fence ledger: `FUTURES-ORIG.md`).
-/
