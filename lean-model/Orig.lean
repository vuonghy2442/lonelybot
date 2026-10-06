import Orig.Basic
import Orig.State
import Orig.Play
import Orig.Fate
import Orig.Twin
import Orig.Macro
import Orig.Mono
import Orig.Phase
import Orig.Combine

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
   reversible round trip (drain + redeal) and the head `iff` are
   still on the card.
7. Tickets, in dependency order:
   - `step` preserves `State.WF` (the conservation invariant, all
     six move kinds);
   - `State.initial` of a `Deal.WF` deal is `WF`;
   - search integrity at `WF` states (`pileOfTop`/`pileHolding`
     unique), and the self-blocking facts that make `canPlace` safe
     without cross-pile side conditions;
   - the irreversibility classification: tabulating each move
     against the three measures and instantiating the bridge.  The
     measure tables (`Orig.Irreversible`, in flight) feed this
     bridge; the draw rows are `Orig.Phase` above.  The remaining
     work: the undo witnesses for the reversible half (worry-back
     round trips), the foundTotal no-worry row, and the
     classification assembly;
   - the arrangement-blind abstraction `α` and its replay license —
     the bridge to `Klondike.*`;
   - the futures count: a commitment leaves at most two
     `sameFate`-distinct successors, per accommodation window —
     restated on the original game, with the `Klondike` witness
     corpus re-derived here first.
-/
