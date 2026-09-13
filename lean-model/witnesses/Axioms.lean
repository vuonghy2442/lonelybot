import Klondike.Dominance
import Klondike.Macro
import Klondike.Pace
import Klondike.Progress
import Klondike.Relabel
import Klondike.Theorems

/-!
# The axioms gate — the crown theorems stay axiom-clean

`#print axioms` for the farm's crown theorems, pinned under
`#guard_msgs`.  Every crown theorem must come out depending only on
`propext` and `Quot.sound` — plus `Classical.choice` exactly where its
proof genuinely uses classical reasoning (marked per-theorem below;
that is a legitimate axiom, not dirt).

Any OTHER axiom — `sorryAx` above all — fails the guard.  That is a
FINDING, not a chore: do not update an expectation to match a dirty
run; record it in FARM_MEMORY and escalate to the orchestrator.

Baseline taken 2026-09-13 against the oleans of the post-wave-10
consolidation (toolchain v4.33.1, census 11).
-/

/-- info: 'cascade_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms cascade_sound

/-- info: 'pace_dominance' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms pace_dominance

/-- info: 'pace_dominance_residue' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms pace_dominance_residue

/-- info: 'pace_dominance_impure_pure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms pace_dominance_impure_pure

/-- info: 'window_firstDraw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms window_firstDraw

/-- info: 'window_firstDraw_macro' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms window_firstDraw_macro

/-- info: 'solvable_relabel' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms solvable_relabel

/-- info: 'solvable_flipAll' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms solvable_flipAll

/-- info: 'Pace.realizes_iff_stepsOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Pace.realizes_iff_stepsOK

/-- info: 'applyDrawTo_eq_dealPlay' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms applyDrawTo_eq_dealPlay

/-- info: 'applyDrawStackTo_eq_dealPlay' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms applyDrawStackTo_eq_dealPlay

/-- info: 'solvable_of_stackPile' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms solvable_of_stackPile

/-- info: 'solvable_of_pileStack_return' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms solvable_of_pileStack_return

/-- info: 'dominant_of_commutesWithAll' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms dominant_of_commutesWithAll

/-- info: 'deckPile_safe_prunable' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms deckPile_safe_prunable

/-- info: 'safe_pileStack_dominant_of_return' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms safe_pileStack_dominant_of_return

/-- info: 'cascade_escape_progress' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms cascade_escape_progress

/-- info: 'solvable_em' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms solvable_em

/- C1 — the macro reduction (Macro.lean, proven 2026-09-13; the
witness for its def repair is witnesses/MacroC1Witness.lean). -/

/-- info: 'engine_of_macro' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms engine_of_macro

/-- info: 'macro_of_engine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms macro_of_engine

/-- info: 'macroSteps_engine_run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms macroSteps_engine_run

/-- info: 'engine_macro_lift' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms engine_macro_lift
