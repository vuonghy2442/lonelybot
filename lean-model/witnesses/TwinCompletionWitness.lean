import Klondike.TwinSwapCompletion

/-!
# TwinCompletionWitness — the O3/O1 residue's two licenses are genuine

The two accessibility licenses that `Klondike/TwinSwapCompletion.lean`
carries as premises are NOT derivable in general — each has a concrete
finite obstruction.  These are the skeletons for the residue tickets
recorded in FARM.md (wave 17); the finite checks below are
machine-checked `decide` facts, not heuristic probes.

## A — the per-card accessibility premise (`haccess`) is necessary

`State.solvable_swapTwin_catchup` (the pure catch-up window) hypothesizes
that the catch-up segment is playable at the PRE-firing state A.  The
obstruction: a catch-up card buried DIRECTLY UNDER the twin — its
`pileStack` guard `topOf (inr c) = none` reads the twin's own seat, so
the catch-up card becomes stackable exactly when the twin's stacking
freed it.  The window play [stack t; catch-up; …] exists; the reordered
[catch-up; …] does not — the license cannot be dropped.

Witness: t = ♦5 (diamond at rung 4), t' = ♥5 (hearts at rung 2 — the
asymmetric O3 boundary).  The catch-up card ♥3 is dealt under ♦5: board
p0: ♥3 with ♦5 on top.  Stacking ♦5 bares ♥3's seat; before that, ♥3's
`pileStack` is blocked.

## B — the covered-twin canonicalization corner (§6.5's residue)

`twin_stack_order_exchange_catchup` hypothesizes that the LOW twin
fires at the reordered state (`hacc`'s second license).  The
obstruction: the mate seated on the twin — with the high twin ON TOP of
the low twin, the L-first firing is blocked while the covered-twin
configuration stands (exactly §6.5's "both twins visible, one covered":
the sweep must keep the unstacked twin's ordering rather than flip it
— the flipped reading is refuted as a *free* reshaping, and the
safety of the canonical pick continues to run through the win-shape's
own first player).

Witness: L = ♥5, H = ♦5, board p1: ♥5 with ♦5 on top; hearts = diamonds
= 4 (both twins at the rung).  `pileStack ♥5` is blocked (covered by
♦5); `pileStack ♦5` fires.  The L-first reshaping needs the mate gone
first — the canonicalizer may only flip the pair at states where the
covered-twin corner is absent.

## C — the deferral's pre-catch-up fireability is necessary (wave 19)

`State.solvable_swapTwin_mixed_back_catchupfirst` resolves wave 18's
catch-up-first→between DEFERRAL license-free, because the between
window's `q₁` may swallow the whole catch-up (the empty-mid
re-bracketing).  What that genuinely forecloses is the LICENSED
LITERAL SPLIT — re-seating the mirror's mid BETWEEN the two stackings
(`[q₁; stack t'; mid; stack t; q₂]` with the mid nonempty): it needs
the mirror's first stacking to fire BEFORE the mid, and here that
fails twice over.

Witness: u = ♥5 (the mirror's first-stacked twin — the flipped
roles of witness A), with the catch-up card ♥3 dealt ONTO it (board
p1: ♥5, cell (inr ♥5): ♥3 — the flipped witness-A corner: the
catch-up card sitting ON the twin, uncovered only by its own raise
mid-catch-up), the second catch-up card ♥4 at p2; hearts = 2.
The catch-up-first bracket [raise ♥3 (frees u's seat, hearts 2→3);
raise ♥4 (3→4); stack ♥5 (rung 4, seat now bare)] fires in order; the
deferral's first step `[stack ♥5; …]` does not (the SEAT corner: ♥3
still covers the twin), and even after the uncovering raise the early
stack stays blocked (the RUNG pin: 3 ≠ 4 — only the full catch-up sets
the rung).  Both obstructions are guard readings of this one state,
machine-checked below.

Witnesses A, B and C are deliberately minimal non-WF countermodels
(the licenses are premises, so necessity does not require WF); the
analytic content throughout is the guard readings — rank-financial
facts of the specific states.
-/

namespace TwinCompletionWitness

abbrev wh3 : Card := ⟨Suit.heart, Rank.three⟩
abbrev wh5 : Card := ⟨Suit.heart, Rank.five⟩
abbrev wd5 : Card := ⟨Suit.diamond, Rank.five⟩

/-- Witness A's board: p0 carries ♥3 with ♦5 on top (♥3 is the twin's
under-card — the catch-up card). -/
def wboardA : Board :=
  ((Board.empty.attach (Sum.inl Anchor.p0) wh3).getD Board.empty
    |>.attach (Sum.inr wh3) wd5).getD Board.empty

/-- Witness A: t = ♦5 stackable (diamond 4), hearts at rung 2 with the
catch-up card ♥3 buried under the twin. -/
def wstA : State where
  deal := { piles := fun _ => [], stock := [] }
  board := wboardA
  heights := fun s => if s = Suit.diamond then 4
    else if s = Suit.heart then 2 else 0
  depths := fun _ => 0
  stock := ⟨[], 0⟩
  drawStep := 1

/-- Witness B's board: p1 carries ♥5 with ♦5 on top (the covered-twin
corner: the high twin seated on its mate). -/
def wboardB : Board :=
  ((Board.empty.attach (Sum.inl Anchor.p1) wh5).getD Board.empty
    |>.attach (Sum.inr wh5) wd5).getD Board.empty

/-- Witness B: both twins at the rung (diamond = heart = 4), but ♥5 is
covered by its mate ♦5. -/
def wstB : State where
  deal := { piles := fun _ => [], stock := [] }
  board := wboardB
  heights := fun s => if s = Suit.diamond then 4
    else if s = Suit.heart then 4 else 0
  depths := fun _ => 0
  stock := ⟨[], 0⟩
  drawStep := 1

-- A: the twin ♦5 is stackable now (diamond 4, bare at the rung's card):
/-- info: true -/
#guard_msgs in
#eval (wstA.apply (Move.pileStack wd5)).isSome

-- A: the catch-up card ♥3 is BLOCKED while the twin sits on it:
/-- info: false -/
#guard_msgs in
#eval (wstA.apply (Move.pileStack wh3)).isSome

-- A: ...and fires exactly once the twin's stacking freed its seat:
/-- info: true -/
#guard_msgs in
#eval ((wstA.apply (Move.pileStack wd5)).bind
  fun s => s.apply (Move.pileStack wh3)).isSome

-- B: L = ♥5 is covered by its mate — the L-first firing is blocked:
/-- info: false -/
#guard_msgs in
#eval (wstB.apply (Move.pileStack wh5)).isSome

-- B: H = ♦5 fires (the unstacked twin keeps the ordering):
/-- info: true -/
#guard_msgs in
#eval (wstB.apply (Move.pileStack wd5)).isSome

/-- The prover-confirmed core (A): the window play fires, the reordered
catch-up is blocked — `haccess` is genuinely a license, not a theorem. -/
example : ((wstA.apply (Move.pileStack wd5)).bind
      fun s => s.apply (Move.pileStack wh3)).isSome = true
    ∧ (wstA.apply (Move.pileStack wh3)).isSome = false := by
  decide

/-- The prover-confirmed core (B): at equal twin rungs the covered
twin cannot be flipped first — the canonicalization's flipped reading
needs the mate gone first. -/
example : (wstB.apply (Move.pileStack wh5)).isSome = false
    ∧ (wstB.apply (Move.pileStack wd5)).isSome = true := by
  decide

abbrev wh4 : Card := ⟨Suit.heart, Rank.four⟩

/-- Witness C's board, first cell: p1 carries ♥5 with the catch-up
card ♥3 ON TOP of it (the flipped witness-A corner: the twin sits
UNDER the catch-up card, uncovered only by the raise itself). -/
def wboardC0 : Board :=
  ((Board.empty.attach (Sum.inl Anchor.p1) wh5).getD Board.empty
    |>.attach (Sum.inr wh5) wh3).getD Board.empty

/-- Witness C's board: the covered twin plus p2 carrying ♥4 (the
second rung of the catch-up). -/
def wboardC : Board :=
  (wboardC0.attach (Sum.inl Anchor.p2) wh4).getD Board.empty

/-- Witness C: hearts at 2 (the first raise's rung), the twin ♥5
covered by its own suit's catch-up card ♥3. -/
def wstC : State where
  deal := { piles := fun _ => [], stock := [] }
  board := wboardC
  heights := fun s => if s = Suit.heart then 2 else 0
  depths := fun _ => 0
  stock := ⟨[], 0⟩
  drawStep := 1

-- C: the catch-up-first bracket fires in order —
-- raise ♥3 (uncovering the twin, hearts 2→3), raise ♥4 (3→4),
-- stack ♥5 (the rung, the now-bare seat):
/-- info: true -/
#guard_msgs in
#eval (((wstC.apply (Move.pileStack wh3)).bind (fun s =>
    s.apply (Move.pileStack wh4))).bind (fun s =>
    s.apply (Move.pileStack wh5))).isSome

-- C: the deferral's first step is blocked — the pre-catch-up
-- `stack ♥5` dies on the SEAT corner (♥3 covers the twin) and on the
-- rung (2 ≠ 4):
/-- info: false -/
#guard_msgs in
#eval (wstC.apply (Move.pileStack wh5)).isSome

-- C: even past the uncovering raise the early stack stays blocked —
-- the RUNG pin (3 ≠ 4; only the full catch-up sets the rung):
/-- info: false -/
#guard_msgs in
#eval (((wstC.apply (Move.pileStack wh3)).bind (fun s =>
    s.apply (Move.pileStack wh5)))).isSome

/-- The prover-confirmed core (C): the catch-up-first bracket fires,
the pre-catch-up fireability of the first stacking (the licensed
literal between-split's premise) does not exist at this window — the
deferral's license is genuinely necessary, hence REFUTABLE as stated. -/
example : (((wstC.apply (Move.pileStack wh3)).bind (fun s =>
      s.apply (Move.pileStack wh4))).bind (fun s =>
      s.apply (Move.pileStack wh5))).isSome = true
    ∧ (wstC.apply (Move.pileStack wh5)).isSome = false := by
  decide

end TwinCompletionWitness
