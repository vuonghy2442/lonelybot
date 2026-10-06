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

/-! ## D/E — THE WAVE-22 DECISION CERTIFICATE for
`sweep_covered_corner_safety`

The pin (`State.sweep_covered_corner_safety`, the covered corner's
iff) is TwinSwapCompletion's last census pin.  Three waves landed its
corridor kit; this section records the certified residue map — every
remaining obstruction expressed as a small CONCRETE state family
with its machine-checkable verdicts below (the `#eval`s and `decide`
examples are the evidence; the commentary is the analysis).

**THE OBSTRUCTION CLASS (what the residue protects against).**

* **The class-B corner** (witness E): the L-SEATED corner — the
  covered twin VISIBLE (seated at its deal-head anchor), the unfit
  mate covering it.  WF-legal (`board_edges`'s buried-base clause
  admits it through `bottomOf L` being `isSome`), but a
  `visClean` VIOLATION (`canSitOn H L = false` at the twins), hence
  — since `initial_visClean` + `run_visClean` + the class-A theorem
  `sweep_covered_corner_visClean_class_A` — UNREACHABLE from every
  deal: `initialReachable wstE → False` is machine-checked below.
  AT this family the image's `pileStack L` channel is LIVE while the
  source's is mate-blocked — the unguarded theorem must still win
  there through the deferred dodge-or-found story (dualized); no
  counterexample exists (both sides are equally stuck at the exhibit,
  so the iff holds vacuously there — the witness pins the SHAPE, not
  a refutation).
* **The license-fit hole** (rank core; witnessed at BOTH D and E):
  `canSitOn H L = false` at the twins — the covering cargo IS the
  mate, so the PROVEN exchange rows
  (`solvable_cargoTwin_exchange_licensed`, `_of_visClean`, the bare
  companion `solvable_cargoTwin_exchange_bare`) can never seat the
  corner in either thread.  Its rider-side shadow at the reachable
  class A (witness D): `canPlace x (Sum.inr H) = true` at the source
  while the relabeled `canPlace x (Sum.inr L) = false` at the image —
  the rider park a corridor cannot mirror (the w15fithole
  license-fit shape: no image move attaches onto an unseated host).
* **The reveal-channel divergence** (witness D): at the reachable
  class-A corner the source's reveal of the covered twin is
  RIDDEN-BOUNDARY-BLOCKED (the guard reads the twin's OWN cell; the
  mate sits there) while the image's copy of the same guard reads
  `none` and the image's reveal FIRES — the reverse leg's ONE extra
  channel, formalized as `sweep_covered_corner_image_reveal_fires`
  (TwinSwapCompletion).

**THE MINIMAL PREMISES (named and stated exactly).**

* (P-i) **the no-park discipline at the source**: every solvable
  class-A corner state is solvable by a winning line whose first
  covered-seat clearing is the mate's dodge `Move.pilePile H b` and
  whose pre-clearing segment never parks a rider on `Sum.inr H` —
  i.e. the `hmids` corridor premise's SECOND conjunct; conjuncts 1
  (the cover holds throughout the pre-clearing prefix) and 3 (the
  covered twin stays unseated) are now DERIVABLE —
  `covered_corner_reveal_blocked` is exactly the fact that closes
  the only seating channel (`bottomOf L = none` can only change at a
  `reveal` of `L`, and while the cover stands that reveal is
  blocked).
* (P-ii) **the deferred unpark of the found branch**: at the
  source's `Move.pileStack H` clearing (decided live at E from the
  source side), the image's mate — self-seat frozen, witnessed at E
  as blocked — must find a fitted free base by the moment the
  source's tail seats a crossed host; the REFUTE-FIRST candidate
  (BOTH crossed hosts deckStack-founded, never seated) is unprobed
  on the engine corpus, the honest corpus gap below.
* (P-iii) **the dual of (P-i)+(P-ii) at the image**, with the
  reveal channel substituting for the park.

With (P-i) both dodge branches of the forward leg CLOSE through the
PAID corridor + merge (`sweep_covered_corner_dodge_clearing_forward`
and its engine theorems); (P-ii)/(P-iii) are the same lemma families
conjugated by the Board conjugation kit.

**THE CORPUS VERDICT.**  The gate `initialReachable` is non-vacuous
with zero moves of slack — witness D realizes the covered corner AT
`State.initial (Deal.ofList dlD) 1`: any deal dealing the twin pair
consecutively at the top of a pile (the deal step attaches the upper
twin at the lower's cell) carries the corner from the game's first
state, `example : initialReachable wstD` below.  The
engine-trajectory failure rates of (P-i)'s pre-clearing parks and
(P-ii)'s closed-target windows are NOT measured by any existing
corpus mode (the wave-21 modes measured frozen kings, route urgency,
and promotion irreversibility — adjacent but disjoint); that
measurement is the designated next probe task.

**RECOMMENDATION (to the orchestrator): CONTINUE-THE-SIEGE.**  No
counterexample to the ungated statement was found in three waves or
at this certificate's witnesses; the class split keeps the
unconditional statement plausible; the three remaining pieces are
scoped lemma families over the paid corridor principle; park-and-
promote would strand the wave-20/21 investment one assembly short.

### D — the reachable class-A corner at the dealt initial state

Cast: `L = ♥5` (hidden at p2's reveal boundary), `H = ♦5` (face-up
covering `Sum.inr ♥5`, its own cell bare), `d = ♣4` (the under-card,
hidden one deeper), `♠6` dealt as p5's TOP (the visible dodge
target), `♠4` the probe rider (a fitting `canPlace` for the mate's
cover cell).  All clubs/spades piled, the red non-twin cards stocked.
-/

abbrev wss6 : Card := ⟨Suit.spade, Rank.six⟩
abbrev wss4 : Card := ⟨Suit.spade, Rank.four⟩

def cd (s : Suit) (r : Rank) : Card := ⟨s, r⟩

/-- Witness D's deal: the twin pair ♥5/♦5 dealt consecutively as p2's
top two cards ([♣4, ♥5, ♦5]), so the initial deal step SEATS the mate
on the covered cell — the corner exists at the game's first state. -/
def dlD : List Card :=
  [ cd .club .ace
  , cd .club .two, cd .club .three
  , cd .club .four, cd .heart .five, cd .diamond .five
  , cd .club .five, cd .club .six, cd .club .seven, cd .club .eight
  , cd .club .nine, cd .club .ten, cd .club .jack, cd .club .queen, cd .club .king
  , cd .spade .ace, cd .spade .two, cd .spade .three, cd .spade .four
  , cd .spade .five, cd .spade .six
  , cd .spade .seven, cd .spade .eight, cd .spade .nine, cd .spade .ten
  , cd .spade .jack, cd .spade .queen, cd .spade .king ] ++
  [ cd .heart .ace, cd .heart .two, cd .heart .three, cd .heart .four
  , cd .heart .six, cd .heart .seven, cd .heart .eight, cd .heart .nine
  , cd .heart .ten, cd .heart .jack, cd .heart .queen, cd .heart .king ] ++
  [ cd .diamond .ace, cd .diamond .two, cd .diamond .three, cd .diamond .four
  , cd .diamond .six, cd .diamond .seven, cd .diamond .eight, cd .diamond .nine
  , cd .diamond .ten, cd .diamond .jack, cd .diamond .queen, cd .diamond .king ]

/-- **The covered corner AT the dealt initial state** — zero moves:
`State.initial` itself is the class-A corner shape. -/
def wstD : State := State.initial (Deal.ofList dlD) 1

theorem dlD_length : dlD.length = 52 := by decide

theorem dlD_noDup : noDupCards dlD := by
  intro i j hi hj heq
  rw [dlD_length] at hi hj
  have hall : ∀ i ∈ List.range 52, ∀ j ∈ List.range 52,
      dlD[i]? = dlD[j]? → i = j := by
    decide
  exact hall i (List.mem_range.mpr hi) j (List.mem_range.mpr hj) heq

-- D: the deal is the full disjoint 52:
/-- info: 52 -/
#guard_msgs in
#eval dlD.length

-- D: THE CORNER READS (the class-A shape, all decided together below):
/-- info: true -/
#guard_msgs in
#eval wstD.board.topOf (Sum.inr wh5) == some wd5
/-- info: true -/
#guard_msgs in
#eval wstD.board.topOf (Sum.inr wd5) == none
/-- info: false -/
#guard_msgs in
#eval wstD.isVis wh5
/-- info: true -/
#guard_msgs in
#eval wstD.topHidden Anchor.p2 == some wh5
/-- info: true -/
#guard_msgs in
#eval wstD.board.bottomOf wh5 == none

/-- The prover-confirmed corner core (D): the covered cell is the
mate's, the mate's own cell is bare, the covered twin is an unseated
hidden boundary — the class-A certificates of the class split. -/
example : wstD.board.topOf (Sum.inr wh5) = some wd5
    ∧ wstD.board.topOf (Sum.inr wd5) = none
    ∧ wstD.isVis wh5 = false
    ∧ wstD.topHidden Anchor.p2 = some wh5
    ∧ wstD.board.bottomOf wh5 = none := by
  decide

-- D: THE REACHABILITY VERDICT — the witness IS a dealt initial state,
-- so the reachable form of the safety pin is non-vacuous by exhibit:
example : initialReachable wstD :=
  ⟨Deal.ofList dlD, 1, [], Deal.ofList_wf dlD_length dlD_noDup,
    by decide, rfl⟩

-- D: THE LICENSE-FIT HOLE — the covering cargo IS the mate, and the
-- twin never fits its mate (so neither licensed row nor the bare
-- companion can be seated at the corner):
/-- info: false -/
#guard_msgs in
#eval canSitOn wd5 wh5
/-- info: true -/
#guard_msgs in
#eval wstD.board.bottomOf wd5 == some (Sum.inr wh5)

example : canSitOn wd5 wh5 = false := by decide

-- D: THE RIDER-PARK ASYMMETRY (the w15fithole license-fit shape): a
-- fitting rider can be placed on the MATE'S cover cell at the source…
/-- info: true -/
#guard_msgs in
#eval wstD.canPlace wss4 (Sum.inr wd5)
-- …but the corridor's relabeled copy onto the covered twin's cell
-- dies at the image on the unseated host:
/-- info: false -/
#guard_msgs in
#eval (wstD.exchangeTwinCargo wh5).canPlace wss4 (Sum.inr wh5)

/-- The prover-confirmed channel core (D): the park on the mate's
cover cell is guard-live at the source and guard-dead at the image. -/
example : wstD.canPlace wss4 (Sum.inr wd5) = true
    ∧ (wstD.exchangeTwinCargo wh5).canPlace wss4 (Sum.inr wh5) = false := by
  decide

-- D: THE REVEAL-CHANNEL DIVERGENCE — the source's reveal of the
-- covered twin is ridden-boundary-blocked…
/-- info: false -/
#guard_msgs in
#eval (wstD.apply (Move.reveal Anchor.p2)).isSome
-- …the image's copy of the guard reads `none` and the move FIRES:
/-- info: true -/
#guard_msgs in
#eval ((wstD.exchangeTwinCargo wh5).apply (Move.reveal Anchor.p2)).isSome

/-- The prover-confirmed reveal core (D): blocked at the source, open
at the image — the reverse leg's extra channel in two reads. -/
example : (wstD.apply (Move.reveal Anchor.p2)).isSome = false
    ∧ ((wstD.exchangeTwinCargo wh5).apply (Move.reveal Anchor.p2)).isSome = true := by
  decide

-- D: THE MATE'S DODGE and the threads' merge (the wave-20 clean
-- merge re-verified): the mate dodges onto the dealt ♠6 top; the
-- image plays the SAME dodge…
def dodgeM : Move := Move.pilePile wd5 (Sum.inr wss6)

/-- info: true -/
#guard_msgs in
#eval (wstD.apply dodgeM).isSome
/-- info: true -/
#guard_msgs in
#eval ((wstD.exchangeTwinCargo wh5).apply dodgeM).isSome

/-- Full-field equality of the two threads after the same dodge (the
clean merge, decided over the board, deal, heights, depths, stock,
and draw step). -/
def dodgeMergeEq : Bool :=
  match wstD.apply dodgeM, (wstD.exchangeTwinCargo wh5).apply dodgeM with
  | some s₁, some s₂ =>
      Board.enumBase.all (fun b => s₁.board.topOf b == s₂.board.topOf b)
      && Anchor.all.all (fun a => s₁.deal.piles a == s₂.deal.piles a)
      && s₁.deal.stock == s₂.deal.stock
      && Suit.all.all (fun s => s₁.heights s == s₂.heights s)
      && Anchor.all.all (fun a => s₁.depths a == s₂.depths a)
      && s₁.stock.cards == s₂.stock.cards && s₁.stock.cursor == s₂.stock.cursor
      && s₁.drawStep == s₂.drawStep
  | _, _ => false

/-- info: true -/
#guard_msgs in
#eval dodgeMergeEq

example : dodgeMergeEq = true := by decide

-- D: THE FOUND-BRANCH STATICS — the image's mate is self-seated
-- (its found is guard-blocked even at a ready rung; at this
-- heights-0 exhibit the rung is additionally unready on both sides):
/-- info: true -/
#guard_msgs in
#eval (wstD.exchangeTwinCargo wh5).board.topOf (Sum.inr wd5) == some wd5
/-- info: false -/
#guard_msgs in
#eval ((wstD.exchangeTwinCargo wh5).apply (Move.pileStack wd5)).isSome
/-- info: false -/
#guard_msgs in
#eval (wstD.apply (Move.pileStack wd5)).isSome

/-! ### E — the class-B license-fit-while-mate-sits corner (WF, unreachable)

Cast: `L = ♥5` VISIBLE, seated at p4's ANCHOR as the deal HEAD of
p4 = [♥5, ♦5, ♠J, ♠Q, ♠K] (the [L, H] deal adjacency at the head —
`board_edges`'s buried-base clause admits the mate's cover through
`bottomOf L` being `isSome`); `H = ♦5` on `Sum.inr ♥5`; the hearts
and diamonds rungs both at 4 (the `stackL`/`stackH` channels are
rung-ready), the below-rung red cards consumed (empty cycle, fithole's
pattern); depths all zero (no hidden cards, no reveal channels). -/

/-- Witness E's deal: the twin pair dealt consecutively as p4's first
two cards (the buried-base adjacency at the pile's head). -/
def dlE : List Card :=
  [ cd .spade .ace
  , cd .spade .two, cd .spade .three
  , cd .spade .four, cd .spade .five, cd .spade .six
  , cd .spade .seven, cd .spade .eight, cd .spade .nine, cd .spade .ten
  , cd .heart .five, cd .diamond .five
  , cd .spade .jack, cd .spade .queen, cd .spade .king
  , cd .club .ace, cd .club .two, cd .club .three
  , cd .club .four, cd .club .five, cd .club .six
  , cd .club .seven, cd .club .eight, cd .club .nine
  , cd .club .ten, cd .club .jack, cd .club .queen, cd .club .king ] ++
  [ cd .heart .ace, cd .heart .two, cd .heart .three, cd .heart .four
  , cd .heart .six, cd .heart .seven, cd .heart .eight, cd .heart .nine
  , cd .heart .ten, cd .heart .jack, cd .heart .queen, cd .heart .king ] ++
  [ cd .diamond .ace, cd .diamond .two, cd .diamond .three, cd .diamond .four
  , cd .diamond .six, cd .diamond .seven, cd .diamond .eight, cd .diamond .nine
  , cd .diamond .ten, cd .diamond .jack, cd .diamond .queen, cd .diamond .king ]

/-- The rungs: hearts and diamonds at 4 — both twins' `pileStack`
channels are rung-ready; the below-rung cards are foundation-gone
(empty cycle, all depths zero). -/
def hE : Suit → Nat := fun s =>
  match s with
  | .heart => 4
  | .diamond => 4
  | _ => 0

/-- Witness E's board: L = ♥5 at p4's anchor (its deal head), H = ♦5
covering `Sum.inr ♥5`, the mate's own cell bare. -/
def bE : Board :=
  ((Board.empty.attach (Sum.inl Anchor.p4) wh5).getD Board.empty
    |>.attach (Sum.inr wh5) wd5).getD Board.empty

/-- **The class-B corner**: WF (fithole's replica decides below),
visClean-violating (the unfit mate over a visible host), hence
unreachable from every deal. -/
def wstE : State :=
  State.mk (Deal.ofList dlE) bE hE (fun _ => 0) (Cycle.mk [] 0) 1

-- E1: the deal is the full 52 and the twin pair heads p4:
/-- info: 52 -/
#guard_msgs in
#eval dlE.length
/-- info: true -/
#guard_msgs in
#eval ((Deal.ofList dlE).piles Anchor.p4).head? == some wh5
/-- info: 5 -/
#guard_msgs in
#eval ((Deal.ofList dlE).piles Anchor.p4).length

-- E1: the corner reads — `L` VISIBLE this time (the class split's
-- other half), the cover unfit, the mate's cell bare:
/-- info: true -/
#guard_msgs in
#eval wstE.board.topOf (Sum.inr wh5) == some wd5
/-- info: true -/
#guard_msgs in
#eval wstE.board.topOf (Sum.inr wd5) == none
/-- info: true -/
#guard_msgs in
#eval wstE.isVis wh5
/-- info: true -/
#guard_msgs in
#eval wstE.board.bottomOf wh5 == some (Sum.inl Anchor.p4)

/-- The prover-confirmed class-B core (E): the corner shape with a
VISIBLE covered twin — the visClean-violating half of the split. -/
example : wstE.board.topOf (Sum.inr wh5) = some wd5
    ∧ wstE.board.topOf (Sum.inr wd5) = none
    ∧ wstE.isVis wh5 = true
    ∧ canSitOn wd5 wh5 = false := by
  decide

-- E2: the reflexive WF replica (fithole's, verbatim: the 11
-- conjuncts over the crafted state) — E is genuinely WF:
def consec (l : List Card) (d c : Card) : Bool :=
  match l with
  | x :: y :: rest => (x == d && y == c) || consec (y :: rest) d c
  | _ => false

def edgeOK (st : State) (b : Base) (c : Card) : Bool :=
  match b with
  | Sum.inl a => c.rank == Rank.king || (st.deal.piles a).head? == some c
  | Sum.inr d =>
      (Anchor.all.any (fun a => consec (st.deal.piles a) d c) &&
        (Anchor.all.any (fun a' => st.topHidden a' == some d) ||
          (st.board.bottomOf d).isSome)) ||
      ((st.board.bottomOf d).isSome && canSitOn c d)

def nodupB (l : List Card) : Bool := l.all (fun x => l.count x == 1)

def wfCheck (st : State) : Bool :=
  Anchor.all.all (fun a => (st.deal.piles a).length == a.toIdx + 1) &&
  st.deal.stock.length == 24 &&
  nodupB ((Anchor.all.flatMap st.deal.piles) ++ st.deal.stock) &&
  Anchor.all.all (fun a => decide (st.depths a <= (st.deal.piles a).length)) &&
  Board.enumBase.all (fun b =>
    match st.board.topOf b with
    | none => true
    | some c => (st.board.bottomOf c == some b) && edgeOK st b c) &&
  Card.universe.all (fun c =>
    !(st.isVis c) || st.stock.posOf c == none) &&
  Card.universe.all (fun c =>
    !(st.onFound c) || st.stock.posOf c == none) &&
  Card.universe.all (fun c =>
    !decide (c.rank.toIdx < st.heights c.suit) ||
      (!(st.isVis c) && st.stock.posOf c == none &&
        Anchor.all.all (fun a => !((st.hidden a).contains c)))) &&
  Card.universe.all (fun c =>
    !(st.isVis c) || Anchor.all.all (fun a => !((st.hidden a).contains c))) &&
  Suit.all.all (fun s => decide (st.heights s <= 13)) &&
  decide (st.stock.cursor <= st.stock.cards.length) &&
  0 < st.drawStep &&
  nodupB st.stock.cards &&
  st.stock.cards.all (fun c => st.deal.stock.contains c)

/-- info: true -/
#guard_msgs in
#eval wfCheck wstE
/-- info: true -/
#guard_msgs in
#eval wfCheck wstD

-- E3: THE UNREACHABILITY VERDICT — class B cannot arise from any
-- dealt game: reachable states are visClean, and the visClean corner
-- forces the HIDDEN class (`sweep_covered_corner_visClean_class_A`),
-- contradicting the visible seated twin:
example : initialReachable wstE → False := by
  intro hreach
  obtain ⟨hwfE, hvcE⟩ := initialReachable_visClean hreach
  obtain ⟨-, -, -, hbotL⟩ :=
    sweep_covered_corner_visClean_class_A (L := wh5) (H := wd5) hwfE hvcE
      rfl (by decide)
  exact absurd hbotL (by decide)

-- E4: THE CHANNEL INVERSION (the license-fit-while-mate-sits family,
-- decided): the source founds the mate directly (the found-branch
-- clearing is live at the rung)…
/-- info: true -/
#guard_msgs in
#eval (wstE.apply (Move.pileStack wd5)).isSome
-- …while the image's mate is SELF-SEAT-FROZEN (its own cell hosts
-- itself after the swap; no dodge target exists on this board):
/-- info: false -/
#guard_msgs in
#eval ((wstE.exchangeTwinCargo wh5).apply (Move.pileStack wd5)).isSome
-- the source's own twin is mate-COVERED (its found is blocked)…
/-- info: false -/
#guard_msgs in
#eval (wstE.apply (Move.pileStack wh5)).isSome
-- …while the image's copy of the same guard reads `none` and the
-- L-FIRST founding channel is LIVE — the order flip the unguarded
-- theorem must justify at this family:
/-- info: true -/
#guard_msgs in
#eval ((wstE.exchangeTwinCargo wh5).apply (Move.pileStack wh5)).isSome

/-- The prover-confirmed channel inversion (E): the found-branch
(founded mate / frozen mate) and the order-flipped L-channel live
only at the image — the exact guard-divergence family the residues
(P-ii)/(P-iii) must bridge. -/
example : (wstE.apply (Move.pileStack wd5)).isSome = true
    ∧ ((wstE.exchangeTwinCargo wh5).apply (Move.pileStack wd5)).isSome = false
    ∧ (wstE.apply (Move.pileStack wh5)).isSome = false
    ∧ ((wstE.exchangeTwinCargo wh5).apply (Move.pileStack wh5)).isSome = true := by
  decide

-- E5: the mate's DODGE-STARVATION at E (the closed-target statics of
-- the found branch): the only visible cards are the twins themselves
-- (no free anchor for a non-king) — every pilePile-dodge base is
-- blocked; the source's only L-clearing channel IS the direct found:
/-- info: false -/
#guard_msgs in
#eval (wstE.apply (Move.pilePile wd5 (Sum.inl Anchor.p0))).isSome
/-- info: false -/
#guard_msgs in
#eval (wstE.apply (Move.pilePile wd5 (Sum.inl Anchor.p6))).isSome
/-- info: false -/
#guard_msgs in
#eval (wstE.apply (Move.pilePile wd5 (Sum.inr wh5))).isSome

end TwinCompletionWitness
