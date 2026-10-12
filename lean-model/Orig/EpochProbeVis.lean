import Orig.EpochProbe

/-!
# Orig.EpochProbeVis — THE VISIBLE-ISLAND DRESSER PROBE

The decisive variant of `Orig.EpochProbe`'s downward craft: does a
REVERSIBLE dresser exist on the rank-5-fork economy — two
different-rank forks in ONE reversible class — or is the dressing
commitment STRUCTURAL?  Every row a kernel-decided fact under a
`theorem` wrapper, zero sorry.

THE HYPOTHESIS UNDER TEST (the visible island): seat the dresser 3♣
over a FACE-UP residue topped by the black 4♠ — faceUp
`= [residue…, 4♠, 3♣]` — so the dressing slide's departure leaves the
4♠ topping a nonempty residue (no reveal), and the one-move mirror
`Move.tabToTab C3 (Sum.inr S4)` slides the 3♣ back home onto that
residue-top.  THE FIT AUDIT (§0) kills the hypothesis's own clause
before any board is dealt: `canSitOn C3 S4 = false` — Klondike stacks
opposite colors, and 3-over-4♠ is black-on-black — so `runOK
[S4, C3] = false` and NO `WF` state can host the prescribed island
(the under-seat scan `vis_seats` decides that the dresser's legal
seats are exactly the two RED fours).  The probe then builds the
MAXIMAL LEGAL variant of the mandated economy (`vis0`): the spade
column mirrored exactly as asked — 4♠ unfounded and FACE-UP as a
residue-top, hosted bare-bottom over the spade sink where the seat
bar (not the stock) silences it — while the 3♣ keeps the only legal
dresser shape, the island over a hidden club deck.  The walk pulls
the two red fours onto the two black-5 anchors, slides the dressing,
and THE MIRROR ROW decides the hypothesis's fate.

THE FINDINGS, banked decide-grade:

* **The fit kill (§0)** — the prescribed black-4 residue is unfit;
  the dresser sits only on a red four.
* **The origin lock (§1)** — at the base fork, BOTH red fours sit
  foundation-resident (hearts 4, diamonds 4 — the pair's own
  rungs), so `vis0`'s whole universe refuses the 3♣ a top-target:
  THE VISIBLE ISLAND IS UNBUILDABLE there, and the 3♣ is forced
  bare over the hidden island — the reveal at the departure is
  forced too.
* **The mirror refused (§3)** — at the dressed board the census
  still folds the {4♥, 4♦} pair (the rank-4 fork lands, witness 4♥),
  but the mirror equation `State.step vis3 (Move.tabToTab C3
  (Sum.inr S4)) = none` (rfl): the hosted 4♠ REFUSES the returning
  dresser by the same color bar, and the full landing lattice
  decides that the 3♣'s only top-target is the escape hop 4♥, which
  lands ELSEWHERE; the reveal-descent jury then kills what the
  lattice leaves.  The rank-5 and rank-4 forks are banked on one
  dealt economy, but the class between them ends FORKLESS at `vis2`
  and the dressing leg stays a commitment — **THE SIXTH LANDING IS
  REFUSED STRUCTURALLY; the no-lock pairClass theorem SURVIVES this
  probe** (decide-grade, beside EpochProbe's banked `down_pair`).
-/

/-! ## §0. The private kit and the fit audit -/

private def crd (s : Suit) (r : Rank) : Card := ⟨s, r⟩

/- A suit's foundation prefix at height `n` (the craft's `found`). -/
private def takeUp (s : Suit) (n : Nat) : List Card := s.upCards.take n

/- Oracle step helper (dead-hand plays are construction bugs; the
step theorems below throw — the SProbe/ForkStateUniqGate pattern). -/
private def stepD (st : State) (m : Move) : State :=
  match st.step m with
  | none => st
  | some s' => s'

private def H4 : Card := crd .heart .four
private def H5 : Card := crd .heart .five
private def H6 : Card := crd .heart .six
private def H7 : Card := crd .heart .seven
private def D4 : Card := crd .diamond .four
private def D5 : Card := crd .diamond .five
private def D6 : Card := crd .diamond .six
private def S4 : Card := crd .spade .four
private def S5 : Card := crd .spade .five
private def S6 : Card := crd .spade .six
private def C2 : Card := crd .club .two
private def C3 : Card := crd .club .three
private def C4 : Card := crd .club .four
private def C5 : Card := crd .club .five
private def C6 : Card := crd .club .six
private def C7 : Card := crd .club .seven

/- ### The fit kill — the hypothesis's own clause, audited first

The visible-island hypothesis seats the dresser 3♣ over a black-4
residue: `faceUp = [residue…, 4♠, 3♣]`, claiming the re-landing fits.
The tableau fit decides otherwise — 3♣ on 4♠ is black on black. -/

/-- **THE PRESCRIBED RESIDUE IS UNFIT**: the exact under-seat pair the
hypothesis names fails the fit, and the face-up run it would form is
run-illegal — NO `WF` state can host the prescribed island. -/
theorem vis_blackResidueUnfit :
    canSitOn C3 S4 = false ∧ runOK [S4, C3] = false := ⟨by decide, by decide⟩

/-- **THE UNDER-SEAT SCAN** — over the whole universe, the dresser's
legal face-up seats are exactly the two RED fours. -/
theorem vis_seats :
    ∀ z ∈ Card.universe, canSitOn C3 z = decide (z = H4 ∨ z = D4) := by
  intro z _
  rcases z with ⟨s, r⟩
  cases s <;> cases r <;> decide

/-- **THE OVER-SEAT SCAN** — over the whole universe, the only cards
that may sit face-up ON the dresser are the red twos (a covered
dresser would also build a visible island) — both locked into the
foundations by the base pair's own rungs below. -/
theorem vis_over :
    ∀ z ∈ Card.universe, canSitOn z C3 = decide (z = crd .heart .two ∨
      z = crd .diamond .two) := by
  intro z _
  rcases z with ⟨s, r⟩
  cases s <;> cases r <;> decide

/-! ## §1. The `vis0` board — the maximal legal economy

Rungs ♠ 3 / ♥ 4 / ♦ 4 / ♣ 1 (the EpochProbe `down0` arithmetic): the
{5♥, 5♦} pair lives exactly as the S-craft seats it; clubs at one so
the island's 3♣ dies by rank-read; BOTH black-5 anchors hosted as
pile tops ([6♥, 5♠] and [6♦, 5♣]); and the mirrored spade column:
4♠ UNFOUNDED and face-up as residue-top — hosted bare-bottom over
the spade sink (its rung makes it next-up material, but sitting alone
over a hidden deck, the seat bar — not the stock — silences it). -/

/-- The vis-economy rungs: ♠ 3, ♥ 4, ♦ 4, ♣ 1. -/
private def hmapV : Suit → Nat
  | .heart => 4 | .diamond => 4 | .spade => 3 | .club => 1

/-- **THE VIS-BOARD `vis0`**: p0 = [7♥, 6♠, 5♥] (the rank-5 witness
topping its parent-seated pile); p2 = [6♣, 5♦, 4♣] (the twin under
its cover); p3 = [6♥, 5♠] and p4 = [6♦, 5♣] (the black-5 anchor
piles); p1 = the club island ⟨[7♣ …, K♣], [3♣]⟩ (the 3♣ over the
hidden deck — the ONLY legal shape the fit audit leaves); p5 = the
mirrored spade column ⟨[7♠ …, K♠], [4♠]⟩ (the 4♠ unfounded,
face-up residue-top, seat-barred); p6 hidden sink; stock [2♣];
waste [J♦]; drawStep 1. -/
private def vis0 : State where
  found := fun s => takeUp s (hmapV s)
  piles := fun a => match a with
    | .p0 => ⟨[], [H7, S6, H5]⟩
    | .p1 => ⟨[crd .club .seven, crd .club .eight, crd .club .nine,
               crd .club .ten, crd .club .jack, crd .club .queen,
               crd .club .king], [C3]⟩
    | .p2 => ⟨[], [C6, D5, C4]⟩
    | .p3 => ⟨[], [H6, S5]⟩
    | .p4 => ⟨[], [D6, C5]⟩
    | .p5 => ⟨[crd .spade .seven, crd .spade .eight, crd .spade .nine,
               crd .spade .ten, crd .spade .jack, crd .spade .queen,
               crd .spade .king], [S4]⟩
    | .p6 => ⟨[crd .heart .eight, crd .heart .nine, crd .heart .ten,
               crd .heart .jack, crd .heart .queen, crd .heart .king,
               crd .diamond .seven, crd .diamond .eight, crd .diamond .nine,
               crd .diamond .ten, crd .diamond .queen,
               crd .diamond .king], []⟩
  stock := [C2]
  waste := [crd .diamond .jack]
  drawStep := 1

private theorem vis0_wf_found : ∀ s : Suit, ∃ n, vis0.found s = s.upCards.take n := by
  intro s
  cases s with
  | spade => exact ⟨3, rfl⟩
  | heart => exact ⟨4, rfl⟩
  | diamond => exact ⟨4, rfl⟩
  | club => exact ⟨1, rfl⟩

private theorem vis0_wf_runs : ∀ a : Anchor, runOK (vis0.piles a).faceUp = true := by
  intro a
  cases a <;> rfl

private theorem vis0_wf_count : ∀ c ∈ Card.universe, vis0.cardCount c = 1 := by
  intro c _
  rcases c with ⟨s, r⟩
  cases s <;> cases r <;> decide

/-- The vis-board is `WF` (all four clauses, kernel-decided). -/
private theorem vis0_wf : vis0.WF :=
  ⟨vis0_wf_found, vis0_wf_runs, vis0_wf_count, by decide⟩

/-- **THE BASE IS STILL A GENUINE FORK** — the census folds the
{5♥, 5♦} pair verbatim: the mirrored spade column adds a face-up 4♠
that the seat bar silences (below empty, hidden deck, no king). -/
theorem vis0_fork : forkStateSB vis0 = true := by decide

theorem vis0_forkState : forkState vis0 := (forkStateSB_true_iff vis0_wf).mp vis0_fork

/-- The witness is the vanilla-live 5♥ (rfl-fold of the search). -/
theorem vis0_witness : forkWitnessSB vis0 = some H5 := by rfl

/-- **THE VIS-LEDGER**: the pair lives; the island's 3♣ dies by
rank-read (clubs at 1, its next-up is the stock-resident 2♣ — the
hypothesis's clause, verified); the hosted 4♠ residue-top dies at
the SEAT BAR (face-up, next-up, and still dead — the mirrored
column's own census row); the stock's 2♣ dead. -/
theorem vis0_ledger :
    canRaiseSB vis0 H5 = true ∧ canRaiseSB vis0 D5 = true ∧
      canRaiseSB vis0 C3 = false ∧ canRaiseSB vis0 S4 = false ∧
        canRaiseSB vis0 C2 = false :=
  ⟨by decide, by decide, by decide, by decide, by decide⟩

/-- **THE ORIGIN LOCK** — at the base fork the dresser has NO legal
top-target in the whole universe: its only fit seats (the under-seat
scan) are the red fours, and both sit foundation-resident at the
pair's own rungs (hearts 4, diamonds 4 — `founTop` read off
`rfl` below), so no pile tops one; the empty-anchor recourse is
king-only and the 3♣ is no king.  THE VISIBLE ISLAND IS UNBUILDABLE:
every legal under-seat is locked in a foundation, and the 3♣ is
forced bare over its hidden deck. -/
theorem vis0_lock :
    (∀ z ∈ Card.universe, vis0.canPlace C3 (Sum.inr z) = false) ∧
      (∀ a : Anchor, vis0.canPlace C3 (Sum.inl a) = false) ∧
        vis0.foundTop Suit.heart = some H4 ∧
          vis0.foundTop Suit.diamond = some D4 := by
  refine ⟨?_, ?_, rfl, rfl⟩
  · intro z _
    rcases z with ⟨s, r⟩
    cases s <;> cases r <;> decide
  · intro a
    cases a <;> decide

/-- The prescribed mirror, tried AT THE ORIGIN onto the hosted 4♠
residue-top: the step refuses (the fit kill made operational — the
4♠ tops a real face-up pile here, and still the match fails). -/
theorem vis0_mirrorTry :
    State.step vis0 (Move.tabToTab C3 (Sum.inr S4)) = none := by rfl

/-! ## §2. The walk

The licensed dilation, one `rfl` row per milestone: pull 4♥ off the
hearts foundation onto the 5♠ anchor (`vis1`, hearts → 3), pull 4♦
onto the 5♣ anchor (`vis2`, diamonds → 3), slide the island's 3♣
onto the landed 4♦ (`vis3`, the dressing: [6♦, 5♣, 4♦, 3♣]). -/

/-- `vis1`: the first pull — 4♥ onto the 5♠-anchor pile. -/
private def vis1 : State := stepD vis0 (Move.foundToTab H4 (Sum.inr S5))

/-- `vis2`: the second pull — 4♦ onto the 5♣-anchor pile. -/
private def vis2 : State := stepD vis1 (Move.foundToTab D4 (Sum.inr C5))

/-- `vis3`: the dressing — the island's 3♣ slid onto the landed 4♦. -/
private def vis3 : State := stepD vis2 (Move.tabToTab C3 (Sum.inr D4))

theorem vis1_step :
    State.step vis0 (Move.foundToTab H4 (Sum.inr S5)) = some vis1 := by rfl
theorem vis2_step :
    State.step vis1 (Move.foundToTab D4 (Sum.inr C5)) = some vis2 := by rfl
theorem vis3_step :
    State.step vis2 (Move.tabToTab C3 (Sum.inr D4)) = some vis3 := by rfl

private theorem vis1_wf_found : ∀ s : Suit, ∃ n, vis1.found s = s.upCards.take n := by
  intro s
  cases s with
  | spade => exact ⟨3, rfl⟩
  | heart => exact ⟨3, rfl⟩
  | diamond => exact ⟨4, rfl⟩
  | club => exact ⟨1, rfl⟩

private theorem vis1_wf_runs : ∀ a : Anchor, runOK (vis1.piles a).faceUp = true := by
  intro a
  cases a <;> rfl

private theorem vis1_wf_count : ∀ c ∈ Card.universe, vis1.cardCount c = 1 := by
  intro c _
  rcases c with ⟨s, r⟩
  cases s <;> cases r <;> decide

private theorem vis1_wf : vis1.WF :=
  ⟨vis1_wf_found, vis1_wf_runs, vis1_wf_count, by decide⟩

private theorem vis2_wf_found : ∀ s : Suit, ∃ n, vis2.found s = s.upCards.take n := by
  intro s
  cases s with
  | spade => exact ⟨3, rfl⟩
  | heart => exact ⟨3, rfl⟩
  | diamond => exact ⟨3, rfl⟩
  | club => exact ⟨1, rfl⟩

private theorem vis2_wf_runs : ∀ a : Anchor, runOK (vis2.piles a).faceUp = true := by
  intro a
  cases a <;> rfl

private theorem vis2_wf_count : ∀ c ∈ Card.universe, vis2.cardCount c = 1 := by
  intro c _
  rcases c with ⟨s, r⟩
  cases s <;> cases r <;> decide

private theorem vis2_wf : vis2.WF :=
  ⟨vis2_wf_found, vis2_wf_runs, vis2_wf_count, by decide⟩

private theorem vis3_wf_found : ∀ s : Suit, ∃ n, vis3.found s = s.upCards.take n := by
  intro s
  cases s with
  | spade => exact ⟨3, rfl⟩
  | heart => exact ⟨3, rfl⟩
  | diamond => exact ⟨3, rfl⟩
  | club => exact ⟨1, rfl⟩

private theorem vis3_wf_runs : ∀ a : Anchor, runOK (vis3.piles a).faceUp = true := by
  intro a
  cases a <;> rfl

private theorem vis3_wf_count : ∀ c ∈ Card.universe, vis3.cardCount c = 1 := by
  intro c _
  rcases c with ⟨s, r⟩
  cases s <;> cases r <;> decide

/-- The dressed endpoint is `WF` (all four clauses, kernel-decided). -/
private theorem vis3_wf : vis3.WF :=
  ⟨vis3_wf_found, vis3_wf_runs, vis3_wf_count, by decide⟩

/-- **MID-WALK 1, DEAD**: the pulled 4♥ and the witness-topped twin
5♦ both live (the twin's exit still rides 5♥'s standing top) — two
live cards, no pair. -/
theorem vis1_forkSB : forkStateSB vis1 = false := by decide

theorem vis1_live :
    canRaiseSB vis1 H4 = true ∧ canRaiseSB vis1 D5 = true :=
  ⟨by decide, by decide⟩

/-- **MID-WALK 2, DEAD — the orientation pin dies**: both pulled
fours top their anchors and are VANILLA-live — the census sees
{4♥, 4♦} but no witness. -/
theorem vis2_forkSB : forkStateSB vis2 = false := by decide

theorem vis2_pin :
    canRaiseB vis2 H4 = true ∧ canRaiseB vis2 D4 = true :=
  ⟨by decide, by decide⟩

/-! ## §3. THE MIRROR ROW — the hypothesis's move, tried and refused

The whole point of the visible island was the one-move mirror
`Move.tabToTab C3 (Sum.inr S4)`: the dressing's departure leaves the
4♠ topping its residue, and the returning dresser slides back onto
it.  The fit kill makes the mirror a dead move AT EVERY BOARD: at
`vis3` the 4♠ really is a live face-up pile top — the mirrored spade
column hosted it exactly as asked — and the step still refuses,
because the color bar does not know about hospitality.  The full
landing lattice then decides what IS open: the escape hop onto the
witness's top 4♥ — which lands ELSEWHERE — and nothing else. -/

/-- The hold-and-read shape at the dressed board: the reveal exposed
7♣ as the island's top (the incoming mirror's would-be home), and
the sandwich stands [6♦, 5♣, 4♦, 3♣]. -/
theorem vis3_island :
    (vis3.piles .p1).faceUp = [C7] ∧
      (vis3.piles .p4).faceUp = [D6, C5, D4, C3] :=
  ⟨rfl, rfl⟩

/-- **THE PRESCRIBED MIRROR, REFUSED AT THE LANDING** — the 4♠
residue-top is on-board, face-up, and hosting-ready at `vis3`, and
the step is `none` anyway: `canPlace C3 (Sum.inr S4)` reads the
hosted top and fails the color bar. -/
theorem vis3_mirror_none :
    State.step vis3 (Move.tabToTab C3 (Sum.inr S4)) = none := by rfl

/-- **ONE-WAY DOOR, BOTH BARS DECIDED**: the 3♣'s complete landing
lattice at the dressed board — over the whole universe, its ONLY
top-fit landing is the escape hop 4♥ (which lands on the other
anchor's pile — no return); the empty-anchor recourse is king-only;
the found-route is dead by the rank-lock. -/
theorem vis_mirrorDead :
    (∀ z ∈ Card.universe, vis3.canPlace C3 (Sum.inr z) = decide (z = H4)) ∧
      (∀ a : Anchor, vis3.canPlace C3 (Sum.inl a) = false) ∧
        vis3.nextUp C3 = false := by
  refine ⟨?_, ?_, by decide⟩
  · intro z _
    rcases z with ⟨s, r⟩
    cases s <;> cases r <;> decide
  · intro a
    cases a <;> decide

/-- The escape hop: the lone legal landing, played — the 3♣ runs
onto the witness's top 4♥ at the other anchor. -/
private def vis3hop : State := stepD vis3 (Move.tabToTab C3 (Sum.inr H4))

theorem vis3hop_step :
    State.step vis3 (Move.tabToTab C3 (Sum.inr H4)) = some vis3hop := by rfl

/-- **THE ESCAPE HOP LANDS ELSEWHERE**: the only legal landing
changes the other anchor's pile, not the island — the dressed 3♣
cannot go home, decided against `vis2`'s island pile. -/
theorem vis3hop_elsewhere :
    vis3hop.piles Anchor.p1 ≠ vis2.piles Anchor.p1 := by decide

/-- **THE DRESSING SLIDE IS A COMMITMENT** — theorem-grade: the
departure from the hidden island is a REVEALING slide (the whole run
leaves the pile, the hidden deck under it loses a card for good —
the banked monotone-table jury `journey_tabToTab_never_reveal`).
The fit audit and the origin lock show this reveal was FORCED: no
legal face-up under-seat exists for the 3♣ on this economy, so the
visible island — the reveal's only alternative — is unbuildable. -/
theorem vis_slide_irr :
    ¬ reversibleAtW vis2 (Move.tabToTab C3 (Sum.inr D4)) :=
  journey_tabToTab_never_reveal vis3_step
    (show vis2.pileHolding C3 = some Anchor.p1 from by rfl)
    (show below C3 (vis2.piles Anchor.p1).faceUp = [] from by rfl)
    (show (vis2.piles Anchor.p1).hidden ≠ [] from by decide)

/-! ## §4. The reversible dilation, and where the class stops

The two pulls are reversible (each one-move mirror is a licensed
re-found at the landing), so `vis0` and `vis2` are macro-class mates
through the two-leg witness shuffles — and the class's pulled end is
FORKLESS (`vis2_forkSB`) with the dressing leg the audited door. -/

/-- The licensed mirror: the pulled 4♥ re-founds from its landed top. -/
private theorem vis1_mirror :
    State.step vis1 (Move.tabToFound H4) = some vis0 := by
  have hstep : State.step vis1 (Move.tabToFound H4) =
      some (stepD vis1 (Move.tabToFound H4)) := by rfl
  have hxEq : stepD vis1 (Move.tabToFound H4) = vis0 := by
    refine State.ext (funext fun σ => ?_) (funext fun a => ?_) ?_ ?_ ?_
    · cases σ <;> rfl
    · cases a <;> rfl
    · rfl
    · rfl
    · rfl
  rw [hstep, hxEq]

/-- The licensed mirror: the pulled 4♦ re-founds from its landed
top, back to the first-pull position. -/
private theorem vis2_mirror :
    State.step vis2 (Move.tabToFound D4) = some vis1 := by
  have hstep : State.step vis2 (Move.tabToFound D4) =
      some (stepD vis2 (Move.tabToFound D4)) := by rfl
  have hxEq : stepD vis2 (Move.tabToFound D4) = vis1 := by
    refine State.ext (funext fun σ => ?_) (funext fun a => ?_) ?_ ?_ ?_
    · cases σ <;> rfl
    · cases a <;> rfl
    · rfl
    · rfl
    · rfl
  rw [hstep, hxEq]

/-- Each pull leg is reversible by its one-move mirror. -/
private theorem revPullA :
    reversibleAtW vis0 (Move.foundToTab H4 (Sum.inr S5)) :=
  ⟨vis1, [Move.tabToFound H4], vis1_step, run_one vis1_mirror⟩

private theorem revPullB :
    reversibleAtW vis1 (Move.foundToTab D4 (Sum.inr C5)) :=
  ⟨vis2, [Move.tabToFound D4], vis2_step, run_one vis2_mirror⟩

/-- Each re-found leg is reversible the other way, by its pull. -/
private theorem revFoundB :
    reversibleAtW vis2 (Move.tabToFound D4) :=
  ⟨vis1, [Move.foundToTab D4 (Sum.inr C5)], vis2_mirror, run_one vis2_step⟩

private theorem revFoundA :
    reversibleAtW vis1 (Move.tabToFound H4) :=
  ⟨vis0, [Move.foundToTab H4 (Sum.inr S5)], vis1_mirror, run_one vis1_step⟩

/-- The forward witness shuffle: `vis0 → vis2` through the pulls. -/
private theorem visFwd : ShufflePlayW vis0
    [Move.foundToTab H4 (Sum.inr S5), Move.foundToTab D4 (Sum.inr C5)] vis2 :=
  .cons revPullA vis1_step (.cons revPullB vis2_step (.nil vis2))

/-- The backward witness shuffle: `vis2 → vis0` through the
licensed re-founds. -/
private theorem visBwd : ShufflePlayW vis2 [Move.tabToFound D4, Move.tabToFound H4] vis0 :=
  .cons revFoundB vis2_mirror (.cons revFoundA vis1_mirror (.nil vis0))

/-- **THE REVERSIBLE DILATION IS CERTIFIED** — `vis0` and `vis2` are
macro-class mates through the fully-audited two-leg pull journey. -/
theorem vis_classPulls : sameOrbitSetoid.r vis0 vis2 :=
  ⟨[Move.tabToFound D4, Move.tabToFound H4], visBwd,
    [Move.foundToTab H4 (Sum.inr S5), Move.foundToTab D4 (Sum.inr C5)], visFwd⟩

/-! ## §5. THE VERDICT ROWS

The census at the dressed board folds the {4♥, 4♦} pair — the
rank-4 fork lands with witness 4♥, one rank below the base's 5♥, on
the same dealt economy — and the connection ledger prices the class:
the reversible dilation reaches only the FORKLESS `vis2`, the
dressing leg is the audited commitment, and the hypothesis's own
mirror move is a decided `none`.  The sixth landing is REFUSED —
the two different-rank forks cannot be banked in ONE reversible
class — the no-lock pairClass theorem SURVIVES. -/

/-- **THE VERDICT CENSUS: TRUE** — after the dressing slide the
census folds the {4♥, 4♦} pair: the pulled four tops the spade anchor
(vanilla-live), the OTHER pulled four sits COVERED under the
rank-locked black-3 (S-live through the twin's topping,
vanilla-dead) — a genuine rank-4 fork on the mirrored economy. -/
theorem vis3_forkSB : forkStateSB vis3 = true := by decide

/-- **THE WITNESS NAMED**: the SB search folds to the pulled 4♥
(rank 4 — the epoch's downward pair). -/
theorem vis3_witness : forkWitnessSB vis3 = some H4 := by rfl

/-- **BANKED: the rank-4 fork**, predicate grade, bridge-lifted. -/
theorem vis_fork : forkState vis3 := (forkStateSB_true_iff vis3_wf).mp vis3_forkSB

/-- The pair pins at the epoch's both ends: the rank-5 pair sits at
its rungs at `vis0`, the rank-4 pair at `vis3`. -/
theorem vis_pins :
    rungAt vis0 Suit.heart = H5.rank.toIdx ∧
      rungAt vis0 Suit.diamond = H5.rank.toIdx ∧
        rungAt vis3 Suit.heart = H4.rank.toIdx ∧
          rungAt vis3 Suit.diamond = H4.rank.toIdx :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- **THE DRESSED LEDGER**: exactly the pair lives — witness 4♥
vanilla-live; the covered 4♦ S-live but VANILLA-DEAD (the pin
restored by the dressing); the dressed 3♣ dead by the club
rank-lock; the OLD pair dead at the dropped rungs; the hosted 4♠
residue-top still seat-barred; the stock resident dead. -/
theorem vis3_ledger :
    canRaiseSB vis3 H4 = true ∧ canRaiseSB vis3 D4 = true ∧
      canRaiseB vis3 D4 = false ∧
        canRaiseSB vis3 C3 = false ∧
          canRaiseSB vis3 S4 = false ∧
            canRaiseSB vis3 H5 = false ∧ canRaiseSB vis3 D5 = false ∧
              canRaiseSB vis3 C2 = false :=
  ⟨by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide⟩

/-- **THE DOWN-PAIR LEDGER** — decide-grade: two forkStates of
different pair ranks on the one mirrored economy, the reversible
class between them ENDING FORKLESS at `vis2`, and the dressing leg a
one-way door whose own prescribed mirror — the black-4 residue — is
a decided `none` at the landing: the no-lock pairClass theorem's
visible-island counterexample FAILS to be same-class — the theorem
survives this probe. -/
theorem vis_pair :
    forkState vis0 ∧ forkState vis3 ∧
      forkWitnessSB vis0 = some H5 ∧ forkWitnessSB vis3 = some H4 ∧
        H4.rank.toIdx + 1 = H5.rank.toIdx ∧
          forkStateSB vis2 = false ∧
            sameOrbitSetoid.r vis0 vis2 ∧
              ¬ reversibleAtW vis2 (Move.tabToTab C3 (Sum.inr D4)) ∧
                State.step vis3 (Move.tabToTab C3 (Sum.inr S4)) = none :=
  ⟨vis0_forkState, vis_fork, vis0_witness, vis3_witness,
    by decide, vis2_forkSB, vis_classPulls, vis_slide_irr, vis3_mirror_none⟩

/-- **THE CONNECTION VERDICT** (`vis_class`): what the vis probe's
same-class story earns — the pulls are reversible class legs, the
dressing is not, the rank-4 fork lives outside the certified class
with its only landing decided ELSEWHERE than home. -/
theorem vis_class :
    sameOrbitSetoid.r vis0 vis2 ∧
      ¬ reversibleAtW vis2 (Move.tabToTab C3 (Sum.inr D4)) ∧
        vis3.canPlace C3 (Sum.inr S4) = false ∧
          vis3hop.piles Anchor.p1 ≠ vis2.piles Anchor.p1 :=
  ⟨vis_classPulls, vis_slide_irr, by decide, vis3hop_elsewhere⟩

/-! ## §6. The census summary — one theorem per verdict, pure decides -/

theorem EpochProbeVis_vis0 : forkStateSB vis0 = true := vis0_fork
theorem EpochProbeVis_vis1 : forkStateSB vis1 = false := vis1_forkSB
theorem EpochProbeVis_vis2 : forkStateSB vis2 = false := vis2_forkSB
theorem EpochProbeVis_vis3 : forkStateSB vis3 = true := vis3_forkSB

/-- **THE PROBE LEDGER**: the full visible-island verdict in one
breath — the residue unfit, the two different-rank forks banked
(witnesses 5♥ and 4♥), the hypothesis's mirror move a decided
`none`, the only legal landing the escape hop, and the reversible
class ending FORKLESS at `vis2`: the structural door stands shut,
mirroring the committed EpochProbe `down_pair` row (its boards are
private to its file; this row is its twin, on this probe's boards). -/
theorem EpochProbeVis_verdicts :
    canSitOn C3 S4 = false ∧ runOK [S4, C3] = false ∧
      forkWitnessSB vis0 = some H5 ∧ forkWitnessSB vis3 = some H4 ∧
        H4.rank.toIdx + 1 = H5.rank.toIdx ∧
          State.step vis3 (Move.tabToTab C3 (Sum.inr S4)) = none ∧
            (∀ z ∈ Card.universe, vis3.canPlace C3 (Sum.inr z) = decide (z = H4)) ∧
              sameOrbitSetoid.r vis0 vis2 ∧
                forkStateSB vis2 = false :=
  ⟨vis_blackResidueUnfit.1, vis_blackResidueUnfit.2,
    vis0_witness, vis3_witness, by decide, vis3_mirror_none,
    vis_mirrorDead.1, vis_classPulls, vis2_forkSB⟩

/-! ### The audit battery

Fresh heads `#print axioms`-audited — every row lands in the allowed
grades: the decide rows at `[propext]`, the table-jury
irreversibility and the bridge-lifted class rows at
`[propext, Quot.sound]` — zero `Classical.choice`, zero sorry. -/

#print axioms vis_blackResidueUnfit
#print axioms vis_seats
#print axioms vis_over
#print axioms vis0_fork
#print axioms vis0_witness
#print axioms vis0_ledger
#print axioms vis0_lock
#print axioms vis0_mirrorTry
#print axioms vis1_forkSB
#print axioms vis2_forkSB
#print axioms vis3_mirror_none
#print axioms vis_mirrorDead
#print axioms vis3hop_step
#print axioms vis3hop_elsewhere
#print axioms vis_slide_irr
#print axioms vis_classPulls
#print axioms vis3_forkSB
#print axioms vis3_witness
#print axioms vis_fork
#print axioms vis_pins
#print axioms vis3_ledger
#print axioms vis_pair
#print axioms vis_class
#print axioms EpochProbeVis_verdicts
