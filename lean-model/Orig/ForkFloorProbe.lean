import Orig.ForkStateSB
import Orig.Phase
import Orig.LowSlab

/-!
# Orig.ForkFloorProbe — THE SINGLE-FAMILY-FRAGILE PROBE BOARDS

Round 3 of the refuter-first program, aimed at
`Orig/ForkFloor.lean`'s main row `fork_floor_of_commit`: the
FALSIFICATION SHAPE, as the main row's own docstring records it — a
single-family-fragile economy (exactly one viable frontier pair,
everything else entombed) where the commit EATS the sole pair member
while its takeback seat is permanently seat-less, so that the
successor forks nowhere in reach.

Three hand-built boards, one per mission cell, every verdict
decide- or kernel-grade:

* **§1 FRAGILE-1 (`fb1`) — the minimal single-family economy with an
  eating commit.**  Cells for ONE frontier pair ({4♥, 4♦}, rungs ♥ 3 /
  ♦ 3) plus the eat cell: a bare hot `S4` over an empty deck at p3
  (rungs ♠ 3 / ♣ 0), the pristine one-card stock.  VERDICT:
  **DOWNWARD-FORK-SURVIVES, DISTANCE 0** — the committed bare lift
  (`tabToFound S4`, graded by the census's own bare-non-king pin
  `bare_lift_irreversibleAt`) leaves the pair census UNTOUCHED: the
  successor `fb1S` is ITSELF a decided fork (witness `4♥`), so the
  exhibit fork run is EMPTY.  The armor datum this board lives for:
  **the eat cell was never pair content** — the seat clause of the
  S-license (`below ≠ []`, or bare over an EMPTY deck at a KING)
  bars bare residency from S-liveness outright, so a bare-over-empty
  non-king hot card cannot participate in ANY fork: the census
  decides it dead next to its own founding.  The takeback-seal
  datapoint beside it: the eater's own return seats are REFUSED —
  no black five tops any pile at `fb1S` (`C5` sits mid-tower, `S5`
  sits under the live member), so the eaten seal really is
  irrevocable — and the floor does not care: the surviving fork
  never rode the eaten cell.
* **§2 FRAGILE-2 (`fb2`) — the corridor economy with the takeback
  seat and the waste-locked surroundings.**  The sole pair {4♥, 4♦}
  again, but now the LIVE member rides the WASTE HEAD (`[4♥, 4♠,
  4♣]` over an empty stock); the seat host `S5` tops its own pile;
  the twin towers as ever.  The origin `fb2` is itself FORKLESS
  (decided — waste residency is S-death), the corridor to the fork
  is ONE move (`wasteToTab 4♥ (inr S5)`), and the mission's eating
  commit is the other waste letter on the same head:
  `wasteToFound 4♥` — a full commitment (the `cycleCount` monotone).
  VERDICT: **DOWNWARD-FORK-SURVIVES, DISTANCE 1** — the founded
  member sits at its foundation top with its takeback seat host
  STILL TOPPING the same pile (the waste letter writes no tableau
  cell — `two_zone_exits_playable`'s own prong, consumed here), so
  the one-move pull `foundToTab 4♥ (inr S5)` re-seats it and lands
  THE CORRIDOR STATE EXACTLY (`fb2R = fb2F`, a `State.ext`
  collapse): the defusing-schedule repair is ONE LEG, the fork
  certificate decided at the landing.  The surrounding cells
  (`4♠`, `4♣`) are waste-locked: decided S-dead AND vanilla-dead,
  and their only conceivable seatings refuse on color.  The
  committed successor EXITS the origin's macro class
  (`commit_exits_class`, consumed on-board) — the floor repairs
  one door outside the class anyway.
* **§3 FRAGILE-3 (`fb3`) — the hidden-buried opposing lows, with
  the committed reveal channel that surfaces one.**  The §2 spine,
  plus the low cells: the heart low `5♥` buried at the HEAD of p3's
  hidden deck under a bare `S6`; a frozen host `D7` topping p4,
  with the diamond low `5♦` entombed in p4's hidden deck forever
  (the host is immovable: no black eight exists to carry it).  The
  eat is §2's again; the verdict is §2's again (SURVIVES, DISTANCE
  1).  THIS board's own beat is the irreversibility of the
  surfaced low, end to end: from the post-eat state the committed
  reveal-slide `tabToTab S6 (inr D7)` fires (jury-barred,
  `journey_tabToTab_never_reveal`; monotone-graded), the low `5♥`
  surfaces HOT (hearts at 4) — **and stays forkless on three
  decided grounds**: (i) bare-over-hidden residency fails the same
  seat clause (`canRaiseSB` dead at the surfacing state); (ii) even
  after it seats itself onto the frozen host's new top (`5♥` onto
  `6♠`, the only landing the surfacing opened), its TWIN `5♦`
  remains entombed behind a frozen host — no black eight anywhere,
  so the deck never reveals again — and a live member with a dead
  twin saturates no pair (`forkStateSB` decided false at the seated
  state); (iii) every deeper head the reveal cascade surfaces is
  rank-cold by construction.  The opposing lows cannot surface into
  corridor content — reversibly or irreversibly.

THE ARMOR LIST (what the three boards jointly witness):

* A1 (§1): the seat clause BARS bare residency from pair content —
  the natural eating commits at minimality eat OUT-of-pair cells.
* A2 (§2): every eat of a member over its seat leaves the SEAT
  HOST topping the same pile (no letter writes the tableau except
  the tableau letters, and those keep the below-card exposed), so
  the member's one-move pull-back re-opens the corridor: THE
  DEFUSING-SCHEDULE REPAIR IS ONE LEG, attained.
* A3 (§2): the waste junk cells are locked by rank-coldness plus
  the color bar on their lone seat — no black five tops anything.
* A4 (§3): surfacing lows — even irreversibly, via committed
  reveals — inherit the same seat clause on the bare side, and the
  frozen hosts bar their twins from ever surfacing in turn; the
  pair saturation stays unreachable.

HUNTING-FLOOR HONESTY (the finite-economy caveat, stated as such):
a probe board can witness SURVIVES by exhibiting a fork run (done
three times above, one of them trivially at the successor itself),
and it can witness the ARMOR MECHANISMS at the exhibited states; a
genuine floor break would need forklessness at EVERY state
reachable from the successor — on these economies the reachable
sets stay forkless-or-repaired along the exhibited cascades, but
the universes of plays are not exhausted by hand.  What the boards
DO close at theorem grade is the mission's specific target shape:
given the premise pair (a fork reachable from `s`, a committed
eaten member-at-its-head), each probed eating geometry fails to
kill the floor for a NAMED structural reason (the seat clause, the
seat-host immortality through the eat, the frozen host), not by
accident of the deal.

DISPOSITION FOR THE INTEGRATOR: the main row
`fork_floor_of_commit` SURVIVES all three probed shapes, the
irrevocable-eaten-seal disjunct is NOT drafted (no probed board
forces it — the eaten seals observed were real yet never carried
the corridor).  The surviving honest danger is the MULTI-COMMIT
schedule (a corridor needing repairs beyond one leg, or eats
landing at states this file's snapshots do not cover) — that is
the defusing-schedule repair time bound, the named residue
`fork_floor_of_commit`'s routes already carry.

House compliance: additive probe leaf (`import Orig.ForkStateSB`,
`import Orig.Phase`, `import Orig.LowSlab`, the same import set as
the sibling probe leaves use, pending the orchestrator's olean
build of `Orig.ForkFloor` for direct import; the one step-arm
consumption below is the per-file private copy of
`Orig/ForkFloor.lean`'s PROVED `two_zone_exits_playable` prong —
probed first here, consumed by name there); decide/kernel grade
only, ZERO SORRY; per-file private kit; BOLD-named docstrings with
verdicts; `#print axioms` battery for every fresh head; zero
`Classical.choice` (the step rows are kernel folds and dec
instances); no other file touched (`Orig/LowSlabProbe.lean`'s
boards are its own; every board here is fresh-built). -/

/-! ## §0. The private kit -/

private def crd (s : Suit) (r : Rank) : Card := ⟨s, r⟩

private def stepD (st : State) (m : Move) : State :=
  match st.step m with
  | none => st
  | some s' => s'

private def H4 : Card := crd .heart .four
private def H5 : Card := crd .heart .five
private def D4 : Card := crd .diamond .four
private def D5 : Card := crd .diamond .five
private def D7 : Card := crd .diamond .seven
private def S3 : Card := crd .spade .three
private def S4 : Card := crd .spade .four
private def S5 : Card := crd .spade .five
private def S6 : Card := crd .spade .six
private def C3 : Card := crd .club .three
private def C4 : Card := crd .club .four
private def C5 : Card := crd .club .five

/-- The waste-founding seat row, as the probe's private kit copy:
the founding exit lands its card at the FOUNDATION TOP and writes
NO tableau cell — the same step-arm prong `Orig/ForkFloor.lean`'s
`two_zone_exits_playable` proves (first consumption there); the
copy rides the per-file private-kit discipline, pending the
orchestrator's olean build of `Orig.ForkFloor` for direct import. -/
private theorem p_wasteFound_seats {s s' : State} {c : Card}
    (hstep : State.step s (Move.wasteToFound c) = some s') :
    s'.foundTop c.suit = some c ∧ s'.piles = s.piles := by
  obtain ⟨-, x, xs, -, hs⟩ := step_wasteToFound_inv hstep
  refine ⟨?_, ?_⟩
  · rw [hs]
    show lastOf ((s.setFound c.suit (s.found c.suit ++ [c])).found c.suit) = some c
    rw [setFound_found_self]
    exact lastOf_snoc
  · rw [hs]
    show (s.setFound c.suit (s.found c.suit ++ [c])).piles = s.piles
    exact setFound_piles s c.suit _
/-- The survives exhibit, packaged in the main row's conclusion
shape (the probe verdict form). -/
private theorem surviveEx (s' : State) (F' : State) (π' : List Move) (x' : Card)
    (hrun : s'.run π' = some F') (hwit : ForkWitness F' x') :
    ∃ (F : State) (π : List Move) (x : Card),
      s'.run π = some F ∧ ForkWitness F x := ⟨F', π', x', hrun, hwit⟩

/-! ## §1. FRAGILE-1: the minimal single-family economy with an
eating commit (`fb1`)

Rungs ♥ 3 / ♦ 3 / ♠ 3 / ♣ 0.  p1 hosts the twin tower `[C5, D4, C3]`
over the eleven-card club deck; p2 hosts the live member `[S5, H4]`;
p3 hosts the EAT CELL: the bare hot `S4` over an empty deck; p4/p5/p6
entomb the rest of the blacks and reds; the stock carries `H5` over
an empty waste (pristine).  The sole viable frontier pair is
{H4, D4}; the eating commit is the bare lift of `S4`. -/

private def hmap1 : Suit → Nat
  | .heart => 3 | .diamond => 3 | .spade => 3 | .club => 0

private def fb1 : State where
  found := fun s => s.upCards.take (hmap1 s)
  piles := fun a => match a with
    | .p0 => ⟨[], []⟩
    | .p1 => ⟨[crd .club .six, crd .club .seven, crd .club .eight,
               crd .club .nine, crd .club .ten, crd .club .jack,
               crd .club .queen, crd .club .king, crd .club .ace,
               crd .club .two, crd .club .four],
              [C5, D4, C3]⟩
    | .p2 => ⟨[], [S5, H4]⟩
    | .p3 => ⟨[], [S4]⟩
    | .p4 => ⟨[crd .spade .six, crd .spade .seven, crd .spade .eight,
               crd .spade .nine, crd .spade .ten, crd .spade .jack,
               crd .spade .queen, crd .spade .king], []⟩
    | .p5 => ⟨[crd .heart .six, crd .heart .seven, crd .heart .eight,
               crd .heart .nine, crd .heart .ten, crd .heart .jack,
               crd .heart .queen, crd .heart .king], []⟩
    | .p6 => ⟨[crd .diamond .five, crd .diamond .six, crd .diamond .seven,
               crd .diamond .eight, crd .diamond .nine, crd .diamond .ten,
               crd .diamond .jack, crd .diamond .queen, crd .diamond .king],
              []⟩
  stock := [H5]
  waste := []
  drawStep := 1

private theorem fb1_wf_found : ∀ s : Suit, ∃ n, fb1.found s = s.upCards.take n := by
  intro s
  cases s with
  | spade => exact ⟨3, rfl⟩
  | heart => exact ⟨3, rfl⟩
  | diamond => exact ⟨3, rfl⟩
  | club => exact ⟨0, rfl⟩

private theorem fb1_wf_runs : ∀ a : Anchor, runOK (fb1.piles a).faceUp = true := by
  intro a
  cases a <;> rfl

private theorem fb1_wf_count : ∀ c ∈ Card.universe, fb1.cardCount c = 1 := by
  intro c _
  rcases c with ⟨s, r⟩
  cases s <;> cases r <;> decide

private theorem fb1_wf : fb1.WF :=
  ⟨fb1_wf_found, fb1_wf_runs, fb1_wf_count, by decide⟩

/-- **§1 PREMISE: the base is a fork of the sole viable pair**
(universe-decided; `S4` itself — hot, bare — reads S-DEAD in the
same census: the eat cell is NOT pair content). -/
theorem fb1_forkSB : forkStateSB fb1 = true := by decide

theorem fb1_witness : forkWitnessSB fb1 = some H4 := by rfl

theorem fb1_forkWitness : ForkWitness fb1 H4 :=
  forkWitnessSB_sound fb1_wf fb1_witness

/-- **§1 THE EAT: the bare lift of the hot `S4`** — committed by the
census's own bare-non-king pin. -/
private def fb1S : State := stepD fb1 (Move.tabToFound S4)

theorem fb1_eat : State.step fb1 (Move.tabToFound S4) = some fb1S := by rfl

theorem fb1_eatCommit : irreversibleAt fb1 (Move.tabToFound S4) :=
  bare_lift_irreversibleAt fb1_eat
    (show fb1.pileOfTop S4 = some Anchor.p3 from rfl)
    (show chop (fb1.piles Anchor.p3).faceUp = [] from rfl)
    (show (fb1.piles Anchor.p3).hidden = [] from rfl)
    (by decide)

/-- **§1 THE EATEN SEAL, WITNESSED**: the eaten card's own return
seats refuse — the empty-anchor landing demands a king, and the only
conceivable card-host (a black five) tops nothing at the successor
(`C5` sits mid-tower, `S5` under the live member).  The seal is
irrevocable; the verdict shows the floor never needed the cell. -/
theorem fb1S_sealRefused :
    State.step fb1S (Move.foundToTab S4 (Sum.inl Anchor.p3)) = none ∧
      State.step fb1S (Move.foundToTab S4 (Sum.inr S5)) = none :=
  ⟨rfl, rfl⟩

/-- **§1 VERDICT: DOWNWARD-FORK-SURVIVES, DISTANCE 0** — the
committed eat cannot dent the pair census: the successor is itself
a decided fork with witness `H4`, so the exhibit run is EMPTY
(`fb1`'s own fork premise rides the trivial journey). -/
theorem fb1S_forkSB : forkStateSB fb1S = true := by decide

theorem fb1S_witness : forkWitnessSB fb1S = some H4 := by decide

theorem fb1S_forkWitness : ForkWitness fb1S H4 :=
  forkWitnessSB_sound (step_wf fb1_wf fb1_eat) fb1S_witness

theorem fb1_survives :
    ∃ (F : State) (π : List Move) (x : Card),
      fb1S.run π = some F ∧ ForkWitness F x :=
  surviveEx fb1S fb1S [] H4 rfl fb1S_forkWitness

/-! ## §2. FRAGILE-2: the corridor economy with the takeback seat
(`fb2`)

Rungs ♥ 3 / ♦ 3 / ♠ 0 / ♣ 0.  The twin tower `[C5, D4, S3]` as ever;
p2 hosts the bare SEAT HOST `[S5]`; the cycle zone carries the live
member at the WASTE HEAD over the locked junk `[4♠, 4♣]`, over an
EMPTY stock.  The origin is itself forkless (decided); the corridor
to the fork is the waste seating of `4♥` onto `S5`; the mission's
eating commit is the other waste letter at the same head. -/

private def hmap2 : Suit → Nat
  | .heart => 3 | .diamond => 3 | .spade => 0 | .club => 0

private def fb2 : State where
  found := fun s => s.upCards.take (hmap2 s)
  piles := fun a => match a with
    | .p0 => ⟨[], []⟩
    | .p1 => ⟨[crd .club .two, crd .club .three, crd .club .six,
               crd .club .seven, crd .club .eight, crd .club .nine,
               crd .club .ten, crd .club .jack, crd .club .queen,
               crd .club .king, crd .club .ace],
              [C5, D4, S3]⟩
    | .p2 => ⟨[], [S5]⟩
    | .p3 => ⟨[], []⟩
    | .p4 => ⟨[crd .spade .ace, crd .spade .two, crd .spade .six,
               crd .spade .seven, crd .spade .eight, crd .spade .nine,
               crd .spade .ten, crd .spade .jack, crd .spade .queen,
               crd .spade .king], []⟩
    | .p5 => ⟨[crd .heart .five, crd .heart .six, crd .heart .seven,
               crd .heart .eight, crd .heart .nine, crd .heart .ten,
               crd .heart .jack, crd .heart .queen, crd .heart .king],
              []⟩
    | .p6 => ⟨[crd .diamond .five, crd .diamond .six, crd .diamond .seven,
               crd .diamond .eight, crd .diamond .nine, crd .diamond .ten,
               crd .diamond .jack, crd .diamond .queen, crd .diamond .king],
              []⟩
  stock := []
  waste := [H4, S4, C4]
  drawStep := 1

private theorem fb2_wf_found : ∀ s : Suit, ∃ n, fb2.found s = s.upCards.take n := by
  intro s
  cases s with
  | spade => exact ⟨0, rfl⟩
  | heart => exact ⟨3, rfl⟩
  | diamond => exact ⟨3, rfl⟩
  | club => exact ⟨0, rfl⟩

private theorem fb2_wf_runs : ∀ a : Anchor, runOK (fb2.piles a).faceUp = true := by
  intro a
  cases a <;> rfl

private theorem fb2_wf_count : ∀ c ∈ Card.universe, fb2.cardCount c = 1 := by
  intro c _
  rcases c with ⟨s, r⟩
  cases s <;> cases r <;> decide

private theorem fb2_wf : fb2.WF :=
  ⟨fb2_wf_found, fb2_wf_runs, fb2_wf_count, by decide⟩

/-- **§2 THE QUIET ORIGIN**: waste residency is S-death — the origin
is FORKLESS (decided); the mission's premise rides the corridor
below, not the origin. -/
theorem fb2_notFork : forkStateSB fb2 = false := by decide

/-- **§2 THE CORRIDOR**: one move seats the waste-headed member onto
its host — a fork, decided at the landing. -/
private def fb2F : State := stepD fb2 (Move.wasteToTab H4 (Sum.inr S5))

theorem fb2_corridor : State.step fb2 (Move.wasteToTab H4 (Sum.inr S5)) = some fb2F := by
  rfl

theorem fb2F_forkSB : forkStateSB fb2F = true := by decide

theorem fb2F_witness : forkWitnessSB fb2F = some H4 := by decide

theorem fb2F_forkWitness : ForkWitness fb2F H4 :=
  forkWitnessSB_sound (step_wf fb2_wf fb2_corridor) fb2F_witness

/-- **§2 PREMISE (the floor row's `hhed`)**: a fork is reachable
from the quiet origin, one leg down the corridor. -/
theorem fb2_hhed :
    ∃ (F : State) (π : List Move) (x : Card),
      fb2.run π = some F ∧ ForkWitness F x :=
  surviveEx fb2 fb2F [Move.wasteToTab H4 (Sum.inr S5)] H4
    (run_one fb2_corridor) fb2F_forkWitness

/-- **§2 THE EAT: the waste founding of the member at its head** —
the other waste letter on the same card, a full commitment (the
cycle count strictly drops and never rises). -/
private def fb2E : State := stepD fb2 (Move.wasteToFound H4)

theorem fb2_eat : State.step fb2 (Move.wasteToFound H4) = some fb2E := by rfl

theorem fb2_eatCommit : irreversibleAt fb2 (Move.wasteToFound H4) :=
  irr_of_desc cycleCount (fun s m s' h => cycleCount_step h) fb2_eat
    (by have := cycleCount_step_wasteToFound fb2_eat; omega)

/-- **§2 THE DANGER, WITNESSED**: the eat really killed the pair
census — hearts founded past the fork point, the member gone: the
post-eat state is forkless (decided). -/
theorem fb2E_notFork : forkStateSB fb2E = false := by decide

/-- **§2 THE SEAT-HOST IMMORTALITY** (the private kit copy of
`Orig/ForkFloor.lean`'s `two_zone_exits_playable` prong, proved
there): the founding exit landed the member at its FOUNDATION TOP
and wrote NO tableau cell.  The takeback seat host `S5` still tops
the very pile the corridor consults. -/
theorem fb2_seatsSurvive :
    fb2E.foundTop H4.suit = some H4 ∧ fb2E.piles = fb2.piles :=
  p_wasteFound_seats fb2_eat

/-- **§2 THE REPAIR, ONE LEG**: the pull-back re-seats the member
onto its untouched host, and lands THE CORRIDOR STATE EXACTLY
(`fb2R = fb2F`, the component collapse below) — the
defusing-schedule repair at distance one. -/
private def fb2R : State := stepD fb2E (Move.foundToTab H4 (Sum.inr S5))

theorem fb2_repair : State.step fb2E (Move.foundToTab H4 (Sum.inr S5)) = some fb2R := by
  rfl

theorem fb2R_eq : fb2R = fb2F := by
  refine State.ext (funext fun σ => ?_) (funext fun a => ?_) ?_ ?_ ?_
  · cases σ <;> rfl
  · cases a <;> rfl
  · rfl
  · rfl
  · rfl

/-- **§2 VERDICT: DOWNWARD-FORK-SURVIVES, DISTANCE 1** — the one-leg
pull lands the corridor state; the fork certificate decided there. -/
theorem fb2_survives :
    ∃ (F : State) (π : List Move) (x : Card),
      fb2E.run π = some F ∧ ForkWitness F x :=
  surviveEx fb2E fb2R [Move.foundToTab H4 (Sum.inr S5)] H4
    (run_one fb2_repair)
    (by rw [fb2R_eq]; exact fb2F_forkWitness)

/-- **§2 THE LOCKED SURROUNDINGS**: the junk cells are rank-cold
AND vanilla-dead at every reading — waste-locked by the rungs. -/
theorem fb2_junkCold :
    canRaiseSB fb2 S4 = false ∧ canRaiseSB fb2 C4 = false ∧
      canRaiseB fb2 S4 = false ∧ canRaiseB fb2 C4 = false := by decide

/-- **§2 THE CLASS EXIT** (the consumed neighbor-program row): the
committed eat left the origin's macro class outright — the floor
repaired one door outside the class anyway. -/
theorem fb2_classExit : ¬ sameOrbitSetoid.r fb2 fb2E :=
  commit_exits_class fb2_eat fb2_eatCommit

/-! ## §3. FRAGILE-3: the hidden-buried opposing lows, with the
committed reveal channel (`fb3`)

The §2 spine (forkless origin, corridor, waste eat) plus the low
cells: the heart low `5♥` buried at the HEAD of p3's hidden deck
under a bare `S6`; the frozen host `D7` topping p4 over a hidden
deck that entombs the diamond low `5♦` (the opposing twin) behind
it.  This board's own beat: the committed reveal channel from the
post-eat state — the surfacing of the low, its seating attempt, and
the three decided grounds on which no corridor opens. -/

private def hmap3 : Suit → Nat
  | .heart => 3 | .diamond => 3 | .spade => 0 | .club => 0

private def fb3 : State where
  found := fun s => s.upCards.take (hmap3 s)
  piles := fun a => match a with
    | .p0 => ⟨[], []⟩
    | .p1 => ⟨[crd .club .ace, crd .club .two, crd .club .three,
               crd .club .four, crd .club .six, crd .club .seven,
               crd .club .eight, crd .club .nine, crd .club .ten,
               crd .club .jack, crd .club .queen, crd .club .king],
              [C5, D4, S3]⟩
    | .p2 => ⟨[], [S5]⟩
    | .p3 => ⟨[H5, crd .spade .seven, crd .spade .eight, crd .spade .nine,
               crd .spade .ten, crd .spade .jack, crd .spade .queen,
               crd .spade .king],
              [S6]⟩
    | .p4 => ⟨[crd .spade .ace, crd .spade .two, crd .spade .four,
               D5, crd .diamond .six, crd .diamond .eight,
               crd .diamond .nine, crd .diamond .ten, crd .diamond .jack,
               crd .diamond .queen, crd .diamond .king],
              [D7]⟩
    | .p5 => ⟨[crd .heart .six, crd .heart .seven, crd .heart .eight,
               crd .heart .nine, crd .heart .ten, crd .heart .jack,
               crd .heart .queen, crd .heart .king], []⟩
    | .p6 => ⟨[], []⟩
  stock := []
  waste := [H4]
  drawStep := 1

private theorem fb3_wf_found : ∀ s : Suit, ∃ n, fb3.found s = s.upCards.take n := by
  intro s
  cases s with
  | spade => exact ⟨0, rfl⟩
  | heart => exact ⟨3, rfl⟩
  | diamond => exact ⟨3, rfl⟩
  | club => exact ⟨0, rfl⟩

private theorem fb3_wf_runs : ∀ a : Anchor, runOK (fb3.piles a).faceUp = true := by
  intro a
  cases a <;> rfl

private theorem fb3_wf_count : ∀ c ∈ Card.universe, fb3.cardCount c = 1 := by
  intro c _
  rcases c with ⟨s, r⟩
  cases s <;> cases r <;> decide

private theorem fb3_wf : fb3.WF :=
  ⟨fb3_wf_found, fb3_wf_runs, fb3_wf_count, by decide⟩

/-- **§3 THE QUIET ORIGIN**: forkless, decided (the member rides the
waste). -/
theorem fb3_notFork : forkStateSB fb3 = false := by decide

/-- **§3 THE CORRIDOR, UNCHANGED**: the waste seating lands the
fork, decided there; the low cells do not interfere (the census
covers them: `S6`, `D7` rank-cold, the buried lows hidden). -/
private def fb3F : State := stepD fb3 (Move.wasteToTab H4 (Sum.inr S5))

theorem fb3_corridor : State.step fb3 (Move.wasteToTab H4 (Sum.inr S5)) = some fb3F := by
  rfl

theorem fb3F_forkSB : forkStateSB fb3F = true := by decide

theorem fb3F_witness : forkWitnessSB fb3F = some H4 := by decide

theorem fb3F_forkWitness : ForkWitness fb3F H4 :=
  forkWitnessSB_sound (step_wf fb3_wf fb3_corridor) fb3F_witness

theorem fb3_hhed :
    ∃ (F : State) (π : List Move) (x : Card),
      fb3.run π = some F ∧ ForkWitness F x :=
  surviveEx fb3 fb3F [Move.wasteToTab H4 (Sum.inr S5)] H4
    (run_one fb3_corridor) fb3F_forkWitness

/-- **§3 THE EAT**: §2's waste founding, graded the same way. -/
private def fb3E : State := stepD fb3 (Move.wasteToFound H4)

theorem fb3_eat : State.step fb3 (Move.wasteToFound H4) = some fb3E := by rfl

theorem fb3_eatCommit : irreversibleAt fb3 (Move.wasteToFound H4) :=
  irr_of_desc cycleCount (fun s m s' h => cycleCount_step h) fb3_eat
    (by have := cycleCount_step_wasteToFound fb3_eat; omega)

/-- **§3 THE REPAIR, ONE LEG, LANDING THE CORRIDOR STATE EXACTLY**
— the low cells sit away from every leg. -/
private def fb3R : State := stepD fb3E (Move.foundToTab H4 (Sum.inr S5))

theorem fb3_repair : State.step fb3E (Move.foundToTab H4 (Sum.inr S5)) = some fb3R := by
  rfl

theorem fb3R_eq : fb3R = fb3F := by
  refine State.ext (funext fun σ => ?_) (funext fun a => ?_) ?_ ?_ ?_
  · cases σ <;> rfl
  · cases a <;> rfl
  · rfl
  · rfl
  · rfl

/-- **§3 VERDICT (the §2 arm): DOWNWARD-FORK-SURVIVES, DISTANCE 1.** -/
theorem fb3_survives :
    ∃ (F : State) (π : List Move) (x : Card),
      fb3E.run π = some F ∧ ForkWitness F x :=
  surviveEx fb3E fb3R [Move.foundToTab H4 (Sum.inr S5)] H4
    (run_one fb3_repair)
    (by rw [fb3R_eq]; exact fb3F_forkWitness)

/-- **§3 THE REVEAL CHANNEL, COMMITTED**: from the post-eat state,
the bare `S6` slides onto the frozen host `D7`, stripping p3 to
its deck — the buried heart low `5♥` surfaces.  The slide is
jury-barred (banked census bar) and monotone-graded: a genuine
reveal commitment, i.e. the surfacing is IRREVERSIBLE. -/
private def fb3W : State := stepD fb3E (Move.tabToTab S6 (Sum.inr D7))

theorem fb3_revealA : State.step fb3E (Move.tabToTab S6 (Sum.inr D7)) = some fb3W := by
  rfl

theorem fb3_revealA_jury : ¬ reversibleAtW fb3E (Move.tabToTab S6 (Sum.inr D7)) :=
  journey_tabToTab_never_reveal fb3_revealA
    (show fb3E.pileHolding S6 = some Anchor.p3 from rfl)
    (show below S6 (fb3E.piles Anchor.p3).faceUp = [] from rfl)
    (show (fb3E.piles Anchor.p3).hidden ≠ [] from by decide)

theorem fb3_revealA_commit : irreversibleAt fb3E (Move.tabToTab S6 (Sum.inr D7)) :=
  irr_of_desc hiddenTotal (fun s m s' h => hiddenTotal_step h) fb3_revealA
    (by decide)

/-- **§3 THE SURFACED LOW, HOT AND BARE**: hearts now stand at 4
(the member was eaten), so the revealed `5♥` is its suit's
next-up — face-up over a NONEMPTY hidden deck, the exact residency
the seat clause bars. -/
theorem fb3W_lowUp :
    (fb3W.piles Anchor.p3).faceUp = [H5] ∧
      (fb3W.piles Anchor.p4).faceUp = [D7, S6] ∧
        rungAt fb3W Suit.heart = 4 ∧ fb3W.nextUp H5 = true :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- **§3 ARMOR (i): the seat clause at the bare-over-hidden low** —
hot, face-up, and S-DEAD anyway (decided): the surfacing does not
even begin a corridor. -/
theorem fb3W_lowSeatedBar :
    fb3W.nextUp H5 = true ∧ canRaiseSB fb3W H5 = false ∧
      forkStateSB fb3W = false :=
  ⟨rfl, by decide, by decide⟩

/-- **§3 THE LOW'S SEATING ATTEMPT**: the only landing the
surfacing opened is the frozen host's new top (`5♥` onto `6♠`) —
another committed reveal (the deck pays `S7`); the low SEATS
itself, and the census turns it S-live. -/
private def fb3X : State := stepD fb3W (Move.tabToTab H5 (Sum.inr S6))

theorem fb3_seatTry : State.step fb3W (Move.tabToTab H5 (Sum.inr S6)) = some fb3X := by
  rfl

theorem fb3X_seated :
    (fb3X.piles Anchor.p4).faceUp = [D7, S6, H5] ∧
      (fb3X.piles Anchor.p3).faceUp = [crd .spade .seven] ∧
        canRaiseSB fb3X H5 = true :=
  ⟨rfl, rfl, by decide⟩

/-- **§3 ARMOR (ii)+(iii): the seated low still saturates no pair**
— its TWIN `5♦` rides the frozen host's hidden deck (membership
decided; the host run cannot move again: no black eight exists to
carry `D7`), and the deeper cascade head `S7` is rank-cold.  A live
member with a dead twin is no fork: the census decides. -/
theorem fb3X_twinBuried : D5 ∈ (fb3X.piles Anchor.p4).hidden := by decide

theorem fb3X_notFork : forkStateSB fb3X = false := by decide

theorem fb3_seatTryCommit : irreversibleAt fb3W (Move.tabToTab H5 (Sum.inr S6)) :=
  irr_of_desc hiddenTotal (fun s m s' h => hiddenTotal_step h) fb3_seatTry
    (by decide)

/-! ## §4. The verdict ledger -/

/-- **THE PROBE LEDGER** — every board, one conjunction:

* FRAGILE-1: the origin is a sole-pair fork; the bare-lift eat
  commits; the EATEN SEAL is witnessed (both return seats refuse);
  **SURVIVES, DISTANCE 0** (the successor is itself the fork).
* FRAGILE-2: the quiet origin is forkless WITH a one-leg corridor;
  the waste eat commits and EXITS the class; the post-eat state is
  the witnessed danger (forkless, decided); the seat hosts survive
  the eat verbatim (`two_zone_exits_playable` consumed); **SURVIVES,
  DISTANCE 1** (the one-leg pull lands the corridor state exactly);
  the junk cells locked (S-dead and vanilla-dead).
* FRAGILE-3: the §2 arm holds verbatim on the low-cells economy;
  the committed reveal surfaces the buried heart low HOT-AND-BARE
  and forklessness holds at the surfacing (seat bar) AND at the
  seated state (the twin entombed behind the frozen host); the
  seating attempt is itself a commitment. -/
theorem ForkFloorProbe_verdicts :
    fb1.WF ∧ forkStateSB fb1 = true ∧
      State.step fb1 (Move.tabToFound S4) = some fb1S ∧
        irreversibleAt fb1 (Move.tabToFound S4) ∧
          State.step fb1S (Move.foundToTab S4 (Sum.inl Anchor.p3)) = none ∧
            State.step fb1S (Move.foundToTab S4 (Sum.inr S5)) = none ∧
              forkStateSB fb1S = true ∧
                (∃ (F : State) (π : List Move) (x : Card),
                  fb1S.run π = some F ∧ ForkWitness F x) ∧
      fb2.WF ∧ forkStateSB fb2 = false ∧
        (∃ (F : State) (π : List Move) (x : Card),
          fb2.run π = some F ∧ ForkWitness F x) ∧
          irreversibleAt fb2 (Move.wasteToFound H4) ∧
            forkStateSB fb2E = false ∧
              ¬ sameOrbitSetoid.r fb2 fb2E ∧
                (∃ (F : State) (π : List Move) (x : Card),
                  fb2E.run π = some F ∧ ForkWitness F x) ∧
      fb3.WF ∧ forkStateSB fb3 = false ∧
        (∃ (F : State) (π : List Move) (x : Card),
          fb3.run π = some F ∧ ForkWitness F x) ∧
          irreversibleAt fb3 (Move.wasteToFound H4) ∧
            (∃ (F : State) (π : List Move) (x : Card),
              fb3E.run π = some F ∧ ForkWitness F x) ∧
              irreversibleAt fb3E (Move.tabToTab S6 (Sum.inr D7)) ∧
                canRaiseSB fb3W H5 = false ∧ forkStateSB fb3W = false ∧
                  canRaiseSB fb3X H5 = true ∧ forkStateSB fb3X = false := by
  obtain ⟨hsealL, hsealR⟩ := fb1S_sealRefused
  exact ⟨fb1_wf, fb1_forkSB, fb1_eat, fb1_eatCommit, hsealL, hsealR,
    fb1S_forkSB, fb1_survives,
    fb2_wf, fb2_notFork, fb2_hhed, fb2_eatCommit, fb2E_notFork,
    fb2_classExit, fb2_survives,
    fb3_wf, fb3_notFork, fb3_hhed, fb3_eatCommit, fb3_survives,
    fb3_revealA_commit, fb3W_lowSeatedBar.2.1, fb3W_lowSeatedBar.2.2,
    fb3X_seated.2.2, fb3X_notFork⟩

/-! ## The audit battery

Fresh heads `#print axioms`-audited — decide rows at `[propext]`
grade, journey-consumed and monotone-consumed rows at
`[propext, Quot.sound]`, zero sorry, zero `Classical.choice`
(the step rows are kernel folds; the census rows decide). -/

#print axioms fb1_forkSB
#print axioms fb1_witness
#print axioms fb1_forkWitness
#print axioms fb1_eat
#print axioms fb1_eatCommit
#print axioms fb1S_sealRefused
#print axioms fb1S_forkSB
#print axioms fb1S_witness
#print axioms fb1S_forkWitness
#print axioms fb1_survives
#print axioms fb2_notFork
#print axioms fb2_corridor
#print axioms fb2F_forkSB
#print axioms fb2F_witness
#print axioms fb2F_forkWitness
#print axioms fb2_hhed
#print axioms fb2_eat
#print axioms fb2_eatCommit
#print axioms fb2E_notFork
#print axioms fb2_seatsSurvive
#print axioms fb2_repair
#print axioms fb2R_eq
#print axioms fb2_survives
#print axioms fb2_junkCold
#print axioms fb2_classExit
#print axioms fb3_notFork
#print axioms fb3_corridor
#print axioms fb3F_forkSB
#print axioms fb3F_forkWitness
#print axioms fb3_hhed
#print axioms fb3_eat
#print axioms fb3_eatCommit
#print axioms fb3_repair
#print axioms fb3R_eq
#print axioms fb3_survives
#print axioms fb3_revealA
#print axioms fb3_revealA_jury
#print axioms fb3_revealA_commit
#print axioms fb3W_lowUp
#print axioms fb3W_lowSeatedBar
#print axioms fb3_seatTry
#print axioms fb3X_seated
#print axioms fb3X_twinBuried
#print axioms fb3X_notFork
#print axioms fb3_seatTryCommit
#print axioms ForkFloorProbe_verdicts

