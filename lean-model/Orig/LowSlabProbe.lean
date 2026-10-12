import Orig.ForkStateSB
import Orig.Phase
import Orig.LowSlab

/-!
# Orig.LowSlabProbe — THE LOW-SLAB REFUTER-FIRST PROBE BOARDS

Decide-grade evidence about the four high-risk residues of
`Orig/LowSlab.lean`'s §4 tree, on one hand-built fork economy (fork
point `r = 3`, witness `4♥`, covered twin `4♦`, family rungs pinned at
3, blacks at 0 — every nonpair card rank-cold or stock/hidden-buried,
so the pair saturation is universe-decided):

* **§1 `lb0` — THE BASE FORK.** `forkStateSB lb0 = true` with witness
  `4♥` decided; the full `ForkWitness` parcel read through
  `forkWitnessSB_sound`; the twin under its fitting black-three cover
  over a live takeback seat (`C5`), the live member topped over `S5`;
  `familyBelowFrontier lb0 H4` confirmed TWICE (kernel and through the
  public `fork_self_low`).  The stock holds `5♥` over an empty waste
  (the Q1 pristine-draw economy).
* **§2 THE TWIN-LIFT VARIANT — Q(A'): VERDICT: EXHIBITED, REVERSIBLY
  REACHABLE.**  The cover hops off the twin (`tabToTab S3 (inr H4)`),
  the twin raises (`tabToFound D4`), and the ROUND TRIP is certified
  both ways over per-leg one-move mirrors (`lb1` is macro-CLASS-joined
  to `lb0`, `sameOrbitSetoid.r lb0 lb1`), while reading EXACTLY
  elevated (`¬ familyBelowFrontier lb1 H4`: the twin consumed) and —
  the WF-grade tableau read — with the twin OUT of the tableau, at
  both endpoints of a certified journey (`Orig/SlabEquiv`'s
  `twin_slab_tableau` shape).  The hidden pin rides the class
  (`shuffle_hiddenPinned`).  The x-lift datapoint `lbX`: raising the
  LIVE member keeps the state ON THE SLAB — the owner's refinement
  making x-lifts slab-internal, on record (with the fork census
  dissolving without touching slab membership).
* **§3 Q1 (draw kind): VERDICT: COMMITTED, PRISTINE-GRADE.**  Draws at
  `lb0` AND at the elevated `lb1` are full commitments
  (`draw_irreversible_pristine` — the banked row, premises
  kernel-folded) with a non-identity cycle effect (one card paid into
  the waste).  The fourth-kind discovery holds on-board;
  `fork_lowbridge_draw`'s census note is honest.
* **§4 Q2 (reveal kind): VERDICT: COMMITTED, CONTENT CLASS-INVARIANT.**
  The `C5` slide off the twin's emptied seat reveals the club deck's
  head `C6` — jury-certified one-way
  (`journey_tabToTab_never_reveal`) and commitment-graded by the
  monotone (`irr_of_desc hiddenTotal`), and the revealed content is
  class-invariant: `shuffle_hiddenPinned` reads the SAME hidden head
  at the base and the elevated member.
* **§5 Q3 (pull kind): VERDICT: CANDIDATE-VACUOUS AT WF.**  Two
  engineered tries — the twin takeback pull at `lb1` (§2's own
  certified class leg) and a KING giveback to an empty anchor on the
  dedicated `kb` board — both reversible by their one-move mirrors
  (kernel-verified).  No WF pull-commit was found to instantiate
  `fork_lowbridge_pull`'s shape; the WF-gated vacuity corollary
  (`Orig/LowSlab`'s own `lowslab_pull_wf_undo` residue, its route
  complete) is the integrator's retirement option.
* **§6 Q5 (elevated duplicates): VERDICTS: DUPLICATE-FOUND (×2).**
  For each commitment at the elevated member — the `C5` reveal-slide
  and the draw — the SAME move fires from the slab member `lb0`, the
  target classes match by exhibited re-bridges (the class legs
  RE-FIRE at the committed boards — the commit touched only cells the
  journeys do not read), and the LOW DUPLICATE is fully assembled:
  membership, slab seat, step, COMMIT GRADE (one direct by the
  monotone, one through `fork_lowbridge_commitGlue` — the glue row's
  first on-board consumption), target-class match.  The sufficiency
  conclusion is exhibited as a concrete five-tuple twice.
* **§7 `lbT` — the tower census datapoint** (not a counterexample
  candidate): a deeper host stack under the twin leaves the door
  arithmetic untouched (the wholesale cover slide and twin raise still
  fire, decided; the raised state reads elevated) — host depth is
  door-inert.

Every row is decide- or kernel-grade; the measure consumption is
`irr_of_desc` + the public Table-2 monotone.  Zero sorry.
-/

/-! ## §0. The private kit -/

private def crd (s : Suit) (r : Rank) : Card := ⟨s, r⟩

private def stepD (st : State) (m : Move) : State :=
  match st.step m with
  | none => st
  | some s' => s'

private def H4 : Card := crd .heart .four
private def H5 : Card := crd .heart .five
private def H6 : Card := crd .heart .six
private def HK : Card := crd .heart .king
private def D4 : Card := crd .diamond .four
private def S3 : Card := crd .spade .three
private def S5 : Card := crd .spade .five
private def C5 : Card := crd .club .five
private def C6 : Card := crd .club .six

/-! ## §1. THE BASE FORK `lb0`

Rungs ♥ 3 / ♦ 3 / ♠ 0 / ♣ 0 — the fork point `r = 3` (`4♥`'s index);
both family rungs pinned at `r`.  p1 hosts the TWIN TOWER: the covered
twin `4♦` over its live takeback seat `C5`, under the fitting
black-three cover `S3`, over the twelve-card club deck (head `C6` —
the reveal datum of §4); p2 hosts the LIVE member `4♥` topped over
`S5`; p3 hosts the bare `H6` (the §4 slide's landing host); p0/p4/p5/
p6 are the filler hosts; the stock holds `5♥` over an empty waste. -/

private def hmaplb : Suit → Nat
  | .heart => 3 | .diamond => 3 | .spade => 0 | .club => 0

private def lb0 : State where
  found := fun s => s.upCards.take (hmaplb s)
  piles := fun a => match a with
    | .p0 => ⟨[], []⟩
    | .p1 => ⟨[crd .club .six, crd .club .seven, crd .club .eight,
               crd .club .nine, crd .club .ten, crd .club .jack,
               crd .club .queen, crd .club .king, crd .club .three,
               crd .club .two, crd .club .four, crd .club .ace],
              [C5, D4, S3]⟩
    | .p2 => ⟨[], [S5, H4]⟩
    | .p3 => ⟨[], [H6]⟩
    | .p4 => ⟨[crd .spade .ace, crd .spade .two, crd .spade .four,
               crd .spade .six, crd .spade .seven, crd .spade .eight,
               crd .spade .nine, crd .spade .ten, crd .spade .jack,
               crd .spade .queen, crd .spade .king], []⟩
    | .p5 => ⟨[crd .heart .seven, crd .heart .eight, crd .heart .nine,
               crd .heart .ten, crd .heart .jack, crd .heart .queen,
               crd .heart .king], []⟩
    | .p6 => ⟨[crd .diamond .five, crd .diamond .six, crd .diamond .seven,
               crd .diamond .eight, crd .diamond .nine, crd .diamond .ten,
               crd .diamond .jack, crd .diamond .queen, crd .diamond .king],
              []⟩
  stock := [H5]
  waste := []
  drawStep := 1

private theorem lb0_wf_found : ∀ s : Suit, ∃ n, lb0.found s = s.upCards.take n := by
  intro s
  cases s with
  | spade => exact ⟨0, rfl⟩
  | heart => exact ⟨3, rfl⟩
  | diamond => exact ⟨3, rfl⟩
  | club => exact ⟨0, rfl⟩

private theorem lb0_wf_runs : ∀ a : Anchor, runOK (lb0.piles a).faceUp = true := by
  intro a
  cases a <;> rfl

private theorem lb0_wf_count : ∀ c ∈ Card.universe, lb0.cardCount c = 1 := by
  intro c _
  rcases c with ⟨s, r⟩
  cases s <;> cases r <;> decide

private theorem lb0_wf : lb0.WF :=
  ⟨lb0_wf_found, lb0_wf_runs, lb0_wf_count, by decide⟩

/-- **THE BASE IS A STRONG FORK** — the census folds {4♥, 4♦}. -/
theorem lb0_forkSB : forkStateSB lb0 = true := by decide

theorem lb0_forkState : forkState lb0 := (forkStateSB_true_iff lb0_wf).mp lb0_forkSB

/-- The witness is the vanilla-live `4♥`; the covered twin `4♦` is
vanilla-dead under its cover. -/
theorem lb0_witness : forkWitnessSB lb0 = some H4 := by rfl

theorem lb0_forkWitness : ForkWitness lb0 H4 :=
  forkWitnessSB_sound lb0_wf lb0_witness

/-- **THE PAIR SATURATION, UNIVERSE-DECIDED**: exactly the two pair
members are S-live; nothing else in the deck can raise, now or through
slides — the black aces are buried (stock/hidden), every other card is
rank-cold at its suit's rung. -/
theorem lb0_ledger :
    (∀ c ∈ Card.universe, canRaiseSB lb0 c = true ↔ (c = H4 ∨ c = D4)) ∧
      canRaiseB lb0 D4 = false := by
  refine ⟨?_, by decide⟩
  intro c _
  rcases c with ⟨s, r⟩
  cases s <;> cases r <;> decide

/-- The twin-cover anatomy on record: the covered twin sits on its
live takeback seat `C5` under the fitting black-three cover, with the
club deck beneath (the §4 reveal's content — its head `C6`). -/
theorem lb0_cover :
    (lb0.piles Anchor.p1).faceUp = [C5, D4, S3] ∧
      (lb0.piles Anchor.p1).hidden = C6 :: (lb0.piles Anchor.p1).hidden.tail ∧
        (lb0.piles Anchor.p1).hidden ≠ [] ∧
          lb0.nextUp D4 = true ∧ lb0.nextUp H4 = true ∧
            (lb0.piles Anchor.p2).faceUp = [S5, H4] :=
  ⟨rfl, rfl, by decide, rfl, rfl, rfl⟩

/-- The rung tuple of the fork: both family suits at `r = 3`, blacks
at 0. -/
theorem lb0_rungs :
    rungAt lb0 Suit.heart = 3 ∧ rungAt lb0 Suit.diamond = 3 ∧
      rungAt lb0 Suit.spade = 0 ∧ rungAt lb0 Suit.club = 0 :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- **THE SLAB READ AT THE ORIGIN, TWICE**: the refined twin-side slab
holds at the base by kernel, and through the public self-slab row
(the first probe consumption of `Orig.LowSlab`'s §2). -/
theorem lb0_slab : familyBelowFrontier lb0 H4 := by
  unfold familyBelowFrontier
  decide

theorem lb0_slab_viaSelf : familyBelowFrontier lb0 H4 :=
  fork_self_low lb0_forkWitness

theorem lb0_class_refl : sameOrbitSetoid.r lb0 lb0 :=
  sameOrbitSetoid.iseqv.1 lb0

theorem lb0_zone :
    lb0.stock = [H5] ∧ lb0.waste = [] ∧ lb0.drawStep = 1 :=
  ⟨rfl, rfl, rfl⟩

/-! ## §2. THE TWIN-LIFT VARIANT `lb1` — Q(A')

The elevation play the old route sketched, as a board: (1) the cover
hops off the twin onto the live member's top (`tabToTab S3 (inr H4)`);
(2) the twin raises (`tabToFound D4`, diamonds 3→4 — past the fork
point).  Each leg is one-move-reversible; the successor states are
kernel-artifacts (`stepD`), their step rows and equality rows are
`rfl`/an `State.ext` component bash. -/

private def lb1a : State := stepD lb0 (Move.tabToTab S3 (Sum.inr H4))
private def lb1 : State := stepD lb1a (Move.tabToFound D4)

theorem lb0_slide : State.step lb0 (Move.tabToTab S3 (Sum.inr H4)) = some lb1a := by rfl
theorem lb1a_raise : State.step lb1a (Move.tabToFound D4) = some lb1 := by rfl

private theorem lb1a_slideback :
    State.step lb1a (Move.tabToTab S3 (Sum.inr D4)) = some lb0 := by
  have hstep : State.step lb1a (Move.tabToTab S3 (Sum.inr D4)) =
      some (stepD lb1a (Move.tabToTab S3 (Sum.inr D4))) := by rfl
  have hxEq : stepD lb1a (Move.tabToTab S3 (Sum.inr D4)) = lb0 := by
    refine State.ext (funext fun σ => ?_) (funext fun a => ?_) ?_ ?_ ?_
    · cases σ <;> rfl
    · cases a <;> rfl
    · rfl
    · rfl
    · rfl
  rw [hstep, hxEq]

private theorem lb1_pull :
    State.step lb1 (Move.foundToTab D4 (Sum.inr C5)) = some lb1a := by
  have hstep : State.step lb1 (Move.foundToTab D4 (Sum.inr C5)) =
      some (stepD lb1 (Move.foundToTab D4 (Sum.inr C5))) := by rfl
  have hxEq : stepD lb1 (Move.foundToTab D4 (Sum.inr C5)) = lb1a := by
    refine State.ext (funext fun σ => ?_) (funext fun a => ?_) ?_ ?_ ?_
    · cases σ <;> rfl
    · cases a <;> rfl
    · rfl
    · rfl
    · rfl
  rw [hstep, hxEq]

/-- **Q(A'), LEG BY LEG** — the cover hop and the twin raise are each
reversible by their one-move mirror (the run states
kernel-verified). -/
theorem lb0_slideRev : reversibleAtW lb0 (Move.tabToTab S3 (Sum.inr H4)) :=
  ⟨lb1a, [Move.tabToTab S3 (Sum.inr D4)], lb0_slide, run_one lb1a_slideback⟩

theorem lb1a_slidebackRev : reversibleAtW lb1a (Move.tabToTab S3 (Sum.inr D4)) :=
  ⟨lb0, [Move.tabToTab S3 (Sum.inr H4)], lb1a_slideback, run_one lb0_slide⟩

theorem lb1a_raiseRev : reversibleAtW lb1a (Move.tabToFound D4) :=
  ⟨lb1, [Move.foundToTab D4 (Sum.inr C5)], lb1a_raise, run_one lb1_pull⟩

theorem lb1_pullRev : reversibleAtW lb1 (Move.foundToTab D4 (Sum.inr C5)) :=
  ⟨lb1a, [Move.tabToFound D4], lb1_pull, run_one lb1a_raise⟩

/-- The witness journeys: forward `lb0 → lb1` through the hop+raise,
backward through the pull+re-slide. -/
theorem lbFwd : ShufflePlayW lb0
    [Move.tabToTab S3 (Sum.inr H4), Move.tabToFound D4] lb1 :=
  .cons lb0_slideRev lb0_slide (.cons lb1a_raiseRev lb1a_raise (.nil lb1))

theorem lbBwd : ShufflePlayW lb1
    [Move.foundToTab D4 (Sum.inr C5), Move.tabToTab S3 (Sum.inr D4)] lb0 :=
  .cons lb1_pullRev lb1_pull (.cons lb1a_slidebackRev lb1a_slideback (.nil lb0))

/-- **Q(A') VERDICT — EXHIBITED: the twin-elevated member is
REVERSIBLY reachable, witness round trip each way** — `lb0` and `lb1`
are macro-class mates through the two-leg journey, every leg's
`reversibleAtW` riding a `rfl`-verified mirror. -/
theorem lb_class : sameOrbitSetoid.r lb0 lb1 :=
  ⟨[Move.foundToTab D4 (Sum.inr C5), Move.tabToTab S3 (Sum.inr D4)], lbBwd,
    [Move.tabToTab S3 (Sum.inr H4), Move.tabToFound D4], lbFwd⟩

/-- **THE ELEVATED READ**: the twin side of the slab is BROKEN at
`lb1` (diamonds at 4, past the fork point 3) — the covered twin is
consumed; founds pinned; the under-seat `C5` stands alone over the
club deck. -/
theorem lb1_elevated :
    ¬ familyBelowFrontier lb1 H4 ∧ rungAt lb1 Suit.diamond = 4 ∧
      (lb1.piles Anchor.p1).faceUp = [C5] ∧ lb1.foundTop Suit.diamond = some D4 :=
  ⟨by unfold familyBelowFrontier; decide, rfl, rfl, rfl⟩

/-- The elevation's hidden pin, through the banked row: every pile's
hidden deck — including the twin's club deck and its head `C6` — is
carried verbatim along the class journeys. -/
theorem lb_hiddenPin (a : Anchor) :
    (lb1.piles a).hidden = (lb0.piles a).hidden :=
  shuffle_hiddenPinned lbFwd a

/-- **THE X-LIFT DATAPPOINT** — raising the LIVE member (hearts
3→4) keeps the state ON THE SLAB: the refined slab reads the twin
side alone, so x-lifts are slab-internal.  The lift rides reversibly
(one-move mirror), and the fork census dissolves without touching
slab membership. -/
private def lbX : State := stepD lb0 (Move.tabToFound H4)

theorem lb0_xlift : State.step lb0 (Move.tabToFound H4) = some lbX := by rfl

theorem lbX_slab : familyBelowFrontier lbX H4 := by
  unfold familyBelowFrontier
  decide

theorem lbX_notFork : forkStateSB lbX = false := by decide

/-- ...and the x-lift's one-move mirror parks the live member back. -/
theorem lbX_mirror :
    State.step lbX (Move.foundToTab H4 (Sum.inr S5)) = some lb0 := by
  have hstep : State.step lbX (Move.foundToTab H4 (Sum.inr S5)) =
      some (stepD lbX (Move.foundToTab H4 (Sum.inr S5))) := by rfl
  have hxEq : stepD lbX (Move.foundToTab H4 (Sum.inr S5)) = lb0 := by
    refine State.ext (funext fun σ => ?_) (funext fun a => ?_) ?_ ?_ ?_
    · cases σ <;> rfl
    · cases a <;> rfl
    · rfl
    · rfl
    · rfl
  rw [hstep, hxEq]

theorem lb0_xliftRev : reversibleAtW lb0 (Move.tabToFound H4) :=
  ⟨lbX, [Move.foundToTab H4 (Sum.inr S5)], lb0_xlift, run_one lbX_mirror⟩

/-! ## §3. Q1 — THE DRAW KIND, PRISTINE-GRADE COMMITMENTS

The banked draw rows of `Orig/Phase.lean`, instantiated: with a
positive draw step, a nonempty stock and an empty waste, the draw DEALS
one card into the waste (a non-identity cycle effect) and is a full
`irreversibleAt` commitment — at the base AND at the elevated member
(the class journeys never touch the zone). -/

private def lb0D : State := stepD lb0 Move.draw
private def lb1D : State := stepD lb1 Move.draw

theorem lb0_drawStep : State.step lb0 Move.draw = some lb0D := by rfl
theorem lb1_drawStep : State.step lb1 Move.draw = some lb1D := by rfl

/-- **Q1 VERDICT — COMMITTED AT BOTH BOARDS**: the same pristine-draw
row of `Orig/Phase.lean` fires at the base and at the twin-elevated
member (its zone untouched by the class legs). -/
theorem lb0_drawCommit : irreversibleAt lb0 Move.draw :=
  draw_irreversible_pristine (by decide) (by decide) (by rfl)

theorem lb1_drawCommit : irreversibleAt lb1 Move.draw :=
  draw_irreversible_pristine (by decide) (by decide) (by rfl)

/-- The non-identity cycle effect: exactly one card paid into the
waste, the stock emptied — the pre-draw arrangement never recurs
(the banked row's own argument, read at the board). -/
theorem lb0D_zone :
    lb0D.waste.length = 1 ∧ lb0D.stock = [] ∧ lb0.waste.length = 0 :=
  ⟨by rfl, rfl, rfl⟩

/-! ## §4. Q2 — THE REVEAL KIND AT AN IN-CLASS MEMBER

The `C5` slide at the elevated member `lb1`: the twin's under-seat
stands alone over the club deck (the lone-host anatomy), the slide
strips it, the deck's head `C6` flips — a revealing slide: THE
reveal-commit of the taxonomy, at a member inside the certified
class. -/

private def lb2 : State := stepD lb1 (Move.tabToTab C5 (Sum.inr H6))

theorem lb2_step : State.step lb1 (Move.tabToTab C5 (Sum.inr H6)) = some lb2 := by rfl

/-- The jury read: no witness journey can carry the revealing slide
(the banked census). -/
theorem lb2_jury : ¬ reversibleAtW lb1 (Move.tabToTab C5 (Sum.inr H6)) :=
  journey_tabToTab_never_reveal lb2_step
    (show lb1.pileHolding C5 = some Anchor.p1 from rfl)
    (show below C5 (lb1.piles Anchor.p1).faceUp = [] from rfl)
    (show (lb1.piles Anchor.p1).hidden ≠ [] from by decide)

/-- **Q2 VERDICT, COMMIT GRADE — the monotone's read**: the reveal
strictly drops the hidden total, and no legal move ever raises it, so
the slide is a full `irreversibleAt` commitment. -/
theorem lb2_commit : irreversibleAt lb1 (Move.tabToTab C5 (Sum.inr H6)) :=
  irr_of_desc hiddenTotal (fun s m s' hstep => hiddenTotal_step hstep)
    lb2_step (by decide)

/-- **THE REVEALED CONTENT IS CLASS-INVARIANT — the route's claim,
read at the board**: the flip exposed exactly the club deck's head
`C6` — the same card every class member holds as that pile's hidden
head (the deck rides verbatim along the journeys,
`lb_hiddenPin`). -/
theorem lb2_content :
    (lb2.piles Anchor.p1).faceUp = [C6] ∧
      (lb0.piles Anchor.p1).hidden = C6 :: (lb0.piles Anchor.p1).hidden.tail ∧
        (lb1.piles Anchor.p1).hidden = (lb0.piles Anchor.p1).hidden :=
  ⟨rfl, rfl, lb_hiddenPin Anchor.p1⟩

/-! ## §5. Q3 — THE PULL KIND: VACUITY ATTEMPTS AT WF BOARDS

The `fork_lowbridge_pull` residue's shape — a `foundToTab` commitment
at a WF member — tried twice, both reversible by one-move mirrors:

* TRY 1: the twin takeback `foundToTab D4 (inr C5)` at `lb1`
  (`lb1_pullRev` above) — the mirror re-raise is licensed.
* TRY 2: the KING giveback to an empty anchor on the dedicated `kb`
  economy — the only `inl`-seat pull the guards ever license — again
  mirrored.

No instance found; the verdict row below. -/

private def kb : State where
  found := fun s => s.upCards.take (match s with
    | .heart => 13 | _ => 0)
  piles := fun _ => ⟨[], []⟩
  stock :=
    [crd .spade .ace, crd .spade .two, crd .spade .three, crd .spade .four,
     crd .spade .five, crd .spade .six, crd .spade .seven, crd .spade .eight,
     crd .spade .nine, crd .spade .ten, crd .spade .jack, crd .spade .queen,
     crd .spade .king,
     crd .diamond .ace, crd .diamond .two, crd .diamond .three,
     crd .diamond .four, crd .diamond .five, crd .diamond .six,
     crd .diamond .seven, crd .diamond .eight, crd .diamond .nine,
     crd .diamond .ten, crd .diamond .jack, crd .diamond .queen,
     crd .diamond .king,
     crd .club .ace, crd .club .two, crd .club .three, crd .club .four,
     crd .club .five, crd .club .six, crd .club .seven, crd .club .eight,
     crd .club .nine, crd .club .ten, crd .club .jack, crd .club .queen,
     crd .club .king]
  waste := []
  drawStep := 1

private theorem kb_wf_found : ∀ s : Suit, ∃ n, kb.found s = s.upCards.take n := by
  intro s
  cases s with
  | spade => exact ⟨0, rfl⟩
  | heart => exact ⟨13, rfl⟩
  | diamond => exact ⟨0, rfl⟩
  | club => exact ⟨0, rfl⟩

private theorem kb_wf_runs : ∀ a : Anchor, runOK (kb.piles a).faceUp = true := by
  intro a
  cases a <;> rfl

private theorem kb_wf_count : ∀ c ∈ Card.universe, kb.cardCount c = 1 := by
  intro c _
  rcases c with ⟨s, r⟩
  cases s <;> cases r <;> decide

private theorem kb_wf : kb.WF :=
  ⟨kb_wf_found, kb_wf_runs, kb_wf_count, by decide⟩

theorem kb_anatomy :
    kb.foundTop Suit.heart = some HK ∧ (kb.piles Anchor.p0).faceUp = [] ∧
      kb.stock.length = 39 ∧ kb.waste = [] :=
  ⟨rfl, rfl, by decide, rfl⟩

/-- **Q3 TRY 2** — the king giveback lands the bare `K♥` onto the
empty anchor (theLicensed `inl` seat). -/
private def kbP : State := stepD kb (Move.foundToTab HK (Sum.inl Anchor.p0))

theorem kb_pull :
    State.step kb (Move.foundToTab HK (Sum.inl Anchor.p0)) = some kbP := by rfl

theorem kbP_mirror :
    State.step kbP (Move.tabToFound HK) = some kb := by
  have hstep : State.step kbP (Move.tabToFound HK) =
      some (stepD kbP (Move.tabToFound HK)) := by rfl
  have hxEq : stepD kbP (Move.tabToFound HK) = kb := by
    refine State.ext (funext fun σ => ?_) (funext fun a => ?_) ?_ ?_ ?_
    · cases σ <;> rfl
    · cases a <;> rfl
    · rfl
    · rfl
    · rfl
  rw [hstep, hxEq]

theorem kb_pullRev : reversibleAtW kb (Move.foundToTab HK (Sum.inl Anchor.p0)) :=
  ⟨kbP, [Move.tabToFound HK], kb_pull, run_one kbP_mirror⟩

/-- **Q3 VERDICT — CANDIDATE-VACUOUS AT WF**: both engineered tries
carry one-move mirrors (kernel-verified above; TRY 1 is §2's own
certified class leg `lb1_pullRev`).  The searched space: every shape
the `foundToTab` guards license at a WF board — `inr`-seat givebacks
(the undo row's own below-card read) and the `inl` king giveback; in
each the mirror `tabToFound` re-fires (the popped card is at its
build index by the founded-prefix discipline, and its pile-top search
is pinned by WF uniqueness).  The integrator's retirement option:
`Orig/LowSlab.lean`'s `lowslab_pull_wf_undo` [M], whose route is
exactly this derivation, promoted from residue to row. -/
theorem LowSlabProbe_q3 :
    reversibleAtW lb1 (Move.foundToTab D4 (Sum.inr C5)) ∧
      reversibleAtW kb (Move.foundToTab HK (Sum.inl Anchor.p0)) :=
  ⟨lb1_pullRev, kb_pullRev⟩

/-! ## §6. Q5 — THE DUPLICATES

### 6(a). The reveal-commit's low duplicate

The SAME slide at the slab member `lb0` — the run `[C5, D4, S3]`
slides wholesale onto `H6`, the twin pile empties and reveals `C6`
(itself a commitment, graded by the same monotone) — and the two
post-slide states are class-joined by an exhibited re-bridge: the
class legs (pull onto the takeback seat, cover hop) RE-FIRE at the
committed boards, because the commit touched only cells the journeys
do not read.  The glue row (`fork_lowbridge_commitGlue`, its first
on-board consumption) then grades the duplicate's OWN commitment from
the links alone, and the full five-tuple of the sufficiency
conclusion is exhibited. -/

private def lb2R : State := stepD lb0 (Move.tabToTab C5 (Sum.inr H6))
private def lb2P : State := stepD lb2 (Move.foundToTab D4 (Sum.inr C5))
private def lb2PS : State := stepD lb2P (Move.tabToTab S3 (Sum.inr D4))

theorem lb2R_step : State.step lb0 (Move.tabToTab C5 (Sum.inr H6)) = some lb2R := by rfl
theorem lb2P_step : State.step lb2 (Move.foundToTab D4 (Sum.inr C5)) = some lb2P := by rfl
theorem lb2PS_step : State.step lb2P (Move.tabToTab S3 (Sum.inr D4)) = some lb2PS := by rfl

/-- The re-bridge's landing IS the slab-side post-slide state. -/
theorem lb2PS_eq : lb2PS = lb2R := by
  refine State.ext (funext fun σ => ?_) (funext fun a => ?_) ?_ ?_ ?_
  · cases σ <;> rfl
  · cases a <;> rfl
  · rfl
  · rfl
  · rfl

theorem lb2PS_stepR :
    State.step lb2P (Move.tabToTab S3 (Sum.inr D4)) = some lb2R := by
  rw [← lb2PS_eq]
  exact lb2PS_step

/-- The re-bridge legs' mirrors: the pulled twin re-raises, the slid
cover comes home. -/
theorem lb2P_mirror : State.step lb2P (Move.tabToFound D4) = some lb2 := by
  have hstep : State.step lb2P (Move.tabToFound D4) =
      some (stepD lb2P (Move.tabToFound D4)) := by rfl
  have hxEq : stepD lb2P (Move.tabToFound D4) = lb2 := by
    refine State.ext (funext fun σ => ?_) (funext fun a => ?_) ?_ ?_ ?_
    · cases σ <;> rfl
    · cases a <;> rfl
    · rfl
    · rfl
    · rfl
  rw [hstep, hxEq]

theorem lb2PS_mirror :
    State.step lb2PS (Move.tabToTab S3 (Sum.inr H4)) = some lb2P := by
  have hstep : State.step lb2PS (Move.tabToTab S3 (Sum.inr H4)) =
      some (stepD lb2PS (Move.tabToTab S3 (Sum.inr H4))) := by rfl
  have hxEq : stepD lb2PS (Move.tabToTab S3 (Sum.inr H4)) = lb2P := by
    refine State.ext (funext fun σ => ?_) (funext fun a => ?_) ?_ ?_ ?_
    · cases σ <;> rfl
    · cases a <;> rfl
    · rfl
    · rfl
    · rfl
  rw [hstep, hxEq]

theorem lb2R_slideStep :
    State.step lb2R (Move.tabToTab S3 (Sum.inr H4)) = some lb2P := by
  rw [← lb2PS_eq]
  exact lb2PS_mirror

theorem lb2_pullRev : reversibleAtW lb2 (Move.foundToTab D4 (Sum.inr C5)) :=
  ⟨lb2P, [Move.tabToFound D4], lb2P_step, run_one lb2P_mirror⟩

theorem lb2P_slideRev : reversibleAtW lb2P (Move.tabToTab S3 (Sum.inr D4)) :=
  ⟨lb2PS, [Move.tabToTab S3 (Sum.inr H4)], lb2PS_step, run_one lb2PS_mirror⟩

theorem lb2P_raiseRev : reversibleAtW lb2P (Move.tabToFound D4) :=
  ⟨lb2, [Move.foundToTab D4 (Sum.inr C5)], lb2P_mirror, run_one lb2P_step⟩

theorem lb2PS_slidebackRev : reversibleAtW lb2PS (Move.tabToTab S3 (Sum.inr H4)) :=
  ⟨lb2P, [Move.tabToTab S3 (Sum.inr D4)], lb2PS_mirror, run_one lb2PS_step⟩

theorem lb2R_slideRev : reversibleAtW lb2R (Move.tabToTab S3 (Sum.inr H4)) :=
  ⟨lb2P, [Move.tabToTab S3 (Sum.inr D4)], lb2R_slideStep, run_one lb2PS_stepR⟩

/-- The re-bridge journeys: `lb2 → lb2R` through the pull+hop forwards,
back through the same class legs re-firing at the committed board. -/
theorem lb2Fwd : ShufflePlayW lb2
    [Move.foundToTab D4 (Sum.inr C5), Move.tabToTab S3 (Sum.inr D4)] lb2R :=
  .cons lb2_pullRev lb2P_step
    (.cons lb2P_slideRev lb2PS_stepR (.nil lb2R))

theorem lb2Bwd : ShufflePlayW lb2R
    [Move.tabToTab S3 (Sum.inr H4), Move.tabToFound D4] lb2 :=
  .cons lb2R_slideRev lb2R_slideStep
    (.cons lb2P_raiseRev lb2P_mirror (.nil lb2))

/-- **Q5(a) — THE TARGET CLASSES MATCH**: the same-move slide at the
slab member lands in the elevated member's post-commit class. -/
theorem lb2_class : sameOrbitSetoid.r lb2R lb2 :=
  ⟨[Move.foundToTab D4 (Sum.inr C5), Move.tabToTab S3 (Sum.inr D4)], lb2Fwd,
    [Move.tabToTab S3 (Sum.inr H4), Move.tabToFound D4], lb2Bwd⟩

/-- The slab-side slide is ITSELF a commitment (the same monotone:
wholesale run, emptied pile, revealed deck head). -/
theorem lb2R_commit : irreversibleAt lb0 (Move.tabToTab C5 (Sum.inr H6)) :=
  irr_of_desc hiddenTotal (fun s m s' hstep => hiddenTotal_step hstep)
    lb2R_step (by decide)

/-- **THE GLUE ROW'S FIRST ON-BOARD CONSUMPTION**: the duplicate's
commit grade, read from the class links alone (the original elevated
commitment + the produced slab-side step + the target-class match). -/
theorem lb2R_commit_viaGlue : irreversibleAt lb0 (Move.tabToTab C5 (Sum.inr H6)) :=
  fork_lowbridge_commitGlue lb_class lb0_class_refl lb2_step lb2_commit
    lb2R_step lb2_class

/-- **Q5(a) VERDICT — DUPLICATE-FOUND, FULLY ASSEMBLED**: the
sufficiency conclusion for the elevated reveal-commit, as a concrete
five-tuple — slab member `lb0`, the same slide, target class-matched,
commit grade included. -/
theorem lb2_dup :
    ∃ (u₀ : State) (m₀ : Move) (v₀ : State),
      sameOrbitSetoid.r lb0 u₀ ∧
      familyBelowFrontier u₀ H4 ∧
      State.step u₀ m₀ = some v₀ ∧
      irreversibleAt u₀ m₀ ∧
      sameOrbitSetoid.r v₀ lb2 :=
  ⟨lb0, Move.tabToTab C5 (Sum.inr H6), lb2R, lb0_class_refl, lb0_slab,
    lb2R_step, lb2R_commit_viaGlue, lb2_class⟩

/-! ### 6(b). The draw-commit's low duplicate

The draw at the elevated member and the draw at the slab member land
in the SAME target class: the class legs (cover hop, raise) commute
with the zone move pointwise (the board legs write no zone field), so
the fwd/bwd journeys re-fire after the draws. -/

private def lb1aD : State := stepD lb1a Move.draw
private def lb0Da : State := stepD lb0D (Move.tabToTab S3 (Sum.inr H4))

theorem lb0Da_eq : lb0Da = lb1aD := by
  refine State.ext (funext fun σ => ?_) (funext fun a => ?_) ?_ ?_ ?_
  · cases σ <;> rfl
  · cases a <;> rfl
  · rfl
  · rfl
  · rfl

theorem lb0D_slide :
    State.step lb0D (Move.tabToTab S3 (Sum.inr H4)) = some lb0Da := by rfl

theorem lb1aD_raise : State.step lb1aD (Move.tabToFound D4) = some lb1D := by
  have hstep : State.step lb1aD (Move.tabToFound D4) =
      some (stepD lb1aD (Move.tabToFound D4)) := by rfl
  have hxEq : stepD lb1aD (Move.tabToFound D4) = lb1D := by
    refine State.ext (funext fun σ => ?_) (funext fun a => ?_) ?_ ?_ ?_
    · cases σ <;> rfl
    · cases a <;> rfl
    · rfl
    · rfl
    · rfl
  rw [hstep, hxEq]

theorem lb0Da_raise : State.step lb0Da (Move.tabToFound D4) = some lb1D := by
  rw [lb0Da_eq]
  exact lb1aD_raise

theorem lb1D_pull :
    State.step lb1D (Move.foundToTab D4 (Sum.inr C5)) = some lb1aD := by
  have hstep : State.step lb1D (Move.foundToTab D4 (Sum.inr C5)) =
      some (stepD lb1D (Move.foundToTab D4 (Sum.inr C5))) := by rfl
  have hxEq : stepD lb1D (Move.foundToTab D4 (Sum.inr C5)) = lb1aD := by
    refine State.ext (funext fun σ => ?_) (funext fun a => ?_) ?_ ?_ ?_
    · cases σ <;> rfl
    · cases a <;> rfl
    · rfl
    · rfl
    · rfl
  rw [hstep, hxEq]

theorem lb1aD_slideback :
    State.step lb1aD (Move.tabToTab S3 (Sum.inr D4)) = some lb0D := by
  have hstep : State.step lb1aD (Move.tabToTab S3 (Sum.inr D4)) =
      some (stepD lb1aD (Move.tabToTab S3 (Sum.inr D4))) := by rfl
  have hxEq : stepD lb1aD (Move.tabToTab S3 (Sum.inr D4)) = lb0D := by
    refine State.ext (funext fun σ => ?_) (funext fun a => ?_) ?_ ?_ ?_
    · cases σ <;> rfl
    · cases a <;> rfl
    · rfl
    · rfl
    · rfl
  rw [hstep, hxEq]

theorem lb0D_slideRev : reversibleAtW lb0D (Move.tabToTab S3 (Sum.inr H4)) :=
  ⟨lb0Da, [Move.tabToTab S3 (Sum.inr D4)], lb0D_slide,
    run_one (by rw [lb0Da_eq]; exact lb1aD_slideback)⟩

theorem lb1aD_slidebackRev : reversibleAtW lb1aD (Move.tabToTab S3 (Sum.inr D4)) :=
  ⟨lb0D, [Move.tabToTab S3 (Sum.inr H4)], lb1aD_slideback,
    run_one (by
      have h := lb0D_slide
      rw [lb0Da_eq] at h
      exact run_one h)⟩

theorem lb0Da_raiseRev : reversibleAtW lb0Da (Move.tabToFound D4) :=
  ⟨lb1D, [Move.foundToTab D4 (Sum.inr C5)], lb0Da_raise, run_one lb1D_pull⟩

theorem lb1D_pullRev : reversibleAtW lb1D (Move.foundToTab D4 (Sum.inr C5)) :=
  ⟨lb1aD, [Move.tabToFound D4], lb1D_pull, run_one lb1aD_raise⟩

theorem lbFwdD : ShufflePlayW lb0D
    [Move.tabToTab S3 (Sum.inr H4), Move.tabToFound D4] lb1D :=
  .cons lb0D_slideRev lb0D_slide (.cons lb0Da_raiseRev lb0Da_raise (.nil lb1D))

theorem lbBwdD : ShufflePlayW lb1D
    [Move.foundToTab D4 (Sum.inr C5), Move.tabToTab S3 (Sum.inr D4)] lb0D :=
  .cons lb1D_pullRev lb1D_pull (.cons lb1aD_slidebackRev lb1aD_slideback (.nil lb0D))

theorem lbD_class : sameOrbitSetoid.r lb0D lb1D :=
  ⟨[Move.foundToTab D4 (Sum.inr C5), Move.tabToTab S3 (Sum.inr D4)], lbBwdD,
    [Move.tabToTab S3 (Sum.inr H4), Move.tabToFound D4], lbFwdD⟩

/-- **Q5(b) VERDICT — DUPLICATE-FOUND, FULLY ASSEMBLED**: the
sufficiency conclusion for the elevated draw-commit, as a concrete
five-tuple. -/
theorem lb1_dup :
    ∃ (u₀ : State) (m₀ : Move) (v₀ : State),
      sameOrbitSetoid.r lb0 u₀ ∧
      familyBelowFrontier u₀ H4 ∧
      State.step u₀ m₀ = some v₀ ∧
      irreversibleAt u₀ m₀ ∧
      sameOrbitSetoid.r v₀ lb1D :=
  ⟨lb0, Move.draw, lb0D, lb0_class_refl, lb0_slab,
    lb0_drawStep, lb0_drawCommit, lbD_class⟩

/-! ## §7. The tower datapoint `lbT` (census-only)

A deeper host stack under the twin (`D6` beneath the takeback seat
`C5`): the door arithmetic is UNTOUCHED — the twin's S-license and
vanilla-deadness hold (decided), the wholesale cover slide and twin
raise still fire (kernel), and the raised state reads elevated.  Host
depth is door-inert. -/

private def lbT : State where
  found := fun s => s.upCards.take (hmaplb s)
  piles := fun a => match a with
    | .p0 => ⟨[], []⟩
    | .p1 => ⟨[crd .club .six, crd .club .seven, crd .club .eight,
               crd .club .nine, crd .club .ten, crd .club .jack,
               crd .club .queen, crd .club .king, crd .club .three,
               crd .club .two, crd .club .four, crd .club .ace],
              [crd .diamond .six, C5, D4, S3]⟩
    | .p2 => ⟨[], [S5, H4]⟩
    | .p3 => ⟨[], [H6]⟩
    | .p4 => ⟨[crd .spade .ace, crd .spade .two, crd .spade .four,
               crd .spade .six, crd .spade .seven, crd .spade .eight,
               crd .spade .nine, crd .spade .ten, crd .spade .jack,
               crd .spade .queen, crd .spade .king], []⟩
    | .p5 => ⟨[crd .heart .seven, crd .heart .eight, crd .heart .nine,
               crd .heart .ten, crd .heart .jack, crd .heart .queen,
               crd .heart .king], []⟩
    | .p6 => ⟨[crd .diamond .five, crd .diamond .seven, crd .diamond .eight,
               crd .diamond .nine, crd .diamond .ten, crd .diamond .jack,
               crd .diamond .queen, crd .diamond .king], []⟩
  stock := [H5]
  waste := []
  drawStep := 1

private def lbTa : State := stepD lbT (Move.tabToTab S3 (Sum.inr H4))
private def lbTb : State := stepD lbTa (Move.tabToFound D4)

theorem lbT_forkSB : forkStateSB lbT = true := by decide

theorem lbT_twin :
    canRaiseSB lbT D4 = true ∧ canRaiseB lbT D4 = false ∧
      (lbT.piles Anchor.p1).faceUp = [crd .diamond .six, C5, D4, S3] :=
  ⟨by decide, by decide, rfl⟩

theorem lbT_slide :
    State.step lbT (Move.tabToTab S3 (Sum.inr H4)) = some lbTa := by rfl
theorem lbT_raise :
    State.step lbTa (Move.tabToFound D4) = some lbTb := by rfl

theorem lbT_elevated : ¬ familyBelowFrontier lbTb H4 := by
  unfold familyBelowFrontier
  decide

/-! ## §8. The verdict ledger -/

/-- **THE PROBE LEDGER** — every question, one conjunction: the base
fork with its parcel; the twin-lift round trip (Q(A'): EXHIBITED);
the pristine draw commitments (Q1: COMMITTED, both boards); the
reveal-commit and its class-invariant content (Q2: COMMITTED +
INVARIANT); the two pull-vacuity tries (Q3: CANDIDATE-VACUOUS at
WF); the two fully-assembled low duplicates (Q5: DUPLICATE-FOUND ×2 —
the reveal-slide and the draw, each with commit grade, one through
the glue row); the x-lift slab-internality; the tower's
door-inertness. -/

theorem LowSlabProbe_verdicts :
    forkStateSB lb0 = true ∧ forkWitnessSB lb0 = some H4 ∧
      ForkWitness lb0 H4 ∧ familyBelowFrontier lb0 H4 ∧
        sameOrbitSetoid.r lb0 lb1 ∧ ¬ familyBelowFrontier lb1 H4 ∧
          irreversibleAt lb0 Move.draw ∧ irreversibleAt lb1 Move.draw ∧
            irreversibleAt lb1 (Move.tabToTab C5 (Sum.inr H6)) ∧
              (lb2.piles Anchor.p1).faceUp = [C6] ∧
                reversibleAtW kb (Move.foundToTab HK (Sum.inl Anchor.p0)) ∧
                  familyBelowFrontier lbX H4 ∧
                    forkStateSB lbX = false ∧
                      (∃ (u₀ : State) (m₀ : Move) (v₀ : State),
                        sameOrbitSetoid.r lb0 u₀ ∧
                          familyBelowFrontier u₀ H4 ∧
                            State.step u₀ m₀ = some v₀ ∧
                              irreversibleAt u₀ m₀ ∧
                                sameOrbitSetoid.r v₀ lb2) ∧
                      (∃ (u₀ : State) (m₀ : Move) (v₀ : State),
                        sameOrbitSetoid.r lb0 u₀ ∧
                          familyBelowFrontier u₀ H4 ∧
                            State.step u₀ m₀ = some v₀ ∧
                              irreversibleAt u₀ m₀ ∧
                                sameOrbitSetoid.r v₀ lb1D) ∧
                        forkStateSB lbT = true :=
  ⟨lb0_forkSB, lb0_witness, lb0_forkWitness, lb0_slab, lb_class,
    lb1_elevated.1, lb0_drawCommit, lb1_drawCommit, lb2_commit,
    lb2_content.1, kb_pullRev, lbX_slab, lbX_notFork, lb2_dup, lb1_dup,
    lbT_forkSB⟩

/-! ### The audit battery

Fresh heads `#print axioms`-audited — decide rows at `[propext]`
grade, journey-consumed and monotone-consumed rows at
`[propext, Quot.sound]`, zero sorry, zero `Classical.choice`. -/

#print axioms lb0_forkSB
#print axioms lb0_forkState
#print axioms lb0_witness
#print axioms lb0_forkWitness
#print axioms lb0_ledger
#print axioms lb0_cover
#print axioms lb0_rungs
#print axioms lb0_slab
#print axioms lb0_slab_viaSelf
#print axioms lb0_class_refl
#print axioms lb0_zone
#print axioms lb0_slide
#print axioms lb1a_raise
#print axioms lb1a_slideback
#print axioms lb1_pull
#print axioms lb0_slideRev
#print axioms lb1a_slidebackRev
#print axioms lb1a_raiseRev
#print axioms lb1_pullRev
#print axioms lb_class
#print axioms lb1_elevated
#print axioms lb_hiddenPin
#print axioms lbX_slab
#print axioms lbX_notFork
#print axioms lbX_mirror
#print axioms lb0_xliftRev
#print axioms lb0_drawStep
#print axioms lb1_drawStep
#print axioms lb0_drawCommit
#print axioms lb1_drawCommit
#print axioms lb0D_zone
#print axioms lb2_step
#print axioms lb2_jury
#print axioms lb2_commit
#print axioms lb2_content
#print axioms kb_anatomy
#print axioms kb_pull
#print axioms kbP_mirror
#print axioms kb_pullRev
#print axioms LowSlabProbe_q3
#print axioms lb2R_step
#print axioms lb2P_step
#print axioms lb2PS_step
#print axioms lb2PS_eq
#print axioms lb2PS_stepR
#print axioms lb2P_mirror
#print axioms lb2PS_mirror
#print axioms lb2R_slideStep
#print axioms lb2_pullRev
#print axioms lb2P_slideRev
#print axioms lb2P_raiseRev
#print axioms lb2PS_slidebackRev
#print axioms lb2R_slideRev
#print axioms lb2Fwd
#print axioms lb2Bwd
#print axioms lb2_class
#print axioms lb2R_commit
#print axioms lb2R_commit_viaGlue
#print axioms lb2_dup
#print axioms lb0Da_eq
#print axioms lb0D_slide
#print axioms lb1aD_raise
#print axioms lb0Da_raise
#print axioms lb1D_pull
#print axioms lb1aD_slideback
#print axioms lb0D_slideRev
#print axioms lb1aD_slidebackRev
#print axioms lb0Da_raiseRev
#print axioms lb1D_pullRev
#print axioms lbFwdD
#print axioms lbBwdD
#print axioms lbD_class
#print axioms lb1_dup
#print axioms lbT_forkSB
#print axioms lbT_twin
#print axioms lbT_slide
#print axioms lbT_raise
#print axioms lbT_elevated
#print axioms LowSlabProbe_verdicts

/-! ## §9. ROUND 2, FAMILY 1 — BARE-LIFT RAISE COMMITS (`bb0`)

The raise row's rung bracket, never yet exercised.  Economy: rungs
♥ 3 / ♦ 3 / ♠ 3 / ♣ 0 — the third family rung makes `S4` hot; it sits
BARE over an empty deck at p3, so its raise is the census's BARE
NON-KING species (a completely bare pile: no face-up below, no
hidden).  The bare seat is S-license-dead (no slide can free it), so
– the probe confirms decide-grade – the board still certifies as a
strong fork of {H4, D4} while carrying an unraisable-in-class commit
card.  Elevation: the C3 cover hops onto the live member, the twin
raises (diamonds 3→4); the bare S4 is untouched by every elevation
leg, so THE COMMIT FIRES AT THE ELEVATED MEMBER TOO. -/

private def S4 : Card := crd .spade .four
private def C3 : Card := crd .club .three
private def C4 : Card := crd .club .four
private def D3 : Card := crd .diamond .three
private def D5 : Card := crd .diamond .five

private def hmapbb : Suit → Nat
  | .heart => 3 | .diamond => 3 | .spade => 3 | .club => 0

private def bb0 : State where
  found := fun s => s.upCards.take (hmapbb s)
  piles := fun a => match a with
    | .p0 => ⟨[], []⟩
    | .p1 => ⟨[crd .club .six, crd .club .seven, crd .club .eight,
               crd .club .nine, crd .club .ten, crd .club .jack,
               crd .club .queen, crd .club .king, crd .club .two,
               crd .club .four, crd .club .ace],
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

private theorem bb0_wf_found : ∀ s : Suit, ∃ n, bb0.found s = s.upCards.take n := by
  intro s
  cases s with
  | spade => exact ⟨3, rfl⟩
  | heart => exact ⟨3, rfl⟩
  | diamond => exact ⟨3, rfl⟩
  | club => exact ⟨0, rfl⟩

private theorem bb0_wf_runs : ∀ a : Anchor, runOK (bb0.piles a).faceUp = true := by
  intro a
  cases a <;> rfl

private theorem bb0_wf_count : ∀ c ∈ Card.universe, bb0.cardCount c = 1 := by
  intro c _
  rcases c with ⟨s, r⟩
  cases s <;> cases r <;> decide

private theorem bb0_wf : bb0.WF :=
  ⟨bb0_wf_found, bb0_wf_runs, bb0_wf_count, by decide⟩

/-- The bare hot `S4` is SB-DEAD (its bare seat fails the S-license),
so the pair saturation survives: the board IS a strong fork of
{H4, D4} while hosting an in-class-unraisable commit card (decided). -/
theorem bb0_forkSB : forkStateSB bb0 = true := by decide

theorem bb0_witness : forkWitnessSB bb0 = some H4 := by rfl

theorem bb0_forkWitness : ForkWitness bb0 H4 :=
  forkWitnessSB_sound bb0_wf bb0_witness

theorem bb0_refl : sameOrbitSetoid.r bb0 bb0 :=
  sameOrbitSetoid.iseqv.1 bb0

theorem bb0_slab : familyBelowFrontier bb0 H4 := by
  unfold familyBelowFrontier
  decide

theorem bb0_bare : (bb0.piles Anchor.p3).faceUp = [S4] ∧
    (bb0.piles Anchor.p3).hidden = [] ∧ bb0.nextUp S4 = true :=
  ⟨rfl, rfl, rfl⟩

/-- **FIG-1(a): THE BARE-LIFT COMMIT AT THE ELEVATED MEMBER** — a
witness chain to the twin-elevated member, then the bare `S4` raise
as the census's certified commit species. -/
private def bbA : State := stepD bb0 (Move.tabToTab C3 (Sum.inr H4))
private def bb1 : State := stepD bbA (Move.tabToFound D4)
private def bb1S : State := stepD bb1 (Move.tabToFound S4)
private def bb0S : State := stepD bb0 (Move.tabToFound S4)
private def bb0SA : State := stepD bb0S (Move.tabToTab C3 (Sum.inr H4))
private def bbSAS : State := stepD bb1S (Move.foundToTab D4 (Sum.inr C5))

theorem bb0_slide : State.step bb0 (Move.tabToTab C3 (Sum.inr H4)) = some bbA := by rfl
theorem bbA_raise : State.step bbA (Move.tabToFound D4) = some bb1 := by rfl
theorem bb1_bareStep : State.step bb1 (Move.tabToFound S4) = some bb1S := by rfl
theorem bb0_bareStep : State.step bb0 (Move.tabToFound S4) = some bb0S := by rfl
theorem bb0S_slide : State.step bb0S (Move.tabToTab C3 (Sum.inr H4)) = some bb0SA := by rfl
theorem bb1S_pull : State.step bb1S (Move.foundToTab D4 (Sum.inr C5)) = some bbSAS := by rfl

private theorem bbA_slideback :
    State.step bbA (Move.tabToTab C3 (Sum.inr D4)) = some bb0 := by
  have hstep : State.step bbA (Move.tabToTab C3 (Sum.inr D4)) =
      some (stepD bbA (Move.tabToTab C3 (Sum.inr D4))) := by rfl
  have hxEq : stepD bbA (Move.tabToTab C3 (Sum.inr D4)) = bb0 := by
    refine State.ext (funext fun σ => ?_) (funext fun a => ?_) ?_ ?_ ?_
    · cases σ <;> rfl
    · cases a <;> rfl
    · rfl
    · rfl
    · rfl
  rw [hstep, hxEq]

private theorem bb1_pull :
    State.step bb1 (Move.foundToTab D4 (Sum.inr C5)) = some bbA := by
  have hstep : State.step bb1 (Move.foundToTab D4 (Sum.inr C5)) =
      some (stepD bb1 (Move.foundToTab D4 (Sum.inr C5))) := by rfl
  have hxEq : stepD bb1 (Move.foundToTab D4 (Sum.inr C5)) = bbA := by
    refine State.ext (funext fun σ => ?_) (funext fun a => ?_) ?_ ?_ ?_
    · cases σ <;> rfl
    · cases a <;> rfl
    · rfl
    · rfl
    · rfl
  rw [hstep, hxEq]

theorem bb0_slideRev : reversibleAtW bb0 (Move.tabToTab C3 (Sum.inr H4)) :=
  ⟨bbA, [Move.tabToTab C3 (Sum.inr D4)], bb0_slide, run_one bbA_slideback⟩

theorem bbA_slidebackRev : reversibleAtW bbA (Move.tabToTab C3 (Sum.inr D4)) :=
  ⟨bb0, [Move.tabToTab C3 (Sum.inr H4)], bbA_slideback, run_one bb0_slide⟩

theorem bbA_raiseRev : reversibleAtW bbA (Move.tabToFound D4) :=
  ⟨bb1, [Move.foundToTab D4 (Sum.inr C5)], bbA_raise, run_one bb1_pull⟩

theorem bb1_pullRev : reversibleAtW bb1 (Move.foundToTab D4 (Sum.inr C5)) :=
  ⟨bbA, [Move.tabToFound D4], bb1_pull, run_one bbA_raise⟩

theorem bbFwd : ShufflePlayW bb0
    [Move.tabToTab C3 (Sum.inr H4), Move.tabToFound D4] bb1 :=
  .cons bb0_slideRev bb0_slide (.cons bbA_raiseRev bbA_raise (.nil bb1))

theorem bbBwd : ShufflePlayW bb1
    [Move.foundToTab D4 (Sum.inr C5), Move.tabToTab C3 (Sum.inr D4)] bb0 :=
  .cons bb1_pullRev bb1_pull (.cons bbA_slidebackRev bbA_slideback (.nil bb0))

/-- The fork-class cert: the elevated member rides round-trip from
the fork board (witness each way). -/
theorem bb_class : sameOrbitSetoid.r bb0 bb1 :=
  ⟨[Move.foundToTab D4 (Sum.inr C5), Move.tabToTab C3 (Sum.inr D4)], bbBwd,
    [Move.tabToTab C3 (Sum.inr H4), Move.tabToFound D4], bbFwd⟩

/-- **THE BARE-LIFT COMMIT, THEOREM-GRADE AT THE ELEVATED MEMBER**
— the census's §2 pin itself (no monotone: the hidden total is flat
here; the king-anchored refill pin is the ONLY grader), instantiated
with kernel-folded premises. -/
theorem bb1_bareCommit : irreversibleAt bb1 (Move.tabToFound S4) :=
  bare_lift_irreversibleAt bb1_bareStep
    (show bb1.pileOfTop S4 = some Anchor.p3 from rfl)
    (show chop (bb1.piles Anchor.p3).faceUp = [] from rfl)
    (show (bb1.piles Anchor.p3).hidden = [] from rfl)
    (by decide)

/-- ...and the same species in the direct read at the slab-side fork
board (the pre-commit twin-read row for the duplicate). -/
theorem bb0_bareCommit : irreversibleAt bb0 (Move.tabToFound S4) :=
  bare_lift_irreversibleAt bb0_bareStep
    (show bb0.pileOfTop S4 = some Anchor.p3 from rfl)
    (show chop (bb0.piles Anchor.p3).faceUp = [] from rfl)
    (show (bb0.piles Anchor.p3).hidden = [] from rfl)
    (by decide)

private theorem bbSA_raise :
    State.step bb0SA (Move.tabToFound D4) = some bb1S := by
  have hxEq : stepD bb0SA (Move.tabToFound D4) = bb1S := by
    refine State.ext (funext fun σ => ?_) (funext fun a => ?_) ?_ ?_ ?_
    · cases σ <;> rfl
    · cases a <;> rfl
    · rfl
    · rfl
    · rfl
  show State.step bb0SA (Move.tabToFound D4) = some bb1S
  rw [show State.step bb0SA (Move.tabToFound D4)
      = some (stepD bb0SA (Move.tabToFound D4)) from rfl, hxEq]

private theorem bbSAS_slideback :
    State.step bbSAS (Move.tabToTab C3 (Sum.inr D4)) = some bb0S := by
  have hxEq : stepD bbSAS (Move.tabToTab C3 (Sum.inr D4)) = bb0S := by
    refine State.ext (funext fun σ => ?_) (funext fun a => ?_) ?_ ?_ ?_
    · cases σ <;> rfl
    · cases a <;> rfl
    · rfl
    · rfl
    · rfl
  show State.step bbSAS (Move.tabToTab C3 (Sum.inr D4)) = some bb0S
  rw [show State.step bbSAS (Move.tabToTab C3 (Sum.inr D4))
      = some (stepD bbSAS (Move.tabToTab C3 (Sum.inr D4))) from rfl, hxEq]

private theorem bbSAS_raise :
    State.step bbSAS (Move.tabToFound D4) = some bb1S := by
  have hxEq : stepD bbSAS (Move.tabToFound D4) = bb1S := by
    refine State.ext (funext fun σ => ?_) (funext fun a => ?_) ?_ ?_ ?_
    · cases σ <;> rfl
    · cases a <;> rfl
    · rfl
    · rfl
    · rfl
  show State.step bbSAS (Move.tabToFound D4) = some bb1S
  rw [show State.step bbSAS (Move.tabToFound D4)
      = some (stepD bbSAS (Move.tabToFound D4)) from rfl, hxEq]

private theorem bb0SA_slideback :
    State.step bb0SA (Move.tabToTab C3 (Sum.inr D4)) = some bb0S := by
  have hxEq : stepD bb0SA (Move.tabToTab C3 (Sum.inr D4)) = bb0S := by
    refine State.ext (funext fun σ => ?_) (funext fun a => ?_) ?_ ?_ ?_
    · cases σ <;> rfl
    · cases a <;> rfl
    · rfl
    · rfl
    · rfl
  show State.step bb0SA (Move.tabToTab C3 (Sum.inr D4)) = some bb0S
  rw [show State.step bb0SA (Move.tabToTab C3 (Sum.inr D4))
      = some (stepD bb0SA (Move.tabToTab C3 (Sum.inr D4))) from rfl, hxEq]

theorem bb0S_slideRev : reversibleAtW bb0S (Move.tabToTab C3 (Sum.inr H4)) :=
  ⟨bb0SA, [Move.tabToTab C3 (Sum.inr D4)], bb0S_slide, run_one bb0SA_slideback⟩

theorem bb0SA_slidebackRev : reversibleAtW bb0SA (Move.tabToTab C3 (Sum.inr D4)) :=
  ⟨bb0S, [Move.tabToTab C3 (Sum.inr H4)], bb0SA_slideback, run_one bb0S_slide⟩

/-- **THE MIDTHREAD COALESCENCE** — the bridge's first midstate and the
σ-journey's post-pull state are THE SAME STATE: the bare-S4 raise
commutes past the cover hop, and the D4 raise-then-pull cancels, so
`bb0SA = bbSAS` (this is why every bridge return-play is ONE-LEG:
each midstate's mirror exists straight back). -/
private theorem bb0SA_eq : bb0SA = bbSAS := by
  refine State.ext (funext fun σ => ?_) (funext fun a => ?_) ?_ ?_ ?_
  · cases σ <;> rfl
  · cases a <;> rfl
  · rfl
  · rfl
  · rfl

theorem bb0SA_raiseRev : reversibleAtW bb0SA (Move.tabToFound D4) :=
  ⟨bb1S, [Move.foundToTab D4 (Sum.inr C5)], bbSA_raise,
    run_one (by rw [bb0SA_eq]; exact bb1S_pull)⟩

theorem bb1S_pullRev : reversibleAtW bb1S (Move.foundToTab D4 (Sum.inr C5)) :=
  ⟨bbSAS, [Move.tabToFound D4], bb1S_pull, run_one bbSAS_raise⟩

theorem bbSAS_slidebackRev : reversibleAtW bbSAS (Move.tabToTab C3 (Sum.inr D4)) :=
  ⟨bb0S, [Move.tabToTab C3 (Sum.inr H4)], bbSAS_slideback,
    run_one (by rw [← bb0SA_eq]; exact bb0S_slide)⟩

theorem bbSFwd : ShufflePlayW bb0S
    [Move.tabToTab C3 (Sum.inr H4), Move.tabToFound D4] bb1S :=
  .cons bb0S_slideRev bb0S_slide (.cons bb0SA_raiseRev bbSA_raise (.nil bb1S))

theorem bbSBwd : ShufflePlayW bb1S
    [Move.foundToTab D4 (Sum.inr C5), Move.tabToTab C3 (Sum.inr D4)] bb0S :=
  .cons bb1S_pullRev bb1S_pull (.cons bbSAS_slidebackRev bbSAS_slideback (.nil bb0S))

/-- **FIG-1 TARGET MATCH** — the slab-side commit's successor and the
elevated-side commit's successor are class mates: the elevation legs
commute with the bare raise (disjoint cells), the re-bridge exhibited
pull-then-slide. -/
theorem bb0S_class : sameOrbitSetoid.r bb0S bb1S :=
  ⟨[Move.foundToTab D4 (Sum.inr C5), Move.tabToTab C3 (Sum.inr D4)], bbSBwd,
    [Move.tabToTab C3 (Sum.inr H4), Move.tabToFound D4], bbSFwd⟩

/-- **FIG-1(a) VERDICT: DUPLICATE-FOUND, ASSEMBLED** — the bare-lift
commit at the twin-elevated member has its slab duplicate at the
fork board `bb0`: the same raise, the target class matched by the
exhibited bridge, the duplicate's OWN commit grade read through the
glue row from the class links alone (second on-probe glue
consumption), cross-checked against the direct bare-lift grading. -/
theorem bb1_dup :
    ∃ (u₀ : State) (m₀ : Move) (v₀ : State),
      sameOrbitSetoid.r bb0 u₀ ∧
      familyBelowFrontier u₀ H4 ∧
      State.step u₀ m₀ = some v₀ ∧
      irreversibleAt u₀ m₀ ∧
      sameOrbitSetoid.r v₀ bb1S :=
  ⟨bb0, Move.tabToFound S4, bb0S, bb0_refl, bb0_slab, bb0_bareStep,
    fork_lowbridge_commitGlue bb_class bb0_refl bb1_bareStep bb1_bareCommit
      bb0_bareStep bb0S_class,
    bb0S_class⟩

/-- **FIG-1(b): THE RUNG-BRACKET DATAPOINT** — the raise row's
surviving open step (`rungAt d c.suit = rungAt u c.suit`) held on
this duplicate: the commit suit's rung is IDENTICAL at the elevated
member and the slab duplicate (the elevation moved only the PAIR
suit, whose contrast is recorded beside it). -/
theorem bb_bracket :
    rungAt bb1 Suit.spade = 3 ∧ rungAt bb0 Suit.spade = 3 ∧
      bb1.nextUp S4 = true ∧ bb0.nextUp S4 = true ∧
        rungAt bb1 Suit.diamond = 4 ∧ rungAt bb0 Suit.diamond = 3 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **FIG-1 CENSUS BONUS** — the sibling's witness raise census read
at this economy's own elevation leg: the cover hop exposes the
twin's under-seat `C5`, and the twin raise is the UNDER-ARM of the
census dichotomy, with the exposed `C5` exactly as the census claims:
opposite color, the raised index + 1, UNFOUNDED, census moved only
in the two named cells (decided). -/
theorem bb_raiseCensus :
    chop (bbA.piles Anchor.p1).faceUp ≠ [] ∧
      hostCensus bbA D4.suit.color D4.rank.toIdx
        = hostCensus bb1 D4.suit.color D4.rank.toIdx + 1 ∧
      ∃ z, bb1.topOf Anchor.p1 = some z ∧
        z.suit.color ≠ D4.suit.color ∧ z.rank.toIdx = D4.rank.toIdx + 1 ∧
          z ∉ bbA.found z.suit ∧
          hostCensus bb1 z.suit.color z.rank.toIdx
            = hostCensus bbA z.suit.color z.rank.toIdx + 1 ∧
          ∀ col i, (col ≠ D4.suit.color ∨ i ≠ D4.rank.toIdx) →
            (col ≠ z.suit.color ∨ i ≠ z.rank.toIdx) →
            hostCensus bb1 col i = hostCensus bbA col i := by
  have hwfA : bbA.WF := step_wf bb0_wf bb0_slide
  rcases census_tabToFound_witness hwfA bbA_raiseRev bbA_raise
      (show bbA.pileOfTop D4 = some Anchor.p1 from rfl) with
    ⟨hchopne, hdelta, z, htopz, hcol, hrank, hunf, hzdelta, hothers⟩ |
    ⟨hchop, -, -, -, -⟩
  · exact ⟨hchopne, hdelta, z, htopz, hcol, hrank, hunf, hzdelta, hothers⟩
  · exact absurd hchop (by decide)

/-! ## §10. ROUND 2, FAMILY 2 — THE CURSOR BOARDS (`wb0`)

The waste rows' surviving cursor face.  Economy: rungs ♥ 3 / ♦ 3 /
♠ 2 / ♣ 0 — the THIRD rung makes `S3` hot; it sits at the WASTE HEAD
of a NONTRIVIAL waste (length 4 > drawStep 3, offset 4 % 3 ≠ 0) over
an EMPTY stock — so the board's draws are the two LEGS OF A WITNESS
LOOP: the recycle-deal peels three cards into the waste, and the
CLIPPED second deal restores the arrangement exactly (the empty-stock
cursor algebra, both legs `reversibleAtW` — round 2's own loop rows).
The elevation hops the C3 cover and raises the twin as usual; the
waste letters commit at both readings (`cycleCount` strictly drops,
never rises), and the falsification hunt asks: can a SHIFTED cursor
carry the re-fire? -/

private def hmapwb : Suit → Nat
  | .heart => 3 | .diamond => 3 | .spade => 2 | .club => 0

private def wb0 : State where
  found := fun s => s.upCards.take (hmapwb s)
  piles := fun a => match a with
    | .p0 => ⟨[], []⟩
    | .p1 => ⟨[crd .club .six, crd .club .seven, crd .club .eight,
               crd .club .nine, crd .club .ten, crd .club .jack,
               crd .club .queen, crd .club .king, crd .club .two,
               crd .club .four, crd .club .ace],
              [C5, D4, C3]⟩
    | .p2 => ⟨[], [S5, H4]⟩
    | .p3 => ⟨[], []⟩
    | .p4 => ⟨[crd .spade .eight, crd .spade .nine, crd .spade .ten,
               crd .spade .jack, crd .spade .queen, crd .spade .king],
              []⟩
    | .p5 => ⟨[crd .heart .five, crd .heart .six, crd .heart .seven,
               crd .heart .eight, crd .heart .nine, crd .heart .ten,
               crd .heart .jack, crd .heart .queen, crd .heart .king],
              []⟩
    | .p6 => ⟨[crd .diamond .five, crd .diamond .six, crd .diamond .seven,
               crd .diamond .eight, crd .diamond .nine, crd .diamond .ten,
               crd .diamond .jack, crd .diamond .queen, crd .diamond .king],
              []⟩
  stock := []
  waste := [S3, crd .spade .four, crd .spade .six, crd .spade .seven]
  drawStep := 3

private theorem wb0_wf_found : ∀ s : Suit, ∃ n, wb0.found s = s.upCards.take n := by
  intro s
  cases s with
  | spade => exact ⟨2, rfl⟩
  | heart => exact ⟨3, rfl⟩
  | diamond => exact ⟨3, rfl⟩
  | club => exact ⟨0, rfl⟩

private theorem wb0_wf_runs : ∀ a : Anchor, runOK (wb0.piles a).faceUp = true := by
  intro a
  cases a <;> rfl

private theorem wb0_wf_count : ∀ c ∈ Card.universe, wb0.cardCount c = 1 := by
  intro c _
  rcases c with ⟨s, r⟩
  cases s <;> cases r <;> decide

private theorem wb0_wf : wb0.WF :=
  ⟨wb0_wf_found, wb0_wf_runs, wb0_wf_count, by decide⟩

theorem wb0_forkSB : forkStateSB wb0 = true := by decide

theorem wb0_witness : forkWitnessSB wb0 = some H4 := by rfl

theorem wb0_forkWitness : ForkWitness wb0 H4 :=
  forkWitnessSB_sound wb0_wf wb0_witness

theorem wb0_refl : sameOrbitSetoid.r wb0 wb0 :=
  sameOrbitSetoid.iseqv.1 wb0

theorem wb0_slab : familyBelowFrontier wb0 H4 := by
  unfold familyBelowFrontier
  decide

theorem wb_zone :
    wb0.stock = [] ∧ wb0.waste = [S3, crd .spade .four, crd .spade .six,
      crd .spade .seven] ∧ wb0.drawStep = 3 ∧
      (wb0.waste.length % wb0.drawStep = 1 ∧ 3 < wb0.waste.length) :=
  ⟨rfl, rfl, rfl, by decide⟩

/-- **THE CURSOR LOOP** — the two zone legs of the empty-stock cycle
at a LONG waste: the first draw recycles the waste (reversed) and
deals three of the four cards back (midstate: stock = [S3], waste
head = the COLD `S4`), the CLIPPED second draw deals the last card
and restores the arrangement EXACTLY.  Both legs are one-step
reversible by each other — the witness-grade draws the waste rows'
replays ride. -/
private def wbW : State := stepD wb0 Move.draw

theorem wb0_draw : State.step wb0 Move.draw = some wbW := by rfl

theorem wbW_draw : State.step wbW Move.draw = some wb0 := by
  have hxEq : stepD wbW Move.draw = wb0 := by
    refine State.ext (funext fun σ => ?_) (funext fun a => ?_) ?_ ?_ ?_
    · cases σ <;> rfl
    · cases a <;> rfl
    · rfl
    · rfl
    · rfl
  show State.step wbW Move.draw = some wb0
  rw [show State.step wbW Move.draw = some (stepD wbW Move.draw) from rfl, hxEq]

theorem wbW_zone :
    wbW.stock = [S3] ∧ wbW.waste = [crd .spade .four, crd .spade .six,
      crd .spade .seven] ∧ wbW.piles = wb0.piles :=
  ⟨rfl, rfl, stepDraw_piles wb0_draw⟩

theorem wb0_drawRev : reversibleAtW wb0 Move.draw :=
  ⟨wbW, [Move.draw], wb0_draw, run_one wbW_draw⟩

theorem wbW_drawRev : reversibleAtW wbW Move.draw :=
  ⟨wb0, [Move.draw], wbW_draw, run_one wb0_draw⟩

/-- **THE LOOP-CLASS DRAWS NEVER COMMIT** — at every state of the
zone orbit the draws are the loop legs (the never-commit pattern
read off the witnesses): phase (B) armor for the draw row. -/
theorem wb0_drawNotCommit : ¬ irreversibleAt wb0 Move.draw := by
  intro hiv
  obtain ⟨s₁, play, hs, hr⟩ := wb0_drawRev
  exact absurd hr (hiv s₁ play hs)

theorem wbW_drawNotCommit : ¬ irreversibleAt wbW Move.draw := by
  intro hiv
  obtain ⟨s₁, play, hs, hr⟩ := wbW_drawRev
  exact absurd hr (hiv s₁ play hs)

/-- **THE SHIFTED-CURSOR FALSIFICATION**: at the midstate the hot
`S3` is IN THE STOCK and the waste head is the COLD `S4` — the
committed waste letter's guard refuses the re-fire outright
(kernel-decided `none`), so a SHIFTED cursor cannot carry the
duplicate. -/
theorem wbW_noFire :
    State.step wbW (Move.wasteToFound S3) = none ∧
      State.step wbW (Move.wasteToTab S3 (Sum.inr H4)) = none :=
  ⟨rfl, rfl⟩

/-- **THE ELEVATION**, unchanged from the r=3 mold, with the zone
recorded as untouched (board legs write no zone cell). -/
private def wbA : State := stepD wb0 (Move.tabToTab C3 (Sum.inr H4))
private def wbE : State := stepD wbA (Move.tabToFound D4)
private def wbES : State := stepD wbE (Move.wasteToFound S3)
private def wb0S : State := stepD wb0 (Move.wasteToFound S3)
private def wb0SA : State := stepD wb0S (Move.tabToTab C3 (Sum.inr H4))

theorem wb0_slide : State.step wb0 (Move.tabToTab C3 (Sum.inr H4)) = some wbA := by rfl
theorem wbA_raise : State.step wbA (Move.tabToFound D4) = some wbE := by rfl
theorem wbE_wstep : State.step wbE (Move.wasteToFound S3) = some wbES := by rfl
theorem wb0_wstep : State.step wb0 (Move.wasteToFound S3) = some wb0S := by rfl
theorem wb0S_slide : State.step wb0S (Move.tabToTab C3 (Sum.inr H4)) = some wb0SA := by rfl

theorem wbE_zone : wbE.stock = [] ∧ wbE.waste = wb0.waste :=
  ⟨rfl, rfl⟩

private theorem wbA_slideback :
    State.step wbA (Move.tabToTab C3 (Sum.inr D4)) = some wb0 := by
  have hstep : State.step wbA (Move.tabToTab C3 (Sum.inr D4)) =
      some (stepD wbA (Move.tabToTab C3 (Sum.inr D4))) := by rfl
  have hxEq : stepD wbA (Move.tabToTab C3 (Sum.inr D4)) = wb0 := by
    refine State.ext (funext fun σ => ?_) (funext fun a => ?_) ?_ ?_ ?_
    · cases σ <;> rfl
    · cases a <;> rfl
    · rfl
    · rfl
    · rfl
  rw [hstep, hxEq]

private theorem wbE_pull :
    State.step wbE (Move.foundToTab D4 (Sum.inr C5)) = some wbA := by
  have hstep : State.step wbE (Move.foundToTab D4 (Sum.inr C5)) =
      some (stepD wbE (Move.foundToTab D4 (Sum.inr C5))) := by rfl
  have hxEq : stepD wbE (Move.foundToTab D4 (Sum.inr C5)) = wbA := by
    refine State.ext (funext fun σ => ?_) (funext fun a => ?_) ?_ ?_ ?_
    · cases σ <;> rfl
    · cases a <;> rfl
    · rfl
    · rfl
    · rfl
  rw [hstep, hxEq]

theorem wb0_slideRev : reversibleAtW wb0 (Move.tabToTab C3 (Sum.inr H4)) :=
  ⟨wbA, [Move.tabToTab C3 (Sum.inr D4)], wb0_slide, run_one wbA_slideback⟩

theorem wbA_slidebackRev : reversibleAtW wbA (Move.tabToTab C3 (Sum.inr D4)) :=
  ⟨wb0, [Move.tabToTab C3 (Sum.inr H4)], wbA_slideback, run_one wb0_slide⟩

theorem wbA_raiseRev : reversibleAtW wbA (Move.tabToFound D4) :=
  ⟨wbE, [Move.foundToTab D4 (Sum.inr C5)], wbA_raise, run_one wbE_pull⟩

theorem wbE_pullRev : reversibleAtW wbE (Move.foundToTab D4 (Sum.inr C5)) :=
  ⟨wbA, [Move.tabToFound D4], wbE_pull, run_one wbA_raise⟩

theorem wbFwd : ShufflePlayW wb0
    [Move.tabToTab C3 (Sum.inr H4), Move.tabToFound D4] wbE :=
  .cons wb0_slideRev wb0_slide (.cons wbA_raiseRev wbA_raise (.nil wbE))

theorem wbBwd : ShufflePlayW wbE
    [Move.foundToTab D4 (Sum.inr C5), Move.tabToTab C3 (Sum.inr D4)] wb0 :=
  .cons wbE_pullRev wbE_pull (.cons wbA_slidebackRev wbA_slideback (.nil wb0))

theorem wb_class : sameOrbitSetoid.r wb0 wbE :=
  ⟨[Move.foundToTab D4 (Sum.inr C5), Move.tabToTab C3 (Sum.inr D4)], wbBwd,
    [Move.tabToTab C3 (Sum.inr H4), Move.tabToFound D4], wbFwd⟩

/-- **FIG-2(a): THE WASTE-COMMITS, THEOREM-GRADE** — the `cycleCount`
monotone (strict drop at the waste letters, never a rise anywhere)
grades both readings: at the elevated member and at the fork board. -/
theorem wbE_commit : irreversibleAt wbE (Move.wasteToFound S3) :=
  irr_of_desc cycleCount (fun s m s' h => cycleCount_step h) wbE_wstep
    (by have := cycleCount_step_wasteToFound wbE_wstep; omega)

theorem wb0_commit : irreversibleAt wb0 (Move.wasteToFound S3) :=
  irr_of_desc cycleCount (fun s m s' h => cycleCount_step h) wb0_wstep
    (by have := cycleCount_step_wasteToFound wb0_wstep; omega)

/-- **FIG-2 TARGET BRIDGE** — the elevation legs re-fire at the
committed boards (the waste letter touched only the zone and the
spade foundation — disjoint from the board cells), the re-bridge
exhibited slide-then-raise with mirrored returns. -/
private theorem wbSA_raise :
    State.step wb0SA (Move.tabToFound D4) = some wbES := by
  have hstep : State.step wb0SA (Move.tabToFound D4) =
      some (stepD wb0SA (Move.tabToFound D4)) := by rfl
  have hxEq : stepD wb0SA (Move.tabToFound D4) = wbES := by
    refine State.ext (funext fun σ => ?_) (funext fun a => ?_) ?_ ?_ ?_
    · cases σ <;> rfl
    · cases a <;> rfl
    · rfl
    · rfl
    · rfl
  rw [hstep, hxEq]

private theorem wbES_pull :
    State.step wbES (Move.foundToTab D4 (Sum.inr C5)) = some wb0SA := by
  have hstep : State.step wbES (Move.foundToTab D4 (Sum.inr C5)) =
      some (stepD wbES (Move.foundToTab D4 (Sum.inr C5))) := by rfl
  have hxEq : stepD wbES (Move.foundToTab D4 (Sum.inr C5)) = wb0SA := by
    refine State.ext (funext fun σ => ?_) (funext fun a => ?_) ?_ ?_ ?_
    · cases σ <;> rfl
    · cases a <;> rfl
    · rfl
    · rfl
    · rfl
  rw [hstep, hxEq]

private theorem wb0SA_slideback :
    State.step wb0SA (Move.tabToTab C3 (Sum.inr D4)) = some wb0S := by
  have hstep : State.step wb0SA (Move.tabToTab C3 (Sum.inr D4)) =
      some (stepD wb0SA (Move.tabToTab C3 (Sum.inr D4))) := by rfl
  have hxEq : stepD wb0SA (Move.tabToTab C3 (Sum.inr D4)) = wb0S := by
    refine State.ext (funext fun σ => ?_) (funext fun a => ?_) ?_ ?_ ?_
    · cases σ <;> rfl
    · cases a <;> rfl
    · rfl
    · rfl
    · rfl
  rw [hstep, hxEq]

private theorem wbES_raiseBack :
    State.step wb0SA (Move.tabToFound D4) = some wbES := wbSA_raise

theorem wb0S_slideRev : reversibleAtW wb0S (Move.tabToTab C3 (Sum.inr H4)) :=
  ⟨wb0SA, [Move.tabToTab C3 (Sum.inr D4)], wb0S_slide, run_one wb0SA_slideback⟩

theorem wb0SA_slidebackRev : reversibleAtW wb0SA (Move.tabToTab C3 (Sum.inr D4)) :=
  ⟨wb0S, [Move.tabToTab C3 (Sum.inr H4)], wb0SA_slideback, run_one wb0S_slide⟩

theorem wb0SA_raiseRev : reversibleAtW wb0SA (Move.tabToFound D4) :=
  ⟨wbES, [Move.foundToTab D4 (Sum.inr C5)], wbSA_raise, run_one wbES_pull⟩

theorem wbES_pullRev : reversibleAtW wbES (Move.foundToTab D4 (Sum.inr C5)) :=
  ⟨wb0SA, [Move.tabToFound D4], wbES_pull, run_one wbSA_raise⟩

theorem wbSFwd : ShufflePlayW wb0S
    [Move.tabToTab C3 (Sum.inr H4), Move.tabToFound D4] wbES :=
  .cons wb0S_slideRev wb0S_slide (.cons wb0SA_raiseRev wbSA_raise (.nil wbES))

theorem wbSBwd : ShufflePlayW wbES
    [Move.foundToTab D4 (Sum.inr C5), Move.tabToTab C3 (Sum.inr D4)] wb0S :=
  .cons wbES_pullRev wbES_pull (.cons wb0SA_slidebackRev wb0SA_slideback (.nil wb0S))

theorem wb0S_class : sameOrbitSetoid.r wb0S wbES :=
  ⟨[Move.foundToTab D4 (Sum.inr C5), Move.tabToTab C3 (Sum.inr D4)], wbSBwd,
    [Move.tabToTab C3 (Sum.inr H4), Move.tabToFound D4], wbSFwd⟩

/-- **FIG-2(a) VERDICT: DUPLICATE-FOUND, ASSEMBLED** — the
waste-letter commit at the twin-elevated member; the duplicate at the
fork board: SAME move, SAME cursor (the zone recorded identical at
the two commit sites — the board legs never wrote a zone cell),
target class matched by the exhibited re-bridge, the duplicate's
grade through the glue row from the class links alone, cross-checked
against the direct cycleCount grading. -/
theorem wb1_dup :
    ∃ (u₀ : State) (m₀ : Move) (v₀ : State),
      sameOrbitSetoid.r wb0 u₀ ∧
      familyBelowFrontier u₀ H4 ∧
      State.step u₀ m₀ = some v₀ ∧
      irreversibleAt u₀ m₀ ∧
      sameOrbitSetoid.r v₀ wbES :=
  ⟨wb0, Move.wasteToFound S3, wb0S, wb0_refl, wb0_slab, wb0_wstep,
    fork_lowbridge_commitGlue wb_class wb0_refl wbE_wstep wbE_commit
      wb0_wstep wb0S_class,
    wb0S_class⟩

/-- **FIG-2 CURSOR DATAPOINT** — the cursors at the two commit sites
are IDENTICAL (the midstate's shifted cursor is the one site where
the guard refuses the move outright, `wbW_noFire` above): the
duplicate's availability at this board rode the cursor coincidence,
which the class supplied because the zone orbit commutes with the
board legs. -/
theorem wb_cursorCoincidence :
    wbE.waste = wb0.waste ∧ wbE.stock = wb0.stock ∧
      wb0S.waste = [crd .spade .four, crd .spade .six, crd .spade .seven] :=
  ⟨rfl, rfl, rfl⟩

/-- **FIG-2/3 MIXTURE ROW** — the zone LOOP COMMUTES over the
elevation: the same two draw legs are witnesses at the elevated
member, returning it exactly — the interleaved replays of part (B)
exist and stay reversible on BOTH sides; the class carries the loop
equally on the slab side and the elevated side. -/
private def wbEW : State := stepD wbE Move.draw

theorem wbE_draw : State.step wbE Move.draw = some wbEW := by rfl

theorem wbEW_draw : State.step wbEW Move.draw = some wbE := by
  have hxEq : stepD wbEW Move.draw = wbE := by
    refine State.ext (funext fun σ => ?_) (funext fun a => ?_) ?_ ?_ ?_
    · cases σ <;> rfl
    · cases a <;> rfl
    · rfl
    · rfl
    · rfl
  show State.step wbEW Move.draw = some wbE
  rw [show State.step wbEW Move.draw = some (stepD wbEW Move.draw) from rfl, hxEq]

theorem wbE_drawRev : reversibleAtW wbE Move.draw :=
  ⟨wbEW, [Move.draw], wbE_draw, run_one wbEW_draw⟩

theorem wbEW_drawRev : reversibleAtW wbEW Move.draw :=
  ⟨wbE, [Move.draw], wbEW_draw, run_one wbE_draw⟩

theorem wbE_loopClass :
    sameOrbitSetoid.r wbE wbEW ∧
      ¬ irreversibleAt wbE Move.draw ∧ ¬ irreversibleAt wbEW Move.draw :=
  ⟨⟨[Move.draw], (by
      show ShufflePlayW wbEW [Move.draw] wbE
      exact .cons wbEW_drawRev wbEW_draw (.nil wbE)),
    [Move.draw], (by
      show ShufflePlayW wbE [Move.draw] wbEW
      exact .cons wbE_drawRev wbE_draw (.nil wbEW))⟩,
    by
      intro hiv
      obtain ⟨s₁, play, hs, hr⟩ := wbE_drawRev
      exact absurd hr (hiv s₁ play hs),
    by
      intro hiv
      obtain ⟨s₁, play, hs, hr⟩ := wbEW_drawRev
      exact absurd hr (hiv s₁ play hs)⟩

/-! ## §11. ROUND 2, FAMILY 3 — THE PHASE BOARDS (part-(B) armor)

Draw commits and witness draws occupy DISJOINT zone regimes at the
r=3 economies, assembled from both sides:

* the PRISTINE regime (`lb0`-economy, round 1): the stock carries
  one card over an empty waste; the draw commits at both readings
  (`lb0_drawCommit`, `lb1_drawCommit`, Phase's pristine row), and
  the committed target EXITS the origin class outright (the first
  on-probe consumption of LowSlab's own `commit_exits_class`) — a
  "pure-phase" class-match across the commit cannot even form;
  the post-commit side's own draws are Phase's selfRecycle
  identity-legs (`lb0D`), provably never commits.
* the LOOP regime (`wb0`-economy, §10): the long waste over an
  empty stock; every draw of the zone orbit is a reversible loop
  leg (`wb0`/`wbW`/`wbE`/`wbEW` — provably never commits at all
  four readings).

The interleave arm of part (B) is thereby armored at both regimes:
the falsification shapes tried — (i) pristine-commit target matched
to the origin class by phase alone: barred by the exit row;
(ii) loop-class draws as commits: barred by the loop witnesses;
(iii) mixtures: the zone orbits commute over the board legs
(`wbE_loopClass`), so no member of a loop class is ever a
stock-nonempty/waste-empty pristine state — the regimes are
state-disjoint. -/

theorem lb0D_selfRecycle : reversibleAtW lb0D Move.draw :=
  draw_reversible_selfRecycleW (by rfl) (by decide) (by decide)

theorem lb0D_drawNotCommit : ¬ irreversibleAt lb0D Move.draw := by
  intro hiv
  obtain ⟨s₁, play, hs, hr⟩ := lb0D_selfRecycle
  exact absurd hr (hiv s₁ play hs)

/-- The committed pristine draw EXITS its own class: the pure-phase
match cannot form across a draw commit. -/
theorem lb0_phaseExit : ¬ sameOrbitSetoid.r lb0 lb0D :=
  commit_exits_class lb0_drawStep lb0_drawCommit

theorem r2_phaseArmor :
    ¬ irreversibleAt lb0D Move.draw ∧
      ¬ irreversibleAt wb0 Move.draw ∧ ¬ irreversibleAt wbW Move.draw ∧
        ¬ sameOrbitSetoid.r lb0 lb0D ∧
          irreversibleAt lb0 Move.draw ∧
            irreversibleAt wbE (Move.wasteToFound S3) :=
  ⟨lb0D_drawNotCommit, wb0_drawNotCommit, wbW_drawNotCommit, lb0_phaseExit,
    lb0_drawCommit, wbE_commit⟩

/-! ## §12. ROUND 2, FAMILY 4 — BOOTSTRAP STRESS

### 12(a) The twin-blind pair — the cell census cannot name the twin

`tb0` is `lb0` with the twin roles SWAPPED: the live member `H4`
sits covered in the tower (`[C5, H4, S3]`), the covered twin `D4`
tops the seat pile (`[S5, D4]`).  The (red, three-index) cell census
is IDENTICAL at both boards — ONE top either way — while the TWIN
holding that cell differs: `top_census`'s surviving card-level
bootstrap is irreducible to cell data, on record. -/

private def tb0 : State where
  found := fun s => s.upCards.take (hmaplb s)
  piles := fun a => match a with
    | .p0 => ⟨[], []⟩
    | .p1 => ⟨[crd .club .six, crd .club .seven, crd .club .eight,
               crd .club .nine, crd .club .ten, crd .club .jack,
               crd .club .queen, crd .club .king, crd .club .three,
               crd .club .two, crd .club .four, crd .club .ace],
              [C5, H4, S3]⟩
    | .p2 => ⟨[], [S5, D4]⟩
    | .p3 => ⟨[], [H6]⟩
    | .p4 => ⟨[crd .spade .ace, crd .spade .two, crd .spade .four,
               crd .spade .six, crd .spade .seven, crd .spade .eight,
               crd .spade .nine, crd .spade .ten, crd .spade .jack,
               crd .spade .queen, crd .spade .king], []⟩
    | .p5 => ⟨[crd .heart .seven, crd .heart .eight, crd .heart .nine,
               crd .heart .ten, crd .heart .jack, crd .heart .queen,
               crd .heart .king], []⟩
    | .p6 => ⟨[crd .diamond .five, crd .diamond .six, crd .diamond .seven,
               crd .diamond .eight, crd .diamond .nine, crd .diamond .ten,
               crd .diamond .jack, crd .diamond .queen, crd .diamond .king],
              []⟩
  stock := [H5]
  waste := []
  drawStep := 1

private theorem tb0_wf_count : ∀ c ∈ Card.universe, tb0.cardCount c = 1 := by
  intro c _
  rcases c with ⟨s, r⟩
  cases s <;> cases r <;> decide

private theorem tb0_wf_runs : ∀ a : Anchor, runOK (tb0.piles a).faceUp = true := by
  intro a
  cases a <;> rfl

theorem r2_censusBlind :
    H4.suit.color = D4.suit.color ∧ H4.rank.toIdx = D4.rank.toIdx ∧
      hostCensus lb0 H4.suit.color H4.rank.toIdx = 1 ∧
        hostCensus tb0 H4.suit.color H4.rank.toIdx = 1 ∧
          (lb0.piles Anchor.p2).top = some H4 ∧
            (tb0.piles Anchor.p2).top = some D4 :=
  ⟨by decide, rfl, by decide, by decide, rfl, rfl⟩

/- **12(a) VERDICT — the bootstrap is real content, benignly
exhibited**: the cell (red family, index three) carries ONE top at
both boards — but WHICH twin holds it differs.  A census-only
reduction of `lowslab_top_census`'s card-level bridge is impossible
at decide grade; the twin-separation must ride the one-founding row
(the refinement's own rationale), which is exactly where the LowSlab
route prices it.

### 12(b) The exhumed-host reveal — the loan repaid load-bearing

Economy `xb0`: the twin tower and live seat as in round 1; p3 hosts
the club-four `C4` over the club deck (head `C6`); p4 hosts the red
five `D5` over `S6`; the diamond foundation sits at three, so its
top `D3` is pull-able.  The chain: PULL `D3` onto `C4` (the
exhumation: a reversible leg, mirror-re-raising); then the
reveal-slide `[C4, D3]` onto `D5` — a commit that strips the
EXHUMED ALONG WITH its host, emptying p3 to the deck (the reveal).
The same slide at the PRE-EXHUMATION member fires WITHOUT the
exhumed cargo — the theorem's rescheduling claim tested where the
loan is load-bearing. -/

private def xb0 : State where
  found := fun s => s.upCards.take (hmaplb s)
  piles := fun a => match a with
    | .p0 => ⟨[], []⟩
    | .p1 => ⟨[], [C5, D4, S3]⟩
    | .p2 => ⟨[], [S5, H4]⟩
    | .p3 => ⟨[crd .club .six, crd .club .seven, crd .club .eight,
               crd .club .nine, crd .club .ten, crd .club .jack,
               crd .club .queen, crd .club .king, crd .club .three,
               crd .club .two, crd .club .ace], [C4]⟩
    | .p4 => ⟨[], [crd .spade .six, D5]⟩
    | .p5 => ⟨[crd .spade .ace, crd .spade .two, crd .spade .four,
               crd .spade .seven, crd .spade .eight, crd .spade .nine,
               crd .spade .ten, crd .spade .jack, crd .spade .queen,
               crd .spade .king], []⟩
    | .p6 => ⟨[crd .heart .five, crd .heart .six, crd .heart .seven,
               crd .heart .eight, crd .heart .nine, crd .heart .ten,
               crd .heart .jack, crd .heart .queen, crd .heart .king,
               crd .diamond .six, crd .diamond .seven, crd .diamond .eight,
               crd .diamond .nine, crd .diamond .ten, crd .diamond .jack,
               crd .diamond .queen], []⟩
  stock := [crd .diamond .king]
  waste := []
  drawStep := 1

private theorem xb0_wf_found : ∀ s : Suit, ∃ n, xb0.found s = s.upCards.take n := by
  intro s
  cases s with
  | spade => exact ⟨0, rfl⟩
  | heart => exact ⟨3, rfl⟩
  | diamond => exact ⟨3, rfl⟩
  | club => exact ⟨0, rfl⟩

private theorem xb0_wf_runs : ∀ a : Anchor, runOK (xb0.piles a).faceUp = true := by
  intro a
  cases a <;> rfl

private theorem xb0_wf_count : ∀ c ∈ Card.universe, xb0.cardCount c = 1 := by
  intro c _
  rcases c with ⟨s, r⟩
  cases s <;> cases r <;> decide

private theorem xb0_wf : xb0.WF :=
  ⟨xb0_wf_found, xb0_wf_runs, xb0_wf_count, by decide⟩

theorem xb0_slab : familyBelowFrontier xb0 H4 := by
  unfold familyBelowFrontier
  decide

theorem xb0_refl : sameOrbitSetoid.r xb0 xb0 :=
  sameOrbitSetoid.iseqv.1 xb0

/-- **THE EXHUMATION LEG** — the diamond top `D3` pulled onto `C4`:
one move, mirror-re-raising (the post-state's diamond row is the
chopped `[A,2]`, so the mirror's own next-up guard fires by the
founded-prefix arithmetic — the promoted `lowslab_pull_wf_undo`'s
route, witnessed on a board). -/
private def xb1 : State := stepD xb0 (Move.foundToTab D3 (Sum.inr C4))
private def xb2 : State := stepD xb1 (Move.tabToTab C4 (Sum.inr D5))
private def xb0R : State := stepD xb0 (Move.tabToTab C4 (Sum.inr D5))

theorem xb_pull : State.step xb0 (Move.foundToTab D3 (Sum.inr C4)) = some xb1 := by rfl

private theorem xb_raiseMirror :
    State.step xb1 (Move.tabToFound D3) = some xb0 := by
  have hstep : State.step xb1 (Move.tabToFound D3) =
      some (stepD xb1 (Move.tabToFound D3)) := by rfl
  have hxEq : stepD xb1 (Move.tabToFound D3) = xb0 := by
    refine State.ext (funext fun σ => ?_) (funext fun a => ?_) ?_ ?_ ?_
    · cases σ <;> rfl
    · cases a <;> rfl
    · rfl
    · rfl
    · rfl
  rw [hstep, hxEq]

theorem xb_pullRev : reversibleAtW xb0 (Move.foundToTab D3 (Sum.inr C4)) :=
  ⟨xb1, [Move.tabToFound D3], xb_pull, run_one xb_raiseMirror⟩

theorem xb_raiseRev : reversibleAtW xb1 (Move.tabToFound D3) :=
  ⟨xb0, [Move.foundToTab D3 (Sum.inr C4)], xb_raiseMirror, run_one xb_pull⟩

theorem xb_class : sameOrbitSetoid.r xb0 xb1 :=
  ⟨[Move.tabToFound D3],
    (.cons xb_raiseRev xb_raiseMirror (.nil xb0)),
    [Move.foundToTab D3 (Sum.inr C4)],
    (.cons xb_pullRev xb_pull (.nil xb1))⟩

/-- The exhumation touched no hidden deck: the reveal's content —
the club deck's head `C6` — is IDENTICAL before and after the pull
(the hidden pin instantiated). -/
theorem xb_revealContent :
    (xb0.piles Anchor.p3).hidden = C6 :: (xb0.piles Anchor.p3).hidden.tail ∧
      (xb1.piles Anchor.p3).hidden = (xb0.piles Anchor.p3).hidden :=
  ⟨rfl, shuffle_hiddenPinned
    ((.cons xb_pullRev xb_pull (.nil xb1)) : ShufflePlayW xb0 _ xb1) Anchor.p3⟩

/-- **FIG-4(b): THE LOAD-BEARING REVEAL** — the slide `[C4, D3]`
strips the exhumed along with its host: p3 empties to the deck,
the head `C6` flips — a reveal-commit, jury-barred and
monotone-graded, at the post-exhumation member. -/
theorem xb1_revealStep :
    State.step xb1 (Move.tabToTab C4 (Sum.inr D5)) = some xb2 := by rfl

theorem xb1_revealJury : ¬ reversibleAtW xb1 (Move.tabToTab C4 (Sum.inr D5)) :=
  journey_tabToTab_never_reveal xb1_revealStep
    (show xb1.pileHolding C4 = some Anchor.p3 from rfl)
    (show below C4 (xb1.piles Anchor.p3).faceUp = [] from rfl)
    (show (xb1.piles Anchor.p3).hidden ≠ [] from by decide)

theorem xb1_revealCommit : irreversibleAt xb1 (Move.tabToTab C4 (Sum.inr D5)) :=
  irr_of_desc hiddenTotal (fun s m s' h => hiddenTotal_step h) xb1_revealStep
    (by decide)

/-- ...and the same slide WITHOUT the exhumed cargo at the base
member — also a reveal-commit (the deck fires the flip either way). -/
theorem xb0_revealStep :
    State.step xb0 (Move.tabToTab C4 (Sum.inr D5)) = some xb0R := by rfl

theorem xb0_revealJury : ¬ reversibleAtW xb0 (Move.tabToTab C4 (Sum.inr D5)) :=
  journey_tabToTab_never_reveal xb0_revealStep
    (show xb0.pileHolding C4 = some Anchor.p3 from rfl)
    (show below C4 (xb0.piles Anchor.p3).faceUp = [] from rfl)
    (show (xb0.piles Anchor.p3).hidden ≠ [] from by decide)

theorem xb0_revealCommit : irreversibleAt xb0 (Move.tabToTab C4 (Sum.inr D5)) :=
  irr_of_desc hiddenTotal (fun s m s' h => hiddenTotal_step h) xb0_revealStep
    (by decide)

/-- **FIG-4(b) TARGET BRIDGE — THE LOAN REPAID** — the two committed
targets join by ONE posterior pull: pull `D3` onto wherever `C4`
landed and the states COALESCE (the pull commutes past the slide,
the exhumed card re-occupying the very seat the run carried).  The
census corollary's language on a board: the excursion issued no
seat the return does not reclaim. -/
private theorem xb0R_pull :
    State.step xb0R (Move.foundToTab D3 (Sum.inr C4)) = some xb2 := by
  have hstep : State.step xb0R (Move.foundToTab D3 (Sum.inr C4)) =
      some (stepD xb0R (Move.foundToTab D3 (Sum.inr C4))) := by rfl
  have hxEq : stepD xb0R (Move.foundToTab D3 (Sum.inr C4)) = xb2 := by
    refine State.ext (funext fun σ => ?_) (funext fun a => ?_) ?_ ?_ ?_
    · cases σ <;> rfl
    · cases a <;> rfl
    · rfl
    · rfl
    · rfl
  rw [hstep, hxEq]

private theorem xb2_raiseMirror :
    State.step xb2 (Move.tabToFound D3) = some xb0R := by
  have hstep : State.step xb2 (Move.tabToFound D3) =
      some (stepD xb2 (Move.tabToFound D3)) := by rfl
  have hxEq : stepD xb2 (Move.tabToFound D3) = xb0R := by
    refine State.ext (funext fun σ => ?_) (funext fun a => ?_) ?_ ?_ ?_
    · cases σ <;> rfl
    · cases a <;> rfl
    · rfl
    · rfl
    · rfl
  rw [hstep, hxEq]

theorem xb0R_pullRev :
    reversibleAtW xb0R (Move.foundToTab D3 (Sum.inr C4)) :=
  ⟨xb2, [Move.tabToFound D3], xb0R_pull, run_one xb2_raiseMirror⟩

theorem xb2_raiseRev : reversibleAtW xb2 (Move.tabToFound D3) :=
  ⟨xb0R, [Move.foundToTab D3 (Sum.inr C4)], xb2_raiseMirror, run_one xb0R_pull⟩

theorem xbR_class : sameOrbitSetoid.r xb0R xb2 :=
  ⟨[Move.tabToFound D3],
    (.cons xb2_raiseRev xb2_raiseMirror (.nil xb0R)),
    [Move.foundToTab D3 (Sum.inr C4)],
    (.cons xb0R_pullRev xb0R_pull (.nil xb2))⟩

/-- **FIG-4(b) VERDICT: DUPLICATE-FOUND, ASSEMBLED — the
rescheduling HELD load-bearing**: the committed reveal at the
post-exhumation member; the duplicate at the pre-exhumation member:
the SAME move, target class joined by the exhibited one-leg
re-bridge, the duplicate's grade through the glue row from the
class links alone (third on-probe glue consumption), cross-checked
against the direct monotone grading. -/
theorem xb1_dup :
    ∃ (u₀ : State) (m₀ : Move) (v₀ : State),
      sameOrbitSetoid.r xb0 u₀ ∧
      familyBelowFrontier u₀ H4 ∧
      State.step u₀ m₀ = some v₀ ∧
      irreversibleAt u₀ m₀ ∧
      sameOrbitSetoid.r v₀ xb2 :=
  ⟨xb0, Move.tabToTab C4 (Sum.inr D5), xb0R, xb0_refl, xb0_slab,
    xb0_revealStep,
    fork_lowbridge_commitGlue xb_class xb0_refl xb1_revealStep
      xb1_revealCommit xb0_revealStep xbR_class,
    xbR_class⟩

/-- **FIG-4(b) CENSUS BONUS** — the sibling's reveal-census row,
verbatim at the exhumed shape: the exposed deck head `C6` takes
over the source seat, and the per-cell ledger exchanges exactly the
consumed host `D5`'s indicator for the revealed `C6`'s (decided). -/
theorem xb_revealCensus :
    xb2.topOf Anchor.p3 = some C6 ∧
      ∀ col i, hostCensus xb2 col i + seatInd (some D5) col i
        = hostCensus xb1 col i + seatInd (some C6) col i := by
  have hwf1 : xb1.WF := step_wf xb0_wf xb_pull
  exact census_tabToTab_reveal hwf1 xb1_revealStep
    (show xb1.pileHolding C4 = some Anchor.p3 from rfl)
    (show xb1.pileOfTop D5 = some Anchor.p4 from rfl)
    (show below C4 (xb1.piles Anchor.p3).faceUp = [] from rfl)
    (show (xb1.piles Anchor.p3).hidden
        = C6 :: [crd .club .seven, crd .club .eight, crd .club .nine,
            crd .club .ten, crd .club .jack, crd .club .queen,
            crd .club .king, crd .club .three, crd .club .two,
            crd .club .ace] from rfl)

/-! ## §13. ROUND 2 — THE VERDICT LEDGER -/

/-- **THE ROUND-2 PROBE LEDGER** — decide-grade:

* FAMILY 1 (bare-lift): the bare hot `S4` commit fires
  theorem-grade at the twin-elevated member AND at the fork board
  (the census's own §2 pin, no monotone needed); the duplicate is
  fully assembled with the rung bracket EQUAL at the two sites
  (the commit suit untouched by the elevation; the pair suit's
  contrast recorded) — verdict DUPLICATE-FOUND, BRACKET HELD.
* FAMILY 2 (cursor): the waste-letter commits at both the
  elevated member and the fork board (cycleCount monotone), the
  zone loop witnesses reversible at all four readings, the
  SHIFTED-cursor site REFUSES the re-fire outright — verdict
  DUPLICATE-FOUND (identical cursors at the commit sites;
  the shift kills the guard, not the class).
* FAMILY 3 (phase): both regimes armored — pristine commits exit
  their class (`commit_exits_class` consumed on-probe), loop-class
  draws provably never commit — verdict SYSTEMATIC FAILURE of the
  pure-phase falsification at every tried shape: the regimes are
  state-disjoint, the interleaves commute.
* FAMILY 4 (bootstrap): the cell census is TWIN-BLIND at matching
  profiles (the card-level bridge is real content, benignly
  exhibited); the exhumed-host reveal has its slab duplicate with
  the loan repaid by a ONE-LEG posterior pull — verdict
  RESCHEDULING HELD, LOAD-BEARING. -/
theorem LowSlabProbeR2_verdicts :
    irreversibleAt bb1 (Move.tabToFound S4) ∧
      irreversibleAt bb0 (Move.tabToFound S4) ∧
        rungAt bb1 Suit.spade = rungAt bb0 Suit.spade ∧
          irreversibleAt wbE (Move.wasteToFound S3) ∧
            ¬ irreversibleAt wb0 Move.draw ∧ ¬ irreversibleAt wbW Move.draw ∧
              State.step wbW (Move.wasteToFound S3) = none ∧
                ¬ sameOrbitSetoid.r lb0 lb0D ∧
                  hostCensus lb0 H4.suit.color H4.rank.toIdx
                    = hostCensus tb0 H4.suit.color H4.rank.toIdx ∧
                    (lb0.piles Anchor.p2).top ≠ (tb0.piles Anchor.p2).top ∧
                      irreversibleAt xb1 (Move.tabToTab C4 (Sum.inr D5)) ∧
                        irreversibleAt xb0 (Move.tabToTab C4 (Sum.inr D5)) ∧
                          (∃ (u₀ : State) (m₀ : Move) (v₀ : State),
                            sameOrbitSetoid.r xb0 u₀ ∧
                              familyBelowFrontier u₀ H4 ∧
                                State.step u₀ m₀ = some v₀ ∧
                                  irreversibleAt u₀ m₀ ∧
                                    sameOrbitSetoid.r v₀ xb2) :=
  ⟨bb1_bareCommit, bb0_bareCommit, rfl, wbE_commit, wb0_drawNotCommit,
    wbW_drawNotCommit, wbW_noFire.1, lb0_phaseExit, by decide, by decide,
    xb1_revealCommit, xb0_revealCommit, xb1_dup⟩

/-! ### The round-2 audit battery -/

#print axioms bb0_forkSB
#print axioms bb0_witness
#print axioms bb0_forkWitness
#print axioms bb0_refl
#print axioms bb0_slab
#print axioms bb0_bare
#print axioms bb0_bareCommit
#print axioms bb1_bareCommit
#print axioms bb0S_class
#print axioms bb1_dup
#print axioms bb_bracket
#print axioms bb_raiseCensus
#print axioms wb0_forkSB
#print axioms wb0_forkWitness
#print axioms wb0_slab
#print axioms wb0_drawRev
#print axioms wbW_drawRev
#print axioms wb0_drawNotCommit
#print axioms wbW_drawNotCommit
#print axioms wbW_noFire
#print axioms wbE_commit
#print axioms wb0_commit
#print axioms wb0S_class
#print axioms wb1_dup
#print axioms wb_cursorCoincidence
#print axioms wbE_loopClass
#print axioms lb0D_selfRecycle
#print axioms lb0D_drawNotCommit
#print axioms lb0_phaseExit
#print axioms r2_phaseArmor
#print axioms r2_censusBlind
#print axioms xb_revealContent
#print axioms xb1_revealJury
#print axioms xb1_revealCommit
#print axioms xb0_revealJury
#print axioms xb0_revealCommit
#print axioms xbR_class
#print axioms xb1_dup
#print axioms xb_revealCensus
#print axioms LowSlabProbeR2_verdicts
