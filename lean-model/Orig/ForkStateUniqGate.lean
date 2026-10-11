import Orig.ForkStateUniq
import Orig.MacroInternal

/-!
# Orig.ForkStateUniqGate — the maximality-transport gate, closed

The gate file the forkState-unique card's §11-L5 residue named: the
G2 maximality-transport head, attacked probe-first per the house
discipline (the probe `probes/ForkUniqProbe.lean` is the evidence
twin of every row here).

**THE PROBE-FIRST VERDICT (decide-grade, oracle-verified).**  The
task's G2 head — *two same-class `forkState`s witnessing the SAME
pair have equal rungs on every non-pair suit, the strict invariant
`rungAt st₁ s = rungAt st₂ s`* — is **REFUTED at theorem grade by a
WF craft**, and with it the assembled in-tree statement of
`forkState_unique` itself (which this file disproves exactly as
stated, at BOTH grades of the corrected cross-bridge `FaceShape`
of 07247ec, all its premises satisfied).  The mechanism the sketch
never priced: the maximality `∀ c, CanRaise st c ↔ c = x` pins
licenses at the FIXED arrangement, but the MACRO CLASS may contain
a flat cargo leg that relocates the witness off a next-up card it
was blocking (the craft: the witness 5♥ sits DIRECTLY ON the
black next-up 6♠; slide it to a fitting top 6♣ — one reversible
`tabToTab` — and 6♠ exposes with its under-seat intact, so the
licensed raise of 6♠ is a reversible journey leg; the successor is
AGAIN a `forkState` of the SAME pair {5♥, 5♦} with the SAME
orientation, one non-pair rung higher).  `FaceShape` between the
two is impossible at either grade: every cargo leg preserves all
rungs (`cargoPath_rungs`, §1 of `Orig.ForkStateUniq`), and the
cross-grade's conjugate composite is net-flat on foundations (its
slide leg is a `tabToTab` whatever card it moves — the §4
loose-shape row `conjugate_endpoint_netflat` absorbs the 172ca30
correction verbatim) — yet the spade rung moved, so
`forkState_unique` as currently stated can never close — its
residue was hiding a false conjunct, not a missing lemma.
(The conjugate-composite and FaceShape corrections of 172ca30 /
ac0c187 / 07247ec are DEFINITION-ORTHOGONAL to the G2 content: the
maximality transport never touched the composite; this file's
§1 was re-validated at 07247ec and survived with exactly the
two-grade `FaceShape` case split added to the refutation head.)

**What this file lands:**

* §1 THE COUNTEREXAMPLE FAMILY, theorem grade.  The crafted class:
  rungs (♠ 5, ♥ 4, ♦ 4, ♣ 3), forkState of the pair {5♥, 5♦} pinned
  at rank 5, witness 5♥; the forward journey
  `[tabToTab 5♥ (inr 6♣), tabToFound 6♠]` and the return journey
  `[foundToTab 6♠ (inr 7♥), tabToTab 5♥ (inr 6♠)]`, every leg undone
  by its one-move mirror (the witnesses are ONE def-`rfl` each); both
  endpoints WF, both `forkState` with witness 5♥ (the license
  census, decided over the full 52-card universe through the banked
  `canRaiseB` bridge), the pair suits pinned at both, and the
  spade rung moved 5 → 6.  The heads: the strict-G2 negation, and
  `forkState_unique`'s own statement negated (consuming
  `cargoPath_rungs` for the `FaceShape` impossibility).
* §2 THE SURVIVORS — the transport rows that DO hold and are the
  honest machinery a repaired uniqueness statement will consume:
  the journey-letter census (waste moves and reveal-shaped lifts
  never ride witness shuffles — `irr_of_desc` over the banked
  `cycleCount`/`hiddenTotal` tables), the raise-shape row (every
  reversible `tabToFound` leg is a licensed `CanRaise` raise or
  sits in the named bare-bottom residue), the under-seat strand
  (a seated raise's seat card is an UNFOUNDED, face-up, opposite-
  color board card of rank one above the raised card — the
  scarcity content the repaired head will price), the hidden-depth
  pin (hidden lists agree along witness journeys, leg by leg), and
  the conditional G2′ content head: same class + equal rungs ⇒
  founds agree card-for-card (the banked `rung_found_congr`) and
  hidden profiles agree — the honest form of the "non-pair content
  agrees" claim, with the rungs-equality hypothesis the craft says
  cannot be dropped.

Every row audits `[propext]` or `[propext, Quot.sound]` — zero
`Classical.choice`, zero `sorry` (this file's splits ride
`Decidable.em` and `decide` only).
-/

/-! ## §1. The counterexample family, theorem grade -/

private def crd (s : Suit) (r : Rank) : Card := ⟨s, r⟩

/-- The fork pair's witness twin (5♥) and its covered twin (5♦). -/
private def H5 : Card := crd .heart .five
private def D5 : Card := crd .diamond .five
/-- The movable black next-up (6♠) and the witness's seats. -/
private def S6 : Card := crd .spade .six
private def H7 : Card := crd .heart .seven
private def C6 : Card := crd .club .six
private def D7 : Card := crd .diamond .seven

/-- The crafted rungs: ♥ 4, ♦ 4, ♠ 5, ♣ 3. -/
private def hmap : Suit → Nat
  | .heart => 4 | .diamond => 4 | .spade => 5 | .club => 3

/-- THE CRAFTED FORKSTATE `cell`.  p0 = [7♥, 6♠, 5♥] (the witness
seated ON the black next-up — its own blocking cargo); p1 = [7♦, 6♣]
(the landing host for the witness's slide); p2 = [5♦] (the twin,
bare-bottom over an empty hidden deck, non-king — the seat bar kills
its license); p3–p6 hidden-only sink piles (face-up empty: nothing
fires from them, nothing lands on them); stock [7♠, 4♣] (the current
♠/♣ next-ups, stock-resident and dead); waste empty, drawStep 1. -/
private def cell : State where
  found := fun s => s.upCards.take (hmap s)
  piles := fun a => match a with
    | .p0 => ⟨[], [H7, S6, H5]⟩
    | .p1 => ⟨[], [D7, C6]⟩
    | .p2 => ⟨[], [D5]⟩
    | .p3 => ⟨[crd .club .king, crd .club .queen], []⟩
    | .p4 => ⟨[crd .heart .king, crd .heart .queen, crd .heart .jack,
               crd .heart .ten, crd .heart .nine, crd .heart .eight,
               crd .heart .six], []⟩
    | .p5 => ⟨[crd .diamond .king, crd .diamond .queen, crd .diamond .jack,
               crd .diamond .ten, crd .diamond .nine, crd .diamond .eight,
               crd .diamond .six], []⟩
    | .p6 => ⟨[crd .spade .king, crd .spade .queen, crd .spade .jack,
               crd .spade .ten, crd .spade .nine, crd .spade .eight,
               crd .club .five, crd .club .seven, crd .club .eight,
               crd .club .nine, crd .club .ten, crd .club .jack], []⟩
  stock := [crd .spade .seven, crd .club .four]
  waste := []
  drawStep := 1

/-- The forward journey: slide the witness off 6♠ (onto 6♣), then
raise 6♠ to its foundation. -/
private def mSlide : Move := Move.tabToTab H5 (Sum.inr C6)
private def mClimb : Move := Move.tabToFound S6

/-- The return journey: pull 6♠ back onto its under-seat 7♥, then
slide the witness back onto the exposed 6♠. -/
private def uPull : Move := Move.foundToTab S6 (Sum.inr H7)
private def uSlide : Move := Move.tabToTab H5 (Sum.inr S6)

/-- Oracle step: the successor, or the identity at a dead play (a
dead hand play is a construction bug — the gates below throw). -/
private def stepD (st : State) (m : Move) : State :=
  match st.step m with
  | none => st
  | some s' => s'

private def mid : State := stepD cell mSlide
private def mate : State := stepD mid mClimb

/-- The four legs fire exactly as claimed.  The slide and the climb
are `rfl` (the successor routes through the same composite); the
pull and the slide-back compare through `State.ext` pointwise —
the setFound/setPile record lambdas are stuck at variable suits,
but at each concrete suit/anchor they collapse to the same lists. -/
private theorem hSlide : State.step cell mSlide = some mid := by rfl

private theorem hClimb : State.step mid mClimb = some mate := by rfl

private theorem hPull : State.step mate uPull = some mid := by
  have hstep : State.step mate uPull = some (stepD mate uPull) := by rfl
  have hxEq : stepD mate uPull = mid := by
    refine State.ext (funext fun σ => ?_) (funext fun a => ?_) ?_ ?_ ?_
    · cases σ <;> rfl
    · cases a <;> rfl
    · rfl
    · rfl
    · rfl
  rw [hstep, hxEq]

private theorem hSlideUndo : State.step mid uSlide = some cell := by
  have hstep : State.step mid uSlide = some (stepD mid uSlide) := by rfl
  have hxEq : stepD mid uSlide = cell := by
    refine State.ext (funext fun σ => ?_) (funext fun a => ?_) ?_ ?_ ?_
    · cases σ <;> rfl
    · cases a <;> rfl
    · rfl
    · rfl
    · rfl
  rw [hstep, hxEq]

/-- Each leg is reversible by its one-move mirror, so the journeys
run on `ShufflePlayW` legs (the `reversibleAtW` witnesses). -/
private theorem revSlide : reversibleAtW cell mSlide :=
  ⟨mid, [uSlide], hSlide, run_one hSlideUndo⟩
private theorem revClimb : reversibleAtW mid mClimb :=
  ⟨mate, [uPull], hClimb, run_one hPull⟩
private theorem revPull : reversibleAtW mate uPull :=
  ⟨mid, [mClimb], hPull, run_one hClimb⟩
private theorem revSlideUndo : reversibleAtW mid uSlide :=
  ⟨cell, [mSlide], hSlideUndo, run_one hSlide⟩

/-- The forward witness shuffle: `cell → mate` through the slide and
the climb. -/
private theorem fwdShuffle : ShufflePlayW cell [mSlide, mClimb] mate :=
  .cons revSlide hSlide (.cons revClimb hClimb (.nil mate))

/-- The backward witness shuffle: `mate → cell` through the pull and
the slide-back. -/
private theorem bwdShuffle : ShufflePlayW mate [uPull, uSlide] cell :=
  .cons revPull hPull (.cons revSlideUndo hSlideUndo (.nil cell))

/-- **The two states are macro-class mates** — witness shuffles both
ways through the reversible four legs (the setoid's rev-closure
orientation). -/
theorem forkGate_class : sameOrbitSetoid.r cell mate :=
  ⟨[uPull, uSlide], bwdShuffle, [mSlide, mClimb], fwdShuffle⟩

/-- The class packaging: one `SameOrbit` quotient holding both
endpoints (`classOf` for both, through `Quotient.sound`). -/
theorem forkGate_corbit : ∃ C : SameOrbit, classOf C cell ∧ classOf C mate :=
  ⟨Quotient.mk sameOrbitSetoid cell, rfl, (Quotient.sound forkGate_class).symm⟩

/-! ### The WF audit rows -/

private theorem cell_wf_found : ∀ s : Suit, ∃ n, cell.found s = s.upCards.take n := by
  intro s
  cases s with
  | spade => exact ⟨5, rfl⟩
  | heart => exact ⟨4, rfl⟩
  | diamond => exact ⟨4, rfl⟩
  | club => exact ⟨3, rfl⟩

private theorem cell_wf_runs : ∀ a : Anchor, runOK (cell.piles a).faceUp = true := by
  intro a
  cases a <;> rfl

private theorem cell_wf_count : ∀ c ∈ Card.universe, cell.cardCount c = 1 := by
  intro c _
  rcases c with ⟨s, r⟩
  cases s <;> cases r <;> decide

/-- The craft is `WF` (all four clauses, kernel-decided). -/
theorem forkGate_cell_wf : cell.WF :=
  ⟨cell_wf_found, cell_wf_runs, cell_wf_count, by decide⟩

private theorem mate_wf_found : ∀ s : Suit, ∃ n, mate.found s = s.upCards.take n := by
  intro s
  cases s with
  | spade => exact ⟨6, rfl⟩
  | heart => exact ⟨4, rfl⟩
  | diamond => exact ⟨4, rfl⟩
  | club => exact ⟨3, rfl⟩

private theorem mate_wf_runs : ∀ a : Anchor, runOK (mate.piles a).faceUp = true := by
  intro a
  cases a <;> rfl

private theorem mate_wf_count : ∀ c ∈ Card.universe, mate.cardCount c = 1 := by
  intro c _
  rcases c with ⟨s, r⟩
  cases s <;> cases r <;> decide

/-- The journey's endpoint is `WF` too (WF rides the legs, but the
audit reads it directly). -/
theorem forkGate_mate_wf : mate.WF :=
  ⟨mate_wf_found, mate_wf_runs, mate_wf_count, by decide⟩

/-! ### The forkState census rows -/

/-- The 52-card license census at `cell`: only 5♥ is `CanRaise`
(through the banked `canRaiseB` Bool bridge, kernel-decided per
card). -/
private theorem cell_license : ∀ c : Card, CanRaise cell c ↔ c = H5 := by
  intro c
  rcases c with ⟨s, r⟩
  cases s <;> cases r
  all_goals
    first
    | exact ⟨fun _ => rfl, fun _ => (canRaiseB_true_iff).1 (by decide)⟩
    | exact ⟨fun hh => absurd ((canRaiseB_true_iff).2 hh) (by decide),
        fun hh => absurd hh (by decide)⟩

private theorem mate_license : ∀ c : Card, CanRaise mate c ↔ c = H5 := by
  intro c
  rcases c with ⟨s, r⟩
  cases s <;> cases r
  all_goals
    first
    | exact ⟨fun _ => rfl, fun _ => (canRaiseB_true_iff).1 (by decide)⟩
    | exact ⟨fun hh => absurd ((canRaiseB_true_iff).2 hh) (by decide),
        fun hh => absurd hh (by decide)⟩

/-- The pair pins at `cell` (witness 5♥). -/
private theorem cell_pins :
    rungAt cell H5.suit = H5.rank.toIdx ∧
    rungAt cell H5.twin.suit = H5.rank.toIdx := ⟨by rfl, by rfl⟩

/-- The pair pins at `mate`, intact after the climb. -/
private theorem mate_pins :
    rungAt mate H5.suit = H5.rank.toIdx ∧
    rungAt mate H5.twin.suit = H5.rank.toIdx := ⟨by rfl, by rfl⟩

/-- `cell` is a `forkState` (witness 5♥). -/
theorem forkGate_cell_fork : forkState cell :=
  ⟨H5, cell_pins.1, cell_pins.2, cell_license⟩

/-- `mate` is a `forkState` of the SAME pair, SAME orientation
(witness 5♥ again — the slide relocated it, the census names it,
nothing else went live). -/
theorem forkGate_mate_fork : forkState mate :=
  ⟨H5, mate_pins.1, mate_pins.2, mate_license⟩

/-! ### The rung ledger -/

/-- The pair family's rungs and the club rung survive the journey
untouched. -/
theorem forkGate_rungs_stay :
    rungAt cell Suit.heart = rungAt mate Suit.heart ∧
    rungAt cell Suit.diamond = rungAt mate Suit.diamond ∧
    rungAt cell Suit.club = rungAt mate Suit.club :=
  ⟨rfl, rfl, rfl⟩

/-- THE RUNG LEDGER: the non-pair spade foundation climbed by one on
the journey (5 → 6) — at the two same-class, same-pair forkStates. -/
theorem forkGate_spade_climbed :
    rungAt cell Suit.spade + 1 = rungAt mate Suit.spade := by rfl

/-! ### The refutation heads -/

/-- **THE STRICT G2 HEAD IS FALSE** — two `WF` `forkState`s of one
macro class, witnessing the same pair with the same orientation
(the iff's witness is literally the equal card at both), whose
non-pair spade rungs DIFFER.  The probe-first discipline's
anti-lemma: the craft succeeds, so `rungAt st₁ s = rungAt st₂ s`
for all non-pair suits is not provable — it is refuted. -/
theorem forkGate_strict_head_false :
    ∃ (C : SameOrbit) (st₁ st₂ : State) (x : Card) (s : Suit),
      st₁.WF ∧ st₂.WF ∧ forkState st₁ ∧ forkState st₂ ∧
        classOf C st₁ ∧ classOf C st₂ ∧
        (∀ c, CanRaise st₁ c ↔ c = x) ∧ (∀ c, CanRaise st₂ c ↔ c = x) ∧
        s ≠ x.suit ∧ s ≠ x.twin.suit ∧
        rungAt st₁ s ≠ rungAt st₂ s := by
  obtain ⟨C, hc1, hc2⟩ := forkGate_corbit
  refine ⟨C, cell, mate, H5, .spade, ?_, ?_, ?_, ?_, ?_, ?_,
    cell_license, mate_license, by decide, by decide, ?_⟩
  · exact forkGate_cell_wf
  · exact forkGate_mate_wf
  · exact forkGate_cell_fork
  · exact forkGate_mate_fork
  · exact hc1
  · exact hc2
  · intro hcon
    have := forkGate_spade_climbed
    omega

/-- **THE IN-TREE MAIN ROW IS FALSE AS STATED** — `forkState_unique`
(all its premises satisfied by the craft) cannot close at EITHER
grade of the corrected cross-bridge `FaceShape` (07247ec): the
same-face grade's cargo legs preserve all rungs (`cargoPath_rungs`,
§1 of `Orig.ForkStateUniq`), and the cross-face grade composes the
physical-swap composite (net-flat on every foundation: raise +1 on
x's suit, the `tabToTab` slide flat, the pull −1 back — the §4
loose-shape row `conjugate_endpoint_netflat`, whose `∃ d` absorbs
the correction's `d := x.twin` verbatim) with a cargo walk (flat) —
yet the spade rung moved 5 → 6 between the two craft endpoints.
The residue under the in-tree row was a false conjunct, not a
missing lemma; the honest repair needs class-grade fork hypotheses
(the §2 survivors below carry the machinery a repaired statement
will consume). -/
theorem forkState_unique_refuted :
    ¬ (∀ (C : SameOrbit) (st₁ st₂ : State), st₁.WF → st₂.WF →
        forkState st₁ → forkState st₂ →
        classOf C st₁ → classOf C st₂ → FaceShape st₁ st₂) := by
  intro h
  obtain ⟨C, hc1, hc2⟩ := forkGate_corbit
  have hfs := h C cell mate forkGate_cell_wf forkGate_mate_wf
    forkGate_cell_fork forkGate_mate_fork hc1 hc2
  have hmove : rungAt cell Suit.spade + 1 = rungAt mate Suit.spade :=
    forkGate_spade_climbed
  rcases hfs with hcp | ⟨z, hconj, hcpz⟩
  · have hsame := cargoPath_rungs hcp Suit.spade
    omega
  · obtain ⟨x, ba, bb, st₁, st₂, -, hr, hs, hp⟩ := hconj
    have hnet := conjugate_endpoint_netflat (w := z) (x := x)
      ⟨x.twin, ba, bb, st₁, st₂, hr, hs, hp⟩
    have hz : rungAt z Suit.spade = rungAt cell Suit.spade := by
      show (z.found Suit.spade).length = (cell.found Suit.spade).length
      rw [hnet Suit.spade]
    have hcross := cargoPath_rungs hcpz Suit.spade
    omega

/-! ## §2. The survivors — the transport machinery a repaired statement will consume

The corrected conjugate composite and the bridged `FaceShape` are
definition-orthogonal to every row here: this section reads only
the step records, the banked irreversibility tables
(`Orig.Irreversible`: `cycleCount_step`, `hiddenTotal_step`, and
the reveal-cells), and the `Mono` descent bridge.  None of the G2
content survived the probe; ALL of the mechanism did: a repaired
uniqueness statement (with class-grade fork premises) assembles
from exactly these rows plus whatever rung-pinning its extra
hypotheses buy.
-/

/-- **No waste raise ever rides** — a `wasteToFound` pops the draw
cycle irreversibly (the cycle count strictly drops at the move and
never rises through any play, `irr_of_desc` over Table 1), so a
witness-shuffle leg can never be one. -/
theorem journey_never_wasteToFound {st s' : State} {c : Card}
    (hstep : State.step st (Move.wasteToFound c) = some s') :
    ¬ reversibleAtW st (Move.wasteToFound c) := by
  intro hrev
  have hdrop : cycleCount s' < cycleCount st := by
    have := cycleCount_step_wasteToFound hstep
    omega
  exact absurd hrev (not_reversibleAtW_of_irreversibleAt
    (irr_of_desc cycleCount (fun s m s'' h => cycleCount_step h) hstep hdrop))

/-- **No waste placement ever rides** — same measure, the other
waste consumer. -/
theorem journey_never_wasteToTab {st s' : State} {c : Card} {b : Base}
    (hstep : State.step st (Move.wasteToTab c b) = some s') :
    ¬ reversibleAtW st (Move.wasteToTab c b) := by
  intro hrev
  have hdrop : cycleCount s' < cycleCount st := by
    have := cycleCount_step_wasteToTab hstep
    omega
  exact absurd hrev (not_reversibleAtW_of_irreversibleAt
    (irr_of_desc cycleCount (fun s m s'' h => cycleCount_step h) hstep hdrop))

/-- **A revealing raise never rides** — a `tabToFound` that strips
the last face-up card over a hidden deck drops the hidden total
irreversibly (Table 2's reveal cell through the descent bridge). -/
theorem journey_tabToFound_never_reveal {st s' : State} {c : Card} {a : Anchor}
    (hstep : State.step st (Move.tabToFound c) = some s')
    (hpa : st.pileOfTop c = some a)
    (hchop : chop (st.piles a).faceUp = [])
    (hhne : (st.piles a).hidden ≠ []) :
    ¬ reversibleAtW st (Move.tabToFound c) := by
  intro hrev
  have hdrop : hiddenTotal s' < hiddenTotal st := by
    have := hiddenTotal_step_tabToFound_reveal hstep hpa hchop hhne
    omega
  exact absurd hrev (not_reversibleAtW_of_irreversibleAt
    (irr_of_desc hiddenTotal (fun s m s'' h => hiddenTotal_step h) hstep hdrop))

/-- **A revealing slide never rides** — the `tabToTab` form of the
same reveal bar (the whole run leaves the pile, the hidden deck
under it loses a card for good). -/
theorem journey_tabToTab_never_reveal {st s' : State} {c : Card} {b : Base}
    {a : Anchor}
    (hstep : State.step st (Move.tabToTab c b) = some s')
    (hh : st.pileHolding c = some a)
    (hbel : below c (st.piles a).faceUp = [])
    (hhne : (st.piles a).hidden ≠ []) :
    ¬ reversibleAtW st (Move.tabToTab c b) := by
  intro hrev
  have hdrop : hiddenTotal s' < hiddenTotal st := by
    have := hiddenTotal_step_tabToTab_reveal hstep hh hbel hhne
    omega
  exact absurd hrev (not_reversibleAtW_of_irreversibleAt
    (irr_of_desc hiddenTotal (fun s m s'' h => hiddenTotal_step h) hstep hdrop))

/-- **The licensed-or-bare trichotomy of reversible raises** — every
`tabToFound` that rides a witness journey either IS a licensed
`CanRaise` raise at its own pre-state, or sits in the named
bare-bottom residue: the emptied seat (no face-up cards below over
an empty hidden deck at a non-king — the (Q,J)-falsifier's cell,
decided at the CanonV3 census; its `nextUp`-arithmetic residency is
the same corner `foundToTab_undo`'s `hnext` premise fences, and the
irreversibility of the bare-non-king lift is the write-analysis
residual the future classification card owns). -/
theorem journey_raise_shape {st s' : State} {c : Card}
    (hstep : State.step st (Move.tabToFound c) = some s')
    (hrev : reversibleAtW st (Move.tabToFound c)) :
    CanRaise st c ∨
      (∃ a, st.pileOfTop c = some a ∧ chop (st.piles a).faceUp = [] ∧
         (st.piles a).hidden = [] ∧ c.rank ≠ Rank.king) := by
  obtain ⟨hn, a, hpa, -⟩ := step_tabToFound_inv hstep
  rcases Decidable.em (chop (st.piles a).faceUp = []) with hc | hc
  · rcases Decidable.em ((st.piles a).hidden = []) with hh | hh
    · rcases Decidable.em (c.rank = Rank.king) with hk | hk
      · exact Or.inl ⟨hn, a, hpa, Or.inr ⟨hh, hk⟩⟩
      · exact Or.inr ⟨a, hpa, hc, hh, hk⟩
    · exact absurd hrev (journey_tabToFound_never_reveal hstep hpa hc hh)
  · exact Or.inl ⟨hn, a, hpa, Or.inl hc⟩

/-- **The under-seat strand** — a seated reversible raise's seat
card (the face-up card directly below the raised one, pinned by the
pile discipline) is UNFOUNDED, and the fit says it is an
opposite-color board card one rank above.  This is the scarcity
certificate a repaired G2 will price: a licensed non-pair raise
burns an unfounded opposite-family card of rank (r + 1) as its
seat — the craft's own mechanism (the witness 5♥ serving as 6♠'s
seat) is the loophole, and its closure is extra hypothesis. -/
theorem journey_raise_seatUnfounded {st s' : State} {c : Card} {a : Anchor}
    (hwf : st.WF)
    (_hstep : State.step st (Move.tabToFound c) = some s')
    (hpa : st.pileOfTop c = some a)
    (hchop : chop (st.piles a).faceUp ≠ []) :
    ∃ z : Card, z ∈ (st.piles a).faceUp ∧ z ∉ st.found z.suit ∧
      c.rank.toIdx + 1 = z.rank.toIdx ∧ c.suit.color ≠ z.suit.color := by
  obtain ⟨hfu, hlast⟩ := pileOfTop_top hpa
  have hsnoc : (st.piles a).faceUp = chop (st.piles a).faceUp ++ [c] :=
    lastOf_chop hlast
  have hrok : runOK (chop (st.piles a).faceUp ++ [c]) = true := by
    rw [← hsnoc]
    exact hwf.2.1 a
  obtain ⟨z, hz, hsit⟩ := runOK_snoc_sit hchop hrok
  have hzmemF : z ∈ (st.piles a).faceUp := by
    rw [hsnoc]
    exact List.mem_append.mpr (Or.inl (lastOf_mem hz))
  refine ⟨z, hzmemF, (mem_faceUp_only hwf hzmemF).2.2.2.2 z.suit,
    ((canSitOn_eq c z).mp hsit).1, ((canSitOn_eq c z).mp hsit).2⟩

/-- **The hidden-depth pin, per-pile write analysis** (the private
copy of `Orig.Irreversible`'s battery, restated as the exact
dichotomy the pin consumes: every firing move keeps each pile's
hidden list EXACTLY, or the pile is the move's own reveal source
and lost strictly one card).  Components cited: the public
`afterRunRemoved_hidden` trichotomy, `putCard_hidden_eq`,
`stepDraw_piles`, and the per-move inversion rows. -/
private theorem tabToFound_pile_hidden {st s' : State} {c : Card} {a a' : Anchor}
    (hstep : State.step st (Move.tabToFound c) = some s')
    (hpa : st.pileOfTop c = some a) :
    (s'.piles a').hidden = (st.piles a').hidden ∨
      (s'.piles a').hidden.length + 1 ≤ (st.piles a').hidden.length := by
  obtain ⟨-, a₀, hp2, hs⟩ := step_tabToFound_inv hstep
  have hpair : some a = some a₀ := hpa.symm.trans hp2
  injection hpair with haa
  subst haa
  rw [hs]
  show (if a' = a then Pile.afterRunRemoved (st.piles a) (chop (st.piles a).faceUp)
      else st.piles a').hidden = (st.piles a').hidden ∨
    (if a' = a then Pile.afterRunRemoved (st.piles a) (chop (st.piles a).faceUp)
      else st.piles a').hidden.length + 1 ≤ (st.piles a').hidden.length
  by_cases hae : a' = a
  · rw [hae, ite_eq_left rfl]
    rcases afterRunRemoved_hidden (st.piles a) (chop (st.piles a).faceUp) with
      ⟨-, hhe⟩ | ⟨-, -, hhe⟩ | ⟨-, -, hdrop⟩
    · exact Or.inl hhe
    · exact Or.inl hhe
    · exact Or.inr (by omega)
  · rw [ite_eq_right hae]
    exact Or.inl rfl

/-- The run-removal `setPile`, as a hidden-dichotomy at any anchor
(the shared trichotomy consumer of the two legs below). -/
private theorem setPileARR_hidden (st : State) (a : Anchor) (c : Card) (a' : Anchor) :
    ((st.setPile a
        (Pile.afterRunRemoved (st.piles a) (below c (st.piles a).faceUp))).piles a').hidden =
      (st.piles a').hidden ∨
    ((st.setPile a
        (Pile.afterRunRemoved (st.piles a) (below c (st.piles a).faceUp))).piles a').hidden.length
      + 1 ≤ (st.piles a').hidden.length := by
  by_cases hae : a' = a
  · rw [hae, setPile_afterRunRemoved_piles_self st a c]
    rcases afterRunRemoved_hidden (st.piles a) (below c (st.piles a).faceUp) with
      ⟨-, hhe⟩ | ⟨-, -, hhe⟩ | ⟨-, -, hdrop⟩
    · exact Or.inl hhe
    · exact Or.inl hhe
    · exact Or.inr (by omega)
  · rw [setPile_afterRunRemoved_piles_ne st a c a' hae]
    exact Or.inl rfl

/-- The `tabToTab` leg of the dichotomy (the copy's copy-shape of
`Orig/MacroInternal`'s rung battery and `hiddenTotal_step`'s own
per-pile analysis; all components public). -/
private theorem tabToTab_pile_hidden {st s' : State} {c : Card} {b : Base}
    {a a' : Anchor}
    (hstep : State.step st (Move.tabToTab c b) = some s')
    (hh : st.pileHolding c = some a) :
    (s'.piles a').hidden = (st.piles a').hidden ∨
      (s'.piles a').hidden.length + 1 ≤ (st.piles a').hidden.length := by
  obtain ⟨a₀, hh2, hcp, -, hs⟩ := step_tabToTab_inv hstep
  have hpair : some a = some a₀ := hh.symm.trans hh2
  injection hpair with haa
  subst haa
  rw [hs]
  cases b with
  | inl a₁ =>
      obtain ⟨hemp, -⟩ := canPlace_inl hcp
      obtain ⟨hhd, -⟩ := (Pile.isEmpty_eq _).mp hemp
      simp only [putRun_piles_inl]
      by_cases hae : a' = a₁
      · rw [hae, ite_eq_left rfl, hhd]
        exact Or.inl rfl
      · rw [ite_eq_right hae]
        rcases setPileARR_hidden st a c a' with h | h
        · exact Or.inl h
        · exact Or.inr h
  | inr z =>
      cases hz : (st.setPile a
          (Pile.afterRunRemoved (st.piles a) (below c (st.piles a).faceUp))).pileOfTop z with
      | none =>
          rw [putRun_inr_none hz]
          rcases setPileARR_hidden st a c a' with h | h
          · exact Or.inl h
          · exact Or.inr h
      | some k =>
          simp only [putRun_piles_inr _ _ _ _ hz]
          by_cases hae : a' = k
          · rw [hae, ite_eq_left rfl]
            show ((st.setPile a
                (Pile.afterRunRemoved (st.piles a)
                  (below c (st.piles a).faceUp))).piles k).hidden =
              (st.piles k).hidden ∨ _
            rcases setPileARR_hidden st a c k with h | h
            · exact Or.inl h
            · exact Or.inr h
          · rw [ite_eq_right hae]
            rcases setPileARR_hidden st a c a' with h | h
            · exact Or.inl h
            · exact Or.inr h

/-- The per-pile hidden dichotomy for ANY firing move — the
composite over the six letters (draw and the waste letters keep
every pile's hidden list verbatim; the two reveal-carrying letters
keep-or-drop-one at their own source pile). -/
private theorem step_pile_hidden {st s' : State} {m : Move}
    (h : State.step st m = some s') (a' : Anchor) :
    (s'.piles a').hidden = (st.piles a').hidden ∨
      (s'.piles a').hidden.length + 1 ≤ (st.piles a').hidden.length := by
  cases m with
  | draw =>
      have hp := stepDraw_piles h
      rw [← hp]
      exact Or.inl rfl
  | wasteToFound c =>
      obtain ⟨-, x, xs, -, hs⟩ := step_wasteToFound_inv h
      rw [hs]
      exact Or.inl rfl
  | wasteToTab c b =>
      obtain ⟨hg, hrest⟩ := step_wasteToTab_inv h
      obtain ⟨x, xs, -, hs⟩ := hrest
      rw [Bool.and_eq_true] at hg
      rw [hs]
      refine Or.inl (show ((st.putCard c b).piles a').hidden = (st.piles a').hidden from
        putCard_hidden_eq hg.2 a')
  | tabToFound c =>
      obtain ⟨-, a, hpa, -⟩ := step_tabToFound_inv h
      exact tabToFound_pile_hidden h hpa
  | foundToTab c b =>
      obtain ⟨-, -, -, hcp, hs⟩ := step_foundToTab_inv h
      have hcp2 : (st.setFound c.suit (chop (st.found c.suit))).canPlace c b = true := hcp
      rw [hs]
      refine Or.inl (by rw [putCard_hidden_eq hcp2]; rfl)
  | tabToTab c b =>
      obtain ⟨a, hh, -, -, hs⟩ := step_tabToTab_inv h
      exact tabToTab_pile_hidden h hh

/-- A play can never REGROW any pile's hidden list (the run-lift of
the dichotomy's ≤-half). -/
private theorem run_pile_hidden_le : ∀ (st : State) (play : List Move) (w : State),
    st.run play = some w →
    ∀ a, (w.piles a).hidden.length ≤ (st.piles a).hidden.length := by
  intro st play
  revert st
  induction play with
  | nil =>
      intro st w h a
      have hp : some st = some w := h
      injection hp with hc
      rw [← hc]
      exact Nat.le_refl _
  | cons p rest ih =>
      intro st w h a
      obtain ⟨s₁, hstep, hrest⟩ := State.run_cons h
      rcases step_pile_hidden hstep a with heq | hdrop
      · rw [← heq]
        exact ih s₁ w hrest a
      · exact Nat.le_trans (ih s₁ w hrest a) (by omega)

/-- **THE HIDDEN-DEPTH PIN** — along a witness shuffle, every pile's
hidden list is PRESERVED EXACTLY: a leg that drops any pile's
hidden content is irreversible (its return play can never regrow
it, `run_pile_hidden_le`), so no such leg can ride.  The honest
"hidden depths agree" claim of the §11-L5 diagnosis, landed as a
class-grade transport row. -/
theorem shuffle_hiddenPinned {st w : State} : ∀ {play : List Move},
    ShufflePlayW st play w →
    ∀ a, (w.piles a).hidden = (st.piles a).hidden := by
  intro play h
  induction h with
  | nil s => intro a; rfl
  | @cons st₀ m s₁ rest w₀ hrev hstep hrest ih =>
      intro a
      rcases step_pile_hidden hstep a with heq | hdrop
      · exact (ih a).trans heq
      · obtain ⟨s₁', ρ, hstep2, hrun⟩ := hrev
        have hs₁eq : s₁' = s₁ := by
          have hp : some s₁' = some s₁ := hstep2.symm.trans hstep
          injection hp with hcon
        rw [hs₁eq] at hrun
        have hle := run_pile_hidden_le s₁ ρ st₀ hrun a
        omega

/-- **THE CONDITIONAL G2′ CONTENT HEAD** — the honest form of the
"non-pair content agrees" claim, with the rungs-equality
hypothesis the counterexample says cannot be dropped: at a shared
height tuple, same-class members read the foundations
card-for-card (the banked `rung_found_congr` — so ALL suit
foundations agree, pair and non-pair alike) and the per-pile
hidden profiles agree (the pin above, through the setoid's own
witness shuffles).  A repaired `forkState_unique` that proves the
rung agreement from its extra class-grade hypotheses consumes
exactly this row as its finishing step. -/
theorem forkState_content_of_rungsAgree {st₁ st₂ : State}
    (hwf₁ : st₁.WF) (hwf₂ : st₂.WF)
    (hclass : sameOrbitSetoid.r st₁ st₂)
    (hrungs : ∀ σ : Suit, rungAt st₁ σ = rungAt st₂ σ) :
    (∀ σ : Suit, st₁.found σ = st₂.found σ) ∧
      (∀ a : Anchor, (st₁.piles a).hidden = (st₂.piles a).hidden) := by
  refine ⟨fun σ => rung_found_congr st₁ st₂ hwf₁ hwf₂ σ (hrungs σ), ?_⟩
  obtain ⟨σs, hσs, -, -⟩ := hclass
  intro a
  -- the class's own σ-witness runs st₂ → st₁; the pin reads it
  -- end-toward-start, which is exactly the goal's orientation
  exact shuffle_hiddenPinned hσs a

/-! ## The audit battery

`#print axioms` per fresh head — expected `[propext]` or
`[propext, Quot.sound]` (the class/head rows carry `Quot.sound`),
zero `Classical.choice` (every split rides `Decidable.em` or
kernel-decided census rows), zero `sorry`: the refutation is a
constructed counterexample, not a gated row. -/

#print axioms forkGate_class
#print axioms forkGate_corbit
#print axioms forkGate_cell_wf
#print axioms forkGate_mate_wf
#print axioms forkGate_cell_fork
#print axioms forkGate_mate_fork
#print axioms forkGate_rungs_stay
#print axioms forkGate_spade_climbed
#print axioms forkGate_strict_head_false
#print axioms forkState_unique_refuted
#print axioms journey_never_wasteToFound
#print axioms journey_never_wasteToTab
#print axioms journey_tabToFound_never_reveal
#print axioms journey_tabToTab_never_reveal
#print axioms journey_raise_shape
#print axioms journey_raise_seatUnfounded
#print axioms shuffle_hiddenPinned
#print axioms forkState_content_of_rungsAgree

