import Orig.ForkStateSB

/-!
# Orig.CrossFamilyProbe — THE CROSS-FAMILY DECIDE PROBE

THE QUESTION: can one rich board host a class containing a {5♥, 5♦}
fork AND a {5♠, 5♣} fork — rank-equal, cross-family?  Decide-grade:

* **§1 `cf0`** — the red fork {5♥, 5♦} with BOTH black 5s WELL-SEATED
  on live content ([6♥, 5♠], [6♦, 5♣] — the fit-legal reading of the
  ticket's seat pairs): `forkStateSB cf0 = true`, both black 5s
  COLD at the origin.  The census read that forces it: the twin's
  cover is a BLACK FOUR on the tableau (the only fitters over 5♦),
  capping clubs at r−2; the other black four is hot with NO legal
  cover (red threes: foundation-resident) and NO free seat (red
  fives: fork-held), so it sits LONE over its deck — and BOTH lone
  lifts are revealing commitments (banked journey juries).
* **§2 `cf3`** — the engineered far end: the BLACK fork {5♠, 5♣}
  pins, `forkStateSB cf3 = true` — THE FIFTH LANDING LANDS, as a
  board.  Its price: the twin's red-four cover is pulled from the
  heart foundation (hearts 4→2, LIFO popping the 3♥ after it), and
  the co-popped 3♥ arrives NEXT-UP with every fitting seat and
  cover (black fours, black twos) FOUNDED by the black fork's own
  rungs — the iterated freeze leaves it a bar-seat only.
* **The quilt dies at both doors**: at cf0 the ONLY black-rung
  raisers are the two lone lifts and the lone re-seat — each a
  decided one-way; at cf3 the popped refugee cannot be seated
  anywhere (empty landing lattice, all fits foundation-resident).
  The pairClass theorem's door closes BY ORDERING at both ends;
  the cross-family residue stands unhurt.

Every row kernel-decided, zero sorry.
-/

/-! ## §0. The private kit -/

private def crd (s : Suit) (r : Rank) : Card := ⟨s, r⟩

/- Oracle step helper (dead-hand plays are construction bugs). -/
private def stepD (st : State) (m : Move) : State :=
  match st.step m with
  | none => st
  | some s' => s'

private def H3 : Card := crd .heart .three
private def H4 : Card := crd .heart .four
private def H5 : Card := crd .heart .five
private def H6 : Card := crd .heart .six
private def H7 : Card := crd .heart .seven
private def D3 : Card := crd .diamond .three
private def D4 : Card := crd .diamond .four
private def D5 : Card := crd .diamond .five
private def D6 : Card := crd .diamond .six
private def S4 : Card := crd .spade .four
private def S5 : Card := crd .spade .five
private def S6 : Card := crd .spade .six
private def C3 : Card := crd .club .three
private def C4 : Card := crd .club .four
private def C5 : Card := crd .club .five
private def C6 : Card := crd .club .six

/-! ## §1. THE ORIGIN `cf0` — the red fork, the black pair seated cold

Rungs ♥ 4 / ♦ 4 / ♠ 3 / ♣ 2.  Clubs CANNOT sit at 3: the twin's
cover 4♣ would then be next-up hot (SProbe's own seal note).  p0 =
[7♥, 6♠, 5♥] (the witness); p2 = [6♣, 5♦, 4♣] (the twin under the
cold black-four cover — the MANDATE: the only fitters over 5♦ are
the black fours, so the fork's own saturation parks (r−1) black
material ON the tableau); p3/p4 = [6♥, 5♠] and [6♦, 5♣] (the
WELL-SEATED black 5s, cold by the rank-read: both columns sit BELOW
the fork index at the origin); p1/p5 = the lone hot strata (4♠
next-up at spades 3, 3♣ next-up at clubs 2 — each seat-barred over
its deck, each a revealing lift away); p6/stock the diamond sink. -/

private def hmap0 : Suit → Nat
  | .heart => 4 | .diamond => 4 | .spade => 3 | .club => 2

private def cf0 : State where
  found := fun s => s.upCards.take (hmap0 s)
  piles := fun a => match a with
    | .p0 => ⟨[], [H7, S6, H5]⟩
    | .p1 => ⟨[crd .spade .seven, crd .spade .eight, crd .spade .nine,
               crd .spade .ten, crd .spade .jack, crd .spade .queen,
               crd .spade .king], [S4]⟩
    | .p2 => ⟨[], [C6, D5, C4]⟩
    | .p3 => ⟨[crd .heart .eight, crd .heart .nine, crd .heart .ten],
              [H6, S5]⟩
    | .p4 => ⟨[crd .heart .jack, crd .heart .queen, crd .heart .king],
              [D6, C5]⟩
    | .p5 => ⟨[crd .club .seven, crd .club .eight, crd .club .nine,
               crd .club .ten, crd .club .jack, crd .club .queen,
               crd .club .king], [C3]⟩
    | .p6 => ⟨[crd .diamond .seven, crd .diamond .eight, crd .diamond .nine,
               crd .diamond .ten, crd .diamond .jack, crd .diamond .queen], []⟩
  stock := [crd .diamond .king]
  waste := []
  drawStep := 1

private theorem cf0_wf_found : ∀ s : Suit, ∃ n, cf0.found s = s.upCards.take n := by
  intro s
  cases s with
  | spade => exact ⟨3, rfl⟩
  | heart => exact ⟨4, rfl⟩
  | diamond => exact ⟨4, rfl⟩
  | club => exact ⟨2, rfl⟩

private theorem cf0_wf_runs : ∀ a : Anchor, runOK (cf0.piles a).faceUp = true := by
  intro a
  cases a <;> rfl

private theorem cf0_wf_count : ∀ c ∈ Card.universe, cf0.cardCount c = 1 := by
  intro c _
  rcases c with ⟨s, r⟩
  cases s <;> cases r <;> decide

private theorem cf0_wf : cf0.WF :=
  ⟨cf0_wf_found, cf0_wf_runs, cf0_wf_count, by decide⟩

/-- **THE ORIGIN IS A STRONG FORK** — the census folds {5♥, 5♦}. -/
theorem cf0_fork : forkStateSB cf0 = true := by decide

theorem cf0_forkState : forkState cf0 := (forkStateSB_true_iff cf0_wf).mp cf0_fork

/-- The witness is the vanilla-live 5♥ — the covered twin 5♦ is
vanilla-dead, so the orientation row names 5♥ (rfl-fold). -/
theorem cf0_witness : forkWitnessSB cf0 = some H5 := by rfl

/-- The pair lives; exactly the pair: both black 5s COLD (the
task's audit column), the hot lone strata bar-seated. -/
theorem cf0_ledger :
    canRaiseSB cf0 H5 = true ∧ canRaiseSB cf0 D5 = true ∧
      canRaiseB cf0 D5 = false ∧
        canRaiseSB cf0 S5 = false ∧ canRaiseSB cf0 C5 = false ∧
          canRaiseSB cf0 S4 = false ∧ canRaiseSB cf0 C3 = false ∧
            canRaiseSB cf0 C4 = false :=
  ⟨by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide⟩

/-! ### The origin read — the order rows that close the other-family door

The task's question — can the black 5s be next-up AND cold at cf0? —
is decided in the negative, and the rows below name the exact census
reads: -/

/-- **THE WELL-SEATED BLACKS**: both black 5s sit on live face-up
content (not buried, not lone), and BOTH are rank-dead — their
columns sit BELOW the fork index at the origin (♠ at r−1, ♣ at
r−2). -/
theorem cf0_seats :
    (cf0.piles Anchor.p3).faceUp = [H6, S5] ∧
      (cf0.piles Anchor.p4).faceUp = [D6, C5] ∧
        cf0.nextUp S5 = false ∧ cf0.nextUp C5 = false ∧
          rungAt cf0 Suit.spade = 3 ∧ rungAt cf0 Suit.club = 2 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **THE COVER MANDATE, FIT-AUDITED**: over the whole universe the
ONLY cards that may sit face-up on the twin 5♦ are the BLACK FOURS —
the fork's own sandwich parks (r−1) black material ON the tableau,
and that suit's column is capped below the fork rank forever after:
4♣ here is cold only because clubs sit at r−2. -/
theorem cf0_coverFit : ∀ z ∈ Card.universe, canSitOn z D5 = decide (z = S4 ∨ z = C4) := by
  intro z _
  rcases z with ⟨s, r⟩
  cases s <;> cases r <;> decide

/-- The cover on record: cold at the club rank-read (not seat, not
exit — pure ordering). -/
theorem cf0_cover :
    (cf0.piles Anchor.p2).faceUp = [C6, D5, C4] ∧
      cf0.nextUp C4 = false ∧
        cf0.canPlace C4 (Sum.inr H5) = true :=
  ⟨rfl, rfl, by decide⟩

/-- **THE HOT-BLACK SCANS**: the free black four 4♠ is next-up at
the origin (spades r−1), and its ONLY legal covers are the RED
THREES — both foundation-resident at the fork's own family rungs.
No cover exists for it anywhere on the board. -/
theorem cf0_S4_fit :
    cf0.nextUp S4 = true ∧
      (∀ z ∈ Card.universe, canSitOn z S4 = decide (z = H3 ∨ z = D3)) ∧
        H3 ∈ cf0.found Suit.heart ∧ D3 ∈ cf0.found Suit.diamond ∧
          cf0.foundTop Suit.heart = some H4 ∧
            cf0.foundTop Suit.diamond = some D4 :=
  ⟨rfl, by intro z _; rcases z with ⟨s, r⟩; cases s <;> cases r <;> decide,
    by decide, by decide, rfl, rfl⟩

/-- **THE COMPLETE ORIGIN CENSUS**: the only hot cards at cf0 are
the live pair and the two lone black strata — every other raise in
the universe is refused by the rank-read alone. -/
theorem cf0_hot :
    ∀ c ∈ Card.universe, cf0.nextUp c = true ↔
      (c = H5 ∨ c = D5 ∨ c = S4 ∨ c = C3) := by
  intro c _
  rcases c with ⟨s, r⟩
  cases s <;> cases r <;> decide

/-- The black 5s cannot be raised at the origin (steps are `none`),
and neither black column can pin while its four is out. -/
theorem cf0_climbRefused :
    State.step cf0 (Move.tabToFound S5) = none ∧
      State.step cf0 (Move.tabToFound C5) = none ∧
        State.step cf0 (Move.tabToFound C4) = none :=
  ⟨rfl, rfl, rfl⟩

/-- The lone lifts DO fire — the climb attempts — and the black
fork would need BOTH columns raised to r: the spade lift alone is
not enough, and each lone lift strips its deck's cover (reveals). -/
private def cf0S4Lift : State := stepD cf0 (Move.tabToFound S4)
private def cf0C3Lift : State := stepD cf0 (Move.tabToFound C3)
private def cf0S4Seat : State := stepD cf0 (Move.tabToTab S4 (Sum.inr H5))

theorem cf0_S4_liftStep : State.step cf0 (Move.tabToFound S4) = some cf0S4Lift := by rfl
theorem cf0_C3_liftStep : State.step cf0 (Move.tabToFound C3) = some cf0C3Lift := by rfl
theorem cf0_S4_seatStep : State.step cf0 (Move.tabToTab S4 (Sum.inr H5)) = some cf0S4Seat := by rfl

/-- **THE LONE RE-SEAT LATTICE**: over the whole universe 4♠'s only
placeable top is the witness's own head (its one fitter that tops a
pile); every empty anchor is king-barred. -/
theorem cf0_S4_lattice :
    (∀ z ∈ Card.universe, cf0.canPlace S4 (Sum.inr z) = decide (z = H5)) ∧
      (∀ a : Anchor, cf0.canPlace S4 (Sum.inl a) = false) := by
  refine ⟨?_, ?_⟩
  · intro z _
    rcases z with ⟨s, r⟩
    cases s <;> cases r <;> decide
  · intro a
    cases a <;> decide

/-- **THE ONE-WAY CLIMB ATTEMPTS**: all three legal black-climb
legs at the origin are revealing commitments over the lone bars —
banked journey juries, each with its kernel-folded step. -/
theorem cf0_S4_liftOneWay : ¬ reversibleAtW cf0 (Move.tabToFound S4) :=
  journey_tabToFound_never_reveal cf0_S4_liftStep
    (show cf0.pileOfTop S4 = some Anchor.p1 from rfl)
    (show chop (cf0.piles Anchor.p1).faceUp = [] from rfl)
    (show (cf0.piles Anchor.p1).hidden ≠ [] from by decide)

theorem cf0_C3_liftOneWay : ¬ reversibleAtW cf0 (Move.tabToFound C3) :=
  journey_tabToFound_never_reveal cf0_C3_liftStep
    (show cf0.pileOfTop C3 = some Anchor.p5 from rfl)
    (show chop (cf0.piles Anchor.p5).faceUp = [] from rfl)
    (show (cf0.piles Anchor.p5).hidden ≠ [] from by decide)

theorem cf0_S4_seatOneWay : ¬ reversibleAtW cf0 (Move.tabToTab S4 (Sum.inr H5)) :=
  journey_tabToTab_never_reveal cf0_S4_seatStep
    (show cf0.pileHolding S4 = some Anchor.p1 from rfl)
    (show below S4 (cf0.piles Anchor.p1).faceUp = [] from rfl)
    (show (cf0.piles Anchor.p1).hidden ≠ [] from by decide)

/-! ## §2. THE FAR END `cf3` — the engineered black fork

The maximal legal craft: both black columns at r (founded A–4,
pinned by the pair's own witnesses), the twin 5♣ seated under a
pulled RED-FOUR cover (hearts 4→2: LIFO pops the 4♥ onto the twin
first, then the 3♥ after it), the OTHER red five rank-buried into
its foundation (diamonds 4→5), cf0's witness pile surviving verbatim
(all rank-dead at the drops).  The popped red 3♥ arrives NEXT-UP at
hearts 2 and can be cold ONLY over a bar-seat — every fitting seat
(black fours) and cover (black twos) is foundation-resident at the
black fork's own rungs: THE FREEZE ITERATED. -/

private def hmap3 : Suit → Nat
  | .heart => 2 | .diamond => 5 | .spade => 4 | .club => 4

private def cf3 : State where
  found := fun s => s.upCards.take (hmap3 s)
  piles := fun a => match a with
    | .p0 => ⟨[], [H7, S6, H5]⟩
    | .p1 => ⟨[crd .spade .seven, crd .spade .eight, crd .spade .nine,
               crd .spade .ten, crd .spade .jack, crd .spade .queen,
               crd .spade .king], []⟩
    | .p2 => ⟨[crd .club .seven, crd .club .eight, crd .club .nine,
               crd .club .ten, crd .club .jack, crd .club .queen,
               crd .club .king], [C6]⟩
    | .p3 => ⟨[crd .heart .queen], [D6, S5]⟩
    | .p4 => ⟨[crd .heart .king], [H6, C5, H4]⟩
    | .p5 => ⟨[crd .heart .eight, crd .heart .nine, crd .heart .ten,
               crd .heart .jack], [H3]⟩
    | .p6 => ⟨[crd .diamond .seven, crd .diamond .eight, crd .diamond .nine,
               crd .diamond .ten, crd .diamond .jack, crd .diamond .queen,
               crd .diamond .king], []⟩
  stock := []
  waste := []
  drawStep := 1

private theorem cf3_wf_found : ∀ s : Suit, ∃ n, cf3.found s = s.upCards.take n := by
  intro s
  cases s with
  | spade => exact ⟨4, rfl⟩
  | heart => exact ⟨2, rfl⟩
  | diamond => exact ⟨5, rfl⟩
  | club => exact ⟨4, rfl⟩

private theorem cf3_wf_runs : ∀ a : Anchor, runOK (cf3.piles a).faceUp = true := by
  intro a
  cases a <;> rfl

private theorem cf3_wf_count : ∀ c ∈ Card.universe, cf3.cardCount c = 1 := by
  intro c _
  rcases c with ⟨s, r⟩
  cases s <;> cases r <;> decide

private theorem cf3_wf : cf3.WF :=
  ⟨cf3_wf_found, cf3_wf_runs, cf3_wf_count, by decide⟩

/-- **THE VERDICT AT THE FAR END: TRUE — THE FIFTH LANDING LANDS.**
The census folds {5♠, 5♣}: the black pair pins on the mirrored
economy (decided). -/
theorem cf3_fork : forkStateSB cf3 = true := by decide

theorem cf3_forkState : forkState cf3 := (forkStateSB_true_iff cf3_wf).mp cf3_fork

/-- The witness is the vanilla-live 5♠; the covered twin 5♣ is
vanilla-dead under the pulled heart four. -/
theorem cf3_witness : forkWitnessSB cf3 = some S5 := by rfl

/-- The far-end ledger: exactly the black pair lives.  The old red
pair is dead — 5♥ by the rank-read (hearts sit at 2), 5♦ by the
rank-burial (founded into diamonds); the twin's pulled cover 4♥ is
cold by the same rank-read; the refugee 3♥ and the witness-seat
6♦ are hot and bar-seated. -/
theorem cf3_ledger :
    canRaiseSB cf3 S5 = true ∧ canRaiseSB cf3 C5 = true ∧
      canRaiseB cf3 C5 = false ∧
        canRaiseSB cf3 H5 = false ∧ canRaiseSB cf3 D5 = false ∧
          canRaiseSB cf3 H4 = false ∧ canRaiseSB cf3 H3 = false ∧
            canRaiseSB cf3 D6 = false ∧ canRaiseSB cf3 C6 = false :=
  ⟨by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide⟩

theorem cf3_shape :
    (cf3.piles Anchor.p3).faceUp = [D6, S5] ∧
      (cf3.piles Anchor.p4).faceUp = [H6, C5, H4] ∧
        (cf3.piles Anchor.p0).faceUp = [H7, S6, H5] :=
  ⟨rfl, rfl, rfl⟩

/-- The rung tuple: blacks pinned at r by the fork's own
witnesses; hearts dropped TWO (the cover's LIFO price — a red four
out means its suit sits at r−2); diamonds CLIMBED one (the 5♦
rank-burial). -/
theorem cf3_rungs :
    rungAt cf3 Suit.spade = 4 ∧ rungAt cf3 Suit.club = 4 ∧
      rungAt cf3 Suit.heart = 2 ∧ rungAt cf3 Suit.diamond = 5 ∧
        cf3.foundTop Suit.diamond = some D5 ∧
          cf3.nextUp H5 = false ∧ cf3.nextUp D5 = false :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **THE COMPLETE FAR-END CENSUS**: the only hot cards are the
live black pair and the two bar-cards (the refugee 3♥, the
witness-seat 6♦). -/
theorem cf3_hot :
    ∀ c ∈ Card.universe, cf3.nextUp c = true ↔
      (c = S5 ∨ c = C5 ∨ c = H3 ∨ c = D6) := by
  intro c _
  rcases c with ⟨s, r⟩
  cases s <;> cases r <;> decide

/-- **THE REFUGEE, PRICED**: the co-popped 3♥ is next-up at the far
end, hosted over a bar-seat — and its landing lattice is EMPTY over
the whole universe: no pile top fits it, no empty anchor takes it.
Its fits would be exactly the black fours (seats) and black twos
(covers) — and those suits stand at 4: everything it could sit on
or under is foundation-resident at the black fork's own rungs. -/
theorem cf3_refugee :
    cf3.nextUp H3 = true ∧ (cf3.piles Anchor.p5).faceUp = [H3] ∧
      (∀ z ∈ Card.universe, cf3.canPlace H3 (Sum.inr z) = false) ∧
        (∀ a : Anchor, cf3.canPlace H3 (Sum.inl a) = false) ∧
          (∀ z ∈ Card.universe, canSitOn H3 z = decide (z = S4 ∨ z = C4)) ∧
            (∀ z ∈ Card.universe, canSitOn z H3 =
              decide (z = crd .spade .two ∨ z = crd .club .two)) ∧
              cf3.foundTop Suit.spade = some S4 ∧
                cf3.foundTop Suit.club = some C4 := by
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, rfl, rfl⟩
  · intro z _
    rcases z with ⟨s, r⟩
    cases s <;> cases r <;> decide
  · intro a
    cases a <;> decide
  · intro z _
    rcases z with ⟨s, r⟩
    cases s <;> cases r <;> decide
  · intro z _
    rcases z with ⟨s, r⟩
    cases s <;> cases r <;> decide

/-- The hot bars: 6♦ (the witness's own seat-bearer — diamonds at 5
make it next-up) sits bare-bottom over a nonempty deck, as does the
refugee: the SEAT BAR is the only cold hosting left at this
economy. -/
theorem cf3_bars :
    cf3.nextUp D6 = true ∧ canRaiseSB cf3 D6 = false ∧
      below D6 (cf3.piles Anchor.p3).faceUp = [] ∧
        (cf3.piles Anchor.p3).hidden ≠ [] ∧
          below H3 (cf3.piles Anchor.p5).faceUp = [] ∧
            (cf3.piles Anchor.p5).hidden ≠ [] :=
  ⟨rfl, by decide, rfl, by decide, rfl, by decide⟩

/-! ## §3. The verdict rows

THE FIFTH LANDING BANKS AS A BOARD: a cross-family pair of
rank-equal forks exists decide-grade (5♥/5♦ at cf0, 5♠/5♣ at cf3,
witnesses named, colors crossed).  THE REVERSIBLE QUILT DIES AT
BOTH DOORS, and the rows price it: at the origin the ONLY hot
black material is lone over its decks, and all three of its legal
legs are revealing commitments; at the far end the co-popped red
refugee arrives next-up into an EMPTY landing lattice — the fork's
own saturation closes the other-family door BY ORDERING at both
ends.  The no-lock pairClass theorem SURVIVES this probe. -/

theorem CrossFamilyProbe_cf0 : forkStateSB cf0 = true := cf0_fork
theorem CrossFamilyProbe_cf3 : forkStateSB cf3 = true := cf3_fork

theorem CrossFamilyProbe_cross :
    forkWitnessSB cf0 = some H5 ∧ forkWitnessSB cf3 = some S5 ∧
      H5.rank = S5.rank ∧ H5.suit.color ≠ S5.suit.color :=
  ⟨cf0_witness, cf3_witness, rfl, by decide⟩

/-- **THE PROBE LEDGER**: both landings, the origin ordering-kill
(the black 5s next-up-dead while well-seated; the only black-climb
legs one-way), and the far-end iterated freeze (the refugee hot,
bar-seated, unlandable anywhere). -/
theorem CrossFamilyProbe_verdict :
    forkStateSB cf0 = true ∧ forkStateSB cf3 = true ∧
      forkWitnessSB cf0 = some H5 ∧ forkWitnessSB cf3 = some S5 ∧
        H5.rank = S5.rank ∧ H5.suit.color ≠ S5.suit.color ∧
          cf0.nextUp S5 = false ∧ cf0.nextUp C5 = false ∧
            State.step cf0 (Move.tabToFound S5) = none ∧
              ¬ reversibleAtW cf0 (Move.tabToFound S4) ∧
                ¬ reversibleAtW cf0 (Move.tabToFound C3) ∧
                  ¬ reversibleAtW cf0 (Move.tabToTab S4 (Sum.inr H5)) ∧
                    cf3.nextUp H3 = true ∧
                      (∀ z ∈ Card.universe, cf3.canPlace H3 (Sum.inr z) = false) ∧
                        (∀ a : Anchor, cf3.canPlace H3 (Sum.inl a) = false) ∧
                          canRaiseSB cf3 D6 = false :=
  ⟨cf0_fork, cf3_fork, cf0_witness, cf3_witness, rfl, by decide,
    cf0_seats.2.2.1, cf0_seats.2.2.2.1, cf0_climbRefused.1,
    cf0_S4_liftOneWay, cf0_C3_liftOneWay, cf0_S4_seatOneWay,
    cf3_refugee.1, cf3_refugee.2.2.1, cf3_refugee.2.2.2.1, cf3_bars.2.1⟩

/-! ### The audit battery

Fresh heads `#print axioms`-audited — every row lands at
`[propext]` (decides) or `[propext, Quot.sound]` (jury-consumed
irreversibility): zero sorry, zero `Classical.choice`. -/

#print axioms cf0_fork
#print axioms cf0_forkState
#print axioms cf0_witness
#print axioms cf0_ledger
#print axioms cf0_seats
#print axioms cf0_coverFit
#print axioms cf0_cover
#print axioms cf0_S4_fit
#print axioms cf0_hot
#print axioms cf0_climbRefused
#print axioms cf0_S4_liftOneWay
#print axioms cf0_C3_liftOneWay
#print axioms cf0_S4_seatOneWay
#print axioms cf0_S4_lattice
#print axioms cf3_fork
#print axioms cf3_forkState
#print axioms cf3_witness
#print axioms cf3_ledger
#print axioms cf3_rungs
#print axioms cf3_hot
#print axioms cf3_refugee
#print axioms cf3_bars
#print axioms CrossFamilyProbe_verdict