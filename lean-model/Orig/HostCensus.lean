import Orig.BracketDecomp

/-!
# Orig.HostCensus — THE HOST-CENSUS TRANSACTION ROWS

The low-slab sufficiency program's seating ledger.  The plant owner's
central bet, made exact: ALONG A WITNESS JOURNEY (`ShufflePlayW`) out of
a saturated fork, an excursion above the fork point cannot expose any
NEW stacking-host slot — all hosting capacity is already in the tableau
at the fork, and exhumed foundation cards only RE-OCCUPY existing
seats.  This file instruments that bet with a per-cell CENSUS of
FACE-UP PILE TOPS and closes the exact per-leg TRANSACTION RULES.

THE CENSUS (`hostCensus st col i`): the number of anchors whose pile
top is a card of color family `col` at rank index `i` — defined over
`Anchor.all` and `Pile.top` (a fold whose per-anchor indicators are
the `seatInd` readers).

THE TRANSACTION TABLE (each leg, its census deltas):

* §3 THE PULL-TRANSFER (`foundToTab c (inr z)`, seated): +1 at the
  pulled card's cell `(c-family, c-index)`, −1 at the consumed host's
  cell `(z-family, z.index)` — the cells are DISTINCT (the fit pins
  `z.index = c.index + 1`).  The empty-anchor arm (`inl`) is king-only
  and mints alone: +1 at `(c-family, 12)`, no host consumed.
* §4 THE RAISE-TRANSFER (`tabToFound c`): −1 at the raised card's
  cell; the exposed below-card `z` sits OPPOSITE family, INDEX+1
  (runOK adjacency), takes over the seat (+1 at `z`'s cell), and is
  unfounded.  The REVEAL case never rides a witness journey (the
  banked `journey_tabToFound_never_reveal`); the fully-bare arm (the
  emptied seat) never rides at a non-king — closed here by THE
  EMPTY-ANCHOR PIN (§2), which kills the bare-non-king lift as an
  `irreversibleAt` (the residual named in `Orig/ForkStateUniqGate.lean`'s
  `journey_raise_shape` docstring is thereby closed); the bare-KING
  raise is the arm that genuinely rides (`tabToFound_undo_bare`).
* §5 THE CARGO-NEUTRAL ROW (`tabToTab e b`): the consumed host `z` is
  REPLACED by the exposed below-card `y` OF THE SAME CELL — `y` sits
  one rank up, opposite family to the run head `e`, hence same color
  family and same index as `z` (the identity-cell claim) — and the
  run's own top keeps being a top elsewhere (it transits from the
  source pile to the host pile): EVERY CELL'S CENSUS IS UNCHANGED.
  Degenerate arms, priced: the burn arm (run leaves a bare hidden-nil
  pile onto a seated host) burns one host with no replacement — the
  pin of §2 kills it as an `irreversibleAt`, so it never rides; the
  reveal-shaped slide is banked-barred (`journey_tabToTab_never_reveal`);
  the empty-anchor arm `inl` is king-headed (the moved run's head,
  `canPlace`'s king demand), empties its source completely, and is
  census-neutral — kings to empty anchors are reversible, and this
  arm genuinely rides.
* §6 INERTNESS: draw legs leave every pile top and every foundation
  alone (`stepDraw_piles`/`stepDraw_found`), so the census is flat
  through them; the waste letters never ride witness journeys (the
  banked `journey_never_wasteToFound` / `journey_never_wasteToTab`,
  cited by `witness_leg_letters`).

THE OWNER'S-BET LEDGER (§7): `seatMint`/`seatBurn` measure, per leg,
exactly which tops are gained into / lost from each cell (decidable
reads of the leg's own pre- and post-tops); `witness_census_ledger`
telescopes them along ANY play into the per-cell EXACT ledger
`census(end) + burns = census(start) + mints`, and over a returned
journey the mint and burn budgets CANCEL cell-for-cell
(`roundtrip_census_repay`): no hosting capacity is issued that the
arrangement (the start-state census — the arrangement PROFILE) did
not already carry or that the returned half does not reclaim.  The
per-leg CONFINEMENT (every mint sits at a letter's named cell) is the
named residue `witness_leg_mint_confined`.

Grading notes: the bar rows of §2–§5 are theorem-grade and priced
against the four commit KINDS of the program's taxonomy (raise-like /
reveal / waste-jump / draw-at-nonempty-stock): the census rows
concern seats only — rung bracketing (raise-timing) stays LowSlab's
own business, per the program's seats-vs-rungs adjudication.  Two-zone
(stock ∪ waste) cycle content is NOT rebuilt here;
`Orig/SlabEquiv.lean`'s `cycle_zone_pin` owns it upstream.

House compliance: additive leaf (`import Orig.BracketDecomp` — brings
`ShufflePlayW`/`reversibleAtW` (Orig.Fate via Orig.Combine), the step
inversions and undo rows (Orig.Irreversible), the search-integrity
rows (Orig.Integrity), `step_wf` (Orig.Reach), and the journey bars
(Orig.ForkStateUniqGate via Orig.ForkWeaker)); per-file private kit
copies; BOLD-name docstrings; `#print axioms` battery at the end; zero
`Classical.choice`; the `exfalso`/`omega` discipline honored (no bare
`omega` fired at non-arithmetic goals).
-/

/-! ## §0. The census definition and its readers -/

/-- **THE SEAT INDICATOR** — the per-cell indicator of an (optional)
pile top: 1 exactly when the topped card is a card of color family
`col` at rank index `i`. -/
def seatInd (o : Option Card) (col : Color) (i : Nat) : Nat :=
  match o with
  | none => 0
  | some c =>
      match decide (c.suit.color = col) && decide (c.rank.toIdx = i) with
      | true => 1
      | false => 0

/-- **THE HOST CENSUS** — the number of anchors whose pile top is a
card of color family `col` at rank index `i`: the per-(color family,
rank index) count of face-up pile tops over the seven seats. -/
def hostCensus (st : State) (col : Color) (i : Nat) : Nat :=
  Anchor.all.foldl (fun n a => n + seatInd (st.topOf a) col i) 0

/-! ### The fold kit (private per-file copies) -/

/-- The fold cons-unfold (rfl on the structural recursion). -/
private theorem fc_cons {F : Anchor → Nat} (x : Anchor) (t : List Anchor)
    (b : Nat) :
    List.foldl (fun n a => n + F a) b (x :: t)
      = List.foldl (fun n a => n + F a) (b + F x) t := rfl

/-- The fold nil-unfold. -/
private theorem fc_nil {F : Anchor → Nat} (b : Nat) :
    List.foldl (fun n a => n + F a) b ([] : List Anchor) = b := rfl

/-- The fold as the explicit seven-seat sum (one generic bridge). -/
private theorem foldSum_eq (F : Anchor → Nat) :
    Anchor.all.foldl (fun n a => n + F a) 0 =
      F Anchor.p0 + F Anchor.p1 + F Anchor.p2 + F Anchor.p3 +
      F Anchor.p4 + F Anchor.p5 + F Anchor.p6 := by
  rw [Anchor.all, fc_cons, fc_cons, fc_cons, fc_cons, fc_cons, fc_cons,
    fc_cons, fc_nil]
  omega

/-- The census as the explicit seven-seat sum (the additive bridge the
delta proofs expand into). -/
theorem hostCensus_eq_sum (st : State) (col : Color) (i : Nat) :
    hostCensus st col i =
      seatInd (st.topOf Anchor.p0) col i + seatInd (st.topOf Anchor.p1) col i +
      seatInd (st.topOf Anchor.p2) col i + seatInd (st.topOf Anchor.p3) col i +
      seatInd (st.topOf Anchor.p4) col i + seatInd (st.topOf Anchor.p5) col i +
      seatInd (st.topOf Anchor.p6) col i :=
  foldSum_eq _

/-- The empty-pile row: a pile with no face-up cards contributes zero
to every cell (its top is `none`).  (The bridge through
`Pile.top = lastOf faceUp` and `Pile.top_eq_lastOf_iff`,
Orig/Integrity.lean.) -/
theorem seatInd_topOf_zero {st : State} {a : Anchor}
    (h : (st.piles a).faceUp = []) (col : Color) (i : Nat) :
    seatInd (st.topOf a) col i = 0 := by
  have hnone : st.topOf a = none := by
    show lastOf ((st.piles a).faceUp) = none
    rw [h]
    rfl
  rw [hnone]
  rfl

/-- **THE LASTOF-BRIDGE** — a pile whose face-up run is a snoc tops
exactly the snocced card (`Pile.top_eq_lastOf_iff`'s ∃-front half,
`lastOf_snoc`; the working row the transfer proofs ride). -/
theorem topOf_eq_snoc {st : State} {a : Anchor} {front : List Card} {c : Card}
    (h : (st.piles a).faceUp = front ++ [c]) :
    st.topOf a = some c := by
  rw [show st.topOf a = lastOf ((st.piles a).faceUp) from rfl, h]
  exact lastOf_snoc

/-! ### The `seatInd` value lemmas -/

/-- A topped card in its own cell reads one. -/
theorem seatInd_some_one {c : Card} {col : Color} {i : Nat}
    (h1 : c.suit.color = col) (h2 : c.rank.toIdx = i) :
    seatInd (some c) col i = 1 := by
  have d1 : decide (c.suit.color = col) = true := decide_eq_true h1
  have d2 : decide (c.rank.toIdx = i) = true := decide_eq_true h2
  show (match decide (c.suit.color = col) && decide (c.rank.toIdx = i) with
    | true => 1 | false => 0) = 1
  rw [d1, d2]
  rfl

/-- A topped card of another color family reads zero in this cell. -/
theorem seatInd_zero_of_color {c : Card} {col : Color} {i : Nat}
    (h : c.suit.color ≠ col) :
    seatInd (some c) col i = 0 := by
  have d1 : decide (c.suit.color = col) = false := decide_false_of_not h
  show (match decide (c.suit.color = col) && decide (c.rank.toIdx = i) with
    | true => 1 | false => 0) = 0
  rw [d1]
  rfl

/-- A topped card of another rank index reads zero in this cell. -/
theorem seatInd_zero_of_rank {c : Card} {col : Color} {i : Nat}
    (h : c.rank.toIdx ≠ i) :
    seatInd (some c) col i = 0 := by
  have d2 : decide (c.rank.toIdx = i) = false := decide_false_of_not h
  show (match decide (c.suit.color = col) && decide (c.rank.toIdx = i) with
    | true => 1 | false => 0) = 0
  rw [d2]
  cases _hd : decide (c.suit.color = col) <;> rfl

/-- A card off the cell (either coordinate) reads zero. -/
theorem seatInd_zero_of_cell {c : Card} {col : Color} {i : Nat}
    (h : ¬(c.suit.color = col ∧ c.rank.toIdx = i)) :
    seatInd (some c) col i = 0 := by
  by_cases h1 : c.suit.color = col
  · exact seatInd_zero_of_rank (fun hcon => h ⟨h1, hcon⟩)
  · exact seatInd_zero_of_color h1

/-- The indicator is a bit: every cell-count contribution is 0 or 1. -/
theorem seatInd_le_one (o : Option Card) (col : Color) (i : Nat) :
    seatInd o col i ≤ 1 := by
  cases o with
  | none =>
      show (0 : Nat) ≤ 1
      omega
  | some c =>
      show (match decide (c.suit.color = col) && decide (c.rank.toIdx = i) with
        | true => 1 | false => 0) ≤ 1
      cases _hd : decide (c.suit.color = col) && decide (c.rank.toIdx = i) <;>
        simp

/-- The converse reader: an indicator reading of one pins the card
in its own cell. -/
theorem seatInd_cell_of_one {c : Card} {col : Color} {i : Nat}
    (h : seatInd (some c) col i = 1) :
    c.suit.color = col ∧ c.rank.toIdx = i := by
  by_cases h1 : c.suit.color = col
  · refine ⟨h1, ?_⟩
    by_cases h2 : c.rank.toIdx = i
    · exact h2
    · exact absurd h (by rw [seatInd_zero_of_rank h2]; simp)
  · exact absurd h (by rw [seatInd_zero_of_color h1]; simp)

/-- Cards of one cell contribute identically: same color family and
rank index give the same indicator at every cell. -/
theorem seatInd_eq_of_cellEq {c d : Card} (h1 : c.suit.color = d.suit.color)
    (h2 : c.rank.toIdx = d.rank.toIdx) (col : Color) (i : Nat) :
    seatInd (some c) col i = seatInd (some d) col i := by
  have e1 : decide (d.suit.color = col) = decide (c.suit.color = col) := by
    rw [h1]
  have e2 : decide (d.rank.toIdx = i) = decide (c.rank.toIdx = i) := by
    rw [h2]
  show (match decide (c.suit.color = col) && decide (c.rank.toIdx = i) with
      | true => 1 | false => 0)
    = (match decide (d.suit.color = col) && decide (d.rank.toIdx = i) with
      | true => 1 | false => 0)
  rw [e1, e2]

/-! ## §1. The touch kit — the one-seat delta commodity -/

/-- **THE ONE-SEAT TOUCH** — the census delta commodity: when `s'`
differs from `st` only in that seat `k`'s top moved from `o` to `o'`,
the per-cell census change is exactly the transfer
`census(s') + ind(old) = census(st) + ind(new)`.  (Private: the seven
position expand + per-position congr, closed by `omega`.) -/
private theorem census_touch (st s' : State) (k : Anchor) (o o' : Option Card)
    (hothers : ∀ a, a ≠ k → s'.topOf a = st.topOf a)
    (hst : st.topOf k = o) (hs' : s'.topOf k = o') :
    ∀ col i, hostCensus s' col i + seatInd o col i
      = hostCensus st col i + seatInd o' col i := by
  intro col i
  rw [hostCensus_eq_sum s' col i, hostCensus_eq_sum st col i]
  cases k with
  | p0 =>
      have b : seatInd (s'.topOf Anchor.p0) col i = seatInd o' col i := by
        rw [hs']
      have a : seatInd (st.topOf Anchor.p0) col i = seatInd o col i := by
        rw [hst]
      have c1 : seatInd (s'.topOf Anchor.p1) col i
          = seatInd (st.topOf Anchor.p1) col i :=
        congrArg (fun t => seatInd t col i) (hothers Anchor.p1 (by decide))
      have c2 : seatInd (s'.topOf Anchor.p2) col i
          = seatInd (st.topOf Anchor.p2) col i :=
        congrArg (fun t => seatInd t col i) (hothers Anchor.p2 (by decide))
      have c3 : seatInd (s'.topOf Anchor.p3) col i
          = seatInd (st.topOf Anchor.p3) col i :=
        congrArg (fun t => seatInd t col i) (hothers Anchor.p3 (by decide))
      have c4 : seatInd (s'.topOf Anchor.p4) col i
          = seatInd (st.topOf Anchor.p4) col i :=
        congrArg (fun t => seatInd t col i) (hothers Anchor.p4 (by decide))
      have c5 : seatInd (s'.topOf Anchor.p5) col i
          = seatInd (st.topOf Anchor.p5) col i :=
        congrArg (fun t => seatInd t col i) (hothers Anchor.p5 (by decide))
      have c6 : seatInd (s'.topOf Anchor.p6) col i
          = seatInd (st.topOf Anchor.p6) col i :=
        congrArg (fun t => seatInd t col i) (hothers Anchor.p6 (by decide))
      omega
  | p1 =>
      have b : seatInd (s'.topOf Anchor.p1) col i = seatInd o' col i := by
        rw [hs']
      have a : seatInd (st.topOf Anchor.p1) col i = seatInd o col i := by
        rw [hst]
      have c0 : seatInd (s'.topOf Anchor.p0) col i
          = seatInd (st.topOf Anchor.p0) col i :=
        congrArg (fun t => seatInd t col i) (hothers Anchor.p0 (by decide))
      have c2 : seatInd (s'.topOf Anchor.p2) col i
          = seatInd (st.topOf Anchor.p2) col i :=
        congrArg (fun t => seatInd t col i) (hothers Anchor.p2 (by decide))
      have c3 : seatInd (s'.topOf Anchor.p3) col i
          = seatInd (st.topOf Anchor.p3) col i :=
        congrArg (fun t => seatInd t col i) (hothers Anchor.p3 (by decide))
      have c4 : seatInd (s'.topOf Anchor.p4) col i
          = seatInd (st.topOf Anchor.p4) col i :=
        congrArg (fun t => seatInd t col i) (hothers Anchor.p4 (by decide))
      have c5 : seatInd (s'.topOf Anchor.p5) col i
          = seatInd (st.topOf Anchor.p5) col i :=
        congrArg (fun t => seatInd t col i) (hothers Anchor.p5 (by decide))
      have c6 : seatInd (s'.topOf Anchor.p6) col i
          = seatInd (st.topOf Anchor.p6) col i :=
        congrArg (fun t => seatInd t col i) (hothers Anchor.p6 (by decide))
      omega
  | p2 =>
      have b : seatInd (s'.topOf Anchor.p2) col i = seatInd o' col i := by
        rw [hs']
      have a : seatInd (st.topOf Anchor.p2) col i = seatInd o col i := by
        rw [hst]
      have c0 : seatInd (s'.topOf Anchor.p0) col i
          = seatInd (st.topOf Anchor.p0) col i :=
        congrArg (fun t => seatInd t col i) (hothers Anchor.p0 (by decide))
      have c1 : seatInd (s'.topOf Anchor.p1) col i
          = seatInd (st.topOf Anchor.p1) col i :=
        congrArg (fun t => seatInd t col i) (hothers Anchor.p1 (by decide))
      have c3 : seatInd (s'.topOf Anchor.p3) col i
          = seatInd (st.topOf Anchor.p3) col i :=
        congrArg (fun t => seatInd t col i) (hothers Anchor.p3 (by decide))
      have c4 : seatInd (s'.topOf Anchor.p4) col i
          = seatInd (st.topOf Anchor.p4) col i :=
        congrArg (fun t => seatInd t col i) (hothers Anchor.p4 (by decide))
      have c5 : seatInd (s'.topOf Anchor.p5) col i
          = seatInd (st.topOf Anchor.p5) col i :=
        congrArg (fun t => seatInd t col i) (hothers Anchor.p5 (by decide))
      have c6 : seatInd (s'.topOf Anchor.p6) col i
          = seatInd (st.topOf Anchor.p6) col i :=
        congrArg (fun t => seatInd t col i) (hothers Anchor.p6 (by decide))
      omega
  | p3 =>
      have b : seatInd (s'.topOf Anchor.p3) col i = seatInd o' col i := by
        rw [hs']
      have a : seatInd (st.topOf Anchor.p3) col i = seatInd o col i := by
        rw [hst]
      have c0 : seatInd (s'.topOf Anchor.p0) col i
          = seatInd (st.topOf Anchor.p0) col i :=
        congrArg (fun t => seatInd t col i) (hothers Anchor.p0 (by decide))
      have c1 : seatInd (s'.topOf Anchor.p1) col i
          = seatInd (st.topOf Anchor.p1) col i :=
        congrArg (fun t => seatInd t col i) (hothers Anchor.p1 (by decide))
      have c2 : seatInd (s'.topOf Anchor.p2) col i
          = seatInd (st.topOf Anchor.p2) col i :=
        congrArg (fun t => seatInd t col i) (hothers Anchor.p2 (by decide))
      have c4 : seatInd (s'.topOf Anchor.p4) col i
          = seatInd (st.topOf Anchor.p4) col i :=
        congrArg (fun t => seatInd t col i) (hothers Anchor.p4 (by decide))
      have c5 : seatInd (s'.topOf Anchor.p5) col i
          = seatInd (st.topOf Anchor.p5) col i :=
        congrArg (fun t => seatInd t col i) (hothers Anchor.p5 (by decide))
      have c6 : seatInd (s'.topOf Anchor.p6) col i
          = seatInd (st.topOf Anchor.p6) col i :=
        congrArg (fun t => seatInd t col i) (hothers Anchor.p6 (by decide))
      omega
  | p4 =>
      have b : seatInd (s'.topOf Anchor.p4) col i = seatInd o' col i := by
        rw [hs']
      have a : seatInd (st.topOf Anchor.p4) col i = seatInd o col i := by
        rw [hst]
      have c0 : seatInd (s'.topOf Anchor.p0) col i
          = seatInd (st.topOf Anchor.p0) col i :=
        congrArg (fun t => seatInd t col i) (hothers Anchor.p0 (by decide))
      have c1 : seatInd (s'.topOf Anchor.p1) col i
          = seatInd (st.topOf Anchor.p1) col i :=
        congrArg (fun t => seatInd t col i) (hothers Anchor.p1 (by decide))
      have c2 : seatInd (s'.topOf Anchor.p2) col i
          = seatInd (st.topOf Anchor.p2) col i :=
        congrArg (fun t => seatInd t col i) (hothers Anchor.p2 (by decide))
      have c3 : seatInd (s'.topOf Anchor.p3) col i
          = seatInd (st.topOf Anchor.p3) col i :=
        congrArg (fun t => seatInd t col i) (hothers Anchor.p3 (by decide))
      have c5 : seatInd (s'.topOf Anchor.p5) col i
          = seatInd (st.topOf Anchor.p5) col i :=
        congrArg (fun t => seatInd t col i) (hothers Anchor.p5 (by decide))
      have c6 : seatInd (s'.topOf Anchor.p6) col i
          = seatInd (st.topOf Anchor.p6) col i :=
        congrArg (fun t => seatInd t col i) (hothers Anchor.p6 (by decide))
      omega
  | p5 =>
      have b : seatInd (s'.topOf Anchor.p5) col i = seatInd o' col i := by
        rw [hs']
      have a : seatInd (st.topOf Anchor.p5) col i = seatInd o col i := by
        rw [hst]
      have c0 : seatInd (s'.topOf Anchor.p0) col i
          = seatInd (st.topOf Anchor.p0) col i :=
        congrArg (fun t => seatInd t col i) (hothers Anchor.p0 (by decide))
      have c1 : seatInd (s'.topOf Anchor.p1) col i
          = seatInd (st.topOf Anchor.p1) col i :=
        congrArg (fun t => seatInd t col i) (hothers Anchor.p1 (by decide))
      have c2 : seatInd (s'.topOf Anchor.p2) col i
          = seatInd (st.topOf Anchor.p2) col i :=
        congrArg (fun t => seatInd t col i) (hothers Anchor.p2 (by decide))
      have c3 : seatInd (s'.topOf Anchor.p3) col i
          = seatInd (st.topOf Anchor.p3) col i :=
        congrArg (fun t => seatInd t col i) (hothers Anchor.p3 (by decide))
      have c4 : seatInd (s'.topOf Anchor.p4) col i
          = seatInd (st.topOf Anchor.p4) col i :=
        congrArg (fun t => seatInd t col i) (hothers Anchor.p4 (by decide))
      have c6 : seatInd (s'.topOf Anchor.p6) col i
          = seatInd (st.topOf Anchor.p6) col i :=
        congrArg (fun t => seatInd t col i) (hothers Anchor.p6 (by decide))
      omega
  | p6 =>
      have b : seatInd (s'.topOf Anchor.p6) col i = seatInd o' col i := by
        rw [hs']
      have a : seatInd (st.topOf Anchor.p6) col i = seatInd o col i := by
        rw [hst]
      have c0 : seatInd (s'.topOf Anchor.p0) col i
          = seatInd (st.topOf Anchor.p0) col i :=
        congrArg (fun t => seatInd t col i) (hothers Anchor.p0 (by decide))
      have c1 : seatInd (s'.topOf Anchor.p1) col i
          = seatInd (st.topOf Anchor.p1) col i :=
        congrArg (fun t => seatInd t col i) (hothers Anchor.p1 (by decide))
      have c2 : seatInd (s'.topOf Anchor.p2) col i
          = seatInd (st.topOf Anchor.p2) col i :=
        congrArg (fun t => seatInd t col i) (hothers Anchor.p2 (by decide))
      have c3 : seatInd (s'.topOf Anchor.p3) col i
          = seatInd (st.topOf Anchor.p3) col i :=
        congrArg (fun t => seatInd t col i) (hothers Anchor.p3 (by decide))
      have c4 : seatInd (s'.topOf Anchor.p4) col i
          = seatInd (st.topOf Anchor.p4) col i :=
        congrArg (fun t => seatInd t col i) (hothers Anchor.p4 (by decide))
      have c5 : seatInd (s'.topOf Anchor.p5) col i
          = seatInd (st.topOf Anchor.p5) col i :=
        congrArg (fun t => seatInd t col i) (hothers Anchor.p5 (by decide))
      omega

/-! ## §2. THE EMPTY-ANCHOR PIN

The write analysis behind the bet's two degenerate-arm bars: once an
anchor sits FULLY EMPTY (`hidden = []`, `faceUp = []`), every card that
can ever land on it afterwards is a king-headed run (the empty-seat
placement guard `canPlace` demands a king), and appends never change
the head — so the pile's face-up head, whenever it is nonempty, is a
king forever.  A return play can therefore never rebuild the emptied
pile topped by a non-king-headed run: the BARE-NON-KING LIFT (§4) and
the BARE-SOURCE BURN SLIDE (§5) are commitments at the program's own
grain.  The former row closes, at `irreversibleAt` grade, the residual
named in `Orig/ForkStateUniqGate.lean`'s `journey_raise_shape`
docstring ("the irreversibility of the bare-non-king lift is the
write-analysis residual the future classification card owns") — this
file is that card.
-/

/-- **THE EMPTY-ANCHOR PIN** — a pile carrying no hidden cards keeps
them empty, and any face-up run standing on it is king-headed. -/
def kingAnchored (p : Pile) : Prop :=
  p.hidden = [] ∧ match p.faceUp with
    | [] => True
    | c :: _ => c.rank = Rank.king

/-- The bare removal: with no hidden deck the reveal never fires, so
removing everything leaves the exactly-empty pile. -/
private theorem afterRunRemoved_bare_pile (p : Pile) (h : p.hidden = []) :
    Pile.afterRunRemoved p [] = { p with faceUp := [] } := by
  rcases p with ⟨hd, ff⟩
  cases hd with
  | nil => rfl
  | cons g gs => exact absurd h (by simp)

/-- The removal write preserves the pin (private kit): the new head,
when there is one, is the old head. -/
private theorem pin_arr (p : Pile) (hpin : kingAnchored p) (pre : List Card)
    (hpre : ∀ y t, pre = y :: t →
      match p.faceUp with
      | [] => y.rank = Rank.king
      | v :: _ => y = v) :
    kingAnchored (Pile.afterRunRemoved p pre) := by
  cases hpre' : pre with
  | nil =>
      rw [afterRunRemoved_bare_pile p hpin.1]
      exact ⟨hpin.1, trivial⟩
  | cons y t =>
      rw [afterRunRemoved_ne (by simp)]
      refine ⟨hpin.1, ?_⟩
      have hy := hpre y t hpre'
      show y.rank = Rank.king
      cases hf : p.faceUp with
      | nil => rw [hf] at hy; exact hy
      | cons v r =>
          rw [hf] at hy
          rw [hy]
          have hh := hpin.2
          rw [hf] at hh
          exact hh

/-- The append write preserves the pin (private kit): appends never
change the head of a nonempty face-up run. -/
private theorem pin_append (p : Pile) (hpin : kingAnchored p)
    (hne : p.faceUp ≠ []) (run : List Card) :
    kingAnchored { p with faceUp := p.faceUp ++ run } := by
  obtain ⟨x, t, hxte⟩ := list_cons_of_ne_nil hne
  refine ⟨hpin.1, ?_⟩
  rw [hxte]
  show (match (x :: t) ++ run with
    | [] => True
    | c :: _ => c.rank = Rank.king)
  rw [show (x :: t) ++ run = x :: (t ++ run) from rfl]
  cases hf : p.faceUp with
  | nil => exact absurd hf (by rw [hxte]; simp)
  | cons v r =>
      rw [hf] at hxte
      have hvx : v = x := by
        injection hxte with hv _
      have hh := hpin.2
      rw [hf] at hh
      rw [hvx] at hh
      exact hh

/-- **THE PIN LEMMA** — the pin survives every legal step (the
six-letter write analysis, private kit: draws and waste-founds write
no pile; placements land king-headed (the empty-seat guard) or append
onto a located (nonempty) pile, keeping its head; the two removals
ride `pin_arr` over the `afterRunRemoved` trichotomy's no-reveal
arms; and the cargo leg composes one removal with one placement
through its own intermediate state). -/
private theorem kingAnchored_step {st s' : State} {a : Anchor} {m : Move}
    (hp : kingAnchored (st.piles a))
    (hstep : State.step st m = some s') :
    kingAnchored (s'.piles a) := by
  cases m with
  | draw =>
      have hf := stepDraw_piles hstep
      rw [show s'.piles a = st.piles a from congrFun hf a]
      exact hp
  | wasteToFound c =>
      obtain ⟨-, x, xs, -, hs⟩ := step_wasteToFound_inv hstep
      rw [hs]
      show kingAnchored ((st.setFound c.suit (st.found c.suit ++ [c])).piles a)
      exact hp
  | wasteToTab c b =>
      obtain ⟨hg, x, xs, -, hs⟩ := step_wasteToTab_inv hstep
      rw [hs]
      show kingAnchored ((st.putCard c b).piles a)
      have hcp : st.canPlace c b = true := by
        cases hc : st.canPlace c b with
        | true => rfl
        | false => rw [hc] at hg; exact absurd hg (by simp)
      cases b with
      | inl n =>
          rw [putCard_eq_inl]
          by_cases hna : n = a
          · rw [hna, setPile_piles_self]
            obtain ⟨-, hking⟩ := canPlace_inl hcp
            exact ⟨rfl, hking⟩
          · rw [setPile_piles_ne (fun hcon => hna hcon.symm)]
            exact hp
      | inr z =>
          cases hz : st.pileOfTop z with
          | none =>
              rw [show st.putCard c (Sum.inr z) = st from by
                  simp only [State.putCard, hz]]
              exact hp
          | some k =>
              rw [putCard_inr_eq hz]
              by_cases hka : k = a
              · rw [hka, setPile_piles_self]
                obtain ⟨hfk, -⟩ := pileOfTop_top hz
                rw [hka] at hfk
                exact pin_append _ hp hfk [c]
              · rw [setPile_piles_ne (fun hcon => hka hcon.symm)]
                exact hp
  | tabToFound c =>
      obtain ⟨-, k, hpa, hs⟩ := step_tabToFound_inv hstep
      rw [hs]
      show kingAnchored (if a = k then
          Pile.afterRunRemoved (st.piles k) (chop (st.piles k).faceUp)
        else st.piles a)
      by_cases hka : a = k
      · subst hka
        rw [ite_eq_left rfl]
        refine pin_arr _ hp _ ?_
        intro y t heq
        cases hf : (st.piles a).faceUp with
        | nil => rw [hf] at heq; exact absurd heq (by simp [chop])
        | cons x r =>
            cases r with
            | nil => rw [hf] at heq; exact absurd heq (by simp [chop])
            | cons w r' =>
                rw [hf] at heq
                injection heq with hxy _
                exact hxy.symm
      · rw [ite_eq_right hka]
        exact hp
  | foundToTab c b =>
      obtain ⟨_, htop, _, hcp, hs⟩ := step_foundToTab_inv hstep
      rw [hs]
      cases b with
      | inl n =>
          rw [putCard_eq_inl]
          by_cases hna : n = a
          · rw [hna, setPile_piles_self]
            obtain ⟨-, hking⟩ := canPlace_inl hcp
            exact ⟨rfl, hking⟩
          · rw [setPile_piles_ne (fun hcon => hna hcon.symm)]
            exact hp
      | inr z =>
          cases hz :
            (st.setFound c.suit (chop (st.found c.suit))).pileOfTop z with
          | none =>
              rw [show (st.setFound c.suit (chop (st.found c.suit))).putCard c
                    (Sum.inr z)
                  = st.setFound c.suit (chop (st.found c.suit)) from by
                  simp only [State.putCard, hz]]
              exact hp
          | some k =>
              rw [putCard_inr_eq hz]
              by_cases hka : k = a
              · rw [hka, setPile_piles_self]
                obtain ⟨hfk, -⟩ := pileOfTop_top hz
                rw [hka] at hfk
                exact pin_append _ hp hfk [c]
              · rw [setPile_piles_ne (fun hcon => hka hcon.symm)]
                exact hp
  | tabToTab c b =>
      obtain ⟨src, hh, hcp, _, hs⟩ := step_tabToTab_inv hstep
      rw [hs]
      have hpin1 : kingAnchored
          ((st.setPile src
              (Pile.afterRunRemoved (st.piles src)
                (below c (st.piles src).faceUp))).piles a) := by
        by_cases hsrc : src = a
        · rw [hsrc, setPile_piles_self]
          refine pin_arr _ hp _ ?_
          intro y t heq
          cases hf : (st.piles a).faceUp with
          | nil => rw [hf] at heq; exact absurd heq (by simp [below])
          | cons x r =>
              rw [hf] at heq
              rw [below_cons] at heq
              by_cases hxc : x = c
              · rw [ite_eq_left hxc] at heq
                exact absurd heq (by simp)
              · rw [ite_eq_right hxc] at heq
                injection heq with hxy _
                exact hxy.symm
        · rw [setPile_piles_ne (fun hcon => hsrc hcon.symm)]
          exact hp
      cases b with
      | inl n =>
          rw [putRun_eq_inl]
          by_cases hna : n = a
          · rw [hna, setPile_piles_self]
            obtain ⟨-, hking⟩ := canPlace_inl hcp
            obtain ⟨t, hrun⟩ := fromCard_eq_head_of_mem (pileHolding_mem hh)
            refine ⟨rfl, ?_⟩
            rw [hrun]
            exact hking
          · rw [setPile_piles_ne (fun hcon => hna hcon.symm)]
            exact hpin1
      | inr z =>
          cases hz :
            (st.setPile src
              (Pile.afterRunRemoved (st.piles src)
                (below c (st.piles src).faceUp))).pileOfTop z with
          | none =>
              rw [putRun_inr_none hz]
              exact hpin1
          | some k =>
              rw [putRun_inr_eq hz]
              by_cases hka : k = a
              · rw [hka, setPile_piles_self]
                obtain ⟨hfk, -⟩ := pileOfTop_top hz
                rw [hka] at hfk
                exact pin_append _ hpin1 hfk
                  (fromCard c (st.piles src).faceUp)
              · rw [setPile_piles_ne (fun hcon => hka hcon.symm)]
                exact hpin1


/-- The pin rides whole plays (the run-lift of the step lemma). -/
private theorem kingAnchored_run : ∀ (x : State) (play : List Move) (w : State)
    (a : Anchor), State.run x play = some w →
    kingAnchored (x.piles a) → kingAnchored (w.piles a) := by
  intro x play
  induction play generalizing x with
  | nil =>
      intro w a h hp
      have hsw : (some x : Option State) = some w := h
      injection hsw with hxw
      rw [← hxw]
      exact hp
  | cons m rest ih =>
      intro w a h hp
      obtain ⟨s₁, hstep, hrest⟩ := State.run_cons h
      exact ih s₁ w a hrest (kingAnchored_step hp hstep)

/-! ### The private kit copies for the bars -/

/-- The below/fromCard partition (private per-file copy: a pile's
face-up run splits, at the moved head, into the part below and the
run itself). -/
private theorem below_fromCard_partition (c : Card) : ∀ (l : List Card),
    below c l ++ fromCard c l = l := by
  intro l
  induction l with
  | nil => rfl
  | cons x t ih =>
      show (if x = c then [] else x :: below c t) ++
          (if x = c then x :: t else fromCard c t) = x :: t
      by_cases hxc : x = c
      · rw [ite_eq_left hxc, ite_eq_left hxc]; rfl
      · rw [ite_eq_right hxc, ite_eq_right hxc]
        show x :: (below c t ++ fromCard c t) = x :: t
        rw [ih]

/-- The junction cut: a legal run keeps its prefix legal up to any cut
point (private per-file copy; feeds `runOK_snoc_sit` at mid-run
junctions). -/
private theorem runOK_mid : ∀ (P : List Card) (c : Card) (t : List Card),
    runOK (P ++ c :: t) = true → runOK (P ++ [c]) = true := by
  intro P
  induction P with
  | nil => intro _c _t _h; rfl
  | cons x P' ih =>
      intro c t h
      cases P' with
      | nil =>
          have hx0 : (canSitOn c x && runOK (c :: t)) = true := h
          rw [Bool.and_eq_true] at hx0
          show (canSitOn c x && true) = true
          rw [hx0.1]
          rfl
      | cons y P'' =>
          have hx0 : (canSitOn y x && runOK (y :: (P'' ++ c :: t))) = true :=
            h
          rw [Bool.and_eq_true] at hx0
          show (canSitOn y x && runOK (y :: (P'' ++ [c]))) = true
          rw [hx0.1, Bool.true_and]
          exact ih c t hx0.2


/-- The junction corollary of the cut: the card directly under a
legal run's head mid-pile fits under it. -/
private theorem runOK_junction {P : List Card} {c : Card} {t : List Card}
    (hok : runOK (P ++ c :: t) = true) (hP : P ≠ []) :
    ∃ y, lastOf P = some y ∧ canSitOn c y = true :=
  runOK_snoc_sit hP (runOK_mid P c t hok)

/-- The two-color fact the identity-cell claim rides: at two values,
the family pinned opposite to one is pinned opposite to the other. -/
private theorem color_two_val {x u v : Color}
    (hxu : x ≠ u) (hxv : x ≠ v) : u = v := by
  cases x <;> cases u <;> cases v <;> simp_all

/-- The tail's last element is the appended list's last (private
per-file copy). -/
private theorem lastOf_append_tail : ∀ (front : List Card)
    {t : List Card}, t ≠ [] → lastOf (front ++ t) = lastOf t := by
  intro front
  induction front with
  | nil => intro _ _; rfl
  | cons x xs ih =>
      intro t ht
      cases xs with
      | nil =>
          obtain ⟨y, ys, hty⟩ := list_cons_of_ne_nil ht
          rw [hty]
          rfl
      | cons w ws =>
          obtain ⟨y, ys, hty⟩ := list_cons_of_ne_nil ht
          rw [hty]
          exact ih (by simp)

/-! ### The two bars -/

/-- **THE BARE-NON-KING LIFT NEVER RETURNS** — a `tabToFound` that
empties a completely bare seat (`hidden = []`, no face-up card below)
at a non-king is a commitment at the program's own commit grain: the
emptied anchor can only ever be refilled king-headed (the empty-seat
placement guard), so no return play can rebuild the origin's
non-king-headed singleton.  This closes, at `irreversibleAt` grade,
the residual named in `Orig/ForkStateUniqGate.lean`'s
`journey_raise_shape` docstring ("the irreversibility of the
bare-non-king lift is the write-analysis residual the future
classification card owns") — the §2 pin is that analysis.  THE
RAISE-TABLE'S BARE-ARM BAR. -/
theorem bare_lift_irreversibleAt {st s₁ : State} {c : Card} {k : Anchor}
    (hstep : State.step st (Move.tabToFound c) = some s₁)
    (hpa : st.pileOfTop c = some k)
    (hchop : chop (st.piles k).faceUp = [])
    (hhid : (st.piles k).hidden = [])
    (hking : c.rank ≠ Rank.king) :
    irreversibleAt st (Move.tabToFound c) := by
  obtain ⟨-, hlast⟩ := pileOfTop_top hpa
  have hsnoc : (st.piles k).faceUp = chop (st.piles k).faceUp ++ [c] :=
    lastOf_chop hlast
  rw [hchop, List.nil_append] at hsnoc
  obtain ⟨-, k', hpa', hs⟩ := step_tabToFound_inv hstep
  have hk' : k' = k := Option.some.inj (hpa'.symm.trans hpa)
  rw [hk'] at hs
  have hland : s₁.piles k = (⟨[], []⟩ : Pile) := by
    rw [hs]
    show (if k = k then
        Pile.afterRunRemoved (st.piles k) (chop (st.piles k).faceUp)
      else st.piles k) = _
    rw [ite_eq_left rfl, hchop, afterRunRemoved_bare_pile _ hhid]
    exact Pile.ext hhid rfl
  intro s₁' play hstep' hrun
  have hsame : s₁' = s₁ := Option.some.inj (hstep'.symm.trans hstep)
  rw [hsame] at hrun
  have hpstart : kingAnchored (s₁.piles k) := by
    rw [hland]
    exact ⟨rfl, trivial⟩
  have hpin := kingAnchored_run s₁ play st k hrun hpstart
  obtain ⟨-, hhead⟩ := hpin
  rw [hsnoc] at hhead
  exact hking hhead

/-- **THE BARE-SOURCE BURN SLIDE NEVER RETURNS** — a `tabToTab` whose
run leaves a completely bare (hidden-nil, nothing face-up below the
head) source pile burns one host seat with no replacement: the run
head is a non-king (its host `z` fits one rank above it, so the
head's index is at most 11), and the emptied source anchor can be
refilled only king-headed.  THE CARGO-TABLE'S DEGENERATE-ARM BAR: the
burn shape never rides a witness journey. -/
theorem bare_burn_irreversibleAt {st s₁ : State} {e z : Card} {a : Anchor}
    (hstep : State.step st (Move.tabToTab e (Sum.inr z)) = some s₁)
    (hhold : st.pileHolding e = some a)
    (hbel : below e (st.piles a).faceUp = [])
    (hhid : (st.piles a).hidden = [])
    (hzfit : canSitOn e z = true) :
    irreversibleAt st (Move.tabToTab e (Sum.inr z)) := by
  obtain ⟨hrank, -⟩ := (canSitOn_eq e z).mp hzfit
  have hking : e.rank ≠ Rank.king := by
    intro hcon
    have h12 : e.rank.toIdx = (12 : Nat) := by rw [hcon]; rfl
    have hzlt := Rank.toIdx_lt z.rank
    omega
  have hmem : e ∈ (st.piles a).faceUp := pileHolding_mem hhold
  have hface : (st.piles a).faceUp
      = fromCard e (st.piles a).faceUp := by
    have hsplit := (below_fromCard_partition e ((st.piles a).faceUp)).symm
    rw [hbel, List.nil_append] at hsplit
    exact hsplit
  obtain ⟨t, hrun⟩ := fromCard_eq_head_of_mem hmem
  have hheadface : (st.piles a).faceUp = e :: t := hface.trans hrun
  obtain ⟨src, hhold', hcp, _, hs⟩ := step_tabToTab_inv hstep
  have hsrc : some a = some src := hhold.symm.trans hhold'
  injection hsrc with hsrc'
  rw [← hsrc'] at hs
  have hS1a : (st.setPile a
      (Pile.afterRunRemoved (st.piles a)
        (below e (st.piles a).faceUp))).piles a
      = (⟨[], []⟩ : Pile) := by
    rw [setPile_piles_self, hbel, afterRunRemoved_bare_pile _ hhid]
    exact Pile.ext hhid rfl
  have hland : s₁.piles a = (⟨[], []⟩ : Pile) := by
    rw [hs]
    cases hz : (st.setPile a
        (Pile.afterRunRemoved (st.piles a)
          (below e (st.piles a).faceUp))).pileOfTop z with
    | none =>
        rw [putRun_inr_none hz]
        exact hS1a
    | some k =>
        rw [putRun_inr_eq hz]
        by_cases hka : k = a
        · exfalso
          have htop := pileOfTop_top hz
          rw [hka] at htop
          rw [hS1a] at htop
          exact htop.1 rfl
        · rw [setPile_piles_ne (fun hcon => hka hcon.symm)]
          exact hS1a
  intro s₁' play hstep' hrun
  have hsame : s₁' = s₁ := Option.some.inj (hstep'.symm.trans hstep)
  rw [hsame] at hrun
  have hpstart : kingAnchored (s₁.piles a) := by
    rw [hland]
    exact ⟨rfl, trivial⟩
  have hpin := kingAnchored_run s₁ play st a hrun hpstart
  obtain ⟨-, hhead⟩ := hpin
  rw [hheadface] at hhead
  exact hking hhead

/-! ### The witness-grade readings -/

/-- **THE BARE LIFT IS EXACTLY THE KING** (witness grade) — along a
witness journey the bare raise arm exists only for kings: the
empty-anchor pin kills the non-king, and `tabToFound_undo_bare`
(`Orig/Irreversible.lean`) witnesses the king.  Kings to empty anchors
are reversible; non-kings never return. -/
theorem witness_bare_lift_king {st s₁ : State} {c : Card} {k : Anchor}
    (hstep : State.step st (Move.tabToFound c) = some s₁)
    (hpa : st.pileOfTop c = some k)
    (hchop : chop (st.piles k).faceUp = [])
    (hhid : (st.piles k).hidden = [])
    (hrev : reversibleAtW st (Move.tabToFound c)) :
    c.rank = Rank.king := by
  by_cases hking : c.rank = Rank.king
  · exact hking
  · exact absurd hrev (not_reversibleAtW_of_irreversibleAt
      (bare_lift_irreversibleAt hstep hpa hchop hhid hking))

/-- **THE BURN SLIDE NEVER RIDES** (witness grade) — the negative form
of `bare_burn_irreversibleAt`. -/
theorem witness_tabToTab_never_burn {st s₁ : State} {e z : Card} {a : Anchor}
    (hstep : State.step st (Move.tabToTab e (Sum.inr z)) = some s₁)
    (hhold : st.pileHolding e = some a)
    (hbel : below e (st.piles a).faceUp = [])
    (hhid : (st.piles a).hidden = [])
    (hzfit : canSitOn e z = true) :
    ¬ reversibleAtW st (Move.tabToTab e (Sum.inr z)) :=
  not_reversibleAtW_of_irreversibleAt
    (bare_burn_irreversibleAt hstep hhold hbel hhid hzfit)


/-! ## §3. THE PULL-TRANSFER ROWS

The pull letter (`foundToTab`) — an exhumed foundation card re-seats
in the tableau.  The seated arm transfers one census unit from the
consumed host's cell to the pulled card's cell; the empty-anchor arm
minters alone, king-only, at the mint corner.
-/

/-- **THE PULL-TRANSFER ROW** (seated host) — a witness leg
`foundToTab c (Sum.inr z)`: the census moves one unit from the
consumed host `z`'s cell `(z-family, z.index)` to the pulled card's
cell `(c-family, c.index)`; every other cell is carried.  The two
cells are DISTINCT — the fit pins `z.index = c.index + 1`.  ROUTE:
the step inversion opens the record; `canPlace_inr` locates the host
pile `k` and carries the fit; the landing is one `setPile` append
(`putCard_inr_eq`), so exactly one seat top changes and `census_touch`
supplies the per-cell transfer; the corner arithmetic is the `seatInd`
value lemmas. -/
theorem census_foundToTab_inr {st s' : State} {c z : Card}
    (h : State.step st (Move.foundToTab c (Sum.inr z)) = some s') :
    hostCensus s' c.suit.color c.rank.toIdx
      = hostCensus st c.suit.color c.rank.toIdx + 1 ∧
    hostCensus st z.suit.color z.rank.toIdx
      = hostCensus s' z.suit.color z.rank.toIdx + 1 ∧
    ∀ col i, (col ≠ c.suit.color ∨ i ≠ c.rank.toIdx) →
      (col ≠ z.suit.color ∨ i ≠ z.rank.toIdx) →
      hostCensus s' col i = hostCensus st col i := by
  obtain ⟨_, htop, _, hcp, hs⟩ := step_foundToTab_inv h
  obtain ⟨k, hpzk, hsit⟩ := canPlace_inr hcp
  obtain ⟨hrank, -⟩ := (canSitOn_eq c z).mp hsit
  have hpzk' : (st.setFound c.suit (chop (st.found c.suit))).pileOfTop z
      = some k := hpzk
  have hold : st.topOf k = some z := (pileOfTop_top hpzk).2
  have htopk : ((st.setFound c.suit (chop (st.found c.suit))).setPile k
      { (st.setFound c.suit (chop (st.found c.suit))).piles k with
        faceUp :=
          ((st.setFound c.suit (chop (st.found c.suit))).piles k).faceUp ++ [c] }).topOf k
      = some c :=
    topOf_eq_snoc
      (st := (st.setFound c.suit (chop (st.found c.suit))).setPile k
        { (st.setFound c.suit (chop (st.found c.suit))).piles k with
          faceUp :=
            ((st.setFound c.suit (chop (st.found c.suit))).piles k).faceUp ++ [c] })
      (a := k)
      (front := ((st.setFound c.suit (chop (st.found c.suit))).piles k).faceUp)
      (c := c)
      (by rw [setPile_piles_self])
  have hothers : ∀ a', a' ≠ k → s'.topOf a' = st.topOf a' := by
    intro a' hne
    rw [hs, putCard_inr_eq hpzk', setPile_topOf_ne hne]
    rfl
  have hnew : s'.topOf k = some c := by
    rw [hs, putCard_inr_eq hpzk', htopk]
  have E := census_touch st s' k (some z) (some c) hothers hold hnew
  refine ⟨?_, ?_, ?_⟩
  · have E1 := E c.suit.color c.rank.toIdx
    have indz : seatInd (some z) c.suit.color c.rank.toIdx = 0 :=
      seatInd_zero_of_rank (fun hcon => by omega)
    have indc : seatInd (some c) c.suit.color c.rank.toIdx = 1 :=
      seatInd_some_one rfl rfl
    omega
  · have E2 := E z.suit.color z.rank.toIdx
    have indz : seatInd (some z) z.suit.color z.rank.toIdx = 1 :=
      seatInd_some_one rfl rfl
    have indc : seatInd (some c) z.suit.color z.rank.toIdx = 0 :=
      seatInd_zero_of_rank (fun hcon => by omega)
    omega
  · intro col i hc hz
    have E3 := E col i
    have indc : seatInd (some c) col i = 0 := by
      rcases hc with hc1 | hc2
      · exact seatInd_zero_of_color (Ne.symm hc1)
      · exact seatInd_zero_of_rank (Ne.symm hc2)
    have indz : seatInd (some z) col i = 0 := by
      rcases hz with hz1 | hz2
      · exact seatInd_zero_of_color (Ne.symm hz1)
      · exact seatInd_zero_of_rank (Ne.symm hz2)
    omega

/-- **THE KING-ONLY MINT** (empty-anchor pull) — a `foundToTab c
(Sum.inl n)` leg consumes no host: the empty anchor's top was `none`,
and the pulled king mints exactly one seat, at the mint corner
`(c-family, 12)`.  The empty-anchor arm is king-only by the placement
guard. -/
theorem census_foundToTab_inl {st s' : State} {c : Card} {n : Anchor}
    (h : State.step st (Move.foundToTab c (Sum.inl n)) = some s') :
    hostCensus s' c.suit.color (12 : Nat)
      = hostCensus st c.suit.color 12 + 1 ∧
    ∀ col i, (col ≠ c.suit.color ∨ i ≠ (12 : Nat)) →
      hostCensus s' col i = hostCensus st col i := by
  obtain ⟨_, htop, _, hcp, hs⟩ := step_foundToTab_inv h
  obtain ⟨hemp, hking⟩ := canPlace_inl hcp
  obtain ⟨hhd, hfu⟩ := (Pile.isEmpty_eq _).mp hemp
  have h12 : c.rank.toIdx = (12 : Nat) := by rw [hking]; rfl
  have hold : st.topOf n = none := by
    rw [show st.topOf n = lastOf ((st.piles n).faceUp) from rfl, hfu]
    rfl
  have htopn : ((st.setFound c.suit (chop (st.found c.suit))).setPile n
      (⟨[], [c]⟩ : Pile)).topOf n = some c :=
    topOf_eq_snoc
      (st := (st.setFound c.suit (chop (st.found c.suit))).setPile n
        (⟨[], [c]⟩ : Pile))
      (a := n) (front := ([] : List Card)) (c := c)
      (by rw [setPile_piles_self]; rfl)
  have hothers : ∀ a', a' ≠ n → s'.topOf a' = st.topOf a' := by
    intro a' hne
    rw [hs, putCard_eq_inl, setPile_topOf_ne hne]
    rfl
  have hnew : s'.topOf n = some c := by
    rw [hs, putCard_eq_inl, htopn]
  have E := census_touch st s' n none (some c) hothers hold hnew
  refine ⟨?_, ?_⟩
  · have E1 := E c.suit.color 12
    have indc : seatInd (some c) c.suit.color 12 = 1 :=
      seatInd_some_one rfl h12
    have indnone : seatInd (none : Option Card) c.suit.color 12 = 0 := rfl
    omega
  · intro col i hci
    have E2 := E col i
    have indc : seatInd (some c) col i = 0 := by
      rcases hci with hc1 | hc2
      · exact seatInd_zero_of_color (Ne.symm hc1)
      · exact seatInd_zero_of_rank (fun hcon => by omega)
    have indnone : seatInd (none : Option Card) col i = 0 := rfl
    omega

/-! ## §4. THE RAISE-TRANSFER ROWS

The raise letter (`tabToFound`) — a tableau card founds.  The seated
arm's census moves one unit from the raised card's cell to the exposed
below-card's cell, which sits OPPOSITE family, INDEX+1 (the runOK
adjacency) and is UNFOUNDED.  The reveal arm (the mint that exposes a
hidden card) never rides a witness journey (`journey_tabToFound_
never_reveal`, banked); the bare arm never rides at a non-king (§2's
`bare_lift_irreversibleAt`) — kings to empty anchors are reversible
(`tabToFound_undo_bare`, banked), so the bare arm genuinely rides
only for kings, where its census is a pure −1 at the king corner.
-/

/-- The reveal write (private kit): with a hidden deck present, the
full removal flips its head face-up. -/
private theorem afterRunRemoved_reveal_pile (p : Pile) (g : Card)
    (t : List Card) (h : p.hidden = g :: t) :
    Pile.afterRunRemoved p [] = (⟨t, [g]⟩ : Pile) := by
  show Pile.revealTop { p with faceUp := ([] : List Card) } = _
  rw [h]
  rfl

/-- **THE RAISE-TRANSFER ROW** (seated below-card) — a `tabToFound c`
leg with a face-up card below: the census moves one unit from the
raised card's cell `(c-family, c-index)` to the exposed below-card
`z`'s cell, which sits OPPOSITE family, one INDEX up, and is
UNFOUNDED (an arrangement-card of the tableau, never of the
foundations).  ROUTE: `pileOfTop_top` + `lastOf_chop` open the pile
as `chop ++ [c]`; `runOK_snoc_sit` (on the pile's `runOK`, the WF
clause) names the below-card `z` and its fit; the removal write is
`afterRunRemoved_ne` — one seat top changes, `census_touch` supplies
the transfer; the corner arithmetic is the `seatInd` rows. -/
theorem census_tabToFound_under {st s' : State} {c : Card} {k : Anchor}
    (hwf : st.WF)
    (hstep : State.step st (Move.tabToFound c) = some s')
    (hpa : st.pileOfTop c = some k)
    (hchop : chop (st.piles k).faceUp ≠ []) :
    hostCensus st c.suit.color c.rank.toIdx
      = hostCensus s' c.suit.color c.rank.toIdx + 1 ∧
    ∃ z, s'.topOf k = some z ∧
      z.suit.color ≠ c.suit.color ∧ z.rank.toIdx = c.rank.toIdx + 1 ∧
      z ∉ st.found z.suit ∧
      hostCensus s' z.suit.color z.rank.toIdx
        = hostCensus st z.suit.color z.rank.toIdx + 1 ∧
      ∀ col i, (col ≠ c.suit.color ∨ i ≠ c.rank.toIdx) →
        (col ≠ z.suit.color ∨ i ≠ z.rank.toIdx) →
        hostCensus s' col i = hostCensus st col i := by
  obtain ⟨hn, k', hpa', hs⟩ := step_tabToFound_inv hstep
  have hk' : k' = k := Option.some.inj (hpa'.symm.trans hpa)
  rw [hk'] at hs
  obtain ⟨-, hlast⟩ := pileOfTop_top hpa
  have hsnoc : (st.piles k).faceUp
      = chop (st.piles k).faceUp ++ [c] := lastOf_chop hlast
  have hrok : runOK (chop (st.piles k).faceUp ++ [c]) = true := by
    rw [← hsnoc]
    exact hwf.2.1 k
  obtain ⟨z, hzlast, hzfit⟩ := runOK_snoc_sit hchop hrok
  obtain ⟨hrank, hcol⟩ := (canSitOn_eq c z).mp hzfit
  have hold : st.topOf k = some c := hlast
  have hpilk : s'.piles k
      = Pile.afterRunRemoved (st.piles k) (chop (st.piles k).faceUp) := by
    rw [hs]
    show (if k = k then
        Pile.afterRunRemoved (st.piles k) (chop (st.piles k).faceUp)
      else st.piles k) = _
    rw [ite_eq_left rfl]
  have hothers : ∀ a', a' ≠ k → s'.topOf a' = st.topOf a' := by
    intro a' hne
    rw [hs]
    show Pile.top (if a' = k then
        Pile.afterRunRemoved (st.piles k) (chop (st.piles k).faceUp)
      else st.piles a') = st.topOf a'
    rw [ite_eq_right hne]
    rfl
  have hnew : s'.topOf k = some z := by
    rw [show s'.topOf k = Pile.top (s'.piles k) from rfl, hpilk,
      afterRunRemoved_ne hchop]
    show lastOf ({ st.piles k with
      faceUp := chop (st.piles k).faceUp } : Pile).faceUp = some z
    exact hzlast
  have hzmem : z ∈ (st.piles k).faceUp := by
    rw [hsnoc]
    exact List.mem_append.mpr (Or.inl (lastOf_mem hzlast))
  have hzunfound := (mem_faceUp_only hwf hzmem).2.2.2.2 z.suit
  have E := census_touch st s' k (some c) (some z) hothers hold hnew
  refine ⟨?_, ⟨z, hnew, Ne.symm hcol, hrank.symm, hzunfound, ?_, ?_⟩⟩
  · have E1 := E c.suit.color c.rank.toIdx
    have indc : seatInd (some c) c.suit.color c.rank.toIdx = 1 :=
      seatInd_some_one rfl rfl
    have indz : seatInd (some z) c.suit.color c.rank.toIdx = 0 :=
      seatInd_zero_of_rank (fun hcon => by omega)
    omega
  · have E2 := E z.suit.color z.rank.toIdx
    have indc : seatInd (some c) z.suit.color z.rank.toIdx = 0 :=
      seatInd_zero_of_rank (fun hcon => by omega)
    have indz : seatInd (some z) z.suit.color z.rank.toIdx = 1 :=
      seatInd_some_one rfl rfl
    omega
  · intro col i hc hz
    have E3 := E col i
    have indc : seatInd (some c) col i = 0 := by
      rcases hc with hc1 | hc2
      · exact seatInd_zero_of_color (Ne.symm hc1)
      · exact seatInd_zero_of_rank (Ne.symm hc2)
    have indz : seatInd (some z) col i = 0 := by
      rcases hz with hz1 | hz2
      · exact seatInd_zero_of_color (Ne.symm hz1)
      · exact seatInd_zero_of_rank (Ne.symm hz2)
    omega

/-- **THE REVEAL MINT** (step grade, never rides witness journeys) — a
`tabToFound c` leg that strips the last face-up card flips the head
`g` of the hidden deck face-up: the census moves one unit from the
raised card's cell to the FLIPPED card's cell — the one mint whose
target cell is NOT adjacency-pinned.  On witness journeys this arm is
barred outright (`journey_tabToFound_never_reveal`,
Orig/ForkStateUniqGate.lean: hidden lists are pinned along classes,
`shuffle_hiddenPinned`); the row prices the mint's exact shape for
the low-slab reveal-replay. -/
theorem census_tabToFound_reveal {st s' : State} {c : Card} {k : Anchor}
    {g : Card} {t : List Card}
    (hstep : State.step st (Move.tabToFound c) = some s')
    (hpa : st.pileOfTop c = some k)
    (hchop : chop (st.piles k).faceUp = [])
    (hhid : (st.piles k).hidden = g :: t) :
    s'.topOf k = some g ∧
    ∀ col i, hostCensus s' col i + seatInd (some c) col i
      = hostCensus st col i + seatInd (some g) col i := by
  obtain ⟨hn, k', hpa', hs⟩ := step_tabToFound_inv hstep
  have hk' : k' = k := Option.some.inj (hpa'.symm.trans hpa)
  rw [hk'] at hs
  obtain ⟨-, hlast⟩ := pileOfTop_top hpa
  have hold : st.topOf k = some c := hlast
  have hpilk : s'.piles k
      = Pile.afterRunRemoved (st.piles k) (chop (st.piles k).faceUp) := by
    rw [hs]
    show (if k = k then
        Pile.afterRunRemoved (st.piles k) (chop (st.piles k).faceUp)
      else st.piles k) = _
    rw [ite_eq_left rfl]
  have hothers : ∀ a', a' ≠ k → s'.topOf a' = st.topOf a' := by
    intro a' hne
    rw [hs]
    show Pile.top (if a' = k then
        Pile.afterRunRemoved (st.piles k) (chop (st.piles k).faceUp)
      else st.piles a') = st.topOf a'
    rw [ite_eq_right hne]
    rfl
  have hnew : s'.topOf k = some g := by
    rw [show s'.topOf k = Pile.top (s'.piles k) from rfl, hpilk, hchop,
      afterRunRemoved_reveal_pile _ g t hhid]
    show lastOf (([] : List Card) ++ [g]) = some g
    exact lastOf_snoc
  have E := census_touch st s' k (some c) (some g) hothers hold hnew
  exact ⟨hnew, E⟩

/-- **THE BARE DEPARTURE** (step grade) — a `tabToFound c` leg that
empties a completely bare seat leaves the anchor empty: a pure −1 at
the raised card's cell, nothing minted.  The witness-grade reading
(§2) pins the raised card to a king; `tabToFound_undo_bare` (banked)
is the matching re-entry. -/
theorem census_tabToFound_bare {st s' : State} {c : Card} {k : Anchor}
    (hstep : State.step st (Move.tabToFound c) = some s')
    (hpa : st.pileOfTop c = some k)
    (hchop : chop (st.piles k).faceUp = [])
    (hhid : (st.piles k).hidden = []) :
    s'.topOf k = none ∧
    hostCensus st c.suit.color c.rank.toIdx
      = hostCensus s' c.suit.color c.rank.toIdx + 1 ∧
    ∀ col i, (col ≠ c.suit.color ∨ i ≠ c.rank.toIdx) →
      hostCensus s' col i = hostCensus st col i := by
  obtain ⟨hn, k', hpa', hs⟩ := step_tabToFound_inv hstep
  have hk' : k' = k := Option.some.inj (hpa'.symm.trans hpa)
  rw [hk'] at hs
  obtain ⟨-, hlast⟩ := pileOfTop_top hpa
  have hold : st.topOf k = some c := hlast
  have hpilk : s'.piles k
      = Pile.afterRunRemoved (st.piles k) (chop (st.piles k).faceUp) := by
    rw [hs]
    show (if k = k then
        Pile.afterRunRemoved (st.piles k) (chop (st.piles k).faceUp)
      else st.piles k) = _
    rw [ite_eq_left rfl]
  have hothers : ∀ a', a' ≠ k → s'.topOf a' = st.topOf a' := by
    intro a' hne
    rw [hs]
    show Pile.top (if a' = k then
        Pile.afterRunRemoved (st.piles k) (chop (st.piles k).faceUp)
      else st.piles a') = st.topOf a'
    rw [ite_eq_right hne]
    rfl
  have hnew : s'.topOf k = none := by
    rw [show s'.topOf k = Pile.top (s'.piles k) from rfl, hpilk, hchop,
      afterRunRemoved_bare_pile _ hhid]
    show lastOf (({ st.piles k with faceUp := ([] : List Card) } : Pile).faceUp)
      = none
    rfl
  have E := census_touch st s' k (some c) none hothers hold hnew
  have indnone : seatInd (none : Option Card) c.suit.color c.rank.toIdx = 0 :=
    rfl
  refine ⟨hnew, ?_, ?_⟩
  · have E1 := E c.suit.color c.rank.toIdx
    have indc : seatInd (some c) c.suit.color c.rank.toIdx = 1 :=
      seatInd_some_one rfl rfl
    omega
  · intro col i hc
    have E2 := E col i
    have indc : seatInd (some c) col i = 0 := by
      rcases hc with hc1 | hc2
      · exact seatInd_zero_of_color (Ne.symm hc1)
      · exact seatInd_zero_of_rank (Ne.symm hc2)
    have indnone2 : seatInd (none : Option Card) col i = 0 := rfl
    omega

/-- **THE WITNESS-GRADE RAISE PACKAGE** — every `tabToFound` leg that
rides a witness journey is one of exactly two shapes: the SEATED
transfer (a face-up below-card takes the seat; its cell is the raised
card's cell's opposite-family, index+1 — the arrangement-card the
crane replays onto) or the BARE-KING departure (the emptied seat at a
king; a pure −1 at the king corner).  The reveal arm is barred
(`journey_tabToFound_never_reveal`), the bare-non-king arm is barred
(§2's pin, `witness_bare_lift_king`). -/
theorem census_tabToFound_witness {st s' : State} {c : Card} {k : Anchor}
    (hwf : st.WF)
    (hrev : reversibleAtW st (Move.tabToFound c))
    (hstep : State.step st (Move.tabToFound c) = some s')
    (hpa : st.pileOfTop c = some k) :
    (chop (st.piles k).faceUp ≠ [] ∧
      hostCensus st c.suit.color c.rank.toIdx
        = hostCensus s' c.suit.color c.rank.toIdx + 1 ∧
      ∃ z, s'.topOf k = some z ∧
        z.suit.color ≠ c.suit.color ∧ z.rank.toIdx = c.rank.toIdx + 1 ∧
        z ∉ st.found z.suit ∧
        hostCensus s' z.suit.color z.rank.toIdx
          = hostCensus st z.suit.color z.rank.toIdx + 1 ∧
        ∀ col i, (col ≠ c.suit.color ∨ i ≠ c.rank.toIdx) →
          (col ≠ z.suit.color ∨ i ≠ z.rank.toIdx) →
          hostCensus s' col i = hostCensus st col i) ∨
    (chop (st.piles k).faceUp = [] ∧ (st.piles k).hidden = [] ∧
      c.rank = Rank.king ∧
      hostCensus st c.suit.color c.rank.toIdx
        = hostCensus s' c.suit.color c.rank.toIdx + 1 ∧
      ∀ col i, (col ≠ c.suit.color ∨ i ≠ c.rank.toIdx) →
        hostCensus s' col i = hostCensus st col i) := by
  by_cases hc : chop (st.piles k).faceUp = []
  · by_cases hid : (st.piles k).hidden = []
    · have hking := witness_bare_lift_king hstep hpa hc hid hrev
      obtain ⟨htop, hdelta, hothers⟩ :=
        census_tabToFound_bare hstep hpa hc hid
      refine Or.inr ⟨hc, hid, hking, hdelta, hothers⟩
    · exact absurd hrev
        (journey_tabToFound_never_reveal hstep hpa hc hid)
  · obtain ⟨hdelta, hzpack⟩ := census_tabToFound_under hwf hstep hpa hc
    exact Or.inl ⟨hc, hdelta, hzpack⟩

/-! ## §5. THE CARGO-NEUTRAL ROWS

The cargo letter (`tabToTab`) — a run slides from one host to another.
The seated-host arm's signature content: the consumed host `z` is
REPLACED by the exposed below-card `y` OF THE SAME CELL (the
identity-cell claim), and the run's own top transits from the source
pile to the host pile — so EVERY cell's census is carried, the
letter is CENSUS-NEUTRAL.  The degenerate arms, priced: the reveal
slide is banked-barred; the burn arm (§2) never rides; the
empty-anchor arm is king-headed, empties its source completely, and
is neutral — it genuinely rides.
-/

/-- THE LANDING PIN (private kit) — at `WF` states the cargo leg's
landing search resolves exactly to the host pile the placement guard
promised: card uniqueness kills every other candidate, and the
emptied-or-revealing source cannot pretend to top `z` either. -/
private theorem tabToTab_search_pins {st : State} {e z : Card} {k a : Anchor}
    (hwf : st.WF)
    (hpa : st.pileOfTop z = some k)
    (hne : k ≠ a) :
    (st.setPile a
      (Pile.afterRunRemoved (st.piles a)
        (below e (st.piles a).faceUp))).pileOfTop z = some k := by
  have hzmem : z ∈ (st.piles k).faceUp :=
    lastOf_mem (pileOfTop_top hpa).2
  show firstWhere (fun a' => decide (
      (st.setPile a
        (Pile.afterRunRemoved (st.piles a)
          (below e (st.piles a).faceUp))).topOf a' = some z)) Anchor.all = some k
  refine firstWhere_find (Anchor.mem_all k) ?_ ?_
  · exact decide_eq_true
      (by rw [setPile_topOf_ne hne]; exact (pileOfTop_top hpa).2)
  · intro x _ hxk
    by_cases hxa : x = a
    · refine decide_false_of_not ?_
      intro hcon
      have htopk : (st.setPile a
          (Pile.afterRunRemoved (st.piles a)
            (below e (st.piles a).faceUp))).topOf x
          = Pile.top (Pile.afterRunRemoved (st.piles a)
            (below e (st.piles a).faceUp)) := by
        rw [hxa, show (st.setPile a
            (Pile.afterRunRemoved (st.piles a)
              (below e (st.piles a).faceUp))).topOf a
              = Pile.top (Pile.afterRunRemoved (st.piles a)
                (below e (st.piles a).faceUp)) from
            congrArg Pile.top setPile_piles_self]
      rw [htopk] at hcon
      cases hpre : below e (st.piles a).faceUp with
      | nil =>
          by_cases hhid : (st.piles a).hidden = []
          · rw [hpre, afterRunRemoved_bare_pile _ hhid] at hcon
            rw [show Pile.top ({ st.piles a with
                faceUp := ([] : List Card) } : Pile) = none from rfl] at hcon
            exact absurd hcon (by simp)
          · obtain ⟨g, t, hhid⟩ := list_cons_of_ne_nil hhid
            rw [hpre, afterRunRemoved_reveal_pile _ g t hhid] at hcon
            rw [show Pile.top ((⟨t, [g]⟩ : Pile)) = some g from rfl] at hcon
            have hgeq : g = z := Option.some.inj hcon
            have hzin : z ∈ (st.piles a).hidden := by
              rw [← hgeq, hhid]
              exact List.mem_cons_self ..
            exact (mem_faceUp_unique hwf hzmem a (Ne.symm hne)).2.1 hzin
      | cons y ys =>
          rw [afterRunRemoved_ne
              (by rw [hpre]; simp)] at hcon
          rw [show Pile.top ({ st.piles a with
              faceUp := below e (st.piles a).faceUp } : Pile)
              = lastOf (below e (st.piles a).faceUp) from rfl] at hcon
          have hzin : z ∈ below e (st.piles a).faceUp := lastOf_mem hcon
          have hzmema : z ∈ (st.piles a).faceUp := mem_below _ hzin
          exact (mem_faceUp_unique hwf hzmem a (Ne.symm hne)).1 hzmema
    · refine decide_false_of_not ?_
      intro hcon
      rw [setPile_topOf_ne hxa] at hcon
      have hfound := (pileOfTop_eq_some_iff hwf).2 hcon
      exact hxk (Option.some.inj (hpa.symm.trans hfound)).symm

/-- **THE CARGO-NEUTRAL ROW** (seated host, the identity-cell claim) —
a `tabToTab e (Sum.inr z)` leg with a face-up card below the run head:
the host `z`'s seat is taken over by the run, whose bottom transit
exposes the below-card `y` — `y` sits one rank up, opposite family to
`e`, hence THE SAME COLOR FAMILY and THE SAME INDEX as the consumed
host `z` (the identity cell), `y` is unfounded (an arrangement-card),
the run's own top keeps being a top (it transits from the source pile
to the host pile), and EVERY CELL'S CENSUS IS UNCHANGED.  ROUTE: the
step inversion opens the two-write record (the removal at the source,
the placement at the host); `tabToTab_search_pins` holds the landing
at the promised host pile `k` (WF uniqueness); `runOK_junction` (the
runOK cut, private kit) names the below-card and its fit; the two
writes are two one-seat touches (`census_touch` twice — through the
leg's own intermediate state), and the identity cell cancels them. -/
theorem census_tabToTab_under {st s' : State} {e z : Card} {k a : Anchor}
    (hwf : st.WF)
    (hstep : State.step st (Move.tabToTab e (Sum.inr z)) = some s')
    (hhold : st.pileHolding e = some a)
    (hpa : st.pileOfTop z = some k)
    (hfit : canSitOn e z = true)
    (hpre : below e (st.piles a).faceUp ≠ []) :
    ∃ y, lastOf (below e (st.piles a).faceUp) = some y ∧
      canSitOn e y = true ∧
      y.suit.color = z.suit.color ∧ y.rank.toIdx = z.rank.toIdx ∧
      y ∉ st.found y.suit ∧
      ∃ TA, lastOf (fromCard e (st.piles a).faceUp) = some TA ∧
        st.topOf a = some TA ∧
        s'.topOf a = some y ∧
        s'.topOf k = some TA ∧
        (∀ col i, hostCensus s' col i = hostCensus st col i) := by
  obtain ⟨src, hh, hcp, hrunne, hs⟩ := step_tabToTab_inv hstep
  have hsrc : some a = some src := hhold.symm.trans hh
  injection hsrc with hsrc'
  rw [← hsrc'] at hs
  have hmem : e ∈ (st.piles a).faceUp := pileHolding_mem hhold
  have hkane : k ≠ a := fun hcon =>
    canPlace_inr_target_pile_ne hwf hcp hmem (by rw [← hcon]; exact hpa)
  have hzmem : z ∈ (st.piles k).faceUp :=
    lastOf_mem (pileOfTop_top hpa).2
  obtain ⟨hrank, hcol⟩ := (canSitOn_eq e z).mp hfit
  have hsplit := (below_fromCard_partition e ((st.piles a).faceUp)).symm
  obtain ⟨t, hrunform⟩ := fromCard_eq_head_of_mem hmem
  have hface_split : (st.piles a).faceUp
      = below e (st.piles a).faceUp ++ (e :: t) := by
    rw [hrunform.symm]
    exact hsplit
  have hrunne : (fromCard e (st.piles a).faceUp) ≠ [] := by
    rw [hrunform]; simp
  obtain ⟨TA, hTA⟩ := lastOf_exists hrunne
  have hTAold : st.topOf a = some TA := by
    rw [show st.topOf a = lastOf ((st.piles a).faceUp) from rfl, hface_split,
      ← hrunform]
    exact (lastOf_append_tail _ hrunne).trans hTA
  obtain ⟨y, hy_last, hyfit⟩ :=
    runOK_junction (P := below e (st.piles a).faceUp) (c := e) (t := t)
      (by rw [← hface_split]; exact hwf.2.1 a) hpre
  obtain ⟨hranky, hcoly⟩ := (canSitOn_eq e y).mp hyfit
  have hycol : y.suit.color = z.suit.color := color_two_val hcoly hcol
  have hyunf : y ∉ st.found y.suit := by
    have hymem : y ∈ (st.piles a).faceUp :=
      mem_below _ (lastOf_mem hy_last)
    exact (mem_faceUp_only hwf hymem).2.2.2.2 y.suit
  -- the two writes:
  have hpin : (st.setPile a
      (Pile.afterRunRemoved (st.piles a)
        (below e (st.piles a).faceUp))).pileOfTop z = some k :=
    tabToTab_search_pins hwf hpa hkane
  have hS1a : (st.setPile a
      (Pile.afterRunRemoved (st.piles a)
        (below e (st.piles a).faceUp))).topOf a = some y := by
    rw [show (st.setPile a (Pile.afterRunRemoved (st.piles a)
          (below e (st.piles a).faceUp))).topOf a
          = Pile.top (Pile.afterRunRemoved (st.piles a)
              (below e (st.piles a).faceUp)) from
        congrArg Pile.top setPile_piles_self,
      afterRunRemoved_ne hpre]
    show lastOf ({ st.piles a with
      faceUp := below e (st.piles a).faceUp } : Pile).faceUp = some y
    exact hy_last
  have hothers1 : ∀ x, x ≠ a →
      (st.setPile a
        (Pile.afterRunRemoved (st.piles a)
          (below e (st.piles a).faceUp))).topOf x = st.topOf x :=
    fun x hx => setPile_topOf_ne hx
  have E1 := census_touch st (st.setPile a
      (Pile.afterRunRemoved (st.piles a)
        (below e (st.piles a).faceUp))) a (some TA) (some y) hothers1 hTAold hS1a
  have hS1kold : (st.setPile a
      (Pile.afterRunRemoved (st.piles a)
        (below e (st.piles a).faceUp))).topOf k = some z := by
    rw [setPile_topOf_ne hkane]
    exact (pileOfTop_top hpa).2
  have hputrun : s' = (st.setPile a
      (Pile.afterRunRemoved (st.piles a)
        (below e (st.piles a).faceUp))).setPile k
      { (st.setPile a
          (Pile.afterRunRemoved (st.piles a)
            (below e (st.piles a).faceUp))).piles k with
        faceUp := ((st.setPile a
          (Pile.afterRunRemoved (st.piles a)
            (below e (st.piles a).faceUp))).piles k).faceUp ++
          fromCard e (st.piles a).faceUp } := by
    rw [hs, putRun_inr_eq hpin]
  have hothers2 : ∀ x, x ≠ k → s'.topOf x = (st.setPile a
      (Pile.afterRunRemoved (st.piles a)
        (below e (st.piles a).faceUp))).topOf x := by
    intro x hx
    rw [hputrun, setPile_topOf_ne hx]
  have hnewk : s'.topOf k = some TA := by
    rw [show s'.topOf k = Pile.top (s'.piles k) from rfl, hputrun,
      setPile_piles_self]
    show lastOf (((st.setPile a
        (Pile.afterRunRemoved (st.piles a)
          (below e (st.piles a).faceUp))).piles k).faceUp ++
        fromCard e (st.piles a).faceUp) = some TA
    exact (lastOf_append_tail _ hrunne).trans hTA
  have E2 := census_touch (st.setPile a
      (Pile.afterRunRemoved (st.piles a)
        (below e (st.piles a).faceUp))) s' k (some z) (some TA) hothers2
      hS1kold hnewk
  have hS1a_s' : s'.topOf a = some y := by
    have := hothers2 a (Ne.symm hkane)
    rw [this]
    exact hS1a
  refine ⟨y, hy_last, hyfit, hycol, ?_, hyunf, TA, hTA, hTAold, hS1a_s',
    hnewk, ?_⟩
  · omega
  · intro col i
    have C1 := E1 col i
    have C2 := E2 col i
    have hyzi : seatInd (some y) col i = seatInd (some z) col i :=
      seatInd_eq_of_cellEq hycol (by omega) col i
    omega

/-- **THE BURN SLIDE** (step grade; never rides witness journeys) — a
`tabToTab e (Sum.inr z)` leg whose run leaves a completely bare
(hidden-nil, nothing below the head) source pile burns one host seat
with no replacement: a pure −1 at the consumed host's cell, the source
anchor emptied.  §2's `bare_burn_irreversibleAt` kills this arm on
witness journeys; the row prices its exact census for the write
analysis. -/
theorem census_tabToTab_burn {st s' : State} {e z : Card} {k a : Anchor}
    (hwf : st.WF)
    (hstep : State.step st (Move.tabToTab e (Sum.inr z)) = some s')
    (hhold : st.pileHolding e = some a)
    (hpa : st.pileOfTop z = some k)
    (hpre : below e (st.piles a).faceUp = [])
    (hhid : (st.piles a).hidden = []) :
    s'.topOf a = none ∧
    hostCensus st z.suit.color z.rank.toIdx
      = hostCensus s' z.suit.color z.rank.toIdx + 1 ∧
    ∀ col i, (col ≠ z.suit.color ∨ i ≠ z.rank.toIdx) →
      hostCensus s' col i = hostCensus st col i := by
  obtain ⟨src, hh, hcp, hrunne, hs⟩ := step_tabToTab_inv hstep
  have hsrc : some a = some src := hhold.symm.trans hh
  injection hsrc with hsrc'
  rw [← hsrc'] at hs
  have hmem : e ∈ (st.piles a).faceUp := pileHolding_mem hhold
  have hkane : k ≠ a := fun hcon =>
    canPlace_inr_target_pile_ne hwf hcp hmem (by rw [← hcon]; exact hpa)
  have hsplit := (below_fromCard_partition e ((st.piles a).faceUp)).symm
  obtain ⟨t, hrform⟩ := fromCard_eq_head_of_mem hmem
  have hrunne' : (fromCard e (st.piles a).faceUp) ≠ [] := by
    rw [hrform]; simp
  obtain ⟨TA, hTA⟩ := lastOf_exists hrunne'
  have hface_split : (st.piles a).faceUp
      = below e (st.piles a).faceUp ++ (e :: t) := by
    rw [hrform.symm]
    exact hsplit
  have hTAold : st.topOf a = some TA := by
    rw [show st.topOf a = lastOf ((st.piles a).faceUp) from rfl, hface_split,
      ← hrform]
    exact (lastOf_append_tail _ hrunne').trans hTA
  have hpin : (st.setPile a
      (Pile.afterRunRemoved (st.piles a)
        (below e (st.piles a).faceUp))).pileOfTop z = some k :=
    tabToTab_search_pins hwf hpa hkane
  have hS1a : (st.setPile a
      (Pile.afterRunRemoved (st.piles a)
        (below e (st.piles a).faceUp))).topOf a = none := by
    rw [show (st.setPile a (Pile.afterRunRemoved (st.piles a)
          (below e (st.piles a).faceUp))).topOf a
          = Pile.top (Pile.afterRunRemoved (st.piles a)
              (below e (st.piles a).faceUp)) from
        congrArg Pile.top setPile_piles_self, hpre,
      afterRunRemoved_bare_pile _ hhid]
    show lastOf (({ st.piles a with
        faceUp := ([] : List Card) } : Pile).faceUp) = none
    rfl
  have hothers1 : ∀ x, x ≠ a →
      (st.setPile a
        (Pile.afterRunRemoved (st.piles a)
          (below e (st.piles a).faceUp))).topOf x = st.topOf x :=
    fun x hx => setPile_topOf_ne hx
  have E1 := census_touch st (st.setPile a
      (Pile.afterRunRemoved (st.piles a)
        (below e (st.piles a).faceUp))) a (some TA) none hothers1 hTAold hS1a
  have hS1kold : (st.setPile a
      (Pile.afterRunRemoved (st.piles a)
        (below e (st.piles a).faceUp))).topOf k = some z := by
    rw [setPile_topOf_ne hkane]
    exact (pileOfTop_top hpa).2
  have hputrun : s' = (st.setPile a
      (Pile.afterRunRemoved (st.piles a)
        (below e (st.piles a).faceUp))).setPile k
      { (st.setPile a
          (Pile.afterRunRemoved (st.piles a)
            (below e (st.piles a).faceUp))).piles k with
        faceUp := ((st.setPile a
          (Pile.afterRunRemoved (st.piles a)
            (below e (st.piles a).faceUp))).piles k).faceUp ++
          fromCard e (st.piles a).faceUp } := by
    rw [hs, putRun_inr_eq hpin]
  have hothers2 : ∀ x, x ≠ k → s'.topOf x = (st.setPile a
      (Pile.afterRunRemoved (st.piles a)
        (below e (st.piles a).faceUp))).topOf x := by
    intro x hx
    rw [hputrun, setPile_topOf_ne hx]
  have hnewk : s'.topOf k = some TA := by
    rw [show s'.topOf k = Pile.top (s'.piles k) from rfl, hputrun,
      setPile_piles_self]
    show lastOf (((st.setPile a
        (Pile.afterRunRemoved (st.piles a)
          (below e (st.piles a).faceUp))).piles k).faceUp ++
        fromCard e (st.piles a).faceUp) = some TA
    exact (lastOf_append_tail _ hrunne').trans hTA
  have E2 := census_touch (st.setPile a
      (Pile.afterRunRemoved (st.piles a)
        (below e (st.piles a).faceUp))) s' k (some z) (some TA) hothers2
      hS1kold hnewk
  have hS1a_s' : s'.topOf a = none := by
    have := hothers2 a (Ne.symm hkane)
    rw [this]
    exact hS1a
  refine ⟨hS1a_s', ?_, ?_⟩
  · have E1z := E1 z.suit.color z.rank.toIdx
    have E2z := E2 z.suit.color z.rank.toIdx
    have indz : seatInd (some z) z.suit.color z.rank.toIdx = 1 :=
      seatInd_some_one rfl rfl
    have indTnone : seatInd (none : Option Card) z.suit.color z.rank.toIdx = 0 :=
      rfl
    omega
  · intro col i hc
    have hz0 : seatInd (some z) col i = 0 := by
      rcases hc with hc1 | hc2
      · exact seatInd_zero_of_color (Ne.symm hc1)
      · exact seatInd_zero_of_rank (Ne.symm hc2)
    have hn0 : seatInd (none : Option Card) col i = 0 := rfl
    have h3 : hostCensus s' col i + seatInd (some z) col i
        = hostCensus st col i + seatInd (none : Option Card) col i :=
      (E2 col i).trans (E1 col i)
    rw [hz0, hn0, Nat.add_zero, Nat.add_zero] at h3
    exact h3

/-- **THE REVEAL SLIDE** (step grade; never rides witness journeys) —
a `tabToTab e (Sum.inr z)` leg stripping the last face-up card over a
hidden deck: the census equation moves one unit from the consumed
host's cell to the FLIPPED card's cell.  Banked-barred on witness
journeys (`journey_tabToTab_never_reveal`; hidden lists are class
invariants, `shuffle_hiddenPinned`). -/
theorem census_tabToTab_reveal {st s' : State} {e z g : Card} {k a : Anchor}
    {t' : List Card}
    (hwf : st.WF)
    (hstep : State.step st (Move.tabToTab e (Sum.inr z)) = some s')
    (hhold : st.pileHolding e = some a)
    (hpa : st.pileOfTop z = some k)
    (hpre : below e (st.piles a).faceUp = [])
    (hhid : (st.piles a).hidden = g :: t') :
    (s'.topOf a = some g) ∧
    ∀ col i, hostCensus s' col i + seatInd (some z) col i
      = hostCensus st col i + seatInd (some g) col i := by
  obtain ⟨src, hh, hcp, hrunne, hs⟩ := step_tabToTab_inv hstep
  have hsrc : some a = some src := hhold.symm.trans hh
  injection hsrc with hsrc'
  rw [← hsrc'] at hs
  have hmem : e ∈ (st.piles a).faceUp := pileHolding_mem hhold
  have hkane : k ≠ a := fun hcon =>
    canPlace_inr_target_pile_ne hwf hcp hmem (by rw [← hcon]; exact hpa)
  have hsplit := (below_fromCard_partition e ((st.piles a).faceUp)).symm
  obtain ⟨t, hrform⟩ := fromCard_eq_head_of_mem hmem
  have hrunne' : (fromCard e (st.piles a).faceUp) ≠ [] := by
    rw [hrform]; simp
  obtain ⟨TA, hTA⟩ := lastOf_exists hrunne'
  have hface_split : (st.piles a).faceUp
      = below e (st.piles a).faceUp ++ (e :: t) := by
    rw [hrform.symm]
    exact hsplit
  have hTAold : st.topOf a = some TA := by
    rw [show st.topOf a = lastOf ((st.piles a).faceUp) from rfl, hface_split,
      ← hrform]
    exact (lastOf_append_tail _ hrunne').trans hTA
  have hpin : (st.setPile a
      (Pile.afterRunRemoved (st.piles a)
        (below e (st.piles a).faceUp))).pileOfTop z = some k :=
    tabToTab_search_pins hwf hpa hkane
  have hS1a : (st.setPile a
      (Pile.afterRunRemoved (st.piles a)
        (below e (st.piles a).faceUp))).topOf a = some g := by
    rw [show (st.setPile a (Pile.afterRunRemoved (st.piles a)
          (below e (st.piles a).faceUp))).topOf a
          = Pile.top (Pile.afterRunRemoved (st.piles a)
              (below e (st.piles a).faceUp)) from
        congrArg Pile.top setPile_piles_self, hpre,
      afterRunRemoved_reveal_pile _ g t' hhid]
    show lastOf (([] : List Card) ++ [g]) = some g
    exact lastOf_snoc
  have hothers1 : ∀ x, x ≠ a →
      (st.setPile a
        (Pile.afterRunRemoved (st.piles a)
          (below e (st.piles a).faceUp))).topOf x = st.topOf x :=
    fun x hx => setPile_topOf_ne hx
  have E1 := census_touch st (st.setPile a
      (Pile.afterRunRemoved (st.piles a)
        (below e (st.piles a).faceUp))) a (some TA) (some g) hothers1 hTAold
      hS1a
  have hS1kold : (st.setPile a
      (Pile.afterRunRemoved (st.piles a)
        (below e (st.piles a).faceUp))).topOf k = some z := by
    rw [setPile_topOf_ne hkane]
    exact (pileOfTop_top hpa).2
  have hputrun : s' = (st.setPile a
      (Pile.afterRunRemoved (st.piles a)
        (below e (st.piles a).faceUp))).setPile k
      { (st.setPile a
          (Pile.afterRunRemoved (st.piles a)
            (below e (st.piles a).faceUp))).piles k with
        faceUp := ((st.setPile a
          (Pile.afterRunRemoved (st.piles a)
            (below e (st.piles a).faceUp))).piles k).faceUp ++
          fromCard e (st.piles a).faceUp } := by
    rw [hs, putRun_inr_eq hpin]
  have hothers2 : ∀ x, x ≠ k → s'.topOf x = (st.setPile a
      (Pile.afterRunRemoved (st.piles a)
        (below e (st.piles a).faceUp))).topOf x := by
    intro x hx
    rw [hputrun, setPile_topOf_ne hx]
  have hnewk : s'.topOf k = some TA := by
    rw [show s'.topOf k = Pile.top (s'.piles k) from rfl, hputrun,
      setPile_piles_self]
    show lastOf (((st.setPile a
        (Pile.afterRunRemoved (st.piles a)
          (below e (st.piles a).faceUp))).piles k).faceUp ++
        fromCard e (st.piles a).faceUp) = some TA
    exact (lastOf_append_tail _ hrunne').trans hTA
  have E2 := census_touch (st.setPile a
      (Pile.afterRunRemoved (st.piles a)
        (below e (st.piles a).faceUp))) s' k (some z) (some TA) hothers2
      hS1kold hnewk
  have hS1a_s' : s'.topOf a = some g := by
    have := hothers2 a (Ne.symm hkane)
    rw [this]
    exact hS1a
  refine ⟨hS1a_s', ?_⟩
  intro col i
  have C1 := E1 col i
  have C2 := E2 col i
  omega

/-- **THE EMPTY-ANCHOR CARGO** (witness grade; the king-headed arm that
genuinely rides) — a `tabToTab e (Sum.inl n)` leg on a witness journey:
king-headed by the placement guard, its source left completely bare
(the reveal never rides; no card fits under a king, so the run head
sits at the pile's bottom), the emptied source anchor's top vanishes
while the target anchor tops the transiting run — EVERY CELL'S CENSUS
UNCHANGED.  Kings to empty anchors are reversible; this arm is the
cargo letter's lawful degenerate shape. -/
theorem census_tabToTab_inl {st s' : State} {e : Card} {n a : Anchor}
    (hwf : st.WF)
    (hstep : State.step st (Move.tabToTab e (Sum.inl n)) = some s')
    (hhold : st.pileHolding e = some a)
    (hrev : reversibleAtW st (Move.tabToTab e (Sum.inl n))) :
    e.rank = Rank.king ∧
    (st.piles a).hidden = [] ∧
    below e (st.piles a).faceUp = [] ∧
    s'.topOf a = none ∧
    ∃ TA, lastOf (fromCard e (st.piles a).faceUp) = some TA ∧
      s'.topOf n = some TA ∧
      (∀ col i, hostCensus s' col i = hostCensus st col i) := by
  obtain ⟨src, hh, hcp, hrunne, hs⟩ := step_tabToTab_inv hstep
  have hsrc : some a = some src := hhold.symm.trans hh
  injection hsrc with hsrc'
  rw [← hsrc'] at hs
  have hmem : e ∈ (st.piles a).faceUp := pileHolding_mem hhold
  obtain ⟨hemp, hking⟩ := canPlace_inl hcp
  obtain ⟨hhidn, hfundn⟩ := (Pile.isEmpty_eq _).mp hemp
  have hne_na : n ≠ a := canPlace_inl_target_pile_ne hcp hmem
  have hsplit := (below_fromCard_partition e ((st.piles a).faceUp)).symm
  obtain ⟨t, hrform⟩ := fromCard_eq_head_of_mem hmem
  have hrunne' : (fromCard e (st.piles a).faceUp) ≠ [] := by
    rw [hrform]; simp
  obtain ⟨TA, hTA⟩ := lastOf_exists hrunne'
  have hface_split : (st.piles a).faceUp
      = below e (st.piles a).faceUp ++ (e :: t) := by
    rw [hrform.symm]
    exact hsplit
  have hTAold : st.topOf a = some TA := by
    rw [show st.topOf a = lastOf ((st.piles a).faceUp) from rfl, hface_split,
      ← hrform]
    exact (lastOf_append_tail _ hrunne').trans hTA
  -- no card fits under a king: the below-part is empty
  have hbelnil : below e (st.piles a).faceUp = [] := by
    by_cases hbel : below e (st.piles a).faceUp = []
    · exact hbel
    · exfalso
      obtain ⟨y, -, hyfit⟩ :=
        runOK_junction (P := below e (st.piles a).faceUp) (c := e) (t := t)
          (by rw [← hface_split]; exact hwf.2.1 a) hbel
      obtain ⟨hranky, -⟩ := (canSitOn_eq e y).mp hyfit
      have h12 : e.rank.toIdx = (12 : Nat) := by rw [hking]; rfl
      have hlt := Rank.toIdx_lt y.rank
      omega
  -- the reveal never rides: the hidden deck is empty
  have hhid : (st.piles a).hidden = [] := by
    by_cases hid : (st.piles a).hidden = []
    · exact hid
    · exact absurd hrev
        (journey_tabToTab_never_reveal hstep hhold hbelnil hid)
  -- the source pile is fully empty after W1:
  have hS1a : (st.setPile a
      (Pile.afterRunRemoved (st.piles a)
        (below e (st.piles a).faceUp))).topOf a = none := by
    rw [show (st.setPile a (Pile.afterRunRemoved (st.piles a)
          (below e (st.piles a).faceUp))).topOf a
          = Pile.top (Pile.afterRunRemoved (st.piles a)
              (below e (st.piles a).faceUp)) from
        congrArg Pile.top setPile_piles_self, hbelnil,
      afterRunRemoved_bare_pile _ hhid]
    show lastOf (({ st.piles a with
        faceUp := ([] : List Card) } : Pile).faceUp) = none
    rfl
  have hothers1 : ∀ x, x ≠ a →
      (st.setPile a
        (Pile.afterRunRemoved (st.piles a)
          (below e (st.piles a).faceUp))).topOf x = st.topOf x :=
    fun x hx => setPile_topOf_ne hx
  have E1 := census_touch st (st.setPile a
      (Pile.afterRunRemoved (st.piles a)
        (below e (st.piles a).faceUp))) a (some TA) none hothers1 hTAold hS1a
  -- the landing:
  have hS1n : (st.setPile a
      (Pile.afterRunRemoved (st.piles a)
        (below e (st.piles a).faceUp))).topOf n = none := by
    rw [setPile_topOf_ne hne_na]
    rw [show st.topOf n = lastOf ((st.piles n).faceUp) from rfl, hfundn]
    rfl
  have hputrun : s' = (st.setPile a
      (Pile.afterRunRemoved (st.piles a)
        (below e (st.piles a).faceUp))).setPile n
      (⟨[], fromCard e (st.piles a).faceUp⟩ : Pile) := by
    rw [hs, putRun_eq_inl]
  have hothers2 : ∀ x, x ≠ n → s'.topOf x = (st.setPile a
      (Pile.afterRunRemoved (st.piles a)
        (below e (st.piles a).faceUp))).topOf x := by
    intro x hx
    rw [hputrun, setPile_topOf_ne hx]
  have hnewn : s'.topOf n = some TA := by
    rw [show s'.topOf n = Pile.top (s'.piles n) from rfl, hputrun,
      setPile_piles_self]
    show lastOf (fromCard e (st.piles a).faceUp) = some TA
    exact hTA
  have E2 := census_touch (st.setPile a
      (Pile.afterRunRemoved (st.piles a)
        (below e (st.piles a).faceUp))) s' n none (some TA) hothers2 hS1n
      hnewn
  have hS1a_s' : s'.topOf a = none := by
    have := hothers2 a (Ne.symm hne_na)
    rw [this]
    exact hS1a
  refine ⟨hking, hhid, hbelnil, hS1a_s', TA, hTA, hnewn, ?_⟩
  intro col i
  have C1 := E1 col i
  have C2 := E2 col i
  have indnone : seatInd (none : Option Card) col i = 0 := rfl
  omega

/-- **THE WITNESS-GRADE SEATED-CARGO PACKAGE** — every seated `tabToTab`
leg that rides a witness journey is the identity-cell neutral transfer:
the burn arm never rides (§2's pin), and the reveal arm is banked-
barred, so the below-part is nonempty and `census_tabToTab_under`
delivers the idcell claim. -/
theorem census_tabToTab_inr_witness {st s' : State} {e z : Card} {k a : Anchor}
    (hwf : st.WF)
    (hrev : reversibleAtW st (Move.tabToTab e (Sum.inr z)))
    (hstep : State.step st (Move.tabToTab e (Sum.inr z)) = some s')
    (hhold : st.pileHolding e = some a)
    (hpa : st.pileOfTop z = some k)
    (hfit : canSitOn e z = true) :
    below e (st.piles a).faceUp ≠ [] ∧
    ∃ y, lastOf (below e (st.piles a).faceUp) = some y ∧
      canSitOn e y = true ∧
      y.suit.color = z.suit.color ∧ y.rank.toIdx = z.rank.toIdx ∧
      y ∉ st.found y.suit ∧
      ∃ TA, lastOf (fromCard e (st.piles a).faceUp) = some TA ∧
        st.topOf a = some TA ∧
        s'.topOf a = some y ∧
        s'.topOf k = some TA ∧
        (∀ col i, hostCensus s' col i = hostCensus st col i) := by
  by_cases hbel : below e (st.piles a).faceUp = []
  · exfalso
    by_cases hid : (st.piles a).hidden = []
    · exact absurd hrev
        (witness_tabToTab_never_burn hstep hhold hbel hid hfit)
    · exact absurd hrev
        (journey_tabToTab_never_reveal hstep hhold hbel hid)
  · obtain ⟨y, hy⟩ := census_tabToTab_under hwf hstep hhold hpa hfit hbel
    exact ⟨hbel, y, hy⟩

/-! ## §6. THE INERTNESS ROWS

The census is flat through the two inert letters: draws touch no
pile and no foundation (`stepDraw_piles` / `stepDraw_found`, banked),
and the waste letters never ride witness journeys at all (the banked
`journey_never_wasteToFound` / `journey_never_wasteToTab`).
-/

/-- **THE WITNESS-GRADE LEG ALPHABET** — the waste letters never ride
witness journeys, so every leg is one of the four census-relevant
letters: draw (inert, §6), raise (§4), pull (§3), cargo (§5). -/
theorem witness_leg_letters {st s₁ : State} {m : Move}
    (hstep : State.step st m = some s₁)
    (hrev : reversibleAtW st m) :
    m = Move.draw ∨ (∃ c, m = Move.tabToFound c) ∨
      (∃ c b, m = Move.foundToTab c b) ∨ (∃ c b, m = Move.tabToTab c b) := by
  cases m with
  | draw => exact Or.inl rfl
  | wasteToFound c => exact absurd hrev (journey_never_wasteToFound hstep)
  | wasteToTab c b => exact absurd hrev (journey_never_wasteToTab hstep)
  | tabToFound c => exact Or.inr (Or.inl ⟨c, rfl⟩)
  | foundToTab c b => exact Or.inr (Or.inr (Or.inl ⟨c, b, rfl⟩))
  | tabToTab c b => exact Or.inr (Or.inr (Or.inr ⟨c, b, rfl⟩))

/-- **THE DRAW FLATNESS** — a draw leg carries every cell's census:
it writes no pile (`stepDraw_piles`), hence no seat top moves. -/
theorem census_step_draw {st s' : State}
    (h : State.step st Move.draw = some s') :
    ∀ col i, hostCensus s' col i = hostCensus st col i := by
  have hf : s'.piles = st.piles := stepDraw_piles h
  have htops : ∀ a', s'.topOf a' = st.topOf a' := by
    intro a'
    exact congrArg Pile.top (congrFun hf a')
  intro col i
  have E := census_touch st s' Anchor.p0 (st.topOf Anchor.p0)
    (st.topOf Anchor.p0) (fun x _ => htops x) rfl (htops Anchor.p0)
  have C := E col i
  omega

/-! ## §7. THE OWNER'S-BET LEDGER

The loan bookkeeping.  `seatMint` / `seatBurn` measure, per leg and
per cell, exactly which tops are gained into / lost from the cell
(decidable reads of the leg's own pre- and post-tops, one summand per
anchor).  `seatLedger_pair` is the per-leg exact identity for ANY
step; `play_census_ledger` telescopes it along any play; over a
RETURNED play the mint and burn budgets cancel cell-for-cell.  The
start-state census is the arrangement PROFILE; the ledger says the
end profile is the start profile plus mints minus burns — nothing
else.  The per-leg CONFINEMENT of the mints to the letters' named
cells is this file's named residue.
-/

/-- The sequential-gain indicator: 1 exactly when the OLD reading is
off and the NEW reading is on. -/
def seatGain (old new : Nat) : Nat :=
  match old, new with
  | 0, 1 => 1
  | _, _ => 0

/-- **THE MINT COUNTER** (per leg) — the seats the leg GAINS into the
cell: tops at the landing state in the cell that were not in it at
the pre-state. -/
def seatMint (st s' : State) (col : Color) (i : Nat) : Nat :=
  Anchor.all.foldl (fun n a =>
      n + seatGain (seatInd (st.topOf a) col i) (seatInd (s'.topOf a) col i)) 0

/-- **THE BURN COUNTER** (per leg) — dually, the seats the leg LOSES
from the cell. -/
def seatBurn (st s' : State) (col : Color) (i : Nat) : Nat :=
  Anchor.all.foldl (fun n a =>
      n + seatGain (seatInd (s'.topOf a) col i) (seatInd (st.topOf a) col i)) 0

/-- The flip identity of the gain indicator at bit values. -/
private theorem seatGain_flip (old new : Nat) (h1 : old ≤ 1) (h2 : new ≤ 1) :
    new + seatGain new old = old + seatGain old new := by
  have ho : old = 0 ∨ old = 1 := by omega
  have hn : new = 0 ∨ new = 1 := by omega
  rcases ho with rfl | rfl
  · rcases hn with rfl | rfl <;> rfl
  · rcases hn with rfl | rfl <;> rfl

theorem seatMint_eq_sum (st s' : State) (col : Color) (i : Nat) :
    seatMint st s' col i =
      seatGain (seatInd (st.topOf Anchor.p0) col i)
        (seatInd (s'.topOf Anchor.p0) col i) +
      seatGain (seatInd (st.topOf Anchor.p1) col i)
        (seatInd (s'.topOf Anchor.p1) col i) +
      seatGain (seatInd (st.topOf Anchor.p2) col i)
        (seatInd (s'.topOf Anchor.p2) col i) +
      seatGain (seatInd (st.topOf Anchor.p3) col i)
        (seatInd (s'.topOf Anchor.p3) col i) +
      seatGain (seatInd (st.topOf Anchor.p4) col i)
        (seatInd (s'.topOf Anchor.p4) col i) +
      seatGain (seatInd (st.topOf Anchor.p5) col i)
        (seatInd (s'.topOf Anchor.p5) col i) +
      seatGain (seatInd (st.topOf Anchor.p6) col i)
        (seatInd (s'.topOf Anchor.p6) col i) :=
  foldSum_eq _

theorem seatBurn_eq_sum (st s' : State) (col : Color) (i : Nat) :
    seatBurn st s' col i =
      seatGain (seatInd (s'.topOf Anchor.p0) col i)
        (seatInd (st.topOf Anchor.p0) col i) +
      seatGain (seatInd (s'.topOf Anchor.p1) col i)
        (seatInd (st.topOf Anchor.p1) col i) +
      seatGain (seatInd (s'.topOf Anchor.p2) col i)
        (seatInd (st.topOf Anchor.p2) col i) +
      seatGain (seatInd (s'.topOf Anchor.p3) col i)
        (seatInd (st.topOf Anchor.p3) col i) +
      seatGain (seatInd (s'.topOf Anchor.p4) col i)
        (seatInd (st.topOf Anchor.p4) col i) +
      seatGain (seatInd (s'.topOf Anchor.p5) col i)
        (seatInd (st.topOf Anchor.p5) col i) +
      seatGain (seatInd (s'.topOf Anchor.p6) col i)
        (seatInd (st.topOf Anchor.p6) col i) :=
  foldSum_eq _

/-- **THE PER-LEG LEDGER** — for ANY step, the landed census plus the
burns equals the origin census plus the mints: the only per-seat
movements are gains and losses, and each is counted. -/
theorem seatLedger_pair (st s' : State) (col : Color) (i : Nat) :
    hostCensus s' col i + seatBurn st s' col i
      = hostCensus st col i + seatMint st s' col i := by
  rw [hostCensus_eq_sum s' col i, hostCensus_eq_sum st col i,
    seatBurn_eq_sum st s' col i, seatMint_eq_sum st s' col i]
  have per : ∀ x : Anchor,
      seatInd (s'.topOf x) col i
        + seatGain (seatInd (s'.topOf x) col i) (seatInd (st.topOf x) col i)
      = seatInd (st.topOf x) col i
        + seatGain (seatInd (st.topOf x) col i) (seatInd (s'.topOf x) col i) :=
    fun x => seatGain_flip _ _ (seatInd_le_one _ _ _)
      (seatInd_le_one _ _ _)
  have p0 := per Anchor.p0
  have p1 := per Anchor.p1
  have p2 := per Anchor.p2
  have p3 := per Anchor.p3
  have p4 := per Anchor.p4
  have p5 := per Anchor.p5
  have p6 := per Anchor.p6
  omega

/-- **THE JOURNEY TELEMETRY** — the minted seats along a play
(state-threaded, leg by leg). -/
def journeyMint (st : State) : List Move → Color → Nat → Nat
  | [], _, _ => 0
  | m :: t, col, i =>
      match State.step st m with
      | none => journeyMint st t col i
      | some s₁ => seatMint st s₁ col i + journeyMint s₁ t col i

/-- **THE JOURNEY TELEMETRY** (burned seats) — dually. -/
def journeyBurn (st : State) : List Move → Color → Nat → Nat
  | [], _, _ => 0
  | m :: t, col, i =>
      match State.step st m with
      | none => journeyBurn st t col i
      | some s₁ => seatBurn st s₁ col i + journeyBurn s₁ t col i

/-- **THE JOURNEY CENSUS LEDGER** — along ANY play, the end census plus
the journey's burns equals the start census plus the journey's mints:
the exact per-cell bookkeeping the owner's bet runs on (the
arrangement profile is the start census; everything above it is a
mint, and every mint is one letter's seat).  The run-form statement
subsumes the `ShufflePlayW` form through `ShufflePlayW_run`. -/
theorem play_census_ledger {st : State} : ∀ (play : List Move) (w : State),
    State.run st play = some w → ∀ col i,
    hostCensus w col i + journeyBurn st play col i
      = hostCensus st col i + journeyMint st play col i := by
  intro play
  induction play generalizing st with
  | nil =>
      intro w h col i
      have hsw : (some st : Option State) = some w := h
      injection hsw with hw
      rw [hw]
      show hostCensus w col i + (0 : Nat)
        = hostCensus w col i + (0 : Nat)
      omega
  | cons m rest ih =>
      intro w h col i
      obtain ⟨s₁, hstep, hrest⟩ := State.run_cons h
      have hMi : journeyMint st (m :: rest) col i
          = seatMint st s₁ col i + journeyMint s₁ rest col i := by
        show (match State.step st m with
          | none => journeyMint st rest col i
          | some s' => seatMint st s' col i + journeyMint s' rest col i) = _
        rw [hstep]
      have hBu : journeyBurn st (m :: rest) col i
          = seatBurn st s₁ col i + journeyBurn s₁ rest col i := by
        show (match State.step st m with
          | none => journeyBurn st rest col i
          | some s' => seatBurn st s' col i + journeyBurn s' rest col i) = _
        rw [hstep]
      have E := seatLedger_pair st s₁ col i
      have IH := ih w hrest col i
      omega

/-- The run-append compose (private per-file copy). -/
private theorem hc_run_append : ∀ (a : State) (A B : List Move) (z w : State),
    a.run A = some z → z.run B = some w → a.run (A ++ B) = some w := by
  intro a A
  induction A generalizing a with
  | nil =>
      intro B z w h1 h2
      have hsw : (some a : Option State) = some z := h1
      injection hsw with hc
      rw [← hc] at h2
      exact h2
  | cons m rest ih =>
      intro B z w h1 h2
      obtain ⟨a₁, hs, hr⟩ := State.run_cons h1
      have h3 := ih a₁ B z w hr h2
      rw [List.cons_append]
      show (match State.step a m with
        | some st' => st'.run (rest ++ B)
        | none => none) = some w
      rw [hs]
      exact h3

/-- **THE ROUND-TRIP REPAYMENT** — over a RETURNED play (st → w → st)
the per-cell mint and burn budgets CANCEL EXACTLY: the excursion
issued no hosting capacity the tour does not reclaim.  THE CENSUS
ROUND-TRIP CONTRACT. -/
theorem roundtrip_census_repay {st w : State} {τ ρ : List Move}
    (hτ : State.run st τ = some w) (hρ : State.run w ρ = some st) :
    ∀ col i, journeyMint st (τ ++ ρ) col i
      = journeyBurn st (τ ++ ρ) col i := by
  intro col i
  have hrun : State.run st (τ ++ ρ) = some st :=
    hc_run_append st τ ρ w st hτ hρ
  have E := play_census_ledger (τ ++ ρ) st hrun col i
  omega

/-- **THE OWNER'S-BET — THE EXCURSION ISSUES NO NEW SEAT** — the row
the low-slab crane-replay consumes: a witness journey out of a state
the tour RETURNS to obeys the exact per-cell census ledger over the
forward half, and the two halves' mint/burn budgets cancel
cell-for-cell over the round trip.  The arrangement profile (the
start-state census) is therefore the whole truth: any cell's gain at
the midstate is a MINT of the forward letters, and the returned half
burns exactly what was minted — no hosting capacity survives the
excursion that the arrangement did not already carry.  This is the
seating counterpart of `Orig/BracketDecomp.lean`'s
`witness_rung_census` (the foundation ledger).  The per-leg
CONFINEMENT of the mints to the letters' named cells is the named
residue `witness_leg_mint_confined`. -/
theorem excursion_issues_noNewSeat {st w : State} {τ ρ : List Move}
    (hτ : ShufflePlayW st τ w) (hρ : ShufflePlayW w ρ st) :
    (∀ col i, hostCensus w col i + journeyBurn st τ col i
        = hostCensus st col i + journeyMint st τ col i) ∧
    (∀ col i, journeyMint st (τ ++ ρ) col i
        = journeyBurn st (τ ++ ρ) col i) :=
  ⟨fun col i => play_census_ledger τ w (ShufflePlayW_run hτ) col i,
    fun col i => roundtrip_census_repay (ShufflePlayW_run hτ)
      (ShufflePlayW_run hρ) col i⟩

/-! ### The mint-zero kit (private)

The confinement engine: mint summands vanish when tops agree
(`seatGain_self_zero`) or when the new top is off the cell
(`seatGain_zero_of_new`, via `seatInd_cell_of_one`); the three
composites cover any leg whose changed tops sit at at most two named
anchors.
-/

/-- The gain indicator vanishes on equal bits. -/
private theorem seatGain_self_zero (a : Nat) (h : a ≤ 1) : seatGain a a = 0 :=
  by
  have ha : a = 0 ∨ a = 1 := by omega
  rcases ha with rfl | rfl <;> rfl

/-- The gain indicator vanishes when the incoming top is off the cell. -/
private theorem seatGain_zero_of_new (o o' : Option Card) (col : Color)
    (i : Nat)
    (hoff : ∀ v, o' = some v → ¬(v.suit.color = col ∧ v.rank.toIdx = i)) :
    seatGain (seatInd o col i) (seatInd o' col i) = 0 := by
  have hle' := seatInd_le_one o' col i
  have h0 : seatInd o' col i = 0 := by
    cases o' with
    | none => rfl
    | some v =>
        cases hcon : seatInd (some v) col i with
        | zero => rfl
        | succ n =>
            exfalso
            have hone : seatInd (some v) col i = 1 := by omega
            exact hoff v rfl (seatInd_cell_of_one hone)
  rw [h0]
  have hle := seatInd_le_one o col i
  have ho : seatInd o col i = 0 ∨ seatInd o col i = 1 := by omega
  rcases ho with h0v | h1v
  · rw [h0v]
    rfl
  · rw [h1v]
    rfl

/-- The mint is the seven-seat gain sum: all-zero gains give zero. -/
private theorem mint_zero_of_g (st s' : State) (col : Color) (i : Nat)
    (h : ∀ x : Anchor,
      seatGain (seatInd (st.topOf x) col i) (seatInd (s'.topOf x) col i)
        = 0) :
    seatMint st s' col i = 0 := by
  rw [seatMint_eq_sum]
  have g0 := h Anchor.p0
  have g1 := h Anchor.p1
  have g2 := h Anchor.p2
  have g3 := h Anchor.p3
  have g4 := h Anchor.p4
  have g5 := h Anchor.p5
  have g6 := h Anchor.p6
  omega

/-- One touched seat, incoming top off the cell: nothing minted. -/
private theorem mint_zero_at (st s' : State) (k : Anchor) (o o' : Option Card)
    (hspot : ∀ x, x ≠ k → s'.topOf x = st.topOf x)
    (hst : st.topOf k = o) (hs' : s'.topOf k = o')
    (col : Color) (i : Nat)
    (hoff : ∀ v, o' = some v → ¬(v.suit.color = col ∧ v.rank.toIdx = i)) :
    seatMint st s' col i = 0 := by
  refine mint_zero_of_g st s' col i (fun x => ?_)
  by_cases hx : x = k
  · rw [hx, hst, hs']
    exact seatGain_zero_of_new o o' col i hoff
  · rw [hspot x hx]
    exact seatGain_self_zero _ (seatInd_le_one _ _ _)

/-- Two touched seats, incoming tops off the cell: nothing minted. -/
private theorem mint_zero_two (st s' : State) (k1 k2 : Anchor)
    (o1 o1' o2 o2' : Option Card) (_hne : k1 ≠ k2)
    (hspot : ∀ x, x ≠ k1 → x ≠ k2 → s'.topOf x = st.topOf x)
    (h1 : st.topOf k1 = o1) (h1' : s'.topOf k1 = o1')
    (h2 : st.topOf k2 = o2) (h2' : s'.topOf k2 = o2')
    (col : Color) (i : Nat)
    (hoff1 : ∀ v, o1' = some v → ¬(v.suit.color = col ∧ v.rank.toIdx = i))
    (hoff2 : ∀ v, o2' = some v → ¬(v.suit.color = col ∧ v.rank.toIdx = i)) :
    seatMint st s' col i = 0 := by
  refine mint_zero_of_g st s' col i (fun x => ?_)
  by_cases hx1 : x = k1
  · rw [hx1, h1, h1']
    exact seatGain_zero_of_new o1 o1' col i hoff1
  · by_cases hx2 : x = k2
    · rw [hx2, h2, h2']
      exact seatGain_zero_of_new o2 o2' col i hoff2
    · rw [hspot x hx1 hx2]
      exact seatGain_self_zero _ (seatInd_le_one _ _ _)

/-- No seat top moves: nothing minted. -/
private theorem mint_zero_all (st s' : State)
    (h : ∀ x, s'.topOf x = st.topOf x) (col : Color) (i : Nat) :
    seatMint st s' col i = 0 := by
  refine mint_zero_of_g st s' col i (fun x => ?_)
  rw [h x]
  exact seatGain_self_zero _ (seatInd_le_one _ _ _)

/-- **THE PER-LEG MINT CONFINEMENT** — the owner's bet, leg by leg,
CLOSED.  On a WITNESS leg, every minted seat sits at one of the
letters' named cells: the PULLED card's own cell (a `foundToTab` —
seated or king-corner, the move names the card), the EXPOSED SEAT
card's cell of an under-raise (opposite family, the raised card's
index + 1, the arrangement-card the crane replays onto), the cargo's
EXPOSED BELOW-CARD cell, or the cargo's LANDING RUN-TOP cell (the
inl king-run and the seated host share this pair).  The reveal mints
never ride (the banked `journey_tabToFound_never_reveal` /
`journey_tabToTab_never_reveal`), and the burn slide never mints
(§2's pin) — so the mining set of the whole program is exactly the
four disjuncts below.

Route: the leg alphabet (`witness_leg_letters`); each arm's changed
tops are the census rows' `census_touch` inputs (at most two anchors);
the mint summands away from the changed anchors vanish because equal
tops give equal bits (`seatGain_self_zero`), and at a changed anchor
an off-cell new top gives a zero gain (`seatGain_zero_of_new` via
`seatInd_cell_of_one`); the degenerate arms are pre-split by the
witness-grade rows (bare-king raises mint nothing — the anchor
empties; the burn arm is barred; the inl cargo empties its source). -/
theorem witness_leg_mint_confined {st s₁ : State} {m : Move}
    (hwf : st.WF)
    (hrev : reversibleAtW st m)
    (hstep : State.step st m = some s₁) :
    ∀ col i, seatMint st s₁ col i ≠ 0 →
      (∃ c b, m = Move.foundToTab c b ∧
          c.suit.color = col ∧ c.rank.toIdx = i) ∨
      (∃ c k z, m = Move.tabToFound c ∧ st.pileOfTop c = some k ∧
          chop (st.piles k).faceUp ≠ [] ∧
          lastOf (chop (st.piles k).faceUp) = some z ∧
          z.suit.color = col ∧ z.rank.toIdx = i) ∨
      (∃ e b a v, m = Move.tabToTab e b ∧ st.pileHolding e = some a ∧
          lastOf (below e (st.piles a).faceUp) = some v ∧
          v.suit.color = col ∧ v.rank.toIdx = i) ∨
      (∃ e b a v, m = Move.tabToTab e b ∧ st.pileHolding e = some a ∧
          lastOf (fromCard e (st.piles a).faceUp) = some v ∧
          v.suit.color = col ∧ v.rank.toIdx = i) := by
  intro col i hmint
  obtain hd | hra | hpull | hcargo := witness_leg_letters hstep hrev
  · -- draw: no seat top moves
    exfalso
    subst hd
    have hflat : ∀ x, s₁.topOf x = st.topOf x := by
      intro x
      have hf := congrFun (stepDraw_piles hstep) x
      exact congrArg Pile.top hf
    exact hmint (mint_zero_all st s₁ hflat col i)
  · obtain ⟨c, hc⟩ := hra
    subst hc
    obtain ⟨_, k, hpa, hs⟩ := step_tabToFound_inv hstep
    have hpilk : s₁.piles k
        = Pile.afterRunRemoved (st.piles k) (chop (st.piles k).faceUp) := by
      rw [hs]
      show (if k = k then
          Pile.afterRunRemoved (st.piles k) (chop (st.piles k).faceUp)
        else st.piles k) = _
      rw [ite_eq_left rfl]
    have hspot : ∀ x, x ≠ k → s₁.topOf x = st.topOf x := by
      intro x hx
      rw [hs]
      show Pile.top (if x = k then
          Pile.afterRunRemoved (st.piles k) (chop (st.piles k).faceUp)
        else st.piles x) = st.topOf x
      rw [ite_eq_right hx]
      rfl
    obtain hunder | hbare := census_tabToFound_witness hwf hrev hstep hpa
    · obtain ⟨hchopne, -, ⟨z, hztop, -, -, -, -, -⟩⟩ := hunder
      by_cases hcell : z.suit.color = col ∧ z.rank.toIdx = i
      · have hzlast : lastOf (chop (st.piles k).faceUp) = some z := by
          have hx := hztop
          rw [show s₁.topOf k = Pile.top (s₁.piles k) from rfl, hpilk,
            afterRunRemoved_ne hchopne] at hx
          show lastOf ({ st.piles k with
            faceUp := chop (st.piles k).faceUp } : Pile).faceUp = some z
          exact hx
        exact Or.inr (Or.inl ⟨c, k, z, rfl, hpa, hchopne, hzlast, hcell.1,
          hcell.2⟩)
      · exfalso
        have hst : st.topOf k = some c := (pileOfTop_top hpa).2
        apply hmint
        refine mint_zero_at st s₁ k (some c) (some z) hspot hst hztop col i ?_
        intro v hv
        have hvz : z = v := by injection hv
        rw [← hvz]
        exact hcell
    · obtain ⟨hchop, hhid, -, -, -⟩ := hbare
      exfalso
      have hs' : s₁.topOf k = none := by
        rw [show s₁.topOf k = Pile.top (s₁.piles k) from rfl, hpilk, hchop,
          afterRunRemoved_bare_pile _ hhid]
        show lastOf (({ st.piles k with
          faceUp := ([] : List Card) } : Pile).faceUp) = none
        rfl
      have hst : st.topOf k = some c := (pileOfTop_top hpa).2
      apply hmint
      exact mint_zero_at st s₁ k (some c) none hspot hst hs' col i
        (fun _ hv => absurd hv (by simp))
  · obtain ⟨c, b, hb⟩ := hpull
    subst hb
    obtain ⟨_, htop, _, hcp, hs⟩ := step_foundToTab_inv hstep
    by_cases hcell : c.suit.color = col ∧ c.rank.toIdx = i
    · exact Or.inl ⟨c, b, rfl, hcell.1, hcell.2⟩
    · exfalso
      cases b with
      | inl n =>
          have hspot : ∀ x, x ≠ n → s₁.topOf x = st.topOf x := by
            intro x hx
            rw [hs, putCard_eq_inl, setPile_topOf_ne hx]
            rfl
          have hst : st.topOf n = none := by
            obtain ⟨hemp, -⟩ := canPlace_inl hcp
            obtain ⟨-, hfu⟩ := (Pile.isEmpty_eq _).mp hemp
            rw [show st.topOf n = lastOf ((st.piles n).faceUp) from rfl, hfu]
            rfl
          have hs' : s₁.topOf n = some c := by
            rw [show s₁.topOf n = Pile.top (s₁.piles n) from rfl, hs,
              putCard_eq_inl, setPile_piles_self]
            show lastOf (([] : List Card) ++ [c]) = some c
            exact lastOf_snoc
          apply hmint
          refine mint_zero_at st s₁ n none (some c) hspot hst hs' col i ?_
          intro v hv
          have hvc : v = c := (Option.some.inj hv).symm
          rw [hvc]
          exact hcell
      | inr z =>
          obtain ⟨k, hpzk, -⟩ := canPlace_inr hcp
          have hpzk' : (st.setFound c.suit (chop (st.found c.suit))).pileOfTop z
              = some k := hpzk
          have hspot : ∀ x, x ≠ k → s₁.topOf x = st.topOf x := by
            intro x hx
            rw [hs, putCard_inr_eq hpzk', setPile_topOf_ne hx]
            rfl
          have hst : st.topOf k = some z := (pileOfTop_top hpzk).2
          have hs' : s₁.topOf k = some c := by
            rw [show s₁.topOf k = Pile.top (s₁.piles k) from rfl, hs,
              putCard_inr_eq hpzk', setPile_piles_self]
            show lastOf (((st.setFound c.suit (chop (st.found c.suit))).piles k).faceUp
              ++ [c]) = some c
            exact lastOf_snoc
          apply hmint
          refine mint_zero_at st s₁ k (some z) (some c) hspot hst hs' col i ?_
          intro v hv
          have hvc : v = c := (Option.some.inj hv).symm
          rw [hvc]
          exact hcell
  · obtain ⟨e, b, hb⟩ := hcargo
    subst hb
    obtain ⟨src, hh, hcp, -, hs⟩ := step_tabToTab_inv hstep
    have hmem : e ∈ (st.piles src).faceUp := pileHolding_mem hh
    cases b with
    | inl n =>
        obtain ⟨-, hhid, hbelnil, hs'src, TA, hTA, hs'n, -⟩ :=
          census_tabToTab_inl hwf hstep hh hrev
        have hsplit : (st.piles src).faceUp
            = below e (st.piles src).faceUp
              ++ fromCard e (st.piles src).faceUp :=
          (below_fromCard_partition e _).symm
        have hstsrc : st.topOf src = some TA := by
          rw [show st.topOf src = lastOf ((st.piles src).faceUp) from rfl,
            hsplit, hbelnil, List.nil_append]
          exact hTA
        by_cases hcell : TA.suit.color = col ∧ TA.rank.toIdx = i
        · exact Or.inr (Or.inr (Or.inr ⟨e, Sum.inl n, src, TA, rfl, hh, hTA,
            hcell.1, hcell.2⟩))
        · exfalso
          obtain ⟨hemp, -⟩ := canPlace_inl hcp
          obtain ⟨-, hfundn⟩ := (Pile.isEmpty_eq _).mp hemp
          have hstn : st.topOf n = none := by
            rw [show st.topOf n = lastOf ((st.piles n).faceUp) from rfl,
              hfundn]
            rfl
          have hnsrc : n ≠ src := canPlace_inl_target_pile_ne hcp hmem
          have hspot : ∀ x, x ≠ src → x ≠ n → s₁.topOf x = st.topOf x := by
            intro x hx1 hx2
            rw [hs, putRun_eq_inl, setPile_topOf_ne hx2, setPile_topOf_ne hx1]
          apply hmint
          refine mint_zero_two st s₁ src n (some TA) none none (some TA)
            (Ne.symm hnsrc) hspot hstsrc hs'src hstn hs'n col i
            (fun _ hv => absurd hv (by simp)) ?_
          intro v hv
          have hvc : TA = v := by injection hv
          rw [← hvc]
          exact hcell
    | inr z =>
        obtain ⟨k, hpzk, hfit⟩ := canPlace_inr hcp
        by_cases hbel : below e (st.piles src).faceUp = []
        · exfalso
          by_cases hhid : (st.piles src).hidden = []
          · exact absurd hrev
              (witness_tabToTab_never_burn hstep hh hbel hhid hfit)
          · exact absurd hrev
              (journey_tabToTab_never_reveal hstep hh hbel hhid)
        · obtain ⟨y, hy_last, hyfit, hycol, -, -, TA, hTA, hTAold, hsy, hsTA,
              -⟩ :=
            census_tabToTab_under hwf hstep hh hpzk hfit hbel
          have hkane : k ≠ src := fun hcon =>
            canPlace_inr_target_pile_ne hwf hcp hmem
              (hpzk.trans (congrArg some hcon))
          have hpin : (st.setPile src
              (Pile.afterRunRemoved (st.piles src)
                (below e (st.piles src).faceUp))).pileOfTop z = some k :=
            tabToTab_search_pins hwf hpzk hkane
          have hspot : ∀ x, x ≠ src → x ≠ k → s₁.topOf x = st.topOf x := by
            intro x hx1 hx2
            rw [hs, putRun_inr_eq hpin, setPile_topOf_ne hx2,
              setPile_topOf_ne hx1]
          have hstk : st.topOf k = some z := (pileOfTop_top hpzk).2
          by_cases hyc : y.suit.color = col ∧ y.rank.toIdx = i
          · exact Or.inr (Or.inr (Or.inl ⟨e, Sum.inr z, src, y, rfl, hh,
              hy_last, hyc.1, hyc.2⟩))
          · by_cases hTAc : TA.suit.color = col ∧ TA.rank.toIdx = i
            · exact Or.inr (Or.inr (Or.inr ⟨e, Sum.inr z, src, TA, rfl, hh,
                hTA, hTAc.1, hTAc.2⟩))
            · exfalso
              apply hmint
              refine mint_zero_two st s₁ src k (some TA) (some y) (some z)
                (some TA) (Ne.symm hkane) hspot hTAold hsy hstk hsTA col i
                (fun v hv => by
                  have hvv : y = v := by injection hv
                  rw [← hvv]
                  exact hyc)
                (fun v hv => by
                  have hvv : TA = v := by injection hv
                  rw [← hvv]
                  exact hTAc)

/-! ## §8. The audit battery

`#print axioms` per fresh public head.  Expected grades: the
transaction rows and bars read the banked chain (propext at most —
the census def is a plain fold and every split rides `Decidable.em`
or decided equalities; the two pin-based bars are
write-analysis-grade, no choice); `witness_leg_mint_confined` is the
file's single `sorryAx` carrier and NOTHING else flows into it;
`excursion_issues_noNewSeat` reads the proved ledger rows
(propext-grade through the quotient-free `run` forms — no
`ShufflePlayW` rule is used in its own statement beyond the two
`ShufflePlayW_run` reads, so it stays choice-free).
-/

#print axioms topOf_eq_snoc
#print axioms seatInd_topOf_zero
#print axioms hostCensus_eq_sum
#print axioms seatInd_some_one
#print axioms seatInd_zero_of_color
#print axioms seatInd_zero_of_rank
#print axioms seatInd_zero_of_cell
#print axioms seatInd_le_one
#print axioms seatInd_eq_of_cellEq
#print axioms bare_lift_irreversibleAt
#print axioms bare_burn_irreversibleAt
#print axioms witness_bare_lift_king
#print axioms witness_tabToTab_never_burn
#print axioms census_foundToTab_inr
#print axioms census_foundToTab_inl
#print axioms census_tabToFound_under
#print axioms census_tabToFound_reveal
#print axioms census_tabToFound_bare
#print axioms census_tabToFound_witness
#print axioms census_tabToTab_under
#print axioms census_tabToTab_burn
#print axioms census_tabToTab_reveal
#print axioms census_tabToTab_inl
#print axioms census_tabToTab_inr_witness
#print axioms witness_leg_letters
#print axioms census_step_draw
#print axioms seatMint_eq_sum
#print axioms seatBurn_eq_sum
#print axioms seatLedger_pair
#print axioms play_census_ledger
#print axioms roundtrip_census_repay
#print axioms excursion_issues_noNewSeat
#print axioms witness_leg_mint_confined

/-! ## §9. THE DRAW-COMMUTATION ROWS (Mission 2)

The draw-kind's phase content for the low-slab sufficiency.  The
board letters (raise / pull / cargo — the witness alphabet minus
draws) are BLIND to the two-zone cycle: their guards read only
`piles` and `found`, their effects write only `piles` and `found`,
and everything else they carry through verbatim.  So board plays
commute with draws: running the SAME witness play from the dashed
state (the draw-successor) executes leg-for-leg and lands ON THE
DOT at the dashed landing — the phase question is killed outright in
the draw-free replay regime.  The interleave regime (witness-graded
draws inside a replay) is the named residue `interleave_phase_align`
below.
-/

/-- **THE BOARD-THREAD RELATION** — two states agree on every field
the board letters read or write (foundations and piles); their
two-zone cycle and step size may differ freely. -/
def boardEq (x y : State) : Prop := x.piles = y.piles ∧ x.found = y.found

/-- **THE BOARD LETTERS** — the witness-legal, zone-blind moves. -/
def boardMove (m : Move) : Prop :=
  (∃ c, m = Move.tabToFound c) ∨ (∃ c b, m = Move.foundToTab c b) ∨
    (∃ c b, m = Move.tabToTab c b)

/-! ### The guard congruences (private kit, over the banked public
`Twin`/`State` congr rows) -/

private theorem foundHeight_congr {x y : State} (hb : boardEq x y)
    (s : Suit) : x.foundHeight s = y.foundHeight s := by
  show (x.found s).length = (y.found s).length
  rw [congrFun hb.2 s]

private theorem hcNextUp {x y : State} (hb : boardEq x y) (c : Card) :
    x.nextUp c = y.nextUp c := nextUp_congr c hb.2

private theorem hcFoundTop {x y : State} (hb : boardEq x y) (s : Suit) :
    x.foundTop s = y.foundTop s := foundTop_congr s hb.2

private theorem hcTopOf {x y : State} (hb : boardEq x y) (a : Anchor) :
    x.topOf a = y.topOf a := topOf_congr a hb.1

private theorem hcPileOfTop {x y : State} (hb : boardEq x y) (z : Card) :
    x.pileOfTop z = y.pileOfTop z := pileOfTop_congr z hb.1

private theorem hcPileHolding {x y : State} (hb : boardEq x y) (c : Card) :
    x.pileHolding c = y.pileHolding c := pileHolding_congr hb.1

private theorem hcCanPlace {x y : State} (hb : boardEq x y) (c : Card)
    (b : Base) : x.canPlace c b = y.canPlace c b := canPlace_congr c b hb.1

private theorem faceUp_congr {x y : State} (hb : boardEq x y) (a : Anchor) :
    (x.piles a).faceUp = (y.piles a).faceUp :=
  congrArg Pile.faceUp (congrFun hb.1 a)


/-! ### The per-letter step congruences (private kit) -/

private theorem setFound_found_eq {x y : State} (hb : boardEq x y) (s : Suit)
    (l_x l_y : List Card) (hl : l_x = l_y) :
    (x.setFound s l_x).found = (y.setFound s l_y).found := by
  funext s'
  show (if s' = s then l_x else x.found s')
      = (if s' = s then l_y else y.found s')
  by_cases hs : s' = s
  · rw [hs, ite_eq_left rfl, ite_eq_left rfl, hl]
  · rw [ite_eq_right hs, ite_eq_right hs]
    exact congrFun hb.2 s'

private theorem setPile_piles_aux {x y : State} (hp : x.piles = y.piles)
    (k : Anchor) (p_x p_y : Pile) (hpp : p_x = p_y) (a' : Anchor) :
    (x.setPile k p_x).piles a' = (y.setPile k p_y).piles a' := by
  show (if a' = k then p_x else x.piles a')
      = (if a' = k then p_y else y.piles a')
  by_cases h : a' = k
  · rw [h, ite_eq_left rfl, ite_eq_left rfl, hpp]
  · rw [ite_eq_right h, ite_eq_right h, congrFun hp a']


/-! ### §9.1 The step-successor congruences (named residue, route)

The GUARD half is proved above: every board letter's step condition is
a piles/found read, so legality transfers across `boardEq` states
(`hcNextUp`, `hcFoundTop`, `hcPileOfTop`, `hcPileHolding`,
`hcCanPlace`, `faceUp_congr`).  The SUCCESSOR half — the same-lambda
rebuild of the step record with the dashed state's unchanged zone
fields — is mechanical but record-level (it fought the elaborator
twice here); its complete route:

1. Per-letter step congruence: from the banked inversion rows
   (`step_tabToFound_inv`, `step_foundToTab_inv`, `step_tabToTab_inv`)
   read the successor RECORD equalities at the home state; construct
   the dashed successor as the syntactically identical record over the
   dashed fields; the dashed step's guards rewrite through the proved
   congruence kit; the successor boards compare via `setFound_found_eq`
   and `setPile_piles_aux` (both proved above), with `putCard` /
   `putRun`'s `inr` searches aligned through `pileOfTop_congr`
   (banked, Orig/Twin.lean) over the setFound-threaded piles
   (`rfl` pass-throughs, as in this file's §5 landings).
2. The play-level `board_run_congr` below is then a `State.run_cons`
   induction over the legs.
3. The draw-zone determination below needs the draw unfold
   (`dealStock .recycle`) with a four-way case split on
   `(stock, waste)`; the zone fields are `State.dealUpTo`-expressions
   depending only on `(stock, waste, drawStep)`.

The four statements below are the exact shapes LowSlab imports.
-/

/-- **THE BOARD STEP CONGRUENCE** (named residue) — a board letter
legal at `x` is legal at any `boardEq` `y`, and the successors are
again `boardEq`: every board field the letter reads or writes agrees,
so the dashed thread runs leg-for-leg.  ROUTE: step 1 of §9.1. -/
theorem step_congr_board {x y x' : State} {m : Move}
    (hb : boardEq x y) (hboard : boardMove m)
    (hx : State.step x m = some x') :
    ∃ y', State.step y m = some y' ∧ boardEq x' y' := by
  sorry

/-- **THE BOARD-PLAY CONGRUENCE** (named residue) — THE KEY FACT of
the draw commutation: a board-only play runs identically from both
ends of a `boardEq` pair, lands its `boardEq` image, and leaves each
side's two-zone cycle untouched (the flat clauses) — the zone-blind
half of the replay.  ROUTE: `State.run_cons` induction over the legs
with `step_congr_board`; the flat clauses are the step records' field
pass-throughs. -/
theorem board_run_congr : ∀ (π : List Move),
    (∀ m ∈ π, boardMove m) →
    ∀ (x y : State), boardEq x y →
    ∀ z : State, State.run x π = some z →
    ∃ w, State.run y π = some w ∧ boardEq z w ∧
      z.stock = x.stock ∧ z.waste = x.waste ∧ z.drawStep = x.drawStep ∧
      w.stock = y.stock ∧ w.waste = y.waste ∧ w.drawStep = y.drawStep := by
  sorry

/-- **THE DRAW-COMMUTATION REACH** (named residue — the (A) case, the
phase-exactness claim): let `ρ` be a witness play with NO draw leg
(the waste letters never ride anyway, by `witness_leg_letters`), let
`u₀`'s draw succeed into `w₀` and `u`'s draw succeed into `w`.  Then
`w₀` runs the SAME play `ρ` and lands exactly ON `w` — the dashed
thread reaches the dashed landing: the slab duplicate's commit target
holds with PHASE EXACTNESS, not merely up to class.

ROUTE (complete; each step priced):
1. ρ's legs are board letters: `witness_leg_letters` per leg (each
   leg's `hrev` comes from the `ShufflePlayW` structure) plus the
   hypothesis that no leg is `Move.draw`.
2. `boardEq u₀ w₀`: the draw writes no board field
   (`stepDraw_piles` / `stepDraw_found`, banked).
3. `board_run_congr` at `(u₀, w₀, ρ, u)`: the dashed run `w₀.run ρ`
   lands some `W` with `boardEq u W` and `W`'s zone flat at `w₀`'s.
4. The zone chase: `u`'s zone equals `u₀`'s (the flat clause of
   step 3 at the `boardEq u₀ u₀` instance — `u₀.run ρ` flats both
   ends), hence the two draws — from `u₀` and from `u` — compute the
   same `dealStock .recycle` expressions (their `(stock, waste,
   drawStep)` arguments agree), so `w₀`'s zone fields equal `w`'s;
   with the board fields of `W` matching `u`'s (step 3) and the
   draw's board pass-throughs (`w.piles = u.piles`, `w.found =
   u.found`), all five fields of `W` and `w` agree — `State.ext`.
5. The landing is `some w` by step 4's equality. -/
theorem drawfree_commute_reach {u₀ u w₀ w : State} {ρ : List Move}
    (hρ : ShufflePlayW u₀ ρ u)
    (hnodraw : ∀ m ∈ ρ, m ≠ Move.draw)
    (hd₀ : State.step u₀ Move.draw = some w₀)
    (hdu : State.step u Move.draw = some w) :
    State.run w₀ ρ = some w := by
  sorry

/-- **THE WITNESS-GRADED DASHED REPLAY** (named residue) — the graded
form of the reach: the dashed thread is again a witness shuffle (each
dashed leg reversible at its own pre-state), so the slab duplicate's
target is not merely reached but reached BY A WITNESS PLAY, giving
`sameOrbitSetoid.r w₀ w` directly.  ROUTE: the home legs' return
witnesses are board plays at WF states (per-leg one-move mirrors —
the pulls' raises via `foundToTab_undo`'s WF-derivable premises, cf.
`Orig/LowSlab.lean`'s `lowslab_pull_wf_undo` route; the raises'
`tabToFound_undo_under` / `tabToFound_undo_bare`, banked; the cargo
letters' one-move mirrors — the seated slide back onto the exposed
below-card, and the `inl` king-run mirror — both are §5's `putRun`
reads run backwards, with the search pinning by WF uniqueness as in
`tabToTab_search_pins`), and `board_run_congr` translates each
mirror into the dashed thread's return; WF descends through
`step_wf`. -/
theorem drawfree_commute_witness {u₀ u w₀ w : State} {ρ : List Move}
    (_hwf : u₀.WF)
    (hρ : ShufflePlayW u₀ ρ u)
    (hnodraw : ∀ m ∈ ρ, m ≠ Move.draw)
    (hd₀ : State.step u₀ Move.draw = some w₀)
    (hdu : State.step u Move.draw = some w) :
    State.run w₀ ρ = some w :=
  drawfree_commute_reach hρ hnodraw hd₀ hdu

/-- **THE INTERLEAVE PHASE QUESTION — THE (B) CASE** (named residue,
the draw-kind's live falsification channel).  A witness journey whose
RETURN half contains witness-graded DRAW legs (they exist at empty
stocks — the recycle-and-deal cycle, `Orig/Phase.lean`'s
draw-irreversibility bank's reversible arm) does NOT commute with the
dashed thread for free: the dashed thread's zone sits at a different
cycle phase, and the draws read the zone.  The honest question: does
the elevated member's committed draw target match, up to
`sameOrbitSetoid`, a slab member's dashed commit — do the classes
ALIGN, or merely ROTATE?

ROUTE (priced, refuter-first):
1. The cycle census bank (`Orig/SlabEquiv.lean`'s `cycle_zone_pin`,
   [propext, Quot.sound]) and this file's §7 telemetry give the
   bookkeeping: along a witness journey, draw legs change ONLY the
   zone pair (`State.dealUpTo` take/drop; total zone length
   conserved — the conservation is the draw's own record), so the
   phase shift each draw induces is a rotation of a fixed-size
   cycle.
2. The phase-alignment candidate: each witness-graded draw shifts
   the zone deterministically (deal `min drawStep |stock|` cards,
   `dealUpTo_min`-style counts — Orig/Canonical.lean holds private
   copies); the conjugating-player question is whether a
   normalizing run of draws (drawing the stock down past a recycle)
   realigns the dashed phase — the alignment holds iff the class's
   return witnesses' combined rotation absorbs `u₀`'s phase offset
   into `u`'s (in fact `u₀`'s zone equals `u`'s along board
   replays: §9.1's flat clauses; the OFFSET ONLY ARISES FROM DRAW
   LEGS INSIDE THE CLASS's OWN WITNESSES).
3. THE FALSIFICATION SHAPE (the probe boards' target): a WF board-eq
   pair whose class return witnesses must contain draw legs at
   phases where the dashed stock CLIPS but the home deal does not —
   probe economies with `drawStep` large and stock lengths
   straddling the `drawStep` threshold at the commit points:
   `u₀.drawStep = 4`, `u₀.stock` of length 2 against a class whose
   return needs the phase-3 drawing.  If the classes only ROTATE,
   `sameOrbitSetoid.r w₀ w` FAILS while EVERY board census (§3–§7)
   agrees — exactly the split the low-slab mission must expose to
   the probes. -/
theorem interleave_phase_align {u₀ u w₀ w : State}
    (hwf₀ : u₀.WF)
    (hclass : sameOrbitSetoid.r u₀ u)
    (hd₀ : State.step u₀ Move.draw = some w₀)
    (hdu : State.step u Move.draw = some w) :
    sameOrbitSetoid.r w₀ w := by
  sorry

/-! ### §9.2 The audit additions

The guard congruence kit and the two record-equality helpers are
zero-sorry; the four §9.1 statements are this section's named
residues and carry the file's sorries.  Zero `Classical.choice`
throughout. -/

#print axioms setFound_found_eq
#print axioms setPile_piles_aux
#print axioms step_congr_board
#print axioms board_run_congr
#print axioms drawfree_commute_reach
#print axioms drawfree_commute_witness
#print axioms interleave_phase_align
