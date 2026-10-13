import Orig.ForkAscent
import Orig.ForkStateSB

/-!
# Orig.ForkAscentProbe — THE COVER-BURIAL PROBE

Decide-grade evidence for the ONE genuine open falsification shape of
the exhaustion program: the COVER-BURIAL corner of
`ascent_cover_cell` — hostile runs that bury the sole fitting covers
BEFORE stuckness.  Every row is a kernel-decided fact under a
`theorem` wrapper; zero sorry.

## What this probe decides

The burial experiment at the SMALLEST frontier economy `r = 1`
(the pair = the TWOS of the black family; the cover cells = the ACES
of the red family):

* THE RIGIDITY — at `r = 1` the cover cells are ACES, and aces are
  PILE FLOORS in this mechanization (`canSitOn` demands the sitter
  sit one rank BELOW its host: nothing sits on an ace).  So the ace
  cover cells can NEVER ride a slide's run, a self-landing run can
  never consume them (the run would have to contain them above its
  head), and no seating "buries" their fitness: at this economy the
  ONLY burial mode is FOUNDING.  (At higher `r` the `r−1` cells can
  ride runs — the self-landing burn corner of the route note in
  `Orig/ForkAscent.lean` — but founding remains the clean burial.)
* THE PRE-BROKEN GUARD — the full-time no-eat guard protects the
  two cover cells ONLY while they stand as an intact mobile pair (an
  ace and its ace twin, both face-up, both at-or-above their rungs).
  Pre-founding ONE cell (hearts at one in the start board `ab0`)
  breaks the pair — the founded card lives on the foundation, not
  in any pile's face-up, so the surviving twin's `MobileTwin` read
  fails at the conjunct that wants its twin face-up — and the guard
  no longer declines the second cell's raise.
* THE HOSTILE LEG — the one-move ascent run `[tabToFound A♦]` is
  legal at `ab0` (unguarded, hot at the empty diamond rung, face-up,
  topped) and lands `ab1` with BOTH cover cells founded: hearts at
  one, diamonds at one.  `ab1` is STUCK (neither hot raise remains —
  the only face-up cards are the black twos, and they sit one index
  ABOVE their suits' empty rungs; no slide places: the two face-up
  tops fit neither each other's tops nor an empty king seat — both
  refuted by enumeration).
* THE VERDICT — the stuck hostile landing `ab1` is a genuine,
  decide-witnessed EXHAUSTION whose shape carries NO FITTING COVER
  (`TwinSlideHalt ab1` is decide-false; for both red aces
  `d.rank.toIdx = 0 < 1 ≤ foundHeight`, so the exhaustion shape's
  cover clauses are unsatisfiable AT a stuck state).

## The honest read (what the evidence prices)

1. THE BURIAL SCENARIO BUILDS.  A satisfiable WF board admits a
   legal ascent run that founds both cover cells and parks stuck
   with the pair face-up and unfounded.  This probe does NOT
   compute whether `ab0` itself satisfies the exhaustion row's
   `hbelow` premise — the full move alphabet (draws surfacing stock
   cards through the waste) makes fork-reachability a wide-open
   computation this file does not run, so `ab0` is neither a
   counterexample to the frozen statement nor a certified
   satisfying board.  The datapoint stands: burial-by-founding is
   mechanically CHEAP (one pre-broken guard plus one licensed
   raise), and the exhaustion row's cover conclusion can only
   survive through economies where `hbelow`'s reachable fork rules
   the burial out.  THE DECISIVE OPEN QUESTION, named precisely:
   does any hbelow-SATISFYING board admit the founding-burial run?
   The probe's structural read: hbelow's reachable fork F carries
   its own saturation at the pair, and every founding of a cover
   cell raises the opposite-family rungs one index past the cover
   rank — whether F's reachability forces those rungs back down
   (it cannot: rungs never lower) or forces the twins of the
   founded cells to stay face-up-and-unfounded (the guard-trap's
   mirror) is the invariant the statement's honesty hangs on; this
   probe does not decide it and says so.
2. THE REPAIR SHAPES INDICATED, both noted for the owner:
   (α) strengthen the exhaustion premise so the cover cells' fate is
   tied to the reachable fork's economy (the reachable witness's own
   cover demand, carried from `F` back to the exhaustion's start);
   or (β) the lighter repair — weaken the delivered shape's cover
   clause to a RECOVERABLE disjunct (a cell founded at its suit's
   frontier returns by the descent alphabet's `foundToTab`-family:
   at `ab1` the founded red aces are exactly the frontier-recoverable
   cards of their suits, one licensed pull away).
3. THE SECOND BURIAL MODE — slide-SEATING is REFUTED AS A THREAT at
   every economy: the delivered shape's cover clauses read only
   rank, color, foundation height, and face-up-ness — none of which
   any seating changes (a covered card is still face-up, its rank
   and the rungs untouched).  The genuine burial modes are exactly
   founding (this file) and the self-landing burn of a riding cover
   (possible only at `r ≥ 2` where the cells can ride runs).

House compliance: additive leaf; private kit copies per file; zero
sorry; fresh heads audited at the bottom. -/

/-! ## §0. The private kit -/

/- The house card-maker (each probe file carries its own). -/
private def crd (s : Suit) (r : Rank) : Card := ⟨s, r⟩

/- A suit's foundation prefix at height `n` (the craft's `found`). -/
private def takeUp (s : Suit) (n : Nat) : List Card := s.upCards.take n

/- Oracle step helper (dead-hand plays are construction bugs). -/
private def stepD (st : State) (m : Move) : State :=
  match st.step m with
  | none => st
  | some s' => s'

/-! ## §1. The hostile board `ab0`

The pre-broken guard economy: hearts at one (the A♥ founded BEFORE
the run), diamonds empty with the A♦ FACE-UP as the surviving cover
cell, the black family parked at empty rungs with the TWOs face-up
(the below-frontier pair), every other card sunk in the stock. -/

private def AH : Card := crd .heart .ace
private def AD : Card := crd .diamond .ace
private def S2 : Card := crd .spade .two
private def C2 : Card := crd .club .two

/-- The hostile rungs: ♠ 0, ♣ 0, ♥ 1, ♦ 0 (the A♥ pre-founded). -/
private def hmapB : Suit → Nat
  | .spade => 0 | .club => 0 | .heart => 1 | .diamond => 0

/-- **THE HOSTILE START `ab0`**: p0 = [2♠] and p1 = [2♣] (the
below-frontier pair, bare over empty hidden decks); p2 = [A♦] (the
surviving cover cell, face-up); all other piles fully empty; the
whole rest of the deck in the stock; waste empty and `drawStep = 1`
so the raise arm reads the pair cold (both black rungs sit one below
the twos) and the slide arm reads no fits. -/
private def ab0 : State where
  found := fun s => takeUp s (hmapB s)
  piles := fun a => match a with
    | .p0 => ⟨[], [S2]⟩
    | .p1 => ⟨[], [C2]⟩
    | .p2 => ⟨[], [AD]⟩
    | .p3 => ⟨[], []⟩
    | .p4 => ⟨[], []⟩
    | .p5 => ⟨[], []⟩
    | .p6 => ⟨[], []⟩
  stock :=
    [crd .spade .ace, crd .spade .three, crd .spade .four, crd .spade .five,
     crd .spade .six, crd .spade .seven, crd .spade .eight, crd .spade .nine,
     crd .spade .ten, crd .spade .jack, crd .spade .queen, crd .spade .king,
     crd .club .ace, crd .club .three, crd .club .four, crd .club .five,
     crd .club .six, crd .club .seven, crd .club .eight, crd .club .nine,
     crd .club .ten, crd .club .jack, crd .club .queen, crd .club .king,
     crd .heart .two, crd .heart .three, crd .heart .four, crd .heart .five,
     crd .heart .six, crd .heart .seven, crd .heart .eight, crd .heart .nine,
     crd .heart .ten, crd .heart .jack, crd .heart .queen, crd .heart .king,
     crd .diamond .two, crd .diamond .three, crd .diamond .four,
     crd .diamond .five, crd .diamond .six, crd .diamond .seven,
     crd .diamond .eight, crd .diamond .nine, crd .diamond .ten,
     crd .diamond .jack, crd .diamond .queen, crd .diamond .king]
  waste := []
  drawStep := 1

private theorem ab0_wf_found : ∀ s : Suit, ∃ n, ab0.found s = s.upCards.take n := by
  intro s
  cases s with
  | spade => exact ⟨0, rfl⟩
  | club => exact ⟨0, rfl⟩
  | heart => exact ⟨1, rfl⟩
  | diamond => exact ⟨0, rfl⟩

private theorem ab0_wf_runs : ∀ a : Anchor, runOK (ab0.piles a).faceUp = true := by
  intro a
  cases a <;> rfl

private theorem ab0_wf_count : ∀ c ∈ Card.universe, ab0.cardCount c = 1 := by
  intro c _
  rcases c with ⟨s, r⟩
  cases s <;> cases r <;> decide

/-- The hostile board is `WF` (kernel-decided). -/
private theorem ab0_wf : ab0.WF :=
  ⟨ab0_wf_found, ab0_wf_runs, ab0_wf_count, by decide⟩

/-! ## §2. The hostile leg and the stuck landing
-/

/-- **THE PRE-BROKEN GUARD**: the no-eat guard does not protect the
surviving cover cell — its ace twin lives on the HEART foundation
(`MobileTwin A♦` fails at the face-up conjunct for the founded
twin), so the hostile raise is unblocked. -/
theorem ab0_guard : ∀ y, MobileTwin ab0 y → AD ≠ y ∧ AD ≠ y.twin := by
  intro y hy
  constructor
  · intro heq
    obtain ⟨-, -, ⟨b, hb⟩, -⟩ := hy
    rw [← heq, show AD.twin = AH from rfl] at hb
    cases b <;> exact absurd hb (by decide)
  · intro heq
    obtain ⟨⟨a, ha⟩, -, -, -⟩ := hy
    have h1 : y = y.twin.twin := (Card.twin_twin y).symm
    rw [h1, show y.twin = AD from heq.symm,
      show AD.twin = AH from rfl] at ha
    cases a <;> exact absurd ha (by decide)

/-- **THE HOSTILE LEG FIRES**: the A♦ raise is a legal, unguarded,
licensed ascent move. -/
theorem ab0_ascentMove : AscentMove ab0 (Move.tabToFound AD) :=
  Or.inl ⟨AD, rfl,
    show AD.rank.toIdx = ab0.foundHeight AD.suit from rfl,
    ⟨.p2, by decide⟩,
    ab0_guard⟩

/-- The hostile landing: the A♦ founded, diamonds at one. -/
private def ab1 : State := stepD ab0 (Move.tabToFound AD)

theorem ab1_step : State.step ab0 (Move.tabToFound AD) = some ab1 := by rfl

/-- **THE HOSTILE RUN**: the one-leg ascent from `ab0` into the
stuck landing. -/
theorem ab0_run : AscentRun ab0 [Move.tabToFound AD] ab1 :=
  AscentRun.cons ab0_ascentMove ab1_step (AscentRun.nil ab1)

/-- The landing is WF (the step preserves it). -/
private theorem ab1_wf : ab1.WF := step_wf ab0_wf ab1_step

/-- The frozen landing piles (the step's kernel reduction: the A♦
departed to the diamond foundation, the emptied pile revealed
nothing, every other pile is untouched). -/
private theorem ab1_p0 : ab1.piles .p0 = ⟨[], [S2]⟩ := rfl
private theorem ab1_p1 : ab1.piles .p1 = ⟨[], [C2]⟩ := rfl
private theorem ab1_p2 : ab1.piles .p2 = ⟨[], []⟩ := rfl
private theorem ab1_p3 : ab1.piles .p3 = ⟨[], []⟩ := rfl
private theorem ab1_p4 : ab1.piles .p4 = ⟨[], []⟩ := rfl
private theorem ab1_p5 : ab1.piles .p5 = ⟨[], []⟩ := rfl
private theorem ab1_p6 : ab1.piles .p6 = ⟨[], []⟩ := rfl

/-- **THE FACE-UP INVENTORY AT THE LANDING**: only the black twos
stand face-up (the A♦ departed to the diamond foundation; every
hidden deck was empty, so no reveal fired). -/
theorem ab1_faceUp : ∀ c ∈ Card.universe,
    (∃ a, c ∈ (ab1.piles a).faceUp) → c = S2 ∨ c = C2 := by
  intro c _ ⟨a, hc⟩
  cases a with
  | p0 => rw [ab1_p0] at hc; simp at hc; exact Or.inl hc
  | p1 => rw [ab1_p1] at hc; simp at hc; exact Or.inr hc
  | p2 => rw [ab1_p2] at hc; cases hc
  | p3 => rw [ab1_p3] at hc; cases hc
  | p4 => rw [ab1_p4] at hc; cases hc
  | p5 => rw [ab1_p5] at hc; cases hc
  | p6 => rw [ab1_p6] at hc; cases hc

/-- **THE STUCK LANDING**: `ab1` is exhausted — no raise is hot
among the standing face-up cards (the twos sit one index above
their suits' empty rungs), and no slide places (a non-twos run head
has no face-up residence at all; the two face-up tops fit neither
each other's tops nor an empty king seat). -/
theorem ab1_stuck : AscentStuck ab1 := by
  intro m hm
  rcases hm with ⟨c, hmEq, hhot, hface, -⟩ | ⟨c, b, hmEq⟩
  · rw [hmEq]
    have hfc := ab1_faceUp c (Card.mem_universe c) hface
    rcases hfc with hs | hc
    · rw [hs]; decide
    · rw [hc]; decide
  · rw [hmEq]
    -- the slide arm: crush by the finite placement inventory
    cases b with
    | inl n =>
        rcases c with ⟨cs, cr⟩
        cases cs <;> cases cr <;> cases n <;> decide
    | inr z =>
        rcases c with ⟨cs, cr⟩
        rcases z with ⟨zs, zr⟩
        cases cs <;> cases cr <;> cases zs <;> cases zr <;> decide

/-! ## §3. The verdict rows
-/

/-- The founded heights at the landing: hearts and diamonds both at
one (BOTH cover cells founded below their frontiers). -/
theorem ab1_founded_heights :
    ab1.foundHeight Suit.heart = 1 ∧ ab1.foundHeight Suit.diamond = 1 :=
  ⟨by rfl, by rfl⟩

/-- **THE COVER CLAUSES ARE UNSATISFIABLE AT THE LANDING**: the
delivered twin must be a face-up black two, its fitting covers are
exactly the two red aces, and both are founded below their suits'
frontiers — the un-founded clause fails by one index. -/
theorem ab1_noHalt : ¬ TwinSlideHalt ab1 := by
  rintro ⟨x, d, ⟨a, b, hx, hxt, -, -⟩, hd1, hd2, hd3, -, -⟩
  have hfx : x = S2 ∨ x = C2 := ab1_faceUp x (Card.mem_universe x) ⟨a, hx⟩
  rcases hfx with rfl | rfl <;>
    rcases d with ⟨ds, dr⟩ <;>
    cases ds <;> cases dr <;>
    first
    | omega
    | exact absurd hd1 (by decide)
    | exact absurd hd3 (by decide)
    | exact absurd hd2 (by decide)

/-! ## §4. The intact-cell contrast, the cell guard trap, and the β-repair draft
-/

/-- The intact-cell board `ab2`: the pair as in `ab0`, but BOTH red
aces face-up — the two cover cells stand as an INTACT mobile pair
(every `MobileTwin` conjunct reads true for each cell), so the
full-time no-eat guard protects them both. -/
private def ah2p : Suit → Nat
  | .spade => 0 | .club => 0 | .heart => 0 | .diamond => 0

private def ab2 : State where
  found := fun s => takeUp s (ah2p s)
  piles := fun a => match a with
    | .p0 => ⟨[], [S2]⟩
    | .p1 => ⟨[], [C2]⟩
    | .p2 => ⟨[], [AH]⟩
    | .p3 => ⟨[], [AD]⟩
    | .p4 => ⟨[], []⟩
    | .p5 => ⟨[], []⟩
    | .p6 => ⟨[], []⟩
  stock :=
    [crd .spade .ace, crd .spade .three, crd .spade .four, crd .spade .five,
     crd .spade .six, crd .spade .seven, crd .spade .eight, crd .spade .nine,
     crd .spade .ten, crd .spade .jack, crd .spade .queen, crd .spade .king,
     crd .club .ace, crd .club .three, crd .club .four, crd .club .five,
     crd .club .six, crd .club .seven, crd .club .eight, crd .club .nine,
     crd .club .ten, crd .club .jack, crd .club .queen, crd .club .king,
     crd .heart .two, crd .heart .three, crd .heart .four, crd .heart .five,
     crd .heart .six, crd .heart .seven, crd .heart .eight, crd .heart .nine,
     crd .heart .ten, crd .heart .jack, crd .heart .queen, crd .heart .king,
     crd .diamond .two, crd .diamond .three, crd .diamond .four,
     crd .diamond .five, crd .diamond .six, crd .diamond .seven,
     crd .diamond .eight, crd .diamond .nine, crd .diamond .ten,
     crd .diamond .jack, crd .diamond .queen, crd .diamond .king]
  waste := []
  drawStep := 1

private theorem ab2_wf_found : ∀ s : Suit, ∃ n, ab2.found s = s.upCards.take n := by
  intro s
  cases s with
  | spade => exact ⟨0, rfl⟩
  | club => exact ⟨0, rfl⟩
  | heart => exact ⟨0, rfl⟩
  | diamond => exact ⟨0, rfl⟩

private theorem ab2_wf_runs : ∀ a : Anchor, runOK (ab2.piles a).faceUp = true := by
  intro a
  cases a <;> rfl

private theorem ab2_wf_count : ∀ c ∈ Card.universe, ab2.cardCount c = 1 := by
  intro c _
  rcases c with ⟨s, r⟩
  cases s <;> cases r <;> decide

/-- The intact-cell board is `WF` (kernel-decided). -/
private theorem ab2_wf : ab2.WF :=
  ⟨ab2_wf_found, ab2_wf_runs, ab2_wf_count, by decide⟩

/-- **THE CELL GUARD TRAP, DATUM SIDE**: at the intact-cell board the
cover cells' own `MobileTwin` read holds — each cell is the other's
twin, both face-up, both at-or-above their (empty) rungs — so the
no-eat guard's own predicate is live for them. -/
theorem ab2_cellMobile : MobileTwin ab2 AH ∧ MobileTwin ab2 AD :=
  ⟨⟨⟨Anchor.p2, by decide⟩, by decide, ⟨Anchor.p3, by decide⟩, by decide⟩,
   ⟨⟨Anchor.p3, by decide⟩, by decide, ⟨Anchor.p2, by decide⟩, by decide⟩⟩

/-- **THE ARMOR DATUM**: at the intact-cell board the hostile raise
is NOT an ascent move — the guard declines founding either cell
(its own `MobileTwin` witness must stay intact). -/
theorem ab2_raiseNotAscent : ¬ AscentMove ab2 (Move.tabToFound AD) ∧
    ¬ AscentMove ab2 (Move.tabToFound AH) := by
  constructor
  · rintro (hc | hslide)
    · obtain ⟨c, heq, -, -, hguard⟩ := hc
      injection heq with heqc
      rw [← heqc] at hguard
      exact absurd rfl (hguard AH ab2_cellMobile.1).2
    · obtain ⟨c, b, hb⟩ := hslide
      exact absurd hb (by simp)
  · rintro (hc | hslide)
    · obtain ⟨c, heq, -, -, hguard⟩ := hc
      injection heq with heqc
      rw [← heqc] at hguard
      exact absurd rfl (hguard AD ab2_cellMobile.2).2
    · obtain ⟨c, b, hb⟩ := hslide
      exact absurd hb (by simp)

/-- **THE β-REPAIR DRAFT** (lemma-level statement, presented for the
owner's ratification — the exhausted shape's cover clause weakened
to the RECOVERABLE disjunct): a fitting cover is delivered either
STANDING at the tableau (the frozen `TwinSlideHalt` clause) or
FOUNDED at its suit's frontier, exactly one licensed `foundToTab`
return away.  The drafted clauses are chosen so the decided hostile
landing `ab1` satisfies the recoverable side verbatim (the witness
row below): the founded A♦ is the diamond foundation top at the
frontier, and its licensed return base — the black two's top — is
present at the same exhausted state. -/
def TwinSlideHaltRec (st : State) : Prop :=
  ∃ (x d : Card),
    DoubleHot st x ∧
      d.rank.toIdx + 1 = x.rank.toIdx ∧
      d.suit.color ≠ x.suit.color ∧
      canSitOn d x.twin = true ∧
      ((d.rank.toIdx ≥ st.foundHeight d.suit ∧
          (∃ (c : Anchor), d ∈ (st.piles c).faceUp)) ∨
        (st.foundTop d.suit = some d ∧
          d.rank.toIdx + 1 = st.foundHeight d.suit ∧
          ∃ (e : Card), st.canPlace d (Sum.inr e) = true))

/-- **THE RECOVERABILITY DATUM**: at the hostile founding-burial
landing the drafted recoverable side holds for the founded cover
cell — the diamond foundation top is exactly the buried A♦ at its
suit's frontier, and a licensed landing base (the black two's top)
is present at the same exhausted state. -/
theorem ab1_beta_recoverability :
    ab1.foundTop Suit.diamond = some AD ∧
      AD.rank.toIdx + 1 = ab1.foundHeight Suit.diamond ∧
      ab1.canPlace AD (Sum.inr S2) = true :=
  ⟨by rfl, rfl, by
    show (match ab1.pileOfTop S2 with
      | some _ => canSitOn AD S2
      | none => false) = true
    have hpot : ab1.pileOfTop S2 = some Anchor.p0 := by decide
    rw [hpot]
    rfl⟩

/-! ## §5. The hunt's verdict (decide-adjacent; the structural rest priced)
-/

/- VERDICT, three datapoints deep:

* BURIAL-BARRED inside the intact-cell armor — at `ab2` the cell
  pair's own `MobileTwin` stands, the guard declines both cell
  raises (`ab2_raiseNotAscent`), and the pair is UNBREAKABLE within
  the ascent alphabet: every break mode for the cells' mobility
  (founding a member, burying a member's face-up) requires a
  founding-or-consumption, the founding needs the guard already
  broken (circular, hence barred), and the slide consumption is
  REFUTED outright by `Orig/ForkAscent.lean`'s `ascent_selfland_refuted`
  (a run rider can never be its own landing base: the guard's fit
  arithmetic is a rank contradiction).  THE NAMED INVARIANT: a
  cell pair that starts `MobileTwin`-intact can never lose either
  member along an ascent run.
* BURIAL-BUILDS wherever a cell arrives PRE-BROKEN — the `ab0`/`ab1`
  economy decided above (pre-founded cell, guard off at the
  conjunct for the founded twin, one licensed raise, stuck landing,
  no standing cover).  The exhaustion row's `hbelow` premise
  COUPLES NOTHING to the cover cells (the fork-play `π` and the
  ascent-run `ρ` are independent plays; the premise's visible
  parcel constrains the pair members only), so the structural read
  is that a pre-broken-cell board with a reachable fork remains
  hbelow-compatible in principle; this file has not decided that
  co-existence (the full-alphabet reachability computation), and
  says so.
* THE REPAIR INDICATED: β, drafted above as `TwinSlideHaltRec` —
  with the decisive datum that the hostile landing itself satisfies
  the recoverable side (`ab1_beta_recoverability`: a founded
  frontier cell with a licensed return base at the same state).
  At the r = 1 corner the recoverable side is the ONLY side a
  founded ace can satisfy (aces never re-seat themselves on the
  tableau by the tabToFound alphabet); the draft is presented for
  the owner's ratification and the main row's statement in
  `Orig/ForkAscent.lean` is left byte-frozen. -/

/-! ## The audit battery -/

#print axioms ab0_guard
#print axioms ab0_ascentMove
#print axioms ab0_run
#print axioms ab1_stuck
#print axioms ab1_noHalt
#print axioms ab2_cellMobile
#print axioms ab2_raiseNotAscent
#print axioms ab1_beta_recoverability
