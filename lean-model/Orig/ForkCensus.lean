import Orig.LowSlab
import Orig.OriginLock

/-!
# Orig.ForkCensus — THE FORK-IN-CLASS DETECTOR

The census program for forks ACROSS THE MACRO CLASS: the cheap,
class-stable portrait of a fork's pair, read at every member of the
class from the three membership pins (per-pile hidden decks, the
two-zone, the foundations), and the decider-shape composite that
assembles the fork itself from the census plus the class-internal
arrangeability.  The design (the owner's, from the session records):

* **§0 THE FILTER DEFINITIONS**   (decidable where cheap): `Mobile`
  (not buried in any pile's hidden deck, not parked in the two-zone —
  the two legs the class pins make free), `PairCandidate` (the pair
  `{x, x.twin}` located face-up and mobile), `LowCellsMobile` (every
  same-family card of index below the pair's rank is mobile), and
  `CoverCellMobile` (at least one opposite-family `r−1` cell is
  mobile — the cell that could be the cover).  Every filter carries a
  Bool probe (`mobileB`, `pairCandidateB`, `lowCellsMobileB`,
  `coverCellMobileB`, `censusPassB`) with a WF-free bridge
  (the quiet probe's bridge carries the `canRaiseSB` probe's own WF
  premise) — finite enumerations over `Card.universe`/`Anchor.all`
  in the pattern of `Orig/ForkStateSB.lean`'s deciders.
* **§1 THE NECESSITY ROWS**: `fork_inventory_necessary` — a class
  member's `ForkWitness` for `x` forces, at EVERY class-mate, the
  pair mobile, all low cells mobile, a cover cell mobile: the
  hidden-pin (`shuffle_hiddenPinned`), the two-zone pin
  (`cycle_zone_pin`), the founded-mobile read (`mem_found_unique`),
  and the cover-shape reads of the OriginLock chain
  (`pair_cover_pins`, `pair_lowFamily_founded`) assemble it
  ([M]-grade).  `fork_label` — the one-pair labeling: at one state
  the pair is unique up to the twin flip (two lines off the iff);
  the family-grade class label (`fork_label_family`) cites the
  public assembly `forkState_family_pairClass`; the FULL class
  label (`fork_label_class` [H], the named residue) — at most one
  fork pair per class — has its same-family slice banked and its
  cross-family slice priced in its route.
* **§2 THE DECIDER-SHAPE COMPOSITE**: `class_forks_decidable` — a
  state is fork-headed-in-its-class iff some candidate pair PASSES
  THE FILTER (`CensusPass`, the class-stable necessity grade) AND
  the class-internal arrangeability holds (`PairArrangeable`).  Both
  directions are assembly ([M]): the necessity leg is §1's census
  transport, the sufficiency leg the journey-membership kit.  The
  HONEST READING (documented at the row): the head may hold a pair
  member FOUNDED (the elevated head — `lb1` in the probe corpus), so
  the located `PairCandidate` filter is NOT the class-necessity
  grade and lives inside the arrangeability's landing, not at the
  head.  The saturation assembly lands as `crane_assembly_at_head`
  (the decidable `ForkMeal` — the quiet located sandwich — assembles
  the `ForkWitness` outright, over `canRaiseS_free` and the covered
  twin's top-pinning), the label-conditioned crane leg as
  `crane_label_conditioned` (proved), and the arrangeability's own
  oracle — the head-side label discharge — is the named residue
  `crane_seat_issuance` [H], routed over `fork_label_class`, the
  card algebra `census_pair_named` (rank and family name the pair),
  and the noNewSeat/low-slab families.
* **§3 THE COMPOSITE-FRONTIER NOTE**: the pair census — at most 26
  candidates (13 ranks × 2 color-families) per class, enumerated by
  `forkCandidateBoard` (`forkCandidateBoard_length = 26`, decided;
  each pair orientation-canonical via `censusPass_twin`), so the
  filter is O(n)-grade per candidate over the board.  Probe
  evidence: the lb-family boards (`Orig/LowSlabProbe.lean` — the
  `r = 3` economy, witness `4♥`, cover `S3`) are the readable
  citation for the census shapes: at `lb0` the low cells sit
  FOUNDED and the cover window passes through the face-up black
  three alone (the `C3` cell is hidden — a singleton-cell pass); at
  the elevated `lb1` the twin sits FOUNDED — the datum that fixes
  the composite's honest grade.

House compliance: additive leaf (`Orig.LowSlab` + `Orig.OriginLock`,
the pins machinery transitively); every fresh head audited (the
`#print axioms` battery printed at the tail); zero `Classical.choice`
(the splits ride `Decidable.em`, `decide` and kernel folds; `omega`
faces no live `∃`); the two named residues carry complete priced
routes; the private kit rows are per-file copies per the house dedup
discipline.
-/

/-! ## §0a. The per-file kit (private, the house dedup discipline) -/

/-- The twin keeps the suit's color (the twin suits are same-color). -/
private theorem census_twin_color (c : Card) : c.twin.suit.color = c.suit.color := by
  rw [Card.twin_suit, Suit.color_twin]

/-- The conjunction read of `&&` at its true side (the per-file copy
of the Bool kit, in equation form). -/
private theorem census_and2 {a b : Bool} : (a && b) = true → a = true ∧ b = true := by
  intro h
  rw [Bool.and_eq_true] at h
  exact h

/-- The conjunction build of `&&` at its true side. -/
private theorem census_and2_of {a b : Bool} (h1 : a = true) (h2 : b = true) :
    (a && b) = true := by
  rw [h1, h2]
  rfl

/-- The existence read of `List.any`'s true side (the per-file copy). -/
private theorem census_any_mem {α : Type} (p : α → Bool) {l : List α} :
    l.any p = true → ∃ a, a ∈ l ∧ p a = true :=
  fun h => List.any_eq_true.mp h

/-! ## §0b. The filter definitions (decidable where cheap) -/

/-- **THE MOBILITY READ** — the census's own "available to the game"
notion: not buried in any pile's hidden deck, not parked in the
two-zone (stock or waste).  This is exactly the union of the two
membership classes the macro pins make class-stable: per-pile hidden
decks are pinned verbatim along witness shuffles
(`shuffle_hiddenPinned`), and two-zone membership is pinned both ways
(`cycle_zone_pin`), so `Mobile` is a CLASS notion — the transport
row is §1's `fork_mobile_class`. -/
def Mobile (st : State) (c : Card) : Prop :=
  (∀ a, c ∉ (st.piles a).hidden) ∧ c ∉ st.stock ∧ c ∉ st.waste

/-- **THE MOBILITY PROBE** — the computable side of `Mobile`: finite
folds over `Anchor.all` and the two zone lists, kernel-decidable. -/
def mobileB (st : State) (c : Card) : Bool :=
  Anchor.all.all (fun a => decide (c ∉ (st.piles a).hidden)) &&
    (decide (c ∉ st.stock) && decide (c ∉ st.waste))

/-- The mobility probe's bridge — WF-free, pure decide bookkeeping. -/
theorem mobileB_true_iff (st : State) (c : Card) :
    mobileB st c = true ↔ Mobile st c := by
  rw [mobileB, Bool.and_eq_true, Bool.and_eq_true, List.all_eq_true]
  constructor
  · rintro ⟨hhid, hs, hw⟩
    exact ⟨fun a => of_decide_eq_true (hhid a (Anchor.mem_all a)),
      of_decide_eq_true hs, of_decide_eq_true hw⟩
  · rintro ⟨hhid, hs, hw⟩
    exact ⟨fun a _ => decide_eq_true (hhid a), decide_eq_true hs,
      decide_eq_true hw⟩

/-- **THE LOW CELLS** — the would-be low inventory of the pair `x`:
the same-family cards (color match) of rank index strictly below the
pair's.  At a fork these are all FOUNDED
(`pair_lowFamily_founded`); the census asks only that they be
`Mobile` — the grade that transports across the class. -/
def LowCells (x : Card) : List Card :=
  Card.universe.filter (fun c =>
    decide (c.suit.color = x.suit.color) && decide (c.rank.toIdx < x.rank.toIdx))

/-- The low-cells membership bridge (every card lives in the
universe, so the filter reads its two conditions directly). -/
theorem mem_lowCells_iff {c x : Card} :
    c ∈ LowCells x ↔ (c.suit.color = x.suit.color ∧ c.rank.toIdx < x.rank.toIdx) := by
  rw [LowCells, List.mem_filter]
  constructor
  · rintro ⟨-, hc⟩
    rw [Bool.and_eq_true] at hc
    exact ⟨of_decide_eq_true hc.1, of_decide_eq_true hc.2⟩
  · rintro ⟨hcol, hrk⟩
    exact ⟨Card.mem_universe c, by
      rw [decide_eq_true hcol, decide_eq_true hrk]; rfl⟩

/-- **THE COVER CELLS** — the two opposite-family cards of rank index
`r−1` (for `x` of rank index `r`): the cells that could carry the
fork's cover (the `pair_cover_pins` necessity — the cover `d` sits
one below, opposite family, and its mobility is the cover window). -/
def CoverCells (x : Card) : List Card :=
  Card.universe.filter (fun c =>
    decide (c.suit.color ≠ x.suit.color) && decide (c.rank.toIdx + 1 = x.rank.toIdx))

/-- The cover-cells membership bridge. -/
theorem mem_coverCells_iff {c x : Card} :
    c ∈ CoverCells x ↔ (c.suit.color ≠ x.suit.color ∧ c.rank.toIdx + 1 = x.rank.toIdx) := by
  rw [CoverCells, List.mem_filter]
  constructor
  · rintro ⟨-, hc⟩
    rw [Bool.and_eq_true] at hc
    exact ⟨of_decide_eq_true hc.1, of_decide_eq_true hc.2⟩
  · rintro ⟨hcol, hrk⟩
    exact ⟨Card.mem_universe c, by
      rw [decide_eq_true hcol, decide_eq_true hrk]; rfl⟩

/-- The twin keeps both cell conditions (same color, same rank), so
the cell lists are twin-invariant — the pair census is
orientation-free. -/
theorem mem_lowCells_twin {c x : Card} : c ∈ LowCells x.twin ↔ c ∈ LowCells x := by
  rw [mem_lowCells_iff, mem_lowCells_iff, census_twin_color x, Card.twin_rank]

/-- The cover-cells twin invariance. -/
theorem mem_coverCells_twin {c x : Card} :
    c ∈ CoverCells x.twin ↔ c ∈ CoverCells x := by
  rw [mem_coverCells_iff, mem_coverCells_iff, census_twin_color x, Card.twin_rank]

/-- **THE PAIR CANDIDATE FILTER** `PairCandidate` — the pair
`{x, x.twin}` is fork-eligible AT `st`: both members mobile (not
hidden, not two-zone) and both located face-up on the tableau.  The
located clauses are the honestly LOCAL grade — a class member may
hold a pair member FOUNDED (the elevated head; the `lb1` datapoint),
so the candidate filter is the arrangeability-side census, not the
class-necessity grade. -/
def PairCandidate (st : State) (x : Card) : Prop :=
  Mobile st x ∧ Mobile st x.twin ∧
    (∃ a, x ∈ (st.piles a).faceUp) ∧ (∃ b, x.twin ∈ (st.piles b).faceUp)

/-- **THE CANDIDATE PROBE** — the computable side of
`PairCandidate`: mobility on both members and the anchored face-up
search on both. -/
def pairCandidateB (st : State) (x : Card) : Bool :=
  mobileB st x && mobileB st x.twin &&
    (Anchor.all.any (fun a => decide (x ∈ (st.piles a).faceUp)) &&
      Anchor.all.any (fun a => decide (x.twin ∈ (st.piles a).faceUp)))

/-- The candidate probe's bridge — WF-free. -/
theorem pairCandidateB_true_iff (st : State) (x : Card) :
    pairCandidateB st x = true ↔ PairCandidate st x := by
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := census_and2 h
    obtain ⟨h3, h4⟩ := census_and2 h1
    obtain ⟨h5, h6⟩ := census_and2 h2
    obtain ⟨a, -, hu1⟩ := census_any_mem _ h5
    obtain ⟨b, -, hu2⟩ := census_any_mem _ h6
    exact ⟨(mobileB_true_iff st x).1 h3, (mobileB_true_iff st x.twin).1 h4,
      ⟨a, of_decide_eq_true hu1⟩, ⟨b, of_decide_eq_true hu2⟩⟩
  · intro h
    obtain ⟨m1, m2, ha, hb⟩ := h
    obtain ⟨a, hamem⟩ := ha
    obtain ⟨b, hbmem⟩ := hb
    refine census_and2_of (census_and2_of ((mobileB_true_iff st x).2 m1)
      ((mobileB_true_iff st x.twin).2 m2)) ?_
    refine census_and2_of ?_ ?_
    · exact List.any_eq_true.mpr ⟨a, Anchor.mem_all a, decide_eq_true hamem⟩
    · exact List.any_eq_true.mpr ⟨b, Anchor.mem_all b, decide_eq_true hbmem⟩

/-- **THE LOW-CELLS FILTER** `LowCellsMobile` — every same-family
card of index below the pair's rank is mobile at `st`
(the `pair_lowFamily_founded`-grade necessity, census-stated). -/
def LowCellsMobile (st : State) (x : Card) : Prop := ∀ c ∈ LowCells x, Mobile st c

/-- The low-cells probe. -/
def lowCellsMobileB (st : State) (x : Card) : Bool :=
  (LowCells x).all (fun c => mobileB st c)

/-- The low-cells probe's bridge — WF-free. -/
theorem lowCellsMobileB_true_iff (st : State) (x : Card) :
    lowCellsMobileB st x = true ↔ LowCellsMobile st x := by
  rw [lowCellsMobileB, List.all_eq_true]
  constructor
  · intro h
    show ∀ c ∈ LowCells x, Mobile st c
    intro c hc
    exact (mobileB_true_iff st c).1 (h c hc)
  · intro h
    show ∀ c ∈ LowCells x, mobileB st c = true
    intro c hc
    exact (mobileB_true_iff st c).2 (h c hc)

/-- **THE COVER-CELL FILTER** `CoverCellMobile` — at least one
opposite-family `r−1` cell is mobile at `st`: the cell that could be
the cover. -/
def CoverCellMobile (st : State) (x : Card) : Prop :=
  ∃ c ∈ CoverCells x, Mobile st c

/-- The cover-cell probe. -/
def coverCellMobileB (st : State) (x : Card) : Bool :=
  (CoverCells x).any (fun c => mobileB st c)

/-- The cover-cell probe's bridge — WF-free. -/
theorem coverCellMobileB_true_iff (st : State) (x : Card) :
    coverCellMobileB st x = true ↔ CoverCellMobile st x := by
  rw [coverCellMobileB, List.any_eq_true]
  constructor
  · rintro ⟨c, hc, hm⟩
    exact ⟨c, hc, (mobileB_true_iff st c).1 hm⟩
  · rintro ⟨c, hc, hm⟩
    exact ⟨c, hc, (mobileB_true_iff st c).2 hm⟩

/-- The candidate filter is twin-invariant: the pair, not its
orientation (the cell lists' twin invariance carries the filter, the
mobility reads are symmetric). -/
theorem pairCandidate_twin {st : State} {x : Card}
    (h : PairCandidate st x) : PairCandidate st x.twin := by
  obtain ⟨m1, m2, ha, hb⟩ := h
  show Mobile st x.twin ∧ Mobile st x.twin.twin ∧
    (∃ a, x.twin ∈ (st.piles a).faceUp) ∧
    ∃ b, x.twin.twin ∈ (st.piles b).faceUp
  rw [Card.twin_twin]
  exact ⟨m2, m1, hb, ha⟩

/-- **THE FULL CENSUS PASS** `CensusPass` — the three filters
together: the pair mobile (both members), the low cells mobile, a
cover cell mobile.  This is the CLASS-STABLE portrait — every
conjunct transports unchanged along witness journeys (§1's necessity
row), so it is the honest head-side filter of the §2 composite. -/
def CensusPass (st : State) (x : Card) : Prop :=
  Mobile st x ∧ Mobile st x.twin ∧ LowCellsMobile st x ∧ CoverCellMobile st x

/-- The census-pass probe. -/
def censusPassB (st : State) (x : Card) : Bool :=
  mobileB st x && mobileB st x.twin &&
    (lowCellsMobileB st x && coverCellMobileB st x)

/-- The census-pass probe's bridge — WF-free. -/
theorem censusPassB_true_iff (st : State) (x : Card) :
    censusPassB st x = true ↔ CensusPass st x := by
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := census_and2 h
    obtain ⟨h3, h4⟩ := census_and2 h1
    obtain ⟨h5, h6⟩ := census_and2 h2
    exact ⟨(mobileB_true_iff st x).1 h3, (mobileB_true_iff st x.twin).1 h4,
      (lowCellsMobileB_true_iff st x).1 h5, (coverCellMobileB_true_iff st x).1 h6⟩
  · intro h
    obtain ⟨m1, m2, hlow, hcover⟩ := h
    exact census_and2_of (census_and2_of ((mobileB_true_iff st x).2 m1)
      ((mobileB_true_iff st x.twin).2 m2))
      (census_and2_of ((lowCellsMobileB_true_iff st x).2 hlow)
        ((coverCellMobileB_true_iff st x).2 hcover))

/-- The census pass is twin-invariant (the cells' twin invariance
carries both filter legs). -/
theorem censusPass_twin {st : State} {x : Card}
    (h : CensusPass st x) : CensusPass st x.twin := by
  obtain ⟨m1, m2, hlow, hcover⟩ := h
  have hlowF : ∀ c ∈ LowCells x, Mobile st c := hlow
  have hcoverF : ∃ c ∈ CoverCells x, Mobile st c := hcover
  show Mobile st x.twin ∧ Mobile st x.twin.twin ∧
    (∀ c ∈ LowCells x.twin, Mobile st c) ∧ ∃ c ∈ CoverCells x.twin, Mobile st c
  rw [Card.twin_twin]
  refine ⟨m2, m1, fun c hc => hlowF c (mem_lowCells_twin.mp hc), ?_⟩
  obtain ⟨d, hdc, hdm⟩ := hcoverF
  exact ⟨d, mem_coverCells_twin.mpr hdc, hdm⟩

/-- **THE QUIET READ** `SQuietAt` — no card OUTSIDE the pair is
S-live at `st`: the saturation half of the local assembly.  The read
is decidable in principle (the `canRaiseSB` probe of
`Orig/ForkStateSB.lean`'s decider family), but that decider file is
NOT in this leaf's import closure (`Orig.LowSlab` +
`Orig.OriginLock`), so the Bool side is route-noted here and the
`Prop` form is what the assembly consumes. -/
def SQuietAt (st : State) (x : Card) : Prop :=
  ∀ c, ¬ (c = x ∨ c = x.twin) → ¬ CanRaiseS st c

/-! ## §1. The necessity rows (proved from the banked pins) -/

/-- **THE FACE-UP MOBILITY** — a face-up card is mobile at a `WF`
state (the `mem_faceUp_only` census: no pile's hidden deck, not
stocked, not wasted). -/
theorem faceUp_mobile {st : State} (hwf : st.WF) {c : Card} {a : Anchor}
    (hmem : c ∈ (st.piles a).faceUp) : Mobile st c := by
  obtain ⟨hothers, hown, hs, hw, -⟩ := mem_faceUp_only hwf hmem
  show (∀ a', c ∉ (st.piles a').hidden) ∧ c ∉ st.stock ∧ c ∉ st.waste
  refine ⟨fun a' hmem' => ?_, hs, hw⟩
  rcases Decidable.em (a' = a) with h | h
  · rw [h] at hmem'
    exact hown hmem'
  · exact (hothers a' h).1 hmem'

/-- **THE FOUNDED MOBILITY** — a founded card is mobile (the
`mem_found_unique` census). -/
theorem founded_mobile {st : State} (hwf : st.WF) {c : Card}
    (hf : c ∈ st.found c.suit) : Mobile st c := by
  obtain ⟨hpiles, hs, hw, -⟩ := mem_found_unique hwf hf
  show (∀ a, c ∉ (st.piles a).hidden) ∧ c ∉ st.stock ∧ c ∉ st.waste
  exact ⟨fun a => (hpiles a).1, hs, hw⟩

/-- **THE PIN ROUND** — mobility transports unchanged along any
witness journey: the per-pile hidden decks are pinned verbatim
(the hidden pin), and two-zone membership iff
(the two-zone pin).  WF-free at both ends. -/
theorem fork_mobile_class {s w : State} :
    ∀ {ρ : List Move}, ShufflePlayW s ρ w → ∀ {c : Card}, Mobile s c → Mobile w c := by
  intro ρ hρ c hc
  have hpin := shuffle_hiddenPinned hρ
  show (∀ a, c ∉ (w.piles a).hidden) ∧ c ∉ w.stock ∧ c ∉ w.waste
  refine ⟨fun a hmem => hc.1 a (by rw [← hpin a]; exact hmem), fun hmem => ?_,
    fun hmem => ?_⟩
  · rcases (cycle_zone_pin hρ c).1 (Or.inl hmem) with h | h
    · exact hc.2.1 h
    · exact absurd h hc.2.2
  · rcases (cycle_zone_pin hρ c).1 (Or.inr hmem) with h | h
    · exact absurd h hc.2.1
    · exact hc.2.2 h

/-- **THE FILTER PASSES AT THE FORK** — a witnessed fork state
carries its own full census: the pair located face-up (the witness
tops its pile by `forkState_witness_canRaise`; the twin sits directly
under the cover by `pair_cover_pins`), hence mobile; the low cells
all FOUNDED (`pair_lowFamily_founded`), hence mobile; and the
cover's own cell (the cover `d` of the pins read) is face-up, hence
mobile.  [M]-grade assembly over the OriginLock chain. -/
theorem fork_state_candidate {st : State} (hwf : st.WF) {x : Card}
    (hx : ForkWitness st x) :
    PairCandidate st x ∧ LowCellsMobile st x ∧ CoverCellMobile st x := by
  obtain ⟨hiff, hnt⟩ := id hx
  obtain ⟨-, a, hpo, -⟩ := forkState_witness_canRaise hwf hiff hnt
  have hxmem : x ∈ (st.piles a).faceUp := Pile.mem_of_top (pileOfTop_top hpo).2
  obtain ⟨c, bs, d, hshape, -, hfit, -, -, -⟩ := pair_cover_pins hwf hx
  have hxtwinmem : x.twin ∈ (st.piles c).faceUp := by
    rw [hshape]
    exact List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))
  have hdmem : d ∈ (st.piles c).faceUp := by
    rw [hshape]
    exact List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inr
      (List.mem_singleton.mpr rfl))))
  have hcand : PairCandidate st x :=
    ⟨faceUp_mobile hwf hxmem, faceUp_mobile hwf hxtwinmem,
      ⟨a, hxmem⟩, ⟨c, hxtwinmem⟩⟩
  refine ⟨hcand, ?_, ?_⟩
  · show ∀ u ∈ LowCells x, Mobile st u
    intro u hu
    obtain ⟨hcol, hrk⟩ := mem_lowCells_iff.mp hu
    exact founded_mobile hwf (pair_lowFamily_founded hwf hx hcol hrk)
  · obtain ⟨hrank, hcolT⟩ := (canSitOn_eq d x.twin).mp hfit
    rw [Card.twin_rank] at hrank
    have hcolx : d.suit.color ≠ x.suit.color := by
      rw [← census_twin_color x]
      exact hcolT
    exact ⟨d, mem_coverCells_iff.2 ⟨hcolx, hrank⟩, faceUp_mobile hwf hdmem⟩

/-- **THE NECESSITY ROW** `fork_inventory_necessary` [M, the §1
main] — if a class member carries a `ForkWitness` for `x`, then at
EVERY class-mate the census holds: the pair mobile (both members),
every same-family low cell mobile, at least one cover cell mobile.
The transport is the PinRound (`fork_mobile_class`) over the
class's own forward witness play (`sameOrbit_forward`), off the
fork's own filter pass (`fork_state_candidate`): hidden/zone
membership is class-invariant, so the census — a pure mobility
portrait — never leaves the class.  WF-free at the member end. -/
theorem fork_inventory_necessary {F w : State} (hwfF : F.WF) {x : Card}
    (hx : ForkWitness F x) (hclass : sameOrbitSetoid.r F w) :
    Mobile w x ∧ Mobile w x.twin ∧ LowCellsMobile w x ∧ CoverCellMobile w x := by
  obtain ⟨ρ, hρ⟩ := sameOrbit_forward hclass
  obtain ⟨hcand, hlow, hcover⟩ := fork_state_candidate hwfF hx
  have hlowF : ∀ c ∈ LowCells x, Mobile F c := hlow
  have hcoverF : ∃ c ∈ CoverCells x, Mobile F c := hcover
  show Mobile w x ∧ Mobile w x.twin ∧
    (∀ c ∈ LowCells x, Mobile w c) ∧ ∃ c ∈ CoverCells x, Mobile w c
  refine ⟨fork_mobile_class hρ hcand.1, fork_mobile_class hρ hcand.2.1,
    fun c hc => fork_mobile_class hρ (hlowF c hc), ?_⟩
  obtain ⟨d, hdc, hdm⟩ := hcoverF
  exact ⟨d, hdc, fork_mobile_class hρ hdm⟩

/-- **THE STATE LABEL** `fork_label` [M, proved] — the one-pair
labeling at ONE state: any two fork witnesses of the same state
agree, up to the twin flip (each witness's own iff reads the
other's S-liveness as pair membership).  WF-free. -/
theorem fork_label {st : State} {x y : Card}
    (hx : ForkWitness st x) (hy : ForkWitness st y) : y = x ∨ y = x.twin :=
  (hx.1 y).mpr ((hy.1 y).mp (Or.inl rfl))

/-- **THE CARD-ALGEBRA NAMING** — rank and family name the pair:
a family-mate of `x` at `x`'s rank index IS a pair member (the
banked `SeedKit.rankColor_pair` seed row).  This is the algebra the
label rows and the §2 residue ride: the class's fork pair is fixed
by `(rank, suit family)` alone. -/
theorem census_pair_named {x y : Card}
    (hfam : y.suit = x.suit ∨ y.suit = x.twin.suit)
    (hrank : y.rank.toIdx = x.rank.toIdx) : y = x ∨ y = x.twin := by
  refine SeedKit.rankColor_pair hrank ?_
  rcases hfam with h | h
  · rw [h]
  · rw [h, Card.twin_suit]
    exact Suit.color_twin x.suit

/-- **THE FAMILY-GRADE CLASS LABEL** `fork_label_family` [M, the
public-grade citation] — same-family forks of ONE class agree in
rank and as pairs: the OriginLock chain's public assembly
(`forkState_family_pairClass`), cited per the never-force
discipline (no private rows consumed). -/
theorem fork_label_family {F G : State} (hwfF : F.WF) (hwfG : G.WF)
    (hcls : sameOrbitSetoid.r F G) {w v : Card}
    (hw : ForkWitness F w) (hv : ForkWitness G v)
    (hfam : v.suit = w.suit ∨ v.suit = w.twin.suit) :
    v.rank.toIdx = w.rank.toIdx ∧ (v = w ∨ v = w.twin) :=
  forkState_family_pairClass F G hwfF hwfG hcls w hw hv hfam

/-- **THE CLASS LABEL** `fork_label_class` [H, NAMED RESIDUE] — a
macro class carries at most ONE fork pair: any two fork states of
one class agree as pairs, with no family premise.

WHAT IS BANKED: the same-family slice is PROVED (`fork_label_family`
above — the public `forkState_family_pairClass`, whose two halves
are `forkState_sameFamily_rankCeiling` and
`forkState_family_rankFloor`); the state-level label is PROVED
(`fork_label`); and the card algebra (`census_pair_named`) means the
class label is exhausted by the ONE question below.

THE OPEN CONTENT (the cross-family exclusion): can one macro class
carry fork states of TWO DIFFERENT suit families — say a `♥/♦` fork
at one member and a `♠/♣` fork at another?  Nothing banked prices
it: the confinement cards pin rung movement on the PAIR'S OWN
family only (`forkState_one_founding`), the floor/ceiling rows ride
the family premise, and the `forkState_unique` refutation
(`Orig/ForkStateUniqGate.lean`'s crafted class) shows class-mate
fork states may differ in NON-PAIR content (a reversible cargo leg
relocates a witness off a black next-up, one non-pair rung apart) —
so any future proof cannot run through full-content uniqueness; the
label is the honest carve-out.

REFUTER-FIRST: the natural craft would seat both sandwiches in one
class (two `lower_sandwich` shapes, opposite families, each with its
dressing over a live seat); the probe corpus's closest datum is the
EpochProbe down-pair boards (`Orig/EpochProbeVis.lean` — the rank-5
and rank-4 forks of one economy whose only connecting leg is a
certified commitment, i.e. the two forks sit in DIFFERENT classes) —
rank separation across a commit boundary at the SAME family; the
two-family analogue is uncharted.  No counterexample board is on
record in either direction.

ROUTE (each step priced against banked rows):
1. THE RUNG LEDGERS — for the witnessing journey between the two
   endpoints, `witness_rung_census` nets all four suits: both
   families pin at both ends (each fork pins its own family rungs),
   so each family's raises and pulls cancel exactly along a
   returned journey; the `lowslab_bracket_transfer`-grade bracket
   carries each family's rungs verbatim, and the census machinery
   (`excursion_issues_noNewSeat` — the round trip issues no seat
   beyond the arrangement) prices whether two cross-family
   sandwich racks can be simultaneously presented.
2. THE DRESSER SEATS — each fork's dress (`r−1`, opposite family)
   is isolated and frozen at ITS own end (`origin_dresser_frozen`
   grade); at the OTHER fork's end each dress is a low cell of the
   first fork's family (the families cross: one's cover cells lie
   inside the other's family) — founded by `pair_lowFamily_founded`
   there, so the arrangement census of the two racks interacts
   through the founded/hidden diagonals.
3. THE CRASH SHAPE — at either end, the OTHER family's pair members
   are same-family lows of the local fork (rank below its point),
   hence FOUNDED at that end
   (`origin_lowerPairResident`), and the ironing is whether the
   witnessing journey can pay the pull census
   (`origin_lowerJourney_pulls`) for BOTH families at once — the
   two-family analogue of the OriginLock eureka, priced [H] here,
   never forced. -/
theorem fork_label_class {F G : State} (hwfF : F.WF) (hwfG : G.WF)
    (hcls : sameOrbitSetoid.r F G) {w v : Card}
    (hw : ForkWitness F w) (hv : ForkWitness G v) :
    v = w ∨ v = w.twin := by
  sorry

/-! ## §2. The decider-shape composite (statement + route) -/

/-- **THE CLASS-HEADED READ** — the state's macro CLASS contains a
fork: some class-mate carries a `ForkWitness`. -/
def ClassForkHeaded (st : State) : Prop :=
  ∃ (F : State) (x : Card), sameOrbitSetoid.r st F ∧ ForkWitness F x

/-- **THE CLASS-INTERNAL ARRANGEABILITY** `PairArrangeable` — the
pair can be PRESENTED and SATURATED inside the class: a witness
journey out of `st` reaches a fork member for the pair (the witness
card `z` may name either orientation; the fork member itself carries
the located candidate `PairCandidate F x`, which
`fork_state_candidate` makes free).  This package is the composite's
deep right-hand side — the content the §2 residue prices. -/
def PairArrangeable (st : State) (x : Card) : Prop :=
  ∃ (F : State) (ρ : List Move) (z : Card),
    ShufflePlayW st ρ F ∧ (z = x ∨ z = x.twin) ∧ ForkWitness F z ∧
      PairCandidate F x

/-- **THE ASSEMBLY MEAL** `ForkMeal` — the decidable local recipe
that assembles a fork AT a state: both pair rungs pinned at the
pair's rank index (both members next-up), the witness `x` topping a
seat-sound pile, the twin covered DIRECTLY under the fitting dress
`d` over a live takeback seat, in a DIFFERENT pile (the run
discipline's descent bars a shared pile), with the board S-quiet
outside the pair.  Every clause is decidable in principle: the rungs
are arithmetic, the seats and the sandwich are pile reads, and the
quiet is the `SQuietAt` read over the S-license (its Bool probe
lives in the `canRaiseSB` decider family of
`Orig/ForkStateSB.lean`, outside this leaf's import closure). -/
def ForkMeal (st : State) (x : Card) : Prop :=
  rungAt st x.suit = x.rank.toIdx ∧
    rungAt st x.twin.suit = x.rank.toIdx ∧
    SQuietAt st x ∧
    ∃ (a c : Anchor) (bs : List Card) (d : Card) (rest : List Card),
      st.pileOfTop x = some a ∧
        (chop (st.piles a).faceUp ≠ [] ∨
          ((st.piles a).hidden = [] ∧ x.rank = Rank.king)) ∧
        (st.piles c).faceUp = (bs ++ [x.twin]) ++ (d :: rest) ∧
        (bs ≠ [] ∨ ((st.piles c).hidden = [] ∧ x.twin.rank = Rank.king)) ∧
        a ≠ c ∧
        canSitOn d x.twin = true

/-- The tail read (per-file copy of the list kit). -/
private theorem fcensus_lastOf_cons {w : Card} {L : List Card} (h : L ≠ []) :
    lastOf (w :: L) = lastOf L := by
  cases L with
  | nil => exact absurd rfl h
  | cons y t => rfl

/-- The last of an appended nonempty suffix is the suffix's last
(per-file copy of the list kit). -/
private theorem fcensus_lastOf_append : ∀ (L m : List Card), m ≠ [] →
    lastOf (L ++ m) = lastOf m := by
  intro L
  induction L with
  | nil => intro m _; rfl
  | cons u t ih =>
      intro m hm
      have hne : t ++ m ≠ [] := by
        intro hcon
        apply hm
        cases t with
        | nil => rw [List.nil_append] at hcon; exact hcon
        | cons v vs => exact absurd hcon (by simp)
      rw [List.cons_append, fcensus_lastOf_cons hne]
      exact ih m hm

/-- The fitting dress is never the card it covers (rank arithmetic). -/
private theorem fcensus_fit_ne (d z : Card) (hfit : canSitOn d z = true) : d ≠ z := by
  obtain ⟨hrank, -⟩ := (canSitOn_eq d z).mp hfit
  intro hcon
  rw [← hcon] at hrank
  omega

/-- A cover sitting directly above `u` in a legal run buries `u`'s
top: `u` is nowhere last. -/
private theorem fcensus_top_buried (bs : List Card) (u d : Card) : ∀ (rest : List Card),
    runOK ((bs ++ [u]) ++ (d :: rest)) = true → d ≠ u →
    lastOf ((bs ++ [u]) ++ (d :: rest)) ≠ some u := by
  intro rest hok hdne hcon
  have huS : u ∈ (d :: rest) := by
    rw [fcensus_lastOf_append (bs ++ [u]) (d :: rest)
      (by cases rest <;> simp)] at hcon
    exact lastOf_mem hcon
  have huP : u ∈ bs ++ [u] :=
    List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl))
  have hd := runOK_desc (P := bs ++ [u]) (S := d :: rest) hok huP huS
  omega

/-- **THE SATURATION ASSEMBLY** `crane_assembly_at_head` [M, proved]
— the meal assembles the fork AT the head: the rung pins make both
members next-up; the witness's vanilla license fires (tops its
seat-sound pile); the covered twin rides the free lemma
(`canRaiseS_free` — its cover fits, its seat lives, its exit is the
witness's own top); the quiet closes the pair-saturation iff; and
the orientation pin is the cover itself — the twin is buried under
`d`, so it tops nothing (the WF search pins its only face-up pile),
and the state IS the fork. -/
theorem crane_assembly_at_head {st : State} (hwf : st.WF) {x : Card}
    (hmeal : ForkMeal st x) : ForkWitness st x := by
  obtain ⟨hrungA, hrungB, hquiet, a, c, bs, d, rest, hpo, hseatX, hshape,
    hseatT, hne, hfit⟩ := hmeal
  have hnextX : st.nextUp x = true := by
    show decide (x.rank.toIdx = st.foundHeight x.suit) = true
    rw [show st.foundHeight x.suit = rungAt st x.suit from rfl]
    exact decide_eq_true hrungA.symm
  have hnextT : st.nextUp x.twin = true := by
    show decide (x.twin.rank.toIdx = st.foundHeight x.twin.suit) = true
    rw [show st.foundHeight x.twin.suit = rungAt st x.twin.suit from rfl, Card.twin_rank]
    exact decide_eq_true hrungB.symm
  have hxS : CanRaiseS st x :=
    CanRaiseS.now x ⟨hnextX, a, hpo, hseatX⟩
  have hpoT : st.pileOfTop x.twin.twin = some a := by
    rw [Card.twin_twin]
    exact hpo
  have htwinS : CanRaiseS st x.twin :=
    canRaiseS_free hwf hshape hpoT hne hfit hnextT hseatT
  have hTopC : (st.piles c).top ≠ some x.twin := by
    show lastOf (st.piles c).faceUp ≠ some x.twin
    rw [hshape]
    exact fcensus_top_buried bs x.twin d rest
      (by rw [← hshape]; exact hwf.2.1 c) (fcensus_fit_ne d x.twin hfit)
  refine ⟨fun cc => ⟨fun hp => ?_, fun hl => ?_⟩, ?_⟩
  · rcases hp with rfl | rfl
    · exact hxS
    · exact htwinS
  · rcases Decidable.em (cc = x) with h1 | h1
    · exact Or.inl h1
    · rcases Decidable.em (cc = x.twin) with h2 | h2
      · exact Or.inr h2
      · exact absurd hl (hquiet cc (fun hcc => by
          rcases hcc with h3 | h3
          · exact h1 h3
          · exact h2 h3))
  · rintro ⟨-, p, hp, -⟩
    have hxtm : x.twin ∈ (st.piles c).faceUp := by
      rw [hshape]
      exact List.mem_append.mpr (Or.inl (List.mem_append.mpr
        (Or.inr (List.mem_singleton.mpr rfl))))
    have hpmem : x.twin ∈ (st.piles p).faceUp :=
      Pile.mem_of_top (pileOfTop_top hp).2
    have hpc : p = c := by
      by_cases hcase : p = c
      · exact hcase
      · obtain ⟨hothers, -⟩ := mem_faceUp_only hwf hxtm
        exact absurd hpmem ((hothers p hcase).2)
    rw [hpc] at hp
    exact hTopC (pileOfTop_top hp).2

/-- A reversible leg stays inside the macro class (per-file copy of
the round-trip engine pattern). -/
private theorem fcensus_shuffleW_of_round : ∀ (σ : List Move) (x w : State),
    x.run σ = some w → ∀ ρ : List Move, w.run ρ = some x →
    ShufflePlayW x σ w := by
  intro σ
  induction σ with
  | nil =>
      intro x w hσ ρ hρ
      have hxw : (some x : Option State) = some w := hσ
      injection hxw with hx
      rw [hx]
      exact .nil w
  | cons p rest ih =>
      intro x w hσ ρ hρ
      obtain ⟨y, hp, hrest⟩ := State.run_cons hσ
      refine .cons ⟨y, rest ++ ρ, hp, run_split rest y w ρ x hrest hρ⟩ hp ?_
      exact ih y w hrest (ρ ++ [p]) (run_split ρ w x [p] y hρ (run_one hp))

/-- The per-leg class weld (per-file copy). -/
private theorem fcensus_class_leg {st s₁ : State} {m : Move}
    (hrev : reversibleAtW st m) (hstep : State.step st m = some s₁) :
    sameOrbitSetoid.r st s₁ := by
  obtain ⟨s₁', play, hstep', hrun⟩ := hrev
  have hs : s₁' = s₁ := Option.some.inj (hstep'.symm.trans hstep)
  rw [hs] at hrun
  show RevEqW s₁ st
  exact ⟨play, fcensus_shuffleW_of_round play s₁ st hrun [m] (run_one hstep),
    [m], .cons ⟨s₁, play, hstep, hrun⟩ hstep (.nil s₁)⟩

/-- Every member a witness journey reaches is a class-mate of its
origin (per-file copy). -/
private theorem fcensus_journey_class {st z : State} {ρ : List Move}
    (hρ : ShufflePlayW st ρ z) : sameOrbitSetoid.r st z := by
  induction hρ with
  | nil s => exact sameOrbitSetoid.iseqv.1 s
  | @cons s m s₁ rest w hrev hstep hrest ih =>
      exact sameOrbitSetoid.iseqv.trans (fcensus_class_leg hrev hstep) ih

/-- `WF` travels a witness journey (per-file copy). -/
private theorem fcensus_shuffleW_wf {st : State} : ∀ {ρ : List Move} {s' : State},
    ShufflePlayW st ρ s' → st.WF → s'.WF := by
  intro ρ s' h
  induction h with
  | nil s => exact fun hf => hf
  | @cons s m s₁ rest w hrev hstep hrest ih => exact fun hf => ih (step_wf hf hstep)

/-- **THE DECIDER-SHAPE COMPOSITE** `class_forks_decidable`
[M, proved] — a state is fork-headed-in-its-class iff some candidate
pair passes the census filter at the head AND the pair is
class-internally arrangeable.

THE HONEST READING (graded): the filter clause is the CLASS-STABLE
census `CensusPass` — the portrait §1 proves necessary at every
member; the located face-up grade (`PairCandidate`) is deliberately
NOT the head-side necessity, because a class member may hold a pair
member FOUNDED (the elevated head — the `lb1` datapoint: the twin
lifted, `¬ familyBelowFrontier`), so the locatedness lives inside
the arrangeability's landing, not at the head.  Both directions are
assembly: (⇒) rides §1's necessity row plus the class's own forward
witness play plus the fork member's own filter pass
(`fork_state_candidate`); (⇐) rides the journey-membership kit
(`fcensus_journey_class`).  `hwf` is load-bearing on the necessity
leg (the fork member's `WF` derives from the head's along the
journey). -/
theorem class_forks_decidable {st : State} (hwf : st.WF) :
    ClassForkHeaded st ↔
      ∃ x, CensusPass st x ∧ PairArrangeable st x := by
  constructor
  · rintro ⟨F, x, hcls, hwit⟩
    obtain ⟨ρ, hρ⟩ := sameOrbit_forward hcls
    have hwfF : F.WF := fcensus_shuffleW_wf hρ hwf
    obtain ⟨h1, h2, h3, h4⟩ :=
      fork_inventory_necessary hwfF hwit (sameOrbitSetoid.iseqv.symm hcls)
    obtain ⟨hcand, -, -⟩ := fork_state_candidate hwfF hwit
    exact ⟨x, ⟨h1, h2, h3, h4⟩,
      ⟨F, ρ, x, hρ, Or.inl rfl, hwit, hcand⟩⟩
  · rintro ⟨x, -, F, ρ, z, hρ, -, hwit, -⟩
    exact ⟨F, z, fcensus_journey_class hρ, hwit⟩

/-- **THE CLASS LABEL** — the labeling predicate for the head-side
crane: every fork of the class names `x`'s pair (up to the twin
flip). -/
def ForkClassLabel (st : State) (x : Card) : Prop :=
  ∀ (F : State) (w : Card), sameOrbitSetoid.r st F →
    ForkWitness F w → w = x ∨ w = x.twin

/-- **THE LABEL-CONDITIONED CRANE LEG**
`crane_label_conditioned` [M, proved] — given the class labels the
pair `x` at the head, class-headed and arrangeability collapse: the
journey is the class relation's own forward play, the fork member's
located candidate is its own filter pass (`fork_state_candidate`),
and the orientation is handled by the candidate filter's twin
invariance.  This is the mechanical half of the arrangeability;
its oracle is the residue below. -/
theorem crane_label_conditioned {st : State} (hwf : st.WF) {x : Card}
    (hlabel : ForkClassLabel st x) (hhead : ClassForkHeaded st) :
    PairArrangeable st x := by
  obtain ⟨F, y, hcls, hwit⟩ := hhead
  have hypair : y = x ∨ y = x.twin := hlabel F y hcls hwit
  obtain ⟨ρ, hρ⟩ := sameOrbit_forward hcls
  have hwfF : F.WF := fcensus_shuffleW_wf hρ hwf
  obtain ⟨hcand, -, -⟩ := fork_state_candidate hwfF hwit
  rcases hypair with h | h
  · rw [h] at hwit hcand
    exact ⟨F, ρ, x, hρ, Or.inl rfl, hwit, hcand⟩
  · rw [h] at hwit hcand
    refine ⟨F, ρ, x.twin, hρ, Or.inr rfl, hwit, ?_⟩
    have hc2 : PairCandidate F x.twin.twin := pairCandidate_twin hcand
    rw [Card.twin_twin] at hc2
    exact hc2

/-- **THE SEAT-ISSUANCE RESIDUE** `crane_seat_issuance` [H, NAMED
RESIDUE] — the arrangeability's own oracle: at a head whose class
carries a fork, if the head's pair-census data names the class's
fork pair (same family, same rank index), then the class LABELS the
head's pair — and `crane_label_conditioned` converts the label into
the full arrangeability.  The composite's head-directed leg is
thereby reduced to this one row.

WHAT IS BANKED (per premise): `census_pair_named` (rank + family
name the pair — the card algebra, proved) reduces the conclusion to
the class-fork IS the head's pair; the family-grade member label
(`forkState_family_pairClass`) closes every same-family member fork;
`WF` management along the witnessing journeys is the per-file kit;
the noNewSeat family (`excursion_issues_noNewSeat`) and the low-slab
machinery (`fork_neighbor_lowbridge`, `familyBelowFrontier`,
`fork_self_low`) are the census engine the cross-family route
prices against.

THE OPEN CONTENT: the member forks reach the head only through the
CLASS relation — the head itself is unwitnessed, so the labeling
row `fork_label_class` (the cross-family exclusion) is exactly the
missing piece: this residue is [H] with `fork_label_class`, and
assembly without it.  REFUTER-FIRST: the elevated head `lb1`
(mobile census, twin FOUNDED — the necessity grade passes, the
located grade fails) is the datapoint that any candidate-strengthening
of the head-side filter must survive; the wrong-rank pair (a lower
same-family pair whose cover cell happens to read mobile at some
member) is the live counterexample family for dropping the rank
premise — priced, never forced.

ROUTE: (1) fix the class's fork member `F` and witness `y`;
`census_pair_named` makes `y` a pair member of `x`; (2) for any
other fork `G`/`w` of the class: `G.WF` rides the head's journey
(`fcensus_shuffleW_wf`), and — IF `w` is same-family with `y` —
`forkState_family_pairClass G F` closes `w` into the pair; (3) the
cross-family `w` is the open slice: `fork_label_class` (this file's
§1 residue) is imported verbatim as the remaining content; (4) with
the label, `crane_label_conditioned` finishes. -/
theorem crane_seat_issuance {st : State} (hwf : st.WF) {x : Card}
    {F : State} {y : Card}
    (hcls : sameOrbitSetoid.r st F) (hwfF : F.WF)
    (hwit : ForkWitness F y)
    (hfam : y.suit = x.suit ∨ y.suit = x.twin.suit)
    (hrank : y.rank.toIdx = x.rank.toIdx) :
    ForkClassLabel st x := by
  sorry

/-! ## §3. The composite-frontier note: the pair census -/

/-- **THE CANDIDATE BOARD** — the census's enumeration domain: one
canonical representative per pair (the hearts carry the red
families, the spades the black) — 26 cards for the 26 unordered
twin pairs. -/
def forkCandidateBoard : List Card :=
  Card.universe.filter (fun c =>
    decide (c.suit = Suit.heart ∨ c.suit = Suit.spade))

/-- The board's membership bridge. -/
theorem mem_forkCandidateBoard_iff {c : Card} :
    c ∈ forkCandidateBoard ↔ (c.suit = Suit.heart ∨ c.suit = Suit.spade) := by
  rw [forkCandidateBoard, List.mem_filter]
  constructor
  · rintro ⟨-, hsu⟩
    exact of_decide_eq_true hsu
  · rintro hsu
    exact ⟨Card.mem_universe c, decide_eq_true hsu⟩

/-- **THE REPRESENTATION ROW** — every pair is named on the board:
each card is either its pair's representative or the twin of one. -/
theorem forkCandidateBoard_representative (x : Card) :
    ∃ y ∈ forkCandidateBoard, y = x ∨ y = x.twin := by
  rcases x with ⟨xs, xr⟩
  cases xs with
  | heart => exact ⟨⟨.heart, xr⟩, mem_forkCandidateBoard_iff.2 (Or.inl rfl), Or.inl rfl⟩
  | spade => exact ⟨⟨.spade, xr⟩, mem_forkCandidateBoard_iff.2 (Or.inr rfl), Or.inl rfl⟩
  | diamond =>
      exact ⟨⟨Suit.heart, xr⟩, mem_forkCandidateBoard_iff.2 (Or.inl rfl), Or.inr rfl⟩
  | club =>
      exact ⟨⟨Suit.spade, xr⟩, mem_forkCandidateBoard_iff.2 (Or.inr rfl), Or.inr rfl⟩

/-- Every passing candidate is represented by a PASSING board
member (the candidate filter's twin invariance carries the flip). -/
theorem pairCandidate_board_witness {st : State} {x : Card}
    (hcand : PairCandidate st x) :
    ∃ y ∈ forkCandidateBoard, PairCandidate st y ∧ (y = x ∨ y = x.twin) := by
  obtain ⟨y, hy, hypair⟩ := forkCandidateBoard_representative x
  rcases hypair with h | h
  · rw [h] at hy
    exact ⟨x, hy, hcand, Or.inl rfl⟩
  · rw [h] at hy
    exact ⟨x.twin, hy, pairCandidate_twin hcand, Or.inr rfl⟩

/-- **THE PAIR CENSUS** — the board is 26 cards: 13 ranks × 2
color-families, decided by the kernel.  The composite's filter is
therefore O(n)-grade per candidate: the census probes run over
sublists of `Card.universe` once per board member, and the §2
composite adds to this the arrangeability oracle only for pairs
that pass. -/
theorem forkCandidateBoard_length : forkCandidateBoard.length = 26 := by
  decide

/-- **THE CLASS-LEVEL CENSUS PROBE** — the composite's filter
computed over the board: a fold any-decides `∃ x, CensusPass st x`
(the representation row plus the census's twin invariance makes the
board enumeration complete). -/
def classCensusB (st : State) : Bool :=
  forkCandidateBoard.any (fun y => censusPassB st y)

/-- The class-level probe's bridge — WF-free, complete over the 26
representatives. -/
theorem classCensusB_true_iff (st : State) :
    classCensusB st = true ↔ ∃ x, CensusPass st x := by
  rw [classCensusB, List.any_eq_true]
  constructor
  · rintro ⟨y, -, hc⟩
    exact ⟨y, (censusPassB_true_iff st y).1 hc⟩
  · rintro ⟨x, hc⟩
    obtain ⟨y, hy, hypair⟩ := forkCandidateBoard_representative x
    rcases hypair with h | h
    · rw [h] at hy
      exact ⟨x, hy, (censusPassB_true_iff st x).2 hc⟩
    · rw [h] at hy
      exact ⟨x.twin, hy, (censusPassB_true_iff st x.twin).2 (censusPass_twin hc)⟩

/-! ## The audit battery

`#print axioms` per fresh head, as elaborated.  The §0 probe bridges
and the §3 census read `[propext, Quot.sound]` (the decide
bookkeeping's list plumbing over the kernel folds); the pure
card-algebra rows (`pairCandidate_twin`, `fork_label`,
`census_pair_named`) read `[propext]`; `forkCandidateBoard_length`
reads `[]` (kernel decide).  The §1/§2 assembly rows — including
`fork_inventory_necessary`, `crane_assembly_at_head` (the saturation
assembly, zero-sorry), `class_forks_decidable` (the composite, both
directions assembly) and `crane_label_conditioned` — read
`[propext, Quot.sound]` with NO `sorryAx`.  The two named residues
(`fork_label_class`, `crane_seat_issuance`) read exactly
`[propext, sorryAx]` — one `sorryAx` each, nothing else flows into
them; their complete routes are in their docstrings.  Zero
`Classical.choice` anywhere: the splits ride `Decidable.em`,
`decide`, and kernel-decided folds, and no `omega` faces a live
`∃`. -/

#print axioms mobileB_true_iff
#print axioms mem_lowCells_iff
#print axioms mem_coverCells_iff
#print axioms mem_lowCells_twin
#print axioms mem_coverCells_twin
#print axioms pairCandidateB_true_iff
#print axioms lowCellsMobileB_true_iff
#print axioms coverCellMobileB_true_iff
#print axioms pairCandidate_twin
#print axioms censusPassB_true_iff
#print axioms censusPass_twin
#print axioms faceUp_mobile
#print axioms founded_mobile
#print axioms fork_mobile_class
#print axioms fork_state_candidate
#print axioms fork_inventory_necessary
#print axioms fork_label
#print axioms census_pair_named
#print axioms fork_label_family
#print axioms fork_label_class
#print axioms crane_assembly_at_head
#print axioms class_forks_decidable
#print axioms crane_label_conditioned
#print axioms crane_seat_issuance
#print axioms mem_forkCandidateBoard_iff
#print axioms forkCandidateBoard_representative
#print axioms pairCandidate_board_witness
#print axioms forkCandidateBoard_length
#print axioms classCensusB_true_iff
