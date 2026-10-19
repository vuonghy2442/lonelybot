import Orig2.Vocab

set_option warn.sorry false

/-!
# Orig2.Claims — THE CLAIMS LAYER

The statements ledger: each claim is a frozen statement with its
`sorry` as honest debt, a PRICE line in its docstring (the content
that discharges it), and the promotion rule — when the proof
lands, the claim moves to the theorems tier, the stub deleted,
never duplicated.  The debt only shrinks.

THE WITNESS-ONLY REGIME (owner, 2026-10-17): the semantic pair
`irreversibleAt`/`reversibleAt` is retired from the new interface;
the program's ONE reversibility notion is the carrier
`reversibleAtW`, decided at WF by the oracle `reversibleOf`.  The
old classical fence (never state the unconditional
`reversibleAtW ↔ reversibleAt`) is MOOT — its other side no longer
exists in the vocabulary.  Commitment is what shape-false MEANS at
WF; the wild-state divergence corners stay archived as boundary
data in the frozen tier.

## §1. The claim

PRICE: the classification program, both halves at witness grade —
(→) shape-true HANDS the explicit undo play, constructor by
constructor (the draw's re-deal back; the raise's giveback over
the chop; the pull's re-raise onto the accepting base; the slide's
whole-segment relocation; the bare-king vacates); (←) shape-false
DENIES the witness (the replacement arguments restated at witness
grade: the waste rows' cycle-count drop, the hidden flip's
reveal-arms-never-re-arm, the bare non-king lifts' no-redo seat —
each refutes a returning play directly, intuitionistically, no
classical step anywhere).  Frozen-tier templates:
`Orig/Classify.lean`'s `drawClass`/`tabToFoundClass`/
`foundToTabClass`/`tabToTabClass` and the waste rows
(commit-polarity there; flip per case).  The decidability rider
(`Decidable (reversibleAtW st m)` at WF, through the bridge) is a
corollary of this claim, not a separate one.

PROMOTED (2026-10-17): the claim is DISCHARGED at
`Orig2/Classification.lean` §7 — the classification card proves
`reversibleOf_iff_reversibleAtW` over its five landed letters
(draw / waste pair / tabToFound / foundToTab / tabToTab, each
cell handing or denying the carrier per constructor), and the
card's battery carries the head ([propext, Quot.sound]).  The
stub is deleted per the promotion rule (never duplicated); the
Claims battery line for this claim moved to the card. -/

/-! ## §1B. The orbit-factor claim (owner-approved clean cut)

PRICE: the machinery card `Orig2/OrbitFactor.lean`, four pieces —
(1) THE GENERAL disjoint-field commutation lemma: a fired draw's
field-trace (stock/waste/drawStep) is disjoint from every board
leg's, so they commute at any fired adjacency — ONE general row at
the field-equation grade, with the per-move-kind instantiations at
a few lines each (the old card proved the squares thrice, ~50
lines per table move — templates `Orig/OrbitFactor.lean:73,132,179`);
(2) THE DRAWS-LAST BUBBLING: every witness journey permutes to
draws-last (ordinary induction once the square is general;
template `shuffle_drawsLast`, `Orig/OrbitFactorC.lean:371`);
(3) THE DRAW-BLOCK TRANSPLANT: re-rooting a draw block at the
rotated position — the one deep piece, rides the Phase loop
algebra (template `draw_play_transplant`,
`Orig/OrbitFactor.lean:560`);
(4) THE ASSEMBLY: → extracts the two-witness journeys from the
rev-closure, bubbles both, transplants to the common board z;
← composes the four witnesses (template `sameOrbit_factor_full`,
`Orig/OrbitFactorC.lean:442-487`).  The frozen tier's two proved
rows are the correctness oracle.

PROMOTED (2026-10-17): the claim is DISCHARGED at
`Orig2/OrbitFactor.lean` §4 — the machinery card proves
`sameOrbit_factor` real over its four landed pieces (the ONE
general disjoint-field commutation square at the field-equation
grade; the draws-last bubbling with the restated pull core — the
crossed board legs re-witness by an explicit composite undo play,
the classification bridge replaced by witness transport; the
draw-block transplant over the card's private Phase kit; the
four-witness composition), and the card's battery carries the
head ([propext, Quot.sound], zero sorryAx, zero
`Classical.choice`).  The stub is deleted per the promotion rule
(never duplicated); the Claims battery line for this claim moved
to the card. -/

/-! ## §1C. The bare-cargo tier — support retired to the generic kit

Since the steps-first migration (owner, 2026-10-17), the dumb
cargo play is a GENERIC instance — `∃ ρ, Walk (tabToTab-shape
predicate) A ρ B` —
and no separate name or per-instance support rows live here: the
verbatim lineage (`Orig/ForklessCeiling.lean:100,108,118`) is
subsumed by the generic `Walk_run`/`Walk_append` kit.

PULLED BY OWNER (2026-10-17, "for now"): the exchange-bridge claim
`dumbSpan_iff_exchange` (the raw both-ways dumb spans ARE the
official exchange — the chain composite per leg: suffix ++
reverse span ++ accumulated prefix) WAS DISCHARGED and promoted to
a cargo-bridge card, then pulled with its card at the owner's call;
the proof bytes await at `Temp/cargo_bridge_aborted.lean` (unbuilt)
and the enforcement restate of `BareCargoEquiv` stands in the
registry unchanged. -/

/-! ## §1E. The chart claim book (owner-ratified, the minimal set
representation — priced per the move algebra; the two promoted
cards' private keep-kits are the primary ports)

PRICE across the book: the seam's own step unfolds
(`State.lean`'s `setPile`/`putRun`/`afterRunRemoved`/`pileOfTop`
/`pileHolding` rows) plus both promoted cards' private field-keep
kits (the classification and orbit cards each hold copies — this
book is the dedup strike that replaces them). -/

/-! **CLAIM `chart_round_trip`** — the chart is faithful: states are
their readouts (the named full agreement).

RE-GATING PROVENANCE (2026-10-18): the ungated form (`chartAgree`
alone) is FALSE — refuted by the chart card's kernel witness
`chart_round_trip_ungated_false` (`Orig2/Chart.lean` §11, battery
[propext]): the seat search stops at a card's FIRST face-up pile,
so a masked extra copy of a card in any LATER pile changes no
readout whatsoever — two wild boards differing only in the masked
tail of a late pile are chart-twins but not equal.  The WF gates
(occurrence uniqueness on BOTH sides) kill exactly this; the claim
is re-stated at the WF-grade, `chart_round_trip (st w) (hwfst :
st.WF) (hwfw : w.WF) (h : chartAgree st w) : st = w`, never in the
ungated shape again.

THE GRADE LADDER (2026-10-18): the card separates the load-bearing
content — `chart_round_trip_core` is the bare occurrence-grade row
(`∀ c, cardCount c = 1` per side; no run legality, foundation
shape, or draw quantum is consumed anywhere), the WF claim is that
core with the count clause extracted, and
`chart_round_trip_counts` is the CONSERVATION GRADE: st.WF plus
count AGREEMENT (`∀ c, st.cardCount c = w.cardCount c`) pins the
mate with NO mate-side gate.

DEBT-LINKAGE CONSEQUENCE (recorded 2026-10-18, restated on the
grade ladder): the floater books' hoists read `∀ A B, chartAgree
A B → A = B` UNGATED — they cannot drop verbatim with the
discharge (the re-gated row needs the mate's WF, which a wild
SeatEdit-spec-mate need not have).  Their honest consumption is
one of two amendments per site: the conservation grade's count-
neutrality clause — a SeatEdit gains `∀ c, w.cardCount c =
st.cardCount c` (an edit creates no cards; the natural companion
of the already-listed conserved readouts) and rides
`chart_round_trip_counts` — or a direct mate-side WF premise.  The
floater books' own re-gating work, either way.

PROMOTED (2026-10-18): the re-gated claim is DISCHARGED at
`Orig2/Chart.lean` §10 — the chart card proves it over the
below-profile transfer (the one induction: a card's position datum
transfers to any chart-mate at the same anchor, parent step by
parent step, every step an occurrence kill; the top card then pins
the whole face-up run), plus the pool/cut recovery and the field
congruences.  The card's battery carries the head ([propext,
Quot.sound], zero sorryAx, zero `Classical.choice`).  The stub is
deleted per the promotion rule (never duplicated); the Claims
battery line for this claim moved to the card. -/

/-! **CLAIM `chart_tabToTab` (RE-GATED)** — the UPDATE row: one pair
change, nothing else in the world moves.  RE-GATING PROVENANCE
(2026-10-17): the ungated form (`hstep` alone) was REFUTED by the
floater-ladder probe's kernel witness (`Temp/float_check.lean`'s
private `chart_tabToTab_ungated_false`, battery [propext]): (i)
at wild states a duplicated mover breaks the successor search;
(ii) a non-reversible fired slide reveals a hidden card and
materializes its seat (`none → some (.inl a)`), breaking the point
edit and `boardFixed` alike.  The WF gate (occurrence uniqueness)
kills (i); the reversibility gate (whose bare cell carries
`hidden = []`) kills (ii).  The `reversibleAtW` form rides the
certified per-letter row; the sibling chart rows carry analogous
gates at their own discharge.

PROMOTED (2026-10-17): the claim is DISCHARGED at
`Orig2/FloatFiber.lean` §H2 — the fiber card's
`floater_seat_change_spec` proves the one-point chart edit at the
mover (the point-edit row plus the conservation row: the edit
bundle IS this claim's statement — the seat point edit, the fixed
hidden decks and deal quantum, the foundation rows, the pool and
the cut), together with the class-STEP fiber (the twin-family
reseating or the bare-king vacate) — strictly more than the stub.
The card's battery carries the head ([propext, Quot.sound], zero
sorryAx, zero `Classical.choice`).  The stub is deleted per the
promotion rule (never duplicated); the Claims battery line for
this claim moved to the card. -/

/-- **CLAIM `chart_tabToFound`** — the DELETE row: the pair vanishes,
the card lands on its foundation row, nothing else moves. -/
theorem chart_tabToFound {st s' : State} {c : Card}
    (hstep : State.step st (Move.tabToFound c) = some s') :
    seatOf s' c = none ∧ (∀ x ≠ c, seatOf s' x = seatOf st x) ∧
    c ∈ s'.found c.suit ∧
    (s'.found c.suit).length = (st.found c.suit).length + 1 ∧
    (∀ s ≠ c.suit, st.found s = s'.found s) ∧
    boardFixed st s' ∧ drawPool st = drawPool s' ∧
    cutOf st = cutOf s' := by
  sorry

/-- **CLAIM `chart_foundToTab`** — the ADD row: the pair appears at
the giveback base, the foundation row sheds its top, nothing else
moves. -/
theorem chart_foundToTab {st s' : State} {c : Card} {b : Base}
    (hstep : State.step st (Move.foundToTab c b) = some s') :
    seatOf s' c = some b ∧ (∀ x ≠ c, seatOf s' x = seatOf st x) ∧
    c ∉ s'.found c.suit ∧
    (st.found c.suit).length = (s'.found c.suit).length + 1 ∧
    (∀ s ≠ c.suit, st.found s = s'.found s) ∧
    boardFixed st s' ∧ drawPool st = drawPool s' ∧
    cutOf st = cutOf s' := by
  sorry

/-! **CLAIM `chart_draw` (PROMOTED 2026-10-18)** — the CUT row: no
pair changes, no foundation changes, the pool is conserved; only the
split moves.  DISCHARGED at `Orig2/Chart.lean` §6, exactly as stated
(ungated — the draw writes only the stock and the waste, so no gate
is load-bearing): the record congruence rides the draw footprint fold
(`Orig2/Kit.lean` §1d: `draw_footprint` and its projections), the
pool clause is one `dealUpTo`-split computation plus the recycle
cases (frozen template `Orig/Canonical.lean:2619 draw_pool_keep`,
restated constructively).  The card's battery carries the head
([propext, Quot.sound], zero sorryAx, zero `Classical.choice`).  The
stub is deleted per the promotion rule (never duplicated); the
Claims battery line for this claim moved to the card. -/

/-- **CLAIM `chart_wasteToFound`** — the pool-to-foundation row: no
pair changes, the pool head is consumed, the card lands on its
foundation row. -/
theorem chart_wasteToFound {st s' : State} {c : Card}
    (hstep : State.step st (Move.wasteToFound c) = some s') :
    (∀ x, seatOf s' x = seatOf st x) ∧
    (drawPool s').length = (drawPool st).length - 1 ∧
    c ∈ s'.found c.suit ∧
    (s'.found c.suit).length = (st.found c.suit).length + 1 ∧
    (∀ s ≠ c.suit, st.found s = s'.found s) ∧
    boardFixed st s' ∧ cutOf st = cutOf s' := by
  sorry

/-- **CLAIM `chart_wasteToTab`** — the pool-to-seat row: one pair
ADDED (the mover lands on its base), the pool head consumed. -/
theorem chart_wasteToTab {st s' : State} {c : Card} {b : Base}
    (hstep : State.step st (Move.wasteToTab c b) = some s') :
    seatOf s' c = some b ∧ (∀ x ≠ c, seatOf s' x = seatOf st x) ∧
    (drawPool s').length = (drawPool st).length - 1 ∧
    foundsFixed st s' ∧ boardFixed st s' ∧
    cutOf st = cutOf s' := by
  sorry

/-! ## §1F. THE FLOATER CLAIM BOOK (promoted at the fiber card and
the orbit card; the dry-run's four rows, the ladder restatements,
and the class-invariance keystone)

PROVENANCE (2026-10-17): dry-ran as `Temp/float_agent_check.lean`
(the agent dry-run over the owner's `Temp/float_check.lean` kit,
2,300+ lines of certification compiled with every head at
[propext, Quot.sound] — zero sorry, zero `Classical.choice`), and
installed at owner request ("migrate it … create a new file for the
new claim").  PRICE across the book (all landed): the twin-fiber
forcing (`canSitOn`'s twin-blindness plus the parent-tops-nothing
seat row), the certified one-point chart edit, the reversible
slide's readout conservation, the WF-gated R-oracle, and the priced
`chart_round_trip` hoist.

UPDATE (2026-10-18, the round-trip re-gate): the keystone priced in
the line above landed at `Orig2/Chart.lean` WF-GATED — the ungated
form is refuted there (`chart_round_trip_ungated_false`, battery
[propext]): a wild chart-mate can carry masked extra copies and
still satisfy every readout, so no ungated round trip exists.  The
hoists at the rows below therefore do NOT drop verbatim; each
hoist-site needs its mate pinned — by a mate-side WF premise, or by
the card's CONSERVATION GRADE `chart_round_trip_counts` (st.WF
plus count-neutrality `∀ c, w.cardCount c = st.cardCount c`, the
natural amendment of a SeatEdit-grade spec) — the floater books'
own re-gating work, recorded here so the debt linkage is not
misread as settled.

PROMOTED (2026-10-17), per entry:

* `floater_seat_change_spec` (this ledger's `chart_tabToTab`
  discharge, plus the class-STEP fiber: twin-family reseating or a
  bare-king vacate) at `Orig2/FloatFiber.lean` §H2;
* `floater_cargo_lift` (the reverse layer 1: a live fiber-valid
  cell plus a placement license FIRES as an actual reversible cargo
  leg realizing the chart spec) at FloatFiber §H2;
* `floater_classification` (the structural iff: the behavioral
  Floater equals the target-existence shape `FloaterSpec`) at
  FloatFiber §H3;
* `floater_seat_to_equiv'` (the reverse layer 2 MODULO this
  ledger's priced `chart_round_trip`, hoisted as a hypothesis —
  the DEBT LINKAGE: when that stub is discharged, the hoist drops)
  at FloatFiber §H4;
* the ladder restatements — `slide_reversible_iff_cell` (the
  per-slide oracle at the seat algebra), `floaterSpec_iff_cargoEdit`
  and `floater_iff_cargoEdit` (the registry-grade per-card flat
  iff: the Floater is exactly the licensed one-point class edit),
  and `bareCargo_iff_chartEdits` (the class iff: the bare-cargo
  class IS the iterated one-point floater-edit closure — its
  forward half consumes ONE cargo direction and needs no round
  trip, its backward half re-hoists `chart_round_trip` once and
  rides the reverse-layer rows per step) at FloatFiber §H5;
* `floater_leg_invariant` and `floater_orbit_invariant` (THE
  ORBIT-INVARIANCE CARD: along one reversible leg — hence along
  the whole bare-cargo orbit — floater-hood per card is FIXED; the
  floater SET is a `BareCargoEquiv`-class invariant, the
  conservation keystone that makes the flat class
  characterization derivable) at `Orig2/FloatOrbit.lean`;
* `floater_path_invariant` (the one-way companion: a single cargo
  DIRECTION already fixes floater-hood per card) and
  `bareCargo_to_chartDiff` (Stage 2 of the flat reformulation:
  every class-mate is reached with the per-card three-way net
  seat relation (the chain invariant), the conserved readouts
  (hidden decks and deal quantum, foundations, pool, cut), and
  DERIVED st-side licensing — a net-changed card was some
  prefix-endpoint's mover, the path invariance transports its
  floater-hood back, and the classification re-exports the
  spec LITERALLY at the origin: no round trip, one cargo
  direction) at `Orig2/FloatOrbit.lean` §J.  The Stage-3a
  single-edit compose-unit and the single-hop reconstruction rows
  were RETIRED (2026-10-18) as a dead-end chain carrying the
  refuted global round-trip hypothesis; the flat iff is closed
  unconditionally by the VK arm (`bareCargo_iff_vk`, §1F.1 below).

The two cards' batteries carry the heads ([propext, Quot.sound]
line-by-line, zero sorryAx, zero `Classical.choice`); the stubs are
deleted per the promotion rule (never duplicated) — this book had
no stubs to delete (the rows were certified before registration),
the `chart_tabToTab` promotion above being the one stub the
discharge retired. -/

/-! ### §1F.1  THE SEAT-CHART IFF (owner's target, priced): the
bare-cargo orbit characterized by pure seatOf data.  TARGET
STATEMENT: `BareCargoEquiv st w ↔ w.WF ∧ per-card three-way net
seat relation (carried | parent→parent's twin | bare king's
empty-seat change) ∧ readoutsAgree (hidden, deal quantum,
founds, pool, cut) ∧ st-side licensing of every net-changed card`.
STATUS: the → direction is PROMOTED (`bareCargo_to_chartDiff`
plus the freshly banked `floater_orbit_wf_prsv` — the WF fence
rides the whole orbit, one cargo direction suffices — both at
`Orig2/FloatOrbit.lean`, battery [propext, Quot.sound]).  The ←
direction (the mirror program) is PRICED: (i) license rows at
consistent neighbors — at any state w-shaped on the pending
cards, a pending card's mirror undo-leg is licensed directly by
the flat data itself (the vacated parent tops its pile by
occurrence uniqueness; a king's vacated pile is empty by the
readout agreement); (ii) the master induction over the
changed-card roster firing undo-leg/redo-leg pairs — the undo
chain builds the w→st path, the redo legs reassemble the
st→w path, no forward license-preservation machinery; (iii)
NECESSARY RHS UPGRADE (found 2026-10-17): the king arm must
carry its target pile's hidden-emptiness at st — `c: a → a′`
requires `(st.piles a′).hidden = []` — else the flat condition
admits a near-miss (a hidden card parked under the king's
w-slot: every naive clause holds, the landing is physically
impossible, no reversible journey realizes it); the →
direction derives the upgraded clause from the journey (the
mover's landing leg rides the bare cell with hidden = [], and
the readout chains carry it back to st).

PROMOTED (2026-10-17) THEN RETIRED (2026-10-18, the company
grade): the twin-hop seat-chart iff
(`bareCargo_iff_seatchart_company`), its activation
(`bareCargo_of_seatchart_company`), and the company master induction
(`orbit_company_mirror_induct`) were removed: the unconditional VK
arm below subsumes the company grade, and the company-only rows had
no Lean consumers.  The shared license rows
(`orbit_company_undo_license`, `orbit_company_redo_license`) remain
— the mixed induction consumes them.  ALSO PROMOTED (2026-10-17):
THE KING-ARM HIDDEN-[] DERIVATION — the → upgrade's derivation
from the journey: `orbit_king_hidden_vacate` at
`Orig2/FloatOrbit.lean` ([propext, Quot.sound]), riding the
last-mover locator (`orbit_last_mover_locator`: a seat-changed
card's LAST fired-and-reversible leg, whose successor keeps the
card's seat to the far end) plus the oracle's canPlace-target
emptiness plus the prefix readout chains.  With it, EVERY clause
of the flat RHS is now derivable in the → direction for all arms.
PRICED REMAINDER (the last piece): the KING grade of the ←
direction only — the token-sliding order content for king
chains landing on piles other kings vacate (the swap-cycle:
undo-ordering genuinely matters; the last-mover locator now
certifies the JOURNEY structure this analysis will read).

FINAL PROMOTION AND CLOSING DISCOVERY (2026-10-17): the MIXED
master induction (`orbit_mixed_mirror_induct`) is landed — the
changed queue processes each pending card by its own arm: company
twin hops through the twin license rows, king vacates through the
king license rows (`orbit_king_undo_license`,
`orbit_king_redo_license`: the strengthened target-clause carries
the target pile's st-emptiness; claimant anchors die by
bottom-uniqueness or their own clause), stale entries skipping as
ever — ACTIVATED at the filtered universe by
`bareCargo_of_seatchart` ([propext, Quot.sound], the card's
battery): with the flat data plus the strengthened king clauses
the class is genuinely realizable; EVERY clause of the ←
direction is now landed at FULL grade.  THE CLOSING DISCOVERY,
recorded as the final priced core: the two directions of the
NAIVE full iff do not meet — the → derivation of the
strengthened clause collects ONLY the hidden emptiness
(`orbit_king_hidden_vacate`), while the target pile's faceUp at
st can be occupied in MEDIATED king chains (a second king
vacates the target before the mover lands — the swap-cycle
again), and the ← mirror genuinely consumes the full isEmpty.
Hence the unrestricted `bareCargo_iff_seatchart` REQUIRES the
token-sliding order card — the mediated-journey structure made
chart-derivable — as its final ingredient; every other component
of the §1F.1 price is PROMOTED and battery-certified.

PROMOTED (2026-10-18, the unrestricted iff — the VK arm): the
mediate obstruction is DISSOLVED rather than excluded.  The king arm
of the class relation now reads "the changed king lands on a node of
the origin's FUEL SET" (`VKSet st a'` = vacant or bare-king-bottom),
not "the target pile is empty at st": the empty-target clause is
refuted outright by the two-king swap (a mediator vacates the target
before the mover lands), while the fuel-set clause is what every
reversible leg actually preserves — `bareCargo_orbit_vk` (pointwise
invariance of `{vacant} ⊎ {king-bottom}`) and
`bareCargo_orbit_vk_transfer` (inside the set only kings move).  Both
directions are certified ([propext, Quot.sound], the card's battery):
`bareCargo_to_chartDiff_vk` (the →, no mediator binder) and
`bareCargo_of_chartVK` (the ← : the king seats form an injective map
into `VKSet` — injective for free by `king_seat_injective`, and the
schedule exists by `king_assignment_reachable`, §M11b), assembled in
**`bareCargo_iff_vk`** — THE ONE ↔ THEOREM, with NO `hnomed`.
`bareCargo_iff_split` factors the same iff into the king half (fuel
targets) and the twin half.  The former unmediated rows
(`orbit_king_isEmpty_unmediated`, `bareCargo_iff_seatchart_unmediated`)
and the company-grade arm are RETIRED: the VK arm subsumes them, and
the token-sliding "order" is no longer a missing ingredient — its
content is the fuel-set invariant plus reachability.

PROMOTED (2026-10-18, the spare-empty invariant and the
KING-SHUFFLE card at `Orig2/FloatOrbit.lean` §§M9–M10, both
[propext, Quot.sound]): `bareCargo_orbit_spare_empty` (the vacancy
never disappears along the orbit — company legs touch no empty
pile, bare-king legs swap consumed target for vacated donor), and
**"with a vacant spot, shuffle the kings all you want"** — TWO
rows: `king_shuffle_vacancy` (the shuffle leg: a bottomed bare
king swaps into the current vacancy reversibly, THE VACANCY
TRAVELS to the king's old pile — the successor carries an empty
donor, the chain's fuel; the class-mates close via the chart
activation row, the lift's own SeatEdit being the carried-arm
chart, the readouts its fixed components, and the licensing the
hypotheses themselves — the spec's bare-cell shape with the
vacancy as the empty-pile existential), and `king_shuffle_closure`
over the `KingShuffle` reachability family (any sequence of
vacancy-swapping bare-king trades keeps the far end a bare-cargo
class-mate of the start; the fence and the priced round trip ride
the chain).  With the traveling-vacancy leg and the spare-slot
invariant both certified, the token-sliding card's remaining
content is exactly the MEDIATED order analysis. -/

/-! ## §1G. THE SEAT-MATE STACK CLAIM (2026-10-19; PROMOTED AS THE REPAIRED
DISJUNCTION — the requested shape is refuted, see `ClaimsScrutiny` §S5)

The requested statement: ANY possible play that moves a non-Floater
tableau card must contain a founding move of the card or of one of its
seat-mates (`SeatMate`: the twin-pair for an ordinary card, the king quad
for a king).  That shape is FALSE: the FOUNDATION TWIN PULL
(`z.twin` in the foundation, pulled onto the tableau, then `c` slides onto
it) changes `c`'s seat with no `tabToFound` at all.  The repaired statement
adds the target pull as a second arm:

  (∃ x, SeatMate c x ∧ Move.tabToFound x ∈ play) ∨
  (∃ z b, seatOf st c = some (Sum.inr z) ∧ Move.foundToTab z.twin b ∈ play)

It is proved in `Orig2/SeatMateStack.lean`; the master row is
`nonFloater_change_split`, with the arms
`nonFloater_change_found_needs_target_pull`,
`nonFloater_nonKing_change_seatmate_of_not_found`, and
`nonFloater_king_change_needs_king_stack`.  The old stub is deleted under
the no-stub rule; the card's theorem is the single home of the name. -/

/-! ## The audit battery

All battery lines live at the proving cards:
`reversibleOf_iff_reversibleAtW` at the classification card
(`Orig2/Classification.lean` §7), `sameOrbit_factor` at the
orbit-factor card (`Orig2/OrbitFactor.lean` §4), the fiber book's
heads at the fiber card (`Orig2/FloatFiber.lean`), the
orbit-invariance card's heads at `Orig2/FloatOrbit.lean`, and the
landed chart heads `chart_draw` and `chart_round_trip` (re-gated
at WF) at the chart card (`Orig2/Chart.lean`, 2026-10-18 — the
card's battery section re-prints every head, including the
ungated-round-trip refutation `chart_round_trip_ungated_false` at
[propext]).  The priced stubs left standing are the chart book's
per-letter readout rows (`chart_tabToFound`, `chart_foundToTab`,
`chart_wasteToFound`, `chart_wasteToTab`); the banked walk-steps
bridge rows stay pulled with the cargo pause (owner, 2026-10-17,
"for now" — the bytes await at
`Temp/cargo_bridge_aborted.lean`). -/
