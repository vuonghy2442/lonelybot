import Orig2.Vocab

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

/-- **CLAIM `chart_round_trip`** — the chart is faithful: states
are their readouts (the named full agreement). -/
theorem chart_round_trip (st w : State) (h : chartAgree st w) :
    st = w := by
  sorry

/-- **CLAIM `chart_tabToTab` (RE-GATED)** — the UPDATE row: one pair
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
gates at their own discharge. -/
theorem chart_tabToTab {st s' : State} {c : Card} {b : Base}
    (hwf : st.WF)
    (hstep : State.step st (Move.tabToTab c b) = some s')
    (hrev : reversibleAtW st (Move.tabToTab c b)) :
    (∀ x, seatOf s' x = if x = c then some b else seatOf st x) ∧
    boardFixed st s' ∧ foundsFixed st s' ∧
    drawPool st = drawPool s' ∧ cutOf st = cutOf s' := by
  sorry

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

/-- **CLAIM `chart_draw`** — the CUT row: no pair changes, no
foundation changes, the pool is conserved; only the split moves
(the exact cut curve — the pass-base and recycle cases — priced
from the seam's draw unfold and the orbit card's phase kit). -/
theorem chart_draw {st s' : State}
    (hstep : State.step st Move.draw = some s') :
    (∀ c, seatOf s' c = seatOf st c) ∧ foundsFixed st s' ∧
    boardFixed st s' ∧ drawPool st = drawPool s' := by
  sorry

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

/-! ## The audit battery

All battery lines live at the proving cards:
`reversibleOf_iff_reversibleAtW` at the classification card
(`Orig2/Classification.lean` §7), `sameOrbit_factor` at the
orbit-factor card (`Orig2/OrbitFactor.lean` §4).  The banked
walk-steps bridge rows were pulled with the cargo pause (owner,
2026-10-17, "for now" — the bytes await at
`Temp/cargo_bridge_aborted.lean`); no priced stub remains. -/
