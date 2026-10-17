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
cargo play is a GENERIC instance — `∃ ρ, Walk CargoLetter A ρ B`,
realized on demand through the banked bridge `steps_to_walk` —
and no separate name or per-instance support rows live here: the
verbatim lineage (`Orig/ForklessCeiling.lean:100,108,118`) is
subsumed by the generic `Walk_run`/`Walk_append` kit, and the
official-exchange equivalence is the CLAIM §1C-3
(`dumbSpan_iff_exchange`) below. -/

/-!
CLAIM §1C-3 — the exchange bridge, restated at the enforcement
(owner, 2026-10-17: the exchange ENFORCES reversibility in its
own definition — "so that it stays in class" — and this row
carries the enforcement's real content): the RAW both-ways dumb
spans and the official exchange agree — each leg of a both-ways
dumb span IS reversible, by the chain composite.

PRICE: (← the easy letter-unpack) a `CargoLeg` is the shadow
letter with its witness — plain cons-induction builds each
direction's dumb span; no WF needed.
(→ the chain half) for any leg of the A→B dumb span, origin w,
successor u, the `reversibleAtW` witness play is the composite
suffix (u →* B) ++ reverse span (B →* A) ++ accumulated prefix
(A →* w) — a cons-induction with a prefix accumulator over the
BANKED generic kit (`steps_to_walk`, `Walk_append`, `Walk_run`);
the frozen mirrors (one-move returns,
`Orig/ForklessCeiling.lean` §0a-§0d) are finer content this row
does not need; no WF gate.
-/

/-- **CLAIM `dumbSpan_iff_exchange`** — the raw both-ways dumb
spans are the official exchange, exactly. -/
theorem dumbSpan_iff_exchange (A B : State) :
    (Steps (StepOf CargoLetter) A B ∧
      Steps (StepOf CargoLetter) B A) ↔ BareCargoEquiv A B := by
  sorry

/-! ## §1D. The walk-steps bridge (banked green)

The Rosetta rows between the two journey generics, proved once
generically: a `Walk P` witness forgets its list into the span
at the shadow letter `StepOf P`; a span at the shadow letter
realizes back to SOME `Walk P` play (per-leg `obtain` — no
choice, fully intuitionistic). -/

/-- The forgetful map: a `Walk P` witness is a `Steps (StepOf P)`
span (the move list dropped). -/
theorem walk_to_steps (P : State → Move → Prop) {st : State} :
    ∀ {ρ : List Move} {W : State},
    Walk P st ρ W → Steps (StepOf P) st W := by
  intro ρ W h
  induction h with
  | nil s => exact Steps.refl s
  | cons hlet hstep _ ih => exact Steps.cons ⟨_, hlet, hstep⟩ ih

/-- The realization map: a span at the shadow letter carries some
`Walk P` play reaching it. -/
theorem steps_to_walk (P : State → Move → Prop) {st : State} :
    ∀ {W : State}, Steps (StepOf P) st W →
    ∃ ρ, Walk P st ρ W := by
  intro W h
  induction h with
  | refl s => exact ⟨[], Walk.nil s⟩
  | @cons w z u hQ _t ih =>
      obtain ⟨ρ, hρ⟩ := ih
      obtain ⟨m, hP, hstep⟩ := hQ
      exact ⟨m :: ρ, Walk.cons hP hstep hρ⟩

/-! ## The audit battery

`reversibleOf_iff_reversibleAtW`'s battery line moved to the
classification card at promotion.  The remaining claim stubs
carry `sorryAx` by design — the layer's whole debt ledger on one
row each, priced above. -/

#print axioms walk_to_steps
#print axioms steps_to_walk
#print axioms dumbSpan_iff_exchange
