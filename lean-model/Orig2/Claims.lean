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
corollary of this claim, not a separate one. -/

/-- **CLAIM `reversibleOf_iff_reversibleAtW`** — the oracle meets
the witness carrier exactly at WF worlds. -/
theorem reversibleOf_iff_reversibleAtW {st : State} (hwf : st.WF)
    (m : Move) :
    reversibleOf st m = true ↔ reversibleAtW st m := by
  sorry

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
rows are the correctness oracle. -/

/-- **CLAIM `sameOrbit_factor`** — the phase factorization: a
class membership is a draw-free board reshuffle to a phase-mate,
then a pure rotation round. -/
theorem sameOrbit_factor {u v : State} (hwf₁ : u.WF) (hwf₂ : v.WF) :
    sameOrbitSetoid.r u v ↔ ∃ z, NoDrawPlayW u z ∧ SWRotW z v := by
  sorry

/-! ## §1C. The bare-cargo tier — support retired to the generic kit

Since the steps-first migration (owner, 2026-10-17), the dumb
cargo play is a GENERIC instance — `∃ ρ, Walk CargoLetter A ρ B`,
realized on demand through the banked bridge `steps_to_walk` —
and no separate name or per-instance support rows live here: the
verbatim lineage (`Orig/ForklessCeiling.lean:100,108,118`) is
subsumed by the generic `Walk_run`/`Walk_append` kit and the
compat row `bareCargoEquiv_iff_play` (§1D, banked green). -/

/-!
CLAIM §1C-3 — the exchange bridge (the owner's formulation): the
DUMB both-ways exchange and the WITNESS-grade cargo closure agree
at WF.

PRICE: (→ the easy half) `CargoPath` legs are witnesses — each
`FlatStep.cargo` leg IS a cargo letter, so a letter-wise
induction plus the generic `Walk_append` build the two dumb
plays;
(← the deep half) at WF every SURVIVING cargo leg carries its
one-move return — the dumb play, letter by letter, lifts to the
reversible closure.  The frozen content: the exclusion and seat
mirror rows ride the tabToTabR shape (Claim §1A's slide half);
the frozen insight lives in `Orig/ForklessCeiling.lean` §0a-§0d
(the mirrors: every surviving leg's one-move return; the
zone-fix rows give the field discipline).
-/

/-- **CLAIM `bareCargo_iff_cargoPath`** — the dumb exchange meets
the witness cargo closure exactly at WF worlds. -/
theorem bareCargo_iff_cargoPath {A B : State} (hwfA : A.WF)
    (hwfB : B.WF) :
    BareCargoEquiv A B ↔ CargoPath A B ∧ CargoPath B A := by
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

/-- The dumb cargo play form, on demand through the generic
bridges (the steps-first restate's compatibility row, banked
green): the both-ways spans carry the both-ways dumb plays and
conversely. -/
theorem bareCargoEquiv_iff_play (A B : State) :
    BareCargoEquiv A B ↔
    ∃ τ, Walk CargoLetter A τ B ∧ ∃ ρ, Walk CargoLetter B ρ A := by
  constructor
  · rintro ⟨hAB, hBA⟩
    obtain ⟨τ, hτ⟩ := steps_to_walk _ hAB
    obtain ⟨ρ, hρ⟩ := steps_to_walk _ hBA
    exact ⟨τ, hτ, ρ, hρ⟩
  · rintro ⟨τ, hτ, ρ, hρ⟩
    exact ⟨walk_to_steps _ hτ, walk_to_steps _ hρ⟩

/-! ## The audit battery

The single claim stub carries `sorryAx` by design — the layer's
whole debt ledger on one row, priced above. -/

#print axioms reversibleOf_iff_reversibleAtW
#print axioms sameOrbit_factor
#print axioms walk_to_steps
#print axioms steps_to_walk
#print axioms bareCargoEquiv_iff_play
#print axioms bareCargo_iff_cargoPath
