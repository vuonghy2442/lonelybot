import Orig2.Model

/-!
# Orig2.Vocab — THE VOCABULARY REGISTRY (definitions only)

The rebuild library's intent gate, made physical: EVERY program-wide
definition of `Orig2` lives in this file and nowhere else, and every
definition sits under its owner-adjudicated intent tag.  Reviewing
this file IS reviewing the program's language.

THE FILE RULES

* definitions only — the ONE structural exception is the setoid
  support kit of §3 (the three carrier rows the Setoid instance
  cannot exist without), each flagged and audited;
* a port from the frozen `Orig` tier is a VERBATIM shape copy with
  the source cited, or an honest re-statement — never a shape-guess;
* the REVIEW ANNEX holds the old tier's remaining main vocabulary
  with one verdict per entry: KEEP-SHAPE (ported), RESTATE (new
  line), or RETIRE (fenced here; the frozen tier keeps its boundary
  data).  No pending entry is ported.

OWNER REVIEW LEDGER (2026-10-17): KILLED — `weakForkState`,
`FaceShape`, `conjugateForkState`, `conjugateCompositeRev` (the weak
grade and the conjugate-composite family exit the new vocabulary;
their frozen-tier consumers — the G2 falsifier records, the §9
composites, the S-siblings — stay on record where they are).  KEPT —
`CanRaise`, `CanRaiseS`, `ShufflePlayW`, `RevEqW`, `sameOrbitSetoid`,
`classOf`, `rungAt`, `twinSuit`.  PENDING — everything in the annex
below.

## §1. PLAY-TAXONOMY COUNTERS (live, ported)

Ported verbatim from `Orig/BracketDecomp.lean:254-275` — pure play
classification, macro-free, substrate of the rung ledger.
-/

/-- **raisesOf play σ** — the `tabToFound` raise letters of `play`
whose card belongs to the suit `σ`. -/
def raisesOf : List Move → Suit → Nat
  | [], _ => 0
  | Move.tabToFound c :: t, σ => (if c.suit = σ then 1 else 0) + raisesOf t σ
  | _ :: t, σ => raisesOf t σ

/-- **pullsOf play σ** — the `foundToTab` pull letters of `play`
whose card belongs to the suit `σ`. -/
def pullsOf : List Move → Suit → Nat
  | [], _ => 0
  | Move.foundToTab c _ :: t, σ => (if c.suit = σ then 1 else 0) + pullsOf t σ
  | _ :: t, σ => pullsOf t σ

/-- **raiseTotal play** — all raise letters, over all suits. -/
def raiseTotal : List Move → Nat
  | [] => 0
  | Move.tabToFound _ :: t => raiseTotal t + 1
  | _ :: t => raiseTotal t

/-- **pullTotal play** — all pull letters, over all suits. -/
def pullTotal : List Move → Nat
  | [] => 0
  | Move.foundToTab _ _ :: t => pullTotal t + 1
  | _ :: t => pullTotal t

/-!
## §2. THE LICENSES  (live, KEPT 2026-10-17)
-/

/-- **CanRaise st c** — the vanilla lift license: next-up, and the
card sits top-of-pile with a chop beneath it or a bare-king seat.
PORTED VERBATIM from `Orig/Canonical.lean:359`. -/
def CanRaise (st : State) (c : Card) : Prop :=
  st.nextUp c = true ∧ ∃ a, st.pileOfTop c = some a ∧
    (chop (st.piles a).faceUp ≠ [] ∨
      ((st.piles a).hidden = [] ∧ c.rank = Rank.king))

/-- **CanRaiseS st c** — the swap-aware license: raisable now
(vanilla), or raisable after finitely many licensed cargo slides —
the {slide · raise} closure, the cascade license.  PORTED VERBATIM
from `Orig/MacroInternal.lean:1176`. -/
inductive CanRaiseS : State → Card → Prop
  | now {st : State} (c : Card) (h : CanRaise st c) : CanRaiseS st c
  | via {st st' : State} (c : Card)
      (hl : ∃ d b, st.step (.tabToTab d b) = some st' ∧
                       reversibleAtW st (.tabToTab d b))
      (h : CanRaiseS st' c) : CanRaiseS st c

/-!
## §3. THE CLASS FOUNDATION  (live, KEPT 2026-10-17)
-/

/-- **ShufflePlayW** — a witness shuffle: a legal play whose every
move carries an explicit undoubling play back to the position it was
played from (the constructive content of `reversibleAt`).  PORTED
VERBATIM from `Orig/Combine.lean:51`. -/
inductive ShufflePlayW : State → List Move → State → Prop
  | nil (st : State) : ShufflePlayW st [] st
  | cons {st : State} {m : Move} {s₁ : State} {rest : List Move} {st' : State}
      (hw : reversibleAtW st m) (hstep : State.step st m = some s₁)
      (hrest : ShufflePlayW s₁ rest st') :
      ShufflePlayW st (m :: rest) st'

/-- Support kit (the setoid's carrier rows — the ONE structural
exception to definitions-only, flagged): witness shuffles
concatenate.  PORTED VERBATIM from `Orig/Combine.lean:71`. -/
theorem ShufflePlayW_append {a : State} : ∀ {l₁ : List Move} {b : State},
    ShufflePlayW a l₁ b → ∀ {l₂ : List Move} {c : State},
    ShufflePlayW b l₂ c → ShufflePlayW a (l₁ ++ l₂) c := by
  intro l₁ b h
  induction h with
  | nil s =>
      intro l₂ c h₂
      exact h₂
  | cons hw hstep hrest ih =>
      intro l₂ c h₂
      exact .cons hw hstep (ih h₂)

/-- **RevEqW s s'** — the reversible quotient in witness form: two
positions joined by witness shuffles in both directions.  PORTED
VERBATIM from `Orig/Combine.lean:121`. -/
def RevEqW (s s' : State) : Prop :=
  ∃ σ, ShufflePlayW s σ s' ∧ ∃ τ, ShufflePlayW s' τ s

/-- Support kit (flagged): reflexivity of the carrier.  PORTED
VERBATIM from `Orig/Combine.lean:125`. -/
theorem RevEqW_refl (s : State) : RevEqW s s :=
  ⟨[], ShufflePlayW.nil s, [], ShufflePlayW.nil s⟩

/-- Support kit (flagged): symmetry of the carrier.  PORTED
VERBATIM from `Orig/Combine.lean:130`. -/
theorem RevEqW_symm {s s' : State} (h : RevEqW s s') : RevEqW s' s := by
  obtain ⟨σ, hσ, τ, hτ⟩ := h
  exact ⟨τ, hτ, σ, hσ⟩

/-- Support kit (flagged): transitivity of the carrier.  PORTED
VERBATIM from `Orig/Combine.lean:135`. -/
theorem RevEqW_trans {a_ b c : State} (h₁ : RevEqW a_ b) (h₂ : RevEqW b c) :
    RevEqW a_ c := by
  obtain ⟨σ, hσ, ρ, hρ⟩ := h₁
  obtain ⟨ν, hν, μ, hμ⟩ := h₂
  exact ⟨σ ++ ν, ShufflePlayW_append hσ hν, μ ++ ρ, ShufflePlayW_append hμ hρ⟩

/-- **sameOrbitSetoid** — THE MACRO STATE: the witness reversible
quotient (the rev-closure; the twin relabeling descends to an
automorphism, not an identification).  PORTED VERBATIM from
`Orig/Combine.lean:158`. -/
instance sameOrbitSetoid : Setoid State where
  r a b := RevEqW b a
  iseqv := ⟨fun a => RevEqW_refl a, fun h => RevEqW_symm h,
    fun h k => RevEqW_trans k h⟩

/-- **SameOrbit** — positions modulo the same-orbit relation.  PORTED
VERBATIM from `Orig/Combine.lean:164`. -/
abbrev SameOrbit := Quotient sameOrbitSetoid

/-- **classOf C w** — membership in a macro class.  PORTED VERBATIM
from `Orig/MacroInternal.lean:51`. -/
def classOf (C : SameOrbit) (w : State) : Prop :=
  Quotient.mk sameOrbitSetoid w = C

/-- **rungAt w s** — the current founded count of a suit — the
rung.  PORTED VERBATIM from `Orig/MacroInternal.lean:55`. -/
def rungAt (w : State) (s : Suit) : Nat := (w.found s).length

/-- **twinSuit s₁ s₂** — suits of one color.  PORTED VERBATIM from
`Orig/MacroInternal.lean:58`. -/
def twinSuit (s₁ s₂ : Suit) : Prop := s₁ = s₂ ∨ s₁ = s₂.twin

/-!
# THE REVIEW ANNEX — pending adjudication

The old tier's remaining main vocabulary.  Verdict slots open; no
pending entry is ported.

## KILLED (owner, 2026-10-17) — never re-land; fences

* `weakForkState` (`Orig/MacroInternal.lean:1069`) — RETIRED from
  the new vocabulary.  The weak grade lives only where it already
  is: inside the frozen tier's G2 falsifier records and their
  consumed rows.  FENCE: no new-interface row is stated at the weak
  grade; new detection content speaks `CanRaiseS`-grade only.
* `FaceShape` — RETIRED (`Orig/MacroInternal.lean:1362`).
* `conjugateForkState` — RETIRED (`Orig/MacroInternal.lean:1126`).
* `conjugateCompositeRev` — RETIRED (`Orig/MacroInternal.lean:1565`).
  FENCE (the family): the conjugate-composite vocabulary exits; the
  frozen tier's composite rows (the §9 wave, the S-siblings) stay on
  record as boundary data.

## PENDING — licenses, letters & grades

* `FlatStep` / `FlatPath` (`Orig/MacroInternal.lean:458,510`)
  REVIEW: ☐ KEEP-SHAPE  ☐ RESTATE (line:)  ☐ RETIRE
* `CargoPath` (`Orig/MacroInternal.lean:1348`)
  REVIEW: ☐ KEEP-SHAPE  ☐ RESTATE (line:)  ☐ RETIRE
* `Journey` (`Orig/MacroInternal.lean:1304`)
  REVIEW: ☐ KEEP-SHAPE  ☐ RESTATE (line:)  ☐ RETIRE
* `canon` / `satStep` / `canonAux` (`Orig/Canonical.lean:1480-1493`;
  companions `pick`/`raise` port along)
  REVIEW: ☐ KEEP-SHAPE  ☐ RESTATE (line:)  ☐ RETIRE
* `Final` — `def Final (st : State) : Prop := ∀ c, ¬ CanRaise st c`
  (`Orig/Canonical.lean:406`)
  REVIEW: ☐ KEEP-SHAPE  ☐ RESTATE (line:)  ☐ RETIRE
* `saturatesTo` (`Orig/MacroInternal.lean:1198`; companion `StackRun`)
  REVIEW: ☐ KEEP-SHAPE  ☐ RESTATE (line:)  ☐ RETIRE
* `atRungInClass` / `satStackable` / `strandedInClass` /
  `pendingForever` / `surelyStackable` (`Orig/MacroInternal.lean:65-89`)
  REVIEW (family): ☐ KEEP-SHAPE  ☐ RESTATE (line:)  ☐ RETIRE
* `forkedCard` (`Orig/MacroInternal.lean:1218`)
  REVIEW: ☐ KEEP-SHAPE  ☐ RESTATE (line:)  ☐ RETIRE
* `unionable` / `unionRung` (`Orig/MacroInternal.lean:1281,1285`)
  REVIEW: ☐ KEEP-SHAPE  ☐ RESTATE (line:)  ☐ RETIRE
* `OnlyPairLicensed` (`Orig/MacroInternal.lean:1331`)
  REVIEW: ☐ KEEP-SHAPE  ☐ RESTATE (line:)  ☐ RETIRE
* `coveredIn` (`Orig/MacroInternal.lean:1168`)
  REVIEW: ☐ KEEP-SHAPE  ☐ RESTATE (line:)  ☐ RETIRE

## PENDING — detection

* `forkState` (`Orig/MacroInternal.lean:1193`) and `ForkWitness`
  (`Orig/PairName.lean:27`) — the S-grade pair and its per-witness
  parcel.
  REVIEW: ☐ KEEP-SHAPE  ☐ RESTATE (line:)  ☐ RETIRE

## PENDING — frontier vocabulary (layer 3-5, restated at their
migration cards)

`familyBelowFrontier` (`Orig/LowSlab.lean:239`), `WasteGuard`
(`Orig/LowSlab.lean:1810`), `DescentMove`/`DescentStuck`/`PullPlay`
(`Orig/ForkDescent.lean:132,140,146`), the `ForkCensus` filter
family, `below_fork` (owner DRAFT line pending ratification:
`ForkWitness st x ∧ (x.twin face-up or covered-hidden in some pile)`),
the steered-ascent zone rows (in-flight).

## HOUSE COMPLIANCE

Definitions only, modulo the flagged setoid support kit (audited:
the four rows are the verbatim carrier kit); zero sorry; zero
`Classical.choice`; the seam import is `Orig2.Model`.
-/
