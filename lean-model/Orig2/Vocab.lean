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
`classOf`, `rungAt`, `twinSuit`, the reversibility carrier
`reversibleAtW`, and the journey letters
`FlatStep`/`FlatPath`/`CargoPath`/`Journey`.  PENDING — everything
in the annex below.

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
## §1.5. THE REVERSIBILITY CARRIER  (live, KEPT 2026-10-17)
-/

/-- **reversibleAtW st m** — the witness form of reversible: the move
is legal and an EXPLICIT play returns to the origin — the
constructive content every class-grade letter rides on.  PORTED
VERBATIM from `Orig/Fate.lean:92`.  DESIGN NOTE (carried from the
old home): the unconditioned iff between the negative form
(`reversibleAt`) and this witness form is deliberately NOT stated —
it is the one step that drags `Classical.choice` through the
vocabulary; the new tier keeps the same discipline: classification
rows supply the effective dichotomy themselves. -/
def reversibleAtW (st : State) (m : Move) : Prop :=
  ∃ s₁ play, State.step st m = some s₁ ∧ s₁.run play = some st

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
## §4. THE JOURNEY LETTERS  (live, KEPT 2026-10-17)
-/

/-- **FlatStep** — the flat letters: a reversible cargo slide or a
reversible draw loop (the two non-writing letters — phase rotations).
PORTED VERBATIM from `Orig/MacroInternal.lean:458`. -/
inductive FlatStep : State → State → Prop
  | cargo {w u : State} (c : Card) (b : Base)
      (hstep : w.step (.tabToTab c b) = some u)
      (hrev : reversibleAtW w (.tabToTab c b)) : FlatStep w u
  | draw {w u : State}
      (hstep : w.step .draw = some u)
      (hrev : reversibleAtW w .draw) : FlatStep w u

/-- **FlatPath** — a block of flat letters; the interior grammar of
brackets and phases.  PORTED VERBATIM from
`Orig/MacroInternal.lean:510`. -/
inductive FlatPath : State → State → Prop
  | refl (w : State) : FlatPath w w
  | cons {w z u : State} (h : FlatStep w z) (t : FlatPath z u) : FlatPath w u

/-- **CargoPath** — the flat world's cargo letter ALONE (no draws:
phase stays pinned); free twin swaps realize as one cargo move.
PORTED VERBATIM from `Orig/MacroInternal.lean:1348`. -/
inductive CargoPath : State → State → Prop
  | refl (w : State) : CargoPath w w
  | cons {w z w' : State} (h : FlatStep w z)
      (hkind : ∃ c b hstep hrev, h = FlatStep.cargo c b hstep hrev)
      (t : CargoPath z w') : CargoPath w w'

/-- **Journey** — a legal journey: any play of legal moves.  PORTED
VERBATIM from `Orig/MacroInternal.lean:1304`. -/
inductive Journey : State → State → Prop
  | refl (w : State) : Journey w w
  | cons {w u u' : State} (h : ∃ m, w.step m = some u) (t : Journey u u') :
      Journey w u'

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

## PENDING — the 2026-10-17 completeness pass (owner-caught gap)

The first annex cut missed whole def tiers; indexed verbatim-cite,
pending adjudication like the rest:

* **The phase/rotation tier** (`Orig/OrbitFactor.lean`,
  `Orig/Canonical.lean`) — the orbit-FACTORING vocabulary:
  `NoDrawPlayW` (OrbitFactor:40), `swCompSetoid` (:587), `SWPhase`
  (:594), `mkSW` (:597); with `SWComp` (Canonical:2473),
  `DrawPlayW` (:2477), `SWRotW` (:2483).  These carry the
  factorization claims `sameOrbit_factor_fwd`/`sameOrbit_factor_full`
  (`Orig/OrbitFactorC.lean:442,482`) — Claims-layer candidates once
  their vocabulary lands.
  REVIEW (family): ☐ KEEP-SHAPE  ☐ RESTATE (line:)  ☐ RETIRE
* **The tip-edge datum tier** (`Orig/EdgeLabel.lean`) —
  `EdgeLabel` (535), `TipEdge` (1386), `MacroDatums` (1322) +
  `datumOf`/`CanonLabel`/`labelOf`/`drawNext`/`drawNextQ`/
  `wasteNext`/`SameDatums` + the pool-miss/dropper/root-freed
  family, `WasteOf`, `RevealCellAt`/`VacateCellAt`, `nzRoot`,
  `isWasteMove`.
  REVIEW (family): ☐ KEEP-SHAPE  ☐ RESTATE (line:)  ☐ RETIRE
* **The census kit** (`Orig/HostCensus.lean`) — `seatInd` (109),
  `hostCensus` (120), `kingAnchored` (459), `seatGain`/`seatMint`/
  `seatBurn` (1933-1947), `journeyMint`/`journeyBurn` (2111-2119),
  `boardEq`/`boardMove` (2483-2486).
  REVIEW (family): ☐ KEEP-SHAPE  ☐ RESTATE (line:)  ☐ RETIRE
* **The residency trio** (`Orig/ZoneAgree.lean`) — `foundResident`,
  `tabResident`, `cycleResident` (:25-33).
  REVIEW (family): ☐ KEEP-SHAPE  ☐ RESTATE (line:)  ☐ RETIRE
* **Slab both-suits form** — `xyBelowBoth` (`Orig/SlabForms.lean:93`).
  REVIEW: ☐ KEEP-SHAPE  ☐ RESTATE (line:)  ☐ RETIRE
* **Canonical supports** (`Orig/Canonical.lean`) — `Stackable`
  (321), `canRaiseB` (365), `pick` (409), `IsRaise`/`raise`
  (465-469), `StackRun` (530), `suitGap`/`stackFuel` (541-544),
  `drawPool` (2466), `SameMacroO` (2930).
  REVIEW (family): ☐ KEEP-SHAPE  ☐ RESTATE (line:)  ☐ RETIRE
* **Composites** (`Orig/Classify.lean`) — `irreversibleOf` (2854),
  `WFRun` (2907).
  REVIEW (family): ☐ KEEP-SHAPE  ☐ RESTATE (line:)  ☐ RETIRE
* **Cone/dance & ledger walls** (`Orig/MacroInternal.lean`) —
  `ConeStep`/`ConePath` (329/341), `DanceStep`/`DancePath`
  (388/394), `popWindow` (810), `ConeLedger` (838), `rungFiber`
  (1011), `CanonFace` (1379).
  REVIEW (family): ☐ KEEP-SHAPE  ☐ RESTATE (line:)  ☐ RETIRE

## HOUSE COMPLIANCE

Definitions only, modulo the flagged setoid support kit (audited:
the four rows are the verbatim carrier kit); zero sorry; zero
`Classical.choice`; the seam import is `Orig2.Model`.
-/
