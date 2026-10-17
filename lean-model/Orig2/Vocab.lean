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

OWNER REVIEW LEDGER (2026-10-17): KILLED — the early four
(`weakForkState`, `FaceShape`, `conjugateForkState`,
`conjugateCompositeRev`), the witness-only restate's semantic pair,
the commit-polarity shape originals, and the class-grade sweep
(the canon family, `Final`, the five class-grade reads,
`forkedCard`, `unionable`/`unionRung`, `OnlyPairLicensed`) — full
fences and lineage in the annex's KILLED section, where the
retirements' consumer records (the G2 falsifier rows, the §9
composites, the class-grade consumers) are noted as frozen-tier
boundary data.  KEPT —
`CanRaise`, `CanRaiseS`, `ShufflePlayW`, `RevEqW`, `sameOrbitSetoid`,
`classOf`, `rungAt`, `twinSuit`, the reversibility carrier
`reversibleAtW` (the regime's ONE semantic notion), the R-shapes
`drawR`/`tabToFoundR`/`foundToTabR`/`tabToTabR` and the
negation-free oracle `reversibleOf` (the inside-flip; the
commit-polarity originals retired), and the journey letters
`FlatStep`/`FlatPath`/`CargoPath`/`Journey`, and the detection
pair `forkState`/`ForkWitness`.  PENDING — everything
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
## §1.6. THE UNDOABILITY ORACLE  (live, KEPT 2026-10-17; shapes
flipped reversible-first, then the WITNESS-ONLY REGIME adopted —
both owner restates the same day)

The oracle tier: each shape predicate reads UNDOABILITY natively
(`drawR`, `tabToFoundR`, `foundToTabR`, `tabToTabR`) — the flip
superseded the commit-polarity originals (retired; their frozen
homes keep the certified classification rows).  THE WITNESS-ONLY
REGIME: the semantic pair `irreversibleAt`/`reversibleAt` is
RETIRED with it — the program's ONE reversibility notion is the
carrier `reversibleAtW`, decided at WF by the oracle below;
commitment is what shape-false MEANS at WF (the program never
leaves WF), and the wild-state divergence corners stay archived as
boundary data.  Retirement record: the commitment notion re-enters
only if a future card demonstrates a need the witness grade cannot
serve.  The specification rows (the WF-gated bridge, the
decidability rider) are Claims-layer material, not registry.
-/

/-- **drawR st** — the draw undoability shape: no stock and the
waste rests (or stock present and the cycle rests off-multiple)
means the draw re-deals back; with stock and an off-rest waste the
draw consumes irreversibly.  RESTATE (polarity flip) of the
commit-polarity `drawIrr` (`Orig/Classify.lean:2778`); each case
flipped, provenance cited. -/
def drawR (st : State) : Bool :=
  match st.stock with
  | [] => decide (st.waste ≠ [])
  | _ => decide (st.waste ≠ []) && decide (st.waste.length % st.drawStep = 0)

/-- **tabToFoundR st c** — the raise undoability shape: reversible
iff licensed AND a chop beneath the card (the giveback seat), or a
bare KING seat (the emptied seat readmits the king); bare non-king
lifts and hidden flips are commits.  RESTATE (polarity flip) of
the commit-polarity `tabToFoundIrr` (`Orig/Classify.lean:1775`);
each case flipped. -/
def tabToFoundR (st : State) (c : Card) : Bool :=
  match st.nextUp c with
  | false => false
  | true =>
      match st.pileOfTop c with
      | none => false
      | some a =>
          match chop (st.piles a).faceUp with
          | [] =>
              match (st.piles a).hidden with
              | [] => decide (c.rank = Rank.king)
              | _ :: _ => false
          | _ :: _ => true

/-- **foundToTabR st c b** — the pull undoability shape: reversible
iff the suit's founded top IS the card AND the landing base
accepts it (the re-raise); any other read is a commit.  RESTATE
(polarity flip) of the commit-polarity `foundToTabIrr`
(`Orig/Classify.lean:1974`); each case flipped. -/
def foundToTabR (st : State) (c : Card) (b : Base) : Bool :=
  match st.foundTop c.suit with
  | none => false
  | some c' => if c' = c then st.canPlace c b else false

/-- **tabToTabR st c b** — the slide undoability shape: reversible
iff holding is known, the landing accepts, and the card rides with
company beneath it (the segment relocates whole), or a bare KING
seat; hidden flips and bare non-king moves are commits.  RESTATE
(polarity flip) of the commit-polarity `tabToTabIrr`
(`Orig/Classify.lean:2166`); each case flipped. -/
def tabToTabR (st : State) (c : Card) (b : Base) : Bool :=
  match st.pileHolding c with
  | none => false
  | some a =>
      match st.canPlace c b with
      | false => false
      | true =>
          match below c (st.piles a).faceUp with
          | [] =>
              match (st.piles a).hidden with
              | [] => decide (c.rank = Rank.king)
              | _ :: _ => false
          | _ :: _ => true

/-- **reversibleOf st m** — the per-move oracle, REVERSIBLE-FIRST
(owner flip, 2026-10-17): the assembly reads undoability directly
from the R-shapes — no negations anywhere.  At WF states this
decides THE WITNESS CARRIER exactly (the Claims-tier bridge:
`reversibleOf st m = true ↔ reversibleAtW st m`); deliberately not
a global instance-gate — at wild states the shape and the carrier
diverge in both directions (the witnessed corners are in the
frozen-tier witness archive).  Restate lineage: the old
`irreversibleOf` (`Orig/Classify.lean:2854`) → the negated-assembly
flip → the inside-flipped R-shapes (this, the final form). -/
def reversibleOf (st : State) (m : Move) : Bool :=
  match m with
  | .draw => drawR st
  | .wasteToFound _ => false
  | .wasteToTab _ _ => false
  | .tabToFound c => tabToFoundR st c
  | .foundToTab c b => foundToTabR st c b
  | .tabToTab c b => tabToTabR st c b

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
## §3. THE CLASS FOUNDATION  (live, KEPT 2026-10-17; the walk
unification restate executed the same day by owner decree —
completed before the in-flight missions' cards rather than after,
constructor names and statements preserved through the abbrevs)
-/

/-- **Walk P st ρ W** — THE GENERIC PLAY CLOSURE (the walk
unification, owner restate 2026-10-17): a legal play whose every
letter satisfies the letter predicate `P st m` at its origin.
The list-carrying journey grades are instances of this one
closure; the state-pair step relations (`FlatStep`/`FlatPath`/
`CargoPath`, whose letters bind the successor state or filter by
kind) and the letter-free `Journey` stay outside the unification,
on shape merit. -/
inductive Walk (P : State → Move → Prop) :
    State → List Move → State → Prop
  | nil (st : State) : Walk P st [] st
  | cons {st s₁ W : State} {m : Move} {ρ : List Move}
      (hlet : P st m) (hstep : State.step st m = some s₁)
      (hrest : Walk P s₁ ρ W) :
      Walk P st (m :: ρ) W

/-- **ShufflePlayW** — a witness shuffle: a legal play whose every
move carries an explicit undoubling play back to the position it
was played from (the constructive content of `reversibleAt`).  The
Walk instance at the reversibility letter.  RESTATE (owner
unification): formerly the verbatim port of
`Orig/Combine.lean:51`, now `Walk` applied — identical statements,
constructor names preserved. -/
abbrev ShufflePlayW := Walk (fun st m => reversibleAtW st m)

/-- Support kit (the setoid's carrier rows — the ONE structural
exception to definitions-only, flagged).  Walk legs run. -/
theorem Walk_run (P : State → Move → Prop) {st : State} :
    ∀ {ρ : List Move} {W : State}, Walk P st ρ W → st.run ρ = some W := by
  intro ρ W h
  induction h with
  | nil s => rfl
  | cons _ hstep _ ih =>
      simp only [State.run, hstep]
      exact ih

/-- Support kit (flagged): walks concatenate — one proof for every
letter grade. -/
theorem Walk_append (P : State → Move → Prop) {a b : State} :
    ∀ {l₁ : List Move}, Walk P a l₁ b →
    ∀ {l₂ : List Move} {c : State}, Walk P b l₂ c →
    Walk P a (l₁ ++ l₂) c := by
  intro l₁ h
  induction h with
  | nil s => intro l₂ c h₂; exact h₂
  | @cons st s₁ b' m ρ' hlet hstep hrest ih =>
      intro l₂ c h₂
      rw [List.cons_append]
      exact .cons hlet hstep (ih h₂)

/-- Support kit forwarding (name stability for the ported rows
that cite it): witness shuffles concatenate. -/
theorem ShufflePlayW_append {a : State} : ∀ {l₁ : List Move} {b : State},
    ShufflePlayW a l₁ b → ∀ {l₂ : List Move} {c : State},
    ShufflePlayW b l₂ c → ShufflePlayW a (l₁ ++ l₂) c :=
  Walk_append _

/-- **RevEqW s s'** — the reversible quotient in witness form: two
positions joined by witness shuffles in both directions.  PORTED
VERBATIM from `Orig/Combine.lean:121`. -/
def RevEqW (s s' : State) : Prop :=
  ∃ σ, ShufflePlayW s σ s' ∧ ∃ τ, ShufflePlayW s' τ s

/-- Support kit (flagged): reflexivity of the carrier.  PORTED
VERBATIM from `Orig/Combine.lean:125` (constructor head corrected
to the generic at the walk unification). -/
theorem RevEqW_refl (s : State) : RevEqW s s :=
  ⟨[], Walk.nil s, [], Walk.nil s⟩

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
## §4. THE JOURNEY LETTERS  (live, KEPT 2026-10-17; the state-pair
unification executed the same day — the closures become instances
of the generic `Steps Q`, and the CargoPath kind-filter wart
dissolves into a clean direct letter)
-/

/-- **FlatStep** — the flat letters: a reversible cargo slide or a
reversible draw loop (the two non-writing letters — phase
rotations).  The LETTER ALPHABET; the closures over it are
`Steps Q` instances below.  PORTED VERBATIM from
`Orig/MacroInternal.lean:458`. -/
inductive FlatStep : State → State → Prop
  | cargo {w u : State} (c : Card) (b : Base)
      (hstep : w.step (.tabToTab c b) = some u)
      (hrev : reversibleAtW w (.tabToTab c b)) : FlatStep w u
  | draw {w u : State}
      (hstep : w.step .draw = some u)
      (hrev : reversibleAtW w .draw) : FlatStep w u

/-- **Steps Q** — THE GENERIC STATE-PAIR CLOSURE (the state-pair
half of the walk unification, owner restate 2026-10-17): the
refl-cons closure over any two-place letter predicate.  The
list-carrying grades live at `Walk P` (§3); the state-pair grades
below are instances of this one closure.

STATEMENT CONVENTION (owner, 2026-10-17) — STEPS FIRST: every new
span notion states at the lightest honest letter, as a `Steps Q`
instance; a notion reaches for `Walk P` exactly when its content
touches the moves themselves — filter premises over letters,
census arithmetic, permutation and order arguments.  The test:
would a consumer ever need to know WHICH moves?  Never — `Steps`;
the analysis touches the letters — `Walk`.  (Letter-constrained
spans like `NoDrawPlayW` constrain over the letters and therefore
belong to `Walk` even though they read as span claims.  The
crossing is free: the banked generic bridges
`walk_to_steps`/`steps_to_walk` convert without re-derivation.) -/
inductive Steps (Q : State → State → Prop) : State → State → Prop
  | refl (w : State) : Steps Q w w
  | cons {w z u : State} (h : Q w z) (t : Steps Q z u) : Steps Q w u

/-- **StepOf P w u** — THE CONNECTING LETTER (the walk-steps
Rosetta): the transition shadow of a letter predicate — some
move satisfying `P` at the origin fires to `u`.  (The two generic
bridge rows that ran through this letter — the forgetful map and
the realization map — were banked green and pulled at the
owner's cargo pause, 2026-10-17: the bytes await at
`Temp/cargo_bridge_aborted.lean`.) -/
def StepOf (P : State → Move → Prop) (w u : State) : Prop :=
  ∃ m, P w m ∧ w.step m = some u

/-- **FlatPath** — a block of flat letters; the interior grammar of
brackets and phases.  The Steps instance at the flat alphabet.
RESTATE (owner unification): formerly the verbatim port of
`Orig/MacroInternal.lean:510`, now `Steps FlatStep` — identical
statement; the constructor head is `Steps.refl`/`Steps.cons`. -/
abbrev FlatPath := Steps FlatStep

/-- **CargoLeg w z** — the cargo letter as a DIRECT two-place
predicate: a fired reversible `tabToTab` leg.  RESTATE (the
kind-filter wart fix riding the unification): the old `CargoPath`
cons carried an `h : FlatStep w z` plus a kind-witness existential
rebuilding the cargo constructor's data — redundant pair; this
letter states the shape directly.  (The trivial bridge — a
`FlatStep` together with its cargo-kind witness IS a `CargoLeg` —
is a two-line claim whenever a consumer wants it.) -/
def CargoLeg (w z : State) : Prop :=
  ∃ c b, w.step (.tabToTab c b) = some z ∧
    reversibleAtW w (.tabToTab c b)

/-- **CargoPath** — the flat world's cargo letter ALONE (no draws:
phase stays pinned); free twin swaps realize as one cargo move.
The Steps instance at the cargo letter.  RESTATE (owner
unification): formerly the verbatim port of
`Orig/MacroInternal.lean:1348` with its kind-witness cons, now
`Steps CargoLeg` — identical span content, the direct letter. -/
abbrev CargoPath := Steps CargoLeg

/-- **Journey** — a legal journey: any play of legal moves.  The
Steps instance at the anonymous some-fired-move letter.  RESTATE
(owner unification): formerly the verbatim port of
`Orig/MacroInternal.lean:1304`, now the `Steps` instance — identical
statement (`refl` + the ∃-letter cons). -/
abbrev Journey := Steps (fun w u => ∃ m, w.step m = some u)

/-!
## §4.5. THE TWIN INVOLUTION ON CARDS  (live, KEPT 2026-10-17)
-/

/-- **Card.twin c** — the twin relabeling on cards: every card's
suit becomes its same-color twin.  PORTED VERBATIM from
`Orig/Twin.lean:33` (the one-liner is registry-owned rather than
seam-carried — the `Orig.Twin` module's transitive imports
collide with the registry's `reversibleAtW`; the involution
lemmas ride at the Claims layer when needed). -/
def Card.twin (c : Card) : Card := ⟨c.suit.twin, c.rank⟩

/-!
## §5. THE DETECTION  (live, KEPT 2026-10-17)
-/

/-- **forkState st** — THE DETECTION, the maneuver-stable S-grade:
the pair-saturation iff at the {slide · raise} grade, plus the
orientation pin (the twin blocked under cargo).  PORTED VERBATIM
from `Orig/MacroInternal.lean:1193`.  NOTE (the witness-only
regime's detection side): the RETIRED weak grade does not re-enter
here — the falsifier family that separated the two grades stays
archived, and new detection-adjacent rows speak this shape. -/
def forkState (st : State) : Prop :=
  ∃ x, (∀ c, (c = x ∨ c = x.twin) ↔ CanRaiseS st c) ∧
       ¬ CanRaise st x.twin

/-- **ForkWitness st x** — the per-witness parcel of the
detection: `x` names the S-live pair (up to the twin flip) and its
twin is vanilla-blocked.  PORTED VERBATIM from
`Orig/PairName.lean:27`. -/
def ForkWitness (st : State) (x : Card) : Prop :=
  (∀ c, (c = x ∨ c = x.twin) ↔ CanRaiseS st c) ∧ ¬ CanRaise st x.twin

/-!
## §6. THE PHASE ROTATION COMPONENTS  (live, KEPT 2026-10-17;
the orbit-factor migration's vocabulary, owner-approved clean cut)
-/

/-- **NoDrawPlayW u v** — the board-move closure: two positions
joined by draw-free witness journeys both ways; the board can be
reshuffled from one to the other without ever touching the draw
zone.  PORTED VERBATIM from `Orig/OrbitFactor.lean:40`. -/
def NoDrawPlayW (u v : State) : Prop :=
  ∃ play, ShufflePlayW u play v ∧ (∀ m ∈ play, m ≠ Move.draw) ∧
    ∃ back, ShufflePlayW v back u ∧ (∀ m ∈ back, m ≠ Move.draw)

/-- **DrawPlayW u play v** — a witness shuffle consisting only of
draws.  PORTED VERBATIM from `Orig/Canonical.lean:2477`. -/
def DrawPlayW (u : State) (play : List Move) (v : State) : Prop :=
  ShufflePlayW u play v ∧ ∀ m ∈ play, m = Move.draw

/-- **SWRotW u v** — the witness-backed rotation closure: two
positions sit at rotations of one draw cycle, joined by draws-only
witness rounds.  PORTED VERBATIM from `Orig/Canonical.lean:2483`.
PLUMBING NOTE (the 2026-10-17 clean cut): the phase-quotient tier
(`SWComp`, `drawPool`, `inPhase`, `swCompSetoid`, `SWPhase`,
`mkSW`) is NOT ported — it was the factor card's consumer
interface and invariant bookkeeping; that content lives in the
machinery card as per-file private kit, and the quotient type is
resurrectable by a future card with its own intent line. -/
def SWRotW (u v : State) : Prop :=
  ∃ σ τ : List Move, DrawPlayW u σ v ∧ DrawPlayW v τ u

/-!
## §7. THE BARE-CARGO EXCHANGE  (live, KEPT 2026-10-17)
-/

/-- **CargoLetter st m** — the DUMB closure generator: any
`tabToTab` letter, no arm filter.  The state argument is the
`Walk P` letter-predicate SOCKET (the cargo letter itself is
state-independent — any tabToTab at any origin); the burn/reveal
arms are excluded BY THEOREM (the classification claim's slide
half), not by this definition.  PORTED from
`Orig/ForklessCeiling.lean:95` (binder trued to `_st`, recording
the socket-only role). -/
def CargoLetter (_st : State) (m : Move) : Prop :=
  ∃ (c : Card) (b : Base), m = Move.tabToTab c b

/-- **BareCargoEquiv A B** — the owner's bare-cargo exchange, with
REVERSIBILITY ENFORCED (owner restate, 2026-10-17: "we should
enforce the reversible so that it stays in class"): two states
joined by witness-grade cargo closures in both directions — every
leg carries its `reversibleAtW`, so both states sit in the same
reversibility class BY CONSTRUCTION.  RESTATE LINEAGE: the frozen
tier's definition (`∃ τ, CargoPlay A τ B ∧ ∃ ρ, CargoPlay B ρ A`,
`Orig/ForklessCeiling.lean:137`) was deliberately DUMB — any
tabToTab both ways — with per-leg reversibility a THEOREM of the
both-ways structure (the chain composite: each leg's return plays
suffix ++ reverse-span ++ prefix; that row was banked green and
pulled at the owner's cargo pause, 2026-10-17 — the bytes await
at `Temp/cargo_bridge_aborted.lean`).  PLUMBING NOTE: the cargo-orbit quotient
tier (`cargoSetoid`, `CargoOrbit`, the fiber rows) is not ported
— the orbit-factor precedent (§6); resurrectable by intent line. -/
def BareCargoEquiv (A B : State) : Prop :=
  CargoPath A B ∧ CargoPath B A

/-!
# THE REVIEW ANNEX — pending adjudication

The old tier's remaining main vocabulary.  Verdict slots open; no
pending entry is ported.

## KILLED (owner, 2026-10-17) — never re-land; fences

The sweep batch (the class-grade population tier + the canonical
machinery, all killed before any port — the frozen tier keeps the
certified rows as boundary data):

* `canon` / `satStep` / `canonAux` (with the `pick`/`raise`
  companions) — the deterministic saturator-canon exits the new
  vocabulary.  FENCE: any future canonical representative is a
  NEW shape with its own intent line, not this 53-step fold.
* `Final` (`∀ c, ¬ CanRaise st c`) — the vanilla saturation read
  exits.  Future saturation cards write their own grade.
* `atRungInClass` / `satStackable` / `strandedInClass` /
  `pendingForever` / `surelyStackable` — the one-existential
  class-grade family exits.  FENCE: the arm-contingency content
  (sat vs surely gap) returns only as a NEW grade with an owner
  line; the pairClass migration wave (the founding ledger's first
  wave) meets these grades as CONSUMERS — its card writes the new
  population vocabulary when chartered.
* `forkedCard` (sat ∧ ¬surely) — the fork's macro-grade arm
  language exits with the family it rode.
* `unionable` / `unionRung` — the saturating-descendant union
  profile exits.
* `OnlyPairLicensed` — the canonical-face fence row exits.
* `saturatesTo` (with its `StackRun` companion) — the saturating-
  completion read exits with the union and canon families it
  rode.
* `coveredIn` — the covered-seat read exits; future seating cards
  write their own.

Earlier kills the same day: `weakForkState` (the weak grade lives
only inside the frozen tier's G2 falsifier records),
`FaceShape`, `conjugateForkState`, `conjugateCompositeRev` (the
conjugate-composite family), the semantic commitment pair
`irreversibleAt`/`reversibleAt` (the witness-only regime), and the
commit-polarity shape originals `drawIrr`/`tabToFoundIrr`/
`foundToTabIrr`/`tabToTabIrr`/`irreversibleOf` (the inside-flip).

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

* **The phase/rotation tier** — RESOLVED 2026-10-17:
  `NoDrawPlayW`/`DrawPlayW`/`SWRotW` ported live (§6, the
  orbit-factor vocabulary); the quotient plumbing
  (`swCompSetoid`/`SWPhase`/`mkSW`) and the invariant bookkeeping
  (`SWComp`/`drawPool`/`inPhase`) NOT ported — private kit in the
  machinery card, resurrectable by intent line.
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
  `boardEq`/`boardMove` (2483-2486); (`Mobile`'s port was pulled
  with the floating tier — see the residency-trio bullet; the
  detector filters — `PairCandidate`, `CensusPass` and kin —
  stay with the census migration card.)
  REVIEW (family): ☐ KEEP-SHAPE  ☐ RESTATE (line:)  ☐ RETIRE
* **The residency trio + the floating read** — PULLED BY OWNER
  ("for now", 2026-10-17): `foundResident`/`tabResident`/
  `cycleResident` (`Orig/ZoneAgree.lean:25-33`) and `Mobile`
  (`Orig/ForkCensus.lean:125`) were ported live at commit
  `e165d78` and removed the same day by owner call; the bytes
  await at that commit.  REVIEW: resumes on owner word.
* **The twin-suffix exchange family** (the swap tier — surfaced by
  the owner's swap question, an index gap now closed):
  `TwinExchOK` (`Orig/TwinExchangeQuotient.lean:90`), `ExchStep`
  (:97), `exchAll` (:424), `ExchFamOk` (:432), and the
  `TwinExchangeBoth` suffix-swap rows; the frozen content: at any
  licensed twin pair the riding-suffix swap realizes as ONE cargo
  move (or the degenerate identity).  ATOMIC note: the single-leg
  swap at the new tier is `CargoLeg` itself (the tabToTab
  semantics); the twin family is the COORDINATED two-pile shape.
  REVIEW (family): ☐ KEEP-SHAPE  ☐ RESTATE (line:)  ☐ RETIRE
* **Slab both-suits form** — `xyBelowBoth` (`Orig/SlabForms.lean:93`).
  REVIEW: ☐ KEEP-SHAPE  ☐ RESTATE (line:)  ☐ RETIRE
* **Canonical supports** (`Orig/Canonical.lean`) — KILLED (owner,
  2026-10-17): `Stackable` (321), `canRaiseB` (365), `IsRaise`
  (465), `suitGap`/`stackFuel` (541-544), `SameMacroO` (2930) —
  the saturator-tail supports exit with the canon family they
  rode (`CanRaise`'s own Bool probe is unnecessary in the new
  tier; `SameMacroO` is the old setoid-mirror prose-restatement,
  redundant at the registry's own `sameOrbitSetoid`).  Earlier
  same-day resolutions: `pick`/`raise` killed with the canon
  family; `StackRun` killed with `saturatesTo`; `drawPool` went
  to the orbit-factor machinery card's private kit.
* **Composites** (`Orig/Classify.lean`) — `WFRun` (2907).
  (The oracle tier RESOLVED with lineage: `irreversibleOf` and its
  commit-polarity companions REMOVED in favor of the inside-flip —
  the live forms are the R-shapes `drawR`/`tabToFoundR`/
  `foundToTabR`/`tabToTabR` + the negation-free `reversibleOf`,
  registry §1.6.)
  REVIEW (family): ☐ KEEP-SHAPE  ☐ RESTATE (line:)  ☐ RETIRE
* **Cone/dance & ledger walls** (`Orig/MacroInternal.lean`) —
  KILLED (owner, 2026-10-17): `ConeStep`/`ConePath` (329/341),
  `DanceStep`/`DancePath` (388/394), `popWindow` (810),
  `ConeLedger` (838), `rungFiber` (1011), `CanonFace` (1379) —
  the cone/dance reachability walls and the canon-face dossier
  tier exit the new vocabulary; any future reachability content
  is a NEW shape with an owner line (the frozen cone/dance rows
  stay boundary data).

## HOUSE COMPLIANCE

Definitions only, modulo the flagged setoid support kit (audited:
the four rows are the verbatim carrier kit); zero sorry; zero
`Classical.choice`; the seam import is `Orig2.Model`.
-/
