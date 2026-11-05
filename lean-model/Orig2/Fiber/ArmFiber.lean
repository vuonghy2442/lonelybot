import Orig2.Fork.Local.ForkCriticalPair
import Orig2.Substrate.PairClassSeed

set_option autoImplicit false

/-!
# Orig2.ArmFiber — saturated arms, cargo fibers, and the arm residue

THE ARM DECOMPOSITION'S PROVABLE CORE.  This card formalizes the part
of the "saturated class = graph of (arm, cargo fiber) vertices" picture
that is provable today, states the exact residue the graph picture adds
(`ArmDichotomy`, `Orig2/Substrate/Vocab.lean`), and records the Position-level
fork certificate.

## What is proved here

* `canRaiseS_bareCargo_iff'` — the S-license is a cargo-fiber invariant
  WITHOUT `WF` (the repo's `canRaiseS_bareCargo_iff`,
  `Orig2/Substrate/CargoRaise.lean`, needs `hwf` and is stated existentially).
* `ssaturated_bareCargo_iff` — saturation descends to `BareCargoEquiv`.
* `bareCargo_rungs` — cargo fibers have a well-defined rung vector
  (foundations are cargo-fixed).
* `ForkLive` — the fiber-level fork grade: the S-spectrum is exactly a
  twin pair.
## What is NOT proved (blockers, named)

* `ArmDichotomy` itself — REFUTED by the draw counterexample
  (`Orig2/Boundary.lean`, `armDichotomy_draw_false`).  The repaired
  flat-fiber target is `ArmDichotomySW` (`Orig2/Fiber/SWDichotomy.lean`);
  do not re-attack the cargo-fiber form.
* `ForkLive → forkState`: the vanilla orientation pin
  `¬ CanRaise st x.twin` is representative-dependent, not fiber-level.
  The repo's killed `weakForkState` is exactly `ForkLive`; do not
  silently resurrect it (`Orig2/Substrate/Vocab.lean`'s fence note).
* The graph-is-a-tree claim is FALSE as stated: the `vcS` class already
  has two `K_{2,2}` fork-orientation diamonds and the Plan-4 `s1` class
  has quotient cycle rank 92.  Only the fork-contracted `vcS` core is a
  tree; do not adopt the tree slogan.

House compliance: additive leaf (`Orig2.ForkCriticalPair` for the local
fork rows, `Orig2.PairClassSeed` for the detection bridge); zero
`sorry`, zero `Classical.choice`; battery at the tail.
-/

/-! ## §1. Cargo-fiber invariants -/

/-- **THE S-LICENSE IS A CARGO-FIBER INVARIANT** — no `WF` needed: a
`BareCargoEquiv` pair carries a cargo path in BOTH directions, so a
cargo path from either endpoint appends to one from the other. -/
theorem canRaiseS_bareCargo_iff' {a b : State} (h : BareCargoEquiv a b)
    (c : Card) : CanRaiseS a c ↔ CanRaiseS b c := by
  obtain ⟨hab, hba⟩ := h
  constructor
  · rintro ⟨z, haz, hz⟩
    exact ⟨z, steps_trans hba haz, hz⟩
  · rintro ⟨z, hbz, hz⟩
    exact ⟨z, steps_trans hab hbz, hz⟩

/-- **SATURATION DESCENDS** — a `BareCargoEquiv` pair agrees on
`SSaturated`, again with no `WF`. -/
theorem ssaturated_bareCargo_iff {a b : State} (h : BareCargoEquiv a b) :
    SSaturated a ↔ SSaturated b := by
  constructor
  · intro ha c hc
    exact ha c ((canRaiseS_bareCargo_iff' h c).mpr hc)
  · intro hb c hc
    exact hb c ((canRaiseS_bareCargo_iff' h c).mp hc)

/-- A cargo leg fixes every rung. -/
theorem rungAt_cargoLeg {a b : State} (h : CargoLeg a b) (σ : Suit) :
    rungAt a σ = rungAt b σ := by
  obtain ⟨c, base, hstep, -⟩ := h
  exact (rungAt_tabToTab hstep σ).symm

/-- **CARGO FIBERS HAVE A WELL-DEFINED RUNG VECTOR** — the
`BareCargoEquiv` class fixes the foundations' heights.  (The frozen
tier's `cargo_fix_rungs`, `Orig/ForklessCeiling.lean:1224`, is the same
row at the old vocabulary.) -/
theorem bareCargo_rungs {a b : State} (h : BareCargoEquiv a b) :
    RungEq a b :=
  fun σ => rungAt_cargoPath h.1 σ

/-! ## §2. The fiber-level fork grade -/

/-- **ForkLive st** — the fiber-level ("weak") fork read: the S-license
spectrum is EXACTLY one twin pair `{x, x.twin}`.  This is the first
conjunct of `forkState`/`ForkWitness`; it omits the vanilla orientation
pin `¬ CanRaise st x.twin`, which is NOT a fiber invariant.  (The old
tier's `weakForkState`, `Orig/MacroInternal.lean:1069`, was this shape
and was killed — the fence note at `Orig2/Substrate/Vocab.lean`; this def is the
fiber-grade name, not a re-landing of the detection.) -/
def ForkLive (st : State) : Prop :=
  ∃ x, ∀ c, (c = x ∨ c = x.twin) ↔ CanRaiseS st c

/-- **THE DETECTION IMPLIES THE FIBER GRADE** — `forkState` is
`ForkLive` plus the vanilla pin. -/
theorem forkState_forkLive {st : State} (h : forkState st) : ForkLive st := by
  obtain ⟨x, h1, -⟩ := h
  exact ⟨x, h1⟩

/-- **THE FIBER GRADE DESCENDS** — `ForkLive` is a `BareCargoEquiv`
invariant, by `canRaiseS_bareCargo_iff'`. -/
theorem forkLive_bareCargo_iff {a b : State} (h : BareCargoEquiv a b) :
    ForkLive a ↔ ForkLive b := by
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x, fun c => (hx c).trans (canRaiseS_bareCargo_iff' h c)⟩
  · rintro ⟨x, hx⟩
    exact ⟨x, fun c => (hx c).trans (canRaiseS_bareCargo_iff' h c).symm⟩

/-! ## §4. Position-level fork certificates -/

/-- **forkLikePos** — the Position-level fork-presence certificate: the
descended spectrum is exactly one twin pair.  It is BFS-free: it reads a
single `Position`. -/
def forkLikePos (q : Position) : Prop :=
  ∃ x, ∀ c, (c = x ∨ c = x.twin) ↔ spec q c

/-- The certificate at a representative. -/
theorem forkLikePos_mk (p : WFState) :
    forkLikePos (Quotient.mk orbitRungSetoid p) ↔ ForkLive p.1 :=
  Iff.rfl

/-! ## §6. Audit -/

#print axioms canRaiseS_bareCargo_iff'
#print axioms ssaturated_bareCargo_iff
#print axioms bareCargo_rungs
