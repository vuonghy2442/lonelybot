import Orig2.Fork.ForkCriticalPair
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

* `cargoSetoid` / `CargoFiber` — `BareCargoEquiv` is an equivalence
  relation (no `WF`: both directions are carried in the definition).
* `canRaiseS_bareCargo_iff'` — the S-license is a cargo-fiber invariant
  WITHOUT `WF` (the repo's `canRaiseS_bareCargo_iff`,
  `Orig2/Substrate/CargoRaise.lean`, needs `hwf` and is stated existentially).
* `ssaturated_bareCargo_iff` — saturation descends to `CargoFiber`.
* `bareCargo_rungs` — cargo fibers have a well-defined rung vector
  (foundations are cargo-fixed), so `fiberRungs` descends.
* `ForkLive` — the fiber-level fork grade: the S-spectrum is exactly a
  twin pair.  `forkState → ForkLive`; `ForkLive` descends.
* `SatArm` — a saturated arm is a cargo fiber with a rung label.
* `armDichotomy_to_satDifferFork` — the arm residue discharges the
  campaign's named residue.
* `forkless_bareCargo_unique` / `forkless_found_unique_via_fiber` — the
  campaign theorem re-derived from the arm residue.

## What is NOT proved (blockers, named)

* `ArmDichotomy` itself — sharp at `vcS/vcT`, no proof exists.
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

/-! ## §1. The cargo-fiber quotient -/

/-- **cargoSetoid** — `BareCargoEquiv` packaged as a setoid.  Symmetry
is the definition's own conjunction swap; transitivity is
`steps_trans` on both halves.  No `WF` is consulted. -/
def cargoSetoid : Setoid State where
  r a b := BareCargoEquiv a b
  iseqv :=
    ⟨fun a => ⟨Steps.refl a, Steps.refl a⟩,
     fun h => ⟨h.2, h.1⟩,
     fun h k => ⟨steps_trans h.1 k.1, steps_trans k.2 h.2⟩⟩

/-- **CargoFiber** — a `BareCargoEquiv` class: the graph's vertex type. -/
abbrev CargoFiber : Type := Quotient cargoSetoid

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

/-- **fiberSat** — saturation, descended to the fiber. -/
def fiberSat : CargoFiber → Prop :=
  Quotient.lift (fun st => SSaturated st)
    (fun _ _ h => propext (ssaturated_bareCargo_iff h))

/-- **fiberRungs** — the rung vector, descended to the fiber. -/
def fiberRungs : CargoFiber → Suit → Nat :=
  Quotient.lift (fun st σ => rungAt st σ)
    (fun _ _ h => funext (fun σ => bareCargo_rungs h σ))

/-- The defining equations at a representative. -/
theorem fiberSat_mk (st : State) :
    fiberSat (Quotient.mk cargoSetoid st) ↔ SSaturated st := Iff.rfl

theorem fiberRungs_mk (st : State) (σ : Suit) :
    fiberRungs (Quotient.mk cargoSetoid st) σ = rungAt st σ := rfl

/-! ## §2. Saturated arms -/

/-- **SatArm F rv** — THE ARM VERTEX: the cargo fiber `F` is saturated
and its rung vector is `rv`.  This is the "(saturated rung arm,
BareCargoEquiv class)" vertex of the target picture, with saturation
and the rung label both descended rather than read at a representative. -/
def SatArm (F : CargoFiber) (rv : Suit → Nat) : Prop :=
  fiberSat F ∧ ∀ σ, fiberRungs F σ = rv σ

/-- Every saturated state presents its fiber as an arm at its own rung. -/
theorem satArm_mk (st : State) (h : SSaturated st) :
    SatArm (Quotient.mk cargoSetoid st) (fun σ => rungAt st σ) :=
  ⟨(fiberSat_mk st).mpr h, fun σ => fiberRungs_mk st σ⟩

/-- **ARM INJECTIVITY ON THE RUNG LABEL** — the rung label is a function
of the fiber, so two assignments of `SatArm` to one fiber agree. -/
theorem satArm_rung_unique {F : CargoFiber} {rv rv' : Suit → Nat} :
    SatArm F rv → SatArm F rv' → rv = rv' := by
  rintro ⟨-, h1⟩ ⟨-, h2⟩
  funext σ
  exact (h1 σ).symm.trans (h2 σ)

/-! ## §3. The fiber-level fork grade -/

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

/-- **fiberFork** — the fiber-level fork grade, descended. -/
def fiberFork : CargoFiber → Prop :=
  Quotient.lift ForkLive (fun _ _ h => propext (forkLive_bareCargo_iff h))

theorem fiberFork_mk (st : State) :
    fiberFork (Quotient.mk cargoSetoid st) ↔ ForkLive st := Iff.rfl

/-! ## §4. The arm residue and the campaign theorem -/

/-- **THE ARM RESIDUE DISCHARGES `SatDifferFork`** — differing rungs
already force different cargo fibers by `bareCargo_rungs`, so the
dichotomy's second branch is the campaign's named fork. -/
theorem armDichotomy_to_satDifferFork (h : ArmDichotomy) : SatDifferFork := by
  intro u v hu hv horb hdiff
  obtain ⟨σ, hσ⟩ := hdiff
  rcases h u v hu hv horb with hbc | hfork
  · exact absurd (bareCargo_rungs hbc σ) hσ
  · exact hfork

/-- **THE ARM FORM OF THE CAMPAIGN THEOREM** — in a forkless class, two
saturated class-mates are the SAME cargo fiber.  This is the graph
statement "a forkless saturated class is a single arm vertex". -/
theorem forkless_bareCargo_unique (h : ArmDichotomy) {s s' : State}
    (hclass : sameOrbitSetoid.r s s')
    (hfrk : ∀ u, sameOrbitSetoid.r s u → ¬ forkState u)
    (hsat : SSaturated s) (hsat' : SSaturated s') :
    BareCargoEquiv s s' := by
  rcases h s s' hsat hsat' hclass with hbc | ⟨F, x, hF, hfx⟩
  · exact hbc
  · exact absurd (forkState_iff.mpr ⟨x, hfx⟩) (hfrk F hF)

/-- **THE CAMPAIGN THEOREM FROM THE ARM RESIDUE** — forkless + saturated
class-mates share their foundations verbatim.  The route is the graph
one: same fiber, hence same rungs, hence the same founded prefix. -/
theorem forkless_found_unique_via_fiber (h : ArmDichotomy) {s s' : State}
    (hwf : s.WF) (hwf' : s'.WF)
    (hclass : sameOrbitSetoid.r s s')
    (hfrk : ∀ u, sameOrbitSetoid.r s u → ¬ forkState u)
    (hsat : SSaturated s) (hsat' : SSaturated s') :
    s.found = s'.found := by
  have hbc := forkless_bareCargo_unique h hclass hfrk hsat hsat'
  funext σ
  exact found_congr_of_rungs hwf hwf' (bareCargo_rungs hbc σ)

/-! ## §5. Position-level fork certificates -/

/-- **forkLikePos** — the Position-level fork-presence certificate: the
descended spectrum is exactly one twin pair.  It is BFS-free: it reads a
single `Position`. -/
def forkLikePos (q : Position) : Prop :=
  ∃ x, ∀ c, (c = x ∨ c = x.twin) ↔ spec q c

/-- The certificate at a representative. -/
theorem forkLikePos_mk (p : WFState) :
    forkLikePos (Quotient.mk orbitRungSetoid p) ↔ ForkLive p.1 :=
  Iff.rfl

/-- **A FORK STATE PRESENTS THE POSITION CERTIFICATE** — no class search
is needed to certify the PRESENCE of a fork at a Position. -/
theorem forkState_forkLikePos {p : WFState} (h : forkState p.1) :
    forkLikePos (Quotient.mk orbitRungSetoid p) :=
  (forkLikePos_mk p).mpr (forkState_forkLive h)

/-- **THE RUNG PIN AT THE POSITION LEVEL** — a fork witness forces both
twin-suit rungs to the pair's rank index.  This is a BFS-free necessary
condition for a fork at a Position: two twin suits at equal rung `r`
with the rank-`r` cards next-up. -/
theorem forkLikePos_rung_pin {p : WFState} {x : Card}
    (h : ForkWitness p.1 x) :
    rungsOf (Quotient.mk orbitRungSetoid p) x.suit = x.rank.toIdx ∧
      rungsOf (Quotient.mk orbitRungSetoid p) x.twin.suit = x.rank.toIdx := by
  obtain ⟨h1, h2⟩ := forkState_witness_rungs h
  exact ⟨h1, h2⟩

/-! ## §6. Audit -/

#print axioms canRaiseS_bareCargo_iff'
#print axioms ssaturated_bareCargo_iff
#print axioms bareCargo_rungs
#print axioms forkLive_bareCargo_iff
#print axioms armDichotomy_to_satDifferFork
#print axioms forkless_bareCargo_unique
#print axioms forkless_found_unique_via_fiber
#print axioms forkState_forkLikePos
#print axioms forkLikePos_rung_pin
