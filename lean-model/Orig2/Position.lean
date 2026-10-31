import Orig2.StratifiedQuotient
import Orig2.FreeOrbit

/-!
# Orig2.Position - THE GAME-POSITION QUOTIENT (the grid card)

THE MISSION (the owner's grid program, opened 2026-10-31): quotient
the game by the free-card orbit campaign's invariant.  The campaign
certified that the S-license is an (orbit, rung-tuple) invariant
(`canRaiseS_orbit_rung`, `Orig2/FreeOrbit.lean` par.5): at equal
rungs, orbit-mates share every card's license - the possible
`tabToFound` moves cannot tell them apart.  This card makes that
literal.

THE SHAPE: the game fibers over the four-dimensional rung grid.
Within a fiber, the reversible moves are the quotient's own glue -
they vanish; the raises are the grid's deterministic edges (+e_suit),
the pulls their mirrors (-e_suit).  Because raises are reversible,
orbits CROSS rungs - so the position is the MEET of the macro class
and the ledger: orbit-mates at equal rungs.

* **par.1 THE SETOID** - `RungEq` (the ledger equality), `WFState`
(the arena - the respect proofs need the run discipline), and
`orbitRungSetoid` (the meet).
* **par.2 THE QUOTIENT** - `Position` (the grid's vertex space).
* **par.3 THE DESCENT** - `rungsOf`, `foundsOf`, and `spec` (the
license spectrum: the possible `tabToFound` moves as a
position-function - the campaign theorem's respect proof), with its
flat probe `specB`.
* **par.4 THE SOUNDNESS** - the spectrum can't tell representatives
apart (`spec_sound`, via `Quotient.sound`); the probe reads the
spectrum (`specB_iff`).
* **par.9 THE BATTERY**.

THE NEXT SITTINGS: the rung-step arithmetic (raise +e_suit, pull
-e_suit, free moves 0), the free moves' vanishing, and the raise's
class-determinism (the pull-back + orbit-walk + raise concatenation)
- then the residue campaign runs on the grid.
-/

/-! ## par.1. The setoid -/

/-- **RungEq s s'** - the ledger equality: every suit's foundation
rung agrees. -/
abbrev RungEq (s s' : State) : Prop := ∀ σ, rungAt s σ = rungAt s' σ

/-- **orbitRungSetoid** - THE GAME-POSITION EQUIVALENCE: orbit-mates
at equal rungs.  The meet of the macro class (`sameOrbitSetoid`) and
the ledger (`RungEq`) - the orbit alone would collapse the
foundation progress (raises are reversible), the rungs alone would
not glue the orbit's free rearrangements.  The carrier is
`StratifiedQuotient`'s `WFState` (the same arena, per the kit rule:
the stratified twin-membership meet and this rung meet share it). -/
instance orbitRungSetoid : Setoid WFState where
  r p p' := sameOrbitSetoid.r p.1 p'.1 ∧ RungEq p.1 p'.1
  iseqv :=
    ⟨fun p => ⟨sameOrbitSetoid.iseqv.refl p.1, fun _ => rfl⟩,
     fun ⟨h1, h2⟩ => ⟨sameOrbitSetoid.iseqv.symm h1, fun σ => (h2 σ).symm⟩,
     fun ⟨h1, h2⟩ ⟨h1', h2'⟩ =>
       ⟨sameOrbitSetoid.iseqv.trans h1 h1', fun σ => (h2 σ).trans (h2' σ)⟩⟩

/-! ## par.2. The quotient -/

/-- **Position** - the game's position space: well-formed states
modulo orbit-mates-at-equal-rungs.  The grid's vertices. -/
abbrev Position := Quotient orbitRungSetoid

/-! ## par.3. The descent -/

/-- Bool equality from iff-of-true (the flat-probe bridge). -/
private theorem bool_eq_of_iff_true {a b : Bool} (h : (a = true) ↔ (b = true)) :
    a = b := by
  cases a with
  | false =>
      cases b with
      | false => rfl
      | true => exact h.mpr rfl
  | true =>
      cases b with
      | false => exact (h.mp rfl).symm
      | true => rfl

/-- **rungsOf** - the grid coordinate: the position's rung vector
(every suit's founded count).  The respect is the meet's ledger
component. -/
def rungsOf : Position → Suit → Nat :=
  Quotient.lift (fun p σ => rungAt p.1 σ) (fun _ _ h => funext h.2)

/-- **foundsOf** - the foundations: equal rungs force equal founds
(the take-prefix discipline, `found_congr_of_rungs`). -/
def foundsOf : Position → Suit → List Card :=
  Quotient.lift (fun p => p.1.found)
    (fun p p' h => funext fun σ => found_congr_of_rungs p.2 p'.2 (h.2 σ))

/-- **spec** - THE LICENSE SPECTRUM: the possible `tabToFound` moves
as a function of the position.  The respect proof IS the campaign's
theorem (`canRaiseS_orbit_rung`), descended through `propext`. -/
def spec : Position → Card → Prop :=
  Quotient.lift (fun p c => CanRaiseS p.1 c)
    (fun p _p' h => funext fun _c => propext (canRaiseS_orbit_rung p.2 h.1 h.2))

/-- **specB** - the spectrum's flat probe: the campaign's decidable
checker, descended. -/
def specB : Position → Card → Bool :=
  Quotient.lift (fun p => canRaiseSB p.1)
    (fun p p' h => funext fun _c =>
      bool_eq_of_iff_true (by
        rw [canRaiseSB_iff p.2, canRaiseSB_iff p'.2]
        exact canRaiseS_orbit_rung p.2 h.1 h.2))

/-! ## par.4. The soundness -/

/-- The spectrum reads any representative's license (the lift's
defining equation). -/
theorem spec_mk (p : WFState) (c : Card) :
    spec (Quotient.mk orbitRungSetoid p) c ↔ CanRaiseS p.1 c := Iff.rfl

/-- The flat probe reads any representative's computation. -/
theorem specB_mk (p : WFState) (c : Card) :
    specB (Quotient.mk orbitRungSetoid p) c = canRaiseSB p.1 c := rfl

/-- The rung vector reads any representative's rungs. -/
theorem rungsOf_mk (p : WFState) (σ : Suit) :
    rungsOf (Quotient.mk orbitRungSetoid p) σ = rungAt p.1 σ := rfl

/-- The foundations read any representative's founds. -/
theorem foundsOf_mk (p : WFState) (σ : Suit) :
    foundsOf (Quotient.mk orbitRungSetoid p) σ = p.1.found σ := rfl

/-- **THE SPECTRUM CAN'T TELL REPRESENTATIVES APART** - the possible
`tabToFound` moves are a function of the position: the campaign's
theorem, now as the quotient's soundness. -/
theorem spec_sound {p p' : WFState} (h : orbitRungSetoid.r p p') (c : Card) :
    spec (Quotient.mk orbitRungSetoid p) c ↔
      spec (Quotient.mk orbitRungSetoid p') c := by
  rw [Quotient.sound h]

/-- The flat probe computes the spectrum. -/
theorem specB_iff {q : Position} {c : Card} :
    specB q c = true ↔ spec q c := by
  refine Quotient.inductionOn q (fun p => ?_)
  rw [specB_mk, spec_mk]
  exact canRaiseSB_iff p.2

/-! ## par.9. The battery -/

#print axioms rungsOf
#print axioms foundsOf
#print axioms spec
#print axioms specB
#print axioms spec_sound
#print axioms specB_iff
