import Orig2.Vocab

/-!
# Orig2.CargoRaise — THE CARGO BRIDGE (the flat characterization's
migration wave, stage 2)

THE MISSION: `CanRaiseS` as CARGO-REACHABILITY OF A VANILLA RAISE —
the {slide · raise} closure is exactly the cargo path span:

  `CanRaiseS st c ↔ ∃ z, CargoPath st z ∧ CanRaise z c`

The via-leg IS `CargoLeg` by definition — the identical ∃-shape at
`Vocab`'s `CanRaiseS.via` and `CargoLeg` — so both directions are
structural inductions.  This is the bridge the flat
characterization's migration rides: with the cargo-orbit
characterization (`bareCargo_iff_vk` / `bareCargo_iff_split`,
`Orig2/FloatOrbit.lean`) the necessity direction of the frozen
`canRaiseS_iff` (`Orig/ForkStateS.lean:539`) becomes a SEAT-DIFF
READING rather than a path induction — the mutual lock, the
position engine, and the sufficiency construction all live inside
the certified orbit iff:

* the only cards that can come to sit on `c` within the class came
  from `c.twin` (the twin-carried clause);
* the cover of `c` can only leave to `c.twin` (the same clause);
* `nextUp` is `foundsFixed` (a clause of the iff, no induction);
* the mate-slide IS the iff's own sufficiency construction.

WAVE: this card's landing is the bridge (§1).  Staged next:
`cargoPath` symmetry (the leg inversion — the undo's
reversibility is `reversible_mirrorW`, only the undo-fires
construction remains), the seat-diff corollaries of
`bareCargo_iff_split`, the FloaterSpec ↔ twin-top correspondence,
then the flat iff and the decidability packaging (the `RankSat`
checker — Q9 of the campaign's question family).

House compliance: additive leaf (`Orig2.Vocab` only — the minimal
seam); zero `sorry`, zero `Classical.choice`; the battery at the
tail.
-/

/-! ## §1. The bridge -/

/-- **THE CARGO BRIDGE, REACHABILITY HALF** — a cargo path to a
state where the vanilla raise fires is already a maneuver-raise:
peel the legs one `via` at a time (the cargo letter and the
via-leg are the same ∃-shape). -/
theorem canRaiseS_of_cargoPath {st z : State} {c : Card}
    (hp : CargoPath st z) : CanRaise z c → CanRaiseS st c := by
  induction hp with
  | refl w => exact fun hcr => CanRaiseS.now c hcr
  | cons h t ih => exact fun hcr => CanRaiseS.via c h (ih hcr)

/-- **THE CARGO BRIDGE, WITNESS HALF** — a maneuver-raise deposits a
cargo path to a vanilla-raise state: the via-legs compose into the
path directly. -/
theorem cargoPath_of_canRaiseS {st : State} {c : Card}
    (h : CanRaiseS st c) : ∃ z, CargoPath st z ∧ CanRaise z c := by
  induction h with
  | @now st' _ hcr => exact ⟨st', Steps.refl st', hcr⟩
  | @via st st' _ hl _ ih =>
      obtain ⟨z, hp, hcr⟩ := ih
      exact ⟨z, Steps.cons hl hp, hcr⟩

/-- **THE CARGO BRIDGE** — the swap-aware license IS the cargo
span of the vanilla license: `CanRaiseS st c` exactly when some
cargo path reaches a state where `c` raises now.  The flat
characterization's migration base: every downstream question about
the S-license becomes a question about the cargo class. -/
theorem canRaiseS_cargoPath_iff {st : State} {c : Card} :
    CanRaiseS st c ↔ ∃ z, CargoPath st z ∧ CanRaise z c :=
  ⟨fun h => cargoPath_of_canRaiseS h,
    fun ⟨_, hp, hcr⟩ => canRaiseS_of_cargoPath hp hcr⟩

/-! ## §2. The battery -/

#print axioms canRaiseS_of_cargoPath
#print axioms cargoPath_of_canRaiseS
#print axioms canRaiseS_cargoPath_iff
