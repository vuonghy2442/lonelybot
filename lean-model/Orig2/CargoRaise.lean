import Orig2.Vocab
import Orig2.Classification
import Orig2.StepWF

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

House compliance: additive leaf (`Orig2.Vocab` +
`Orig2.Classification` for the public mirror row, `Orig2.StepWF`
for the well-formedness propagation); zero `sorry`, zero
`Classical.choice`; the battery at the tail.
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

/-! ## §2. The leg inversion (the wave's stage 3) -/

/-- **STEPS TRANSITIVITY** — path concatenation: a path to `z` then
a path from `z` lands at `u`.  The generic closure the reversal
composes through. -/
theorem steps_trans {Q : State → State → Prop} {w z u : State}
    (h₁ : Steps Q w z) : Steps Q z u → Steps Q w u := by
  induction h₁ with
  | refl _ => exact fun h₂ => h₂
  | cons h _ ih => exact fun h₂ => Steps.cons h (ih h₂)

/-- **THE LEG INVERSION** — at `WF`, every cargo leg has a mirror
leg: the reversible slide's moved run relocates back whole.  The
mirror's EXISTENCE is the classification's public `tabToTab_mirror`
(stage 3's one public extraction — the undo rows' conclusions were
strengthened to expose the firing); the mirror's own reversibility
is `reversible_mirrorW` over the two firings. -/
theorem cargoLeg_symm {a b : State} (hwf : a.WF) (h : CargoLeg a b) : CargoLeg b a := by
  obtain ⟨c, b', hfire, hrev⟩ := h
  obtain ⟨b₂, hfire2⟩ := tabToTab_mirror hwf hfire hrev
  exact ⟨c, b₂, hfire2, reversible_mirrorW hfire2 hfire⟩

/-- **THE CARGO PATH IS SYMMETRIC** — at `WF`, one-way cargo
reachability is two-way: reverse the legs one mirror at a time,
propagating well-formedness through each firing. -/
theorem cargoPath_symm {a b : State} (hwf : a.WF) (h : CargoPath a b) : CargoPath b a := by
  revert hwf
  induction h with
  | refl _ => exact fun _ => Steps.refl _
  | @cons w z u hleg t ih =>
      intro hwf
      obtain ⟨c, b', hfire, hrev⟩ := hleg
      exact steps_trans (ih (step_wf hwf hfire))
        (Steps.cons (cargoLeg_symm hwf ⟨c, b', hfire, hrev⟩) (Steps.refl w))

/-- **ONE-WAY IS TWO-WAY** — at `WF`, cargo reachability IS the
bare cargo equivalence: the bridge's existential reads directly on
the orbit characterization's currency. -/
theorem cargoPath_bareCargo {a b : State} (hwf : a.WF) (h : CargoPath a b) :
    BareCargoEquiv a b := ⟨h, cargoPath_symm hwf h⟩

/-- **THE BRIDGE, BARE-CARGO FORM** — the swap-aware license reads
on the orbit characterization's currency: some bare-cargo mate of
`st` raises `c` now.  Stage 4 (the seat-diff readings of
`bareCargo_iff_split`) picks up exactly here. -/
theorem canRaiseS_bareCargo_iff {st : State} (hwf : st.WF) {c : Card} :
    CanRaiseS st c ↔ ∃ z, BareCargoEquiv st z ∧ CanRaise z c := by
  rw [canRaiseS_cargoPath_iff]
  constructor
  · rintro ⟨z, hp, hcr⟩
    exact ⟨z, ⟨hp, cargoPath_symm hwf hp⟩, hcr⟩
  · rintro ⟨z, ⟨hp, -⟩, hcr⟩
    exact ⟨z, hp, hcr⟩

/-! ## §3. The battery -/

#print axioms canRaiseS_of_cargoPath
#print axioms cargoPath_of_canRaiseS
#print axioms canRaiseS_cargoPath_iff
#print axioms steps_trans
#print axioms cargoLeg_symm
#print axioms cargoPath_symm
#print axioms cargoPath_bareCargo
#print axioms canRaiseS_bareCargo_iff
