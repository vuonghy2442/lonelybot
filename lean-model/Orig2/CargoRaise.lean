import Orig2.Vocab
import Orig2.Classification
import Orig2.StepWF
import Orig2.FloatOrbit

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
for the well-formedness propagation, `Orig2.FloatOrbit` for the
cargo-orbit characterization); zero `sorry`, zero
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

/-! ## §3. The seat-diff readings (the wave's stage 4) -/

/-- A card seated `.inr` on a card parent is not a king.  Lineage:
`Archive/TwinFoundationRow.lean:180`, restated private at
`Orig2/FiberTransfer.lean:531`; re-landed here (the wave's card,
over the public CargoKit seat rows) rather than widening the
import surface to the fiber-transfer card. -/
private theorem seatOf_inr_rank_ne_king {s : State} {c r : Card}
    (hwf : s.WF) (hseat : seatOf s c = some (Sum.inr r)) :
    c.rank ≠ Rank.king := by
  obtain ⟨a, hhold, -, hlast⟩ := tfc_seatOf_of_inr hseat
  have hfit : canSitOn c r = true := (tfc_seat_parent hwf hhold hlast).1
  intro hking
  have hlt := ((canSitOn_eq c r).mp hfit).1
  have hidx : c.rank.toIdx = 12 := by rw [hking]; rfl
  have hlt' := Rank.toIdx_lt r.rank
  omega

/-- **THE COVER LEAVES ONLY TO THE TWIN** — within a bare-cargo
pair, a card seated on `c` at `st` that moves at all lands on
`c.twin`: the twin-carried clause of the split iff, read at the
`.inr` seat.  The mate-slide's rigidity, stated at the class
grade. -/
theorem bareCargo_cover_to {st w : State} (hwfst : st.WF) (hw : w.WF)
    (h : BareCargoEquiv st w) {y c : Card}
    (hy : seatOf st y = some (Sum.inr c))
    (hchg : seatOf st y ≠ seatOf w y) :
    seatOf w y = some (Sum.inr c.twin) := by
  obtain ⟨⟨-, hnon⟩, -⟩ := (bareCargo_iff_split hwfst hw).mp h
  have hk : y.rank ≠ Rank.king := seatOf_inr_rank_ne_king hwfst hy
  obtain ⟨z', hz1, hz2⟩ := hnon y hk hchg
  rw [hy] at hz1
  injection hz1 with hz1'
  injection hz1' with hz1''
  rw [← hz1''] at hz2
  exact hz2

/-- **THE ONLY ARRIVAL IS FROM THE TWIN** — within a bare-cargo
pair, a card seated on `c` at `w` that moved at all came from
`c.twin`: the twin-carried clause, reverse direction. -/
theorem bareCargo_cover_from {st w : State} (hwfst : st.WF) (hw : w.WF)
    (h : BareCargoEquiv st w) {y c : Card}
    (hy : seatOf w y = some (Sum.inr c))
    (hchg : seatOf st y ≠ seatOf w y) :
    seatOf st y = some (Sum.inr c.twin) := by
  obtain ⟨⟨hking, hnon⟩, -⟩ := (bareCargo_iff_split hwfst hw).mp h
  by_cases hk : y.rank = Rank.king
  · obtain ⟨a', hcon, -⟩ := hking y hk hchg
    rw [hcon] at hy
    exact absurd hy (by simp)
  · obtain ⟨z', hz1, hz2⟩ := hnon y hk hchg
    rw [hz2] at hy
    injection hy with hy'
    injection hy' with hy''
    have hz : z' = c.twin := by
      rw [← tfc_card_twin_twin z', hy'']
    rw [hz] at hz1
    exact hz1

/-- **THE MOVED COVER'S ORIGIN LICENSE IS THE TWIN-TOP
CONDITION** — a card seated on `c` that moves within the class
carries `FloaterSpec` at the origin, and for a non-king `.inr`
seat that license IS the company cell: the parent's twin tops
some pile.  This is the mutual lock's core, stated at the class
grade — the flat characterization's run-or-twin clause rides it. -/
theorem bareCargo_cover_license {st w : State} (hwfst : st.WF) (hw : w.WF)
    (h : BareCargoEquiv st w) {y c : Card}
    (hy : seatOf st y = some (Sum.inr c))
    (hchg : seatOf st y ≠ seatOf w y) :
    st.pileOfTop c.twin ≠ none := by
  obtain ⟨⟨hking, hnon⟩, hlic, hro⟩ := (bareCargo_iff_split hwfst hw).mp h
  have hk : y.rank ≠ Rank.king := seatOf_inr_rank_ne_king hwfst hy
  have hfsp : FloaterSpec st y := hlic y hchg
  unfold FloaterSpec at hfsp
  rcases hfsp with
    ⟨z, a₁, hz, hhold₁, hinner⟩ | ⟨a₂, hclash, hkk, hh, he⟩
  · rw [hy] at hz
    injection hz with hz'
    injection hz' with hz''
    rw [← hz''] at hinner
    rcases hinner with ⟨k, hk2⟩ | ⟨hk2, hke⟩
    · intro hcon
      rw [hcon] at hk2
      exact absurd hk2 (by simp)
    · exact absurd hk2 hk
  · rw [hclash] at hy
    exact absurd hy (by simp)

/-- **THE FOUNDATIONS ARE THE LICENSE'S PHASE** — within a
bare-cargo pair the vanilla `nextUp` read is preserved (the
`foundsFixed` readout; the {slide · raise} closure never leaves
its fiber). -/
theorem bareCargo_nextUp {st w : State} (hwfst : st.WF) (hw : w.WF)
    (h : BareCargoEquiv st w) {c : Card} :
    st.nextUp c = w.nextUp c := by
  obtain ⟨-, -, hro⟩ := (bareCargo_iff_split hwfst hw).mp h
  have hf : st.found = w.found := funext (fun s => hro.2.1 s)
  exact congrArg (fun (f : Suit → List Card) =>
    decide (c.rank.toIdx = (f c.suit).length)) hf

/-! ## §4. The battery -/

#print axioms canRaiseS_of_cargoPath
#print axioms cargoPath_of_canRaiseS
#print axioms canRaiseS_cargoPath_iff
#print axioms steps_trans
#print axioms cargoLeg_symm
#print axioms cargoPath_symm
#print axioms cargoPath_bareCargo
#print axioms canRaiseS_bareCargo_iff
#print axioms bareCargo_cover_to
#print axioms bareCargo_cover_from
#print axioms bareCargo_cover_license
#print axioms bareCargo_nextUp
