import Orig2.Fork.Class.ForkFibMeet
import Orig2.Fiber.LockRung

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-!
# Orig2/ForkMeetCover — `MeetConstancy` is a THEOREM given a fork at the meet

READ-ONLY scratch card (no `Orig2/` edit; nothing committed).  Zero `sorry`,
zero `Classical.choice`, zero `native_decide`; axiom battery at the tail.

## The result

`Orig2/Fork/Class/ForkFibMeet.lean` names three things:

* `MeetPositionForkLike` — the meet of a differing-rung saturated pair is
  fork-LIKE (its `Position` spectrum is exactly one twin pair, at the pair
  meet),
* `MeetConstancy` — at such a meet position EVERY same-orbit member is a FULL
  `forkState` (the report's ALL-FORK 13/13),
* `MeetFibreBlock` — the pointwise cover datum.

The counterexample sweep (`Temp/Meet_Report.md`: 2 327 components, 99 715
states, 11 243 differing-rung saturated pairs, 230 208 meet-position
member-states) reports

* pair meet `min(rungAt G σ) (rungAt H σ) = x.rank`: 11 243 / 11 243,
* ALL-FORK at every non-empty meet position: 11 064 / 11 064,
* at every such member EXACTLY ONE twin is covered: 230 208 / 230 208.

This card turns the second and third rows into a THEOREM, and in doing so
removes `MeetConstancy` from the critical path:

* **`forkState_of_same_position` (PROVED)** — the 13/13 ALL-FORK row, for ALL
  boards: at the `Position` of a `forkState`, every same-position member is a
  `forkState`.  The proof is the `LockRung` **cover token invariant**
  (`cover_token_invariant`): the card that blocks the fork's twin at `F` can
  only ever sit on `x` or `x.twin` for the rest of the orbit; combined with the
  local engine `canRaise_or_covered` (S-live + not covered ⇒ raisable) the pin
  is therefore never lost on the position's fibre.
* **`meetConstancy_of_forkAtMeet` (PROVED)** — `ForkAtMeet` (a `forkState`
  presenting the named pair AT the meet position) implies `MeetConstancy`.
* **`satDifferFork_of_forkAtMeet` (PROVED)** — `MeetPositionForkLike +
  ForkAtMeet ⇒ SatDifferFork`, hence the campaign theorem.
* **`not_pointwise_twinCover` (PROVED)** — the ungated pointwise form is FALSE
  (`BlockMin.gFin`): the meet hypothesis is load-bearing.

So the OPEN content is exactly the LOCATOR plus EXISTENCE: that the meet
position is fork-like with a `forkState` on it (`ForkAtMeet`, whose locator half
is `PairFloorLocal` + `PairMeetTight`).  `MeetConstancy` is not extra content.
-/

namespace MeetCoverTwo

open ForkFib

/-! ## §1. The local engine: spectrum + cover ⇒ fork state -/

/-- **THE SPECTRUM BRIDGE** — `ForkLiveAt` at a `Position` reads the
`CanRaiseS` spectrum of every representative of that position. -/
theorem forkLiveAt_twinLivePair {q : Position} {x : Card}
    (h : ForkLiveAt q x) {p : WFState}
    (hp : (Quotient.mk orbitRungSetoid p : Position) = q) :
    TwinLivePair p.1 x := by
  intro c
  have h1 : spec (Quotient.mk orbitRungSetoid p) c ↔ CanRaiseS p.1 c :=
    spec_mk p c
  rw [hp] at h1
  exact h1.symm.trans (h c).symm

/-- **A COVERED TWIN FORCES THE FORK STATE.**  With the exact twin-pair
spectrum in hand one covered twin is enough: the fork card is the other twin,
whose orientation pin is `¬ CanRaise` of the covered card. -/
theorem forkState_of_covered_twin {p : WFState} {x : Card}
    (hl : TwinLivePair p.1 x)
    (hcov : CoveredAt p.1 x ∨ CoveredAt p.1 x.twin) :
    forkState p.1 := by
  rcases hcov with hcov | hcov
  · refine forkState_iff.mpr ⟨x.twin, (forkWitness_iff p.1 x.twin).mpr ⟨?_, ?_⟩⟩
    · intro c
      rw [card_twin_twin]
      exact (hl c).trans or_comm
    · rw [card_twin_twin]
      exact not_canRaise_of_covered p.2 hcov
  · exact forkState_iff.mpr
      ⟨x, (forkWitness_iff p.1 x).mpr ⟨hl, not_canRaise_of_covered p.2 hcov⟩⟩

/-! ## §2. THE ALL-FORK ROW: the pin is constant on a fork's Position -/

/-- **THE COVER OF THE FORK'S TWIN NEVER LEAVES THE PAIR.**  (`LockRung`'s
`cover_token_invariant`, restated at the direction this card consumes.) -/
theorem fork_cover_on_pair {F : State} (hF : F.WF) {x : Card}
    (hx : ForkWitness F x) {p : WFState}
    (hcls : sameOrbitSetoid.r F p.1) :
    CoveredAt p.1 x ∨ CoveredAt p.1 x.twin := by
  have hl : TwinLivePair F x := fun c => (hx.1 c).symm
  have hyS : CanRaiseS F x.twin := (hx.1 x.twin).mp (Or.inr rfl)
  have hcov : CoveredAt F x.twin :=
    (forkWitness_iff_covered (y := x.twin) hF rfl hl hyS).mp hx
  obtain ⟨d, hd⟩ := hcov
  obtain ⟨-, _, play, hplay⟩ : RevEqW p.1 F := hcls
  have hseat := cover_token_invariant (x := x) (y := x.twin) (d := d)
    hF rfl hl hd hplay
  rcases hseat with hs | hs
  · exact Or.inl ⟨d, hs⟩
  · exact Or.inr ⟨d, hs⟩

/-- **FORK-POSITION CONSTANCY (the 13/13 ALL-FORK row, for ALL boards).**  At
the `Position` of a `forkState`, every same-position member is a `forkState`.

Proof: the fork's blocked twin is covered at `F` (`forkWitness_iff_covered`);
the cover token invariant keeps that cover on `x` or `x.twin` across the whole
orbit; the spectrum is positional; and `canRaise_or_covered` turns the covered
twin into the pin. -/
theorem forkState_of_same_position {F : State} (hF : F.WF) {x : Card}
    (hx : ForkWitness F x) {p : WFState}
    (hpos : (Quotient.mk orbitRungSetoid p : Position) =
      (Quotient.mk orbitRungSetoid ⟨F, hF⟩)) :
    forkState p.1 := by
  have hposr : orbitRungSetoid.r p ⟨F, hF⟩ := Quotient.exact hpos
  have hcls : sameOrbitSetoid.r F p.1 :=
    sameOrbitSetoid.iseqv.symm hposr.1
  have hcovP : CoveredAt p.1 x ∨ CoveredAt p.1 x.twin :=
    fork_cover_on_pair hF hx hcls
  have hlP : TwinLivePair p.1 x := by
    intro c
    have h1 : spec (Quotient.mk orbitRungSetoid p) c ↔ CanRaiseS p.1 c :=
      spec_mk p c
    have h2 : spec (Quotient.mk orbitRungSetoid ⟨F, hF⟩) c ↔ CanRaiseS F c :=
      spec_mk ⟨F, hF⟩ c
    rw [hpos] at h1
    exact (h1.symm.trans h2).trans (hx.1 c).symm
  exact forkState_of_covered_twin hlP hcovP

/-! ## §3. `MeetConstancy` from a fork AT the meet -/

/-- **`ForkAtMeet` — THE REMAINING OBLIGATION, AND IT IS A LOCATOR.**  At the
pair-meet position of a differing-rung saturated pair, there is a `forkState`
in `u`'s orbit presenting the SAME named twin pair `x`, sitting AT that
position.

Empirically this is the 11 064 / 11 064 row of `Temp/Meet_Report.md`.  Its two
halves are `PairFloorLocal + PairMeetTight` (the locator, `Orig2/Fork/Class/ForkFibMeet.lean`
§1) plus "a fork exists at that position". -/
def ForkAtMeet : Prop :=
  ∀ (u v : State) (x : Card) (q : Position),
    SSaturated u → SSaturated v → sameOrbitSetoid.r u v →
    (∃ σ : Suit, rungAt u σ ≠ rungAt v σ) →
    PairMeetAt q u v x → ForkLiveAt q x →
    ∃ (F : State) (hF : F.WF),
      sameOrbitSetoid.r u F ∧ ForkWitness F x ∧
        (Quotient.mk orbitRungSetoid ⟨F, hF⟩ : Position) = q

/-- **`ForkAtMeet` IMPLIES `MeetConstancy`** — the constancy conjecture is not
extra content: it is the cover token invariant plus §2. -/
theorem meetConstancy_of_forkAtMeet (hf : ForkAtMeet) : MeetConstancy := by
  intro u v x q hsu hsv hcls hdiff hmeet hfl p hp _hpu
  obtain ⟨F, hF, _hclsF, hx, hFpos⟩ :=
    hf u v x q hsu hsv hcls hdiff hmeet hfl
  have hpos : (Quotient.mk orbitRungSetoid p : Position) =
      (Quotient.mk orbitRungSetoid ⟨F, hF⟩) := by
    rw [hp, hFpos]
  exact forkState_of_same_position hF hx hpos

/-- **THE CAMPAIGN RESIDUE FROM THE LOCATOR.**  `MeetPositionForkLike +
ForkAtMeet ⇒ SatDifferFork`. -/
theorem satDifferFork_of_forkAtMeet
    (hM : MeetPositionForkLike) (hf : ForkAtMeet) : SatDifferFork :=
  satDifferFork_of_meetConstancy hM (meetConstancy_of_forkAtMeet hf)

/-- **THE CAMPAIGN THEOREM FROM THE LOCATOR.** -/
theorem forkless_found_unique_of_forkAtMeet
    (hM : MeetPositionForkLike) (hf : ForkAtMeet)
    {s s' : State} (hwf : s.WF) (hwf' : s'.WF)
    (hclass : sameOrbitSetoid.r s s')
    (hfrk : ∀ u, sameOrbitSetoid.r s u → ¬ forkState u)
    (hsat : SSaturated s) (hsat' : SSaturated s') :
    s.found = s'.found :=
  forkless_found_unique_of_meet hM (meetConstancy_of_forkAtMeet hf)
    hwf hwf' hclass hfrk hsat hsat'

/-! ## §4. The cover residual (the weaker, pointwise split) -/

/-- **`MeetTwinCover` — THE COVER RESIDUAL AT A PAIR-MEET POSITION.**  Weaker
than `MeetConstancy` (it asks for the cover datum, not the pin). -/
def MeetTwinCover : Prop :=
  ∀ (u v : State) (x : Card) (q : Position) (p : WFState),
    SSaturated u → SSaturated v → sameOrbitSetoid.r u v →
    (∃ σ : Suit, rungAt u σ ≠ rungAt v σ) →
    PairMeetAt q u v x → ForkLiveAt q x →
    (Quotient.mk orbitRungSetoid p : Position) = q →
      CoveredAt p.1 x ∨ CoveredAt p.1 x.twin

/-- `MeetTwinCover` implies `MeetConstancy` (via §1). -/
theorem meetConstancy_of_meetTwinCover (hcov : MeetTwinCover) : MeetConstancy := by
  intro u v x q hsu hsv hcls hdiff hmeet hfl p hp _hpu
  exact forkState_of_covered_twin (forkLiveAt_twinLivePair hfl hp)
    (hcov u v x q p hsu hsv hcls hdiff hmeet hfl hp)

/-! ## §5. The gate is load-bearing (the ungated cover form is FALSE) -/

/-- The twin names agree (`5H.twin = 5D`), recorded so the next row reads. -/
theorem H5_twin : BlockMin.H5.twin = BlockMin.D5 := rfl

/-- **THE POINTWISE COVER FORM IS FALSE.**  `BlockMin.gFin` has the exact
twin-pair spectrum `{5H, 5D}` and NEITHER twin covered — so the cover cannot be
won pointwise, only at a meet position.  This is the kernel shadow of the 833
non-meet fork-live positions carrying a non-fork member in the sweep. -/
theorem not_pointwise_twinCover :
    ¬ (∀ (p : WFState) (x : Card), TwinLivePair p.1 x →
        CoveredAt p.1 x ∨ CoveredAt p.1 x.twin) := by
  intro h
  have hboth := h ⟨BlockMin.gFin, BlockMin.gFin_wf⟩ BlockMin.H5
    BlockMin.gFin_twinLivePair
  rcases hboth with h1 | h1
  · exact BlockMin.gFin_H5_not_covered h1
  · exact BlockMin.gFin_D5_not_covered (H5_twin ▸ h1)

end MeetCoverTwo

/-! ## §6. Axiom battery -/

#print axioms MeetCoverTwo.forkLiveAt_twinLivePair
#print axioms MeetCoverTwo.forkState_of_covered_twin
#print axioms MeetCoverTwo.fork_cover_on_pair
#print axioms MeetCoverTwo.forkState_of_same_position
#print axioms MeetCoverTwo.meetConstancy_of_forkAtMeet
#print axioms MeetCoverTwo.satDifferFork_of_forkAtMeet
#print axioms MeetCoverTwo.forkless_found_unique_of_forkAtMeet
#print axioms MeetCoverTwo.meetConstancy_of_meetTwinCover
#print axioms MeetCoverTwo.not_pointwise_twinCover
#print axioms MeetCoverTwo.H5_twin

#check @MeetCoverTwo.ForkAtMeet
#check @MeetCoverTwo.MeetTwinCover
