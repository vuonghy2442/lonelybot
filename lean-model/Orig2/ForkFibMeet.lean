import Orig2.ForkThirdHigh
import Orig2.ForkDipPin
import Orig2.ForkPinAt

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-!
# Orig2/ForkFibMeet — the fork-at-the-meet bridge, assembled honestly

READ-ONLY scratch card (no `Orig2/` edit; nothing committed).  Zero `sorry`,
zero `Classical.choice`, zero `native_decide`; the axiom battery is at the tail.

## What is PROVED here

* **§1 the pair meet, conditional on its two named obligations.**
  `fork_at_the_meet_of_parts` states the report's `fork_pair_meet` — the fork's
  OWN PAIR columns (`x.suit`, `x.twin.suit`) sit at the pairwise minimum of the
  two differing saturated endpoints — with the two obligations supplied as
  hypotheses:
  * `PairFloorLocal` (the `≤` half; `Orig2/ForkFloor.lean`'s residual,
    rank 0 and 1 proved, `k ≥ 2` open) and
  * `PairMeetTight` (the `≥` / tightness half; OPEN, a `def`, not a theorem).
  The full-vector version is FALSE (7/13 census components carry a hearts gap
  strictly below the componentwise min); only the fork's pair suits are exact.
  `RungDiffers` is genuinely needed (the equal-rung stratum has the fork strictly
  below the pair min too, `Temp/EqualRung_Report.md`).

* **§3 the positional dichotomy.**  `FreeOrbit.canRaiseS_orbit_rung` makes the
  S-spectrum — hence `ForkLive` / `forkLikePos` — a function of the
  `Position`.  On a same-position fibre the fork-or-not dichotomy is therefore
  positional: every `ForkWitness` state presents a fork-like position, and no
  fork state lives at a position whose spectrum is not a twin pair.

* **§4 the GATED existential iff.**  With the pointwise fibre datum
  `BlockMin.FibreBlockData` at a representative,
  `forkLikePos position ↔ ∃ same-position member that is a fork state`.
  The forward direction is `BlockMin.exists_blocked_twin_of_data` (the fibre pin
  turns fork-likeness into a witness at a same-position mate); the reverse is
  `forkState_forkLikePos`.  The gate is NOT removable: it is FALSE at
  `BlockMin.gFin` (`BlockMin.gFin_not_fibreBlockData`).

## What is CONJECTURE (stated as `def`s, NOT proved)

* `MeetPositionForkLike` — at the meet of a differing-rung saturated pair, the
  position is fork-like (the bridge target; the locator half is §1's content).
* `MeetConstancy` — at meet positions the pin is fibre-constant: every member
  of the position is a FULL `forkState` (the census reads ALL-FORK 13/13 at
  every member of every fork position).  The UNGATED form is FALSE: the
  `Temp/TwinPin_Report.md` two-move gadget's end state `BlockMin.gFin` is `WF`,
  fork-like (`{5H,5D}`), both twins vanilla-raisable and no ready blocker, so it
  is fork-like but not a fork state (`not_forkLikePos_implies_forkState`, §5).
* `MeetFibreBlock` — the provable gate read at the meet; with it (and WITHOUT
  the constancy conjecture) the proved existential closes the campaign.

## The client chain

```text
MeetPositionForkLike + MeetConstancy      -> SatDifferFork   (§6, constancy route)
MeetPositionForkLike + MeetFibreBlock     -> SatDifferFork   (§6, data route)
SatDifferFork           -> SatDifferForkWF                   (drop the WF binder)
SatDifferForkWF -> CeilingBridge.forkless_found_unique_wf    (the campaign theorem)
```
-/

namespace ForkFib

open BlockMin

/-! ## §1. The meet of a differing saturated pair (the fork's own pair suits) -/

/-! ### 1a. The floor obligation, copied from `Orig2/ForkFloor.lean`

The two definitions and the two rows below are verbatim copies of the GREEN
part of `Orig2/ForkFloor.lean` §3 (`PairFloorLocalAt`, `PairFloorLocal`,
`floor_coordinate`, `fork_pair_floor_of_local`).  They are copied rather than
imported because `Temp/` cards are not a Lake library; the copy is
kernel-identical. -/

/-- **THE LOCAL RESIDUAL AT ONE RANK (`PairFloorLocalAt`).**  At a `WF`,
S-saturated `G` in the class of the fork `F`, no card `c` of a pair suit, of
rank index exactly `k < r`, that is founded at `F`, can be next-up AND
supported at `G`.  (`Orig2/ForkFloor.lean:127`.) -/
def PairFloorLocalAt (F : State) (x : Card) (k : Nat) : Prop :=
  ∀ (G : State) (c : Card), G.WF → SSaturated G → sameOrbitSetoid.r F G →
    (c.suit = x.suit ∨ c.suit = x.twin.suit) →
    c.rank.toIdx = k → k < x.rank.toIdx →
    c ∈ F.found c.suit →
    G.nextUp c = true → ¬ ThirdHigh.Supported G c

/-- **`PairFloorLocal`** — the floor obligation: `PairFloorLocalAt` at every
rank below the fork rank (`Orig2/ForkFloor.lean:135`). -/
def PairFloorLocal (F : State) (x : Card) : Prop :=
  ∀ k : Nat, PairFloorLocalAt F x k

/-- **THE PER-COORDINATE EXODUS LEMMA** (verbatim,
`Orig2/ForkFloor.lean:146`). -/
theorem floor_coordinate {F G : State} {x : Card} {σ : Suit}
    (hF : F.WF) (hG : G.WF) (hcls : sameOrbitSetoid.r F G)
    (hx : ForkWitness F x) (hsat : SSaturated G)
    (hσ : σ = x.suit ∨ σ = x.twin.suit)
    (hrF : rungAt F σ = x.rank.toIdx)
    (hloc : PairFloorLocal F x) :
    rungAt F σ ≤ rungAt G σ := by
  refine Nat.le_of_not_lt ?_
  intro hcon
  have hlt : rungAt G σ < x.rank.toIdx := by omega
  have hr13 : rungAt G σ < 13 := by
    have h := Rank.toIdx_lt x.rank
    omega
  let c : Card := ⟨σ, FoundKit.Rk (rungAt G σ)⟩
  have hcidx : c.rank.toIdx = rungAt G σ := FoundKit.Rk_toIdx _ hr13
  have hcsuit : c.suit = σ := rfl
  have hcF : c ∈ F.found c.suit := by
    apply FoundKit.mem_found_of_rung hF
    rw [hcidx, hcsuit, hrF]
    exact hlt
  have hcG : c ∉ G.found c.suit := by
    intro hmem
    have h := (FoundKit.mem_found_iff_height hG).mp hmem
    rw [hcidx] at h
    exact Nat.lt_irrefl _ h
  have hnext : G.nextUp c = true := by
    unfold State.nextUp State.foundHeight
    rw [hcidx]
    exact decide_eq_true rfl
  have hsup : ThirdHigh.Supported G c := by
    obtain ⟨-, -, play, hplay⟩ := hcls
    exact ThirdHigh.supported_of_forked_transit hF hplay (by
      intro hk
      have hk' : c.rank.toIdx = 12 := by rw [hk]; rfl
      have h12 := Rank.toIdx_lt x.rank
      omega) hcF hcG
  exact hloc (rungAt G σ) G c hG hsat hcls
    (by rcases hσ with h | h; exact Or.inl (by rw [hcsuit, h]); exact Or.inr (by rw [hcsuit, h]))
    hcidx hlt hcF hnext hsup

/-- **THE PAIR FLOOR FROM THE LOCAL RESIDUAL** (verbatim,
`Orig2/ForkFloor.lean:188`). -/
theorem fork_pair_floor_of_local {F G : State} {x : Card}
    (hF : F.WF) (hG : G.WF) (hcls : sameOrbitSetoid.r F G)
    (hx : ForkWitness F x) (hsat : SSaturated G) (hloc : PairFloorLocal F x) :
    rungAt F x.suit ≤ rungAt G x.suit ∧
      rungAt F x.twin.suit ≤ rungAt G x.twin.suit := by
  constructor
  · exact floor_coordinate hF hG hcls hx hsat (Or.inl rfl)
      (forkState_witness_rungs hx).1 hloc
  · exact floor_coordinate hF hG hcls hx hsat (Or.inr rfl)
      (forkState_witness_rungs hx).2 hloc

/-! ### 1b. The tightness obligation (OPEN; named, NOT proved) -/

/-- **`PairMeetTight` — THE TIGHTNESS HALF OF `fork_pair_meet`.**
The fork is not STRICTLY below the meeting level on its own pair suits:

```text
min (rungAt G x.suit) (rungAt H x.suit)          ≤ x.rank.toIdx
min (rungAt G x.twin.suit) (rungAt H x.twin.suit) ≤ x.rank.toIdx
```

This is the `≥` direction of `fork_pair_meet` (the `≤` direction is
`PairFloorLocal` above).  It is OPEN: the census certifies it 13/13, and the
first-passage "at the rung exactly" is the intended mechanism, but no proof
exists.  Scope note: only the fork's PAIR SUITS are pinned; the full-vector
version is FALSE (7/13 components carry a non-pair gap, always hearts, e.g.
`B_reloc6H min (6,0,2,2) fork (3,0,2,2)`). -/
def PairMeetTight : Prop :=
  ∀ (F G H : State) (x : Card), F.WF → G.WF → H.WF →
    sameOrbitSetoid.r F G → sameOrbitSetoid.r F H →
    ForkWitness F x → SSaturated G → SSaturated H →
    (∃ σ : Suit, rungAt G σ ≠ rungAt H σ) →
    min (rungAt G x.suit) (rungAt H x.suit) ≤ x.rank.toIdx ∧
      min (rungAt G x.twin.suit) (rungAt H x.twin.suit) ≤ x.rank.toIdx

/-- **`fork_at_the_meet_of_parts` — THE DROP-IN, WITH ITS TWO OBLIGATIONS.**
Do NOT read this as a theorem about the meet: it is the conditional assembly
`PairFloorLocal + PairMeetTight → fork_pair_meet`.  Both hypotheses are named
above; neither is proved.  `RungDiffers` is a genuine hypothesis (the equal-rung
stratum has the fork below the pair min). -/
theorem fork_at_the_meet_of_parts {F G H : State} {x : Card}
    (hF : F.WF) (hG : G.WF) (hH : H.WF)
    (hFG : sameOrbitSetoid.r F G) (hFH : sameOrbitSetoid.r F H)
    (hx : ForkWitness F x) (hsG : SSaturated G) (hsH : SSaturated H)
    (hdiff : ∃ σ : Suit, rungAt G σ ≠ rungAt H σ)
    (hfloor : PairFloorLocal F x) (htight : PairMeetTight) :
    x.rank.toIdx = min (rungAt G x.suit) (rungAt H x.suit) ∧
      x.rank.toIdx = min (rungAt G x.twin.suit) (rungAt H x.twin.suit) := by
  have hpair := forkState_witness_rungs hx
  obtain ⟨hG1, hG2⟩ := fork_pair_floor_of_local hF hG hFG hx hsG hfloor
  obtain ⟨hH1, hH2⟩ := fork_pair_floor_of_local hF hH hFH hx hsH hfloor
  obtain ⟨ht1, ht2⟩ := htight F G H x hF hG hH hFG hFH hx hsG hsH hdiff
  constructor
  · exact Nat.le_antisymm
      ((Nat.le_min).mpr ⟨by rw [← hpair.1]; exact hG1,
        by rw [← hpair.1]; exact hH1⟩) ht1
  · exact Nat.le_antisymm
      ((Nat.le_min).mpr ⟨by rw [← hpair.2]; exact hG2,
        by rw [← hpair.2]; exact hH2⟩) ht2

/-- The `≤` half of the pair meet, at the same hypotheses (this one is
UNCONDITIONAL given `PairFloorLocal`): the fork's pair rank is at most the
pairwise minimum. -/
theorem fork_pair_rank_le_meet {F G H : State} {x : Card}
    (hF : F.WF) (hG : G.WF) (hH : H.WF)
    (hFG : sameOrbitSetoid.r F G) (hFH : sameOrbitSetoid.r F H)
    (hx : ForkWitness F x) (hsG : SSaturated G) (hsH : SSaturated H)
    (hfloor : PairFloorLocal F x) :
    x.rank.toIdx ≤ min (rungAt G x.suit) (rungAt H x.suit) ∧
      x.rank.toIdx ≤ min (rungAt G x.twin.suit) (rungAt H x.twin.suit) := by
  have hpair := forkState_witness_rungs hx
  obtain ⟨hG1, hG2⟩ := fork_pair_floor_of_local hF hG hFG hx hsG hfloor
  obtain ⟨hH1, hH2⟩ := fork_pair_floor_of_local hF hH hFH hx hsH hfloor
  exact ⟨(Nat.le_min).mpr ⟨by rw [← hpair.1]; exact hG1,
      by rw [← hpair.1]; exact hH1⟩,
    (Nat.le_min).mpr ⟨by rw [← hpair.2]; exact hG2,
      by rw [← hpair.2]; exact hH2⟩⟩

/-! ## §2. The arm-dichotomy reduction (re-export of the proved row) -/

/-- The proved arm reduction (`Orig2/ArmFiber.lean:180`): the arm dichotomy —
which is NOT proved — implies the campaign residue.  Recorded so the exact
consumer is visible in this card; `ArmDichotomy` itself is the unproved input. -/
theorem armDichotomy_imp_satDifferFork (h : ArmDichotomy) : SatDifferFork :=
  armDichotomy_to_satDifferFork h

/-! ## §3. The positional dichotomy (PROVED) -/

/-- **THE SPECTRUM IS POSITIONAL** — same-position representatives agree on
`forkLikePos` (`FreeOrbit.canRaiseS_orbit_rung`, descended in `Position.spec`). -/
theorem forkLikePos_positional {p p' : WFState} (h : orbitRungSetoid.r p p') :
    forkLikePos (Quotient.mk orbitRungSetoid p) ↔
      forkLikePos (Quotient.mk orbitRungSetoid p') := by
  rw [Quotient.sound h]

/-- `ForkLive` (the state-level weak grade) is positional too. -/
theorem forkLive_positional {p p' : WFState} (h : orbitRungSetoid.r p p') :
    ForkLive p.1 ↔ ForkLive p'.1 := by
  rw [← forkLikePos_mk p, ← forkLikePos_mk p']
  exact forkLikePos_positional h

/-- **A FORK STATE CANNOT LIVE AT A NON-FORK-LIKE POSITION** — the
contrapositive of the proved detection implication. -/
theorem not_forkState_of_not_forkLikePos {p : WFState}
    (h : ¬ forkLikePos (Quotient.mk orbitRungSetoid p)) : ¬ forkState p.1 :=
  fun hf => h (forkState_forkLikePos hf)

/-- A `forkState` at one member certifies the position of every mate. -/
theorem forkState_implies_forkLikePos_mate {p q : WFState}
    (hcls : orbitRungSetoid.r p q) (hf : forkState p.1) :
    forkLikePos (Quotient.mk orbitRungSetoid q) :=
  (forkLikePos_positional hcls).mp (forkState_forkLikePos hf)

/-- **THE DICHOTOMY OF A FIBRE IS POSITIONAL.**  On a same-position fibre the
fork-or-not split is a function of the Position: fork-likeness is constant, a
fork state forces its mates' positions fork-like, and a non-fork-like position
carries no fork state at all.  (This is the positional content; it does NOT say
`forkLikePos -> forkState` — that fails pointwise, §5.) -/
theorem fibre_dichotomy_positional {p p' : WFState}
    (h : orbitRungSetoid.r p p') :
    (forkLikePos (Quotient.mk orbitRungSetoid p) ↔
      forkLikePos (Quotient.mk orbitRungSetoid p')) ∧
    (forkState p.1 → forkLikePos (Quotient.mk orbitRungSetoid p')) ∧
    (¬ forkLikePos (Quotient.mk orbitRungSetoid p) → ¬ forkState p'.1) :=
  ⟨forkLikePos_positional h,
    fun hf => forkState_implies_forkLikePos_mate h hf,
    fun hnf hf => hnf ((forkLikePos_positional h).mpr (forkState_forkLikePos hf))⟩

/-! ## §4. The gated existential iff (PROVED) -/

/-- **THE EXISTENTIAL IFF, GATED BY THE FIBRE PIN.**  At a representative whose
fibre carries `FibreBlockData`, being fork-like is exactly the existence of a
same-position member that is a FULL fork state.  Forward:
`BlockMin.forkWitness_of_data` (through `exists_blocked_twin_of_data`) produces
the blocked-twin representative; reverse: `forkState_forkLikePos` plus
position transport.

The gate is load-bearing, not cosmetic: it is FALSE at `BlockMin.gFin` (§5). -/
theorem forkLikePos_iff_exists_forkState_of_data (p : WFState)
    (hd : BlockMin.FibreBlockData p.1) :
    forkLikePos (Quotient.mk orbitRungSetoid p) ↔
      ∃ p' : WFState, orbitRungSetoid.r p p' ∧ forkState p'.1 := by
  constructor
  · intro hfl
    have hlive : ForkLive p.1 := (forkLikePos_mk p).mp hfl
    obtain ⟨x, hx⟩ := hlive
    have hl : TwinLivePair p.1 x := fun c => (hx c).symm
    obtain ⟨F', z, hrev, hrung, hfork⟩ :=
      BlockMin.forkWitness_of_data p.2 hd hl
    have hF' : F'.WF := by
      obtain ⟨σ, hσ, -⟩ := hrev
      exact walk_wf p.2 hσ
    refine ⟨⟨F', hF'⟩, ?_, forkState_iff.mpr ⟨z, hfork⟩⟩
    exact ⟨RevEqW_symm hrev, fun σ => (hrung σ).symm⟩
  · rintro ⟨p', hpos, hfs⟩
    exact (forkLikePos_positional hpos).mpr (forkState_forkLikePos hfs)

/-- The same iff read at a Position `q` (any representative presenting it). -/
theorem forkLikePos_iff_exists_forkState_of_position_data
    (q : Position) (p : WFState) (hq : (Quotient.mk orbitRungSetoid p : Position) = q)
    (hd : BlockMin.FibreBlockData p.1) :
    forkLikePos q ↔
      ∃ p' : WFState, (Quotient.mk orbitRungSetoid p' : Position) = q ∧
        forkState p'.1 := by
  rw [← hq]
  constructor
  · intro hfl
    obtain ⟨p', hpos, hfs⟩ :=
      (forkLikePos_iff_exists_forkState_of_data p hd).mp hfl
    exact ⟨p', (Quotient.sound hpos).symm, hfs⟩
  · rintro ⟨p', hp', hfs⟩
    exact (forkLikePos_iff_exists_forkState_of_data p hd).mpr
      ⟨p', Setoid.symm (Quotient.exact hp'), hfs⟩

/-! ## §5. The ungated form is FALSE: the `TwinPin` gadget (PROVED) -/

/-- `BlockMin.gFin`'s spectrum is the twin pair `{5H, 5D}` (the weak grade). -/
theorem gFin_forkLive : ForkLive BlockMin.gFin :=
  ⟨BlockMin.H5, fun c => (BlockMin.gFin_twinLivePair c).symm⟩

/-- `gFin`'s Position is fork-like. -/
theorem gFin_forkLike :
    forkLikePos (Quotient.mk orbitRungSetoid ⟨BlockMin.gFin, BlockMin.gFin_wf⟩) :=
  (forkLikePos_mk _).mpr gFin_forkLive

/-- `5H` is vanilla-raisable at `gFin` (not covered, so the S-licence raises). -/
theorem gFin_canRaise_H5 : CanRaise BlockMin.gFin BlockMin.H5 := by
  rcases canRaise_or_covered BlockMin.gFin_wf
    ((BlockMin.gFin_twinLivePair BlockMin.H5).mpr (Or.inl rfl)) with h | h
  · exact h
  · exact absurd h BlockMin.gFin_H5_not_covered

/-- `5D = 5H.twin` is vanilla-raisable at `gFin` as well. -/
theorem gFin_canRaise_D5 : CanRaise BlockMin.gFin BlockMin.D5 := by
  rcases canRaise_or_covered BlockMin.gFin_wf
    ((BlockMin.gFin_twinLivePair BlockMin.D5).mpr (Or.inr rfl)) with h | h
  · exact h
  · exact absurd h BlockMin.gFin_D5_not_covered

/-- **`gFin` IS FORK-LIKE BUT NOT A FORK STATE** — the `TwinPin` pointwise
counterexample to `forkLikePos -> forkState`.  Both twins are raisable, so the
orientation pin `¬ CanRaise x.twin` fails for whichever twin names the pair. -/
theorem gFin_not_forkState : ¬ forkState BlockMin.gFin := by
  rintro ⟨x, hspec, hpin⟩
  have hxS : CanRaiseS BlockMin.gFin x := (hspec x).mp (Or.inl rfl)
  have hx : x = BlockMin.H5 ∨ x = BlockMin.H5.twin :=
    (BlockMin.gFin_twinLivePair x).mp hxS
  rcases hx with hx | hx
  · rw [hx] at hpin
    exact hpin gFin_canRaise_D5
  · rw [hx] at hpin
    exact hpin (by simpa [card_twin_twin] using gFin_canRaise_H5)

/-- **THE UNGATED POINTWISE FORM IS FALSE.**  There is a `WF`, fork-like state
that is not a fork state, so `forkState` is not a function of `forkLikePos`
alone and the `forkState s <-> forkState s'` reading cannot be stated globally.
This is exactly why `MeetConstancy` below is gated at meet positions. -/
theorem not_forkLikePos_implies_forkState :
    ¬ (∀ (p : WFState),
        forkLikePos (Quotient.mk orbitRungSetoid p) → forkState p.1) := by
  intro h
  exact gFin_not_forkState
    (h ⟨BlockMin.gFin, BlockMin.gFin_wf⟩ gFin_forkLike)

/-- The gate `FibreBlockData` is not removable either: it is FALSE at `gFin`. -/
theorem gFin_not_fibreBlockData : ¬ BlockMin.FibreBlockData BlockMin.gFin :=
  BlockMin.gFin_not_fibreBlockData

/-! ## §6. The bridge: meet positions, constancy, and the reduction -/

/-- **`ForkLiveAt q x` — THE NAMED TWIN-PAIR SPECTRUM AT A POSITION.**  The
position's S-spectrum is exactly `{x, x.twin}`.  This is the per-pair spelling
of `forkLikePos` (`forkLikePos_iff_exists_forkLiveAt`, definitional). -/
def ForkLiveAt (q : Position) (x : Card) : Prop :=
  ∀ c, (c = x ∨ c = x.twin) ↔ spec q c

/-- `forkLikePos` is the existential closure of `ForkLiveAt` (definitional). -/
theorem forkLikePos_iff_exists_forkLiveAt (q : Position) :
    forkLikePos q ↔ ∃ x, ForkLiveAt q x := Iff.rfl

/-- **`PairMeetAt q u v x` — THE PAIR-MEET LOCATOR READ AT A POSITION.**
On the fork's own twin pair the position's rungs are the pairwise minima of the
two differing saturated endpoints.  This is the Position-level spelling of §1's
`fork_pair_meet` (and nothing more: the full vector is not asserted). -/
def PairMeetAt (q : Position) (u v : State) (x : Card) : Prop :=
  rungsOf q x.suit = min (rungAt u x.suit) (rungAt v x.suit) ∧
    rungsOf q x.twin.suit = min (rungAt u x.twin.suit) (rungAt v x.twin.suit)

/-- **`MeetPositionForkLike` — THE BRIDGE TARGET (CONJECTURE-shaped, NOT proved).**

At the meet of a differing-rung pair of saturated same-orbit states there is a
representative `F` in `u`'s orbit whose Position `q` carries the SAME named twin
pair `x` that sits at the pair meet: the spectrum is exactly `{x, x.twin}`
(`ForkLiveAt q x`) and `q`'s rungs on `x.suit`/`x.twin.suit` are the pairwise
minima of the endpoints (`PairMeetAt q u v x`).  That is the report's
"`SatDifferFork` becomes: the differing pair's meet position is fork-like — one
position, one twin pair, one level".

Neither conjunct is proved here: the locator half is the `PairFloorLocal` /
`PairMeetTight` pair (§1, both open), and the fork-likeness half is the
existence of the fork at that position.  The census reads it 13/13. -/
def MeetPositionForkLike : Prop :=
  ∀ (u v : State), SSaturated u → SSaturated v → sameOrbitSetoid.r u v →
    (∃ σ : Suit, rungAt u σ ≠ rungAt v σ) →
    ∃ (F : State) (hF : F.WF) (x : Card),
      sameOrbitSetoid.r u F ∧
      ForkLiveAt (Quotient.mk orbitRungSetoid ⟨F, hF⟩) x ∧
      PairMeetAt (Quotient.mk orbitRungSetoid ⟨F, hF⟩) u v x

/-- **`MeetConstancy` — THE MEET-CONSTANCY CONJECTURE (13/13 data, NOT proved).**

At a meet position (a Position carrying `PairMeetAt` for a fork's own twin pair)
fork-likeness is CONSTANT: every same-orbit member of that Position is a FULL
`forkState`.  This is exactly the ungated `forkState s ↔ forkState s'` on the
fibre — but read only at meet positions, where the campaign needs it.

EVIDENCE: the `Temp/Sat_fork_probe.py` census reads ALL-FORK 13/13 — at every
fork's rung vector, every state of the class at that vector (group sizes 4–16)
is a full fork state; the source proves only that the SPECTRUM is positional
(`ForkLive` / `forkLikePos`, §3).

WHY THE GATE: the ungated statement is FALSE.  The `Temp/TwinPin_Report.md`
two-move gadget's end state `BlockMin.gFin` is `WF` with spectrum `{5H,5D}`, both
twins vanilla-raisable and no ready blocker; it is fork-like but NOT a fork state
(`not_forkLikePos_implies_forkState`, §5).  So `forkLikePos q → forkState` is not
a theorem, and neither is the global `forkState s ↔ forkState s'`.

STATUS: unproved.  If `MeetTest` finds a broader-board counterexample this def
is the false hypothesis and the bridge must be re-stated (the constancy route),
while the `MeetFibreBlock` route below survives. -/
def MeetConstancy : Prop :=
  ∀ (u v : State) (x : Card) (q : Position),
    SSaturated u → SSaturated v → sameOrbitSetoid.r u v →
    (∃ σ : Suit, rungAt u σ ≠ rungAt v σ) →
    PairMeetAt q u v x → ForkLiveAt q x →
    ∀ (p : WFState), (Quotient.mk orbitRungSetoid p : Position) = q →
      sameOrbitSetoid.r u p.1 → forkState p.1

/-- **`MeetFibreBlock` — THE PROVABLE GATE AT THE MEET.**  The pointwise fibre
datum `BlockMin.FibreBlockData` holds at every representative of a meet
position.  This is weaker than `MeetConstancy` (it asks for the blocked-twin
data, not the pin at every member) and it is exactly what the PROVED existential
(§4) consumes.  Like `MeetConstancy` it is a named hypothesis, not a theorem:
`BlockMin.gFin_not_fibreBlockData` shows the pointwise form cannot be asserted
globally. -/
def MeetFibreBlock : Prop :=
  ∀ (u v : State) (x : Card) (q : Position) (p : WFState),
    SSaturated u → SSaturated v → sameOrbitSetoid.r u v →
    (∃ σ : Suit, rungAt u σ ≠ rungAt v σ) →
    PairMeetAt q u v x →
    (Quotient.mk orbitRungSetoid p : Position) = q →
    sameOrbitSetoid.r u p.1 → BlockMin.FibreBlockData p.1

/-- **THE CONSTANCY ROUTE.**  `MeetPositionForkLike` plus the meet-constancy
conjecture discharge the registered residue `SatDifferFork`.  The constancy
conjecture is a HYPOTHESIS: this theorem is a reduction, not a proof of the
conjecture. -/
theorem satDifferFork_of_meetConstancy
    (hM : MeetPositionForkLike) (hc : MeetConstancy) : SatDifferFork := by
  intro u v hsu hsv hcls hdiff
  obtain ⟨F, hF, x, hclsF, hfl, hmeet⟩ := hM u v hsu hsv hcls hdiff
  have hfs : forkState F :=
    hc u v x (Quotient.mk orbitRungSetoid ⟨F, hF⟩)
      hsu hsv hcls hdiff hmeet hfl ⟨F, hF⟩ rfl hclsF
  obtain ⟨y, hy⟩ := forkState_iff.mp hfs
  exact ⟨F, y, hclsF, hy⟩

/-- **THE DATA ROUTE (no constancy conjecture).**  `MeetPositionForkLike` plus
the weaker meet-gate `MeetFibreBlock` discharge `SatDifferFork` through the
PROVED gated existential (§4). -/
theorem satDifferFork_of_meet_of_data
    (hM : MeetPositionForkLike) (hgate : MeetFibreBlock) : SatDifferFork := by
  intro u v hsu hsv hcls hdiff
  obtain ⟨F, hF, x, hclsF, hfl, hmeet⟩ := hM u v hsu hsv hcls hdiff
  have hd : BlockMin.FibreBlockData F :=
    hgate u v x (Quotient.mk orbitRungSetoid ⟨F, hF⟩) ⟨F, hF⟩
      hsu hsv hcls hdiff hmeet rfl hclsF
  have hflpos : forkLikePos (Quotient.mk orbitRungSetoid ⟨F, hF⟩) := ⟨x, hfl⟩
  obtain ⟨p', hpos, hfs⟩ :=
    (forkLikePos_iff_exists_forkState_of_data ⟨F, hF⟩ hd).mp hflpos
  have hcls' : sameOrbitSetoid.r u p'.1 :=
    sameOrbitSetoid.iseqv.trans hclsF hpos.1
  obtain ⟨y, hy⟩ := forkState_iff.mp hfs
  exact ⟨p'.1, y, hcls', hy⟩

/-- **THE UNGATED IFF AT MEET POSITIONS** — the docstring claim of
`MeetConstancy`, made explicit: at a meet position, two same-orbit members are
fork states IF AND ONLY IF each other (both are, by constancy). -/
theorem meetConstancy_forkState_iff (hc : MeetConstancy)
    {u v : State} {x : Card} {q : Position}
    (hsu : SSaturated u) (hsv : SSaturated v) (hcls : sameOrbitSetoid.r u v)
    (hdiff : ∃ σ : Suit, rungAt u σ ≠ rungAt v σ)
    (hmeet : PairMeetAt q u v x) (hfl : ForkLiveAt q x)
    {p p' : WFState}
    (hp : (Quotient.mk orbitRungSetoid p : Position) = q)
    (hp' : (Quotient.mk orbitRungSetoid p' : Position) = q)
    (hpu : sameOrbitSetoid.r u p.1) (hp'u : sameOrbitSetoid.r u p'.1) :
    forkState p.1 ↔ forkState p'.1 :=
  ⟨fun _ => hc u v x q hsu hsv hcls hdiff hmeet hfl p' hp' hp'u,
   fun _ => hc u v x q hsu hsv hcls hdiff hmeet hfl p hp hpu⟩

/-! ## §7. The exact consumer chain -/

/-- `SatDifferFork` implies its `WF`-gated form (drop the binder). -/
theorem satDifferForkWF_of_satDifferFork (h : SatDifferFork) : SatDifferForkWF :=
  fun u v _ hsu hsv hcls hdiff => h u v hsu hsv hcls hdiff

/-- **THE CAMPAIGN THEOREM FROM THE MEET-CONSTANCY ROUTE.**  The full chain:
`MeetPositionForkLike + MeetConstancy -> SatDifferFork -> SatDifferForkWF ->
forkless_found_unique_wf`.  Both meet inputs are HYPOTHESES. -/
theorem forkless_found_unique_of_meet
    (hM : MeetPositionForkLike) (hc : MeetConstancy)
    {s s' : State} (hwf : s.WF) (hwf' : s'.WF)
    (hclass : sameOrbitSetoid.r s s')
    (hfrk : ∀ u, sameOrbitSetoid.r s u → ¬ forkState u)
    (hsat : SSaturated s) (hsat' : SSaturated s') :
    s.found = s'.found :=
  forkless_found_unique_wf (satDifferForkWF_of_satDifferFork
    (satDifferFork_of_meetConstancy hM hc)) hwf hwf' hclass hfrk hsat hsat'

/-- **THE CAMPAIGN THEOREM FROM THE DATA ROUTE.** -/
theorem forkless_found_unique_of_meet_data
    (hM : MeetPositionForkLike) (hgate : MeetFibreBlock)
    {s s' : State} (hwf : s.WF) (hwf' : s'.WF)
    (hclass : sameOrbitSetoid.r s s')
    (hfrk : ∀ u, sameOrbitSetoid.r s u → ¬ forkState u)
    (hsat : SSaturated s) (hsat' : SSaturated s') :
    s.found = s'.found :=
  forkless_found_unique_wf (satDifferForkWF_of_satDifferFork
    (satDifferFork_of_meet_of_data hM hgate)) hwf hwf' hclass hfrk hsat hsat'

end ForkFib

/-! ## §8. Axiom battery -/

#print axioms ForkFib.floor_coordinate
#print axioms ForkFib.fork_pair_floor_of_local
#print axioms ForkFib.fork_at_the_meet_of_parts
#print axioms ForkFib.fork_pair_rank_le_meet
#print axioms ForkFib.armDichotomy_imp_satDifferFork
#print axioms ForkFib.forkLikePos_positional
#print axioms ForkFib.forkLive_positional
#print axioms ForkFib.not_forkState_of_not_forkLikePos
#print axioms ForkFib.forkState_implies_forkLikePos_mate
#print axioms ForkFib.fibre_dichotomy_positional
#print axioms ForkFib.forkLikePos_iff_exists_forkLiveAt
#print axioms ForkFib.forkLikePos_iff_exists_forkState_of_data
#print axioms ForkFib.forkLikePos_iff_exists_forkState_of_position_data
#print axioms ForkFib.gFin_forkLive
#print axioms ForkFib.gFin_forkLike
#print axioms ForkFib.gFin_canRaise_H5
#print axioms ForkFib.gFin_canRaise_D5
#print axioms ForkFib.gFin_not_forkState
#print axioms ForkFib.not_forkLikePos_implies_forkState
#print axioms ForkFib.gFin_not_fibreBlockData
#print axioms ForkFib.satDifferFork_of_meetConstancy
#print axioms ForkFib.satDifferFork_of_meet_of_data
#print axioms ForkFib.meetConstancy_forkState_iff
#print axioms ForkFib.satDifferForkWF_of_satDifferFork
#print axioms ForkFib.forkless_found_unique_of_meet
#print axioms ForkFib.forkless_found_unique_of_meet_data

#check @ForkFib.ForkLiveAt
#check @ForkFib.PairMeetAt
#check @ForkFib.MeetPositionForkLike
#check @ForkFib.MeetConstancy
#check @ForkFib.MeetFibreBlock
#check @ForkFib.PairMeetTight
#check @ForkFib.PairFloorLocal
