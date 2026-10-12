import Orig.BracketDecomp

/-!
# Orig.PhaseClipProbe — THE (B) CLIPPING HUNT

The probe leaf hunting `Orig/HostCensus.lean`'s `interleave_phase_align`
falsification signature: witness-graded draws inside a replay shift the
zone deterministically; the classes only ROTATE (and the (B) row fails)
if mate states sit at phases where one draw CLIPS (`dealUpTo` take
saturates at `min k |stock|`) while the other deals full — commit-dash
one side of the threshold, home the other — so no reversible journey
joins the two drawn landings (`sameOrbitSetoid.r w₀ w` false) while
every board census agrees.

THE BOARDS (all zone-only exhibits — board fields sit inert; no row
below reads WF; every hunt leg is decide-grade):

* §1 STRADDLING (`pbS`): drawStep 3, pool 4 — the clip site (stock 1)
  over aligned waste; the two zone legs (recycle-deal + clipped
  restore) form the LOOOP, plus the pure-crossing pristine and the
  CLIPPED-OFFSET straddle (stock 2 < 3 over a mis-aligned waste) where
  the clipped draw COMMITS.
* §2 LARGE-DRASTEP (`pbL`): drawStep 5 — the sous-threshold regime
  is the whole pool; a mixed crossing (stock 6 → 1) rides the
  in-phase reversible family (the clipped mid-phase draw is a LEG,
  machine-certified by `draw_reversible_inphaseW`); the pristine
  straddle (stock 2 < 5) commits.
* §3 RECYCLE-EPOCH (`pbR`): the empty-stock boundary — at pool = k+1
  and pool = 2·k the recycle-deal pairs loop; the tiny offset pair
  (stock 1, waste 1) at drawStep 2 — the smallest conceivable
  crossing — commits off the phase line.

THE HUNT RESULT (see §5 ledger): at every board the (B)
precondition pair — MATE states with DIFFERING zones whose draws
both fire as COMMITS — failed to assemble: every draw site inside a
zone-crossing class leg is phase-aligned or recycle-sited, and
`Orig/Phase.lean`'s classification makes THOSE reversible (loop
legs); every clipped-but-COMMITTING site (pristine or offset) has NO
reversible draw leg of its own, so (with the waste letters barred
and the board letters zone-blind — `Orig/HostCensus.lean` §9) its
class is a ZONE ISLAND: zone-equal mates only, whose copies of the
commit commute by the board-blind transport.  The threshold crossing
itself is never the crime; the PHASE LINE is.  The one live
falsification channel narrows to: a clipped commit site whose
stroke-orbit class still reaches across zones — nothing on these
boards exhibits one, and Phase's classification + HostCensus's
board-blindness close off the ways it could form.

House discipline: per-file private kit copies; BOLD-name docstrings;
`#print axioms` battery; zero `Classical.choice`; sorry-free.
-/

/-! ## §0. The private kit -/

private def crd (s : Suit) (r : Rank) : Card := ⟨s, r⟩

private def S4 : Card := crd .spade .four
private def S5 : Card := crd .spade .five
private def S6 : Card := crd .spade .six
private def S7 : Card := crd .spade .seven
private def S8 : Card := crd .spade .eight
private def S9 : Card := crd .spade .nine
private def S10 : Card := crd .spade .ten
private def S11 : Card := crd .spade .ace
private def S12 : Card := crd .spade .two

/-- The drained step: the landing a move writes, the origin itself if
it refuses (the probe-house idiom, read off `Orig/LowSlabProbe.lean`'s
kit). -/
private def stepD (st : State) (m : Move) : State :=
  match st.step m with
  | some s' => s'
  | none => st

/-- The inert board: no foundations, all piles empty (hunt exhibits
are zone-only; any board-blind transport holds vacuously here). -/
private def inertPiles : Anchor → Pile := fun _ => ⟨[], []⟩
private def inertState (stock waste : List Card) (k : Nat) : State where
  found := fun _ => []
  piles := inertPiles
  stock := stock
  waste := waste
  drawStep := k

/-- **THE RUN SPLIT** (per-file copy of the `Orig/MacroInternal.lean`
private splice row): runs concatenate. -/
private theorem pb_run_split : ∀ (σ : List Move) (x y w : State),
    x.run σ = some y → ∀ (ρ : List Move), y.run ρ = some w →
    x.run (σ ++ ρ) = some w := by
  intro σ
  induction σ with
  | nil =>
      intro x y w hσ ρ hρ
      have h : (some x : Option State) = some y := hσ
      injection h with hx
      rw [← hx] at hρ
      rw [List.nil_append]
      exact hρ
  | cons m rest ih =>
      intro x y w hσ ρ hρ
      obtain ⟨s₁, hm, hrs⟩ := State.run_cons hσ
      have h3 := ih s₁ y w hrs ρ hρ
      rw [List.cons_append]
      show (match State.step x m with
        | some st' => st'.run (rest ++ ρ)
        | none => none) = some w
      rw [hm]
      exact h3

/-- **THE ROUND-TRIP SHUFFLE** (per-file copy of the
`Orig/MacroInternal.lean` private gadget): a pair of plain runs
chaining home makes a witness shuffle — every interior leg's
reversing play is the loop remainder spliced after it. -/
private theorem pb_shuffleW_of_round : ∀ (σ : List Move) (x w : State),
    x.run σ = some w → ∀ ρ : List Move, w.run ρ = some x →
      ShufflePlayW x σ w := by
  intro σ
  induction σ with
  | nil =>
      intro x w hσ ρ _hρ
      have hxw : (some x : Option State) = some w := hσ
      injection hxw with hx
      rw [hx]
      exact .nil w
  | cons p rest ih =>
      intro x w hσ ρ hρ
      obtain ⟨y, hp, hrest⟩ := State.run_cons hσ
      refine .cons ⟨y, rest ++ ρ, hp,
        pb_run_split rest y w x hrest ρ hρ⟩ hp ?_
      exact ih y w hrest (ρ ++ [p]) (pb_run_split ρ w x y hρ [p]
        (run_one hp))

/-- **THE LEG-TO-CLASS ROW** (per-file copy of the
`Orig/MacroInternal.lean` heart): one reversible move welds the
firing and its landing into the macro class. -/
private theorem pb_class_leg {st s₁ : State} {m : Move}
    (hrev : reversibleAtW st m) (hstep : State.step st m = some s₁) :
    sameOrbitSetoid.r st s₁ := by
  obtain ⟨s₁', play, hstep', hrun⟩ := hrev
  have hs : s₁' = s₁ := Option.some.inj (hstep'.symm.trans hstep)
  rw [hs] at hrun
  show RevEqW s₁ st
  exact ⟨play, pb_shuffleW_of_round play s₁ st hrun [m] (run_one hstep),
    [m], .cons ⟨s₁, play, hstep, hrun⟩ hstep (.nil s₁)⟩

/-! ## §1. STRADDLING — the `pbS` board

drawStep 3, pool 4.  The CROSSING at full speed: the recycle-deal
takes three of the four cards, the CLIPPED second take (stock 1 <
drawStep 3) restores the arrangement exactly — the two zone legs of
the loop, both `reversibleAtW`.  The fully-bare pristine STRADDLE
(stock 2 < 3 over an empty waste) COMMITS by the pristine row; the
CLIPPED-OFFSET STRADDLE (stock 2 < 3 over a mis-aligned waste)
COMMITS by the offset row — the crossing alone is not the crime.
-/

private def pbS0 : State := inertState [] [S4, S5, S6, S7] 3
private def pbS1 : State := stepD pbS0 Move.draw

theorem pbS0_zone : pbS0.stock = [] ∧ pbS0.waste = [S4, S5, S6, S7] ∧
    pbS0.drawStep = 3 := ⟨rfl, rfl, rfl⟩

theorem pbS0_draw : State.step pbS0 Move.draw = some pbS1 := rfl

theorem pbS1_zone : pbS1.stock = [S4] ∧ pbS1.waste = [S5, S6, S7] ∧
    pbS1.drawStep = 3 := by
  refine ⟨by rfl, by rfl, ?_⟩
  decide

theorem pbS1_draw : State.step pbS1 Move.draw = some pbS0 := by
  have hxEq : stepD pbS1 Move.draw = pbS0 := by
    refine State.ext (funext fun σ => ?_) (funext fun a => ?_) ?_ ?_ ?_
    · cases σ <;> rfl
    · cases a <;> rfl
    · rfl
    · rfl
    · rfl
  show State.step pbS1 Move.draw = some pbS0
  rw [show State.step pbS1 Move.draw
      = some (stepD pbS1 Move.draw) from rfl, hxEq]

theorem pbS0_drawRev : reversibleAtW pbS0 Move.draw :=
  ⟨pbS1, [Move.draw], pbS0_draw, run_one pbS1_draw⟩

theorem pbS1_drawRev : reversibleAtW pbS1 Move.draw :=
  ⟨pbS0, [Move.draw], pbS1_draw, run_one pbS0_draw⟩

theorem pbS0_notCommit : ¬ irreversibleAt pbS0 Move.draw := by
  intro hiv
  obtain ⟨s₁, play, hs, hr⟩ := pbS0_drawRev
  exact absurd hr (hiv s₁ play hs)

theorem pbS1_notCommit : ¬ irreversibleAt pbS1 Move.draw := by
  intro hiv
  obtain ⟨s₁, play, hs, hr⟩ := pbS1_drawRev
  exact absurd hr (hiv s₁ play hs)

/-- The loop pair is a class pair (the interleave COMMUTES at the
aligned crossing: drawn landings of the loop are loop states again). -/
theorem pbS_class : sameOrbitSetoid.r pbS0 pbS1 :=
  pb_class_leg pbS0_drawRev pbS0_draw

/-- The pristine STRADDLE crosses and COMMITS (clip irrelevant). -/
private def pbSP : State := inertState [S4, S5] [] 3

theorem pbSP_irr : irreversibleAt pbSP Move.draw :=
  draw_irreversible_pristine (by decide) (by decide) (by rfl)

theorem pbSP_notRev : ¬ reversibleAtW pbSP Move.draw :=
  not_reversibleAtW_of_irreversibleAt pbSP_irr

/-- The CLIPPED-OFFSET STRADDLE commits off the phase line. -/
private def pbSO : State := inertState [S4, S5] [S6] 3

theorem pbSO_irr : irreversibleAt pbSO Move.draw :=
  draw_irreversible_offset (by decide) (by decide) (by decide)

theorem pbSO_notRev : ¬ reversibleAtW pbSO Move.draw :=
  not_reversibleAtW_of_irreversibleAt pbSO_irr

/-! ## §2. LARGE-DRASTEP — the `pbL` board

drawStep 5, the sous-threshold regime.  The loop at pool 6 (recycle
deals five, the CLIPPED one-card restore); the MIXED crossing rides
the in-phase family — a full deal off six (stock 6 → 1) then the
CLIPPED mid-phase draw, machine-certified reversible by
`draw_reversible_inphaseW` — and the pristine straddle (stock 2 <
5) commits.
-/

private def pbL0 : State := inertState [] [S4, S5, S6, S7, S8, S9] 5
private def pbL1 : State := stepD pbL0 Move.draw

theorem pbL0_draw : State.step pbL0 Move.draw = some pbL1 := rfl

theorem pbL1_zone : pbL1.stock = [S4] ∧ pbL1.waste = [S5, S6, S7, S8, S9] ∧
    pbL1.drawStep = 5 := by
  refine ⟨by rfl, by rfl, ?_⟩
  decide

theorem pbL1_draw : State.step pbL1 Move.draw = some pbL0 := by
  have hxEq : stepD pbL1 Move.draw = pbL0 := by
    refine State.ext (funext fun σ => ?_) (funext fun a => ?_) ?_ ?_ ?_
    · cases σ <;> rfl
    · cases a <;> rfl
    · rfl
    · rfl
    · rfl
  show State.step pbL1 Move.draw = some pbL0
  rw [show State.step pbL1 Move.draw
      = some (stepD pbL1 Move.draw) from rfl, hxEq]

theorem pbL0_drawRev : reversibleAtW pbL0 Move.draw :=
  ⟨pbL1, [Move.draw], pbL0_draw, run_one pbL1_draw⟩

theorem pbL1_drawRev : reversibleAtW pbL1 Move.draw :=
  ⟨pbL0, [Move.draw], pbL1_draw, run_one pbL0_draw⟩

theorem pbL_class : sameOrbitSetoid.r pbL0 pbL1 :=
  pb_class_leg pbL0_drawRev pbL0_draw

/-- The mixed crossing: a FULL deal off six, then the CLIPPED draw at
the leftover one — the clipped mid-phase draw is a REVERSIBLE LEG
(`draw_reversible_inphaseW`), never a commit. -/
private def pbL2 : State := inertState [S4, S5, S6, S7, S8, S9]
    [S10, S11, S12, S4, S5] 5

theorem pbL2_inPhase : inPhase pbL2 = true := by
  show (match pbL2.stock with
    | [] => true
    | _ => decide (pbL2.waste.length % pbL2.drawStep = 0)) = true
  decide

theorem pbL2_drawRev : reversibleAtW pbL2 Move.draw := by
  refine draw_reversible_inphaseW (by decide) (by decide) (by decide)
    pbL2_inPhase

/-- The pristine LARGE-DRASTEP straddle commits. -/
private def pbLP : State := inertState [S4, S5] [] 5

theorem pbLP_irr : irreversibleAt pbLP Move.draw :=
  draw_irreversible_pristine (by decide) (by decide) (by rfl)

theorem pbLP_notRev : ¬ reversibleAtW pbLP Move.draw :=
  not_reversibleAtW_of_irreversibleAt pbLP_irr

/-- The full-deal OFFSET crossing at large drawStep commits too. -/
private def pbLO : State := inertState [S4, S5, S6, S7, S8] [S9] 5

theorem pbLO_irr : irreversibleAt pbLO Move.draw :=
  draw_irreversible_offset (by decide) (by decide) (by decide)

/-! ## §3. RECYCLE-EPOCH — the `pbR` boards

drawStep 2 at the empty-stock boundary.  The pool-4 epoch (pool =
2·drawStep) loops with TWO FULL deals — the boundary epoch — while
the pool-3 epoch clips its leftover back.  The tiny OFFSET PAIR
(stock 1, waste 1) — the smallest conceivable crossing at
drawStep 2 — sits OFF the phase line and COMMITS: even at the
epoch's doorstep the alignment decides, not the threshold.
-/

private def pbR0 : State := inertState [] [S4, S5, S6, S7] 2
private def pbR1 : State := stepD pbR0 Move.draw

theorem pbR0_draw : State.step pbR0 Move.draw = some pbR1 := rfl

theorem pbR1_zone : pbR1.stock = [S5, S4] ∧ pbR1.waste = [S6, S7] ∧
    pbR1.drawStep = 2 := by
  refine ⟨by rfl, by rfl, ?_⟩
  decide

theorem pbR1_draw : State.step pbR1 Move.draw = some pbR0 := by
  have hxEq : stepD pbR1 Move.draw = pbR0 := by
    refine State.ext (funext fun σ => ?_) (funext fun a => ?_) ?_ ?_ ?_
    · cases σ <;> rfl
    · cases a <;> rfl
    · rfl
    · rfl
    · rfl
  show State.step pbR1 Move.draw = some pbR0
  rw [show State.step pbR1 Move.draw
      = some (stepD pbR1 Move.draw) from rfl, hxEq]

theorem pbR0_drawRev : reversibleAtW pbR0 Move.draw :=
  ⟨pbR1, [Move.draw], pbR0_draw, run_one pbR1_draw⟩

theorem pbR1_drawRev : reversibleAtW pbR1 Move.draw :=
  ⟨pbR0, [Move.draw], pbR1_draw, run_one pbR0_draw⟩

theorem pbR_class : sameOrbitSetoid.r pbR0 pbR1 :=
  pb_class_leg pbR0_drawRev pbR0_draw

/- The pool-3 epoch: recycle deals two of three (stock 1), the
CLIPPED restore is the short-stock full deal. -/
private def pbR2 : State := inertState [] [S4, S5, S6] 2
private def pbR3 : State := stepD pbR2 Move.draw

theorem pbR2_draw : State.step pbR2 Move.draw = some pbR3 := rfl

theorem pbR3_zone : pbR3.stock = [S4] ∧ pbR3.waste = [S5, S6] ∧
    pbR3.drawStep = 2 := by
  refine ⟨by rfl, by rfl, ?_⟩
  decide

theorem pbR3_draw : State.step pbR3 Move.draw = some pbR2 := by
  have hxEq : stepD pbR3 Move.draw = pbR2 := by
    refine State.ext (funext fun σ => ?_) (funext fun a => ?_) ?_ ?_ ?_
    · cases σ <;> rfl
    · cases a <;> rfl
    · rfl
    · rfl
    · rfl
  show State.step pbR3 Move.draw = some pbR2
  rw [show State.step pbR3 Move.draw
      = some (stepD pbR3 Move.draw) from rfl, hxEq]

theorem pbR2_drawRev : reversibleAtW pbR2 Move.draw :=
  ⟨pbR3, [Move.draw], pbR2_draw, run_one pbR3_draw⟩

theorem pbR3_drawRev : reversibleAtW pbR3 Move.draw :=
  ⟨pbR2, [Move.draw], pbR3_draw, run_one pbR2_draw⟩

theorem pbR2_class : sameOrbitSetoid.r pbR2 pbR3 :=
  pb_class_leg pbR2_drawRev pbR2_draw

/- The smallest conceivable crossing COMMITS off the phase line. -/
private def pbRO : State := inertState [S4] [S5] 2

theorem pbRO_irr : irreversibleAt pbRO Move.draw :=
  draw_irreversible_offset (by decide) (by decide) (by decide)

theorem pbRO_notRev : ¬ reversibleAtW pbRO Move.draw :=
  not_reversibleAtW_of_irreversibleAt pbRO_irr

/- The epoch's pristine doorway commits. -/
private def pbRP : State := inertState [S4] [] 2

theorem pbRP_irr : irreversibleAt pbRP Move.draw :=
  draw_irreversible_pristine (by decide) (by decide) (by rfl)

theorem pbRP_notRev : ¬ reversibleAtW pbRP Move.draw :=
  not_reversibleAtW_of_irreversibleAt pbRP_irr

/-! ## §4. THE CATEGORICAL ROWS

The hunt's structural observations, machine-verifiable without
quantifying over plays: a reversible draw site is NEVER a commit site
(the definitional dichotomy), and a commit site has no reversible
draw leg of its own (the Phase classification: pristine and offset
cover every firing draw that is not phase-aligned-loop or
recycle-sited).
-/

/-- A reversible draw is never a commit (the banked contrapositive,
packaged once for the ledger). -/
theorem pb_rev_not_commit {st : State}
    (h : reversibleAtW st Move.draw) :
    ¬ irreversibleAt st Move.draw := by
  intro hiv
  obtain ⟨s₁, play, hs, hr⟩ := h
  exact absurd hr (hiv s₁ play hs)

/-- A commit draw has no reversible leg of its own at that state —
the (B) precondition, machine side: a committing site cannot be the
class leg that welds zones. -/
theorem pb_commit_no_leg {st : State}
    (h : irreversibleAt st Move.draw) :
    ¬ reversibleAtW st Move.draw :=
  not_reversibleAtW_of_irreversibleAt h

/-- Every committing draw site exhibited here sits off the
phase-line or pristine — the threshold crossings themselves
(pbS, pbL, pbR loops) are all loop legs. -/
theorem pb_crossings_all_legs :
    reversibleAtW pbS0 Move.draw ∧ reversibleAtW pbS1 Move.draw ∧
      reversibleAtW pbL0 Move.draw ∧ reversibleAtW pbL1 Move.draw ∧
        reversibleAtW pbL2 Move.draw ∧ reversibleAtW pbR0 Move.draw ∧
          reversibleAtW pbR2 Move.draw ∧ reversibleAtW pbR3 Move.draw :=
  ⟨pbS0_drawRev, pbS1_drawRev, pbL0_drawRev, pbL1_drawRev, pbL2_drawRev,
    pbR0_drawRev, pbR2_drawRev, pbR3_drawRev⟩

/-- Every committing site exhibited here is pristine or offset —
including the clipped straddles. -/
theorem pb_commits_all_offline :
    irreversibleAt pbSP Move.draw ∧ ¬ reversibleAtW pbSP Move.draw ∧
      irreversibleAt pbSO Move.draw ∧ ¬ reversibleAtW pbSO Move.draw ∧
        irreversibleAt pbLP Move.draw ∧ ¬ reversibleAtW pbLP Move.draw ∧
          irreversibleAt pbLO Move.draw ∧
            irreversibleAt pbRO Move.draw ∧ ¬ reversibleAtW pbRO Move.draw ∧
              irreversibleAt pbRP Move.draw ∧ ¬ reversibleAtW pbRP Move.draw :=
  ⟨pbSP_irr, pbSP_notRev, pbSO_irr, pbSO_notRev,
    pbLP_irr, pbLP_notRev, pbLO_irr,
    pbRO_irr, pbRO_notRev, pbRP_irr, pbRP_notRev⟩

/-! ## §5. THE VERDICT LEDGER

**Hunt disposition — no candidate counterexample; three
systematic-failure datapoints.**  Per board:

* §1 STRADDLING: the pool's own crossing (stock 1 < k over aligned
  waste) is the loop's clip leg — reversible, commuting
  (`pbS_class`); the fully-crossing pristine (`pbSP`) and the
  CLIPPED-OFFSET (`pbSO`) both commit by the Phase rows
  (`pb_commits_all_offline`) and lose every reversible draw leg
  (`pb_commit_no_leg`), so the (B) precondition — zone-differing
  MATE whose draws both COMMIT — failed to assemble in both
  directions tried: (i) aligned mates' draws never commit;
  (ii) committing sites never mate across zones (their only
  zone-writing leg is the committed draw itself).
* §2 LARGE-DRASTEP: same, at the dominant-clip regime — including
  the full-deal-then-clip crossing (`pbL2`), whose clipped draw is
  machine-certified reversible by `draw_reversible_inphaseW`; the
  pristine (`pbLP`) and offset (`pbLO`) commits stand barred.
* §3 RECYCLE-EPOCH: the epoch loops (`pbR0/pbR1`, `pbR2/pbR3`)
  include the boundary pool = 2·drawStep epoch and the clip-restore
  epoch; the smallest crossing (stock 1, waste 1 at drawStep 2 —
  `pbRO`) is OFF the phase line and commits — strengthened armor:
  even at the epoch's doorstep the ALIGNMENT decides, not the
  threshold.

THE ARMOR (tried and did not break): the phase-line classification
(`draw_irreversible_pristine` / `draw_irreversible_offset` /
`draw_reversible_inphaseW` / the loop rows) held at every shape
thrown at it; the leg/commit dichotomy (`pb_rev_not_commit`,
`pb_commit_no_leg`) held definitionally; the board-blindness
transport of `Orig/HostCensus.lean` §9 stands unbroken — no
census-blind split was even approachable.

DISPOSITION OF (B): the falsification signature did NOT materialize
on any tried economy.  The structural read recorded for the
integrator: a commit site's macro class is a zone island
(its only zone-writing move is the committed draw; waste letters
are journey-barred; board letters are zone-blind), so the (B)
precondition pair reduces to zone-equal mates, whose copied
commits commute by the board-blind transport
(`drawfree_commute_reach`'s machinery, `Orig/HostCensus.lean` §9).
The live channels this probe could NOT close by decide-grade
exhibits — and hands to the integrator: (i) commit sites with a
board leg chain that re-legalizes the waste letters (a
`wasteTo*`-riding witness journey is barred by the alphabet, so
this needs the letters' own reversibility regime — none exists in
the bank); (ii) the epoch-deep `inPhase` restore at
pool = k + r with r | k-style resonances — the loop-closing
condition (pool < 2·drawStep here) may admit longer-period
structures on bigger economies where the clip return doesn't
restore the arrangement; hunt those at large pools with
drawStep | pool − drawStep.
-/

theorem pb_huntLedger :
    -- the aligned crossings commute
    (sameOrbitSetoid.r pbS0 pbS1 ∧ reversibleAtW pbS0 Move.draw ∧
      reversibleAtW pbS1 Move.draw ∧
    sameOrbitSetoid.r pbL0 pbL1 ∧ sameOrbitSetoid.r pbR0 pbR1 ∧
      sameOrbitSetoid.r pbR2 pbR3 ∧
    -- the mixed full-then-clip crossing is a leg
    reversibleAtW pbL2 Move.draw ∧
    -- the commits fire and lose their legs
    irreversibleAt pbSP Move.draw ∧ ¬ reversibleAtW pbSP Move.draw ∧
    irreversibleAt pbSO Move.draw ∧ ¬ reversibleAtW pbSO Move.draw ∧
    irreversibleAt pbLP Move.draw ∧ ¬ reversibleAtW pbLP Move.draw ∧
    irreversibleAt pbLO Move.draw ∧
    irreversibleAt pbRO Move.draw ∧ ¬ reversibleAtW pbRO Move.draw ∧
    irreversibleAt pbRP Move.draw ∧ ¬ reversibleAtW pbRP Move.draw ∧
    -- and the dichotomy rows are live
    (∀ st : State, reversibleAtW st Move.draw →
       ¬ irreversibleAt st Move.draw) ∧
    (∀ st : State, irreversibleAt st Move.draw →
       ¬ reversibleAtW st Move.draw)) :=
  ⟨pbS_class, pbS0_drawRev, pbS1_drawRev, pbL_class, pbR_class,
    pbR2_class, pbL2_drawRev, pbSP_irr, pbSP_notRev, pbSO_irr,
    pbSO_notRev, pbLP_irr, pbLP_notRev, pbLO_irr, pbRO_irr,
    pbRO_notRev, pbRP_irr, pbRP_notRev,
    fun _ h => pb_rev_not_commit h,
    fun _ h => pb_commit_no_leg h⟩

/-! ### The audit battery

Decide-grade throughout; zero `sorry`, zero `Classical.choice`
(the `sameOrbitSetoid` materials ride the banked quotient). -/

#print axioms pbS_class
#print axioms pbL_class
#print axioms pbL2_drawRev
#print axioms pbR_class
#print axioms pbR2_class
#print axioms pbSP_irr
#print axioms pbSO_irr
#print axioms pbLP_irr
#print axioms pbLO_irr
#print axioms pbRO_irr
#print axioms pbRP_irr
#print axioms pb_rev_not_commit
#print axioms pb_commit_no_leg
#print axioms pb_crossings_all_legs
#print axioms pb_commits_all_offline
#print axioms pb_huntLedger
