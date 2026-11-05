import Orig2.Substrate.CargoRaise
import Orig2.Fiber.TwinEquivariance
import Orig2.Fiber.ArmSplit
import Orig2.Substrate.StepWF

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# Orig2.Boundary — the two boundary cases

THE COUNTEREXAMPLES THAT FIX THE TARGET SHAPES.

## §1. The equal-rung boundary (`vcS/vcT`)

Two `WF` states with the same rung vector `(H,D,S,C) = (3,0,4,3)`, both
`SSaturated`, in one `sameOrbitSetoid` class, and NOT `BareCargoEquiv`.
This is the separating example for `ArmDichotomy`; `vc_armDichotomy_fork`
shows the residue must supply a class-wide fork here.

## §2. The draw boundary

The all-non-king board (A–Q of each suit founded, every pile empty, the
four kings split between stock and waste, `drawStep = 1`) is draw-only:
no founded king exists, so no `foundToTab` onto an empty anchor is
available and the tableau stays empty.  `drawD0` and `drawD1` are both
`SSaturated`, same-orbit, NOT `BareCargoEquiv`, and the class has no
fork.  Hence:

```lean
¬ SatEqualFork
¬ ArmDichotomy
```

The repairs are `ArmDichotomyRung` (rung branch; exactly `SatDifferFork`)
and the flat-fiber `ArmDichotomySW` (`Orig2/Fiber/SWDichotomy.lean`).

House compliance: additive leaf (`Orig2.CargoRaise`,
`Orig2.TwinEquivariance`, `Orig2.ArmSplit`, `Orig2.StepWF`); zero `sorry`,
zero `Classical.choice`; battery at tail.
-/
private def vcC (s : Suit) (r : Rank) : Card := ⟨s, r⟩

private def vcFound : Suit → List Card
  | .heart => [vcC .heart .ace, vcC .heart .two, vcC .heart .three]
  | .diamond => []
  | .spade =>
      [vcC .spade .ace, vcC .spade .two, vcC .spade .three, vcC .spade .four]
  | .club => [vcC .club .ace, vcC .club .two, vcC .club .three]

private def vcHidden : List Card :=
  [vcC .diamond .ace, vcC .diamond .two, vcC .heart .four,
   vcC .diamond .four, vcC .spade .five, vcC .heart .six,
   vcC .club .seven, vcC .diamond .eight, vcC .club .eight,
   vcC .heart .nine, vcC .spade .nine, vcC .diamond .ten,
   vcC .spade .ten, vcC .club .ten, vcC .heart .jack,
   vcC .diamond .jack, vcC .spade .jack, vcC .club .jack,
   vcC .diamond .queen, vcC .spade .queen, vcC .club .queen,
   vcC .heart .king, vcC .diamond .king, vcC .spade .king,
   vcC .club .king]

def vcS : State where
  found := vcFound
  piles := fun a => match a with
    | .p0 => ⟨[], [vcC .heart .five, vcC .club .four, vcC .diamond .three]⟩
    | .p1 => ⟨[], [vcC .heart .seven, vcC .spade .six, vcC .diamond .five]⟩
    | .p2 => ⟨[], [vcC .heart .ten, vcC .club .nine, vcC .heart .eight]⟩
    | .p3 => ⟨[], [vcC .diamond .nine, vcC .spade .eight,
                    vcC .diamond .seven, vcC .club .six]⟩
    | .p4 => ⟨[], [vcC .heart .queen]⟩
    | .p5 => ⟨[], [vcC .spade .seven, vcC .diamond .six, vcC .club .five]⟩
    | .p6 => ⟨vcHidden, []⟩
  stock := []
  waste := []
  drawStep := 1

def vcT : State where
  found := vcFound
  piles := fun a => match a with
    | .p0 => ⟨[], [vcC .heart .five]⟩
    | .p1 => ⟨[], [vcC .heart .seven, vcC .club .six]⟩
    | .p2 => ⟨[], [vcC .heart .ten, vcC .club .nine, vcC .heart .eight]⟩
    | .p3 => ⟨[], [vcC .diamond .nine, vcC .spade .eight,
                    vcC .diamond .seven, vcC .spade .six,
                    vcC .diamond .five, vcC .club .four,
                    vcC .diamond .three]⟩
    | .p4 => ⟨[], [vcC .heart .queen]⟩
    | .p5 => ⟨[], [vcC .spade .seven, vcC .diamond .six, vcC .club .five]⟩
    | .p6 => ⟨vcHidden, []⟩
  stock := []
  waste := []
  drawStep := 1

theorem vcS_wf : vcS.WF := by
  refine ⟨fun s => ?_, ?_, ?_, ?_⟩
  · cases s with
    | heart => exact ⟨3, rfl⟩
    | diamond => exact ⟨0, rfl⟩
    | spade => exact ⟨4, rfl⟩
    | club => exact ⟨3, rfl⟩
  · intro a
    cases a <;> decide
  · intro c _
    rcases c with ⟨s, r⟩
    cases s <;> cases r <;> decide
  · decide

theorem vcT_wf : vcT.WF := by
  refine ⟨fun s => ?_, ?_, ?_, ?_⟩
  · cases s with
    | heart => exact ⟨3, rfl⟩
    | diamond => exact ⟨0, rfl⟩
    | spade => exact ⟨4, rfl⟩
    | club => exact ⟨3, rfl⟩
  · intro a
    cases a <;> decide
  · intro c _
    rcases c with ⟨s, r⟩
    cases s <;> cases r <;> decide
  · decide

/-- The rung vector agrees. -/
theorem vc_rungs : ∀ σ, rungAt vcS σ = rungAt vcT σ := by
  intro σ
  cases σ <;> rfl

/-! ## The witness journey (12 legs, each with a one-move mirror) -/

private def m1 : Move := Move.foundToTab (vcC .spade .four) (Sum.inr (vcC .diamond .five))
private def m2 : Move := Move.tabToTab (vcC .diamond .three) (Sum.inr (vcC .spade .four))
private def m3 : Move := Move.tabToFound (vcC .club .four)
private def m4 : Move := Move.tabToTab (vcC .spade .four) (Sum.inr (vcC .heart .five))
private def m5 : Move := Move.tabToFound (vcC .club .five)
private def m6 : Move := Move.tabToFound (vcC .club .six)
private def m7 : Move := Move.tabToTab (vcC .spade .six) (Sum.inr (vcC .diamond .seven))
private def m8 : Move := Move.foundToTab (vcC .club .six) (Sum.inr (vcC .heart .seven))
private def m9 : Move := Move.foundToTab (vcC .club .five) (Sum.inr (vcC .diamond .six))
private def m10 : Move := Move.foundToTab (vcC .club .four) (Sum.inr (vcC .diamond .five))
private def m11 : Move := Move.tabToTab (vcC .diamond .three) (Sum.inr (vcC .club .four))
private def m12 : Move := Move.tabToFound (vcC .spade .four)

private def vcStep (st : State) (m : Move) : State :=
  match st.step m with
  | none => st
  | some s' => s'

private def vcS1 : State := vcStep vcS m1
private def vcS2 : State := vcStep vcS1 m2
private def vcS3 : State := vcStep vcS2 m3
private def vcS4 : State := vcStep vcS3 m4
private def vcS5 : State := vcStep vcS4 m5
private def vcS6 : State := vcStep vcS5 m6
private def vcS7 : State := vcStep vcS6 m7
private def vcS8 : State := vcStep vcS7 m8
private def vcS9 : State := vcStep vcS8 m9
private def vcS10 : State := vcStep vcS9 m10
private def vcS11 : State := vcStep vcS10 m11
private def vcS12 : State := vcStep vcS11 m12

private theorem vc_step_1 : State.step vcS m1 = some vcS1 := by rfl
private theorem vc_step_2 : State.step vcS1 m2 = some vcS2 := by rfl
private theorem vc_step_3 : State.step vcS2 m3 = some vcS3 := by rfl
private theorem vc_step_4 : State.step vcS3 m4 = some vcS4 := by rfl
private theorem vc_step_5 : State.step vcS4 m5 = some vcS5 := by rfl
private theorem vc_step_6 : State.step vcS5 m6 = some vcS6 := by rfl
private theorem vc_step_7 : State.step vcS6 m7 = some vcS7 := by rfl
private theorem vc_step_8 : State.step vcS7 m8 = some vcS8 := by rfl
private theorem vc_step_9 : State.step vcS8 m9 = some vcS9 := by rfl
private theorem vc_step_10 : State.step vcS9 m10 = some vcS10 := by rfl
private theorem vc_step_11 : State.step vcS10 m11 = some vcS11 := by rfl
private theorem vc_step_12 : State.step vcS11 m12 = some vcS12 := by rfl

private theorem vcS12_eq_vcT : vcS12 = vcT := by
  refine State.ext (funext fun s => ?_) (funext fun a => ?_) rfl rfl rfl
  · cases s <;> rfl
  · cases a <;> rfl

/-- Both endpoints are SSaturated: the flat S-license probe scans false. -/
theorem vcS_sat : SSaturated vcS := by
  have h : rankSatB 12 vcS = true := by decide
  have hRS := (rankSatB_iff vcS_wf 12).mp h
  intro c hc
  exact hRS c (by have := Rank.toIdx_lt c.rank; omega) hc

theorem vcT_sat : SSaturated vcT := by
  have h : rankSatB 12 vcT = true := by decide
  have hRS := (rankSatB_iff vcT_wf 12).mp h
  intro c hc
  exact hRS c (by have := Rank.toIdx_lt c.rank; omega) hc

private def rm1 : Move := Move.tabToFound (vcC .spade .four)
private def rm2 : Move := Move.tabToTab (vcC .diamond .three) (Sum.inr (vcC .club .four))
private def rm3 : Move := Move.foundToTab (vcC .club .four) (Sum.inr (vcC .heart .five))
private def rm4 : Move := Move.tabToTab (vcC .spade .four) (Sum.inr (vcC .diamond .five))
private def rm5 : Move := Move.foundToTab (vcC .club .five) (Sum.inr (vcC .diamond .six))
private def rm6 : Move := Move.foundToTab (vcC .club .six) (Sum.inr (vcC .diamond .seven))
private def rm7 : Move := Move.tabToTab (vcC .spade .six) (Sum.inr (vcC .heart .seven))
private def rm8 : Move := Move.tabToFound (vcC .club .six)
private def rm9 : Move := Move.tabToFound (vcC .club .five)
private def rm10 : Move := Move.tabToFound (vcC .club .four)
private def rm11 : Move := Move.tabToTab (vcC .diamond .three) (Sum.inr (vcC .spade .four))
private def rm12 : Move := Move.foundToTab (vcC .spade .four) (Sum.inr (vcC .heart .five))

private def rv1 : State := vcStep vcS1 rm1
private def rv2 : State := vcStep vcS2 rm2
private def rv3 : State := vcStep vcS3 rm3
private def rv4 : State := vcStep vcS4 rm4
private def rv5 : State := vcStep vcS5 rm5
private def rv6 : State := vcStep vcS6 rm6
private def rv7 : State := vcStep vcS7 rm7
private def rv8 : State := vcStep vcS8 rm8
private def rv9 : State := vcStep vcS9 rm9
private def rv10 : State := vcStep vcS10 rm10
private def rv11 : State := vcStep vcS11 rm11
private def rv12 : State := vcStep vcS12 rm12

private theorem vc_retstep_1 : State.step vcS1 rm1 = some rv1 := by rfl
private theorem vc_retstep_2 : State.step vcS2 rm2 = some rv2 := by rfl
private theorem vc_retstep_3 : State.step vcS3 rm3 = some rv3 := by rfl
private theorem vc_retstep_4 : State.step vcS4 rm4 = some rv4 := by rfl
private theorem vc_retstep_5 : State.step vcS5 rm5 = some rv5 := by rfl
private theorem vc_retstep_6 : State.step vcS6 rm6 = some rv6 := by rfl
private theorem vc_retstep_7 : State.step vcS7 rm7 = some rv7 := by rfl
private theorem vc_retstep_8 : State.step vcS8 rm8 = some rv8 := by rfl
private theorem vc_retstep_9 : State.step vcS9 rm9 = some rv9 := by rfl
private theorem vc_retstep_10 : State.step vcS10 rm10 = some rv10 := by rfl
private theorem vc_retstep_11 : State.step vcS11 rm11 = some rv11 := by rfl
private theorem vc_retstep_12 : State.step vcS12 rm12 = some rv12 := by rfl

private theorem vc_rveq_1 : rv1 = vcS := by
  refine State.ext (funext fun s => ?_) (funext fun a => ?_) rfl rfl rfl
  · cases s <;> rfl
  · cases a <;> rfl
private theorem vc_rveq_2 : rv2 = vcS1 := by
  refine State.ext (funext fun s => ?_) (funext fun a => ?_) rfl rfl rfl
  · cases s <;> rfl
  · cases a <;> rfl
private theorem vc_rveq_3 : rv3 = vcS2 := by
  refine State.ext (funext fun s => ?_) (funext fun a => ?_) rfl rfl rfl
  · cases s <;> rfl
  · cases a <;> rfl
private theorem vc_rveq_4 : rv4 = vcS3 := by
  refine State.ext (funext fun s => ?_) (funext fun a => ?_) rfl rfl rfl
  · cases s <;> rfl
  · cases a <;> rfl
private theorem vc_rveq_5 : rv5 = vcS4 := by
  refine State.ext (funext fun s => ?_) (funext fun a => ?_) rfl rfl rfl
  · cases s <;> rfl
  · cases a <;> rfl
private theorem vc_rveq_6 : rv6 = vcS5 := by
  refine State.ext (funext fun s => ?_) (funext fun a => ?_) rfl rfl rfl
  · cases s <;> rfl
  · cases a <;> rfl
private theorem vc_rveq_7 : rv7 = vcS6 := by
  refine State.ext (funext fun s => ?_) (funext fun a => ?_) rfl rfl rfl
  · cases s <;> rfl
  · cases a <;> rfl
private theorem vc_rveq_8 : rv8 = vcS7 := by
  refine State.ext (funext fun s => ?_) (funext fun a => ?_) rfl rfl rfl
  · cases s <;> rfl
  · cases a <;> rfl
private theorem vc_rveq_9 : rv9 = vcS8 := by
  refine State.ext (funext fun s => ?_) (funext fun a => ?_) rfl rfl rfl
  · cases s <;> rfl
  · cases a <;> rfl
private theorem vc_rveq_10 : rv10 = vcS9 := by
  refine State.ext (funext fun s => ?_) (funext fun a => ?_) rfl rfl rfl
  · cases s <;> rfl
  · cases a <;> rfl
private theorem vc_rveq_11 : rv11 = vcS10 := by
  refine State.ext (funext fun s => ?_) (funext fun a => ?_) rfl rfl rfl
  · cases s <;> rfl
  · cases a <;> rfl
private theorem vc_rveq_12 : rv12 = vcS11 := by
  refine State.ext (funext fun s => ?_) (funext fun a => ?_) rfl rfl rfl
  · cases s <;> rfl
  · cases a <;> rfl

private theorem vc_ret_1 : State.step vcS1 rm1 = some vcS := by
  rw [vc_retstep_1, vc_rveq_1]
private theorem vc_ret_2 : State.step vcS2 rm2 = some vcS1 := by
  rw [vc_retstep_2, vc_rveq_2]
private theorem vc_ret_3 : State.step vcS3 rm3 = some vcS2 := by
  rw [vc_retstep_3, vc_rveq_3]
private theorem vc_ret_4 : State.step vcS4 rm4 = some vcS3 := by
  rw [vc_retstep_4, vc_rveq_4]
private theorem vc_ret_5 : State.step vcS5 rm5 = some vcS4 := by
  rw [vc_retstep_5, vc_rveq_5]
private theorem vc_ret_6 : State.step vcS6 rm6 = some vcS5 := by
  rw [vc_retstep_6, vc_rveq_6]
private theorem vc_ret_7 : State.step vcS7 rm7 = some vcS6 := by
  rw [vc_retstep_7, vc_rveq_7]
private theorem vc_ret_8 : State.step vcS8 rm8 = some vcS7 := by
  rw [vc_retstep_8, vc_rveq_8]
private theorem vc_ret_9 : State.step vcS9 rm9 = some vcS8 := by
  rw [vc_retstep_9, vc_rveq_9]
private theorem vc_ret_10 : State.step vcS10 rm10 = some vcS9 := by
  rw [vc_retstep_10, vc_rveq_10]
private theorem vc_ret_11 : State.step vcS11 rm11 = some vcS10 := by
  rw [vc_retstep_11, vc_rveq_11]
private theorem vc_ret_12 : State.step vcS12 rm12 = some vcS11 := by
  rw [vc_retstep_12, vc_rveq_12]

private theorem vc_rev_1 : reversibleAtW vcS m1 :=
  ⟨vcS1, [rm1], vc_step_1, run_one vc_ret_1⟩
private theorem vc_rev_2 : reversibleAtW vcS1 m2 :=
  ⟨vcS2, [rm2], vc_step_2, run_one vc_ret_2⟩
private theorem vc_rev_3 : reversibleAtW vcS2 m3 :=
  ⟨vcS3, [rm3], vc_step_3, run_one vc_ret_3⟩
private theorem vc_rev_4 : reversibleAtW vcS3 m4 :=
  ⟨vcS4, [rm4], vc_step_4, run_one vc_ret_4⟩
private theorem vc_rev_5 : reversibleAtW vcS4 m5 :=
  ⟨vcS5, [rm5], vc_step_5, run_one vc_ret_5⟩
private theorem vc_rev_6 : reversibleAtW vcS5 m6 :=
  ⟨vcS6, [rm6], vc_step_6, run_one vc_ret_6⟩
private theorem vc_rev_7 : reversibleAtW vcS6 m7 :=
  ⟨vcS7, [rm7], vc_step_7, run_one vc_ret_7⟩
private theorem vc_rev_8 : reversibleAtW vcS7 m8 :=
  ⟨vcS8, [rm8], vc_step_8, run_one vc_ret_8⟩
private theorem vc_rev_9 : reversibleAtW vcS8 m9 :=
  ⟨vcS9, [rm9], vc_step_9, run_one vc_ret_9⟩
private theorem vc_rev_10 : reversibleAtW vcS9 m10 :=
  ⟨vcS10, [rm10], vc_step_10, run_one vc_ret_10⟩
private theorem vc_rev_11 : reversibleAtW vcS10 m11 :=
  ⟨vcS11, [rm11], vc_step_11, run_one vc_ret_11⟩
private theorem vc_rev_12 : reversibleAtW vcS11 m12 :=
  ⟨vcS12, [rm12], vc_step_12, run_one vc_ret_12⟩

private theorem vc_shuffle : ShufflePlayW vcS [m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12] vcS12 :=
  (.cons vc_rev_1 vc_step_1 (.cons vc_rev_2 vc_step_2 (.cons vc_rev_3 vc_step_3 (.cons vc_rev_4 vc_step_4 (.cons vc_rev_5 vc_step_5 (.cons vc_rev_6 vc_step_6 (.cons vc_rev_7 vc_step_7 (.cons vc_rev_8 vc_step_8 (.cons vc_rev_9 vc_step_9 (.cons vc_rev_10 vc_step_10 (.cons vc_rev_11 vc_step_11 (.cons vc_rev_12 vc_step_12 (.nil vcS12)))))))))))))

private theorem vc_orbit : RevEqW vcS vcT := by
  have h := shufflePlayW_revEqW vc_shuffle
  rwa [vcS12_eq_vcT] at h

theorem vc_sameOrbit : sameOrbitSetoid.r vcS vcT := RevEqW_symm vc_orbit


/-- The 6C seat changes: 7D at vcS, 7H at vcT. -/
private theorem vc_seat6C_s :
    seatOf vcS (vcC .club .six) = some (Sum.inr (vcC .diamond .seven)) := by rfl
private theorem vc_seat6C_t :
    seatOf vcT (vcC .club .six) = some (Sum.inr (vcC .heart .seven)) := by rfl

/-- 7H is not a pile top at vcS (buried under 6S,5D on p1). -/
private theorem vc_top7H_s : vcS.pileOfTop (vcC .heart .seven) = none := by rfl

/-- 6C carries no origin floater license at vcS. -/
private theorem vc_not_floater6C : ¬ FloaterSpec vcS (vcC .club .six) := by
  intro h
  unfold FloaterSpec at h
  rcases h with ⟨z, a, hseat, hhold, hinner⟩ | ⟨a, hseat, hking, hhid, hvac⟩
  · -- seat = inr 7D
    rw [vc_seat6C_s] at hseat
    injection hseat with hz
    injection hz with hz
    rw [← hz] at hinner
    -- 7D.twin = 7H, whose top is none
    rcases hinner with ⟨k, htop⟩ | ⟨hk, -⟩
    · rw [show (vcC .diamond .seven).twin = vcC .heart .seven from rfl,
          vc_top7H_s] at htop
      exact absurd htop (by simp)
    · exact absurd hk (by decide)
  · rw [vc_seat6C_s] at hseat
    exact absurd hseat (by simp)

/-- 6C moves between the endpoints, so a bare-cargo equivalence would
have to license it at vcS; it is not licensed. -/
theorem vc_not_bareCargo : ¬ BareCargoEquiv vcS vcT := by
  intro h
  obtain ⟨-, hlic, -⟩ := (bareCargo_iff_split vcS_wf vcT_wf).mp h
  have hchg : seatOf vcS (vcC .club .six) ≠ seatOf vcT (vcC .club .six) := by
    rw [vc_seat6C_s, vc_seat6C_t]
    intro hcon
    injection hcon with h1
    injection h1 with h2
    exact absurd h2 (by decide)
  exact vc_not_floater6C (hlic _ hchg)

/-- Hence no cargo path vcS -> vcT. -/
theorem vc_not_cargoPath : ¬ CargoPath vcS vcT := by
  intro h
  exact vc_not_bareCargo (cargoPath_bareCargo vcS_wf h)

/-- **THE EQUAL-RUNG BOUNDARY CERTIFICATE.**  The pair `vcS/vcT` is
well-formed, rung-equal, saturated, class-mate, and cargo-separated.
This is the exact configuration `SatDifferFork` cannot see and
`ArmDichotomy` must cover. -/
theorem vc_equalRung_boundary :
    vcS.WF ∧ vcT.WF ∧ (∀ σ, rungAt vcS σ = rungAt vcT σ) ∧
      SSaturated vcS ∧ SSaturated vcT ∧
      sameOrbitSetoid.r vcS vcT ∧ ¬ BareCargoEquiv vcS vcT :=
  ⟨vcS_wf, vcT_wf, vc_rungs, vcS_sat, vcT_sat, vc_sameOrbit, vc_not_bareCargo⟩

/-- **WHAT `ArmDichotomy` MUST SUPPLY HERE.**  On this boundary the
dichotomy's first branch is refuted, so the residue forces a class-wide
fork.  (This is a consequence of the residue, not a proof of it.) -/
theorem vc_armDichotomy_fork (h : ArmDichotomy) :
    ∃ F x, sameOrbitSetoid.r vcS F ∧ ForkWitness F x := by
  rcases h vcS vcT vcS_sat vcT_sat vc_sameOrbit with hbc | hfork
  · exact absurd hbc vc_not_bareCargo
  · exact hfork
def drawKc (s : Suit) (r : Rank) : Card := ⟨s, r⟩

def drawEmptyPile : Pile := ⟨[], []⟩

/-- The 48-card non-king foundation. -/
def drawFound (s : Suit) : List Card := (Suit.upCards s).take 12

def drawD0 : State where
  found := drawFound
  piles := fun _ => drawEmptyPile
  stock := [drawKc .spade .king]
  waste := [drawKc .heart .king, drawKc .diamond .king, drawKc .club .king]
  drawStep := 1

def drawD1 : State where
  found := drawFound
  piles := fun _ => drawEmptyPile
  stock := []
  waste := [drawKc .spade .king, drawKc .heart .king, drawKc .diamond .king, drawKc .club .king]
  drawStep := 1

private def drawD2 : State where
  found := drawFound
  piles := fun _ => drawEmptyPile
  stock := [drawKc .diamond .king, drawKc .heart .king, drawKc .spade .king]
  waste := [drawKc .club .king]
  drawStep := 1

private def drawD3 : State where
  found := drawFound
  piles := fun _ => drawEmptyPile
  stock := [drawKc .heart .king, drawKc .spade .king]
  waste := [drawKc .diamond .king, drawKc .club .king]
  drawStep := 1

private theorem step_d0 : State.step drawD0 Move.draw = some drawD1 := rfl

private theorem step_d1 : State.step drawD1 Move.draw = some drawD2 := rfl

private theorem step_d2 : State.step drawD2 Move.draw = some drawD3 := rfl

private theorem step_d3 : State.step drawD3 Move.draw = some drawD0 := rfl

private theorem d0_wf : drawD0.WF := by
  refine ⟨fun s => ⟨12, rfl⟩, ?_, ?_, ?_⟩
  · intro a; cases a <;> decide
  · intro c _
    rcases c with ⟨s, r⟩
    cases s <;> cases r <;> decide
  · decide

private theorem d1_wf : drawD1.WF := step_wf d0_wf step_d0

/-! ## The 4-cycle of draws -/

private theorem run_d1 : drawD1.run [Move.draw, Move.draw, Move.draw] = some drawD0 := rfl

private theorem run_d2 : drawD2.run [Move.draw, Move.draw, Move.draw] = some drawD1 := rfl

private theorem run_d3 : drawD3.run [Move.draw, Move.draw, Move.draw] = some drawD2 := rfl

private theorem rev_d0 : reversibleAtW drawD0 Move.draw :=
  ⟨drawD1, [Move.draw, Move.draw, Move.draw], step_d0, run_d1⟩

private theorem rev_d1 : reversibleAtW drawD1 Move.draw :=
  ⟨drawD2, [Move.draw, Move.draw, Move.draw], step_d1, run_d2⟩

private theorem rev_d2 : reversibleAtW drawD2 Move.draw :=
  ⟨drawD3, [Move.draw, Move.draw, Move.draw], step_d2, run_d3⟩

private theorem rev_d3 : reversibleAtW drawD3 Move.draw :=
  ⟨drawD0, [Move.draw, Move.draw, Move.draw], step_d3, by
    -- drawD0.run [draw,draw,draw] = some drawD3
    rfl⟩

/-- `drawD1 → drawD2 → drawD3 → drawD0`, every letter a reversible draw. -/
private theorem shuffle_d1_d0 :
    ShufflePlayW drawD1 [Move.draw, Move.draw, Move.draw] drawD0 :=
  Walk.cons rev_d1 step_d1
    (Walk.cons rev_d2 step_d2
      (Walk.cons rev_d3 step_d3 (Walk.nil drawD0)))

/-- `drawD0 → drawD1`. -/
private theorem shuffle_d0_d1 : ShufflePlayW drawD0 [Move.draw] drawD1 :=
  Walk.cons rev_d0 step_d0 (Walk.nil drawD1)

/-- **THE DRAW ROTATION IS AN SW CYCLE.**  The forward and return draw
rounds make `drawD0` and `drawD1` SW-rotation mates. -/
theorem draw_swRotW : SWRotW drawD0 drawD1 :=
  ⟨[Move.draw], [Move.draw, Move.draw, Move.draw],
    ⟨shuffle_d0_d1, by simp⟩, ⟨shuffle_d1_d0, by simp⟩⟩

/-- **THE DRAW IS A FLAT FIBER.**  The forward draw and the three-draw
return are `FlatPath`s, so the two states are `BareFlatEquiv` — the
draw-plus-cargo fiber. -/
theorem draw_bareFlat : BareFlatEquiv drawD0 drawD1 :=
  ⟨Steps.cons (FlatStep.draw step_d0 rev_d0) (Steps.refl drawD1),
   Steps.cons (FlatStep.draw step_d1 rev_d1)
     (Steps.cons (FlatStep.draw step_d2 rev_d2)
       (Steps.cons (FlatStep.draw step_d3 rev_d3) (Steps.refl drawD0)))⟩

/-- **The two states are in one macro class.**  `sameOrbitSetoid.r drawD0 drawD1`
is `RevEqW drawD1 drawD0`, so the witness is `drawD1 → drawD0` with the reverse
`drawD0 → drawD1`. -/
theorem draw_sameOrbit : sameOrbitSetoid.r drawD0 drawD1 :=
  ⟨[Move.draw, Move.draw, Move.draw], shuffle_d1_d0, [Move.draw], shuffle_d0_d1⟩


/-! ## The empty-tableau invariant

Along any reversible play from `drawD0` the tableau stays empty and the
foundations stay the fixed 48-card non-king set.  The only reversible
letter at such a state is the draw, and the draw keeps both fields. -/

private def DrawInv (st : State) : Prop :=
  (∀ a, (st.piles a).hidden = [] ∧ (st.piles a).faceUp = []) ∧
  (∀ s, st.found s = drawFound s)

private theorem drawInv_face {st : State} (hinv : DrawInv st) :
    ∀ a, (st.piles a).faceUp = [] := fun a => (hinv.1 a).2

private theorem firstWhere_false {α : Type} (l : List α) :
    firstWhere (fun _ => false) l = none := by
  induction l with
  | nil => rfl
  | cons x t ih => simp [firstWhere, ih]

private theorem topOf_eq_none {st : State}
    (hp : ∀ a, (st.piles a).faceUp = []) (a : Anchor) : st.topOf a = none := by
  show lastOf (st.piles a).faceUp = none
  rw [hp a]
  rfl

private theorem pileOfTop_eq_none {st : State}
    (hp : ∀ a, (st.piles a).faceUp = []) (c : Card) : st.pileOfTop c = none := by
  unfold State.pileOfTop
  have hfun : (fun a => decide (st.topOf a = some c)) = (fun _ => false) := by
    funext a
    rw [topOf_eq_none hp a]
    rfl
  rw [hfun, firstWhere_false]

private theorem pileHolding_eq_none {st : State}
    (hp : ∀ a, (st.piles a).faceUp = []) (c : Card) : st.pileHolding c = none := by
  unfold State.pileHolding
  have hfun : (fun a => decide (c ∈ (st.piles a).faceUp)) = (fun _ => false) := by
    funext a
    rw [hp a]
    rfl
  rw [hfun, firstWhere_false]

private theorem emptyPile_isEmpty {st : State} (hinv : DrawInv st) (a : Anchor) :
    (st.piles a).isEmpty = true := by
  obtain ⟨hh, hf⟩ := hinv.1 a
  unfold Pile.isEmpty
  rw [hh, hf]

private theorem foundTop_eq_queen {st : State} (hinv : DrawInv st) (s : Suit) :
    st.foundTop s = some (drawKc s .queen) := by
  unfold State.foundTop
  rw [hinv.2 s]
  cases s <;> rfl

private theorem canPlace_queen_false {st : State} (hinv : DrawInv st)
    (c : Card) (hc : c.rank = Rank.queen) (b : Base) :
    st.canPlace c b = false := by
  cases b with
  | inl a =>
      rw [canPlace_inl_unfold, emptyPile_isEmpty hinv a, hc]
      rfl
  | inr z =>
      rw [canPlace_inr_eq, pileOfTop_eq_none (drawInv_face hinv) z]

/-- At an `DrawInv` state the cargo span is trivial: no `tabToTab` letter
can fire, so `CanRaiseS` collapses to the vanilla `CanRaise`. -/
private theorem canRaise_of_canRaiseS {st : State} (hinv : DrawInv st) {c : Card}
    (h : CanRaiseS st c) : CanRaise st c := by
  obtain ⟨z, hz, hcr⟩ := h
  have hz' : z = st := by
    cases hz with
    | refl => rfl
    | cons hleg _ =>
        obtain ⟨c', b, hstep, _hrev⟩ := hleg
        rw [step_tabToTab_eq, pileHolding_eq_none (drawInv_face hinv) c'] at hstep
        simp at hstep
  rw [hz'] at hcr
  exact hcr

private theorem not_canRaise {st : State} (hinv : DrawInv st) {c : Card}
    (h : CanRaise st c) : False := by
  obtain ⟨-, a, hpo, -⟩ := h
  rw [pileOfTop_eq_none (drawInv_face hinv) c] at hpo
  simp at hpo

private theorem ssaturated_of_inv {st : State} (hinv : DrawInv st) : SSaturated st := by
  intro c h
  exact not_canRaise hinv (canRaise_of_canRaiseS hinv h)

private theorem inv_d0 : DrawInv drawD0 := ⟨fun _ => ⟨rfl, rfl⟩, fun _ => rfl⟩

private theorem inv_d1 : DrawInv drawD1 := ⟨fun _ => ⟨rfl, rfl⟩, fun _ => rfl⟩

/-- A reversible step preserves the invariant. -/
private theorem inv_step {st st' : State} {m : Move}
    (hinv : DrawInv st) (hstep : State.step st m = some st')
    (hrev : reversibleAtW st m) : DrawInv st' := by
  have hm : m = Move.draw := by
    cases m with
    | draw => rfl
    | wasteToFound c =>
        exact absurd hrev (wasteToFound_not_reversibleAtW st c)
    | wasteToTab c b =>
        exact absurd hrev (wasteToTab_not_reversibleAtW st c b)
    | tabToFound c =>
        exfalso
        rw [step_tabToFound_eq, pileOfTop_eq_none (drawInv_face hinv) c] at hstep
        simp at hstep
    | foundToTab c b =>
        exfalso
        rw [step_foundToTab_eq, foundTop_eq_queen hinv c.suit] at hstep
        by_cases hq : drawKc c.suit .queen = c
        · have hcr : c.rank = Rank.queen := by rw [← hq]; rfl
          rw [canPlace_queen_false hinv c hcr b] at hstep
          simp [hq] at hstep
        · simp [hq] at hstep
    | tabToTab c b =>
        exfalso
        rw [step_tabToTab_eq, pileHolding_eq_none (drawInv_face hinv) c] at hstep
        simp at hstep
  subst hm
  refine ⟨?_, ?_⟩
  · intro a
    have hp : st'.piles = st.piles := stepDraw_piles hstep
    rw [hp]
    exact hinv.1 a
  · intro s
    have hf : st'.found = st.found := stepDraw_found hstep
    rw [hf]
    exact hinv.2 s

/-- The invariant propagates along a witness shuffle. -/
private theorem inv_walk {st W : State} {ρ : List Move}
    (h : ShufflePlayW st ρ W) : DrawInv st → DrawInv W := by
  induction h with
  | nil => exact id
  | cons hlet hstep _ ih => exact fun hinv => ih (inv_step hinv hstep hlet)


/-! ## The counterexample facts -/

/-- A class-mate of `drawD0` inherits the empty-tableau invariant: the
witness shuffle `drawD0 → F` (the reverse half of `RevEqW F drawD0`). -/
theorem ssaturated_of_sameOrbit {F : State}
    (hF : sameOrbitSetoid.r drawD0 F) : SSaturated F := by
  obtain ⟨σ, hσ, τ, hτ⟩ := hF
  exact ssaturated_of_inv (inv_walk hτ inv_d0)

/-- **No fork in the class of `drawD0`.**  Every class-mate is saturated, so
the `forkState` iff can never supply its S-live pair. -/
theorem no_fork_of_sameOrbit {F : State}
    (hF : sameOrbitSetoid.r drawD0 F) : ¬ forkState F := by
  intro hfs
  obtain ⟨x, hx, _⟩ := hfs
  exact ssaturated_of_sameOrbit hF x ((hx x).mp (Or.inl rfl))

/-- The stock differs, so the two states are in different cargo fibers. -/
theorem not_bareCargo_d0_d1 : ¬ BareCargoEquiv drawD0 drawD1 :=
  not_bareCargo_of_stock_ne (by decide)

/-- `drawD0` and `drawD1` lie at the same rung vector. -/
theorem rung_d0_d1 : RungEq drawD0 drawD1 := by
  intro σ
  rfl

/-- Public aliases for the counterexample data. -/
theorem draw_d0_wf : drawD0.WF := d0_wf

theorem draw_d1_wf : drawD1.WF := d1_wf

theorem draw_ss_d0 : SSaturated drawD0 := ssaturated_of_inv inv_d0

theorem draw_ss_d1 : SSaturated drawD1 := ssaturated_of_inv inv_d1

/-- **The draw counterexample refutes `SatEqualFork`.** -/
theorem satEqualFork_draw_false : ¬ SatEqualFork := by
  intro h
  rcases h drawD0 drawD1 (ssaturated_of_inv inv_d0) (ssaturated_of_inv inv_d1)
      draw_sameOrbit (fun σ => rfl) with hbc | ⟨F, x, hF, hfx⟩
  · exact not_bareCargo_d0_d1 hbc
  · exact no_fork_of_sameOrbit hF (forkWitness_forkState hfx)

/-- **The draw counterexample refutes `ArmDichotomy`.** -/
theorem armDichotomy_draw_false : ¬ ArmDichotomy :=
  fun h => satEqualFork_draw_false (satEqualFork_of_armDichotomy h)

/-! ## The amended target

The first branch must be the rung ledger equality `RungEq`, not the
cargo fiber: a reversible draw changes the cargo fiber while preserving
the rungs and the saturation grade. -/


/-- The four-suit enumeration decides the rung mismatch (a local
re-proof of `ArmSplit`'s private instance, avoiding `Classical`). -/
private theorem rungEq_or_differ (u v : State) :
    RungEq u v ∨ ∃ σ : Suit, rungAt u σ ≠ rungAt v σ := by
  by_cases hs : rungAt u .spade = rungAt v .spade
  · by_cases hh : rungAt u .heart = rungAt v .heart
    · by_cases hd : rungAt u .diamond = rungAt v .diamond
      · by_cases hc : rungAt u .club = rungAt v .club
        · left
          intro σ
          cases σ <;> assumption
        · exact Or.inr ⟨.club, hc⟩
      · exact Or.inr ⟨.diamond, hd⟩
    · exact Or.inr ⟨.heart, hh⟩
  · exact Or.inr ⟨.spade, hs⟩

/-- **The amended dichotomy is exactly `SatDifferFork`.**  The `RungEq`
branch is the complement of the differing-rung premise, so the two
statements are one case split apart. -/
theorem armDichotomyRung_iff_satDifferFork :
    ArmDichotomyRung ↔ SatDifferFork := by
  constructor
  · intro h u v hu hv horb hdiff
    rcases h u v hu hv horb with hre | hfork
    · obtain ⟨σ, hσ⟩ := hdiff
      exact absurd (hre σ) hσ
    · exact hfork
  · intro hD u v hu hv horb
    rcases rungEq_or_differ u v with hre | hdiff
    · exact Or.inl hre
    · exact Or.inr (hD u v hu hv horb hdiff)

/-! ## The battery -/
#print axioms vcS_sat
#print axioms vcT_sat
#print axioms vc_sameOrbit
#print axioms vc_not_cargoPath
#print axioms vcS_wf
#print axioms vcT_wf
#print axioms vc_rungs
#print axioms vc_not_bareCargo
#print axioms vc_equalRung_boundary
#print axioms vc_armDichotomy_fork
#print axioms satEqualFork_draw_false
#print axioms armDichotomy_draw_false
#print axioms armDichotomyRung_iff_satDifferFork
#print axioms draw_sameOrbit
#print axioms draw_swRotW
#print axioms draw_bareFlat
#print axioms draw_d0_wf
#print axioms draw_d1_wf
#print axioms draw_ss_d0
#print axioms draw_ss_d1
#print axioms ssaturated_of_inv
#print axioms ssaturated_of_sameOrbit
#print axioms no_fork_of_sameOrbit
#print axioms not_bareCargo_d0_d1
#print axioms rung_d0_d1