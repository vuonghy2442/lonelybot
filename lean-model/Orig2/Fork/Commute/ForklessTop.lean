import Orig2.Fiber.SWDichotomy
import Orig2.Fork.Class.CeilingBridge
import Orig2.Fork.Class.ForkOneColourClosure
import Orig2.Fork.Split.ForkDrainClose
import Orig2.Substrate.CargoRaise
import Orig2.Fork.Local.ForkCriticalPair
import Orig2.Fork.Class.ForkTwinJoin

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-!
# ForklessTop_Main — the rung top of a forkless class

Scratch card (`Temp/`), READ-ONLY on `Orig2/`; nothing committed.
No `sorry`, no `Classical.choice`, no `native_decide`.

## What is proved

1. `exists_armRaise_sameOrbit` — an S-licensed card raises to a
   same-orbit `WF` landing, one coordinate up, every other coordinate
   fixed.  (Restated from `Temp/FullJoin_Top.lean`; its proof is the
   certified `canRaiseS = cargo span + reversible raise` route.)
2. `exists_saturated_above` — **THE RAISE-ONLY CLIMB.**  Every `WF`
   state has a saturated same-orbit upper bound.  The recursion measure
   is `52 - rungSum`; the live card is extracted from the certified
   decidable probe `rankSatB 13` (`Orig2/Substrate/CargoRaise.lean`), so no
   classical choice is used.  The stall of this climb is exactly
   `SSaturated`.
3. `forkless_saturated_rungs_eq` — the hypothesis shape of the brief,
   converted to the pairwise form `ForklessSatRungsAgree`.
4. `forklessHasTop_of_forklessSatRungsAgree` — saturation climb +
   pairwise rung agreement ⇒ `ForklessHasTop`.
5. `forklessHasTop_of_forklessFlatNormal` — `ForklessFlatNormalWF`
   ⇒ `ForklessHasTop`.
6. `forklessHasTop_of_satFlatFiberFork` — `SatFlatFiberFork`
   ⇒ `ForklessHasTop`, via the decidable rung-equality split (no
   classical case analysis on `BareFlatEquiv`).

## The stall, honestly

The raise-only climb has one stall: `SSaturated`.  At `WF` this is a
decidable question (`rankSatB 13`), and `exists_live_of_not_ssaturated`
turns a non-stall into an actual live card.  The *balanced* climb of
`Temp/ArgminEq_Report.md` has a different stall: at a balanced state
with both twins buried, neither twin is S-live even though the class is
not saturated.  That stall is not a fork (measured: 176/984 core,
1506/13923 random `bothblocked_noS`), and the measured escape is an
other-colour raise.  It is irrelevant to the top construction below:
the top climb never insists on keeping a chosen pair balanced, so it
raises whatever card is S-live and terminates at saturation.

House compliance: additive scratch leaf; battery at the tail.
-/

namespace ForklessTop

open OneColourClosure

/-! ## §1. Vocabulary -/

/-- **`ForklessSatRungsAgree`** — in a forkless class, any two saturated
class-mates have equal rungs.  This is the exact pairwise input the
top construction consumes. -/
def ForklessSatRungsAgree : Prop :=
  ∀ u v : State, u.WF → v.WF → Forkless u → sameOrbitSetoid.r u v →
    SSaturated u → SSaturated v → RungEq u v

/-! ## §2. Basic orbit and raise kit -/

/-- **An S-licensed card raises to a same-orbit `WF` landing.**  The
raised suit increments by one, every other rung is fixed. -/
theorem exists_armRaise_sameOrbit {F : State} {c : Card} (hF : F.WF)
    (hc : CanRaiseS F c) :
    ∃ A, ArmRaise F c A ∧ sameOrbitSetoid.r F A ∧ A.WF ∧
      ∀ σ : Suit, rungAt A σ =
        if σ = c.suit then rungAt F σ + 1 else rungAt F σ := by
  obtain ⟨z, hpath, hcan⟩ := hc
  obtain ⟨A, hstep⟩ := step_tabToFound_of_canRaise hcan
  have hzWF : z.WF := cargoPath_wf hF hpath
  have hA : ArmRaise F c A := ⟨z, hpath, hstep⟩
  have hrev : reversibleAtW z (Move.tabToFound c) :=
    DrainClose.reversibleAtW_tabToFound_of_canRaise hzWF hcan
  have hzA : sameOrbitSetoid.r z A := Drain.sameOrbit_of_step hrev hstep
  have hFz : sameOrbitSetoid.r F z := by
    obtain ⟨play, hplay⟩ := flatPath_shuffle (cargoPath_flatPath hpath)
    exact RevEqW_symm (shufflePlayW_revEqW hplay)
  exact ⟨A, hA, sameOrbitSetoid.iseqv.trans hFz hzA,
    step_wf hzWF hstep, fun σ => armRaise_rung hA σ⟩

/-- `rungSum` is determined by the four rung coordinates. -/
theorem rungSum_eq_of_rung_eq {u v : State}
    (h : ∀ σ : Suit, rungAt u σ = rungAt v σ) :
    Drain.rungSum u = Drain.rungSum v := by
  unfold Drain.rungSum
  congr 1
  exact List.map_congr_left (fun s _ => h s)

/-! ## §3. The decidable saturation frontier -/

theorem ssaturated_of_rankSatB_true {st : State} (hwf : st.WF)
    (h : rankSatB 13 st = true) : SSaturated st := by
  have hRank : RankSat 13 st := (rankSatB_iff hwf 13).mp h
  intro c hc
  exact hRank c (Nat.le_of_lt (Rank.toIdx_lt c.rank)) hc

/-- A `rankSatB` failure extracts a live card constructively (the
`Drain.exists_of_all_false` kit, no `Classical.choice`). -/
theorem exists_live_of_rankSatB_false {st : State} (hwf : st.WF) {k : Nat}
    (h : rankSatB k st = false) :
    ∃ c, c.rank.toIdx ≤ k ∧ CanRaiseS st c := by
  unfold rankSatB at h
  obtain ⟨c, _hc_mem, hc⟩ := Drain.exists_of_all_false h
  have hc' : (decide (c.rank.toIdx ≤ k) && canRaiseSB st c) = true := by
    simpa using hc
  rw [Bool.and_eq_true] at hc'
  exact ⟨c, of_decide_eq_true hc'.1, (canRaiseSB_iff hwf).mp hc'.2⟩

/-- **At `WF`, a non-saturated state has an S-live card** — the decidable
frontier turns the stall test into a witness. -/
theorem exists_live_of_not_ssaturated {st : State} (hwf : st.WF)
    (h : ¬ SSaturated st) : ∃ c, CanRaiseS st c := by
  cases hb : rankSatB 13 st with
  | true => exact absurd (ssaturated_of_rankSatB_true hwf hb) h
  | false =>
      obtain ⟨c, -, hc⟩ := exists_live_of_rankSatB_false hwf hb
      exact ⟨c, hc⟩

/-! ## §4. The raise-only climb -/

/-- **`exists_saturated_above` — THE RAISE-ONLY CLIMB.**  Every `WF`
state has a saturated same-orbit class-mate whose rungs dominate the
start componentwise.  The recursion is on `52 - rungSum`; each step
raises one S-live card and strictly increases the sum. -/
theorem exists_saturated_above (u : State) (hu : u.WF) :
    ∃ w, sameOrbitSetoid.r u w ∧ w.WF ∧ SSaturated w ∧
      ∀ σ : Suit, rungAt u σ ≤ rungAt w σ := by
  have key : ∀ N (u : State), u.WF → 52 - Drain.rungSum u = N →
      ∃ w, sameOrbitSetoid.r u w ∧ w.WF ∧ SSaturated w ∧
        ∀ σ : Suit, rungAt u σ ≤ rungAt w σ := by
    intro N
    induction N using Nat.strongRecOn with
    | ind N ih =>
      intro u hu hN
      cases hb : rankSatB 13 u with
      | true =>
          exact ⟨u, sameOrbitSetoid.iseqv.refl u, hu,
            ssaturated_of_rankSatB_true hu hb, fun σ => Nat.le_refl _⟩
      | false =>
          obtain ⟨c, -, hcS⟩ := exists_live_of_rankSatB_false hu hb
          obtain ⟨A, hArm, hcls, hAwf, hrung⟩ := exists_armRaise_sameOrbit hu hcS
          obtain ⟨z, hpath, hstep⟩ := hArm
          have hsumA : Drain.rungSum A = Drain.rungSum u + 1 := by
            have hz : Drain.rungSum z = Drain.rungSum u :=
              rungSum_eq_of_rung_eq (fun σ => (rungAt_cargoPath hpath σ).symm)
            rw [DrainClose.rungSum_raise hstep, hz]
          have hN' : 52 - Drain.rungSum A < N := by
            have hleA52 := Drain.rungSum_le_52 hAwf
            have hr : Drain.rungSum u < 52 := by omega
            have hlt : 52 - (Drain.rungSum u + 1) < 52 - Drain.rungSum u :=
              Nat.sub_lt_sub_left hr (Nat.lt_succ_self (Drain.rungSum u))
            rw [hsumA, ← hN]
            exact hlt
          obtain ⟨w, hAw, hwwf, hwsat, hleA⟩ :=
            ih (52 - Drain.rungSum A) hN' A hAwf rfl
          refine ⟨w, sameOrbitSetoid.iseqv.trans hcls hAw, hwwf, hwsat, ?_⟩
          intro σ
          have huA : rungAt u σ ≤ rungAt A σ := by
            have h := hrung σ
            by_cases hσ : σ = c.suit
            · rw [ite_eq_left hσ] at h; omega
            · rw [ite_eq_right hσ] at h; omega
          exact Nat.le_trans huA (hleA σ)
  exact key (52 - Drain.rungSum u) u hu rfl

/-! ## §5. Rung agreement ⇒ top -/

/-- **`forkless_saturated_rungs_eq`** — the brief's hypothesis shape,
converted to the pairwise `ForklessSatRungsAgree` form used below. -/
theorem forkless_saturated_rungs_eq
    (h : ∀ u, u.WF → Forkless u →
      ∀ v, sameOrbitSetoid.r u v → SSaturated v → RungEq u v) :
    ForklessSatRungsAgree := by
  intro u v hu hv hfrk horb _hsu hsv
  exact h u hu hfrk v horb hsv

/-- The same row with the brief's premise written out (`∀ F, ...`) rather
than through the `Forkless` abbreviation. -/
theorem forkless_saturated_rungs_eq_explicit
    (h : ∀ u, u.WF → (∀ F, sameOrbitSetoid.r u F → ¬ forkState F) →
      ∀ v, sameOrbitSetoid.r u v → SSaturated v → RungEq u v) :
    ∀ u v, u.WF → v.WF →
      (∀ F, sameOrbitSetoid.r u F → ¬ forkState F) →
      sameOrbitSetoid.r u v → SSaturated u → SSaturated v → RungEq u v := by
  intro u v hu _hv hfrk horb _hsu hsv
  exact h u hu hfrk v horb hsv

/-- `SatDifferForkWF` gives the pairwise rung agreement
(`forkless_rungs_agree_wf`, `Orig2/Fork/Class/CeilingBridge.lean`). -/
theorem forklessSatRungsAgree_of_satDifferForkWF (h : SatDifferForkWF) :
    ForklessSatRungsAgree := by
  intro u v hu _hv hfrk horb hsu hsv
  exact forkless_rungs_agree_wf h hu horb hfrk hsu hsv

/-- `SatFlatFiberFork` gives the pairwise rung agreement.  The only
case split is on a decidable Nat equality; `not_bareFlat_of_rung_ne`
supplies the flat-fiber mismatch. -/
theorem forklessSatRungsAgree_of_satFlatFiberFork (h : SatFlatFiberFork) :
    ForklessSatRungsAgree := by
  intro u v hu _hv hfrk horb hsu hsv σ
  by_cases hEq : rungAt u σ = rungAt v σ
  · exact hEq
  · exfalso
    have hnf : ¬ BareFlatEquiv u v := not_bareFlat_of_rung_ne hEq
    obtain ⟨F, x, hF, hx⟩ := h u v hu hsu hsv horb hnf
    exact hfrk F hF (forkState_iff.mpr ⟨x, hx⟩)

/-- `ForklessFlatNormalWF` gives the pairwise rung agreement: saturated
class-mates lie in one flat fiber, and a flat path fixes every rung. -/
theorem forklessSatRungsAgree_of_forklessFlatNormal
    (h : ForklessFlatNormalWF) : ForklessSatRungsAgree := by
  intro u v hu _hv hfrk horb hsu hsv
  exact bareFlat_rung (h u v hu hsu hsv horb hfrk)

/-- **THE MAIN REDUCTION.**  The raise-only climb plus pairwise rung
agreement of saturated class-mates gives `ForklessHasTop`. -/
theorem forklessHasTop_of_forklessSatRungsAgree
    (h : ForklessSatRungsAgree) : ForklessHasTop := by
  intro u hu hfrk
  obtain ⟨w, huw, hwf, hwsat, _hleu⟩ := exists_saturated_above u hu
  refine ⟨w, huw, ?_⟩
  intro x hux σ
  obtain ⟨y, hxy, hywf, hysat, hlex⟩ :=
    exists_saturated_above x (wf_of_sameOrbit hux hu)
  have hfrkw : Forkless w := fun F hF =>
    hfrk F (sameOrbitSetoid.iseqv.trans huw hF)
  have hwx : sameOrbitSetoid.r w x :=
    sameOrbitSetoid.iseqv.trans (sameOrbitSetoid.iseqv.symm huw) hux
  have hwy : sameOrbitSetoid.r w y :=
    sameOrbitSetoid.iseqv.trans hwx hxy
  have heq : RungEq w y := h w y hwf hywf hfrkw hwy hwsat hysat
  exact Nat.le_trans (hlex σ) (Nat.le_of_eq (heq σ).symm)

/-- The brief's `forkless_saturated_rungs_eq` hypothesis consumed directly. -/
theorem forklessHasTop_of_forkless_saturated_rungs_eq
    (h : ∀ u, u.WF → Forkless u →
      ∀ v, sameOrbitSetoid.r u v → SSaturated v → RungEq u v) :
    ForklessHasTop :=
  forklessHasTop_of_forklessSatRungsAgree (forkless_saturated_rungs_eq h)

/-- The same consumer with the brief's premise written out. -/
theorem forklessHasTop_of_forkless_saturated_rungs_eq_explicit
    (h : ∀ u, u.WF → (∀ F, sameOrbitSetoid.r u F → ¬ forkState F) →
      ∀ v, sameOrbitSetoid.r u v → SSaturated v → RungEq u v) :
    ForklessHasTop :=
  forklessHasTop_of_forklessSatRungsAgree
    (forkless_saturated_rungs_eq_explicit h)

/-- **`forklessHasTop_of_forklessFlatNormal`** — the flat-normal
invariant implies the top. -/
theorem forklessHasTop_of_forklessFlatNormal
    (h : ForklessFlatNormalWF) : ForklessHasTop :=
  forklessHasTop_of_forklessSatRungsAgree
    (forklessSatRungsAgree_of_forklessFlatNormal h)

/-- The expanded form of the target, with the brief's premises written out. -/
theorem forklessHasTop_of_forklessFlatNormal_expanded
    (h : ForklessFlatNormalWF) :
    ∀ u, u.WF → (∀ F, sameOrbitSetoid.r u F → ¬ forkState F) →
      ∃ w, sameOrbitSetoid.r u w ∧
        ∀ x, sameOrbitSetoid.r u x → ∀ σ : Suit, rungAt x σ ≤ rungAt w σ :=
  forklessHasTop_of_forklessFlatNormal h

/-- **`forklessHasTop_of_satFlatFiberFork`** — the class-global flat-fiber
invariant also gives the top. -/
theorem forklessHasTop_of_satFlatFiberFork
    (h : SatFlatFiberFork) : ForklessHasTop :=
  forklessHasTop_of_forklessSatRungsAgree
    (forklessSatRungsAgree_of_satFlatFiberFork h)

/-- **`forklessHasTop_of_satDifferForkWF`** — the `WF`-gated campaign
residue gives the top. -/
theorem forklessHasTop_of_satDifferForkWF (h : SatDifferForkWF) :
    ForklessHasTop :=
  forklessHasTop_of_forklessSatRungsAgree
    (forklessSatRungsAgree_of_satDifferForkWF h)

/-- **`forklessHasTop_of_armDichotomySW`** — the SW arm dichotomy gives
the top through `satDifferForkWF_of_armDichotomySW`. -/
theorem forklessHasTop_of_armDichotomySW (h : ArmDichotomySW) :
    ForklessHasTop :=
  forklessHasTop_of_satDifferForkWF (satDifferForkWF_of_armDichotomySW h)

/-- **The strictness gap, conditional form.**  A forkless component with
a rung top but with two saturated class-mates in different flat fibers
refutes `ForklessFlatNormalWF`: the flat-normal statement carries
fiber-connectivity content that the rung projection of `ForklessHasTop`
does not mention.  (No such component is asserted to exist here; the
measured flat-fiber census is the place to look.) -/
theorem not_forklessFlatNormalWF_of_fiberSplit
    (h : ∃ u v : State, u.WF ∧ Forkless u ∧ sameOrbitSetoid.r u v ∧
      SSaturated u ∧ SSaturated v ∧ ¬ BareFlatEquiv u v ∧
      ∃ w, HasTopRung u w) :
    ¬ ForklessFlatNormalWF := by
  obtain ⟨u, v, hu, hfrk, horb, hsu, hsv, hnf, _htop⟩ := h
  intro hflat
  exact hnf (hflat u v hu hsu hsv horb hfrk)

/-- A rung top is saturated: an S-live card would raise a class-mate
strictly above the top on its suit. -/
theorem hasTopRung_ssaturated {w : State} (hw : w.WF)
    (htop : HasTopRung w w) : SSaturated w := by
  intro c hcS
  obtain ⟨A, -, hcls, -, hrung⟩ := exists_armRaise_sameOrbit hw hcS
  have hle : rungAt A c.suit ≤ rungAt w c.suit := htop.2 A hcls c.suit
  have hinc : rungAt A c.suit = rungAt w c.suit + 1 := by
    have h := hrung c.suit
    rw [ite_eq_left rfl] at h
    exact h
  omega

/-- A non-saturated state is not its own rung top. -/
theorem not_hasTopRung_self_of_not_ssaturated {w : State} (hw : w.WF)
    (h : ¬ SSaturated w) : ¬ HasTopRung w w :=
  fun htop => h (hasTopRung_ssaturated hw htop)

/-- **The balanced stall is escapable unless the state is saturated.**
This is the honest form of the "stall ⇒ other-colour raise" observation:
the raise may be any S-live card, not necessarily a card of the chosen
balanced twin pair. -/
theorem balanced_stall_escapable {z : State} (hz : z.WF) {t : Suit}
    (_hbal : rungAt z t = rungAt z t.twin) (hstall : ¬ SSaturated z) :
    ∃ c, CanRaiseS z c :=
  exists_live_of_not_ssaturated hz hstall

/-- **The balanced-stall live split.**  If a state with an exact twin live
pair is not saturated, then either some card *outside* the pair is S-live
(the other-colour escape), or both twins are S-live (the push/fork case
of `twin_pair_stack_or_fork`).  This is the precise stall dichotomy: there
is no third case. -/
theorem balanced_stall_live_split {z : State} {x : Card} (hz : z.WF)
    (hlive : TwinLivePair z x) (hstall : ¬ SSaturated z) :
    (∃ c, CanRaiseS z c ∧ c ≠ x ∧ c ≠ x.twin) ∨
      (CanRaiseS z x ∧ CanRaiseS z x.twin) := by
  obtain ⟨c, hc⟩ := exists_live_of_not_ssaturated hz hstall
  by_cases hcx : c = x
  · right
    have hx : CanRaiseS z x := by rw [← hcx]; exact hc
    exact ⟨hx, (hlive x.twin).mpr (Or.inr rfl)⟩
  · by_cases hct : c = x.twin
    · right
      have hxt : CanRaiseS z x.twin := by rw [← hct]; exact hc
      exact ⟨(hlive x).mpr (Or.inl rfl), hxt⟩
    · left
      exact ⟨c, hc, hcx, hct⟩

/-! ## §6. The raise-only / balanced lane (conditional leaves)

The top construction above is deliberately *not* the balanced climb: it
raises whatever card is S-live.  The balanced lane is the local
synchronizer, and its compiled conditional leaves are recorded here.

* `TwinJoin.RaiseOnlyData` / `TwinJoin.ArgminStepGameWF` /
  `TwinJoin.argminStepGameWF_of_raiseOnly` (`Orig2/Fork/Class/ForkRaiseOnly.lean`):
  the HIGH-raise-only datum yields the one-coordinate LOW lift.
* `TwinJoin.argmin_step_of_raiseOnly` is the local elim.
* `balanced_push_to_low_target` / `lower_push_to_common_point` and
  `twin_pair_stack_or_fork` are compiled in `Temp/PinLocal_Core.lean`
  and `Temp/PinFork_Core.lean` (see the report for exact types).  They
  are *conditional*: their per-level `hpush`/`hclimb` hypotheses are
  exactly the stall case, and the unconditional "stall ⇒ fork" is false
  (`Temp/ArgminEq_Report.md` §6).
-/

/-- The balanced lane's local elim, restated as a named conditional
leaf: a `RaiseOnlyData` at a HIGH/LOW twin pair produces a class-mate
with LOW up one and HIGH frozen. -/
theorem balanced_raiseOnly_escape {s : State} {t : Suit} {c : Card}
    (hs : s.WF) (hdata : TwinJoin.RaiseOnlyData s t c)
    (hcsu : c.suit = t.twin) :
    ∃ s'', sameOrbitSetoid.r s s'' ∧
      rungAt s'' t = rungAt s t ∧
      rungAt s'' t.twin = rungAt s t.twin + 1 :=
  TwinJoin.argmin_step_of_raiseOnly hs hdata hcsu

/-- The global RaiseOnly-to-Argmin bridge, re-exported under the local
name used in the report. -/
theorem argminStepGameWF_of_raiseOnly
    (h : ∀ (s s' : State) (t : Suit) (c : Card),
      s.WF → s'.WF → sameOrbitSetoid.r s s' →
      rungAt s t.twin ≤ rungAt s t →
      rungAt s t ≤ rungAt s' t →
      rungAt s t.twin < rungAt s' t.twin →
      c.suit = t.twin → c.rank.toIdx = rungAt s t.twin →
      TwinJoin.RaiseOnlyData s t c) :
    TwinJoin.ArgminStepGameWF :=
  TwinJoin.argminStepGameWF_of_raiseOnly h

end ForklessTop

/-! ## §7. Axiom battery -/

#print axioms ForklessTop.exists_armRaise_sameOrbit
#print axioms ForklessTop.rungSum_eq_of_rung_eq
#print axioms ForklessTop.ssaturated_of_rankSatB_true
#print axioms ForklessTop.exists_live_of_rankSatB_false
#print axioms ForklessTop.exists_live_of_not_ssaturated
#print axioms ForklessTop.exists_saturated_above
#print axioms ForklessTop.forkless_saturated_rungs_eq
#print axioms ForklessTop.forkless_saturated_rungs_eq_explicit
#print axioms ForklessTop.forklessSatRungsAgree_of_satDifferForkWF
#print axioms ForklessTop.forklessSatRungsAgree_of_satFlatFiberFork
#print axioms ForklessTop.forklessSatRungsAgree_of_forklessFlatNormal
#print axioms ForklessTop.forklessHasTop_of_forklessSatRungsAgree
#print axioms ForklessTop.forklessHasTop_of_forkless_saturated_rungs_eq
#print axioms ForklessTop.forklessHasTop_of_forkless_saturated_rungs_eq_explicit
#print axioms ForklessTop.forklessHasTop_of_forklessFlatNormal
#print axioms ForklessTop.forklessHasTop_of_forklessFlatNormal_expanded
#print axioms ForklessTop.forklessHasTop_of_satFlatFiberFork
#print axioms ForklessTop.forklessHasTop_of_satDifferForkWF
#print axioms ForklessTop.forklessHasTop_of_armDichotomySW
#print axioms ForklessTop.hasTopRung_ssaturated
#print axioms ForklessTop.not_hasTopRung_self_of_not_ssaturated
#print axioms ForklessTop.balanced_stall_escapable
#print axioms ForklessTop.balanced_stall_live_split
#print axioms ForklessTop.not_forklessFlatNormalWF_of_fiberSplit
#print axioms ForklessTop.balanced_raiseOnly_escape
#print axioms ForklessTop.argminStepGameWF_of_raiseOnly
