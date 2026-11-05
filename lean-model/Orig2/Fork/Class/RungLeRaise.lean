import Orig2.Fork.Class.ForkRaiseReorderKit
import Orig2.Fork.Class.ForkPrefixClimb

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-!
# Orig2/Fork/Class/RungLeRaise — the `(R)` reduction

`(R)` is: if `u` and `v` are in one reversible orbit and `RungLe u v`, then
some **raise-only** play (`RaiseSSeqLicensed`, i.e. slides then licensed
raises) carries `u` to a state whose rung vector is exactly `rungAt v`.

This card banks the reduction to one named progress residual:

* `ClimbProgress` — from `RungLe u v`, a same-orbit `v`, and a strict deficit,
  there is an `S`-live card of a deficient suit.

The proof is the cap-directed climb: set `cap := rungAt v`, induct on
`capSum cap - rungSum u`, fire the progress card, and recurse.  The
`PrefixOK`-styled climb lives in `ForkPrefixClimb`; this card replaces its
static `PrefixOK` start by the per-step progress residual (which is the exact
content left, and which was measured true on every sampled pair: the sharp
form is "the minimal-rank surplus card is exposed by one slide").

House compliance: additive leaf, zero `sorry`, zero `Classical.choice`;
battery at the tail.
-/

namespace OneColourClosure

open PrefixClimb

/-- **THE NAMED PROGRESS RESIDUAL.**  If `u, v` are orbit-mates, `RungLe u v`
and the deficit is strict, then some `S`-live card sits on a deficient suit.
This is the only mathematical input of the `(R)` theorem.

Sharp measured form (not needed for the induction): the minimal-rank surplus
card is exposed by one reversible slide, and so is every equal-rank tie. -/
def ClimbProgress : Prop :=
  ∀ (u v : State), u.WF → sameOrbitSetoid.r u v → RungLe u v →
    (∃ σ : Suit, rungAt u σ < rungAt v σ) →
    ∃ c : Card, CanRaiseS u c ∧ rungAt u c.suit < rungAt v c.suit

/-- **THE SHARP FORM (the target to prove).**  The lowest-rank deficient suit
has an `S`-live next-up card — and the same holds for every equal-rank tie
(`σ` is any suit whose deficient rung is minimal).  This implies
`ClimbProgress` (pick a minimal deficient suit), hence `(R)`.

Measured: every minimal-rank surplus card is exposed by one reversible slide
(`Temp/sorted_play_search.py`: 262/262 sampled `RungLe` pairs; the sharp form
180/180 minimal cards). -/
def MinCardOneSlideExposed : Prop :=
  ∀ (u v : State) (σ : Suit), u.WF → sameOrbitSetoid.r u v → RungLe u v →
    rungAt u σ < rungAt v σ →
    (∀ τ : Suit, rungAt u τ < rungAt v τ → rungAt u σ ≤ rungAt u τ) →
    ∃ c : Card, c.suit = σ ∧ c.rank.toIdx = rungAt u σ ∧ CanRaiseS u c

/-- **THE `freeCardS` FORM OF THE RESIDUAL (Bool-shaped).**  Some deficient
next-up card is *tableau-free*: `freeCardS u c = true`.  By
`canRaiseS_split` this is `CanRaiseS` (the `nextUp` half is the given
`c.rank.toIdx = rungAt u c.suit`).

`freeCardS` is the licence (`below c ≠ [] ∨ hidden = [] ∧ c = king`) plus the
run-or-twin disjunct (`run = [] ∨ pileOfTop u c.twin ≠ none`); see
`Orig2/Substrate/CargoRaise.lean:835`.  Measured: the minimal deficient card
satisfies it on every sampled pair (180/180), and `Orig/RunOrTwin.lean`'s
`mutualFreeze` is the tool for the run-or-twin half. -/
def MinCardFree : Prop :=
  ∀ (u v : State), u.WF → sameOrbitSetoid.r u v → RungLe u v →
    (∃ σ : Suit, rungAt u σ < rungAt v σ) →
    ∃ c : Card,
      c.rank.toIdx = rungAt u c.suit ∧
      rungAt u c.suit < rungAt v c.suit ∧
      freeCardS u c = true

/-- **`ClimbProgress` from the `freeCardS` residual.**  The licence split
(`canRaiseS_split`) turns `nextUp ∧ freeCardS` into `CanRaiseS`. -/
theorem climbProgress_of_minCardFree (h : MinCardFree) : ClimbProgress := by
  intro u v hu horb hle hne
  obtain ⟨c, hnext, hdef, hfree⟩ := h u v hu horb hle hne
  refine ⟨c, ?_, hdef⟩
  rw [canRaiseS_split hu]
  exact ⟨TwinKit.nextUp_true_iff.mpr hnext.symm, hfree⟩

/-- **`(R)`, from the progress residual.**  `RungLe u v` (same orbit) gives a
licensed raise-only play from `u` to the rung of `v`. -/
theorem rungLe_raiseReach_of_climbProgress (hprog : ClimbProgress) :
    ∀ (u v : State), u.WF → sameOrbitSetoid.r u v → RungLe u v →
      ∃ (ws : List Card) (z : State),
        RaiseSSeqLicensed u ws z ∧ ∀ σ : Suit, rungAt z σ = rungAt v σ := by
  intro u v₀ hu₀ horb₀ hle₀
  have main : ∀ n : Nat,
      ∀ (u v : State), u.WF → sameOrbitSetoid.r u v → RungLe u v →
        PrefixClimb.capSum (fun σ => rungAt v σ) - Drain.rungSum u ≤ n →
        ∃ (ws : List Card) (z : State),
          RaiseSSeqLicensed u ws z ∧ ∀ σ : Suit, rungAt z σ = rungAt v σ := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro u v hu horb hle hbound
      let cap : Suit → Nat := fun σ => rungAt v σ
      have hunder : PrefixClimb.Under u cap := hle
      have hleSum : Drain.rungSum u ≤ PrefixClimb.capSum cap :=
        PrefixClimb.rungSum_le_capSum hunder
      by_cases hfin : PrefixClimb.capSum cap = Drain.rungSum u
      · -- deficit zero: the rungs already agree
        have hrungs : ∀ σ : Suit, rungAt u σ = cap σ :=
          PrefixClimb.rungs_eq_of_sum_eq hunder hfin.symm
        exact ⟨[], u, RaiseSSeqLicensed.nil u, hrungs⟩
      · -- strict deficit: fire the progress card once, then recurse
        have hlt : Drain.rungSum u < PrefixClimb.capSum cap := by
          rcases Nat.lt_or_eq_of_le hleSum with h | h
          · exact h
          · exact absurd h.symm hfin
        obtain ⟨σ, hσ⟩ := PrefixClimb.exists_lt_of_sum_lt hunder hlt
        have hne : ∃ σ : Suit, rungAt u σ < rungAt v σ := ⟨σ, hσ⟩
        obtain ⟨c, hcS, hccap⟩ := hprog u v hu horb hle hne
        -- fire the licensed letter
        obtain ⟨z₀, hpath, hcan⟩ := hcS
        have hcS' : CanRaiseS u c := ⟨z₀, hpath, hcan⟩
        obtain ⟨z', hstep⟩ := step_tabToFound_of_canRaise hcan
        have hz₀wf : z₀.WF := cargoPath_wf hu hpath
        have hz'wf : z'.WF := step_wf hz₀wf hstep
        -- `Under` transport across the cargo path and the raise
        have hcap₀ : rungAt z₀ c.suit < cap c.suit := by
          show rungAt z₀ c.suit < rungAt v c.suit
          rw [← rungAt_cargoPath hpath c.suit]
          exact hccap
        have hunder₀ : PrefixClimb.Under z₀ cap := by
          intro τ
          show rungAt z₀ τ ≤ rungAt v τ
          rw [← rungAt_cargoPath hpath τ]
          exact hunder τ
        have hunder' : PrefixClimb.Under z' cap :=
          PrefixClimb.Under.step hunder₀ hstep hcap₀
        -- orbit: u ~ z₀ ~ z' ~ v
        have hu_z₀ : sameOrbitSetoid.r u z₀ := sameOrbit_of_cargoPath hpath
        have hz₀_z' : sameOrbitSetoid.r z₀ z' :=
          Drain.sameOrbit_of_step
            (DrainClose.reversibleAtW_tabToFound_of_canRaise hz₀wf hcan) hstep
        have hu_z' : sameOrbitSetoid.r u z' := sameOrbitSetoid.iseqv.trans hu_z₀ hz₀_z'
        have hz'_v : sameOrbitSetoid.r z' v :=
          sameOrbitSetoid.iseqv.trans (sameOrbitSetoid.iseqv.symm hu_z') horb
        -- the rank sum climbs by exactly one
        have hsum₀ : Drain.rungSum z₀ = Drain.rungSum u := by
          have hmap : Suit.all.map (fun s => rungAt z₀ s) =
              Suit.all.map (fun s => rungAt u s) :=
            List.map_congr_left (fun τ _ => (rungAt_cargoPath hpath τ).symm)
          unfold Drain.rungSum
          rw [hmap]
        have hsum' : Drain.rungSum z' = Drain.rungSum z₀ + 1 :=
          DrainClose.rungSum_raise hstep
        have hrung' : Drain.rungSum z' = Drain.rungSum u + 1 := by
          rw [hsum', hsum₀]
        have hbound' : PrefixClimb.capSum cap - Drain.rungSum u ≤ n := hbound
        have hdec : PrefixClimb.capSum cap - Drain.rungSum z' < n := by
          have hpos : 0 < PrefixClimb.capSum cap - Drain.rungSum u :=
            Nat.sub_pos_of_lt hlt
          have hEq : PrefixClimb.capSum cap - Drain.rungSum z' =
              PrefixClimb.capSum cap - Drain.rungSum u - 1 := by
            rw [hrung', Nat.sub_sub]
          rw [hEq]
          exact Nat.lt_of_lt_of_le (Nat.sub_lt hpos Nat.one_pos) hbound'
        -- recurse from z'
        obtain ⟨ws, z, hseq, hrungs⟩ :=
          ih (PrefixClimb.capSum cap - Drain.rungSum z') hdec
            z' v hz'wf hz'_v hunder' (Nat.le_refl _)
        -- prepend the first letter (word order: `ws ++ [c]`)
        have hletter : RaiseSSeqLicensed u [c] z' :=
          RaiseSSeqLicensed.cons (RaiseSSeqLicensed.nil u) hcS' hpath hstep
        have hcombined : RaiseSSeqLicensed u (ws ++ [c]) z :=
          RaiseSSeqLicensed.append hletter hseq
        exact ⟨ws ++ [c], z, hcombined, hrungs⟩
  exact main (PrefixClimb.capSum (fun σ => rungAt v₀ σ) - Drain.rungSum u)
    u v₀ hu₀ horb₀ hle₀ (Nat.le_refl _)

#print axioms climbProgress_of_minCardFree
#print axioms rungLe_raiseReach_of_climbProgress
#check @ClimbProgress
#check @MinCardFree
#check @MinCardOneSlideExposed
#check @climbProgress_of_minCardFree
#check @rungLe_raiseReach_of_climbProgress

end OneColourClosure
