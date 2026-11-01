import Orig2.ForkEqualRungMin
import Orig2.ForkEqualRungDist
import Orig2.ForkMountainGate

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

/-!
# EqualRung_Main — the `SplitHyp` instance, and what it does and does not refute

READ-ONLY scratch card.  No source file is modified; nothing is committed.
Zero `sorry`, zero `Classical.choice`, zero `native_decide`; axiom battery at
the tail.

## SCOPE — read this first

The mountain hypothesis was **re-gated in source** while this card was being
written:

```lean
-- Orig2/ForkMountainGate.lean
MountainGate.RungDiffers u v           := ∃ σ : Suit, rungAt u σ ≠ rungAt v σ
MountainGate.MountainAtSplitsDiffering :=
  ∀ (split data), RungDiffers u v → SplitHyp … → MountainSplit left right
```

`Direct.MountainAtSplits` (and `Frontier.MountainSplitHyp`) are now marked
**UNDER-GATED**; `Orig2/ForkGatedTower.lean` re-derives the consumer tower from
`MountainAtSplitsDiffering`.

The witness transcribed here has **equal** rung vectors `(4,0,3,2)` at its
endpoints, so it lies strictly **outside** `RungDiffers`.  Therefore:

* it refutes only the **under-gated** `Direct.MountainAtSplits`, which the
  campaign has already stopped citing;
* it does **not** touch `MountainAtSplitsDiffering`, `ForkGatedTower`,
  `MountainShape` or `SatDifferForkWF`.

It is recorded as **OUT OF SCOPE**, as an artifact, not as a kill.

## What is certified here

* `valleySplitAt` / `splitHyp_of_minimal` — the full `SplitKit.SplitHyp`
  instance at `F = s11`, **given** minimality of the play (`WitnessMinimality`
  is the one open Bool of `Orig2/ForkEqualRungMin.lean` §5b);
* `not_mountainSplit` — unconditionally, the split's left leg contains the
  raise `m3 = raise 3C`, so `MountainKit.MountainSplit left right` is false;
* `mountainAtSplits_false_of_minimal` — `¬ Direct.MountainAtSplits` follows
  from that single open hypothesis.
-/

namespace EqualRung

/-! ## §1. The valley split of the witness play -/

/-- **THE VALLEY SPLIT AT `s11`.**  The last pull of the down leg is `m9`
(`3C` onto `4D`), followed by the one free slide `m10` (`2D` onto `3C`); the up
leg opens with `m11` (`raise 3S`). -/
theorem valleySplitAt : ValleyElim.ValleySplitAt s0 s13 rho s11 :=
  ⟨left, right, cpc, drc, cb, pre, post, tail,
   rho_eq, play_left, play_right, left_eq, post_free, right_eq⟩

/-- **THE `SplitHyp` INSTANCE** — every conjunct.  Minimality is the only
hypothesis, and it is exactly `WitnessMinimality`. -/
theorem splitHyp_of_minimal (hmin : WitnessMinimality) :
    SplitKit.SplitHyp s0 s13 rho s11 left right cpc drc cb pre post tail :=
  ⟨s0_wf, s0_sat, s13_sat, play, valleySplitAt,
   (fun ρ' h' => hmin ρ' h'),
   rho_eq, play_left, play_right, left_eq, post_free, right_eq⟩

/-- The left leg carries a raise (`m3 = raise 3C`). -/
theorem left_has_raise : Bubble.IsRaise m3 :=
  ⟨crd .club .three, rfl⟩

/-- **`MountainSplit` FAILS AT THIS SPLIT** — unconditionally: the left leg is
not raise-free.  (`MountainSplit α β = (∀ m ∈ α, ¬ IsRaise m) ∧ …`.) -/
theorem not_mountainSplit : ¬ MountainKit.MountainSplit left right := by
  intro h
  exact h.1 m3 (by simp [left]) left_has_raise

/-! ## §2. The conditional refutation of the under-gated form -/

/-- **`Direct.MountainAtSplits` IS FALSE** (given the one open BFS equation).
This is the *under-gated* form; see the header — the campaign now uses
`MountainGate.MountainAtSplitsDiffering`, which the equal-rung witness cannot
touch. -/
theorem mountainAtSplits_false_of_minimal (hmin : WitnessMinimality) :
    ¬ Direct.MountainAtSplits := by
  intro h
  exact not_mountainSplit (h s0 s13 rho s11 left right cpc drc cb pre post tail
    (splitHyp_of_minimal hmin))

/-! ## §2b. The unconditional form — minimality DISCHARGED

`Orig2/ForkEqualRungDist.lean` proves `witnessMinimality : WitnessMinimality` by
the distance certificate (the 392-entry table + per-state Lipschitz checks,
flat memory).  The one open Bool of the campaign's `EqualRung_Min` §5b is
therefore closed, and the refutation below carries no hypothesis. -/

/-- **THE `SplitHyp` INSTANCE — UNCONDITIONALLY.** -/
theorem splitHyp : SplitKit.SplitHyp s0 s13 rho s11 left right cpc drc cb pre post tail :=
  splitHyp_of_minimal witnessMinimality

/-- **`Direct.MountainAtSplits` IS FALSE — UNCONDITIONALLY.**  The equal-rung
13-move relocation is a genuine minimal `SSaturated → SSaturated` witness
play whose valley split has a raise in its left leg.  (The under-gated form
only; see the header — the campaign cites `MountainAtSplitsDiffering`, which
the equal-rung witness cannot touch.) -/
theorem mountainAtSplits_false : ¬ Direct.MountainAtSplits :=
  mountainAtSplits_false_of_minimal witnessMinimality

/-! ## §3. What this does NOT say

* It does **not** refute `MountainGate.MountainAtSplitsDiffering`: the endpoints
  have equal rungs, so `RungDiffers s0 s13` is false
  (`¬ MountainGate.RungDiffers s0 s13`, immediate from `rung_eq`).
* It does **not** touch `SatDifferForkWF` (same reason).
* It does **not** touch `MountainKit.MountainShape`, which carries
  `∃ σ, rungAt u σ ≠ rungAt v σ`.
* `mountainAtSplits_false_of_minimal` is conditional on `WitnessMinimality`,
  which `Orig2/ForkEqualRungMin.lean` does **not** discharge — but
  `mountainAtSplits_false` (below) discharges it via `witnessMinimality` from
  `Orig2/ForkEqualRungDist.lean`, so the refutation itself is unconditional. -/

/-- The gate really is closed on this pair. -/
theorem not_rungDiffers : ¬ MountainGate.RungDiffers s0 s13 := by
  rintro ⟨σ, hσ⟩
  exact hσ (rung_eq σ)

end EqualRung

/-! ## §4. Axiom battery -/

#print axioms EqualRung.skey_inj
#print axioms EqualRung.step0
#print axioms EqualRung.play
#print axioms EqualRung.s0_wf
#print axioms EqualRung.s13_wf
#print axioms EqualRung.s0_sat
#print axioms EqualRung.s13_sat
#print axioms EqualRung.rung_eq
#print axioms EqualRung.s0_ne_s13
#print axioms EqualRung.step_mem_allMoves
#print axioms EqualRung.succ_mem_succsOf
#print axioms EqualRung.memCode_of_mem
#print axioms EqualRung.eq_of_memCode
#print axioms EqualRung.mem_of_memCode
#print axioms EqualRung.ReachLE_mono
#print axioms EqualRung.ReachLE_succ
#print axioms EqualRung.walk_one
#print axioms EqualRung.exists_snoc
#print axioms EqualRung.walk_last
#print axioms EqualRung.self_mem_reachN
#print axioms EqualRung.reach_step_mem
#print axioms EqualRung.reach_spec
#print axioms EqualRung.witnessMinimality_of_bfs
#print axioms EqualRung.valleySplitAt
#print axioms EqualRung.splitHyp_of_minimal
#print axioms EqualRung.left_has_raise
#print axioms EqualRung.not_mountainSplit
#print axioms EqualRung.mountainAtSplits_false_of_minimal
#print axioms EqualRung.splitHyp
#print axioms EqualRung.mountainAtSplits_false
#print axioms EqualRung.not_rungDiffers
