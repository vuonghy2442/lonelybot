import Orig2.ForkEqualRungMain

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

/-!
# Orig2/ForkEqSplitWitness — the known equal-rung witness reads off the same bracket

The only kernel-certified equal-rung minimal `SplitHyp` is
`EqualRung.splitHyp` (`Orig2/ForkEqualRungMain.lean:102`), whose split card is
`cpc = 3C`.  This card records the *letter geometry* of that witness, which is
the complement of what `MountainSplit` asks for:

* `raise 3C` fires in `pre` — i.e. in the **left** leg, before the split;
* `pull 3C` *is* the split's own pull (`m9`), so the pair is a genuine
  `pull c ; raise c` bracket of the split card — with the raise on the wrong
  side of the split.

Hence at the only known equal-rung minimal split the mountain fails on its
FIRST conjunct (raise-free left leg), while
`EqSplit.noEqualRungMountainSplit_of_slideFree` closes the other escape (a
`raise c` in the pull-free right leg, with a clean interior window).

No `sorry`, no `Classical.choice`, no `native_decide`; battery at the tail.
-/

namespace EqSplitWitness

open EqualRung

/-- The split card is `3C`. -/
theorem cpc_eq : cpc = crd .club .three := rfl

/-- The split's own pull is `pull 3C → 4D`. -/
theorem split_pull_is_pull_cpc : m9 = Move.foundToTab cpc cb := rfl

/-- **`raise c` IS IN THE LEFT LEG.**  The witness raises the split card in
`pre`, before pulling it at the split. -/
theorem raise_cpc_mem_pre : Move.tabToFound cpc ∈ pre := by
  show Move.tabToFound cpc ∈ [m0, m1, m2, m3, m4, m5, m6, m7, m8]
  have hm3 : m3 = Move.tabToFound cpc := rfl
  rw [hm3]
  simp

/-- **THE SPLIT CARD'S PULL AND ITS RAISE ARE THE SAME CARD.** -/
theorem bracket_card : pre = [m0, m1, m2] ++ Move.tabToFound cpc :: [m4, m5, m6, m7, m8] := by
  show [m0, m1, m2, m3, m4, m5, m6, m7, m8]
    = [m0, m1, m2] ++ Move.tabToFound cpc :: [m4, m5, m6, m7, m8]
  rw [show m3 = Move.tabToFound cpc from rfl]
  rfl

/-- **THE OTHER ESCAPE IS NOT THE ONE THE WITNESS TAKES.**  The witness's
right leg is raise-only, hence pull-free: the mountain fails on the left leg
exactly as `EqualRung.not_mountainSplit` witnesses. -/
theorem right_pull_free : ∀ m ∈ right, ¬ Bubble.IsPull m := by
  intro m hm
  show ¬ Bubble.IsPull m
  have hmem : m ∈ [m11, m12] := hm
  have h1 : m = m11 ∨ m = m12 := by simpa using hmem
  rcases h1 with rfl | rfl
  · intro hp; obtain ⟨x, bb, hx⟩ := hp; cases hx
  · intro hp; obtain ⟨x, bb, hx⟩ := hp; cases hx

end EqSplitWitness

#print axioms EqSplitWitness.cpc_eq
#print axioms EqSplitWitness.split_pull_is_pull_cpc
#print axioms EqSplitWitness.raise_cpc_mem_pre
#print axioms EqSplitWitness.bracket_card
#print axioms EqSplitWitness.right_pull_free
