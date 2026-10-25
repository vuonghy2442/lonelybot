import Orig2.Kit
import Orig2.TwinPairFreeRev
import Orig2.Integrity
import Orig2.StepWF
import Orig2.Classification

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# Orig2.TwinSelfArm — the self-arming law at the return state

The keystone of the last-return route to `FirstTouchRestart`: after a
successful pull of `c` (`foundToTab c b` — the excursion's return),
the post-state is `nextUp` for `c` again — the return's chop re-arms
the raise.  The row rides one landed fact,
`TwinPairFreeRev.found_chop_length_eq_rank` (a WF foundation's chop
length is the rank index of its top card), plus the step inversion's
state equation `step_foundToTab_inv`.

This is the whole content of the "self-arming law" the ledger records
("pulled window-cards land as licensed raisable tops"), at the exact
grade the twin-swap recipe's `hraise` cell needs.
-/

open State

/-- **The self-arming law.**  A successful `foundToTab c b` leaves the
post-state next-up for `c`: the chop re-arms the raise. -/
theorem nextUp_of_foundToTab {u s : State} {c : Card} {b : Base}
    (hwf : u.WF) (hstep : State.step u (Move.foundToTab c b) = some s) :
    s.nextUp c = true := by
  obtain ⟨c', htop, hc'c, -, hs⟩ := step_foundToTab_inv hstep
  rw [hc'c] at htop
  have hsf : s.found c.suit = chop (u.found c.suit) := by
    rw [hs, putCard_found]
    simp [State.setFound]
  have hchop := TwinPairFreeRev.found_chop_length_eq_rank hwf htop
  show decide (c.rank.toIdx = (s.found c.suit).length)
  rw [hsf, hchop]
  simp

/-- **The self-armed reversibility.**  After a successful return
(`foundToTab c b`), the post-state can raise `c` reversibly: the
chop re-arms the raise (the previous row), and the raised card
always has a giveback seat — the card beneath it (the chop-cons
cell), or the king's vacate (the anchor landing, kings only).
This is the `hraise` cell the twin-swap recipe consumes, satisfied
by the return itself. -/
theorem reversibleAtW_tabToFound_of_foundToTab {u s : State} {c : Card} {b : Base}
    (hwf : u.WF) (hstep : State.step u (Move.foundToTab c b) = some s) :
    reversibleAtW s (Move.tabToFound c) := by
  have hwfs : s.WF := step_wf hwf hstep
  have hn : s.nextUp c = true := nextUp_of_foundToTab hwf hstep
  refine (tabToFoundR_iff_reversibleAtW hwfs c).mp ?_
  obtain ⟨c', htop, hc'c, hcp, hs⟩ := step_foundToTab_inv hstep
  rw [hc'c] at htop
  cases b with
  | inl a' =>
      have hking : c.rank = Rank.king := (canPlace_inl hcp).2
      have hpiles : s.piles a' = { hidden := [], faceUp := [c] } := by
        rw [hs, putCard_piles_inl]
        simp
      have hpt : s.pileOfTop c = some a' :=
        (pileOfTop_eq_some_iff hwfs).mpr (by rw [hpiles]; rfl)
      simp only [tabToFoundR, hn, hpt, hpiles, chop]
      rw [hking]
      rfl
  | inr z =>
      obtain ⟨k, hloc, -⟩ := canPlace_inr hcp
      have hpiles : (s.piles k).faceUp = (u.piles k).faceUp ++ [c] := by
        rw [hs, putCard_piles_inr (u.setFound c.suit (chop (u.found c.suit))) c z k hloc]
        simp [State.setFound]
      have hpt : s.pileOfTop c = some k :=
        (pileOfTop_eq_some_iff hwfs).mpr (by
          show lastOf (s.piles k).faceUp = some c
          rw [hpiles, lastOf_snoc])
      have hzmem : z ∈ (u.piles k).faceUp :=
        lastOf_mem ((pileOfTop_eq_some_iff hwf).mp hloc)
      have hchop : chop (s.piles k).faceUp = (u.piles k).faceUp := by
        rw [hpiles, chop_snoc]
      cases hu : (u.piles k).faceUp with
      | nil => exact absurd hzmem (by rw [hu]; simp)
      | cons hd tl =>
          simp only [tabToFoundR, hn, hpt, hchop, hu]

#print axioms nextUp_of_foundToTab
#print axioms reversibleAtW_tabToFound_of_foundToTab
