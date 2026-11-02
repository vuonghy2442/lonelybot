import Orig2.ForkEqSplitSlide
import Orig2.ForkLandResNetZero
import Orig2.ForkLandResSeat
import Orig2.ForkChoiceFree
import Orig2.Fork.Local.ForkNoSelf

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-!
# Orig2/ForkBaseAdjoint — the adjacent cover/uncover pair is not shortest

READ-ONLY scratch.  No source edit, no commit.  No `sorry`, no
`Classical.choice`, no `native_decide`; battery at the tail.

The base clause of the equal-rung residual fails along a **cover/uncover pair**:
a window slide `x → c` lands `x` directly on `c`, and `x` must leave again
before `raise c` can fire (a raise needs its card to be a pile **top**).

This file proves the **empty-interior** case outright: if `x` leaves `c` with
the *very next* letter — the slide `x → b''` — then the two-letter word is
replaced by the single slide `x → b''` from the pre-cover state, using the
state-level net-zero `LandRes.slideSt_slideSt_self`.

All hypotheses are the net-zero's own data plus the two steps and the
reversibility of the direct slide at the pre-cover state; nothing is assumed
about the rest of the play (the shortening is purely local).
-/

namespace BaseAdjoint

open CommuteStep

/-- **THE ADJACENT COVER/UNCOVER PAIR SHORTENS.**  `A --slide x (inr c)--> A1
--slide x b''--> A2`, with the direct slide legal *and reversible* at `A`, is
replaced by the one-letter play `A --slide x b''--> A2`. -/
theorem adjacent_cover_uncover_shortens
    {A A1 A2 : State} {x c : Card} {a k k'' : Anchor} {b'' : Base}
    (hA : A.WF)
    (hrevA : reversibleAtW A (Move.tabToTab x b''))
    (hxa : A.pileOfTop x = some a)
    (hkd : A.pileOfTop c = some k) (hka : k ≠ a)
    (hcpd : A.canPlace x (Sum.inr c) = true)
    (hcp0 : A.canPlace x b'' = true)
    (hcp0s : (slideSt A x (Sum.inr c) a).canPlace x b'' = true)
    (hk'' : tgt A b'' = some k'') (hk''a : k'' ≠ a) (hk''k : k'' ≠ k)
    (hcell : below x (A.piles a).faceUp ≠ [] ∨
      (below x (A.piles a).faceUp = [] ∧ (A.piles a).hidden = []))
    (htgt : tgt (slideSt A x (Sum.inr c) a) b'' = some k'')
    (hstep1 : State.step A (Move.tabToTab x (Sum.inr c)) = some A1)
    (hstep2 : State.step A1 (Move.tabToTab x b'') = some A2) :
    ∃ ρ' : List Move, ShufflePlayW A ρ' A2 ∧ ρ'.length < 2 := by
  -- the single-card run of the cover
  have hsingle : fromCard x (A.piles a).faceUp = [x] :=
    NoSelfKit.fromCard_singleton_of_last (runOK_nodup (hA.runOK_of a))
      (pileOfTop_top hxa).2
  -- the cover lands on `slideSt`
  obtain ⟨a1, hhold1, hcp1, hrunv1, hs1⟩ := step_tabToTab_slideSt hstep1
  have ha1 : a1 = a :=
    Option.some.inj (hhold1.symm.trans (Drain.pileHolding_of_pileOfTop hA hxa))
  have hA1 : A1 = slideSt A x (Sum.inr c) a := by rw [hs1, ha1]
  have hS1wf : (slideSt A x (Sum.inr c) a).WF := by
    rw [← hA1]; exact step_wf hA hstep1
  -- the direct slide at `A`
  have hstep_direct : State.step A (Move.tabToTab x b'') = some (slideSt A x b'' a) := by
    rw [step_tabToTab_eq, Drain.pileHolding_of_pileOfTop hA hxa]
    show (if A.canPlace x b'' then
        (match fromCard x (A.piles a).faceUp with
         | [] => none
         | run => some ((A.setPile a
              (Pile.afterRunRemoved (A.piles a) (below x (A.piles a).faceUp))).putRun run b''))
      else none) = some (slideSt A x b'' a)
    rw [ite_eq_left hcp0, hsingle]
    simp only [slideSt, hsingle]
  -- the removal's source is the cover pile
  have hx1 : (slideSt A x (Sum.inr c) a).pileOfTop x = some k :=
    slideSt_pileOfTop_source hA hcpd hkd hka
      (by rw [hsingle]; simp) hcell (z := x) hxa
  have hA2 : A2 = slideSt A x b'' a := by
    rw [hA1] at hstep2
    obtain ⟨a2, hhold2, hcp2, hrunv2, hs2⟩ := step_tabToTab_slideSt hstep2
    have ha2 : a2 = k :=
      Option.some.inj (hhold2.symm.trans (Drain.pileHolding_of_pileOfTop hS1wf hx1))
    rw [hs2, ha2]
    exact LandRes.slideSt_slideSt_self hA hxa hkd hka hcpd hcp0 hcp0s
      hk'' hk''a hk''k hcell htgt
  exact ⟨[Move.tabToTab x b''], Walk.cons hrevA hstep_direct (by rw [hA2]; exact Walk.nil _),
    by simp⟩

end BaseAdjoint

#print axioms BaseAdjoint.adjacent_cover_uncover_shortens