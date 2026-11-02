import Orig2.ForkEqSplitSlide
import Orig2.ForkLandResSeat
import Orig2.Fork.ForkCommuteSlide
import Orig2.ForkChoiceFree
import Orig2.ForkBaseSeat

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-!
# Orig2/ForkBasePile — a seat-inert letter leaves the cover pile untouched

READ-ONLY scratch.  No source edit, no commit.  No `sorry`, no
`Classical.choice`, no `native_decide`; battery at the tail.

`BaseSeat.SeatInert` is `SeatSafe` (the letter does not name the lander and does
not land on it) plus "does not slide a run out of the lander's pile".  This file
proves the *pile-level* content of that notion:

```text
x tops pile k, q is SeatInert for x, q is legal  ⇒  (step q).piles k = st.piles k
```

so a whole seat-inert play leaves the lander's pile **literally unchanged**.  This
is the frame fact the cover/uncover reconstruction needs: the cover's pile is
invisible to the corridor interior, in the strong sense that the pile value — not
only its top search — is preserved.
-/

namespace BasePile

open CommuteStep

/-- **A TARGETED BASE NEVER POINTS AT THE LANDER'S PILE UNLESS IT NAMES THE
LANDER.**  Hence a `SeatSafe` letter whose target is legal writes no pile
`k` that the lander tops. -/
theorem tgt_ne_seat {st : State} (hwf : st.WF) {y x : Card} {k : Anchor}
    (htop : st.pileOfTop x = some k) {b : Base} (hb : b ≠ Sum.inr x)
    (hcp : st.canPlace y b = true) :
    tgt st b ≠ some k := by
  intro h
  cases b with
  | inl A =>
      have hAk : A = k := Option.some.inj ((tgt_inl st A).symm.trans h)
      rw [canPlace_inl_unfold] at hcp
      have hemp : (st.piles k).isEmpty = true := by
        rw [← hAk]
        exact (Bool.and_eq_true _ _).mp hcp |>.1
      rw [Pile.isEmpty_eq] at hemp
      have hmem : x ∈ (st.piles k).faceUp := lastOf_mem (pileOfTop_top htop).2
      rw [hemp.2] at hmem
      exact absurd hmem List.not_mem_nil
  | inr z =>
      have hz : st.pileOfTop z = some k := h
      have hztop : (st.piles k).top = some z :=
        (pileOfTop_eq_some_iff (z := z) (a := k) hwf).1 hz
      have hxtop : (st.piles k).top = some x :=
        (pileOfTop_eq_some_iff (z := x) (a := k) hwf).1 htop
      have hzx : z = x := Option.some.inj (hztop.symm.trans hxtop)
      exact hb (by rw [hzx])

/-- **THE COVER PILE IS FROZEN BY A SEAT-INERT LETTER.** -/
theorem pile_untouched_of_seatInert {st s' : State} {x : Card} {k : Anchor} {q : Move}
    (hwf : st.WF) (hrev : reversibleAtW st q) (hstep : State.step st q = some s')
    (htop : st.pileOfTop x = some k) (hin : BaseSeat.SeatInert st x k q) :
    s'.piles k = st.piles k := by
  obtain ⟨hsafe, hsrc⟩ := hin
  cases q with
  | draw => rw [stepDraw_piles hstep]
  | wasteToFound c => exact absurd hrev (wasteToFound_not_reversibleAtW st c)
  | wasteToTab c b => exact absurd hrev (wasteToTab_not_reversibleAtW st c b)
  | tabToFound w =>
      obtain ⟨hn, a, hpa, hs⟩ := step_tabToFound_inv hstep
      have haw : w ≠ x := hsafe
      have hka : k ≠ a := by
        intro hEq
        have htopw : st.pileOfTop w = some k := by rw [hEq]; exact hpa
        have hwt : (st.piles k).top = some w :=
          (pileOfTop_eq_some_iff (z := w) (a := k) hwf).1 htopw
        have hxt : (st.piles k).top = some x :=
          (pileOfTop_eq_some_iff (z := x) (a := k) hwf).1 htop
        exact haw (Option.some.inj (hwt.symm.trans hxt))
      have hstep' : State.step st (Move.tabToFound w) = some (raiseSt st w a) := by
        rw [step_tabToFound_splice hn hpa]
        rfl
      have hs' : s' = raiseSt st w a := Option.some.inj (hstep.symm.trans hstep')
      rw [hs', raiseSt_piles_apply, ite_eq_right hka]
  | foundToTab y b =>
      obtain ⟨y', htop', hyx, hcp, hs⟩ := step_foundToTab_pullSt hstep
      obtain ⟨K, hK⟩ := exists_tgt_of_canPlace hcp
      have hKk : K ≠ k := by
        intro hEq
        exact tgt_ne_seat hwf htop hsafe.2 hcp (by rw [hK, hEq])
      subst hs
      exact pullSt_piles_ne hK (Ne.symm hKk)
  | tabToTab y b =>
      obtain ⟨a1, hhold1, hcp1, hrunv1, hs1⟩ := step_tabToTab_slideSt hstep
      obtain ⟨a0, k0, hhold0, hcp0, hk0, hka0, hface0, hrunv0, hcell0⟩ :=
        slide_data hwf hrev
      have hae : a0 = a1 := Option.some.inj (hhold0.symm.trans hhold1)
      have hka : k ≠ a0 := by
        intro hEq
        exact (hsrc y b rfl) (by rw [hEq]; exact hhold0)
      have hkk0 : k ≠ k0 := by
        intro hEq
        exact tgt_ne_seat hwf htop hsafe.2 hcp0 (by rw [hk0, hEq])
      subst hs1
      rw [← hae]
      exact slideSt_piles_other hwf hcp0 hk0 hka0 hcell0 hka hkk0

/-- **A SEAT-INERT PLAY LEAVES THE COVER PILE UNTOUCHED.** -/
theorem pile_untouched_of_seatInertPlay {st s : State} {l : List Move} {x : Card} {k : Anchor}
    (hcert : BaseSeat.SeatInertPlay x k st l) (hplay : ShufflePlayW st l s)
    (hwf : st.WF) (htop : st.pileOfTop x = some k) :
    s.piles k = st.piles k := by
  induction l generalizing st with
  | nil =>
      cases hplay
      rfl
  | cons q t ih =>
      obtain ⟨st1, hrev, hstep, hrest⟩ := Bubble.walk_cons_inv hplay
      obtain ⟨h1, h2⟩ := hcert
      have hwf1 : st1.WF := step_wf hwf hstep
      have htop1 : st1.pileOfTop x = some k :=
        BaseSeat.pileOfTop_of_seatInert hwf hrev hstep htop h1
      have hbody : st1.piles k = st.piles k :=
        pile_untouched_of_seatInert hwf hrev hstep htop h1
      have htail : s.piles k = st1.piles k := ih (h2 st1 hstep) hrest hwf1 htop1
      rw [htail, hbody]

end BasePile

#print axioms BasePile.tgt_ne_seat
#print axioms BasePile.pile_untouched_of_seatInert
#print axioms BasePile.pile_untouched_of_seatInertPlay