import Orig2.ForkEqSplitSlide
import Orig2.ForkLandResSeat
import Orig2.ForkChoiceFree
import Orig2.Substrate.Integrity
import Orig2.ForkBaseSeat
import Orig2.ForkBasePile
import Orig2.ForkBaseMain

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-!
# Orig2/ForkBaseRaise — the corridor always exists, and its removal is classified

READ-ONLY scratch.  No source edit, no commit.  No `sorry`, no
`Classical.choice`, no `native_decide`; battery at the tail.

This is the **extraction glue** of the base clause.  The data are:

* `P` — the state right after a window **cover** of `c` by the lander `x`;
* `P.pileOfTop x = some k` (singleton lander, `Base_Report.md` §4 (O1));
* `c ∈ (P.piles k).faceUp` (the cover put `c` under `x`);
* a play `P --l--> Q` to a state where `c` **tops** a pile (the pre-raise
  state of a `raise c`).

Then the corridor exists: a prefix `α` that is seat-inert for the lander, a
removal `r` that moves the lander's seat, and `r` is one of the three shapes
`Names x` / `LandsOn x` / `Drags k`.

So, at any `raise c` reachable after a singleton-lander cover, **the removal of
the lander exists and is named** — the base clause reduces to the *replay* of
the seat-inert interior around the lander (`BaseMain.CorridorReplay`).
-/

namespace BaseRaise

open CommuteStep
open ValleyElim

/-- A face-up card's pile is the pile its top search names. -/
theorem pileOfTop_eq_of_mem {st : State} (hwf : st.WF) {c : Card} {k j : Anchor}
    (hmem : c ∈ (st.piles k).faceUp) (htop : st.pileOfTop c = some j) : j = k := by
  by_cases hjk : j = k
  · exact hjk
  · exfalso
    exact (mem_faceUp_unique hwf hmem j hjk).1 (lastOf_mem (pileOfTop_top htop).2)

/-- **THE CORRIDOR EXISTS AT ANY RAISE-READY STATE.**  Either a seat-inert
prefix followed by a classified removal of the lander, or — impossibly — the
lander stays on its pile while `c` tops a pile it shares with the lander. -/
theorem corridor_at_top {P Q : State} {l : List Move} {x c : Card} {k j : Anchor}
    (hP : P.WF) (hplay : ShufflePlayW P l Q)
    (htop : P.pileOfTop x = some k)
    (hcmem : c ∈ (P.piles k).faceUp) (hxc : c ≠ x)
    (hctop : Q.pileOfTop c = some j) :
    ∃ (α : List Move) (r : Move) (β : List Move) (A B : State),
      l = α ++ r :: β ∧ ShufflePlayW P α A ∧ State.step A r = some B ∧
      BaseSeat.SeatInertPlay x k P α ∧
      (BaseMain.Names x r ∨ ChoiceFree.LandsOn x r ∨ BaseMain.Drags k A r) := by
  rcases BaseSeat.corridor_split_or_inert hplay hP htop with
    ⟨α, r, β, A, B, hl, hα, hstepA, hcert, hAtop, hBtop⟩ | hall
  · have hAwf : A.WF := SatDifferCensus.ShufflePlayW.wf_end hα hP
    have hrevA : reversibleAtW A r := by
      obtain ⟨mid, hmid, hrest⟩ := ShufflePlayW_split hplay α (r :: β) hl
      obtain ⟨A'', hrev, hstep, -⟩ := Bubble.walk_cons_inv hrest
      have h1 : State.run P α = some A := Walk_run _ hα
      have h2 : State.run P α = some mid := Walk_run _ hmid
      rw [h1] at h2
      have hAeq : mid = A := (Option.some.inj h2).symm
      rw [hAeq] at hrev
      exact hrev
    have hnot : ¬ BaseSeat.SeatInert A x k r := by
      intro hin
      exact hBtop (BaseSeat.pileOfTop_of_seatInert hAwf hrevA hstepA hAtop hin)
    exact ⟨α, r, β, A, B, hl, hα, hstepA, hcert, BaseMain.not_seatInert_cases hrevA hnot⟩
  · -- the lander never moves: `c` would have to top the lander's own pile
    exfalso
    have hQwf : Q.WF := SatDifferCensus.ShufflePlayW.wf_end hplay hP
    have hpile : Q.piles k = P.piles k :=
      BasePile.pile_untouched_of_seatInertPlay hall hplay hP htop
    have hxtop : Q.pileOfTop x = some k :=
      BaseSeat.pileOfTop_of_seatInertPlay hall hplay hP htop
    have hcmemQ : c ∈ (Q.piles k).faceUp := by rw [hpile]; exact hcmem
    have hjk : j = k := pileOfTop_eq_of_mem hQwf hcmemQ hctop
    have hctopk : Q.pileOfTop c = some k := by rw [hjk] at hctop; exact hctop
    have h1 : (Q.piles k).top = some c :=
      (pileOfTop_eq_some_iff (z := c) (a := k) hQwf).1 hctopk
    have h2 : (Q.piles k).top = some x :=
      (pileOfTop_eq_some_iff (z := x) (a := k) hQwf).1 hxtop
    exact hxc (Option.some.inj (h1.symm.trans h2))

end BaseRaise

#print axioms BaseRaise.pileOfTop_eq_of_mem
#print axioms BaseRaise.corridor_at_top