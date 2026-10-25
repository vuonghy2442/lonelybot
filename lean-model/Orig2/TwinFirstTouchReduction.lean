import Orig2.TwinPairFreeTransfer
import Orig2.TwinSplicePlay
import Orig2.TwinForcedCancel
import Orig2.DetourKit
import Orig2.Kit
import Orig2.StepWF

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false

/-!
# Orig2.TwinFirstTouchReduction — the full transfer reduced to the first touch

The owner's reduction step toward `fiber_transfer_corrected`
(`Orig2/ClaimsScrutiny.lean:248`): every witness journey either never
touches the twin, or has a FIRST touching move — and at that state the
swap availability has already arrived, by the pair-free transfer
(`Orig2/TwinPairFreeTransfer.lean`, landed 2026-10-25).

## The factorization

For a witness journey `s ⇝ t` with both twins `.inr`-seated at both
ends, `DetourKit.exists_pairFound_split` splits the play:

* ALL letters pair-free — the LANDED card: availability transfers.
* FIRST touching move `m` at `w` (prefix `s ⇝ w` pair-free, suffix
  `w' ⇝ t` arbitrary):
  - the prefix transfers availability to `w` (the pair-free card, over
    `wf_seats_of_pairFreeWalk` for the seats);
  - everything else is `FirstTouchRestart` below.

`swappableIn_transfer_of_firstTouchRestart` is the composition; the
class-level read `swappableIn_transfer_class_of_firstTouchRestart` is
the campaign's rigidity row at the `BitWellDefined` grade (cf.
`bitWellDefined_iff_nonKingTransfer`, `Orig2/TwinFiberQuotient.lean`).

## The residual

`FirstTouchRestart` — the named residual — is the full theorem with
the FIRST touch made explicit: ONE touching move (reversible, `¬
NotFoundPair`), an arbitrary suffix, and the swap already available at
the pre-touch state.  By `firstTouch_is_raise` below, the touching move
is necessarily a RAISE of a twin (`tabToFound x` / `tabToFound
x.twin`) — the pull shapes cannot fire at a seated state — so the
residual is exactly ONE excursion: raise the twin, do the middle,
come back seated.  The pair-free prefix problem is GONE; the excursion
content (`TwinExcursionClosure` / `LastPullCancellation` territory) is
all that remains, now with a seated, swap-available entry point.

Zero `sorry`, zero `Classical.choice`.
-/

open State

/-! ## 1. Kit — splitting a walk over an appended list -/

theorem walk_append_split {P : State → Move → Prop}
    {a c : State} {l1 l2 : List Move} (h : Walk P a (l1 ++ l2) c) :
    ∃ b, Walk P a l1 b ∧ Walk P b l2 c := by
  induction l1 generalizing a with
  | nil => exact ⟨a, Walk.nil a, h⟩
  | cons m rest ih =>
      obtain ⟨s1, hlet, hstep, hrest⟩ :=
        TwinForcedCancel.walk_cons_inv (by simpa using h)
      obtain ⟨b, hb1, hb2⟩ := ih hrest
      exact ⟨b, Walk.cons hlet hstep hb1, hb2⟩

/-! ## 2. Kit — WF and the `.inr` seats are maintained along pair-free walks -/

private theorem wf_seats_of_pairFreeWalk {u v : State} {x : Card} {play : List Move}
    (hwf : u.WF) (hplay : ShufflePlayW u play v)
    (hx : ∃ z, seatOf u x = some (Sum.inr z))
    (hxt : ∃ z : Card, seatOf u x.twin = some (Sum.inr z.twin))
    (hno : ∀ m ∈ play, NotFoundPair x m) :
    v.WF ∧ (∃ z, seatOf v x = some (Sum.inr z)) ∧
      (∃ z : Card, seatOf v x.twin = some (Sum.inr z.twin)) := by
  revert hwf hx hxt hno
  induction hplay with
  | nil st =>
      intro hwf hx hxt _
      exact ⟨hwf, hx, hxt⟩
  | @cons st s1 W m rest' hrev hstep hrest ih =>
      intro hwf hx hxt hno
      obtain ⟨hs1, hst1⟩ :=
        seat_inr_of_pairFree_step hwf hstep hrev (hno m (by simp)) hx hxt
      exact ih (step_wf hwf hstep) hs1 hst1
        (fun n hn => hno n (List.mem_cons_of_mem _ hn))

/-! ## 3. The sharpening — the first touch is necessarily a raise -/

private theorem not_notFoundPair_of_isPairFound {x : Card} {m : Move}
    (hm : IsPairFound x m) : ¬ NotFoundPair x m := fun h =>
  (notFoundPair_iff_not_isPairFound x m).mp h hm

/-- At a state where both twins are `.inr`-seated, a touching move
that fires is necessarily a RAISE of a twin: the pull shapes
(`foundToTab x b` / `foundToTab x.twin b`) cannot fire, because a
seated card is not on the foundation. -/
theorem firstTouch_is_raise {w w' : State} {x : Card} {m : Move}
    (hwf : w.WF)
    (hx : ∃ z, seatOf w x = some (Sum.inr z))
    (hxt : ∃ z : Card, seatOf w x.twin = some (Sum.inr z.twin))
    (hstep : State.step w m = some w')
    (hm : IsPairFound x m) :
    m = Move.tabToFound x ∨ m = Move.tabToFound x.twin := by
  rcases hm with h | h | ⟨b, hb⟩ | ⟨b, hb⟩
  · exact Or.inl h
  · exact Or.inr h
  · subst hb
    obtain ⟨c', htop, hc'c, -, -⟩ := step_foundToTab_inv hstep
    rw [hc'c] at htop
    have hmem : x ∈ w.found x.suit := by
      simpa [State.foundTop] using lastOf_mem htop
    obtain ⟨z, hz⟩ := hx
    rw [TwinForcedCancel.seatOf_none_of_mem_found hwf hmem] at hz
    simp at hz
  · subst hb
    obtain ⟨c', htop, hc'c, -, -⟩ := step_foundToTab_inv hstep
    rw [hc'c] at htop
    have hmem : x.twin ∈ w.found x.twin.suit := by
      simpa [State.foundTop] using lastOf_mem htop
    obtain ⟨z, hz⟩ := hxt
    rw [TwinForcedCancel.seatOf_none_of_mem_found hwf hmem] at hz
    simp at hz

/-! ## 4. The residual and the reduction -/

/-- **`FirstTouchRestart`** — the owner's named residual: the full
transfer with the FIRST touching move made explicit.  The swap is
already available at the pre-touch state `w` (provided by the pair-free
prefix in the reduction); one reversible touching move fires; the
suffix to the seated end `v` is arbitrary. -/
def FirstTouchRestart : Prop :=
  ∀ (w w' v : State) (x : Card) (rest : List Move),
    w.WF → v.WF →
    (∃ z, seatOf w x = some (Sum.inr z)) →
    (∃ z : Card, seatOf w x.twin = some (Sum.inr z.twin)) →
    (∃ z, seatOf v x = some (Sum.inr z)) →
    (∃ z : Card, seatOf v x.twin = some (Sum.inr z.twin)) →
    SwappableIn w x →
    (∃ m, ¬ NotFoundPair x m ∧ reversibleAtW w m ∧
        State.step w m = some w' ∧ ShufflePlayW w' rest v) →
    SwappableIn v x

/-- **THE REDUCTION (witness-journey form).**  Every witness journey
from seated, swap-available `s` to seated `t` either never touches the
twin — the landed pair-free card — or its first touching move is
reached with availability already transferred to the pre-touch state;
`FirstTouchRestart` finishes. -/
theorem swappableIn_transfer_of_firstTouchRestart
    (hR : FirstTouchRestart)
    {s t : State} {x : Card} {play : List Move}
    (hwf : s.WF) (hwft : t.WF)
    (hsx : ∃ z, seatOf s x = some (Sum.inr z))
    (hstx : ∃ z : Card, seatOf s x.twin = some (Sum.inr z.twin))
    (htx : ∃ z, seatOf t x = some (Sum.inr z))
    (httx : ∃ z : Card, seatOf t x.twin = some (Sum.inr z.twin))
    (hplay : ShufflePlayW s play t)
    (hswap : SwappableIn s x) :
    SwappableIn t x := by
  rcases exists_pairFound_split x play with hall | ⟨pre, m, post, hsplit, hm, hpre⟩
  · refine swappableIn_transfer_of_pairFreePath hwf hwft hsx hstx htx httx hplay ?_ hswap
    intro n hn
    exact (notFoundPair_iff_not_isPairFound x n).mpr (hall n hn)
  · subst hsplit
    obtain ⟨w, hwpre, hwpost⟩ := walk_append_split hplay
    have hnoPre : ∀ n ∈ pre, NotFoundPair x n := fun n hn =>
      (notFoundPair_iff_not_isPairFound x n).mpr (hpre n hn)
    obtain ⟨hwfw, hwx, hwtx⟩ :=
      wf_seats_of_pairFreeWalk hwf hwpre hsx hstx hnoPre
    have hswapw : SwappableIn w x :=
      swappableIn_transfer_of_pairFreePath hwf hwfw hsx hstx hwx hwtx hwpre hnoPre hswap
    obtain ⟨w', hrev, hstep, hrest⟩ := TwinForcedCancel.walk_cons_inv hwpost
    exact hR w w' t x post hwfw hwft hwx hwtx htx httx hswapw
      ⟨m, not_notFoundPair_of_isPairFound hm, hrev, hstep, hrest⟩

/-- **THE REDUCTION (class form).**  The campaign's rigidity row at the
`BitWellDefined` grade: availability transfers along the class. -/
theorem swappableIn_transfer_class_of_firstTouchRestart
    (hR : FirstTouchRestart)
    {s s' : State} {x : Card}
    (hwf : s.WF) (hwf' : s'.WF)
    (hclass : sameOrbitSetoid.r s s')
    (hsx : ∃ z, seatOf s x = some (Sum.inr z))
    (hstx : ∃ z : Card, seatOf s x.twin = some (Sum.inr z.twin))
    (htx : ∃ z, seatOf s' x = some (Sum.inr z))
    (httx : ∃ z : Card, seatOf s' x.twin = some (Sum.inr z.twin))
    (hswap : SwappableIn s x) :
    SwappableIn s' x := by
  obtain ⟨π, hπ, -⟩ := sameOrbitSetoid.iseqv.symm hclass
  exact swappableIn_transfer_of_firstTouchRestart hR hwf hwf' hsx hstx htx httx hπ hswap

#print axioms firstTouch_is_raise
#print axioms swappableIn_transfer_of_firstTouchRestart
#print axioms swappableIn_transfer_class_of_firstTouchRestart
