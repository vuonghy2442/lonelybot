import Orig2.FirstPassage


set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# Orig2/ForkValley — the local cancellation step of valley elimination

A valley segment is `A --pulls--> B --raises--> C`.  At the bottom `B` the
last pull and the first raise are ADJACENT.  This file formalizes the
cancellation when they are the SAME card, and the fork case where the
entering pull is the raisable twin.

* `valley_cancel_same`     — `… pull c ; raise c …` deletes both.
* `fork_first_raise_eq`    — at a fork, the first raise is the raisable
  twin (the blocked twin cannot be raised).
* `valley_cancel_at_fork_twin` — at a fork, a valley entered through the
  raisable twin still cancels; the only surviving fork valley enters on a
  different suit.

The remaining crossing case (last pull `c`, first raise `d`, `c ≠ d`) is
NOT handled here: it needs the bracket uncrossing (commute the matching
raise/pull), which is the `step_comm_raise_raise` / `step_comm_pull_pull`
work.
-/

namespace ValleyStep

/-- **SAME-CARD CANCELLATION.**  If a witness play reaches `A'`, pulls `c`
onto `b` to reach `B`, and immediately raises `c` again, then the two
letters delete: the rest of the play runs from `A'`. -/
theorem valley_cancel_same {A A' B C : State} {ρ₁ ρ₂ : List Move}
    {c : Card} {b : Base}
    (hwf : A.WF)
    (h₁ : ShufflePlayW A ρ₁ A')
    (hpull : State.step A' (Move.foundToTab c b) = some B)
    (h₂ : ShufflePlayW B (Move.tabToFound c :: ρ₂) C) :
    ShufflePlayW A (ρ₁ ++ ρ₂) C := by
  have hA' : A'.WF := SatDifferCensus.ShufflePlayW.wf_end h₁ hwf
  have hback : State.step B (Move.tabToFound c) = some A' :=
    step_tabToFound_of_foundToTab hA' hpull
  cases h₂ with
  | cons hrev hstep hrest =>
      rename_i B'
      have hBB' : B' = A' := Option.some.inj (hstep.symm.trans hback)
      subst hBB'
      exact ShufflePlayW_append h₁ hrest

/-- **AT A FORK THE FIRST RAISE IS THE RAISABLE TWIN.**  The blocked twin
cannot be raised, and the fork's live set is exactly the pair. -/
theorem fork_first_raise_eq {F : State} {x d : Card}
    (hF : F.WF) (hfork : ForkWitness F x)
    (hrev : reversibleAtW F (Move.tabToFound d)) :
    d = x := by
  have hR : tabToFoundR F d = true :=
    (tabToFoundR_iff_reversibleAtW hF d).mpr hrev
  have hcan : CanRaise F d := SatDifferCensus.canRaise_of_tabToFoundR hR
  have hS : CanRaiseS F d := CanRaiseS.now d hcan
  rcases (hfork.1 d).mpr hS with h | h
  · exact h
  · subst h
    exact absurd hcan hfork.2

/-- **A FORK VALLEY ENTERED THROUGH THE TWIN CANCELS.**  If the last pull
before the fork is the raisable twin `x`, the first raise (which must also
be `x` by `fork_first_raise_eq`) deletes the pair. -/
theorem valley_cancel_at_fork_twin
    {A A' F F' C : State} {ρ₁ ρ₂ : List Move}
    {x d : Card} {b : Base}
    (hwf : A.WF) (hfork : ForkWitness F x)
    (h₁ : ShufflePlayW A ρ₁ A')
    (hpull : State.step A' (Move.foundToTab x b) = some F)
    (hrev : reversibleAtW F (Move.tabToFound d))
    (hstep : State.step F (Move.tabToFound d) = some F')
    (h₂ : ShufflePlayW F' ρ₂ C) :
    d = x ∧ ShufflePlayW A (ρ₁ ++ ρ₂) C := by
  have hA' : A'.WF := SatDifferCensus.ShufflePlayW.wf_end h₁ hwf
  have hF : F.WF := step_wf hA' hpull
  have hdx : d = x := fork_first_raise_eq hF hfork hrev
  subst d
  have hback : State.step F (Move.tabToFound x) = some A' :=
    step_tabToFound_of_foundToTab hA' hpull
  have hF' : F' = A' := Option.some.inj (hstep.symm.trans hback)
  subst F'
  exact ⟨rfl, ShufflePlayW_append h₁ h₂⟩

/-- **A PULL'S CARD IS VANILLA-LIVE AT THE LANDING** (local copy of the
`pull_card_live` proof, strengthened to `CanRaise`). -/
theorem pull_card_canRaise {st w : State} (hwf : st.WF) {c : Card} {b : Base}
    (hstep : State.step st (Move.foundToTab c b) = some w) :
    CanRaise w c := by
  obtain ⟨c', htop, hc', -, -⟩ := step_foundToTab_inv hstep
  rw [hc'] at htop
  have hidx : c.rank.toIdx + 1 = rungAt st c.suit :=
    SatDifferCensus.foundTop_rank_succ hwf htop
  have hrung : rungAt w c.suit = rungAt st c.suit - 1 := by
    have h := rungAt_foundToTab hstep c.suit
    rw [ite_eq_left rfl] at h
    exact h
  have hfh : w.foundHeight c.suit = c.rank.toIdx := by
    show (w.found c.suit).length = c.rank.toIdx
    rw [show (w.found c.suit).length = rungAt w c.suit from rfl, hrung]
    omega
  have hnext : w.nextUp c = true := by
    unfold State.nextUp
    rw [hfh]
    exact decide_eq_true rfl
  exact SatDifferCensus.canRaise_post_of_pull hwf hstep hnext

/-- **THE ONLY PULL INTO A FORK IS THE RAISABLE TWIN.**  A pull's card is
vanilla-live at the landing; the fork's live set is exactly `{x, x.twin}`
and `x.twin` is not vanilla-live. -/
theorem fork_last_pull_eq {st F : State} {x c : Card} {b : Base}
    (hwf : st.WF) (hfork : ForkWitness F x)
    (hstep : State.step st (Move.foundToTab c b) = some F) :
    c = x := by
  have hcan : CanRaise F c := pull_card_canRaise hwf hstep
  have hS : CanRaiseS F c := CanRaiseS.now c hcan
  rcases (hfork.1 c).mpr hS with h | h
  · exact h
  · subst h
    exact absurd hcan hfork.2

/-- **ANY PULL-ENTERED FORK VALLEY CANCELS.**  The entering pull is the
raisable twin (`fork_last_pull_eq`) and the exiting raise is the same twin
(`fork_first_raise_eq`), so the adjacent pair deletes. -/
theorem fork_valley_cancel_of_pull
    {A A' F F' C : State} {ρ₁ ρ₂ : List Move}
    {x c d : Card} {b : Base}
    (hwf : A.WF) (hfork : ForkWitness F x)
    (h₁ : ShufflePlayW A ρ₁ A')
    (hpull : State.step A' (Move.foundToTab c b) = some F)
    (hrev : reversibleAtW F (Move.tabToFound d))
    (hstep : State.step F (Move.tabToFound d) = some F')
    (h₂ : ShufflePlayW F' ρ₂ C) :
    ShufflePlayW A (ρ₁ ++ ρ₂) C := by
  have hA' : A'.WF := SatDifferCensus.ShufflePlayW.wf_end h₁ hwf
  have hcx : c = x := fork_last_pull_eq hA' hfork hpull
  subst c
  exact (valley_cancel_at_fork_twin hwf hfork h₁ hpull hrev hstep h₂).2

#print axioms ValleyStep.valley_cancel_same
#print axioms ValleyStep.pull_card_canRaise
#print axioms ValleyStep.fork_last_pull_eq
#print axioms ValleyStep.fork_first_raise_eq
#print axioms ValleyStep.valley_cancel_at_fork_twin
#print axioms ValleyStep.fork_valley_cancel_of_pull

end ValleyStep
