import Orig2.Fork.Split.FirstPassage


set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

/-!
# Orig2/ForkNoPull — a pull cannot create a *new* next-up card

The mountain normal form argument rests on one structural fact:

> the only raise a pull can enable is the raise of the pulled card itself.

This file formalizes the foundation half exactly (`nextUp`): a
`foundToTab c b` lowers the `c.suit` rung by one, so the only card that can
become next-up is the card just pulled.  The pile half (`pileOfTop` can only
be destroyed by a pull, never created) is monotone in the same way.
-/

namespace ValleyNoPull

/-- **A pull cannot make a different card next-up.** -/
theorem nextUp_of_pull_of_ne {st w : State} {c d : Card} {b : Base}
    (hwf : st.WF) (hstep : State.step st (Move.foundToTab c b) = some w)
    (hdc : d ≠ c) (h : w.nextUp d = true) : st.nextUp d = true := by
  obtain ⟨c', htop, hc', hcp, hs⟩ := step_foundToTab_inv hstep
  subst c'
  have hw : d.rank.toIdx = (w.found d.suit).length := by
    simpa [State.nextUp, State.foundHeight] using of_decide_eq_true h
  have hds_ne : d.suit ≠ c.suit := by
    intro hds
    have hwr : (w.found d.suit).length = (st.found d.suit).length - 1 := by
      have hh := rungAt_foundToTab hstep d.suit
      rw [ite_eq_left hds] at hh
      exact hh
    have htop' : c.rank.toIdx + 1 = (st.found c.suit).length :=
      SatDifferCensus.foundTop_rank_succ hwf htop
    have hrc : d.rank.toIdx = c.rank.toIdx := by
      have h1 : d.rank.toIdx = (st.found d.suit).length - 1 := by
        rw [hw]
        exact hwr
      rw [hds] at h1
      rw [← htop'] at h1
      omega
    have hrank : d.rank = c.rank := Rank.toIdx_inj hrc
    cases d with
    | mk dr ds =>
      cases c with
      | mk cr cs =>
        simp_all
  have hlen : (w.found d.suit).length = (st.found d.suit).length := by
    have hh : rungAt w d.suit = rungAt st d.suit := by
      rw [rungAt_foundToTab hstep d.suit, ite_eq_right hds_ne]
    exact hh
  unfold State.nextUp
  apply decide_eq_true
  show d.rank.toIdx = (st.found d.suit).length
  rw [← hlen]
  exact hw

/-- **The same-card exception is real:** the pulled card does become
next-up.  This is why `pull ; raise` is the only cancelable pair. -/
theorem nextUp_pull_self {st w : State} {c : Card} {b : Base}
    (hwf : st.WF) (h : State.step st (Move.foundToTab c b) = some w) :
    w.nextUp c = true := by
  obtain ⟨c', htop, hc', hcp, hs⟩ := step_foundToTab_inv h
  subst c'
  have hidx : c.rank.toIdx + 1 = (st.found c.suit).length :=
    SatDifferCensus.foundTop_rank_succ hwf htop
  have hrung : (w.found c.suit).length = (st.found c.suit).length - 1 := by
    have hh := rungAt_foundToTab h c.suit
    rw [ite_eq_left rfl] at hh
    exact hh
  unfold State.nextUp
  apply decide_eq_true
  show c.rank.toIdx = (w.found c.suit).length
  rw [hrung]
  omega

#print axioms ValleyNoPull.nextUp_of_pull_of_ne
#print axioms ValleyNoPull.nextUp_pull_self

end ValleyNoPull
