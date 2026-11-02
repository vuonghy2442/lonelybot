import Orig2.Fork.Split.FirstPassage


set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

/-!
# Orig2/ForkDrain — raising other cards preserves a blocked twin

The drain raises live cards that are not the twins.  This file proves the
vanilla half of the invariant:

> if raising `c` does not touch `d`'s suit and does not change `d`'s pile,
> then `CanRaise` of `d` is preserved in both directions.

Hence `¬ CanRaise st d` survives such a raise — the asymmetry is stable.

The `CanRaiseS` half needs the cargo path to be transported across the
raise (the slide/raise square, assembly pending).
-/

namespace ValleyDrain

/-- **A raise cannot create a new raisable card outside its own pile.**
If `d`'s suit is untouched and `d`'s pile is unchanged by the raise, then
`CanRaise w d → CanRaise st d`. -/
theorem canRaise_of_raise_other {st w : State} {c d : Card}
    (hwf : st.WF) (hstep : State.step st (Move.tabToFound c) = some w)
    (hsu : d.suit ≠ c.suit)
    {b : Anchor} (hd : st.pileHolding d = some b)
    (hpiles : w.piles b = st.piles b)
    (h : CanRaise w d) : CanRaise st d := by
  obtain ⟨hnext_w, a1, hpa_w, hclause_w⟩ := h
  have hwfw : w.WF := step_wf hwf hstep
  obtain ⟨-, a0, hpa0, hs⟩ := step_tabToFound_inv hstep
  -- foundation of `d` is untouched
  have hf : w.found d.suit = st.found d.suit := by
    rw [hs]
    exact setFound_found_ne hsu
  -- nextUp transfers
  have hnext_st : st.nextUp d = true := by
    have h1 : d.rank.toIdx = (w.found d.suit).length := by
      simpa [State.nextUp, State.foundHeight] using of_decide_eq_true hnext_w
    rw [hf] at h1
    unfold State.nextUp
    apply decide_eq_true
    show d.rank.toIdx = (st.found d.suit).length
    exact h1
  -- the top card of `d`'s pile
  have htop_w : (w.piles a1).top = some d :=
    (pileOfTop_eq_some_iff hwfw).mp hpa_w
  have hmem_w : d ∈ (w.piles b).faceUp := by
    rw [hpiles]
    exact pileHolding_mem hd
  have ha1 : a1 = b := by
    by_cases hne : a1 = b
    · exact hne
    · exfalso
      have hmem_a1 : d ∈ (w.piles a1).faceUp := Pile.mem_of_top htop_w
      have hnot : d ∉ (w.piles b).faceUp :=
        (mem_faceUp_unique hwfw hmem_a1 b (Ne.symm hne)).1
      exact hnot hmem_w
  have htop_st : (st.piles b).top = some d := by
    rw [← hpiles, ← ha1]
    exact htop_w
  have hpile_st : st.pileOfTop d = some b :=
    (pileOfTop_eq_some_iff hwf).mpr htop_st
  -- the seat clause transfers with the pile
  refine ⟨hnext_st, b, hpile_st, ?_⟩
  rcases hclause_w with hchop | ⟨hhid, hking⟩
  · left
    intro hnil
    rw [← hpiles, ← ha1] at hnil
    exact hchop hnil
  · right
    refine ⟨?_, hking⟩
    rw [← hpiles, ← ha1]
    exact hhid

/-- The contrapositive form used by the drain: a blocked card stays blocked
when an unrelated card is raised. -/
theorem not_canRaise_of_raise_other {st w : State} {c d : Card}
    (hwf : st.WF) (hstep : State.step st (Move.tabToFound c) = some w)
    (hsu : d.suit ≠ c.suit)
    {b : Anchor} (hd : st.pileHolding d = some b)
    (hpiles : w.piles b = st.piles b)
    (h : ¬ CanRaise st d) : ¬ CanRaise w d :=
  fun hw => h (canRaise_of_raise_other hwf hstep hsu hd hpiles hw)

#print axioms ValleyDrain.canRaise_of_raise_other
#print axioms ValleyDrain.not_canRaise_of_raise_other

/-- **The rank condition removes the cover.**  If the raised card `c` has
rank at least the blocked card `d`'s rank, then `c` is not in `d`'s pile
(the cards above `d` have strictly smaller ranks), so the pile hypothesis
of `canRaise_of_raise_other` is automatic. -/
theorem canRaise_of_raise_high {st w : State} {c d : Card} {b : Anchor}
    (hwf : st.WF) (hstep : State.step st (Move.tabToFound c) = some w)
    (hsu : d.suit ≠ c.suit)
    (hd : st.pileHolding d = some b)
    (hrank : d.rank.toIdx ≤ c.rank.toIdx)
    (h : CanRaise w d) : CanRaise st d := by
  obtain ⟨-, a0, hpa0, hs⟩ := step_tabToFound_inv hstep
  have hb_ne : b ≠ a0 := by
    intro hba
    have htop_c : (st.piles a0).top = some c :=
      (pileOfTop_eq_some_iff hwf).mp hpa0
    have hlast : lastOf (st.piles a0).faceUp = some c := htop_c
    have hface : (st.piles a0).faceUp = chop (st.piles a0).faceUp ++ [c] :=
      lastOf_chop hlast
    have hdmem : d ∈ (st.piles a0).faceUp := by
      rw [← hba]
      exact pileHolding_mem hd
    have hdne : d ≠ c := fun hdc => hsu (by rw [hdc])
    have hdchop : d ∈ chop (st.piles a0).faceUp := by
      rw [hface] at hdmem
      rcases List.mem_append.mp hdmem with h' | h'
      · exact h'
      · exact absurd (List.mem_singleton.mp h') hdne
    have hok : runOK (chop (st.piles a0).faceUp ++ [c]) = true := by
      rw [← hface]
      exact hwf.2.1 a0
    have hlt : c.rank.toIdx < d.rank.toIdx :=
      runOK_desc hok hdchop (List.mem_singleton_self c)
    omega
  have hpiles : w.piles b = st.piles b := by
    rw [hs]
    show (if b = a0 then
        Pile.afterRunRemoved (st.piles a0) (chop (st.piles a0).faceUp)
      else st.piles b) = st.piles b
    rw [ite_eq_right hb_ne]
  exact canRaise_of_raise_other hwf hstep hsu hd hpiles h

#print axioms ValleyDrain.canRaise_of_raise_high
end ValleyDrain
