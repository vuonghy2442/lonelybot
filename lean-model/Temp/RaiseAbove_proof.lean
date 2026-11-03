import Orig2.Fork.Class.ForkRaiseReorder

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

/-!
# T1 — `RaiseAbove`

A raise at rank `r` cannot disturb the readiness of a card `d` of another
suit that is *strictly above* rank `r` in the rank order, **provided one
knows which pile `d` sits in**.

The key structural point (brief, §"structural facts" 1): runs descend upward
in rank, so `c.rank < d.rank` does **not** place `d` outside `c`'s pile — `d`
may sit *below* `c`.  In the forward direction this is impossible: `CanRaise
st d` makes `d` a pile top, and a pile has only one top, so `d` cannot share
`c`'s pile (where `c` is the top).  Hence `b ≠ a₀` (the pile of `c` from
`step_tabToFound_inv`) and the raise leaves `d`'s pile literally unchanged.

The reverse direction needs `d ∉` the pile of `c` as an explicit hypothesis:
if `d` sits immediately below `c`, the raise exposes `d` and it can *become*
raisable, so `CanRaise w d → CanRaise st d` is false without that clause.

Nothing under `Orig2/` is touched; this is a standalone `Temp/` card.
-/

namespace OneColourClosure

/-- **Forward other-pile rerouting of `CanRaise`.**
If `d`'s suit is untouched and `d`'s pile `b` is unchanged by the raise of
`c`, then `CanRaise st d → CanRaise w d`.  (Forward mirror of
`Drain.canRaise_of_raise_other`; the `hpiles` block is copied verbatim from
`ForkDrainInduction.lean:245-251`.) -/
theorem canRaise_of_raise_other_fwd {st w : State} {c d : Card} {b : Anchor}
    (hwf : st.WF) (hstep : State.step st (Move.tabToFound c) = some w)
    (hsu : d.suit ≠ c.suit)
    (hd : st.pileHolding d = some b)
    (hpiles : w.piles b = st.piles b)
    (h : CanRaise st d) : CanRaise w d := by
  obtain ⟨hnext, a1, hpa1, hclause⟩ := h
  -- `a1` and `b` are the same pile
  have htop1 : (st.piles a1).top = some d := (pileOfTop_eq_some_iff hwf).mp hpa1
  have hmem1 : d ∈ (st.piles a1).faceUp := Pile.mem_of_top htop1
  have hmem_b : d ∈ (st.piles b).faceUp := pileHolding_mem hd
  have ha1 : a1 = b := by
    by_cases hne : a1 = b
    · exact hne
    · exfalso
      exact ((mem_faceUp_unique hwf hmem1 b (Ne.symm hne)).1) hmem_b
  -- foundations of `d`'s suit are untouched
  have hfound : w.found d.suit = st.found d.suit := by
    obtain ⟨-, a0, -, hs⟩ := step_tabToFound_inv hstep
    rw [hs]
    exact setFound_found_ne hsu
  have hnext_w : w.nextUp d = true := by
    have h1 : d.rank.toIdx = (st.found d.suit).length := by
      simpa [State.nextUp, State.foundHeight] using of_decide_eq_true hnext
    unfold State.nextUp State.foundHeight
    rw [hfound]
    exact decide_eq_true h1
  -- the pile read survives
  have htop_st_b : (st.piles b).top = some d := by
    rw [← ha1]
    exact htop1
  have hwfw : w.WF := step_wf hwf hstep
  have htop_w : (w.piles b).top = some d := by rw [hpiles]; exact htop_st_b
  have hpile_w : w.pileOfTop d = some b := (pileOfTop_eq_some_iff hwfw).mpr htop_w
  have hclause_b : chop (st.piles b).faceUp ≠ [] ∨
      ((st.piles b).hidden = [] ∧ d.rank = Rank.king) := by
    simpa [ha1] using hclause
  refine ⟨hnext_w, b, hpile_w, ?_⟩
  rcases hclause_b with hchop | ⟨hhid, hking⟩
  · left
    rw [hpiles]
    exact hchop
  · right
    refine ⟨?_, hking⟩
    rw [hpiles]
    exact hhid

/-- **T1, forward.**  Raising `c` cannot destroy `d`'s readiness for a card
`d` of another suit that is strictly above `c` in rank.

`c.rank < d.rank` is kept in the statement for compatibility with the card's
`RaiseAbove`, although the proof does not need it: `CanRaise st d` already
forces `d`'s pile to differ from `c`'s pile. -/
theorem canRaise_of_raise_above {st w : State} {c d : Card} {b : Anchor}
    (hwf : st.WF) (hstep : State.step st (Move.tabToFound c) = some w)
    (hsu : d.suit ≠ c.suit) (hrank : c.rank.toIdx < d.rank.toIdx)
    (hd : st.pileHolding d = some b) (h : CanRaise st d) : CanRaise w d := by
  obtain ⟨-, a0, hpa0, hs⟩ := step_tabToFound_inv hstep
  -- `d`'s pile is not `c`'s pile: two tops in one pile would force `d = c`.
  have hb_ne : b ≠ a0 := by
    intro hba
    obtain ⟨-, a1, hpa1, -⟩ := h
    have htop1 : (st.piles a1).top = some d := (pileOfTop_eq_some_iff hwf).mp hpa1
    have hmem1 : d ∈ (st.piles a1).faceUp := Pile.mem_of_top htop1
    have hmem_b : d ∈ (st.piles b).faceUp := pileHolding_mem hd
    have ha1 : a1 = b := by
      by_cases hne : a1 = b
      · exact hne
      · exfalso
        exact ((mem_faceUp_unique hwf hmem1 b (Ne.symm hne)).1) hmem_b
    have ha1a0 : a1 = a0 := ha1.trans hba
    have htop_c : (st.piles a0).top = some c := (pileOfTop_eq_some_iff hwf).mp hpa0
    have htop_d : (st.piles a0).top = some d := by
      rw [ha1a0] at htop1
      exact htop1
    have hdc : d = c := by
      rw [htop_d] at htop_c
      exact Option.some.inj htop_c
    exact hsu (by rw [hdc])
  -- the `hpiles` block of `ForkDrainInduction.lean:245-250`
  have hpiles : w.piles b = st.piles b := by
    rw [hs]
    show (if b = a0 then
        Pile.afterRunRemoved (st.piles a0) (chop (st.piles a0).faceUp)
      else st.piles b) = st.piles b
    rw [ite_eq_right hb_ne]
  exact canRaise_of_raise_other_fwd hwf hstep hsu hd hpiles h

/-- **T1, reverse (with the necessary separation hypothesis).**
If `d`'s pile `b` is not the pile of the top `c` (hypothesis `hsep`), then
`CanRaise w d → CanRaise st d`.

The separation hypothesis is not removable: if `d` sits immediately below
`c` in `c`'s pile, the raise exposes `d`, and `CanRaise w d` can hold while
`CanRaise st d` fails (e.g. `c = 5♠` on `d = 6♥` with the ♥ foundation at
height 5 and the ♠ foundation at height 4). -/
theorem canRaise_of_raise_above_rev {st w : State} {c d : Card} {b : Anchor}
    (hwf : st.WF) (hstep : State.step st (Move.tabToFound c) = some w)
    (hsu : d.suit ≠ c.suit) (hrank : c.rank.toIdx < d.rank.toIdx)
    (hd : st.pileHolding d = some b)
    (hsep : ∀ a, st.pileOfTop c = some a → b ≠ a)
    (h : CanRaise w d) : CanRaise st d := by
  obtain ⟨-, a0, hpa0, hs⟩ := step_tabToFound_inv hstep
  have hb_ne : b ≠ a0 := hsep a0 hpa0
  have hpiles : w.piles b = st.piles b := by
    rw [hs]
    show (if b = a0 then
        Pile.afterRunRemoved (st.piles a0) (chop (st.piles a0).faceUp)
      else st.piles b) = st.piles b
    rw [ite_eq_right hb_ne]
  exact Drain.canRaise_of_raise_other hwf hstep hsu hd hpiles h

/-- **T1, packaged `↔`.**  Under the separation hypothesis `hsep` (which the
reverse genuinely needs), readiness of `d` is exactly preserved. -/
theorem canRaise_of_raise_above_iff {st w : State} {c d : Card} {b : Anchor}
    (hwf : st.WF) (hstep : State.step st (Move.tabToFound c) = some w)
    (hsu : d.suit ≠ c.suit) (hrank : c.rank.toIdx < d.rank.toIdx)
    (hd : st.pileHolding d = some b)
    (hsep : ∀ a, st.pileOfTop c = some a → b ≠ a) :
    CanRaise st d ↔ CanRaise w d :=
  ⟨canRaise_of_raise_above hwf hstep hsu hrank hd,
   canRaise_of_raise_above_rev hwf hstep hsu hrank hd hsep⟩

end OneColourClosure

#print axioms OneColourClosure.canRaise_of_raise_other_fwd
#print axioms OneColourClosure.canRaise_of_raise_above
#print axioms OneColourClosure.canRaise_of_raise_above_rev
#print axioms OneColourClosure.canRaise_of_raise_above_iff
