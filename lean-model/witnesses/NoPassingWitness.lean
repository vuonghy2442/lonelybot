import Klondike.Initial

/-!
  Scratch (blocker evidence for `safe_pileStack_dominant` & co.) —
  RESOLVED 2026-09-13 by the invariant-layer repair (Repair A):

  `State.WF` did NOT imply the *no-passing* invariant (`∀ visible c,
  heights c.suit ≤ toIdx c`) that the Blake&Gent worry-back argument
  (channel A of pruning_dominance_interaction.md §4) needs.  Witness
  `stNP`: the standard initial game with `heights ♥ := 1`.

  THE WITNESS IS NOW KILLED: WF gained the `founds_gone` conjunct
  (any card below its suit's foundation height is neither visible,
  nor in the stock cycle, nor hidden in a pile).  `stNP` has visible
  ♥A (on p0) with `heights ♥ = 1 > 0 = toIdx ♥A` — so `stNP.WF` is
  now FALSE (below), and `WF` DOES imply no-passing: contrapositively,
  a visible card satisfies `heights c.suit ≤ c.rank.toIdx`.
-/

namespace NoPassingWitness

def stNP : State :=
  { State.initial Deal.standard 1 with
    heights := fun s => if s = Suit.heart then 1 else 0 }

theorem standard_wf : Deal.standard.WF :=
  Deal.ofList_wf Card.universe_length universe_noDup

theorem initial_wf' : (State.initial Deal.standard 1).WF :=
  initial_wf standard_wf (by decide : (0 : Nat) < 1)

/-- ♥A is visible on p0 in `stNP`. -/
theorem stNP_vis : stNP.board.bottomOf (⟨Suit.heart, Rank.ace⟩ : Card)
    = some (Sum.inl Anchor.p0) := by decide

/-- KILLED: the witness state is no longer WF — `founds_gone` fails on
the visible, foundation-passed ♥A. -/
theorem stNP_not_wf : ¬ stNP.WF := by
  intro h
  have htrig : (⟨Suit.heart, Rank.ace⟩ : Card).rank.toIdx
      < stNP.heights (⟨Suit.heart, Rank.ace⟩ : Card).suit := by
    have h1 : (⟨Suit.heart, Rank.ace⟩ : Card).rank.toIdx = 0 := rfl
    have h2 : stNP.heights (⟨Suit.heart, Rank.ace⟩ : Card).suit = 1 := rfl
    omega
  have hfg := h.founds_gone (⟨Suit.heart, Rank.ace⟩ : Card) htrig
  have h1 : stNP.isVis (⟨Suit.heart, Rank.ace⟩ : Card) = true := by
    show (stNP.board.bottomOf (⟨Suit.heart, Rank.ace⟩ : Card)).isSome = true
    rw [stNP_vis]
    rfl
  rw [hfg.1] at h1
  exact Bool.noConfusion h1

/-- WF now implies no-passing: every visible card sits at or above its
suit's foundation height (the channel-A license the dominances need). -/
theorem wf_noPassing (st : State) (hwf : st.WF) :
    ∀ c, (st.board.bottomOf c).isSome = true → st.heights c.suit ≤ c.rank.toIdx := by
  intro c hc
  rcases Nat.lt_or_ge (c.rank.toIdx) (st.heights c.suit) with hlt | hge
  · exfalso
    have hfg := hwf.founds_gone c hlt
    have hvis : st.isVis c = true := by
      show (st.board.bottomOf c).isSome = true
      exact hc
    rw [hfg.1] at hvis
    exact Bool.noConfusion hvis
  · exact hge

end NoPassingWitness

#print axioms NoPassingWitness.stNP_not_wf
#print axioms NoPassingWitness.wf_noPassing
