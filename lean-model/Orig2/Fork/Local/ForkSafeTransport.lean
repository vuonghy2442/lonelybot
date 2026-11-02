import Orig2.Fork.Split.FirstPassage


set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

/-!
# Temp/SafeTransport — raising a high card preserves `CanRaiseS`

READ-ONLY scratch card.  No source edits, no commit.

We prove the last mathematical input of the drain-to-fork theorem:

> a reversible raise of a card `c` of rank at least `x.rank` and in a
> different suit than `x` preserves `CanRaiseS · x`, provided
> `c ≠ x.twin`.

The proof uses the flat characterization `canRaiseS_iff`: the low-layer
cargo path of `x` is read off as a single flat witness (the holding
pile's `bs ++ x :: run` split).  The raise only writes its own pile and
its own rung, and `x` (and `x.twin`) cannot live at/above that pile:
every card above `x` has strictly smaller rank, so `x` is never in the
raised pile, and the raised pile's top is `c`, never `x.twin`.

We record the honest side condition `c ≠ x.twin`.  It is *necessary*:
`x.twin` is exactly the twin whose disappearance can break the
`run ≠ []` cover clause of the flat characterization.  In the consumer
(`Drain.RaiseTransport.CanRaiseS_preserved`) it is supplied.
-/

namespace SafeTransport

/-! ## §1. The restricted low-layer move set -/

/-- **safeMoves r x** — the drain's restricted cargo alphabet: slides of
cards strictly below rung `r`, with bases either low, `x`, or `x.twin`. -/
def safeMoves (r : Nat) (x : Card) : MoveSet := fun m =>
  ∃ d b, m = Move.tabToTab d b ∧ d.rank.toIdx < r ∧
    (∀ z, b = Sum.inr z → z.rank.toIdx < r ∨ z = x ∨ z = x.twin)

/-- A safe reversible step is a cargo leg. -/
theorem cargoLeg_of_safeRevStep {r : Nat} {x : Card} {u v : State}
    (h : RevStepOf (safeMoves r x) u v) : CargoLeg u v := by
  obtain ⟨m, hm, hstep, hrev⟩ := h
  obtain ⟨d, b, rfl, -⟩ := hm
  exact ⟨d, b, hstep, hrev⟩

/-- A restricted safe path is a cargo path. -/
theorem cargoPath_of_safeSteps {r : Nat} {x : Card} {u v : State}
    (h : Steps (RevStepOf (safeMoves r x)) u v) : CargoPath u v := by
  induction h with
  | refl w => exact Steps.refl w
  | cons hleg _ ih => exact Steps.cons (cargoLeg_of_safeRevStep hleg) ih

/-- The `CanRaiseS` reading of the safe-path hypothesis. -/
theorem canRaiseS_of_safePath {st : State} {x : Card}
    (hsafe : ∃ z, Steps (RevStepOf (safeMoves x.rank.toIdx x)) st z ∧ CanRaise z x) :
    CanRaiseS st x := by
  obtain ⟨z, hp, hcr⟩ := hsafe
  exact ⟨z, cargoPath_of_safeSteps hp, hcr⟩

/-! ## §2. The raise's pile never holds a card at/above the raised rank -/

/-- If `x` is face-up in pile `a`, `x ≠ c`, and `x`'s rank is at most
`c`'s, then `a` is not the pile `c` tops: every face-up card strictly
below the top `c` sits strictly below `c` in rank. -/
theorem tabToFound_pile_ne_of_mem {st : State} {c x : Card} {a a0 : Anchor}
    (hwf : st.WF) (hpa0 : st.pileOfTop c = some a0)
    (hxmem : x ∈ (st.piles a).faceUp)
    (hxc : x ≠ c)
    (hrank : x.rank.toIdx ≤ c.rank.toIdx) :
    a ≠ a0 := by
  intro ha
  rw [← ha] at hpa0
  have htop : (st.piles a).top = some c := (pileOfTop_eq_some_iff hwf).mp hpa0
  have hface : (st.piles a).faceUp = chop (st.piles a).faceUp ++ [c] :=
    lastOf_chop htop
  have hxchop : x ∈ chop (st.piles a).faceUp := by
    rw [hface] at hxmem
    rcases List.mem_append.mp hxmem with h' | h'
    · exact h'
    · exact absurd (List.mem_singleton.mp h') hxc
  have hok : runOK (chop (st.piles a).faceUp ++ [c]) = true := by
    rw [← hface]
    exact hwf.2.1 a
  have hlt : c.rank.toIdx < x.rank.toIdx :=
    runOK_desc hok hxchop (List.mem_singleton_self c)
  omega

/-! ## §3. The raise's action on the other piles -/

/-- A raise leaves every pile but its own untouched. -/
theorem piles_tabToFound_ne {st w : State} {c : Card} {a0 a : Anchor}
    (hstep : State.step st (Move.tabToFound c) = some w)
    (hpa0 : st.pileOfTop c = some a0) (ha : a ≠ a0) :
    w.piles a = st.piles a := by
  obtain ⟨-, a', hpa', hs⟩ := step_tabToFound_inv hstep
  have haa : a' = a0 := Option.some.inj (hpa'.symm.trans hpa0)
  rw [hs, haa]
  show (if a = a0 then _ else st.piles a) = st.piles a
  exact ite_eq_right ha

/-- A raise leaves the top search of a card topping a different pile
alone. -/
theorem pileOfTop_tabToFound_ne {st w : State} {c z : Card} {a0 k : Anchor}
    (hwf : st.WF) (hstep : State.step st (Move.tabToFound c) = some w)
    (hpa0 : st.pileOfTop c = some a0)
    (hz : st.pileOfTop z = some k) (hka0 : k ≠ a0) :
    w.pileOfTop z = some k := by
  have hwfw : w.WF := step_wf hwf hstep
  have htopk : (st.piles k).top = some z := (pileOfTop_eq_some_iff hwf).mp hz
  have hpile : w.piles k = st.piles k :=
    piles_tabToFound_ne hstep hpa0 hka0
  have htopk_w : (w.piles k).top = some z := by
    rw [hpile]
    exact htopk
  exact (pileOfTop_eq_some_iff hwfw).mpr htopk_w

/-- A raise leaves every other rung untouched. -/
theorem found_tabToFound_ne {st w : State} {c : Card}
    (hstep : State.step st (Move.tabToFound c) = some w)
    {s : Suit} (hs : s ≠ c.suit) :
    w.found s = st.found s := by
  obtain ⟨-, a', hpa', hw⟩ := step_tabToFound_inv hstep
  rw [hw]
  show (st.setFound c.suit (st.found c.suit ++ [c])).found s = st.found s
  exact setFound_found_ne hs

/-- A raise leaves the next-up test of another suit alone. -/
theorem nextUp_tabToFound_ne {st w : State} {c x : Card}
    (hstep : State.step st (Move.tabToFound c) = some w)
    (hcs : c.suit ≠ x.suit) (hnext : st.nextUp x = true) :
    w.nextUp x = true := by
  have hf : w.found x.suit = st.found x.suit :=
    found_tabToFound_ne hstep hcs.symm
  unfold State.nextUp State.foundHeight at hnext ⊢
  rw [hf]
  exact hnext

/-! ## §4. THE THEOREMS -/

/-- **The core SafeTransport row.**  A raise of a card `c` of rank at
least `x.rank`, in a suit different from `x`'s, preserves `CanRaiseS · x`
— provided `c ≠ x.twin`.

No layer restriction on the cargo path is used: the flat
characterization `canRaiseS_iff` turns `CanRaiseS st x` into the local
shape `bs ++ x :: run` at `x`'s pile, and the raise is disjoint from
that pile by the rank argument. -/
theorem canRaiseS_of_canRaiseS_raise_high
    {st w : State} {c x : Card}
    (hwf : st.WF)
    (hstep : State.step st (Move.tabToFound c) = some w)
    (hcs : c.suit ≠ x.suit)
    (hct : c ≠ x.twin)
    (hrank : x.rank.toIdx ≤ c.rank.toIdx)
    (hS : CanRaiseS st x)
    : CanRaiseS w x := by
  have hwfw : w.WF := step_wf hwf hstep
  rw [canRaiseS_iff hwfw]
  rw [canRaiseS_iff hwf] at hS
  obtain ⟨hnext, a, bs, run, hface, hseat, hcond⟩ := hS
  obtain ⟨-, a0, hpa0, -⟩ := step_tabToFound_inv hstep
  have hxmem : x ∈ (st.piles a).faceUp := by
    rw [hface]
    exact List.mem_append.mpr (Or.inr List.mem_cons_self)
  have hxc : x ≠ c := fun h => hcs (by rw [h])
  have ha : a ≠ a0 := tabToFound_pile_ne_of_mem hwf hpa0 hxmem hxc hrank
  have hpile : w.piles a = st.piles a := piles_tabToFound_ne hstep hpa0 ha
  have hnext_w : w.nextUp x = true := nextUp_tabToFound_ne hstep hcs hnext
  refine ⟨hnext_w, a, bs, run, ?_, ?_, ?_⟩
  · rw [hpile]
    exact hface
  · rw [hpile]
    exact hseat
  · rcases hcond with hrun | hsome
    · exact Or.inl hrun
    · right
      intro hnone
      obtain ⟨k, hk⟩ : ∃ k, st.pileOfTop x.twin = some k := by
        cases h : st.pileOfTop x.twin with
        | none => exact absurd h hsome
        | some k => exact ⟨k, rfl⟩
      have hka0 : k ≠ a0 := by
        intro hka
        have htop : (st.piles a0).top = some x.twin :=
          (pileOfTop_eq_some_iff hwf).mp (hka ▸ hk)
        have htopc : (st.piles a0).top = some c :=
          (pileOfTop_eq_some_iff hwf).mp hpa0
        have hxct : x.twin = c := Option.some.inj (htop.symm.trans htopc)
        exact hct hxct.symm
      have hwk : w.pileOfTop x.twin = some k :=
        pileOfTop_tabToFound_ne hwf hstep hpa0 hk hka0
      rw [hwk] at hnone
      exact nomatch hnone

/-- **The requested theorem.**  A reversible high raise preserves
`CanRaiseS · x` on any restricted safe path.

The `hrev` hypothesis is kept to match the consumer's signature; the
flat characterization route does not need it (the raise's own pile is
excluded by the rank argument, not by reversibility). -/
theorem canRaiseS_of_raise_high
    {st w : State} {c x : Card}
    (hwf : st.WF)
    (hstep : State.step st (Move.tabToFound c) = some w)
    (hrev : reversibleAtW st (Move.tabToFound c))
    (hcs : c.suit ≠ x.suit)
    (hct : c ≠ x.twin)
    (hrank : x.rank.toIdx ≤ c.rank.toIdx)
    (hsafe : ∃ z, Steps (RevStepOf (safeMoves x.rank.toIdx x)) st z ∧ CanRaise z x)
    : CanRaiseS w x :=
  canRaiseS_of_canRaiseS_raise_high hwf hstep hcs hct hrank
    (canRaiseS_of_safePath hsafe)

/-- **The consumer-shaped corollary** (`Temp/Drain_Invariant.lean:558`):
the held card is the blocked twin `y`, waiting for `CanRaiseS u' y`
after a raise of `c` with `c ≠ y`, `c ≠ y.twin`. -/
theorem canRaiseS_twin_of_raise_high
    {u u' : State} {c y : Card}
    (huwf : u.WF)
    (hstep : State.step u (Move.tabToFound c) = some u')
    (hcs : c.suit ≠ y.suit)
    (hct : c ≠ y.twin)
    (hrank : y.rank.toIdx ≤ c.rank.toIdx)
    (hS : CanRaiseS u y) :
    CanRaiseS u' y :=
  canRaiseS_of_canRaiseS_raise_high huwf hstep hcs hct hrank hS

#print axioms SafeTransport.canRaiseS_of_canRaiseS_raise_high
#print axioms SafeTransport.canRaiseS_of_raise_high
#print axioms SafeTransport.canRaiseS_of_safePath
#print axioms SafeTransport.canRaiseS_twin_of_raise_high

end SafeTransport
