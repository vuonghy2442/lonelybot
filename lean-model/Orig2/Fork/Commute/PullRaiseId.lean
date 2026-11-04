import Orig2.Substrate.Classification

/-!
# Temp/PullRaiseId — the pull is cancelled by the raise

The round trip `foundToTab c b ; tabToFound c` returns to its origin at
`WF` states.  The `WF` premise is not removable: the raw step functions
allow two piles to carry the same card on top, and then `pileOfTop` may
locate the raise's pile at the wrong copy (a concrete counterexample is
recorded in `Temp/PullRaiseId_Report.md`).  At `WF` states the card-count
invariant supplies uniqueness, and the cancellation is total — the
`CanRaise` licence `hcan` is then a consequence of the pull
(`SatDifferConfig.canRaise_after_pull`), not an extra hypothesis.

The proofs read the existing promoted round trip
`step_tabToFound_of_foundToTab` (`Orig2/Substrate/Classification.lean`)
and the pull inverse `step_foundToTab_inv` (`Orig2/Substrate/Kit.lean`).
-/

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **The pull is cancelled by the raise.**  A successful
`foundToTab c b` at a `WF` state is undone by `tabToFound c` of the same
card: the landing `s'` of the raise is the origin `s`. -/
theorem pull_raise_id {s u s' : State} {c : Card} {b : Base}
    (hwf : s.WF)
    (hpull : State.step s (Move.foundToTab c b) = some u)
    (hcan : CanRaise u c)
    (hraise : State.step u (Move.tabToFound c) = some s') :
    s' = s := by
  have hback : State.step u (Move.tabToFound c) = some s :=
    step_tabToFound_of_foundToTab hwf hpull
  rw [hback] at hraise
  exact (Option.some.inj hraise).symm

/-- **The rung corollary**: the cancelled pull leaves every rung where it
was. -/
theorem pull_raise_id_rung {s u s' : State} {c : Card} {b : Base}
    (hwf : s.WF)
    (hpull : State.step s (Move.foundToTab c b) = some u)
    (hcan : CanRaise u c)
    (hraise : State.step u (Move.tabToFound c) = some s') :
    ∀ σ, rungAt s' σ = rungAt s σ := by
  intro σ
  rw [pull_raise_id hwf hpull hcan hraise]

/-- **The state-component form** consumed by the main proof: after the
cancelled pull every field of the state agrees. -/
theorem pull_raise_id_components {s u s' : State} {c : Card} {b : Base}
    (hwf : s.WF)
    (hpull : State.step s (Move.foundToTab c b) = some u)
    (hcan : CanRaise u c)
    (hraise : State.step u (Move.tabToFound c) = some s') :
    s'.found = s.found ∧ s'.piles = s.piles ∧ s'.stock = s.stock ∧
      s'.waste = s.waste ∧ s'.drawStep = s.drawStep := by
  have h : s' = s := pull_raise_id hwf hpull hcan hraise
  subst h
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- **The non-repayable case**: a pull always shortens its suit's rung by
one.  This is unconditional — the pull's `foundToTab` branch writes
`chop` of the suit's foundation, and `foundTop = some c` makes `c` the
last card.  (At `WF` states `h` is contradictory, by
`canRaise_after_pull`; the statement is kept for consumers that only
carry the raw pull.) -/
theorem not_canRaise_after_pull_short {s u : State} {c : Card} {b : Base}
    (hpull : State.step s (Move.foundToTab c b) = some u)
    (h : ¬ CanRaise u c) :
    rungAt u c.suit = rungAt s c.suit - 1 := by
  obtain ⟨c', htop, hc'c, _hcp, hs⟩ := step_foundToTab_inv hpull
  rw [hc'c] at htop
  have hlast : lastOf (s.found c.suit) = some c := htop
  have hfoundu : u.found c.suit = chop (s.found c.suit) := by
    rw [hs, putCard_found, setFound_found_self]
  have hdec : s.found c.suit = chop (s.found c.suit) ++ [c] :=
    lastOf_chop hlast
  have hlen : (s.found c.suit).length =
      (chop (s.found c.suit)).length + 1 := by
    have := congrArg List.length hdec
    simpa using this
  unfold rungAt
  rw [hfoundu]
  omega

#print axioms pull_raise_id
#print axioms pull_raise_id_rung
#print axioms pull_raise_id_components
#print axioms not_canRaise_after_pull_short



