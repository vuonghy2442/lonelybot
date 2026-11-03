import Orig2.Fork.Class.ForkRaiseReorderProof

set_option autoImplicit false

/-!
# Temp/RungMono — the rung monotonicity kit for `raiseS`

A `raiseS` letter climbs exactly one rung of the raised card's suit and fixes
every other rung, so a `raiseS` word only ever *adds* rungs, and the count of
letters of a given suit is the exact rung gain.

Everything here is a port/reuse of rows that already live in `Orig2`:

* `rungAt_tabToFound` (`Orig2/Substrate/Position.lean:166`) — the raise edge;
* `rungAt_cargoPath` (`Orig2/Fork/Local/ForkCriticalPair.lean:97`) — a cargo
  slide holds every rung;
* `RaiseSSeqLicensed.rungAt_eq`
  (`Orig2/Fork/Class/ForkRaiseReorderProof.lean:73`) — the word ledger.

No `sorry`, no `Classical`, no `noncomputable`, no new `Prop`.
-/

namespace OneColourClosure

/-! ## §1. One letter -/

/-- **A `raiseS` letter climbs exactly one rung.**  If `z ⟶ raiseS c ⟶ z'`,
then `c`'s suit gains exactly one rung and every other suit's rung is fixed. -/
theorem rungAt_raiseStepS {z z' : State} {c : Card} (h : RaiseStepS z z' c) :
    rungAt z' c.suit = rungAt z c.suit + 1 ∧
      ∀ σ : Suit, σ ≠ c.suit → rungAt z' σ = rungAt z σ := by
  obtain ⟨z₀, hp, hstep⟩ := h
  refine ⟨?_, ?_⟩
  · rw [rungAt_tabToFound hstep c.suit, ite_eq_left rfl,
      rungAt_cargoPath hp c.suit]
  · intro σ hσ
    rw [rungAt_tabToFound hstep σ, ite_eq_right hσ, rungAt_cargoPath hp σ]

/-! ## §2. Whole words

The word ledger `RaiseSSeqLicensed.rungAt_eq` already says
`rungAt z σ = rungAt s σ + ws.countP (fun c => decide (c.suit = σ))`; the rows
below read it as a sum of counted letters. -/

/-- A word that raises no card of suit `σ` leaves `σ`'s rung unchanged.
Constructive induction over the play (no `countP` decidability detour, so no
`Classical.choice`). -/
theorem rungAt_eq_of_no_letter {u v : State} {ws : List Card} {σ : Suit}
    (h : RaiseSSeqLicensed u ws v) (hno : ∀ d ∈ ws, d.suit ≠ σ) :
    rungAt v σ = rungAt u σ := by
  induction h with
  | nil => rfl
  | cons htail hS hp hstep ih =>
      rename_i z z₀ z' c ws'
      have hc : σ ≠ c.suit :=
        fun hh => hno c (List.mem_cons.mpr (Or.inl rfl)) hh.symm
      have htailno : ∀ d ∈ ws', d.suit ≠ σ :=
        fun d hd => hno d (List.mem_cons.mpr (Or.inr hd))
      have hstep' : rungAt z' σ = rungAt z σ :=
        (rungAt_raiseStepS ⟨z₀, hp, hstep⟩).2 σ hc
      rw [hstep']
      exact ih htailno

/-- **The rung ledger as a sum of counted letters.**  A `raiseS` word gains
exactly as many rungs in `σ` as it contains cards of suit `σ`. -/
theorem rungAt_add_count {u v : State} {ws : List Card}
    (h : RaiseSSeqLicensed u ws v) (σ : Suit) :
    rungAt v σ = rungAt u σ + (ws.filter (fun d => d.suit = σ)).length := by
  rw [RaiseSSeqLicensed.rungAt_eq h σ, List.countP_eq_length_filter]

/-- The same ledger in the `countP` shape of the ported kit. -/
theorem rungAt_add_countP {u v : State} {ws : List Card}
    (h : RaiseSSeqLicensed u ws v) (σ : Suit) :
    rungAt v σ = rungAt u σ + ws.countP (fun d => decide (d.suit = σ)) :=
  RaiseSSeqLicensed.rungAt_eq h σ

/-- **Rungs never decrease along a `raiseS` word.** -/
theorem rungAt_le_of_raiseSSeqLicensed {u v : State} {ws : List Card}
    (h : RaiseSSeqLicensed u ws v) (σ : Suit) :
    rungAt u σ ≤ rungAt v σ := by
  rw [rungAt_add_count h σ]
  exact Nat.le_add_right _ _

/-- Short alias for `rungAt_le_of_raiseSSeqLicensed`. -/
theorem rungAt_le {u v : State} {ws : List Card}
    (h : RaiseSSeqLicensed u ws v) (σ : Suit) :
    rungAt u σ ≤ rungAt v σ :=
  rungAt_le_of_raiseSSeqLicensed h σ

end OneColourClosure

#print axioms OneColourClosure.rungAt_raiseStepS
#print axioms OneColourClosure.rungAt_eq_of_no_letter
#print axioms OneColourClosure.rungAt_add_count
#print axioms OneColourClosure.rungAt_add_countP
#print axioms OneColourClosure.rungAt_le_of_raiseSSeqLicensed
#print axioms OneColourClosure.rungAt_le
