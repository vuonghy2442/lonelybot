# `Temp/RungMono.lean` — report

Status: `lake env lean Temp/RungMono.lean` exits **0**, no `sorry`, no
`Classical.choice`, no `noncomputable`, nothing outside `Temp/RungMono.lean`
touched.

The theorems live in `namespace RungMono` (they are also reachable after
`open RungMono`); they are stated over `OneColourClosure.RaiseStepS` /
`OneColourClosure.RaiseSSeqLicensed` and `OneColourClosure.rungAt`.

## Exact statements

```lean
theorem RungMono.rungAt_raiseStepS {z z' : State} {c : Card}
    (h : RaiseStepS z z' c) :
    rungAt z' c.suit = rungAt z c.suit + 1 ∧
      ∀ σ : Suit, σ ≠ c.suit → rungAt z' σ = rungAt z σ

theorem RungMono.rungAt_eq_of_no_letter {s z : State} {ws : List Card}
    (h : RaiseSSeqLicensed s ws z) {σ : Suit}
    (hno : ∀ d ∈ ws, d.suit ≠ σ) :
    rungAt z σ = rungAt s σ

theorem RungMono.rungAt_le_of_raiseSSeqLicensed {s z : State} {ws : List Card}
    (h : RaiseSSeqLicensed s ws z) {σ : Suit}
    (hno : ∀ d ∈ ws, d.suit ≠ σ) :
    rungAt z σ ≤ rungAt s σ

theorem RungMono.rungAt_add_count {s z : State} {ws : List Card}
    (h : RaiseSSeqLicensed s ws z) (σ : Suit) :
    rungAt z σ = rungAt s σ +
      (ws.filter (fun d => decide (d.suit = σ))).length

theorem RungMono.rungAt_le {s z : State} {ws : List Card}
    (h : RaiseSSeqLicensed s ws z) (σ : Suit) :
    rungAt s σ ≤ rungAt z σ
```

`rungAt_le` is the requested *unconditional* monotonicity (no hypothesis on
`ws`).  `rungAt_le_of_raiseSSeqLicensed` is the weaker `hno`-guarded variant
that was already in the file when it was rewritten by the parallel worker; the
two coexist.

## Axiom lines

```text
'RungMono.rungAt_raiseStepS' depends on axioms: [propext, Quot.sound]
'RungMono.rungAt_eq_of_no_letter' depends on axioms: [propext, Quot.sound]
'RungMono.rungAt_le_of_raiseSSeqLicensed' depends on axioms: [propext, Quot.sound]
'RungMono.rungAt_add_count' depends on axioms: [propext, Quot.sound]
'RungMono.rungAt_le' depends on axioms: [propext, Quot.sound]
```

## How

Nothing is reproved: `rungAt_raiseStepS` is
`rungAt_tabToFound` (`Orig2/Substrate/Position.lean:166`) composed with
`cargoPath_rungAt` (`Orig2/Fork/Class/ForkRaiseReorderProof.lean:62`, which is
`rungAt_cargoPath` in `Orig2/Fork/Local/ForkCriticalPair.lean:97`);
`rungAt_add_count` is the word ledger
`RaiseSSeqLicensed.rungAt_eq` (`ForkRaiseReorderProof.lean:73`) plus
`List.countP_eq_length_filter`; `rungAt_le` is `Nat.le_add_right` on that.

Note on constructivity: the `rungAt_eq_of_no_letter` proof here is by
induction on the word (no classical reasoning).  An earlier draft discharged
the count with `List.countP_eq_zero` + `simp`, which pulled
`Classical.choice` into the axiom line; the inductive form keeps the file at
`[propext, Quot.sound]`.

## Addendum (verified in this session)

* `List.filter` in Lean 4 core has type `(α → Bool) → List α → List α`, so the
  ledger's predicate must be written `fun d => decide (d.suit = σ)` (the
  brief's `fun d => d.suit = σ` does not elaborate).  This is exactly
  `List.countP (fun d => decide (d.suit = σ))` up to
  `List.countP_eq_length_filter`, i.e. the same quantity.
* `rungAt_raiseStepS` is stated over the **weak** `RaiseStepS` (which admits
  commit raises), so it is a fortiori available for the licensed relation;
  the three word-level rows are stated over `RaiseSSeqLicensed` as requested.
* Nothing in `Orig2/` was modified; the only files touched are
  `Temp/RungMono.lean` and this report.
* Re-verified: `lake env lean Temp/RungMono.lean` exits 0 and the five
  `#print axioms` lines are exactly the `[propext, Quot.sound]` list above.
