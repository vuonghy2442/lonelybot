# Temp/RungMono — report

File: `Temp/RungMono.lean` (imports `Orig2.Fork.Class.ForkRaiseReorderProof`).
Check: `lake env lean Temp/RungMono.lean` → exit 0, no warnings.
Olean: `lake env lean -o .lake/build/lib/lean/Temp/RungMono.olean Temp/RungMono.lean` → exit 0.

No `sorry`, no `Classical`, no `noncomputable`, no new `Prop` definitions.
All rows are stated with `RaiseSSeqLicensed` / `RaiseStepS` hypotheses inline.

## Statements (namespace `OneColourClosure`)

```lean
theorem rungAt_raiseStepS {z z' : State} {c : Card} (h : RaiseStepS z z' c) :
    rungAt z' c.suit = rungAt z c.suit + 1 ∧
      ∀ σ : Suit, σ ≠ c.suit → rungAt z' σ = rungAt z σ

theorem rungAt_eq_of_no_letter {u v : State} {ws : List Card} {σ : Suit}
    (h : RaiseSSeqLicensed u ws v) (hno : ∀ d ∈ ws, d.suit ≠ σ) :
    rungAt v σ = rungAt u σ

theorem rungAt_add_count {u v : State} {ws : List Card}
    (h : RaiseSSeqLicensed u ws v) (σ : Suit) :
    rungAt v σ = rungAt u σ + (ws.filter (fun d => d.suit = σ)).length

theorem rungAt_add_countP {u v : State} {ws : List Card}
    (h : RaiseSSeqLicensed u ws v) (σ : Suit) :
    rungAt v σ = rungAt u σ + ws.countP (fun d => decide (d.suit = σ))

theorem rungAt_le_of_raiseSSeqLicensed {u v : State} {ws : List Card}
    (h : RaiseSSeqLicensed u ws v) (σ : Suit) :
    rungAt u σ ≤ rungAt v σ

theorem rungAt_le {u v : State} {ws : List Card}
    (h : RaiseSSeqLicensed u ws v) (σ : Suit) :
    rungAt u σ ≤ rungAt v σ
```

`rungAt_le` is a one-line alias of `rungAt_le_of_raiseSSeqLicensed`; cite either.

## Axiom lines (verbatim output)

```
'OneColourClosure.rungAt_raiseStepS' depends on axioms: [propext, Quot.sound]
'OneColourClosure.rungAt_eq_of_no_letter' depends on axioms: [propext, Quot.sound]
'OneColourClosure.rungAt_add_count' depends on axioms: [propext, Quot.sound]
'OneColourClosure.rungAt_add_countP' depends on axioms: [propext, Quot.sound]
'OneColourClosure.rungAt_le_of_raiseSSeqLicensed' depends on axioms: [propext, Quot.sound]
'OneColourClosure.rungAt_le' depends on axioms: [propext, Quot.sound]
```

## Reused from `Orig2` (cite these instead of the copies where possible)

| row used | statement | file:line |
|---|---|---|
| `rungAt_tabToFound` | `rungAt v σ = if σ = c.suit then rungAt u σ + 1 else rungAt u σ` for a `tabToFound` step | `Orig2/Substrate/Position.lean:166` |
| `rungAt_cargoPath` | `rungAt a σ = rungAt b σ` for `CargoPath a b` | `Orig2/Fork/Local/ForkCriticalPair.lean:97` |
| `RaiseSSeqLicensed.rungAt_eq` | `rungAt z σ = rungAt s σ + ws.countP (fun c => decide (c.suit = σ))` | `Orig2/Fork/Class/ForkRaiseReorderProof.lean:73` |

Notes:

* `rungAt_raiseStepS` closes `RaiseStepS` by `rungAt_cargoPath` + `rungAt_tabToFound`
  (unpacking `⟨z₀, CargoPath z z₀, step …⟩`); no new ingredient.
* `rungAt_add_countP` **is** `RaiseSSeqLicensed.rungAt_eq` (definitionally), and
  `rungAt_add_count` is that row rewritten with `List.countP_eq_length_filter`.
  Both are in `Orig2`; the main proof can call `RaiseSSeqLicensed.rungAt_eq` directly.
* `rungAt_eq_of_no_letter` is *not* in `Orig2`. It is proved here by induction on
  the licensed play using `rungAt_raiseStepS`. An earlier `countP = 0` route
  (`List.countP_eq_zero` + `simp`) was rejected because `#print axioms` showed
  `Classical.choice`; the induction proof is clean (`[propext, Quot.sound]`).
* `rungAt_le_of_raiseSSeqLicensed` (and its alias `rungAt_le`) is not in `Orig2`;
  it is `Nat.le_add_right` after `rungAt_add_count`.
* An equivalent of `rungAt_cargoPath` also exists as
  `OneColourClosure.cargoPath_rungAt` (`Orig2/Fork/Class/ForkRaiseReorderProof.lean:62`,
  same statement, proved by induction over `Steps`); either may be cited.

## Consequence available to the main proof

`rungAt_eq_of_no_letter` gives suit-local invariance without any licence
side condition beyond the letters themselves, and `rungAt_add_count` makes the
rung gain *exactly* the multiset count — so order/permutation of a licensed
word is invisible to every rung (`rungAt_eq_of_perm` in the ported kit is the
two-word form of the same fact).
