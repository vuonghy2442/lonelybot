# Saturation + strengthened join — report

Status: **both jobs of the `Temp/Saturation.lean` / `Temp/Join_strengthened.lean`
assignment are closed.**  No `sorry`, no `Classical`, no `noncomputable`, no
`axiom`, no `native_decide`; both files exit 0 under `lake env lean`.

Files created (nothing under `Orig2/` and no existing `Temp/` file was touched):

* `Temp/Saturation.lean`
* `Temp/Join_strengthened.lean`

Prerequisite oleans built as instructed:

```
lake env lean -o .lake/build/lib/lean/Temp/Join_raiseS.olean Temp/Join_raiseS.lean      # exit 0
lake env lean -o .lake/build/lib/lean/Temp/Saturation.olean Temp/Saturation.lean        # exit 0
lake env lean -o .lake/build/lib/lean/Temp/Join_strengthened.olean Temp/Join_strengthened.lean  # exit 0
```

(`Temp/Drain_transport_rows.lean` and `Temp/SpecShift_sem.lean` are **not**
imported.)

---

## Job 1 — saturation exists, unconditionally

Exact statement (`Temp/Saturation.lean`):

```lean
theorem OneColourClosure.saturation_exists :
    ∀ s : State, s.WF → ∃ u, sameOrbitSetoid.r s u ∧ SSaturated u ∧
      ∀ σ : Suit, rungAt s σ ≤ rungAt u σ
```

The proof goes through the path-carrying form (needed by Job 2):

```lean
theorem OneColourClosure.saturation_exists_strong :
    ∀ s : State, s.WF → ∃ ws z, RaiseSSeqLicensed s ws z ∧ SSaturated z ∧
      ∀ σ : Suit, rungAt s σ ≤ rungAt z σ
```

and its engine

```lean
theorem OneColourClosure.saturation_aux (n : Nat) :
    ∀ s : State, s.WF → 52 - Drain.rungSum s ≤ n →
      ∃ ws z, RaiseSSeqLicensed s ws z ∧ SSaturated z ∧
        ∀ σ : Suit, rungAt s σ ≤ rungAt z σ
```

### Shape of the proof

* `Nat.strongRecOn` on `52 - Drain.rungSum s`; the bound is
  `Drain.rungSum_le_52`, and the climb is `Drain.rungSum_tabToFound`
  (a `tabToFound` raises the rank sum by exactly one; reused, not reproved),
  plus `rungAt_cargoPath` for the slide star (`rungSum z = rungSum s`).
* If `SSaturated s`, return `s` with the empty licensed word.
* Otherwise the failed saturation test yields a card `c` with `CanRaiseS s c`;
  that is `⟨z, CargoPath s z, CanRaise z c⟩`, and
  `step_tabToFound_of_canRaise` fires `z → z'`.  The one-letter licensed play is
  `RaiseSSeqLicensed.cons (nil) ⟨z,hpath,hcan⟩ hpath hstep`.
* `RaiseSSeqLicensed.wf` gives `z'.WF`; `RaiseSSeqLicensed.revEqW` gives the
  orbit relation at the end; `RaiseSSeqLicensed.rungAt_eq` + `omega` gives the
  rung monotonicity; the recursion appends the new letter with
  `RaiseSSeqLicensed.append`.
* `saturation_exists` projects `sameOrbitSetoid.r s z` from
  `RevEqW_symm (RaiseSSeqLicensed.revEqW hpath hs)`.

### One deviation worth naming

The termination test must be decided constructively.  The file uses the
pre-existing certified probe `rankSatB 12` (`Orig2/Substrate/CargoRaise.lean`,
`rankSatB_iff`) and `Drain.exists_of_all_false` — the constructive witness
extractor from a failed `List.all` (the core `List.all_eq_false` drags
`Classical.choice`).  So the raisable card is *eliminated from the failed probe*
as the plan requires, and no `Classical` enters, but the probe itself is a
`Card.universe` census inside the already-banked `rankSatB`.  If "no
`Card.universe` enumeration" is read as "not even a pre-existing `Bool` census",
this is the one place the file deviates; there is no other decidable read of
`SSaturated` in the repository, and skipping decidability would force
`Classical.choice` by excluded middle.

## Job 2 — the strengthened join from the residue

Exact statement (`Temp/Join_strengthened.lean`):

```lean
theorem OneColourClosure.fullJoinAtLeastRaiseSOrFork_of_residue
    (hres : SatDifferForkWF) :
    FullJoinAtLeastRaiseSOrFork
```

where the target is the one already defined in `Temp/Join_raiseS.lean`:

```lean
def FullJoinAtLeastRaiseSOrFork : Prop :=
  ∀ s s', s.WF → s'.WF → sameOrbitSetoid.r s s' →
    (∃ w, FullJoinAtLeastRaiseS s s' w) ∨ Fork s
```

### Shape of the proof

* Saturate both endpoints with `saturation_exists_strong`, giving `u`, `v`,
  their licensed words, `SSaturated u`, `SSaturated v` and the two rung
  inequalities.
* `u.WF` from `RaiseSSeqLicensed.wf`; `sameOrbitSetoid.r u v` by transitivity of
  the setoid (the two paths plus `hcls`).
* `hres u v hu_wf hsu_sat hsv_sat huv`: a fork witness lifts to `Fork s` by
  `Setoid.iseqv.trans hsu hF`.
* Otherwise the rungs agree.  The split is on the four **decidable `Nat`**
  equalities (`Suit.spade/heart/diamond/club`), never on
  `∃ σ, rungAt u σ ≠ rungAt v σ`.
* In the agreeing branch `w := u`:
  * `FullJoinAtLeast s s' u` from `Nat.max_le` with `hsu_r`, and `hsv_r`
    rewritten across `hEq`;
  * `RungReachableAtLeast s u` is `⟨ws, u, hpathu, le_refl⟩`;
  * `RungReachableAtLeast s' u` is `⟨ws', v, hpathv, Nat.le_of_eq (hEq σ)⟩`.

As requested, the docstring records that this assembly uses **no**
`ForklessHasTop`, `ForklessOrFork` or `ForklessOneColourClosure`; the only
class-level input is the residue itself.

---

## Axiom lines (verbatim)

```
'OneColourClosure.saturation_exists' depends on axioms: [propext, Quot.sound]
'OneColourClosure.saturation_exists_strong' depends on axioms: [propext, Quot.sound]
'OneColourClosure.fullJoinAtLeastRaiseSOrFork_of_residue' depends on axioms: [propext, Quot.sound]
```

(For Job 1 only `saturation_exists` was required; its two auxiliaries carry the
same profile.)

## What `FullJoinAtLeastRaiseSOrFork` now costs

Bluntly: it costs exactly `SatDifferForkWF` — saturation is free, the four-way
rung split is decidable arithmetic, and no top/closure/`Forkless*` hypothesis
remains; so the strengthened join is now only as expensive as the ceiling
campaign's single residue.

---

## Note on the other assignment pasted into the same prompt

The same message also contained a `Temp/SatDiffer_config.lean` /
`Temp/SatDiffer_config_Report.md` assignment (a `SatDifferConfig` structure with
`cargo_second`, `free_persists`, `first_pull_door`, `uncovered_reset` and a
`satDifferForkWF_of_config` reduction).  It was **not** implemented: its field
statements are given only in truncated prose (e.g. "`CargoPath v z` for
`z = sinkTo...`"), and the pull/sink vocabulary it refers to (`sink`,
`applyPulls`, `uncovered_reset`) does not exist anywhere in the repository, so
the four fields cannot be stated faithfully without inventing a new theory.
Repackaging `SatDifferForkWF` into a config field would close the file
vacuously, which is not the requested circuit.  Nothing in that half was
modified or stubbed.
