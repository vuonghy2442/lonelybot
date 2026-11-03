# `Temp/SpectrumCollapse.lean` — report

Status: **green**. `lake env lean Temp/SpectrumCollapse.lean` exits `0`.
No `sorry`, no `Classical`, no `noncomputable`.  Nothing under `Orig2/` and no
existing `Temp/*.lean` card was modified; the fork producers
(`fork_of_spectrum`, `fork_of_collapsed_spectrum`, `twin_raise_square_both`,
`forkWitness_of_spectrum`) are **reused, not reproved**.  In particular
`spectrum_pair_fork_of_blocked` and `spectrum_pair_fork_of_flipped_blocked`
call `fork_of_collapsed_spectrum` directly and lift its `Fork z'` along the
class relation.

## 1. Exact statements

```lean
namespace SpectrumCollapse
open OneColourClosure

theorem drain_pair_stays_live {z z' : State} {d x : Card} (hz : z.WF)
    (hstep : RaiseStepS z z' d)
    (hd : d ≠ x) (hdt : d ≠ x.twin)
    (hx : CanRaiseS z x) (hxt : CanRaiseS z x.twin) :
    CanRaiseS z' x ∧ CanRaiseS z' x.twin

theorem rungSum_raiseStepS {z z' : State} {d : Card} (h : RaiseStepS z z' d) :
    Drain.rungSum z' = Drain.rungSum z + 1

theorem drain_aux (x : Card) (n : Nat) :
    ∀ z : State, z.WF → 52 - Drain.rungSum z ≤ n →
      CanRaiseS z x → CanRaiseS z x.twin →
      ∃ ws z', RaiseSSeqLicensed z ws z' ∧
        (∀ c, CanRaiseS z' c → c = x ∨ c = x.twin) ∧
        sameOrbitSetoid.r z z' ∧
        CanRaiseS z' x ∧ CanRaiseS z' x.twin

theorem spectrum_pair_by_draining {z : State} (hz : z.WF) {x : Card}
    (hx : CanRaiseS z x) (hxt : CanRaiseS z x.twin) :
    ∃ z', sameOrbitSetoid.r z z' ∧
      (∀ c, CanRaiseS z' c → c = x ∨ c = x.twin)

theorem spectrum_pair_by_draining_live {z : State} (hz : z.WF) {x : Card}
    (hx : CanRaiseS z x) (hxt : CanRaiseS z x.twin) :
    ∃ ws z', RaiseSSeqLicensed z ws z' ∧
      (∀ c, CanRaiseS z' c → c = x ∨ c = x.twin) ∧
      sameOrbitSetoid.r z z' ∧ CanRaiseS z' x ∧ CanRaiseS z' x.twin

theorem spectrum_iff_of_subset {z : State} {x : Card}
    (hx : CanRaiseS z x) (hxt : CanRaiseS z x.twin)
    (hsub : ∀ c, CanRaiseS z c → c = x ∨ c = x.twin) :
    ∀ c, (c = x ∨ c = x.twin) ↔ CanRaiseS z c

theorem forkWitness_twin_of_blocked_x {z : State} {x : Card}
    (hx : CanRaiseS z x) (hxt : CanRaiseS z x.twin)
    (hsub : ∀ c, CanRaiseS z c → c = x ∨ c = x.twin)
    (hblk : ¬ CanRaise z x) : ForkWitness z x.twin

theorem spectrum_pair_fork_of_blocked {z z' : State} {x : Card}
    (horb : sameOrbitSetoid.r z z')
    (hx : CanRaiseS z' x) (hxt : CanRaiseS z' x.twin)
    (hsub : ∀ c, CanRaiseS z' c → c = x ∨ c = x.twin)
    (hblk : ¬ CanRaise z' x.twin) : Fork z

theorem spectrum_pair_fork_of_flipped_blocked {z z' : State} {x : Card}
    (horb : sameOrbitSetoid.r z z')
    (hx : CanRaiseS z' x) (hxt : CanRaiseS z' x.twin)
    (hsub : ∀ c, CanRaiseS z' c → c = x ∨ c = x.twin)
    (hblk : ¬ CanRaise z' x) : Fork z

theorem spectrum_pair_trichotomy {z : State} (hz : z.WF) {x : Card}
    (hx : CanRaiseS z x) (hxt : CanRaiseS z x.twin) :
    ∃ z', sameOrbitSetoid.r z z' ∧
      (∀ c, CanRaiseS z' c → c = x ∨ c = x.twin) ∧
      (ForkWitness z' x ∨ ForkWitness z' x.twin ∨
        (CanRaise z' x ∧ CanRaise z' x.twin))

theorem spectrum_pair_dichotomy {z : State} (hz : z.WF) {x : Card}
    (hx : CanRaiseS z x) (hxt : CanRaiseS z x.twin) :
    (∃ z', sameOrbitSetoid.r z z' ∧
      (∀ c, CanRaiseS z' c → c = x ∨ c = x.twin) ∧
      (¬ CanRaise z' x.twin ∨ ¬ CanRaise z' x))
    ∨ (∃ z', sameOrbitSetoid.r z z' ∧
      (∀ c, CanRaiseS z' c → c = x ∨ c = x.twin) ∧
      CanRaise z' x ∧ CanRaise z' x.twin)

theorem spectrum_pair_fork_or_both {z : State} (hz : z.WF) {x : Card}
    (hx : CanRaiseS z x) (hxt : CanRaiseS z x.twin) :
    Fork z ∨
      ∃ z', sameOrbitSetoid.r z z' ∧
        (∀ c, CanRaiseS z' c → c = x ∨ c = x.twin) ∧
        CanRaise z' x ∧ CanRaise z' x.twin

theorem spectrum_pair_both_square {z z' : State} {x : Card}
    (hz' : z'.WF) (hx : CanRaise z' x) (hxt : CanRaise z' x.twin) :
    ∃ zt zc z2 : State,
      State.step z' (Move.tabToFound x.twin) = some zt ∧
      State.step zt (Move.tabToFound x) = some z2 ∧
      State.step z' (Move.tabToFound x) = some zc ∧
      State.step zc (Move.tabToFound x.twin) = some z2

theorem spectrum_pair_fork_or_both_square {z : State} (hz : z.WF) {x : Card}
    (hx : CanRaiseS z x) (hxt : CanRaiseS z x.twin) :
    Fork z ∨
      ∃ z', sameOrbitSetoid.r z z' ∧
        (∀ c, CanRaiseS z' c → c = x ∨ c = x.twin) ∧
        CanRaise z' x ∧ CanRaise z' x.twin ∧
        ∃ zt zc z2 : State,
          State.step z' (Move.tabToFound x.twin) = some zt ∧
          State.step zt (Move.tabToFound x) = some z2 ∧
          State.step z' (Move.tabToFound x) = some zc ∧
          State.step zc (Move.tabToFound x.twin) = some z2
```

### Note on the literal dichotomy template

The template in the brief,

```
(∃ z', ... ∧ ¬ CanRaise z' x.twin) ∨ (∃ z', ... ∧ CanRaise z' x ∧ CanRaise z' x.twin)
```

is **not exhaustive**, and the data does say otherwise.  The missing case is
the *flipped* fork: the drain exposes `x.twin`, but `x` itself is covered, so
`¬ CanRaise z' x.twin` fails, `CanRaise z' x` fails, and yet
`ForkWitness z' x.twin` holds (because `x.twin.twin = x`).  This case is
proved as `forkWitness_twin_of_blocked_x` and is the second arm of
`spectrum_pair_trichotomy`.  The corrected exhaustive statements are
`spectrum_pair_dichotomy` (block on **either** twin, or both vanilla) and
`spectrum_pair_fork_or_both` (the two blocked arms packaged as `Fork z` via
the sibling `Fork` definition).  The first branch is therefore not forced.

## 2. Axiom lines (verbatim from the build)

```
'SpectrumCollapse.drain_pair_stays_live' depends on axioms: [propext, Quot.sound]
'SpectrumCollapse.rungSum_raiseStepS' depends on axioms: [propext, Quot.sound]
'SpectrumCollapse.drain_aux' depends on axioms: [propext, Quot.sound]
'SpectrumCollapse.spectrum_pair_by_draining' depends on axioms: [propext, Quot.sound]
'SpectrumCollapse.spectrum_pair_by_draining_live' depends on axioms: [propext, Quot.sound]
'SpectrumCollapse.spectrum_iff_of_subset' depends on axioms: [propext]
'SpectrumCollapse.forkWitness_twin_of_blocked_x' depends on axioms: [propext]
'SpectrumCollapse.spectrum_pair_trichotomy' depends on axioms: [propext, Quot.sound]
'SpectrumCollapse.spectrum_pair_dichotomy' depends on axioms: [propext, Quot.sound]
'SpectrumCollapse.spectrum_pair_fork_of_blocked' depends on axioms: [propext]
'SpectrumCollapse.spectrum_pair_fork_of_flipped_blocked' depends on axioms: [propext]
'SpectrumCollapse.spectrum_pair_fork_or_both' depends on axioms: [propext, Quot.sound]
'SpectrumCollapse.spectrum_pair_both_square' depends on axioms: [propext, Quot.sound]
'SpectrumCollapse.spectrum_pair_fork_or_both_square' depends on axioms: [propext, Quot.sound]
```

No `sorryAx`, no `Classical.choice`, no `native_decide`, no `noncomputable`.

## 3. Does the endpoint really have spectrum ⊆ pair?

**Blunt answer: yes — `spectrum_pair_by_draining` proves the inclusion on a real
class-mate, obtained by licensed raises only; the block is a separate question,
and the drain is not allowed to assume it.**

The inclusion is unconditional (given the start is `WF` and both twins are
`S`-live).  It is a genuine saturation: each drained letter founds one card,
`Drain.rungSum` rises by exactly one (`rungSum_raiseStepS`), is bounded by 52
(`Drain.rungSum_le_52`), and the census split is constructive, so the endpoint
is reached with no choice.

## 4. Can the drain actually unblock the twin in practice?

Two different hypotheses must be kept apart.

* **The fork context (rank floor `x.rank ≤ d.rank` for every `S`-live `d`).**
  Here the twin's cover has rank `x.rank − 1`, strictly below the floor, so it
  is **not** `S`-live and is never chosen by the drain; raising a live card
  cannot touch it.  The only cargo move that could move the cover would land
  it on the *other* twin, which flips which twin is covered but does not
  unblock both.  The repo's own census is decisive: `Temp/Rewrite_Report.md`
  §13b/§13c records **0 mode-2 (twin-unblocked) events in 460/460 drains**
  (248 named + 212 random two-saturated classes), and every terminal is a
  fork.  In this context the first branch of the dichotomy is the one that
  fires; the both-vanilla branch is vacuous in the sample.

* **The hypotheses of `spectrum_pair_by_draining` (no rank floor).**  A card
  sitting on `x.twin` may itself be `S`-live (its rank can be above
  `x.rank`, e.g. any `S`-live card of an equal-or-higher rank), so the drain
  *can* choose it and remove the cover; the branch is real and is exactly why
  `spectrum_pair_dichotomy` / `spectrum_pair_fork_or_both` exist.  This card
  does **not** contain a kernel-checked concrete board witnessing the unblock,
  and none is claimed: the unconstrained statement is a theorem about all
  `WF` states, and the census above only covers the rank-floor asymmetry
  context.  What *is* kernel-checked is that if the block is lost, the endpoint
  is still a fork whenever the other twin is blocked
  (`forkWitness_twin_of_blocked_x`), and otherwise both twins are vanilla and
  the square `twin_raise_square_both` applies
  (`spectrum_pair_fork_or_both_square`).

So: the drain's endpoint always has spectrum ⊆ pair; it need not have the
twin blocked under the unconstrained hypotheses, and the honest output is the
trichotomy/fork-or-both dichotomy, with the unblocking case absorbed rather
than forced into the first branch.
