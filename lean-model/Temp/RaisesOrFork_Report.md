# `Temp/RaisesOrFork` - the raise-or-fork route, branch report

Date: 2026-11-03.  Root `B:\code\lonelybot\lean-model`.
New files only; nothing under `Orig2/` and no existing `Temp/*.lean` modified.

* `Temp/RaisesOrFork.lean` - the Lean card (compiles, `EXIT=0`, no `sorry`,
  no `Classical`, no `noncomputable`).
* `Temp/RaisesOrFork_probe.py` + `Temp/RaisesOrFork_probe_out.txt` - the
  independent falsification probe of the **target itself**.
* `Temp/RaisesOrFork_prepend_probe.py` - the probe of the parent's pull-branch
  mechanism (append / prepend a raise of the pulled card).
* (read only) `Temp/RaisesOrFork_probe_Report.md`, `Temp/RaisesOrFork_probe_s2.py`
  - the sibling card's ungated probe, which my gated probe corroborates.

---

## 0. Verdict

**The main theorem is not closed.**  Three things are closed and kernel-checked
(`Temp/RaisesOrFork.lean`):

1. **The non-twin "insert the raise" branch**, at the grade the plan can
   actually prove it:
   `exists_append_raise_of_word_notMem` and its licence engine
   `canRaiseS_of_word_notMem`.
2. **The drain-to-fork terminal step**, with no invariant and no rank floor:
   `fork_of_collapsed_spectrum` / `fork_of_spectrum`.
3. **The route's payoff**: `fullJoinAtLeastOrFork_of_raises_or_fork` shows the
   target implies `FullJoinAtLeastOrFork` with `w := v`, **no residue, no
   saturation, no `SatDifferForkWF`, no `ForklessHasTop`**.
4. **The deadlock dichotomy at a deficit point** (§2.4), with the commit-lock
   branch closed in both sub-cases (`frozen_of_deficit_lock`) and the first
   cover-descent step (`CoveredAt`) closed.

Plus three supporting facts: the both-vanilla twin square
(`twin_raise_square_both`), and the two rung facts that make the target's
`RungLe s v` conjunct free (`rungAt_le_of_raiseSSeqLicensed`,
`rungLe_of_raiseSSeqLicensed`).

**The one open goal** is the target itself:

```lean
theorem raises_or_fork {s t : State} (hs : s.WF)
    (h : sameOrbitSetoid.r s t) :
    (∃ ws v, RaiseSSeqLicensed s ws v ∧ RungLe s v ∧ RungLe t v) ∨ Fork s
```

Nothing in this card weakens or restates it.  §4 explains exactly where the
induction sticks: the pull-first step needs the same conclusion for the pull's
landing, plus a *replay* lemma (`pull_replay`) that the two proved lemmas do not
supply.

---

## 1. Axiom lines (verbatim from `lake env lean Temp/RaisesOrFork.lean`)

```
'OneColourClosure.canRaiseS_of_word_notMem'                [propext, Quot.sound]
'OneColourClosure.exists_append_raise'                     [propext]
'OneColourClosure.exists_append_raise_of_word_notMem'      [propext, Quot.sound]
'OneColourClosure.twin_raise_square_both'                  [propext, Quot.sound]
'OneColourClosure.rungLe_of_raiseSSeqLicensed'             [propext, Quot.sound]
'OneColourClosure.obstruction_at_deficit'                  [propext, Quot.sound]
'OneColourClosure.covered_at_of_buried'                    [propext, Quot.sound]
'OneColourClosure.frozen_of_deficit_lock'                  [propext, Quot.sound]
'OneColourClosure.obstruction_dichotomy'                   [propext, Quot.sound]
'OneColourClosure.fork_of_collapsed_spectrum'              [propext]
'OneColourClosure.fork_of_spectrum'                        [propext]
'OneColourClosure.raisesOrFork_of_rungLe_rev'              [propext]
'OneColourClosure.raisesOrFork_of_rungEq'                  [propext]
'OneColourClosure.fullJoinAtLeastOrFork_of_raises_or_fork' [propext, Quot.sound]
```

`EXIT=0`; build command:

```
cd B:\code\lonelybot\lean-model
lake env lean Temp/SatDiffer_config.lean   # olean built (it was missing)
lake env lean Temp/Fork_producer.lean      # olean built (it was missing)
lake env lean Temp/RaisesOrFork.lean
```

---

## 2. What each closed statement says (exact)

### 2.1 The "insert the raise" engine (plan step 1, true half)

`RaiseSSeqLicensed` words are in **reverse play order** - the head is the last
raise (`Orig2/Fork/Class/ForkRaiseReorder.lean`, module docstring).  So
`c :: ws` is *the play `ws`, then a raise of `c`*, i.e. the plan's **append**.

```lean
theorem canRaiseS_of_word_notMem {s z : State} {ws : List Card} {c : Card}
    (h : RaiseSSeqLicensed s ws z) (hwf : s.WF) (hc : CanRaiseS s c)
    (hself : c ∉ ws) (htwin : c.twin ∉ ws) : CanRaiseS z c

theorem exists_append_raise {s z : State} {ws : List Card} {c : Card}
    (h : RaiseSSeqLicensed s ws z) (hc : CanRaiseS z c) :
    ∃ z', RaiseSSeqLicensed s (c :: ws) z'

theorem exists_append_raise_of_word_notMem {s z : State} {ws : List Card}
    {c : Card} (h : RaiseSSeqLicensed s ws z) (hwf : s.WF) (hc : CanRaiseS s c)
    (hself : c ∉ ws) (htwin : c.twin ∉ ws) :
    ∃ z', RaiseSSeqLicensed s (c :: ws) z' ∧ RungLe z z' ∧
      rungAt z' c.suit = rungAt z c.suit + 1
```

Proof: rank `≠ c.rank` letters are licence-inert (R1,
`canRaiseS_step_of_rank_ne`); rank `= c.rank` letters other than `c`, `c.twin`
are inert (`SatDifferConfig.licence_lost_only_by_twin`).  The last raise then
fires by `step_tabToFound_of_canRaise`, and the rung arithmetic is
`rungAt_tabToFound` + `rungAt_cargoPath`.

**This is exactly the plan's case (i)**, i.e. "the play contains no `c.twin`
raise, so `c` stays raisable throughout, so append `raise c`".  It holds.

### 2.2 The terminal drain step (plan step 2, closed shape)

```lean
theorem fork_of_collapsed_spectrum {st : State} {x : Card}
    (hx : CanRaiseS st x) (hxt : CanRaiseS st x.twin)
    (honly : ∀ d, CanRaiseS st d → d = x ∨ d = x.twin)
    (hblocked : ¬ CanRaise st x.twin) : Fork st

theorem fork_of_spectrum {st : State} {x : Card}
    (hspec : ∀ c : Card, (c = x ∨ c = x.twin) ↔ CanRaiseS st c)
    (hblocked : ¬ CanRaise st x.twin) : Fork st
```

Definitional through `forkWitness_of_spectrum` (`Temp/Fork_producer.lean`) and
`Fork st := ∃ F x, sameOrbitSetoid.r st F ∧ ForkWitness F x`; the witness
`F = st` with `RevEqW_refl`.  **No `DrainInvariant`, no rank floor** - as the
brief anticipated.  What is *not* closed is producing the collapse (the
well-founded drain loop).

### 2.3 The both-vanilla twin square (the tie case's state-level input)

```lean
theorem twin_raise_square_both {z : State} {c : Card} (hz : z.WF)
    (hc : CanRaise z c) (hct : CanRaise z c.twin) :
    ∃ zt zc z2,
      State.step z (Move.tabToFound c.twin) = some zt ∧
      State.step zt (Move.tabToFound c) = some z2 ∧
      State.step z (Move.tabToFound c) = some zc ∧
      State.step zc (Move.tabToFound c.twin) = some z2
```

A packaged `twin_raise_square` (`Orig2/Fork/Local/ForkCriticalPair.lean:241`):
both orders fire and share the landing state.  This is the state-level input the
tie case names; it is **not** an insertion lemma for an existing play.

### 2.4 The deadlock dichotomy at a deficit point (batch-1 alignment)

The refined plan's "cover/nextUp descent" starts from the obstruction of the
card `c` that must be raised.  Built on `Temp/Obstruction.lean`
(`not_canRaiseS_cases`) and `Temp/FrozenSuit.lean`:

```lean
theorem obstruction_at_deficit {z : State} (hz : z.WF) {c : Card}
    (hnext : z.nextUp c = true) {a : Anchor} (hhold : z.pileHolding c = some a)
    (h : ¬ CanRaiseS z c) :
    (∃ bs run, (z.piles a).faceUp = bs ++ c :: run ∧ run ≠ [] ∧
        z.pileOfTop c.twin = none)
      ∨ (below c (z.piles a).faceUp = [] ∧
          ((z.piles a).hidden ≠ [] ∨ c.rank ≠ Rank.king))

theorem obstruction_dichotomy ... :
    CoveredAt z c ∨
      (below c (z.piles a).faceUp = [] ∧
        ((z.piles a).hidden ≠ [] ∨ c.rank ≠ Rank.king))

theorem frozen_of_deficit_lock {z w : State} {c : Card} {a : Anchor}
    (hz : z.WF) (horb : sameOrbitSetoid.r z w)
    (hnext : z.nextUp c = true) (htop : z.pileOfTop c = some a)
    (hbel : below c (z.piles a).faceUp = [])
    (hlk : (z.piles a).hidden ≠ [] ∨ c.rank ≠ Rank.king) :
    rungAt w c.suit ≤ rungAt z c.suit
```

So at a deficit point the two "structural" disjuncts of the sibling's four-way
obstruction (`nextUp = false`, `pileHolding = none`) are discharged by the
deficit data, and the **commit-lock branch is closed in both sub-cases**
(`hidden ≠ []` via `FrozenSuit.commitLocked_rung_le`, non-king via
`FrozenSuit.commitLocked_rung_le_of_not_king`).  The remaining branch is the
buried one, for which the first descent step (`CoveredAt z c`) is closed here
and the rest is the residual in §8.

### 2.5 Rungs only climb

```lean
theorem rungAt_le_of_raiseSSeqLicensed {s z : State} {ws : List Card}
    (h : RaiseSSeqLicensed s ws z) (σ : Suit) : rungAt s σ ≤ rungAt z σ
theorem rungLe_of_raiseSSeqLicensed {s z : State} {ws : List Card}
    (h : RaiseSSeqLicensed s ws z) : RungLe s z
```

Hence in the target the conjunct `RungLe s v` is **automatic** given the play;
the whole content is `RungLe t v` (or the fork).

### 2.6 The payoff

```lean
theorem fullJoinAtLeastOrFork_of_raises_or_fork
    (h : ∀ s t : State, s.WF → sameOrbitSetoid.r s t →
      (∃ ws v, RaiseSSeqLicensed s ws v ∧ RungLe s v ∧ RungLe t v) ∨ Fork s) :
    FullJoinAtLeastOrFork
```

`w := v`; the orbit conjunct is `RevEqW_symm (RaiseSSeqLicensed.revEqW hplay hs)`
and the rung conjunct is `Nat.max_le.mpr ⟨hsv, hs'v⟩`.

**Blunt sentence: the route does imply `FullJoinAtLeastOrFork` with no
residue, and that implication is kernel-checked here; only the target itself is
open.**

---

## 3. The empirical status of the target (independent probe)

`Temp/RaisesOrFork_probe.py` is an *independent* probe, deliberately **gated
exactly like the target**: it only tests source/target-rung pairs with
`RungLe s (target rungs)`.  (The sibling card's probe, `RaisesOrFork_probe_Report.md`, tests
all ordered pairs, so its 270 240 "failures" are pairs the target never
quantifies over; its headline "failures ⇔ forked" is consistent with, but
different from, the target.)

For each gated pair it asks for the *strongest* form: is the rung tuple of `t`
reachable from `s` by a slides+raises play (not merely dominated)?  The test is
run per **target rung tuple** (the conclusion depends on `t` only through
`rungs t`), so "pairs" below = (source state, distinct target rung tuple) with
`RungLe s (target tuple)`.

| family | components | states | gated pairs | exact rung reached | fork needed | **failures** | saturated strictly below a mate |
|---|---:|---:|---:|---:|---:|---:|---:|
| campaign `s1` (397-state orbit) | 1 | 397 | 7 964 | 7 964 | 0 | **0** | 0 |
| second family | 1 | 44 | 220 | 220 | 0 | **0** | 0 |
| FJ minimal 12-state board | 1 | 12 | 32 | 32 | 0 | **0** | 0 |
| random high-rung, seed 4242 | 400 | 44 508 | 638 426 | 638 426 | 0 | **0** | 0 |
| random high-rung, seed 987654 | 400 | 55 335 | 1 000 947 | 1 000 947 | 0 | **0** | 0 |
| random high-rung, seed 31337 | 400 | 51 994 | 1 053 824 | 1 053 824 | 0 | **0** | 0 |
| **COMPLETE** `enum_boards(K=3, tab≤5)` (all 4 183 859 boards) | 2 398 179 | 9 703 967 | 29 833 891 | 29 833 891 | 0 | **0** | 0 |
| `enum_boards(K=4, tab≤5)`, 120 s generator prefix | 1 051 740 | 1 334 368 | 1 601 964 | 1 601 964 | 0 | **0** | 0 |

**Totals: 8 216 + 2 693 197 + 29 833 891 + 1 601 964 = 34 137 268 gated pairs
over 3 451 122 WF components (11 190 625 states) - 0 failures.**  In every
single instance the **exact** rung tuple of `t` is raiseS-reachable from `s`, so
the fork disjunct is never even needed; and no `S`-saturated state is strictly
below an orbit mate (4 739 saturated states in the random rows alone, 2 in the
campaign orbit; 0 hits).

The two `enum_boards` rows use the vetted `Temp/Search_enum.enum_boards`
(K = rank prefix, `tab` = face-up card bound) in generator order; each consumed
its full 120 s, so those rows are *prefixes*, not completed enumerations.
`Temp/RaisesOrFork_enum3.py` runs the `K=3, tab≤5` family to the end
(4 183 859 canonical boards); see §3.1.

### 3.1 The completed `K=3, tab≤5` enumeration

`python Temp/RaisesOrFork_enum3.py 2400` walks all 4 183 859 canonical boards,
dedups components and runs the gated test on each.  Raw log:
`Temp/RaisesOrFork_enum3_out.txt`; the run prints its own
`FINAL boards=... complete=True/False ...` line.  The prefix of 600 000 boards
(503 540 components, 1 032 095 states) already had `failures=0 sat_below=0`;
the final line supersedes it and is quoted here:

```
FINAL boards=4183859/4183859 complete=True comps=2398179 states=9703967
      pairs=29833891 exact=29833891 dom=29833891 needed_fork=0 failures=0
      sat_below=0 time=1449s
```

That is a **complete exhaustive family**: all 4 183 859 canonical boards with
rank prefix `K=3` and at most 5 face-up cards, 2 398 179 distinct components,
29 833 891 gated pairs, **0 failures**, 0 fork-necessities and 0 saturated
states below a mate.  (It is the `K=3/tab≤5` row of the table above.)

---

## 4. The pull branch: what the parent's mechanism does and does not give

The plan for the pull-first step:

> `s --(pull c b)--> u`, IH gives `ρ : u → v` with `rungs v ≥ t`; the deficit
> is only `c.suit`, so `ρ` raises no `c`; **prepend lemma** gives
> `RaiseSSeqLicensed u (c :: ρ) v'`; and since `pull c ; raise c = id` at `s`,
> the tail starts at `s`, so this is a raiseS play **from `s`**.

Three separate points, in order of certainty.

### 4.1 The cancellation identity is already in the library

```lean
-- Orig2/Substrate/Position.lean:688
theorem foundToTab_pull_back {s t : State} {c : Card} {b : Base}
    (hwf : s.WF) (hstep : State.step s (Move.foundToTab c b) = some t) :
    State.step t (Move.tabToFound c) = some s
```

So `pull_raise_id` needs **no** new proof (and, being a state computation, it is
true).

### 4.2 The append lemma is true and now proved (with the twin excluded)

`Temp/RaisesOrFork_prepend_probe.py` tests the *firing* statement with the
state-set BFS (`cargo closure`, then fire the raise), i.e. the exact conclusion
of `exists_append_raise_of_word_notMem`:

* play `ρ` first, then `raise c` (the Lean word `c :: ρ`);
* `ρ` contains **no** letter of `c`'s suit and **no** `c.twin`
  (the deficit argument gives the first; the plan's case split excludes the
  second):

**5 041 pull edges, 4 531 sampled plays (length ≤ 4), 39 107 rung checks:
0 firing failures and 0 rung failures.**  This is exactly the region covered by
the Lean theorem, so the probe and the proof agree.

Allowing `c.twin` in `ρ` produces failures (67 in the same sample) - the
residual the plan calls the twin case.

### 4.3 The "hence a play from `s`" step is **not** implied by 4.1 + 4.2

Two different orders are in play, and they must not be conflated.

* **String order.** `RaiseSSeqLicensed` words are in reverse play order, so the
  proved lemma's word `c :: ρ` is *play `ρ`, then `raise c`* (the **append**
  order).  Its conclusion is a play **from the pull's landing `u`**:
  `RaiseSSeqLicensed u (c :: ρ) v'`.
* **The order step 3 needs.** For "the tail starts at `s`" the raise must come
  **first**: `u --raise c--> s --ρ--> v'`, i.e. the map must contain a licensed
  play `s` --ρ--> ... .  That is a *replay of the same word* `ρ` from `s`, which
  is not what `canRaiseS_of_word_notMem` proves (it proves that `ρ` does not
  destroy `c`'s licence at its endpoint).

The cancellation identity `pull c ; raise c = id` (`foundToTab_pull_back`)
does not bridge them either: it says `u --raise c--> s`, a statement about
`u → s`, not a transport of `ρ`.

So the precise missing lemma is

```lean
-- the pull replay: the SAME word, replayed at the pull's source
theorem pull_replay {s u v : State} {c : Card} {b : Base} {ws : List Card}
    (hwf : s.WF) (hpull : State.step s (Move.foundToTab c b) = some u)
    (hρ : RaiseSSeqLicensed u ws v)
    (hnosuit : ∀ d ∈ ws, d.suit ≠ c.suit) (htwin : c.twin ∉ ws) :
    ∃ v', RaiseSSeqLicensed s ws v'
```

This is *not* refuted: in the plan's region (`ρ` has no `c`-suit letter and no
`c.twin`) the c-first reading fires in **769 / 769** sampled instances, and the
append reading in **4 531 / 4 531** (`Temp/RaisesOrFork_prepend_probe.py`).
It is also not proved: it needs a licence **and** cargo-path transport across
the pull, which is strictly more than the two lemmas above.

An earlier run of the same probe *without* the `c.twin` exclusion produced
**67 / 4 531** append failures and **75 / 1 674** c-first failures; those are
exactly the twin cases the plan sends to the fork branch (e.g. the FJ minimal
orbit: `s = F<AH2H3H4H AD2D3D AS2S3S> P{4:5S4D3C | 5:5C}`, pull `4H`,
`ρ = [raise 4D]`, where `4D = 4H.twin`; after raising `4H` we are back at `s`
and `4D` is buried under `5S` with no legal 6-red seat, so neither order fires).
So the exclusion is load-bearing, and the twin exclusion is exactly the case
split's boundary.

### 4.4 The residual, stated precisely

The pull-first case reduces to the replay lemma of §4.3:

> **Open (pull case).**  `s.WF`, `RungLe s t`, `step s (foundToTab c b) = some u`,
> and `ρ : u → v` licensed with `RungLe t v`, no `c`-suit letter, no `c.twin`.
> Then `∃ ws v', RaiseSSeqLicensed s ws v' ∧ RungLe t v'`
> (the rungs then work: `rungs v' ≥ rungs u + e_c` rungwise on `c.suit`, which
> repairs the one-suit deficit and leaves the other suits at `≥ rungs t`).

The twin sub-case needs: if a licensed play raises `c.twin` at a point where
both `c` and `c.twin` are vanilla-raisable, `twin_raise_square`
(`Orig2/Fork/Local/ForkCriticalPair.lean:241`) commutes them, so `c` can still
be inserted; otherwise the spectrum collapses and §2.2 gives the fork.  Neither
of those two sub-arguments is formalised here.

---

## 5. Controls

* `kept oleans`: `Temp/SatDiffer_config.olean` and `Temp/Fork_producer.olean`
  did not exist; they were built with
  `lake env lean -o .lake/build/lib/lean/Temp/<name>.olean Temp/<name>.lean`.
  No source file changed.
* `#print axioms` on every theorem: all `[propext]` or
  `[propext, Quot.sound]`; nothing depends on `Classical.choice`, no `sorryAx`.
* Two new Python probes only; `Temp/RaisesOrFork_probe_out.txt` is the raw run.
* The sibling report `Temp/RaisesOrFork_probe_Report.md` is left untouched; my
  probe is independent of it (different gating, different analysis: exact-rung
  reachability rather than domination-only).

## 6. Reproduce

```
cd B:\code\lonelybot\lean-model
lake env lean Temp/RaisesOrFork.lean
python Temp/RaisesOrFork_probe.py 240          # ~4 min, writes nothing
python Temp/RaisesOrFork_prepend_probe.py 90   # ~14 min (component BFS heavy)
```

## 7. Blunt summary

* **Closed:** the non-twin raise insertion (licence persistence + append), the
  terminal spectrum-collapse fork, and the kernel-checked reduction
  `target ⇒ FullJoinAtLeastOrFork` with `w := v` and **no residue**.
* **Open, single named goal:** `raises_or_fork`, exactly as stated in §0.
  The gap is the pull-first induction step: the proved append lemma produces a
  play from the pull's landing, while the step needs the same word replayed at
  the pull's source (`pull_replay`, §4.3); the `pull ; raise = id` identity does
  not supply that transport.  The lemma is empirically unrefuted (769/769).
* **Empirically:** 34 137 268 gated pairs, 0 failures, exact rung tuple always
  reachable; so the open goal looks like a theorem, and the fork disjunct is not
  needed in the observed data.

---

## 8. Batch-1 alignment (refined pull case)

`Temp/RaisesOrFork.lean` now imports `Temp.RungMono`, `Temp.PullRaiseId`,
`Temp.Obstruction`, `Temp.FrozenSuit` and does **not** duplicate any of their
lemmas.

### 8.1 What changed

* deleted my earlier `rungAt_le_of_raiseSSeqLicensed` (it duplicated
  `RungMono.rungAt_le`, and the *sibling's* name of that shape is the guarded,
  reversed one - the naming trap in the coordination note).  The `RungLe`-shaped
  corollary `rungLe_of_raiseSSeqLicensed` now delegates to `RungMono.rungAt_le`.
* added `obstruction_at_deficit`, `covered_at_of_buried`,
  `obstruction_dichotomy`, `frozen_of_deficit_lock` (§2.4).
* `pull_raise_id` is **not** reproved: `Temp.PullRaiseId.pull_raise_id` and
  `Orig2/Substrate/Position.lean`'s `foundToTab_pull_back` are used as-is
  (`pull_raise_id` needs `s.WF`, which the induction has).

### 8.2 Closed parts of the refined plan

| plan step | status |
|---|---|
| (2)/(3) the obstruction of the card to raise, at a deficit point | **closed**: `obstruction_dichotomy` (cover, or lock) |
| commit-lock branch "harmless" | **closed in both sub-cases**: `frozen_of_deficit_lock` (hidden deck / non-king) |
| first step of the cover descent | **closed**: `CoveredAt z c` from the buried obstruction |
| append `raise c` when the play avoids `c`, `c.twin` | **closed**: `exists_append_raise_of_word_notMem` |
| both-vanilla twins: both orders fire | **closed**: `twin_raise_square_both` |
| terminal spectrum collapse ⇒ `Fork` | **closed**: `fork_of_collapsed_spectrum` |
| target ⇒ `FullJoinAtLeastOrFork`, no residue | **closed**: `fullJoinAtLeastOrFork_of_raises_or_fork` |
| **replay `ρ` at the pull's source** | **open** (the residual below) |
| twin interlock ⇒ `Fork` (the `cover_seats` assembly) | **open** |
| append at the *upper boundary of `c`'s rank block* + `raiseS_rankfront_L` + cancel | **open** |

### 8.3 The precise residual, in Lean syntax

```lean
-- (R1) THE PULL REPLAY.  The refined plan's step 1: the same word at the source.
theorem pull_replay {s u v : State} {c : Card} {b : Base} {ws : List Card}
    (hwf : s.WF) (hpull : State.step s (Move.foundToTab c b) = some u)
    (hρ : RaiseSSeqLicensed u ws v)
    (hnosuit : ∀ d ∈ ws, d.suit ≠ c.suit) (htwin : c.twin ∉ ws) :
    ∃ v', RaiseSSeqLicensed s ws v'

-- (R2) TWIN INTERLOCK ⇒ FORK.  At a point where the spectrum has collapsed
-- onto the pair and one twin is vanilla-blocked, the fork witness is
-- `fork_of_collapsed_spectrum`; what is missing is producing the spectrum
-- collapse from the cover descent (the `cover_seats` assembly).
--   shape:  (∀ d, CanRaiseS z d → d = c ∨ d = c.twin)
--           ∧ CanRaiseS z c ∧ ¬ CanRaise z c.twin  →  Fork z
--   the implication itself is closed (`fork_of_collapsed_spectrum`); the
--   spectrum hypothesis is what the drain has to produce.

-- (R3) THE UPPER-BOUNDARY INSERTION.  Append `raise c` at the top of c's rank
-- block rather than at the end of `ρ`:
theorem insert_at_rank_block {u v : State} {ws : List Card} {c : Card}
    (h : RaiseSSeqLicensed u ws v) (hc : CanRaiseS u c)
    (hblock : ∀ d ∈ ws, c.rank < d.rank) :          -- the tail above the block
    ∃ v', RaiseSSeqLicensed u (c :: ws) v'
```

`(R1)` is the one the coordination note calls "play `ρ` replayed at `s`"; it is
*not* implied by `rungAt` bookkeeping, because it must transport cargo-path
existence, not only licences.  `(R3)` is the ordered variant of the append
lemma: the tail has strictly larger rank, so R1
(`canRaiseS_step_of_rank_ne`) is inert on it - but the play prefix must still
be reordered, which is `raiseS_rankfront_L` territory.  **`(R3)` is a shape, not
a claim**: the real obligation composes `raiseS_rankfront_L` with a permutation
of `ws`, so it has to be stated at the word-permutation grade (a literal
`c :: ws` is one of the two orders, and §4.3 shows which one carries the play).

### 8.4 Where the sibling statements did **not** fit

* `RungMono.rungAt_le_of_raiseSSeqLicensed` is the *guarded* row with the
  inequality running `z → s`; the unconditional monotone needed for `RungLe` is
  `RungMono.rungAt_le`.  Both were needed at different places - using the wrong
  one type-checks in the `≤` direction only by accident of the guard.
* `Obstruction.not_canRaiseS_cases` and `covered_of_not_canRaiseS` live in the
  **root** namespace, not `Obstruction.*` (the file declares no namespace).
* The four-way obstruction's third disjunct bundles `hidden ≠ [] ∨ x ≠ king`;
  `FrozenSuit.commitLocked_rung_le` wants `hidden ≠ []` and
  `commitLocked_rung_le_of_not_king` wants `x ≠ king`, so the disjunction is
  covered **only** by dispatching on it (done in `frozen_of_deficit_lock`).
* `not_canRaiseS_cases`'s buried disjunct gives `faceUp = bs ++ c :: run` with
  `run ≠ []`, i.e. it already knows `c` is not a top; the plan's phrase "the
  right invariant is head-of-run, not pile-top" matches what the file produces -
  no mismatch, but `pileOfTop c = some a` must be supplied separately to get
  `below`/`hidden` at the same anchor, which is why `obstruction_at_deficit`
  takes `pileHolding c = some a` as an explicit hypothesis.
