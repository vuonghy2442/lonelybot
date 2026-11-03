# `(R)` — the corrected componentwise `RungLe` probe

Follow-up to `Temp/SatDiffer_vacuity_Report.md` (same session, same model).
The earlier `RungLe` probe results are discarded: its generator produced
non-`WF` ascending runs (see §4 of the vacuity report). This card redoes the
probe properly.

## What is tested

`(R)` (raiseS-only):

> `sameOrbit s s'` and `RungLe s s'` (componentwise: `∀ σ, rungAt s σ ≤ rungAt s' σ`)
> ⇒ some **raiseS-only licensed** play from `s` ends at rungs `= rungs s'`.

The letter set is the licensed `raiseS` relation of
`Orig2/Fork/Class/ForkRaiseReorder.lean` (`RaiseStepS` under the
`RaiseSSeqLicensed` licence, `CanRaiseS`): a letter is *slide-star (reversible
`tabToTab`) then one licensed raise (`tabToFound`)*. **No `foundToTab` pulls,
no draws.** At `WF`, `CanRaiseS` and reversibility of the raise coincide, so
in the compact model the letters are exactly `c_moves` filtered to
`{tabToTab, tabToFound}`.

Two consequences are used and were checked empirically:

* slides preserve rungs, so the raiseS-reachable **rung tuples** are the
  closure under `{slides, licensed raises}`;
* at an `SSaturated` state no raise is licensed anywhere in its slide fibre,
  so its only raiseS-reachable rung tuple is its own — hence at a saturated
  `s`, `(R)` says every comparable orbit mate has **equal** rungs. This is
  the "no saturated state is strictly below another orbit state" claim.

Note the pair test is componentwise, so the previously found instances
(`s1 (5,0,4,2)` vs `t1 (5,0,2,5)`, and the second family
`(0,1,4,3)` vs `(0,1,3,4)`) are **incomparable** and are *not* witnesses
against `(R)`. That is exactly the point of this follow-up.

---

## 1. Generator correction and `WF` filter

`legal_runs` now walks **down** one rank at a time
(`can_sit_on(c,b) := c.rank + 1 == b.rank`, face-up runs are descending
bottom-first), and every seed is passed through `Search_lib.to_full`, which
asserts the model's `WF` (wrapped in `try/except`).

Seed survival (raw `seed_state`/walk attempts → components whose final state
passes `to_full`):

| sweep seed | attempts | WF-surviving | rate |
|---|---|---|---|
| 1 | 27 896 | 900 | 3.2% |
| 424242 | 7 921 | 250 | 3.2% |
| 31337 | 7 110 | 250 | 3.5% |
| 2026 | 6 693 | 250 | 3.7% |
| 555 | 14 759 | 500 | 3.4% |
| 8675309 | 14 210 | 500 | 3.5% |
| **total** | **78 589** | **2 650** | **3.37%** |

The component graph is symmetric on `WF` states (asserted on the campaign
orbit, the second family, and every 50th random component); mutual
reachability therefore equals `reach`, which is what the sweep uses.

---

## 2. Coverage

For every component: every `SSaturated` `u` and every orbit mate `v` with
`RungLe u v` was checked for `rungs u = rungs v`; and for every non-saturated
`s`, every orbit mate rung tuple `rv` with `RungLe s rv` was checked against
the raiseS-reachable rung set from `s`.

### 2.1 The two known instance families

| family | orbit | saturated | saturated strict-comparable hits | full-(R) pairs checked | unreachable |
|---|---|---|---|---|---|
| campaign (`s1`, `t1`) | 397 | 2 | **0** | 7 567 | **0** |
| second (`A`, `B`) | 44 | 4 | **0** | 176 | **0** |

In the campaign orbit the two saturated states are `s1 (5,0,4,2)` and
`t1 (5,0,2,5)`; both are `RungLe`-maximal in the orbit (the only rung tuple
dominating either is itself), but they are incomparable to each other.
In the second family the four saturated states sit at `(0,1,4,3)` (×2) and
`(0,1,3,4)` (×2), again both maximal and mutually incomparable.

### 2.2 Random `WF`-valid components

| sweep seed | components | states | saturated | pull-bearing | with a strict pair | source/target pairs | reachable | **unreachable** | sat. strict hits |
|---|---|---|---|---|---|---|---|---|---|
| 1 | 900 | 8 240 | 1 524 | 585 | 585 | 37 049 | 37 049 | **0** | **0** |
| 424242 | 250 | 2 725 | 406 | 161 | 161 | 29 686 | 29 686 | **0** | **0** |
| 31337 | 250 | 2 048 | 421 | 172 | 172 | 6 553 | 6 553 | **0** | **0** |
| 2026 | 250 | 1 668 | 396 | 161 | 161 | 5 332 | 5 332 | **0** | **0** |
| 555 | 500 | 3 723 | 844 | 327 | 327 | 14 506 | 14 506 | **0** | **0** |
| 8675309 | 500 | 3 725 | 868 | 334 | 334 | 11 041 | 11 041 | **0** | **0** |
| **random total** | **2 650** | **22 129** | **4 459** | **1 740** | **1 740** | **104 167** | **104 167** | **0** | **0** |
| **total incl. 2 families** | **2 652** | **22 570** | **4 465** | — | — | **111 910** | **111 910** | **0** | **0** |

**Not a vacuous test:** 1 740 / 2 650 random components (65.7%) contain at
least one `foundToTab` pull letter, and exactly the same 1 740 (65.7%) contain
a strict comparable pair of rung tuples somewhere in the orbit. This is not a
coincidence: in a symmetric reversible orbit a raise and its inverse pull come
together, and any raise creates a strict comparable pair (its pre-state is
below its post-state), so *strict comparability*, *raise-bearing* and
*pull-bearing* coincide. The campaign orbit has 594 pull letters and 39 rung
tuples; the second family has 52 pull letters and 15 rung tuples. So the sweep
is genuinely exercising pull-bearing orbits, not just raiseS-closed ones.

### 2.3 Adversarial high-rung sweep

Seeds with rungs 2..5 and deeper runs, so `foundToTab` pulls are available
immediately and the full orbit is much larger. Same analysis.

| sweep seed | components | states | saturated | pull-bearing | with a strict pair | pairs checked | **unreachable** | sat. strict hits |
|---|---|---|---|---|---|---|---|---|
| 4242 | 500 | 54 257 | 1 755 | 466 | 466 | 751 958 | **0** | **0** |
| 987654 | 500 | 74 522 | 1 907 | 467 | 467 | 1 350 159 | **0** | **0** |
| **total** | **1 000** | **128 779** | **3 662** | **933** | **933** | **2 102 117** | **0** | **0** |

93.3% of these components are pull-bearing, and the same 933 contain a strict
comparable pair; the largest component has 3 960 states. Seed survival here is
higher (503/8 872 = 5.7% and 504/9 779 = 5.2%) because the rungs are forced
above 0. Still zero failures — every comparable target rung tuple is
raiseS-reachable, including from states far from saturation.

`424242` includes a 1 256-state component with 8 saturated states; the
high-rung sweep pushes the largest component to 3 960 states. `31337` includes
the two components that supplied the second/third instance families of the
vacuity report.

**No counterexample anywhere: all 2 214 027 comparable source→target rung
pairs (across all 3 652 orbits) were raiseS-reachable.**

### 2.4 The saturation lemma

For every saturated state in every component we also checked

> `raiseS_rungs(u) = {rungs u}`

(the formal reason: `CanRaiseS` is invariant up the slide fibre, so a
saturated state has no licensed raise there, and slides do not move rungs).

* violations over 8 127 saturated states: **0**
* largest raiseS rung-set seen from any state (main sweep): 48 rung tuples.

---

## 3. Constructive witnesses (spot checks that the closure is real)

The closure is a BFS in the raiseS graph; to show it is not permissive we
reconstructed explicit plays and replayed them move by move.

Campaign orbit — four sample `(R)` instances (`Temp/RungLe_construct.py`):

```
(0,0,0,2) -> (4,0,3,2):
    raise AH ; raise AS ; raise 2H ; raise 2S ; raise 3H ; raise 3S ; raise 4H
(0,0,0,2) -> (5,0,2,5):                      # t1's rung tuple
    raise AH ; raise AS ; raise 2H ; raise 2S ; raise 3H ; slide 2D->3S ;
    raise 3C ; raise 4C ; slide 3S->4D ; raise 4H ; raise 5H ; raise 5C
(0,0,0,2) -> (5,0,4,2):                      # s1's rung tuple
    raise AH ; raise AS ; raise 2H ; raise 2S ; raise 3H ; slide 2D->3C ;
    raise 3S ; raise 4S ; slide 3C->4D ; raise 4H ; slide 4C->5D ; raise 5H
(2,0,4,0) -> (2,0,4,2):
    raise AC ; raise 2C
```

All letters are `tabToTab`/`tabToFound` only; the endpoint rungs match. The
second and third examples reach, respectively, `t1`'s and `s1`'s rung tuples
from a low state in their own orbit — with **no pulls** — which is exactly the
`(R)` content.

---

## 4. Verdict

**No counterexample to `(R)` was found.** In particular the weaker claim
survives every test:

> **no `S`-saturated state is strictly below another orbit state in the
> componentwise rung order.**

Across 3 652 mutual orbits — 151 349 states, 8 127 saturated states, 2 214 027
comparable source/target pairs — there is not one saturated `u`, orbit mate
`v`, with `RungLe u v` and `rungs u ≠ rungs v`, and no non-saturated failure
of the raiseS-reachability conclusion either. The probe checked precisely the
conclusion of `(R)` on every comparable pair (not only the saturated special
case) and found zero exceptions, so the evidence points at `(R)` being a
theorem (rank-front / raiseS-reordering territory in
`Orig2/Fork/Class/ForkRaiseReorder.lean`), not merely a surviving residue.

Blunt sentence: **"no strictly comparable saturated pair" survives this probe
— it is not refuted by any of the 3 652 orbits (8 127 saturated states), so the
campaign can keep using it, while the stronger "saturated ⇒ rung top" remains
false exactly because `s1`/`t1` are incomparable saturated maxima of one
orbit.**

No `Temp/RungLe_counterexample.lean` was written: there is no counterexample
to kernel-check.

---

## 5. Reproduce

```
cd lean-model
python Temp/RungLe_probe.py 900 1 4000
python Temp/RungLe_probe.py 250 424242 3000
python Temp/RungLe_probe.py 250 31337 3000
python Temp/RungLe_probe.py 250 2026 3000
python Temp/RungLe_probe.py 500 555 4000
python Temp/RungLe_probe.py 500 8675309 4000
python Temp/RungLe_probe_hi.py 500 4242 4000
python Temp/RungLe_probe_hi.py 500 987654 4000
python Temp/RungLe_construct.py
```

New files (all under `Temp/`, nothing in `Orig2/` modified):
`RungLe_probe.py`, `RungLe_probe_hi.py`, `RungLe_construct.py`, this report.
