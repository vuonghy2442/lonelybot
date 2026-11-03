# One-sided raise-or-fork — empirical probe

**Claim tested.** For any two orbit mates `s`, `t` (mutual reversible witness
reachability):

> either there is a **raiseS-only** licensed play from `s` to some `v` with
> `rungs v ≥ rungs t` (componentwise, incomparable targets allowed),
> **or** the class of `s` is forked.

`raiseS` = slide-star (reversible `tabToTab` closure) then one licensed rise
(`tabToFound`); no `foundToTab` pulls, no draws. Fork = `∃` class mate `F` with
`c_live(F) == {x, twin(x)}` and `x.twin ∉ c_can_raise_set(F)`.

## Verdict (up front)

**The claim survives. 270 240 failures of the raise-up test were found, and
every single one lies in a forked component: zero counterexamples.** On this
data the disjunction is in fact an equivalence — the components where the
raise-up test fails are exactly the forked components, and exactly the
components with ≥ 2 Pareto-maximal rung tuples.

---

## 1. Method (and why the fibre abstraction is exact)

Model: `Temp/Search_lib.py` compact witness model (`c_step`, `c_moves`,
`c_cargo_closure`, `c_can_raise_set`, `c_live`, `c_fibers`, `c_component`).

* **Slide fibres.** `raiseS` lets slides happen for free, and slides preserve
  rungs, so raiseS reachability of **rung tuples** depends only on the
  `tabToTab` fibre. The probe therefore works on the quotient
  *node = slide fibre, edge = a licensed raise from some state of the fibre*.
  A raise strictly increases one rung, so the quotient is acyclic and the
  per-fibre reachable-rung set is a memoised DFS. This is exactly the BFS of
  the brief (`for z in c_cargo_closure(u): c_step(z, ('tabToFound', c))` for
  `c ∈ c_can_raise_set(z)`), collapsed to rungs.
* **`ok(s,t)`** = `∃` reachable rung tuple `m` with `rungs(t) ≤ m`. Only the
  Pareto maxima of the reachable-rung set need to be compared, and target
  states are grouped by rung tuple; every one of the `|orbit|²` ordered pairs
  is still decided (multiplicities counted exactly).
* **Fork test.** `c_live(F)` is replaced by the union of the direct raise sets
  over `F`'s slide fibre (identical by definition of the cargo fibre); both
  orientations `x` and `twin(x)` are tested, as the brief requires. For **every
  forked component** one witness is re-checked against the real
  `Search_lib.c_live(F)`.
* **Generator.** The corrected descending bottom-first generator of
  `Temp/RungLe_probe.py` (`can_sit_on(c,b) := c.rank+1 = b.rank`), every seed
  filtered through `to_full` (only `WF` states survive); high-rung seeds from
  `Temp/RungLe_probe_hi.walk_hi`. Campaign orbit from `SatDiffer_sweep.s1`;
  the second known family `A` from `SatDiffer_vacuity_Report.md` is included
  too.

The graph is symmetric on `WF` states, so `c_component` (directed) is the
mutual orbit.

## 2. Coverage

5 196 WF components, 177 443 states, **177 908 157 ordered pairs**, 10 856
`S`-saturated states, 3 694 pull-bearing components (71 %), max component
3 984 states, max 689 fibres/component, largest raiseS rung set 87.

| family | components | states | ordered pairs | forked | ok-failures | bare |
|---|---:|---:|---:|---:|---:|---:|
| campaign orbit (`s1`) | 1 | 397 | 157 609 | 1 | 5 096 | 0 |
| second family (`A`) | 1 | 44 | 1 936 | 1 | 128 | 0 |
| random, rng 1 | 1 200 | 12 518 | 3 187 538 | 1 | 648 | 0 |
| random, rng 7 | 1 200 | 9 630 | 493 372 | 1 | 32 | 0 |
| random, rng 2026 | 600 | 4 924 | 311 592 | 1 | 128 | 0 |
| random, rng 31337 | 600 | 5 453 | 540 435 | 3 | 3 912 | 0 |
| random, rng 424242 | 600 | 5 380 | 1 693 218 | 1 | 12 800 | 0 |
| high-rung, rng 4242 | 398 | 44 453 | 32 153 823 | 1 | 1 152 | 0 |
| high-rung, rng 987654 | 398 | 54 735 | 59 288 203 | 5 | 86 496 | 0 |
| high-rung, rng 555 | 198 | 39 909 | 80 080 431 | 2 | 159 848 | 0 |
| **total** | **5 196** | **177 443** | **177 908 157** | **17** | **270 240** | **0** |

Six high-rung components exceeded the 6 000-state cap and were skipped; none
of the analysed components hit the cap.

## 3. Failures of `ok`

* **270 240** failing ordered pairs (0.152 %), spread over **17** components.
* **270 240 / 270 240 are in forked components.** `bare = 0`.
* All 17 forked components are among the 17 components that have at least two
  Pareto-maximal rung tuples, and all 17 of those have `ok`-failures. Thus,
  on this sample:

  > `ok` fails somewhere in the class  ⇔  the class has ≥ 2 Pareto-maximal
  > rung tuples  ⇔  the class is forked.

  (Every class in the other 5 179 components has a unique Pareto-maximal rung
  tuple and has no failure at all.)

### 3.1 The campaign orbit (`s1`, 397 states, the known incomparable twin maxima)

Failing pair — the source is the saturated maximal state `s1`, and `t` at
`(3,0,2,3)` is incomparable with `(5,0,4,2)` because of the club coordinate
alone (heart/spade are lower, club is higher).

```
s  rungs (5,0,4,2)  raiseS reach = {(5,0,4,2)}   (s is S-saturated)
   F<AH2H3H4H5H  AS2S3S4S AC2C> P{0:4D3C2D | 1:8D7S | 2:5D4C | 3:6H5C | 4:6C | 5:8S7D | 6:#}
t  rungs (3,0,2,3)
   F<AH2H3H  AS2S AC2C3C> P{0:4D | 1:8D7S | 2:5D4C | 3:6H5C4H3S2D | 4:6C5H4S | 5:8S7D | 6:#}
```

The component is forked (8 fork witness states). One:

```
rungs (3,0,2,2),  x = 3S, live = {3S,3C}, 3C not directly raisable at F
F<AH2H3H  AS2S AC2C> P{0:4D3C2D | 1:8D7S | 2:5D4C | 3:6H5C4H3S | 4:6C5H4S | 5:8S7D | 6:#}
```

This is the campaign's own `N6` fork of `SatDiffer_vacuity_Report.md`
(`ForkWitness N6 (♠3)`), reproduced exactly, and the orbit has the same 397
states / 2 saturated states / 8 forks.

### 3.2 The second family `A` (44 states)

Failing pair `(0,1,4,3)` vs `(0,1,3,4)` (both saturated, incomparable), 128
failing pairs; the component has 4 fork witnesses, e.g. at rungs `(0,1,3,3)`
with `live = {3S,3C}`:

```
s  rungs (0,1,4,3)
   F< AD AS2S3S4S AC2C3C> P{0:6S5H | 1:#6C5D4C3D | 2:6D5C4D | 3:# | 4:JCTH}
t  rungs (0,1,3,4)
   F< AD AS2S3S AC2C3C4C> P{0:6S5H4S3D | 1:#6C5D | 2:6D5C4D | 3:# | 4:JCTH}
```

### 3.3 A non-saturated failure (random-1, 176 states)

`ok` also fails from low states, not only from maximal ones:

```
s  rungs (0,0,0,3)
   F<   AC2C3C> P{0:8H7C6H5S4D | 1:3D | 2:4H3S2DAS | 3:7D6C5H4C3H2SAH | 4:# | 5:TH}
t  rungs (1,0,3,2)
   F<AH  AS2S3S AC2C> P{0:8H7C6H5S4D3C2D | 1:3D | 2:4H | 3:7D6C5H4C3H | 4:# | 5:TH}
```

No raiseS endpoint from `s` dominates `(1,0,3,2)`; the component is forked
(4 witnesses, e.g. rungs `(1,0,2,2)`, `live = {3S,3C}`).

### 3.4 A large high-rung failure (high-555, 1 168 states, 16 200 failing pairs)

```
s  rungs (3,3,2,6)   raiseS reach = {(3,3,2,6),(3,3,3,6),(3,3,4,6),
                                      (4,3,3,6),(4,3,4,6),(4,3,5,6)}
   F<AH2H3H AD2D3D AS2S AC2C3C4C5C6C> P{0:#JCTH9S8H7S6H | 1:7D6S5D4S | 2:7C6D5S4H3S | 3:#QD | 4:9H8C7H}
t  rungs (4,3,6,5)
   F<AH2H3H4H AD2D3D AS2S3S4S5S6S AC2C3C4C5C> P{0:#JCTH9S8H7S6H | 1:7D | 2:7C6D | 3:#QD | 4:9H8C7H6C5D}
```

The reach has 6 rung tuples and still misses `(4,3,6,5)` (club 5 > 6 fails);
fork witness at rungs `(4,3,5,5)`, `live = {6S,6C}`.

### 3.5 All 17 failure components

Every one is forked; none is bare. `maxima` are the Pareto-maximal rung
tuples of the component, `fails` the failing ordered pairs.

| family | states | maxima | forks | fails |
|---|---:|---|---:|---:|
| campaign | 397 | (5,0,2,5), (5,0,4,2) | 8 | 5 096 |
| second | 44 | (0,1,3,4), (0,1,4,3) | 4 | 128 |
| random-1 | 176 | (1,0,2,3), (1,0,3,2) | 4 | 648 |
| random-7 | 24 | (0,3,3,4), (0,3,4,3) | 8 | 32 |
| random-2026 | 44 | (0,1,3,4), (0,1,4,3) | 4 | 128 |
| random-31337 | 12 | (2,3,2,0), (3,2,2,0) | 4 | 8 |
| random-31337 | 16 | (0,0,2,3), (0,0,3,2) | 8 | 32 |
| random-31337 | 256 | (2,1,3,4), (2,1,4,3) | 8 | 3 872 |
| random-424242 | 1 256 | (4,1,3,5), (4,1,5,3) | 8 | 12 800 |
| high-4242 | 848 | (3,5,5,6), (3,5,6,5) | 4 | 1 152 |
| high-987654 | 56 | (3,3,5,6), (3,3,6,5) | 4 | 200 |
| high-987654 | 1 200 | (3,2,4,5), (3,2,5,4) | 24 | 83 232 |
| high-987654 | 176 | (3,2,5,6), (3,2,6,5) | 16 | 2 048 |
| high-987654 | 12 | (4,5,2,4), (5,4,2,4) | 4 | 8 |
| high-987654 | 786 | (3,6,5,6), (3,6,7,5) | 4 | 1 008 |
| high-555 | 1 168 | (4,3,5,6), (4,3,6,5) | 4 | 16 200 |
| high-555 | 3 600 | (5,6,4,2), (6,5,4,2) | 8 | 143 648 |

Every maximum pair is incomparable and differs (usually by exchanging ranks
between the two suits of one colour). No non-forked component anywhere in the
sample has ≥ 2 Pareto-maximal rung tuples.

## 4. Independent verification

`Temp/RaisesOrFork_verify_s2.py` re-derives the two load-bearing primitives
without the quotient:

1. **Literal raiseS BFS** — from a state `u`, take `c_cargo_closure(u)` and
   fire every `c_can_raise_set` raise, iterating. On the campaign (397
   states/130 fibres), the second family, six random components and three
   high-rung components (including the 1 168-state one), this reproduces the
   probe's rung set exactly at every sampled source.
2. **Exact fork test** — for every slide fibre of those components,
   `union of direct raise sets == c_live(rep)`; and every reported fork
   witness satisfies `c_live(F) == {x, twin(x)}` and
   `twin(x) ∉ c_can_raise_set(F)`. All pass.
3. **Failure re-check** — for the campaign, the second family and the
   1 168-state high-rung failure, the literal BFS finds **no** endpoint
   dominating `t`, confirming the failures are real rather than an artefact
   of the fibre quotient.

All checks passed (`ALL VERIFICATION CHECKS PASSED`).

## 5. Relation to `FullJoinAtLeastOrFork`

A raiseS play from `s` ends at `v` with `rungs v ≥ rungs s` automatically
(rises increment one rung, slides preserve all rungs). So whenever `ok` holds,
`w := v` satisfies

```
FullJoinAtLeast s t w := sameOrbit s w ∧ ∀ σ, max(rungAt s σ, rungAt t σ) ≤ rungAt w σ,
```

and when it fails the class is forked. Hence the tested claim is pointwise
**at least as strong** as `FullJoinAtLeastOrFork`, with **no residue**: on
all 177 908 157 ordered pairs of the sample it supplies the full-join witness
`w` explicitly (inside the raiseS-only fragment) or a fork in the same class.
The data never needed the fork disjunct outside the 17 `≥2`-maxima classes,
and inside them `w` genuinely does not exist.

## 6. Caveats

* Only **17** forked components were exercised (124 fork witness states); the
  fork disjunct is the thinly-covered side of the test. The implication
  "`ok` fails ⇒ forked" is, however, uniform across all of them, and its
  converse pattern is exact.
* Six components larger than 6 000 states were skipped, so the
  large-component regime is sampled (up to 3 984 states), not exhausted.
* The generator is random; this is empirical evidence, not proof. The clean
  pattern "multiple Pareto-maximal rung tuples ⇔ fork ⇔ an `ok` failure"
  deserves a proof attempt, but nothing here refutes the claim and nothing
  here needs a new residue hypothesis.
* No file under `Orig2/` was modified; no counterexample `.lean` card was
  written because no counterexample was found.

## 7. Blunt answer

**The claim survives — across 5 196 WF components, 177 443 states and
177 908 157 ordered pairs there are 270 240 failures of the raise-up test and
all of them occur in forked components (indeed exactly the 17 classes with
two incomparable rung maxima, which are exactly the 17 forked classes), so
there is not one counterexample and the claim is on this data strictly at
least as strong as `FullJoinAtLeastOrFork`, delivering its witness directly in
the raiseS-only fragment with no residue.**

## 8. Reproduce

```
cd lean-model
python Temp/RaisesOrFork_probe_s2.py 1200 400 6000 1800   # full sweep (~95 s)
python Temp/RaisesOrFork_verify_s2.py                       # independent checks
```

Files added (all under `Temp/`, nothing in `Orig2/` or existing `Temp/`
scripts modified):

* `Temp/RaisesOrFork_probe_s2.py` — the probe
* `Temp/RaisesOrFork_verify_s2.py` — literal-BFS / `c_live` cross-checks
* `Temp/RaisesOrFork_probe_s2.out` — raw output of the full sweep
* this report
