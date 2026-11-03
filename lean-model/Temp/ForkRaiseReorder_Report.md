# `Orig2/Fork/Class/ForkRaiseReorder.lean` — rewrite report

**Verdict:** the card now contains **no false statement**.  The three false
`def … : Prop` obligations (`RaiseAbove`, `SpecShift`, `RaiseSReorder`) are
gone; the two that were replaced by their true forward forms are labelled
*PROVED* with the exact `Temp` location, and the two remaining obligations
(`RankFront`, `CoverMustBeRaised`) are labelled **OPEN** — they are definitions,
not assertions, and no proof of them is claimed.

---

## 1. State before / after

| | before | after |
|---|---|---|
| lines | 147 | 360 |
| imported module | `Orig2.Fork.Class.ForkOneColourClosure` | unchanged |
| false `Prop` obligations | 3 (`RaiseAbove`, `SpecShift`, `RaiseSReorder`) | 0 |
| inline-proved theorems | 3 | 4 |
| `sorry` / `Classical` / `noncomputable` | none | none |
| axiom footprint | `[propext]`, `[propext, Quot.sound]` | same |

The file was verified to be the untouched original (147 lines) before writing.

---

## 2. Kept unchanged (statements)

`RaiseStepS`, `RaiseSSeq`, `suit_eq_or_twin_of_color`, `cover_seats`,
`nextUp_raise_ne` — statements and proofs byte-for-byte (only the `RaiseSSeq`
docstring gained the head-is-last-raise convention note; `nextUp_raise_ne`
gained a `#print axioms` line).

---

## 3. Inline-proved theorems (the only `theorem`s in the file)

| theorem | what it says | axioms |
|---|---|---|
| `suit_eq_or_twin_of_color` | same-colour suits are equal or twins | `[propext]` |
| `nextUp_raise_ne` | a raise of `c` does not move `d`'s `nextUp` bit when `d.suit ≠ c.suit` | `[propext]` |
| `cover_seats` | a card that can sit on `c.twin` has only the seats `c`, `c.twin` | `[propext, Quot.sound]` |
| `cover_seats_cases` | **new**: a card seated on `t` can only ever sit on `t` or `t.twin` (proved here from `cover_seats`; same row as `Temp`'s `seat_possibilities`) | `[propext, Quot.sound]` |

`#print axioms` output, verbatim:

```
'OneColourClosure.suit_eq_or_twin_of_color' depends on axioms: [propext]
'OneColourClosure.nextUp_raise_ne' depends on axioms: [propext]
'OneColourClosure.cover_seats' depends on axioms: [propext, Quot.sound]
'OneColourClosure.cover_seats_cases' depends on axioms: [propext, Quot.sound]
```

The only remaining compiler message is the pre-existing deprecation
`warning: 'if_neg' has been deprecated` at `nextUp_raise_ne` (line 119); it was
already there in the original file and is left untouched.

---

## 4. Obligations replaced

| old (false) | new | status | where it is checked |
|---|---|---|---|
| `RaiseAbove` — `CanRaise st d ↔ CanRaise w d` | **`RaiseAboveFwd`** — forward only | PROVED | `Temp/RaiseAbove_proof.lean:88` `canRaise_of_raise_above` |
| `SpecShift` — `CanRaiseS z d ↔ CanRaiseS z' d` | **`SpecShiftFwd`** — forward only | PROVED | `Temp/SpecShift_sem.lean:336` `specShift_sem_fwd` |
| `RaiseSReorder` — word `c :: ws.erase c` | **`RankFront`** — word `rankFrontWord c ws` | **OPEN** | none (census 107/107; licensed + distinct-rank case at `Temp/RankFront_proof.lean:130`) |

Notes recorded in the card:

* `SpecShiftFwd` needs **no** "no reveal / off-pile" hypothesis (the old
  docstring's claim is true only for the forward direction).
* `RaiseAboveFwd` is stated without the `d.suit ≠ c.suit` and
  `pileHolding d = some b` hypotheses that `canRaise_of_raise_above` carries;
  the docstring explains why both are supplied by the statement's own
  hypotheses (rank gap ⇒ suit gap; `CanRaise` ⇒ `pileHolding`, via
  `pileHolding_of_pileOfTop`, `Orig2/Fork/Split/ForkDrainInduction.lean:121`).

New helper definitions for `RankFront`: `insertByRank`, `sortByRank`,
`rankFrontWord` (the `Temp` sort, renamed so this card cannot shadow
`Temp/RankFront_proof.lean`'s `insRank`/`sortRank`/`rankFront`).

---

## 5. Obligations added

| name | content | status | where it is checked |
|---|---|---|---|
| `RankOrder` | a card above `y` in a well-formed face-up run has strictly lower rank | PROVED | `Temp/RankFront_final.lean:59` `above_rank_lt`, `:78` `above_rank_lt_of_pile` |
| `LicenceStep` | a raise of `d` preserves `c`'s licence when `d.rank ≠ c.rank` | PROVED | `Temp/RankFront_proof.lean:61` `canRaiseS_step_of_rank_ne` |
| `LicenceWord` | the same across a whole `RaiseSSeq` | PROVED | `Temp/RankFront_proof.lean:71` `canRaiseS_persist_of_rank_ne` |
| `CoverLock` | with `x` seated on `t` and `t.twin` founded, `t` is unraisable at every cargo mate | PROVED | `Temp/RankFront_final.lean:153` `step_none_of_twin_covered` (from `twin_covered_persists` `:127`, `no_canPlace_of_seated` `:98`, `seat_possibilities` `:86`) |
| `CoverMustBeRaised` | play level: every valid word raising `t` also raises its cover `x` | **OPEN** | none (`Temp/RankFront_final.lean:171`, stated only) |
| `RaiseSSeqL` | the licensed `raiseS` sequence (H1's carrier) | definition | — |

---

## 6. Counterexample register (exact locations in the card's docstrings)

All refutations below were kernel-checked against the *old* `def`s; the card
records the statement, the witness state and the refutation's home so the dead
end is not re-attacked.

| refutation | file:line | state shape recorded |
|---|---|---|
| `not_RaiseAbove` (`¬ (CanRaise st d ↔ CanRaise w d)`) | `Temp/SpecShift_proof.lean:455` | `zceB`: found `♠ A..6`, `♥ A..7`, `♦ = ♣ = []`; `p0 = ⟨[], [9♣, 8♥, 7♠]⟩`, `p1 = ⟨[8♦], [7♣]⟩`; raise `c = 7♠` exposes `d = 8♥` below it in the same pile (`c.rank.toIdx = 6 < 7 = d.rank.toIdx`) |
| `not_SpecShift` (`¬ (CanRaiseS z d ↔ CanRaiseS z' d)`) | `Temp/SpecShift_proof.lean:323` | `zce`: `p0 = ⟨[K♦], [K♠]⟩`, foundations height 12; raising `K♠` flips the hidden head `K♦` up, creating `d = K♦`'s licence |
| `not_SpecShift_reversible` (same, with a *reversible* raise) | `Temp/SpecShift_proof.lean:462` | `zceB` above |
| `not_specShift_with_suit` (`d.suit ≠ c.suit` does not repair the `↔`) | `Temp/SpecShift_proof.lean:331` | `zce` |
| `specShift_false` (same-shaped refutation, second witness) | `Temp/Reorder_proof.lean:286` | `probeState` `p0 = ⟨[], [10♦, 9♠, 8♥]⟩`, found `♠ A..8`, `♥ A..7` |
| `raiseSReorder_false` (unsorted word `c :: ws.erase c`) | `Temp/Reorder_proof.lean:318` | same `probeState` (`:74`); word `[9♠, 8♥]`, `c = 8♥` |
| `raiseSReorderFront_false` (unsorted play-front `ws.erase c ++ [c]`) | `Temp/Reorder_front_proof.lean:308` | `probeState` (`:67`) `p0 = ⟨[], [K♥]⟩`, `p1 = ⟨[], [K♦, Q♠]⟩`, found `♠ A..J`, `♥ A..Q`, `♦ A..Q`; word `[K♥, Q♠, K♦]`, `c = K♥` |

The docstrings also record *why* each `↔` fails (licence creation by reveal /
uncovering; and the cover-lock obstruction for the front move), and the two
named residuals:

* **H1** — `RaiseSSeq.cons` carries only `State.step`; a bridge to `CanRaise`
  is impossible (`t4a_fires` + `t4a_not_canRaise`,
  `Temp/RankFront_proof.lean:175,165`), so plays carry their licences
  (`RaiseSSeqL`) or start fully licensed.
* **H2** — replay across shifted prefixes; reduced to
  `canRaiseS_unraise_of_rank_lt` (under test, one slide-based failure mode
  known). Nothing in the card depends on it.

---

## 7. Verification performed

```
cd lean-model
lake env lean Orig2/Fork/Class/ForkRaiseReorder.lean      # clean (one pre-existing deprecation warning)
lake env lean Temp/SpecShift_sem.lean                     # still checks; specShift_sem_fwd : [propext, Quot.sound]
lake env lean Temp/RaiseAbove_proof.lean                  # still checks; canRaise_of_raise_above : [propext, Quot.sound]
```

Both cited proof modules import the card and **still elaborate unchanged**, so
the two forward proofs remain machine-checked against the rewritten card.

---

## 8. Caveats on the `Temp` import graph

Four `Temp` files import this card (contrary to the task note that nothing
does): `Temp/SpecShift_sem.lean`, `Temp/RaiseAbove_proof.lean`,
`Temp/SpecShift_proof.lean`, `Temp/Reorder_proof.lean` (and the `RankFront_*`
chain transitively through `Temp/Reorder_front_proof.lean` →
`Temp/SpecShift_sem.lean`).

* `Temp/SpecShift_sem.lean` and `Temp/RaiseAbove_proof.lean` still compile
  (verified above) — they only use the kept vocabulary.
* `Temp/Reorder_front_proof.lean` does not mention any removed identifier, so
  its refutation of `ws.erase c ++ [c]` stays valid.
* `Temp/SpecShift_proof.lean` and `Temp/Reorder_proof.lean` still contain the
  refutations but refer to the removed `def`s (`SpecShift`, `RaiseAbove`,
  `RaiseSReorder`); they will not elaborate until those three local statements
  are re-declared in the `Temp` file (the witnesses and refutations themselves
  replay unchanged).  Per the task, no `Temp` file except this report was
  touched.
* `Temp/RankFront_final.lean` declares `CoverMustBeRaised` itself; since the
  card now declares the identical statement in the same namespace, that one
  line must be deleted from the `Temp` file if the `RankFront` chain is
  rebuilt. All other `Temp` helper names (`sortRank`, `rankFront`, `insRank`,
  `seat_possibilities`, `above_rank_lt`, …) were deliberately **not** reused
  here (`sortByRank`, `rankFrontWord`, `cover_seats_cases` instead), so no
  other duplicate declarations are introduced.

---

## 9. Map of the new card

```
§1  RaiseStepS, RaiseSSeq (kept), RaiseSSeqL (new, H1's carrier)
§2  suit_eq_or_twin_of_color, nextUp_raise_ne            (proved, kept)
§3  cover_seats (kept), cover_seats_cases                (proved; second is new)
§4  RankOrder                                            (PROVED in Temp)
§5  LicenceStep, LicenceWord                             (PROVED in Temp)
§6  CoverLock (PROVED in Temp), CoverMustBeRaised (OPEN)
§7  SpecShiftFwd, RaiseAboveFwd                          (PROVED in Temp; replace the false ↔ forms)
§8  insertByRank, sortByRank, rankFrontWord, RankFront   (OPEN; replaces RaiseSReorder)
```
