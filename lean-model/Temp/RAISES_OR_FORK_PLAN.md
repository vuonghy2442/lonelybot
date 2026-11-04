# The raises-or-fork plan (detailed working document)

> **SOLVED (2026-11-04).** The plan closed via the commutation route (not
> `TailReplay`): see `Orig2/Fork/Commute/PullCommute.lean`,
> `OneColourClosure.raises_or_fork` and
> `OneColourClosure.fullJoinAtLeastOrFork_proved`.  The historical notes below
> are kept for context.

Status: **the path induction is complete; one arm remains — the twin arm of the pull case.**
Last updated after the `RaisesOrForkMain` round.

---

## 1. What is being proved

**Target (the route's end point):**

```lean
theorem raises_or_fork {s t : State} (hs : s.WF) (h : sameOrbitSetoid.r s t) :
    (∃ ws v, RaiseSSeqLicensed s ws v ∧ RungLe s v ∧ RungLe t v) ∨ Fork s
```

In words: *from `s`, using raises only (each raise allowed to be preceded by slides),
you can reach rungs dominating both `s` and `t` — or the orbit class of `s` contains a fork.*

**Downstream (already proved):**

```lean
fullJoinAtLeastOrFork_of_raises_or_fork   -- raises_or_fork ⇒ FullJoinAtLeastOrFork
fullJoinAtLeastOrFork_of_hPull            -- same, with the induction's own pull hypothesis
```

with `w := v` (the endpoint is itself the join witness). **No residue** (`SatDifferForkWF`,
`ArmDichotomy`, `ForklessHasTop`, …) is used.

**Why it matters:** `FullJoinAtLeastOrFork` is the campaign's join target; this route avoids
the `BottomDip` / `SatDifferForkWF` reduction entirely.

---

## 2. Conventions (get these wrong and everything else is wrong)

| symbol | meaning |
|---|---|
| `RaiseStepS z z' c` | `∃ z₀, CargoPath z z₀ ∧ State.step z₀ (tabToFound c) = some z'` — slide-star, then **one** raise |
| `RaiseSSeqLicensed s ws z` | licensed sequence; **the head of `ws` is the LAST raise** (reverse play order) |
| `playWord L` | the word whose *chronology* is `L` (so `playWord (c :: ws)` = "raise `c` first, then `ws`") |
| `RungLe v w` | `∀ σ, rungAt v σ ≤ rungAt w σ` (`Orig2/Fork/Class/ForkOneColourClosure.lean:288`) |
| `rungAt st σ` | foundation height of suit `σ` |
| `SSaturated st` | `∀ c, ¬ CanRaiseS st c` |
| `Fork u` | `∃ F x, sameOrbitSetoid.r u F ∧ ForkWitness F x` |
| `ForkWitness F x` | **spectrum equality**: `(∀ c, (c = x ∨ c = x.twin) ↔ CanRaiseS F c) ∧ ¬ CanRaise F x.twin` |

Two ordering facts used constantly:

* word head = last raise (so appending at the end of a *play* = consing onto the *word*);
* `raiseS` letters only ever increase one rung, by exactly one.

---

## 3. The induction skeleton (proved)

`raises_or_fork_play` (`Temp/RaisesOrForkMain.lean`): induction on a reversible play
`ShufflePlayW s play t`, with the case split on its first move.

| first move | treatment | status |
|---|---|---|
| (empty play) | `v := s` | ✅ |
| `tabToFound c` | `u ≥ s` (`RungMono.rungAt_raiseStepS`); IH on the suffix; prepend the letter | ✅ |
| `tabToTab` (slide) | rungs unchanged; `replay_of_orbit_rung` moves the suffix's play to the new start | ✅ |
| `draw` | same replay; `nextUp`/`freeCardS` do not read stock/waste | ✅ |
| `foundToTab c b` (pull) | **the pull case** — see §4 | 🔶 one arm open |
| `wasteToFound` / `wasteToTab` | impossible in an orbit play (`*_not_reversibleAtW`) | ✅ |
| `Fork` lift | `fork_of_sameOrbit` | ✅ |

The pull case is factored as a single hypothesis so the induction is already written:

```lean
hPull : ∀ {s u t v : State} {c : Card} {b : Base} {ws : List Card},
    s.WF →
    State.step s (Move.foundToTab c b) = some u →
    RaiseSSeqLicensed u ws v →
    RungLe t v →
    (∃ v', RaiseSSeqLicensed s (playWord (sortByRank ws)) v' ∧ RungLe s v' ∧ RungLe t v')
    ∨ Fork s
```

**Note:** there is **no** hypothesis `RungLe v u` — a licensed play only climbs, so the
induction recovers it. Anything that assumes `RungLe v u` externally is over-specified.

---

## 4. The pull case (the whole difficulty)

Setting: the path starts `s --pull c from base b--> u`, then a licensed play `ρ` with word
`ws` reaches `v`, and `RungLe t v`.

### 4.1 The deficit

* the pull lowers **only** `c`'s suit, by exactly one: `u = s − e_c`;
* hence `v ≥ u` gives `v ≥ s` in every suit except possibly `c`'s;
* `rungAt_eq_of_no_letter`: if no letter of `ws` has `c`'s suit, then `rungAt v c.suit =
  rungAt u c.suit`, i.e. **`ws` raises nothing of `c`'s suit**;
* so the only shortfall possible is `rungAt v c.suit = rungAt s c.suit − 1`, and then
  `ws` contains no letter of `c`'s suit at all.

If the shortfall does **not** occur, the IH's play already works and the case is trivial
(`replay_of_orbit_rung` / rung bookkeeping).

### 4.2 Sort and reorder

`sortable` / `tieFree` / `raiseS_rankfront_L` (all in
`Orig2/Fork/Class/ForkRaiseReorderProof.lean`) give: a licensed play ⇒ a *rank-sorted*
licensed play with the same multiset of letters. **Sortedness cannot be dropped**:
permutations of a licensed play are not always licensed (covers must precede).

### 4.3 (I) — larger-rank inertness

```lean
canRaiseS_inert_of_canRaiseStep :
  RaiseStepS z z' d → d.rank > x.rank → (CanRaiseS z x ↔ CanRaiseS z' x)
```

Both directions, **scoped to strictly larger ranks** (this is the correct form of "raisable
at one point of such a segment ⇒ raisable at all of them"). For *different* ranks in the
other direction use R1: `canRaiseS_step_of_rank_ne` (forward only). For *equal* ranks the
only dangerous card is the twin: `licence_lost_only_by_twin`.

Consequence used everywhere: the strictly-higher-rank tail can be ignored, and a lower-rank
letter can be inserted at its rank boundary.

### 4.4 The plan's four arms

1. **`c.twin ∉ ws`** ⇒ `c` stays S-live all the way (`block_end_licensed`), so we may
   append `raise c` at the end of the play; then hoist it to the front
   (`raiseS_rankfront_L`) and cancel the pull (`cancel_prefix_is_play_from_source`).
   *Proved: `pull_case_noTwin` (unconditional).*
2. **`c.twin ∈ ws`, `c` still live at `v`** ⇒ same append/hoist/cancel
   (`pull_case_of_end_live`, `pull_case_mem`). *Proved.*
3. **`c` dead, cover raisable** ⇒ raise the cover first (its rank is `c.rank − 1`, so it
   belongs strictly before the tie block; insert by (I)+R1), reviving `c`; then arm 2.
   *Machinery proved (`insert_at_block_end`), composition open.*
4. **`c` dead, cover not raisable, no fork** ⇒ **the open case.** The plan's answer was
   "fork", but that is **false** on the acceptance board (§6.1). The working resolution is
   the **replay**: run the same word `ws` from `s` (where `c` is founded, so the twin-clause
   problem does not exist).

### 4.5 Why the replay is the right resolution in arm 4

Per letter, `CanRaiseS` is a **local read**:

```lean
canRaiseS_split : CanRaiseS st c ↔ st.nextUp c ∧ freeCardS st c
freeCardS st c  reads:  c's pile (run, below, hidden)  and  pileOfTop c.twin
```

At the `s`-side vs the `u`-side:

| read | difference |
|---|---|
| `nextUp d` for `d.suit ≠ c.suit` | identical (only `c`'s suit moved) |
| `d`'s pile | identical, or *shorter run* at the `s`-side (the pulled card is founded there) ⇒ easier |
| `pileOfTop d.twin` | identical **unless `d = c.twin`** |

So the only letter needing care is `c.twin`'s. Its read is `pileOfTop c`, which is `none` at
the `s`-side (the card is founded). Therefore: at the `s`-side, `c.twin` must be **a pile
top** (or become one). By `cover_seats`, its cover has only the seats `c` and `c.twin`; `c`
is founded, so the cover cannot be slid — it must be raised, which is a *rank
`c.rank − 1`* insertion. If `c.twin` is already a pile top at `s`, the replay goes through
directly.

**Rung bookkeeping for the replay:** the same word from `s` founds the same cards, and `s` is
one rung higher in `c`'s suit than `u`, so the endpoint is `v + e_c` — which dominates both
`s` and `t`.

---

## 5. Lemma inventory (proved — do not reprove)

All `[propext]` or `[propext, Quot.sound]`; all files compile with `lake env lean`; no
`sorry` / `Classical` / `noncomputable`.

### Rung arithmetic — `Temp/RungMono.lean` (namespace `RungMono`)
* `rungAt_raiseStepS` — one letter: `+1` on `c.suit`, others fixed.
* `rungAt_eq_of_no_letter` — a word with no letter of `σ` leaves `σ`'s rung fixed.
* `rungAt_add_count` — `rungAt z σ = rungAt s σ + #{letters of σ}` (the exact ledger).
* `rungAt_le` — unconditional monotonicity.
* `rungAt_le_of_raiseSSeqLicensed` — guarded, `≤` in the reverse direction (naming trap).
* Originals to cite when convenient: `rungAt_cargoPath` (`ForkCriticalPair.lean:97`),
  `rungAt_tabToFound` (`Position.lean:166`), `RaiseSSeqLicensed.rungAt_eq`
  (`ForkRaiseReorderProof.lean:73`).

### The pull — `Temp/PullRaiseId.lean` (root namespace)
* `pull_raise_id (s.WF) … : s' = s` — pull then raise is the identity. **`s.WF` is
  necessary**: without it, duplicated copies of `c` on two piles break it.
* `pull_raise_id_rung`, `pull_raise_id_components`.
* `not_canRaise_after_pull_short` — a non-repayable pull leaves the suit one short.

### Obstruction classification — `Temp/Obstruction.lean` (root namespace)
* `not_canRaiseS_cases` — a non-S-live card is: `nextUp = false` **or** `pileHolding = none`
  **or** buried with no twin top **or** commit-locked
  (`below = [] ∧ (hidden ≠ [] ∨ ¬ king)`).
* `covered_of_not_canRaiseS` — buried ⇒ a cover exists.
* `canRaiseS_of_nextUp_of_freeCardS` — the converse (`canRaiseS_split.mpr`).

### Commit lock — `Temp/FrozenSuit.lean` (namespace `FrozenSuit`)
* `lock_step` / `lock_play` — the invariant "`w` is the head of its face-up run, the deck
  beneath is non-empty, `w` is not founded" is closed under every reversible letter.
* `commitLocked_rung_le` — hence `rungAt z w.suit ≤ rungAt s w.suit` for every orbit mate.
* `commitLocked_rung_le_of_not_king` — `hidden ≠ []` can be dropped for non-kings.

### The dichotomy and the fork producers — `Temp/RaisesOrFork.lean` (namespace `OneColourClosure`)
* `obstruction_at_deficit`, `covered_at_of_buried`, `frozen_of_deficit_lock`,
  **`obstruction_dichotomy`**: at a deficit point the four-way obstruction collapses to
  **cover ∨ lock**.
* `exists_append_raise`, `exists_append_raise_of_word_notMem`.
* `twin_raise_square_both` — both twins vanilla ⇒ both orders.
* `fork_of_spectrum`, `fork_of_collapsed_spectrum`.
* `raisesOrFork_of_rungLe_rev`, `raisesOrFork_of_rungEq` — restricted forms.
* `fullJoinAtLeastOrFork_of_raises_or_fork`.

### Block housing and cancellation — `Temp/BlockHousing.lean` (namespace `OneColourClosure`)
* `insert_at_block_end`, `_split`, `_sorted` — insert `raise c` at the upper boundary of its
  rank block (requires the word sorted).
* `suffix_transport`, `suffix_insert` — a strictly-higher-rank tail is inert for `c`.
* **`cancel_prefix_is_play_from_source`** — from a play whose chronology starts with
  `raise c`, the tail is a play from the pull's source. No transport lemma needed.

### Spectrum collapse — `Temp/SpectrumCollapse.lean` (namespace `SpectrumCollapse`)
* `spectrum_pair_by_draining`, `drain_pair_stays_live`, `drain_aux` (termination on
  `52 − Drain.rungSum`).
* `spectrum_pair_trichotomy`:
  `ForkWitness z' x ∨ ForkWitness z' x.twin ∨ (both twins vanilla)` — the corrected,
  exhaustive form (the "flipped fork" arm was missing from the first attempt).
* `spectrum_pair_fork_or_both`, `_square`.

### Licence at the block end — `Temp/PullReplay.lean` (namespace `OneColourClosure`)
* `block_end_licensed` — with `c.twin ∉ low`: `c` survives the block.
* `block_end_dead_dichotomy`, `block_end_licensed_or_dichotomy` — at the block end `c` is
  live, or covered, or commit-locked.
* `pull_case_of_end_live` — append → hoist → cancel; endpoint `v + e_c`.
* `pull_case_sorted`, `pull_case_sorted_rungLe`.

### The induction — `Temp/RaisesOrForkMain.lean` (namespace `OneColourClosure`)
* `sameOrbit_of_revStep(')`, `fork_of_sameOrbit`, `rungLe_of_rung_eq`.
* `replay_of_orbit_rung` — same word from an equal-rung orbit mate (the slide/draw cases).
* `pull_case_of_end_live`, `pull_case_mem`, `pull_case_noTwin`.
* `countP_erase_add`.
* `raises_or_fork_play (hPull)`, `raises_or_fork_of (hPull) (hspectrum)`,
  `fullJoinAtLeastOrFork_of_hPull (hPull) (hspectrum)`.

---

## 6. Refutations (do not re-attack these)

### 6.1 `block_end_licensed` without `c.twin ∉ ws` is FALSE
`PullReplayCounter.block_end_licensed_twin_refuted`:

```
♥ = A..4, ♦ = A..4 founded;  p0 = [6♣, 5♥, 4♠],  p1 = [6♠, 5♦];  c = 5♥,  low = [5♦]
```

`5♥` is alive at `u` only because `5♦` (its twin) tops `p1`. Raising `5♦` kills it while
`4♠` keeps it buried — and `4♠` is not raisable. **All three plan arms fail** on this board:
no append (dead), no cover insertion (`4♠` not raisable), no fork (the pair is not both
live). The only resolution is the replay from `s`, where `5♦` *is* a pile top. **This board
is the acceptance test for the twin arm.**

### 6.2 Related refutations from the earlier lane (context)
* `raiseSReorder_false`, `raiseSReorderFront_false` — the *unsorted* front is false; rank
  ordering is what makes the sorted form true.
* `not_SpecShift`, `not_SpecShift_reversible`, `not_RaiseAbove` — the `↔` forms of licence
  shift are false; only the forward direction holds.
* `unraise_probe_refutes` — higher-rank inertness fails for *unlicensed* (commit) steps.
* `SortedPrefixLicence` without `x ∉ R` is false.

---

## 7. The residual, precisely

Everything reduces to the **twin arm**:

> `c.twin ∈ ws`, `c` is dead at the block end, its cover is not raisable, and no fork is
> available at that state.

Proposed resolution (two small pieces, each testable on §6.1):

1. **`replay_of_no_twin`** — if `c.twin ∉ ws`, replaying `ws` at `s` is immediate: no letter
   reads `c`'s position, so `nextUp` and `freeCardS` are *identical*, rung excepted.
2. **The twin letter** — with `c.twin ∈ ws`, either
   * drop that letter (endpoint loses one rung in the twin's suit; if `t` doesn't need it,
     apply (1)), or
   * `c.twin` is a pile top at the `s`-side ⇒ the replay is legal after all, or
   * `c.twin` is covered: raise the cover — rank `c.rank − 1`, insertable by (I)+R1 — or, if
     that fails, report the exact obstruction (this is the only place a `Fork` arm could be
     needed, and the campaign's fork producers are ready).

---

## 8. Build & verify

```
cd lean-model
lake env lean -o .lake/build/lib/lean/Temp/RaisesOrFork.olean Temp/RaisesOrFork.lean
lake env lean -o .lake/build/lib/lean/Temp/PullRaiseId.olean Temp/PullRaiseId.lean
… (RungMono, Obstruction, FrozenSuit, BlockHousing, SpectrumCollapse, PullReplay, RaisesOrForkMain)
lake env lean Temp/RaisesOrForkMain.lean
```

Every theorem must print `[propext]` or `[propext, Quot.sound]`; no `sorry`, no
`Classical.choice`, no `noncomputable`.

## 9. Open risks, honestly

1. **The twin letter at the `s`-side may be dead too** (cover unreachable). Then the replay
   fails and nothing in the current inventory yields the fork — this is where the plan could
   be *false* rather than merely unfinished. The 34.1M-pair probe (and one exhaustive family,
   29.8M pairs) found no such case.
2. **Interface churn.** The pull case has changed shape three times (append → hoist/cancel →
   dichotomy → replay). Any new statement must be checked against §5 before being adopted.
3. **Do not re-introduce** `BottomDip`, `BottomAsymmetry` (as a target), or a transport
   lemma for `ρ`: all three were either strictly harder than the goal or avoidable.
