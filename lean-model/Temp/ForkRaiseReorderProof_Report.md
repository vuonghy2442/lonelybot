# Port report — the rank-front theorem into `Orig2`

**Deliverables**

| file | lines |
|---|---|
| `Orig2/Fork/Class/ForkRaiseReorderKit.lean` | 1040 |
| `Orig2/Fork/Class/ForkRaiseReorderProof.lean` | 1631 |
| this report | — |

Both files compile clean:

```
lake env lean Orig2/Fork/Class/ForkRaiseReorderKit.lean    → exit 0
lake env lean Orig2/Fork/Class/ForkRaiseReorderProof.lean   → exit 0
lake build Orig2.Fork.Class.ForkRaiseReorderKit \
           Orig2.Fork.Class.ForkRaiseReorderProof           → Build completed successfully
```

No `sorry`, no `Classical`, no `noncomputable` (the only occurrences of those
words are in the house-rules docstrings).  Nothing outside the two new files was
edited (`git status` shows exactly those two untracked files under `Orig2/`).

Both files import **only `Orig2.*`**:

* Kit: `Orig2.Fork.Class.ForkRaiseReorder`, `Orig2.Fiber.FreeOrbit`,
  `Orig2.Fiber.LockRung`, `Orig2.Fork.Local.ForkCriticalPair`.
* Proof: `Orig2.Fork.Class.ForkRaiseReorderKit` alone.

No `Temp.*`, no `Orig.*`, no `Archive.*` import appears.

---

## 1. Does `rankFront_holds : RankFront` close?

**Yes.**  The statement is the card's own `def RankFront` used verbatim:

```lean
theorem rankFront_holds : RankFront := by
  intro s c hs hc ws z hplay hmem
  exact raiseS_rankfront_L hs hc hplay hmem
```

and it is the last theorem of `ForkRaiseReorderProof.lean`.  There is **no**
word/play bridge to prove: the card's `rankFrontWord c ws` is
`(sortByRank (ws.erase c)).reverse ++ [c]`, literally the `Temp` `rankFront`
with `sortRank` renamed to the card's `sortByRank`, and the card's
`RaiseSSeqLicensed` uses the same "head = last raise" convention as `Temp`'s
`RaiseSSeqL`.  The final step of `raiseS_rankfront_L` is still the explicit
`playWord`/`append` rewrite
`playWord (sortByRank (ws.erase c)) ++ [c] = rankFrontWord c ws`, proved by
`simp [rankFrontWord, playWord]`.

`tail_exists` and `raiseS_rankfront_L` are exposed under exactly those names, at
the card's vocabulary (`RaiseSSeqLicensed`, `sortByRank`, `rankFrontWord`).

## 2. Axioms

Every theorem in both files was `#print axioms`-ed; the complete battery is at
the foot of each file.  All rows are `[propext]` or `[propext, Quot.sound]` — no
`sorryAx`, no `Classical.choice`.  The six requested lines, verbatim:

```
'OneColourClosure.rankFront_holds' depends on axioms: [propext, Quot.sound]
'OneColourClosure.tail_exists' depends on axioms: [propext, Quot.sound]
'OneColourClosure.raiseS_rankfront_L' depends on axioms: [propext, Quot.sound]
'OneColourClosure.canRaiseS_of_raise_perm' depends on axioms: [propext, Quot.sound]
'OneColourClosure.cover_must_be_raised' depends on axioms: [propext, Quot.sound]
'OneColourClosure.tie_swap' depends on axioms: [propext, Quot.sound]
```

## 3. Naming reconciliation (the mechanical part)

| `Temp` name | ported as |
|---|---|
| `RaiseSSeqL` (inductive, `Temp/RankFront_licensed.lean`) | **deleted**; the card's `RaiseSSeqLicensed` is used throughout |
| `RaiseSSeqL.toSeq / .wf / .append / .canRaiseS_head / .cargoPath / .step_s` | `RaiseSSeqLicensed.*` (same names) |
| `rankFront c ws` / `sortRank` / `insRank` | `rankFrontWord c ws` / `sortByRank` / `insertByRank` (the card's defs; `Temp`'s `insRank`/`sortRank` bodies are identical, so the helper lemmas `mem_insertByRank`, `insertByRank_perm`, `insertByRank_asc`, `sortByRank_perm`, `sortByRank_asc` are proved about the card's defs) |
| `RankFrontClaim` | the card's `RankFront` (never restated) |
| `playWord` (chronological-play notation) | kept (no card equivalent) |

One deliberate rename where the card already owns the name with a different
meaning: `Temp`'s `canRaiseS_cargoPath_iff` (cargo invariance of the S-licence
along a path) is ported as **`canRaiseS_cargoPath_bicond`**, because
`Orig2.Substrate.CargoRaise.canRaiseS_cargoPath_iff` is the *definitional*
bridge `CanRaiseS st c ↔ ∃ z, CargoPath st z ∧ CanRaise z c`.

`Temp`'s `step_s` (which extracts the *vanilla* licence at the slide's end) is
kept as `RaiseSSeqLicensed.step_s`, but at the card's carrier it needs `s.WF`;
the WF-free destructor that returns the `CanRaiseS` field is added beside it as
`RaiseSSeqLicensed.step_s'`.  The bridge that makes `step_s` possible is the new
lemma `canRaise_of_canRaiseS_of_step`: along a cargo path the seat/hatch
disjunct is invariant, so a **fired** raise at the path's end is vanilla-licensed
there.

## 4. Rule changes applied

* **No new `Prop` predicates.**  No `LicenceStep`, `LicenceWord`, `CoverLock`,
  `RankOrder`, `CoverMustBeRaised`, `SortedPrefixLicence`,
  `SortedPrefixLicenceFixed`, `TailExists`, `CommitMove` or `CommitRaise` was
  introduced.  In particular:
  * `TailExists` is gone — `tail_exists` is a plain theorem with its hypotheses
    inline;
  * `CoverMustBeRaised` is gone — `cover_must_be_raised : CoverMustBeRaisedWord`
    proves the card's own `def`;
  * `Asc P` (the `Temp` ascending wrapper) is gone — every statement spells out
    `P.Pairwise (fun a b => a.rank.toIdx ≤ b.rank.toIdx)`;
  * the one new *computable* definition is `playWord : List Card → List Card`
    (`P.reverse`), a function, not a `Prop` wrapper.

* **The six new card lemmas were reused, not reproved.**
  `canRaise_reversibleAtW` is cited directly (so `Temp`'s
  `canRaise_tabToFoundR`/`canRaise_reversibleAtW` pair is dropped — the card's
  `tabToFoundR_iff_canRaise` subsumes both);
  `canRaiseS_iff_cargoPath_reversibleAtW`, `canRaise_of_reversibleAtW` and
  `not_canRaise_of_not_reversibleAtW` are available but not needed by this lane.

* **`resequence_of_shuffle` was not attempted.**  The decision is the one the
  brief permits ("skip if it fights the API").  Two concrete blockers:
  1. the given signature has no `s.WF`, but converting a
     `ShufflePlayW` letter `reversibleAtW z (tabToFound c)` into `CanRaise z c`
     at the carrier grade needs `canRaise_of_reversibleAtW` (which takes `z.WF`),
     and `ShufflePlayW` does not carry well-formedness;
  2. the induced word is reverse-chronological (the card's convention: the head
     of `ws` is the *last* raise) while a `List Move` walk is chronological, so
     the conversion needs a "split off the last maximal cargo run" induction —
     strictly more than the ~150-line budget, and it would restate the same
     content as `raiseS_rankfront_L` in a second vocabulary.

  The card-word theorem `rankFront_holds : RankFront` is the deliverable and is
  complete.

## 5. What was ported (by `Temp` §)

**Kit** (`ForkRaiseReorderKit.lean`)

* `SpecShift_sem` §1–§5 in full: `mem_chop_of_mem_chop`,
  `mem_chop_of_mem_of_ne_last`, `below_chop_of_mem_of_ne_last`,
  `mem_afterRunRemoved_faceUp_of_mem_of_ne_last`,
  `mem_and_below_of_mem_afterRunRemoved`, `piles_tabToFound`,
  `found_tabToFound`, `mem_piles_tabToFound_of_mem_of_ne`,
  `not_mem_piles_tabToFound_self`, `parented_tabToFound_of_ne`,
  `bare_tabToFound_of_ne`, `parented_of_tabToFound`,
  `freeCardS_mono_of_ne_twin`, `revEqW_of_cargoPath`,
  `sameOrbit_of_cargoPath`, `nextUp_cargoPath`, `specShift_sem_fwd`.
* `RankFront_final` §1–§2: `above_rank_lt`, `above_rank_lt_of_pile`,
  `no_canPlace_of_seated`, `twin_covered_persists`,
  `step_none_of_twin_covered` (plus `cover_rank_lt`, `cover_rank_ne` from
  `RankFront_proof` §3).
* `RankFront_proof` §2: `raiseStepS_wf`, `canRaiseS_step_of_rank_ne`,
  `canRaiseS_persist_of_rank_ne`.
* `Reorder_front_proof` §4/§8: `found_cargoLeg`, `found_cargoPath`,
  `parented_of_cargoPath`, `raiseStepS_of_canRaiseS`, `raiseSSeq_snoc`,
  `raiseSSeq_append`, `raiseSSeq_wf`, `exists_append_cons_of_mem`,
  `erase_append_cons_of_not_mem`.
* `RankFront_licensed` §1–§2 and §4: `RaiseSSeqLicensed` accessors/adequacy,
  `canRaiseS_step_of_rank_ne_L`,
  `RaiseSSeqLicensed.canRaiseS_persist_of_rank_ne`, `swap_of_licensed`;
  R3 play level in full: `seatOf_tabToFound_of_seated_ne`,
  `seatOf_cargoLeg_of_seated`, `seatOf_cargoPath_of_seated`,
  `seat_invariant_of_not_mem`, `cover_must_be_raised`,
  `cover_must_be_raised_L`.
* New bridging lemma: `canRaise_of_canRaiseS_of_step` (+
  `canRaiseS_cargoPath_bicond`, `chop_ne_nil_of_two_le`,
  `afterRunRemoved_faceUp_bare`).

**Proof** (`ForkRaiseReorderProof.lean`)

* `RankFront_close` §0–§7: `playWord` kit, `cargoLeg_rungAt`,
  `cargoPath_rungAt`, `RaiseSSeqLicensed.rungAt_eq`, `rungAt_eq_of_perm`,
  `RaiseSSeqLicensed.revEqW`, `revEqW_of_raise_plays`,
  `canRaiseS_of_raise_perm`, `canRaiseS_of_raise_perm'`, `perm_reverse`,
  `perm_two_reverse_aux`, `perm_erase`, `RaiseSSeqLicensed.split_head`,
  `split_chron`, `tail_transport`, `swap_inversion`;
  §9: `insertByRank_push`, `sortable`, `raiseS_sorted_of_licensed`.
* `RankFront_licensed` §3: `rank_lt_of_mem_of_lastOf`,
  `not_mem_pileOfTop_of_rank_lt`, `not_mem_pileOfTop_twin_of_rank_lt`,
  `pileHolding_eq_of_agree`, `pileOfTop_eq_of_agree`,
  `nextUp_tabToFound_eq_of_low_rank`, `freeCardS_tabToFound_eq_of_low_rank`,
  `canRaiseS_inert_tabToFound_of_low_rank`, `canRaiseS_inert_of_canRaiseStep`,
  `canRaiseS_unraise_word`.
* `RankFront_tail` §1–§8 in full: `chop_append_singleton` (Orig2),
  `below_append_singleton_of_not_mem`,
  `fromCard_append_singleton_of_not_mem`, `fromCard_singleton_decomp`,
  `card_twin_ne_self`, `suit_ne_of_twin`, `not_mem_pileOfTop_of_rank_eq`,
  `not_mem_pileOfTop_twin_of_rank_eq`, `freeCardS_unpack`, `freeCardS_of_data`,
  `freeCardS_tabToFound_eq_of_rank_eq_notTwin`,
  `canRaiseS_tabToFound_iff_of_rank_eq_notTwin`,
  `fromCard_nil_of_freeCardS_of_twin_none`,
  `freeCardS_tabToFound_bwd_of_twin`, `canRaiseS_tabToFound_bwd_of_twin`,
  `freeCardS_tabToFound_fwd_of_twin`, `canRaiseS_rankEq_notTwin_step_iff`,
  `canRaiseS_rankEq_twin_step_bwd`, `canRaise_of_canRaiseS_of_exposed`,
  `twinStep_piles`, `exposed_bwd_of_twin_step`, `canRaise_of_raise_sameRank`,
  `tie_swap`, `asc_swap`, `bubble_tie`, `bubble_front`, the ascending-list kit
  (`asc_head_le_all`, `asc_le_of_mem_append`, `asc_append_left`, `asc_erase`,
  `asc_erase_append`), `tieFree_aux`, `tieFree`, `tail_exists`,
  `raiseS_rankfront_L`, `rankFront_holds`.

## 6. What was dropped, and what replaces it

Dropped **because an `Orig2` row already covers it** (not reproved):

| `Temp` row | `Orig2` replacement |
|---|---|
| `canRaise_tabToFoundR`, `canRaise_reversibleAtW` (`RankFront_close` §1) | card's `tabToFoundR_iff_canRaise`, `canRaise_reversibleAtW` |
| `seat_possibilities` (`RankFront_final` §2) | card's `cover_seats_cases` |
| `afterRunRemoved_ne` | `afterRunRemoved_faceUp_ne` (faceUp form) + `afterRunRemoved_hidden` (hidden form) |
| `Pile.afterRunRemoved_bare` | `afterRunRemoved_faceUp_bare` (faceUp consequence only) |
| `chop_append_singleton` (explicit `c`) | Orig2's `chop_append_singleton` (implicit `c`) |
| `twin_rank`, `twin_rank_toIdx` | `Card.twin_rank` (rfl) |
| `cover_seats`, `nextUp_raise_ne`, `suit_eq_or_twin_of_color` | card's, untouched |
| `cargoPath_shuffle`, `ShufflePlayW_append`, `shufflePlayW_revEqW`, `RevEqW_*` | Orig2 `Fiber.FloatOrbit` / `Fiber.FreeOrbit` |
| `canRaiseS_split`, `canRaiseS_iff`, `canRaiseS_orbit_rung`, `freeCardS_sem`, `freeCardS_orbit_rung` | Orig2 `Substrate.CargoRaise` / `Fiber.FreeOrbit` |
| `twin_raise_square`, `step_tabToFound_of_canRaise`, `pileOfTop_eq_none_of_found`, `rungAt_cargoPath` | Orig2 `Fork.Local.ForkCriticalPair` |
| `no_top_of_seat`, `tfc_seatOf_*`, `tfc_seat_parent`, `tfc_tabToTabR_inv`, `tfc_fromCard_cons_head`, `tfc_runOK_two_true`, `tfc_seat_point_edit`, `tfc_not_mem_faceUp_of_holdNone`, `tfc_pileHolding_none` | Orig2 `Substrate.CargoKit` / `Substrate.Kit` |
| `pileHolding_eq_some_iff`, `pileOfTop_eq_some_iff`, `pileOfTop_top`, `mem_found_unique`, `runOK_nodup`, `lastOf_snoc`, `firstWhere_congr`, `step_tabToTab_inv`, `putRun_found`, `setPile_found` | Orig2 `Substrate.Integrity` / `Substrate.Kit` |
| `SeedKit.runOK_adjacent_fit` | Orig2 `Substrate.PairClassSeed` |
| `card_eq_of_suit_rank`, `canSitOn_eq`, `Rank.toIdx_inj`, `Suit.twin_ne` | `Klondike.Basic` / `Substrate.CargoKit` |

Dropped **as unused / superseded / refutation-side** (with reason):

| `Temp` row | why dropped |
|---|---|
| `RaiseSReorderFront`, `raiseSReorderFront_false`, `raiseSReorder_false`, `not_SpecShift*`, `not_RaiseAbove`, `unraise_probe_refutes`, `urState`/`ur*`, `t4a_*`, `sortedPrefixLicence_false`, `t6_*` | kernel refutations/evidence, not part of the theorem |
| `real_rankfront_two`, `real_nil`, `raiseS_rankfront_single`, `raiseS_rankfront_of_licensed`, `real_of_licensed_distinct`, `swap_last_two` | superseded by the unconditional `raiseS_rankfront_L` |
| `canRaiseS_persist_fwd`, `raiseSSeq_defer`, `swap_c_first`, `swap_d_first`, `raiseSSeq_front_two`, `raiseS_reorder_front_of_block` | refutation-side / unused |
| `canRaiseS_of_prefix_rank_gt`, `RaiseSSeqL.drop_suffix`, `canRaiseS_of_min_rank` | unused by the proof |
| `nextUp_raise_same_suit_succ`, `not_canRaiseS_iff_of_same_suit_succ` (`SpecShift_sem` §6) | refutation evidence for the `↔` forms |
| `SortedPrefixLicence`, `SortedPrefixLicenceFixed`, `TailExists`, `RankOrder`, `LicenceStep`, `LicenceWord`, `CoverLock`, `CoverMustBeRaised`, `RankFrontClaim` | `def … : Prop` wrappers: forbidden by the vocabulary rule, or superseded by the card's defs |
| `Real`, `raiseS_rankfront_L_of_tail` | `Real` is census notation; the reduction is folded into `raiseS_rankfront_L` |
| `canRaise_lic`, `t2_*`, `t3_*`, `t5_*`, `t6_*`, `e8H`…`cKH`, `fndOf`, `stockOf`, `probeState`, `afterKH*` | probe/census example material |
| `RankFrontClose` §0 `SortedPrefixLicenceFixed` prose, census rows | evidence, not theorem |

## 7. Blunt answer

**Yes — the general rank-front theorem is now part of the `Orig2` build.**
`OneColourClosure.rankFront_holds : RankFront` compiles in
`Orig2/Fork/Class/ForkRaiseReorderProof.lean` with axioms
`[propext, Quot.sound]`, no `sorry`, no `Classical`, no `noncomputable`, and no
declaration is missing.  The only deliverable *not* produced is the optional
`resequence_of_shuffle` corollary, whose absence does not weaken `RankFront`
(§4 above gives the two concrete reasons).
