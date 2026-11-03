# GOAL + NEXT STEPS (resume card)

Snapshot: branch `macro-game`, remote `origin/macro-game` at `9cab052` — everything below is
committed and pushed.

---

## THE GOAL (one line)

> Prove **`raises_or_fork`** and derive **`FullJoinAtLeastOrFork`** from it, with **no residue**
> — i.e. without `SatDifferForkWF`, `ArmDichotomy`, `ForklessHasTop`, `BottomDip` or any
> `ForklessOrFork` decision.

```lean
-- the target
theorem raises_or_fork {s t : State} (hs : s.WF) (h : sameOrbitSetoid.r s t) :
    (∃ ws v, RaiseSSeqLicensed s ws v ∧ RungLe s v ∧ RungLe t v) ∨ Fork s

-- the payoff (proved, waiting only for the target)
theorem fullJoinAtLeastOrFork_of_hPull (hPull) (hspectrum) : FullJoinAtLeastOrFork
```

Meaning: *from `s`, raising only (each raise may be preceded by slides), you can reach rungs
dominating both `s` and `t` — or the class forks.* With `w := v`, the endpoint is the join.

Full working document: `Temp/RAISES_OR_FORK_PLAN.md`.

---

## DONE (do not redo)

| area | theorem / file |
|---|---|
| path induction, all cases but the pull-twin arm | `raises_or_fork_play`, `raises_or_fork_of`, `fullJoinAtLeastOrFork_of_hPull` — `Temp/RaisesOrForkMain.lean` |
| pull case, non-twin and `c ∈ ws` | `pull_case_noTwin`, `pull_case_mem` (both unconditional) |
| append → hoist → cancel, endpoint `v + e_c` | `pull_case_of_end_live`, `cancel_prefix_is_play_from_source` |
| block-end insertion / rank housing | `insert_at_block_end(_split/_sorted)`, `suffix_transport`, `Temp/BlockHousing.lean` |
| licence at the block end | `block_end_licensed`, `block_end_licensed_or_dichotomy` |
| obstruction trichotomy + dichotomy (cover ∨ lock) | `not_canRaiseS_cases`, `obstruction_dichotomy` |
| commit lock frozen across the orbit | `FrozenSuit.commitLocked_rung_le` |
| spectrum collapse (fork branch) | `SpectrumCollapse.spectrum_pair_fork_or_both` (+ trichotomy with the flipped fork) |
| fork producers | `fork_of_spectrum`, `fork_of_collapsed_spectrum` |
| rung ledger | `RungMono.*`, `RaiseSSeqLicensed.rungAt_eq` |
| pull/raise cancellation | `pull_raise_id` (needs `s.WF`) |
| the campaign link | `fullJoinAtLeastOrFork_of_raises_or_fork` |

**Refutations — never re-attack:**
* `PullReplayCounter.block_end_licensed_twin_refuted` — `block_end_licensed` without
  `c.twin ∉ ws` is FALSE. Board: `♥=A..4, ♦=A..4` founded, `p0=[6♣,5♥,4♠]`, `p1=[6♠,5♦]`,
  `c=5♥`, `ws=[5♦]`. All three plan arms fail there; only the **replay at `s`** works.
* `raiseSReorder_false`, `raiseSReorderFront_false` — the **unsorted** front is false.
* `not_SpecShift`, `not_RaiseAbove` — the `↔` licence-shift forms are false (forward only).
* `unraise_probe_refutes` — higher-rank inertness fails for unlicensed (commit) steps.
* `SortedPrefixLicence` without `x ∉ R` is false.

---

## OPEN — exactly one arm

```lean
theorem pull_case {s u t v : State} {c : Card} {b : Base} {ws : List Card}
    (hs : s.WF) (hpull : State.step s (Move.foundToTab c b) = some u)
    (hρ : RaiseSSeqLicensed u ws v) (ht : RungLe t v) (hno : ∀ d ∈ ws, d.suit ≠ c.suit) :
    (∃ v', RaiseSSeqLicensed s (playWord (sortByRank ws)) v' ∧ RungLe s v' ∧ RungLe t v')
    ∨ Fork s
```

Proof plan (detailed in `RAISES_OR_FORK_PLAN.md` §4 and in the agent brief):

1. **Case A `CanRaiseS v c`** — `pull_case_of_end_live` + rung arithmetic. Closes immediately;
   no deficit hypothesis needed.
2. **Case B `¬ CanRaiseS v c`** — then `c.twin ∈ ws` automatically
   (`canRaiseS_of_word_notMem`). Sub-cases:
   * `CoveredAt bnd c` with the cover raisable ⇒ insert `raise cover` (rank `c.rank − 1`,
     suit ≠ `c.suit`) at its rank boundary ⇒ `c` live ⇒ Case A;
   * commit-locked at `bnd` **and** `nextUp c` ⇒ contradiction with
     `FrozenSuit.commitLocked_rung_le` (since `s` has `c` founded, `rungAt s c.suit = c.rank + 1`);
   * `¬ nextUp c` ⇒ recurse on the suit's next card (ranks strictly decrease, ≤ 13 steps);
   * cascade bottoms out ⇒ **replay `ws` at `s`**: per letter the local reads are identical
     except `c.twin`'s, which needs `c.twin` to be a **pile top** at `s`; if it is, the replay
     lands at `v + e_c ≥ s, ≥ t`.

**Acceptance test:** the refutation board above must be closed by the replay (there `5♦` is a
pile top at `s`).

---

## NEXT ACTIONS (in order)

1. Wait for `Temp/PullTwin.lean` (agent running) and check whether `pull_case` closed.
   * Compile: `lake env lean Temp/PullTwin.lean`; check `#print axioms` = `[propext]` /
     `[propext, Quot.sound]`; check the acceptance board is handled.
2. If `pull_case` closed ⇒ instantiate:
   ```lean
   theorem raises_or_fork := raises_or_fork_of (hPull := pull_case) (hspectrum := …)
   theorem fullJoinAtLeastOrFork := fullJoinAtLeastOrFork_of_hPull (hPull := pull_case) …
   ```
   then `lake build` the two new modules and commit.
3. If a sub-case is open ⇒ take the **precise residual** from the agent's report, check it
   against the DONE ledger (is it already a proved lemma in disguise?), and only then extend
   the plan.
4. Optional hardening: port the lane's `Temp` files into `Orig2` (as was done for
   `ForkRaiseReorderProof`), so the theorem is part of the library build.

---

## GUARDRAILS (learned the hard way)

* **`RaiseSSeqLicensed` word order:** the head of the word is the **LAST** raise; the last
  element is the first raise. Check every statement against this.
* **A reduction must delete a hypothesis or weaken a conclusion.** Adding a conjunct, a play,
  a valley, or a minimality condition is a *new target*, not progress.
* **Check every agent-reported "residual" against the DONE ledger** before adopting it
  (`pull_replay` and `BottomDip` both cost rounds this way).
* **Axioms:** every theorem must be `[propext]` or `[propext, Quot.sound]`. `List.countP`
  rewrites can sneak `Classical.choice` in — always run `#print axioms`.
* **`s.WF` matters:** `pull_raise_id` and the obstruction lemmas are false without it
  (duplicate cards break `pileOfTop`).
* **Never use** `by_cases` on an undecidable Prop (injects `Classical.choice`); split on
  `Nat` equalities or `Bool` reads instead.

## RESUME COMMANDS

```
cd lean-model
git pull --rebase origin macro-game          # if the remote moved
lake env lean Temp/RaisesOrForkMain.lean     # the induction (hPull-conditional)
lake env lean Temp/PullTwin.lean             # the open arm
# build order for imports:
lake env lean -o .lake/build/lib/lean/Temp/RungMono.olean Temp/RungMono.lean
# … same for PullRaiseId, Obstruction, FrozenSuit, RaisesOrFork, BlockHousing,
#            SpectrumCollapse, PullReplay, RaisesOrForkMain
```
