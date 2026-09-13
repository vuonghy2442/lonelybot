# The proof farm — handoff document

51 `sorry`s (recount: `Select-String -Path Klondike\*.lean -Pattern ':= sorry'`),
each carrying a `TODO(proof)` route comment in source.  Difficulty:
**[T]** rfl/decide/case-bash · **[E]** one induction · **[M]** real
work · **[H]** needs ideas (do not assign casually).

**`FARM_MEMORY.md`** — the agents' append-only shared quirks ledger
(syntax, recipes, wrong routes, reusable helpers).  Read it first;
append your findings there, never here.

## Rules of engagement

- **The prover is the oracle.**  Build after every edit —
  `lake build Klondike`; one file: `lake env lean Klondike/Foo.lean`.
  The errors print the goal and often the fix.
- **Syntax is a query, not a recall test.**  Two candidate
  spellings?  Pick either, build, let the error choose.  At most one
  reasoning step on syntax before a build.
- **Cheap tactics first**: `rfl`, `decide`, `simp`, `omega` — several
  items fall immediately (`flipAll_eq_relabelTwin` was `rfl`).
- **Routes here are hypotheses.**  Prover disagrees with a route ⇒
  fix the row, not the proof; record it as a finding.
- **Statements can be wrong too.**  Confirm the counterexample with
  the prover, `git grep` downstream users, repair *minimally* — add
  the missing hypothesis, never weaken the conclusion (vacuous is
  worse than `sorry`) — fix the row.  No guard saves it ⇒ mark
  **UNSOUND**, record the witness, escalate (the ledger's
  rejected-claim discipline).  Worked example:
  `eStep_deckStack_unique` needed `noDupCards` — a duplicated order
  gives two draw indices, hence two offsets.
- **Hygiene**: one item at a time; tree stays green; commit per
  batch (`feat(lean): prove ...`); others' `sorry`s are untouchable.

## Syntax card — paid-for facts (core 4.30, no mathlib)

- `xs[i]?`, not `List.get?`; removal is `Cycle.removeIdx` (ours).
- Dot notation needs `def State.foo` — a top-level `def foo (st : State)` won't project.
- Impossible `none = some c`: `simp at h`, not bare `Option.noConfusion h`.
- Multi-line `{st with …}`: first field on its own line.
- `decide` needs `Decidable` — no matches returning `Prop`.
- `Nat` subtraction truncates: `0 - 1 = 0` (silent index bugs).
- `∈ b :: t`: `simp only [List.mem_cons] at h` before `rcases`.
- `omega` knows literal `/` and `%`; treats the rest as atoms.
- Known-good simp set: `mem_cons/map/append/flatMap/range`,
  `decide_eq_true_iff`, `and_eq_true`, `some.injEq`.
- `rfl` is strong here (structure eta carries it across states).
- `Rank`/`Anchor` are inductives on purpose — no `Fin`.

Work the waves in order — later waves lean on earlier ones.  Within a
wave, items are independent (different agents can take different rows
without colliding).

## Wave 0 — COMPLETE (2026-09-13)

All computation items: the C2 uniqueness quartet (deckStack's
statement repaired with `noDupCards`), `removeAt_comm`,
`esolvable_offset_irrel` (+ reusable `eStep_offset`/`eRun_offset`/
`isWin_offset`), the seven Progress measure/fold lemmas, and the
`Initial` trio (`universe_noDup`, `ofList_wf`, `initial_wf` — the
file fully proven, with the `initBase`/`initStep` fold refactor).

## Wave 1 — COMPLETE (2026-09-13)

Board.lean fully proven: `bottomOf_eq`, `bottomOf_eq_none`,
`empty_bottomOf`, the `attach` consumption lemmas, `mapBy`'s law.
New reusables: `attach_inj`, `mapBy_inj`, `Base.flipBase_flipBase`,
`Board.ext_topOf` (same `topOf` ⇒ equal boards).

## Wave 2 — move-level glue

| item | file:line | tag | route |
|---|---|---|---|
| `legal_pileStack_iff` | Move | [M] | unfold `apply`; the Board lemmas (Wave 1 done) |
| ~~`apply_wf`~~ | Move | **done** | the 7-way maintenance lemma, all arms — the keystone; the old "sub-multiset" blocker died with WF's `stock_wf` (noDup + membership) repair |
| `pilePile_roundtrip` | Theorems | [M] | the run carries back; `aboveOf` untouched |
| ~~`pileStack_stackPile_roundtrip`~~ | Theorems | **done** | detach-then-attach; heights ± |
| ~~`draw_full_cycle`~~ | Theorems | **superseded** | the rotate-form died with the physical rework (rotate removed); replaced by `draw_full_pass` below (Wave 9) |
| `draw_full_pass` | Theorems | [M] | the deal chain from cursor 0: each deal from `k·s` lands `min ((k+1)·s, n)`, the clamp hits `n` at `k = ⌈n/s⌉`, the next deal wraps; period `⌈n/s⌉+1` at any `s ≥ 1` |

## Wave 3 — symmetry and commutation

| item | file:line | tag | route |
|---|---|---|---|
| `apply_relabel` | Theorems:72 | [M] | 7 move cases; each near-`rfl` (factored suits!) |
| `solvable_relabel` | Theorems:78 | [M] | play induction via `apply_relabel` |
| `irreversible_reveal` | Theorems:128 | [M] | depths monotone along plays |
| `irreversible_deckPile` | Theorems:132 | [M] | cycle length monotone along plays |
| `irreversible_deckStack` | Theorems:136 | [M] | as above |
| `commute_of_compsDisjoint` | Theorems:194 | [M] | per-move: legality reads only own components |
| `reveal_draw_comm` | Theorems:200 | [E] | instance of the above |
| `commute_of_disjoint_touch` | Theorems:229 | [H] | the type-ball lemma — the C13 premise |
| `drawTo_comm_modAdjacent` | Theorems:240 | [M] | `removeIdx_comm` + cursor arithmetic (incl. wrap) |
| `drawTo_nonadjacent_diverge` | Theorems:253 | [M] | end cursors `j−1` vs `i` |

## Wave 4 — structure and progress

| item | file:line | tag | route |
|---|---|---|---|
| `aboveOf_rank_grading` | Theorems | [M] | induction along the walk; WF edge legality |
| `aboveOf_irrefl` | Theorems | [E] | from the grading |
| ~~`play_self_is_shuffle`~~ | Progress | **done** | measure-disjunction induction (route revised — see FARM_MEMORY) |
| ~~`play_cut_loop`~~ | Progress | **done** | `run_append` + determinism |
| ~~`solvable_iff_distinctTrace`~~ | Progress | **done** | + `run_take_trace` workhorse |
| `solvable_iff_boundedPlay` | Progress | [H] | distinct trace + the shape count (needs `apply_wf`) |
| `solvable_decidable` | Progress | [H] | bounded enumeration |

## Wave 5 — the dominances (§5)

| item | file:line | tag | route |
|---|---|---|---|
| `dominant_of_commutesWithAll` | Dominance:41 | [M] | play induction, bubbling |
| `safe_pileStack_dominant` | Dominance:62 | [H] | worry-back; return-base is the crux |
| `least_redundantStack_dominant` | Dominance:90 | [H] | §5.2's canonical-representative argument |
| `deck_dominance_draw1` | Dominance:113 | [H] | front-loading reshaping; the pure-deck fact |
| `stackPile_safe_prunable` | Dominance:120 | [H] | §5.4 first half |
| `deckPile_safe_prunable` | Dominance:126 | [H] | §5.4 second half |
| `twinPair_placement_equi` | Dominance:140 | [H] | local twin swap; both heights equal is the license |
| `cascade_sound` | Dominance:158 | [H] | **the open composition question** — needs the progress measure (Wave 4's cycle theorem) |

## Wave 6 — the B-legs core

| item | file:line | tag | route |
|---|---|---|---|
| ~~`solvable_of_accommodates`~~ | Theorems | **done** | prepend the shuffle play |
| `solvable_accommodates` | Theorems | **[H]** | **B4 / the reshape lemma — the farm's hardest item** |
| `solvable_engine_iff` | Move | **[H]** | the no-pile-to-pile legs |
| ~~`realizable_of_wf`~~ | Realizability | **done** | WF → Fits glue (post-repair) |
| ~~`apply_realizable`~~ | Realizability | **done** | one line: `realizable_of_wf (apply_wf …)` — the keystone's shadow |
| `uncovered_eq_freeType` | Realizability | [M] | the counting bijection (injectivity + edge legality) |

## Wave 7 — macro and bridge

| item | file:line | tag | route |
|---|---|---|---|
| `macroStep_engine_play` | Macro:52 | [M] | unfold; shuffles + rotation + commit are engine moves |
| `solvableEngine_iff_macro` | Macro:62 | [H] | A3's regrouping (draws commute, trailing draws drop); at draw ≥ 2 routes through the Wave-9 jump-soundness |
| `drawTo_tableau_outcomes_agree` | Macro:77 | [M] | from `applyDrawTo`'s def + `attach` lemmas (the guard selects the same `i` both times) |
| `toEngine_simulates` | Bridge:152 | [H] | play induction; draws collapse into rotations (model engine ⊆ abstract — the model's pacing is stricter, this direction is unguarded) |
| `toEngine_lifts` | Bridge:161 | **[H]** | the lift — witnesses become accommodations (B4-adjacent); **draw-1 gated (statement repaired 2026-09-13: the abstract deck moves are free jumps, the model is paced — at draw ≥ 2 the lift fails; the all-steps form needs the `eStep` guard + `equivalent_to`, deferred reading)** |
| `engine_iff` | Bridge:167 | [H] | simulation + lift (draw-1 gated as the lift) |

## Wave 8 — the draw pacing (any step; the unsat ladder's G4)

The reading is done (deck_bf.py: the characterization validated on
every reachable state N ≤ 15, all permutations N ≤ 9, 6k random
sequences at N = 24 both directions, all 56 corpus d3 winning lines;
steps 2 and 4 likewise — states N = 6/9, all permutations N ≤ 8,
1k+1k samples at N = 12, zero violations; pace_port_check.py: the
Lean port ≡ deck_sim, 260 states 0 mismatches).
Depends only on wave 0's cycle lemmas — independent of waves 2–7.

Statement-repair history (2026-09-13, the wrong-statement protocol):
`maskPos_mem_iff`/`maskPos_step1`/`realizes_iff_stepsOK` gained the
cursor invariant `hcur : cursor ≤ length` (past `len + 1` the wrapped
lane leaks out-of-range positions); `pos_shift` gained `noDupCards`
(with duplicates the run draws the same value twice while `rBelow`
counts by `idxOf`); and the divergence the wave arrived with was
resolved in the machine, not the statement — `Cycle.drawTo` is now
the deck.rs-literal jump `{ cursor := i + 1 }` (saturating), so
`cursor_after` is exact with no mod.

| item | file:line | tag | route |
|---|---|---|---|
| ~~`laneUp_mem`~~ | Pace | **done** | fuel induction + the `(a + step) % step` shift lemma |
| `maskPos_mem_iff` | Pace | [M] | mem_append/mem_singleton + laneUp_mem ×2; case cursor = 0 and cursor % step = 0; the residue bookkeeping is Nat.mod_eq_of_lt + omega; `hcur` is the cursor invariant |
| ~~`maskPos_step1`~~ | Pace | **done** | laneUp_mem + `Nat.mod_one`, cases on the cursor |
| `pos_shift` | Pace | [M] | induction on pre through run; removeIdx order preservation + the below-count split; `hnd` excludes the duplicate-draw witness |
| `cursor_after` | Pace | [M] | drawTo i lands i+1 exactly, removeAt i decrements — no wrap anywhere now; pos_shift supplies i |
| `burial_bound` | Pace | [M] | idxOf injective on d (hnd), so O(w) < O(x) vs O(x) < O(w); the first is the saturation count (the interval holds exactly O(x) − O(w) − 1 cards besides w), the second vacuous both sides |
| `realizes_iff_stepsOK` | Pace | **[H]** | prefix-walk induction with maskPos_mem_iff + pos_shift + cursor_after + burial_bound; ← induction, each stepOK disjunct via the converses (a leading-lane claim after a max-draw forces p = last, so the max disjunct catches it). `hcur` is the initial state's invariant, maintained by every drawCard. The SAT ladder's rung-3 soundness reduces to this row |

**Deliberately not in the farm** (need reading, not proving):
the `bm` XOR algebra (state.rs), C12 (macro_formalization §6.5b),
B3 (no_pile §6), the 61-bit encode packing, and the all-steps
bridge (the `eStep` pacing guard + the `equivalent_to`
transposition identity replacing `eRun_offset` — see
`toEngine_lifts`'s note). (Draw-3 pacing was
here until 2026-09-13: the reading is done — wave 8.)

## Wave 9 — the deck integration (jump ≡ deal-then-play)

The physical rework's payoff statements: the guarded Draw
commitments ARE the physical game.  Depends on wave 8 (the
maskPos ↔ deal-reachability correspondence is its content).
`reachablePos_step1` is done and reusable — the draw-1 degeneration
at the game level (C9's premise, now a theorem), the gate the wave-7
repairs lean on.

| item | file:line | tag | route |
|---|---|---|---|
| `applyDrawTo_eq_dealPlay` | Theorems | **[H]** | → the guard gives the deal count (maskPos ↔ deal-iteration — wave 8's chain), then `apply_deckPile_iff`'s shape; ← contrapositive by the same correspondence.  Draw-1 instance: `reachablePos_step1` + every jump is k deals |
| `applyDrawStackTo_eq_dealPlay` | Theorems | **[H]** | as above through `apply_deckStack_iff` |

## Wave 10 — the pace dominance (the offset-dominance registry)

Filed 2026-09-13 after the engine measurements: the refuted-offset
registry rules R1/R2, measured at **43.8% of seed-32 draw-3 states**
(1.38M of 3.15M doomed; 912k of them pure states killed by impure
siblings — R2 is the bigger half); draw-1 exactly 0 (its offsets are
fully normalized — the rules are draw-3's analogue of that).  Rust
falsifier: `pace_dominance_order` (src/macro_game.rs — 100 random
decks × every offset: pure-pure equal, residue-monotone, impure ⊇
pure, merge holds).  The machine rows depend only on wave 8's
`maskPos_mem_iff`; the game rows are the macro machinery.

The theorem family: the state space factors as *board × pace* —
reveals are pace-inert (never touch the stock), draws reset the pace
to the drawn card's position (a function of the cards alone), so the
pace only matters through `maskPos` at the instant of a draw.

| item | file:line | tag | route |
|---|---|---|---|
| `maskPos_pure_indep` | Pace | [E] | maskPos_mem_iff ×2: a pure cursor's leading lane has residue step−1 (vacuous at 0/pass-end), subsumed by the batch-top disjunct — both sides reduce to batch ∪ last |
| `maskPos_residue_mono` | Pace | [E] | maskPos_mem_iff: disjuncts 1–2 cursor-free; the leading lane's `o'−1 ≤ p` weakens to `o−1 ≤ p`, residues agree |
| `maskPos_impure_sup_pure` | Pace | [E] | the pure side reduces to the cursor-free disjuncts (pure_indep's route), which the impure side covers |
| `drawCard_cursor_indep` | Pace | [E] | congruence: posOf (cards-only), drawTo overwrites the cursor, removeAt's successor cursor reads the overwritten value — no source cursor anywhere |
| `pace_dominance` | Macro | **[H]** | the simulation: induction on the commitment list; reveals preserve the (equal-boards, maskPos-superset) invariant, the draw case merges via `drawCard_cursor_indep`; accommodations replay verbatim (stock-blind) |
| `pace_dominance_residue` | Macro | [M] | `pace_dominance` at the o-variant + `maskPos_residue_mono` as `hK` |
| `pace_dominance_impure_pure` | Macro | [M] | `pace_dominance` at the o-variant + `maskPos_impure_sup_pure` as `hK` |
