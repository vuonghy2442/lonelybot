# The proof farm — handoff document

62 `sorry`s (recount: `Select-String -Path Klondike\*.lean -Pattern ':= sorry'`),
each carrying a `TODO(proof)` route comment in source.  Difficulty:
**[T]** rfl/decide/case-bash · **[E]** one induction · **[M]** real
work · **[H]** needs ideas (do not assign casually).

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

## Wave 0 — no dependencies, pure computation

| item | file:line | tag | route |
|---|---|---|---|
| ~~`removeAt_comm`~~ | ~~Cycle:116~~ | **done** | `removeIdx_comm` + cursor `if`s |
| `apply_reveal_totalDepth_lt` | Progress:21 | [E] | case `reveal`; `totalDepth` is a sum of 7 |
| `apply_totalDepth_le` | Progress:25 | [E] | 7-way move case bash; only reveal changes depths |
| `apply_stockLen_le` | Progress:29 | [E] | 7-way case bash; nothing adds to the cycle |
| `apply_deckPile_shortens` | Progress:35 | [E] | WF cursor bound makes `cursor−1` a valid index |
| `apply_deckStack_shortens` | Progress:40 | [E] | as above |
| `run_append` | Progress:55 | [E] | induction on `l₁`; `run` is a fold |
| `run_eq_trace_last` | Progress:71 | [E] | induction on the play |
| ~~`eStep_pileStack_unique`~~ | ~~Bridge~~ | **done** | the witness only justifies |
| ~~`eStep_deckPile_unique`~~ | ~~Bridge~~ | **done** | `noDupCards` pins the draw index |
| ~~`eStep_deckStack_unique`~~ | ~~Bridge~~ | **done + statement fixed** | was *unsound* without `noDupCards` — a duplicated order gives two indices, two offsets |
| ~~`eStep_stackPile_unique`~~ | ~~Bridge~~ | **done** | as `pileStack` |
| `esolvable_offset_irrel` | Bridge:144 | [E] | no guard reads the offset (v1); plays correspond |
| `Card.universe_noDup` | Initial | [M] | index-wise, over the factored product |
| `Deal.ofList_wf` | Initial | [M] | lengths by the triangular split; `drop`/`take` preserve |
| `initial_wf` | Initial | [M] | the exhibit — initial edges are WF-exempt by construction |

## Wave 1 — the Board foundation (everything leans on these)

| item | file:line | tag | route |
|---|---|---|---|
| `bottomOf_eq` | Board:114 | [M] | `findFirst_mem` + `findFirst_of_unique` + `enumBase_complete` + `inj` |
| `bottomOf_eq_none` | Board:118 | [M] | `findFirst_eq_none` + `enumBase_complete` |
| `empty_bottomOf` | Board:128 | [E] | `findFirst_eq_none` + `empty_topOf` |
| `attach_topOf` | Board:175 | [E] | unfold `attach`; `update_self` |
| `attach_topOf_ne` | Board:179 | [E] | `update_ne` |
| `attach_eq_some_iff` | Board:183 | [E] | the two dite guards |

## Wave 2 — move-level glue

| item | file:line | tag | route |
|---|---|---|---|
| `legal_pileStack_iff` | Move:194 | [M] | unfold `apply`; the two Board lemmas above |
| `apply_wf` | Move:218 | [M] | 7-way case bash; the matching clause uses `bottomOf_eq` |
| `pileStack_stackPile_roundtrip` | Theorems:105 | [M] | detach-then-attach = identity; heights ± |
| `pilePile_roundtrip` | Theorems:111 | [M] | the run carries back; `aboveOf` untouched |
| `draw_full_cycle` | Theorems:119 | [E] | `(cursor + len) % len = cursor` from the WF bound |

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
| `aboveOf_rank_grading` | Theorems:265 | [M] | induction along the walk; WF edge legality |
| `aboveOf_irrefl` | Theorems:269 | [E] | from the grading |
| `play_self_is_shuffle` | Progress:49 | [M] | Wave 0 measures + play induction |
| `play_cut_loop` | Progress:87 | [E] | `run_append` + determinism |
| `solvable_iff_distinctTrace` | Progress:79 | [M] | cut loops until fixpoint |
| `solvable_iff_boundedPlay` | Progress:107 | [H] | distinct trace + the shape count (needs `apply_wf`) |
| `solvable_decidable` | Progress:112 | [H] | bounded enumeration |

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
| `solvable_of_accommodates` | Theorems:158 | [E] | prepend the shuffle play |
| `solvable_accommodates` | Theorems:164 | **[H]** | **B4 / the reshape lemma — the farm's hardest item** |
| `solvable_engine_iff` | Move:213 | **[H]** | the no-pile-to-pile legs |
| `realizable_of_wf` | Realizability:117 | [M] | WF → `Board.Fits` glue |
| `apply_realizable` | Realizability:126 | [M] | `apply_wf` + the above |
| `uncovered_eq_freeType` | Realizability:94 | [M] | the counting bijection (injectivity + edge legality) |

## Wave 7 — macro and bridge

| item | file:line | tag | route |
|---|---|---|---|
| `macroStep_engine_play` | Macro:52 | [M] | unfold; shuffles + rotation + commit are engine moves |
| `solvableEngine_iff_macro` | Macro:62 | [H] | A3's regrouping (draws commute, trailing draws drop) |
| `drawTo_tableau_outcomes_agree` | Macro:77 | [M] | from `applyDrawTo`'s def + `attach` lemmas |
| `toEngine_simulates` | Bridge:152 | [H] | play induction; draws collapse into rotations |
| `toEngine_lifts` | Bridge:161 | **[H]** | the lift — witnesses become accommodations (B4-adjacent) |
| `engine_iff` | Bridge:167 | [H] | simulation + lift |

**Deliberately not in the farm** (need reading, not proving):
the `bm` XOR algebra (state.rs), C12 (macro_formalization §6.5b),
B3 (no_pile §6), draw-3 pacing (last_draw_rules.md), the 61-bit
encode packing.
