# The proof farm — handoff document

38 `sorry`s (recount: `Select-String -Path Klondike\*.lean -Pattern ':= sorry'`),
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
| `apply_wf` | Move | [H] | 7-way; the cycle must be a deal-stock sub-multiset — **WF was repaired for this** (5 witness-confirmed holes, see FARM_MEMORY) |
| `pilePile_roundtrip` | Theorems | [M] | the run carries back; `aboveOf` untouched |
| ~~`pileStack_stackPile_roundtrip`~~ | Theorems | **done** | detach-then-attach; heights ± |
| ~~`draw_full_cycle`~~ | Theorems | **done + statement fixed** | `≤` was false — rotate never lands at `length`; repaired to `<` |

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
| `apply_realizable` | Realizability | [M] | `apply_wf` + the above |
| `uncovered_eq_freeType` | Realizability | [M] | the counting bijection (injectivity + edge legality) |

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
