# The proof farm — handoff document

**Census: 12 `:= sorry`** (Theorems 1 · Dominance 4 · Kills 4
· Restriction 2 · TwinSwap 1; zero bullets).  Pinned by
`pwsh ../script/lean-census.ps1` (run from `lean-model/`) — it fails on
any NEW sorry or the return of a refuted constant.  All 12 are
believed-true open theorems with routes below.
Every definition is final code; refutations live in
[witnesses/](witnesses/) and the REFUTED section below — **not** in
the library.

Session history: 63 (farm open) → 30 (2026-09-13 morning) → **7**
(2026-09-13 evening: waves 8/9/10 complete, the pace family, the B4
decomposition, cascade_sound; ~26 theorems proved, **6 fresh
refutations** — every one caught by a refute-first probe *before*
wasted proof effort — and 2 legacy refuted constants removed from the
library).

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
  **UNSOUND**, record the witness, remove it from the library (see
  REFUTED below), escalate.  Worked examples:
  `eStep_deckStack_unique` needed `noDupCards`; `realizes_iff_stepsOK`
  needed `hpure`; the crux needed `hnotlock`.
- **Refute-first**: the target statements have not been through the
  witness protocol.  Before investing in a proof, spend a bounded
  probe attempting to falsify it (`#eval` grids on small instances —
  the definitions are executable).  Session evidence: 6 of 6
  refutations were caught this way, cheaply.
- **Hygiene**: one item at a time; tree stays green; commit per
  batch (`feat(lean): prove ...`); others' `sorry`s are untouchable.
  Parallel sessions may be farming — never revert anyone's work.

## Syntax card — paid-for facts (core 4.33.1, no mathlib)

- Toolchain: v4.33.1 (migrated from 4.30.0-rc2 with three one-line
  fixes).  `Nat.div_add_mod` product order flipped in 4.33.
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
- `lake env lean` reads DISK oleans — after editing an upstream file,
  refresh with a scoped `lake build Klondike.<Module>` (never a full
  build from an agent; lock contention).  Sibling red-olean outages
  are weather: poll, don't work around.
- MORE in FARM_MEMORY (the ledger is the source of truth — e.g. the
  `cases h : e` goal-substitution trap, `bif`'s trailing `rfl`,
  `show...from` not a tactic, state_ext slot order).

## Proved infrastructure (cite these, don't re-prove)

The general theorems that factor the routes:

- **Search/progress** (Progress, sorry-free): `run_append`,
  `solvable_of_reaches` + `solvable_iff_mutuallyReaches`,
  `play_self_is_shuffle` (every cycle is a shuffle), `play_cut_loop`,
  `solvable_iff_distinctTrace`, `solvable_iff_boundedPlay`.
- **Simulation**: `solvable_of_simulates` (move level),
  `macroSolvable_of_simulates` (macro level — the parent every pace
  dominance instantiates).
- **The pace machine** (Pace, sorry-free — G4 machine-checked): the
  residue kit, `maskPos_mem_iff` (the characterization),
  `drawCard_cursor_indep`, `run_cards_filter` (the run's end deck IS
  `filter (·∉pre)`), `pos_shift`, `cursor_after`, `burial_bound`,
  **`realizes_iff_stepsOK`** (repaired `+hpure`; rung 3's soundness),
  `maskPos_step1`, `maskPos_pure_indep/_residue_mono/_impure_sup_pure`.
- **Pace dominances** (Macro): `pace_dominance`, `_residue`, `_impure_pure`
  (the simulation forms), the physical family (`deal_chain_reaches`,
  `deal_passEnd_reaches` — both repaired `+hstep`),
  `pace_dominance_phys_residue/_passEnd`, `solvable_iff_pure_cursors`,
  `window_firstDraw(_macro)`, `run_replicate_draw`,
  `dealOnce_iterate_add`, `dealOnce_reach_end(_any)`.
- **Dominance layer** (Dominance): `dominant_of_commutesWithAll`
  (the POR bridge), `safe_pileStack_dominant_of_return` (the R-half),
  `deckPile_safe_prunable` (§5.4 second half), `stackPile_pileStack_cancel`,
  **`cascade_sound`** (repaired: the escape move must strictly drop
  `cascadeMeasure := heightDebt + totalDepth + stockLen`; the
  instantiation kit `cascade_escape_progress` proves the commit
  moves do).
- **The B4 case kit** (Theorems, around the crux):
  `solvable_of_stackPile` (the worry-back half), `solvable_of_pileStack_return`
  (the returnable endgame — CLOSED), `pileStack_pilePile_stackPile`,
  the commute squares `pileStack_comm_{draw,reveal,deckStack,deckPile}`,
  `stackPile_pileStack_return`, `pileStack_stackPile_roundtrip`,
  `solvable_of_accomm_step` (+hnl) and the `safeAccommodates` induction
  skeleton (the main `solvable_accommodates` is proved against the crux).
- **Kit/Cycle-level**: Kit's idxOf/take/count kits
  (`idxOf_filter`, `filter_split_compl`, `count_below`,
  `filter_mem_take_count`, `mem_removeIdx_of/_iff`, `NoDupP_noDupCards`,
  `dropLast_append_single`); the upstream lifts
  `State.isLocked` (State.lean), `vis_base_of_notLocked` (Theorems),
  `Board.bottomOf_detach_self` (Board).
- **The wave-9 deck integration** (Theorems):
  `applyDrawTo_eq_dealPlay` / `applyDrawStackTo_eq_dealPlay`
  (the jump-soundness theorems, `+canPlace` repair), the
  `dealIter`/`dealChain`/`draw_full_pass` machinery.

## Wave 11 — the open items (7)

Work any row; D-rows collide only with each other (same file).
Within Dominance, rows are independent.

| item | file:line | tag | route |
|---|---|---|---|
| `solvable_of_pileStack` (the crux) | Theorems:1028 | **[H]** | the case ledger below — 2 squares, the π-induction, then the park/endgame (N-half) |
| ~~`solvableEngine_iff_macro` (C1)~~ | Macro | **done** | A3's regrouping landed (parallel session) |
| `safe_pileStack_dominant` (N-half) | Dominance:237 | [H] | post-crux: the endgame IS this row's root (canReturnBase fails on deal-adjacent bases → rank-mate worry-back) |
| `least_redundantStack_dominant` | Dominance | **done**(repair+proof, parallel session) | repaired `+hsafe` exactly per the wave-11 concern (safety premise was missing); proven against §5.1's R-half |
| `deck_dominance_draw1` (C4) | Dominance:292 | [H] | front-loading reshaping; the pure-deck fact; draw-1 — `maskPos_step1` (every position accessible) + the deal machinery |
| `stackPile_safe_prunable` (§5.4 first half) | Dominance:421 | [H] | worry-back ban; the cancellation kit (`stackPile_pileStack_cancel`) + the safety formula |
| `twinPair_placement_equi` (C6) | Dominance:492 | [H] | T machinery (`solvable_flipAll`, PROVEN) applied as a local swap; both heights equal is the license |

## Wave 12 — the closure-goal kills (the K-rules, scaffolded 2026-09-13)

The engine's `goal_dead` (src/macro_game.rs K1–K6) as closure
invariants over `safeAccommodates`.  Scaffolded and believed-true;
**refute-first gate**: the Rust differential probe
(`macro_direct_matches_oracle`) — there is no Lean-side executable
closure walk, do not hand-probe with `#eval`.  Substrate landed and
proved: `Card.only_blocker_is_twin` + `Card.receivers` +
`Card.mem_receivers_iff` (Basic.lean), `State.frontier` (State.lean —
the `ClosureCtx.frontier` mirror), `Rank.toIdx_inj` homed upstream.

Work order: the keystone first — the two K-rows consume it.

| item | file:line | tag | route |
|---|---|---|---|
| `vis_of_safeAccommodates` | Kills:40 | [M] | play induction; the foundation-side shadow (closure-foundation ⊆ root-foundation ∪ root-vis) is the carry; `stackPile`'s new visible comes from the firing foundation |
| `State.frontier_spec` | Kills:52 | [M] | `find?` spec over the `toIdx`-filtered `Rank.all`; minimality needs the filtered list's `toIdx`-sortedness (decide-able list fact) |
| `K1_stack_goal_dead` | Kills:75 | [M] | keystone + frontier_spec + the climb lemma (heights rose past `k` ⟹ rank `k` was `pileStack`-fired; play induction) |
| `K2_tableau_goal_dead` | Kills:89 | [E] | `canPlace` case-split; king excluded by `hking`; `inr d` ⇒ `d ∈ receivers` (mem_receivers_iff) ⇒ keystone contradicts `hrecv` |

**Not yet statable (prerequisites, then come back)** — text rows, do
NOT add constants prematurely (the no-guessing rule; C12's deferral is
the model):

- **K4** (first-layer locked king's reveal-tableau goal never opens):
  needs a `firstLayer` predicate (pile's hidden bottom card).  Base-rule
  note: the engine's `reveal` generator additionally excludes lone
  first-layer kings and reads `free_slot` (state.rs:314) — the model's
  `applyReveal` is strictly more permissive; that base restriction is a
  game-level prune worth its own row when the predicate lands.
- **K5** (saturated boards: all 7 piles locked-surfaced ⇒ the empty-pile
  gate is pinned shut; every king tableau goal dead): statable once the
  keystone proves the locked-surfaces invariance; hypothesis shape
  `7 ≤ {locked surfaces}.length`.
- **K6** (the four-card ball): K2 + the climb-blocked twin + the
  movability-algebra encoding (§8.1, `free`/`vis` xor form) — statable
  after K1/K2 land; the xor algebra is its own reading task.
- **C12 (forced reveal-commitment)**: needs "reveal-by-stacking" — the
  model's `applyPileStack` never decrements `depths`.  A composite move
  or a `commitApplies` extension is a design decision first (orchestrator).
- **The path-conditioned prunes (method.md 6.2/6.3/6.4, D1–D5)**: the
  model has no history/`ExtraInfo`.  Two candidate encodings — (a)
  existential reshaping ("every win has a witness avoiding …"), proven
  per rule and composable by transitivity; (b) generalize
  `solvableWith`/`cascade_sound` to history-dependent filters
  (`solvableWithHist`).  Design decision pending (orchestrator/user).
- **Parking / destination collapse (macro_parking.md Lemma P)**, the
  full C13 sleep-set layer, C14 fold cut, theorem T's local two-card
  swap: need their own readings (ledger rows in
  `docs/soundness_ledger.md`).

## Wave 13 — the pile-to-pile restriction (B2, scaffolded 2026-09-13)

The engine's license: on dealt-reachable states the full physical game
and the restricted move set agree (`Klondike/Restriction.lean`).  The
naive all-states iff was refuted (EngineWitness; the model's `reveal`
is bare-trigger, the engine's `Reveal` is run-carrying) — the repaired
statements are scoped by the new `initialReachable` predicate.

**Refute-first gate (run before farming the rows)**: replay the
EngineWitness state by an *engine* play from `State.initial wdeal 1`
(`witnesses/EngineWitness.lean`, `wstate`/`wdeal` are in file).  If
reachable, the wave-13 statements fall — escalate (the repair is the
run-carrying-reveal model extension, a design decision below).

| item | file:line | tag | route |
|---|---|---|---|
| `solvableEngine_iff_solvable_of_reachable` (B2 crown) | Restriction:73 | [H] | `cascadeMeasure` well-founded induction; per-move replay is the row below; → is `solvable_of_engine` (proven) |
| `engine_replay_of_pilePile` (the replay step) | Restriction:88 | [H] | case ledger in the file's header: (1) returnable base — proven kits (`stackPile_pileStack_cancel`, `pileStack_comm_*`); (2) locked boundary carry — the B4 crux + rank-mate twin step via `solvable_flipAll` (proven) under the both-heights-equal license, §5.5's pattern; (3) the probe's alarm |

Dependencies: row 2 consumes the B4 crux (Theorems `solvable_of_pileStack`)
— reasonably sequenced AFTER wave 11's crux rows.  The twin-swap
dependency is already discharged (Relabel.lean, axiom-clean).

## Wave 14 — the twin pair at play level (CLOSED; settlement 2026-09-13)

The day's end state: the *seat-swap* direction (state-level twin
exchange as an automorphism/conjugation) was REFUTED three ways —
witnesses/TwinSwapWitness.lean (decide-verified in the Witnesses lib)
records the legality flip.  The correct formulation is the **cargo
transfer** (what sits above the twins — the seat never moves, so no
reveal structure is touched), proven in TwinSwap.lean as
`solvable_cargoTwin_transfer` via the `pilePile` roundtrip +
`solvable_iff_mutuallyReaches`.

Landed and proven: `Card.swapTwin` + kit (involution/color/rank/inj,
`swapTwin_of_ne`, `canSitOn_swapTwin_right/_left`, Basic.lean);
`Base.swapTwin` + `Board.mapByTwin` (Board.lean);
`State.swapTwin`/`Move.swapTwin` + `State.swapTwin_swapTwin`
(involution), `heights_eq_of_redundantStack` +
`redundantTwins_heights_eq` (§5.5's license source), the §1 visibility
machinery (`isVis_antimono`, `pileStack_mem_of_win`,
`isVis_of_apply_pileStack`, `topOf_none_of_apply_pileStack`) — all in
TwinSwap.lean.  The `swapFull`/`swapColorOf` family and the SimTwin/
supermove detours were removed same-day (the refuted branch) per the
laundering rule.

| item | file:line | tag | route |
|---|---|---|---|
| `State.pilePile_return_legal` | TwinSwap:~278 | [M] | the return-request legality: invert the transfer `apply_pilePile_iff`; the `aboveOf` reseat-invariance helper is the kit it needs |

**Design frozen**: the wide-closure and supermove candidates above were
designs for the REFUTED seat-swap direction; the cargo direction needs
neither.  They stay closed pending the transfer row's landing.

## The crux's case ledger (B4 decomposition state)

`solvable_of_pileStack {st} (hwf : st.WF) (hnotlock : st.isLocked c = false)`
— a legal `pileStack` never hurts solvability.  Repairs: `+hwf`
(phantom tenant, witnesses/… B4 archive), `+hnotlock` (locked
stackable strands its boundary — witnesses/B4LockedWitness.lean; this
hole was Dominance's, never propagated to B4 until 2026-09-13).

DONE: the R-half (`solvable_of_pileStack_return`); `pilePile` replay;
commute squares for draw/reveal/deckStack/deckPile.
REMAINING, in order:
1. the 2 squares (`stackPile x b''` with `x.suit ≠ c.suit`;
   `pilePile x b''` with `x ≠ c`) — `deckPile`'s square is the
   template (equality halves already exist in Commutation);
2. the π-induction (delete case trivial, nil vacuous);
3. the park-on-`c` analysis (catch-22: parks are transient — the rung
   card must top; the parked `x` leaves before the rung passes);
4. the excursion pair (`stackPile` of `c`'s suit at the shifted rung);
5. the endgame (return-base crux: deal-adjacent base ⇒ the worry-back
   lands on a rank-mate) — this IS Dominance's N-half; taking it here
   kills two rows.

## REFUTED — archived out of the library

Removed 2026-09-13 (laundering hazard: a `sorry`'d false statement is
citable without warning — FARM_MEMORY:24).  Witnesses in
[witnesses/](witnesses/) are historical; their `*_refuted` corollaries
cite the deleted constants by design.  Any return needs a repaired
statement, a proof, and an orchestrator decision.

1. `solvable_engine_iff` (was Move.lean) — the no-pile-to-pile iff:
   ```
   theorem solvable_engine_iff {st : State} (hwf : st.WF) :
       st.solvableFrom ↔ st.solvableEngine
   ```
   REFUTED: the engine's `Reveal` is run-carrying, the model's demands
   a bare trigger — the concrete move subset is strictly weaker
   (witnesses/EngineWitness.lean; the p2 = [♥3, ♠5, ♥4] deadlock).
   Repair routes: state for *initial* states (B2+B4's content), or
   let `reveal` carry the run.  The easy leg survives as
   `solvable_of_engine` (Move.lean, proven).
2. `toEngine_lifts` (was Bridge.lean) — the draw-1 lift:
   ```
   theorem toEngine_lifts {st : State} {eplay : List EMove} {w : EState}
       (hwf : st.WF) (hstep : st.drawStep = 1)
       (hrun : eRun (toEngine st) eplay w) (hwin : w.isWin = true) :
       st.solvableEngine
   ```
   REFUTED twice (buried base — closed by the Fits repair; then the
   deal-adjacency/canSitOn mirror — witnesses/LiftWitness*.lean): the
   abstraction's arrangement freedom re-seats a card across `Fits`'
   independent seating disjuncts and the model engine game cannot
   follow.  No local guard.  Repair routes: matching-tracking in
   `EState`, a B4 reshape gate, or the initial-states form.
3. `engine_iff` (was Bridge.lean) — the bridge iff: ← is the lift;
   refuted transitively.  The proven → survives as `toEngine_simulates`
   (Bridge.lean).

## Consolidation-3 queue (before wave 11 farming)

Duplication is compounding — canonicalize into Kit/Cycle per the DAG:

- `Cycle.dealN` kit (Macro) vs `Cycle.dealIter` kit (Theorems) —
  near-verbatim, DAG-forced;
- `removeAt_drawTo` ×3 (Move:1881, Commutation:2103, Pace:424) → one
  in Cycle.lean;
- `bottomOf_detach_self` ×3 (Board:202, Move:1007, Bridge:231) → one
  in Board.lean;
- six lemmas verbatim-duplicated Move↔Commutation under different
  names (`applyDrawTo_eq`/`applyDrawTo_shape`, `attach_attach_comm` ×2,
  `findFirstIdx_removeIdx_*` ×4) — both copies patched in lockstep once
  already (toolchain migration);
- the round-2 local kits (Pace-local: `run_mem`, `run_pre_nodup`,
  `run_cards_filter`, `rBelow_append_single`, `count_interval`, …;
  Macro-local 17-helper kit) — promote the Cycle-level ones to
  Kit/Cycle, keep the game-level ones local;
- `Kit.mem_middle_split` = Card-specialized `Kit.mem_split`, one consumer;
- the raw update lambdas — 28 copies of
  `fun s => if s = c.suit then st.heights s + 1 else st.heights s`:
  introduce `bumpHeight`/`dropHeight` named combinators + simp lemmas
  (the highest-value small refactor);
- positional WF construction (9 sites): named constructor lemmas or
  `{ deal_wf := …, … }` dot-notation construction;
- `apply_wf` (~815 lines): the `notMem_removeIdx_self` idiom ×4 —
  extract;
- `Commutation.lean` at 2372 lines: split coarse (compsDisjoint +
  blindness) vs fine (touch + drawTo).

## Chore queue

- `solvable_decidable` (Progress:1166) overclaims: it is the classical
  case split (`solvableFrom ∨ ¬solvableFrom`), not a `Decidable`
  instance — rename (`solvable_em`?) or document.
- Realizability:219/246 lint warnings ("unused simp arg"): **load-
  bearing calls** (terminal `rfl` closers) — do NOT delete; replace
  with explicit closers only with proof in hand.
- `hwf` vestigial in `play_self_is_shuffle` / `solvable_iff_distinctTrace`
  — dropping it from the former is load-bearing for a WF-free cascade
  route; prefer dropping over silencing.
- lean-model/README.md status section: stale (pre-split file list).
- docs/soundness_ledger.md rows A4/B1/B4/G4: model-level proofs landed
  (solvable_relabel; Realizability sorry-free; B4 decomposed with the
  lockedness repair; realizes_iff_stepsOK repaired+proven) — sync the
  tiers.
- witnesses/ → a buildable regression `lean_lib` (`example … := by
  decide` forms, `#guard_msgs` on `#eval`s, `#print axioms` gates) —
  turns archived refutations into tests.

## Design decisions pending (orchestrator/user — do not farm)

- **`applyDrawTo` guard fold-in**: fold `canPlace` into the def
  (simplifies the three compensation sites; wave-9 statements go
  hypothesis-free) vs rename to `applyDrawJumpTo` + document.
- **The Bridge repair route**: EState matching-tracking vs B4 gate vs
  initial-states — needed before any `engine_iff`-style theorem returns.
- **lean-verify/ debris** (untracked, unbuildable): tarball to
  docs/attic or delete; README's last paragraph still cites it.
- **Repo-root clutter**: `a_*.txt` ×5, `fail_*.txt`, logs, notebooks,
  `src/bit_deck_no_bmi2.rs` (orphan Rust in src/) — ignore rules or
  delete.
