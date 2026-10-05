# The proof farm — handoff document

**Census: 12 `:= sorry`** (Theorems 1 · Dominance 4 · Kills 0
· Movability 0 · C2Streamlined 0 · TwinSwapCompletion 2
· Restriction 2 · TwinExchange 1 · TwinQuotient 2; zero bullets;
waves 12/17 base + all four wave-18 sessions + the wave-19 C2
re-scope, 2026-10-05: §8.7 closed
by movability-equivalence; the C2 pillar set refute-probed — FOUR of
the five wave-17 pillars FALSE as stated (C2KingAnchorWitness; the
as-stated c2_two_option among them — the unstackable-at-rung corner
the engine corpus never reaches), in their place the PROVEN
`commitTableau_class` (the destination collapse at the commitment
level, the stackable-rung regime) and the CONDITIONAL
`c2_two_option` with the play-level content as explicit premises; and
the T catchup-residue session's mixed-mid window proven (`solvable_
swapTwin_mixed(_run/_back)`), leaving the two believed-true pins
`mid_access_of_noSeat` + `sweep_covered_corner_safety`); and the
wave-19 C2 re-scope: `hpin`/`hp2` DERIVED for the zero-spend channels
under the root rung (the bound itself premise-free at zero-spend
labelings — `c2_two_option_zeroSpend_rung`) and the raise-ray core
PROVEN (the pacing-guard invariance, F2's deterministic raise, the
corner's derived world, every stack-channel witness's forced
same-suit rank-mate `pileStack`).  Pinned by
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

Work order: the keystone first — K1 consumes it.  (K2 landed
2026-10-05 keystone-tainted: its proof *cites* the keystone as a
premise, so it auto-cleans when the keystone lands — no re-proof.)

**K1 LANDED 2026-10-05 (the k1 farm session, branch
farm/k1-stack-kill)**: the keystone, the frontier spec, and the K1 row
are proven, sorry-free, no WF hypothesis (as planned) — axioms
`[propext, Quot.sound]` for the keystone/frontier/vis steps,
`[propext, Classical.choice, Quot.sound]` for the climb/K1
(the first-passage induction's card-uniqueness split pulls the
choicer).  New machinery shipped with the proofs (all in Kills.lean,
all reusable downstream): the `find?` prefix law
`find?_prefix_false`, the rank split `Rank.all_split_filter`, the
one-step vis laws `vis_of_pileStack`/`vis_of_stackPile`, the play
induction `vis_shadow_play` (the shadow carried explicitly), and the
exported first-passage firing `climb_firstPassage` — K6's
"climb-blocked twin" and any future prefix-conditioned row should
start from these.  Rust deltas found while aligning: none semantic —
the Lean premise `frontier < rank` subsumes the engine's explicit
`h₀ ≥ rank ⟹ no kill` descent guard (descents force
`frontier ≥ h₀ > rank`), and the engine's `locked` mask vs the
model's `isLocked` is the standard bridge-debt noted in §8.7.

| item | file:line | tag | route |
|---|---|---|---|
| `vis_of_safeAccommodates` | Kills:259 | **done**(K1 session 2026-10-05) | `vis_shadow_play` (Kills:130): induction with a *generalized play start*, carrying the foundation-side shadow (`vis` + `onFound` both bounded vs the start); `pileStack`'s new foundation card IS the fired card (root-visible by its guard), `stackPile`'s new visible IS root-foundation (un-stack guard) — safety unused, no WF |
| `State.frontier_spec` | Kills:275 | **done**(K1 session 2026-10-05) | core's `find?_eq_some_iff_append` names the witness + blockedness; minimality via `find?_prefix_false` (Kills:42) over the `filter_append`/`filter_cons` reassembly around `Rank.all_split_filter` (Kills:67, the 13-way decide) |
| `K1_stack_goal_dead` | Kills:501 | **done**(K1 session 2026-10-05) | `climb_firstPassage` (Kills:357): heights past `k` ⟹ the `k`-card was `pileStack`-fired, visible (apply guard) + unlocked (play safety) at the firing state, seat/lockedness root-invariant until then (lockedness lemmas + card-immobility below its rank); the firing contradicts the frontier witness's blockedness both ways |
| `K2_tableau_goal_dead` | Kills:566 | **done**(wave-12 K2 session 2026-10-05) | PROVEN: `Bool.eq_false_or_eq_true` split; the anchor arm king-killed (`king_of_canPlace_inl`, `hking`), the tableau arm via `canPlace_inr_iff` ⇒ `mem_receivers_iff` ⇒ the keystone contradicts `hrecv` both disjuncts (root-vis false: `simp at` the conjunct; the worry-back rank bound: `omega`). Keystone-tainted (`sorryAx` via `vis_of_safeAccommodates`) in the K2 tree — **the wave-12 merge discharges the taint** (K1's keystone proof landed); census **Kills 4 → 0**. §8.1's substrate banked same session in `Klondike/Movability.lean` (see the session note) |

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
  UPDATE 2026-10-05 (K2 session): K2 landed; the §8.1 encoding is
  banked (`Klondike/Movability.lean` — `Card.underPair` IS the
  ball's under-pair, `orVis_of_movableOf` the `or_vis` door,
  `movableOf_flipSuit` the ×0b11 pair property); the remaining K6
  prerequisite is K1's climb-blocked twin fact.
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

**Refute-first gate (run before farming the rows)** — **CLOSED
2026-09-15, the statement stands**: `witnesses/EngineReachProbe.lean`
proves `wstate_not_reachable : ¬ initialReachable wstate` (axioms
`[propext, Classical.choice, Quot.sound]`).  Maintenance covers the FULL
move set, not just engine moves: the witness's pristine mono-suit `p3`
chain can't survive its own digging (the four-way disjunction protects
"fully dug ⇒ chain scarred"; the 1→0 reveal kill-move is disarmed by
the cover-pinning aux: only `wh9` ever covers the still-hidden `wh10`'s
seat, so when it can leave bare, the middle link is already broken).
The initialReachable hypothesis is doing exactly its job; the
run-carrying-reveal repair stays in the drawer.

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
| ~~`State.pilePile_return_legal`~~ | TwinSwap:~300 | **done** (2026-09-13) | the full guard bundle; only the walk-invariance was split out |
| ~~`Board.aboveOf_congr_off`~~ | TwinSwap:~296 | **done** (2026-09-14) | fuel induction via `Board.aboveOf_go_congr_aux` (analytical invariant: acc members + current-call output stay pair-free, so `hagree` covers every probe) on `Board.aboveOf_go_mono` (acc ⊆ output); twin line now sorry-free |

**Design frozen**: the wide-closure and supermove candidates above were
designs for the REFUTED seat-swap direction; the cargo direction needs
neither.  They stay closed pending the transfer row's landing.

## Wave 15 — the twin pair, both-cargo exchange (scaffolded 2026-09-14)

**Claim** (2026-09-14, user): states A (cargo `z` on twin `t`, cargo `z'`
on twin `t'`) and B (cargos exchanged, everything else untouched) are
solvable-equivalent — *without* the exchange being executable (no legal
pilePile can swap both cargos; seats stay put).  This is the engine's
twin-transposition reasoning at the both-occupied shape; the wave-14
theorem (`State.solvable_cargoTwin`) covers exactly the one-bare-twin
boundary case of it.

**Scaffold landed** (Klondike/TwinExchange.lean): the state-transform is
the two-seat VALUE swap — `Board.exchangeTwin` (topOf := bd.topOf ∘
seat-swap; the cargo stacks RIDE, since every card above a cargo root
names its own seat, so only the two root edges change) +
`State.exchangeTwinCargo` (board-only lift), with the kit PROVEN and
axiom-clean: the pointwise characterization, the involutions (board and
state level), the `bottomOf` seat-swap law, and the two transfer
realizations of the exchange (`pilePile_exchangeTwinCargo_fwd`,
`exchangeTwinCargo_pilePile_back` — the detach/attach composite IS the
two-slot swap, both directions, given the bare premise).

**Proof sketch (scheduling argument, user's idea)**: three links.
(1) **Frozen-phase mirroring**: until a twin frees, simulate the play
step-for-step; invariant: states differ only at the two twin seats.
While both seats are occupied no landing can target them (occupied
bases reject), but the run walks DO read them — a walk passing the
CARD `t` continues into the other thread's cargo — so the move
correspondence is structural, not verbatim (a pilePile landing a run
on a cargo top maps to the other cargo's top; `canSitOn_swapTwin`
carries the fit, `aboveOf_congr_off` the walk congruence).  (2) **Bridge
at the first freedom**: the instant a cargo run leaves a twin, both
threads have one occupied + one bare seat — bridge with
`State.solvable_cargoTwin` plus `pilePile_exchangeTwinCargo_fwd`'s
identification of the post-transfer state with the exchange.  (3)
**tails coincide** (even with no freedom ever, the height-writes
mirror, so a terminal win transfers — no "freedom must exist"
premise).

| item | file:line | tag | route |
|---|---|---|---|
| `solvable_cargoTwin_exchange` (both-occupied iff) | TwinExchange:1007 | [H] | **REPAIRED `+hwf` (2026-09-14, session 7) — the gate FIRED on the merge shape**: the premiseless form is REFUTED by the witness at Temp/opencode/w15merge.lean (#eval, re-verified against the real definitions at Temp/opencode/w15mergecheck.lean: a crafted non-WF state — empty deal, heights past visible cards — where the 3-move win goes through the MERGE `pilePile ♥10 (inr ♣J)`, while the exchanged state is FROZEN: its whole reachable space is two states, the second with zero legal moves; the merge self-lands there and every dodge is blocked — the strays sit at foundation-passed ranks, all anchors occupied, the mirror landing blocked by a crafted tenant).  The repair kills the witness via founds_gone/board_edges — the session-6 phantom-stack finding realized; symmetric (the exchange preserves WF: swapped edges legal-seated by twin-blindness) and non-vacuous at every engine state.  Mechanics otherwise COMPLETE (sessions 3-5): the freedom-first bridge; mirror steps for all six non-freedom kinds; `Board.aboveOf_sub_detach` LANDED.  The user's session-7 correction**: t-passing runs landing OFF both cargo stacks mirror fine — the merge is EXACTLY the cargo-stack landing; the step lemma's v2 guard is LANDED (`Board.selfLanding_exchangeTwin_of_off_cargo`, on the walk-bound `Board.aboveOf_exchangeTwin_bound` + the attach-growth law `Board.mem_aboveOf_attach` + the seeded-walk bounds — sessions 6-7).  Remaining: **UPDATE 2026-09-16 — all LANDED**: the h₀/hvis transfers, the WF stack-free derivations (`twinLicensed_attach` on `State.topOf_inr_eq_none`), the v2 wiring, and the assembly itself (the [M] g-simulation `solvable_exchangeTwinCargo_go` — the play induction with the license re-seating at every step, all seven kinds dispatched, the freedom-first bridges at both cargo sides, the seat lock killing `pilePile z`/`pilePile z'` pre-freedom).  The row's sole remaining content: the two merge bridges (`solvable_of_exchange_merge` TwinQuotient:647, `solvable_of_exchange_merge_rooted` TwinQuotient:3080) — normalization or the B&G piecewise bookkeeping; the clean-stacks form below needs neither.  Premise arithmetic: `z' = z.flipSuit` forced; `canSitOn_hosts_are_twins` (LANDED) is the seat lock |
| ~~`solvable_cargoTwin_exchange_of_visClean`~~ (both-occupied iff, clean-stacks) | TwinQuotient:3800 | **done** (2026-09-16) | The reachable-states form — the row's premise bundle **plus `hvc : st.visClean`** gives the iff, PROVEN with no bridge consulted (every reachable state qualifies via `initialReachable_visClean`).  Engine: `solvable_exchangeTwinCargo_go_gen` — the assembly's induction parameterized by (i) the two merge bridges taken with the license OPEN (its eight facts, so the handler's z/z' is syntactically the landing premise's — a bundled `twinLicensed` handler re-binds fresh witnesses and cannot feed the impossibility lemmas) and (ii) a riding invariant `P`; the WF instance re-derives the original `_go` verbatim (`P := fun _ => True`, handlers = the two sorry'd bridges — the WF-level route untouched), the clean instance (`_go_clean`: `P := visClean` via `apply_visClean`) closes both merge corners by contradiction — `merge_impossible_of_visClean` (passing) + the new `merge_rooted_impossible_of_visClean` (Restriction:588 — rooted: the landing fit puts the card one ABOVE the twin, the clean-walk descent pins it strictly BELOW the other cargo).  Backward direction: the involution + `wf_exchangeTwinCargo_of_twinLicensed` + `twinLicensed_exchangeTwinCargo` + the new `visClean_exchangeTwinCargo` (the only swapped edges are the two cargo-on-twin seats, re-fitted by `canSitOn_swapTwin_right`).  Axioms [propext, Classical.choice, Quot.sound] (row) / [propext, Quot.sound] (core); TwinQuotient now imports Restriction |
| ~~`solvable_cargoTwin_exchange_bare`~~ (bare-twin, move-free) | TwinExchange | **done** (2026-09-14) | PROVEN via the *backward* realization (`exchangeTwinCargo_pilePile_back`): from the exchanged state the cargo's pilePile onto its original twin is legal and lands on the original — the exchange is one move from the original, and the win replays through it.  The twin card is never consulted, so the statement was STRENGTHENED: the planned `hzone`/`hwf` premises dropped, phantom twins (stocked/buried/foundationed) covered for free |

**Refute-first gate — HALF-FIRED (2026-09-14, session 7)**: the
**deal-inherited cargo/host adjacency** leg (hfit's premiselessness)
remains unprobed — witness-hunt it separately if the hfit premises are
ever to be weakened.  The **merge-shape leg FIRED**: the premiseless
(no-`hwf`) form is refuted — the witness at
Temp/opencode/w15merge.lean (re-verified at w15mergecheck.lean against
the real definitions): a crafted non-WF both-occupied state where the
win REQUIRES the merge (the t-passing run onto the other cargo's
stack) and the exchanged state is frozen-dead.  The repair `+hwf`
LANDED in the statement; the WF-side merge (reachable states) remains
the sole open question — the normalization or the piecewise
bookkeeping, per the row above.  The companion's direction is settled
in the strong (proven) direction; the reverse `stx → st` at invisible
twins has a candidate stuck shape (see FARM_MEMORY's wave-15 note).

**Session note (2026-09-16, toolchain + the extraction corollary)**:
the model bumped to `leanprover/lean4:v4.34.0` (three `show`
normal-form repairs in Relabel/TwinFrame/TwinAgnostic — v4.34 changed
how `List.contains`/`elem` unfolds relative to the `||` pattern; the
match form is the canonical one now).  **TwinBridge §12.1's named
residue LANDED**: the isWin-side extraction corollary — every tableau
card (board-seated OR hidden-in-pile) meets its own `pileStack` along
a winning play — is now `State.pileStack_mem_of_win_tableau`
(TwinSwap.lean, axiom-clean [propext, Quot.sound]), via the un-hide
step `State.isVis_of_apply_of_not_mem_hidden` (the location-wise
conservation: the deal's pile slices are constants of the motion, the
only `depths` writer is the reveal stepping one boundary down, the
leaving card being exactly the revealed one) plus the win-induction's
hidden side `State.pileStack_mem_of_win_hidden` (the terminal
`founds_gone` forces the exit).  The count form's location half is
now LANDED too (`State.Located` + `State.located_apply`, same session:
every card seated/hidden/stock/founded, the class transferring along
every move — the deck moves splicing the played card, the rank gap
separating `stackPile`'s same-suit bystanders); only the partition
arithmetic (52 = |classes|) remains unformalized — nothing downstream
cites it.
Census: TwinSwap stays 0 (the new lemmas are proven); TwinQuotient
pinned at 2 (the merge bridges — the census entry predating commit
9a40232's file).  Remaining for [H]/[H′]: the three named premises
(`ExchangeRiderPrefix`/`ExchangeDeepNorm` + rooted readings) and the
§12.3 residuals (the deckStack partner-past arm, the worry-back
anti-skews, the schedule existence, the successor's window transfer).

**Session note (2026-09-16, later — the reveal rule REPAIRED to the
physical flip)**: `Move.reveal` is anchor-indexed and legal exactly
when the pile's boundary is bare (commit c5c6904).  The pre-repair
trigger-card rule admitted unphysical covered flips AND starved
exposed boundaries — the dead-pile pathology (the B4/Dominance
hnotlock guards' original motivation) was an artifact of it, retired
with the witnesses reframed historical (the accommodation successor
now REVIVES: `[reveal a, pileStack r]` — `wState1_solvable` pinned at
both witnesses).  **The fresh B4 question**: whether the `hnotlock`
premise can be dropped — the locked successor's boundary is now a
normal visible top after the flip, so the stranding corner is gone;
but the crux's remaining content (`rungNormal_or_forcedPark`'s
normal-form characterization — the (B, L) descent, the (c-α)/(c-β)
sub-gaps) is unchanged by the repair.  The reveal-dependent machinery
survived: `apply_wf`, the mirror steps, the license transfers, the
extraction family — all re-verified under the new rule (build green,
census pinned at 14, unchanged).

**Session note (2026-09-16, evening — the file split)**: two new
iteration-homes in `lean-model/Klondike/`:
`MergeFire.lean` (importing TwinBridge — the merge's re-firing
family: `merge_refires_clean` MOVED here from TwinBridge, with
`merge_refires_mixed` the incoming next piece; the walk-entry kit it
consumes — `RunChain`, `aboveOf_run_root_of_chain`,
`aboveOf_card_base` — lives in TwinQuotient's walk family) and the
user's `TwinCollapse.lean` (the anchor-relocation kit).  Both wired
into `Klondike.lean`'s import list (TwinCollapse was an orphan
module before).  The iteration economics: a MergeFire check is ~3s
vs ~4.2s for the TwinBridge re-elaboration — and, more importantly,
the small files isolate concurrent red states (a broken TwinExchange
no longer blocks MergeFire's compilation — the pattern the user's
"green under v4.34 while TwinExchange was red" already exhibited).
RECOVERY NOTE: the split surgery collided with concurrent edits and
briefly zeroed TwinBridge.lean — restored from git (the only
uncommitted delta was the trim itself), the stub olean (1.4KB,
timestamped before its own dependencies — the
building-through-breakage artifact) deleted, full clean rebuild green
(60 jobs both libs), census pinned at 14.  LESSON: after any
`lake clean` under concurrent edits, verify the olean sizes — a
KB-sized olean for a K-line file means lake skipped a phantom
"fresh" stub.

**Follow-up (same evening — `merge_refires_mixed` LANDED)**:
`State.merge_refires_mixed` (MergeFire.lean, axiom-clean
[propext, Quot.sound], the first theorem in the file's own home) —
the firing-half derivation for the FULL mixed schedule
(`exchangeDoubleClear_of_sched_mixed`'s shape): a firing merge
re-fires after a CleanStack prefix + the z'-detour, under the
schedule-natural premises (`hβcard`: the detour's landing card off
the merge root's walk and off the detoured run at the source;
`hself`: the detour not landing at its own root's seat; `hβne`:
the two landings distinct; `hchain`/`hride`: the detoured run as a
chain with the merge's landing riding it; `hc₀`: the merge root off
the run at the end state).  The contains-guard is the walk-entry
assembly: `mem_aboveOf_attach` decomposes, the riding case forces
the run root in (`aboveOf_run_root_of_chain`), whose seat is the
detour's landing (`aboveOf_card_base_of_mem` + board injectivity),
whose pred re-enters the attach-decomposition and dies by `hβcard`
on all three branches.  The mixed consumers' re-firing premise now
reduces to the source firing + the schedule's own shape premises;
the successor's window-solvability (L1/O0) is the sole remaining
half.

**Session note (2026-09-16, night — the fusion point MAPPED, the
hybrid ladder's floor BANKED)**: `solvable_cargoTwin_exchange` at
visClean is DONE (the user's `go_clean` + the impossibility — banked
unconditionally).  The pure-WF statement's remaining content is
exactly the two merge bridges, and the collapse lane's front half is
proven: the trichotomy skeleton (`merge_ply_cases` +
`mirror_fires_of_bare` + `blocker_leaves_mirror` +
`dislodge_reland`/`park_reland` + `mirror_of_bare_rung`), the
discipline chain (`unseats_imp_pileStack` — the only unseating move
is the card's own pileStack; `same_suit_no_stack` + `founded_not_in_aboveOf`
+ the §12.1 extraction = the same-suit cascade arm: the twin MUST
dislodge on any winning line), and `merge_rank_arith`.  **The
fusion point** — where the collapse lane meets the window lane —
needs exactly two glue lemmas, both now sharp:

1. **THE CORRESPONDENCE AT THE AFTERMATH**: `twinCorr_of_ply`
   (TwinBridge) builds `TwinCorr (swapTwin z) z.suit S M` from the
   board-conjugation data (`M.board = S.board.mapByTwin z`,
   deal/heights/depths/stock equal, both cargos visible).  The
   collapse aftermaths give exactly that data shape —
   `dislodge_reland`/`mirror_fires_of_bare` conclude `s₂.board.topOf
   (Sum.inr z') = some c ∧ topOf (Sum.inr d) = none ∧ heights/stock/
   depths preserved` — so the glue is: the aftermath `s₂` equals
   `a₁.mapByTwin`-shape for the source's merge successor `a₁` (the
   seat-level matching of the composite's conclusion against
   `mapByTwin`'s pointwise action), then `twinCorr_of_ply` applies
   verbatim.  `blocker_leaves_mirror`'s height bump (the blocker's
   rung) is the wrinkle: the correspondence's `M.heights = S.heights`
   clause needs the heights difference absorbed — either by running
   the correspondence at the pre-stack state (the §5 growth
   precedent: the first pair-stack inside the window), or the
   TwinCorrX strand form.

2. **L1/O0 AT THE AFTERMATH**: the source's `a₁` is plain-solvable
   (the handler's premise); the climb-out needs
   `solvableWindow'`.  The aftermath-shape question: at the merged
   configuration (c on z', the pair colocated), does the head's
   equalization come cheap?  The landed tail classes
   (`TailClimbClean` with both climb sources,
   `playWindow'_of_rescheduled`, `append_nostack`) cover the
   post-equalization tail; the head is the open half, and the
   trichotomy's forcing may present it well-shaped (the blocker's
   stack = the first pair-rung climb, already played).

The lane split at the fusion: the collapse lane composites the
discipline chain into the forcing theorem; the window lane derives
the correspondence + assesses the aftermath head.  Both glue lemmas
live in MergeFire (the correspondence) and TwinReplay (the window
premises) — no file collisions.

**Session note (2026-09-16, close — the column composition LANDED)**:
`State.exchangeDoubleClear_of_columns` (TwinBridge §12.3, axiom-clean
[propext, Quot.sound]) closes the gap between `both_columns_clear`
(the two FIRING rider-runs — the schedule's structural skeleton) and
`ExchangeDoubleClear` itself: the concatenated column-run is
CleanStack by the protection (the mirror's verbatim replay DERIVED via
the run-level replay lemma), and the both-bare end state plus the
merge's re-firing with a window-solvable successor close the premise.
The [H]/[H′] chain now reads: winning play → (the extraction residue:
the FIRING column-runs + the successor's window-solvability — the
raiser adjacency, the covers-on-riders constructed detour, the L1/O0
transfer) → `exchangeDoubleClear_of_columns` → `ExchangeDoubleClear` →
`solvable_of_exchange_merge_rooted_direct` → the merge bridge → the
licensed iff assembly.

**Session note (2026-09-16, the window's deckStack partner-past arm
GROWN)**: `playWindow'`'s pre-episode `deckStack` arm gained the
ρ-fixed ∧ partner-past third disjunct (`TwinReplay`), with the
strengthened window's replay case added (the stock-sourced
post-equalization climb translates via
`TwinCore.rung_eq_of_partner_past` + `TwinCorrX.apply_deckStack_onsuit`
— both pre-existing) and the one downstream admission proof
(`playWindow'_tail_of_eq_heights`'s off-pair deckStack) adapted; the
sufficiency family (65 admission-proving uses) unaffected.  Axiom-clean
[propext, Quot.sound]; census pinned at 14.  This closes §12.3's
audit residue (a) — the stock-sourced on-pair climbs no longer need
the skew/alternation once the partner rung is past the pair rank.  The
window's remaining declared obstruction is (b) alone: the `stackPile`
arm's pair-member and just-below-pair worry-back anti-skews.

**Follow-up (same day): the alternation-kill's tail class EXTENDED** —
`State.TailClimbClean` now admits the ρ-fixed on-pair `deckStack`s
too (the stock-sourced climbs), and `playWindow'_tail_of_equalized`
carries the case (the partner-past derivation mirroring the stack
case's, minus the routing — the deckStack arm always stays `.pre`).
Post-equalization, a run of height-blind moves plus ρ-fixed on-pair
climbs of EITHER source (tableau or stock) admits verbatim — the
co-climb alternation is dead for both.  Axiom-clean
[propext, Quot.sound]; census pinned at 14.

**Follow-up (the merge's re-firing DERIVED)**:
`State.merge_refires_clean` (TwinBridge, axiom-clean
[propext, Quot.sound]) — a firing merge re-fires at the end of a
CleanStack column-run whose stacked cards stay off the merge's
touch-set (the root `c`, and the landing base's card `d`): the run is
detach-only, so the root's base, the landing base's freeness, and the
landing card's visibility are carried verbatim, and the run-walk only
shrinks (`aboveOf_shrink_run`).  This derives the FIRING half of the
double-clear schedule's re-firing premise
(`exchangeDoubleClear_of_columns`'s `hmerge`); the WINDOW half (the
successor's `solvableWindow'`) is the L1/O0 residue, now the sole
remaining content of that premise.  NOTE the honest boundary: the
landing-survival premise (`d` not among the run's stacked cards) is
exactly the geometry where the landing card is not itself a cleared
rider — the deep-landing corners (the landing ON a cleared z'-rider)
need the route's other machinery, and the schedule's consumer-side
analysis of which landings satisfy it is the next session's map-work.

**Follow-up (the landing geometry MAPPED — the schedule's shape
constraint)**: `State.rooted_merge_landing` (TwinBridge, axiom-clean)
— with `z` fit-seated on `t`, any card hosting `t` (the rooted
merge's landing) sits exactly TWO ranks above `z`, in `z`'s color, and
is NEVER one of the four protected cards (the rank arithmetic
excludes the twins and the cargos outright).  **The consequence**:
at the `[H]/[H′]` `hland` shapes the landing is a strict z'-column
member — so the CLEANSTACK-ONLY double-clear schedule CANNOT serve
the merge bridges: both columns clear (the both-bare premise), the
landing is among the cleared, and the re-firing on its seat dies.
The honest schedule is MIXED: CleanStack clearings for the column
bulk PLUS pilePile re-homing for the landing card itself (detaching
it off the column to a surviving seat — visible and bare — before
the merge re-fires there; §13's "re-route, not commute" made
concrete).  The mixed-run mirror replay exists in pieces (the
CleanAt run-replay, `exchangeTwinCargo_step_pilePile`), and
`merge_refires_clean` serves the CleanStack segments; the re-homing
existence (the landing's new seat, via the clean-stacks theorem's
candidate analysis) is the next session's construction.

**Follow-up (the mixed schedule's firing-half — the design mapped)**:
`merge_refires_mixed` (not yet landed) would derive the re-firing
half of `exchangeDoubleClear_of_sched_mixed`'s `hstep` premise from
the source firing, completing `merge_refires_clean`'s premise
reduction to the window side for the FULL mixed schedule.  The
design: (i) the CleanStack segment's guards-transfer is
`merge_refires_clean` verbatim; (ii) the DETOUR segment's transfer —
the root's base via `State.apply_pilePile_bottomOf` (r₁ ≠ c), the
landing base's freeness via the attach/detach `topOf_ne` pair (the
firing's b₀ ≠ b automatic: topOf b₀ = some r₁ ≠ none), the landing
card's visibility via `apply_pilePile_bottomOf` (r₁ ≠ d) or the
root-reseating (d = r₁: the new base β is some); (iii) the
contains-guard `d ∉ aboveOf c` needs the walk-ENTRY fact —
`mem_aboveOf_attach` is too coarse (its third disjunct covers the
whole moved run regardless of connection) — the sharp form: every
S₀-path from c uses the new attach edge (else it exists in Sₛ), so
the β-card is on the c-walk, contra the premise — formalizable via
the `aboveOf_pred`-family's walk induction (TwinQuotient's
pred-reaches pair).  With (i)-(iii), the mixed consumers' `hstep`
reduces to the source firing + the schedule's own premises.

**Follow-up (the admission-composition kit)**:
`State.playWindow'_append_nostack` (TwinBridge, axiom-clean
[propext, Quot.sound]) — the pre-episode admission composes over a
routing-free prefix: a segment with no `pileStack` (only a stack's
failed-skew pair card routes to the mid-episode; the six other kinds'
pre-arms stay `.pre` unconditionally), itself pre-admitted and
running `S → S₀`, extends any pre-admitted tail at `S₀`.  This is the
L1/O0 transfer's assembly tool: the successor's admission will be
built as [raiser head (deckStacks, no stackings) + the rescheduled
body + the equalized tail], each piece admitted separately and glued
by this lemma — the head's own admission (the pre-equalization skew
arms) and the tail's worry-backs (residue (b)) stay the residue, but
the gluing is now mechanical.

Sequenced after the live cruxes (waves 11–13 remnants: B4/Kills B2
etc.).  **Dependency note**: W4's reformulation (the W-repair at the
crux ledger) already absorbs park cases via the swap — whether it needs
the both-cargo shape or only the bare-twin one should be settled before
farming this wave.

## Wave 16 — the twin mirror: all moves twin-agnostic except the foundation moves (LANDED 2026-09-14, sorry-free)

**Claim** (the alternative route to T, by move-level decomposition): the
local twin exchange `State.swapTwin t` conjugates every CLEAN move —
clean = not a foundation move of a pair member (`Move.cleanTwin`): the
three foundation kinds (`pileStack`/`deckStack`/`stackPile`) read
`heights`, which the swap fixes, so they cross to the OTHER suit's
count exactly when the moved card is `t`/`t.flipSuit`
(TwinSwapWitness's refutation shape); NOTHING tableau-side is an
exception (`draw`/`reveal`/`deckPile`/`pilePile` — `canSitOn` is
color-blind, the run walk reads relabeled seats, the deal/depths views
map along).

**Landed** (Klondike/TwinAgnostic.lean, imports only the Relabel chain
— below the Theorems breakage — axiom-clean
`[propext, Quot.sound]`, census 0):

- `apply_swapTwin_clean` — the mirror lemma:
  `(st.swapTwin t).apply (m.swapTwin t) = (st.apply m).map (State.swapTwin t)`
  for clean `m`, unconditional in the state (no WF, no height
  alignment); the none-direction rides the involution (the mirror of a
  clean mirror is the source), so only the some-direction is
  constructed.  Play form: `run_swapTwin_clean`.
- `run_swapTwin_pair` + `solvable_swapTwin_paired`/`_back` — **the
  licensed pair**: where the winning play's twin foundation moves are
  ONE adjacent pair `[pileStack t, pileStack t.flipSuit]` (the aligned
  shape — both stackable at the same moment, §5.5's redundant pair
  supplies it in the engine), the exchange preserves solvability both
  directions.  The alignment is DERIVED, not premises: the pair firing
  pins both suits' heights to the shared rank; after the pair the
  heights re-sync (each suit gained its twin's rank once in both), so
  the tail mirrors verbatim — no skew survives the back-to-back shape.
- The `mapByTwin` transfer kit (topOf/bottomOf/attach/detach/aboveOf,
  the twin-seat probes `mapByTwin_topOf_flip(_Suit)`/
  `mapByTwin_bottomOf_flip(_Suit)`, the cycle laws `twinCycle_*`, the
  composed guards) — the local-swap analogue of Relabel's `relabelBy`
  kit, consumable by the window argument.

**Substrate relocation (same day)**: `Move.swapTwin`/`State.swapTwin`/
`State.swapTwin_swapTwin` moved TwinSwap → Relabel (the relabeling
group's canonical home), `Card.swapTwin_flipSuit`/`Base.swapTwin_flipSuit`
moved TwinExchange → Relabel (plus the new `Move.swapTwin_flipSuit`/
`State.swapTwin_flipSuit`) — names and proofs unchanged, TwinAgnostic
sits below the Theorems chain and needs the substrate.

**What remains open** — T's general window (this wave's residue, and
wave 15 [H]'s sibling): when the twin stacks are NOT adjacent, the
source play interleaves its same-color catch-up between them, and the
mirrored game cannot copy it verbatim — the ±1 height skew on the twin
suits blocks the s1-cascade in the mirror and vice versa (the successor
correspondence after ONE twin stack is `State.twinSkew`, board-swapped
with the one suit bumped — exactly the divergence the pair re-sync
cancels).  The bridge — reorderings plus reveal-relocations of the
stuck twin — is the interleaving lemma (L1/O3) of
macro_formalization §3; the mirror lemma is its mechanical half,
isolated so the window argument consumes it.  Candidate normalization
before farming: "winning plays can be reshaped so the twin stacks are
adjacent" (false in general — the catch-up needs the structure unlocked
by the FIRST stack, e.g. the empty-pile/king chain; the refute-first
shape is exactly that deadlock).



## The crux's case ledger (B4 decomposition state)

**ROUTE (2026-09-14): [ENDGAME.md](ENDGAME.md)** — the reading pass
over B&G + no_pile §5 + the landed kit.  The normal form is
`rungNormal` (before the first, forced `pileStack c` — the rung pass —
no move parks on `c`, no c-suit worry-back); the measure is
lexicographic (blocked-moves-before-rung, play length); the work order
is W1 (landed 2026-09-14) → W2 (landed, `≤`-repaired) → W3 (adjacent
landed; spread blocked on the frame theory) → W4.  **REFORMULATION
DECISION (2026-09-14, user): the staged crux is FALSE at the forced-park
shape — known, no refutation witness needed.  The repair is NOT a
guard (`+hsafe`/`initialReachable` deprioritized): W4 is reformulated
to rely on the twin swap — canonicalize via the proven automorphism
(`swapTwin`, TwinSwap.lean) + `solvable_cargoTwin_transfer`, so the
park/pilePile-shaped cases are absorbed by the swap rather than
case-split.  **PICKED 2026-09-14: (c) + hybrid** — the certificate form
`s₁.solvableFrom ∨ st.forcedPark c` (added conclusion, no guards) +
`rungNormal_or_forcedPark`, with TwinExchange's rows as lemma-0 (the
user's in-flight Klondike/TwinExchange.lean; contracts R1–R4 in
ENDGAME §8).  Propagation: the disjunct reaches
`solvable_of_accomm_step`.**

`solvable_of_pileStack {st} (hwf : st.WF) (hnotlock : st.isLocked c = false)`
— a legal `pileStack` never hurts solvability.  Repairs: `+hwf`
(phantom tenant, witnesses/… B4 archive), `+hnotlock` (locked
stackable strands its boundary — witnesses/B4LockedWitness.lean; this
hole was Dominance's, never propagated to B4 until 2026-09-13).

DONE: the R-half (`solvable_of_pileStack_return`); `pilePile` replay;
all commute squares (incl. `pileStack_comm_pileStack`, which the
original plan missed); the seven step dispatch lemmas
(`solvable_of_pileStack_step_*`) + `reveal_notLocked`.
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

Removed 2026-10-05 (wave-18, the C2-closure session; same laundering
hazard).  All four cite ONE witness —
[witnesses/C2KingAnchorWitness.lean](witnesses/C2KingAnchorWitness.lean):
a pristine WF state (empty board, all foundations 0, standard deal,
the four kings + clubs + high diamonds as the spade-blocked stock)
where `♠K` commits to SEVEN pairwise closure-separated anchor
landings (no pileStack of the landed king can ever fire — spade
height is frozen at 0; no accommodation move ever unseats it).  The
negated as-stated spellings live in the witness as
`wk_c2_as_stated_false`, `wk_same_pin_as_stated_false`,
`wk_p2_direct_as_stated_false`, `wk_crease_as_stated_false`
(axiom-clean, no sorry):

4. `succ_labeled` (was C2Streamlined.lean, wave-17's P0) — every
   macro successor labeled by a channel live-at-root.  REFUTED: the
   channel list misses the anchored-head unseating (a seated pile
   head leaves by its rung-dig, the king lands on the vacated anchor
   — hole-shaped at the end state, dead at the root, no free anchor
   there).  Repair routes: add the king-anchor channel to `Label`
   (a generator change; orchestrator scope), or guard the statement
   to king-free/root-live states.  Analytic countermodel; witness
   pending (the king-anchor witness above covers the other four —
   this fifth poles as the next ticket).
5. `p2_direct_class` / `same_pin_closureEq` / `crease_chain_absorbed`
   (was C2Streamlined.lean, wave-17's P2/P3/crease) and with them
   the as-stated `c2_two_option` — every tableau-arm successor of
   the same stocked card asked to join ONE closure class.  REFUTED:
   an unstackable-at-its-rung target can never leave its landed
   seat (only `pileStack` unseats a card), so two landings are
   genuinely closure-split — no local guard on the witnesses'
   hypotheses fixes it short of the rung premise.  Repair routes:
   the rung premise `X.rank.toIdx = st.heights X.suit` on the
   class-join claims — exactly the regime PROVEN in
   `commitTableau_class` (C2Streamlined §9.5: the destination
   collapse at the commitment level, the two-move foundation
   shuttle, axiom-clean) — plus, for `succ_labeled`-labeled plays,
   the free-float residue work still open; `stack_ball_corner`
   (the fifth pillar) was never refuted and survives as the `hball`
   premise of the repaired conditional `c2_two_option`.

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

## Refactor Phase 0 — the friction-cleanup scope (core-only)

**Decision (2026-09-14, user): core Lean 4 only — mathlib declined
(bulk), batteries/std4 also declined (purity-as-a-value).  All
ergonomics work below is therefore encapsulation + simp-normal-form +
small macros, nothing external.**

### R1 — `aboveOf` encapsulation (the walk API)

Consumers must never name `fuel` again.  At Board.lean level:

- prove the kit once: `aboveOf_step` (one-step equation), `aboveOf_nodup`
  (the contains-guard preserves `List.Nodup`) — the ≤52-distinct-cards
  argument: raw boards never fuel-truncate; keep `c ∈ aboveOf c` as the
  *cycle marker* (true exactly on loop junk — pair it with the parked
  `board_acyclic` row so WF-consumers later get `c ∉` for free);
- re-home `aboveOf_go_succ` (Relabel.lean) into Board.lean as part of
  the kit; consumer sweep: GREP all `aboveOf.go`/`go_succ` uses outside
  Board.lean (Relabel, Theorems' replay, TwinSwap's two aux) and port
  onto the kit.  Make `Board.aboveOf.go` `private` on landing.
- acceptance: no `aboveOf.go` token outside Board.lean; census
  unchanged; crowns' `#print axioms` unchanged.

### R2 — guard normal form (`@[guard]` simp set)

One `Klondike/Guardnorm.lean`: canonical `= true`-level characterization
lemmas for `State.legal`, `State.canPlace`, `State.canMoveRun`,
`State.isRedundantStack` — statement shape rewrite directly into the
Bool conjunction (avoid the bare-decide intermediate that bit the
canMoveRun harvest, FARM_MEMORY 2026-09-14).  Sweep the ~40
`Bool.and_eq_true_iff.mp` decompositions in apply_wf/TwinSwap/
Dominance/Kills/Commutation/Theorems onto the set.
- acceptance: build green; `Bool.and_eq_true`-token count in proof
  bodies drops ≥ half; crowns' axioms unchanged.

### R3 — the two macros (`Klondike/Tactics.lean`, new)

- `run_step h h₁`: the `State.run` cons-propagation dance
  (`simp only [State.run]` + apply-case + `Option.some.inj` + `rfl`),
  currently pasted verbatim twice inside `solvable_cargoTwin_transfer`
  alone.
- `move_cases h`: destruct `h : st.apply m = some st'` — dispatch
  `cases m`, apply the right `apply_*_iff`, obtain-destructure with
  generic names.
- acceptance: ≥5 real call sites converted; theorems' statements and
  axioms byte-identical.

### Land-rules for R1–R3

One item per commit; `lean-census.ps1` stays pinned; Witnesses lib
green; `#print axioms` snapshot over the crown set
(`solvableEngine_iff_macro`, `solvable_cargoTwin`,
`solvable_cargoTwin_exchange_bare`, `realizes_iff_stepsOK`) recorded in
the commit message before/after.  Honest sizing: R1 ~[M], R2 ~[S],
R3 ~[S]; R1's kit proofs are the only non-mechanical part (the
congruence template already exists in TwinSwap).  Sequenced in dead
time alongside the cruxes; NOT ahead of them.

### Parked beyond Phase 0 (trigger-gated)

- Phase 1: move-kind file split (Theorems 3945 proof-lines; Commutation
  2135) — trigger: one more parallel-session build collision.
- Phase 2: Frame discipline generalized to board-slot frames (kills
  future `aboveOf_congr_off`-shaped one-offs) — trigger: the wave-15
  bisimulation actually farming.

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

- **SETTLED 2026-09-14 — batteries/std4: stay core-only.** The
  hand-rolled List/Option kit is battle-tested and consolidated;
  switching mid-endgame churns for marginal gain. Revisit only
  post-endgame, with a concrete duplication count.
- **Ops note**: intermittent `.olean.private` read failures under
  concurrent sessions are AV-weather (files verified healthy) —
  recommended fix: real-time-scan exclusion for the elan toolchain
  dir and the repo. Until then: retry (the polling protocol).
- **`applyDrawTo` guard fold-in**: fold `canPlace` into the def
  (simplifies the three compensation sites; wave-9 statements go
  hypothesis-free) vs rename to `applyDrawJumpTo` + document.
- **The Bridge repair route**: EState matching-tracking vs B4 gate vs
  initial-states — needed before any `engine_iff`-style theorem returns.
- **Repo-root clutter**: `a_*.txt` ×5, `fail_*.txt`, logs, notebooks,
  `src/bit_deck_no_bmi2.rs` (orphan Rust in src/) — ignore rules or
  delete. (lean-verify/ was deleted 2026-09-13 — row closed.)

## Session note (2026-10-05 — wave-12's K2 lands; §8.1's Movability substrate banked)

- **`K2_tableau_goal_dead` PROVEN** (Kills.lean, the staged [E] route
  verbatim): `Bool.eq_false_or_eq_true` split; the anchor arm
  king-killed, the tableau arm via `canPlace_inr_iff` +
  `Card.mem_receivers_iff`, the shared keystone
  `vis_of_safeAccommodates` contradicting the death conjuncts both
  ways (`simp at hvis0` on root-visibility; `omega` on the
  worry-back rank bound `heights ≤ rank` vs `< heights`).  Axioms
  `[propext, sorryAx, Quot.sound]` — the `sorryAx` arrives ONLY
  through the keystone (the sibling session's row), so K2's own
  census marker is gone (Kills 4 → 3) and it auto-cleans at
  keystone-landing.
- **`Klondike/Movability.lean` NEW** (§8.1 / ledger C15's substrate,
  the K6 bullet's "movability-algebra encoding"): `Card.underPair`
  (the Option-shaped twin pair one rank below, opposite color — the
  engine's `reduce_rank_swap_color`/`swap_suit` pair members, order
  included), the sitter recognition `canSitOn_iff_underPair`,
  §8.1's formula as the DEFINITION (`Card.movableOf` on raw
  vis/locked functions; `State.free = vis ∧ ¬locked`, the
  `State.movable` wrapper), `orVis_of_movableOf` (the `or_vis` door —
  K2's §8.5 receiver premise), `movableOf_ace` (aces movable whenever
  the type-pair is visible), `movableOf_flipSuit` (the ×0b11
  type-pair property via `underPair_flipSuit_of_pred` +
  `movable_pair_symm`), and the engine mask transcription
  (`Suit.code`/`Card.maskIndex` — the rank-parity-interleaved layout
  of src/card.rs; `Mask.maskOf`/`shr1`/`shl4`/`alt`/`spread`/
  `bottomMask` — `bottom_mask_of` on little-endian position words).
  Everything listed is PROVEN, axiom-clean [propext, Quot.sound]
  (`movableOf_flipSuit`/`State.movable`: [propext]); registered in
  the umbrella after `Klondike.State`.
- **The §8.7 owed equivalence STATED, not claimed**:
  `Mask.bottomMask_matches_movableOf` — the sole new sorry (census
  +1), one-paragraph decode plan in its docstring (maskIndex
  bijection + the `± 4` under-pair reads + the ace underflow + the
  16-case Bool exhaustion; no u64 truncation event below 52+4 < 64).
  The Rust side stays bound by `bm_algebra_matches`.
- **Substrate relocation**: `Color.flip`, `color_ne_flip`,
  `Rank.pred`, `rank_pred_iff` moved Realizability → Basic.lean
  (verbatim, pointer notes both sides — the wave-14 relocation
  pattern; Movability needs them upstream of State).  Realizability
  unchanged otherwise, build green.
- **Census discipline**: baseline updated (Kills 3, Movability 1,
  total 14, pinned OK).  LEGAL TRAP recorded: the census greps the
  literal `:= sorry` text — do not write that string inside
  doc-comments/prose (the K2 taint note tripped it before rewording).
- **Next tickets**: (1) the keystone (sibling, in flight) — K2
  auto-cleans; (2) `Mask.bottomMask_matches_movableOf` [M];
  (3) `frontier_spec` (K1's premise) then K1 — which also unblocks
  K6's climb-blocked-twin fact (the four-card ball is otherwise
  banked); (4) the doc-side alignment note below lands in
  macro_formalization.md §8.8 (append-only keep-§8.7-caveat).
## 2026-10-05 SESSION — Theorem T's O1/O3 slice LANDED (wave 17)

MISSION: T's open O1 (locality) + O3 (the asymmetric boundary) + the
§6.5 canonicalization corollary, in a fresh worktree branched at
macro-game HEAD (the spawned branch sat at pre-macro dc41b8e —
ff-only merge first, nothing unique lost).  T's status at entry:
the global relabeling form PROVEN (`solvable_relabel`/`_flipAll`,
Tier [P]); the local pair exchange licensed — adjacent
(`solvable_swapTwin_paired`/`_back`) and ortho-separated
(`solvable_swapTwin_separated`/`_back`) PROVEN; the [H] both-occupied
iff at visClean PROVEN; the seat-swap itself REFUTED; L1/O3's residue
(ii) — twin-suit activity BETWEEN the stackings — open.

LANDED — all NEW in `Klondike/TwinSwapCompletion.lean` (registered in
the umbrella; sorry-free; census 14 PINNED; axiom-clean
[propext, Quot.sound] per `#print axioms`):

- **O1, destination collapse (resolved minimal form)** —
  `State.solvable_twinDestination_collapse`: at WF, twin-destination
  `deckPile` landings of one drawn card (`inr Y` vs `inr Y.flipSuit`)
  are solvability-equivalent — one `pilePile` transfer each way with
  the landing closing EXACTLY (the vacated seat's `attach ∘ detach =
  id`, new helper `Board.attach_detach_cancel`); the WF premise kills
  the phantom-stack leg (`State.topOf_inr_eq_none` + new
  `Cycle.prev_mem`/`State.stock_prev_not_mem_hidden`).  §4's
  observation CONFIRMED: C2's collapse needs NO cross-pile swap.
- **O3, the pure catch-up window** — `State.solvable_swapTwin_catchup`
  (+ `_run` packaging): f(t.suit) = r but f(t̄.suit) < r — one twin
  stackable now, the other not — the low suit raised between the two
  stackings by a pure exact-rung prefix `cu`.  Engine: new
  `apply_pileStack_pileStack_exchange` (off-suit `pileStack`s
  commute; every guard transfer is derived from the two firings — no
  case split) + `pileStack_catchup_reorder` (the window's cornerstone:
  the catch-up segment commutes with the twin's firing, the reordered
  landing EXACTLY the source's mid successor), then the
  twinSkew/crossTwin spine re-used with the re-aligned rung
  (`halign₁` from the catch-up's reach).  `haccess` = the per-card
  accessibility license (the catch-up runnable at the pre-firing
  state) — "subject to per-card accessibility" made formal.
- **§6.5 instance** — `twin_stack_order_exchange_catchup`: the
  SAME-STATE order exchange: a win via [prefix; stack H; cu; stack L;
  tail] reshapes into [prefix; cu; stack L; stack H; tail] landing on
  the SAME successor — the sweep's lowest-first canonicalization
  never uniquely loses wins at this window.
- **witnesses/TwinCompletionWitness.lean** (decide-anchored,
  axiom-clean): BOTH licenses machine-checked necessary — (A) a
  catch-up card dealt under the twin (window play fires, reorder
  blocked: the `haccess` premise is real); (B) the covered-twin corner
  (mate seated on the twin: the L-first firing blocked at equal
  rungs — §6.5's "one covered" residue is real).

NEXT (tickets, in order):
1. L1/O3(ii) general window: mids MIXING ortho moves with the catch-up
   — the obstruction is an ortho landing onto the vacated twin seat
   (same shape as witness B); needs either a no-landing premise or the
   W15-style exchange (canonicalize the landing's read).
2. Twin-suit worry-backs in the window; the `haccess` DERIVATION at
   engine corpora (reached states' board discipline).
3. The catch-up iff (the `_back` form needs the catch-up-first→between
   DEFERRAL — L1(ii) again on the mirror side).
4. §6.5 residue: the covered-twin corner's sweep-word safety (reduce
   to the both-occupied exchange family at the covered seat).
## Wave 17 — C2-streamlined: §7's two-option commitment scaffold
(scaffolded 2026-10-05, the C2-streamlined farm session)

`docs/macro_formalization.md` §7, model side — the campaign's central
theorem as a poset-counting argument.  **Land**: `Klondike/C2Streamlined.lean`
(registered in Klondike.lean), building on the C2-model seed (Macro.lean's
`applyDrawTo` line), §6.2's locality (`Card.only_blocker_is_twin`,
reused, not duplicated — its argument order is *coverer-first*: see
`coverer_fitted_twin`), and the destination/seat kit
(`canPlace_inr_iff`/`topOf_of_canPlace`/`canSitOn_of_canPlace_inr`,
Move.lean).  The engine anchor (`macro_game.rs` channels `core_run`,
`closure_classes`/`closure_contains`, `collapse_pick`; the 16,791-row
histogram `[_, 16777, 14, 0, 0]`) was read for definition alignment
only; `src/` untouched.

**PROVEN (axiom-clean, the small core)**:

- the two-type ball: `receivers_twin_pair` (F1/§6.2 "never a third
  suit"), `receivers_king_nil`;
- **P1 in full**: `founded_not_covered` (a foundation-passed card sits
  under nothing — `board_edges`' base-clauses ∨ `founds_gone`), the
  twin `founded_unseated`, and `p1_bothBorrows_noDig` (both borrows
  live kill the dig — §6.7's exclusion `borrowable: 2 ⟹ dig: false`);
- §6.2's in-flight half for stocked targets: `coverer_is_twin
  fitted_twin` + `coverer_is_twin_of_stocked`;
- the one-step channel semantics `digOpens`/`borrowOpens` (the pins
  really enable the direct landing) and **P2's one-step cores**
  `p2_core_dig`/`p2_core_borrow` (the direct commit provably never
  disturbs a dig's or borrow's own enabling facts — the base collisions
  die by rank arithmetic);
- the **register** `register_le_two` — §7's finite lemma: three live
  ball pinnings contain two equal ones (king gate →
  `receivers_king_nil`; the borrow pigeonhole → the twin pair; P1
  closes the `{dig, borrow, borrow̄}` corner);
- the stretch's ray core: `InRay` + `inRay_rank`, `inRay_color` (the
  parity alternation), `inRay_color_rel`/`inRay_same_color`,
  `inRay_twin_pair` (the per-level twin-pair confinement — "runs may
  repeat suits; only colors alternate"), `inRay_bounded` (kings
  terminate the ray);
- the **main theorem's assembly**: `c2_two_option` — three successors
  of a `drawCommit` always contain a closure-equal pair, by case
  analysis over the pillar-labeled pinnings (P2's world / the
  pin-sharing / the register's refutation / `stack_ball_corner`).

**The 5 sorried pillars** (each with its full PROOF PLAN in-file;
census baseline updated 14 → 19, this file 5):

| item | file:line | tag | route |
|---|---|---|---|
| `succ_labeled` (P0: §6.4's channel completeness — every successor labeled by a minimal live pinning) | C2Streamlined:924 | **[H]** | α-decomposition (A2) + the residence-class stability (hidden never seated by α) + fitted-coverer forcing at the cover's seating + `unseats_imp_pileStack` for the vacate | 
| `p2_direct_class` (P2's class half — the scar reproducible in the same closure) | C2Streamlined:957 | **[H]** | the one-step cores lifted to plays; `comm_deckPile_pileStack`/`_stackPile` or `commute_of_disjoint_frames`; destination-collapse (macro_parking P) for base variance; the late `PileStack X` for the safe stack arm |
| `same_pin_closureEq` (P3's class half + the §6.3 float-noise collapse) | C2Streamlined:984 | **[H]** | equal-spend free-float reconciliation (`aboveOf_congr_off` walks); nested chains → the crease; the within-channel twin choice → the local exchange/destination collapse |
| `crease_chain_absorbed` (§7's named crease — "the one line still requiring a line-force proof"; `c2_two_option`'s same-pin cases route here) | C2Streamlined:1016 | **[H]** | the line-force: `InRay` per-level twin confinement + per-level `only_blocker_is_twin` ⟹ deep landings never covered by the shallow commit ⟹ the deep `stackPile`s re-fire post-commit (MergeFire's `merge_refires_*` walk kit) and cancel (`stackPile_pileStack_cancel`) |
| `stack_ball_corner` (the L1/L2-diligence residue: raise-stack + two distinct live pins) | C2Streamlined:1045 | [H] | the raise chain is itself a same-suit-deterministic (F2) dig/borrow ray into one of the two live balls ⟹ the stack successor reproduces in that pin's class; the count is the L1/L2 table (no corpus third class) |

**Session notes**: `closureEq` is stated as *mutual* accommodation
reachability (the model's `accommodates` is not known symmetric — the
Rust `closure_contains` leans on reversibility's symmetry; P2/P3
adjuvant lemmas must mind the direction).  The `Label` set is
`{direct, dig, borrow p, hole, toStack}` — five, not §7's four: the
stack *residence* is not a resource spend (its raise-residue is priced
in `LabelLive.toStack` + the crease) — the doc's `{dig + one borrow}`
and `{borrow + borrow̄}` live-set claims are exactly the register's
pairing analysis, P1 closing the overlap.  §7's "∎ (modulo the crease
and the L1/L2 count tables)" is now formal graph structure: the crease
and the corner are the two named lemmas the assembly cites.


## Session note (2026-10-05 — §8.7 PAID: `Mask.bottomMask_matches_movableOf` PROVEN, Movability.lean sorry-free)

- **The owed equivalence is closed** (Movability:565): the engine's
  `bottom_mask_of` mask arithmetic and §8.1's `Card.movableOf` formula
  agree, per card, at every `(vis, locked)` grid — the Lean half of the
  Rust `bm_algebra_matches` binding.  The whole banked K-row dependency
  chain is now Lean-side sorry-free up to the (separate, shipped
  Rust-side) test.  Census: Movability 1 → 0 (global 16 → 15), pinned
  OK; the row's chain `[propext, Quot.sound]` per `#print axioms`.
- **The proof is the docstring decode plan, made lemma-shaped**:
  - step 1, layout (grid `decide`s, no classically-tainted helpers):
    `Card.maskIndex_inj` (Movability:249 — owner uniqueness via the
    mod-4 decode: rank block by division-by-4-bounds + `Suit.code_inj`,
    both omegas), `Card.even_maskIndex` / `Card.odd_maskIndex` (bit 0 IS
    the pair bit — the ALT gate's semantics), the twin adjacency
    `Card.maskIndex_flip_pair_false` / `Card.maskIndex_flip_pair_true`
    (`maskIndex flip = maskIndex ± 1`), `Card.maskIndex_lt64` (no u64
    truncation event ever: 52 + 4 < 64), `Card.maskIndex_lt4` /
    `Card.maskIndex_ge4` (the `<<< 4` guard splits aces exactly), and
    `Card.maskIndex_underPair_positions` (Movability:321 — the `± 4`
    block arithmetic lands the two under-pair reads on the two sitters;
    color cases + per-conjunct omega over `rank_pred_iff`, NOT a
    52-by-13 `simp_all` grid — that route strands the pred rank free,
    see FARM_MEMORY).
  - step 2, reads: `Mask.maskOf_maskIndex` (Movability:392 — the owner
    reads its own bit: `List.any_eq_true` + injectivity, the
    `decide_eq_true_iff` beq lane), `Mask.alt_of_even` / `alt_of_odd`
    (the ALT gates), the definitional zeta bridge `Mask.bottomMask_eq`
    into a private no-`let` `coreWord` (Movability:444), and private
    `spread_even` (the `× 0b11` twin arm under an even position dies by
    the ALT parity — the position's own bit is everything).
  - step 3, finish: private `bm_skeleton` — the xor chain equals the
    blocked-unders form over the same four bits (16-case Bool
    exhaustion, `movable_pair_symm`'s own trick, one lemma up);
    aces underflow to zero (`movableOf_ace`); the pair-`true` question
    routes through `movableOf_flipSuit` + the spread parity
    (`bm_rep` at Movability:476 is the pair-`false` representative
    decode; the main theorem's odd arm is three rewrites on it).
- **A companion reading of the word, for the consumers**: the
  engine word reads `locked` ONLY inside the under-pair `free` cut —
  `xor_vis` / `or_vis` read `vis` alone at the self and twin positions.
  K6's receiver-side questions never need a self-position locked read.
- **Next tickets**: (1) K6 fully unblocked — K1 + K2 + the §8.1
  substrate + the §8.7 equivalence have all landed; statable and
  provable off `State.movable`; (2) the doc-side alignment (§8.8 note
  in macro_formalization.md, plus the C15 ledger row) is now
  updatable — this row discharges the "parity debt" those
  entries hedge on; (3) nothing else in Movability.lean remains.
## Wave 18 — C2 closure: the pillar set refute-probed, the collapse's
proven half landed (2026-10-05, the C2-closure finisher session)

The wave-17 pillars were taken to the prover with wave-12/17's merged
weapons (TwinSwapCompletion's `attach_detach_cancel` +
`State.topOf_inr_eq_none`, Movability/Kills upstream).  The
refute-first gate FIRED: **four of the five universal pillars are
FALSE as stated** (REFUTED §4–§5 above;
`witnesses/C2KingAnchorWitness.lean` — one pristine WF state where a
climb-blocked stocked king's anchor landings are pairwise
closure-separated, killing `p2_direct_class`, `same_pin_closureEq`,
`crease_chain_absorbed` and the as-stated `c2_two_option` at once;
`succ_labeled` falls to the channel-list gap, witness pending).
The engine corpus never showed the corner because its class counting
ran on SWEEP-CANONICALIZED samples — a stackable-at-rung target has
every landing swept to one post-state, which is precisely the
PROVEN regime below.

**PROVEN this wave (axiom-clean, no sorry)**:

- `stocked_not_mem_hidden` (C2Streamlined:782) — the membership form
  of the stock/hidden-pile disjointness (the wave-17 kit had only
  the `prev` form);
- `commitTableau_shape` (C2Streamlined:794) — the tableau arm's
  commit unpacked (reachable position, attach, successor literal);
- **`commitTableau_shuttle`** (C2Streamlined:806) — the one-way
  foundation shuttle: from one committed landing of a stackable drawn
  card, `[pileStack X; stackPile X b₂]` reaches the OTHER commit's
  successor exactly (the board is `attach_detach_cancel` away from
  the same source, the bump-and-drop heights cancel at X's suit, the
  stock is the same splice — the guard's reachable position is the
  state's own);
- **`commitTableau_class`** (C2Streamlined:968) — the destination
  collapse at the commitment level: the two tableau-arm successors
  of the same drawn card at one WF state are `closureEq` whenever
  the card is stackable at its rung.  This covers both destination
  twins AND (for kings) free-anchor pairs, and is exactly the
  within-channel twin choice of §6.3's class computation — the
  model-side proof the wave-17 plan wanted from T's machinery, and
  the load-bearing half for any future repaired same-pin statement;
- **`c2_two_option` (conditional form)** (C2Streamlined:1221) — the
  main theorem rebuilt: same conclusion, with the play-level content
  as EXPLICIT premises (`hlab₁ hlab₂ hlab₃` the P0 labelings, `hp2`
  the P2 class-join, `hpin` the same-pin join, `hball` the
  L1/L2-residue corner, never refuted).  The wave-17 assembly — the
  register, the pigeonhole, `through_direct_hole_commits`'
  arms-cannot-label step — stays PROVEN verbatim against the
  premises.

**Census delta**: C2Streamlined 5 → 0; total 16 → 11 (script +
header updated together).  `Klondike.C2Streamlined` now imports
`Klondike.TwinSwapCompletion` (one DAG edge, umbrella order fixed);
no helper file was needed.

**Next tickets** (the honest path to the wave-17 ambition):

1. `succ_labeled`'s channel gap: build the king-anchor-head witness
   (analytic in REFUTED §4), then either extend `Label` with the
   king-anchor channel (generator change — orchestrator sign-off,
   the §6.4 case list is §7's spine) or guard P0;
2. the repaired same-pin program: `hpin` under the rung premise is
   exactly `commitTableau_class` at equal accommodations — the open
   content is the free-float residue (α₁ ≠ α₂) and the crease chains;
   re-scope `hpin`/`hp2`'s statements around the rung premise first
   (the witness makes the unguarded form provably false);
3. `stack_ball_corner`/`hball`: the one never-refuted pillar — the
   raise-ray geometry per §11's plan; closing it turns the
   no-direct branch of the conditional theorem unconditional there;
4. engine-side: probe the corpus for the climb-blocked stocking
   corner (three free anchors + climb-blocked stocked king) to bound
   how far §7's measured claim reaches beyond the proven regime.
## Wave 18 — T's catchup-residue: the L1/O3(ii) general window LANDED
(landed 2026-10-05, the catchup-residue farm session; TwinSwapCompletion
owned in place at macro-game HEAD)

The wave-17 T session's NEXT list, executed: items 1–2 PROVEN in full,
item 3 half proven + half pinned as the named reduction, item 4's
reduction IDENTIFIED (proven at the cell level) + pinned.  Census
16 → 18 (two believed-true pinning sorries, TwinSwapCompletion 0 → 2).

**PROVEN (all in `Klondike/TwinSwapCompletion.lean`, axiom-clean,
zero sorry; file grew 620 → 1351 lines)**:

- **The mixed-mid predicate** `Move.twinMid` (TwinSwapCompletion:667):
  `true` iff every `pileStack`/`deckStack`/`stackPile` in the move is
  of a card off the twin's own suit AND off the pair; `draw`, `reveal`,
  `deckPile`, `pilePile` ride unconditionally.  This subsumes the pure
  catch-up family (`catchup_mem_twinMid`: below-rank low-suit cards are
  off-pair by rank), the separated window's ORTHO moves, and the LOW
  suit's worry-backs and raises (the twin's firing does not touch the
  low suit's height, so their guards transfer verbatim).  NOTE: the
  predicate is deliberately ONE-SIDED in its suit condition, hence NOT
  flip-dual — the `_back` states its premises at the flipped roles
  directly (the prover caught my first flip-dual lemma as FALSE: a
  `t`-suit non-pair card is `twinMid t`-excluded but
  `twinMid t.flipSuit`-legal — correct, since at the flipped window
  the divergent suit is the other one).
- **Six per-kind exchange steps** (`twin_fire_exchange_draw/_deckStack/
  _deckPile/_stackPile/_pilePile/_reveal`, :733-1160): each takes the
  twin's guarded firing at `S` and the mid move firing on BOTH sides,
  and concludes the twin fires at the moved state landing EXACTLY the
  moved successor.  The vacated-seat landing (base = β) and the
  covered-twin landing (base = `Sum.inr t`) are DERIVED from the two
  firings — a β-landing cannot fire at `S` (the cell holds the twin),
  a twin-seat landing cannot fire at `B` (the fired twin is unseated,
  invisible as a base) — so `haccess` really is the no-landing premise
  in executable form, exactly as the ticket guessed.  The `pilePile`
  step (:920) covers the twin RIDING INSIDE the moved run (internal
  edges ride; only two root cells are written).  The `reveal` step
  (:1014) is the sole `hwf` consumer: `vis_not_hidden` keeps the
  seated twin out of every hidden slice, so a mid reveal cannot seat
  the boundary card onto it (the covered-twin corner as a MID move —
  the shape witness B blocks).
- **The general reorder** `pileStack_mid_reorder` (:1078): the MIXED
  mid commutes with the twin's stacking — induction over the mid
  dispatching to the per-kind steps (`pileStack` case = the existing
  `apply_pileStack_pileStack_exchange`), carrying WF and the twin's
  captured firing along the prefixes; the replayed mid fires the twin
  into exactly the source's mid successor.
- **Item 1, the general window** `State.solvable_swapTwin_mixed`
  TwinSwapCompletion:1140; `_run` packaging :1224): source wins via
  [prefix; stack t; MIXED mid; stack t'; tail] + `haccess` + `hwf`
  ⟹ `(st.swapTwin t).solvableFrom`.  Same twinSkew/crossTwin spine as
  the pure window — the reorder feeds `hCshape`, and the low rung at
  `M₀` (`hC₀low`) is now DERIVED (the twin's firing preserves the low
  suit's height, and the source's own second bracket pins it) — no
  per-card catch-up list needed anymore.
- **Item 2, the iff's backward half** `State.solvable_swapTwin_mixed_back`
  (:1289): the mirror-side hypothesis in the BETWEEN shape (at
  `(st.swapTwin t)` with roles flipped) ⟹ `st.solvableFrom`, by the
  forward window at the flipped twin + the involution.  The honest
  boundary (in-file, and the recorded successor ticket): the
  CATCH-UP-FIRST mirror plays need the catch-up-first→between
  DEFERRAL, and the deferral is *not* free — moving the mirror's
  first stacking across its catch-up needs the pre-catch-up
  fireability license (a catch-up card may sit ON that twin, uncovered
  only mid-catch-up — the flipped witness-A corner), and the
  post-stacking tail runs in the mirror's play at a state the
  forward window's `haccess` knows nothing about.  That deferral
  (L1(ii) at the mirror) is the next wave's first ticket.
- **Item 3's proven half** — the twin-suit worry-back discipline:
  `twin_fire_tSuit_stackPile_impossible` (:1328) and
  `twin_fire_tSuit_pileStack_impossible` (:1348): a foundation move
  reading the TWIN'S OWN suit cannot fire on both sides of the
  exchange at all (the ±1 rung offset) — the `twinMid` exclusion is
  contentful, not convenience; the LOW suit's worry-backs RIDE (are
  `twinMid`-legal and handled by the `stackPile` exchange step).
  `run_worryback_pair_excise` (:1369): an adjacent
  [worry-back, re-stack] pair nets to the identity
  (`stackPile_pileStack_return`), so excursion-shaped worry-backs
  lift out of any winning run — inside or beside the window.

**PINNED (2 sorries, each with its one-paragraph plan in-file; census
TwinSwapCompletion 0 → 2)**:

- `State.mid_access_of_noSeat` (TwinSwapCompletion:1443) — the
  `haccess` DERIVATION at the no-landing premise, the model half of
  item 3's engine-corpus audit: given the source's own mid plus the
  per-seat exclusions (landing bases off β and off `Sum.inr t`),
  the whole mid replays at the pre-firing state AND lands on the
  source's successor.  Plan (in-file): the B→A mirror of the six
  exchange steps; the genuinely new piece is the `pilePile`
  walk-extension (`x ∈ aboveOf_A z → x ∈ aboveOf_B z ∨ x = t`, by the
  `aboveOf_go` induction — the A-walk reads β, gains t, stops at the
  bare seat); the reveal needs the state-dependent `hiddenBase`
  exclusion.  The corpus half — which reached states' between-mids
  satisfy the seat exclusions — is §8's audit (the histogram pull).
- `State.sweep_covered_corner_safety` (TwinSwapCompletion:1533) —
  §6.5's semantic obligation AT the covered corner (item 4): the
  covered corner and its exchange image are solvability-equivalent, so
  the sweep's deterministic lowest-first pick never UNIQUELY loses a
  win at the ambiguous pair.  The reduction's IDENTIFICATION half is
  PROVEN: `exchangeTwinCargo_flip_cover` (TwinSwapCompletion:1486) —
  at the corner, `st.exchangeTwinCargo L` has exactly the flipped cell
  readings (the two identity-resolutions of the word are the two
  exchange-images; note the raw seat-swap rides the cover card's
  VALUE to its own seat — why the safety must route through the
  discipline kit, not a literal symmetry).  Plan (in-file): WF forces
  the corner to be deal-adjacent (`canSitOn` dies at the mate's own
  rank); every win must dislodge the covering mate (extraction +
  `unseats_imp_pileStack`); at the dislodged/bare pair the PROVEN
  `twin_stack_order_exchange_catchup` +
  `solvable_cargoTwin_exchange_licensed`/`_of_visClean` family
  supplies the equivalence; the residue inside that is the
  LICENSE-FIT while the mate still sits (the w15fithole rider-detour
  class).

NEXT (tickets, in order):
1. ~~The catch-up-first→between DEFERRAL at the mirror~~ — PAID
   (wave 19; see the wave-19 row below).
2. `State.mid_access_of_noSeat` — REPAIRED + DRAFTED (wave 19; the
   statement was false as wave-18 pinned it — see the wave-19 row);
   successor: reinstate `attic/MidAccessDraft.lean` into
   TwinSwapCompletion.lean and finish the elaboration.  Then §8's
   landing-site histogram pull (engine corpus: do between-mids ever
   land on the twin seats?).
3. `State.sweep_covered_corner_safety`'s plan: the deal-adjacent
   license-fit (or dislodge-first normalization), reducing the
   §6.5 covered corner into the proven exchange family.
4. Optional probe: a decide-anchored witness for the ON-PAIR shuttle
   corner (a `pileStack t'`/`deckStack t'` inside the mid is
   source-inconsistent — the second bracket's rung pin; a small
   `#eval` cast would document it).
5. Optional: the swapTwin-WF preservation lemma (`st.WF →
   (st.swapTwin t).WF` — deal/stock relabeling + board conjugation),
   which would let the mixed iff stand on `st.WF` alone and drop
   `_back`'s mirror-side WF premise.

### Wave-19 (2026-10-05, the t-iff-complete session; file
TwinSwapCompletion.lean at pin 2, census 12 GREEN)

TARGET 1 — THE MIRROR-SIDE DEFERRAL: **PAID, license-free**.  The
honest resolution: `_back`'s window restricts the BETWEEN-MID
(`twinMid t'`) but never restricts `q₁` (only `cleanTwin t'` — which
bans ON-PAIR FOUNDATION moves only; `t'`-suit raises are off-pair by
rank), so a catch-up-first mirror play — `q₁` swallowing the whole
catch-up-containing prefix, the two twin stackings ADJACENT —
RE-BRACKETS VERBATIM as the between window with the EMPTY mid:
`State.solvable_swapTwin_mixed_back_catchupfirst` (PROVEN, no
license consumed).  The LICENSED literal split (the mid itself
re-seated between the stackings) is REFUTED at the asymmetric
window: the rung pin (the catch-up is what raises the first-stacked
twin's suit to its rung) + the flipped witness-A SEAT corner — a
catch-up card sitting ON the twin, uncovered only by its own raise
mid-catch-up — see **witness C**
(witnesses/TwinCompletionWitness.lean, decide-anchored: the
catch-up-first bracket [raise ♥3; raise ♥4; stack ♥5] fires; the
pre-catch-up `stack ♥5` is seat- and rung-blocked).  Wave-18's
"deferral is the recorded successor ticket" is closed: no license is
needed and none carries the literal split.  The `_back` docstring
and the file's section note carry the history.

TARGET 2 — `State.mid_access_of_noSeat`: **REPAIRED, not closed**.
Wave-19's guard audit found the wave-18 pin FALSE AS STATED (two
exclusion classes missing): (a) `pileStack` SEATS — the twin may sit
ON a mid raise card (`β = Sum.inr c`; witness A's own corner, live
at WF via `board_edges` deal-adjacency); (b) REVEAL cells — the
boundary's own seat (a twin dealt onto the hidden boundary) and
the attach base (a twin-king on a one-hidden-card pile's anchor
blocks `hiddenBase a = β`-shaped reveals).  The repaired statement
(statically excluding, per mid reveal: the anchor, `A.hiddenBase a`,
and every seat of every card of `A.hidden a` — the current AND all
future boundaries/attach cells of the pile's reveal chain, sound
because `mem_of_getLast` + take-mono keep later boundaries inside
the shrinking prefix) is IN-FILE, still sorry'd (the file's pin count
is unchanged at 2 — this is a re-pin of the same theorem, with its
one-paragraph plan in-file per the census rules).  The FULL ~700-line
proof is drafted in `attic/MidAccessDraft.lean` (NOT built; nothing
imports it): the `TwinReplayTrace` pair-delta invariant, its base
case off the twin's firing, the seven B→A transfer mirrors (the
`pilePile` one through the `aboveOf_twin_delta` walk delta — the
A-side run gains at most the twin as its head — plus the
`heights_tSuit_stable`/`deal_stable_move`/`depths_mono_move` shape
lemmas and the `mid_access_chain` induction).  Remaining: ~25 local
elaboration fixes (literal-projection `show` orientations, a few
`rw` directions); the successor reinstates it into
TwinSwapCompletion.lean, fixes those, git-rms the attic file.

TARGET 3 — `State.sweep_covered_corner_safety`: NOT attempted this
wave (budget went to targets 1–2); the ticket-3 plan stands as
written, and per this wave's finding the LICENSE-FIT residue should
be scoped against the same cleanTwin-swallows-the-catch-up reading
that closed target 1 (the transfer family already constrains only
the between-mid; the dislodge-first normalization remains the
plan's (2)).

Census: 12 total, TwinSwapCompletion pinned 2 (mid_access_of_noSeat
repaired/re-pinned + sweep_covered_corner_safety), inventory OK.
Build: `lake build Klondike Witnesses` green (fresh full build at
macro-game HEAD; the "expected Given the worktree sits at an old
base" gotcha hit — fast-forwarded to b99ad47 first).

## Wave 19 — C2 re-scope: the rung premise's derivations + the
raise-ray core (landed 2026-10-05, the C2-rescope farm session;
C2Streamlined owned in place at macro-game b99ad47)

The wave-18 C2-closure NEXT list, items 2–3 executed, item 1
(`succ_labeled`'s channel decision) delivered as the analysis below —
orchestrator scope, per REFUTED §4; item 4 (engine corpus probe)
untouched.  All new content is PROOFS (zero new sorries; census pinned
12 / C2Streamlined 0 — the header updated together).

**LANDED — item 2, the `hpin`/`hp2` rung re-scope (C2Streamlined
§12.5):**

- `succThrough_zeroSpend` [propext, Quot.sound] — the zero-spend
  channels (`direct`, `hole`) demand the EMPTY accommodation (their
  `LabelSig` is `α = []`), so their witnesses commit AT THE ROOT (and
  with `through_direct_hole_commits`: the direct-absent world cannot
  present a zero-spend label at all);
- `pin_join_zeroSpend_rung` [propext, Quot.sound] — **`hpin` DERIVED
  for the zero-spend channels** under the root-rung premise: both
  witnesses commit at `st`, so the same-pin join IS
  `commitTableau_class` at the root — the rung-carrying re-scope the
  wave-18 row called for, now a theorem (the king-anchor witness's
  split is exactly this rung's failure; un-refuted corner closed);
- `p2_join_zeroSpend_rung` [propext, Quot.sound] — **`hp2` DERIVED for
  the zero-spend channels**: every root commit's arm joins — the
  tableau arm by `commitTableau_class`, the STACK arm by the two-move
  worried-back roundtrip (`stackPile X b` rebuilds the tableau
  successor exactly: same attach, same stock splice — both arms jump
  the SAME reachable position —, bump/drop heights cancelling;
  `pileStack X` returns it) — §6.7's empirical "late `PileStack(X)`
  merge" (the 1,102 mixed-kind single-class commitments) as a proof;
- `c2_two_option_zeroSpend_rung` [propext, Quot.sound] — the
  derived-scope bound itself: three zero-spend-labeled successors
  contain a closure-equal pair with NO play-level premises (any one
  zero-spend label forces a root commit; all such successors join
  every root commit's class — the register is not even consulted).

**LANDED — item 3, the raise-ray core (`hball`, C2Streamlined §14):**

- `reachablePos_of_accommodation(_run)` [propext, Quot.sound] —
  accommodations never touch the stock cycle or draw step: the
  commitment pacing guard is invariant along every accommodation play
  (the denominator behind the stack-channel witness's reachability
  being the ROOT's);
- `heights_step_accommodation` [propext, Quot.sound] — the per-move
  step law: a suit's standing height moves only at a same-suit
  `pileStack` (+1, the fired card's rank-index pinned by the move's
  guard to the standing level) or a same-suit `stackPile` (-1);
- `raise_crossing_mem` [propext, Classical.choice, Quot.sound] —
  **F2's deterministic raise**: any accommodation play crossing
  standing level `k` of `X`'s own suit upward fires, somewhere in its
  course, the `pileStack` of the (unique) `X`-suit card at
  rank-index `k` — first-passage analysis, the crossing move's own
  guard forcing suit and rank-index into the witness;
- `stack_channel_world` [propext, Quot.sound] — the corner's derived
  shape: WF + stack channel live + direct absent FORCE `X` reachable
  and the suit's standing height strictly BELOW `X`'s rank (a founded
  card is never stocked; a rung-matched reachable card would fire the
  stack commit) — the raise content is present, never degenerate;
- `stack_raise_deterministic` + `stack_channel_raise_mem`
  [propext, Classical.choice, Quot.sound] — every stack-channel
  witness's play fires the `pileStack` of `X`'s SAME-SUIT RANK-MATE
  (the `X`-suit card one below `X`'s rank-index) — the same final
  raise for every witness, exposed with its own play and stack
  commit; the residue analysis's shared spine;
- `raise_card_off_ball` + `flipSuit_suit_ne` [propext, Quot.sound /
  propext] — the hygiene: the raise spends strictly inside `X`'s
  suit-column — never the twin's seat (the pair-flip suit), never a
  receiver (rank above), never a borrow pin's own signature card
  (opposite color).

**The honest residues, named for the next pass** (in-file §12.5/§14):

- `hpin`/`hp2` for the SPEND channels (`dig`, `borrow p`) and the
  stack channel's same-pin case: the free-float reconciliation (two
  witnesses' plays α₁ ≠ α₂ ending at different accommodation states)
  plus the crease chains — the root rung does not reach these (plays
  can raise/re-drop a suit past the rung);
- `hball`'s full content: reconciling the raise's ENABLERS (the moves
  freeing the rank-mate at its firing state) with the two live pins'
  own witnessing plays — exactly the crease/free-float residue; what
  is proven bounds every resolution: no stack-channel witness exists
  without consuming the one same-suit raise chain.

**Item 1 — the `succ_labeled` channel decision (analysis; the
witness itself is the sibling session's `witnesses/SuccLabeledWitness.lean`,
merged 58448d7 on macro-game, past this branch's base):** the
anchored-head unseating corner is now witness-backed (seven occupied
anchors, one removable non-spade head, the spade-freeze invariant
closed under both accommodation moves — every root label dead while
the king lands on the vacated anchor).  The decision list, both routes
surrounding the five-element poset: (a) extend `Label` with the
king-anchor/unseat channel — a generator change through the whole
surface (`Label`, `labelPin`, `LabelLive`, `LabelSig`, `commitArmOf`,
`register_le_two`'s live-set, the conditional's `hlab` spellings);
needs orchestrator sign-off; (b) guard P0's labelings to root-live
channels only (the conditional stays sound; its labeling premise
hardens; the orphan successors stay outside the theorem).  This
session's derivations are untouched either way: they take their
labelings as premises and consume no P0 content.

**initialReachability interop** (per the reach-probe sibling's ask,
its session no longer reachable at reply time — recorded here): my
theorems need NO domain hypothesis — state-universal under the LOCAL
rung premise, which reachability neither implies nor needs; the
absorbable premise is `hlab`'s channel-list gap (the natural
`initialReachable` repair target via Restriction's fences); the
as-stated `hpin`/`hp2` refutations need ≥ 2 simultaneously-free
anchors for a climb-blocked stocked king, so the WEAK reachable
corner (one free anchor) cannot revive them — an
initialReachable-scoped `c2_two_option` is live and orthogonal to the
rung-scoped derivations; `hball`'s free-float residue is play-level,
not expectably absorbable by reachability.  The spade-freeze
invariant is the suggested composition-counting target for the
probe session's per-pillar table (five pillars: `wk_c2` /
`wk_same_pin` / `wk_p2_direct` / `wk_crease` / `wk_succ_labeled`).

**Census delta: NONE** — 12 pinned, C2Streamlined 0; `lake build
Klondike Witnesses` green at this branch.

NEXT (tickets):
1. The spend-channel free-float: reconcile two dig/borrow-channel
   witnesses whose plays end rung-matched (the α₁ ≠ α₂ collapse under
   the two-type ball locality — §11's P3 plan with the zero-spend half
   now proven); decide-first against the king-anchor family.
2. `hball`'s residue: the raise's enabler analysis (who covers the
   rank-mate at the root, which pin's signature frees it) — with
   `stack_raise_deterministic` in hand the two witnesses share one
   spine, so the pairwise resolution reduces to the crease's
   depth-ordering.
3. Orchestrator: the `Label` channel-list extension vs P0 guard
   (decision list above); the engine-side climb-blocked stocking
   probe (wave-18 item 4, still unowned).
4. Optional polish: promote the state_ext-literal slot chains and
   the `run_nil_elim`/`run_cons_elim` induction idiom into
   Tactics.lean macros (three-plus uses now recorded in
   FARM_MEMORY's wave-19 note).
---

## wave 19B (2026-10-05) — the C2 reachability probe: all five refutation corners live OFF the dealt-reachable fragment

Session: farm-kinganchor-reach-probe.  Content:
`witnesses/KingAnchorReachProbe.lean` (root, glob-registered; facade
import added — see below).  `lake build Klondike Witnesses` green;
census unchanged (witnesses not counted, no Klondike file touched).

THE DATUM the wave-18 falsity pass and the wave-19A anchored-head
witness left open: can any of the five negated universals' countermodel
states be *reached from a dealt game* (`initialReachable`,
Restriction.lean)?  Answer: NO, at every root AND at every king-landing
successor — so every initialReachable-gated restatement of the five
universals is beyond this witness family's reach:

- wk_c2            — RESTORED under hreach (pristine root unreachable)
- wk_same_pin      — RESTORED under hreach (same root)
- wk_p2_direct     — RESTORED under hreach (same root; all seven
  landing successors also unreachable, so successor-side reachability
  premises are safe from this family too)
- wk_crease        — RESTORED under hreach (same root)
- wk_succ_labeled  — RESTORED under hreach (anchored-heads root
  unreachable: the board seats only the seven heads, ♠A buried in
  p1 nowhere)

OBSTRUCTION CLASS: (b) pile-structure conservation, not (a) stock
composition.  Both witness deals are honest 52-card deals (spade count
closes: twelve pile spades + the stocked ♠K).  The new fence
`KingAnchorReach.pileCards_seated_of_initialReachable`: at a
dealt-reachable state with all depths and heights zero, EVERY dealt
pile card is visible (28 buried cards cannot all vanish).  Backed by:

- `KingAnchorReach.accounted` + `apply_accounted` (all seven moves) +
  `run_accounted` + `initial_accounted` — the conservation invariant:
  along any play every pile card stays hidden, visible, or founded
  (the stock cycle never gains cards and starts deal-disjoint from
  the piles; `reveal`'s boundary-one-reveal, the pilePile image
  preservation, the bump/drop uniqueness arguments).
- `initialBoard_seats` (private, in-file): the forward seating theorem
  the initial case needs — the deal fold boards EVERY pile's top card
  at its `initBase` (InitImg image induction over the fold; initBase
  injectivity from deal distinctness).  Reusable far beyond this file.
- Three public replica verdicts, each with a WF exhibit so the fence
  separates two genuinely inhabited worlds:
  `KingAnchorReach.wstate_not_initialReachable`,
  `.wsucc_not_initialReachable (a)`, `.ustate_not_initialReachable`
  (axioms [propext, Classical.choice, Quot.sound]).  The replicas are
  field-identical spellings of the read-only witnesses' private
  states — verdicts are stated at the replicas because the originals
  are private (ticket below to retire them).
- Facade: `Witnesses.lean` now imports the probe — the FIRST
  witness-facade cross-import, chain-checked namespace-hygienic in the
  umbrella comment — so wave-20 cites the verdicts directly.

CAVEAT for the wave-20 restorer: "restored" here means the witnesses
no longer counterexample the gated statements.  The gated universals
themselves are OPEN: the corpus's weak corners (a lone climb-blocked
anchored king, 12 states in 5 seeds — seed 26, ♣K on p1) ARE
dealt-reachable, so the gated proofs carry real content.

NEXT (tickets this verdict enables, in order):
1. Prove the reach-gated universals (all five) — `commitTableau_class`
   carries the stackable-rung half; the label-completion route
   (wave-19A's `anchorHead a` channel decision) carries succ_labeled;
   the fence licenses the pristine-corner premise re-scope.
2. One-word orchestrator edit, then retire the replicas: deprivatize
   `wState`/`wDeal` in C2KingAnchorWitness and `uState` in
   SuccLabeledWitness (private def → def); with the names public the
   replica-unreachability theorems transfer by one-line rfl.
3. (wave-18's standing tickets 1-4 unchanged.)



## wave 20 (2026-10-05) — the C2 restoration: the five gated universals in their honest regimes, and the reachable-corner countermodels that bound them

Session: farm-c2-restoration (this wave-20 branch).  `lake build Klondike
Witnesses` green; census unchanged at 12 (C2Streamlined 0 — sorry-free).

THE TWO-FOLD ANSWER this wave gives the wave-19B ticket 1 ("prove the
reach-gated universals, all five"):

**(A) THE GATED UNIVERSALS DO NOT HOLD NAIVELY — the reachable corner
is its own countermodel family** (`witnesses/SuccLabeledWitness.lean`,
the reachable-corner addendum — decide-anchored, all axiom-clean):
`rState` is the dealt INITIAL state of an honest 52-card deal (reach:
`rState_reachable`, the EMPTY play — no fence can bite; ♠K drawn
first; every pile's top dealt card a non-spade so the spade suit is
frozen) with ♥A — pile 0's single card — UNCOVERED ON ITS ANCHOR at
foundation height 0.  There:

- the anchored-ace promotion route fires (`rUnseat`, `rStep`): the
  `Draw(♠K)` commitment lands the king on the vacated anchor while
  every current channel fails to label the successor
  (`rSucc_unlabeled`; `hole` is LIVE at the root but its empty-window
  signature cannot name a promotion successor — the heart height
  separation `rRoute_not_hole`): **`wk_succ_labeled_reachable_false`**
  — the wave-19B "RESTORED under hreach" reading for succ_labeled was
  wrong (it fenced only the pristine shape);
- AND the same root splits the four class universals' gated readings
  too: with six free anchors, three root tableau landings of the
  frozen king are pairwise closure-separated (`rLand_split`, the
  frozen-seat invariant `rFrozen_seat_step/_run` — pileStack ♠K needs
  rung 12 against the frozen 0; no non-king spade can ever seat;
  stackPile cannot land on the occupied anchor) while all three go
  through the live, P2-safe `hole` label with empty windows:
  **`wk_c2_reachable_false`**, **`wk_same_pin_reachable_false`**,
  **`wk_p2_direct_reachable_false`**, **`wk_crease_reachable_false`**.
  The wave-19B per-pillar table is revised in-file
  (witnesses/KingAnchorReachProbe.lean's verdict table + its
  docstring).

THE LABEL-DECISION INPUT (the wave-20 ticket 3, recorded in the
addendum's header): the anchored-head unseat route is NOT a pristine
countermodel artifact — it occurs at zero-move-reachable dealt
initial states, so the five-channel completeness fails ON the
fragment the engine plays.  Repair routes stand as wave-19A listed
them, now with reachability evidence: (a) the `anchorHead a` channel
atom, or (b) the context-irreversibility window gate (under which the
promotion is its own commit and the successor IS hole-labeled at the
shifted root — `uShifted_hole_cover`).  Engine-side harness tickets
(out of Lean's reach, for the orchestrator): (1) the corpus sweep
for frozen-suit stocked kings at ≥2-free-anchor states (wave-18's
standing ticket — now known REACHABLE, frequency unknown); (2) the
frequency of uncovered promotable anchored heads (any rank-mate
head on an anchor) alongside a frozen drawn king — the route's
real-world urgency.

**(B) WHAT IS PROVEN — the honest regimes** (all in
`Klondike/C2Streamlined.lean` §15, sorry-free, census-clean; the
packing: the weak-corner corpus shape, no rung where the corpus says
so):

- `heights_of_applyDrawStackTo` — the stack commit's own guard,
  extracted (the rung read out of any stack-arm successor);
- `king_tableau_base` — a king's tableau placements are exactly the
  free anchors;
- `same_pin_hole_oneAnchor` — the same-pin universal's weak-corner
  restoration: two `hole`-through successors at ≤1-free-anchor states
  join; NO rung, NO WF (the corpus's climb-blocked corners need
  exactly this);
- `labelLive_of_king_frozen` + `succThrough_king_frozen_join` +
  **`c2_two_option_king_frozen`** — the ≤2-count universal at the
  frozen one-anchor king corner, FULLY proven modulo the labelings
  (the P0 content stays a premise — the addendum shows it is not
  gate-dischargeable);
- `crease_stack_deterministic` + **`crease_absorbed_reachable`** —
  the crease's equal-window half: two same-channel windows that end
  at the SAME accommodation state (`hwin : u = u'` — the free-float
  residue isolated as an explicit premise, honestly replacing the
  refuted Sublist-alone claim) with the rung at the shared end join
  (tableau arms by `commitTableau_class`, stack arm by determinism);
  `initialReachable` supplies the end state's WF along the window;
- **`c2_two_option_reachable`** — the reach-gated conditional
  umbrella: the gate discharges `st.WF` and nothing else (the four
  play-level premises stay — by (A) they are not gate-dischargeable);
- **`p2_direct_class_king_oneAnchor_reachable`** — the P2-direct
  universal's weak-corner restoration, gated (WF from reach; the
  stack arm forces its own rung via the extraction above, so §12.5's
  roundtrip applies).

HYGIENE (wave-19B ticket 2, DONE): the replicas are retired —
`wDeal`/`wState`/`wSucc`/`wS_shape`/`wBoard`/`wS_bot_none`
(C2KingAnchorWitness) and `uState` (SuccLabeledWitness) are public;
the three verdicts are restated AT THE ORIGINALS
(`KingAnchorReach.wState_not_initialReachable`,
`.wSucc_not_initialReachable (a)`, `.uState_not_initialReachable`,
all axiom-clean); the probe's replica sections are deleted; the
deal-fold forward seating theorem moved into the lib
(`Klondike/Initial.lean`: `initialBoard_seats` + `getLast?_of_index`,
public); the probe now imports `Witnesses.SuccLabeledWitness` (the
second witness-file cross-import after the wave-19B facade, acyclic).

CENSUS DELTA: NONE — 12 pinned, C2Streamlined 0, witnesses uncounted.

NEXT (tickets):
1. Orchestrator: the Label channel-list decision (a) `anchorHead`
   vs (b) the window gate — now with the reachable-corner evidence
   attached; the engine-side corpus sweeps (1)/(2) above as harness
   tickets.
2. The spend-channel free-float (`hpin`/`hp2` for dig/borrow at
   rung) — wave-19's tickets 1-2 stand, now scoped by §15's regimes.
3. `c2_two_option_reachable`'s premise discharge fragments: any new
   proven regime (a new shape class) slots straight into §15's list.
