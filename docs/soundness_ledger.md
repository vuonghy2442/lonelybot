# Soundness ledger — the rigor status of every claim

A single index: what each soundness-bearing claim is, where it is argued,
how close it is to rigorous, and what closes it. Details live in the
specialized docs; this file maps claims to tiers, not proofs. Update a row's
tier when the underlying doc moves — a stale ledger is worse than none.

- [method.md](method.md) — the method itself (rules, engineering)
- [no_pile_to_pile.md](no_pile_to_pile.md) — the move-set restriction theorem (legs 1+2)
- [pruning_dominance_interaction.md](pruning_dominance_interaction.md) — the D × P × TP composition (and the recorded sequencing decision, §8)
- [last_draw_rules.md](last_draw_rules.md) — the `last_draw` streak rules (6.4)
- [macro_formalization.md](macro_formalization.md) — the macro/commitment rework
- [rigor_status.md](rigor_status.md) — the narrative framing: what "rigorous" means here, the finish line, and the overall read
- [rigor_status.md](rigor_status.md) — the narrative framing behind these
  tiers (the standard, the three cores, the finish line)

**Scope.** The *thoughtful* solver — correctness of the solvable/unsolvable
verdict. The no-undo player adds value evaluation on top (determinization
bias is a strength question, not soundness); only its replay assertions
lean on this ledger, via row F1.

**Tiers** (aligned with the [x]/[~]/[ ] legends in the companion docs):

- **[P] proven** — machine-checked, or a published proof that applies
  verbatim.
- **[x] argued complete** — an informal proof in the repo whose remaining
  steps are mechanical case-checks a reviewer can fill without new ideas.
- **[~] argued with named gaps** — a proof shape whose missing steps are
  named conjectures, each with a falsifier or instrument.
- **[ ] open** — intent or anecdote only.
- **⟂ superseded-by-design** — the commitment-game rework deletes the rule
  by construction, so the row is a holdover, not an active proof
  obligation. Its *instrument* still runs in Phase 0: the falsifiers get
  their chance to fire before the demolition. See the sequencing decision
  in the interaction doc's §8 and the migration plan below.

Tiers propagate as a minimum over dependencies: an [x] row resting on a
[ ] row is effectively [ ] until the dependency moves. The "effective"
column records that.

## A. State representation and the transposition table

| # | Claim | Argued in | Tier | Depends on | Closed by |
|---|---|---|---|---|---|
| A1 | Hidden identities are pinned within a game (deal prefixes + counts), so the encode never conflates hidden arrangements | no_pile_to_pile §1 (discharges macro O2) | [x] | — | — |
| A2 | `MixHasher` is a u64→u64 bijection, hence zero collisions | src/utils.rs (xorshift × odd-multiply = composed bijections) | [x] | — | trivial; Lean-able |
| A3 | α-invariance: solvability is a function of the abstract state = soundness of the TP conflation | no_pile_to_pile §0/§5 (corollary); interaction doc H3 | [~] | B1–B4 | inherits B4 |
| A4 | Twin-swap theorem T (narrow scope: twin substitution) | macro_formalization §3 | [~] | — | Lean (macro O4); proof strategy written, O1/O3/O5 open |

## B. Move-set completeness (legs 1+2 of method.md §9)

| # | Claim | Argued in | Tier | Depends on | Closed by |
|---|---|---|---|---|---|
| B1 | Realizability invariant + parity lemma (bm computes uncovered_t > 0) | no_pile §3 (maintenance cases + boundary conditions written) | [x] | — | Lean obligation 1; the full (present, placed) case table |
| B2 | Completeness: concrete winning play ⇒ abstract winning play, via the compression lemma | no_pile §4 | [x] | B1, B3 | Lean obligation 2 |
| B3 | First-layer-king relabeling is a behavioral isomorphism (raw level) | no_pile §6 | [x] | — | Lean obligation 3; context-sensitive version owed to the pruner layer (D-layer) |
| B4 | Concretization / reshape lemma: abstract winning play ⇒ concrete winning play | no_pile §5: twin-expansion isolated as the sole "no concrete counterpart" case; normal-form conjecture (compute_visible_piles) as strategy | [~] | A4 | Lean obligation 4 + the relocation-failure instrument (§5.2; src/convert.rs:63) |

**The leg-1+2 theorem itself is [~]:** B2 [x] + B4 [~] ⇒ min [~].

## C. The dominance cascade (method.md §5)

| # | Claim | Argued in | Tier | Depends on | Closed by |
|---|---|---|---|---|---|
| C1 | Forced safe stack (5.1) — Keller's rule, opp ≥ r−1, twin ≥ r−2 | Blake & Gent App. B.1 (standard game); channels A/B decomposition in interaction doc §4 | [P] external; [~] effective here until ported | B-theorem (port bridge, no_pile §8) | port via B4 + set abstraction |
| C2 | Worry-back ban (5.4), incl. compatibility with C1 | Blake & Gent §5.4.1 + Thm. 5 (standard game) | [P] external; [~] effective | C1, B | same port |
| C3 | ≥3 redundant stackables → lowest only (5.2) | interaction doc Table 1: reduces to C1+C2 + stack-stack commutation | [~] | C1, C2, A4 | writeup, then Lean |
| C4 | Deck dominance, draw-1 (5.3 partial) | published stock≈reserve exception (B&G §5.4.1) | [P] external; [~] effective | B | same port |
| C5 | Deck dominance, draw ≥ 2 (`is_pure` last card) | two-sentence purity sketch (method §5.3); exceeds a published warning | [ ] | — | the writeup owed (TODO), then differential test |
| C6 | Twin-pair collapse (5.5) | T-equivalence + free_slot = placements onto the pair (L1); dropped KING_MASK rescued by drain-safes-first | [~] (T survives; drain-safes ⟂) | A4, E2 | T proof (shared spine); the drain-safes rescue dies with the D-layer — Phase 2 must re-derive the king exemption inside the accommodation solver |
| C7 | Least-stack cascade (5.6) | intent comments only (src/state.rs:222-286) | [ ] | A4, C3 | the TODO(vuong) writeup — the least-argued rule left |
| C8 | King / empty-pile rules (5.7) | = B3 + the free_slot king gate | [x] | B3 | — |
| C9 | Deck-source dominance at the macro fold (draw-1): when a drawable deck card is dominantly stackable, only the lowest such card is offered as a Draw commitment | C4 ported to the commitment level; the commute lemma: for any other commitment c on offer, {Draw c; Draw d} ≡ {Draw d; Draw c} up to the canonical sweep — parking never consults the foundation, and `canonicalize` stacks dominantly-safe cards for free the moment they land. Premise: dealing is unbounded (deck.rs `iter_callback` wraps the offset: jumping the offset never forfeits a card), which is exactly the assumption the engine's draw-1 rule already made | [~] | C1 (the Keller premise), unbounded-dealing semantics | falsifiers: `macro_verdict_matches_engine` (live), `macro_verdict_sweep_big` + `macro_verdict_sweep_ks` per fold change; Lean with C1's B4 port |
| C9x | **Falsified extension:** the same restriction lifted to draw ≥ 2 | — | [!] 2026-09 — seeds 67 & 74 (draw 3) flip `old=true → direct=false` under the lift; the pace-shaped drawable set of draw ≥ 2 means the "jump to the lowest dominant" commitment can skip over cards the win needs parked first (the draw-1 argument's "you can always stack it first" has no counterweight there). Reverted to the draw-1 gate. Recorded so it isn't re-proposed without a new argument | — | it just fired (the acceptance sweep) |
| C11 | **Falsified port:** C5 (last-card purity) at the macro fold — "deck pure + last card dominantly stackable ⇒ only its stack outcome, swallowing the node" | — | [!] 2026-09 — seed 21 (draw 1) flips `old=true → direct=false`. Mechanism: `Deck::is_pure()` means "offset sits at a step boundary / at the end" in a *dealing* model, but the macro commitment draws jump the offset straight to the drawn card, so macro-pure ≠ old-pure — the premise fires "true" at macro states where the old rule never applied it. The old engine's comment on the same arm is on record as `// not very useful as dominance`. Recorded so it isn't re-proposed without a macro-native pure-waste definition | — | the live 32-game gate |
| C6r | **Rejected port:** dropping the higher-twin child in the accommodation BFS ("twin collapse") | failure mechanism: the crease BFS's goals are per-*card* (`Possibility::Tableau(x)` checks `pile_stack & xmask`), so forbidding the higher twin forces witness detours along the lower twin's chain; the detours can outrun the per-goal depth caps (≤10/40) and silently lose goals → lost classes, wrong horizons. C6 at move level is a *priority* rule (force the pair's stacking, keep both twins), not an eliminability rule — that distinction survives any port. Rejected before profiling; the dedup-on-stack-word already kills true duplicates | rejected 2026-09 (never shipped) | — | — |
| C10 | **Rejected port:** crease-level forced-stack singleton (C1 inside the accommodation BFS: "never wander past a dominantly-safe stackable child") | measured failure: the differential's `missing` counter moved 0 → 14, tableau-bfs output dropped 70 → 56 — goal openings that need a worry-back detour *before* the safe stack lands get starved, so the singleton loses crease coverage. C1's license holds at destination/verdict level (a safe stack never flips solvability), not at goal-search level (it can flip *which class of the same commitment gets found* — the C-SCAR axis). The singleton rule is legal at the fold (search policy), not inside witnesses | rejected 2026-09 (gated out by the differential) | C1 | the differential dial it moved |
| C12 | Forced-commitment dominance at the macro fold, `Reveal` arm: if a locked surface is dominantly stackable, its Reveal commitment (stack outcome) is the node's only successor | the generalization of the move-level interlock; measured: seed 32 draw-1 37.5s → 8.5s with the unique-state count now matching the complete refutation's scale (~2.98M macro vs 2.90M old misses) | [~] | C2 (worry-back ban), the sweep canonicality (≔ macro §4.5/§6.5b) | falsifiers: live 32-game gate + both 128-game sweeps per fold change (green 2026-09); Lean after P.1c+P.6 settle |
| C-IND | Partial-order structure of commitments (C-IND): the interaction ball of a commitment is its five-type neighborhood; disjoint-ball commitments commute (measurement probe: `debug_commutation_landscape`) | 2026-09 measured on the differential corpus: **draw·reveal pairs commute at ~92% exact in both draw steps**; reveal·reveal ~86–100%; draw·draw splits by pace (draw-1 ~92%, draw-3 ~2% — the pace argument of C9x returning as data). The residual classes are named: `disabled` (one commitment kills the other — enablement hazard, 8%/33% by step) and `distinct` (post-states not same-encode nor closure; rare except draw-3·draw-3). Canonical-order pruning (reveal-before-draw among commuting pairs) is the first stubborn-set rule this licenses; the hazard rule "never defer a pair in `disabled`" is the correctness side-condition | [m] | C6r/C9x/C11 measure the pace wall | the probe itself; a canonical-order fold rule exists only as a falsifiable candidate — sweeps gate it when landed |

## D. The pruners (method.md §6, last_draw_rules.md)

Row IDs D1–D5 here are pruner rules — **not** the deck-offset lemmas D1–D3
of last_draw_rules.md; cross-references always name their doc.

| # | Claim | Argued in | Tier | Depends on | Closed by |
|---|---|---|---|---|---|
| D1 | CyclePruner (2-cycle splice) | interaction Table 2 | [x] | — | — |
| D2 | 6.2 kings-only after `RevealEmpty` | interaction §4: reorder induction + drain-safes-first; **open corner**: the filler king may be safe-stacked with all substitutes hole-gated | [~] ⟂ | E2 | P2 instrument (Phase 0); fill-existence lemma ⟂ — contexts vanish in the macro game |
| D3 | 6.3 `{r, twin(r)}` exemption = exactly the reveal's legality delta | interaction §5; exact via L2 | [x] ⟂ | E2 | L1/L2 case discharge (the case tables survive in the shared spine); the rule itself dies with contexts |
| D4 | 6.4a pile_stack → `twin(d)` only | last_draw_rules §5: convergent encode + burial mechanism (Claim B); time-criticality for `twin(d)` | [~] ⟂ | E3 | **measured 2026-09**: convergent-encode + `DeckStack(d)` equivalence + design-exemption machine-checkable in the harness; burial-frequency not yet tagged; necessity proof ⟂ |
| D5 | 6.4b reveal restriction `(mm>>4) ∪ first_layer` | last_draw_rules §2–§4: D1–D3 cover the offset-neutral case; residues R1/R2 named as counterexample shapes | [~] ⟂ | E2 | **measured 2026-09:** P3 implemented (`phase0_streak_witnesses`) — R1 is the common firing mode (24,212 witnessless kills / 801,716 audited streak states), zero verdict flips across 55 flagged games; benign-with-unproven-mechanism; closure proof ⟂ (superseded by the macro rework) |

## E. Search structure

| # | Claim | Argued in | Tier | Depends on | Closed by |
|---|---|---|---|---|---|
| E1 | Search termination | finite states + TP insert-once ⟹ each state expanded once (no DAG property needed) | [x] | — | — |
| E2 | L1 (placement monotonicity) / L2 (reveal legality delta) | interaction doc §3; formula-level | [x] pending case tables | B1 | Lean — small, self-contained |
| E3 | Reachable graph is a DAG modulo broken 2-cycles | method.md §7 + tests/no_cycle.rs (exhaustive per game, 2 seeds) | [~] ⟂ | D-rules | wider manual runs only if Phase 0 fires; the macro graph is a DAG by construction (both moves irreversible) |
| E4 | H2/GHI: insert-once TP is context-independent | interaction §3: regime-disjointness + shallow contexts; residual exposure named | [~] ⟂ | A3 (state-level), D2 (context-level) | ctx-aware TP one-off (Phase 0); the context-level question vanishes with contexts |

## F. Player level

| # | Claim | Argued in | Tier | Depends on | Closed by |
|---|---|---|---|---|---|
| F1 | Candidate paths replay legally on the real (unshuffled) game | lonecli assertion (src/main.rs:211) + encode invariance under determinization; 15,024-game run, zero failures | [x] | A1 | the assertion is the instrument |

## The three choke points

Dependency-wise, everything open bottlenecks on:

1. **B4 — the reshape lemma** (no_pile §5). Unblocks A3, the C1/C2/C4
   literature ports, and the whole "legs 1+2" theorem. Only active claim
   with both a named hard case and a deployed falsifier candidate — and
   architecture-independent, so it is first among equals in Phase 1.
2. **The 6.4 cluster (D4/D5, with D2's corner)** — superseded-by-design:
   the Phase-0 falsifiers decide whether it must be paid off before the
   demolition; otherwise the proof obligation is cancelled, not discharged.
3. **C5/C7 — the unwritten dominances** — deferred, not superseded:
   Phase 2 must check whether the macro candidate generator keeps
   analogues of `is_pure` or the least-stack cascade; if so, they return
   to the proof list. The drain-safes-first lemma (D2/C6's rescue) is ⟂
   with the D-layer.

## Instruments → claims map

| Instrument | Spec at | Claims it decides | Implemented |
|---|---|---|---|
| P1: filtered-empty-but-live logger, tagged by rule pair | interaction §7 item 6 | the composition closure property wholesale | **superseded 2026-09**: naive form measured ~129k events/1.7M states (dead branches are the norm, not the signal); replaced by the verdict-level 2×2 ablation `traverse::tests::phase0_verdict_ablation` (green, 120 games × 2 draws × 4 configs); per-state hooks remain in `traverse` under `Callback::INSTRUMENT` for diagnosis |
| P2: king-fill existence after RevealEmpty | interaction §7 item 7 | D2's corner | diagnostic-only per the same lesson; the informative variant rides with P3 (winning-path check) |
| P3: streak-rescue witnesses + R1/R2 tags + burial frequency | last_draw_rules §6; `traverse::tests::phase0_streak_witnesses` | D4, D5 | **implemented 2026-09**: 24,212 witnessless kills / 801,716 audited streak states, all R1-shaped; verdict sluice green on all flagged games; R1/R2 subtags and TP-witness variant not yet built |
| Relocation-failure counter (unwrap → counted error) | no_pile §5 item 2 (src/convert.rs:63,138,153) | B4 depth | no |
| ctx-aware TP one-off experiment | interaction §7 item 3 | E4 | no |
| Draw-step split ground-truth differential | interaction §7 item 9 | C5 vs C4 attribution | no |
| no_cycle on a wider seed set (manual, slow) | tests/no_cycle.rs | E3 | yes, 2 seeds |

## Migration plan (three phases; the recorded decision)

The sequencing rationale is recorded in the interaction doc's §8 — the
short version: the hardest-to-prove rows are exactly the ones the
commitment game deletes by construction, so they get falsified, not
proven; and the deep theorems are architecture-independent, so they get
funded on the way through.

1. **Phase 0 — falsify first** (days; existing callback machinery).
   Implement P1 + P2 + P3 + the relocation-failure counter on the
   *current* engine; run the reference corpus. Protects the published
   81.95%/47.58% numbers during the transition (this engine is production
   until the macro one matches it verdict-for-verdict); a counterexample
   reroutes everything; the instruments double as the macro acceptance
   harness.
2. **Phase 1 — the shared spine** (architecture-independent; nothing here
   is wasted if the macro later fails): B4 the reshape lemma via the
   normal-form conjecture, twin-expansion first; T; L1/L2 + B1's case
   tables; the B&G safe-stack port (C1/C2/C4's bridge).
3. **Phase 2 — build the commitment game**, proving C1/C2 during
   construction rather than retrofitting, gated on full-corpus verdict
   equality against the current engine and then a fresh 1M-scale
   validation run. Inside Phase 2: check whether the macro candidate
   generator keeps analogues of C5/C7, and repatriate them to the proof
   list if so.

Skipped unless Phase 0 fires: closure proofs for 6.4's R1/R2/Claim B,
the 5.6 cascade writeup, the `is_pure` formalization, drain-safes-first
as a standalone theorem — an instrument catching one of these failing
converts it from a proof obligation into a bug, which is cheaper
information either way.

Snapshot (this writing, 26 rows): [P] 3 (all external, effective [~] until
the port lands) · [x] 11 · [~] 10 · [ ] 2 — with D2–D5, E3, E4 superseded
(⟂) and C6 partially so. Nothing is [P] *for this engine* yet; that is the
lean-verify program.
