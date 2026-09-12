# Soundness ledger — the rigor status of every claim

A single index: what each soundness-bearing claim is, where it is argued,
how close it is to rigorous, and what closes it. Details live in the
specialized docs; this file maps claims to tiers, not proofs. Update a row's
tier when the underlying doc moves — a stale ledger is worse than none.

- [method.md](method.md) — the method itself (rules, engineering)
- [no_pile_to_pile.md](no_pile_to_pile.md) — the move-set restriction theorem (legs 1+2)
- [pruning_dominance_interaction.md](pruning_dominance_interaction.md) — the D × P × TP composition
- [last_draw_rules.md](last_draw_rules.md) — the `last_draw` streak rules (6.4)
- [macro_formalization.md](macro_formalization.md) — the macro/commitment rework
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
| C6 | Twin-pair collapse (5.5) | T-equivalence + free_slot = placements onto the pair (L1); dropped KING_MASK rescued by drain-safes-first | [~] | A4, E2 | T + drain-safes proof |
| C7 | Least-stack cascade (5.6) | intent comments only (src/state.rs:222-286) | [ ] | A4, C3 | the TODO(vuong) writeup — the least-argued rule left |
| C8 | King / empty-pile rules (5.7) | = B3 + the free_slot king gate | [x] | B3 | — |

## D. The pruners (method.md §6, last_draw_rules.md)

Row IDs D1–D5 here are pruner rules — **not** the deck-offset lemmas D1–D3
of last_draw_rules.md; cross-references always name their doc.

| # | Claim | Argued in | Tier | Depends on | Closed by |
|---|---|---|---|---|---|
| D1 | CyclePruner (2-cycle splice) | interaction Table 2 | [x] | — | — |
| D2 | 6.2 kings-only after `RevealEmpty` | interaction §4: reorder induction + drain-safes-first; **open corner**: the filler king may be safe-stacked with all substitutes hole-gated | [~] | E2 | P2 instrument (falsifiable); fill-existence lemma |
| D3 | 6.3 `{r, twin(r)}` exemption = exactly the reveal's legality delta | interaction §5; exact via L2 | [x] | E2 | L1/L2 case discharge |
| D4 | 6.4a pile_stack → `twin(d)` only | last_draw_rules §5: convergent encode + burial mechanism (Claim B); time-criticality for `twin(d)` | [~] | E3 | burial-frequency measurement (P3) + necessity direction |
| D5 | 6.4b reveal restriction `(mm>>4) ∪ first_layer` | last_draw_rules §2–§4: D1–D3 cover the offset-neutral case; residues R1/R2 named as counterexample shapes | [~] | E2 | P3 extension (§6 spec) + R1/R2 discharge |

## E. Search structure

| # | Claim | Argued in | Tier | Depends on | Closed by |
|---|---|---|---|---|---|
| E1 | Search termination | finite states + TP insert-once ⟹ each state expanded once (no DAG property needed) | [x] | — | — |
| E2 | L1 (placement monotonicity) / L2 (reveal legality delta) | interaction doc §3; formula-level | [x] pending case tables | B1 | Lean — small, self-contained |
| E3 | Reachable graph is a DAG modulo broken 2-cycles | method.md §7 + tests/no_cycle.rs (exhaustive per game, 2 seeds) | [~] | D-rules | wider manual runs |
| E4 | H2/GHI: insert-once TP is context-independent | interaction §3: regime-disjointness + shallow contexts; residual exposure named | [~] | A3 (state-level), D2 (context-level) | ctx-aware TP one-off experiment; P1 |

## F. Player level

| # | Claim | Argued in | Tier | Depends on | Closed by |
|---|---|---|---|---|---|
| F1 | Candidate paths replay legally on the real (unshuffled) game | lonecli assertion (src/main.rs:211) + encode invariance under determinization; 15,024-game run, zero failures | [x] | A1 | the assertion is the instrument |

## The three choke points

Dependency-wise, everything open bottlenecks on:

1. **B4 — the reshape lemma** (no_pile §5). Unblocks A3, the C1/C2/C4
   literature ports, and the whole "legs 1+2" theorem. Only active claim
   with both a named hard case and a deployed falsifier candidate.
2. **The 6.4 residues and Claim B** (D4/D5). Triangulated, not discharged;
   the P3 extension measures whether R1/R2 ever fire.
3. **The unwritten-dominance cluster: C5 (`is_pure`, draw ≥ 2) and C7
   (least-stack cascade)** — the only rules left with no argument beyond
   intent/comments, plus the drain-safes-first lemma still stated but
   unproven (it backs D2, C6).

## Instruments → claims map

| Instrument | Spec at | Claims it decides | Implemented |
|---|---|---|---|
| P1: filtered-empty-but-live logger, tagged by rule pair | interaction §7 item 6 | the composition closure property wholesale (D2, D4, D5, C2×C-cascade, anything unanticipated) | no |
| P2: king-fill existence after RevealEmpty | interaction §7 item 7 | D2's corner | no |
| P3: streak-rescue witnesses + R1/R2 tags + burial frequency | last_draw_rules §6 | D4, D5 | no |
| Relocation-failure counter (unwrap → counted error) | no_pile §5 item 2 (src/convert.rs:63,138,153) | B4 depth | no |
| ctx-aware TP one-off experiment | interaction §7 item 3 | E4 | no |
| Draw-step split ground-truth differential | interaction §7 item 9 | C5 vs C4 attribution | no |
| no_cycle on a wider seed set (manual, slow) | tests/no_cycle.rs | E3 | yes, 2 seeds |

## Migration plan (the order to move rows up)

1. Implement P1 + P2 + the relocation-failure counter (days; existing
   callback machinery). Zero-logs over the reference corpus moves several
   [~] rows to "never observed to fail at the decision point".
2. Write up C5 and C7 properly (the only [ ] rows; thinking, not code).
3. Discharge E2 and B1's case tables in prose or Lean — mechanical.
4. Lean obligations 2–3 of no_pile §9 (compression, relabeling) — small.
5. Attack B4 (normal-form conjecture; twin-expansion first) — the one
   worthwhile fight.
6. T (A4) in Lean — needed by B4's hard case and C6 either way.

Snapshot (this writing, 26 rows): [P] 3 (all external, effective [~] until
the port lands) · [x] 11 · [~] 10 · [ ] 2. Nothing is [P] *for this engine*
yet; that is the lean-verify program.
