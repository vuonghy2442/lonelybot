# lean-census.ps1 — pin the sorry inventory of lean-model/Klondike.
# Run from anywhere: pwsh script/lean-census.ps1
# Exit 0 = inventory unchanged. Exit 1 = DRIFT: a new sorry appeared,
# or a refuted constant re-entered the library. Update $baseline ONLY
# via the orchestrator (FARM.md), with a proof or a witness in hand.
$ErrorActionPreference = 'Stop'
$k = Join-Path (Split-Path $PSScriptRoot -Parent) 'lean-model\Klondike'

# Baseline 2026-09-13 (post waves 8/9/10, post refuted-constant disposal,
# +wave-12 scaffolding: the K-rules closure kills — Klondike/Kills.lean,
# +wave-13 scaffolding: the pile-to-pile restriction — Klondike/Restriction.lean):
$baseline = @{
  'Theorems.lean'  = 1  # solvable_of_pileStack (B4 crux, repaired +hnotlock)
  'Macro.lean'     = 0  # C1 PROVEN 2026-09-13 (def repair: macroSolvable gained the
                        # trailing accommodation — witnesses/MacroC1Witness.lean)
  'Dominance.lean' = 4  # safe_pileStack_dominant, deck_dominance_draw1,
                        # stackPile_safe_prunable, twinPair_placement_equi
                        # (least_redundantStack_dominant PROVEN with the +hsafe
                        # repair, per its wave-11 concern, by the parallel
                        # session 2026-09-13)
  'Kills.lean'     = 0  # wave-12 COMPLETE (K1 + K2 sessions, merged 2026-10-05):
                        # vis_of_safeAccommodates (keystone), State.frontier_spec,
                        # K1_stack_goal_dead — sorry-free, no WF (K1 session;
                        # machinery vis_shadow_play / climb_firstPassage /
                        # find?_prefix_false / Rank.all_split_filter /
                        # vis_of_pileStack / vis_of_stackPile shipped) — and
                        # K2_tableau_goal_dead PROVEN (K2 session; the K1
                        # keystone discharges its sorryAx taint in the merge)
  'Movability.lean' = 1  # +wave-12 K2 session (2026-10-05): §8.1's movability
                        # algebra, Klondike/Movability.lean — the single open row
                        # is Mask.bottomMask_matches_movableOf, the §8.7 owed
                        # equivalence (the engine's mask arithmetic vs the
                        # formula; the Rust side is already bound by
                        # bm_algebra_matches) — plan in the docstring.
                        # Everything else in the file is proven, axiom-clean.
  'Restriction.lean' = 2  # solvableEngine_iff_solvable_of_reachable (B2),
                        # engine_replay_of_pilePile (the replay step)
  'TwinSwap.lean'  = 0  # Board.aboveOf_congr_off PROVEN 2026-09-14 via the
                        # fuel-induction congruence (Board.aboveOf_go_congr_aux)
                        # + acc-monotonicity (Board.aboveOf_go_mono); the twin
                        # line is now sorry-free
                        # (the naive conjugation was REFUTED as stated —
                        #  witnesses/TwinSwapWitness.lean; FARM.md wave 14)
  'TwinExchange.lean' = 1  # +wave-15 scaffolding: the both-cargo exchange —
                        # solvable_cargoTwin_exchange (both-occupied iff) remains.
                        # PROVEN 2026-09-14: solvable_cargoTwin_exchange_bare
                        # (the one-bare companion) via the backward realization
                        # exchangeTwinCargo_pilePile_back — the statement
                        # STRENGTHENED (hwf/hzone dropped, no zone premise);
                        # the exchangeTwin substrate + both transfer
                        # identifications are proven, axiom-clean
  'TwinQuotient.lean' = 2  # +wave-15 quotient layer (commit 9a40232): the licensed
                         # iff + assembly PROVEN; the two remaining are the MERGE
                         # bridges — solvable_of_exchange_merge (TwinQuotient:646)
                         # and solvable_of_exchange_merge_rooted (:2997) — the
                         # [H] crux at WF (FARM.md wave-15 row: normalization or
                         # B&G piecewise bookkeeping)
  # +wave-17 (C2-streamlined session, 2026-10-05; FARM.md Wave-17 / the §7
  # two-option commitment scaffold — Klondike/C2Streamlined.lean): the five
  # play-level pillars specified by docs/macro_formalization.md §7, each with
  # an in-file PROOF PLAN; everything finite/arithmetic around them is PROVEN
  # (P1, the register, the one-step P2 cores, the ray confinement, and the
  # main theorem's case assembly P1–P3 against these pillars):
  'C2Streamlined.lean' = 5  # succ_labeled (P0 labeling — §6.4 extraction + crease),
                           # p2_direct_class (P2 class half — the reproducible scar),
                           # same_pin_closureEq (P3/float class half),
                           # crease_chain_absorbed (§7's named crease — the
                           #   line-force lemma, cited by same_pin_closureEq's plan),
                           # stack_ball_corner (the L1/L2-diligence residue)
}

$drift = $false
$total = 0
Get-ChildItem (Join-Path $k '*.lean') | Sort-Object Name | ForEach-Object {
  $n = @(Select-String -LiteralPath $_.FullName -Pattern ':= sorry').Count
  $total += $n
  $expected = if ($baseline.ContainsKey($_.Name)) { $baseline[$_.Name] } else { 0 }
  if ($n -ne $expected) { $drift = $true }
  '{0,-18} {1,2} sorries (expected {2})' -f $_.Name, $n, $expected
}
$bullets = @(Select-String -Path (Join-Path $k '*.lean') -Pattern '^\s*· sorry\s*$|^\s*sorry\s*$').Count
if ($bullets -ne 0) { $drift = $true }
"bullet sorries:    $bullets (expected 0)"
"total:             $total"
if ($drift) {
  Write-Output 'SORRY INVENTORY DRIFT — new sorry, or a refuted constant re-entered the library.'
  exit 1
}
Write-Output 'inventory pinned: OK'
exit 0
