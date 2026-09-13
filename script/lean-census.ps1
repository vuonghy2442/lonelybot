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
  'Dominance.lean' = 5  # safe_pileStack_dominant, least_redundantStack_dominant,
                        # deck_dominance_draw1, stackPile_safe_prunable,
                        # twinPair_placement_equi
  'Kills.lean'     = 4  # vis_of_safeAccommodates (keystone), State.frontier_spec,
                        # K1_stack_goal_dead, K2_tableau_goal_dead
  'Restriction.lean' = 2  # solvableEngine_iff_solvable_of_reachable (B2),
                        # engine_replay_of_pilePile (the replay step)
  'TwinSwap.lean'  = 8  # crown `solvable_swapTwin` is PROVEN-modulo-3-rows;
                        # open rows: solvable_pileStack_twin_iff (pivot),
                        # solvable_iff_canonicalStack, apply_swapFull_of_avoids,
                        # solvable_cover_twin_iff, swapTwin_wf,
                        # swapTwin_swapTwin, simTwin_step [H], simTwin_runWin
                        # (the naive conjugation was REFUTED as stated —
                        #  witnesses/TwinSwapWitness.lean; FARM.md wave 14)
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
