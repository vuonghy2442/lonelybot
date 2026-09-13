# lean-census.ps1 — pin the sorry inventory of lean-model/Klondike.
# Run from anywhere: pwsh script/lean-census.ps1
# Exit 0 = inventory unchanged. Exit 1 = DRIFT: a new sorry appeared,
# or a refuted constant re-entered the library. Update $baseline ONLY
# via the orchestrator (FARM.md), with a proof or a witness in hand.
$ErrorActionPreference = 'Stop'
$k = Join-Path (Split-Path $PSScriptRoot -Parent) 'lean-model\Klondike'

# Baseline 2026-09-13 (post waves 8/9/10, post refuted-constant disposal):
$baseline = @{
  'Theorems.lean'  = 1  # solvable_of_pileStack (B4 crux, repaired +hnotlock)
  'Macro.lean'     = 1  # solvableEngine_iff_macro (C1)
  'Dominance.lean' = 5  # safe_pileStack_dominant, least_redundantStack_dominant,
                        # deck_dominance_draw1, stackPile_safe_prunable,
                        # twinPair_placement_equi
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
