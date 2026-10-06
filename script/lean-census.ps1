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
  'Movability.lean' = 0  # §8.7 PAID 2026-10-05 (movability-equivalence session):
                        # Mask.bottomMask_matches_movableOf PROVEN — the engine's
                        # mask arithmetic IS §8.1's formula, per card, at every
                        # (vis, locked) grid, by the docstring's decode plan (the
                        # layout battery as grid decides, the owner-unique reads
                        # via maskIndex injectivity, the 16-case §8.1 skeleton,
                        # the pair-true twins routed through movableOf_flipSuit).
                        # File sorry-free, theorem chain axiom-clean
                        # [propext, Quot.sound].  The Rust side stays bound by
                        # bm_algebra_matches (src-side, shipped).
  'Restriction.lean' = 1  # wave-22 (b2-residue session, 2026-10-06): the residue
                         # SHARPENED — the bare-at-rung head case is PROVEN
                         # (pilePile_via_foundation: the two-move foundation detour
                         # lands on the very pilePile successor, axiom-clean
                         # [propext, Quot.sound]; the measure skeleton
                         # replay_head_len resolves each pilePile head by the
                         # geometry split).  Both B2 rows (statements unchanged
                         # from wave 21) now rest on the single named
                         # arrangement_tail_residue ALONE (the off-rung bare
                         # relocation + the covered carrier — precisely
                         # no_pile_to_pile.md §5's arrangement-tail rewrite;
                         # the wave-22 paragraph plan at its site; case 3 stays
                         # closed by the wave-19B probe).
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
  # +wave-17 (C2-streamlined session, 2026-10-05) landed the five play-level
  # pillars with proof plans. +wave-18 (the 2026-10-05 C2-closure session;
  # FARM.md Wave-18 row) refute-probed them: FOUR were FALSE as stated and
  # left the library per the refutation protocol — succ_labeled,
  # p2_direct_class, same_pin_closureEq, crease_chain_absorbed, and with them
  # the as-stated c2_two_option (witnesses/C2KingAnchorWitness.lean: a
  # climb-blocked stocked king whose anchor landings are pairwise
  # closure-separated; the negated as-stated universals live there as
  # wk_c2 / wk_same_pin / wk_p2_direct / wk_crease_as_stated_false). In their
  # place: commitTableau_class (C2Streamlined §9.5 — the destination collapse
  # at the commitment level, the stackable-rung regime, PROVEN via the
  # two-move foundation shuttle) and the CONDITIONAL c2_two_option whose
  # hypotheses spell the play-level content explicitly (the hlab/hp2/hpin/
  # hball premises; the register/pigeonhole/arm-labeling assembly stays
  # PROVEN). stack_ball_corner's content survives as the hball premise
  # (believed true, never refuted, still unpinned):
  'C2Streamlined.lean' = 0  # wave-18: the pillar rows are gone — 4 refuted
                             # with the witness, 1 re-homed as a premise; the
                             # file is sorry-free and axiom-clean
  # +wave-18 (the catchup-residue session, 2026-10-05; FARM.md wave-18 — the
  # L1/O3(ii) general mixed window + its iff LANDED, TwinSwapCompletion owned
  # in place; the two remaining are the named reductions with in-file plans):
   'TwinSwapCompletion.lean' = 1  # wave-20 (midaccess-reinstatement session,
                                 # 2026-10-05): State.mid_access_of_noSeat
                                 # PROVEN ax-clean (the repaired no-landing ->
                                 # haccess derivation, drafted wave 19 in the
                                 # attic, reinstated + elaborated; depends on
                                 # [propext, Classical.choice, Quot.sound]).
                                 # Remaining:
                                 # State.sweep_covered_corner_safety (the §6.5
                                 #   covered-corner sweep-word safety — reduce to
                                 #   the both-occupied exchange family; the cell
                                 #   identification exchangeTwinCargo_flip_cover
                                 #   is PROVEN ax-clean)
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
