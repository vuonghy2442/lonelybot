# Archive — superseded route cards (owner decree 2026-10-25)

Moved here from `Orig2/` per the owner's cleanup decision. These cards
are RETIRED, not deleted: the falsity/audit discipline is preserved
(anything refuted stays greppable here), and a card can be restored by
moving it back to `Orig2/` and re-adding its import line.

Nothing in the build imports any card here; `lake build Orig2` does not
see this folder.

## The cards

| card | why retired |
|---|---|
| `TwinShape4Terminal` | mid-edit/broken (unsolved goals at `:151`/`:160`/`:162`); superseded by the landed `TwinShape4TerminalClose` (on the proof spine) |
| `TwinSingleDetour` | standalone duplicate: root `PairFreeOrbit` clashes with `TwinPairFreeClass` (CLEANUP_PLAN §5, which prescribed this archive move); canonical cases superseded by `TwinLastPull`/`TwinDetourArbitraryMid` |
| `TwinNormalizeSplit` | superseded normalization split; imported only by `Orig2.lean` |
| `TwinConcreteSelfSwap` | superseded rider-route segment (world-B 5L); replaced by the point-transfer route |
| `TwinBothCoveredPath` | the rider/recipe route's both-covered capstone (commit `c71df84`) — superseded by the point-transfer + first-touch reduction route |

## What was deliberately NOT archived (the importer census)

Off the mainline spine but load-bearing for in-flight campaign
material, per the 2026-10-25 importer scan:

- the excursion engine cards (`TwinInteriorWindow`, `TwinStraddleClose`,
  `TwinTerminalLadder`, `TwinBalancedMiddle`, `TwinRaiseInterior`,
  `TwinCrossedSlideInterior`) and their substrate (`TwinCoverMotive`,
  `TwinCoverIrrelevant`, `TwinMirrorHop`, `TwinMirrorReroute`,
  `TwinBalancedRaise` — imported by the kept engines/umbrella);
- the published-but-unlanded ticket material (`TwinInterleavedPrefix`,
  `TwinPreludeClosure` — cited by `TwinCampaignAssembly`'s wiring);
- the alternate tickets (`TwinFiberQuotient`, `TwinCampaignAssembly`,
  `TwinCrossingArm`, `TwinExchangeNoSlide`);
- the universal-property layer (`TwinBritton`, `TwinBrittonConfluence`);
- the ledger and facades (`Claims`, `ClaimsScrutiny`, `FlagShip`,
  `TwinAttachment`).

A second pass can widen this set once the campaign lands.

## The campaign wave (2026-10-25, owner decree - the lane retired)

The 53 excursion/attachment lane cards moved here the same day the
campaign target closed (`fiber_transfer_corrected`, proven by the
last-return route - see FARM_MEMORY and Orig2/FiberTransfer.lean):
the TwinAtt* functor world, the cover tables, the both-unseated
arms, the Britton calculus, the excursion-closure lane, the
campaign pad, the fiber quotient skeleton, the mirror routes, the
engines.  All alternate routes to a closed target - superseded, not
deleted.  The ledger doors (Claims, ClaimsScrutiny, FlagShip) stay
in Orig2/ as the statement book.

## The consolidation retirees (2026-10-25)

`Orig2.FiberTransfer.lean` (the new card) consolidates the whole
corrected fiber transfer into ONE file riding only the certified
tracked substrate (fifteen imports); the seventeen cards below are
therefore superseded.  Axiom-clean `[propext, Quot.sound]`, zero
`sorry`, zero `Classical.choice`.

The four-card arc (superseded by the single consolidated card):

| card | why retired |
|---|---|
| `TwinPairFreeTransfer` | the pair-free transfer - restated as FiberTransfer §4 (`swappableIn_transfer_of_pairFreePath`, `fiber_transfer_corrected_of_pairFreePath`) |
| `TwinFirstTouchReduction` | the first-touch reduction - restated as FiberTransfer §6 (`FirstTouchRestart`, `firstTouch_is_raise`, the two transfer reductions) |
| `TwinSelfArm` | the self-arming keystone - restated as FiberTransfer §3 (`nextUp_of_foundToTab`, `reversibleAtW_tabToFound_of_foundToTab`) |
| `TwinLastReturn` | the last-return main proof - restated as FiberTransfer §7 (`firstTouchRestart`, `fiber_transfer_corrected_of_lastReturn`) |

The thirteen dependency cards (their rows restated per-file-kit inside
FiberTransfer with citations; the originals keep the full general
machinery):

| card | row restated in FiberTransfer |
|---|---|
| `TwinPairFreeClass` | `PairFreeOrbit` + `pairFreeOrbit_refl` / `PairFreeOrbit.trans` / `pairFreeOrbit_of_play` (§1) |
| `TwinLastPull` | `notFoundPair_relabelMover`, `pairFreeOrbit_splice_of_pairFree` (§1) |
| `TwinPairFreeRev` | the chop-length arithmetic: `upCards_nodup`, `posOf_take_of_mem`, `posOf_last_eq_length_sub_one`, `found_chop_length_eq_rank` (§2) |
| `TwinForcedCancel` | `walk_cons_inv`, `seatOf_none_of_mem_found` (§5) |
| `TwinFoundationRow` | `raise_found_self`, `seated_inr_rank_ne_king` (§5) |
| `TwinPreludeFunctor` | `canSitOn_twin_left'`, `not_twin_same_parent`, `twin_parent_eq_of_seats` (§5) |
| `TwinCargoKernel` | no row restated - the raise/pull round-trip machinery fed routes the last-return route bypasses |
| `TwinDetourArbitraryMid` | no row restated - the arbitrary-mid detour machinery is bypassed by the reconstruction at the last return |
| `TwinPullLift` | no row restated - the attach-functoriality residual was never consumed by the landed route |
| `TwinRaiseCommute` | no row restated - the same-suit commutation obstructions are sidestepped, not resolved |
| `TwinSuffixCancel` | no row restated - the last-letter residual is subsumed by the last-touch split of §7 |
| `TwinPreludeAssembly` | assembly layer for the retired prelude chain |
| `TwinPreludeCollapse` | assembly layer for the retired prelude chain |

(The §7 foundation-membership rows are likewise cited restatements -
from `TwinAttShapes.lean:1026` and `TwinExcursionClosure.lean:832`,
both retired with the campaign wave above.)

Restore recipe: `git mv` the file back to `Orig2/`, rebuild - the
retired cards were green at HEAD when archived.

## Scratch-card retirees (2026-11-02)

Five cards that were never in the root closure and can never be: each
opens with a bare `import Orig2`, so the root cannot import it back
without a cycle, and no reachable `Orig2/` card imports it.  Their own
headers already mark them as scratch (`READ-ONLY scratch`, `nothing
committed`).  Retired, not deleted - the restore recipe is unchanged
(move back to `Orig2/` and, for a card that shadowed the root, drop the
bare `import Orig2` line first).

| card | why retired |
|---|---|
| `ForkDisj` | scratch disjunctive-clause composition (`Temp/Disj_Branches` companion) |
| `ForkDisjBranches` | scratch branch analysis for `ForkDisj` |
| `ForkPrePull` | scratch `pre ≠ []` lane of `Pin.BottomNotBothRaisable` |
| `ForkSwapOff` | scratch two-pile frame (`SameOff`) transport |
| `ForkSwapOffMain` | scratch frame at a real cover/direct pair |

Deliberately NOT retired in the same pass: the `ForkCert*` cluster (12
cards).  It is the kernel certificate for the cross-suit refutation, built
as an explicit leaf by `Tools/build_crosssuit_cert.ps1` and intentionally
outside `lake build Orig2`; it is audit material, not clutter.  Likewise
`probes/` stays (documented #eval evidence, nothing imported).

## Restored 2026-10-25 (same day, owner directive)

The king arm + orbit kit returned to Orig2/ as the attack kit for
the OPEN original fiber_transfer_corrected (the .inl corners):
KingOrbitFull, KingTrace, KingSwapStrict, KingSwapAssembly,
AnchorRelabel, FloatOrbit, OrbitFactor.  They build green
standalone; the root stays minimal (import Orig2.FiberTransfer only).
