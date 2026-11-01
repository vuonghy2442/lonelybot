import Orig2.Substrate
import Orig2.Fork
import Orig2.ForkDrainInduction
import Orig2.ForkDrainClose
import Orig2.ForkBridge
import Orig2.ForkSplitResidual
import Orig2.ForkLivePair
import Orig2.ForkMechanism
import Orig2.ForkTailCover
import Orig2.ForkLanding
import Orig2.ForkLocator
import Orig2.ForkLocatorRefute
import Orig2.ForkElim
import Orig2.ForkNonfork
import Orig2.ForkReadBracket
import Orig2.ForkExistRefute
import Orig2.ForkExist
import Orig2.ForkMinCross
import Orig2.ForkMountain
import Orig2.ForkLandingLocal
import Orig2.ForkLedger
import Orig2.ForkLedgerResidual
import Orig2.ForkThirdLive
import Orig2.ForkThirdCrossing
import Orig2.ForkThirdResidual
import Orig2.ForkTwinLive
import Orig2.ForkDipPin
import Orig2.ForkMountainAccount
import Orig2.ForkMountainShape
import Orig2.ForkSurvivor
import Orig2.ForkPairRung
import Orig2.ForkEmptyTail
import Orig2.ForkPin
import Orig2.ForkMate
import Orig2.ForkRaiseLeft
import Orig2.ForkRungGe
import Orig2.ForkRungGePair
import Orig2.ForkRungGeGadget
import Orig2.ForkNormalizeTail
import Orig2.Fiber
import Orig2.Boundary
import Orig2.BoundaryForkFree
import Orig2.BoundaryMinPath
import Orig2.ForkFrontier
import Orig2.ForkSlideFwd
import Orig2.ForkDirect
import Orig2.ForkWindow
import Orig2.ForkTwinAt
import Orig2.ForkNoSelf
import Orig2.ForkPinAt
import Orig2.ForkNoMate
import Orig2.ForkRankFloor
import Orig2.ForkRankFloorAttack
import Orig2.ForkJoint
import Orig2.ForkPinRight
import Orig2.ForkRelocate
import Orig2.ForkMountainRefute
import Orig2.ForkKingGadget
import Orig2.ForkRelocGadget
import Orig2.ForkStraddle
import Orig2.ForkPullSwaps
import Orig2.ForkMountainGate
import Orig2.ForkGatedTower
import Orig2.ForkChoiceFree
import Orig2.ForkBaseEnabling

/-!
# Orig2 — the proof root

The root is now four topic umbrellas over the certified substrate:

```text
Orig2
├─ Substrate    the game core, the fiber transfer, the claims ledger,
│               the orbit factor, the cargo bridge, the Position grid
├─ Fork         the local two-raise dichotomy, the cover card, the
│               class-level fork theorem, and the Position reduction
├─ Fiber        the cargo/flat fiber hierarchy, the arm split, the
│               SW draw repair, and the generic MoveFiber bridge
└─ Boundary     the vcS/vcT equal-rung certificate and the draw
                counterexample that fixes the target statement
```

The earlier consolidated proof is `FiberTransfer` alone; everything else
— the campaign lanes, the old conditional capstone, the king/floater/
rider machinery — is retired to `Archive/`.  The ledger (`Claims`,
`ClaimsScrutiny`) remains the statement book.

The live campaign targets are:

* `SatDifferFork` — differing-rung saturated class-mates force a fork.
* `ForkPositionRigid` — all forks of a class share one Position; reduced
  to `ForkThirdRigid`.
* `ArmDichotomySW` — the flat-fiber, draw-corrected arm dichotomy;
  equivalent to `SatDifferFork ∧ SatEqualCargoSW`.
-/
