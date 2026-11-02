import Orig2.Substrate
import Orig2.Fork
import Orig2.Fork.ForkDrainInduction
import Orig2.Fork.ForkDrainClose
import Orig2.Fork.ForkBridge
import Orig2.Fork.ForkSplitResidual
import Orig2.Fork.ForkLivePair
import Orig2.Fork.ForkMechanism
import Orig2.Fork.ForkTailCover
import Orig2.Fork.ForkLanding
import Orig2.Fork.ForkLocator
import Orig2.Fork.ForkElim
import Orig2.Fork.ForkNonfork
import Orig2.Fork.ForkReadBracket
import Orig2.Fork.ForkExistRefute
import Orig2.Fork.ForkExist
import Orig2.Fork.ForkMinCross
import Orig2.Fork.ForkMountain
import Orig2.Fork.ForkLandingLocal
import Orig2.Fork.ForkLedger
import Orig2.Fork.ForkThirdLive
import Orig2.Fork.ForkThirdCrossing
import Orig2.Fork.ForkThirdResidual
import Orig2.Fork.ForkTwinLive
import Orig2.Fork.ForkDipPin
import Orig2.Fork.ForkMountainAccount
import Orig2.Fork.ForkMountainShape
import Orig2.Fork.ForkSurvivor
import Orig2.Fork.ForkPairRung
import Orig2.Fork.ForkEmptyTail
import Orig2.Fork.ForkPin
import Orig2.Fork.ForkMate
import Orig2.Fork.ForkRaiseLeft
import Orig2.Fork.ForkRungGe
import Orig2.Fork.ForkRungGePair
import Orig2.Fork.ForkRungGeGadget
import Orig2.Fork.ForkNormalizeTail
import Orig2.Fiber
import Orig2.Boundary
import Orig2.Boundary.BoundaryForkFree
import Orig2.Boundary.BoundaryMinPath
import Orig2.Fork.ForkFrontier
import Orig2.Fork.ForkSlideFwd
import Orig2.Fork.ForkDirect
import Orig2.Fork.ForkWindow
import Orig2.Fork.ForkTwinAt
import Orig2.Fork.ForkNoSelf
import Orig2.Fork.ForkPinAt
import Orig2.Fork.ForkNoMate
import Orig2.Fork.ForkRankFloor
import Orig2.Fork.ForkRankFloorAttack
import Orig2.Fork.ForkJoint
import Orig2.Fork.ForkPinRight
import Orig2.Fork.ForkRelocate
import Orig2.Fork.ForkStraddle
import Orig2.Fork.ForkPullSwaps
import Orig2.Fork.ForkMountainGate
import Orig2.Fork.ForkGatedTower
import Orig2.Fork.ForkBaseEnabling
import Orig2.Fork.ForkLandResReduction
import Orig2.Fork.ForkMtnExists
import Orig2.Fork.ForkTailHead
import Orig2.Fork.ForkCrossSuit
import Orig2.Fork.ForkCrossSuitPure
import Orig2.Fork.ForkChain
import Orig2.Fork.ForkFibreCorridor
import Orig2.Fork.ForkCanon
import Orig2.Fork.ForkBlocks
import Orig2.Fork.ForkFace1
import Orig2.Fork.ForkFibMeet
import Orig2.Fork.ForkMeetCover
import Orig2.Fork.ForkNonComp
import Orig2.Fork.ForkTwinJoin
import Orig2.Fork.ForkRaiseOnly
import Orig2.Fork.ForkOneColourClosure
import Orig2.Fork.ForkMin
import Orig2.Fork.ForkDecide

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

On disk the same four umbrellas group the cards (2026-11-02 layout):

```text
Orig2/Substrate/   12 cards  (game core, kits, Position, Classification)
Orig2/Fork/        90 cards  (the fork campaign)
Orig2/Fiber/       28 cards  (fiber, orbit, king, twin machinery)
Orig2/Boundary/     2 cards  (BoundaryForkFree, BoundaryMinPath)
Orig2/Claims/       3 cards  (Claims, ClaimsScrutiny, Chart)
```

with the umbrella modules `Substrate.lean`, `Fork.lean`, `Fiber.lean`,
`Boundary.lean` kept at the top level of `Orig2/`.

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
