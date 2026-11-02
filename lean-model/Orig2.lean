import Orig2.Substrate
import Orig2.Fork
import Orig2.Fork.Split.ForkDrainInduction
import Orig2.Fork.Split.ForkDrainClose
import Orig2.Fork.Split.ForkBridge
import Orig2.Fork.Split.ForkSplitResidual
import Orig2.Fork.Class.ForkLivePair
import Orig2.Fork.Local.ForkMechanism
import Orig2.Fork.Split.ForkTailCover
import Orig2.Fork.Split.ForkLanding
import Orig2.Fork.Split.ForkLocator
import Orig2.Fork.Third.ForkElim
import Orig2.Fork.Third.ForkNonfork
import Orig2.Fork.Class.ForkReadBracket
import Orig2.Fork.Class.ForkExistRefute
import Orig2.Fork.Class.ForkExist
import Orig2.Fork.Class.ForkMinCross
import Orig2.Fork.Split.ForkMountain
import Orig2.Fork.Split.ForkLandingLocal
import Orig2.Fork.Split.ForkLedger
import Orig2.Fork.Third.ForkThirdLive
import Orig2.Fork.Third.ForkThirdCrossing
import Orig2.Fork.Third.ForkThirdResidual
import Orig2.Fork.Class.ForkTwinLive
import Orig2.Fork.Split.ForkDipPin
import Orig2.Fork.Split.ForkMountainAccount
import Orig2.Fork.Split.ForkMountainShape
import Orig2.Fork.Third.ForkSurvivor
import Orig2.Fork.Class.ForkPairRung
import Orig2.Fork.Split.ForkEmptyTail
import Orig2.Fork.Split.ForkPin
import Orig2.Fork.Third.ForkMate
import Orig2.Fork.Local.ForkRaiseLeft
import Orig2.Fork.Class.ForkRungGe
import Orig2.Fork.Class.ForkRungGeGadget
import Orig2.Fork.Local.ForkNormalizeTail
import Orig2.Fiber
import Orig2.Boundary
import Orig2.Boundary.BoundaryForkFree
import Orig2.Boundary.BoundaryMinPath
import Orig2.Fork.Split.ForkFrontier
import Orig2.Fork.Local.ForkSlideFwd
import Orig2.Fork.Local.ForkDirect
import Orig2.Fork.Local.ForkWindow
import Orig2.Fork.Class.ForkTwinAt
import Orig2.Fork.Local.ForkNoSelf
import Orig2.Fork.Split.ForkPinAt
import Orig2.Fork.Third.ForkNoMate
import Orig2.Fork.Class.ForkRankFloor
import Orig2.Fork.Class.ForkRankFloorAttack
import Orig2.Fork.Split.ForkJoint
import Orig2.Fork.Split.ForkPinRight
import Orig2.Fork.Local.ForkRelocate
import Orig2.Fork.Local.ForkStraddle
import Orig2.Fork.Local.ForkPullSwaps
import Orig2.Fork.Split.ForkGatedTower
import Orig2.Fork.Split.ForkBaseEnabling
import Orig2.Fork.Split.ForkMtnExists
import Orig2.Fork.Split.ForkTailHead
import Orig2.Fork.Local.ForkChain
import Orig2.Fork.Class.ForkCanon
import Orig2.Fork.Local.ForkBlocks
import Orig2.Fork.Third.ForkFace1
import Orig2.Fork.Class.ForkFibMeet
import Orig2.Fork.Class.ForkMeetCover
import Orig2.Fork.Class.ForkNonComp
import Orig2.Fork.Class.ForkTwinJoin
import Orig2.Fork.Class.ForkRaiseOnly
import Orig2.Fork.Class.ForkOneColourClosure
import Orig2.Fork.Class.ForkMin
import Orig2.Fork.Class.ForkDecide

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
Orig2/Fork/Class/  24 cards  (fork class theory, rung/non-comparability, join/slice)
Orig2/Fork/Local/  23 cards  (letter commutation, normalization, relocation)
Orig2/Fork/Split/  26 cards  (split/tail/landing/pin/mountain/drain/frontier)
Orig2/Fork/Third/  11 cards  (third-suit, survivor, mate, elimination)
Orig2/Fiber/       26 cards  (fiber, orbit, king, twin machinery)
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
