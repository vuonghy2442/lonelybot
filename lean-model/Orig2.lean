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
import Orig2.ForkNormalizeTail
import Orig2.Fiber
import Orig2.Boundary
import Orig2.BoundaryForkFree
import Orig2.BoundaryMinPath

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
