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
import Orig2.Fork.Class.ForkExist
import Orig2.Fork.Class.ForkMinCross
import Orig2.Fork.Split.ForkMountain
import Orig2.Fork.Split.ForkLandingLocal
import Orig2.Fork.Split.ForkLedger
import Orig2.Fork.Class.ForkTwinLive
import Orig2.Fork.Split.ForkDipPin
import Orig2.Fork.Class.ForkPairRung
import Orig2.Fork.Split.ForkPin
import Orig2.Fork.Class.ForkRungGe
import Orig2.Fork.Class.ForkRungGeGadget
import Orig2.Fork.Local.ForkNormalizeTail
import Orig2.Fiber
import Orig2.Boundary
import Orig2.Boundary.BoundaryForkFree
import Orig2.Boundary.BoundaryMinPath
import Orig2.Fork.Class.ForkTwinAt
import Orig2.Fork.Split.ForkPinAt
import Orig2.Fork.Class.ForkFibMeet
import Orig2.Fork.Class.ForkMeetCover
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
Orig2/Fork/Class/  19 cards  (fork class theory, rung/non-comparability, join/slice)
Orig2/Fork/Local/  13 cards  (letter commutation, normalization, relocation)
Orig2/Fork/Split/  16 cards  (split/tail/landing/pin/mountain/drain/frontier)
Orig2/Fork/Third/   4 cards  (third-suit, survivor, mate, elimination)
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

The live campaign is the **slice / join normal form**:

* `ForklessOneColourClosure` - pair targets have a one-colour-exact upper
  bound (the arbitrary-target form is FALSE);
* `ForklessSliceLUB` / `ForklessSliceMeet` / `SliceFinite` - the exact
  numeric height as a 2D slice computation;
* `MinimalFullJoin` - the least class-mate above the componentwise max.

The old conditional route (`SplitLivePair`, `SameCardRelocation`,
`ReadBracketElim`, `NonforkBracketLocal`, `MountainAtSplits`,
`RaiseBeforePullShortens` and their `SatDifferForkWF_of_*` consumers) was
refuted and retired to `Archive/` on 2026-11-02: the residuals are false,
so the route is vacuous.  It stays restorable and greppable there.

INDEPENDENT OF THAT ROUTE, the fork-Position rigidity results are
**unconditional and retained** in `Fork/Third/ForkThirdHigh.lean`:
`forkThirdRigid_unconditional : ForkThirdRigid`,
`forkPositionRigid_unconditional : ForkPositionRigid`,
`forkFoundRigid_unconditional : ForkFoundRigid`, and "a fork class carries
at most one fork `Position`" (`fork_one_position_of_rigid`), all with axioms
`[propext, Quot.sound]`.  The archived route was only the conditional
`SatDifferForkWF` reduction, never the Position-rigidity proof.

-/
