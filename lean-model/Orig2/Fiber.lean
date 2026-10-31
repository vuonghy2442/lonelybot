import Orig2.ArmFiber
import Orig2.ArmSplit
import Orig2.SWDichotomy
import Orig2.FiberHierarchy

/-!
# Orig2.Fiber — the fiber hierarchy umbrella

The cargo/fiber side of the macro class:

* `ArmFiber` — `BareCargoEquiv` as a setoid, `SatArm`, `ForkLive`,
  `ArmDichotomy` implications, the forkless campaign theorem.
* `ArmSplit` — `ArmDichotomy ↔ SatDifferFork ∧ SatEqualFork`, the
  forkless-normalization route, and the abstract draw obstruction.
* `SWDichotomy` — the flat-fiber repair (`BareFlatEquiv` = `FlatSpan`),
  `ArmDichotomySW`, `SatEqualCargoSW`, `forkless_found_unique_SW`.
* `FiberHierarchy` — the generic `MoveFiber M` definition and the
  bridges `CargoSpan ↔ BareCargoEquiv`, `FlatSpan ↔ BareFlatEquiv`,
  `MacroSpan ↔ sameOrbitSetoid`, plus the rung readout quotient and
  `Position = MacroSpan × RungClass`.

This module is an umbrella only; the cards themselves are unchanged.
-/
