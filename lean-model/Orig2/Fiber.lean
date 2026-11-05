import Orig2.Fiber.ArmFiber
import Orig2.Fiber.ArmSplit
import Orig2.Fiber.SWDichotomy
import Orig2.Fiber.FiberHierarchy

/-!
# Orig2.Fiber — the fiber hierarchy umbrella

The cargo/fiber side of the macro class:

* `ArmFiber` — `BareCargoEquiv` invariants, `ForkLive`, and `forkLikePos`
  (the cargo `ArmDichotomy` is refuted in `Orig2/Boundary.lean`).
* `ArmSplit` — the generic `ArmDichotomyFor R` split and the cargo draw
  obstruction (`ArmDichotomySW` is the live flat-fiber repair).
* `SWDichotomy` — the flat-fiber repair (`BareFlatEquiv` = `FlatSpan`),
  `ArmDichotomySW`, `SatEqualCargoSW`, `forkless_found_unique_SW`.
* `FiberHierarchy` — the generic `MoveFiber M` definition and the
  bridges `CargoSpan ↔ BareCargoEquiv`, `FlatSpan ↔ BareFlatEquiv`,
  `MacroSpan ↔ sameOrbitSetoid`, plus the rung readout quotient and
  `Position = MacroSpan × RungClass`.

This module is an umbrella only; the cards themselves are unchanged.
-/
