import Orig2.ForkCriticalPair
import Orig2.Cover
import Orig2.ForkClass
import Orig2.LockRung
import Orig2.ForkPosition
import Orig2.ForkThird
import Orig2.ForkThirdHigh
import Orig2.FirstPassage

/-!
# Orig2.Fork — the fork theory umbrella

The local and class-level fork cards, in dependency order:

* `ForkCriticalPair` — the two-raise dichotomy, the rung obstruction,
  the twin-raise square, the cover lock.
* `Cover` — the cover pin, the cover-top/base rows, the cascade ledger.
* `ForkClass` — the conditional class theorem from `CoverToken +
  OneFounding`.
* `LockRung` — the two residues discharged; unconditional
  `fork_label_class`, `twinPair_founds`, `coverSuit_rung_eq`.
* `ForkPosition` — `ForkPositionRigid` / `ForkThirdRigid`, the
  under-card structure, and `Position = class × RungEq`.
* `ForkThird` — the third-suit split: cover-suit rigidity, the low-rung
  lock, and the reduction of `ForkThirdRigid` to
  `ForkThirdRigidHigh`.
* `ForkThirdHigh` — the non-king half of `ForkThirdRigidHigh` proved;
  the king slice reduced to `KingExodusSeated`.
* `FirstPassage` — the per-suit first-passage ledger for the
  `SatDifferFork` dip (first passage, first rise, flat seat at the
  climb).

This module is an umbrella only; the cards themselves are unchanged.
-/
