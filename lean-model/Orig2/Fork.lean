import Orig2.ForkCriticalPair
import Orig2.Cover
import Orig2.ForkClass
import Orig2.LockRung
import Orig2.ForkPosition
import Orig2.ForkThird
import Orig2.ForkThirdHigh
import Orig2.FirstPassage
import Orig2.ForkValley
import Orig2.ForkNoPull
import Orig2.ForkDrain
import Orig2.ForkOneSlide
import Orig2.ForkSafeTransport
import Orig2.ForkOneSlideLive
import Orig2.ForkSplit
import Orig2.ForkCommute

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
* `ForkThirdHigh` — `ForkThirdRigidHigh` PROVED, including the king
  slice (`KingExodusSeated` via the `KingKeep` invariant); hence
  unconditional `ForkThirdRigid`, `ForkPositionRigid`,
  `ForkFoundRigid`, and "a fork class carries at most one fork
  `Position`".
* `FirstPassage` — the per-suit first-passage ledger for the
  `SatDifferFork` dip (first passage, first rise, flat seat at the
  climb).
* `ForkValley` — the local valley-turn cancellations: a same-card
  `pull ; raise` turn deletes, a fork valley entered by its raisable
  twin deletes, and the only pull into / raise out of a fork is the
  raisable twin.
* `ForkNoPull` — a pull enables only its own card's raise.
* `ForkDrain` — raising a rank-`≥ r` card of another suit preserves
  `¬ CanRaise` of a blocked card, including the rank condition that
  removes the cover.
* `ForkOneSlide` — the unconditional one-slide safe cargo path: a
  blocked S-live card is one slide of its cover onto its twin from
  raisable.
* `ForkSafeTransport` — `CanRaiseS` is preserved by a high raise, with
  the necessary side condition `c ≠ x.twin`.

This module is an umbrella only; the cards themselves are unchanged.
-/
