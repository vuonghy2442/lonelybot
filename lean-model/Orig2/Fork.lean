import Orig2.Fork.ForkCriticalPair
import Orig2.Fork.Cover
import Orig2.Fork.ForkClass
import Orig2.Fiber.LockRung
import Orig2.Fork.ForkPosition
import Orig2.Fork.ForkThird
import Orig2.Fork.ForkThirdHigh
import Orig2.Fork.FirstPassage
import Orig2.Fork.ForkValley
import Orig2.Fork.ForkNoPull
import Orig2.Fork.ForkDrain
import Orig2.Fork.ForkOneSlide
import Orig2.Fork.ForkSafeTransport
import Orig2.Fork.ForkOneSlideLive
import Orig2.Fork.ForkSplit
import Orig2.Fork.ForkCommute
import Orig2.Fork.ForkCommuteSlide
import Orig2.Fork.ForkBubble
import Orig2.Fork.ForkNormalize

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
* `ForkSafeTransport` - `CanRaiseS` is preserved by a high raise, with
  the necessary side condition `c ≠ x.twin`.
* `ForkCommuteSlide` - the two remaining slide squares: `slide/pull`
  and `slide/raise` (unconditional; the `slide/slide` square is false
  without `c1 ≠ c2` and is deliberately not stated).
* `ForkBubble` — the play-level bubbling kit: `swap_at`, `bubble_one`,
  `bracket_delete_at`, the raise/pull normal form, and the inversion
  measure.
* `ForkNormalize` — the directional window writers and the conditional
  bracket normalizer (`crossingBracketNormalizer_of_commutes`, its
  `NoSlide` corollary, and the explicit slide-row reduction).

This module is an umbrella only; the cards themselves are unchanged.
-/
