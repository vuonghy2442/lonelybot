import Orig2.Fork.ForkRaiseLeft
import Orig2.Fork.ForkPairRung
import Orig2.Fork.ForkPin
import Orig2.Fork.ForkThirdResidual
import Orig2.Fork.ForkSurvivor
import Orig2.Fork.ForkLanding
import Orig2.Fork.ForkMechanism
import Orig2.Fork.ForkExist
import Orig2.Fork.ForkMinCross

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-!
# Orig2/ForkFrontier — THE FRONTIER CARD

One legible place for the whole campaign: the LIVE residuals (as `def`s in one
namespace, copied verbatim from their homes), the DEAD routes (kernel
refutations, with `file:line`), the MEASURED facts (with numbers), the MINIMAL
hypothesis set for `SatDifferForkWF`, and one composed theorem per route.

This card adds no mathematics: every row below is either a verbatim copy of a
declaration that already exists (with an `_iff_home` re-export tying it to its
home), a definition introduced here for legibility, or a composition of rows
that are already kernel-checked.  Zero `sorry`, zero `Classical.choice`, zero
`native_decide`, no `axiom`; the battery at the tail must print only `[]`,
`[propext]`, `[Quot.sound]` or `[propext, Quot.sound]`.

## 1. THE LIVE RESIDUALS

Five live objects.  Each is a verbatim copy in this namespace; the docstring of
each copy cites its home, and `<name>_iff_home` re-exports the identity.

| frontier row | home | shape |
|---|---|---|
| `KeepsForward` | `Orig2/Fork/ForkRaiseLeft.lean:145` (`RaiseLeft`) | per-window swap certificate before a `raise c` |
| `KeepsForwardReadSafe` | this file (restriction of the above) | the same on `R12.ReadOK c` windows |
| `LandingThirdSuitFree` | `Orig2/Fork/ForkLanding.lean:194` (`Landing`) | no third-suit S-live card at the pull landing |
| `SplitTwinRungGe` | `Orig2/Fork/ForkPairRung.lean:168` (`PairRungKit`) | one rung inequality at the bottom |
| `BottomBothRaisableBlock` | `Orig2/Fork/ForkDipPin.lean:274` (`BlockMin`) | gated blocker in the both-raisable case |
| `ShortestPlayExists` | `Orig2/Fork/ForkSplit.lean:874` (`ValleyElim`) | the accepted interface hypothesis |

Two important *negative* status remarks, both already in the tree:

* `BottomBothRaisableBlock` is **NOT independent**: it is implied by
  `SplitKit.SplitBlock` (`Pin.bottomBothRaisableBlock_of_splitBlock`,
  `Orig2/Fork/ForkPin.lean:228`, through `Pin.bottomNotBoth_of_splitBlock`,
  `Orig2/Fork/ForkPin.lean:217`).  Keeping it as a frontier row is honest only as a
  *consequence* of the block: the pin lane closes into the block.
* `KeepsForwardReadSafe` is **not a residual at all**: it is a THEOREM at every
  `WF` state with `CanRaise F c` (`keepsForwardReadSafe_holds`, from
  `R12.raiseSwaps_of_read`, `Orig2/Fork/ForkReadBracket.lean:675`).  The live
  content of `KeepsForward` is therefore exactly the NON-read-safe windows —
  the `c`-suit pull / cover / self-slide positions that §6 of
  `Orig2/Fork/ForkRaiseLeft.lean` proves cannot be swapped in either order
  (`not_canRaise_of_pull_same_suit`,
  `step_foundToTab_raiseSt_same_suit`).

### The containment residual: exact equivalences, one one-way strengthening

`Landing.LandingThirdSuitFree` is the frontier residual of this group.  The
equivalences that exist as rows:

* `ThirdLive.thirdBracketRead_iff_landingThirdSuitFree`
  (`Orig2/Fork/ForkThirdResidual.lean:141`) — **exact** (`↔`), so
  `ThirdLive.ThirdBracketRead` is the same residual in bracket form, and both
  directions are re-exported here.
* `Surv.survivorMateBracket_thirdBracketRead` (`Orig2/Fork/ForkSurvivor.lean:513`) —
  **one way only** (`SurvivorMateBracket → ThirdBracketRead`).  The brief lists
  the three as "equivalent"; that is not what the tree proves.  The pinned
  form pins the bracket card to `e`'s rank-mate (`e = z ∨ e = z.twin`), which
  the bracket form does not, so `SurvivorMateBracket` is a *strengthening*.  No
  row produces the reverse; this card does not invent one.
* `Surv.splitHyp_not_readBracket` (`Orig2/Fork/ForkMate.lean:62`) — at ANY `SplitHyp`
  there is **no** read-safe same-card bracket for any `z`.  Consequence: there
  is no bracket route to the containment.  `ThirdBracketRead`'s content is
  exactly "no violation", i.e. the containment itself, so the containment must
  be attacked directly (or by a new argument), not reduced further.

## 2. THE DEAD ROUTES (kernel refutations; `file:line`)

1. **`Bridge.SplitResidual` — DEAD by binder scope.**
   `SplitKit.not_splitResidual_of_split` (`Orig2/Fork/ForkSplitResidual.lean:301`),
   `SplitKit.not_splitResidual_of_satDiffer` (`:316`).  The hypothesis never
   mentions `left right c d b pre post tail`; it forces `d = c.twin` for
   arbitrary cards, so `c = d = x` gives `x = x.twin`.
2. **`ValleyElim.ValleyCrossingLocator` — DEAD.**
   `LocatorRefute.valleyCrossingLocator_false`
   (`Orig2/ForkLocatorRefute.lean:164`).  Two independent defects: the partner
   letters need not occur (witness `pull A♠ ; raise A♦`, length 2), and
   contiguity is syntactic (commuting produces a different play).  The def is
   marked WITHDRAWN in `Orig2/Fork/ForkSplit.lean:905`.
3. **`CommuteStep.SwapsRightFrom` / `SwapsLeftFrom` — DEAD (counterexample C0).**
   `not_swapsLeftFrom` / `not_swapsRightFrom`
   (`Temp/Transport_Counter.lean:186`, `:191`; write-up
   `Temp/Transport_Report.md`).  At diamonds/spades to 4 with `p1 = [6S,5D]`,
   `raise 5D` and `pull 4S onto 5D` are both legal and reversible, yet one
   covers `5D` and kills the other.  This is why the whole
   commuting-normalizer route is dead as stated.
4. **Ungated `R12.ReadBracketElim` — DEAD.**
   `ExistRefute.not_readBracketElim` (`Orig2/Fork/ForkExistRefute.lean:355`).  The
   four-letter loop `pull 5H→6C ; slide 4C→5H ; slide 4C→5D ; raise 5H`
   returns to its start (`V_eq_u`, `:418`), is not a fork, and the only
   same-card bracket's interior begins with `slide 4C→5H` (base `.inr 5H`, so
   `S2` fails); even the semantic `RaiseSwaps` fails (`no_raise_swap`, `:373`).
5. **Ungated `NonforkKit.NonforkBracketLocal` — DEAD.**
   `ExistRefute.not_nonforkBracketLocal` (`Orig2/Fork/ForkExistRefute.lean:387`),
   same witness loop.  The census missed it because every census pair has
   DIFFERING rungs, which excludes `u = v` loops.
6. **The local pin, "Lemma A" — DEAD.**
   `Temp/TwinPin_Report.md`.  The 2-move gadget's end state `gFin` has
   `gFin_twinLivePair` (`Orig2/Fork/ForkDipPin.lean:555`) but
   `gFin_not_fibreBlockData` (`:615`): a saturated-state witness play reaches
   an exact twin live pair with BOTH twins vanilla-raisable, so
   "exact twin pair ⇒ one twin blocked" is false.
7. **Pointwise fibre block data — DEAD.**
   `Pin.gAce_not_bothRaisableBlock` (`Orig2/Fork/ForkPin.lean:400`) and
   `BlockMin.gFin_not_fibreBlockData` (`Orig2/Fork/ForkDipPin.lean:615`).  `gAce` is
   `WF` with live `{AH,AD}`, both raisable, no ready blocker
   (`fits_ace`: no card fits an ace), and it is literally the landing of the
   pull `AD → 2C` (`gAceMid_landing_both`).  Hence the residual MUST stay gated
   at a minimal bottom.
8. **The ladder-bottom hypothesis — DEAD (probe).**
   `Temp/PullBottom_probe.py`, `Temp/PullBottom_out.txt`.  The fork rung equals
   the componentwise class minimum in **0/13** classes; the class minimum is
   attained in 1/13; a pull is legal at fork states in 100/100.  The fork is an
   INTERSECTION (the twin frontier pair at the play-relative dip), not an
   extremum and not pull-stuck.
9. **The pull-dual — DEAD AS A LAW (probe).**
   `Temp/RealCensus_Report.md`.  At fork states `#slots` (landing slots shared
   by the two foundation tops) is `{0: 460, 1: 704, 2: 576}` over 1740 fork
   states — 33% have TWO slots, in 142 classes including an unplanted random
   board; the toy 100/100 correlation is an artefact.  Only the rung-equality
   half of the pull dual survives, and it is `SplitPairRungEq` in source.
10. **`Surv.splitHyp_not_readBracket` — no bracket route.**
    `Orig2/Fork/ForkMate.lean:62` (plus `splitHyp_self_bracket_impossible`, `:88`,
    and the prefix-internal form, `:178`).  At any `SplitHyp` a read-safe
    same-card bracket would bubble (`R12.raiseSwaps_of_read`) and delete
    (`NonforkKit.bracket_delete_gen`), contradicting `hmin`.

## 3. THE MEASURED FACTS (canonical list, `lean-model/FARM_MEMORY.md`)

* `SplitBlock` at scale: **20 classes / 142 rung-differing pairs / 748 shortest
  plays** — ALL splits, **0** with `CanRaise F c`, **0** with `post = []`;
  **2,339** random boards → 50 shortest plays, 0 violations.
* Identity pairs: **508** shortest splits — 0 adjacent identity pairs, 0
  slide/slide loops on the cover card, 0 identity pairs in `post`.  The cover
  slide is the first letter of `post` in **2900/4010** and the second in
  **1110/4010** ("some slide in post").
* Valley commutation: **916/916** non-twin valley plays commute; nearest
  bracket is `pull c ; raise c` (**588**) or `pull d ; raise d` (**328**), no
  other; syntactic read-invariance `S1` 916/916, `S2` 916/916; the stronger
  slide-source condition fails **400/916** yet the play still commutes.
* Empty tail: **783** splits (658 named/CutSep + 123 random abstract + 2 real
  tableaux) — **0** with `post = []`; **660/660** with `d = c.twin`;
  **0/660** with any `pull d`.
* Pin census: **41** classes (6 named + 14 CutSep + 21 random), **2572**
  minimal splits — 0 both-raisable bottoms, 0 non-twin bottoms, **1468/1468**
  bottoms have exactly one raisable twin and a ready blocker; 48 bottom
  fibres (116 members) with no both-raisable member.
* Pair-rung: **432/432** splits over 27 classes satisfy the pin (and the
  stronger `d = twin(c)`).
* Mountain: **51,116** minimal witness plays (13 boards; unit-cost 1,724 +
  bracket-cost 49,392) — M1 no raise before a pull, M2 per-suit heights never
  up-then-down, M3 a free letter between the last pull and the first raise, all
  exact, zero violations; **0/68** ordered pairs have more than one
  componentwise-minimum rung vector.
* Dip fibre: 13 boards, **1570** fibres, **476** rung groups — `live ⊆
  frontier` 1570/1570; `live` a function of the rung vector 476/476; fork
  fibres are equal-height twin pairs **42/42**.
* Real-tableau census: **4911** saturated-class searches (40 pristine, 4499
  random, 300 planted, 72 planted+filler) — 0 failures; `live ⊆ frontier`
  **38,240/38,240**; `live` a function of the rung vector 0 violations /
  **27,780** groups; every fork fibre has equal twin heights **1740/1740**;
  M1/M2/M3 **9966/9966** (both cost models); unique dip vector = fork rung
  **774/774**; the fork rung is L1 = 1 below each saturated endpoint in
  **370/387** classes (the dip is ONE step, not an arbitrary floor).
* Ladder-bottom, survived at scale: fork rung = class cw-min only **83/387**
  (and **12/316** for `n > 10`).
* Pull-dual, died at scale: see DEAD ROUTE 9.

## 4. THE MINIMAL HYPOTHESIS SET for `SatDifferForkWF`

The tightest set the tree reaches is three clauses plus the interface:

    SatDifferForkWF  ⟸  SplitBlock ∧ SplitContainment ∧ SplitTwinRungPin
                        (+ ValleyElim.ShortestPlayExists)

(`TwinKit.satDifferForkWF_of_block_containment_of_pin`,
`Orig2/Fork/ForkTwinLive.lean:515`, consumed by
`Frontier.satDifferForkWF_of_minimalHypotheses` below).  Each clause is
*necessary* in the sense that it is a projection of the target's own data
(`SplitBlock` is the block, `SplitContainment` the containment, the pin is
implied by the landing live pair: `rungAt_twin_of_landingLivePair`,
`Orig2/Fork/ForkTwinLive.lean:308`).  Equivalent spellings, all proved in the tree:

* `SplitBlock ∧ LandingThirdSuitFree ∧ SplitTwinRungGe` — the form of Route B
  below; `SplitContainment` is derived from `LandingThirdSuitFree` by transport
  along the free tail (`Frontier.splitContainment_of_landingThirdSuitFree`),
  and `SplitTwinRungGe` upgrades to the pin under `SplitBlock`
  (`PairRungKit.splitPairRungEq_iff_ge_of_block`,
  `Orig2/Fork/ForkPairRung.lean:219`).
* `SplitLivePair ∧ BottomNotBothRaisable` — the relaxed pin route
  (`Pin.satDifferForkWF_of_notBoth`, `Orig2/Fork/ForkPin.lean:285`), where
  `BottomNotBothRaisable` is itself a consequence of `SplitBlock`.
* `SplitLivePair ∧ BottomBothRaisableBlock` — the `DipPin` route
  (`BlockMin.satDifferForkWF_of_bothRaisable_drainClosed`,
  `Orig2/Fork/ForkDipPin.lean:371`); `BottomBothRaisableBlock` is NOT independent
  of the block.

**The load-bearing clause is `SplitKit.SplitBlock`.**  Every other live row in
this file is either implied by it, a weakened spelling of part of it, or a
different route to `SplitLivePair`.  Nothing weaker than the three-clause set
is known; the five DEAD ROUTES above are the failed attempts to drop or
replace one of the clauses.

## 5. THE COMPOSED ROUTES

* `satDifferForkWF_of_keepsForward_and_containment` — Route A, the raise-left
  route.  **The brief's declared signature does not typecheck**, and this is
  recorded honestly rather than patched: `KeepsForward` only yields
  `NoEmptyTail` (`RaiseLeft.noEmptyTail_of_keepsForward`), never the cover half
  of `SplitBlock`, and `LandingThirdSuitFree` alone is only the *second* half
  of `LandingAll` (`Landing.landingAll_iff_parts`) — the twin clause
  (`Landing.LandingTwinLive`) is independent.  The composition that DOES check
  therefore carries `Landing.LandingTwinLive` (equivalently, under
  `SplitBlock` + containment, the rung pin `SplitTwinRungPin`), the cover half
  `BlockKit.TailCovers`, and the now-FALSE datum `MountainSplitHyp` (the live
  form is `MountainGate.MountainSplitHypDiffering`).
* `satDifferForkWF_of_gated_containment_and_twinGe` — Route B, exactly as
  declared in the brief: `SplitBlock → LandingThirdSuitFree →
  SplitTwinRungGe → ShortestPlayExists → SatDifferForkWF`.
* `satDifferForkWF_of_splitLivePair_and_notBoth` — Route C, through
  `Pin.satDifferForkWF_of_notBoth`, with the two variants that use the named
  residual `BottomBothRaisableBlock` and the direct `SplitBlock` collapse.
* §4 re-exports the four other committed consumers (`Mech`, `ExistKit`,
  `MinKit`, `BlockMin.DipPin`) so the whole frontier is visible from here.
-/

namespace Frontier

open SplitKit
open NonforkKit

/-! ## §1. The live residuals, verbatim -/

/-- **`KeepsForward F c` — THE LIVE RESIDUAL OF THE RAISE-LEFT ROUTE.**
Verbatim copy of `RaiseLeft.KeepsForward` (`Orig2/Fork/ForkRaiseLeft.lean:145`):
every window `σ` that precedes an occurrence of `raise c` in a witness play out
of `F` satisfies the per-position swap certificate `RaiseSwaps`.

The residual is genuinely non-removable in this form: at a `c`-suit pull
position NEITHER order of the two-letter datum exists
(`RaiseLeft.not_canRaise_of_pull_same_suit`,
`RaiseLeft.step_foundToTab_raiseSt_same_suit`, §6 of the home card).  It IS
discharged on raise-only windows (`RaiseLeft.keepsForward_of_raise_letters`)
and on every read-safe window (`KeepsForwardReadSafe`, below). -/
def KeepsForward (F : State) (c : Card) : Prop :=
  ∀ (σ τ : List Move) (v : State),
    ShufflePlayW F (σ ++ Move.tabToFound c :: τ) v → RaiseSwaps F c σ

/-- The frontier copy is literally the home declaration. -/
theorem keepsForward_iff_home (F : State) (c : Card) :
    Frontier.KeepsForward F c ↔ RaiseLeft.KeepsForward F c :=
  Iff.rfl

/-- **`KeepsForwardReadSafe F c` — THE RESTRICTION THAT IS ACTUALLY NEEDED.**
The same certificate, demanded only on windows whose letters are read-safe for
the pending raise (`R12.ReadOK c`: no pull/raise in `c`'s suit, no letter
landing on `c`, no slide headed by `c`).  This is the "bare-top / read-safe
window" form: the positions excluded are exactly the ones §6 of
`Orig2/Fork/ForkRaiseLeft.lean` proves have no swapped order at all.

This form is NOT an independent residual: `keepsForwardReadSafe_holds` proves
it outright.  The live content of `KeepsForward` is precisely its complement
(the non-read-safe windows). -/
def KeepsForwardReadSafe (F : State) (c : Card) : Prop :=
  ∀ (σ τ : List Move) (v : State),
    ShufflePlayW F (σ ++ Move.tabToFound c :: τ) v →
    (∀ q ∈ σ, R12.ReadOK c q) → RaiseSwaps F c σ

/-- **THE READ-SAFE RESIDUAL IS A THEOREM.**  `R12.raiseSwaps_of_read`
(`Orig2/Fork/ForkReadBracket.lean:675`) builds the whole per-position certificate
from the syntactic read-safety of the window; no minimality, no commutation
row.  So the swap half of the raise-left route costs nothing wherever the
window is read-safe. -/
theorem keepsForwardReadSafe_holds (F : State) (c : Card)
    (hF : F.WF) (hc : CanRaise F c) : KeepsForwardReadSafe F c :=
  fun σ τ v hplay hread => R12.raiseSwaps_of_read hF hplay hc hread

/-- `KeepsForward` implies its read-safe restriction (the restriction is
weaker: it has an extra premise). -/
theorem keepsForward_of_readSafe {F : State} {c : Card} (h : KeepsForward F c) :
    KeepsForwardReadSafe F c :=
  fun σ τ v hplay _ => h σ τ v hplay

/-- **`LandingThirdSuitFree` — THE LIVE CONTAINMENT RESIDUAL.**  Verbatim copy
of `Landing.LandingThirdSuitFree` (`Orig2/Fork/ForkLanding.lean:194`): no card of a
third suit is S-live at a split's pull landing `B`.

This is the frontier residual of the containment group.  It is EXACTLY the
bracket form `ThirdLive.ThirdBracketRead`
(`ThirdLive.thirdBracketRead_iff_landingThirdSuitFree`,
`Orig2/Fork/ForkThirdResidual.lean:141`); the pinned form
`Surv.SurvivorMateBracket` implies it ONE WAY only (see the module docstring). -/
def LandingThirdSuitFree : Prop :=
  ∀ (u v : State) (ρ : List Move) (F : State)
    (left right : List Move) (c d : Card) (b : Base)
    (pre post tail : List Move),
    SplitKit.SplitHyp u v ρ F left right c d b pre post tail →
    ∀ (A' B : State), ShufflePlayW u pre A' →
      State.step A' (Move.foundToTab c b) = some B →
      ∀ e : Card, CanRaiseS B e →
        e.suit ≠ c.suit → e.suit ≠ c.twin.suit → False

/-- The frontier copy is literally the home declaration. -/
theorem landingThirdSuitFree_iff_home :
    Frontier.LandingThirdSuitFree ↔ Landing.LandingThirdSuitFree :=
  Iff.rfl

/-- **`ThirdBracketRead` — the containment in BRACKET form.**  Verbatim copy of
`ThirdLive.ThirdBracketRead` (`Orig2/Fork/ForkThirdResidual.lean:93`): every
third-suit S-live card at a landing is the pulled card of an EARLIER bracket
whose interior is read-safe. -/
def ThirdBracketRead : Prop :=
  ∀ (u v : State) (ρ : List Move) (F : State)
    (left right : List Move) (c d : Card) (b : Base)
    (pre post tail : List Move),
    SplitKit.SplitHyp u v ρ F left right c d b pre post tail →
    ∀ (A' B : State), ShufflePlayW u pre A' →
      State.step A' (Move.foundToTab c b) = some B →
      ∀ e : Card, CanRaiseS B e → e.suit ≠ c.suit → e.suit ≠ c.twin.suit →
      ∃ (α γ β : List Move) (z : Card) (bz : Base) (P Q : State),
        ρ = α ++ Move.foundToTab z bz :: γ ++ Move.tabToFound z :: β ∧
        ShufflePlayW u α P ∧
        State.step P (Move.foundToTab z bz) = some Q ∧
        (∀ q ∈ γ, R12.ReadOK z q)

/-- The frontier copy is literally the home declaration. -/
theorem thirdBracketRead_iff_home :
    Frontier.ThirdBracketRead ↔ ThirdLive.ThirdBracketRead :=
  Iff.rfl

/-- **THE CONTAINMENT IS EXACTLY ITS BRACKET FORM** (re-export of
`ThirdLive.thirdBracketRead_iff_landingThirdSuitFree`). -/
theorem landingThirdSuitFree_iff_thirdBracketRead :
    Frontier.LandingThirdSuitFree ↔ Frontier.ThirdBracketRead :=
  ⟨ThirdLive.thirdBracketRead_of_landingThirdSuitFree,
    ThirdLive.landingThirdSuitFree_of_thirdBracketRead⟩

/-- **`SurvivorMateBracket` — the containment in PINNED form.**  Verbatim copy
of `Surv.SurvivorMateBracket` (`Orig2/Fork/ForkSurvivor.lean:497`): the bracket card
is a rank-mate of the survivor (`e = z ∨ e = z.twin`). -/
def SurvivorMateBracket : Prop :=
  ∀ (u v : State) (rho : List Move) (F : State)
    (left right : List Move) (c d : Card) (b : Base)
    (pre post tail : List Move),
    SplitKit.SplitHyp u v rho F left right c d b pre post tail →
    ∀ (A' B : State), ShufflePlayW u pre A' →
      State.step A' (Move.foundToTab c b) = some B →
      ∀ e : Card, CanRaiseS B e → e.suit ≠ c.suit → e.suit ≠ c.twin.suit →
      ∃ (α γ β : List Move) (z : Card) (bz : Base) (P Q : State),
        (e = z ∨ e = z.twin) ∧
        rho = α ++ Move.foundToTab z bz :: γ ++ Move.tabToFound z :: β ∧
        ShufflePlayW u α P ∧
        State.step P (Move.foundToTab z bz) = some Q ∧
        (∀ q ∈ γ, R12.ReadOK z q)

/-- The frontier copy is literally the home declaration. -/
theorem survivorMateBracket_iff_home :
    Frontier.SurvivorMateBracket ↔ Surv.SurvivorMateBracket :=
  Iff.rfl

/-- **THE PINNED FORM IMPLIES THE CONTAINMENT (ONE WAY).**  Re-export of
`Surv.survivorMateBracket_thirdBracketRead`.  The reverse is NOT in the tree:
pinning `z` to a rank-mate of `e` is extra content, so this is a strengthening,
not an equivalence. -/
theorem thirdBracketRead_of_survivorMateBracket
    (h : Frontier.SurvivorMateBracket) : Frontier.ThirdBracketRead :=
  Surv.survivorMateBracket_thirdBracketRead h

/-- **`SplitTwinRungGe` — THE LIVE TWIN CLAUSE (ONE INEQUALITY).**  Verbatim
copy of `PairRungKit.SplitTwinRungGe` (`Orig2/Fork/ForkPairRung.lean:168`): at every
valley bottom the pull-card suit's rung is at most the twin suit's rung.

The other half `rungAt F c.twin.suit ≤ rungAt F c.suit` is FREE under
`SplitBlock` (`PairRungKit.splitTwinRungLe_of_block`,
`Orig2/Fork/ForkPairRung.lean:189`), so this single inequality is the whole twin
clause; under `SplitBlock` it is equivalent to the rung EQUALITY
`TwinKit.SplitPairRungEq` (`PairRungKit.splitPairRungEq_iff_ge_of_block`,
`:219`). -/
def SplitTwinRungGe : Prop :=
  ∀ (u v : State) (ρ : List Move) (F : State)
    (left right : List Move) (c d : Card) (b : Base)
    (pre post tail : List Move),
    SplitKit.SplitHyp u v ρ F left right c d b pre post tail →
    rungAt F c.suit ≤ rungAt F c.twin.suit

/-- The frontier copy is literally the home declaration. -/
theorem splitTwinRungGe_iff_home :
    Frontier.SplitTwinRungGe ↔ PairRungKit.SplitTwinRungGe :=
  Iff.rfl

/-- **`BottomBothRaisableBlock` — THE GATED BOTH-RAISABLE PIN.  NOT
INDEPENDENT.**  Verbatim copy of `BlockMin.BottomBothRaisableBlock`
(`Orig2/Fork/ForkDipPin.lean:274`): at every minimal bottom, if both twins of the
live pair are vanilla-raisable then a ready blocker exists for one.

It is **implied by `SplitKit.SplitBlock`**
(`Pin.bottomBothRaisableBlock_of_splitBlock`, `Orig2/Fork/ForkPin.lean:228`, via
`Pin.bottomNotBoth_of_splitBlock`, `:217`) and therefore is NOT an independent
frontier row — keeping it here documents the pin lane as a CONSEQUENCE of the
block.  The ungated (pointwise) form is FALSE: see
`Pin.gAce_not_bothRaisableBlock` and `BlockMin.gFin_not_fibreBlockData`. -/
def BottomBothRaisableBlock : Prop :=
  ∀ (u v : State) (ρ : List Move) (F₀ : State)
    (left right : List Move) (c d : Card) (b : Base)
    (pre post tail : List Move),
    SplitKit.SplitHyp u v ρ F₀ left right c d b pre post tail →
    BlockMin.BothRaisableBlock F₀

/-- The frontier copy is literally the home declaration. -/
theorem bottomBothRaisableBlock_iff_home :
    Frontier.BottomBothRaisableBlock ↔ BlockMin.BottomBothRaisableBlock :=
  Iff.rfl

/-- **THE BLOCK DISCHARGES THE PIN** (re-export of
`Pin.bottomBothRaisableBlock_of_splitBlock`): the dependence direction that
makes the pin non-independent. -/
theorem bottomBothRaisableBlock_of_splitBlock (hb : SplitKit.SplitBlock) :
    Frontier.BottomBothRaisableBlock :=
  Pin.bottomBothRaisableBlock_of_splitBlock hb

/-- **`ShortestPlayExists` — NOW A THEOREM, NO LONGER AN INTERFACE HYPOTHESIS.**
Verbatim copy of `ValleyElim.ShortestPlayExists` (`Orig2/Fork/ForkSplit.lean:874`):
between two saturated class-mates of differing rungs there is a witness play of
minimal length.  DISCHARGED constructively by
`DecideKit.shortestPlayExists_choiceFree` (`Orig2/Fork/ForkDecide.lean`), axioms
`[propext, Quot.sound]`: existence is a projection of `sameOrbitSetoid`, and the
minimum comes from a Bool-decided play-length predicate (the WF reversibility
oracle) plus a bounded first-satisfier — no `Nat.find`, no EM.  The definition
is kept as the named statement the reduction cites. -/
def ShortestPlayExists : Prop :=
  ∀ (u v : State), u.WF → SSaturated u → SSaturated v →
    sameOrbitSetoid.r u v →
    (∃ σ : Suit, rungAt u σ ≠ rungAt v σ) →
    ∃ ρ : List Move, ShufflePlayW u ρ v ∧
      ∀ ρ' : List Move, ShufflePlayW u ρ' v → ρ.length ≤ ρ'.length

/-- The frontier copy is literally the home declaration. -/
theorem shortestPlayExists_iff_home :
    Frontier.ShortestPlayExists ↔ ValleyElim.ShortestPlayExists :=
  Iff.rfl

/-- **`MountainSplitHyp` - FALSE; DO NOT CITE.  USE `MountainGate.MountainSplitHypDiffering`.**

The mountain-leg datum at every split (left leg raise-free, right leg
pull-free), MEASURED 51 116/51 116 on 13 boards.  `SplitKit.SplitHyp`
carries **no rung hypothesis**, so this also quantifies over the **equal-rung**
stratum.  That stratum is now probed and the statement is FALSE: the equal-rung
13-move relocation is a unit-shortest `SSaturated -> SSaturated` play whose
valley split has a raise in its left leg, so `MountainKit.MountainSplit left
right` fails there (`EqualRung.not_mountainSplit`,
`EqualRung.mountainAtSplits_false`, `Orig2/ForkEqualRungMain.lean`; see
`Temp/EqualRung_Report.md`).  Hence this definition proves nothing and every
theorem that assumes it is vacuous.  The live form is
`MountainGate.MountainSplitHypDiffering` (= `MountainAtSplitsDiffering`), which
the equal-rung witness cannot touch (`EqualRung.not_rungDiffers`; the witness
has equal rungs).  Retained only so the refutation and the historical consumers
can name it. -/
def MountainSplitHyp : Prop :=
  ∀ (u v : State) (ρ : List Move) (F : State)
    (left right : List Move) (c d : Card) (b : Base)
    (pre post tail : List Move),
    SplitKit.SplitHyp u v ρ F left right c d b pre post tail →
    MountainKit.MountainSplit left right

/-! ## §2. The minimal hypothesis set, as one row -/

/-- **THE MINIMAL HYPOTHESIS SET.**  The three-clause set: the block, the
containment, and the twin rung pin.  `Frontier.satDifferForkWF_of_minimalHypotheses`
consumes it. -/
def MinimalHypotheses : Prop :=
  SplitKit.SplitBlock ∧ TwinKit.SplitContainment ∧ TwinKit.SplitTwinRungPin

/-! ## §3. Composed route A — raise-left (`KeepsForward`) + containment -/

/-- **ROUTE A, THE COMPOSITION THAT CHECKS.**  `KeepsForward` (pointwise)
supplies the swap certificate and hence `NoEmptyTail`; the containment residual
in its bracket form plus the twin clause supply `SplitLivePair`; the cover half
`TailCovers` completes `SplitBlock`; the shortest-play interface finishes.

THE BRIEF'S DECLARED SIGNATURE
`(∀ F c, F.WF → CanRaise F c → KeepsForward F c) → LandingThirdSuitFree →
ShortestPlayExists → SatDifferForkWF` DOES NOT TYPECHECK, and nothing here
weakens `KeepsForward` or adds an axiom to force it.  The two gaps, precisely:

* `KeepsForward` reaches only `NoEmptyTail`
  (`RaiseLeft.noEmptyTail_of_keepsForward`); the COVER half of `SplitBlock`
  (`BlockKit.TailCovers`) is a separate obligation.  Hence `hcov`.
* `LandingThirdSuitFree` is only the SECOND conjunct of `LandingAll`
  (`Landing.landingAll_iff_parts`); `SplitLivePair` needs the twin clause too.
  Hence `htwin : Landing.LandingTwinLive` (equivalently, given `SplitBlock` +
  containment, the rung pin `SplitTwinRungPin`,
  `TwinKit.splitLandingTwin_iff_splitTwinRungPin`).
* `hms` is the FALSE under-gated datum (`EqualRung.mountainAtSplits_false`);
  this whole signature is vacuous.  The live Route A is
  `Gated.satDifferForkWF_of_gated_mountain` (`Orig2/Fork/ForkGatedTower.lean`). -/
theorem satDifferForkWF_of_keepsForward_and_containment
    (hkf : ∀ (F : State) (c : Card), F.WF → CanRaise F c → KeepsForward F c)
    (hms : MountainSplitHyp)
    (htwin : Landing.LandingTwinLive)
    (hcont : Landing.LandingThirdSuitFree)
    (hcov : BlockKit.TailCovers)
    (hmin : ValleyElim.ShortestPlayExists) :
    SatDifferForkWF := by
  have hkf' : ∀ (F : State) (c : Card), F.WF → CanRaise F c →
      RaiseLeft.KeepsForward F c :=
    fun F c hF hc => (keepsForward_iff_home F c).mp (hkf F c hF hc)
  have hread : ThirdLive.ThirdBracketRead :=
    ThirdLive.thirdBracketRead_of_landingThirdSuitFree hcont
  have hl : SplitKit.SplitLivePair :=
    ThirdLive.splitLivePair_of_twin_thirdBracketRead htwin hread
  have hne : BlockKit.NoEmptyTail :=
    RaiseLeft.noEmptyTail_of_keepsForward hl hms
      (RaiseLeft.raise_moves_left_of_keepsForward hkf')
  exact BlockKit.satDifferForkWF_of_livePair_parts hl hne hcov hmin

/-! ## §4. Composed route B — gated containment + one-sided twin rung -/

/-- **`SplitContainment` FROM `LandingThirdSuitFree`.**  The containment read at
the bottom `F` is the same statement as the containment read at the pull
landing `B`: `Mech.canRaiseS_landing_iff` transports the S-live set along the
free tail, in both directions.  This is the bridge that lets Route B be stated
with the frontier residual `LandingThirdSuitFree`. -/
theorem splitContainment_of_landingThirdSuitFree
    (hf : Landing.LandingThirdSuitFree) : TwinKit.SplitContainment := by
  intro u v ρ F left right c d b pre post tail hs e he
  have hsk := hs
  obtain ⟨huwf, -, -, -, -, -, -, hleft, -, hshape, hfree, -⟩ := hs
  obtain ⟨A', hpre, hrest⟩ :=
    ValleyElim.ShufflePlayW_split hleft pre (Move.foundToTab c b :: post) hshape
  cases hrest with
  | @cons _ B _ _ _ hrev hstep hpost =>
      have hA' : A'.WF := SatDifferCensus.ShufflePlayW.wf_end hpre huwf
      have hB : B.WF := step_wf hA' hstep
      have heB : CanRaiseS B e :=
        (Mech.canRaiseS_landing_iff hB hpost hfree e).mpr he
      by_cases h1 : e.suit = c.suit
      · exact Or.inl h1
      · by_cases h2 : e.suit = c.twin.suit
        · exact Or.inr h2
        · exact (hf u v ρ F left right c d b pre post tail hsk A' B hpre hstep
            e heB h1 h2).elim

/-- **ROUTE B, EXACTLY AS DECLARED.**  `SplitBlock` + `LandingThirdSuitFree` +
`SplitTwinRungGe` + the shortest-play interface give `SatDifferForkWF`:
`SplitContainment` is derived above, `SplitTwinRungGe` upgrades to the pin
(`PairRungKit.splitPairRungEq_iff_ge_of_block`), and the campaign's three-clause
chain takes over. -/
theorem satDifferForkWF_of_gated_containment_and_twinGe
    (hb : SplitKit.SplitBlock)
    (hcont : Landing.LandingThirdSuitFree)
    (hg : SplitTwinRungGe)
    (hmin : ValleyElim.ShortestPlayExists) :
    SatDifferForkWF :=
  PairRungKit.satDifferForkWF_of_block_containment_of_ge hb
    (splitContainment_of_landingThirdSuitFree hcont) hg hmin

/-- **THE MINIMAL HYPOTHESIS SET CONSUMED.**  `MinimalHypotheses` plus the
shortest-play interface. -/
theorem satDifferForkWF_of_minimalHypotheses
    (h : MinimalHypotheses) (hmin : ValleyElim.ShortestPlayExists) :
    SatDifferForkWF :=
  TwinKit.satDifferForkWF_of_block_containment_of_pin h.1 h.2.1 h.2.2 hmin

/-! ## §5. Composed route C — live pair + the both-raisable pin -/

/-- **ROUTE C, THE VACUITY FORM.**  `SplitLivePair` + the gated vacuity
`Pin.BottomNotBothRaisable` + the interface.  `Pin.satDifferForkWF_of_notBoth`
(`Orig2/Fork/ForkPin.lean:285`) is the row. -/
theorem satDifferForkWF_of_splitLivePair_and_notBoth
    (hl : SplitKit.SplitLivePair)
    (h : Pin.BottomNotBothRaisable)
    (hmin : ValleyElim.ShortestPlayExists) :
    SatDifferForkWF :=
  Pin.satDifferForkWF_of_notBoth hl h hmin

/-- **ROUTE C, THE NAMED RESIDUAL FORM.**  `SplitLivePair` + the frontier row
`BottomBothRaisableBlock` + the interface
(`BlockMin.satDifferForkWF_of_bothRaisable_drainClosed`,
`Orig2/Fork/ForkDipPin.lean:371`). -/
theorem satDifferForkWF_of_splitLivePair_and_bothRaisableBlock
    (hl : SplitKit.SplitLivePair)
    (h : BottomBothRaisableBlock)
    (hmin : ValleyElim.ShortestPlayExists) :
    SatDifferForkWF :=
  BlockMin.satDifferForkWF_of_bothRaisable_drainClosed hl h hmin

/-- **ROUTE C, COLLAPSED INTO THE BLOCK.**  `SplitLivePair` + `SplitBlock` +
the interface, with no pin hypothesis at all: the block implies the gated
vacuity and hence the pin, and the `DipPin` route finishes
(`BlockMin.dipPin_of_livePair_block`,
`BlockMin.satDifferForkWF_of_dipPin`).  This row exhibits the redundancy of the
pin lane: the pin is not an independent target. -/
theorem satDifferForkWF_of_splitLivePair_and_splitBlock
    (hl : SplitKit.SplitLivePair)
    (hb : SplitKit.SplitBlock)
    (hmin : ValleyElim.ShortestPlayExists) :
    SatDifferForkWF :=
  BlockMin.satDifferForkWF_of_dipPin
    (BlockMin.dipPin_of_livePair_block hl hb) hmin

/-! ## §6. The other committed consumers (re-exports) -/

/-- **The mechanism route**: `LandingLivePair` + `CoverEvent` bundled as
`Mech.MechanismResidual`, plus the interface
(`Orig2/Fork/ForkMechanism.lean:525`). -/
theorem satDifferForkWF_of_mechanismResidual
    (h : Mech.MechanismResidual) (hmin : ValleyElim.ShortestPlayExists) :
    SatDifferForkWF :=
  Mech.satDifferForkWF_of_mechanismResidual_drainClosed h hmin

/-- **The fork-at-min route**: every minimal valley bottom is a fork
(`Orig2/Fork/ForkExist.lean:210`). -/
theorem satDifferForkWF_of_forkAtMin
    (h : ExistKit.ValleyForkAtMin) (hmin : ValleyElim.ShortestPlayExists) :
    SatDifferForkWF :=
  ExistKit.satDifferForkWF_of_forkAtMin h hmin

/-- **The min-crossing route** (the strictly weaker residual: a fork ANYWHERE on
the minimal play, `Orig2/Fork/ForkMinCross.lean:72`). -/
theorem satDifferForkWF_of_minCrossesFork
    (h : MinKit.MinCrossesFork) (hmin : ValleyElim.ShortestPlayExists) :
    SatDifferForkWF :=
  MinKit.satDifferForkWF_of_minCrossesFork h hmin

/-- **The DipPin route** (`Orig2/Fork/ForkDipPin.lean:353`). -/
theorem satDifferForkWF_of_dipPin
    (h : BlockMin.DipPin) (hmin : ValleyElim.ShortestPlayExists) :
    SatDifferForkWF :=
  BlockMin.satDifferForkWF_of_dipPin h hmin

/-! ## §7. The other committed reductions, for the ledger -/

/-- **THE PIN REDUCES TO THE VACUITY** (`Pin.bottomBothRaisableBlock_of_notBoth`,
`Orig2/Fork/ForkPin.lean:207`). -/
theorem bottomBothRaisableBlock_of_notBoth
    (h : Pin.BottomNotBothRaisable) : Frontier.BottomBothRaisableBlock :=
  Pin.bottomBothRaisableBlock_of_notBoth h

/-- **THE ONE-SIDED CLAUSE IS FREE UNDER THE BLOCK** (re-export of
`PairRungKit.splitTwinRungLe_of_block`). -/
theorem splitTwinRungLe_of_block (hb : SplitKit.SplitBlock) :
    PairRungKit.SplitTwinRungLe :=
  PairRungKit.splitTwinRungLe_of_block hb

/-- **THE TWIN CLAUSE IS ONE INEQUALITY UNDER THE BLOCK** (re-export of
`PairRungKit.splitPairRungEq_iff_ge_of_block`). -/
theorem splitPairRungEq_iff_ge_of_block (hb : SplitKit.SplitBlock) :
    TwinKit.SplitPairRungEq ↔ Frontier.SplitTwinRungGe :=
  PairRungKit.splitPairRungEq_iff_ge_of_block hb

end Frontier

/-! ## §8. Battery — every new row; `[]` / `[propext]` / `[Quot.sound]` only -/

#check @Frontier.KeepsForward
#check @Frontier.KeepsForwardReadSafe
#check @Frontier.LandingThirdSuitFree
#check @Frontier.ThirdBracketRead
#check @Frontier.SurvivorMateBracket
#check @Frontier.SplitTwinRungGe
#check @Frontier.BottomBothRaisableBlock
#check @Frontier.ShortestPlayExists
#check @Frontier.MountainSplitHyp
#check @Frontier.MinimalHypotheses

#print axioms Frontier.KeepsForward
#print axioms Frontier.keepsForward_iff_home
#print axioms Frontier.KeepsForwardReadSafe
#print axioms Frontier.keepsForwardReadSafe_holds
#print axioms Frontier.keepsForward_of_readSafe
#print axioms Frontier.LandingThirdSuitFree
#print axioms Frontier.landingThirdSuitFree_iff_home
#print axioms Frontier.ThirdBracketRead
#print axioms Frontier.thirdBracketRead_iff_home
#print axioms Frontier.landingThirdSuitFree_iff_thirdBracketRead
#print axioms Frontier.SurvivorMateBracket
#print axioms Frontier.survivorMateBracket_iff_home
#print axioms Frontier.thirdBracketRead_of_survivorMateBracket
#print axioms Frontier.SplitTwinRungGe
#print axioms Frontier.splitTwinRungGe_iff_home
#print axioms Frontier.BottomBothRaisableBlock
#print axioms Frontier.bottomBothRaisableBlock_iff_home
#print axioms Frontier.bottomBothRaisableBlock_of_splitBlock
#print axioms Frontier.ShortestPlayExists
#print axioms Frontier.shortestPlayExists_iff_home
#print axioms Frontier.MountainSplitHyp
#print axioms Frontier.MinimalHypotheses
#print axioms Frontier.satDifferForkWF_of_keepsForward_and_containment
#print axioms Frontier.splitContainment_of_landingThirdSuitFree
#print axioms Frontier.satDifferForkWF_of_gated_containment_and_twinGe
#print axioms Frontier.satDifferForkWF_of_minimalHypotheses
#print axioms Frontier.satDifferForkWF_of_splitLivePair_and_notBoth
#print axioms Frontier.satDifferForkWF_of_splitLivePair_and_bothRaisableBlock
#print axioms Frontier.satDifferForkWF_of_splitLivePair_and_splitBlock
#print axioms Frontier.satDifferForkWF_of_mechanismResidual
#print axioms Frontier.satDifferForkWF_of_forkAtMin
#print axioms Frontier.satDifferForkWF_of_minCrossesFork
#print axioms Frontier.satDifferForkWF_of_dipPin
#print axioms Frontier.bottomBothRaisableBlock_of_notBoth
#print axioms Frontier.splitTwinRungLe_of_block
#print axioms Frontier.splitPairRungEq_iff_ge_of_block
