import Orig2.Fork.Local.ForkMechanism
import Orig2.Fork.Class.ForkRungGe
import Orig2.Fork.Local.ForkNoSelf

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-!
# Orig2/ForkRankFloor — the FLOOR replaces the CONTAINMENT in the drain chain

READ-ONLY scratch card (no source edit, no commit).  Zero `sorry`, zero
`Classical.choice`, zero `native_decide`; axiom battery at the tail.

## The reframing

The campaign's live set at a valley bottom is *exactly* `{c, c.twin}`
(`Landing.LandingThirdSuitFree` / `SplitKit.SplitLivePair` /
`TwinKit.SplitContainment`).  The theorem it feeds does not need exactness:
`DrainClose.fork_exists_of_asymmetry` (`Orig2/Fork/Split/ForkDrainClose.lean:766`) consumes

* `CanRaise st x`,
* `CanRaiseS st x.twin`,
* `¬ CanRaise st x.twin`,
* **an inequality**: `∀ c, CanRaiseS st c → x.rank.toIdx ≤ c.rank.toIdx`.

So the containment can be replaced by `RankFloorAtSplit` (below), read at the
raise card `d` (`x := d`).  This card proves the replacement chain

    SplitTwinCovered → RankFloorAtSplit → ShortestPlayExists → SatDifferForkWF

and separately reduces the asymmetry clause to the campaign's existing
`SplitKit.SplitBlock` + `SplitKit.SplitTwin`, and the floor to the campaign's
existing `SplitKit.SplitFloor`:

    RankFloorAtSplit  ↔  SplitKit.SplitFloor     (given `SplitTwin`),
    SplitLivePair     ⇒  SplitTwin ∧ RankFloorAtSplit.

Hence: **the only conjunct this lane assumes is `SplitKit.SplitFloor`, an
inequality, and it is implied by — but does not imply — the containment.**

## What is proved here

* `RankFloorAtSplit` — the drain's floor read at the split's raise card `d`.
* `SplitTwinCovered` — the drain's twin asymmetry read at `d`:
  `CanRaiseS F d.twin ∧ ¬ CanRaise F d.twin`.
* `splitTwinCovered_of_block_twin` — `SplitBlock` + `SplitTwin` give it (the
  twin liveness is the *green* `CanRaiseS F c` of `splitHyp_green`).
* `rankFloor_iff_splitFloor` — the floor at `d` **is** `SplitKit.SplitFloor`
  once the mechanism `d = c.twin` is known.  (`SplitFloor` already exists.)
* `livePair_implies_twin_and_floor` — the containment implies both conjuncts,
  so this lane is at most as hard as the containment lane.
* `satDifferForkWF_of_covered_rankFloor` — THE CHAIN:
  `SplitTwinCovered + RankFloorAtSplit + ShortestPlayExists ⇒ SatDifferForkWF`.
* `satDifferForkWF_of_rankFloor` — the brief's shape with `SplitBlock` and
  `SplitTwin`: `SplitBlock + SplitTwin + RankFloorAtSplit ⇒ SatDifferForkWF`.
* `satDifferForkWF_of_rankFloor_livePair` — same, with `SplitLivePair`
  standing in for the mechanism (it implies `SplitTwin` and
  `RungGe.SplitTwinLiveAtBottom`, so it is the brief's conjunct set).
-/

namespace FloorRank

/-! ## §1. The two halves of the drain hypothesis, read at the split -/

/-- **`RankFloorAtSplit`** — THE FLOOR.  At every valley bottom `F` of a
minimal play, no S-live card has rank below the raise card `d`: exactly the
drain's `hfloor` at `x := d` (`Orig2/Fork/Split/ForkDrainClose.lean:770`).  This is an
*inequality*, not the containment of the live set. -/
def RankFloorAtSplit : Prop :=
  ∀ (u v : State) (ρ : List Move) (F : State)
    (left right : List Move) (c d : Card) (b : Base)
    (pre post tail : List Move),
    SplitKit.SplitHyp u v ρ F left right c d b pre post tail →
      ∀ e, CanRaiseS F e → d.rank.toIdx ≤ e.rank.toIdx

/-- **`SplitTwinCovered`** — THE TWIN ASYMMETRY, read at the raise card `d`:
`d.twin` is S-live and vanilla-blocked at the bottom.  Together with the green
`CanRaise F d` (`SplitKit.splitHyp_green`) this is the drain's first three
hypotheses at `x := d`. -/
def SplitTwinCovered : Prop :=
  ∀ (u v : State) (ρ : List Move) (F : State)
    (left right : List Move) (c d : Card) (b : Base)
    (pre post tail : List Move),
    SplitKit.SplitHyp u v ρ F left right c d b pre post tail →
      CanRaiseS F d.twin ∧ ¬ CanRaise F d.twin

/-! ## §2. The asymmetry clause from `SplitBlock` + `SplitTwin` -/

/-- **`SplitBlock` + the mechanism give the covered twin.**  `SplitTwin` says
`d = c.twin`, so `d.twin = c`; the twin's liveness is then the *green*
`CanRaiseS F c` (`Bridge.bottom_pull_live`) and its block is `SplitBlock`. -/
theorem splitTwinCovered_of_block_twin
    (hb : SplitKit.SplitBlock) (ht : SplitKit.SplitTwin) : SplitTwinCovered := by
  intro u v ρ F left right c d b pre post tail h
  obtain ⟨-, hSc, -, -⟩ := SplitKit.splitHyp_green h
  have hd : d = c.twin := ht u v ρ F left right c d b pre post tail h
  have hdt : d.twin = c := by rw [hd, card_twin_twin]
  refine ⟨?_, ?_⟩
  · rw [hdt]; exact hSc
  · rw [hdt]; exact hb u v ρ F left right c d b pre post tail h

/-! ## §3. The floor *is* the campaign's `SplitFloor` -/

/-- The floor at the raise card `d` is the floor at the pull card `c`, once
`d = c.twin` (the twin keeps the rank). -/
theorem splitFloor_of_rankFloor (h : RankFloorAtSplit) (ht : SplitKit.SplitTwin) :
    SplitKit.SplitFloor := by
  intro u v ρ F left right c d b pre post tail hh e he
  have hd : d.rank.toIdx = c.rank.toIdx := by
    rw [ht u v ρ F left right c d b pre post tail hh, Card.twin_rank]
  rw [← hd]
  exact h u v ρ F left right c d b pre post tail hh e he

/-- Conversely `SplitFloor` is the floor at `d`. -/
theorem rankFloor_of_splitFloor (h : SplitKit.SplitFloor) (ht : SplitKit.SplitTwin) :
    RankFloorAtSplit := by
  intro u v ρ F left right c d b pre post tail hh e he
  have hd : d.rank.toIdx = c.rank.toIdx := by
    rw [ht u v ρ F left right c d b pre post tail hh, Card.twin_rank]
  rw [hd]
  exact h u v ρ F left right c d b pre post tail hh e he

/-- **THE FLOOR IS NOT A NEW RESIDUAL.**  Given the mechanism `d = c.twin`, the
drain's floor at the raise card is *exactly* the campaign's already-named
`SplitKit.SplitFloor` (`Orig2/Fork/Split/ForkSplitResidual.lean:255`). -/
theorem rankFloor_iff_splitFloor (ht : SplitKit.SplitTwin) :
    RankFloorAtSplit ↔ SplitKit.SplitFloor :=
  ⟨fun h => splitFloor_of_rankFloor h ht, fun h => rankFloor_of_splitFloor h ht⟩

/-! ## §4. The containment implies both new conjuncts -/

/-- **THE CONTAINMENT IS STRONGER.**  `SplitLivePair` (the live set is exactly
`{d, d.twin}`) gives the mechanism and the floor.  So the floor lane never asks
for more than the current chain does — it asks for strictly less. -/
theorem livePair_implies_twin_and_floor
    (hb : SplitKit.SplitBlock) (hl : SplitKit.SplitLivePair) :
    SplitKit.SplitTwin ∧ RankFloorAtSplit := by
  have ht : SplitKit.SplitTwin := SplitKit.splitTwin_of_livePair_block hl hb
  exact ⟨ht, rankFloor_of_splitFloor (SplitKit.splitFloor_of_livePair_twin hl ht) ht⟩

/-- `SplitLivePair` also gives the brief's `SplitTwinLiveAtBottom` conjunct
(the twin's S-liveness at the bottom). -/
theorem twinLiveAtBottom_of_livePair (hl : SplitKit.SplitLivePair) :
    RungGe.SplitTwinLiveAtBottom :=
  RungGe.twinLiveAtBottom_of_splitLivePair hl

/-! ## §5. THE CHAIN -/

/-- **THE REPLACEMENT CHAIN.**  The drain's hypotheses at the split's raise card
`d` — the covered twin `SplitTwinCovered`, and the FLOOR `RankFloorAtSplit` —
plus the choice-free shortest-play interface give `SatDifferForkWF`.

The green `CanRaise F d` is `SplitKit.splitHyp_green`; nothing about the
containment of the live set is consumed. -/
theorem satDifferForkWF_of_covered_rankFloor
    (hcover : SplitTwinCovered) (hfloor : RankFloorAtSplit)
    (hmin : ValleyElim.ShortestPlayExists) : SatDifferForkWF := by
  intro u v huwf hsu hsv hcls hdiff
  obtain ⟨ρ, hplay, hminlen⟩ := hmin u v huwf hsu hsv hcls hdiff
  obtain ⟨F, hsplit⟩ := ValleyElim.valley_exists huwf hsu hsv hdiff hplay
  obtain ⟨left, right, c, d, b, pre, post, tail,
    hρ, hleft, hright, hshape, hfree, hrightShape⟩ := hsplit
  have hh : SplitKit.SplitHyp u v ρ F left right c d b pre post tail :=
    ⟨huwf, hsu, hsv, hplay,
      ⟨left, right, c, d, b, pre, post, tail,
        hρ, hleft, hright, hshape, hfree, hrightShape⟩,
      hminlen, hρ, hleft, hright, hshape, hfree, hrightShape⟩
  obtain ⟨hF, -, hcanD, -⟩ := SplitKit.splitHyp_green hh
  obtain ⟨hlive, hblock⟩ := hcover u v ρ F left right c d b pre post tail hh
  obtain ⟨F', hrF, hfork⟩ :=
    DrainClose.fork_exists_of_asymmetry hF hcanD hlive hblock
      (hfloor u v ρ F left right c d b pre post tail hh)
  obtain ⟨y, hy⟩ := forkState_iff.mp hfork
  exact ⟨F', y,
    sameOrbitSetoid.iseqv.trans (RevEqW_symm (shufflePlayW_revEqW hleft)) hrF, hy⟩

/-- **THE BRIEF'S SHAPE.**  `SplitBlock` + `SplitTwin` + `RankFloorAtSplit` +
`ShortestPlayExists ⇒ SatDifferForkWF`.  The only conjunct beyond the green /
mechanism facts is the floor. -/
theorem satDifferForkWF_of_rankFloor
    (hb : SplitKit.SplitBlock) (ht : SplitKit.SplitTwin)
    (hfloor : RankFloorAtSplit)
    (hmin : ValleyElim.ShortestPlayExists) : SatDifferForkWF :=
  satDifferForkWF_of_covered_rankFloor (splitTwinCovered_of_block_twin hb ht) hfloor hmin

/-- **THE SAME CHAIN WITH `SplitLivePair`** (the current chain's containment
hypothesis) standing in for the mechanism: it implies both `SplitTwin` and
`RungGe.SplitTwinLiveAtBottom`, so this is the brief's conjunct set with the
twin-liveness discharged, not assumed. -/
theorem satDifferForkWF_of_rankFloor_livePair
    (hb : SplitKit.SplitBlock) (hl : SplitKit.SplitLivePair)
    (hfloor : RankFloorAtSplit)
    (hmin : ValleyElim.ShortestPlayExists) : SatDifferForkWF :=
  satDifferForkWF_of_rankFloor hb (SplitKit.splitTwin_of_livePair_block hl hb) hfloor hmin

/-- **THE FLOOR + FLOOR-FORM (no twin equation).**  If the campaign prefers to
keep the *existing* residual names, this is the same chain: `SplitBlock` +
`SplitFloor` + the mechanism.  (`SplitFloor` is `Orig2/Fork/Split/ForkSplitResidual.lean`.) -/
theorem satDifferForkWF_of_splitFloor
    (hb : SplitKit.SplitBlock) (ht : SplitKit.SplitTwin)
    (hfloor : SplitKit.SplitFloor)
    (hmin : ValleyElim.ShortestPlayExists) : SatDifferForkWF :=
  satDifferForkWF_of_rankFloor hb ht (rankFloor_of_splitFloor hfloor ht) hmin

/-! ## §6. Axiom battery -/

#print axioms FloorRank.splitTwinCovered_of_block_twin
#print axioms FloorRank.splitFloor_of_rankFloor
#print axioms FloorRank.rankFloor_of_splitFloor
#print axioms FloorRank.rankFloor_iff_splitFloor
#print axioms FloorRank.livePair_implies_twin_and_floor
#print axioms FloorRank.twinLiveAtBottom_of_livePair
#print axioms FloorRank.satDifferForkWF_of_covered_rankFloor
#print axioms FloorRank.satDifferForkWF_of_rankFloor
#print axioms FloorRank.satDifferForkWF_of_rankFloor_livePair
#print axioms FloorRank.satDifferForkWF_of_splitFloor

#check @FloorRank.RankFloorAtSplit
#check @FloorRank.SplitTwinCovered
#check @FloorRank.satDifferForkWF_of_rankFloor

end FloorRank
