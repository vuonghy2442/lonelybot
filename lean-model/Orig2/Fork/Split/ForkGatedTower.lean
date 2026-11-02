import Orig2.Fork.Class.ForkRankFloorAttack
import Orig2.Fork.Third.ForkNoMate
import Orig2.Fork.Split.ForkFrontier
import Orig2.Fork.Local.ForkDirect

/-! ## Merged from `Orig2/Fork/Split/ForkMountainGate.lean` (2026-11-02) -/

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

/-!
# ForkMountainGate — the mountain hypothesis, RE-GATED

`Direct.MountainAtSplits` and `Frontier.MountainSplitHyp` are the same statement:

```text
∀ (split data), SplitHyp … → MountainSplit left right
```

`SplitKit.SplitHyp` carries `u.WF`, `SSaturated u`, `SSaturated v`, the play,
the valley split and the SHORTEST-PLAY conjunct — but **no rung hypothesis**.  So
both defs also quantify over the **equal-rung** stratum, and that stratum is
exactly where the mountain has no reason to hold:

* the mountain's force is the accounting identity
  `length = Σσ(h_u + h_v − 2m_σ) + #free`, whose "budget" is the L1 rung gap —
  which is **zero** when the endpoints agree;
* every census (`51 116 + 9 966` minimal plays) enumerated only **differing-rung**
  pairs, so the equal-rung stratum was never probed;
* the one equal-rung datum we have is a **candidate relocation** (13 moves,
  unit-shortest, saturated endpoints at equal rungs `(4,0,3,2)`, containing
  `raise 5C … pull 5C → 6D`; probe only, see `Temp/Crack_Report.md` regime R4,
  being kernel-certified in `Temp/EqualRung_*`).

So the un-gated forms are **FALSE** (`EqualRung.mountainAtSplits_false`,
`Orig2/ForkEqualRungMain.lean`): the equal-rung stratum is now probed and
refuted, and their consumers must not be cited as conditional on a hypothesis
the campaign can discharge.  The campaign's own endpoint hypothesis already
supplies the missing gate — `SatDifferForkWF` literally carries
`∃ σ, rungAt u σ ≠ rungAt v σ` — so the corrected forms below are the ones to
use.

The two un-gated definitions are kept (marked FALSE in their docstrings) only so
the refutation and the historical consumers can name them; every theorem that
assumes one is vacuous.
-/

namespace MountainGate

open ValleyElim

/-- **The gate.** The campaign's own endpoint hypothesis, as its own name. -/
def RungDiffers (u v : State) : Prop := ∃ σ : Suit, rungAt u σ ≠ rungAt v σ

/-- **`MountainAtSplitsDiffering` — THE GATED MOUNTAIN.**  The down-then-up shape,
asked only where the campaign actually uses it: at a minimal play between
saturated endpoints whose rung vectors DIFFER.  This is the form that has
census support (`M1` 100 % on both cost models) and the only form whose "budget"
is non-zero. -/
def MountainAtSplitsDiffering : Prop :=
  ∀ (u v : State) (ρ : List Move) (F : State)
    (left right : List Move) (c d : Card) (b : Base)
    (pre post tail : List Move),
    RungDiffers u v →
    SplitKit.SplitHyp u v ρ F left right c d b pre post tail →
    MountainKit.MountainSplit left right

/-- The frontier spelling of the same gated statement. -/
def MountainSplitHypDiffering : Prop :=
  MountainAtSplitsDiffering

/-- The two spellings agree. -/
theorem mountainSplitHypDiffering_eq : MountainSplitHypDiffering = MountainAtSplitsDiffering :=
  rfl

/-- **VACUOUS: the un-gated hypothesis is FALSE.**  This implication is
vacuously true (`EqualRung.mountainAtSplits_false`), so it is NOT a way to
obtain the gate and it does NOT show "gating loses nothing".  The gate is
load-bearing: the equal-rung 13-move relocation refutes the un-gated form while
`EqualRung.not_rungDiffers` keeps it outside the gated form.  Kept only for
interface archaeology; do not cite. -/
theorem mountainAtSplitsDiffering_of_ungated
    (h : Direct.MountainAtSplits) : MountainAtSplitsDiffering :=
  fun u v ρ F left right c d b pre post tail _ hs =>
    h u v ρ F left right c d b pre post tail hs

/-- **VACUOUS**: same statement for the frontier spelling
(`Direct.MountainAtSplits = Frontier.MountainSplitHyp`, which is FALSE). -/
theorem mountainSplitHypDiffering_of_ungated
    (h : Frontier.MountainSplitHyp) : MountainSplitHypDiffering :=
  fun u v ρ F left right c d b pre post tail _ hs =>
    h u v ρ F left right c d b pre post tail hs

/-- **Sanity: the gate is exactly the campaign's endpoint hypothesis.**  This is the
witness `SatDifferForkWF` already carries, so the gated mountain is instantiable
wherever the campaign applies it. -/
theorem rungDiffers_of_satDiffer
    {u v : State} (h : ∃ σ : Suit, rungAt u σ ≠ rungAt v σ) : RungDiffers u v :=
  h

#print axioms MountainGate.mountainAtSplitsDiffering_of_ungated
#print axioms MountainGate.mountainSplitHypDiffering_of_ungated

end MountainGate


set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-!
# Gated_Tower — the consumer tower, re-gated

Scratch card.  READ-ONLY on `Orig2/`; no source edit, no commit.  Zero
`sorry`, zero `Classical.choice`, zero `native_decide`; the axiom battery is
at the tail.

## What this card does

`MountainGate.MountainAtSplitsDiffering` is the gated mountain: the
down-then-up shape asked only at a split whose endpoints satisfy

    RungDiffers u v  :=  ∃ σ : Suit, rungAt u σ ≠ rungAt v σ,

which is exactly the hypothesis `SatDifferForkWF` already carries.  This card
re-gates the five consumers of the un-gated hypothesis (`Direct:556`,
`NoMate:218`, `FloorAttack:140`, `FloorAttack:219`, `Frontier:495`) by

1. defining **gated twins** of the intermediate ∀-statements, with
   `RungDiffers u v` as an explicit parameter immediately before the split
   hypothesis, and
2. copying each original proof, passing the gate to every application of the
   mountain.

The tower then composes to `satDifferForkWF_of_gated_mountain`, the exact
analogue of `Frontier.satDifferForkWF_of_keepsForward_and_containment` with
the gated mountain.  A second top-level, `satDifferForkWF_of_gated_mountain_of_mateRaiseFree`,
uses the re-gated raise-exclusion instead of the containment residual.

## Design note (locality)

The gate is threaded **only** at the splits that the campaign actually
instantiates.  No un-gated global statement is invented from a gated one: the
gated twins are all `∀ u v, RungDiffers u v → SplitHyp … → …`, and the
un-gated residuals that do not mention the mountain (`SplitLivePair`,
`SplitBlock`, `TailCovers`, `LandingTwinLive`, `LandingThirdSuitFree`,
`KeepsForward`) are consumed unchanged.
-/

namespace Gated

open ValleyElim

/-! ## §1. `Direct` — the containment from the raise-exclusion -/

/-- **`MateRaiseFreeDiffering`** — the raise-exclusion, gated: at a split of a
minimal play whose endpoints have differing rungs and whose right leg is
pull-free (`MountainSplit`), no third-suit card S-live at the pull landing has
either rank-mate raised in the right leg. -/
def MateRaiseFreeDiffering : Prop :=
  ∀ (u v : State) (ρ : List Move) (F : State)
    (left right : List Move) (c d : Card) (b : Base)
    (pre post tail : List Move),
    MountainGate.RungDiffers u v →
    SplitKit.SplitHyp u v ρ F left right c d b pre post tail →
    MountainKit.MountainSplit left right →
    ∀ (A' B : State), ShufflePlayW u pre A' →
      State.step A' (Move.foundToTab c b) = some B →
      ∀ e : Card, CanRaiseS B e → e.suit ≠ c.suit → e.suit ≠ c.twin.suit →
        ¬ Direct.Occurs (Move.tabToFound e) right ∧
          ¬ Direct.Occurs (Move.tabToFound e.twin) right

/-- **`LandingThirdSuitFreeDiffering`** — the containment, gated. -/
def LandingThirdSuitFreeDiffering : Prop :=
  ∀ (u v : State) (ρ : List Move) (F : State)
    (left right : List Move) (c d : Card) (b : Base)
    (pre post tail : List Move),
    MountainGate.RungDiffers u v →
    SplitKit.SplitHyp u v ρ F left right c d b pre post tail →
    ∀ (A' B : State), ShufflePlayW u pre A' →
      State.step A' (Move.foundToTab c b) = some B →
      ∀ e : Card, CanRaiseS B e →
        e.suit ≠ c.suit → e.suit ≠ c.twin.suit → False

/-- **THE TARGET FROM THE GATED RESIDUAL.**  `Direct.landingThirdSuitFree_of_mateRaiseFree`
with the gate threaded: the mountain is only consulted at a differing-rung
split, where the gate is available. -/
theorem landingThirdSuitFreeDiffering_of_mateRaiseFreeDiffering
    (hmt : MountainGate.MountainAtSplitsDiffering)
    (h : MateRaiseFreeDiffering) :
    LandingThirdSuitFreeDiffering := by
  intro u v ρ F left right c d b pre post tail hd hs A' B hpre hstep e he h1 h2
  have hms := hmt u v ρ F left right c d b pre post tail hd hs
  obtain ⟨hnoe, hnot⟩ := h u v ρ F left right c d b pre post tail hd hs hms
    A' B hpre hstep e he h1 h2
  rcases Direct.split_survivor_bad_raise hs hms hpre hstep he with hbad | hbad
  · exact hnoe hbad
  · exact hnot hbad

/-- The containment-to-raise-exclusion direction (`NoMate.mateRaiseFree_of_containment`
gated).  No mountain is used. -/
theorem mateRaiseFreeDiffering_of_containmentDiffering
    (h : LandingThirdSuitFreeDiffering) : MateRaiseFreeDiffering := by
  intro u v ρ F left right c d b pre post tail hd hs hms A' B hpre hstep e he h1 h2
  exact ⟨fun _ => h u v ρ F left right c d b pre post tail hd hs A' B hpre hstep
      e he h1 h2,
    fun _ => h u v ρ F left right c d b pre post tail hd hs A' B hpre hstep
      e he h1 h2⟩

/-- **THE VERDICT, GATED.**  `NoMate.mateRaiseFree_iff_containment` with both
sides gated: under the gated mountain the raise-exclusion and the containment
are the same proposition at differing-rung splits. -/
theorem mateRaiseFreeDiffering_iff_containmentDiffering
    (hmt : MountainGate.MountainAtSplitsDiffering) :
    MateRaiseFreeDiffering ↔ LandingThirdSuitFreeDiffering :=
  ⟨landingThirdSuitFreeDiffering_of_mateRaiseFreeDiffering hmt,
    mateRaiseFreeDiffering_of_containmentDiffering⟩

/-! ## §2. `FloorAttack` — the rank floor from `RightRaisesHigh` -/

/-- **`RightRaisesHighDiffering`** — the play-level inequality residual, gated. -/
def RightRaisesHighDiffering : Prop :=
  ∀ (u v : State) (ρ : List Move) (F : State)
    (left right : List Move) (c d : Card) (b : Base)
    (pre post tail : List Move),
    MountainGate.RungDiffers u v →
    SplitKit.SplitHyp u v ρ F left right c d b pre post tail →
    MountainKit.MountainSplit left right →
      ∀ x : Card, Direct.Occurs (Move.tabToFound x) right →
        d.rank.toIdx ≤ x.rank.toIdx

/-- **`RankFloorAtSplitDiffering`** — the floor, gated. -/
def RankFloorAtSplitDiffering : Prop :=
  ∀ (u v : State) (ρ : List Move) (F : State)
    (left right : List Move) (c d : Card) (b : Base)
    (pre post tail : List Move),
    MountainGate.RungDiffers u v →
    SplitKit.SplitHyp u v ρ F left right c d b pre post tail →
      ∀ e, CanRaiseS F e → d.rank.toIdx ≤ e.rank.toIdx

/-- **THE FLOOR FROM THE GATED RAISE-EXCLUSION** (`rankFloor_of_rightRaisesHigh`
gated). -/
theorem rankFloorDiffering_of_rightRaisesHighDiffering
    (h : RightRaisesHighDiffering)
    (hmt : MountainGate.MountainAtSplitsDiffering) :
    RankFloorAtSplitDiffering := by
  intro u v ρ F left right c d b pre post tail hd hh e he
  have hms := hmt u v ρ F left right c d b pre post tail hd hh
  obtain ⟨x, hocc, hrank⟩ := FloorAttack.exists_raise_of_rank hh hms he
  have h1 := h u v ρ F left right c d b pre post tail hd hh hms x hocc
  omega

/-- **THE CHAIN, GATED** (`FloorRank.satDifferForkWF_of_covered_rankFloor`
with the gate threaded; `hdiff` is exactly `RungDiffers`). -/
theorem satDifferForkWF_of_covered_rankFloorDiffering
    (hcover : FloorRank.SplitTwinCovered)
    (hfloor : RankFloorAtSplitDiffering)
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
      (hfloor u v ρ F left right c d b pre post tail hdiff hh)
  obtain ⟨y, hy⟩ := forkState_iff.mp hfork
  exact ⟨F', y,
    sameOrbitSetoid.iseqv.trans (RevEqW_symm (shufflePlayW_revEqW hleft)) hrF, hy⟩

/-- **THE BRIEF'S SHAPE, GATED.**  `SplitBlock` + `SplitTwin` + the gated floor
give `SatDifferForkWF`. -/
theorem satDifferForkWF_of_rankFloorDiffering
    (hb : SplitKit.SplitBlock) (ht : SplitKit.SplitTwin)
    (hfloor : RankFloorAtSplitDiffering)
    (hmin : ValleyElim.ShortestPlayExists) : SatDifferForkWF :=
  satDifferForkWF_of_covered_rankFloorDiffering
    (FloorRank.splitTwinCovered_of_block_twin hb ht) hfloor hmin

/-- **END TO END FROM THE GATED RAISE-EXCLUSION**
(`FloorAttack.satDifferForkWF_of_rightRaisesHigh` gated). -/
theorem satDifferForkWF_of_rightRaisesHighDiffering
    (hb : SplitKit.SplitBlock) (ht : SplitKit.SplitTwin)
    (hmt : MountainGate.MountainAtSplitsDiffering)
    (hrh : RightRaisesHighDiffering)
    (hmin : ValleyElim.ShortestPlayExists) : SatDifferForkWF :=
  satDifferForkWF_of_rankFloorDiffering hb ht
    (rankFloorDiffering_of_rightRaisesHighDiffering hrh hmt) hmin

/-! ## §3. The gated live-pair / empty-tail tower -/

/-- **`SplitLivePairDiffering`** — the bottom's live pair, gated.  This is the
only place the gate touches the live-set lane: the pair is a residual, but its
*use* inside the empty-tail argument is at a split whose endpoints differ. -/
def SplitLivePairDiffering : Prop :=
  ∀ (u v : State) (ρ : List Move) (F : State)
    (left right : List Move) (c d : Card) (b : Base)
    (pre post tail : List Move),
    MountainGate.RungDiffers u v →
    SplitKit.SplitHyp u v ρ F left right c d b pre post tail →
      TwinLivePair F d

/-- An un-gated live pair is a gated one (the gate is simply discarded). -/
theorem splitLivePairDiffering_of_splitLivePair
    (hl : SplitKit.SplitLivePair) : SplitLivePairDiffering :=
  fun u v ρ F left right c d b pre post tail _ h =>
    hl u v ρ F left right c d b pre post tail h

/-- **THE EMPTY-TAIL TWIN, GATED** (`EmptyTail.twin_of_livePair_emptyTail`
with a gated live pair). -/
theorem twin_of_livePair_emptyTailDiffering
    (hl : SplitLivePairDiffering)
    {u v : State} {ρ : List Move} {F : State}
    {left right : List Move} {c d : Card} {b : Base}
    {pre post tail : List Move}
    (hd : MountainGate.RungDiffers u v)
    (h : SplitKit.SplitHyp u v ρ F left right c d b pre post tail)
    (hpost : post = []) :
    d = c.twin := by
  have hpair : TwinLivePair F d :=
    hl u v ρ F left right c d b pre post tail hd h
  have hcanF : CanRaise F c := BlockKit.emptyTail_canRaise h hpost
  have hcd : c ≠ d := BlockKit.emptyTail_turn_ne h hpost
  rcases (hpair c).mp (CanRaiseS.now c hcanF) with hce | hce
  · exact absurd hce hcd
  · calc d = d.twin.twin := (card_twin_twin d).symm
      _ = c.twin := by rw [← hce]

/-- **`NoEmptyTailDiffering`** — the no-empty-tail clause, gated. -/
def NoEmptyTailDiffering : Prop :=
  ∀ (u v : State) (ρ : List Move) (F : State)
    (left right : List Move) (c d : Card) (b : Base)
    (pre post tail : List Move),
    MountainGate.RungDiffers u v →
    SplitKit.SplitHyp u v ρ F left right c d b pre post tail → post ≠ []

/-- **`NoEmptyTail` FROM THE RAISE BUBBLE, GATED.**
`RaiseLeft.noEmptyTail_of_keepsForward` with the mountain applied at the gated
split. -/
theorem noEmptyTailDiffering_of_keepsForward
    (hl : SplitLivePairDiffering)
    (hmt : MountainGate.MountainAtSplitsDiffering)
    (hrt : RaiseLeft.RaiseLeftAcrossTailLen) :
    NoEmptyTailDiffering := by
  intro u v ρ F left right c d b pre post tail hd h hpost
  have hkeep := h
  obtain ⟨huwf, hsu, hsv, hplay, hsplitAt, hmin, hρ, hleft, hright, hshape,
    hfree, hrightShape⟩ := h
  -- the empty-tail bottom is the twin pair
  have htwin : d = c.twin := twin_of_livePair_emptyTailDiffering hl hd hkeep hpost
  -- and the raise partner `raise c` occurs in the pull-free tail
  have hpart : EmptyTail.RaisePartner tail c :=
    EmptyTail.twin_raisePartner hkeep hpost
      (hmt u v ρ F left right c d b pre post tail hd hkeep) htwin
  obtain ⟨γ, β, htail⟩ := hpart
  -- the green facts at the bottom
  have hFwf : F.WF := SatDifferCensus.ShufflePlayW.wf_end hleft huwf
  have hcanF : CanRaise F c := BlockKit.emptyTail_canRaise hkeep hpost
  -- the right leg, written with the split tail
  have hrightD : ShufflePlayW F (Move.tabToFound d :: tail) v := by
    rw [hrightShape] at hright
    exact hright
  rw [htail] at hrightD
  rw [hpost] at hshape
  -- bubble `raise c` to the front
  have hmem : Move.tabToFound c ∈
      Move.tabToFound d :: (γ ++ Move.tabToFound c :: β) :=
    List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_cons_self ..))
  obtain ⟨tail', htail'play, htail'len⟩ :=
    hrt F v c (Move.tabToFound d :: (γ ++ Move.tabToFound c :: β))
      hFwf hcanF hrightD hmem
  -- the pull's origin
  have hleft' : ShufflePlayW u (pre ++ [Move.foundToTab c b]) F := by
    rw [← hshape]
    simpa using hleft
  obtain ⟨A', hpre, hrest⟩ :=
    ValleyElim.ShufflePlayW_split hleft' pre [Move.foundToTab c b] rfl
  have hstepPull : State.step A' (Move.foundToTab c b) = some F :=
    Elim.step_of_singleton hrest
  have hA' : A'.WF := SatDifferCensus.ShufflePlayW.wf_end hpre huwf
  have hstepRaise : State.step F (Move.tabToFound c) = some A' :=
    step_tabToFound_of_foundToTab hA' hstepPull
  -- the rearranged play, with the adjacent identity pair at the seam
  have hnew : ShufflePlayW u
      (pre ++ Move.foundToTab c b :: Move.tabToFound c :: tail') v := by
    have h := ShufflePlayW_append hleft' htail'play
    simpa [List.append_assoc] using h
  -- delete the pair
  obtain ⟨ρ', hρ'play, hρ'len⟩ :=
    LiveKit.identity_pair_delete (u := u) (v := v)
      (ρ := pre ++ Move.foundToTab c b :: Move.tabToFound c :: tail')
      (α := pre) (β := tail')
      (m1 := Move.foundToTab c b) (m2 := Move.tabToFound c)
      (A := A') (T := F) hnew rfl hpre ⟨hstepPull, hstepRaise⟩
  -- the lengths agree
  have hlenLeft : left.length = pre.length + 1 := by
    rw [hshape]
    simp
  have hlenRight : right.length = tail.length + 1 := by
    rw [hrightShape]
    simp
  have hlenTail : tail'.length = tail.length := by
    have hh := htail'len
    rw [htail]
    simp only [List.length_cons, List.length_append] at hh ⊢
    omega
  have hlenEq :
      (pre ++ Move.foundToTab c b :: Move.tabToFound c :: tail').length = ρ.length := by
    rw [hρ]
    simp only [List.length_append, List.length_cons]
    omega
  rw [hlenEq] at hρ'len
  exact absurd hρ'len (Nat.not_lt.mpr (hmin ρ' hρ'play))

/-- **`SplitBlockDiffering`** — the block clause, gated. -/
def SplitBlockDiffering : Prop :=
  ∀ (u v : State) (ρ : List Move) (F : State)
    (left right : List Move) (c d : Card) (b : Base)
    (pre post tail : List Move),
    MountainGate.RungDiffers u v →
    SplitKit.SplitHyp u v ρ F left right c d b pre post tail →
      ¬ CanRaise F c

/-- **THE BLOCK FROM ITS TWO HALVES, GATED** (`BlockKit.splitBlock_of_parts`). -/
theorem splitBlockDiffering_of_parts
    (h1 : NoEmptyTailDiffering) (h2 : BlockKit.TailCovers) :
    SplitBlockDiffering := by
  intro u v ρ F left right c d b pre post tail hd h
  obtain ⟨hF, -, -, -⟩ := SplitKit.splitHyp_green h
  exact not_canRaise_of_covered hF
    (h2 u v ρ F left right c d b pre post tail h
      (h1 u v ρ F left right c d b pre post tail hd h))

/-- **`SplitResidualDataDiffering`** — the corrected residual, gated. -/
def SplitResidualDataDiffering : Prop :=
  ∀ (u v : State) (ρ : List Move) (F : State)
    (left right : List Move) (c d : Card) (b : Base)
    (pre post tail : List Move),
    MountainGate.RungDiffers u v →
    SplitKit.SplitHyp u v ρ F left right c d b pre post tail →
    d = c.twin ∧ ¬ CanRaise F c ∧
      (∀ e, CanRaiseS F e → c.rank.toIdx ≤ e.rank.toIdx)

/-- **THE STRICT REDUCTION, GATED** (`splitResidualData_of_livePair_block`
with the gate threaded; the twin and floor clauses are proved at the gated
split, so no global `SplitBlock` is needed). -/
theorem splitResidualDataDiffering_of_livePair_blockDiffering
    (hl : SplitLivePairDiffering) (hb : SplitBlockDiffering) :
    SplitResidualDataDiffering := by
  intro u v ρ F left right c d b pre post tail hd h
  obtain ⟨-, hSc, hcanD, -⟩ := SplitKit.splitHyp_green h
  have htwin : d = c.twin := by
    rcases (hl u v ρ F left right c d b pre post tail hd h c).mp hSc with h' | h'
    · have hc : CanRaise F c := by rw [h']; exact hcanD
      exact absurd hc (hb u v ρ F left right c d b pre post tail hd h)
    · rw [h', card_twin_twin]
  refine ⟨htwin, hb u v ρ F left right c d b pre post tail hd h, ?_⟩
  intro e he
  have hdc : d.rank.toIdx = c.rank.toIdx := by rw [htwin, Card.twin_rank]
  rcases (hl u v ρ F left right c d b pre post tail hd h e).mp he with h' | h'
  · rw [h']; omega
  · rw [h', Card.twin_rank]; omega

/-- **THE CORRECTED RESIDUAL IMPLIES `BottomDip`, GATED**
(`SplitKit.bottomDip_of_splitResidualData` with `hdiff` in scope). -/
theorem bottomDip_of_splitResidualDataDiffering
    (h : SplitResidualDataDiffering) : Bridge.BottomDip := by
  intro u v ρ F huwf hsu hsv hcls hdiff hplay hsplit hmin
  obtain ⟨left, right, c, d, b, pre, post, tail,
    hρ, hleft, hright, hshape, hfree, hrightShape⟩ := hsplit
  have hsplit' : ValleyElim.ValleySplitAt u v ρ F :=
    ⟨left, right, c, d, b, pre, post, tail,
      hρ, hleft, hright, hshape, hfree, hrightShape⟩
  have hh : SplitKit.SplitHyp u v ρ F left right c d b pre post tail :=
    ⟨huwf, hsu, hsv, hplay, hsplit', hmin, hρ, hleft, hright, hshape, hfree, hrightShape⟩
  obtain ⟨htwin, hblock, hfloor⟩ :=
    h u v ρ F left right c d b pre post tail hdiff hh
  obtain ⟨-, hcan, hS, hblk, hfloor'⟩ :=
    Bridge.bottom_asymmetry_of_split_data huwf hleft hright hshape hfree hrightShape
      htwin hblock hfloor
  exact ⟨d, hcan, hS, hblk, hfloor'⟩

/-- **THE FULL CHAIN, WITH THE GATED RESIDUAL**
(`satDifferForkWF_of_splitResidualData_drainClosed` gated). -/
theorem satDifferForkWF_of_splitResidualDataDiffering_drainClosed
    (h : SplitResidualDataDiffering) (hmin : ValleyElim.ShortestPlayExists) :
    SatDifferForkWF :=
  Bridge.satDifferForkWF_of_bottom_asymmetry
    (Bridge.bottomAsymmetry_of_bottomDip
      (bottomDip_of_splitResidualDataDiffering h) hmin)
    Bridge.forkExistenceFromAsymmetry_drainClosed

/-- The same chain from the two-clause gated form. -/
theorem satDifferForkWF_of_livePair_blockDiffering_drainClosed
    (hl : SplitLivePairDiffering) (hb : SplitBlockDiffering)
    (hmin : ValleyElim.ShortestPlayExists) : SatDifferForkWF :=
  satDifferForkWF_of_splitResidualDataDiffering_drainClosed
    (splitResidualDataDiffering_of_livePair_blockDiffering hl hb) hmin

/-- **THE CAMPAIGN CHAIN FROM THE TWO GEOMETRIC HALVES, GATED**
(`BlockKit.satDifferForkWF_of_livePair_parts` gated). -/
theorem satDifferForkWF_of_livePair_partsDiffering
    (hl : SplitLivePairDiffering) (h1 : NoEmptyTailDiffering)
    (h2 : BlockKit.TailCovers)
    (hmin : ValleyElim.ShortestPlayExists) : SatDifferForkWF :=
  satDifferForkWF_of_livePair_blockDiffering_drainClosed hl
    (splitBlockDiffering_of_parts h1 h2) hmin

/-! ## §4. The containment from the gated lift, at the gated split -/

/-- **`SplitLivePair` FROM THE LANDING PARTS, GATED**
(`Landing.splitLivePair_of_landing_parts` with a gated containment). -/
theorem splitLivePairDiffering_of_landing_partsDiffering
    (ht : Landing.LandingTwinLive)
    (hf : LandingThirdSuitFreeDiffering) :
    SplitLivePairDiffering := by
  intro u v ρ F left right c d b pre post tail hd h
  have hk := h
  obtain ⟨huwf, -, -, -, -, -, -, hleft, -, hshape, hfree, -⟩ := h
  obtain ⟨A', hpre, hrest⟩ :=
    ValleyElim.ShufflePlayW_split hleft pre (Move.foundToTab c b :: post) hshape
  have hA' : A'.WF := SatDifferCensus.ShufflePlayW.wf_end hpre huwf
  cases hrest with
  | @cons _ B _ _ _ hrev hstep hpost =>
      have hB : B.WF := step_wf hA' hstep
      have hcF : CanRaiseS F c := Bridge.bottom_pull_live huwf hleft hshape hfree
      have hctF : CanRaiseS F c.twin :=
        (Mech.canRaiseS_landing_iff hB hpost hfree c.twin).mp
          (ht u v ρ F left right c d b pre post tail hk A' B hpre hstep)
      have hrungBF : rungAt F c.suit = c.rank.toIdx := by
        rw [ValleyElim.rungAt_eq_of_free_play hpost hfree c.suit]
        exact Mech.rungAt_landing_eq hA' hstep
      have hrungTF : rungAt F c.twin.suit = c.rank.toIdx := by
        have h1 := canRaiseS_rung hctF
        rw [Card.twin_rank] at h1
        exact h1
      have hTwinC : TwinLivePair F c := by
        intro e
        constructor
        · intro he
          have heB : CanRaiseS B e :=
            (Mech.canRaiseS_landing_iff hB hpost hfree e).mpr he
          by_cases hs1 : e.suit = c.suit
          · exact Or.inl (Mech.live_eq_of_suit_left hrungBF he hs1)
          · by_cases hs2 : e.suit = c.twin.suit
            · exact Or.inr (Mech.live_eq_of_suit_twin hrungTF he hs2)
            · exact (hf u v ρ F left right c d b pre post tail hd hk A' B hpre hstep
                e heB hs1 hs2).elim
        · rintro (rfl | rfl)
          · exact hcF
          · exact hctF
      obtain ⟨-, -, -, hSFd⟩ := SplitKit.splitHyp_green hk
      rcases (hTwinC d).mp hSFd with hdc | hdc
      · subst hdc
        exact hTwinC
      · exact Mech.twinLivePair_of_eq_twin hTwinC hdc

/-! ## §5. The top-level gated routes -/

/-- **THE GATED CAMPAIGN THEOREM.**  The exact analogue of
`Frontier.satDifferForkWF_of_keepsForward_and_containment` with the mountain
replaced by `MountainGate.MountainAtSplitsDiffering`:

* `KeepsForward` (-> `RaiseLeftAcrossTailLen`),
* the gated mountain (only consulted at differing-rung splits),
* the twin landing clause,
* the containment residual,
* the cover half,
* the shortest-play interface.

No un-gated mountain hypothesis occurs. -/
theorem satDifferForkWF_of_gated_mountain
    (hkf : ∀ (F : State) (c : Card), F.WF → CanRaise F c → Frontier.KeepsForward F c)
    (hmt : MountainGate.MountainAtSplitsDiffering)
    (htwin : Landing.LandingTwinLive)
    (hcont : Landing.LandingThirdSuitFree)
    (hcov : BlockKit.TailCovers)
    (hmin : ValleyElim.ShortestPlayExists) :
    SatDifferForkWF := by
  have hkf' : ∀ (F : State) (c : Card), F.WF → CanRaise F c →
      RaiseLeft.KeepsForward F c :=
    fun F c hF hc => (Frontier.keepsForward_iff_home F c).mp (hkf F c hF hc)
  have hread : ThirdLive.ThirdBracketRead :=
    ThirdLive.thirdBracketRead_of_landingThirdSuitFree hcont
  have hl : SplitKit.SplitLivePair :=
    ThirdLive.splitLivePair_of_twin_thirdBracketRead htwin hread
  have hne : NoEmptyTailDiffering :=
    noEmptyTailDiffering_of_keepsForward (splitLivePairDiffering_of_splitLivePair hl)
      hmt (RaiseLeft.raise_moves_left_of_keepsForward hkf')
  exact satDifferForkWF_of_livePair_partsDiffering
    (splitLivePairDiffering_of_splitLivePair hl) hne hcov hmin

/-- **THE GATED CAMPAIGN THEOREM, FROM THE GATED RAISE-EXCLUSION.**  Same route,
but the containment is *derived* from `MateRaiseFreeDiffering` by
`landingThirdSuitFreeDiffering_of_mateRaiseFreeDiffering`; the gated
`SplitLivePair` is built directly from the gated containment. -/
theorem satDifferForkWF_of_gated_mountain_of_mateRaiseFree
    (hkf : ∀ (F : State) (c : Card), F.WF → CanRaise F c → Frontier.KeepsForward F c)
    (hmt : MountainGate.MountainAtSplitsDiffering)
    (htwin : Landing.LandingTwinLive)
    (hmrf : MateRaiseFreeDiffering)
    (hcov : BlockKit.TailCovers)
    (hmin : ValleyElim.ShortestPlayExists) :
    SatDifferForkWF := by
  have hkf' : ∀ (F : State) (c : Card), F.WF → CanRaise F c →
      RaiseLeft.KeepsForward F c :=
    fun F c hF hc => (Frontier.keepsForward_iff_home F c).mp (hkf F c hF hc)
  have hcont : LandingThirdSuitFreeDiffering :=
    landingThirdSuitFreeDiffering_of_mateRaiseFreeDiffering hmt hmrf
  have hl : SplitLivePairDiffering :=
    splitLivePairDiffering_of_landing_partsDiffering htwin hcont
  have hne : NoEmptyTailDiffering :=
    noEmptyTailDiffering_of_keepsForward hl hmt
      (RaiseLeft.raise_moves_left_of_keepsForward hkf')
  exact satDifferForkWF_of_livePair_partsDiffering hl hne hcov hmin

/-! ## §5b. VACUOUS COMPATIBILITY: the un-gated hypothesis is FALSE

`MountainGate.mountainAtSplitsDiffering_of_ungated` turns the un-gated
hypothesis into the gated one, but that implication is now VACUOUS: the
un-gated form is refuted unconditionally (`EqualRung.mountainAtSplits_false`,
`Orig2/ForkEqualRungMain.lean`).  The `..._of_ungated_mountain*` twins below
are kept only for interface archaeology and must not be cited.

(LINEAGE: this section was "Conservativity: gating loses nothing"; that reading
is now wrong - the gate is load-bearing, not removable.  The equal-rung
relocation has equal rungs, so `EqualRung.not_rungDiffers` keeps it strictly
outside the gated form.) -/

/-- **VACUOUS.**  The gated theorem from the **FALSE** un-gated hypothesis
(`EqualRung.mountainAtSplits_false`).  Kept only so the old Route A signature
can still elaborate; do not cite. -/
theorem satDifferForkWF_of_ungated_mountain
    (hkf : ∀ (F : State) (c : Card), F.WF → CanRaise F c → Frontier.KeepsForward F c)
    (hms : Direct.MountainAtSplits)
    (htwin : Landing.LandingTwinLive)
    (hcont : Landing.LandingThirdSuitFree)
    (hcov : BlockKit.TailCovers)
    (hmin : ValleyElim.ShortestPlayExists) :
    SatDifferForkWF :=
  satDifferForkWF_of_gated_mountain hkf
    (MountainGate.mountainAtSplitsDiffering_of_ungated hms) htwin hcont hcov hmin

/-- The gated raise-exclusion route from the **un-gated** mountain. -/
theorem satDifferForkWF_of_ungated_mountain_of_mateRaiseFree
    (hkf : ∀ (F : State) (c : Card), F.WF → CanRaise F c → Frontier.KeepsForward F c)
    (hms : Direct.MountainAtSplits)
    (htwin : Landing.LandingTwinLive)
    (hmrf : MateRaiseFreeDiffering)
    (hcov : BlockKit.TailCovers)
    (hmin : ValleyElim.ShortestPlayExists) :
    SatDifferForkWF :=
  satDifferForkWF_of_gated_mountain_of_mateRaiseFree hkf
    (MountainGate.mountainAtSplitsDiffering_of_ungated hms) htwin hmrf hcov hmin

end Gated

/-! ## §6. Axiom battery -/

#print axioms Gated.landingThirdSuitFreeDiffering_of_mateRaiseFreeDiffering
#print axioms Gated.mateRaiseFreeDiffering_of_containmentDiffering
#print axioms Gated.mateRaiseFreeDiffering_iff_containmentDiffering
#print axioms Gated.rankFloorDiffering_of_rightRaisesHighDiffering
#print axioms Gated.satDifferForkWF_of_covered_rankFloorDiffering
#print axioms Gated.satDifferForkWF_of_rankFloorDiffering
#print axioms Gated.satDifferForkWF_of_rightRaisesHighDiffering
#print axioms Gated.splitLivePairDiffering_of_splitLivePair
#print axioms Gated.twin_of_livePair_emptyTailDiffering
#print axioms Gated.noEmptyTailDiffering_of_keepsForward
#print axioms Gated.splitBlockDiffering_of_parts
#print axioms Gated.splitResidualDataDiffering_of_livePair_blockDiffering
#print axioms Gated.bottomDip_of_splitResidualDataDiffering
#print axioms Gated.satDifferForkWF_of_splitResidualDataDiffering_drainClosed
#print axioms Gated.satDifferForkWF_of_livePair_blockDiffering_drainClosed
#print axioms Gated.satDifferForkWF_of_livePair_partsDiffering
#print axioms Gated.splitLivePairDiffering_of_landing_partsDiffering
#print axioms Gated.satDifferForkWF_of_gated_mountain
#print axioms Gated.satDifferForkWF_of_gated_mountain_of_mateRaiseFree
#print axioms Gated.satDifferForkWF_of_ungated_mountain
#print axioms Gated.satDifferForkWF_of_ungated_mountain_of_mateRaiseFree

#check @Gated.MateRaiseFreeDiffering
#check @Gated.LandingThirdSuitFreeDiffering
#check @Gated.RightRaisesHighDiffering
#check @Gated.RankFloorAtSplitDiffering
#check @Gated.NoEmptyTailDiffering
#check @Gated.SplitBlockDiffering
#check @Gated.SplitLivePairDiffering
#check @Gated.SplitResidualDataDiffering
#check @Gated.satDifferForkWF_of_gated_mountain
