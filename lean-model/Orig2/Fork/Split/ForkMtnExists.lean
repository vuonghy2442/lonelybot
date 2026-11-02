import Orig2.Fork.Split.ForkGatedTower

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-!
# MtnExists - the mountain as an **∃**-claim

Scratch card.  READ-ONLY on `Orig2/`; no source edit, no commit.  Zero `sorry`,
zero `Classical.choice`, zero `native_decide`; the axiom battery is at the tail.

## What this card does

The campaign's mountain hypothesis is stated *universally over geodesics*:

```text
MountainGate.MountainAtSplitsDiffering
  ∀ split data, RungDiffers u v → SplitHyp ... → MountainSplit left right
```

i.e. **every** minimal play between the endpoints is a mountain.  The card
`FORKS` this into the ∃-form the campaign actually consumes:

```text
MountainMinExists
  ∀ u v, u.WF → SSaturated u → SSaturated v → sameOrbit u v → RungDiffers u v →
    ∃ ρ, ShufflePlayW u ρ v
       ∧ (∀ ρ', ShufflePlayW u ρ' v → ρ.length ≤ ρ'.length)   -- ρ is a geodesic
       ∧ ∃ split data, ValleySplitAt u v ρ F ∧ MountainSplit left right
```

* **§1** the definition (`MountainMinExists`, with `ValleySplitData` as its
  split-data carrier - the conjuncts of `ValleyElim.ValleySplitAt` spelled out
  so that the pivot cards stay in scope; cf. the binder-scope defect of
  `Bridge.SplitResidual`, `Temp/Mountain2_Report.md` §1).
* **§2** the reduction: `MountainAtSplitsDiffering → MountainMinExists`
  (`mountainMinExists_of_gated`).  The ∀-form is *strictly* stronger: the ∃
  picks one geodesic and never has to control the others.
* **§3** the campaign, re-derived: `satDifferForkWF_of_mountainMinExists` is
  `Gated.satDifferForkWF_of_gated_mountain` with the ∀-mountain replaced by
  `MountainMinExists`.  The proof *chooses* the mountain geodesic, takes its
  split, and applies the existing residual cards to THAT split only
  (`noEmptyTail_at` is the local instance of
  `Gated.noEmptyTailDiffering_of_keepsForward`).
* **§4** axiom battery.

## Why the ∃-form matters

A geodesic containing a **cross-suit** `raise c ; … ; pull d b` (`c.suit ≠
d.suit`) is simply not the geodesic we pick.  The cross-suit case is exactly
where the ∀-form has no technique (`Orig2/Fork/Local/ForkRelocate.lean`,
`twoSuit_gap_is_shortest`: a two-letter cross-suit play is shortest; the
withdrawn `RaiseBeforePullShortens`, `Orig2/Fork/Split/ForkMountainShape.lean:521`, dies at
unsaturated endpoints).  The ∃-form has no obligation to control it.

`hmin : ShortestPlayExists` is *carried* on the composed theorem for interface
compatibility (the other route's signature); the ∃-form supplies its own
minimality witness, so the core proof does not consume it.  Both the with-`hmin`
and the `hmin`-free forms are proved.
-/

namespace MtnExists

open ValleyElim

/-! ## §1. The ∃-form -/

/-- **`ValleySplitData`** - the split data of `ValleyElim.ValleySplitAt u v ρ F`,
with every pivot card named.  `ValleySplitAt` hides `left right c d b pre post
tail` behind one `∃`, so a `MountainSplit left right` stated outside it would be
about *fresh* cards (the binder-scope defect that killed `Bridge.SplitResidual`).
This carrier keeps them in scope. -/
def ValleySplitData (u v : State) (ρ : List Move) (F : State)
    (left right : List Move) (c d : Card) (b : Base)
    (pre post tail : List Move) : Prop :=
  ρ = left ++ right ∧
  ShufflePlayW u left F ∧
  ShufflePlayW F right v ∧
  left = pre ++ Move.foundToTab c b :: post ∧
  (∀ m ∈ post, FreeMove m) ∧
  right = Move.tabToFound d :: tail

/-- The carrier is exactly `ValleySplitAt`. -/
theorem valleySplitAt_of_data {u v : State} {ρ : List Move} {F : State}
    {left right : List Move} {c d : Card} {b : Base}
    {pre post tail : List Move}
    (h : ValleySplitData u v ρ F left right c d b pre post tail) :
    ValleySplitAt u v ρ F :=
  ⟨left, right, c, d, b, pre, post, tail,
    h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

/-- **`MountainMinExists` - THE ∃-FORM OF THE GATED MOUNTAIN.**

Between `WF`, `SSaturated`, same-orbit endpoints with differing rungs, there is
**one** geodesic `ρ` which carries a valley split whose left leg is raise-free
and whose right leg is pull-free.  No obligation on any other geodesic. -/
def MountainMinExists : Prop :=
  ∀ (u v : State), u.WF → SSaturated u → SSaturated v → sameOrbitSetoid.r u v →
    (∃ σ : Suit, rungAt u σ ≠ rungAt v σ) →
    ∃ (ρ : List Move),
      ShufflePlayW u ρ v ∧
      (∀ ρ' : List Move, ShufflePlayW u ρ' v → ρ.length ≤ ρ'.length) ∧
      ∃ (F : State) (left right : List Move) (c d : Card) (b : Base)
        (pre post tail : List Move),
        ValleySplitData u v ρ F left right c d b pre post tail ∧
        MountainKit.MountainSplit left right

/-- The ∃-form at a split whose data have been unfolded (the working shape). -/
theorem mountainSplit_of_minExists (h : MountainMinExists)
    {u v : State} (huwf : u.WF) (hsu : SSaturated u) (hsv : SSaturated v)
    (hcls : sameOrbitSetoid.r u v)
    (hdiff : ∃ σ : Suit, rungAt u σ ≠ rungAt v σ) :
    ∃ (ρ : List Move) (F : State) (left right : List Move)
      (c d : Card) (b : Base) (pre post tail : List Move),
      ShufflePlayW u ρ v ∧
      (∀ ρ' : List Move, ShufflePlayW u ρ' v → ρ.length ≤ ρ'.length) ∧
      ValleySplitData u v ρ F left right c d b pre post tail ∧
      MountainKit.MountainSplit left right := by
  obtain ⟨ρ, hplay, hmin, F, left, right, c, d, b, pre, post, tail, hdata, hms⟩ :=
    h u v huwf hsu hsv hcls hdiff
  exact ⟨ρ, F, left, right, c, d, b, pre, post, tail, hplay, hmin, hdata, hms⟩

/-! ## §2. The ∀-form implies the ∃-form -/

/-- **THE REDUCTION.**  `MountainAtSplitsDiffering` (every minimal play is a
mountain) implies `MountainMinExists` (some minimal play is).  Take a geodesic
from `ShortestPlayExists`, its valley split from `valley_exists`, and apply the
∀-form there. -/
theorem mountainMinExists_of_gated
    (hmt : MountainGate.MountainAtSplitsDiffering)
    (hmin : ValleyElim.ShortestPlayExists) :
    MountainMinExists := by
  intro u v huwf hsu hsv hcls hdiff
  obtain ⟨ρ, hplay, hminlen⟩ := hmin u v huwf hsu hsv hcls hdiff
  obtain ⟨F, left, right, c, d, b, pre, post, tail,
    hρ, hleft, hright, hshape, hfree, hrightShape⟩ :=
    ValleyElim.valley_exists huwf hsu hsv hdiff hplay
  refine ⟨ρ, hplay, hminlen, F, left, right, c, d, b, pre, post, tail,
    ⟨hρ, hleft, hright, hshape, hfree, hrightShape⟩, ?_⟩
  exact hmt u v ρ F left right c d b pre post tail hdiff
    ⟨huwf, hsu, hsv, hplay,
      ⟨left, right, c, d, b, pre, post, tail, hρ, hleft, hright, hshape, hfree,
        hrightShape⟩,
      hminlen, hρ, hleft, hright, hshape, hfree, hrightShape⟩

/-! ## §2b. The census claim (M1) implies the ∃-form

The probe measures **M1** on minimal plays: *no raise occurs before a later
pull* (`Temp/MtnExists_probe.py`).  M1 is the letter-order form of
`MountainSplit` (`Orig2/Fork/Split/ForkMountainShape.lean:172`), but the equivalence there
is stated at an *arbitrary* cut; the mountain needs the cut to be the **valley**
one.  The two small rows below place M1 at the valley cut, so the census claim
is a legitimate input to `MountainMinExists`. -/

/-- A raise is never a free letter. -/
theorem not_free_of_isRaise {m : Move} (h : Bubble.IsRaise m) : ¬ FreeMove m := by
  obtain ⟨c, rfl⟩ := h
  intro hf
  rcases hf with h | ⟨c', b', h⟩
  · cases h
  · cases h

/-- **M1 AT THE VALLEY CUT.**  If the play is M1 and `left` ends with a pull
(with a free tail) while `right` opens with a raise, then the valley split is a
mountain: no raise in `left` (it would precede the cut's pull), no pull in
`right` (it would follow the cut's raise). -/
theorem mountainSplit_of_mountainOrder_valley
    {ρ left right pre post tail : List Move} {c d : Card} {b : Base}
    (hρ : ρ = left ++ right)
    (hno : MountainKit.NoRaiseBeforePull ρ)
    (hshape : left = pre ++ Move.foundToTab c b :: post)
    (hfree : ∀ m ∈ post, FreeMove m)
    (hrightShape : right = Move.tabToFound d :: tail) :
    MountainKit.MountainSplit left right := by
  constructor
  · intro m hm hmr
    obtain ⟨e, rfl⟩ := hmr
    rw [hshape] at hm
    rcases List.mem_append.mp hm with hpre | hrest
    · -- `raise e` sits in `pre`, strictly before the cut's pull
      obtain ⟨p1, p2, hpreEq⟩ := List.mem_iff_append.mp hpre
      refine hno ⟨p1, p2 ++ Move.foundToTab c b :: (post ++ right), e, c, b, ?_, ?_⟩
      · rw [hρ, hshape, hpreEq]
        simp [List.append_assoc]
      · exact List.mem_append_right _ (List.mem_cons_self ..)
    · -- inside `pull c b :: post`: the head is a pull, the tail is free
      rcases List.mem_cons.mp hrest with hhead | hpost
      · exact (ValleyElim.foundToTab_ne_tabToFound c b e) hhead.symm
      · exact not_free_of_isRaise ⟨e, rfl⟩ (hfree _ hpost)
  · intro m hm hmp
    obtain ⟨e, b', rfl⟩ := hmp
    rw [hrightShape] at hm
    rcases List.mem_cons.mp hm with hhead | htail
    · exact (ValleyElim.foundToTab_ne_tabToFound e b' d) hhead
    · exact hno ⟨left, tail, d, e, b', by rw [hρ, hrightShape], htail⟩

/-- **THE CENSUS CLAIM, AS A HYPOTHESIS.**  Every minimal play between `WF`,
`SSaturated`, differing-rung endpoints is M1.  This is exactly what
`Temp/Mountain_probe.py` measured (`M1 = 51 116 / 51 116`,
`Temp/Mountain_Report.md`) and what `Temp/MtnExists_probe.py` re-measures per
ordered pair. -/
def EveryMinPlayMountainOrder : Prop :=
  ∀ (u v : State) (ρ : List Move), u.WF → SSaturated u → SSaturated v →
    (∃ σ : Suit, rungAt u σ ≠ rungAt v σ) →
    ShufflePlayW u ρ v →
    (∀ ρ' : List Move, ShufflePlayW u ρ' v → ρ.length ≤ ρ'.length) →
    MountainKit.NoRaiseBeforePull ρ

/-- **M1 ⇒ THE ∃-FORM** (the census claim discharges `MountainMinExists`). -/
theorem mountainMinExists_of_mountainOrder
    (h : EveryMinPlayMountainOrder)
    (hmin : ValleyElim.ShortestPlayExists) :
    MountainMinExists := by
  intro u v huwf hsu hsv hcls hdiff
  obtain ⟨ρ, hplay, hminlen⟩ := hmin u v huwf hsu hsv hcls hdiff
  obtain ⟨F, left, right, c, d, b, pre, post, tail,
    hρ, hleft, hright, hshape, hfree, hrightShape⟩ :=
    ValleyElim.valley_exists huwf hsu hsv hdiff hplay
  refine ⟨ρ, hplay, hminlen, F, left, right, c, d, b, pre, post, tail,
    ⟨hρ, hleft, hright, hshape, hfree, hrightShape⟩, ?_⟩
  exact mountainSplit_of_mountainOrder_valley hρ
    (h u v ρ huwf hsu hsv hdiff hplay hminlen) hshape hfree hrightShape

/-! ## §3. The campaign from the ∃-form -/

/-- **THE EMPTY-TAIL CONTRADICTION, AT ONE SPLIT.**

`Gated.noEmptyTailDiffering_of_keepsForward` with the mountain *supplied*
(`hms : MountainSplit left right`) instead of derived from a ∀-hypothesis.  This
is the only place the campaign consumes the mountain, and it consumes it at the
single split under consideration - which is exactly what the ∃-form licenses. -/
theorem noEmptyTail_at
    (hl : SplitKit.SplitLivePair)
    {u v : State} {ρ : List Move} {F : State}
    {left right : List Move} {c d : Card} {b : Base}
    {pre post tail : List Move}
    (h : SplitKit.SplitHyp u v ρ F left right c d b pre post tail)
    (hpost : post = [])
    (hms : MountainKit.MountainSplit left right)
    (hrt : RaiseLeft.RaiseLeftAcrossTailLen) : False := by
  have hkeep := h
  obtain ⟨huwf, hsu, hsv, hplay, hsplitAt, hmin, hρ, hleft, hright, hshape,
    hfree, hrightShape⟩ := h
  -- the empty-tail bottom is the twin pair
  have htwin : d = c.twin := EmptyTail.twin_of_livePair_emptyTail hl hkeep hpost
  -- and the raise partner `raise c` occurs in the pull-free tail
  have hpart : EmptyTail.RaisePartner tail c :=
    EmptyTail.twin_raisePartner hkeep hpost hms htwin
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

/-- **THE CAMPAIGN THEOREM FROM THE ∃-FORM.**

Same conjuncts as `Gated.satDifferForkWF_of_gated_mountain` with the ∀-mountain
replaced by `MountainMinExists`.  The proof chooses the mountain geodesic and
its split, then runs exactly the existing residual cards at THAT split. -/
theorem satDifferForkWF_of_mountainMinExists_core
    (hkf : ∀ (F : State) (c : Card), F.WF → CanRaise F c → Frontier.KeepsForward F c)
    (hM : MountainMinExists)
    (htwin : Landing.LandingTwinLive)
    (hcont : Landing.LandingThirdSuitFree)
    (hcov : BlockKit.TailCovers) :
    SatDifferForkWF := by
  have hkf' : ∀ (F : State) (c : Card), F.WF → CanRaise F c →
      RaiseLeft.KeepsForward F c :=
    fun F c hF hc => (Frontier.keepsForward_iff_home F c).mp (hkf F c hF hc)
  have hrt : RaiseLeft.RaiseLeftAcrossTailLen :=
    RaiseLeft.raise_moves_left_of_keepsForward hkf'
  have hread : ThirdLive.ThirdBracketRead :=
    ThirdLive.thirdBracketRead_of_landingThirdSuitFree hcont
  have hl : SplitKit.SplitLivePair :=
    ThirdLive.splitLivePair_of_twin_thirdBracketRead htwin hread
  intro u v huwf hsu hsv hcls hdiff
  -- choose the mountain geodesic and its split
  obtain ⟨ρ, F, left, right, c, d, b, pre, post, tail,
    hplay, hminlen, hdata, hms⟩ :=
    mountainSplit_of_minExists hM huwf hsu hsv hcls hdiff
  obtain ⟨hρ, hleft, hright, hshape, hfree, hrightShape⟩ := hdata
  -- the split hypothesis at THAT split
  have hh : SplitKit.SplitHyp u v ρ F left right c d b pre post tail :=
    ⟨huwf, hsu, hsv, hplay,
      ⟨left, right, c, d, b, pre, post, tail, hρ, hleft, hright, hshape, hfree,
        hrightShape⟩,
      hminlen, hρ, hleft, hright, hshape, hfree, hrightShape⟩
  -- the free tail is nonempty (the mountain is consumed right here)
  have hpost : post ≠ [] := fun hpost0 => noEmptyTail_at hl hh hpost0 hms hrt
  -- the block clause at this split
  have hF : F.WF := SatDifferCensus.ShufflePlayW.wf_end hleft huwf
  have hblock : ¬ CanRaise F c :=
    not_canRaise_of_covered hF
      (hcov u v ρ F left right c d b pre post tail hh hpost)
  -- the twin clause and the rank floor at this split
  have hpair : TwinLivePair F d := hl u v ρ F left right c d b pre post tail hh
  obtain ⟨-, hSc, hcanD, -⟩ := SplitKit.splitHyp_green hh
  have htwinC : d = c.twin := by
    rcases (hpair c).mp hSc with h' | h'
    · exact absurd (by rw [h']; exact hcanD) hblock
    · rw [h', card_twin_twin]
  have hfloor : ∀ e, CanRaiseS F e → c.rank.toIdx ≤ e.rank.toIdx := by
    intro e he
    have hdc : d.rank.toIdx = c.rank.toIdx := by rw [htwinC, Card.twin_rank]
    rcases (hpair e).mp he with h' | h'
    · rw [h']; omega
    · rw [h', Card.twin_rank]; omega
  -- the bottom asymmetry, then the drain-closed fork
  obtain ⟨hr, hcanD', hS', hblockT', hfloor'⟩ :=
    Bridge.bottom_asymmetry_of_split_data huwf hleft hright hshape hfree hrightShape
      htwinC hblock hfloor
  obtain ⟨F', y, hrF', hfork⟩ :=
    Bridge.forkExistenceFromAsymmetry_drainClosed F d hF hcanD' hS' hblockT' hfloor'
  exact ⟨F', y, sameOrbitSetoid.iseqv.trans hr hrF', hfork⟩

/-- **THE BRIEF'S SHAPE.**  The ∃-form with the shortest-play interface carried
(as in `Gated.satDifferForkWF_of_gated_mountain`).  `hmin` is not consumed: the
∃-form carries its own minimality witness (`MountainMinExists` §1). -/
theorem satDifferForkWF_of_mountainMinExists
    (hkf : ∀ (F : State) (c : Card), F.WF → CanRaise F c → Frontier.KeepsForward F c)
    (hM : MountainMinExists)
    (htwin : Landing.LandingTwinLive)
    (hcont : Landing.LandingThirdSuitFree)
    (hcov : BlockKit.TailCovers)
    (hmin : ValleyElim.ShortestPlayExists) :
    SatDifferForkWF :=
  satDifferForkWF_of_mountainMinExists_core hkf hM htwin hcont hcov

/-- **END TO END FROM THE ∀-FORM, THROUGH THE ∃-FORM.**  Conservativity check:
the ∃-route recovers the ∀-route's conclusion (`Gated.satDifferForkWF_of_gated_mountain`). -/
theorem satDifferForkWF_of_gated_mountain_via_minExists
    (hkf : ∀ (F : State) (c : Card), F.WF → CanRaise F c → Frontier.KeepsForward F c)
    (hmt : MountainGate.MountainAtSplitsDiffering)
    (htwin : Landing.LandingTwinLive)
    (hcont : Landing.LandingThirdSuitFree)
    (hcov : BlockKit.TailCovers)
    (hmin : ValleyElim.ShortestPlayExists) :
    SatDifferForkWF :=
  satDifferForkWF_of_mountainMinExists hkf
    (mountainMinExists_of_gated hmt hmin) htwin hcont hcov hmin

end MtnExists

/-! ## §4. Axiom battery -/

#print axioms MtnExists.valleySplitAt_of_data
#print axioms MtnExists.mountainSplit_of_minExists
#print axioms MtnExists.mountainMinExists_of_gated
#print axioms MtnExists.not_free_of_isRaise
#print axioms MtnExists.mountainSplit_of_mountainOrder_valley
#print axioms MtnExists.mountainMinExists_of_mountainOrder
#print axioms MtnExists.noEmptyTail_at
#print axioms MtnExists.satDifferForkWF_of_mountainMinExists_core
#print axioms MtnExists.satDifferForkWF_of_mountainMinExists
#print axioms MtnExists.satDifferForkWF_of_gated_mountain_via_minExists

#check @MtnExists.MountainMinExists
#check @MtnExists.ValleySplitData
#check @MtnExists.satDifferForkWF_of_mountainMinExists
