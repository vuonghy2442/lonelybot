import Orig2.Fork.Split.ForkPinAt

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-!
# Temp/PinRight — the pin under a free prefix, and the general live-set reduction

READ-ONLY scratch card (`Temp/`).  No source file is modified; nothing is
committed.  Zero `sorry`, zero `Classical.choice`, zero `native_decide`;
axiom battery at the tail.

## What this card proves

The campaign's last clause is `TwinKit.SplitTwinRungPin`
(`Orig2/Fork/Class/ForkTwinLive.lean:362`), i.e. at every `SplitKit.SplitHyp`
`F.nextUp c.twin = true`, equivalently the one-sided
`PairRungKit.SplitTwinRungGe` (`Orig2/Fork/Class/ForkPairRung.lean:168`).

**§1–§2 — THE PIN IS CLOSED UNDER A FREE PREFIX.**  The whole content of the
pin turns out to be a *live-set* statement, not a rung statement:

* a pull of `c` can only create S-liveness among `{c, c.twin}`
  (`LandKit.canRaiseS_pull_creation`, `Orig2/Fork/Split/ForkLandingLocal.lean:269`),
  while free letters preserve it in both directions
  (`Bridge.canRaiseS_of_free_play_iff`, `Orig2/Fork/Split/ForkBridge.lean:85`);

* hence at a split whose prefix `pre` is free, the bottom's whole S-live set is
  `{c, c.twin}` (`live_at_bottom_of_free_pre`), and the raise card — which is
  S-live at `F` by the green licence — is `c` or `c.twin`; the block excludes
  `c`, so `d = c.twin` (`raise_eq_twin_of_free_pre`).  That is the census's
  own mechanism, and it yields the pin (`pin_of_free_pre`).

Consequently, with `SplitKit.SplitBlock` and `PinAt.FreePreSplit` — exactly the
two hypotheses `PinAt.splitTwinRungGe_of_deepTwinFrontier` already takes as
given — the pin, the one-sided `SplitTwinRungGe`, and `PinAt.DeepTwinFrontier`
itself are all THEOREMS (§3).  In particular `DeepTwinFrontier` is not an
independent obligation: it is implied by the split's shape.

**§4 — THE GENERAL CASE REDUCES TO ONE CARD STATEMENT.**  Without a free
prefix, the same induction (along the *raise-free* left leg) says

    every card S-live at the bottom is c, or c.twin, or a card pulled in the
    prefix `pre`, or the twin of such a card          (`live_at_bottom_of_split`)

so under the block

    d = c.twin  ∨  d is a card pulled in `pre`, or its twin
                                     (`raise_eq_twin_or_prePull`).

The named residual `NoPrePullRaise` — the raise card is *never* a prefix-pull
card or its twin — therefore closes the pin (`pin_of_noPrePullRaise`), and it is
not a restatement: it mentions no rung, no licence and no bottom coordinate.

## No circular hypothesis

Nothing here uses `SplitKit.SplitLivePair`, `Mech.LandingLivePair`,
`Mech.LandingAll`, `ValleyElim.ValleyElimNonfork`,
`TwinKit.SplitPairRungEq`, `RungGe.SplitTwinLiveAtBottom` or
`Mech.mechanism_yields`; `SplitKit.SplitBlock` is used only as the *negation* of
`CanRaise F c`, and the green facts of the split only for their licence half.
-/

namespace PinRight

open TwinKit

/-- A pull letter is not a free letter. -/
theorem foundToTab_not_free {c : Card} {b : Base} :
    ¬ ValleyElim.FreeMove (Move.foundToTab c b) := by
  intro hf
  rcases hf with h | ⟨c', b', h⟩
  · cases h
  · cases h

/-- The card of a pull letter is determined by the letter. -/
theorem foundToTab_inj_card {c c' : Card} {b b' : Base}
    (h : Move.foundToTab c b = Move.foundToTab c' b') : c = c' := by
  cases h
  rfl

/-! ## §1. The live set of a raise-free leg is carried by its pulls -/

/-- **A PULL CANNOT CREATE THE S-LIVENESS OF A CARD OUTSIDE `{z, z.twin}`.**
(`LandKit.canRaiseS_pull_creation`'s contrapositive form, stated backwards so it
can be chained with the free-letter transport.) -/
theorem live_leg_subset_pulls {u F : State} {γ : List Move}
    (hplay : ShufflePlayW u γ F)
    (hno : ∀ m ∈ γ, ¬ Bubble.IsRaise m) :
    ∀ (hwu : u.WF) (e : Card), CanRaiseS F e →
      (∃ (z : Card) (b : Base), Move.foundToTab z b ∈ γ ∧ (e = z ∨ e = z.twin)) ∨
        CanRaiseS u e := by
  induction hplay with
  | nil st => intro _ e he; exact Or.inr he
  | @cons st s₁ W m ρ hrev hstep hrest ih =>
      intro hwu e he
      have hwfS : s₁.WF := step_wf hwu hstep
      have hnoTail : ∀ m' ∈ ρ, ¬ Bubble.IsRaise m' :=
        fun m' hm' => hno m' (List.mem_cons_of_mem m hm')
      have hnoHead : ¬ Bubble.IsRaise m := hno m (List.mem_cons_self ..)
      rcases ih hnoTail hwfS e he with ⟨z, bz, hmem, hez⟩ | hback
      · exact Or.inl ⟨z, bz, List.mem_cons_of_mem m hmem, hez⟩
      · -- the head letter has to be pushed backwards across
        have hsingle : ShufflePlayW st [m] s₁ := Walk.cons hrev hstep (Walk.nil s₁)
        cases m with
        | draw =>
            exact Or.inr ((Bridge.canRaiseS_of_free_play_iff hsingle (by
              intro m' hm'
              rw [List.mem_singleton] at hm'
              subst hm'
              exact Or.inl rfl) hwu e).mpr hback)
        | tabToTab x bb =>
            exact Or.inr ((Bridge.canRaiseS_of_free_play_iff hsingle (by
              intro m' hm'
              rw [List.mem_singleton] at hm'
              subst hm'
              exact Or.inr ⟨x, bb, rfl⟩) hwu e).mpr hback)
        | foundToTab z bz =>
            rcases LandKit.canRaiseS_pull_creation hwu hstep hback with
              hez | hez | hback'
            · exact Or.inl ⟨z, bz, List.mem_cons_self .., Or.inl hez⟩
            · exact Or.inl ⟨z, bz, List.mem_cons_self .., Or.inr hez⟩
            · exact Or.inr hback'
        | tabToFound x => exact absurd ⟨x, rfl⟩ hnoHead
        | wasteToFound x => exact absurd hrev (wasteToFound_not_reversibleAtW st x)
        | wasteToTab x bb =>
            exact absurd hrev (wasteToTab_not_reversibleAtW st x bb)

/-- **THE LIVE SET OF A RAISE-FREE LEG FROM A SATURATED STATE.**  Every card
S-live at the far end is a card the leg pulled, or the twin of one.  This is the
"nothing new appears" half of the S-licence. -/
theorem live_subset_pulls_of_raiseFree {u F : State} {γ : List Move}
    (hplay : ShufflePlayW u γ F) (hwu : u.WF) (hsat : SSaturated u)
    (hno : ∀ m ∈ γ, ¬ Bubble.IsRaise m) {e : Card} (he : CanRaiseS F e) :
    ∃ (z : Card) (b : Base), Move.foundToTab z b ∈ γ ∧ (e = z ∨ e = z.twin) := by
  rcases live_leg_subset_pulls hplay hno hwu e he with h | h
  · exact h
  · exact absurd h (hsat e)

/-! ## §2. A free prefix: the bottom's live set is exactly the twin pair -/

/-- **THE LIVE SET AT A FREE-PREFIX SPLIT IS `{c, c.twin}`.**  The prefix is
free (so it transports the licence from the saturated `u`, where nothing is
live), the pull creates only `c` and `c.twin`, and the free tail transports
again. -/
theorem live_at_bottom_of_free_pre
    {u v : State} {ρ : List Move} {F : State} {left right : List Move}
    {c d : Card} {b : Base} {pre post tail : List Move}
    (h : SplitKit.SplitHyp u v ρ F left right c d b pre post tail)
    (hfreepre : ∀ m ∈ pre, ValleyElim.FreeMove m)
    {e : Card} (he : CanRaiseS F e) : e = c ∨ e = c.twin := by
  obtain ⟨A', B, hpre, hstep, hpost⟩ := PairRungKit.split_pre_pull_data h
  obtain ⟨huwf, hsu, -, -, -, -, -, -, -, -, hfreepost, -⟩ := h
  have hA' : A'.WF := SatDifferCensus.ShufflePlayW.wf_end hpre huwf
  have hB : B.WF := step_wf hA' hstep
  have heB : CanRaiseS B e :=
    (Bridge.canRaiseS_of_free_play_iff hpost hfreepost hB e).mpr he
  rcases LandKit.canRaiseS_pull_creation hA' hstep heB with hc | hc | hback
  · exact Or.inl hc
  · exact Or.inr hc
  · exact absurd ((Bridge.canRaiseS_of_free_play_iff hpre hfreepre huwf e).mpr hback)
      (hsu e)

/-- **THE RAISE CARD IS THE PULL CARD'S TWIN** (free prefix + block): the
census's own mechanism `d = c.twin`, read off the live set. -/
theorem raise_eq_twin_of_free_pre
    {u v : State} {ρ : List Move} {F : State} {left right : List Move}
    {c d : Card} {b : Base} {pre post tail : List Move}
    (h : SplitKit.SplitHyp u v ρ F left right c d b pre post tail)
    (hfreepre : ∀ m ∈ pre, ValleyElim.FreeMove m)
    (hblock : ¬ CanRaise F c) : d = c.twin := by
  obtain ⟨-, -, hcanD, -⟩ := SplitKit.splitHyp_green h
  rcases live_at_bottom_of_free_pre h hfreepre (CanRaiseS.now d hcanD) with hd | hd
  · exact absurd (hd ▸ hcanD) hblock
  · exact hd

/-- **THE PIN FROM THE CARD EQUATION `d = c.twin`.**  The mechanism clause read
through `PairRungKit.pin_of_raise_eq_twin` and the green licence. -/
theorem pin_of_raise_eq_twin_rung
    {u v : State} {ρ : List Move} {F : State} {left right : List Move}
    {c d : Card} {b : Base} {pre post tail : List Move}
    (h : SplitKit.SplitHyp u v ρ F left right c d b pre post tail)
    (hd : d = c.twin) :
    rungAt F c.twin.suit = c.rank.toIdx := by
  have hpair : rungAt F c.twin.suit = rungAt F c.suit :=
    PairRungKit.pin_of_raise_eq_twin h hd
  obtain ⟨-, hSc, -, -⟩ := SplitKit.splitHyp_green h
  rw [hpair, canRaiseS_rung hSc]

/-- **THE PIN AT A FREE-PREFIX SPLIT.**  `F.nextUp c.twin = true`, i.e. the
twin suit's rung is exactly the pull card's rank index. -/
theorem pin_of_free_pre
    {u v : State} {ρ : List Move} {F : State} {left right : List Move}
    {c d : Card} {b : Base} {pre post tail : List Move}
    (h : SplitKit.SplitHyp u v ρ F left right c d b pre post tail)
    (hfreepre : ∀ m ∈ pre, ValleyElim.FreeMove m)
    (hblock : ¬ CanRaise F c) :
    rungAt F c.twin.suit = c.rank.toIdx :=
  pin_of_raise_eq_twin_rung h (raise_eq_twin_of_free_pre h hfreepre hblock)

/-! ## §3. The global forms: the pin, the one-sided inequality, the deep residual -/

/-- **`SplitTwinRungPin` FROM `FreePreSplit` + `SplitBlock`.**  The two
hypotheses are exactly the ones the campaign's own consumer
(`PinAt.splitTwinRungGe_of_deepTwinFrontier`) takes as given. -/
theorem splitTwinRungPin_of_freePreSplit
    (hpre : PinAt.FreePreSplit) (hb : SplitKit.SplitBlock) :
    TwinKit.SplitTwinRungPin := by
  intro u v ρ F left right c d b pre post tail h
  exact TwinKit.nextUp_true_iff.mpr
    (pin_of_free_pre h (hpre u v ρ F left right c d b pre post tail h)
      (hb u v ρ F left right c d b pre post tail h))

/-- **`SplitTwinRungGe` — THE CAMPAIGN'S ONE-SIDED CLAUSE — IS A THEOREM**
under `FreePreSplit` + `SplitBlock`. -/
theorem splitTwinRungGe_of_freePreSplit
    (hpre : PinAt.FreePreSplit) (hb : SplitKit.SplitBlock) :
    PairRungKit.SplitTwinRungGe := by
  intro u v ρ F left right c d b pre post tail h
  have hpin := pin_of_free_pre h (hpre u v ρ F left right c d b pre post tail h)
    (hb u v ρ F left right c d b pre post tail h)
  obtain ⟨-, hSc, -, -⟩ := SplitKit.splitHyp_green h
  have hsig : rungAt F c.suit = c.rank.toIdx := canRaiseS_rung hSc
  omega

/-- **`PinAt.DeepTwinFrontier` IS A THEOREM** under `FreePreSplit` +
`SplitBlock`: the previous card's residual is not an independent obligation. -/
theorem deepTwinFrontier_of_freePreSplit
    (hpre : PinAt.FreePreSplit) (hb : SplitKit.SplitBlock) :
    PinAt.DeepTwinFrontier :=
  (PinAt.splitTwinRungPin_iff_deepTwinFrontier hb hpre).mp
    (splitTwinRungPin_of_freePreSplit hpre hb)

/-- **THE DEEP ENDPOINT IS EXACTLY ON THE FRONTIER** (explicit transport).  At a
free-prefix split the twin suit sits at `c`'s rank index at the saturated deep
endpoint — the lower bound is §3 and the upper bound is the block's free half
(`PinAt.deep_upper_of_block`). -/
theorem deep_twin_rung_eq_of_freePreSplit'
    {u v : State} {ρ : List Move} {F : State} {left right : List Move}
    {c d : Card} {b : Base} {pre post tail : List Move}
    (hpre : PinAt.FreePreSplit) (hb : SplitKit.SplitBlock)
    (h : SplitKit.SplitHyp u v ρ F left right c d b pre post tail)
    (htrans : ∀ A' : State, ShufflePlayW u pre A' →
      rungAt u c.twin.suit = rungAt A' c.twin.suit) :
    rungAt u c.twin.suit = c.rank.toIdx := by
  have hle : rungAt u c.twin.suit ≤ c.rank.toIdx :=
    PinAt.deep_upper_of_block h htrans (hb u v ρ F left right c d b pre post tail h)
  have hge : c.rank.toIdx ≤ rungAt u c.twin.suit :=
    (deepTwinFrontier_of_freePreSplit hpre hb)
      u v ρ F left right c d b pre post tail h htrans
  omega

/-- **THE DEEP ENDPOINT IS EXACTLY ON THE FRONTIER.**  At a free-prefix split
the twin suit sits at `c`'s rank index at the saturated deep endpoint — the
lower bound is §3 and the upper bound is the block's free half
(`PinAt.deep_upper_of_block`).  The prefix-transport side condition is derived
from freeness, not assumed. -/
theorem deep_twin_rung_eq_of_freePreSplit
    {u v : State} {ρ : List Move} {F : State} {left right : List Move}
    {c d : Card} {b : Base} {pre post tail : List Move}
    (hpre : PinAt.FreePreSplit) (hb : SplitKit.SplitBlock)
    (h : SplitKit.SplitHyp u v ρ F left right c d b pre post tail) :
    rungAt u c.twin.suit = c.rank.toIdx := by
  have htrans : ∀ A' : State, ShufflePlayW u pre A' →
      rungAt u c.twin.suit = rungAt A' c.twin.suit :=
    fun A' hplay => (ValleyElim.rungAt_eq_of_free_play hplay
      (hpre u v ρ F left right c d b pre post tail h) c.twin.suit).symm
  exact deep_twin_rung_eq_of_freePreSplit' hpre hb h htrans

/-! ## §4. The general reduction: the raise card versus the prefix's pulls -/

/-- `PrePullPair pre e` — `e` is a card pulled in `pre`, or its twin.  This is
the set on which a pull can *create* S-liveness. -/
def PrePullPair (pre : List Move) (e : Card) : Prop :=
  ∃ (z : Card) (b : Base), Move.foundToTab z b ∈ pre ∧ (e = z ∨ e = z.twin)

/-- **THE LIVE SET AT ANY SPLIT WHOSE LEFT LEG IS RAISE-FREE.** -/
theorem live_at_bottom_of_split
    {u v : State} {ρ : List Move} {F : State} {left right : List Move}
    {c d : Card} {b : Base} {pre post tail : List Move}
    (h : SplitKit.SplitHyp u v ρ F left right c d b pre post tail)
    (hraiseFree : ∀ m ∈ left, ¬ Bubble.IsRaise m)
    {e : Card} (he : CanRaiseS F e) :
    e = c ∨ e = c.twin ∨ PrePullPair pre e := by
  obtain ⟨huwf, hsu, -, -, -, -, -, hleft, -, hshape, hfree, -⟩ := h
  rcases live_subset_pulls_of_raiseFree hleft huwf hsu hraiseFree he with
    ⟨z, bz, hmem, hez⟩
  -- locate the pull letter: in `pre`, at the valley pull, or (not) in `post`
  have hmem' : Move.foundToTab z bz ∈ pre ++ Move.foundToTab c b :: post := by
    rw [← hshape]; exact hmem
  rcases List.mem_append.mp hmem' with hpre | hrest
  · exact Or.inr (Or.inr ⟨z, bz, hpre, hez⟩)
  · rcases List.mem_cons.mp hrest with hhead | hpost
    · -- the valley pull itself
      have hzc : z = c := foundToTab_inj_card hhead
      subst hzc
      rcases hez with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · -- `post` is free, so it carries no pull
      exact absurd (hfree (Move.foundToTab z bz) hpost) foundToTab_not_free

/-- **THE RAISE CARD IS THE TWIN, OR A PREFIX-PULL CARD OR ITS TWIN.**  This is
the exact place where a non-free prefix enters: `pre`'s own pulls are the only
other source of S-liveness at the bottom. -/
theorem raise_eq_twin_or_prePull
    {u v : State} {ρ : List Move} {F : State} {left right : List Move}
    {c d : Card} {b : Base} {pre post tail : List Move}
    (h : SplitKit.SplitHyp u v ρ F left right c d b pre post tail)
    (hraiseFree : ∀ m ∈ left, ¬ Bubble.IsRaise m)
    (hblock : ¬ CanRaise F c) :
    d = c.twin ∨ PrePullPair pre d := by
  obtain ⟨-, -, hcanD, -⟩ := SplitKit.splitHyp_green h
  rcases live_at_bottom_of_split h hraiseFree (CanRaiseS.now d hcanD) with
    hd | hd | hd
  · exact absurd (hd ▸ hcanD) hblock
  · exact Or.inl hd
  · exact Or.inr hd

/-- **`NoPrePullRaise` — THE NAMED RESIDUAL.**  At every split whose left leg is
raise-free, the raise card is neither a card pulled in the prefix nor the twin of
one.  Card-level; no rung, no licence, no bottom coordinate. -/
def NoPrePullRaise : Prop :=
  ∀ (u v : State) (ρ : List Move) (F : State) (left right : List Move)
    (c d : Card) (b : Base) (pre post tail : List Move),
    SplitKit.SplitHyp u v ρ F left right c d b pre post tail →
    (∀ m ∈ left, ¬ Bubble.IsRaise m) →
    ¬ PrePullPair pre d

/-- **THE PIN FROM THE NAMED RESIDUAL.**  `NoPrePullRaise` + the block gives the
pin at every split whose left leg is raise-free; with the measured mountain datum
(`MountainKit.MountainSplit`, which supplies exactly that) it gives the global
pin. -/
theorem pin_of_noPrePullRaise
    (hres : NoPrePullRaise)
    {u v : State} {ρ : List Move} {F : State} {left right : List Move}
    {c d : Card} {b : Base} {pre post tail : List Move}
    (h : SplitKit.SplitHyp u v ρ F left right c d b pre post tail)
    (hraiseFree : ∀ m ∈ left, ¬ Bubble.IsRaise m)
    (hblock : ¬ CanRaise F c) :
    rungAt F c.twin.suit = c.rank.toIdx := by
  rcases raise_eq_twin_or_prePull h hraiseFree hblock with hd | hbad
  · exact pin_of_raise_eq_twin_rung h hd
  · exact absurd hbad (hres u v ρ F left right c d b pre post tail h hraiseFree)

/-- **THE PIN FROM THE RESIDUAL, GLOBALLY** (the mountain datum supplies the
raise-freeness of the left leg). -/
theorem splitTwinRungPin_of_noPrePullRaise
    (hres : NoPrePullRaise)
    (hms : ∀ (u v : State) (ρ : List Move) (F : State) (left right : List Move)
      (c d : Card) (b : Base) (pre post tail : List Move),
      SplitKit.SplitHyp u v ρ F left right c d b pre post tail →
      MountainKit.MountainSplit left right)
    (hb : SplitKit.SplitBlock) : TwinKit.SplitTwinRungPin := by
  intro u v ρ F left right c d b pre post tail h
  exact TwinKit.nextUp_true_iff.mpr
    (pin_of_noPrePullRaise hres h (hms u v ρ F left right c d b pre post tail h).1
      (hb u v ρ F left right c d b pre post tail h))

/-! ## §5. The campaign hook -/

/-- **THE RESIDUAL IS EMPTY ON FREE PREFIXES** — consistency of §2 with §4. -/
theorem noPrePullRaise_of_freePreSplit (hpre : PinAt.FreePreSplit) :
    NoPrePullRaise := by
  intro u v ρ F left right c d b pre post tail h _ hpair
  obtain ⟨z, bz, hmem, -⟩ := hpair
  exact foundToTab_not_free
    (hpre u v ρ F left right c d b pre post tail h (Move.foundToTab z bz) hmem)

/-- **THE CAMPAIGN CHAIN, WITH THE PIN DISCHARGED.**  `FreePreSplit` +
`SplitBlock` + the containment lane's clause + the shortest-play interface give
`SatDifferForkWF`.  The pin is *derived* here (it was the last independent
clause); `SplitContainment` is the other lane's named input and is only consumed,
never proved. -/
theorem satDifferForkWF_of_freePreSplit_block_containment
    (hpre : PinAt.FreePreSplit) (hb : SplitKit.SplitBlock)
    (hc : TwinKit.SplitContainment) (hmin : ValleyElim.ShortestPlayExists) :
    SatDifferForkWF :=
  PairRungKit.satDifferForkWF_of_block_containment_of_ge hb hc
    (splitTwinRungGe_of_freePreSplit hpre hb) hmin

/-! ## §6. Battery -/

#print axioms PinRight.foundToTab_not_free
#print axioms PinRight.foundToTab_inj_card
#print axioms PinRight.live_leg_subset_pulls
#print axioms PinRight.live_subset_pulls_of_raiseFree
#print axioms PinRight.live_at_bottom_of_free_pre
#print axioms PinRight.raise_eq_twin_of_free_pre
#print axioms PinRight.pin_of_raise_eq_twin_rung
#print axioms PinRight.pin_of_free_pre
#print axioms PinRight.splitTwinRungPin_of_freePreSplit
#print axioms PinRight.splitTwinRungGe_of_freePreSplit
#print axioms PinRight.deepTwinFrontier_of_freePreSplit
#print axioms PinRight.deep_twin_rung_eq_of_freePreSplit'
#print axioms PinRight.deep_twin_rung_eq_of_freePreSplit
#print axioms PinRight.live_at_bottom_of_split
#print axioms PinRight.raise_eq_twin_or_prePull
#print axioms PinRight.pin_of_noPrePullRaise
#print axioms PinRight.splitTwinRungPin_of_noPrePullRaise
#print axioms PinRight.noPrePullRaise_of_freePreSplit
#print axioms PinRight.satDifferForkWF_of_freePreSplit_block_containment

end PinRight
