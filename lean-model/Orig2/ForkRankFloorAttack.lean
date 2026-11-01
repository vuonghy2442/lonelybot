import Orig2.ForkThirdLive
import Orig2.ForkDirect
import Orig2.ForkMountainAccount
import Orig2.ForkRungGe
import Orig2.ForkRankFloor

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-!
# Orig2/ForkRankFloorAttack — attacking `RankFloorAtSplit`

READ-ONLY scratch card (no source edit, no commit).  Zero `sorry`, zero
`Classical.choice`, zero `native_decide`; axiom battery at the tail.

This card attacks the *only* conjunct of `Temp/Floor_RankChain.lean`, the floor

    RankFloorAtSplit :  ∀ e, CanRaiseS F e → d.rank.toIdx ≤ e.rank.toIdx

at a valley bottom `F` of a minimal play (`d` = the raise card).

## What is proved (all green)

1. **THE KILL DICHOTOMY, WITH RANKS** (`exists_raise_of_rank`): every card
   S-live at the bottom has its *own rank* raised in the right leg — the leg
   raises `e` or `e.twin` (`Direct.canRaiseS_end_or_bad_raise`; `SSaturated v`
   kills the surviving arm).  The twin arm is real: raising `e.twin` removes the
   cover that licences `e`.

2. **THE THIRD-SUIT DICHOTOMY** (`rise_or_twin_raise`): for a third-suit live
   card, either `e.suit`'s rung climbs strictly to the far endpoint (the ledger
   `raisesOf right e.suit = rungAt v − rungAt F`, since the right leg is
   pull-free), or the right leg raises `e.twin`.

3. **THE FLOOR REDUCES TO A RAISE-EXCLUSION** (`rankFloor_of_rightRaisesHigh`):
   if the right leg raises no card below `d`'s rank, the floor holds.  This is a
   play-level *inequality* (`RightRaisesHigh`), with no live-set vocabulary at
   all, and it is one line from (1): the raised card has `e`'s rank.

4. **THE FLOOR IS AUTOMATIC ON THE TWIN PAIR** (`rankFloor_iff_thirdSuitFloor`):
   given the mechanism `d = c.twin`, the floor is *exactly* its third-suit part.
   So the whole content of the floor is "no third-suit live card below `d`".

5. **THE CONTAINMENT IS FREE WHEN THE RIGHT LEG RAISES ONCE**
   (`live_eq_pair_of_tail_raiseFree`, `SingleRaiseContainment`): if the right
   leg's tail contains no raise, the bottom's live set is *literally contained*
   in `{d, d.twin}` — the containment, hence the floor, is a theorem there.
   The whole difficulty is the multi-raise right leg.

6. **STRICTNESS, KERNEL-CHECKED** (`floor_not_containment`): a `WF` state with
   `CanRaise d`, `CanRaiseS c`, `¬ CanRaise c`, the floor at `d` — and a
   *third-suit* live card.  Hence the floor does **not** imply the containment,
   even with all the green data of a split bottom.

## What is NOT proved

`RankFloorAtSplit` itself.  §6 records the exact obstruction: a violation is a
`pull e … raise e` bracket of the minimal play (`e` is founded at `u` and not at
`F`, so the left leg pulled it; the right leg raises `e` or `e.twin` by (1)),
and deleting it needs the slide/raise, pull/slide commutation recorded as missing
in `Temp/Mechanism_Report.md` §4.  No exactness (containment) is needed anywhere
in this card.
-/

namespace FloorAttack

open ValleyElim
open Bubble

/-! ## §1. Every live card at the bottom is raised by the right leg -/

/-- **EVERY LIVE CARD IS KILLED BY A RAISE OF ITS OWN RANK.**  At `WF`, over a
pull-free witness leg ending at a *saturated* state, an S-live card either
survives (impossible) or is raised — and the raised card is `e` or `e.twin`,
both of rank `e.rank` (`Direct.canRaiseS_end_or_bad_raise`).  (The twin arm is
real: raising `e.twin` removes the cover that licences `e`.) -/
theorem exists_raise_of_rank
    {u v : State} {ρ : List Move} {F : State} {left right : List Move}
    {c d : Card} {b : Base} {pre post tail : List Move}
    (h : SplitKit.SplitHyp u v ρ F left right c d b pre post tail)
    (hms : MountainKit.MountainSplit left right)
    {e : Card} (he : CanRaiseS F e) :
    ∃ x : Card, Direct.Occurs (Move.tabToFound x) right ∧
      x.rank.toIdx = e.rank.toIdx := by
  obtain ⟨huwf, -, hsv, -, -, -, -, hleft, hright, -, -, -⟩ := h
  have hF : F.WF := SatDifferCensus.ShufflePlayW.wf_end hleft huwf
  rcases Direct.canRaiseS_end_or_bad_raise hright hF hms.2 he with h1 | h1 | h1
  · exact absurd h1 (hsv e)
  · exact ⟨e, h1, rfl⟩
  · exact ⟨e.twin, h1, by rw [Card.twin_rank]⟩

/-! ## §2. A violation forces either a rung rise or the twin's raise -/

/-- **THE THIRD-SUIT DICHOTOMY.**  For a third-suit live card `e`, the right leg
either raises `e` itself — in which case `e.suit`'s rung climbs strictly to the
far endpoint (the right leg is pull-free, so the ledger reads
`raisesOf right e.suit = rungAt v - rungAt F ≥ 1`) — or it kills `e` through the
twin's raise, `Occurs (tabToFound e.twin) right`. -/
theorem rise_or_twin_raise
    {u v : State} {ρ : List Move} {F : State} {left right : List Move}
    {c d : Card} {b : Base} {pre post tail : List Move}
    (h : SplitKit.SplitHyp u v ρ F left right c d b pre post tail)
    (hms : MountainKit.MountainSplit left right)
    {e : Card} (he : CanRaiseS F e) :
    rungAt F e.suit < rungAt v e.suit ∨
      Direct.Occurs (Move.tabToFound e.twin) right := by
  obtain ⟨huwf, -, hsv, -, -, -, -, hleft, hright, -, -, -⟩ := h
  have hF : F.WF := SatDifferCensus.ShufflePlayW.wf_end hleft huwf
  rcases Direct.canRaiseS_end_or_bad_raise hright hF hms.2 he with h1 | h1 | h1
  · exact absurd h1 (hsv e)
  · left
    have hled : raisesOf right e.suit = rungAt v e.suit - rungAt F e.suit :=
      MountainKit.raisesOf_eq_sub_of_no_pull (σ := e.suit) hright hms.2
    have hpos : 0 < raisesOf right e.suit := by
      refine LedgerKit.raisesOf_pos_iff.mpr ⟨e, rfl, ?_⟩
      obtain ⟨s1, s2, hs⟩ := h1
      rw [hs]; exact List.mem_append_right _ (List.mem_cons_self ..)
    omega
  · exact Or.inr h1

/-! ## §3. The floor as a raise-exclusion -/

/-- **`RightRaisesHigh`** — THE INEQUALITY RESIDUAL: at every split of a minimal
play, every card raised by the right leg has rank at least the raise card's.
This mentions no live set and no licence. -/
def RightRaisesHigh : Prop :=
  ∀ (u v : State) (ρ : List Move) (F : State)
    (left right : List Move) (c d : Card) (b : Base)
    (pre post tail : List Move),
    SplitKit.SplitHyp u v ρ F left right c d b pre post tail →
    MountainKit.MountainSplit left right →
      ∀ x : Card, Direct.Occurs (Move.tabToFound x) right →
        d.rank.toIdx ≤ x.rank.toIdx

/-- **`RightRaisesHigh` GIVES THE FLOOR** — via §1 (`exists_raise_of_rank`).
No containment is used. -/
theorem rankFloor_of_rightRaisesHigh (h : RightRaisesHigh)
    (hms : Direct.MountainAtSplits) : FloorRank.RankFloorAtSplit := by
  intro u v ρ F left right c d b pre post tail hh e he
  obtain ⟨x, hocc, hrank⟩ :=
    exists_raise_of_rank hh (hms u v ρ F left right c d b pre post tail hh) he
  have h1 := h u v ρ F left right c d b pre post tail hh
    (hms u v ρ F left right c d b pre post tail hh) x hocc
  omega

/-- The unfolded `RankFloorAtSplit` (the same statement, so §6 can speak of a
"violation" without leaving the file). -/
theorem rankFloor_apply
    (h : FloorRank.RankFloorAtSplit)
    {u v : State} {ρ : List Move} {F : State} {left right : List Move}
    {c d : Card} {b : Base} {pre post tail : List Move}
    (hh : SplitKit.SplitHyp u v ρ F left right c d b pre post tail)
    {e : Card} (he : CanRaiseS F e) :
    d.rank.toIdx ≤ e.rank.toIdx :=
  h u v ρ F left right c d b pre post tail hh e he

/-! ## §4. The floor is automatic on the twin pair -/

/-- **`ThirdSuitFloor`** — the floor restricted to suits that are *not* the
pair's.  This is the exact residual of §3's decomposition: on the two pair suits
the rank is pinned by the rung, so the floor there is a tautology. -/
def ThirdSuitFloor : Prop :=
  ∀ (u v : State) (ρ : List Move) (F : State)
    (left right : List Move) (c d : Card) (b : Base)
    (pre post tail : List Move),
    SplitKit.SplitHyp u v ρ F left right c d b pre post tail →
      ∀ e, CanRaiseS F e → e.suit ≠ c.suit → e.suit ≠ c.twin.suit →
        d.rank.toIdx ≤ e.rank.toIdx

theorem thirdSuitFloor_of_rankFloor (h : FloorRank.RankFloorAtSplit) :
    ThirdSuitFloor := by
  intro u v ρ F left right c d b pre post tail hh e he _ _
  exact h u v ρ F left right c d b pre post tail hh e he

/-- **THE DECOMPOSITION.**  Given the mechanism `d = c.twin`, the floor is
*exactly* its third-suit part: every live card on `c.suit` or on `c.twin.suit`
has rank `d.rank`, by the rung pins. -/
theorem rankFloor_of_thirdSuitFloor (h : ThirdSuitFloor)
    (ht : SplitKit.SplitTwin) : FloorRank.RankFloorAtSplit := by
  intro u v ρ F left right c d b pre post tail hh e he
  obtain ⟨hF, hSc, hcanD, -⟩ := SplitKit.splitHyp_green hh
  have hd : d = c.twin := ht u v ρ F left right c d b pre post tail hh
  have hrankD : d.rank.toIdx = rungAt F d.suit :=
    (TwinKit.nextUp_true_iff.mp hcanD.1).symm
  have hrankE : e.rank.toIdx = rungAt F e.suit :=
    ThirdLive.rank_eq_rungAt_of_canRaiseS hF he
  by_cases h1 : e.suit = c.suit
  · have hc : c.rank.toIdx = rungAt F c.suit :=
      ThirdLive.rank_eq_rungAt_of_canRaiseS hF hSc
    have hdr : d.rank.toIdx = c.rank.toIdx := by rw [hd, Card.twin_rank]
    rw [hrankE, h1, ← hc, ← hdr]
    exact Nat.le_refl _
  · by_cases h2 : e.suit = c.twin.suit
    · rw [hrankE, h2, ← hd, ← hrankD]
      exact Nat.le_refl _
    · exact h u v ρ F left right c d b pre post tail hh e he h1 h2

/-- **THE EXACT FORM OF THE RESIDUAL.**  Under the mechanism, the floor at the
raise card is the third-suit-only inequality `ThirdSuitFloor`. -/
theorem rankFloor_iff_thirdSuitFloor (ht : SplitKit.SplitTwin) :
    FloorRank.RankFloorAtSplit ↔ ThirdSuitFloor :=
  ⟨thirdSuitFloor_of_rankFloor, fun h => rankFloor_of_thirdSuitFloor h ht⟩

/-- **END TO END FROM THE THIRD-SUIT FLOOR** (§4 + the chain of
`Temp/Floor_RankChain.lean`). -/
theorem satDifferForkWF_of_thirdSuitFloor
    (hb : SplitKit.SplitBlock) (ht : SplitKit.SplitTwin)
    (hts : ThirdSuitFloor) (hmin : ValleyElim.ShortestPlayExists) : SatDifferForkWF :=
  FloorRank.satDifferForkWF_of_rankFloor hb ht
    (rankFloor_of_thirdSuitFloor hts ht) hmin

/-- **END TO END FROM THE RAISE-EXCLUSION** (§3 + the chain): `SplitBlock`,
the mechanism `SplitTwin`, the mountain shape and the *play-level* inequality
`RightRaisesHigh` give `SatDifferForkWF`. -/
theorem satDifferForkWF_of_rightRaisesHigh
    (hb : SplitKit.SplitBlock) (ht : SplitKit.SplitTwin)
    (hms : Direct.MountainAtSplits) (hrh : RightRaisesHigh)
    (hmin : ValleyElim.ShortestPlayExists) : SatDifferForkWF :=
  FloorRank.satDifferForkWF_of_rankFloor hb ht
    (rankFloor_of_rightRaisesHigh hrh hms) hmin

/-! ## §5. The containment is free when the right leg raises once -/

/-- **`SingleRaiseContainment`** — the bottom's live set is contained in
`{d, d.twin}`, *given* that the right leg's tail carries no raise. -/
def SingleRaiseContainment : Prop :=
  ∀ (u v : State) (ρ : List Move) (F : State)
    (left right : List Move) (c d : Card) (b : Base)
    (pre post tail : List Move),
    SplitKit.SplitHyp u v ρ F left right c d b pre post tail →
    MountainKit.MountainSplit left right →
      (∀ m ∈ tail, ¬ IsRaise m) →
        ∀ e, CanRaiseS F e → e = d ∨ e = d.twin

/-- **THE ONE-RAISE CASE IS A THEOREM.**  Raising `d` can only kill `d` and
`d.twin` (`Direct.canRaiseS_survives_raise_of_ne`); every other live card then
survives the raise-free, pull-free tail to `v`
(`Direct.canRaiseS_survives_free_leg`), contradicting `SSaturated v`. -/
theorem live_eq_pair_of_tail_raiseFree
    {u v : State} {ρ : List Move} {F : State} {left right : List Move}
    {c d : Card} {b : Base} {pre post tail : List Move}
    (h : SplitKit.SplitHyp u v ρ F left right c d b pre post tail)
    (hms : MountainKit.MountainSplit left right)
    (htail : ∀ m ∈ tail, ¬ IsRaise m) :
    ∀ e : Card, CanRaiseS F e → e = d ∨ e = d.twin := by
  obtain ⟨huwf, -, hsv, -, -, -, -, hleft, hright, -, -, hrightShape⟩ := h
  have hF : F.WF := SatDifferCensus.ShufflePlayW.wf_end hleft huwf
  rw [hrightShape] at hright
  obtain ⟨G, hstepD, hplayG⟩ :
      ∃ G : State, State.step F (Move.tabToFound d) = some G ∧
        ShufflePlayW G tail v := by
    cases hright with
    | cons _ hs hrest => exact ⟨_, hs, hrest⟩
  intro e he
  by_cases h1 : e = d
  · exact Or.inl h1
  · by_cases h2 : e = d.twin
    · exact Or.inr h2
    · exfalso
      have hGwf : G.WF := step_wf hF hstepD
      have hct : d ≠ e.twin := fun hh => h2 (by rw [hh, card_twin_twin])
      have hS' : CanRaiseS G e :=
        Direct.canRaiseS_survives_raise_of_ne hF hstepD
          (fun hh => h1 hh.symm) hct he
      have hnp : ∀ m ∈ tail, ¬ IsPull m := by
        intro m hm hp
        exact hms.2 m (by rw [hrightShape]; exact List.mem_cons_of_mem _ hm) hp
      exact hsv e (Direct.canRaiseS_survives_free_leg hplayG hGwf hnp htail hS')

theorem singleRaiseContainment_proved : SingleRaiseContainment := by
  intro u v ρ F left right c d b pre post tail h hms htail
  exact live_eq_pair_of_tail_raiseFree h hms htail

/-- **THE CONTAINMENT IN SUIT FORM**, when the right leg raises once and the
mechanism holds.  So `TwinKit.SplitContainment` — and hence the floor — costs
nothing on single-raise splits; only multi-raise right legs are open. -/
theorem splitContainment_of_singleRaise
    (ht : SplitKit.SplitTwin) (hs : SingleRaiseContainment) :
    ∀ (u v : State) (ρ : List Move) (F : State)
      (left right : List Move) (c d : Card) (b : Base)
      (pre post tail : List Move),
      SplitKit.SplitHyp u v ρ F left right c d b pre post tail →
      MountainKit.MountainSplit left right →
      (∀ m ∈ tail, ¬ IsRaise m) →
        ∀ e, CanRaiseS F e → e.suit = c.suit ∨ e.suit = c.twin.suit := by
  intro u v ρ F left right c d b pre post tail hh hms htail e he
  have hd : d = c.twin := ht u v ρ F left right c d b pre post tail hh
  rcases hs u v ρ F left right c d b pre post tail hh hms htail e he with h' | h'
  · right
    rw [h', hd]
  · left
    rw [h', hd, card_twin_twin]

/-! ## §6. The floor does not imply the containment (kernel-checked) -/

namespace Gadget

def H2 : Card := ⟨.heart, .two⟩
def H3 : Card := ⟨.heart, .three⟩
def H4 : Card := ⟨.heart, .four⟩
def H5 : Card := ⟨.heart, .five⟩
def D2 : Card := ⟨.diamond, .two⟩
def D3 : Card := ⟨.diamond, .three⟩
def D4 : Card := ⟨.diamond, .four⟩
def D5 : Card := ⟨.diamond, .five⟩
def D6 : Card := ⟨.diamond, .six⟩
def S2 : Card := ⟨.spade, .two⟩
def S3 : Card := ⟨.spade, .three⟩
def S4 : Card := ⟨.spade, .four⟩
def S5 : Card := ⟨.spade, .five⟩
def S6 : Card := ⟨.spade, .six⟩
def AC : Card := ⟨.club, .ace⟩
def C4 : Card := ⟨.club, .four⟩
def C6 : Card := ⟨.club, .six⟩

/-- Hearts `A..4`, diamonds `A..4`, spades `A..4`, clubs `A`: every pair suit
sits on rung `4`, the club suit on rung `1`. -/
def fixed : List Card :=
  [⟨.heart, .ace⟩, H2, H3, H4, H5,
   ⟨.diamond, .ace⟩, D2, D3, D4, D5, D6,
   ⟨.spade, .ace⟩, S2, S3, S4, S5, S6,
   AC, C4, C6]

/-- The 32-card stock (the complement of `fixed`). -/
def rest : List Card := Card.universe.filter (fun c => !(decide (c ∈ fixed)))

/-- **`g`** — the separation board:
`p0 = [6C, 5H]` (`d = 5H` raisable), `p1 = [6S, 5D, 4C]` (`c = 5D` live and
blocked, with company below *and* a cover above), `p2 = [6D, 5S]` (a
**third-suit** live card `5S`), everything else in the stock. -/
def g : State :=
  { found := fun s => match s with
      | .heart => [⟨.heart, .ace⟩, H2, H3, H4]
      | .diamond => [⟨.diamond, .ace⟩, D2, D3, D4]
      | .spade => [⟨.spade, .ace⟩, S2, S3, S4]
      | .club => [AC]
    piles := fun a => match a with
      | .p0 => ⟨[], [C6, H5]⟩
      | .p1 => ⟨[], [S6, D5, C4]⟩
      | .p2 => ⟨[], [D6, S5]⟩
      | _ => ⟨[], []⟩
    stock := rest
    waste := []
    drawStep := 1 }

theorem g_wf : g.WF := by
  refine ⟨?_, ?_, ?_, by decide⟩
  · intro s
    cases s
    · exact ⟨4, rfl⟩
    · exact ⟨4, rfl⟩
    · exact ⟨4, rfl⟩
    · exact ⟨1, rfl⟩
  · intro a; cases a <;> decide
  · intro c _
    rcases c with ⟨s, r⟩
    cases s <;> cases r <;> decide

/-- The raise card `d = 5H` is vanilla-raisable. -/
theorem g_canRaise_H5 : CanRaise g H5 :=
  ⟨by decide, .p0, by decide, Or.inl (by decide)⟩

theorem g_live_H5 : CanRaiseS g H5 := CanRaiseS.now H5 g_canRaise_H5

/-- The pull card `c = 5D` is S-live (it is covered, and `5D.twin = 5H` tops
`p0`). -/
theorem g_live_D5 : CanRaiseS g D5 := by
  refine (LandKit.canRaiseS_below_form g_wf).mpr
    ⟨by decide, .p1, by decide, Or.inl (by decide), Or.inr (by decide)⟩

/-- ... but it is **vanilla-blocked** (it is not a pile top). -/
theorem g_not_canRaise_D5 : ¬ CanRaise g D5 := by
  rintro ⟨-, a, hpa, -⟩
  have hnone : g.pileOfTop D5 = none := by decide
  rw [hnone] at hpa
  exact absurd hpa (by simp)

/-- **THE THIRD-SUIT LIVE CARD** `5S` (spades are neither `c`'s nor `c.twin`'s
suit). -/
theorem g_live_S5 : CanRaiseS g S5 := by
  refine (LandKit.canRaiseS_below_form g_wf).mpr
    ⟨by decide, .p2, by decide, Or.inl (by decide), Or.inl (by decide)⟩

/-- **THE FLOOR HOLDS**: every S-live card of `g` has rank index at least `4`
(=`5H`'s).  The club frontier `2C` is in the stock, so it is not live; every
other suit's frontier is its `5`. -/
theorem g_floor : ∀ e : Card, CanRaiseS g e → H5.rank.toIdx ≤ e.rank.toIdx := by
  intro e he
  have hnext : g.nextUp e = true := ((LandKit.canRaiseS_below_form g_wf).mp he).1
  rcases e with ⟨s, r⟩
  cases s <;> cases r <;>
    first
      | (exact absurd hnext (by decide))
      | (decide)
      | (exfalso
         exact absurd ((canRaiseSB_iff g_wf).mpr he) (by decide))

end Gadget

/-- **THE FLOOR DOES NOT IMPLY THE CONTAINMENT.**  Even with every local datum a
split bottom's floor lane has — `WF`, `CanRaise d`, `CanRaiseS c`, `¬ CanRaise c`,
and the floor at `d` — the live set need not be confined to the pair's suits.
So `RankFloorAtSplit` is *strictly* weaker than the containment as a local
condition. -/
theorem floor_not_containment :
    ¬ (∀ (F : State) (c d : Card), F.WF → CanRaise F d → CanRaiseS F c →
        ¬ CanRaise F c →
        (∀ e : Card, CanRaiseS F e → d.rank.toIdx ≤ e.rank.toIdx) →
        ∀ e : Card, CanRaiseS F e → e.suit = c.suit ∨ e.suit = c.twin.suit) := by
  intro h
  have hcont := h Gadget.g Gadget.D5 Gadget.H5 Gadget.g_wf
    Gadget.g_canRaise_H5 Gadget.g_live_D5 Gadget.g_not_canRaise_D5 Gadget.g_floor
    Gadget.S5 Gadget.g_live_S5
  rcases hcont with h' | h' <;> revert h' <;> decide

/-! ## §7. Axiom battery -/

#print axioms FloorAttack.exists_raise_of_rank
#print axioms FloorAttack.rise_or_twin_raise
#print axioms FloorAttack.rankFloor_of_rightRaisesHigh
#print axioms FloorAttack.thirdSuitFloor_of_rankFloor
#print axioms FloorAttack.rankFloor_of_thirdSuitFloor
#print axioms FloorAttack.rankFloor_iff_thirdSuitFloor
#print axioms FloorAttack.satDifferForkWF_of_thirdSuitFloor
#print axioms FloorAttack.satDifferForkWF_of_rightRaisesHigh
#print axioms FloorAttack.live_eq_pair_of_tail_raiseFree
#print axioms FloorAttack.singleRaiseContainment_proved
#print axioms FloorAttack.splitContainment_of_singleRaise
#print axioms FloorAttack.Gadget.g_wf
#print axioms FloorAttack.Gadget.g_canRaise_H5
#print axioms FloorAttack.Gadget.g_live_D5
#print axioms FloorAttack.Gadget.g_not_canRaise_D5
#print axioms FloorAttack.Gadget.g_live_S5
#print axioms FloorAttack.Gadget.g_floor
#print axioms FloorAttack.floor_not_containment

#check @FloorAttack.RightRaisesHigh
#check @FloorAttack.ThirdSuitFloor
#check @FloorAttack.SingleRaiseContainment
#check @FloorAttack.rankFloor_of_rightRaisesHigh

end FloorAttack

