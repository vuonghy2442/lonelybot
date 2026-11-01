import Orig2

/-!
# Orig2/ForkDisj - the disjunctive clause forms and their composition

Scratch card (read-only on `Orig2/`; nothing committed).  Zero `sorry`,
zero `Classical.choice`, zero `native_decide`; axiom battery at the tail.

## The idea

The campaign target `SatDifferForkWF` concludes `∃ F x, sameOrbitSetoid.r u F ∧
ForkWitness F x`.  Hence a split clause does not have to be proved outright:
`clause ∨ fork-in-the-class` is enough.  This card states the three
disjunctive clauses, proves the easy direction (`clause → clause ∨ fork`),
and proves the COMPOSITION: the three disjunctive forms plus the shortest-play
interface give `SatDifferForkWF`.  The composition is via the pointwise
assembly `forkInClass_of_clauses` (block + containment + pin at ONE split
give the drain asymmetry at the bottom, and the drain is
`DrainClose.fork_exists_of_asymmetry`).

The branch analysis of the violation side lives in `Temp/Disj_Branches.lean`.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Disj

/-- **`ForkInClass u`** - the conclusion of `SatDifferForkWF`, at the class of
`u`: some same-orbit state carries a fork. -/
def ForkInClass (u : State) : Prop :=
  ∃ F x, sameOrbitSetoid.r u F ∧ ForkWitness F x

/-- A `forkState` class-mate gives `ForkInClass`. -/
theorem forkInClass_of_forkState {u F : State}
    (hcls : sameOrbitSetoid.r u F) (h : forkState F) : ForkInClass u := by
  obtain ⟨x, hx⟩ := forkState_iff.mp h
  exact ⟨F, x, hcls, hx⟩

/-- The drain asymmetry at a class-mate gives `ForkInClass`.  This is the
consumer shape of `DrainClose.fork_exists_of_asymmetry`. -/
theorem forkInClass_of_drainInvariant {u F : State} {x : Card}
    (hcls : sameOrbitSetoid.r u F) (hF : F.WF)
    (hinv : Drain.DrainInvariant F x) : ForkInClass u := by
  obtain ⟨hcan, hlive, hblock, hfloor⟩ := hinv
  obtain ⟨G, hFG, hfork⟩ :=
    DrainClose.fork_exists_of_asymmetry hF hcan hlive hblock hfloor
  obtain ⟨y, hy⟩ := forkState_iff.mp hfork
  exact ⟨G, y, sameOrbitSetoid.iseqv.trans hcls hFG, hy⟩

/-! ## §1. The three disjunctive clause forms -/

/-- **`SplitBlockOrFork`** - at every split, either the pull card is blocked at
the bottom, or the class already contains a fork. -/
def SplitBlockOrFork : Prop :=
  ∀ (u v : State) (ρ : List Move) (F : State)
    (left right : List Move) (c d : Card) (b : Base)
    (pre post tail : List Move),
    SplitKit.SplitHyp u v ρ F left right c d b pre post tail →
      (¬ CanRaise F c) ∨ ForkInClass u

/-- **`SplitContainmentOrFork`** - at every split, either no third-suit card is
S-live at the bottom, or the class already contains a fork.  (This is the
bottom form of `Landing.LandingThirdSuitFree`; the landing form reduces to it
by the free-tail transport `Mech.canRaiseS_landing_iff`.) -/
def SplitContainmentOrFork : Prop :=
  ∀ (u v : State) (ρ : List Move) (F : State)
    (left right : List Move) (c d : Card) (b : Base)
    (pre post tail : List Move),
    SplitKit.SplitHyp u v ρ F left right c d b pre post tail →
      ((∀ e, CanRaiseS F e → e.suit = c.suit ∨ e.suit = c.twin.suit) ∨
        ForkInClass u)

/-- **`SplitPinOrFork`** - at every split, either the twin suit's rung is at the
pull card's rank (`nextUp c.twin`), or the class already contains a fork. -/
def SplitPinOrFork : Prop :=
  ∀ (u v : State) (ρ : List Move) (F : State)
    (left right : List Move) (c d : Card) (b : Base)
    (pre post tail : List Move),
    SplitKit.SplitHyp u v ρ F left right c d b pre post tail →
      (F.nextUp c.twin = true ∨ ForkInClass u)

/-- **`LandingThirdSuitFreeOrFork`** - the brief's landing-side spelling of the
containment disjunct: at every split, either no third-suit card is S-live at
the PULL LANDING `B`, or the class already contains a fork. -/
def LandingThirdSuitFreeOrFork : Prop :=
  ∀ (u v : State) (ρ : List Move) (F : State)
    (left right : List Move) (c d : Card) (b : Base)
    (pre post tail : List Move),
    SplitKit.SplitHyp u v ρ F left right c d b pre post tail →
      ((∀ (A' B : State), ShufflePlayW u pre A' →
          State.step A' (Move.foundToTab c b) = some B →
          ∀ e : Card, CanRaiseS B e → e.suit ≠ c.suit →
            e.suit ≠ c.twin.suit → False)
        ∨ ForkInClass u)

/-! ## §2. The easy direction: a clause implies its disjunctive form -/

theorem splitBlockOrFork_of_splitBlock (h : SplitKit.SplitBlock) :
    SplitBlockOrFork :=
  fun u v ρ F left right c d b pre post tail hh =>
    Or.inl (h u v ρ F left right c d b pre post tail hh)

theorem splitContainmentOrFork_of_splitContainment
    (h : TwinKit.SplitContainment) : SplitContainmentOrFork :=
  fun u v ρ F left right c d b pre post tail hh =>
    Or.inl (h u v ρ F left right c d b pre post tail hh)

theorem splitPinOrFork_of_splitPin (h : TwinKit.SplitTwinRungPin) :
    SplitPinOrFork :=
  fun u v ρ F left right c d b pre post tail hh =>
    Or.inl (h u v ρ F left right c d b pre post tail hh)

theorem landingThirdSuitFreeOrFork_of_landingThirdSuitFree
    (h : Landing.LandingThirdSuitFree) : LandingThirdSuitFreeOrFork :=
  fun u v ρ F left right c d b pre post tail hh =>
    Or.inl (h u v ρ F left right c d b pre post tail hh)

/-- The landing-side disjunct gives the bottom-side one, by transporting the
landing's live set down the free tail (`Mech.canRaiseS_landing_iff`). -/
theorem splitContainmentOrFork_of_landingThirdSuitFreeOrFork
    (h : LandingThirdSuitFreeOrFork) : SplitContainmentOrFork := by
  intro u v ρ F left right c d b pre post tail hs
  rcases h u v ρ F left right c d b pre post tail hs with hthird | hfork
  · left
    obtain ⟨huwf, -, -, -, -, -, -, hleft, -, hshape, hfreePost, -⟩ := hs
    obtain ⟨A', hpre, hrest⟩ :=
      ValleyElim.ShufflePlayW_split hleft pre
        (Move.foundToTab c b :: post) hshape
    cases hrest with
    | @cons _ B _ _ _ hrev hstep hpost =>
      intro e he
      have hA' : A'.WF := SatDifferCensus.ShufflePlayW.wf_end hpre huwf
      have hB : B.WF := step_wf hA' hstep
      have heB : CanRaiseS B e :=
        (Mech.canRaiseS_landing_iff hB hpost hfreePost e).mpr he
      by_cases h1 : e.suit = c.suit
      · exact Or.inl h1
      · by_cases h2 : e.suit = c.twin.suit
        · exact Or.inr h2
        · exact (hthird A' B hpre hstep e heB h1 h2).elim
  · exact Or.inr hfork

/-- Conversely, the bottom-side containment disjunct gives the landing-side
one: the free tail is an iff-transport of the S-live set. -/
theorem landingThirdSuitFreeOrFork_of_splitContainmentOrFork
    (h : SplitContainmentOrFork) : LandingThirdSuitFreeOrFork := by
  intro u v ρ F left right c d b pre post tail hs
  rcases h u v ρ F left right c d b pre post tail hs with hcont | hfork
  · left
    have hsk := hs
    obtain ⟨-, -, -, -, -, -, -, -, -, -, hfreePost, -⟩ := hs
    intro A' B hpre hstep e heB h1 h2
    obtain ⟨hpost, hB⟩ := Landing.post_play_of_landing hsk hpre hstep
    have heF : CanRaiseS F e :=
      (Mech.canRaiseS_landing_iff hB hpost hfreePost e).mp heB
    rcases hcont e heF with hsuit | hsuit
    · exact h1 hsuit
    · exact h2 hsuit
  · exact Or.inr hfork

theorem splitContainmentOrFork_iff_landingThirdSuitFreeOrFork :
    SplitContainmentOrFork ↔ LandingThirdSuitFreeOrFork :=
  ⟨landingThirdSuitFreeOrFork_of_splitContainmentOrFork,
    splitContainmentOrFork_of_landingThirdSuitFreeOrFork⟩

/-! ## §3. The pointwise assembly: three clause instances at one split -/

/-- **THREE CLAUSES AT ONE SPLIT ⇒ FORK IN THE CLASS.**  At the bottom of a
split, the block plus the containment plus the pin give the twin equation
`d = c.twin`, the live pair `{c, c.twin}`, the rank floor and hence
`Drain.DrainInvariant F d`; `DrainClose.fork_exists_of_asymmetry` then produces
a fork at a same-orbit state, and the left leg puts it in `u`'s class.

No minimality is used: only the three clause instances and the split's left
leg (for the class relation). -/
theorem forkInClass_of_clauses {u v : State} {ρ : List Move} {F : State}
    {left right : List Move} {c d : Card} {b : Base}
    {pre post tail : List Move}
    (h : SplitKit.SplitHyp u v ρ F left right c d b pre post tail)
    (hblock : ¬ CanRaise F c)
    (hcont : ∀ e, CanRaiseS F e → e.suit = c.suit ∨ e.suit = c.twin.suit)
    (hpin : F.nextUp c.twin = true) :
    ForkInClass u := by
  have hk := h
  obtain ⟨hF, hSc, hcanD, -⟩ := SplitKit.splitHyp_green hk
  obtain ⟨-, -, -, -, -, -, -, hleft, -, -, -, -⟩ := hk
  have hpinR : rungAt F c.twin.suit = c.rank.toIdx :=
    TwinKit.nextUp_true_iff.mp hpin
  have htwin : d = c.twin :=
    TwinKit.raise_eq_twin_of_block_containment hSc hblock hcont hpinR hcanD
  have hliveT : CanRaiseS F c.twin :=
    TwinKit.canRaiseS_twin_of_block_containment hSc hblock hcont hpin hcanD
  have hl : TwinLivePair F d := by
    rw [htwin]
    intro e
    rw [card_twin_twin]
    constructor
    · intro he
      rcases hcont e he with hs | hs
      · exact Or.inr (Mech.live_eq_of_suit_left (canRaiseS_rung hSc) he hs)
      · exact Or.inl (Mech.live_eq_of_suit_twin hpinR he hs)
    · rintro (h' | h')
      · rw [h']; exact hliveT
      · rw [h']; exact hSc
  have hfloor : ∀ e, CanRaiseS F e → c.rank.toIdx ≤ e.rank.toIdx :=
    Mech.floor_of_livePair_twin hl htwin
  have hinv : Drain.DrainInvariant F d :=
    SplitKit.splitData_drainInvariant h htwin hblock hfloor
  exact forkInClass_of_drainInvariant
    (RevEqW_symm (shufflePlayW_revEqW hleft)) hF hinv

/-! ## §4. The composition theorem -/

/-- **THE DISJUNCTIVE COMPOSITION.**  The three disjunctive clause forms plus
the choice-free shortest-play interface give `SatDifferForkWF`.

Proof: take the shortest witness play and its valley split.  Apply the three
disjuncts at that split.  A fork disjunct is the goal; otherwise all three
clause instances hold and `forkInClass_of_clauses` finishes. -/
theorem satDifferForkWF_of_disjunctive
    (hb : SplitBlockOrFork) (hc : SplitContainmentOrFork) (hp : SplitPinOrFork)
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
  rcases hb u v ρ F left right c d b pre post tail hh with hblock | hfork
  · rcases hc u v ρ F left right c d b pre post tail hh with hcont | hfork
    · rcases hp u v ρ F left right c d b pre post tail hh with hpin | hfork
      · exact forkInClass_of_clauses hh hblock hcont hpin
      · exact hfork
    · exact hfork
  · exact hfork

/-! ## §5. Sanity: the old clause route is a special case -/

/-- The existing three-clause route is the `Or.inl` instance. -/
theorem satDifferForkWF_of_clauses
    (hb : SplitKit.SplitBlock) (hc : TwinKit.SplitContainment)
    (hp : TwinKit.SplitTwinRungPin)
    (hmin : ValleyElim.ShortestPlayExists) : SatDifferForkWF :=
  satDifferForkWF_of_disjunctive
    (splitBlockOrFork_of_splitBlock hb)
    (splitContainmentOrFork_of_splitContainment hc)
    (splitPinOrFork_of_splitPin hp) hmin

/-- The landing-side containment disjunct composes just as well. -/
theorem satDifferForkWF_of_landingDisjunctive
    (hb : SplitBlockOrFork) (hc : LandingThirdSuitFreeOrFork)
    (hp : SplitPinOrFork)
    (hmin : ValleyElim.ShortestPlayExists) : SatDifferForkWF :=
  satDifferForkWF_of_disjunctive hb
    (splitContainmentOrFork_of_landingThirdSuitFreeOrFork hc) hp hmin

/-! ## §6. A forkless class reads the disjunctive forms as the clauses -/

/-- In a class with no fork, the block disjunct is the block clause. -/
theorem splitBlock_of_orFork (h : SplitBlockOrFork)
    (hnf : ∀ u : State, ¬ ForkInClass u) : SplitKit.SplitBlock :=
  fun u v ρ F left right c d b pre post tail hh =>
    (h u v ρ F left right c d b pre post tail hh).resolve_right (hnf u)

/-- In a class with no fork, the containment disjunct is the containment
clause. -/
theorem splitContainment_of_orFork (h : SplitContainmentOrFork)
    (hnf : ∀ u : State, ¬ ForkInClass u) : TwinKit.SplitContainment :=
  fun u v ρ F left right c d b pre post tail hh =>
    (h u v ρ F left right c d b pre post tail hh).resolve_right (hnf u)

/-- In a class with no fork, the pin disjunct is the pin clause. -/
theorem splitPin_of_orFork (h : SplitPinOrFork)
    (hnf : ∀ u : State, ¬ ForkInClass u) : TwinKit.SplitTwinRungPin :=
  fun u v ρ F left right c d b pre post tail hh =>
    (h u v ρ F left right c d b pre post tail hh).resolve_right (hnf u)

end Disj

/-! ## Battery -/

#print axioms Disj.forkInClass_of_forkState
#print axioms Disj.forkInClass_of_drainInvariant
#print axioms Disj.splitBlockOrFork_of_splitBlock
#print axioms Disj.splitContainmentOrFork_of_splitContainment
#print axioms Disj.splitPinOrFork_of_splitPin
#print axioms Disj.landingThirdSuitFreeOrFork_of_landingThirdSuitFree
#print axioms Disj.splitContainmentOrFork_of_landingThirdSuitFreeOrFork
#print axioms Disj.landingThirdSuitFreeOrFork_of_splitContainmentOrFork
#print axioms Disj.splitContainmentOrFork_iff_landingThirdSuitFreeOrFork
#print axioms Disj.forkInClass_of_clauses
#print axioms Disj.satDifferForkWF_of_disjunctive
#print axioms Disj.satDifferForkWF_of_clauses
#print axioms Disj.satDifferForkWF_of_landingDisjunctive
#print axioms Disj.splitBlock_of_orFork
#print axioms Disj.splitContainment_of_orFork
#print axioms Disj.splitPin_of_orFork
