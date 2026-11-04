import Orig2.Fork.Split.ForkLandingLocal
import Orig2.Fork.Split.ForkLedger
import Orig2.Fork.Split.ForkMountain

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

/-!
# Orig2/ForkTwinLive — the FIRST conjunct of `Mech.LandingLivePair`

READ-ONLY scratch card: no source edit, no commit.  Zero `sorry`, zero
`Classical.choice`, zero `native_decide`; axiom battery at the tail.

Target: `CanRaiseS B c.twin` at the pull's landing `B` of a valley split
(`left = pre ++ foundToTab c b :: post`, `post` free,
`ShufflePlayW B post F`, `CanRaiseS F c` from `Bridge.bottom_pull_live`).

## 1. The exact reduction (§1–§3)

`LandKit.canRaiseS_below_form` writes `CanRaiseS st x` as

    nextUp x  ∧  x face-up in a pile with company (or a bare king)
              ∧  (x is its pile's top  ∨  x.twin tops some pile)

For `x = c.twin` the **third** clause is free at the landing: the pull puts
`c` on top of the target pile (`LandKit.pull_card_pile_top_at_landing`) and
`c.twin.twin = c`.  Hence, at any `WF` state where `c` tops a pile,

    `CanRaiseS st c.twin`  ↔  `LandingTwinDatum st c`                     (`canRaiseS_twin_iff`)

    `LandingTwinDatum st c` := `st.nextUp c.twin = true` ∧ `TwinSited st c`

    `TwinSited st c`        := ∃ a, c.twin ∈ (st.piles a).faceUp ∧
                                 (below c.twin (st.piles a).faceUp ≠ [] ∨
                                   ((st.piles a).hidden = [] ∧ c.twin.rank = Rank.king))

`TwinSited` is a *static siting* datum (where does `c.twin` physically sit),
with no rung, no licence and no cargo content.  Both halves are necessary
(`sited_of_canRaiseS`, `not_canRaiseS_of_not_nextUp`), so the reduction is
exact: `landingLivePair_iff_datum_and_third`.

## 2. The structural identity (§4)

Given `CanRaiseS F c`, the campaign's landing pair is *exactly* "the live set
is the twin pair":

    `Mech.LandingLivePair F c`  ↔  `PairExactLive F c`        (`landingLivePair_iff_pairExact`)
    `ForkWitness F c.twin`      ↔  `PairExactLive F c` ∧ `¬ CanRaise F c`

(`forkWitness_twin_iff_pairExact`).  Consequences:

* `LandingLivePair F c → F.nextUp c.twin = true`: the `nextUp` half of §1 is
  *implied* by the goal (via `canRaiseS_rung`), i.e. the reduction is
  lossless — it loses nothing but the free cover clause.
* The repo's only source of a *twin-suit* rung pin is
  `forkState_witness_rungs`, which consumes the **full** `ForkWitness`,
  i.e. exactly `PairExactLive` — **the containment clause**.  So the `nextUp`
  half is *not* derivable from `¬ CanRaise F c` + `CanRaiseS F c` alone.
  (Attempting it is the circularity `forkWitness_twin_of_block` would need:
  it wants `CanRaiseS F c.twin` itself to build the witness.)  This is the
  precise reason route "block ⟹ pin" does **not** close, recorded here as a
  negative result.

## 3. The two remaining routes (§5–§6)

* **Route A (containment-free).**  `SplitBlock` + the *pin* `F.nextUp c.twin`
  + `SplitLandingTwinSited` ⟹ `LandKit.SplitLandingTwin`
  (`splitLandingTwin_of_pin_of_sited`): the licence is manufactured by the
  pull, the pin is the rung equation, only the siting is consumed.

* **Route B (siting-free).**  `SplitBlock` + the containment clause + the
  same pin ⟹ `LandKit.SplitLandingTwin`
  (`splitLandingTwin_of_block_containment_of_pin`).  The pin makes the rung
  match, the containment clause forces the raise card `d` onto the twin suit,
  and `d`'s *vanilla* raisability then *supplies the siting for free*:
  `d = c.twin` and `CanRaise F c.twin`
  (`canRaise_twin_of_block_containment`).  So on Route B the residual is the
  **single rung equation** `F.nextUp c.twin` — a ledger/dip statement, not a
  licence statement.  This is the sharpest residual this card reaches:

      `SplitBlock` + `SplitContainment` + `SplitTwinRungPin`
        ⟹ `Mech.MechanismResidual` ⟹ `SatDifferForkWF`
      (`mechanismResidual_of_block_containment_of_pin`,
       `satDifferForkWF_of_block_containment_of_pin`)
-/

namespace TwinKit

open ValleyElim

/-! ## §0. `nextUp` is a rung equation -/

/-- **`nextUp` IS A RUNG EQUALITY.**  (`foundHeight` and `rungAt` are the
same term.) -/
theorem nextUp_true_iff {st : State} {c : Card} :
    st.nextUp c = true ↔ rungAt st c.suit = c.rank.toIdx := by
  show decide (c.rank.toIdx = (st.found c.suit).length) = true ↔
    (st.found c.suit).length = c.rank.toIdx
  rw [decide_eq_true_iff, eq_comm]

theorem nextUp_of_free_play_iff {B F : State} {post : List Move} {c : Card}
    (hplay : ShufflePlayW B post F) (hfree : ∀ m ∈ post, FreeMove m) :
    B.nextUp c = true ↔ F.nextUp c = true := by
  rw [nextUp_true_iff, nextUp_true_iff, rungAt_eq_of_free_play hplay hfree]

/-! ## §0b. Determinism: the free tail after a specified pull -/

/-- **THE TAIL AFTER THE PULL IS THE TAIL OF THE SPLIT.**  If the play
`pre ++ pull :: post` runs `u → F` and the given `pre` runs `u → A'`, then
stepping `A'` by the pull reaches exactly the state whose `post`-play lands
at `F`.  (`State.step` is a function, so the two endpoints agree.)

This is the missing glue that lets the split-level residual be stated at the
*arbitrary* landing `B` supplied by `SplitHyp` (`run` determinism). -/
theorem shufflePlayW_tail_of_step {u A' B F : State} {pre post : List Move}
    {c : Card} {b : Base}
    (hleft : ShufflePlayW u (pre ++ Move.foundToTab c b :: post) F)
    (hpre : ShufflePlayW u pre A')
    (hstep : State.step A' (Move.foundToTab c b) = some B) :
    ShufflePlayW B post F := by
  obtain ⟨A₂, hpre₂, hrest⟩ :=
    ValleyElim.ShufflePlayW_split hleft pre (Move.foundToTab c b :: post) rfl
  have hA : A₂ = A' :=
    Option.some.inj ((Walk_run _ hpre₂).symm.trans (Walk_run _ hpre))
  subst hA
  cases hrest with
  | @cons _ B₂ _ _ _ hrev hstep₂ hpost =>
      have hB : B₂ = B := Option.some.inj (hstep₂.symm.trans hstep)
      subst hB
      exact hpost

/-! ## §1. The static residual `TwinSited` -/

/-- **`TwinSited st c`** — `c.twin` is face up in some pile and has a card
physically under it (or is a bare king over an empty deck).  This is exactly
the *seat* half of the flat `CanRaiseS` form read at `c.twin`: no rungs, no
licence, no cargo. -/
def TwinSited (st : State) (c : Card) : Prop :=
  ∃ a : Anchor, c.twin ∈ (st.piles a).faceUp ∧
    (below c.twin (st.piles a).faceUp ≠ [] ∨
      ((st.piles a).hidden = [] ∧ c.twin.rank = Rank.king))

/-- **THE SEAT HALF IS NECESSARY.**  Every S-live `c.twin` is sited. -/
theorem sited_of_canRaiseS {st : State} {c : Card} (hwf : st.WF)
    (h : CanRaiseS st c.twin) : TwinSited st c := by
  obtain ⟨-, a, hmem, hseat, -⟩ := (LandKit.canRaiseS_below_form hwf).mp h
  exact ⟨a, hmem, hseat⟩

def LandingTwinDatum (st : State) (c : Card) : Prop :=
  st.nextUp c.twin = true ∧ TwinSited st c

/-- **THE EXACT CHARACTERIZATION.**  At a `WF` state where `c` tops a pile,
the S-licence of `c.twin` is *exactly* the datum: the flat cover clause
`fromCard c.twin = [c.twin] ∨ pileOfTop c.twin.twin ≠ none` is free because
`c.twin.twin = c` tops a pile. -/
theorem canRaiseS_twin_iff {st : State} {c : Card} (hwf : st.WF)
    (hctop : st.pileOfTop c ≠ none) :
    CanRaiseS st c.twin ↔ LandingTwinDatum st c := by
  constructor
  · intro h
    exact ⟨nextUp_true_iff.mpr (canRaiseS_rung h), sited_of_canRaiseS hwf h⟩
  · rintro ⟨hnext, a, hmem, hseat⟩
    have hcov : st.pileOfTop c.twin.twin ≠ none := by rwa [card_twin_twin]
    exact (LandKit.canRaiseS_below_form hwf).mpr
      ⟨hnext, a, hmem, hseat, Or.inr hcov⟩

/-- The sufficiency direction, spelled out (no `Iff` juggling needed). -/
theorem canRaiseS_twin_of_datum {st : State} {c : Card} (hwf : st.WF)
    (hctop : st.pileOfTop c ≠ none) (h : LandingTwinDatum st c) :
    CanRaiseS st c.twin :=
  (canRaiseS_twin_iff hwf hctop).mpr h

theorem canRaiseS_twin_at_landing {A B F : State} {post : List Move}
    {c : Card} {b : Base}
    (hB : B.WF) (hstep : State.step A (Move.foundToTab c b) = some B)
    (hplay : ShufflePlayW B post F) (hfree : ∀ m ∈ post, FreeMove m)
    (hS : CanRaiseS F c) (hblock : ¬ CanRaise F c) (h : LandingTwinDatum B c) :
    CanRaiseS B c.twin := by
  rw [LandingTwinDatum] at h
  obtain ⟨a, hmem, hseat⟩ := h.2
  refine LandKit.canRaiseS_twin_of_landing hB hstep h.1 hmem hseat

/-- A pull-shaped restatement: the datum at the landing is all that is left
once the pull is placed. -/
theorem canRaiseS_twin_at_landing_iff {A B : State} {c : Card} {b : Base}
    (hB : B.WF) (hstep : State.step A (Move.foundToTab c b) = some B) :
    CanRaiseS B c.twin ↔ LandingTwinDatum B c := by
  obtain ⟨k, htop⟩ := LandKit.pull_card_pile_top_at_landing hB hstep
  exact canRaiseS_twin_iff hB (by rw [htop]; simp)

/-! ## §4. The structural identity: the landing pair is the live pair -/

/-- **`PairExactLive st c`** — the live set of `st` is *exactly* the twin
pair `{c, c.twin}` (as cards, not merely as suits). -/
def PairExactLive (st : State) (c : Card) : Prop :=
  ∀ y : Card, (y = c.twin ∨ y = c) ↔ CanRaiseS st y

theorem forkWitness_twin_iff_pairExact {st : State} {c : Card} :
    ForkWitness st c.twin ↔ PairExactLive st c ∧ ¬ CanRaise st c := by
  unfold ForkWitness PairExactLive
  simp only [card_twin_twin]

/-- **THE LANDING PAIR IS THE LIVE PAIR.**  Given `CanRaiseS F c`, the
campaign's `LandingLivePair` is exactly "the live set is `{c, c.twin}`".

Forward: the third-suit clause sends any live card to a pair suit, and the
rung pins (`canRaiseS_rung` on `c`, then on `c.twin`, the latter being the
twin clause itself) make each pair suit's live card unique.  Backward: the
pair disjunction gives the twin clause and the suit containment. -/
theorem landingLivePair_iff_pairExact {F : State} {c : Card}
    (hS : CanRaiseS F c) :
    Mech.LandingLivePair F c ↔ PairExactLive F c := by
  constructor
  · rintro ⟨htwin, hcont⟩
    intro y
    constructor
    · rintro (h | h)
      · rw [h]; exact htwin
      · rw [h]; exact hS
    · intro hy
      rcases hcont y hy with hs | hs
      · exact Or.inr (Mech.live_eq_of_suit_left (canRaiseS_rung hS) hy hs)
      · exact Or.inl (Mech.live_eq_of_suit_twin (canRaiseS_rung htwin) hy hs)
  · intro h
    refine ⟨(h c.twin).mp (Or.inl rfl), ?_⟩
    intro e he
    rcases (h e).mpr he with h' | h'
    · exact Or.inr (congrArg Card.suit h')
    · exact Or.inl (congrArg Card.suit h')

theorem raise_eq_twin_of_block_containment {F : State} {c d : Card}
    (hS : CanRaiseS F c) (hblock : ¬ CanRaise F c)
    (hcont : ∀ e, CanRaiseS F e → e.suit = c.suit ∨ e.suit = c.twin.suit)
    (hrungT : rungAt F c.twin.suit = c.rank.toIdx)
    (hcanD : CanRaise F d) : d = c.twin := by
  have hSd : CanRaiseS F d := CanRaiseS.now d hcanD
  rcases hcont d hSd with hs | hs
  · have hdc : d = c := Mech.live_eq_of_suit_left (canRaiseS_rung hS) hSd hs
    rw [hdc] at hcanD
    exact absurd hcanD hblock
  · exact Mech.live_eq_of_suit_twin hrungT hSd hs

/-- **THE FIRST CONJUNCT FROM THE OTHER CLAUSE + THE PIN.**  Not merely
`CanRaiseS F c.twin` but the vanilla `CanRaise F c.twin`. -/
theorem canRaise_twin_of_block_containment {F : State} {c d : Card}
    (hS : CanRaiseS F c) (hblock : ¬ CanRaise F c)
    (hcont : ∀ e, CanRaiseS F e → e.suit = c.suit ∨ e.suit = c.twin.suit)
    (hrungT : rungAt F c.twin.suit = c.rank.toIdx)
    (hcanD : CanRaise F d) : CanRaise F c.twin := by
  have hd := raise_eq_twin_of_block_containment hS hblock hcont hrungT hcanD
  rw [hd] at hcanD
  exact hcanD

/-- **THE FIRST CONJUNCT FROM THE OTHER CLAUSE + THE PIN, ON `nextUp`.** -/
theorem canRaiseS_twin_of_block_containment {F : State} {c d : Card}
    (hS : CanRaiseS F c) (hblock : ¬ CanRaise F c)
    (hcont : ∀ e, CanRaiseS F e → e.suit = c.suit ∨ e.suit = c.twin.suit)
    (hpin : F.nextUp c.twin = true) (hcanD : CanRaise F d) :
    CanRaiseS F c.twin :=
  CanRaiseS.now c.twin
    (canRaise_twin_of_block_containment hS hblock hcont (nextUp_true_iff.mp hpin) hcanD)

/-- **`SplitTwinRungPin`** — THE SHARPEST RESIDUAL THIS CARD REACHES: at every
split's bottom, the twin suit's rung sits exactly at `c`'s rank index.  This
is a pure ledger statement (one coordinate of the dip), not a licence
statement.  It is *implied* by the first conjunct
(`nextUp_twin_of_landingLivePair`), so assuming it is not a weakening of the
target — it is the part of the target the mountain/ledger campaign can attack
without any cargo content. -/
def SplitTwinRungPin : Prop :=
  ∀ (u v : State) (ρ : List Move) (F : State)
    (left right : List Move) (c d : Card) (b : Base)
    (pre post tail : List Move),
    SplitKit.SplitHyp u v ρ F left right c d b pre post tail → F.nextUp c.twin = true

/-- **`SplitContainment`** — the second landing clause, one instance per
split, read at the bottom `F`.  (The other agent's clause; only *named*
here, never proved.) -/
def SplitContainment : Prop :=
  ∀ (u v : State) (ρ : List Move) (F : State)
    (left right : List Move) (c d : Card) (b : Base)
    (pre post tail : List Move),
    SplitKit.SplitHyp u v ρ F left right c d b pre post tail →
    ∀ e, CanRaiseS F e → e.suit = c.suit ∨ e.suit = c.twin.suit

theorem pin_iff_pairRungEq {F : State} {c : Card} (hS : CanRaiseS F c) :
    F.nextUp c.twin = true ↔ rungAt F c.twin.suit = rungAt F c.suit := by
  rw [nextUp_true_iff]
  constructor
  · intro h
    rw [h, canRaiseS_rung hS]
    rfl
  · intro h
    rw [h]
    exact canRaiseS_rung hS

/-- **`SplitPairRungEq`** — THE RESIDUAL IN LEDGER FORM: at every valley
bottom the two suits of the twin pair sit on the SAME rung.  (The bottom form
of `forkState_witness_rungs`, with the licence content removed.) -/
def SplitPairRungEq : Prop :=
  ∀ (u v : State) (ρ : List Move) (F : State)
    (left right : List Move) (c d : Card) (b : Base)
    (pre post tail : List Move),
    SplitKit.SplitHyp u v ρ F left right c d b pre post tail →
    rungAt F c.twin.suit = rungAt F c.suit

/-- **THE LEDGER FORM AND THE `nextUp` FORM ARE THE SAME RESIDUAL.** -/
theorem splitPairRungEq_iff_splitTwinRungPin :
    SplitPairRungEq ↔ SplitTwinRungPin := by
  constructor
  · intro h u v ρ F left right c d b pre post tail hh
    exact (pin_iff_pairRungEq (SplitKit.splitHyp_green hh).2.1).mpr
      (h u v ρ F left right c d b pre post tail hh)
  · intro h u v ρ F left right c d b pre post tail hh
    exact (pin_iff_pairRungEq (SplitKit.splitHyp_green hh).2.1).mp
      (h u v ρ F left right c d b pre post tail hh)

/-! ## §6. Route B at the split level -/

/-- **THE FIRST CONJUNCT AT EVERY SPLIT, FROM THE OTHER CLAUSE + THE PIN.**
`SplitBlock` + `SplitContainment` + `SplitTwinRungPin` ⟹
`LandKit.SplitLandingTwin`.  The siting is never assumed: it comes from the
raise card's vanilla licence (Route B). -/
theorem splitLandingTwin_of_block_containment_of_pin
    (hb : SplitKit.SplitBlock) (hc : SplitContainment) (hp : SplitTwinRungPin) :
    LandKit.SplitLandingTwin := by
  intro u v ρ F left right c d b pre post tail h A' B hpre hstep
  have hk := h
  obtain ⟨huwf, -, -, -, -, -, -, hleft, -, hshape, hfree, -⟩ := h
  obtain ⟨hF, hSc, hcanD, -⟩ := SplitKit.splitHyp_green hk
  have hblock : ¬ CanRaise F c := hb u v ρ F left right c d b pre post tail hk
  have hcont : ∀ e, CanRaiseS F e → e.suit = c.suit ∨ e.suit = c.twin.suit :=
    hc u v ρ F left right c d b pre post tail hk
  have hpin : F.nextUp c.twin = true :=
    hp u v ρ F left right c d b pre post tail hk
  have htwinF : CanRaiseS F c.twin :=
    canRaiseS_twin_of_block_containment hSc hblock hcont hpin hcanD
  have hA' : A'.WF := SatDifferCensus.ShufflePlayW.wf_end hpre huwf
  have hB : B.WF := step_wf hA' hstep
  have hpost : ShufflePlayW B post F :=
    shufflePlayW_tail_of_step (hshape ▸ hleft) hpre hstep
  exact (Mech.canRaiseS_landing_iff hB hpost hfree c.twin).mpr htwinF

theorem mechanismResidual_of_block_containment_of_pin
    (hb : SplitKit.SplitBlock) (hc : SplitContainment) (hp : SplitTwinRungPin) :
    Mech.MechanismResidual := by
  intro u v ρ F left right c d b pre post tail h
  have hk := h
  obtain ⟨huwf, -, -, -, -, -, -, hleft, -, hshape, hfree, -⟩ := h
  obtain ⟨hF, hSc, hcanD, -⟩ := SplitKit.splitHyp_green hk
  have hblock : ¬ CanRaise F c := hb u v ρ F left right c d b pre post tail hk
  have hcont : ∀ e, CanRaiseS F e → e.suit = c.suit ∨ e.suit = c.twin.suit :=
    hc u v ρ F left right c d b pre post tail hk
  have hpin : F.nextUp c.twin = true :=
    hp u v ρ F left right c d b pre post tail hk
  have htwinF : CanRaiseS F c.twin :=
    canRaiseS_twin_of_block_containment hSc hblock hcont hpin hcanD
  obtain ⟨A', hpre, hrest⟩ :=
    ValleyElim.ShufflePlayW_split hleft pre (Move.foundToTab c b :: post) hshape
  cases hrest with
  | @cons _ B _ _ _ hrev hstep hpost =>
      have hA' : A'.WF := SatDifferCensus.ShufflePlayW.wf_end hpre huwf
      have hB : B.WF := step_wf hA' hstep
      have hcanB : CanRaise B c := ValleyStep.pull_card_canRaise hA' hstep
      have htwinB : CanRaiseS B c.twin :=
        (Mech.canRaiseS_landing_iff hB hpost hfree c.twin).mpr htwinF
      have hcontB : ∀ e, CanRaiseS B e →
          e.suit = c.suit ∨ e.suit = c.twin.suit :=
        fun e he => hcont e ((Mech.canRaiseS_landing_iff hB hpost hfree e).mp he)
      exact ⟨A', B, hpre, hstep, hpost, ⟨htwinB, hcontB⟩,
        Mech.coverEvent_of_block hB hpost hfree hcanB hSc hblock⟩

theorem splitTwinRungPin_of_splitLandingTwin (h : LandKit.SplitLandingTwin) :
    SplitTwinRungPin := by
  intro u v ρ F left right c d b pre post tail hh
  have hk := hh
  obtain ⟨-, -, -, -, -, -, -, hleft, -, hshape, hfree, -⟩ := hh
  obtain ⟨A', hpre, hrest⟩ :=
    ValleyElim.ShufflePlayW_split hleft pre (Move.foundToTab c b :: post) hshape
  cases hrest with
  | @cons _ B _ _ _ hrev hstep hpost =>
      have hlive : CanRaiseS B c.twin :=
        h u v ρ F left right c d b pre post tail hk A' B hpre hstep
      have hnext : B.nextUp c.twin = true :=
        nextUp_true_iff.mpr (canRaiseS_rung hlive)
      exact (nextUp_of_free_play_iff hpost hfree).mp hnext

/-- **THE EXACT EQUIVALENCE.**  Given `SplitBlock` and the containment clause,
the first landing conjunct is *exactly* the rung pin `SplitTwinRungPin`.
Nothing else is left: no siting, no licence, no cargo. -/
theorem splitLandingTwin_iff_splitTwinRungPin
    (hb : SplitKit.SplitBlock) (hc : SplitContainment) :
    LandKit.SplitLandingTwin ↔ SplitTwinRungPin :=
  ⟨splitTwinRungPin_of_splitLandingTwin,
    splitLandingTwin_of_block_containment_of_pin hb hc⟩

/-! ## §6c. The campaign in ledger form -/

/-- **THE CAMPAIGN FROM THREE CLAUSES, IN LEDGER FORM.**
`SplitBlock` + `SplitContainment` + `SplitPairRungEq` ⟹
`Mech.MechanismResidual`. -/
theorem mechanismResidual_of_block_containment_of_pairRungEq
    (hb : SplitKit.SplitBlock) (hc : SplitContainment) (hr : SplitPairRungEq) :
    Mech.MechanismResidual :=
  mechanismResidual_of_block_containment_of_pin hb hc
    (splitPairRungEq_iff_splitTwinRungPin.mp hr)

/-! ## §6d. `SplitTwin`, `SplitLivePair` and `SplitResidualData` derived -/

/-- **THE RAISE CARD IS THE TWIN, AT EVERY SPLIT.**  `SplitKit.SplitTwin` is
a *consequence* of `SplitBlock` + `SplitContainment` + `SplitTwinRungPin`, not
an assumption. -/
theorem splitTwin_of_block_containment_of_pin
    (hb : SplitKit.SplitBlock) (hc : SplitContainment) (hp : SplitTwinRungPin) :
    SplitKit.SplitTwin := by
  intro u v ρ F left right c d b pre post tail hh
  obtain ⟨-, hSc, hcanD, -⟩ := SplitKit.splitHyp_green hh
  exact raise_eq_twin_of_block_containment hSc
    (hb u v ρ F left right c d b pre post tail hh)
    (hc u v ρ F left right c d b pre post tail hh)
    (nextUp_true_iff.mp (hp u v ρ F left right c d b pre post tail hh))
    hcanD

/-- **THE CORRECTED RESIDUAL `SplitResidualData`, DERIVED.**  With
`SplitBlock`, `SplitContainment` and `SplitTwinRungPin` supplying clause 1
and clause 2, only the third agent's rank floor `SplitFloor` is left. -/
theorem splitResidualData_of_block_containment_of_pin_floor
    (hb : SplitKit.SplitBlock) (hc : SplitContainment) (hp : SplitTwinRungPin)
    (hfloor : SplitKit.SplitFloor) : SplitKit.SplitResidualData :=
  SplitKit.splitResidualData_of_parts
    (splitTwin_of_block_containment_of_pin hb hc hp) hb hfloor

#print axioms TwinKit.nextUp_true_iff
#print axioms TwinKit.nextUp_of_free_play_iff
#print axioms TwinKit.shufflePlayW_tail_of_step
#print axioms TwinKit.sited_of_canRaiseS
#print axioms TwinKit.canRaiseS_twin_iff
#print axioms TwinKit.canRaiseS_twin_of_datum
#print axioms TwinKit.canRaiseS_twin_at_landing
#print axioms TwinKit.canRaiseS_twin_at_landing_iff
#print axioms TwinKit.forkWitness_twin_iff_pairExact
#print axioms TwinKit.landingLivePair_iff_pairExact
#print axioms TwinKit.raise_eq_twin_of_block_containment
#print axioms TwinKit.canRaise_twin_of_block_containment
#print axioms TwinKit.canRaiseS_twin_of_block_containment
#print axioms TwinKit.splitLandingTwin_of_block_containment_of_pin
#print axioms TwinKit.mechanismResidual_of_block_containment_of_pin
#print axioms TwinKit.splitTwinRungPin_of_splitLandingTwin
#print axioms TwinKit.splitLandingTwin_iff_splitTwinRungPin
#print axioms TwinKit.pin_iff_pairRungEq
#print axioms TwinKit.splitPairRungEq_iff_splitTwinRungPin
#print axioms TwinKit.mechanismResidual_of_block_containment_of_pairRungEq
#print axioms TwinKit.splitTwin_of_block_containment_of_pin
#print axioms TwinKit.splitResidualData_of_block_containment_of_pin_floor

end TwinKit
