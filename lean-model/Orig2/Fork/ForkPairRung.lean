import Orig2.Fork.ForkTwinLive

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

/-!
# Orig2-scratch `PairRung` — the twin clause as a ONE-SIDED rung inequality

READ-ONLY scratch card: no source edit, no commit.  Zero `sorry`, zero
`Classical.choice`, zero `native_decide`; axiom battery at the tail.

## What this card proves

The campaign's last purely arithmetic clause is

    `TwinKit.SplitPairRungEq`  :=  at every split,
        `rungAt F c.twin.suit = rungAt F c.suit`

(`Orig2/Fork/ForkTwinLive.lean:411`), equivalent to `TwinKit.SplitTwinRungPin`
(`splitPairRungEq_iff_splitTwinRungPin`, `Orig2/Fork/ForkTwinLive.lean:419`).

**§2 — the upper half is FREE.**  The cover clause of the twin's licence is a
theorem at any blocked bottom: with `CanRaiseS F c` and `¬ CanRaise F c`, the
card `c.twin` must top some pile (`pileOfTop_twin_of_block`).  For if `c` topped
its pile, it would be vanilla-raisable, against the block; so the S-licence of
`c` must be discharging its `fromCard`-or-twin-top clause through `c.twin`.
The piled-rung read (`piled_rung`, `Orig2/Fork/Cover.lean:46`) then gives

    `rungAt F c.twin.suit ≤ c.rank.toIdx = rungAt F c.suit`
    (`rungAt_twin_le_of_block`).

**§3 — the residual is ONE inequality.**  Consequently, given the campaign's
`SplitBlock`, the two rung statements are EQUIVALENT:

    `SplitPairRungEq ↔ SplitTwinRungGe`   (`splitPairRungEq_iff_ge_of_block`)

where `SplitTwinRungGe` is the single inequality
`rungAt F c.suit ≤ rungAt F c.twin.suit` at every split.  This is the exact
residual: *no* licence content, *no* card equation, one Nat comparison.  (The
pull card's own rung is pinned to `c.rank.toIdx` by `CanRaiseS F c`, so the
inequality is `c.rank.toIdx ≤ rungAt F c.twin.suit`.)  The failure mode is
therefore ONE-SIDED: a failing pin always has the twin suit *strictly behind*
(`pin_fails_iff_strictly_behind`), never ahead.  In the brief's spelling, the
half `rungAt F c.twin.suit ≤ rungAt F c.suit` is a THEOREM under `SplitBlock`
(`SplitTwinRungLe`, `splitTwinRungLe_of_block`); the residual is its converse.

**§4 — the residual can be read BEFORE the pull.**  The free tail and the pull
itself move no twin-suit rung, so the pin at the bottom is equivalent to the
rung GAP at the pre-pull state `A'` (`u --pre--> A' --pull c--> …`):

    `rungAt F c.twin.suit = rungAt F c.suit`
      ↔ `rungAt A' c.twin.suit + 1 = rungAt A' c.suit`
        (`prePull_gap_iff_bottom_pin`),

and globally `SplitPairRungEq ↔ SplitPrePullGap`
(`splitPairRungEq_iff_prePullGap`).

**§5 — fragments proved outright.**  The pin is *implied* by the mechanism
clause (`d = c.twin`, hence `SplitKit.SplitTwin → SplitPairRungEq`), and if the
pull card is an ace (`c.rank.toIdx = 0`) the residual's inequality
`0 ≤ rungAt F c.twin.suit` is trivial, so the pin is a THEOREM at every such
split (`pin_of_pull_ace`).

**§6 — the campaign consumes the new residual.**  `SplitBlock` +
`SplitContainment` + `SplitTwinRungGe` + `ShortestPlayExists` already give
`SatDifferForkWF` (`satDifferForkWF_of_block_containment_of_ge`): the one-sided
residual upgrades to the campaign's pin by §3, and the campaign chain
(`TwinKit.satDifferForkWF_of_block_containment_of_pairRungEq`,
`Orig2/Fork/ForkTwinLive.lean:577`) takes over.

## The exact residual (verbatim)

```lean
def SplitTwinRungGe : Prop :=
  ∀ (u v : State) (ρ : List Move) (F : State)
    (left right : List Move) (c d : Card) (b : Base)
    (pre post tail : List Move),
    SplitKit.SplitHyp u v ρ F left right c d b pre post tail →
    rungAt F c.suit ≤ rungAt F c.twin.suit
```

or, free of the bottom, `SplitPrePullGap` (§4):

```lean
∀ …, SplitHyp … → rungAt A' c.twin.suit + 1 = rungAt A' c.suit
```

(`A'` the pre-pull state).  Both are proved EQUIVALENT to `SplitPairRungEq`
given `SplitBlock`.
-/

namespace PairRungKit

open TwinKit

/-! ## §1. Kit: `chop`/`lastOf` of a singleton `fromCard` -/

/- KIT-HOIST STRIKE (2026-11-01): `chop_append_singleton` is hoisted to
`Orig2/Substrate/Kit.lean` (one home below both former copies); the cites
re-point there by name. -/

/-- If `fromCard c l` is the singleton `[c]`, then `c` is the LAST card of
`l` (nothing sits above it). -/
theorem lastOf_of_fromCard_singleton {l : List Card} {c : Card}
    (h : fromCard c l = [c]) : lastOf l = some c := by
  have hsplit : below c l ++ fromCard c l = l := tfc_below_fromCard c l
  rw [h] at hsplit
  rw [← hsplit]
  exact lastOf_snoc

/-- The same in `pileOfTop` form. -/
theorem pileOfTop_of_fromCard_singleton {st : State} {c : Card} {a : Anchor}
    (hwf : st.WF) (h : fromCard c (st.piles a).faceUp = [c]) :
    st.pileOfTop c = some a :=
  (pileOfTop_eq_some_iff hwf).2 (lastOf_of_fromCard_singleton h)

/-! ## §2. The cover clause of the twin is free at a blocked bottom -/

/-- **THE TWIN TOPS A PILE WHEN THE PULL CARD IS BLOCKED.**  `CanRaiseS F c`
discharges its `fromCard`-or-twin-top clause; the first arm puts `c` on top of
its pile with company below, i.e. `CanRaise F c` (its rung is already `c`'s),
contradicting the block.  So the second arm holds. -/
theorem pileOfTop_twin_of_block {F : State} {c : Card}
    (hF : F.WF) (hS : CanRaiseS F c) (hb : ¬ CanRaise F c) :
    F.pileOfTop c.twin ≠ none := by
  obtain ⟨hnext, a, hmem, hseat, hdisj⟩ :=
    (LandKit.canRaiseS_below_form hF).mp hS
  rcases hdisj with hsingle | htop
  · exfalso
    apply hb
    have hpod : F.pileOfTop c = some a :=
      pileOfTop_of_fromCard_singleton hF hsingle
    refine ⟨hnext, a, hpod, ?_⟩
    rcases hseat with hbelow | hbare
    · left
      have hsplit : below c (F.piles a).faceUp ++ [c] = (F.piles a).faceUp := by
        have h' := tfc_below_fromCard c (F.piles a).faceUp
        rw [hsingle] at h'
        exact h'
      rw [← hsplit, chop_append_singleton]
      exact hbelow
    · exact Or.inr hbare
  · exact htop

/-- **THE UPPER HALF OF THE PIN IS FREE.**  At a blocked bottom the twin-suit
rung sits at or below the pull card's rank index.  (`piled_rung`,
`Orig2/Fork/Cover.lean:46`: a face-up card's suit rung never exceeds its rank
index, since a taller rung would have founded it — against conservation.) -/
theorem rungAt_twin_le_of_block {F : State} {c : Card}
    (hF : F.WF) (hS : CanRaiseS F c) (hb : ¬ CanRaise F c) :
    rungAt F c.twin.suit ≤ c.rank.toIdx := by
  obtain ⟨a, htop⟩ :=
    option_some_of_ne_none (pileOfTop_twin_of_block hF hS hb)
  have hmem : c.twin ∈ (F.piles a).faceUp :=
    Pile.mem_of_top ((pileOfTop_eq_some_iff hF).mp htop)
  have hle : rungAt F c.twin.suit ≤ c.twin.rank.toIdx :=
    piled_rung hF hmem
  rwa [Card.twin_rank] at hle

/-! ## §3. The residual is a ONE-SIDED inequality -/

/-- **`SplitTwinRungGe`** — THE RESIDUAL, ONE INEQUALITY: at every split the
pull card's own suit sits at or below the twin suit.  No licence, no card
equation.  (`rungAt F c.suit` is *pinned* to `c.rank.toIdx` by `CanRaiseS F c`,
so this is `c.rank.toIdx ≤ rungAt F c.twin.suit`: the twin suit already
carries every lower card.) -/
def SplitTwinRungGe : Prop :=
  ∀ (u v : State) (ρ : List Move) (F : State)
    (left right : List Move) (c d : Card) (b : Base)
    (pre post tail : List Move),
    SplitKit.SplitHyp u v ρ F left right c d b pre post tail →
    rungAt F c.suit ≤ rungAt F c.twin.suit

/-- **`SplitTwinRungLe`** — the *other* inequality: at every split the twin
suit sits at or below the pull card's own suit.  This one is a THEOREM under
the campaign's `SplitBlock` (`splitTwinRungLe_of_block`): the twin is never
ahead.  The residual `SplitTwinRungGe` is exactly its converse. -/
def SplitTwinRungLe : Prop :=
  ∀ (u v : State) (ρ : List Move) (F : State)
    (left right : List Move) (c d : Card) (b : Base)
    (pre post tail : List Move),
    SplitKit.SplitHyp u v ρ F left right c d b pre post tail →
    rungAt F c.twin.suit ≤ rungAt F c.suit

/-- **THE `≤` HALF OF THE PIN IS FREE.**  Under `SplitBlock`, at every split
`rungAt F c.twin.suit ≤ rungAt F c.suit`.  (This is the inequality the brief
asks for: it is `rungAt_twin_le_of_block` plus `canRaiseS_rung`.) -/
theorem splitTwinRungLe_of_block (hb : SplitKit.SplitBlock) : SplitTwinRungLe := by
  intro u v ρ F left right c d b pre post tail h
  obtain ⟨hF, hSc, -, -⟩ := SplitKit.splitHyp_green h
  have hle := rungAt_twin_le_of_block hF hSc
    (hb u v ρ F left right c d b pre post tail h)
  have hsig : rungAt F c.suit = c.rank.toIdx := canRaiseS_rung hSc
  omega

/-- The one-sided residual upgrades to the pair-rung equality under the
campaign's `SplitBlock`. -/
theorem splitPairRungEq_of_block_of_ge
    (hb : SplitKit.SplitBlock) (hg : SplitTwinRungGe) :
    SplitPairRungEq := by
  intro u v ρ F left right c d b pre post tail h
  obtain ⟨hF, hSc, -, -⟩ := SplitKit.splitHyp_green h
  have hblock : ¬ CanRaise F c := hb u v ρ F left right c d b pre post tail h
  have hle := rungAt_twin_le_of_block hF hSc hblock
  have hsig : rungAt F c.suit = c.rank.toIdx := canRaiseS_rung hSc
  have hge := hg u v ρ F left right c d b pre post tail h
  omega

/-- The pair-rung equality gives the one-sided residual. -/
theorem splitTwinRungGe_of_pairRungEq (h : SplitPairRungEq) :
    SplitTwinRungGe := by
  intro u v ρ F left right c d b pre post tail hh
  exact Nat.le_of_eq (h u v ρ F left right c d b pre post tail hh).symm

/-- **THE EXACT FORM OF THE RESIDUAL.**  Given the campaign's `SplitBlock`,
`SplitPairRungEq` and the single inequality `SplitTwinRungGe` are the SAME
statement. -/
theorem splitPairRungEq_iff_ge_of_block (hb : SplitKit.SplitBlock) :
    SplitPairRungEq ↔ SplitTwinRungGe :=
  ⟨splitTwinRungGe_of_pairRungEq, splitPairRungEq_of_block_of_ge hb⟩

/-! ## §4. The residual read BEFORE the pull -/

/-- **THE PULL AND THE FREE TAIL MOVE NO TWIN-SUIT RUNG.**  Across
`A' --pull c--> B --post (free)--> F` the twin suit's rung is untouched. -/
theorem prePull_twin_rung {A' B F : State} {c : Card} {b : Base}
    {post : List Move}
    (hstep : State.step A' (Move.foundToTab c b) = some B)
    (hpost : ShufflePlayW B post F) (hfree : ∀ m ∈ post, ValleyElim.FreeMove m) :
    rungAt A' c.twin.suit = rungAt F c.twin.suit := by
  have hB_tau : rungAt B c.twin.suit = rungAt A' c.twin.suit := by
    have h := rungAt_foundToTab hstep c.twin.suit
    have hne : ¬ (c.twin.suit = c.suit) := by
      intro hc
      exact Suit.twin_ne c.suit (by simpa [Card.twin_suit] using hc)
    rw [ite_eq_right hne] at h
    exact h
  have hF_tau : rungAt F c.twin.suit = rungAt B c.twin.suit :=
    ValleyElim.rungAt_eq_of_free_play hpost hfree c.twin.suit
  rw [hF_tau, hB_tau]

/-- **THE PULL COSTS EXACTLY ONE RUNG OF `c`'s OWN SUIT.**  Across
`A' --pull c--> B --post (free)--> F`, `rungAt A' c.suit = rungAt F c.suit + 1`
(the pull is legal, so `A'` has `c` on top of a nonempty foundation). -/
theorem prePull_own_rung {A' B F : State} {c : Card} {b : Base}
    {post : List Move}
    (hA' : A'.WF) (hstep : State.step A' (Move.foundToTab c b) = some B)
    (hpost : ShufflePlayW B post F) (hfree : ∀ m ∈ post, ValleyElim.FreeMove m) :
    rungAt A' c.suit = rungAt F c.suit + 1 := by
  obtain ⟨c', htop, hc', -, -⟩ := step_foundToTab_inv hstep
  rw [hc'] at htop
  have hAc : c.rank.toIdx + 1 = rungAt A' c.suit :=
    SatDifferCensus.foundTop_rank_succ hA' htop
  have hB_sig : rungAt B c.suit = rungAt A' c.suit - 1 := by
    have h := rungAt_foundToTab hstep c.suit
    rw [ite_eq_left rfl] at h
    exact h
  have hF_sig : rungAt F c.suit = rungAt B c.suit :=
    ValleyElim.rungAt_eq_of_free_play hpost hfree c.suit
  omega

/-- **THE PIN AT `F` IS THE RUNG GAP AT `A'`.**  The pin at the bottom is
exactly the statement that the two twin suits sit one rung apart at the
pre-pull state. -/
theorem prePull_gap_iff_bottom_pin {A' B F : State} {c : Card} {b : Base}
    {post : List Move}
    (hA' : A'.WF) (hstep : State.step A' (Move.foundToTab c b) = some B)
    (hpost : ShufflePlayW B post F) (hfree : ∀ m ∈ post, ValleyElim.FreeMove m) :
    (rungAt F c.twin.suit = rungAt F c.suit) ↔
      (rungAt A' c.twin.suit + 1 = rungAt A' c.suit) := by
  have htau : rungAt A' c.twin.suit = rungAt F c.twin.suit :=
    prePull_twin_rung hstep hpost hfree
  have hsig : rungAt A' c.suit = rungAt F c.suit + 1 :=
    prePull_own_rung hA' hstep hpost hfree
  constructor <;> intro h <;> omega

/-- **`SplitPrePullGap`** — the residual at the state BEFORE the pull: the two
twin suits sit exactly one rung apart.  (`A'` is the state `pre` reaches.) -/
def SplitPrePullGap : Prop :=
  ∀ (u v : State) (ρ : List Move) (F : State)
    (left right : List Move) (c d : Card) (b : Base)
    (pre post tail : List Move),
    SplitKit.SplitHyp u v ρ F left right c d b pre post tail →
    ∀ (A' : State), ShufflePlayW u pre A' →
      rungAt A' c.twin.suit + 1 = rungAt A' c.suit

/-- Extract the pre-pull state of a split together with its pull step. -/
theorem split_pre_pull_data {u v : State} {ρ : List Move} {F : State}
    {left right : List Move} {c d : Card} {b : Base}
    {pre post tail : List Move}
    (h : SplitKit.SplitHyp u v ρ F left right c d b pre post tail) :
    ∃ (A' B : State), ShufflePlayW u pre A' ∧
      State.step A' (Move.foundToTab c b) = some B ∧
      ShufflePlayW B post F := by
  obtain ⟨-, -, -, -, -, -, -, hleft, -, hshape, -, -⟩ := h
  obtain ⟨A', hpre, hrest⟩ :=
    ValleyElim.ShufflePlayW_split hleft pre (Move.foundToTab c b :: post) hshape
  cases hrest with
  | cons hrev hstep hpost => exact ⟨A', _, hpre, hstep, hpost⟩

/-- `SplitPairRungEq` implies the pre-pull gap. -/
theorem splitPrePullGap_of_pairRungEq (h : SplitPairRungEq) : SplitPrePullGap := by
  refine fun u v ρ F left right c d b pre post tail hh A' hpre => ?_
  have hk := hh
  obtain ⟨hF, hSc, -, -⟩ := SplitKit.splitHyp_green hh
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hfree, -⟩ := hk
  obtain ⟨A'', B, hpre'', hstep, hpost⟩ := split_pre_pull_data hh
  have hA'' : A''.WF := SatDifferCensus.ShufflePlayW.wf_end hpre'' hh.1
  have hAA : A'' = A' :=
    Option.some.inj ((Walk_run _ hpre'').symm.trans (Walk_run _ hpre))
  subst hAA
  exact (prePull_gap_iff_bottom_pin hA'' hstep hpost hfree).mp
    (h u v ρ F left right c d b pre post tail hh)

/-- The pre-pull gap implies `SplitPairRungEq`. -/
theorem pairRungEq_of_splitPrePullGap (hg : SplitPrePullGap) : SplitPairRungEq := by
  refine fun u v ρ F left right c d b pre post tail hh => ?_
  have hk := hh
  obtain ⟨-, hSc, -, -⟩ := SplitKit.splitHyp_green hh
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hfree, -⟩ := hk
  obtain ⟨A', B, hpre, hstep, hpost⟩ := split_pre_pull_data hh
  have hA' : A'.WF := SatDifferCensus.ShufflePlayW.wf_end hpre hh.1
  exact (prePull_gap_iff_bottom_pin hA' hstep hpost hfree).mpr
    (hg u v ρ F left right c d b pre post tail hh A' hpre)

/-- **THE RESIDUAL, PULL-FREE FORM.**  `SplitPairRungEq` and the pre-pull rung
gap are the same statement. -/
theorem splitPairRungEq_iff_prePullGap :
    SplitPairRungEq ↔ SplitPrePullGap :=
  ⟨splitPrePullGap_of_pairRungEq, pairRungEq_of_splitPrePullGap⟩

/-- **`SplitPrePullGe`** — the ONE-SIDED residual read at the pre-pull state
`A'`: the twin suit already carries `c`'s rank index.  No block, no licence. -/
def SplitPrePullGe : Prop :=
  ∀ (u v : State) (ρ : List Move) (F : State)
    (left right : List Move) (c d : Card) (b : Base)
    (pre post tail : List Move),
    SplitKit.SplitHyp u v ρ F left right c d b pre post tail →
    ∀ (A' : State), ShufflePlayW u pre A' →
      c.rank.toIdx ≤ rungAt A' c.twin.suit

/-- **THE ONE-SIDED RESIDUAL, PULL-FREE FORM.**  The one-sided inequality at
the bottom and at the pre-pull state are the same statement (the twin-suit
rung is transported by `prePull_twin_rung`; the own-suit rung is pinned to
`c.rank.toIdx` by `CanRaiseS`). -/
theorem splitTwinRungGe_iff_prePullGe :
    SplitTwinRungGe ↔ SplitPrePullGe := by
  constructor
  · intro hg u v ρ F left right c d b pre post tail hh A' hpre
    obtain ⟨-, hSc, -, -⟩ := SplitKit.splitHyp_green hh
    have hk := hh
    obtain ⟨-, -, -, -, -, -, -, -, -, -, hfree, -⟩ := hk
    obtain ⟨A'', B, hpre'', hstep, hpost⟩ := split_pre_pull_data hh
    have hAA : A'' = A' :=
      Option.some.inj ((Walk_run _ hpre'').symm.trans (Walk_run _ hpre))
    have htau : rungAt A'' c.twin.suit = rungAt F c.twin.suit :=
      prePull_twin_rung hstep hpost hfree
    have hsig : rungAt F c.suit = c.rank.toIdx := canRaiseS_rung hSc
    have hge := hg u v ρ F left right c d b pre post tail hh
    rw [← hAA]
    omega
  · intro hg u v ρ F left right c d b pre post tail hh
    obtain ⟨-, hSc, -, -⟩ := SplitKit.splitHyp_green hh
    have hk := hh
    obtain ⟨-, -, -, -, -, -, -, -, -, -, hfree, -⟩ := hk
    obtain ⟨A', B, hpre, hstep, hpost⟩ := split_pre_pull_data hh
    have htau : rungAt A' c.twin.suit = rungAt F c.twin.suit :=
      prePull_twin_rung hstep hpost hfree
    have hsig : rungAt F c.suit = c.rank.toIdx := canRaiseS_rung hSc
    have hge := hg u v ρ F left right c d b pre post tail hh A' hpre
    omega

/-- **THE RESIDUAL AT THE PRE-PULL STATE, ONE INEQUALITY.**  Given
`SplitBlock`, `SplitPairRungEq` is the single inequality
`c.rank.toIdx ≤ rungAt A' c.twin.suit` at every split. -/
theorem splitPairRungEq_iff_prePullGe_of_block (hb : SplitKit.SplitBlock) :
    SplitPairRungEq ↔ SplitPrePullGe :=
  (splitPairRungEq_iff_ge_of_block hb).trans splitTwinRungGe_iff_prePullGe

/-! ## §5. Fragments proved outright -/

/-- **THE FAILURE MODE IS ONE-SIDED.**  At a blocked bottom, if the pin fails
then the twin suit is strictly BEHIND: `rungAt F c.twin.suit < c.rank.toIdx`.
The twin can never be *ahead* (that direction is `rungAt_twin_le_of_block`), so
the whole residual is the single question "has the twin suit caught up?". -/
theorem pin_fails_iff_strictly_behind {F : State} {c : Card}
    (hF : F.WF) (hS : CanRaiseS F c) (hb : ¬ CanRaise F c) :
    (rungAt F c.twin.suit < c.rank.toIdx) ↔
      (rungAt F c.twin.suit ≠ rungAt F c.suit) := by
  have hle := rungAt_twin_le_of_block hF hS hb
  have hsig := canRaiseS_rung hS
  constructor <;> intro h <;> omega

/-- **THE PIN IS IMPLIED BY THE MECHANISM CLAUSE.**  If the raise card is the
pull card's twin (the campaign's `SplitKit.SplitTwin`), the pin follows from
`CanRaise F d`'s rung gate.  So the one-sided residual is *necessary* for the
mechanism, and `SplitTwin ⟹ SplitPairRungEq`. -/
theorem pin_of_raise_eq_twin {u v : State} {ρ : List Move} {F : State}
    {left right : List Move} {c d : Card} {b : Base}
    {pre post tail : List Move}
    (h : SplitKit.SplitHyp u v ρ F left right c d b pre post tail)
    (hd : d = c.twin) :
    rungAt F c.twin.suit = rungAt F c.suit := by
  obtain ⟨-, hSc, hcanD, -⟩ := SplitKit.splitHyp_green h
  have hr : rungAt F d.suit = d.rank.toIdx := nextUp_true_iff.mp hcanD.1
  rw [hd, Card.twin_rank] at hr
  rw [hr, canRaiseS_rung hSc]

/-- `SplitKit.SplitTwin` (the mechanism's card equation) implies the pair-rung
clause. -/
theorem splitPairRungEq_of_splitTwin (h : SplitKit.SplitTwin) :
    SplitPairRungEq := by
  intro u v ρ F left right c d b pre post tail hh
  exact pin_of_raise_eq_twin hh (h u v ρ F left right c d b pre post tail hh)

/-- **THE PIN AT AN ACE PULL.**  If the pull card is an ace, the pull card's
own suit rung is `0` at the bottom, so the one-sided residual
`0 ≤ rungAt F c.twin.suit` is trivial and the pin is a theorem at a blocked
bottom. -/
theorem pin_of_pull_ace {F : State} {c : Card}
    (hF : F.WF) (hS : CanRaiseS F c) (hb : ¬ CanRaise F c)
    (hace : c.rank.toIdx = 0) :
    rungAt F c.twin.suit = rungAt F c.suit := by
  have hsig : rungAt F c.suit = 0 := by
    rw [canRaiseS_rung hS, hace]
  have hle := rungAt_twin_le_of_block hF hS hb
  rw [hace] at hle
  rw [hsig]
  omega

/-- The ace fragment at every split. -/
theorem splitPairRungEq_of_block_of_pull_ace
    (hb : SplitKit.SplitBlock)
    (hace : ∀ (u v : State) (ρ : List Move) (F : State)
      (left right : List Move) (c d : Card) (b : Base)
      (pre post tail : List Move),
      SplitKit.SplitHyp u v ρ F left right c d b pre post tail →
      c.rank.toIdx = 0) :
    SplitPairRungEq := by
  intro u v ρ F left right c d b pre post tail h
  obtain ⟨hF, hSc, -, -⟩ := SplitKit.splitHyp_green h
  exact pin_of_pull_ace hF hSc
    (hb u v ρ F left right c d b pre post tail h)
    (hace u v ρ F left right c d b pre post tail h)

/-! ## §6. The campaign consumes the new residual -/

/-- **THE CAMPAIGN FROM THE ONE-SIDED RESIDUAL.**  `SplitBlock` +
`SplitContainment` + `SplitTwinRungGe` give `Mech.MechanismResidual`. -/
theorem mechanismResidual_of_block_containment_of_ge
    (hb : SplitKit.SplitBlock) (hc : TwinKit.SplitContainment)
    (hg : SplitTwinRungGe) : Mech.MechanismResidual :=
  TwinKit.mechanismResidual_of_block_containment_of_pairRungEq hb hc
    (splitPairRungEq_of_block_of_ge hb hg)

/-- **THE CAMPAIGN FROM THE ONE-SIDED RESIDUAL** (with the choice-free
shortest-play interface). -/
theorem satDifferForkWF_of_block_containment_of_ge
    (hb : SplitKit.SplitBlock) (hc : TwinKit.SplitContainment)
    (hg : SplitTwinRungGe) (hmin : ValleyElim.ShortestPlayExists) :
    SatDifferForkWF :=
  TwinKit.satDifferForkWF_of_block_containment_of_pairRungEq hb hc
    (splitPairRungEq_of_block_of_ge hb hg) hmin

/-- The same in `TwinKit.SplitTwinRungPin` form (the campaign's own spelling). -/
theorem satDifferForkWF_of_block_containment_of_ge_pin
    (hb : SplitKit.SplitBlock) (hc : TwinKit.SplitContainment)
    (hg : SplitTwinRungGe) (hmin : ValleyElim.ShortestPlayExists) :
    SatDifferForkWF := by
  have hpair : SplitPairRungEq := splitPairRungEq_of_block_of_ge hb hg
  exact TwinKit.satDifferForkWF_of_block_containment_of_pin hb hc
    (splitPairRungEq_iff_splitTwinRungPin.mp hpair) hmin

/-! ## §7. Battery -/

#check @PairRungKit.SplitTwinRungGe
#check @PairRungKit.SplitTwinRungLe
#check @PairRungKit.SplitPrePullGap
#check @PairRungKit.SplitPrePullGe
#check @PairRungKit.rungAt_twin_le_of_block
#check @PairRungKit.splitTwinRungLe_of_block
#check @PairRungKit.splitPairRungEq_iff_ge_of_block

#print axioms chop_append_singleton
#print axioms PairRungKit.lastOf_of_fromCard_singleton
#print axioms PairRungKit.pileOfTop_of_fromCard_singleton
#print axioms PairRungKit.pileOfTop_twin_of_block
#print axioms PairRungKit.rungAt_twin_le_of_block
#print axioms PairRungKit.splitPairRungEq_of_block_of_ge
#print axioms PairRungKit.splitTwinRungGe_of_pairRungEq
#print axioms PairRungKit.splitTwinRungLe_of_block
#print axioms PairRungKit.splitPairRungEq_iff_ge_of_block
#print axioms PairRungKit.prePull_twin_rung
#print axioms PairRungKit.prePull_own_rung
#print axioms PairRungKit.prePull_gap_iff_bottom_pin
#print axioms PairRungKit.split_pre_pull_data
#print axioms PairRungKit.splitPrePullGap_of_pairRungEq
#print axioms PairRungKit.pairRungEq_of_splitPrePullGap
#print axioms PairRungKit.splitPairRungEq_iff_prePullGap
#print axioms PairRungKit.splitTwinRungGe_iff_prePullGe
#print axioms PairRungKit.splitPairRungEq_iff_prePullGe_of_block
#print axioms PairRungKit.pin_fails_iff_strictly_behind
#print axioms PairRungKit.pin_of_raise_eq_twin
#print axioms PairRungKit.splitPairRungEq_of_splitTwin
#print axioms PairRungKit.pin_of_pull_ace
#print axioms PairRungKit.splitPairRungEq_of_block_of_pull_ace
#print axioms PairRungKit.mechanismResidual_of_block_containment_of_ge
#print axioms PairRungKit.satDifferForkWF_of_block_containment_of_ge
#print axioms PairRungKit.satDifferForkWF_of_block_containment_of_ge_pin

end PairRungKit
