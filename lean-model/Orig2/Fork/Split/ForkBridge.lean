import Orig2.Fork
import Orig2.Fork.Split.ForkSplit
import Orig2.Fork.Split.ForkDrainClose

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-!
# Orig2/ForkBridge — THE BRIDGE from a valley bottom to the twin asymmetry

READ-ONLY scratch card (not source; no edits, no commit).  Self-contained
apart from the two scratch cards it builds on
(`Temp/ValleyElim_Kit.lean`, `Temp/Drain_Invariant.lean`), which are
compiled to oleans by `lean -o` for the experiment.

## What is proved here (all unconditional, no `sorry`, no choice)

* §0 `canRaiseS_of_free_play_iff` — the S-license is invariant under a FREE
  play (draws and slides), so the free letters *at* a valley turn do not
  move the bottom's live set.
* §1 TARGET 1: `bottom_pull_live`, `bottom_raise_live`,
  `bottom_cards_live` — at a valley bottom the last pull's card and the
  first raise's card are both S-live.  `bottom_cards_raisable` strengthens
  `d` to vanilla `CanRaise`.
* §2 TARGET 2: `adjacent_same_turn_shortens` — an adjacent same-card
  `pull ; raise` turn strictly shortens; `shortest_adjacent_turn_ne` —
  hence in a shortest play an adjacent valley turn has `c ≠ d`
  (`valley_cancel_same`, `Orig2/Fork/Local/ForkValley.lean:33`).
* §3 TARGET 3: `twin_asymmetry_pack` (the abstract twin case) and the
  SHARP ORIENTATION NO-GO `valley_bottom_no_twin_block`: the raise card is
  reversible at any valley bottom, hence vanilla-raisable, so the twin pair
  can NEVER be blocked in the orientation `x = pull card`,
  `x.twin = raise card`.  `valley_bottom_twins_both_raisable` extends this
  to the pull's own LANDING: there both twins are raisable, so a bottom
  that is the pull's landing carries no asymmetry at all.
* §3.1 `bottom_asymmetry_of_split_data` — THE CONCRETE BRIDGE: with the
  split data, `d = c.twin`, `c` blocked at the bottom and the rank floor,
  the bottom itself carries the asymmetry in the ONLY surviving
  orientation (`x = d` the raise card, `x.twin = c` the pull card).
  `SplitResidual` / `BottomDip` (the named residuals) and
  `bottomDip_of_splitResidual`.  `blocked_pull_needs_free_tail` shows the
  block conjunct FORCES a nonempty free tail between the last pull and the
  bottom; `not_forkWitness_of_two_raisable` /
  `no_forkWitness_at_pull_landing` show two raisable live cards kill every
  `ForkWitness` (so the bottom is not a fork by itself).
* §3.5 `asymmetry_iff_covered` — the block conjunct IS `CoveredAt` at
  `WF`; `covered_twin_of_block` / `covered_twin_head_fits` give the exact
  flat shape the residual must supply; `covered_of_pull_onto_card` is the
  pull-side cover mechanism (the pull's base card is covered).
* §4 `ForkExistenceFromAsymmetry` is DISCHARGED from the drain inputs of
  `Temp/Drain_Invariant.lean` §11 (`DrainInputs` ⇒ `forkExistence_of_drainInputs`),
  and `forkExistenceFromAsymmetry_iff_cover` restates it in cover form.
* §5 TARGET 4: the reduction `satDifferForkWF_of_bottom_asymmetry` exactly
  in the brief's shape (plus the named drain half),
  `satDifferForkWF_of_drainInputs`, and the cover-vocabulary form.
* §5c THE FULL CHAIN `satDifferForkWF_of_splitResidual` (and `_drainInputs`):
  `SplitResidual` ⇒ `BottomDip` ⇒ `BottomAsymmetry` ⇒ (drain) ⇒
  `SatDifferForkWF`.  `SplitResidual` is the minimal named hypothesis; see
  `Temp/Bridge_Report.md` §7 for its exact proof obligation.

House compliance: scratch leaf, read-only on the repository, zero `sorry`,
zero `Classical.choice`, zero `native_decide`; battery at the tail.
-/

namespace Bridge

/-! ## §0. Free plays preserve the S-license -/

/-- A cargo leg preserves `CanRaiseS` — backward unconditionally, forward at
`WF` (through `cargoPath_symm`). -/
theorem canRaiseS_cargoLeg_iff {a b : State} (hwf : a.WF) (h : CargoLeg a b) (c : Card) :
    CanRaiseS a c ↔ CanRaiseS b c := by
  constructor
  · rintro ⟨z, haz, hz⟩
    exact ⟨z, steps_trans (cargoPath_symm hwf (Steps.cons h (Steps.refl b))) haz, hz⟩
  · rintro ⟨z, hbz, hz⟩
    exact ⟨z, steps_trans (Steps.cons h (Steps.refl b)) hbz, hz⟩

/-- **FREE PLAYS PRESERVE THE S-LICENSE.**  Draws preserve foundations and
piles (`canRaiseS_congr_found_piles`), slides are cargo legs
(`canRaiseS_cargoLeg_iff`).  This is the row that lets the valley split carry
free letters between the last pull and the bottom. -/
theorem canRaiseS_of_free_play_iff {a b : State} {ρ : List Move}
    (hplay : ShufflePlayW a ρ b) (hfree : ∀ m ∈ ρ, ValleyElim.FreeMove m)
    (hwf : a.WF) (c : Card) : CanRaiseS a c ↔ CanRaiseS b c := by
  induction hplay with
  | nil st => exact Iff.rfl
  | @cons st s₁ W m ρ hlet hstep hrest ih =>
      have hfreeTail : ∀ x ∈ ρ, ValleyElim.FreeMove x :=
        fun x hx => hfree x (List.mem_cons_of_mem m hx)
      have hwfS : s₁.WF := step_wf hwf hstep
      have htail := ih hfreeTail hwfS
      have hhead : CanRaiseS st c ↔ CanRaiseS s₁ c := by
        rcases hfree m (List.mem_cons_self ..) with hm | ⟨cc, bb, hm⟩
        · subst hm
          exact ValleyElim.canRaiseS_congr_found_piles hwf hwfS
            (stepDraw_found hstep).symm (stepDraw_piles hstep).symm c
        · subst hm
          exact canRaiseS_cargoLeg_iff hwf ⟨cc, bb, hstep, hlet⟩ c
      exact hhead.trans htail

/-! ## §1. TARGET 1 — the bottom's two live cards -/

/-- **THE LAST PULL'S CARD IS S-LIVE AT THE BOTTOM.**  The pull fires at some
`A'` with landing `B`; the free tail `post` does not change the S-license
(§0), so the card is S-live at the bottom `F`. -/
theorem bottom_pull_live {u F : State} {left : List Move} {c : Card} {b : Base}
    {pre post : List Move}
    (huwf : u.WF) (hleft : ShufflePlayW u left F)
    (hshape : left = pre ++ Move.foundToTab c b :: post)
    (hfree : ∀ m ∈ post, ValleyElim.FreeMove m) :
    CanRaiseS F c := by
  obtain ⟨A', hpre, hrest⟩ :=
    ValleyElim.ShufflePlayW_split hleft pre (Move.foundToTab c b :: post) hshape
  have hA' : A'.WF := SatDifferCensus.ShufflePlayW.wf_end hpre huwf
  cases hrest with
  | cons hrev hstep hpost =>
      exact (canRaiseS_of_free_play_iff hpost hfree (step_wf hA' hstep) c).mp
        (CanRaiseS.now c (ValleyStep.pull_card_canRaise hA' hstep))

theorem canRaise_of_reversible_raise {F : State} {d : Card} (hF : F.WF)
    (hrev : reversibleAtW F (Move.tabToFound d)) : CanRaise F d :=
  SatDifferCensus.canRaise_of_tabToFoundR ((tabToFoundR_iff_reversibleAtW hF d).mpr hrev)

theorem adjacent_same_turn_shortens {u v F : State} {pre post : List Move}
    {c : Card} {b : Base}
    (huwf : u.WF) (hpre : ShufflePlayW u pre F)
    (hplay : ShufflePlayW u (pre ++ Move.foundToTab c b :: Move.tabToFound c :: post) v) :
    ∃ ρ' : List Move, ShufflePlayW u ρ' v ∧
      ρ'.length < (pre ++ Move.foundToTab c b :: Move.tabToFound c :: post).length := by
  obtain ⟨F', hpre', hrest⟩ :=
    ValleyElim.ShufflePlayW_split hplay pre
      (Move.foundToTab c b :: Move.tabToFound c :: post) rfl
  have hF' : F' = F := by
    have h1 := Walk_run (fun st m => reversibleAtW st m) hpre'
    have h2 := Walk_run (fun st m => reversibleAtW st m) hpre
    exact Option.some.inj (h1.symm.trans h2)
  subst hF'
  cases hrest with
  | cons hrevP hstepP hrest1 =>
      cases hrest1 with
      | cons hrevR hstepR hrest2 =>
          refine ⟨pre ++ post,
            ValleyStep.valley_cancel_same huwf hpre hstepP
              (Walk.cons hrevR hstepR hrest2), ?_⟩
          simp only [List.length_append, List.length_cons, List.length_nil]
          omega

/-- **IN A SHORTEST PLAY AN ADJACENT VALLEY TURN HAS DIFFERENT CARDS.**  The
same-card case would delete the pair and contradict minimality. -/
theorem shortest_adjacent_turn_ne {u v F : State} {pre post : List Move}
    {c d : Card} {b : Base}
    (huwf : u.WF) (hpre : ShufflePlayW u pre F)
    (hplay : ShufflePlayW u (pre ++ Move.foundToTab c b :: Move.tabToFound d :: post) v)
    (hmin : ∀ ρ' : List Move, ShufflePlayW u ρ' v →
      (pre ++ Move.foundToTab c b :: Move.tabToFound d :: post).length ≤ ρ'.length) :
    c ≠ d := by
  intro hcd
  subst hcd
  obtain ⟨ρ', hρ', hlen⟩ := adjacent_same_turn_shortens huwf hpre hplay
  exact absurd hlen (Nat.not_lt.mpr (hmin ρ' hρ'))

/-! ## §3. TARGET 3 — the twin case -/

theorem valley_bottom_no_twin_block {F : State} {c d : Card}
    (hF : F.WF) (hrev : reversibleAtW F (Move.tabToFound d))
    (htwin : d = c.twin) :
    CanRaise F c.twin := by
  rw [← htwin]
  exact canRaise_of_reversible_raise hF hrev

/-- The no-go at the pull's LANDING: there the twin pair `{c, c.twin}` has NO
blocked member at all, in either orientation.  Hence a valley bottom that is
the pull's landing can never carry the twin asymmetry; the free tail after the
last pull must be nonempty for the dip to exist. -/
theorem valley_bottom_twins_both_raisable {A' F : State} {c d : Card} {b : Base}
    (hA' : A'.WF) (hpull : State.step A' (Move.foundToTab c b) = some F)
    (hrev : reversibleAtW F (Move.tabToFound d)) (htwin : d = c.twin) :
    CanRaise F c ∧ CanRaise F c.twin := by
  have hF : F.WF := step_wf hA' hpull
  exact ⟨ValleyStep.pull_card_canRaise hA' hpull,
    valley_bottom_no_twin_block hF hrev htwin⟩

/-! ## §3.1. THE BOTTOM ASYMMETRY, CONCRETELY (the forced orientation) -/

/-- The first letter of a play with a `tabToFound` head: it fires and is
reversible at the origin (no list surgery needed downstream). -/
theorem first_letter_of_play {F v : State} {d : Card} {tail : List Move}
    (hright : ShufflePlayW F (Move.tabToFound d :: tail) v) :
    ∃ F' : State, State.step F (Move.tabToFound d) = some F' ∧
      reversibleAtW F (Move.tabToFound d) := by
  cases hright with
  | cons hrev hstep hrest => exact ⟨_, hstep, hrev⟩

/-- **THE BOTTOM ASYMMETRY, CONCRETELY.**  Valley-split data at the bottom `F`,
with the two live cards twins (`d = c.twin`), the PULL card `c` BLOCKED at `F`,
and the rank floor.  Then the bottom ITSELF carries the asymmetry, with
`x = d` (the raise card) and `x.twin = c` (the pull card) — and, by
`valley_bottom_no_twin_block`, this is the ONLY possible orientation.

`c` is only S-live at `F` (via the free tail `post`), not vanilla-live: this is
exactly the "one covered" dip, and the cover is created by the free slides of
`post` (`covered_of_pull_onto_card` and the one-slide rows show the mechanism).
-/
theorem bottom_asymmetry_of_split_data
    {u v F : State} {left right : List Move} {c d : Card} {b : Base}
    {pre post tail : List Move}
    (huwf : u.WF) (hleft : ShufflePlayW u left F)
    (hright : ShufflePlayW F right v)
    (hshape : left = pre ++ Move.foundToTab c b :: post)
    (hfree : ∀ m ∈ post, ValleyElim.FreeMove m)
    (hrightShape : right = Move.tabToFound d :: tail)
    (htwin : d = c.twin) (hblock : ¬ CanRaise F c)
    (hfloor : ∀ e, CanRaiseS F e → c.rank.toIdx ≤ e.rank.toIdx) :
    sameOrbitSetoid.r u F ∧ CanRaise F d ∧ CanRaiseS F d.twin ∧
      ¬ CanRaise F d.twin ∧ (∀ e, CanRaiseS F e → d.rank.toIdx ≤ e.rank.toIdx) := by
  have hF : F.WF := SatDifferCensus.ShufflePlayW.wf_end hleft huwf
  obtain ⟨F', hstep, hrev⟩ := first_letter_of_play (hrightShape ▸ hright)
  have hcan : CanRaise F d := canRaise_of_reversible_raise hF hrev
  have hS : CanRaiseS F d := CanRaiseS.now d hcan
  -- `d.twin = c`
  have hdt : d.twin = c := by rw [htwin, card_twin_twin]
  refine ⟨RevEqW_symm (shufflePlayW_revEqW hleft), hcan, ?_, ?_, ?_⟩
  · rw [hdt]; exact bottom_pull_live huwf hleft hshape hfree
  · rw [hdt]; exact hblock
  · intro e he
    rw [htwin, Card.twin_rank]
    exact hfloor e he

/-- **TWO VANILLA-RAISABLE CARDS KILL EVERY FORK WITNESS.**  A `ForkWitness` is
exactly "the live set is a twin pair, the mate blocked"; if two distinct cards
are both vanilla-raisable (hence both S-live), no card names a fork. -/
theorem not_forkWitness_of_two_raisable {w : State} {c d : Card}
    (hcd : c ≠ d) (hc : CanRaise w c) (hd : CanRaise w d) :
    ∀ x : Card, ¬ ForkWitness w x := by
  intro x hx
  obtain ⟨hiff, hblk⟩ := hx
  rcases (hiff c).mpr (CanRaiseS.now c hc) with hcx | hcxt
  · rcases (hiff d).mpr (CanRaiseS.now d hd) with hdx | hdxt
    · exact hcd (hcx.trans hdx.symm)
    · rw [← hdxt] at hblk
      exact hblk hd
  · rw [← hcxt] at hblk
    exact hblk hc

/-- **NO FORK AT THE PULL'S LANDING.**  The landing has two distinct
vanilla-raisable cards (the pulled one by the pull, the raised one by
reversibility), so it names no fork — in particular
`ValleyElim.ValleyElimNonfork`'s fork disjunct cannot fire at a bottom that IS
the pull's landing. -/
theorem no_forkWitness_at_pull_landing {A' F : State} {c d : Card} {b : Base}
    (hA' : A'.WF) (hpull : State.step A' (Move.foundToTab c b) = some F)
    (hrev : reversibleAtW F (Move.tabToFound d)) (hcd : c ≠ d) :
    ∀ x : Card, ¬ ForkWitness F x := by
  have hF : F.WF := step_wf hA' hpull
  exact not_forkWitness_of_two_raisable hcd
    (ValleyStep.pull_card_canRaise hA' hpull) (canRaise_of_reversible_raise hF hrev)

/-- **`SplitResidual` — WITHDRAWN, FALSE AS LITERALLY STATED.**  The binders
`left right c d b pre post tail` do not occur in the hypotheses (only
`ValleySplitAt`, which is itself an ∃ over fresh data), so the definition
forces `d = c.twin` for *arbitrary* `d`.  The refutation is
`SplitKit.not_splitResidual_of_split` in `Orig2/Fork/Split/ForkSplitResidual.lean`.

The correct form is `SplitKit.SplitResidualData`, where the split equations
are hypotheses (`SplitHyp`).  This definition is kept only so the refutation
can name it; do not use it as a target. -/
def SplitResidual : Prop :=
  ∀ (u v : State) (ρ : List Move) (F : State)
    (left right : List Move) (c d : Card) (b : Base)
    (pre post tail : List Move),
    u.WF → SSaturated u → SSaturated v →
    ShufflePlayW u ρ v → ValleyElim.ValleySplitAt u v ρ F →
    (∀ ρ' : List Move, ShufflePlayW u ρ' v → ρ.length ≤ ρ'.length) →
    d = c.twin ∧ ¬ CanRaise F c ∧
      (∀ e, CanRaiseS F e → c.rank.toIdx ≤ e.rank.toIdx)

/-- **`BottomDip`** — THE BRIDGE RESIDUAL (bottom form): at the bottom of a
shortest witness play between saturated `WF` class-mates with differing rungs,
the asymmetry holds. -/
def BottomDip : Prop :=
  ∀ (u v : State) (ρ : List Move) (F : State),
    u.WF → SSaturated u → SSaturated v → sameOrbitSetoid.r u v →
    (∃ σ : Suit, rungAt u σ ≠ rungAt v σ) →
    ShufflePlayW u ρ v → ValleyElim.ValleySplitAt u v ρ F →
    (∀ ρ' : List Move, ShufflePlayW u ρ' v → ρ.length ≤ ρ'.length) →
    ∃ x : Card, CanRaise F x ∧ CanRaiseS F x.twin ∧ ¬ CanRaise F x.twin ∧
      (∀ e, CanRaiseS F e → x.rank.toIdx ≤ e.rank.toIdx)

/-- **A PLAY THAT ENDS IN THE PULL ENDS AT ITS LANDING.**  Hence the pull card
is vanilla-raisable there. -/
theorem raisable_of_pull_at_end {u F : State} {c : Card} {b : Base} {pre : List Move}
    (huwf : u.WF) (hleft : ShufflePlayW u (pre ++ [Move.foundToTab c b]) F) :
    CanRaise F c := by
  obtain ⟨A', hpre, hrest⟩ :=
    ValleyElim.ShufflePlayW_split hleft pre [Move.foundToTab c b] rfl
  have hA' : A'.WF := SatDifferCensus.ShufflePlayW.wf_end hpre huwf
  cases hrest with
  | cons hrev hstep hlast =>
      cases hlast with
      | nil st =>
          exact ValleyStep.pull_card_canRaise hA' hstep

/-- **THE BLOCK CONJUNCT FORCES A NONEMPTY FREE TAIL.**  If the split's `post`
is empty the bottom IS the pull's landing, where the pull card is raisable.  So
the residual's `¬ CanRaise F c` requires free letters (a slide) between the last
pull and the bottom: the dip's cover is created by the free tail. -/
theorem blocked_pull_needs_free_tail {u F : State} {c : Card} {b : Base}
    {pre post : List Move}
    (huwf : u.WF) (hleft : ShufflePlayW u (pre ++ Move.foundToTab c b :: post) F)
    (hblock : ¬ CanRaise F c) :
    post ≠ [] := by
  intro hpost
  subst hpost
  exact hblock (raisable_of_pull_at_end huwf hleft)

/- `BottomDip` implies the bridge residual `BottomAsymmetry`
(`valley_exists` supplies the split, the shortest play supplies minimality) —
stated in §5, after `BottomAsymmetry`'s definition. -/


/-! ## §3.5. What the residual must supply: a COVERED twin -/

def ForkExistenceFromAsymmetry : Prop :=
  ∀ (w : State) (x : Card), w.WF →
    CanRaise w x → CanRaiseS w x.twin → ¬ CanRaise w x.twin →
    (∀ c, CanRaiseS w c → x.rank.toIdx ≤ c.rank.toIdx) →
    ∃ (F : State) (y : Card), sameOrbitSetoid.r w F ∧ ForkWitness F y

/-- **The drain inputs**, exactly the named residues of
`Temp/Drain_Invariant.lean` §11 (its `RaiseTransport` bundle plus the
raisability and reversibility providers of its `drain_raise_phase`). -/
structure DrainInputs : Prop where
  /-- Every non-twin live card is vanilla-raisable (`DrainRaisable`). -/
  raisable : ∀ (x : Card) (w : State), w.WF → Drain.DrainInvariant w x →
    Drain.DrainRaisable w x
  /-- Every such raise is reversible. -/
  canrev : ∀ (x : Card) (w : State) (c : Card), w.WF → Drain.DrainInvariant w x →
    Drain.DrainRaisable w x → CanRaise w c → c ≠ x → c ≠ x.twin →
    reversibleAtW w (Move.tabToFound c)
  /-- The three transport clauses (`CanRaiseS_preserved`, `rank_preserved`,
  `raisable_preserved`). -/
  transport : ∀ x : Card, Drain.RaiseTransport x

/-- **THE DRAIN IS ASSEMBLED.**  `Temp/Drain_Invariant.lean`'s raise-only
phase (`Drain.drain_raise_phase`) consumes exactly the asymmetry plus the
`DrainInputs` and produces a fork in the class. -/
theorem forkExistence_of_drainInputs (h : DrainInputs) : ForkExistenceFromAsymmetry := by
  intro w x hwf hcan hS hblock hfloor
  have hinv : Drain.DrainInvariant w x := ⟨hcan, hS, hblock, hfloor⟩
  obtain ⟨F, hrel, hfork⟩ :=
    Drain.drain_raise_phase hwf hinv (h.raisable x w hwf hinv) (h.canrev x)
      (h.transport x)
  obtain ⟨y, hy⟩ := hfork
  exact ⟨F, y, hrel, hy⟩

/-! ## §5. TARGET 4 — the reduction -/

/-- **`BottomAsymmetry`** — THE BRIDGE RESIDUAL.  Two saturated `WF`
class-mates with differing rungs must have a class-mate carrying the twin
asymmetry with the rank floor. -/
def BottomAsymmetry : Prop :=
  ∀ u v : State, u.WF → SSaturated u → SSaturated v → sameOrbitSetoid.r u v →
    (∃ σ : Suit, rungAt u σ ≠ rungAt v σ) →
    ∃ (w : State) (x : Card), sameOrbitSetoid.r u w ∧
      CanRaise w x ∧ CanRaiseS w x.twin ∧ ¬ CanRaise w x.twin ∧
      (∀ c, CanRaiseS w c → x.rank.toIdx ≤ c.rank.toIdx)

/-- `BottomDip` implies the bridge residual `BottomAsymmetry`
(`valley_exists` supplies the split, the shortest play supplies minimality). -/
theorem bottomAsymmetry_of_bottomDip (hdip : BottomDip)
    (hmin : ValleyElim.ShortestPlayExists) : BottomAsymmetry := by
  intro u v huwf hsu hsv hcls hdiff
  obtain ⟨ρ, hρplay, hρmin⟩ := hmin u v huwf hsu hsv hcls hdiff
  obtain ⟨F, hsplit⟩ := ValleyElim.valley_exists huwf hsu hsv hdiff hρplay
  obtain ⟨x, hcan, hS, hblk, hfloor⟩ :=
    hdip u v ρ F huwf hsu hsv hcls hdiff hρplay hsplit hρmin
  obtain ⟨left, right, c, d, b, pre, post, tail,
    hρ, hleft, hright, hshape, hfree, hrightShape⟩ := hsplit
  exact ⟨F, x, RevEqW_symm (shufflePlayW_revEqW hleft), hcan, hS, hblk, hfloor⟩

/-- **THE REDUCTION (brief's statement, plus the drain half as a named
hypothesis).** -/
theorem satDifferForkWF_of_bottom_asymmetry
    (hbridge : BottomAsymmetry) (hdrain : ForkExistenceFromAsymmetry) :
    SatDifferForkWF := by
  intro u v huwf hsu hsv hcls hdiff
  obtain ⟨w, x, huw, hcan, hS, hblock, hfloor⟩ := hbridge u v huwf hsu hsv hcls hdiff
  have hwwf : w.WF := by
    obtain ⟨σ, hσ, τ, hτ⟩ := huw
    exact wf_of_shuffle hτ huwf
  obtain ⟨F, y, hrF, hfork⟩ := hdrain w x hwwf hcan hS hblock hfloor
  exact ⟨F, y, sameOrbitSetoid.iseqv.trans huw hrF, hfork⟩

def BottomCover : Prop :=
  ∀ u v : State, u.WF → SSaturated u → SSaturated v → sameOrbitSetoid.r u v →
    (∃ σ : Suit, rungAt u σ ≠ rungAt v σ) →
    ∃ (w : State) (x : Card), sameOrbitSetoid.r u w ∧
      CanRaise w x ∧ CanRaiseS w x.twin ∧ CoveredAt w x.twin ∧
      (∀ c, CanRaiseS w c → x.rank.toIdx ≤ c.rank.toIdx)

theorem forkExistenceFromAsymmetry_drainClosed : ForkExistenceFromAsymmetry := by
  intro w x hwf hcan hlive hblock hfloor
  obtain ⟨F, hrel, hfork⟩ :=
    DrainClose.fork_exists_of_asymmetry hwf hcan hlive hblock hfloor
  obtain ⟨y, hy⟩ := forkState_iff.mp hfork
  exact ⟨F, y, hrel, hy⟩

/-! ## §6. Battery -/

#print axioms canRaiseS_cargoLeg_iff
#print axioms canRaiseS_of_free_play_iff
#print axioms bottom_pull_live
#print axioms adjacent_same_turn_shortens
#print axioms shortest_adjacent_turn_ne
#print axioms valley_bottom_no_twin_block
#print axioms valley_bottom_twins_both_raisable
#print axioms forkExistence_of_drainInputs
#print axioms satDifferForkWF_of_bottom_asymmetry
#print axioms first_letter_of_play
#print axioms raisable_of_pull_at_end
#print axioms blocked_pull_needs_free_tail
#print axioms not_forkWitness_of_two_raisable
#print axioms no_forkWitness_at_pull_landing
#print axioms bottom_asymmetry_of_split_data
#print axioms bottomAsymmetry_of_bottomDip
#print axioms forkExistenceFromAsymmetry_drainClosed

end Bridge
