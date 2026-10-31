import Orig2.Fork
import Orig2.ForkSplit
import Orig2.ForkDrainClose

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
  (`valley_cancel_same`, `Orig2/ForkValley.lean:33`).
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

/-- The pulled card is not merely S-live: it is VANILLA-raisable at the bottom
(the pull's landing, and the free tail preserves the vanilla license too —
here we use that the card is live and the pull's own landing state is
`found`/`piles`-congruent… instead we keep the sharp statement at the landing).

NOTE: this row is stated at the pull's landing `B`; §2's no-go uses it there. -/
theorem pull_landing_raisable {A' B : State} {c : Card} {b : Base}
    (hA' : A'.WF) (hstep : State.step A' (Move.foundToTab c b) = some B) :
    CanRaise B c :=
  ValleyStep.pull_card_canRaise hA' hstep

/-- **A REVERSIBLE RAISE IS VANILLA-RAISABLE.**  `tabToFoundR` at `WF` is the
reversibility oracle and `canRaise_of_tabToFoundR` reads the license off it. -/
theorem canRaise_of_reversible_raise {F : State} {d : Card} (hF : F.WF)
    (hrev : reversibleAtW F (Move.tabToFound d)) : CanRaise F d :=
  SatDifferCensus.canRaise_of_tabToFoundR ((tabToFoundR_iff_reversibleAtW hF d).mpr hrev)

/-- **THE FIRST RAISE'S CARD IS S-LIVE AT THE BOTTOM** (indeed vanilla-live:
the raise fires at the bottom itself). -/
theorem bottom_raise_live {F v : State} {right tail : List Move} {d : Card}
    (hF : F.WF) (hright : ShufflePlayW F right v)
    (hshape : right = Move.tabToFound d :: tail) :
    CanRaiseS F d := by
  rw [hshape] at hright
  cases hright with
  | cons hrev hstep hrest =>
      exact CanRaiseS.now d (canRaise_of_reversible_raise hF hrev)

/-- **TARGET 1, BOTTOM FORM.**  At a valley split, both live cards are S-live
at the bottom. -/
theorem bottom_cards_live {u v : State} {ρ : List Move} {F : State}
    (huwf : u.WF) (hsplit : ValleyElim.ValleySplitAt u v ρ F) :
    ∃ c d : Card, CanRaiseS F c ∧ CanRaiseS F d := by
  obtain ⟨left, right, c, d, b, pre, post, tail,
    hρ, hleft, hright, hshape, hfree, hrightShape⟩ := hsplit
  have hF : F.WF := SatDifferCensus.ShufflePlayW.wf_end hleft huwf
  exact ⟨c, d, bottom_pull_live huwf hleft hshape hfree,
    bottom_raise_live hF hright hrightShape⟩

/-- **TARGET 1, SHARP FORM.**  At a valley split BOTH live cards are
vanilla-raisable at the bottom: the pull's card by the pull, the raise's card
by reversibility.  (The free tail `post` is not even needed for the raise, and
the pull card is read at its landing then transported — see
`valley_bottom_cards_raisable` for the bottom form.) -/
theorem bottom_cards_raisable {u v : State} {ρ : List Move} {F : State}
    (huwf : u.WF) (hsplit : ValleyElim.ValleySplitAt u v ρ F) :
    ∃ c d : Card, CanRaiseS F c ∧ CanRaiseS F d ∧ CanRaise F d := by
  obtain ⟨left, right, c, d, b, pre, post, tail,
    hρ, hleft, hright, hshape, hfree, hrightShape⟩ := hsplit
  have hF : F.WF := SatDifferCensus.ShufflePlayW.wf_end hleft huwf
  rw [hrightShape] at hright
  cases hright with
  | cons hrev hstep hrest =>
      exact ⟨c, d, bottom_pull_live huwf hleft hshape hfree,
        CanRaiseS.now d (canRaise_of_reversible_raise hF hrev),
        canRaise_of_reversible_raise hF hrev⟩

/-! ## §2. TARGET 2 — a same-card adjacent turn strictly shortens -/

/-- **ADJACENT SAME-CARD TURN SHORTENS.**  A contiguous
`pull c ; raise c` inside a witness play deletes both letters
(`valley_cancel_same`). -/
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

/-- **THE TWIN CASE (packaged).**  If one twin is raisable, the other is
S-live and vanilla-blocked, and nothing S-live sits below the pair's rank,
then the twin asymmetry holds verbatim. -/
theorem twin_asymmetry_pack {w : State} {x : Card}
    (hcan : CanRaise w x) (hS : CanRaiseS w x.twin) (hblock : ¬ CanRaise w x.twin)
    (hfloor : ∀ c, CanRaiseS w c → x.rank.toIdx ≤ c.rank.toIdx) :
    CanRaise w x ∧ CanRaiseS w x.twin ∧ ¬ CanRaise w x.twin ∧
      (∀ c, CanRaiseS w c → x.rank.toIdx ≤ c.rank.toIdx) :=
  ⟨hcan, hS, hblock, hfloor⟩

/-- **THE ORIENTATION NO-GO.**  At ANY valley bottom the raise card `d` is
reversible there, hence vanilla-raisable: if `d = c.twin` then `c.twin` is
raisable.  So the asymmetry can NEVER be oriented `x = c` (pull card),
`x.twin = d` (raise card).

The OTHER orientation (`x = d`, `x.twin = c`) survives exactly when the pull
card `c` is blocked at the bottom — which is impossible at the pull's own
LANDING (`valley_bottom_twins_both_raisable`), so the surviving dip needs a
NONEMPTY free tail between the last pull and the bottom. -/
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

/-- **`SplitResidual`** — THE FINEST NAMED RESIDUAL.  At the canonical valley
split of a SHORTEST witness play between saturated `WF` class-mates with
differing rungs: the last pull's card `c` and the first raise's card `d` are
twins, the pull card is blocked at the bottom, and nothing S-live sits below
the pair's rank there.

(Needed only for the split `valley_exists` returns; quantified over all splits
here, which is a harmless strengthening.) -/
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

/-- `SplitResidual` implies `BottomDip` (through the concrete orientation
theorem above). -/
theorem bottomDip_of_splitResidual (h : SplitResidual) : BottomDip := by
  intro u v ρ F huwf hsu hsv hcls hdiff hplay hsplit hmin
  obtain ⟨left, right, c, d, b, pre, post, tail,
    hρ, hleft, hright, hshape, hfree, hrightShape⟩ := hsplit
  obtain ⟨htwin, hblock, hfloor⟩ :=
    h u v ρ F left right c d b pre post tail huwf hsu hsv hplay
      ⟨left, right, c, d, b, pre, post, tail,
        hρ, hleft, hright, hshape, hfree, hrightShape⟩ hmin
  obtain ⟨-, hcan, hS, hblk, hfloor'⟩ :=
    bottom_asymmetry_of_split_data huwf hleft hright hshape hfree hrightShape
      htwin hblock hfloor
  exact ⟨d, hcan, hS, hblk, hfloor'⟩

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

/-- **THE ASYMMETRY IN COVER VOCABULARY.**  At `WF`, "S-live but
vanilla-blocked" is EXACTLY `CoveredAt` (the flat dichotomy per card,
`Orig2/ForkCriticalPair.lean:401` and `:451`).  So the bridge residual can be
stated with the chart's cover read (`seatOf`/`CoveredAt`,
`Orig2/Vocab.lean:889,917`) instead of the negated license. -/
theorem asymmetry_iff_covered {w : State} {x : Card} (hwf : w.WF) :
    (CanRaise w x ∧ CanRaiseS w x.twin ∧ ¬ CanRaise w x.twin ∧
        (∀ c, CanRaiseS w c → x.rank.toIdx ≤ c.rank.toIdx))
      ↔ (CanRaise w x ∧ CanRaiseS w x.twin ∧ CoveredAt w x.twin ∧
        (∀ c, CanRaiseS w c → x.rank.toIdx ≤ c.rank.toIdx)) := by
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨h1, h2, covered_of_live_not_canRaise hwf h2 h3, h4⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨h1, h2, not_canRaise_of_covered hwf h3, h4⟩

/-- **THE FORK FORM OF THE TWIN CASE.**  A live twin pair with the mate
covered IS a fork (`forkWitness_iff_covered`,
`Orig2/ForkCriticalPair.lean:465`). -/
theorem fork_of_twin_live_covered {w : State} {x : Card} (hwf : w.WF)
    (hlive : TwinLivePair w x) (hcov : CoveredAt w x.twin) : ForkWitness w x :=
  (forkWitness_iff_covered hwf rfl hlive ((hlive x.twin).mpr (Or.inr rfl))).mpr hcov

/-- **THE MECHANISM: A PULL ONTO A CARD COVERS IT.**  If the pull's base is
`inr e` (the card `e`), the pulled card lands directly ON `e`, so `e` is
covered at the landing (`seatOf_foundToTab_mover`,
`Orig2/TwinSpliceComm.lean:810`).  This is the only way a *down*-leg letter
can create the cover the asymmetry needs, and it pins the residual to the
pull's BASE: the dip's covered card is the base card of the last pull. -/
theorem covered_of_pull_onto_card {A' B : State} {c e : Card}
    (hA' : A'.WF) (hstep : State.step A' (Move.foundToTab c (Sum.inr e)) = some B) :
    CoveredAt B e :=
  ⟨c, TwinSpliceComm.seatOf_foundToTab_mover hA' hstep⟩

/-- The same row in `seatOf` form. -/
theorem seatOf_mover_of_pull {A' B : State} {c : Card} {base : Base}
    (hA' : A'.WF) (hstep : State.step A' (Move.foundToTab c base) = some B) :
    seatOf B c = some base :=
  TwinSpliceComm.seatOf_foundToTab_mover hA' hstep

/-- **A BLOCKED S-LIVE TWIN IS COVERED.**  Unfolding the asymmetry's two
conjuncts through the flat characterization (`ForkOneSlide`): the blocked
twin is next-up and S-live, so it is not the top of its pile, i.e. a NONEMPTY
run sits above it.  This is the exact shape a `BottomAsymmetry` producer has
to exhibit. -/
theorem covered_twin_of_block {w : State} {x : Card} (hwf : w.WF)
    (hS : CanRaiseS w x.twin) (hblock : ¬ CanRaise w x.twin) :
    ∃ (a : Anchor) (bs : List Card) (u1 : Card) (rest : List Card),
      (w.piles a).faceUp = bs ++ x.twin :: u1 :: rest := by
  obtain ⟨hnext, a, bs, run, hshape, hseat, hdisj⟩ :=
    SafePathFiber.twin_flat_data hwf hS
  have hrun : run ≠ [] := SafePathFiber.twin_run_ne_nil hwf hnext hblock hshape hseat
  cases run with
  | nil => exact absurd rfl hrun
  | cons u1 rest => exact ⟨a, bs, u1, rest, hshape⟩

/-- The cover's head is one rank below the pair: it fits the blocked twin
(`runOK_adjacent_fit`, as in `Orig2/ForkOneSlide.lean:128`), so the residual
is a genuine one-slide statement.  Stated as the corollary the campaign
needs: the head `u1` sits on the twin. -/
theorem covered_twin_head_fits {w : State} {x : Card} (hwf : w.WF)
    (hS : CanRaiseS w x.twin) (hblock : ¬ CanRaise w x.twin) :
    ∃ (a : Anchor) (bs : List Card) (u1 : Card) (rest : List Card),
      (w.piles a).faceUp = bs ++ x.twin :: u1 :: rest ∧ canSitOn u1 x.twin = true := by
  obtain ⟨a, bs, u1, rest, hshape⟩ := covered_twin_of_block hwf hS hblock
  refine ⟨a, bs, u1, rest, hshape, ?_⟩
  have hok : runOK (bs ++ x.twin :: u1 :: rest) = true := by
    rw [← hshape]; exact hwf.2.1 a
  exact SeedKit.runOK_adjacent_fit x.twin u1 bs rest hok

/-! ## §4. The drain half of the bridge -/

/-- **`ForkExistenceFromAsymmetry`** — the drain half: any state carrying the
twin asymmetry (with the rank floor) has a FORK in its class.  Named here, and
discharged in `forkExistence_of_drainInputs` from the `Drain_Invariant` inputs. -/
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

/-- **THE REDUCTION FROM THE DRAIN INPUTS** — no named drain hypothesis
beyond the `DrainInputs` bundle of `Temp/Drain_Invariant.lean`. -/
theorem satDifferForkWF_of_drainInputs (hbridge : BottomAsymmetry) (hin : DrainInputs) :
    SatDifferForkWF :=
  satDifferForkWF_of_bottom_asymmetry hbridge (forkExistence_of_drainInputs hin)

/-! ## §5b. The residual in cover vocabulary (the concrete obligation) -/

/-- **`BottomCover`** — `BottomAsymmetry` with the blocked conjunct written as
`CoveredAt`.  This is the form a campaign worker can discharge from the chart:
exhibit a class-mate of the valley bottom where one twin of a live pair is
COVERED (a card sits directly on it) and nothing is live below the pair. -/
def BottomCover : Prop :=
  ∀ u v : State, u.WF → SSaturated u → SSaturated v → sameOrbitSetoid.r u v →
    (∃ σ : Suit, rungAt u σ ≠ rungAt v σ) →
    ∃ (w : State) (x : Card), sameOrbitSetoid.r u w ∧
      CanRaise w x ∧ CanRaiseS w x.twin ∧ CoveredAt w x.twin ∧
      (∀ c, CanRaiseS w c → x.rank.toIdx ≤ c.rank.toIdx)

theorem bottomAsymmetry_of_bottomCover (h : BottomCover) : BottomAsymmetry := by
  intro u v huwf hsu hsv hcls hdiff
  obtain ⟨w, x, huw, h1, h2, h3, h4⟩ := h u v huwf hsu hsv hcls hdiff
  have hwwf : w.WF := by
    obtain ⟨σ, hσ, τ, hτ⟩ := huw
    exact wf_of_shuffle hτ huwf
  exact ⟨w, x, huw, (asymmetry_iff_covered hwwf).mpr ⟨h1, h2, h3, h4⟩⟩

/-- The reduction from the COVER residual. -/
theorem satDifferForkWF_of_bottomCover (hbridge : BottomCover)
    (hdrain : ForkExistenceFromAsymmetry) : SatDifferForkWF :=
  satDifferForkWF_of_bottom_asymmetry (bottomAsymmetry_of_bottomCover hbridge) hdrain

/-- The drain half in cover vocabulary. -/
def ForkExistenceFromCover : Prop :=
  ∀ (w : State) (x : Card), w.WF → CanRaise w x → CanRaiseS w x.twin →
    CoveredAt w x.twin →
    (∀ c, CanRaiseS w c → x.rank.toIdx ≤ c.rank.toIdx) →
    ∃ (F : State) (y : Card), sameOrbitSetoid.r w F ∧ ForkWitness F y

theorem forkExistenceFromAsymmetry_iff_cover :
    ForkExistenceFromAsymmetry ↔ ForkExistenceFromCover := by
  constructor
  · intro h w x hwf h1 h2 h3 h4
    obtain ⟨a1, a2, a3, a4⟩ := (asymmetry_iff_covered hwf).mpr ⟨h1, h2, h3, h4⟩
    exact h w x hwf a1 a2 a3 a4
  · intro h w x hwf h1 h2 h3 h4
    obtain ⟨a1, a2, a3, a4⟩ := (asymmetry_iff_covered hwf).mp ⟨h1, h2, h3, h4⟩
    exact h w x hwf a1 a2 a3 a4

/-! ## §5c. The full chain from the finest residual -/

/-- **THE FULL CHAIN.**  `SplitResidual` (twins + blocked pull + rank floor at
the canonical shortest-play valley bottom) plus shortest-play existence and the
drain half gives `SatDifferForkWF`. -/
theorem satDifferForkWF_of_splitResidual (h : SplitResidual)
    (hmin : ValleyElim.ShortestPlayExists) (hdrain : ForkExistenceFromAsymmetry) :
    SatDifferForkWF :=
  satDifferForkWF_of_bottom_asymmetry
    (bottomAsymmetry_of_bottomDip (bottomDip_of_splitResidual h) hmin) hdrain

/-- The same chain with the drain discharged from `DrainInputs`. -/
theorem satDifferForkWF_of_splitResidual_drainInputs (h : SplitResidual)
    (hmin : ValleyElim.ShortestPlayExists) (hin : DrainInputs) :
    SatDifferForkWF :=
  satDifferForkWF_of_splitResidual h hmin (forkExistence_of_drainInputs hin)

/-- **THE CAMPAIGN TARGET, DRAIN DISCHARGED.**  The drain half is
`DrainClose.fork_exists_of_asymmetry`; the only remaining hypotheses are the
bridge `SplitResidual` and the choice-free shortest-play interface. -/
theorem forkExistenceFromAsymmetry_drainClosed : ForkExistenceFromAsymmetry := by
  intro w x hwf hcan hlive hblock hfloor
  obtain ⟨F, hrel, hfork⟩ :=
    DrainClose.fork_exists_of_asymmetry hwf hcan hlive hblock hfloor
  obtain ⟨y, hy⟩ := forkState_iff.mp hfork
  exact ⟨F, y, hrel, hy⟩

theorem satDifferForkWF_of_splitResidual_drainClosed
    (h : SplitResidual) (hmin : ValleyElim.ShortestPlayExists) :
    SatDifferForkWF :=
  satDifferForkWF_of_splitResidual h hmin forkExistenceFromAsymmetry_drainClosed

/-! ## §6. Battery -/

#print axioms canRaiseS_cargoLeg_iff
#print axioms canRaiseS_of_free_play_iff
#print axioms bottom_pull_live
#print axioms bottom_raise_live
#print axioms bottom_cards_live
#print axioms bottom_cards_raisable
#print axioms adjacent_same_turn_shortens
#print axioms shortest_adjacent_turn_ne
#print axioms twin_asymmetry_pack
#print axioms valley_bottom_no_twin_block
#print axioms valley_bottom_twins_both_raisable
#print axioms covered_of_pull_onto_card
#print axioms seatOf_mover_of_pull
#print axioms covered_twin_of_block
#print axioms covered_twin_head_fits
#print axioms asymmetry_iff_covered
#print axioms fork_of_twin_live_covered
#print axioms forkExistence_of_drainInputs
#print axioms satDifferForkWF_of_bottom_asymmetry
#print axioms satDifferForkWF_of_drainInputs
#print axioms bottomAsymmetry_of_bottomCover
#print axioms satDifferForkWF_of_bottomCover
#print axioms forkExistenceFromAsymmetry_iff_cover
#print axioms first_letter_of_play
#print axioms raisable_of_pull_at_end
#print axioms blocked_pull_needs_free_tail
#print axioms not_forkWitness_of_two_raisable
#print axioms no_forkWitness_at_pull_landing
#print axioms bottom_asymmetry_of_split_data
#print axioms bottomDip_of_splitResidual
#print axioms bottomAsymmetry_of_bottomDip
#print axioms satDifferForkWF_of_splitResidual
#print axioms satDifferForkWF_of_splitResidual_drainInputs
#print axioms forkExistenceFromAsymmetry_drainClosed
#print axioms satDifferForkWF_of_splitResidual_drainClosed

end Bridge
