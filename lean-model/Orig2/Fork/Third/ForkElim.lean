import Orig2.Fork.Split.ForkDrainClose
import Orig2.Fork.Local.ForkNormalize
import Orig2.Fork.Split.ForkTailCover
import Orig2.Fork.Split.ForkLanding

/-! ## Merged from `ForkNormalizeTail.lean` (2026-11-02) -/

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-!
# Orig2/ForkNormalizeTail — the empty-tail and third-suit consequences

PROMOTED from `Temp/Norm_Tail.lean` (2026-11-01).  Two reductions, both keyed
to the same bubble kit:

1. **`NoEmptyTail`** (`BlockKit`): the empty-tail split is
   `pre ++ [pull c ; raise d] ++ tail`; it has no partner `pull d` before the
   turn and no partner `raise c` after it.  The normalizer assumes both
   exist, so the exact extra input is the *existence* half

   `EmptyTailPartners`, not the reordering.  Given it, the normalizer's
   strict shortening contradicts the split's minimality.

2. **`LandingThirdSuitFree`** (`Landing`): the residual is the *same-card*
   bracket `pull z ; … ; raise z`, not the crossing block `c ≠ d`.  The
   normalizer therefore does NOT imply it.  The exact extra inputs are
   `ThirdSuitBracketData` (existence of the bracket letters + slide-free
   interior + the swapped-order plays); `bubble_raise_left` then produces the
   commuted play `ThirdSuitBracket` wants, and `landingThirdSuitFree_of_bracket`
   finishes.
-/

open ValleyElim
open CommuteStep

namespace BlockKit

open SplitKit

/-- **THE EXACT EMPTY-TAIL EXISTENCE GAP.**  The normalizer's decomposition
requires the partner `pull d bd` before the turn and the partner
`raise c` after it.  In the empty-tail split (`post = []`) nothing in
`SplitHyp` supplies them. -/
def EmptyTailPartners : Prop :=
  ∀ (u v : State) (ρ : List Move) (F : State)
    (left right : List Move) (c d : Card) (b : Base)
    (pre post tail : List Move),
    SplitHyp u v ρ F left right c d b pre post tail → post = [] →
    ∃ (α β γ δ ε : List Move) (bd : Base),
      ρ = α ++ [Move.foundToTab d bd] ++ β ++
          [Move.foundToTab c b, Move.tabToFound d] ++ γ ++
          [Move.tabToFound c] ++ δ ++ ε

/-- **`NoEmptyTail` FROM PARTNERS + NORMALIZER.**  If the empty-tail split
supplies the two partner letters, the normalizer produces a strictly shorter
play, contradicting minimality. -/
theorem noEmptyTail_of_partners_normalizer
    (hpart : EmptyTailPartners)
    (hnorm : LocatorCorrected.CrossingBracketNormalizer) : NoEmptyTail := by
  intro u v ρ F left right c d b pre post tail hsplit hpost
  have hcd : c ≠ d := emptyTail_turn_ne hsplit hpost
  have hsuit : c.suit ≠ d.suit := emptyTail_suit_ne hsplit hpost
  obtain ⟨α, β, γ, δ, ε, bd, hdecomp⟩ :=
    hpart u v ρ F left right c d b pre post tail hsplit hpost
  obtain ⟨huwf, -, -, hplay, -, hmin, -, hleft, -, -, -, -⟩ := hsplit
  obtain ⟨ρ'', hplay'', hlt⟩ :=
    LocatorCorrected.normalizer_shortens (tail := tail) (right := right)
      hnorm huwf hplay hdecomp hleft hcd hsuit
  exact absurd hlt (Nat.not_lt.mpr (hmin ρ'' hplay''))

end BlockKit

namespace Landing

/-- **THE EXACT THIRD-SUIT BRACKET GAP.**  A third-suit live card at the pull
landing must yield the same-card bracket letters `pull z ; … ; raise z`, with
a slide-free interior and the swapped-order plays `raise z` before each
interior letter.  `Bubble.bubble_raise_left` then converts this into the
commuted play of `ThirdSuitBracket`. -/
def ThirdSuitBracketData : Prop :=
  ∀ (u v : State) (ρ : List Move) (F : State)
    (left right : List Move) (c d : Card) (b : Base)
    (pre post tail : List Move),
    SplitKit.SplitHyp u v ρ F left right c d b pre post tail →
    ∀ (A' B : State), ShufflePlayW u pre A' →
      State.step A' (Move.foundToTab c b) = some B →
      ∀ e : Card, CanRaiseS B e →
        e.suit ≠ c.suit → e.suit ≠ c.twin.suit →
        ∃ (α γ β : List Move) (z : Card) (bz : Base) (P Q : State),
          ρ = α ++ Move.foundToTab z bz :: γ ++ Move.tabToFound z :: β ∧
          ShufflePlayW u α P ∧
          State.step P (Move.foundToTab z bz) = some Q ∧
          (∀ m ∈ γ, NoSlide m) ∧
          (∀ (pre' : List Move) (mid : State) (q : Move) (post' : List Move),
            pre' ++ q :: post' = γ → ShufflePlayW Q pre' mid →
            ∃ e', ShufflePlayW mid [Move.tabToFound z, q] e')

/-- **THE BRACKET DATA PRODUCES THE COMMUTED PLAY.**  This is
`Bubble.bubble_raise_left` applied at the bracket's pull landing. -/
theorem thirdSuitBracket_of_data (hd : ThirdSuitBracketData) : ThirdSuitBracket := by
  intro u v ρ F left right c d b pre post tail hsplit A' B hpre hstep e he h1 h2
  obtain ⟨α, γ, β, z, bz, P, Q, hρ, hα, hstepP, hnslγ, hbub⟩ :=
    hd u v ρ F left right c d b pre post tail hsplit A' B hpre hstep e he h1 h2
  obtain ⟨huwf, -, -, hplay, -, -, -, -, -, -, -, -⟩ := hsplit
  -- the pull `z` is reversible at `P`: its raise-back is the inverse step
  have hPwf : P.WF := SatDifferCensus.ShufflePlayW.wf_end hα huwf
  have hQwf : Q.WF := step_wf hPwf hstepP
  have hback : State.step Q (Move.tabToFound z) = some P :=
    step_tabToFound_of_foundToTab hPwf hstepP
  have hrevP : reversibleAtW P (Move.foundToTab z bz) :=
    ⟨Q, [Move.tabToFound z], hstepP, by simp [State.run, hback]⟩
  -- split the given play at the prefix ending with the pull
  have hρ' : ρ = (α ++ [Move.foundToTab z bz]) ++
      (γ ++ Move.tabToFound z :: β) := by
    simpa only [List.cons_append, List.append_assoc, List.nil_append] using hρ
  obtain ⟨Q', hpre', hrest'⟩ :=
    ShufflePlayW_split hplay (α ++ [Move.foundToTab z bz])
      (γ ++ Move.tabToFound z :: β) hρ'
  have hQ'eq : Q' = Q := by
    have hsame : ShufflePlayW u (α ++ [Move.foundToTab z bz]) Q :=
      ShufflePlayW_append hα (Walk.cons hrevP hstepP (Walk.nil Q))
    exact Option.some.inj ((Walk_run _ hpre').symm.trans (Walk_run _ hsame))
  have hrestQ : ShufflePlayW Q (γ ++ Move.tabToFound z :: β) v := by
    rw [← hQ'eq]
    exact hrest'
  have hbubbled : ShufflePlayW Q (Move.tabToFound z :: γ ++ β) v :=
    Bubble.bubble_raise_left γ hQwf hnslγ (Bubble.noSlide_tabToFound z) hrestQ hbub
  have hcons : ShufflePlayW P
      (Move.foundToTab z bz :: Move.tabToFound z :: (γ ++ β)) v :=
    Walk.cons hrevP hstepP hbubbled
  exact ⟨α, γ, β, z, bz, P, Q, hρ, ShufflePlayW_append hα hcons, hα, hstepP⟩

/-- **`LandingThirdSuitFree` FROM THE BRACKET DATA.** -/
theorem landingThirdSuitFree_of_data (hd : ThirdSuitBracketData) :
    LandingThirdSuitFree :=
  landingThirdSuitFree_of_bracket (thirdSuitBracket_of_data hd)

end Landing

#print axioms BlockKit.noEmptyTail_of_partners_normalizer
#print axioms Landing.thirdSuitBracket_of_data
#print axioms Landing.landingThirdSuitFree_of_data


set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-!
# Orig2/ForkElim — the same-card bracket route to `ValleyElimNonfork`

READ-ONLY scratch card (no source touched, no commit).  Zero `sorry`, zero
`Classical.choice`, no `native_decide`; the axiom battery is at the tail.

## What is proved here

1. **`bracket_delete_of_commuted`** — the play-level deletion of a same-card
   bracket `pull z ; γ ; raise z` from the *commuted play*: if `raise z` can be
   moved to sit directly behind the pull (i.e. `raise z :: γ ++ β` is a play
   from the pull's landing), then `α ++ γ ++ β` is a strictly shorter witness
   play.  No slide restriction on the interior `γ`: this is
   `valley_cancel_same` on the commuted word plus the length arithmetic.
   `bubble_bracket_shortens` is the special case where `γ` is slide-free and
   the commutation is produced by `Bubble.bubble_raise_left`.

2. **`samecard_turn_nil_shortens`** — an unconditional corner of
   `ValleyElim.ValleyElimNonfork`: a valley split with `post = []` and
   `c = d` strictly shortens (adjacent `pull c ; raise c`).

3. **`samecard_raiseTurn_shortens`** — an unconditional W1 corner: `post = []`,
   `c ≠ d`, and the pull card is re-raised immediately after the turn
   (`right = raise d ; raise c :: rest`).  `raise d` was already legal before
   the pull (`BlockKit.canRaise_of_pull_of_ne`), and the raise/raise square
   identifies the two landings (`ValleyElim.raise_raise_square_norev`); the
   `pull c ; raise c` pair deletes.

4. **`post_nil_no_fork`** — the fork disjunct is *impossible* when `post = []`
   and `c ≠ d` (`Bridge.no_forkWitness_at_pull_landing`).  Hence that corner
   can only be discharged by a shortening whose bracket sits elsewhere in `ρ`:
   the turn itself supplies no same-card pair.

5. **`TurnCommutes` / `turnCommutes_shortens`** — the whole `c = d` branch of
   the elimination follows from one explicit commutation premise (the
   minimality-free form of `LiveKit.PostCommutesRaise`).

6. **`NonforkBracketElim`** — the exact residual left by the probe
   (`Temp/SplitProbe_Report.md` §4): every valley split either already carries
   a fork at its bottom, or the play has a same-card bracket whose raise
   commutes left across the interior.  The residual is a *disjunction* so that
   the reduction to `ValleyElimNonfork` stays constructive (`by_cases` on an
   existential would import `Classical.choice`).

7. **`valleyElimNonfork_of_nonforkBracket`** — `NonforkBracketElim →
   ValleyElimNonfork`.  The fork branch is the identity; the bracket branch is
   (1).

The residual's second disjunct is strictly stronger than the target's second
disjunct, so this is a real reduction: what remains is the geometric existence
of the commuted bracket (the probe's W1/W2 deletion), not the deletion itself.
-/

namespace Elim

open ValleyElim
open CommuteStep

/-- The step of a one-letter witness play. -/
theorem step_of_singleton {A B : State} {m : Move}
    (h : ShufflePlayW A [m] B) : State.step A m = some B := by
  have hrun : A.run [m] = some B := Walk_run _ h
  cases hs : State.step A m with
  | none =>
      rw [show A.run [m] = none by simp [State.run, hs]] at hrun
      cases hrun
  | some B' =>
      have hB' : B' = B := by
        have h' : A.run [m] = some B' := by simp [State.run, hs]
        exact Option.some.inj (h'.symm.trans hrun)
      rw [hB']

/-! ## §1. Play-level same-card bracket deletion -/

/-- **BRACKET DELETION FROM THE COMMUTED PLAY.**  If

```text
ρ = α ++ pull z bz :: γ ++ raise z :: β
```

and the raise can be moved to sit directly behind the pull, i.e.
`raise z :: γ ++ β` is a witness play from the pull's landing `Q`, then the two
bracket letters delete and `α ++ γ ++ β` is a strictly shorter witness play
with the same endpoints.

No slide restriction is imposed on `γ`: the deletion itself is
`valley_cancel_same`, which only needs the commuted word.  The geometric
content (walking `raise z` left across `γ`) is isolated in the hypothesis
`hcomm`. -/
theorem bracket_delete_of_commuted
    {u v : State} {ρ α γ β : List Move}
    {z : Card} {bz : Base} {P Q : State}
    (huwf : u.WF)
    (hplay : ShufflePlayW u ρ v)
    (hρ : ρ = α ++ Move.foundToTab z bz :: γ ++ Move.tabToFound z :: β)
    (hα : ShufflePlayW u α P)
    (hstep : State.step P (Move.foundToTab z bz) = some Q)
    (hcomm : ShufflePlayW Q (Move.tabToFound z :: γ ++ β) v) :
    ∃ ρ' : List Move, ShufflePlayW u ρ' v ∧ ρ'.length < ρ.length := by
  have hdel : ShufflePlayW u (α ++ γ ++ β) v := by
    simpa only [List.append_assoc] using
      (ValleyElim.valley_cancel_same (A := u) (A' := P) (B := Q) (C := v)
        (ρ₁ := α) (ρ₂ := γ ++ β) (c := z) (b := bz) huwf hα hstep hcomm)
  refine ⟨α ++ γ ++ β, hdel, ?_⟩
  rw [hρ]
  simp only [List.length_append, List.length_cons]
  omega

/-- **SLIDE-FREE BRACKET DATA SHORTENS.**  The special case where the interior
`γ` is slide-free and the commutation is supplied by `bubble_raise_left` (the
explicit per-adjacent-pair swapped-order certificate `hbub`).  This is the
`bracket_delete_at` route, stated with the play already split at the bracket. -/
theorem bubble_bracket_shortens
    {u v : State} {ρ α γ β : List Move}
    {z : Card} {bz : Base} {P Q : State}
    (huwf : u.WF)
    (hplay : ShufflePlayW u ρ v)
    (hρ : ρ = α ++ Move.foundToTab z bz :: γ ++ Move.tabToFound z :: β)
    (hα : ShufflePlayW u α P)
    (hstep : State.step P (Move.foundToTab z bz) = some Q)
    (hbr : ShufflePlayW Q (γ ++ Move.tabToFound z :: β) v)
    (hnsl : ∀ m ∈ γ, NoSlide m)
    (hbub : ∀ (pre : List Move) (mid : State) (q : Move) (post : List Move),
        pre ++ q :: post = γ → ShufflePlayW Q pre mid →
        ∃ e, ShufflePlayW mid [Move.tabToFound z, q] e) :
    ∃ ρ' : List Move, ShufflePlayW u ρ' v ∧ ρ'.length < ρ.length := by
  have hPwf : P.WF := SatDifferCensus.ShufflePlayW.wf_end hα huwf
  have hQwf : Q.WF := step_wf hPwf hstep
  have hcomm : ShufflePlayW Q (Move.tabToFound z :: γ ++ β) v :=
    Bubble.bubble_raise_left γ hQwf hnsl (Bubble.noSlide_tabToFound z) hbr hbub
  exact bracket_delete_of_commuted huwf hplay hρ hα hstep hcomm

/-! ## §2. The empty-tail same-card turn -/

/-- **UNCONDITIONAL CORNER: `post = []` and `c = d`.**  A valley split whose
turn is the adjacent same-card pair `pull c ; raise c` strictly shortens.
(Deletion is `ValleyStep.valley_cancel_same`.) -/
theorem samecard_turn_nil_shortens
    {u v F : State} {ρ left right pre post tail : List Move}
    {c d : Card} {b : Base}
    (huwf : u.WF)
    (hρ : ρ = left ++ right)
    (hleft : ShufflePlayW u left F)
    (hright : ShufflePlayW F right v)
    (hshape : left = pre ++ Move.foundToTab c b :: post)
    (hrightShape : right = Move.tabToFound d :: tail)
    (hpost : post = []) (hcd : c = d) :
    ∃ ρ' : List Move, ShufflePlayW u ρ' v ∧ ρ'.length < ρ.length := by
  subst hpost
  subst hcd
  have hplay : ShufflePlayW u ρ v := by
    rw [hρ]; exact ShufflePlayW_append hleft hright
  -- the prefix of `ρ` before the turn: `pre ++ pull c b`
  have hdec : ρ = (pre ++ [Move.foundToTab c b]) ++
      (Move.tabToFound c :: tail) := by
    rw [hρ, hshape, hrightShape]
  obtain ⟨Q, hpreFull, hrest⟩ := ShufflePlayW_split hplay _ _ hdec
  -- the left leg's pull lands at `F`
  obtain ⟨P0, hpre0, hlast0⟩ :=
    ShufflePlayW_split hleft pre [Move.foundToTab c b] hshape
  have hstep0 : State.step P0 (Move.foundToTab c b) = some F :=
    step_of_singleton hlast0
  -- the same prefix inside `ρ` lands at `Q`
  obtain ⟨P1, hpre1, hlast1⟩ :=
    ShufflePlayW_split hpreFull pre [Move.foundToTab c b] rfl
  have hP : P1 = P0 := by
    have h1 := Walk_run (fun st m => reversibleAtW st m) hpre1
    have h2 := Walk_run (fun st m => reversibleAtW st m) hpre0
    exact Option.some.inj (h1.symm.trans h2)
  have hlast1' : ShufflePlayW P0 [Move.foundToTab c b] Q := by
    rw [← hP]; exact hlast1
  have hstep1 : State.step P0 (Move.foundToTab c b) = some Q :=
    step_of_singleton hlast1'
  have hQF : Q = F := Option.some.inj (hstep1.symm.trans hstep0)
  rw [hQF] at hrest
  refine ⟨pre ++ tail,
    ValleyElim.valley_cancel_same (A := u) (A' := P0) (B := F) (C := v)
      (ρ₁ := pre) (ρ₂ := tail) (c := c) (b := b) huwf hpre0 hstep0 hrest, ?_⟩
  rw [hρ, hshape, hrightShape]
  simp only [List.length_append, List.length_cons, List.length_nil]
  omega

/-- **UNCONDITIONAL CORNER: `post = []` AND THE PULL CARD IS RE-RAISED AT
ONCE.**  If the empty-tail turn `pull c ; raise d` (`c ≠ d`) is followed
*immediately* by `raise c`, then the pull is undone by its own raise across the
turn: `raise d` was already legal before the pull
(`BlockKit.canRaise_of_pull_of_ne`), and the raise/raise square identifies the
two landings (`ValleyElim.raise_raise_square_norev`).  The play strictly
shortens by deleting `pull c ; raise c`.

This is the W1 deletion shape (`Temp/SplitProbe_Report.md` §4.3) at the empty
tail: delete the `c` pair rather than the crossing turn. -/
theorem samecard_raiseTurn_shortens
    {u v F : State} {ρ left right pre post tail rest : List Move}
    {c d : Card} {b : Base}
    (huwf : u.WF)
    (hρ : ρ = left ++ right)
    (hleft : ShufflePlayW u left F)
    (hright : ShufflePlayW F right v)
    (hshape : left = pre ++ Move.foundToTab c b :: post)
    (hrightShape : right = Move.tabToFound d :: Move.tabToFound c :: rest)
    (hpost : post = []) (hcd : c ≠ d) :
    ∃ ρ' : List Move, ShufflePlayW u ρ' v ∧ ρ'.length < ρ.length := by
  subst hpost
  have hplay : ShufflePlayW u ρ v := by
    rw [hρ]; exact ShufflePlayW_append hleft hright
  -- the prefix ends with the pull from `A'` to `F`
  obtain ⟨A', hpre, hlast⟩ :=
    ShufflePlayW_split hleft pre [Move.foundToTab c b] hshape
  have hstepP : State.step A' (Move.foundToTab c b) = some F :=
    step_of_singleton hlast
  have hA' : A'.WF := by
    have h := hleft
    rw [hshape] at h
    exact SatDifferCensus.ShufflePlayW.wf_end hpre huwf
  have hF : F.WF := step_wf hA' hstepP
  -- the right leg: `raise d`, then `raise c`, then `rest`
  have hr : ShufflePlayW F (Move.tabToFound d :: Move.tabToFound c :: rest) v :=
    hrightShape ▸ hright
  obtain ⟨G, hrevD, hstepD, hright1⟩ := Bubble.walk_cons_inv hr
  obtain ⟨H, hrevC, hstepC, hrest⟩ := Bubble.walk_cons_inv hright1
  -- `raise d` was already legal before the pull
  have hcanFd : CanRaise F d := Bridge.canRaise_of_reversible_raise hF hrevD
  have hcanA'd : CanRaise A' d :=
    BlockKit.canRaise_of_pull_of_ne hA' hstepP (Ne.symm hcd) hcanFd
  have hrevA'd : reversibleAtW A' (Move.tabToFound d) :=
    DrainClose.reversibleAtW_tabToFound_of_canRaise hA' hcanA'd
  obtain ⟨G', hstepD'⟩ := step_tabToFound_of_canRaise hcanA'd
  -- undoing the pull: `raise c` lands back at `A'`
  have hbackC : State.step F (Move.tabToFound c) = some A' :=
    step_tabToFound_of_foundToTab hA' hstepP
  -- the raise/raise square at `F` identifies the two landings
  have hsq : G' = H :=
    ValleyElim.raise_raise_square_norev hF hbackC hstepD hstepD' hstepC
  have hrestG' : ShufflePlayW G' rest v := by
    rw [hsq]; exact hrest
  refine ⟨pre ++ Move.tabToFound d :: rest,
    ShufflePlayW_append hpre (Walk.cons hrevA'd hstepD' hrestG'), ?_⟩
  rw [hρ, hshape, hrightShape]
  simp only [List.length_append, List.length_cons, List.length_nil]
  omega

/-! ## §3. The empty-tail crossing corner has NO fork -/

/-- **`post = []` AND `c ≠ d` KILLS THE FORK DISJUNCT.**  The bottom is then the
pull's landing, where the pulled card and the raise card are both
vanilla-raisable and distinct, so no `ForkWitness` exists there
(`Bridge.no_forkWitness_at_pull_landing`).  Consequently, in this corner the
only way `ValleyElimNonfork` can hold is a strictly shorter play whose bracket
lies somewhere else in `ρ`. -/
theorem post_nil_no_fork
    {u v F : State} {left right pre post tail : List Move}
    {c d : Card} {b : Base}
    (huwf : u.WF)
    (hleft : ShufflePlayW u left F)
    (hright : ShufflePlayW F right v)
    (hshape : left = pre ++ Move.foundToTab c b :: post)
    (hrightShape : right = Move.tabToFound d :: tail)
    (hpost : post = []) (hcd : c ≠ d) :
    ∀ x : Card, ¬ ForkWitness F x := by
  subst hpost
  obtain ⟨A', hpre, hlast⟩ :=
    ShufflePlayW_split hleft pre [Move.foundToTab c b] hshape
  have hstep : State.step A' (Move.foundToTab c b) = some F :=
    step_of_singleton hlast
  have hA' : A'.WF := by
    have h := hleft
    rw [hshape] at h
    exact SatDifferCensus.ShufflePlayW.wf_end hpre huwf
  obtain ⟨_, _, hrev⟩ := Bridge.first_letter_of_play (hrightShape ▸ hright)
  exact Bridge.no_forkWitness_at_pull_landing hA' hstep hrev hcd

/-! ## §3b. The same-card (`c = d`) branch from one commutation premise -/

/-- **THE SAME-CARD COMMUTATION PREMISE (minimality-free).**  This is
`LiveKit.PostCommutesRaise` with the `SplitHyp` minimality conjunct removed, as
needed by `ValleyElimNonfork` (which has no shortest-play hypothesis).  The
commuted word moves `raise c` left across the free tail `post`. -/
def TurnCommutes : Prop :=
  ∀ (u v F : State) (ρ left right : List Move) (pre post tail : List Move)
    (c d : Card) (b : Base),
    ShufflePlayW u ρ v →
    (∀ m ∈ post, FreeMove m) →
    ρ = left ++ right →
    left = pre ++ Move.foundToTab c b :: post →
    right = Move.tabToFound d :: tail →
    c = d →
    ShufflePlayW u
      (pre ++ Move.foundToTab c b :: Move.tabToFound c :: (post ++ tail)) v

/-- **THE `c = d` BRANCH SHORTENS.**  Given the commutation premise, a valley
split with `c = d` yields an adjacent identity pair `pull c ; raise c` in the
commuted play; `LiveKit.identity_pair_delete` removes it, and the commuted word
has the same length as `ρ`, so `ρ` strictly shortens.

This proves the `c = d` half of `ValleyElimNonfork`'s elimination branch
modulo exactly one premise: the free tail must commute past the raise.  The
slide half of that premise is *not* free (`Temp/Transport_Report.md`: the left
window is not protected by the play). -/
theorem turnCommutes_shortens (hc : TurnCommutes)
    {u v F : State} {ρ left right pre post tail : List Move}
    {c d : Card} {b : Base}
    (huwf : u.WF)
    (hplay : ShufflePlayW u ρ v)
    (hfree : ∀ m ∈ post, FreeMove m)
    (hρ : ρ = left ++ right)
    (hleft : left = pre ++ Move.foundToTab c b :: post)
    (hright : right = Move.tabToFound d :: tail)
    (hcd : c = d) :
    ∃ ρ' : List Move, ShufflePlayW u ρ' v ∧ ρ'.length < ρ.length := by
  -- the commuted play
  have hcomm : ShufflePlayW u
      (pre ++ Move.foundToTab c b :: Move.tabToFound c :: (post ++ tail)) v :=
    hc u v F ρ left right pre post tail c d b hplay hfree hρ hleft hright hcd
  -- split it at `pre`
  obtain ⟨A, hpre, hrest⟩ :=
    ShufflePlayW_split hcomm pre
      (Move.foundToTab c b :: Move.tabToFound c :: (post ++ tail)) rfl
  have hAwf : A.WF := SatDifferCensus.ShufflePlayW.wf_end hpre huwf
  obtain ⟨B, _hrevB, hstep, _hrest1⟩ := Bubble.walk_cons_inv hrest
  -- W3 at the seam
  obtain ⟨ρ', hρ'play, hlen⟩ :=
    LiveKit.pull_raise_pair_shortens
      (u := u) (v := v)
      (ρ := pre ++ Move.foundToTab c b :: Move.tabToFound c :: (post ++ tail))
      (α := pre) (β := post ++ tail) (c := c) (b := b) (A := A) (B := B)
      hcomm rfl hpre hAwf hstep
  refine ⟨ρ', hρ'play, ?_⟩
  -- the commuted word has the same length as `ρ`
  have hlenC :
      (pre ++ Move.foundToTab c b :: Move.tabToFound c :: (post ++ tail)).length
        = ρ.length := by
    rw [hρ, hleft, hright, ← hcd]
    simp only [List.length_append, List.length_cons]
    omega
  omega

/-! ## §4. The residual and the reduction -/

/-- **THE EXACT RESIDUAL.**  Every valley split either

* already exhibits a `ForkWitness` at its bottom `F`, or
* the whole play `ρ` contains a **same-card bracket** `pull z ; γ ; raise z`
  whose raise has been commuted left across the interior, i.e. the word
  `raise z :: γ ++ β` is a witness play from the bracket's pull landing.

This is exactly the probe's dichotomy (`Temp/SplitProbe_Report.md` §4.2:
916/916 non-twin valley plays shorten by deleting a same-card bracket), with
the commutation made explicit.  The interior `γ` MAY CONTAIN SLIDES — this is
required by the probe's W2 (`Temp/SplitProbe_Report.md:286-308`), where the
interior is `pull 3D ; slide 2S→3D`; the deletion itself
(`bracket_delete_of_commuted`) is slide-free-free.

The disjunctive shape keeps the reduction constructive. -/
def NonforkBracketElim : Prop :=
  ∀ (u v : State) (ρ : List Move) (F : State),
    u.WF → SSaturated u → SSaturated v →
    ShufflePlayW u ρ v →
    ValleySplitAt u v ρ F →
    (∃ x : Card, ForkWitness F x) ∨
    (∃ (α γ β : List Move) (z : Card) (bz : Base) (P Q : State),
      ρ = α ++ Move.foundToTab z bz :: γ ++ Move.tabToFound z :: β ∧
      ShufflePlayW u α P ∧
      State.step P (Move.foundToTab z bz) = some Q ∧
      ShufflePlayW Q (Move.tabToFound z :: γ ++ β) v)

/-- **THE REDUCTION.**  `NonforkBracketElim` implies the campaign's
`ValleyElimNonfork`.  The fork branch is the identity; the bracket branch is
`bracket_delete_of_commuted`. -/
theorem valleyElimNonfork_of_nonforkBracket
    (h : NonforkBracketElim) : ValleyElimNonfork := by
  intro u v ρ F huwf hsu hsv hplay hsplit
  rcases h u v ρ F huwf hsu hsv hplay hsplit with
    hf | ⟨α, γ, β, z, bz, P, Q, hρ, hα, hstep, hcomm⟩
  · exact Or.inl hf
  · exact Or.inr (bracket_delete_of_commuted huwf hplay hρ hα hstep hcomm)

end Elim

#print axioms Elim.step_of_singleton
#print axioms Elim.bracket_delete_of_commuted
#print axioms Elim.bubble_bracket_shortens
#print axioms Elim.samecard_turn_nil_shortens
#print axioms Elim.samecard_raiseTurn_shortens
#print axioms Elim.post_nil_no_fork
#print axioms Elim.turnCommutes_shortens
#print axioms Elim.valleyElimNonfork_of_nonforkBracket
