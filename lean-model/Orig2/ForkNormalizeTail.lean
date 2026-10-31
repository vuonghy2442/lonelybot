import Orig2.ForkNormalize
import Orig2.ForkTailCover
import Orig2.ForkLanding

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
