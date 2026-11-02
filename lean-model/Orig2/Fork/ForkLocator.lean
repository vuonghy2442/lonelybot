import Orig2.Fork.ForkSplit
import Orig2.Fork.ForkCommute

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-!
# Orig2/ForkLocator — the repaired locator (SCRATCH)

READ-ONLY scratch (no existing source touched; no commit).  Zero
`sorry`, zero `Classical.choice`, zero `native_decide`; battery at the
tail.

`ValleyElim.ValleyCrossingLocator` is refuted in
`Temp/Locator_Refute.lean`.  Two independent defects:

1. **Existence.**  The partner letters `pull d` and `raise c` need not
   occur anywhere in the play.
2. **Contiguity is syntactic.**  `CrossingBlock u v ρ` is a predicate on
   the *given* list `ρ`.  Commuting interior letters produces a
   *different* play `ρ'`; a block found after reordering lives in `ρ'`,
   never in `ρ`.

This file states and proves the two correct replacements:

* `ValleyCrossingPartnerLocator` — the partners are already adjacent to
  the turn, so the block *is* in `ρ`; proved directly from the play's
  own steps (no commutation).
* `CrossingBracketNormalizer` — the general target: the partners exist
  with arbitrary interior segments, and the conclusion is a re-run play
  `ρ'` of the *same length* containing a block.  The reduction
  `normalizer → strictly shorter play` is proved via
  `crossing_block_delete`.
-/

namespace LocatorCorrected

open ValleyElim

/-- **THE REPAIRED LOCATOR.**  Same data as `ValleyCrossingLocator`,
plus the two partner letters: the matching pull of `d` is the last
letter of `left`, and the matching raise of `c` is the first letter of
`right`.  Then the play *is* the contiguous block
`pull d ; pull c ; raise d ; raise c`, and `CrossingBlock` follows from
the play's own steps (no commutation needed). -/
def ValleyCrossingPartnerLocator : Prop :=
  ∀ (u v : State) (ρ : List Move) (F : State)
    (left right : List Move) (c d : Card) (b : Base) (tail : List Move)
    (α γ : List Move) (bd : Base),
    u.WF → ShufflePlayW u ρ v →
    ρ = left ++ [Move.foundToTab c b, Move.tabToFound d] ++ right →
    left = α ++ [Move.foundToTab d bd] →
    right = Move.tabToFound c :: γ →
    ShufflePlayW u left F →
    c ≠ d → c.suit ≠ d.suit →
    CrossingBlock u v ρ

/-- **A CONTIGUOUS BLOCK IN THE GIVEN PLAY.**  Splitting the play at the
prefix and at the four-letter block recovers the four steps; the block's
own landing is the prefix state (`crossing_cancel`), so the suffix is a
play from the prefix state.  This is the reusable core of the repaired
locator. -/
theorem crossingBlock_of_block_decomp {u v : State} {ρ α γ : List Move}
    {c d : Card} {b bd : Base}
    (huwf : u.WF) (hplay : ShufflePlayW u ρ v)
    (hρ : ρ = α ++ [Move.foundToTab d bd, Move.foundToTab c b,
        Move.tabToFound d, Move.tabToFound c] ++ γ) :
    CrossingBlock u v ρ := by
  have hsplit : ρ = α ++ ([Move.foundToTab d bd, Move.foundToTab c b,
      Move.tabToFound d, Move.tabToFound c] ++ γ) := by
    rw [hρ]; simp only [List.append_assoc]
  obtain ⟨A, hα, hrest⟩ := ShufflePlayW_split hplay α
    ([Move.foundToTab d bd, Move.foundToTab c b,
      Move.tabToFound d, Move.tabToFound c] ++ γ) hsplit
  obtain ⟨E, hblock, hγ⟩ := ShufflePlayW_split hrest
    [Move.foundToTab d bd, Move.foundToTab c b,
      Move.tabToFound d, Move.tabToFound c] γ rfl
  obtain ⟨B, hB, htail1⟩ := ShufflePlayW_split hblock
    [Move.foundToTab d bd] [Move.foundToTab c b, Move.tabToFound d,
      Move.tabToFound c] rfl
  cases hB with
  | cons hrevd hstepd hnil =>
    cases hnil with
    | nil =>
      obtain ⟨C, hC, htail2⟩ := ShufflePlayW_split htail1
        [Move.foundToTab c b] [Move.tabToFound d, Move.tabToFound c] rfl
      cases hC with
      | cons hrevc hstepc hnil2 =>
        cases hnil2 with
        | nil =>
          obtain ⟨D, hD, htail3⟩ := ShufflePlayW_split htail2
            [Move.tabToFound d] [Move.tabToFound c] rfl
          cases hD with
          | cons hrevrd hsteprd hnil3 =>
            cases hnil3 with
            | nil =>
              obtain ⟨E', hE, htail4⟩ := ShufflePlayW_split htail3
                [Move.tabToFound c] [] rfl
              cases htail4 with
              | nil =>
              cases hE with
              | cons hrevrc hsteprc hnil4 =>
                cases hnil4 with
                | nil =>
                  have hAwf : A.WF := SatDifferCensus.ShufflePlayW.wf_end hα huwf
                  have hEA : E = A := crossing_cancel hAwf hstepd hstepc hsteprd hsteprc
                  have hγA : ShufflePlayW A γ v := by
                    rw [hEA] at hγ
                    exact hγ
                  exact ⟨α, γ, c, d, bd, b, A, B, C, D, E, hρ, hα,
                    hstepd, hstepc, hsteprd, hsteprc, hγA⟩

/-- **THE REPAIRED LOCATOR HOLDS.** -/
theorem valleyCrossingPartnerLocator : ValleyCrossingPartnerLocator := by
  intro u v ρ F left right c d b tail α γ bd huwf hplay hρ hleft hright _ _ _
  refine crossingBlock_of_block_decomp (c := c) (d := d) (b := b) (bd := bd)
    (α := α) (γ := γ) huwf hplay ?_
  rw [hρ, hleft, hright]
  simp only [List.cons_append, List.nil_append, List.append_assoc]

/-- The shortening corollary, exactly parallel to
`ValleyElim.valley_elim_pull_raise_cross_of_locator`. -/
theorem valley_elim_pull_raise_cross_of_partnerLocator
    (hloc : ValleyCrossingPartnerLocator)
    {u v : State} {ρ : List Move} {F : State}
    {left right : List Move} {c d : Card} {b : Base} {tail : List Move}
    {α γ : List Move} {bd : Base}
    (huwf : u.WF) (hplay : ShufflePlayW u ρ v)
    (hdecomp : ρ = left ++ [Move.foundToTab c b, Move.tabToFound d] ++ right)
    (hpartL : left = α ++ [Move.foundToTab d bd])
    (hpartR : right = Move.tabToFound c :: γ)
    (hleft : ShufflePlayW u left F)
    (hcd : c ≠ d) (hsuit : c.suit ≠ d.suit) :
    ∃ ρ' : List Move, ShufflePlayW u ρ' v ∧ ρ'.length < ρ.length :=
  crossing_block_delete huwf (hloc u v ρ F left right c d b tail α γ bd
    huwf hplay hdecomp hpartL hpartR hleft hcd hsuit)

/-! ## §1. The named residual: non-adjacent bracket normalization -/

/-- **THE NAMED RESIDUAL.**  The partner letters may sit anywhere around
the turn:

```text
ρ = α ++ [pull d bd] ++ β ++ [pull c b ; raise d] ++ γ ++ [raise c] ++ δ ++ ε
```

The conclusion is a **re-run play `ρ'` of the same length** containing a
crossing block.  It cannot be `CrossingBlock u v ρ` (defect 2 of the
refuted locator); the block only becomes contiguous after the interior
letters are commuted away.  This is the smallest honest replacement: it
assumes the partner letters exist (defect 1) and leaves only the
reordering.

The reordering itself is the play-level bubble of `Temp/Bubble_Core.lean`
(`swap_at`, `bubble_raise_left`, `bracket_delete_at`); the required
local squares are `step_comm_pull_pull`, `step_comm_pull_raise`,
`step_comm_raise_raise`, the draw squares, and the (still-unassembled)
slide/pull and slide/raise squares.  `step_comm_slide_slide` is *not*
needed (the reordering only crosses pulls and raises, never a slide
past another slide), so the `c1 ≠ c2` side condition does not enter. -/
def CrossingBracketNormalizer : Prop :=
  ∀ (u v : State) (ρ : List Move) (F : State)
    (left right : List Move) (c d : Card) (b : Base) (tail : List Move)
    (α β γ δ ε : List Move) (bd : Base),
    u.WF → ShufflePlayW u ρ v →
    ρ = α ++ [Move.foundToTab d bd] ++ β ++
        [Move.foundToTab c b, Move.tabToFound d] ++ γ ++
        [Move.tabToFound c] ++ δ ++ ε →
    ShufflePlayW u left F →
    c ≠ d → c.suit ≠ d.suit →
    ∃ ρ' : List Move, ShufflePlayW u ρ' v ∧ ρ'.length = ρ.length ∧
      CrossingBlock u v ρ'

/-- **REDUCTION: NORMALIZER ⟹ STRICTLY SHORTER PLAY.**  Once the play is
re-run with the four letters contiguous, `crossing_block_delete` removes
them.  The equality of lengths transfers the bound back to `ρ`. -/
theorem normalizer_shortens (h : CrossingBracketNormalizer)
    {u v : State} {ρ : List Move} {F : State}
    {left right : List Move} {c d : Card} {b : Base} {tail : List Move}
    {α β γ δ ε : List Move} {bd : Base}
    (huwf : u.WF) (hplay : ShufflePlayW u ρ v)
    (hdecomp : ρ = α ++ [Move.foundToTab d bd] ++ β ++
        [Move.foundToTab c b, Move.tabToFound d] ++ γ ++
        [Move.tabToFound c] ++ δ ++ ε)
    (hleft : ShufflePlayW u left F)
    (hcd : c ≠ d) (hsuit : c.suit ≠ d.suit) :
    ∃ ρ'' : List Move, ShufflePlayW u ρ'' v ∧ ρ''.length < ρ.length := by
  obtain ⟨ρ', hplay', hlen, hblock⟩ :=
    h u v ρ F left right c d b tail α β γ δ ε bd huwf hplay hdecomp hleft hcd hsuit
  obtain ⟨ρ'', hplay'', hlt⟩ := crossing_block_delete huwf hblock
  exact ⟨ρ'', hplay'', by omega⟩

/-- **THE IDENTITY CASE IS PROVED.**  When the interior segments are
empty, the block already lies in `ρ`, so the normalizer holds with
`ρ' = ρ`.  This connects the normalizer to the repaired locator's
kernel. -/
theorem normalizer_identity {u v : State} {ρ α γ : List Move}
    {c d : Card} {b bd : Base} {F : State}
    {left right tail : List Move}
    (huwf : u.WF) (hplay : ShufflePlayW u ρ v)
    (hρ : ρ = α ++ [Move.foundToTab d bd, Move.foundToTab c b,
        Move.tabToFound d, Move.tabToFound c] ++ γ) :
    ∃ ρ' : List Move, ShufflePlayW u ρ' v ∧ ρ'.length = ρ.length ∧
      CrossingBlock u v ρ' :=
  ⟨ρ, hplay, rfl, crossingBlock_of_block_decomp huwf hplay hρ⟩

end LocatorCorrected

#print axioms LocatorCorrected.crossingBlock_of_block_decomp
#print axioms LocatorCorrected.valleyCrossingPartnerLocator
#print axioms LocatorCorrected.valley_elim_pull_raise_cross_of_partnerLocator
#print axioms LocatorCorrected.normalizer_shortens
#print axioms LocatorCorrected.normalizer_identity
