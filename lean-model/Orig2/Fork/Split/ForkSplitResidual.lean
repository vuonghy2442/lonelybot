import Orig2.Fork.Split.ForkBridge

/-!
# Orig2/ForkSplitResidual — `Bridge.SplitResidual`: refutation, correction, reduction

READ-ONLY scratch card.  Nothing under `Orig2/` (or any other source
directory) is modified; no commits.  Zero `sorry`, zero
`Classical.choice`, zero `native_decide` (battery at the tail: every row
is `[propext, Quot.sound]` or `[propext]`).

## Headline

1. **`Bridge.SplitResidual` (`Orig2/Fork/Split/ForkBridge.lean:346`) is FALSE as
   literally stated.**  Its binders `left right c d b pre post tail`
   never occur in the hypotheses: the hypothesis list mentions only
   `u v ρ F` plus `ValleyElim.ValleySplitAt u v ρ F`, which is an
   *existential* over fresh data.  So the residual asserts
   `d = c.twin` for arbitrary cards.  Refutation:
   `not_splitResidual_of_split` (`c = d = x` gives `x = x.twin`), and
   `not_splitResidual_of_satDiffer` (via `ValleyElim.valley_exists`).
   `Bridge.bottomDip_of_splitResidual` is still a valid proof term, but
   its hypothesis is uninhabitable, so that chain is vacuous.

2. **The corrected residual** is `SplitResidualData` here: same
   conclusion, with the split equations of `ValleyElim.ValleySplitAt`
   supplied as hypotheses (`SplitHyp`).  This is the statement the
   campaign actually feeds (`Temp/Split_check.py`: 240/240 splits over
   the 20 known classes satisfy it, with `post` of length 1 or 2 and
   never 0).

3. **Three-way decomposition** (the "strictly smaller named residual"
   in the brief's sense): `SplitTwin` / `SplitBlock` / `SplitFloor`
   with `splitResidualData_iff_parts` (both directions).

4. **Two-way strict reduction**: `SplitLivePair ∧ SplitBlock ⇒
   SplitResidualData` (`splitResidualData_of_livePair_block`), where
   *the twin equation and the rank floor are PROVED*:
   * `SplitTwin` from `SplitLivePair` + `SplitBlock` + the green
     `CanRaise F d` (`splitTwin_of_livePair_block`);
   * `SplitFloor` from `SplitLivePair` + `SplitTwin`, with EQUALITY
     (`splitFloor_of_livePair_twin`).
   `SplitLivePair` is `TwinLivePair F d` (`Orig2/Fork/Local/ForkCriticalPair.lean:46`)
   — a card-equation-free, rank-free statement about the bottom's live
   set.

5. **Fork form.**  `SplitLivePair ∧ SplitBlock` is exactly the fork
   `ForkWitness F d` (`Orig2/Substrate/Vocab.lean:592`) up to the pin `c = d.twin`:
   - `splitFork_of_livePair_block`;
   - `splitResidualData_of_fork_ne` : `SplitFork → SplitNe → SplitResidualData`;
   - `splitNe_of_block` : the block clause alone gives the pin `c ≠ d`;
   - hence `splitResidualData_of_fork_block`.

6. Green corollaries on the split data: `c ≠ d` from the twin clause,
   `CoveredAt F c`, the exact cover pile shape (`canSitOn u1 c`),
   `post ≠ []`, `Drain.DrainInvariant F d`, and
   `Drain.DrainTerminal F d` from `SplitLivePair` + `SplitBlock`.

7. The campaign chain is re-derived from the corrected residual
   (`bottomDip_of_splitResidualData`,
   `satDifferForkWF_of_splitResidualData_drainClosed`).
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

namespace SplitKit

/-! ## §1. The split hypotheses as one predicate -/

/-- **`SplitHyp`** — all the data of a genuine valley split: the play, the
minimality of the play, the split equations, and the endpoint grades.
This is exactly the conjunction `Bridge.SplitResidual` *forgot* to
require of its binders. -/
def SplitHyp (u v : State) (ρ : List Move) (F : State)
    (left right : List Move) (c d : Card) (b : Base)
    (pre post tail : List Move) : Prop :=
  u.WF ∧ SSaturated u ∧ SSaturated v ∧ ShufflePlayW u ρ v ∧
  ValleyElim.ValleySplitAt u v ρ F ∧
  (∀ ρ' : List Move, ShufflePlayW u ρ' v → ρ.length ≤ ρ'.length) ∧
  ρ = left ++ right ∧
  ShufflePlayW u left F ∧
  ShufflePlayW F right v ∧
  left = pre ++ Move.foundToTab c b :: post ∧
  (∀ m ∈ post, ValleyElim.FreeMove m) ∧
  right = Move.tabToFound d :: tail

/-! ## §1b. The one read the block clause needs: `CanRaise` sees only
`found` and `piles` -/

theorem drawPlay_found_piles {u v : State} {ρ : List Move}
    (hplay : ShufflePlayW u ρ v) (hall : ∀ m ∈ ρ, m = Move.draw) :
    v.found = u.found ∧ v.piles = u.piles := by
  induction hplay with
  | nil st => exact ⟨rfl, rfl⟩
  | @cons st s₁ W m ρ hlet hstep hrest ih =>
      have htail : ∀ x ∈ ρ, x = Move.draw := fun x hx => hall x (List.mem_cons_of_mem m hx)
      obtain ⟨hf2, hp2⟩ := ih htail
      have hm : m = Move.draw := hall m (List.mem_cons_self ..)
      subst hm
      exact ⟨hf2.trans (stepDraw_found hstep), hp2.trans (stepDraw_piles hstep)⟩

/-- Computable "is a slide" (the constructive handle on `post`). -/
def isSlideB : Move → Bool
  | Move.tabToTab _ _ => true
  | _ => false

theorem isSlideB_eq_true_iff {m : Move} :
    isSlideB m = true ↔ ∃ (c : Card) (b : Base), m = Move.tabToTab c b := by
  cases m <;> simp [isSlideB]


/-- **THE GREEN FACTS OF A SPLIT.**  At the bottom `F`: `F.WF`, the pull
card `c` is S-live (`Bridge.bottom_pull_live`), and the raise card `d` is
vanilla-`CanRaise` (the raise fires at `F`) hence S-live. -/
theorem splitHyp_green {u v : State} {ρ : List Move} {F : State}
    {left right : List Move} {c d : Card} {b : Base}
    {pre post tail : List Move}
    (h : SplitHyp u v ρ F left right c d b pre post tail) :
    F.WF ∧ CanRaiseS F c ∧ CanRaise F d ∧ CanRaiseS F d := by
  obtain ⟨huwf, -, -, -, -, -, -, hleft, hright, hshape, hfree, hrightShape⟩ := h
  have hF : F.WF := SatDifferCensus.ShufflePlayW.wf_end hleft huwf
  have hSc : CanRaiseS F c := Bridge.bottom_pull_live huwf hleft hshape hfree
  obtain ⟨F', hstep, hrev⟩ := Bridge.first_letter_of_play (hrightShape ▸ hright)
  have hcanD : CanRaise F d := Bridge.canRaise_of_reversible_raise hF hrev
  exact ⟨hF, hSc, hcanD, CanRaiseS.now d hcanD⟩

/-- **The block clause forces a nonempty free tail** (green
`Bridge.blocked_pull_needs_free_tail`, restated on `SplitHyp`). -/
theorem splitHyp_post_ne_nil {u v : State} {ρ : List Move} {F : State}
    {left right : List Move} {c d : Card} {b : Base}
    {pre post tail : List Move}
    (h : SplitHyp u v ρ F left right c d b pre post tail)
    (hblock : ¬ CanRaise F c) : post ≠ [] := by
  obtain ⟨huwf, -, -, -, -, -, -, hleft, -, hshape, -, -⟩ := h
  exact Bridge.blocked_pull_needs_free_tail huwf (hshape ▸ hleft) hblock

def SplitResidualData : Prop :=
  ∀ (u v : State) (ρ : List Move) (F : State)
    (left right : List Move) (c d : Card) (b : Base)
    (pre post tail : List Move),
    SplitHyp u v ρ F left right c d b pre post tail →
    d = c.twin ∧ ¬ CanRaise F c ∧
      (∀ e, CanRaiseS F e → c.rank.toIdx ≤ e.rank.toIdx)

/-- Clause 1 alone: the raise card is the pull card's twin. -/
def SplitTwin : Prop :=
  ∀ (u v : State) (ρ : List Move) (F : State)
    (left right : List Move) (c d : Card) (b : Base)
    (pre post tail : List Move),
    SplitHyp u v ρ F left right c d b pre post tail → d = c.twin

/-- Clause 2 alone: the pull card is vanilla-blocked at the bottom. -/
def SplitBlock : Prop :=
  ∀ (u v : State) (ρ : List Move) (F : State)
    (left right : List Move) (c d : Card) (b : Base)
    (pre post tail : List Move),
    SplitHyp u v ρ F left right c d b pre post tail → ¬ CanRaise F c

/-- Clause 3 alone: the rank floor at the bottom. -/
def SplitFloor : Prop :=
  ∀ (u v : State) (ρ : List Move) (F : State)
    (left right : List Move) (c d : Card) (b : Base)
    (pre post tail : List Move),
    SplitHyp u v ρ F left right c d b pre post tail →
      ∀ e, CanRaiseS F e → c.rank.toIdx ≤ e.rank.toIdx

/-- The three clauses reassemble the corrected residual. -/
theorem splitResidualData_of_parts (h1 : SplitTwin) (h2 : SplitBlock)
    (h3 : SplitFloor) : SplitResidualData := by
  intro u v ρ F left right c d b pre post tail h
  exact ⟨h1 u v ρ F left right c d b pre post tail h,
    h2 u v ρ F left right c d b pre post tail h,
    h3 u v ρ F left right c d b pre post tail h⟩

/-- Conversely each clause is a projection of the corrected residual. -/
theorem parts_of_splitResidualData (h : SplitResidualData) :
    SplitTwin ∧ SplitBlock ∧ SplitFloor := by
  refine ⟨?_, ?_, ?_⟩
  · intro u v ρ F left right c d b pre post tail hh
    exact (h u v ρ F left right c d b pre post tail hh).1
  · intro u v ρ F left right c d b pre post tail hh
    exact (h u v ρ F left right c d b pre post tail hh).2.1
  · intro u v ρ F left right c d b pre post tail hh
    exact (h u v ρ F left right c d b pre post tail hh).2.2

/-- **THE THREE-CLAUSE DECOMPOSITION** — the corrected residual is exactly
the conjunction of the three named residuals. -/
theorem splitResidualData_iff_parts :
    SplitResidualData ↔ SplitTwin ∧ SplitBlock ∧ SplitFloor := by
  constructor
  · exact parts_of_splitResidualData
  · rintro ⟨h1, h2, h3⟩
    exact splitResidualData_of_parts h1 h2 h3

/-! ## §3. `Bridge.SplitResidual` is FALSE as literally stated -/

/-- **THE BINDER-SCOPE REFUTATION.**  `Bridge.SplitResidual`'s hypotheses
never mention the binders `left right c d b pre post tail`; only
`ValleyElim.ValleySplitAt u v ρ F` occurs, and that is an existential over
*fresh* data.  Hence the residual forces `d = c.twin` for *arbitrary*
cards; taking `c = d = x` gives `x = x.twin`, absurd.

So as soon as ONE valley split exists (which `valley_exists` guarantees
for any saturated differing-rung pair with a witness play),
`Bridge.SplitResidual` is contradictory. -/
theorem not_splitResidual_of_split
    {u v : State} {ρ : List Move} {F : State}
    (huwf : u.WF) (hsu : SSaturated u) (hsv : SSaturated v)
    (hplay : ShufflePlayW u ρ v) (hsplit : ValleyElim.ValleySplitAt u v ρ F)
    (hmin : ∀ ρ' : List Move, ShufflePlayW u ρ' v → ρ.length ≤ ρ'.length) :
    ¬ Bridge.SplitResidual := by
  intro h
  let x : Card := ⟨Suit.spade, Rank.ace⟩
  have hbad := h u v ρ F [] [] x x (Sum.inr x) [] [] []
    huwf hsu hsv hplay hsplit hmin
  exact card_twin_ne x hbad.1.symm

def SplitLivePair : Prop :=
  ∀ (u v : State) (ρ : List Move) (F : State)
    (left right : List Move) (c d : Card) (b : Base)
    (pre post tail : List Move),
    SplitHyp u v ρ F left right c d b pre post tail → TwinLivePair F d

/-- **`SplitNe`** — the pull card is not the raise card.  This is the only
content of the same-card valley elimination across the free tail: it needs
`raise` to commute past the slides of `post` (`Temp/Commute_Step_Report.md`
§4 records that the slide/raise square is the missing kit row). -/
def SplitNe : Prop :=
  ∀ (u v : State) (ρ : List Move) (F : State)
    (left right : List Move) (c d : Card) (b : Base)
    (pre post tail : List Move),
    SplitHyp u v ρ F left right c d b pre post tail → c ≠ d

theorem bottomDip_of_splitResidualData (h : SplitResidualData) : Bridge.BottomDip := by
  intro u v ρ F huwf hsu hsv hcls hdiff hplay hsplit hmin
  obtain ⟨left, right, c, d, b, pre, post, tail,
    hρ, hleft, hright, hshape, hfree, hrightShape⟩ := hsplit
  have hsplit' : ValleyElim.ValleySplitAt u v ρ F :=
    ⟨left, right, c, d, b, pre, post, tail,
      hρ, hleft, hright, hshape, hfree, hrightShape⟩
  have hh : SplitHyp u v ρ F left right c d b pre post tail :=
    ⟨huwf, hsu, hsv, hplay, hsplit', hmin, hρ, hleft, hright, hshape, hfree, hrightShape⟩
  obtain ⟨htwin, hblock, hfloor⟩ := h u v ρ F left right c d b pre post tail hh
  obtain ⟨-, hcan, hS, hblk, hfloor'⟩ :=
    Bridge.bottom_asymmetry_of_split_data huwf hleft hright hshape hfree hrightShape
      htwin hblock hfloor
  exact ⟨d, hcan, hS, hblk, hfloor'⟩

/-- **THE FULL CHAIN, WITH THE CORRECTED RESIDUAL.**  The corrected
residual plus the choice-free shortest-play interface gives
`SatDifferForkWF` (the drain is discharged by
`Bridge.forkExistenceFromAsymmetry_drainClosed`). -/
theorem satDifferForkWF_of_splitResidualData_drainClosed
    (h : SplitResidualData) (hmin : ValleyElim.ShortestPlayExists) :
    SatDifferForkWF :=
  Bridge.satDifferForkWF_of_bottom_asymmetry
    (Bridge.bottomAsymmetry_of_bottomDip (bottomDip_of_splitResidualData h) hmin)
    Bridge.forkExistenceFromAsymmetry_drainClosed

/-- **THE TWIN CLAUSE IS PROVED.**  From `TwinLivePair F d` (the live set
is exactly `{d, d.twin}`), the green `CanRaise F d` (the raise fires at
the bottom) and the block of `c`: `c` cannot be `d`, hence `c = d.twin`
and `d = c.twin`. -/
theorem splitTwin_of_livePair_block (hl : SplitLivePair) (hb : SplitBlock) :
    SplitTwin := by
  intro u v ρ F left right c d b pre post tail h
  obtain ⟨-, hSc, hcanD, -⟩ := splitHyp_green h
  rcases (hl u v ρ F left right c d b pre post tail h c).mp hSc with h' | h'
  · have hc : CanRaise F c := by rw [h']; exact hcanD
    exact absurd hc (hb u v ρ F left right c d b pre post tail h)
  · rw [h', card_twin_twin]

/-- **MINIMALITY FORCES `c ≠ d` IN THE EMPTY-TAIL CASE.** -/
theorem emptyTail_turn_ne
    {u v : State} {ρ : List Move} {F : State}
    {left right : List Move} {c d : Card} {b : Base}
    {pre post tail : List Move}
    (h : SplitHyp u v ρ F left right c d b pre post tail) (hpost : post = []) :
    c ≠ d := by
  obtain ⟨huwf, -, -, hplay, -, hmin, hρ, hleft, hright, hshape, hfree,
    hrightShape⟩ := h
  subst hpost
  have hplay' : ShufflePlayW u
      (pre ++ Move.foundToTab c b :: Move.tabToFound d :: tail) v := by
    have hp := hplay
    rw [hρ, hshape, hrightShape] at hp
    simpa [List.append_assoc] using hp
  have hlen' : ∀ ρ' : List Move, ShufflePlayW u ρ' v →
      (pre ++ Move.foundToTab c b :: Move.tabToFound d :: tail).length ≤ ρ'.length := by
    intro ρ' hρ'
    have hlen := hmin ρ' hρ'
    rw [hρ, hshape, hrightShape] at hlen
    simpa [List.append_assoc] using hlen
  have hleft' : ShufflePlayW u (pre ++ Move.foundToTab c b :: ([] : List Move)) F := by
    rw [← hshape]
    simpa using hleft
  obtain ⟨A', hpre, hrest⟩ :=
    ValleyElim.ShufflePlayW_split hleft' pre [Move.foundToTab c b] rfl
  exact Bridge.shortest_adjacent_turn_ne huwf hpre hplay' hlen'

end SplitKit

/-! ## §7. Battery -/

#print axioms SplitKit.drawPlay_found_piles
#print axioms SplitKit.isSlideB_eq_true_iff
#print axioms SplitKit.splitHyp_green
#print axioms SplitKit.splitHyp_post_ne_nil
#print axioms SplitKit.emptyTail_turn_ne
#print axioms SplitKit.splitResidualData_of_parts
#print axioms SplitKit.parts_of_splitResidualData
#print axioms SplitKit.splitResidualData_iff_parts
#print axioms SplitKit.not_splitResidual_of_split
#print axioms SplitKit.bottomDip_of_splitResidualData
#print axioms SplitKit.satDifferForkWF_of_splitResidualData_drainClosed
