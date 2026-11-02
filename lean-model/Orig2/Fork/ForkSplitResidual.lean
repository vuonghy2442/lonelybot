import Orig2.Fork.ForkBridge

/-!
# Orig2/ForkSplitResidual — `Bridge.SplitResidual`: refutation, correction, reduction

READ-ONLY scratch card.  Nothing under `Orig2/` (or any other source
directory) is modified; no commits.  Zero `sorry`, zero
`Classical.choice`, zero `native_decide` (battery at the tail: every row
is `[propext, Quot.sound]` or `[propext]`).

## Headline

1. **`Bridge.SplitResidual` (`Orig2/Fork/ForkBridge.lean:346`) is FALSE as
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
   `SplitLivePair` is `TwinLivePair F d` (`Orig2/Fork/ForkCriticalPair.lean:46`)
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

/-- The twin of a card is never the card. -/
theorem card_twin_ne (c : Card) : c.twin ≠ c := by
  intro h
  exact Suit.twin_ne c.suit (congrArg Card.suit h)

/-! ## §1b. The one read the block clause needs: `CanRaise` sees only
`found` and `piles` -/

/-- Congruence of the anchor search (local copy; `Orig/Twin.lean`'s
`firstWhere_congr` is outside the seam). -/
theorem firstWhere_congr_local {α : Type} {p q : α → Bool} (h : ∀ x, p x = q x) :
    ∀ l : List α, firstWhere p l = firstWhere q l
  | [] => rfl
  | x :: t => by
      show (match p x with
            | true => some x
            | false => firstWhere p t) =
           (match q x with
            | true => some x
            | false => firstWhere q t)
      rw [h x]
      cases q x with
      | false => exact firstWhere_congr_local h t
      | true => rfl

theorem topOf_congr_piles {u v : State} (hp : u.piles = v.piles) (a : Anchor) :
    u.topOf a = v.topOf a := by
  unfold State.topOf
  rw [hp]

theorem pileOfTop_congr_piles {u v : State} (hp : u.piles = v.piles) (z : Card) :
    u.pileOfTop z = v.pileOfTop z := by
  unfold State.pileOfTop
  exact firstWhere_congr_local
    (p := fun a => decide (u.topOf a = some z))
    (q := fun a => decide (v.topOf a = some z))
    (fun a => by rw [topOf_congr_piles hp a]) Anchor.all

/-- The vanilla raise license is a `found`+`piles` read. -/
theorem canRaise_congr_found_piles {u v : State} (hf : u.found = v.found)
    (hp : u.piles = v.piles) (c : Card) : CanRaise u c ↔ CanRaise v c := by
  have hpile : u.pileOfTop c = v.pileOfTop c := pileOfTop_congr_piles hp c
  have hnext : u.nextUp c = v.nextUp c := by
    unfold State.nextUp State.foundHeight
    rw [hf]
  unfold CanRaise
  rw [hnext, hpile, hp]

/-- A draw-only play preserves `found` and `piles`. -/
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

/-- **THE BLOCK CLAUSE FORCES A *SLIDE* IN THE FREE TAIL** — the strict
sharpening of `splitHyp_post_ne_nil`.  If every letter of `post` were a
draw, then `F.found = B.found` and `F.piles = B.piles` at the pull's
landing `B`, and `CanRaise` is a `found`+`piles` read, so the pull card
would still be raisable at `F`.  Hence a `tabToTab` must occur. -/
theorem splitHyp_post_has_slide {u v : State} {ρ : List Move} {F : State}
    {left right : List Move} {c d : Card} {b : Base}
    {pre post tail : List Move}
    (h : SplitHyp u v ρ F left right c d b pre post tail)
    (hblock : ¬ CanRaise F c) :
    ∃ (c' : Card) (b' : Base), Move.tabToTab c' b' ∈ post := by
  obtain ⟨huwf, -, -, -, -, -, -, hleft, -, hshape, hfree, -⟩ := h
  obtain ⟨A', hpre, hrest⟩ :=
    ValleyElim.ShufflePlayW_split hleft pre (Move.foundToTab c b :: post) hshape
  have hA' : A'.WF := SatDifferCensus.ShufflePlayW.wf_end hpre huwf
  obtain ⟨B, hstepP, hpost⟩ :
      ∃ B : State, State.step A' (Move.foundToTab c b) = some B ∧
        ShufflePlayW B post F := by
    cases hrest with
    | cons hrev hstep hpost => exact ⟨_, hstep, hpost⟩
  have hcanB : CanRaise B c := ValleyStep.pull_card_canRaise hA' hstepP
  by_cases hany : post.any isSlideB = true
  · obtain ⟨α, m, β, heq, hα, hm⟩ := ValleyElim.exists_first_bool isSlideB post hany
    obtain ⟨c', b', rfl⟩ := isSlideB_eq_true_iff.mp hm
    exact ⟨c', b', by rw [heq]; exact List.mem_append_right _ (List.mem_cons_self ..)⟩
  · exfalso
    have hfalse : post.any isSlideB = false := by
      cases hv : post.any isSlideB with
      | false => rfl
      | true => exact absurd hv hany
    have hno : ∀ m ∈ post, isSlideB m = false := ValleyElim.any_eq_false hfalse
    have hdraw : ∀ m ∈ post, m = Move.draw := by
      intro m hm
      rcases hfree m hm with rfl | ⟨c', b', hm'⟩
      · rfl
      · exfalso
        have hs : isSlideB m = true := by rw [hm']; rfl
        rw [hno m hm] at hs
        exact Bool.false_ne_true hs
    obtain ⟨hf, hp⟩ := drawPlay_found_piles hpost hdraw
    exact hblock ((canRaise_congr_found_piles hf hp c).mpr hcanB)


/-! ## §2. The corrected residual and its three-clause decomposition -/

/-- **`SplitResidualData`** — the CORRECTED `Bridge.SplitResidual`: the
split equations are hypotheses, so the conclusion is about the cards that
actually occur in the split. -/
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

/-- **THE REFUTATION FROM DIFFERING RUNGS.**  For any saturated
differing-rung pair with a witness play, `Bridge.SplitResidual` is false
— `ValleyElim.valley_exists` supplies the split. -/
theorem not_splitResidual_of_satDiffer
    {u v : State} {ρ : List Move}
    (huwf : u.WF) (hsu : SSaturated u) (hsv : SSaturated v)
    (hdiff : ∃ σ : Suit, rungAt u σ ≠ rungAt v σ)
    (hplay : ShufflePlayW u ρ v)
    (hmin : ∀ ρ' : List Move, ShufflePlayW u ρ' v → ρ.length ≤ ρ'.length) :
    ¬ Bridge.SplitResidual := by
  obtain ⟨F, hF⟩ := ValleyElim.valley_exists huwf hsu hsv hdiff hplay
  exact not_splitResidual_of_split huwf hsu hsv hplay hF hmin

/-! ## §4. The strictly smaller residuals -/

/-- **`SplitLivePair`** — at the bottom, every S-live card is the raise
card `d` or its twin, and both are live.  This is the campaign's own
`TwinLivePair` (`Orig2/Fork/ForkCriticalPair.lean:46`): a card-free,
rank-free statement about the bottom's live set. -/
def SplitLivePair : Prop :=
  ∀ (u v : State) (ρ : List Move) (F : State)
    (left right : List Move) (c d : Card) (b : Base)
    (pre post tail : List Move),
    SplitHyp u v ρ F left right c d b pre post tail → TwinLivePair F d

/-- **`SplitFork`** — the bottom is a fork on the raise card
(`ForkWitness F d`, `Orig2/Substrate/Vocab.lean:592`). -/
def SplitFork : Prop :=
  ∀ (u v : State) (ρ : List Move) (F : State)
    (left right : List Move) (c d : Card) (b : Base)
    (pre post tail : List Move),
    SplitHyp u v ρ F left right c d b pre post tail → ForkWitness F d

/-- **`SplitNe`** — the pull card is not the raise card.  This is the only
content of the same-card valley elimination across the free tail: it needs
`raise` to commute past the slides of `post` (`Temp/Commute_Step_Report.md`
§4 records that the slide/raise square is the missing kit row). -/
def SplitNe : Prop :=
  ∀ (u v : State) (ρ : List Move) (F : State)
    (left right : List Move) (c d : Card) (b : Base)
    (pre post tail : List Move),
    SplitHyp u v ρ F left right c d b pre post tail → c ≠ d

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

/-- **THE RANK FLOOR IS PROVED** — indeed, from the twin clause the live
pair's rank equals `c.rank`, so the floor holds with equality.  The floor
needs `SplitLivePair` plus `SplitTwin` (which is itself derived from
`SplitLivePair` + `SplitBlock` above). -/
theorem splitFloor_of_livePair_twin (hl : SplitLivePair) (ht : SplitTwin) :
    SplitFloor := by
  intro u v ρ F left right c d b pre post tail h e he
  have hdc : d.rank.toIdx = c.rank.toIdx := by
    rw [ht u v ρ F left right c d b pre post tail h, Card.twin_rank]
  rcases (hl u v ρ F left right c d b pre post tail h e).mp he with h' | h'
  · rw [h']
    omega
  · rw [h', Card.twin_rank]
    omega

/-- **THE STRICT REDUCTION (3 clauses → 2).**  `SplitLivePair` (the
bottom's live set is the raise card's twin pair) plus `SplitBlock` (the
pull card is blocked) implies the whole corrected residual: the twin
clause and the rank floor are *proved*, not assumed. -/
theorem splitResidualData_of_livePair_block (hl : SplitLivePair) (hb : SplitBlock) :
    SplitResidualData := by
  intro u v ρ F left right c d b pre post tail h
  have ht : SplitTwin := splitTwin_of_livePair_block hl hb
  exact ⟨ht u v ρ F left right c d b pre post tail h,
    hb u v ρ F left right c d b pre post tail h,
    splitFloor_of_livePair_twin hl ht u v ρ F left right c d b pre post tail h⟩

/-- **THE BLOCK CLAUSE PROVES THE PIN.**  `c` is blocked and `d` is
raisable at the bottom, so `c ≠ d`; hence `SplitNe` follows from
`SplitBlock` with no extra input. -/
theorem splitNe_of_block (hb : SplitBlock) : SplitNe := by
  intro u v ρ F left right c d b pre post tail h hcd
  obtain ⟨-, -, hcanD, -⟩ := splitHyp_green h
  exact hb u v ρ F left right c d b pre post tail h (hcd ▸ hcanD)

/-- **THE FORK'S LIVE-SET HALF IS `SplitLivePair`** — the fork witness pins
the live set outright (`forkWitness_iff`,
`Orig2/Fork/ForkCriticalPair.lean:50`). -/
theorem splitLivePair_of_fork (hf : SplitFork) : SplitLivePair := by
  intro u v ρ F left right c d b pre post tail h
  exact ((forkWitness_iff F d).mp (hf u v ρ F left right c d b pre post tail h)).1

/-- `SplitLivePair ∧ SplitBlock` yields the fork form: the live set is
exactly the twin pair and the blocked member is the pull card. -/
theorem splitFork_of_livePair_block (hl : SplitLivePair) (hb : SplitBlock) :
    SplitFork := by
  intro u v ρ F left right c d b pre post tail h
  have htwin : d = c.twin := splitTwin_of_livePair_block hl hb
    u v ρ F left right c d b pre post tail h
  have hdtc : d.twin = c := by rw [htwin, card_twin_twin]
  refine ⟨?_, ?_⟩
  · intro z
    exact (hl u v ρ F left right c d b pre post tail h z).symm
  · rw [hdtc]
    exact hb u v ρ F left right c d b pre post tail h

/-- **THE FORK-FORM REDUCTION.**  If the bottom is a fork on the raise
card and the pull card is not the raise card, the corrected residual
follows.  (The pin is what turns "the raise card's twin is blocked" into
"the *pull* card is blocked".) -/
theorem splitResidualData_of_fork_ne (hf : SplitFork) (hn : SplitNe) :
    SplitResidualData := by
  intro u v ρ F left right c d b pre post tail h
  obtain ⟨hiff, hblkdt⟩ := hf u v ρ F left right c d b pre post tail h
  have hcd : c ≠ d := hn u v ρ F left right c d b pre post tail h
  obtain ⟨-, hSc, -, -⟩ := splitHyp_green h
  have hct : c = d.twin := by
    rcases (hiff c).mpr hSc with h' | h'
    · exact absurd h' hcd
    · exact h'
  have htwin : d = c.twin := by rw [hct, card_twin_twin]
  refine ⟨htwin, ?_, ?_⟩
  · rw [hct]; exact hblkdt
  · intro e he
    have hdc : d.rank.toIdx = c.rank.toIdx := by rw [htwin, Card.twin_rank]
    rcases (hiff e).mpr he with h' | h'
    · rw [h']; omega
    · rw [h', Card.twin_rank]; omega

/-- The fork form with the block clause instead of the pin. -/
theorem splitResidualData_of_fork_block (hf : SplitFork) (hb : SplitBlock) :
    SplitResidualData :=
  splitResidualData_of_fork_ne hf (splitNe_of_block hb)

/-! ## §5. Green corollaries on the split data -/

/-- From the twin clause: the pull card and the raise card differ. -/
theorem splitData_ne {u v : State} {ρ : List Move} {F : State}
    {left right : List Move} {c d : Card} {b : Base}
    {pre post tail : List Move}
    (h : SplitHyp u v ρ F left right c d b pre post tail)
    (htwin : d = c.twin) : c ≠ d := by
  intro hcd
  have : c = c.twin := by rw [← htwin, hcd]
  exact card_twin_ne c this.symm

/-- **THE BLOCK CLAUSE FORCES DIFFERENT SUITS.**  The pull fixes the rung
of `c`'s suit at `c.rank.toIdx`; the raise at `F` makes `d` next-up,
fixing the rung of `d`'s suit at `d.rank.toIdx`.  Equal suits would force
equal ranks, hence `c = d`, contradicting the block.  (This is the
`c.suit ≠ d.suit` side condition of `ValleyElim.ValleyCrossingLocator`,
discharged in the blocked branch.) -/
theorem splitBlock_suit_ne {u v : State} {ρ : List Move} {F : State}
    {left right : List Move} {c d : Card} {b : Base}
    {pre post tail : List Move}
    (h : SplitHyp u v ρ F left right c d b pre post tail)
    (hblock : ¬ CanRaise F c) : c.suit ≠ d.suit := by
  intro hsu
  obtain ⟨-, -, hcanD, -⟩ := splitHyp_green h
  obtain ⟨huwf, -, -, -, -, -, -, hleft, -, hshape, hfree, -⟩ := h
  obtain ⟨A', hpre, hrest⟩ :=
    ValleyElim.ShufflePlayW_split hleft pre (Move.foundToTab c b :: post) hshape
  have hA' : A'.WF := SatDifferCensus.ShufflePlayW.wf_end hpre huwf
  obtain ⟨B, hstepP, hpost⟩ :
      ∃ B : State, State.step A' (Move.foundToTab c b) = some B ∧
        ShufflePlayW B post F := by
    cases hrest with
    | cons hrev hstep hpost => exact ⟨_, hstep, hpost⟩
  have hnextD : F.nextUp d = true := hcanD.1
  have hdrank : d.rank.toIdx = (F.found d.suit).length := by
    have hh := of_decide_eq_true hnextD
    simpa [State.nextUp, State.foundHeight] using hh
  obtain ⟨c', htop, hc', -, -⟩ := step_foundToTab_inv hstepP
  rw [hc'] at htop
  have hidx : c.rank.toIdx + 1 = (A'.found c.suit).length :=
    SatDifferCensus.foundTop_rank_succ hA' htop
  have hrungB : (B.found c.suit).length = (A'.found c.suit).length - 1 := by
    have hh := rungAt_foundToTab hstepP c.suit
    rw [ite_eq_left rfl] at hh
    exact hh
  have hcrank : c.rank.toIdx = (F.found c.suit).length := by
    have hpres := ValleyElim.rungAt_eq_of_free_play hpost hfree c.suit
    rw [show (F.found c.suit).length = (B.found c.suit).length from hpres, hrungB]
    omega
  have hrank : c.rank = d.rank := by
    apply Rank.toIdx_inj
    rw [hcrank, hdrank, hsu]
  have hcd : c = d := by
    cases c with
    | mk s1 r1 =>
      cases d with
      | mk s2 r2 =>
        simp_all
  have hc : CanRaise F c := by rw [hcd]; exact hcanD
  exact hblock hc

/-- **THE RESIDUAL'S TURN IS A GENUINE CROSSING TURN**: with the twin and
block clauses the two cards differ and lie in different suits — exactly
the second disjunct of `ValleyElim.valley_elim_pull_raise`'s `hturn`. -/
theorem splitData_crossing {u v : State} {ρ : List Move} {F : State}
    {left right : List Move} {c d : Card} {b : Base}
    {pre post tail : List Move}
    (h : SplitHyp u v ρ F left right c d b pre post tail)
    (htwin : d = c.twin) (hblock : ¬ CanRaise F c) :
    c ≠ d ∧ c.suit ≠ d.suit :=
  ⟨splitData_ne h htwin, splitBlock_suit_ne h hblock⟩


/-- The pull card is **covered** at the bottom (the chart's `CoveredAt`
read of the block clause, `Orig2/Substrate/Vocab.lean:917`). -/
theorem splitData_covered {u v : State} {ρ : List Move} {F : State}
    {left right : List Move} {c d : Card} {b : Base}
    {pre post tail : List Move}
    (h : SplitHyp u v ρ F left right c d b pre post tail)
    (hblock : ¬ CanRaise F c) : CoveredAt F c := by
  obtain ⟨hF, hSc, -, -⟩ := splitHyp_green h
  exact covered_of_live_not_canRaise hF hSc hblock

/-- The exact cover shape: a nonempty run sits directly on the covered
pull card (a card `u1` on `c`, with `canSitOn u1 c`). -/
theorem splitData_covered_shape {u v : State} {ρ : List Move} {F : State}
    {left right : List Move} {c d : Card} {b : Base}
    {pre post tail : List Move}
    (h : SplitHyp u v ρ F left right c d b pre post tail)
    (htwin : d = c.twin) (hblock : ¬ CanRaise F c) :
    ∃ (a : Anchor) (bs : List Card) (u1 : Card) (rest : List Card),
      (F.piles a).faceUp = bs ++ c :: u1 :: rest ∧ canSitOn u1 c = true := by
  obtain ⟨hF, hSc, -, -⟩ := splitHyp_green h
  have hdtc : d.twin = c := by rw [htwin, card_twin_twin]
  have hSdt : CanRaiseS F d.twin := by rw [hdtc]; exact hSc
  have hbdt : ¬ CanRaise F d.twin := by rw [hdtc]; exact hblock
  simpa only [hdtc] using Bridge.covered_twin_head_fits hF hSdt hbdt

/-- **THE SPLIT DATA IS A DRAIN INVARIANT.**  With the residual's three
clauses, the bottom carries `Drain.DrainInvariant F d` — exactly the input
of the drain phase (`Orig2/Fork/ForkDrainInduction.lean:65`,
`Drain.drain_raise_phase`). -/
theorem splitData_drainInvariant {u v : State} {ρ : List Move} {F : State}
    {left right : List Move} {c d : Card} {b : Base}
    {pre post tail : List Move}
    (h : SplitHyp u v ρ F left right c d b pre post tail)
    (htwin : d = c.twin) (hblock : ¬ CanRaise F c)
    (hfloor : ∀ e, CanRaiseS F e → c.rank.toIdx ≤ e.rank.toIdx) :
    Drain.DrainInvariant F d := by
  obtain ⟨hF, hSc, hcanD, -⟩ := splitHyp_green h
  have hdtc : d.twin = c := by rw [htwin, card_twin_twin]
  have hSdt : CanRaiseS F d.twin := by rw [hdtc]; exact hSc
  have hbdt : ¬ CanRaise F d.twin := by rw [hdtc]; exact hblock
  have hrank : d.rank.toIdx = c.rank.toIdx := by rw [htwin, Card.twin_rank]
  exact ⟨hcanD, hSdt, hbdt, fun e he => by rw [hrank]; exact hfloor e he⟩

/-- **THE BOTTOM IS A DRAIN TERMINAL.**  `SplitLivePair` + `SplitBlock`
alone give `Drain.DrainTerminal F d`: the drain's terminal branch
(`drain_terminal_fork`) applies at the bottom with no further work. -/
theorem splitData_drainTerminal {u v : State} {ρ : List Move} {F : State}
    {left right : List Move} {c d : Card} {b : Base}
    {pre post tail : List Move}
    (h : SplitHyp u v ρ F left right c d b pre post tail)
    (hl : TwinLivePair F d) (hblock : ¬ CanRaise F c) :
    Drain.DrainTerminal F d := by
  obtain ⟨hF, hSc, hcanD, -⟩ := splitHyp_green h
  have hct : c = d.twin := by
    rcases (hl c).mp hSc with h' | h'
    · have hc : CanRaise F c := by rw [h']; exact hcanD
      exact absurd hc hblock
    · exact h'
  have htwin : d = c.twin := by rw [hct, card_twin_twin]
  have hfloor : ∀ e, CanRaiseS F e → c.rank.toIdx ≤ e.rank.toIdx := by
    intro e he
    have hdc : d.rank.toIdx = c.rank.toIdx := by rw [htwin, Card.twin_rank]
    rcases (hl e).mp he with h' | h'
    · rw [h']; omega
    · rw [h', Card.twin_rank]; omega
  exact ⟨splitData_drainInvariant h htwin hblock hfloor,
    fun e he => (hl e).mp he⟩

/-! ## §6. The campaign chain from the corrected residual -/

/-- The corrected residual implies the bridge residual `BottomDip` (the
proof of `Bridge.bottomDip_of_splitResidual`, with the split equations
available so no binder mismatch remains). -/
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

/-- The same chain from the two-clause form. -/
theorem satDifferForkWF_of_livePair_block_drainClosed
    (hl : SplitLivePair) (hb : SplitBlock) (hmin : ValleyElim.ShortestPlayExists) :
    SatDifferForkWF :=
  satDifferForkWF_of_splitResidualData_drainClosed
    (splitResidualData_of_livePair_block hl hb) hmin

end SplitKit

/-! ## §7. Battery -/

#print axioms SplitKit.card_twin_ne
#print axioms SplitKit.firstWhere_congr_local
#print axioms SplitKit.pileOfTop_congr_piles
#print axioms SplitKit.canRaise_congr_found_piles
#print axioms SplitKit.drawPlay_found_piles
#print axioms SplitKit.isSlideB_eq_true_iff
#print axioms SplitKit.splitHyp_green
#print axioms SplitKit.splitHyp_post_ne_nil
#print axioms SplitKit.splitHyp_post_has_slide
#print axioms SplitKit.splitResidualData_of_parts
#print axioms SplitKit.parts_of_splitResidualData
#print axioms SplitKit.splitResidualData_iff_parts
#print axioms SplitKit.not_splitResidual_of_split
#print axioms SplitKit.not_splitResidual_of_satDiffer
#print axioms SplitKit.splitTwin_of_livePair_block
#print axioms SplitKit.splitFloor_of_livePair_twin
#print axioms SplitKit.splitResidualData_of_livePair_block
#print axioms SplitKit.splitNe_of_block
#print axioms SplitKit.splitLivePair_of_fork
#print axioms SplitKit.splitFork_of_livePair_block
#print axioms SplitKit.splitResidualData_of_fork_ne
#print axioms SplitKit.splitResidualData_of_fork_block
#print axioms SplitKit.splitData_ne
#print axioms SplitKit.splitBlock_suit_ne
#print axioms SplitKit.splitData_crossing
#print axioms SplitKit.splitData_covered
#print axioms SplitKit.splitData_covered_shape
#print axioms SplitKit.splitData_drainInvariant
#print axioms SplitKit.splitData_drainTerminal
#print axioms SplitKit.bottomDip_of_splitResidualData
#print axioms SplitKit.satDifferForkWF_of_splitResidualData_drainClosed
#print axioms SplitKit.satDifferForkWF_of_livePair_block_drainClosed
