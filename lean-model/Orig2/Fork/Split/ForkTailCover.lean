import Orig2.Fork.Split.ForkSplitResidual

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-!
# Orig2/ForkTailCover — `SplitKit.SplitBlock`: reduction, equivalence, and the exact residual

READ-ONLY scratch card (no source edits, no commit).  Zero `sorry`, zero
`Classical.choice`, zero `native_decide`; battery at the tail.

## Headline

1. **The block clause IS the cover clause.**  `splitBlock_iff_postCover`
   (`Orig2/Fork/Split/ForkTailCover.lean` §0): at `WF`, "`c` is not vanilla-raisable" is
   exactly "a card sits directly on `c`" (`canRaise_or_covered`), because
   `c` is S-live at the bottom (`SplitKit.splitHyp_green`).
2. **The block clause splits into two named halves**
   (`splitBlock_iff_parts`, §1):
   * `NoEmptyTail` — the free tail `post` of a split is never empty;
   * `TailCovers`  — a nonempty free tail covers `c` at the bottom.
3. **`canRaise_of_pull_of_ne`** (§2) — a `foundToTab` can never create the
   raisability of a DIFFERENT card: the *pile half* that
   `Orig2/Fork/Local/ForkNoPull.lean` records as missing (it proves only the `nextUp`
   half).  Consequence (§3): in the empty-tail case the raise card `d` was
   already raisable *before* the pull — the pull is irrelevant to `d`.
4. **The empty-tail half is a real obligation, not a minimality
   triviality**: for `post = []` minimality gives `c ≠ d`
   (`emptyTail_turn_ne`) and then `c.suit ≠ d.suit` (`emptyTail_suit_ne`),
   and the two letters are a *commuting square* — the swapped play has the
   SAME length, so no length argument can delete the case
   (`emptyTail_swap`).  The missing input is the crossing-block locator
   (`ValleyElim.ValleyCrossingLocator`, `Orig2/Fork/Split/ForkSplit.lean:912`).
5. **The cover half is the one-slide mechanism** (§4):
   `tailCovers_imp_unblock` turns the cover into the exact
   `OneSlide.one_slide_of_blocked_live` witness (a slide
   `tabToTab u1 (inr c.twin)` whose successor raises `c`).  The probe
   (`Temp/SplitProbe_Report.md`) shows this slide comes off `c.twin` in
   4010/4010 minimal bottoms.

## Census checks run for this card (Python, `Temp/Block_*.py`)

* `Temp/Block_probe.py` — every split (not just the canonical one) of every
  unit-shortest play over the 20 named/CutSep classes: 748 plays / 748
  splits, **0** with `CanRaise F c` and **0** with `post = []`; every
  shortest play is valley-shaped (no raise before a pull), so the split is
  unique.
* `Temp/Block_rand.py` — random-class search (11 classes with saturated
  rung-differing pairs, 50 shortest plays), 0 violations.
* `Temp/Block_adj.py` — adjacent `pull ; raise` turns DO occur in the
  components (410 in Plan-4, 906 in `P4_plus1`, 264 in `RED_n288`) but
  **none** lies on a shortest play between saturated states; in every
  sampled case (`Temp/Block_adj2.py`, 12/12) the raise card is already
  raisable before the pull, matching §2.
-/

namespace BlockKit

open SplitKit

/-! ## §0. The cover form -/

/-- **`PostCover`** — the block clause in chart/cover vocabulary: at every
split of a shortest play, a card sits directly on the pull card `c` at the
bottom.  (`CoveredAt`, `Orig2/Substrate/Vocab.lean:917`.) -/
def PostCover : Prop :=
  ∀ (u v : State) (ρ : List Move) (F : State)
    (left right : List Move) (c d : Card) (b : Base)
    (pre post tail : List Move),
    SplitHyp u v ρ F left right c d b pre post tail → CoveredAt F c

/-- **BLOCK ⟹ COVER.**  `c` is S-live at the bottom, so the flat dichotomy
per card (`canRaise_or_covered`) upgrades the negated license to a cover. -/
theorem postCover_of_splitBlock (hb : SplitBlock) : PostCover := by
  intro u v ρ F left right c d b pre post tail h
  obtain ⟨hF, hSc, -, -⟩ := splitHyp_green h
  exact covered_of_live_not_canRaise hF hSc
    (hb u v ρ F left right c d b pre post tail h)

/-- **COVER ⟹ BLOCK.**  A covered card tops no pile
(`not_canRaise_of_covered`). -/
theorem splitBlock_of_postCover (hc : PostCover) : SplitBlock := by
  intro u v ρ F left right c d b pre post tail h
  obtain ⟨hF, -, -, -⟩ := splitHyp_green h
  exact not_canRaise_of_covered hF
    (hc u v ρ F left right c d b pre post tail h)

/-- **THE BLOCK CLAUSE IS THE COVER CLAUSE.** -/
theorem splitBlock_iff_postCover : SplitBlock ↔ PostCover :=
  ⟨postCover_of_splitBlock, splitBlock_of_postCover⟩

/-! ## §1. The two halves of the block clause -/

/-- **`NoEmptyTail`** — the free tail of a split is never empty.  (A split
with `post = []` has `F` equal to the pull's landing, where `c` is
raisable: `Bridge.raisable_of_pull_at_end`.) -/
def NoEmptyTail : Prop :=
  ∀ (u v : State) (ρ : List Move) (F : State)
    (left right : List Move) (c d : Card) (b : Base)
    (pre post tail : List Move),
    SplitHyp u v ρ F left right c d b pre post tail → post ≠ []

/-- **`TailCovers`** — at every split with a nonempty free tail, the pull
card is covered at the bottom.  This is the free-tail licence transfer: the
probe's cover slide `x -> c`. -/
def TailCovers : Prop :=
  ∀ (u v : State) (ρ : List Move) (F : State)
    (left right : List Move) (c d : Card) (b : Base)
    (pre post tail : List Move),
    SplitHyp u v ρ F left right c d b pre post tail → post ≠ [] → CoveredAt F c

theorem noEmptyTail_of_splitBlock (hb : SplitBlock) : NoEmptyTail :=
  fun u v ρ F left right c d b pre post tail h =>
    splitHyp_post_ne_nil h (hb u v ρ F left right c d b pre post tail h)

theorem tailCovers_of_splitBlock (hb : SplitBlock) : TailCovers := by
  intro u v ρ F left right c d b pre post tail h _
  exact postCover_of_splitBlock hb u v ρ F left right c d b pre post tail h

/-- **THE BLOCK CLAUSE FROM ITS TWO HALVES.** -/
theorem splitBlock_of_parts (h1 : NoEmptyTail) (h2 : TailCovers) : SplitBlock := by
  intro u v ρ F left right c d b pre post tail h
  obtain ⟨hF, -, -, -⟩ := splitHyp_green h
  exact not_canRaise_of_covered hF
    (h2 u v ρ F left right c d b pre post tail h
      (h1 u v ρ F left right c d b pre post tail h))

/-- **THE EXACT DECOMPOSITION OF `SplitBlock`.**  Both halves are
necessary and sufficient. -/
theorem splitBlock_iff_parts : SplitBlock ↔ NoEmptyTail ∧ TailCovers := by
  constructor
  · intro hb
    exact ⟨noEmptyTail_of_splitBlock hb, tailCovers_of_splitBlock hb⟩
  · rintro ⟨h1, h2⟩
    exact splitBlock_of_parts h1 h2

/-! ## §2. A pull cannot create ANOTHER card's raise (the pile half)

`Orig2/Fork/Local/ForkNoPull.lean` proves `nextUp_of_pull_of_ne` and describes the
pile half ("`pileOfTop` can only be destroyed by a pull, never created") as
monotone "in the same way", but proves only the `nextUp` half — the file
contains no `pileOfTop` row (`FARM_MEMORY.md` records the pile half as still
to formalize).
This section proves it: a `foundToTab c b` writes exactly ONE pile — the
target of `b` — and that pile's new top is `c`, so no other card can
become (or stop being) a pile top, and its seat clause is untouched. -/

/-- **A PULL CANNOT CREATE THE RAISABILITY OF ANOTHER CARD.**  The full
`CanRaise` version of `ValleyNoPull.nextUp_of_pull_of_ne`: the foundation
half is that row, the pile half is `putCard`'s single-pile write. -/
theorem canRaise_of_pull_of_ne {st w : State} {c d : Card} {b : Base}
    (hwf : st.WF) (hstep : State.step st (Move.foundToTab c b) = some w)
    (hdc : d ≠ c) (h : CanRaise w d) : CanRaise st d := by
  obtain ⟨hnext, a, hpod, hseat⟩ := h
  have hwwf : w.WF := step_wf hwf hstep
  have hnextSt : st.nextUp d = true :=
    ValleyNoPull.nextUp_of_pull_of_ne hwf hstep hdc hnext
  obtain ⟨c', htop, hc', hcp, hs⟩ := step_foundToTab_inv hstep
  rw [hc'] at htop
  have htopW : (w.piles a).top = some d := (pileOfTop_eq_some_iff hwwf).mp hpod
  -- the foundation edit is invisible to the pile map
  have hpl0 : w.piles = (st.putCard c b).piles := by
    rw [hs]
    exact KingFuel.kf_setFound_putCard_piles st c.suit (chop (st.found c.suit)) c b
  -- a point write at pile `kk` whose new top is `c` cannot move `d`'s pile
  have key : ∀ (kk : Anchor) (P : Pile),
      w.piles = (fun a' => if a' = kk then P else st.piles a') →
      P.top = some c →
      st.pileOfTop d = some a ∧
        (chop (st.piles a).faceUp ≠ [] ∨
          ((st.piles a).hidden = [] ∧ d.rank = Rank.king)) := by
    intro kk P hpl hPtop
    have hne : a ≠ kk := by
      intro hae
      have htopk : (w.piles a).top = some c := by
        rw [hae, hpl]
        simp only [ite_eq_left rfl]
        exact hPtop
      rw [htopW] at htopk
      exact hdc (Option.some.inj htopk)
    have hpilea : w.piles a = st.piles a := by
      rw [hpl]
      simp only [ite_eq_right hne]
    have htopSt : (st.piles a).top = some d := by
      rw [← hpilea]; exact htopW
    refine ⟨(pileOfTop_eq_some_iff hwf).mpr htopSt, ?_⟩
    rw [← hpilea]
    exact hseat
  cases b with
  | inl kk =>
      have hpl : w.piles =
          (fun a' => if a' = kk then (⟨[], [c]⟩ : Pile) else st.piles a') := by
        rw [hpl0]
        exact putCard_piles_inl st c kk
      obtain ⟨h1, h2⟩ := key kk ⟨[], [c]⟩ hpl rfl
      exact ⟨hnextSt, a, h1, h2⟩
  | inr z =>
      have hkExists : ∃ kk, st.pileOfTop z = some kk := by
        cases hpo : st.pileOfTop z with
        | none =>
            rw [show st.canPlace c (Sum.inr z) = false by
              simp [State.canPlace, hpo]] at hcp
            exact absurd hcp (by simp)
        | some kk => exact ⟨kk, rfl⟩
      obtain ⟨kk, hk⟩ := hkExists
      have hpl : w.piles = (fun a' => if a' = kk then
            ({ st.piles kk with faceUp := (st.piles kk).faceUp ++ [c] } : Pile)
          else st.piles a') := by
        rw [hpl0]
        exact putCard_piles_inr st c z kk hk
      have hPtop : ({ st.piles kk with
          faceUp := (st.piles kk).faceUp ++ [c] } : Pile).top = some c := by
        simp only [Pile.top]
        exact lastOf_snoc
      obtain ⟨h1, h2⟩ := key kk _ hpl hPtop
      exact ⟨hnextSt, a, h1, h2⟩

/-! ## §3. The empty-tail case: `post = []`

If the free tail is empty then `F` is the pull's landing and `c` is
raisable there (`emptyTail_canRaise`), so `NoEmptyTail` is *necessary*.
This section records what minimality does and does not give in that case. -/

/-- Two raisable cards that are different have different suits.  (Same suit
plus both next-up forces equal ranks, hence equal cards.) -/
theorem suit_ne_of_canRaise_of_ne {w : State} {c d : Card}
    (hc : CanRaise w c) (hd : CanRaise w d) (hcd : c ≠ d) : c.suit ≠ d.suit := by
  intro hsu
  have h1 : c.rank.toIdx = (w.found c.suit).length := by
    simpa [State.nextUp, State.foundHeight] using of_decide_eq_true hc.1
  have h2 : d.rank.toIdx = (w.found d.suit).length := by
    simpa [State.nextUp, State.foundHeight] using of_decide_eq_true hd.1
  have hr : c.rank = d.rank := by
    apply Rank.toIdx_inj
    rw [h1, h2, hsu]
  have hcd' : c = d := by
    cases c with
    | mk s1 r1 =>
      cases d with
      | mk s2 r2 =>
        simp_all
  exact hcd hcd'

/-- **THE EMPTY TAIL MAKES THE PULL CARD RAISABLE.**  `post = []` means the
bottom IS the pull's landing, so `Bridge.raisable_of_pull_at_end` applies. -/
theorem emptyTail_canRaise {u v : State} {ρ : List Move} {F : State}
    {left right : List Move} {c d : Card} {b : Base}
    {pre post tail : List Move}
    (h : SplitHyp u v ρ F left right c d b pre post tail) (hpost : post = []) :
    CanRaise F c := by
  obtain ⟨huwf, -, -, -, -, -, -, hleft, -, hshape, -, -⟩ := h
  subst hpost
  have hleft' : ShufflePlayW u (pre ++ [Move.foundToTab c b]) F := by
    rw [← hshape]
    simpa using hleft
  exact Bridge.raisable_of_pull_at_end huwf hleft'

/-- **MINIMALITY FORCES `c ≠ d` IN THE EMPTY-TAIL CASE.**  `post = []` makes
the turn an ADJACENT `pull c ; raise d`; if `c = d` the two letters delete
(`Bridge.shortest_adjacent_turn_ne`), contradicting minimality. -/
theorem emptyTail_turn_ne {u v : State} {ρ : List Move} {F : State}
    {left right : List Move} {c d : Card} {b : Base}
    {pre post tail : List Move}
    (h : SplitHyp u v ρ F left right c d b pre post tail) (hpost : post = []) :
    c ≠ d := by
  obtain ⟨huwf, -, -, hplay, -, hmin, hρ, hleft, -, hshape, -, hrightShape⟩ := h
  subst hpost
  have hEq : ρ = pre ++ Move.foundToTab c b :: Move.tabToFound d :: tail := by
    rw [hρ, hshape, hrightShape]
    simp
  have hplay' : ShufflePlayW u
      (pre ++ Move.foundToTab c b :: Move.tabToFound d :: tail) v := hEq ▸ hplay
  obtain ⟨A', hpre, _⟩ :=
    ValleyElim.ShufflePlayW_split hleft pre (Move.foundToTab c b :: []) hshape
  have hmin' : ∀ ρ' : List Move, ShufflePlayW u ρ' v →
      (pre ++ Move.foundToTab c b :: Move.tabToFound d :: tail).length ≤ ρ'.length := by
    intro ρ' hρ'
    have hh := hmin ρ' hρ'
    rw [hEq] at hh
    exact hh
  exact Bridge.shortest_adjacent_turn_ne huwf hpre hplay' hmin'

/-- **THE EMPTY-TAIL TURN IS A GENUINE CROSSING TURN.**  With minimality the
two cards differ and (being both next-up at the bottom) lie in different
suits: exactly the second disjunct of
`ValleyElim.valley_elim_pull_raise`'s `hturn`. -/
theorem emptyTail_suit_ne {u v : State} {ρ : List Move} {F : State}
    {left right : List Move} {c d : Card} {b : Base}
    {pre post tail : List Move}
    (h : SplitHyp u v ρ F left right c d b pre post tail) (hpost : post = []) :
    c.suit ≠ d.suit := by
  have hcanC : CanRaise F c := emptyTail_canRaise h hpost
  obtain ⟨-, -, hcanD, -⟩ := splitHyp_green h
  exact suit_ne_of_canRaise_of_ne hcanC hcanD (emptyTail_turn_ne h hpost)

/-- **THE RAISE CARD IS RAISABLE *BEFORE* THE PULL** (empty-tail case).
This is `canRaise_of_pull_of_ne` (§2): the pull of `c` cannot have created
`d`'s license, so `d` was already raisable at the pull's origin.  The probe
(`Temp/Block_adj2.py`) confirms this on every adjacent turn found in the
components: `can_raise d at u = True` in 12/12 sampled Plan-4 pairs. -/
theorem emptyTail_canRaise_before {u v : State} {ρ : List Move} {F : State}
    {left right : List Move} {c d : Card} {b : Base}
    {pre post tail : List Move}
    (h : SplitHyp u v ρ F left right c d b pre post tail) (hpost : post = []) :
    ∃ A' : State, ShufflePlayW u pre A' ∧ CanRaise A' d := by
  have hcd : d ≠ c := (emptyTail_turn_ne h hpost).symm
  obtain ⟨-, -, hcanD, -⟩ := splitHyp_green h
  obtain ⟨huwf, -, -, -, -, -, -, hleft, -, hshape, -, -⟩ := h
  subst hpost
  obtain ⟨A', hpre, hrest⟩ :=
    ValleyElim.ShufflePlayW_split hleft pre (Move.foundToTab c b :: []) hshape
  have hA' : A'.WF := SatDifferCensus.ShufflePlayW.wf_end hpre huwf
  cases hrest with
  | cons _ hstep htail =>
      cases htail with
      | nil =>
          exact ⟨A', hpre, canRaise_of_pull_of_ne hA' hstep hcd hcanD⟩

/-! ## §4. The cover half is the one-slide mechanism -/

/-- **THE COVER IS THE ONE-SLIDE WITNESS.**  `TailCovers` at a split is
exactly the hypothesis of `OneSlide.one_slide_of_blocked_live`: the card
`u1` directly on `c` slides its run onto `c.twin`, reversibly, and the
successor raises `c`.  So the residual `TailCovers` is the same obligation
as "the free tail performs the twin-source cover slide" — the mechanism the
probe finds in 4010/4010 minimal bottoms
(`Temp/SplitProbe_Report.md` §3). -/
theorem tailCovers_imp_unblock (h : TailCovers) :
    ∀ (u v : State) (ρ : List Move) (F : State)
      (left right : List Move) (c d : Card) (b : Base)
      (pre post tail : List Move),
      SplitHyp u v ρ F left right c d b pre post tail → post ≠ [] →
      ∃ (u1 : Card) (z : State) (a : Anchor) (bs run : List Card),
        (F.piles a).faceUp = bs ++ c :: u1 :: run ∧
        State.step F (Move.tabToTab u1 (Sum.inr c.twin)) = some z ∧
        reversibleAtW F (Move.tabToTab u1 (Sum.inr c.twin)) ∧
        CanRaise z c := by
  intro u v ρ F left right c d b pre post tail hh hpost
  obtain ⟨hF, hSc, -, -⟩ := splitHyp_green hh
  have hcov : CoveredAt F c := h u v ρ F left right c d b pre post tail hh hpost
  exact OneSlide.one_slide_of_blocked_live hF hSc
    (not_canRaise_of_covered hF hcov)

/-! ## §5. The cover half needs a SLIDE in the free tail -/

/-- **A DRAW-ONLY FREE TAIL NEVER COVERS `c`.**  Draws preserve the piles
(`SplitKit.drawPlay_found_piles`); at the pull's landing `c` is the top of
the pile it was placed on, so nothing sits on it there, and the cover read
is a pile read (`seatOf_congr_piles`).  Hence `TailCovers` is only possible
when the free tail contains a slide — the probe's "cover created by a slide
in `post`", 4010/4010. -/
theorem not_covered_of_draw_tail {u v : State} {ρ : List Move} {F : State}
    {left right : List Move} {c d : Card} {b : Base}
    {pre post tail : List Move}
    (h : SplitHyp u v ρ F left right c d b pre post tail)
    (hdraw : ∀ m ∈ post, m = Move.draw) :
    ¬ CoveredAt F c := by
  obtain ⟨huwf, -, -, -, -, -, -, hleft, -, hshape, -, -⟩ := h
  obtain ⟨A', hpre, hrest⟩ :=
    ValleyElim.ShufflePlayW_split hleft pre (Move.foundToTab c b :: post) hshape
  have hA' : A'.WF := SatDifferCensus.ShufflePlayW.wf_end hpre huwf
  obtain ⟨B, hstep, hpost⟩ :
      ∃ B : State, State.step A' (Move.foundToTab c b) = some B ∧
        ShufflePlayW B post F := by
    cases hrest with
    | cons _ hstep hpost => exact ⟨_, hstep, hpost⟩
  have hBwf : B.WF := step_wf hA' hstep
  have hcanB : CanRaise B c := ValleyStep.pull_card_canRaise hA' hstep
  have hBcov : ¬ CoveredAt B c := fun hcov =>
    (not_canRaise_of_covered hBwf hcov) hcanB
  obtain ⟨-, hpiles⟩ := drawPlay_found_piles hpost hdraw
  intro hcov
  obtain ⟨y, hy⟩ := hcov
  exact hBcov ⟨y, by
    rw [← seatOf_congr_piles hpiles y]
    exact hy⟩

/-- **THE COVER HALF FORCES A SLIDE IN THE FREE TAIL.**  This is the converse
direction of `SplitKit.splitHyp_post_has_slide` (which goes from the block
to a slide); together they say the block clause and the cover half pin the
same event. -/
theorem tailCovers_imp_slide (h : TailCovers) :
    ∀ (u v : State) (ρ : List Move) (F : State)
      (left right : List Move) (c d : Card) (b : Base)
      (pre post tail : List Move),
      SplitHyp u v ρ F left right c d b pre post tail → post ≠ [] →
      ∃ (c' : Card) (b' : Base), Move.tabToTab c' b' ∈ post := by
  intro u v ρ F left right c d b pre post tail hh hpost
  have hh0 := hh
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hfree, -⟩ := hh0
  by_cases hany : post.any isSlideB = true
  · obtain ⟨α, m, β, heq, _, hm⟩ := ValleyElim.exists_first_bool isSlideB post hany
    obtain ⟨c', b', rfl⟩ := isSlideB_eq_true_iff.mp hm
    exact ⟨c', b', by
      rw [heq]
      exact List.mem_append_right _ (List.mem_cons_self ..)⟩
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
    exact not_covered_of_draw_tail hh hdraw
      (h u v ρ F left right c d b pre post tail hh hpost)

/-- **THE CAMPAIGN CHAIN FROM THE TWO GEOMETRIC HALVES.**  `SplitLivePair`
plus the two halves of the block clause (nonempty free tail, cover) plus the
choice-free shortest-play interface give `SatDifferForkWF`; the twin clause
and the rank floor are derived (`splitResidualData_of_livePair_block`), and
the drain is discharged (`Bridge.forkExistenceFromAsymmetry_drainClosed`). -/
theorem satDifferForkWF_of_livePair_parts
    (hl : SplitLivePair) (h1 : NoEmptyTail) (h2 : TailCovers)
    (hmin : ValleyElim.ShortestPlayExists) : SatDifferForkWF :=
  satDifferForkWF_of_livePair_block_drainClosed hl (splitBlock_of_parts h1 h2) hmin

end BlockKit

/-! ## §6. Battery -/

#print axioms BlockKit.postCover_of_splitBlock
#print axioms BlockKit.splitBlock_of_postCover
#print axioms BlockKit.splitBlock_iff_postCover
#print axioms BlockKit.noEmptyTail_of_splitBlock
#print axioms BlockKit.tailCovers_of_splitBlock
#print axioms BlockKit.splitBlock_of_parts
#print axioms BlockKit.splitBlock_iff_parts
#print axioms BlockKit.canRaise_of_pull_of_ne
#print axioms BlockKit.suit_ne_of_canRaise_of_ne
#print axioms BlockKit.emptyTail_canRaise
#print axioms BlockKit.emptyTail_turn_ne
#print axioms BlockKit.emptyTail_suit_ne
#print axioms BlockKit.emptyTail_canRaise_before
#print axioms BlockKit.tailCovers_imp_unblock
#print axioms BlockKit.not_covered_of_draw_tail
#print axioms BlockKit.tailCovers_imp_slide
#print axioms BlockKit.satDifferForkWF_of_livePair_parts
