import Orig2.ForkEqSplit
import Orig2.FiberTransfer

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-!
# Orig2/ForkEqSplitSlide — the equal-rung interior window: the pull/raise pairing

READ-ONLY scratch.  No source edit, no commit.  Zero `sorry`, zero
`Classical.choice`, zero `native_decide`, zero `axiom`; axiom battery at the
tail.

Target: `EqSplit.EqualRungInteriorSlideFree` (`Orig2/ForkEqSplit.lean:257`),
the two-clause residual

```text
    ρ = pre ++ pull c b :: (post ++ γ) ++ raise c :: β
    (a)  no slide of `post ++ γ` is headed by `c`      -- `SlideFwd.NoSlideOf c`
    (b)  no slide of `post ++ γ` lands on `c`          -- `∀ x, tabToTab x (inr c) ∉ …`
```

## Contents (kernel-checked; the residual's hypotheses are unchanged)

* **§1** `mem_found_iff_rung`, `found_nodup` — the foundation-row bridge.

* **§2** `pulled_of_found_loss`, `raised_of_found_gain` — play level: losing
  foundation membership forces a pull of the card, gaining it forces a raise.

* **§3 `paired_iff` — THE PULL/RAISE PAIRING (main result).**  At `SplitHyp` +
  `MountainSplit` + equal rungs,

  ```text
  (∃ b, pull x b ∈ left)  ↔  raise x ∈ right
  ```

  The two mountain legs are paired **card by card**, not merely by the
  per-suit count (`MountainKit.raisesOf_eq_sub_of_no_pull`).  So the identity
  of every right-leg raise is determined by the left leg.

* **§4** `window_landing_rank`, `window_landing_pulled` — anatomy of a
  base-clause violation: a window slide `x → c`
  - has `x.rank.toIdx + 1 = c.rank.toIdx` (the mover sits exactly one rank
    below `c`, in an opposite-colour suit), and
  - if `x` leaves `c` by a raise (`raise x ∈ right`) then `x` was **pulled in
    `pre`**; the pull cannot be the split's own pull because the ranks differ.

  Hence a base-clause violation is always a genuine cover/uncover pair whose
  mover is a full `pull … raise` bracket on the rank just below `c`.  It is
  *not* a local impossibility.  The exact play-level content of the clause is
  `WindowLandingShortens` (`Temp/Slide_Report.md` §2).
-/

namespace SlideCore

open ValleyElim

/-! ## §1. The foundation-row bridge -/

/-- Suit build order is `Nodup`. -/
theorem upCards_nodup' (s : Suit) : (s.upCards).Nodup := by
  cases s <;> decide

/-- The foundation row is `Nodup`. -/
theorem found_nodup {st : State} (hwf : st.WF) (s : Suit) :
    (st.found s).Nodup := by
  obtain ⟨n, hn⟩ := hwf.found_prefix s
  rw [hn]
  exact List.Pairwise.take (i := n) (upCards_nodup' s)

/-- **FOUNDED ⟺ BELOW THE RUNG.** -/
theorem mem_found_iff_rung {st : State} (hwf : st.WF) {c : Card} :
    c ∈ st.found c.suit ↔ c.rank.toIdx < rungAt st c.suit := by
  have h := FoundKit.mem_found_iff_height hwf (c := c)
  simpa [State.foundHeight, rungAt] using h

/-! ## §2. Gain and loss of foundation membership -/

/-- **GAIN FORCES THE RAISE.** -/
theorem raised_of_found_gain {Q W : State} {ρ : List Move} {x : Card}
    (hplay : ShufflePlayW Q ρ W)
    (hQ : x ∉ Q.found x.suit) (hW : x ∈ W.found x.suit) :
    Move.tabToFound x ∈ ρ := by
  by_cases h : Move.tabToFound x ∈ ρ
  · exact h
  · exfalso
    exact (found_not_mem_play_of_not_raise hplay hQ
      (fun k hk hk' => h (hk' ▸ hk))) hW

/-- Foundation membership survives one non-pull letter. -/
theorem found_mem_step_of_not_pull {Q Q1 : State} {m : Move} {x : Card}
    (hplay : ShufflePlayW Q [m] Q1) (hQ : x ∈ Q.found x.suit)
    (hnot : ∀ b : Base, m ≠ Move.foundToTab x b) :
    x ∈ Q1.found x.suit :=
  found_mem_play_of_not_pull hplay hQ (fun k hk b hb => by
    have hk' : k = m := by simpa using hk
    exact hnot b (hk' ▸ hb))

/-- **LOSS FORCES THE PULL** (constructive, by structural induction on the
play — no decidability of an existential is used, so no `Classical.choice`). -/
theorem pulled_of_found_loss {Q W : State} {ρ : List Move} {x : Card}
    (hplay : ShufflePlayW Q ρ W)
    (hQ : x ∈ Q.found x.suit) (hW : x ∉ W.found x.suit) :
    ∃ b : Base, Move.foundToTab x b ∈ ρ := by
  induction ρ generalizing Q with
  | nil =>
      cases hplay
      exact absurd hQ hW
  | cons m t ih =>
      obtain ⟨Q1, hrev, hstep, hrest⟩ := Bubble.walk_cons_inv hplay
      have hone : ShufflePlayW Q [m] Q1 := Walk.cons hrev hstep (Walk.nil Q1)
      cases m with
      | foundToTab c bb =>
          by_cases hcx : c = x
          · subst hcx
            exact ⟨bb, List.mem_cons_self ..⟩
          · have hQ1 : x ∈ Q1.found x.suit :=
              found_mem_step_of_not_pull hone hQ
                (fun b hb => hcx (Move.foundToTab.inj hb).1)
            obtain ⟨b, hb⟩ := ih hrest hQ1
            exact ⟨b, List.mem_cons_of_mem _ hb⟩
      | draw =>
          have hQ1 : x ∈ Q1.found x.suit :=
            found_mem_step_of_not_pull hone hQ (fun b hb => by cases hb)
          obtain ⟨b, hb⟩ := ih hrest hQ1
          exact ⟨b, List.mem_cons_of_mem _ hb⟩
      | tabToFound c =>
          have hQ1 : x ∈ Q1.found x.suit :=
            found_mem_step_of_not_pull hone hQ (fun b hb => by cases hb)
          obtain ⟨b, hb⟩ := ih hrest hQ1
          exact ⟨b, List.mem_cons_of_mem _ hb⟩
      | wasteToFound c =>
          have hQ1 : x ∈ Q1.found x.suit :=
            found_mem_step_of_not_pull hone hQ (fun b hb => by cases hb)
          obtain ⟨b, hb⟩ := ih hrest hQ1
          exact ⟨b, List.mem_cons_of_mem _ hb⟩
      | wasteToTab c bb =>
          have hQ1 : x ∈ Q1.found x.suit :=
            found_mem_step_of_not_pull hone hQ (fun b hb => by cases hb)
          obtain ⟨b, hb⟩ := ih hrest hQ1
          exact ⟨b, List.mem_cons_of_mem _ hb⟩
      | tabToTab c bb =>
          have hQ1 : x ∈ Q1.found x.suit :=
            found_mem_step_of_not_pull hone hQ (fun b hb => by cases hb)
          obtain ⟨b, hb⟩ := ih hrest hQ1
          exact ⟨b, List.mem_cons_of_mem _ hb⟩

/-! ## §3. The pull/raise pairing -/

/-- **SPLITTING A PLAY AT A NAMED LETTER.** -/
theorem step_of_mem_split {Q W : State} {ρ α rest : List Move} {l : Move}
    (hplay : ShufflePlayW Q ρ W) (hρ : ρ = α ++ l :: rest) :
    ∃ P P' : State, ShufflePlayW Q α P ∧ State.step P l = some P' ∧
      ShufflePlayW P' rest W := by
  subst hρ
  obtain ⟨P, hα, hrest⟩ := ShufflePlayW_split hplay α (l :: rest) rfl
  obtain ⟨P', hrev, hstep, htail⟩ := Bubble.walk_cons_inv hrest
  exact ⟨P, P', hα, hstep, htail⟩

/-- A founded card is no pile top, expressed as a `pileOfTop` statement. -/
theorem pileOfTop_none_of_found {st : State} (hwf : st.WF) {c : Card}
    (h : c ∈ st.found c.suit) : st.pileOfTop c = none := by
  cases hp : st.pileOfTop c with
  | none => rfl
  | some k =>
      exact absurd ((pileOfTop_eq_some_iff hwf).mp hp)
        (CommuteStep.not_top_of_found hwf h k)

/-- **A PULL IS A FOUNDATION EXIT.**  If `x` is pulled somewhere in a
raise-free leg, then `x` is founded at the leg's origin and off its
foundation row just after the pull. -/
theorem pull_found_data {u F : State} {left : List Move} {x : Card} {b : Base}
    (huwf : u.WF) (hraiseFree : ∀ m ∈ left, ¬ Bubble.IsRaise m)
    (hleft : ShufflePlayW u left F) (hx : Move.foundToTab x b ∈ left) :
    x ∈ u.found x.suit ∧
      ∃ (α rest : List Move) (P P' : State),
        left = α ++ Move.foundToTab x b :: rest ∧
        ShufflePlayW u α P ∧
        State.step P (Move.foundToTab x b) = some P' ∧
        ShufflePlayW P' rest F ∧
        x ∉ P'.found x.suit := by
  obtain ⟨α, rest, hsplit⟩ := RaiseLeft.exists_split_mem hx
  obtain ⟨P, P', hα, hstep, hrestPlay⟩ := step_of_mem_split hleft hsplit
  obtain ⟨c', htop, hc'x, hcp, hP'⟩ := step_foundToTab_inv hstep
  have hPwf : P.WF := SatDifferCensus.ShufflePlayW.wf_end hα huwf
  have hlastP : lastOf (P.found x.suit) = some x := by
    have h1 : P.foundTop x.suit = some c' := htop
    unfold State.foundTop at h1
    rw [hc'x] at h1
    exact h1
  have hPmem : x ∈ P.found x.suit := lastOf_mem hlastP
  have hnoRaiseα : ∀ k ∈ α, k ≠ Move.tabToFound x := by
    intro k hk hke
    exact hraiseFree k (by rw [hsplit]; exact List.mem_append_left _ hk) ⟨x, hke⟩
  have hmemu : x ∈ u.found x.suit := by
    by_cases hcon : x ∈ u.found x.suit
    · exact hcon
    · exfalso
      exact (found_not_mem_play_of_not_raise hα hcon hnoRaiseα) hPmem
  have hP'not : x ∉ P'.found x.suit := by
    rw [hP']
    rw [show ((P.setFound x.suit (chop (P.found x.suit))).putCard x b).found x.suit
          = chop (P.found x.suit) from by
      cases b with
      | inl a => rw [putCard_inl_found, setFound_found_self]
      | inr z => rw [putCard_inr_found, setFound_found_self]]
    exact CommuteStep.not_mem_chop_of_last (found_nodup hPwf x.suit) hlastP
  exact ⟨hmemu, α, rest, P, P', hsplit, hα, hstep, hrestPlay, hP'not⟩

/-- **THE PULL/RAISE PAIRING, FORWARD.**  Every card pulled in the left leg of
an equal-rung `MountainSplit` is raised in the right leg. -/
theorem pulled_imp_raised
    {u v : State} {ρ : List Move} {F : State} {left right : List Move}
    {c d : Card} {b : Base} {pre post tail : List Move}
    (heq : ∀ σ : Suit, rungAt u σ = rungAt v σ)
    (hs : SplitKit.SplitHyp u v ρ F left right c d b pre post tail)
    (hms : MountainKit.MountainSplit left right)
    {x : Card} {bx : Base} (hx : Move.foundToTab x bx ∈ left) :
    Move.tabToFound x ∈ right := by
  obtain ⟨huwf, -, -, hplay, -, -, -, hleft, hright, -, hfree, -⟩ := hs
  have hvwf : v.WF := SatDifferCensus.ShufflePlayW.wf_end hplay huwf
  obtain ⟨hmemu, α, rest, P, P', hsplit, hα, hstep, hrestPlay, hP'not⟩ :=
    pull_found_data huwf hms.1 hleft hx
  have hrestNot : x ∉ F.found x.suit := by
    refine (found_not_mem_play_of_not_raise hrestPlay hP'not) ?_
    intro k hk hke
    exact hms.1 k (by
      rw [hsplit]; exact List.mem_append_right _ (List.mem_cons_of_mem _ hk))
      ⟨x, hke⟩
  have hvmem : x ∈ v.found x.suit := by
    refine (mem_found_iff_rung hvwf).mpr ?_
    rw [← heq x.suit]
    exact (mem_found_iff_rung huwf).mp hmemu
  exact raised_of_found_gain hright hrestNot hvmem

/-- **THE PULL/RAISE PAIRING, BACKWARD.**  Every card raised in the right leg
of an equal-rung `MountainSplit` is pulled in the left leg. -/
theorem raised_imp_pulled
    {u v : State} {ρ : List Move} {F : State} {left right : List Move}
    {c d : Card} {b : Base} {pre post tail : List Move}
    (heq : ∀ σ : Suit, rungAt u σ = rungAt v σ)
    (hs : SplitKit.SplitHyp u v ρ F left right c d b pre post tail)
    (hms : MountainKit.MountainSplit left right)
    {x : Card} (hx : Move.tabToFound x ∈ right) :
    ∃ bx : Base, Move.foundToTab x bx ∈ left := by
  obtain ⟨huwf, -, -, hplay, -, -, -, hleft, hright, -, hfree, -⟩ := hs
  have hFwf : F.WF := SatDifferCensus.ShufflePlayW.wf_end hleft huwf
  have hvwf : v.WF := SatDifferCensus.ShufflePlayW.wf_end hplay huwf
  obtain ⟨α, rest, hsplit⟩ := RaiseLeft.exists_split_mem hx
  obtain ⟨A, B, hα, hstep, hBrest⟩ := step_of_mem_split hright hsplit
  have hAwf : A.WF := SatDifferCensus.ShufflePlayW.wf_end hα hFwf
  obtain ⟨-, a, hpa, hsB⟩ := step_tabToFound_inv hstep
  -- `x` is a pile top at `A`, so not founded there
  have hAnot : x ∉ A.found x.suit := by
    intro hmem
    rw [pileOfTop_none_of_found hAwf hmem] at hpa
    exact absurd hpa (by simp)
  -- the raise puts `x` on the row, and the pull-free rest keeps it there
  have hBmem : x ∈ B.found x.suit := by
    obtain ⟨hfound, -, -⟩ := tabToFound_found_trio (a := a) hsB
    rw [hfound]
    exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
  have hnoPullRest : ∀ k ∈ rest, ∀ (y : Card) (bb : Base),
      k ≠ Move.foundToTab y bb := by
    intro k hk y bb hke
    exact hms.2 k (by
      rw [hsplit]; exact List.mem_append_right _ (List.mem_cons_of_mem _ hk))
      ⟨y, bb, hke⟩
  have hvmem : x ∈ v.found x.suit :=
    found_mem_play_of_not_pull hBrest hBmem
      (fun k hk b' hb' => hnoPullRest k hk x b' hb')
  -- so `x` is founded at `u` (equal rungs), and not at `F`
  have hmemu : x ∈ u.found x.suit := by
    refine (mem_found_iff_rung huwf).mpr ?_
    rw [heq x.suit]
    exact (mem_found_iff_rung hvwf).mp hvmem
  have hnoPullα : ∀ k ∈ α, ∀ (y : Card) (bb : Base),
      k ≠ Move.foundToTab y bb := by
    intro k hk y bb hke
    exact hms.2 k (by
      rw [hsplit]; exact List.mem_append_left _ hk) ⟨y, bb, hke⟩
  have hFnot : x ∉ F.found x.suit := by
    intro hmem
    exact hAnot (found_mem_play_of_not_pull hα hmem
      (fun k hk b' hb' => hnoPullα k hk x b' hb'))
  exact pulled_of_found_loss hleft hmemu hFnot

/-- **THE PULL/RAISE PAIRING.**  At an equal-rung `MountainSplit`, a card is
pulled in the left leg **iff** it is raised in the right leg. -/
theorem paired_iff
    {u v : State} {ρ : List Move} {F : State} {left right : List Move}
    {c d : Card} {b : Base} {pre post tail : List Move}
    (heq : ∀ σ : Suit, rungAt u σ = rungAt v σ)
    (hs : SplitKit.SplitHyp u v ρ F left right c d b pre post tail)
    (hms : MountainKit.MountainSplit left right)
    (x : Card) :
    (∃ bx : Base, Move.foundToTab x bx ∈ left) ↔ Move.tabToFound x ∈ right :=
  ⟨fun ⟨bx, hx⟩ => pulled_imp_raised heq hs hms hx,
   fun hx => raised_imp_pulled heq hs hms hx⟩

/-! ## §3b. Corollaries of the pairing -/

/-- **EVERY RIGHT-LEG RAISE CARD WAS ALREADY FOUNDED AT `u`.**  The right leg
cannot raise a card that sat in the tableau at the origin. -/
theorem raised_mem_found_u
    {u v : State} {ρ : List Move} {F : State} {left right : List Move}
    {c d : Card} {b : Base} {pre post tail : List Move}
    (heq : ∀ σ : Suit, rungAt u σ = rungAt v σ)
    (hs : SplitKit.SplitHyp u v ρ F left right c d b pre post tail)
    (hms : MountainKit.MountainSplit left right)
    {x : Card} (hx : Move.tabToFound x ∈ right) :
    x ∈ u.found x.suit := by
  obtain ⟨bx, hbx⟩ := raised_imp_pulled heq hs hms hx
  obtain ⟨huwf, -, -, -, -, -, -, hleft, -, -, -, -⟩ := hs
  obtain ⟨hmemu, -⟩ := pull_found_data huwf hms.1 hleft hbx
  exact hmemu

/-- **THE RIGHT-LEG RAISE SET IS THE `pre`-PULL SET.**  For a card `x` that is
not the split card, being raised in the right leg is *equivalent* to being
pulled in `pre`.  (`raise c` itself corresponds to the split's own pull.) -/
theorem raised_iff_pulled_pre
    {u v : State} {ρ : List Move} {F : State} {left right : List Move}
    {c d : Card} {b : Base} {pre post tail : List Move}
    (heq : ∀ σ : Suit, rungAt u σ = rungAt v σ)
    (hs : SplitKit.SplitHyp u v ρ F left right c d b pre post tail)
    (hms : MountainKit.MountainSplit left right)
    {x : Card} (hxc : x ≠ c) :
    Move.tabToFound x ∈ right ↔ ∃ bx : Base, Move.foundToTab x bx ∈ pre := by
  constructor
  · intro hx
    obtain ⟨bx, hbx⟩ := raised_imp_pulled heq hs hms hx
    have hρ : ρ = left ++ right := hs.2.2.2.2.2.2.1
    have hmemρ : Move.foundToTab x bx ∈ ρ := by
      rw [hρ]; exact List.mem_append_left _ hbx
    rcases MateGate.pull_mem_pre_or_eq hs hms hmemρ with h | ⟨h1, h2⟩
    · exact ⟨bx, h⟩
    · exact absurd h1 hxc
  · rintro ⟨bx, hbx⟩
    have hleft : left = pre ++ Move.foundToTab c b :: post :=
      hs.2.2.2.2.2.2.2.2.2.1
    exact pulled_imp_raised heq hs hms (bx := bx) (by
      rw [hleft]
      exact List.mem_append_left _ hbx)

/-! ## §4. The anatomy of a base-clause violation -/

/-- **A WINDOW LANDER HAS RANK `c.rank - 1`.** -/
theorem window_landing_rank {st : State} {x c : Card}
    (h : st.canPlace x (Sum.inr c) = true) :
    x.rank.toIdx + 1 = c.rank.toIdx ∧ x.suit.color ≠ c.suit.color := by
  obtain ⟨k, hk, hfit⟩ := canPlace_inr h
  exact (canSitOn_eq x c).mp hfit

/-- **THE HEAD-CLAUSE ANATOMY.**  `c` only ever sits on a card of rank
`c.rank + 1` in the opposite colour; exactly two cards have that profile, and
they are twins.  So a slide of `c` re-lands it on the card it was pulled onto,
or on that card's twin. -/
theorem slide_base_is_pull_base_or_twin {c z w : Card}
    (hz : canSitOn c z = true) (hw : canSitOn c w = true) :
    w = z ∨ w = z.twin :=
  tfc_fitting_parent hw hz

/-- **A WINDOW LANDER'S PULL IS IN `pre`.**  If a window slide lands `x` on
`c` and `x` is raised in the right leg, then `x` is pulled in `pre`: the pull
cannot be the split's own pull, because the ranks differ. -/
theorem window_landing_pulled
    {u v : State} {ρ : List Move} {F : State} {left right : List Move}
    {c d : Card} {b : Base} {pre post tail : List Move} {γ β : List Move}
    (heq : ∀ σ : Suit, rungAt u σ = rungAt v σ)
    (hs : SplitKit.SplitHyp u v ρ F left right c d b pre post tail)
    (hms : MountainKit.MountainSplit left right)
    (hrightEq : right = γ ++ Move.tabToFound c :: β)
    {x : Card} (hrank : x.rank.toIdx + 1 = c.rank.toIdx)
    (hbγ : ∃ bγ : Base, Move.tabToTab x bγ ∈ post ++ γ)
    (hraised : Move.tabToFound x ∈ right) :
    ∃ bx : Base, Move.foundToTab x bx ∈ pre := by
  obtain ⟨bx, hbx⟩ := raised_imp_pulled heq hs hms hraised
  have hρ : ρ = left ++ right := hs.2.2.2.2.2.2.1
  have hmemρ : Move.foundToTab x bx ∈ ρ := by
    rw [hρ]
    exact List.mem_append_left _ hbx
  refine ⟨bx, ?_⟩
  rcases MateGate.pull_mem_pre_or_eq hs hms hmemρ with h | ⟨hxc, hb⟩
  · exact h
  · exfalso
    rw [hxc] at hrank
    omega

/-! ## §5. The exact residual, in length form

`EqualRungInteriorBaseFree` (clause (b) alone) is *exactly* the statement that a
window landing on `c` shortens the play: the base clause is a `∀` over the
window letters, the shortening form is a `length` inequality.  Both directions
are kernel-checked below, so nothing is lost or gained by the reformulation —
and the shortening form is what a cover/uncover net-zero has to deliver
(`LandRes.slideSt_slideSt_self`). -/

/-- **`EqualRungWindowLandingShortens` — THE BASE CLAUSE, IN LENGTH FORM.**
Every window slide landing on `c` gives a shorter witness play from `u` to `v`. -/
def EqualRungWindowLandingShortens : Prop :=
  ∀ (u v : State) (ρ : List Move) (F : State)
    (left right : List Move) (c d : Card) (b : Base)
    (pre post tail : List Move),
    (∀ σ : Suit, rungAt u σ = rungAt v σ) →
    SplitKit.SplitHyp u v ρ F left right c d b pre post tail →
    MountainKit.MountainSplit left right →
    ∀ (γ β : List Move), right = γ ++ Move.tabToFound c :: β →
      ∀ (x : Card) (bγ : Base),
        Move.tabToTab x (Sum.inr c) ∈ post ++ γ →
        ∃ ρ' : List Move, ShufflePlayW u ρ' v ∧ ρ'.length < ρ.length

/-- **THE SHORTENING FORM GIVES THE BASE CLAUSE.** -/
theorem no_window_landing_of_shortens (h : EqualRungWindowLandingShortens)
    {u v : State} {ρ : List Move} {F : State} {left right : List Move}
    {c d : Card} {b : Base} {pre post tail : List Move} {γ β : List Move}
    (heq : ∀ σ : Suit, rungAt u σ = rungAt v σ)
    (hs : SplitKit.SplitHyp u v ρ F left right c d b pre post tail)
    (hms : MountainKit.MountainSplit left right)
    (hrightEq : right = γ ++ Move.tabToFound c :: β) :
    ∀ x : Card, Move.tabToTab x (Sum.inr c) ∉ post ++ γ := by
  intro x hx
  have hmin : ∀ ρ' : List Move, ShufflePlayW u ρ' v → ρ.length ≤ ρ'.length := hs.2.2.2.2.2.1
  obtain ⟨ρ', hplay', hlen⟩ :=
    h u v ρ F left right c d b pre post tail heq hs hms γ β hrightEq x (Sum.inr c) hx
  exact absurd hlen (Nat.not_lt.mpr (hmin ρ' hplay'))

/-- **THE BASE CLAUSE GIVES THE SHORTENING FORM** (vacuously: the landing is
refuted). -/
theorem shortens_of_no_window_landing
    (hbase : ∀ (u v : State) (ρ : List Move) (F : State)
      (left right : List Move) (c d : Card) (b : Base)
      (pre post tail : List Move),
      SplitKit.SplitHyp u v ρ F left right c d b pre post tail →
      ∀ (γ β : List Move), right = γ ++ Move.tabToFound c :: β →
        ∀ x : Card, Move.tabToTab x (Sum.inr c) ∉ post ++ γ) :
    EqualRungWindowLandingShortens := by
  intro u v ρ F left right c d b pre post tail heq hs hms γ β hrightEq x bγ hx
  exact absurd hx (hbase u v ρ F left right c d b pre post tail hs γ β hrightEq x)

/-- **THE REDUCTION, WITH THE HEAD CLAUSE KEPT AND THE BASE CLAUSE IN LENGTH
FORM.**  `EqualRungInteriorHeadFree` + `EqualRungWindowLandingShortens` gives
`EqSplit.EqualRungInteriorSlideFree`. -/
theorem slideFree_of_headFree_of_shortens
    (hhead : EqSplit.EqualRungInteriorHeadFree)
    (hshort : EqualRungWindowLandingShortens) :
    EqSplit.EqualRungInteriorSlideFree := by
  intro u v ρ F left right c d b pre post tail heq hs hms
  obtain ⟨γ, β, hrightEq, hfirst, hnoslide⟩ :=
    hhead u v ρ F left right c d b pre post tail heq hs hms
  refine ⟨γ, β, hrightEq, hfirst, hnoslide, ?_⟩
  exact no_window_landing_of_shortens hshort heq hs hms hrightEq

end SlideCore

#print axioms SlideCore.upCards_nodup'
#print axioms SlideCore.found_nodup
#print axioms SlideCore.mem_found_iff_rung
#print axioms SlideCore.raised_of_found_gain
#print axioms SlideCore.pulled_of_found_loss
#print axioms SlideCore.step_of_mem_split
#print axioms SlideCore.pileOfTop_none_of_found
#print axioms SlideCore.pull_found_data
#print axioms SlideCore.pulled_imp_raised
#print axioms SlideCore.raised_imp_pulled
#print axioms SlideCore.paired_iff
#print axioms SlideCore.raised_mem_found_u
#print axioms SlideCore.raised_iff_pulled_pre
#print axioms SlideCore.window_landing_rank
#print axioms SlideCore.slide_base_is_pull_base_or_twin
#print axioms SlideCore.window_landing_pulled
#print axioms SlideCore.EqualRungWindowLandingShortens
#print axioms SlideCore.no_window_landing_of_shortens
#print axioms SlideCore.shortens_of_no_window_landing
#print axioms SlideCore.slideFree_of_headFree_of_shortens
