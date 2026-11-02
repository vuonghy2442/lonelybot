import Orig2.Fork.ForkLedger
import Orig2.Fork.ForkLandingLocal
import Orig2.Fork.ForkLanding
import Orig2.Fork.ForkSplitResidual

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

/-!
# Orig2/ForkThirdCrossing — what the pull crossing and the frozen branch force

READ-ONLY scratch (no source touched, no commit).  Zero `sorry`, zero
`Classical.choice`, zero `native_decide`; battery at the tail.

## What is proved here

1. `NoSigmaLetter` / `noSigma_iff_counts` — the ledger's letter notion
   ("`σ`-pull or `σ`-raise") as an explicit per-letter predicate.

2. `crossing_counts_zero` — **THE CROSSING IS `σ`-SILENT.**  For a third
   suit `σ ≠ c.suit`, the pull crossing `pull c ; post` (pull + free tail)
   contains no `σ`-pull and no `σ`-raise: the pull is `c`'s letter, and free
   letters are invisible to the ledger.

3. `rungAt_const_of_noSigma` / `nextUp_const_of_noSigma` — **A `σ`-SILENT
   STRETCH FREEZES `σ`.**  Along any witness stretch with no `σ`-pull and
   no `σ`-raise, the `σ`-rung is constant and hence every `σ`-card's
   `nextUp` is constant.  In particular, on the split's pull crossing
   (`A' → B → F`) a third-suit live card is `nextUp` at ALL THREE states:
   the crossing cannot even move the frontier.

4. `frozen_branch_nextUp_at_end` — **THE FAR ENDPOINT IS `nextUp` ON `e`
   IN THE FROZEN BRANCH.**  If the third suit's rung is unchanged from the
   bottom to the far endpoint (`rungAt v σ = rungAt F σ`), then `e` is
   `nextUp` at `v` — while `SSaturated v` says `e` is not live there.  So in
   this branch `e`'s death is *purely* a seat/exposure death (a cover or a
   twin-top event), never a raise of `e` and never a `σ`-letter.

5. `third_frontier_nextUp` — the same fingerprint in `nextUp` form.
-/

namespace ThirdLive

open ValleyElim

/-! ## §0. The letter notion of the ledger -/

/-- **`NoSigmaLetter σ m`** — `m` is neither a pull nor a raise of a `σ`-card.
Free letters (draws, slides) always satisfy it; the ledger only counts
`foundToTab`/`tabToFound`. -/
def NoSigmaLetter (σ : Suit) (m : Move) : Prop :=
  (∀ (c : Card) (b : Base), m = Move.foundToTab c b → c.suit ≠ σ) ∧
    (∀ c : Card, m = Move.tabToFound c → c.suit ≠ σ)

/-- A free letter is `σ`-silent. -/
theorem noSigma_of_free {σ : Suit} {m : Move} (h : FreeMove m) :
    NoSigmaLetter σ m := by
  rcases h with rfl | ⟨c, b, rfl⟩
  · exact ⟨fun c' b' hc => absurd hc (by simp), fun c' hc => absurd hc (by simp)⟩
  · exact ⟨fun c' b' hc => absurd hc (by simp), fun c' hc => absurd hc (by simp)⟩

/-- **`σ`-silence is exactly the vanishing of both ledger counts.** -/
theorem noSigma_iff_counts {play : List Move} {σ : Suit} :
    (∀ m ∈ play, NoSigmaLetter σ m) ↔
      (pullsOf play σ = 0 ∧ raisesOf play σ = 0) := by
  constructor
  · intro hall
    induction play with
    | nil => simp [pullsOf, raisesOf]
    | cons m t ih =>
        have htail : ∀ x ∈ t, NoSigmaLetter σ x :=
          fun x hx => hall x (List.mem_cons_of_mem m hx)
        obtain ⟨hp, hr⟩ := ih htail
        have hm := hall m (List.mem_cons_self ..)
        cases m with
        | draw => simpa [pullsOf, raisesOf] using ⟨hp, hr⟩
        | wasteToFound c => simpa [pullsOf, raisesOf] using ⟨hp, hr⟩
        | wasteToTab c b => simpa [pullsOf, raisesOf] using ⟨hp, hr⟩
        | foundToTab c b =>
            have hcs : c.suit ≠ σ := hm.1 c b rfl
            have hif : (if c.suit = σ then 1 else 0) = 0 := by
              rw [ite_eq_right hcs]
            simp only [pullsOf, raisesOf, hif, Nat.zero_add]
            exact ⟨hp, hr⟩
        | tabToFound c =>
            have hcs : c.suit ≠ σ := hm.2 c rfl
            have hif : (if c.suit = σ then 1 else 0) = 0 := by
              rw [ite_eq_right hcs]
            simp only [raisesOf, pullsOf, hif, Nat.zero_add]
            exact ⟨hp, hr⟩
        | tabToTab c b => simpa [pullsOf, raisesOf] using ⟨hp, hr⟩
  · rintro ⟨hp, hr⟩ m hm
    refine ⟨?_, ?_⟩
    · intro c' b' hmb hcs
      have : 0 < pullsOf play σ :=
        LedgerKit.pullsOf_pos_iff.mpr ⟨c', b', hcs, by rw [← hmb]; exact hm⟩
      omega
    · intro c' hmb hcs
      have : 0 < raisesOf play σ :=
        LedgerKit.raisesOf_pos_iff.mpr ⟨c', hcs, by rw [← hmb]; exact hm⟩
      omega

/-! ## §1. The `σ`-silent stretch freezes `σ` -/

/-- **A `σ`-SILENT WITNESS STRETCH PRESERVES THE `σ`-RUNG.** -/
theorem rungAt_const_of_noSigma {u v : State} {play : List Move} {σ : Suit}
    (hplay : ShufflePlayW u play v) (hno : ∀ m ∈ play, NoSigmaLetter σ m) :
    rungAt v σ = rungAt u σ := by
  induction hplay with
  | nil => rfl
  | @cons st s1 W m rest _hrev hstep _hrest ih =>
      have htail : ∀ x ∈ rest, NoSigmaLetter σ x :=
        fun x hx => hno x (List.mem_cons_of_mem m hx)
      have hIH := ih htail
      have hm := hno m (List.mem_cons_self ..)
      cases m with
      | draw => rw [hIH, rungAt_draw hstep σ]
      | wasteToFound c => exact absurd _hrev (wasteToFound_not_reversibleAtW st c)
      | wasteToTab c b => exact absurd _hrev (wasteToTab_not_reversibleAtW st c b)
      | tabToTab c b => rw [hIH, rungAt_tabToTab hstep σ]
      | foundToTab c b =>
          have hcs : c.suit ≠ σ := hm.1 c b rfl
          rw [hIH, rungAt_foundToTab hstep σ,
            ite_eq_right (fun h : σ = c.suit => hcs h.symm)]
      | tabToFound c =>
          have hcs : c.suit ≠ σ := hm.2 c rfl
          rw [hIH, rungAt_tabToFound hstep σ,
            ite_eq_right (fun h : σ = c.suit => hcs h.symm)]

/-- **A `σ`-SILENT WITNESS STRETCH PRESERVES `nextUp` ON `σ`-CARDS.** -/
theorem nextUp_const_of_noSigma {u v : State} {play : List Move} {σ : Suit}
    (hplay : ShufflePlayW u play v) (hno : ∀ m ∈ play, NoSigmaLetter σ m)
    {e : Card} (he : e.suit = σ) : v.nextUp e = u.nextUp e := by
  have hconst : rungAt v σ = rungAt u σ := rungAt_const_of_noSigma hplay hno
  have h1 : rungAt v e.suit = rungAt u e.suit := by rw [he]; exact hconst
  unfold State.nextUp State.foundHeight
  rw [show (v.found e.suit).length = rungAt v e.suit from rfl,
    show (u.found e.suit).length = rungAt u e.suit from rfl, h1]

/-! ## §2. The pull crossing is `σ`-silent -/

/-- The free tail is `σ`-silent for every suit. -/
theorem free_play_noSigma {B F : State} {post : List Move} (hplay : ShufflePlayW B post F)
    (hfree : ∀ m ∈ post, FreeMove m) (σ : Suit) :
    ∀ m ∈ post, NoSigmaLetter σ m :=
  fun m hm => noSigma_of_free (hfree m hm)

/-- **THE CROSSING IS `σ`-SILENT.**  A pull of `c` followed by a free tail
carries no `σ`-pull and no `σ`-raise for any third suit `σ ≠ c.suit`. -/
theorem crossing_noSigma {B F : State} {c : Card} {b : Base} {post : List Move}
    (hpost : ShufflePlayW B post F) (hfree : ∀ m ∈ post, FreeMove m)
    {σ : Suit} (hσ : σ ≠ c.suit) :
    ∀ m ∈ (Move.foundToTab c b :: post), NoSigmaLetter σ m := by
  intro m hm
  rcases List.mem_cons.mp hm with rfl | hm
  · refine ⟨?_, ?_⟩
    · rintro c' b' hc hcs
      injection hc with hc1 hc2
      subst hc1
      exact hσ hcs.symm
    · rintro c' hc
      exact absurd hc (by simp)
  · exact noSigma_of_free (hfree m hm)

/-- The same in ledger-count form. -/
theorem crossing_counts_zero {B F : State} {c : Card} {b : Base}
    {post : List Move} (hpost : ShufflePlayW B post F)
    (hfree : ∀ m ∈ post, FreeMove m) {σ : Suit} (hσ : σ ≠ c.suit) :
    pullsOf (Move.foundToTab c b :: post) σ = 0 ∧
      raisesOf (Move.foundToTab c b :: post) σ = 0 :=
  noSigma_iff_counts.mp (crossing_noSigma hpost hfree hσ)

/-! ## §3. The frozen branch at the far endpoint -/

/-- **THE FAR ENDPOINT IS `nextUp` ON `e` IN THE FROZEN BRANCH.**  If the
third suit's rung does not move from the bottom `F` to the far endpoint `v`,
then `nextUp e` is still `true` at `v`.  With `SSaturated v` (nothing live at
`v`) this says `e` was killed without any `e`-suit letter: the kill is a
seat/exposure event, not a raise of `e`. -/
theorem frozen_branch_nextUp_at_end {F v : State} {right : List Move} {σ : Suit}
    (hplay : ShufflePlayW F right v)
    (hno : ∀ m ∈ right, NoSigmaLetter σ m) {e : Card} (he : e.suit = σ)
    (hnextF : F.nextUp e = true) : v.nextUp e = true := by
  rw [nextUp_const_of_noSigma hplay hno he]
  exact hnextF

/-- The same read at the split: if the third suit comes back to its bottom
rung on the right leg, then `e` is `nextUp` at the far endpoint. -/
theorem frozen_branch_nextUp_at_end_of_rung {F v : State} {right : List Move} {σ : Suit}
    (hplay : ShufflePlayW F right v)
    (hnoPull : ∀ m ∈ right, ¬ Bubble.IsPull m) (hrung : rungAt v σ = rungAt F σ)
    {e : Card} (he : e.suit = σ) (hrank : e.rank.toIdx = rungAt F σ) :
    v.nextUp e = true := by
  have hp0 : pullsOf right σ = 0 := by
    cases hp : pullsOf right σ with
    | zero => rfl
    | succ k =>
        have hpos : 0 < pullsOf right σ := by rw [hp]; omega
        obtain ⟨c', b', hcs, hmem⟩ := LedgerKit.pullsOf_pos_iff.mp hpos
        exact absurd ⟨c', b', rfl⟩ (hnoPull _ hmem)
  have hr0 : raisesOf right σ = 0 := by
    have hled := LedgerKit.rungAt_ledger (u := F) (v := v) (ρ := right) (σ := σ) hplay
    omega
  have hno : ∀ m ∈ right, NoSigmaLetter σ m :=
    noSigma_iff_counts.mpr ⟨hp0, hr0⟩
  have hnextF : F.nextUp e = true := by
    unfold State.nextUp
    rw [show F.foundHeight e.suit = rungAt F σ from by rw [he]; rfl, hrank]
    exact decide_eq_true rfl
  exact frozen_branch_nextUp_at_end hplay hno he hnextF

/-- **THE FINGERPRINT IN `nextUp` FORM** — an S-live card is next-up. -/
theorem nextUp_of_live {st : State} (hwf : st.WF) {e : Card} (he : CanRaiseS st e) :
    st.nextUp e = true :=
  ((LandKit.canRaiseS_below_form hwf).mp he).1

/-! ## §4. The split-level capstone -/

/-- The rank fingerprint (a local restatement of
`ThirdLive.rank_eq_rungAt_of_canRaiseS`). -/
theorem rank_eq_rungAt_of_live {st : State} (hwf : st.WF) {e : Card}
    (he : CanRaiseS st e) : e.rank.toIdx = rungAt st e.suit := by
  have h := of_decide_eq_true (nextUp_of_live hwf he)
  simpa [State.nextUp, State.foundHeight, rungAt] using h

/-- **THE STRUCTURE OF A SURVIVING THIRD-SUIT CARD.**  At a genuine valley
split, a third-suit card `e` that is S-live at the pull's landing is:

* the frontier card of its own suit at `A'`, at `B` and at `F`
  (`e.rank.toIdx = rungAt · e.suit`), so it is `nextUp` at all three;
* untouched by the crossing: the stretch `pull c ; post` carries no
  `e.suit`-pull and no `e.suit`-raise.

Nothing here uses minimality: this is the *local* content of the violation. -/
theorem third_survivor_structure
    {u v : State} {ρ : List Move} {F : State} {left right : List Move}
    {c d : Card} {b : Base} {pre post tail : List Move}
    (h : SplitKit.SplitHyp u v ρ F left right c d b pre post tail)
    {A' B : State} (hpre : ShufflePlayW u pre A')
    (hstep : State.step A' (Move.foundToTab c b) = some B)
    {e : Card} (he : CanRaiseS B e) (hec : e ≠ c) (het : e ≠ c.twin)
    (hsuit : e.suit ≠ c.suit) :
    e.rank.toIdx = rungAt A' e.suit ∧ e.rank.toIdx = rungAt B e.suit ∧
      e.rank.toIdx = rungAt F e.suit ∧
      (∀ m ∈ (Move.foundToTab c b :: post), NoSigmaLetter e.suit m) ∧
      A'.nextUp e = true ∧ B.nextUp e = true ∧ F.nextUp e = true := by
  obtain ⟨huwf, hsu, hsv, hplay, hvs, hmin, hρeq, hleft, hright, hshape,
    hfree, hrt⟩ := h
  have hA' : A'.WF := SatDifferCensus.ShufflePlayW.wf_end hpre huwf
  have hB : B.WF := step_wf hA' hstep
  obtain ⟨hpost, -⟩ := Landing.post_play_of_landing ⟨huwf, hsu, hsv, hplay, hvs,
    hmin, hρeq, hleft, hright, hshape, hfree, hrt⟩ hpre hstep
  have hF : F.WF := SatDifferCensus.ShufflePlayW.wf_end hpost hB
  have hBrank : e.rank.toIdx = rungAt B e.suit := rank_eq_rungAt_of_live hB he
  have hliveA : CanRaiseS A' e := by
    rcases LandKit.local_dichotomy hA' hstep he hec with htw | hA
    · exact absurd htw het
    · exact hA
  have hArank : e.rank.toIdx = rungAt A' e.suit := rank_eq_rungAt_of_live hA' hliveA
  have hAB : rungAt B e.suit = rungAt A' e.suit :=
    (rungAt_foundToTab hstep e.suit) ▸ (ite_eq_right (fun hce : e.suit = c.suit => hsuit hce))
  have hBF : rungAt F e.suit = rungAt B e.suit :=
    rungAt_eq_of_free_play hpost hfree e.suit
  have hFrank : e.rank.toIdx = rungAt F e.suit := by rw [hBF, hAB, ← hArank]
  have hnextA : A'.nextUp e = true := by
    unfold State.nextUp State.foundHeight
    rw [show (A'.found e.suit).length = rungAt A' e.suit from rfl, hArank]
    exact decide_eq_true rfl
  have hnextB : B.nextUp e = true := by
    unfold State.nextUp State.foundHeight
    rw [show (B.found e.suit).length = rungAt B e.suit from rfl, hBrank]
    exact decide_eq_true rfl
  have hnextF : F.nextUp e = true := by
    unfold State.nextUp State.foundHeight
    rw [show (F.found e.suit).length = rungAt F e.suit from rfl, hFrank]
    exact decide_eq_true rfl
  exact ⟨hArank, hBrank, hFrank,
    crossing_noSigma hpost hfree hsuit, hnextA, hnextB, hnextF⟩

end ThirdLive

#print axioms ThirdLive.NoSigmaLetter
#print axioms ThirdLive.noSigma_of_free
#print axioms ThirdLive.noSigma_iff_counts
#print axioms ThirdLive.rungAt_const_of_noSigma
#print axioms ThirdLive.nextUp_const_of_noSigma
#print axioms ThirdLive.free_play_noSigma
#print axioms ThirdLive.crossing_noSigma
#print axioms ThirdLive.crossing_counts_zero
#print axioms ThirdLive.frozen_branch_nextUp_at_end
#print axioms ThirdLive.frozen_branch_nextUp_at_end_of_rung
#print axioms ThirdLive.nextUp_of_live
#print axioms ThirdLive.rank_eq_rungAt_of_live
#print axioms ThirdLive.third_survivor_structure
