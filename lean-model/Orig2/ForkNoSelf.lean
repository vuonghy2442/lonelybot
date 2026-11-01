import Orig2.ForkSlideFwd

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-!
# Orig2/ForkNoSelf — `EmptyTailNoSelfSlide`, discharged

READ-ONLY scratch card (no source edits, no commit).  Zero `sorry`, zero
`Classical.choice`, no `native_decide`.

## What is proved

`SlideFwd.EmptyTailNoSelfSlide` (`Orig2/ForkSlideFwd.lean:807`) is PROVED here,
under the campaign's two standing inputs `SplitLivePair` and
`MountainKit.MountainSplit` — the same inputs every other row of the chain
already takes (`SlideFwd.satDifferForkWF_of_noSelfSlide`).

## The argument, and where the census bites

Let `s = tabToTab c b'` be the LAST slide of `c` in the window `gamma`, and
`gamma = alpha ++ s :: delta`.  Two facts are needed, and the census
(`Temp/NoSelf_probe.py`) shows they are exactly what the general window does
NOT give and the empty-tail geometry DOES:

* `c` is a PILE TOP at the state before `s` (so `s` moves the singleton `[c]`
  and `raise c` is legal right there);
* every letter of `delta` is `ReadSafe c` (no pull/raise in `c`'s suit, no
  letter landing on `c`, no slide headed by `c`).

In the empty-tail geometry nothing ever lands on `c` (`EmptyTail.twin_no_coverSlide`
through `SlideFwd.emptyTail_window_soft`) and the right leg is pull-free, so
`c` stays a bare top.

Given those, the deletion has two halves:

1. **net-zero core** (`raiseSt_slideSt_self`): at a `WF` state where `c` is a
   pile top, `s ; raise c` and `raise c` alone land on the SAME state;
2. **bubble** (`selfSlide_shortens`): `delta` is read-safe, so `raise c`
   bubbles to the front of `delta` (`SlideFwd.raiseSwaps_of_readSafe`), landing
   exactly on the state of (1); the play `s ; delta ; raise c` is replaced by
   the strictly shorter `raise c ; delta` with the SAME endpoint.

That contradicts `SplitHyp`'s shortest-play conjunct, so no such `s` exists.
-/

namespace NoSelfKit

open SplitKit
open SlideFwd
open NonforkKit

/-! ## §1. The last self-slide -/

/-- Computable "is a slide headed by `c`" (keeps the split constructive: no
`Classical.choice` through a `by_cases` on an existential). -/
def isSelfSlideB (c : Card) : Move → Bool
  | Move.tabToTab w _ => decide (w = c)
  | _ => false

theorem isSelfSlideB_eq_true_iff {c : Card} {q : Move} :
    isSelfSlideB c q = true ↔ ∃ b : Base, q = Move.tabToTab c b := by
  cases q with
  | tabToTab w b =>
      show decide (w = c) = true ↔ ∃ b' : Base, Move.tabToTab w b = Move.tabToTab c b'
      constructor
      · intro h
        exact ⟨b, by rw [of_decide_eq_true h]⟩
      · rintro ⟨b', h⟩
        cases h
        exact decide_eq_true rfl
  | draw => simp [isSelfSlideB]
  | wasteToFound x => simp [isSelfSlideB]
  | wasteToTab x b => simp [isSelfSlideB]
  | tabToFound x => simp [isSelfSlideB]
  | foundToTab x b => simp [isSelfSlideB]

/-- Either the window has no slide headed by `c`, or it splits at its LAST
such slide, and the suffix has none. -/
theorem noSlideOf_or_last (c : Card) :
    ∀ l : List Move,
      SlideFwd.NoSlideOf c l ∨
      ∃ (α : List Move) (b : Base) (δ : List Move),
        l = α ++ Move.tabToTab c b :: δ ∧ SlideFwd.NoSlideOf c δ := by
  intro l
  induction l with
  | nil =>
      exact Or.inl (fun w b h => absurd h (List.not_mem_nil))
  | cons q t ih =>
      rcases ih with h | ⟨α, b, δ, ht, hδ⟩
      · by_cases hq : isSelfSlideB c q = true
        · obtain ⟨b, rfl⟩ := isSelfSlideB_eq_true_iff.mp hq
          exact Or.inr ⟨[], b, t, rfl, h⟩
        · refine Or.inl ?_
          intro w b hw
          rcases List.mem_cons.mp hw with rfl | hw'
          · exact fun hwc => hq (isSelfSlideB_eq_true_iff.mpr ⟨b, by rw [hwc]⟩)
          · exact h w b hw'
      · exact Or.inr ⟨q :: α, b, δ, by rw [ht]; rfl, hδ⟩

/-! ## §2. `CanRaise` survives the read-safe window (self-slides included) -/

/-- **`CanRaise` PERSISTS ACROSS A SOFT WINDOW.**  Every letter is either
`ReadSafeNoSelfHead c` or a slide headed by `c` itself
(`EmptyTail.canRaise_survives_own_slide`). -/
theorem canRaise_survives_soft {Q W : State} {c : Card} {τ : List Move}
    (hplay : ShufflePlayW Q τ W) (hQ : Q.WF) (hcan : CanRaise Q c)
    (hsoft : ∀ q ∈ τ, ReadSafeNoSelfHead c q ∨
      ∃ b : Base, q = Move.tabToTab c b) :
    CanRaise W c := by
  induction hplay with
  | nil st => exact hcan
  | @cons st s₁ W m τ' hrev hstep hrest ih =>
      have htail : ∀ q ∈ τ', ReadSafeNoSelfHead c q ∨
          ∃ b : Base, q = Move.tabToTab c b :=
        fun q hq => hsoft q (List.mem_cons_of_mem m hq)
      have hwf : st.WF := hQ
      have hnext : CanRaise s₁ c := by
        rcases hsoft m (List.mem_cons_self ..) with hs | ⟨b', rfl⟩
        · cases m with
          | draw =>
              exact R12.canRaise_survives_draw hstep hcan
          | wasteToFound x =>
              exact absurd hrev (wasteToFound_not_reversibleAtW st x)
          | wasteToTab x b' =>
              exact absurd hrev (wasteToTab_not_reversibleAtW st x b')
          | tabToFound w =>
              exact R12.canRaise_survives_raise hwf hstep hs
                (fun hwc => hs (by rw [hwc])) hcan
          | foundToTab x b' =>
              exact R12.canRaise_survives_pull hwf hstep hs.1 hs.2 hcan
          | tabToTab x b' =>
              by_cases hxc : x = c
              · subst hxc
                exact EmptyTail.canRaise_survives_own_slide hwf hstep hrev hcan
              · exact R12.canRaise_survives_slide hwf hstep hrev hxc hs hcan
        · exact EmptyTail.canRaise_survives_own_slide hwf hstep hrev hcan
      exact ih (step_wf hwf hstep) hnext htail

/-! ## §3. The net-zero core: `slide c b' ; raise c` = `raise c` -/

/-- `fromCard c l` is the singleton `[c]` when `c` is the LAST card of a
duplicate-free run. -/
theorem fromCard_singleton_of_last {l : List Card} {c : Card}
    (hnd : l.Nodup) (hlt : lastOf l = some c) :
    fromCard c l = [c] := by
  obtain ⟨front, hfe⟩ := lastOf_eq_snoc hlt
  have hnd' : (front ++ [c]).Nodup := by rw [← hfe]; exact hnd
  have hc : c ∉ front := fun hmem =>
    (List.nodup_append.mp hnd').2.2 c hmem c (List.mem_singleton.mpr rfl) rfl
  rw [hfe, show front ++ [c] = front ++ c :: [] from rfl,
    CommuteStep.fromCard_append_stop hc]

/-- `below` and `chop` agree at the last card of a duplicate-free run. -/
theorem below_eq_chop_of_last {l : List Card} {c : Card}
    (hnd : l.Nodup) (hlt : lastOf l = some c) :
    below c l = chop l := by
  obtain ⟨front, hfe⟩ := lastOf_eq_snoc hlt
  have hnd' : (front ++ [c]).Nodup := by rw [← hfe]; exact hnd
  have hc : c ∉ front := fun hmem =>
    (List.nodup_append.mp hnd').2.2 c hmem c (List.mem_singleton.mpr rfl) rfl
  rw [hfe, show front ++ [c] = front ++ c :: [] from rfl,
    CommuteStep.below_append_stop hc, chop_snoc]

/-- Removing a just-added top card restores the pile (it is `afterRunRemoved`
of the snoc at the original run). -/
theorem afterRunRemoved_snoc_self {p : Pile} {c : Card}
    (h : p.faceUp ≠ [] ∨ p.hidden = []) :
    Pile.afterRunRemoved { p with faceUp := p.faceUp ++ [c] } p.faceUp = p := by
  rcases p with ⟨hd, fq⟩
  cases fq with
  | nil =>
      have hhd : hd = [] := by
        rcases h with h' | h'
        · exact absurd rfl h'
        · exact h'
      subst hhd
      rfl
  | cons x xs => rfl

/-- The slide's source pile is the raise's `afterRunRemoved` (the singleton
`[c]` case of `slideSt_piles_source`). -/
theorem slideSt_piles_source_run {st : State} {c : Card} {b : Base} {a k : Anchor}
    (hwf : st.WF) (hcp : st.canPlace c b = true) (hk : CommuteStep.tgt st b = some k)
    (hka : k ≠ a)
    (hcell : below c (st.piles a).faceUp ≠ [] ∨
      (below c (st.piles a).faceUp = [] ∧ (st.piles a).hidden = [])) :
    (CommuteStep.slideSt st c b a).piles a =
      Pile.afterRunRemoved (st.piles a) (below c (st.piles a).faceUp) := by
  rw [CommuteStep.slideSt_piles_source hwf hcp hk hka hcell]
  rcases hcell with h | ⟨h, hh⟩
  · cases hb : below c (st.piles a).faceUp with
    | nil => exact absurd hb h
    | cons x xs => rfl
  · cases hb : below c (st.piles a).faceUp with
    | nil =>
        rw [show ({ st.piles a with faceUp := [] } : Pile)
            = (⟨[], []⟩ : Pile) from by rw [← hh]]
        exact (Pile.afterRunRemoved_bare hh).symm
    | cons x xs => rw [h] at hb; exact absurd hb (by simp)

/-- **THE NET-ZERO CORE.**  At a `WF` state where `c` is a pile top (so
`CanRaise` holds and the slide of `c` moves the singleton `[c]`), the two-word
play `slide c b ; raise c` and the one-word play `raise c` land on the SAME
state. -/
theorem raiseSt_slideSt_self {st : State} {c : Card} {b : Base} {a k : Anchor}
    (hwf : st.WF) (hpa : st.pileOfTop c = some a)
    (hcp : st.canPlace c b = true) (hk : CommuteStep.tgt st b = some k)
    (hka : k ≠ a)
    (hcell : below c (st.piles a).faceUp ≠ [] ∨
      (below c (st.piles a).faceUp = [] ∧ (st.piles a).hidden = [])) :
    raiseSt (CommuteStep.slideSt st c b a) c k = raiseSt st c a := by
  have hnd : (st.piles a).faceUp.Nodup := runOK_nodup (hwf.runOK_of a)
  have hlt : lastOf (st.piles a).faceUp = some c := (pileOfTop_top hpa).2
  have hsingle : fromCard c (st.piles a).faceUp = [c] :=
    fromCard_singleton_of_last hnd hlt
  have hbelow : below c (st.piles a).faceUp = chop (st.piles a).faceUp :=
    below_eq_chop_of_last hnd hlt
  have hsrc : (CommuteStep.slideSt st c b a).piles a =
      Pile.afterRunRemoved (st.piles a) (chop (st.piles a).faceUp) := by
    rw [slideSt_piles_source_run hwf hcp hk hka hcell, hbelow]
  have hK : (CommuteStep.slideSt st c b a).piles k =
      { st.piles k with faceUp := (st.piles k).faceUp ++ [c] } := by
    rw [CommuteStep.slideSt_piles_target hwf hcp hk hka hcell, hsingle]
  -- the target pile's cell condition
  have hfuK : (st.piles k).faceUp ≠ [] ∨ (st.piles k).hidden = [] := by
    cases b with
    | inl j =>
        have hkj : j = k := by simpa [CommuteStep.tgt] using hk
        subst hkj
        obtain ⟨hE, -⟩ := canPlace_inl hcp
        exact Or.inr (Pile.isEmpty_eq _ |>.mp hE).1
    | inr z =>
        have hz : st.pileOfTop z = some k := hk
        exact Or.inl (pileOfTop_top hz).1
  have hfill : Pile.afterRunRemoved
      { st.piles k with faceUp := (st.piles k).faceUp ++ [c] }
      (chop ({ st.piles k with faceUp := (st.piles k).faceUp ++ [c] } : Pile).faceUp)
      = st.piles k := by
    show Pile.afterRunRemoved
      { st.piles k with faceUp := (st.piles k).faceUp ++ [c] }
      (chop ((st.piles k).faceUp ++ [c])) = st.piles k
    rw [chop_snoc]
    exact afterRunRemoved_snoc_self hfuK
  apply State.ext
  · funext s
    rw [raiseSt_found_apply, raiseSt_found_apply, CommuteStep.slideSt_found]
  · funext a'
    rw [raiseSt_piles_apply, raiseSt_piles_apply]
    by_cases h1 : a' = k
    · subst h1
      rw [ite_eq_left rfl, ite_eq_right hka, hK, hfill]
    · rw [ite_eq_right h1]
      by_cases h2 : a' = a
      · subst h2
        rw [ite_eq_left rfl]
        exact hsrc
      · rw [ite_eq_right h2]
        exact CommuteStep.slideSt_piles_other hwf hcp hk hka hcell h2 h1
  · rw [raiseSt_stock, raiseSt_stock, CommuteStep.slideSt_stock]
  · rw [raiseSt_waste, raiseSt_waste, CommuteStep.slideSt_waste]
  · rw [raiseSt_drawStep, raiseSt_drawStep, CommuteStep.slideSt_drawStep]

/-- **`step`-level net-zero.**  The `raise c` after a slide of `c` and the
`raise c` before it land on the same state. -/
theorem step_raise_of_slide_self {st s' : State} {c : Card} {b : Base}
    (hwf : st.WF) (hcan : CanRaise st c)
    (hrev : reversibleAtW st (Move.tabToTab c b))
    (hstep : State.step st (Move.tabToTab c b) = some s') :
    ∃ W : State, State.step s' (Move.tabToFound c) = some W ∧
      State.step st (Move.tabToFound c) = some W := by
  obtain ⟨hnext, a, hpa, hseat⟩ := hcan
  obtain ⟨a0, k, hhold, hcp, hk, hka, hface, hrunne, hcell⟩ :=
    CommuteStep.slide_data hwf hrev
  have ha0 : a0 = a := by
    have h1 := Drain.pileHolding_of_pileOfTop hwf hpa
    rw [hhold] at h1
    exact Option.some.inj h1
  subst a0
  -- the slide lands on `slideSt`
  have hs' : s' = CommuteStep.slideSt st c b a := by
    obtain ⟨a', hh, hcp', hne', hs⟩ := CommuteStep.step_tabToTab_slideSt hstep
    have ha' : a' = a := by
      rw [hhold] at hh
      exact (Option.some.inj hh).symm
    rw [hs, ha']
  subst hs'
  have hraise_st : State.step st (Move.tabToFound c) = some (raiseSt st c a) := by
    rw [step_tabToFound_splice hnext hpa]
    rfl
  have htopSL : (CommuteStep.slideSt st c b a).pileOfTop c = some k :=
    CommuteStep.slideSt_pileOfTop_source hwf hcp hk hka hrunne hcell hpa
  have hnextSL : (CommuteStep.slideSt st c b a).nextUp c = true := by
    unfold State.nextUp State.foundHeight
    rw [CommuteStep.slideSt_found]
    exact hnext
  have hraise_SL : State.step (CommuteStep.slideSt st c b a) (Move.tabToFound c) =
      some (raiseSt (CommuteStep.slideSt st c b a) c k) := by
    rw [step_tabToFound_splice hnextSL htopSL]
    rfl
  refine ⟨raiseSt st c a, ?_, hraise_st⟩
  rw [hraise_SL, raiseSt_slideSt_self hwf hpa hcp hk hka hcell]

/-! ## §4. The deletion: a self-slide in the window shortens the play -/

/-- **THE DELETION LEMMA.**  If the window before `raise c` splits as
`α ++ slide c b :: δ` where every window letter is `ReadSafeNoSelfHead c` and
`δ` is free of slides of `c`, then a strictly shorter witness play with the
same endpoints exists.  (The hypotheses say exactly: `c` stays a bare pile top
across `α`, so `raise c` is legal where the slide fires, and `δ` is `ReadSafe c`.) -/
theorem selfSlide_shortens {G v : State} {c : Card} {γ β : List Move}
    (hG : G.WF) (hcan : CanRaise G c)
    (hplay : ShufflePlayW G (γ ++ Move.tabToFound c :: β) v)
    (hsoft : ∀ q ∈ γ, ReadSafeNoSelfHead c q)
    (hself : ∃ (α : List Move) (b : Base) (δ : List Move),
      γ = α ++ Move.tabToTab c b :: δ ∧ NoSlideOf c δ) :
    ∃ ρ' : List Move, ShufflePlayW G ρ' v ∧
      ρ'.length < (γ ++ Move.tabToFound c :: β).length := by
  obtain ⟨α, b, δ, hγ, hδ⟩ := hself
  subst hγ
  have hplay' : ShufflePlayW G
      (α ++ Move.tabToTab c b :: (δ ++ Move.tabToFound c :: β)) v := by
    simpa [List.append_assoc] using hplay
  obtain ⟨T, hα, hrest⟩ :=
    ValleyElim.ShufflePlayW_split hplay' α
      (Move.tabToTab c b :: (δ ++ Move.tabToFound c :: β)) rfl
  have hTwf : T.WF := SatDifferCensus.ShufflePlayW.wf_end hα hG
  have hsoftα : ∀ q ∈ α, ReadSafeNoSelfHead c q ∨
      ∃ b' : Base, q = Move.tabToTab c b' := by
    intro q hq
    exact Or.inl (hsoft q (List.mem_append_left _ hq))
  have hcanT : CanRaise T c := canRaise_survives_soft hα hG hcan hsoftα
  obtain ⟨T', hrevs, hsteps, hrest2⟩ := Bubble.walk_cons_inv hrest
  have hT'wf : T'.WF := step_wf hTwf hsteps
  have hcanT' : CanRaise T' c :=
    EmptyTail.canRaise_survives_own_slide hTwf hsteps hrevs hcanT
  have hread : ∀ q ∈ δ, ReadSafe c q := by
    intro q hq
    refine readSafe_of_noSelfHead (hsoft q ?mem) ?noself
    · exact List.mem_append_right _
        (List.mem_cons_of_mem _ hq)
    · intro w b' hqeq
      subst hqeq
      exact hδ w b' hq
  have hsw : RaiseSwaps T' c δ :=
    raiseSwaps_of_readSafe hT'wf hrest2 hcanT' hread
  have hbubble : ShufflePlayW T' (Move.tabToFound c :: δ ++ β) v :=
    raise_bubble δ hrest2 hsw
  obtain ⟨W', hrevr, hstepr, htail2⟩ := Bubble.walk_cons_inv hbubble
  obtain ⟨W, hstepW', hstepW⟩ := step_raise_of_slide_self hTwf hcanT hrevs hsteps
  have hW : W' = W := Option.some.inj (hstepr.symm.trans hstepW')
  subst hW
  refine ⟨α ++ Move.tabToFound c :: (δ ++ β), ?_, ?_⟩
  · exact ShufflePlayW_append hα (Walk.cons
      (DrainClose.reversibleAtW_tabToFound_of_canRaise (st := T) (c := c) hTwf hcanT)
      hstepW htail2)
  · simp only [List.length_cons, List.length_append]
    omega

/-- **THE WINDOW IS SELF-SLIDE FREE — general form.**  A window that is
`ReadSafeNoSelfHead c` everywhere is free of slides of `c` in a SHORTEST play
out of a state where `c` is raisable.  `EmptyTailNoSelfSlide` is the
split-level instance of this statement. -/
theorem noSelfSlide_of_soft_window {G v : State} {c : Card} {γ β : List Move}
    (hG : G.WF) (hcan : CanRaise G c)
    (hplay : ShufflePlayW G (γ ++ Move.tabToFound c :: β) v)
    (hsoft : ∀ q ∈ γ, ReadSafeNoSelfHead c q)
    (hmin : ∀ ρ', ShufflePlayW G ρ' v →
      (γ ++ Move.tabToFound c :: β).length ≤ ρ'.length) :
    NoSlideOf c γ := by
  rcases noSlideOf_or_last c γ with h | ⟨α, b, δ, hγ, hδ⟩
  · exact h
  · obtain ⟨ρ', hρ'play, hρ'len⟩ :=
      selfSlide_shortens hG hcan hplay hsoft ⟨α, b, δ, hγ, hδ⟩
    exact absurd hρ'len (Nat.not_lt.mpr (hmin ρ' hρ'play))

/-! ## §5. `EmptyTailNoSelfSlide` -/

/-- **THE RESIDUAL IS A THEOREM** under the campaign's standing inputs. -/
theorem emptyTailNoSelfSlide_of_livePair_mountain
    (hl : SplitLivePair)
    (hms : ∀ (u v : State) (ρ : List Move) (F : State)
      (left right : List Move) (c d : Card) (b : Base)
      (pre post tail : List Move),
      SplitHyp u v ρ F left right c d b pre post tail →
      MountainKit.MountainSplit left right) :
    EmptyTailNoSelfSlide := by
  intro u v ρ F left right c d b pre post tail γ β h hpost htail hfirst
  have hkeep := h
  have htwin : d = c.twin := EmptyTail.twin_of_livePair_emptyTail hl h hpost
  have hms' : MountainKit.MountainSplit left right :=
    hms u v ρ F left right c d b pre post tail h
  obtain ⟨γ₀, β₀, htail₀, hfirst₀, hsoft₀⟩ :=
    emptyTail_window_soft h hpost hms' htwin
  -- the first-occurrence decomposition is unique
  have hγγ : γ₀ = γ :=
    (first_decomp_unique (by rw [← htail, ← htail₀]) hfirst hfirst₀).symm
  subst hγγ
  obtain ⟨huwf, -, hsv, hplay, hsplitAt, hmin, hρ, hleft, hright, hshape,
    hfree, hrightShape⟩ := h
  have hcanF : CanRaise F c := BlockKit.emptyTail_canRaise hkeep hpost
  have hnopullRight : ∀ m ∈ right, ¬ Bubble.IsPull m := hms'.2
  have hnopullTail : ∀ m ∈ tail, ¬ Bubble.IsPull m := by
    intro m hm hpull
    exact hnopullRight m (by rw [hrightShape]; exact List.mem_cons_of_mem _ hm) hpull
  rw [hrightShape] at hright
  obtain ⟨G, hstepD, hplayG⟩ : ∃ G : State,
      State.step F (Move.tabToFound d) = some G ∧ ShufflePlayW G tail v := by
    cases hright with
    | cons _ hs hrest => exact ⟨_, hs, hrest⟩
  have hsu : d.suit ≠ c.suit := by
    rw [htwin]; exact EmptyTail.twin_suit_ne c.suit
  have hdw : d ≠ c := by
    rw [htwin]; exact SplitKit.card_twin_ne c
  have hFwf : F.WF := SatDifferCensus.ShufflePlayW.wf_end hleft huwf
  have hcanG : CanRaise G c :=
    R12.canRaise_survives_raise hFwf hstepD hsu hdw hcanF
  have hGwf : G.WF := step_wf hFwf hstepD
  have hsoftG : ∀ q ∈ γ₀, ReadSafeNoSelfHead c q :=
    fun q hq => hsoft₀ q (List.mem_cons_of_mem _ hq)
  rcases noSlideOf_or_last c γ₀ with hnoslide | ⟨α, bs, δ, hγeq, hδ⟩
  · exact hnoslide
  · -- a self-slide would shorten the play
    have hplayG' : ShufflePlayW G (γ₀ ++ Move.tabToFound c :: β₀) v := by
      rw [← htail₀]; exact hplayG
    obtain ⟨ρ', hρ'play, hρ'len⟩ :=
      selfSlide_shortens hGwf hcanG hplayG' hsoftG ⟨α, bs, δ, hγeq, hδ⟩
    -- prepend the split's own prefix
    have hρ' : ρ = (pre ++ [Move.foundToTab c b, Move.tabToFound d]) ++
        (γ₀ ++ Move.tabToFound c :: β₀) := by
      rw [hρ, hshape, hrightShape, htail₀, hpost]
      simp only [List.cons_append, List.nil_append, List.append_assoc,
        List.append_nil]
    obtain ⟨G', hprefix, hplayG''⟩ := ValleyElim.ShufflePlayW_split hplay _ _ hρ'
    -- the same prefix reaches `G`
    have hprefixG : ShufflePlayW u
        (pre ++ [Move.foundToTab c b, Move.tabToFound d]) G := by
      have hleft' : ShufflePlayW u (pre ++ [Move.foundToTab c b]) F := by
        have hs : pre ++ [Move.foundToTab c b] = left := by
          rw [hshape, hpost]
        rw [hs]
        exact hleft
      obtain ⟨A', hpre, hrest⟩ :=
        ValleyElim.ShufflePlayW_split hleft' pre [Move.foundToTab c b] rfl
      have hrevPull : reversibleAtW A' (Move.foundToTab c b) := by
        cases hrest with | cons hlet _ _ => exact hlet
      have hstepPull : State.step A' (Move.foundToTab c b) = some F :=
        Elim.step_of_singleton hrest
      have hrevD : reversibleAtW F (Move.tabToFound d) := by
        cases hright with | cons hlet _ _ => exact hlet
      have hsingle : ShufflePlayW A' [Move.foundToTab c b, Move.tabToFound d] G := by
        refine Walk.cons hrevPull hstepPull ?_
        exact Walk.cons hrevD hstepD (Walk.nil G)
      exact ShufflePlayW_append hpre hsingle
    have hG' : G' = G := by
      have r1 := Walk_run _ hprefix
      have r2 := Walk_run _ hprefixG
      exact Option.some.inj (r1.symm.trans r2)
    subst hG'
    have hnew : ShufflePlayW u
        ((pre ++ [Move.foundToTab c b, Move.tabToFound d]) ++ ρ') v :=
      ShufflePlayW_append hprefix hρ'play
    have hlen : ((pre ++ [Move.foundToTab c b, Move.tabToFound d]) ++ ρ').length
        < ρ.length := by
      rw [hρ' ]
      simp only [List.length_append, List.length_cons, List.length_nil]
      have := hρ'len
      simp only [List.length_append, List.length_cons] at this
      omega
    exact absurd hlen (Nat.not_lt.mpr (hmin _ hnew))

/-! ## §6. The campaign chain -/

/-- **`SplitBlock` FROM THE RESIDUAL, WITH THE RESIDUAL PROVED.** -/
theorem splitBlock_of_livePair_mountain
    (hl : SplitLivePair)
    (hms : ∀ (u v : State) (ρ : List Move) (F : State)
      (left right : List Move) (c d : Card) (b : Base)
      (pre post tail : List Move),
      SplitHyp u v ρ F left right c d b pre post tail →
      MountainKit.MountainSplit left right)
    (hcov : BlockKit.TailCovers) : SplitBlock :=
  splitBlock_of_noSelfSlide hl hms
    (emptyTailNoSelfSlide_of_livePair_mountain hl hms) hcov

/-- **THE CAMPAIGN CHAIN, UNCONDITIONAL IN THE BLOCK LANE.** -/
theorem satDifferForkWF_of_livePair_mountain
    (hl : SplitLivePair)
    (hms : ∀ (u v : State) (ρ : List Move) (F : State)
      (left right : List Move) (c d : Card) (b : Base)
      (pre post tail : List Move),
      SplitHyp u v ρ F left right c d b pre post tail →
      MountainKit.MountainSplit left right)
    (hcov : BlockKit.TailCovers) (hmin : ValleyElim.ShortestPlayExists) :
    SatDifferForkWF :=
  satDifferForkWF_of_noSelfSlide hl hms
    (emptyTailNoSelfSlide_of_livePair_mountain hl hms) hcov hmin

end NoSelfKit

-- statements (verbatim)
#check @NoSelfKit.emptyTailNoSelfSlide_of_livePair_mountain
#check @NoSelfKit.splitBlock_of_livePair_mountain
#check @NoSelfKit.satDifferForkWF_of_livePair_mountain
#check @NoSelfKit.raiseSt_slideSt_self
#check @NoSelfKit.step_raise_of_slide_self
#check @NoSelfKit.selfSlide_shortens
#check @NoSelfKit.noSelfSlide_of_soft_window
#check @NoSelfKit.canRaise_survives_soft

namespace NoSelfKit

/-- The residual is exactly the one the chain consumes. -/
example (hl : SplitKit.SplitLivePair)
    (hms : ∀ (u v : State) (ρ : List Move) (F : State)
      (left right : List Move) (c d : Card) (b : Base)
      (pre post tail : List Move),
      SplitKit.SplitHyp u v ρ F left right c d b pre post tail →
      MountainKit.MountainSplit left right) :
    SlideFwd.EmptyTailNoSelfSlide :=
  emptyTailNoSelfSlide_of_livePair_mountain hl hms

end NoSelfKit

#print axioms NoSelfKit.noSlideOf_or_last
#print axioms NoSelfKit.canRaise_survives_soft
#print axioms NoSelfKit.fromCard_singleton_of_last
#print axioms NoSelfKit.below_eq_chop_of_last
#print axioms NoSelfKit.afterRunRemoved_snoc_self
#print axioms NoSelfKit.raiseSt_slideSt_self
#print axioms NoSelfKit.step_raise_of_slide_self
#print axioms NoSelfKit.selfSlide_shortens
#print axioms NoSelfKit.noSelfSlide_of_soft_window
#print axioms NoSelfKit.emptyTailNoSelfSlide_of_livePair_mountain
#print axioms NoSelfKit.splitBlock_of_livePair_mountain
#print axioms NoSelfKit.satDifferForkWF_of_livePair_mountain
