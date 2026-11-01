import Orig2.ForkSurvivor
import Orig2.ForkMountainShape
import Orig2.ForkThirdLive
import Orig2.ForkThirdCrossing
import Orig2.ForkSafeTransport
import Orig2.ForkCommuteSlide

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option linter.unusedVariables false

/-!
# Orig2/ForkDirect — the survivor's death is its twin's raise

READ-ONLY scratch (no source edit, no commit).  Zero `sorry`, zero
`Classical.choice`, zero `native_decide`; axiom battery at the tail.

## The argument (a different kind from the bracket)

`CanRaiseS` is a **cargo span** (`Orig2/Vocab.lean:485`): `e` is S-live iff some
finite chain of *reversible slides* reaches a state where `e` carries the
vanilla raise license.  Slides are invertible, and the inverse of a reversible
slide is a reversible slide, so a whole slide chain can be traversed backwards
and re-traversed.  Hence:

* **a slide never changes `CanRaiseS`** — in particular *covering `e` cannot
  kill it*: the cover slides back off (`canRaiseS_survives_slide`);
* **a draw never changes `CanRaiseS`** (`canRaiseS_survives_draw`);
* **a raise of a card `x ∉ {e, e.twin}` never changes it**
  (`canRaiseS_survives_raise_of_ne`) — the flat characterization
  (`CargoRaise.canRaiseS_flat_necessity`, `Orig2/CargoRaise.lean:320`) reads
  `e` as `bs ++ e :: run` at its pile; a raise of another card either is
  disjoint from that pile, or tops it and truncates `run` by its last letter,
  and the twin-top clause survives because `x ≠ e.twin`.

Hence over a pull-free leg the *only* letters that can destroy `e`'s
S-liveness are `raise e` and `raise e.twin` (`canRaiseS_end_or_bad_raise`).  At
a valley split the far endpoint `v` is saturated, so `e` does die, and

* **`split_survivor_bad_raise`**: `raise e ∈ right ∨ raise e.twin ∈ right`;
* **`split_survivor_mate_raise`**: in the frozen branch (no `e.suit` raise in
  the right leg) it is `raise e.twin` — *not* a cover slide and *not* a tower
  of slides.  This is the kernel refutation of the "bury `e` under an
  immovable stack" mechanism: every such stack is a slide chain, and every
  slide chain is harmless to `CanRaiseS`.

The residual is therefore `MateRaiseFree` (**no `raise e.twin` in the right
leg**), a raise-exclusion rather than a bracket statement;
`landingThirdSuitFree_of_mateRaiseFree` transfers it.

The same lemma also removes the rank side condition of the repository's own
transport row `SafeTransport.canRaiseS_of_canRaiseS_raise_high`
(`Orig2/ForkSafeTransport.lean:151`), which requires `x.rank ≤ c.rank`; the
flat route needs no rank comparison (`canRaiseS_of_canRaiseS_raise_high'`).
-/

namespace Direct

open ValleyElim

/-! ## §1. Occurrence of a letter in a play -/

/-- `Occurs m l`: the play `l` contains the letter `m`. -/
def Occurs (m : Move) (l : List Move) : Prop :=
  ∃ s₁ s₂ : List Move, l = s₁ ++ m :: s₂

theorem occurs_cons {m a : Move} {l : List Move} (h : Occurs m l) :
    Occurs m (a :: l) := by
  obtain ⟨s₁, s₂, hs⟩ := h
  exact ⟨a :: s₁, s₂, by rw [hs]; rfl⟩

theorem occurs_head (m : Move) (l : List Move) : Occurs m (m :: l) :=
  ⟨[], l, rfl⟩

theorem occurs_tail {m m' : Move} {l : List Move} (h : Occurs m (m' :: l))
    (hne : m ≠ m') : Occurs m l := by
  obtain ⟨s₁, s₂, hs⟩ := h
  cases s₁ with
  | nil =>
      rw [List.nil_append] at hs
      injection hs with h1 h2
      exact absurd h1.symm hne
  | cons a t =>
      rw [List.cons_append] at hs
      injection hs with h1 h2
      exact ⟨t, s₂, h2⟩

theorem occurs_append_left {m : Move} {l₁ l₂ : List Move} (h : Occurs m l₁) :
    Occurs m (l₁ ++ l₂) := by
  obtain ⟨s₁, s₂, hs⟩ := h
  exact ⟨s₁, s₂ ++ l₂, by rw [hs]; simp only [List.cons_append, List.append_assoc]⟩

theorem occurs_append_right {m : Move} {l₁ l₂ : List Move} (h : Occurs m l₂) :
    Occurs m (l₁ ++ l₂) := by
  obtain ⟨s₁, s₂, hs⟩ := h
  exact ⟨l₁ ++ s₁, s₂, by rw [hs]; simp only [List.append_assoc]⟩

/-! ## §2. The invariance kit for `CanRaiseS` -/

/-- **A DRAW PRESERVES `CanRaiseS`** — a draw writes only stock and waste. -/
theorem canRaiseS_survives_draw {st st' : State} {e : Card}
    (hwf : st.WF) (hstep : State.step st Move.draw = some st')
    (h : CanRaiseS st e) : CanRaiseS st' e := by
  obtain ⟨hnext, a, bs, run, hface, hseat, hcond⟩ :=
    canRaiseS_flat_necessity hwf h
  have hfound : st'.found = st.found := stepDraw_found hstep
  have hpiles : st'.piles = st.piles := stepDraw_piles hstep
  have hnext' : st'.nextUp e = true := by
    unfold State.nextUp State.foundHeight
    rw [hfound]
    exact hnext
  refine canRaiseS_flat_sufficiency (step_wf hwf hstep)
    ⟨hnext', a, bs, run, ?_, ?_, ?_⟩
  · show (st'.piles a).faceUp = bs ++ e :: run
    rw [hpiles]
    exact hface
  · show bs ≠ [] ∨ ((st'.piles a).hidden = [] ∧ e.rank = Rank.king)
    rw [hpiles]
    exact hseat
  · show run = [] ∨ st'.pileOfTop e.twin ≠ none
    rw [SplitKit.pileOfTop_congr_piles hpiles e.twin]
    exact hcond

/-- The mirror of a reversible slide is a reversible slide
(`tabToTab_mirror` + `Kit.reversible_mirrorW`). -/
theorem slide_mirror_rev {st st' : State} {x : Card} {b : Base}
    (hwf : st.WF) (hstep : State.step st (Move.tabToTab x b) = some st')
    (hrev : reversibleAtW st (Move.tabToTab x b)) :
    ∃ b₂, State.step st' (Move.tabToTab x b₂) = some st ∧
      reversibleAtW st' (Move.tabToTab x b₂) := by
  obtain ⟨b₂, hstep₂⟩ := tabToTab_mirror hwf hstep hrev
  exact ⟨b₂, hstep₂, reversible_mirrorW hstep₂ hstep⟩

/-- **A SLIDE PRESERVES `CanRaiseS`** — the mirror of a reversible slide is a
reversible slide, so the slide chain can be traversed backwards and
re-traversed.  In particular a slide **landing on `e` (a cover) cannot kill
`e`'s S-liveness**: the cover slides off again. -/
theorem canRaiseS_survives_slide {st st' : State} {x : Card} {b : Base} {e : Card}
    (hwf : st.WF) (hstep : State.step st (Move.tabToTab x b) = some st')
    (hrev : reversibleAtW st (Move.tabToTab x b)) (h : CanRaiseS st e) :
    CanRaiseS st' e := by
  obtain ⟨b₂, hstep₂, hrev₂⟩ := slide_mirror_rev hwf hstep hrev
  exact CanRaiseS.via e ⟨x, b₂, hstep₂, hrev₂⟩ h

/-! ### §2b. The raise that misses both `e` and `e.twin` -/

/-- The raised pile's face-up list, with the raised card chopped off, still
exhibits the protected card at the same depth. -/
theorem chop_shape_of_last {bs run run' : List Card} {e c : Card}
    (hrun : run = run' ++ [c]) :
    chop (bs ++ e :: run) = bs ++ e :: run' := by
  rw [hrun]
  have hassoc : bs ++ e :: (run' ++ [c]) = (bs ++ e :: run') ++ [c] := by
    simp only [List.cons_append, List.append_assoc]
  rw [hassoc, chop_snoc]

/-- The pile a raise rewrites is the pile its card tops. -/
theorem piles_tabToFound_at {st st' : State} {c : Card} {a : Anchor}
    (hstep : State.step st (Move.tabToFound c) = some st')
    (hpa : st.pileOfTop c = some a) :
    st'.piles a = (st.piles a).afterRunRemoved (chop (st.piles a).faceUp) := by
  obtain ⟨-, a', hpa', hs⟩ := step_tabToFound_inv hstep
  have haa : a' = a := Option.some.inj (hpa'.symm.trans hpa)
  rw [hs, haa]
  show (if a = a then Pile.afterRunRemoved (st.piles a) (chop (st.piles a).faceUp)
    else st.piles a) = Pile.afterRunRemoved (st.piles a) (chop (st.piles a).faceUp)
  rw [ite_eq_left rfl]

theorem afterRunRemoved_faceUp_of_ne {p : Pile} {pre : List Card} (h : pre ≠ []) :
    (p.afterRunRemoved pre).faceUp = pre := by
  unfold Pile.afterRunRemoved
  cases pre with
  | nil => exact absurd rfl h
  | cons x xs => rfl

theorem afterRunRemoved_hidden_of_ne {p : Pile} {pre : List Card} (h : pre ≠ []) :
    (p.afterRunRemoved pre).hidden = p.hidden := by
  unfold Pile.afterRunRemoved
  cases pre with
  | nil => exact absurd rfl h
  | cons x xs => rfl

/-- **A RAISE OF `x ∉ {e, e.twin}` PRESERVES `CanRaiseS · e`.**

This is `SafeTransport.canRaiseS_of_canRaiseS_raise_high`
(`Orig2/ForkSafeTransport.lean:151`) **without its rank hypothesis**: the flat
shape `bs ++ e :: run` of `e`'s pile is left alone unless `x` is the top card of
that very pile, in which case the raise only chops the last letter of `run`. -/
theorem canRaiseS_survives_raise_of_ne {st st' : State} {c e : Card}
    (hwf : st.WF) (hstep : State.step st (Move.tabToFound c) = some st')
    (hce : c ≠ e) (hct : c ≠ e.twin) (h : CanRaiseS st e) :
    CanRaiseS st' e := by
  obtain ⟨hnext, a, bs, run, hface, hseat, hcond⟩ :=
    canRaiseS_flat_necessity hwf h
  obtain ⟨hnextc, a₀, hpa₀, -⟩ := step_tabToFound_inv hstep
  have htopc : (st.piles a₀).top = some c := (pileOfTop_eq_some_iff hwf).mp hpa₀
  -- the raised card is in another suit (`e` is the unique next-up of its suit)
  have hcs : c.suit ≠ e.suit := by
    intro hse
    have hcrank : c.rank.toIdx = rungAt st e.suit := by
      have hh := of_decide_eq_true hnextc
      unfold rungAt
      rw [hse] at hh
      exact hh
    have herank : e.rank.toIdx = rungAt st e.suit := by
      have hh := of_decide_eq_true hnext
      unfold rungAt
      exact hh
    have hrc : c.rank = e.rank := Rank.toIdx_inj (by omega)
    exact hce (by cases c; cases e; simp_all)
  have hnext' : st'.nextUp e = true := SafeTransport.nextUp_tabToFound_ne hstep hcs hnext
  by_cases ha : a = a₀
  · -- the raised card tops `e`'s own pile: the raise chops it off `run`
    subst ha
    have hsplit : (st.piles a).faceUp = chop (st.piles a).faceUp ++ [c] :=
      lastOf_chop htopc
    have hrunne : run ≠ [] := by
      intro hr
      rw [hr] at hface
      have hlast : lastOf (bs ++ e :: ([] : List Card)) = some e := lastOf_snoc
      rw [← hface, hsplit, lastOf_snoc] at hlast
      exact hce (Option.some.inj hlast)
    have hlastrun : lastOf run = some c := by
      have h1 : lastOf (bs ++ e :: run) = some c := by
        rw [← hface, hsplit, lastOf_snoc]
      rw [CommuteStep.lastOf_append_of_ne_nil (l := bs) (m := e :: run) (by simp)] at h1
      have h2 : lastOf (e :: run) = lastOf run := by
        cases run with
        | nil => exact absurd rfl hrunne
        | cons y ys => rfl
      rwa [h2] at h1
    obtain ⟨run', hrun'⟩ := lastOf_eq_snoc hlastrun
    have hchop : chop (st.piles a).faceUp = bs ++ e :: run' := by
      rw [hface]
      exact chop_shape_of_last hrun'
    have hne : chop (st.piles a).faceUp ≠ [] := by
      rw [hchop]; simp
    have hface' : (st'.piles a).faceUp = bs ++ e :: run' := by
      rw [piles_tabToFound_at hstep hpa₀, afterRunRemoved_faceUp_of_ne hne, hchop]
    have hhidden : (st'.piles a).hidden = (st.piles a).hidden := by
      rw [piles_tabToFound_at hstep hpa₀, afterRunRemoved_hidden_of_ne hne]
    refine canRaiseS_flat_sufficiency (step_wf hwf hstep)
      ⟨hnext', a, bs, run', hface', ?_, ?_⟩
    · rw [hhidden]; exact hseat
    · rcases hcond with hrun0 | hsome
      · exfalso
        rw [hrun'] at hrun0
        simp at hrun0
      · right
        obtain ⟨k, hk⟩ : ∃ k, st.pileOfTop e.twin = some k := by
          cases hh : st.pileOfTop e.twin with
          | none => exact absurd hh hsome
          | some k => exact ⟨k, rfl⟩
        have hka : k ≠ a := by
          intro hka
          have ht1 : (st.piles a).top = some e.twin :=
            (pileOfTop_eq_some_iff hwf).mp (by rw [← hka]; exact hk)
          exact hct (Option.some.inj (ht1.symm.trans htopc)).symm
        have hres := SafeTransport.pileOfTop_tabToFound_ne hwf hstep hpa₀ hk hka
        rw [hres]; simp
  · -- the raised pile is another pile: nothing about `e` moves
    have hpile : st'.piles a = st.piles a :=
      SafeTransport.piles_tabToFound_ne hstep hpa₀ ha
    refine canRaiseS_flat_sufficiency (step_wf hwf hstep)
      ⟨hnext', a, bs, run, ?_, ?_, ?_⟩
    · rw [hpile]; exact hface
    · rw [hpile]; exact hseat
    · rcases hcond with hrun0 | hsome
      · exact Or.inl hrun0
      · right
        obtain ⟨k, hk⟩ : ∃ k, st.pileOfTop e.twin = some k := by
          cases hh : st.pileOfTop e.twin with
          | none => exact absurd hh hsome
          | some k => exact ⟨k, rfl⟩
        have hka : k ≠ a₀ := by
          intro hka
          have ht1 : (st.piles a₀).top = some e.twin :=
            (pileOfTop_eq_some_iff hwf).mp (by rw [← hka]; exact hk)
          exact hct (Option.some.inj (ht1.symm.trans htopc)).symm
        have hres := SafeTransport.pileOfTop_tabToFound_ne hwf hstep hpa₀ hk hka
        rw [hres]; simp

/-- **THE REPOSITORY'S TRANSPORT ROW, WITH THE RANK HYPOTHESIS REMOVED.**
Compare `SafeTransport.canRaiseS_of_canRaiseS_raise_high`
(`Orig2/ForkSafeTransport.lean:151`), which additionally requires
`x.rank.toIdx ≤ c.rank.toIdx`.  No rank comparison is needed. -/
theorem canRaiseS_of_canRaiseS_raise_high' {st st' : State} {c x : Card}
    (hwf : st.WF) (hstep : State.step st (Move.tabToFound c) = some st')
    (hcs : c.suit ≠ x.suit) (hct : c ≠ x.twin) (hS : CanRaiseS st x) :
    CanRaiseS st' x := by
  have hcx : c ≠ x := by
    intro hh; exact hcs (by rw [hh])
  exact canRaiseS_survives_raise_of_ne hwf hstep hcx hct hS

/-! ## §3. Over a pull-free leg only the two rank-mates can kill -/

/-- **THE KILL DICHOTOMY.**  Over a pull-free witness leg, an S-live card `e`
either stays S-live, or the leg raises `e`, or it raises `e.twin`.  Slides
(including every cover and every run move) and draws are *harmless*: no tower
of slides can bury `e` out of S-liveness. -/
theorem canRaiseS_end_or_bad_raise {st W : State} {play : List Move} {e : Card}
    (hplay : ShufflePlayW st play W) (hwf : st.WF)
    (hnopull : ∀ m ∈ play, ¬ Bubble.IsPull m) (h : CanRaiseS st e) :
    CanRaiseS W e ∨ Occurs (Move.tabToFound e) play ∨
      Occurs (Move.tabToFound e.twin) play := by
  induction hplay with
  | nil => exact Or.inl h
  | @cons st s₁ W m rest hrev hstep hrest ih =>
      have hwf' : s₁.WF := step_wf hwf hstep
      have hnp : ∀ m' ∈ rest, ¬ Bubble.IsPull m' :=
        fun m' hm' => hnopull m' (List.mem_cons_of_mem m hm')
      have hhead : CanRaiseS s₁ e ∨ m = Move.tabToFound e ∨
          m = Move.tabToFound e.twin := by
        cases m with
        | draw => exact Or.inl (canRaiseS_survives_draw hwf hstep h)
        | wasteToFound c =>
            exact absurd hrev (wasteToFound_not_reversibleAtW st c)
        | wasteToTab c b =>
            exact absurd hrev (wasteToTab_not_reversibleAtW st c b)
        | foundToTab c b =>
            exact absurd ⟨c, b, rfl⟩ (hnopull _ (List.mem_cons_self ..))
        | tabToFound c =>
            by_cases hce : c = e
            · exact Or.inr (Or.inl (by rw [hce]))
            · by_cases hct : c = e.twin
              · exact Or.inr (Or.inr (by rw [hct]))
              · exact Or.inl (canRaiseS_survives_raise_of_ne hwf hstep hce hct h)
        | tabToTab c b =>
            exact Or.inl (canRaiseS_survives_slide hwf hstep hrev h)
      rcases hhead with hsurv | hrfl | hrfl
      · rcases ih hwf' hnp hsurv with h1 | h1 | h1
        · exact Or.inl h1
        · exact Or.inr (Or.inl (occurs_cons h1))
        · exact Or.inr (Or.inr (occurs_cons h1))
      · subst hrfl
        exact Or.inr (Or.inl (occurs_head _ rest))
      · subst hrfl
        exact Or.inr (Or.inr (occurs_head _ rest))

/-! ## §4. The first `e.suit` raise of a frontier-frozen leg is `raise e` -/

/-- **NO `e.suit` RAISE AT ALL, OR `raise e` OCCURS.**  Starting where `e` is
the frontier card of its suit (rung `= e.rank.toIdx`), a pull-free leg can only
raise `e` first: the card raised at rung `e.rank` of `e.suit` is `e`. -/
theorem no_sigma_raise_or_raise_e {st W : State} {play : List Move} {e : Card}
    (hplay : ShufflePlayW st play W) (hwf : st.WF)
    (hnopull : ∀ m ∈ play, ¬ Bubble.IsPull m)
    (hrung : rungAt st e.suit = e.rank.toIdx) :
    (∀ c : Card, Occurs (Move.tabToFound c) play → c.suit ≠ e.suit) ∨
      Occurs (Move.tabToFound e) play := by
  induction hplay with
  | nil =>
      left
      intro c hc
      obtain ⟨s₁, s₂, hs⟩ := hc
      exact absurd hs (by simp)
  | @cons st s₁ W m rest hrev hstep hrest ih =>
      have hwf' : s₁.WF := step_wf hwf hstep
      have hnp : ∀ m' ∈ rest, ¬ Bubble.IsPull m' :=
        fun m' hm' => hnopull m' (List.mem_cons_of_mem m hm')
      -- either the head is already `raise e`, or the head is not an `e.suit`
      -- raise and the rung is frozen
      have hkey : Occurs (Move.tabToFound e) (m :: rest) ∨
          ((∀ c : Card, m = Move.tabToFound c → c.suit ≠ e.suit) ∧
            rungAt s₁ e.suit = e.rank.toIdx) := by
        cases m with
        | draw =>
            exact Or.inr ⟨(fun c hc => absurd hc (by simp)),
              by rw [rungAt_draw hstep, hrung]⟩
        | tabToTab x b =>
            exact Or.inr ⟨(fun c hc => absurd hc (by simp)),
              by rw [rungAt_tabToTab hstep, hrung]⟩
        | foundToTab x b =>
            exact absurd ⟨x, b, rfl⟩ (hnopull _ (List.mem_cons_self ..))
        | wasteToFound x =>
            exact absurd hrev (wasteToFound_not_reversibleAtW st x)
        | wasteToTab x b =>
            exact absurd hrev (wasteToTab_not_reversibleAtW st x b)
        | tabToFound x =>
            by_cases hx : x.suit = e.suit
            · -- the head is an `e.suit` raise: it is `e` itself
              left
              have hnext : st.nextUp x = true := (step_tabToFound_inv hstep).1
              have hcr : x.rank.toIdx = e.rank.toIdx := by
                have hh := of_decide_eq_true hnext
                have h1 : x.rank.toIdx = rungAt st x.suit := by
                  unfold rungAt
                  exact hh
                rw [hx, hrung] at h1
                exact h1
              have hxe : x = e := by
                have hr : x.rank = e.rank := Rank.toIdx_inj hcr
                cases x; cases e; simp_all
              rw [hxe]
              exact occurs_head _ rest
            · right
              refine ⟨?_, ?_⟩
              · intro c hc
                have hxc : x = c := by injection hc
                subst hxc
                exact hx
              · rw [rungAt_tabToFound hstep e.suit,
                  ite_eq_right (fun hh : e.suit = x.suit => hx hh.symm), hrung]
      rcases hkey with hocc | ⟨hheadne, hrung'⟩
      · exact Or.inr hocc
      · rcases ih hwf' hnp hrung' with hnone | hocc
        · left
          intro c hc
          by_cases hmc : m = Move.tabToFound c
          · exact hheadne c hmc
          · exact hnone c (occurs_tail hc (fun hh => hmc hh.symm))
        · exact Or.inr (occurs_cons hocc)

/-- **THE FROZEN RIGHT LEG HAS NO `e.suit` RAISE IFF IT HAS NO `raise e`.**
Contrapositive form of `no_sigma_raise_or_raise_e`, packaged for consumers. -/
theorem sigma_raise_of_raise_e_mem {st W : State} {play : List Move} {e : Card}
    (hplay : ShufflePlayW st play W) (hwf : st.WF)
    (hnopull : ∀ m ∈ play, ¬ Bubble.IsPull m)
    (hrung : rungAt st e.suit = e.rank.toIdx)
    (h : ∃ c : Card, Occurs (Move.tabToFound c) play ∧ c.suit = e.suit) :
    Occurs (Move.tabToFound e) play := by
  rcases no_sigma_raise_or_raise_e hplay hwf hnopull hrung with hnone | hocc
  · obtain ⟨c, hc, hcs⟩ := h
    exact absurd hcs (hnone c hc)
  · exact hocc

/-! ## §5. The split level: the survivor's death is a rank-mate raise -/

/-- **THE SURVIVOR'S DEATH IS A RANK-MATE RAISE.**  At a valley split whose
right leg is pull-free (`MountainKit.MountainSplit`), a card `e` S-live at the
pull landing does not survive to the saturated far endpoint `v`; hence the
right leg raises `e` or `e.twin`.

No third-suit hypothesis is used: the statement is about every S-live card. -/
theorem split_survivor_bad_raise
    {u v : State} {ρ : List Move} {F : State} {left right : List Move}
    {c d : Card} {b : Base} {pre post tail : List Move}
    (h : SplitKit.SplitHyp u v ρ F left right c d b pre post tail)
    (hms : MountainKit.MountainSplit left right)
    {A' B : State} (hpre : ShufflePlayW u pre A')
    (hstep : State.step A' (Move.foundToTab c b) = some B)
    {e : Card} (he : CanRaiseS B e) :
    Occurs (Move.tabToFound e) right ∨ Occurs (Move.tabToFound e.twin) right := by
  obtain ⟨huwf, hsu, hsv, hplay, hvs, hmin, hρ, hleft, hright, hshape, hfree, hrr⟩ := h
  have hF : F.WF := SatDifferCensus.ShufflePlayW.wf_end hleft huwf
  have heF : CanRaiseS F e := ThirdLive.third_alive_at_F ⟨huwf, hsu, hsv, hplay, hvs,
    hmin, hρ, hleft, hright, hshape, hfree, hrr⟩ hpre hstep he
  rcases canRaiseS_end_or_bad_raise hright hF hms.2 heF with h1 | h1 | h1
  · exact absurd h1 (hsv e)
  · exact Or.inl h1
  · exact Or.inr h1

/-- **THE SPLIT'S OWN PULL CARD.**  Sanity check of the mechanism against the
campaign's fork picture: the card `c` pulled at the bottom is S-live at its own
landing (`ValleyStep.pull_card_canRaise`), so its rank-mate is raised in the
right leg — for the census's splits this is `d = c.twin`, the head of `right`
(`Temp/SplitProbe_Report.md:243-250`). -/
theorem split_pull_card_bad_raise
    {u v : State} {ρ : List Move} {F : State} {left right : List Move}
    {c d : Card} {b : Base} {pre post tail : List Move}
    (h : SplitKit.SplitHyp u v ρ F left right c d b pre post tail)
    (hms : MountainKit.MountainSplit left right)
    {A' B : State} (hpre : ShufflePlayW u pre A')
    (hstep : State.step A' (Move.foundToTab c b) = some B) :
    Occurs (Move.tabToFound c) right ∨ Occurs (Move.tabToFound c.twin) right := by
  have hA' : A'.WF := SatDifferCensus.ShufflePlayW.wf_end hpre h.1
  exact split_survivor_bad_raise h hms hpre hstep
    (CanRaiseS.now c (ValleyStep.pull_card_canRaise hA' hstep))

/-- **THE COVER IS HARMLESS (kernel refutation of the "bury it" mechanism).**
If the right leg is draw/slide-only — no pulls, no raises at all — then `e`
stays S-live to the far endpoint.  So no stack of covers built by slides (a
"tower" whose top cannot be moved away) can destroy `e`'s S-liveness: the tower
is a slide chain and `CanRaiseS` is a slide-chain invariant
(`canRaiseS_survives_slide`). -/
theorem canRaiseS_survives_free_leg {F v : State} {right : List Move} {e : Card}
    (hplay : ShufflePlayW F right v) (hF : F.WF)
    (hnopull : ∀ m ∈ right, ¬ Bubble.IsPull m)
    (hnoraise : ∀ m ∈ right, ¬ Bubble.IsRaise m)
    (h : CanRaiseS F e) : CanRaiseS v e := by
  rcases canRaiseS_end_or_bad_raise hplay hF hnopull h with h1 | h1 | h1
  · exact h1
  · obtain ⟨s₁, s₂, hs⟩ := h1
    exact absurd ⟨e, rfl⟩ (hnoraise _ (by
      rw [hs]; exact List.mem_append_right _ (List.mem_cons_self ..)))
  · obtain ⟨s₁, s₂, hs⟩ := h1
    exact absurd ⟨e.twin, rfl⟩ (hnoraise _ (by
      rw [hs]; exact List.mem_append_right _ (List.mem_cons_self ..)))

/-- **THE ONLY NON-HARMLESS LETTERS ARE THE TWO RANK-MATES.**  A leg with no
pull and no raise outside `{e, e.twin}` preserves `CanRaiseS · e`. -/
theorem canRaiseS_survives_no_mate_raise {F v : State} {right : List Move} {e : Card}
    (hplay : ShufflePlayW F right v) (hF : F.WF)
    (hnopull : ∀ m ∈ right, ¬ Bubble.IsPull m)
    (hnor : ∀ c : Card, Occurs (Move.tabToFound c) right → c ≠ e ∧ c ≠ e.twin)
    (h : CanRaiseS F e) : CanRaiseS v e := by
  rcases canRaiseS_end_or_bad_raise hplay hF hnopull h with h1 | h1 | h1
  · exact h1
  · exact absurd rfl (hnor e h1).1
  · exact absurd rfl (hnor e.twin h1).2

/-- **THE FROZEN-BRANCH FORM.**  If in addition the right leg carries no raise
in `e`'s suit, the death is *exactly* a raise of `e.twin`.  This is the
replacement for `Surv.frozen_survivor_mechanism`'s cover taxonomy: covers and
run moves **cannot** be the cause; only the mate raise can. -/
theorem split_survivor_mate_raise
    {u v : State} {ρ : List Move} {F : State} {left right : List Move}
    {c d : Card} {b : Base} {pre post tail : List Move}
    (h : SplitKit.SplitHyp u v ρ F left right c d b pre post tail)
    (hms : MountainKit.MountainSplit left right)
    {A' B : State} (hpre : ShufflePlayW u pre A')
    (hstep : State.step A' (Move.foundToTab c b) = some B)
    {e : Card} (he : CanRaiseS B e)
    (hno : ∀ x : Card, Occurs (Move.tabToFound x) right → x.suit ≠ e.suit) :
    Occurs (Move.tabToFound e.twin) right := by
  rcases split_survivor_bad_raise h hms hpre hstep he with h1 | h1
  · exact absurd rfl (hno e h1)
  · exact h1

/-! ## §6. The residual: no mate raise in the right leg -/

/-- **`MateRaiseFree` — THE RESIDUAL.**  At every valley split with a
pull-free right leg, no third-suit card S-live at the pull landing has either
rank-mate raised in the right leg: the right leg raises neither `e` nor
`e.twin`.  This is a *raise*-exclusion: it says nothing about brackets, covers
or commutation.

By `sigma_raise_of_raise_e_mem` the first conjunct is exactly the frozen
hypothesis (no `e.suit` raise in the right leg). -/
def MateRaiseFree : Prop :=
  ∀ (u v : State) (ρ : List Move) (F : State)
    (left right : List Move) (c d : Card) (b : Base)
    (pre post tail : List Move),
    SplitKit.SplitHyp u v ρ F left right c d b pre post tail →
    MountainKit.MountainSplit left right →
    ∀ (A' B : State), ShufflePlayW u pre A' →
      State.step A' (Move.foundToTab c b) = some B →
      ∀ e : Card, CanRaiseS B e → e.suit ≠ c.suit → e.suit ≠ c.twin.suit →
        ¬ Occurs (Move.tabToFound e) right ∧
          ¬ Occurs (Move.tabToFound e.twin) right

/-- **`MountainAtSplits` — the standing mountain shape, at the split's own
turn.**  (Implied by `MountainKit`'s `MountainShape`; kept as its own name so
the new residual is the only fresh input.) -/
def MountainAtSplits : Prop :=
  ∀ (u v : State) (ρ : List Move) (F : State)
    (left right : List Move) (c d : Card) (b : Base)
    (pre post tail : List Move),
    SplitKit.SplitHyp u v ρ F left right c d b pre post tail →
    MountainKit.MountainSplit left right

/-- **THE TARGET FROM THE NEW RESIDUAL.**  `LandingThirdSuitFree` (the
containment half of `Mech.LandingLivePair`) follows from the mountain shape and
the raise-exclusion `MateRaiseFree`. -/
theorem landingThirdSuitFree_of_mateRaiseFree
    (hmt : MountainAtSplits) (h : MateRaiseFree) :
    Landing.LandingThirdSuitFree := by
  intro u v ρ F left right c d b pre post tail hs A' B hpre hstep e he h1 h2
  have hms := hmt u v ρ F left right c d b pre post tail hs
  obtain ⟨hnoe, hnot⟩ := h u v ρ F left right c d b pre post tail hs hms
    A' B hpre hstep e he h1 h2
  rcases split_survivor_bad_raise hs hms hpre hstep he with hbad | hbad
  · exact hnoe hbad
  · exact hnot hbad

end Direct

#print axioms Direct.occurs_cons
#print axioms Direct.occurs_tail
#print axioms Direct.canRaiseS_survives_draw
#print axioms Direct.canRaiseS_survives_slide
#print axioms Direct.canRaiseS_survives_raise_of_ne
#print axioms Direct.canRaiseS_of_canRaiseS_raise_high'
#print axioms Direct.canRaiseS_end_or_bad_raise
#print axioms Direct.no_sigma_raise_or_raise_e
#print axioms Direct.sigma_raise_of_raise_e_mem
#print axioms Direct.split_survivor_bad_raise
#print axioms Direct.split_pull_card_bad_raise
#print axioms Direct.canRaiseS_survives_free_leg
#print axioms Direct.canRaiseS_survives_no_mate_raise
#print axioms Direct.split_survivor_mate_raise
#print axioms Direct.MateRaiseFree
#print axioms Direct.MountainAtSplits
#print axioms Direct.landingThirdSuitFree_of_mateRaiseFree
