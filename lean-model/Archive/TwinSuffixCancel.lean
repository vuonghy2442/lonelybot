import Orig2.TwinPairFreeClass
import Orig2.TwinRaiseCommute
import Orig2.TwinSplicePlay
import Orig2.Classification
import Orig2.SeatMateStack
import Orig2.Integrity
import Orig2.Kit

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-!
# Orig2.TwinSuffixCancel — the last pair-foundation letter is a pull

This card continues `Orig2/TwinPairFreeClass.lean`.  The endpoint
classification splits a play at its **last** pair-foundation letter

```
pre ++ m :: suf,          suf pair-free.
```

The two unconditional rows proved here are:

* `pairFree_step_seat_none` / `pairFree_play_seat_none`: a pair-free
  reversible step (play) keeps an unseated twin unseated.  The per-letter
  proof cases on the move: a draw fixes every seat, the waste letters are
  never reversible, a raise keeps an unseated non-mover unseated
  (`raise_seat_none`), a pull changes only the pulled card's seat
  (`pull_seat_change`), and a reversible slide changes only its mover's
  seat (`tfc_seat_point_edit`), while an unseated mover cannot hold a pile.

* `last_pairFound_is_pull`: in the hypotheses of
  `PairFoundSuffixCancellation`, the last pair-foundation letter cannot be
  a raise.  A raise leaves its mover on the foundation (seat `none`), and
  the pair-free suffix preserves that `none` (first row), contradicting
  the endpoint's `.inr` seat.  Hence the last letter is one of the four
  pulls `foundToTab y b` with `y ∈ {x, x.twin}`.

Two further rows support the suffix reduction:

* `pairFree_play_seat_inl`: a pair-free play keeps a non-king card that is
  the root of its pile (`.inl` seat) at that root.  A reversible slide of
  a bare non-king is impossible (`tfc_leg_shape`), so no pair-free letter
  can move it.

* `pairFree_play_start_inr_of_end_inr`: a pair-free play ending with a
  non-king twin `.inr`-seated starts with that twin `.inr`-seated.  This
  is the row that makes the suffix reversal legal: the state after the
  last pull is both-.inr-seated.

The final section states the precise remaining obligation
(`LastPullCancellation`) and proves the canonical single-detour identity
case: a pair-free prefix, a raise of a twin, the immediate pull back onto
its original card parent, and a pair-free suffix.  The raise/pull pair is
a state-level identity (`tsc_raise_pull_self_eq`, a self-contained copy of
the `TwinSingleDetour` cancellation proof; that file is deliberately not
imported), so the endpoint is pair-free orbit to the source.

Zero `sorry`, zero `Classical.choice`, no new axioms.
-/

open State

/-! ## §1. Unseated twins stay unseated -/

/-- An unseated card holds no pile. -/
private theorem tsc_holding_none_of_seat_none {st : State} {c : Card}
    (h : seatOf st c = none) : st.pileHolding c = none := by
  cases hh : st.pileHolding c with
  | none => rfl
  | some a =>
      rw [tfc_seatOf_pair hh] at h
      cases hg : List.getLast? (below c (st.piles a).faceUp) <;> simp [hg] at h

/-- **Pair-free reversible steps keep an unseated twin unseated.** -/
theorem pairFree_step_seat_none {u v : State} {x y : Card} {m : Move}
    (hwf : u.WF) (hstep : State.step u m = some v)
    (hrev : reversibleAtW u m) (hno : NotFoundPair x m)
    (hy : y = x ∨ y = x.twin) (hseat : seatOf u y = none) :
    seatOf v y = none := by
  have hhold : u.pileHolding y = none := tsc_holding_none_of_seat_none hseat
  cases m with
  | draw =>
      exact (chart_draw hstep).1 y ▸ hseat
  | wasteToFound c =>
      exact absurd hrev (wasteToFound_not_reversibleAtW u c)
  | wasteToTab c b =>
      exact absurd hrev (wasteToTab_not_reversibleAtW u c b)
  | tabToFound d =>
      have hyd : y ≠ d := by
        intro h
        rcases hy with hx | hx
        · exact hno.1 (congrArg Move.tabToFound (h.symm.trans hx))
        · exact hno.2.1 (congrArg Move.tabToFound (h.symm.trans hx))
      obtain ⟨-, a, hpa, -⟩ := step_tabToFound_inv hstep
      exact TwinSpliceComm.raise_seat_none hwf hstep hrev hpa hseat hyd
  | foundToTab d b =>
      have hyd : y ≠ d := by
        intro h
        rcases hy with hx | hx
        · exact hno.2.2.1 b (congrArg (fun c => Move.foundToTab c b) (h.symm.trans hx))
        · exact hno.2.2.2 b (congrArg (fun c => Move.foundToTab c b) (h.symm.trans hx))
      exact (pull_seat_change hstep y hyd).trans hseat
  | tabToTab d b =>
      obtain ⟨a, hholdD, -, -, -⟩ := step_tabToTab_inv hstep
      have hyd : y ≠ d := by
        intro h
        subst h
        rw [hhold] at hholdD
        cases hholdD
      have h := tfc_seat_point_edit hwf hstep hrev y
      rw [ite_eq_right hyd] at h
      exact h.trans hseat

/-- **Pair-free plays keep an unseated twin unseated.** -/
theorem pairFree_play_seat_none {x y : Card} {s t : State} {play : List Move}
    (hwf : s.WF) (hplay : ShufflePlayW s play t)
    (hno : ∀ m ∈ play, NotFoundPair x m)
    (hy : y = x ∨ y = x.twin) (hseat : seatOf s y = none) :
    seatOf t y = none := by
  induction hplay with
  | nil st => exact hseat
  | @cons st mid w m rest hrev hstep hrest ih =>
      have hnone : seatOf mid y = none :=
        pairFree_step_seat_none hwf hstep hrev (hno m (by simp)) hy hseat
      exact ih (step_wf hwf hstep)
        (fun n hn => hno n (List.mem_cons_of_mem m hn)) hnone

/-! ## §2. Card-parent arithmetic for a twin -/

/-- A card seated `.inr` on a card parent is not a king: a king fits no
card base (`canSitOn` demands the parent one rank higher). -/
theorem tsc_rank_ne_king_of_inr {s : State} {c z : Card}
    (hwf : s.WF) (h : seatOf s c = some (Sum.inr z)) :
    c.rank ≠ Rank.king := by
  obtain ⟨a, hhold, -, hlast⟩ := tfc_seatOf_of_inr h
  have hsit := (tfc_seat_parent hwf hhold hlast).1
  intro hk
  rw [canSitOn_eq] at hsit
  have hkidx : c.rank.toIdx = 12 := by rw [hk]; rfl
  have hzlt : z.rank.toIdx < 13 := Rank.toIdx_lt z.rank
  omega

/-- Both twins are non-kings at a both-`.inr` state. -/
theorem tsc_twin_rank_ne_king {u : State} {x z zt : Card}
    (hwf : u.WF)
    (hx : seatOf u x = some (Sum.inr z))
    (hxt : seatOf u x.twin = some (Sum.inr zt.twin)) :
    x.rank ≠ Rank.king ∧ x.twin.rank ≠ Rank.king :=
  ⟨tsc_rank_ne_king_of_inr hwf hx, tsc_rank_ne_king_of_inr hwf hxt⟩

/-! ## §3. Rooted (`.inl`) twins stay rooted -/

/-- **Pair-free reversible steps keep a non-king `.inl` card rooted.**
The only letter that changes a non-mover's seat is a slide, whose mover
is that card; a reversible slide of a bare non-king is impossible, and an
`.inl` seat has an empty below-part. -/
theorem pairFree_step_seat_inl {u v : State} {x y : Card} {m : Move} {a : Anchor}
    (hwf : u.WF) (hstep : State.step u m = some v)
    (hrev : reversibleAtW u m) (hno : NotFoundPair x m)
    (hnk : y.rank ≠ Rank.king) (hy : y = x ∨ y = x.twin)
    (hseat : seatOf u y = some (Sum.inl a)) :
    seatOf v y = some (Sum.inl a) := by
  cases m with
  | draw =>
      rw [(chart_draw hstep).1 y]
      exact hseat
  | wasteToFound c =>
      exact absurd hrev (wasteToFound_not_reversibleAtW u c)
  | wasteToTab c b =>
      exact absurd hrev (wasteToTab_not_reversibleAtW u c b)
  | tabToFound d =>
      have hyd : y ≠ d := by
        intro h
        rcases hy with hx | hx
        · exact hno.1 (congrArg Move.tabToFound (h.symm.trans hx))
        · exact hno.2.1 (congrArg Move.tabToFound (h.symm.trans hx))
      have hne : seatOf u y ≠ none := by rw [hseat]; simp
      exact (raise_seat_change_of_seated hstep hrev hne hyd).trans hseat
  | foundToTab d b =>
      have hyd : y ≠ d := by
        intro h
        rcases hy with hx | hx
        · exact hno.2.2.1 b (congrArg (fun c => Move.foundToTab c b) (h.symm.trans hx))
        · exact hno.2.2.2 b (congrArg (fun c => Move.foundToTab c b) (h.symm.trans hx))
      exact (pull_seat_change hstep y hyd).trans hseat
  | tabToTab d b =>
      by_cases hyd : y = d
      · subst hyd
        obtain ⟨a', tr, s', hhold, hcp, hface, hcrr, hleg, hstep'⟩ :=
          tfc_leg_shape hwf hrev
        obtain ⟨hholdY, hbelowY⟩ := tfc_seatOf_of_inl hseat
        have ha'a : a' = a := by
          rw [hholdY] at hhold
          exact Option.some.inj hhold.symm
        have hbelow : below y (u.piles a').faceUp = [] := by
          rw [ha'a]
          exact hbelowY
        rcases hleg with hne | ⟨-, -, hking⟩
        · exfalso
          rw [hbelow] at hne
          exact absurd rfl hne
        · exact absurd hking hnk
      · have h := tfc_seat_point_edit hwf hstep hrev y
        rw [ite_eq_right hyd] at h
        rw [h]
        exact hseat

/-- **Pair-free plays keep a non-king `.inl` card rooted.** -/
theorem pairFree_play_seat_inl {x y : Card} {a : Anchor} {s t : State}
    {play : List Move}
    (hwf : s.WF) (hplay : ShufflePlayW s play t)
    (hno : ∀ m ∈ play, NotFoundPair x m)
    (hnk : y.rank ≠ Rank.king) (hy : y = x ∨ y = x.twin)
    (hseat : seatOf s y = some (Sum.inl a)) :
    seatOf t y = some (Sum.inl a) := by
  induction hplay with
  | nil st => exact hseat
  | @cons st mid w m rest hrev hstep hrest ih =>
      have hseat' : seatOf mid y = some (Sum.inl a) :=
        pairFree_step_seat_inl hwf hstep hrev (hno m (by simp)) hnk hy hseat
      exact ih (step_wf hwf hstep)
        (fun n hn => hno n (List.mem_cons_of_mem m hn)) hseat'

/-- **A pair-free play ending in an `.inr` twin starts in an `.inr`
twin.**  The twin is a non-king (both twins are `.inr` at the common
source of the intended applications), a `none` seat is preserved by
`pairFree_play_seat_none`, and an `.inl` seat is preserved by
`pairFree_play_seat_inl`. -/
theorem pairFree_play_start_inr_of_end_inr {x y : Card} {s t : State}
    {play : List Move}
    (hwf : s.WF) (hplay : ShufflePlayW s play t)
    (hno : ∀ m ∈ play, NotFoundPair x m)
    (hnk : y.rank ≠ Rank.king) (hy : y = x ∨ y = x.twin)
    (hend : ∃ p, seatOf t y = some (Sum.inr p)) :
    ∃ p, seatOf s y = some (Sum.inr p) := by
  have hse : seatOf s y ≠ none := by
    intro hnone
    have hvnone := pairFree_play_seat_none hwf hplay hno hy hnone
    obtain ⟨p, hp⟩ := hend
    rw [hvnone] at hp
    cases hp
  obtain ⟨b, hb⟩ := option_some_of_ne_none hse
  cases b with
  | inl a =>
      have hinl := pairFree_play_seat_inl hwf hplay hno hnk hy hb
      obtain ⟨p, hp⟩ := hend
      rw [hinl] at hp
      cases hp
  | inr p => exact ⟨p, hb⟩

/-- Split a witness walk at a list prefix. -/
private theorem tsc_walk_split {P : State → Move → Prop} :
    ∀ {s s' : State} {A B : List Move},
      Walk P s (A ++ B) s' → ∃ u, Walk P s A u ∧ Walk P u B s' := by
  intro s s' A B
  induction A generalizing s with
  | nil =>
      intro h
      exact ⟨s, .nil s, by simpa using h⟩
  | cons m rest ih =>
      intro h
      cases h with
      | cons hlet hstep hrest =>
          obtain ⟨u, hA, hB⟩ := ih hrest
          exact ⟨u, .cons hlet hstep hA, hB⟩

/-- Expose the first letter of a witness walk and its successor. -/
private theorem tsc_walk_cons_inv {P : State → Move → Prop} {st s' : State}
    {m : Move} {ρ : List Move} (h : Walk P st (m :: ρ) s') :
    ∃ s1, P st m ∧ State.step st m = some s1 ∧ Walk P s1 ρ s' := by
  cases h with
  | cons hlet hstep hrest => exact ⟨_, hlet, hstep, hrest⟩

/-! ## §3.1. Exact `.inr` seat preservation (private copy) -/

/-- A pair-free reversible letter fixes both twins' `.inr` seats **exactly**
at a both-`.inr` state.  This is the equality form used by the detour
cancellation below (the same per-letter analysis as the public existence
row `seat_inr_of_pairFree_step`, with the conclusion strengthened). -/
private theorem tsc_seat_eq_of_pairFree_step {u v : State} {x : Card} {m : Move}
    (hwf : u.WF) (hstep : State.step u m = some v)
    (hrev : reversibleAtW u m) (hno : NotFoundPair x m)
    (hx : ∃ z, seatOf u x = some (Sum.inr z))
    (hxt : ∃ z : Card, seatOf u x.twin = some (Sum.inr z.twin)) :
    seatOf v x = seatOf u x ∧ seatOf v x.twin = seatOf u x.twin := by
  have hse_x : seatOf u x ≠ none := by
    obtain ⟨z, hz⟩ := hx
    rw [hz]
    simp
  have hse_xt : seatOf u x.twin ≠ none := by
    obtain ⟨z, hz⟩ := hxt
    rw [hz]
    simp
  have hxEq : seatOf v x = seatOf u x := by
    cases m with
    | draw => exact (chart_draw hstep).1 x
    | wasteToFound y => exact absurd hrev (wasteToFound_not_reversibleAtW u y)
    | wasteToTab y base => exact absurd hrev (wasteToTab_not_reversibleAtW u y base)
    | tabToFound y =>
        have hyx : y ≠ x := fun h => hno.1 (by rw [h])
        exact raise_seat_change_of_seated hstep hrev hse_x (Ne.symm hyx)
    | foundToTab y base =>
        have hyx : y ≠ x := fun h => hno.2.2.1 base (by rw [h])
        exact pull_seat_change hstep x (Ne.symm hyx)
    | tabToTab y base =>
        obtain ⟨hyx, -⟩ := TwinSpliceComm.tabToTab_mover_off hwf hx hxt hstep
        have h := tfc_seat_point_edit hwf hstep hrev x
        rwa [ite_eq_right (Ne.symm hyx)] at h
  have hxtEq : seatOf v x.twin = seatOf u x.twin := by
    cases m with
    | draw => exact (chart_draw hstep).1 x.twin
    | wasteToFound y => exact absurd hrev (wasteToFound_not_reversibleAtW u y)
    | wasteToTab y base => exact absurd hrev (wasteToTab_not_reversibleAtW u y base)
    | tabToFound y =>
        have hyt : y ≠ x.twin := fun h => hno.2.1 (by rw [h])
        exact raise_seat_change_of_seated hstep hrev hse_xt (Ne.symm hyt)
    | foundToTab y base =>
        have hyt : y ≠ x.twin := fun h => hno.2.2.2 base (by rw [h])
        exact pull_seat_change hstep x.twin (Ne.symm hyt)
    | tabToTab y base =>
        obtain ⟨-, hyt⟩ := TwinSpliceComm.tabToTab_mover_off hwf hx hxt hstep
        have h := tfc_seat_point_edit hwf hstep hrev x.twin
        rwa [ite_eq_right (Ne.symm hyt)] at h
  exact ⟨hxEq, hxtEq⟩

/-- A pair-free witness shuffle fixes both twins' `.inr` seats verbatim. -/
private theorem tsc_seat_eq_of_pairFree_play {x : Card} :
    ∀ {s w : State} {seg : List Move},
      s.WF → ShufflePlayW s seg w →
      (∀ m ∈ seg, NotFoundPair x m) →
      (∃ z, seatOf s x = some (Sum.inr z)) →
      (∃ z : Card, seatOf s x.twin = some (Sum.inr z.twin)) →
      seatOf w x = seatOf s x ∧ seatOf w x.twin = seatOf s x.twin := by
  intro s w seg
  induction seg generalizing s with
  | nil =>
      intro _ hplay _ _ _
      cases hplay
      exact ⟨rfl, rfl⟩
  | cons m rest ih =>
      intro hwf hplay hno hx hxt
      obtain ⟨s₁, hrev, hstep, hrest⟩ := tsc_walk_cons_inv hplay
      have hm : NotFoundPair x m := hno m (by simp)
      have hstepEq := tsc_seat_eq_of_pairFree_step hwf hstep hrev hm hx hxt
      have hx₁ : ∃ z, seatOf s₁ x = some (Sum.inr z) := by
        obtain ⟨z, hz⟩ := hx
        exact ⟨z, by rw [hstepEq.1, hz]⟩
      have hxt₁ : ∃ z : Card, seatOf s₁ x.twin = some (Sum.inr z.twin) := by
        obtain ⟨z, hz⟩ := hxt
        exact ⟨z, by rw [hstepEq.2, hz]⟩
      have hwf₁ : s₁.WF := step_wf hwf hstep
      have ih' := ih hwf₁ hrest
        (fun n hn => hno n (List.mem_cons_of_mem m hn)) hx₁ hxt₁
      exact ⟨ih'.1.trans hstepEq.1, ih'.2.trans hstepEq.2⟩

/-! ## §3.2. Raise-then-pull cancellation (self-contained copy) -/

/-- **`tsc_raise_pull_self_eq`** — raising a card off its card parent and
then pulling it back onto that parent restores the source exactly.
(Self-contained copy of the `TwinSingleDetour` row; that file is not
imported.) -/
private theorem tsc_raise_pull_self_eq {s s₁ s₂ : State} {x z : Card}
    (hwf : s.WF)
    (hx : seatOf s x = some (Sum.inr z))
    (hraise : State.step s (Move.tabToFound x) = some s₁)
    (hpull : State.step s₁ (Move.foundToTab x (Sum.inr z)) = some s₂) :
    s₂ = s := by
  obtain ⟨a, hhold, _hbelow_ne, hlast⟩ := tfc_seatOf_of_inr hx
  obtain ⟨_hnext, a₀, hpa₀, hs₁⟩ := step_tabToFound_inv hraise
  have htop₀ : (s.piles a₀).top = some x := (tfc_pileOfTop_top hpa₀).2
  have hhold₀ : s.pileHolding x = some a₀ :=
    (pileHolding_eq_some_iff hwf).mpr (Pile.mem_of_top htop₀)
  have ha₀ : a₀ = a := pileHolding_inj hhold₀ hhold
  subst a₀
  let st₁ : State :=
    { s.setFound x.suit (s.found x.suit ++ [x]) with
      piles := fun a' => if a' = a then
          Pile.afterRunRemoved (s.piles a) (chop (s.piles a).faceUp)
        else s.piles a' }
  have hs₁' : s₁ = st₁ := hs₁
  have htop : lastOf (s.piles a).faceUp = some x := (tfc_pileOfTop_top hpa₀).2
  have hface : (s.piles a).faceUp = chop (s.piles a).faceUp ++ [x] :=
    lastOf_chop htop
  have hnodup : (s.piles a).faceUp.Nodup := runOK_nodup (hwf.runOK_of a)
  have hx_not_chop : x ∉ chop (s.piles a).faceUp := by
    rw [hface] at hnodup
    exact List.snoc_nodup_notMem _ _ hnodup
  have hbelow_eq : below x (s.piles a).faceUp = chop (s.piles a).faceUp := by
    conv =>
      lhs
      rw [hface]
    exact below_snoc_not_mem hx_not_chop
  have hlast_chop : lastOf (chop (s.piles a).faceUp) = some z := by
    rw [← hbelow_eq]
    exact hlast
  have hchop_ne : chop (s.piles a).faceUp ≠ [] := by
    intro h
    rw [h] at hlast_chop
    nomatch hlast_chop
  have hs₁_pa : s₁.piles a =
      Pile.afterRunRemoved (s.piles a) (chop (s.piles a).faceUp) := by
    rw [hs₁']
    simp only [st₁, ite_true]
  have hs₁_pne : ∀ a' ≠ a, s₁.piles a' = s.piles a' := by
    intro a' ha'
    rw [hs₁']
    simp only [st₁, ite_eq_right ha']
  have hs₁_face : (s₁.piles a).faceUp = chop (s.piles a).faceUp := by
    rw [hs₁_pa, afterRunRemoved_faceUp_ne hchop_ne]
  have hwf₁ : s₁.WF := step_wf hwf hraise
  have hs₁_top_z : s₁.pileOfTop z = some a := by
    rw [pileOfTop_eq_some_iff hwf₁]
    show lastOf (s₁.piles a).faceUp = some z
    rw [hs₁_face]
    exact hlast_chop
  have hfit : canSitOn x z = true := (tfc_seat_parent hwf hhold hlast).1
  have hcp : s₁.canPlace x (Sum.inr z) = true := by
    rw [canPlace_inr_located hs₁_top_z]
    exact hfit
  have hfound_trio := tabToFound_found_trio (st := s) (s₁ := s₁)
    (c := x) (a := a) hs₁
  have hs₁_found_self : s₁.found x.suit = s.found x.suit ++ [x] :=
    hfound_trio.1
  have hs₁_found_ne : ∀ σ, σ ≠ x.suit → s₁.found σ = s.found σ :=
    hfound_trio.2.1
  have hs₁_foundTop : s₁.foundTop x.suit = some x := hfound_trio.2.2
  have hpull_eq : s₂ =
      (s₁.setFound x.suit (chop (s₁.found x.suit))).putCard x (Sum.inr z) := by
    have hfire := step_foundToTab_splice (st := s₁) (c := x)
      (b := Sum.inr z) hs₁_foundTop hcp
    rw [hfire] at hpull
    exact (Option.some.inj hpull).symm
  subst hpull_eq
  refine State.ext ?_ ?_ ?_ ?_ ?_
  · funext σ
    rw [putCard_found]
    by_cases hσ : σ = x.suit
    · rw [hσ, setFound_found_self, hs₁_found_self, chop_snoc]
    · rw [setFound_found_ne hσ, hs₁_found_ne σ hσ]
  · funext a'
    have hset_top : (s₁.setFound x.suit (chop (s₁.found x.suit))).pileOfTop z =
        some a := by
      unfold State.pileOfTop State.topOf
      rw [setFound_piles]
      exact hs₁_top_z
    rw [putCard_piles_inr (s₁.setFound x.suit (chop (s₁.found x.suit))) x z a
      hset_top]
    dsimp only
    by_cases ha' : a' = a
    · rw [ha', ite_eq_left rfl, setFound_piles]
      apply Pile.ext
      · rw [hs₁_pa, afterRunRemoved_ne hchop_ne]
      · rw [hs₁_face]
        exact hface.symm
    · rw [ite_eq_right ha', setFound_piles, hs₁_pne a' ha']
  · rw [putCard_stock, setFound_stock]
    rw [hs₁']
    rfl
  · rw [putCard_waste, setFound_waste]
    rw [hs₁']
    rfl
  · rw [putCard_drawStep, setFound_drawStep]
    rw [hs₁']
    rfl

/-! ## §5. The last pair-foundation letter is a pull -/

/-- **The last pair-foundation letter cannot be a raise.**  A raise of
either twin leaves that twin unseated; the pair-free suffix preserves the
`none` seat, contradicting the endpoint's `.inr` seat. -/
theorem last_pairFound_is_pull {x : Card} {u v : State} {z : Card}
    {pre : List Move} {m : Move} {suf : List Move}
    (hwf : u.WF)
    (hx : seatOf u x = some (Sum.inr z))
    (hxt : seatOf u x.twin = some (Sum.inr z.twin))
    (hplay : ShufflePlayW u (pre ++ m :: suf) v)
    (hm : IsPairFound x m)
    (hnoSuf : ∀ n ∈ suf, NotFoundPair x n)
    (hvx : ∃ w, seatOf v x = some (Sum.inr w))
    (hvt : ∃ w', seatOf v x.twin = some (Sum.inr w')) :
    ∃ y b, (y = x ∨ y = x.twin) ∧ m = Move.foundToTab y b := by
  rcases hm with hraise | hraise | ⟨b, hpull⟩ | ⟨b, hpull⟩
  · -- raising `x`
    subst hraise
    obtain ⟨s, hpre, hrest⟩ := tsc_walk_split hplay
    obtain ⟨s1, -, hstep, htail⟩ := tsc_walk_cons_inv hrest
    have hswf : s.WF := run_wf hwf (Walk_run _ hpre)
    have hs1wf : s1.WF := step_wf hswf hstep
    have hnone : seatOf s1 x = none :=
      TwinSpliceComm.seatOf_tabToFound_mover_none hswf hstep
    have hnoneV : seatOf v x = none :=
      pairFree_play_seat_none hs1wf htail hnoSuf (Or.inl rfl) hnone
    obtain ⟨w, hw⟩ := hvx
    rw [hnoneV] at hw
    cases hw
  · -- raising `x.twin`
    subst hraise
    obtain ⟨s, hpre, hrest⟩ := tsc_walk_split hplay
    obtain ⟨s1, -, hstep, htail⟩ := tsc_walk_cons_inv hrest
    have hswf : s.WF := run_wf hwf (Walk_run _ hpre)
    have hs1wf : s1.WF := step_wf hswf hstep
    have hnone : seatOf s1 x.twin = none :=
      TwinSpliceComm.seatOf_tabToFound_mover_none hswf hstep
    have hnoneV : seatOf v x.twin = none :=
      pairFree_play_seat_none hs1wf htail hnoSuf (Or.inr rfl) hnone
    obtain ⟨w', hw'⟩ := hvt
    rw [hnoneV] at hw'
    cases hw'
  · -- pulling `x`
    subst hpull
    exact ⟨x, b, Or.inl rfl, rfl⟩
  · -- pulling `x.twin`
    subst hpull
    exact ⟨x.twin, b, Or.inr rfl, rfl⟩

/-- **The last pull's base is the original parent or its twin.**  The
pull's placement license supplies `canSitOn y b`, and `y` was seated on
`p` at the source; `tfc_fitting_parent` pins the card base.  This is the
forced-target row used by the remaining cancellation. -/
theorem lastPull_base_eq_parent_or_twin {u v : State} {pre : List Move}
    {y p : Card} {b : Base}
    (hwf : u.WF)
    (hyp : seatOf u y = some (Sum.inr p))
    (hplay : ShufflePlayW u (pre ++ [Move.foundToTab y b]) v)
    (hvy : ∃ q, seatOf v y = some (Sum.inr q)) :
    b = Sum.inr p ∨ b = Sum.inr p.twin := by
  obtain ⟨s, hpre, hrest⟩ := tsc_walk_split hplay
  obtain ⟨w, -, hstep, hnil⟩ := tsc_walk_cons_inv hrest
  cases hnil
  have hswf : s.WF := run_wf hwf (Walk_run _ hpre)
  obtain ⟨c', htop, hc', hcp, hs⟩ := step_foundToTab_inv hstep
  cases b with
  | inl a =>
      have hmover : seatOf v y = some (Sum.inl a) :=
        TwinSpliceComm.seatOf_foundToTab_mover hswf hstep
      obtain ⟨q, hq⟩ := hvy
      rw [hmover] at hq
      cases hq
  | inr z =>
      obtain ⟨k, hk, hfit⟩ := canPlace_inr hcp
      rcases canSitOn_target_eq_parent_or_twin hwf hyp hfit with h | h
      · exact Or.inl (by rw [h])
      · exact Or.inr (by rw [h])

/-! ## §6. The suffix reduction -/

/-- **`LastPullCancellation x`** — the precise remaining obligation of the
last-letter analysis: a play of the shape `pre ++ [m]` whose last letter
`m` is pair-foundation, whose source and endpoint are both `.inr`-seated,
already satisfies the endpoint conclusion.  The pair-free suffix has been
stripped; `m` is a pull by `last_pairFound_is_pull`. -/
def LastPullCancellation (x : Card) : Prop :=
  ∀ {u v : State} {z : Card} {pre : List Move} {m : Move},
    u.WF →
    seatOf u x = some (Sum.inr z) →
    seatOf u x.twin = some (Sum.inr z.twin) →
    ShufflePlayW u (pre ++ [m]) v →
    IsPairFound x m →
    (∃ w, seatOf v x = some (Sum.inr w)) →
    (∃ w' : Card, seatOf v x.twin = some (Sum.inr w')) →
    PairFreeOrbit x v u ∨ PairFreeOrbit x v (u.spliceTwinRuns x)

/-- **The suffix reduction.**  Pair-free reversal of the suffix (made
legal by `pairFree_play_start_inr_of_end_inr`), followed by the
last-letter obligation on the prefix. -/
theorem pairFoundSuffixCancellation_of_reversal_of_lastPull {x : Card}
    (hrev : PairFreeReversal x) (hlast : LastPullCancellation x) :
    PairFoundSuffixCancellation x := by
  intro u v z pre m suf hwf hx hxt hplay hm hnoSuf hvx hvt
  obtain ⟨s, hpre, hrest⟩ := tsc_walk_split hplay
  obtain ⟨w, hrevM, hmstep, hsuf⟩ := tsc_walk_cons_inv hrest
  have hprem : ShufflePlayW u (pre ++ [m]) w :=
    ShufflePlayW_append hpre (Walk.cons hrevM hmstep (Walk.nil w))
  have hwwf : w.WF := run_wf hwf (Walk_run _ hprem)
  have hrank := tsc_twin_rank_ne_king hwf hx hxt
  obtain ⟨zx, hzx⟩ :=
    pairFree_play_start_inr_of_end_inr hwwf hsuf hnoSuf hrank.1 (Or.inl rfl) hvx
  obtain ⟨p, hp⟩ :=
    pairFree_play_start_inr_of_end_inr hwwf hsuf hnoSuf hrank.2 (Or.inr rfl) hvt
  have hpt : p.twin = zx := by
    have hpform : seatOf w x.twin = some (Sum.inr p.twin.twin) := by
      simpa [card_twin_twin] using hp
    exact twin_parent_eq_of_seats hwwf hzx hpform
  have hpzx : p = zx.twin := by
    have := congrArg Card.twin hpt
    simpa [card_twin_twin] using this
  have hp' : seatOf w x.twin = some (Sum.inr zx.twin) := by
    rw [← hpzx]
    exact hp
  have hback : PairFreeOrbit x v w := hrev hwwf hzx hp' hsuf hnoSuf
  have hlast' : PairFreeOrbit x w u ∨ PairFreeOrbit x w (u.spliceTwinRuns x) :=
    hlast hwf hx hxt hprem hm ⟨zx, hzx⟩ ⟨p, hp⟩
  rcases hlast' with h | h
  · exact Or.inl (PairFreeOrbit.trans hback h)
  · exact Or.inr (PairFreeOrbit.trans hback h)

/-- `LastPullCancellation` is a subcase of the full suffix cancellation
(the suffix is empty). -/
theorem lastPullCancellation_of_pairFoundSuffixCancellation {x : Card}
    (hsuf : PairFoundSuffixCancellation x) : LastPullCancellation x := by
  intro u v z pre m hwf hx hxt hplay hm hvx hvt
  exact hsuf hwf hx hxt (by simpa using hplay) hm (by simp) hvx hvt

/-- **The exact form of the remaining gap.**  Given pair-free reversal,
the full last-letter cancellation is equivalent to the empty-suffix
obligation `LastPullCancellation x`. -/
theorem pairFoundSuffixCancellation_iff_lastPull_of_reversal {x : Card}
    (hrev : PairFreeReversal x) :
    PairFoundSuffixCancellation x ↔ LastPullCancellation x :=
  ⟨lastPullCancellation_of_pairFoundSuffixCancellation,
    pairFoundSuffixCancellation_of_reversal_of_lastPull hrev⟩

/-! ### §6.1. The canonical single-detour identity subcase -/

/-- **Canonical identity detour, arbitrary pair-free ends.**  The play is

```
pre ++ [raise y] ++ [pull y back onto its original parent] ++ suf
```

with `pre` and `suf` pair-free.  The raise/pull pair is a state-level
identity (`tsc_raise_pull_self_eq`), so the endpoint is pair-free orbit to
the source by reversing the two pair-free ends.  This is a non-vacuous
subcase of the missing `LastPullCancellation`: the arbitrary pair-free
prefix moves other cards, and the suffix may be any pair-free play. -/
theorem pairFree_singleDetour_identity {x z p : Card} {u v : State}
    {pre suf : List Move} {y : Card}
    (hrev : PairFreeReversal x)
    (hwf : u.WF)
    (hx : seatOf u x = some (Sum.inr z))
    (hxt : seatOf u x.twin = some (Sum.inr z.twin))
    (hy : y = x ∨ y = x.twin)
    (hseatY : seatOf u y = some (Sum.inr p))
    (hplay : ShufflePlayW u
      (pre ++ Move.tabToFound y :: Move.foundToTab y (Sum.inr p) :: suf) v)
    (hnoPre : ∀ m ∈ pre, NotFoundPair x m)
    (hnoSuf : ∀ m ∈ suf, NotFoundPair x m)
    (hvx : ∃ w, seatOf v x = some (Sum.inr w))
    (hvt : ∃ w' : Card, seatOf v x.twin = some (Sum.inr w'.twin)) :
    PairFreeOrbit x v u ∨ PairFreeOrbit x v (u.spliceTwinRuns x) := by
  obtain ⟨u₁, hpre, hrest⟩ := tsc_walk_split hplay
  obtain ⟨s₁, -, hraise, hrest₁⟩ := tsc_walk_cons_inv hrest
  obtain ⟨w, -, hpull, hsuf⟩ := tsc_walk_cons_inv hrest₁
  have hwf₁ : u₁.WF := run_wf hwf (Walk_run _ hpre)
  have hseats :=
    tsc_seat_eq_of_pairFree_play hwf hpre hnoPre ⟨z, hx⟩ ⟨z, hxt⟩
  have hx₁ : seatOf u₁ x = some (Sum.inr z) := hseats.1.trans hx
  have hxt₁ : seatOf u₁ x.twin = some (Sum.inr z.twin) := hseats.2.trans hxt
  have hy₁ : seatOf u₁ y = some (Sum.inr p) := by
    rcases hy with rfl | rfl
    · rw [hseats.1]
      exact hseatY
    · rw [hseats.2]
      exact hseatY
  have hcancel : w = u₁ := tsc_raise_pull_self_eq hwf₁ hy₁ hraise hpull
  rw [hcancel] at hsuf
  have hback : PairFreeOrbit x v u₁ := hrev hwf₁ hx₁ hxt₁ hsuf hnoSuf
  have hpreback : PairFreeOrbit x u₁ u := hrev hwf hx hxt hpre hnoPre
  exact Or.inl (PairFreeOrbit.trans hback hpreback)

/-! ## §7. Audit -/

#print axioms pairFree_step_seat_none
#print axioms pairFree_play_seat_none
#print axioms tsc_rank_ne_king_of_inr
#print axioms tsc_twin_rank_ne_king
#print axioms pairFree_step_seat_inl
#print axioms pairFree_play_seat_inl
#print axioms pairFree_play_start_inr_of_end_inr
#print axioms last_pairFound_is_pull
#print axioms lastPull_base_eq_parent_or_twin
#print axioms tsc_seat_eq_of_pairFree_play
#print axioms tsc_raise_pull_self_eq
#print axioms pairFoundSuffixCancellation_of_reversal_of_lastPull
#print axioms lastPullCancellation_of_pairFoundSuffixCancellation
#print axioms pairFoundSuffixCancellation_iff_lastPull_of_reversal
#print axioms pairFree_singleDetour_identity

/-! ## §8. Report: exact remaining goal

Deliverables 1 and 2 are unconditional:

* `pairFree_step_seat_none`, `pairFree_play_seat_none`;
* `last_pairFound_is_pull` (and the supporting
  `pairFree_step_seat_inl`, `pairFree_play_seat_inl`,
  `pairFree_play_start_inr_of_end_inr`).

Deliverable 3 is reduced exactly.  The single-detour identity subcase
`pairFree_singleDetour_identity` is proved for an arbitrary pair-free
prefix and suffix.  The full `PairFoundSuffixCancellation x` follows from
`hrev : PairFreeReversal x` plus the following Lean goal, and is
equivalent to it:

```
def LastPullCancellation (x : Card) : Prop :=
  ∀ {u v : State} {z : Card} {pre : List Move} {m : Move},
    u.WF →
    seatOf u x = some (Sum.inr z) →
    seatOf u x.twin = some (Sum.inr z.twin) →
    ShufflePlayW u (pre ++ [m]) v →
    IsPairFound x m →
    (∃ w, seatOf v x = some (Sum.inr w)) →
    (∃ w' : Card, seatOf v x.twin = some (Sum.inr w')) →
    PairFreeOrbit x v u ∨ PairFreeOrbit x v (u.spliceTwinRuns x)
```

By `last_pairFound_is_pull`, `m = Move.foundToTab y b` with
`y ∈ {x, x.twin}`, and `lastPull_base_eq_parent_or_twin` pins the pull
base to the original parent or its twin.  The missing geometric step is
the arbitrary-prefix raise/pull cancellation: commuting the letters of
`pre` past the excursion that raises `y` and pulls it back, using the
positive `TwinRaiseCommute` squares for disjoint slides/raises/empty-seat
pulls and isolating the moves that compete for the raised pile or the
pull target.  No counterexample was found.
-/
