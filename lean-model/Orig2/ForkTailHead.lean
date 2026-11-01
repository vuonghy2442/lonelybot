import Orig2.ForkLandResReduction
import Orig2.ForkMtnExists
import Orig2.ForkPinRight
import Orig2.ForkJoint
import Orig2.ForkWindow
import Orig2.ForkDirect

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-!
# Temp/TailHead — the pull-first cover clause (`JointKit.TailCoversHead`)

READ-ONLY scratch card (no source edits, no commit).  Zero `sorry`, zero
`Classical.choice`, zero `native_decide`; `#print axioms` battery at the tail.

## What this card does

`JointKit.TailCoversHead` (`Orig2/ForkJoint.lean:§7b`) demands the cover
`CoveredAt F c` only at **pull-first** splits (`pre = []`, or `pre` headed by a
non-free letter).  This card

1. **`tailCoversHead_iff_pullFirstBlock`** — proves the restricted clause is
   EXACTLY the block clause `¬ CanRaise F c` at pull-first splits (via
   `Mech.coverEvent_iff_block`'s dichotomy `canRaise_or_covered`).  So
   `TailCoversHead` is *not weaker in content* than `SplitBlock`; it only
   removes the free-headed `pre` (18/281 = 6.4% of the census splits,
   `Temp/Joint_Report.md`; 93.6% of splits are pull-first).  The exact residual
   is therefore named `PullFirstBlock` and every consumer is re-derived from it;
   `tailCoversHead_iff_split` splits it into the two disjoint lanes
   `TailCoversNilPre` (`pre = []`) and `TailCoversPullPre` (`pre` pull-headed);
2. **`pre_head_is_pull`** — a structural theorem: at a pull-first split the
   play's FIRST letter is a pull.  (A raise is impossible at the saturated
   origin `u`; the two waste letters are never reversible.)  So pull-first
   splits are exactly "the play begins with a pull";
3. **`pre_nil_live_subset` / `pre_nil_turn_dichotomy`** — at `pre = []` the
   bottom's whole S-live set is `{c, c.twin}` (`LandKit.canRaiseS_pull_creation`
   fired at the saturated origin), hence the raise card is `c` or `c.twin`;
4. **`sameCard_turn_has_cover`** — at ANY split with `d = c`, the free tail
   `post` must contain a slide LANDING ON `c`.  (Otherwise `post` is
   `ReadSafeNoSelfHead c`, `NoSelfKit.noSelfSlide_of_soft_window` removes every
   self-slide, `raise c` bubbles left to the pull, and the adjacent
   `pull c ; raise c` pair deletes — contradicting minimality.)  This is the
   brief's "a raise of `c` in a pull-free tail is an identity-pair partner",
   made precise;
5. **`covered_of_tail_draws_and_landing`** — a free tail consisting of draws
   plus ONE slide landing on `c` does cover `c` at the bottom (draws preserve
   piles).  Combined with **`canRaise_of_tail_draws_and_slide`** (a tail of
   draws plus one non-landing slide preserves the pull card's licence) this
   settles the whole `|slides(post)| ≤ 1` stratum (`atMostOneSlide_dichotomy`),
   and yields **`sameCard_turn_atLeastTwoSlides`**: a same-card turn forces the
   free tail to contain at least two slides — i.e. the cover must be created
   *and later undone* (`Mech.seat_eq_of_free_play_no_mover` is the frame fact
   that would close the "not undone" half, which the card does not attempt).

## What is NOT proved

`PullFirstBlock` itself (equivalently `TailCoversHead`).  The reduction is
exact, so the residual is the campaign's block clause on the 93.6% of census
splits the joint induction cannot shift; items 4/5 localise the remaining
difficulty to tails with **at least two slides** (where a cover slide can be
created and later undone).  The two lanes of `tailCoversHead_iff_split` carry
the two known obstruction shapes: the `pre = []` lane is where
`BottomNotBothRaisable`/`SplitNe` bites, the pull-headed lane is
`ForkPinRight`'s `PrePullPair`/`NoPrePullRaise` lane.
-/

namespace TailHead

open SplitKit

/-! ## §1. The exact residual: the block clause at pull-first splits -/

/-- **`PullFirstBlock`** — `SplitBlock`'s `¬ CanRaise F c` demanded only at
pull-first splits with a nonempty free tail (the exact content of
`TailCoversHead`, cf. `tailCoversHead_iff_pullFirstBlock`). -/
def PullFirstBlock : Prop :=
  ∀ (u v : State) (ρ : List Move) (F : State)
    (left right : List Move) (c d : Card) (b : Base)
    (pre post tail : List Move),
    SplitHyp u v ρ F left right c d b pre post tail →
    (pre = [] ∨ ∃ (m : Move) (pre2 : List Move), pre = m :: pre2 ∧
      ¬ ValleyElim.FreeMove m) →
    post ≠ [] → ¬ CanRaise F c

/-- The block at pull-first splits gives the cover there (`c` is S-live at the
bottom, `SplitKit.splitHyp_green`). -/
theorem tailCoversHead_of_pullFirstBlock (h : PullFirstBlock) : JointKit.TailCoversHead := by
  intro u v ρ F left right c d b pre post tail hsplit hfirst hpost
  obtain ⟨hF, hSc, -, -⟩ := splitHyp_green hsplit
  exact covered_of_live_not_canRaise hF hSc
    (h u v ρ F left right c d b pre post tail hsplit hfirst hpost)

/-- A cover at a pull-first split forbids the block there
(`not_canRaise_of_covered`). -/
theorem pullFirstBlock_of_tailCoversHead (h : JointKit.TailCoversHead) : PullFirstBlock := by
  intro u v ρ F left right c d b pre post tail hsplit hfirst hpost
  have hF : F.WF := (splitHyp_green hsplit).1
  exact not_canRaise_of_covered hF
    (h u v ρ F left right c d b pre post tail hsplit hfirst hpost)

/-- **THE RESTRICTED CLAUSE IS THE PULL-FIRST BLOCK.**  No content is lost:
the cover at a pull-first split is *equivalent* to the block there. -/
theorem tailCoversHead_iff_pullFirstBlock :
    JointKit.TailCoversHead ↔ PullFirstBlock :=
  ⟨pullFirstBlock_of_tailCoversHead, tailCoversHead_of_pullFirstBlock⟩

/-- `SplitBlock` restricts to `TailCoversHead` (sanity row: the residual is a
restriction of the campaign clause, not a new obligation). -/
theorem tailCoversHead_of_splitBlock (hb : SplitBlock) : JointKit.TailCoversHead :=
  JointKit.tailCoversHead_of_tailCovers (BlockKit.tailCovers_of_splitBlock hb)

/-! ## §2. Pull-first means the play starts with a pull -/

/-- **A NON-FREE FIRST LETTER OF A WITNESS PLAY FROM A SATURATED STATE IS A
PULL.**  The two waste letters are never reversible
(`wasteToFound_not_reversibleAtW`, `wasteToTab_not_reversibleAtW`); a raise
needs `CanRaise` at the origin, hence an S-live card there, which `SSaturated`
forbids. -/
theorem head_pull_of_saturated
    {u v : State} {m : Move} {rest : List Move}
    (huwf : u.WF) (hsat : SSaturated u)
    (hplay : ShufflePlayW u (m :: rest) v)
    (hnf : ¬ ValleyElim.FreeMove m) :
    ∃ (c : Card) (b : Base), m = Move.foundToTab c b := by
  cases hplay with
  | cons hrev hstep hrest =>
      cases m with
      | draw => exact absurd ValleyElim.free_draw hnf
      | tabToTab c b => exact absurd (ValleyElim.free_slide c b) hnf
      | wasteToFound c => exact absurd hrev (wasteToFound_not_reversibleAtW u c)
      | wasteToTab c b => exact absurd hrev (wasteToTab_not_reversibleAtW u c b)
      | tabToFound c =>
          exact absurd (CanRaiseS.now c (Bridge.canRaise_of_reversible_raise huwf hrev))
            (hsat c)
      | foundToTab c b => exact ⟨c, b, rfl⟩

/-- **AT A PULL-FIRST SPLIT WHOSE `pre` IS NONEMPTY, ITS HEAD IS A PULL.** -/
theorem pre_head_is_pull
    {u v : State} {ρ : List Move} {F : State} {left right : List Move}
    {c d : Card} {b : Base} {pre post tail : List Move}
    (h : SplitHyp u v ρ F left right c d b pre post tail)
    {m : Move} {pre2 : List Move} (hpre : pre = m :: pre2)
    (hnf : ¬ ValleyElim.FreeMove m) :
    ∃ (z : Card) (bz : Base), m = Move.foundToTab z bz := by
  obtain ⟨huwf, hsu, -, -, -, -, -, hleft, -, hshape, -, -⟩ := h
  have hshape' : left = m :: (pre2 ++ Move.foundToTab c b :: post) := by
    rw [hshape, hpre]
    rfl
  have hplayF : ShufflePlayW u (m :: (pre2 ++ Move.foundToTab c b :: post)) F := by
    rw [← hshape']
    exact hleft
  exact head_pull_of_saturated huwf hsu hplayF hnf

/-! ## §3. The pull landing of a split -/

/-- **THE PULL LANDING.**  A split exposes the state `A'` before its last pull
and the landing `B`; the landing is `WF` and the pulled card is raisable (even
vanilla) there. -/
theorem split_pull_landing
    {u v : State} {ρ : List Move} {F : State} {left right : List Move}
    {c d : Card} {b : Base} {pre post tail : List Move}
    (h : SplitHyp u v ρ F left right c d b pre post tail) :
    ∃ A' B : State,
      ShufflePlayW u pre A' ∧
      reversibleAtW A' (Move.foundToTab c b) ∧
      State.step A' (Move.foundToTab c b) = some B ∧
      ShufflePlayW B post F ∧
      A'.WF ∧ B.WF ∧ CanRaise B c ∧
      (∀ m ∈ post, ValleyElim.FreeMove m) := by
  obtain ⟨huwf, -, -, -, -, -, -, hleft, hright, hshape, hfree, hrightShape⟩ := h
  obtain ⟨A', hpre, hrest⟩ :=
    ValleyElim.ShufflePlayW_split hleft pre (Move.foundToTab c b :: post) hshape
  have hA' : A'.WF := SatDifferCensus.ShufflePlayW.wf_end hpre huwf
  cases hrest with
  | cons hrev hstep hpost =>
      exact ⟨A', _, hpre, hrev, hstep, hpost, hA', step_wf hA' hstep,
        ValleyStep.pull_card_canRaise hA' hstep, hfree⟩

/-! ## §4. At `pre = []` the bottom's live set is `{c, c.twin}` -/

/-- **THE BOTTOM'S LIVE SET AT A `pre = []` SPLIT.**  The origin is saturated,
so the pull creates S-liveness only for `c` and `c.twin`
(`LandKit.canRaiseS_pull_creation`), and the free tail transports the live set
(`Bridge.canRaiseS_of_free_play_iff`). -/
theorem pre_nil_live_subset
    {u v : State} {ρ : List Move} {F : State} {left right : List Move}
    {c d : Card} {b : Base} {post tail : List Move}
    (h : SplitHyp u v ρ F left right c d b [] post tail)
    {e : Card} (he : CanRaiseS F e) :
    e = c ∨ e = c.twin := by
  obtain ⟨A', B, hpre, hrev, hstep, hpost, hA', hB, hcanB, -⟩ :=
    split_pull_landing h
  obtain ⟨huwf, hsu, -, -, -, -, -, hleft, -, hshape, hfree, -⟩ := h
  have hA'u : A' = u := by
    cases hpre with
    | nil => rfl
  subst hA'u
  have heB : CanRaiseS B e :=
    (Bridge.canRaiseS_of_free_play_iff hpost hfree hB e).mpr he
  rcases LandKit.canRaiseS_pull_creation hA' hstep heB with h1 | h1 | h1
  · exact Or.inl h1
  · exact Or.inr h1
  · exact absurd h1 (hsu e)

/-- **THE RAISE CARD AT A `pre = []` SPLIT IS `c` OR `c.twin`.** -/
theorem pre_nil_turn_dichotomy
    {u v : State} {ρ : List Move} {F : State} {left right : List Move}
    {c d : Card} {b : Base} {post tail : List Move}
    (h : SplitHyp u v ρ F left right c d b [] post tail) :
    d = c ∨ d = c.twin := by
  obtain ⟨-, -, hcanD, -⟩ := splitHyp_green h
  exact pre_nil_live_subset h (CanRaiseS.now d hcanD)

/-! ## §5. A same-card turn forces a cover slide in the free tail -/

/-- **`isCoverB c`** — computable "this letter is a slide landing ON `c`". -/
def isCoverB (c : Card) : Move → Bool
  | Move.tabToTab _ b => decide (b = Sum.inr c)
  | _ => false

theorem isCoverB_eq_true_iff {c : Card} {m : Move} :
    isCoverB c m = true ↔ ∃ (x : Card), m = Move.tabToTab x (Sum.inr c) := by
  cases m with
  | draw => simp [isCoverB]
  | wasteToFound x => simp [isCoverB]
  | wasteToTab x b => simp [isCoverB]
  | tabToFound x => simp [isCoverB]
  | foundToTab x b => simp [isCoverB]
  | tabToTab y b =>
      show decide (b = Sum.inr c) = true ↔ ∃ x, Move.tabToTab y b =
        Move.tabToTab x (Sum.inr c)
      constructor
      · intro hb
        exact ⟨y, by rw [of_decide_eq_true hb]⟩
      · rintro ⟨x, hx⟩
        cases hx
        exact decide_eq_true rfl

/-- Pointwise-false letters make a computable scan false. -/
theorem any_eq_false_of_forall {p : Move → Bool} :
    ∀ {l : List Move}, (∀ m ∈ l, p m = false) → l.any p = false
  | [], _ => rfl
  | a :: t, h => by
      have ha : p a = false := h a (List.mem_cons_self ..)
      have ht : (t.any p) = false :=
        any_eq_false_of_forall (fun m hm => h m (List.mem_cons_of_mem a hm))
      rw [List.any_cons, ha]
      exact ht

/-- **A SAME-CARD TURN NEEDS A COVER SLIDE.**  If the split's raise card is its
pull card (`d = c`), then the free tail `post` contains a slide landing on `c`.

Proof by contradiction: if not, every letter of `post` is
`ReadSafeNoSelfHead c` (a free letter is a draw or a slide, and no slide lands
on `c`), so `NoSelfKit.noSelfSlide_of_soft_window` removes every self-slide of
`c`; the window is then `ReadSafe c` and `raise c` bubbles left to the pull
(`NonforkKit.raise_bubble`); the adjacent `pull c ; raise c` pair deletes
(`ValleyStep.valley_cancel_same`), giving a strictly shorter play — against
minimality. -/
theorem sameCard_turn_has_cover
    {u v : State} {ρ : List Move} {F : State} {left right : List Move}
    {c d : Card} {b : Base} {pre post tail : List Move}
    (h : SplitHyp u v ρ F left right c d b pre post tail) (hdc : d = c) :
    post.any (isCoverB c) = true := by
  have hwhole := h
  by_cases hany : post.any (isCoverB c) = true
  · exact hany
  · exfalso
    obtain ⟨A', B, hpre, hrevP, hstepP, hpost, hA', hB, hcanB, -⟩ :=
      split_pull_landing h
    obtain ⟨huwf, -, hsv, hplay, hsplitAt, hmin, hρ, hleft, hright, hshape,
      hfree, hrightShape⟩ := h
    have hright' : ShufflePlayW F (Move.tabToFound c :: tail) v := by
      have hh := hright
      rw [hrightShape, hdc] at hh
      exact hh
    have hplayB : ShufflePlayW B (post ++ Move.tabToFound c :: tail) v :=
      ShufflePlayW_append hpost hright'
    -- the segment from `B` on is shortest between its own endpoints
    have hρeq : ρ = (pre ++ [Move.foundToTab c b]) ++
        (post ++ Move.tabToFound c :: tail) ++ [] := by
      rw [hρ, hshape, hrightShape, hdc]
      simp only [List.append_assoc, List.cons_append, List.singleton_append,
        List.nil_append, List.append_nil]
    have hα : ShufflePlayW u (pre ++ [Move.foundToTab c b]) B :=
      ShufflePlayW_append hpre (Walk.cons hrevP hstepP (Walk.nil B))
    have hminseg : ∀ seg' : List Move, ShufflePlayW B seg' v →
        (post ++ Move.tabToFound c :: tail).length ≤ seg'.length :=
      JointKit.segment_shortest hplay hρeq hmin hα hplayB
    -- the free tail never lands on `c`, hence is soft for `c`
    have hfalse : post.any (isCoverB c) = false := by
      cases hv : post.any (isCoverB c) with
      | false => rfl
      | true => exact absurd hv hany
    have hno : ∀ m ∈ post, isCoverB c m = false := ValleyElim.any_eq_false hfalse
    have hsoft : ∀ q ∈ post, SlideFwd.ReadSafeNoSelfHead c q := by
      intro q hq
      rcases hfree q hq with rfl | ⟨x, bb, rfl⟩
      · exact trivial
      · intro hb
        have htrue : isCoverB c (Move.tabToTab x bb) = true := by
          show decide (bb = Sum.inr c) = true
          rw [hb]
          exact decide_eq_true rfl
        rw [hno _ hq] at htrue
        exact Bool.false_ne_true htrue
    have hS : SlideFwd.NoSlideOf c post :=
      NoSelfKit.noSelfSlide_of_soft_window hB hcanB hplayB hsoft hminseg
    have hread : ∀ q ∈ post, SlideFwd.ReadSafe c q := by
      intro q hq
      exact SlideFwd.readSafe_of_noSelfHead (hsoft q hq)
        (by
          intro w bb hqeq
          subst hqeq
          exact hS w bb hq)
    have hsw : NonforkKit.RaiseSwaps B c post :=
      SlideFwd.raiseSwaps_of_readSafe hB hplayB hcanB hread
    have hbubble : ShufflePlayW B (Move.tabToFound c :: post ++ tail) v :=
      NonforkKit.raise_bubble post hplayB hsw
    have hnew : ShufflePlayW u (pre ++ (post ++ tail)) v :=
      ValleyStep.valley_cancel_same huwf hpre hstepP hbubble
    have hlen : (pre ++ (post ++ tail)).length < ρ.length := by
      rw [JointKit.splitHyp_length_eq hwhole]
      simp only [List.length_append]
      omega
    exact absurd (hmin _ hnew) (Nat.not_le.mpr hlen)

/-! ## §6. The `|slides(post)| ≤ 1` stratum is settled -/

/-- A draw-only witness leg preserves the vanilla licence (draws preserve
`found` and `piles`, and `CanRaise` is a `found`+`piles` read). -/
theorem canRaise_of_draw_play {Q W : State} {c : Card} {τ : List Move}
    (hplay : ShufflePlayW Q τ W) (hdraw : ∀ m ∈ τ, m = Move.draw)
    (h : CanRaise Q c) : CanRaise W c := by
  obtain ⟨hf, hp⟩ := SplitKit.drawPlay_found_piles hplay hdraw
  exact (SplitKit.canRaise_congr_found_piles hf.symm hp.symm c).mp h

/-- **A COVER SLIDE AT THE END OF A DRAW-FREE SUFFIX PERSISTS.**  If the free
tail is draws, then one slide landing on `c`, then draws again, the mover stays
on `c` down to the bottom (draws preserve `piles`). -/
theorem covered_of_tail_draws_and_landing
    {u v : State} {ρ : List Move} {F : State} {left right : List Move}
    {c d : Card} {b : Base} {pre post tail : List Move}
    (h : SplitHyp u v ρ F left right c d b pre post tail)
    {s1 s2 : List Move} {x : Card}
    (hpost : post = s1 ++ Move.tabToTab x (Sum.inr c) :: s2)
    (h1 : ∀ m ∈ s1, m = Move.draw) (h2 : ∀ m ∈ s2, m = Move.draw) :
    CoveredAt F c := by
  obtain ⟨A', B, hpre, hrev, hstep, hpostplay, hA', hB, hcanB, -⟩ :=
    split_pull_landing h
  rw [hpost] at hpostplay
  obtain ⟨Mid, hs1, hrest⟩ :=
    ValleyElim.ShufflePlayW_split hpostplay s1
      (Move.tabToTab x (Sum.inr c) :: s2) rfl
  have hMid : Mid.WF := SatDifferCensus.ShufflePlayW.wf_end hs1 hB
  cases hrest with
  | cons hrevS hstepS hplay2 =>
      rename_i Z
      have hseat : seatOf Z x = some (Sum.inr c) := by
        rw [tfc_seat_point_edit hMid hstepS hrevS x, ite_eq_left rfl]
      obtain ⟨-, hpiles⟩ := SplitKit.drawPlay_found_piles hplay2 h2
      exact ⟨x, by rw [seatOf_congr_piles hpiles x]; exact hseat⟩

/-- **A DRAW-ONLY TAIL PLUS ONE NON-LANDING SLIDE KEEPS `c` RAISABLE.**  Draws
preserve `CanRaise`; a slide that neither moves `c` nor lands on it preserves
it too (`R12.canRaise_survives_slide`), and a self-slide of `c` as well
(`EmptyTail.canRaise_survives_own_slide`). -/
theorem canRaise_of_tail_draws_and_slide
    {u v : State} {ρ : List Move} {F : State} {left right : List Move}
    {c d : Card} {b : Base} {pre post tail : List Move}
    (h : SplitHyp u v ρ F left right c d b pre post tail)
    {s1 s2 : List Move} {x : Card} {bb : Base}
    (hpost : post = s1 ++ Move.tabToTab x bb :: s2)
    (h1 : ∀ m ∈ s1, m = Move.draw) (h2 : ∀ m ∈ s2, m = Move.draw)
    (hbb : bb ≠ Sum.inr c) :
    CanRaise F c := by
  obtain ⟨A', B, hpre, hrev, hstep, hpostplay, hA', hB, hcanB, -⟩ :=
    split_pull_landing h
  rw [hpost] at hpostplay
  -- the draws before the slide
  obtain ⟨Mid, hs1, hrest⟩ :=
    ValleyElim.ShufflePlayW_split hpostplay s1
      (Move.tabToTab x bb :: s2) rfl
  have hMid : Mid.WF := SatDifferCensus.ShufflePlayW.wf_end hs1 hB
  have hcanMid : CanRaise Mid c := canRaise_of_draw_play hs1 h1 hcanB
  cases hrest with
  | cons hrevS hstepS hplay2 =>
      rename_i Z
      have hcanZ : CanRaise Z c := by
        by_cases hxc : x = c
        · subst hxc
          exact EmptyTail.canRaise_survives_own_slide hMid hstepS hrevS hcanMid
        · exact R12.canRaise_survives_slide hMid hstepS hrevS hxc hbb hcanMid
      exact canRaise_of_draw_play hplay2 h2 hcanZ

/-- **THE `|slides(post)| ≤ 1` DICHOTOMY.**  If the free tail is draws plus at
most one slide, then either that slide lands on `c` (and `c` is covered at the
bottom) or it does not (and `c` is still raisable there). -/
theorem atMostOneSlide_dichotomy
    {u v : State} {ρ : List Move} {F : State} {left right : List Move}
    {c d : Card} {b : Base} {pre post tail : List Move}
    (h : SplitHyp u v ρ F left right c d b pre post tail)
    {s1 s2 : List Move} {x : Card} {bb : Base}
    (hpost : post = s1 ++ Move.tabToTab x bb :: s2)
    (h1 : ∀ m ∈ s1, m = Move.draw) (h2 : ∀ m ∈ s2, m = Move.draw) :
    (bb = Sum.inr c ∧ CoveredAt F c) ∨ (bb ≠ Sum.inr c ∧ CanRaise F c) := by
  by_cases hbb : bb = Sum.inr c
  · refine Or.inl ⟨hbb, ?_⟩
    exact covered_of_tail_draws_and_landing h (by rw [hpost, hbb]) h1 h2
  · exact Or.inr ⟨hbb, canRaise_of_tail_draws_and_slide h hpost h1 h2 hbb⟩

/-- **`AtMostOneSlide post`** — the free tail is all draws, or draws with
exactly one slide in the middle.  (This is the stratum the card settles.) -/
def AtMostOneSlide (post : List Move) : Prop :=
  (∀ m ∈ post, m = Move.draw) ∨
    ∃ (s1 s2 : List Move) (x : Card) (bb : Base),
      post = s1 ++ Move.tabToTab x bb :: s2 ∧
      (∀ m ∈ s1, m = Move.draw) ∧ (∀ m ∈ s2, m = Move.draw)

/-- **A SAME-CARD TURN FORCES AT LEAST TWO SLIDES.**  At a split with `d = c`
the free tail is NOT "at most one slide": `sameCard_turn_has_cover` forces a
slide landing on `c`, and the `|slides| ≤ 1` shapes either exclude such a slide
(the all-draw tail) or would cover `c` (the single-slide tail, by
`covered_of_tail_draws_and_landing`), contradicting the raisability of `c` at
the bottom. -/
theorem sameCard_turn_atLeastTwoSlides
    {u v : State} {ρ : List Move} {F : State} {left right : List Move}
    {c d : Card} {b : Base} {pre post tail : List Move}
    (h : SplitHyp u v ρ F left right c d b pre post tail) (hdc : d = c)
    (hpost : AtMostOneSlide post) :
    False := by
  obtain ⟨-, -, hcanD, -⟩ := splitHyp_green h
  have hcanF : CanRaise F c := by rw [← hdc]; exact hcanD
  have hF : F.WF := (splitHyp_green h).1
  rcases hpost with hall | ⟨s1, s2, x, bb, hpost, h1, h2⟩
  · obtain ⟨α, m, β, heq, -, hm⟩ :=
      ValleyElim.exists_first_bool (isCoverB c) post (sameCard_turn_has_cover h hdc)
    obtain ⟨y, hy⟩ := isCoverB_eq_true_iff.mp hm
    have hdraw : m = Move.draw :=
      hall m (by rw [heq]; exact List.mem_append_right _ (List.mem_cons_self ..))
    rw [hy] at hdraw
    exact Move.noConfusion hdraw
  · rcases atMostOneSlide_dichotomy h hpost h1 h2 with ⟨hbb, hcov⟩ | ⟨hbb, -⟩
    · exact not_canRaise_of_covered hF hcov hcanF
    · have hnoany : post.any (isCoverB c) = false := by
        refine any_eq_false_of_forall ?_
        intro m hm
        rw [hpost] at hm
        rcases List.mem_append.mp hm with hm1 | hm2
        · rw [h1 m hm1]
          rfl
        · rcases List.mem_cons.mp hm2 with rfl | hm3
          · show decide (bb = Sum.inr c) = false
            rw [decide_eq_false_iff_not]
            exact hbb
          · rw [h2 m hm3]
            rfl
      rw [sameCard_turn_has_cover h hdc] at hnoany
      exact Bool.noConfusion hnoany

/-! ## §7. The residual, and the campaign chain through it -/

/-! ### §7a. The residual splits into two DISJOINT lanes -/

/-- **`TailCoversNilPre`** — the cover demand at the `pre = []` splits, where
the origin is saturated and (by §4) the bottom's live set is `{c, c.twin}`.
This is the free-prefix-like lane (the pull is the play's first letter). -/
def TailCoversNilPre : Prop :=
  ∀ (u v : State) (ρ : List Move) (F : State)
    (left right : List Move) (c d : Card) (b : Base)
    (post tail : List Move),
    SplitHyp u v ρ F left right c d b [] post tail →
    post ≠ [] → CoveredAt F c

/-- **`TailCoversPullPre`** — the cover demand at the splits whose `pre` is
nonempty and headed by a non-free letter.  By §2 that head is a PULL, so this
is the "`pre` contains pulls" lane (the live set at the bottom may carry the
twins of the cards pulled in `pre`: `ForkPinRight`'s `PrePullPair` lane). -/
def TailCoversPullPre : Prop :=
  ∀ (u v : State) (ρ : List Move) (F : State)
    (left right : List Move) (c d : Card) (b : Base)
    (pre post tail : List Move),
    SplitHyp u v ρ F left right c d b pre post tail →
    (∃ (m : Move) (pre2 : List Move), pre = m :: pre2 ∧
      ¬ ValleyElim.FreeMove m) →
    post ≠ [] → CoveredAt F c

/-- **THE RESIDUAL IS THE CONJUNCTION OF ITS TWO LANES.** -/
theorem tailCoversHead_iff_split :
    JointKit.TailCoversHead ↔ TailCoversNilPre ∧ TailCoversPullPre := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro u v ρ F left right c d b post tail hh hpost
      exact h u v ρ F left right c d b [] post tail hh (Or.inl rfl) hpost
    · intro u v ρ F left right c d b pre post tail hh hfirst hpost
      exact h u v ρ F left right c d b pre post tail hh (Or.inr hfirst) hpost
  · rintro ⟨h0, h1⟩ u v ρ F left right c d b pre post tail hh hfirst hpost
    rcases hfirst with rfl | hfirst
    · exact h0 u v ρ F left right c d b post tail hh hpost
    · exact h1 u v ρ F left right c d b pre post tail hh hfirst hpost

/-- The same decomposition at the block level. -/
theorem pullFirstBlock_iff_split :
    PullFirstBlock ↔
      (∀ (u v : State) (ρ : List Move) (F : State)
        (left right : List Move) (c d : Card) (b : Base)
        (post tail : List Move),
        SplitHyp u v ρ F left right c d b [] post tail →
        post ≠ [] → ¬ CanRaise F c) ∧
      (∀ (u v : State) (ρ : List Move) (F : State)
        (left right : List Move) (c d : Card) (b : Base)
        (pre post tail : List Move),
        SplitHyp u v ρ F left right c d b pre post tail →
        (∃ (m : Move) (pre2 : List Move), pre = m :: pre2 ∧
          ¬ ValleyElim.FreeMove m) →
        post ≠ [] → ¬ CanRaise F c) := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro u v ρ F left right c d b post tail hh hpost
      exact h u v ρ F left right c d b [] post tail hh (Or.inl rfl) hpost
    · intro u v ρ F left right c d b pre post tail hh hfirst hpost
      exact h u v ρ F left right c d b pre post tail hh (Or.inr hfirst) hpost
  · rintro ⟨h0, h1⟩ u v ρ F left right c d b pre post tail hh hfirst hpost
    rcases hfirst with rfl | hfirst
    · exact h0 u v ρ F left right c d b post tail hh hpost
    · exact h1 u v ρ F left right c d b pre post tail hh hfirst hpost

/-! ### §7b. The `pre = []` lane, read without the cover vocabulary -/

/-- At a `pre = []` split the block and the cover are literally the same
statement (the pull card is S-live at the bottom, §1/`splitHyp_green`). -/
theorem pre_nil_block_iff_covered
    {u v : State} {ρ : List Move} {F : State} {left right : List Move}
    {c d : Card} {b : Base} {post tail : List Move}
    (h : SplitHyp u v ρ F left right c d b [] post tail) :
    ¬ CanRaise F c ↔ CoveredAt F c := by
  obtain ⟨hF, hSc, -, -⟩ := splitHyp_green h
  exact ⟨covered_of_live_not_canRaise hF hSc, not_canRaise_of_covered hF⟩

/-- **AT `pre = []` THE TAIL EITHER CARRIES A COVER SLIDE OR THE RAISE CARD IS
THE TWIN.**  This is the sharp form of §4 + §5 in the nil-`pre` lane: the only
way a same-card turn avoids a landing slide is impossible, so a tail with no
landing slide forces `d = c.twin` (the campaign's mechanism). -/
theorem pre_nil_cover_slide_or_twin
    {u v : State} {ρ : List Move} {F : State} {left right : List Move}
    {c d : Card} {b : Base} {post tail : List Move}
    (h : SplitHyp u v ρ F left right c d b [] post tail) :
    post.any (isCoverB c) = true ∨ d = c.twin := by
  rcases pre_nil_turn_dichotomy h with hdc | hdt
  · exact Or.inl (sameCard_turn_has_cover h hdc)
  · exact Or.inr hdt

/-- **THE PLAY OF A PULL-FIRST SPLIT BEGINS WITH A PULL.**  (`pre = []` makes
the split's own pull the first letter; a nonempty non-free head is itself a
pull, §2.) -/
theorem pullFirst_first_letter
    {u v : State} {ρ : List Move} {F : State} {left right : List Move}
    {c d : Card} {b : Base} {pre post tail : List Move}
    (h : SplitHyp u v ρ F left right c d b pre post tail)
    (hfirst : pre = [] ∨ ∃ (m : Move) (pre2 : List Move), pre = m :: pre2 ∧
      ¬ ValleyElim.FreeMove m) :
    ∃ (z : Card) (bz : Base) (rest : List Move),
      ρ = Move.foundToTab z bz :: rest := by
  have hwhole := h
  obtain ⟨-, -, -, -, -, -, hρ, hleft, -, hshape, -, hrightShape⟩ := h
  rcases hfirst with rfl | ⟨m, pre2, hpre, hnf⟩
  · refine ⟨c, b, post ++ right, ?_⟩
    rw [hρ, hshape, hrightShape]
    rfl
  · obtain ⟨z, bz, hm⟩ := pre_head_is_pull hwhole hpre hnf
    refine ⟨z, bz, (pre2 ++ Move.foundToTab c b :: post) ++ right, ?_⟩
    rw [hρ, hshape, hpre, hm]
    rfl

/-! ### §7c. The residual, named -/

/-- **THE EXACT RESIDUAL** — re-exported under its own name: the block clause
at pull-first splits with a nonempty free tail. -/
def PullFirstTailResidual : Prop := PullFirstBlock

theorem pullFirstTailResidual_iff_head :
    PullFirstTailResidual ↔ JointKit.TailCoversHead :=
  ⟨tailCoversHead_of_pullFirstBlock, pullFirstBlock_of_tailCoversHead⟩

/-- The campaign's cover half, through the residual. -/
theorem tailCovers_of_pullFirstBlock
    (hl : SplitLivePair)
    (hms : ∀ (u v : State) (ρ : List Move) (F : State)
      (left right : List Move) (c d : Card) (b : Base)
      (pre post tail : List Move),
      SplitHyp u v ρ F left right c d b pre post tail →
      MountainKit.MountainSplit left right)
    (h : PullFirstBlock) : BlockKit.TailCovers :=
  JointKit.tailCovers_of_head_cover hl hms (tailCoversHead_of_pullFirstBlock h)

/-- `SplitBlock` from the residual (the joint induction consumes the
free-headed `pre`). -/
theorem splitBlock_of_pullFirstBlock
    (hl : SplitLivePair)
    (hms : ∀ (u v : State) (ρ : List Move) (F : State)
      (left right : List Move) (c d : Card) (b : Base)
      (pre post tail : List Move),
      SplitHyp u v ρ F left right c d b pre post tail →
      MountainKit.MountainSplit left right)
    (h : PullFirstBlock) : SplitBlock :=
  JointKit.splitBlock_of_head_cover hl hms (tailCoversHead_of_pullFirstBlock h)

/-- The campaign, with the cover half carried by the pull-first block. -/
theorem satDifferForkWF_of_pullFirstBlock
    (hl : SplitLivePair)
    (hms : ∀ (u v : State) (ρ : List Move) (F : State)
      (left right : List Move) (c d : Card) (b : Base)
      (pre post tail : List Move),
      SplitHyp u v ρ F left right c d b pre post tail →
      MountainKit.MountainSplit left right)
    (h : PullFirstBlock) (hmin : ValleyElim.ShortestPlayExists) :
    SatDifferForkWF :=
  JointKit.satDifferForkWF_of_head_cover hl hms
    (tailCoversHead_of_pullFirstBlock h) hmin

end TailHead

/-! ## §8. Battery -/

#print axioms TailHead.tailCoversHead_of_pullFirstBlock
#print axioms TailHead.pullFirstBlock_of_tailCoversHead
#print axioms TailHead.tailCoversHead_iff_pullFirstBlock
#print axioms TailHead.tailCoversHead_of_splitBlock
#print axioms TailHead.head_pull_of_saturated
#print axioms TailHead.pre_head_is_pull
#print axioms TailHead.split_pull_landing
#print axioms TailHead.pre_nil_live_subset
#print axioms TailHead.pre_nil_turn_dichotomy
#print axioms TailHead.isCoverB_eq_true_iff
#print axioms TailHead.any_eq_false_of_forall
#print axioms TailHead.sameCard_turn_has_cover
#print axioms TailHead.covered_of_tail_draws_and_landing
#print axioms TailHead.canRaise_of_tail_draws_and_slide
#print axioms TailHead.atMostOneSlide_dichotomy
#print axioms TailHead.sameCard_turn_atLeastTwoSlides
#print axioms TailHead.tailCoversHead_iff_split
#print axioms TailHead.pullFirstBlock_iff_split
#print axioms TailHead.pre_nil_block_iff_covered
#print axioms TailHead.pre_nil_cover_slide_or_twin
#print axioms TailHead.pullFirst_first_letter
#print axioms TailHead.pullFirstTailResidual_iff_head
#print axioms TailHead.tailCovers_of_pullFirstBlock
#print axioms TailHead.splitBlock_of_pullFirstBlock
#print axioms TailHead.satDifferForkWF_of_pullFirstBlock
