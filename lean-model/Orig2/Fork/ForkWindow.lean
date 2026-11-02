import Orig2.Fork.ForkSlideFwd
import Orig2.Fork.ForkSurvivor

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-!
# Orig2/ForkWindow — the READ-SAFE window of an empty-tail split, and its exact gap

READ-ONLY scratch (no source edits, no commit).  Zero `sorry`, zero
`Classical.choice`, no `native_decide`; battery at the tail.

## What this file does

The task's target is the INPUT side of the block lane: at an empty-tail split
(`post = []`) the window of letters from the landing `F` of the split's own
pull up to the tail's `raise c` should be *read-safe* for `c`, so that
`R12.raiseSwaps_of_read` / `SlideFwd.raiseSwaps_of_readSafe` can turn it into
the bubble certificate `RaiseSwaps`.

`Temp/SlideFwd_Core.lean` and `Temp/SlideFwd_Chain.lean` had already reduced
the geometric question to ONE clause: **no slide headed by `c` before the
raise**.  This file proves everything else, and leaves that clause as the
named residual `NoSelfSlide` (a `def`, never an `axiom`).

## Proved here (no residual)

1. **§1 — the rung kit.**  `rungAt` never rises on a pull-free play
   (`MountainKit.rungAt_le_of_no_pull`, restated locally) and never changes on
   a letter that is neither a pull nor a raise in `c`'s suit
   (`rung_step_of_not_pull_not_raise`).  Consequently, on a pull-free play
   starting and ending with `c` next-up, **no letter is a raise in `c`'s
   suit** (`no_raise_same_suit_of_pull_free`).  This is the "a raise in `c`'s
   suit must be `raise c` itself, and `raise c` is unique" argument: after
   `raise c` the rung of `c`'s suit is strictly above `c`'s rank index, and a
   pull-free play never lowers a rung, so `c` can never be next-up again.

2. **§2 — no slide lands on `c`.**  In the empty-tail twin regime `c.twin` is
   raised at the head of the right leg and the rest of the leg is pull-free, so
   `c.twin` stays in the foundation; a reversible slide landing on `c` would
   need its mover seated on `c.twin` (`Mech.mover_seat_twin_of_slide_into_card`)
   and a foundational card lies on no pile (`mem_found_unique`)
   (`no_slide_onto_of_twin_found`).

3. **§3 — `CanRaise c` at every prefix.**  Each window letter either preserves
   `CanRaise c` read-safely (`R12.canRaise_survives_*`) or is a slide headed by
   `c`, which preserves it by `EmptyTail.canRaise_survives_own_slide`.  Hence
   `canRaise_prefix_of_window` and the task's companion
   `canRaise_along_emptyTail_window`.

4. **§4 — `emptyTail_raiseSafe`:** at an empty-tail split, every letter of the
   window `raise d :: γ` is `ReadSafeLoose c` — `ReadSafe` with the
   "not headed by `c`" clause dropped.  Everything except the self-slide clause
   is therefore a theorem.

5. **§5 — the task's `emptyTail_window_readOK`,** with the honest hypotheses:
   the split, `post = []`, `MountainSplit`, the twin identity of the split's
   raise card, the decomposition `tail = γ ++ raise c :: β`, and the remaining
   geometric clause `NoSelfSlide` (no `tabToTab c _` in `γ`).  Conclusion:
   `∀ q ∈ raise d :: γ, R12.ReadOK c q`.

6. **§6 — the payoff chain:** `NoSelfSlide ⇒ SlideFwd.EmptyTailReadWindow ⇒
   NoEmptyTail ⇒ SplitBlock ⇒ SatDifferForkWF`, plus the restricted
   `KeepsForward` form (`keepsForward_emptyTailWindow`) and the bubble
   (`emptyTail_bubble`).

## The composed residual

`NoSelfSlide`: at an empty-tail split there is an occurrence of `raise c` in
the pull-free tail whose preceding window contains no slide headed by `c`.
That is the exact datum consumed by `emptyTail_window_auto`; it is the
input-side counterpart of the state-level slide datum, and it is NOT derivable
from `SplitHyp + MountainSplit + SplitLivePair` by the arguments above
(they prove the other three `ReadSafe` clauses).  The report cites the census
run on it.
-/

namespace Window

open NonforkKit
open SplitKit

/-! ## §1. The rung kit — what a pull-free play does to `nextUp` -/

/-- If `c` and `w` are both next-up and in the same suit, they are the same
card.  (A suit's foundation height is the rank index, so equal heights give
equal ranks.) -/
theorem card_eq_of_nextUp {st : State} {c w : Card}
    (hc : st.nextUp c = true) (hw : st.nextUp w = true) (hsu : w.suit = c.suit) :
    w = c := by
  have h1 : w.rank.toIdx = rungAt st w.suit := by
    simpa [rungAt, State.nextUp, State.foundHeight] using of_decide_eq_true hw
  have h2 : c.rank.toIdx = rungAt st c.suit := by
    simpa [rungAt, State.nextUp, State.foundHeight] using of_decide_eq_true hc
  have hr : w.rank = c.rank := by
    apply Rank.toIdx_inj
    rw [h1, h2, hsu]
  cases w with
  | mk ws wr =>
      cases c with
      | mk cs cr => simp_all

/-- **A LETTER THAT IS NEITHER A PULL NOR A RAISE IN `c`'s SUIT DOES NOT MOVE
`c`'s RUNG.**  Draws and slides fix the foundations; a raise of another suit
fixes `c`'s suit. -/
theorem rung_step_of_not_pull_not_raise {st s' : State} {q : Move} {c : Card}
    (hrev : reversibleAtW st q) (hstep : State.step st q = some s')
    (hnp : ¬ Bubble.IsPull q)
    (hnr : ∀ w : Card, q = Move.tabToFound w → w.suit ≠ c.suit) :
    rungAt s' c.suit = rungAt st c.suit := by
  cases q with
  | draw => exact rungAt_draw hstep c.suit
  | wasteToFound x => exact absurd hrev (wasteToFound_not_reversibleAtW st x)
  | wasteToTab x bb => exact absurd hrev (wasteToTab_not_reversibleAtW st x bb)
  | tabToFound w =>
      rw [rungAt_tabToFound hstep c.suit,
        ite_eq_right (fun h : c.suit = w.suit => hnr w rfl h.symm)]
  | foundToTab x bb => exact absurd ⟨x, bb, rfl⟩ hnp
  | tabToTab x bb => exact rungAt_tabToTab hstep c.suit

/-- **NO RAISE IN `c`'s SUIT BEFORE A LATER NEXT-UP `c`, ON A PULL-FREE PLAY.**

If `c` is next-up at the start and again at the end of a pull-free play, then
no letter of the play is a raise in `c`'s suit.  Proof: such a letter at a
state where `c` is next-up would be `raise c` itself; after `raise c` the rung
of `c`'s suit is `c.rank.toIdx + 1`, and the rest of the play (pull-free)
cannot lower it, so `c` could not be next-up at the end. -/
theorem no_raise_same_suit_of_pull_free
    {G Q : State} {g : List Move} {c : Card}
    (hplay : ShufflePlayW G g Q)
    (hnopull : ∀ m ∈ g, ¬ Bubble.IsPull m)
    (hG : G.nextUp c = true) (hQ : Q.nextUp c = true) :
    ∀ m ∈ g, ∀ w : Card, m = Move.tabToFound w → w.suit ≠ c.suit := by
  induction hplay with
  | nil st =>
      intro m hm
      exact absurd hm List.not_mem_nil
  | @cons st s₁ W m g' hrev hstep hrest ih =>
      have hnopull_m : ¬ Bubble.IsPull m := hnopull m (List.mem_cons_self ..)
      have hnopull' : ∀ m' ∈ g', ¬ Bubble.IsPull m' :=
        fun m' hm' => hnopull m' (List.mem_cons_of_mem m hm')
      -- if the head avoids `c`'s suit, `s₁` is still next-up
      have finish : (∀ w : Card, m = Move.tabToFound w → w.suit ≠ c.suit) →
          (∀ m' ∈ m :: g', ∀ w : Card, m' = Move.tabToFound w → w.suit ≠ c.suit) := by
        intro hgood m' hm' w hw
        rcases List.mem_cons.mp hm' with rfl | hm''
        · exact hgood w hw
        · have hs₁next : s₁.nextUp c = true := by
            have hrung : rungAt s₁ c.suit = rungAt st c.suit :=
              rung_step_of_not_pull_not_raise hrev hstep hnopull_m hgood
            have hl : (s₁.found c.suit).length = (st.found c.suit).length := by
              simpa [rungAt] using hrung
            unfold State.nextUp State.foundHeight
            rw [hl]
            exact hG
          exact ih hnopull' hs₁next hQ m' hm'' w hw
      cases m with
      | draw => exact finish (fun w hw => by cases hw)
      | wasteToFound x => exact absurd hrev (wasteToFound_not_reversibleAtW st x)
      | wasteToTab x bb => exact absurd hrev (wasteToTab_not_reversibleAtW st x bb)
      | foundToTab x bb => exact absurd ⟨x, bb, rfl⟩ hnopull_m
      | tabToTab x bb => exact finish (fun w hw => by cases hw)
      | tabToFound w =>
          by_cases hsu : w.suit = c.suit
          · exfalso
            have hwnext : st.nextUp w = true := (step_tabToFound_inv hstep).1
            have hweq : w = c := card_eq_of_nextUp hG hwnext hsu
            rw [hweq] at hstep
            have hidx : c.rank.toIdx = rungAt st c.suit := by
              simpa [rungAt, State.nextUp, State.foundHeight] using of_decide_eq_true hG
            have hs₁ : rungAt s₁ c.suit = rungAt st c.suit + 1 := by
              rw [rungAt_tabToFound hstep c.suit, ite_eq_left rfl]
            have hle : rungAt s₁ c.suit ≤ rungAt W c.suit :=
              MountainKit.rungAt_le_of_no_pull hrest hnopull'
            have hidxW : c.rank.toIdx = rungAt W c.suit := by
              simpa [rungAt, State.nextUp, State.foundHeight] using of_decide_eq_true hQ
            omega
          · exact finish (fun w' hw' => by
              injection hw' with hww
              rw [← hww]
              exact hsu)

/-! ## §2. No slide lands on `c` in the twin regime -/

/-- **A SLIDE LANDING ON `c` IS IMPOSSIBLE WHEN `c.twin` IS FOUNDED.**  The
twin-source law seats the mover on `c.twin`, but `c.twin` is a foundation card
and foundation cards lie on no pile. -/
theorem false_of_slide_onto_of_twin_found
    {A Z : State} {x c : Card} {bb : Base} {σ : Suit}
    (hAwf : A.WF) (hstep : State.step A (Move.tabToTab x bb) = some Z)
    (hrev : reversibleAtW A (Move.tabToTab x bb))
    (hb : bb = Sum.inr c) (hfound : c.twin ∈ A.found σ) : False := by
  subst hb
  have hseat : seatOf A x = some (Sum.inr c.twin) :=
    Mech.mover_seat_twin_of_slide_into_card hAwf hstep hrev
  obtain ⟨a, -, -, hlast⟩ := tfc_seatOf_of_inr hseat
  have hmem : c.twin ∈ (A.piles a).faceUp := mem_below _ (lastOf_mem hlast)
  exact ((mem_found_unique hAwf hfound).1 a).2 hmem

/-- **NO SLIDE OF A PULL-FREE PLAY LANDS ON `c`, GIVEN A FOUNDED TWIN.** -/
theorem no_slide_onto_of_twin_found
    {G Q : State} {g : List Move} {c : Card} {σ : Suit}
    (hGwf : G.WF) (hplay : ShufflePlayW G g Q)
    (hnopull : ∀ m ∈ g, ¬ Bubble.IsPull m)
    (hfound : c.twin ∈ G.found σ) :
    ∀ (x : Card) (bb : Base), Move.tabToTab x bb ∈ g → bb ≠ Sum.inr c := by
  intro x bb hmem hb
  obtain ⟨pre, post, hg⟩ := RaiseLeft.exists_split_mem hmem
  rw [hg] at hplay
  obtain ⟨A, hpre, hrest⟩ :=
    ValleyElim.ShufflePlayW_split hplay pre (Move.tabToTab x bb :: post) rfl
  obtain ⟨Z, hrevA, hstepA, -⟩ := Bubble.walk_cons_inv hrest
  have hAwf : A.WF := SatDifferCensus.ShufflePlayW.wf_end hpre hGwf
  have hnopull_pre : ∀ m ∈ pre, ¬ Bubble.IsPull m := by
    intro m hm hp
    exact hnopull m (by rw [hg]; exact List.mem_append_left _ hm) hp
  obtain ⟨σ', hfoundA⟩ := EmptyTail.found_mem_of_no_pull hpre hfound hnopull_pre
  exact false_of_slide_onto_of_twin_found hAwf hstepA hrevA hb hfoundA

/-! ## §3. `CanRaise c` along the window -/

/-- **A WINDOW LETTER PRESERVES `CanRaise c`.**  Read-safe letters preserve it
by the `R12` survival rows; a slide headed by `c` preserves it by
`EmptyTail.canRaise_survives_own_slide`; a slide landing on `c` is excluded by
`hnc`. -/
theorem canRaise_step_of_window {st s' : State} {m : Move} {c : Card}
    (hst : st.WF) (hrev : reversibleAtW st m) (hstep : State.step st m = some s')
    (hnp : ¬ Bubble.IsPull m)
    (hnr : ∀ w : Card, m = Move.tabToFound w → w.suit ≠ c.suit)
    (hnc : ∀ (x : Card) (bb : Base), m = Move.tabToTab x bb → bb ≠ Sum.inr c)
    (h : CanRaise st c) : CanRaise s' c := by
  cases m with
  | draw => exact R12.canRaise_survives_draw hstep h
  | wasteToFound x => exact absurd hrev (wasteToFound_not_reversibleAtW st x)
  | wasteToTab x bb => exact absurd hrev (wasteToTab_not_reversibleAtW st x bb)
  | tabToFound w =>
      exact R12.canRaise_survives_raise hst hstep (hnr w rfl)
        (fun hwc => hnr w rfl (by rw [hwc])) h
  | foundToTab x bb => exact absurd ⟨x, bb, rfl⟩ hnp
  | tabToTab x bb =>
      by_cases hxc : x = c
      · subst hxc
        exact EmptyTail.canRaise_survives_own_slide hst hstep hrev h
      · exact R12.canRaise_survives_slide hst hstep hrev hxc (hnc x bb rfl) h

/-- **`CanRaise c` AT EVERY PREFIX OF A PULL-FREE WINDOW** whose letters avoid
`c`'s suit, avoid pulls and avoid landing on `c`. -/
theorem canRaise_prefix_of_window {c : Card} :
    ∀ (g : List Move) (G : State), G.WF → CanRaise G c →
      (∀ m ∈ g, ¬ Bubble.IsPull m) →
      (∀ m ∈ g, ∀ w : Card, m = Move.tabToFound w → w.suit ≠ c.suit) →
      (∀ (x : Card) (bb : Base), Move.tabToTab x bb ∈ g → bb ≠ Sum.inr c) →
      ∀ (pre : List Move) (mid : State) (rest : List Move),
        pre ++ rest = g → ShufflePlayW G pre mid → CanRaise mid c := by
  intro g
  induction g with
  | nil =>
      intro G hGwf hcan _ _ _ pre mid rest hsplit hpre
      cases pre with
      | nil =>
          cases hpre with
          | nil st => exact hcan
      | cons a as =>
          simp only [List.cons_append] at hsplit
          exact absurd hsplit (by simp)
  | cons m g' ih =>
      intro G hGwf hcan hnp hnr hnc pre mid rest hsplit hpre
      cases pre with
      | nil =>
          cases hpre with
          | nil st => exact hcan
      | cons a as =>
          simp only [List.cons_append] at hsplit
          obtain ⟨ha, htl⟩ := List.cons.inj hsplit
          rw [ha] at hpre
          obtain ⟨s1, hrev, hstep, hpre'⟩ := Bubble.walk_cons_inv hpre
          have hnopull_m : ¬ Bubble.IsPull m := hnp m (List.mem_cons_self ..)
          have hnopull' : ∀ m' ∈ g', ¬ Bubble.IsPull m' :=
            fun m' hm' => hnp m' (List.mem_cons_of_mem m hm')
          have hnr' : ∀ m' ∈ g', ∀ w : Card, m' = Move.tabToFound w → w.suit ≠ c.suit :=
            fun m' hm' w hw => hnr m' (List.mem_cons_of_mem m hm') w hw
          have hnc' : ∀ (x : Card) (bb : Base), Move.tabToTab x bb ∈ g' → bb ≠ Sum.inr c :=
            fun x bb hx => hnc x bb (List.mem_cons_of_mem m hx)
          have hcan1 : CanRaise s1 c :=
            canRaise_step_of_window hGwf hrev hstep hnopull_m
              (fun w hw => hnr m (List.mem_cons_self ..) w hw)
              (fun x bb hx => hnc x bb (by rw [hx]; exact List.mem_cons_self ..))
              hcan
          exact ih s1 (step_wf hGwf hstep) hcan1 hnopull' hnr' hnc'
            as mid rest htl hpre'

/-! ## §4. The window predicate, and the empty-tail window theorem -/

/-- **`ReadSafeLoose c q`** — `SlideFwd.ReadSafe c` with the *only* clause this
card cannot prove dropped: the slide clause asks only that the slide does not
LAND on `c` (`bb ≠ Sum.inr c`), not that its head differs from `c`.  The
`ReadSafe` slide clause is exactly `ReadSafeLoose` plus "head ≠ `c`". -/
def ReadSafeLoose (z : Card) (q : Move) : Prop :=
  match q with
  | Move.draw => True
  | Move.wasteToFound _ => True
  | Move.wasteToTab _ _ => True
  | Move.tabToFound w => w.suit ≠ z.suit
  | Move.foundToTab c b => c.suit ≠ z.suit ∧ b ≠ Sum.inr z
  | Move.tabToTab _ b => b ≠ Sum.inr z

/-- `ReadSafeLoose` plus "no slide headed by `z`" is `ReadSafe`. -/
theorem readSafe_of_loose_of_noSelf {z : Card} {q : Move}
    (h : ReadSafeLoose z q)
    (hns : ∀ b : Base, q = Move.tabToTab z b → False) :
    SlideFwd.ReadSafe z q := by
  cases q with
  | draw => exact trivial
  | wasteToFound x => exact trivial
  | wasteToTab x bb => exact trivial
  | tabToFound w => exact h
  | foundToTab x bb => exact h
  | tabToTab x bb => exact ⟨(fun hx => hns bb (by rw [hx])), h⟩

/-- `ReadSafeLoose` at `raise d` says exactly that `d` is not in `c`'s suit. -/
theorem loose_raise {c w : Card} (h : w.suit ≠ c.suit) :
    ReadSafeLoose c (Move.tabToFound w) := h

/-- **THE DROPPED CLAUSE IS NOT VACUOUS.**  A slide headed by `c` is never
`ReadSafe c`, so `emptyTail_raiseSafe`'s `ReadSafeLoose` cannot be strengthened
to `ReadSafe` without the geometric input. -/
theorem not_readSafe_selfSlide (c : Card) (bb : Base) :
    ¬ SlideFwd.ReadSafe c (Move.tabToTab c bb) :=
  fun h => h.1 rfl

/-- The same for the target predicate `R12.ReadOK`. -/
theorem not_readOK_selfSlide (c : Card) (bb : Base) :
    ¬ R12.ReadOK c (Move.tabToTab c bb) :=
  fun h => h.1 rfl

open SplitKit in
/-- **THE EMPTY-TAIL WINDOW, EVERYTHING BUT THE SELF-SLIDE.**  At an empty-tail
split of a twin bottom, with the right leg pull-free (`MountainSplit`), every
letter of the window `raise d :: γ` preceding the tail's `raise c` is
`ReadSafeLoose c`.

The three proved clauses:
* no pull (`MountainSplit`);
* no raise in `c`'s suit (`no_raise_same_suit_of_pull_free`, from the rung of
  `c`'s suit at the two ends of the window);
* no slide landing on `c` (`no_slide_onto_of_twin_found`, from the twin founded
  by the split's own `raise d`). -/
theorem emptyTail_raiseSafe
    {u v : State} {ρ : List Move} {F : State}
    {left right : List Move} {c d : Card} {b : Base}
    {pre post tail : List Move}
    (hs : SplitHyp u v ρ F left right c d b pre post tail)
    (hempty : post = [])
    (hms : MountainKit.MountainSplit left right)
    (htwin : d = c.twin)
    {γ β : List Move}
    (hdecomp : tail = γ ++ Move.tabToFound c :: β) :
    ∀ q ∈ Move.tabToFound d :: γ, ReadSafeLoose c q := by
  have hs' := hs
  obtain ⟨huwf, hsu, hsv, hplay, hsplitAt, hmin, hρ, hleft, hright, hshape,
    hfree, hrightShape⟩ := hs
  -- the green facts at the bottom
  have hFwf : F.WF := SatDifferCensus.ShufflePlayW.wf_end hleft huwf
  have hcanF : CanRaise F c := BlockKit.emptyTail_canRaise hs' hempty
  have hdsu : d.suit ≠ c.suit := by
    rw [htwin]
    exact EmptyTail.twin_suit_ne c.suit
  have hdc : d ≠ c := by
    rw [htwin]
    exact SplitKit.card_twin_ne c
  -- the right leg: `raise d` then the pull-free tail
  have hrightD : ShufflePlayW F (Move.tabToFound d :: tail) v := by
    rw [← hrightShape]
    exact hright
  have hnopullRight : ∀ m ∈ right, ¬ Bubble.IsPull m := hms.2
  have hnopullTail : ∀ m ∈ tail, ¬ Bubble.IsPull m := by
    intro m hm hp
    exact hnopullRight m (by rw [hrightShape]; exact List.mem_cons_of_mem _ hm) hp
  have hnopullγ : ∀ m ∈ γ, ¬ Bubble.IsPull m := by
    intro m hm hp
    exact hnopullTail m (by rw [hdecomp]; exact List.mem_append_left _ hm) hp
  obtain ⟨G, hstepD, hplayTail⟩ : ∃ G : State,
      State.step F (Move.tabToFound d) = some G ∧ ShufflePlayW G tail v := by
    cases hrightD with
    | cons _ hs hrest => exact ⟨_, hs, hrest⟩
  have hGwf : G.WF := step_wf hFwf hstepD
  have hcanG : CanRaise G c :=
    R12.canRaise_survives_raise hFwf hstepD hdsu hdc hcanF
  have hnextG : G.nextUp c = true := hcanG.1
  -- split the tail at the `raise c` occurrence
  rw [hdecomp] at hplayTail
  obtain ⟨Q, hplayG1, hrest⟩ :=
    ValleyElim.ShufflePlayW_split hplayTail γ (Move.tabToFound c :: β) rfl
  obtain ⟨Q', -, hstepC, -⟩ := Bubble.walk_cons_inv hrest
  have hnextQ : Q.nextUp c = true := (step_tabToFound_inv hstepC).1
  -- the twin is founded by the split's own `raise d`
  have hfoundG : ∃ σ, c.twin ∈ G.found σ := by
    obtain ⟨-, ap, -, hsG⟩ := step_tabToFound_inv hstepD
    have hsG2 : G = raiseSt F d ap := hsG
    refine ⟨d.suit, ?_⟩
    rw [hsG2, raiseSt_found_apply, ite_eq_left rfl, htwin]
    exact List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl))
  -- no raise in `c`'s suit in `γ`
  have hnoRaise : ∀ m ∈ γ, ∀ w : Card, m = Move.tabToFound w → w.suit ≠ c.suit :=
    no_raise_same_suit_of_pull_free hplayG1 hnopullγ hnextG hnextQ
  -- no slide landing on `c` in `γ`
  have hnoCover : ∀ (x : Card) (bb : Base), Move.tabToTab x bb ∈ γ → bb ≠ Sum.inr c := by
    obtain ⟨σ, hfoundσ⟩ := hfoundG
    exact no_slide_onto_of_twin_found hGwf hplayG1 hnopullγ hfoundσ
  intro q hq
  rcases List.mem_cons.mp hq with rfl | hq'
  · exact loose_raise hdsu
  · cases q with
    | draw => exact trivial
    | wasteToFound x => exact trivial
    | wasteToTab x bb => exact trivial
    | tabToFound w => exact hnoRaise _ hq' w rfl
    | foundToTab x bb => exact absurd ⟨x, bb, rfl⟩ (hnopullγ _ hq')
    | tabToTab x bb => exact hnoCover x bb hq'

open SplitKit in
/-- **THE READ-SAFE WINDOW.**  `emptyTail_raiseSafe` plus the geometric clause
`hns` (no slide headed by `c` in `γ`) gives the full
`SlideFwd.ReadSafe` certificate on `raise d :: γ`. -/
theorem emptyTail_readSafe
    {u v : State} {ρ : List Move} {F : State}
    {left right : List Move} {c d : Card} {b : Base}
    {pre post tail : List Move}
    (hs : SplitHyp u v ρ F left right c d b pre post tail)
    (hempty : post = [])
    (hms : MountainKit.MountainSplit left right)
    (htwin : d = c.twin)
    {γ β : List Move}
    (hdecomp : tail = γ ++ Move.tabToFound c :: β)
    (hns : ∀ bb : Base, Move.tabToTab c bb ∉ γ) :
    ∀ q ∈ Move.tabToFound d :: γ, SlideFwd.ReadSafe c q := by
  have hloose := emptyTail_raiseSafe hs hempty hms htwin hdecomp
  intro q hq
  rcases List.mem_cons.mp hq with rfl | hq'
  · exact hloose _ (List.mem_cons_self ..)
  · refine readSafe_of_loose_of_noSelf (hloose _ (List.mem_cons_of_mem _ hq')) ?_
    intro bb hqeq
    exact hns bb (hqeq ▸ hq')

open SplitKit in
/-- **THE TASK'S `emptyTail_window_readOK`, with the honest hypotheses.**

Differences from the brief's literal statement (see `Temp/Window_Report.md`):
* the window is `raise d :: γ`, not `γ`: `γ` is a suffix of `tail`, which starts
  only after the split's own `raise d`, so the prefix play cannot start at `F`;
* `MountainSplit` (the right leg is pull-free) and the twin identity
  `d = c.twin` are required;
* the self-slide clause `hns` is the remaining geometric input.

The conclusion is the brief's `∀ q ∈ g1, R12.ReadOK c q` (with `g1 = γ`). -/
theorem emptyTail_window_readOK
    {u v : State} {ρ : List Move} {F : State}
    {left right : List Move} {c d : Card} {b : Base}
    {pre post tail : List Move}
    (hs : SplitHyp u v ρ F left right c d b pre post tail)
    (hempty : post = [])
    (hms : MountainKit.MountainSplit left right)
    (htwin : d = c.twin)
    {γ β : List Move}
    (hdecomp : tail = γ ++ Move.tabToFound c :: β)
    (hns : ∀ bb : Base, Move.tabToTab c bb ∉ γ) :
    ∀ q ∈ γ, R12.ReadOK c q := by
  have hsafe := emptyTail_readSafe hs hempty hms htwin hdecomp hns
  obtain ⟨huwf, -, -, -, -, -, -, hleft, hright, -, -, hrightShape⟩ := hs
  have hFwf : F.WF := SatDifferCensus.ShufflePlayW.wf_end hleft huwf
  have hplayW : ShufflePlayW F ((Move.tabToFound d :: γ) ++ Move.tabToFound c :: β) v := by
    have hrightD : ShufflePlayW F (Move.tabToFound d :: tail) v := by
      rw [← hrightShape]
      exact hright
    rw [List.cons_append, ← hdecomp]
    exact hrightD
  intro q hq
  have hmem : q ∈ (Move.tabToFound d :: γ) ++ Move.tabToFound c :: β :=
    List.mem_append_left _ (List.mem_cons_of_mem _ hq)
  obtain ⟨st, hrev⟩ := Surv.walk_exists_reversible hplayW q hmem
  exact SlideFwd.readOK_of_readSafe hrev (hsafe q (List.mem_cons_of_mem _ hq))

open SplitKit in
/-- **THE COMPANION PERSISTENCE FACT.**  Every prefix state of the window
`raise d :: γ` (up to, but not including, the tail's `raise c`) has `CanRaise c`.

This is the task's `canRaise_along_emptyTail_window`, stated at the level of an
arbitrary cut of the window (the brief's `hpre : ShufflePlayW F g1 Q` form is
the case `pre = raise d :: γ`, `rest = []`, with `Q` the cut state). -/
theorem canRaise_along_emptyTail_window
    {u v : State} {ρ : List Move} {F : State}
    {left right : List Move} {c d : Card} {b : Base}
    {pre post tail : List Move}
    (hs : SplitHyp u v ρ F left right c d b pre post tail)
    (hempty : post = [])
    (hms : MountainKit.MountainSplit left right)
    (htwin : d = c.twin)
    {γ β : List Move}
    (hdecomp : tail = γ ++ Move.tabToFound c :: β) :
    ∀ (pre' : List Move) (mid : State) (rest : List Move),
      pre' ++ rest = Move.tabToFound d :: γ →
      ShufflePlayW F pre' mid → CanRaise mid c := by
  have hs' := hs
  obtain ⟨huwf, -, -, -, -, -, -, hleft, hright, -, -, hrightShape⟩ := hs
  have hFwf : F.WF := SatDifferCensus.ShufflePlayW.wf_end hleft huwf
  have hcanF : CanRaise F c := BlockKit.emptyTail_canRaise hs' hempty
  have hdsu : d.suit ≠ c.suit := by
    rw [htwin]
    exact EmptyTail.twin_suit_ne c.suit
  have hdc : d ≠ c := by
    rw [htwin]
    exact SplitKit.card_twin_ne c
  -- the tail is pull-free, hence `γ` is
  have hnopullRight : ∀ m ∈ right, ¬ Bubble.IsPull m := hms.2
  have hnopullTail : ∀ m ∈ tail, ¬ Bubble.IsPull m := by
    intro m hm hp
    exact hnopullRight m (by rw [hrightShape]; exact List.mem_cons_of_mem _ hm) hp
  have hnopullγ : ∀ m ∈ γ, ¬ Bubble.IsPull m := by
    intro m hm hp
    exact hnopullTail m (by rw [hdecomp]; exact List.mem_append_left _ hm) hp
  -- the play from the split's own `raise d`
  have hrightD : ShufflePlayW F (Move.tabToFound d :: tail) v := by
    rw [← hrightShape]
    exact hright
  obtain ⟨G, hstepD, hplayTail⟩ : ∃ G : State,
      State.step F (Move.tabToFound d) = some G ∧ ShufflePlayW G tail v := by
    cases hrightD with
    | cons _ hs hrest => exact ⟨_, hs, hrest⟩
  have hGwf : G.WF := step_wf hFwf hstepD
  have hcanG : CanRaise G c :=
    R12.canRaise_survives_raise hFwf hstepD hdsu hdc hcanF
  rw [hdecomp] at hplayTail
  obtain ⟨Q, hplayG1, hrest⟩ :=
    ValleyElim.ShufflePlayW_split hplayTail γ (Move.tabToFound c :: β) rfl
  obtain ⟨Q', -, hstepC, -⟩ := Bubble.walk_cons_inv hrest
  have hnextQ : Q.nextUp c = true := (step_tabToFound_inv hstepC).1
  -- the twin is founded after `raise d`
  have hfoundG : ∃ σ, c.twin ∈ G.found σ := by
    obtain ⟨-, ap, -, hsG⟩ := step_tabToFound_inv hstepD
    have hsG2 : G = raiseSt F d ap := hsG
    refine ⟨d.suit, ?_⟩
    rw [hsG2, raiseSt_found_apply, ite_eq_left rfl, htwin]
    exact List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl))
  have hnoRaise : ∀ m ∈ γ, ∀ w : Card, m = Move.tabToFound w → w.suit ≠ c.suit :=
    no_raise_same_suit_of_pull_free hplayG1 hnopullγ hcanG.1 hnextQ
  have hnoCover : ∀ (x : Card) (bb : Base), Move.tabToTab x bb ∈ γ → bb ≠ Sum.inr c := by
    obtain ⟨σ, hfoundσ⟩ := hfoundG
    exact no_slide_onto_of_twin_found hGwf hplayG1 hnopullγ hfoundσ
  -- lift the three letter conditions to the whole window `raise d :: γ`
  have hnpW : ∀ m ∈ Move.tabToFound d :: γ, ¬ Bubble.IsPull m := by
    intro m hm
    rcases List.mem_cons.mp hm with rfl | hm'
    · rintro ⟨x, bb, hx⟩
      cases hx
    · exact hnopullγ m hm'
  have hnrW : ∀ m ∈ Move.tabToFound d :: γ, ∀ w : Card,
      m = Move.tabToFound w → w.suit ≠ c.suit := by
    intro m hm w hw
    rcases List.mem_cons.mp hm with rfl | hm'
    · injection hw with hdw
      subst hdw
      exact hdsu
    · exact hnoRaise m hm' w hw
  have hncW : ∀ (x : Card) (bb : Base),
      Move.tabToTab x bb ∈ Move.tabToFound d :: γ → bb ≠ Sum.inr c := by
    intro x bb hm
    rcases List.mem_cons.mp hm with hx | hm'
    · cases hx
    · exact hnoCover x bb hm'
  exact canRaise_prefix_of_window (Move.tabToFound d :: γ) F hFwf hcanF
    hnpW hnrW hncW

open SplitKit in
/-- The brief's companion, at the end of the window (`pre = raise d :: γ`). -/
theorem canRaise_end_of_emptyTail_window
    {u v : State} {ρ : List Move} {F : State}
    {left right : List Move} {c d : Card} {b : Base}
    {pre post tail : List Move}
    (hs : SplitHyp u v ρ F left right c d b pre post tail)
    (hempty : post = [])
    (hms : MountainKit.MountainSplit left right)
    (htwin : d = c.twin)
    {γ β : List Move}
    (hdecomp : tail = γ ++ Move.tabToFound c :: β)
    {Q : State}
    (hpre : ShufflePlayW F (Move.tabToFound d :: γ) Q) :
    CanRaise Q c :=
  canRaise_along_emptyTail_window hs hempty hms htwin hdecomp
    (Move.tabToFound d :: γ) Q [] (by simp) hpre

/-! ## §5. The residual, and the payoff chain -/

/-- **`NoSelfSlide` — THE REMAINING GEOMETRIC DATUM.**  At an empty-tail split
there is an occurrence of the tail's `raise c` whose preceding window contains
no slide headed by `c`.

In the empty-tail twin regime the raise partner exists unconditionally
(`EmptyTail.twin_raisePartner`), so the `∃ γ β` part is free; the only clause of
the read-safe window this card cannot derive from
`SplitHyp + MountainSplit + SplitLivePair` is "no slide headed by `c`"
(§1–§4 prove the other three `ReadSafe` clauses).

Why it is stated over the split and not over the bare state: `CanRaise c` is
*preserved* by a slide headed by `c` (`EmptyTail.canRaise_survives_own_slide`),
so no local state read forbids one; and a c-headed slide followed by `raise c`
is a legal two-letter shape, so the un-gated state-level form is not available.
The datum has to remember that the window is a window of a minimal split. -/
def NoSelfSlide : Prop :=
  ∀ (u v : State) (ρ : List Move) (F : State)
    (left right : List Move) (c d : Card) (b : Base)
    (pre post tail : List Move),
    SplitHyp u v ρ F left right c d b pre post tail → post = [] →
    ∃ (γ β : List Move), tail = γ ++ Move.tabToFound c :: β ∧
      ∀ bb : Base, Move.tabToTab c bb ∉ γ

/-- **THE SLIDE DATUM (named, not proved here).**  The state-level slide datum
owned by the companion card enters this lane exactly as `NoSelfSlide`; this
alias names the interface so the composition below is independent of the
spelling. -/
def SlideRaiseDatum : Prop := NoSelfSlide

theorem noSelfSlide_of_slideRaiseDatum (h : SlideRaiseDatum) : NoSelfSlide := h

open SplitKit in
/-- **THE DATUM GIVES THE READ-SAFE WINDOW RESIDUAL.**  This is the composition
`NoSelfSlide ⇒ SlideFwd.EmptyTailReadWindow`; `SplitLivePair` supplies the
twin identity `d = c.twin` (`EmptyTail.twin_of_livePair_emptyTail`). -/
theorem emptyTail_window_auto
    (hl : SplitLivePair)
    (hms : ∀ (u v : State) (ρ : List Move) (F : State)
      (left right : List Move) (c d : Card) (b : Base)
      (pre post tail : List Move),
      SplitHyp u v ρ F left right c d b pre post tail →
      MountainKit.MountainSplit left right)
    (hns : NoSelfSlide) :
    SlideFwd.EmptyTailReadWindow := by
  intro u v ρ F left right c d b pre post tail hs hempty
  obtain ⟨γ, β, hdecomp, hnoslide⟩ :=
    hns u v ρ F left right c d b pre post tail hs hempty
  have htwin : d = c.twin :=
    EmptyTail.twin_of_livePair_emptyTail hl hs hempty
  have hread := emptyTail_readSafe hs hempty
    (hms u v ρ F left right c d b pre post tail hs) htwin hdecomp hnoslide
  exact ⟨γ, β, hdecomp, hread⟩

/-- **`NoEmptyTail` FROM THE SLIDE DATUM.** -/
theorem noEmptyTail_of_noSelfSlide
    (hl : SplitLivePair)
    (hms : ∀ (u v : State) (ρ : List Move) (F : State)
      (left right : List Move) (c d : Card) (b : Base)
      (pre post tail : List Move),
      SplitHyp u v ρ F left right c d b pre post tail →
      MountainKit.MountainSplit left right)
    (hns : NoSelfSlide) :
    BlockKit.NoEmptyTail :=
  SlideFwd.noEmptyTail_of_readWindow hl hms (emptyTail_window_auto hl hms hns)

/-- **`SplitBlock` FROM THE SLIDE DATUM AND THE COVER HALF.** -/
theorem splitBlock_of_noSelfSlide
    (hl : SplitLivePair)
    (hms : ∀ (u v : State) (ρ : List Move) (F : State)
      (left right : List Move) (c d : Card) (b : Base)
      (pre post tail : List Move),
      SplitHyp u v ρ F left right c d b pre post tail →
      MountainKit.MountainSplit left right)
    (hns : NoSelfSlide) (hcov : BlockKit.TailCovers) :
    SplitBlock :=
  SlideFwd.splitBlock_of_readWindow hl hms (emptyTail_window_auto hl hms hns) hcov

/-- **THE CAMPAIGN CHAIN FROM THE SLIDE DATUM.** -/
theorem satDifferForkWF_of_noSelfSlide
    (hl : SplitLivePair)
    (hms : ∀ (u v : State) (ρ : List Move) (F : State)
      (left right : List Move) (c d : Card) (b : Base)
      (pre post tail : List Move),
      SplitHyp u v ρ F left right c d b pre post tail →
      MountainKit.MountainSplit left right)
    (hns : NoSelfSlide) (hcov : BlockKit.TailCovers)
    (hmin : ValleyElim.ShortestPlayExists) :
    SatDifferForkWF :=
  SlideFwd.satDifferForkWF_of_readWindow hl hms
    (emptyTail_window_auto hl hms hns) hcov hmin

open SplitKit in
/-- **`KeepsForward` RESTRICTED TO EMPTY-TAIL WINDOWS.**  At every empty-tail
split, the pre-`raise c` window `raise d :: γ` satisfies the bubble certificate
`RaiseSwaps`.  This is the input-side form of the task's payoff chain; it uses
`SlideFwd.raiseSwaps_of_readSafe` and no unrestricted `KeepsForward`. -/
theorem keepsForward_emptyTailWindow
    (hl : SplitLivePair)
    (hms : ∀ (u v : State) (ρ : List Move) (F : State)
      (left right : List Move) (c d : Card) (b : Base)
      (pre post tail : List Move),
      SplitHyp u v ρ F left right c d b pre post tail →
      MountainKit.MountainSplit left right)
    (hns : NoSelfSlide)
    {u v : State} {ρ : List Move} {F : State}
    {left right : List Move} {c d : Card} {b : Base}
    {pre post tail : List Move}
    (hs : SplitHyp u v ρ F left right c d b pre post tail) (hempty : post = []) :
    ∃ (γ β : List Move), tail = γ ++ Move.tabToFound c :: β ∧
      RaiseSwaps F c (Move.tabToFound d :: γ) := by
  obtain ⟨γ, β, hdecomp, hnoslide⟩ :=
    hns u v ρ F left right c d b pre post tail hs hempty
  have htwin : d = c.twin := EmptyTail.twin_of_livePair_emptyTail hl hs hempty
  have hread := emptyTail_readSafe hs hempty
    (hms u v ρ F left right c d b pre post tail hs) htwin hdecomp hnoslide
  have hcanF : CanRaise F c := BlockKit.emptyTail_canRaise hs hempty
  obtain ⟨huwf, -, -, -, -, -, -, hleft, hright, -, -, hrightShape⟩ := hs
  have hFwf : F.WF := SatDifferCensus.ShufflePlayW.wf_end hleft huwf
  have hrightD : ShufflePlayW F (Move.tabToFound d :: tail) v := by
    rw [← hrightShape]
    exact hright
  have hplayW : ShufflePlayW F ((Move.tabToFound d :: γ) ++ Move.tabToFound c :: β) v := by
    rw [List.cons_append, ← hdecomp]
    exact hrightD
  exact ⟨γ, β, hdecomp,
    SlideFwd.raiseSwaps_of_readSafe hFwf hplayW hcanF hread⟩

/-- **`KeepsForwardEmptyTail` — `KeepsForward` RESTRICTED TO EMPTY-TAIL
WINDOWS.**  At every empty-tail split, the pre-`raise c` window `raise d :: γ`
satisfies the bubble certificate `RaiseSwaps`.  (The window is quantified
existentially because the raise-partner occurrence is the one
`EmptyTail.twin_raisePartner` produces.) -/
def KeepsForwardEmptyTail : Prop :=
  ∀ (u v : State) (ρ : List Move) (F : State)
    (left right : List Move) (c d : Card) (b : Base)
    (pre post tail : List Move),
    SplitHyp u v ρ F left right c d b pre post tail → post = [] →
    ∃ (γ β : List Move), tail = γ ++ Move.tabToFound c :: β ∧
      RaiseSwaps F c (Move.tabToFound d :: γ)

/-- **THE SLIDE DATUM GIVES THE RESTRICTED `KeepsForward`.** -/
theorem keepsForwardEmptyTail_of_noSelfSlide
    (hl : SplitLivePair)
    (hms : ∀ (u v : State) (ρ : List Move) (F : State)
      (left right : List Move) (c d : Card) (b : Base)
      (pre post tail : List Move),
      SplitHyp u v ρ F left right c d b pre post tail →
      MountainKit.MountainSplit left right)
    (hns : NoSelfSlide) :
    KeepsForwardEmptyTail :=
  fun u v ρ F left right c d b pre post tail hs hempty =>
    keepsForward_emptyTailWindow hl hms hns hs hempty

/-- **`NoEmptyTail` FROM THE RESTRICTED `KeepsForward`.**  The campaign chain's
empty-tail step, exactly as `RaiseLeft.noEmptyTail_of_keepsForward` performs it,
with the window certificate supplied by `KeepsForwardEmptyTail` instead of the
unrestricted `RaiseLeftAcrossTailLen`.  The pair `pull c ; raise c` at the seam
is an identity pair, so the play strictly shortens — against `SplitHyp`'s
minimality. -/
theorem noEmptyTail_of_keepsForwardEmptyTail
    (hl : SplitLivePair)
    (hms : ∀ (u v : State) (ρ : List Move) (F : State)
      (left right : List Move) (c d : Card) (b : Base)
      (pre post tail : List Move),
      SplitHyp u v ρ F left right c d b pre post tail →
      MountainKit.MountainSplit left right)
    (hk : KeepsForwardEmptyTail) :
    BlockKit.NoEmptyTail := by
  intro u v ρ F left right c d b pre post tail h hpost
  have hkeep := h
  obtain ⟨huwf, hsu, hsv, hplay, hsplitAt, hmin, hρ, hleft, hright, hshape,
    hfree, hrightShape⟩ := h
  -- the window certificate
  obtain ⟨γ, β, htail, hsw⟩ :=
    hk u v ρ F left right c d b pre post tail hkeep hpost
  have hFwf : F.WF := SatDifferCensus.ShufflePlayW.wf_end hleft huwf
  -- the right leg, written with the split tail
  have hrightD : ShufflePlayW F (Move.tabToFound d :: tail) v := by
    rw [← hrightShape]
    exact hright
  rw [htail] at hrightD
  rw [hpost] at hshape
  -- bubble `raise c` to the front of `raise d :: γ`
  have hbubble :
      ShufflePlayW F (Move.tabToFound c :: (Move.tabToFound d :: γ) ++ β) v :=
    RaiseLeft.raise_moves_left_window hrightD hsw
  -- the pull's origin
  have hleft' : ShufflePlayW u (pre ++ [Move.foundToTab c b]) F := by
    rw [← hshape]
    simpa using hleft
  obtain ⟨A', hpre, hrest⟩ :=
    ValleyElim.ShufflePlayW_split hleft' pre [Move.foundToTab c b] rfl
  have hstepPull : State.step A' (Move.foundToTab c b) = some F :=
    Elim.step_of_singleton hrest
  have hA' : A'.WF := SatDifferCensus.ShufflePlayW.wf_end hpre huwf
  have hstepRaise : State.step F (Move.tabToFound c) = some A' :=
    step_tabToFound_of_foundToTab hA' hstepPull
  -- the rearranged play, with the adjacent identity pair at the seam
  have hnew : ShufflePlayW u
      (pre ++ Move.foundToTab c b :: Move.tabToFound c ::
        ((Move.tabToFound d :: γ) ++ β)) v := by
    have h := ShufflePlayW_append hleft' hbubble
    simpa [List.append_assoc] using h
  obtain ⟨ρ', hρ'play, hρ'len⟩ :=
    LiveKit.identity_pair_delete (u := u) (v := v)
      (ρ := pre ++ Move.foundToTab c b :: Move.tabToFound c ::
        ((Move.tabToFound d :: γ) ++ β))
      (α := pre) (β := (Move.tabToFound d :: γ) ++ β)
      (m1 := Move.foundToTab c b) (m2 := Move.tabToFound c)
      (A := A') (T := F) hnew rfl hpre ⟨hstepPull, hstepRaise⟩
  -- the lengths agree
  have hlenTail : ((Move.tabToFound d :: γ) ++ β).length = tail.length := by
    rw [htail]
    simp only [List.length_cons, List.length_append] at *
    omega
  have hlenEq :
      (pre ++ Move.foundToTab c b :: Move.tabToFound c ::
        ((Move.tabToFound d :: γ) ++ β)).length = ρ.length := by
    rw [hρ, hshape, hrightShape, htail]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  rw [hlenEq] at hρ'len
  exact absurd hρ'len (Nat.not_lt.mpr (hmin ρ' hρ'play))

/-- **THE PAYOFF CHAIN, INPUT SIDE.**  `SlideRaiseDatum` (the state-level slide
datum, here `NoSelfSlide`) gives `KeepsForwardEmptyTail`, hence `NoEmptyTail`. -/
theorem noEmptyTail_of_slideRaiseDatum
    (hl : SplitLivePair)
    (hms : ∀ (u v : State) (ρ : List Move) (F : State)
      (left right : List Move) (c d : Card) (b : Base)
      (pre post tail : List Move),
      SplitHyp u v ρ F left right c d b pre post tail →
      MountainKit.MountainSplit left right)
    (hdatum : SlideRaiseDatum) :
    BlockKit.NoEmptyTail :=
  noEmptyTail_of_keepsForwardEmptyTail hl hms
    (keepsForwardEmptyTail_of_noSelfSlide hl hms
      (noSelfSlide_of_slideRaiseDatum hdatum))

/-- **`SplitBlock` FROM THE SLIDE DATUM AND THE COVER HALF** (input-side
route, through the restricted `KeepsForward`). -/
theorem splitBlock_of_slideRaiseDatum
    (hl : SplitLivePair)
    (hms : ∀ (u v : State) (ρ : List Move) (F : State)
      (left right : List Move) (c d : Card) (b : Base)
      (pre post tail : List Move),
      SplitHyp u v ρ F left right c d b pre post tail →
      MountainKit.MountainSplit left right)
    (hdatum : SlideRaiseDatum) (hcov : BlockKit.TailCovers) :
    SplitBlock :=
  BlockKit.splitBlock_of_parts
    (noEmptyTail_of_slideRaiseDatum hl hms hdatum) hcov

/-- **THE CAMPAIGN CHAIN FROM THE SLIDE DATUM** — the brief's payoff, in the
input-side spelling: `SlideRaiseDatum ⇒ KeepsForwardEmptyTail ⇒ NoEmptyTail ⇒
SplitBlock ⇒ SatDifferForkWF`. -/
theorem satDifferForkWF_of_slideRaiseDatum
    (hl : SplitLivePair)
    (hms : ∀ (u v : State) (ρ : List Move) (F : State)
      (left right : List Move) (c d : Card) (b : Base)
      (pre post tail : List Move),
      SplitHyp u v ρ F left right c d b pre post tail →
      MountainKit.MountainSplit left right)
    (hdatum : SlideRaiseDatum) (hcov : BlockKit.TailCovers)
    (hmin : ValleyElim.ShortestPlayExists) :
    SatDifferForkWF :=
  BlockKit.satDifferForkWF_of_livePair_parts hl
    (noEmptyTail_of_slideRaiseDatum hl hms hdatum) hcov hmin

open SplitKit in
/-- **THE BUBBLE AT AN EMPTY-TAIL SPLIT.**  The certificate of
`keepsForward_emptyTailWindow` moves the tail's `raise c` to the front of the
window, at the same total length — the exact consequence
`RaiseLeft.noEmptyTail_of_keepsForward` uses. -/
theorem emptyTail_bubble
    (hl : SplitLivePair)
    (hms : ∀ (u v : State) (ρ : List Move) (F : State)
      (left right : List Move) (c d : Card) (b : Base)
      (pre post tail : List Move),
      SplitHyp u v ρ F left right c d b pre post tail →
      MountainKit.MountainSplit left right)
    (hns : NoSelfSlide)
    {u v : State} {ρ : List Move} {F : State}
    {left right : List Move} {c d : Card} {b : Base}
    {pre post tail : List Move}
    (hs : SplitHyp u v ρ F left right c d b pre post tail) (hempty : post = []) :
    ∃ (γ β : List Move), tail = γ ++ Move.tabToFound c :: β ∧
      ShufflePlayW F (Move.tabToFound c :: ((Move.tabToFound d :: γ) ++ β)) v := by
  obtain ⟨γ, β, hdecomp, hsw⟩ := keepsForward_emptyTailWindow hl hms hns hs hempty
  obtain ⟨-, -, -, -, -, -, -, -, hright, -, -, hrightShape⟩ := hs
  have hrightD : ShufflePlayW F (Move.tabToFound d :: tail) v := by
    rw [← hrightShape]
    exact hright
  have hplayW : ShufflePlayW F ((Move.tabToFound d :: γ) ++ Move.tabToFound c :: β) v := by
    rw [List.cons_append, ← hdecomp]
    exact hrightD
  exact ⟨γ, β, hdecomp, RaiseLeft.raise_moves_left_window hplayW hsw⟩

/-! ## §5b. The first-occurrence residual of the source card

`Orig2/Fork/ForkSlideFwd.lean` (the state-level slide-datum card, source, added
concurrently) states the same gap in the FIRST-OCCURRENCE form
`SlideFwd.EmptyTailNoSelfSlide` (`Orig2/Fork/ForkSlideFwd.lean:807`): for the
decomposition at the first `raise c` of the tail (whose prefix contains no
`raise c`), the prefix contains no slide headed by `c`.  This section proves
that the first-occurrence form discharges `NoSelfSlide`, so the two lanes
compose without importing each other's namespaces. -/

/-- **A LIST CONTAINING `m` HAS A FIRST-OCCURRENCE DECOMPOSITION.** -/
theorem exists_first_occurrence {l : List Move} {m : Move} (h : m ∈ l) :
    ∃ (γ β : List Move), l = γ ++ m :: β ∧ ∀ q ∈ γ, q ≠ m := by
  induction l with
  | nil => exact absurd h List.not_mem_nil
  | cons a t ih =>
      by_cases ha : a = m
      · subst ha
        exact ⟨[], t, rfl, by intro q hq; exact absurd hq List.not_mem_nil⟩
      · have h' : m ∈ t := by
          rcases List.mem_cons.mp h with h1 | h2
          · exact absurd h1.symm ha
          · exact h2
        obtain ⟨γ, β, hγ, hfirst⟩ := ih h'
        refine ⟨a :: γ, β, by rw [hγ]; rfl, ?_⟩
        intro q hq
        rcases List.mem_cons.mp hq with rfl | hq'
        · exact ha
        · exact hfirst q hq'

/-- **`NoSelfSlideFirst`** — the first-occurrence form of `NoSelfSlide`: the
window at the FIRST `raise c` of the tail (prefix `raise c`-free) has no slide
headed by `c`.  `SlideFwd.EmptyTailNoSelfSlide`
(`Orig2/Fork/ForkSlideFwd.lean:807`) is exactly this predicate. -/
def NoSelfSlideFirst : Prop :=
  ∀ (u v : State) (ρ : List Move) (F : State)
    (left right : List Move) (c d : Card) (b : Base)
    (pre post tail : List Move) (γ β : List Move),
    SplitHyp u v ρ F left right c d b pre post tail → post = [] →
    tail = γ ++ Move.tabToFound c :: β →
    (∀ q ∈ γ, q ≠ Move.tabToFound c) →
    ∀ bb : Base, Move.tabToTab c bb ∉ γ

/-- **THE FIRST-OCCURRENCE DATUM DISCHARGES `NoSelfSlide`.**  The raise partner
exists unconditionally (`EmptyTail.twin_raisePartner`); cut the tail at its
first occurrence (`exists_first_occurrence`) and apply the datum. -/
theorem noSelfSlide_of_noSelfSlideFirst
    (hl : SplitLivePair)
    (hms : ∀ (u v : State) (ρ : List Move) (F : State)
      (left right : List Move) (c d : Card) (b : Base)
      (pre post tail : List Move),
      SplitHyp u v ρ F left right c d b pre post tail →
      MountainKit.MountainSplit left right)
    (h : NoSelfSlideFirst) :
    NoSelfSlide := by
  intro u v ρ F left right c d b pre post tail hs hempty
  have htwin : d = c.twin := EmptyTail.twin_of_livePair_emptyTail hl hs hempty
  have hpart : EmptyTail.RaisePartner tail c :=
    EmptyTail.twin_raisePartner hs hempty
      (hms u v ρ F left right c d b pre post tail hs) htwin
  obtain ⟨γ₀, β₀, hγ₀⟩ := hpart
  have hmem : Move.tabToFound c ∈ tail := by
    rw [hγ₀]
    exact List.mem_append_right _ (List.mem_cons_self ..)
  obtain ⟨γ, β, hdecomp, hfirst⟩ :=
    exists_first_occurrence (l := tail) (m := Move.tabToFound c) hmem
  exact ⟨γ, β, hdecomp,
    h u v ρ F left right c d b pre post tail γ β hs hempty hdecomp hfirst⟩

/-- **THE WHOLE CHAIN FROM THE FIRST-OCCURRENCE DATUM.** -/
theorem satDifferForkWF_of_noSelfSlideFirst
    (hl : SplitLivePair)
    (hms : ∀ (u v : State) (ρ : List Move) (F : State)
      (left right : List Move) (c d : Card) (b : Base)
      (pre post tail : List Move),
      SplitHyp u v ρ F left right c d b pre post tail →
      MountainKit.MountainSplit left right)
    (hres : NoSelfSlideFirst) (hcov : BlockKit.TailCovers)
    (hmin : ValleyElim.ShortestPlayExists) :
    SatDifferForkWF :=
  satDifferForkWF_of_noSelfSlide hl hms
    (noSelfSlide_of_noSelfSlideFirst hl hms hres) hcov hmin

/-- The source card's residual is the first-occurrence form spelled with
`NoSlideOf`. -/
theorem noSelfSlideFirst_of_emptyTailNoSelfSlide
    (h : SlideFwd.EmptyTailNoSelfSlide) : NoSelfSlideFirst := by
  intro u v ρ F left right c d b pre post tail γ β hs hempty hdecomp hfirst bb hmem
  exact (h u v ρ F left right c d b pre post tail γ β hs hempty hdecomp hfirst)
    c bb hmem rfl

/-- **THE OTHER CARD'S DATUM DISCHARGES `NoSelfSlide`.**  `SlideFwd.EmptyTailNoSelfSlide`
(`Orig2/Fork/ForkSlideFwd.lean:807`, source) is the state-level slide datum in the
first-occurrence spelling; this is the composition the two lanes need. -/
theorem noSelfSlide_of_emptyTailNoSelfSlide
    (hl : SplitLivePair)
    (hms : ∀ (u v : State) (ρ : List Move) (F : State)
      (left right : List Move) (c d : Card) (b : Base)
      (pre post tail : List Move),
      SplitHyp u v ρ F left right c d b pre post tail →
      MountainKit.MountainSplit left right)
    (h : SlideFwd.EmptyTailNoSelfSlide) :
    NoSelfSlide :=
  noSelfSlide_of_noSelfSlideFirst hl hms
    (noSelfSlideFirst_of_emptyTailNoSelfSlide h)

/-- **THE WHOLE CAMPAIGN CHAIN FROM THE SOURCE CARD'S DATUM.** -/
theorem satDifferForkWF_of_emptyTailNoSelfSlide
    (hl : SplitLivePair)
    (hms : ∀ (u v : State) (ρ : List Move) (F : State)
      (left right : List Move) (c d : Card) (b : Base)
      (pre post tail : List Move),
      SplitHyp u v ρ F left right c d b pre post tail →
      MountainKit.MountainSplit left right)
    (hres : SlideFwd.EmptyTailNoSelfSlide) (hcov : BlockKit.TailCovers)
    (hmin : ValleyElim.ShortestPlayExists) :
    SatDifferForkWF :=
  satDifferForkWF_of_noSelfSlide hl hms
    (noSelfSlide_of_emptyTailNoSelfSlide hl hms hres) hcov hmin

end Window

/-! ## §6. Battery -/

#print axioms Window.card_eq_of_nextUp
#print axioms Window.rung_step_of_not_pull_not_raise
#print axioms Window.no_raise_same_suit_of_pull_free
#print axioms Window.false_of_slide_onto_of_twin_found
#print axioms Window.no_slide_onto_of_twin_found
#print axioms Window.canRaise_step_of_window
#print axioms Window.canRaise_prefix_of_window
#print axioms Window.readSafe_of_loose_of_noSelf
#print axioms Window.loose_raise
#print axioms Window.not_readSafe_selfSlide
#print axioms Window.not_readOK_selfSlide
#print axioms Window.emptyTail_raiseSafe
#print axioms Window.emptyTail_readSafe
#print axioms Window.emptyTail_window_readOK
#print axioms Window.canRaise_along_emptyTail_window
#print axioms Window.canRaise_end_of_emptyTail_window
#print axioms Window.noSelfSlide_of_slideRaiseDatum
#print axioms Window.emptyTail_window_auto
#print axioms Window.keepsForwardEmptyTail_of_noSelfSlide
#print axioms Window.noEmptyTail_of_keepsForwardEmptyTail
#print axioms Window.noEmptyTail_of_slideRaiseDatum
#print axioms Window.splitBlock_of_slideRaiseDatum
#print axioms Window.satDifferForkWF_of_slideRaiseDatum
#print axioms Window.noEmptyTail_of_noSelfSlide
#print axioms Window.splitBlock_of_noSelfSlide
#print axioms Window.satDifferForkWF_of_noSelfSlide
#print axioms Window.keepsForward_emptyTailWindow
#print axioms Window.emptyTail_bubble
#print axioms Window.exists_first_occurrence
#print axioms Window.noSelfSlide_of_noSelfSlideFirst
#print axioms Window.satDifferForkWF_of_noSelfSlideFirst
#print axioms Window.noSelfSlideFirst_of_emptyTailNoSelfSlide
#print axioms Window.noSelfSlide_of_emptyTailNoSelfSlide
#print axioms Window.satDifferForkWF_of_emptyTailNoSelfSlide
