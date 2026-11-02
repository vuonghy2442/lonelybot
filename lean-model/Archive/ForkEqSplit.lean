import Orig2.ForkMateGate
import Orig2.Fork.Class.ForkReadBracket
import Orig2.Fork.Third.ForkNonfork

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option linter.unusedVariables false

/-!
# Orig2/ForkEqSplit — `NoEqualRungMountainSplit`: the self-bracket reduction

READ-ONLY scratch (no source edit, no commit).  Zero `sorry`, zero
`Classical.choice`, zero `native_decide`; axiom battery at the tail.

## What this card establishes

1. **The equal-rung corner is a genuine `pull c ; … ; raise c` self-bracket**
   (`MateGate.raise_c_mem_right_of_equalRung` promoted from `Orig2/ForkMateGate`),
   and the pull is the *last* pull of the play (`MateGate.pull_mem_pre_or_eq`).

2. **Every clause of the read-safe window is free except the two slide
   clauses.**  With `ρ = pre ++ pull c b :: (post ++ γ) ++ raise c :: β` and `γ`
   the *first* occurrence window in the pull-free right leg:
   - no pull in the window (`MountainSplit`'s right leg is pull-free, `post` is
     free);
   - no `c.suit` raise in the window (`Direct.no_sigma_raise_or_raise_e` at
     `rungAt F c.suit = c.rank`, plus firstness);
   - `draw`s are inert for the pending raise.
   So `SlideFwd.ReadSafe c` holds on the window as soon as
     (a) no slide of the window is headed by `c`, and
     (b) no slide of the window lands on `c`.

3. **The two slide clauses are exactly the residual.**  They are the two
   clauses of `R12.ReadOK` that no rung/ledger argument reaches, and they are
   the same obstruction as the campaign's own `SlideFwd.EmptyTailNoSelfSlide`
   (`Orig2/Fork/Local/ForkSlideFwd.lean:807`): a slide headed by `c` can never be bubbled
   past `raise c` (`R12.no_slide_self_at`).

4. **The reduction.**  `EqualRungInteriorSlideFree` (the named residual, §4)
   implies `MateGate.NoEqualRungMountainSplit`: the read-safe window makes
   `NonforkKit.bracket_delete_gen` delete the bracket, contradicting the
   split's shortest-play conjunct.

5. **Unconditional sub-cases.**  The residual is discharged, hence the target
   is proved outright, whenever the window carries no slide at all — in
   particular at `post = []` with the right leg opening on `raise c`
   (§5).

6. **The "lands on `c`" clause is free when `c.twin` is founded at the pull
   landing** (§6), by `Mech.mover_seat_twin_of_slide_into_card` +
   `EmptyTail.twin_no_coverSlide`; only the head clause is then owed
   (`EqualRungInteriorHeadFree`).

7. **Both slide clauses are necessary for the bubbling method** (§7):
   `R12.no_slide_self_at` (head) and `no_base_slide_after_raise` (base, proved
   here: after `raise c` the card is founded and tops no pile).

8. **Cross-check against the campaign's own residual** (§8): in the empty-tail
   twin regime the residual of this card is *implied* by
   `SlideFwd.EmptyTailNoSelfSlide` together with `emptyTail_window_soft`, so
   this is not a new obligation.

## The witness `F_t1_runshiftp2` reads off the same geometry

At the only known equal-rung minimal `SplitHyp`
(`Orig2/ForkEqualRungMain.lean:102`) the split card is `c = 3C`, the split's
pull is `m9 = pull 3C → 4D`, and `m3 = raise 3C` sits in `pre`
(`Orig2/ForkEqualRungBoard.lean:254,260,423-427`).  So the known equal-rung
self-bracket has its raise on the **left** of the split, which is exactly what
`MountainSplit`'s first conjunct forbids; this card closes the *other* escape
(the raise in `right`), leaving only the window clauses above.
-/

namespace EqSplit

open ValleyElim

/-! ## §1. Split data: the pull letter and the first `raise c` of the right leg -/

/-- **THE SPLIT'S OWN PULL, EXTENDED TO ITS STEP.**  `SplitHyp` gives
`left = pre ++ pull c b :: post`; splitting the left witness leg at `pre` and
reading the head step gives the pull's origin and landing. -/
theorem split_pull_data
    {u v : State} {ρ : List Move} {F : State} {left right : List Move}
    {c d : Card} {b : Base} {pre post tail : List Move}
    (hs : SplitKit.SplitHyp u v ρ F left right c d b pre post tail) :
    ∃ A' B : State, ShufflePlayW u pre A' ∧
      State.step A' (Move.foundToTab c b) = some B := by
  obtain ⟨-, -, -, -, -, -, -, hleft, -, hshape, -, -⟩ := hs
  obtain ⟨A', hpre, hrest⟩ :=
    ShufflePlayW_split hleft pre (Move.foundToTab c b :: post) hshape
  cases hrest with
  | @cons _ B _ _ _ hrev hstep hpost => exact ⟨A', B, hpre, hstep⟩

/-- **THE FIRST `raise c` OF A LIST, AS A DECOMPOSITION.**  A computable
first-occurrence split: the window is `raise c`-free. -/
theorem first_raise_split {c : Card} {l : List Move}
    (h : Direct.Occurs (Move.tabToFound c) l) :
    ∃ γ β : List Move, l = γ ++ Move.tabToFound c :: β ∧
      ∀ q ∈ γ, q ≠ Move.tabToFound c := by
  obtain ⟨s1, s2, hs⟩ := h
  have hany : l.any (fun m => decide (m = Move.tabToFound c)) = true := by
    refine ValleyElim.any_eq_true_of_mem (m := Move.tabToFound c) ?_ ?_
    · rw [hs]; exact List.mem_append_right _ (List.mem_cons_self ..)
    · exact decide_eq_true rfl
  obtain ⟨γ, m, β, hl, hfalse, htrue⟩ :=
    ValleyElim.exists_first_bool (fun m => decide (m = Move.tabToFound c)) l hany
  have hm : m = Move.tabToFound c := of_decide_eq_true htrue
  subst hm
  refine ⟨γ, β, hl, ?_⟩
  intro q hq hqe
  have h1 : decide (q = Move.tabToFound c) = false := hfalse q hq
  rw [hqe, decide_eq_true rfl] at h1
  exact Bool.false_ne_true h1.symm

/-- **THE BOTTOM'S `c.suit` RUNG IS `c.rank`.**  At equal rung vectors the
split card is exactly the frontier card of its suit at the bottom: the pull
drops the rung to `c.rank` and the free tail preserves it. -/
theorem rungAt_F_eq_card_rank
    {u v : State} {ρ : List Move} {F : State} {left right : List Move}
    {c d : Card} {b : Base} {pre post tail : List Move}
    (heq : ∀ σ : Suit, rungAt u σ = rungAt v σ)
    (hs : SplitKit.SplitHyp u v ρ F left right c d b pre post tail) :
    rungAt F c.suit = c.rank.toIdx := by
  have hsk := hs
  obtain ⟨huwf, -, -, -, -, -, -, -, -, -, hfree, -⟩ := hs
  obtain ⟨A', B, hpre, hstep⟩ := split_pull_data hsk
  have hA' : A'.WF := SatDifferCensus.ShufflePlayW.wf_end hpre huwf
  have hB : B.WF := step_wf hA' hstep
  obtain ⟨hpost, -⟩ := Landing.post_play_of_landing hsk hpre hstep
  have hcanB : CanRaise B c := ValleyStep.pull_card_canRaise hA' hstep
  have hrungB : rungAt B c.suit = c.rank.toIdx :=
    (ThirdLive.rank_eq_rungAt_of_canRaiseS hB (CanRaiseS.now c hcanB)).symm
  rw [ValleyElim.rungAt_eq_of_free_play hpost hfree c.suit, hrungB]

/-! ## §2. The interior window: everything but the two slide clauses -/

/-- **NO `c.suit` RAISE IN THE FIRST-OCCURRENCE WINDOW.**  The right leg is
pull-free and starts at rung `c.rank`; by
`Direct.no_sigma_raise_or_raise_e` any `c.suit` raise of the window would be
`raise c` itself, contradicting firstness. -/
theorem no_csuit_raise_in_window
    {F mid : State} {γ : List Move} {c : Card}
    (hplay : ShufflePlayW F γ mid) (hF : F.WF)
    (hnopull : ∀ m ∈ γ, ¬ Bubble.IsPull m)
    (hrung : rungAt F c.suit = c.rank.toIdx)
    (hfirst : ∀ q ∈ γ, q ≠ Move.tabToFound c) :
    ∀ w : Card, Direct.Occurs (Move.tabToFound w) γ → w.suit ≠ c.suit := by
  intro w hw
  rcases Direct.no_sigma_raise_or_raise_e hplay hF hnopull hrung with h | h
  · exact h w hw
  · obtain ⟨s1, s2, hs⟩ := h
    have hmem : Move.tabToFound c ∈ γ := by
      rw [hs]; exact List.mem_append_right _ (List.mem_cons_self ..)
    exact absurd rfl (hfirst _ hmem)

/-- **THE WINDOW IS READ-SAFE ONCE THE TWO SLIDE CLAUSES HOLD.**  `post` is
free (draw or slide) and `γ` is a pull-free first-occurrence window, so the
only letters that can touch `c`'s pending raise are the slides. -/
theorem interior_readSafe
    {post γ : List Move} {c : Card}
    (hfree : ∀ m ∈ post, FreeMove m)
    (hnopullγ : ∀ m ∈ γ, ¬ Bubble.IsPull m)
    (hnoraiseγ : ∀ w : Card, Direct.Occurs (Move.tabToFound w) γ →
      w.suit ≠ c.suit)
    (hnoslide : SlideFwd.NoSlideOf c (post ++ γ))
    (hnobase : ∀ x : Card, Move.tabToTab x (Sum.inr c) ∉ post ++ γ) :
    ∀ q ∈ post ++ γ, SlideFwd.ReadSafe c q := by
  intro q hq
  rcases List.mem_append.mp hq with hq | hq
  · rcases hfree q hq with hdraw | ⟨x, bb, hsl⟩
    · subst hdraw; exact trivial
    · subst hsl
      exact SlideFwd.readSafe_slide_of_ne
        (hnoslide x bb (List.mem_append_left _ hq))
        (fun hb => hnobase x (hb ▸ List.mem_append_left _ hq))
  · cases q with
    | draw => exact trivial
    | wasteToFound x => exact trivial
    | wasteToTab x bb => exact trivial
    | tabToFound w =>
        exact hnoraiseγ w
          (by obtain ⟨s1, s2, hs⟩ := RaiseLeft.exists_split_mem hq; exact ⟨s1, s2, hs⟩)
    | foundToTab x bb =>
        exact absurd ⟨x, bb, rfl⟩ (hnopullγ _ hq)
    | tabToTab x bb =>
        exact SlideFwd.readSafe_slide_of_ne
          (hnoslide x bb (List.mem_append_right _ hq))
          (fun hb => hnobase x (hb ▸ List.mem_append_right _ hq))

/-! ## §3. The deletion: a clean self-bracket contradicts minimality -/

/-- **THE SELF-BRACKET DELETION.**  Given the equal-rung split, the
first-occurrence window `γ` of `raise c` in the pull-free right leg, and the two
slide clauses on `post ++ γ`, the bracket `pull c b ; post ++ γ ; raise c` is
read-safe, so `NonforkKit.bracket_delete_gen` deletes it — contradicting the
shortest-play conjunct of `SplitHyp`. -/
theorem not_mountainSplit_of_window
    {u v : State} {ρ : List Move} {F : State} {left right : List Move}
    {c d : Card} {b : Base} {pre post tail : List Move} {γ β : List Move}
    (heq : ∀ σ : Suit, rungAt u σ = rungAt v σ)
    (hs : SplitKit.SplitHyp u v ρ F left right c d b pre post tail)
    (hms : MountainKit.MountainSplit left right)
    (hrightEq : right = γ ++ Move.tabToFound c :: β)
    (hfirst : ∀ q ∈ γ, q ≠ Move.tabToFound c)
    (hnoslide : SlideFwd.NoSlideOf c (post ++ γ))
    (hnobase : ∀ x : Card, Move.tabToTab x (Sum.inr c) ∉ post ++ γ) :
    False := by
  have hsk := hs
  obtain ⟨huwf, hsu, hsv, hplay, hvs, hmin, hρ, hleft, hright, hshape, hfree,
    hrightShape⟩ := hs
  obtain ⟨A', B, hpre, hstep⟩ := split_pull_data hsk
  have hA' : A'.WF := SatDifferCensus.ShufflePlayW.wf_end hpre huwf
  have hBwf : B.WF := step_wf hA' hstep
  obtain ⟨hpostPlay, -⟩ := Landing.post_play_of_landing hsk hpre hstep
  have hF : F.WF := SatDifferCensus.ShufflePlayW.wf_end hleft huwf
  have hrungF : rungAt F c.suit = c.rank.toIdx :=
    rungAt_F_eq_card_rank heq hsk
  -- the right leg splits at the first `raise c`
  obtain ⟨mid, hγplay, hrestPlay⟩ :=
    ShufflePlayW_split hright γ (Move.tabToFound c :: β) hrightEq
  have hnopullγ : ∀ m ∈ γ, ¬ Bubble.IsPull m :=
    fun m hm => hms.2 m (by rw [hrightEq]; exact List.mem_append_left _ hm)
  have hnoraiseγ : ∀ w : Card, Direct.Occurs (Move.tabToFound w) γ →
      w.suit ≠ c.suit :=
    no_csuit_raise_in_window hγplay hF hnopullγ hrungF hfirst
  have hread : ∀ q ∈ post ++ γ, SlideFwd.ReadSafe c q :=
    interior_readSafe hfree hnopullγ hnoraiseγ hnoslide hnobase
  -- the bracket play from the pull's landing
  have hbracket : ShufflePlayW B (post ++ γ ++ Move.tabToFound c :: β) v := by
    have hchain : ShufflePlayW B (post ++ right) v := ShufflePlayW_append hpostPlay hright
    rw [hrightEq] at hchain
    simpa only [List.append_assoc] using hchain
  have hcanB : CanRaise B c := ValleyStep.pull_card_canRaise hA' hstep
  have hsw : NonforkKit.RaiseSwaps B c (post ++ γ) :=
    SlideFwd.raiseSwaps_of_readSafe hBwf hbracket hcanB hread
  -- the whole play, in the deletion shape
  have hρ' : ρ = pre ++ Move.foundToTab c b :: (post ++ γ) ++ Move.tabToFound c :: β := by
    rw [hρ, hshape, hrightEq]
    simp only [List.append_assoc, List.cons_append]
  obtain ⟨ρ', hρ'play, hρ'len⟩ :=
    NonforkKit.bracket_delete_gen huwf hplay hρ' hpre hstep hsw
  exact absurd hρ'len (Nat.not_lt.mpr (hmin ρ' hρ'play))

/-! ## §4. The residual, and the reduction -/

/-- **`EqualRungInteriorSlideFree` — THE EXACT RESIDUAL.**  At an equal-rung
`MountainSplit` split there is an occurrence of `raise c` in the pull-free
right leg whose interior window `post ++ γ` carries:

* no slide headed by `c` (the campaign's `NoSelfSlide` clause), and
* no slide landing on `c` (the twin-seat clause of `EmptyTail.twin_no_coverSlide`).

Everything else about the window is derived in §2. -/
def EqualRungInteriorSlideFree : Prop :=
  ∀ (u v : State) (ρ : List Move) (F : State)
    (left right : List Move) (c d : Card) (b : Base)
    (pre post tail : List Move),
    (∀ σ : Suit, rungAt u σ = rungAt v σ) →
    SplitKit.SplitHyp u v ρ F left right c d b pre post tail →
    MountainKit.MountainSplit left right →
    ∃ (γ β : List Move),
      right = γ ++ Move.tabToFound c :: β ∧
      (∀ q ∈ γ, q ≠ Move.tabToFound c) ∧
      SlideFwd.NoSlideOf c (post ++ γ) ∧
      (∀ x : Card, Move.tabToTab x (Sum.inr c) ∉ post ++ γ)

/-- **THE RESIDUAL IMPLIES THE TARGET.**  `NoEqualRungMountainSplit` follows
from `EqualRungInteriorSlideFree` by the bracket deletion of §3. -/
theorem noEqualRungMountainSplit_of_slideFree
    (hres : EqualRungInteriorSlideFree) :
    MateGate.NoEqualRungMountainSplit := by
  intro u v ρ F left right c d b pre post tail heq hs hms
  obtain ⟨γ, β, hrightEq, hfirst, hnoslide, hnobase⟩ :=
    hres u v ρ F left right c d b pre post tail heq hs hms
  exact not_mountainSplit_of_window heq hs hms hrightEq hfirst hnoslide hnobase

/-- **THE GATE IS FREE FROM THE RESIDUAL.**  With `EqualRungInteriorSlideFree`
the un-gated `Direct.MateRaiseFree` is exactly the gated
`Gated.MateRaiseFreeDiffering` — the payoff the `MateGate` card asks for. -/
theorem mateRaiseFree_iff_differing_of_slideFree
    (hres : EqualRungInteriorSlideFree) :
    Direct.MateRaiseFree ↔ Gated.MateRaiseFreeDiffering :=
  MateGate.mateRaiseFree_iff_differing_of_noEqualRung
    (noEqualRungMountainSplit_of_slideFree hres)

/-- **THE EQUAL-RUNG CLAUSE IS FREE FROM THE RESIDUAL.** -/
theorem equalRungMateRaiseFree_of_slideFree
    (hres : EqualRungInteriorSlideFree) : MateGate.EqualRungMateRaiseFree := by
  intro u v ρ F left right c d b pre post tail heq hs hms A' B hpre hstep e he h1 h2
  exact absurd hms (noEqualRungMountainSplit_of_slideFree hres
    u v ρ F left right c d b pre post tail heq hs)

/-! ## §5. Unconditional sub-cases: windows with no slide at all

If the window carries no slide, both clauses are free and the target holds
with no residual.  The natural instance is the empty window. -/

/-- **A SLIDE-FREE WINDOW DISCHARGES THE RESIDUAL.** -/
theorem not_mountainSplit_of_window_noSlide
    {u v : State} {ρ : List Move} {F : State} {left right : List Move}
    {c d : Card} {b : Base} {pre post tail : List Move} {γ β : List Move}
    (heq : ∀ σ : Suit, rungAt u σ = rungAt v σ)
    (hs : SplitKit.SplitHyp u v ρ F left right c d b pre post tail)
    (hms : MountainKit.MountainSplit left right)
    (hrightEq : right = γ ++ Move.tabToFound c :: β)
    (hfirst : ∀ q ∈ γ, q ≠ Move.tabToFound c)
    (hnoslides : ∀ (x : Card) (bb : Base), Move.tabToTab x bb ∉ post ++ γ) :
    False := by
  refine not_mountainSplit_of_window heq hs hms hrightEq hfirst ?_ ?_
  · intro x bb hmem
    exact absurd hmem (hnoslides x bb)
  · intro x hmem
    exact hnoslides x (Sum.inr c) hmem

/-- **THE EMPTY-WINDOW CORNER: THE RIGHT LEG OPENS ON `raise c`.**  If the
free tail is empty and the right leg's first `raise c` is its head, the window
is empty, so no equal-rung `MountainSplit` exists at that split. -/
theorem not_mountainSplit_of_post_nil_of_head
    {u v : State} {ρ : List Move} {F : State} {left right : List Move}
    {c d : Card} {b : Base} {pre post tail : List Move} {β : List Move}
    (heq : ∀ σ : Suit, rungAt u σ = rungAt v σ)
    (hs : SplitKit.SplitHyp u v ρ F left right c d b pre post tail)
    (hms : MountainKit.MountainSplit left right)
    (hpost : post = [])
    (hrightEq : right = Move.tabToFound c :: β) :
    False := by
  have hsk := hs
  refine not_mountainSplit_of_window_noSlide heq hsk hms
    (γ := []) (β := β) ?_ ?_ ?_
  · simpa using hrightEq
  · intro q hq; exact absurd hq (by simp)
  · intro x bb hmem
    rw [hpost] at hmem
    exact absurd hmem (by simp)

/-! ## §6. The "lands on `c`" clause is free when `c.twin` is founded at the
pull landing

`Mech.mover_seat_twin_of_slide_into_card` (`Orig2/Fork/Local/ForkMechanism.lean:50`) says
a reversible slide landing on `c` has its mover seated directly on `c.twin`.
Hence if `c.twin` is in a foundation at the pull's landing `B`, no slide of the
(pull-free) window can land on `c` — `EmptyTail.twin_no_coverSlide`
(`Orig2/Fork/Split/ForkEmptyTail.lean:370`).  So in that regime only the *head* clause is
owed. -/

/-- **NO SLIDE LANDS ON `c` WHEN `c.twin` IS FOUNDED AT THE WINDOW'S START.** -/
theorem not_base_of_twin_found
    {B mid : State} {post γ : List Move} {c : Card}
    (hB : B.WF) (hplay : ShufflePlayW B (post ++ γ) mid)
    (hnopull : ∀ m ∈ post ++ γ, ¬ Bubble.IsPull m)
    (hfound : ∃ σ : Suit, c.twin ∈ B.found σ) :
    ∀ x : Card, Move.tabToTab x (Sum.inr c) ∉ post ++ γ := by
  intro x hmem
  obtain ⟨pre, rest, heq⟩ := RaiseLeft.exists_split_mem hmem
  refine EmptyTail.twin_no_coverSlide hB hplay hnopull hfound ?_
  refine SlideFwd.tailCoverSlide_of_letter hplay pre (x := x) (rest := rest) ?_
  exact heq

/-- **`EqualRungInteriorHeadFree` — the head-only residual.**  The same window
as `EqualRungInteriorSlideFree`, owing only the clause "no slide is headed by
`c`" (the campaign's `NoSelfSlide`). -/
def EqualRungInteriorHeadFree : Prop :=
  ∀ (u v : State) (ρ : List Move) (F : State)
    (left right : List Move) (c d : Card) (b : Base)
    (pre post tail : List Move),
    (∀ σ : Suit, rungAt u σ = rungAt v σ) →
    SplitKit.SplitHyp u v ρ F left right c d b pre post tail →
    MountainKit.MountainSplit left right →
    ∃ (γ β : List Move),
      right = γ ++ Move.tabToFound c :: β ∧
      (∀ q ∈ γ, q ≠ Move.tabToFound c) ∧
      SlideFwd.NoSlideOf c (post ++ γ)

/-- **THE HEAD-ONLY RESIDUAL PLUS A FOUNDED TWIN AT THE LANDING.**  This is the
`NoSelfSlide` corner with the "lands on `c`" clause discharged by
`not_base_of_twin_found`. -/
theorem noEqualRungMountainSplit_of_headFree_of_twinFound
    (hres : EqualRungInteriorHeadFree)
    (htwin : ∀ (u v : State) (ρ : List Move) (F : State)
      (left right : List Move) (c d : Card) (b : Base)
      (pre post tail : List Move),
      (∀ σ : Suit, rungAt u σ = rungAt v σ) →
      SplitKit.SplitHyp u v ρ F left right c d b pre post tail →
      ∀ (A' B : State), ShufflePlayW u pre A' →
        State.step A' (Move.foundToTab c b) = some B →
        ∃ σ : Suit, c.twin ∈ B.found σ) :
    MateGate.NoEqualRungMountainSplit := by
  intro u v ρ F left right c d b pre post tail heq hs hms
  obtain ⟨γ, β, hrightEq, hfirst, hnoslide⟩ :=
    hres u v ρ F left right c d b pre post tail heq hs hms
  have hsk := hs
  obtain ⟨huwf, hsu, hsv, hplay, hvs, hmin, hρ, hleft, hright, hshape, hfree,
    hrightShape⟩ := hs
  obtain ⟨A', B, hpre, hstep⟩ := split_pull_data hsk
  have hA' : A'.WF := SatDifferCensus.ShufflePlayW.wf_end hpre huwf
  have hBwf : B.WF := step_wf hA' hstep
  obtain ⟨hpostPlay, -⟩ := Landing.post_play_of_landing hsk hpre hstep
  obtain ⟨mid, hγplay, -⟩ :=
    ShufflePlayW_split hright γ (Move.tabToFound c :: β) hrightEq
  have hnopullPost : ∀ m ∈ post, ¬ Bubble.IsPull m := by
    intro m hm hp
    rcases hfree m hm with hd | ⟨x, bb, hsl⟩
    · subst hd; obtain ⟨y, c', hy⟩ := hp; cases hy
    · subst hsl; obtain ⟨y, c', hy⟩ := hp; cases hy
  have hnopullWindow : ∀ m ∈ post ++ γ, ¬ Bubble.IsPull m := by
    intro m hm
    rcases List.mem_append.mp hm with hm | hm
    · exact hnopullPost m hm
    · exact hms.2 m (by rw [hrightEq]; exact List.mem_append_left _ hm)
  have hwindow : ShufflePlayW B (post ++ γ) mid := ShufflePlayW_append hpostPlay hγplay
  have hfound : ∃ σ : Suit, c.twin ∈ B.found σ :=
    htwin u v ρ F left right c d b pre post tail heq hsk A' B hpre hstep
  have hnobase : ∀ x : Card, Move.tabToTab x (Sum.inr c) ∉ post ++ γ :=
    not_base_of_twin_found hBwf hwindow hnopullWindow hfound
  exact not_mountainSplit_of_window heq hsk hms hrightEq hfirst hnoslide hnobase

/-! ## §7. Both slide clauses are *necessary* for the bubbling method

`R12.no_slide_self_at` (`Orig2/Fork/Class/ForkReadBracket.lean:766`) shows that a slide
**headed by** `c` can never follow `raise c`, so no bubble certificate can open
with it.  The dual fact is the "lands on `c`" clause: after `raise c` the card
`c` is on the foundation, so it tops no pile and the slide onto it is illegal.
Both clauses are therefore irreducible for this method. -/

/-- **NO SLIDE ONTO `c` CAN FOLLOW `raise c`.**  After the raise, `c` is
founded and hence tops no pile, so `canPlace · (inr c)` is `false`. -/
theorem no_base_slide_after_raise {Q : State} {c x : Card} {b : Base}
    (hQwf : Q.WF) :
    ¬ ∃ e, ShufflePlayW Q [Move.tabToFound c, Move.tabToTab x (Sum.inr c)] e := by
  rintro ⟨e, h⟩
  obtain ⟨s1, hrevR, hstepR, hrest⟩ := Bubble.walk_cons_inv h
  obtain ⟨e', hrevS, hstepS, -⟩ := Bubble.walk_cons_inv hrest
  obtain ⟨hnz, a, hpa, hseat⟩ := Bridge.canRaise_of_reversible_raise hQwf hrevR
  have hsp : Q.step (Move.tabToFound c) = some (raiseSt Q c a) := by
    rw [step_tabToFound_splice hnz hpa]
    rfl
  have hs1 : s1 = raiseSt Q c a := Option.some.inj (hstepR.symm.trans hsp)
  subst hs1
  have hwf1 : (raiseSt Q c a).WF := step_wf hQwf hsp
  have hcfound : c ∈ (raiseSt Q c a).found c.suit := by
    rw [raiseSt_found_apply, ite_eq_left rfl]
    exact List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl))
  have hcnot : ∀ a' : Anchor, c ∉ ((raiseSt Q c a).piles a').faceUp :=
    fun a' => ((mem_found_unique hwf1 hcfound).1 a').2
  have htopnone : (raiseSt Q c a).pileOfTop c = none := by
    cases hpt : (raiseSt Q c a).pileOfTop c with
    | none => rfl
    | some k =>
        exfalso
        have htop : ((raiseSt Q c a).piles k).top = some c :=
          (pileOfTop_eq_some_iff hwf1).mp hpt
        exact hcnot k (lastOf_mem htop)
  have hcan : (raiseSt Q c a).canPlace x (Sum.inr c) = false := by
    rw [canPlace_inr_eq, htopnone]
  cases hph : (raiseSt Q c a).pileHolding x with
  | none =>
      rw [show State.step (raiseSt Q c a) (Move.tabToTab x (Sum.inr c)) = none by
        simp only [State.step, hph]] at hstepS
      exact absurd hstepS (by simp)
  | some a' =>
      rw [show State.step (raiseSt Q c a) (Move.tabToTab x (Sum.inr c)) = none by
        simp only [State.step, hph]
        rw [hcan]
        simp] at hstepS
      exact absurd hstepS (by simp)

/-! ## §8. Cross-check: the residual is the campaign's `NoSelfSlide` datum

In the empty-tail twin regime (`post = []`, `d = c.twin`) the window of this
card is `raise d :: γ'` with `γ'` the campaign's `EmptyTail` window.  The head
clause is *exactly* `SlideFwd.EmptyTailNoSelfSlide`, and the base clause is
what `emptyTail_window_soft` derives from `EmptyTail.twin_no_coverSlide`
(`ReadSafeNoSelfHead` on a slide is the clause "does not land on `c`").  So
`EqualRungInteriorSlideFree` is not a new obligation: it is the campaign's own
named residual, read at the equal-rung split. -/

/-- **THE EMPTY-TAIL TWIN REGIME DISCHARGES THIS CARD'S RESIDUAL FROM
`SlideFwd.EmptyTailNoSelfSlide`.** -/
theorem slideFree_of_emptyTail_noSelfSlide
    (hns : SlideFwd.EmptyTailNoSelfSlide)
    {u v : State} {ρ : List Move} {F : State} {left right : List Move}
    {c d : Card} {b : Base} {pre post tail : List Move}
    (hs : SplitKit.SplitHyp u v ρ F left right c d b pre post tail)
    (hms : MountainKit.MountainSplit left right)
    (hempty : post = [])
    (htwin : d = c.twin) :
    ∃ (γ β : List Move),
      right = γ ++ Move.tabToFound c :: β ∧
      (∀ q ∈ γ, q ≠ Move.tabToFound c) ∧
      SlideFwd.NoSlideOf c (post ++ γ) ∧
      (∀ x : Card, Move.tabToTab x (Sum.inr c) ∉ post ++ γ) := by
  have hsk := hs
  have hrightShape : right = Move.tabToFound d :: tail :=
    (show SplitKit.SplitHyp u v ρ F left right c d b pre post tail from hsk).2.2.2.2.2.2.2.2.2.2.2
  obtain ⟨γ', β', htail, hfirst', hread⟩ :=
    SlideFwd.emptyTail_window_soft hsk hempty hms htwin
  have hdc : d ≠ c := fun h => SplitKit.card_twin_ne c (htwin ▸ h)
  have hrdc : Move.tabToFound d ≠ Move.tabToFound c :=
    fun h => hdc (Move.tabToFound.inj h)
  refine ⟨Move.tabToFound d :: γ', β', ?_, ?_, ?_, ?_⟩
  · rw [hrightShape, htail]
    simp only [List.cons_append]
  · intro q hq
    rcases List.mem_cons.mp hq with rfl | hq'
    · exact hrdc
    · exact hfirst' q hq'
  · intro w bb hmem
    rw [hempty] at hmem
    simp only [List.nil_append] at hmem
    rcases List.mem_cons.mp hmem with hhead | hmem'
    · exact absurd hhead (by simp)
    · exact (hns u v ρ F left right c d b pre post tail γ' β' hsk hempty htail hfirst')
        w bb hmem'
  · intro x hmem
    rw [hempty] at hmem
    simp only [List.nil_append] at hmem
    rcases List.mem_cons.mp hmem with hhead | hmem'
    · exact absurd hhead (by simp)
    · exact (hread (Move.tabToTab x (Sum.inr c))
        (List.mem_cons_of_mem _ hmem')) rfl

end EqSplit

#print axioms EqSplit.split_pull_data
#print axioms EqSplit.first_raise_split
#print axioms EqSplit.rungAt_F_eq_card_rank
#print axioms EqSplit.no_csuit_raise_in_window
#print axioms EqSplit.interior_readSafe
#print axioms EqSplit.not_mountainSplit_of_window
#print axioms EqSplit.EqualRungInteriorSlideFree
#print axioms EqSplit.noEqualRungMountainSplit_of_slideFree
#print axioms EqSplit.mateRaiseFree_iff_differing_of_slideFree
#print axioms EqSplit.equalRungMateRaiseFree_of_slideFree
#print axioms EqSplit.not_mountainSplit_of_window_noSlide
#print axioms EqSplit.not_mountainSplit_of_post_nil_of_head
#print axioms EqSplit.not_base_of_twin_found
#print axioms EqSplit.EqualRungInteriorHeadFree
#print axioms EqSplit.noEqualRungMountainSplit_of_headFree_of_twinFound
#print axioms EqSplit.no_base_slide_after_raise
#print axioms EqSplit.slideFree_of_emptyTail_noSelfSlide
