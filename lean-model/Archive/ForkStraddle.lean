
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-!
# Temp/Strad — the straddling bracket reduced to ONE bad letter

READ-ONLY scratch card (`Temp/`).  No source file is modified; nothing is
committed.  Zero `sorry`, zero `Classical.choice`, no `native_decide`.

## What this card proves

The pin lane (`Orig2/Fork/Split/ForkPinRight.lean`) closes the pin except for the
`PrePullPair pre d` disjunct: `d` is the card of a pull in the split's prefix,
or its twin.  The matching raise is the **first letter of the right leg**, so
between the pull and the raise stands

```text
beta ++ pull c b :: post          ("the interior")
```

which is **raise-free** (`MountainSplit` says the left leg has no raise, `post`
is free) and consists of free letters and pulls only.

* §1 — the bad-letter algebra: after `d.suit`-silence the only free-or-pull
  letters that are not `R12.ReadOK d` are (a) a slide headed by `d`, (b) a
  letter landing on `d`.  `BadLetter` names them.
* §2 — the straddle is packaged as a bracket `pull d ... interior ... raise d`.
* §3 — the interior is `d.suit`-silent (`StradKit.noSigma_interior`), by the
  rung drop at the pull of `d` and the `nextUp d` at the bottom.
* §4 — **the reduction**: if no interior letter is a bad letter, the interior is
  fully `ReadOK d`, and `Mate.splitHyp_not_readBracket` deletes the bracket —
  contradicting shortestness.  **Moreover the self-slide shape is dead**
  (`straddle_no_landing_false`): with no landing letter, either the interior is
  read-safe (`NonforkKit.bracket_delete_gen`) or the last self-slide pairs with
  the raise's net-zero core (`NoSelfKit.selfSlide_shortens`).  So only the
  **landing** shape survives.
* §5 — `StraddleResidual` (bad letters) and `LandingResidual` (landing letters
  only) are each *equivalent* to `NoStraddlingBracket` (the brief's target), so
  the reduction loses nothing.  The pin: once self-straddles are gone,
  `PrePullPair pre d` collapses to the **twin** form `pull d.twin` in `pre`
  (`raise_eq_twin_or_twinPull`), so the pin follows from `NoTwinPullOfRaise`
  plus the block.
* §6 — a kernel witness that the landing letters are REAL: `ForkExistRefute`'s
  4-letter loop is a same-card bracket whose interior contains a slide landing
  on the bracket card, and the closing raise is still legal.  So the brief's
  "nothing lands on `z`, else `raise z` is illegal at the end" is FALSE; the
  landing letter is removed by a later slide, not by a raise.
-/

namespace StradKit

open SplitKit

/-! ## §0. A length helper -/

/-- Extending the same prefix and head preserves a strict length gap. -/
theorem length_lt_of_suffix_lt {α r R : List Move} {m : Move}
    (hlen : r.length < R.length) :
    (α ++ m :: r).length < (α ++ m :: R).length := by
  simp only [List.length_append, List.length_cons]
  omega

/-! ## §1. The bad-letter shapes -/

/-- After `z.suit`-silence, the only ways a free-or-pull letter can fail
`R12.ReadOK z` are: a slide headed by `z`, or any slide/pull landing on `z`. -/
def BadLetter (z : Card) : Move → Prop
  | Move.tabToTab x b => x = z ∨ b = Sum.inr z
  | Move.foundToTab x b => b = Sum.inr z
  | _ => False

/-- **BAD LETTERS ARE EXACTLY THE NON-`ReadOK` FREE-OR-PULL LETTERS** once the
letter is `z.suit`-silent. -/
theorem badLetter_of_not_readOK {z : Card} {q : Move}
    (hfp : LandKit.FreeOrPull q)
    (hns : ThirdLive.NoSigmaLetter z.suit q)
    (h : ¬ R12.ReadOK z q) : BadLetter z q := by
  rcases hfp with hfree | ⟨x, b, rfl⟩
  · rcases hfree with rfl | ⟨x, b, rfl⟩
    · exact absurd trivial h
    · show x = z ∨ b = Sum.inr z
      by_cases hx : x = z
      · exact Or.inl hx
      · by_cases hb : b = Sum.inr z
        · exact Or.inr hb
        · exact absurd ⟨hx, hb⟩ h
  · show b = Sum.inr z
    by_cases hb : b = Sum.inr z
    · exact hb
    · exact absurd ⟨hns.1 x b rfl, hb⟩ h

/-- A bad letter is never `ReadOK`. -/
theorem not_readOK_of_badLetter {z : Card} {q : Move}
    (h : BadLetter z q) : ¬ R12.ReadOK z q := by
  cases q with
  | draw => exact absurd h (by simp [BadLetter])
  | wasteToFound c => exact absurd h (by simp [BadLetter])
  | wasteToTab c b => exact absurd h (by simp [BadLetter])
  | tabToFound c => exact absurd h (by simp [BadLetter])
  | foundToTab x b =>
      intro hr
      exact hr.2 h
  | tabToTab x b =>
      intro hr
      rcases h with h | h
      · exact hr.1 h
      · exact hr.2 h

/-- A pull letter is bad iff it lands on `z`. -/
theorem badLetter_pull_iff {z x : Card} {b : Base} :
    BadLetter z (Move.foundToTab x b) ↔ b = Sum.inr z := Iff.rfl

/-- A slide letter is bad iff it is headed by `z` or lands on `z`. -/
theorem badLetter_slide_iff {z x : Card} {b : Base} :
    BadLetter z (Move.tabToTab x b) ↔ (x = z ∨ b = Sum.inr z) := Iff.rfl

/-- The **landing** clause: the letter places a card on top of `z`. -/
def LandsOn (z : Card) : Move → Prop
  | Move.tabToTab x b => b = Sum.inr z
  | Move.foundToTab x b => b = Sum.inr z
  | _ => False

/-- The **self-head** clause: the letter is a slide headed by `z`. -/
def SelfSlideHead (z : Card) : Move → Prop
  | Move.tabToTab x _ => x = z
  | _ => False

/-- The bad letter is exactly a landing letter or a self-headed slide. -/
theorem badLetter_iff_landsOn_or_selfHead {z : Card} {q : Move} :
    BadLetter z q ↔ (LandsOn z q ∨ SelfSlideHead z q) := by
  cases q <;> simp [BadLetter, LandsOn, SelfSlideHead, or_comm]

/-! ## §2. Packaging a straddling self-bracket -/

/-- **THE STRADDLE PACKAGE.**  A pull of `d` inside `pre` and the turn's raise
`raise d` at the bottom form the bracket

```text
alpha ; pull d bz ; (beta ; pull c b ; post) ; raise d ; tail
```

with the *interior* `beta ++ pull c b :: post` entirely inside the left leg
(hence raise-free under a mountain split). -/
theorem straddle_package
    {u v : State} {ρ : List Move} {F : State} {left right : List Move}
    {c d : Card} {b : Base} {pre post tail : List Move}
    (hs : SplitKit.SplitHyp u v ρ F left right c d b pre post tail)
    {α β : List Move} {bz : Base}
    (hpre : pre = α ++ Move.foundToTab d bz :: β) :
    ∃ P Q : State,
      ρ = α ++ Move.foundToTab d bz ::
          ((β ++ Move.foundToTab c b :: post) ++ Move.tabToFound d :: tail) ∧
      ShufflePlayW u α P ∧
      reversibleAtW P (Move.foundToTab d bz) ∧
      State.step P (Move.foundToTab d bz) = some Q ∧
      ShufflePlayW Q ((β ++ Move.foundToTab c b :: post) ++
        Move.tabToFound d :: tail) v := by
  obtain ⟨huwf, -, -, hplay, -, -, hρ, hleft, -, hshape, hfree, hright⟩ := hs
  have hρ0 : ρ = (pre ++ Move.foundToTab c b :: post) ++
      (Move.tabToFound d :: tail) := by
    rw [hρ, hshape, hright]
  have hρ' : ρ = α ++ Move.foundToTab d bz ::
      ((β ++ Move.foundToTab c b :: post) ++ Move.tabToFound d :: tail) := by
    rw [hρ0, hpre]
    simp only [List.append_assoc, List.cons_append]
  obtain ⟨P, hα, hrest⟩ :=
    ValleyElim.ShufflePlayW_split hplay α _ hρ'
  obtain ⟨Q, hrev, hstep, hplayQ⟩ := Bubble.walk_cons_inv hrest
  exact ⟨P, Q, hρ', hα, hrev, hstep, hplayQ⟩

/-! ## §3. The interior is `d.suit`-silent -/

/-- **THE INTERIOR ALPHABET.**  Every letter between the pull of `d` and the
turn's raise is free or a pull: the tail `β` of `pre` sits in the raise-free
left leg, `pull c b` is a pull, and `post` is free. -/
theorem interior_freeOrPull
    {u v : State} {ρ : List Move} {F : State} {left right : List Move}
    {c d : Card} {b : Base} {pre post tail : List Move}
    (hs : SplitKit.SplitHyp u v ρ F left right c d b pre post tail)
    (hraiseFree : ∀ m ∈ left, ¬ Bubble.IsRaise m)
    {α β : List Move} {bz : Base}
    (hpre : pre = α ++ Move.foundToTab d bz :: β) :
    ∀ m ∈ (β ++ Move.foundToTab c b :: post), LandKit.FreeOrPull m := by
  obtain ⟨-, -, -, -, -, -, -, hleft, -, hshape, hfree, -⟩ := hs
  intro m hm
  rcases List.mem_append.mp hm with hmβ | hmrest
  · have hmpre : m ∈ pre := by
      rw [hpre]
      exact List.mem_append_right _ (List.mem_cons_of_mem _ hmβ)
    have hmleft : m ∈ left := by
      rw [hshape]
      exact List.mem_append_left _ hmpre
    rcases MountainKit.free_or_pull_or_raise_of_play hleft m hmleft with
      hf | hp | hr
    · exact Or.inl hf
    · exact Or.inr hp
    · exact absurd hr (hraiseFree m hmleft)
  · rcases List.mem_cons.mp hmrest with rfl | hmp
    · exact Or.inr ⟨c, b, rfl⟩
    · exact Or.inl (hfree m hmp)

/-- **THE INTERIOR SPEAKS NO `d.suit`.**  After the pull of `d`, the suit's rung
sits at `d.rank.toIdx`.  The interior is raise-free, so the rung is
non-increasing; at the bottom `nextUp d` forces it back to `d.rank.toIdx`.
Hence no pull and no raise of `d.suit` can occur inside. -/
theorem noSigma_interior
    {u v : State} {ρ : List Move} {F : State} {left right : List Move}
    {c d : Card} {b : Base} {pre post tail : List Move}
    (hs : SplitKit.SplitHyp u v ρ F left right c d b pre post tail)
    (hraiseFree : ∀ m ∈ left, ¬ Bubble.IsRaise m)
    {α β : List Move} {bz : Base} {P Q : State}
    (hpre : pre = α ++ Move.foundToTab d bz :: β)
    (hα : ShufflePlayW u α P)
    (hstep : State.step P (Move.foundToTab d bz) = some Q)
    (hplayQ : ShufflePlayW Q ((β ++ Move.foundToTab c b :: post) ++
        Move.tabToFound d :: tail) v) :
    ∀ m ∈ (β ++ Move.foundToTab c b :: post),
      ThirdLive.NoSigmaLetter d.suit m := by
  have hsk := hs
  obtain ⟨huwf, -, -, -, -, -, -, hleft, -, hshape, hfree, -⟩ := hs
  have hPwf : P.WF := SatDifferCensus.ShufflePlayW.wf_end hα huwf
  obtain ⟨X, hγplay, hrest⟩ :=
    ValleyElim.ShufflePlayW_split hplayQ (β ++ Move.foundToTab c b :: post)
      (Move.tabToFound d :: tail) rfl
  have hXwf : X.WF := SatDifferCensus.ShufflePlayW.wf_end hγplay (step_wf hPwf hstep)
  obtain ⟨-, hrevR, -, -⟩ := Bubble.walk_cons_inv hrest
  have hlive : CanRaiseS X d :=
    CanRaiseS.now d (Bridge.canRaise_of_reversible_raise hXwf hrevR)
  have hall := interior_freeOrPull hsk hraiseFree hpre
  exact Mate.noSigma_after_self_pull_of_live hPwf hstep hγplay hall hlive

/-! ## §4. The reduction: a straddling self-bracket carries a bad letter -/

/-- **THE REDUCTION.**  At a `SplitHyp` with a mountain split, a pull of `d`
inside `pre` cannot have a fully `ReadOK d` interior: that would be a read-safe
same-card bracket, which shortestness deletes (`Mate.splitHyp_not_readBracket`).
Hence some interior letter is bad. -/
theorem straddle_not_all_readOK
    {u v : State} {ρ : List Move} {F : State} {left right : List Move}
    {c d : Card} {b : Base} {pre post tail : List Move}
    (hs : SplitKit.SplitHyp u v ρ F left right c d b pre post tail)
    (hraiseFree : ∀ m ∈ left, ¬ Bubble.IsRaise m)
    {α β : List Move} {bz : Base}
    (hpre : pre = α ++ Move.foundToTab d bz :: β)
    (hnobad : ∀ q ∈ (β ++ Move.foundToTab c b :: post), ¬ BadLetter d q) :
    False := by
  obtain ⟨P, Q, hρ, hα, hrev, hstep, hplayQ⟩ := straddle_package hs hpre
  have hall := interior_freeOrPull hs hraiseFree hpre
  have hns := noSigma_interior hs hraiseFree hpre hα hstep hplayQ
  have hread : ∀ q ∈ (β ++ Move.foundToTab c b :: post), R12.ReadOK d q := by
    intro q hq
    by_cases hr : R12.ReadOK d q
    · exact hr
    · exact absurd (badLetter_of_not_readOK (hall q hq) (hns q hq) hr) (hnobad q hq)
  have hρ2 : ρ = (α ++ Move.foundToTab d bz ::
      (β ++ Move.foundToTab c b :: post)) ++ Move.tabToFound d :: tail := by
    simpa only [List.append_assoc, List.cons_append] using hρ
  exact Mate.splitHyp_not_readBracket (hs := hs) (hρ := hρ2)
    (hα := hα) (hstep := hstep) (hread := hread)

/-- **THE SELF-SLIDE SHAPE IS NOT THE OBSTRUCTION.**  If the interior never lands
on `d`, then either it is fully read-safe (deleted by `bracket_delete_gen`) or it
contains a slide headed by `d`, which `NoSelfKit.selfSlide_shortens` deletes
outright.  Either way a strictly shorter play exists. -/
theorem straddle_no_landing_false
    {u v : State} {ρ : List Move} {F : State} {left right : List Move}
    {c d : Card} {b : Base} {pre post tail : List Move}
    (hs : SplitKit.SplitHyp u v ρ F left right c d b pre post tail)
    (hraiseFree : ∀ m ∈ left, ¬ Bubble.IsRaise m)
    {α β : List Move} {bz : Base}
    (hpre : pre = α ++ Move.foundToTab d bz :: β)
    (hnoland : ∀ q ∈ (β ++ Move.foundToTab c b :: post), ¬ LandsOn d q) :
    False := by
  have hsk := hs
  obtain ⟨huwf, -, -, hplay, -, hmin, -, -, -, -, -, -⟩ := hs
  obtain ⟨P, Q, hρ, hα, hrev, hstep, hplayQ⟩ := straddle_package hsk hpre
  have hPwf : P.WF := SatDifferCensus.ShufflePlayW.wf_end hα huwf
  have hQwf : Q.WF := step_wf hPwf hstep
  have hcanQ : CanRaise Q d := ValleyStep.pull_card_canRaise hPwf hstep
  have hns := noSigma_interior hsk hraiseFree hpre hα hstep hplayQ
  have hsoft : ∀ q ∈ (β ++ Move.foundToTab c b :: post),
      SlideFwd.ReadSafeNoSelfHead d q := by
    intro q hq
    have hq' := hns q hq
    cases q with
    | draw => exact trivial
    | wasteToFound x => exact trivial
    | wasteToTab x bb => exact trivial
    | tabToFound w => exact hq'.2 w rfl
    | foundToTab x bb =>
        exact ⟨hq'.1 x bb rfl, fun hb => hnoland _ hq hb⟩
    | tabToTab x bb => exact fun hb => hnoland _ hq hb
  rcases NoSelfKit.noSlideOf_or_last d (β ++ Move.foundToTab c b :: post) with
    hnsli | ⟨a, bs, δ, hγeq, hδ⟩
  · -- no self-slide: the whole interior is read-safe
    have hread : ∀ q ∈ (β ++ Move.foundToTab c b :: post), SlideFwd.ReadSafe d q := by
      intro q hq
      exact SlideFwd.readSafe_of_noSelfHead (hsoft q hq)
        (fun w bb hqeq => hnsli w bb (hqeq ▸ hq))
    have hsw : NonforkKit.RaiseSwaps Q d (β ++ Move.foundToTab c b :: post) :=
      SlideFwd.raiseSwaps_of_readSafe hQwf hplayQ hcanQ hread
    have hρ2 : ρ = (α ++ Move.foundToTab d bz ::
        (β ++ Move.foundToTab c b :: post)) ++ Move.tabToFound d :: tail := by
      simpa only [List.append_assoc, List.cons_append] using hρ
    obtain ⟨ρ', hρ'play, hlen⟩ :=
      NonforkKit.bracket_delete_gen huwf hplay hρ2 hα hstep hsw
    exact absurd hlen (Nat.not_lt.mpr (hmin ρ' hρ'play))
  · -- a self-slide deletes the pair (net-zero core)
    obtain ⟨ρ', hρ'play, hlen⟩ :=
      NoSelfKit.selfSlide_shortens hQwf hcanQ hplayQ hsoft ⟨a, bs, δ, hγeq, hδ⟩
    have hnew : ShufflePlayW u (α ++ Move.foundToTab d bz :: ρ') v :=
      ShufflePlayW_append hα (Walk.cons hrev hstep hρ'play)
    have hlenR : ρ'.length <
        ((β ++ Move.foundToTab c b :: post) ++ Move.tabToFound d :: tail).length :=
      hlen
    have hcalc := length_lt_of_suffix_lt (α := α) (m := Move.foundToTab d bz)
      (r := ρ')
      (R := (β ++ Move.foundToTab c b :: post) ++ Move.tabToFound d :: tail) hlenR
    have hcalc' : (α ++ Move.foundToTab d bz :: ρ').length < ρ.length := by
      rw [hρ]
      exact hcalc
    exact absurd hcalc' (Nat.not_lt.mpr (hmin _ hnew))

/-! ## §5. The residual, and the pin it gives -/

/-- **`StraddleResidual` — THE NAMED RESIDUAL.**  At every `SplitHyp` whose
left leg is raise-free, no same-card straddling bracket `pull d ... raise d` has
a bad letter in its interior.  By §4 this is *exactly* the missing statement: its
negation is proved (every straddle carries a bad letter), and it implies that
`d` is never itself pulled in `pre`. -/
def StraddleResidual : Prop :=
  ∀ (u v : State) (ρ : List Move) (F : State) (left right : List Move)
    (c d : Card) (b : Base) (pre post tail : List Move),
    SplitKit.SplitHyp u v ρ F left right c d b pre post tail →
    (∀ m ∈ left, ¬ Bubble.IsRaise m) →
    ∀ (bz : Base) (α β : List Move),
      pre = α ++ Move.foundToTab d bz :: β →
      ∀ q ∈ (β ++ Move.foundToTab c b :: post), ¬ BadLetter d q

/-- **THE REDUCTION IS EXACT.**  `StraddleResidual` holds iff the raise card is
never itself the card of a prefix pull — i.e. the residual is not a weakening of
the no-straddle statement, it *is* it, letter for letter. -/
theorem straddleResidual_iff_noSelfPull :
    StraddleResidual ↔
      (∀ (u v : State) (ρ : List Move) (F : State) (left right : List Move)
        (c d : Card) (b : Base) (pre post tail : List Move),
        SplitKit.SplitHyp u v ρ F left right c d b pre post tail →
        (∀ m ∈ left, ¬ Bubble.IsRaise m) →
        ∀ bz : Base, Move.foundToTab d bz ∉ pre) := by
  constructor
  · intro h u v ρ F left right c d b pre post tail hs hrf bz hmem
    obtain ⟨α, β, hpre⟩ := List.mem_iff_append.mp hmem
    exact straddle_not_all_readOK hs hrf hpre
      (h u v ρ F left right c d b pre post tail hs hrf bz α β hpre)
  · intro h u v ρ F left right c d b pre post tail hs hrf bz α β hpre q hq hb
    exact absurd (by rw [hpre]; exact List.mem_append_right _ (List.mem_cons_self ..))
      (h u v ρ F left right c d b pre post tail hs hrf bz)

/-- **NO STRADDLING SELF-BRACKET AT A MOUNTAIN SPLIT.** -/
theorem no_self_pull_in_pre (h : StraddleResidual) :
    ∀ (u v : State) (ρ : List Move) (F : State) (left right : List Move)
      (c d : Card) (b : Base) (pre post tail : List Move),
      SplitKit.SplitHyp u v ρ F left right c d b pre post tail →
      (∀ m ∈ left, ¬ Bubble.IsRaise m) →
      ∀ bz : Base, Move.foundToTab d bz ∉ pre :=
  straddleResidual_iff_noSelfPull.mp h

/-- **`NoStraddlingBracket` — THE BRIEF'S TARGET.**  At every `SplitHyp` whose
left leg is raise-free, the raise card is not the card of a prefix pull. -/
def NoStraddlingBracket : Prop :=
  ∀ (u v : State) (ρ : List Move) (F : State) (left right : List Move)
    (c d : Card) (b : Base) (pre post tail : List Move),
    SplitKit.SplitHyp u v ρ F left right c d b pre post tail →
    (∀ m ∈ left, ¬ Bubble.IsRaise m) →
    ∀ bz : Base, Move.foundToTab d bz ∉ pre

/-- **`NoStraddlingBracket` IS EXACTLY `StraddleResidual`.** -/
theorem noStraddlingBracket_iff_straddleResidual :
    NoStraddlingBracket ↔ StraddleResidual :=
  straddleResidual_iff_noSelfPull.symm

/-- **`LandingResidual` — THE SHARPEST FORM: only landing letters survive.**
The self-slide shape is *proved* impossible (`straddle_no_landing_false`), so the
whole missing statement is that the interior of a straddling self-bracket never
lands a card on the raise card. -/
def LandingResidual : Prop :=
  ∀ (u v : State) (ρ : List Move) (F : State) (left right : List Move)
    (c d : Card) (b : Base) (pre post tail : List Move),
    SplitKit.SplitHyp u v ρ F left right c d b pre post tail →
    (∀ m ∈ left, ¬ Bubble.IsRaise m) →
    ∀ (bz : Base) (α β : List Move),
      pre = α ++ Move.foundToTab d bz :: β →
      ∀ q ∈ (β ++ Move.foundToTab c b :: post), ¬ LandsOn d q

/-- **`LandingResidual` KILLS EVERY STRADDLING SELF-BRACKET.** -/
theorem noStraddlingBracket_of_landingResidual (h : LandingResidual) :
    NoStraddlingBracket := by
  intro u v ρ F left right c d b pre post tail hs hrf bz hmem
  obtain ⟨α, β, hpre⟩ := List.mem_iff_append.mp hmem
  exact straddle_no_landing_false hs hrf hpre
    (h u v ρ F left right c d b pre post tail hs hrf bz α β hpre)

/-- **THE LANDING RESIDUAL IS NOT A WEAKENING.**  Any no-straddle statement
entails it vacuously. -/
theorem landingResidual_of_noStraddlingBracket (h : NoStraddlingBracket) :
    LandingResidual := by
  intro u v ρ F left right c d b pre post tail hs hrf bz α β hpre q hq hland
  exact h u v ρ F left right c d b pre post tail hs hrf bz
    (by rw [hpre]; exact List.mem_append_right _ (List.mem_cons_self ..))

/-- **THE EXACT REDUCTION.**  The landing residual, the bad-letter residual and
the no-self-straddle statement are the SAME statement. -/
theorem landingResidual_iff_noStraddlingBracket :
    LandingResidual ↔ NoStraddlingBracket :=
  ⟨noStraddlingBracket_of_landingResidual, landingResidual_of_noStraddlingBracket⟩

/-- **THE PIN'S CARD DICHOTOMY, SHARPENED.**  `PinRight.raise_eq_twin_or_prePull`
leaves `d` a prefix-pull card or its twin.  The first alternative is now dead
(`no_self_pull_in_pre`), so the only surviving way for the pin to fail is the
**twin pull** `pull d.twin` in `pre`. -/
theorem raise_eq_twin_or_twinPull
    {u v : State} {ρ : List Move} {F : State} {left right : List Move}
    {c d : Card} {b : Base} {pre post tail : List Move}
    (hs : SplitKit.SplitHyp u v ρ F left right c d b pre post tail)
    (hraiseFree : ∀ m ∈ left, ¬ Bubble.IsRaise m)
    (hblock : ¬ CanRaise F c)
    (hself : ∀ bz : Base, Move.foundToTab d bz ∉ pre) :
    d = c.twin ∨ ∃ bz : Base, Move.foundToTab d.twin bz ∈ pre := by
  rcases PinRight.raise_eq_twin_or_prePull hs hraiseFree hblock with hd | hbad
  · exact Or.inl hd
  · obtain ⟨z, bz, hmem, hdz⟩ := hbad
    rcases hdz with hdz | hdz
    · exact absurd (show Move.foundToTab d bz ∈ pre by rw [hdz]; exact hmem) (hself bz)
    · refine Or.inr ⟨bz, ?_⟩
      have hz : z = d.twin := by rw [hdz, card_twin_twin]
      rwa [hz] at hmem

/-- **`NoTwinPullOfRaise` — THE FINAL NAMED RESIDUAL.**  At every split whose
left leg is raise-free, the twin of the raise card is not the card of a pull in
the prefix.  This is the whole of `PinRight.NoPrePullRaise` after §4. -/
def NoTwinPullOfRaise : Prop :=
  ∀ (u v : State) (ρ : List Move) (F : State) (left right : List Move)
    (c d : Card) (b : Base) (pre post tail : List Move),
    SplitKit.SplitHyp u v ρ F left right c d b pre post tail →
    (∀ m ∈ left, ¬ Bubble.IsRaise m) →
    ∀ bz : Base, Move.foundToTab d.twin bz ∉ pre

/-- **THE PIN FROM THE TWIN RESIDUAL.** -/
theorem pin_of_straddle_twin
    (hst : StraddleResidual) (hres : NoTwinPullOfRaise)
    {u v : State} {ρ : List Move} {F : State} {left right : List Move}
    {c d : Card} {b : Base} {pre post tail : List Move}
    (hs : SplitKit.SplitHyp u v ρ F left right c d b pre post tail)
    (hraiseFree : ∀ m ∈ left, ¬ Bubble.IsRaise m)
    (hblock : ¬ CanRaise F c) :
    rungAt F c.twin.suit = c.rank.toIdx := by
  rcases raise_eq_twin_or_twinPull hs hraiseFree hblock
    (fun bz => no_self_pull_in_pre hst u v ρ F left right c d b pre post tail
      hs hraiseFree bz) with hd | ⟨bz, hmem⟩
  · exact PinRight.pin_of_raise_eq_twin_rung hs hd
  · exact absurd hmem (hres u v ρ F left right c d b pre post tail hs hraiseFree bz)

/-- **`NoPrePullRaise` FROM THE TWO NAMED RESIDUALS.**  `PinRight`'s residual is
`StraddleResidual` (no bad letter in a self-bracket) plus `NoTwinPullOfRaise`
(no twin pull) — the exact split of the bracket into its *same-card* and
*cross-twin* halves. -/
theorem noPrePullRaise_of_straddle_twin
    (hst : StraddleResidual) (hres : NoTwinPullOfRaise) :
    PinRight.NoPrePullRaise := by
  intro u v ρ F left right c d b pre post tail hs hraiseFree hpair
  obtain ⟨z, bz, hmem, hdz⟩ := hpair
  rcases hdz with hdz | hdz
  · exact no_self_pull_in_pre hst u v ρ F left right c d b pre post tail
      hs hraiseFree bz (by rw [hdz]; exact hmem)
  · refine hres u v ρ F left right c d b pre post tail hs hraiseFree bz ?_
    have hz : z = d.twin := by rw [hdz, card_twin_twin]
    rw [← hz]
    exact hmem

/-- **THE CAMPAIGN PIN, FROM THE TWIN RESIDUAL.**  With the mountain datum
supplying raise-freeness of the left leg. -/
theorem splitTwinRungPin_of_straddle_twin
    (hst : StraddleResidual) (hres : NoTwinPullOfRaise)
    (hms : ∀ (u v : State) (ρ : List Move) (F : State) (left right : List Move)
      (c d : Card) (b : Base) (pre post tail : List Move),
      SplitKit.SplitHyp u v ρ F left right c d b pre post tail →
      MountainKit.MountainSplit left right)
    (hb : SplitKit.SplitBlock) : TwinKit.SplitTwinRungPin := by
  intro u v ρ F left right c d b pre post tail h
  exact TwinKit.nextUp_true_iff.mpr
    (pin_of_straddle_twin hst hres h
      (hms u v ρ F left right c d b pre post tail h).1
      (hb u v ρ F left right c d b pre post tail h))

/-- **`NoPrePullRaise` FROM THE LANDING RESIDUAL + THE TWIN RESIDUAL.** -/
theorem noPrePullRaise_of_landing_twin
    (hland : LandingResidual) (hres : NoTwinPullOfRaise) :
    PinRight.NoPrePullRaise :=
  noPrePullRaise_of_straddle_twin
    (noStraddlingBracket_iff_straddleResidual.mp
      (landingResidual_iff_noStraddlingBracket.mp hland)) hres

/-- **THE CAMPAIGN PIN FROM THE TWO RESIDUALS** (landing letters + twin pull). -/
theorem splitTwinRungPin_of_landing_twin
    (hland : LandingResidual) (hres : NoTwinPullOfRaise)
    (hms : ∀ (u v : State) (ρ : List Move) (F : State) (left right : List Move)
      (c d : Card) (b : Base) (pre post tail : List Move),
      SplitKit.SplitHyp u v ρ F left right c d b pre post tail →
      MountainKit.MountainSplit left right)
    (hb : SplitKit.SplitBlock) : TwinKit.SplitTwinRungPin :=
  splitTwinRungPin_of_straddle_twin
    (noStraddlingBracket_iff_straddleResidual.mp
      (landingResidual_iff_noStraddlingBracket.mp hland)) hres hms hb

/-- **THE CAMPAIGN'S ONE-SIDED CLAUSE (`SplitTwinRungGe`) FROM THE TWO
RESIDUALS.**  Exactly `PinRight.splitTwinRungGe_of_freePreSplit`'s argument, with
`FreePreSplit` replaced by the landing + twin residuals. -/
theorem splitTwinRungGe_of_landing_twin
    (hland : LandingResidual) (hres : NoTwinPullOfRaise)
    (hms : ∀ (u v : State) (ρ : List Move) (F : State) (left right : List Move)
      (c d : Card) (b : Base) (pre post tail : List Move),
      SplitKit.SplitHyp u v ρ F left right c d b pre post tail →
      MountainKit.MountainSplit left right)
    (hb : SplitKit.SplitBlock) : PairRungKit.SplitTwinRungGe := by
  intro u v ρ F left right c d b pre post tail h
  have hpin := pin_of_straddle_twin
    (noStraddlingBracket_iff_straddleResidual.mp
      (landingResidual_iff_noStraddlingBracket.mp hland)) hres h
    (hms u v ρ F left right c d b pre post tail h).1
    (hb u v ρ F left right c d b pre post tail h)
  obtain ⟨-, hSc, -, -⟩ := SplitKit.splitHyp_green h
  have hsig : rungAt F c.suit = c.rank.toIdx := canRaiseS_rung hSc
  omega

/-! ## §6. The bad letters are REAL: `ForkExistRefute`'s bracket

The brief's "crux" is that *nothing lands on `z`*, because otherwise `raise z`
would be illegal at the end.  This is **false**: `ForkExistRefute`'s four-letter
play is a same-card bracket `pull 5H ; slide 4C -> 5H ; slide 4C -> 5D ;
raise 5H` whose first interior letter lands on `5H`; the landing buries `5H`,
and the later slide uncovers it, so the closing raise still fires.  The play is
a loop (`V = u`), hence shortestness (not the landing argument) is what excludes
it -- exactly the reason `StraddleResidual` is needed. -/

/-- The bracket decomposition of `ExistRefute.rho`. -/
theorem existRefute_bracket :
    ExistRefute.rho = ([] : List Move) ++
      Move.foundToTab ExistRefute.H5 (Sum.inr ExistRefute.C6) ::
      ([ExistRefute.mS1, ExistRefute.mS2] ++ Move.tabToFound ExistRefute.H5 :: []) :=
  rfl

/-- The interior's first letter lands on the bracket card. -/
theorem existRefute_badLetter :
    BadLetter ExistRefute.H5 ExistRefute.mS1 :=
  Or.inr rfl

/-- … and is therefore not `ReadOK`. -/
theorem existRefute_not_readOK :
    ¬ R12.ReadOK ExistRefute.H5 ExistRefute.mS1 :=
  not_readOK_of_badLetter existRefute_badLetter

/-- **THE LANDING IS NOT FATAL.**  After the landing (state `S`) the play slides
`4C` off and the closing `raise 5H` fires at `F`. -/
theorem existRefute_landing_not_fatal :
    State.step ExistRefute.B ExistRefute.mS1 = some ExistRefute.S ∧
    State.step ExistRefute.S ExistRefute.mS2 = some ExistRefute.F ∧
    State.step ExistRefute.F ExistRefute.mRaise = some ExistRefute.V :=
  ⟨ExistRefute.step_s1, ExistRefute.step_s2, ExistRefute.step_raise⟩

/-- **THE CLOSING RAISE IS LEGAL AT THE END** — the card that landed on `5H` is
gone by `F`.  (`CanRaise F 5H` is already the reversibility of the raise.) -/
theorem existRefute_raise_legal :
    CanRaise ExistRefute.F ExistRefute.H5 :=
  Bridge.canRaise_of_reversible_raise ExistRefute.F_wf ExistRefute.raise_rev

/-- **… AND THE PLAY IS A LOOP.**  `V = u`, so the empty play is shorter: the
bracket is excluded by minimality, not by its landing letter. -/
theorem existRefute_loop :
    ExistRefute.V = ExistRefute.u ∧
      ∃ ρ' : List Move, ShufflePlayW ExistRefute.u ρ' ExistRefute.V ∧
        ρ'.length < ExistRefute.rho.length :=
  ⟨ExistRefute.V_eq_u, ExistRefute.shorter_play_V⟩

/-! ## §7. Battery -/

#print axioms StradKit.length_lt_of_suffix_lt
#print axioms StradKit.badLetter_of_not_readOK
#print axioms StradKit.not_readOK_of_badLetter
#print axioms StradKit.badLetter_iff_landsOn_or_selfHead
#print axioms StradKit.straddle_package
#print axioms StradKit.interior_freeOrPull
#print axioms StradKit.noSigma_interior
#print axioms StradKit.straddle_not_all_readOK
#print axioms StradKit.straddle_no_landing_false
#print axioms StradKit.straddleResidual_iff_noSelfPull
#print axioms StradKit.noStraddlingBracket_iff_straddleResidual
#print axioms StradKit.noStraddlingBracket_of_landingResidual
#print axioms StradKit.landingResidual_of_noStraddlingBracket
#print axioms StradKit.landingResidual_iff_noStraddlingBracket
#print axioms StradKit.raise_eq_twin_or_twinPull
#print axioms StradKit.pin_of_straddle_twin
#print axioms StradKit.noPrePullRaise_of_straddle_twin
#print axioms StradKit.splitTwinRungPin_of_straddle_twin
#print axioms StradKit.noPrePullRaise_of_landing_twin
#print axioms StradKit.splitTwinRungPin_of_landing_twin
#print axioms StradKit.splitTwinRungGe_of_landing_twin
#print axioms StradKit.existRefute_bracket
#print axioms StradKit.existRefute_badLetter
#print axioms StradKit.existRefute_not_readOK
#print axioms StradKit.existRefute_landing_not_fatal
#print axioms StradKit.existRefute_raise_legal
#print axioms StradKit.existRefute_loop

end StradKit
