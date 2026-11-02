import Orig2.Fork.ForkPinRight
import Orig2.Fork.ForkReadBracket
import Orig2.Fork.ForkNoSelf
import Orig2.Fork.ForkMate
import Orig2.Fork.ForkMountainAccount

/-!
# Orig2/ForkChoiceFree — the choice-free geometry of the straddling bracket

READ-ONLY scratch card (`Temp/`).  No source file is modified; nothing is
committed.  **Zero `sorry`, zero `Classical.choice`, zero `native_decide`,
zero `axiom`**; every row is discharged by `#print axioms` at the tail.

This is the promotable extract of `Temp/Choice_Main.lean` (the classical
variant of the straddle lane).  The audit there showed that the *geometry* was
already choice-free and only the selectors were tainted.  This card goes one
step further: the last-bad-letter selector is restated over a `DecidablePred`,
which — because `R12.ReadOK d` is a decidable predicate on `Move` — makes the
**entire reduction** choice-free, not just the local lemmas.

## Contents

* §1 — the bad-letter algebra, in the constructive lane's vocabulary
  (`BadLetter = LandsOn ∨ SelfSlideHead`).
* §2 — the last bad letter, choice-free (`[DecidablePred P]`).
* §3 — the local deletion machinery: a landing buries the raise card, a
  self-slide is cancelled by `NoSelfKit.raiseSt_slideSt_self`, and **`CanRaise`
  transfers backwards across a reversible self-slide**
  (`canRaise_of_canRaise_after_selfSlide` — the new lemma).
* §4 — the packaging (`straddle_package`, the interior's alphabet and its
  `d.suit`-silence) and the missing `Walk.append`.
* §5 — the residual `LastBadLicensed` and the **choice-free** reduction from it
  to `PinRight.NoPrePullRaise` and `TwinKit.SplitTwinRungPin`.
* §6 — **the two lanes' common statement**: `LandingResidual` (the constructive
  lane's residual) **implies** `LastBadLicensed`, via a licence-persistence
  lemma.  The converse does not hold; see the docstring and `ChoiceFree_Report`.
* §7 — the gadget explaining *why* the backwards transfer is safe.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace ChoiceFree

open ValleyElim

/-! ## §1. The bad letters of a same-card bracket -/

/-- The bad letters for the pending raise of `z`: a slide headed by `z`, or a
letter landing on `z`. -/
def BadLetter (z : Card) : Move → Prop
  | Move.tabToTab x b => x = z ∨ b = Sum.inr z
  | Move.foundToTab x b => b = Sum.inr z
  | _ => False

/-- The **landing** clause: the letter puts a card on `z`.  (Verbatim the
constructive lane's `StradKit.LandsOn`.) -/
def LandsOn (z : Card) : Move → Prop
  | Move.tabToTab x b => b = Sum.inr z
  | Move.foundToTab x b => b = Sum.inr z
  | _ => False

/-- The **self-head** clause: the letter is a slide headed by `z`. -/
def SelfSlideHead (z : Card) : Move → Prop
  | Move.tabToTab x b => x = z
  | _ => False

/-- The bad letter is exactly a landing letter or a self-headed slide. -/
theorem badLetter_iff_landsOn_or_selfHead {z : Card} {q : Move} :
    BadLetter z q ↔ (LandsOn z q ∨ SelfSlideHead z q) := by
  cases q <;> simp [BadLetter, LandsOn, SelfSlideHead, or_comm]

/-- A non-`ReadOK` free-or-pull letter in a `z.suit`-silent window is a bad
letter.  (The `by_cases` here are on `x = z` / `b = inr z`, which are
computably decidable, so the row is choice-free.) -/
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

/-- A landing is a bad letter. -/
theorem badLetter_of_landsOn {z : Card} {q : Move} (h : LandsOn z q) :
    BadLetter z q :=
  (badLetter_iff_landsOn_or_selfHead).mpr (Or.inl h)

/-- A self-slide is a bad letter. -/
theorem badLetter_of_selfSlideHead {z : Card} {q : Move}
    (h : SelfSlideHead z q) : BadLetter z q :=
  (badLetter_iff_landsOn_or_selfHead).mpr (Or.inr h)

/-! ## §2. The last bad letter, choice-free

The classical card used a `by_cases` on `∃ x ∈ t, ¬P x` for an *arbitrary*
`P`, which is what dragged `Classical.choice` in.  Over a `DecidablePred` the
same induction is choice-free — and `R12.ReadOK d` is decidable, so the
reduction loses nothing. -/

/-- **THE LAST BAD LETTER (choice-free).**  `l = A ++ x :: B`, `x` bad, every
letter of `B` good. -/
theorem exists_last_dec {α : Type} [DecidableEq α] {l : List α} {P : α → Prop}
    [DecidablePred P]
    (h : ∃ x ∈ l, ¬ P x) :
    ∃ A x B, l = A ++ x :: B ∧ ¬ P x ∧ ∀ y ∈ B, P y := by
  induction l with
  | nil =>
      obtain ⟨x, hx, -⟩ := h
      exact absurd hx List.not_mem_nil
  | cons a t ih =>
      by_cases ht : ∃ x ∈ t, ¬ P x
      · obtain ⟨A, x, B, hAB, hx, hB⟩ := ih ht
        exact ⟨a :: A, x, B, by rw [hAB]; rfl, hx, hB⟩
      · by_cases ha : P a
        · obtain ⟨x, hx, hnx⟩ := h
          rcases List.mem_cons.mp hx with rfl | hx
          · exact absurd ha hnx
          · exact absurd ⟨x, hx, hnx⟩ ht
        · refine ⟨[], a, t, rfl, ha, ?_⟩
          intro y hy
          by_cases hpy : P y
          · exact hpy
          · exact absurd ⟨y, hy, hpy⟩ ht

/-! ## §3. The local deletion machinery

A bad letter *immediately followed by* `raise d` is impossible: a landing
leaves `d` buried (so the raise cannot fire), and a self-slide is cancelled by
`NoSelfKit.raiseSt_slideSt_self` (one letter shorter).  The backwards licence
transfer is what supplies the reversibility the cancellation needs. -/

/-- A card is never strictly below itself. -/
theorem not_mem_below_self {c : Card} : ∀ l : List Card, c ∉ below c l := by
  intro l
  induction l with
  | nil => exact List.not_mem_nil
  | cons x t ih =>
      rw [below_cons]
      by_cases hx : x = c
      · rw [ite_eq_left hx]
        exact List.not_mem_nil
      · rw [ite_eq_right hx]
        intro hm
        rcases List.mem_cons.mp hm with h | h
        · exact hx h.symm
        · exact ih h

/-- **A SELF-SLIDE OF `c` CANNOT PRODUCE A TOP OF `c` UNLESS `c` WAS ONE.**
(The converse of `CommuteStep.slideSt_pileOfTop_source` at the moving card.) -/
theorem pileOfTop_self_of_slideSt {st : State} {c : Card} {b : Base} {a k : Anchor}
    (hst : st.WF) (hhold : st.pileHolding c = some a)
    (hcp : st.canPlace c b = true) (hk : CommuteStep.tgt st b = some k)
    (hka : k ≠ a) (hrunv : fromCard c (st.piles a).faceUp ≠ [])
    (hcell : below c (st.piles a).faceUp ≠ [] ∨
      (below c (st.piles a).faceUp = [] ∧ (st.piles a).hidden = []))
    {m : Anchor}
    (h : (CommuteStep.slideSt st c b a).pileOfTop c = some m) :
    st.pileOfTop c = some a := by
  by_cases htop : st.pileOfTop c = some a
  · exact htop
  · exfalso
    have hnone : st.pileOfTop c = none := by
      cases hh : st.pileOfTop c with
      | none => rfl
      | some a' =>
          have h1 := Drain.pileHolding_of_pileOfTop hst hh
          rw [hhold] at h1
          have h2 : a' = a := (Option.some.inj h1).symm
          rw [h2] at hh
          exact absurd hh htop
    have hmem : c ∈ (st.piles a).faceUp := pileHolding_mem hhold
    have hno : ∀ j : Anchor, ((CommuteStep.slideSt st c b a).piles j).top ≠ some c := by
      intro j hj
      by_cases hja : j = a
      · subst hja
        rw [CommuteStep.slideSt_piles_source hst hcp hk hka hcell] at hj
        change lastOf (below c (st.piles j).faceUp) = some c at hj
        exact not_mem_below_self (st.piles j).faceUp (lastOf_mem hj)
      · by_cases hjk : j = k
        · subst hjk
          rw [CommuteStep.slideSt_piles_target hst hcp hk hka hcell] at hj
          change lastOf ((st.piles j).faceUp ++ fromCard c (st.piles a).faceUp) = some c at hj
          rw [CommuteStep.lastOf_append_of_ne_nil hrunv] at hj
          rw [SlideFwd.lastOf_fromCard_of_mem hmem] at hj
          have hc : st.pileOfTop c = some a := (pileOfTop_eq_some_iff hst).2 hj
          rw [hnone] at hc
          exact absurd hc (by simp)
        · rw [CommuteStep.slideSt_piles_other hst hcp hk hka hcell hja hjk] at hj
          have hcmem : c ∈ (st.piles j).faceUp := Pile.mem_of_top hj
          exact (mem_faceUp_unique hst hmem j hja).1 hcmem
    rw [CommuteStep.pileOfTop_none_of_no_top hno] at h
    exact absurd h (by simp)

/-- A PULL landing on `d` leaves `d` buried. -/
theorem pileOfTop_none_of_pull_landing {st s' : State} {d x : Card} {b : Base}
    (hst : st.WF) (hstep : State.step st (Move.foundToTab x b) = some s')
    (hb : b = Sum.inr d) : s'.pileOfTop d = none := by
  subst hb
  obtain ⟨x', -, hx', hcp, hs⟩ := CommuteStep.step_foundToTab_pullSt hstep
  obtain ⟨k, hk, hsit⟩ := canPlace_inr hcp
  have hkt : CommuteStep.tgt st (Sum.inr d) = some k := by
    simpa only [CommuteStep.tgt_inr] using hk
  have hxd : x ≠ d := by
    intro h
    subst h
    rw [canSitOn_eq] at hsit
    omega
  rw [CommuteStep.pileOfTop_none_of_no_top]
  intro j hj
  by_cases hjk : j = k
  · subst hjk
    rw [hs, CommuteStep.pullSt_piles, CommuteStep.putCard_top_written hkt] at hj
    exact hxd (Option.some.inj hj)
  · rw [hs, CommuteStep.pullSt_piles, CommuteStep.putCard_piles_ne hkt hjk] at hj
    have hmem : d ∈ (st.piles j).faceUp := Pile.mem_of_top hj
    have hmemk : d ∈ (st.piles k).faceUp := Pile.mem_of_top (pileOfTop_top hk).2
    exact (mem_faceUp_unique hst hmemk j hjk).1 hmem

/-- A SLIDE landing on `d` leaves `d` buried (`slideSt_pileOfTop_target`). -/
theorem pileOfTop_none_of_slide_landing {st s' : State} {d x : Card} {b : Base}
    (hst : st.WF) (hrev : reversibleAtW st (Move.tabToTab x b))
    (hstep : State.step st (Move.tabToTab x b) = some s')
    (hb : b = Sum.inr d) : s'.pileOfTop d = none := by
  subst hb
  obtain ⟨a₀, hhold, -, -, hs⟩ := CommuteStep.step_tabToTab_slideSt hstep
  obtain ⟨a, k, hholdD, hcpD, hk, hka, hface, hrunvD, hcell⟩ :=
    CommuteStep.slide_data hst hrev
  have ha : a = a₀ := Option.some.inj (hholdD.symm.trans hhold)
  have hkd : st.pileOfTop d = some k := by
    have h := hk
    simpa only [CommuteStep.tgt_inr] using h
  rw [hs, ← ha]
  exact CommuteStep.slideSt_pileOfTop_target hst hcpD hk hka hrunvD hcell hkd

/-- **A LANDING BURIES `d`** — uniformly over the letter. -/
theorem pileOfTop_none_of_landing {st s' : State} {d : Card} {q : Move}
    (hst : st.WF) (hrev : reversibleAtW st q)
    (hstep : State.step st q = some s')
    (hland : LandsOn d q) : s'.pileOfTop d = none := by
  cases q with
  | draw => exact absurd hland (by simp [LandsOn])
  | wasteToFound c => exact absurd hland (by simp [LandsOn])
  | wasteToTab c b => exact absurd hland (by simp [LandsOn])
  | tabToFound c => exact absurd hland (by simp [LandsOn])
  | foundToTab x b =>
      exact pileOfTop_none_of_pull_landing hst hstep (by simpa [LandsOn] using hland)
  | tabToTab x b =>
      exact pileOfTop_none_of_slide_landing hst hrev hstep
        (by simpa [LandsOn] using hland)

/-- **(the local deletion lemma)** A bad letter immediately followed by
`raise d` forces the bad letter to be a SELF-SLIDE of `d`, and then the two
letters `bad ; raise d` land exactly where `raise d` alone lands — one letter
shorter. -/
theorem bad_adjacent_raise_selfslide
    {st s' W : State} {d : Card} {q : Move}
    (hst : st.WF) (hrev : reversibleAtW st q)
    (hstep : State.step st q = some s')
    (hbad : BadLetter d q)
    (hraise : State.step s' (Move.tabToFound d) = some W) :
    SelfSlideHead d q ∧
      ∃ W', State.step st (Move.tabToFound d) = some W' ∧ W' = W := by
  rcases (badLetter_iff_landsOn_or_selfHead).mp hbad with hl | hs
  · exfalso
    have hnone : s'.pileOfTop d = none := pileOfTop_none_of_landing hst hrev hstep hl
    obtain ⟨-, a, ha, -⟩ := step_tabToFound_inv hraise
    rw [hnone] at ha
    exact absurd ha (by simp)
  · have hq : ∃ b : Base, q = Move.tabToTab d b := by
      cases q with
      | draw => exact absurd hs (by simp [SelfSlideHead])
      | wasteToFound c => exact absurd hs (by simp [SelfSlideHead])
      | wasteToTab c b => exact absurd hs (by simp [SelfSlideHead])
      | tabToFound c => exact absurd hs (by simp [SelfSlideHead])
      | foundToTab x b => exact absurd hs (by simp [SelfSlideHead])
      | tabToTab x b => exact ⟨b, by simpa [SelfSlideHead] using hs⟩
    obtain ⟨b, rfl⟩ := hq
    obtain ⟨a₀, hhold, -, -, hs'⟩ := CommuteStep.step_tabToTab_slideSt hstep
    obtain ⟨a, k, hholdD, hcpD, hk, hka, hface, hrunvD, hcell⟩ :=
      CommuteStep.slide_data hst hrev
    have ha : a = a₀ := Option.some.inj (hholdD.symm.trans hhold)
    obtain ⟨hnext', k', hk', hW⟩ := step_tabToFound_inv hraise
    have hnext : st.nextUp d = true := by
      have h := hnext'
      rw [hs'] at h
      unfold State.nextUp State.foundHeight at h ⊢
      rw [CommuteStep.slideSt_found] at h
      exact h
    have htop : st.pileOfTop d = some a := by
      refine pileOfTop_self_of_slideSt (m := k') hst hholdD hcpD hk hka hrunvD hcell ?_
      rw [ha, ← hs']
      exact hk'
    have hksource : (CommuteStep.slideSt st d b a).pileOfTop d = some k :=
      CommuteStep.slideSt_pileOfTop_source hst hcpD hk hka hrunvD hcell htop
    have hkk : k' = k := by
      have h1 := hk'
      rw [hs', ← ha] at h1
      rw [h1] at hksource
      exact Option.some.inj hksource
    have hcancel := NoSelfKit.raiseSt_slideSt_self hst htop hcpD hk hka hcell
    refine ⟨?_, raiseSt st d a, ?_, ?_⟩
    · simp [SelfSlideHead]
    · rw [step_tabToFound_splice hnext htop]
      rfl
    · rw [hW, hs', ← ha, hkk]
      exact hcancel.symm

/-- **REVERSE PRESERVATION OF THE LICENCE ACROSS A REVERSIBLE SELF-SLIDE.**
The oracle `tabToTabR` says a reversible self-slide with an empty `below` and an
empty hidden deck forces the card to be a king — and then the bare-king seat
clause holds.  Hence `CanRaise` transfers BACKWARDS. -/
theorem canRaise_of_canRaise_after_selfSlide
    {st s' : State} {d : Card} {b : Base}
    (hst : st.WF) (hrev : reversibleAtW st (Move.tabToTab d b))
    (hstep : State.step st (Move.tabToTab d b) = some s')
    (h : CanRaise s' d) : CanRaise st d := by
  obtain ⟨hnext', m, hm, -⟩ := h
  obtain ⟨a₀, hhold0, -, -, hs0⟩ := CommuteStep.step_tabToTab_slideSt hstep
  obtain ⟨a, k, hhold, hcp, hk, hka, hface, hrunv, hcell⟩ :=
    CommuteStep.slide_data hst hrev
  have ha : a = a₀ := Option.some.inj (hhold.symm.trans hhold0)
  have hs' : s' = CommuteStep.slideSt st d b a := by rw [hs0, ← ha]
  have hnext : st.nextUp d = true := by
    have hh := hnext'
    rw [hs'] at hh
    unfold State.nextUp State.foundHeight at hh ⊢
    rw [CommuteStep.slideSt_found] at hh
    exact hh
  have htop : st.pileOfTop d = some a := by
    refine pileOfTop_self_of_slideSt (m := m) hst hhold hcp hk hka hrunv hcell ?_
    rw [← hs']
    exact hm
  have hR : tabToTabR st d b = true :=
    (tabToTabR_iff_reversibleAtW hst d b).mpr hrev
  have hdeg : below d (st.piles a).faceUp = [] → (st.piles a).hidden = [] →
      d.rank = Rank.king := by
    intro hb hhid
    unfold tabToTabR at hR
    rw [hhold, hcp] at hR
    have hR2 : (match below d (st.piles a).faceUp with
        | [] => (match (st.piles a).hidden with
                 | [] => decide (d.rank = Rank.king)
                 | _ :: _ => false)
        | _ :: _ => true) = true := hR
    rw [hb, hhid] at hR2
    exact of_decide_eq_true hR2
  refine ⟨hnext, a, htop, ?_⟩
  rcases hcell with hbelow | ⟨hbelow, hhidden⟩
  · refine Or.inl ?_
    rw [hface]
    exact EmptyTail.chop_append_ne_nil hbelow hrunv
  · exact Or.inr ⟨hhidden, hdeg hbelow hhidden⟩

/-! ## §4. The packaging -/

/-- The interior of the bracket `pull d ; ... ; raise d`. -/
def Interior (β : List Move) (c : Card) (b : Base) (post : List Move) : List Move :=
  β ++ Move.foundToTab c b :: post

/-- Generic `Walk` append (absent from the core). -/
theorem walk_append {P : State → Move → Prop} {st mid W : State} {ρ σ : List Move}
    (h1 : Walk P st ρ mid) (h2 : Walk P mid σ W) : Walk P st (ρ ++ σ) W := by
  induction h1 with
  | nil st => simpa using h2
  | cons hlet hstep hrest ih => exact Walk.cons hlet hstep (ih h2)

/-- **THE STRADDLE PACKAGE.**  `pre = α ++ pull d bz :: β` produces the bracket
`α ; pull d ; (β ; pull c b ; post) ; raise d ; tail`, with the pull letter's
reversibility. -/
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
  obtain ⟨huwf, -, -, hplay, -, -, hρ, hleft, -, hshape, -, hright⟩ := hs
  have hρ0 : ρ = (pre ++ Move.foundToTab c b :: post) ++
      (Move.tabToFound d :: tail) := by
    rw [hρ, hshape, hright]
  have hρ' : ρ = α ++ Move.foundToTab d bz ::
      ((β ++ Move.foundToTab c b :: post) ++ Move.tabToFound d :: tail) := by
    rw [hρ0, hpre]
    simp only [List.append_assoc, List.cons_append]
  obtain ⟨P, hα, hrest⟩ := ValleyElim.ShufflePlayW_split hplay α _ hρ'
  obtain ⟨Q, hrevpull, hstep, hplayQ⟩ := Bubble.walk_cons_inv hrest
  exact ⟨P, Q, hρ', hα, hrevpull, hstep, hplayQ⟩

/-- **THE INTERIOR IS FREE-OR-PULL.** -/
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
    rcases MountainKit.free_or_pull_or_raise_of_play hleft m hmleft with hf | hp | hr
    · exact Or.inl hf
    · exact Or.inr hp
    · exact absurd hr (hraiseFree m hmleft)
  · rcases List.mem_cons.mp hmrest with rfl | hmp
    · exact Or.inr ⟨c, b, rfl⟩
    · exact Or.inl (hfree m hmp)

/-- **THE INTERIOR SPEAKS NO `d.suit`.** -/
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
  exact Mate.noSigma_after_self_pull_of_live hPwf hstep hγplay
    (interior_freeOrPull hsk hraiseFree hpre) hlive

/-! ## §5. The residual and the reduction

`LastBadLicensed` is the classical card's single residual, now freed of choice. -/

/-- **`LastBadLicensed`** — at the state reached just after the LAST bad letter
of the interior, `raise d` is still licensed. -/
def LastBadLicensed (d : Card) (Q : State) (I : List Move) : Prop :=
  ∀ (γ₁ : List Move) (q : Move) (γ₂ : List Move),
    I = γ₁ ++ q :: γ₂ →
    (∀ r ∈ γ₂, R12.ReadOK d r) →
    ¬ R12.ReadOK d q →
    ∀ Q₁ Q₂ : State, ShufflePlayW Q γ₁ Q₁ → State.step Q₁ q = some Q₂ →
      CanRaise Q₂ d

/-- **THE SHORTENING FROM THE SINGLE RESIDUAL** (choice-free; the classical
card needed `Classical.choice` only to *find* the last bad letter). -/
theorem no_self_pull_of_lastBad
    {u v : State} {ρ : List Move} {F : State} {left right : List Move}
    {c d : Card} {b : Base} {pre post tail : List Move}
    (hs : SplitKit.SplitHyp u v ρ F left right c d b pre post tail)
    (hraiseFree : ∀ m ∈ left, ¬ Bubble.IsRaise m)
    {α β : List Move} {bz : Base}
    (hpre : pre = α ++ Move.foundToTab d bz :: β)
    (hlic : ∀ (P Q : State),
      ShufflePlayW u α P → State.step P (Move.foundToTab d bz) = some Q →
      LastBadLicensed d Q (β ++ Move.foundToTab c b :: post))
    (hbad : ∃ q ∈ (β ++ Move.foundToTab c b :: post), ¬ R12.ReadOK d q) :
    False := by
  have hsk := hs
  obtain ⟨P, Q, hρ, hα, hrevpull, hstep, hplayQ⟩ := straddle_package hs hpre
  obtain ⟨huwf, -, -, -, -, hmin, -, -, -, -, -, -⟩ := hs
  have hall := interior_freeOrPull hsk hraiseFree hpre
  have hns := noSigma_interior hsk hraiseFree hpre hα hstep hplayQ
  have hQwf : Q.WF := step_wf (SatDifferCensus.ShufflePlayW.wf_end hα huwf) hstep
  -- the last bad letter (choice-free selector)
  obtain ⟨γ₁, q, γ₂, hI, hbadq, hgood⟩ :=
    exists_last_dec (P := fun q => R12.ReadOK d q) hbad
  have hI2 : (β ++ Move.foundToTab c b :: post) ++ Move.tabToFound d :: tail
      = γ₁ ++ q :: (γ₂ ++ Move.tabToFound d :: tail) := by
    rw [hI]
    simp only [List.append_assoc, List.cons_append]
  obtain ⟨Q₁, hplay1, hplay2⟩ :=
    ValleyElim.ShufflePlayW_split hplayQ γ₁ (q :: (γ₂ ++ Move.tabToFound d :: tail)) hI2
  obtain ⟨Q₂, hrevq, hstepq, hplay3⟩ := Bubble.walk_cons_inv hplay2
  have hQ₁wf : Q₁.WF := SatDifferCensus.ShufflePlayW.wf_end hplay1 hQwf
  have hcan : CanRaise Q₂ d :=
    hlic P Q hα hstep γ₁ q γ₂ hI hgood hbadq Q₁ Q₂ hplay1 hstepq
  have hmemI : q ∈ (β ++ Move.foundToTab c b :: post) := by
    rw [hI]
    exact List.mem_append_right _ (List.mem_cons_self ..)
  have hbadL : BadLetter d q := badLetter_of_not_readOK (hall q hmemI) (hns q hmemI) hbadq
  -- a landing would bury `d`; so the last bad letter is a self-slide, and the
  -- licence transfers backwards to its origin
  have hself : SelfSlideHead d q := by
    rcases (badLetter_iff_landsOn_or_selfHead).mp hbadL with hland | hself
    · exfalso
      have hnone := pileOfTop_none_of_landing hQ₁wf hrevq hstepq hland
      obtain ⟨-, m, hm, -⟩ := hcan
      rw [hnone] at hm
      exact absurd hm (by simp)
    · exact hself
  have hslide : ∃ b : Base, q = Move.tabToTab d b := by
    cases q with
    | draw => exact absurd hself (by simp [SelfSlideHead])
    | wasteToFound c => exact absurd hself (by simp [SelfSlideHead])
    | wasteToTab c b => exact absurd hself (by simp [SelfSlideHead])
    | tabToFound c => exact absurd hself (by simp [SelfSlideHead])
    | foundToTab x b => exact absurd hself (by simp [SelfSlideHead])
    | tabToTab x b => exact ⟨b, by simpa [SelfSlideHead] using hself⟩
  obtain ⟨bq, rfl⟩ := hslide
  have hcan₁ : CanRaise Q₁ d :=
    canRaise_of_canRaise_after_selfSlide hQ₁wf hrevq hstepq hcan
  have hrevR : reversibleAtW Q₁ (Move.tabToFound d) :=
    DrainClose.reversibleAtW_tabToFound_of_canRaise hQ₁wf hcan₁
  -- hoist the raise over the good suffix
  have hsw : NonforkKit.RaiseSwaps Q₂ d γ₂ :=
    R12.raiseSwaps_of_read (step_wf hQ₁wf hstepq) hplay3 hcan hgood
  have hbubble : ShufflePlayW Q₂ (Move.tabToFound d :: γ₂ ++ tail) v :=
    NonforkKit.raise_bubble γ₂ hplay3 hsw
  obtain ⟨W, -, hraise, hplayW⟩ := Bubble.walk_cons_inv hbubble
  obtain ⟨-, W', hraise', hWW⟩ :=
    bad_adjacent_raise_selfslide hQ₁wf hrevq hstepq hbadL hraise
  -- the shorter WITNESS play
  have hρ'play : ShufflePlayW u (α ++ Move.foundToTab d bz ::
      (γ₁ ++ Move.tabToFound d :: (γ₂ ++ tail))) v := by
    have h1 : ShufflePlayW u (α ++ Move.foundToTab d bz :: γ₁) Q₁ :=
      walk_append hα (Walk.cons hrevpull hstep hplay1)
    have h2 : ShufflePlayW Q₁ (Move.tabToFound d :: (γ₂ ++ tail)) v :=
      Walk.cons hrevR hraise' (hWW.symm ▸ hplayW)
    have h3 := walk_append h1 h2
    simpa only [List.append_assoc, List.cons_append] using h3
  have hshort : (α ++ Move.foundToTab d bz ::
      (γ₁ ++ Move.tabToFound d :: (γ₂ ++ tail))).length < ρ.length := by
    rw [hρ, hI]
    simp only [List.length_append, List.length_cons]
    omega
  exact absurd hshort (Nat.not_lt.mpr (hmin _ hρ'play))

/-- The twin-pull residual (the cross-twin half; unchanged from `Strad_Main`). -/
def NoTwinPullOfRaise : Prop :=
  ∀ (u v : State) (ρ : List Move) (F : State) (left right : List Move)
    (c d : Card) (b : Base) (pre post tail : List Move),
    SplitKit.SplitHyp u v ρ F left right c d b pre post tail →
    (∀ m ∈ left, ¬ Bubble.IsRaise m) →
    ∀ bz : Base, Move.foundToTab d.twin bz ∉ pre

/-- The global form of the residual. -/
def LastBadLicensedGlobal : Prop :=
  ∀ (u v : State) (ρ : List Move) (F : State) (left right : List Move)
    (c d : Card) (b : Base) (pre post tail : List Move),
    SplitKit.SplitHyp u v ρ F left right c d b pre post tail →
    (∀ m ∈ left, ¬ Bubble.IsRaise m) →
    ∀ (bz : Base) (α β : List Move),
      pre = α ++ Move.foundToTab d bz :: β →
      ∀ (P Q : State), ShufflePlayW u α P →
        State.step P (Move.foundToTab d bz) = some Q →
        LastBadLicensed d Q (β ++ Move.foundToTab c b :: post)

/-- **THE SELF-PULL HALF, GLOBALLY — choice-free.** -/
theorem no_self_pull_of_global
    (hlic : LastBadLicensedGlobal)
    {u v : State} {ρ : List Move} {F : State} {left right : List Move}
    {c d : Card} {b : Base} {pre post tail : List Move}
    (hs : SplitKit.SplitHyp u v ρ F left right c d b pre post tail)
    (hraiseFree : ∀ m ∈ left, ¬ Bubble.IsRaise m) :
    ∀ bz : Base, Move.foundToTab d bz ∉ pre := by
  intro bz hmem
  obtain ⟨α, β, hpre⟩ := List.mem_iff_append.mp hmem
  by_cases hbad : ∃ q ∈ (β ++ Move.foundToTab c b :: post), ¬ R12.ReadOK d q
  · have hlic' := hlic u v ρ F left right c d b pre post tail hs hraiseFree
      bz α β hpre
    exact no_self_pull_of_lastBad hs hraiseFree hpre hlic' hbad
  · -- no bad letter: the bracket is read-safe and deleted
    obtain ⟨P, Q, hρ, hα, -, hstep, hplayQ⟩ := straddle_package hs hpre
    have hread : ∀ q ∈ (β ++ Move.foundToTab c b :: post), R12.ReadOK d q := by
      intro q hq
      by_cases hr : R12.ReadOK d q
      · exact hr
      · exact absurd ⟨q, hq, hr⟩ hbad
    have hρ2 : ρ = (α ++ Move.foundToTab d bz ::
        (β ++ Move.foundToTab c b :: post)) ++ Move.tabToFound d :: tail := by
      simpa only [List.append_assoc, List.cons_append] using hρ
    exact Mate.splitHyp_not_readBracket (hs := hs) (hρ := hρ2)
      (hα := hα) (hstep := hstep) (hread := hread)

/-- **`PinRight.NoPrePullRaise` FROM THE RESIDUALS — choice-free.** -/
theorem noPrePullRaise_of_residuals
    (hlic : LastBadLicensedGlobal) (htwin : NoTwinPullOfRaise) :
    PinRight.NoPrePullRaise := by
  intro u v ρ F left right c d b pre post tail hs hraiseFree hpair
  obtain ⟨z, bz, hmem, hdz⟩ := hpair
  rcases hdz with hdz | hdz
  · exact no_self_pull_of_global hlic hs hraiseFree bz (hdz ▸ hmem)
  · refine htwin u v ρ F left right c d b pre post tail hs hraiseFree bz ?_
    have hz : z = d.twin := by rw [hdz, card_twin_twin]
    rwa [hz] at hmem

/-- **THE CAMPAIGN PIN FROM THE RESIDUALS — choice-free.** -/
theorem splitTwinRungPin_of_residuals
    (hlic : LastBadLicensedGlobal) (htwin : NoTwinPullOfRaise)
    (hms : ∀ (u v : State) (ρ : List Move) (F : State) (left right : List Move)
      (c d : Card) (b : Base) (pre post tail : List Move),
      SplitKit.SplitHyp u v ρ F left right c d b pre post tail →
      MountainKit.MountainSplit left right)
    (hb : SplitKit.SplitBlock) : TwinKit.SplitTwinRungPin := by
  intro u v ρ F left right c d b pre post tail h
  have hres : PinRight.NoPrePullRaise := noPrePullRaise_of_residuals hlic htwin
  exact TwinKit.nextUp_true_iff.mpr
    (PinRight.pin_of_noPrePullRaise hres h
      (hms u v ρ F left right c d b pre post tail h).1
      (hb u v ρ F left right c d b pre post tail h))


/-! ## §6. The two lanes' common statement

The constructive lane (`Temp/Strad_Main.lean`) reduces to `LandingResidual`: the
interior of a straddling self-bracket never **lands** a card on the raise card.
This card reduces to `LastBadLicensed`: the raise is still **licensed** at the
last bad letter.

These are not the same statement — `LandingResidual` is letter-shaped and
universal over the interior, `LastBadLicensed` is state-shaped and mentions only
the last bad letter — but **`LandingResidual` implies `LastBadLicensed`**, and
the proof is the content of the next two rows: with no landing letter, the
licence propagates unchanged along the whole interior (slides preserve it,
including self-slides by `EmptyTail.canRaise_survives_own_slide`; pulls preserve
it by `d.suit`-silence; draws trivially).

The converse does **not** hold: `LastBadLicensed` constrains only the *last* bad
letter, so a landing earlier in the interior is untouched by it.  So the
constructive residual is the strictly stronger of the two, and both are
equivalent to the no-straddle target in the `⇒` direction. -/

/-- `LandingResidual` — the constructive lane's residual, restated verbatim
(`Temp/Strad_Main.lean`, `StradKit.LandingResidual`). -/
def LandingResidual : Prop :=
  ∀ (u v : State) (ρ : List Move) (F : State) (left right : List Move)
    (c d : Card) (b : Base) (pre post tail : List Move),
    SplitKit.SplitHyp u v ρ F left right c d b pre post tail →
    (∀ m ∈ left, ¬ Bubble.IsRaise m) →
    ∀ (bz : Base) (α β : List Move),
      pre = α ++ Move.foundToTab d bz :: β →
      ∀ q ∈ (β ++ Move.foundToTab c b :: post), ¬ LandsOn d q

/-- **THE LICENCE IS INVARIANT ALONG A NO-LANDING INTERIOR.**  A witness play
whose letters are free-or-pull, `d.suit`-silent, and never land on `d` preserves
`CanRaise · d`. -/
theorem canRaise_persists_no_landing
    {Q R : State} {d : Card} {γ : List Move} (hplay : ShufflePlayW Q γ R) :
    Q.WF → (∀ m ∈ γ, LandKit.FreeOrPull m) →
      (∀ m ∈ γ, ThirdLive.NoSigmaLetter d.suit m) →
      (∀ m ∈ γ, ¬ LandsOn d m) → CanRaise Q d → CanRaise R d :=
  Walk.rec
    (motive := fun Q γ R _ =>
      Q.WF → (∀ m ∈ γ, LandKit.FreeOrPull m) →
        (∀ m ∈ γ, ThirdLive.NoSigmaLetter d.suit m) →
        (∀ m ∈ γ, ¬ LandsOn d m) → CanRaise Q d → CanRaise R d)
    (fun st => by intro _ _ _ _ hcan; exact hcan)
    (fun {st s₁ W m ρ} hrev hstep hrest ih => by
      intro hwf hfp hns hnl hcan
      have hs₁ : s₁.WF := step_wf hwf hstep
      have hfp' : ∀ x ∈ ρ, LandKit.FreeOrPull x :=
        fun x hx => hfp x (List.mem_cons_of_mem m hx)
      have hns' : ∀ x ∈ ρ, ThirdLive.NoSigmaLetter d.suit x :=
        fun x hx => hns x (List.mem_cons_of_mem m hx)
      have hnl' : ∀ x ∈ ρ, ¬ LandsOn d x :=
        fun x hx => hnl x (List.mem_cons_of_mem m hx)
      have hcan' : CanRaise s₁ d := by
        rcases hfp m (List.mem_cons_self ..) with hfree | ⟨x, b, rfl⟩
        · rcases hfree with rfl | ⟨x, b, rfl⟩
          · exact R12.canRaise_survives_draw hstep hcan
          · by_cases hxd : x = d
            · subst hxd
              exact EmptyTail.canRaise_survives_own_slide hwf hstep hrev hcan
            · exact R12.canRaise_survives_slide hwf hstep hrev hxd
                (hnl (Move.tabToTab x b) (List.mem_cons_self ..)) hcan
        · exact R12.canRaise_survives_pull hwf hstep
            ((hns (Move.foundToTab x b) (List.mem_cons_self ..)).1 x b rfl)
            (hnl (Move.foundToTab x b) (List.mem_cons_self ..)) hcan
      exact ih hs₁ hfp' hns' hnl' hcan')
    hplay

/-- **`LandingResidual` ⇒ `LastBadLicensed`** — the two lanes reached the same
place, read at a state instead of at a letter. -/
theorem lastBadLicensed_of_landingResidual
    (hl : LandingResidual)
    {u v : State} {ρ : List Move} {F : State} {left right : List Move}
    {c d : Card} {b : Base} {pre post tail : List Move}
    (hs : SplitKit.SplitHyp u v ρ F left right c d b pre post tail)
    (hraiseFree : ∀ m ∈ left, ¬ Bubble.IsRaise m)
    {α β : List Move} {bz : Base}
    (hpre : pre = α ++ Move.foundToTab d bz :: β)
    {P Q : State} (hα : ShufflePlayW u α P)
    (hstep : State.step P (Move.foundToTab d bz) = some Q) :
    LastBadLicensed d Q (β ++ Move.foundToTab c b :: post) := by
  intro γ₁ q γ₂ hI hgood hbadq Q₁ Q₂ hplay1 hstepq
  have hsk := hs
  obtain ⟨P', Q', hρ, hα', hrevpull, hstep', hplayQ⟩ := straddle_package hs hpre
  -- the package's `P, Q` are the given ones (determinism of the play)
  have hPQ : P' = P := by
    have h1 := Walk_run _ hα'
    have h2 := Walk_run _ hα
    rw [h2] at h1
    exact (Option.some.inj h1).symm
  have hQQ : Q' = Q := by
    rw [hPQ] at hstep'
    have hh := hstep
    rw [hstep'] at hh
    exact Option.some.inj hh
  rw [hQQ] at hplayQ
  have hPwf : P.WF := SatDifferCensus.ShufflePlayW.wf_end hα hs.1
  have hQwf : Q.WF := step_wf hPwf hstep
  have hcanQ : CanRaise Q d := Mate.self_pull_canRaise hPwf hstep
  -- the actual play reaches `Q₁` through `γ₁`, with `q` as the next letter
  have hI2 : (β ++ Move.foundToTab c b :: post) ++ Move.tabToFound d :: tail
      = γ₁ ++ q :: (γ₂ ++ Move.tabToFound d :: tail) := by
    rw [hI]
    simp only [List.append_assoc, List.cons_append]
  obtain ⟨Q₁', hplay1', hplay2'⟩ :=
    ValleyElim.ShufflePlayW_split hplayQ γ₁ (q :: (γ₂ ++ Move.tabToFound d :: tail)) hI2
  obtain ⟨Q₂', hrevq', hstepq', hplay3'⟩ := Bubble.walk_cons_inv hplay2'
  have hQ₁'Q₁ : Q₁' = Q₁ := by
    have h1 := Walk_run _ hplay1'
    have h2 := Walk_run _ hplay1
    rw [h2] at h1
    exact (Option.some.inj h1).symm
  rw [hQ₁'Q₁] at hrevq'
  -- every letter of the window `γ₁ ++ [q]` is in the interior
  have hmem : ∀ m ∈ γ₁ ++ [q], m ∈ (β ++ Move.foundToTab c b :: post) := by
    intro m hm
    rw [hI]
    rw [List.mem_append] at hm ⊢
    rcases hm with hm | hm
    · exact Or.inl hm
    · rw [List.mem_singleton] at hm
      subst hm
      exact Or.inr (List.mem_cons_self ..)
  have hfp : ∀ m ∈ γ₁ ++ [q], LandKit.FreeOrPull m :=
    fun m hm => interior_freeOrPull hsk hraiseFree hpre m (hmem m hm)
  have hns : ∀ m ∈ γ₁ ++ [q], ThirdLive.NoSigmaLetter d.suit m :=
    fun m hm => noSigma_interior hsk hraiseFree hpre hα hstep hplayQ m (hmem m hm)
  have hnl : ∀ m ∈ γ₁ ++ [q], ¬ LandsOn d m :=
    fun m hm => hl u v ρ F left right c d b pre post tail hs hraiseFree bz α β hpre m
      (hmem m hm)
  have hplayq : ShufflePlayW Q (γ₁ ++ [q]) Q₂ :=
    walk_append hplay1 (Walk.cons hrevq' hstepq (Walk.nil Q₂))
  exact canRaise_persists_no_landing hplayq hQwf hfp hns hnl hcanQ
/-- **`LandingResidual` forbids EVERY landing.** -/
theorem landsOn_false_of_landingResidual
    (hl : LandingResidual)
    {u v : State} {ρ : List Move} {F : State} {left right : List Move}
    {c d : Card} {b : Base} {pre post tail : List Move}
    (hs : SplitKit.SplitHyp u v ρ F left right c d b pre post tail)
    (hraiseFree : ∀ m ∈ left, ¬ Bubble.IsRaise m)
    {bz : Base} {α β : List Move}
    (hpre : pre = α ++ Move.foundToTab d bz :: β)
    {q : Move} (hq : q ∈ (β ++ Move.foundToTab c b :: post)) :
    ¬ LandsOn d q :=
  hl u v ρ F left right c d b pre post tail hs hraiseFree bz α β hpre q hq

/-- **`LastBadLicensed` forbids the LAST bad letter from landing.**  A landing
would bury `d`, and the licence needs `d` to be a pile top. -/
theorem landsOn_false_of_lastBadLicensed
    {Q Q₁ Q₂ : State} {d : Card}
    {γ₁ : List Move} {q : Move} {γ₂ : List Move}
    (hQ₁wf : Q₁.WF) (hrevq : reversibleAtW Q₁ q)
    (hstepq : State.step Q₁ q = some Q₂)
    (hlic : LastBadLicensed d Q (γ₁ ++ q :: γ₂))
    (hgood : ∀ r ∈ γ₂, R12.ReadOK d r) (hbadq : ¬ R12.ReadOK d q)
    (hplay : ShufflePlayW Q γ₁ Q₁) :
    ¬ LandsOn d q := by
  intro hland
  have hcan : CanRaise Q₂ d :=
    hlic γ₁ q γ₂ rfl hgood hbadq Q₁ Q₂ hplay hstepq
  have hnone := pileOfTop_none_of_landing hQ₁wf hrevq hstepq hland
  obtain ⟨-, m, hm, -⟩ := hcan
  rw [hnone] at hm
  exact absurd hm (by simp)

/-- **THE GLOBAL FORM.**  `LandingResidual` implies the classical card's global
residual `LastBadLicensedGlobal` — so every consumer of the classical reduction
can be fed from the constructive lane's residual. -/
theorem lastBadLicensedGlobal_of_landingResidual (hl : LandingResidual) :
    LastBadLicensedGlobal := by
  intro u v ρ F left right c d b pre post tail hs hraiseFree bz α β hpre P Q hα hstep
  exact lastBadLicensed_of_landingResidual hl hs hraiseFree hpre hα hstep

/-- **END TO END: THE TWO LANES COMPOSE — choice-free.**  The constructive lane's
`LandingResidual` plus the (untouched) cross-twin half discharge the pin. -/
theorem splitTwinRungPin_of_landingResidual_twin
    (hl : LandingResidual) (htwin : NoTwinPullOfRaise)
    (hms : ∀ (u v : State) (ρ : List Move) (F : State) (left right : List Move)
      (c d : Card) (b : Base) (pre post tail : List Move),
      SplitKit.SplitHyp u v ρ F left right c d b pre post tail →
      MountainKit.MountainSplit left right)
    (hb : SplitKit.SplitBlock) : TwinKit.SplitTwinRungPin :=
  splitTwinRungPin_of_residuals (lastBadLicensedGlobal_of_landingResidual hl)
    htwin hms hb

/-! ## §7. Why the backwards transfer is safe (kernel gadget)

The backward-preservation lemma is true because the only way a self-slide can
*create* the licence is the degenerate `below = []`, `hidden = []`, non-king
configuration — and that slide is **irreversible** (`tabToTabR` demands a king),
so it never occurs in a witness play. -/

/-- `Q♠` — a lone pile top over an empty hidden deck. -/
def GD : Card := ⟨.spade, .queen⟩
/-- `K♥` — the red king it can be slid onto. -/
def GKH : Card := ⟨.heart, .king⟩

/-- spades `A..J` founded (so `Q♠` is next-up), hearts `A..Q` founded;
`p0 = ⟨[], [Q♠]⟩`, `p1 = ⟨[], [K♥]⟩`; everything else in the stock. -/
def gadget : State :=
  { found := fun s => match s with
      | .spade => [⟨.spade, .ace⟩, ⟨.spade, .two⟩, ⟨.spade, .three⟩,
          ⟨.spade, .four⟩, ⟨.spade, .five⟩, ⟨.spade, .six⟩, ⟨.spade, .seven⟩,
          ⟨.spade, .eight⟩, ⟨.spade, .nine⟩, ⟨.spade, .ten⟩, ⟨.spade, .jack⟩]
      | .heart => [⟨.heart, .ace⟩, ⟨.heart, .two⟩, ⟨.heart, .three⟩,
          ⟨.heart, .four⟩, ⟨.heart, .five⟩, ⟨.heart, .six⟩, ⟨.heart, .seven⟩,
          ⟨.heart, .eight⟩, ⟨.heart, .nine⟩, ⟨.heart, .ten⟩,
          ⟨.heart, .jack⟩, ⟨.heart, .queen⟩]
      | _ => []
    piles := fun a => match a with
      | .p0 => ⟨[], [GD]⟩
      | .p1 => ⟨[], [GKH]⟩
      | _ => ⟨[], []⟩
    stock := Card.universe.filter
      (fun c => !(decide (c ∈ [GD, GKH] ++ [⟨.spade, .ace⟩, ⟨.spade, .two⟩,
        ⟨.spade, .three⟩, ⟨.spade, .four⟩, ⟨.spade, .five⟩, ⟨.spade, .six⟩,
        ⟨.spade, .seven⟩, ⟨.spade, .eight⟩, ⟨.spade, .nine⟩, ⟨.spade, .ten⟩,
        ⟨.spade, .jack⟩, ⟨.heart, .ace⟩, ⟨.heart, .two⟩, ⟨.heart, .three⟩,
        ⟨.heart, .four⟩, ⟨.heart, .five⟩, ⟨.heart, .six⟩, ⟨.heart, .seven⟩,
        ⟨.heart, .eight⟩, ⟨.heart, .nine⟩, ⟨.heart, .ten⟩,
        ⟨.heart, .jack⟩, ⟨.heart, .queen⟩])))
    waste := []
    drawStep := 1 }

theorem gadget_wf : gadget.WF := by
  refine ⟨?_, ?_, ?_, by decide⟩
  · intro s
    cases s
    · exact ⟨11, rfl⟩
    · exact ⟨12, rfl⟩
    · exact ⟨0, rfl⟩
    · exact ⟨0, rfl⟩
  · intro a
    cases a <;> decide
  · intro c _
    rcases c with ⟨s, r⟩
    cases s <;> cases r <;> decide

/-- `Q♠` is NOT raisable from the gadget: `chop` of its column is empty, the
hidden deck is empty, and `Q♠` is not a king. -/
theorem gadget_not_canRaise : ¬ CanRaise gadget GD := by
  rintro ⟨-, a, ha, hseat⟩
  have ha' : a = Anchor.p0 := by
    revert ha
    cases a <;> decide
  subst ha'
  revert hseat
  decide

/-- **THE NAIVE IMPLICATION FAILS FOR LEGAL (BUT IRREVERSIBLE) SLIDES.**  The
self-slide of `Q♠` onto `K♥` is legal and makes `Q♠` raisable, although it was
not raisable before — precisely the configuration the backwards-transfer lemma
must exclude. -/
theorem gadget_legal_licence_appears :
    ∃ s' : State, gadget.step (Move.tabToTab GD (Sum.inr GKH)) = some s' ∧
      ¬ CanRaise gadget GD ∧ CanRaise s' GD := by
  have hcp : gadget.canPlace GD (Sum.inr GKH) = true := by decide
  have hk : CommuteStep.tgt gadget (Sum.inr GKH) = some Anchor.p1 := by decide
  have hka : Anchor.p1 ≠ Anchor.p0 := by decide
  have hhold : gadget.pileHolding GD = some Anchor.p0 := by decide
  have hrunv : fromCard GD (gadget.piles Anchor.p0).faceUp ≠ [] := by decide
  have hcell : below GD (gadget.piles Anchor.p0).faceUp ≠ [] ∨
      (below GD (gadget.piles Anchor.p0).faceUp = [] ∧
        (gadget.piles Anchor.p0).hidden = []) := by decide
  have hpa : gadget.pileOfTop GD = some Anchor.p0 := by decide
  have htop : (CommuteStep.slideSt gadget GD (Sum.inr GKH) Anchor.p0).pileOfTop GD
      = some Anchor.p1 :=
    CommuteStep.slideSt_pileOfTop_source gadget_wf hcp hk hka hrunv hcell hpa
  refine ⟨CommuteStep.slideSt gadget GD (Sum.inr GKH) Anchor.p0, ?_,
    gadget_not_canRaise, ?_⟩
  · rw [step_tabToTab_eq, hhold]
    dsimp only
    rw [hcp, ite_eq_left rfl]
    cases hfc : fromCard GD (gadget.piles Anchor.p0).faceUp with
    | nil => exact absurd hfc hrunv
    | cons x xs =>
        unfold CommuteStep.slideSt
        rw [hfc]
  · refine ⟨?_, Anchor.p1, htop, ?_⟩
    · unfold State.nextUp State.foundHeight
      rw [CommuteStep.slideSt_found]
      decide
    · rw [CommuteStep.slideSt_piles_target gadget_wf hcp hk hka hcell]
      exact Or.inl (by decide)

/-- **THE SAME SLIDE IS IRREVERSIBLE.**  `tabToTabR` requires a king when the
column below is empty and the hidden deck is empty; `Q♠` is not a king. -/
theorem gadget_slide_irreversible :
    ¬ reversibleAtW gadget (Move.tabToTab GD (Sum.inr GKH)) := by
  intro hrev
  have hR : tabToTabR gadget GD (Sum.inr GKH) = true :=
    (tabToTabR_iff_reversibleAtW gadget_wf GD (Sum.inr GKH)).mpr hrev
  revert hR
  decide

/-! ## §8. Axiom battery — every row must be choice-free -/

#print axioms ChoiceFree.badLetter_iff_landsOn_or_selfHead
#print axioms ChoiceFree.badLetter_of_not_readOK
#print axioms ChoiceFree.not_readOK_of_badLetter
#print axioms ChoiceFree.badLetter_of_landsOn
#print axioms ChoiceFree.badLetter_of_selfSlideHead
#print axioms ChoiceFree.exists_last_dec
#print axioms ChoiceFree.not_mem_below_self
#print axioms ChoiceFree.pileOfTop_self_of_slideSt
#print axioms ChoiceFree.pileOfTop_none_of_pull_landing
#print axioms ChoiceFree.pileOfTop_none_of_slide_landing
#print axioms ChoiceFree.pileOfTop_none_of_landing
#print axioms ChoiceFree.bad_adjacent_raise_selfslide
#print axioms ChoiceFree.canRaise_of_canRaise_after_selfSlide
#print axioms ChoiceFree.walk_append
#print axioms ChoiceFree.straddle_package
#print axioms ChoiceFree.interior_freeOrPull
#print axioms ChoiceFree.noSigma_interior
#print axioms ChoiceFree.no_self_pull_of_lastBad
#print axioms ChoiceFree.no_self_pull_of_global
#print axioms ChoiceFree.noPrePullRaise_of_residuals
#print axioms ChoiceFree.splitTwinRungPin_of_residuals
#print axioms ChoiceFree.canRaise_persists_no_landing
#print axioms ChoiceFree.lastBadLicensed_of_landingResidual
#print axioms ChoiceFree.landsOn_false_of_landingResidual
#print axioms ChoiceFree.landsOn_false_of_lastBadLicensed
#print axioms ChoiceFree.lastBadLicensedGlobal_of_landingResidual
#print axioms ChoiceFree.splitTwinRungPin_of_landingResidual_twin
#print axioms ChoiceFree.gadget_wf
#print axioms ChoiceFree.gadget_not_canRaise
#print axioms ChoiceFree.gadget_legal_licence_appears
#print axioms ChoiceFree.gadget_slide_irreversible

end ChoiceFree
