import Orig2.Fork.ForkCriticalPair
import Orig2.Substrate.Classification
import Orig2.Fork.FirstPassage
import Orig2.Fiber.ArmFiber
import Orig2.Substrate.CargoRaise

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-!
# Orig2/ForkSplit — valley elimination, local kit (SCRATCH)

Self-contained copies of the green rows from `Temp/Valley_Step.lean`,
`Temp/Commute_Step_Raise.lean`, and the first-excursion saturation kit,
plus `crossing_cancel`, the crossing-block deletion, the valley-split
finder, and the same-card adjacent valley elimination.

House compliance: scratch leaf, read-only on the repository, no `sorry`,
no `Classical.choice`, no `native_decide`.
-/

namespace ValleyElim

/-! ## §0. Free letters -/

/-- A rung-preserving reversible letter: draw or a tableau slide.  The
two waste letters are never reversible, so at `ShufflePlayW` origins the
non-free letters are exactly the pulls (`foundToTab`) and raises
(`tabToFound`). -/
def FreeMove (m : Move) : Prop :=
  m = Move.draw ∨ ∃ (c : Card) (b : Base), m = Move.tabToTab c b

theorem free_draw : FreeMove Move.draw := Or.inl rfl

theorem free_slide (c : Card) (b : Base) : FreeMove (Move.tabToTab c b) :=
  Or.inr ⟨c, b, rfl⟩

/-- Computable spelling of `FreeMove`, for constructive existence search. -/
def isFreeB : Move → Bool
  | Move.draw => true
  | Move.tabToTab _ _ => true
  | _ => false

theorem isFreeB_eq_true_iff {m : Move} : isFreeB m = true ↔ FreeMove m := by
  cases m with
  | draw => simp [isFreeB, FreeMove]
  | wasteToFound c => simp [isFreeB, FreeMove]
  | wasteToTab c b => simp [isFreeB, FreeMove]
  | tabToFound c => simp [isFreeB, FreeMove]
  | foundToTab c b => simp [isFreeB, FreeMove]
  | tabToTab c b => simp [isFreeB, FreeMove]

theorem isFreeB_eq_false_iff {m : Move} : isFreeB m = false ↔ ¬ FreeMove m := by
  constructor
  · intro h hf
    have htrue : isFreeB m = true := isFreeB_eq_true_iff.mpr hf
    rw [h] at htrue
    exact Bool.false_ne_true htrue
  · intro hf
    cases hv : isFreeB m with
    | false => rfl
    | true => exact absurd (isFreeB_eq_true_iff.mp hv) hf

theorem not_not_isFreeB_eq_false {m : Move} (h : (!isFreeB m) = false) :
    FreeMove m := by
  cases hv : isFreeB m with
  | false =>
      exfalso
      rw [hv] at h
      change true = false at h
      cases h
  | true => exact isFreeB_eq_true_iff.mp hv

theorem not_not_isFreeB_eq_true {m : Move} (h : (!isFreeB m) = true) :
    ¬ FreeMove m := by
  cases hv : isFreeB m with
  | false => exact isFreeB_eq_false_iff.mp hv
  | true =>
      exfalso
      rw [hv] at h
      change false = true at h
      cases h

/-- Computable spelling of "is a pull". -/
def isPullB : Move → Bool
  | Move.foundToTab _ _ => true
  | _ => false

theorem isPullB_eq_true_iff {m : Move} :
    isPullB m = true ↔ ∃ (c : Card) (b : Base), m = Move.foundToTab c b := by
  cases m with
  | draw => simp [isPullB]
  | wasteToFound c => simp [isPullB]
  | wasteToTab c b => simp [isPullB]
  | tabToFound c => simp [isPullB]
  | foundToTab c b => simp [isPullB]
  | tabToTab c b => simp [isPullB]

/-- Computable spelling of "is a raise". -/
def isRaiseB : Move → Bool
  | Move.tabToFound _ => true
  | _ => false

theorem isRaiseB_eq_true_iff {m : Move} :
    isRaiseB m = true ↔ ∃ d : Card, m = Move.tabToFound d := by
  cases m with
  | draw => simp [isRaiseB]
  | wasteToFound c => simp [isRaiseB]
  | wasteToTab c b => simp [isRaiseB]
  | tabToFound c => simp [isRaiseB]
  | foundToTab c b => simp [isRaiseB]
  | tabToTab c b => simp [isRaiseB]

/-- A member with a true Boolean predicate makes `List.any` true. -/
theorem any_eq_true_of_mem {p : Move → Bool} {m : Move} {l : List Move}
    (hm : m ∈ l) (hp : p m = true) : l.any p = true := by
  induction l with
  | nil => exact absurd hm (by simp)
  | cons x xs ih =>
      rcases List.mem_cons.mp hm with rfl | hm'
      · change (p m || xs.any p) = true
        rw [hp]
        rfl
      · change (p x || xs.any p) = true
        rw [ih hm']
        exact Bool.or_true _

/-- The first occurrence of a Boolean move predicate. -/
theorem exists_first_bool (p : Move → Bool) (ρ : List Move)
    (h : ρ.any p = true) :
    ∃ (α : List Move) (m : Move) (β : List Move),
      ρ = α ++ m :: β ∧ (∀ x ∈ α, p x = false) ∧ p m = true := by
  induction ρ with
  | nil => change false = true at h; cases h
  | cons x xs ih =>
      change (p x || xs.any p) = true at h
      cases hpx : p x with
      | true => exact ⟨[], x, xs, rfl, by simp, hpx⟩
      | false =>
          have hxs : xs.any p = true := by
            rw [hpx] at h
            exact h
          obtain ⟨α, m, β, heq, hα, hm⟩ := ih hxs
          refine ⟨x :: α, m, β, ?_, ?_, hm⟩
          · rw [heq]; rfl
          · intro y hy
            rcases List.mem_cons.mp hy with rfl | hy'
            · exact hpx
            · exact hα y hy'

/-- No member satisfies the predicate when `List.any` is false. -/
theorem any_eq_false {p : Move → Bool} {l : List Move}
    (h : l.any p = false) : ∀ m ∈ l, p m = false := by
  induction l with
  | nil => intro m hm; exact absurd hm (by simp)
  | cons x xs ih =>
      change (p x || xs.any p) = false at h
      cases hpx : p x with
      | true =>
          rw [hpx] at h
          cases h
      | false =>
          have hxs : xs.any p = false := by
            rw [hpx] at h
            exact h
          intro m hm
          rcases List.mem_cons.mp hm with rfl | hm'
          · exact hpx
          · exact ih hxs m hm'

/-- The last occurrence of a Boolean move predicate. -/
theorem exists_last_bool (p : Move → Bool) (ρ : List Move)
    (h : ρ.any p = true) :
    ∃ (α : List Move) (m : Move) (β : List Move),
      ρ = α ++ m :: β ∧ (∀ x ∈ β, p x = false) ∧ p m = true := by
  induction ρ with
  | nil => change false = true at h; cases h
  | cons x xs ih =>
      change (p x || xs.any p) = true at h
      cases hxs : xs.any p with
      | true =>
          obtain ⟨α, m, β, heq, hβ, hm⟩ := ih hxs
          refine ⟨x :: α, m, β, ?_, hβ, hm⟩
          rw [heq]; rfl
      | false =>
          rw [hxs] at h
          have hpx : p x = true := by
            change (p x || false) = true at h
            cases hv : p x with
            | false =>
                rw [hv] at h
                change false = true at h
                cases h
            | true => rfl
          refine ⟨[], x, xs, rfl, ?_, hpx⟩
          exact any_eq_false hxs

theorem exists_isFreeB_false {ρ : List Move} (h : ρ.all isFreeB = false) :
    ∃ m ∈ ρ, isFreeB m = false := by
  induction ρ with
  | nil =>
      change true = false at h
      cases h
  | cons x xs ih =>
      change (isFreeB x && xs.all isFreeB) = false at h
      rw [Bool.and_eq_false_iff] at h
      rcases h with hx | hxs
      · exact ⟨x, List.mem_cons_self .., hx⟩
      · obtain ⟨m, hm, hmf⟩ := ih hxs
        exact ⟨m, List.mem_cons_of_mem x hm, hmf⟩

/-- A constructive witness form of "not every letter is free". -/
theorem exists_nonfree_of_not_all_free (ρ : List Move)
    (h : ¬ ∀ m ∈ ρ, FreeMove m) :
    ∃ m ∈ ρ, ¬ FreeMove m := by
  have hfalse : ρ.all isFreeB = false := by
    cases hv : ρ.all isFreeB with
    | false => rfl
    | true =>
        exfalso
        exact h (fun m hm =>
          isFreeB_eq_true_iff.mp ((List.all_eq_true.mp hv) m hm))
  obtain ⟨m, hm, hmf⟩ := exists_isFreeB_false hfalse
  exact ⟨m, hm, fun hfree => by
    have htrue : isFreeB m = true := isFreeB_eq_true_iff.mpr hfree
    rw [hmf] at htrue
    exact Bool.false_ne_true htrue⟩

/-- A pull and a raise are different letters. -/
theorem foundToTab_ne_tabToFound (c : Card) (b : Base) (d : Card) :
    (Move.foundToTab c b : Move) ≠ Move.tabToFound d := by
  intro h
  cases h

/-- A reversible non-free letter is a pull or a raise. -/
theorem nonfree_reversible_is_pull_or_raise {st : State} {m : Move}
    (hrev : reversibleAtW st m) (hnf : ¬ FreeMove m) :
    (∃ c : Card, m = Move.tabToFound c) ∨
      ∃ (c : Card) (b : Base), m = Move.foundToTab c b := by
  cases m with
  | draw => exact absurd (Or.inl rfl) hnf
  | wasteToFound c =>
      exact absurd hrev (wasteToFound_not_reversibleAtW st c)
  | wasteToTab c b =>
      exact absurd hrev (wasteToTab_not_reversibleAtW st c b)
  | tabToFound c => exact Or.inl ⟨c, rfl⟩
  | foundToTab c b => exact Or.inr ⟨c, b, rfl⟩
  | tabToTab c b => exact absurd (Or.inr ⟨c, b, rfl⟩) hnf

/-- Every letter of a witness play is reversible at its own origin. -/
theorem shuffle_letter_reversible {u v : State} {ρ : List Move}
    (h : ShufflePlayW u ρ v) : ∀ m ∈ ρ, ∃ st : State, reversibleAtW st m := by
  induction h with
  | nil st => intro m hm; exact absurd hm (by simp)
  | @cons st s₁ W m ρ hlet hstep hrest ih =>
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact ⟨st, hlet⟩
      · exact ih x hx'

/-- No waste letter survives a witness play. -/
theorem shuffle_letter_not_wasteToFound {u v : State} {ρ : List Move}
    (h : ShufflePlayW u ρ v) {c : Card} :
    Move.wasteToFound c ∉ ρ := by
  intro hmem
  obtain ⟨st, hrev⟩ := shuffle_letter_reversible h _ hmem
  exact wasteToFound_not_reversibleAtW st c hrev

theorem shuffle_letter_not_wasteToTab {u v : State} {ρ : List Move}
    (h : ShufflePlayW u ρ v) {c : Card} {b : Base} :
    Move.wasteToTab c b ∉ ρ := by
  intro hmem
  obtain ⟨st, hrev⟩ := shuffle_letter_reversible h _ hmem
  exact wasteToTab_not_reversibleAtW st c b hrev

/-! ## §1. Saturation invariance under free plays -/

/-- Cargo steps are transitive (local copy of `steps_trans`). -/
theorem cargo_steps_trans {Q : State → State → Prop} {w z u : State}
    (h₁ : Steps Q w z) : Steps Q z u → Steps Q w u := by
  induction h₁ with
  | refl _ => exact fun h₂ => h₂
  | cons h _ ih => exact fun h₂ => Steps.cons h (ih h₂)

/-- Saturation propagates forward along a cargo path. -/
theorem ssaturated_of_cargoPath' {a b : State} (h : CargoPath a b)
    (hs : SSaturated a) : SSaturated b := by
  intro c hc
  obtain ⟨z, hbz, hz⟩ := hc
  exact hs c ⟨z, cargo_steps_trans h hbz, hz⟩

/-- Saturation is invariant under a step that preserves foundations and
piles: `CanRaiseS` only reads those two components (via the flat
characterization at `WF`). -/
theorem canRaiseS_congr_found_piles {a b : State} (ha : a.WF) (hb : b.WF)
    (hf : a.found = b.found) (hp : a.piles = b.piles) (c : Card) :
    CanRaiseS a c ↔ CanRaiseS b c := by
  rw [canRaiseS_iff ha, canRaiseS_iff hb]
  have hnext : a.nextUp c = b.nextUp c := by
    unfold State.nextUp State.foundHeight
    rw [hf]
  constructor
  · rintro ⟨h, a0, bs, run, hshape, hseat, hdisj⟩
    refine ⟨by rw [← hnext]; exact h, a0, bs, run, ?_, ?_, ?_⟩
    · have hp' : (a.piles a0).faceUp = (b.piles a0).faceUp := by rw [hp]
      rw [← hp']; exact hshape
    · rcases hseat with hbs | hbk
      · exact Or.inl hbs
      · exact Or.inr ⟨by rw [← hp]; exact hbk.1, hbk.2⟩
    · rcases hdisj with hrun | htwin
      · exact Or.inl hrun
      · refine Or.inr ?_
        simp only [State.pileOfTop, State.topOf, hp] at htwin ⊢
        exact htwin
  · rintro ⟨h, a0, bs, run, hshape, hseat, hdisj⟩
    refine ⟨by rw [hnext]; exact h, a0, bs, run, ?_, ?_, ?_⟩
    · have hp' : (a.piles a0).faceUp = (b.piles a0).faceUp := by rw [hp]
      rw [hp']; exact hshape
    · rcases hseat with hbs | hbk
      · exact Or.inl hbs
      · exact Or.inr ⟨by rw [hp]; exact hbk.1, hbk.2⟩
    · rcases hdisj with hrun | htwin
      · exact Or.inl hrun
      · refine Or.inr ?_
        simp only [State.pileOfTop, State.topOf, hp] at htwin ⊢
        exact htwin

/-- Saturation is invariant under a successful draw. -/
theorem ssaturated_of_draw {u v : State} (h : State.step u Move.draw = some v)
    (hwf : u.WF) (hs : SSaturated u) : SSaturated v := by
  have hvf : v.WF := step_wf hwf h
  have hfound : v.found = u.found := stepDraw_found h
  have hpiles : v.piles = u.piles := stepDraw_piles h
  intro c hc
  exact hs c ((canRaiseS_congr_found_piles hwf hvf hfound.symm hpiles.symm c).mpr hc)

/-- Saturation propagates forward along a free play. -/
theorem ssaturated_free_prefix {u v : State} {ρ : List Move}
    (hplay : ShufflePlayW u ρ v) (hfree : ∀ m ∈ ρ, FreeMove m)
    (hwf : u.WF) (hs : SSaturated u) : SSaturated v := by
  induction hplay with
  | nil st => exact hs
  | @cons st s₁ W m ρ hlet hstep hrest ih =>
      have hfreeTail : ∀ x ∈ ρ, FreeMove x :=
        fun x hx => hfree x (List.mem_cons_of_mem m hx)
      have hwfS : s₁.WF := step_wf hwf hstep
      have hsS : SSaturated s₁ := by
        rcases hfree m (List.mem_cons_self ..) with hm | ⟨c, b, hm⟩
        · subst hm
          exact ssaturated_of_draw hstep hwf hs
        · subst hm
          exact ssaturated_of_cargoPath'
            (Steps.cons (show CargoLeg st s₁ from ⟨c, b, hstep, hlet⟩) (Steps.refl s₁)) hs
      exact ih hfreeTail hwfS hsS

/-- Saturation propagates backward along a free play. -/
theorem ssaturated_free_suffix {u v : State} {ρ : List Move}
    (hplay : ShufflePlayW u ρ v) (hfree : ∀ m ∈ ρ, FreeMove m)
    (hwf : u.WF) (hs : SSaturated v) : SSaturated u := by
  revert hwf hs
  induction hplay with
  | nil st => intro _ hs; exact hs
  | @cons st s₁ W m ρ hlet hstep hrest ih =>
      intro hwf hs
      have hfreeTail : ∀ x ∈ ρ, FreeMove x :=
        fun x hx => hfree x (List.mem_cons_of_mem m hx)
      have hwfS : s₁.WF := step_wf hwf hstep
      have hsS : SSaturated s₁ := ih hfreeTail hwfS hs
      rcases hfree m (List.mem_cons_self ..) with hm | ⟨c, b, hm⟩
      · subst hm
        intro x hx
        exact hsS x ((canRaiseS_congr_found_piles hwf hwfS
          (stepDraw_found hstep).symm (stepDraw_piles hstep).symm x).mp hx)
      · subst hm
        exact ssaturated_of_cargoPath'
          (cargoPath_symm hwf (Steps.cons
            (show CargoLeg st s₁ from ⟨c, b, hstep, hlet⟩) (Steps.refl s₁))) hsS

/-- A free play preserves every rung. -/
theorem rungAt_eq_of_free_play {u v : State} {ρ : List Move}
    (hplay : ShufflePlayW u ρ v) (hfree : ∀ m ∈ ρ, FreeMove m) :
    ∀ σ : Suit, rungAt v σ = rungAt u σ := by
  induction hplay with
  | nil st => intro σ; rfl
  | @cons st s₁ W m ρ hlet hstep hrest ih =>
      intro σ
      have hfreeTail : ∀ x ∈ ρ, FreeMove x :=
        fun x hx => hfree x (List.mem_cons_of_mem m hx)
      have htail := ih hfreeTail σ
      rcases hfree m (List.mem_cons_self ..) with hm | ⟨c, b, hm⟩
      · subst hm
        rw [htail, rungAt_draw hstep σ]
      · subst hm
        rw [htail, rungAt_tabToTab hstep σ]

/-! ## §2. The raise/raise square without reversibility hypotheses -/

/-- Two raises of the same suit cannot both fire in both orders. -/
theorem raise_same_suit_contra {u s1 s2 s12 : State} (hwf : u.WF) {c1 c2 : Card}
    (h1 : State.step u (Move.tabToFound c1) = some s1)
    (h2 : State.step u (Move.tabToFound c2) = some s2)
    (hsu : c1.suit = c2.suit)
    (h12 : State.step s1 (Move.tabToFound c2) = some s12) : False := by
  obtain ⟨hnextU1, a, hpa, hs1⟩ := step_tabToFound_inv h1
  obtain ⟨hnextU2, -⟩ := step_tabToFound_inv h2
  obtain ⟨hnextS2, -⟩ := step_tabToFound_inv h12
  have hu1 : c1.rank.toIdx = (u.found c1.suit).length := by
    have h := of_decide_eq_true hnextU1
    simpa [State.nextUp, State.foundHeight] using h
  have hu2 : c2.rank.toIdx = (u.found c2.suit).length := by
    have h := of_decide_eq_true hnextU2
    simpa [State.nextUp, State.foundHeight] using h
  have hs2l : c2.rank.toIdx = (s1.found c2.suit).length := by
    have h := of_decide_eq_true hnextS2
    simpa [State.nextUp, State.foundHeight] using h
  have hs1f : s1.found c2.suit = u.found c1.suit ++ [c1] := by
    rw [hs1]
    show (u.setFound c1.suit (u.found c1.suit ++ [c1])).found c2.suit = _
    rw [← hsu, setFound_found_self]
  have hlen : (s1.found c2.suit).length = (u.found c1.suit).length + 1 := by
    rw [hs1f, List.length_append]
    simp
  have hc2c1 : c2 = c1 := by
    have hr : c2.rank = c1.rank := by
      apply Rank.toIdx_inj
      rw [hu2, ← hsu, ← hu1]
    cases c2
    cases c1
    simp_all
  rw [← hc2c1] at hu1
  rw [hsu] at hlen
  omega

/-- The raise/raise square, with the reversibility hypotheses removed. -/
theorem raise_raise_square_norev {st s1 s2 s12 s21 : State} {c1 c2 : Card}
    (hwf : st.WF)
    (h1 : State.step st (Move.tabToFound c1) = some s1)
    (h2 : State.step st (Move.tabToFound c2) = some s2)
    (h12 : State.step s1 (Move.tabToFound c2) = some s12)
    (h21 : State.step s2 (Move.tabToFound c1) = some s21) :
    s12 = s21 := by
  by_cases hsu : c1.suit = c2.suit
  · exfalso
    exact raise_same_suit_contra hwf h1 h2 hsu h12
  · obtain ⟨w, hw12, hw21⟩ := twin_raise_square hwf hsu h1 h2
    have e1 : s12 = w := by
      rw [h12] at hw12
      exact Option.some.inj hw12
    have e2 : s21 = w := by
      rw [h21] at hw21
      exact Option.some.inj hw21
    rw [e1, e2]

/-! ## §3. Crossing cancellation -/

/-- **CROSSING CANCELLATION.**  The four-letter block
`pull d ; pull c ; raise d ; raise c` returns to its origin.
The two pulls are undone by `step_tabToFound_of_foundToTab`, giving the
other raise order at the middle state; the raise/raise square then
identifies the two landings. -/
theorem crossing_cancel {st s1 mid s12 back : State} {c d : Card}
    {bc bd : Base}
    (hwf : st.WF)
    (h1 : State.step st (Move.foundToTab d bd) = some s1)
    (h2 : State.step s1 (Move.foundToTab c bc) = some mid)
    (h3 : State.step mid (Move.tabToFound d) = some s12)
    (h4 : State.step s12 (Move.tabToFound c) = some back) :
    back = st := by
  have hs1wf : s1.WF := step_wf hwf h1
  have hmidwf : mid.WF := step_wf hs1wf h2
  have h1inv : State.step s1 (Move.tabToFound d) = some st :=
    step_tabToFound_of_foundToTab hwf h1
  have h2inv : State.step mid (Move.tabToFound c) = some s1 :=
    step_tabToFound_of_foundToTab hs1wf h2
  exact raise_raise_square_norev hmidwf h3 h2inv h4 h1inv

/-- **THE CROSSING BLOCK IS DELETABLE.**  A contiguous
`pull d ; pull c ; raise d ; raise c` loop inside a witness play can be
dropped. -/
def CrossingBlock (u v : State) (ρ : List Move) : Prop :=
  ∃ (α β : List Move) (c d : Card) (bd bc : Base)
    (A B C D E : State),
    ρ = α ++ [Move.foundToTab d bd, Move.foundToTab c bc,
              Move.tabToFound d, Move.tabToFound c] ++ β ∧
    ShufflePlayW u α A ∧
    State.step A (Move.foundToTab d bd) = some B ∧
    State.step B (Move.foundToTab c bc) = some C ∧
    State.step C (Move.tabToFound d) = some D ∧
    State.step D (Move.tabToFound c) = some E ∧
    ShufflePlayW A β v

theorem crossing_block_delete {u v : State} {ρ : List Move}
    (huwf : u.WF) (h : CrossingBlock u v ρ) :
    ∃ ρ' : List Move, ShufflePlayW u ρ' v ∧ ρ'.length < ρ.length := by
  obtain ⟨α, β, c, d, bd, bc, A, B, C, D, E, hρ, hα, h1, h2, h3, h4, hβ⟩ := h
  have hAwf : A.WF := SatDifferCensus.ShufflePlayW.wf_end hα huwf
  have hEA : E = A := crossing_cancel hAwf h1 h2 h3 h4
  refine ⟨α ++ β, ShufflePlayW_append hα hβ, ?_⟩
  rw [hρ]
  simp only [List.length_append, List.length_cons, List.length_nil]
  omega

/-! ## §4. The adjacent valley turn (same-card cancellation) -/

/-- **SAME-CARD VALLEY CANCELLATION.**  If a witness play reaches `A'`,
pulls `c` onto `b` to reach `B`, and immediately raises `c`, the two
letters delete. -/
theorem valley_cancel_same {A A' B C : State} {ρ₁ ρ₂ : List Move}
    {c : Card} {b : Base}
    (hwf : A.WF)
    (h₁ : ShufflePlayW A ρ₁ A')
    (hpull : State.step A' (Move.foundToTab c b) = some B)
    (h₂ : ShufflePlayW B (Move.tabToFound c :: ρ₂) C) :
    ShufflePlayW A (ρ₁ ++ ρ₂) C := by
  have hA' : A'.WF := SatDifferCensus.ShufflePlayW.wf_end h₁ hwf
  have hback : State.step B (Move.tabToFound c) = some A' :=
    step_tabToFound_of_foundToTab hA' hpull
  cases h₂ with
  | cons hrev hstep hrest =>
      rename_i B'
      have hBB' : B' = A' := Option.some.inj (hstep.symm.trans hback)
      subst hBB'
      exact ShufflePlayW_append h₁ hrest

/-- Adjacent valley elimination in the same-card case. -/
theorem valley_elim_pull_raise_same
    {A A' F C : State} {ρ₁ ρ₂ : List Move} {c : Card} {b : Base}
    (hwf : A.WF)
    (h₁ : ShufflePlayW A ρ₁ A')
    (hpull : State.step A' (Move.foundToTab c b) = some F)
    (hrev : reversibleAtW F (Move.tabToFound c))
    (hstep : State.step F (Move.tabToFound c) = some A')
    (h₂ : ShufflePlayW A' ρ₂ C) :
    ShufflePlayW A (ρ₁ ++ ρ₂) C :=
  valley_cancel_same hwf h₁ hpull (Walk.cons hrev hstep h₂)

/-! ## §5. List decompositions -/

/-- Split a witness shuffle at any cut of its move list. -/
theorem ShufflePlayW_split {u v : State} {ρ : List Move}
    (h : ShufflePlayW u ρ v) :
    ∀ (a b : List Move), ρ = a ++ b →
      ∃ F : State, ShufflePlayW u a F ∧ ShufflePlayW F b v := by
  induction h with
  | nil st =>
      intro a b hab
      have hab' : a ++ b = [] := hab.symm
      have ha : a = [] := (List.append_eq_nil_iff.mp hab').1
      have hb : b = [] := (List.append_eq_nil_iff.mp hab').2
      subst ha; subst hb
      exact ⟨st, Walk.nil st, Walk.nil st⟩
  | @cons st s₁ W m ρ hlet hstep hrest ih =>
      intro a b hab
      cases a with
      | nil =>
          have hb : b = m :: ρ := hab.symm
          subst hb
          exact ⟨st, Walk.nil st, Walk.cons hlet hstep hrest⟩
      | cons m' a' =>
          simp only [List.cons_append] at hab
          injection hab with hm htl
          subst hm
          obtain ⟨F, h1, h2⟩ := ih a' b htl
          exact ⟨F, Walk.cons hlet hstep h1, h2⟩

/-- The first non-free letter: a free prefix, then a non-free letter. -/
theorem exists_first_nonfree (ρ : List Move)
    (h : ∃ m ∈ ρ, ¬ FreeMove m) :
    ∃ (α : List Move) (m : Move) (β : List Move),
      ρ = α ++ m :: β ∧ (∀ x ∈ α, FreeMove x) ∧ ¬ FreeMove m := by
  obtain ⟨m₀, hm₀, hnf₀⟩ := h
  have hp₀ : (fun m => !isFreeB m) m₀ = true := by
    change (!isFreeB m₀) = true
    have hf : isFreeB m₀ = false := isFreeB_eq_false_iff.mpr hnf₀
    rw [hf]; rfl
  obtain ⟨α, m, β, heq, hα, hm⟩ :=
    exists_first_bool (fun m => !isFreeB m) ρ
      (any_eq_true_of_mem hm₀ hp₀)
  exact ⟨α, m, β, heq, fun x hx => not_not_isFreeB_eq_false (hα x hx),
    not_not_isFreeB_eq_true hm⟩

/-- The last non-free letter: a non-free letter, then a free tail. -/
theorem exists_last_nonfree (ρ : List Move)
    (h : ∃ m ∈ ρ, ¬ FreeMove m) :
    ∃ (α : List Move) (m : Move) (β : List Move),
      ρ = α ++ m :: β ∧ (∀ x ∈ β, FreeMove x) ∧ ¬ FreeMove m := by
  obtain ⟨m₀, hm₀, hnf₀⟩ := h
  have hp₀ : (fun m => !isFreeB m) m₀ = true := by
    change (!isFreeB m₀) = true
    have hf : isFreeB m₀ = false := isFreeB_eq_false_iff.mpr hnf₀
    rw [hf]; rfl
  obtain ⟨α, m, β, heq, hβ, hm⟩ :=
    exists_last_bool (fun m => !isFreeB m) ρ
      (any_eq_true_of_mem hm₀ hp₀)
  exact ⟨α, m, β, heq, fun x hx => not_not_isFreeB_eq_false (hβ x hx),
    not_not_isFreeB_eq_true hm⟩

/-- The last pull in a list, with a pull-free tail. -/
theorem exists_last_pull (ρ : List Move)
    (h : ∃ c b, Move.foundToTab c b ∈ ρ) :
    ∃ (α : List Move) (c : Card) (b : Base) (β : List Move),
      ρ = α ++ Move.foundToTab c b :: β ∧
        ∀ c' b', Move.foundToTab c' b' ∉ β := by
  obtain ⟨c₀, b₀, hm₀⟩ := h
  have hp₀ : isPullB (Move.foundToTab c₀ b₀) = true := rfl
  obtain ⟨α, m, β, heq, hβ, hm⟩ :=
    exists_last_bool isPullB ρ (any_eq_true_of_mem hm₀ hp₀)
  obtain ⟨c, b, rfl⟩ := isPullB_eq_true_iff.mp hm
  refine ⟨α, c, b, β, heq, ?_⟩
  intro c' b' hmem
  have hfalse : isPullB (Move.foundToTab c' b') = false :=
    hβ (Move.foundToTab c' b') hmem
  change true = false at hfalse
  cases hfalse

/-- The first raise in a list: a raise-free prefix, then a raise. -/
theorem exists_first_raise (ρ : List Move)
    (h : ∃ d : Card, Move.tabToFound d ∈ ρ) :
    ∃ (ρ₁ : List Move) (d : Card) (ρ₂ : List Move),
      ρ = ρ₁ ++ Move.tabToFound d :: ρ₂ ∧
        ∀ m ∈ ρ₁, ∀ e : Card, m ≠ Move.tabToFound e := by
  obtain ⟨d₀, hm₀⟩ := h
  have hp₀ : isRaiseB (Move.tabToFound d₀) = true := rfl
  obtain ⟨ρ₁, m, ρ₂, heq, hρ₁, hm⟩ :=
    exists_first_bool isRaiseB ρ (any_eq_true_of_mem hm₀ hp₀)
  obtain ⟨d, rfl⟩ := isRaiseB_eq_true_iff.mp hm
  refine ⟨ρ₁, d, ρ₂, heq, ?_⟩
  intro m' hm' e hme
  have hfalse : isRaiseB m' = false := hρ₁ m' hm'
  rw [hme] at hfalse
  change true = false at hfalse
  cases hfalse

/-- If a free prefix is followed by a non-free letter, and another
decomposition also has a free prefix and a non-free head, the heads
agree.  (One-sided uniqueness of the first non-free decomposition.) -/
theorem first_nonfree_eq_of_free_prefix :
    ∀ (α : List Move), (∀ x ∈ α, FreeMove x) →
      ∀ {m : Move}, ¬ FreeMove m →
        ∀ {β : List Move} {α' : List Move}, (∀ x ∈ α', FreeMove x) →
          ∀ {m' : Move}, ¬ FreeMove m' → ∀ {β' : List Move},
            α ++ m :: β = α' ++ m' :: β' → m = m' := by
  intro α
  induction α with
  | nil =>
      intro _ m hm β α' hα' m' hm' β' h
      cases α' with
      | nil =>
          simp only [List.nil_append] at h
          exact (List.cons.inj h).1
      | cons y α₂ =>
          simp only [List.nil_append, List.cons_append] at h
          have hmy : m = y := (List.cons.inj h).1
          have hyfree : FreeMove y := hα' y (List.mem_cons_self ..)
          exact absurd (hmy.symm ▸ hyfree) hm
  | cons x α₁ ih =>
      intro hα m hm β α' hα' m' hm' β' h
      cases α' with
      | nil =>
          simp only [List.cons_append, List.nil_append] at h
          have hxm' : x = m' := (List.cons.inj h).1
          have hxfree : FreeMove x := hα x (List.mem_cons_self ..)
          exact absurd (hxm' ▸ hxfree) hm'
      | cons y α₂ =>
          simp only [List.cons_append] at h
          have htail : α₁ ++ m :: β = α₂ ++ m' :: β' := (List.cons.inj h).2
          have h₁ : ∀ z ∈ α₁, FreeMove z :=
            fun z hz => hα z (List.mem_cons_of_mem x hz)
          have h₂ : ∀ z ∈ α₂, FreeMove z :=
            fun z hz => hα' z (List.mem_cons_of_mem y hz)
          exact ih h₁ hm h₂ hm' htail

/-! ## §6. The first non-free letter is a pull; the last is a raise -/

/-- A saturated state carries no vanilla raise. -/
theorem no_raise_of_saturated {u : State} (hs : SSaturated u) (c : Card) :
    ¬ CanRaise u c :=
  fun h => hs c (CanRaiseS.now c h)

/-- A saturated `WF` state carries no reversible `tabToFound`. -/
theorem not_reversible_tabToFound_of_saturated {u : State} (hwf : u.WF)
    (hs : SSaturated u) (c : Card) :
    ¬ reversibleAtW u (Move.tabToFound c) :=
  fun h =>
    no_raise_of_saturated hs c
      (SatDifferCensus.canRaise_of_tabToFoundR
        ((tabToFoundR_iff_reversibleAtW hwf c).mpr h))

/-- A pull's card is S-live at the landing (local copy of
`FirstExcursion.pull_card_live`). -/
theorem pull_card_live {st w : State} (hwf : st.WF) {c : Card} {b : Base}
    (hstep : State.step st (Move.foundToTab c b) = some w) :
    CanRaiseS w c := by
  obtain ⟨c', htop, hc', -, -⟩ := step_foundToTab_inv hstep
  rw [hc'] at htop
  have hidx : c.rank.toIdx + 1 = rungAt st c.suit :=
    SatDifferCensus.foundTop_rank_succ hwf htop
  have hrung : rungAt w c.suit = rungAt st c.suit - 1 := by
    have h := rungAt_foundToTab hstep c.suit
    rw [ite_eq_left rfl] at h
    exact h
  have hfh : w.foundHeight c.suit = c.rank.toIdx := by
    show (w.found c.suit).length = c.rank.toIdx
    rw [show (w.found c.suit).length = rungAt w c.suit from rfl, hrung]
    omega
  have hnext : w.nextUp c = true := by
    unfold State.nextUp
    rw [hfh]
    exact decide_eq_true rfl
  exact CanRaiseS.now c (SatDifferCensus.canRaise_post_of_pull hwf hstep hnext)

theorem first_nonfree_pull {u v : State} {ρ : List Move}
    (huwf : u.WF) (hu : SSaturated u) (hplay : ShufflePlayW u ρ v)
    (hex : ∃ m ∈ ρ, ¬ FreeMove m) :
    ∃ (α : List Move) (c : Card) (b : Base) (β : List Move),
      ρ = α ++ Move.foundToTab c b :: β ∧ (∀ x ∈ α, FreeMove x) := by
  obtain ⟨α, m, β, heq, hα, hm⟩ := exists_first_nonfree ρ hex
  obtain ⟨F, hαplay, hrest⟩ := ShufflePlayW_split hplay α (m :: β) heq
  have hFwf : F.WF := SatDifferCensus.ShufflePlayW.wf_end hαplay huwf
  have hFsat : SSaturated F := ssaturated_free_prefix hαplay hα huwf hu
  cases hrest with
  | cons hrev hstep htail =>
      rcases nonfree_reversible_is_pull_or_raise hrev hm with ⟨c, rfl⟩ | ⟨c, b, rfl⟩
      · exact absurd hrev (not_reversible_tabToFound_of_saturated hFwf hFsat c)
      · exact ⟨α, c, b, β, heq, hα⟩

theorem last_nonfree_raise {u v : State} {ρ : List Move}
    (huwf : u.WF) (hv : SSaturated v) (hplay : ShufflePlayW u ρ v)
    (hex : ∃ m ∈ ρ, ¬ FreeMove m) :
    ∃ (α : List Move) (d : Card) (β : List Move),
      ρ = α ++ Move.tabToFound d :: β ∧ (∀ x ∈ β, FreeMove x) := by
  obtain ⟨α, m, β, heq, hβ, hm⟩ := exists_last_nonfree ρ hex
  obtain ⟨F, hαplay, hrest⟩ := ShufflePlayW_split hplay α (m :: β) heq
  have hFwf : F.WF := SatDifferCensus.ShufflePlayW.wf_end hαplay huwf
  cases hrest with
  | cons hrev hstep htail =>
      have hs₁wf := step_wf hFwf hstep
      have hs₁sat := ssaturated_free_suffix htail hβ hs₁wf hv
      rcases nonfree_reversible_is_pull_or_raise hrev hm with ⟨c, rfl⟩ | ⟨c, b, rfl⟩
      · exact ⟨α, c, β, heq, hβ⟩
      · exact absurd (pull_card_live hFwf hstep) (hs₁sat c)

/-! ## §7. The valley split and `valley_exists` -/

/-- A valley split at the state `F`: the play reaches `F` with its last
non-free letter a pull (then a free tail), and leaves `F` with a raise.
Free (draw/slide) letters are allowed at the turn. -/
def ValleySplitAt (u v : State) (ρ : List Move) (F : State) : Prop :=
  ∃ (left right : List Move) (c d : Card) (b : Base)
    (pre post tail : List Move),
    ρ = left ++ right ∧
    ShufflePlayW u left F ∧
    ShufflePlayW F right v ∧
    left = pre ++ Move.foundToTab c b :: post ∧
    (∀ m ∈ post, FreeMove m) ∧
    right = Move.tabToFound d :: tail

/-- A witness play has a valley split. -/
def ValleySplit (u v : State) (ρ : List Move) : Prop :=
  ∃ F : State, ValleySplitAt u v ρ F

/-- **VALLEY EXISTS.**  Between saturated `WF` endpoints with differing
rungs, every witness play has a valley split: the last non-free letter
of the down leg is a pull and the first letter of the up leg is a raise,
with slides allowed at the split. -/
theorem valley_exists {u v : State} {ρ : List Move}
    (huwf : u.WF) (hu : SSaturated u) (hv : SSaturated v)
    (hdiff : ∃ σ : Suit, rungAt u σ ≠ rungAt v σ)
    (hplay : ShufflePlayW u ρ v) :
    ValleySplit u v ρ := by
  -- there is at least one non-free letter
  have hnonfree : ∃ m ∈ ρ, ¬ FreeMove m := by
    apply exists_nonfree_of_not_all_free
    intro hall
    have hr := rungAt_eq_of_free_play hplay hall
    obtain ⟨σ, hσ⟩ := hdiff
    exact hσ (hr σ).symm
  -- the first non-free letter is a pull
  obtain ⟨α₀, c₀, b₀, β₀, hpullEq, hα₀free⟩ :=
    first_nonfree_pull huwf hu hplay hnonfree
  -- the last non-free letter is a raise, so some raise occurs
  obtain ⟨αR, dR, βR, hREq, hβRfree⟩ :=
    last_nonfree_raise huwf hv hplay hnonfree
  have hraiseMem : ∃ d : Card, Move.tabToFound d ∈ ρ := by
    refine ⟨dR, ?_⟩
    rw [hREq]
    exact List.mem_append.mpr (Or.inr (List.mem_cons_self ..))
  obtain ⟨ρ₁, d₁, ρ₂, hρ₁Eq, hnoRaise⟩ := exists_first_raise ρ hraiseMem
  -- the prefix before the first raise contains a non-free letter
  have hρ₁nonfree : ∃ m ∈ ρ₁, ¬ FreeMove m := by
    apply exists_nonfree_of_not_all_free
    intro hall
    have heqhead : Move.tabToFound d₁ = Move.foundToTab c₀ b₀ :=
      first_nonfree_eq_of_free_prefix (α := ρ₁) hall
        (m := Move.tabToFound d₁) (by intro he; rcases he with h | ⟨c, b, h⟩ <;> cases h)
        (β := ρ₂) (α' := α₀) hα₀free
        (m' := Move.foundToTab c₀ b₀) (by intro he; rcases he with h | ⟨c, b, h⟩ <;> cases h)
        (β' := β₀) (hρ₁Eq.symm.trans hpullEq)
    exact (foundToTab_ne_tabToFound c₀ b₀ d₁) heqhead.symm
  -- that non-free letter is a pull
  obtain ⟨m₁, hm₁mem, hm₁nf⟩ := hρ₁nonfree
  have hm₁pull : ∃ c b, m₁ = Move.foundToTab c b := by
    cases m₁ with
    | draw => exfalso; exact absurd (Or.inl rfl) hm₁nf
    | wasteToFound c =>
        exfalso
        exact absurd (by
          rw [hρ₁Eq]
          exact List.mem_append_left (Move.tabToFound d₁ :: ρ₂) hm₁mem)
          (shuffle_letter_not_wasteToFound hplay)
    | wasteToTab c b =>
        exfalso
        exact absurd (by
          rw [hρ₁Eq]
          exact List.mem_append_left (Move.tabToFound d₁ :: ρ₂) hm₁mem)
          (shuffle_letter_not_wasteToTab hplay)
    | tabToFound e => exfalso; exact absurd rfl (hnoRaise _ hm₁mem e)
    | foundToTab c b => exact ⟨c, b, rfl⟩
    | tabToTab c b => exfalso; exact absurd (Or.inr ⟨c, b, rfl⟩) hm₁nf
  -- take the last pull of the prefix
  obtain ⟨c, b, hpullmem⟩ := hm₁pull
  have hpullmem₁ : Move.foundToTab c b ∈ ρ₁ := by
    rw [← hpullmem]; exact hm₁mem
  obtain ⟨α₁, c₁, b₁, β₁, hρ₁shape, hnoPullβ⟩ := exists_last_pull ρ₁ ⟨c, b, hpullmem₁⟩
  -- the tail after the last pull is free
  have hβ₁free : ∀ m ∈ β₁, FreeMove m := by
    intro m hm
    have hmemρ₁ : m ∈ ρ₁ := by
      rw [hρ₁shape]
      exact List.mem_append.mpr (Or.inr (List.mem_cons_of_mem _ hm))
    cases m with
    | draw => exact Or.inl rfl
    | tabToTab c' b' => exact Or.inr ⟨c', b', rfl⟩
    | tabToFound e => exfalso; exact absurd rfl (hnoRaise _ hmemρ₁ e)
    | wasteToFound c' =>
        exfalso
        exact absurd (by
          rw [hρ₁Eq]
          exact List.mem_append_left (Move.tabToFound d₁ :: ρ₂) hmemρ₁)
          (shuffle_letter_not_wasteToFound hplay)
    | wasteToTab c' b' =>
        exfalso
        exact absurd (by
          rw [hρ₁Eq]
          exact List.mem_append_left (Move.tabToFound d₁ :: ρ₂) hmemρ₁)
          (shuffle_letter_not_wasteToTab hplay)
    | foundToTab c' b' => exfalso; exact (hnoPullβ c' b') hm
  -- split the play at the prefix
  obtain ⟨F, hleft, hright⟩ := ShufflePlayW_split hplay ρ₁ (Move.tabToFound d₁ :: ρ₂) hρ₁Eq
  exact ⟨F, ρ₁, Move.tabToFound d₁ :: ρ₂, c₁, d₁, b₁,
    α₁, β₁, ρ₂, hρ₁Eq, hleft, hright, hρ₁shape, hβ₁free, rfl⟩

/-! ## §8. The reduction to `SatDifferForkWF` -/

/-- **VALLEY ELIMINATION AT VALLEY BOTTOMS (constructive form).**  Every
valley split either already exhibits a fork at its bottom, or yields a
strictly shorter witness play between the same endpoints.  This is the
named residual hypothesis of the reduction; the local `pull/raise`
cancellation rows are meant to discharge its second disjunct when the
bottom is not a fork.  The disjunctive form avoids a classical case
split on `∃ x, ForkWitness F x` (which would import `Classical.choice`). -/
def ValleyElimNonfork : Prop :=
  ∀ (u v : State) (ρ : List Move) (F : State),
    u.WF → SSaturated u → SSaturated v →
    ShufflePlayW u ρ v →
    ValleySplitAt u v ρ F →
    (∃ x : Card, ForkWitness F x) ∨
      (∃ ρ' : List Move, ShufflePlayW u ρ' v ∧ ρ'.length < ρ.length)

/-- The accepted shortest-play input for the reduction (the task allows
this as an explicit hypothesis). -/
def ShortestPlayExists : Prop :=
  ∀ (u v : State), u.WF → SSaturated u → SSaturated v →
    sameOrbitSetoid.r u v →
    (∃ σ : Suit, rungAt u σ ≠ rungAt v σ) →
    ∃ ρ : List Move, ShufflePlayW u ρ v ∧
      ∀ ρ' : List Move, ShufflePlayW u ρ' v → ρ.length ≤ ρ'.length

/-- **THE REDUCTION.**  `ValleyElimNonfork` plus shortest-play existence
implies the `WF`-gated ceiling residue `SatDifferForkWF`: take a shortest
witness play between two saturated class-mates with differing rungs, find
a valley split, and apply valley elimination.  If the elimination branch
fires, minimality is contradicted; hence the bottom is a fork. -/
theorem satDifferForkWF_of_valleyElimNonfork
    (h : ValleyElimNonfork) (hmin : ShortestPlayExists) :
    SatDifferForkWF := by
  intro u v huwf hsu hsv hcls hdiff
  obtain ⟨ρ, hρ, hminlen⟩ := hmin u v huwf hsu hsv hcls hdiff
  obtain ⟨F, hFsplit⟩ := valley_exists huwf hsu hsv hdiff hρ
  obtain ⟨left, right, c, d, b, pre, post, tail,
    hsplitEq, hleft, hright, hshape, hfree, hrightShape⟩ := hFsplit
  rcases h u v ρ F huwf hsu hsv hρ
      ⟨left, right, c, d, b, pre, post, tail,
        hsplitEq, hleft, hright, hshape, hfree, hrightShape⟩ with
    hfork | ⟨ρ', hρ'play, hρ'len⟩
  · obtain ⟨x, hx⟩ := hfork
    exact ⟨F, x, RevEqW_symm (shufflePlayW_revEqW hleft), hx⟩
  · exfalso
    exact (Nat.not_lt.mpr (hminlen ρ' hρ'play)) hρ'len

/-! ## §9. The crossing valley and its named locator -/

/-- **THE LOCATOR — WITHDRAWN, FALSE AS STATED.**  Two independent defects,
both kernel-checked in `Orig2/ForkLocatorRefute.lean`
(`LocatorRefute.valleyCrossingLocator_false`):

1. **Existence:** the partner letters `pull d` (before) and `raise c` (after)
   need not occur in the play (witness: `pull A♠ ; raise A♦`, length 2).
2. **Contiguity is syntactic:** commuting the interior produces a *different*
   play `ρ'`; a block found after reordering lives in `ρ'`, not in `ρ`.

The corrected targets live in `Orig2/Fork/ForkLocator.lean`:
`ValleyCrossingPartnerLocator` (partners adjacent, block in `ρ`; proved) and
`CrossingBracketNormalizer` (partners with arbitrary interior; conclusion is
a re-run play `ρ'` of the same length with a contiguous block).  This
definition is kept only so the refutation can name it. -/
def ValleyCrossingLocator : Prop :=
  ∀ (u v : State) (ρ : List Move) (F : State)
    (left right : List Move) (c d : Card) (b : Base) (tail : List Move),
    u.WF → ShufflePlayW u ρ v →
    ρ = left ++ [Move.foundToTab c b, Move.tabToFound d] ++ right →
    ShufflePlayW u left F →
    c ≠ d → c.suit ≠ d.suit →
    CrossingBlock u v ρ

/-- The crossing branch of valley elimination, conditional on the named
locator.  The locator places the four-letter block; `crossing_block_delete`
then shortens the play. -/
theorem valley_elim_pull_raise_cross_of_locator (hloc : ValleyCrossingLocator)
    {u v : State} {ρ : List Move} {F : State}
    {left right : List Move} {c d : Card} {b : Base} {tail : List Move}
    (huwf : u.WF) (hplay : ShufflePlayW u ρ v)
    (hdecomp : ρ = left ++ [Move.foundToTab c b, Move.tabToFound d] ++ right)
    (hleft : ShufflePlayW u left F)
    (hcd : c ≠ d) (hsuit : c.suit ≠ d.suit) :
    ∃ ρ' : List Move, ShufflePlayW u ρ' v ∧ ρ'.length < ρ.length :=
  crossing_block_delete huwf (hloc u v ρ F left right c d b tail
    huwf hplay hdecomp hleft hcd hsuit)

/-- **ADJACENT VALLEY ELIMINATION.**  The combined pull/raise turn:
either the same card (`c = d`, unconditional) or a genuine crossing
(`c ≠ d` and different suits, conditional on `ValleyCrossingLocator`).
In both cases the two-letter turn is deleted and the play strictly
shortens.  Free letters at the turn are handled by the caller; this is
the adjacent-turn core. -/
theorem valley_elim_pull_raise (hloc : ValleyCrossingLocator)
    {u v F : State} {left right : List Move} {c d : Card} {b : Base}
    (huwf : u.WF)
    (hplay : ShufflePlayW u (left ++ [Move.foundToTab c b, Move.tabToFound d] ++ right) v)
    (hleft : ShufflePlayW u left F)
    (hturn : c = d ∨ (c ≠ d ∧ c.suit ≠ d.suit)) :
    ∃ ρ' : List Move, ShufflePlayW u ρ' v ∧
      ρ'.length < (left ++ [Move.foundToTab c b, Move.tabToFound d] ++ right).length := by
  obtain ⟨F', hleft', hrest⟩ := ShufflePlayW_split hplay left
    ([Move.foundToTab c b, Move.tabToFound d] ++ right) (by simp only [List.append_assoc])
  have hF : F' = F := by
    have h1 := Walk_run (fun st m => reversibleAtW st m) hleft'
    have h2 := Walk_run (fun st m => reversibleAtW st m) hleft
    exact Option.some.inj (h1.symm.trans h2)
  subst hF
  cases hrest with
  | cons hrevPull hstepPull hrest1 =>
      cases hrest1 with
      | cons hrevRaise hstepRaise hright =>
          rcases hturn with hcd | ⟨hcd, hsuit⟩
          · subst hcd
            refine ⟨left ++ right,
              valley_cancel_same huwf hleft hstepPull (Walk.cons hrevRaise hstepRaise hright), ?_⟩
            simp only [List.length_append, List.length_cons, List.length_nil]
            omega
          · have hblock : CrossingBlock u v
                (left ++ [Move.foundToTab c b, Move.tabToFound d] ++ right) :=
              hloc u v _ _ left right c d b right huwf hplay rfl hleft hcd hsuit
            exact crossing_block_delete huwf hblock

end ValleyElim

#print axioms ValleyElim.crossing_cancel
#print axioms ValleyElim.crossing_block_delete
#print axioms ValleyElim.valley_cancel_same
#print axioms ValleyElim.valley_elim_pull_raise_same
#print axioms ValleyElim.valley_exists
#print axioms ValleyElim.satDifferForkWF_of_valleyElimNonfork
#print axioms ValleyElim.valley_elim_pull_raise_cross_of_locator

#print axioms ValleyElim.exists_nonfree_of_not_all_free
#print axioms ValleyElim.rungAt_eq_of_free_play
#print axioms ValleyElim.first_nonfree_pull
#print axioms ValleyElim.last_nonfree_raise
#print axioms ValleyElim.ssaturated_free_prefix
#print axioms ValleyElim.ssaturated_free_suffix
#print axioms ValleyElim.ShufflePlayW_split

#print axioms ValleyElim.exists_first_nonfree
#print axioms ValleyElim.nonfree_reversible_is_pull_or_raise
#print axioms ValleyElim.not_reversible_tabToFound_of_saturated
#print axioms ValleyElim.pull_card_live
#print axioms ValleyElim.raise_same_suit_contra

#print axioms ValleyElim.valley_elim_pull_raise
