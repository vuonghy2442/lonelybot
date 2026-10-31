import Orig2.ForkBubble
import Orig2.ForkLocator
import Orig2.ForkCommuteSlide

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-!
# Orig2/ForkNormalize — the exact commutation rows and the bracket normalizer

PROMOTED from `Temp/Norm_General.lean` (2026-11-01); scratch witnesses
`Temp/Norm_Bubble.lean` and `Temp/Norm_General.lean` remain the compile
transcripts.  This card adds, on top of `Orig2/ForkBubble`:

* the two directional window writers `move_right_comm` / `move_left_comm`;
* `crossingBracketNormalizer_of_commutes`, the play-level reordering that
  turns the decomp

  `α ++ [pull d bd] ++ β ++ [pull c b ; raise d] ++ γ ++ [raise c] ++ δ ++ ε`

  into a SAME-LENGTH play whose four crossing letters are contiguous;
* `crossingBracketNormalizer_of_slideRows`, the explicit reduction from the
  two missing slide endpoint rows (`SlidePullRow`, `SlideRaiseRow`) plus the
  swapped-order transport schemas;
* `crossingBracketNormalizer_of_noslide`, the slide-free corollary.

The target `LocatorCorrected.CrossingBracketNormalizer` is a `def : Prop`, so
"proving it" means producing an inhabitant.  The unconditional inhabitant
would need both slide rows AND both transport schemas; the conditional
theorems below isolate exactly what remains.  No `sorry`, no
`Classical.choice`, no `native_decide`.
-/


open ValleyElim
open CommuteStep

namespace Bubble

/-! ## §1. The endpoint row and its reversible closure -/

/-- **THE ENDPOINT ROW.**  The two orders of `m1 ; m2` and `m2 ; m1` land on
the same state (whenever both are legal).  For slide-free letters this is
`CommuteStep.diamond_noslide`; for slides it is the missing
`step_comm_slide_pull` / `step_comm_slide_raise`. -/
def DiamondAt (st : State) (m1 m2 : Move) : Prop :=
  ∀ (s1 s2 s12 s21 : State),
    State.step st m1 = some s1 → State.step st m2 = some s2 →
    State.step s1 m2 = some s12 → State.step s2 m1 = some s21 →
    s12 = s21

/-- **THE CONSUMED ROW.**  `DiamondAt`, with the two reversibility witnesses
that the play supplies (and that the row may need). -/
def Commutes (st : State) (m1 m2 : Move) : Prop :=
  reversibleAtW st m1 → reversibleAtW st m2 → DiamondAt st m1 m2

/-- Slide-free pairs commute for free: this is `diamond_noslide`. -/
theorem commutes_noslide {st : State} {m1 m2 : Move}
    (hwf : st.WF) (h1 : NoSlide m1) (h2 : NoSlide m2) : Commutes st m1 m2 :=
  fun hrev1 hrev2 s1 s2 s12 s21 hstep1 hstep2 hstep12 hstep21 =>
    diamond_noslide hwf hrev1 hrev2 h1 h2 hstep1 hstep2 hstep12 hstep21

/-- The endpoint row is symmetric in its two letters. -/
theorem diamondAt_symm {st : State} {m1 m2 : Move} (h : DiamondAt st m1 m2) :
    DiamondAt st m2 m1 := by
  intro p q pq qp hp hq hpq hqp
  exact (h q p qp pq hq hp hqp hpq).symm

/-- `Commutes` is symmetric in its two letters. -/
theorem commutes_symm {st : State} {m1 m2 : Move} (h : Commutes st m1 m2) :
    Commutes st m2 m1 :=
  fun hrev2 hrev1 => diamondAt_symm (h hrev1 hrev2)

/-- A pull is slide-free. -/
theorem noSlide_foundToTab (c : Card) (b : Base) : NoSlide (Move.foundToTab c b) :=
  noSlide_of_isPull ⟨c, b, rfl⟩

/-- A raise is slide-free. -/
theorem noSlide_tabToFound (c : Card) : NoSlide (Move.tabToFound c) :=
  noSlide_of_isRaise ⟨c, rfl⟩

/-- Every state reachable from a `WF` state is `WF`. -/
theorem wf_of_reachable {u mid : State} (huwf : u.WF) (h : Reachable u mid) : mid.WF := by
  obtain ⟨σ, hσ⟩ := h
  exact SatDifferCensus.ShufflePlayW.wf_end hσ huwf

/-! ## §2. `swap_at_comm` — the swap from the endpoint row -/

theorem swap_at_comm_aux : ∀ (ρ₁ : List Move) {st B : State} {m1 m2 : Move} {ρ₂ : List Move},
    st.WF →
    ShufflePlayW st (ρ₁ ++ m1 :: m2 :: ρ₂) B →
    (∀ (mid : State), ShufflePlayW st ρ₁ mid → ∃ e, ShufflePlayW mid [m2, m1] e) →
    (∀ (mid : State), ShufflePlayW st ρ₁ mid → Commutes mid m1 m2) →
    ShufflePlayW st (ρ₁ ++ m2 :: m1 :: ρ₂) B := by
  intro ρ₁
  induction ρ₁ with
  | nil =>
      intro st B m1 m2 ρ₂ hwf h hpair hcomm
      obtain ⟨e, hpp⟩ := hpair st (Walk.nil st)
      obtain ⟨s1, hrev1, hstep1, hrest1⟩ := walk_cons_inv h
      obtain ⟨s12, hrev2s, hstep2s, hrestB⟩ := walk_cons_inv hrest1
      obtain ⟨s2, hrev2, hstep2, hrest2⟩ := walk_cons_inv hpp
      obtain ⟨e2, hrev1s, hstep1s, _⟩ := walk_cons_inv hrest2
      have hdia : DiamondAt st m1 m2 := hcomm st (Walk.nil st) hrev1 hrev2
      have hEq : s12 = e2 := hdia s1 s2 s12 e2 hstep1 hstep2 hstep2s hstep1s
      subst hEq
      exact Walk.cons hrev2 hstep2 (Walk.cons hrev1s hstep1s hrestB)
  | cons a as ih =>
      intro st B m1 m2 ρ₂ hwf h hpair hcomm
      obtain ⟨s1, hrev_a, hstep_a, hrest⟩ := walk_cons_inv h
      have hs1wf : s1.WF := step_wf hwf hstep_a
      have hpair' : ∀ mid, ShufflePlayW s1 as mid → ∃ e, ShufflePlayW mid [m2, m1] e := by
        intro mid hmid
        exact hpair mid (Walk.cons hrev_a hstep_a hmid)
      have hcomm' : ∀ mid, ShufflePlayW s1 as mid → Commutes mid m1 m2 := by
        intro mid hmid
        exact hcomm mid (Walk.cons hrev_a hstep_a hmid)
      exact Walk.cons hrev_a hstep_a (ih hs1wf hrest hpair' hcomm')

/-- **`swap_at_comm`** — exchange an adjacent pair using the endpoint row
instead of `NoSlide`.  The swapped-order *play* is still supplied explicitly
(it carries both reversibility transports). -/
theorem swap_at_comm {st mid B : State} {ρ₁ : List Move} {m1 m2 : Move} {ρ₂ : List Move}
    (hwf : st.WF)
    (hpre : ShufflePlayW st ρ₁ mid)
    (h : ShufflePlayW st (ρ₁ ++ m1 :: m2 :: ρ₂) B)
    (hpair : ∃ e, ShufflePlayW mid [m2, m1] e)
    (hcomm : Commutes mid m1 m2) :
    ShufflePlayW st (ρ₁ ++ m2 :: m1 :: ρ₂) B := by
  refine swap_at_comm_aux ρ₁ hwf h ?_ ?_
  · intro mid' hmid'
    have hrun₁ : st.run ρ₁ = some mid := Walk_run _ hpre
    have hrun₂ : st.run ρ₁ = some mid' := Walk_run _ hmid'
    have hEq : mid = mid' := Option.some.inj (hrun₁.symm.trans hrun₂)
    subst hEq
    exact hpair
  · intro mid' hmid'
    have hrun₁ : st.run ρ₁ = some mid := Walk_run _ hpre
    have hrun₂ : st.run ρ₁ = some mid' := Walk_run _ hmid'
    have hEq : mid = mid' := Option.some.inj (hrun₁.symm.trans hrun₂)
    subst hEq
    exact hcomm

/-! ## §3. The two window schemas and the writers -/

/-- **THE SWAPPED-ORDER TRANSPORT ROW — NOT A CONSEQUENCE OF THE PLAY.**
`SwapsRightFrom` is FALSE in general (counterexample: a legal reversible raise
and pull that cover each other, `Temp/Transport_Counter.lean`; the same data
refutes the normalizer's `hγ`).  The corrected hypothesis is
`RowsRight = AlwaysReversible ∧ WindowReversible ∧ KeepsForward`
(`Temp/Transport_Report.md`).  This definition is kept only as the named
hypothesis of the normalizer. -/
def SwapsRightFrom (u : State) (p : Move) (w : List Move) : Prop :=
  ∀ mid : State, Reachable u mid → ∀ q ∈ w, ∃ e, ShufflePlayW mid [q, p] e

/-- **THE SWAPPED-ORDER TRANSPORT ROW — NOT A CONSEQUENCE OF THE PLAY.**
See `SwapsRightFrom`; false in general, use `RowsLeft`. -/
def SwapsLeftFrom (u : State) (r : Move) (w : List Move) : Prop :=
  ∀ mid : State, Reachable u mid → ∀ q ∈ w, ∃ e, ShufflePlayW mid [r, q] e

def CommutesRight (u : State) (p : Move) (w : List Move) : Prop :=
  ∀ mid : State, Reachable u mid → ∀ q ∈ w, Commutes mid p q

def CommutesLeft (u : State) (r : Move) (w : List Move) : Prop :=
  ∀ mid : State, Reachable u mid → ∀ q ∈ w, Commutes mid q r

theorem swapsRightFrom_tail {u : State} {p a : Move} {w : List Move}
    (h : SwapsRightFrom u p (a :: w)) : SwapsRightFrom u p w :=
  fun mid hmid q hq => h mid hmid q (List.mem_cons_of_mem _ hq)

theorem swapsLeftFrom_tail {u : State} {r a : Move} {w : List Move}
    (h : SwapsLeftFrom u r (a :: w)) : SwapsLeftFrom u r w :=
  fun mid hmid q hq => h mid hmid q (List.mem_cons_of_mem _ hq)

theorem commutesRight_tail {u : State} {p a : Move} {w : List Move}
    (h : CommutesRight u p (a :: w)) : CommutesRight u p w :=
  fun mid hmid q hq => h mid hmid q (List.mem_cons_of_mem _ hq)

theorem commutesLeft_tail {u : State} {r a : Move} {w : List Move}
    (h : CommutesLeft u r (a :: w)) : CommutesLeft u r w :=
  fun mid hmid q hq => h mid hmid q (List.mem_cons_of_mem _ hq)

/-- **MOVE RIGHT (general).**  Same writer as `move_right`, but the window may
contain slides: each swap consumes the endpoint row `Commutes mid p q`. -/
theorem move_right_comm : ∀ (w : List Move) {u B : State} {pre rest : List Move} {p : Move},
    u.WF →
    ShufflePlayW u (pre ++ p :: w ++ rest) B →
    SwapsRightFrom u p w →
    CommutesRight u p w →
    ShufflePlayW u (pre ++ w ++ p :: rest) B := by
  intro w
  induction w with
  | nil =>
      intro u B pre rest p hwf h hsw hcomm
      simpa using h
  | cons a as ih =>
      intro u B pre rest p hwf h hsw hcomm
      have hsw_as : SwapsRightFrom u p as := swapsRightFrom_tail hsw
      have hcomm_as : CommutesRight u p as := commutesRight_tail hcomm
      have hnorm : ShufflePlayW u (pre ++ p :: a :: (as ++ rest)) B := by
        simpa only [List.cons_append, List.append_assoc] using h
      obtain ⟨mid, hpre, _⟩ :=
        ShufflePlayW_split h pre (p :: a :: as ++ rest) (by simp only [List.append_assoc])
      have hpair : ∃ e, ShufflePlayW mid [a, p] e :=
        hsw mid ⟨pre, hpre⟩ a (List.mem_cons_self ..)
      have hcomm_a : Commutes mid p a := hcomm mid ⟨pre, hpre⟩ a (List.mem_cons_self ..)
      have hswap : ShufflePlayW u (pre ++ a :: p :: (as ++ rest)) B :=
        swap_at_comm (ρ₁ := pre) (m1 := p) (m2 := a) (ρ₂ := as ++ rest)
          hwf hpre hnorm hpair hcomm_a
      have hswap' : ShufflePlayW u ((pre ++ [a]) ++ p :: as ++ rest) B := by
        simpa only [List.cons_append, List.append_assoc, List.nil_append] using hswap
      have ih' : ShufflePlayW u ((pre ++ [a]) ++ as ++ p :: rest) B :=
        ih hwf hswap' hsw_as hcomm_as
      simpa only [List.cons_append, List.append_assoc, List.nil_append] using ih'

/-- **MOVE LEFT (general).**  Dual writer; the window may contain slides. -/
theorem move_left_comm : ∀ (w : List Move) {u B : State} {pre rest : List Move} {r : Move},
    u.WF →
    ShufflePlayW u (pre ++ w ++ r :: rest) B →
    SwapsLeftFrom u r w →
    CommutesLeft u r w →
    ShufflePlayW u (pre ++ r :: w ++ rest) B := by
  intro w
  induction w with
  | nil =>
      intro u B pre rest r hwf h hsw hcomm
      simpa using h
  | cons a as ih =>
      intro u B pre rest r hwf h hsw hcomm
      have hsw_as : SwapsLeftFrom u r as := swapsLeftFrom_tail hsw
      have hcomm_as : CommutesLeft u r as := commutesLeft_tail hcomm
      have h1 : ShufflePlayW u (pre ++ a :: r :: (as ++ rest)) B := by
        have h' : ShufflePlayW u ((pre ++ [a]) ++ as ++ r :: rest) B := by
          simpa only [List.cons_append, List.append_assoc, List.nil_append] using h
        have ih'' : ShufflePlayW u (pre ++ a :: r :: (as ++ rest)) B := by
          have ih' := ih (u := u) (B := B) (pre := pre ++ [a]) (rest := rest)
            (r := r) hwf h' hsw_as hcomm_as
          simpa only [List.cons_append, List.append_assoc, List.nil_append] using ih'
        exact ih''
      obtain ⟨mid, hpre, _⟩ :=
        ShufflePlayW_split h1 pre (a :: r :: as ++ rest) rfl
      have hpair : ∃ e, ShufflePlayW mid [r, a] e :=
        hsw mid ⟨pre, hpre⟩ a (List.mem_cons_self ..)
      have hcomm_a : Commutes mid a r := hcomm mid ⟨pre, hpre⟩ a (List.mem_cons_self ..)
      have hswap : ShufflePlayW u (pre ++ r :: a :: (as ++ rest)) B :=
        swap_at_comm (ρ₁ := pre) (m1 := a) (m2 := r) (ρ₂ := as ++ rest)
          hwf hpre h1 hpair hcomm_a
      simpa only [List.cons_append, List.append_assoc] using hswap

end Bubble

namespace LocatorCorrected

open Bubble

/-- **THE NORMALIZER FROM THE EXACT ROWS.**  No `NoSlide` side condition: the
endpoint commutation is supplied by `CommutesRight`/`CommutesLeft`, and the
swapped-order plays by `SwapsRightFrom`/`SwapsLeftFrom`. -/
theorem crossingBracketNormalizer_of_commutes
    {u v : State} {ρ : List Move} {F : State}
    {left right : List Move} {c d : Card} {b : Base} {tail : List Move}
    {α β γ δ ε : List Move} {bd : Base}
    (huwf : u.WF) (hplay : ShufflePlayW u ρ v)
    (hdecomp : ρ = α ++ [Move.foundToTab d bd] ++ β ++
        [Move.foundToTab c b, Move.tabToFound d] ++ γ ++
        [Move.tabToFound c] ++ δ ++ ε)
    (hleft : ShufflePlayW u left F)
    (hcd : c ≠ d) (hsuit : c.suit ≠ d.suit)
    (hβ : SwapsRightFrom u (Move.foundToTab d bd) β)
    (hγ : SwapsLeftFrom u (Move.tabToFound c) γ)
    (hdβ : CommutesRight u (Move.foundToTab d bd) β)
    (hdγ : CommutesLeft u (Move.tabToFound c) γ) :
    ∃ ρ' : List Move, ShufflePlayW u ρ' v ∧ ρ'.length = ρ.length ∧
      CrossingBlock u v ρ' := by
  have hplay' : ShufflePlayW u
      (α ++ [Move.foundToTab d bd] ++ β ++
        [Move.foundToTab c b, Move.tabToFound d] ++ γ ++
        [Move.tabToFound c] ++ δ ++ ε) v := by
    rw [← hdecomp]
    exact hplay
  have hstep1 : ShufflePlayW u
      (α ++ β ++ Move.foundToTab d bd ::
        (Move.foundToTab c b :: Move.tabToFound d ::
          (γ ++ Move.tabToFound c :: δ ++ ε))) v := by
    have h' : ShufflePlayW u
        (α ++ Move.foundToTab d bd ::
          (β ++ (Move.foundToTab c b :: Move.tabToFound d ::
            (γ ++ Move.tabToFound c :: δ ++ ε)))) v := by
      simpa [List.append_assoc] using hplay'
    have h'norm : ShufflePlayW u
        (α ++ (Move.foundToTab d bd :: β) ++
          (Move.foundToTab c b :: Move.tabToFound d ::
            (γ ++ Move.tabToFound c :: δ ++ ε))) v := by
      simpa only [List.cons_append, List.append_assoc] using h'
    have hmoved :=
      move_right_comm (w := β) (u := u) (B := v) (pre := α)
        (rest := Move.foundToTab c b :: Move.tabToFound d ::
          (γ ++ Move.tabToFound c :: δ ++ ε))
        (p := Move.foundToTab d bd) huwf h'norm hβ hdβ
    simpa [List.append_assoc] using hmoved
  have hstep2 : ShufflePlayW u
      (α ++ β ++ [Move.foundToTab d bd, Move.foundToTab c b, Move.tabToFound d] ++
        (Move.tabToFound c :: γ ++ δ ++ ε)) v := by
    have h'' : ShufflePlayW u
        ((α ++ β ++ [Move.foundToTab d bd, Move.foundToTab c b, Move.tabToFound d]) ++
          γ ++ Move.tabToFound c :: (δ ++ ε)) v := by
      simpa [List.append_assoc] using hstep1
    have hmoved :=
      move_left_comm (w := γ) (u := u) (B := v)
        (pre := α ++ β ++ [Move.foundToTab d bd, Move.foundToTab c b, Move.tabToFound d])
        (rest := δ ++ ε) (r := Move.tabToFound c)
        huwf h'' hγ hdγ
    simpa [List.append_assoc] using hmoved
  refine ⟨(α ++ β) ++ [Move.foundToTab d bd, Move.foundToTab c b,
      Move.tabToFound d, Move.tabToFound c] ++ (γ ++ δ ++ ε), ?_, ?_, ?_⟩
  · simpa [List.append_assoc] using hstep2
  · rw [hdecomp]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  · exact crossingBlock_of_block_decomp (u := u) (v := v)
      (ρ := (α ++ β) ++ [Move.foundToTab d bd, Move.foundToTab c b,
        Move.tabToFound d, Move.tabToFound c] ++ (γ ++ δ ++ ε))
      (α := α ++ β) (γ := γ ++ δ ++ ε) (c := c) (d := d) (b := b) (bd := bd)
      huwf (by simpa [List.append_assoc] using hstep2)
      (by simp only [List.append_assoc])

/-! ## §4. The exact slide rows -/

/-- **THE MISSING SLIDE/PULL ROW.**  The endpoint equality for a slide and a
pull.  (Origin source: `Temp/Commute_Slide_Report.md` §5-§6 says the case
analysis is complete but the Lean assembly is unfinished; `Orig2/ForkCommute`
has no slide row at all.) -/
def SlidePullRow : Prop :=
  ∀ (st : State) (c : Card) (b : Base) (c' : Card) (b' : Base),
    st.WF → Commutes st (Move.tabToTab c b) (Move.foundToTab c' b')

/-- **THE MISSING SLIDE/RAISE ROW.**  The endpoint equality for a slide and a
raise. -/
def SlideRaiseRow : Prop :=
  ∀ (st : State) (c : Card) (b : Base) (c' : Card),
    st.WF → Commutes st (Move.tabToTab c b) (Move.tabToFound c')

/-- A slide row supplies the `Commutes` component for slide window letters. -/
theorem commutes_of_slidePullRow (h : SlidePullRow) {st : State} {c : Card}
    {b : Base} {c' : Card} {b' : Base} (hwf : st.WF) :
    Commutes st (Move.tabToTab c b) (Move.foundToTab c' b') :=
  h st c b c' b' hwf

theorem commutes_of_slideRaiseRow (h : SlideRaiseRow) {st : State} {c : Card}
    {b : Base} {c' : Card} (hwf : st.WF) :
    Commutes st (Move.tabToTab c b) (Move.tabToFound c') :=
  h st c b c' hwf

/-- **THE SLIDE/PULL ROW IS FREE.**  Discharged by
`CommuteStep.step_comm_slide_pull` (`Orig2/ForkCommuteSlide.lean`). -/
theorem slidePullRow_holds : SlidePullRow := by
  intro st c b c' b' hwf hrev1 hrev2 s1 s2 s12 s21 h1 h2 h12 h21
  exact CommuteStep.step_comm_slide_pull hwf hrev1 hrev2 h1 h2 h12 h21

/-- **THE SLIDE/RAISE ROW IS FREE.**  Discharged by
`CommuteStep.step_comm_slide_raise` (`Orig2/ForkCommuteSlide.lean`). -/
theorem slideRaiseRow_holds : SlideRaiseRow := by
  intro st c b c' hwf hrev1 hrev2 s1 s2 s12 s21 h1 h2 h12 h21
  exact CommuteStep.step_comm_slide_raise hwf hrev1 hrev2 h1 h2 h12 h21

/-- A letter that is a pull, a raise, or a slide. -/
def PullRaiseSlide (m : Move) : Prop :=
  IsPull m ∨ IsRaise m ∨ ∃ (c : Card) (b : Base), m = Move.tabToTab c b

theorem pullRaiseSlide_of_mem {l : List Move} (h : ∀ m ∈ l, PullRaiseSlide m) {m : Move}
    (hm : m ∈ l) : PullRaiseSlide m :=
  h m hm

/-- **THE SLIDE-ROW REDUCTION (right window).**  A window whose letters are
pulls/raises/slides has its endpoint rows: pulls and raises for free
(`commutes_noslide`), slides by `SlidePullRow`. -/
theorem commutesRight_of_slideRows (hsp : SlidePullRow)
    {u : State} (huwf : u.WF) (p : Move) (hp : IsPull p) (hpns : NoSlide p) {w : List Move}
    (hw : ∀ m ∈ w, PullRaiseSlide m) : CommutesRight u p w := by
  obtain ⟨dp, bp, rfl⟩ := hp
  intro mid hmid q hq
  have hmidwf : mid.WF := Bubble.wf_of_reachable huwf hmid
  rcases hw q hq with hpull | hraise | ⟨c, b, rfl⟩
  · exact commutes_noslide hmidwf hpns (noSlide_of_isPull hpull)
  · exact commutes_noslide hmidwf hpns (noSlide_of_isRaise hraise)
  · exact commutes_symm (commutes_of_slidePullRow hsp hmidwf)

/-- **THE SLIDE-ROW REDUCTION (left window).**  Dual. -/
theorem commutesLeft_of_slideRows (hsr : SlideRaiseRow)
    {u : State} (huwf : u.WF) (r : Move) (hr : IsRaise r) (hrns : NoSlide r) {w : List Move}
    (hw : ∀ m ∈ w, PullRaiseSlide m) : CommutesLeft u r w := by
  obtain ⟨dr, rfl⟩ := hr
  intro mid hmid q hq
  have hmidwf : mid.WF := Bubble.wf_of_reachable huwf hmid
  rcases hw q hq with hpull | hraise | ⟨c, b, rfl⟩
  · exact commutes_noslide hmidwf (noSlide_of_isPull hpull) hrns
  · exact commutes_noslide hmidwf (noSlide_of_isRaise hraise) hrns
  · exact commutes_of_slideRaiseRow hsr hmidwf

/-- **`CrossingBracketNormalizer` FROM THE TWO NAMED SLIDE ROWS + THE
TRANSPORT SCHEMAS.**  This is the explicit `row → normalizer` reduction:
`hsp`/`hsr` are the missing `step_comm_slide_pull` / `step_comm_slide_raise`
endpoint rows, and `hβ`/`hγ` are the swapped-order plays (both reversibility
transports).  The windows may contain arbitrary pulls, raises and slides. -/
theorem crossingBracketNormalizer_of_slideRows
    (hsp : SlidePullRow) (hsr : SlideRaiseRow)
    {u v : State} {ρ : List Move} {F : State}
    {left right : List Move} {c d : Card} {b : Base} {tail : List Move}
    {α β γ δ ε : List Move} {bd : Base}
    (huwf : u.WF) (hplay : ShufflePlayW u ρ v)
    (hdecomp : ρ = α ++ [Move.foundToTab d bd] ++ β ++
        [Move.foundToTab c b, Move.tabToFound d] ++ γ ++
        [Move.tabToFound c] ++ δ ++ ε)
    (hleft : ShufflePlayW u left F)
    (hcd : c ≠ d) (hsuit : c.suit ≠ d.suit)
    (hβ : SwapsRightFrom u (Move.foundToTab d bd) β)
    (hγ : SwapsLeftFrom u (Move.tabToFound c) γ)
    (hβletters : ∀ m ∈ β, PullRaiseSlide m)
    (hγletters : ∀ m ∈ γ, PullRaiseSlide m) :
    ∃ ρ' : List Move, ShufflePlayW u ρ' v ∧ ρ'.length = ρ.length ∧
      CrossingBlock u v ρ' :=
  crossingBracketNormalizer_of_commutes (tail := tail) (right := right)
    huwf hplay hdecomp hleft hcd hsuit hβ hγ
    (commutesRight_of_slideRows hsp huwf (Move.foundToTab d bd)
      ⟨d, bd, rfl⟩ (Bubble.noSlide_foundToTab d bd) hβletters)
    (commutesLeft_of_slideRows hsr huwf (Move.tabToFound c)
      ⟨c, rfl⟩ (Bubble.noSlide_tabToFound c) hγletters)

/-- **THE `NoSlide` COROLLARY.**  When the windows are slide-free both
endpoint schemas are free (`diamond_noslide`), leaving only the two
swapped-order transport schemas. -/
theorem crossingBracketNormalizer_of_noslide
    {u v : State} {ρ : List Move} {F : State}
    {left right : List Move} {c d : Card} {b : Base} {tail : List Move}
    {α β γ δ ε : List Move} {bd : Base}
    (huwf : u.WF) (hplay : ShufflePlayW u ρ v)
    (hdecomp : ρ = α ++ [Move.foundToTab d bd] ++ β ++
        [Move.foundToTab c b, Move.tabToFound d] ++ γ ++
        [Move.tabToFound c] ++ δ ++ ε)
    (hleft : ShufflePlayW u left F)
    (hcd : c ≠ d) (hsuit : c.suit ≠ d.suit)
    (hβ : SwapsRightFrom u (Move.foundToTab d bd) β)
    (hγ : SwapsLeftFrom u (Move.tabToFound c) γ)
    (hnslβ : ∀ m ∈ β, NoSlide m) (hnslγ : ∀ m ∈ γ, NoSlide m) :
    ∃ ρ' : List Move, ShufflePlayW u ρ' v ∧ ρ'.length = ρ.length ∧
      CrossingBlock u v ρ' :=
  crossingBracketNormalizer_of_commutes (tail := tail) (right := right)
    huwf hplay hdecomp hleft hcd hsuit hβ hγ
    (fun mid hmid q hq =>
      commutes_noslide (Bubble.wf_of_reachable huwf hmid)
        (Bubble.noSlide_foundToTab d bd) (hnslβ q hq))
    (fun mid hmid q hq =>
      commutes_noslide (Bubble.wf_of_reachable huwf hmid)
        (hnslγ q hq) (Bubble.noSlide_tabToFound c))

end LocatorCorrected

#print axioms Bubble.commutes_noslide
#print axioms Bubble.wf_of_reachable
#print axioms Bubble.swap_at_comm
#print axioms Bubble.move_right_comm
#print axioms Bubble.move_left_comm
#print axioms LocatorCorrected.crossingBracketNormalizer_of_commutes
#print axioms LocatorCorrected.commutes_of_slidePullRow
#print axioms LocatorCorrected.commutes_of_slideRaiseRow
#print axioms Bubble.commutes_symm
#print axioms LocatorCorrected.crossingBracketNormalizer_of_slideRows
#print axioms LocatorCorrected.crossingBracketNormalizer_of_noslide
#print axioms LocatorCorrected.commutesRight_of_slideRows
#print axioms LocatorCorrected.commutesLeft_of_slideRows
