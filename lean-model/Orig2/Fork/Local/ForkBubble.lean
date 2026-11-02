import Orig2.Fork.Split.ForkSplit
import Orig2.Fiber.SWDichotomy
import Orig2.Fork.Split.FirstPassage
import Orig2.Fork.Local.ForkCommute

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-!
# Orig2/ForkBubble — lifting the local diamond to the play level

PROMOTED from `Temp/Bubble_Core.lean` (2026-11-01).  The scratch file
imported the scratch assembly `Temp.Commute_Step_Assembly`; the promotion
consumes the source card `Orig2/ForkCommute` instead, whose tail carries
`NoSlide`, `diamond_noslide` and `swap_adjacent_noslide` under the same
`CommuteStep` namespace (`Orig2/Fork/Local/ForkCommute.lean:973-1035`).  No statement
changed.

`Temp/Commute_Step_Assembly.lean` proves the head-local flip
`swap_adjacent_noslide` for a pair of letters drawn from
`{draw, tabToFound, foundToTab}` (no `tabToTab`, no waste letters).

This file lifts it to whole plays:

* `walk_split` — a play on `ρ₁ ++ ρ₂` splits at the intermediate state.
* `swap_at_aux` / `swap_at` — exchange an adjacent pair `m1, m2` inside a
  play whenever both orders are legal at the state before them.
* `swap_head` — the `ρ₁ = []` specialization.

The side conditions are exactly those of the local diamond: `NoSlide` on
both exchanged letters and the WF of the state where the exchange happens.
The swapped order is supplied as a *play* (`ShufflePlayW mid [m2, m1] e`),
not merely as a pair of steps: the second letter must also be reversible
at its new origin, which the diamond alone does not give.
-/

namespace Bubble

open CommuteStep

/-! ## §0. Splitting a play at a list boundary -/

/-- Destruct a nonempty witness play into head letter, step and tail. -/
theorem walk_cons_inv {P : State → Move → Prop} {st B : State} {m : Move} {ρ : List Move}
    (h : Walk P st (m :: ρ) B) :
    ∃ s1, P st m ∧ State.step st m = some s1 ∧ Walk P s1 ρ B := by
  cases h with
  | cons hlet hstep hrest => exact ⟨_, hlet, hstep, hrest⟩

/-- **SPLIT.**  A witness play on `ρ₁ ++ ρ₂` factors at the intermediate
state (which is `st.run ρ₁`, by `Walk_run`). -/
theorem walk_split : ∀ (ρ₁ : List Move) {st B : State} {rest : List Move},
    ShufflePlayW st (ρ₁ ++ rest) B →
    ∃ mid, ShufflePlayW st ρ₁ mid ∧ ShufflePlayW mid rest B := by
  intro ρ₁
  induction ρ₁ with
  | nil =>
      intro st B rest h
      exact ⟨st, Walk.nil st, h⟩
  | cons a as ih =>
      intro st B rest h
      obtain ⟨s1, hlet, hstep, hrest⟩ := walk_cons_inv h
      obtain ⟨mid, h1, h2⟩ := ih hrest
      exact ⟨mid, Walk.cons hlet hstep h1, h2⟩

/-! ## §1. `swap_at` — exchanging an adjacent pair inside a play -/

/-- **THE INDUCTION ENGINE.**  A play on `ρ₁ ++ m1 :: m2 :: ρ₂` can be
re-run on `ρ₁ ++ m2 :: m1 :: ρ₂` to the same endpoint, provided the pair
`m2, m1` is itself a play from every state reached by `ρ₁` (and both
letters are slide-free, so the local diamond applies). -/
theorem swap_at_aux : ∀ (ρ₁ : List Move) {st B : State} {m1 m2 : Move} {ρ₂ : List Move},
    st.WF →
    ShufflePlayW st (ρ₁ ++ m1 :: m2 :: ρ₂) B →
    NoSlide m1 → NoSlide m2 →
    (∀ (mid : State), ShufflePlayW st ρ₁ mid → ∃ e, ShufflePlayW mid [m2, m1] e) →
    ShufflePlayW st (ρ₁ ++ m2 :: m1 :: ρ₂) B := by
  intro ρ₁
  induction ρ₁ with
  | nil =>
      intro st B m1 m2 ρ₂ hwf h hn1 hn2 hpair
      obtain ⟨e, hpp⟩ := hpair st (Walk.nil st)
      obtain ⟨s1, hrev1, hstep1, hrest1⟩ := walk_cons_inv h
      obtain ⟨s12, hrev2s, hstep2s, hrestB⟩ := walk_cons_inv hrest1
      obtain ⟨s2, hrev2, hstep2, hrest2⟩ := walk_cons_inv hpp
      obtain ⟨e2, hrev1s, hstep1s, _⟩ := walk_cons_inv hrest2
      obtain ⟨s2', hstep2', hstep1''⟩ :=
        swap_adjacent_noslide hwf hrev1 hrev2 hn1 hn2 hstep1 hstep2s hstep2 hstep1s
      have hs2' : s2' = s2 := Option.some.inj (hstep2'.symm.trans hstep2)
      have hstep_mid : State.step s2 m1 = some s12 := by
        rw [← hs2']; exact hstep1''
      exact Walk.cons hrev2 hstep2 (Walk.cons hrev1s hstep_mid hrestB)
  | cons a as ih =>
      intro st B m1 m2 ρ₂ hwf h hn1 hn2 hpair
      obtain ⟨s1, hrev_a, hstep_a, hrest⟩ := walk_cons_inv h
      have hs1wf : s1.WF := step_wf hwf hstep_a
      have hpair' : ∀ mid, ShufflePlayW s1 as mid → ∃ e, ShufflePlayW mid [m2, m1] e := by
        intro mid hmid
        exact hpair mid (Walk.cons hrev_a hstep_a hmid)
      exact Walk.cons hrev_a hstep_a (ih hs1wf hrest hn1 hn2 hpair')

/-- **`swap_at` — the list-level wrapper.**  In a witness play
`st --ρ₁--> mid --m1;m2--> …`, if the two *orders* `m1;m2` and `m2;m1`
are both legal at `mid` (the second given as a play, which also carries
the reversibility of `m1` at its new origin), then the play can be re-run
with the pair exchanged, to the SAME endpoint. -/
theorem swap_at {st mid B : State} {ρ₁ : List Move} {m1 m2 : Move} {ρ₂ : List Move}
    (hwf : st.WF)
    (hpre : ShufflePlayW st ρ₁ mid)
    (h : ShufflePlayW st (ρ₁ ++ m1 :: m2 :: ρ₂) B)
    (hn1 : NoSlide m1) (hn2 : NoSlide m2)
    (hpair : ∃ e, ShufflePlayW mid [m2, m1] e) :
    ShufflePlayW st (ρ₁ ++ m2 :: m1 :: ρ₂) B := by
  refine swap_at_aux ρ₁ hwf h hn1 hn2 ?_
  intro mid' hmid'
  have hrun₁ : st.run ρ₁ = some mid := Walk_run _ hpre
  have hrun₂ : st.run ρ₁ = some mid' := Walk_run _ hmid'
  have hEq : mid = mid' := Option.some.inj (hrun₁.symm.trans hrun₂)
  subst hEq
  exact hpair

/-- **`swap_head` — the `ρ₁ = []` case.** -/
theorem swap_head {st B : State} {m1 m2 : Move} {ρ₂ : List Move}
    (hwf : st.WF)
    (h : ShufflePlayW st (m1 :: m2 :: ρ₂) B)
    (hn1 : NoSlide m1) (hn2 : NoSlide m2)
    (hpair : ∃ e, ShufflePlayW st [m2, m1] e) :
    ShufflePlayW st (m2 :: m1 :: ρ₂) B :=
  swap_at hwf (Walk.nil st) h hn1 hn2 hpair

/-- **WHAT `swap_at` CONSUMES, UNFOLDED.**  The swapped-order hypothesis is
exactly: `m2` is reversible at `mid`, and `m1` is reversible at the state
`m2` leads to.  The second half is *not* a consequence of the local
diamond (`m1` is reversible at `mid`, but the diamond only controls the
two *steps*, not the return plays) — this is the gap the schema
`RaisesPullsPlay` pays for in `sort_raises`. -/
theorem pair_play_iff {mid : State} {m1 m2 : Move} :
    (∃ e, ShufflePlayW mid [m2, m1] e) ↔
      (reversibleAtW mid m2 ∧ ∃ s, State.step mid m2 = some s ∧ reversibleAtW s m1) := by
  constructor
  · rintro ⟨e, h⟩
    obtain ⟨s, hrev2, hstep2, hrest⟩ := walk_cons_inv h
    obtain ⟨e', hrev1', hstep1', _⟩ := walk_cons_inv hrest
    exact ⟨hrev2, s, hstep2, hrev1'⟩
  · rintro ⟨hrev2, s, hstep2, hrev1⟩
    have hs1 : ∃ e, State.step s m1 = some e := by
      obtain ⟨a, _b, hst, _hr⟩ := hrev1
      exact ⟨a, hst⟩
    obtain ⟨e, hstep1⟩ := hs1
    exact ⟨e, Walk.cons hrev2 hstep2 (Walk.cons hrev1 hstep1 (Walk.nil e))⟩

/-! ## §2. Letter classes

The three letters the local diamond covers (`draw`, `tabToFound`,
`foundToTab`) get named classes.  `tabToTab` (the slide) is deliberately
NOT given a class: the unconditional slide/slide square is false (two
slides of the same card have different endpoints), so no slide is ever
swapped in this file. -/

/-- The letter is a pull (`foundToTab`). -/
def IsPull (m : Move) : Prop := ∃ (c : Card) (b : Base), m = Move.foundToTab c b

/-- The letter is a raise (`tabToFound`). -/
def IsRaise (m : Move) : Prop := ∃ c : Card, m = Move.tabToFound c

/-- A pull is never a slide. -/
theorem noSlide_of_isPull {m : Move} (h : IsPull m) : NoSlide m := by
  obtain ⟨c, b, rfl⟩ := h
  intro c' b' heq
  cases heq

/-- A raise is never a slide. -/
theorem noSlide_of_isRaise {m : Move} (h : IsRaise m) : NoSlide m := by
  obtain ⟨c, rfl⟩ := h
  intro c' b' heq
  cases heq

/-- Every letter is a raise, and every letter is a pull. -/
def OnlyRaises (l : List Move) : Prop := ∀ m ∈ l, IsRaise m
def OnlyPulls (l : List Move) : Prop := ∀ m ∈ l, IsPull m
/-- Every letter is a raise or a pull (no slide, draw or waste letter). -/
def OnlyRaisePull (l : List Move) : Prop := ∀ m ∈ l, IsRaise m ∨ IsPull m

theorem onlyRaises_tail {a : Move} {l : List Move} (h : OnlyRaises (a :: l)) : OnlyRaises l :=
  fun m hm => h m (List.mem_cons_of_mem _ hm)

theorem onlyPulls_tail {a : Move} {l : List Move} (h : OnlyPulls (a :: l)) : OnlyPulls l :=
  fun m hm => h m (List.mem_cons_of_mem _ hm)

theorem onlyRaisePull_tail {a : Move} {l : List Move} (h : OnlyRaisePull (a :: l)) :
    OnlyRaisePull l := fun m hm => h m (List.mem_cons_of_mem _ hm)

/-! ## §3. `bubble_raise_left` and `bubble_one`

Move a chosen raise leftward across a window of letters.  The window
letters must be slide-free (so the local diamond applies) and every
adjacent pair, in its *swapped* order, must be a legal play at the state
where the swap is performed.  That last datum is what `swap_head`
consumes; it is the exact form of "both orders are legal". -/

/-- **BUBBLE (general).**  In a play `w ; r`, the raise `r` can be moved
in front of the window `w`, provided every letter of `w` is slide-free
and every adjacent `(letter, r)` pair is legal in the swapped order at
the state where the swap happens. -/
theorem bubble_raise_left : ∀ (w : List Move) {st B : State} {r : Move} {rest : List Move},
    st.WF →
    (∀ m ∈ w, NoSlide m) → NoSlide r →
    ShufflePlayW st (w ++ r :: rest) B →
    (∀ (pre : List Move) (mid : State) (q : Move) (post : List Move),
        pre ++ q :: post = w → ShufflePlayW st pre mid →
        ∃ e, ShufflePlayW mid [r, q] e) →
    ShufflePlayW st (r :: w ++ rest) B := by
  intro w
  induction w with
  | nil =>
      intro st B r rest hwf hnsl hnr h hsw
      simpa using h
  | cons a as ih =>
      intro st B r rest hwf hnsl hnr h hsw
      obtain ⟨s1, hrev_a, hstep_a, hrest⟩ := walk_cons_inv h
      have hnsl_a : NoSlide a := hnsl a (List.mem_cons_self ..)
      have hnsl_as : ∀ m ∈ as, NoSlide m := fun m hm => hnsl m (List.mem_cons_of_mem _ hm)
      have hs1wf : s1.WF := step_wf hwf hstep_a
      have hsw' : ∀ (pre : List Move) (mid : State) (q : Move) (post : List Move),
          pre ++ q :: post = as → ShufflePlayW s1 pre mid →
          ∃ e, ShufflePlayW mid [r, q] e := by
        intro pre mid q post hsplit hpre
        exact hsw (a :: pre) mid q post (by rw [List.cons_append, hsplit])
          (Walk.cons hrev_a hstep_a hpre)
      have ih' : ShufflePlayW s1 (r :: as ++ rest) B := ih hs1wf hnsl_as hnr hrest hsw'
      have hcons : ShufflePlayW st (a :: r :: as ++ rest) B := Walk.cons hrev_a hstep_a ih'
      have hcert : ∃ e, ShufflePlayW st [r, a] e := hsw [] st a as rfl (Walk.nil st)
      simpa using swap_head hwf hcons hnsl_a hnr hcert

/-- **`bubble_one`.**  A raise preceded (inside its window) only by pulls
can be moved to the front of that window.  This is `bubble_raise_left`
with `NoSlide` derived from `IsPull`. -/
theorem bubble_one : ∀ (w : List Move) {st B : State} {r : Move} {rest : List Move},
    st.WF →
    (∀ m ∈ w, IsPull m) → IsRaise r →
    ShufflePlayW st (w ++ r :: rest) B →
    (∀ (pre : List Move) (mid : State) (p : Move) (post : List Move),
        pre ++ p :: post = w → ShufflePlayW st pre mid →
        ∃ e, ShufflePlayW mid [r, p] e) →
    ShufflePlayW st (r :: w ++ rest) B :=
  fun w st B r rest hwf hpull hraise h hsw =>
    bubble_raise_left w hwf (fun m hm => noSlide_of_isPull (hpull m hm))
      (noSlide_of_isRaise hraise) h hsw

/-! ## §4. `bubble_pull_right` — the dual move

To sort a raise-headed tail, a pull sitting at the head of a window of
raises has to move to the *right*.  The bookkeeping is the same, with the
pair order reversed. -/

/-- **BUBBLE-PULL-RIGHT.**  In a play `p ; w`, the pull `p` can be moved
behind the window `w` of raises, provided every adjacent `(raise, pull)`
pair is legal in the swapped order at the state where the swap happens. -/
theorem bubble_pull_right : ∀ (w : List Move) {st B : State} {p : Move} {rest : List Move},
    st.WF →
    (∀ m ∈ w, IsRaise m) → IsPull p →
    ShufflePlayW st (p :: w ++ rest) B →
    (∀ (pre : List Move) (mid : State) (q : Move) (post : List Move),
        pre ++ q :: post = w → ShufflePlayW st pre mid →
        ∃ e, ShufflePlayW mid [q, p] e) →
    ShufflePlayW st (w ++ p :: rest) B := by
  intro w
  induction w with
  | nil =>
      intro st B p rest hwf hra hpull h hsw
      simpa using h
  | cons a as ih =>
      intro st B p rest hwf hra hpull h hsw
      have hraise_a : IsRaise a := hra a (List.mem_cons_self ..)
      have hra_as : ∀ m ∈ as, IsRaise m := fun m hm => hra m (List.mem_cons_of_mem _ hm)
      have hnsl_a : NoSlide a := noSlide_of_isRaise hraise_a
      have hnsl_p : NoSlide p := noSlide_of_isPull hpull
      have hcert : ∃ e, ShufflePlayW st [a, p] e := hsw [] st a as rfl (Walk.nil st)
      have hswapped : ShufflePlayW st (a :: p :: as ++ rest) B :=
        swap_head hwf h hnsl_p hnsl_a hcert
      obtain ⟨t1, hrev_a, hstep_a, hrest⟩ := walk_cons_inv hswapped
      have ht1wf : t1.WF := step_wf hwf hstep_a
      have hsw' : ∀ (pre : List Move) (mid : State) (q : Move) (post : List Move),
          pre ++ q :: post = as → ShufflePlayW t1 pre mid →
          ∃ e, ShufflePlayW mid [q, p] e := by
        intro pre mid q post hsplit hpre
        exact hsw (a :: pre) mid q post (by rw [List.cons_append, hsplit])
          (Walk.cons hrev_a hstep_a hpre)
      have ih' : ShufflePlayW t1 (as ++ p :: rest) B :=
        ih ht1wf hra_as hpull hrest hsw'
      exact Walk.cons hrev_a hstep_a ih'

/-! ## §5. `sort_raises` — the raise block / pull block normal form

The sorting below is a bubble sort on the two-letter alphabet
`{raise, pull}`, whose swaps are exactly the ones `swap_at` licenses.
Slides, draws and waste letters are excluded (`OnlyRaisePull`): a raise
does not commute with a slide or a draw, so they can obstruct the normal
form (see `Temp/Bubble_Report.md` §4 for the word-level counterexample).

The hypothesis `RaisesPullsPlay st` is the "both orders are legal"
schema at the play level: at EVERY state reachable from `st`, every
`(raise, pull)` pair can be played in the `(raise, pull)` order.  It is
what the sort consumes; the *local* version of `swap_at` is not enough,
because the sorting procedure visits states that never occur in the given
play (after the first letter of a swapped pair), and the second letter
must be reversible there. -/

/-- A play with no pull letter. -/
def NoPull (l : List Move) : Prop := ∀ m ∈ l, ∀ (c : Card) (b : Base), m ≠ Move.foundToTab c b

/-- A play with no raise letter. -/
def NoRaise (l : List Move) : Prop := ∀ m ∈ l, ∀ c : Card, m ≠ Move.tabToFound c

/-- **The mountain shape**: a raise/flat block followed by a pull/flat block. -/
def Mountain (u v : State) : Prop :=
  ∃ peak ρ₁ ρ₂, ShufflePlayW u ρ₁ peak ∧ ShufflePlayW peak ρ₂ v ∧
    NoPull ρ₁ ∧ NoRaise ρ₂

/-- A state reachable from `st` by a witness play. -/
def Reachable (st mid : State) : Prop := ∃ σ, ShufflePlayW st σ mid

/-- **THE SWAP SCHEMA.**  At every state reachable from `st`, each
`(raise, pull)` pair is legally playable in the raise-first order. -/
def RaisesPullsPlay (st : State) : Prop :=
  ∀ (mid : State) (p r : Move), Reachable st mid → IsPull p → IsRaise r →
    ∃ e, ShufflePlayW mid [r, p] e

/-- The swap schema transports forward along a play. -/
theorem raisesPullsPlay_of_play {st s : State} {σ : List Move}
    (hσ : ShufflePlayW st σ s) (h : RaisesPullsPlay st) : RaisesPullsPlay s := by
  intro mid p r hreach hp hr
  obtain ⟨τ, hτ⟩ := hreach
  exact h mid p r ⟨σ ++ τ, ShufflePlayW_append hσ hτ⟩ hp hr

/-- **SORT RAISES.**  If a witness play has only raise and pull letters,
and every `(raise, pull)` pair is legally playable raise-first at every
state reachable from the origin, then the play can be re-run in the
mountain normal form `ρ₁ ++ ρ₂` with `ρ₁` all raises and `ρ₂` raise-free,
to the SAME endpoint. -/
theorem sort_raises : ∀ (ρ : List Move) {st B : State},
    st.WF → OnlyRaisePull ρ → ShufflePlayW st ρ B → RaisesPullsPlay st →
    ∃ ρ₁ ρ₂, ShufflePlayW st (ρ₁ ++ ρ₂) B ∧ OnlyRaises ρ₁ ∧ NoRaise ρ₂ := by
  intro ρ
  induction ρ with
  | nil =>
      intro st B hwf horp h hcomm
      exact ⟨[], [], by simpa using h,
        (by intro m hm; simp at hm),
        (by intro m hm c hc; simp at hm)⟩
  | cons m t ih =>
      intro st B hwf horp h hcomm
      obtain ⟨s1, hrev_m, hstep_m, hrest⟩ := walk_cons_inv h
      have hs1wf : s1.WF := step_wf hwf hstep_m
      have horp_t : OnlyRaisePull t := onlyRaisePull_tail horp
      have hcomm_s1 : RaisesPullsPlay s1 :=
        raisesPullsPlay_of_play (Walk.cons hrev_m hstep_m (Walk.nil s1)) hcomm
      obtain ⟨t₁, t₂, htplay, htOnlyR, htNR⟩ := ih hs1wf horp_t hrest hcomm_s1
      rcases horp m (List.mem_cons_self ..) with hm_raise | hm_pull
      · -- head is a raise: it belongs to the raise block
        refine ⟨m :: t₁, t₂, ?_, ?_, htNR⟩
        · simpa using Walk.cons hrev_m hstep_m htplay
        · intro x hx
          rcases List.mem_cons.mp hx with rfl | hx'
          · exact hm_raise
          · exact htOnlyR x hx'
      · -- head is a pull: it is pushed right behind the raise block
        have hfull : ShufflePlayW st (m :: t₁ ++ t₂) B :=
          Walk.cons hrev_m hstep_m htplay
        have hsw : ∀ (pre : List Move) (mid : State) (q : Move) (post : List Move),
            pre ++ q :: post = t₁ → ShufflePlayW st pre mid →
            ∃ e, ShufflePlayW mid [q, m] e := by
          intro pre mid q post hsplit hpre
          have hq : q ∈ t₁ := by rw [← hsplit]; simp
          exact hcomm mid m q ⟨pre, hpre⟩ hm_pull (htOnlyR q hq)
        have hsorted : ShufflePlayW st (t₁ ++ m :: t₂) B :=
          bubble_pull_right t₁ hwf htOnlyR hm_pull hfull hsw
        refine ⟨t₁, m :: t₂, hsorted, htOnlyR, ?_⟩
        obtain ⟨c0, b0, rfl⟩ := hm_pull
        intro x hx c hc
        rcases List.mem_cons.mp hx with rfl | hx'
        · cases hc
        · exact htNR x hx' c hc

/-! ## §6. The mountain shape -/

theorem noPull_of_onlyRaises {l : List Move} (h : OnlyRaises l) : NoPull l := by
  intro m hm c b hc
  obtain ⟨c', h'⟩ := h m hm
  rw [h'] at hc
  cases hc

theorem noRaise_of_onlyPulls {l : List Move} (h : OnlyPulls l) : NoRaise l := by
  intro m hm c hc
  obtain ⟨c', b', h'⟩ := h m hm
  rw [h'] at hc
  cases hc

/-- Any play already split in the mountain shape is a mountain. -/
theorem mountain_of_shape {u peak v : State} {ρ₁ ρ₂ : List Move}
    (h₁ : ShufflePlayW u ρ₁ peak) (h₂ : ShufflePlayW peak ρ₂ v)
    (hnp : NoPull ρ₁) (hnr : NoRaise ρ₂) : Mountain u v :=
  ⟨peak, ρ₁, ρ₂, h₁, h₂, hnp, hnr⟩

/-- A sorted *play* (given as one list `ρ₁ ++ ρ₂`) is a mountain: split it
at the block boundary. -/
theorem mountain_of_sorted {u v : State} {ρ₁ ρ₂ : List Move}
    (hsorted : ShufflePlayW u (ρ₁ ++ ρ₂) v) (hnp : NoPull ρ₁) (hnr : NoRaise ρ₂) :
    Mountain u v := by
  obtain ⟨peak, h₁, h₂⟩ := walk_split ρ₁ hsorted
  exact mountain_of_shape h₁ h₂ hnp hnr

/-- **`mountain_of_shuffle`** — the play-level lifting: a `{raise, pull}`
play whose raise/pull pairs are swappable at every reachable state is a
mountain.  `sort_raises` produces the sorted play; `mountain_of_sorted`
splits it. -/
theorem mountain_of_shuffle {u v : State} {ρ : List Move}
    (hwf : u.WF) (h : ShufflePlayW u ρ v)
    (horp : OnlyRaisePull ρ) (hcomm : RaisesPullsPlay u) :
    Mountain u v := by
  obtain ⟨ρ₁, ρ₂, hplay, hOnlyR, hNR⟩ := sort_raises ρ hwf horp h hcomm
  exact mountain_of_sorted hplay (noPull_of_onlyRaises hOnlyR) hNR

/-- **Degenerate case (no hypothesis).**  A play with no pull letter is a
mountain: the raise block is the whole play, the pull block is empty. -/
theorem mountain_of_raiseBlock {u v : State} {ρ : List Move}
    (h : ShufflePlayW u ρ v) (hnp : NoPull ρ) : Mountain u v :=
  mountain_of_shape h (Walk.nil v) hnp (by intro m hm; simp at hm)

/-- **Degenerate case (no hypothesis).**  A play with no raise letter is a
mountain: the raise block is empty. -/
theorem mountain_of_pullBlock {u v : State} {ρ : List Move}
    (h : ShufflePlayW u ρ v) (hnr : NoRaise ρ) : Mountain u v :=
  mountain_of_shape (Walk.nil u) h (by intro m hm; simp at hm) hnr

/-! ## §7. `bracket_delete_at` — deleting a `pull c ; … ; raise c` bracket -/

/-- **SAME-CARD CANCELLATION** (verbatim from `Temp/Valley_Step.lean:33`):
`… pull c ; raise c …` deletes both letters. -/
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

/-- **BRACKET DELETE.**  Suppose a play reaches `A'`, pulls `c` onto `b`
to `S`, then plays an interior `inner` and finally raises `c`.  If the
interior is slide-free and can be re-run from `A'` (the "independent of
`c` and its base" certificate, supplied as swapped-order plays for each
of its letters), then the pull/raise bracket deletes: the play on
`ρ₁ ++ inner ++ ρ₂` runs from the original origin to the original
endpoint.

The independence hypothesis is exactly `hbr` + `hsw`: `hbr` says the
interior followed by the raise is a legal play from `S`, and `hsw` says
each adjacent `(letter, raise c)` pair is legal in the swapped order, so
`bubble_raise_left` walks the raise left until it is adjacent to the
pull, where `valley_cancel_same` deletes both.

The empty interior (`inner = []`) needs no swap certificate at all and is
exactly `valley_cancel_same`; the one-letter (and longer) interior is the
`bubble_raise_left` induction. -/
theorem bracket_delete_at {A A' S C : State} {ρ₁ inner ρ₂ : List Move}
    {c : Card} {b : Base}
    (hwf : A.WF)
    (h₁ : ShufflePlayW A ρ₁ A')
    (hpull : State.step A' (Move.foundToTab c b) = some S)
    (hbr : ShufflePlayW S (inner ++ Move.tabToFound c :: ρ₂) C)
    (hnsl : ∀ m ∈ inner, NoSlide m)
    (hsw : ∀ (pre : List Move) (mid : State) (q : Move) (post : List Move),
        pre ++ q :: post = inner → ShufflePlayW S pre mid →
        ∃ e, ShufflePlayW mid [Move.tabToFound c, q] e) :
    ShufflePlayW A (ρ₁ ++ inner ++ ρ₂) C := by
  have hA' : A'.WF := SatDifferCensus.ShufflePlayW.wf_end h₁ hwf
  have hSwf : S.WF := step_wf hA' hpull
  have hbubble : ShufflePlayW S (Move.tabToFound c :: inner ++ ρ₂) C :=
    bubble_raise_left inner hSwf hnsl (noSlide_of_isRaise ⟨c, rfl⟩) hbr hsw
  simpa [List.append_assoc] using
    valley_cancel_same (A := A) (A' := A') (B := S) (C := C)
      (ρ₁ := ρ₁) (ρ₂ := inner ++ ρ₂) (c := c) (b := b) hwf h₁ hpull hbubble

/-- **Empty interior** — the `inner = []` base case: this is exactly
`valley_cancel_same`. -/
theorem bracket_delete_nil {A A' S C : State} {ρ₁ ρ₂ : List Move} {c : Card} {b : Base}
    (hwf : A.WF) (h₁ : ShufflePlayW A ρ₁ A')
    (hpull : State.step A' (Move.foundToTab c b) = some S)
    (h₂ : ShufflePlayW S (Move.tabToFound c :: ρ₂) C) :
    ShufflePlayW A (ρ₁ ++ ρ₂) C :=
  valley_cancel_same hwf h₁ hpull h₂

/-- **One-letter interior** — the inductive step in the smallest case:
one slide-free letter `m` between the pull and the raise, with the
swapped-order certificate `∃ e, ShufflePlayW S [raise c, m] e` saying `m`
is independent of `c` and its base. -/
theorem bracket_delete_one {A A' S C : State} {ρ₁ ρ₂ : List Move} {c : Card} {b : Base}
    {m : Move}
    (hwf : A.WF) (h₁ : ShufflePlayW A ρ₁ A')
    (hpull : State.step A' (Move.foundToTab c b) = some S)
    (hbr : ShufflePlayW S (m :: Move.tabToFound c :: ρ₂) C)
    (hnsl : NoSlide m)
    (hcert : ∃ e, ShufflePlayW S [Move.tabToFound c, m] e) :
    ShufflePlayW A (ρ₁ ++ [m] ++ ρ₂) C := by
  refine bracket_delete_at (inner := [m]) hwf h₁ hpull hbr ?_ ?_
  · intro x hx
    rw [List.mem_singleton] at hx
    subst hx
    exact hnsl
  · intro pre mid q post hsplit hpre
    cases pre with
    | nil =>
        simp only [List.nil_append] at hsplit
        injection hsplit with hq hpost
        subst hq
        subst hpost
        have hmid : mid = S := by
          have hrun : S.run [] = some mid := Walk_run _ hpre
          have hS : S.run [] = some S := rfl
          exact Option.some.inj (hrun.symm.trans hS)
        subst hmid
        exact hcert
    | cons a as =>
        simp only [List.cons_append] at hsplit
        exact absurd hsplit (by simp)

/-! ## §7b. The inversion measure for the raise/pull alphabet

Target 3 asks for a well-founded measure: the number of `pull ; raise`
inversions.  The sorting *proof* below (§5) is by structural recursion
(equivalent termination, no `Nat` measure needed), but the measure and
the decrease lemma are recorded here: they certify that the licensed
rewrite `pull ; raise → raise ; pull` is terminating, and hence that the
normal form of §5 is what a measure-guided bubble sort would reach. -/

/-- Shape test for the raise letter. -/
def isRaiseB : Move → Bool
  | Move.tabToFound _ => true
  | _ => false

/-- Shape test for the pull letter. -/
def isPullB : Move → Bool
  | Move.foundToTab _ _ => true
  | _ => false

theorem isPullB_eq_true {m : Move} (h : IsPull m) : isPullB m = true := by
  obtain ⟨c, b, rfl⟩ := h
  rfl

theorem isRaiseB_eq_true {m : Move} (h : IsRaise m) : isRaiseB m = true := by
  obtain ⟨c, rfl⟩ := h
  rfl

theorem isPullB_eq_false_of_raise {m : Move} (h : IsRaise m) : isPullB m = false := by
  obtain ⟨c, rfl⟩ := h
  rfl

theorem isRaiseB_eq_false_of_pull {m : Move} (h : IsPull m) : isRaiseB m = false := by
  obtain ⟨c, b, rfl⟩ := h
  rfl

/-- Number of letters satisfying a shape test. -/
def countTrue (p : Move → Bool) : List Move → Nat
  | [] => 0
  | m :: t => (if p m then 1 else 0) + countTrue p t

theorem countTrue_append (p : Move → Bool) : ∀ (a b : List Move),
    countTrue p (a ++ b) = countTrue p a + countTrue p b := by
  intro a
  induction a with
  | nil => intro b; simp [countTrue]
  | cons c cs ih =>
      intro b
      simp only [List.cons_append, countTrue, ih]
      omega

/-- `countTrue` is invariant under swapping two adjacent letters. -/
theorem countTrue_swap (p : Move → Bool) : ∀ (pre : List Move) (a b : Move) (post : List Move),
    countTrue p (pre ++ a :: b :: post) = countTrue p (pre ++ b :: a :: post) := by
  intro pre
  induction pre with
  | nil =>
      intro a b post
      simp only [List.nil_append, countTrue]
      rcases hpa : p a with _ | _ <;> rcases hpb : p b with _ | _ <;>
        simp [hpa, hpb, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
  | cons c cs ih =>
      intro a b post
      simp only [List.cons_append, countTrue, ih]

/-- **THE INVERSION COUNT**: ordered pairs `pull ; raise`. -/
def invCount : List Move → Nat
  | [] => 0
  | m :: t => (if isPullB m then countTrue isRaiseB t else 0) + invCount t

/-- **THE MEASURE DECREASES.**  Swapping an adjacent `pull ; raise` into
`raise ; pull` lowers the inversion count by exactly one — so the
licensed rewrite is terminating and every maximal rewrite chain reaches
the raise-block/pull-block normal form. -/
theorem invCount_swap_adj : ∀ (pre : List Move) {p r : Move} {post : List Move},
    IsPull p → IsRaise r →
    invCount (pre ++ p :: r :: post) = invCount (pre ++ r :: p :: post) + 1 := by
  intro pre
  induction pre with
  | nil =>
      intro p r post hp hr
      have hp' : isPullB p = true := isPullB_eq_true hp
      have hr' : isRaiseB r = true := isRaiseB_eq_true hr
      have hpr : isPullB r = false := isPullB_eq_false_of_raise hr
      have hrp : isRaiseB p = false := isRaiseB_eq_false_of_pull hp
      simp only [List.nil_append, invCount, countTrue]
      rw [hp', hr', hpr, hrp]
      simp
      omega
  | cons a as ih =>
      intro p r post hp hr
      simp only [List.cons_append, invCount]
      rw [countTrue_swap isRaiseB, ih (p := p) (r := r) (post := post) hp hr]
      omega

/-! ## §8. Axiom profiles -/

#print axioms walk_split
#print axioms swap_at_aux
#print axioms swap_at
#print axioms pair_play_iff
#print axioms swap_head
#print axioms bubble_raise_left
#print axioms bubble_one
#print axioms bubble_pull_right
#print axioms raisesPullsPlay_of_play
#print axioms sort_raises
#print axioms mountain_of_sorted
#print axioms mountain_of_shuffle
#print axioms mountain_of_raiseBlock
#print axioms mountain_of_pullBlock
#print axioms valley_cancel_same
#print axioms bracket_delete_at
#print axioms bracket_delete_nil
#print axioms bracket_delete_one
#print axioms countTrue_append
#print axioms countTrue_swap
#print axioms invCount_swap_adj

end Bubble
