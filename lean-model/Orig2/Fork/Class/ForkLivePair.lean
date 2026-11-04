import Orig2.Fork.Split.ForkSplitResidual

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

/-!
# Orig2/ForkLivePair - live-set geometry and the shortened split

READ-ONLY scratch card: no source edits, no commits.  Zero `sorry`, zero
`Classical.choice`, zero `native_decide`; the axiom battery is at the tail.

## Status (2026-11-02)

The `SplitLivePair` residual is **FALSE** (`TwinAt.not_splitLivePair_of_corner`,
`Orig2/Fork/Class/ForkTwinAt.lean`).  The constructors
`splitLivePair_of_landing_ne/_block/_forkAtRaise/_valleyElim` and the
`splitResidualData_of_valleyElim_*` capstones were therefore **removed**
(archived in `Archive/WITHDRAWN_DEFS.md`).  The residual definition and its
live kernel refutation are kept as evidence anchors.

## What remains (all kernel-checked)

* section 1 - the geometric core: two seats of one card pin the twin;
* section 2 - the live set at the bottom is the live set at the pull landing;
* section 3 - the local landing residual `SplitLiveAtLanding` (route withdrawn);
* section 4 - `ValleyElimForkAtRaise` and its pinning step from
  `ValleyElimNonfork`;
* section 5 - the complete local identity rule (`FullCancel` W3) and the
  minimality discriminator;
* section 5b - `SplitNe` / `SplitBlock` from the commutation premise.
-/

namespace LiveKit

open SplitKit

/-! ## §1. The geometric core: two seats of one card pin the twin -/

theorem live_iff_of_free_tail {B F : State} {post : List Move}
    (hpost : ShufflePlayW B post F)
    (hfree : ∀ m ∈ post, ValleyElim.FreeMove m) (hB : B.WF) (e : Card) :
    CanRaiseS F e ↔ CanRaiseS B e :=
  (Bridge.canRaiseS_of_free_play_iff hpost hfree hB e).symm

/-- **THE LIVE SET AT THE BOTTOM IS CONTAINED IN THE PULL CARD'S PAIR**, given
the same containment at the pull's landing.  This is the exact pointwise
reading of the task's suggested missing lemma. -/
theorem contained_at_F_of_landing
    {u v : State} {ρ : List Move} {F : State}
    {left right : List Move} {c d : Card} {b : Base}
    {pre post tail : List Move}
    (h : SplitHyp u v ρ F left right c d b pre post tail)
    (hcont : ∀ (A' B : State), ShufflePlayW u pre A' →
      State.step A' (Move.foundToTab c b) = some B →
      ∀ e, CanRaiseS B e → e = c ∨ e = c.twin) :
    ∀ e, CanRaiseS F e → e = c ∨ e = c.twin := by
  obtain ⟨huwf, -, -, -, -, -, -, hleft, -, hshape, hfree, -⟩ := h
  obtain ⟨A', hpre, hrest⟩ :=
    ValleyElim.ShufflePlayW_split hleft pre (Move.foundToTab c b :: post) hshape
  cases hrest with
  | @cons _ B _ _ _ hrev hstep hpost =>
      have hAwf : A'.WF := SatDifferCensus.ShufflePlayW.wf_end hpre huwf
      have hBwf : B.WF := step_wf hAwf hstep
      intro e he
      exact hcont A' B hpre hstep e (live_iff_of_free_tail hpost hfree hBwf e |>.mp he)

/-! ## §3. The local landing residual (route withdrawn) -/

/-- **THE LOCAL LIVE-SET RESIDUAL** (the task's suggested missing lemma): at
the pull's landing, every S-live card is the pull card or its twin. -/
def SplitLiveAtLanding : Prop :=
  ∀ (u v : State) (ρ : List Move) (F : State)
    (left right : List Move) (c d : Card) (b : Base)
    (pre post tail : List Move) (A' B : State),
    SplitHyp u v ρ F left right c d b pre post tail →
    ShufflePlayW u pre A' →
    State.step A' (Move.foundToTab c b) = some B →
    ∀ e, CanRaiseS B e → e = c ∨ e = c.twin

/-! ## §4. `ValleyElimForkAtRaise` and the pinning step -/

/-- **THE EXACT CONSUMED RESIDUAL** — the disjunctive valley-elimination form
with the fork *pinned to the split's raise card* `d`: at the bottom, either
`ForkWitness F d` already holds, or the play strictly shortens.  This is the
only shape `SplitLivePair` consumes (the fork branch is exactly
`TwinLivePair F d`). -/
def ValleyElimForkAtRaise : Prop :=
  ∀ (u v : State) (ρ : List Move) (F : State)
    (left right : List Move) (c d : Card) (b : Base)
    (pre post tail : List Move),
    SplitHyp u v ρ F left right c d b pre post tail →
    ForkWitness F d ∨
      (∃ ρ' : List Move, ShufflePlayW u ρ' v ∧ ρ'.length < ρ.length)

/-- **THE PINNING STEP.**  `ValleyElim.ValleyElimNonfork`'s fork is on *some*
card `x`; at the split's raise card it is on `d`.  Indeed `d` is S-live
(`splitHyp_green`), so the fork's live set puts it in `{x, x.twin}`; it cannot
be the blocked `x.twin` (it is vanilla-raisable at `F`), hence `d = x`. -/
theorem valleyElimForkAtRaise_of_valleyElim
    (helim : ValleyElim.ValleyElimNonfork) : ValleyElimForkAtRaise := by
  intro u v ρ F left right c d b pre post tail h
  obtain ⟨-, -, hcanD, hSFd⟩ := splitHyp_green h
  obtain ⟨huwf, hsu, hsv, hplay, hsplitAt, hmin, hρ, hleft, hright, hshape,
    hfree, hrightShape⟩ := h
  rcases helim u v ρ F huwf hsu hsv hplay
      ⟨left, right, c, d, b, pre, post, tail,
        hρ, hleft, hright, hshape, hfree, hrightShape⟩ with
    ⟨x, hx⟩ | ⟨ρ', hρ', hlen⟩
  · left
    have hdx : d = x := by
      rcases (hx.1 d).mpr hSFd with h' | h'
      · exact h'
      · exfalso
        exact hx.2 (by rw [h'] at hcanD; exact hcanD)
    rw [hdx]
    exact hx
  · exact Or.inr ⟨ρ', hρ', hlen⟩

/-! ## §5. The complete local identity rule (`FullCancel` W3)

`Temp/FullCancel_Report.md:331-334` states the correct cancellation rule: for
adjacent letters `m1 ; m2` at a state `A`, if `step (step A m1) m2 = A`, delete
both.  This is strictly stronger than the old same-card pull/raise rule: it
also covers `raise ; pull-back` and the 2-move slide/slide loops
(`FullCancel_Report.md:396-412`, smallest witness `S4C>5H ; S4C>5D`).

The deletions below are kernel-level.  The identity hypothesis is exactly
"the pair returns to its origin"; the shorter play is `α ++ β`, and the
continuation `β` is read off the original play at the pair's exit state. -/

/-- An adjacent pair that returns to the state it started from. -/
def IdentityPair (A T : State) (m1 m2 : Move) : Prop :=
  State.step A m1 = some T ∧ State.step T m2 = some A

/-- **W3 — COMPLETE LOCAL IDENTITY DELETION.**  If a witness play factors as
`α ++ m1 :: m2 :: β` with an identity pair at the seam, then the pair deletes:
`α ++ β` is a strictly shorter witness play with the same endpoints. -/
theorem identity_pair_delete
    {u v : State} {ρ α β : List Move} {m1 m2 : Move} {A T : State}
    (hplay : ShufflePlayW u ρ v)
    (hρ : ρ = α ++ m1 :: m2 :: β)
    (hα : ShufflePlayW u α A)
    (hid : IdentityPair A T m1 m2) :
    ∃ ρ' : List Move, ShufflePlayW u ρ' v ∧ ρ'.length < ρ.length := by
  obtain ⟨h1, h2⟩ := hid
  have hρ' : ρ = (α ++ [m1, m2]) ++ β := by
    rw [hρ]
    simp
  obtain ⟨Z, hpre, hβZ⟩ :=
    ValleyElim.ShufflePlayW_split hplay (α ++ [m1, m2]) β hρ'
  obtain ⟨A', hα', hrest⟩ :=
    ValleyElim.ShufflePlayW_split hpre α [m1, m2] rfl
  -- the prefix `α` is deterministic: `A' = A`
  have hA' : A' = A := by
    have r1 := Walk_run _ hα'
    have r2 := Walk_run _ hα
    exact Option.some.inj (r1.symm.trans r2)
  subst A'
  cases hrest with
  | @cons _ T' _ _ _ hrev1 hstep1 hrest1 =>
      cases hrest1 with
      | @cons _ Z' _ _ _ hrev2 hstep2 hnil =>
          cases hnil
          have hT' : T' = T := Option.some.inj (hstep1.symm.trans h1)
          rw [hT'] at hstep2
          have hZ : Z = A := Option.some.inj (hstep2.symm.trans h2)
          rw [hZ] at hβZ
          refine ⟨α ++ β, ShufflePlayW_append hα hβZ, ?_⟩
          rw [hρ]
          simp only [List.length_append, List.length_cons]
          omega

/-- **Adjacent `pull c ; raise c` is an identity pair.**  This is the old
same-card rule, now a special case of W3 (`step_tabToFound_of_foundToTab`,
`Orig2/Substrate/Classification.lean:1011`). -/
theorem pull_raise_identity_pair {A B : State} {c : Card} {b : Base}
    (hA : A.WF) (hstep : State.step A (Move.foundToTab c b) = some B) :
    IdentityPair A B (Move.foundToTab c b) (Move.tabToFound c) :=
  ⟨hstep, step_tabToFound_of_foundToTab hA hstep⟩

/-- **A 2-move slide/slide loop is an identity pair** — the new family that
the old rule misses (smallest witness `S4C>5H ; S4C>5D`,
`FullCancel_Report.md:396-412`). -/
theorem slide_slide_identity_pair {A B : State} {c : Card} {b1 b2 : Base}
    (h1 : State.step A (Move.tabToTab c b1) = some B)
    (h2 : State.step B (Move.tabToTab c b2) = some A) :
    IdentityPair A B (Move.tabToTab c b1) (Move.tabToTab c b2) :=
  ⟨h1, h2⟩

theorem pull_raise_pair_shortens
    {u v : State} {ρ α β : List Move} {c : Card} {b : Base} {A B : State}
    (hplay : ShufflePlayW u ρ v)
    (hρ : ρ = α ++ Move.foundToTab c b :: Move.tabToFound c :: β)
    (hα : ShufflePlayW u α A) (hA : A.WF)
    (hstep : State.step A (Move.foundToTab c b) = some B) :
    ∃ ρ' : List Move, ShufflePlayW u ρ' v ∧ ρ'.length < ρ.length :=
  identity_pair_delete hplay hρ hα (pull_raise_identity_pair hA hstep)

/-- **A SHORTEST PLAY CONTAINS NO IDENTITY PAIR.**  Contrapositive of W3. -/
theorem shortest_no_identity_pair {u v : State} {ρ : List Move}
    (hplay : ShufflePlayW u ρ v)
    (hmin : ∀ ρ' : List Move, ShufflePlayW u ρ' v → ρ.length ≤ ρ'.length)
    {α β : List Move} {m1 m2 : Move} {A T : State}
    (hρ : ρ = α ++ m1 :: m2 :: β)
    (hα : ShufflePlayW u α A) (hid : IdentityPair A T m1 m2) : False := by
  obtain ⟨ρ', hρ', hlen⟩ := identity_pair_delete hplay hρ hα hid
  exact absurd hlen (Nat.not_lt.mpr (hmin ρ' hρ'))

/-- **AT A SHORTEST SPLIT BOTTOM NO IDENTITY PAIR OCCURS.**  This is W3 read at
`SplitHyp`: any adjacent `m1 ; m2` returning to its origin would strictly
shorten `ρ`.  In the non-minimal census the offending pair is a same-card
`pull z … raise z` bracket; it becomes an *adjacent* identity pair only after
the raise is commuted left across the free tail (`Temp/FullCancel_Report.md`
§5.2, §6.1), which is the remaining commutation premise. -/
theorem splitHyp_no_identity_pair
    {u v : State} {ρ : List Move} {F : State}
    {left right : List Move} {c d : Card} {b : Base}
    {pre post tail : List Move}
    (h : SplitHyp u v ρ F left right c d b pre post tail)
    {α β : List Move} {m1 m2 : Move} {A T : State}
    (hρ : ρ = α ++ m1 :: m2 :: β)
    (hα : ShufflePlayW u α A) (hid : IdentityPair A T m1 m2) : False := by
  obtain ⟨huwf, -, -, hplay, -, hmin, -⟩ := h
  exact shortest_no_identity_pair hplay hmin hρ hα hid

/-! ## §5b. `SplitNe` / `SplitBlock` from the commutation that feeds W3

In the `c = d` case the same-card bracket `pull c … raise c` is separated by
the free tail `post`.  W3 then fires as soon as the raise is commuted left
across `post`, making the pair adjacent.  The commutation is isolated as the
named premise `PostCommutesRaise`; everything else (the W3 deletion, the
minimality contradiction) is proved. -/

/-- **THE COMMUTATION PREMISE.**  If the split's cards coincide (`c = d`), the
first raise can be moved left across the free tail, i.e. the rearranged list
`pre ++ pull c b :: raise c :: post ++ tail` is again a witness play `u → v`.
For free `post` this is the slide/raise and pull/raise commutation of
`Temp/Commute_Step_Report.md` (the pair may also be a slide/slide loop, in
which case no commutation at all is needed). -/
def PostCommutesRaise : Prop :=
  ∀ (u v : State) (ρ : List Move) (F : State)
    (left right : List Move) (c d : Card) (b : Base)
    (pre post tail : List Move),
    SplitHyp u v ρ F left right c d b pre post tail → c = d →
    ShufflePlayW u
      (pre ++ Move.foundToTab c b :: Move.tabToFound c :: (post ++ tail)) v

/-- **`SplitNe` FROM THE COMMUTATION.**  If `c = d`, the commuted play has the
adjacent identity pair `pull c ; raise c` at the seam; W3 deletes it and
strictly shortens `ρ`, contradicting shortest-ness. -/
theorem splitNe_of_postCommutesRaise (hc : PostCommutesRaise) : SplitNe := by
  intro u v ρ F left right c d b pre post tail h hcd
  have hmin := h.2.2.2.2.2.1
  have hρ : ρ = left ++ right := h.2.2.2.2.2.2.1
  have hleft : ShufflePlayW u left F := h.2.2.2.2.2.2.2.1
  have hrightShape : right = Move.tabToFound d :: tail := h.2.2.2.2.2.2.2.2.2.2.2
  have hshape : left = pre ++ Move.foundToTab c b :: post := h.2.2.2.2.2.2.2.2.2.1
  -- the commuted play
  have hcomm := hc u v ρ F left right c d b pre post tail h hcd
  -- the pull fires from the prefix's endpoint
  obtain ⟨A, hpre, hrest⟩ :=
    ValleyElim.ShufflePlayW_split hleft pre (Move.foundToTab c b :: post) hshape
  cases hrest with
  | @cons _ B _ _ _ hrev hstep hpost =>
      have hAwf : A.WF := SatDifferCensus.ShufflePlayW.wf_end hpre h.1
      -- W3 at the seam
      obtain ⟨ρ', hρ'play, hlen⟩ :=
        pull_raise_pair_shortens
          (u := u) (v := v)
          (ρ := pre ++ Move.foundToTab c b :: Move.tabToFound c :: (post ++ tail))
          (α := pre) (β := post ++ tail) (c := c) (b := b) (A := A) (B := B)
          hcomm rfl hpre hAwf hstep
      -- lengths: the commuted list is a permutation, hence the same length
      have hlenC :
          (pre ++ Move.foundToTab c b :: Move.tabToFound c :: (post ++ tail)).length
            = ρ.length := by
        rw [hρ, hshape, hrightShape, ← hcd]
        simp only [List.length_append, List.length_cons]
        omega
      rw [hlenC] at hlen
      exact absurd hlen (Nat.not_lt.mpr (hmin ρ' hρ'play))

/-- **`SplitBlock` FROM `ValleyElimNonfork` + `SplitNe`.**  Under the pinned
fork, `CanRaise F c` forces `c = d` (the pull card is live, so it is the
raisable fork card or its blocked twin; the blocked twin is excluded by the
licence), and `SplitNe` forbids `c = d`. -/
theorem splitBlock_of_valleyElim_ne
    (helim : ValleyElim.ValleyElimNonfork) (hne : SplitNe) : SplitBlock := by
  intro u v ρ F left right c d b pre post tail h hcan
  have hgreen := splitHyp_green h
  have hne' : c ≠ d := hne u v ρ F left right c d b pre post tail h
  obtain ⟨huwf, hsu, hsv, hplay, hsplitAt, hmin, hρ, hleft, hright, hshape,
    hfree, hrightShape⟩ := h
  obtain ⟨-, hSFc, -, -⟩ := hgreen
  rcases (valleyElimForkAtRaise_of_valleyElim helim) u v ρ F left right c d b
      pre post tail
      ⟨huwf, hsu, hsv, hplay, hsplitAt, hmin, hρ, hleft, hright, hshape,
        hfree, hrightShape⟩ with hx | ⟨ρ', hρ', hlen⟩
  · rcases (hx.1 c).mpr hSFc with h' | h'
    · exact hne' h'
    · exact hx.2 (by rw [h'] at hcan; exact hcan)
  · exact absurd hlen (Nat.not_lt.mpr (hmin ρ' hρ'))

/-- **`SplitBlock` FROM `ValleyElimNonfork` + THE COMMUTATION.** -/
theorem splitBlock_of_valleyElim_postCommutes
    (helim : ValleyElim.ValleyElimNonfork) (hc : PostCommutesRaise) :
    SplitBlock :=
  splitBlock_of_valleyElim_ne helim (splitNe_of_postCommutesRaise hc)

/-! ## §7. Axiom battery -/

#print axioms live_iff_of_free_tail
#print axioms contained_at_F_of_landing
#print axioms valleyElimForkAtRaise_of_valleyElim
#print axioms identity_pair_delete
#print axioms pull_raise_identity_pair
#print axioms slide_slide_identity_pair
#print axioms pull_raise_pair_shortens
#print axioms shortest_no_identity_pair
#print axioms splitHyp_no_identity_pair
#print axioms splitNe_of_postCommutesRaise
#print axioms splitBlock_of_valleyElim_ne
#print axioms splitBlock_of_valleyElim_postCommutes

end LiveKit
