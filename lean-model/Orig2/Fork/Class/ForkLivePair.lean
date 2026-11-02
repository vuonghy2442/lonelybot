import Orig2.Fork.Split.ForkSplitResidual

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

/-!
# Orig2/ForkLivePair — proving `SplitKit.SplitLivePair`

READ-ONLY scratch card: no source edits, no commits.  Zero `sorry`, zero
`Classical.choice`, zero `native_decide`; the axiom battery is at the tail.

## What is proved here

The redirected target is `SplitKit.SplitLivePair`:

```
SplitLivePair := ∀ …, SplitHyp u v ρ F left right c d b pre post tail →
                  TwinLivePair F d
```

## Reductions proved kernel-checked

1. **`SplitLivePair` from `ValleyElim.ValleyElimNonfork` (no extra input).**
   `ValleyElimNonfork` (`Orig2/Fork/Split/ForkSplit.lean:864`) is the campaign's
   existing valley-elimination residual: at every valley split either a
   `ForkWitness` already sits at the bottom, or the play strictly shortens.
   The shortest-play conjunct of `SplitHyp` kills the shortening branch, and
   the fork branch pins the raise card `d` to the fork's raisable card `x`
   (`d ≠ x.twin` because the fork blocks `x.twin`), so the live set at `F`
   is exactly `{d, d.twin}`.  This is `splitLivePair_of_valleyElim`.

2. **`SplitLivePair` from a local live-set residual**
   `SplitLiveAtLanding` (the task's suggested missing lemma: *the live set
   at the pull's landing is contained in `{c, c.twin}`*), plus the `SplitNe`
   pin.  This is `splitLivePair_of_landing_ne`, with
   `splitLivePair_of_landing_block` as the `SplitBlock`-fed form.

3. **The complete local identity rule (W3, `Temp/FullCancel_Report.md`).**
   `identity_pair_delete` deletes any adjacent pair `m1 ; m2` with
   `step (step A m1) m2 = A`; it covers the old `pull ; raise` family
   (`pull_raise_identity_pair`), the 2-move slide/slide loops
   (`slide_slide_identity_pair`, smallest witness `S4C>5H ; S4C>5D`), and
   raise-then-pull-back.  `shortest_no_identity_pair` /
   `splitHyp_no_identity_pair` read it contrapositively at a shortest split,
   and `post_nil_turn_ne` is the `post = []` split-bottom application.

4. **`SplitNe` and `SplitBlock` from the commutation that feeds W3.**
   If `c = d`, commuting the raise left across the free tail makes
   `pull c ; raise c` adjacent, and W3 shortens the play.  The commutation is
   the named premise `PostCommutesRaise`; `splitNe_of_postCommutesRaise` is
   the kernel-checked deletion, and
   `splitBlock_of_valleyElim_ne` / `splitBlock_of_valleyElim_postCommutes`
   combine it with the pinned fork.

The geometric half of the twin mechanism is also proved unconditionally
(`eq_twin_of_cover_seat`): if the cover card `x` of `c` at the bottom was
seated on `d` at an earlier state of the play, then `d = c.twin`.  This is
the probe's "one free slide moves `x` off `c.twin` onto `c`", reduced to
pure `canSitOn` arithmetic (`tfc_fitting_parent`).

## Consequence

`ValleyElimNonfork ∧ SplitBlock ⇒ SplitResidualData` and hence the bridge
chain (`bottomDip_of_valleyElim_block`,
`satDifferForkWF_of_valleyElim_block_drainClosed`).  The sharper capstone is
`splitResidualData_of_valleyElim_postCommutes`:
`ValleyElimNonfork ∧ PostCommutesRaise ⇒ SplitResidualData`, i.e. the
corrected residual reduces to the existing valley-elimination residual plus
the one explicit commutation premise consumed by W3.
-/

namespace LiveKit

open SplitKit

/-! ## §1. The geometric core: two seats of one card pin the twin -/

/-- **THE FITTING-PARENT PIN.**  If one card `x` fits on both `c` and `z`,
then `z` is `c` or `c.twin`.  (`tfc_fitting_parent`,
`Orig2/Substrate/CargoKit.lean:929`.) -/
theorem parent_eq_or_twin {x c z : Card}
    (h1 : canSitOn x c = true) (h2 : canSitOn x z = true) :
    z = c ∨ z = c.twin := by
  rcases tfc_fitting_parent h2 h1 with h | h
  · exact Or.inl h
  · exact Or.inr h

/-- **A SEATED CARD FITS ON ITS PARENT.**  (`tfc_seatOf_of_inr` +
`tfc_seat_parent`, `Orig2/Substrate/CargoKit.lean:976`.) -/
theorem canSitOn_of_seat {st : State} (hwf : st.WF) {x p : Card}
    (h : seatOf st x = some (Sum.inr p)) : canSitOn x p = true := by
  obtain ⟨a, hhold, -, hlast⟩ := tfc_seatOf_of_inr h
  exact (tfc_seat_parent hwf hhold hlast).1

/-- **TWO SEATS OF THE SAME CARD PIN THE PARENT.**  If `x` sits on `c` at a
`WF` state `F` and on `z` at a `WF` state `B`, then `z = c ∨ z = c.twin`.
This is the card arithmetic of the probe's cover slide. -/
theorem seat_parents_eq_or_twin {F B : State} (hF : F.WF) (hB : B.WF)
    {x c z : Card}
    (hc : seatOf F x = some (Sum.inr c))
    (hz : seatOf B x = some (Sum.inr z)) :
    z = c ∨ z = c.twin :=
  parent_eq_or_twin (canSitOn_of_seat hF hc) (canSitOn_of_seat hB hz)

/-- **THE TWIN-SOURCE COVER PIN.**  If the card `x` covering `c` at the
bottom `F` was seated on `d` at an earlier `WF` state `B` of the play, and
`c ≠ d`, then `d = c.twin`.  This is the exact kernel shape suggested by
`Temp/SplitProbe_Report.md:415-422`. -/
theorem eq_twin_of_cover_seat {F B : State} (hF : F.WF) (hB : B.WF)
    {c d x : Card}
    (hcov : seatOf F x = some (Sum.inr c))
    (hsrc : seatOf B x = some (Sum.inr d))
    (hne : c ≠ d) : d = c.twin := by
  rcases seat_parents_eq_or_twin hF hB hcov hsrc with h | h
  · exact absurd h.symm hne
  · exact h

/-! ## §2. The live set at the bottom is the live set at the pull landing -/

/-- The live set is unchanged by the free tail `post`
(`Bridge.canRaiseS_of_free_play_iff`, `Orig2/Fork/Split/ForkBridge.lean:85`). -/
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

/-! ## §3. `SplitLivePair` from the local landing residual -/

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

/-- **`SplitLivePair` FROM THE LANDING CONTAINMENT PLUS `c ≠ d`.**  At `F`,
`d` is live, so containment puts it in `{c, c.twin}`; `c ≠ d` excludes
`d = c`, so `d = c.twin` and the live set is the twin pair of `d`. -/
theorem splitLivePair_of_landing_ne
    (hland : SplitLiveAtLanding) (hne : SplitNe) : SplitLivePair := by
  intro u v ρ F left right c d b pre post tail h
  have hcontF := contained_at_F_of_landing h
    (fun A' B hpre hstep =>
      hland u v ρ F left right c d b pre post tail A' B h hpre hstep)
  have hcd : c ≠ d := hne u v ρ F left right c d b pre post tail h
  obtain ⟨-, hSFc, hcanD, hSFd⟩ := splitHyp_green h
  have hdt : d = c.twin := by
    rcases hcontF d hSFd with h' | h'
    · exact absurd h' (Ne.symm hcd)
    · exact h'
  have hdtc : d.twin = c := by rw [hdt, card_twin_twin]
  have hSFdt : CanRaiseS F d.twin := by
    rw [hdtc]; exact hSFc
  intro e
  constructor
  · intro he
    rcases hcontF e he with h' | h'
    · exact Or.inr (h'.trans hdtc.symm)
    · exact Or.inl (h'.trans hdt.symm)
  · rintro (h' | h')
    · rw [h']; exact hSFd
    · rw [h']; exact hSFdt

/-- **`SplitLivePair` FROM THE LANDING CONTAINMENT PLUS `SplitBlock`.**  The
block gives `¬ CanRaise F c`, and `d` is vanilla-raisable at `F`, so `c ≠ d`. -/
theorem splitLivePair_of_landing_block
    (hland : SplitLiveAtLanding) (hblock : SplitBlock) : SplitLivePair := by
  refine splitLivePair_of_landing_ne hland ?_
  intro u v ρ F left right c d b pre post tail h
  obtain ⟨-, -, hcanD, -⟩ := splitHyp_green h
  intro hcd
  exact hblock u v ρ F left right c d b pre post tail h
    (by rw [hcd]; exact hcanD)

/-! ## §4. `SplitLivePair` from the campaign's valley-elimination residual -/

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

/-- **`SplitLivePair` FROM THE PINNED RESIDUAL.**  The fork branch *is* the
live-pair clause; the shortening branch contradicts the shortest-play
conjunct of `SplitHyp`. -/
theorem splitLivePair_of_forkAtRaise
    (hf : ValleyElimForkAtRaise) : SplitLivePair := by
  intro u v ρ F left right c d b pre post tail h
  obtain ⟨huwf, hsu, hsv, hplay, hsplitAt, hmin, hρ, hleft, hright, hshape,
    hfree, hrightShape⟩ := h
  rcases hf u v ρ F left right c d b pre post tail
      ⟨huwf, hsu, hsv, hplay, hsplitAt, hmin, hρ, hleft, hright, hshape,
        hfree, hrightShape⟩ with hx | ⟨ρ', hρ', hlen⟩
  · exact ((forkWitness_iff F d).mp hx).1
  · exact absurd hlen (Nat.not_lt.mpr (hmin ρ' hρ'))

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

/-- **THE MAIN REDUCTION.**  `ValleyElim.ValleyElimNonfork` alone gives
`SplitLivePair`: minimality kills the elimination branch, and at the fork the
raise card `d` is the fork's raisable card `x` (it cannot be the blocked
`x.twin`), so the live set at `F` is exactly `{d, d.twin}`.

No `SplitBlock`, no `SplitNe`, no extra geometric input. -/
theorem splitLivePair_of_valleyElim
    (helim : ValleyElim.ValleyElimNonfork) : SplitLivePair :=
  splitLivePair_of_forkAtRaise (valleyElimForkAtRaise_of_valleyElim helim)

/-- **The same reduction for the twin clause**, routed through
`splitTwin_of_livePair_block`. -/
theorem splitTwin_of_valleyElim_block
    (helim : ValleyElim.ValleyElimNonfork) (hblock : SplitBlock) : SplitTwin :=
  splitTwin_of_livePair_block (splitLivePair_of_valleyElim helim) hblock

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

/-- A slide/slide loop at the seam deletes both slides. -/
theorem slide_slide_pair_shortens
    {u v : State} {ρ α β : List Move} {c : Card} {b1 b2 : Base} {A B : State}
    (hplay : ShufflePlayW u ρ v)
    (hρ : ρ = α ++ Move.tabToTab c b1 :: Move.tabToTab c b2 :: β)
    (hα : ShufflePlayW u α A)
    (h1 : State.step A (Move.tabToTab c b1) = some B)
    (h2 : State.step B (Move.tabToTab c b2) = some A) :
    ∃ ρ' : List Move, ShufflePlayW u ρ' v ∧ ρ'.length < ρ.length :=
  identity_pair_delete hplay hρ hα (slide_slide_identity_pair h1 h2)

/-- A same-card pull/raise pair at the seam deletes both letters. -/
theorem pull_raise_pair_shortens
    {u v : State} {ρ α β : List Move} {c : Card} {b : Base} {A B : State}
    (hplay : ShufflePlayW u ρ v)
    (hρ : ρ = α ++ Move.foundToTab c b :: Move.tabToFound c :: β)
    (hα : ShufflePlayW u α A) (hA : A.WF)
    (hstep : State.step A (Move.foundToTab c b) = some B) :
    ∃ ρ' : List Move, ShufflePlayW u ρ' v ∧ ρ'.length < ρ.length :=
  identity_pair_delete hplay hρ hα (pull_raise_identity_pair hA hstep)

/-- **A SPLIT-BOTTOM APPLICATION (adjacent-turn case).**  If the free tail
`post` is empty, the split's turn IS an adjacent `pull c ; raise d`; shortest
plays therefore force `c ≠ d`.  This is the `post = []` corner of the
`SplitNe` pin, and it is exactly W3's pull/raise family
(`Bridge.shortest_adjacent_turn_ne`, `Orig2/Fork/Split/ForkBridge.lean:211`). -/
theorem post_nil_turn_ne
    {u v : State} {ρ : List Move} {F : State}
    {left right : List Move} {c d : Card} {b : Base}
    {pre post tail : List Move}
    (h : SplitHyp u v ρ F left right c d b pre post tail) (hpost : post = []) :
    c ≠ d := by
  obtain ⟨huwf, -, -, hplay, -, hmin, hρ, hleft, hright, hshape, hfree,
    hrightShape⟩ := h
  subst hpost
  -- rewrite the play into the adjacent-turn shape
  have hplay' : ShufflePlayW u
      (pre ++ Move.foundToTab c b :: Move.tabToFound d :: tail) v := by
    have hp := hplay
    rw [hρ, hshape, hrightShape] at hp
    simpa [List.append_assoc] using hp
  have hlen' : ∀ ρ' : List Move, ShufflePlayW u ρ' v →
      (pre ++ Move.foundToTab c b :: Move.tabToFound d :: tail).length ≤ ρ'.length := by
    intro ρ' hρ'
    have hlen := hmin ρ' hρ'
    rw [hρ, hshape, hrightShape] at hlen
    simpa [List.append_assoc] using hlen
  -- the prefix reaches the turn's pre-state
  have hleft' : ShufflePlayW u (pre ++ Move.foundToTab c b :: ([] : List Move)) F := by
    rw [← hshape]
    simpa using hleft
  obtain ⟨A', hpre, hrest⟩ :=
    ValleyElim.ShufflePlayW_split hleft' pre [Move.foundToTab c b] rfl
  -- the adjacent-turn theorem's `F` is that pre-state
  exact Bridge.shortest_adjacent_turn_ne huwf hpre hplay' hlen'

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

/-! ## §6. Consequence: the corrected residual from the named inputs -/

/-- **`SplitResidualData` FROM `ValleyElimNonfork` + `SplitBlock`.** -/
theorem splitResidualData_of_valleyElim_block
    (helim : ValleyElim.ValleyElimNonfork) (hblock : SplitBlock) :
    SplitResidualData :=
  splitResidualData_of_livePair_block (splitLivePair_of_valleyElim helim) hblock

/-- **`SplitResidualData` FROM THE LOCAL LANDING RESIDUAL + `SplitBlock`.** -/
theorem splitResidualData_of_landing_block
    (hland : SplitLiveAtLanding) (hblock : SplitBlock) : SplitResidualData :=
  splitResidualData_of_livePair_block
    (splitLivePair_of_landing_block hland hblock) hblock

/-- **`SplitResidualData` FROM `ValleyElimNonfork` + THE COMMUTATION.**  This
is the sharpest capstone here: the live-pair clause needs only the existing
valley-elimination residual, and the block clause needs the single explicit
commutation premise that lets W3 cancel the same-card bracket. -/
theorem splitResidualData_of_valleyElim_postCommutes
    (helim : ValleyElim.ValleyElimNonfork) (hc : PostCommutesRaise) :
    SplitResidualData :=
  splitResidualData_of_livePair_block
    (splitLivePair_of_valleyElim helim)
    (splitBlock_of_valleyElim_postCommutes helim hc)

/-- The bridge residual from the valley-elimination reduction. -/
theorem bottomDip_of_valleyElim_block
    (helim : ValleyElim.ValleyElimNonfork) (hblock : SplitBlock) :
    Bridge.BottomDip :=
  bottomDip_of_splitResidualData (splitResidualData_of_valleyElim_block helim hblock)

/-- The bridge residual from the landing-containment reduction. -/
theorem bottomDip_of_landing_block
    (hland : SplitLiveAtLanding) (hblock : SplitBlock) : Bridge.BottomDip :=
  bottomDip_of_splitResidualData (splitResidualData_of_landing_block hland hblock)

/-- **THE FULL CHAIN from `ValleyElimNonfork` + `SplitBlock`** (the drain is
discharged by `Bridge.forkExistenceFromAsymmetry_drainClosed`). -/
theorem satDifferForkWF_of_valleyElim_block_drainClosed
    (helim : ValleyElim.ValleyElimNonfork) (hblock : SplitBlock)
    (hmin : ValleyElim.ShortestPlayExists) : SatDifferForkWF :=
  satDifferForkWF_of_splitResidualData_drainClosed
    (splitResidualData_of_valleyElim_block helim hblock) hmin

/-- **THE FULL CHAIN from the local landing residual + `SplitBlock`.** -/
theorem satDifferForkWF_of_landing_block_drainClosed
    (hland : SplitLiveAtLanding) (hblock : SplitBlock)
    (hmin : ValleyElim.ShortestPlayExists) : SatDifferForkWF :=
  satDifferForkWF_of_splitResidualData_drainClosed
    (splitResidualData_of_landing_block hland hblock) hmin

/-- The bridge residual from `ValleyElimNonfork` + the commutation. -/
theorem bottomDip_of_valleyElim_postCommutes
    (helim : ValleyElim.ValleyElimNonfork) (hc : PostCommutesRaise) :
    Bridge.BottomDip :=
  bottomDip_of_splitResidualData
    (splitResidualData_of_valleyElim_postCommutes helim hc)

/-- **THE FULL CHAIN from `ValleyElimNonfork` + the commutation.** -/
theorem satDifferForkWF_of_valleyElim_postCommutes_drainClosed
    (helim : ValleyElim.ValleyElimNonfork) (hc : PostCommutesRaise)
    (hmin : ValleyElim.ShortestPlayExists) : SatDifferForkWF :=
  satDifferForkWF_of_splitResidualData_drainClosed
    (splitResidualData_of_valleyElim_postCommutes helim hc) hmin

/-! ## §7. Axiom battery -/

#print axioms parent_eq_or_twin
#print axioms canSitOn_of_seat
#print axioms seat_parents_eq_or_twin
#print axioms eq_twin_of_cover_seat
#print axioms live_iff_of_free_tail
#print axioms contained_at_F_of_landing
#print axioms splitLivePair_of_landing_ne
#print axioms splitLivePair_of_landing_block
#print axioms splitLivePair_of_forkAtRaise
#print axioms valleyElimForkAtRaise_of_valleyElim
#print axioms splitLivePair_of_valleyElim
#print axioms splitTwin_of_valleyElim_block
#print axioms identity_pair_delete
#print axioms pull_raise_identity_pair
#print axioms slide_slide_identity_pair
#print axioms slide_slide_pair_shortens
#print axioms pull_raise_pair_shortens
#print axioms post_nil_turn_ne
#print axioms shortest_no_identity_pair
#print axioms splitHyp_no_identity_pair
#print axioms splitNe_of_postCommutesRaise
#print axioms splitBlock_of_valleyElim_ne
#print axioms splitBlock_of_valleyElim_postCommutes
#print axioms splitResidualData_of_valleyElim_block
#print axioms splitResidualData_of_landing_block
#print axioms splitResidualData_of_valleyElim_postCommutes
#print axioms bottomDip_of_valleyElim_block
#print axioms bottomDip_of_landing_block
#print axioms bottomDip_of_valleyElim_postCommutes
#print axioms satDifferForkWF_of_valleyElim_block_drainClosed
#print axioms satDifferForkWF_of_landing_block_drainClosed
#print axioms satDifferForkWF_of_valleyElim_postCommutes_drainClosed

end LiveKit
