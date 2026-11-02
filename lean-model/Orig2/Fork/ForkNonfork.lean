import Orig2.Fork.ForkElim

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-!
# Orig2/ForkNonfork — the slide-tolerant bracket kit, and the local residual

READ-ONLY scratch (no source touched, no commit).  Zero `sorry`, zero
`Classical.choice`, no `native_decide`; battery at the tail.

This card attacks `Elim.NonforkBracketElim` (`Orig2/Fork/ForkElim.lean:363`) by
factoring its second disjunct into

```text
   (the same-card bracket exists)              -- combinatorial half
 ∧ (the raise bubbles left over its interior)  -- geometric half
```

and by removing the `NoSlide γ` restriction that every existing route to the
deletion carries (`Elim.bubble_bracket_shortens`,
`Landing.ThirdSuitBracketData`, `BlockKit.ThirdSuitBracketData`).

## What is proved here

1. **`raise_bubble`** — a raise `raise z` can be moved to the front of an
   arbitrary window `γ` of a witness play, with NO slide restriction.  The
   local datum consumed at each window position is `RaiseSwaps`-shaped: the
   two-letter word `[raise z, q]` is a witness play landing at the same state
   as `[q, raise z]`.  (`Bubble.bubble_raise_left` needs `NoSlide γ` because
   it gets this datum from the no-slide diamond; the slide/raise square
   `CommuteStep.step_comm_slide_raise` supplies it for slides, so the
   restriction is unnecessary.)

2. **`bracket_delete_gen`** — the play-level deletion of a same-card bracket
   `pull z ; γ ; raise z` for an ARBITRARY interior `γ`, from `RaiseSwaps`.
   This strictly strengthens `Elim.bracket_delete_of_commuted`'s only
   non-play input and drops `NoSlide γ` from `Elim.bubble_bracket_shortens`.

3. **`NonforkBracketLocal`** — the exact residual: every valley split either
   already has a fork at its bottom, or carries a same-card bracket whose
   raise bubbles left over the interior (`RaiseSwaps`).  This is
   `Elim.NonforkBracketElim` with the single hypothesis `hcomm` replaced by
   the per-position local datum — strictly more informative, and exactly the
   certificate the probe's W1/W2 witness plays satisfy
   (`Temp/SplitProbe_Report.md:270-308`).

4. **`nonforkBracketElim_of_local`** — `NonforkBracketLocal →
   Elim.NonforkBracketElim`.

5. **`local_of_samecard_nil`** — the `post = []`, `c = d` corner of the
   target: it already satisfies the STRONG (bracket) disjunct with empty
   interior, so that corner is discharged unconditionally.

The census (`Temp/Nonfork_commute_probe_out.txt`) shows that all 916
non-twin valley witness plays of `Temp/SplitProbe_minimality.py` satisfy the
*whole* `Elim.NonforkBracketElim` second disjunct verbatim; the successful
bracket is always either the valley pull card's own pair (588) or the
enclosing raise-card pair (328).  So the residual below is not vacuous.
-/

namespace NonforkKit

open ValleyElim
open CommuteStep

/-! ## §1. The local swap certificate -/

/-- **`RaiseSwaps Q z γ`** — the raise `raise z` swaps left across EVERY
position of the window `γ` starting from `Q`.  At each decomposition
`γ = pre ++ q :: rest` and each state `mid` reached by `pre`, the two-letter
word `[raise z, q]` is a witness play, and it lands where the ORIGINAL order
`[q, raise z]` lands.

This is the play-local read-invariance certificate: it says no interior letter
destroys `z`'s pending raise nor is disturbed by firing it first.  It is
exactly the shape `Bubble.bubble_raise_left` consumes, with the no-slide
diamond replaced by the endpoint identity. -/
def RaiseSwaps (Q : State) (z : Card) (γ : List Move) : Prop :=
  ∀ (pre : List Move) (mid : State) (q : Move) (rest : List Move),
    pre ++ q :: rest = γ → ShufflePlayW Q pre mid →
    ∃ e, ShufflePlayW mid [Move.tabToFound z, q] e ∧
         mid.run [q, Move.tabToFound z] = some e

/-- The empty window needs no certificate. -/
theorem raiseSwaps_nil (Q : State) (z : Card) : RaiseSwaps Q z [] := by
  intro pre mid q rest hsplit _
  cases pre with
  | nil => exact absurd hsplit (by simp)
  | cons a as => exact absurd hsplit (by simp)

/-! ## §2. The slide-tolerant raise bubble -/

/-- **RAISE BUBBLE (no slide restriction).**  Move `raise z` to the front of
an arbitrary window of a witness play.  Only the local certificate
`RaiseSwaps` is consumed; slides are handled by
`CommuteStep.step_comm_slide_raise` (through the certificate's endpoint
identity), so no `NoSlide γ` appears. -/
theorem raise_bubble :
    ∀ (γ : List Move) {Q v : State} {z : Card} {β : List Move},
      ShufflePlayW Q (γ ++ Move.tabToFound z :: β) v →
      RaiseSwaps Q z γ →
      ShufflePlayW Q (Move.tabToFound z :: γ ++ β) v := by
  intro γ
  induction γ with
  | nil =>
      intro Q v z β h _
      simpa using h
  | cons a as ih =>
      intro Q v z β h hsw
      -- the original play, split at the head letter
      obtain ⟨S1, hrev_a, hstep_a, hrest⟩ := Bubble.walk_cons_inv h
      -- the local certificate at the head
      obtain ⟨e, hswap, hrun⟩ := hsw [] Q a as rfl (Walk.nil Q)
      -- `[a, raise z]` from `Q` lands at `e`
      have hstep_r : State.step S1 (Move.tabToFound z) = some e := by
        obtain ⟨s1, hs1, hrest1⟩ := State.run_cons hrun
        have hs1' : s1 = S1 := Option.some.inj (hs1.symm.trans hstep_a)
        subst hs1'
        obtain ⟨s2, hs2, hrest2⟩ := State.run_cons hrest1
        have hs2' : s2 = e := by simpa [State.run] using hrest2
        subst hs2'
        exact hs2
      -- the induction hypothesis on the inner window
      have hsw' : RaiseSwaps S1 z as := by
        intro pre mid q rest hsplit hpre
        exact hsw (a :: pre) mid q rest
          (by rw [List.cons_append, hsplit])
          (Walk.cons hrev_a hstep_a hpre)
      have hIH : ShufflePlayW S1 (Move.tabToFound z :: as ++ β) v :=
        ih hrest hsw'
      -- the raised inner play starts at `e`
      obtain ⟨s0, hrev_r, hstep_r1, hrest2⟩ := Bubble.walk_cons_inv hIH
      have hs0 : s0 = e := Option.some.inj (hstep_r1.symm.trans hstep_r)
      subst hs0
      -- the swapped play `[raise z, a]` from `Q`
      obtain ⟨R, hrev_R, hstep_R, hrest3⟩ := Bubble.walk_cons_inv hswap
      obtain ⟨e2, hrev_a2, hstep_a2, hnil⟩ := Bubble.walk_cons_inv hrest3
      cases hnil
      exact Walk.cons hrev_R hstep_R (Walk.cons hrev_a2 hstep_a2 hrest2)

/-! ## §3. The commuted bracket play, with slides in the interior -/

/-- **THE COMMUTED BRACKET PLAY.**  From the play `ρ`, the bracket
decomposition, and the local swap certificate, produce the word
`raise z :: γ ++ β` as a witness play from the pull's landing `Q`.

This is exactly the missing `hcomm` of `Elim.bracket_delete_of_commuted`
(`Orig2/Fork/ForkElim.lean:106`) and of `Elim.turnCommutes_shortens`, produced from
*local* data instead of a global commutation premise — and with no `NoSlide`
restriction on `γ`. -/
theorem bracket_play_of_swaps
    {u v : State} {ρ α γ β : List Move} {z : Card} {bz : Base} {P Q : State}
    (hplay : ShufflePlayW u ρ v)
    (hρ : ρ = α ++ Move.foundToTab z bz :: γ ++ Move.tabToFound z :: β)
    (hα : ShufflePlayW u α P)
    (hstep : State.step P (Move.foundToTab z bz) = some Q)
    (hsw : RaiseSwaps Q z γ) :
    ShufflePlayW Q (Move.tabToFound z :: γ ++ β) v := by
  have hρ' : ρ = (α ++ [Move.foundToTab z bz]) ++
      (γ ++ Move.tabToFound z :: β) := by
    rw [hρ]; simp only [List.cons_append, List.append_assoc, List.nil_append]
  obtain ⟨Q', hplay1, hplay2⟩ := ShufflePlayW_split hplay _ _ hρ'
  obtain ⟨P1, hpre1, hlast1⟩ :=
    ShufflePlayW_split hplay1 α [Move.foundToTab z bz] rfl
  have hstep1 : State.step P1 (Move.foundToTab z bz) = some Q' :=
    Elim.step_of_singleton hlast1
  have hP : P1 = P := by
    have h1 := Walk_run (fun st m => reversibleAtW st m) hpre1
    have h2 := Walk_run (fun st m => reversibleAtW st m) hα
    exact Option.some.inj (h1.symm.trans h2)
  subst hP
  have hQ : Q' = Q := Option.some.inj (hstep1.symm.trans hstep)
  subst hQ
  exact raise_bubble γ hplay2 hsw

/-- **BRACKET DELETION, ARBITRARY INTERIOR.**  Same-card bracket deletion
with no slide restriction on the interior.  This is
`Elim.bubble_bracket_shortens` without `NoSlide γ`: the no-slide diamond it
used (`Bubble.swap_adjacent_noslide`) is replaced by the local certificate
`RaiseSwaps`, which the slide/raise square
(`CommuteStep.step_comm_slide_raise`) can supply for slides. -/
theorem bracket_delete_gen
    {u v : State} {ρ α γ β : List Move} {z : Card} {bz : Base} {P Q : State}
    (huwf : u.WF)
    (hplay : ShufflePlayW u ρ v)
    (hρ : ρ = α ++ Move.foundToTab z bz :: γ ++ Move.tabToFound z :: β)
    (hα : ShufflePlayW u α P)
    (hstep : State.step P (Move.foundToTab z bz) = some Q)
    (hsw : RaiseSwaps Q z γ) :
    ∃ ρ' : List Move, ShufflePlayW u ρ' v ∧ ρ'.length < ρ.length :=
  Elim.bracket_delete_of_commuted huwf hplay hρ hα hstep
    (bracket_play_of_swaps hplay hρ hα hstep hsw)

/-! ## §4. The local residual and the reduction -/

/-- **`NonforkBracketLocal` — WITHDRAWN, FALSE AS STATED.**  A four-letter
witness loop (`pull 5H -> 6C ; slide 4C -> 5H ; slide 4C -> 5D ; raise 5H`)
has a non-fork bottom whose only same-card bracket begins with a slide landing
on the bracket card (S2 fails); kernel-checked by
`ExistRefute.not_nonforkBracketLocal`.  The minimality-gated form is
`ExistKit.ReadBracketElimMin` / `ExistKit.ValleyForkAtMin`.  This definition is
kept only as the hypothesis of the reduction. -/
def NonforkBracketLocal : Prop :=
  ∀ (u v : State) (ρ : List Move) (F : State),
    u.WF → SSaturated u → SSaturated v →
    ShufflePlayW u ρ v →
    ValleySplitAt u v ρ F →
    (∃ x : Card, ForkWitness F x) ∨
    (∃ (α γ β : List Move) (z : Card) (bz : Base) (P Q : State),
      ρ = α ++ Move.foundToTab z bz :: γ ++ Move.tabToFound z :: β ∧
      ShufflePlayW u α P ∧
      State.step P (Move.foundToTab z bz) = some Q ∧
      RaiseSwaps Q z γ)

/-- **THE REDUCTION.**  `NonforkBracketLocal` implies the campaign's
`Elim.NonforkBracketElim`. -/
theorem nonforkBracketElim_of_local (h : NonforkBracketLocal) :
    Elim.NonforkBracketElim := by
  intro u v ρ F huwf hsu hsv hplay hsplit
  rcases h u v ρ F huwf hsu hsv hplay hsplit with
    hf | ⟨α, γ, β, z, bz, P, Q, hρ, hα, hstep, hsw⟩
  · exact Or.inl hf
  · exact Or.inr ⟨α, γ, β, z, bz, P, Q, hρ, hα, hstep,
      bracket_play_of_swaps hplay hρ hα hstep hsw⟩

/-- **THE LOCAL RESIDUAL IMPLIES THE VALLEY ELIMINATION.**  Composing with
`Elim.valleyElimNonfork_of_nonforkBracket`. -/
theorem valleyElimNonfork_of_local (h : NonforkBracketLocal) :
    ValleyElimNonfork :=
  Elim.valleyElimNonfork_of_nonforkBracket (nonforkBracketElim_of_local h)

/-! ## §5. An unconditional corner of the strong disjunct

The `post = []`, `c = d` corner already satisfies the STRONG (bracket)
disjunct, with the EMPTY interior — so it needs no `RaiseSwaps` content at
all, and contributes nothing to the residual. -/

/-- **THE EMPTY-TAIL SAME-CARD CORNER SATISFIES THE BRACKET DISJUNCT.** -/
theorem local_of_samecard_nil
    {u v F : State} {ρ left right pre post tail : List Move}
    {c d : Card} {b : Base}
    (hρ : ρ = left ++ right)
    (hleft : ShufflePlayW u left F)
    (hshape : left = pre ++ Move.foundToTab c b :: post)
    (hrightShape : right = Move.tabToFound d :: tail)
    (hpost : post = []) (hcd : c = d) :
    ∃ (α γ β : List Move) (z : Card) (bz : Base) (P Q : State),
      ρ = α ++ Move.foundToTab z bz :: γ ++ Move.tabToFound z :: β ∧
      ShufflePlayW u α P ∧
      State.step P (Move.foundToTab z bz) = some Q ∧
      RaiseSwaps Q z γ := by
  subst hpost
  subst hcd
  obtain ⟨P, hpre, hlast⟩ :=
    ShufflePlayW_split hleft pre [Move.foundToTab c b] hshape
  have hstep : State.step P (Move.foundToTab c b) = some F :=
    Elim.step_of_singleton hlast
  refine ⟨pre, [], tail, c, b, P, F, ?_, hpre, hstep, raiseSwaps_nil F c⟩
  rw [hρ, hshape, hrightShape]
/-! ## §6. A geometric case: the raise/raise square is a `RaiseSwaps` datum

The W1/W2 interiors (`Temp/SplitProbe_Report.md:270-308`) both begin with a
raise of a card in a DIFFERENT suit from the bracket card.  Here is the
kernel-checked geometric fact: two vanilla raises of different suits fire in
both orders, land together, and the SECOND is reversible after the first —
so the two-letter window is a `RaiseSwaps` datum.  This is the local
certificate at such a position, unconditionally. -/

/-- **TWO RAISES COMMUTE AS WITNESS PLAYS.**  At a `WF` state, two
vanilla-raisable cards of different suits fire in both orders, land on the
same state, and the swapped order is a *witness* play (the second raise is
reversible at its new origin). -/
theorem raise_swap_raise {S : State} {z w : Card}
    (hS : S.WF) (hz : CanRaise S z) (hw : CanRaise S w)
    (hsu : z.suit ≠ w.suit) :
    ∃ e, ShufflePlayW S [Move.tabToFound z, Move.tabToFound w] e ∧
         S.run [Move.tabToFound w, Move.tabToFound z] = some e := by
  have hz0 : CanRaise S z := hz
  have hw0 : CanRaise S w := hw
  obtain ⟨hnz, a, hpa, hseat_z⟩ := hz0
  obtain ⟨hnw, b, hpb, hseat_w⟩ := hw0
  have hzw : z ≠ w := fun h => hsu (by rw [h])
  have htopA : (S.piles a).top = some z := (pileOfTop_top hpa).2
  have htopB : (S.piles b).top = some w := (pileOfTop_top hpb).2
  have hab : a ≠ b := by
    intro hab
    rw [hab] at htopA
    exact hzw (Option.some.inj (htopA.symm.trans htopB))
  have hzst : State.step S (Move.tabToFound z) = some (raiseSt S z a) := by
    rw [step_tabToFound_splice hnz hpa]; rfl
  have hwst : State.step S (Move.tabToFound w) = some (raiseSt S w b) := by
    rw [step_tabToFound_splice hnw hpb]; rfl
  have hstep1 : State.step (raiseSt S z a) (Move.tabToFound w) =
      some (raiseSt (raiseSt S z a) w b) :=
    step_raiseSt_raise hS hsu hab hnw hpb
  have hstep2 : State.step (raiseSt S w b) (Move.tabToFound z) =
      some (raiseSt (raiseSt S w b) z a) :=
    step_raiseSt_raise hS (Ne.symm hsu) (Ne.symm hab) hnz hpa
  have hcomm : raiseSt (raiseSt S z a) w b = raiseSt (raiseSt S w b) z a :=
    raiseSt_commute hab hsu
  refine ⟨raiseSt (raiseSt S z a) w b, ?_, ?_⟩
  · refine Walk.cons (DrainClose.reversibleAtW_tabToFound_of_canRaise hS hz) hzst ?_
    have hS1wf : (raiseSt S z a).WF := step_wf hS hzst
    have hcanW : CanRaise (raiseSt S z a) w :=
      ⟨by rw [raiseSt_nextUp_ne hsu]; exact hnw,
       b, raiseSt_pileOfTop_ne hS hpb hab,
       by rw [raiseSt_piles_apply, ite_eq_right (Ne.symm hab)]; exact hseat_w⟩
    exact Walk.cons
      (DrainClose.reversibleAtW_tabToFound_of_canRaise hS1wf hcanW)
      hstep1 (Walk.nil _)
  · simp only [State.run, hwst, hstep2, hcomm]

/-- **A SINGLETON RAISE WINDOW IS A `RaiseSwaps` DATUM.**  If the interior is
one raise `raise w` in another suit and the original play runs
`raise w ; raise z`, the certificate holds. -/
theorem raiseSwaps_single_raise {Q F : State} {z w : Card}
    (hQ : Q.WF) (hz : CanRaise Q z) (hw : CanRaise Q w)
    (hsu : z.suit ≠ w.suit)
    (hplay : ShufflePlayW Q [Move.tabToFound w, Move.tabToFound z] F) :
    RaiseSwaps Q z [Move.tabToFound w] := by
  intro pre mid q rest hsplit hQQ
  -- the only possible split is the empty prefix
  cases pre with
  | cons a as => exact absurd hsplit (by simp)
  | nil =>
      simp only [List.nil_append] at hsplit
      injection hsplit with hq hrest
      subst hq
      subst hrest
      -- `mid = Q`
      have hmid : mid = Q := by
        have h := Walk_run (fun st m => reversibleAtW st m) hQQ
        exact Option.some.inj (h.symm.trans rfl)
      subst hmid
      obtain ⟨e, hswap, hrun⟩ := raise_swap_raise hQ hz hw hsu
      refine ⟨e, hswap, ?_⟩
      -- the original order's endpoint is `e`, by the witness play
      have hF : F = e := by
        have h1 := Walk_run (fun st m => reversibleAtW st m) hplay
        exact Option.some.inj (h1.symm.trans hrun)
      subst hF
      exact hrun

/-- **THE EMPTY-TAIL RAISE-TURN CORNER SATISFIES THE BRACKET DISJUNCT.**
`post = []`, `c ≠ d` and the turn followed at once by `raise c`: the
same-card bracket is the turn's own `pull c` closed by `raise c`, with
one-letter interior `[raise d]`.  The certificate is
`raiseSwaps_single_raise`: `raise d` and `raise c` commute because they are
two vanilla raises in *different* suits
(`BlockKit.suit_ne_of_canRaise_of_ne`). -/
theorem local_of_raiseTurn
    {u v F : State} {ρ left right pre post rest : List Move}
    {c d : Card} {b : Base}
    (huwf : u.WF)
    (hρ : ρ = left ++ right)
    (hleft : ShufflePlayW u left F)
    (hright : ShufflePlayW F right v)
    (hshape : left = pre ++ Move.foundToTab c b :: post)
    (hrightShape : right = Move.tabToFound d :: Move.tabToFound c :: rest)
    (hpost : post = []) (hcd : c ≠ d) :
    ∃ (α γ β : List Move) (z : Card) (bz : Base) (P Q : State),
      ρ = α ++ Move.foundToTab z bz :: γ ++ Move.tabToFound z :: β ∧
      ShufflePlayW u α P ∧
      State.step P (Move.foundToTab z bz) = some Q ∧
      RaiseSwaps Q z γ := by
  subst hpost
  obtain ⟨P, hpre, hlast⟩ :=
    ShufflePlayW_split hleft pre [Move.foundToTab c b] hshape
  have hstepP : State.step P (Move.foundToTab c b) = some F :=
    Elim.step_of_singleton hlast
  have hPwf : P.WF := by
    have h := hleft
    rw [hshape] at h
    exact SatDifferCensus.ShufflePlayW.wf_end hpre huwf
  have hFwf : F.WF := step_wf hPwf hstepP
  -- the two-letter head `raise d ; raise c` of the right leg
  have hright' : ShufflePlayW F (Move.tabToFound d :: Move.tabToFound c :: rest) v :=
    hrightShape ▸ hright
  obtain ⟨G, hrevD, hstepD, hright1⟩ := Bubble.walk_cons_inv hright'
  obtain ⟨H, hrevC, hstepC, _hrest2⟩ := Bubble.walk_cons_inv hright1
  have htwo : ShufflePlayW F [Move.tabToFound d, Move.tabToFound c] H :=
    Walk.cons hrevD hstepD (Walk.cons hrevC hstepC (Walk.nil H))
  -- both cards are vanilla-raisable at the bottom
  have hcanC : CanRaise F c := ValleyStep.pull_card_canRaise hPwf hstepP
  have hcanD : CanRaise F d := Bridge.canRaise_of_reversible_raise hFwf hrevD
  have hsu : c.suit ≠ d.suit :=
    BlockKit.suit_ne_of_canRaise_of_ne hcanC hcanD hcd
  have hsw : RaiseSwaps F c [Move.tabToFound d] :=
    raiseSwaps_single_raise hFwf hcanC hcanD hsu htwo
  refine ⟨pre, [Move.tabToFound d], rest, c, b, P, F, ?_, hpre, hstepP, hsw⟩
  rw [hρ, hshape, hrightShape]
  simp only [List.cons_append, List.append_assoc, List.nil_append]

end NonforkKit

#print axioms NonforkKit.raiseSwaps_nil
#print axioms NonforkKit.raise_bubble
#print axioms NonforkKit.bracket_play_of_swaps
#print axioms NonforkKit.bracket_delete_gen
#print axioms NonforkKit.nonforkBracketElim_of_local
#print axioms NonforkKit.valleyElimNonfork_of_local
#print axioms NonforkKit.local_of_samecard_nil
#print axioms NonforkKit.raise_swap_raise
#print axioms NonforkKit.raiseSwaps_single_raise
#print axioms NonforkKit.local_of_raiseTurn
