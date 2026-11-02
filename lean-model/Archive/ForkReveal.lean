import Orig2.ForkOffWindow

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-!
# Orig2/ForkReveal — the REVEAL face of the prepared-seat window is a COMMIT

READ-ONLY scratch.  No source edit, no commit.  Zero `sorry`, zero
`Classical.choice`, zero `native_decide`, zero `decide` over `State`; axiom
battery at the tail.

## The target

`OffWindow.RevealResidual B a p z` (`Orig2/ForkOffWindow.lean:435`) is the one
face of the prepared-seat window that is **not** a twin exchange:

```text
below p (B.piles a).faceUp = []      -- p is the BOTTOM of its whole face-up run
(B.piles a).hidden = z :: rest       -- z is the hidden card directly under it
```

Sliding the run headed by `p` off the pile empties the run, so the automatic
reveal (`Pile.afterRunRemoved p [] = Pile.revealTop {p with faceUp := []}`)
flips `z` onto the face-up run.  The pull `d (inr z)` may then land on `z`.

## What this card proves (no residual)

1. **§1 the reveal mechanic, definitionally.**  `afterRunRemoved_reveal`:
   a run removal over an empty prefix of a pile whose hidden deck is `z :: rest`
   produces `⟨rest, [z]⟩` — exactly one hidden card flips, and it is the head.

2. **§2 the reveal is IRREVERSIBLE, and no move — let alone the reverse slide —
   re-hides `z`.**  The hidden total drops by at least one
   (`reveal_slide_hidden_drop`) and no legal step ever raises it
   (`hiddenTotal_step`), so *no* legal move takes the successor back to the
   origin (`reveal_no_reverse_move`) and the slide is not
   `reversibleAtW` (`reveal_slide_not_reversibleAtW`).  The `WF` bridge
   (`reveal_slide_not_reversibleAtW_of_wf`) reads the holding search off the
   `RevealResidual` face itself (`below = []` pins `p` as the run head).
   The consumer form `reversible_slide_below_ne_nil_of_hidden`: a reversible
   slide over a nonempty hidden deck **must** have company beneath its mover —
   so its run cannot empty, and no flip fires.

3. **§3 the commit oracle agrees.**  `tabToTabR` is `false` on the reveal face
   (§3a), and the classification's `tabToTabR_iff_reversibleAtW` re-derives the
   same impossibility (§3b) — two independent routes.

4. **§4 `RevealResidual` is a LETTER-grade void, not a state-grade one.**
   `reveal_not_witness_letter`: no `ShufflePlayW` play carries a reveal slide
   at a `RevealResidual` origin, in any decomposition.  `revealResidual_demo`
   exhibits a state satisfying the predicate — and `revealResidual_of_singleton`
   shows every pile with a one-card face-up run over a nonempty hidden deck
   qualifies (the ordinary deal shape), so the unqualified
   `¬ RevealResidual` is **false** and must not be attempted.

5. **§5 corridor form.**  In the prepared-seat corridor
   `pre ; raise c ; [slide] ; pull ; tail` of a witness play, the single-slide
   window that reveals `z` from the hidden deck does not exist
   (`corridor_reveal_window_impossible`).  So in a witness prepared-seat window
   `z` must have been face-up at the raise's image; it was covered there
   (`pileOfTop_none_of_window_not_pullable`), so the window is the cover case —
   the twin exchange of `slide_expose_card_twin`.  The reveal face is closed.

6. **§6 the two faces are disjoint at `WF`.**  A `TwinExchangeWindow` at the
   same state would put `z` face-up in pile `a`, while `RevealResidual` puts it
   in the hidden deck; conservation (`mem_faceUp_not_hidden`) forbids both
   (`reveal_not_twin_window`).  So the reveal face is genuinely outside the
   twin lane, and its closure is not a re-derivation of `slide_expose_card_twin`.

7. **§7 non-implication.**  Two gadget states with the same hidden head `z`
   (hence the same `d`-side rank datum) and movers of different ranks, both
   satisfying `RevealResidual`, neither mover `d.twin` (`demo_twin_not_forced`).
   The reveal data carries **no** rank/colour relation between the mover and
   `z`; `twin_of_two_fits`'s missing premise `p.rank + 1 = z.rank` cannot be
   recovered.  The gadgets are not `WF` — the claim is the non-implication,
   which is exactly why the twin lane cannot absorb this face.

## Saturation

None is needed: the reveal dies at the **letter** grade, before the pull, the
tail, or `SSaturated` can matter.  The face cannot be a `ShufflePlayW` play at
all.
-/

namespace Rev

open OffWindow

/-! ## §1. The reveal mechanic, definitionally -/

/-- **THE FLIP.**  A run removal over the empty prefix of a pile whose hidden
deck is `z :: rest` hands back the pile with exactly one card flipped: the head
`z` face-up, the remainder `rest` still hidden.  (`hidden` keeps the
next-to-flip card at its head, `Orig/State.lean:255`.) -/
theorem afterRunRemoved_reveal {z : Card} {rest fu : List Card} :
    Pile.afterRunRemoved (⟨z :: rest, fu⟩ : Pile) [] = ⟨rest, [z]⟩ := rfl

/-- **THE FLIP, IN THE STEP'S OWN TERMS.**  If the mover heads the face-up run
(`faceUp = p :: t`, so `below p faceUp = []`) and the hidden deck is `z :: rest`,
the source edit is the reveal of `z`, whatever the run above `p` looks like. -/
theorem afterRunRemoved_below_head {p z : Card} {rest t : List Card} :
    Pile.afterRunRemoved (⟨z :: rest, p :: t⟩ : Pile) (below p (p :: t)) =
      ⟨rest, [z]⟩ := by
  rw [below_cons_self]
  rfl

/-! ## §2. The reveal slide is a strict commit -/

/-- **`below = []` PINS THE RUN HEAD.**  A nonempty face-up run with nothing
below `c` starts **at** `c`. -/
theorem eq_head_of_below_nil {c x : Card} {t : List Card}
    (h : below c (x :: t) = []) : x = c := by
  rw [below_cons] at h
  by_cases hxc : x = c
  · exact hxc
  · rw [ite_eq_right hxc] at h
    exact absurd h (by simp)

/-- **`below = []` GIVES MEMBERSHIP.**  In particular the `RevealResidual`
face makes its mover a face-up card of the named pile. -/
theorem mem_of_below_nil {c : Card} {l : List Card}
    (h : below c l = []) (hne : l ≠ []) : c ∈ l := by
  cases l with
  | nil => exact absurd rfl hne
  | cons x t =>
      have hxc : x = c := eq_head_of_below_nil h
      rw [hxc]
      exact List.mem_cons_self ..

/-- **THE REVEAL SLIDE DROPS THE HIDDEN TOTAL.**  `hiddenTotal` is the flat
length of the seven hidden decks (`Orig2/Kit.lean:138`); the reveal converts one
hidden card to face-up and nothing else grows. -/
theorem reveal_slide_hidden_drop
    {st s' : State} {a : Anchor} {p z : Card} {b : Base}
    (hhold : st.pileHolding p = some a)
    (hrr : RevealResidual st a p z)
    (hstep : State.step st (Move.tabToTab p b) = some s') :
    hiddenTotal s' < hiddenTotal st := by
  obtain ⟨-, hbelow, rest, hhid⟩ := hrr
  have hne : (st.piles a).hidden ≠ [] := by rw [hhid]; simp
  have h := hiddenTotal_step_tabToTab_reveal hstep hhold hbelow hne
  omega

/-- **NO MOVE UNDOES A REVEAL.**  The flipped card cannot be re-hidden by the
reverse slide: *no* legal single move returns the reveal's successor to the
origin, because `hiddenTotal` never rises. -/
theorem reveal_no_reverse_move
    {st s' : State} {a : Anchor} {p z : Card} {b : Base}
    (hhold : st.pileHolding p = some a)
    (hrr : RevealResidual st a p z)
    (hstep : State.step st (Move.tabToTab p b) = some s') :
    ∀ m : Move, State.step s' m ≠ some st := by
  have hdrop := reveal_slide_hidden_drop hhold hrr hstep
  intro m hm
  have hle := hiddenTotal_step hm
  omega

/-- **THE REVEAL SLIDE IS NOT REVERSIBLE** (holding grade — no `WF` needed).
A reveal can therefore never be a `ShufflePlayW` letter, whose letter predicate
is exactly `reversibleAtW`. -/
theorem reveal_slide_not_reversibleAtW
    {st : State} {a : Anchor} {p z : Card} {b : Base}
    (hhold : st.pileHolding p = some a)
    (hrr : RevealResidual st a p z) :
    ¬ reversibleAtW st (Move.tabToTab p b) := by
  rintro ⟨s', play, hstep, hrun⟩
  exact not_W_of_desc hiddenTotal
    (fun s m s' hs => hiddenTotal_step hs) hstep
    (reveal_slide_hidden_drop hhold hrr hstep) ⟨s', play, hstep, hrun⟩

/-- **THE REVEAL FACE IS EMPTY AT `WF`.**  The residual itself supplies the
holding datum: `below = []` over a nonempty run makes `p` the run's head, and
`pileHolding_eq_some_iff` locates it. -/
theorem reveal_slide_not_reversibleAtW_of_wf
    {st s' : State} {a : Anchor} {p z : Card} {b : Base}
    (hwf : st.WF) (hrr : RevealResidual st a p z)
    (hstep : State.step st (Move.tabToTab p b) = some s') :
    ¬ reversibleAtW st (Move.tabToTab p b) := by
  have hmem : p ∈ (st.piles a).faceUp := mem_of_below_nil hrr.2.1 hrr.1
  have hhold : st.pileHolding p = some a := (pileHolding_eq_some_iff hwf).2 hmem
  exact reveal_slide_not_reversibleAtW hhold hrr

/-- **THE REVEAL-FREE FORM: a reversible slide over a nonempty hidden deck has
company beneath its mover.**  No `z` witness and no `WF` are needed — this is
the row the cover lane consumes to rule out the reveal face of a window.  It is
the exact contrapositive of the reveal commit: `below p faceUp ≠ []` says `p` is
*not* the bottom of its run, so sliding the run off cannot empty the pile and no
flip fires. -/
theorem reversible_slide_below_ne_nil_of_hidden
    {st : State} {p : Card} {b : Base} {a : Anchor}
    (hhold : st.pileHolding p = some a)
    (hrev : reversibleAtW st (Move.tabToTab p b))
    (hhid : (st.piles a).hidden ≠ []) :
    below p (st.piles a).faceUp ≠ [] := by
  intro hbelow
  have hface : (st.piles a).faceUp ≠ [] := by
    intro hnil
    have hmem := pileHolding_mem hhold
    rw [hnil] at hmem
    exact List.not_mem_nil hmem
  obtain ⟨z, rest, hz⟩ := list_cons_of_ne_nil hhid
  exact reveal_slide_not_reversibleAtW hhold ⟨hface, hbelow, ⟨rest, hz⟩⟩ hrev

/-- **EVEN A WHOLE PLAY CANNOT RETURN.**  The `mono_run` form: no legal play
from the reveal's successor ends at the origin.  (The `not_W_of_desc` above is
the one-move-witness corollary this packages.) -/
theorem reveal_no_returning_play
    {st s' : State} {a : Anchor} {p z : Card} {b : Base}
    (hhold : st.pileHolding p = some a)
    (hrr : RevealResidual st a p z)
    (hstep : State.step st (Move.tabToTab p b) = some s') :
    ¬ ∃ play, s'.run play = some st := by
  rintro ⟨play, hrun⟩
  have hle := mono_run hiddenTotal (fun s m s' hs => hiddenTotal_step hs) hrun
  have hdrop := reveal_slide_hidden_drop hhold hrr hstep
  omega

/-! ## §3. The commit oracle agrees -/

/-- **THE COMMIT SHAPE READS `false`.**  `tabToTabR` (`Orig2/Vocab.lean:174`)
is the reveal-vs-company discriminator: `below = []` plus a nonempty hidden deck
is the commit arm. -/
theorem reveal_tabToTabR_eq_false
    {st : State} {a : Anchor} {p z : Card}
    (b : Base)
    (hhold : st.pileHolding p = some a)
    (hrr : RevealResidual st a p z) :
    tabToTabR st p b = false := by
  obtain ⟨-, hbelow, rest, hhid⟩ := hrr
  cases hcp : st.canPlace p b with
  | false => simp [tabToTabR, hhold, hcp]
  | true => simp [tabToTabR, hhold, hcp, hbelow, hhid]

/-- **SECOND ROUTE.**  The classification's WF bridge
(`Orig2/Classification.lean:2350`) re-derives the impossibility from the shape
row above. -/
theorem reveal_slide_not_reversibleAtW_via_classification
    {st : State} {a : Anchor} {p z : Card} {b : Base}
    (hwf : st.WF) (hhold : st.pileHolding p = some a)
    (hrr : RevealResidual st a p z) :
    ¬ reversibleAtW st (Move.tabToTab p b) := by
  have hfalse := reveal_tabToTabR_eq_false b hhold hrr
  intro hrev
  have htrue := (tabToTabR_iff_reversibleAtW hwf p b).mpr hrev
  rw [hfalse] at htrue
  exact Bool.noConfusion htrue

/-! ## §4. The reveal is a letter-grade void -/

/-- **NO WITNESS PLAY CARRIES A REVEAL SLIDE.**  At any decomposition of a
`ShufflePlayW` play, the letter `tabToTab p b` cannot fire at an origin carrying
`RevealResidual` for its own mover.  This is the precise sense in which the
reveal face of the prepared-seat window is EMPTY. -/
theorem reveal_not_witness_letter
    {u v : State} {τ pre rest : List Move} {p z : Card} {a : Anchor} {b : Base}
    (huwf : u.WF) (hplay : ShufflePlayW u τ v)
    (hdec : τ = pre ++ Move.tabToTab p b :: rest)
    (A C : State) (hpre : ShufflePlayW u pre A)
    (hstep : State.step A (Move.tabToTab p b) = some C)
    (hrr : RevealResidual A a p z) : False := by
  obtain ⟨A', hA1, hA2⟩ :=
    ValleyElim.ShufflePlayW_split hplay pre (Move.tabToTab p b :: rest) hdec
  have hAeq : A' = A := walk_end_unique hA1 hpre
  rw [hAeq] at hA2
  obtain ⟨-, hrev, -, -⟩ := Bubble.walk_cons_inv hA2
  have hAwf : A.WF := SatDifferCensus.ShufflePlayW.wf_end hpre huwf
  exact reveal_slide_not_reversibleAtW_of_wf hAwf hrr hstep hrev

/-- The head-letter specialization: a witness play cannot **start** with a
reveal slide. -/
theorem reveal_not_witness_head
    {u v : State} {rest : List Move} {p z : Card} {a : Anchor} {b : Base}
    (huwf : u.WF) (hplay : ShufflePlayW u (Move.tabToTab p b :: rest) v)
    (hhold : u.pileHolding p = some a) (hrr : RevealResidual u a p z) : False := by
  obtain ⟨C, hrev, hstep, -⟩ := Bubble.walk_cons_inv hplay
  exact reveal_slide_not_reversibleAtW hhold hrr hrev

/-! ## §5. The corridor form — the prepared-seat reveal window does not exist -/

/-- **THE PREPARED-SEAT REVEAL WINDOW IS IMPOSSIBLE.**  In the corridor
`pre ; raise c ; γ ; pull d b ; tail` of a witness play, if the window `γ` is
the single slide `tabToTab p bb` and its origin carries `RevealResidual` (so the
window exposes `z` from the hidden deck), there is no play.  Hence the reveal
face is closed at the corridor grade. -/
theorem corridor_reveal_window_impossible
    {u v : State} {ρ pre γ tail : List Move} {c d : Card} {b : Base} {A B : State}
    {p z : Card} {a : Anchor} {bb : Base}
    (huwf : u.WF)
    (hplay : ShufflePlayW u ρ v)
    (heq : ρ = pre ++ (Move.tabToFound c :: (γ ++ (Move.foundToTab d b :: tail))))
    (hpre : ShufflePlayW u pre A)
    (hstepR : State.step A (Move.tabToFound c) = some B)
    (hγ : γ = [Move.tabToTab p bb])
    (hrr : RevealResidual B a p z) : False := by
  have hdecomp : ρ = (pre ++ [Move.tabToFound c]) ++
      (γ ++ (Move.foundToTab d b :: tail)) := by
    rw [heq]
    simp [List.append_assoc]
  obtain ⟨B', hleft, hright⟩ :=
    ValleyElim.ShufflePlayW_split hplay _ _ hdecomp
  obtain ⟨M, hupre, hraise⟩ := Bubble.walk_split pre hleft
  have hMA : M = A := walk_end_unique hupre hpre
  obtain ⟨s1, -, hstep1, hnil⟩ := Bubble.walk_cons_inv hraise
  cases hnil
  have hB'B : B' = B := by
    rw [hMA] at hstep1
    exact Option.some.inj (hstep1.symm.trans hstepR)
  rw [hB'B] at hright
  obtain ⟨C, hγwalk, hrest⟩ := Bubble.walk_split γ hright
  rw [hγ] at hγwalk
  obtain ⟨s2, hrevS, hstepS, -⟩ := Bubble.walk_cons_inv hγwalk
  have hBwf : B.WF := step_wf (SatDifferCensus.ShufflePlayW.wf_end hpre huwf) hstepR
  exact reveal_slide_not_reversibleAtW_of_wf hBwf hrr hstepS hrevS

/-! ## §6. The reveal face is disjoint from the twin exchange, at `WF` -/

/-- **THE TWO FACES ARE DISTINCT.**  `TwinExchangeWindow` puts `z` in pile
`a`'s face-up run; `RevealResidual` puts it in pile `a`'s hidden deck.
Conservation forbids the same card in both (`mem_faceUp_not_hidden`). -/
theorem reveal_not_twin_window
    {B C Pv : State} {a : Anchor} {front rest : List Card} {p z d : Card}
    (h : TwinExchangeWindow B C Pv a front rest p z d)
    (hrr : RevealResidual B a p z) : False := by
  have hzface : z ∈ (B.piles a).faceUp := by
    rw [h.face]
    simp
  obtain ⟨-, -, rest', hhid⟩ := hrr
  have hzhid : z ∈ (B.piles a).hidden := by
    rw [hhid]
    exact List.mem_cons_self ..
  exact mem_faceUp_not_hidden h.wf hzface hzhid

/-! ## §7. `RevealResidual` is inhabited — the honest boundary

The predicate is a *state* predicate: nothing in it involves reversibility.
A pile with a one-card face-up run over a nonempty hidden deck satisfies it —
exactly the shape every deal gives its non-first columns — so
`¬ RevealResidual` is unprovable, and the void lives precisely at the letter
grade (`RevealResidual → ¬ reversibleAtW`).  The gadgets below carry the other
boundary datum: with the hidden head fixed, the mover's rank is unconstrained
and need not be `d.twin`, so the twin identity is not a consequence of the
reveal data. -/

/-- **THE RESIDUAL IS THE ORDINARY SINGLETON SHAPE.**  Any pile whose face-up
run is a singleton and whose hidden deck is nonempty is a reveal residual — at
*any* state.  In particular every pile of a standard deal but the first column
has this shape (`Pile.ofDealt`, `Orig/State.lean:292`: `faceUp` is the last
dealt card, `hidden` the rest), so the predicate is inhabited at `WF` worlds and
`¬ RevealResidual` is flatly false. -/
theorem revealResidual_of_singleton {B : State} {a : Anchor} {p z : Card}
    {rest : List Card}
    (hhid : (B.piles a).hidden = z :: rest) (hfu : (B.piles a).faceUp = [p]) :
    RevealResidual B a p z :=
  ⟨by rw [hfu]; simp,
   by rw [hfu, below_cons_self],
   ⟨rest, hhid⟩⟩

/-- The mover: the sole face-up card of pile `p0`. -/
def demoP : Card := ⟨Suit.diamond, Rank.five⟩
/-- The hidden card revealed by the slide. -/
def demoZ : Card := ⟨Suit.spade, Rank.five⟩
/-- The slide's landing base card (`demoP` fits it: 5 red on 6 black). -/
def demoW : Card := ⟨Suit.spade, Rank.six⟩
/-- The pull's card (`demoZ`'s twin rank/colour complement: 4 red on 5 black). -/
def demoD : Card := ⟨Suit.heart, Rank.four⟩

/-- The demonstrated state: pile `p0` is `demoP` over the hidden `demoZ`,
pile `p1` tops `demoW`, the heart foundation tops `demoD`, everything else bare. -/
def demoState : State :=
  { found := fun s => if s = Suit.heart then [demoD] else []
    piles := fun a =>
      if a = Anchor.p0 then ⟨[demoZ], [demoP]⟩
      else if a = Anchor.p1 then ⟨[], [demoW]⟩
      else ⟨[], []⟩
    stock := []
    waste := []
    drawStep := 1 }

/-- A second mover over the **same** hidden `z`, at a different rank: the
reveal data fixes nothing about the mover. -/
def demoP₂ : Card := ⟨Suit.club, Rank.nine⟩

/-- The same gadget with the other mover. -/
def demoState₂ : State :=
  { demoState with
    piles := fun a =>
      if a = Anchor.p0 then ⟨[demoZ], [demoP₂]⟩
      else if a = Anchor.p1 then ⟨[], [demoW]⟩
      else ⟨[], []⟩ }

/-- **THE STATE PREDICATE IS INHABITED.**  `¬ RevealResidual` is FALSE: pile
`p0` is the single face-up `demoP` over the hidden `demoZ`, so `below` is empty
and the hidden head is `z`. -/
theorem revealResidual_demo : RevealResidual demoState Anchor.p0 demoP demoZ := by
  refine ⟨?_, ?_, ?_⟩
  · show (demoState.piles Anchor.p0).faceUp ≠ []
    simp [demoState]
  · show below demoP (demoState.piles Anchor.p0).faceUp = []
    simp [demoState, below_cons]
  · refine ⟨[], ?_⟩
    show (demoState.piles Anchor.p0).hidden = demoZ :: []
    simp [demoState]

/-- **THE REVEAL MECHANIC FIRES AT THE DEMO STATE.**  The slide of the sole
face-up card reveals `demoZ` and leaves it as the pile's only face-up card. -/
theorem demo_afterRunRemoved :
    Pile.afterRunRemoved (demoState.piles Anchor.p0)
        (below demoP (demoState.piles Anchor.p0).faceUp) =
      (⟨[], [demoZ]⟩ : Pile) := by
  have hpile : demoState.piles Anchor.p0 = (⟨[demoZ], [demoP]⟩ : Pile) := by
    simp [demoState]
  rw [hpile, below_cons_self]
  rfl

/-- The second gadget is a residual too: same `z`, same `d`-side foundation,
different mover. -/
theorem revealResidual_demo₂ : RevealResidual demoState₂ Anchor.p0 demoP₂ demoZ := by
  refine ⟨?_, ?_, ?_⟩
  · show (demoState₂.piles Anchor.p0).faceUp ≠ []
    simp [demoState₂, demoState]
  · show below demoP₂ (demoState₂.piles Anchor.p0).faceUp = []
    simp [demoState₂, demoState, below_cons]
  · refine ⟨[], ?_⟩
    show (demoState₂.piles Anchor.p0).hidden = demoZ :: []
    simp [demoState₂, demoState]

/-- **THE TWIN IDENTITY IS NOT RECOVERABLE FROM THE REVEAL DATA.**  Two states
with the same hidden head `z` (hence the same pull side: `d.rank + 1 = z.rank`
is the only rank datum in play) and movers of *different ranks*; both satisfy
`RevealResidual`, and neither mover is `d.twin`.  `twin_of_two_fits` needs the
mover's *fit on `z`*; the reveal face never supplies it.  (The states are not
`WF`; the claim is the non-implication, not a `WF` counterexample.) -/
theorem demo_twin_not_forced :
    demoP ≠ demoD.twin ∧ demoP₂ ≠ demoD.twin ∧
      demoP₂.rank.toIdx ≠ demoP.rank.toIdx := by
  refine ⟨?_, ?_, ?_⟩
  · unfold demoP demoD Card.twin
    simp
  · unfold demoP₂ demoD Card.twin
    simp
  · unfold demoP₂ demoP
    decide

end Rev

#print axioms Rev.afterRunRemoved_reveal
#print axioms Rev.afterRunRemoved_below_head
#print axioms Rev.eq_head_of_below_nil
#print axioms Rev.mem_of_below_nil
#print axioms Rev.reveal_slide_hidden_drop
#print axioms Rev.reveal_no_reverse_move
#print axioms Rev.reveal_slide_not_reversibleAtW
#print axioms Rev.reveal_slide_not_reversibleAtW_of_wf
#print axioms Rev.reversible_slide_below_ne_nil_of_hidden
#print axioms Rev.reveal_no_returning_play
#print axioms Rev.reveal_tabToTabR_eq_false
#print axioms Rev.reveal_slide_not_reversibleAtW_via_classification
#print axioms Rev.reveal_not_witness_letter
#print axioms Rev.reveal_not_witness_head
#print axioms Rev.corridor_reveal_window_impossible
#print axioms Rev.reveal_not_twin_window
#print axioms Rev.revealResidual_of_singleton
#print axioms Rev.revealResidual_demo
#print axioms Rev.demo_afterRunRemoved
#print axioms Rev.revealResidual_demo₂
#print axioms Rev.demo_twin_not_forced
