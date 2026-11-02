import Orig2.ForkEqSplitSlide
import Orig2.ForkLandResSeat
import Orig2.ForkChoiceFree

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-!
# Orig2/ForkBaseSeat — the lander's seat: the exact non-`SeatSafe` letter

READ-ONLY scratch.  No source edit, no commit.  No `sorry`, no
`Classical.choice`, no `native_decide`; battery at the tail.

The brief's claim is that in the equal-rung right leg every letter between a
window cover of `c` and the cover's removal is `SeatSafe` for the **lander**.
That is not true as stated (a later letter may land on the lander, raising the
stack above it), and this file proves the correct statement:

```text
x tops pile `k` before q  ∧  x tops pile `k` after q
  ⇒  q neither names x, nor lands on x, nor slides a run out of `k` (`SeatInert`).
```

So the *only* letter of a corridor that is not seat-safe for the lander is the
letter that **moves** the lander — i.e. the removal itself
(`seatInert_of_preserved`).  `corridor_inert` then says every letter before the
first seat change is seat-inert.

This is the frame half of the cover/uncover deletion: seat-inertness is exactly
what lets the interior be replayed around the lander.
-/

namespace BaseSeat

open CommuteStep

/-- **`SeatInert st x k q`** — the letter `q` does not read the lander's seat:
it neither names `x`, nor lands on `x`, nor slides a run out of the pile `k`
that `x` tops.  (The last clause is `LandResSeat.SeatSafe`'s `hsource`
obligation, in the form needed for the frame.) -/
def SeatInert (st : State) (x : Card) (k : Anchor) (q : Move) : Prop :=
  LandResSeat.SeatSafe x q ∧
    (∀ (y : Card) (b : Base), q = Move.tabToTab y b →
      st.pileHolding y ≠ some k)

theorem seatInert_draw (st : State) (x : Card) (k : Anchor) :
    SeatInert st x k Move.draw := by
  refine ⟨trivial, ?_⟩
  intro y b h
  cases h

theorem seatInert_raise {st : State} {x w : Card} {k : Anchor} (h : w ≠ x) :
    SeatInert st x k (Move.tabToFound w) := by
  refine ⟨h, ?_⟩
  intro y b hq
  cases hq

theorem seatInert_pull {st : State} {x y : Card} {k : Anchor} {b : Base}
    (hy : y ≠ x) (hb : b ≠ Sum.inr x) :
    SeatInert st x k (Move.foundToTab y b) := by
  refine ⟨⟨hy, hb⟩, ?_⟩
  intro y' b' hq
  cases hq

theorem seatInert_slide {st : State} {x y : Card} {k : Anchor} {b : Base}
    (hy : y ≠ x) (hb : b ≠ Sum.inr x) (hsrc : st.pileHolding y ≠ some k) :
    SeatInert st x k (Move.tabToTab y b) := by
  refine ⟨⟨hy, hb⟩, ?_⟩
  intro y' b' hq
  cases hq
  exact hsrc

/-- The seat-inert letter leaves the pile top search of the lander alone. -/
theorem pileOfTop_of_seatInert {st s' : State} {x : Card} {k : Anchor} {q : Move}
    (hwf : st.WF) (hrev : reversibleAtW st q) (hstep : State.step st q = some s')
    (htop : st.pileOfTop x = some k) (hin : SeatInert st x k q) :
    s'.pileOfTop x = some k :=
  LandResSeat.pileOfTop_of_seatSafe hwf hrev hstep htop hin.1 hin.2

/-- **THE ONLY NON-SEAT-SAFE LETTER IS THE REMOVAL.**  If the lander still tops
the same pile after `q`, then `q` does not read its seat: it does not name `x`,
does not land on `x`, and does not slide a run out of `x`'s pile.

Equivalently: a letter is NOT `SeatInert` only if it moves `x` — raises it,
slides it, buries it, or drags its pile out from under it. -/
theorem seatInert_of_preserved {st s' : State} {x : Card} {k : Anchor} {q : Move}
    (hwf : st.WF) (hrev : reversibleAtW st q) (hstep : State.step st q = some s')
    (htop : st.pileOfTop x = some k) (hpres : s'.pileOfTop x = some k) :
    SeatInert st x k q := by
  have hswf : s'.WF := step_wf hwf hstep
  have hne : s'.pileOfTop x ≠ none := by rw [hpres]; simp
  cases q with
  | draw => exact seatInert_draw st x k
  | wasteToFound c =>
      exact absurd hrev (wasteToFound_not_reversibleAtW st c)
  | wasteToTab c b =>
      exact absurd hrev (wasteToTab_not_reversibleAtW st c b)
  | tabToFound w =>
      refine seatInert_raise ?_
      intro hwx
      rw [← hwx] at htop hpres hne
      obtain ⟨-, a, hpa, hs⟩ := step_tabToFound_inv hstep
      obtain ⟨hfound, -, -⟩ := tabToFound_found_trio (st := st) (c := w) (a := a) hs
      have hmem : w ∈ s'.found w.suit := by
        rw [hfound]
        exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
      exact hne (SlideCore.pileOfTop_none_of_found hswf hmem)
  | foundToTab y b =>
      refine seatInert_pull ?_ ?_
      · intro hyx
        rw [← hyx] at htop hpres
        obtain ⟨c', htop', hc', hcp, hs⟩ := step_foundToTab_pullSt hstep
        rw [hc'] at htop'
        have hmem : y ∈ st.found y.suit := lastOf_mem htop'
        have hnone := SlideCore.pileOfTop_none_of_found hwf hmem
        rw [htop] at hnone
        exact absurd hnone (by simp)
      · intro hb
        exact hne (ChoiceFree.pileOfTop_none_of_landing hwf hrev hstep (d := x) hb)
  | tabToTab y b =>
      obtain ⟨a1, hhold1, hcp1, hrunv1, hs1⟩ := step_tabToTab_slideSt hstep
      obtain ⟨a0, k0, hhold0, hcp0, hk0, hka0, hface0, hrunv0, hcell0⟩ :=
        slide_data hwf hrev
      have hxk : st.pileHolding x = some k := Drain.pileHolding_of_pileOfTop hwf htop
      -- if the mover starts in `x`'s pile then `x` moves with the run
      have hkey : st.pileHolding y = some k → False := by
        intro hsrc
        have ha0k : a0 = k := Option.some.inj (hhold0.symm.trans hsrc)
        have ha1k : a1 = k := Option.some.inj (hhold1.symm.trans hsrc)
        rw [ha0k] at hka0 hrunv0 hcell0
        rw [ha1k] at hs1
        have hres := slideSt_pileOfTop_source hwf hcp0 hk0 hka0 hrunv0 hcell0
          (z := x) (a := k) htop
        rw [hs1] at hpres
        rw [hres] at hpres
        exact hka0 (Option.some.inj hpres)
      refine seatInert_slide ?_ ?_ ?_
      · rintro rfl
        exact hkey hxk
      · rintro rfl
        exact hne (ChoiceFree.pileOfTop_none_of_landing hwf hrev hstep (d := x) rfl)
      · exact hkey

/-- **`SeatInertPlay x k st l`** — every letter of the play from `st` leaves the
lander's seat (`x` on pile `k`) alone. -/
def SeatInertPlay (x : Card) (k : Anchor) : State → List Move → Prop
  | _, [] => True
  | st, q :: t =>
      SeatInert st x k q ∧ ∀ s', State.step st q = some s' → SeatInertPlay x k s' t

/-- A seat-inert play keeps the lander on its pile. -/
theorem pileOfTop_of_seatInertPlay {st s : State} {l : List Move} {x : Card} {k : Anchor}
    (hcert : SeatInertPlay x k st l) (hplay : ShufflePlayW st l s) (hwf : st.WF)
    (htop : st.pileOfTop x = some k) : s.pileOfTop x = some k := by
  induction l generalizing st with
  | nil =>
      cases hplay
      exact htop
  | cons q t ih =>
      obtain ⟨st1, hrev, hstep, hrest⟩ := Bubble.walk_cons_inv hplay
      obtain ⟨h1, h2⟩ := hcert
      exact ih (h2 st1 hstep) hrest (step_wf hwf hstep)
        (pileOfTop_of_seatInert hwf hrev hstep htop h1)

/-- **THE CORRIDOR.**  A play that starts with the lander on pile `k` and ends
with the lander off it splits as

```text
l = α ++ r :: β,     α seat-inert,     r the (first) removal,
```

with `x` still on `k` at `r`'s source and off `k` at its target.  So the whole
interior between a cover and its removal is seat-inert, and the *only* letter
that is not `SeatSafe` for the lander is `r` itself. -/
theorem corridor_inert {P W : State} {l : List Move} {x : Card} {k : Anchor}
    (hplay : ShufflePlayW P l W) (hP : P.WF) (htop : P.pileOfTop x = some k)
    (hW : W.pileOfTop x ≠ some k) :
    ∃ (α : List Move) (r : Move) (β : List Move) (A B : State),
      l = α ++ r :: β ∧ ShufflePlayW P α A ∧ State.step A r = some B ∧
      SeatInertPlay x k P α ∧ A.pileOfTop x = some k ∧ B.pileOfTop x ≠ some k := by
  induction l generalizing P with
  | nil =>
      cases hplay
      exact absurd htop hW
  | cons m t ih =>
      obtain ⟨P1, hrev, hstep, hrest⟩ := Bubble.walk_cons_inv hplay
      have hP1wf : P1.WF := step_wf hP hstep
      by_cases hpres : P1.pileOfTop x = some k
      · obtain ⟨α, r, β, A, B, hl, hα, hstepA, hcert, hAtop, hBtop⟩ :=
          ih hrest hP1wf hpres
        refine ⟨m :: α, r, β, A, B, ?_, ?_, hstepA, ?_, hAtop, hBtop⟩
        · rw [hl]
          rfl
        · exact Walk.cons hrev hstep hα
        · refine ⟨seatInert_of_preserved hP hrev hstep htop hpres, ?_⟩
          intro s' hs'
          have hs'P1 : s' = P1 := Option.some.inj (hs'.symm.trans hstep)
          rw [hs'P1]
          exact hcert
      · exact ⟨[], m, t, P, P1, rfl, Walk.nil P, hstep, trivial, htop, hpres⟩

/-- **THE CORRIDOR DICHOTOMY.**  A play from a state where the lander tops pile
`k` either contains a first letter that moves the lander's seat (and everything
before it is seat-inert), or it is seat-inert throughout. -/
theorem corridor_split_or_inert {P W : State} {l : List Move} {x : Card} {k : Anchor}
    (hplay : ShufflePlayW P l W) (hP : P.WF) (htop : P.pileOfTop x = some k) :
    (∃ (α : List Move) (r : Move) (β : List Move) (A B : State),
      l = α ++ r :: β ∧ ShufflePlayW P α A ∧ State.step A r = some B ∧
      SeatInertPlay x k P α ∧ A.pileOfTop x = some k ∧ B.pileOfTop x ≠ some k)
    ∨ SeatInertPlay x k P l := by
  induction l generalizing P with
  | nil => exact Or.inr trivial
  | cons m t ih =>
      obtain ⟨P1, hrev, hstep, hrest⟩ := Bubble.walk_cons_inv hplay
      have hP1wf : P1.WF := step_wf hP hstep
      by_cases hpres : P1.pileOfTop x = some k
      · rcases ih hrest hP1wf hpres with
          ⟨α, r, β, A, B, hl, hα, hstepA, hcert, hAtop, hBtop⟩ | hall
        · refine Or.inl ⟨m :: α, r, β, A, B, by rw [hl]; rfl, Walk.cons hrev hstep hα,
            hstepA, ⟨seatInert_of_preserved hP hrev hstep htop hpres, ?_⟩, hAtop, hBtop⟩
          intro s' hs'
          have hs'P1 : s' = P1 := Option.some.inj (hs'.symm.trans hstep)
          rw [hs'P1]
          exact hcert
        · refine Or.inr ⟨seatInert_of_preserved hP hrev hstep htop hpres, ?_⟩
          intro s' hs'
          have hs'P1 : s' = P1 := Option.some.inj (hs'.symm.trans hstep)
          rw [hs'P1]
          exact hall
      · exact Or.inl ⟨[], m, t, P, P1, rfl, Walk.nil P, hstep, trivial, htop, hpres⟩

/-- **A SEAT-INERT PLAY CANNOT END WITH THE LANDER OFF ITS PILE.** -/
theorem not_off_of_seatInertPlay {P W : State} {l : List Move} {x : Card} {k : Anchor}
    (hcert : SeatInertPlay x k P l) (hplay : ShufflePlayW P l W) (hP : P.WF)
    (htop : P.pileOfTop x = some k) : W.pileOfTop x = some k :=
  pileOfTop_of_seatInertPlay hcert hplay hP htop

end BaseSeat

#print axioms BaseSeat.pileOfTop_of_seatInert
#print axioms BaseSeat.seatInert_of_preserved
#print axioms BaseSeat.pileOfTop_of_seatInertPlay
#print axioms BaseSeat.corridor_inert
#print axioms BaseSeat.corridor_split_or_inert
