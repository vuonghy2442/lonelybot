import Orig2.ForkEqSplitSlide
import Orig2.ForkLandResSeat
import Orig2.ForkChoiceFree
import Orig2.ForkBaseSeat
import Orig2.ForkBasePile

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-!
# Orig2/ForkBaseMain — the exact non-`SeatSafe` letter, and the residual

READ-ONLY scratch.  No source edit, no commit.  No `sorry`, no
`Classical.choice`, no `native_decide`; battery at the tail.

## Content

* **§1 `Names`** — the letters that move a named card.

* **§2 `not_seatInert_cases`** — the exact statement the brief asks for.  A
  letter of the corridor is NOT seat-inert for the lander `x` (occupying pile
  `k`) iff it is one of

  ```text
  (i)   a letter naming `x`           (raise / pull / slide of `x`),
  (ii)  a letter landing on `x`       (a slide or pull onto `inr x`),
  (iii) a slide headed by a card of `k` (dragging `x` with the run).
  ```

  So: *every* letter of the corridor strictly before the removal is seat-safe
  for the lander **and** leaves its pile untouched — the only non-seat-safe
  letter is the removal itself, and it is one of the three shapes above.  (The
  brief's "every letter is `SeatSafe`" is false for (ii): a letter landing on
  the lander is invisible to `SeatSafe`'s slide clause but moves its seat.)

* **§3 `corridor_pile_frozen`** — the cover pile is literally unchanged from
  the cover state to the removal: the interior is invisible to it.

* **§4 the residual**, named precisely: the gate `AvoidsPlay` (the interior does
  not read the pile the lander will land on) and the gated replay
  `CorridorReplay`.  Neither is a restatement of the base clause: both are
  statements about a *corridor*, i.e. about the letters between a cover and its
  removal.  The gate is **not** free — `Temp/Base_probe.py` exhibits corridors
  whose interior reads the lander's landing pile (`Base_Report.md` §5).
-/

namespace BaseMain

open CommuteStep
open ValleyElim

/-! ## §1. The letters that move a card -/

/-- `Names x q`: the letter moves the card `x` itself. -/
def Names (x : Card) : Move → Prop
  | Move.tabToFound w => w = x
  | Move.foundToTab y _ => y = x
  | Move.tabToTab y _ => y = x
  | _ => False

/-- `Drags k q`: the letter slides a run out of the pile `k`. -/
def Drags (k : Anchor) (st : State) : Move → Prop
  | Move.tabToTab y _ => st.pileHolding y = some k
  | _ => False

/-! ## §1b. The residual's vocabulary -/

/-- **`Avoids1 J st q`** — the letter reads neither the pile `J` nor any pile
under it: no source from `J` and no landing on `J`. -/
def Avoids1 (J : Anchor) (st : State) : Move → Prop
  | Move.draw => True
  | Move.wasteToFound _ => False
  | Move.wasteToTab _ _ => False
  | Move.tabToFound w => st.pileOfTop w ≠ some J
  | Move.foundToTab _ b => CommuteStep.tgt st b ≠ some J
  | Move.tabToTab y b => st.pileHolding y ≠ some J ∧ CommuteStep.tgt st b ≠ some J

/-- **`AvoidsPlay J st l`** — every letter of the play (at the state where it
fires) avoids the pile `J`. -/
def AvoidsPlay (J : Anchor) : State → List Move → Prop
  | _, [] => True
  | st, q :: t => Avoids1 J st q ∧ ∀ s', State.step st q = some s' → AvoidsPlay J s' t

/-- **`CorridorReplay` — THE EXACT RESIDUAL.**  A cover/uncover corridor
`slide x (inr c) ; μ ; slide x b''` whose interior `μ` is seat-inert for the
lander `x` and avoids the pile `k''` the lander lands on is strictly shortened
by the direct slide.  The two gates are real: the probe shows the avoidance can
fail, and `Base_Adjoint.adjacent_cover_uncover_shortens` proves the `μ = []`
instance under the net-zero's own data. -/
def CorridorReplay : Prop :=
  ∀ (A A1 A2 A3 : State) (x c : Card) (a k k'' : Anchor) (b'' : Base) (μ : List Move),
    A.WF →
    State.step A (Move.tabToTab x (Sum.inr c)) = some A1 →
    A1 = CommuteStep.slideSt A x (Sum.inr c) a →
    ShufflePlayW A1 μ A2 →
    BaseSeat.SeatInertPlay x k A1 μ →
    A1.pileOfTop x = some k →
    A2.pileOfTop x = some k →
    AvoidsPlay k'' A1 μ →
    State.step A2 (Move.tabToTab x b'') = some A3 →
    CommuteStep.tgt A2 b'' = some k'' →
    ∃ ρ' : List Move, ShufflePlayW A ρ' A3 ∧
      ρ'.length < (Move.tabToTab x (Sum.inr c) :: μ ++ [Move.tabToTab x b'']).length

/-! ## §2. The exact classification -/

/-- **THE EXACT NON-SEAT-INERT LETTER.**  A legal letter that is not seat-inert
for the lander names it, lands on it, or drags its pile. -/
theorem not_seatInert_cases {st : State} {x : Card} {k : Anchor} {q : Move}
    (hrev : reversibleAtW st q) (h : ¬ BaseSeat.SeatInert st x k q) :
    Names x q ∨ ChoiceFree.LandsOn x q ∨ Drags k st q := by
  cases q with
  | draw => exact absurd (BaseSeat.seatInert_draw st x k) h
  | wasteToFound c => exact absurd hrev (wasteToFound_not_reversibleAtW st c)
  | wasteToTab c b => exact absurd hrev (wasteToTab_not_reversibleAtW st c b)
  | tabToFound w =>
      by_cases hw : w = x
      · exact Or.inl hw
      · exact absurd (BaseSeat.seatInert_raise hw) h
  | foundToTab y b =>
      by_cases hy : y = x
      · exact Or.inl hy
      · by_cases hb : b = Sum.inr x
        · exact Or.inr (Or.inl hb)
        · exact absurd (BaseSeat.seatInert_pull hy hb) h
  | tabToTab y b =>
      by_cases hy : y = x
      · exact Or.inl hy
      · by_cases hb : b = Sum.inr x
        · exact Or.inr (Or.inl hb)
        · right; right
          show st.pileHolding y = some k
          by_cases hsrc : st.pileHolding y = some k
          · exact hsrc
          · exact absurd ⟨⟨hy, hb⟩, (by
              intro y' b' hq
              injection hq with hy' hb'
              subst hy'; subst hb'
              exact hsrc)⟩ h

/-- A letter naming the lander is not seat-inert. -/
theorem not_seatInert_of_names {st : State} {x : Card} {k : Anchor} {q : Move}
    (h : Names x q) : ¬ BaseSeat.SeatInert st x k q := by
  intro hin
  cases q with
  | draw => exact h
  | wasteToFound c => exact h
  | wasteToTab c b => exact h
  | tabToFound w => exact hin.1 h
  | foundToTab y b => exact hin.1.1 h
  | tabToTab y b => exact hin.1.1 h

/-- A letter landing on the lander is not seat-inert. -/
theorem not_seatInert_of_landsOn {st : State} {x : Card} {k : Anchor} {q : Move}
    (h : ChoiceFree.LandsOn x q) : ¬ BaseSeat.SeatInert st x k q := by
  intro hin
  cases q with
  | draw => exact h
  | wasteToFound c => exact h
  | wasteToTab c b => exact h
  | tabToFound w => exact h
  | foundToTab y b => exact hin.1.2 h
  | tabToTab y b => exact hin.1.2 h

/-- A letter dragging the lander's pile is not seat-inert. -/
theorem not_seatInert_of_drags {st : State} {x : Card} {k : Anchor} {q : Move}
    (h : Drags k st q) : ¬ BaseSeat.SeatInert st x k q := by
  intro hin
  cases q with
  | draw => exact h
  | wasteToFound c => exact h
  | wasteToTab c b => exact h
  | tabToFound w => exact h
  | foundToTab y b => exact h
  | tabToTab y b => exact hin.2 y b rfl h

/-- **THE CLASSIFICATION, AS AN IFF.** -/
theorem not_seatInert_iff {st : State} {x : Card} {k : Anchor} {q : Move}
    (hrev : reversibleAtW st q) :
    ¬ BaseSeat.SeatInert st x k q ↔
      Names x q ∨ ChoiceFree.LandsOn x q ∨ Drags k st q :=
  ⟨not_seatInert_cases hrev,
   fun h hin => h.elim (fun hn => not_seatInert_of_names hn hin)
     (fun hl => hl.elim (fun hlo => not_seatInert_of_landsOn hlo hin)
       (fun hd => not_seatInert_of_drags hd hin))⟩

/-! ## §3. The corridor: the cover pile is frozen, and the removal is classified -/

/-- **THE CORRIDOR, WITH THE PILE FROZEN.**  `corridor_inert` plus
`pile_untouched_of_seatInertPlay`: the interior before the removal leaves the
lander's pile *literally* unchanged. -/
theorem corridor_pile_frozen {P W : State} {l : List Move} {x : Card} {k : Anchor}
    (hplay : ShufflePlayW P l W) (hP : P.WF) (htop : P.pileOfTop x = some k)
    (hW : W.pileOfTop x ≠ some k) :
    ∃ (α : List Move) (r : Move) (β : List Move) (A B : State),
      l = α ++ r :: β ∧ ShufflePlayW P α A ∧ State.step A r = some B ∧
      BaseSeat.SeatInertPlay x k P α ∧ A.pileOfTop x = some k ∧
      B.pileOfTop x ≠ some k ∧ A.piles k = P.piles k := by
  obtain ⟨α, r, β, A, B, hl, hα, hstepA, hcert, hAtop, hBtop⟩ :=
    BaseSeat.corridor_inert hplay hP htop hW
  exact ⟨α, r, β, A, B, hl, hα, hstepA, hcert, hAtop, hBtop,
    BasePile.pile_untouched_of_seatInertPlay hcert hα hP htop⟩

/-- **THE REMOVAL IS NOT SEAT-INERT.**  At the removal's source the lander still
tops its pile, and after the removal it does not; so the removal is one of the
three shapes of §2. -/
theorem removal_classified {P W : State} {l : List Move} {x : Card} {k : Anchor}
    (hplay : ShufflePlayW P l W) (hP : P.WF) (htop : P.pileOfTop x = some k)
    (hW : W.pileOfTop x ≠ some k) :
    ∃ (r : Move) (A : State),
      Names x r ∨ ChoiceFree.LandsOn x r ∨ Drags k A r := by
  obtain ⟨α, r, β, A, B, hl, hα, hstepA, hcert, hAtop, hBtop⟩ :=
    BaseSeat.corridor_inert hplay hP htop hW
  -- reversibility of `r` at `A`: read it off the walk
  have hrevA : reversibleAtW A r := by
    obtain ⟨mid, hmid, hrest⟩ := ShufflePlayW_split hplay α (r :: β) hl
    obtain ⟨A'', hrev, hstep, -⟩ := Bubble.walk_cons_inv hrest
    have h1 : State.run P α = some A := Walk_run _ hα
    have h2 : State.run P α = some mid := Walk_run _ hmid
    rw [h1] at h2
    have hAeq : mid = A := (Option.some.inj h2).symm
    rw [hAeq] at hrev
    exact hrev
  have hAwf : A.WF := SatDifferCensus.ShufflePlayW.wf_end hα hP
  have hnot : ¬ BaseSeat.SeatInert A x k r := by
    intro hin
    exact hBtop (BaseSeat.pileOfTop_of_seatInert hAwf hrevA hstepA hAtop hin)
  exact ⟨r, A, not_seatInert_cases hrevA hnot⟩

end BaseMain

#print axioms BaseMain.not_seatInert_cases
#print axioms BaseMain.not_seatInert_iff
#print axioms BaseMain.corridor_pile_frozen
#print axioms BaseMain.removal_classified