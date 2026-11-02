import Orig2.Fork.ForkReadBracket
import Orig2.Fork.ForkNonfork
import Orig2.Fork.ForkLanding
import Orig2.Fork.ForkLandingLocal
import Orig2.Fork.ForkSplitResidual

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

/-!
# Orig2/ForkThirdResidual — the third-suit exclusion from a read-safe bracket

READ-ONLY scratch (no source touched, no commit).  Zero `sorry`, zero
`Classical.choice`, zero `native_decide`; battery at the tail.

## What is proved here

1. `readOK_of_free` — the syntactic per-letter read-safety condition
   `R12.ReadOK z` is *automatic* for a free letter (`draw`, or a slide) that
   neither moves `z` nor lands on `z`.

2. `ThirdBracketRead` — **THE EXACT RESIDUAL**: every third-suit card `e`
   S-live at a split's pull landing carries an earlier same-card bracket
   `pull z ; γ ; raise z` in the split's play, whose interior `γ` is
   READ-SAFE for `z` (`∀ q ∈ γ, R12.ReadOK z q`).  This is purely syntactic:
   no commutation, no transport row, no `CanRaise` premise.

3. `landingThirdSuitFree_of_thirdBracketRead` — **THE REDUCTION**:
   `ThirdBracketRead → LandingThirdSuitFree`.  The bracket's raise bubbles
   left across the read-safe interior (`R12.raiseSwaps_of_read`, built from
   the certified per-letter swap squares) and W3 deletes the adjacent
   `pull z ; raise z` pair (`NonforkKit.bracket_delete_gen`), strictly
   shortening the play — contradicting the split's minimality.

4. `thirdBracketRead_iff_landingThirdSuitFree` — the residual is EXACT (the
   converse is vacuity: a violation contradicts the exclusion).

5. `landingLivePair_of_splitTwin_thirdBracketRead`,
   `splitLandingResidual_of_twin_thirdBracketRead`,
   `splitLivePair_of_twin_thirdBracketRead` — the composition with the
   twin clause (`LandKit.SplitLandingTwin`, owned by the parallel agent):
   the twin clause plus this card's residual give the whole `LandingAll`
   / `SplitLivePair` clause.

6. §4 the rank-dichotomy geometry of the brief's sub-case (b): two
   third-suit/opposite-colour cards of the SAME rank cannot both receive
   the same card (`tfc_fitting_parent`), cannot stack on each other, and are
   of opposite colour (`suit_eq_twin_of_color_eq`).
-/

namespace ThirdLive

open ValleyElim

/-! ## §1. Read-safety of free letters -/

/-- A draw is read-safe for every card. -/
theorem readOK_draw (z : Card) : R12.ReadOK z Move.draw := R12.readOK_draw z

/-- A slide is read-safe unless it moves `z` or lands on `z`. -/
theorem readOK_slide {z x : Card} {b : Base} (hx : x ≠ z) (hb : b ≠ Sum.inr z) :
    R12.ReadOK z (Move.tabToTab x b) := R12.readOK_slide_of_ne hx hb

/-- A pull is read-safe unless it is in `z`'s suit or lands on `z`. -/
theorem readOK_pull {z x : Card} {b : Base} (hx : x.suit ≠ z.suit)
    (hb : b ≠ Sum.inr z) : R12.ReadOK z (Move.foundToTab x b) :=
  R12.readOK_pull_of_ne hx hb

/-- **FREE LETTERS ARE READ-SAFE WHEN THEY AVOID `z`.**  A free letter
(`draw` or a slide) is read-safe for `z` provided no slide among its
realizations moves `z` or lands on `z`. -/
theorem readOK_of_free {z : Card} {q : Move} (hfree : FreeMove q)
    (hslide : ∀ (x : Card) (b : Base), q = Move.tabToTab x b →
      x ≠ z ∧ b ≠ Sum.inr z) :
    R12.ReadOK z q := by
  rcases hfree with rfl | ⟨x, b, rfl⟩
  · exact R12.readOK_draw z
  · exact R12.readOK_slide_of_ne (hslide x b rfl).1 (hslide x b rfl).2

/-! ## §2. The exact residual -/

/-- **`ThirdBracketRead` — THE READ-SAFE BRACKET RESIDUAL.**  Every
third-suit card `e` that is S-live at a split's pull landing `B` is the
pulled card `z` of an EARLIER pull in the split's play, whose matching raise
`raise z` occurs later, and whose interior `γ` is read-safe for `z`
(`R12.ReadOK z`, a purely syntactic per-letter condition).

No commutation row, no transport row and no `CanRaise` premise occurs: the
raise's own swap certificate is *built* from the read-safety inside the
reduction, and the pull card's raisability at its landing is the certified
`ValleyStep.pull_card_canRaise`. -/
def ThirdBracketRead : Prop :=
  ∀ (u v : State) (ρ : List Move) (F : State)
    (left right : List Move) (c d : Card) (b : Base)
    (pre post tail : List Move),
    SplitKit.SplitHyp u v ρ F left right c d b pre post tail →
    ∀ (A' B : State), ShufflePlayW u pre A' →
      State.step A' (Move.foundToTab c b) = some B →
      ∀ e : Card, CanRaiseS B e → e.suit ≠ c.suit → e.suit ≠ c.twin.suit →
      ∃ (α γ β : List Move) (z : Card) (bz : Base) (P Q : State),
        ρ = α ++ Move.foundToTab z bz :: γ ++ Move.tabToFound z :: β ∧
        ShufflePlayW u α P ∧
        State.step P (Move.foundToTab z bz) = some Q ∧
        (∀ q ∈ γ, R12.ReadOK z q)

/-- **THE REDUCTION.**  The read-safe bracket residual implies the third-suit
exclusion at every split.  The bracket's raise bubbles left over the
read-safe interior (the per-letter certificate `R12.raiseSwaps_of_read` is
built from the certified swap squares of `Orig2/Fork/ForkReadBracket.lean`), and
the adjacent `pull ; raise` pair is deleted by W3
(`NonforkKit.bracket_delete_gen`), which strictly shortens the split's
minimal play. -/
theorem landingThirdSuitFree_of_thirdBracketRead (hb : ThirdBracketRead) :
    Landing.LandingThirdSuitFree := by
  intro u v ρ F left right c d b pre post tail hs A' B hpre hstep e he h1 h2
  have hk := hs
  obtain ⟨huwf, hsu, hsv, hplay, hvs, hmin, hρeq, hleft, hright, hshape,
    hfree, hrt⟩ := hs
  obtain ⟨α, γ, β, z, bz, P, Q, hρ, hα, hstepP, hread⟩ :=
    hb u v ρ F left right c d b pre post tail hk A' B hpre hstep e he h1 h2
  have hPwf : P.WF := SatDifferCensus.ShufflePlayW.wf_end hα huwf
  have hQwf : Q.WF := step_wf hPwf hstepP
  have hcanQ : CanRaise Q z := ValleyStep.pull_card_canRaise hPwf hstepP
  have hplayQ : ShufflePlayW Q (γ ++ Move.tabToFound z :: β) v :=
    R12.bracket_landing_play hplay hρ hα hstepP
  have hsw : NonforkKit.RaiseSwaps Q z γ :=
    R12.raiseSwaps_of_read hQwf hplayQ hcanQ hread
  obtain ⟨ρ', hρ'play, hlen⟩ :=
    NonforkKit.bracket_delete_gen huwf hplay hρ hα hstepP hsw
  exact absurd hlen (Nat.not_lt.mpr (hmin ρ' hρ'play))

/-- The residual is not a strengthening: the third-suit exclusion makes its
hypothesis set contradictory, so it supplies the bracket vacuously. -/
theorem thirdBracketRead_of_landingThirdSuitFree
    (hf : Landing.LandingThirdSuitFree) : ThirdBracketRead := by
  intro u v ρ F left right c d b pre post tail hs A' B hpre hstep e he h1 h2
  exact (hf u v ρ F left right c d b pre post tail hs A' B hpre hstep e he h1 h2).elim

/-- **THE RESIDUAL IS EXACT.** -/
theorem thirdBracketRead_iff_landingThirdSuitFree :
    ThirdBracketRead ↔ Landing.LandingThirdSuitFree :=
  ⟨landingThirdSuitFree_of_thirdBracketRead,
    thirdBracketRead_of_landingThirdSuitFree⟩

/-! ## §3. Composition with the twin clause and with `SplitLivePair` -/

/-- **THE LANDING LIVE PAIR AT ONE SPLIT** from the twin clause and this
card's residual: the third-suit exclusion is supplied by
`landingThirdSuitFree_of_thirdBracketRead`, and `LandKit.landingLivePair_of_local`
assembles the pair. -/
theorem landingLivePair_of_splitTwin_thirdBracketRead
    (htwin : LandKit.SplitLandingTwin) (hb : ThirdBracketRead)
    {u v : State} {ρ : List Move} {F : State} {left right : List Move}
    {c d : Card} {b : Base} {pre post tail : List Move}
    (hs : SplitKit.SplitHyp u v ρ F left right c d b pre post tail)
    {A' B : State} (hpre : ShufflePlayW u pre A')
    (hstep : State.step A' (Move.foundToTab c b) = some B) :
    Mech.LandingLivePair B c := by
  have hA' : A'.WF := SatDifferCensus.ShufflePlayW.wf_end hpre hs.1
  refine LandKit.landingLivePair_of_local hA' hstep
    (htwin u v ρ F left right c d b pre post tail hs A' B hpre hstep) ?_
  intro e heA heB
  by_cases h1 : e.suit = c.suit
  · exact Or.inl h1
  · by_cases h2 : e.suit = c.twin.suit
    · exact Or.inr h2
    · exact (landingThirdSuitFree_of_thirdBracketRead hb
        u v ρ F left right c d b pre post tail hs A' B hpre hstep e heB h1 h2).elim

/-- **THE SPLIT-LEVEL LANDING RESIDUAL** from the twin clause and the
read-safe bracket residual.  Clause 2 is exactly `LandKit.LandingThirdFreeAt`. -/
theorem splitLandingResidual_of_twin_thirdBracketRead
    (htwin : LandKit.SplitLandingTwin) (hb : ThirdBracketRead) :
    LandKit.SplitLandingResidual := by
  intro u v ρ F left right c d b pre post tail hs A' B hpre hstep
  refine ⟨htwin u v ρ F left right c d b pre post tail hs A' B hpre hstep, ?_⟩
  intro e heA heB
  by_cases h1 : e.suit = c.suit
  · exact Or.inl h1
  · by_cases h2 : e.suit = c.twin.suit
    · exact Or.inr h2
    · exact (landingThirdSuitFree_of_thirdBracketRead hb
        u v ρ F left right c d b pre post tail hs A' B hpre hstep e heB h1 h2).elim

/-- **THE WHOLE LANDING CLAUSE** from the twin clause and the residual. -/
theorem landingAll_of_twin_thirdBracketRead
    (htwin : Landing.LandingTwinLive) (hb : ThirdBracketRead) :
    Landing.LandingAll :=
  Landing.landingAll_iff_parts.mpr
    ⟨htwin, landingThirdSuitFree_of_thirdBracketRead hb⟩

/-- **`SplitLivePair`** from the twin clause and the residual. -/
theorem splitLivePair_of_twin_thirdBracketRead
    (htwin : Landing.LandingTwinLive) (hb : ThirdBracketRead) :
    SplitKit.SplitLivePair :=
  Landing.landingAll_iff_splitLivePair.mp (landingAll_of_twin_thirdBracketRead htwin hb)

/-! ## §4. Sub-case (b): the rank mate's geometry -/

/-- Two different suits of the same colour are twins. -/
theorem suit_eq_twin_of_color_eq {s t : Suit} (h : s.color = t.color) (hne : s ≠ t) :
    s = t.twin := by
  cases s <;> cases t <;> simp_all [Suit.color, Suit.twin]

/-- **SAME RANK, THIRD SUIT ⟹ OPPOSITE COLOUR.**  A third-suit card `e`
whose rank equals `c`'s rank has the *opposite* colour to `c`: the same
colour at the same rank would make it `c` or `c.twin`. -/
theorem color_ne_of_rank_eq_third {e c : Card} (hr : e.rank = c.rank)
    (hs1 : e.suit ≠ c.suit) (hs2 : e.suit ≠ c.twin.suit) :
    e.suit.color ≠ c.suit.color := by
  intro hcol
  have htw : e.suit = c.suit.twin := suit_eq_twin_of_color_eq hcol hs1
  exact hs2 (by rw [htw]; exact (Card.twin_suit c).symm)

/-- Same-rank cards never stack on each other: `canSitOn` needs a strict rank
drop. -/
theorem not_canSitOn_same_rank {e c : Card} (hr : e.rank = c.rank) :
    canSitOn e c = false := by
  cases h : canSitOn e c with
  | false => rfl
  | true =>
      obtain ⟨h1, -⟩ := (canSitOn_eq e c).mp h
      rw [hr] at h1
      omega

/-- **A CARD CANNOT SIT ON BOTH `c` AND A THIRD-SUIT RANK MATE.**  The fit
rule (`tfc_fitting_parent`) makes the two parents twins, which the third-suit
hypotheses forbid. -/
theorem not_seat_both_of_third {e c x : Card}
    (hs1 : e.suit ≠ c.suit) (hs2 : e.suit ≠ c.twin.suit) :
    ¬ (canSitOn x c = true ∧ canSitOn x e = true) := by
  rintro ⟨hxc, hxe⟩
  rcases tfc_fitting_parent hxc hxe with h | h
  · exact hs1 (by rw [h])
  · have hcs : c.suit = e.suit.twin := by rw [h, Card.twin_suit]
    have hct : c.twin.suit = c.suit.twin := Card.twin_suit c
    exact hs2 (by rw [hct, hcs, Suit.twin_twin])

/-! ## §5. The bracket card of a violation is itself a third-suit card -/

/-- The twin is injective on suits. -/
theorem twin_inj {s t : Suit} (h : s.twin = t.twin) : s = t := by
  rw [← Suit.twin_twin s, h, Suit.twin_twin]

/-- **THE EARLIER PULL CARD IS A THIRD-SUIT CARD.**  If the violation `e` is
an earlier pull card or its twin (`LandKit.landing_third_suit_earlier_pull`),
then that pull card is in a third suit too, and has `e`'s rank.  So the
residual's bracket never involves `c`'s pair and always involves `e`'s rank
class. -/
theorem bracket_card_third {e z c : Card} (hmem : e = z ∨ e = z.twin)
    (hs1 : e.suit ≠ c.suit) (hs2 : e.suit ≠ c.twin.suit) :
    (z.suit ≠ c.suit ∧ z.suit ≠ c.twin.suit) ∧ z.rank = e.rank := by
  have hrank : z.rank = e.rank := by
    rcases hmem with h | h
    · rw [h]
    · rw [h, Card.twin_rank]
  refine ⟨⟨?_, ?_⟩, hrank⟩
  · rcases hmem with h | h
    · intro hc
      exact hs1 (by rw [h]; exact hc)
    · intro hc
      have hz : z = e.twin := by rw [h, card_twin_twin]
      have h1 : e.suit.twin = c.suit := by
        rw [← Card.twin_suit e, ← hz]
        exact hc
      have h2 : e.suit = c.suit.twin := by
        rw [← Suit.twin_twin e.suit, h1]
      exact hs2 (by rw [h2, ← Card.twin_suit c])
  · rcases hmem with h | h
    · intro hc
      exact hs2 (by rw [h]; exact hc)
    · intro hc
      have hz : z = e.twin := by rw [h, card_twin_twin]
      have h1 : e.suit.twin = c.twin.suit := by
        rw [← Card.twin_suit e, ← hz]
        exact hc
      have h2 : e.suit.twin = c.suit.twin := by
        rw [h1, Card.twin_suit c]
      exact hs1 (twin_inj h2)

end ThirdLive

#print axioms ThirdLive.readOK_draw
#print axioms ThirdLive.readOK_slide
#print axioms ThirdLive.readOK_pull
#print axioms ThirdLive.readOK_of_free
#print axioms ThirdLive.ThirdBracketRead
#print axioms ThirdLive.landingThirdSuitFree_of_thirdBracketRead
#print axioms ThirdLive.thirdBracketRead_of_landingThirdSuitFree
#print axioms ThirdLive.thirdBracketRead_iff_landingThirdSuitFree
#print axioms ThirdLive.landingLivePair_of_splitTwin_thirdBracketRead
#print axioms ThirdLive.splitLandingResidual_of_twin_thirdBracketRead
#print axioms ThirdLive.landingAll_of_twin_thirdBracketRead
#print axioms ThirdLive.splitLivePair_of_twin_thirdBracketRead
#print axioms ThirdLive.suit_eq_twin_of_color_eq
#print axioms ThirdLive.color_ne_of_rank_eq_third
#print axioms ThirdLive.not_canSitOn_same_rank
#print axioms ThirdLive.not_seat_both_of_third
#print axioms ThirdLive.twin_inj
#print axioms ThirdLive.bracket_card_third
