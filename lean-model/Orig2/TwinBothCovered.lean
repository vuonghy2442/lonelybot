import Orig2.TwinSpliceUnique
import Orig2.TwinSplicePlay
import Orig2.TwinEquivariance
import Orig2.TwinParentShift
import Orig2.TwinSuffixExchange
import Orig2.TwinSwapRecipe
import Orig2.Classification

set_option linter.unusedSectionVars false

/-!
# Orig2.TwinBothCovered — the minimal 5L both-covered point swap

The concrete normal-form case the recipe grammar does not recognise:
both twins `x, x.twin` sit on `.inr` parents and each carries a rider,
so neither is a pile top and the 3-leg foundation recipe cannot fire at
the source.

This card ports the minimal 5L route (world B, pair `Q♠ | Q♣`):

```
raise J♥          -- clear the rider on Q♠
raise Q♠          -- now the 3-leg recipe can start
slide Q♣ -> K♦    -- Q♣'s run moves onto Q♠'s vacated parent
pull  Q♠ -> K♥    -- Q♠ onto Q♣'s vacated parent
re-seat J♥ on Q♠  -- the cleared rider follows its host
```

The endpoint is the *strict* twin swap `spliceTwinRuns Q♠ uB`, so the
route witnesses `SwappableIn uB Q♠` at the concrete state.  The last
two sections record the frozen edit-level template and the precise
parent-shift relation (E-face, not S-face) that motivates the 5L block.
-/

namespace TwinBothCovered

open State

/-! ## §1. The concrete world B state and the route's five intermediates -/

private def kS : Card := ⟨Suit.spade, Rank.king⟩
private def kH : Card := ⟨Suit.heart, Rank.king⟩
private def kD : Card := ⟨Suit.diamond, Rank.king⟩
private def kC : Card := ⟨Suit.club, Rank.king⟩
private def cQS : Card := ⟨Suit.spade, Rank.queen⟩
private def cQC : Card := ⟨Suit.club, Rank.queen⟩
private def cQH : Card := ⟨Suit.heart, Rank.queen⟩
private def cQD : Card := ⟨Suit.diamond, Rank.queen⟩
private def cJH : Card := ⟨Suit.heart, Rank.jack⟩
private def cJD : Card := ⟨Suit.diamond, Rank.jack⟩

private def foundsB : Suit → List Card := fun s =>
  match s with
  | .spade => (Suit.upCards Suit.spade).take 11
  | .heart => (Suit.upCards Suit.heart).take 10
  | .diamond => (Suit.upCards Suit.diamond).take 10
  | .club => (Suit.upCards Suit.club).take 11

private def uBp : Anchor → Pile := fun a =>
  match a with
  | .p0 => ⟨[], [kD, cQS, cJH]⟩
  | .p1 => ⟨[], [kH, cQC, cJD]⟩
  | .p2 => ⟨[], [kC, cQH]⟩
  | .p3 => ⟨[], [kS, cQD]⟩
  | .p4 => ⟨[], []⟩
  | .p5 => ⟨[], []⟩
  | .p6 => ⟨[], []⟩

private def uB : State :=
  { found := foundsB, piles := uBp, stock := [], waste := [], drawStep := 1 }

private def v1 : State :=
  { uB.setFound Suit.heart (uB.found Suit.heart ++ [cJH]) with
    piles := fun a' =>
      if a' = Anchor.p0 then
        Pile.afterRunRemoved (uB.piles Anchor.p0) (chop (uB.piles Anchor.p0).faceUp)
      else uB.piles a' }

private def v2 : State :=
  { v1.setFound Suit.spade (v1.found Suit.spade ++ [cQS]) with
    piles := fun a' =>
      if a' = Anchor.p0 then
        Pile.afterRunRemoved (v1.piles Anchor.p0) (chop (v1.piles Anchor.p0).faceUp)
      else v1.piles a' }

private def v3 : State :=
  (v2.setPile Anchor.p1 (Pile.afterRunRemoved (v2.piles Anchor.p1)
    (below cQC (v2.piles Anchor.p1).faceUp))).putRun
    (fromCard cQC (v2.piles Anchor.p1).faceUp) (Sum.inr kD)

private def v4 : State :=
  (v3.setFound Suit.spade (chop (v3.found Suit.spade))).putCard cQS (Sum.inr kH)

private def v5 : State :=
  (v4.setFound Suit.heart (chop (v4.found Suit.heart))).putCard cJH (Sum.inr cQS)

/-! ## §2. The step legs -/

private theorem stepV1 : State.step uB (Move.tabToFound cJH) = some v1 :=
  step_tabToFound_splice (by decide) (by decide)

private theorem stepV2 : State.step v1 (Move.tabToFound cQS) = some v2 :=
  step_tabToFound_splice (by decide) (by decide)

private theorem stepV3 : State.step v2 (Move.tabToTab cQC (Sum.inr kD)) = some v3 := by
  rw [step_tabToTab_eq]
  have hhold : v2.pileHolding cQC = some Anchor.p1 := by decide
  have hcp : v2.canPlace cQC (Sum.inr kD) = true := by decide
  have hfrom : fromCard cQC (v2.piles Anchor.p1).faceUp = [cQC, cJD] := by decide
  rw [hhold]
  simp only [hcp, ite_true]
  rw [hfrom]
  rfl

private theorem stepV4 : State.step v3 (Move.foundToTab cQS (Sum.inr kH)) = some v4 :=
  step_foundToTab_splice (by decide) (by decide)

private theorem stepV5 : State.step v4 (Move.foundToTab cJH (Sum.inr cQS)) = some v5 :=
  step_foundToTab_splice (by decide) (by decide)

/-! ## §3. WF of the five states -/

private def allTrue (l : List Card) (p : Card → Bool) : Bool :=
  match l with
  | [] => true
  | x :: t => p x && allTrue t p

private theorem allTrue_forall {l : List Card} {p : Card → Bool}
    (h : allTrue l p = true) : ∀ x ∈ l, p x = true := by
  induction l with
  | nil => intro x hx; cases hx
  | cons a t ih =>
      intro x hx
      rw [allTrue, Bool.and_eq_true] at h
      rcases List.mem_cons.mp hx with rfl | hmem
      · exact h.1
      · exact ih h.2 x hmem

private theorem wfB (n0 n1 n2 n3 : Nat) (st : State) (hd : 0 < st.drawStep)
    (e0 : st.found Suit.spade = (Suit.upCards Suit.spade).take n0)
    (e1 : st.found Suit.heart = (Suit.upCards Suit.heart).take n1)
    (e2 : st.found Suit.diamond = (Suit.upCards Suit.diamond).take n2)
    (e3 : st.found Suit.club = (Suit.upCards Suit.club).take n3)
    (hr : ∀ a : Anchor, runOK (st.piles a).faceUp = true)
    (hc : allTrue Card.universe (fun c => decide (st.cardCount c = 1)) = true) :
    st.WF := by
  refine ⟨fun s => ?_, fun a => hr a, fun c hc2 => ?_, hd⟩
  · cases s with
    | spade => exact ⟨n0, e0⟩
    | heart => exact ⟨n1, e1⟩
    | diamond => exact ⟨n2, e2⟩
    | club => exact ⟨n3, e3⟩
  · exact of_decide_eq_true (allTrue_forall hc c hc2)

private theorem uB_wf : uB.WF :=
  wfB 11 10 10 11 uB (by decide) (by decide) (by decide) (by decide) (by decide)
    (by intro a; cases a <;> decide) (by decide)

private theorem v1_wf : v1.WF :=
  wfB 11 11 10 11 v1 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by intro a; cases a <;> decide) (by decide)

private theorem v2_wf : v2.WF :=
  wfB 12 11 10 11 v2 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by intro a; cases a <;> decide) (by decide)

private theorem v3_wf : v3.WF :=
  wfB 12 11 10 11 v3 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by intro a; cases a <;> decide) (by decide)

private theorem v4_wf : v4.WF :=
  wfB 11 11 10 11 v4 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by intro a; cases a <;> decide) (by decide)

private theorem v5_wf : v5.WF :=
  wfB 11 10 10 11 v5 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by intro a; cases a <;> decide) (by decide)

/-! ## §4. Reversibility of the five legs -/

private theorem revV1 : reversibleAtW uB (Move.tabToFound cJH) :=
  (reversibleOf_iff_reversibleAtW uB_wf _).mp (by decide)

private theorem revV2 : reversibleAtW v1 (Move.tabToFound cQS) :=
  (reversibleOf_iff_reversibleAtW v1_wf _).mp (by decide)

private theorem revV3 : reversibleAtW v2 (Move.tabToTab cQC (Sum.inr kD)) :=
  (reversibleOf_iff_reversibleAtW v2_wf _).mp (by decide)

private theorem revV4 : reversibleAtW v3 (Move.foundToTab cQS (Sum.inr kH)) :=
  (reversibleOf_iff_reversibleAtW v3_wf _).mp (by decide)

private theorem revV5 : reversibleAtW v4 (Move.foundToTab cJH (Sum.inr cQS)) :=
  (reversibleOf_iff_reversibleAtW v4_wf _).mp (by decide)

/-! ## §5. The 5L play and its endpoint -/

private def play5 : List Move :=
  [Move.tabToFound cJH, Move.tabToFound cQS,
   Move.tabToTab cQC (Sum.inr kD),
   Move.foundToTab cQS (Sum.inr kH),
   Move.foundToTab cJH (Sum.inr cQS)]

private theorem play5_fwd : ShufflePlayW uB play5 v5 :=
  .cons revV1 stepV1
    (.cons revV2 stepV2
      (.cons revV3 stepV3
        (.cons revV4 stepV4
          (.cons revV5 stepV5 (.nil v5)))))

/-- The endpoint is the run splice at `Q♠`: the strict point swap. -/
private theorem v5_eq_splice : v5 = uB.spliceTwinRuns cQS := by
  apply State.ext
  · funext s
    cases s <;> decide
  · funext a
    cases a <;> decide
  · rfl
  · rfl
  · rfl

/-- The visible endpoint shape, for the report: `J♦` rides `Q♣` on
`K♦`, `J♥` rides `Q♠` on `K♥`. -/
theorem v5_shape :
    (v5.piles Anchor.p0).faceUp = [kD, cQC, cJD] ∧
      (v5.piles Anchor.p1).faceUp = [kH, cQS, cJH] := by
  constructor <;> rfl

/-- **The minimal both-covered 5L case.**  At world B's both-covered
`Q♠ | Q♣` pair the strict twin swap is orbit-realizable: the five
legs above clear the `J♥` rider, run the 3-leg foundation recipe at
the now-exposed `Q♠`, and re-seat the rider. -/
theorem swappableIn_uB_cQS : SwappableIn uB cQS := by
  refine ⟨v5, ?_, ?_⟩
  · rw [v5_eq_splice]
    exact twinPairSwapStrict_splice uB_wf ⟨kD, by decide⟩ ⟨kD, by decide⟩
  · exact RevEqW_symm (shufflePlayW_revEqW play5_fwd)

/-! ## §6. The abstract 5L template

The concrete route above is an instance of a two-line recipe: clear the
one rider `y` from the twin `x` that will be raised first (a pair-free
prelude), run the frozen one-raise recipe at the exposed `x`, then
transport `SwappableIn` back along the prelude's inverse (the re-seat).
The rider on `x.twin` is never cleared: it rides along in the slide.
-/

/-- `SwappableIn` is symmetric in the two members of the pair. -/
theorem swappableIn_twin_comm {s : State} {x : Card} :
    SwappableIn s x ↔ SwappableIn s x.twin := by
  constructor
  · rintro ⟨v, h, horb⟩
    obtain ⟨h1, h2, h3, hb, hf, hs, hw, hc⟩ := h
    refine ⟨v, ?_, horb⟩
    refine ⟨?_, ?_, ?_, hb, hf, hs, hw, hc⟩
    · simpa [card_twin_twin] using h2
    · simpa [card_twin_twin] using h1
    · intro y hy1 hy2
      exact h3 y (by simpa [card_twin_twin] using hy2) hy1
  · rintro ⟨v, h, horb⟩
    obtain ⟨h1, h2, h3, hb, hf, hs, hw, hc⟩ := h
    refine ⟨v, ?_, horb⟩
    refine ⟨?_, ?_, ?_, hb, hf, hs, hw, hc⟩
    · simpa [card_twin_twin] using h2
    · simpa [card_twin_twin] using h1
    · intro y hy1 hy2
      exact h3 y hy2 (by simpa [card_twin_twin] using hy1)

/-- **The pair-free-prelude template — the 5L/7L/ladder family.**  A
pair-free reversible prelude `pre` exposes `x` at `u`; the frozen
one-raise recipe at `u` realizes `SwappableIn u x`; and the prelude's
legal pair-free inverse `post` transfers the predicate back to `s`.

The rider on `x.twin` is never touched: the recipe's slide carries its
whole run.  `pre` may be one rider raise (5L), two cover raises (7L),
or a licensure ladder ending in `x`'s raise (the `Q♥ | Q♦` cells). -/
theorem swappableIn_of_pairFree_prelude
    {s u : State} {x z : Card} {pre post : List Move}
    (hwf_s : s.WF) (hwf_u : u.WF)
    (hxs : ∃ z, seatOf s x = some (Sum.inr z))
    (hxts : ∃ z : Card, seatOf s x.twin = some (Sum.inr z.twin))
    (hc : seatOf u x = some (Sum.inr z.twin))
    (hct : seatOf u x.twin = some (Sum.inr z))
    (hraise : reversibleAtW u (Move.tabToFound x))
    (_hpre : ShufflePlayW s pre u)
    (hpost : ShufflePlayW u post s)
    (hno : ∀ m ∈ post, NotFoundPair x m) :
    SwappableIn s x := by
  have hxu : ∃ z', seatOf u x = some (Sum.inr z') := ⟨z.twin, hc⟩
  have hxtu : ∃ z' : Card, seatOf u x.twin = some (Sum.inr z'.twin) :=
    ⟨(z.twin : Card), by rw [card_twin_twin]; exact hct⟩
  have hc' : seatOf u x.twin.twin = some (Sum.inr z.twin) := by
    rw [card_twin_twin]; exact hc
  have hraise' : reversibleAtW u (Move.tabToFound x.twin.twin) := by
    rw [card_twin_twin]; exact hraise
  have hswap_u_twin : SwappableIn u x.twin :=
    swappableIn_of_twin_raise (c := x.twin) (z := z) hwf_u hct hc' hraise'
  have hswap_u : SwappableIn u x :=
    (swappableIn_twin_comm (s := u) (x := x)).mpr hswap_u_twin
  exact swappableIn_transfer_point_play hwf_u hwf_s hxu hxtu hxs hxts hpost hno
    hswap_u

/-- **The minimal 5L instance.**  `pre = [tabToFound y]` clears the one
rider on `x`; the frozen 3-leg recipe fires at `u`; `post` is the
inverse re-seat.  No rider on `x.twin` is cleared. -/
theorem swappableIn_of_rider_raise
    {s u : State} {x y z : Card}
    (hwf_s : s.WF) (hwf_u : u.WF)
    (hxs : ∃ z, seatOf s x = some (Sum.inr z))
    (hxts : ∃ z : Card, seatOf s x.twin = some (Sum.inr z.twin))
    (hc : seatOf u x = some (Sum.inr z.twin))
    (hct : seatOf u x.twin = some (Sum.inr z))
    (hraise : reversibleAtW u (Move.tabToFound x))
    (hyx : y ≠ x) (hyt : y ≠ x.twin)
    (hpre : ShufflePlayW s [Move.tabToFound y] u)
    (hpost : ShufflePlayW u [Move.foundToTab y (Sum.inr x)] s) :
    SwappableIn s x := by
  have hno : ∀ m ∈ [Move.foundToTab y (Sum.inr x)], NotFoundPair x m := by
    intro m hm
    simp only [List.mem_singleton] at hm
    subst hm
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro h; nomatch h
    · intro h; nomatch h
    · intro b h; injection h with hy _; exact hyx hy
    · intro b h; injection h with hy _; exact hyt hy
  exact swappableIn_of_pairFree_prelude (pre := [Move.tabToFound y])
    (post := [Move.foundToTab y (Sum.inr x)]) hwf_s hwf_u hxs hxts hc hct
    hraise hpre hpost hno

/-! ## §7. The frozen edit-level template

`TwinParentShift.exchangeSuffix_eq_splice_bottom` reduces the E-face
suffix exchange at `Q♠` to the lower pair's run splice at `J♥ | J♦`,
and `TwinSuffixExchange.relabelTwin_exchangeSuffix` turns that into the
S-face point splice.  The 5L play above is the physical realization of
this edit identity; the relabel is not itself a legal move.
-/

/-- **The frozen parent-shift template at world B.** -/
theorem uB_parent_shift :
    uB.exchangeSuffix cQS = uB.spliceTwinRuns cJH :=
  exchangeSuffix_eq_splice_bottom (s := uB) (x := cQS) (y := cJH)
    (a := Anchor.p0) (b := Anchor.p1) (restA := []) (restB := [])
    uB_wf (by decide) (by decide) (by decide) (by decide) (by decide)

/-- **The frozen relabel decomposition at world B:**
`S(Q♠) = ρ(Q♠) ∘ E(Q♠) = ρ(Q♠) ∘ S(J♥)`. -/
theorem uB_relabel_decomposition :
    State.relabelTwin cQS (uB.exchangeSuffix cQS) = uB.spliceTwinRuns cQS :=
  relabelTwin_exchangeSuffix uB_wf ⟨kD, by decide⟩ ⟨kD, by decide⟩

/-- The both-covered **S-face is the E-face relabelled**, not the
lower-pair point swap itself: the parent-shift only gives
`E(Q♠) = S(J♥)`. -/
theorem uB_splice_via_lower :
    State.relabelTwin cQS (uB.spliceTwinRuns cJH) = uB.spliceTwinRuns cQS := by
  rw [← uB_parent_shift]
  exact uB_relabel_decomposition

/-- The lower pair `J♥ | J♦` is itself one-bare (both riders top their
piles), so its point swap is exactly the frozen 3-leg recipe.  This is
the contrast that shows why the upper 5L block is genuinely extra: the
parent-shift gives `E(Q♠) = S(J♥)`, but the S-face at `Q♠` is
`ρ(Q♠) ∘ S(J♥)`, and `ρ` is not a legal move. -/
theorem swappableIn_uB_cJH : SwappableIn uB cJH :=
  swappableIn_of_twin_raise (c := cJH) (z := cQS) uB_wf
    (by decide) (by decide)
    ((reversibleOf_iff_reversibleAtW uB_wf (Move.tabToFound cJD)).mp (by decide))

#print axioms v5_shape
#print axioms swappableIn_uB_cQS
#print axioms swappableIn_twin_comm
#print axioms swappableIn_of_pairFree_prelude
#print axioms swappableIn_of_rider_raise
#print axioms uB_parent_shift
#print axioms uB_relabel_decomposition
#print axioms uB_splice_via_lower
#print axioms swappableIn_uB_cJH

end TwinBothCovered

/-!
## §8. Public surface for the concrete 5L world

The concrete world B is entirely private above.  These aliases expose
the pair card, the two endpoints, the five-move play, and the private
rows needed by downstream cards, without changing any private proof.
-/

namespace TwinBothCovered

open State

/-- Public alias for the concrete pair card `Q♠` of world B. -/
def cQSpub : Card := cQS

/-- Public alias for world B's concrete source state. -/
def uBpub : State := uB

/-- Public alias for the concrete five-leg endpoint state. -/
def v5pub : State := v5

/-- Public alias for the concrete five-move play. -/
def play5pub : List Move := play5

/-- The private world-B integrity row, exposed. -/
theorem uBpub_wf : uBpub.WF := uB_wf

/-- Both twins are `.inr`-seated at the concrete source: `Q♠` on `K♦`
and `Q♣` on `K♥`. -/
theorem uBpub_seats :
    (∃ z, seatOf uBpub cQSpub = some (Sum.inr z)) ∧
      (∃ z : Card, seatOf uBpub cQSpub.twin = some (Sum.inr z.twin)) :=
  ⟨⟨⟨Suit.diamond, Rank.king⟩, by decide⟩,
   ⟨⟨Suit.diamond, Rank.king⟩, by decide⟩⟩

/-- The private five-leg shuffle, exposed at the public aliases. -/
theorem play5pub_shuffle : ShufflePlayW uBpub play5pub v5pub := play5_fwd

/-- The private endpoint identity `v5 = uB.spliceTwinRuns Q♠`, exposed. -/
theorem v5pub_eq_splice : v5pub = uBpub.spliceTwinRuns cQSpub := v5_eq_splice

/-- The private concrete swap at world B, exposed at the public aliases. -/
theorem swappableIn_uB_cQSpub : SwappableIn uBpub cQSpub := swappableIn_uB_cQS

#print axioms cQSpub
#print axioms uBpub
#print axioms v5pub
#print axioms play5pub
#print axioms uBpub_wf
#print axioms uBpub_seats
#print axioms play5pub_shuffle
#print axioms v5pub_eq_splice
#print axioms swappableIn_uB_cQSpub

end TwinBothCovered
