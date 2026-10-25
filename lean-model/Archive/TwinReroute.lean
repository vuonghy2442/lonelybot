import Orig2.DetourKit
import Orig2.TwinRecipeSegment

/-!
# Orig2.TwinReroute — the base-case pair-foundation reroute

The play splits into

  pair-free prefix  ++  the exact 3-leg recipe  ++  pair-free suffix.

The prefix and suffix use the rider-free transfer; the recipe segment uses
`swappableIn_recipe_segment`.  This is the base case of the reroute; longer
5L/7L detours and covered pairs remain outside this card.
-/

/-- **TwinReady s x** — both twins are seated and rider-free at `s`. -/
def TwinReady (s : State) (x : Card) : Prop :=
  (∃ b, seatOf s x = some b) ∧ (∃ b, seatOf s x.twin = some b) ∧
    (∀ y, y ≠ x → seatOf s y ≠ some (Sum.inr x)) ∧
    (∀ y, y ≠ x.twin → seatOf s y ≠ some (Sum.inr x.twin))

/-- **The base-case reroute.**  A pair-free prefix, the exact 3-leg recipe,
and a pair-free suffix transfer `SwappableIn` from `s` to `s'`. -/
theorem swappableIn_transfer_recipePlay
    {s u w s' : State} {x z : Card} {a : Anchor} {pre post : List Move}
    (hwf : s.WF) (hwfu : u.WF) (hwfw : w.WF) (hwf' : s'.WF)
    (hready_s : TwinReady s x) (hready_u : TwinReady u x)
    (hready_w : TwinReady w x) (hready_s' : TwinReady s' x)
    (hpre : ShufflePlayW s pre u)
    (hnoPre : ∀ m ∈ pre, NotFoundPair x m)
    (hseg : ShufflePlayW u
      [Move.tabToFound x.twin, Move.tabToTab x (Sum.inr z.twin),
        Move.foundToTab x.twin (Sum.inr z)] w)
    (hpost : ShufflePlayW w post s')
    (hnoPost : ∀ m ∈ post, NotFoundPair x m)
    (hc : seatOf u x = some (Sum.inr z))
    (hct : seatOf u x.twin = some (Sum.inr z.twin))
    (hpa : u.pileOfTop x.twin = some a)
    (hraise : reversibleAtW u (Move.tabToFound x.twin))
    (hswap : SwappableIn s x) :
    SwappableIn s' x := by
  obtain ⟨hsx, hstx, hrx, hrt⟩ := hready_s
  obtain ⟨hux, hutx, hurx, hurt⟩ := hready_u
  obtain ⟨hwx, hwtx, hwrx, hwrt⟩ := hready_w
  obtain ⟨hs'x, hs'tx, hs'rx, hs'rt⟩ := hready_s'
  have h1 : SwappableIn u x :=
    swappableIn_transfer_of_seated_riderFree hwf hwfu
      hsx hstx hux hutx hrx hrt hurx hurt hpre hnoPre hswap
  have h2 : SwappableIn w x :=
    (swappableIn_recipe_segment hwfu hwfw hc hct hpa hraise hseg
      hurx hurt hwrx hwrt).mp h1
  exact swappableIn_transfer_of_seated_riderFree hwfw hwf'
    hwx hwtx hs'x hs'tx hwrx hwrt hs'rx hs'rt hpost hnoPost h2

#print axioms swappableIn_transfer_recipePlay
