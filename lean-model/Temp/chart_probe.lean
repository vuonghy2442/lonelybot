import Orig2.Vocab

/-!
# The chart book's kernel probe (2026-10-18)

Scratch for the `chart_round_trip` / `chart_draw` discharge card:

* PROBE 1 — the ungated round trip is FALSE at wild states: the
  below-mask doppelganger.  A card whose FIRST face-up occurrence is
  at an early pile is chart-masked in every LATER pile: the seat
  search stops at the first pile, so a masked extra copy of a card in
  a late pile changes no readout whatsoever.  Two states differing
  only in the ORDER (and multiplicity) of the masked tail of one
  late pile are chart-twins but not equal.
* PROBE 2 — ext shapes and core row availability.

RESULT (2026-10-18): CONFIRMED — the refutation below compiled
verbatim at battery [propext] and moved INTO THE TREE as
`Orig2.Chart.chart_round_trip_ungated_false` (with the re-gated
keystone `chart_round_trip` at [propext, Quot.sound]); this file is
the day-one scratch and stays for provenance.
-/

#check @State.ext
#check @Pile.ext
#check @List.reverse_reverse
#check @List.reverse_append
#check @List.length_reverse
#check @List.take_append_drop
#check @decide_eq_true
#print axioms List.reverse_reverse
#print axioms List.take_append_drop

/-! ## §1. The wild doppelgangers -/

/-- The masked card (a spade king). -/
def wC : Card := ⟨.spade, .king⟩
/-- The second masked card (a heart ace). -/
def wD : Card := ⟨.heart, .ace⟩

/-- The seven-pile board: c bottoms p0, d bottoms p1, both also ride
p5's face-up deck (the masked tail). -/
def wpA : Anchor → Pile
  | .p0 => ⟨[], [wC]⟩
  | .p1 => ⟨[], [wD]⟩
  | .p5 => ⟨[], [wC, wD]⟩
  | _ => ⟨[], ([] : List Card)⟩

/-- The twin board: the same first-occurrence seats, p5's masked tail
swapped in order. -/
def wpB : Anchor → Pile
  | .p0 => ⟨[], [wC]⟩
  | .p1 => ⟨[], [wD]⟩
  | .p5 => ⟨[], [wD, wC]⟩
  | _ => ⟨[], ([] : List Card)⟩

def wS : State :=
  { found := fun _ => [], piles := wpA, stock := [], waste := [],
    drawStep := 1 }
def wW : State :=
  { found := fun _ => [], piles := wpB, stock := [], waste := [],
    drawStep := 1 }

/-- The two wild states differ. -/
theorem wS_ne_wW : wS ≠ wW := by
  intro h
  have h5 : (wS.piles .p5).faceUp = (wW.piles .p5).faceUp :=
    congrArg (fun (s : State) => (s.piles .p5).faceUp) h
  exact absurd h5 (by decide)

/-- Seat raw computation at the wild pair: identical readouts.
The two special cards (and the two states' empties) reduce by `rfl`. -/
example : wS.pileHolding wC = some .p0 := rfl
example : wW.pileHolding wC = some .p0 := rfl
example : wS.pileHolding wD = some .p1 := rfl
example : wW.pileHolding wD = some .p1 := rfl
example : seatOf wS wC = some (.inl .p0) := rfl
example : seatOf wW wC = some (.inl .p0) := rfl
example : seatOf wS wD = some (.inl .p1) := rfl
example : seatOf wW wD = some (.inl .p1) := rfl

/-- A third card sits nowhere on either board, so both searches
decline (the search scans all seven piles of the concrete board). -/
example : (wS.pileHolding ⟨.club, .two⟩) = none := rfl
example : (wW.pileHolding ⟨.club, .two⟩) = none := rfl

/-- The full chart agreement of the wild pair (the kernel premise of
the refutation). -/
theorem chartAgree_wS_wW : chartAgree wS wW := by
  refine ⟨?_, ⟨?_, rfl⟩, fun _ => rfl, rfl, rfl⟩
  · intro c
    match c with
    | ⟨.spade, .king⟩ => rfl
    | ⟨.heart, .ace⟩ => rfl
    | ⟨.diamond, .ace⟩ => rfl
    | ⟨.club, .two⟩ => rfl
    | ⟨.spade, .ace⟩ => rfl
    | ⟨.heart, .king⟩ => rfl
    | ⟨.diamond, .king⟩ => rfl
    | ⟨.club, .king⟩ => rfl
    | ⟨.spade, .queen⟩ => rfl
    | ⟨.heart, .two⟩ => rfl
    | ⟨.spade, .two⟩ => rfl
    | ⟨.diamond, .two⟩ => rfl
    | ⟨.club, .ace⟩ => rfl
    | ⟨.heart, .queen⟩ => rfl
    | ⟨.diamond, .queen⟩ => rfl
    | ⟨.club, .queen⟩ => rfl
    | ⟨.spade, .three⟩ => rfl
    | ⟨.heart, .three⟩ => rfl
    | ⟨.diamond, .three⟩ => rfl
    | ⟨.club, .three⟩ => rfl
    | ⟨.spade, .four⟩ => rfl
    | ⟨.heart, .four⟩ => rfl
    | ⟨.diamond, .four⟩ => rfl
    | ⟨.club, .four⟩ => rfl
    | ⟨.spade, .five⟩ => rfl
    | ⟨.heart, .five⟩ => rfl
    | ⟨.diamond, .five⟩ => rfl
    | ⟨.club, .five⟩ => rfl
    | ⟨.spade, .six⟩ => rfl
    | ⟨.heart, .six⟩ => rfl
    | ⟨.diamond, .six⟩ => rfl
    | ⟨.club, .six⟩ => rfl
    | ⟨.spade, .seven⟩ => rfl
    | ⟨.heart, .seven⟩ => rfl
    | ⟨.diamond, .seven⟩ => rfl
    | ⟨.club, .seven⟩ => rfl
    | ⟨.spade, .eight⟩ => rfl
    | ⟨.heart, .eight⟩ => rfl
    | ⟨.diamond, .eight⟩ => rfl
    | ⟨.club, .eight⟩ => rfl
    | ⟨.spade, .nine⟩ => rfl
    | ⟨.heart, .nine⟩ => rfl
    | ⟨.diamond, .nine⟩ => rfl
    | ⟨.club, .nine⟩ => rfl
    | ⟨.spade, .ten⟩ => rfl
    | ⟨.heart, .ten⟩ => rfl
    | ⟨.diamond, .ten⟩ => rfl
    | ⟨.club, .ten⟩ => rfl
    | ⟨.spade, .jack⟩ => rfl
    | ⟨.heart, .jack⟩ => rfl
    | ⟨.diamond, .jack⟩ => rfl
    | ⟨.club, .jack⟩ => rfl
  · intro a
    match a with
    | .p0 => rfl
    | .p1 => rfl
    | .p2 => rfl
    | .p3 => rfl
    | .p4 => rfl
    | .p5 => rfl
    | .p6 => rfl

/-- **KERNEL WITNESS** — the ungated round trip is FALSE: the wild
pair agrees on every chart readout yet the states differ. -/
theorem chart_round_trip_ungated_false :
    ¬ (∀ st w : State, chartAgree st w → st = w) := by
  intro h
  exact absurd (h wS wW chartAgree_wS_wW) wS_ne_wW
