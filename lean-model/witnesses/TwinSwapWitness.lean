import Klondike.TwinSwap

/-!
# TwinSwapWitness — why the local twin swap needs equal heights

Refutation of the weakening "liveness (both twins not yet on the
foundation) suffices for the swap conjugation", proposed 2026-09-13.

The witness: t = ♦5, t' = ♥5 — both live (4 < 4 false, 4 < 3 false —
neither is foundation-passed) — with heights ♦ = 4, ♥ = 3.  ♦5 sits
bare on anchor p0, so `pileStack ♦5` is legal (rank 4 = ♦ 4).  The
swapped state's image move is `pileStack ♥5`, whose guard probes the
*hearts* count (3 ≠ 4): illegal.  The legality sets do not correspond
under the swap, so no automorphism — and the would-be unconditional
`apply_swapTwin` (and the liveness-licensed `solvable_swapTwin`) is
false as stated.

Root cause: the foundation guards consult heights *per suit*, and the
suit is shared with every other card of the suit (a non-swapped ♥7
still probes the hearts count) — the renaming can't move the count for
just the pair, so the two counts must already agree.  Hence the
licensed form in `Klondike/TwinSwap.lean` keeps `heights t.suit =
heights t.flipSuit.suit`, supplied in practice by §5.5's both-redundant
setup (`State.redundantTwins_heights_eq`).

The state is deliberately minimal (the falsified statements have no WF
hypothesis — the quantifier is over all states); a WF-hardened variant
with a winning-line tempo race (the weak license breaking the
*solvability* iff, not just move correspondence) is probe work for the
Rust differential.
-/

namespace TwinSwapWitness

abbrev wh4 : Card := ⟨Suit.heart, Rank.four⟩
abbrev wh5 : Card := ⟨Suit.heart, Rank.five⟩
abbrev wd5 : Card := ⟨Suit.diamond, Rank.five⟩

/-- The witness's board: ♦5 alone on anchor p0 (built through `attach`
so the injectivity field comes for free). -/
def wboard : Board := (Board.empty.attach (Sum.inl Anchor.p0) wd5).getD Board.empty

/-- The witness state: heights ♦ = 4 (♦5 stackable), ♥ = 3 (♥5 not),
draw-1, empty stock. -/
def wst : State where
  deal := { piles := fun _ => [], stock := [] }
  board := wboard
  heights := fun s => if s = Suit.diamond then 4 else if s = Suit.heart then 3 else 0
  depths := fun _ => 0
  stock := ⟨[], 0⟩
  drawStep := 1

-- Both twins are live (not foundation-passed):
/-- info: false -/
#guard_msgs in
#eval wst.onFound wd5
/-- info: false -/
#guard_msgs in
#eval wst.onFound wh5

-- Yet the move correspondence breaks across the swap:
/-- info: true -/
#guard_msgs in
#eval (wst.apply (Move.pileStack wd5)).isSome
-- (bare at p0, rank 4 = ♦ 4)
/-- info: false -/
#guard_msgs in
#eval ((wst.swapTwin wd5).apply (Move.pileStack wh5)).isSome
-- (the image move probes the HEARTS count: 4 ≠ 3)

/-- The prover-confirmed core: legal before, illegal after (axioms
should be [propext, Quot.sound] only — none at all expected). -/
example : (wst.apply (Move.pileStack wd5)).isSome = true
    ∧ ((wst.swapTwin wd5).apply (Move.pileStack wh5)).isSome = false := by
  decide

end TwinSwapWitness
