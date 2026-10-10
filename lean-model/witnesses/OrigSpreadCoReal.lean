import Orig.Dominance

/-!
# The (C) spread-residue co-realizability witness — premises, a
spread-shaped winning play, and the repair's positive instance

The farm-orig-dom-c-normform session's regress layer (2026-10-10),
for `draw1_worry_spread_residue` (Dominance §5.3(C)'s one named
stub) and its parent `draw1_compliant_normalForm`.

* **Co-realizability** — the residue's premises are inhabited
  TOGETHER at ONE WF draw-1 state: `wState` carries the stocked,
  next-up `♥K` (`c`; hearts at height 12, so the suit's top is
  `x = ♥Q`), one `♣K`-topped pile as the worry's fit, and the other
  two suits complete.  The exhibited winning play OPENS with the
  c-suit worry `foundToTab ♥Q (inr ♣K)` followed by a `draw` — a
  move OTHER than the restack: the spread shape.  No premise is
  vacuous; no guard is unsatisfiable.

* **The repair's positive instance** — the SAME state carries the
  compliant winning play `[draw, wasteToFound ♥K, tabToFound ♣K]`:
  the exhibited play with the worry/restack pair excised, ending at
  the SAME won state (`wFin`) — the pair cancel through
  `foundToTab_return`'s identity, decide-anchored here.

* **The gate** — this residue's refute-first gate (and the wave-24
  (C)-gate, `a compliant-less corner`, doubling as it) was probed by
  crafting corner variants of `wState`: clubs stripped below height
  12 so the worry's landing is load-bearing, the kings swapped
  between the twin red suits, `c` pre-loaded in the waste against
  the stock.  Every crafted corner either failed to co-fire the
  premises or still admitted a compliant winning play — the
  52-card full countermodel search is outside decide reach — so NO
  refutation of the residue-shaped statement was found this session.
  What this file regression-pins is the premises' honesty, the
  spread shape's realizability, and the repair's positive instance
  at the pinned state.
-/

namespace OrigSpreadCoreal

/-! ## The craft state -/

private def H (r : Rank) : Card := ⟨Suit.heart, r⟩
private def S (r : Rank) : Card := ⟨Suit.spade, r⟩
private def D (r : Rank) : Card := ⟨Suit.diamond, r⟩
private def C (r : Rank) : Card := ⟨Suit.club, r⟩

private def foundF : Suit → List Card
  | .heart => [H .ace, H .two, H .three, H .four, H .five, H .six, H .seven,
      H .eight, H .nine, H .ten, H .jack, H .queen]
  | .club => [C .ace, C .two, C .three, C .four, C .five, C .six, C .seven,
      C .eight, C .nine, C .ten, C .jack, C .queen]
  | .spade => [S .ace, S .two, S .three, S .four, S .five, S .six, S .seven,
      S .eight, S .nine, S .ten, S .jack, S .queen, S .king]
  | .diamond => [D .ace, D .two, D .three, D .four, D .five, D .six, D .seven,
      D .eight, D .nine, D .ten, D .jack, D .queen, D .king]

private def pilesF : Anchor → Pile
  | .p0 => ⟨[], [C .king]⟩
  | _ => ⟨[], []⟩

/-- The craft state: hearts and clubs each one king short (their
kings are the stocked rung card `♥K` and the sole pile top `♣K`),
spades and diamonds complete, `drawStep = 1`, empty waste. -/
def wState : State where
  found := foundF
  piles := pilesF
  stock := [H .king]
  waste := []
  drawStep := 1

/-- The won endpoint of both exhibited plays: every foundation
complete, board and cycle empty. -/
def wFin : State where
  found := fun s => s.upCards
  piles := fun _ => ⟨[], []⟩
  stock := []
  waste := []
  drawStep := 1

/-! ## The state is WF -/

private theorem wState_wf : wState.WF := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s
    cases s with
    | spade => exact ⟨13, rfl⟩
    | heart => exact ⟨12, rfl⟩
    | diamond => exact ⟨13, rfl⟩
    | club => exact ⟨12, rfl⟩
  · intro a
    cases a <;> decide
  · intro c _
    rcases c with ⟨s, r⟩
    cases s <;> cases r <;> decide
  · decide

/-! ## The local instruments

`decSt` is the same hand-rolled `DecidableEq State` the witness
corpus's other files carry (see `witnesses/OrigKingAnchorWitness.lean`'s
copy, dedup-marked there as "family 1"): state equality as a
14-component pointwise decision, so the step/run equations below are
`decide`-anchored. -/

private def decSt (s t : State) : Decidable (s = t) :=
  decidable_of_decidable_of_iff (p :=
    (s.found .spade = t.found .spade ∧ s.found .heart = t.found .heart ∧
     s.found .diamond = t.found .diamond ∧ s.found .club = t.found .club ∧
     s.piles .p0 = t.piles .p0 ∧ s.piles .p1 = t.piles .p1 ∧
     s.piles .p2 = t.piles .p2 ∧ s.piles .p3 = t.piles .p3 ∧
     s.piles .p4 = t.piles .p4 ∧ s.piles .p5 = t.piles .p5 ∧
     s.piles .p6 = t.piles .p6 ∧
     s.stock = t.stock ∧ s.waste = t.waste ∧ s.drawStep = t.drawStep))
    (by
      constructor
      · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩
        apply State.ext
        · funext σ; cases σ <;> assumption
        · funext a; cases a <;> assumption
        · assumption
        · assumption
        · assumption
      · rintro rfl
        exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩)

local instance : DecidableEq State := fun s t => decSt s t

/-! ## The (C)-bundle and the residue's premises at `wState` -/

/-- The root (C)-bundle, decide-anchored: `♥K` is stocked, next-up,
and SAFE (every opposite-color foundation sits within one of its
index; hearts/diamonds within two). -/
theorem wState_cBundle :
    wState.drawStep = 1 ∧ wState.nextUp (H .king) = true ∧ (H .king) ∈ wState.stock ∧
      safeToFound wState (H .king) = true := by
  refine ⟨rfl, by decide, by decide, by decide⟩

/-- The residue's suit premise: the worried card is `c`'s suit top
(hearts at height 12 topped by the queen, `c` the king one above). -/
theorem wState_xSuit : (H .queen).suit = (H .king).suit := rfl

/-- The spread second-move premise: `draw` is not the restack. -/
theorem wState_neDraw : Move.draw ≠ Move.tabToFound (H .queen) := by decide

/-- The worry-successor of the exhibited play: `♥Q` chopped off the
hearts foundation onto the `♣K`-topped pile. -/
def wMid : State where
  found := fun s =>
    match s with
    | .heart => [H .ace, H .two, H .three, H .four, H .five, H .six, H .seven,
        H .eight, H .nine, H .ten, H .jack]
    | .club => foundF .club
    | .spade => foundF .spade
    | .diamond => foundF .diamond
  piles := fun a =>
    match a with
    | .p0 => ⟨[], [C .king, H .queen]⟩
    | _ => ⟨[], []⟩
  stock := [H .king]
  waste := []
  drawStep := 1

/-- The worry fires at `wState` — `♥Q` onto the `♣K` pile — and the
remaining play `[draw; restack; c-exit; ♣K-raise]` WINS: the
premises of the residue co-fire with a spread-shaped witness play
whose window's second move is a `draw`. -/
theorem wState_spread :
    ∃ s₁, State.step wState (Move.foundToTab (H .queen) (Sum.inr (C .king))) = some s₁ ∧
      s₁.run [Move.draw, Move.tabToFound (H .queen), Move.wasteToFound (H .king),
        Move.tabToFound (C .king)] = some wFin ∧ wFin.isWin = true := by
  refine ⟨wMid, by decide, by decide, by decide⟩

/-! ## The repair's positive instance -/

/-- The two-moves-shorter play is compliant AND winning at the same
state: the head draw is rung-clean, the second move is the c-exit
(wasteToFound `♥K`), and the raise of `♣K` completes the clubs with
the worried `♥Q` never having left its foundation. -/
theorem wState_compliant :
    ∃ w, wState.run [Move.draw, Move.wasteToFound (H .king), Move.tabToFound (C .king)] = some w ∧
      w.isWin = true ∧ rungHeldUntilExit (H .king)
        [Move.draw, Move.wasteToFound (H .king), Move.tabToFound (C .king)] := by
  refine ⟨wFin, by decide, by decide, ?_⟩
  exact Or.inr ⟨rfl, Or.inl rfl⟩

/-- The adjacent window's cancellation, decide-anchored at the
craft state — the worry/restack pair in front of the compliant play
changes nothing: `[worry; restack]` composites to the identity
(`foundToTab_return`'s two-step shape at one concrete instance). -/
theorem wState_pairId :
    wState.run [Move.foundToTab (H .queen) (Sum.inr (C .king)), Move.tabToFound (H .queen),
      Move.draw, Move.wasteToFound (H .king), Move.tabToFound (C .king)] = some wFin := by
  decide

end OrigSpreadCoreal
