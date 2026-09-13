import Klondike.Initial

/-!
# `apply_wf` witnesses #3 & #4 — the states the repairs now reject

Witness #3 (2026-09-13): the strengthened inr disjunct 1 (`∃ a,
topHidden a = some d`) did not force the sitting card to be
deal-adjacent to `d`.  `reveal` leaves the trigger card on the
freshly-revealed card *as a visible-on-visible edge*; absent adjacency
(or `canSitOn`), no disjunct of the then-current clause justified it in
the successor.  Witness `stE`: standard deal, depths 1 everywhere,
board {inr ♥2 ↦ ♠9} (♠9 sits on pile p1's hidden boundary — legal by
the then-disjunct 1 — but ♠9 was dealt in pile p6, not adjacent to
♥2), fresh stock; `reveal ♠9` was legal and the successor was not WF.

Witness #4 (independent residual hole): WF constrained the deal's stock
and the state stock's internal distinctness, but never the state's
stock against the deal's PILES.  A boundary card sitting in the
state's stock becomes visible under `reveal` while remaining in the
stock — `isVis → posOf = none` breaks.  Witness `stF`: standard deal,
depths 1, board {inr ♥2 ↦ ♥3} (deliberately deal-adjacent, isolating
this hole), stock ⟨[♥2, ♠9], 1⟩; `reveal ♥3` was legal and the
successor had ♥2 visible with `posOf ♥2 = some 0`.

Both repairs landed 2026-09-13 (board_edges' deal-adjacency base
condition; WF's stock membership conjunct) and `apply_wf` is PROVEN —
the old `apply_wf_still_unsound_(reveal|stock) : False` theorems are
now false statements and have been removed.  What remains is the
positive regression: both witness STATES are now rejected outright by
the strengthened invariant itself (`stE_not_wf`, `stF_not_wf`) — no
state of either shape can ever again instantiate the move-preserves-WF
claim to refute it.
-/

/-- ♥2: pile p1's bottom card. -/
def c2 : Card := ⟨Suit.heart, Rank.two⟩

/-- ♠9: pile p6's bottom card. -/
def s9 : Card := ⟨Suit.spade, Rank.nine⟩

/-- ♠9 visible, sitting on pile p1's hidden boundary ♥2. -/
def bdE : Board where
  topOf := Board.update Board.empty.topOf (Sum.inr c2) (some s9)
  inj := Board.attach_inj Board.empty (Sum.inr c2) s9 (Board.empty_bottomOf s9)

/-- The witness state: boundary at 1 everywhere, fresh stock. -/
def stE : State where
  deal := Deal.standard
  board := bdE
  heights := fun _ => 0
  depths := fun _ => 1
  stock := ⟨Deal.standard.stock, 0⟩
  drawStep := 1

/-- The reveal successor (computed by the kernel; kept as the
countermodel record). -/
def stE1 : State := (stE.apply (Move.reveal s9)).getD stE

theorem stE_topOf_self : stE.board.topOf (Sum.inr c2) = some s9 :=
  Board.update_self Board.empty.topOf (Sum.inr c2) (some s9)

theorem stE_topOf_ne {b : Base} (h : b ≠ Sum.inr c2) : stE.board.topOf b = none :=
  (Board.update_ne Board.empty.topOf (Sum.inr c2) b (some s9) h).trans (Board.empty_topOf b)

/-- KILLED BY THE `board_edges` REPAIR: the ♠9-on-♥2 edge is neither
deal-adjacent (♠9 was dealt in p6, ♥2 in p1 — no pile holds them
consecutively in that order) nor canSitOn-legal (9 does not sit on 2),
and ♥2 is nowhere placed — the strengthened clause rejects the state
itself. -/
theorem stE_not_wf : ¬ stE.WF := by
  intro hwf
  have hedge := hwf.board_edges (Sum.inr c2) s9 stE_topOf_self
  rcases hedge.2 with ⟨a, t, rest, hpiles, -⟩ | ⟨-, hcs⟩
  · have hc2 : c2 ∈ stE.deal.piles a := by rw [hpiles]; simp
    have hs9 : s9 ∈ stE.deal.piles a := by rw [hpiles]; simp
    cases a with
    | p0 => exact absurd hc2 (by decide)
    | p1 => exact absurd hs9 (by decide)
    | p2 => exact absurd hc2 (by decide)
    | p3 => exact absurd hc2 (by decide)
    | p4 => exact absurd hc2 (by decide)
    | p5 => exact absurd hc2 (by decide)
    | p6 => exact absurd hc2 (by decide)
  · exact absurd hcs (show ¬ (canSitOn s9 c2 = true) from by decide)

/-- The countermodel's premise still holds (by the kernel): `reveal ♠9`
is legal at the witness. -/
example : (stE.apply (Move.reveal s9)).isSome = true := by decide

/-! ## Witness #4 — the stock⊄deal hole, closed by membership -/

/-- ♥3: pile p1's top dealt card (deal-adjacent to ♥2). -/
def c3 : Card := ⟨Suit.heart, Rank.three⟩

/-- The adjacent one-edge board: ♥3 on the hidden boundary ♥2. -/
def bdF : Board where
  topOf := Board.update Board.empty.topOf (Sum.inr c2) (some c3)
  inj := Board.attach_inj Board.empty (Sum.inr c2) c3 (Board.empty_bottomOf c3)

/-- The old witness: the stock carries the boundary card ♥2 itself. -/
def stF : State where
  deal := Deal.standard
  board := bdF
  heights := fun _ => 0
  depths := fun _ => 1
  stock := ⟨[c2, s9], 1⟩
  drawStep := 1

/-- The reveal successor (computed by the kernel; kept as the
countermodel record). -/
def stF1 : State := (stF.apply (Move.reveal c3)).getD stF

theorem stF_topOf_self : stF.board.topOf (Sum.inr c2) = some c3 :=
  Board.update_self Board.empty.topOf (Sum.inr c2) (some c3)

theorem stF_topOf_ne {b : Base} (h : b ≠ Sum.inr c2) : stF.board.topOf b = none :=
  (Board.update_ne Board.empty.topOf (Sum.inr c2) b (some c3) h).trans (Board.empty_topOf b)

/-- KILLED BY THE `stock_wf` REPAIR: the state's cycle must be a
sub-list of the deal's stock — the boundary ♥2 is dealt in p1, so
carrying it in the cycle is now impossible (the old proof needed the
successor; the repair kills the source state directly). -/
theorem stF_not_wf : ¬ stF.WF := by
  intro hwf
  have hmem := hwf.stock_wf.2 c2 (by decide)
  exact absurd hmem (by decide)

/-- The countermodel's premise still holds (by the kernel): `reveal ♥3`
is legal at the witness (the edge is genuinely deal-adjacent). -/
example : (stF.apply (Move.reveal c3)).isSome = true := by decide

/-- info: 'stE_not_wf' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms stE_not_wf

/-- info: 'stF_not_wf' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms stF_not_wf
