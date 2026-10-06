import Witnesses.C2KingAnchorWitness
import Witnesses.PileSwapConsequences

/-! # The king-land orbit probe (wave-22, decide-first)

Decide-first probes for the king-side graded bound through the pile
quotient, before the proof work:

* **The content merge without board emptiness.**  Candidate claim: at
  a `depthsZero` state, the king-commitment landings on any two FREE
  anchors are content-orbit-related by the ONE washed swap — with NO
  board-emptiness premise (the wave-21 first cut used the empty
  board).  Probed at a NONempty `depthsZero` board (DEPTHSHALLOW
  below: pristine `wState` with one card-edge seated on a card seat,
  anchor seats untouched): the probe state's landings on `p₀` and
  `p₃` — the wash composition `(L₁.swapPiles p₀ p₃).setDeal st.deal`
  vs `L₂`, field by field.  If a field fails, the generalization is
  dead and the empty-board premise is load-bearing.
* **The carve boundary.**  The same wash composition at the NOT-emptied
  reachable corner (`ReachCorner.sState`, depths 0..6) must FAIL —
  the depths field cannot match (permuted depths ≠ fixed depths), so
  the emptied-ness flag is exactly where the content merge lives.
* **The six-anchor world's cover.**  At `sState` the king ♠K places on
  every anchor EXCEPT p₀ (the anchored ♠A head), the stack arm is
  dead (king rung 12 ≠ heights 0), and the depths profile is the
  6-anchor world's signature.
-/

/-- Spades for the cartridge. -/
def pS (r : Rank) : Card := ⟨Suit.spade, r⟩
/-- ♣Q — a card seat. -/
def pQ : Card := ⟨Suit.club, Rank.queen⟩
/-- ♦J — a card to seat. -/
def pJ : Card := ⟨Suit.diamond, Rank.jack⟩

/-- A nonempty board over the pristine world: exactly one card-edge,
seated on a CARD seat. -/
def seatBoard : Board := (Board.empty.attach (Sum.inr pQ) pJ).getD Board.empty

/-- DEPTHSHALLOW: the pristine state with the nonempty card-seat
board — depthsZero, board NOT empty, anchored seats all free. -/
def st : State := { KingAnchor.wState with board := seatBoard }

/-- The king-landings of DEPTHSHALLOW on the two anchors. -/
def pL₁ : State := (st.applyDrawTo (pS .king) (Sum.inl Anchor.p0)).getD st
def pL₂ : State := (st.applyDrawTo (pS .king) (Sum.inl Anchor.p3)).getD st

/-- The washed-swap composition the content merge claims to be `pL₂`. -/
def pM : State := (pL₁.swapPiles Anchor.p0 Anchor.p3).setDeal st.deal

#eval st.reachablePos (pS .king)                        -- some 0 (the stock is wState's)
#eval (st.depths Anchor.p6 == 0, st.board.topOf (Sum.inr pQ) == some pJ) -- (true, true): depthsZero, board nonempty
#eval (st.board.topOf (Sum.inl Anchor.p0) == none && st.board.topOf (Sum.inl Anchor.p3) == none) -- true: both free
#eval (pL₁.board.topOf (Sum.inl Anchor.p0) == some (pS .king) &&
       pL₂.board.topOf (Sum.inl Anchor.p3) == some (pS .king)) -- true: both landings carry the king
-- the wash composition, field by field:
#eval Board.enumBase.all (fun b => pM.board.topOf b == pL₂.board.topOf b)
#eval Anchor.all.all (fun a => pM.depths a == pL₂.depths a)
#eval Suit.all.all (fun s => pM.heights s == pL₂.heights s)
#eval (pM.stock.cards == pL₂.stock.cards && pM.stock.cursor == pL₂.stock.cursor)
#eval (Anchor.all.all (fun a => pM.deal.piles a == pL₂.deal.piles a) &&
       pM.deal.stock == pL₂.deal.stock)
#eval pM.drawStep == pL₂.drawStep

-- The carve boundary: the same composition at the reachable corner
-- must fail (the depths field is the blocker; the board conjugation
-- itself survives because both anchors are free).
def rL₁ : State := ReachCorner.sLand Anchor.p1
def rL₂ : State := ReachCorner.sLand Anchor.p2
def rM : State := (rL₁.swapPiles Anchor.p1 Anchor.p2).setDeal ReachCorner.sState.deal

#eval Anchor.all.map (fun a => ReachCorner.sState.depths a) -- [0,1,2,3,4,5,6]: NOT depthsZero
-- the carve boundary (expected (true, false)): board conjugates, depths don't
#eval Board.enumBase.all (fun b => rM.board.topOf b == rL₂.board.topOf b)
#eval Anchor.all.all (fun a => rM.depths a == rL₂.depths a)

-- The six-anchor world's cover data at the reachable corner.
#eval Anchor.all.map (fun a => ReachCorner.sState.canPlace (pS .king) (Sum.inl a))
#eval (ReachCorner.sState.applyDrawStackTo (pS .king)).isNone      -- true: the stack arm is dead
#eval ReachCorner.sState.reachablePos (pS .king)          -- some 0: the Draw commitment fires

-- The pristine corner's own firing data (public re-derivation support).
#eval KingAnchor.wState.reachablePos (pS .king)
#eval Anchor.all.all (fun a =>
  (KingAnchor.wState.applyDrawTo (pS .king) (Sum.inl a)).isSome) -- true x7: all seven fire
