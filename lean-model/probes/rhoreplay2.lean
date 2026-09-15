import Klondike.Initial
import Klondike.TwinQuotient

/-!
# The ρ-replay probe II (L1/O3 part ii — the growing correspondence)

Three validation targets on the w15wfmerge miniature (verbatim cast):

1. **THE GROWTH-RULE MIRROR.**  At a misaligned black stacking of `q`
   (the mirror's rung `M.heights (ρ q).suit` one behind `q`'s rank),
   the mirror plays `pileStack (flip (ρ q))` — the FLIP — and the
   correspondence grows by `τ_{ρ q}`.  `playGrowMir` from the
   BOARD-ONLY swap `wstB` (the ply result's shape:
   `exchange_merge_ply_root` keeps the source's deal/stock) grows ρ
   TWICE (at ♠Q and at ♠K) and wins: the mirror stacks
   [♣Q, ♠J, ♣K, ♠Q, ♠K] where the source stacks [♠Q, ♣J, ♠K, ♣Q, ♣K]
   — no catch-up reordering needed, every source move answered in
   place.

2. **THE MID-EPISODE WORRY-BACK** (the deferral's host-shape check).
   `playWB` worries the freshly stacked ♠Q back onto ♦K mid-episode
   (then re-stacks it); `playWBmir` translates the worry-back through
   the grown correspondence (♣Q onto ♦K — the twin rungs within one,
   so `ρ` itself translates the card) and wins.

3. **THE CROSSING** (the precise residue).  After the growth (8 moves
   in), the source's ♠Q-seat `p0` is empty while the mirror still
   holds ♠Q there, and the mirror's ♣Q-seat `p3` is empty while the
   source still holds ♣Q there: the two boards are NOT related by any
   card relabeling at those two seats.  The stacked-set invariant
   holds throughout; the BOARD correspondence is maintained only
   outside the crossed seat pair — the content the interleaving
   window must still resolve.
-/

/-! ## The cast (w15wfmerge.lean, verbatim) -/

def c_ (s : Suit) (r : Rank) : Card := Card.mk s r

def attachAll : Board -> List (Prod Base Card) -> Board
  | bd, [] => bd
  | bd, (b, c) :: rest => attachAll ((bd.attach b c).getD bd) rest

def dl : List Card :=
  [c_ .spade .queen]
  ++ [c_ .heart .queen, c_ .diamond .ace]
  ++ [c_ .diamond .king, c_ .heart .ten, c_ .diamond .queen]
  ++ [c_ .club .queen, c_ .heart .jack, c_ .spade .jack, c_ .club .jack]
  ++ [c_ .spade .king, c_ .diamond .ten, c_ .diamond .jack, c_ .heart .two, c_ .heart .three]
  ++ [c_ .heart .king, c_ .club .two, c_ .club .three, c_ .club .four, c_ .club .five, c_ .club .six]
  ++ [c_ .club .king, c_ .spade .ace, c_ .spade .two, c_ .spade .three, c_ .spade .four, c_ .spade .five, c_ .spade .six]
  ++ [c_ .diamond .two, c_ .diamond .three, c_ .diamond .four, c_ .diamond .five, c_ .diamond .six,
      c_ .diamond .seven, c_ .diamond .eight, c_ .diamond .nine,
      c_ .heart .ace, c_ .heart .four, c_ .heart .five, c_ .heart .six,
      c_ .heart .seven, c_ .heart .eight, c_ .heart .nine,
      c_ .spade .seven, c_ .spade .eight, c_ .spade .nine, c_ .spade .ten,
      c_ .club .ace, c_ .club .seven, c_ .club .eight, c_ .club .nine, c_ .club .ten]

def hts : Suit -> Nat := fun s =>
  match s with
  | .diamond => 9 | .heart => 9 | .spade => 10 | .club => 10

def bW : Board := attachAll Board.empty
  [ (Sum.inl Anchor.p2, c_ .diamond .king)
  , (Sum.inr (c_ .diamond .king), c_ .heart .ten)
  , (Sum.inr (c_ .heart .ten), c_ .diamond .queen)
  , (Sum.inr (c_ .diamond .queen), c_ .spade .jack)
  , (Sum.inr (c_ .spade .jack), c_ .diamond .ten)
  , (Sum.inl Anchor.p1, c_ .heart .queen)
  , (Sum.inr (c_ .heart .queen), c_ .club .jack)
  , (Sum.inl Anchor.p0, c_ .spade .queen)
  , (Sum.inl Anchor.p3, c_ .club .queen)
  , (Sum.inr (c_ .club .queen), c_ .diamond .jack)
  , (Sum.inl Anchor.p4, c_ .spade .king)
  , (Sum.inr (c_ .spade .queen), c_ .heart .jack)
  , (Sum.inl Anchor.p5, c_ .heart .king)
  , (Sum.inl Anchor.p6, c_ .club .king) ]

def wst : State := State.mk (Deal.ofList dl) bW hts (fun _ => 0) (Cycle.mk [] 0) 1

def tQ : Card := c_ .diamond .queen
def tQ2 : Card := c_ .heart .queen
def zS : Card := c_ .spade .jack
def zC : Card := c_ .club .jack
def cH : Card := c_ .heart .ten
def xD : Card := c_ .diamond .king
def bB : Card := c_ .diamond .ten

/-- The BOARD-ONLY twin swap at the cargo z — the ply result's shape
(`exchange_merge_ply_root`: the board is `mapByTwin z`, every other
field the source's). -/
def wstB : State := { wst with board := wst.board.mapByTwin zS }

/-! ## (1) the growth-rule mirror: flip at the misaligned moments -/

def playVar : List Move :=
  [ Move.pilePile cH (Sum.inr zC)
  , Move.pileStack bB
  , Move.pileStack zS                       -- pair move 1 (z)
  , Move.pileStack (c_ .diamond .jack)      -- mid (ortho)
  , Move.pileStack tQ                       -- mid (ortho)
  , Move.pileStack cH                        -- mid (ortho)
  , Move.pileStack (c_ .heart .jack)        -- mid (ortho)
  , Move.pileStack (c_ .spade .queen)       -- mid — BLACK, growth trigger
  , Move.pileStack zC                       -- pair move 2 (z')
  , Move.pileStack xD
  , Move.pileStack tQ2
  , Move.pileStack (c_ .heart .king)
  , Move.pileStack (c_ .spade .king)
  , Move.pileStack (c_ .club .queen)
  , Move.pileStack (c_ .club .king) ]

/-- The growth-rule mirror: [♣Q, ♠J, ♣K, ♠Q, ♠K] answers
[♠Q, ♣J, ♠K, ♣Q, ♣K] — two growths (at ♠Q, at ♠K), no reordering. -/
def playGrowMir : List Move :=
  [ Move.pilePile cH (Sum.inr zS)          -- the translated merge
  , Move.pileStack bB
  , Move.pileStack zC                       -- FLIP of pair move 1
  , Move.pileStack (c_ .diamond .jack)
  , Move.pileStack tQ
  , Move.pileStack cH
  , Move.pileStack (c_ .heart .jack)
  , Move.pileStack (c_ .club .queen)        -- GROWTH 1: flip of ρ₀(♠Q)
  , Move.pileStack zS                       -- ρ₁(z') — pair move 2
  , Move.pileStack xD
  , Move.pileStack tQ2
  , Move.pileStack (c_ .heart .king)
  , Move.pileStack (c_ .club .king)          -- GROWTH 2: flip of ρ₁(♠K)
  , Move.pileStack (c_ .spade .queen)        -- ρ₂(♣Q)
  , Move.pileStack (c_ .spade .king) ]      -- ρ₂(♣K)

/-! ## (2) the mid-episode worry-back -/

/-- The source with a mid-episode worry-back: after stacking ♠Q (the
growth trigger), worry it back onto ♦K, then re-stack it and finish. -/
def playWB : List Move :=
  [ Move.pilePile cH (Sum.inr zC)
  , Move.pileStack bB
  , Move.pileStack zS
  , Move.pileStack (c_ .diamond .jack)
  , Move.pileStack tQ
  , Move.pileStack cH
  , Move.pileStack (c_ .heart .jack)
  , Move.pileStack (c_ .spade .queen)       -- growth trigger
  , Move.stackPile (c_ .spade .queen) (Sum.inr xD)   -- the worry-back
  , Move.pileStack (c_ .spade .queen)       -- the re-stack
  , Move.pileStack zC
  , Move.pileStack xD
  , Move.pileStack tQ2
  , Move.pileStack (c_ .heart .king)
  , Move.pileStack (c_ .spade .king)
  , Move.pileStack (c_ .club .queen)
  , Move.pileStack (c_ .club .king) ]

/-- The mirror: the worry-back translates through the grown
correspondence — ♣Q (= ρ₁(♠Q)) back onto ♦K — no growth, no
reordering. -/
def playWBmir : List Move :=
  [ Move.pilePile cH (Sum.inr zS)
  , Move.pileStack bB
  , Move.pileStack zC
  , Move.pileStack (c_ .diamond .jack)
  , Move.pileStack tQ
  , Move.pileStack cH
  , Move.pileStack (c_ .heart .jack)
  , Move.pileStack (c_ .club .queen)        -- GROWTH
  , Move.stackPile (c_ .club .queen) (Sum.inr xD)   -- the translated worry-back
  , Move.pileStack (c_ .club .queen)        -- the re-stack
  , Move.pileStack zS
  , Move.pileStack xD
  , Move.pileStack tQ2
  , Move.pileStack (c_ .heart .king)
  , Move.pileStack (c_ .club .king)          -- GROWTH 2
  , Move.pileStack (c_ .spade .queen)
  , Move.pileStack (c_ .spade .king) ]

/-- The first failing move's index (none = the whole play runs). -/
def firstFail : State → List Move → Nat → Option Nat
  | _, [], _ => none
  | S, m :: ms, i =>
      match S.apply m with
      | none => some i
      | some S' => firstFail S' ms (i + 1)

#eval Option.map State.isWin (wst.run playVar)
#eval firstFail wst playVar 0
#eval Option.map State.isWin (wstB.run playGrowMir)
#eval firstFail wstB playGrowMir 0
#eval Option.map State.isWin (wst.run playWB)
#eval firstFail wst playWB 0
#eval Option.map State.isWin (wstB.run playWBmir)
#eval firstFail wstB playWBmir 0
#eval (wst.run playWB).map (fun W => Suit.all.map (fun s => W.heights s))
#eval (wstB.run playWBmir).map (fun W => Suit.all.map (fun s => W.heights s))

/-! ## (3) the crossing, after the growth (8 moves in) -/

-- The source after 8 moves: p0 (♠Q's seat) is EMPTY, ♣Q still at p3.
#eval (wst.run (playVar.take 8)).map (fun S =>
  ((S.board.topOf (Sum.inl Anchor.p0)).map (fun c => (c.suit, c.rank)),
   (S.board.topOf (Sum.inl Anchor.p3)).map (fun c => (c.suit, c.rank))))

-- The mirror after 8 moves: ♠Q STILL at p0, p3 (♣Q's seat) EMPTY —
-- the crossed pair: no card relabeling relates the two boards.
#eval (wstB.run (playGrowMir.take 8)).map (fun S =>
  ((S.board.topOf (Sum.inl Anchor.p0)).map (fun c => (c.suit, c.rank)),
   (S.board.topOf (Sum.inl Anchor.p3)).map (fun c => (c.suit, c.rank))))

/-! ## (4) the on-suit deckStack probe (Residual 2's decision) -/

-- A variant with a live stock: the twin-suit stock card ♠7 on top,
-- the spade rung dropped to its exact rank (6) so it deckStacks.
def wst2 : State := State.mk (Deal.ofList dl) bW
  (fun s => match s with | .spade => 6 | s' => hts s')
  (fun _ => 0) (Cycle.mk [c_ .spade .seven] 1) 1

-- The mirror (the board-only twin swap at z, heights unchanged).
def wst2B : State := { wst2 with board := wst2.board.mapByTwin zS }

-- The misaligned mirror (one behind on the spade rung).
def wst2B' : State :=
  { wst2B with heights := fun s => match s with | .spade => 5 | s' => hts s' }

-- (a) the source's on-suit deckStack fires.
#eval (wst2.apply (Move.deckStack (c_ .spade .seven))).isSome
-- (b) the ALIGNED mirror's SAME-CARD response fires (the rungs pinned
--     equal by the stacked-set iff - the non-pair card is rho-fixed).
#eval (wst2B.apply (Move.deckStack (c_ .spade .seven))).isSome
-- (c) the MISALIGNED mirror cannot respond in kind (the rung behind):
--     only the run-level deferral or the parking remain.
#eval (wst2B'.apply (Move.deckStack (c_ .spade .seven))).isSome
-- (d) the parking response's legality: with a base-compatible stock card
--     (a nine, sitting on a ten), the misaligned mirror CAN park it
--     (deckPile - no rung read; the anchor variant needs a king).
def wst3 : State := State.mk (Deal.ofList dl) bW
  (fun s => match s with | .spade => 8 | s' => hts s')
  (fun _ => 0) (Cycle.mk [c_ .spade .nine] 1) 1
def wst3B' : State := State.mk (Deal.ofList dl) (wst3.board.mapByTwin zS)
  (fun s => match s with | .spade => 7 | s' => hts s')
  (fun _ => 0) (Cycle.mk [c_ .spade .nine] 1) 1
#eval (wst3.apply (Move.deckStack (c_ .spade .nine))).isSome
#eval (wst3B'.apply (Move.deckStack (c_ .spade .nine))).isSome
#eval (wst3B'.apply (Move.deckPile (c_ .spade .nine) (Sum.inr bB))).isSome
