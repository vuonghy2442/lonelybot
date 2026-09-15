import Klondike.Move

/-! NOTE: `Klondike.TwinExchange`'s olean was absent during this session
(a parallel rebuild); the two definitions below are VERBATIM copies from
TwinExchange.lean:89-137 (`Board.exchangeTwin_inj`, `Board.exchangeTwin`,
`State.exchangeTwinCargo`) so the probe is self-contained.  They depend
only on `Base.swapTwin` / `Card.swapTwin` (Board.lean/Basic.lean, built).
Re-verify against the real import once TwinExchange builds. -/

/-- Injectivity for the two-slot value swap (TwinExchange.lean:89). -/
theorem Board.exchangeTwin_inj (bd : Board) (t : Card) :
    forall (b1 b2 : Base) (c : Card), bd.topOf (b1.swapTwin t) = some c ->
      bd.topOf (b2.swapTwin t) = some c -> b1 = b2 := by
  intro b1 b2 c h1 h2
  have hb : b1.swapTwin t = b2.swapTwin t := bd.inj _ _ c h1 h2
  have hb2 := congrArg (fun b => b.swapTwin t) hb
  rw [Base.swapTwin_swapTwin, Base.swapTwin_swapTwin] at hb2
  exact hb2

/-- The both-cargo exchange at the board level (TwinExchange.lean:104). -/
def Board.exchangeTwin (bd : Board) (t : Card) : Board where
  topOf := fun b => bd.topOf (b.swapTwin t)
  inj := Board.exchangeTwin_inj bd t

/-- The both-cargo exchange at the state level (TwinExchange.lean:136). -/
def State.exchangeTwinCargo (st : State) (t : Card) : State :=
  { st with board := st.board.exchangeTwin t }

/-!
#w15 MERGE probe (refute-first, 2026-09-14) -- does the MERGE break
`State.solvable_cargoTwin_exchange` (TwinExchange.lean, ~line 991)?

The merge shape: during a winning play from st (cargo z on twin t, cargo
z' on t'), a `pilePile c (inr d)` whose run above c CONTAINS t (so the
cargo z and z's stack ride the twin), landing on the OTHER cargo's
stack (d = z' or d in aboveOf z').  The move is legal in st but
SELF-LANDING (illegal) in st.exchangeTwinCargo t, where z' rides t.

Findings (all #eval-verified in this file):
(1a) Concrete: the merge fires in st and dies (self-landing) in stx.
(1b) Concrete: a t-passing run landing OFF both cargo stacks is legal
     in BOTH games (the user's correction, confirmed).
(2)  A crafted family-(a) witness (WF-ness deliberately uncertain -- the
     scaffolded theorem carries NO st.WF premise):
       st  : wins in exactly 3 moves, and the merge is load-bearing
             (legalMoves st = [the merge, pileStack HK]: without the
             merge the buried diamond king DK is never exposed, so
             diamond is stuck at 12);
       stx : FROZEN -- its only legal move is pileStack HK, and the
             successor has NO legal moves at all; the reachable space
             has 2 states, neither winning: exhaustively unsolvable
             (bounded-verified up to depth 14, and closed under moves).
     The obstruction is exactly the merge: c's run passes t, and the
     only landing (z' = CJ) is blocked by self-landing once the
     exchange has z' riding t (the mirror merge onto z is blocked by
     the crafted blocker B on z).  The witness is non-WF (empty deal,
     crafted non-fitting edges, heights past on-board cards: heart 12
     with HQ/H10/HJ/... on the board, etc.), so it refutes the claim AS
     SCAFFOLDED and confirms the planned `+hwf` repair; the WF-strength
     question stays open (see the final report).
-/

/-! ## Small kit (printing + board building) -/

def rankOfIdx : Nat -> Rank
  | 0 => .ace | 1 => .two | 2 => .three | 3 => .four | 4 => .five | 5 => .six
  | 6 => .seven | 7 => .eight | 8 => .nine | 9 => .ten | 10 => .jack | 11 => .queen
  | _ => .king

def rankStr (r : Rank) : String :=
  match r with
  | .ace => "A" | .two => "2" | .three => "3" | .four => "4" | .five => "5"
  | .six => "6" | .seven => "7" | .eight => "8" | .nine => "9" | .ten => "10"
  | .jack => "J" | .queen => "Q" | .king => "K"

def cardStr (c : Card) : String :=
  (if c.suit = Suit.heart then "H"
   else if c.suit = Suit.diamond then "D"
   else if c.suit = Suit.spade then "S"
   else "C") ++ rankStr c.rank

def anchorStr (a : Anchor) : String :=
  match a with
  | .p0 => "p0" | .p1 => "p1" | .p2 => "p2" | .p3 => "p3"
  | .p4 => "p4" | .p5 => "p5" | .p6 => "p6"

def baseStr (b : Base) : String :=
  match b with
  | Sum.inl a => anchorStr a
  | Sum.inr c => cardStr c

/-- Chain-attach; a failed attach falls back to the previous board
(none fail here -- the premise evals below double as verification). -/
def attachAll : Board -> List (Prod Base Card) -> Board
  | bd, [] => bd
  | bd, (b, c) :: rest => attachAll ((bd.attach b c).getD bd) rest

def moveStr : Move -> String
  | .draw => "draw"
  | .reveal c => "reveal " ++ cardStr c
  | .deckPile c b => "deckPile " ++ cardStr c ++ " " ++ baseStr b
  | .deckStack c => "deckStack " ++ cardStr c
  | .pileStack c => "pileStack " ++ cardStr c
  | .stackPile c b => "stackPile " ++ cardStr c ++ " " ++ baseStr b
  | .pilePile c b => "pilePile " ++ cardStr c ++ " " ++ baseStr b

/-! ## The cast -/

def tQ  : Card := Card.mk Suit.diamond Rank.queen   -- t   (the twin seat)
def tQ2 : Card := Card.mk Suit.heart Rank.queen     -- t'  (= t.flipSuit)
def zS  : Card := Card.mk Suit.spade Rank.jack       -- z   (cargo on t)
def zC  : Card := Card.mk Suit.club Rank.jack        -- z'  (= z.flipSuit, cargo on t')
def cH  : Card := Card.mk Suit.heart Rank.ten        -- c   (merge mover; run above c passes t)
def xD  : Card := Card.mk Suit.diamond Rank.king     -- X   (under c; exposed BY the merge; diamond 12->13)
def bH3 : Card := Card.mk Suit.heart Rank.three      -- B   (crafted on z; blocks z's seat in stx)
def d7  : Card := Card.mk Suit.heart Rank.seven      -- kH's host (NOT an anchor: stacking kH must not free one)
def kH  : Card := Card.mk Suit.heart Rank.king       -- the free heart climber (12->13)
def stn1 : Card := Card.mk Suit.heart Rank.jack      -- anchor stones: keep ALL 7 anchors occupied so
def stn2 : Card := Card.mk Suit.heart Rank.four      --   no king can be pulled from a completed foundation
def stn3 : Card := Card.mk Suit.heart Rank.five      --   (spade/club are at 13; their tops are kings; a free
def stn4 : Card := Card.mk Suit.heart Rank.six       --   anchor + a king = a landing pad = the king escape)

#eval (tQ2 == tQ.flipSuit, zC == zS.flipSuit)    -- (true, true)
#eval (canSitOn zS tQ, canSitOn zC tQ2)          -- (true, true)

/-! ## The witness state (family (a): crafted, non-WF) -/

def hts : Suit -> Nat := fun s =>
  match s.color with
  | Color.red => 12      -- heart 12, diamond 12
  | Color.black => 13    -- spade 13, club 13

def d0 : Deal := Deal.mk (fun _ => []) []

def bW : Board := attachAll Board.empty
  [ (Sum.inl Anchor.p0, xD), (Sum.inr xD, cH), (Sum.inr cH, tQ), (Sum.inr tQ, zS), (Sum.inr zS, bH3)
  , (Sum.inl Anchor.p1, tQ2), (Sum.inr tQ2, zC)
  , (Sum.inl Anchor.p2, d7), (Sum.inr d7, kH)
  , (Sum.inl Anchor.p3, stn1), (Sum.inl Anchor.p4, stn2)
  , (Sum.inl Anchor.p5, stn3), (Sum.inl Anchor.p6, stn4) ]

def w15st : State := State.mk d0 bW hts (fun _ => 0) (Cycle.mk [] 0) 1
def w15stx : State := w15st.exchangeTwinCargo tQ

-- the full record of st: occupied seats (base <- card), heights, deal/stock/depths
#eval String.intercalate "; " (Board.enumBase.filterMap (fun b =>
  (w15st.board.topOf b).map (fun c => baseStr b ++ " <- " ++ cardStr c)))
#eval Suit.all.map (fun s => (s, w15st.heights s))
#eval (Anchor.all.map (fun a => (w15st.deal.piles a).length),
       Anchor.all.map (fun a => w15st.depths a),
       w15st.stock.cards.length, w15st.stock.cursor, w15st.drawStep)

-- the exchange swapped exactly the two cargos
#eval (w15st.board.bottomOf zS == some (Sum.inr tQ),
       w15st.board.bottomOf zC == some (Sum.inr tQ2))
#eval (w15stx.board.bottomOf zC == some (Sum.inr tQ),
       w15stx.board.bottomOf zS == some (Sum.inr tQ2))

/-! ## The claim's premises, all executable, on st -/

#eval (w15st.isVis tQ, w15st.isVis tQ2)
#eval (w15st.board.bottomOf zS == some (Sum.inr tQ),
       w15st.board.bottomOf zC == some (Sum.inr tQ2))
#eval (canSitOn zS tQ, canSitOn zC tQ2)
#eval (!(w15st.board.aboveOf zS).contains tQ && !(w15st.board.aboveOf zS).contains tQ2,
       !(w15st.board.aboveOf zC).contains tQ && !(w15st.board.aboveOf zC).contains tQ2)

/-! ## (1a) The MERGE: legal in st, self-landing (illegal) in stx -/

#eval (w15st.board.aboveOf cH).contains tQ     -- true : the run above c passes t (z and B ride)
#eval (w15st.apply (Move.pilePile cH (Sum.inr zC))).isSome   -- true  : LEGAL in st  (the merge)
#eval (w15stx.apply (Move.pilePile cH (Sum.inr zC))).isSome  -- false : ILLEGAL in stx
#eval (w15stx.board.aboveOf cH).contains zC    -- true  : the cause -- z' rides t in stx -> self-landing

-- st's winning play (3 moves, merge first): expose DK, stack DK, stack HK
#eval Option.map State.isWin
  (w15st.run [Move.pilePile cH (Sum.inr zC), Move.pileStack xD, Move.pileStack kH])  -- some true

/-! ## (1b) A t-passing run landing OFF both cargo stacks: legal in BOTH -/

def mM : Card := Card.mk Suit.spade Rank.ten    -- the mover (t sits on it)
def hJ : Card := Card.mk Suit.heart Rank.jack   -- the off-cargo landing (a red jack; neither z=SJ nor z'=CJ)

def bB : Board := attachAll Board.empty
  [ (Sum.inl Anchor.p0, mM), (Sum.inr mM, tQ), (Sum.inr tQ, zS)
  , (Sum.inl Anchor.p1, tQ2), (Sum.inr tQ2, zC), (Sum.inl Anchor.p2, hJ) ]

def w15bst : State := State.mk d0 bB hts (fun _ => 0) (Cycle.mk [] 0) 1
def w15bstx : State := w15bst.exchangeTwinCargo tQ

#eval (w15bst.board.aboveOf mM).contains tQ                    -- true : t-passing
#eval (w15bst.apply (Move.pilePile mM (Sum.inr hJ))).isSome    -- true : legal in st
#eval (w15bstx.apply (Move.pilePile mM (Sum.inr hJ))).isSome   -- true : legal in stx too

/-! ## The bounded searcher -/

/-- All legal moves, exhaustive per kind.  `draw` on an empty stock is a
state identity (cursor 0 -> 0 on no cards), so it is omitted when the
stock is empty -- plays stay comparable, shortened by the no-ops. -/
def legalMoves (st : State) : List Move :=
  let vis : List Card := Board.enumBase.flatMap (fun b =>
    match st.board.topOf b with | some c => [c] | none => [])
  let cands : List Move :=
    (if st.stock.cards == [] then [] else [Move.draw])
    ++ vis.map (fun c => Move.reveal c)
    ++ vis.map (fun c => Move.pileStack c)
    ++ (match st.stock.prev with
        | some p => (Move.deckStack p :: Board.enumBase.map (fun b => Move.deckPile p b))
        | none => [])
    ++ Suit.all.flatMap (fun s =>
        if 0 < st.heights s then
          Board.enumBase.map (fun b => Move.stackPile (Card.mk s (rankOfIdx (st.heights s - 1))) b)
        else [])
    ++ vis.flatMap (fun c => Board.enumBase.map (fun b => Move.pilePile c b))
  cands.filter (fun m => (st.apply m).isSome)

def succs (st : State) : List State :=
  (legalMoves st).flatMap (fun m => match st.apply m with
    | some s' => [s'] | none => [])

/-- The mission's naive bounded searcher: winIn k st = exists a play of
length <= k from st to a win. -/
def winIn : Nat -> State -> Bool
  | 0, st => st.isWin
  | k + 1, st =>
      st.isWin ||
        (legalMoves st).any (fun m =>
          match st.apply m with
          | some s' => winIn k s'
          | none => false)

/-- A canonical key for dedup (heights, depths, stock, drawStep, deal,
board image; the deal is move-invariant so the key is complete here). -/
def stateKey (st : State) : String :=
  String.intercalate "," (Suit.all.map (fun s => toString (st.heights s))) ++ "|" ++
  String.intercalate "," (Anchor.all.map (fun a => toString (st.depths a))) ++ "|" ++
  toString st.stock.cursor ++ "/" ++ String.intercalate ";" (st.stock.cards.map cardStr) ++ "|" ++
  toString st.drawStep ++ "|" ++
  String.intercalate ";" (Anchor.all.flatMap (fun a => (st.deal.piles a).map cardStr)) ++ "|" ++
  String.intercalate ";" (Board.enumBase.map (fun b =>
    match st.board.topOf b with | none => "-" | some c => cardStr c))

/-- The dedup'd BFS with the same semantics (first visit = maximal
remaining budget, so global visited is sound for "play of length <= k"). -/
def bfsWin : Nat -> List State -> List String -> Bool
  | 0, front, _ => front.any (fun s => s.isWin)
  | k + 1, front, vis =>
      front.any (fun s => s.isWin) ||
        let next := front.flatMap succs
        let news := next.filter (fun s => !(vis.contains (stateKey s)))
        bfsWin k news (news.foldl (fun acc s => stateKey s :: acc) vis)

def winBFS (k : Nat) (st : State) : Bool :=
  bfsWin k [st] [stateKey st]

/-! ## The DIVERGENCE -/

#eval (winIn 2 w15st, winIn 3 w15st)            -- (false, true)  : st wins in exactly 3
#eval (winIn 2 w15stx, winIn 3 w15stx)          -- (false, false)
#eval (winBFS 14 w15st, winBFS 6 w15stx, winBFS 10 w15stx, winBFS 14 w15stx)
                                                -- (true, false, false, false)

/-! ## Why stx is dead: its entire reachable space, by hand -/

#eval String.intercalate "; " ((legalMoves w15st).map moveStr)
-- pileStack HK; pilePile H10 CJ      (the merge + the heart stack)
#eval String.intercalate "; " ((legalMoves w15stx).map moveStr)
-- pileStack HK                        (the merge died; the mirror merge died: SJ carries B)
def w15stx1 : State := (w15stx.apply (Move.pileStack kH)).getD w15stx
#eval String.intercalate "; " ((legalMoves w15stx1).map moveStr)
-- (empty)                             (frozen: no legal moves at all)
#eval (w15stx.isWin, w15stx1.isWin)              -- (false, false)

-- deeper bounds: stx's reachable space is the 2 states above (the second
-- has NO legal moves), so no bound can ever change the verdict
#eval (winBFS 20 w15stx, winBFS 24 w15stx)       -- (false, false)

-- the merge is load-bearing: after the non-merge first move, the ONLY
-- legal move is the merge (and it is still needed to expose DK)
def w15st2 : State := (w15st.apply (Move.pileStack kH)).getD w15st
#eval String.intercalate "; " ((legalMoves w15st2).map moveStr)
-- pilePile H10 CJ
#eval winBFS 12 w15st2                           -- true (via the merge + pileStack DK)
