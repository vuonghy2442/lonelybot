import Klondike.Initial
import Klondike.TwinQuotient

/-!
# w15 WF-MERGE probe (the gate for the two [H] bridges, 2026-09-14)

**FINDING: NO DIVERGENCE — the first WF candidate is not a witness.**
Both `wst` and `wstx` are WF (all 11 conjuncts, executable check
below) and licensed; the merge is load-bearing for st's exhibited
15-move win (the run [♥10, ♦Q, ♠J, ♦10] onto ♣J exposes the ♦K the
diamond climb needs); the merge is SELF-LANDING in stx and the mirror
landing is blocked by B = ♦10 — but stx WINS ANYWAY (the 15-move play
below): **founds_gone forces B to be live** (every on-board card sits
at/above its suit's height, hence is eventually stackable), B stacks
off (diamond 9 -> 10), the mirror merge opens, and the threads rejoin.

The w15merge witness family is STRUCTURALLY DEAD at WF — all three of
its blockades were WF-forbidden: dead blockers (foundation-passed
ranks, killed by founds_gone), non-king anchor stones (killed by
board_edges' anchor clause), and crafted non-fitting edges (killed by
board_edges' fit/deal-adjacency disjunct).  The remaining candidate
family: CIRCULAR blocker dependencies (a blocker whose stacking rung
is only reachable through the cards it blocks).  Evidence now leans
toward the bridges being TRUE at WF — and the exhibited stx play IS
the piecewise-bookkeeping argument in miniature (clear the blocker,
the mirror opens, the threads merge).

The probe (the cast re-crafted under the FULL WF constraint):

- a real deal (`Deal.ofList` of the 52, triangular), the deal-adjacency
  chain [♦K, ♥10, ♦Q] in pile p2 (X < c < t, the only deal-adjacent
  edges — everything else is fit or anchor-head/king);
- heights (♦9, ♥9, ♠10, ♣10): every visible card sits at/above its
  suit's height (founds_gone), the below-height cards are neither
  visible, in the (empty) cycle, nor hidden (depths 0);
- the blocker B = ♦10 rides z = ♠J (fit): in the exchanged state z
  rides t', so the mirror landing (c's run onto z) is blocked by B,
  while the direct landing on z' self-lands — the run [♥10, ♦Q, ♠J's
  side] has NO legal landing in stx.

Cast: t = ♦Q, t' = ♥Q, z = ♠J, z' = ♣J, c = ♥10, X = ♦K (buried,
exposed BY the merge — the diamond climb needs it), B = ♦10.
-/

/-! ## Small kit (from w15merge.lean, verbatim) -/

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

/-! ## The WF checker (all 11 conjuncts, executable) -/

def consec (l : List Card) (d c : Card) : Bool :=
  match l with
  | x :: y :: rest => (x == d && y == c) || consec (y :: rest) d c
  | _ => false

/-- board_edges' clause for the edge c -> b, at state st. -/
def edgeOK (st : State) (b : Base) (c : Card) : Bool :=
  match b with
  | Sum.inl a => c.rank == Rank.king || (st.deal.piles a).head? == some c
  | Sum.inr d =>
      (Anchor.all.any (fun a => consec (st.deal.piles a) d c) &&
        (Anchor.all.any (fun a' => st.topHidden a' == some d) ||
          (st.board.bottomOf d).isSome)) ||
      ((st.board.bottomOf d).isSome && canSitOn c d)

def nodupB (l : List Card) : Bool := l.all (fun x => l.count x == 1)

def wfCheck (st : State) : Bool :=
  Anchor.all.all (fun a => (st.deal.piles a).length == a.toIdx + 1) &&
  st.deal.stock.length == 24 &&
  nodupB ((Anchor.all.flatMap st.deal.piles) ++ st.deal.stock) &&
  Anchor.all.all (fun a => decide (st.depths a <= (st.deal.piles a).length)) &&  Board.enumBase.all (fun b =>
    match st.board.topOf b with
    | none => true
    | some c => (st.board.bottomOf c == some b) && edgeOK st b c) &&
  Card.universe.all (fun c =>
    !(st.isVis c) || st.stock.posOf c == none) &&
  Card.universe.all (fun c =>
    !(st.onFound c) || st.stock.posOf c == none) &&
  Card.universe.all (fun c =>
    !decide (c.rank.toIdx < st.heights c.suit) ||
    (!(st.isVis c) && st.stock.posOf c == none &&
      Anchor.all.all (fun a => !((st.hidden a).contains c)))) &&
  Card.universe.all (fun c =>
    !(st.isVis c) || Anchor.all.all (fun a => !((st.hidden a).contains c))) &&
  Suit.all.all (fun s => decide (st.heights s <= 13)) &&
  decide (st.stock.cursor <= st.stock.cards.length) &&
  0 < st.drawStep &&
  nodupB st.stock.cards &&
  st.stock.cards.all (fun c => st.deal.stock.contains c)

/-! ## The state -/

def c_ (s : Suit) (r : Rank) : Card := Card.mk s r

/-- The deal: 52 slots, triangular split; the structural constraints:
p1 head = ♥Q (t'), p2 = [♦K, ♥10, ♦Q] (X < c < t, consecutive). -/
def dl : List Card :=
  [c_ .spade .queen]                                          -- p0: ♠Q (head, anchor p0)
  ++ [c_ .heart .queen, c_ .diamond .ace]                      -- p1: ♥Q (head, anchor p1) + pad
  ++ [c_ .diamond .king, c_ .heart .ten, c_ .diamond .queen]   -- p2: ♦K (head, anchor) < ♥10 < ♦Q
  ++ [c_ .club .queen, c_ .heart .jack, c_ .spade .jack, c_ .club .jack]  -- p3: ♣Q (head) + parked sitters
  ++ [c_ .spade .king, c_ .diamond .ten, c_ .diamond .jack, c_ .heart .two, c_ .heart .three]  -- p4: ♠K (head)
  ++ [c_ .heart .king, c_ .club .two, c_ .club .three, c_ .club .four, c_ .club .five, c_ .club .six]  -- p5: ♥K (head)
  ++ [c_ .club .king, c_ .spade .ace, c_ .spade .two, c_ .spade .three, c_ .spade .four, c_ .spade .five, c_ .spade .six]  -- p6: ♣K (head)
  ++ [c_ .diamond .two, c_ .diamond .three, c_ .diamond .four, c_ .diamond .five, c_ .diamond .six,
      c_ .diamond .seven, c_ .diamond .eight, c_ .diamond .nine,             -- stock (24)
      c_ .heart .ace, c_ .heart .four, c_ .heart .five, c_ .heart .six,
      c_ .heart .seven, c_ .heart .eight, c_ .heart .nine,
      c_ .spade .seven, c_ .spade .eight, c_ .spade .nine, c_ .spade .ten,
      c_ .club .ace, c_ .club .seven, c_ .club .eight, c_ .club .nine, c_ .club .ten]

#eval dl.length                                    -- 52
#eval (Deal.ofList dl).piles Anchor.p2 |>.map cardStr   -- [♦K, ♥10, ♦Q]
#eval (Deal.ofList dl).piles Anchor.p1 |>.map cardStr   -- [♥Q, ♦A]

def hts : Suit -> Nat := fun s =>
  match s with
  | .diamond => 9 | .heart => 9 | .spade => 10 | .club => 10

def bW : Board := attachAll Board.empty
  [ (Sum.inl Anchor.p2, c_ .diamond .king)        -- X = ♦K on p2 (king, p2's head)
  , (Sum.inr (c_ .diamond .king), c_ .heart .ten)     -- c = ♥10 on X (deal-adj: p2 consecutive)
  , (Sum.inr (c_ .heart .ten), c_ .diamond .queen)    -- t = ♦Q on c (deal-adj)
  , (Sum.inr (c_ .diamond .queen), c_ .spade .jack)   -- z = ♠J on t (fit)
  , (Sum.inr (c_ .spade .jack), c_ .diamond .ten)     -- B = ♦10 on z (fit; blocks the mirror)
  , (Sum.inl Anchor.p1, c_ .heart .queen)             -- t' = ♥Q on p1 (p1's head)
  , (Sum.inr (c_ .heart .queen), c_ .club .jack)     -- z' = ♣J on t' (fit)
  , (Sum.inl Anchor.p0, c_ .spade .queen)             -- ♠Q on p0 (head)
  , (Sum.inl Anchor.p3, c_ .club .queen)              -- ♣Q on p3 (head)
  , (Sum.inr (c_ .club .queen), c_ .diamond .jack)    -- ♦J on ♣Q (fit)
  , (Sum.inl Anchor.p4, c_ .spade .king)              -- ♠K on p4 (king)
  , (Sum.inr (c_ .spade .queen), c_ .heart .jack)     -- ♥J on ♠Q (fit; exposes ♠Q)
  , (Sum.inl Anchor.p5, c_ .heart .king)              -- ♥K on p5 (king)
  , (Sum.inl Anchor.p6, c_ .club .king) ]             -- ♣K on p6 (king)

def wst : State := State.mk (Deal.ofList dl) bW hts (fun _ => 0) (Cycle.mk [] 0) 1
def wstx : State := wst.exchangeTwinCargo (c_ .diamond .queen)

-- THE WF CHECK
#eval wfCheck wst
#eval wfCheck wstx

-- diagnostics: which conjunct / which move
#eval (Anchor.all.all (fun a => (wst.deal.piles a).length == a.toIdx + 1),
       wst.deal.stock.length == 24,
       nodupB ((Anchor.all.flatMap wst.deal.piles) ++ wst.deal.stock))
#eval Board.enumBase.all (fun b =>
  match wst.board.topOf b with
  | none => true
  | some c => (wst.board.bottomOf c == some b) && edgeOK wst b c)
#eval Board.enumBase.filterMap (fun b =>
  match wst.board.topOf b with
  | none => none
  | some c => if (wst.board.bottomOf c == some b) && edgeOK wst b c then none
    else some (baseStr b ++ " <- " ++ cardStr c))
#eval (Card.universe.filter (fun c =>
  decide (c.rank.toIdx < wst.heights c.suit) &&
    (wst.isVis c || (wst.stock.posOf c).isSome ||
      Anchor.all.any (fun a => (wst.hidden a).contains c)))).map cardStr

def s1 : State := (wst.apply (Move.pilePile (c_ .heart .ten) (Sum.inr (c_ .club .jack)))).getD wst
def s2 : State := (s1.apply (Move.pileStack (c_ .diamond .ten))).getD s1
def s3 : State := (s2.apply (Move.pileStack (c_ .spade .jack))).getD s2
def s4 : State := (s3.apply (Move.pileStack (c_ .diamond .jack))).getD s3
#eval ((wst.apply (Move.pilePile (c_ .heart .ten) (Sum.inr (c_ .club .jack)))).isSome,
       (s1.apply (Move.pileStack (c_ .diamond .ten))).isSome,
       (s2.apply (Move.pileStack (c_ .spade .jack))).isSome,
       (s3.apply (Move.pileStack (c_ .diamond .jack))).isSome)

-- the state's shape
#eval String.intercalate "; " (Board.enumBase.filterMap (fun b =>
  (wst.board.topOf b).map (fun c => baseStr b ++ " <- " ++ cardStr c)))
#eval Suit.all.map (fun s => (s, wst.heights s))

/-! ## The license, the merge, the divergence -/

def tQ : Card := c_ .diamond .queen
def tQ2 : Card := c_ .heart .queen
def zS : Card := c_ .spade .jack
def zC : Card := c_ .club .jack
def cH : Card := c_ .heart .ten
def xD : Card := c_ .diamond .king
def bB : Card := c_ .diamond .ten

#eval (tQ2 == tQ.flipSuit, zC == zS.flipSuit)
#eval (wst.isVis tQ, wst.isVis tQ2)
#eval (wst.board.bottomOf zS == some (Sum.inr tQ),
       wst.board.bottomOf zC == some (Sum.inr tQ2))
#eval (canSitOn zS tQ, canSitOn zC tQ2)
#eval (!(wst.board.aboveOf zS).contains tQ && !(wst.board.aboveOf zS).contains tQ2,
       !(wst.board.aboveOf zC).contains tQ && !(wst.board.aboveOf zC).contains tQ2)

-- the merge: legal in st, self-landing in stx
#eval (wst.board.aboveOf cH).contains tQ
#eval (wst.apply (Move.pilePile cH (Sum.inr zC))).isSome
#eval (wstx.apply (Move.pilePile cH (Sum.inr zC))).isSome
#eval (wstx.board.aboveOf cH).contains zC

-- the mirror landing (onto z) is blocked by B in stx
#eval (wstx.apply (Move.pilePile cH (Sum.inr zS))).isSome
#eval (wstx.board.topOf (Sum.inr zS)).map cardStr   -- some ♦10 (B blocks)

/-! ## The bounded searcher (from w15merge.lean, verbatim) -/

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

def winIn : Nat -> State -> Bool
  | 0, st => st.isWin
  | k + 1, st =>
      st.isWin ||
        (legalMoves st).any (fun m =>
          match st.apply m with
          | some s' => winIn k s'
          | none => false)

def stateKey (st : State) : String :=
  String.intercalate "," (Suit.all.map (fun s => toString (st.heights s))) ++ "|" ++
  String.intercalate "," (Anchor.all.map (fun a => toString (st.depths a))) ++ "|" ++
  toString st.stock.cursor ++ "/" ++ String.intercalate ";" (st.stock.cards.map cardStr) ++ "|" ++
  toString st.drawStep ++ "|" ++
  String.intercalate ";" (Anchor.all.flatMap (fun a => (st.deal.piles a).map cardStr)) ++ "|" ++
  String.intercalate ";" (Board.enumBase.map (fun b =>
    match st.board.topOf b with | none => "-" | some c => cardStr c))

def bfsWin : Nat -> List State -> List String -> Bool
  | 0, front, _ => front.any (fun s => s.isWin)
  | k + 1, front, vis =>
      front.any (fun s => s.isWin) ||
        let next := front.flatMap succs
        let news := next.filter (fun s => !(vis.contains (stateKey s)))
        bfsWin k news (news.foldl (fun acc s => stateKey s :: acc) vis)

def winBFS (k : Nat) (st : State) : Bool :=
  bfsWin k [st] [stateKey st]

/-! ## The DIVERGENCE? -/

-- st's winning play: the merge first, then the 14 climbs
-- (♣J before ♥Q: the merged stack unwinds from ♥10 down to ♣J, and
-- t' = ♥Q only goes bare once ♣J stacks off)
#eval Option.map State.isWin (wst.run
  [ Move.pilePile cH (Sum.inr zC)
  , Move.pileStack bB, Move.pileStack zS, Move.pileStack (c_ .diamond .jack)
  , Move.pileStack tQ, Move.pileStack xD
  , Move.pileStack cH, Move.pileStack zC, Move.pileStack (c_ .heart .jack)
  , Move.pileStack tQ2, Move.pileStack (c_ .heart .king)
  , Move.pileStack (c_ .spade .queen), Move.pileStack (c_ .spade .king)
  , Move.pileStack (c_ .club .queen), Move.pileStack (c_ .club .king) ])

-- stx's immediate structure (fast)
#eval String.intercalate "; " ((legalMoves wstx).map moveStr)

-- stx WINS TOO: founds_gone forces the blocker B = ♦10 to be LIVE
-- (at/above its suit's height), so B stacks off (diamond 9 -> 10),
-- the mirror merge opens (the run [♥10, ♦Q, ♣J] onto the now-bare
-- z = ♠J), and the full climb follows.  The w15merge blockade family
-- (a dead blocker riding the cargo) is STRUCTURALLY DEAD at WF.
#eval Option.map State.isWin (wstx.run
  [ Move.pileStack bB                                  -- ♦10: diamond 9 -> 10 (B leaves z)
  , Move.pilePile cH (Sum.inr zS)                      -- the MIRROR merge: [♥10, ♦Q, ♣J] onto ♠J
  , Move.pileStack zC                                  -- ♣J: club 10 -> 11
  , Move.pileStack (c_ .diamond .jack)                  -- ♦J: diamond 10 -> 11
  , Move.pileStack tQ                                  -- ♦Q: diamond 11 -> 12
  , Move.pileStack cH                                  -- ♥10: heart 9 -> 10
  , Move.pileStack zS                                  -- ♠J: spade 10 -> 11
  , Move.pileStack xD                                  -- ♦K (exposed): diamond 12 -> 13
  , Move.pileStack (c_ .heart .jack)                    -- ♥J: heart 10 -> 11
  , Move.pileStack tQ2                                 -- ♥Q: heart 11 -> 12
  , Move.pileStack (c_ .heart .king)                    -- ♥K: heart 12 -> 13
  , Move.pileStack (c_ .spade .queen)                   -- ♠Q: spade 11 -> 12
  , Move.pileStack (c_ .spade .king)                    -- ♠K: spade 12 -> 13
  , Move.pileStack (c_ .club .queen)                    -- ♣Q: club 11 -> 12
  , Move.pileStack (c_ .club .king) ])                  -- ♣K: club 12 -> 13

/-! ## The CYCLE probe: can a crafted WF state be cyclic?

**VERDICT: YES — `wfCheck wcyc` = true.** WF (all 11 conjuncts) does NOT
exclude cycles: the deal-adjacency "placed" arm + two fit edges close a
loop (♠K on ♣J deal-adjacent, ♣J on ♦Q fit, ♦Q on ♠K fit — ranks
J < Q < K, the two fit edges close through the unranked deal edge).
Consequences: the step-expansion (`aboveOf_step_some`, hypothesis
`c' ∉ aboveOf c'`) is NOT available at WF in general — self-disjointness
is not WF-implied (the walk from ♠K self-includes).  The merge
bridge's mirror-guard needs either an acyclicity premise in the
license (decidable, per-state) or the REACHABILITY scoping (reachable
boards are cycle-free: the initial board is linear and the
self-landing guard provably blocks every cycle-closing move — the
`initialReachable` descent).  Re-opens the gate: witness-hunt the
cyclic+licensed+merge family before choosing the repair.

The crafted 3-cycle (the probe):

def cd : Card := c_ .club .jack
def ce : Card := c_ .diamond .queen
def cc : Card := c_ .spade .king

def dl2 : List Card :=
  [c_ .heart .ace]                                        -- p0
  ++ [c_ .heart .two, c_ .heart .three]                    -- p1
  ++ [c_ .club .jack, c_ .spade .king, c_ .heart .four]    -- p2: the deal-adjacent pair ♣J < ♠K
  ++ [c_ .heart .five, c_ .heart .six, c_ .heart .seven, c_ .heart .eight]          -- p3
  ++ [c_ .heart .nine, c_ .heart .ten, c_ .heart .jack, c_ .heart .queen, c_ .heart .king]  -- p4
  ++ [c_ .spade .ace, c_ .spade .two, c_ .spade .three, c_ .spade .four,
      c_ .spade .five, c_ .spade .six]                    -- p5
  ++ [c_ .spade .seven, c_ .spade .eight, c_ .spade .nine, c_ .spade .ten,
      c_ .spade .jack, c_ .spade .queen, c_ .club .ace]   -- p6
  ++ [c_ .club .two, c_ .club .three, c_ .club .four, c_ .club .five, c_ .club .six,
      c_ .club .seven, c_ .club .eight, c_ .club .nine, c_ .club .ten,
      c_ .club .queen, c_ .club .king,
      c_ .diamond .ace, c_ .diamond .two, c_ .diamond .three, c_ .diamond .four,
      c_ .diamond .five, c_ .diamond .six, c_ .diamond .seven, c_ .diamond .eight,
      c_ .diamond .nine, c_ .diamond .ten, c_ .diamond .jack, c_ .diamond .queen,
      c_ .diamond .king]                                    -- stock (24)

def bcyc : Board := attachAll Board.empty
  [ (Sum.inr (c_ .diamond .queen), c_ .club .jack)     -- ♣J on ♦Q (fit: J on Q)
  , (Sum.inr (c_ .spade .king), c_ .diamond .queen)    -- ♦Q on ♠K (fit: Q on K)
  , (Sum.inr (c_ .club .jack), c_ .spade .king) ]     -- ♠K on ♣J (DEAL-ADJ)

def wcyc : State := State.mk (Deal.ofList dl2) bcyc (fun _ => 0) (fun _ => 0) (Cycle.mk [] 0) 1

#eval dl2.length                                          -- 52
#eval wfCheck wcyc                                        -- ???
#eval (wcyc.board.aboveOf cc).map cardStr                 -- the walk from ♠K (cycles?)
#eval (wcyc.board.aboveOf cc).contains cc                 -- self-inclusive?
#eval ((wcyc.board.aboveOf cd).contains ce,
       (wcyc.board.aboveOf ce).contains cc,
       (wcyc.board.aboveOf cc).contains cd)              -- the loop
