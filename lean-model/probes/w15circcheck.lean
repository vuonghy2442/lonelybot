import Klondike.Initial
import Klondike.TwinQuotient

/-! # w15circcheck: the w15circ cast re-verified against the REAL definitions (the tree green again after the v4.34 repair; the verbatim local copy in w15circ.lean is retired). Expected: every finding unchanged -- wfCheck both true, the license components, the merge blocked/self-landing in stx, the 16-move st win, the 18-move stx collapse. -/
/-!
# w15 CIRC probe — the circular-blocker family at WF (2026-09-16)

The gate for the merge shape at WF, attacking the remaining candidate
family from w15wfmerge's closing note: CIRCULAR blocker dependencies
("a blocker whose stacking rung is only reachable through the cards it
blocks").

The cast (t is a KING — the structural novelty):

- t = ♦K, t' = ♥K: the sub-run [t, z'] has NO card landings (nothing
  sits on a king), killing the w15-family black-king redirect at the
  root;
- c = ♥J, z = ♠Q, z' = ♣Q (the two black queens are exactly z, z' —
  c's run can only land on them);
- R = ♦Q rides z (deal-adjacent); R's rung ♦J is BURIED UNDER c: in
  stx, R's removal needs ♦J founded, ♦J's exposure needs c's run to
  move, c's run has no landing (z blocked by R, z' self-landing) —
  the circle;
- ♠K hidden behind the locked pin [♣9, ♣10] (the reveal is blocked
  while ♣9 sits on the boundary); X = ♣K at the merge pile's head;
- heights (♦10, ♥10, ♠11, ♣8), empty current stock (pure endgame —
  all 13 unfounded cards are board-seated or hidden).

st wins in 16 moves (the merge first, the pin unwinding through the
merge-exposed ♦J).

**FINDING: NO DIVERGENCE — the circular family COLLAPSES at WF.**
Both `wst` and `wstx` are WF (all conjuncts, executable check) and
licensed; the merge is forced in st (the buried rung ♦J exposes only
through c's run, whose only landing is z'); the merge self-lands in
stx and the mirror is blocked by R — **but stx WINS ANYWAY** (the
18-move collapse play below): t is a KING, so [t, z'] parks at a free
anchor (kings relocate freely), c re-lands on the now-bare z' (the
self-landing guard dies with the run), the burial chain unwinds
through the exposed ♦J, the [♣9, ♣10] pin breaks through the bare c,
and the full climb follows.

The w15wfmerge note's remaining family — CIRCULAR blocker
dependencies — is dead at WF in this cast.  The mechanism is the
ANCHOR-RELOCATION COLLAPSE: a blocked run with a king inside can be
dismantled from the top, and the freed twin cargo re-admits the run
head.  Free anchors are the collapse's fuel: holding all seven needs
~7 frozen occupants, each demanding circular stacking with a
merge-exposed unwind target — and the burial chain under c is the
only such target, single-use per cover rank.  Third documented
mirror-repair mechanism (after w15wfmerge's blocker-stacks-off and
fithole's rider-detour); the B&G piecewise bookkeeping's merge
handling gains the case.

NOTE: ran against a verbatim local copy of the exchange
(TwinExchange is red under the v4.34 toolchain — omega/rewrite/type
errors at 1263/1269/1291, its olean missing); re-verify against the
real definitions once the tree is green (the w15mergecheck pattern).
-/

/-! ## Small kit (from w15merge.lean, verbatim except the
anchor-indexed reveal) -/

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
  | .reveal a => "reveal " ++ anchorStr a
  | .deckPile c b => "deckPile " ++ cardStr c ++ " " ++ baseStr b
  | .deckStack c => "deckStack " ++ cardStr c
  | .pileStack c => "pileStack " ++ cardStr c
  | .stackPile c b => "stackPile " ++ cardStr c ++ " " ++ baseStr b
  | .pilePile c b => "pilePile " ++ cardStr c ++ " " ++ baseStr b

/-! ## The WF checker (all conjuncts, executable) -/

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

/-! ## The cast -/

def c_ (s : Suit) (r : Rank) : Card := Card.mk s r

/-- The deal: 52 slots, triangular split.
p1 head = ♥K (t'), p2 head = ♥Q, p3 carries the (♠Q, ♦Q) consec
(R's edge on z), p4 = ♠K hidden at the head + the pin consec pairs,
p5 = the merge pile (X = ♣K head, ♦J buried, c, t), p6 parks ♣J, ♣Q. -/
def dl : List Card :=
  [c_ .spade .ace]                                          -- p0: pad
  ++ [c_ .heart .king, c_ .club .ace]                       -- p1: ♥K = t' (head) + pad
  ++ [c_ .heart .queen, c_ .diamond .ace, c_ .diamond .two] -- p2: ♥Q (head) + pads
  ++ [c_ .spade .two, c_ .spade .queen, c_ .diamond .queen, c_ .spade .three]  -- p3: the (♠Q, ♦Q) consec
  ++ [c_ .spade .king, c_ .club .nine, c_ .club .ten, c_ .spade .four, c_ .spade .five]  -- p4: ♠K (hidden, depths 1) + pin pairs
  ++ [c_ .club .king, c_ .diamond .jack, c_ .heart .jack, c_ .diamond .king, c_ .spade .six, c_ .spade .seven]  -- p5: X < ♦J < c < t
  ++ [c_ .club .jack, c_ .club .queen, c_ .spade .eight, c_ .spade .nine, c_ .spade .ten, c_ .spade .jack, c_ .heart .ace]  -- p6: parked sitters + pads
  ++ [c_ .heart .two, c_ .heart .three, c_ .heart .four, c_ .heart .five, c_ .heart .six,
      c_ .heart .seven, c_ .heart .eight, c_ .heart .nine, c_ .heart .ten,
      c_ .diamond .three, c_ .diamond .four, c_ .diamond .five, c_ .diamond .six,
      c_ .diamond .seven, c_ .diamond .eight, c_ .diamond .nine, c_ .diamond .ten,
      c_ .club .two, c_ .club .three, c_ .club .four, c_ .club .five, c_ .club .six,
      c_ .club .seven, c_ .club .eight]                     -- deal stock (24)

#eval dl.length                                          -- 52
#eval Anchor.all.map (fun a => (Deal.ofList dl).piles a |>.map cardStr)
#eval (Deal.ofList dl).piles Anchor.p4 |>.map cardStr    -- [♠K, ♣9, ♣10, ♠4, ♠5]
#eval (Deal.ofList dl).piles Anchor.p5 |>.map cardStr    -- [♣K, ♦J, ♥J, ♦K, ♠6, ♠7]
#eval (Deal.ofList dl).piles Anchor.p3 |>.map cardStr    -- [♠2, ♠Q, ♦Q, ♠3]

/-- heights: every visible card at/above its suit's rung; c and z are
their suits' rungs (the circularity anchors). -/
def hts : Suit -> Nat := fun s =>
  match s with
  | .diamond => 10 | .heart => 10 | .spade => 11 | .club => 8

/-- the hidden pile: p4's boundary is ♠K (depths 1). -/
def dps : Anchor -> Nat := fun a =>
  match a with
  | .p4 => 1
  | _ => 0

/-- The board (st):

- p5-chain: X=♣K (head) <- ♦J (R's rung, buried) <- c=♥J <- t=♦K <-
  z=♠Q (fit) <- R=♦Q (deal-adj) <- ♣J (fit, R's cover);
- p1-chain: t'=♥K (head) <- z'=♣Q (fit);
- p2: ♥Q (head);
- p4: the hidden ♠K <- ♣9 (deal-adj on the boundary) <- ♣10 (deal-adj). -/
def bW : Board := attachAll Board.empty
  [ (Sum.inl Anchor.p5, c_ .club .king)                 -- X = ♣K (p5's head)
  , (Sum.inr (c_ .club .king), c_ .diamond .jack)       -- ♦J = R's rung, buried under c
  , (Sum.inr (c_ .diamond .jack), c_ .heart .jack)       -- c = ♥J
  , (Sum.inr (c_ .heart .jack), c_ .diamond .king)       -- t = ♦K
  , (Sum.inr (c_ .diamond .king), c_ .spade .queen)      -- z = ♠Q (fit)
  , (Sum.inr (c_ .spade .queen), c_ .diamond .queen)     -- R = ♦Q (deal-adj: p3's consec)
  , (Sum.inr (c_ .diamond .queen), c_ .club .jack)        -- ♣J on R (fit)
  , (Sum.inl Anchor.p1, c_ .heart .king)                  -- t' = ♥K (p1's head)
  , (Sum.inr (c_ .heart .king), c_ .club .queen)          -- z' = ♣Q (fit)
  , (Sum.inl Anchor.p2, c_ .heart .queen)                 -- ♥Q (p2's head)
  , (Sum.inr (c_ .spade .king), c_ .club .nine)           -- the pin on the hidden ♠K
  , (Sum.inr (c_ .club .nine), c_ .club .ten) ]           -- the pin cover

def wst : State := State.mk (Deal.ofList dl) bW hts dps (Cycle.mk [] 0) 1
def wstx : State := wst.exchangeTwinCargo (c_ .diamond .king)

-- THE WF CHECK
#eval wfCheck wst
#eval wfCheck wstx

-- diagnostics: which edge / which card, if a check fails
#eval Board.enumBase.filterMap (fun b =>
  match wst.board.topOf b with
  | none => none
  | some c => if (wst.board.bottomOf c == some b) && edgeOK wst b c then none
    else some (baseStr b ++ " <- " ++ cardStr c))
#eval (Card.universe.filter (fun c =>
  decide (c.rank.toIdx < wst.heights c.suit) &&
    (wst.isVis c || (wst.stock.posOf c).isSome ||
      Anchor.all.any (fun a => (wst.hidden a).contains c)))).map cardStr

-- the state's shape
#eval String.intercalate "; " (Board.enumBase.filterMap (fun b =>
  (wst.board.topOf b).map (fun c => baseStr b ++ " <- " ++ cardStr c)))
#eval Suit.all.map (fun s => (s, wst.heights s))
#eval (wst.topHidden Anchor.p4).map cardStr              -- some ♠K

/-! ## The names, the license, the merge -/

def tK : Card := c_ .diamond .king     -- t
def tK2 : Card := c_ .heart .king      -- t'
def zS : Card := c_ .spade .queen      -- z
def zC : Card := c_ .club .queen       -- z'
def cH : Card := c_ .heart .jack       -- c
def rD : Card := c_ .diamond .queen    -- R
def xC : Card := c_ .club .king        -- X
def bD : Card := c_ .diamond .jack     -- the buried rung ♦J

-- the twinLicensed components (all executable)
#eval (tK2 == tK.flipSuit, zC == zS.flipSuit)
#eval (wst.isVis tK, wst.isVis tK2)
#eval (wst.board.bottomOf zS == some (Sum.inr tK),
       wst.board.bottomOf zC == some (Sum.inr tK2))
#eval (canSitOn zS tK2, canSitOn zC tK)                 -- the license fits
#eval (!(wst.board.aboveOf zS).contains tK && !(wst.board.aboveOf zS).contains tK2,
       !(wst.board.aboveOf zC).contains tK && !(wst.board.aboveOf zC).contains tK2)
#eval (!(wst.board.aboveOf zS).contains zC, !(wst.board.aboveOf zC).contains zS)  -- no braid

-- the merge: legal in st, self-landing in stx, mirror blocked by R in stx
#eval (wst.apply (Move.pilePile cH (Sum.inr zC))).isSome
#eval (wstx.apply (Move.pilePile cH (Sum.inr zC))).isSome
#eval (wstx.apply (Move.pilePile cH (Sum.inr zS))).isSome
#eval (wstx.board.topOf (Sum.inr zS)).map cardStr        -- some ♦Q (R blocks)
#eval (wstx.board.topOf (Sum.inr tK)).map cardStr        -- some ♣Q (z' rides t: self-landing)
#eval (wstx.board.topOf (Sum.inr tK2)).map cardStr       -- some ♠Q (z rides t')

/-! ## The bounded searcher (reveal is anchor-indexed now) -/

def legalMoves (st : State) : List Move :=
  let vis : List Card := Board.enumBase.flatMap (fun b =>
    match st.board.topOf b with | some c => [c] | none => [])
  let cands : List Move :=
    (if st.stock.cards == [] then [] else [Move.draw])
    ++ Anchor.all.map (fun a => Move.reveal a)
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

/-! ## st WINS: the merge first, the pin unwinding through the
merge-exposed ♦J, then the climbs. -/

#eval Option.map State.isWin (wst.run
  [ Move.pilePile cH (Sum.inr zC)                     -- THE MERGE
  , Move.pilePile (c_ .club .ten) (Sum.inr bD)        -- the pin unwinds: ♣10 -> the exposed ♦J
  , Move.pileStack (c_ .club .nine)                   -- ♣9 (the ♣ rung)
  , Move.pileStack (c_ .club .ten)                   -- ♣10
  , Move.pileStack bD                                -- ♦J (the ♦ rung)
  , Move.pileStack (c_ .club .jack)                  -- ♣J
  , Move.pileStack rD                                -- R
  , Move.pileStack zS                                -- z (the ♠ rung)
  , Move.pileStack tK                                -- t
  , Move.pileStack cH                                -- c (the ♥ rung)
  , Move.pileStack zC                                -- z'
  , Move.pileStack (c_ .heart .queen)                -- ♥Q
  , Move.pileStack tK2                               -- t'
  , Move.reveal Anchor.p4                            -- ♠K surfaces
  , Move.pileStack (c_ .spade .king)                 -- ♠K
  , Move.pileStack xC ])                             -- X

/-! ## stx: the circle's death certificate or its collapse.

The predicted COLLAPSE (if the family is dead at WF): [t, z'] parks
at the free anchor p0, c re-lands on the bare z', the burial chain
unwinds, the pin breaks through the bare c, and the full climb
follows. -/

#eval String.intercalate "; " ((legalMoves wstx).map moveStr)

#eval Option.map State.isWin (wstx.run
  [ Move.pilePile tK (Sum.inl Anchor.p0)              -- the collapse: [t, z'] parks at p0
  , Move.pilePile cH (Sum.inr zC)                     -- c re-lands on the bare z'
  , Move.pileStack bD                                 -- the exposed rung ♦J
  , Move.pilePile (c_ .club .jack) (Sum.inr (c_ .heart .queen))  -- ♣J hops to ♥Q (frees R)
  , Move.pileStack rD                                -- R (♦ 11 -> 12)
  , Move.pilePile (c_ .club .ten) (Sum.inr cH)        -- the pin unwinds onto the bare c
  , Move.pileStack (c_ .club .nine)                   -- ♣ 8 -> 9
  , Move.pileStack (c_ .club .ten)                   -- ♣ 9 -> 10
  , Move.pileStack (c_ .club .jack)                  -- ♣ 10 -> 11
  , Move.pileStack cH                                -- c (♥ 10 -> 11)
  , Move.pileStack (c_ .heart .queen)                -- ♥Q (♥ 11 -> 12)
  , Move.pileStack zC                                 -- z' (♣ 11 -> 12)
  , Move.pileStack tK                                -- t (♦ 12 -> 13)
  , Move.pileStack zS                                -- z (♠ 11 -> 12)
  , Move.pileStack tK2                               -- t' (♥ 12 -> 13)
  , Move.reveal Anchor.p4                             -- ♠K surfaces
  , Move.pileStack (c_ .spade .king)                 -- ♠K (♠ 12 -> 13)
  , Move.pileStack xC ])                              -- X (♣ 12 -> 13)

-- THE GATE: the bounded search on stx (parked: the string-keyed BFS is
-- too slow at #eval; the explicit plays above decide the gate, and a
-- cheap depths audit can follow)
-- #eval winBFS 20 wstx
-- #eval winBFS 12 wst
