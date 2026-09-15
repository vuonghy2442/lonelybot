import Klondike.Initial
import Klondike.TwinQuotient

/-!
# The FIT-HOLE probe (route step 2b — the deep landing's rider transfer)

**FINDING: THE HOLE IS LIVE AT WF.**

The witness `fst` is WF (all 11 conjuncts; `wfCheck` true for BOTH `fst`
and the exchanged `fstx`) and twinLicensed at t = ♥Q; the merge
`pilePile ♦J (inr ♠Q)` is a DEEP landing (d = ♠Q rides r₁ = ♥K on
z' = ♣J, d ≠ z'), legal, and on the source's winning line (`playDeep`,
13 moves).  The FIRST RIDER r₁ = ♥K sits on z' by DEAL-ADJACENCY —
(♣J, ♥K) genuinely consecutive in pile p3 — and fits NEITHER cargo
(`canSitOn ♥K ♣J = false`, `canSitOn ♥K ♠J = false`), so twin-blindness
gives nothing: the 2b rider transfer `pilePile r₁ (inr z)` is ILLEGAL
in the exchanged state, and the mirror merge `pilePile c (inr d)` is
self-landing there (the exchange seats z' on t, inside c's run).

**THE REPAIR (validated): PLAY NORMALIZATION (a), mirrored.**  The
rider-detour `pilePile ♥K (inl p0)` — r₁'s run to the free anchor p0 —
is legal in BOTH states (a clean move: the rider run is off-pair by
the license's no-braid premises, so the existing
`exchangeTwinCargo_step_pilePile` shape applies); after it, the
ORIGINAL merge move `pilePile ♦J (inr ♠Q)` is legal in BOTH states
(d has left c's run in each) and the results are related BOTH ways:
twin-swapped at z (`m1D.board == a1D.board.mapByTwin ♠J` — the ply
conclusion of `exchange_merge_ply_root`) and seat-exchanged
(`m1D.board == a1D.exchangeTwinCargo ♥Q`'s — the conclusion of
`exchangeTwinCargo_step_pilePile_passing`).  The normalized source
play (`playNorm`) and the exchanged repair play (`playMir`) — the
SAME two moves plus translated climbs — both win; every alternative
cut (b) fails.

Cast: t = ♥Q, t' = ♦Q, z = ♠J, z' = ♣J, c = ♦J, r₁ = ♥K, d = ♠Q;
heights (10, 10, 10, 10); the deal-adjacency pairs (♦J, ♥Q) in p2
[the t-edge] and (♣J, ♥K) in p3 [the RIDER edge]; only anchor p0 free
(the detour's target).  Rungs: J = 10, Q = 11, K = 12.
-/

/-! ## The kit (w15wfmerge.lean, verbatim) -/

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

/-- The first failing move's index (none = the whole play runs). -/
def firstFail : State → List Move → Nat → Option Nat
  | _, [], _ => none
  | S, m :: ms, i =>
      match S.apply m with
      | none => some i
      | some S' => firstFail S' ms (i + 1)

/-! ## The cast -/

def c_ (s : Suit) (r : Rank) : Card := Card.mk s r

def tH : Card := c_ .heart .queen        -- t  (the licensed twin)
def tD : Card := c_ .diamond .queen      -- t' = t.flipSuit
def zS : Card := c_ .spade .jack          -- z  (the cargo on t)
def zC : Card := c_ .club .jack           -- z' = z.flipSuit (the cargo on t')
def cJ : Card := c_ .diamond .jack        -- c  (the merge's root)
def rH : Card := c_ .heart .king           -- r₁ (the first rider — DEAL-ADJACENT on z')
def qS : Card := c_ .spade .queen          -- d  (the deep landing, on r₁)
def hJ : Card := c_ .heart .jack
def dK : Card := c_ .diamond .king
def cQ : Card := c_ .club .queen
def sK : Card := c_ .spade .king
def cK : Card := c_ .club .king

/-- The deal: p1 head = t'; p2 = [c, t, pad] (the t-edge pair
(♦J, ♥Q)); p3 = [pad, z', r₁, d] (the RIDER pair (♣J, ♥K)); anchors
p4/p5/p6 host the kings and the ♦K-stack; p0's head is an unplaced
pad, so anchor p0 is FREE (the detour's target). -/
def dl : List Card :=
  [c_ .diamond .two]                                            -- p0: pad (anchor p0 EMPTY)
  ++ [c_ .diamond .queen, c_ .heart .four]                       -- p1: t' = ♦Q (head) + pad
  ++ [c_ .diamond .jack, c_ .heart .queen, c_ .spade .eight]     -- p2: c = ♦J (head) < t = ♥Q (pair)
  ++ [c_ .heart .five, c_ .club .jack, c_ .heart .king, c_ .spade .queen]  -- p3: pad, z' < r₁ (pair), d
  ++ [c_ .diamond .king, c_ .heart .jack, c_ .club .queen, c_ .club .four, c_ .club .five]  -- p4: ♦K (head)
  ++ [c_ .spade .king, c_ .spade .jack, c_ .spade .two, c_ .spade .three, c_ .heart .six, c_ .heart .seven]  -- p5: ♠K (head), z = ♠J
  ++ [c_ .club .king, c_ .club .six, c_ .club .seven, c_ .club .eight, c_ .diamond .three, c_ .diamond .four, c_ .diamond .five]  -- p6: ♣K (head)
  ++ [c_ .heart .ace, c_ .heart .two, c_ .heart .three, c_ .heart .eight, c_ .heart .nine, c_ .heart .ten,
      c_ .diamond .ace, c_ .diamond .six, c_ .diamond .seven, c_ .diamond .eight, c_ .diamond .nine, c_ .diamond .ten,
      c_ .spade .ace, c_ .spade .four, c_ .spade .five, c_ .spade .six, c_ .spade .seven,
      c_ .spade .nine, c_ .spade .ten,
      c_ .club .ace, c_ .club .two, c_ .club .three, c_ .club .nine, c_ .club .ten]  -- stock (24, all below height)

def hts : Suit -> Nat := fun s =>
  match s with
  | .diamond => 10 | .heart => 10 | .spade => 10 | .club => 10

def bF : Board := attachAll Board.empty
  [ (Sum.inl Anchor.p1, tD)          -- t' = ♦Q (p1's head)
  , (Sum.inr tD, zC)                 -- z' = ♣J on t' (fit)
  , (Sum.inr zC, rH)                 -- r₁ = ♥K on z' (DEAL-ADJ: the p3 pair) — THE HOLE EDGE
  , (Sum.inr rH, qS)                 -- d = ♠Q on r₁ (fit)
  , (Sum.inl Anchor.p2, cJ)          -- c = ♦J (p2's head)
  , (Sum.inr cJ, tH)                 -- t = ♥Q on c (DEAL-ADJ: the p2 pair)
  , (Sum.inr tH, zS)                 -- z = ♠J on t (fit; BARE — riders-cleared)
  , (Sum.inl Anchor.p4, dK)          -- ♦K (p4's head, king)
  , (Sum.inr dK, cQ)                 -- ♣Q on ♦K (fit)
  , (Sum.inr cQ, hJ)                 -- ♥J on ♣Q (fit)
  , (Sum.inl Anchor.p5, sK)          -- ♠K (p5's head, king)
  , (Sum.inl Anchor.p6, cK) ]        -- ♣K (p6's head, king)

def fst : State := State.mk (Deal.ofList dl) bF hts (fun _ => 0) (Cycle.mk [] 0) 1
def fstx : State := fst.exchangeTwinCargo tH

/-! ## Q1: the witness is WF and licensed -/

#eval dl.length                                                       -- 52
#eval (Deal.ofList dl).piles Anchor.p2 |>.map cardStr                  -- [♦J, ♥Q, ♠8] — the t-edge pair
#eval (Deal.ofList dl).piles Anchor.p3 |>.map cardStr                  -- [♥5, ♣J, ♥K, ♠Q] — the RIDER pair

#eval wfCheck fst                                                     -- TRUE — all 11 conjuncts
#eval wfCheck fstx                                                    -- TRUE

-- diagnostics (clean = empty)
#eval Board.enumBase.filterMap (fun b =>
  match fst.board.topOf b with
  | none => none
  | some c => if (fst.board.bottomOf c == some b) && edgeOK fst b c then none
    else some (baseStr b ++ " <- " ++ cardStr c))
#eval (Card.universe.filter (fun c =>
  decide (c.rank.toIdx < fst.heights c.suit) &&
    (fst.isVis c || (fst.stock.posOf c).isSome ||
      Anchor.all.any (fun a => (fst.hidden a).contains c)))).map cardStr
#eval String.intercalate "; " (Board.enumBase.filterMap (fun b =>
  (fst.board.topOf b).map (fun c => baseStr b ++ " <- " ++ cardStr c)))
#eval Suit.all.map (fun s => (s, fst.heights s))

-- the license at t = ♥Q (twinLicensed, unpacked)
#eval (tD == tH.flipSuit, zC == zS.flipSuit)                           -- (true, true) — the twin pairs
#eval (fst.isVis tH, fst.isVis tD)                                     -- (true, true)
#eval (fst.board.bottomOf zS == some (Sum.inr tH),
       fst.board.bottomOf zC == some (Sum.inr tD))                      -- (true, true) — cargos on the twins
#eval (canSitOn zS tH, canSitOn zC tD)                                 -- (true, true) — both fits
#eval (!(fst.board.aboveOf zS).contains tH && !(fst.board.aboveOf zS).contains tD,
       !(fst.board.aboveOf zC).contains tH && !(fst.board.aboveOf zC).contains tD)  -- (true, true) — no braids
#eval (fst.board.topOf (Sum.inr zS)).isNone                            -- true — z bare (riders-cleared)

-- the deep merge and its shape
#eval (fst.board.aboveOf zC).map cardStr                                -- ["SQ", "HK"] — d and r₁ above z'
#eval ((fst.board.aboveOf zC).contains qS, qS != zC)                    -- (true, true) — DEEP (d ≠ z')
#eval (fst.board.topOf (Sum.inr zC) == some rH,
       fst.board.bottomOf rH == some (Sum.inr zC))                     -- (true, true) — r₁ DIRECTLY on z'
#eval (fst.board.aboveOf cJ).map cardStr                                -- ["SJ", "HQ"] — c's run passes t
#eval (fst.apply (Move.pilePile cJ (Sum.inr qS))).isSome                 -- true — the deep merge LEGAL

/-! ## Q1: THE HOLE -/

#eval (canSitOn rH zC, canSitOn rH zS)                                  -- (false, false) — THE HOLE
#eval consec (fst.deal.piles Anchor.p3) zC rH                          -- true — (♣J, ♥K) consecutive in p3
#eval edgeOK fst (Sum.inr zC) rH                                       -- true — the edge is deal-adj-justified
#eval (fstx.board.topOf (Sum.inr tH)).map cardStr                       -- some "CJ" — z' rides t in stx
#eval (fstx.board.aboveOf cJ).map cardStr                               -- ["SQ", "HK", "CJ", "HQ"] — d inside c's run
#eval (fstx.apply (Move.pilePile rH (Sum.inr zS))).isSome                -- FALSE — the RIDER TRANSFER dies
#eval (fstx.apply (Move.pilePile cJ (Sum.inr qS))).isSome                -- FALSE — the mirror merge self-lands

/-! ## Q2(b): the alternative cuts — ALL FAIL -/

#eval (fstx.apply (Move.pilePile qS (Sum.inr zS))).isSome               -- false — a different prefix (from d): no fit
#eval (fstx.apply (Move.pilePile cJ (Sum.inr zC))).isSome               -- false — land on z': self-landing
#eval (fstx.apply (Move.pilePile cJ (Sum.inr rH))).isSome                -- false — land on r₁: no fit

/-! ## Q2(a): the repair — the rider DETOUR (normalization, mirrored) -/

#eval (fst.apply (Move.pilePile rH (Sum.inl Anchor.p0))).isSome         -- true — the detour, in st
#eval (fstx.apply (Move.pilePile rH (Sum.inl Anchor.p0))).isSome        -- true — the SAME move, in stx (clean)

def stD : State := (fst.apply (Move.pilePile rH (Sum.inl Anchor.p0))).getD fst
def stxD : State := (fstx.apply (Move.pilePile rH (Sum.inl Anchor.p0))).getD fstx

#eval (stD.board.topOf (Sum.inr zC)).isNone                            -- true — z' bare after the detour
#eval ((stD.board.aboveOf zC).contains qS)                              -- false — the landing left the cargo run
#eval (stD.apply (Move.pilePile cJ (Sum.inr zS))).isSome                -- false — the ROOT variant needs rank(c) = rank(z')−1
#eval (stD.apply (Move.pilePile cJ (Sum.inr qS))).isSome                 -- true — the ORIGINAL merge (the passing shape)
#eval (stxD.apply (Move.pilePile cJ (Sum.inr qS))).isSome                -- true — the SAME merge, legal in stx too

def a1D : State := (stD.apply (Move.pilePile cJ (Sum.inr qS))).getD stD
def m1D : State := (stxD.apply (Move.pilePile cJ (Sum.inr qS))).getD stxD

-- the ply results: twin-swapped at z (exchange_merge_ply_root's conclusion shape) ...
#eval Board.enumBase.all (fun b => m1D.board.topOf b == (a1D.board.mapByTwin zS).topOf b)   -- true
-- ... AND seat-exchanged (exchangeTwinCargo_step_pilePile_passing's conclusion shape)
#eval Board.enumBase.all (fun b => m1D.board.topOf b == (a1D.exchangeTwinCargo tH).board.topOf b)  -- true
#eval (Anchor.all.all (fun a => m1D.deal.piles a == a1D.deal.piles a) && m1D.deal.stock == a1D.deal.stock
      && Suit.all.all (fun s => m1D.heights s == a1D.heights s)
      && Anchor.all.all (fun a => m1D.depths a == a1D.depths a)
      && m1D.stock.cards == a1D.stock.cards && m1D.stock.cursor == a1D.stock.cursor
      && m1D.drawStep == a1D.drawStep)                                   -- true — every other field equal

/-! ## The plays -/

/-- The SOURCE's win THROUGH the deep merge (13 moves). -/
def playDeep : List Move :=
  [ Move.pilePile cJ (Sum.inr qS)                    -- 1. THE DEEP MERGE (c's run onto d = ♠Q)
  , Move.pileStack hJ                                 -- 2. ♥J (heart 10→11)
  , Move.pileStack zS                                 -- 3. ♠J (spade 10→11)
  , Move.pileStack tH                                 -- 4. ♥Q (heart 11→12)
  , Move.pileStack cJ                                 -- 5. ♦J (diamond 10→11)
  , Move.pileStack qS                                 -- 6. ♠Q (spade 11→12)
  , Move.pileStack rH                                 -- 7. ♥K = r₁ (heart 12→13)
  , Move.pileStack zC                                 -- 8. ♣J = z' (club 10→11)
  , Move.pileStack tD                                 -- 9. ♦Q = t' (diamond 11→12)
  , Move.pileStack cQ                                 -- 10. ♣Q (club 11→12)
  , Move.pileStack dK                                 -- 11. ♦K (diamond 12→13)
  , Move.pileStack cK                                 -- 12. ♣K (club 12→13)
  , Move.pileStack sK ]                               -- 13. ♠K (spade 12→13)

/-- The SOURCE, NORMALIZED: the detour first, then the (now off-cargo)
merge — the SAME merge move, landing no longer deep (14). -/
def playNorm : List Move :=
  [ Move.pilePile rH (Sum.inl Anchor.p0)             -- 1. THE DETOUR: r₁'s run [♥K, ♠Q] to p0
  , Move.pilePile cJ (Sum.inr qS)                     -- 2. the merge onto d — no longer deep
  , Move.pileStack hJ, Move.pileStack zS, Move.pileStack tH, Move.pileStack cJ
  , Move.pileStack qS, Move.pileStack rH, Move.pileStack zC, Move.pileStack tD
  , Move.pileStack cQ, Move.pileStack dK, Move.pileStack cK, Move.pileStack sK ]

/-- The EXCHANGED state's REPAIR PLAY: the SAME detour, the SAME merge
(both legal there after the detour), then the translated climbs (14). -/
def playMir : List Move :=
  [ Move.pilePile rH (Sum.inl Anchor.p0)             -- 1. the SAME detour (clean)
  , Move.pilePile cJ (Sum.inr qS)                     -- 2. the SAME merge (d is off c's run in stx too)
  , Move.pileStack hJ, Move.pileStack zC, Move.pileStack tH, Move.pileStack cJ
  , Move.pileStack zS, Move.pileStack qS, Move.pileStack rH, Move.pileStack tD
  , Move.pileStack cQ, Move.pileStack dK, Move.pileStack cK, Move.pileStack sK ]

#eval Option.map State.isWin (fst.run playDeep)       -- some true
#eval firstFail fst playDeep 0                         -- none
#eval Option.map State.isWin (fst.run playNorm)       -- some true
#eval firstFail fst playNorm 0                         -- none
#eval Option.map State.isWin (fstx.run playMir)       -- some true
#eval firstFail fstx playMir 0                         -- none
#eval (fst.run playDeep).map (fun W => Suit.all.map (fun s => W.heights s))    -- some [13,13,13,13]
#eval (fstx.run playMir).map (fun W => Suit.all.map (fun s => W.heights s))     -- some [13,13,13,13]
