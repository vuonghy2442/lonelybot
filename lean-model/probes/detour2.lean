import Klondike.Initial
import Klondike.TwinQuotient

/-!
# The DETOUR-BASE probe II — the KING blockade (fithole's cast, anchors filled)

**FINDING: BLOCKABLE via the ANCHOR route too — a KING rider with NO free
anchor has NO detach base at WF.**

fithole's witness (r₁ = ♥K, a king, detouring to the free anchor p0) is here
modified in exactly one respect: BOTH free anchors are filled by their piles'
heads — p0 hosts ♦10 (p0's head) and p3 hosts ♥10 (p3's head) — with the
heights lowered to (9, 9, 10, 10) so both tens are finds_gone-legal (a visible
card must sit at/above its suit's height).  Everything else is fithole verbatim:
the license at t = ♥Q, the deep merge `pilePile ♦J (inr ♠Q)` (d = ♠Q rides
r₁ = ♥K on z' = ♣J), the hole (`canSitOn ♥K ♠J = false`), and a winning line
through the merge (`playDeep`, 15 moves).

A king has NO card-candidates at all (canSitOn ♥K e needs rank(e) = 13), so the
detach's only route is a FREE ANCHOR — and all seven are occupied:
p0 (♦10), p1 (t' = ♦Q), p2 (c = ♦J), p3 (♥10), p4 (♦K), p5 (♠K), p6 (♣K).
`Board.enumBase.all (fun b => !(dst2.apply (Move.pilePile rH b)).isSome)` =
TRUE: `State.ExchangeDeepNorm ♥Q ♠J ♣J ♦J (inr ♠Q)` FAILS here too, with all
hypotheses holding.

The contrast: in fithole, p0's and p3's heads were BELOW-height limbo pads
(♦2, ♥5 with heights 10) and p0 was free — the detour `pilePile ♥K (inl p0)`
fired.  The delta is exactly the two anchor-filler heads plus the two lowered
heights; nothing else changes.  (The deal-stock cards are all "drawn and gone" —
the state's cycle is empty — so the low stock cards are unconstrained, as in
fithole.)
-/

/-! ## The kit (fithole.lean, verbatim) -/

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

/-! ## The cast (fithole's, with the two anchor fillers) -/

def c_ (s : Suit) (r : Rank) : Card := Card.mk s r

def tH : Card := c_ .heart .queen        -- t  (the licensed twin)
def tD : Card := c_ .diamond .queen      -- t' = t.flipSuit
def zS : Card := c_ .spade .jack          -- z  (the cargo on t)
def zC : Card := c_ .club .jack           -- z' = z.flipSuit (the cargo on t')
def cJ : Card := c_ .diamond .jack        -- c  (the merge's root)
def rH : Card := c_ .heart .king           -- r₁ (the first rider — A KING this time)
def qS : Card := c_ .spade .queen          -- d  (the deep landing, fit on r₁)
def hJ : Card := c_ .heart .jack
def dK : Card := c_ .diamond .king
def cQ : Card := c_ .club .queen
def sK : Card := c_ .spade .king
def cK : Card := c_ .club .king
def d10 : Card := c_ .diamond .ten         -- THE ANCHOR FILLER for p0 (its head)
def h10 : Card := c_ .heart .ten           -- THE ANCHOR FILLER for p3 (its head)

/-- fithole's deal with p0 = [♦10] and p3 = [♥10, ...] (the filler heads); the
displaced pads (♦2, ♥5) swap into the stock. -/
def dl : List Card :=
  [c_ .diamond .ten]                                           -- p0: ♦10 (head — THE FILLER)
  ++ [c_ .diamond .queen, c_ .heart .four]                    -- p1: t' = ♦Q (head) + pad
  ++ [c_ .diamond .jack, c_ .heart .queen, c_ .spade .eight]  -- p2: c = ♦J (head) < t = ♥Q (pair)
  ++ [c_ .heart .ten, c_ .club .jack, c_ .heart .king, c_ .spade .queen]  -- p3: ♥10 (head — THE FILLER), z' < r₁ (pair), d
  ++ [c_ .diamond .king, c_ .heart .jack, c_ .club .queen, c_ .club .four, c_ .club .five]  -- p4: ♦K (head)
  ++ [c_ .spade .king, c_ .spade .jack, c_ .spade .two, c_ .spade .three, c_ .heart .six, c_ .heart .seven]  -- p5: ♠K (head), z = ♠J
  ++ [c_ .club .king, c_ .club .six, c_ .club .seven, c_ .club .eight, c_ .diamond .three, c_ .diamond .four, c_ .diamond .five]  -- p6: ♣K (head)
  ++ [c_ .heart .ace, c_ .heart .two, c_ .heart .three, c_ .heart .five, c_ .heart .eight, c_ .heart .nine,
      c_ .diamond .ace, c_ .diamond .two, c_ .diamond .six, c_ .diamond .seven, c_ .diamond .eight, c_ .diamond .nine,
      c_ .spade .ace, c_ .spade .four, c_ .spade .five, c_ .spade .six, c_ .spade .seven,
      c_ .spade .nine, c_ .spade .ten,
      c_ .club .ace, c_ .club .two, c_ .club .three, c_ .club .nine, c_ .club .ten]  -- stock (24)

/-- heights lowered from fithole's (10,10,10,10) so the two filler tens are
founds_gone-legal visible heads. -/
def hts : Suit -> Nat := fun s =>
  match s with
  | .diamond => 9 | .heart => 9 | .spade => 10 | .club => 10

def bW : Board := attachAll Board.empty
  [ (Sum.inl Anchor.p1, tD)          -- t' = ♦Q (p1's head)
  , (Sum.inr tD, zC)                 -- z' = ♣J on t' (fit)
  , (Sum.inr zC, rH)                 -- r₁ = ♥K on z' (DEAL-ADJ: the p3 pair) — THE HOLE EDGE
  , (Sum.inr rH, qS)                 -- d = ♠Q on r₁ (fit; BARE)
  , (Sum.inl Anchor.p2, cJ)          -- c = ♦J (p2's head)
  , (Sum.inr cJ, tH)                 -- t = ♥Q on c (DEAL-ADJ: the p2 pair)
  , (Sum.inr tH, zS)                 -- z = ♠J on t (fit; BARE — riders-cleared)
  , (Sum.inl Anchor.p4, dK)          -- ♦K (p4's head, king)
  , (Sum.inr dK, cQ)                 -- ♣Q on ♦K (fit)
  , (Sum.inr cQ, hJ)                 -- ♥J on ♣Q (fit)
  , (Sum.inl Anchor.p5, sK)          -- ♠K (p5's head, king)
  , (Sum.inl Anchor.p6, cK)         -- ♣K (p6's head, king)
  , (Sum.inl Anchor.p0, d10)        -- ♦10 (p0's head) — THE FILLER (fithole left p0 FREE)
  , (Sum.inl Anchor.p3, h10) ]      -- ♥10 (p3's head) — THE FILLER (fithole left p3 FREE)

def dst2 : State := State.mk (Deal.ofList dl) bW hts (fun _ => 0) (Cycle.mk [] 0) 1
def dst2x : State := dst2.exchangeTwinCargo tH

/-! ## The witness is WF and licensed -/

#eval dl.length                                                       -- 52
#eval (Deal.ofList dl).piles Anchor.p2 |>.map cardStr                  -- [DJ, HQ, S8] — the t-edge pair
#eval (Deal.ofList dl).piles Anchor.p3 |>.map cardStr                  -- [H10, CJ, HK, SQ] — the RIDER pair (♣J, ♥K)

#eval wfCheck dst2                                                     -- TRUE — all 11 conjuncts
#eval wfCheck dst2x                                                    -- TRUE

-- diagnostics (clean = empty)
#eval Board.enumBase.filterMap (fun b =>
  match dst2.board.topOf b with
  | none => none
  | some c => if (dst2.board.bottomOf c == some b) && edgeOK dst2 b c then none
    else some (baseStr b ++ " <- " ++ cardStr c))
#eval (Card.universe.filter (fun c =>
  decide (c.rank.toIdx < dst2.heights c.suit) &&
    (dst2.isVis c || (dst2.stock.posOf c).isSome ||
      Anchor.all.any (fun a => (dst2.hidden a).contains c)))).map cardStr
#eval String.intercalate "; " (Board.enumBase.filterMap (fun b =>
  (dst2.board.topOf b).map (fun c => baseStr b ++ " <- " ++ cardStr c)))
#eval Suit.all.map (fun s => (s, dst2.heights s))

-- the license at t = ♥Q (TwinLicensedAt, unpacked)
#eval (tD == tH.flipSuit, zC == zS.flipSuit)                           -- (true, true)
#eval (dst2.isVis tH, dst2.isVis tD)                                   -- (true, true)
#eval (dst2.board.bottomOf zS == some (Sum.inr tH),
       dst2.board.bottomOf zC == some (Sum.inr tD))                     -- (true, true)
#eval (canSitOn zS tH, canSitOn zC tD)                                 -- (true, true)
#eval (!(dst2.board.aboveOf zS).contains tH && !(dst2.board.aboveOf zS).contains tD,
       !(dst2.board.aboveOf zC).contains tH && !(dst2.board.aboveOf zC).contains tD)  -- (true, true)
#eval (dst2.board.topOf (Sum.inr zS)).isNone                            -- true — z bare

-- the deep merge and its shape
#eval (dst2.board.aboveOf zC).map cardStr                                -- [SQ, HK] — d and r₁ above z'
#eval ((dst2.board.aboveOf zC).contains qS, qS != zC)                     -- (true, true) — DEEP
#eval (dst2.board.topOf (Sum.inr zC) == some rH,
       dst2.board.bottomOf rH == some (Sum.inr zC))                      -- (true, true) — r₁ DIRECTLY on z'
#eval (dst2.board.aboveOf cJ).contains tH                                -- true — t ∈ aboveOf c
#eval (dst2.apply (Move.pilePile cJ (Sum.inr qS))).isSome                 -- true — the deep merge LEGAL
#eval (canSitOn rH zS, canSitOn rH zC)                                  -- (false, false) — THE HOLE
#eval consec (dst2.deal.piles Anchor.p3) zC rH                          -- true — (♣J, ♥K) consecutive in p3

/-! ## THE BLOCKADE (king + all anchors occupied) -/

#eval (rH.rank == Rank.king)                                          -- true — r₁ is a KING (no card-candidates exist)
#eval Anchor.all.all (fun a => (dst2.board.topOf (Sum.inl a)).isSome)    -- TRUE — ALL SEVEN anchors occupied
#eval Anchor.all.map (fun a => (dst2.board.topOf (Sum.inl a)).map cardStr)
#eval (dst2.apply (Move.pilePile rH (Sum.inl Anchor.p0))).isSome        -- false — fithole's detour base, now filled
#eval (dst2.apply (Move.pilePile rH (Sum.inl Anchor.p3))).isSome        -- false — the other former free anchor
-- THE SWEEP: NO detach base exists at all
#eval Board.enumBase.all (fun b => !(dst2.apply (Move.pilePile rH b)).isSome)   -- TRUE — NO DETACH EXISTS

-- the exchanged state: the hole is LIVE there (fithole's finding, re-confirmed)
#eval (dst2x.board.topOf (Sum.inr tH)).map cardStr                       -- some "CJ" — z' rides t in stx
#eval (dst2x.apply (Move.pilePile cJ (Sum.inr qS))).isSome               -- false — the mirror merge self-lands
#eval (dst2x.apply (Move.pilePile rH (Sum.inr zS))).isSome                -- false — the rider transfer dies
#eval (!(dst2.board.aboveOf rH).contains tH && !(dst2.board.aboveOf rH).contains tD)  -- true — detour-clean shape

/-! ## The play (the merge on a winning line) -/

def aA2 : State := (dst2.apply (Move.pilePile cJ (Sum.inr qS))).getD dst2

/-- The climb from A (14 stacks). -/
def playClimb2 : List Move :=
  [ Move.pileStack h10                      -- ♥10 (heart 9→10) — p3's filler
  , Move.pileStack hJ                       -- ♥J (heart 10→11)
  , Move.pileStack d10                      -- ♦10 (diamond 9→10) — p0's filler
  , Move.pileStack zS                       -- z = ♠J (spade 10→11)
  , Move.pileStack tH                       -- t = ♥Q (heart 11→12)
  , Move.pileStack cJ                       -- c = ♦J (diamond 10→11)
  , Move.pileStack qS                       -- d = ♠Q (spade 11→12)
  , Move.pileStack rH                       -- r₁ = ♥K (heart 12→13)
  , Move.pileStack zC                       -- z' = ♣J (club 10→11)
  , Move.pileStack tD                       -- t' = ♦Q (diamond 11→12)
  , Move.pileStack cQ                       -- ♣Q (club 11→12)
  , Move.pileStack dK                       -- ♦K (diamond 12→13)
  , Move.pileStack sK                       -- ♠K (spade 12→13)
  , Move.pileStack cK ]                     -- ♣K (club 12→13)

def playDeep2 : List Move := Move.pilePile cJ (Sum.inr qS) :: playClimb2

#eval Option.map State.isWin (aA2.run playClimb2)     -- some true — A.solvableFrom
#eval firstFail aA2 playClimb2 0                       -- none
#eval Option.map State.isWin (dst2.run playDeep2)     -- some true — the merge on a winning line
#eval firstFail dst2 playDeep2 0                       -- none
#eval (dst2.run playDeep2).map (fun W => Suit.all.map (fun s => W.heights s))    -- some [13,13,13,13]

/-! ## The ITERATED NORMALIZATION rescues this witness too (both sides) -/

/-- Clear the filler (♥10 stacks off anchor p3 — heart 9 = rank(♥10)), then the
king-detour fires (p3 now free), then the SAME merge, then the climbs (16). -/
def playIter2 : List Move :=
  [ Move.pileStack h10                      -- 1. CLEAR: ♥10 (heart 9→10) — anchor p3 goes FREE
  , Move.pilePile rH (Sum.inl Anchor.p3)     -- 2. THE DETOUR: r₁'s run [♥K, ♠Q] onto the freed p3
  , Move.pilePile cJ (Sum.inr qS)            -- 3. the merge onto d — the run left the cargo seat
  , Move.pileStack hJ, Move.pileStack d10, Move.pileStack zS, Move.pileStack tH
  , Move.pileStack cJ, Move.pileStack qS, Move.pileStack rH, Move.pileStack zC
  , Move.pileStack tD, Move.pileStack cQ, Move.pileStack dK, Move.pileStack sK
  , Move.pileStack cK ]

/-- The EXCHANGED state's iterated repair: the same three moves, translated
climbs (16). -/
def playIter2X : List Move :=
  [ Move.pileStack h10
  , Move.pilePile rH (Sum.inl Anchor.p3)
  , Move.pilePile cJ (Sum.inr qS)
  , Move.pileStack zC, Move.pileStack zS, Move.pileStack hJ, Move.pileStack d10
  , Move.pileStack tH, Move.pileStack cJ, Move.pileStack qS, Move.pileStack rH
  , Move.pileStack tD, Move.pileStack cQ, Move.pileStack dK, Move.pileStack sK
  , Move.pileStack cK ]

#eval Option.map State.isWin (dst2.run playIter2)     -- some true — the ITERATED NORMALIZATION wins
#eval firstFail dst2 playIter2 0                       -- none
#eval Option.map State.isWin (dst2x.run playIter2X)   -- some true — the mirror repair wins
#eval firstFail dst2x playIter2X 0                     -- none
#eval (dst2.run playIter2).map (fun W => Suit.all.map (fun s => W.heights s))    -- some [13,13,13,13]
#eval (dst2x.run playIter2X).map (fun W => Suit.all.map (fun s => W.heights s))  -- some [13,13,13,13]
