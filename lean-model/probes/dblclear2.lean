import Klondike.Initial
import Klondike.TwinQuotient

/-! # The constructive double-clearing schedule — the rung-raising route

The constructive lead, probed: detour.lean's blockade witness REBUILT
with the blocker's rung NOT YET ARRIVED (heart height 8, so `pileStack
♥10` cannot fire), and the missing rung card ♥9 placed in the STATE
STOCK as the waste top.  The CONSTRUCTIVE schedule — no extraction from
a winning play, built from the structure:

  (a) RAISE THE RUNG: `deckStack ♥9` — a stock card, hence never a
      protected card (the protected four are all visible/seated, and
      WF's `vis_off_cycle` keeps visible cards out of the stock), and
      deckStack/draw are UNCONDITIONALLY exchange-clean (the step kit
      has them premise-free);
  (b) STACK THE BLOCKER: `pileStack ♥10` — now the rung is exact —
      clean (♥10 off both pairs);
  (c) THE Z'-DETOUR: `pilePile ♣J (inr ♦Q)` — the rider run onto the
      now-bare ♦Q (clean per the detour analysis);
  (d) THE MERGE, then the climbs.

Both sides win through the schedule (the mirror plays the SAME first
four moves — draws/deckStacks/stacks/detours are exchange-clean — then
the translated climbs).  This is the constructive existence evidence:
the (a)-step is always available (any stock card is reachable by draws
and consumed by deckStack; the raisers never collide with the protected
cards by the rank ladder — see the (i)-check below), and the (b)/(c)
steps are the already-validated iterated repair.
-/

/-! ## The kit (detour.lean, verbatim) -/

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

/-! ## detour.lean's cast, rebuilt with the rung NOT YET ARRIVED -/

def c_ (s : Suit) (r : Rank) : Card := Card.mk s r

def tS : Card := c_ .spade .queen        -- t
def tC : Card := c_ .club .queen         -- t' = t.flipSuit
def zH : Card := c_ .heart .jack          -- z
def zD : Card := c_ .diamond .jack        -- z'
def cH : Card := c_ .heart .queen          -- c  (the merge's root)
def rC : Card := c_ .club .jack            -- r₁ (the hole rider on z')
def dS : Card := c_ .spade .king            -- d  (the deep landing)
def qD : Card := c_ .diamond .queen        -- r₁'s candidate #2 (blocker-ridden)
def h10 : Card := c_ .heart .ten           -- THE BLOCKER on ♦Q
def h9 : Card := c_ .heart .nine            -- THE MISSING RUNG CARD (in the stock)
def hK : Card := c_ .heart .king
def dK : Card := c_ .diamond .king
def cK : Card := c_ .club .king

def dl : List Card :=
  [c_ .heart .king]
  ++ [c_ .club .queen, c_ .heart .ace]
  ++ [c_ .heart .queen, c_ .spade .queen, c_ .heart .jack]
  ++ [c_ .spade .ace, c_ .diamond .jack, c_ .club .jack, c_ .spade .king]
  ++ [c_ .diamond .queen, c_ .heart .ten, c_ .heart .two, c_ .heart .three, c_ .heart .four]
  ++ [c_ .diamond .king, c_ .spade .two, c_ .spade .three, c_ .spade .four, c_ .spade .five, c_ .spade .six]
  ++ [c_ .club .king, c_ .club .ace, c_ .club .two, c_ .club .three, c_ .club .four, c_ .club .five, c_ .club .six]
  ++ [c_ .heart .five, c_ .heart .six, c_ .heart .seven, c_ .heart .eight, c_ .heart .nine,
      c_ .diamond .ace, c_ .diamond .two, c_ .diamond .three, c_ .diamond .four, c_ .diamond .five,
      c_ .diamond .six, c_ .diamond .seven, c_ .diamond .eight, c_ .diamond .nine, c_ .diamond .ten,
      c_ .spade .seven, c_ .spade .eight, c_ .spade .nine, c_ .spade .ten, c_ .spade .jack,
      c_ .club .seven, c_ .club .eight, c_ .club .nine, c_ .club .ten]

/-- Heart height LOWERED to 8: the blocker ♥10's rung has NOT arrived. -/
def hts : Suit -> Nat := fun s =>
  match s with
  | .heart => 8 | .diamond => 10 | .spade => 11 | .club => 10

def bZ : Board := attachAll Board.empty
  [ (Sum.inl Anchor.p1, tC)
  , (Sum.inr tC, zD)
  , (Sum.inr zD, rC)
  , (Sum.inr rC, dS)
  , (Sum.inl Anchor.p2, cH)
  , (Sum.inr cH, tS)
  , (Sum.inr tS, zH)
  , (Sum.inl Anchor.p4, qD)
  , (Sum.inr qD, h10)
  , (Sum.inl Anchor.p0, hK)
  , (Sum.inl Anchor.p5, dK)
  , (Sum.inl Anchor.p6, cK) ]

/-- The state stock: ♥9 as the waste top (cursor 1) — the raiser is a
STOCK card, hence never protected. -/
def dst8 : State := State.mk (Deal.ofList dl) bZ hts (fun _ => 0) (Cycle.mk [h9] 1) 1
def dst8x : State := dst8.exchangeTwinCargo tS

/-! ## The regime checks -/

#eval wfCheck dst8                                                      -- TRUE
#eval wfCheck dst8x                                                     -- TRUE
#eval (dst8.board.topOf (Sum.inr h10)).isNone                           -- false — the blocker NOT stackable yet? no: BARE check
#eval (dst8.apply (Move.pileStack h10)).isSome                          -- FALSE — the blocker CANNOT stack (rung 8 ≠ 9)
#eval (dst8.apply (Move.deckStack h9)).isSome                           -- TRUE — the RAISER stacks from the stock
-- the (i)-check: the raiser is off the protected four, by the rank ladder
-- (8 < 10 = the cargos' rank < 11 = the twins' rank):
#eval (decide (h9.rank.toIdx < zH.rank.toIdx), !(h9 == tS), !(h9 == tC), !(h9 == zH), !(h9 == zD))  -- (true, true, true, true, true)

/-! ## The constructive schedule, both sides -/

/-- The source's constructive schedule: raise, stack the blocker, detour,
merge, climb. -/
def sched : List Move :=
  [ Move.deckStack h9                                   -- (a) RAISE the rung (a stock card — never protected)
  , Move.pileStack h10                                  -- (b) STACK the blocker (the rung now exact)
  , Move.pilePile rC (Sum.inr qD)                       -- (c) THE Z'-DETOUR (r₁'s run onto the bare ♦Q)
  , Move.pilePile cH (Sum.inr dS)                       -- (d) THE MERGE
  , Move.pileStack zH, Move.pileStack tS, Move.pileStack cH, Move.pileStack dS
  , Move.pileStack rC, Move.pileStack zD, Move.pileStack qD, Move.pileStack tC
  , Move.pileStack hK, Move.pileStack dK, Move.pileStack cK ]

/-- The mirror: the SAME four first moves (all exchange-clean), then the
translated climbs (the mirror's post-merge geometry has z' where the
source has z). -/
def schedX : List Move :=
  [ Move.deckStack h9
  , Move.pileStack h10
  , Move.pilePile rC (Sum.inr qD)
  , Move.pilePile cH (Sum.inr dS)
  , Move.pileStack zD, Move.pileStack zH, Move.pileStack tS, Move.pileStack cH
  , Move.pileStack dS, Move.pileStack rC, Move.pileStack qD, Move.pileStack tC
  , Move.pileStack hK, Move.pileStack dK, Move.pileStack cK ]

#eval Option.map State.isWin (dst8.run sched)                           -- some true — the constructive schedule WINS (source)
#eval Option.map State.isWin (dst8x.run schedX)                         -- some true — the mirror WINS too
#eval (dst8.run sched).map (fun W => Suit.all.map (fun s => W.heights s))   -- some [13,13,13,13]

/-! ## The schedule's endpoint: the both-bare licensed state + the merge -/

def π₀' : List Move := [Move.deckStack h9, Move.pileStack h10, Move.pilePile rC (Sum.inr qD)]
def S₀' : State := (dst8.run π₀').getD dst8

#eval wfCheck S₀'                                                       -- TRUE
#eval (S₀'.board.topOf (Sum.inr tS) == some zH,
       S₀'.board.topOf (Sum.inr tC) == some zD)                          -- (true, true) — the covers survive
#eval (S₀'.board.topOf (Sum.inr zH)).isNone                              -- true — z bare
#eval (S₀'.board.topOf (Sum.inr zD)).isNone                              -- true — z' bare (the detour emptied it)
#eval (S₀'.apply (Move.pilePile cH (Sum.inr dS))).isSome                 -- true — the merge re-fires
-- and the mirror's run of the same prefix lands at the exchange of S₀'
-- (the first two moves are unconditionally clean; the third is the
-- validated detour replay):
#eval Board.enumBase.all (fun b =>
  ((dst8x.run π₀').getD dst8x).board.topOf b ==
    (S₀'.exchangeTwinCargo tS).board.topOf b)                            -- TRUE
