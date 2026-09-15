import Klondike.Initial
import Klondike.TwinQuotient

/-! # The double-clearing probe — witness-or-hope for `ExchangeDoubleClear`

**The regime map** (the mission's Q1, probed at detour.lean's blockade
witness — the non-king rider whose both candidate tops are occupied and
the free anchor is king-locked):

* **(a) The trivial regime**: at a BOTH-BARE licensed state the premise
  holds with π = [] — every clause is the hypothesis set of
  `solvable_of_exchange_merge_direct` itself.  Here S₀ (the witness
  after the full clearing π₀ + the detour) is such a state.
* **(b) The rider-carrying regime**: at the witness dst the
  double-clearing prefix exists — π₀ = [pileStack ♥10 (clearing the
  blocker), pilePile ♣J (inr ♦Q) (the z'-detour)] — and the mirror
  replays it VERBATIM (the premise's second clause): the exchanged
  state's run of π₀ lands exactly at the exchange of the source's π₀-end
  state, field by field (the board per seat, the heights per suit, the
  deal piles, the depths, the stock, the draw step).  This is the
  empirical content of the replay clause at a real blockade witness;
  playIter/playIterX (detour.lean) already showed both sides WIN through
  [π₀; merge; climbs].
* **(c) The failure-mode search (the cycle blockade)**: the attempted
  construction — a rider r whose candidate tops are both occupied by
  riders whose OWN candidate tops are occupied circularly, with the
  anchors filled and the rungs too low — dissolves at the solvability
  hypothesis: the rung can always be raised through the stock (draws are
  clean, deckStacks are clean, and a rider's suit is disjoint from both
  cargos' suits — the fit's color structure — so no rung-raiser is ever
  a protected card; the twin shares at most the suit, never the rung).
  The two known blockades (detour.lean's, detour2.lean's) are dissolved
  by ONE clean stack each — playIter2/playIter2X validate the second
  (king, all anchors filled) identically.  No refuting witness found; the
  residue is the SCHEDULING (the commutation), not a hard blockade —
  see the report.
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

/-! ## detour.lean's cast (verbatim) -/

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

def hts : Suit -> Nat := fun s =>
  match s with
  | .heart => 9 | .diamond => 10 | .spade => 11 | .club => 10

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

def dst : State := State.mk (Deal.ofList dl) bZ hts (fun _ => 0) (Cycle.mk [] 0) 1
def dstx : State := dst.exchangeTwinCargo tS

/-- The double-clearing prefix π₀: clear the blocker (a clean stack —
♥10 is off both pairs), then the z'-detour (a clean run move). -/
def π₀ : List Move := [Move.pileStack h10, Move.pilePile rC (Sum.inr qD)]

/-- The both-bare end state S₀ = dst after π₀. -/
def S₀ : State := (dst.run π₀).getD dst

/-- The merge's successor climb from S₀ (playIter's tail). -/
def climbTail : List Move :=
  [ Move.pilePile cH (Sum.inr dS)
  , Move.pileStack zH, Move.pileStack tS, Move.pileStack cH, Move.pileStack dS
  , Move.pileStack rC, Move.pileStack zD, Move.pileStack qD, Move.pileStack tC
  , Move.pileStack hK, Move.pileStack dK, Move.pileStack cK ]

/-! ## (a) The trivial regime: S₀ is both-bare, licensed, the merge re-fires,
the successor solvable — ExchangeDoubleClear with π = [] -/

#eval wfCheck dst                                                       -- TRUE
#eval wfCheck dstx                                                      -- TRUE
#eval wfCheck S₀                                                        -- TRUE
#eval (S₀.board.topOf (Sum.inr tS) == some zH,
       S₀.board.topOf (Sum.inr tC) == some zD)                          -- (true, true) — the covers
#eval (S₀.board.topOf (Sum.inr zH)).isNone                              -- true — z bare
#eval (S₀.board.topOf (Sum.inr zD)).isNone                              -- true — z' bare (the detour emptied it)
#eval (S₀.apply (Move.pilePile cH (Sum.inr dS))).isSome                 -- true — the merge re-fires at S₀
#eval Option.map State.isWin (S₀.run climbTail)                         -- some true — the successor solvable
-- so at S₀ the premise holds with π = [] (the direct bridge's own regime).

/-! ## (b) The verbatim-replay clause, empirically: the mirror's run of π₀
lands exactly at the exchange of the source's π₀-end -/

#eval Board.enumBase.all (fun b =>
  ((dstx.run π₀).getD dstx).board.topOf b ==
    (S₀.exchangeTwinCargo tS).board.topOf b)                            -- TRUE — the boards agree per seat
#eval Suit.all.all (fun s =>
  ((dstx.run π₀).getD dstx).heights s == (S₀.exchangeTwinCargo tS).heights s)  -- TRUE
#eval Anchor.all.all (fun a =>
  ((dstx.run π₀).getD dstx).deal.piles a == (S₀.exchangeTwinCargo tS).deal.piles a)  -- TRUE
#eval Anchor.all.all (fun a =>
  ((dstx.run π₀).getD dstx).depths a == (S₀.exchangeTwinCargo tS).depths a)  -- TRUE
#eval (((dstx.run π₀).getD dstx).stock.cards == (S₀.exchangeTwinCargo tS).stock.cards,
       ((dstx.run π₀).getD dstx).drawStep == (S₀.exchangeTwinCargo tS).drawStep)  -- (true, true)
/-- The mirror's WIN through [π₀; merge; climbs] — with the TRANSLATED
climb (the mirror's post-merge geometry has z' where the source has z:
the merge moved [c; t; z'] onto d in the mirror, so z' stacks before t;
this is detour.lean's playIterX, re-run here from the π₀-prefixed
start).  The premise itself needs no mirror play — the direct route
derives the win from the correspondence — this is belt-and-braces. -/
def climbTailX : List Move :=
  [ Move.pilePile cH (Sum.inr dS)
  , Move.pileStack zD, Move.pileStack zH, Move.pileStack tS, Move.pileStack cH
  , Move.pileStack dS, Move.pileStack rC, Move.pileStack qD, Move.pileStack tC
  , Move.pileStack hK, Move.pileStack dK, Move.pileStack cK ]
#eval Option.map State.isWin (dstx.run (π₀ ++ climbTailX))              -- some true — the mirror wins too
