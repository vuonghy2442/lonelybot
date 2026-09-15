import Klondike.Initial
import Klondike.TwinBridge

/-! # The equal-heights sufficiency probe (the last hsolw' gap)

At the dblclear2 witness's BOTH-BARE state S₀' (post [deckStack ♥9;
pileStack ♥10; detour]), the pair is z = ♥J (heart rung 10 = z.rank),
z' = ♦J (diamond rung 10) — the SKEW-HOLDING regime: the skew
z.rank(10) ≤ heights (flipSuit z).suit = heights diamond = 10 HOLDS.
The equal-heights sufficiency route validated empirically:

* the ADJACENT-HEAD play [pileStack z; pileStack z'; the translated
  climbs] runs to a WIN (#eval some true, heights [13,13,13,13]);
* its `playWindow'` value is TRUE (the skew-holding branch: both
  stackings admitted via the skew arms, the twin rungs EQUALIZING at
  z.rank+1 = 11, the tail then fully PRE-admitted — every on-suit
  climb move's skew holds from the raised partner rung; no
  worry-backs in the tail);
* the two components the theorem composes: `adjacent_pair_skew`'s
  derived second skew (11 ≥ 11) and the tail's admission — both
  visible in the dump below.

Also recorded: the rung-raiser NON-commutability that blocks the pure
adjacency normalization (the second stacking's firing rung is RAISED by
the z'-suit deckStacks/pileStacks between the stackings — commuting it
past them breaks its firing) — the reason the adjacent-head shape stays
a premise rather than a derived normalization. -/

/-! ## The kit + cast (dblclear2.lean, verbatim) -/

def rankOfIdx : Nat -> Rank
  | 0 => .ace | 1 => .two | 2 => .three | 3 => .four | 4 => .five | 5 => .six
  | 6 => .seven | 7 => .eight | 8 => .nine | 9 => .ten | 10 => .jack | 11 => .queen
  | _ => .king

def cardStr (c : Card) :=
  (if c.suit = Suit.heart then "H"
   else if c.suit = Suit.diamond then "D"
   else if c.suit = Suit.spade then "S"
   else "C") ++ (match c.rank with
  | .ace => "A" | .two => "2" | .three => "3" | .four => "4" | .five => "5"
  | .six => "6" | .seven => "7" | .eight => "8" | .nine => "9" | .ten => "10"
  | .jack => "J" | .queen => "Q" | .king => "K")

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
  Card.universe.all (fun c => !(st.isVis c) || st.stock.posOf c == none) &&
  Card.universe.all (fun c => !(st.onFound c) || st.stock.posOf c == none) &&
  Card.universe.all (fun c => !decide (c.rank.toIdx < st.heights c.suit) ||
      (!(st.isVis c) && st.stock.posOf c == none &&
        Anchor.all.all (fun a => !((st.hidden a).contains c)))) &&
  Card.universe.all (fun c => !(st.isVis c) ||
    Anchor.all.all (fun a => !((st.hidden a).contains c))) &&
  Suit.all.all (fun s => decide (st.heights s <= 13)) &&
  decide (st.stock.cursor <= st.stock.cards.length) &&
  0 < st.drawStep &&
  nodupB st.stock.cards &&
  st.stock.cards.all (fun c => st.deal.stock.contains c)

def c_ (s : Suit) (r : Rank) : Card := Card.mk s r

def tS : Card := c_ .spade .queen
def tC : Card := c_ .club .queen
def zH : Card := c_ .heart .jack
def zD : Card := c_ .diamond .jack
def cH : Card := c_ .heart .queen
def rC : Card := c_ .club .jack
def dS : Card := c_ .spade .king
def qD : Card := c_ .diamond .queen
def h10 : Card := c_ .heart .ten
def h9 : Card := c_ .heart .nine
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

def dst8 : State := State.mk (Deal.ofList dl) bZ hts (fun _ => 0) (Cycle.mk [h9] 1) 1

/-- The both-bare post-clearing state (the schedule's endpoint). -/
def π₀' : List Move := [Move.deckStack h9, Move.pileStack h10, Move.pilePile rC (Sum.inr qD)]
def S₀' : State := (dst8.run π₀').getD dst8

/-- The equal-heights adjacent-head play: [pileStack z; pileStack z';
the translated climbs]. -/
def eqPlay : List Move :=
  [ Move.pileStack zH, Move.pileStack zD
  , Move.pileStack tS, Move.pileStack cH, Move.pileStack dS
  , Move.pileStack rC, Move.pileStack qD, Move.pileStack tC
  , Move.pileStack hK, Move.pileStack dK, Move.pileStack cK ]

/-! ## The regime + the validation -/

#eval wfCheck S₀'                                                        -- TRUE
#eval (S₀'.board.topOf (Sum.inr tS) == some zH,
       S₀'.board.topOf (Sum.inr tC) == some zD)                          -- (true, true) — the covers
#eval ((S₀'.board.topOf (Sum.inr zH)).isNone,
       (S₀'.board.topOf (Sum.inr zD)).isNone)                            -- (true, true) — both bare
-- the SKEW-HOLDING regime at S₀':
#eval (zH.rank.toIdx, S₀'.heights (Card.flipSuit zH).suit)                 -- (10, 10) — the skew HOLDS (equality)
-- the adjacent-head play WINS:
#eval Option.map State.isWin (S₀'.run eqPlay)                            -- some true
#eval (S₀'.run eqPlay).map (fun W => Suit.all.map (fun s => W.heights s))  -- some [13,13,13,13]
-- AND its playWindow' value is TRUE (the sufficiency route, empirically):
#eval State.playWindow' zH zH.suit State.WindowEp.pre S₀' eqPlay          -- TRUE
-- the components: the twin rungs EQUALIZE at z.rank+1 = 11 after the head:
#eval ((S₀'.run [Move.pileStack zH, Move.pileStack zD]).getD S₀').heights Suit.heart  -- 11
#eval ((S₀'.run [Move.pileStack zH, Move.pileStack zD]).getD S₀').heights Suit.diamond -- 11
-- and the second stacking's DERIVED skew (adjacent_pair_skew's content):
#eval ((S₀'.apply (Move.pileStack zH)).getD S₀').heights Suit.heart       -- 11 ≥ z'.rank = 10 ✓
-- the tail alone (from the post-head state) is fully PRE-admitted:
#eval State.playWindow' zH zH.suit State.WindowEp.pre
    ((S₀'.run [Move.pileStack zH, Move.pileStack zD]).getD S₀')
    [Move.pileStack tS, Move.pileStack cH, Move.pileStack dS, Move.pileStack rC,
     Move.pileStack qD, Move.pileStack tC, Move.pileStack hK, Move.pileStack dK,
     Move.pileStack cK]                                                   -- TRUE
