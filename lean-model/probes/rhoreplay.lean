import Klondike.Initial
import Klondike.TwinQuotient

/-!
# The ρ-replay probe (L1/O3 part ii — the deferral, investigated)

Three questions, one cast (the w15wfmerge miniature, verbatim):

1. Does the miniature exercise the deferral?  NO — both exhibited
   plays are SEPARATED at the cargo pair z = ♠J (the mid is red-only;
   the spade/club activity sits in the suffix).

2. Does the mid's twin-suit STACKING (the exact-rung ♠Q) break the
   mirror replay?  NOT under the GROWING-ρ correspondence: the mirror
   plays the FLIP (♣Q for ♠Q) at the source's stacking moment — legal,
   the episode's rung exchange — and the correspondence grows by the
   twin transposition τ_{♠Q}.  `playVar` inserts ♠Q INTO the mid
   (non-ortho); `playMir` is the ρ-replay from `wst.swapTwin ♠J`:
   flip at the black moments, the catch-up ♠Q rung-sorted before ♠K.

3. The deferral itself (push ♠Q past the second pair move) also
   commutes on this instance (`playDef`) — the stacking half of part
   (ii) is benign here.  The worry-back hosting shape remains
   unexercised — and, per the ρ-analysis, it DISSOLVES: a mid landing
   on a worried-back card ρ-translates onto the flipped card (the fit
   is twin-blind, the walks are mapByTwin-equivariant) — no commutation
   needed.
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

/-- The cargo-pair relabel of the source state. -/
def wstS : State := wst.swapTwin zS

/-! ## (2) the source variant: ♠Q INSIDE the mid (non-ortho) -/

def playVar : List Move :=
  [ Move.pilePile cH (Sum.inr zC)
  , Move.pileStack bB
  , Move.pileStack zS                       -- pair move 1 (z)
  , Move.pileStack (c_ .diamond .jack)      -- mid (ortho)
  , Move.pileStack tQ                       -- mid (ortho)
  , Move.pileStack cH                       -- mid (ortho)
  , Move.pileStack (c_ .heart .jack)        -- mid (ortho)
  , Move.pileStack (c_ .spade .queen)       -- mid — BLACK, non-ortho!
  , Move.pileStack zC                       -- pair move 2 (z')
  , Move.pileStack xD
  , Move.pileStack tQ2
  , Move.pileStack (c_ .heart .king)
  , Move.pileStack (c_ .spade .king)
  , Move.pileStack (c_ .club .queen)        -- the source's catch-up
  , Move.pileStack (c_ .club .king) ]

/-! ## (3) the deferral variant: ♠Q pushed past the pair move -/

def playDef : List Move :=
  [ Move.pilePile cH (Sum.inr zC)
  , Move.pileStack bB
  , Move.pileStack zS
  , Move.pileStack (c_ .diamond .jack)
  , Move.pileStack tQ
  , Move.pileStack cH
  , Move.pileStack (c_ .heart .jack)
  , Move.pileStack zC
  , Move.pileStack (c_ .spade .queen)       -- deferred
  , Move.pileStack xD
  , Move.pileStack tQ2
  , Move.pileStack (c_ .heart .king)
  , Move.pileStack (c_ .spade .king)
  , Move.pileStack (c_ .club .queen)
  , Move.pileStack (c_ .club .king) ]

/-! ## (2') the ρ-replay: from wst.swapTwin zS, flip-translated -/

def playMir : List Move :=
  [ Move.pilePile cH (Sum.inr zS)          -- the translated merge
  , Move.pileStack bB
  , Move.pileStack zC                       -- FLIP of pair move 1
  , Move.pileStack (c_ .diamond .jack)
  , Move.pileStack tQ
  , Move.pileStack cH
  , Move.pileStack (c_ .heart .jack)
  , Move.pileStack (c_ .club .queen)        -- FLIP of the mid's ♠Q
  , Move.pileStack zS                       -- ρ(z') — pair move 2
  , Move.pileStack xD
  , Move.pileStack tQ2
  , Move.pileStack (c_ .heart .king)
  , Move.pileStack (c_ .spade .queen)       -- ρ(♣Q) — the catch-up, rung-sorted
  , Move.pileStack (c_ .spade .king)
  , Move.pileStack (c_ .club .king) ]

/-- The first failing move's index (none = the whole play runs). -/
def firstFail : State → List Move → Nat → Option Nat
  | _, [], _ => none
  | S, m :: ms, i =>
      match S.apply m with
      | none => some i
      | some S' => firstFail S' ms (i + 1)

#eval Option.map State.isWin (wst.run playVar)
#eval firstFail wst playVar 0
#eval Option.map State.isWin (wst.run playDef)
#eval firstFail wst playDef 0
#eval Option.map State.isWin (wstS.run playMir)
#eval firstFail wstS playMir 0
#eval (wst.run playVar).map (fun W => Suit.all.map (fun s => W.heights s))
#eval (wstS.run playMir).map (fun W => Suit.all.map (fun s => W.heights s))
