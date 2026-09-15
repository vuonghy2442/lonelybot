import Klondike.Initial
import Klondike.TwinQuotient

/-!
# The DETOUR-BASE probe III — Q2: does the detour break the merge's premises?

fithole's witness, re-run, plus the checks fithole did not run: at `stD` (the
state after the rider detour `pilePile ♥K (inl p0)`), the FULL license
(`TwinLicensedAt`-shape) still holds — both twins visible, both cargos still
seated on them, both fits (card-intrinsic), and both no-braid premises now
TRIVIAL (the detour emptied z' and z was already bare: both `aboveOf` walks
are `[]`) — and the merge's own guard still holds: d = ♠Q rode along on p0 and
is STILL BARE, the fit `canSitOn ♦J ♠Q` is card-intrinsic, and the
self-landing guard survives because THE DETOUR CANNOT LAND INSIDE c's RUN:
the only bare card of c's run is z (the riders-cleared top — t is occupied by
z), and the hole hypothesis `canSitOn r₁ z = false` kills exactly that base.
This is the structural reason the detour is harmless to the merge: nothing it
can legally do touches any premise the merge needs.

Also recorded: the mirror-replay premise the bridge's `exchangeTwinCargo_step_
pilePile` consumes (t, t' ∉ aboveOf r₁ — `first_rider_off`'s conclusion
shape), which holds at both this cast and the blockade witnesses.
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

/-! ## fithole's cast (verbatim) -/

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

def dl : List Card :=
  [c_ .diamond .two]                                            -- p0: pad (anchor p0 EMPTY — the detour's target)
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

-- the basic re-confirmation (fithole's own checks)
#eval wfCheck fst                                                      -- TRUE
#eval wfCheck fstx                                                     -- TRUE
#eval (canSitOn rH zS, canSitOn rH zC)                                 -- (false, false) — THE HOLE
#eval (fst.board.topOf (Sum.inr zS)).isNone                            -- true — z bare
#eval (fst.apply (Move.pilePile cJ (Sum.inr qS))).isSome                 -- true — the deep merge LEGAL
#eval (fst.apply (Move.pilePile rH (Sum.inl Anchor.p0))).isSome          -- TRUE — the detour EXISTS here (p0 free)

/-- The detoured states (source and exchanged). -/
def stD : State := (fst.apply (Move.pilePile rH (Sum.inl Anchor.p0))).getD fst
def stxD : State := (fstx.apply (Move.pilePile rH (Sum.inl Anchor.p0))).getD fstx

/-! ## Q2(b): the license SURVIVES the detour (TwinLicensedAt at stD) -/

#eval (stD.isVis tH, stD.isVis tD)                                     -- (true, true) — twins still visible
#eval (stD.board.bottomOf zS == some (Sum.inr tH),
       stD.board.bottomOf zC == some (Sum.inr tD))                      -- (true, true) — cargos STILL SEATED
#eval (canSitOn zS tH, canSitOn zC tD)                                  -- (true, true) — the fits (card-intrinsic)
#eval ((stD.board.aboveOf zS).map cardStr, (stD.board.aboveOf zC).map cardStr)  -- ([], []) — BOTH walks EMPTY: no-braids trivial
#eval (!(stD.board.aboveOf zS).contains tH && !(stD.board.aboveOf zS).contains tD,
       !(stD.board.aboveOf zC).contains tH && !(stD.board.aboveOf zC).contains tD)  -- (true, true) — no braids
#eval (stD.board.topOf (Sum.inr zS)).isNone                            -- true — z still bare
#eval (stD.board.topOf (Sum.inr zC)).isNone                            -- true — z' NOW bare too (the detour emptied it)

/-! ## Q2(b): the merge's OWN guard survives the detour -/

#eval (stD.board.topOf (Sum.inr qS)).isNone                            -- true — d STILL BARE (it rode to p0)
#eval (stD.isVis qS, canSitOn cJ qS)                                   -- (true, true) — the landing's isVis + fit
#eval !(stD.board.aboveOf cJ).contains qS                              -- true — the self-landing guard SURVIVES
#eval (stD.apply (Move.pilePile cJ (Sum.inr qS))).isSome                 -- true — the merge RE-FIRES at stD
#eval (stxD.apply (Move.pilePile cJ (Sum.inr qS))).isSome                -- true — and at stxD (the passing shape)

/-! ## Q2(b): WHY the self-landing guard survives — the detour cannot land in c's run -/

-- the run above c: t (occupied by z) and z (bare) — z is the ONLY bare card of the run
#eval (fst.board.aboveOf cJ).map cardStr                                -- [SJ, HQ] — t and z above c
#eval ((fst.board.topOf (Sum.inr tH)).isSome, (fst.board.topOf (Sum.inr zS)).isSome)  -- (true, false)
-- ... and the hole kills exactly that base:
#eval (canSitOn rH zS)                                                 -- false — THE HOLE IS THE GUARD
-- the detour-clean premise (exchangeTwinCargo_step_pilePile's replay condition):
#eval (!(fst.board.aboveOf rH).contains tH && !(fst.board.aboveOf rH).contains tD)   -- true — t, t' ∉ aboveOf r₁

/-! ## Q2(a): the plays (re-run of fithole's, for the record) -/

/-- The SOURCE's win THROUGH the deep merge (13 moves). -/
def playDeep : List Move :=
  [ Move.pilePile cJ (Sum.inr qS)                    -- 1. THE DEEP MERGE
  , Move.pileStack hJ, Move.pileStack zS, Move.pileStack tH, Move.pileStack cJ
  , Move.pileStack qS, Move.pileStack rH, Move.pileStack zC, Move.pileStack tD
  , Move.pileStack cQ, Move.pileStack dK, Move.pileStack cK, Move.pileStack sK ]

/-- The SOURCE, NORMALIZED: the detour first, then the (now off-cargo) merge (14). -/
def playNorm : List Move :=
  [ Move.pilePile rH (Sum.inl Anchor.p0)             -- 1. THE DETOUR: r₁'s run [♥K, ♠Q] to p0
  , Move.pilePile cJ (Sum.inr qS)                     -- 2. the merge onto d — no longer deep
  , Move.pileStack hJ, Move.pileStack zS, Move.pileStack tH, Move.pileStack cJ
  , Move.pileStack qS, Move.pileStack rH, Move.pileStack zC, Move.pileStack tD
  , Move.pileStack cQ, Move.pileStack dK, Move.pileStack cK, Move.pileStack sK ]

/-- The EXCHANGED state's REPAIR PLAY (the same two moves, translated climbs). -/
def playMir : List Move :=
  [ Move.pilePile rH (Sum.inl Anchor.p0)             -- 1. the SAME detour (clean)
  , Move.pilePile cJ (Sum.inr qS)                     -- 2. the SAME merge
  , Move.pileStack hJ, Move.pileStack zC, Move.pileStack tH, Move.pileStack cJ
  , Move.pileStack zS, Move.pileStack qS, Move.pileStack rH, Move.pileStack tD
  , Move.pileStack cQ, Move.pileStack dK, Move.pileStack cK, Move.pileStack sK ]

#eval Option.map State.isWin (fst.run playDeep)       -- some true — the merge on a winning line
#eval firstFail fst playDeep 0                         -- none
#eval Option.map State.isWin (fst.run playNorm)       -- some true — THE DETOUR-PREPENDED SOURCE WINS
#eval firstFail fst playNorm 0                         -- none
#eval Option.map State.isWin (fstx.run playMir)        -- some true — the mirror repair wins
#eval firstFail fstx playMir 0                         -- none
#eval (fst.run playNorm).map (fun W => Suit.all.map (fun s => W.heights s))    -- some [13,13,13,13]
#eval (fstx.run playMir).map (fun W => Suit.all.map (fun s => W.heights s))   -- some [13,13,13,13]
