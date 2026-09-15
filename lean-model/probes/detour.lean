import Klondike.Initial
import Klondike.TwinQuotient

/-!
# The DETOUR-BASE probe (route step 2b-deep — Q1: can the rider-detach be BLOCKED at WF?)

**FINDING: BLOCKABLE — `State.ExchangeDeepNorm`'s detach-existence half is FALSE at WF.**

The witness `dst` is WF (all 11 conjuncts, for BOTH `dst` and the exchanged
`dstx`) and twinLicensed at t = ♠Q; the merge `pilePile ♥Q (inr ♠K)` is a DEEP
landing (d = ♠K rides r₁ = ♣J on z' = ♦J, d ≠ z'), legal, and on the source's
winning line (`playDeep`, 13 moves).  The FIRST RIDER r₁ = ♣J sits on z' by
DEAL-ADJACENCY — (♦J, ♣J) consecutive in pile p3 — and fits NEITHER cargo
(`canSitOn ♣J ♥J = false`, twin-blindly `canSitOn ♣J ♦J = false`), so the 2b
rider transfer `pilePile r₁ (inr z)` is ILLEGAL in the exchanged state and the
mirror merge is self-landing there.

**THE BLOCKADE (the new content):** r₁ = ♣J is a NON-KING, so the anchor route
is closed by the `canPlace_inl_iff` guard itself (rank = king) — even the FREE
anchor p3 does not serve a jack.  r₁'s candidate tops are the two red queens
{♥Q, ♦Q} (rank 11 = rank(♣J)+1, opposite color):
  * ♥Q IS THE MERGE ROOT c ITSELF — occupied by its own run (t = ♠Q rides c);
  * ♦Q carries the deal-adjacent blocker ♥10 (pair (♦Q, ♥10) in pile p4).
So EVERY base β is blocked: `Board.enumBase.all (fun b => !(dst.apply
(Move.pilePile r₁ b)).isSome)` = TRUE — no detach exists AT ALL, hence
`State.ExchangeDeepNorm ♠Q ♥J ♦J ♥Q (inr ♠K)` FAILS at this state although all
its hypotheses hold (WF, licensed, riders-cleared, t ∈ aboveOf c, r₁ on z',
the hole, the merge firing, A solvable via the 12-stack climb).

**THE REPAIR SHAPE (validated, both sides):** the normalization ITERATES —
clear the blocker first (`pileStack ♥10`, legal at dst since heart height 9 =
rank(♥10)), THEN the detach `pilePile ♣J (inr ♦Q)` fires (♦Q now bare), THEN
the same merge, then the same climbs: `playIter` wins from dst and `playIterX`
(the same three moves, then translated climbs) wins from dstx.  This is the
evidence for the recommended premise repair: a CLEAN CLEARING PREFIX before
the detach (see the report).

Cast: t = ♠Q, t' = ♣Q, z = ♥J, z' = ♦J, c = ♥Q, r₁ = ♣J, d = ♠K,
blocker = ♥10 on ♦Q; heights (heart 9, diamond 10, spade 11, club 10);
kings ♥K/♦K/♣K bare on anchors p0/p5/p6 (anchor p3 left FREE to demonstrate
the king-guard, not occupancy, is what closes the anchor route).
-/

/-! ## The kit (w15wfmerge.lean / fithole.lean, verbatim) -/

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

def tS : Card := c_ .spade .queen        -- t  (the licensed twin)
def tC : Card := c_ .club .queen         -- t' = t.flipSuit
def zH : Card := c_ .heart .jack          -- z  (the cargo on t)
def zD : Card := c_ .diamond .jack        -- z' = z.flipSuit (the cargo on t')
def cH : Card := c_ .heart .queen          -- c  (the merge's root) — ALSO r₁'s candidate #1
def rC : Card := c_ .club .jack            -- r₁ (the first rider — DEAL-ADJACENT on z', NON-KING)
def dS : Card := c_ .spade .king            -- d  (the deep landing, DEAL-ADJ on r₁, BARE)
def qD : Card := c_ .diamond .queen        -- r₁'s candidate #2 (carries the blocker)
def h10 : Card := c_ .heart .ten           -- THE BLOCKER (deal-adj rider on ♦Q)
def hK : Card := c_ .heart .king
def dK : Card := c_ .diamond .king
def cK : Card := c_ .club .king

/-- The deal: p1 head = t'; p2 = [c, t, z] (the t-edge pair (♥Q, ♠Q), z
fit-seated); p3 = [pad, z', r₁, d] (the RIDER pair (♦J, ♣J) and the d-pair
(♣J, ♠K)); p4 = [♦Q, ♥10, ...] (the BLOCKER pair (♦Q, ♥10)); anchors p0/p5/p6
host the kings; p0's head is an unplaced pad, so anchor p3 is FREE (to show the
king-guard, not occupancy, closes the anchor route). -/
def dl : List Card :=
  [c_ .heart .king]                                          -- p0: ♥K (head, king)
  ++ [c_ .club .queen, c_ .heart .ace]                        -- p1: t' = ♣Q (head) + pad
  ++ [c_ .heart .queen, c_ .spade .queen, c_ .heart .jack]     -- p2: c = ♥Q (head) < t = ♠Q (pair); z = ♥J
  ++ [c_ .spade .ace, c_ .diamond .jack, c_ .club .jack, c_ .spade .king]  -- p3: pad, z' < r₁ (pair), d (pair)
  ++ [c_ .diamond .queen, c_ .heart .ten, c_ .heart .two, c_ .heart .three, c_ .heart .four]  -- p4: ♦Q (head) + blocker ♥10
  ++ [c_ .diamond .king, c_ .spade .two, c_ .spade .three, c_ .spade .four, c_ .spade .five, c_ .spade .six]  -- p5: ♦K (head)
  ++ [c_ .club .king, c_ .club .ace, c_ .club .two, c_ .club .three, c_ .club .four, c_ .club .five, c_ .club .six]  -- p6: ♣K (head)
  ++ [c_ .heart .five, c_ .heart .six, c_ .heart .seven, c_ .heart .eight, c_ .heart .nine,
      c_ .diamond .ace, c_ .diamond .two, c_ .diamond .three, c_ .diamond .four, c_ .diamond .five,
      c_ .diamond .six, c_ .diamond .seven, c_ .diamond .eight, c_ .diamond .nine, c_ .diamond .ten,
      c_ .spade .seven, c_ .spade .eight, c_ .spade .nine, c_ .spade .ten, c_ .spade .jack,
      c_ .club .seven, c_ .club .eight, c_ .club .nine, c_ .club .ten]  -- stock (24, all below height)

def hts : Suit -> Nat := fun s =>
  match s with
  | .heart => 9 | .diamond => 10 | .spade => 11 | .club => 10

def bZ : Board := attachAll Board.empty
  [ (Sum.inl Anchor.p1, tC)          -- t' = ♣Q (p1's head)
  , (Sum.inr tC, zD)                 -- z' = ♦J on t' (fit)
  , (Sum.inr zD, rC)                 -- r₁ = ♣J on z' (DEAL-ADJ: the p3 pair) — THE HOLE EDGE
  , (Sum.inr rC, dS)                 -- d = ♠K on r₁ (DEAL-ADJ: the p3 pair) — BARE
  , (Sum.inl Anchor.p2, cH)          -- c = ♥Q (p2's head) — r₁'s candidate #1
  , (Sum.inr cH, tS)                 -- t = ♠Q on c (DEAL-ADJ: the p2 pair)
  , (Sum.inr tS, zH)                 -- z = ♥J on t (fit; BARE — riders-cleared)
  , (Sum.inl Anchor.p4, qD)          -- ♦Q (p4's head) — r₁'s candidate #2
  , (Sum.inr qD, h10)                -- ♥10 on ♦Q (DEAL-ADJ: the p4 pair) — THE BLOCKER
  , (Sum.inl Anchor.p0, hK)          -- ♥K (king)
  , (Sum.inl Anchor.p5, dK)          -- ♦K (king)
  , (Sum.inl Anchor.p6, cK) ]        -- ♣K (king)

def dst : State := State.mk (Deal.ofList dl) bZ hts (fun _ => 0) (Cycle.mk [] 0) 1
def dstx : State := dst.exchangeTwinCargo tS

/-! ## Q1: the witness is WF and licensed -/

#eval dl.length                                                       -- 52
#eval (Deal.ofList dl).piles Anchor.p2 |>.map cardStr                  -- [HQ, SQ, HJ] — the t-edge pair (♥Q, ♠Q)
#eval (Deal.ofList dl).piles Anchor.p3 |>.map cardStr                  -- [SA, DJ, CJ, SK] — the RIDER pair (♦J, ♣J), the d-pair (♣J, ♠K)
#eval (Deal.ofList dl).piles Anchor.p4 |>.map cardStr                  -- [DQ, H10, H2, H3, H4] — the BLOCKER pair (♦Q, ♥10)

#eval wfCheck dst                                                     -- TRUE — all 11 conjuncts
#eval wfCheck dstx                                                    -- TRUE

-- diagnostics (clean = empty)
#eval Board.enumBase.filterMap (fun b =>
  match dst.board.topOf b with
  | none => none
  | some c => if (dst.board.bottomOf c == some b) && edgeOK dst b c then none
    else some (baseStr b ++ " <- " ++ cardStr c))
#eval (Card.universe.filter (fun c =>
  decide (c.rank.toIdx < dst.heights c.suit) &&
    (dst.isVis c || (dst.stock.posOf c).isSome ||
      Anchor.all.any (fun a => (dst.hidden a).contains c)))).map cardStr
#eval String.intercalate "; " (Board.enumBase.filterMap (fun b =>
  (dst.board.topOf b).map (fun c => baseStr b ++ " <- " ++ cardStr c)))
#eval Suit.all.map (fun s => (s, dst.heights s))

-- the license at t = ♠Q (TwinLicensedAt, unpacked)
#eval (tC == tS.flipSuit, zD == zH.flipSuit)                           -- (true, true) — the twin pairs
#eval (dst.isVis tS, dst.isVis tC)                                     -- (true, true)
#eval (dst.board.bottomOf zH == some (Sum.inr tS),
       dst.board.bottomOf zD == some (Sum.inr tC))                      -- (true, true) — cargos on the twins
#eval (canSitOn zH tS, canSitOn zD tC)                                 -- (true, true) — both fits
#eval (!(dst.board.aboveOf zH).contains tS && !(dst.board.aboveOf zH).contains tC,
       !(dst.board.aboveOf zD).contains tS && !(dst.board.aboveOf zD).contains tC)  -- (true, true) — no braids
#eval (dst.board.topOf (Sum.inr zH)).isNone                            -- true — z bare (riders-cleared)

-- the deep merge and its shape
#eval (dst.board.aboveOf zD).map cardStr                                -- [SK, CJ] — d and r₁ above z'
#eval ((dst.board.aboveOf zD).contains dS, dS != zD)                    -- (true, true) — DEEP (d ≠ z')
#eval (dst.board.topOf (Sum.inr zD) == some rC,
       dst.board.bottomOf rC == some (Sum.inr zD))                     -- (true, true) — r₁ DIRECTLY on z'
#eval (dst.board.aboveOf cH).map cardStr                                -- [HJ, SQ] — c's run passes t
#eval (dst.board.aboveOf cH).contains tS                               -- true — t ∈ aboveOf c
#eval (dst.apply (Move.pilePile cH (Sum.inr dS))).isSome                 -- true — the deep merge LEGAL

/-! ## Q1: THE HOLE and THE BLOCKADE -/

#eval (canSitOn rC zH, canSitOn rC zD)                                 -- (false, false) — THE HOLE (twin-blind)
#eval consec (dst.deal.piles Anchor.p3) zD rC                          -- true — (♦J, ♣J) consecutive in p3
#eval consec (dst.deal.piles Anchor.p3) rC dS                          -- true — (♣J, ♠K) consecutive in p3
#eval consec (dst.deal.piles Anchor.p2) cH tS                          -- true — (♥Q, ♠Q) consecutive in p2
#eval consec (dst.deal.piles Anchor.p4) qD h10                         -- true — (♦Q, ♥10) consecutive in p4
#eval (edgeOK dst (Sum.inr zD) rC, edgeOK dst (Sum.inr rC) dS)        -- (true, true) — both rider edges justified

-- THE BLOCKADE: r₁ = ♣J is a NON-KING — the anchor route is closed by the guard itself
#eval (rC.rank == Rank.king)                                          -- false — ♣J is a jack
#eval (dst.board.topOf (Sum.inl Anchor.p3)).isNone                    -- true — anchor p3 is FREE...
#eval (dst.apply (Move.pilePile rC (Sum.inl Anchor.p3))).isSome        -- false — ...and STILL no serve (king guard)

-- the two candidate tops (rank 11, red — the opposite-color rank+1 pair):
#eval (canSitOn rC cH, canSitOn rC qD)                                -- (true, true) — both FIT
#eval (dst.board.topOf (Sum.inr cH)).map cardStr                       -- some "SQ" — candidate #1 = c, OCCUPIED by its own run
#eval (dst.board.topOf (Sum.inr qD)).map cardStr                       -- some "H10" — candidate #2, OCCUPIED by the blocker
#eval (dst.board.topOf (Sum.inr zH)).map cardStr                       -- none — z bare but the hole kills it
#eval (dst.board.topOf (Sum.inr zD)).map cardStr                       -- some "CJ" — z' hosts r₁ itself

-- THE SWEEP: NO detach base exists at all
#eval Board.enumBase.all (fun b => !(dst.apply (Move.pilePile rC b)).isSome)   -- TRUE — NO DETACH EXISTS

-- the exchanged state: the hole is LIVE there (the mirror problem)
#eval (dstx.board.topOf (Sum.inr tS)).map cardStr                       -- some "DJ" — z' rides t in stx
#eval (dstx.board.aboveOf cH).map cardStr                                -- [SK, CJ, DJ, SQ] — d inside c's run
#eval (dstx.apply (Move.pilePile cH (Sum.inr dS))).isSome                -- FALSE — the mirror merge SELF-LANDS
#eval (dstx.apply (Move.pilePile rC (Sum.inr zH))).isSome                -- FALSE — the RIDER TRANSFER dies (the hole)
-- the detour-clean premise for the bridge's mirror replay (first_rider_off's shape)
#eval (!(dst.board.aboveOf rC).contains tS && !(dst.board.aboveOf rC).contains tC)  -- true — t, t' ∉ aboveOf r₁

/-! ## The plays -/

/-- The merge successor A (for the A.solvableFrom hypothesis). -/
def aA : State := (dst.apply (Move.pilePile cH (Sum.inr dS))).getD dst

/-- The climb from A (12 stacks; also playDeep's tail). -/
def playClimb : List Move :=
  [ Move.pileStack h10                       -- ♥10 (heart 9→10) — frees ♦Q
  , Move.pileStack zH                        -- z = ♥J (heart 10→11)
  , Move.pileStack tS                        -- t = ♠Q (spade 11→12)
  , Move.pileStack cH                        -- c = ♥Q (heart 11→12)
  , Move.pileStack dS                        -- d = ♠K (spade 12→13)
  , Move.pileStack rC                        -- r₁ = ♣J (club 10→11)
  , Move.pileStack zD                        -- z' = ♦J (diamond 10→11)
  , Move.pileStack tC                        -- t' = ♣Q (club 11→12)
  , Move.pileStack qD                        -- ♦Q (diamond 11→12)
  , Move.pileStack hK                        -- ♥K (heart 12→13)
  , Move.pileStack dK                        -- ♦K (diamond 12→13)
  , Move.pileStack cK ]                      -- ♣K (club 12→13)

/-- The SOURCE's win THROUGH the deep merge (13 moves). -/
def playDeep : List Move := Move.pilePile cH (Sum.inr dS) :: playClimb

/-- The SOURCE, NORMALIZED the ITERATED way: clear the blocker first, THEN the
detach, THEN the same merge — the strengthened premise's shape (14 moves). -/
def playIter : List Move :=
  [ Move.pileStack h10                       -- 1. CLEAR the blocker (heart 9→10) — ♦Q goes bare
  , Move.pilePile rC (Sum.inr qD)            -- 2. THE DETOUR: r₁'s run [♣J, ♠K] onto the now-bare ♦Q
  , Move.pilePile cH (Sum.inr dS)            -- 3. the merge onto d — the run left the cargo seat
  , Move.pileStack zH, Move.pileStack tS, Move.pileStack cH, Move.pileStack dS
  , Move.pileStack rC, Move.pileStack zD, Move.pileStack qD, Move.pileStack tC
  , Move.pileStack hK, Move.pileStack dK, Move.pileStack cK ]

/-- The EXCHANGED state's REPAIR PLAY: the same clearing move, the same detour,
the same merge (all legal there too), then translated climbs (14). -/
def playIterX : List Move :=
  [ Move.pileStack h10                       -- 1. CLEAR (same — the blocker stack is off the pair)
  , Move.pilePile rC (Sum.inr qD)            -- 2. THE DETOUR (clean in the mirror too)
  , Move.pilePile cH (Sum.inr dS)            -- 3. THE MERGE (d is off c's run in stx too)
  , Move.pileStack zD, Move.pileStack zH, Move.pileStack tS, Move.pileStack cH
  , Move.pileStack dS, Move.pileStack rC, Move.pileStack qD, Move.pileStack tC
  , Move.pileStack hK, Move.pileStack dK, Move.pileStack cK ]

#eval Option.map State.isWin (aA.run playClimb)       -- some true — A.solvableFrom (the hypothesis)
#eval firstFail aA playClimb 0                         -- none
#eval Option.map State.isWin (dst.run playDeep)       -- some true — the merge is on a winning line
#eval firstFail dst playDeep 0                         -- none
#eval (dst.run playDeep).map (fun W => Suit.all.map (fun s => W.heights s))    -- some [13,13,13,13]
#eval Option.map State.isWin (dst.run playIter)       -- some true — the ITERATED NORMALIZATION wins
#eval firstFail dst playIter 0                         -- none
#eval Option.map State.isWin (dstx.run playIterX)     -- some true — the mirror repair wins
#eval firstFail dstx playIterX 0                       -- none
#eval (dstx.run playIterX).map (fun W => Suit.all.map (fun s => W.heights s))  -- some [13,13,13,13]
