import Klondike.Initial
import Klondike.TwinQuotient

/-!
# The FIT-HOLE probe II — the CONTROL (the rider FITS: the premise
repair (c), validated)

The same deep-merge shape as fithole.lean, but the FIRST RIDER r₁ = ♦10
sits on z' = ♣J by FIT (`canSitOn ♦10 ♣J = true` — no deal-adjacency).
This is the shape the 2b route ASSUMED: with the premise
`canSitOn r₁ z = true` (twin-blindly: `canSitOn r₁ z' = true`), the
2b TWO-PLY — the rider transfer `pilePile r₁ (inr z)` then the
ORIGINAL merge `pilePile c (inr d)` — is LEGAL in the exchanged state
and composes EXACTLY to the twin-swap of the source's merge successor
(`s2x.board == a1C.board.mapByTwin ♠J` AND
`s2x.board == a1C.exchangeTwinCargo ♥Q`'s board, #eval below) — the
SAME conclusion as the PROVEN 2a ply (`exchange_merge_ply_root`).  So
the premise buys the entire 2b ply step; the remaining route content
is the same climb-out as 2a (the L1/O3 interleaving — the control's
stx play needs one climb-out detour, `pilePile ♥K (inl p0)`, to
un-bury z early: the residue the window must handle).

Cast: t = ♥Q, t' = ♦Q, z = ♠J, z' = ♣J, c = ♠Q, r₁ = ♦10 (FITS z'),
d = ♥K (deal-adjacent on r₁); heights (heart 11, diamond 9, spade 10,
club 10); the deal-adjacency pairs (♠Q, ♥Q) in p2 [the t-edge] and
(♦10, ♥K) in p3 [the r₁-edge]; anchor p0 free (the climb-out detour).
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

/-! ## The control cast -/

def c_ (s : Suit) (r : Rank) : Card := Card.mk s r

def tH : Card := c_ .heart .queen        -- t  (the licensed twin)
def tD : Card := c_ .diamond .queen      -- t' = t.flipSuit
def zS : Card := c_ .spade .jack          -- z  (the cargo on t)
def zC : Card := c_ .club .jack           -- z' = z.flipSuit (the cargo on t')
def cS : Card := c_ .spade .queen          -- c  (the merge's root)
def rD : Card := c_ .diamond .ten          -- r₁ (the first rider — FITS z': the control)
def dH : Card := c_ .heart .king            -- d  (the deep landing, DEAL-ADJ on r₁)
def dJ : Card := c_ .diamond .jack
def dK : Card := c_ .diamond .king
def cQ : Card := c_ .club .queen
def sK : Card := c_ .spade .king
def cK : Card := c_ .club .king

def dl2 : List Card :=
  [c_ .heart .two]                                               -- p0: pad (anchor p0 EMPTY)
  ++ [c_ .diamond .queen, c_ .heart .three]                      -- p1: t' = ♦Q (head) + pad
  ++ [c_ .spade .queen, c_ .heart .queen, c_ .spade .eight]       -- p2: c = ♠Q (head) < t = ♥Q (pair)
  ++ [c_ .heart .four, c_ .diamond .ten, c_ .heart .king, c_ .club .four]  -- p3: pad, r₁ < d (pair), pad
  ++ [c_ .spade .king, c_ .spade .jack, c_ .heart .five, c_ .heart .six, c_ .heart .seven]  -- p4: ♠K (head), z = ♠J
  ++ [c_ .diamond .king, c_ .club .queen, c_ .diamond .jack, c_ .spade .two, c_ .spade .three, c_ .spade .four]  -- p5: ♦K (head), ♣Q, ♦J
  ++ [c_ .club .king, c_ .club .jack, c_ .club .five, c_ .club .six, c_ .club .seven, c_ .club .eight, c_ .club .nine]  -- p6: ♣K (head), z' = ♣J
  ++ [c_ .heart .ace, c_ .heart .eight, c_ .heart .nine, c_ .heart .ten, c_ .heart .jack,
      c_ .diamond .ace, c_ .diamond .two, c_ .diamond .three, c_ .diamond .four,
      c_ .diamond .five, c_ .diamond .six, c_ .diamond .seven, c_ .diamond .eight, c_ .diamond .nine,
      c_ .spade .ace, c_ .spade .five, c_ .spade .six, c_ .spade .seven, c_ .spade .nine, c_ .spade .ten,
      c_ .club .ace, c_ .club .two, c_ .club .three, c_ .club .ten]  -- stock (24, all below height)

def hts2 : Suit -> Nat := fun s =>
  match s with
  | .diamond => 9 | .heart => 11 | .spade => 10 | .club => 10

def bF2 : Board := attachAll Board.empty
  [ (Sum.inl Anchor.p1, tD)          -- t' = ♦Q (p1's head)
  , (Sum.inr tD, zC)                 -- z' = ♣J on t' (fit)
  , (Sum.inr zC, rD)                 -- r₁ = ♦10 on z' (FIT — THE CONTROL: no deal-adjacency)
  , (Sum.inr rD, dH)                 -- d = ♥K on r₁ (DEAL-ADJ: the p3 pair)
  , (Sum.inl Anchor.p2, cS)          -- c = ♠Q (p2's head)
  , (Sum.inr cS, tH)                 -- t = ♥Q on c (DEAL-ADJ: the p2 pair)
  , (Sum.inr tH, zS)                 -- z = ♠J on t (fit; BARE — riders-cleared)
  , (Sum.inl Anchor.p4, sK)          -- ♠K (p4's head, king)
  , (Sum.inl Anchor.p5, dK)          -- ♦K (p5's head, king)
  , (Sum.inr dK, cQ)                 -- ♣Q on ♦K (fit)
  , (Sum.inr cQ, dJ)                 -- ♦J on ♣Q (fit)
  , (Sum.inl Anchor.p6, cK) ]        -- ♣K (p6's head, king)

def fst2 : State := State.mk (Deal.ofList dl2) bF2 hts2 (fun _ => 0) (Cycle.mk [] 0) 1
def fstx2 : State := fst2.exchangeTwinCargo tH

/-! ## The control is WF and licensed; the deep merge is on the winning line -/

#eval dl2.length                                                       -- 52
#eval (Deal.ofList dl2).piles Anchor.p2 |>.map cardStr                  -- [♠Q, ♥Q, ♠8] — the t-edge pair
#eval (Deal.ofList dl2).piles Anchor.p3 |>.map cardStr                  -- [♥4, ♦10, ♥K, ♣4] — the r₁-edge pair

#eval wfCheck fst2                                                     -- TRUE — all 11 conjuncts
#eval wfCheck fstx2                                                    -- TRUE

-- the license at t = ♥Q (twinLicensed, unpacked)
#eval (tD == tH.flipSuit, zC == zS.flipSuit)                           -- (true, true)
#eval (fst2.isVis tH, fst2.isVis tD)                                    -- (true, true)
#eval (fst2.board.bottomOf zS == some (Sum.inr tH),
       fst2.board.bottomOf zC == some (Sum.inr tD))                     -- (true, true)
#eval (canSitOn zS tH, canSitOn zC tD)                                  -- (true, true)
#eval (!(fst2.board.aboveOf zS).contains tH && !(fst2.board.aboveOf zS).contains tD,
       !(fst2.board.aboveOf zC).contains tH && !(fst2.board.aboveOf zC).contains tD)  -- (true, true)
#eval (fst2.board.topOf (Sum.inr zS)).isNone                            -- true — z bare

-- the deep merge and its shape
#eval (fst2.board.aboveOf zC).map cardStr                                -- ["HK", "D10"] — d and r₁ above z'
#eval ((fst2.board.aboveOf zC).contains dH, dH != zC)                     -- (true, true) — DEEP
#eval (fst2.board.topOf (Sum.inr zC) == some rD,
       fst2.board.bottomOf rD == some (Sum.inr zC))                      -- (true, true) — r₁ DIRECTLY on z'
#eval (fst2.board.aboveOf cS).map cardStr                                -- ["SJ", "HQ"] — c's run passes t
#eval (fst2.apply (Move.pilePile cS (Sum.inr dH))).isSome                 -- true — the deep merge LEGAL

-- THE CONTROL: r₁ FITS z' (and twin-blindly z)
#eval (canSitOn rD zC, canSitOn rD zS)                                  -- (true, true) — the twin-blind fit HOLDS
#eval consec (fst2.deal.piles Anchor.p3) rD dH                          -- true — (♦10, ♥K) consecutive in p3 (the d-edge)

/-! ## The 2b TWO-PLY, with the fit: LEGAL, and composes to the twin-swap -/

#eval (fstx2.apply (Move.pilePile rD (Sum.inr zS))).isSome               -- TRUE — the rider transfer LEGAL (vs false at the hole)
#eval (fstx2.apply (Move.pilePile cS (Sum.inr dH))).isSome               -- false — the merge alone still self-lands

def a1C : State := (fst2.apply (Move.pilePile cS (Sum.inr dH))).getD fst2
def s1x : State := (fstx2.apply (Move.pilePile rD (Sum.inr zS))).getD fstx2
def s2x : State := (s1x.apply (Move.pilePile cS (Sum.inr dH))).getD s1x

#eval Board.enumBase.all (fun b => s2x.board.topOf b == (a1C.board.mapByTwin zS).topOf b)   -- true — the TWO-PLY = twin-swap of a₁
#eval Board.enumBase.all (fun b => s2x.board.topOf b == (a1C.exchangeTwinCargo tH).board.topOf b)  -- true — and seat-exchanged
#eval (Anchor.all.all (fun a => s2x.deal.piles a == a1C.deal.piles a) && s2x.deal.stock == a1C.deal.stock
      && Suit.all.all (fun s => s2x.heights s == a1C.heights s)
      && Anchor.all.all (fun a => s2x.depths a == a1C.depths a)
      && s2x.stock.cards == a1C.stock.cards && s2x.stock.cursor == a1C.stock.cursor
      && s2x.drawStep == a1C.drawStep)                                   -- true — every other field equal

/-! ## The plays -/

/-- The SOURCE's win THROUGH the deep merge (13 moves). -/
def playDeepC : List Move :=
  [ Move.pilePile cS (Sum.inr dH)                    -- 1. THE DEEP MERGE (c's run onto d = ♥K)
  , Move.pileStack zS                                 -- 2. ♠J (spade 10→11)
  , Move.pileStack tH                                 -- 3. ♥Q (heart 11→12)
  , Move.pileStack cS                                 -- 4. ♠Q (spade 11→12)
  , Move.pileStack dH                                 -- 5. ♥K = d (heart 12→13)
  , Move.pileStack rD                                 -- 6. ♦10 = r₁ (diamond 9→10)
  , Move.pileStack dJ                                 -- 7. ♦J (diamond 10→11)
  , Move.pileStack zC                                 -- 8. ♣J = z' (club 10→11)
  , Move.pileStack tD                                 -- 9. ♦Q = t' (diamond 11→12)
  , Move.pileStack cQ                                 -- 10. ♣Q (club 11→12)
  , Move.pileStack sK                                 -- 11. ♠K (spade 12→13)
  , Move.pileStack dK                                 -- 12. ♦K (diamond 12→13)
  , Move.pileStack cK ]                               -- 13. ♣K (club 12→13)

/-- The EXCHANGED state's 2b play: the rider transfer, the original
merge, then a climb-out detour and the climbs (15). -/
def playPlyC : List Move :=
  [ Move.pilePile rD (Sum.inr zS)                    -- 1. (i) the RIDER TRANSFER (legal: r₁ fits z)
  , Move.pilePile cS (Sum.inr dH)                     -- 2. (ii) the ORIGINAL merge
  , Move.pilePile dH (Sum.inl Anchor.p0)              -- 3. (iii) the climb-out detour (♥K's run to p0)
  , Move.pileStack rD                                 -- 4. ♦10 (diamond 9→10)
  , Move.pileStack zS                                 -- 5. ♠J (spade 10→11)
  , Move.pileStack dJ                                 -- 6. ♦J (diamond 10→11)
  , Move.pileStack tD                                 -- 7. ♦Q (diamond 11→12)
  , Move.pileStack zC                                 -- 8. ♣J (club 10→11)
  , Move.pileStack tH                                 -- 9. ♥Q (heart 11→12)
  , Move.pileStack cS                                 -- 10. ♠Q (spade 11→12)
  , Move.pileStack dH                                 -- 11. ♥K (heart 12→13)
  , Move.pileStack cQ                                 -- 12. ♣Q (club 11→12)
  , Move.pileStack sK                                 -- 13. ♠K (spade 12→13)
  , Move.pileStack dK                                 -- 14. ♦K (diamond 12→13)
  , Move.pileStack cK ]                               -- 15. ♣K (club 12→13)

#eval Option.map State.isWin (fst2.run playDeepC)     -- some true
#eval firstFail fst2 playDeepC 0                       -- none
#eval Option.map State.isWin (fstx2.run playPlyC)     -- some true
#eval firstFail fstx2 playPlyC 0                       -- none
#eval (fst2.run playDeepC).map (fun W => Suit.all.map (fun s => W.heights s))    -- some [13,13,13,13]
#eval (fstx2.run playPlyC).map (fun W => Suit.all.map (fun s => W.heights s))     -- some [13,13,13,13]
