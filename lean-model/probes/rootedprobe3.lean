import Klondike.Initial
import Klondike.TwinQuotient

/-! # Rooted-bridge probe 3: the DIRECT correspondence — which one is true?

**Q1 (the mission's twin-pair claim — FALSE at licensed states).**  The
claim `TwinCorr (swapTwin t) t.suit st (st.exchangeTwinCargo t)` demands
`M.board = mapByRho (swapTwin t) st.board` (TwinCorr's `board_eq`, the
value-relabeling conjugation).  But the EXCHANGE swaps the twin seats'
CONTENTS without relabeling card identities, while `mapByRho` relabels
values by ρ — they disagree exactly at the seats carrying t or t' as
their top, i.e. THE TWINS' OWN BASES — and at a licensed state both
twins are seated (that is `isVis`).  At fithole's witness: t = ♥Q sits
on c = ♦J, so the seat `inr ♦J` carries ♥Q; the exchange keeps it there,
while the ρ-relabel maps it to ♦Q.

**Q2 (the corrected cargo-pair, both-bare form — TRUE).**  At a state
whose BOTH cargo seats are bare (z and z' riders-cleared) the license's
covers identify the exchange with the cargo twin swap (TwinBridge §1's
`exchangeTwin_eq_mapByTwin_of_covers`), so `TwinCorr (swapTwin z)
z.suit st (st.exchangeTwinCargo t)`'s board clause holds.  fithole's
post-detour state stD is exactly such a state (the detour emptied z';
z was already bare).
-/

/-! ## The kit (fithole.lean / detour3.lean, verbatim) -/

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

/-! ## fithole's cast (detour3.lean, verbatim) -/

def c_ (s : Suit) (r : Rank) : Card := Card.mk s r

def tH : Card := c_ .heart .queen        -- t  (the licensed twin)
def tD : Card := c_ .diamond .queen      -- t' = t.flipSuit
def zS : Card := c_ .spade .jack          -- z  (the cargo on t)
def zC : Card := c_ .club .jack           -- z' = z.flipSuit (the cargo on t')
def cJ : Card := c_ .diamond .jack        -- c  (the merge's root; t's own base)
def rH : Card := c_ .heart .king           -- r₁ (the first rider on z')
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
  , (Sum.inl Anchor.p2, cJ)          -- c = ♦J (p2's head) — ALSO t's own base
  , (Sum.inr cJ, tH)                 -- t = ♥Q on c (DEAL-ADJ: the p2 pair)
  , (Sum.inr tH, zS)                 -- z = ♠J on t (fit; BARE — riders-cleared)
  , (Sum.inl Anchor.p4, dK)          -- ♦K (p4's head, king)
  , (Sum.inr dK, cQ)                 -- ♣Q on ♦K (fit)
  , (Sum.inr cQ, hJ)                 -- ♥J on ♣Q (fit)
  , (Sum.inl Anchor.p5, sK)          -- ♠K (p5's head, king)
  , (Sum.inl Anchor.p6, cK) ]        -- ♣K (p6's head, king)

def fst : State := State.mk (Deal.ofList dl) bF hts (fun _ => 0) (Cycle.mk [] 0) 1
def fstx : State := fst.exchangeTwinCargo tH

/-- The post-detour state: BOTH cargo seats bare (the detour emptied z'),
the license intact. -/
def stD : State := (fst.apply (Move.pilePile rH (Sum.inl Anchor.p0))).getD fst
def stDx : State := stD.exchangeTwinCargo tH

/-! ## Q1: the twin-pair claim is FALSE at the licensed state -/

#eval wfCheck fst                                                       -- TRUE — the witness is WF
#eval (fst.isVis tH, fst.isVis tD)                                      -- (true, true) — the twins are SEATED
#eval (fst.board.topOf (Sum.inr cJ)).map cardStr                        -- "HQ" — t rides c: the seat inr cJ CARRIES t
-- the exchange keeps it there (the exchange moves seat CONTENTS, not card identities):
#eval (fstx.board.topOf (Sum.inr cJ)).map cardStr                       -- "HQ" — t STILL the top of its own base
-- while the ρ-relabel (ρ = swapTwin t) maps the value t to t':
#eval (fst.board.topOf (Sum.inr cJ)).map (Card.swapTwin tH) |>.map cardStr  -- "DQ" — the relabelled image
-- so TwinCorr's board_eq FAILS at b := inr cJ:  some ♥Q ≠ some ♦Q.
#eval (fstx.board.topOf (Sum.inr cJ)) ==
  (fst.board.topOf (Sum.inr cJ)).map (Card.swapTwin tH)                  -- FALSE — the correspondence's board clause
-- (and the two requirements are mutually exclusive: board_eq needs NO seat to carry
--  t/t' — i.e. the twins UNSEATED — while the stacked_iff cross-case needs them
--  visible for founds_gone.  The mission's premise set is unsatisfiable.)

/-! ## Q2: the corrected cargo-pair, both-bare form HOLDS at stD -/

#eval wfCheck stD                                                       -- TRUE
#eval (stD.board.topOf (Sum.inr zS)).isNone                            -- true — z bare
#eval (stD.board.topOf (Sum.inr zC)).isNone                            -- true — z' bare (the detour emptied it)
#eval (stD.board.topOf (Sum.inr tH) == some zS,
       stD.board.topOf (Sum.inr tD) == some zC)                          -- (true, true) — the covers
#eval (canSitOn zS tH, canSitOn zC tD)                                  -- (true, true) — the fits
-- the exchange IS the cargo twin swap at such a state (§1's covers lemma), hence
-- TwinCorr (swapTwin z) z.suit stD (stD.exchangeTwinCargo t)'s board clause holds:
#eval Board.enumBase.all (fun b =>
  (stDx.board.topOf b) == (stD.board.mapByTwin zS).topOf b)             -- TRUE — the boards agree on EVERY seat
-- and the other fields are rfl (the exchange is board-only), so the correspondence
-- holds — the direct route is live at both-bare licensed states.
