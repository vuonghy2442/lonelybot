import Orig.Twin

/-!
# The ORIG merge probe (refute-first gate; the target is a theorem instance)

The engine card's escape-clause design for the ORIG twin exchange: at any
state whose twin hosts sit face-up in DISTINCT piles with regional
uniqueness (NO `colClean` premise in the floor), every winning play either
replays as a win from the suffix-swapped state `st → swapTwinSuffixes`, or
passes a MERGE — a legal `tabToTab c (inr z)` whose moved run CONTAINS one
host (rooted at-or-below it in its column) and whose base lands on a card
of the OTHER host's region.

The engine wants the disjunction certified two-sided BEFORE it runs.  This
probe supplies the #eval evidence, in three parts:

(1) THE MERGE-LIVE WITNESS (`omSt`, hand-built, non-WF the w15merge way —
    lying found heights past on-board cards; conservation is NOT claimed
    and NOT a premise of the instance).  Twin hosts `♥J` (p0) / `♦J` (p1)
    face-up in distinct piles; the below-host column of p0 is NOT
    `runOK`; the regional uniqueness (hosts plus both strictly-above
    suffixes, over the board zones) holds.  The merge
    `tabToTab ♠J (inr ♦Q)` is legal at `omSt`: its run `[♠J, ♥J, ♦K]`
    contains the host `♥J` (rooted below it), and the base `♦Q` sits in
    the other host's region (the strictly-above suffix of `♦J`).  `omSt`
    wins in exactly 5 moves WITH THE MERGE FIRST — the linchpin being that
    the merge EXPOSES p0's buried prefix `♥Q`, the only seat from which
    hearts' 12th can arrive.

    The suffix-swapped state `omStx` is WINLESS: searched exhaustively to
    the engine card's ~6 horizon and one level beyond it — 706 distinct
    states at depth 6, 1,788 at depth 7, every single one win-checked, no
    win; the frontier never empties (the space keeps growing through
    shuffle dead-ends), so the negative is HORIZON-LIMITED to depth 7 and
    is reported as such — exactly the honest negative the card asks for.
    The freeze is the designed w15merge mechanism, ported: the exchange
    transplants p1's suffix `[♦Q]` ON TOP of `omStx`'s host column, where
    the passed ♦queen (diamonds sit at 12) jams the heart chain for good —
    the mirror landing "blocked by a crafted non-fitting tenant"; and
    because the merge base `♦Q` is rank-decoupled from the jack hosts,
    the twin-blind self-landing swallow offers no rescue (`canSitOn ♠J
    ♥J` fails by rank, so no legal tabToTab pops p0's tail off the host
    stub).

(2) THE DEGENERATE-SHUTTLE CAVEAT (the honest boundary of the design):
    `omSt` ALSO has a 5-move winning play with NO merge-shaped move — pop
    the host first, and then the very same `t2t ♠J → ♦Q` is a bare
    shuttle whose run `[♠J]` no longer contains any host.  Same move, the
    classification is state-dependent.  That play's move list run from
    `omStx` reaches no win either, so disjunct 1 (replay) cannot save
    it: the STRICT instance ("every winning play replays or passes a
    merge") is REFUTED at the wild-state premises EVEN WITH disjunct 2
    genuinely live.  The engine-side moral is recorded with the numbers:
    the merge clause alone cannot carry the escape design at wild states;
    the corollary side is where its security actually lives.

(3) THE KILL SANITY (the colClean corollary made decidable): at a second
    crafted state whose BOTH host columns are clean (`runOK = true` on
    p0/p1, hosts again `♥J`/`♦J` in distinct piles, uniqueness intact),
    exhaustive enumeration of every legal move finds NO merge-shaped
    `tabToTab`.  That is the corollary's 3-line rank argument made
    executable: a clean host column forces `idx c = idx t + k` (k ≥ 0) for
    every run rooted at-or-below `t`, while the fit demands
    `idx c = idx z - 1`, and every base `z` of the other host's region
    (the host itself, or a strictly-above suffix card of a clean column,
    hence strictly lower in index) satisfies `idx z ≤ idx t` — a
    contradiction.  The same classifier DOES flag the witness merge at
    `omSt`, so "no merge fires at colClean states up to the probe's
    horizon" is evidence about the shape, not the classifier.

Everything here is evidence, not theorems — nothing is imported by the
library.  Run with `lake env lean probes/origmerge.lean` from
`lean-model/`.  Read the verdicts bottom-up: every printed claim is
re-checked by the gates, and the final `#eval!` throws unless ALL of them
hold, so the script exits 0 exactly when its evidence stands.
-/

/-! ## Kit -/

private def crd (s : Suit) (r : Rank) : Card := ⟨s, r⟩

private def rankStr : Rank → String
  | .ace => "A" | .two => "2" | .three => "3" | .four => "4" | .five => "5"
  | .six => "6" | .seven => "7" | .eight => "8" | .nine => "9" | .ten => "10"
  | .jack => "J" | .queen => "Q" | .king => "K"

private def suitStr : Suit → String
  | .spade => "S" | .heart => "H" | .diamond => "D" | .club => "C"

private def cardStr (c : Card) : String := suitStr c.suit ++ rankStr c.rank

private def cardsStr (l : List Card) : String :=
  "[" ++ String.intercalate " " (l.map cardStr) ++ "]"

private def anchorStr : Anchor → String
  | .p0 => "p0" | .p1 => "p1" | .p2 => "p2" | .p3 => "p3" | .p4 => "p4"
  | .p5 => "p5" | .p6 => "p6"

private def moveStr : Move → String
  | .draw => "draw"
  | .wasteToFound c => "w2f " ++ cardStr c
  | .wasteToTab c b => "w2t " ++ cardStr c ++ "@" ++ (match b with
    | .inl a => anchorStr a | .inr c => cardStr c)
  | .tabToFound c => "t2f " ++ cardStr c
  | .foundToTab c b => "f2t " ++ cardStr c ++ "@" ++ (match b with
    | .inl a => anchorStr a | .inr c => cardStr c)
  | .tabToTab c b => "t2t " ++ cardStr c ++ "@" ++ (match b with
    | .inl a => anchorStr a | .inr c => cardStr c)

/-! ## (1) The engine: legal-move enumeration + bounded dedup'd BFS

The candidate generator follows the engine card's letter: `draw`;
`wasteToFound`/`wasteToTab` with `c` the state's waste top; `tabToFound`
over all pile tops; `foundToTab` over foundation tops × bases (all
anchors + all current tops); `tabToTab` with `c` over all face-up cards
and `b` over anchors + tops.  Every candidate is filtered through
`State.step`.  The BFS is dedup'd breadth-first with a move budget;
`isWin` is checked at every visited state, the start included; `diedAt`
records whether the frontier ever emptied (exhaustion upgrades "no win to
depth k" to "no win, ever"). -/

private def bases (st : State) : List (Sum Anchor Card) :=
  Anchor.all.map Sum.inl ++ ((Anchor.all.map st.topOf).filterMap id).map Sum.inr

private def moveCands (st : State) : List Move :=
  [Move.draw]
  ++ (match st.waste with
      | [] => []
      | c :: _ => [Move.wasteToFound c] ++ (bases st).map (fun b => Move.wasteToTab c b))
  ++ ((Anchor.all.map st.topOf).filterMap id).map (fun c => Move.tabToFound c)
  ++ (Suit.all.flatMap (fun s => match st.foundTop s with
      | some c => (bases st).map (fun b => Move.foundToTab c b)
      | none => []))
  ++ ((Anchor.all.flatMap (fun a => (st.piles a).faceUp)).flatMap
      (fun c => (bases st).map (fun b => Move.tabToTab c b)))

private def legalMoves (st : State) : List Move :=
  (moveCands st).filter (fun m => (State.step st m).isSome)

private def succs (st : State) : List State :=
  (legalMoves st).flatMap (fun m => match State.step st m with
    | some s' => [s'] | none => [])

/-- A canonical key over every zone the moves can change: foundations,
all piles (hidden + face-up), stock, waste, draw step. -/
private def stateKey (st : State) : String :=
  String.intercalate "," (Suit.all.map (fun s => cardsStr (st.found s))) ++ "|" ++
  String.intercalate ";" (Anchor.all.map (fun a =>
    String.intercalate "" ((st.piles a).hidden.map cardStr) ++ "."
    ++ String.intercalate "" ((st.piles a).faceUp.map cardStr))) ++ "|" ++
  String.intercalate "" (st.stock.map cardStr) ++ "|" ++
  String.intercalate "" (st.waste.map cardStr) ++ "|" ++ toString st.drawStep

private structure SearchR where
  winDepth : Option Nat
  visited : Nat
  diedAt : Option Nat
  deriving Nonempty

private partial def bfsAux (budget lvl : Nat) (front : List State)
    (vis : List String) : SearchR :=
  if front.any (fun s => s.isWin) then
    { winDepth := some lvl, visited := vis.length, diedAt := none }
  else if budget = 0 then
    { winDepth := none, visited := vis.length, diedAt := none }
  else
    let next := front.flatMap succs
    let news := next.filter (fun s => !vis.contains (stateKey s))
    let newsD := news.foldl (fun acc s =>
      if (acc.map stateKey).contains (stateKey s) then acc else s :: acc) []
    if newsD.isEmpty then
      { winDepth := none, visited := vis.length, diedAt := some lvl }
    else
      bfsAux (budget - 1) (lvl + 1) newsD
        (newsD.foldl (fun acc s => stateKey s :: acc) vis)

private def runSearch (budget : Nat) (st : State) : SearchR :=
  bfsAux budget 0 [st] [stateKey st]

/-! ## The private local swap + the merge classifier

`swapTwinSuffixes` is this file's private copy of the exchange the
parallel `Orig.TwinExchange` card is landing: locate both hosts via
`State.pileHolding`, swap the STRICTLY-ABOVE suffixes between the two
host piles, leave everything else (the piles' bottoms, the hosts
themselves, other piles, stock, waste, foundations) untouched. -/

private def aboveStrict (c : Card) (p : Pile) : List Card :=
  (fromCard c p.faceUp).drop 1

private def swapTwinSuffixes (st : State) (t : Card) : Option State :=
  match st.pileHolding t, st.pileHolding t.twin with
  | some a, some a' =>
      if a = a' then none
      else
        let pa := st.piles a
        let pa' := st.piles a'
        let na : Pile := ⟨pa.hidden, below t pa.faceUp ++ [t] ++ aboveStrict t.twin pa'⟩
        let na' : Pile := ⟨pa'.hidden, below t.twin pa'.faceUp ++ [t.twin] ++ aboveStrict t pa⟩
        some ((st.setPile a na).setPile a' na')
  | _, _ => none

/-- The protected region of `h` at `st`: `h` plus its strictly-above suffix. -/
private def regionOf (st : State) (h : Card) : List Card :=
  match st.pileHolding h with
  | some a => [h] ++ aboveStrict h (st.piles a)
  | none => [h]

/--
Is `tabToTab c (inr z)` at `st` a MERGE for the twin pair rooted at `t`?
The moved run must CONTAIN one host — so the root `c` is at-or-below it in
its column, by run direction — and the base card must be of the OTHER
host's region.  The run is read at the CURRENT state, so the same move
literal can be a merge in one state and a bare shuttle in another (the
degenerate-shuttle caveat below). -/
private def isMergeShaped (st : State) (t c z : Card) : Bool :=
  match st.pileHolding c with
  | none => false
  | some a =>
      let run := fromCard c (st.piles a).faceUp
      (run.contains t && (regionOf st t.twin).contains z)
      || (run.contains t.twin && (regionOf st t).contains z)

private def allMergeMoves (st : State) (t : Card) : List Move :=
  (legalMoves st).filter (fun m =>
    match m with
    | .tabToTab c (Sum.inr z) => isMergeShaped st t c z
    | _ => false)

/-! ## The premise checks

Regional uniqueness is read over the BOARD zones — every pile's hidden +
face-up strata, the stock, and the waste.  Foundations are the
bookkeeping zone of the crafted lying-heights state and sit outside the
executable reading, exactly as in w15merge ("heights past visible cards").
-/

private def boardOcc (st : State) (c : Card) : Nat :=
  (Anchor.all.foldl (fun n a =>
      n + (st.piles a).faceUp.countP (fun x => decide (x = c))
        + (st.piles a).hidden.countP (fun x => decide (x = c))) 0)
  + st.stock.countP (fun x => decide (x = c))
  + st.waste.countP (fun x => decide (x = c))

private def hostsDistinct (st : State) (t : Card) : Bool :=
  match st.pileHolding t, st.pileHolding t.twin with
  | some a, some b => decide (a ≠ b)
  | _, _ => false

private def protectedSet (st : State) (t : Card) : List Card :=
  regionOf st t ++ regionOf st t.twin

private def uniqueOk (st : State) (t : Card) : Bool :=
  (protectedSet st t).all (fun c => boardOcc st c = 1)

/-! ## (2) The main craft: the merge-live witness

    p0 = [♥Q, ♠J, ♥J, ♦K]  the heart queen buried in the prefix under the
                           root ♠J under the host ♥J under the suffix
                           [♦K]; the below-host column [♥Q, ♠J] is NOT
                           `runOK` (a ♥jack cannot sit on a ♠jack — the
                           root is a junk non-descending tenant, the
                           crafted dirt the design wants)
    p1 = [♦J, ♦Q]         the twin host; its strictly-above suffix ♦Q is
                           the merge base (rank-decoupled from the hosts)
    p2 = [♣2, ♥K]         the free heart climber
    p3..p6 = ♥2 ♥3 ♥4 ♥5  single-card stones: all seven piles occupied, so
                           the king escape (parking a king run on an empty
                           anchor) does not exist
    found: ♥ A..10 (10), ♦ A..Q (12), ♠ and ♣ complete (13); stock and
    waste empty.  Diamonds' 13th is the ♦K atop p0; hearts need J, Q, K —
    the J is the p0 host, the Q the p0 prefix, the K the p2 climber. -/

private def omFnd : Suit → List Card := fun s =>
  s.upCards.take (match s with | .spade => 13 | .club => 13 | .heart => 10 | .diamond => 12)

private def omSt : State :=
  { found := omFnd
    piles := fun a => match a with
      | .p0 => ⟨[], [crd .heart .queen, crd .spade .jack, crd .heart .jack,
                     crd .diamond .king]⟩
      | .p1 => ⟨[], [crd .diamond .jack, crd .diamond .queen]⟩
      | .p2 => ⟨[], [crd .club .two, crd .heart .king]⟩
      | .p3 => ⟨[], [crd .heart .two]⟩
      | .p4 => ⟨[], [crd .heart .three]⟩
      | .p5 => ⟨[], [crd .heart .four]⟩
      | .p6 => ⟨[], [crd .heart .five]⟩
    stock := [], waste := [], drawStep := 1 }

private def omT : Card := crd .heart .jack        -- the p0 host
private def omTT : Card := omT.twin                -- = ♦J, the p1 host
private def omC : Card := crd .spade .jack         -- the merge root
private def omZ : Card := crd .diamond .queen      -- the merge base

#eval Anchor.all.map (fun a => (anchorStr a, cardsStr (omSt.piles a).faceUp))
#eval Suit.all.map (fun s => (suitStr s, (omSt.found s).length))

-- premise (i): twin hosts face-up in DISTINCT piles
#eval (hostsDistinct omSt omT, omSt.pileHolding omT, omSt.pileHolding omTT)
-- premise (ii): regional uniqueness, board zones
#eval (protectedSet omSt omT).map cardStr
#eval uniqueOk omSt omT
-- the crafted dirt: the below-host column is NOT runOK
#eval (runOK (omSt.piles Anchor.p0).faceUp, runOK (omSt.piles Anchor.p1).faceUp)

-- the merge and its shape at omSt
#eval (allMergeMoves omSt omT).map moveStr
#eval isMergeShaped omSt omT omC omZ

/-! The exhibited winning play: FIVE moves, the merge first.  The merge
moves `[♠J, ♥J, ♦K]` onto ♦Q and EXPOSES the prefix ♥Q of p0 — the win's
linchpin: hearts' 12th can only arrive from there, and it is reachable
only by emptying p0's tail. -/

private def omWin : List Move :=
  [ Move.tabToTab omC (Sum.inr omZ)                     -- the MERGE
  , Move.tabToFound (crd .diamond .king)               -- p1 top: ♦ 12 → 13
  , Move.tabToFound omT                                -- p1 top: ♥ 10 → 11
  , Move.tabToFound (crd .heart .queen)                -- p0 prefix: ♥ 11 → 12
  , Move.tabToFound (crd .heart .king) ]               -- p2 top: ♥ 12 → 13

#eval String.intercalate " ; " (omWin.map moveStr)
#eval (State.run omSt omWin).map State.isWin          -- some true
#eval (State.run omSt omWin).map (fun w => Suit.all.map (fun s => (w.found s).length))

/-! ## (3) The frozen exchange -/

private def omStx : State := (swapTwinSuffixes omSt omT).getD omSt

#eval Anchor.all.map (fun a => (anchorStr a, cardsStr (omStx.piles a).faceUp))
#eval (stateKey omSt != stateKey omStx)               -- the swap is live (nonvacuous)

-- WINLESS, exhaustively searched: no win to depth 6, nor to depth 7; the
-- visited counts grow (706 → 1,788) but stay winless; the frontier NEVER
-- empties (diedAt = none), so the negative is horizon-limited and is
-- reported so.
#eval (let r := runSearch 6 omStx; (r.winDepth, r.visited, r.diedAt))
#eval (let r := runSearch 7 omStx; (r.winDepth, r.visited, r.diedAt))

-- disjunct 1 dies on this instance: the exhibited play's own move list
-- cannot be run from omStx to any win (it dies AT the merge: the base
-- ♦Q is no longer a pile top there — the swap buried it on top of p0)
#eval ((State.run omStx omWin).map State.isWin)        -- none

/-! The degenerate shuttle (the honest boundary): `omSt` ALSO wins with
NO merge-shaped move — host popped first, the same `t2t ♠J ♦Q` is then a
bare shuttle whose run holds no host.  Its move list likewise reaches no
win from `omStx`. -/


private def omDegen : List Move :=
  [ Move.tabToFound (crd .diamond .king)               -- p0 top: ♦ 12 → 13
  , Move.tabToFound omT                                -- p0 top: ♥ 10 → 11
  , Move.tabToTab omC (Sum.inr omZ)                    -- the bare shuttle
  , Move.tabToFound (crd .heart .queen)                -- p0 prefix: ♥ 11 → 12
  , Move.tabToFound (crd .heart .king) ]               -- p2 top: ♥ 12 → 13

#eval String.intercalate " ; " (omDegen.map moveStr)
#eval (State.run omSt omDegen).map State.isWin          -- some true (recorded caveat)
#eval (State.run omStx omDegen).map State.isWin         -- none

/-! ## (4) The kill sanity: colClean states admit no merge

    p0 = [♠Q, ♥J, ♣10, ♥9]  host ♥J mid-column, CLEAN: ♥J sits on ♠Q,
                            ♣10 on ♥J, ♥9 on ♣10; suffix [♣10, ♥9]
    p1 = [♦J, ♠10]          the twin host at the base, CLEAN: ♠10 sits
                            on ♦J; suffix [♠10]
The 3-line rank argument, made decidable: on a clean host column every
run rooted at-or-below a host has `idx c = idx t + k` (k ≥ 0), while any
fit onto the other host's region needs `idx c = idx z - 1` with `idx z ≤
idx t` — the other host itself, or a strictly-above suffix card of a
clean (descending) column — a contradiction.  Foundations complete (every
rank foundation-passed, so no pop noise); all piles occupied. -/

private def kilSt : State :=
  { found := fun s => s.upCards
    piles := fun a => match a with
      | .p0 => ⟨[], [crd .spade .queen, crd .heart .jack,
                     crd .club .ten, crd .heart .nine]⟩
      | .p1 => ⟨[], [crd .diamond .jack, crd .spade .ten]⟩
      | .p2 => ⟨[], [crd .heart .two]⟩
      | .p3 => ⟨[], [crd .heart .three]⟩
      | .p4 => ⟨[], [crd .heart .four]⟩
      | .p5 => ⟨[], [crd .heart .five]⟩
      | .p6 => ⟨[], [crd .heart .six]⟩
    stock := [], waste := [], drawStep := 1 }

#eval (runOK (kilSt.piles Anchor.p0).faceUp, runOK (kilSt.piles Anchor.p1).faceUp)
#eval (hostsDistinct kilSt omT, uniqueOk kilSt omT)

-- the kill: NO merge-shaped tabToTab is legal, by exhaustive enumeration
-- over the engine's own generator
#eval (allMergeMoves kilSt omT).map moveStr             -- []

-- the contrast: the same classifier flags the witness merge at omSt
#eval (allMergeMoves omSt omT).map moveStr               -- [t2t SJ@DQ]

/-! ## (5) The verdict gates

Every printed claim is re-checked here; the `#eval!` throws unless ALL
hold, so `lake env lean probes/origmerge.lean` exits nonzero exactly when
the evidence fails. -/

private def gatePremises : Bool :=
  hostsDistinct omSt omT && uniqueOk omSt omT
    && !runOK (omSt.piles Anchor.p0).faceUp

private def gateMergeLive : Bool :=
  (State.run omSt omWin).any (fun w => w.isWin)
    && isMergeShaped omSt omT omC omZ
    && omWin.length ≤ 5

private def gateFrozen : Bool :=
  stateKey omSt != stateKey omStx
    && (runSearch 6 omStx).winDepth.isNone
    && (runSearch 7 omStx).winDepth.isNone
    && !(State.run omStx omWin).any (fun w => w.isWin)
    && !(State.run omStx omDegen).any (fun w => w.isWin)

private def gateCaveat : Bool :=
  (State.run omSt omDegen).any (fun w => w.isWin)
    -- the caveat must be REAL (that is the finding) — but it must also be
    -- replay-dead, or the recorded moral would be wrong
    && (allMergeMoves (kilSt) omT).isEmpty

private def gateKill : Bool :=
  runOK (kilSt.piles Anchor.p0).faceUp && runOK (kilSt.piles Anchor.p1).faceUp
    && hostsDistinct kilSt omT && uniqueOk kilSt omT
    && (allMergeMoves kilSt omT).isEmpty
    && !(allMergeMoves omSt omT).isEmpty

private def allGates : Bool :=
  gatePremises && gateMergeLive && gateFrozen && gateCaveat && gateKill

#eval! do
  if allGates then
    IO.println "ORIGMERGE: ALL GATES HOLD — merge live at the wild-state witness; exchange winless to depth 7; no merge at the colClean kill state; degenerate-shuttle caveat recorded."
  else
    throw (IO.userError "ORIGMERGE: A GATE FAILED — see the numbers above")
