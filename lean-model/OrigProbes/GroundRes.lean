import Orig.Play
import Lean

/-!
# The (N) ground-normal-form transfer probes (wave-24, row
`tabToFound_groundNormalForm`)

Refute-first evidence for the load-bearing claims of the
ground-normal-form protocol (route note: `docs/method.md` §5.1, the
B&G App. B.1 Thm-1 transform, physically):

* **C1 (the row at the root).**  At a WF quartet state passing the
  `safeToFound` razor bounds for `c`, if the state wins then the
  raised state (`tabToFound c`) wins.  A falsifier here is a premise
  repair for the row itself.
* **C2 (the eroded-window transfer).**  The same implication at
  quartet states whose height slack was spent by clean other-suit
  worry-backs — exactly the window the first-blocked elimination
  meets.  If C2 fails, the route's per-arm squares need the slack
  premise re-derived at the window (bookkeeping repair).
* **W1..W6 (the spread-window carry, added by the spread-core
  session).**  The two candidate window lemmas the (N) α/β residue
  and the (C) storage prong both consume, at hand-composed
  window-shaped members (the plays themselves are checked by the
  oracle — a dead hand play is a construction bug and the exe
  throws): (i) the α1 spread — a waste head parked on `c`'s seat,
  c-blind suit raises between, the delayed restack; the claim run is
  the same prefix plus a `wasteToFound` closer at the window END, the
  end state EXACTLY equal; (ii) the β spread — a foundation worry
  onto another suit's tenant, a cross-suit raise between, its
  restack; the claim: the pair alone deletes with the end state
  EXACTLY equal; (iii) the covered foundation-park bubble — worry,
  cover-park on the worried card, eviction, restack — nets to zero
  as a UNIT (the deleted thread runs the empty segment); (iv) the
  covered waste-park — a cover fired on the parked waste tenant
  mid-window (an E3 shape).  At the razor heights this corner is
  UNAVAILABLE by the razor's own arithmetic: the parked `Q♥`'s
  covers are the black jacks — the c-suit one is founded two deep
  (LIFO-dead for its own worry), the other is `c`'s dig partner
  waiting hidden under `c` — so the member lives at the slack-1
  heights (`h♣ = 11`, still `safeToFound`-consistent), where the
  cover fires as a foundation worry (`fT J♣` onto the parked `Q♥`)
  and the whole [cover; σ; un-cover] bubble nets to zero while the
  deleted thread raises σ verbatim and takes the delayed waste
  closer; (v) the queued α1 window (the parked card behind a second
  waste card); (vi) the diamond — tenant raise and rung raise
  commute at distinct suits, both orders legal and EXACTLY equal.
  A W-asymmetry (window thread wins, transformed thread does not, or
  the ends differ) is the falsifier shape: the exe reports the case
  and throws for hand-exhaustive follow-up.

Exhaustive dedup'd BFS over the full physical move set
(`State.step` is the only oracle), exact Nat positional keys in a
hash set (no collision risk: a key encodes every zone card-by-card),
win plays recorded.  Raised-world slices: raise-priority DFS (wins
certified; a NO-WIN is a smoke gun, not a verdict).  Corpus: the
`K♠` razor corner (r = 12) plus eroded members (legal worry-towers
spending the ♥/♣ slack), the club-rung twin razor `K♣` (r = 12, the
suit-mirrored seed) with its own two erodes, and the queued
variants.  The W-cases come as state pairs (window thread, deleted
thread) with hand-composed plays, every play verified by the
oracle.

Run: `lake env lean probes/groundres.lean` from `lean-model/`.
The final `#eval!` throws if any member falsified the transfer, or
if the corpus came out vacuous/ill-formed.
-/

private def crd (s : Suit) (r : Rank) : Card := ⟨s, r⟩

private def rankStr : Rank → String
  | .ace => "A" | .two => "2" | .three => "3" | .four => "4"
  | .five => "5" | .six => "6" | .seven => "7" | .eight => "8"
  | .nine => "9" | .ten => "10" | .jack => "J" | .queen => "Q"
  | .king => "K"

private def suitStr : Suit → String
  | .spade => "♠" | .heart => "♥" | .diamond => "♦" | .club => "♣"

private def cardStr (c : Card) : String := suitStr c.suit ++ rankStr c.rank

private def anchorStr : Anchor → String
  | .p0 => "0" | .p1 => "1" | .p2 => "2" | .p3 => "3"
  | .p4 => "4" | .p5 => "5" | .p6 => "6"

private def baseStr : Sum Anchor Card → String
  | .inl a => s!"∅{anchorStr a}" | .inr z => s!"on {cardStr z}"

private def moveStr : Move → String
  | .draw => "draw"
  | .wasteToFound c => s!"wF {cardStr c}"
  | .wasteToTab c b => s!"wT {cardStr c} {baseStr b}"
  | .tabToFound c => s!"tF {cardStr c}"
  | .foundToTab c b => s!"fT {cardStr c} {baseStr b}"
  | .tabToTab c b => s!"tT {cardStr c} {baseStr b}"

/-! ## The BFS engine (exact Nat keys + hash set) -/

private def suitNum : Suit → Nat
  | .spade => 0 | .heart => 1 | .diamond => 2 | .club => 3

/-- Exact positional encoding: every zone, card by card, base 53. -/
private def cat (k : Nat) (c : Card) : Nat := k * 53 + (13 * suitNum c.suit + c.rank.toIdx + 1)
private def sep (k : Nat) : Nat := k * 53

private def stateKey (st : State) : Nat :=
  let kf := Suit.all.foldl (fun k s => sep ((st.found s).foldl cat (sep k))) 0
  let kp := Anchor.all.foldl (fun k a =>
    let kh := (st.piles a).hidden.foldl cat (sep k)
    sep ((st.piles a).faceUp.foldl cat (sep kh))) kf
  let ks := st.stock.foldl cat (sep kp)
  let kw := sep (st.waste.foldl cat ks)
  kw * 5 + st.drawStep

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

private def succs (st : State) : List (State × Move) :=
  (moveCands st).filterMap (fun m => match State.step st m with
    | some s' => some (s', m) | none => none)

private structure SearchR where
  winDepth : Option Nat
  visited : Nat
  diedAt : Option Nat
  play : List Move
  deriving Nonempty

private partial def bfsAux (budget lvl : Nat) (front : List (State × List Move))
    (vis : Std.HashSet Nat) : SearchR :=
  if front.any (fun s => s.1.isWin) then
    { winDepth := some lvl, visited := vis.size, diedAt := none,
      play := ((front.find? (fun s => s.1.isWin)).map (fun s => s.2)).getD [] }
  else if budget = 0 then
    { winDepth := none, visited := vis.size, diedAt := none, play := [] }
  else
    let next := front.flatMap (fun s =>
      (succs s.1).map (fun q => (q.1, s.2 ++ [q.2])))
    let filtered := next.filter (fun s => !vis.contains (stateKey s.1))
    let init : List (State × List Move) × Std.HashSet Nat := ([], {})
    let (newsD, _) := filtered.foldl (fun acc s =>
      if (acc.2).contains (stateKey s.1) then acc
      else (s :: acc.1, (acc.2).insert (stateKey s.1))) init
    if newsD.isEmpty then
      { winDepth := none , visited := vis.size, diedAt := some lvl, play := [] }
    else
      bfsAux (budget - 1) (lvl + 1) newsD
        (newsD.foldl (fun acc s => acc.insert (stateKey s.1)) vis)

private def runSearch (budget : Nat) (st : State) : SearchR :=
  let vis0 : Std.HashSet Nat := {stateKey st}
  bfsAux budget 0 [(st, [])] vis0

private def verdictOf (budget : Nat) (st : State) : String :=
  let r := runSearch budget st
  match r.winDepth with
  | some d => s!"WIN@{d} (v={r.visited})"
  | none => match r.diedAt with
    | some d => s!"DEAD@{d} (v={r.visited})"
    | none => s!"HORIZON (v={r.visited})"

/-! ## The Q♠ razor corner corpus -/

private def pref (s : Suit) (n : Nat) : List Card := (Suit.upCards s).take n

/-- The rung card: `K♠` over a hidden `J♣` (r = 12; the razor forces
exactly eight live cards: `K♠ J♣ Q♣ K♣ K♥ Q♦ K♦` and the α1 waste
candidate `Q♥`). -/
private def cK : Card := crd .spade .king

private def wfCheck (st : State) : Bool :=
  Card.universe.all (fun c => st.cardCount c == 1)

/-- The quartet the row needs at the window, for a general rung card
`c` on pile 0. -/
private def quartetCheckB (c : Card) (st : State) : Bool :=
  (st.piles Anchor.p0).faceUp == [c]
    && st.topOf Anchor.p0 == some c
    && st.pileOfTop c == some Anchor.p0
    && st.nextUp c && runOK (st.piles Anchor.p0).faceUp

/-- `safeToFound` at the razor bounds for `c` exactly (the ≥-form: the
rung suit at its own index, every other suit within the two bounds) —
the member-level tightness witness stays quartet + razor names. -/
private def razorCheckB (c : Card) (st : State) : Bool :=
  (Suit.all.all fun σ =>
    if σ.color = c.suit.color
    then decide (c.rank.toIdx ≤ st.foundHeight σ + 2)
    else decide (c.rank.toIdx ≤ st.foundHeight σ + 1))
  && st.foundHeight c.suit == c.rank.toIdx

/-- The quartet the row needs at the window. -/
private def quartetCheck (st : State) : Bool := quartetCheckB cK st

/-- Keller razorness for `c = K♠` (r = 12): `h♥, h♦ ≥ 11`, `h♣ ≥ 10`,
`h♠ = 12` — exact-minimum at all four. -/
private def razorCheck (st : State) : Bool := razorCheckB cK st

/-- Corpus frame: founds `♠12 ♥11 ♦11 ♣10`; `p0 = ⟨[J♣], [K♠]⟩` (the
`hcorner` dig), `p1 = [Q♣]`, `p2 = [K♣]`, `p3 = [K♥]`, `p4 = [Q♦]`,
`p5 = [K♦]`, `p6` empty, waste `[Q♥]`, stock empty, drawStep 1. -/
private def kf : State :=
  { found := fun s =>
      match s with
      | .spade => pref .spade 12
      | .heart => pref .heart 11
      | .diamond => pref .diamond 11
      | .club => pref .club 10
    , piles := fun a =>
      match a with
      | .p0 => ⟨[crd .club .jack], [cK]⟩
      | .p1 => ⟨[], [crd .club .queen]⟩
      | .p2 => ⟨[], [crd .club .king]⟩
      | .p3 => ⟨[], [crd .heart .king]⟩
      | .p4 => ⟨[], [crd .diamond .queen]⟩
      | .p5 => ⟨[], [crd .diamond .king]⟩
      | .p6 => ⟨[], []⟩
    , stock := [], waste := [crd .heart .queen], drawStep := 1 }

/-- er1: worry `J♥` (the ♥ top at h♥ = 11) onto `Q♣`-p1 — a clean
`Q♠`-invisible worry: `h♥: 11 → 10`, so the waste tenant `Q♥` is no
longer at its index. -/
private def eroded1 : Option State :=
  match State.step kf (Move.foundToTab (crd .heart .jack) (Sum.inr (crd .club .queen))) with
  | some s' => some s' | none => none

/-- er2: er1 + worry `10♣` (the ♣ top at h♣ = 10) onto `J♥` — the
mixed tower `[Q♣, J♥, 10♣]`; `h♣: 10 → 9` — below the razor twin bound. -/
private def eroded2 : Option State :=
  match eroded1 with
  | none => none
  | some s => match State.step s (Move.foundToTab (crd .club .ten) (Sum.inr (crd .heart .jack))) with
    | some s' => some s' | none => none

/-- The queued variant: `Q♥` over `K♥` in the waste (the queen's
disposal gates the king), `p3` emptied. -/
private def kfQ : State :=
  { kf with
    piles := (fun a =>
      match a with
      | .p3 => ⟨[], []⟩
      | other => kf.piles other)
    waste := [crd .heart .queen, crd .heart .king] }

/-- er3: the queued erode (`J♥` onto `Q♣`) from `kfQ`. -/
private def eroded3 : Option State :=
  match State.step kfQ (Move.foundToTab (crd .heart .jack) (Sum.inr (crd .club .queen))) with
  | some s' => some s' | none => none

/-- er4: er3 + the ♣ spend (`10♣` onto `J♥`) — queued and twin-below. -/
private def eroded4 : Option State :=
  match eroded3 with
  | none => none
  | some s => match State.step s (Move.foundToTab (crd .club .ten) (Sum.inr (crd .heart .jack))) with
    | some s' => some s' | none => none

/-! ## The club-rung twin seed (the suit-mirrored razor) -/

/-- The club rung: `K♣` over a hidden `J♠` (r = 12; the same razor
economy mirrored — eight live cards `K♣ J♠ Q♠ K♠ K♥ Q♦ K♦` and the
waste candidate `Q♥`). -/
private def cC : Card := crd .club .king

/-- Mirror frame: founds `♣12 ♥11 ♦11 ♠10`; `p0 = ⟨[J♠], [K♣]⟩` (the
dig), `p1 = [Q♠]`, `p2 = [K♠]`, `p3 = [K♥]`, `p4 = [Q♦]`, `p5 =
[K♦]`, `p6` empty, waste `[Q♥]`, stock empty, drawStep 1. -/
private def kfC : State :=
  { found := fun s =>
      match s with
      | .spade => pref .spade 10
      | .heart => pref .heart 11
      | .diamond => pref .diamond 11
      | .club => pref .club 12
    , piles := fun a =>
      match a with
      | .p0 => ⟨[crd .spade .jack], [cC]⟩
      | .p1 => ⟨[], [crd .spade .queen]⟩
      | .p2 => ⟨[], [crd .spade .king]⟩
      | .p3 => ⟨[], [crd .heart .king]⟩
      | .p4 => ⟨[], [crd .diamond .queen]⟩
      | .p5 => ⟨[], [crd .diamond .king]⟩
      | .p6 => ⟨[], []⟩
    , stock := [], waste := [crd .heart .queen], drawStep := 1 }

/-- erC1: worry `J♥` (the ♥ top at h♥ = 11) onto `Q♠`-p1 — the
mirrored clean worry; `h♥: 11 → 10`, `Q♥` stranded. -/
private def erodedC1 : Option State :=
  match State.step kfC (Move.foundToTab (crd .heart .jack) (Sum.inr (crd .spade .queen))) with
  | some s' => some s' | none => none

/-- erC2: erC1 + worry `10♠` (the ♠ top at h♠ = 10) onto `J♥` — the
mirrored mixed tower `[Q♠, J♥, 10♠]`; `h♠: 10 → 9` — the black twin
spent below the razor bound. -/
private def erodedC2 : Option State :=
  match erodedC1 with
  | none => none
  | some s => match State.step s (Move.foundToTab (crd .spade .ten) (Sum.inr (crd .heart .jack))) with
    | some s' => some s' | none => none

/-- The slack-1 coverable world (W6's root): the corner of `K♠` at
heights one club above the razor (`h♣ = 11`, still
`safeToFound`-consistent), where the parked `Q♥` HAS an available
cover — the foundation-top `J♣` (founded but not deep).  Founds
`♠12 ♥11 ♦11 ♣11`; `p0 = ⟨[K♥], [K♠]⟩` (the dig is `K♥`), `p1 =
[Q♣]`, `p2 = [K♣]`, `p3 = [Q♦]`, `p4 = [K♦]`, `p5`/`p6` empty,
waste `[Q♥]`. -/
private def q6 : State :=
  { found := fun s =>
      match s with
      | .spade => pref .spade 12
      | .heart => pref .heart 11
      | .diamond => pref .diamond 11
      | .club => pref .club 11
    , piles := fun a =>
      match a with
      | .p0 => ⟨[crd .heart .king], [cK]⟩
      | .p1 => ⟨[], [crd .club .queen]⟩
      | .p2 => ⟨[], [crd .club .king]⟩
      | .p3 => ⟨[], [crd .diamond .queen]⟩
      | .p4 => ⟨[], [crd .diamond .king]⟩
      | .p5 => ⟨[], []⟩
      | .p6 => ⟨[], []⟩
    , stock := [], waste := [crd .heart .queen], drawStep := 1 }

private def seeds : List (String × Card × State) :=
  [("razor K♠ (h♥=h♦=11, h♣=10; J♣ digs)", cK, kf)]
  ++ (match eroded1 with | none => [] | some u => [("er1 (h♥=10, Q♥ stranded in waste)", cK, u)])
  ++ (match eroded2 with | none => [] | some u => [("er2 (h♣=9, mixed tower on p1)", cK, u)])
  ++ (match eroded3 with | none => [] | some u => [("er3 (queued: Q♥ over K♥, h♥=10)", cK, u)])
  ++ (match eroded4 with | none => [] | some u => [("er4 (queued + h♣=9, two towers)", cK, u)])
  ++ [("razorC K♣ (mirrored seed, J♠ digs)", cC, kfC)]
  ++ (match erodedC1 with | none => [] | some u => [("erC1 (h♥=10, Q♥ stranded)", cC, u)])
  ++ (match erodedC2 with | none => [] | some u => [("erC2 (h♠=9, mirrored tower)", cC, u)])
  ++ [("slack1 q6 (coverable world, h♣=11)", cK, q6)]


private def legalMoves (st : State) : List Move :=
  (moveCands st).filter (fun m => (State.step st m).isSome)

/-! ## Raise-priority DFS win finder

The corpus wins are raise-climbs of depth <= 15 plus the odd erode-heal;
a raise-first ordered DFS with a cycle set finds them in a handful of
nodes.  (This only CERTIFIES wins — a NO-WIN is a smoke gun, not a
verdict; an exhaustive BFS settles any suspicious member by hand.) -/

private def movePrio : Move -> Nat
  | .wasteToFound _ => 0
  | .tabToFound _ => 1
  | .tabToTab _ _ => 2
  | .foundToTab _ _ => 3
  | .wasteToTab _ _ => 4
  | .draw => 5

private def orderedMoves (st : State) : List Move :=
  let l := legalMoves st
  -- insertion sort by `movePrio` (small lists; no core `sortBy` here)
  let ins (m : Move) (acc : List (Nat × Move)) : List (Nat × Move) :=
    let p := movePrio m
    let rec go (l : List (Nat × Move)) : List (Nat × Move) :=
      match l with
      | [] => [(p, m)]
      | h :: t => if p ≤ h.1 then (p, m) :: h :: t else h :: go t
    go acc
  (l.foldl (fun acc m => ins m acc) []).map (fun x => x.2)

/-- Depth-limited DFS, single tail-recursive loop over an explicit
stack of frames (state, path, remaining moves); a node cap bounds the
visit count.  A win may be reported early, at the child step. -/
private partial def dfsLoop (fuel cap : Nat)
    (stack : List (State × List Move × List Move))
    (vis : Std.HashSet Nat) (nodes : Nat) : Option (List Move) × Nat :=
  match fuel, stack with
  | 0, _ => (none, nodes)
  | _, [] => (none, nodes)
  | _+1, (st, path, []) :: tl => dfsLoop fuel cap tl vis nodes
  | _+1, (st, path, m :: rest) :: tl =>
    if st.isWin then (some path.reverse, nodes)
    else if nodes ≥ cap then (none, nodes)
    else match State.step st m with
      | none => dfsLoop fuel cap ((st, path, rest) :: tl) vis nodes
      | some s' =>
        if s'.isWin then (some (m :: path).reverse, nodes + 1)
        else if vis.contains (stateKey s') then
          dfsLoop fuel cap ((st, path, rest) :: tl) vis nodes
        else
          dfsLoop fuel cap
            ((s', m :: path, orderedMoves s') :: (st, path, rest) :: tl)
            (vis.insert (stateKey s')) (nodes + 1)

private def dfsWin (fuel : Nat) (st : State) : Option (List Move) × Nat :=
  if st.isWin then (some [], 0)
  else
    let vis : Std.HashSet Nat := {stateKey st}
    dfsLoop fuel 400000 [(st, [], orderedMoves st)] vis 1

/-! ## Single-pass analysis (DFS win certificates) -/

private structure Analysis where
  name : String
  wf : Bool
  quartet : Bool
  razor : Bool
  heights : String
  src : String
  raised : String
  suspicious : Bool
  srcPlay : String
  raisedPlay : String
  vacuous : Bool

private def analyzeOn (c : Card) (name : String) (u : State) : Analysis :=
  let src := dfsWin 36 u
  let raisedSt := match State.step u (Move.tabToFound c) with
    | some s' => s'
    | none => u
  let raised := dfsWin 36 raisedSt
  let wstr (r : Option (List Move) × Nat) : String :=
    match r.1 with
    | some p => s!"WIN(len={p.length}, nodes={r.2})"
    | none => s!"NO-WIN(nodes={r.2})"
  { name := name, wf := wfCheck u, quartet := quartetCheckB c u, razor := razorCheckB c u
  , heights := s!"h:{u.foundHeight .heart}/{u.foundHeight .diamond}/{u.foundHeight .club}/{u.foundHeight .spade}"
  , src := wstr src, raised := wstr raised
  , suspicious := match src.1, raised.1 with
    | some _, none => true
    | _, _ => false
  , srcPlay := match src.1 with
    | none => "-"
    | some p => String.intercalate " ; " (p.map moveStr)
  , raisedPlay := match raised.1 with
    | none => "-"
    | some p => String.intercalate " ; " (p.map moveStr)
  , vacuous := src.1.isNone }

private def reportLine (a : Analysis) : String :=
  s!"[{a.name}] wf={a.wf} quartet={a.quartet} razor={a.razor} {a.heights} " ++
  s!"src={a.src} raised={a.raised}" ++
  (if a.suspicious then "  ??? SUSPICIOUS (raised world found no win — hand-check)" else "")

/-! ## The spread-window carry cases (W1..W6)

Each W-case is a state PAIR: `win` = the window thread (the opener[s]
applied to a corpus root), `root` = the pair-deleted/reshaped thread;
`srcPlay` is a hand-composed winning play from `win` whose window
slice is `srcSlice`; `refPlay` is the transformed play from `root`
whose slice is `refSlice`.  The oracle verifies: both plays run and
win, and the two SLICES land at the SAME exact state key.  A failing
asymmetry is the falsifier shape and the exe throws. -/

private def tF (c : Card) : Move := Move.tabToFound c
private def wF (c : Card) : Move := Move.wasteToFound c
private def fT (c : Card) (b : Base) : Move := Move.foundToTab c b
private def wT (c : Card) (b : Base) : Move := Move.wasteToTab c b
private def tT (c : Card) (b : Base) : Move := Move.tabToTab c b

private def then1 (o : Option State) (m : Move) : Option State :=
  o >>= fun s => State.step s m

/-- W1: the α1 spread — `Q♥` parked on `K♠` at er2, the mirrored
c-blind tower raises between, the restack from the parked seat; the
deleted thread runs the same suits plus the DELAYED waste closer at
the window end. -/
private def spreadA : Option State :=
  then1 eroded2 (wT (crd .heart .queen) (Sum.inr cK))

/-- W1-mirror: the α1 spread at the club razor (Q♥ on K♣ at erC2,
the ♠ tower raises between). -/
private def spreadAC : Option State :=
  then1 erodedC2 (wT (crd .heart .queen) (Sum.inr cC))

/-- W3: the queued α1 spread (Q♥ parked with K♥ behind it in the
waste). -/
private def spreadAQ : Option State :=
  then1 eroded3 (wT (crd .heart .queen) (Sum.inr cK))

/-- W4: the β spread — `Q♠` (the ♠ foundation top at kf) worried onto
`K♥`@p3, a cross-suit raise and the waste raise between, its restack;
the deleted thread simply drops the pair. -/
private def qbeta : Option State :=
  then1 (some kf) (fT (crd .spade .queen) (Sum.inr (crd .heart .king)))

/-- W5: the covered foundation-park bubble — `J♥` parked ON the
worried `Q♠` (the cover), evicted to `Q♣`, restacked; the whole
three-move bubble nets to zero and the deleted thread runs nothing. -/
private def coverUC : Option State :=
  then1 qbeta (fT (crd .heart .jack) (Sum.inr (crd .spade .queen)))

/-- W6: the covered waste-park at the slack-1 heights.  At the razor
heights the parked tenant `Q♥` has no available cover (her black
jacks are the founded-deep `J♠` and `c`'s own dig partner `J♣`,
hidden under `K♠` until the rung), so this member spends one club
slack: the window opens with the park of `Q♥` on `c` and the COVER
`fT J♣` onto the parked `Q♥` (the E3 shape on an α1 window); σ
raises the diamonds blind; the un-cover re-raises `J♣` from the
covered seat and the restack takes `Q♥`.  The deleted thread runs σ
verbatim and takes the delayed waste closer — the cover bubble nets
to zero. -/
private def coverW : Option State :=
  then1 (then1 (some q6) (wT (crd .heart .queen) (Sum.inr cK)))
    (fT (crd .club .jack) (Sum.inr (crd .heart .queen)))

private structure WindowCase where
  name : String
  c : Card
  root : State
  win : State
  srcSlice : List Move
  srcPlay : List Move
  refSlice : List Move
  refPlay : List Move

private def case1 : Option WindowCase := do
  let r ← eroded2
  let w ← spreadA
  let slice := [tF (crd .club .ten), tF (crd .heart .jack), tF (crd .heart .queen)]
  let refSlice := [tF (crd .club .ten), tF (crd .heart .jack), wF (crd .heart .queen)]
  let tail := [tF (crd .heart .king), tF cK, tF (crd .club .jack),
    tF (crd .club .queen), tF (crd .club .king), tF (crd .diamond .queen),
    tF (crd .diamond .king)]
  let kc : WindowCase :=
    { name := "W1 α1-spread (parked Q♥; tower raises between; delayed closer)"
    , c := cK
    , root := r
    , win := w
    , srcSlice := slice
    , srcPlay := slice ++ tail
    , refSlice := refSlice
    , refPlay := refSlice ++ tail }
  return kc

private def case1C : Option WindowCase := do
  let r ← erodedC2
  let w ← spreadAC
  let slice := [tF (crd .spade .ten), tF (crd .heart .jack), tF (crd .heart .queen)]
  let refSlice := [tF (crd .spade .ten), tF (crd .heart .jack), wF (crd .heart .queen)]
  let tail := [tF (crd .heart .king), tF cC, tF (crd .spade .jack),
    tF (crd .spade .queen), tF (crd .spade .king), tF (crd .diamond .queen),
    tF (crd .diamond .king)]
  let kc : WindowCase :=
    { name := "W1' α1-spread mirrored at the club razor"
    , c := cC
    , root := r
    , win := w
    , srcSlice := slice
    , srcPlay := slice ++ tail
    , refSlice := refSlice
    , refPlay := refSlice ++ tail }
  return kc

private def case3 : Option WindowCase := do
  let r ← eroded3
  let w ← spreadAQ
  let slice := [tF (crd .heart .jack), tF (crd .heart .queen)]
  let refSlice := [tF (crd .heart .jack), wF (crd .heart .queen)]
  let tail := [wF (crd .heart .king), tF cK, tF (crd .club .jack),
    tF (crd .club .queen), tF (crd .club .king), tF (crd .diamond .queen),
    tF (crd .diamond .king)]
  let kc : WindowCase :=
    { name := "W3 α1-spread queued (K♥ behind the parked Q♥)"
    , c := cK
    , root := r
    , win := w
    , srcSlice := slice
    , srcPlay := slice ++ tail
    , refSlice := refSlice
    , refPlay := refSlice ++ tail }
  return kc

private def case4 : Option WindowCase := do
  let r := kf
  let w ← qbeta
  let slice := [tF (crd .diamond .queen), tF (crd .spade .queen)]
  let refSlice := [tF (crd .diamond .queen)]
  let tail := [wF (crd .heart .queen), tF (crd .heart .king),
    tF (crd .diamond .king), tF cK, tF (crd .club .jack),
    tF (crd .club .queen), tF (crd .club .king)]
  let kc : WindowCase :=
    { name := "W4 β-spread (Q♠ worry onto K♥; cross-suit raises between)"
    , c := cK
    , root := r
    , win := w
    , srcSlice := slice
    , srcPlay := slice ++ tail
    , refSlice := refSlice
    , refPlay := refSlice ++ tail }
  return kc

private def case5 : Option WindowCase := do
  let r ← qbeta
  let w ← coverUC
  let slice := [tT (crd .heart .jack) (Sum.inr (crd .club .queen)),
    tF (crd .heart .jack)]
  let slice' := ([] : List Move)
  let tail := [tF (crd .spade .queen), wF (crd .heart .queen),
    tF (crd .heart .king), tF cK, tF (crd .club .jack),
    tF (crd .club .queen), tF (crd .club .king), tF (crd .diamond .queen),
    tF (crd .diamond .king)]
  let kc : WindowCase :=
    { name := "W5 covered fT-park bubble (eviction + restack nets to zero)"
    , c := cK
    , root := r
    , win := w
    , srcSlice := slice
    , srcPlay := slice ++ tail
    , refSlice := slice'
    , refPlay := tail }
  return kc

private def case6 : Option WindowCase := do
  let r := q6
  let w ← coverW
  let slice := [tF (crd .diamond .queen), tF (crd .diamond .king),
    tF (crd .club .jack), tF (crd .heart .queen)]
  let refSlice := [tF (crd .diamond .queen), tF (crd .diamond .king),
    wF (crd .heart .queen)]
  let tail := [tF cK, tF (crd .heart .king), tF (crd .club .queen),
    tF (crd .club .king)]
  let kc : WindowCase :=
    { name := "W6 covered wT-park (cover bubble at slack-1 heights nets to zero)"
    , c := cK
    , root := r
    , win := w
    , srcSlice := slice
    , srcPlay := slice ++ tail
    , refSlice := refSlice
    , refPlay := refSlice ++ tail }
  return kc

private def case7 : Option WindowCase := do
  let r := kf
  let leg1 := [wF (crd .heart .queen), tF cK]
  let leg2 := [tF cK, wF (crd .heart .queen)]
  let tail := [tF (crd .heart .king), tF (crd .club .jack),
    tF (crd .club .queen), tF (crd .club .king), tF (crd .diamond .queen),
    tF (crd .diamond .king)]
  let kc : WindowCase :=
    { name := "W2 diamond K♠ (tenant raise commutes with the rung raise)"
    , c := cK
    , root := r
    , win := r
    , srcSlice := leg1
    , srcPlay := leg1 ++ tail
    , refSlice := leg2
    , refPlay := leg2 ++ tail }
  return kc

private def case8 : Option WindowCase := do
  let r := kfC
  let leg1 := [wF (crd .heart .queen), tF cC]
  let leg2 := [tF cC, wF (crd .heart .queen)]
  let tail := [tF (crd .heart .king), tF (crd .spade .jack),
    tF (crd .spade .queen), tF (crd .spade .king), tF (crd .diamond .queen),
    tF (crd .diamond .king)]
  let kc : WindowCase :=
    { name := "W2' diamond K♣ (mirrored)"
    , c := cC
    , root := r
    , win := r
    , srcSlice := leg1
    , srcPlay := leg1 ++ tail
    , refSlice := leg2
    , refPlay := leg2 ++ tail }
  return kc

private def windowCases : List WindowCase :=
  [case1, case1C, case3, case4, case5, case6, case7, case8].filterMap id

private structure CaseVerdict where
  name : String
  wfR : Bool
  wfW : Bool
  quartet : Bool
  srcRun : Bool
  refRun : Bool
  srcWin : Bool
  refWin : Bool
  sliceEq : Bool
  det : String

private def evalCase (k : WindowCase) : CaseVerdict :=
  let sr := k.win.run k.srcPlay
  let rr := k.root.run k.refPlay
  let ss := k.win.run k.srcSlice
  let rs := k.root.run k.refSlice
  let runOK' (o : Option State) : Bool := match o with | some _ => true | none => false
  let winOK (o : Option State) : Bool := match o with | some w => w.isWin | none => false
  let keys := match ss, rs with
    | some a, some b => s!"keys {stateKey a} ?= {stateKey b}"
    | _, _ => "slice dead"
  { name := k.name, wfR := wfCheck k.root, wfW := wfCheck k.win
  , quartet := quartetCheckB k.c k.root
  , srcRun := runOK' sr, refRun := runOK' rr, srcWin := winOK sr, refWin := winOK rr
  , sliceEq :=
      match ss, rs with
      | some a, some b => stateKey a == stateKey b
      | _, _ => false
  , det := s!"src={match sr with | some w => s!"win?{w.isWin}" | none => "DEAD"} " ++
      s!"ref={match rr with | some w => s!"win?{w.isWin}" | none => "DEAD"}; {keys}" }

/-! ## Entry point -/

def main : IO Unit := do
  let t0 ← IO.monoMsNow
  let mut results : List Analysis := []
  for x in seeds do
    let t ← IO.monoMsNow
    let a := analyzeOn x.2.1 x.1 x.2.2
    let t' ← IO.monoMsNow
    IO.println (reportLine a)
    if a.vacuous then
      IO.println s!"    (vacuous: no source win; {t' - t} ms)"
    else
      IO.println s!"    ({t' - t} ms)"
      IO.println s!"    src:    {a.srcPlay.take 500}"
      IO.println s!"    raised: {a.raisedPlay.take 500}"
    results := a :: results
  let final := results.reverse
  IO.println "---"
  if final.any (fun a => !(a.wf && a.quartet) && !(a.name.startsWith "razor" && !a.razor)) then
    throw (IO.userError
      s!"CORPUS ILL-FORMED: {(final.filter (fun a => !a.wf || !a.quartet || (a.name.startsWith "razor" && !a.razor))).map (fun a => a.name)}")
  if !final.any (fun a => !a.vacuous) then
    throw (IO.userError "corpus vacuous: no member won — widen before trusting")
  if final.any (fun a => a.suspicious) then
    throw (IO.userError
      s!"SUSPICIOUS MEMBERS (raised world found no win): {(final.filter (fun a => a.suspicious)).map (fun a => a.name)} — hand-check these")
  -- the spread-window carry gate
  let mut verdicts : List CaseVerdict := []
  for k in windowCases do
    let v := evalCase k
    IO.println s!"[{v.name}] wf={v.wfR}/{v.wfW} quartet@root={v.quartet} src={v.srcRun}/{v.srcWin} ref={v.refRun}/{v.refWin} sliceEq={v.sliceEq}"
    IO.println s!"    {v.det}"
    verdicts := v :: verdicts
  let vs := verdicts.reverse
  IO.println "---"
  let malformed := vs.filter (fun v => !(v.wfR && v.wfW && v.srcRun) || !v.srcWin)
  if !malformed.isEmpty then
    throw (IO.userError
      s!"WINDOW CASES ILL-FORMED (hand play dead or member not WF): {malformed.map (fun v => v.name)}")
  let falsified := vs.filter (fun v => !v.refRun || !v.refWin || !v.sliceEq)
  if !falsified.isEmpty then
    throw (IO.userError
      s!"WINDOW GATE FAILED (the carry falsified at): {falsified.map (fun v => v.name)} — this is the falsifier shape; hand-exhaust before any repair")
  let t1 ← IO.monoMsNow
  IO.println s!"all sustained ({t1 - t0} ms total)"

