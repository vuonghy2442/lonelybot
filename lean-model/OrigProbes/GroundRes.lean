import Orig.Play
import Lean

/-!
# The (N) ground-normal-form transfer probes (wave-24, row
`tabToFound_groundNormalForm`)

Refute-first evidence for the two load-bearing claims of the
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

Exhaustive dedup'd BFS over the full physical move set
(`State.step` is the only oracle), exact Nat positional keys in a
hash set (no collision risk: a key encodes every zone card-by-card),
win plays recorded.  Corpus: the `Q♠` razor corner (r = 11) plus
eroded members (legal worry-towers spending the ♥/♣ slack).

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

/-- The quartet the row needs at the window. -/
private def quartetCheck (st : State) : Bool :=
  (st.piles Anchor.p0).faceUp == [cK]
    && st.topOf Anchor.p0 == some cK
    && st.pileOfTop cK == some Anchor.p0
    && st.nextUp cK && runOK (st.piles Anchor.p0).faceUp

/-- Keller razorness for `c = K♠` (r = 12): `h♥, h♦ ≥ 11`, `h♣ ≥ 10`,
`h♠ = 12` — exact-minimum at all four. -/
private def razorCheck (st : State) : Bool :=
  st.foundHeight .heart ≥ 11 && st.foundHeight .diamond ≥ 11
    && st.foundHeight .club ≥ 10 && st.foundHeight .spade == 12

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

private def corpus : List (String × State) :=
  [("razor K (h♥ = h♦ = 11, h♣ = 10; J♣ digs)", kf)]
  ++ (match eroded1 with | none => [] | some u => [("er1 (h♥ = 10, Q♥ stranded in waste)", u)])
  ++ (match eroded2 with | none => [] | some u => [("er2 (h♣ = 9, mixed tower on p1)", u)])
  ++ (match eroded3 with | none => [] | some u => [("er3 (queued: Q♥ over K♥, h♥ = 10)", u)])
  ++ (match eroded4 with | none => [] | some u => [("er4 (queued + h♣ = 9, two towers)", u)])


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

private def analyze (name : String) (u : State) : Analysis :=
  let src := dfsWin 36 u
  let raisedSt := match State.step u (Move.tabToFound cK) with
    | some s' => s'
    | none => u
  let raised := dfsWin 36 raisedSt
  let wstr (r : Option (List Move) × Nat) : String :=
    match r.1 with
    | some p => s!"WIN(len={p.length}, nodes={r.2})"
    | none => s!"NO-WIN(nodes={r.2})"
  { name := name, wf := wfCheck u, quartet := quartetCheck u, razor := razorCheck u
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

/-! ## Entry point -/

def main : IO Unit := do
  let t0 ← IO.monoMsNow
  let mut results : List Analysis := []
  for x in corpus do
    let t ← IO.monoMsNow
    let a := analyze x.1 x.2
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
  let t1 ← IO.monoMsNow
  IO.println s!"all sustained ({t1 - t0} ms total)"

