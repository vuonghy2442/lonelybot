import Orig.Play

/-! # DeterminismProbe — the pull-multiset descent-determinism battery

The decide-battery for the descent-determinism family of
`Orig/MacroInternal.lean` (branch `orig-macro-determinism`): the
pull letter's pops are FORCED top-down by the `foundTop` guard, so
the multiset of pulled cards along a descent from a rank-disciplined
anchor is a function of the height-tuple delta alone — never of the
path taken.  The theorem-grade half lives in the library
(`cone_pop_window` / `cone_pulls_congr_tuple`); this file is the
EVIDENCE side, per the house rule stated before any proof effort:

* **D1 — the popped card IS the current top**: every legal `foundToTab`
  at every state the census enumerates names its suit's founded top
  and chops exactly that card (the `foundTop = some c` guard, the
  `chop` write).  This is the raw forcing row.
* **D2 — the window row**: for every enumerated walk, the per-suit pop
  list equals the FORCED WINDOW — `(anchor.found s).drop (rung s at
  the endpoint)`, reversed — the executable mirror of the master.
* **D3 — the determinism census**: among all pairs of walks, no two
  same-tuple endpoints ever disagree on the pulled MULTISET
  (expect-ABSENT: the candidate violator shapes; the counts are
  reported so the gate has teeth).  Non-vacuity rows pin the other
  side: same-tuple pairs EXIST (including order-differing pop lists —
  `[pop♠, pop♥]` routes vs `[pop♥, pop♠]` routes), and different-tuple
  pairs with genuinely different multisets EXIST.

The census engine enumerates every legal pull / slide / draw play
from each cell up to a bounded depth, via `State.step` as the only
oracle; the menus are complete by the guards' own shapes (a pull's
card is perforce a suit's founded top; a relocation's card is
perforce face-up; a placement base is perforce an anchor or a pile
top).  Slides and draws here are NOT reversible-filtered: the
determinism law is step-semantic, so the census ranges over the
superset — a cone restart is a special path — and the family's
negative controls remain valid over the superset (no violator pair
exists in it).

The cells are the twin-king convention consumed from the canon-v3
census craft (`probes/CanonV3Probe.lean`'s families on branch
`orig-canon-v3`): full-deck WF cells with the founded royalty
climbed, both twin-king geometries represented (the bare king, the
covered king under its queen).  Nothing here is imported by the
library; no state-equality is needed anywhere (the census compares
rung tuples and card multisets only); the probe's popWindow mirror
is the dedup-marked shape of the library's `popWindow`.

Run: `lake env lean probes/DeterminismProbe.lean` (after
`lake build Orig`); every gate below must print `true`.
-/

/-- The census-clean stock mover: the deck minus the seated or
founded cards (the exchlaw lesson, consumed from the canon-v3
battery's `v3Stock`). -/
def dtStock (exclude : List Card) : List Card :=
  Card.universe.filter fun c => decide (c ∉ exclude)

/-- The WF check, as an evaluable Bool mirror (the dedup-marked
four-conjunct shape; every crafted cell partitions the full deck). -/
def dtWfB (st : State) : Bool :=
  Suit.all.all (fun s => decide (s.upCards.take (st.found s).length == st.found s)) &&
  Anchor.all.all (fun a => runOK (st.piles a).faceUp == true) &&
  Card.universe.all (fun c => st.cardCount c == 1) &&
  decide (0 < st.drawStep)

/-! ## The deterministic mirrors (dedup-marked against the library) -/

/-- The rung (the shape of the library's `rungAt`). -/
def dtRung (st : State) (s : Suit) : Nat := (st.found s).length

/-- The forced pop window (the shape of the library's `popWindow`):
the founded prefix's drop, reversed — top first. -/
def dtWindow (l : List Card) (j : Nat) : List Card := (l.drop j).reverse

/-- The multiset reading of two pop ledgers: equal populations per
card. -/
def dtMsEq (l1 l2 : List Card) : Bool :=
  Card.universe.all fun c =>
    l1.countP (fun x => decide (x = c)) == l2.countP (fun x => decide (x = c))

/-- The height tuple of an endpoint. -/
def dtTuple (st : State) : List Nat := Suit.all.map (dtRung st)

/-! ## The leg menus (complete by the guards' own shapes) -/

/-- All pile-top cards. -/
def dtTops (st : State) : List Card :=
  Anchor.all.filterMap st.topOf

/-- Every legal base: an anchor or a pile top (a placement's judgment
never consults a buried card). -/
def dtBaseMenu (st : State) : List Base :=
  Anchor.all.map Sum.inl ++ (dtTops st).map Sum.inr

/-- Every face-up card (a relocation source is perforce seated). -/
def dtFaceUps (st : State) : List Card :=
  Anchor.all.flatMap fun a => (st.piles a).faceUp

/-- Every suit's founded top (a pull's card is perforce one). -/
def dtTopCards (st : State) : List Card :=
  Suit.all.filterMap st.foundTop

/-- The legal pulls at `st`, with the popped card named. -/
def dtPullsAt (st : State) : List (Card × State) :=
  (dtTopCards st).flatMap fun c =>
    (dtBaseMenu st).filterMap fun bas =>
      (st.step (Move.foundToTab c bas)).map fun s' => (c, s')

/-- The legal relocations at `st`. -/
def dtSlidesAt (st : State) : List State :=
  (dtFaceUps st).flatMap fun c =>
    (dtBaseMenu st).filterMap fun bas => st.step (Move.tabToTab c bas)

/-- The legal draws at `st`. -/
def dtDrawAt (st : State) : List State :=
  (st.step Move.draw).toList

/-! ## The walk engine -/

/-- Every (endpoint, pop-ledger) pair of a pull/slide/draw play of
length at most `d`, pop ledgers in pop order (oldest head). -/
def dtWalks (st : State) : Nat → List (State × List Card)
  | 0 => [(st, [])]
  | d + 1 =>
      (st, []) ::
      (dtPullsAt st).flatMap
        (fun (c, s') => (dtWalks s' d).map fun (e, ps) => (e, c :: ps)) ++
      (dtSlidesAt st).flatMap (fun s' => dtWalks s' d) ++
      (dtDrawAt st).flatMap (fun s' => dtWalks s' d)

/-! ## The census rows -/

/-- D1 at one state: every legal pull pops literally the current
founded top and chops the foundation. -/
def dtPullsCheckOK (st : State) : Bool :=
  (dtPullsAt st).all fun (c, s') =>
    st.foundTop c.suit == some c && s'.found c.suit == chop (st.found c.suit)

/-- D2 for one walk: the per-suit pop list is the forced window. -/
def dtWindowOKWalk (anchor : State) (e : State) (ps : List Card) : Bool :=
  Suit.all.all fun s =>
    (ps.filter fun x => decide (x.suit = s)) == dtWindow (anchor.found s) (dtRung e s)

/-- D1 over every state the census enumerates (every walk endpoint). -/
def dtPullsRow (st : State) (d : Nat) : Bool :=
  (dtWalks st d).all fun (e, _) => dtPullsCheckOK e

/-- D2 over every enumerated walk. -/
def dtWindowRow (st : State) (d : Nat) : Bool :=
  (dtWalks st d).all fun (e, ps) => dtWindowOKWalk st e ps

/-- D3's expect-absent count: same-tuple endpoint pairs with
genuinely different pop MULTISETS — the candidate violator shapes. -/
def dtViolPairCount (st : State) (d : Nat) : Nat :=
  ((dtWalks st d).flatMap fun w1 =>
    (dtWalks st d).filter fun w2 =>
      (dtTuple w1.1 == dtTuple w2.1) && !dtMsEq w1.2 w2.2).length

/-- Non-vacuity: same-tuple endpoint pairs (walk count). -/
def dtSameTuplePairCount (st : State) (d : Nat) : Nat :=
  ((dtWalks st d).flatMap fun w1 =>
    (dtWalks st d).filter fun w2 => dtTuple w1.1 == dtTuple w2.1).length

/-- Non-vacuity with teeth: same-tuple pairs whose pop lists differ
in ORDER yet agree as multisets — the determinism phenomenon,
visible (interleaved suit pops land in different orders at the same
tuple). -/
def dtOrderDiffPairCount (st : State) (d : Nat) : Nat :=
  ((dtWalks st d).flatMap fun w1 =>
    (dtWalks st d).filter fun w2 =>
      (dtTuple w1.1 == dtTuple w2.1) && !(w1.2 == w2.2) && dtMsEq w1.2 w2.2).length

/-- The negative control with teeth: different-tuple pairs with
different multisets exist (the assertion engine is not vacuous). -/
def dtDiffTupleDiffMsCount (st : State) (d : Nat) : Nat :=
  ((dtWalks st d).flatMap fun w1 =>
    (dtWalks st d).filter fun w2 =>
      !(dtTuple w1.1 == dtTuple w2.1) && !dtMsEq w1.2 w2.2).length

/-! ## Cell 1 — the interleaving cell (the order-differing routes) -/

private def dtH6 : Card := ⟨Suit.heart, Rank.six⟩
private def dtC4 : Card := ⟨Suit.club, Rank.four⟩
private def dtD7 : Card := ⟨Suit.diamond, Rank.seven⟩
private def dtC6 : Card := ⟨Suit.club, Rank.six⟩
private def dtH9 : Card := ⟨Suit.heart, Rank.nine⟩
private def dtS8 : Card := ⟨Suit.spade, Rank.eight⟩
private def dtD9 : Card := ⟨Suit.diamond, Rank.nine⟩

/-- Spades climbed A..5, hearts A..3; the spade-pop base (♥6) and
the heart-pop base (♣4) seated; two relocation families ([♦7, ♣6],
[♥9, ♠8] over the free red nine ♦9).  Both pops are independent, so
their interleavings and a relocation's detours reach equal tuples
with order-differing pop lists. -/
def dtC1 : State where
  found := fun s =>
    match s with
    | .spade => Suit.spade.upCards.take 5
    | .heart => Suit.heart.upCards.take 3
    | _ => []
  piles := fun a =>
    match a with
    | .p1 => ⟨[], [dtH6]⟩
    | .p2 => ⟨[], [dtC4]⟩
    | .p3 => ⟨[], [dtD7, dtC6]⟩
    | .p4 => ⟨[], [dtH9, dtS8]⟩
    | .p5 => ⟨[], [dtD9]⟩
    | _ => ⟨[], []⟩
  stock := dtStock
    (Suit.spade.upCards.take 5 ++ Suit.heart.upCards.take 3 ++
      [dtH6, dtC4, dtD7, dtC6, dtH9, dtS8, dtD9])
  waste := []
  drawStep := 1

/-- The cell-1 gate: WF, D1, D2, the expect-absent violator count,
and the three non-vacuity rows. -/
def dtGateC1 : Bool :=
  dtWfB dtC1 &&
  dtPullsRow dtC1 3 &&
  dtWindowRow dtC1 3 &&
  (dtViolPairCount dtC1 3 == 0) &&
  (dtSameTuplePairCount dtC1 3 ≥ 1) &&
  (dtOrderDiffPairCount dtC1 3 ≥ 1) &&
  (dtDiffTupleDiffMsCount dtC1 3 ≥ 1)

/-! ## Cell 2 — the twin-king cell (the canon-v3 census convention) -/

private def dtHK : Card := ⟨Suit.heart, Rank.king⟩
private def dtDK : Card := ⟨Suit.diamond, Rank.king⟩
private def dtSK : Card := ⟨Suit.spade, Rank.king⟩
private def dtSQ : Card := ⟨Suit.spade, Rank.queen⟩

/-- The B2 fork-family geometry, consumed from the canon-v3
twin-king cells: hearts climbed A..Q, diamonds A..J; ♥K BARE on p1
(the freeness face), ♦K COVERED under ♠Q on p5 (the fork face — the
cover is a queen of the opposite color, the standing-fork signature),
♠K the black-king seat for the ♥Q pop, the covered king's own cover
the seat for the ♦J pop, and ♥K a king-reseating slide (the cargo
family: bare kings relocate only between free anchors).  Both twin
suits pop: ♥Q lands on ♠K; ♦J lands ON the covered king's cover. -/
def dtC2 : State where
  found := fun s =>
    match s with
    | .heart => Suit.heart.upCards.take 12
    | .diamond => Suit.diamond.upCards.take 11
    | _ => []
  piles := fun a =>
    match a with
    | .p1 => ⟨[], [dtHK]⟩
    | .p2 => ⟨[], [dtSK]⟩
    | .p5 => ⟨[], [dtDK, dtSQ]⟩
    | _ => ⟨[], []⟩
  stock := dtStock
    (Suit.heart.upCards.take 12 ++ Suit.diamond.upCards.take 11 ++
      [dtHK, dtDK, dtSK, dtSQ])
  waste := []
  drawStep := 1

/-- The cell-2 gate: the same row family at the twin-king craft
state (depth 2 — the census bounds recorded below). -/
def dtGateC2 : Bool :=
  dtWfB dtC2 &&
  dtPullsRow dtC2 2 &&
  dtWindowRow dtC2 2 &&
  (dtViolPairCount dtC2 2 == 0) &&
  (dtSameTuplePairCount dtC2 2 ≥ 1) &&
  (dtOrderDiffPairCount dtC2 2 ≥ 1) &&
  (dtDiffTupleDiffMsCount dtC2 2 ≥ 1)

/-! ## The recorded numbers (the gate teeth; observed 2026-10-11 at
this battery) -/

#eval dtWfB dtC1 -- true: the cell is WF (full-deck census-clean)
#eval (dtWalks dtC1 3).length -- 114: the depth-3 census at cell 1
#eval dtPullsRow dtC1 3 -- true: D1, every enumerated state
#eval dtWindowRow dtC1 3 -- true: D2, every walk
#eval dtViolPairCount dtC1 3 -- 0: the candidate determinism violators are ABSENT
#eval dtSameTuplePairCount dtC1 3 -- 3346: same-tuple endpoint pairs exist
#eval dtOrderDiffPairCount dtC1 3 -- 200: order-differing pop lists at one tuple
#eval dtDiffTupleDiffMsCount dtC1 3 -- 9650: different tuples genuinely differ
#eval (dtPullsAt dtC1).length -- 2: the anchor's pops (♠5 onto ♥6, ♥3 onto ♣4)
#eval (dtSlidesAt dtC1).length -- 2: the anchor's relocations (incl. the self-landing swallow)
#eval dtGateC1 -- true: the cell-1 battery

#eval dtWfB dtC2 -- true: the cell is WF
#eval (dtWalks dtC2 2).length -- 272: the depth-2 census at cell 2
#eval dtPullsRow dtC2 2 -- true: D1
#eval dtWindowRow dtC2 2 -- true: D2
#eval dtViolPairCount dtC2 2 -- 0: determinism violators ABSENT at the twin-king cell
#eval dtSameTuplePairCount dtC2 2 -- 46208: same-tuple endpoint pairs exist
#eval dtOrderDiffPairCount dtC2 2 -- 2: the interleaved twin-suit pops (♥Q, ♦J) at one tuple
#eval dtDiffTupleDiffMsCount dtC2 2 -- 27776: different tuples genuinely differ
#eval (dtPullsAt dtC2).length -- 2: ♥Q onto ♠K, ♦J onto the covered king's cover
#eval (dtSlidesAt dtC2).length -- 13: king reseatings (3 kings × free anchors) + run relocations
#eval dtGateC2 -- true: the cell-2 battery
