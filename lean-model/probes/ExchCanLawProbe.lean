import Orig.Canonical
import Orig.TwinExchangeQuotient

/-! # ExchCanLawProbe — landing-1 decide battery for the exchange-canon commutation card

The exchlaw sibling of `orig-comm-canlaw` (FUTURES-ORIG.md §3.0's
exchange-canon backlog, inherited verbatim through the decompress
session's §9 "follow-on exchange-canon card" menu), probed BEFORE any
proof effort, per the house rule.  The card:

* the PINCH `canonQ_of_physOrbit` (physical class-mates — closure of
  reversible shuffle legs + licensed bare twin exchanges — have canon
  images connected in the EXCHANGES-ONLY `ExchOrbit` quotient,
  leg-induction form: refl / shuffle case cites the anchor row,
  exchange case cites `exch_canon_comm`, trans composes);
* the engines: `exch_canon_comm` (licensing at the canon images, the
  swap commuting with saturation — expected honest re-saturated
  grade), torsor freeness (`exch_free`, per-pair locality), the
  coarsening row (`exch_le_sameOrbit`, the forgetful map).

Probe families, each with negative controls, every verdict gated so
`lake env lean probes/ExchCanLawProbe.lean` fails exactly when a
recorded claim fails:

A. exch_canon_comm at the banked wiggle cube (the CanonDecompressProbe
   A1 family mirrored: two independent twin-host residues, the 2^2
   cube) — canon is the identity there, so the commutation square and
   the exchange row read plainly.
B. exch_canon_comm at residue-exhibit cells where saturation FIRES:
   B1 the benign cell (a rung-ready residue the canon lifts off either
   seat — the bit is literally erased by saturation);
   B2 the WORRIED-KING fork cell (a twin pair of rung-ready bare kings,
   one covered by a non-twin residue: the exchange at the pair decides
   WHICH king saturates — the §3.1 grading-note fork, canon-graded),
   the first falsifier candidate.
C. licensing-drift corners — the license census around every cube
   corner and along chains (order-dependence, bit-repeatability), and
   the saturation-kill datum at the fork cell.
D. freeness census — the 3-bit cube (K-, Q-, J-pairs, pairwise
   disjoint seats, riding residues): all eight composite corners
   pairwise distinct, deck-partition evidence; the degenerate
   both-bare bit's identity datum.
E. negative controls — unlicensed pairs (hidden-member,
   waste-resident) never generate legal exchanges; the licensed
   both-bare bit is the identity (the freeness pricing datum).

House discipline: this file is EVIDENCE, not theorems — nothing here
is imported by the library; state-equality verdicts ride a probe-local
DecidableEq bridge (the dedup-marked 14-field shape used by the
witness archives and the sibling probes).
-/

/-! ## Kit -/

/-- The state-equality bridge (probe-local re-derivation of the
dedup-marked 14-field shape; the library's own copy is private in
`Orig/Canonical.lean`). -/
private def exDecSt (s t : State) : Decidable (s = t) :=
  decidable_of_decidable_of_iff (p :=
    (s.found .spade = t.found .spade ∧ s.found .heart = t.found .heart ∧
     s.found .diamond = t.found .diamond ∧ s.found .club = t.found .club ∧
     s.piles .p0 = t.piles .p0 ∧ s.piles .p1 = t.piles .p1 ∧
     s.piles .p2 = t.piles .p2 ∧ s.piles .p3 = t.piles .p3 ∧
     s.piles .p4 = t.piles .p4 ∧ s.piles .p5 = t.piles .p5 ∧
     s.piles .p6 = t.piles .p6 ∧
     s.stock = t.stock ∧ s.waste = t.waste ∧ s.drawStep = t.drawStep))
    (by
      constructor
      · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩
        apply State.ext
        · funext σ; cases σ <;> assumption
        · funext a; cases a <;> assumption
        · assumption
        · assumption
        · assumption
      · rintro rfl
        exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩)

local instance : DecidableEq State := fun s t => exDecSt s t

/-- The WF check, as an evaluable Bool mirror (the dedup-marked
four-conjunct shape; every crafted state partitions the full deck). -/
def exWfB (st : State) : Bool :=
  Suit.all.all (fun s => decide (s.upCards.take (st.found s).length == st.found s)) &&
  Anchor.all.all (fun a => runOK (st.piles a).faceUp) &&
  Card.universe.all (fun c => decide (st.cardCount c == 1)) &&
  decide (0 < st.drawStep)

/-- `TwinExchOK st t` as an evaluable Bool mirror, minus its `WF`
conjunct (checked separately at every deployment). -/
def exOKB (st : State) (t : Card) : Bool :=
  match st.pileHolding t, st.pileHolding t.twin with
  | some a, some a' =>
      decide (a ≠ a') &&
      (decide ((aboveIn t (st.piles a).faceUp) = []) ||
        decide ((aboveIn t.twin (st.piles a').faceUp) = []))
  | _, _ => false

/-- The nondegenerate licensed pair representatives face-up at `st`
(both members of a licensed, state-moving pair are counted; the
degenerate both-bare bit is filtered by the identity test). -/
def exLicensedPairs (st : State) : List Card :=
  (Card.universe.filter fun c => exOKB st c && decide (st.exchangeTwin c ≠ st))

/-- Pairwise-distinctness over a state list. -/
def exAllNe : List State → Bool
  | [] => true
  | s :: t => !(t.any fun s' => decide (s' = s)) && exAllNe t

/-- The stock as the deck minus the excluded cards (seated + founded)
— the mover that keeps every crafted cell's census honest. -/
def exStock (exclude : List Card) : List Card :=
  Card.universe.filter fun c => decide (c ∉ exclude)

/-! ## Family A — the banked wiggle cube (no saturation) -/

/-- The two residues, the four hosts (the CanonDecompressProbe A1
cast mirrored). -/
def exHK : Card := ⟨Suit.heart, Rank.king⟩
def exDK : Card := ⟨Suit.diamond, Rank.king⟩
def exSQ : Card := ⟨Suit.spade, Rank.queen⟩
def exHQ : Card := ⟨Suit.heart, Rank.queen⟩
def exDQ : Card := ⟨Suit.diamond, Rank.queen⟩
def exCJ : Card := ⟨Suit.club, Rank.jack⟩
def exSJ : Card := ⟨Suit.spade, Rank.jack⟩
def exCQ : Card := ⟨Suit.club, Rank.queen⟩
def exHJ : Card := ⟨Suit.heart, Rank.jack⟩
def exDJ : Card := ⟨Suit.diamond, Rank.jack⟩
def exCT : Card := ⟨Suit.club, Rank.ten⟩

/-- The wiggle-cube board (the A1 family): `r1` seats ♠Q on the ♦K
pile, `r2` seats ♣J on the ♦Q pile; the residues sit on the heart
hosts otherwise.  Foundations empty, everything else in stock. -/
def exWig (r1 r2 : Bool) : State where
  found := fun _ => []
  piles := fun a =>
    match a with
    | .p1 => if r1 then ⟨[], [exHK]⟩ else ⟨[], [exHK, exSQ]⟩
    | .p5 => if r1 then ⟨[], [exDK, exSQ]⟩ else ⟨[], [exDK]⟩
    | .p3 => if r2 then ⟨[], [exHQ]⟩ else ⟨[], [exHQ, exCJ]⟩
    | .p4 => if r2 then ⟨[], [exDQ, exCJ]⟩ else ⟨[], [exDQ]⟩
    | _ => ⟨[], []⟩
  stock := exStock [exHK, exDK, exSQ, exHQ, exDQ, exCJ]
  waste := []
  drawStep := 1

def exW00 : State := exWig false false  -- ♠Q@p1, ♣J@p3 (the A1 seating)
def exW10 : State := exWig true false   -- ♠Q@p5, ♣J@p3
def exW01 : State := exWig false true   -- ♠Q@p1, ♣J@p4
def exW11 : State := exWig true true

/-- A gates: all corners WF, canon is the identity (nothing is
rung-ready), the bits are licensed everywhere and write exactly their
own corners, the four corners are pairwise distinct, and the canons of
exchange-mates differ (the wiggle survives canon vacuously — canon
cannot seat residues). -/
def exGateA : Bool :=
  [exW00, exW10, exW01, exW11].all (fun s => exWfB s && decide (canon s = s)) &&
  -- the bits are licensed at every corner, both orientations (pair law)
  [exW00, exW10, exW01, exW11].all (fun s =>
    exOKB s exHK && exOKB s exDK && exOKB s exHQ && exOKB s exDQ) &&
  -- the exchange at the K-pair flips r1 exactly, writing only its own seats
  decide (exW00.exchangeTwin exHK = exW10) &&
  decide (exW10.exchangeTwin exHK = exW00) &&
  decide (exW01.exchangeTwin exHK = exW11) &&
  decide (exW11.exchangeTwin exHK = exW01) &&
  -- the exchange at the Q-pair flips r2 exactly
  decide (exW00.exchangeTwin exHQ = exW01) &&
  decide (exW01.exchangeTwin exHQ = exW00) &&
  decide (exW10.exchangeTwin exHQ = exW11) &&
  decide (exW11.exchangeTwin exHQ = exW10) &&
  -- the per-pair locality datum: the K-bit leaves the Q-pair piles verbatim
  decide ((exW00.exchangeTwin exHK).piles .p3 = exW00.piles .p3) &&
  decide ((exW00.exchangeTwin exHK).piles .p4 = exW00.piles .p4) &&
  -- the freeness census at 2 bits: four corners pairwise distinct
  exAllNe [exW00, exW10, exW01, exW11] &&
  -- order-freeness of the composite (the disjoint-seat diamond)
  decide ((exW00.exchangeTwin exHK).exchangeTwin exHQ = (exW00.exchangeTwin exHQ).exchangeTwin exHK) &&
  -- the wiggle datum: canon does NOT seat residues, so canon images of
  -- exchange-mates differ literally (no saturation to erase the bit)
  decide (canon exW10 ≠ canon exW00)

/-! ## Family B — residue-exhibit cells where saturation fires -/

/-- B1, the benign cell: the K-pair with a RUNG-READY residue ♠Q
(spades climbed A..J), seated over ♥K; the canon lifts the residue off
either seat, then the bit is degenerate both-bare. -/
def exBen : State where
  found := fun s =>
    match s with
    | .spade => Suit.spade.upCards.take 11
    | _ => []
  piles := fun a =>
    match a with
    | .p1 => ⟨[], [exHK, exSQ]⟩
    | .p5 => ⟨[], [exDK]⟩
    | _ => ⟨[], []⟩
  stock := exStock (Suit.spade.upCards.take 11 ++ [exHK, exDK, exSQ])
  waste := []
  drawStep := 1

def exBenX : State := exBen.exchangeTwin exHK

/-- B1 gates: WF both sides, the bit licensed and nondegenerate, and
the LITERAL commutation holds — the saturation literally erases the
bit (the lift takes the residue off either seat, both sides land at
one saturated state), the exchange at the saturated state is the
degenerate both-bare identity, and the license survives saturation as
the degenerate license. -/
def exGateB1 : Bool :=
  exWfB exBen && exWfB exBenX &&
  exOKB exBen exHK && decide (exBenX ≠ exBen) &&
  decide (exBenX.piles .p1 = ⟨[], [exHK]⟩) &&
  decide (exBenX.piles .p5 = ⟨[], [exDK, exSQ]⟩) &&
  -- the swap commutes with saturation, LITERALLY:
  decide (canon exBenX = canon exBen) &&
  decide ((canon exBen).exchangeTwin exHK = canon exBen) &&
  -- the license survives saturation as the degenerate both-bare license
  exOKB (canon exBen) exHK &&
  -- canon erases the bit: the residue is founded, both hosts bare
  decide ((canon exBen).found .spade = Suit.spade.upCards.take 12) &&
  decide ((canon exBen).piles .p1 = ⟨[], [exHK]⟩) &&
  decide ((canon exBen).piles .p5 = ⟨[], [exDK]⟩)

/-- B2, the WORRIED-KING fork cell: hearts and diamonds both climbed
A..Q; ♥K sits BARE on p1 (a rung-ready bare king), its twin ♦K carries
the non-twin residue ♣Q on p5.  The exchange at the K-pair is licensed
(one bare host) and moves ♣Q ONTO ♥K — the saturation then lifts
whichever king the exchange left bare. -/
def exFork : State where
  found := fun s =>
    match s with
    | .heart => Suit.heart.upCards.take 12
    | .diamond => Suit.diamond.upCards.take 12
    | _ => []
  piles := fun a =>
    match a with
    | .p1 => ⟨[], [exHK]⟩
    | .p5 => ⟨[], [exDK, exCQ]⟩
    | _ => ⟨[], []⟩
  stock := exStock (Suit.heart.upCards.take 12 ++ Suit.diamond.upCards.take 12 ++
    [exHK, exDK, exCQ])
  waste := []
  drawStep := 1

def exForkX : State := exFork.exchangeTwin exHK

/-- B2 gates: the fork verdicts.  The exchange is licensed and
nondegenerate at the WF base; the two trajectories canon and
canon ∘ swap SATURATE THE TWO DIFFERENT KINGS (the twin-choice fork of
the §3.1 grading note, met at the canon level): the canon images
differ in FOUNDATION content, so no chain of exchanges (which
preserve the foundations verbatim, `State.exchangeTwin_found`) can
join them — the exchanges-only exchange row of the pinch FAILS here.
The literal square and the re-saturated square both fail; saturation
KILLS the license (the host is founded).  The honest witness at this
cell is the A2-anatomy highway: pull (foundToTab), exchange, pull —
all reversible, the sameOrbit grade lives (canonQ_of_orbit's world). -/
def exGateB2 : Bool :=
  exWfB exFork && exWfB exForkX &&
  -- the bit: licensed, nondegenerate, realizes the residue relocation
  exOKB exFork exHK && decide (exForkX ≠ exFork) &&
  decide (exForkX.piles .p1 = ⟨[], [exHK, exCQ]⟩) &&
  decide (exForkX.piles .p5 = ⟨[], [exDK]⟩) &&
  -- the two wings of the fork: canon lifts the BARE king, side-dependent
  decide ((canon exFork).found .heart = Suit.heart.upCards) &&
  decide ((canon exFork).found .diamond = Suit.diamond.upCards.take 12) &&
  decide ((canon exFork).piles .p1 = ⟨[], []⟩) &&
  decide ((canon exFork).piles .p5 = ⟨[], [exDK, exCQ]⟩) &&
  decide ((canon exForkX).found .diamond = Suit.diamond.upCards) &&
  decide ((canon exForkX).found .heart = Suit.heart.upCards.take 12) &&
  decide ((canon exForkX).piles .p5 = ⟨[], []⟩) &&
  decide ((canon exForkX).piles .p1 = ⟨[], [exHK, exCQ]⟩) &&
  -- THE FOUND SPLIT: no exchange chain joins canon images with
  -- different foundations (exchanges write piles only)
  decide ((canon exFork).found .heart ≠ (canon exForkX).found .heart) &&
  decide (canon exForkX ≠ canon exFork) &&
  -- the literal square DIES: the exchange at canon exFork is the
  -- identity (the host ♥K is FOUNDED — pileHolding fails), while
  -- canon ∘ swap follows the other wing
  decide ((canon exFork).exchangeTwin exHK = canon exFork) &&
  decide ((canon exFork).exchangeTwin exHK ≠ canon exForkX) &&
  -- the re-saturated square DIES with it (the RHS re-saturation is a
  -- no-op: the exchange was the identity)
  decide (canon ((canon exFork).exchangeTwin exHK) = canon exFork) &&
  decide (canon ((canon exFork).exchangeTwin exHK) ≠ canon exForkX) &&
  -- saturation KILLS the license: both canon wings have one host founded
  decide (!exOKB (canon exFork) exHK) &&
  decide (!exOKB (canon exForkX) exHK) &&
  -- the exchange is realized as a plain noreveal slide, both directions
  decide (exFork.step (Move.tabToTab exCQ (Sum.inr exHK)) = some exForkX) &&
  decide (exForkX.step (Move.tabToTab exCQ (Sum.inr exDK)) = some exFork) &&
  -- the honest witness highway (the A2 anatomy): pull, exchange, pull
  decide ((canon exFork).step (Move.foundToTab exHK (Sum.inl Anchor.p1)) = some exFork) &&
  decide ((canon exForkX).step (Move.foundToTab exDK (Sum.inl Anchor.p5)) = some exForkX) &&
  -- canon idempotent everywhere (no wing re-saturates)
  decide (canon (canon exFork) = canon exFork) &&
  decide (canon (canon exForkX) = canon exForkX)

/-! ## Family C — licensing drift -/

/-- C gates: around the 2-bit cube the licenses are stable at every
corner; along chains the composite is order-free and each bit is its
own inverse; at the fork cell the license dies at the canon images
(saturation founds a host). -/
def exGateC : Bool :=
  -- drift-free around the 2^2 cube (part of exGateA, restated for the family)
  [exW00, exW10, exW01, exW11].all (fun s =>
    exOKB s exHK && exOKB s exHQ) &&
  -- bit repeatability: the exchange at a corner is an involution
  decide ((exW10.exchangeTwin exHK) = exW00) &&
  decide (((exW00.exchangeTwin exHK).exchangeTwin exHK) = exW00) &&
  -- the three-step chain: K-bit, then Q-bit, then the K-pair AGAIN
  -- (asked at the twin member ♦K — the pair law along a chain): the
  -- re-executed bit toggles home, so the composite lands at r2-only
  decide (((exW00.exchangeTwin exHK).exchangeTwin exHQ).exchangeTwin exDK =
    exW01) &&
  -- the saturated kill at the fork cell is recorded in exGateB2; the
  -- benign cell keeps the license as degenerate
  exOKB (canon exBen) exHK

/-! ## Family D — the freeness census (three disjoint bits) -/

/-- The 3-bit board: K-pair hosts ♥K@p1/♦K@p5 with residue ♠Q; Q-pair
hosts ♥Q@p3/♦Q@p4 with residue ♣J; J-pair hosts ♥J@p2/♦J@p6 with
residue ♣T.  All three host-pile pairs pairwise disjoint, every
residue twin-legal on either host. -/
def exC3 (r1 r2 r3 : Bool) : State where
  found := fun _ => []
  piles := fun a =>
    match a with
    | .p1 => if r1 then ⟨[], [exHK]⟩ else ⟨[], [exHK, exSQ]⟩
    | .p5 => if r1 then ⟨[], [exDK, exSQ]⟩ else ⟨[], [exDK]⟩
    | .p3 => if r2 then ⟨[], [exHQ]⟩ else ⟨[], [exHQ, exCJ]⟩
    | .p4 => if r2 then ⟨[], [exDQ, exCJ]⟩ else ⟨[], [exDQ]⟩
    | .p2 => if r3 then ⟨[], [exHJ]⟩ else ⟨[], [exHJ, exCT]⟩
    | .p6 => if r3 then ⟨[], [exDJ, exCT]⟩ else ⟨[], [exDJ]⟩
    | _ => ⟨[], []⟩
  stock := exStock [exHK, exDK, exSQ, exHQ, exDQ, exCJ, exHJ, exDJ, exCT]
  waste := []
  drawStep := 1

/-- The subset composite: apply the executed bits in canonical order
(the disjoint-seats abelian datum makes the order immaterial —
gated separately). -/
def exComp (r1 r2 r3 : Bool) : State :=
  let s0 := exC3 false false false
  let s1 := if r1 then s0.exchangeTwin exHK else s0
  let s2 := if r2 then s1.exchangeTwin exHQ else s1
  let s3 := if r3 then s2.exchangeTwin exHJ else s2
  s3

def exCorners : List State :=
  [exComp false false false, exComp true false false, exComp false true false,
   exComp false false true, exComp true true false, exComp true false true,
   exComp false true true, exComp true true true]

/-- D gates: all eight corners WF and canon-fixed; the composites
equal the crafted corners (the bits write exactly their own seats);
all eight pairwise distinct (the 2^3 torsor census); every bit is
licensed at every corner (no licensing drift at disjoint seats); the
composite is order-free. -/
def exGateD : Bool :=
  exCorners.all (fun s => exWfB s && decide (canon s = s)) &&
  exCorners.all (fun s => exOKB s exHK && exOKB s exHQ && exOKB s exHJ) &&
  decide (exComp true false false = exC3 true false false) &&
  decide (exComp false true false = exC3 false true false) &&
  decide (exComp false false true = exC3 false false true) &&
  decide (exComp true true false = exC3 true true false) &&
  decide (exComp true false true = exC3 true false true) &&
  decide (exComp false true true = exC3 false true true) &&
  decide (exComp true true true = exC3 true true true) &&
  exAllNe exCorners &&
  -- the partition-of-the-deck datum: the residue witness cards sit
  -- differently at every corner pair (the census is decided on states)
  exWfB (exC3 false false false) &&
  -- order-freeness on the shared-free composite (2 bits of 3)
  decide (((exC3 false false false).exchangeTwin exHK).exchangeTwin exHQ =
    ((exC3 false false false).exchangeTwin exHQ).exchangeTwin exHK)

/-! ## Family E — negative controls and the degenerate pricing -/

/-- The both-bare degenerate cell: the Q-pair carries its residue, the
K-pair sits BOTH BARE — licensed (the license demands only one bare),
and the exchange is the identity. -/
def exDeg : State where
  found := fun _ => []
  piles := fun a =>
    match a with
    | .p1 => ⟨[], [exHK]⟩
    | .p5 => ⟨[], [exDK]⟩
    | .p3 => ⟨[], [exHQ, exCJ]⟩
    | .p4 => ⟨[], [exDQ]⟩
    | _ => ⟨[], []⟩
  stock := exStock [exHK, exDK, exHQ, exDQ, exCJ]
  waste := []
  drawStep := 1

/-- The waste-resident cell: ♥Q face-up on p1, its twin ♦Q resident in
the WASTE (no pile search ever finds it). -/
def exWaste : State where
  found := fun _ => []
  piles := fun a =>
    match a with
    | .p1 => ⟨[], [exHQ]⟩
    | _ => ⟨[], []⟩
  stock := exStock [exHQ, exDQ]
  waste := [exDQ]
  drawStep := 1

/-- E gates: the degenerate both-bare bit is licensed AND the
identity (the freeness pricing datum — such bits carry no state
information); the hidden-member pair (the residue ♠Q's twin ♣Q is in
the stock) is not licensed and the exchange is the identity; the
waste-resident pair is not licensed and the exchange is the
identity.  No unlicensed shape ever generates a legal step. -/
def exGateE : Bool :=
  exWfB exDeg &&
  exOKB exDeg exHK && decide (exDeg.exchangeTwin exHK = exDeg) &&
  exWfB exWaste &&
  decide (!exOKB exWaste exHQ) && decide (exWaste.exchangeTwin exHQ = exWaste) &&
  -- the hidden-member control at the wiggle cube: ♠Q's twin ♣Q is in
  -- stock, so the pair {♠Q, ♣Q} is not licensed, the exchange shall not fire
  decide (!exOKB exW00 exSQ) && decide (exW00.exchangeTwin exSQ = exW00) &&
  decide (!exOKB exW00 exCJ) && decide (exW00.exchangeTwin exCJ = exW00)

/-! ## The verdicts -/

/-- All gates, as the recorded verdict battery. -/
def exAllGates : Bool :=
  exGateA && exGateB1 && exGateB2 && exGateC && exGateD && exGateE

-- The census data the verdicts pin (printed for the ledger; the
-- gates above carry the load-bearing checks):
#eval (exLicensedPairs (exC3 false false false)).length -- expect 6: three pairs, both orientations
#eval (exLicensedPairs exFork).length                   -- expect 2: the K-pair, both orientations
#eval (exLicensedPairs (canon exFork)).length           -- expect 0: saturation founded the hosts
#eval (exLicensedPairs exW00).length                    -- expect 4: two pairs, both orientations
#eval ((canon exFork).found .heart).length              -- expect 13: the heart wing
#eval ((canon exForkX).found .diamond).length           -- expect 13: the diamond wing
#eval decide (canon exFork = canon exForkX)             -- expect false: the fork split
#eval decide (canon exBen = canon (exBen.exchangeTwin exHK)) -- expect true: the benign erase

#eval! do
  if exAllGates then
    IO.println "EXCHCANLAW: ALL GATES HOLD —"
    IO.println "A: at the wiggle cube canon is the identity; the bits are licensed at every"
    IO.println "   corner, write exactly their own seats, and compose order-freely; the four"
    IO.println "   corners are pairwise distinct; canon images of exchange-mates DIFFER"
    IO.println "   literally (the wiggle survives vacuous saturation — canon seats nothing)."
    IO.println "B1: the benign cell commutes LITERALLY — the saturation erases the bit (the"
    IO.println "   rung-ready residue is lifted off either seat to one saturated state); the"
    IO.println "   exchange at the saturated state is the both-bare identity; the license"
    IO.println "   survives saturation as the degenerate license."
    IO.println "B2: THE FORK — the exchanges-only pin DIES at the worried-king cell: one"
    IO.println "   licensed exchange decides which twin king saturates; the canon images"
    IO.println "   differ in FOUNDATION content (hearts 13 vs diamonds 13), and exchanges"
    IO.println "   preserve founds verbatim, so NO ExchChain joins them. The literal square"
    IO.println "   and the re-saturated square both fail; saturation KILLS the license"
    IO.println "   (canon founds a host). The honest witness is the A2 highway:"
    IO.println "   pull, exchange, pull — the sameOrbit grade lives."
    IO.println "C: no licensing drift around the 2^2 cube; bits are involutions; the chain"
    IO.println "   composite is order-free; saturation kills the license at the fork cell"
    IO.println "   but preserves it as degenerate at the benign cell."
    IO.println "D: the 3-bit census — eight composite corners, all WF, all canon-fixed,"
    IO.println "   pairwise distinct (the 2^3 torsor), every bit licensed at every corner."
    IO.println "E: the both-bare bit is licensed and the IDENTITY (freeness prices it at"
    IO.println "   zero); hidden-member and waste-resident pairs are never licensed and"
    IO.println "   never generate a legal step."
  else
    throw (IO.userError "EXCHCANLAW: A GATE FAILED — see the numbers above")

