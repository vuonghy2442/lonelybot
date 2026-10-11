import Orig.Canonical

/-! # CanonDecompressProbe — landing-1 decide battery for the §3.0 completion card

The canon-side completion of §3.0 (FUTURES-ORIG.md :539-611), probed
BEFORE any proof effort, per the house rule.  The card, with the
mid-flight user refinements folded in:

* (A) DECOMPRESSION REACHABILITY — the reverse of the
  canonicalization theorem: every member of a macro class is
  reachable from a FINAL anchor of the class by a two-letter
  padding (foundToTab pull-downs + noreveal tabToTab slides, every
  tabToFound raise leg the exact undo of a pull-down leg).  The
  per-state reverse is the banked reverse undo-ladder
  (`stackRun_returnW`); the one genuine residue named
  `finalWiggle_reach` (Final-to-Final within one class).
* (B) DRAW-PHASE NORMALIZATION — `canon_draw` as a NAMED
  compositional step over the draw zone; the TARGET presentation is
  decided by these probes, not by fiat (the pinning rule): pristine
  (empty-waste) is licensed only if every pure draw orbit contains a
  pristine member at drawStep 1 AND 3, partial-final-draw corners
  included; otherwise the strongest probe-certified reachable normal
  form becomes the target, the residual recorded honestly.
* (R3) the canon_slide extension (residue seating) and its menu:
  the ONE-LETTER padding target (pure foundToTab pulls from the
  class anchor), the seating-rule confluence/canonicity, the
  slide/saturation disjointness (verify legally, not intuitively),
  negative controls where the slide is not licensed, and the
  two-letter fallback grade.

Probe families, each with negative controls, every verdict gated so
`lake env lean probes/CanonDecompressProbe.lean` exits nonzero exactly
when a recorded claim fails:

A. finalWiggle instances beyond length 1 — composed residue
   relocations and pull-down interleavings at crafted WF Final
   states (A1: two independent twin-host residues, the 2^2 wiggle
   cube; A2: a worry-back BRIDGE pair whose journey needs a
   pulled-down substrate, with the direct slide barred; A3: the
   one-letter negative control at the re-derived residue-reloc
   exhibit).
B. pristine reachability — does every PURE draw orbit contain a
   pristine (empty-waste) member at drawStep 1 AND 3, watching the
   partial-final-draw corners at drawStep 3; and what the strongest
   probe-certified reachable normal form is.
C. purity is saturation-invariant — raises never touch the draw
   zone (`canon` computes; the zone and `inPhase` are checked
   verbatim, pure and offset regimes), plus the literal
   draw/canon commutation squares.
D. negative control — offset zones are NOT normalizable (the
   reversible-draw orbit is a singleton; `draw_irreversible_offset`
   is the boundary).
E. the canon_slide surface — seating-rule confluence at the
   multi-residue cube (E1), occupied-twin-host (E2) and
   revealing-slide (E3) negative controls, the
   slide-exposes-a-licensed-raise interaction (E4), and the
   same-pair transposition deadlock (E5).

House discipline: this file is EVIDENCE, not theorems — nothing here
is imported by the library; state-equality verdicts ride a probe-local
DecidableEq bridge (the dedup-marked 14-field shape used by the
witness archives).
-/

/-! ## Kit -/

/-- The state-equality bridge (probe-local re-derivation of the
dedup-marked 14-field shape; the library's own copy is private in
`Orig/Canonical.lean`). -/
private def cdDecSt (s t : State) : Decidable (s = t) :=
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

local instance : DecidableEq State := fun s t => cdDecSt s t

/-- The WF check, as an evaluable Bool mirror of the four conjuncts
(the foundation conjunct decided through the prefix length).  Every
crafted state below partitions the full 52-card deck, so the census
conjunct is live. -/
def cdWfB (st : State) : Bool :=
  Suit.all.all (fun s => decide (s.upCards.take (st.found s).length == st.found s)) &&
  Anchor.all.all (fun a => runOK (st.piles a).faceUp) &&
  Card.universe.all (fun c => decide (st.cardCount c == 1)) &&
  decide (0 < st.drawStep)

/-- `Final`, as the probe reads it: no licensed lift remains. -/
def cdFinalB (st : State) : Bool := (pick st).isNone

/-- The card-bearing board zones read (piles face-up ++ foundations). -/
def cdBoardCards (st : State) : List Card :=
  (Anchor.all.flatMap fun a => (st.piles a).faceUp) ++ Suit.all.flatMap st.found

/-- The one-draw successor of `st` (identity when the draw does not fire). -/
def cdDrawn (st : State) : State :=
  match st.step Move.draw with
  | some s => s
  | none => st

/-- Enumerate every `foundToTab c b` move that fires at `st`
(c over the universe, b over the seven anchors and every card). -/
def cdPullFires (st : State) : List Move :=
  let bases : List Base := (Anchor.all.map Sum.inl) ++ (Card.universe.map Sum.inr)
  Card.universe.flatMap (fun c =>
    (bases.filter (fun b => (st.step (Move.foundToTab c b)).isSome)).map
      (fun b => Move.foundToTab c b))

/-- Enumerate every `tabToTab c b` move that fires at `st`
(c over the board cards, b over the seven anchors and every card). -/
def cdSlideFires (st : State) : List Move :=
  let bases : List Base := (Anchor.all.map Sum.inl) ++ (Card.universe.map Sum.inr)
  (cdBoardCards st).flatMap (fun c =>
    (bases.filter (fun b => (st.step (Move.tabToTab c b)).isSome)).map
      (fun b => Move.tabToTab c b))

/-! ## The zone model

Draws read and write only `(stock, waste, drawStep)`; the
reversibility classification of a draw is decided by the zone alone
(the banked rows: `draw_irreversibility_class` for stock-bearing
zones, `draw_passBase_reversibleW`/`draw_reversible_selfRecycleW` at
the pass base, `draw_irreversible_pristine` for the pristine exit);
board moves never touch the zone (`putCard_keep`/`putRun_keep`/the
setFound readers).  So the draw orbit of a zone can be enumerated at
the presentation level.
-/

/-- A zone presentation: stock (draw order), waste (top at head),
draw step. -/
abbrev CdZone : Type := List Card × List Card × Nat

/-- `State.recycle` on zones. -/
def CdZone.recycle : CdZone → CdZone
  | ([], w, d) => (w.reverse, [], d)
  | z => z

/-- `State.dealStock` on zones. -/
def CdZone.deal : CdZone → Option CdZone
  | ([], _, _) => none
  | (s, w, d) => some ((State.dealUpTo d s).2, (State.dealUpTo d s).1.reverse ++ w, d)

/-- The draw on zones (recycle, then deal — mirroring `stepDraw`). -/
def CdZone.draw (z : CdZone) : Option CdZone := z.recycle.deal

/-- The conserved pool of a zone (`Canonical.drawPool`). -/
def CdZone.pool (z : CdZone) : List Card := z.1.reverse ++ z.2.1

/-- Is the draw at this presentation reversible, per the banked
classification rows?  (Pass base: always reversible; stock-bearing
and in-phase with a nonempty waste: reversible; pristine or offset:
a commitment; the both-empty zone has no draw at all.) -/
def CdZone.revDraw (z : CdZone) : Bool :=
  match z with
  | (_, [], _) => false
  | ([], _, _) => true
  | (_, w, d) => decide (w.length % d == 0)

/-- Does the presentation lie on the phase line? -/
def CdZone.inPhaseB (z : CdZone) : Bool :=
  match z.1 with
  | [] => true
  | _ => decide (z.2.1.length % z.2.2 == 0)

/-- The reversible draw edge leaving `z` (empty when the draw does
not fire, or fires as a commitment). -/
def CdZone.revStep (z : CdZone) : List CdZone :=
  match z.draw with
  | none => []
  | some z' => if z.revDraw then [z'] else []

def cdDedup (l : List CdZone) : List CdZone :=
  l.foldl (fun acc z => if acc.contains z then acc else z :: acc) []

/-- One BFS round over reversible draw edges. -/
def cdExpand (vs : List CdZone) : List CdZone :=
  cdDedup ((vs.flatMap CdZone.revStep) ++ vs)

/-- The fixed-point closure with generous fuel (zones are small:
the reachable presentations are bounded by the pool's split
positions; 300 rounds is several times any closure here). -/
def cdOrbit (z : CdZone) : List CdZone :=
  let rec go : Nat → List CdZone → List CdZone
    | 0, vs => cdExpand vs
    | n+1, vs =>
        let vs' := cdExpand vs
        if vs'.length == vs.length then vs' else go n vs'
  go 300 [z]

/-- Does the orbit contain a pristine (empty-waste) member? -/
def cdOrbitPristine (z : CdZone) : Bool :=
  (cdOrbit z).any (fun z' => z'.2.1 == [])

/-- The pass-base (empty-stock) members of the orbit. -/
def cdOrbitPass (z : CdZone) : List CdZone :=
  (cdOrbit z).filter (fun z' => z'.1 == [])

/-- The expected normal form of a pure non-pristine zone: the PASS
BASE — the drained presentation `([], P, d)`: the pool is conserved
verbatim by every draw, and at the empty stock the waste IS the
pool. -/
def cdNormZone (P : List Card) (d : Nat) : CdZone := ([], P, d)

/-- Build the pure zone with `m` stock-head cards: the stock is the
first `m` cards of the pool, reversed; the waste is the rest.  (The
deals pop the pool's head; the waste grows from the pool's tail, so
`S = (P.take m).reverse` and `W = P.drop m`.  Sanity: pristine is
`m = |P|`, the pass base is `m = 0`.) -/
def cdMk (P : List Card) (m d : Nat) : CdZone :=
  ((P.take m).reverse, P.drop m, d)

/-- The pool-conservation sanity of a crafted zone. -/
def cdMkOk (m d : Nat) (P : List Card) : Bool :=
  (cdMk P m d).pool == P

/-! ## Family A1 — the double-residue wiggle cube (length-2 finalWiggle)

Two independent residues, each free between its twin-host pair:
♠Q between the red kings (p1 = ♥K, p5 = ♦K), ♣J between the red
queens (p3 = ♥Q, p4 = ♦Q).  Foundations empty, everything else in
stock; every configuration is WF and Final; the 2^2 cube is joined
by noreveal tabToTab slides, one move per relocated residue.
-/

def cdHK : Card := ⟨Suit.heart, Rank.king⟩
def cdDK : Card := ⟨Suit.diamond, Rank.king⟩
def cdSQ : Card := ⟨Suit.spade, Rank.queen⟩
def cdHQ : Card := ⟨Suit.heart, Rank.queen⟩
def cdDQ : Card := ⟨Suit.diamond, Rank.queen⟩
def cdCJ : Card := ⟨Suit.club, Rank.jack⟩

/-- The cube configuration board: `r1p5` seats ♠Q on ♦K's pile,
`r2p4` seats ♣J on ♦Q's pile; the residues sit on the heart hosts
otherwise. -/
def cdCube (r1p5 r2p4 : Bool) : State where
  found := fun _ => []
  piles := fun a =>
    match a with
    | .p1 => if r1p5 then ⟨[], [cdHK]⟩ else ⟨[], [cdHK, cdSQ]⟩
    | .p5 => if r1p5 then ⟨[], [cdDK, cdSQ]⟩ else ⟨[], [cdDK]⟩
    | .p3 => if r2p4 then ⟨[], [cdHQ]⟩ else ⟨[], [cdHQ, cdCJ]⟩
    | .p4 => if r2p4 then ⟨[], [cdDQ, cdCJ]⟩ else ⟨[], [cdDQ]⟩
    | _ => ⟨[], []⟩
  stock := Card.universe.filter fun c =>
    decide (c ≠ cdHK ∧ c ≠ cdDK ∧ c ≠ cdSQ ∧ c ≠ cdHQ ∧ c ≠ cdDQ ∧ c ≠ cdCJ)
  waste := []
  drawStep := 1

def cdC00 : State := cdCube false false  -- ♠Q@p1, ♣J@p3 (the canonical seating)
def cdC10 : State := cdCube true false   -- ♠Q@p5, ♣J@p3
def cdC01 : State := cdCube false true   -- ♠Q@p1, ♣J@p4
def cdC11 : State := cdCube true true    -- ♠Q@p5, ♣J@p4

def cdSlideQ : Move := Move.tabToTab cdSQ (Sum.inr cdDK)
def cdSlideQBack : Move := Move.tabToTab cdSQ (Sum.inr cdHK)
def cdSlideJ : Move := Move.tabToTab cdCJ (Sum.inr cdDQ)
def cdSlideJBack : Move := Move.tabToTab cdCJ (Sum.inr cdHQ)

/-- A1 gates: the cube's four corners are WF + Final, pairwise
distinct, joined by noreveal slides both ways, and the length-2
finalWiggle reaches the far corner in either leg order. -/
def cdGateA1 : Bool :=
  [cdC00, cdC10, cdC01, cdC11].all (fun s => cdWfB s && cdFinalB s) &&
  decide (cdC00 ≠ cdC10 && cdC00 ≠ cdC01 && cdC00 ≠ cdC11 && cdC10 ≠ cdC01
    && cdC10 ≠ cdC11 && cdC01 ≠ cdC11) &&
  -- the single-slide cube edges, both directions
  decide ((cdC00.run [cdSlideQ]).any (fun w => w == cdC10)) &&
  decide ((cdC10.run [cdSlideQBack]).any (fun w => w == cdC00)) &&
  decide ((cdC00.run [cdSlideJ]).any (fun w => w == cdC01)) &&
  decide ((cdC01.run [cdSlideJBack]).any (fun w => w == cdC00)) &&
  -- THE LENGTH-2 finalWiggle: both slide orders reach the far corner
  decide ((cdC00.run [cdSlideQ, cdSlideJ]).any (fun w => w == cdC11)) &&
  decide ((cdC00.run [cdSlideJ, cdSlideQ]).any (fun w => w == cdC11)) &&
  decide ((cdC11.run [cdSlideQBack, cdSlideJBack]).any (fun w => w == cdC00)) &&
  decide ((cdC11.run [cdSlideJBack, cdSlideQBack]).any (fun w => w == cdC00))

/-! ## Family A2 — the worry-back BRIDGE pair (pull-down interleaving)

The residue ♠J sits on its (tableau) host ♦Q at p2; its twin host
♥Q is IN THE FOUNDATION (hearts climbed A..Q).  The king-topped p6
is the landing site.  The wiggle-mate v: ♥Q pulled down onto ♠K (a
foundToTab leg), ♠J slid across onto the pulled substrate (a
noreveal tabToTab leg).  The direct slide is barred (♥Q is not on
the tableau); the return journey performs the pull's exact undo
(raise ♥Q) AFTER unburying it — the residence calculus's
pile↔foundation pair, reordered.  Both endpoints WF + Final.
-/

def cdSJ : Card := ⟨Suit.spade, Rank.jack⟩
def cdSK : Card := ⟨Suit.spade, Rank.king⟩

/-- u: residue ♠J on ♦Q; ♥Q founded (A..Q, top ♥Q); the king
landing site holds nothing that fits ♠J. -/
def cdBrU : State where
  found := fun s =>
    match s with
    | .heart => Suit.heart.upCards.take 12  -- ♥A..♥Q (top = ♥Q)
    | _ => []
  piles := fun a =>
    match a with
    | .p2 => ⟨[], [cdDQ, cdSJ]⟩
    | .p6 => ⟨[], [cdSK]⟩
    | _ => ⟨[], []⟩
  stock := Card.universe.filter fun c =>
    decide (c ≠ cdSJ ∧ c ≠ cdSK ∧ c ≠ cdDQ ∧ c ∉ Suit.heart.upCards.take 12)
  waste := []
  drawStep := 1

/-- The pull leg (popped substrate onto the king site). -/
def cdPullQ : Move := Move.foundToTab cdHQ (Sum.inr cdSK)
/-- The slide leg (residue onto the pulled substrate). -/
def cdBridgeSlide : Move := Move.tabToTab cdSJ (Sum.inr cdHQ)
/-- The unslide leg. -/
def cdUnSlide : Move := Move.tabToTab cdSJ (Sum.inr cdDQ)
/-- The raise-back leg (the pull's exact undo, after unburying). -/
def cdRaiseQ : Move := Move.tabToFound cdHQ

def cdBrV : State := (cdBrU.run [cdPullQ, cdBridgeSlide]).getD cdBrU

def cdGateA2 : Bool :=
  cdWfB cdBrU && cdFinalB cdBrU &&
  cdWfB cdBrV && cdFinalB cdBrV &&
  -- the journey lands the mate, genuinely different, in the crafted shape
  decide ((cdBrU.run [cdPullQ, cdBridgeSlide]).any (fun w => w == cdBrV)) &&
  decide (cdBrV ≠ cdBrU) &&
  decide ((cdBrV.piles .p2).faceUp == [cdDQ]) &&
  decide ((cdBrV.piles .p6).faceUp == [cdSK, cdHQ, cdSJ]) &&
  -- the return journey: unslide, then the pull's exact undo
  decide ((cdBrV.run [cdUnSlide, cdRaiseQ]).any (fun w => w == cdBrU)) &&
  -- NEGATIVE CONTROL: the direct slide is barred (♥Q is not tableau)
  decide ((cdBrU.pileOfTop cdHQ).isNone) &&
  decide ((cdBrU.step (Move.tabToTab cdSJ (Sum.inr cdHQ))).isNone) &&
  -- the zone is untouched by the whole wiggle (SWComp trivially)
  decide (cdBrV.stock == cdBrU.stock && cdBrV.waste == cdBrU.waste
    && cdBrV.drawStep == cdBrU.drawStep)

/-! ## Family A3 — the one-letter negative control (re-derived exhibit)

The residue-reloc exhibit re-crafted here (the library's copy is
private evidence in Orig/Canonical.lean): ♠3 between the twin hosts
♥4 (p1) / ♦4 (p5), foundations empty.  Pure foundToTab sits: NONE
fire anywhere (no foundation top exists, so no pull-down can even
start); the pure-pull reachable set from the anchor is the anchor
alone; the wiggle-mate is a same-orbit state.  VERDICT: the
ONE-LETTER class-anchor form (every member reachable from the class
canon by PURE pulls) is refuted at the banked exhibit — the
two-letter grade stands.
-/

def cdRSH4 : Card := ⟨Suit.heart, Rank.four⟩
def cdRSD4 : Card := ⟨Suit.diamond, Rank.four⟩
def cdRSS3 : Card := ⟨Suit.spade, Rank.three⟩

def cdExU : State where
  found := fun _ => []
  piles := fun a =>
    match a with
    | .p1 => ⟨[], [cdRSH4, cdRSS3]⟩
    | .p5 => ⟨[], [cdRSD4]⟩
    | _ => ⟨[], []⟩
  stock := Card.universe.filter fun c =>
    decide (c ≠ cdRSS3 ∧ c ≠ cdRSH4 ∧ c ≠ cdRSD4)
  waste := []
  drawStep := 1

def cdExV : State :=
  (cdExU.run [Move.tabToTab cdRSS3 (Sum.inr cdRSD4)]).getD cdExU

def cdGateA3 : Bool :=
  cdWfB cdExU && cdWfB cdExV && cdFinalB cdExU && cdFinalB cdExV &&
  -- the exhibit round trip is live (the class-mate fact)
  decide ((cdExU.run [Move.tabToTab cdRSS3 (Sum.inr cdRSD4)]).any (fun w => w == cdExV)) &&
  decide ((cdExV.run [Move.tabToTab cdRSS3 (Sum.inr cdRSH4)]).any (fun w => w == cdExU)) &&
  decide (cdExU ≠ cdExV) &&
  -- THE ONE-LETTER REFUTATION datum: no pull fires at the anchor at all
  (cdPullFires cdExU).isEmpty

/-! ## Family B — pristine reachability and the normal form

Zone-only enumeration (draws read/write only the zone; the
classification is presentation-decidable).  Pools: drawn from the
universe head.  `cdMk P m d` is the presentation with `m` stock-head
cards; in-phase demands |W| = |P| - m ≡ 0 (mod d).
-/

def cdP7 : List Card := Card.universe.take 7    -- 7 % 3 = 1 (partial-final corner)
def cdP9 : List Card := Card.universe.take 9    -- clean multiple of 3
def cdP10 : List Card := Card.universe.take 10  -- 10 % 3 = 1 (partial-final corner)
def cdP11 : List Card := Card.universe.take 11  -- 11 % 3 = 2 (the other corner)

/-- Pristine is unreachable from every PURE non-pristine orbit (at
drawStep 1 AND 3, partial-final-draw corners included); the pass
base `([], P, d)` is the UNIQUE empty-stock member of every pure
non-pristine orbit — the strongest probe-certified reachable normal
form. -/
def cdGateB : Bool :=
  cdMkOk 9 1 cdP10 && cdMkOk 3 3 cdP9 && cdMkOk 1 3 cdP7 && cdMkOk 4 3 cdP10
    && cdMkOk 5 3 cdP11 && cdMkOk 0 3 cdP9 &&
  -- d = 1: the whole split family rotates; pristine NEVER; unique pass base
  (let z := cdMk cdP10 9 1
   cdOrbitPristine z == false &&
   (cdOrbitPass z).length == 1 &&
   (cdOrbitPass z).any (fun z' => z' == cdNormZone cdP10 1)) &&
  -- d = 1: the pristine start is a singleton orbit (draws out commit)
  (let z := cdMk cdP10 10 1
   (cdOrbit z).length == 1) &&
  -- d = 3, clean pool 9 (m = 3 in-phase): drains to the unique pass base
  (let z := cdMk cdP9 3 3
   cdOrbitPristine z == false &&
   (cdOrbitPass z).length == 1 &&
   (cdOrbitPass z).any (fun z' => z' == cdNormZone cdP9 3)) &&
  -- d = 3, pool 7, the boundary-deal corner from m = 1 (|W| = 6)
  (let z := cdMk cdP7 1 3
   cdOrbitPristine z == false &&
   (cdOrbitPass z).length == 1 &&
   (cdOrbitPass z).any (fun z' => z' == cdNormZone cdP7 3)) &&
  -- d = 3, pool 7, m = 4 (|W| = 3): the stock-remainder r = 1 corner
  (let z := cdMk cdP7 4 3
   cdOrbitPristine z == false &&
   (cdOrbitPass z).length == 1) &&
  -- d = 3, pool 10, m = 4 (|W| = 6): partial corner r = 1
  (let z := cdMk cdP10 4 3
   cdOrbitPristine z == false &&
   (cdOrbitPass z).length == 1 &&
   (cdOrbitPass z).any (fun z' => z' == cdNormZone cdP10 3)) &&
  -- d = 3, pool 11, m = 5 (|W| = 6): partial corner r = 2
  (let z := cdMk cdP11 5 3
   cdOrbitPristine z == false &&
   (cdOrbitPass z).length == 1) &&
  -- pass-base start (d = 3): rotates out and drains back; pristine NEVER
  (let z := cdNormZone cdP9 3
   cdOrbitPristine z == false &&
   (cdOrbitPass z).length == 1) &&
  -- pristine starts at d = 3 and d = 1: singleton orbits
  ((cdOrbit (cdMk cdP9 9 3)).length == 1) &&
  ((cdOrbit (cdMk cdP9 9 1)).length == 1) &&
  -- the both-empty corner: no draw at all
  ((CdZone.draw ([], [], 3)).isNone)

/-! ## Family C — purity is saturation-invariant; the commutation squares

`canon` computes (canonAux 53 — 52 lifts always suffice).  Gates:
the saturator preserves the whole zone verbatim and the phase line
on pure, offset, and pristine zones; the draw/canon square holds
LITERALLY at every zone shape (the draw is a field-local function
reading and writing only the zone; the saturator reads and writes
only found/piles — the master disjointness shard, here at the
committed commutation instance); the license is zone-blind (pick
survives a draw).
-/

def cdS2 : Card := ⟨Suit.spade, Rank.two⟩
def cdHA : Card := ⟨Suit.heart, Rank.ace⟩

/-- The C-boards' waste pool — three (and two) spades disjoint from
the board cards, so the census stays live. -/
def cdCWaste : List Card :=
  [⟨Suit.spade, Rank.five⟩, ⟨Suit.spade, Rank.six⟩, ⟨Suit.spade, Rank.seven⟩]

/-- A pure-zone state with a licensed raise: ♥A under-seat on ♠2 at
p2; the zone in-phase at d = 3. -/
def cdSatU : State where
  found := fun _ => []
  piles := fun a =>
    match a with
    | .p2 => ⟨[], [cdS2, cdHA]⟩
    | _ => ⟨[], []⟩
  stock := Card.universe.filter fun c =>
    decide (c ≠ cdS2 ∧ c ≠ cdHA ∧ c ∉ cdCWaste)
  waste := cdCWaste
  drawStep := 3

/-- The same board at an offset zone (|W| = 2 at d = 3): the
canonicalizer must not "fix" the zone. -/
def cdSatOff : State where
  found := fun _ => []
  piles := fun a =>
    match a with
    | .p2 => ⟨[], [cdS2, cdHA]⟩
    | _ => ⟨[], []⟩
  stock := Card.universe.filter fun c =>
    decide (c ≠ cdS2 ∧ c ≠ cdHA ∧ c ∉ (cdCWaste.take 2))
  waste := cdCWaste.take 2
  drawStep := 3

/-- The same board at a pristine zone: the presentation the (B)
probes leave un-normalizable. -/
def cdSatPristine : State where
  found := fun _ => []
  piles := fun a =>
    match a with
    | .p2 => ⟨[], [cdS2, cdHA]⟩
    | _ => ⟨[], []⟩
  stock := Card.universe.filter fun c =>
    decide (c ≠ cdS2 ∧ c ≠ cdHA)
  waste := []
  drawStep := 3

/-- The LITERAL draw/canon square at one state (the draw fires
under all three regimes; identities otherwise). -/
def cdCommOK (st : State) : Bool :=
  decide (canon (cdDrawn st) == cdDrawn (canon st))

def cdGateC : Bool :=
  cdWfB cdSatU && cdWfB cdSatOff && cdWfB cdSatPristine &&
  cdFinalB (canon cdSatU) &&
  -- purity is saturation-invariant: zone verbatim, phase line too
  decide ((canon cdSatU).stock == cdSatU.stock &&
    (canon cdSatU).waste == cdSatU.waste &&
    (canon cdSatU).drawStep == cdSatU.drawStep) &&
  decide (inPhase (canon cdSatU) == inPhase cdSatU) &&
  -- and on the offset zone: the offset stays, phase line stays
  decide ((canon cdSatOff).stock == cdSatOff.stock &&
    (canon cdSatOff).waste == cdSatOff.waste &&
    (canon cdSatOff).drawStep == cdSatOff.drawStep) &&
  decide (inPhase (canon cdSatOff) == inPhase cdSatOff) &&
  -- and on the pristine zone
  decide ((canon cdSatPristine).stock == cdSatPristine.stock &&
    (canon cdSatPristine).waste == cdSatPristine.waste &&
    (canon cdSatPristine).drawStep == cdSatPristine.drawStep) &&
  -- the three saturated forms differ only in the zone: boards equal
  Suit.all.all (fun s => decide ((canon cdSatU).found s == (canon cdSatOff).found s
    && (canon cdSatU).found s == (canon cdSatPristine).found s)) &&
  Anchor.all.all (fun a => decide ((canon cdSatU).piles a == (canon cdSatOff).piles a
    && (canon cdSatU).piles a == (canon cdSatPristine).piles a)) &&
  -- the saturation consumed the licensed raise
  decide ((canon cdSatU).found .heart == [cdHA]) &&
  -- the LITERAL commutation squares, one per zone shape
  cdCommOK cdSatU && cdCommOK cdSatOff && cdCommOK cdSatPristine &&
  -- the license is zone-blind: pick survives the draw
  decide (pick (cdDrawn cdSatU) == pick cdSatU) &&
  decide (pick (cdDrawn cdSatOff) == pick cdSatOff)

/-! ## Family D — the offset negative control

Offset zones (stock present, waste strictly inside a deal) have no
reversible draw edge at all: `draw_irreversible_offset` is the
boundary, and the first offset draw commits.  Pristine zones
likewise (draw_irreversible_pristine).  Nothing normalizes them.
-/

def cdGateD : Bool :=
  -- offset at d = 3, waste 2
  (let z : CdZone := (cdP11.take 9, cdP11.drop 9, 3)
   z.revDraw == false && CdZone.revStep z == []) &&
  -- offset at d = 3, waste 8 (a bigger interior)
  (let z : CdZone := (cdP10.take 4, (cdP10.drop 4) ++ (cdP10.take 4), 3)
   z.revDraw == false && CdZone.revStep z == []) &&
  -- pristine zones: the first draw commits
  (CdZone.revDraw (cdP9, [], 3) == false) &&
  (CdZone.revDraw (cdP9, [], 1) == false)

/-! ## Family E — the canon_slide surface

Card and rule probes for the residue-seating pass: E1 the seating
CONFLUENCE evidence at the cube (every corner reaches the canonical
seating by at most two slides, either leg order); E2 the
occupied-twin-host negative; E3 the revealing-slide negative; E4
the slide-exposes-a-licensed-raise interaction (disjointness of the
slide pass from `Final` is FALSE — legal evidence, not intuition);
E5 the same-pair transposition deadlock (the residue-pairing is
class data: at pull-free boards the transposed configurations and
the canonical seating itself are slide-frozen).
-/

def cdQQ : Card := ⟨Suit.club, Rank.queen⟩

/-- E2 (negative): the twin host is occupied by an unfit top (♣Q on
♦K at p5): the residue ♠Q cannot slide there. -/
def cdOccU : State where
  found := fun _ => []
  piles := fun a =>
    match a with
    | .p1 => ⟨[], [cdHK, cdSQ]⟩
    | .p5 => ⟨[], [cdDK, cdQQ]⟩
    | _ => ⟨[], []⟩
  stock := Card.universe.filter fun c =>
    decide (c ≠ cdHK ∧ c ≠ cdDK ∧ c ≠ cdSQ ∧ c ≠ cdQQ)
  waste := []
  drawStep := 1

/-- E3 (negative): the revealing slide — the residue is the whole
face-up run over a nonempty hidden deck; the slide legally fires
but drops `hiddenTotal` (a commitment, barred from the canon_slide
license by the measure rows). -/
def cdRevU : State where
  found := fun _ => []
  piles := fun a =>
    match a with
    | .p1 => ⟨[cdQQ], [cdSQ]⟩
    | .p5 => ⟨[], [cdDK]⟩
    | _ => ⟨[], []⟩
  stock := Card.universe.filter fun c =>
    decide (c ≠ cdSQ ∧ c ≠ cdDK ∧ c ≠ cdQQ)
  waste := []
  drawStep := 1

/-- E4 (interaction): sliding the residue off its host EXPOSES a
licensed raise underneath — the slide pass and `Final` are not
disjoint; any canon_slide must re-saturate (and the exposure can
change the residue geometry). -/
def cdExpU : State where
  found := fun s =>
    match s with
    | .spade => [⟨Suit.spade, Rank.ace⟩, ⟨Suit.spade, Rank.two⟩,
                 ⟨Suit.spade, Rank.three⟩, ⟨Suit.spade, Rank.four⟩]
    | _ => []
  piles := fun a =>
    match a with
    | .p1 => ⟨[], [⟨Suit.heart, Rank.six⟩, ⟨Suit.spade, Rank.five⟩,
                   ⟨Suit.heart, Rank.four⟩]⟩
    | .p4 => ⟨[], [⟨Suit.club, Rank.five⟩]⟩
    | _ => ⟨[], []⟩
  stock := Card.universe.filter fun c =>
    decide (c ∉ [⟨Suit.heart, Rank.six⟩, ⟨Suit.spade, Rank.five⟩,
      ⟨Suit.heart, Rank.four⟩, ⟨Suit.club, Rank.five⟩, ⟨Suit.spade, Rank.ace⟩,
      ⟨Suit.spade, Rank.two⟩, ⟨Suit.spade, Rank.three⟩, ⟨Suit.spade, Rank.four⟩])
  waste := []
  drawStep := 1

def cdExpSlide : Move :=
  Move.tabToTab ⟨Suit.heart, Rank.four⟩ (Sum.inr ⟨Suit.club, Rank.five⟩)

/-- E5 (deadlock): two residues over one twin-host pair — ♠Q and ♣Q
both fit both red kings.  The RESIDUE-QUEENS have no legal
relocation move at either seating (empty anchors take kings only;
the only card-tops are the other queen), and no bounded composition
of slides reaches the transposed seating: the kings may relocate
to empty anchors, but a king carries its rider whole (`fromCard`
moves the run), so the residue-to-host PAIRING is class data, not
something a seating rule chooses.
-/
def cdPairBoard (swapped : Bool) : State where
  found := fun _ => []
  piles := fun a =>
    match a with
    | .p1 => ⟨[], [cdHK, if swapped then cdQQ else cdSQ]⟩
    | .p5 => ⟨[], [cdDK, if swapped then cdSQ else cdQQ]⟩
    | _ => ⟨[], []⟩
  stock := Card.universe.filter fun c =>
    decide (c ≠ cdHK ∧ c ≠ cdDK ∧ c ≠ cdSQ ∧ c ≠ cdQQ)
  waste := []
  drawStep := 1

def cdPairA : State := cdPairBoard false  -- {♠Q@p1, ♣Q@p5}
def cdPairB : State := cdPairBoard true   -- {♣Q@p1, ♠Q@p5}: the transposition

/-- The slide moves that move a RESIDUE (not its host): tabToTab of
the queens themselves. -/
def cdResidueSlideFires (st : State) (cs : List Card) : List Move :=
  let bases : List Base := (Anchor.all.map Sum.inl) ++ (Card.universe.map Sum.inr)
  cs.flatMap (fun c =>
    (bases.filter (fun b => (st.step (Move.tabToTab c b)).isSome)).map
      (fun b => Move.tabToTab c b))

def cdDedupSt (l : List State) : List State :=
  l.foldl (fun acc s => if acc.contains s then acc else s :: acc) []

/-- Bounded slide-closure: all states reachable from `st` by at
most `n` consecutive legal tabToTab moves (pulls add nothing at
these boards — no foundation holds a card). -/
def cdSlideClosure (n : Nat) (st : State) : List State :=
  let rec go : Nat → List State → List State
    | 0, acc => acc
    | k+1, acc =>
        let next := (acc.flatMap (fun s =>
          (cdSlideFires s).flatMap (fun m =>
            match s.step m with
            | none => []
            | some s' => [s'])))
        go k (cdDedupSt (next ++ acc))
  go n [st]

def cdGateE : Bool :=
  -- E1: seating confluence at the cube — every corner reaches the
  -- canonical seating ♠Q@p1, ♣J@p3 by at most two slides, either order
  decide ((cdC10.run [cdSlideQBack]).any (fun w => w == cdC00)) &&
  decide ((cdC01.run [cdSlideJBack]).any (fun w => w == cdC00)) &&
  decide ((cdC11.run [cdSlideQBack, cdSlideJBack]).any (fun w => w == cdC00)) &&
  decide ((cdC11.run [cdSlideJBack, cdSlideQBack]).any (fun w => w == cdC00)) &&
  cdWfB cdC00 && cdFinalB cdC00 &&
  -- E2 (negative): the occupied twin host bars the slide
  cdWfB cdOccU && cdFinalB cdOccU &&
  decide ((cdOccU.step (Move.tabToTab cdSQ (Sum.inr cdQQ))).isNone) &&
  -- E3 (negative): the revealing slide fires but drops the hidden total
  cdWfB cdRevU && cdFinalB cdRevU &&
  (let v := (cdRevU.step (Move.tabToTab cdSQ (Sum.inr cdDK))).getD cdRevU
   decide (hiddenTotal v < hiddenTotal cdRevU)) &&
  -- E4 (interaction): the slide exposes a LICENSED raise underneath
  cdWfB cdExpU && cdFinalB cdExpU &&
  (let v := (cdExpU.step cdExpSlide).getD cdExpU
   decide (canRaiseB cdExpU ⟨Suit.spade, Rank.five⟩ == false) &&
   decide (canRaiseB v ⟨Suit.spade, Rank.five⟩ == true) &&
   cdFinalB v == false) &&
  -- E5 (the pairing datum): the residue-queens have no slide move at
  -- either seating, no pull fires, and the bounded slide-closure
  -- (four moves deep) does not contain the transposition, in either
  -- direction — the kings relocate (carrying their riders), the
  -- residue-to-host pairing cannot be permuted
  cdWfB cdPairA && cdWfB cdPairB && cdFinalB cdPairA && cdFinalB cdPairB &&
  (cdPullFires cdPairA).isEmpty &&
  (cdPullFires cdPairB).isEmpty &&
  (cdResidueSlideFires cdPairA [cdSQ, cdQQ]).isEmpty &&
  (cdResidueSlideFires cdPairB [cdSQ, cdQQ]).isEmpty &&
  decide (!((cdSlideClosure 4 cdPairA).contains cdPairB)) &&
  decide (!((cdSlideClosure 4 cdPairB).contains cdPairA)) &&
  -- and every state in the bounded closure keeps the co-location
  -- (each queen rides its own king pile or its relocation)
  ((cdSlideClosure 4 cdPairA).all (fun s =>
    (s.pileHolding cdSQ).isSome && (s.pileHolding cdQQ).isSome &&
    decide (s.pileHolding cdSQ == s.pileHolding cdHK) &&
    decide (s.pileHolding cdQQ == s.pileHolding cdDK))) &&
  decide (cdPairA ≠ cdPairB)

/-! ## The verdicts -/

/-! ## Family W — the exchange-steered wiggle-fold (probe (a)'s second required cell)

The exchlaw session's refuted pinch (their twin-kings cell in
probes/ExchCanLawProbe.lean, branch orig-exch-canlaw, mirrored here
with credit): hearts and diamonds both climbed A..Q; ♥K sits bare
on p1, its twin ♦K carries the non-twin residue ♣Q on p5.  The two
SATURATED mates split the FOUND channel 13/12 vs 12/13 — canon
literal-unequal, and NO pure-pull play can join them (every pull
strictly drops `foundTotal`, so a foundTotal-preserving pair is
pull-unreachable except vacuously): the SLIDE letter is the
irreducible padding work between them (pull-slide-pull, all
reversible, the A2 anatomy).  VERDICT (the exchlaw correction
certified at my battery too): the sigma-absorption of the slide
letter is REFUTED — the cone alphabet is pulls + slides + pure
draws, three letters, all reversible, class-honest.
-/

def cdFWFHeart : List Card := Suit.heart.upCards.take 12
def cdFWFDiamond : List Card := Suit.diamond.upCards.take 12

/-- The twin-kings fork state (exchlaw's exFork, verbatim shape). -/
def cdFork : State where
  found := fun s =>
    match s with
    | .heart => cdFWFHeart
    | .diamond => cdFWFDiamond
    | _ => []
  piles := fun a =>
    match a with
    | .p1 => ⟨[], [cdHK]⟩
    | .p5 => ⟨[], [cdDK, cdQQ]⟩
    | _ => ⟨[], []⟩
  stock := Card.universe.filter fun c =>
    decide (c ∉ cdFWFHeart ∧ c ∉ cdFWFDiamond ∧
      c ≠ cdHK ∧ c ≠ cdDK ∧ c ≠ cdQQ)
  waste := []
  drawStep := 1

/-- The slide image (the licensed exchange realized as a plain
noreveal tabToTab — exchlaw's exForkX, verbatim shape). -/
def cdForkX : State :=
  (cdFork.run [Move.tabToTab cdQQ (Sum.inr cdHK)]).getD cdFork

def cdCanonF : State := canon cdFork
def cdCanonX : State := canon cdForkX

/-- THE FOUND-SPLIT ANALYSIS, both tiers.  Every `foundToTab` pull
strictly drops `foundTotal` (the banked step tables), so members of
EQUAL `foundTotal` are pure-pull-unreachable from each other except
by the empty play.  THE RAW TIER: exFork and its slide image share
foundTotal 24 and differ — the slide is irreducible at the raw
level.  THE SATURATED TIER: the canon mates share foundTotal 25,
differ by the FOUND split (hearts-full vs diamonds-full, 13/12 vs
12/13) — pure pulls cannot join them, and no exchange chain joins
them either (exchanges write piles only; the exchlaw row).  The
honest A2 highway: each canon reaches its RAW twin by ONE pull
(undo legs of the bare-king raises), and the RAW pair is joined by
the SLIDE — the slide letter is the irreducible padding work, the
sigma-absorption is REFUTED. -/
def cdGateW : Bool :=
  cdWfB cdFork && cdWfB cdForkX &&
  -- the slide realizes the exchange image, both directions
  decide ((cdFork.run [Move.tabToTab cdQQ (Sum.inr cdHK)]).any (fun w => w == cdForkX)) &&
  decide ((cdForkX.run [Move.tabToTab cdQQ (Sum.inr cdDK)]).any (fun w => w == cdFork)) &&
  -- the canon mates: both saturated (Final), canon literal-unequal
  cdFinalB cdCanonF && cdFinalB cdCanonX &&
  decide (cdCanonX ≠ cdCanonF) &&
  -- THE FOUND SPLIT at the saturated mates: 13/12 vs 12/13
  decide ((cdCanonF).found .heart == Suit.heart.upCards) &&
  decide ((cdCanonF).found .diamond == cdFWFDiamond) &&
  decide ((cdCanonX).found .diamond == Suit.diamond.upCards) &&
  decide ((cdCanonX).found .heart == cdFWFHeart) &&
  -- THE EQUAL-TOTAL DATUM at both tiers: pure pulls cannot travel
  -- between equal-total pair members (each pull drops the total)
  decide (foundTotal cdCanonF == foundTotal cdCanonX) &&
  decide (foundTotal cdFork == foundTotal cdForkX) &&
  decide (cdFork ≠ cdForkX) &&
  -- the pulls of the A2 highway: each canon reaches its RAW twin
  -- by one pull (the undo of the bare-king raise)
  decide ((cdCanonF.run [Move.foundToTab cdHK (Sum.inl Anchor.p1)]).any
    (fun w => w == cdFork)) &&
  decide ((cdCanonX.run [Move.foundToTab cdDK (Sum.inl Anchor.p5)]).any
    (fun w => w == cdForkX)) &&
  -- the poisoned composite: the naive one-direction pull-slide-pull
  -- from cdCanonF cannot even run (its third leg would need
  -- diamonds already full at the raw slide image) — the honest
  -- witness at this cell is the split form: canon -> raw by PULL,
  -- raw -> raw image by SLIDE, image <- canon by PULL
  decide ((cdCanonF.run [Move.foundToTab cdHK (Sum.inl Anchor.p1),
      Move.tabToTab cdQQ (Sum.inr cdHK),
      Move.foundToTab cdDK (Sum.inl Anchor.p5)]).isNone)

/-- All gates including the W family. -/
def cdAllGates : Bool :=
  cdGateA1 && cdGateA2 && cdGateA3 && cdGateB && cdGateC && cdGateD && cdGateE
    && cdGateW

-- The orbit sizes and refutation data the verdicts pin (printed for
-- the ledger; the gates above carry the load-bearing checks):
#eval (cdOrbit (cdMk cdP10 9 1)).length
#eval (cdOrbit (cdMk cdP9 3 3)).length
#eval (cdOrbit (cdMk cdP7 1 3)).length
#eval (cdOrbit (cdMk cdP10 4 3)).length
#eval (cdOrbit (cdMk cdP11 5 3)).length
#eval (cdOrbit (cdNormZone cdP9 3)).length
#eval (cdPullFires cdExU).length
#eval (cdSlideFires cdPairA).length                       -- expect 10: only the host-KING run relocations (they carry their riders)
#eval (cdResidueSlideFires cdPairA [cdSQ, cdQQ]).length  -- expect 0: the residues themselves have no slide
#eval (cdSlideClosure 4 cdPairA).length                  -- the bounded pairing-closure size
#eval (foundTotal cdCanonF, foundTotal cdCanonX)          -- expect (25, 25): the equal-total datum

#eval! do
  if cdAllGates then
    IO.println "CANONDECOMPRESS: ALL GATES HOLD —"
    IO.println "A: finalWiggle beyond length 1 live at the cube (two independent twin-host residues,"
    IO.println "   all four corners joined by noreveal slides, both orders commute) and at the"
    IO.println "   worry-back bridge (pulled-substrate relocation, the return's raise the exact"
    IO.println "   undo, the direct slide barred)."
    IO.println "A3: the ONE-LETTER class-anchor form is REFUTED at the re-derived exhibit — no"
    IO.println "    foundToTab fires at its anchor (foundations empty), pure pulls cannot move"
    IO.println "    a residue, so the two-letter grade stands for (A)."
    IO.println "B: pristine is UNREACHABLE from every non-pristine pure orbit, drawStep 1 and 3,"
    IO.println "   partial-final-draw corners included (the first falsifier candidate confirmed)."
    IO.println "   The strongest probe-certified normal form is the UNIQUE PASS BASE ([], pool, d)."
    IO.println "C: saturation preserves the zone verbatim and the phase line; the draw/canon"
    IO.println "   commutation square holds literally at pure, offset and pristine zones; the"
    IO.println "   license is zone-blind."
    IO.println "D: offset (and pristine) zones are frozen: no reversible draw edge leaves them."
    IO.println "E: canon_slide — cube confluence live; occupied-twin-host and revealing-slide"
    IO.println "   negatives hold; the E4 interaction is LIVE (a slide can expose a licensed"
    IO.println "   raise — disjointness dies, any seating pass must re-saturate); the E5"
    IO.println "   same-pair transposition is frozen at pull-free boards — pairing is class data."
    IO.println "W: the exchange-steered twin-kings cell certifies the exchlaw correction —"
    IO.println "   the saturated mates split the found channel (13/12 vs 12/13), no pure-pull"
    IO.println "   play joins them (foundTotal 25 = 25, pulls drop it strictly), and the"
    IO.println "   pull-slide-pull witness carries the SLIDE as irreducible padding work:"
    IO.println "   the sigma-absorption of the slide letter is REFUTED — the cone alphabet"
    IO.println "   is PULLS + SLIDES + PURE DRAWS, three letters, all reversible, class-honest."
  else
    throw (IO.userError "CANONDECOMPRESS: A GATE FAILED — see the numbers above")
