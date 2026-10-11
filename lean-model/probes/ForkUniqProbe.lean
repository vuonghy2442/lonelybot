import Orig.Canonical

/-! # ForkUniqProbe — the G2 maximality-transport gate probe

The forkState-unique card's LAST gate (FUTURES-ORIG §11-L5; the one
named BLOCKED residue under `forkState_unique`) is the
maximality-transport claim, diagnosed G1/G2/G3 per gate.  The task's
G2 head states it at its sharpest:

  **Two same-class forkStates witnessing the SAME pair {x, x.twin}
  have EQUAL rungs on every non-pair suit** — "the strict invariant:
  rungAt st₁ s = rungAt st₂ s for all non-pair suits s".

Per the house rule (probe-first on any row that feels handwavy:
craft two forkStates of one class with a non-pair suit at different
heights — if the craft FAILS, the lemma is provable), this probe
crafts exactly that pair BEFORE any proof effort:

* `st₁` — rungs (♥ 4, ♦ 4, ♠ 5, ♣ 3); the fork pair {5♥, 5♦} pinned
  at rank 5; the only licensed raise is 5♥, which sits DIRECTLY ON
  the black next-up card 6♠ (the witness is its blocker); the twin
  5♦ is bare-bottom non-king at an empty-hidden pile (the V6 seat
  bar kills its license).
* the journey `τ = [tabToTab 5♥ (inr 6♣), tabToFound 6♠]` — ONE
  flat cargo leg (the witness slides OFF 6♠ onto 6♣, both fits
  rank-adjacent opposite-color; the source keeps two face-up cards,
  so the mirror slide back is the leg's own undo), then ONE
  licensed raise (6♠ next-up, exposed, under-seat card 7♥ remains —
  the pull-back is the leg's own undo).  The successor `ω` has rungs
  (♥ 4, ♦ 4, ♠ 6, ♣ 3): the ♠ rung MOVED, everything else identical.
* the return journey `σ = [foundToTab 6♠ (inr 7♥), tabToTab 5♥
  (inr 6♠)]` restores `st₁` EXACTLY — every leg of both journeys is
  reversible by its single-move mirror, so the two states are
  `sameOrbitSetoid`-related (witness shuffles both ways).
* `ω` is ITSELF a forkState of the SAME pair {5♥, 5♦} with the SAME
  orientation (witness 5♥): pins hold; the only licensed raise is
  5♥ (now seated on [7♦, 6♣]); 6♠ is founded; the new ♠ next-up
  7♠ is stock-resident; ♣'s next-up 4♣ is stock-resident.

If every gate below holds, the strict G2 head is REFUTED at theorem
grade: same class, same pair, same orientation, and the non-pair ♠
rungs differ (5 vs 6).  THE 07247ec RE-VALIDATION: the corrected
conjugate composite (`tabToTab x.twin`, not the cargo) and the
cross-bridge `FaceShape := CargoPath w w' ∨ ∧∃ z, conjugateForkState
w z ∧ CargoPath z w'` are DEFINITION-ORTHOGONAL to every row here
(the census, the legs, the reversibility witnesses and the rung
ledger read only the step records); the refutation now closes at
BOTH grades — the cargo grade through `cargoPath_rungs`, the
cross grade through the composite's net-flat (its slide leg is a
`tabToTab` whichever card it moves) — carried at theorem grade in
`Orig/ForkStateUniqGate.lean` (`forkState_unique_refuted`).

Run: `lake env lean probes/ForkUniqProbe.lean` from `lean-model/`.
The final `#eval!` throws if any gate fails.  Every play here is
oracle-verified (`State.step` is the only oracle): a dead hand play
is a construction bug and the probe throws.
-/

private def crd (s : Suit) (r : Rank) : Card := ⟨s, r⟩

/-- The five spot cards of the craft. -/
private def H5 : Card := crd .heart .five     -- the pair witness (5♥)
private def D5 : Card := crd .diamond .five   -- the covered twin (5♦)
private def S6 : Card := crd .spade .six      -- the movable next-up (6♠)
private def H7 : Card := crd .heart .seven    -- the under-seat anchor (7♥)
private def C6 : Card := crd .club .six       -- the witness's landing top (6♣)
private def D7 : Card := crd .diamond .seven -- R's bottom (7♦)

/-- rungs: hearts 4, diamonds 4, spades 5, clubs 3. -/
private def hmap : Suit → Nat
  | .heart => 4 | .diamond => 4 | .spade => 5 | .club => 3

/-- The crafted forkState st₁ (WF by the audit row below):

* p0 (P)  = ⟨[], [7♥, 6♠, 5♥]⟩ — 5♥ tops 6♠ tops 7♥: the witness is
  the blocker of its own suit-neighbor next-up 6♠;
* p1 (R)  = ⟨[], [7♦, 6♣]⟩ — the landing host for the witness slide;
* p2 (P'') = ⟨[], [5♦]⟩ — the twin, bare-bottom OVER NO hidden deck
  (hidden = []), non-king: the seat bar kills its license;
* p3–p6  — hidden-only sink piles (faceUp = []): nothing can fire
  from them (no face-up card to move) and nothing can land on them
  (inl needs isEmpty, inr needs a face-up top), so the rest of the
  deck parks there, dead forever;
* stock = [7♠, 4♣] — the current ♠/♣ next-ups, stock-resident;
* waste = [], drawStep = 1. -/
private def st1 : State where
  found := fun s => s.upCards.take (hmap s)
  piles := fun a => match a with
    | .p0 => ⟨[], [H7, S6, H5]⟩
    | .p1 => ⟨[], [D7, C6]⟩
    | .p2 => ⟨[], [D5]⟩
    | .p3 => ⟨[crd .club .king, crd .club .queen], []⟩
    | .p4 => ⟨[crd .heart .king, crd .heart .queen, crd .heart .jack,
               crd .heart .ten, crd .heart .nine, crd .heart .eight,
               crd .heart .six], []⟩
    | .p5 => ⟨[crd .diamond .king, crd .diamond .queen, crd .diamond .jack,
               crd .diamond .ten, crd .diamond .nine, crd .diamond .eight,
               crd .diamond .six], []⟩
    | .p6 => ⟨[crd .spade .king, crd .spade .queen, crd .spade .jack,
               crd .spade .ten, crd .spade .nine, crd .spade .eight,
               crd .club .five, crd .club .seven, crd .club .eight,
               crd .club .nine, crd .club .ten, crd .club .jack], []⟩
  stock := [crd .spade .seven, crd .club .four]
  waste := []
  drawStep := 1

private def rankStr : Rank → String
  | .ace => "A" | .two => "2" | .three => "3" | .four => "4"
  | .five => "5" | .six => "6" | .seven => "7" | .eight => "8"
  | .nine => "9" | .ten => "10" | .jack => "J" | .queen => "Q"
  | .king => "K"

private def suitStr : Suit → String
  | .spade => "♠" | .heart => "♥" | .diamond => "♦" | .club => "♣"

private def cardStr (c : Card) : String := suitStr c.suit ++ rankStr c.rank

/-- The forward journey τ: slide the witness off 6♠ (onto 6♣), then
raise 6♠ to its foundation. -/
private def m1 : Move := Move.tabToTab H5 (Sum.inr C6)
private def m2 : Move := Move.tabToFound S6

/-- The return journey σ: pull 6♠ back onto its under-seat 7♥,
then slide the witness back onto the exposed 6♠. -/
private def r1 : Move := Move.foundToTab S6 (Sum.inr H7)
private def r2 : Move := Move.tabToTab H5 (Sum.inr S6)

private def stepD (st : State) (m : Move) : State :=
  match st.step m with
  | none => st
  | some s' => s'

/-- Field-exact state equality (State has no `DecidableEq` derive;
compare every zone list-by-list). -/
private def stEqB (u v : State) : Bool :=
  Suit.all.all (fun s => u.found s == v.found s) &&
  Anchor.all.all (fun a =>
    (u.piles a).hidden == (v.piles a).hidden &&
    (u.piles a).faceUp == (v.piles a).faceUp) &&
  u.stock == v.stock && u.waste == v.waste && u.drawStep == v.drawStep

/-- The WF audit of the craft (the conservation invariant,
decide-grade): founds are build-order prefixes, every pile run is
legal, all 52 cards occur exactly once, drawStep is 1. -/
private def wfB (st : State) : Bool :=
  Suit.all.all (fun s => decide (st.found s = s.upCards.take (st.found s).length)) &&
  Anchor.all.all (fun a => runOK (st.piles a).faceUp == true) &&
  Card.universe.all (fun c => decide (st.cardCount c = 1)) &&
  st.drawStep == 1

/-- The forkState census, decide-grade: the pair pins for witness
`w` hold, and the licensed raises at `st` are exactly `w`
(over the full universe, via the banked `canRaiseB` iff). -/
private def forkB (st : State) (w : Card) : Bool :=
  decide ((st.found w.suit).length = w.rank.toIdx) &&
  decide ((st.found w.twin.suit).length = w.rank.toIdx) &&
  Card.universe.all (fun c => decide ((canRaiseB st c == true) == (c == w)))

/-- The rung tuple, for the ledger. -/
private def rungs (st : State) : List Nat :=
  Suit.all.map (fun s => (st.found s).length)

/-- The live-card census (licenses at `st`), for the ledger. -/
private def lives (st : State) : List Card :=
  Card.universe.filter (fun c => canRaiseB st c)

/-- The journey's intermediate and terminal states, oracle-computed
(a failed firing would leave the `getD`-substitute in place and the
equality gates below would throw). -/
private def v1 : State := stepD st1 m1
private def om : State := stepD v1 m2
private def w1 : State := stepD om r1
private def w2 : State := stepD w1 r2

/-- The return leg r2 also fires at v1 (leg m1's own one-move undo,
as `reversibleAtW` wants it), restoring st1 exactly. -/
private def ud1 : State := stepD v1 r2

/-- Leg m2's one-move undo fired at om restores v1 exactly. -/
private def ud2 : State := stepD om r1

private def legOK (st : State) (m : Move) : Bool :=
  match st.step m with | none => false | some _ => true

/-- THE G2 STRICT-INVARIANT VERDICT.  All gates must hold for the
refutation to register. -/
private def allGates : Bool :=
  -- the craft is WF, a forkState of pair {5♥, 5♦}, witness 5♥
  wfB st1 && forkB st1 H5 &&
  -- every journey leg fires (a dead hand play is a construction bug)
  legOK st1 m1 && legOK v1 m2 && legOK om r1 && legOK w1 r2 &&
  -- the one-move undos fire where the reversibility witness needs them
  legOK om r1 && legOK v1 r2 &&
  -- the return journey restores st1 EXACTLY:
  stEqB w2 st1 &&
  -- each leg's own one-move undo restores its pre-leg state:
  stEqB ud2 v1 && stEqB ud1 st1 &&
  -- the terminal state is WF and a forkState of the SAME pair,
  -- SAME orientation (witness 5♥), with pins intact
  wfB om && forkB om H5 &&
  -- the pair suits' rungs agree between st1 and om ...
  decide ((st1.found .heart).length = (om.found .heart).length) &&
  decide ((st1.found .diamond).length = (om.found .diamond).length) &&
  -- ... and the NON-PAIR spade rungs DIFFER (5 vs 6)
  decide (((st1.found .spade).length + 1) = (om.found .spade).length)

#eval wfB st1                -- expect true
#eval forkB st1 H5          -- expect true: st1 is a forkState, witness 5♥
#eval cardStr H5 ++ " live at st1: " ++ toString (canRaiseB st1 H5)
                             -- expect 5♥ live: true
#eval cardStr D5 ++ " (twin) live at st1: " ++ toString (canRaiseB st1 D5)
                             -- expect the twin dead: false
#eval cardStr S6 ++ " live at st1: " ++ toString (canRaiseB st1 S6)
                             -- expect the covered 6♠ dead: false
#eval "st1 rungs (♠,♥,♦,♣): " ++ toString (rungs st1)   -- expect [5, 4, 4, 3]
#eval "v1 live set: " ++ toString ((lives v1).map cardStr)
                             -- expect the mid-journey {5♥, 6♠} pair
#eval legOK st1 m1           -- expect true: the witness slide fires
#eval legOK v1 m2            -- expect true: the 6♠ raise fires
#eval legOK om r1            -- expect true: the 6♠ pull-back fires
#eval legOK w1 r2            -- expect true: the witness slide-back fires
#eval stEqB w2 st1           -- expect true: σ returns to st1 exactly
#eval stEqB ud2 v1            -- expect true: m2's one-move undo at om
#eval stEqB ud1 st1           -- expect true: m1's one-move undo at v1
#eval wfB om                 -- expect true
#eval forkB om H5            -- expect true: ω is a forkState, SAME witness
#eval cardStr H5 ++ " live at om: " ++ toString (canRaiseB om H5)
                             -- expect 5♥ still live at ω: true
#eval "om rungs (♠,♥,♦,♣): " ++ toString (rungs om)     -- expect [6, 4, 4, 3]
#eval "spade rung moved: " ++
  toString ((st1.found .spade).length) ++ " -> " ++
  toString ((om.found .spade).length)        -- expect 5 -> 6

#eval! do
  if allGates then
    IO.println "FORKUNIQ PROBE (G2 maximality-transport, the strict head): ALL GATES HOLD."
    IO.println "The craft: st1 (rungs [S5 H4 D4 C3]; pair {5H, 5D} pinned at rank 5;"
    IO.println "sole license 5H, seated ON the black next-up 6S) and its journey-mate"
    IO.println "omega = st1 after [tabToTab 5H (inr 6C), tabToFound 6S] - both legs"
    IO.println "reversible by their one-move mirrors (probe-verified EXACT state"
    IO.println "restoration both ways), so st1 and omega are sameOrbitSetoid mates."
    IO.println "omega is ITSELF a forkState of the SAME pair {5H, 5D}, SAME orientation"
    IO.println "(witness 5H; the census row above), and its spade rung is 6 vs 5."
    IO.println "VERDICT: the strict G2 head - 'two same-class, same-pair forkStates"
    IO.println "agree on every non-pair rung' - is REFUTED at theorem grade by a"
    IO.println "WF craft, and so is FaceShape between the two (cargo legs preserve"
    IO.println "rungs). The witness's own blocking cargo (5H sits ON 6S) is the"
    IO.println "relocatable cover the task's flip argument never priced: the"
    IO.println "maximality iff pins licenses at the FIXED arrangement, and a flat"
    IO.println "cargo leg can re-expose the covered next-up without touching"
    IO.println "any rung. The honest gate lands as the falsifier plus the"
    IO.println "transport rows that DO survive (the gate file)."
  else
    throw (IO.userError "FORKUNIQ PROBE: A GATE FAILED - read the ledgers above")
