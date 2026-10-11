import Orig

/-!
# CANON-COMMUTATION probe ledger — the census states, decided

Probes for the canon-commutation card (2026-10-11), external to the
workspace, run with `lake env lean`.  `canon` is COMPUTABLE
(`canonAux 53`; every row below kernels it through `decide`), so the
equations are run on concrete STATES before any proof effort:

* E1-LITERAL (`canon (st.commit c) = (canon st).commit c`): the
  committed state on both sides with NO re-saturation on the right.
* E1-HONEST (re-saturated on both sides:
  `canon (st.commit c) = canon ((canon st).commit c)`).
* E2-HONEST (the user's canonical-equality, successor grade at
  `u = canon st`: `canon (u + wasteToFound c) = canon (u + wasteToTab
  c b)` — the seat route's founding leg is carried by the
  saturation's own merge of the seated `c`).
* THE MERGED LEG: the literal route's `tabToFound c` step after the
  middle canon — does it fire?  (At WF: no — `c` is lifted by the
  middle saturation itself, canon never re-seats.)
* THE QUINTET: `wasteToTab` then IMMEDIATE `tabToFound` is
  state-exact to `wasteToFound` (Option equality, same `some`).
* LEGALITY TRANSPORT, both directions, per component (waste head,
  rung, base).
* THE DRAW MIRROR: `canon` after `draw` vs `draw` after `canon` —
  deal case (`drawStep` 1 and 3), recycle case, none-synchrony case.

Card craft notes: every state below is WF and accounts all 52 cards
exactly once (the "rest" cards sit in the waste tail); pile runs are
`runOK`; the parked-card shapes are deliberate (`A♣` / `A♠` as the
rank r−1 opposite-color d-shapes, unstackable in canon — `chop = []`,
not a king — their target appears when `c`'s seating fires, but only
a `tabToTab` (never a canon lift) could ever consume it).
-/

namespace CanLawProbe

set_option maxRecDepth 100000

/-! ## The instruments -/

private def H (r : Rank) : Card := ⟨Suit.heart, r⟩
private def S (r : Rank) : Card := ⟨Suit.spade, r⟩
private def D (r : Rank) : Card := ⟨Suit.diamond, r⟩
private def C (r : Rank) : Card := ⟨Suit.club, r⟩

/-- The deck minus the craft cards. -/
private def restMinus (used : List Card) : List Card :=
  Card.universe.filter fun x => decide (¬ (x ∈ used))

/-- The 14-component pointwise `DecidableEq State` (the witness
corpus's family-1 instrument). -/
private def decSt (s t : State) : Decidable (s = t) :=
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

local instance : DecidableEq State := fun s t => decSt s t

/-- The display bridge for `#eval` verdict lines. -/
private def bEq (s t : State) : Bool :=
  match decSt s t with
  | isTrue _ => true
  | isFalse _ => false

private def bSome (o : Option State) : Bool :=
  match o with
  | some _ => true
  | none => false

/-! ## W1 — the E1-literal refutation, at a canon-fixed census state

The rung-shadow witness: `2♥` at the waste head, hearts at height 1,
and the rung-`+1` card `3♥` parked on a pile top WITH its under-seat
surviving (`[4♠, 3♥]`).  `canon st = st` (nothing licensed), the
commit moves the hearts rung to height 2, and the post-commit
saturation lifts `3♥`.  Both shapes fire for `c = 2♥`; the tab seat
is `3♠` on pile 1. -/

private def w1Found : Suit → List Card
  | .heart => [H .ace]
  | _ => []

private def w1Piles : Anchor → Pile
  | .p0 => ⟨[], [S .four, H .three]⟩
  | .p1 => ⟨[], [S .three]⟩
  | _ => ⟨[], []⟩

def W1 : State where
  found := w1Found
  piles := w1Piles
  stock := []
  waste := [H .two] ++ restMinus [H .ace, S .four, H .three, S .three, H .two]
  drawStep := 1

private theorem W1_wf : W1.WF := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s; cases s with
    | spade => exact ⟨0, rfl⟩
    | heart => exact ⟨1, rfl⟩
    | diamond => exact ⟨0, rfl⟩
    | club => exact ⟨0, rfl⟩
  · intro a; cases a <;> first | rfl | decide
  · intro c _; rcases c with ⟨s, r⟩; cases s <;> cases r <;> decide
  · decide

theorem W1_bothShapes :
    (State.step W1 (Move.wasteToFound (H .two))).isSome = true ∧
    (State.step W1 (Move.wasteToTab (H .two) (Sum.inr (S .three)))).isSome = true := by
  decide

theorem W1_canonFixed : canon W1 = W1 := by decide

/-- The committed state (the found route's successor, the `getD`
plumbing standing on the fire row above). -/
def W1c : State := (State.step W1 (Move.wasteToFound (H .two))).getD W1

/-- The E1-LITERAL right side: the commit fired at `canon W1`. -/
def W1rB : State := (State.step (canon W1) (Move.wasteToFound (H .two))).getD (canon W1)

/-- **E1-LITERAL FAILS** — the re-saturation channel is real. -/
theorem W1_E1_literal_refuted : ¬ (canon W1c = W1rB) := by decide

/-- **E1-HONEST HOLDS** — re-saturate both sides and the shadow dies. -/
theorem W1_E1_honest : canon W1c = canon W1rB := by decide

/-- What the shadow lifted: the left side founds `3♥` (height 3),
the literal right side stays at height 2; pile 0 keeps its run. -/
theorem W1_shadowAnatomy :
    ((canon W1c).found .heart).length = 3 ∧
    (W1rB.found .heart).length = 2 ∧
    ((canon W1c).piles .p0).faceUp = [S .four] ∧
    (W1rB.piles .p0).faceUp = [S .four, H .three] := by
  decide

#eval bEq (canon W1c) W1rB                       -- false : E1-LITERAL refuted
#eval bEq (canon W1c) (canon W1rB)                -- true  : E1-HONEST holds
#eval ((canon W1c).found .heart).length          -- 3     : the post-commit lift ran
#eval (W1rB.found .heart).length                 -- 2     : the literal route stayed put

/-! ## W2 — canon st ≠ st, E1 both ways, the E2 successor grade,
and the d-shape in flight alongside everything

Founds: `♠ [A♠]`, `♦ [A♦]`.  Piles: the `3♦` shadow over `[4♠]`;
the `3♠` seat; the licensed `2♠` over `[3♥]` (so `canon W2 ≠ W2`);
the parked `A♣` — the rank `r−1` opposite-color d-shape for
`c = 2♦`, unstackable in canon, its target created by `c`'s seating. -/

private def w2Found : Suit → List Card
  | .spade => [S .ace]
  | .diamond => [D .ace]
  | _ => []

private def w2Piles : Anchor → Pile
  | .p0 => ⟨[], [S .four, D .three]⟩
  | .p1 => ⟨[], [S .three]⟩
  | .p2 => ⟨[], [H .three, S .two]⟩
  | .p3 => ⟨[], [C .ace]⟩
  | _ => ⟨[], []⟩

private def w2Used : List Card :=
  [S .ace, D .ace, S .four, D .three, S .three, H .three, S .two, C .ace, D .two]

def W2 : State where
  found := w2Found
  piles := w2Piles
  stock := []
  waste := [D .two] ++ restMinus w2Used
  drawStep := 1

private theorem W2_wf : W2.WF := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s; cases s with
    | spade => exact ⟨1, rfl⟩
    | heart => exact ⟨0, rfl⟩
    | diamond => exact ⟨1, rfl⟩
    | club => exact ⟨0, rfl⟩
  · intro a; cases a <;> first | rfl | decide
  · intro c _; rcases c with ⟨s, r⟩; cases s <;> cases r <;> decide
  · decide

theorem W2_bothShapes :
    (State.step W2 (Move.wasteToFound (D .two))).isSome = true ∧
    (State.step W2 (Move.wasteToTab (D .two) (Sum.inr (S .three)))).isSome = true := by
  decide

theorem W2_canonMoves : ¬ (canon W2 = W2) := by decide

/-- The E2 successor grade: both shapes fire AT `u = canon W2`. -/
theorem W2_bothShapesAtCanon :
    (State.step (canon W2) (Move.wasteToFound (D .two))).isSome = true ∧
    (State.step (canon W2) (Move.wasteToTab (D .two) (Sum.inr (S .three)))).isSome = true := by
  decide

/-- The waste-position component transports AS AN IFF (canon never
writes the waste). -/
theorem W2_wastePositionInv : (canon W2).wasteIs (D .two) = W2.wasteIs (D .two) := by
  decide

def W2c : State := (State.step W2 (Move.wasteToFound (D .two))).getD W2
def W2rB : State := (State.step (canon W2) (Move.wasteToFound (D .two))).getD (canon W2)

theorem W2_E1_literal_refuted : ¬ (canon W2c = W2rB) := by decide
theorem W2_E1_honest : canon W2c = canon W2rB := by decide

/-- **E2 at the successor grade** — the two routes out of
`u = canon W2`: `2♦` founded from the waste, versus `2♦` seated on
`3♠` and saturation left to merge it back onto the foundation. -/
def W2uF : State := (State.step (canon W2) (Move.wasteToFound (D .two))).getD (canon W2)
def W2uT : State := (State.step (canon W2) (Move.wasteToTab (D .two) (Sum.inr (S .three)))).getD (canon W2)

theorem W2_E2 : canon W2uF = canon W2uT := by decide

/-- THE MERGED LEG: the literal route's `tabToFound c` after the
middle canon DOES NOT FIRE at WF — the seated `c` was lifted by the
saturation itself. -/
theorem W2_mergedLeg : State.step (canon W2uT) (Move.tabToFound (D .two)) = none := by
  decide

/-- The d-shape card stays parked through every route (canon lifts
only — it can never bury `c` under, nor stack anything onto, the
parked card). -/
theorem W2_dParked :
    ((canon W2uF).piles .p3).faceUp = [C .ace] ∧
    ((canon W2uT).piles .p3).faceUp = [C .ace] := by
  decide

#eval bEq (canon W2c) W2rB                        -- false : E1-LITERAL refuted (canon ≠ st)
#eval bEq (canon W2c) (canon W2rB)                 -- true  : E1-HONEST holds
#eval bEq (canon W2uF) (canon W2uT)                -- true  : E2 holds, successor grade
#eval bSome (State.step (canon W2uT) (Move.tabToFound (D .two))) -- false : the founding leg is merged
#eval (((canon W2uF).piles .p3).faceUp == (W2uT.piles .p3).faceUp : Bool) -- true : the parked d untouched
#eval bEq (canon W2) W2                            -- false : canon did move (the 2♠ lift)

/-! ## W3 — the pure d-shape census, the quintet composite identity

Founds: `♦ [A♦]`.  The parked `A♣` (`[A♣]` alone, so no under-seat
and no bare king), the `3♠` seat, `c = 2♦` at the waste head,
`canon W3 = W3` (nothing licensed: the parked ace is rung-ready but
seat-barred). -/

private def w3Found : Suit → List Card
  | .diamond => [D .ace]
  | _ => []

private def w3Piles : Anchor → Pile
  | .p0 => ⟨[], [C .ace]⟩
  | .p1 => ⟨[], [S .three]⟩
  | _ => ⟨[], []⟩

def W3 : State where
  found := w3Found
  piles := w3Piles
  stock := []
  waste := [D .two] ++ restMinus [D .ace, C .ace, S .three, D .two]
  drawStep := 1

private theorem W3_wf : W3.WF := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s; cases s with
    | spade => exact ⟨0, rfl⟩
    | heart => exact ⟨0, rfl⟩
    | diamond => exact ⟨1, rfl⟩
    | club => exact ⟨0, rfl⟩
  · intro a; cases a <;> first | rfl | decide
  · intro c _; rcases c with ⟨s, r⟩; cases s <;> cases r <;> decide
  · decide

theorem W3_bothShapes :
    (State.step W3 (Move.wasteToFound (D .two))).isSome = true ∧
    (State.step W3 (Move.wasteToTab (D .two) (Sum.inr (S .three)))).isSome = true := by
  decide

theorem W3_canonFixed : canon W3 = W3 := by decide

def W3uF : State := (State.step W3 (Move.wasteToFound (D .two))).getD W3
def W3uT : State := (State.step W3 (Move.wasteToTab (D .two) (Sum.inr (S .three)))).getD W3

/-- **THE QUINTET**: seat `c` then found it IMMEDIATELY — the two
steps land on the exact `some` the direct waste founding produced. -/
theorem W3_quintet :
    State.step W3uT (Move.tabToFound (D .two)) = State.step W3 (Move.wasteToFound (D .two)) := by
  decide

theorem W3_E2 : canon W3uF = canon W3uT := by decide
theorem W3_mergedLeg : State.step (canon W3uT) (Move.tabToFound (D .two)) = none := by decide

/-- The seated state before saturation is the commit state plus the
parked seat card — the saturation's merge of `c` returns pile 1 to
its pre-seat shape. -/
theorem W3_mergeReturns :
    (canon W3uT).piles .p1 = ⟨[], [S .three]⟩ ∧
    (canon W3uF).piles .p1 = ⟨[], [S .three]⟩ := by
  decide

#eval bEq (canon W3uF) (canon W3uT)                -- true  : E2 holds at the pure d-shape
#eval bSome (State.step W3uT (Move.tabToFound (D .two)))     -- true  : the quintet fires pre-canon
#eval bSome (State.step (canon W3uT) (Move.tabToFound (D .two))) -- false : merged post-canon
#eval (((canon W3uF).piles .p0).faceUp == (W3uT.piles .p0).faceUp : Bool) -- true : d stays parked

/-! ## W4 — the draw mirror at a canon-active state (`drawStep` 1
and 3), and the recycle draw at W3 -/

def W4 : State where
  found := w2Found
  piles := w2Piles
  stock := [H .two, H .four]
  waste := [D .two] ++ restMinus (w2Used ++ [H .two, H .four])
  drawStep := 1

private theorem W4_wf : W4.WF := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s; cases s with
    | spade => exact ⟨1, rfl⟩
    | heart => exact ⟨0, rfl⟩
    | diamond => exact ⟨1, rfl⟩
    | club => exact ⟨0, rfl⟩
  · intro a; cases a <;> first | rfl | decide
  · intro c _; rcases c with ⟨s, r⟩; cases s <;> cases r <;> decide
  · decide

theorem W4_canonMoves : ¬ (canon W4 = W4) := by decide

/-- The draw mirror: `canon . draw = draw . canon` at the deal
state, WITH the `2♠` lift live on both routes. -/
theorem W4_drawMirror :
    canon ((State.step W4 Move.draw).getD W4) =
      (State.step (canon W4) Move.draw).getD (canon W4) := by
  decide

/-- Same mirror at draw width 3. -/
def W4b : State where
  found := w2Found
  piles := w2Piles
  stock := [H .two, H .four]
  waste := [D .two] ++ restMinus (w2Used ++ [H .two, H .four])
  drawStep := 3

theorem W4b_drawMirror :
    canon ((State.step W4b Move.draw).getD W4b) =
      (State.step (canon W4b) Move.draw).getD (canon W4b) := by
  decide

/-- The recycle draw (empty stock, nonempty waste) mirrors too,
parked cards and all. -/
theorem W3_recycleDrawMirror :
    canon ((State.step W3 Move.draw).getD W3) =
      (State.step (canon W3) Move.draw).getD (canon W3) := by
  decide

theorem W3_recycleDrawFires : (State.step W3 Move.draw).isSome = true := by decide

/-- The none-synchrony case: everything founded, board and cycle
empty — the draw is `none` at the state AND at its canon. -/
def W5 : State where
  found := fun s => s.upCards
  piles := fun _ => ⟨[], []⟩
  stock := []
  waste := []
  drawStep := 1

private theorem W5_wf : W5.WF := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s; cases s with
    | spade => exact ⟨13, rfl⟩
    | heart => exact ⟨13, rfl⟩
    | diamond => exact ⟨13, rfl⟩
    | club => exact ⟨13, rfl⟩
  · intro a; cases a <;> first | rfl | decide
  · intro c _; rcases c with ⟨s, r⟩; cases s <;> cases r <;> decide
  · decide

theorem W5_drawNoneSync :
    State.step W5 Move.draw = none ∧ State.step (canon W5) Move.draw = none := by
  decide

theorem W5_canonFixed : canon W5 = W5 := by decide

#eval bEq (canon ((State.step W4 Move.draw).getD W4)) ((State.step (canon W4) Move.draw).getD (canon W4))
                                                  -- true : draw mirror, deal case
#eval bEq (canon ((State.step W4b Move.draw).getD W4b)) ((State.step (canon W4b) Move.draw).getD (canon W4b))
                                                  -- true : draw mirror, drawStep 3
#eval bEq (canon ((State.step W3 Move.draw).getD W3)) ((State.step (canon W3) Move.draw).getD (canon W3))
                                                  -- true : draw mirror, recycle case
#eval bSome (State.step W5 Move.draw)              -- false : none-synchrony holds
#eval bSome (State.step (canon W5) Move.draw)      -- false

/-! ## W7 — the legality transport's R→L REFUTATION

`canon` can ADVANCE the rung and create legality that the raw state
lacks: `3♥` at the waste head is illegal at `W7` (hearts at height
1) and legal at `canon W7` (the licensed `2♥` lift brought hearts
to height 2). -/

private def w7Found : Suit → List Card
  | .heart => [H .ace]
  | _ => []

private def w7Piles : Anchor → Pile
  | .p0 => ⟨[], [S .three, H .two]⟩
  | _ => ⟨[], []⟩

def W7 : State where
  found := w7Found
  piles := w7Piles
  stock := []
  waste := [H .three] ++ restMinus [H .ace, S .three, H .two, H .three]
  drawStep := 1

private theorem W7_wf : W7.WF := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s; cases s with
    | spade => exact ⟨0, rfl⟩
    | heart => exact ⟨1, rfl⟩
    | diamond => exact ⟨0, rfl⟩
    | club => exact ⟨0, rfl⟩
  · intro a; cases a <;> first | rfl | decide
  · intro c _; rcases c with ⟨s, r⟩; cases s <;> cases r <;> decide
  · decide

theorem W7_canonMoves : ¬ (canon W7 = W7) := by decide

/-- **R→L REFUTED**: legal at the canonical form... -/
theorem W7_firesAtCanon :
    (State.step (canon W7) (Move.wasteToFound (H .three))).isSome = true := by
  decide

/-- ...ILLEGAL at the raw state — the iff fails at WF. -/
theorem W7_notAtRaw : State.step W7 (Move.wasteToFound (H .three)) = none := by
  decide

/-- The waste-position component is still an iff here (the head
stays the head through the rung-advancing saturation); it is the
RUNG component that breaks the transport backwards. -/
theorem W7_wastePositionInv : (canon W7).wasteIs (H .three) = W7.wasteIs (H .three) := by
  decide

#eval bSome (State.step W7 (Move.wasteToFound (H .three)))      -- false : illegal at raw
#eval bSome (State.step (canon W7) (Move.wasteToFound (H .three))) -- true  : legal at canon
#eval bEq (canon W7) W7                                         -- false : canon advanced the rung

/-! ## W8 — both shapes at the raw state, the seat EVAPORATED at
the canonical one

The tab base `3♠` is licensed to lift at `W8`, so `canon` consumes
it: the seat leg of the census does not transport backwards. -/

private def w8Found : Suit → List Card
  | .spade => [S .ace, S .two]
  | .diamond => [D .ace]
  | _ => []

private def w8Piles : Anchor → Pile
  | .p0 => ⟨[], [H .four, S .three]⟩
  | _ => ⟨[], []⟩

def W8 : State where
  found := w8Found
  piles := w8Piles
  stock := []
  waste := [D .two] ++ restMinus [S .ace, S .two, D .ace, H .four, S .three, D .two]
  drawStep := 1

private theorem W8_wf : W8.WF := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s; cases s with
    | spade => exact ⟨2, rfl⟩
    | heart => exact ⟨0, rfl⟩
    | diamond => exact ⟨1, rfl⟩
    | club => exact ⟨0, rfl⟩
  · intro a; cases a <;> first | rfl | decide
  · intro c _; rcases c with ⟨s, r⟩; cases s <;> cases r <;> decide
  · decide

theorem W8_bothShapesAtRaw :
    (State.step W8 (Move.wasteToFound (D .two))).isSome = true ∧
    (State.step W8 (Move.wasteToTab (D .two) (Sum.inr (S .three)))).isSome = true := by
  decide

theorem W8_canonMoves : ¬ (canon W8 = W8) := by decide

/-- The found leg still fires at the canonical form (the L→R
transport for the rung + waste-position components). -/
theorem W8_foundLegAtCanon :
    (State.step (canon W8) (Move.wasteToFound (D .two))).isSome = true := by
  decide

/-- The seat leg is GONE at the canonical form: `3♠` was lifted. -/
theorem W8_seatLegEvaporated :
    State.step (canon W8) (Move.wasteToTab (D .two) (Sum.inr (S .three))) = none := by
  decide

#eval bSome (State.step W8 (Move.wasteToTab (D .two) (Sum.inr (S .three))))          -- true  at raw
#eval bSome (State.step (canon W8) (Move.wasteToTab (D .two) (Sum.inr (S .three))))  -- false at canon

end CanLawProbe
