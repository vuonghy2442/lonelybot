import Orig.Dominance
import Orig.Mono
import Orig.Progress

/-!
# The bare-floor corner, physically — the premise-and-canonical-shape
battery for §5.1's residue `tabToFound_dominant_of_ground`

The refute-first exhibit file of the farm-orig-dom-n-ground session
(wave 24, `Orig/Dominance.lean`'s one §5.1 residue — the old [GAP]
channel-A/B reshape in physical dress).  What is probed, and why:

* **Co-realizability** — the row's premise bundle is inhabited at BOTH
  corner arms.  `g1` is the reveal-seat arm (♥7 sole face-up over a
  hidden ♦K, so the raise seats the fresh card — and the ♦K's RED
  color makes it a non-fitting base for ♥7, so the landed
  `tabToFound_undo_under` corner does not swallow this one);
  `g2` is the emptied-pile arm (♠6 is the whole of pile 0, no hidden
  cards, non-king — the emptied pile will not take it back).  At both,
  the full WF + `safeToFound` + `pileOfTop`/`bare`/`corner`/`nextUp`
  guard bundle holds WITH the raise firing — no premise is vacuous.

* **The corner is a genuine commitment** — at `g1` the raise strictly
  drops the hidden total (the ♦K reveal), so no play ever returns
  (`g1_raise_committed`, a pure composition of the LANDED measure
  tables: the reveal is physically irreversible).  The row's content
  — the win must survive an undoable-nowhere move — is therefore
  real, not an undo-replay in disguise.  At `g2`'s raised successor
  every worry-back of the moved card lands AWAY from its own former
  seat (`g2_no_reseat`, the 59-base census): the emptied-pile arm is
  exactly the no-return-the-seat shape.

* **The compliance window bans only REAL moves** — every arm of
  `Move.groundBlocked` is inhabited by a live move at the corner
  states: the waste-park on `c` (`g1_park_live`, channel A's subject),
  the two-deep run-park onto `c` (`g1_runpark_live` — the maximal
  `hsafe`-consistent streak [♣6, ♦5] exactly), the c-suit worry-back
  (`g1_worry_live`, channel B), and c's own relocation
  (`g1_relocate_live` — the dig-without-raise shape).  The one-step
  move census at `g1` (below) shows all four among the offered moves.

* **Each ban has its canonical replacement** — the channel-A
  substitutes are live at razor's-edge `safeToFound` heights (every
  conjunct tight): the waste tenant ♠6 stands next-up for a pure
  waste raise (`g1_tenant_raise_live`); the parked streak's
  raise-channel runs END-TO-END through the foundations
  (`g1_streak_raise_chain` — the run parks on c, then each parked
  card leaves by its own `tabToFound`, the two-rank descent the
  route docstrings describe); the substitute raises COMMUTE with the
  rung pass in both orders (`g1_diamond`).

* **The relocation's dig-parity** — the raise digs the source pile
  exactly as the sideways relocation does (`g1_dig_parity`: the two
  successors agree at pile p0), the geometric fact behind the
  residue's relocation-absorption route.

* **The falsity hunt (bounded, honest)** — the full verdict question
  (`WinFrom st ∧ ¬ WinFrom s₁`) is outside `decide` reach at 52-card
  states; the bounded-DFS probes (`canWinB 2` at both corner states
  and the raised successor) are recorded below as the hunt's
  boundary, not as a refutation.  No countermodel to the row was
  found this session, and the battery's design goal was the
  opposite: to make each substitution the residue's route names a
  DECIDED fact at the corner.

Axioms: permitted `[propext, Classical.choice, Quot.sound]`; the
pins at the end show the exhibit theorems at `[propext, Quot.sound]`
or lighter (the `decide` rows are axiom-free, the commitment
composition rides the LANDED `[propext, Quot.sound]` tables).
-/

namespace OrigGround

/-! ## Cards -/

/-- Spades. -/
private def S (r : Rank) : Card := ⟨Suit.spade, r⟩
/-- Hearts. -/
private def H (r : Rank) : Card := ⟨Suit.heart, r⟩
/-- Diamonds. -/
private def D (r : Rank) : Card := ⟨Suit.diamond, r⟩
/-- Clubs. -/
private def C (r : Rank) : Card := ⟨Suit.club, r⟩

/-! ## The state-equality instrument (DEDUP-marked: the same `decSt`
re-derivation as `OrigKingAnchorWitness`; self-contained at this
base). -/

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

/-! ## G1 — the reveal-seat arm -/

/-- Arm 1's piles: the corner tip (♥7 over the hidden ♦K), the
worry-back target (♣7 — a black six-index top for the c-suit prefix
card ♥6), the relocation target (♠8 — a black seven-index top for
♥7 itself), and the maximal streak run [♣6, ♦5] on pile 3. -/
private def g1Piles : Anchor → Pile
  | .p0 => ⟨[D .king], [H .seven]⟩
  | .p1 => ⟨[], [C .seven]⟩
  | .p2 => ⟨[], [S .eight]⟩
  | .p3 => ⟨[], [C .six, D .five]⟩
  | .p4 => ⟨[], []⟩
  | .p5 => ⟨[], []⟩
  | .p6 => ⟨[], []⟩

/-- The stock bulk of arm 1 (draw order chosen for the census only). -/
private def g1Stock : List Card :=
  [H .eight, H .nine, H .ten, H .jack, H .queen, H .king,
   D .six, D .seven, D .eight, D .nine, D .ten, D .jack, D .queen,
   S .seven, S .nine, S .ten, S .jack, S .queen, S .king,
   C .eight, C .nine, C .ten, C .jack, C .queen, C .king]

/-- **The arm-1 corner state.** -/
def g1 : State :=
  { found := fun s =>
      match s with
      | .heart => [H .ace, H .two, H .three, H .four, H .five, H .six]
      | .diamond => [D .ace, D .two, D .three, D .four]
      | .spade => [S .ace, S .two, S .three, S .four, S .five]
      | .club => [C .ace, C .two, C .three, C .four, C .five]
    piles := g1Piles
    stock := g1Stock
    waste := [S .six]
    drawStep := 1 }

/-- The raised successor of arm 1: ♥7 founded, the ♦K reveal seated. -/
def g1r : State :=
  { found := fun s =>
      match s with
      | .heart => [H .ace, H .two, H .three, H .four, H .five, H .six,
        H .seven]
      | .diamond => [D .ace, D .two, D .three, D .four]
      | .spade => [S .ace, S .two, S .three, S .four, S .five]
      | .club => [C .ace, C .two, C .three, C .four, C .five]
    piles := fun a =>
      match a with
      | .p0 => ⟨[], [D .king]⟩
      | .p1 => ⟨[], [C .seven]⟩
      | .p2 => ⟨[], [S .eight]⟩
      | .p3 => ⟨[], [C .six, D .five]⟩
      | .p4 => ⟨[], []⟩
      | .p5 => ⟨[], []⟩
      | .p6 => ⟨[], []⟩
    stock := g1Stock
    waste := [S .six]
    drawStep := 1 }

/-! ### The WF census decide -/

/-- **`g1` is conservative and well-formed** — every one of the 52
cards appears exactly once, foundations are honest prefixes, each
face-up run sits, draw step 1. -/
theorem g1_wf : g1.WF := by
  refine ⟨?_, ?_, ?_, by decide⟩
  · intro σ
    refine ⟨(g1.found σ).length, ?_⟩
    cases σ <;> decide
  · intro a
    cases a <;> decide
  · intro c hc
    have hball : (Card.universe.all fun c => decide (g1.cardCount c = 1)) = true := by
      decide
    have hb := List.all_eq_true.mp hball
    exact of_decide_eq_true (hb c hc)

/-! ### The guard bundle -/

/-- **Safe at the razor's edge** — every `safeToFound` conjunct holds
with equality (the same-colour suits at r−2, the opposite-colour at
r−1 exactly). -/
theorem g1_safe : safeToFound g1 (H .seven) = true := by decide

/-- The rung: ♥7 is next-up for its foundation. -/
theorem g1_nextUp : g1.nextUp (H .seven) = true := by decide

/-- The seat: ♥7 tops pile 0, the sole face-up card of its pile. -/
theorem g1_top : g1.pileOfTop (H .seven) = some Anchor.p0 := by decide

theorem g1_bare : chop (g1.piles Anchor.p0).faceUp = [] := by decide

theorem g1_hidden : (g1.piles Anchor.p0).hidden ≠ [] := by decide

/-- The revealed boundary card is NOT a fitting base for ♥7 (same
colour — the `tabToFound_undo_under` corner does not swallow this
witness's shape). -/
theorem g1_reveal_unfit : canSitOn (H .seven) (D .king) = false := by decide

/-! ### The raise fires, and is a commitment -/

/-- **The arm-1 raise fires as stated.** -/
theorem g1_raise_fires : State.step g1 (Move.tabToFound (H .seven)) = some g1r := by
  decide

/-- **The arm-1 raise is a COMMITMENT** — a genuine `irreversibleAt`,
by composition of the LANDED hidden-total tables: the reveal strictly
drops the measure, and no legal move ever raises it.  The row's
dominance claims the win SURVIVES an undoable-nowhere move; this
exhibit certifies the corner has exactly that content. -/
theorem g1_raise_committed : irreversibleAt g1 (Move.tabToFound (H .seven)) :=
  irr_of_desc hiddenTotal (fun _ _ _ hstep => hiddenTotal_step hstep) g1_raise_fires
    (hiddenTotal_step_tabToFound_reveal g1_raise_fires g1_top g1_bare g1_hidden)

/-! ### The channel-A/B shapes are all inhabited -/

/-- **The waste-park on `c` (channel A's subject): LIVE.**  The black
♠6 fits ♥7 and is in hand. -/
theorem g1_park_live :
    (State.step g1 (Move.wasteToTab (S .six) (Sum.inr (H .seven)))).isSome = true := by
  decide

/-- **The park's substitute is live**: the same ♠6 stands at its own
foundation index (r−1), a pure waste raise. -/
theorem g1_tenant_raise_live :
    (State.step g1 (Move.wasteToFound (S .six))).isSome = true := by
  decide

/-- **The two-deep run-park onto `c` (the maximal `hsafe`-consistent
streak): LIVE** — the streak [♣6, ♦5] arrives on c's seat as one
first-class run move. -/
theorem g1_runpark_live :
    (State.step g1 (Move.tabToTab (C .six) (Sum.inr (H .seven)))).isSome = true := by
  decide

/-- **The streak's raise-channel runs end-to-end**: park the run on
c, then every parked card leaves by its own `tabToFound` — ♦5 from
the top, then ♣6 exposed beneath it.  This is the residue's
channel-A substitution in action, each parked card exactly one below
its own foundation's standing height. -/
theorem g1_streak_raise_chain :
    (((State.step g1 (Move.tabToTab (C .six) (Sum.inr (H .seven)))).bind fun s =>
        State.step s (Move.tabToFound (D .five))).bind fun s =>
        State.step s (Move.tabToFound (C .six))).isSome = true := by
  decide

/-- **The c-suit worry-back (channel B's subject): LIVE** — the ♥6
(the suit's top, the card just under the rung) worries down onto the
black ♣7. -/
theorem g1_worry_live :
    (State.step g1 (Move.foundToTab (H .six) (Sum.inr (C .seven)))).isSome = true := by
  decide

/-- **c's own relocation (the dig-without-raise shape): LIVE** — ♥7
moves sideways onto the ♠8. -/
theorem g1_relocate_live :
    (State.step g1 (Move.tabToTab (H .seven) (Sum.inr (S .eight)))).isSome = true := by
  decide

/-- **The relocation's dig-parity** — the raise and the sideways
relocation leave the source pile IDENTICALLY (the ♦K reveal seats
either way): the relocation buys no digging the raise does not. -/
theorem g1_dig_parity :
    ((State.step g1 (Move.tabToFound (H .seven))).map fun s => s.piles Anchor.p0) =
    ((State.step g1 (Move.tabToTab (H .seven) (Sum.inr (S .eight)))).map
      fun s => s.piles Anchor.p0) := by
  decide

/-! ### The substitute commutes with the rung pass -/

/-- **The diamond**: raise c first then the tenant, tenant first then
c — both orders are legal and land at the SAME state.  The
channel-A substitute never blocks the rung pass, in either order. -/
theorem g1_diamond :
    ((State.step g1 (Move.tabToFound (H .seven))).bind fun s =>
        State.step s (Move.wasteToFound (S .six))) =
    ((State.step g1 (Move.wasteToFound (S .six))).bind fun s =>
        State.step s (Move.tabToFound (H .seven))) := by
  decide

/-! ## G2 — the emptied-pile arm -/

/-- Arm 2's piles: the non-king ♠6 is the WHOLE of pile 0 (no hidden
cards), the relocation target ♥7, and the worry-back target ♥6. -/
private def g2Piles : Anchor → Pile
  | .p0 => ⟨[], [S .six]⟩
  | .p1 => ⟨[], [H .seven]⟩
  | .p2 => ⟨[], [H .six]⟩
  | .p3 => ⟨[], []⟩
  | .p4 => ⟨[], []⟩
  | .p5 => ⟨[], []⟩
  | .p6 => ⟨[], []⟩

private def g2Stock : List Card :=
  [H .eight, H .nine, H .ten, H .jack, H .queen, H .king,
   S .seven, S .eight, S .nine, S .ten, S .jack, S .queen, S .king,
   C .four, C .five, C .six, C .seven, C .eight, C .nine, C .ten,
   C .jack, C .queen, C .king,
   D .five, D .six, D .seven, D .eight, D .nine, D .ten, D .jack,
   D .queen, D .king]

/-- **The arm-2 corner state.** -/
def g2 : State :=
  { found := fun s =>
      match s with
      | .spade => [S .ace, S .two, S .three, S .four, S .five]
      | .club => [C .ace, C .two, C .three]
      | .heart => [H .ace, H .two, H .three, H .four]
      | .diamond => [D .ace, D .two, D .three, D .four]
    piles := g2Piles
    stock := g2Stock
    waste := [H .five]
    drawStep := 1 }

/-- The raised successor of arm 2: ♠6 founded, pile 0 fully EMPTY. -/
def g2r : State :=
  { found := fun s =>
      match s with
      | .spade => [S .ace, S .two, S .three, S .four, S .five, S .six]
      | .club => [C .ace, C .two, C .three]
      | .heart => [H .ace, H .two, H .three, H .four]
      | .diamond => [D .ace, D .two, D .three, D .four]
    piles := fun a =>
      match a with
      | .p0 => ⟨[], []⟩
      | .p1 => ⟨[], [H .seven]⟩
      | .p2 => ⟨[], [H .six]⟩
      | .p3 => ⟨[], []⟩
      | .p4 => ⟨[], []⟩
      | .p5 => ⟨[], []⟩
      | .p6 => ⟨[], []⟩
    stock := g2Stock
    waste := [H .five]
    drawStep := 1 }

/-- **`g2` is conservative and well-formed.** -/
theorem g2_wf : g2.WF := by
  refine ⟨?_, ?_, ?_, by decide⟩
  · intro σ
    refine ⟨(g2.found σ).length, ?_⟩
    cases σ <;> decide
  · intro a
    cases a <;> decide
  · intro c hc
    have hball : (Card.universe.all fun c => decide (g2.cardCount c = 1)) = true := by
      decide
    have hb := List.all_eq_true.mp hball
    exact of_decide_eq_true (hb c hc)

/-- The arm-2 guard bundle: safety (each conjunct tight), rung, seat,
bare floor, and the non-king corner. -/
theorem g2_safe : safeToFound g2 (S .six) = true := by decide

theorem g2_nextUp : g2.nextUp (S .six) = true := by decide

theorem g2_top : g2.pileOfTop (S .six) = some Anchor.p0 := by decide

theorem g2_bare : chop (g2.piles Anchor.p0).faceUp = [] := by decide

theorem g2_hidden : (g2.piles Anchor.p0).hidden = [] := by decide

theorem g2_nonking : (S .six).rank ≠ Rank.king := by decide

/-- **The arm-2 raise fires as stated.** -/
theorem g2_raise_fires : State.step g2 (Move.tabToFound (S .six)) = some g2r := by
  decide

/-- **The raised card comes down only AWAY from its seat** — no
`foundToTab ♠6 b` re-seats the card at its own former pile: pile 0
stays empty through every one-move worry-back (the 59-base census;
the moves DO fire onto the fitting foreign tops ♥7/♥6 — the worry
freedom, exactly not an undo). -/
theorem g2_no_reseat :
    (Base.universe.filter fun b =>
      match State.step g2r (Move.foundToTab (S .six) b) with
      | some s => s.piles Anchor.p0 == g2.piles Anchor.p0
      | none => false) = [] := by
  decide

/-- The channel-A pair at arm 2: the waste tenant parks on c, and its
substitute raise is live (♥5 at its own index r−1). -/
theorem g2_park_live :
    (State.step g2 (Move.wasteToTab (H .five) (Sum.inr (S .six)))).isSome = true := by
  decide

theorem g2_tenant_raise_live :
    (State.step g2 (Move.wasteToFound (H .five))).isSome = true := by
  decide

/-- The c-suit worry-back at arm 2: ♠5 (his suit's top) onto the red
♥6. -/
theorem g2_worry_live :
    (State.step g2 (Move.foundToTab (S .five) (Sum.inr (H .six)))).isSome = true := by
  decide

/-- c's own relocation at arm 2: ♠6 sideways onto the ♥7. -/
theorem g2_relocate_live :
    (State.step g2 (Move.tabToTab (S .six) (Sum.inr (H .seven)))).isSome = true := by
  decide

/-! ## The bounded falsity hunt

The bounded-DFS hunt record: neither corner state, nor the raised
successor, wins within the probed depths.  These are NOT refutations
of the row (the row needs `WinFrom st → WinFrom s₁`); they record
that no SHORT counter-play exists at the probes' reach — the hunt's
honest boundary, per the wave-23 protocol. -/

/-- info: false -/
#guard_msgs in
#eval canWinB 2 g1

/-- info: false -/
#guard_msgs in
#eval canWinB 2 g2

/-- info: false -/
#guard_msgs in
#eval canWinB 2 g1r

/-! ## The one-step move census -/

private def moveCase (st : State) (m : Move) : List Move :=
  match st.step m with
  | some _ => [m]
  | none => []

/-- The full legal-move census at `g1` — the four banned shapes (the
park, the run-park, the worry, the relocation) all appear among the
offered moves: the residue's compliance excludes genuinely playable
shapes, never ghosts. -/
private def g1Moves : List Move :=
  moveCase g1 .draw
  ++ (Card.universe.flatMap fun c =>
        moveCase g1 (.wasteToFound c) ++ moveCase g1 (.tabToFound c))
  ++ ((Card.universe.flatMap fun c => Anchor.all.map fun a => (c, Sum.inl a))
      ++ (Card.universe.flatMap fun c => Card.universe.map fun z => (c, Sum.inr z))
      ).flatMap fun cb =>
      match cb with
      | (c, b) =>
          moveCase g1 (.wasteToTab c b) ++ moveCase g1 (.foundToTab c b)
            ++ moveCase g1 (.tabToTab c b)

/-- info: 8 -/
#guard_msgs in
#eval g1Moves.length

/-! ## Axiom pins -/

#print axioms OrigGround.g1_wf
#print axioms OrigGround.g1_safe
#print axioms OrigGround.g1_nextUp
#print axioms OrigGround.g1_top
#print axioms OrigGround.g1_bare
#print axioms OrigGround.g1_hidden
#print axioms OrigGround.g1_reveal_unfit
#print axioms OrigGround.g1_raise_fires
#print axioms OrigGround.g1_raise_committed
#print axioms OrigGround.g1_park_live
#print axioms OrigGround.g1_tenant_raise_live
#print axioms OrigGround.g1_runpark_live
#print axioms OrigGround.g1_streak_raise_chain
#print axioms OrigGround.g1_worry_live
#print axioms OrigGround.g1_relocate_live
#print axioms OrigGround.g1_dig_parity
#print axioms OrigGround.g1_diamond
#print axioms OrigGround.g2_wf
#print axioms OrigGround.g2_safe
#print axioms OrigGround.g2_nextUp
#print axioms OrigGround.g2_top
#print axioms OrigGround.g2_bare
#print axioms OrigGround.g2_hidden
#print axioms OrigGround.g2_nonking
#print axioms OrigGround.g2_raise_fires
#print axioms OrigGround.g2_no_reseat
#print axioms OrigGround.g2_park_live
#print axioms OrigGround.g2_tenant_raise_live
#print axioms OrigGround.g2_worry_live
#print axioms OrigGround.g2_relocate_live

end OrigGround
