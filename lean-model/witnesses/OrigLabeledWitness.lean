import Orig.Fate
import Orig.Phase
import Orig.Combine

/-!
# The labeled corner, physically — dealt-initial rState-side data (F4)

The old `SuccLabeledWitness` addendum drove `rState`: a DEALT-INITIAL
engine state presenting SIX usable anchors, its split arguments
translating "to unseat, to stack, to phantom" — plus the label
corner's `toStack`/phantom anatomy (`wState_is_unlabeled`,
`unlabeled🎇_of_wFree`, the four gated class universals of :1162+).

The physical re-derivation records the dealt-initial side as DATA,
and the findings are sharper than the engine corner:

* **the naive-tip barrier**: at a staircase `Deal.WF` root, no
  anchor is ever empty, so the drawn `♠K` has NO tableau landing at
  all — `lU0_noLanding` proves the waste-king's arms dead
  everywhere at the naive tip;
* **the flip discipline blocks unseat windows**: a physical
  `ShufflePlay` window bars commitments at each step, and vacating a
  dealt anchor whose pile still holds hidden cards fires the
  automatic reveal — a permanent flip.  The only flip-free unseat at
  the root is founding pile 0's lone head — itself a promotion, a
  commitment, not a window move.  Hence the dealt corner presents
  the king exactly ONE landing, reached through TWO commitments
  (the ace promotion `tabToFound ♥A`, the pristine draw — both
  irreversibility rows cited, `draw_irreversible_pristine` at
  Orig/Phase.lean:930), not the old six-anchor window split;
* the unseated-tip corner (`lU1`) is the dealt-initial datum the
  reachability card's gates can consume: the full one-landing
  shape, decide-verified (`lU1_kingLands`) and census-pinned.

The label corner's `toStack`/phantom anatomy does not restate
physically: the physical vocabulary has no to-stack primitive, and
the labeled-class universals await the futures-count formulation
(the user decision, per the card's scope note).  Recorded as the
annotation of this file's fences, deliberately not stated as
theorems.

Axioms: permitted `[propext, Classical.choice, Quot.sound]`; the
pins at the end show `[propext, Quot.sound]` and less.  DEDUP NOTE:
`decSt` and the shape aliases below are the same local
re-derivations as families 1-3 (self-contained at this base, which
predates `Orig.Integrity`; see the report's overlap list).
-/

namespace OrigLabeled

/-! ## Cards and the dealt-initial corner -/

/-- Spades. -/
private def S (r : Rank) : Card := ⟨Suit.spade, r⟩
/-- Hearts. -/
private def H (r : Rank) : Card := ⟨Suit.heart, r⟩
/-- Diamonds. -/
private def D (r : Rank) : Card := ⟨Suit.diamond, r⟩
/-- Clubs. -/
private def C (r : Rank) : Card := ⟨Suit.club, r⟩

/-- The crafted staircase deal: pile 0's lone head is the heart ace
(the one flip-free unseat candidate, a promotion — no red/black
deuce tops exist anywhere for it to return to); every other head is
a jack, a ten, or the ace — nothing fits another head, so no
relocation window ever empties a pile; `♠K` sits at the head of the
stock. -/
def dLab : State.Deal where
  piles a :=
    match a with
    | .p0 => [H .ace]
    | .p1 => [D .five, S .jack]
    | .p2 => [C .nine, S .three, H .jack]
    | .p3 => [H .six, D .eight, C .four, D .jack]
    | .p4 => [S .two, H .nine, D .six, S .eight, C .jack]
    | .p5 => [C .seven, H .four, S .five, D .queen, C .two, D .king]
    | .p6 => [D .two, S .four, H .seven, D .nine, C .five, H .eight, C .king]
  stock :=
    [S .king, S .ace, S .six, S .seven, S .nine, S .ten, S .queen,
     H .two, H .three, H .five, H .ten, H .queen, H .king,
     D .ace, D .three, D .four, D .seven, D .ten,
     C .ace, C .three, C .six, C .eight, C .ten, C .queen]

/-- The dealt initial state. -/
def lT0 : State := State.initial dLab 1

/-- The naive tip: the pristine draw straight from the root — the
king is in hand, but no anchor is empty (the ace still heads pile
0). -/
def lU0 : State :=
  { found := fun _ => []
    piles := fun a => Pile.ofDealt (dLab.piles a)
    stock := [S .ace, S .six, S .seven, S .nine, S .ten, S .queen,
      H .two, H .three, H .five, H .ten, H .queen, H .king,
      D .ace, D .three, D .four, D .seven, D .ten,
      C .ace, C .three, C .six, C .eight, C .ten, C .queen]
    waste := [S .king]
    drawStep := 1 }

/-- The unseated tip: pile 0's ace has been founded (a promotion
commitment), everything else as dealt. -/
def lT1 : State :=
  { found := fun s =>
      match s with
      | .heart => [H .ace]
      | _ => []
    piles := fun a =>
      if a = Anchor.p0 then ⟨[], []⟩ else Pile.ofDealt (dLab.piles a)
    stock :=
      [S .king, S .ace, S .six, S .seven, S .nine, S .ten, S .queen,
       H .two, H .three, H .five, H .ten, H .queen, H .king,
       D .ace, D .three, D .four, D .seven, D .ten,
       C .ace, C .three, C .six, C .eight, C .ten, C .queen]
    waste := []
    drawStep := 1 }

/-- The unseated hand tip: the post-unseat pristine draw — the king
in hand over pile 0's vacancy. -/
def lU1 : State :=
  { found := fun s =>
      match s with
      | .heart => [H .ace]
      | _ => []
    piles := fun a =>
      if a = Anchor.p0 then ⟨[], []⟩ else Pile.ofDealt (dLab.piles a)
    stock := [S .ace, S .six, S .seven, S .nine, S .ten, S .queen,
      H .two, H .three, H .five, H .ten, H .queen, H .king,
      D .ace, D .three, D .four, D .seven, D .ten,
      C .ace, C .three, C .six, C .eight, C .ten, C .queen]
    waste := [S .king]
    drawStep := 1 }

/-- The dealt corner's one king landing: `♠K` onto the unseated
pile 0. -/
def lK : State :=
  { found := fun s =>
      match s with
      | .heart => [H .ace]
      | _ => []
    piles := fun a =>
      match a with
      | .p0 => ⟨[], [S .king]⟩
      | .p1 => ⟨[D .five], [S .jack]⟩
      | .p2 => ⟨[S .three, C .nine], [H .jack]⟩
      | .p3 => ⟨[C .four, D .eight, H .six], [D .jack]⟩
      | .p4 => ⟨[S .eight, D .six, H .nine, S .two], [C .jack]⟩
      | .p5 => ⟨[C .two, D .queen, S .five, H .four, C .seven], [D .king]⟩
      | .p6 => ⟨[H .eight, C .five, D .nine, H .seven, S .four, D .two], [C .king]⟩
    stock := [S .ace, S .six, S .seven, S .nine, S .ten, S .queen,
      H .two, H .three, H .five, H .ten, H .queen, H .king,
      D .ace, D .three, D .four, D .seven, D .ten,
      C .ace, C .three, C .six, C .eight, C .ten, C .queen]
    waste := []
    drawStep := 1 }

/-! ## The local instruments (DEDUP-marked: the same re-derivations
as families 1-3; nothing imported from `Orig.Integrity`) -/

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

private theorem canPlace_inl_eq (st : State) (c : Card) (a : Anchor) :
    st.canPlace c (.inl a) = ((st.piles a).isEmpty && decide (c.rank = .king)) := rfl

private theorem canPlace_inr_eq (st : State) (c z : Card) :
    st.canPlace c (.inr z) = (match st.pileOfTop z with
      | some _ => canSitOn c z | none => false) := rfl

private theorem step_w2t_eq (st : State) (c : Card) (b : Base) :
    st.step (.wasteToTab c b) =
      (if st.wasteIs c && st.canPlace c b then
        match st.waste with
        | _ :: ws => some { st.putCard c b with waste := ws }
        | [] => none
      else none) := rfl

/-! ## The deal and the two commitments -/

/-- **The deal is well-formed** — the staircase sizes, 24 in stock,
52 cards each exactly once.  [axioms: none — census decide.] -/
theorem dLab_wf : dLab.WF := by
  refine ⟨?_, rfl, ?_⟩
  · intro a
    cases a <;> rfl
  · intro c hc
    have hball : (Card.universe.all fun c =>
        decide ((((Anchor.all.map dLab.piles).flatMap id ++ dLab.stock).filter
          fun x => decide (x = c)).length = 1)) = true := by
      decide
    have hb := List.all_eq_true.mp hball
    exact of_decide_eq_true (hb c hc)

/-- The pristine draw from the root puts `♠K` in hand, and it is a
COMMITMENT (the committed phase row cited). -/
theorem lT0_draw : lT0.step .draw = some lU0 := by decide

theorem lT0_draw_irreversible : irreversibleAt lT0 .draw :=
  draw_irreversible_pristine (by decide) (by decide) rfl

/-- The one flip-free unseat candidate is a PROMOTION, not a window
move: pile 0's lone head founds, emptying the pile. -/
theorem lT0_aceStep : lT0.step (.tabToFound (H .ace)) = some lT1 := by decide

/-- The post-unseat pristine draw puts the king in hand over the
vacancy — again a commitment. -/
theorem lT1_draw : lT1.step .draw = some lU1 := by decide

theorem lT1_draw_irreversible : irreversibleAt lT1 .draw :=
  draw_irreversible_pristine (by decide) (by decide) rfl

/-- **The dealt corner's ONE king landing**, decide-verified —
`♠K` onto the unseated pile 0. -/
theorem lU1_kingLands :
    lU1.step (.wasteToTab (S .king) (.inl Anchor.p0)) = some lK := by decide

/-! ## The naive-tip barrier -/

/-- At the naive tip `lU0` NO pile is empty. -/
private theorem lU0_occupied (a : Anchor) : (lU0.piles a).isEmpty = false := by
  cases a <;> decide

/-- **THE NAIVE-TIP BARRIER (verdict)**: at the dealt root drawn
naively, the in-hand `♠K` has NO tableau landing — every anchor is
occupied and kings sit on no card.  The old six-anchor window split
has no physical counterpart at dealt roots; the king waits for the
ace-vacancy, which itself costs a promotion commitment.  [axioms:
none — per-kind case analysis.] -/
theorem lU0_noLanding (c : Card) (b : Base) (t : State)
    (h : lU0.step (.wasteToTab c b) = some t) : False := by
  rw [step_w2t_eq] at h
  have hcnd : (lU0.wasteIs c && lU0.canPlace c b) = true := by
    cases hc : (lU0.wasteIs c && lU0.canPlace c b) with
    | true => rfl
    | false => rw [hc] at h; simp at h
  rw [Bool.and_eq_true] at hcnd
  obtain ⟨hw, hp⟩ := hcnd
  have hw2 : lU0.wasteIs c = decide (S .king = c) := State.wasteIs_cons rfl c
  rw [hw2] at hw
  have hck : c = S .king := (of_decide_eq_true hw).symm
  subst hck
  cases b with
  | inl a =>
      rw [canPlace_inl_eq, lU0_occupied a] at hp
      simp at hp
  | inr z =>
      rw [canPlace_inr_eq] at hp
      cases hpt : lU0.pileOfTop z with
      | none => rw [hpt] at hp; simp at hp
      | some k =>
          rw [hpt] at hp
          obtain ⟨h1, -⟩ := (canSitOn_eq (S .king) z).mp hp
          have h2 : 12 + 1 = z.rank.toIdx := h1
          have hz := Rank.toIdx_lt z.rank
          omega

end OrigLabeled

/-! ## The census battery (deterministic `#eval` probes) -/

namespace OrigLabeled

private def moveCase (st : State) (m : Move) : List (Move × State) :=
  match st.step m with
  | some t => [(m, t)]
  | none => []

/-- The full move enumeration — the census instrument. -/
private def allMoves (st : State) : List (Move × State) :=
  moveCase st .draw
  ++ (Card.universe.flatMap fun c =>
        moveCase st (.wasteToFound c) ++ moveCase st (.tabToFound c))
  ++ ((Card.universe.flatMap fun c => Anchor.all.map fun a => (c, Sum.inl a))
      ++ (Card.universe.flatMap fun c => Card.universe.map fun z => (c, Sum.inr z))
      ).flatMap fun cb =>
      match cb with
      | (c, b) =>
          moveCase st (.wasteToTab c b) ++ moveCase st (.foundToTab c b)
            ++ moveCase st (.tabToTab c b)

/-- info: 2 -/
#guard_msgs in
#eval (allMoves lT0).length

/-- info: 2 -/
#guard_msgs in
#eval (allMoves lU0).length

/-- info: 3 -/
#guard_msgs in
#eval (allMoves lT1).length

/-- info: 4 -/
#guard_msgs in
#eval (allMoves lU1).length

/-- info: 1 -/
#guard_msgs in
#eval (allMoves lK).length

/- Axiom pins for the battery. -/
#print axioms OrigLabeled.dLab_wf
#print axioms OrigLabeled.lT0_draw
#print axioms OrigLabeled.lT0_draw_irreversible
#print axioms OrigLabeled.lT0_aceStep
#print axioms OrigLabeled.lT1_draw
#print axioms OrigLabeled.lT1_draw_irreversible
#print axioms OrigLabeled.lU1_kingLands
#print axioms OrigLabeled.lU0_noLanding

end OrigLabeled


