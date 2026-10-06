import Orig.Fate
import Orig.Phase
import Orig.Combine

/-!
# The non-king twin-split, physically — and the ffState self-destruct datum

The old `NonKingWitness` drove the wave-21 non-king corner: `nkState`
with X = `♠6` in hand and the twin destinations `♥7`/`♦7` — two
live landing arms of one commit, every dodge blocked — plus the
"free-float" `ffState` three-split.

## The nkState re-cast (STRAIGHTFORWARD, per FUTURES-ORIG §7)

`dNK` is a real `Deal.WF` staircase deal (`dNK_wf`, by the
census-decide) with the spade six at the head of the stock, so the
pristine draw is a COMMITMENT (`draw_irreversible_pristine`,
Orig/Phase.lean:930 — the committed row cited, not re-proved) and
puts `♠6` in hand (the waste head at `nkU`).  The two twin dealt
heads `♥7` (pile 0) and `♦7` (pile 1) are the only red sevens on
any top; the crafted deck leaves no other fit for the spade six and
no ace or king top:

* both twin landings are live (`nk_landings`) and they are the ONLY
  waste-king arms (`nk_arms`) — the old twin-split's census lands
  verbatim;
* the old engine's closure could not carry the anchored `♠6`
  anywhere (its stack-only accommodation), keeping the two
  successors disjoint; **the physical orbit RELINKS them**: the
  landed `♠6` relocates between the twin tops by `tabToTab` with the
  reverse as the explicit returning play (`nk_relinked`) — the same
  orbit-join datum as family 2, now at the non-king twin;
* the sameFate reading of the pair is annotated (not proved here):
  both hand-stuck worlds are expected to be a DEAD PAIR per
  FUTURES-ORIG §5.1's grading note — the win-verdict census is the
  report's open item.

## The ffState self-destruct datum (route-map F3 verdict)

The old `ffState`'s three-way split ran through PROMOTION moves kept
inside accommodation windows — the engine's `deckPile` fresh-card
rows.  On the physical game a window bars them at each step: a
promotion (`tabToFound`) fixes its card forever (the committed
`tabToFound_fixed` machinery, Orig/Phase.lean:498) — a window that
promoted could never return its own origin.  The three-split is
therefore NOT re-derivable on physical windows; this file records
the datum and no ffState-style fence is stated.  The FLOAT HUNT (a
promotion-shaped excursion inside a window) needs a vocabulary hook
that exposes the found-monotonicity state to the window relation —
route-map §7's family-three stretch, out of this file's scope.

Axioms: permitted `[propext, Classical.choice, Quot.sound]`; the
pins at the end show `[propext, Quot.sound]` and less.  DEDUP NOTE:
`decSt` and the shape aliases below are the same local
re-derivations as in families 1-2 (self-contained at this base,
which predates `Orig.Integrity`; see the report's overlap list).
-/

namespace OrigNonKing

/-! ## Cards and the deal -/

/-- Spades. -/
private def S (r : Rank) : Card := ⟨Suit.spade, r⟩
/-- Hearts. -/
private def H (r : Rank) : Card := ⟨Suit.heart, r⟩
/-- Diamonds. -/
private def D (r : Rank) : Card := ⟨Suit.diamond, r⟩
/-- Clubs. -/
private def C (r : Rank) : Card := ⟨Suit.club, r⟩

/-- The crafted staircase deal: twin heads `♥7` and `♦7`, the spade
six at the head of the stock, jack tops, and the crown `♠K` blocking
the last pile's cross-fits. -/
def dNK : State.Deal where
  piles a :=
    match a with
    | .p0 => [H .seven]
    | .p1 => [H .two, D .seven]
    | .p2 => [C .nine, D .four, S .jack]
    | .p3 => [C .eight, H .three, H .eight, C .jack]
    | .p4 => [S .two, D .five, S .nine, D .ten, H .jack]
    | .p5 => [C .seven, S .three, H .five, C .four, S .eight, D .jack]
    | .p6 => [D .two, C .six, H .six, D .eight, C .two, H .nine, S .king]
  stock :=
    [S .six, S .ace, S .four, S .five, S .seven, S .ten, S .queen,
     H .ace, H .four, H .ten, H .queen, H .king,
     D .ace, D .three, D .six, D .nine, D .queen, D .king,
     C .ace, C .three, C .five, C .ten, C .queen, C .king]

/-- The dealt initial state (draw step 1). -/
def nkT0 : State := State.initial dNK 1

/-- The in-hand tip: the pristine draw has put `♠6` at the waste
head (the physical "X in hand"). -/
def nkU : State :=
  { found := fun _ => []
    piles := fun a => Pile.ofDealt (dNK.piles a)
    stock := [S .ace, S .four, S .five, S .seven, S .ten, S .queen,
      H .ace, H .four, H .ten, H .queen, H .king,
      D .ace, D .three, D .six, D .nine, D .queen, D .king,
      C .ace, C .three, C .five, C .ten, C .queen, C .king]
    waste := [S .six]
    drawStep := 1 }

/-- The first twin landing: the spade six onto the heart seven. -/
def nkS1 : State :=
  { found := fun _ => []
    piles := fun a =>
      match a with
      | .p0 => ⟨[], [H .seven, S .six]⟩
      | .p1 => ⟨[H .two], [D .seven]⟩
      | .p2 => ⟨[D .four, C .nine], [S .jack]⟩
      | .p3 => ⟨[H .eight, H .three, C .eight], [C .jack]⟩
      | .p4 => ⟨[D .ten, S .nine, D .five, S .two], [H .jack]⟩
      | .p5 => ⟨[S .eight, C .four, H .five, S .three, C .seven], [D .jack]⟩
      | .p6 => ⟨[H .nine, C .two, D .eight, H .six, C .six, D .two], [S .king]⟩
    stock := [S .ace, S .four, S .five, S .seven, S .ten, S .queen,
      H .ace, H .four, H .ten, H .queen, H .king,
      D .ace, D .three, D .six, D .nine, D .queen, D .king,
      C .ace, C .three, C .five, C .ten, C .queen, C .king]
    waste := []
    drawStep := 1 }

/-- The second twin landing: the spade six onto the diamond seven. -/
def nkS2 : State :=
  { found := fun _ => []
    piles := fun a =>
      match a with
      | .p0 => ⟨[], [H .seven]⟩
      | .p1 => ⟨[H .two], [D .seven, S .six]⟩
      | .p2 => ⟨[D .four, C .nine], [S .jack]⟩
      | .p3 => ⟨[H .eight, H .three, C .eight], [C .jack]⟩
      | .p4 => ⟨[D .ten, S .nine, D .five, S .two], [H .jack]⟩
      | .p5 => ⟨[S .eight, C .four, H .five, S .three, C .seven], [D .jack]⟩
      | .p6 => ⟨[H .nine, C .two, D .eight, H .six, C .six, D .two], [S .king]⟩
    stock := [S .ace, S .four, S .five, S .seven, S .ten, S .queen,
      H .ace, H .four, H .ten, H .queen, H .king,
      D .ace, D .three, D .six, D .nine, D .queen, D .king,
      C .ace, C .three, C .five, C .ten, C .queen, C .king]
    waste := []
    drawStep := 1 }

/-! ## The local instruments (DEDUP-marked: the same re-derivations
as families 1-2; nothing imported from `Orig.Integrity`) -/

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

/-! ## The deal and the commitment -/

/-- **The deal is well-formed** — the standard staircase sizes, 24 in
stock, and every one of the 52 cards exactly once.  [axioms: none —
census decide.] -/
theorem dNK_wf : dNK.WF := by
  refine ⟨?_, rfl, ?_⟩
  · intro a
    cases a <;> rfl
  · intro c hc
    have hball : (Card.universe.all fun c =>
        decide ((((Anchor.all.map dNK.piles).flatMap id ++ dNK.stock).filter
          fun x => decide (x = c)).length = 1)) = true := by
      decide
    have hb := List.all_eq_true.mp hball
    exact of_decide_eq_true (hb c hc)

/-- The pristine draw is a COMMITMENT (the committed phase row), and
it puts `♠6` in hand. -/
theorem nk_draw_commit : nkT0.step .draw = some nkU :=
  by decide

/-- The pristine draw commits — the committed row `draw_irreversible_pristine`
(Orig/Phase.lean:930), cited. -/
theorem nk_draw_irreversible : irreversibleAt nkT0 .draw :=
  draw_irreversible_pristine (by decide) (by decide) rfl

/-! ## The twin landings -/

/-- **The twin-split census lands verbatim: BOTH twin destinations
are live.**  [axioms: none — decide.] -/
theorem nk_landings :
    nkU.step (.wasteToTab (S .six) (.inr (H .seven))) = some nkS1 ∧
    nkU.step (.wasteToTab (S .six) (.inr (D .seven))) = some nkS2 := by
  refine ⟨by decide, by decide⟩

private theorem pileOfTop_some {st : State} {z : Card} {a : Anchor}
    (h : st.pileOfTop z = some a) : st.topOf a = some z := by
  have h' : firstWhere (fun a' => decide (st.topOf a' = some z)) Anchor.all = some a := h
  exact of_decide_eq_true
    (firstWhere_sound (fun a' => decide (st.topOf a' = some z)) h')

/-- `nkU`'s tops are exactly the seven dealt heads. -/
private theorem nkU_topChar (z : Card) (h : nkU.pileOfTop z ≠ none) :
    z = H .seven ∨ z = D .seven ∨ z = S .jack ∨ z = C .jack ∨
    z = H .jack ∨ z = D .jack ∨ z = S .king := by
  obtain ⟨a, ha⟩ : ∃ a, nkU.topOf a = some z := by
    cases hp : nkU.pileOfTop z with
    | none => exact absurd hp h
    | some a => exact ⟨a, pileOfTop_some hp⟩
  cases a with
  | p0 =>
      rw [show nkU.topOf Anchor.p0 = some (H .seven) from rfl] at ha
      exact Or.inl (Option.some.inj ha).symm
  | p1 =>
      rw [show nkU.topOf Anchor.p1 = some (D .seven) from rfl] at ha
      exact Or.inr (Or.inl (Option.some.inj ha).symm)
  | p2 =>
      rw [show nkU.topOf Anchor.p2 = some (S .jack) from rfl] at ha
      exact Or.inr (Or.inr (Or.inl (Option.some.inj ha).symm))
  | p3 =>
      rw [show nkU.topOf Anchor.p3 = some (C .jack) from rfl] at ha
      exact Or.inr (Or.inr (Or.inr (Or.inl (Option.some.inj ha).symm)))
  | p4 =>
      rw [show nkU.topOf Anchor.p4 = some (H .jack) from rfl] at ha
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Option.some.inj ha).symm))))
  | p5 =>
      rw [show nkU.topOf Anchor.p5 = some (D .jack) from rfl] at ha
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Option.some.inj ha).symm)))))
  | p6 =>
      rw [show nkU.topOf Anchor.p6 = some (S .king) from rfl] at ha
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Option.some.inj ha).symm)))))

/-- **The in-hand spade six's tableau arms are EXACTLY the two twin
landings**: the six is the only hand card, the only fits for it are
the twin red sevens, and every dealt anchor is occupied.  [axioms:
none — per-kind case analysis on the crafted shapes.] -/
theorem nk_arms (c : Card) (b : Base) (t : State)
    (h : nkU.step (.wasteToTab c b) = some t) :
    c = S .six ∧ (b = Sum.inr (H .seven) ∨ b = Sum.inr (D .seven)) := by
  rw [step_w2t_eq] at h
  have hcnd : (nkU.wasteIs c && nkU.canPlace c b) = true := by
    cases hc : (nkU.wasteIs c && nkU.canPlace c b) with
    | true => rfl
    | false => rw [hc] at h; simp at h
  rw [Bool.and_eq_true] at hcnd
  obtain ⟨hw, hp⟩ := hcnd
  have hw2 : nkU.wasteIs c = decide (S .six = c) := State.wasteIs_cons rfl c
  rw [hw2] at hw
  have hck : c = S .six := (of_decide_eq_true hw).symm
  refine ⟨hck, ?_⟩
  subst hck
  cases b with
  | inl a =>
      exfalso
      rw [canPlace_inl_eq] at hp
      have hio : (nkU.piles a).isEmpty = false := by cases a <;> decide
      rw [hio] at hp
      simp at hp
  | inr z =>
      rw [canPlace_inr_eq] at hp
      cases hpt : nkU.pileOfTop z with
      | none => rw [hpt] at hp; simp at hp
      | some k =>
          rw [hpt] at hp
          have hfit2 : canSitOn (S .six) z = true := hp
          rcases nkU_topChar z (by rw [hpt]; simp) with rfl | rfl | rfl | rfl | rfl | rfl | rfl
          · exact Or.inl rfl
          · exact Or.inr rfl
          · exact absurd hfit2 (by decide)
          · exact absurd hfit2 (by decide)
          · exact absurd hfit2 (by decide)
          · exact absurd hfit2 (by decide)
          · exact absurd hfit2 (by decide)

/-! ## The relink: the twin successors join in the physical orbit -/

/-- **THE RELINK FENCE (verdict): the physical orbit JOINS the twin
successors** — the landed spade six relocates between the twin tops
with the reverse as the explicit returning play, a `reversibleAtW`
pair, so `nkS1` and `nkS2` are `RevEqW`-related where the engine's
stack-only closure kept them apart.  The sameFate reading of the
pair is the annotated open item (expected DEAD PAIR per
FUTURES-ORIG §5.1).  [axioms: `[propext, Quot.sound]` at most — see
pins.] -/
theorem nk_relinked : RevEqW nkS1 nkS2 :=
  have hfwd : nkS1.step (.tabToTab (S .six) (.inr (D .seven))) = some nkS2 := by decide
  have hbwd : nkS2.step (.tabToTab (S .six) (.inr (H .seven))) = some nkS1 := by decide
  have hrfwd : nkS2.run [.tabToTab (S .six) (.inr (H .seven))] = some nkS1 := by
    show (match nkS2.step (.tabToTab (S .six) (.inr (H .seven))) with
      | some s' => s'.run [] | none => none) = some nkS1
    rw [hbwd]; rfl
  have hrbwd : nkS1.run [.tabToTab (S .six) (.inr (D .seven))] = some nkS2 := by
    show (match nkS1.step (.tabToTab (S .six) (.inr (D .seven))) with
      | some s' => s'.run [] | none => none) = some nkS2
    rw [hfwd]; rfl
  ⟨[.tabToTab (S .six) (.inr (D .seven))],
    .cons ⟨_, [.tabToTab (S .six) (.inr (H .seven))], hfwd, hrfwd⟩ hfwd (.nil _),
    [.tabToTab (S .six) (.inr (H .seven))],
    .cons ⟨_, [.tabToTab (S .six) (.inr (D .seven))], hbwd, hrbwd⟩ hbwd (.nil _)⟩

end OrigNonKing

/-! ## The census battery (deterministic `#eval` probes) -/

namespace OrigNonKing

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

/-- info: 1 -/
#guard_msgs in
#eval (allMoves nkT0).length

/-- info: 3 -/
#guard_msgs in
#eval (allMoves nkU).length

/-- info: 2 -/
#guard_msgs in
#eval (allMoves nkS1).length

/-- info: 2 -/
#guard_msgs in
#eval (allMoves nkS2).length

/- Axiom pins for the battery. -/
#print axioms OrigNonKing.dNK_wf
#print axioms OrigNonKing.nk_draw_commit
#print axioms OrigNonKing.nk_landings
#print axioms OrigNonKing.nk_arms
#print axioms OrigNonKing.nk_relinked

end OrigNonKing

