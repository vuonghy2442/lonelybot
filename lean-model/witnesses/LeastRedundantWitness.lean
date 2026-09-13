import Klondike.Dominance

/-!
# The least-redundant-stack witness — the staged §5.2's hypotheses dissected

The staged `least_redundantStack_dominant` (no `hsafe`) claimed: with ≥3
redundant stackables, stacking the lowest is dominant.  The three
stackables sit in three distinct suits (a suit's foundation admits at
most one stackable card: its height), so the fourth suit's height is
unconstrained, and the §5.1 safety of the lowest stackable does not
follow — the danger card of the unconstrained suit (rank r−1, opposite
colour: the unique card class that can ever sit on `c`) may be live.

This file machine-checks the countermodel's SKELETON on a concrete
state: heights ♠=12, ♥=11, ♣=6, ♦=8 — the redundant stackables ♠K, ♥Q,
♦9 (toIdx = their suit's height, three distinct suits, exactly three).
The lowest is `c = ♦9` (toIdx 8), and safety fails exactly on the
fourth suit: `safeToStack` demands ♣ ≥ 7 (opposite colour to ♦) but
♣ = 6.  The danger card ♣8 (black 8, toIdx 7) is live (♣=6 < 7) and
its ONLY tableau seat is ♦9 (the other red 9, ♥9, and the other black
8, ♠8, are on the foundation).  ♣8 sits on the hidden boundary ♣7 of
pile p1; to win, ♣7 must be revealed — and the reveal needs a card
sitting on the boundary, so ♣8 must move first, onto ♦9.  The state is
WF and 17 moves from the win (all `decide`-verified below).

STATUS OF THE FULL REFUTATION (the successor's unsolvability): OPEN.
Two concrete state designs were analysed and REFUTED AS COUNTERMODELS
by the worry-unwinding web — each state satisfying the hypotheses has
its free stackables act as peel-hosts: a black-J cover of a black Q
is peeled onto the free red-Q stackable (e.g. `pilePile ♣J (inr ♥Q)`),
freeing the Q; the ♥-unwinding then descends (♥J-worry onto the freed
♣Q, ♥10-worry onto the transited ♣J, ♥9-worry onto a free ♣10),
returning a live red 9 to the board and reopening ♣8's transit.  The
machine-checked `¬ dominantAt` needs a state whose towers are peel-free
(no tower top or interior root in the tenant classes of the free
stackables and the anchor-shuffled kings) — the third design
(heights ♠5/♥7/♣11/♦8, c = ♥8, danger ♠7) blocks every unwinding seed
but needs its own web audit.  The `+hsafe` repair in Dominance.lean is
unaffected: the analytic gap (the 4th-suit safety conjunct) is exactly
what the added hypothesis supplies, and B&G's own proof of the
worry-back corollary goes through the §5.1 core.
-/

namespace LeastRedundant

/-- Spades. -/
private def S (r : Rank) : Card := ⟨Suit.spade, r⟩
/-- Hearts. -/
private def H (r : Rank) : Card := ⟨Suit.heart, r⟩
/-- Diamonds. -/
private def D (r : Rank) : Card := ⟨Suit.diamond, r⟩
/-- Clubs. -/
private def C (r : Rank) : Card := ⟨Suit.club, r⟩

/-- The witness deal: the three stackables at their piles' heads, the
♣7/♣8 pair on p1, the towers on p4 (♥K←♣Q←♣J), p5 (♦K←♦Q←♣9←♦J←♦10),
p6 (♣K←♣10), and the already-climbed low cards filling the remaining
list slots. -/
private def wDeal : Deal where
  piles := fun a =>
    match a with
    | .p0 => [S .king]
    | .p1 => [C .seven, C .eight]
    | .p2 => [H .queen, S .ace, H .ace]
    | .p3 => [D .nine, S .two, H .two, D .ace]
    | .p4 => [H .king, C .queen, C .jack, S .three, H .three]
    | .p5 => [D .king, D .queen, C .nine, D .jack, D .ten, D .two]
    | .p6 => [C .king, C .ten, S .four, H .four, C .ace, C .two, C .three]
  stock := [S .five, S .six, S .seven, S .eight, S .nine, S .ten, S .jack, S .queen,
            H .five, H .six, H .seven, H .eight, H .nine, H .ten, H .jack,
            C .four, C .five, C .six,
            D .three, D .four, D .five, D .six, D .seven, D .eight]

/-- The visible seating: 14 edges (♣7 is hidden under ♣8). -/
private def wTop : Base → Option Card
  | Sum.inl Anchor.p0 => some (S .king)
  | Sum.inl Anchor.p2 => some (H .queen)
  | Sum.inl Anchor.p3 => some (D .nine)
  | Sum.inl Anchor.p4 => some (H .king)
  | Sum.inl Anchor.p5 => some (D .king)
  | Sum.inl Anchor.p6 => some (C .king)
  | Sum.inr (Card.mk (Suit.mk Color.black true) Rank.seven) => some (C .eight)
  | Sum.inr (Card.mk (Suit.mk Color.red false) Rank.king) => some (C .queen)
  | Sum.inr (Card.mk (Suit.mk Color.black true) Rank.queen) => some (C .jack)
  | Sum.inr (Card.mk (Suit.mk Color.red true) Rank.king) => some (D .queen)
  | Sum.inr (Card.mk (Suit.mk Color.red true) Rank.queen) => some (C .nine)
  | Sum.inr (Card.mk (Suit.mk Color.black true) Rank.nine) => some (D .jack)
  | Sum.inr (Card.mk (Suit.mk Color.red true) Rank.jack) => some (D .ten)
  | Sum.inr (Card.mk (Suit.mk Color.black true) Rank.king) => some (C .ten)
  | _ => none

/-- The edge list (for the finite injectivity check). -/
private def wEdges : List (Base × Card) :=
  [(Sum.inl Anchor.p0, S .king), (Sum.inr (C .seven), C .eight),
   (Sum.inl Anchor.p2, H .queen), (Sum.inl Anchor.p3, D .nine),
   (Sum.inl Anchor.p4, H .king), (Sum.inr (H .king), C .queen),
   (Sum.inr (C .queen), C .jack), (Sum.inl Anchor.p5, D .king),
   (Sum.inr (D .king), D .queen), (Sum.inr (D .queen), C .nine),
   (Sum.inr (C .nine), D .jack), (Sum.inr (D .jack), D .ten),
   (Sum.inl Anchor.p6, C .king), (Sum.inr (C .king), C .ten)]

private theorem wTop_mem {b : Base} {c : Card} (h : wTop b = some c) : (b, c) ∈ wEdges := by
  cases b with
  | inl a =>
      cases a <;> simp only [wTop, Option.some.injEq] at h
      all_goals first
      | exact absurd h (by simp)
      | subst h
        simp [wEdges, S, H, D, C, Suit.spade, Suit.heart, Suit.diamond, Suit.club]
  | inr cc =>
      rcases cc with ⟨⟨col, pr⟩, rk⟩
      cases col <;> cases pr <;> cases rk <;> simp only [wTop, Option.some.injEq] at h
      all_goals first
      | exact absurd h (by simp)
      | subst h
        simp [wEdges, S, H, D, C, Suit.spade, Suit.heart, Suit.diamond, Suit.club]

private theorem wEdges_base_unique : ∀ p ∈ (wEdges : List (Base × Card)),
    ∀ q ∈ (wEdges : List (Base × Card)), p.2 = q.2 → p.1 = q.1 := by decide

private theorem wTop_inj : ∀ (b₁ b₂ : Base) (c : Card),
    wTop b₁ = some c → wTop b₂ = some c → b₁ = b₂ := by
  intro b₁ b₂ c h₁ h₂
  exact wEdges_base_unique (b₁, c) (wTop_mem h₁) (b₂, c) (wTop_mem h₂) rfl

/-- The witness state: heights ♠12/♥11/♣6/♦8, p1 at depth 1, empty
stock (draw-1, but nothing to draw — the deck moves never fire). -/
private def wState : State where
  deal := wDeal
  board := { topOf := wTop, inj := wTop_inj }
  heights := fun s =>
    if s = Suit.spade then 12
    else if s = Suit.heart then 11
    else if s = Suit.club then 6
    else 8
  depths := fun a => if a = Anchor.p1 then 1 else 0
  stock := ⟨[], 0⟩
  drawStep := 1

/-! ## The witness is WF -/

/-- No edge target is foundation-passed. -/
private theorem wEdges_not_passed : ∀ p ∈ (wEdges : List (Base × Card)),
    ¬ (p.2.rank.toIdx < wState.heights p.2.suit) := by decide

/-- No edge target is ♣7 (the hidden boundary card). -/
private theorem wEdges_ne_seven : ∀ p ∈ (wEdges : List (Base × Card)),
    p.2 ≠ C .seven := by decide

private theorem wDeal_wf : wDeal.WF := by
  refine ⟨fun a => ?_, by decide, ?_⟩
  · cases a <;> decide
  · intro i j hi hj heq
    have hflat : (Anchor.all.flatMap wDeal.piles).length = 28 := by decide
    have hstock : wDeal.stock.length = 24 := by decide
    rw [List.length_append, hflat, hstock] at hi hj
    have hall : ∀ i ∈ List.range 52, ∀ j ∈ List.range 52,
        (Anchor.all.flatMap wDeal.piles ++ wDeal.stock)[i]? =
          (Anchor.all.flatMap wDeal.piles ++ wDeal.stock)[j]? → i = j := by decide
    exact hall i (List.mem_range.mpr hi) j (List.mem_range.mpr hj) heq

private theorem wState_wf : wState.WF := by
  refine State.WF.intro wDeal_wf ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro a
    cases a <;> decide
  · intro b c htop
    have hm : (b, c) ∈ wEdges := wTop_mem htop
    simp only [wEdges, List.mem_cons, Prod.mk.injEq] at hm
    rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | h
    · exact ⟨(Board.bottomOf_eq _ _ _).mpr htop, Or.inr rfl⟩
    · refine ⟨(Board.bottomOf_eq _ _ _).mpr htop, ?_⟩
      exact Or.inl ⟨Anchor.p1, [], [], rfl, Or.inl ⟨Anchor.p1, by decide⟩⟩
    · exact ⟨(Board.bottomOf_eq _ _ _).mpr htop, Or.inr rfl⟩
    · exact ⟨(Board.bottomOf_eq _ _ _).mpr htop, Or.inr rfl⟩
    · exact ⟨(Board.bottomOf_eq _ _ _).mpr htop, Or.inr rfl⟩
    · exact ⟨(Board.bottomOf_eq _ _ _).mpr htop, Or.inr ⟨by decide, by decide⟩⟩
    · refine ⟨(Board.bottomOf_eq _ _ _).mpr htop, ?_⟩
      exact Or.inl ⟨Anchor.p4, [H .king], [S .three, H .three], rfl,
        Or.inr (by decide)⟩
    · exact ⟨(Board.bottomOf_eq _ _ _).mpr htop, Or.inr rfl⟩
    · refine ⟨(Board.bottomOf_eq _ _ _).mpr htop, ?_⟩
      exact Or.inl ⟨Anchor.p5, [], [C .nine, D .jack, D .ten, D .two], rfl,
        Or.inr (by decide)⟩
    · refine ⟨(Board.bottomOf_eq _ _ _).mpr htop, ?_⟩
      exact Or.inl ⟨Anchor.p5, [D .king], [D .jack, D .ten, D .two], rfl,
        Or.inr (by decide)⟩
    · refine ⟨(Board.bottomOf_eq _ _ _).mpr htop, ?_⟩
      exact Or.inl ⟨Anchor.p5, [D .king, D .queen], [D .ten, D .two], rfl,
        Or.inr (by decide)⟩
    · refine ⟨(Board.bottomOf_eq _ _ _).mpr htop, ?_⟩
      exact Or.inl ⟨Anchor.p5, [D .king, D .queen, C .nine], [D .two], rfl,
        Or.inr (by decide)⟩
    · exact ⟨(Board.bottomOf_eq _ _ _).mpr htop, Or.inr rfl⟩
    · refine ⟨(Board.bottomOf_eq _ _ _).mpr htop, ?_⟩
      exact Or.inl ⟨Anchor.p6, [], [S .four, H .four, C .ace, C .two, C .three], rfl,
        Or.inr (by decide)⟩
    · exact absurd h (by simp)
  · intro c _
    rfl
  · intro c _
    rfl
  · intro c hc
    have hnone : wState.board.bottomOf c = none :=
      (Board.bottomOf_eq_none _ c).mpr (fun b hb' =>
        wEdges_not_passed (b, c) (wTop_mem hb') hc)
    refine ⟨by simp [State.isVis, hnone], rfl, ?_⟩
    intro a hca
    cases a with
    | p1 =>
        simp only [wState, State.hidden, wDeal] at hca
        rcases List.mem_cons.mp hca with rfl | h
        · exact absurd hc (by decide)
        · exact absurd h (by simp)
    | p0 => exact nomatch hca
    | p2 => exact nomatch hca
    | p3 => exact nomatch hca
    | p4 => exact nomatch hca
    | p5 => exact nomatch hca
    | p6 => exact nomatch hca
  · intro c hc a hca
    cases a with
    | p1 =>
        simp only [wState, State.hidden, wDeal] at hca
        rcases List.mem_cons.mp hca with h | h
        · exfalso
          rw [h] at hc
          cases hbb : wState.board.bottomOf (C .seven) with
          | none => simp [State.isVis, hbb] at hc
          | some b =>
              exact wEdges_ne_seven (b, C .seven)
                (wTop_mem ((Board.bottomOf_eq _ _ _).mp hbb)) rfl
        · exact absurd h (by simp)
    | p0 => exact nomatch hca
    | p2 => exact nomatch hca
    | p3 => exact nomatch hca
    | p4 => exact nomatch hca
    | p5 => exact nomatch hca
    | p6 => exact nomatch hca
  · intro s
    rcases s with ⟨col, pr⟩
    cases col <;> cases pr <;> decide
  · exact Nat.le_refl 0
  · exact Nat.zero_lt_one
  · exact ⟨fun i j hi _ _ => absurd hi (Nat.not_lt_zero i), fun c hc => nomatch hc⟩

/-! ## The staged hypotheses hold -/

/-- Exactly the three stackables, in three distinct suits, and the
lowest is ♦9. -/
example : wState.redundantStacks = [H .queen, S .king, D .nine] := by decide

example : (D .nine) ∈ wState.redundantStacks := by decide

example : ∀ c' ∈ wState.redundantStacks, (D .nine).rank.toIdx ≤ c'.rank.toIdx := by
  have hall : (wState.redundantStacks.all
      fun c' => decide ((D .nine).rank.toIdx ≤ c'.rank.toIdx)) = true := by decide
  exact fun c' hc' => of_decide_eq_true (List.all_eq_true.mp hall c' hc')

/-- Safety fails exactly on the unconstrained fourth suit (♣). -/
example : safeToStack wState (D .nine) = false := by decide

/-- The state is solvable: 17 moves, the spine being the reveal, the
transit through ♦9's seat, and the four climbs. -/
private def wPlay : List Move :=
  [Move.reveal (C .eight),
   Move.pilePile (C .eight) (Sum.inr (D .nine)),
   Move.pileStack (C .seven),
   Move.pileStack (C .eight),
   Move.pileStack (D .nine),
   Move.pileStack (D .ten),
   Move.pileStack (D .jack),
   Move.pileStack (C .nine),
   Move.pileStack (C .ten),
   Move.pileStack (C .jack),
   Move.pileStack (C .queen),
   Move.pileStack (H .queen),
   Move.pileStack (C .king),
   Move.pileStack (H .king),
   Move.pileStack (S .king),
   Move.pileStack (D .queen),
   Move.pileStack (D .king)]

private def wWin : State := (wState.run wPlay).getD wState

private theorem wRun : wState.run wPlay = some wWin := by
  have his : (wState.run wPlay).isSome = true := by decide
  cases h : wState.run wPlay with
  | none =>
      rw [h] at his
      simp at his
  | some w =>
      have hw : wWin = w := by
        show (wState.run wPlay).getD wState = w
        rw [h]
        rfl
      rw [hw]

private theorem wState_solvable : wState.solvableFrom :=
  ⟨wPlay, wWin, wRun, by decide⟩

end LeastRedundant
