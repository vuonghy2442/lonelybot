import Klondike.Theorems

/-!
# The locked-pile witness — HISTORICAL after the reveal-rule repair

The dead-pile hole (the same one that repaired
`safe_pileStack_dominant`, see `DeadPileWitness.lean`) killed the B4
crux too as staged: when the stackable card `c` is *locked* (it sits
on its pile's hidden boundary), `pileStack c` stranded the boundary
forever under the PRE-2026-09-16 reveal rule — no tenant could ever
sit on it again, so the boundary card could never reach the
foundation and the successor was unsolvable — while the source state
won in three moves.

**The 2026-09-16 reveal-rule repair (the physical flip: `Move.reveal
a`, legal exactly when the boundary is bare) dissolves the lockedness
hole at this witness**: after ♦K stacks, the boundary flips and the
accommodation successor is solvable in two more moves (pinned below).
Whether the `+ hnotlock` guard can now be dropped from the repaired
crux (`solvable_of_pileStack`, still sorry'd) is a fresh question for
the library — the general locked case has an arbitrary boundary card,
not always a rung-ready king.  The state stays as a regression
witness; the tightness examples at the bottom record the historical
guard's motivation.
-/

namespace B4Locked

/-- Spades. -/
private def S (r : Rank) : Card := ⟨Suit.spade, r⟩
/-- Hearts. -/
private def H (r : Rank) : Card := ⟨Suit.heart, r⟩
/-- Diamonds. -/
private def D (r : Rank) : Card := ⟨Suit.diamond, r⟩
/-- Clubs. -/
private def C (r : Rank) : Card := ⟨Suit.club, r⟩

/-- The witness deal: all spades and hearts stacked on the foundations
already, ♦A..♦Q and ♣A..♣Q as the deal's stock, and pile p1 holding
exactly the two kings — ♣K hidden under the visible ♦K. -/
private def wDeal : Deal where
  piles := fun a =>
    match a with
    | .p0 => [S .ace]
    | .p1 => [C .king, D .king]
    | .p2 => [H .ace, S .two, H .two]
    | .p3 => [S .three, H .three, S .four, H .four]
    | .p4 => [S .five, H .five, S .six, H .six, S .seven]
    | .p5 => [H .seven, S .eight, H .eight, S .nine, H .nine, S .ten]
    | .p6 => [H .ten, S .jack, H .jack, S .queen, H .queen, S .king, H .king]
  stock := [D .ace, D .two, D .three, D .four, D .five, D .six, D .seven, D .eight,
            D .nine, D .ten, D .jack, D .queen,
            C .ace, C .two, C .three, C .four, C .five, C .six, C .seven, C .eight,
            C .nine, C .ten, C .jack, C .queen]

/-- The only visible card: ♦K, seated on the hidden ♣K. -/
private def wTop : Base → Option Card :=
  fun b => if b = Sum.inr (C .king) then some (D .king) else none

private theorem wTop_some {b : Base} {c : Card} (h : wTop b = some c) :
    c = D .king ∧ b = Sum.inr (C .king) := by
  by_cases hbc : b = Sum.inr (C .king)
  · refine ⟨?_, hbc⟩
    simp only [wTop, ite_eq_left hbc, Option.some.injEq] at h
    exact h.symm
  · simp only [wTop, ite_eq_right hbc] at h
    exact absurd h (by simp)

private theorem wTop_inj : ∀ (b₁ b₂ : Base) (c : Card),
    wTop b₁ = some c → wTop b₂ = some c → b₁ = b₂ := by
  intro b₁ b₂ c h₁ h₂
  rw [(wTop_some h₁).2, (wTop_some h₂).2]

/-- The witness state: ♠/♥ complete (13), ♦/♣ at 12, pile p1 at depth
1, empty stock, draw step 1. -/
private def wState : State where
  deal := wDeal
  board := { topOf := wTop, inj := wTop_inj }
  heights := fun s => if s = Suit.diamond ∨ s = Suit.club then 12 else 13
  depths := fun a => if a = Anchor.p1 then 1 else 0
  stock := ⟨[], 0⟩
  drawStep := 1

/-! ## Small inversion helpers -/

/-- A `canPlace` onto a card base demands that card visible. -/
private theorem canPlace_inr_isVis {st : State} {x c : Card}
    (h : st.canPlace x (Sum.inr c) = true) : st.isVis c = true := by
  have h2 : (decide (st.board.topOf (Sum.inr c) = none) &&
      (st.isVis c && canSitOn x c)) = true := h
  rw [Bool.and_eq_true, Bool.and_eq_true] at h2
  exact h2.2.1

/-- A `canMoveRun` onto a card base demands that card visible. -/
private theorem canMoveRun_inr_isVis {st : State} {x c : Card}
    (h : st.canMoveRun x (Sum.inr c) = true) : st.isVis c = true := by
  have h2 : (st.canPlace x (Sum.inr c) &&
      !(st.board.aboveOf x).contains c) = true := h
  rw [Bool.and_eq_true] at h2
  exact canPlace_inr_isVis h2.1

/-- The waste top is in the stock. -/
private theorem prev_mem {s : State} {x : Card} (hp : s.stock.prev = some x) :
    x ∈ s.stock.cards := by
  simp only [Cycle.prev] at hp
  split at hp
  · exact absurd hp (by simp)
  · exact List.mem_iff_getElem?.mpr ⟨s.stock.cursor - 1, hp⟩

/-- The pile a pileOfTopHidden points at really has `r` as boundary. -/
private theorem pileOfTopHidden_topHidden {s : State} {r : Card} {a : Anchor}
    (hp : s.pileOfTopHidden r = some a) : s.topHidden a = some r :=
  of_decide_eq_true ((findFirst_mem _ _ _ hp).2)

/-- A card base under a boundary belongs to that pile's deal slice. -/
private theorem hiddenBase_piles {s : State} {a : Anchor} {d : Card}
    (h : s.hiddenBase a = Sum.inr d) : d ∈ s.deal.piles a := by
  simp only [State.hiddenBase] at h
  cases hd : ((s.hidden a).reverse.drop 1).head? with
  | none =>
      rw [hd] at h
      exact absurd h (by simp)
  | some d' =>
      have h2 : (Sum.inr d' : Base) = Sum.inr d := by rw [hd] at h; exact h
      have hdd : d' = d := by injection h2
      rw [hdd] at hd
      cases hgt : (s.hidden a).getLast? with
      | none =>
          exfalso
          cases hs : s.hidden a with
          | nil => rw [hs] at hd; simp at hd
          | cons y t => rw [hs] at hgt; simp at hgt
      | some r =>
          obtain ⟨t, rest, hadj⟩ := hidden_parent_dealt hd hgt
          rw [hadj]
          simp

/-! ## The witness is WF -/

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
  refine ⟨wDeal_wf, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a
    cases a <;> decide
  · intro b c htop
    obtain ⟨hc, hb⟩ := wTop_some htop
    subst hc
    subst hb
    refine ⟨(Board.bottomOf_eq _ _ _).mpr htop, ?_⟩
    left
    exact ⟨Anchor.p1, [], [], rfl, Or.inl ⟨Anchor.p1, by decide⟩⟩
  · intro c _
    rfl
  · intro c _
    rfl
  · intro c hc
    have hnd : c ≠ D .king := by
      intro h
      rw [h] at hc
      exact absurd hc (by decide)
    refine ⟨?_, rfl, ?_⟩
    · cases hb : wState.board.bottomOf c with
      | none => simp [State.isVis, hb]
      | some b => exact absurd ((wTop_some ((Board.bottomOf_eq _ _ _).mp hb)).1) hnd
    · intro a hca
      cases a with
      | p1 =>
          have h1 : c ∈ [C .king] := hca
          rcases List.mem_cons.mp h1 with h | h
          · rw [h] at hc
            exact absurd hc (by decide)
          · exact absurd h (by simp)
      | p0 =>
          have h1 : c ∈ ([] : List Card) := hca
          exact nomatch h1
      | p2 =>
          have h1 : c ∈ ([] : List Card) := hca
          exact nomatch h1
      | p3 =>
          have h1 : c ∈ ([] : List Card) := hca
          exact nomatch h1
      | p4 =>
          have h1 : c ∈ ([] : List Card) := hca
          exact nomatch h1
      | p5 =>
          have h1 : c ∈ ([] : List Card) := hca
          exact nomatch h1
      | p6 =>
          have h1 : c ∈ ([] : List Card) := hca
          exact nomatch h1
  · intro c hc a hca
    have hck : c = D .king := by
      cases hb : wState.board.bottomOf c with
      | none => simp [State.isVis, hb] at hc
      | some b => exact (wTop_some ((Board.bottomOf_eq _ _ _).mp hb)).1
    rw [hck] at hca
    cases a with
    | p1 =>
        have h1 : D .king ∈ [C .king] := hca
        rcases List.mem_cons.mp h1 with h | h
        · exact absurd h (by decide)
        · exact absurd h (by simp)
    | p0 =>
        have h1 : D .king ∈ ([] : List Card) := hca
        exact nomatch h1
    | p2 =>
        have h1 : D .king ∈ ([] : List Card) := hca
        exact nomatch h1
    | p3 =>
        have h1 : D .king ∈ ([] : List Card) := hca
        exact nomatch h1
    | p4 =>
        have h1 : D .king ∈ ([] : List Card) := hca
        exact nomatch h1
    | p5 =>
        have h1 : D .king ∈ ([] : List Card) := hca
        exact nomatch h1
    | p6 =>
        have h1 : D .king ∈ ([] : List Card) := hca
        exact nomatch h1
  · intro s
    show (if s = Suit.diamond ∨ s = Suit.club then 12 else 13) ≤ 13
    split <;> omega
  · exact Nat.le_refl 0
  · exact Nat.zero_lt_one
  · refine ⟨fun i j hi _ _ => ?_, fun c hc => ?_⟩
    · exact absurd hi (Nat.not_lt_zero i)
    · exact nomatch (show c ∈ ([] : List Card) from hc)

/-! ## The witness is solvable (three moves, the physical order) -/

private def wPlay : List Move :=
  [Move.pileStack (D .king), Move.reveal Anchor.p1, Move.pileStack (C .king)]

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

/-! ## The historical guard's motivation + the rule-repair effect

`crux_refuted` / `main_refuted` (this file's first version, 2026-09-13)
derived `False` from the pre-repair statements — `solvable_of_pileStack`
and `solvable_accommodates` without the lockedness guard — via exactly
the facts below: `wState.solvableFrom`, `wState.apply (pileStack ♦K) =
some wState1`, and `¬ wState1.solvableFrom` (the dead-pile invariant,
retired with the reveal rule).  The same-session repair
(`+ hnotlock` on the crux, `safeAccommodates` on the main) excluded
precisely this witness.  The tightness examples (every other
hypothesis holds here) stay green below — and the revival pins record
that the 2026-09-16 rule repair dissolves the hole at this witness: -/

private def wState1 : State := (wState.apply (Move.pileStack (D .king))).getD wState

private theorem wState_apply :
    wState.apply (Move.pileStack (D .king)) = some wState1 := by
  have his : (wState.apply (Move.pileStack (D .king))).isSome = true := by decide
  cases h : wState.apply (Move.pileStack (D .king)) with
  | none =>
      rw [h] at his
      simp at his
  | some s₁ =>
      have hw : wState1 = s₁ := by
        show (wState.apply (Move.pileStack (D .king))).getD wState = s₁
        rw [h]
        rfl
      rw [hw]

private theorem wState1_wf : wState1.WF :=
  apply_wf wState_wf _ _ wState_apply

/-- The flip is illegal while ♦K covers the boundary (pinned). -/
example : (wState.apply (Move.reveal Anchor.p1)).isSome = false := by decide

/-- The revival play: flip the bare boundary, then stack ♣K. -/
private def wRevive : List Move := [Move.reveal Anchor.p1, Move.pileStack (C .king)]

private def wWin1 : State := (wState1.run wRevive).getD wState1

private theorem wState1_run : wState1.run wRevive = some wWin1 := by
  have his : (wState1.run wRevive).isSome = true := by decide
  cases h : wState1.run wRevive with
  | none =>
      rw [h] at his
      simp at his
  | some w =>
      have hw : wWin1 = w := by
        show (wState1.run wRevive).getD wState1 = w
        rw [h]
        rfl
      rw [hw]

/-- **The locked-hole dissolves here**: the accommodation successor is
solvable in two more moves under the physical flip rule. -/
theorem wState1_solvable : wState1.solvableFrom :=
  ⟨wRevive, wWin1, wState1_run, by decide⟩

example : wState.isLocked (D .king) = true := by decide

example : wState.WF := wState_wf

example : wState.apply (Move.pileStack (D .king)) = some wState1 :=
  wState_apply

example : wState.solvableFrom := wState_solvable

end B4Locked

#print axioms B4Locked.wState_wf
#print axioms B4Locked.wState_solvable
#print axioms B4Locked.wState_apply
#print axioms B4Locked.wState1_wf
#print axioms B4Locked.wState1_solvable
