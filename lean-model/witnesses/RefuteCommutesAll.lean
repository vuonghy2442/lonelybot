import Klondike.Dominance

/-!
Scratch (wrong-theorem protocol): the staged `dominant_of_commutesWithAll`
is FALSE.

Witness `stX`: a won state (empty board, all foundations at 13, empty
stock, no hidden cards) with `m = Move.pileStack ♥2`.

- `stX.solvableFrom` — via `[]` (`isWin` by heights alone).
- `stX.apply (Move.pileStack ♥2) = none` — ♥2 is not on the board.
- The commutation hypothesis holds VACUOUSLY at `stX`: the only legal
  moves at `stX` are `draw` and `stackPile` of a king (heights 13 force
  toIdx 12); every one-step successor's board contains at most one king,
  never ♥2 — so `st₁.apply (Move.pileStack ♥2) = none` always.

Hence `dominantAt stX (Move.pileStack ♥2)` fails while the hypothesis
holds: the staged implication is refuted (both facts below are
sorry-free, axiom-checked).
-/

namespace RefuteCommutesAll

/-- The witness card: ♥2. -/
def c2 : Card := ⟨Suit.heart, Rank.two⟩

/-- A won state: empty board, all foundations at 13, empty stock. -/
def stX : State where
  deal := { piles := fun _ => [], stock := [] }
  board := Board.empty
  heights := fun _ => 13
  depths := fun _ => 0
  stock := ⟨[], 0⟩
  drawStep := 1

theorem stX_topOf (b : Base) : stX.board.topOf b = none := rfl

theorem stX_bottomOf (c : Card) : stX.board.bottomOf c = none :=
  Board.empty_bottomOf c

theorem stX_prev : stX.stock.prev = none := rfl

theorem stX_isWin : stX.isWin = true := rfl

theorem stX_solvable : stX.solvableFrom := ⟨[], stX, rfl, stX_isWin⟩

theorem stX_pileStack_none : stX.apply (Move.pileStack c2) = none := by
  show State.applyPileStack stX c2 = none
  simp only [State.applyPileStack]
  rw [stX_topOf, stX_bottomOf]

/-- The staged hypothesis, verified at the witness. -/
theorem stX_h : ∀ (m' : Move) (s₁ s₂ : State),
    stX.apply m' = some s₁ → s₁.apply (Move.pileStack c2) = some s₂ →
    ∃ s₃, stX.apply (Move.pileStack c2) = some s₃ ∧ s₃.apply m' = some s₂ := by
  intro m' s₁ s₂ hm' hst₂
  obtain ⟨_, b', hb', _, _⟩ := apply_pileStack_iff.mp hst₂
  have htop : s₁.board.topOf b' = some c2 := (Board.bottomOf_eq _ _ _).mp hb'
  cases m' with
  | draw =>
      have hs₁ : s₁ = {stX with stock := stX.stock.dealOnce stX.drawStep} :=
        apply_draw_iff.mp hm'
      subst hs₁
      dsimp only at htop
      rw [stX_topOf] at htop
      exact absurd htop (by simp)
  | reveal c =>
      have hnone : stX.apply (Move.reveal c) = none := by
        show State.applyReveal stX c = none
        simp only [State.applyReveal]
        rw [stX_topOf, stX_bottomOf]
      rw [hnone] at hm'
      exact absurd hm' (by simp)
  | deckPile c b =>
      obtain ⟨hp, _, _, _, _⟩ := apply_deckPile_iff.mp hm'
      rw [stX_prev] at hp
      exact absurd hp (by simp)
  | deckStack c =>
      obtain ⟨hp, _, _⟩ := apply_deckStack_iff.mp hm'
      rw [stX_prev] at hp
      exact absurd hp (by simp)
  | pileStack c =>
      obtain ⟨_, _, hb₀, _, _⟩ := apply_pileStack_iff.mp hm'
      rw [stX_bottomOf] at hb₀
      exact absurd hb₀ (by simp)
  | stackPile c b =>
      obtain ⟨hrk, _, bd, hatt, hs₁⟩ := apply_stackPile_iff.mp hm'
      subst hs₁
      dsimp only at htop
      by_cases hb : b' = b
      · subst hb
        rw [Board.attach_topOf _ _ _ hatt] at htop
        rw [Option.some.injEq] at htop
        subst htop
        have h1 : c2.rank.toIdx = 1 := rfl
        have h2 : stX.heights c2.suit = 13 := rfl
        rw [h1, h2] at hrk
        omega
      · rw [Board.attach_topOf_ne _ _ _ hatt hb, stX_topOf] at htop
        exact absurd htop (by simp)
  | pilePile c b =>
      obtain ⟨b₀, hb₀, _, _, _, _⟩ := apply_pilePile_iff.mp hm'
      rw [stX_bottomOf] at hb₀
      exact absurd hb₀ (by simp)

/-- The staged conclusion fails at the witness. -/
theorem stX_not_dominantAt : ¬ dominantAt stX (Move.pileStack c2) := by
  intro hd
  obtain ⟨s₁, hap, _⟩ := hd stX_solvable
  rw [stX_pileStack_none] at hap
  exact absurd hap (by simp)

end RefuteCommutesAll

/-- info: 'RefuteCommutesAll.stX_h' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RefuteCommutesAll.stX_h

/-- info: 'RefuteCommutesAll.stX_not_dominantAt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms RefuteCommutesAll.stX_not_dominantAt

/-- info: 'apply_pileStack_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms apply_pileStack_iff

/-- info: 'apply_draw_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms apply_draw_iff

/-- info: 'apply_deckPile_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms apply_deckPile_iff

/-- info: 'apply_deckStack_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms apply_deckStack_iff

/-- info: 'apply_stackPile_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms apply_stackPile_iff

/-- info: 'apply_pilePile_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms apply_pilePile_iff

/-- info: 'Board.attach_topOf' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Board.attach_topOf

/-- info: 'Board.bottomOf_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Board.bottomOf_eq
