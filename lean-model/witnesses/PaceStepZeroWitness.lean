import Klondike.Macro

/-!
# The pace step-zero witness (2026-09-13)

The physical-game pace theorems as staged — `deal_passEnd_reaches`,
`pace_dominance_phys_passEnd`, `solvable_iff_pure_cursors` — carried no
step-positivity hypothesis, and at `drawStep = 0` every deal is the
identity below the pass end (`min (c + 0) n = c`), so the pass end is
unreachable from a mid-pass cursor and the pure-cursor equivalence
collapses.

State `stZ`: empty board, every foundation at 12, the four kings as the
whole stock, `drawStep = 0`.  From cursor 0 every move but `draw` is
illegal and `draw` is the identity — the state is frozen, hence
unsolvable (`isWin` needs 13s).  From the pass-end twin (cursor 4) the
four kings stack off in four `deckStack`s and WIN.  So: the pass end is
not reachable from cursor 0 (kills `deal_passEnd_reaches`), the pass end
is solvable while cursor 0 is not (kills
`pace_dominance_phys_passEnd`), and cursor 0 is pure while the pass
end is pure too (kills `solvable_iff_pure_cursors`).

HISTORICAL after the repair (all three gained `hstep : 0 <
st.drawStep`, and are PROVEN): the `*_refuted` corollaries that cited
the pre-repair statements have been removed — see the note at the
bottom.  The core facts (`stZ_dead`, `stZ_run_fix`, `stZ_notReach`,
`stZ_notSolvable`, `stN_solvable`) cite no sorry'd constant and stay
green.
-/

/-- The counterexample state: all foundations at 12, the four kings as
the stock, cursor 0, draw step 0. -/
def stZ : State :=
  ⟨⟨fun _ => [], []⟩, Board.empty, fun _ => 12, fun _ => 0,
    ⟨[⟨Suit.heart, Rank.king⟩, ⟨Suit.diamond, Rank.king⟩,
      ⟨Suit.club, Rank.king⟩, ⟨Suit.spade, Rank.king⟩], 0⟩, 0⟩

/-- The pass-end twin: cursor at the length. -/
def stN : State := { stZ with stock := { stZ.stock with cursor := 4 } }

-- Executable sanity probes (the refute-first protocol), pinned:

/-- info: 4 -/
#guard_msgs in
#eval stZ.stock.cards.length

/-- info: 0 -/
#guard_msgs in
#eval (Cycle.dealOnce stZ.drawStep stZ.stock).cursor  -- step 0: the identity below the pass end

/-- info: 0 -/
#guard_msgs in
#eval (Cycle.dealOnce stZ.drawStep stN.stock).cursor  -- from the pass end it wraps

/-- Every move from `stZ` fails, or is `draw`'s identity. -/
theorem stZ_dead : ∀ (m : Move) (s : State), stZ.apply m = some s → s = stZ := by
  intro m s h
  have hbot : ∀ (c : Card), stZ.board.bottomOf c = none := fun c =>
    (Board.bottomOf_eq_none Board.empty c).mpr
      (fun b hb => by simp [Board.empty_topOf] at hb)
  have hprev : stZ.stock.prev = none := rfl
  cases m with
  | draw =>
      have hst : s = { stZ with stock := stZ.stock.dealOnce stZ.drawStep } :=
        (apply_draw_iff (st := stZ) (st' := s)).mp h
      subst hst
      rfl
  | reveal c =>
      obtain ⟨-, r, a, bd, hb, -, -, -⟩ := (apply_reveal_iff (st := stZ) (st' := s)).mp h
      rw [hbot c] at hb; simp at hb
  | deckPile c b =>
      obtain ⟨hp, -, -, -, -⟩ := (apply_deckPile_iff (st := stZ) (st' := s)).mp h
      rw [hprev] at hp; simp at hp
  | deckStack c =>
      obtain ⟨hp, -, -⟩ := (apply_deckStack_iff (st := stZ) (st' := s)).mp h
      rw [hprev] at hp; simp at hp
  | pileStack c =>
      obtain ⟨-, b, hb, -, -⟩ := (apply_pileStack_iff (st := stZ) (st' := s)).mp h
      rw [hbot c] at hb; simp at hb
  | stackPile c b =>
      obtain ⟨h1, h2, -, -, -⟩ := (apply_stackPile_iff (st := stZ) (st' := s)).mp h
      have h1' : c.rank.toIdx + 1 = 12 := h1
      cases b with
      | inl a =>
          simp only [State.canPlace] at h2
          obtain ⟨-, h3⟩ := Bool.and_eq_true_iff.mp h2
          have hkrk : c.rank = Rank.king := of_decide_eq_true h3
          rw [hkrk] at h1'
          exact absurd h1' (by decide)
      | inr d =>
          simp only [State.canPlace] at h2
          obtain ⟨-, h3⟩ := Bool.and_eq_true_iff.mp h2
          obtain ⟨h4, -⟩ := Bool.and_eq_true_iff.mp h3
          simp only [State.isVis] at h4
          rw [hbot d] at h4
          simp at h4
  | pilePile c b =>
      obtain ⟨b₀, hb, -, -, -, -, -⟩ := (apply_pilePile_iff (st := stZ) (st' := s)).mp h
      rw [hbot c] at hb; simp at hb

/-- Every state reached from `stZ` is `stZ`. -/
theorem stZ_run_fix : ∀ (play : List Move) (s : State),
    stZ.run play = some s → s = stZ := by
  intro play
  induction play with
  | nil =>
      intro s h
      exact (Option.some.inj h).symm
  | cons m ms ih =>
      intro s h
      simp only [State.run] at h
      cases hm : stZ.apply m with
      | none => rw [hm] at h; simp at h
      | some s₁ =>
          rw [hm] at h
          have h' : s₁.run ms = some s := h
          have hfix : s₁ = stZ := stZ_dead m s₁ hm
          rw [hfix] at h'
          exact ih s h'

/-- `deal_passEnd_reaches`'s conclusion at `(stZ, 0)` is false. -/
theorem stZ_notReach : ¬ (∃ play, stZ.run play = some stN) := by
  intro ⟨play, hrun⟩
  have hfix := stZ_run_fix play stN hrun
  have hc : (4 : Nat) = 0 := congrArg (fun t : State => t.stock.cursor) hfix
  exact absurd hc (by decide)

/-- `stZ` never wins: it is frozen at 12-high foundations. -/
theorem stZ_notSolvable : ¬ stZ.solvableFrom := by
  intro ⟨play, w, hrun, hwin⟩
  have hw : w = stZ := stZ_run_fix play w hrun
  rw [hw] at hwin
  exact absurd hwin (by decide)

/-- The four kings stack off the pass end: `stN` wins in four
`deckStack`s.  Each `sᵢ` is the corresponding successor literal. -/
def s1 : State := { stN with
  stock := stN.stock.removeAt (stN.stock.cursor - 1),
  heights := fun s => if s = (⟨Suit.spade, Rank.king⟩ : Card).suit
    then stN.heights s + 1 else stN.heights s }

def s2 : State := { s1 with
  stock := s1.stock.removeAt (s1.stock.cursor - 1),
  heights := fun s => if s = (⟨Suit.club, Rank.king⟩ : Card).suit
    then s1.heights s + 1 else s1.heights s }

def s3 : State := { s2 with
  stock := s2.stock.removeAt (s2.stock.cursor - 1),
  heights := fun s => if s = (⟨Suit.diamond, Rank.king⟩ : Card).suit
    then s2.heights s + 1 else s2.heights s }

def s4 : State := { s3 with
  stock := s3.stock.removeAt (s3.stock.cursor - 1),
  heights := fun s => if s = (⟨Suit.heart, Rank.king⟩ : Card).suit
    then s3.heights s + 1 else s3.heights s }

theorem stN_solvable : stN.solvableFrom :=
  ⟨[Move.deckStack ⟨Suit.spade, Rank.king⟩, Move.deckStack ⟨Suit.club, Rank.king⟩,
    Move.deckStack ⟨Suit.diamond, Rank.king⟩, Move.deckStack ⟨Suit.heart, Rank.king⟩],
   s4, rfl, rfl⟩

/-! ## The refutations (HISTORICAL)

`passEnd_refuted`, `passEnd_dominance_refuted`, `pure_cursors_refuted`
(this file's first version) each derived `False` from the pre-repair
statements — `deal_passEnd_reaches`, `pace_dominance_phys_passEnd`,
`solvable_iff_pure_cursors` without the step-positivity hypothesis —
through exactly the facts above: `stZ_notReach` (the pass end is
unreachable at step 0), `stN_solvable` vs `stZ_notSolvable` (the pass
end wins while the mid-pass cursor cannot), and the purity of both
cursors.  The same-session repair gave all three theorems
`hstep : 0 < st.drawStep` (and they are PROVEN); the old citations no
longer typecheck and have been removed.  The countermodel facts stay. -/

/-- info: 'stZ_dead' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms stZ_dead

/-- info: 'stZ_run_fix' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms stZ_run_fix

/-- info: 'stZ_notReach' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms stZ_notReach

/-- info: 'stZ_notSolvable' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms stZ_notSolvable

/-- info: 'stN_solvable' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms stN_solvable
