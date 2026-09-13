import Klondike.Macro

/-!
# The C1 witness — `solvableEngine_iff_macro` was FALSE as staged (2026-09-13)

The macro game as defined (`macroSolvable := ∃ ks w, macroSteps st ks w ∧
w.isWin`) checks wins only at *post-commit* states: `macroSteps` ends on
a commitment, so the final accommodation block of A3's regrouping
("shuffle, commit, shuffle, commit, …, shuffle") has no home.  An
engine win whose last height-raise is a trailing accommodation — and
where no commitment is ever legal — has no macro witness.

State `stC1`: ♥ at 12, ♠/♦/♣ complete, the ♥K as the sole visible card
(seated on anchor p0, a king's legal anchor seat), empty stock, all
depths 0, draw step 1, a standard WF deal.  The engine wins in one
move: `[pileStack ♥K]` (♥K is the ♠/♦/♣-style foundation's next card —
12 = 12 — and nothing sits on it).  But no `commitApplies` ever fires
from any accommodated state: the empty stock kills every Draw
commitment (`reachablePos` is `posOf`-guarded), and the all-zero
depths kill every Reveal commitment (`pileOfTopHidden` finds no
boundary).  So the only macro line is `[]`, ending at `stC1` itself —
not a win (♥ at 12).

This is exactly the shape the Rust macro game accounts for: its solver
checks `is_win` *after* `canonicalize` (the accommodation sweep) at
every node (`macro_solvable_sel`), i.e. the win may arrive through a
final shuffle.  REPAIR (applied in Macro.lean, 2026-09-13):
`macroSolvable` gained the trailing accommodation block —
`∃ ks w w', macroSteps st ks w ∧ accommodates w w' ∧ w'.isWin`.

HISTORICAL after the repair: `macroSolvableOld` below spells the
pre-repair predicate so the refutation stays checkable, and
`stC1_macroNew` records the repaired verdict at this state (the final
shuffle `[pileStack ♥K]` is exactly the missing witness).  The core
facts (`stC1_wf`, `reveal_dead`, `deadCommit`, `accomm_invar`,
`stC1_macroFix`, `stC1_notOldMacro`, `stC1_engine`, `stC1_macroNew`)
cite no sorry'd constant and stay green.
-/

namespace MacroC1

/-- Spades. -/
private def S (r : Rank) : Card := ⟨Suit.spade, r⟩
/-- Hearts. -/
private def H (r : Rank) : Card := ⟨Suit.heart, r⟩
/-- Diamonds. -/
private def D (r : Rank) : Card := ⟨Suit.diamond, r⟩
/-- Clubs. -/
private def C (r : Rank) : Card := ⟨Suit.club, r⟩

/-- The witness deal (a standard-shape 52-card arrangement; its
contents are irrelevant beyond `Deal.WF` — the state's depths are all
zero, so no hidden-card conjunct ever reads it). -/
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

/-- The only visible card: the ♥K, seated on anchor p0. -/
private def c1Top : Base → Option Card :=
  fun b => if b = Sum.inl Anchor.p0 then some (H .king) else none

private theorem c1Top_some {b : Base} {c : Card} (h : c1Top b = some c) :
    c = H .king ∧ b = Sum.inl Anchor.p0 := by
  by_cases hbc : b = Sum.inl Anchor.p0
  · refine ⟨?_, hbc⟩
    simp only [c1Top, if_pos hbc, Option.some.injEq] at h
    exact h.symm
  · simp only [c1Top, if_neg hbc] at h
    exact absurd h (by simp)

private theorem c1Top_inj : ∀ (b₁ b₂ : Base) (c : Card),
    c1Top b₁ = some c → c1Top b₂ = some c → b₁ = b₂ := by
  intro b₁ b₂ c h₁ h₂
  rw [(c1Top_some h₁).2, (c1Top_some h₂).2]

/-- The witness state: ♥ at 12, the others complete, the ♥K sole
visible on anchor p0, empty stock, all depths 0, draw step 1. -/
private def stC1 : State where
  deal := wDeal
  board := { topOf := c1Top, inj := c1Top_inj }
  heights := fun s => if s = Suit.heart then 12 else 13
  depths := fun _ => 0
  stock := ⟨[], 0⟩
  drawStep := 1

-- Executable sanity probes (the refute-first protocol):
/-- info: false -/
#guard_msgs in
#eval stC1.isWin                                            -- not yet a win
/-- info: true -/
#guard_msgs in
#eval (stC1.apply (Move.pileStack (H .king))).isSome        -- the accommodation move is legal
/-- info: true -/
#guard_msgs in
#eval (stC1.apply (Move.pileStack (H .king))).getD stC1 |>.isWin  -- and it wins

private theorem stC1_wf : stC1.WF := by
  refine ⟨wDeal_wf, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a
    show 0 ≤ (wDeal.piles a).length
    exact Nat.zero_le _
  · intro b c htop
    obtain ⟨hc, hb⟩ := c1Top_some htop
    subst hc
    subst hb
    refine ⟨(Board.bottomOf_eq _ _ _).mpr htop, ?_⟩
    left
    rfl
  · intro c _
    rfl
  · intro c _
    rfl
  · intro c hc
    have hcK : c ≠ H .king := by
      intro h
      rw [h] at hc
      exact absurd hc (by decide)
    refine ⟨?_, rfl, ?_⟩
    · cases hb : stC1.board.bottomOf c with
      | none => simp [State.isVis, hb]
      | some b => exact absurd ((c1Top_some ((Board.bottomOf_eq _ _ _).mp hb)).1) hcK
    · intro a hca
      rw [show stC1.hidden a = ([] : List Card) from rfl] at hca
      cases hca
  · intro c _ a hca
    rw [show stC1.hidden a = ([] : List Card) from rfl] at hca
    cases hca
  · intro s
    show (if s = Suit.heart then 12 else 13) ≤ 13
    split <;> omega
  · show stC1.stock.cursor ≤ stC1.stock.cards.length
    exact Nat.le_refl 0
  · show 0 < stC1.drawStep
    decide
  · refine ⟨?_, fun c hc => nomatch hc⟩
    intro i j hi _
    have h0 : stC1.stock.cards.length = 0 := rfl
    rw [h0] at hi
    exact absurd hi (Nat.not_lt_zero i)

/-! ## No commitment ever fires from an accommodated state -/

/-- All-zero depths: no pile has a hidden boundary, so no reveal can
fire (whatever the board). -/
private theorem reveal_dead {s : State} (hdepth : ∀ a, s.depths a = 0) (c : Card) :
    s.apply (Move.reveal c) = none := by
  have hpile : ∀ r, s.pileOfTopHidden r = none := by
    intro r
    refine findFirst_eq_none _ Anchor.all (fun a _ => ?_)
    show (decide (s.topHidden a = some r)) ≠ true
    rw [show s.topHidden a = none from by
      show ((s.deal.piles a).take (s.depths a)).getLast? = none
      rw [hdepth a]
      rfl]
    simp
  cases h : s.apply (Move.reveal c) with
  | none => rfl
  | some st' =>
      rw [apply_reveal_iff] at h
      obtain ⟨_, r, _, _, _, hp, _, _⟩ := h
      rw [hpile r] at hp
      simp at hp

/-- Empty stock + all-zero depths: no commitment applies. -/
private theorem deadCommit {s : State} (hstock : s.stock.cards = [])
    (hdepth : ∀ a, s.depths a = 0) :
    ∀ (k : MacroMove) (s'' : State), ¬ commitApplies s k s'' := by
  intro k s'' hcom
  cases k with
  | revealCommit c =>
      simp only [commitApplies] at hcom
      rw [reveal_dead hdepth c] at hcom
      simp at hcom
  | drawCommit c =>
      simp only [commitApplies] at hcom
      obtain ⟨b, hb⟩ := hcom
      have hpos : s.stock.posOf c = none := by
        show Cycle.findFirstIdx (fun c' => decide (c' = c)) s.stock.cards = none
        rw [hstock]
        rfl
      have hrp : s.reachablePos c = none := by
        simp only [State.reachablePos, hpos]
        split <;> rfl
      rcases hb with ⟨-, hdt⟩ | hds
      · simp [State.applyDrawTo, hrp] at hdt
      · simp [State.applyDrawStackTo, hrp] at hds

/-- Accommodations preserve the stock and the depths (the two facts
the deadlock needs). -/
private theorem accomm_invar : ∀ (play : List Move) (s s' : State),
    (∀ m ∈ play, m.isAccommodation = true) → s.run play = some s' →
    s'.stock = s.stock ∧ ∀ a, s'.depths a = s.depths a := by
  intro play
  induction play with
  | nil =>
      intro s s' _ hrun
      have hs : s = s' := Option.some.inj hrun
      subst hs
      exact ⟨rfl, fun _ => rfl⟩
  | cons m ms ih =>
      intro s s' hall hrun
      simp only [State.run] at hrun
      cases hsm : s.apply m with
      | none => rw [hsm] at hrun; simp at hrun
      | some s₁ =>
          rw [hsm] at hrun
          have hrest : s₁.run ms = some s' := hrun
          have htail := ih s₁ s'
            (fun m' hm' => hall m' (List.mem_cons.mpr (Or.inr hm'))) hrest
          have hmac := hall m (List.mem_cons.mpr (Or.inl rfl))
          cases m with
          | draw => simp [Move.isAccommodation] at hmac
          | reveal c => simp [Move.isAccommodation] at hmac
          | deckPile c b => simp [Move.isAccommodation] at hmac
          | deckStack c => simp [Move.isAccommodation] at hmac
          | pilePile c b => simp [Move.isAccommodation] at hmac
          | pileStack c =>
              rw [apply_pileStack_iff] at hsm
              obtain ⟨_, b, _, _, hst⟩ := hsm
              exact ⟨by rw [htail.1, hst],
                fun a => by rw [htail.2 a, hst]⟩
          | stackPile c b =>
              rw [apply_stackPile_iff] at hsm
              obtain ⟨_, _, bd, _, hst⟩ := hsm
              exact ⟨by rw [htail.1, hst],
                fun a => by rw [htail.2 a, hst]⟩

/-- No macro line from `stC1` beyond the empty one. -/
private theorem stC1_macroFix : ∀ (ks : List MacroMove) (w : State),
    macroSteps stC1 ks w → ks = [] ∧ w = stC1 := by
  intro ks
  induction ks with
  | nil =>
      intro w h
      have h' : stC1 = w := h
      exact ⟨rfl, h'.symm⟩
  | cons k krest ih =>
      intro w hsteps
      obtain ⟨st'', hstep, _⟩ := hsteps
      obtain ⟨st', hacc, hcom⟩ := hstep
      obtain ⟨playA, hrunA, hallA⟩ := hacc
      obtain ⟨hstock, hdepth⟩ := accomm_invar playA stC1 st' hallA hrunA
      exact absurd hcom (deadCommit (by rw [hstock]; rfl)
        (fun a => by rw [hdepth a]; rfl) k st'')

/-- The pre-repair macro solvability, spelled locally so the refutation
stays checkable against the repaired library. -/
def macroSolvableOld (st : State) : Prop :=
  ∃ ks w, macroSteps st ks w ∧ w.isWin = true

/-- `stC1` is engine-solvable but (as staged) not macro-solvable. -/
private theorem stC1_notOldMacro : ¬ macroSolvableOld stC1 := by
  intro ⟨ks, w, hsteps, hwin⟩
  obtain ⟨rfl, rfl⟩ := stC1_macroFix ks w hsteps
  exact absurd hwin (by decide)

/-- The engine win: one `pileStack`. -/
private def wWin : State := { stC1 with
  board := stC1.board.detach (Sum.inl Anchor.p0),
  heights := fun s => if s = (H .king).suit then stC1.heights s + 1 else stC1.heights s }

private theorem stC1_engine : stC1.solvableEngine := by
  refine ⟨[Move.pileStack (H .king)], ?_, wWin, ?_, ?_⟩
  · intro m hm
    obtain rfl := List.mem_singleton.mp hm
    rfl
  · show stC1.run [Move.pileStack (H .king)] = some wWin
    rw [run_singleton]
    refine (apply_pileStack_iff).mpr ⟨rfl, Sum.inl Anchor.p0,
      (Board.bottomOf_eq _ _ _).mpr rfl, rfl, rfl⟩
  · decide

/-- The repaired verdict at this state: the final shuffle is exactly
the missing witness (the empty commitment line plus the winning
accommodation tail). -/
theorem stC1_macroNew : stC1.macroSolvable :=
  ⟨[], stC1, wWin, rfl,
    ⟨[Move.pileStack (H .king)], by
      show stC1.run [Move.pileStack (H .king)] = some wWin
      rw [run_singleton]
      exact (apply_pileStack_iff).mpr ⟨rfl, Sum.inl Anchor.p0,
        (Board.bottomOf_eq _ _ _).mpr rfl, rfl, rfl⟩,
      fun m hm => by obtain rfl := List.mem_singleton.mp hm; rfl⟩,
    by decide⟩


/- Axiom checks: the public verdict is guarded; the three `private`
declarations above print mangled names and are left informational
(the README's convention for B4LockedWitness/DeadPileWitness). -/
/-- info: 'MacroC1.stC1_macroNew' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms stC1_macroNew

#print axioms stC1_wf
#print axioms stC1_notOldMacro
#print axioms stC1_engine
