import Orig2.ForkMountainShape

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-!
# Orig2/ForkMountainRefute — `MountainKit.RaiseBeforePullShortens` is FALSE as stated

READ-ONLY scratch card.  No source file is modified; nothing is committed.
Zero `sorry`, zero `Classical.choice`, zero `native_decide`; axiom battery at
the tail.

## The clause

`MountainKit.RaiseBeforePullShortens` (`Orig2/ForkMountainShape.lean:503`) is
the M1 deletion residual of the mountain route:

```
∀ u v ρ pre post c d b,
  u.WF → ShufflePlayW u ρ v →
  ρ = pre ++ raise c :: post → pull d b ∈ post →
  ∃ ρ', ShufflePlayW u ρ' v ∧ ρ'.length < ρ.length
```

Note the binders: `c` (the raised card) and `d` (the later pulled card) are
**unrelated**, and the statement is **not gated at `SSaturated` endpoints**.
`noRaiseBeforePull_of_minimal` (`Orig2/ForkMountainShape.lean:534`) feeds it
from a minimal play, so the campaign only consumes the saturated/minimal case —
but the clause as written is global, and this card kills the global form.

## The counterexample (7 exposed cards, 2 moves)

```
wU : hearts A..4 founded, AD founded,  p0 = [6S, 5H], p1 = [2S]
      raise 5H      (hearts 4 → 5, p0 → [6S])
      pull AD → 2S  (diamonds 1 → 0, p1 → [2S, AD])
wV : hearts A..5 founded, p1 = [2S, AD], p0 = [6S]
```

The play is `[raise 5H, pull AD→2S]`: a raise followed by a later pull, so it
satisfies `RaiseBeforePull ρ`.

**Minimality is proved here, not assumed.**  The rung vector moves
`(4,1,0,0) → (5,0,0,0)`, whose L1 distance is `2`; every witness letter changes
at most one suit's rung by at most one (`rungAt_draw`, `rungAt_tabToTab`,
`rungAt_tabToFound`, `rungAt_foundToTab`), so **every** `ShufflePlayW wU _ wV`
has length `≥ 2`.  The play has length 2, hence no strictly shorter play exists
and `RaiseBeforePullShortens` — which promises one — is false.

## Why the campaign's *use* survives this (honest boundary)

`wU` is not `SSaturated` (5H is raisable at it; indeed `v` is not either).  The
mountain route only ever instantiates M1 between `SSaturated` endpoints, and
there the first non-free letter is necessarily a *pull* (`first_nonfree_pull`),
so this two-letter obstruction cannot occur.  The next card,
`Orig2/ForkMountainRefutePlay.lean`, transcribes the `SSaturated` witness found by the
probe (`[[Crack_Report.md]]` §4): a 13-move minimal saturated→saturated play
with a genuine same-card relocation.  This card's job is the exact clause kill:
the residual must be stated with the `SSaturated` gate, it cannot be used as a
global deletion hypothesis.
-/

namespace CrackM1

/-- `A..n` of a suit (`take` of the foundation order). -/
def upto (s : Suit) (n : Nat) : List Card := (Suit.upCards s).take n

def H5 : Card := ⟨.heart, .five⟩
def S6 : Card := ⟨.spade, .six⟩
def S2 : Card := ⟨.spade, .two⟩
def AD : Card := ⟨.diamond, .ace⟩

/-- The seven exposed cards. -/
def fixed : List Card := [⟨.heart, .ace⟩, ⟨.heart, .two⟩, ⟨.heart, .three⟩,
  ⟨.heart, .four⟩, H5, S6, S2, AD]

/-- The inert 44-card hidden deck. -/
def deck : List Card :=
  Card.universe.filter (fun c => !(decide (c ∈ fixed)))

def mk (fh fd : List Card) (p0 p1 : List Card) : State :=
  { found := fun s => match s with
      | .heart => fh
      | .diamond => fd
      | _ => []
    piles := fun a => match a with
      | .p0 => ⟨[], p0⟩
      | .p1 => ⟨[], p1⟩
      | .p6 => ⟨deck, []⟩
      | _ => ⟨[], []⟩
    stock := []
    waste := []
    drawStep := 1 }

/-- **`wU`** — hearts `A..4` and `AD` founded; `5H` on `6S`; `2S` bare. -/
def wU : State := mk (upto .heart 4) [AD] [S6, H5] [S2]

/-- **`wV`** — hearts `A..5` founded; `AD` pulled onto `2S`. -/
def wV : State := mk (upto .heart 5) [] [S6] [S2, AD]

/-! ## §1. Well-formedness -/

theorem wU_wf : wU.WF := by
  refine ⟨?_, ?_, ?_, by decide⟩
  · intro s
    cases s with
    | heart => exact ⟨4, rfl⟩
    | diamond => exact ⟨1, rfl⟩
    | spade => exact ⟨0, rfl⟩
    | club => exact ⟨0, rfl⟩
  · intro a; cases a <;> decide
  · intro c _; rcases c with ⟨s, r⟩; cases s <;> cases r <;> decide

theorem wV_wf : wV.WF := by
  refine ⟨?_, ?_, ?_, by decide⟩
  · intro s
    cases s with
    | heart => exact ⟨5, rfl⟩
    | diamond => exact ⟨0, rfl⟩
    | spade => exact ⟨0, rfl⟩
    | club => exact ⟨0, rfl⟩
  · intro a; cases a <;> decide
  · intro c _; rcases c with ⟨s, r⟩; cases s <;> cases r <;> decide

/-! ## §2. The two letters -/

theorem wU_raise :
    State.step wU (Move.tabToFound H5) = some
      (mk (upto .heart 5) [AD] [S6] [S2]) := by
  have hnext : wU.nextUp H5 = true := by decide
  have hpo : wU.pileOfTop H5 = some .p0 := by decide
  rw [step_tabToFound_splice hnext hpo]
  refine congrArg some (State.ext ?_ ?_ ?_ ?_ ?_)
  · funext s; cases s <;> rfl
  · funext a; cases a <;> rfl
  · rfl
  · rfl
  · rfl

theorem wU_raise_rev : reversibleAtW wU (Move.tabToFound H5) :=
  (tabToFoundR_iff_reversibleAtW wU_wf H5).mp (by decide)

/-- The intermediate state after the raise. -/
def wM : State := mk (upto .heart 5) [AD] [S6] [S2]

theorem wM_eq : wM = mk (upto .heart 5) [AD] [S6] [S2] := rfl

theorem wM_pull :
    State.step wM (Move.foundToTab AD (Sum.inr S2)) = some wV := by
  have htop : wM.foundTop .diamond = some AD := by decide
  have hcp : wM.canPlace AD (Sum.inr S2) = true := by decide
  rw [step_foundToTab_splice htop hcp]
  refine congrArg some (State.ext ?_ ?_ ?_ ?_ ?_)
  · funext s; cases s <;> rfl
  · funext a; cases a <;> rfl
  · rfl
  · rfl
  · rfl

theorem wM_wf : wM.WF := by
  refine ⟨?_, ?_, ?_, by decide⟩
  · intro s
    cases s with
    | heart => exact ⟨5, rfl⟩
    | diamond => exact ⟨1, rfl⟩
    | spade => exact ⟨0, rfl⟩
    | club => exact ⟨0, rfl⟩
  · intro a; cases a <;> decide
  · intro c _; rcases c with ⟨s, r⟩; cases s <;> cases r <;> decide

theorem wM_pull_rev : reversibleAtW wM (Move.foundToTab AD (Sum.inr S2)) :=
  (foundToTabR_iff_reversibleAtW wM_wf AD (Sum.inr S2)).mp (by decide)

/-- **THE TWO-LETTER WITNESS PLAY.** -/
theorem w_play :
    ShufflePlayW wU [Move.tabToFound H5, Move.foundToTab AD (Sum.inr S2)] wV := by
  have h1 : State.step wU (Move.tabToFound H5) = some wM := wU_raise
  refine Walk.cons wU_raise_rev h1 ?_
  exact Walk.cons wM_pull_rev wM_pull (Walk.nil wV)

/-- The play contains a raise strictly before a later pull — `RaiseBeforePull`. -/
theorem w_raiseBeforePull :
    MountainKit.RaiseBeforePull
      [Move.tabToFound H5, Move.foundToTab AD (Sum.inr S2)] :=
  ⟨[], [Move.foundToTab AD (Sum.inr S2)], H5, AD, Sum.inr S2, rfl,
    List.mem_cons_self ..⟩

/-! ## §3. Minimality — no shorter play exists -/

/-- **EVERY WITNESS LETTER CHANGES AT MOST ONE SUIT'S RUNG.** -/
theorem step_rung_support {u v : State} {m : Move}
    (h : State.step u m = some v) :
    ∃ σ0 : Suit, ∀ σ, σ ≠ σ0 → rungAt v σ = rungAt u σ := by
  cases m with
  | draw => exact ⟨.heart, fun σ _ => rungAt_draw h σ⟩
  | wasteToFound c =>
      exact ⟨c.suit, fun σ hσ => by
        rw [rungAt_wasteToFound h σ, ite_eq_right hσ]⟩
  | wasteToTab c b => exact ⟨.heart, fun σ _ => rungAt_wasteToTab h σ⟩
  | tabToFound c =>
      exact ⟨c.suit, fun σ hσ => by
        rw [rungAt_tabToFound h σ, ite_eq_right hσ]⟩
  | foundToTab c b =>
      exact ⟨c.suit, fun σ hσ => by
        rw [rungAt_foundToTab h σ, ite_eq_right hσ]⟩
  | tabToTab c b => exact ⟨.heart, fun σ _ => rungAt_tabToTab h σ⟩

theorem wU_rung_heart : rungAt wU .heart = 4 := rfl
theorem wU_rung_diamond : rungAt wU .diamond = 1 := rfl
theorem wV_rung_heart : rungAt wV .heart = 5 := rfl
theorem wV_rung_diamond : rungAt wV .diamond = 0 := rfl

/-- **NO SINGLE MOVE TAKES `wU` TO `wV`**: the rung vector moves in two
coordinates, and a step moves at most one. -/
theorem no_single_step : ∀ m : Move, State.step wU m ≠ some wV := by
  intro m h
  obtain ⟨σ0, hfix⟩ := step_rung_support h
  have hH : rungAt wV .heart ≠ rungAt wU .heart := by
    rw [wV_rung_heart, wU_rung_heart]; decide
  have hD : rungAt wV .diamond ≠ rungAt wU .diamond := by
    rw [wV_rung_diamond, wU_rung_diamond]; decide
  cases σ0 with
  | heart => exact hD (hfix .diamond (by decide))
  | diamond => exact hH (hfix .heart (by decide))
  | spade => exact hH (hfix .heart (by decide))
  | club => exact hH (hfix .heart (by decide))

/-- **MINIMALITY OF THE TWO-LETTER PLAY.**  Every witness play `wU → wV` has
length at least 2. -/
theorem w_minimal {ρ' : List Move} (h : ShufflePlayW wU ρ' wV) :
    2 ≤ ρ'.length := by
  cases ρ' with
  | nil =>
      have hr := Walk_run (fun st m => reversibleAtW st m) h
      simp only [State.run] at hr
      have heq : wU = wV := Option.some.inj hr
      have hv : rungAt wU .heart = 5 := heq.symm ▸ wV_rung_heart
      rw [wU_rung_heart] at hv
      exact absurd hv (by decide)
  | cons m rest =>
      cases rest with
      | nil =>
          have hr := Walk_run (fun st m => reversibleAtW st m) h
          simp only [State.run] at hr
          cases hs : State.step wU m with
          | none => rw [hs] at hr; exact absurd hr (by simp)
          | some s =>
              rw [hs] at hr
              exact absurd (hs.trans (by rw [Option.some.inj hr])) (no_single_step m)
      | cons m' rest' =>
          simp only [List.length_cons]
          omega

/-- **`RaiseBeforePullShortens` IS FALSE AS STATED.**  A 2-move raise-then-pull
witness has no strictly shorter witness play between its endpoints. -/
theorem raiseBeforePullShortens_false :
    ¬ MountainKit.RaiseBeforePullShortens := by
  intro h
  obtain ⟨ρ', hplay', hlen⟩ :=
    h wU wV [Move.tabToFound H5, Move.foundToTab AD (Sum.inr S2)]
      [] [Move.foundToTab AD (Sum.inr S2)] H5 AD (Sum.inr S2)
      wU_wf w_play rfl (List.mem_cons_self ..)
  have hmin := w_minimal hplay'
  simp only [List.length_cons, List.length_nil] at hlen
  omega

/-! ## §4. Axiom battery -/

#print axioms CrackM1.wU_wf
#print axioms CrackM1.wV_wf
#print axioms CrackM1.wU_raise
#print axioms CrackM1.wU_raise_rev
#print axioms CrackM1.wM_pull
#print axioms CrackM1.wM_pull_rev
#print axioms CrackM1.w_play
#print axioms CrackM1.w_raiseBeforePull
#print axioms CrackM1.step_rung_support
#print axioms CrackM1.no_single_step
#print axioms CrackM1.w_minimal
#print axioms CrackM1.raiseBeforePullShortens_false

end CrackM1
