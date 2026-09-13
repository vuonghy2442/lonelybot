import Klondike.Pace

/-!
# The realizes_iff_stepsOK witness (2026-09-13)

`realizes_iff_stepsOK` as staged was FALSE: `realizes`'s FIRST draw
reads `maskPos` of the *initial* cycle — the leading-lane disjunct of
`maskPos_mem_iff` included — but `stepOK` at `pre = []` has no
leading-lane disjunct (no predecessor), so any mid-pass initial cursor
(cursor % step ≠ 0, cursor ≠ length) makes draw orders realizable that
`stepsOK` rejects.

Witness `cy`: deck [♥A, ♥2] (the hearts aces), step 2, cursor 1 (mid-pass:
1 % 2 ≠ 0, 1 ≠ 2).  Position 0 (♥A) is accessible through the initial
leading lane (`maskPos cy 2 = [0, 1]`), so σ = [♥A, ♥2] realizes; but at
`pre = []` the first draw needs `laneAt = 1` (0 % 2 = 0 ✗), `maxRem`
(♥2 above ♥A ✗), or a predecessor (none) — `stepsOK` is false.

The repair (same session): the theorem gained
`(hpure : c.cursor % step = 0 ∨ c.cursor = c.cards.length)` — the pure
class of `maskPos_pure_indep` (the ladder's rung 3 starts at cursor 0,
where it holds trivially).  Probed: with `hpure` the iff is clean on all
permutations of n ≤ 7 decks × steps 1–4 × every pure cursor in range,
plus 40320 perms at n = 8 (step 3, cursors 0 and 8); without it every
impure cursor in [0, n] shows counterexamples.

HISTORICAL after the repair: `iff_refuted`/`broken` cite the pre-repair
statement (no `hpure`).  The core facts (`maskPos_cy`, `realizes_true`,
`stepsOK_false`, all axiom-clean) cite no sorry'd constant and stay
green.
-/

namespace PaceStepsOKWitness

open Pace Cycle

/-- The two witness cards. -/
def a : Card := ⟨Suit.heart, Rank.ace⟩
def b : Card := ⟨Suit.heart, Rank.two⟩

/-- The impure initial state: cursor 1 of 2 (mid-pass at step 2). -/
def cy : Cycle Card := ⟨[a, b], 1⟩

theorem hs : 0 < 2 := by decide

-- Executable sanity probes (the refute-first protocol):
#eval maskPos cy 2 hs                        -- [0, 1]: position 0 leaks in via the leading lane
#eval cy.posOf a                             -- some 0
#eval laneAt [a, b] 2 [] a                   -- 0 ≠ 1: the first step condition fails

/-- The witness deck is duplicate-free. -/
theorem hnd : noDupCards [a, b] := by
  have hb : ∀ i ∈ List.range 2, ∀ j ∈ List.range 2,
      ([a, b] : List Card)[i]? = [a, b][j]? → i = j := by decide
  intro i j hi hj heq
  exact hb i (List.mem_range.mpr hi) j (List.mem_range.mpr hj) heq

theorem hcur : cy.cursor ≤ cy.cards.length := by decide

theorem hpos0 : cy.posOf a = some 0 := rfl

theorem hdraw0 : drawCard a cy = some ⟨[b], 0⟩ := rfl

theorem hpos1 : (⟨[b], 0⟩ : Cycle Card).posOf b = some 0 := rfl

theorem hdraw1 : drawCard b ⟨[b], 0⟩ = some ⟨[], 0⟩ := rfl

theorem mem0 : 0 ∈ maskPos cy 2 hs := by
  rw [maskPos_mem_iff cy 2 hs hcur]
  exact Or.inr (Or.inr ⟨by decide, by decide, by decide, by decide⟩)

theorem mem1 : 0 ∈ maskPos (⟨[b], 0⟩ : Cycle Card) 2 hs := by
  rw [maskPos_mem_iff _ 2 hs (by decide)]
  exact Or.inr (Or.inl ⟨by decide, by decide⟩)

/-- σ = [♥A, ♥2] realizes from the impure cursor: the first draw sits on
the initial leading lane, the second is the only card left. -/
theorem realizes_true : realizes 2 hs cy [a, b] := by
  show (∃ p, cy.posOf a = some p ∧ p ∈ maskPos cy 2 hs)
      ∧ ∃ c', drawCard a cy = some c' ∧ realizes 2 hs c' [b]
  refine ⟨⟨0, hpos0, mem0⟩, ⟨_, hdraw0, ?_⟩⟩
  show (∃ p, (⟨[b], 0⟩ : Cycle Card).posOf b = some p
        ∧ p ∈ maskPos ⟨[b], 0⟩ 2 hs)
      ∧ ∃ c', drawCard b ⟨[b], 0⟩ = some c' ∧ realizes 2 hs c' []
  exact ⟨⟨0, hpos1, mem1⟩, ⟨_, hdraw1, trivial⟩⟩

/-- But the sequence form rejects it: the first draw satisfies none of
the three step conditions. -/
theorem stepsOK_false : ¬ stepsOK [a, b] 2 [a, b] := by
  intro h
  have hstepOK := h [] a [b] (by rfl)
  rcases hstepOK with h1 | h2 | ⟨x, hx, _, _⟩
  · exact absurd h1 (by decide)
  · have hb := h2 b (by decide) (by decide)
    cases hb
  · simp at hx

/-- The staged iff fails on the witness (against the pre-repair
statement: cites the sorry'd `realizes_iff_stepsOK`). -/
theorem iff_refuted : ¬ (realizes 2 hs cy [a, b] ↔ stepsOK [a, b] 2 [a, b]) := by
  intro hiff
  exact stepsOK_false (hiff.mp realizes_true)

theorem broken : False := by
  have hiff := realizes_iff_stepsOK cy 2 hs hcur [a, b] (List.Perm.refl _) hnd
  exact iff_refuted hiff

end PaceStepsOKWitness
