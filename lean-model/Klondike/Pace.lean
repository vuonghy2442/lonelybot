import Klondike.State

/-!
# The draw pacing: the stock machine's accessible set, for any step

deck.rs's `compute_mask` (filter = false) over the K+ representation,
ported loop-for-loop and generalized over the draw step (the engine's
`draw_step : NonZeroU8`; step 3 is the ladder's draw-3).  Reference
ports: python/deck_sim.py (validated against the engine's winning
lines) and python/deck_bf.py (the validator: predicate ≡ mask on every
reachable state at N = 6/9/12/15, conditions ⟺ realizability over all
permutations at N = 6/9, 6k random sequences at N = 24 both
directions, all 56 corpus d3 winning draw lines).

The machine, any step ≥ 1: `maskPos` = loop 1 (the forward lane from
the cursor's waste top) ∪ {the last card} ∪ loop 2 (the batch-top
lane below the wrap end).  The characterization (`maskPos_mem_iff`):
position p is accessible iff

    p % step = step - 1 ∧ p < len - 1        (the top lane)
    ∨ 0 < len ∧ p = len - 1                  (the last card)
    ∨ 0 < cursor ∧ cursor - 1 ≤ p ∧ p < len - 1
      ∧ p % step = (cursor - 1) % step      (the leading lane)

For step = 1 the first disjunct is always true: the draw-1 deck is a
free set (`maskPos_step1`) — the K+ representation's own degeneration.

The characterization theorems carry the machine's cursor invariant
`cursor ≤ length` as a hypothesis (WF's stock conjunct, deck.rs's
`draw_cur ≤ len`): the engine never leaves that domain, and past
`len + 1` the wrapped lane's bound degenerates so out-of-range
positions leak into `maskPos` — the port-check grid stops at `n + 1`,
exactly the last state on the invariant's edge.

The sequence form (`realizes_iff_stepsOK`): a draw order is realizable
iff every consecutive pair satisfies lane-2 ∨ max-remaining ∨
leading-lane-with-burial — the statement the SAT ladder's rung 3
consumes.  The burial is the interval identity (`burial_bound`).

Saturation note: `Cycle.drawTo` lands the cursor at `i + 1` (deck.rs's
`set_offset`), so a last-position draw saturates at `length` (the
pass-end state) exactly like deck.rs — no divergence, and
`cursor_after` is exact (no mod needed).
-/

namespace Pace

open Cycle

/-! ## The accessible set

The machine's mask, ported loop-for-loop from deck.rs's
`iter_callback`/`compute_mask`, and its closed-form characterization
(the lanes and the last card).  This is what the game's
`State.reachablePos` consults. -/

/-- The loop shape of `iter_callback`: the arithmetic progression
`start, start + step, ...` strictly below `bound`. -/
def laneUp (step : Nat) (hstep : 0 < step) (start bound : Nat) : List Nat :=
  if start < bound then start :: laneUp step hstep (start + step) bound else []
  termination_by bound - start
  decreasing_by omega

/-- Loop membership, closed form: the progression from `start` below
`bound`. -/
theorem laneUp_mem (step : Nat) (hstep : 0 < step) (start bound p : Nat) :
    p ∈ laneUp step hstep start bound ↔
      start ≤ p ∧ p < bound ∧ (p - start) % step = 0 := by
  have key : ∀ a : Nat, (a + step) % step = a % step := by
    intro a
    rw [Nat.add_mod, Nat.mod_self, Nat.add_zero, Nat.mod_mod]
  have main : ∀ (fuel start bound p : Nat), bound ≤ start + fuel →
      (p ∈ laneUp step hstep start bound ↔
        start ≤ p ∧ p < bound ∧ (p - start) % step = 0) := by
    intro fuel
    induction fuel with
    | zero =>
        intro start bound p hb
        have hnl : ¬ start < bound := by omega
        rw [laneUp, if_neg hnl]
        constructor
        · intro hmem
          cases hmem
        · intro hmem
          omega
    | succ fuel ih =>
        intro start bound p hb
        rw [laneUp]
        by_cases hlt : start < bound
        · rw [if_pos hlt, List.mem_cons]
          constructor
          · rintro (rfl | hm)
            · exact ⟨by omega, hlt, by simp⟩
            · obtain ⟨h1, h2, h3⟩ := (ih (start + step) bound p (by omega)).mp hm
              refine ⟨by omega, h2, ?_⟩
              have h4 : p - (start + step) = p - start - step := by omega
              rw [h4] at h3
              have h5 : p - start = (p - start - step) + step := by omega
              rw [h5, key]
              exact h3
          · intro h
            obtain ⟨h1, h2, h3⟩ := h
            by_cases hp : p = start
            · exact Or.inl hp
            · right
              have hps : step ≤ p - start := by
                by_cases hcon : step ≤ p - start
                · exact hcon
                · have hlt2 : p - start < step := by omega
                  rw [Nat.mod_eq_of_lt hlt2] at h3
                  omega
              refine (ih (start + step) bound p (by omega)).mpr ⟨by omega, h2, ?_⟩
              have h6 : (p - (start + step)) + step = p - start := by omega
              rw [← h6] at h3
              rw [key (p - (start + step))] at h3
              exact h3
        · rw [if_neg hlt]
          constructor
          · intro hmem
            cases hmem
          · intro hmem
            omega
  exact main bound start bound p (by omega)

/-- deck.rs `compute_mask` (filter = false) as a list of positions:
loop 1 from the cursor's waste top, the last card (when any remain),
loop 2 from the first batch top up to the wrap end.  The two `if`s
mirror `iter_callback`'s `i0 = cursor + (step if cursor = 0 else 0) - 1`
and `end = (len if cursor % step ≠ 0 else cursor) - 1`; Nat
truncation gives `end = 0` at `cursor = 0`, and `step - 1 < 0` is
false, so loop 2 is empty — exactly deck_sim's `-1`.

Port-checked against deck_sim (pace_port_check.py): 260 states
(n ≤ 9, cursor ≤ n+1 including saturated, step 1..4), 0 mismatches. -/
def maskPos {α : Type} (c : Cycle α) (step : Nat) (hstep : 0 < step) : List Nat :=
  let n := c.cards.length
  let i0 := if c.cursor = 0 then step - 1 else c.cursor - 1
  let end2 := (if c.cursor % step != 0 then n else c.cursor) - 1
  laneUp step hstep i0 (n - 1)
  ++ (if 0 < n then [n - 1] else [])
  ++ laneUp step hstep (step - 1) end2

/-- A position `p ≥ a` whose distance to `a` is a step-multiple
carries `a`'s residue. -/
theorem mod_sub_of_eq_zero (step : Nat) (a p : Nat) (h : a ≤ p)
    (h0 : (p - a) % step = 0) : p % step = a % step := by
  have hp : p = (p - a) + a := by omega
  rw [hp, Nat.add_mod, h0, Nat.zero_add]
  exact Nat.mod_mod _ _

/-- Converse: a position `p ≥ a` with `p`'s residue equal to `a`'s
sits a step-multiple above `a`. -/
theorem mod_sub_eq_zero (step : Nat) (hstep : 0 < step) (a p : Nat) (h : a ≤ p)
    (hr : p % step = a % step) : (p - a) % step = 0 := by
  have hp : p = (p - a) + a := by omega
  have h1 : ((p - a) % step + a % step) % step = a % step := by
    rw [← Nat.add_mod, ← hp, hr]
  have hlt1 := Nat.mod_lt (p - a) hstep
  have hlt2 := Nat.mod_lt a hstep
  have hmd : ((p - a) % step + a % step) % step
      + step * (((p - a) % step + a % step) / step)
      = (p - a) % step + a % step :=
    Nat.mod_add_div ((p - a) % step + a % step) step
  rw [h1] at hmd
  cases hk : (((p - a) % step + a % step) / step) with
  | zero => rw [hk, Nat.mul_zero, Nat.add_zero] at hmd; omega
  | succ k => rw [hk, Nat.mul_succ] at hmd; omega

/-- The batch-top lane's residue: a step-multiple above `step - 1`
has residue exactly `step - 1`. -/
theorem residue_eq_top (step : Nat) (hstep : 0 < step) (p : Nat) (hle : step - 1 ≤ p)
    (h0 : (p - (step - 1)) % step = 0) : p % step = step - 1 := by
  rw [mod_sub_of_eq_zero step (step - 1) p hle h0,
    Nat.mod_eq_of_lt (by omega : step - 1 < step)]

theorem residue_top_le (step : Nat) (p : Nat) (h : p % step = step - 1) : step - 1 ≤ p := by
  have := Nat.mod_le p step
  omega

theorem residue_top_sub (step : Nat) (hstep : 0 < step) (p : Nat)
    (h : p % step = step - 1) : (p - (step - 1)) % step = 0 :=
  mod_sub_eq_zero step hstep (step - 1) p (residue_top_le step p h)
    (by rw [h, Nat.mod_eq_of_lt (by omega : step - 1 < step)])

/-- A step-aligned cursor's waste top carries the top residue: `o − 1`
sits one below a step-multiple, so its residue is `step − 1`. -/
theorem mod_sub_one_of_mod_zero (step : Nat) (hstep : 0 < step) (o : Nat)
    (h0 : o % step = 0) (hpos : 0 < o) : (o - 1) % step = step - 1 := by
  have ho : step * (o / step) = o := by
    have hd := Nat.div_add_mod o step
    rw [h0, Nat.add_zero] at hd
    exact hd
  have hq : 1 ≤ o / step := by
    by_cases hzero : o / step = 0
    · rw [hzero, Nat.mul_zero] at ho
      omega
    · exact Nat.pos_of_ne_zero hzero
  have hstepo : step ≤ o := by
    have h1 : step * 1 ≤ step * (o / step) := Nat.mul_le_mul_left step hq
    rw [Nat.mul_one] at h1
    omega
  have hle : step - 1 ≤ o - 1 := by omega
  have hmul : o - step = step * (o / step - 1) := by
    rw [Nat.mul_sub, Nat.mul_one]
    omega
  have hkey : ((o - 1) - (step - 1)) % step = 0 := by
    rw [show o - 1 - (step - 1) = o - step from by omega, hmul]
    exact Nat.mul_mod_right step (o / step - 1)
  have hfinal := mod_sub_of_eq_zero step (step - 1) (o - 1) hle hkey
  rw [Nat.mod_eq_of_lt (by omega : step - 1 < step)] at hfinal
  exact hfinal

/-- **The characterization** (deck_bf.py's `pred_positions`, validated
against the machine on every reachable state at N ≤ 15 for step 3):
a position is accessible iff it is on the batch-top lane, or is the
last card, or is on the leading lane from the cursor (the waste top
and its forward-dealing lane, bounded below by the burial).

`hcur` is the machine's cursor invariant `cursor ≤ length` (WF's stock
conjunct, deck.rs's `draw_cur ≤ len`) — without it the wrapped lane's
bound degenerates past `len + 1` and out-of-range positions leak in
(cf. `maskPos_step1`'s note). -/
theorem maskPos_mem_iff {α : Type} (c : Cycle α) (step : Nat) (hstep : 0 < step)
    (hcur : c.cursor ≤ c.cards.length)
    (p : Nat) :
    p ∈ maskPos c step hstep ↔
      (p % step = step - 1 ∧ p < c.cards.length - 1)
      ∨ (0 < c.cards.length ∧ p = c.cards.length - 1)
      ∨ (0 < c.cursor ∧ c.cursor - 1 ≤ p ∧ p < c.cards.length - 1
          ∧ p % step = (c.cursor - 1) % step) := by
  obtain ⟨cards, cursor⟩ := c
  have hcur : cursor ≤ cards.length := hcur
  have hmid : (p ∈ (if 0 < cards.length then [cards.length - 1] else []))
      ↔ (0 < cards.length ∧ p = cards.length - 1) := by
    by_cases hnpos : 0 < cards.length
    · rw [if_pos hnpos, List.mem_singleton]
      constructor
      · intro h
        exact ⟨hnpos, h⟩
      · intro h
        exact h.2
    · rw [if_neg hnpos]
      constructor
      · intro h
        cases h
      · intro h
        exact absurd h.1 hnpos
  simp only [maskPos, List.mem_append]
  rw [hmid]
  by_cases hbe : (cursor % step != 0) = true
  · -- mid-pass cursor: the wrapped lane's bound is the last card
    rw [if_pos hbe]
    have hc0 : cursor ≠ 0 := by
      intro h0
      subst h0
      rw [Nat.zero_mod] at hbe
      exact Bool.noConfusion hbe
    have hc0' : 0 < cursor := Nat.pos_of_ne_zero hc0
    rw [if_neg hc0]
    rw [laneUp_mem, laneUp_mem]
    constructor
    · rintro ((⟨h1, h2, h3⟩ | ⟨h4, hlast⟩) | ⟨h5, h6, h7⟩)
      · exact Or.inr (Or.inr ⟨hc0', h1, h2, mod_sub_of_eq_zero step (cursor - 1) p h1 h3⟩)
      · exact Or.inr (Or.inl ⟨h4, hlast⟩)
      · exact Or.inl ⟨residue_eq_top step hstep p h5 h7, h6⟩
    · rintro (⟨h1, h2⟩ | ⟨h4, hlast⟩ | ⟨h4, h1, h2, h3⟩)
      · exact Or.inr ⟨residue_top_le step p h1, h2,
          residue_top_sub step hstep p h1⟩
      · exact Or.inl (Or.inr ⟨h4, hlast⟩)
      · exact Or.inl (Or.inl ⟨h1, h2, mod_sub_eq_zero step hstep (cursor - 1) p h1 h3⟩)
  · rw [if_neg hbe]
    by_cases hc0 : cursor = 0
    · -- fresh pass: the leading lane is the batch-top lane itself
      rw [if_pos hc0]
      rw [laneUp_mem, laneUp_mem]
      constructor
      · rintro ((⟨h1, h2, h3⟩ | ⟨h4, hlast⟩) | ⟨h5, h6, h7⟩)
        · exact Or.inl ⟨residue_eq_top step hstep p h1 h3, h2⟩
        · exact Or.inr (Or.inl ⟨h4, hlast⟩)
        · omega
      · rintro (⟨h1, h2⟩ | ⟨h4, hlast⟩ | ⟨h4, h1, h2, h3⟩)
        · exact Or.inl (Or.inl ⟨residue_top_le step p h1, h2,
            residue_top_sub step hstep p h1⟩)
        · exact Or.inl (Or.inr ⟨h4, hlast⟩)
        · omega
    · -- aligned cursor: the wrapped lane degenerates below the cursor
      rw [if_neg hc0]
      have hc0' : 0 < cursor := Nat.pos_of_ne_zero hc0
      have h0 : cursor % step = 0 := by
        by_cases hx : cursor % step = 0
        · exact hx
        · exfalso
          apply hbe
          cases hq : (cursor % step == 0) with
          | true => exact absurd (eq_of_beq hq) hx
          | false =>
              rw [show (cursor % step != 0) = (!(cursor % step == 0)) from rfl, hq]
              rfl
      have hres : (cursor - 1) % step = step - 1 := by
        by_cases hs1 : step = 1
        · subst hs1
          omega
        · have hr := Nat.mod_lt (cursor - 1) hstep
          have hkey : ((cursor - 1) % step + 1) % step = 0 := by
            have h1m : 1 % step = 1 := Nat.mod_eq_of_lt (by omega : 1 < step)
            calc ((cursor - 1) % step + 1) % step
                = ((cursor - 1) % step + 1 % step) % step := by rw [h1m]
              _ = ((cursor - 1) + 1) % step := (Nat.add_mod _ _ _).symm
              _ = cursor % step := by rw [show cursor - 1 + 1 = cursor from by omega]
              _ = 0 := h0
          by_cases hlt : (cursor - 1) % step + 1 < step
          · rw [Nat.mod_eq_of_lt hlt] at hkey
            omega
          · omega
      rw [laneUp_mem, laneUp_mem]
      constructor
      · rintro ((⟨h1, h2, h3⟩ | ⟨h4, hlast⟩) | ⟨h5, h6, h7⟩)
        · exact Or.inr (Or.inr ⟨hc0', h1, h2, mod_sub_of_eq_zero step (cursor - 1) p h1 h3⟩)
        · exact Or.inr (Or.inl ⟨h4, hlast⟩)
        · refine Or.inl ⟨residue_eq_top step hstep p h5 h7, ?_⟩
          omega
      · rintro (⟨h1, h2⟩ | ⟨h4, hlast⟩ | ⟨h4, h1, h2, h3⟩)
        · by_cases hle : cursor - 1 ≤ p
          · exact Or.inl (Or.inl ⟨hle, h2, mod_sub_eq_zero step hstep (cursor - 1) p hle
              (by rw [h1, hres])⟩)
          · exact Or.inr ⟨residue_top_le step p h1, by omega,
              residue_top_sub step hstep p h1⟩
        · exact Or.inl (Or.inr ⟨h4, hlast⟩)
        · exact Or.inl (Or.inl ⟨h1, h2, mod_sub_eq_zero step hstep (cursor - 1) p h1 h3⟩)

/-- The draw-1 degeneration: with step 1 every position below the
length is accessible — the K+ representation's free set, as a theorem.
(Stated by membership: `maskPos` concatenates lanes out of order, so
the list-equality form is false.)

The hypothesis is the machine's cursor invariant `cursor ≤ length`
(WF's stock conjunct, deck.rs's `draw_cur ≤ len`): past `len + 1` the
wrapped lane's bound degenerates and positions beyond the length leak
into the mask — the engine never reaches such cursors. -/
theorem maskPos_step1 {α : Type} (c : Cycle α) (hstep : 0 < 1)
    (hcur : c.cursor ≤ c.cards.length) (p : Nat) :
    p ∈ maskPos c 1 hstep ↔ p < c.cards.length := by
  have hlane : ∀ start bound : Nat,
      (p ∈ laneUp 1 hstep start bound ↔ start ≤ p ∧ p < bound) := by
    intro start bound
    have h := laneUp_mem 1 hstep start bound p
    constructor
    · intro hm
      obtain ⟨h1, h2, -⟩ := h.mp hm
      exact ⟨h1, h2⟩
    · intro hm
      obtain ⟨h1, h2⟩ := hm
      exact h.mpr ⟨h1, h2, Nat.mod_one _⟩
  obtain ⟨cards, cursor⟩ := c
  have hcur : cursor ≤ cards.length := hcur
  cases cursor with
  | zero =>
      simp only [maskPos, Nat.mod_one]
      have hb : ((0 : Nat) != 0) = false := by decide
      rw [hb]
      simp
      rw [hlane, hlane]
      refine ⟨fun h => ?_, fun h => ?_⟩ <;> omega
  | succ m =>
      simp only [maskPos, Nat.mod_one]
      have hb : ((0 : Nat) != 0) = false := by decide
      rw [hb, if_neg (Nat.succ_ne_zero m)]
      simp
      rw [hlane, hlane]
      refine ⟨fun h => ?_, fun h => ?_⟩ <;> omega

/-! ## The pace order — the offset-dominance family

The order the search's refuted-offset registry stands on (engine side,
2026-09: the registry rules R1/R2, measured at 43.8% of seed-32 draw-3
states doomed — 1.38M of 3.15M, of which 912k pure states killed by
impure siblings; draw-1 exactly 0, the normalization's degeneration).
Rust falsifier: `pace_dominance_order` (src/macro_game.rs — 100 random
decks × every offset).  The game-level exploit is Macro.lean's
`pace_dominance`. -/

/-- The pure-pure equality: every pure cursor — aligned
(`o % step = 0`, including 0) or at the pass end (`o = length`) —
accesses the same set: the batch-top lane plus the last card.  This
*derives* deck.rs's `is_pure`/`normalized_offset` encode merge (the
offset normalization draw-1 gets everywhere, draw-3 gets on the pure
class) from the machine's formula instead of asserting it.

A pure cursor's leading lane has residue `(o − 1) % step = step − 1`
(`mod_sub_one_of_mod_zero`; vacuous at `o = 0` or the pass end), so it
subsumes into the batch-top disjunct — both sides reduce to
`p % step = step - 1 ∧ p < n - 1` plus the last card. -/
theorem maskPos_pure_indep {α : Type} (c c' : Cycle α) (step : Nat) (hstep : 0 < step)
    (hc : c.cards = c'.cards)
    (hcur : c.cursor ≤ c.cards.length) (hcur' : c'.cursor ≤ c'.cards.length)
    (hpure : c.cursor % step = 0 ∨ c.cursor = c.cards.length)
    (hpure' : c'.cursor % step = 0 ∨ c'.cursor = c'.cards.length) :
    ∀ p, p ∈ maskPos c step hstep ↔ p ∈ maskPos c' step hstep := by
  intro p
  rw [maskPos_mem_iff c step hstep hcur p, maskPos_mem_iff c' step hstep hcur' p]
  have hlen : c'.cards.length = c.cards.length := by rw [hc]
  rw [hlen]
  -- a pure cursor's leading lane subsumes into the batch-top disjunct
  have key : ∀ (cy : Cycle α) (n : Nat), (cy.cursor % step = 0 ∨ cy.cursor = n) →
      (0 < cy.cursor ∧ cy.cursor - 1 ≤ p ∧ p < n - 1
        ∧ p % step = (cy.cursor - 1) % step) →
      (p % step = step - 1 ∧ p < n - 1) := by
    intro cy n hpure lane
    rcases hpure with hm | he
    · rw [mod_sub_one_of_mod_zero step hstep cy.cursor hm lane.1] at lane
      exact ⟨lane.2.2.2, lane.2.2.1⟩
    · omega
  constructor
  · rintro (h1 | ⟨h4, hlast⟩ | lane)
    · exact Or.inl h1
    · exact Or.inr (Or.inl ⟨h4, hlast⟩)
    · exact Or.inl (key c c.cards.length hpure lane)
  · rintro (h1 | ⟨h4, hlast⟩ | lane)
    · exact Or.inl h1
    · exact Or.inr (Or.inl ⟨h4, hlast⟩)
    · refine Or.inl (key c' c.cards.length ?_ lane)
      rcases hpure' with hm | he
      · exact Or.inl hm
      · exact Or.inr (by omega)

/-- Residue monotonicity: within an impure residue class, the earlier
cursor accesses more — `K(o) ⊇ K(o')` when `o ≤ o'` and
`o % step = o' % step ≠ 0`.  The mechanism: `iter_callback`'s leading
lane starts at `o - 1` (lower for smaller `o`) while the batch-top lane
and the last card are class-invariant.

The first two disjuncts of `maskPos_mem_iff` are cursor-free; the
leading lane's bound `o' - 1 ≤ p` weakens to `o - 1 ≤ p` by `hle`,
the residues agree by `hres`, and `0 < o'` gives `0 < o`. -/
theorem maskPos_residue_mono {α : Type} (c c' : Cycle α) (step : Nat) (hstep : 0 < step)
    (hc : c.cards = c'.cards)
    (hle : c.cursor ≤ c'.cursor)
    (hres : c.cursor % step = c'.cursor % step)
    (himp : c'.cursor % step ≠ 0)
    (hcur : c.cursor ≤ c.cards.length) (hcur' : c'.cursor ≤ c'.cards.length) :
    ∀ p, p ∈ maskPos c' step hstep → p ∈ maskPos c step hstep := by
  intro p hp
  rw [maskPos_mem_iff c' step hstep hcur' p] at hp
  have hlen : c'.cards.length = c.cards.length := by rw [hc]
  rcases hp with h1 | ⟨h4, hlast⟩ | ⟨hpos, hbound, hlt, hlane⟩
  · rw [hlen] at h1
    exact (maskPos_mem_iff c step hstep hcur p).mpr (Or.inl h1)
  · rw [hlen] at hlast
    exact (maskPos_mem_iff c step hstep hcur p).mpr (Or.inr (Or.inl ⟨by omega, hlast⟩))
  · have ho : 0 < c.cursor := by
      rcases Nat.eq_zero_or_pos c.cursor with h0 | h0
      · exfalso
        rw [h0, Nat.zero_mod] at hres
        exact himp hres.symm
      · exact h0
    -- (o' - 1) % step = (o - 1) % step, via the class agreement
    have hsub : (c'.cursor - c.cursor) % step = 0 :=
      mod_sub_eq_zero step hstep c.cursor c'.cursor hle hres.symm
    have hres' : (c'.cursor - 1) % step = (c.cursor - 1) % step := by
      refine mod_sub_of_eq_zero step (c.cursor - 1) (c'.cursor - 1) (by omega) ?_
      rw [show c'.cursor - 1 - (c.cursor - 1) = c'.cursor - c.cursor from by omega]
      exact hsub
    exact (maskPos_mem_iff c step hstep hcur p).mpr
      (Or.inr (Or.inr ⟨ho, by omega, by rw [hlen] at hlt; exact hlt,
        by rw [← hres']; exact hlane⟩))

/-- Impure over pure: any mid-pass cursor's accessible set contains the
pass-boundary (pure) one — the impure set is the pure set (batch-top
lane + last card) *plus* a nonempty leading lane.

The pure side reduces to the two cursor-free disjuncts (the pure
cursor's leading lane either carries the top residue — subsumed by the
batch-top disjunct — or is vacuous at the pass end), which the impure
side's first two disjuncts already cover. -/
theorem maskPos_impure_sup_pure {α : Type} (c c' : Cycle α) (step : Nat) (hstep : 0 < step)
    (hc : c.cards = c'.cards)
    (himp : c.cursor % step ≠ 0)
    (hpure' : c'.cursor % step = 0 ∨ c'.cursor = c'.cards.length)
    (hcur : c.cursor ≤ c.cards.length) (hcur' : c'.cursor ≤ c'.cards.length) :
    ∀ p, p ∈ maskPos c' step hstep → p ∈ maskPos c step hstep := by
  have := himp
  intro p hp
  rw [maskPos_mem_iff c' step hstep hcur' p] at hp
  have hlen : c'.cards.length = c.cards.length := by rw [hc]
  rcases hp with h1 | ⟨h4, hlast⟩ | ⟨hpos, hbound, hlt, hlane⟩
  · rw [hlen] at h1
    exact (maskPos_mem_iff c step hstep hcur p).mpr (Or.inl h1)
  · rw [hlen] at hlast
    exact (maskPos_mem_iff c step hstep hcur p).mpr (Or.inr (Or.inl ⟨by omega, hlast⟩))
  · rcases hpure' with hm | he
    · refine (maskPos_mem_iff c step hstep hcur p).mpr (Or.inl ⟨?_, by
        rw [hlen] at hlt; exact hlt⟩)
      rw [← mod_sub_one_of_mod_zero step hstep c'.cursor hm hpos]
      exact hlane
    · omega

/-! ## The draw machine

The bare-cycle machine the sequence form talks about: one draw is
deck.rs's `draw(id)` — the jump (`drawTo`) plus the splice
(`removeAt`) — and realizability consults the accessible set at every
moment.  The game-side counterparts are `State.applyDrawTo` /
`applyDrawStackTo` (guarded by `State.reachablePos`) and the
jump-soundness theorems connect the two. -/

/-- One draw of the machine (deck.rs `draw(id)` = set_offset(id+1) +
pop_next): jump so `x` is the waste top, then splice it out. -/
def drawCard (x : Card) (c : Cycle Card) : Option (Cycle Card) :=
  match c.posOf x with
  | none => none
  | some i => some ((c.drawTo i).removeAt i)

/-- The draw successor's shape: jump past `i`, then splice `i` out —
the cursor lands exactly on `i` (deck.rs's `set_offset(id+1)` +
`pop_next`).  The source cursor is nowhere in the result. -/
theorem removeAt_drawTo_eq {α : Type} (i : Nat) (cy : Cycle α) :
    (cy.drawTo i).removeAt i = ⟨Cycle.removeIdx cy.cards i, i⟩ := by
  simp only [Cycle.removeAt, Cycle.drawTo, if_pos (by omega : i < i + 1),
    Nat.add_sub_cancel]

/-- The merge lemma: `drawCard` reads only the cards — the jump target
is `posOf` (cards-only), `drawTo` *overwrites* the cursor with `i + 1`,
and `removeAt` computes the successor cursor from that overwritten value
(`if i < i + 1 then i + 1 - 1` = `i`) — so two cycles with the same
cards draw any card to the *identical* successor.  This is what makes
winning lines merge after one common draw, the load-bearing step of
Macro.lean's `pace_dominance` replay. -/
theorem drawCard_cursor_indep (c c' : Cycle Card) (x : Card) (hc : c.cards = c'.cards) :
    drawCard x c = drawCard x c' := by
  have hpos : c.posOf x = c'.posOf x := by
    simp only [Cycle.posOf, hc]
  simp only [drawCard, hpos]
  cases hc2 : c'.posOf x with
  | none => rfl
  | some i =>
      show some ((c.drawTo i).removeAt i) = some ((c'.drawTo i).removeAt i)
      rw [removeAt_drawTo_eq i c, removeAt_drawTo_eq i c', hc]

/-! ### The posOf ↔ idxOf bridge

`Cycle.posOf` (first occurrence, `Option`) and `List.idxOf` (first
occurrence, `Nat`) agree on members, which makes the counting kit
(Kit.lean) applicable to the machine's positions.  Pace-local names:
Move.lean's `Cycle.posOf_*` family sits downstream of this file —
consolidation pass. -/

/-- A found first index points at the card. -/
theorem findFirstIdx_get : ∀ (l : List Card) (w : Card) (i : Nat),
    Cycle.findFirstIdx (fun c' => decide (c' = w)) l = some i → l[i]? = some w := by
  intro l
  induction l with
  | nil => intro w i h; simp [Cycle.findFirstIdx] at h
  | cons a t ih =>
      intro w i h
      simp only [Cycle.findFirstIdx] at h
      by_cases haw : a = w
      · have hp : decide (a = w) = true := by simp [haw]
        rw [if_pos hp, Option.some.injEq] at h
        rw [← h, List.getElem?_cons_zero, haw]
      · have hpn : ¬(decide (a = w) = true) := by simp [haw]
        rw [if_neg hpn] at h
        cases hq : Cycle.findFirstIdx (fun c' => decide (c' = w)) t with
        | none => rw [hq] at h; simp at h
        | some j =>
            rw [hq, Option.map_some, Option.some.injEq] at h
            rw [← h, List.getElem?_cons_succ]
            exact ih w j hq

/-- A successful position search witnesses membership. -/
theorem mem_of_posOf : ∀ (l : List Card) (cur : Nat) (w : Card) (i : Nat),
    posOf w ⟨l, cur⟩ = some i → w ∈ l := by
  intro l
  induction l with
  | nil => intro cur w i h; simp [posOf, Cycle.findFirstIdx] at h
  | cons a t ih =>
      intro cur w i h
      simp only [posOf, Cycle.findFirstIdx] at h
      by_cases haw : a = w
      · rw [haw]
        exact List.mem_cons.mpr (Or.inl rfl)
      · have hpn : ¬(decide (a = w) = true) := by simp [haw]
        rw [if_neg hpn] at h
        cases hq : Cycle.findFirstIdx (fun c' => decide (c' = w)) t with
        | none => rw [hq] at h; simp at h
        | some j =>
            rw [hq, Option.map_some, Option.some.injEq] at h
            exact List.mem_cons_of_mem _ (ih cur w j hq)

/-- On members, `posOf` is `idxOf`. -/
theorem posOf_eq_idxOf : ∀ (l : List Card) (cur : Nat) (w : Card), w ∈ l →
    posOf w ⟨l, cur⟩ = some (l.idxOf w) := by
  intro l
  induction l with
  | nil => intro cur w h; cases h
  | cons a t ih =>
      intro cur w h
      by_cases haw : a = w
      · have hp : decide (a = w) = true := by simp [haw]
        simp only [posOf, Cycle.findFirstIdx]
        rw [if_pos hp, haw, List.idxOf_cons_self]
      · have hpn : ¬(decide (a = w) = true) := by simp [haw]
        have hwt : w ∈ t := (List.mem_cons.mp h).resolve_left (Ne.symm haw)
        have hih : Cycle.findFirstIdx (fun c' => decide (c' = w)) t
            = some (t.idxOf w) := ih cur w hwt
        simp only [posOf, Cycle.findFirstIdx]
        rw [if_neg hpn, hih, Option.map_some, idxOf_cons_ne haw]

/-- The deterministic machine run over a draw order. -/
def run (c : Cycle Card) : List Card → Option (Cycle Card)
  | [] => some c
  | x :: xs => match drawCard x c with
    | some c' => run c' xs
    | none => none

/-! ### The run kit

What a successful run preserves: every drawn card was in the deck, the
draw order is duplicate-free, and the end deck is the original minus the
drawn cards — as a filter (order included).  These feed `pos_shift`
and `cursor_after`. -/

/-- Every card a successful run drew was in the deck. -/
theorem run_mem : ∀ (l : List Card) (c c' : Cycle Card), run c l = some c' →
    ∀ z ∈ l, z ∈ c.cards := by
  intro l
  induction l with
  | nil => intro c c' _ z hz; cases hz
  | cons x xs ih =>
      intro c c' hrun z hz
      simp only [run] at hrun
      cases hdc : drawCard x c with
      | none => rw [hdc] at hrun; simp at hrun
      | some c₁ =>
          rw [hdc] at hrun
          have hrun' : run c₁ xs = some c' := hrun
          simp only [drawCard] at hdc
          cases hp : c.posOf x with
          | none => rw [hp] at hdc; simp at hdc
          | some i =>
              rw [hp] at hdc
              have hinj : (c.drawTo i).removeAt i = c₁ := Option.some.inj hdc
              rcases List.mem_cons.mp hz with hzx | hzs
              · rw [hzx]
                exact mem_of_posOf c.cards c.cursor x i hp
              · have hz1 : z ∈ c₁.cards := ih c₁ c' hrun' z hzs
                rw [← hinj, removeAt_drawTo_eq i c] at hz1
                exact mem_removeIdx_of hz1

/-- A successful run's draw order is duplicate-free. -/
theorem run_pre_nodup : ∀ (pre : List Card) (c c' : Cycle Card), run c pre = some c' →
    noDupCards c.cards → (∀ z ∈ pre, z ∈ c.cards) → noDupCards pre := by
  intro pre
  induction pre with
  | nil => intro c c' _ _ _ i j hi; simp only [List.length_nil] at hi; omega
  | cons x xs ih =>
      intro c c' hrun hnd hsub
      simp only [run] at hrun
      cases hdc : drawCard x c with
      | none => rw [hdc] at hrun; simp at hrun
      | some c₁ =>
          rw [hdc] at hrun
          have hrun' : run c₁ xs = some c' := hrun
          simp only [drawCard] at hdc
          cases hp : c.posOf x with
          | none => rw [hp] at hdc; simp at hdc
          | some i =>
              rw [hp] at hdc
              have hc₁ : c₁ = ⟨Cycle.removeIdx c.cards i, i⟩ :=
                (Option.some.inj hdc).symm.trans (removeAt_drawTo_eq i c)
              have hmem : x ∈ c.cards := hsub x (by simp)
              have hget : c.cards[i]? = some x := findFirstIdx_get c.cards x i hp
              have hsub' : ∀ z ∈ xs, z ∈ c₁.cards := fun z hz => run_mem xs c₁ c' hrun' z hz
              have hxnot : x ∉ c₁.cards := by
                intro hcon
                rw [hc₁] at hcon
                exact ((mem_removeIdx_iff hnd hget x).mp hcon).2 rfl
              have hndxs : noDupCards xs :=
                ih c₁ c' hrun'
                  (by rw [hc₁]; exact noDupCards_removeIdx c.cards i hnd) hsub'
              refine NoDupP_noDupCards ⟨?_, noDupCards_NoDupP hndxs⟩
              intro hxmem
              exact hxnot (hsub' x hxmem)

/-- After a successful run, the end deck is the original minus the drawn
cards — as a filter (order included). -/
theorem run_cards_filter : ∀ (pre : List Card) (c c' : Cycle Card), run c pre = some c' →
    noDupCards c.cards → (∀ z ∈ pre, z ∈ c.cards) →
    c'.cards = c.cards.filter (fun z => decide (z ∉ pre)) := by
  intro pre
  induction pre with
  | nil =>
      intro c c' hrun _ _
      simp only [run] at hrun
      rw [Option.some.injEq] at hrun
      rw [← hrun]
      exact (filter_true_id c.cards).symm.trans (List.filter_congr fun z _ => by simp)
  | cons x xs ih =>
      intro c c' hrun hnd hsub
      simp only [run] at hrun
      cases hdc : drawCard x c with
      | none => rw [hdc] at hrun; simp at hrun
      | some c₁ =>
          rw [hdc] at hrun
          have hrun' : run c₁ xs = some c' := hrun
          simp only [drawCard] at hdc
          cases hp : c.posOf x with
          | none => rw [hp] at hdc; simp at hdc
          | some i =>
              rw [hp] at hdc
              have hinj : (c.drawTo i).removeAt i = c₁ := Option.some.inj hdc
              have hmem : x ∈ c.cards := hsub x (by simp)
              have hget : c.cards[i]? = some x := findFirstIdx_get c.cards x i hp
              have hsub' : ∀ z ∈ xs, z ∈ c₁.cards := fun z hz => run_mem xs c₁ c' hrun' z hz
              have hnd' : noDupCards c₁.cards := by
                rw [← hinj, removeAt_drawTo_eq i c]
                exact noDupCards_removeIdx c.cards i hnd
              have hih : c'.cards = c₁.cards.filter (fun z => decide (z ∉ xs)) :=
                ih c₁ c' hrun' hnd' hsub'
              have hfilter : c₁.cards = c.cards.filter (fun z => decide (z ≠ x)) := by
                rw [← hinj, removeAt_drawTo_eq i c]
                show Cycle.removeIdx c.cards i = c.cards.filter (fun z => decide (z ≠ x))
                rw [removeIdx_filter_mem c.cards i hnd]
                exact List.filter_congr fun z hz => by
                  by_cases hzx : z = x
                  · rw [hzx]
                    have hx' : ¬ (x ∈ Cycle.removeIdx c.cards i) := by
                      rw [mem_removeIdx_iff hnd hget x]
                      exact fun hc => hc.2 rfl
                    simp [hx']
                  · have hz' : z ∈ Cycle.removeIdx c.cards i :=
                      (mem_removeIdx_iff hnd hget z).mpr ⟨hz, hzx⟩
                    simp [hz', hzx]
              rw [hih, hfilter, List.filter_filter]
              exact List.filter_congr fun z _ => by
                by_cases hzx : z = x
                · rw [hzx]
                  simp
                · by_cases hzxs : z ∈ xs
                  · simp [hzxs, List.mem_cons]
                  · simp [hzx, hzxs, List.mem_cons]

/-- Realizability of a draw order: every drawn card was accessible
(`maskPos`) at its moment. -/
def realizes (step : Nat) (hstep : 0 < step) (c : Cycle Card) :
    List Card → Prop
  | [] => True
  | x :: xs =>
      (∃ p, c.posOf x = some p ∧ p ∈ maskPos c step hstep)
      ∧ ∃ c', drawCard x c = some c' ∧ realizes step hstep c' xs

/-! ## The sequence form: lanes, burial, intervals

The per-draw conditions on the original deck order — the statement
the SAT ladder's rung 3 consumes. -/

/-- r(w): how many already-drawn cards sit below `w` in the original
deck order — the counting part of the pass structure. -/
def rBelow (d : List Card) (pre : List Card) (w : Card) : Nat :=
  (pre.filter (fun z => d.idxOf z < d.idxOf w)).length

/-- The lane of `w` at its draw: (O(w) - r(w)) % step. -/
def laneAt (d : List Card) (step : Nat) (pre : List Card) (w : Card) : Nat :=
  (d.idxOf w - rBelow d pre w) % step

/-- `w` is the max remaining card at its draw: every original-above
card was already drawn. -/
def maxRem (d : List Card) (pre : List Card) (w : Card) : Prop :=
  ∀ z ∈ d, d.idxOf w < d.idxOf z → z ∈ pre

/-- The burial interval for the leading lane: when O(w) < O(x), every
card in [O(w), O(x)) besides `w` itself was drawn before `x`. -/
def intervalOK (d : List Card) (before : List Card) (x w : Card) : Prop :=
  d.idxOf w < d.idxOf x →
    ∀ z ∈ d, d.idxOf w ≤ d.idxOf z → d.idxOf z < d.idxOf x → z = w ∨ z ∈ before

/-- The per-draw condition: `w`, drawn after `pre`, is accessible.
The first draw is `pre = []`: the leading lane has no predecessor, so
the condition degenerates to lane-2 ∨ max-remaining. -/
def stepOK (d : List Card) (step : Nat) (pre : List Card) (w : Card) : Prop :=
  laneAt d step pre w = step - 1
  ∨ maxRem d pre w
  ∨ (∃ x, pre.getLast? = some x ∧
      laneAt d step pre w = (laneAt d step pre.dropLast x + step - 1) % step ∧
      intervalOK d pre.dropLast x w)

/-- The sequence form: every draw of `σ` satisfies its step
condition (`pre` = the cards drawn before it). -/
def stepsOK (d : List Card) (step : Nat) (σ : List Card) : Prop :=
  ∀ pre w rest, σ = pre ++ [w] ++ rest → stepOK d step pre w

/-! ## The correspondence theorems

The machine ↔ sequence-form bridge: the position shift, the cursor
placement, the burial identity, and the master equivalence. -/

/-- rBelow steps over a single-suffix append: the appended card counts
iff it sits below `w` in the deck order. -/
theorem rBelow_append_single (d init : List Card) (x w : Card) :
    rBelow d (init ++ [x]) w
      = rBelow d init w + (if d.idxOf x < d.idxOf w then 1 else 0) := by
  simp only [rBelow, List.filter_append, List.length_append]
  have hsingle : ([x].filter (fun z => decide (d.idxOf z < d.idxOf w))).length
      = (if d.idxOf x < d.idxOf w then 1 else 0) := by
    rw [List.filter_cons, List.filter_nil]
    by_cases hxw : d.idxOf x < d.idxOf w
    · rw [if_pos (show decide (d.idxOf x < d.idxOf w) = true from by simp [hxw]),
        if_pos hxw, List.length_cons, List.length_nil]
    · rw [if_neg (show ¬(decide (d.idxOf x < d.idxOf w) = true) from by simp [hxw]),
        if_neg hxw, List.length_nil]
  rw [hsingle]

/-- The interval count: on a distinct deck, the cards with `idxOf` in
`[a, b)` number exactly `b - a`. -/
theorem count_interval (d : List Card) (hnd : noDupCards d) {a b : Nat}
    (ha : a < d.length) (hab : a ≤ b) (hb : b < d.length) :
    (d.filter (fun z => decide (a ≤ d.idxOf z ∧ d.idxOf z < b))).length = b - a := by
  have hca : (d.filter (fun z => decide (d.idxOf z < a))).length = a :=
    count_below hnd (by omega)
  have hcb : (d.filter (fun z => decide (d.idxOf z < b))).length = b :=
    count_below hnd (by omega)
  have hsplit := filter_split_add (fun z => decide (d.idxOf z < b))
    (fun z => decide (d.idxOf z < a)) d
  have c1 : d.filter (fun z => decide (d.idxOf z < b) && decide (d.idxOf z < a))
      = d.filter (fun z => decide (d.idxOf z < a)) := by
    refine List.filter_congr fun z hz => ?_
    by_cases h1 : d.idxOf z < a
    · rw [decide_eq_true h1, Bool.and_true, decide_eq_true (by omega : d.idxOf z < b)]
    · rw [decide_eq_false h1, Bool.and_false]
  have c2 : d.filter (fun z => decide (d.idxOf z < b) && !decide (d.idxOf z < a))
      = d.filter (fun z => decide (a ≤ d.idxOf z ∧ d.idxOf z < b)) := by
    refine List.filter_congr fun z hz => ?_
    by_cases h1 : d.idxOf z < a
    · rw [decide_eq_true h1, Bool.not_true, Bool.and_false,
        decide_eq_false (by omega : ¬(a ≤ d.idxOf z ∧ d.idxOf z < b))]
    · rw [decide_eq_false h1, Bool.not_false, Bool.and_true]
      by_cases h2 : d.idxOf z < b
      · rw [decide_eq_true h2, decide_eq_true (by omega : a ≤ d.idxOf z ∧ d.idxOf z < b)]
      · rw [decide_eq_false h2,
          decide_eq_false (by omega : ¬(a ≤ d.idxOf z ∧ d.idxOf z < b))]
  rw [hsplit, c1, c2] at hcb
  omega

/-- The counting identity: after a run of `pre`, a not-yet-drawn
card's position is its original index minus the drawn-below count
(removeIdx preserves order and shifts later positions down one;
`rBelow` counts exactly the removed-below — the end deck is the
original filtered by `∉ pre`, and a member's index in a filter counts
the passing cards before it).

`hnd` is necessary: with duplicates the run can draw the same value
twice (the second find succeeds at the shifted position) while
`rBelow` counts by `idxOf`, over-counting the shift. -/
theorem pos_shift (c c' : Cycle Card) (pre : List Card) (w : Card)
    (hrun : run c pre = some c') (hsub : ∀ z ∈ pre, z ∈ c.cards)
    (hnd : noDupCards c.cards)
    (hw : w ∈ c.cards) (hnotin : w ∉ pre) :
    c'.posOf w = some (c.cards.idxOf w - rBelow c.cards pre w) := by
  have hfilter := run_cards_filter pre c c' hrun hnd hsub
  have hndpre : noDupCards pre := run_pre_nodup pre c c' hrun hnd hsub
  have hw' : w ∈ c'.cards := by
    rw [hfilter]
    exact List.mem_filter.mpr ⟨hw, by simp [hnotin]⟩
  have hpos : c'.posOf w = some (c'.cards.idxOf w) := posOf_eq_idxOf c'.cards c'.cursor w hw'
  rw [hpos, hfilter]
  have hG := idxOf_filter (p := fun z => decide (z ∉ pre)) c.cards w hw (by simp [hnotin])
  rw [hG]
  have hsplit := filter_split_compl (fun z => decide (z ∉ pre))
    (c.cards.take (c.cards.idxOf w))
  have hcongr : (c.cards.take (c.cards.idxOf w)).filter (fun z => !decide (z ∉ pre))
      = (c.cards.take (c.cards.idxOf w)).filter (fun z => decide (z ∈ pre)) :=
    List.filter_congr fun z _ => by by_cases hzp : z ∈ pre <;> simp [hzp]
  rw [hcongr] at hsplit
  have hcount : ((c.cards.take (c.cards.idxOf w)).filter
      (fun z => decide (z ∈ pre))).length = rBelow c.cards pre w :=
    filter_mem_take_count hnd hndpre hsub (c.cards.idxOf w)
  have htake : (c.cards.take (c.cards.idxOf w)).length = c.cards.idxOf w := by
    rw [List.length_take]
    have := idxOf_lt_length hw
    omega
  refine congrArg some ?_
  omega

/-- After drawing `pre ++ [w]`, the cursor sits exactly at w's
draw-time position: the jump lands `i + 1` and the splice steps back
to `i`; a last-position draw saturates at `length - 1` = the new
length, which is the draw-time position — both conventions, one
exact statement (`pos_shift` supplies `i`). -/
theorem cursor_after (c c' c'' : Cycle Card) (pre : List Card) (w : Card)
    (hrun : run c pre = some c') (hdraw : drawCard w c' = some c'')
    (hsub : ∀ z ∈ w :: pre, z ∈ c.cards) (hndpre : noDupCards (w :: pre))
    (hnd : noDupCards c.cards) :
    c''.cursor = c.cards.idxOf w - rBelow c.cards pre w := by
  have hnotin : w ∉ pre := (noDupCards_NoDupP hndpre).1
  have hw : w ∈ c.cards := hsub w (by simp)
  have hsub' : ∀ z ∈ pre, z ∈ c.cards := fun z hz => hsub z (by simp [hz])
  have hpos := pos_shift c c' pre w hrun hsub' hnd hw hnotin
  simp only [drawCard] at hdraw
  cases hp : c'.posOf w with
  | none => rw [hp] at hdraw; simp at hdraw
  | some i =>
      rw [hp] at hdraw
      have hinj : (c'.drawTo i).removeAt i = c'' := Option.some.inj hdraw
      rw [← hinj, removeAt_drawTo_eq i c']
      have hi : some i = some (c.cards.idxOf w - rBelow c.cards pre w) := by
        rw [← hp]; exact hpos
      exact Option.some.inj hi

/-- The interval identity: the burial condition is exactly the
leading-lane position bound P(w) ≥ P(x) - 1, where P(v) is v's
position at its draw (`idxOf v` minus its `rBelow`).  Both directions:
the between-count saturates iff every interval card besides `w` was
drawn before `x` (on the distinct deck, the interval [O(w), O(x))
holds exactly O(x) − O(w) cards — `count_interval`; the init-side and
deck-side counts are compared by pigeonhole; with O(x) < O(w) the
left side is vacuous and the right side holds by the same counting). -/
theorem burial_bound (d : List Card) (pre : List Card) (x w : Card)
    (hnd : noDupCards d) (hsub : ∀ z ∈ pre, z ∈ d)
    (hndpre : noDupCards pre) (hx : x ∈ d) (hw : w ∈ d)
    (hnotin : w ∉ pre) (hend : ∃ init, pre = init ++ [x]) :
    intervalOK d pre.dropLast x w ↔
      d.idxOf x - rBelow d pre.dropLast x - 1 ≤ d.idxOf w - rBelow d pre w := by
  obtain ⟨init, hpre⟩ := hend
  subst hpre
  rw [dropLast_append_single]
  have hxne : x ≠ w := by
    intro hcon
    exact hnotin (by rw [hcon]; exact List.mem_append_right init (by simp))
  have haxw : d.idxOf x ≠ d.idxOf w := fun hcon => hxne (idxOf_inj hx hw hcon)
  have hndinit : noDupCards init := by
    intro i j hi hj heq
    have h1 : (init ++ [x])[i]? = init[i]? := List.getElem?_append_left (by omega)
    have h2 : (init ++ [x])[j]? = init[j]? := List.getElem?_append_left (by omega)
    have hb1 : i < (init ++ [x]).length := by
      simp only [List.length_append, List.length_singleton]; omega
    have hb2 : j < (init ++ [x]).length := by
      simp only [List.length_append, List.length_singleton]; omega
    exact hndpre i j hb1 hb2 (by rw [h1, h2]; exact heq)
  have hwNotInit : w ∉ init := fun hc => hnotin (List.mem_append.mpr (Or.inl hc))
  have hinitsub : ∀ z ∈ init, z ∈ d := fun z hz => hsub z (List.mem_append.mpr (Or.inl hz))
  have hrw : rBelow d (init ++ [x]) w
      = rBelow d init w + (if d.idxOf x < d.idxOf w then 1 else 0) :=
    rBelow_append_single d init x w
  have hax : d.idxOf x < d.length := idxOf_lt_length hx
  have haw : d.idxOf w < d.length := idxOf_lt_length hw
  by_cases hlt : d.idxOf w < d.idxOf x
  · -- O(w) < O(x): both sides are |A| ≤ |B|
    have hrw0 : rBelow d (init ++ [x]) w = rBelow d init w := by
      rw [hrw, if_neg (by omega : ¬(d.idxOf x < d.idxOf w)), Nat.add_zero]
    -- |A| = O(x) - O(w) - 1, A = the interval strictly above w
    have hAcount : (d.filter (fun z => decide (d.idxOf w < d.idxOf z ∧ d.idxOf z < d.idxOf x))).length
        = d.idxOf x - d.idxOf w - 1 := by
      have hc := count_interval d hnd (a := d.idxOf w + 1) (b := d.idxOf x)
        (by omega) (by omega) (by omega)
      have hcongr : d.filter (fun z => decide (d.idxOf w + 1 ≤ d.idxOf z ∧ d.idxOf z < d.idxOf x))
          = d.filter (fun z => decide (d.idxOf w < d.idxOf z ∧ d.idxOf z < d.idxOf x)) :=
        List.filter_congr fun z _ => rfl
      rw [hcongr] at hc
      omega
    -- |B| + r(init, w) = r(init, x), B = init ∩ interval
    have hBcount : (init.filter (fun z => decide (d.idxOf w < d.idxOf z ∧ d.idxOf z < d.idxOf x))).length
        + rBelow d init w = rBelow d init x := by
      have hsplit := filter_split_add (fun z => decide (d.idxOf z < d.idxOf x))
        (fun z => decide (d.idxOf w < d.idxOf z)) init
      have cB : init.filter (fun z => decide (d.idxOf z < d.idxOf x) && decide (d.idxOf w < d.idxOf z))
          = init.filter (fun z => decide (d.idxOf w < d.idxOf z ∧ d.idxOf z < d.idxOf x)) := by
        refine List.filter_congr fun z _ => ?_
        by_cases h1 : d.idxOf z < d.idxOf x
        · by_cases h2 : d.idxOf w < d.idxOf z
          · rw [decide_eq_true h1, decide_eq_true h2, Bool.true_and,
              decide_eq_true (by omega : d.idxOf w < d.idxOf z ∧ d.idxOf z < d.idxOf x)]
          · rw [decide_eq_true h1, decide_eq_false h2, Bool.true_and,
              decide_eq_false (by omega : ¬(d.idxOf w < d.idxOf z ∧ d.idxOf z < d.idxOf x))]
        · rw [decide_eq_false h1, Bool.false_and,
            decide_eq_false (by omega : ¬(d.idxOf w < d.idxOf z ∧ d.idxOf z < d.idxOf x))]
      have cR : init.filter (fun z => decide (d.idxOf z < d.idxOf x) && !decide (d.idxOf w < d.idxOf z))
          = init.filter (fun z => decide (d.idxOf z < d.idxOf w)) := by
        refine List.filter_congr fun z hz => ?_
        by_cases h1 : d.idxOf w < d.idxOf z
        · rw [decide_eq_true h1, Bool.not_true, Bool.and_false,
            decide_eq_false (by omega : ¬(d.idxOf z < d.idxOf w))]
        · have hzne : z ≠ w := by
            intro hcon
            apply hwNotInit
            rw [hcon] at hz
            exact hz
          have hne : d.idxOf z ≠ d.idxOf w :=
            fun hcon => hzne (idxOf_inj (hinitsub z hz) hw hcon)
          rw [decide_eq_false h1, Bool.not_false, Bool.and_true]
          by_cases h2 : d.idxOf z < d.idxOf x
          · rw [decide_eq_true h2, decide_eq_true (by omega : d.idxOf z < d.idxOf w)]
          · omega
      simp only [rBelow]
      rw [hsplit, cB, cR]
    constructor
    · intro hIO
      rw [hrw0]
      have hsubAB : ∀ a ∈ d.filter (fun z => decide (d.idxOf w < d.idxOf z ∧ d.idxOf z < d.idxOf x)),
          a ∈ init.filter (fun z => decide (d.idxOf w < d.idxOf z ∧ d.idxOf z < d.idxOf x)) := by
        intro a ha
        obtain ⟨hamem, hap⟩ := List.mem_filter.mp ha
        have hap' : d.idxOf w < d.idxOf a ∧ d.idxOf a < d.idxOf x := by simpa using hap
        rcases hIO hlt a hamem (by omega : d.idxOf w ≤ d.idxOf a)
            (by omega : d.idxOf a < d.idxOf x) with haw' | hain
        · exfalso
          rw [haw'] at hap
          simp at hap
        · exact List.mem_filter.mpr ⟨hain, hap⟩
      have hle := pigeonhole_le
        (d.filter (fun z => decide (d.idxOf w < d.idxOf z ∧ d.idxOf z < d.idxOf x)))
        (init.filter (fun z => decide (d.idxOf w < d.idxOf z ∧ d.idxOf z < d.idxOf x)))
        (allDistinct_filter _ _ hnd) hsubAB
      omega
    · intro harith
      rw [hrw0] at harith
      intro hprem z hzmem hz1 hz2
      by_cases hzw : z = w
      · exact Or.inl hzw
      · by_cases hzI : z ∈ init
        · exact Or.inr hzI
        · exfalso
          have hzne : d.idxOf z ≠ d.idxOf w := fun hcon => hzw (idxOf_inj hzmem hw hcon)
          have hzA : z ∈ d.filter
              (fun z_ => decide (d.idxOf w < d.idxOf z_ ∧ d.idxOf z_ < d.idxOf x)) :=
            List.mem_filter.mpr ⟨hzmem, decide_eq_true ⟨by omega, hz2⟩⟩
          have hsubB : ∀ b ∈ init.filter
                (fun z_ => decide (d.idxOf w < d.idxOf z_ ∧ d.idxOf z_ < d.idxOf x)),
              b ∈ (d.filter
                  (fun z_ => decide (d.idxOf w < d.idxOf z_ ∧ d.idxOf z_ < d.idxOf x))).filter
                (fun a => !decide (a = z)) := by
            intro b hb
            obtain ⟨hbmem, hbp⟩ := List.mem_filter.mp hb
            refine List.mem_filter.mpr ⟨List.mem_filter.mpr ⟨hinitsub b hbmem, hbp⟩, ?_⟩
            by_cases hbz : b = z
            · exfalso
              apply hzI
              rw [hbz] at hbmem
              exact hbmem
            · simp [hbz]
          have hle2 := pigeonhole_le
            (init.filter (fun z_ => decide (d.idxOf w < d.idxOf z_ ∧ d.idxOf z_ < d.idxOf x)))
            ((d.filter (fun z_ => decide (d.idxOf w < d.idxOf z_ ∧ d.idxOf z_ < d.idxOf x))).filter
              (fun a => !decide (a = z)))
            (allDistinct_filter _ _ hndinit) hsubB
          have hsingle := count_singleton (allDistinct_filter _ _ hnd) hzA
          have hsplit2 := filter_split_compl (fun a => decide (a = z))
            (d.filter (fun z => decide (d.idxOf w < d.idxOf z ∧ d.idxOf z < d.idxOf x)))
          -- no truncation in the arithmetic: w and z are two distinct
          -- non-init cards below x, so idxOf x ≥ rBelow d init x + 2
          have hwz : w ≠ z := fun hcon => hzw hcon.symm
          have had2 : allDistinct [w, z] := by
            intro i j hi hj heq
            simp only [List.length_cons, List.length_nil] at hi hj
            cases i with
            | zero =>
                cases j with
                | zero => rfl
                | succ j' =>
                    cases j' with
                    | zero =>
                        rw [List.getElem?_cons_zero, List.getElem?_cons_succ,
                          List.getElem?_cons_zero] at heq
                        exact absurd (Option.some.inj heq) hwz
                    | succ j'' => omega
            | succ i' =>
                cases i' with
                | zero =>
                    cases j with
                    | zero =>
                        rw [List.getElem?_cons_succ, List.getElem?_cons_zero,
                          List.getElem?_cons_zero] at heq
                        exact absurd (Option.some.inj heq.symm) hwz
                    | succ j'' => omega
                | succ i'' => omega
          have hwmem : w ∈ d.take (d.idxOf x) :=
            (mem_take_iff (d.idxOf x) w).mpr ⟨hw, hlt⟩
          have hzmem2 : z ∈ d.take (d.idxOf x) :=
            (mem_take_iff (d.idxOf x) z).mpr ⟨hzmem, hz2⟩
          have hsub2 : ∀ u ∈ [w, z],
              u ∈ (d.take (d.idxOf x)).filter (fun u => !decide (u ∈ init)) := by
            intro u hu
            rcases List.mem_cons.mp hu with huw | hu'
            · rw [huw]
              exact List.mem_filter.mpr ⟨hwmem, by simp [hwNotInit]⟩
            · have hu2 : u = z := List.mem_singleton.mp hu'
              rw [hu2]
              exact List.mem_filter.mpr ⟨hzmem2, by simp [hzI]⟩
          have hcard2 := pigeonhole_le [w, z]
            ((d.take (d.idxOf x)).filter (fun u => !decide (u ∈ init))) had2 hsub2
          have hsplit4 := filter_split_compl (fun u => decide (u ∈ init))
            (d.take (d.idxOf x))
          have htake2 : (d.take (d.idxOf x)).length = d.idxOf x := by
            rw [List.length_take]; omega
          have hrt : ((d.take (d.idxOf x)).filter (fun u => decide (u ∈ init))).length
              = rBelow d init x := filter_mem_take_count hnd hndinit hinitsub (d.idxOf x)
          have hlen2 : [w, z].length = 2 := rfl
          omega
  · -- O(x) < O(w): the left side is vacuous, the right side is the
    -- init-interval vs deck-interval count
    have hxa : d.idxOf x < d.idxOf w := by omega
    have hrw1 : rBelow d (init ++ [x]) w = rBelow d init w + 1 := by
      rw [hrw, if_pos hxa]
    have hsplit3 := filter_split_add (fun z => decide (d.idxOf z < d.idxOf w))
      (fun z => decide (d.idxOf z < d.idxOf x)) init
    have cI : init.filter (fun z => decide (d.idxOf z < d.idxOf w) && decide (d.idxOf z < d.idxOf x))
        = init.filter (fun z => decide (d.idxOf z < d.idxOf x)) := by
      refine List.filter_congr fun z _ => ?_
      by_cases h1 : d.idxOf z < d.idxOf x
      · rw [decide_eq_true h1, Bool.and_true, decide_eq_true (by omega : d.idxOf z < d.idxOf w)]
      · rw [decide_eq_false h1, Bool.and_false]
    have cJ : init.filter (fun z => decide (d.idxOf z < d.idxOf w) && !decide (d.idxOf z < d.idxOf x))
        = init.filter (fun z => decide (d.idxOf x ≤ d.idxOf z ∧ d.idxOf z < d.idxOf w)) := by
      refine List.filter_congr fun z _ => ?_
      by_cases h1 : d.idxOf z < d.idxOf x
      · rw [decide_eq_true h1, Bool.not_true, Bool.and_false,
          decide_eq_false (by omega : ¬(d.idxOf x ≤ d.idxOf z ∧ d.idxOf z < d.idxOf w))]
      · rw [decide_eq_false h1, Bool.not_false, Bool.and_true]
        by_cases h2 : d.idxOf z < d.idxOf w
        · rw [decide_eq_true h2,
            decide_eq_true (by omega : d.idxOf x ≤ d.idxOf z ∧ d.idxOf z < d.idxOf w)]
        · rw [decide_eq_false h2,
            decide_eq_false (by omega : ¬(d.idxOf x ≤ d.idxOf z ∧ d.idxOf z < d.idxOf w))]
    have hsplit3' : rBelow d init w
        = (init.filter (fun z => decide (d.idxOf z < d.idxOf x))).length
          + (init.filter (fun z => decide (d.idxOf x ≤ d.idxOf z ∧ d.idxOf z < d.idxOf w))).length := by
      simp only [rBelow]
      rw [hsplit3, cI, cJ]
    have hrx : (init.filter (fun z => decide (d.idxOf z < d.idxOf x))).length
        = rBelow d init x := rfl
    have hcount := count_interval d hnd (a := d.idxOf x) (b := d.idxOf w)
      hax (by omega) haw
    have hsubI : ∀ b ∈ init.filter (fun z => decide (d.idxOf x ≤ d.idxOf z ∧ d.idxOf z < d.idxOf w)),
        b ∈ d.filter (fun z => decide (d.idxOf x ≤ d.idxOf z ∧ d.idxOf z < d.idxOf w)) := by
      intro b hb
      obtain ⟨hbmem, hbp⟩ := List.mem_filter.mp hb
      exact List.mem_filter.mpr ⟨hinitsub b hbmem, hbp⟩
    have hle3 := pigeonhole_le
      (init.filter (fun z => decide (d.idxOf x ≤ d.idxOf z ∧ d.idxOf z < d.idxOf w)))
      (d.filter (fun z => decide (d.idxOf x ≤ d.idxOf z ∧ d.idxOf z < d.idxOf w)))
      (allDistinct_filter _ _ hndinit) hsubI
    constructor
    · intro _
      rw [hrw1]
      omega
    · intro _ hprem
      omega

/-! ### The walk kit

What the master equivalence stands on: the leading lane's mod
arithmetic, `NoDupP` transfer through the permutation, the cursor
invariant of the draw machine, the snoc-split of runs and prefixes, and
the order/counting facts connecting `maxRem` with the last position of
the remaining deck. -/

/-- The predecessor-lane residue: for `a ≥ 1`,
`(a % step + step - 1) % step = (a - 1) % step`. -/
theorem lane_pred_mod (step : Nat) (hstep : 0 < step) {a : Nat} (ha : 1 ≤ a) :
    (a % step + step - 1) % step = (a - 1) % step := by
  by_cases hs : step = 1
  · subst hs
    simp [Nat.mod_one]
  · obtain ⟨b, hb'⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
    subst hb'
    rw [show b + 1 - 1 = b from by omega]
    have hb := Nat.mod_lt b hstep
    have h1m : 1 % step = 1 := Nat.mod_eq_of_lt (by omega)
    have ham : (b + 1) % step = (b % step + 1) % step := by rw [Nat.add_mod, h1m]
    have key : ∀ c : Nat, c < step → (c + step) % step = c := by
      intro c hc
      rw [Nat.add_mod, Nat.mod_self, Nat.add_zero]
      simp [Nat.mod_eq_of_lt hc]
    rcases Nat.lt_or_ge (b % step + 1) step with hlt | hge
    · rw [ham, Nat.mod_eq_of_lt hlt]
      have hsum : b % step + 1 + step - 1 = b % step + step := by omega
      rw [hsum]
      exact key (b % step) hb
    · have he : b % step + 1 = step := by omega
      have hbb : b % step = step - 1 := by omega
      rw [ham, he, hbb, Nat.mod_self, Nat.zero_add]
      exact Nat.mod_eq_of_lt (by omega)

/-- `NoDupP` transfers through a permutation. -/
theorem perm_nodupP {l₁ l₂ : List Card} (h : l₁.Perm l₂) : NoDupP l₂ → NoDupP l₁ := by
  induction h with
  | nil => exact id
  | cons x p ih =>
      intro hnd
      obtain ⟨hx, ht⟩ := hnd
      refine ⟨fun hmem => hx ((List.Perm.mem_iff p).mp hmem), ih ht⟩
  | swap x y l =>
      intro hnd
      obtain ⟨hx, hy, hl⟩ := hnd
      refine ⟨?_, ⟨fun hmem => hx (by simp [hmem]), hl⟩⟩
      intro hmem
      rcases List.mem_cons.mp hmem with hyx | hyl
      · exact hx (by rw [hyx]; simp)
      · exact hy hyl
  | trans h₁ h₂ ih₁ ih₂ => exact fun h => ih₁ (ih₂ h)

/-- A distinct snoc-append hides its last card in the body nowhere. -/
theorem noDupCards_snoc {init : List Card} {x : Card} (h : noDupCards (init ++ [x])) :
    x ∉ init ∧ noDupCards init := by
  have hlen : (init ++ [x]).length = init.length + 1 := by
    rw [List.length_append]; rfl
  constructor
  · intro hmem
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hmem
    have hklt : k < init.length := (List.getElem?_eq_some_iff.mp hk).1
    have h1 : (init ++ [x])[k]? = init[k]? := List.getElem?_append_left (by omega)
    have h2 : (init ++ [x])[init.length]? = some x := by
      rw [List.getElem?_append_right (Nat.le_refl init.length), Nat.sub_self]
      rfl
    have hcon : k = init.length :=
      h k init.length (by rw [hlen]; omega) (by rw [hlen]; omega)
        (by rw [h1, hk, h2])
    omega
  · intro i j hi hj heq
    have h1 : (init ++ [x])[i]? = init[i]? := List.getElem?_append_left (by omega)
    have h2 : (init ++ [x])[j]? = init[j]? := List.getElem?_append_left (by omega)
    exact h i j (by rw [hlen]; omega) (by rw [hlen]; omega) (by rw [h1, h2]; exact heq)

/-- On members, the cycle's position search is the deck index. -/
theorem posOf_idxOf (c : Cycle Card) {w : Card} (hw : w ∈ c.cards) :
    c.posOf w = some (c.cards.idxOf w) := by
  obtain ⟨l, cur⟩ := c
  exact posOf_eq_idxOf l cur w hw

/-- The cursor invariant is maintained by every successful draw: the
drawn position is in range, and the splice steps the length down by
one. -/
theorem run_cursor_le : ∀ (l : List Card) (c c' : Cycle Card),
    run c l = some c' → c.cursor ≤ c.cards.length → c'.cursor ≤ c'.cards.length := by
  intro l
  induction l with
  | nil =>
      intro c c' hrun hcur
      have hc : c = c' := Option.some.inj hrun
      rw [← hc]
      exact hcur
  | cons y t ih =>
      intro c c' hrun hcur
      simp only [run] at hrun
      cases hdc : drawCard y c with
      | none => rw [hdc] at hrun; simp at hrun
      | some c₁ =>
          rw [hdc] at hrun
          have hrun' : run c₁ t = some c' := hrun
          simp only [drawCard] at hdc
          cases hp : c.posOf y with
          | none => rw [hp] at hdc; simp at hdc
          | some i =>
              rw [hp] at hdc
              have hc₁ : c₁ = ⟨Cycle.removeIdx c.cards i, i⟩ :=
                (Option.some.inj hdc).symm.trans (removeAt_drawTo_eq i c)
              have hilt : i < c.cards.length := posOf_lt hp
              have hlen : (Cycle.removeIdx c.cards i).length + 1 = c.cards.length :=
                Cycle.removeIdx_length c.cards i hilt
              have hcle : c₁.cursor ≤ c₁.cards.length := by
                rw [hc₁]
                show i ≤ (Cycle.removeIdx c.cards i).length
                omega
              exact ih c₁ c' hrun' hcle

/-- Extending a successful run by one more successful draw: the
snoc-append run succeeds. -/
theorem run_snoc : ∀ (pre : List Card) (c₀ cend c' : Cycle Card) (w : Card),
    run c₀ pre = some cend → drawCard w cend = some c' →
    run c₀ (pre ++ [w]) = some c' := by
  intro pre
  induction pre with
  | nil =>
      intro c₀ cend c' w hrun hdraw
      have hc : c₀ = cend := Option.some.inj hrun
      rw [← hc] at hdraw
      show run c₀ [w] = some c'
      simp only [run, hdraw]
  | cons y t ih =>
      intro c₀ cend c' w hrun hdraw
      simp only [run] at hrun
      cases hdc : drawCard y c₀ with
      | none => rw [hdc] at hrun; simp at hrun
      | some c₂ =>
          have hrun' : run c₂ t = some cend := by
            rw [hdc] at hrun
            exact hrun
          show run c₀ ((y :: t) ++ [w]) = some c'
          rw [show (y :: t) ++ [w] = y :: (t ++ [w]) from rfl]
          simp only [run, hdc]
          exact ih c₂ cend c' w hrun' hdraw

/-- A successful snoc-append run splits into the body's run and the
final draw. -/
theorem run_snoc_inv : ∀ (init : List Card) (c c' : Cycle Card) (x : Card),
    run c (init ++ [x]) = some c' →
    ∃ c₁, run c init = some c₁ ∧ drawCard x c₁ = some c' := by
  intro init
  induction init with
  | nil =>
      intro c c' x hrun
      simp only [List.nil_append, run] at hrun
      cases hdc : drawCard x c with
      | none => rw [hdc] at hrun; simp at hrun
      | some d =>
          rw [hdc] at hrun
          have hd : d = c' := Option.some.inj hrun
          exact ⟨c, rfl, by rw [← hd]; exact hdc⟩
  | cons y t ih =>
      intro c c' x hrun
      rw [show (y :: t) ++ [x] = y :: (t ++ [x]) from rfl] at hrun
      simp only [run] at hrun
      cases hdc : drawCard y c with
      | none => rw [hdc] at hrun; simp at hrun
      | some c₂ =>
          rw [hdc] at hrun
          obtain ⟨c₁, h1, h2⟩ := ih c₂ c' x hrun
          exact ⟨c₁, by simp only [run, hdc, h1], h2⟩

/-- A realizing walk passes through every prefix: the state after
`pre` still realizes the remaining suffix. -/
theorem realizes_prefix (step : Nat) (hstep : 0 < step) : ∀ (pre : List Card)
    (c : Cycle Card) (σ : List Card) (w : Card) (rest : List Card),
    realizes step hstep c σ → σ = pre ++ [w] ++ rest →
    ∃ c', run c pre = some c' ∧ realizes step hstep c' ([w] ++ rest) := by
  intro pre
  induction pre with
  | nil =>
      intro c σ w rest hreal hsplit
      subst hsplit
      exact ⟨c, rfl, hreal⟩
  | cons y t ih =>
      intro c σ w rest hreal hsplit
      subst hsplit
      obtain ⟨_, c₂, hdc, hreal'⟩ := hreal
      obtain ⟨c', hrun, hreal''⟩ := ih c₂ ((t ++ [w]) ++ rest) w rest hreal' rfl
      refine ⟨c', ?_, hreal''⟩
      simp only [run, hdc, hrun]

/-- After a successful run of `init ++ [x]`, the cursor sits exactly at
x's draw-time position (the `cursor_after` packaging). -/
theorem run_cursor_last (d : List Card) (hnd : noDupCards d) (init : List Card) (x : Card)
    (c₀ c' : Cycle Card) (hcards : c₀.cards = d) (hrun : run c₀ (init ++ [x]) = some c') :
    c'.cursor = d.idxOf x - rBelow d init x := by
  obtain ⟨c₁, h1, h2⟩ := run_snoc_inv init c₀ c' x hrun
  have hnd₀ : noDupCards c₀.cards := by rw [hcards]; exact hnd
  have hmemall : ∀ z ∈ init ++ [x], z ∈ c₀.cards := run_mem (init ++ [x]) c₀ c' hrun
  have hndsnoc : noDupCards (init ++ [x]) :=
    run_pre_nodup (init ++ [x]) c₀ c' hrun hnd₀ hmemall
  obtain ⟨hxinit, hndinit⟩ := noDupCards_snoc hndsnoc
  have hsub : ∀ z ∈ x :: init, z ∈ c₀.cards := by
    intro z hz
    rcases List.mem_cons.mp hz with hzx | hz'
    · exact hmemall z (by rw [hzx]; exact List.mem_append.mpr (Or.inr (by simp)))
    · exact hmemall z (List.mem_append.mpr (Or.inl hz'))
  have hndcons : noDupCards (x :: init) := allDistinct_cons hxinit hndinit
  have hres := cursor_after c₀ c₁ c' init x h1 h2 hsub hndcons hnd₀
  rw [hcards] at hres
  exact hres

/-- The last element of a snoc-append is the appended card. -/
theorem getLast?_snoc : ∀ (init : List Card) (x : Card),
    (init ++ [x]).getLast? = some x := by
  intro init
  induction init with
  | nil => intro x; rfl
  | cons y t ih =>
      intro x
      cases t with
      | nil => rfl
      | cons b t' => exact ih x

/-- Every nonempty list is a snoc-append. -/
theorem snoc_split : ∀ (l : List Card), l ≠ [] → ∃ init x, l = init ++ [x] := by
  intro l
  induction l with
  | nil => intro h; exact absurd rfl h
  | cons y t ih =>
      intro _
      cases t with
      | nil => exact ⟨[], y, rfl⟩
      | cons b t' =>
          obtain ⟨init, x, h⟩ := ih (by simp)
          exact ⟨y :: init, x, by rw [h, ← List.cons_append]⟩

/-- Order preservation through the removal filter: an original-above
card keeps its index strictly above `w`'s in the filtered deck. -/
theorem filter_idxOf_lt (d pre : List Card) (hnd : noDupCards d) {w u : Card}
    (hw : w ∈ d) (hu : u ∈ d) (hwn : w ∉ pre) (hun : u ∉ pre)
    (hlt : d.idxOf w < d.idxOf u) :
    (d.filter (fun z => decide (z ∉ pre))).idxOf w
      < (d.filter (fun z => decide (z ∉ pre))).idxOf u := by
  have hwf : w ∈ d.filter (fun z => decide (z ∉ pre)) :=
    List.mem_filter.mpr ⟨hw, by simp [hwn]⟩
  have huf : u ∈ d.filter (fun z => decide (z ∉ pre)) :=
    List.mem_filter.mpr ⟨hu, by simp [hun]⟩
  have h1 := idxOf_filter (p := fun z => decide (z ∉ pre)) d w hw (by simp [hwn])
  have h2 := idxOf_filter (p := fun z => decide (z ∉ pre)) d u hu (by simp [hun])
  have hndP : NoDupP d := noDupCards_NoDupP hnd
  have hdist : allDistinct (w :: (d.take (d.idxOf w)).filter (fun z => decide (z ∉ pre))) := by
    refine allDistinct_cons ?_
      (NoDupP_noDupCards (nodupP_filter _ (nodupP_take d (d.idxOf w) hndP)))
    intro hmem
    have := (mem_take_iff (d.idxOf w) w).mp (List.mem_filter.mp hmem).1
    omega
  have hsub : ∀ v ∈ w :: (d.take (d.idxOf w)).filter (fun z => decide (z ∉ pre)),
      v ∈ (d.take (d.idxOf u)).filter (fun z => decide (z ∉ pre)) := by
    intro v hv
    rcases List.mem_cons.mp hv with hvw | hut
    · rw [hvw]
      exact List.mem_filter.mpr ⟨(mem_take_iff _ _).mpr ⟨hw, hlt⟩, by simp [hwn]⟩
    · obtain ⟨hum, _⟩ := List.mem_filter.mp hut
      obtain ⟨hud, hui⟩ := (mem_take_iff _ _).mp hum
      exact List.mem_filter.mpr ⟨(mem_take_iff _ _).mpr ⟨hud, by omega⟩,
        (List.mem_filter.mp hut).2⟩
  have hle := pigeonhole_le (w :: (d.take (d.idxOf w)).filter (fun z => decide (z ∉ pre)))
    ((d.take (d.idxOf u)).filter (fun z => decide (z ∉ pre))) hdist hsub
  simp only [List.length_cons] at hle
  omega

/-- A last-position draw is a max-remaining draw: every original-above
card was already drawn. -/
theorem filter_last_maxRem (d pre : List Card) (hnd : noDupCards d) {w u : Card}
    (hw : w ∈ d) (hu : u ∈ d) (hwn : w ∉ pre)
    (hlast : (d.filter (fun z => decide (z ∉ pre))).idxOf w
      = (d.filter (fun z => decide (z ∉ pre))).length - 1)
    (hlt : d.idxOf w < d.idxOf u) : u ∈ pre := by
  rcases Classical.em (u ∈ pre) with hup | hun
  · exact hup
  · exfalso
    have hwf : w ∈ d.filter (fun z => decide (z ∉ pre)) :=
      List.mem_filter.mpr ⟨hw, by simp [hwn]⟩
    have huf : u ∈ d.filter (fun z => decide (z ∉ pre)) :=
      List.mem_filter.mpr ⟨hu, by simp [hun]⟩
    have hord := filter_idxOf_lt d pre hnd hw hu hwn hun hlt
    have hult := idxOf_lt_length huf
    omega

/-- A max-remaining draw sits at the last position of the remaining
deck. -/
theorem maxRem_last (d pre : List Card) (hnd : noDupCards d) {w : Card}
    (hw : w ∈ d) (hnotin : w ∉ pre) (hmax : maxRem d pre w) :
    (d.filter (fun z => decide (z ∉ pre))).idxOf w
      = (d.filter (fun z => decide (z ∉ pre))).length - 1 := by
  have hndP : NoDupP d := noDupCards_NoDupP hnd
  have hsplit : (d.filter (fun z => decide (z ∉ pre))).length
      = (d.filter (fun z => decide (z ∉ pre) && decide (d.idxOf z ≤ d.idxOf w))).length
      + (d.filter (fun z => decide (z ∉ pre)
          && !(decide (d.idxOf z ≤ d.idxOf w)))).length :=
    filter_split_add (fun z => decide (z ∉ pre)) (fun z => decide (d.idxOf z ≤ d.idxOf w)) d
  have hzero : (d.filter (fun z => decide (z ∉ pre)
      && !(decide (d.idxOf z ≤ d.idxOf w)))).length = 0 := by
    refine filter_len_zero _ d ?_
    intro u humem
    by_cases hq : d.idxOf u ≤ d.idxOf w
    · rw [decide_eq_true hq]
      simp
    · have hup : u ∈ pre := hmax u humem (by omega)
      rw [decide_eq_false (fun hcon => hcon hup)]
      simp
  have hwnt : w ∉ (d.take (d.idxOf w)).filter (fun z => decide (z ∉ pre)) := by
    intro hmem
    have := (mem_take_iff (d.idxOf w) w).mp (List.mem_filter.mp hmem).1
    omega
  have hcount : (d.filter (fun z => decide (z ∉ pre)
      && decide (d.idxOf z ≤ d.idxOf w))).length
      = ((d.take (d.idxOf w)).filter (fun z => decide (z ∉ pre))).length + 1 := by
    have h := length_eq_of_bijection (f := fun z => z) (g := fun z => z)
      (d.filter (fun z => decide (z ∉ pre) && decide (d.idxOf z ≤ d.idxOf w)))
      (w :: (d.take (d.idxOf w)).filter (fun z => decide (z ∉ pre)))
      (nodupP_filter _ hndP)
      ⟨hwnt, nodupP_filter _ (nodupP_take d (d.idxOf w) hndP)⟩
      (fun u hu => by
        obtain ⟨hud, hud2⟩ := List.mem_filter.mp hu
        rw [Bool.and_eq_true] at hud2
        obtain ⟨hup, huq⟩ := hud2
        have hup' : u ∉ pre := by simpa using hup
        have huq' : d.idxOf u ≤ d.idxOf w := by simpa using huq
        by_cases huw : u = w
        · exact ⟨List.mem_cons.mpr (Or.inl huw), rfl⟩
        · have hne : d.idxOf u ≠ d.idxOf w := fun hcon => huw (idxOf_inj hud hw hcon)
          exact ⟨List.mem_cons.mpr (Or.inr (List.mem_filter.mpr
            ⟨(mem_take_iff _ _).mpr ⟨hud, by omega⟩, by simp [hup']⟩)), rfl⟩)
      (fun u hu => by
        rcases List.mem_cons.mp hu with huw | hut
        · rw [huw]
          exact ⟨List.mem_filter.mpr ⟨hw, by
            rw [Bool.and_eq_true]
            exact ⟨by simp [hnotin], decide_eq_true (Nat.le_refl _)⟩⟩, rfl⟩
        · obtain ⟨hut1, hut2⟩ := List.mem_filter.mp hut
          obtain ⟨hud, hui⟩ := (mem_take_iff _ _).mp hut1
          exact ⟨List.mem_filter.mpr ⟨hud, by
            rw [Bool.and_eq_true]
            exact ⟨by simpa using hut2, decide_eq_true (by omega : d.idxOf u ≤ d.idxOf w)⟩⟩,
            rfl⟩)
    have h2 : (w :: (d.take (d.idxOf w)).filter (fun z => decide (z ∉ pre))).length
        = ((d.take (d.idxOf w)).filter (fun z => decide (z ∉ pre))).length + 1 := rfl
    omega
  have hD := idxOf_filter (p := fun z => decide (z ∉ pre)) d w hw (by simp [hnotin])
  omega

/-- **The per-step correspondence**: at a mid-sequence draw — `w` drawn
after `pre = init ++ [x]`, at the state `c` after `pre` — machine
accessibility (the mask at `c`) and the sequence-form condition
(`stepOK` at `pre`) say the same thing.  The position comes from
`pos_shift`, the cursor from `cursor_after`, the burial bound from
`burial_bound`, the max-remaining correspondence from the counting
lemmas above. -/
theorem mid_step_iff (d : List Card) (step : Nat) (hstep : 0 < step)
    (init : List Card) (x w : Card) (c : Cycle Card)
    (hnd : noDupCards d) (hsub : ∀ z ∈ init ++ [x], z ∈ d)
    (hndpre : noDupCards (init ++ [x]))
    (hw : w ∈ d) (hnotin : w ∉ init ++ [x])
    (hcards : c.cards = d.filter (fun z => decide (z ∉ init ++ [x])))
    (hcur : c.cursor ≤ c.cards.length)
    (hcursor : c.cursor = d.idxOf x - rBelow d init x)
    (hpos : c.posOf w = some (d.idxOf w - rBelow d (init ++ [x]) w)) :
    (∃ p, c.posOf w = some p ∧ p ∈ maskPos c step hstep)
      ↔ stepOK d step (init ++ [x]) w := by
  have hprex : x ∈ d := hsub x (List.mem_append.mpr (Or.inr (by simp)))
  have hw' : w ∈ c.cards := by
    rw [hcards]
    exact List.mem_filter.mpr ⟨hw, by simp [hnotin]⟩
  have h5 : c.posOf w = some (c.cards.idxOf w) := posOf_idxOf c hw'
  have hP : c.cards.idxOf w = d.idxOf w - rBelow d (init ++ [x]) w :=
    Option.some.inj (h5.symm.trans hpos)
  have hlane : laneAt d step (init ++ [x]) w
      = (d.idxOf w - rBelow d (init ++ [x]) w) % step := rfl
  have hlax : laneAt d step init x = (d.idxOf x - rBelow d init x) % step := rfl
  have hPpos : 0 < c.cards.length := by
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hw'
    have := (List.getElem?_eq_some_iff.mp hj).1
    omega
  have hPlt : c.cards.idxOf w < c.cards.length := idxOf_lt_length hw'
  have hfin : (d.idxOf w - rBelow d (init ++ [x]) w) % step = step - 1
      → (d.idxOf w - rBelow d (init ++ [x]) w) ∈ maskPos c step hstep := by
    intro hPmod
    rw [maskPos_mem_iff c step hstep hcur]
    rcases Nat.lt_or_ge (c.cards.idxOf w) (c.cards.length - 1) with hlt | hge
    · exact Or.inl ⟨hPmod, by rw [← hP]; exact hlt⟩
    · have heq : c.cards.idxOf w = c.cards.length - 1 := by omega
      exact Or.inr (Or.inl ⟨hPpos, by rw [← hP]; exact heq⟩)
  constructor
  · rintro ⟨p, hppos, hpmask⟩
    have hpP : p = d.idxOf w - rBelow d (init ++ [x]) w :=
      Option.some.inj (hppos.symm.trans hpos)
    rw [maskPos_mem_iff c step hstep hcur p] at hpmask
    rcases hpmask with ⟨hA1, hA2⟩ | ⟨-, hB2⟩ | ⟨hC0, hC1, hC2, hC3⟩
    · left
      rw [hlane, ← hpP]
      exact hA1
    · right; left
      intro u hu hlt
      have hlast : (d.filter (fun z => decide (z ∉ init ++ [x]))).idxOf w
          = (d.filter (fun z => decide (z ∉ init ++ [x]))).length - 1 := by
        have h1 : (d.filter (fun z => decide (z ∉ init ++ [x]))).idxOf w
            = c.cards.idxOf w := by rw [hcards]
        have h2 : (d.filter (fun z => decide (z ∉ init ++ [x]))).length
            = c.cards.length := by rw [hcards]
        rw [h1, h2, hP, ← hpP, hB2]
      exact filter_last_maxRem d (init ++ [x]) hnd hw hu hnotin hlast hlt
    · right; right
      refine ⟨x, getLast?_snoc init x, ?_, ?_⟩
      · rw [dropLast_append_single, hlane, hlax, ← hpP, hC3, ← hcursor,
          lane_pred_mod step hstep hC0]
      · rw [burial_bound d (init ++ [x]) x w hnd hsub hndpre hprex hw hnotin ⟨init, rfl⟩,
          dropLast_append_single, ← hcursor, ← hpP]
        exact hC1
  · intro hstepOK
    rcases hstepOK with h1 | h2 | ⟨x', hgl, hlaneq, hIO⟩
    · exact ⟨d.idxOf w - rBelow d (init ++ [x]) w, hpos,
        hfin (by rw [← hlane]; exact h1)⟩
    · have hlast := maxRem_last d (init ++ [x]) hnd hw hnotin h2
      refine ⟨d.idxOf w - rBelow d (init ++ [x]) w, hpos, ?_⟩
      rw [maskPos_mem_iff c step hstep hcur]
      refine Or.inr (Or.inl ⟨hPpos, ?_⟩)
      rw [← hP, hcards, hlast]
    · have hxx : x' = x := Option.some.inj (hgl.symm.trans (getLast?_snoc init x))
      rw [hxx] at hlaneq hIO
      rcases Nat.eq_zero_or_pos (d.idxOf x - rBelow d init x) with hx0 | hxpos
      · have hPmod : (d.idxOf w - rBelow d (init ++ [x]) w) % step = step - 1 := by
          rw [← hlane, hlaneq, dropLast_append_single, hlax, hx0, Nat.zero_mod,
            Nat.zero_add]
          exact Nat.mod_eq_of_lt (by omega)
        exact ⟨d.idxOf w - rBelow d (init ++ [x]) w, hpos, hfin hPmod⟩
      · have hcurpos : 0 < c.cursor := by rw [hcursor]; exact hxpos
        have hPmod : (d.idxOf w - rBelow d (init ++ [x]) w) % step
            = (c.cursor - 1) % step := by
          rw [← hlane, hlaneq, dropLast_append_single, hlax, ← hcursor,
            lane_pred_mod step hstep hcurpos]
        have hbur := (burial_bound d (init ++ [x]) x w hnd hsub hndpre hprex hw hnotin
          ⟨init, rfl⟩).mp hIO
        rw [dropLast_append_single] at hbur
        refine ⟨d.idxOf w - rBelow d (init ++ [x]) w, hpos, ?_⟩
        rw [maskPos_mem_iff c step hstep hcur]
        rcases Nat.lt_or_ge (c.cards.idxOf w) (c.cards.length - 1) with hlt | hge
        · exact Or.inr (Or.inr ⟨hcurpos, by rw [hcursor]; exact hbur,
            by rw [← hP]; exact hlt, hPmod⟩)
        · have heq : c.cards.idxOf w = c.cards.length - 1 := by omega
          exact Or.inr (Or.inl ⟨hPpos, by rw [← hP]; exact heq⟩)

/-- **The first draw's correspondence**: with an empty prefix, the step
conditions reduce to the batch-top lane and the last card — both
cursor-free, so accessibility holds at any state of the invariant
domain. -/
theorem nil_stepOK_realizes (c : Cycle Card) (step : Nat) (hstep : 0 < step)
    (hcur : c.cursor ≤ c.cards.length) (w : Card) (hw : w ∈ c.cards)
    (hnd : noDupCards c.cards)
    (hstepOK : stepOK c.cards step [] w) :
    ∃ p, c.posOf w = some p ∧ p ∈ maskPos c step hstep := by
  have hpidx : c.posOf w = some (c.cards.idxOf w) := posOf_idxOf c hw
  have hPpos : 0 < c.cards.length := by
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hw
    have := (List.getElem?_eq_some_iff.mp hj).1
    omega
  have hlt := idxOf_lt_length hw
  have hfeq : c.cards.filter (fun z => decide (z ∉ ([] : List Card))) = c.cards :=
    (List.filter_congr fun z _ => by simp).trans (filter_true_id c.cards)
  refine ⟨c.cards.idxOf w, hpidx, ?_⟩
  rw [maskPos_mem_iff c step hstep hcur]
  rcases hstepOK with h1 | h2 | ⟨x, hx, _, _⟩
  · have hr0 : rBelow c.cards ([] : List Card) w = 0 := rfl
    have h1' : c.cards.idxOf w % step = step - 1 := by
      have h1'' : (c.cards.idxOf w - rBelow c.cards ([] : List Card) w) % step
          = step - 1 := h1
      rw [hr0, Nat.sub_zero] at h1''
      exact h1''
    rcases Nat.lt_or_ge (c.cards.idxOf w) (c.cards.length - 1) with hlt2 | hge
    · exact Or.inl ⟨h1', hlt2⟩
    · have heq : c.cards.idxOf w = c.cards.length - 1 := by omega
      exact Or.inr (Or.inl ⟨hPpos, heq⟩)
  · have hlast := maxRem_last c.cards ([] : List Card) hnd hw (by simp) h2
    rw [hfeq] at hlast
    exact Or.inr (Or.inl ⟨hPpos, hlast⟩)
  · simp at hx

/-! ## The master equivalence -/

/-- Realizability implies the sequence form: every prefix's draw
satisfies its step condition.  The first draw consults the *initial*
cursor's mask — its leading lane must subsume into the batch-top
disjunct, which is exactly the `hpure` class of `maskPos_pure_indep`. -/
theorem stepsOK_of_realizes (c : Cycle Card) (step : Nat) (hstep : 0 < step)
    (hcur : c.cursor ≤ c.cards.length)
    (hpure : c.cursor % step = 0 ∨ c.cursor = c.cards.length)
    (σ : List Card) (hperm : σ.Perm c.cards) (hnd : noDupCards c.cards)
    (hreal : realizes step hstep c σ) : stepsOK c.cards step σ := by
  intro pre w rest hsplit
  obtain ⟨c', hrun, hreal'⟩ := realizes_prefix step hstep pre c σ w rest hreal hsplit
  obtain ⟨⟨p, hppos, hpmask⟩, _⟩ := hreal'
  have hsub : ∀ z ∈ pre, z ∈ c.cards := run_mem pre c c' hrun
  have hndpre : noDupCards pre := run_pre_nodup pre c c' hrun hnd hsub
  have hcur' : c'.cursor ≤ c'.cards.length := run_cursor_le pre c c' hrun hcur
  have hw : w ∈ c.cards :=
    (List.Perm.mem_iff hperm).mp
      (by rw [hsplit]; exact List.mem_append.mpr (Or.inl (by simp)))
  have hcards : c'.cards = c.cards.filter (fun z => decide (z ∉ pre)) :=
    run_cards_filter pre c c' hrun hnd hsub
  have hw' : w ∈ c'.cards := mem_of_posOf c'.cards c'.cursor w p hppos
  have hnotin : w ∉ pre := by
    have hfl : w ∈ c.cards.filter (fun z => decide (z ∉ pre)) := by
      rw [← hcards]; exact hw'
    have hdec := (List.mem_filter.mp hfl).2
    simpa using hdec
  cases pre with
  | nil =>
      have hcc : c' = c := (Option.some.inj hrun).symm
      rw [hcc] at hppos hpmask
      have h5 : c.posOf w = some (c.cards.idxOf w) := posOf_idxOf c hw
      have hpidx : c.cards.idxOf w = p := Option.some.inj (h5.symm.trans hppos)
      rw [maskPos_mem_iff c step hstep hcur p] at hpmask
      rcases hpmask with ⟨hA1, hA2⟩ | ⟨-, hB2⟩ | ⟨hC0, hC1, hC2, hC3⟩
      · left
        have hr0 : rBelow c.cards ([] : List Card) w = 0 := rfl
        show (c.cards.idxOf w - rBelow c.cards ([] : List Card) w) % step = step - 1
        rw [hr0, Nat.sub_zero, hpidx]
        exact hA1
      · right; left
        intro u hu hlt
        have hfeq : c.cards.filter (fun z => decide (z ∉ ([] : List Card))) = c.cards :=
          (List.filter_congr fun z _ => by simp).trans (filter_true_id c.cards)
        have hlast : (c.cards.filter (fun z => decide (z ∉ ([] : List Card)))).idxOf w
            = (c.cards.filter (fun z => decide (z ∉ ([] : List Card)))).length - 1 := by
          rw [hfeq, hpidx, hB2]
        exact filter_last_maxRem c.cards ([] : List Card) hnd hw hu (by simp) hlast hlt
      · rcases hpure with halign | hsat
        · left
          have hres : (c.cursor - 1) % step = step - 1 :=
            mod_sub_one_of_mod_zero step hstep c.cursor halign hC0
          have hr0 : rBelow c.cards ([] : List Card) w = 0 := rfl
          show (c.cards.idxOf w - rBelow c.cards ([] : List Card) w) % step = step - 1
          rw [hr0, Nat.sub_zero, hpidx, hC3, hres]
        · rw [hsat] at hC1
          omega
  | cons y ys =>
      obtain ⟨init, x, hpre⟩ := snoc_split (y :: ys) (by simp)
      rw [hpre] at hrun hsub hndpre hcards hnotin
      have hcursor : c'.cursor = c.cards.idxOf x - rBelow c.cards init x :=
        run_cursor_last c.cards hnd init x c c' rfl hrun
      have hpos : c'.posOf w = some (c.cards.idxOf w - rBelow c.cards (init ++ [x]) w) :=
        pos_shift c c' (init ++ [x]) w hrun hsub hnd hw hnotin
      rw [hpre]
      exact (mid_step_iff c.cards step hstep init x w c' hnd hsub hndpre hw hnotin hcards
        hcur' hcursor hpos).mp ⟨p, hppos, hpmask⟩

/-- The sequence form implies realizability: every step condition
gives accessibility at its moment (the conditions are cursor-free at
the first draw, and the leading-lane disjunct reconstructs the
predecessor's cursor afterwards). -/
theorem realizes_of_stepsOK (c : Cycle Card) (step : Nat) (hstep : 0 < step)
    (hcur : c.cursor ≤ c.cards.length)
    (σ : List Card) (hperm : σ.Perm c.cards) (hnd : noDupCards c.cards)
    (hsteps : stepsOK c.cards step σ) : realizes step hstep c σ := by
  have hmem : ∀ z ∈ σ, z ∈ c.cards := fun z hz => (List.Perm.mem_iff hperm).mp hz
  have hndPσ : NoDupP σ := perm_nodupP hperm (noDupCards_NoDupP hnd)
  have main : ∀ (L pre : List Card) (cy : Cycle Card),
      pre ++ L = σ → run c pre = some cy → realizes step hstep cy L := by
    intro L
    induction L with
    | nil => intro pre cy _ _; exact trivial
    | cons w tl ih =>
        intro pre cy hsplit hrun
        have hdecomp : σ = (pre ++ [w]) ++ tl := by
          rw [← hsplit, List.append_assoc pre [w] tl]; rfl
        have hstepOK : stepOK c.cards step pre w := hsteps pre w tl hdecomp
        have hw : w ∈ c.cards := hmem w (by
          rw [← hsplit]; exact List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))
        have hsub : ∀ z ∈ pre, z ∈ c.cards := run_mem pre c cy hrun
        have hndpre : noDupCards pre := run_pre_nodup pre c cy hrun hnd hsub
        have hcards : cy.cards = c.cards.filter (fun z => decide (z ∉ pre)) :=
          run_cards_filter pre c cy hrun hnd hsub
        have hcur' : cy.cursor ≤ cy.cards.length := run_cursor_le pre c cy hrun hcur
        have hnotin : w ∉ pre := by
          have hnd2 : NoDupP (pre ++ w :: tl) := by rw [hsplit]; exact hndPσ
          exact fun hcon =>
            nodupP_sub w pre tl hnd2 (List.mem_append.mpr (Or.inl hcon))
        have hacc : ∃ p, cy.posOf w = some p ∧ p ∈ maskPos cy step hstep := by
          cases pre with
          | nil =>
              have hfeq : c.cards.filter (fun z => decide (z ∉ ([] : List Card))) = c.cards :=
                (List.filter_congr fun z _ => by simp).trans (filter_true_id c.cards)
              rw [hfeq] at hcards
              have hwcy : w ∈ cy.cards := by rw [hcards]; exact hw
              have hndcy : noDupCards cy.cards := by rw [hcards]; exact hnd
              rw [← hcards] at hstepOK
              exact nil_stepOK_realizes cy step hstep hcur' w hwcy hndcy hstepOK
          | cons y ys =>
              obtain ⟨init, x, hpre⟩ := snoc_split (y :: ys) (by simp)
              rw [hpre] at hsplit hrun hsub hndpre hcards hnotin hstepOK
              have hcursor : cy.cursor = c.cards.idxOf x - rBelow c.cards init x :=
                run_cursor_last c.cards hnd init x c cy rfl hrun
              have hpos : cy.posOf w
                  = some (c.cards.idxOf w - rBelow c.cards (init ++ [x]) w) :=
                pos_shift c cy (init ++ [x]) w hrun hsub hnd hw hnotin
              exact (mid_step_iff c.cards step hstep init x w cy hnd hsub hndpre hw hnotin
                hcards hcur' hcursor hpos).mpr hstepOK
        obtain ⟨p, hppos, hpmask⟩ := hacc
        show (∃ p, cy.posOf w = some p ∧ p ∈ maskPos cy step hstep)
            ∧ ∃ c'', drawCard w cy = some c'' ∧ realizes step hstep c'' tl
        refine ⟨⟨p, hppos, hpmask⟩, (cy.drawTo p).removeAt p,
          by simp only [drawCard, hppos], ?_⟩
        cases pre with
        | nil =>
            exact ih ([] ++ [w]) ((cy.drawTo p).removeAt p)
              (by rw [← hsplit]; rfl)
              (run_snoc [] c cy ((cy.drawTo p).removeAt p) w hrun
                (by simp only [drawCard, hppos]))
        | cons y ys =>
            obtain ⟨init, x, hpre⟩ := snoc_split (y :: ys) (by simp)
            rw [hpre] at hsplit hrun
            exact ih ((init ++ [x]) ++ [w]) ((cy.drawTo p).removeAt p)
              (by rw [← hsplit, List.append_assoc _ [w] tl]; rfl)
              (run_snoc (init ++ [x]) c cy ((cy.drawTo p).removeAt p) w hrun
                (by simp only [drawCard, hppos]))
  exact main σ [] c rfl rfl

/-- **The sequence form** (deck_bf.py's `check_seq`): a full draw
order of the deck is realizable iff every draw satisfies its step
condition.  This is what rung 3 of the SAT ladder consumes; its UNSAT
soundness reduces to this theorem plus the encoding's definitional
biconditionals.

`hpure` is the initial cursor's purity (the repair of 2026-09-13: the
class of `maskPos_pure_indep`): `realizes`'s *first* draw reads the
initial cycle's mask — leading lane included — while `stepOK` at
`pre = []` has no predecessor, so an impure initial cursor makes
draw orders realizable that the sequence form rejects (witness:
`witnesses/PaceStepsOKWitness.lean`, deck [♥A,♥2], step 2, cursor 1).
Intermediate draws need no purity: the cursor there is the
predecessor's draw-time position (`cursor_after`), which `stepOK`'s
third disjunct reconstructs exactly.  Probed: with `hpure` the iff is
clean on all permutations of n ≤ 7 decks × steps 1–4 × every pure
cursor in range, plus 40320 perms at n = 8 (step 3, cursors 0 and 8). -/
theorem realizes_iff_stepsOK (c : Cycle Card) (step : Nat) (hstep : 0 < step)
    (hcur : c.cursor ≤ c.cards.length)
    (hpure : c.cursor % step = 0 ∨ c.cursor = c.cards.length)
    (σ : List Card) (hperm : σ.Perm c.cards) (hnd : noDupCards c.cards) :
    realizes step hstep c σ ↔ stepsOK c.cards step σ :=
  ⟨stepsOK_of_realizes c step hstep hcur hpure σ hperm hnd,
    realizes_of_stepsOK c step hstep hcur σ hperm hnd⟩

end Pace
