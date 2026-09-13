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

/-- **The characterization** (deck_bf.py's `pred_positions`, validated
against the machine on every reachable state at N ≤ 15 for step 3):
a position is accessible iff it is on the batch-top lane, or is the
last card, or is on the leading lane from the cursor (the waste top
and its forward-dealing lane, bounded below by the burial).

`hcur` is the machine's cursor invariant `cursor ≤ length` (WF's stock
conjunct, deck.rs's `draw_cur ≤ len`) — without it the wrapped lane's
bound degenerates past `len + 1` and out-of-range positions leak in
(cf. `maskPos_step1`'s note).

TODO(proof) [M]: unfold maskPos; List.mem_append/mem_singleton;
laneUp_mem twice; case on cursor = 0 and cursor % step = 0; the
residue bookkeeping is Nat.mod_eq_of_lt + omega. -/
theorem maskPos_mem_iff {α : Type} (c : Cycle α) (step : Nat) (hstep : 0 < step)
    (hcur : c.cursor ≤ c.cards.length)
    (p : Nat) :
    p ∈ maskPos c step hstep ↔
      (p % step = step - 1 ∧ p < c.cards.length - 1)
      ∨ (0 < c.cards.length ∧ p = c.cards.length - 1)
      ∨ (0 < c.cursor ∧ c.cursor - 1 ≤ p ∧ p < c.cards.length - 1
          ∧ p % step = (c.cursor - 1) % step) := sorry

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

TODO(proof) [E]: `maskPos_mem_iff` both sides; a pure cursor's leading
lane has residue `(o - 1) % step = step - 1` (and at `o = 0` or the
pass end it is vacuous), so it subsumes into the batch-top disjunct —
both sides reduce to `p % step = step - 1 ∧ p < n - 1` plus the last
card. -/
theorem maskPos_pure_indep {α : Type} (c c' : Cycle α) (step : Nat) (hstep : 0 < step)
    (hc : c.cards = c'.cards)
    (hcur : c.cursor ≤ c.cards.length) (hcur' : c'.cursor ≤ c'.cards.length)
    (hpure : c.cursor % step = 0 ∨ c.cursor = c.cards.length)
    (hpure' : c'.cursor % step = 0 ∨ c'.cursor = c'.cards.length) :
    ∀ p, p ∈ maskPos c step hstep ↔ p ∈ maskPos c' step hstep := sorry

/-- Residue monotonicity: within an impure residue class, the earlier
cursor accesses more — `K(o) ⊇ K(o')` when `o ≤ o'` and
`o % step = o' % step ≠ 0`.  The mechanism: `iter_callback`'s leading
lane starts at `o - 1` (lower for smaller `o`) while the batch-top lane
and the last card are class-invariant.

TODO(proof) [E]: `maskPos_mem_iff` both sides; the first two disjuncts
are cursor-free; the leading lane's bound `o' - 1 ≤ p` weakens to
`o - 1 ≤ p` by `hle`, the residues agree by `hres`, and `0 < o'`
gives `0 < o`. -/
theorem maskPos_residue_mono {α : Type} (c c' : Cycle α) (step : Nat) (hstep : 0 < step)
    (hc : c.cards = c'.cards)
    (hle : c.cursor ≤ c'.cursor)
    (hres : c.cursor % step = c'.cursor % step)
    (himp : c'.cursor % step ≠ 0)
    (hcur : c.cursor ≤ c.cards.length) (hcur' : c'.cursor ≤ c'.cards.length) :
    ∀ p, p ∈ maskPos c' step hstep → p ∈ maskPos c step hstep := sorry

/-- Impure over pure: any mid-pass cursor's accessible set contains the
pass-boundary (pure) one — the impure set is the pure set (batch-top
lane + last card) *plus* a nonempty leading lane.

TODO(proof) [E]: `maskPos_mem_iff` both sides; the pure side reduces to
the two cursor-free disjuncts (`maskPos_pure_indep`'s route), which the
impure side's first two disjuncts already cover. -/
theorem maskPos_impure_sup_pure {α : Type} (c c' : Cycle α) (step : Nat) (hstep : 0 < step)
    (hc : c.cards = c'.cards)
    (himp : c.cursor % step ≠ 0)
    (hpure' : c'.cursor % step = 0 ∨ c'.cursor = c'.cards.length)
    (hcur : c.cursor ≤ c.cards.length) (hcur' : c'.cursor ≤ c'.cards.length) :
    ∀ p, p ∈ maskPos c' step hstep → p ∈ maskPos c step hstep := sorry

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

/-- The merge lemma: `drawCard` reads only the cards — the jump target
is `posOf` (cards-only), `drawTo` *overwrites* the cursor with `i + 1`,
and `removeAt` computes the successor cursor from that overwritten value
(`if i < i + 1 then i + 1 - 1` = `i`) — so two cycles with the same
cards draw any card to the *identical* successor.  This is what makes
winning lines merge after one common draw, the load-bearing step of
Macro.lean's `pace_dominance` replay.

TODO(proof) [E]: congruence — `posOf` agrees by `hc`, and the successor
cycle `⟨removeIdx c.cards i, i⟩` has no occurrence of the source
cursor. -/
theorem drawCard_cursor_indep (c c' : Cycle Card) (x : Card) (hc : c.cards = c'.cards) :
    drawCard x c = drawCard x c' := sorry

/-- The deterministic machine run over a draw order. -/
def run (c : Cycle Card) : List Card → Option (Cycle Card)
  | [] => some c
  | x :: xs => match drawCard x c with
    | some c' => run c' xs
    | none => none

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

/-- The counting identity: after a run of `pre`, a not-yet-drawn
card's position is its original index minus the drawn-below count
(removeIdx preserves order and shifts later positions down one;
`rBelow` counts exactly the removed-below).

`hnd` is necessary: with duplicates the run can draw the same value
twice (the second find succeeds at the shifted position) while
`rBelow` counts by `idxOf`, over-counting the shift.  From `hnd` +
`hrun`, `noDupCards pre` derives (a repeated draw dies at `posOf`
none — the `eStep_deckStack_unique` pattern in FARM_MEMORY).

TODO(proof) [M]: induction on pre through run; the step case is
removeIdx's order preservation + a below-count split. -/
theorem pos_shift (c c' : Cycle Card) (pre : List Card) (w : Card)
    (hrun : run c pre = some c') (hsub : ∀ z ∈ pre, z ∈ c.cards)
    (hnd : noDupCards c.cards)
    (hw : w ∈ c.cards) (hnotin : w ∉ pre) :
    c'.posOf w = some (c.cards.idxOf w - rBelow c.cards pre w) := sorry

/-- After drawing `pre ++ [w]`, the cursor sits exactly at w's
draw-time position: the jump lands `i + 1` and the splice steps back
to `i`; a last-position draw saturates at `length - 1` = the new
length, which is the draw-time position — both conventions, one
exact statement.

TODO(proof) [M]: drawTo i lands cursor = i + 1, removeAt i decrements
when i < cursor; the last-position case saturates — pos_shift
supplies i. -/
theorem cursor_after (c c' c'' : Cycle Card) (pre : List Card) (w : Card)
    (hrun : run c pre = some c') (hdraw : drawCard w c' = some c'')
    (hsub : ∀ z ∈ w :: pre, z ∈ c.cards) (hndpre : noDupCards (w :: pre))
    (hnd : noDupCards c.cards) :
    c''.cursor = c.cards.idxOf w - rBelow c.cards pre w := sorry

/-- The interval identity: the burial condition is exactly the
leading-lane position bound P(w) ≥ P(x) - 1, where P(v) is v's
position at its draw (`idxOf v` minus its `rBelow`).  Both directions:
the between-count saturates iff every interval card besides `w` was
drawn before `x`.

TODO(proof) [M]: idxOf injective on d (hnd), so O(w) < O(x) vs
O(x) < O(w); the first case is the saturation count (the interval
holds exactly O(x) - O(w) - 1 cards of d besides w), the second is
vacuous both sides. -/
theorem burial_bound (d : List Card) (pre : List Card) (x w : Card)
    (hnd : noDupCards d) (hsub : ∀ z ∈ pre, z ∈ d)
    (hndpre : noDupCards pre) (hx : x ∈ d) (hw : w ∈ d)
    (hnotin : w ∉ pre) (hend : ∃ init, pre = init ++ [x]) :
    intervalOK d pre.dropLast x w ↔
      d.idxOf x - rBelow d pre.dropLast x - 1 ≤ d.idxOf w - rBelow d pre w := sorry

/-- **The sequence form** (deck_bf.py's `check_seq`): a full draw
order of the deck is realizable iff every draw satisfies its step
condition.  This is what rung 3 of the SAT ladder consumes; its UNSAT
soundness reduces to this theorem plus the encoding's definitional
biconditionals.

TODO(proof) [H]: prefix-walk induction on σ; each draw via
maskPos_mem_iff with pos_shift (the position) and cursor_after (the
predecessor's cursor) + burial_bound for the leading lane (the
cursor_after wrap case is a max-draw; its successor never uses the
leading lane).  Converse by induction on σ: each stepOK disjunct
gives accessibility through maskPos_mem_iff's converse +
burial_bound's converse.  `hcur` is the initial state's cursor
invariant (maintained by every `drawCard`, so the walk never leaves
the characterization's domain).  Falsifier: python/deck_bf.py (all
modes green for step 3). -/
theorem realizes_iff_stepsOK (c : Cycle Card) (step : Nat) (hstep : 0 < step)
    (hcur : c.cursor ≤ c.cards.length)
    (σ : List Card) (hperm : σ.Perm c.cards) (hnd : noDupCards c.cards) :
    realizes step hstep c σ ↔ stepsOK c.cards step σ := sorry

end Pace
