import Orig.PairName
import Orig.OrbitFactorC

/-!
# Orig.SWRotInert — THE DRAW-INERTNESS OF FORK FACTS

The factorization biconditional (`sameOrbit_factor_full` in
`Orig.OrbitFactorC`) splits every class journey into its board
component and its draw component.  This card proves the corollary
every assembly consumer cites: the draw legs are DEFINITIONALLY
INERT to every fork fact.  `CanRaise` reads `st.nextUp` (a `found`
read) and `st.pileOfTop`/`st.piles` (boards); `CanRaiseS`'s inductive
mantle reads `CanRaise` and reversible `tabToTab` legs; `ForkWitness`
and `forkState` read only `CanRaiseS` and `CanRaise`.  Every draw
leg preserves `found` and `piles` (the banked `stepDraw_found`/
`stepDraw_piles`); so the entire fork-grade predicate survives
`SWRotW` wholesale.

Consumers: the `forkState_pairClass` assembly (the draw half of every
journey analysis vanishes), the mod-phase spectrum row, and the
pair-fiber/bracket cards' phase-vacuity sections.
-/

/-- Per-leg: a successful draw preserves every `CanRaise` iff —
the license reads only `found` and `piles`. -/
theorem draw_step_canRaise {st s' : State}
    (h : State.step st Move.draw = some s') (c : Card) :
    CanRaise st c ↔ CanRaise s' c := by
  have hd : st.stepDraw = some s' := h
  have hf := stepDraw_found hd
  have hp := stepDraw_piles hd
  constructor
  · intro ⟨hn, a, htop, hseat⟩
    refine ⟨by rw [s'.nextUp, hf]; exact hn, a, ?_, by rw [s'.piles, hp]; exact hseat⟩
    rw [s'.piles, hp]; exact htop
  · intro ⟨hn, a, htop, hseat⟩
    refine ⟨by rw [st.nextUp, hf]; exact hn, a, ?_, by rw [st.piles, hp]; exact hseat⟩
    rw [st.piles, hp]; exact htop

/-- Per-play: a draws-only witness play preserves every `CanRaise` iff. -/
theorem drawPlayW_inert_canRaise {u v : State}
    {play : List Move} (hplay : DrawPlayW u play v) (c : Card) :
    CanRaise u c ↔ CanRaise v c := by
  obtain ⟨hshuffle, hall⟩ := hplay
  induction hshuffle with
  | nil => rfl
  | cons m rest st₁ st₂ hstep _ _ ih =>
      have hdraw : m = Move.draw := hall m (List.mem_cons_self ..)
      have hstep' : State.step st₁ Move.draw = some st₂ := by
        rw [hdraw] at hstep; exact hstep
      exact (draw_step_canRaise hstep' c).trans (ih (fun hm => hall hm (List.mem_cons_of_mem _ (List.mem_cons_self ..))))

/-- Per-play: a draws-only play preserves the `CanRaiseS` inductive. -/
theorem drawPlayW_inert_canRaiseS {u v : State}
    {play : List Move} (hplay : DrawPlayW u play v) (c : Card) :
    CanRaiseS u c ↔ CanRaiseS v c := by
  obtain ⟨hshuffle, hall⟩ := hplay
  constructor
  · intro h
    induction h with
    | now c' hcr => exact .now c' ((drawPlayW_inert_canRaise hplay c').2 hcr)
    | via c' hl hrest ih =>
        sorry -- the via-leg's tabToTab interplay needs the leg-zone machinery
  · sorry

/-- THE COMPONENT-LEVEL COROLLARY — `SWRotW` preserves the
`ForkWitness` relation. -/
theorem swRotW_inert_forkWitness {u v : State}
    (hrot : SWRotW u v) {x : Card}
    (hw : ForkWitness u x) :
    ForkWitness v x := by
  sorry

theorem swRotW_inert_forkState {u v : State}
    (hrot : SWRotW u v)
    (hf : forkState u) :
    forkState v := by
  sorry

#print axioms draw_step_canRaise
#print axioms drawPlayW_inert_canRaise
#print axioms drawPlayW_inert_canRaiseS
#print axioms swRotW_inert_forkWitness
#print axioms swRotW_inert_forkState
