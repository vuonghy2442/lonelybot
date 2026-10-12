import Orig.PairName
import Orig.OrbitFactorC

open EdgeKit

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

## The route

The vanilla grade is pure board congruence: `nextUp_congr` carries
`found` reads and `pileOfTop_congr`/`=_piles` carry the board reads
across a draw (`draw_step_canRaise`), and the play lift chains the
per-leg biconditional leg by leg.

The `via` mantle needs the leg frames.  FORWARD (with the draw), a
`tabToTab` leg at the drawing origin and the fired draw at that
origin cross the three-squares commutation (the square rows of
`Orig.EdgeLabel`'s public `EdgeKit`, consumed here since the
dedup merge): the leg re-fires at the drawn landing, the draw
re-fires at the leg's own landing, and the leg's return play —
waste-free by the cycle-count census (`cycleCount_step` never
rises, the two waste movers drop strictly, the round trip pins the
count) — pushes across the draw (`run_drawPush`) landing exactly
the drawn-source's pair, which re-witnesses the leg at the drawn
landing outright.

BACKWARD (against the draw), the public §1 square
(`board_draw_commute`) re-fires the drawn landing's witnessed leg
at the drawing origin, and the origin-side witness play is a plain
composition: one fired draw (the square's own crossing), then the
leg's own return play, then the outer draw leg's own return play
(the `DrawPlayW` carries it) — no `WF`, no oracle, no phase
arithmetic.  The banked frame row `reversibleAtW_stepDraw_frame` is
deliberately NOT cited: it is `WF`-gated and transports the drawn
landing's witness origin-ward only, while this card's frozen
statements carry no `WF`; the composition above replaces it.  The
inductive mantle threads this composition, and the
`ForkWitness`/`forkState` corollaries are pure iff algebra over the
witness plays of `SWRotW` (the per-play lifts are biconditionals, so
each one-directional conclusion follows from a single round; the
card cites both for convenience).
-/

/-! ## §0 The transport kit — consumed, not carried

The edge-label chapter's transport kit (the three board squares,
the push core, the draw-frame rows, the cycle-count census) is
public as `Orig.EdgeLabel`'s `EdgeKit` since the dedup merge the
farm markers stamped; this card consumes it via `open EdgeKit` and
carries no per-file copies. -/

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
    refine ⟨by rw [nextUp_congr c hf]; exact hn, a, ?_, ?_⟩
    · rw [pileOfTop_congr c hp]; exact htop
    · rw [hp]; exact hseat
  · intro ⟨hn, a, htop, hseat⟩
    refine ⟨by rw [nextUp_congr c hf.symm]; exact hn, a, ?_, ?_⟩
    · rw [pileOfTop_congr c hp.symm]; exact htop
    · rw [← hp]; exact hseat

/-- The play lift of the vanilla license: the draws-only property
rides the induction's goal, so the tail's hypothesis is the IH's own
premise (the `shuffleW_board_keep` idiom). -/
private theorem play_canRaise_aux : ∀ {u v : State} {play : List Move},
    ShufflePlayW u play v → (∀ m ∈ play, m = Move.draw) →
    ∀ c : Card, CanRaise u c ↔ CanRaise v c := by
  intro u v play h
  induction h with
  | nil s => intro _ c; rfl
  | @cons st₀ m mid rest st' hw hstep hrest ih =>
      intro hdr c
      have hmd : m = Move.draw := hdr m (by simp)
      subst hmd
      have hih := ih (fun m' hm' => hdr m' (List.mem_cons_of_mem _ hm')) c
      constructor
      · intro hcr
        exact hih.1 ((draw_step_canRaise hstep c).mp hcr)
      · intro hcr
        exact (draw_step_canRaise hstep c).mpr (hih.2 hcr)

/-- FORWARD per-draw lift of the inductive mantle: the `via` legs
cross the square (leg and draw at the same origin), the leg's own
return play is waste-free by the cycle-count census (a reversible
leg round-trips at a conserved count), and it pushes across the
draw (`run_drawPush`) landing exactly the pair: the leg re-witnesses
at the drawn landing outright. -/
private theorem draw_canRaiseS_fwd {x : State} {c : Card} (h : CanRaiseS x c) :
    ∀ {z : State}, x.stepDraw = some z → CanRaiseS z c := by
  induction h with
  | @now x₀ c' hcr =>
      intro z hd
      exact CanRaiseS.now c' ((draw_step_canRaise
        (show State.step x₀ Move.draw = some z from hd) c').mp hcr)
  | @via x₀ w c' hl h ih =>
      intro z hd
      obtain ⟨d, b, hfired, hrev⟩ := hl
      -- leg × draw at one origin: both re-fire, landings aligned
      obtain ⟨t₂, hzfire, hwt₂⟩ := square_tabToTab hfired hd
      -- the leg's own return play
      obtain ⟨w', P₀, hw'step, hrunP⟩ := hrev
      have hw_eq : w' = w := Option.some.inj (hw'step.symm.trans hfired)
      rw [hw_eq] at hrunP
      -- waste-free: the round trip conserves the cycle count
      have hcount : cycleCount x₀ = cycleCount w :=
        Nat.le_antisymm (run_cycleCount_le hrunP) (cycleCount_step hfired)
      have hfree := run_ne_waste_of_return hrunP hcount
      -- pushed across the draw, landing the outer pair itself
      obtain ⟨u', hpushrun, hpushfire⟩ := run_drawPush P₀ w t₂ x₀ hwt₂ hrunP hfree
      have hu'z : u' = z := Option.some.inj (hpushfire.symm.trans hd)
      rw [hu'z] at hpushrun
      have hrevz : reversibleAtW z (Move.tabToTab d b) := ⟨t₂, P₀, hzfire, hpushrun⟩
      exact CanRaiseS.via c' ⟨d, b, hzfire, hrevz⟩ (ih hwt₂)

/-- BACKWARD per-draw lift of the inductive mantle: the drawn
landing's witnessed leg re-fires at the drawing origin through the
PUBLIC §1 square (`board_draw_commute` — the witness is the landing's
own), and the origin-side round trip is the plain composition of the
crossed draw, the leg's own return play, and the outer draw leg's own
return play (a `DrawPlayW` leg carries it).  The same composition
serves the crossed site's own draw — the IH's premise at the leg's
landed frame.  No `WF`, no oracle. -/
private theorem draw_canRaiseS_bwd {z : State} {c : Card} (h : CanRaiseS z c) :
    ∀ {x : State}, x.stepDraw = some z → reversibleAtW x Move.draw →
      CanRaiseS x c := by
  induction h with
  | @now z₀ c' hcr =>
      intro x hd hrevd
      exact CanRaiseS.now c' ((draw_step_canRaise
        (show State.step x Move.draw = some z₀ from hd) c').mpr hcr)
  | @via z₀ t₂ c' hl h ih =>
      intro x hd hrevd
      obtain ⟨d, b, hfirez, hrevz⟩ := hl
      -- the public square: the landing's witnessed leg re-fires at the origin
      obtain ⟨w, hfirex, hwt₂⟩ := board_draw_commute hd hfirez hrevz
      -- the outer draw's own return play
      obtain ⟨z', R, hz'step, hrunR⟩ := hrevd
      have hz'_eq : z' = z₀ :=
        Option.some.inj (hz'step.symm.trans
          (show State.step x Move.draw = some z₀ from hd))
      rw [hz'_eq] at hrunR
      -- the leg's own return play at the drawn landing
      obtain ⟨t', P, ht'step, hrunP⟩ := hrevz
      have ht'_eq : t' = t₂ := Option.some.inj (ht'step.symm.trans hfirez)
      rw [ht'_eq] at hrunP
      -- the origin-side round trip: draw across, leg's return, draw's return
      have hQ1 : State.step w Move.draw = some t₂ := hwt₂
      have hR2 : t₂.run (P ++ R) = some x := run_split P t₂ z₀ R x hrunP hrunR
      have hrevx : reversibleAtW x (Move.tabToTab d b) :=
        ⟨w, Move.draw :: (P ++ R), hfirex, (run_step_cons' hQ1).trans hR2⟩
      -- the crossed site's own draw, witnessed the same way
      have hQ2 : x.run [Move.tabToTab d b] = some w := run_one hfirex
      have hR3 : t₂.run (P ++ R ++ [Move.tabToTab d b]) = some w :=
        run_split (P ++ R) t₂ x [Move.tabToTab d b] w hR2 hQ2
      have hrevw : reversibleAtW w Move.draw :=
        ⟨t₂, P ++ R ++ [Move.tabToTab d b], hwt₂, hR3⟩
      exact CanRaiseS.via c' ⟨d, b, hfirex, hrevx⟩ (ih hwt₂ hrevw)

/-- The play lift of the mantle: the draws-only property rides the
goal (the `shuffleW_board_keep` idiom), one drawn leg at a time. -/
private theorem play_canRaiseS_aux : ∀ {u v : State} {play : List Move},
    ShufflePlayW u play v → (∀ m ∈ play, m = Move.draw) →
    ∀ c : Card, CanRaiseS u c ↔ CanRaiseS v c := by
  intro u v play h
  induction h with
  | nil s => intro _ c; rfl
  | @cons st₀ m mid rest st' hw hstep hrest ih =>
      intro hdr c
      have hmd : m = Move.draw := hdr m (by simp)
      subst hmd
      have hstepD : st₀.stepDraw = some mid := hstep
      have hrevd : reversibleAtW st₀ Move.draw := hw
      have hih := ih (fun m' hm' => hdr m' (List.mem_cons_of_mem _ hm')) c
      constructor
      · intro hc
        exact hih.1 (draw_canRaiseS_fwd hc hstepD)
      · intro hc
        exact draw_canRaiseS_bwd (hih.2 hc) hstepD hrevd

/-- Per-play: a draws-only witness play preserves every `CanRaise` iff. -/
theorem drawPlayW_inert_canRaise {u v : State}
    {play : List Move} (hplay : DrawPlayW u play v) (c : Card) :
    CanRaise u c ↔ CanRaise v c := by
  obtain ⟨hshuffle, hall⟩ := hplay
  exact play_canRaise_aux hshuffle hall c

/-- Per-play: a draws-only play preserves the `CanRaiseS` inductive. -/
theorem drawPlayW_inert_canRaiseS {u v : State}
    {play : List Move} (hplay : DrawPlayW u play v) (c : Card) :
    CanRaiseS u c ↔ CanRaiseS v c := by
  obtain ⟨hshuffle, hall⟩ := hplay
  exact play_canRaiseS_aux hshuffle hall c

/-- THE COMPONENT-LEVEL COROLLARY — `SWRotW` preserves the
`ForkWitness` relation. -/
theorem swRotW_inert_forkWitness {u v : State}
    (hrot : SWRotW u v) {x : Card}
    (hw : ForkWitness u x) :
    ForkWitness v x := by
  obtain ⟨σ, τ, hσ, hτ⟩ := hrot
  refine ⟨fun c =>
    ⟨fun hL => (drawPlayW_inert_canRaiseS hσ c).mp ((hw.1 c).mp hL),
      fun hR => (hw.1 c).mpr ((drawPlayW_inert_canRaiseS hτ c).mp hR)⟩,
    fun hc => hw.2 ((drawPlayW_inert_canRaise hτ x.twin).mp hc)⟩

theorem swRotW_inert_forkState {u v : State}
    (hrot : SWRotW u v)
    (hf : forkState u) :
    forkState v := by
  obtain ⟨x, hw⟩ := forkState_iff.1 hf
  exact forkState_iff.2 ⟨x, swRotW_inert_forkWitness hrot hw⟩

#print axioms draw_step_canRaise
#print axioms drawPlayW_inert_canRaise
#print axioms drawPlayW_inert_canRaiseS
#print axioms swRotW_inert_forkWitness
#print axioms swRotW_inert_forkState
