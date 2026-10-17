import Orig2.Vocab

/-!
# Orig2.RevSteps — THE REVERSIBLE-STEPS CARD (the general
two-way-closure lemma, installed same hour as its dry-run)

PROMOTION PROVENANCE (2026-10-17): dry-ran as
`Temp/revsteps_check.lean` per the chart-rows direct-discipline
(the general ledger's proof is small; no probe chartered at the
owner's call), compiled green at `[propext]` — zero sorry, zero
`Classical.choice` — and installed byte-identical at owner
approval ("sure help do me that then").

THE LEMMA: over ANY letter family P, the dumb both-ways span
closure equals the reversible closure — the witness-grade,
family-generic abstraction of the cargo-bridge card (the abort
archive `Temp/cargo_bridge_aborted.lean`'s chain template,
generalized off its single family; the cargo instance — the pulled
`dumbSpan_iff_exchange` — is this lemma's P = cargo-letter case,
and its `[propext]`-green chain template is the stepping stone).

WHAT IT LICENSES (the house keystone row): every closure def that
enforces per-leg reversibility at DEFINITION time (NoDrawPlayW,
BareCargoEquiv, the twin sheets) lost NOTHING by the enforcement —
the raw two-way closure was never bigger.  Design-completeness at
every alphabet, WF-free, oracle-free, choice-free.

PRIVATE KIT (the house dedup discipline, per-row cites): the
span-map mono, span transitivity, the span-to-play realization
(a reconstruction of the pulled `steps_to_walk` bridge — the
archive cites it, the pull removed it; rebuilt privately here),
the composite-position kernel, and the chain induction with the
prefix accumulator.
-/

/- `RevStep` is the registry constant at `Orig2/Vocab.lean`
(landed at the same hour as this card); the card consumes it
through the `Orig2.Vocab` import — no local restate. -/

/-- Spans map across letters (the archive's private kit,
    verbatim generalization). -/
private theorem steps_map {Q Q' : State → State → Prop}
    (hQ : ∀ w z, Q w z → Q' w z) {w u : State} :
    Steps Q w u → Steps Q' w u := by
  intro hs
  induction hs with
  | refl s => exact Steps.refl s
  | cons hleg t ih => exact Steps.cons (hQ _ _ hleg) ih

/-- Span transitivity (the archive's private kit, verbatim). -/
private theorem steps_trans {Q : State → State → Prop} :
    ∀ {a b c : State}, Steps Q a b → Steps Q b c → Steps Q a c := by
  intro a b c h1
  induction h1 with
  | refl s => intro h2; exact h2
  | cons hleg t ih => intro h2; exact Steps.cons hleg (ih h2)

/-- The span-to-play realization (reconstruction of the pulled
    banked bridge; the archive cites it, the pull removed it —
    rebuilt privately per the dedup discipline, cite:
    `Temp/cargo_bridge_aborted.lean`'s usage; frozen template
    `Orig/ForklessCeiling.lean`'s returning-cycle machinery). -/
private theorem steps_to_walk (P : State → Move → Prop) {st : State} :
    ∀ {W : State}, Steps (StepOf P) st W →
      ∃ ρ : List Move, Walk P st ρ W := by
  intro W hs
  induction hs with
  | refl s => exact ⟨[], Walk.nil s⟩
  | @cons w z u hleg _ ih =>
      obtain ⟨m, hp, hstep⟩ := hleg
      obtain ⟨ρ, hρ⟩ := ih
      exact ⟨m :: ρ, Walk.cons hp hstep hρ⟩

/-- THE COMPOSITE-POSITION KERNEL — a fired P-letter whose
    successor spans back to its own origin is reversible: the
    return span realizes to a play, and the play IS the carrier's
    witness.  (The archive's `cargoLeg_of_dumbLeg`, generalized
    off the cargo letter.) -/
private theorem revStep_of_stepo (P : State → Move → Prop) {w z : State}
    (hleg : StepOf P w z) (hret : Steps (StepOf P) z w) :
    RevStep P w z := by
  obtain ⟨m, hp, hstep⟩ := hleg
  obtain ⟨ρ, hρ⟩ := steps_to_walk P hret
  exact ⟨m, hp, hstep, z, ρ, hstep, Walk_run P hρ⟩

/-- THE CHAIN INDUCTION (the archive's `aux`, generalized): every
    leg of a dumb span whose far endpoint carries a partner span
    back to the chain root is reversible — the per-leg return is
    the composite suffix ++ partner span ++ accumulated prefix. -/
private theorem revSpan_aux (P : State → Move → Prop) (A : State) :
    ∀ {B X : State}, Steps (StepOf P) X B →
      Steps (StepOf P) B A →
      Steps (StepOf P) A X →
      Steps (RevStep P) X B := by
  intro B X s1
  induction s1 with
  | refl s => intro _ _; exact Steps.refl s
  | cons hleg t ih =>
      intro hBA π
      exact Steps.cons
        (revStep_of_stepo P hleg (steps_trans (steps_trans t hBA) π))
        (ih hBA (steps_trans π (Steps.cons hleg (Steps.refl _))))

/-- **THE GENERAL LEMMA** — the dumb both-ways span closure equals
    the reversible closure, for every letter family P: enforcing
    per-leg reversibility at def time never shrinks a two-way
    closure. -/
theorem rev_steps_iff (P : State → Move → Prop) (A B : State) :
    (Steps (StepOf P) A B ∧ Steps (StepOf P) B A) ↔
    (Steps (RevStep P) A B ∧ Steps (RevStep P) B A) := by
  constructor
  · rintro ⟨hAB, hBA⟩
    exact ⟨revSpan_aux P A hAB hBA (Steps.refl A),
           revSpan_aux P B hBA hAB (Steps.refl B)⟩
  · rintro ⟨rAB, rBA⟩
    have h1 : ∀ w z, RevStep P w z → StepOf P w z := by
      intro w z hleg
      obtain ⟨m, hp, hstep, -⟩ := hleg
      exact ⟨m, hp, hstep⟩
    exact ⟨steps_map h1 rAB, steps_map h1 rBA⟩

/-! ## The audit battery -/

#print axioms rev_steps_iff
