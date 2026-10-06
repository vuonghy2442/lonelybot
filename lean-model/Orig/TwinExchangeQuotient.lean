import Orig.TwinExchange

/-!
# Orig — the quotient for the local twin exchange

The local twin exchange (`State.exchangeTwin`, `Orig.TwinExchange`) is
verdict-invariant at the *licensed* shape — both twin hosts located
face-up in distinct piles with at least one host bare
(`twin_exchange_bare_iff`) — and this file is the quotient that
license demands: the setoid of licensed-exchange chains, the class
type, and the verdict descended onto it.

* **§1 The license** — `TwinExchOK` bundles exactly
  `twin_exchange_bare_iff`'s premises (WF, both hosts located face-up
  in distinct piles, at least one host bare; the both-bare case rides
  for free — the exchange is then the identity).  The license
  descends through the exchange (`TwinExchOK_exchangeTwin`): WF by
  `State.wf_exchangeTwin`, the hosts keep their piles by
  `State.exchangeTwin_hosts_stable`, and the bare clause swaps sides
  by the `aboveIn` slot laws — so the exchange is an honest symmetry
  of the license.
* **§2 The chain** — `ExchStep` (one licensed exchange) and
  `ExchChain` (the reflexive-transitive closure, `ShufflePlayW`'s
  cons-carried shape: every step is explicit, so chain inductions
  re-root along the tail).  `ExchChain_append` concatenates;
  `ExchStep_symm`/`ExchChain_symm` invert each step through the
  involution `State.exchangeTwin_invol`.  The both-occupied shape is
  deliberately not a step here: that row is TwinExchange's declared
  open content, and the chain never crosses it.
* **§3 The descent** — `ExchStep_sameFate` is
  `twin_exchange_bare_iff` with the license unpacked;
  `ExchChain_sameFate` walks it along the chain.
* **§4 The quotient** — `exchSetoid` / `ExchOrbit` and the lifted
  verdict `WinFromQ₃` (the third of the family: `WinFromQ` on the
  twin relabeling, `WinFromQ₂` on the same-orbit classes, this one on
  the licensed-exchange classes).  The workhorses:
  `ExchOrbit.mk_exchangeTwin` (one licensed exchange does not move
  the class), `ExchOrbit.mk_eq_mk` / `ExchOrbit.exact` (equal classes
  carry a chain — the homemade `Quot.exact`),
  `winFromQ₃_mk_iff`, `twin_exch_quotient` (the `twin_quotient`
  analogue: related positions have the same verdict) and
  `twin_exchange_fate_of_classEq` (class equality alone transfers
  the verdict).

Axiom targets of the chapter: `[propext, Quot.sound]` —
`Classical.choice` is never needed (the per-step iff is the
constructive one-move realization of TwinExchange).

Not carried in this chapter (future):

* the engine successor-set descent (`Klondike/PileQuotient.lean` §2's
  shape, for the restricted move set — a bridge question, not an
  Orig question);
* the `RevEqW` refinement — each licensed bare exchange is a one-move
  witness shuffle in both directions, which would land every chain
  inside `sameOrbitSetoid`'s classes; blocked on TwinExchange's
  private realizations (`step_realize_fwd` / `step_realize_bwd`) going
  public;
* the both-occupied row, which would widen the license.
-/

/-! ## §1. The licensed exchange step -/

/-- The license for one local twin exchange: exactly
`twin_exchange_bare_iff`'s premise bundle.  Well-formed position,
both twin hosts located face-up, in distinct piles, and at least one
host bare (both-bare included — `State.exchangeTwin_eq_self_of_both_bare`
makes the exchange the identity there, and the step degenerates to a
reflexive one). -/
def TwinExchOK (st : State) (t : Card) : Prop :=
  st.WF ∧ ∃ a a', st.pileHolding t = some a ∧ st.pileHolding t.twin = some a'
    ∧ a ≠ a' ∧ (aboveIn t (st.piles a).faceUp = []
             ∨ aboveIn t.twin (st.piles a').faceUp = [])

/-- The licensed step relation: `b` is one licensed local twin
exchange of `a`. -/
def ExchStep (a b : State) : Prop :=
  ∃ t, TwinExchOK a t ∧ b = a.exchangeTwin t

/-- The license descends through the exchange: the exchanged state
carries the same license at the same twin, so the step relation is
symmetric in substance before any closure is taken. -/
theorem TwinExchOK_exchangeTwin {st : State} {t : Card} (h : TwinExchOK st t) :
    TwinExchOK (st.exchangeTwin t) t := by
  obtain ⟨hwf, a, a', h₁, h₂, hne, hbare⟩ := h
  have ht : st.cardCount t = 1 := hwf.2.2.1 t (Card.mem_universe t)
  have htw : st.cardCount t.twin = 1 := hwf.2.2.1 t.twin (Card.mem_universe t.twin)
  obtain ⟨hs₁, hs₂⟩ := State.exchangeTwin_hosts_stable h₁ h₂ hne ht htw
  refine ⟨State.wf_exchangeTwin hwf h₁ h₂ hne, a, a', hs₁, hs₂, hne, ?_⟩
  rcases hbare with hb | hb
  · exact Or.inr ((State.exchangeTwin_aboveIn_other h₁ h₂ hne).trans hb)
  · exact Or.inl ((State.exchangeTwin_aboveIn_self h₁ h₂ hne).trans hb)

/-! ## §2. The chain of licensed exchanges -/

/-- The closure spine: positions joined by a finite chain of licensed
local exchanges.  Every `cons` carries its step explicitly, so chain
inductions re-root along the tail (`ShufflePlayW`'s shape). -/
inductive ExchChain : State → State → Prop where
  | nil (st : State) : ExchChain st st
  | cons {st st' st'' : State} (hstep : ExchStep st st')
      (hrest : ExchChain st' st'') : ExchChain st st''

/-- One step is a chain. -/
theorem ExchChain_step {a b : State} (h : ExchStep a b) : ExchChain a b :=
  ExchChain.cons h (ExchChain.nil b)

/-- Chains concatenate (re-rooted induction, `ShufflePlayW_append`'s
shape). -/
theorem ExchChain_append {a b : State} (h₁ : ExchChain a b) :
    ∀ {c : State}, ExchChain b c → ExchChain a c := by
  induction h₁ with
  | nil _s =>
      intro _c h₂
      exact h₂
  | cons hstep _hrest ih =>
      intro c h₂
      exact ExchChain.cons hstep (ih h₂)

/-- The step is symmetric: the exchange is an involution at the
licensed shape (`State.exchangeTwin_invol`), and the license descends
to the exchanged state. -/
theorem ExchStep_symm {a b : State} (h : ExchStep a b) : ExchStep b a := by
  obtain ⟨t, hok, rfl⟩ := h
  have hok' : TwinExchOK (a.exchangeTwin t) t := TwinExchOK_exchangeTwin hok
  have hinveq : a = (a.exchangeTwin t).exchangeTwin t := by
    obtain ⟨hwf, _k, _k', h₁, h₂, hne, -⟩ := hok
    exact (State.exchangeTwin_invol h₁ h₂ hne
      (hwf.2.2.1 t (Card.mem_universe t))
      (hwf.2.2.1 t.twin (Card.mem_universe t.twin))).symm
  exact ⟨t, hok', hinveq⟩

/-- The chain is symmetric: each step inverts through the involution. -/
theorem ExchChain_symm {a b : State} (h : ExchChain a b) : ExchChain b a := by
  induction h with
  | nil s => exact ExchChain.nil s
  | cons hstep _hrest ih =>
      exact ExchChain_append ih (ExchChain_step (ExchStep_symm hstep))

/-! ## §3. The verdict descent -/

/-- One licensed exchange preserves the verdict —
`twin_exchange_bare_iff` with the license unpacked. -/
theorem ExchStep_sameFate {a b : State} (h : ExchStep a b) : sameFate a b := by
  obtain ⟨t, hok, rfl⟩ := h
  obtain ⟨hwf, k, k', h₁, h₂, hne, hbare⟩ := hok
  exact twin_exchange_bare_iff hwf h₁ h₂ hne hbare

/-- Every licensed-exchange chain preserves the verdict. -/
theorem ExchChain_sameFate {a b : State} (h : ExchChain a b) : sameFate a b := by
  induction h with
  | nil _s => exact Iff.rfl
  | cons hstep _hrest ih => exact sameFate_trans (ExchStep_sameFate hstep) ih

/-! ## §4. The quotient -/

/-- The local-twin-exchange setoid: the licensed chains.  Registered
as an instance to match the corpus discipline (`twinSetoid` and
`sameOrbitSetoid` are instances too) — but always passed explicitly
through `ExchOrbit`, never through `≈`, since this file has the twin
relabeling's setoid in scope as well. -/
instance exchSetoid : Setoid State where
  r a b := ExchChain a b
  iseqv :=
    ⟨fun a => ExchChain.nil a,
      fun {_ _} h => ExchChain_symm h,
      fun {_ _ _} h₁ h₂ => ExchChain_append h₁ h₂⟩

/-- Positions modulo licensed local twin exchanges. -/
abbrev ExchOrbit := Quotient exchSetoid

/-- The class of a position. -/
def ExchOrbit.mk (st : State) : ExchOrbit := Quotient.mk exchSetoid st

/-- Classes are equal along the chain (the `Quot.sound` reading). -/
theorem ExchOrbit.mk_eq_mk {a b : State} (h : ExchChain a b) :
    ExchOrbit.mk a = ExchOrbit.mk b :=
  Quotient.sound h

/-- The `sound` converse: equal classes carry a chain witness — the
homemade `Quot.exact` (`PileClass.exact`'s device: the
orbit-through-`a` lifts to the quotient, and the lifted equality
transfers `refl` into the relation). -/
theorem ExchOrbit.exact {a b : State} (h : ExchOrbit.mk a = ExchOrbit.mk b) :
    ExchChain a b := by
  have hf : ∀ (x y : State), ExchChain x y →
      (ExchChain a x) = (ExchChain a y) := by
    intro x y hxy
    apply propext
    constructor
    · intro hax
      exact ExchChain_append hax hxy
    · intro hay
      exact ExchChain_append hay (ExchChain_symm hxy)
  have h1 : Quotient.lift (fun x => ExchChain a x) hf (ExchOrbit.mk a)
      = Quotient.lift (fun x => ExchChain a x) hf (ExchOrbit.mk b) := by rw [h]
  have h1 : ExchChain a a = ExchChain a b := h1
  have h2 : ExchChain a a := ExchChain.nil a
  rw [h1] at h2
  exact h2

/-- One licensed exchange does not move the class. -/
theorem ExchOrbit.mk_exchangeTwin {st : State} {t : Card} (hok : TwinExchOK st t) :
    ExchOrbit.mk (st.exchangeTwin t) = ExchOrbit.mk st :=
  Quotient.sound (ExchChain_step (ExchStep_symm ⟨t, hok, rfl⟩))

/-- The verdict on the licensed-exchange classes: the play verdict
descends to the quotient.  (The third of the family — `WinFromQ` on
the twin relabeling, `WinFromQ₂` on the same-orbit classes, this one
here.) -/
def WinFromQ₃ (q : ExchOrbit) : Prop :=
  Quotient.lift WinFrom (fun _ _ h => propext (ExchChain_sameFate h)) q

/-- The lifted verdict at a class is the raw verdict at any member
(lift-on-`mk` is definitionally transparent, the `WinFromQ₂`
`show` device). -/
theorem winFromQ₃_mk_iff {st : State} : WinFromQ₃ (ExchOrbit.mk st) ↔ WinFrom st :=
  Iff.rfl

/-- The `twin_quotient` analogue: related positions have the same
verdict — the quotient carries a well-defined solvability. -/
theorem twin_exch_quotient {a b : State} (h : exchSetoid.r a b) :
    WinFrom a ↔ WinFrom b :=
  ExchChain_sameFate h

/-- Class equality alone transfers the verdict: `ExchOrbit.exact`
recovers the chain, and `ExchChain_sameFate` walks it. -/
theorem twin_exchange_fate_of_classEq {a b : State}
    (h : ExchOrbit.mk a = ExchOrbit.mk b) : WinFrom a ↔ WinFrom b :=
  ExchChain_sameFate (ExchOrbit.exact h)
