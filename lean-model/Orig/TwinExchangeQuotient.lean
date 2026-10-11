import Orig.TwinExchange
import Orig.Combine

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
* the both-occupied row, which would widen the license.

§5 and §6 (the exch-canlaw card's landing 2, 2026-10-11) close the
first bullet this file carried in its future list: the `RevEqW`
refinement — each licensed bare exchange is a one-move witness
shuffle in both directions — is now LANDED (`exch_leg_RevEqW` over
the public `step_realize_fwd`/`step_realize_bwd`), every chain sits
inside `sameOrbitSetoid`'s classes (`exch_chain_RevEqW`,
`exch_le_sameOrbit`), and the coarsening's forgetful map
`exchOrbit_to_sameOrbit` is defined.  §7 lands the disjoint-family
superposition (`exch_local_pair`, `exch_superpose`) and the torsor
freeness `exch_free`, with the identity pricing the landing-1 probe
battery demanded (`exchangeTwin_ne_self_pile`: a genuine bit writes
its own seat differently; the licensed both-bare bit prices at
zero).  The exchanges-only literal canon-image claim is
RECORD-CLOSED as refuted-by-exhibit in FUTURES-ORIG.md §10 (the
worried-king fork cell; the macro-state-graded spine and pinches
ride landing 3).
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

/-! ## The pair group's class-level corollaries

The state-level commutation (`Orig.TwinExchange`'s `exchangeTwin_comm`)
has its license companion there (`exchangeTwin_other_located`); here
the license descends across pairs, and the elementary-abelian-2
structure becomes three class-level facts: the descent, the two-step
fixed point, and **either order, the same class element** — the
symmetry-collapse resource for chain normal forms. -/

/-- **The license descends across pairs**: after one licensed
exchange at `t₁`, the other pair's license survives at the new state
(the located shape re-anchors, the bare clause transports; the
degenerate pair through the hosts-stable substrate, the stacked
family cannot arise). -/
theorem TwinExchOK_exchangeTwin_other {st : State} {t₁ t₂ : Card}
    (hok₁ : TwinExchOK st t₁) (hok₂ : TwinExchOK st t₂) :
    TwinExchOK (st.exchangeTwin t₁) t₂ := by
  obtain ⟨hwf, a₁, a₁', h₁, h₁', hne₁, hbare₁⟩ := hok₁
  obtain ⟨-, a₂, a₂', h₂, h₂', hne₂, hbare₂⟩ := hok₂
  obtain ⟨b, b', hloc1, hloc2, hne, hbare⟩ :=
    exchangeTwin_other_located hwf h₁ h₁' hne₁ hbare₁ h₂ h₂' hne₂ hbare₂
  exact ⟨State.wf_exchangeTwin hwf h₁ h₁' hne₁, b, b', hloc1, hloc2, hne, hbare⟩

/-- Two licensed exchanges, in either order, compose inside the
starting class: the chain never leaves home. -/
theorem ExchOrbit.mk_exchangeTwin_two {st : State} {t₁ t₂ : Card}
    (hok₁ : TwinExchOK st t₁) (hok₂ : TwinExchOK st t₂) :
    ExchOrbit.mk ((st.exchangeTwin t₁).exchangeTwin t₂) = ExchOrbit.mk st := by
  rw [ExchOrbit.mk_exchangeTwin (TwinExchOK_exchangeTwin_other hok₁ hok₂),
    ExchOrbit.mk_exchangeTwin hok₁]

/-- **The pair group is abelian at the class level**: two licensed
exchanges, either order, the same `ExchOrbit` class element. -/
theorem ExchOrbit.mk_exchangeTwin_comm {st : State} {t₁ t₂ : Card}
    (hok₁ : TwinExchOK st t₁) (hok₂ : TwinExchOK st t₂) :
    ExchOrbit.mk ((st.exchangeTwin t₁).exchangeTwin t₂) =
      ExchOrbit.mk ((st.exchangeTwin t₂).exchangeTwin t₁) := by
  rw [ExchOrbit.mk_exchangeTwin_two hok₁ hok₂,
    ExchOrbit.mk_exchangeTwin_two hok₂ hok₁]

/-! ## §5. The coarsening: every exchange is a `sameOrbit` edge

`Orig.TwinExchange`'s realizations are public (promoted at this
card): at the one-bare shape the exchange is a plain `Move.tabToTab`
in both directions — the cargo rides onto the bare host, and the
mirror move rides it back.  So one licensed exchange is a ONE-MOVE
witness shuffle in both directions, the chain sits inside
`sameOrbitSetoid`'s classes, and the physical quotient COARSENS the
macro state: the forgetful map carries every `ExchOrbit` class into
the sameOrbit class of its members.  The map is surjective and NOT
injective — the not-injectivity is the worried-king fork cell's
meaning, record-closed at FUTURES-ORIG.md §10. -/

/-- The cargo-side orientation of the one-move witness shuffle: the
residing cargo realizes the exchange forward, the mirror rides it
back (the private core the license cases route through; the twin
orientation comes by the pair law). -/
private theorem exch_leg_RevEqW_core {a : State} {t : Card} {k k' : Anchor}
    {z : Card} {rest : List Card}
    (hwf : a.WF)
    (h₁ : a.pileHolding t = some k) (h₂ : a.pileHolding t.twin = some k')
    (hne : k ≠ k')
    (hS : aboveIn t (a.piles k).faceUp = z :: rest)
    (hS' : aboveIn t.twin (a.piles k').faceUp = []) :
    RevEqW a (a.exchangeTwin t) := by
  have hfwd : a.step (Move.tabToTab z (Sum.inr t.twin)) =
      some (a.exchangeTwin t) :=
    step_realize_fwd hwf h₁ h₂ hne hS hS'
  have hbwd : (a.exchangeTwin t).step (Move.tabToTab z (Sum.inr t)) =
      some a :=
    step_realize_bwd hwf h₁ h₂ hne hS hS'
  exact ⟨[Move.tabToTab z (Sum.inr t.twin)],
    ShufflePlayW.cons ⟨a.exchangeTwin t, [Move.tabToTab z (Sum.inr t)],
      hfwd, run_one hbwd⟩ hfwd (ShufflePlayW.nil _),
    [Move.tabToTab z (Sum.inr t)],
    ShufflePlayW.cons ⟨a, [Move.tabToTab z (Sum.inr t.twin)],
      hbwd, run_one hfwd⟩ hbwd (ShufflePlayW.nil _)⟩

/-- Every licensed bare exchange is a one-move witness shuffle in
both directions — `RevEqW` between the exchanged mates.  The
cargo-side orientation rides the core; the bare-side cargo flips
through the pair law; the both-bare license is the identity,
reflexive. -/
theorem exch_leg_RevEqW {a b : State} (h : ExchStep a b) : RevEqW a b := by
  obtain ⟨t, hok, rfl⟩ := h
  obtain ⟨hwf, k, k', h₁, h₂, hne, hbare⟩ := hok
  cases hL : aboveIn t ((a.piles k).faceUp) with
  | nil =>
      cases hR : aboveIn t.twin ((a.piles k').faceUp) with
      | nil =>
          rw [State.exchangeTwin_eq_self_of_both_bare h₁ h₂ hne hL hR]
          exact RevEqW_refl _
      | cons z rest =>
          rw [← State.exchangeTwin_pair a t]
          exact exch_leg_RevEqW_core (a := a) (t := t.twin) (k := k') (k' := k)
            (z := z) (rest := rest) hwf h₂
            (by rw [Card.twin_twin]; exact h₁)
            (fun hc => hne hc.symm) hR
            (by rw [Card.twin_twin]; exact hL)
  | cons z rest =>
      cases hR : aboveIn t.twin ((a.piles k').faceUp) with
      | nil =>
          exact exch_leg_RevEqW_core hwf h₁ h₂ hne hL hR
      | cons w ws =>
          rcases hbare with hb | hb
          · rw [hL] at hb; exact absurd hb (by simp)
          · rw [hR] at hb; exact absurd hb (by simp)

/-- Every licensed-exchange chain is a witness-shuffle journey in
both directions (`ShufflePlayW`'s cons-carried shape keeps every leg
explicit, so the induction re-roots along the tail). -/
theorem exch_chain_RevEqW {a b : State} (h : ExchChain a b) : RevEqW a b := by
  induction h with
  | nil s => exact RevEqW_refl s
  | @cons s s' s'' hstep hrest ih =>
      obtain ⟨σ, hσ, τ, hτ⟩ := ih
      obtain ⟨σ₀, hσ₀, τ₀, hτ₀⟩ := exch_leg_RevEqW hstep
      exact ⟨σ₀ ++ σ, ShufflePlayW_append hσ₀ hσ, τ ++ τ₀,
        ShufflePlayW_append hτ hτ₀⟩

/-- The coarsening row: every licensed-exchange chain stays inside
the macro state — `exchSetoid.r` implies `sameOrbitSetoid.r`
(sameOrbit's engine reads `RevEqW b a`, the witness shuffle flipped;
the banked `RevEqW_symm` does the flip). -/
theorem exch_le_sameOrbit {a b : State} (h : ExchChain a b) :
    sameOrbitSetoid.r a b :=
  RevEqW_symm (exch_chain_RevEqW h)

/-- The forgetful map: the exchanges-only quotient of physical
classes carried into the macro-state quotient.  Well-defined because
every exchange chain is a sameOrbit journey (`exch_le_sameOrbit`);
SURJECTIVE (every macro class contains the image of a physical
class), NOT injective — the worried-king fork cell (the probe
battery's B2, FUTURES-ORIG.md §10) exhibits macro-mates no exchange
chain joins: their canon wings split founds 13/12 vs 12/13 while
`State.exchangeTwin_found` holds founds invariant along every chain. -/
def exchOrbit_to_sameOrbit : ExchOrbit → SameOrbit :=
  Quotient.lift (Quotient.mk sameOrbitSetoid)
    (fun _ _ h => Quotient.sound (exch_le_sameOrbit h))

@[simp]
theorem exchOrbit_to_sameOrbit_mk (u : State) :
    exchOrbit_to_sameOrbit (ExchOrbit.mk u) =
      Quotient.mk sameOrbitSetoid u :=
  rfl

/-- The forgetful map is surjective: every macro class is the image
of the physical class of any representative. -/
theorem exchOrbit_to_sameOrbit_surjective (q : SameOrbit) :
    ∃ p : ExchOrbit, exchOrbit_to_sameOrbit p = q := by
  obtain ⟨u, hu⟩ := Quotient.exists_rep q
  exact ⟨ExchOrbit.mk u, hu⟩

/-! ## §6. Per-pair locality: one exchange touches only its two seats -/

/-- **Per-pair locality**: a single exchange at a located pair
writes only the pair's two seat piles — the foundations, stock,
waste, and draw width are untouched, and every pile off the two
seats is verbatim.  The state-level per-pile rows are
`Orig.TwinExchange`'s (`State.exchangeTwin_pile_self`/`_other`/`_ne`,
the zone rows); this is the coarsening-grade package the
disjoint-family superposition and the torsor freeness ride. -/
theorem exch_local_pair {st : State} {t : Card} {a a' k : Anchor}
    (h₁ : st.pileHolding t = some a) (h₂ : st.pileHolding t.twin = some a')
    (hne : a ≠ a') (hk : k ≠ a ∧ k ≠ a') :
    (st.exchangeTwin t).piles k = st.piles k :=
  State.exchangeTwin_pile_ne h₁ h₂ hne hk.1 hk.2

/-! ## §7. The disjoint-family superposition and the torsor freeness -/

/-- The executed-bit composite: the total exchange folded over a
list of pair representatives. -/
def exchAll : State → List Card → State
  | st, [] => st
  | st, t :: ts => exchAll (st.exchangeTwin t) ts

/-- The disjoint-family data bundle at `st`: the list is
pair-distinct (no representative and its twin both present), every
pair sits located at two DISTINCT seats, and distinct pairs have
pairwise disjoint seats. -/
def ExchFamOk (st : State) (ts : List Card) : Prop :=
  ts.Nodup ∧ (∀ t ∈ ts, t.twin ∉ ts) ∧
    (∀ t ∈ ts, ∃ a a', st.pileHolding t = some a ∧
      st.pileHolding t.twin = some a' ∧ a ≠ a') ∧
    (∀ t ∈ ts, ∀ t' ∈ ts, t ≠ t' →
      st.pileHolding t ≠ st.pileHolding t' ∧
      st.pileHolding t ≠ st.pileHolding t'.twin ∧
      st.pileHolding t.twin ≠ st.pileHolding t' ∧
      st.pileHolding t.twin ≠ st.pileHolding t'.twin)

/-- Prefix-cancel on cons-shared appends: the agreeing spine pins the
tails (private; the list kit the identity pricing rides). -/
private theorem cons_append_cancel : ∀ (x l r : List Card),
    x ++ l = x ++ r → l = r
  | [], _, _, h => h
  | c :: xs, l, r, h =>
      cons_append_cancel xs l r (by
        injection h with h')

/-- Option-level seat disjointness, read at the two `some`s: from the
family bundle's search-inequalities to anchor inequalities. -/
private theorem opt_ne_to_anchor {st : State} {u v : Card} {bu av : Anchor}
    (hne : st.pileHolding u ≠ st.pileHolding v)
    (hu : st.pileHolding u = some bu) (hv : st.pileHolding v = some av) :
    bu ≠ av := by
  intro hcon
  exact hne (by rw [hu, hcon, hv])

/-- Off-seat cards keep their seat through an exchange: if `c` sits
face-up in a pile off the pair's two written seats, the search
relocates it verbatim — the pile is untouched and `WF`
search-exactness pins the answer (the location half of what the
private relocate census did pile-by-pile; the license-free grade). -/
theorem exch_pileHolding_off {st : State} {c t : Card} {k a a' : Anchor}
    (hwf : st.WF) (ha : st.pileHolding t = some a)
    (ha' : st.pileHolding t.twin = some a') (hne : a ≠ a')
    (hk : st.pileHolding c = some k) (hout : k ≠ a ∧ k ≠ a') :
    (st.exchangeTwin t).pileHolding c = some k :=
  (pileHolding_eq_some_iff (State.wf_exchangeTwin hwf ha ha' hne)).mpr
    (by rw [State.exchangeTwin_pile_ne ha ha' hne hout.1 hout.2]
        exact pileHolding_mem hk)

/-- Seat-data congruence of the single exchange: when `t` locates at
the same two seats at `s` and `st` and those seat piles agree, the
two single exchanges agree at both seat piles — the
superposition's term-level engine (only the seat piles are read). -/
theorem exchange_piles_congr {s st : State} {t : Card} {a a' : Anchor}
    (ha : st.pileHolding t = some a) (ha' : st.pileHolding t.twin = some a')
    (hne : a ≠ a')
    (hsa : s.pileHolding t = some a) (hsa' : s.pileHolding t.twin = some a')
    (hpa : s.piles a = st.piles a) (hpa' : s.piles a' = st.piles a') :
    (s.exchangeTwin t).piles a = (st.exchangeTwin t).piles a ∧
      (s.exchangeTwin t).piles a' = (st.exchangeTwin t).piles a' := by
  constructor
  · rw [State.exchangeTwin_pile_self hsa hsa' hne,
      State.exchangeTwin_pile_self ha ha' hne, hpa, hpa']
  · rw [State.exchangeTwin_pile_other hsa hsa' hne,
      State.exchangeTwin_pile_other ha ha' hne, hpa, hpa']

/-- **The disjoint-family superposition** (the per-pair locality of
the composite): executing a pair-distinct list of pairwise
seat-disjoint located pairs, the composite is the per-pile union of
the base-data single writes — each pair's bit writes exactly its
own two seats, read at the BASE state, and every pile off all the
seats stays verbatim.  WF-gated (the locatedness discipline rides
search exactness); no license needed — the licensed reading is the
corollary below. -/
theorem exch_superpose : ∀ (ts : List Card) (st : State), st.WF →
    ExchFamOk st ts →
    (∀ t ∈ ts, ∀ a a', st.pileHolding t = some a →
        st.pileHolding t.twin = some a' →
        (exchAll st ts).piles a = (st.exchangeTwin t).piles a ∧
        (exchAll st ts).piles a' = (st.exchangeTwin t).piles a') ∧
    (∀ k, (∀ t ∈ ts, st.pileHolding t ≠ some k ∧
        st.pileHolding t.twin ≠ some k) →
        (exchAll st ts).piles k = st.piles k) := by
  intro ts
  induction ts with
  | nil =>
      intro st _hwf _hok
      constructor
      · intro t ht; cases ht
      · intro k _; rfl
  | cons t₀ tail ih =>
      intro st hwf hok
      obtain ⟨hnd, hpair, hloc, hdisj⟩ := hok
      obtain ⟨hnd₀, hndt⟩ := List.nodup_cons.mp hnd
      obtain ⟨a₀, a₀', ha₀, ha₀', hne₀⟩ :=
        hloc t₀ (List.mem_cons_self ..)
      have hwf₁ : (st.exchangeTwin t₀).WF :=
        State.wf_exchangeTwin hwf ha₀ ha₀' hne₀
      -- the tail pairs' seats are off the head's two written seats
      have hoτ : ∀ τ ∈ tail, ∀ bb bb' : Anchor,
          st.pileHolding τ = some bb → st.pileHolding τ.twin = some bb' →
          bb ≠ a₀ ∧ bb ≠ a₀' ∧ bb' ≠ a₀ ∧ bb' ≠ a₀' := by
        intro τ hτ bb bb' hbb hbb'
        obtain ⟨ho1, ho2, ho3, ho4⟩ :=
          hdisj τ (List.mem_cons_of_mem _ hτ) t₀ (List.mem_cons_self ..)
            (fun hc => hnd₀ (by rw [← hc]; exact hτ))
        exact ⟨opt_ne_to_anchor ho1 hbb ha₀, opt_ne_to_anchor ho2 hbb ha₀',
          opt_ne_to_anchor ho3 hbb' ha₀, opt_ne_to_anchor ho4 hbb' ha₀'⟩
      -- the tail searches re-anchor identically at the exchanged base
      have hoffτ : ∀ τ ∈ tail,
          (st.exchangeTwin t₀).pileHolding τ = st.pileHolding τ ∧
          (st.exchangeTwin t₀).pileHolding τ.twin = st.pileHolding τ.twin := by
        intro τ hτ
        obtain ⟨b, b', hb, hb', -⟩ := hloc τ (List.mem_cons_of_mem _ hτ)
        obtain ⟨hb0, hb0', hb'0, hb'0'⟩ := hoτ τ hτ b b' hb hb'
        constructor
        · rw [exch_pileHolding_off hwf ha₀ ha₀' hne₀ hb ⟨hb0, hb0'⟩]
          exact hb.symm
        · rw [exch_pileHolding_off hwf ha₀ ha₀' hne₀ hb' ⟨hb'0, hb'0'⟩]
          exact hb'.symm
      -- the tail family stays OK at the exchanged base
      have hoktail : ExchFamOk (st.exchangeTwin t₀) tail := by
        refine ⟨(List.nodup_cons.mp hnd).2,
          fun t ht hmem => hpair t (List.mem_cons_of_mem _ ht)
            (List.mem_cons_of_mem _ hmem), ?_, ?_⟩
        · intro τ hτ
          obtain ⟨b, b', hb, hb', hneb⟩ := hloc τ (List.mem_cons_of_mem _ hτ)
          obtain ⟨hb0, hb0', hb'0, hb'0'⟩ := hoτ τ hτ b b' hb hb'
          exact ⟨b, b',
            exch_pileHolding_off hwf ha₀ ha₀' hne₀ hb ⟨hb0, hb0'⟩,
            exch_pileHolding_off hwf ha₀ ha₀' hne₀ hb' ⟨hb'0, hb'0'⟩,
            hneb⟩
        · intro τ hτ τ' hτ' hneτ
          obtain ⟨hoff1, hoff2⟩ := hoffτ τ hτ
          obtain ⟨hoff1', hoff2'⟩ := hoffτ τ' hτ'
          rw [hoff1, hoff2, hoff1', hoff2']
          exact hdisj τ (List.mem_cons_of_mem _ hτ)
            τ' (List.mem_cons_of_mem _ hτ') hneτ
      obtain ⟨ihseat, ihunt⟩ := ih (st.exchangeTwin t₀) hwf₁ hoktail
      constructor
      · -- the seat thesis
        intro t ht a a' hht1 hht2
        rcases List.mem_cons.mp ht with heq | htail
        · -- the head's own seats: the tail never re-writes them
          rw [heq] at hht1 hht2
          rw [heq]
          have hab : a = a₀ := pileHolding_inj hht1 ha₀
          have hab' : a' = a₀' := pileHolding_inj hht2 ha₀'
          rw [hab, hab']
          have hcond : ∀ τ ∈ tail,
              (st.exchangeTwin t₀).pileHolding τ ≠ some a₀ ∧
              (st.exchangeTwin t₀).pileHolding τ.twin ≠ some a₀ := by
            intro τ hτ
            obtain ⟨b, b', hb, hb', -⟩ := hloc τ (List.mem_cons_of_mem _ hτ)
            obtain ⟨hb0, hb0', hb'0, hb'0'⟩ := hoτ τ hτ b b' hb hb'
            constructor
            · rw [exch_pileHolding_off hwf ha₀ ha₀' hne₀ hb ⟨hb0, hb0'⟩]
              exact fun hcc => hb0 (Option.some.inj hcc)
            · rw [exch_pileHolding_off hwf ha₀ ha₀' hne₀ hb' ⟨hb'0, hb'0'⟩]
              exact fun hcc => hb'0 (Option.some.inj hcc)
          have hcond' : ∀ τ ∈ tail,
              (st.exchangeTwin t₀).pileHolding τ ≠ some a₀' ∧
              (st.exchangeTwin t₀).pileHolding τ.twin ≠ some a₀' := by
            intro τ hτ
            obtain ⟨b, b', hb, hb', -⟩ := hloc τ (List.mem_cons_of_mem _ hτ)
            obtain ⟨hb0, hb0', hb'0, hb'0'⟩ := hoτ τ hτ b b' hb hb'
            constructor
            · rw [exch_pileHolding_off hwf ha₀ ha₀' hne₀ hb ⟨hb0, hb0'⟩]
              exact fun hcc => hb0' (Option.some.inj hcc)
            · rw [exch_pileHolding_off hwf ha₀ ha₀' hne₀ hb' ⟨hb'0, hb'0'⟩]
              exact fun hcc => hb'0' (Option.some.inj hcc)
          constructor
          · show (exchAll (st.exchangeTwin t₀) tail).piles a₀ = _
            exact ihunt a₀ hcond
          · show (exchAll (st.exchangeTwin t₀) tail).piles a₀' = _
            exact ihunt a₀' hcond'
        · -- a tail member's seats: the head never wrote them, so the
          -- single exchange at the exchanged base agrees with the
          -- single exchange at the base
          obtain ⟨b, b', hb, hb', hneb⟩ := hloc t ht
          have hab : a = b := pileHolding_inj hht1 hb
          have hab' : a' = b' := pileHolding_inj hht2 hb'
          rw [hab, hab']
          obtain ⟨hoff1, hoff2⟩ := hoffτ t htail
          obtain ⟨s1seat1, s1seat2⟩ :=
            ihseat t htail b b' (hoff1.trans hb) (hoff2.trans hb')
          obtain ⟨hb0, hb0', hb'0, hb'0'⟩ := hoτ t htail b b' hb hb'
          obtain ⟨cg1, cg2⟩ :=
            exchange_piles_congr hb hb' hneb (hoff1.trans hb) (hoff2.trans hb')
              (exch_local_pair ha₀ ha₀' hne₀ ⟨hb0, hb0'⟩)
              (exch_local_pair ha₀ ha₀' hne₀ ⟨hb'0, hb'0'⟩)
          constructor
          · show (exchAll (st.exchangeTwin t₀) tail).piles b = _
            rw [s1seat1, cg1]
          · show (exchAll (st.exchangeTwin t₀) tail).piles b' = _
            rw [s1seat2, cg2]
      · -- the untouched thesis
        intro k hklist
        have hka₀ : k ≠ a₀ := fun hc =>
          (hklist t₀ (List.mem_cons_self ..)).1 (by rw [ha₀, hc])
        have hka₀' : k ≠ a₀' := fun hc =>
          (hklist t₀ (List.mem_cons_self ..)).2 (by rw [ha₀', hc])
        show (exchAll (st.exchangeTwin t₀) tail).piles k = st.piles k
        refine (ihunt k ?_).trans (exch_local_pair ha₀ ha₀' hne₀ ⟨hka₀, hka₀'⟩)
        intro τ hτ
        obtain ⟨hoff1, hoff2⟩ := hoffτ τ hτ
        obtain ⟨bk1, bk2⟩ := hklist τ (List.mem_cons_of_mem _ hτ)
        rw [hoff1, hoff2]
        exact ⟨bk1, bk2⟩

/-- **The identity pricing row**: at a located-distinct pair, a
genuinely moving exchange writes its own first seat differently —
the written run and the base run share the prefix through the host,
so their equality forces the two suffixes to agree, and agreeing
suffixes make BOTH writes the identity (the exchange is then the
state's identity, and the licensed both-bare bit is exactly the
case that prices at zero). -/
theorem exchangeTwin_ne_self_pile {st : State} {t : Card} {a a' : Anchor}
    (h₁ : st.pileHolding t = some a) (h₂ : st.pileHolding t.twin = some a')
    (hne : a ≠ a') (hmove : st.exchangeTwin t ≠ st) :
    (st.exchangeTwin t).piles a ≠ st.piles a := by
  intro hcon
  apply hmove
  have hTa : t ∈ (st.piles a).faceUp := pileHolding_mem h₁
  have hTb : t.twin ∈ (st.piles a').faceUp := pileHolding_mem h₂
  have hsA : (st.piles a).faceUp =
      below t ((st.piles a).faceUp) ++
        t :: aboveIn t ((st.piles a).faceUp) :=
    below_aboveIn_split hTa
  have hsA' : (st.piles a').faceUp =
      below t.twin ((st.piles a').faceUp) ++
        t.twin :: aboveIn t.twin ((st.piles a').faceUp) :=
    below_aboveIn_split hTb
  have hA : below t ((st.piles a).faceUp) ++
        t :: aboveIn t.twin ((st.piles a').faceUp) = (st.piles a).faceUp := by
    have hcon' := hcon
    rw [State.exchangeTwin_pile_self h₁ h₂ hne] at hcon'
    exact (Pile.ext_iff.mp hcon').2
  have hD0 : t :: aboveIn t.twin ((st.piles a').faceUp) =
      t :: aboveIn t ((st.piles a).faceUp) :=
    cons_append_cancel _ _ _ (hA.trans hsA)
  injection hD0 with _ hD
  apply State.ext
  · rw [State.exchangeTwin_found]
  · funext k
    by_cases hk : k = a
    · rw [hk]; exact hcon
    · by_cases hk' : k = a'
      · rw [hk']
        rw [State.exchangeTwin_pile_other h₁ h₂ hne]
        apply Pile.ext
        · rfl
        · calc below t.twin ((st.piles a').faceUp) ++
                t.twin :: aboveIn t ((st.piles a).faceUp)
                = below t.twin ((st.piles a').faceUp) ++
                    t.twin :: aboveIn t.twin ((st.piles a').faceUp) := by
                  rw [hD]
              _ = (st.piles a').faceUp := hsA'.symm
      · rw [State.exchangeTwin_pile_ne h₁ h₂ hne hk hk']
  · rw [State.exchangeTwin_stock]
  · rw [State.exchangeTwin_waste]
  · rw [State.exchangeTwin_drawStep]

/-- **The torsor freeness** (the landing-2 card item, carrying the
landing-1 probe's amendment): distinct swap-subsets give distinct
states at a disjoint-seat base — restricted to the NON-IDENTITY
bits; identity-valued bits (the licensed both-bare degenerate form)
price at zero and claim no state.  The witness pair `w` is executed
by `ts` but not by `us`, and `w`'s two seats are claimed by no
member of `us`.  The proof is the partition of the deck: both
composites are the base-data superposition, so at `w`'s first seat
one composite carries the genuine bit-write while the other keeps
the base pile. -/
theorem exch_free {st : State} (hwf : st.WF) (w : Card) (ts us : List Card)
    (hokts : ExchFamOk st ts) (hokus : ExchFamOk st us)
    (hw : w ∈ ts) (_hwus : w ∉ us)
    (hcross : ∀ u ∈ us, st.pileHolding u ≠ st.pileHolding w ∧
        st.pileHolding u ≠ st.pileHolding w.twin ∧
        st.pileHolding u.twin ≠ st.pileHolding w ∧
        st.pileHolding u.twin ≠ st.pileHolding w.twin)
    (hmove : st.exchangeTwin w ≠ st) :
    exchAll st ts ≠ exchAll st us := by
  obtain ⟨hndts, hpairsts, hlocts, hdisjts⟩ := hokts
  obtain ⟨a, a', hw1, hw2, hnew⟩ := hlocts w hw
  have hsupts := exch_superpose ts st hwf ⟨hndts, hpairsts, hlocts, hdisjts⟩
  have hwrit := hsupts.1 w hw a a' hw1 hw2
  have hsupus := exch_superpose us st hwf hokus
  intro hcon
  have huclaim : ∀ u ∈ us, st.pileHolding u ≠ some a ∧
      st.pileHolding u.twin ≠ some a := by
    intro u hu
    obtain ⟨hc1, _, hc3, _⟩ := hcross u hu
    rw [hw1] at hc1 hc3
    exact ⟨hc1, hc3⟩
  have hbase := hsupus.2 a huclaim
  refine (exchangeTwin_ne_self_pile hw1 hw2 hnew hmove) ?_
  rw [← hbase, ← hwrit.1, hcon]

/-! ## The landing-2 audit (fresh, in-file)

Every new head of this card's §5–§7, audited where the axioms are
read.  Expected: `[propext, Quot.sound]` or fewer; no
`Classical.choice` anywhere (the coarsening is the constructive
one-move realization of the realizations; the superposition and the
freeness are pure search bookkeeping). -/

#print axioms exch_leg_RevEqW
#print axioms exch_chain_RevEqW
#print axioms exch_le_sameOrbit
#print axioms exchOrbit_to_sameOrbit
#print axioms exchOrbit_to_sameOrbit_mk
#print axioms exchOrbit_to_sameOrbit_surjective
#print axioms exch_local_pair
#print axioms exch_pileHolding_off
#print axioms exchange_piles_congr
#print axioms exch_superpose
#print axioms exchangeTwin_ne_self_pile
#print axioms exch_free

