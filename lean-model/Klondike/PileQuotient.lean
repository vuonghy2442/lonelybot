import Klondike.PileSwap

/-!
# The pile quotient — the state space modulo whole-pile transpositions

The pile transposition Π (`Klondike/PileSwap.lean`) is a state-level
symmetry: `solvable_swapPiles_iff` says every single transposition
preserves the solvability verdict.  This file is the *quotient* the
symmetry demands: the setoid — the equivalence closure of the pile
transpositions on `State` — the descent of the engine move-set to
it, and the lifted solvability verdicts.

The family (sorry-free, axiom targets `[propext, Quot.sound]`):

* **§1 The setoid.**   `PileSwapStep` is the one-transposition
  relation (`b = a.swapPiles i j`), `PileSwapOrbit` its equivalence
  closure (the local `EqvClosure` spine, §0), `pileSwapSetoid` the
  same as a `Setoid`
  *value* — deliberately not a global instance; the quotient layers
  of the twin lines coexist with this one — and `PileClass` the
  class type, with `PileClass.mk_pileSwapPiles` (a swap does not
  move the class) as the soundness workhorse.
* **§2 The engine move-set descends.** A *fixed* move does not
  descend — Π maps the move along (`apply_swapPiles` conjugates `m`
  to `Move.swapM i j m`) — but the SET of engine successors does:
  `engineSuccSet_swapPiles` (one swap does not change the successor
  classes; `apply_swapPiles` + `swapM_isEngine` +
  `Move.swapM_swapM`), `engineSuccSet_orbit` (the closure lift), and
  the well-defined `EngineSuccQ : PileClass → PileClass → Prop`
  with `engineSuccQ_mk_iff` — the quotient's one-step dynamics.
* **§3 Solvability lifts, both directions.** `solvableQ` over
  `PileClass` (via `solvable_swapPiles_iff` closed under the
  closure by induction: `solvableQ_mk_iff`), and the
  engine-restricted twin `solvableEngineQ`.
* **§4 The content quotient.** Two states sharing a deal are
  Π-related only trivially (`swapPiles_eq_sameDeal_forced_eq`,
  PileSwap §7) — the *content* comparison of pristine-like boards
  needs the inert-deal wash included: `PileContentStep` extends the
  one-step relation with `State.setDeal` overwrites AT all-emptied
  states (`State.depthsZero`, where the deal is solvability-inert
  — `solvableFrom_setDeal_iff_of_depthsZero`), `PileContentClass`
  is the resulting quotient with the lifted verdicts `solvableCW`
  and the descended engine successor set `EngineSuccCW`.  Two
  structure theorems calve the quotients apart:
  `depthsZero_contentOrbit_iff` (the emptied-ness flag is a class
  invariant) and `pileSwapOrbit_of_contentOrbit_of_not_depthsZero`
  (off the emptied fragment the wash adds nothing — the pure-Π
  orbits ARE the content classes there).
* **§5 The pristine collapse, as ONE orbit.** At a state whose piles
  are all fully emptied (`depthsZero`, empty matching), the
  Draw-commitment landings on ANY two anchors are the SAME content
  class: `emptyPiles_land_content_eq` — the sibling wave's
  equi-solvability (`emptyPiles_kingLandings_collapse`,
  witnesses/PileSwapConsequences.lean) restated at the setoid level:
  the seven vacant anchors carry identical (empty) content, so all
  usable anchor candidates form ONE swap-orbit.
* **§6 The chain representation and the same-deal fiber.** Every
  orbit is a concrete swap chain: `pileSwapOrbit_exists_applySwaps`
  over `State.applySwaps`, with the composition calculi
  (`applySwaps_piles`/`_depths`/`_board`), and the capstone
  `pileSwapOrbit_sameDeal_eq`: at a WF-deal state the orbit meets
  the same-deal fiber only at the state itself — a swap chain
  that permutes the deal slices back to themselves composes to the
  identity, because the seven slots have distinct lengths
  (`Anchor.toIdx_inj`).  With §4's purity,
  `pileContentOrbit_sameDeal_eq` transfers this off the emptied
  fragment — the wave-20 reachable-corner survival
  (`witnesses/PileSwapConsequences.lean` §2, the single-step
  `ReachCorner.sLand_swapRelated_iff`) upgrades from single steps
  to the FULL quotient: the countermodels' separation is
  orbit-structural (see `witnesses/PileQuotientCorollaries.lean`).
* **§7 The anchor landings' orbit carving (wave-22, king-graded
  kernel).**  The `Draw` commitment's ANCHOR landings carry a fully
  carved orbit structure: at a WF-deal state two anchor landings are
  pure-Π-related EXACTLY on anchor equality
  (`drawLand_pileSwapOrbit_iff` — the §6 fiber read along
  `applyDrawTo`), so each usable vacant anchor is its own orbit; on
  the all-emptied fragment ANY two landings merge into one content
  class with NO board-emptiness premise
  (`drawLand_content_eq_of_depthsZero` — strictly generalizing §5's
  `emptyPiles_land_content_eq`, whose empty board was a proof-route
  artifact: the emptied fragment carries no anchor content at all),
  and off it the content classes separate as well
  (`drawLand_content_class_inj`, by §4 purity).  The induced
  swap-orbit on usable vacant anchors — the king-side graded bound's
  counting object — is therefore the identity relation on anchors
  whenever deal content remains, and ONE class whenever it does not.
-/

/-! ## §0. The closure spine (the hand-rolled `EqvGen`)

This toolchain's core does not export an equivalence-closure
inductive, so the quotient's spine is local: the reflexive-transitive
closure `EqvClosure`, with the constructors the induction arguments
below consume.  (Symmetry is NOT constructor-generic: each orbit
proves its own `symm` from its step relation's symmetry — the pile
transposition by its involutivity, the inert-deal wash by the
overwrite's own overwrite-back; see §4.) -/

/-- The reflexive-transitive closure of a relation: the quotient
spine's carrier builder. -/
inductive EqvClosure (r : α → α → Prop) : α → α → Prop where
  | refl (x : α) : EqvClosure r x x
  | single {x y : α} : r x y → EqvClosure r x y
  | trans {x y z : α} : EqvClosure r x y → EqvClosure r y z → EqvClosure r x z

/-! ## §1. The setoid: the closure of pile transpositions -/

/-- The one-step relation: `b` is one pile transposition of `a`
(any pair of anchors, the degenerate one included). -/
def PileSwapStep (a b : State) : Prop := ∃ i j, b = a.swapPiles i j

/-- **The setoid's carrier relation**: the equivalence closure of
the pile transpositions. -/
def PileSwapOrbit (a b : State) : Prop := EqvClosure PileSwapStep a b

/-- The symmetry of the closure (by closure induction; the step
relation is symmetric by the swap's involutivity). -/
theorem PileSwapOrbit.symm {a b : State} (h : PileSwapOrbit a b) :
    PileSwapOrbit b a := by
  induction h with
  | refl x => exact EqvClosure.refl x
  | @single x y hstep =>
      obtain ⟨i, j, hb⟩ := hstep
      refine EqvClosure.single ⟨i, j, ?_⟩
      rw [hb, State.swapPiles_swapPiles]
  | trans _ _ ih₁ ih₂ => exact EqvClosure.trans ih₂ ih₁

/-- The setoid, as an explicit `Setoid State` value.  Deliberately
NOT registered as an instance: the quotient layers of the twin
lines and the content quotient of §4 coexist in this library, and
a global `Setoid State` would make every `≈` ambiguous. -/
def pileSwapSetoid : Setoid State where
  r := PileSwapOrbit
  iseqv := ⟨fun a => EqvClosure.refl a, fun h => PileSwapOrbit.symm h,
    fun h₁ h₂ => EqvClosure.trans h₁ h₂⟩

/-- **The pile class type.** -/
abbrev PileClass := Quot PileSwapOrbit

/-- The class of a state. -/
def PileClass.mk (st : State) : PileClass := Quot.mk _ st

/-- A swap does not move the class. -/
theorem PileClass.mk_pileSwapPiles (st : State) (i j : Anchor) :
    PileClass.mk (st.swapPiles i j) = PileClass.mk st :=
  Quot.sound (EqvClosure.single ⟨i, j, (State.swapPiles_swapPiles st i j).symm⟩)

/-- Classes are equal along the closure (the `Quot.sound` reading). -/
theorem PileClass.mk_eq_mk {a b : State} (h : PileSwapOrbit a b) :
    PileClass.mk a = PileClass.mk b := Quot.sound h

/-- The `sound` converse: equal classes carry the closure witness —
the orbit-through-`a` is itself a sound lift, so a `mk`-equality
unfolds into the relation (the homemade `Quot.exact`). -/
theorem PileClass.exact {a b : State} (h : PileClass.mk a = PileClass.mk b) :
    PileSwapOrbit a b := by
  have hf : ∀ (x y : State), PileSwapOrbit x y →
      (PileSwapOrbit a x) = (PileSwapOrbit a y) := by
    intro x y hxy
    apply propext
    constructor
    · intro hax
      exact EqvClosure.trans hax hxy
    · intro hay
      exact EqvClosure.trans hay (PileSwapOrbit.symm hxy)
  have h1 : Quot.lift (fun x => PileSwapOrbit a x) hf (PileClass.mk a)
      = Quot.lift (fun x => PileSwapOrbit a x) hf (PileClass.mk b) := by
    rw [h]
  have h1 : PileSwapOrbit a a = PileSwapOrbit a b := h1
  have h2 : PileSwapOrbit a a := EqvClosure.refl a
  rw [h1] at h2
  exact h2

/-! ## §2. The engine move-set descends to classes -/

/-- The engine successor CLASSES of a state: every engine move's
successor, taken in the quotient. -/
def engineSuccSet (st : State) : PileClass → Prop :=
  fun c => ∃ m, m.isEngine = true ∧
    ∃ st', st.apply m = some st' ∧ PileClass.mk st' = c

/-- One swap does not move the engine successors: every engine
successor of the swapped state is the conjugated move of the
original, with its successor swapped within one class.  The
conjugation ties the two readings:
`apply_swapPiles` (the successor conjugates), `swapM_swapM` (it is
an involution on moves), `swapM_isEngine` (the conjugate is engine
exactly when the move is). -/
theorem engineSuccSet_swapPiles_sub (st : State) (i j : Anchor) (c : PileClass)
    (h : engineSuccSet (st.swapPiles i j) c) : engineSuccSet st c := by
  obtain ⟨m, heng, t, hapt, hc⟩ := h
  have mdef : Move.swapM i j (Move.swapM i j m) = m := Move.swapM_swapM i j m
  rw [← mdef] at hapt
  rw [apply_swapPiles i j (Move.swapM i j m) st] at hapt
  obtain ⟨s, hsap, hse⟩ := Option.map_eq_some_iff.mp hapt
  have hse' : s.swapPiles i j = t := hse
  refine ⟨Move.swapM i j m, ?_, s, hsap, ?_⟩
  · have hsw := swapM_isEngine i j (Move.swapM i j m)
    rw [mdef] at hsw
    rw [← hsw]
    exact heng
  · rw [← hse'] at hc
    rw [hc.symm]
    exact (PileClass.mk_pileSwapPiles s i j).symm

/-- The full one-swap invariance of the engine successor set. -/
theorem engineSuccSet_swapPiles (st : State) (i j : Anchor) :
    engineSuccSet (st.swapPiles i j) = engineSuccSet st := by
  funext c
  apply propext
  constructor
  · exact engineSuccSet_swapPiles_sub st i j c
  · intro hcity
    refine engineSuccSet_swapPiles_sub (st.swapPiles i j) i j c ?_
    rw [State.swapPiles_swapPiles]
    exact hcity

/-- The descent closes under the orbit (closure induction). -/
theorem engineSuccSet_orbit {a b : State} (h : PileSwapOrbit a b) :
    engineSuccSet a = engineSuccSet b := by
  induction h with
  | refl x => rfl
  | @single x y hstep =>
      obtain ⟨i, j, hb⟩ := hstep
      rw [hb]
      exact (engineSuccSet_swapPiles x i j).symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- **The quotient's dynamics**: the engine successor-class
predicate is well-defined on classes. -/
def EngineSuccQ (c : PileClass) : PileClass → Prop :=
  Quot.lift engineSuccSet
    (fun (a b : State) (h : PileSwapOrbit a b) => engineSuccSet_orbit h) c

/-- The descended move-set is the represented one. -/
theorem engineSuccQ_mk_iff (st : State) (c : PileClass) :
    EngineSuccQ (PileClass.mk st) c ↔
      ∃ m, m.isEngine = true ∧
        ∃ st', st.apply m = some st' ∧ PileClass.mk st' = c :=
  Iff.rfl

/-! ## §3. Solvability lifts, both directions -/

/-- One orbit transports solvability forward (closure induction over
`solvable_swapPiles_iff`). -/
theorem solvableFrom_pileSwapStep {a b : State}
    (h : PileSwapOrbit a b) (hs : a.solvableFrom) : b.solvableFrom := by
  have key : ∀ (x y : State), PileSwapOrbit x y → (x.solvableFrom → y.solvableFrom) := by
    intro x y h'
    induction h' with
    | refl x => exact fun hs => hs
    | @single x' y' hstep =>
        obtain ⟨i, j, hb⟩ := hstep
        intro hs
        rw [hb]
        exact (solvable_swapPiles_iff i j x').mp hs
    | trans _ _ ih₁ ih₂ => exact fun hs => ih₂ (ih₁ hs)
  exact key a b h hs

/-- **The quotient-validity lift, both directions**: the solvability
verdict is constant along the orbit. -/
theorem solvableFrom_pileSwapOrbit_iff {a b : State} (h : PileSwapOrbit a b) :
    a.solvableFrom ↔ b.solvableFrom :=
  ⟨fun hs => solvableFrom_pileSwapStep h hs,
    fun hs => solvableFrom_pileSwapStep h.symm hs⟩

/-- The lift of the solvability verdict to the pile class. -/
def solvableQ (c : PileClass) : Prop :=
  Quot.lift (fun (st : State) => st.solvableFrom)
    (fun (a b : State) (h : PileSwapOrbit a b) =>
      propext (solvableFrom_pileSwapOrbit_iff h)) c

theorem solvableQ_mk_iff (st : State) :
    solvableQ (PileClass.mk st) ↔ st.solvableFrom := Iff.rfl

/-- The engine-restricted verdict transports along the orbit. -/
theorem solvableEngine_pileSwapStep {a b : State}
    (h : PileSwapOrbit a b) (hs : a.solvableEngine) : b.solvableEngine := by
  have key : ∀ (x y : State), PileSwapOrbit x y → (x.solvableEngine → y.solvableEngine) := by
    intro x y h'
    induction h' with
    | refl x => exact fun hs => hs
    | @single x' y' hstep =>
        obtain ⟨i, j, hb⟩ := hstep
        intro hs
        rw [hb]
        exact (solvableEngine_swapPiles_iff i j x').mp hs
    | trans _ _ ih₁ ih₂ => exact fun hs => ih₂ (ih₁ hs)
  exact key a b h hs

theorem solvableEngine_pileSwapOrbit_iff {a b : State}
    (h : PileSwapOrbit a b) : a.solvableEngine ↔ b.solvableEngine :=
  ⟨fun hs => solvableEngine_pileSwapStep h hs,
    fun hs => solvableEngine_pileSwapStep h.symm hs⟩

/-- The lift of the engine-restricted solvability verdict. -/
def solvableEngineQ (c : PileClass) : Prop :=
  Quot.lift (fun (st : State) => st.solvableEngine)
    (fun (a b : State) (h : PileSwapOrbit a b) =>
      propext (solvableEngine_pileSwapOrbit_iff h)) c

theorem solvableEngineQ_mk_iff (st : State) :
    solvableEngineQ (PileClass.mk st) ↔ st.solvableEngine := Iff.rfl

/-! ## §4. The content quotient: the orbit with the inert-deal wash -/

/-- The content-blind one-step relation: a pile transposition, or —
at a state whose hidden stacks are all empty, where the deal is
solvability-inert (`State.depthsZero`) — an arbitrary deal
overwrite. -/
def PileContentStep (a b : State) : Prop :=
  PileSwapStep a b ∨ (a.depthsZero ∧ ∃ d, b = a.setDeal d)

/-- The content class relation: the closure of the two generators. -/
def PileContentOrbit (a b : State) : Prop := EqvClosure PileContentStep a b

theorem PileContentOrbit.symm {a b : State} (h : PileContentOrbit a b) :
    PileContentOrbit b a := by
  induction h with
  | refl x => exact EqvClosure.refl x
  | @single x y hstep =>
      rcases hstep with ⟨i, j, hb⟩ | ⟨hz, d, hb⟩
      · refine EqvClosure.single (Or.inl ⟨i, j, ?_⟩)
        rw [hb, State.swapPiles_swapPiles]
      · subst hb
        refine EqvClosure.single (Or.inr ⟨State.depthsZero_setDeal hz d, x.deal, ?_⟩)
        rw [State.setDeal_setDeal]
        rfl
  | trans _ _ ih₁ ih₂ => exact EqvClosure.trans ih₂ ih₁

/-- The content setoid (an explicit value, as in §1). -/
def pileContentSetoid : Setoid State where
  r := PileContentOrbit
  iseqv := ⟨fun a => EqvClosure.refl a, fun h => PileContentOrbit.symm h,
    fun h₁ h₂ => EqvClosure.trans h₁ h₂⟩

/-- **The content class type.** -/
abbrev PileContentClass := Quot PileContentOrbit

/-- The content class of a state. -/
def PileContentClass.mk (st : State) : PileContentClass := Quot.mk _ st

/-- A swap does not move the content class. -/
theorem PileContentClass.mk_pileSwapPiles (st : State) (i j : Anchor) :
    PileContentClass.mk (st.swapPiles i j) = PileContentClass.mk st :=
  Quot.sound (EqvClosure.single (Or.inl ⟨i, j, (State.swapPiles_swapPiles st i j).symm⟩))

/-- An inert-deal overwrite does not move the content class. -/
theorem PileContentClass.mk_setDeal (st : State) (hz : st.depthsZero) (d : Deal) :
    PileContentClass.mk (st.setDeal d) = PileContentClass.mk st :=
  Quot.sound (EqvClosure.single (Or.inr ⟨State.depthsZero_setDeal hz d, st.deal, rfl⟩))

/-- The `sound` converse for content classes (the homemade
`Quot.exact`). -/
theorem PileContentClass.exact {a b : State}
    (h : PileContentClass.mk a = PileContentClass.mk b) :
    PileContentOrbit a b := by
  have hf : ∀ (x y : State), PileContentOrbit x y →
      (PileContentOrbit a x) = (PileContentOrbit a y) := by
    intro x y hxy
    apply propext
    constructor
    · intro hax
      exact EqvClosure.trans hax hxy
    · intro hay
      exact EqvClosure.trans hay (PileContentOrbit.symm hxy)
  have h1 : Quot.lift (fun x => PileContentOrbit a x) hf (PileContentClass.mk a)
      = Quot.lift (fun x => PileContentOrbit a x) hf (PileContentClass.mk b) := by
    rw [h]
  have h1 : PileContentOrbit a a = PileContentOrbit a b := h1
  have h2 : PileContentOrbit a a := EqvClosure.refl a
  rw [h1] at h2
  exact h2

/-- The pure-Π orbits refine the content orbits. -/
theorem pileContentOrbit_of_pileSwapOrbit {a b : State} (h : PileSwapOrbit a b) :
    PileContentOrbit a b := by
  induction h with
  | refl x => exact EqvClosure.refl x
  | @single x' y' hstep =>
      obtain ⟨i, j, hb⟩ := hstep
      exact EqvClosure.single (Or.inl ⟨i, j, hb⟩)
  | trans _ _ ih₁ ih₂ => exact EqvClosure.trans ih₁ ih₂

/-- The all-emptied flag survives a swap, both directions. -/
theorem State.depthsZero_swapPiles_iff (st : State) (i j : Anchor) :
    (st.swapPiles i j).depthsZero ↔ st.depthsZero := by
  constructor
  · intro h
    have h2 := State.depthsZero_swapPiles (st := st.swapPiles i j) (i := i) (j := j) h
    rw [State.swapPiles_swapPiles] at h2
    exact h2
  · exact fun h => State.depthsZero_swapPiles h i j

/-- The all-emptied flag is a class invariant of the content orbit. -/
theorem depthsZero_contentStep_iff {a b : State} (h : PileContentStep a b) :
    a.depthsZero ↔ b.depthsZero := by
  rcases h with ⟨i, j, hb⟩ | ⟨hz, d, hb⟩
  · rw [hb]
    exact (State.depthsZero_swapPiles_iff a i j).symm
  · rw [hb]
    exact ⟨fun _ => State.depthsZero_setDeal hz d, fun _ => hz⟩

theorem depthsZero_contentOrbit_iff {a b : State} (h : PileContentOrbit a b) :
    a.depthsZero ↔ b.depthsZero := by
  induction h with
  | refl x => exact Iff.rfl
  | @single x' y' hstep => exact depthsZero_contentStep_iff hstep
  | trans _ _ ih₁ ih₂ => exact Iff.trans ih₁ ih₂

/-- **The off-fragment purity**: at a state with a live hidden
stack, the wash never fires along the content orbit — the content
class is exactly the pure-Π orbit. -/
theorem pileSwapOrbit_of_contentOrbit_of_not_depthsZero {a b : State}
    (h : PileContentOrbit a b) (hnz : ¬ a.depthsZero) : PileSwapOrbit a b := by
  revert hnz
  induction h with
  | refl x => intro _; exact EqvClosure.refl x
  | @single x y hstep =>
      intro hnz
      rcases hstep with ⟨i, j, hb⟩ | ⟨hz, _, _⟩
      · exact EqvClosure.single ⟨i, j, hb⟩
      · exact absurd hz hnz
  | @trans x y z hab hbc ih₁ ih₂ =>
      intro hnz
      refine EqvClosure.trans (ih₁ hnz) (ih₂ ?_)
      intro hzY
      exact hnz ((depthsZero_contentOrbit_iff hab).mpr hzY)

/-- The content successor CLASSES of a state. -/
def engineSuccContent (st : State) : PileContentClass → Prop :=
  fun c => ∃ m, m.isEngine = true ∧
    ∃ st', st.apply m = some st' ∧ PileContentClass.mk st' = c

/-- An inert-deal overwrite does not move the engine successors of
an all-emptied state: `apply_setDeal_eq_of_depthsZero` conjugates
the steps, the stay-successors' all-emptied persistence
(`depthsZero_apply`) makes the overwrites themselves class-trivial. -/
theorem engineSuccContent_setDeal_sub (st : State) (hz : st.depthsZero)
    (d : Deal) (c : PileContentClass)
    (h : engineSuccContent (st.setDeal d) c) : engineSuccContent st c := by
  obtain ⟨m, heng, t, hapt, hc⟩ := h
  have hw : (st.setDeal d).apply m = (st.apply m).map (fun s => s.setDeal d) :=
    State.apply_setDeal_eq_of_depthsZero hz m d
  rw [hw] at hapt
  obtain ⟨s, hsap, hse⟩ := Option.map_eq_some_iff.mp hapt
  have hse' : s.setDeal d = t := hse
  have hzs : s.depthsZero := State.depthsZero_apply hsap hz
  refine ⟨m, heng, s, hsap, ?_⟩
  rw [← hse'] at hc
  rw [← hc]
  exact (PileContentClass.mk_setDeal s hzs d).symm

/-- One swap does not move the content successor set (the §2
argument, over content classes). -/
theorem engineSuccContent_swapPiles_sub (st : State) (i j : Anchor)
    (c : PileContentClass)
    (h : engineSuccContent (st.swapPiles i j) c) : engineSuccContent st c := by
  obtain ⟨m, heng, t, hapt, hc⟩ := h
  have mdef : Move.swapM i j (Move.swapM i j m) = m := Move.swapM_swapM i j m
  rw [← mdef] at hapt
  rw [apply_swapPiles i j (Move.swapM i j m) st] at hapt
  obtain ⟨s, hsap, hse⟩ := Option.map_eq_some_iff.mp hapt
  have hse' : s.swapPiles i j = t := hse
  refine ⟨Move.swapM i j m, ?_, s, hsap, ?_⟩
  · have hsw := swapM_isEngine i j (Move.swapM i j m)
    rw [mdef] at hsw
    rw [← hsw]
    exact heng
  · rw [← hse'] at hc
    rw [hc.symm]
    exact (PileContentClass.mk_pileSwapPiles s i j).symm

/-- The two content successor-set invariances, as equalities. -/
theorem engineSuccContent_swapPiles (st : State) (i j : Anchor) :
    engineSuccContent (st.swapPiles i j) = engineSuccContent st := by
  funext c
  apply propext
  constructor
  · exact engineSuccContent_swapPiles_sub st i j c
  · intro hcity
    refine engineSuccContent_swapPiles_sub (st.swapPiles i j) i j c ?_
    rw [State.swapPiles_swapPiles]
    exact hcity

theorem engineSuccContent_setDeal (st : State) (hz : st.depthsZero) (d : Deal) :
    engineSuccContent (st.setDeal d) = engineSuccContent st := by
  funext c
  apply propext
  constructor
  · exact engineSuccContent_setDeal_sub st hz d c
  · intro hcity
    have heta : (st.setDeal d).setDeal st.deal = st := by
      rw [State.setDeal_setDeal]
      rfl
    rw [← heta] at hcity
    exact engineSuccContent_setDeal_sub (st.setDeal d)
      (State.depthsZero_setDeal hz d) st.deal c hcity

theorem engineSuccContent_orbit {a b : State} (h : PileContentOrbit a b) :
    engineSuccContent a = engineSuccContent b := by
  induction h with
  | refl x => rfl
  | @single x y hstep =>
      rcases hstep with ⟨i, j, hb⟩ | ⟨hz, d, hb⟩
      · rw [hb]
        exact (engineSuccContent_swapPiles x i j).symm
      · rw [hb]
        exact (engineSuccContent_setDeal x hz d).symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- **The content quotient's dynamics**: the engine successor-class
predicate is well-defined on content classes. -/
def EngineSuccCW (c : PileContentClass) : PileContentClass → Prop :=
  Quot.lift engineSuccContent
    (fun (a b : State) (h : PileContentOrbit a b) => engineSuccContent_orbit h) c

theorem engineSuccCW_mk_iff (st : State) (c : PileContentClass) :
    EngineSuccCW (PileContentClass.mk st) c ↔
      ∃ m, m.isEngine = true ∧
        ∃ st', st.apply m = some st' ∧ PileContentClass.mk st' = c :=
  Iff.rfl

/-- The inert-deal overwrite is engine-solvable iff the original is,
at all-emptied states (the play rides unchanged). -/
theorem solvableEngine_setDeal_iff_of_depthsZero {st : State} (hz : st.depthsZero)
    (d : Deal) : st.solvableEngine ↔ (st.setDeal d).solvableEngine := by
  constructor
  · intro heng
    obtain ⟨play, hall, w, hrun, hwin⟩ := heng
    refine ⟨play, hall, w.setDeal d, ?_, ?_⟩
    · have hrw := State.run_setDeal_eq_of_depthsZero st play d hz
      rw [hrw, hrun]
      rfl
    · show w.isWin = true
      exact hwin
  · intro hengD
    have hzD : (st.setDeal d).depthsZero := State.depthsZero_setDeal hz d
    obtain ⟨play, hall, wD, hrunD, hwinD⟩ := hengD
    have hsr := State.run_setDeal_eq_of_depthsZero (st.setDeal d) play st.deal hzD
    have heta : (st.setDeal d).setDeal st.deal = st := by
      rw [State.setDeal_setDeal]
      rfl
    rw [heta, hrunD] at hsr
    refine ⟨play, hall, wD.setDeal st.deal, ?_, ?_⟩
    · exact hsr
    · show wD.isWin = true
      exact hwinD

/-- The content-verdict transport, per step. -/
theorem solvableFrom_contentStep_iff {a b : State} (h : PileContentStep a b) :
    a.solvableFrom ↔ b.solvableFrom := by
  rcases h with ⟨i, j, hb⟩ | ⟨hz, d, hb⟩
  · rw [hb]
    exact solvable_swapPiles_iff i j a
  · rw [hb]
    exact State.solvableFrom_setDeal_iff_of_depthsZero hz d

theorem solvableFrom_contentOrbit_iff {a b : State} (h : PileContentOrbit a b) :
    a.solvableFrom ↔ b.solvableFrom := by
  induction h with
  | refl x => exact Iff.rfl
  | @single x' y' hstep => exact solvableFrom_contentStep_iff hstep
  | trans _ _ ih₁ ih₂ => exact Iff.trans ih₁ ih₂

/-- The lift of the solvability verdict to the content class. -/
def solvableCW (c : PileContentClass) : Prop :=
  Quot.lift (fun (st : State) => st.solvableFrom)
    (fun (a b : State) (h : PileContentOrbit a b) =>
      propext (solvableFrom_contentOrbit_iff h)) c

theorem solvableCW_mk_iff (st : State) :
    solvableCW (PileContentClass.mk st) ↔ st.solvableFrom := Iff.rfl

/-- The engine-restricted content verdict, per step. -/
theorem solvableEngine_contentStep_iff {a b : State} (h : PileContentStep a b) :
    a.solvableEngine ↔ b.solvableEngine := by
  rcases h with ⟨i, j, hb⟩ | ⟨hz, d, hb⟩
  · rw [hb]
    exact solvableEngine_swapPiles_iff i j a
  · rw [hb]
    exact solvableEngine_setDeal_iff_of_depthsZero hz d

theorem solvableEngine_contentOrbit_iff {a b : State} (h : PileContentOrbit a b) :
    a.solvableEngine ↔ b.solvableEngine := by
  induction h with
  | refl x => exact Iff.rfl
  | @single x' y' hstep => exact solvableEngine_contentStep_iff hstep
  | trans _ _ ih₁ ih₂ => exact Iff.trans ih₁ ih₂

/-- The lift of the engine-restricted verdict to the content
class. -/
def solvableEngineCW (c : PileContentClass) : Prop :=
  Quot.lift (fun (st : State) => st.solvableEngine)
    (fun (a b : State) (h : PileContentOrbit a b) =>
      propext (solvableEngine_contentOrbit_iff h)) c

theorem solvableEngineCW_mk_iff (st : State) :
    solvableEngineCW (PileContentClass.mk st) ↔ st.solvableEngine := Iff.rfl

/-! ## §5. The pristine collapse, as ONE orbit -/

/-- `Board.empty.attach (Sum.inl a) c = some bd`: `bd` is the
one-edge board (the king-at-anchor cell, everything else empty). -/
theorem attach_empty_shape {bd : Board} {a : Anchor} {c : Card}
    (hatt : Board.empty.attach (Sum.inl a) c = some bd) (b : Base) :
    bd.topOf b = if b = Sum.inl a then some c else Board.empty.topOf b := by
  by_cases hb : b = Sum.inl a
  · rw [hb, Board.attach_topOf _ _ _ hatt, ite_eq_left rfl]
  · rw [Board.attach_topOf_ne _ _ _ hatt hb, ite_eq_right hb]

/-- The conjugated empty-board landing: attaching at `a₁` and
swapping the piles yields the attaching at `a₂` — the visible
content of the pristine corner's orbit. -/
theorem attach_empty_mapByPileSwap {bd₁ bd₂ : Board} {a₁ a₂ : Anchor} {c : Card}
    (h1 : Board.empty.attach (Sum.inl a₁) c = some bd₁)
    (h2 : Board.empty.attach (Sum.inl a₂) c = some bd₂) :
    bd₁.mapByPileSwap a₁ a₂ = bd₂ := by
  refine Board.ext_topOf (funext (fun b => ?_))
  rw [mapByPileSwap_topOf, attach_empty_shape h1, attach_empty_shape h2]
  cases b with
  | inl x =>
      cases a₁ <;> cases a₂ <;> cases x <;>
        simp [Board.empty_topOf, Base.swapBase_inl, Anchor.swap]
  | inr cd =>
      cases a₁ <;> cases a₂ <;>
        simp [Board.empty_topOf, Base.swapBase_inr]

/-- **THE PRISTINE COLLAPSE, SETOID FORM.**  At a state whose piles
are all fully emptied — every depth zero (the deal inert) and an
empty matching — the Draw-commitment landings on ANY two anchors
are the SAME content class: the washed transposition of the one
landing IS the other.  All vacant anchors carry identical (empty)
content: every usable anchor candidate belongs to ONE swap-orbit.
This is the engine of the first-cut graded bound
(`witnesses/PileQuotientCorollaries.lean` §2: futures ≤ 2 + 1). -/
theorem emptyPiles_land_content_eq {st : State} (hz : st.depthsZero)
    (hb : st.board = Board.empty) {X : Card} (a₁ a₂ : Anchor)
    {L₁ L₂ : State}
    (h₁ : st.applyDrawTo X (Sum.inl a₁) = some L₁)
    (h₂ : st.applyDrawTo X (Sum.inl a₂) = some L₂) :
    PileContentClass.mk L₁ = PileContentClass.mk L₂ := by
  obtain ⟨i₁, bd₁, hp₁, hatt₁, hs₁⟩ := applyDrawTo_eq h₁
  obtain ⟨i₂, bd₂, hp₂, hatt₂, hs₂⟩ := applyDrawTo_eq h₂
  have hi : i₁ = i₂ := Option.some.inj (hp₁.symm.trans hp₂)
  rw [hi] at hs₁
  have hatt₁' : Board.empty.attach (Sum.inl a₁) X = some bd₁ := by
    rw [← hb]; exact hatt₁
  have hatt₂' : Board.empty.attach (Sum.inl a₂) X = some bd₂ := by
    rw [← hb]; exact hatt₂
  have hbd : bd₁.mapByPileSwap a₁ a₂ = bd₂ :=
    attach_empty_mapByPileSwap hatt₁' hatt₂'
  have hwash : (L₁.swapPiles a₁ a₂).setDeal st.deal = L₂ := by
    rw [hs₁, hs₂]
    refine state_ext rfl ?_ rfl ?_ rfl rfl
    · show bd₁.mapByPileSwap a₁ a₂ = bd₂
      exact hbd
    · funext x
      show st.depths (Anchor.swap a₁ a₂ x) = st.depths x
      rw [hz x]
      exact hz _
  have hzL₁ : L₁.depthsZero := by
    rw [hs₁]
    exact hz
  have horb : PileContentOrbit L₁ ((L₁.swapPiles a₁ a₂).setDeal st.deal) :=
    EqvClosure.trans
      (EqvClosure.single (Or.inl ⟨a₁, a₂, rfl⟩))
      (EqvClosure.single (Or.inr ⟨State.depthsZero_swapPiles hzL₁ a₁ a₂, st.deal, rfl⟩))
  rw [hwash] at horb
  exact Quot.sound horb

/-! ## §6. The chain representation and the same-deal fiber -/

/-- A concrete swap chain: apply the transpositions of `L`, in
order (the head first, as a state action). -/
def State.applySwaps (L : List (Anchor × Anchor)) (st : State) : State :=
  L.foldl (fun st p => st.swapPiles p.1 p.2) st

/-- The composed INDEX permutation of a chain — the order the
state-side application INDUCES on the read index: the chain's head
conjugates last, so this folds from the right.  (With the foldl
order the induced reading composition would be reversed; the
per-swap lemmas below close with `rfl` only in this form.) -/
def Anchor.applySwaps (L : List (Anchor × Anchor)) (a : Anchor) : Anchor :=
  L.foldr (fun p x => Anchor.swap p.1 p.2 x) a

/-- The composed BASE permutation of a chain (the same induced
order as `Anchor.applySwaps`; card seats untouched). -/
def Base.applySwaps (L : List (Anchor × Anchor)) (b : Base) : Base :=
  L.foldr (fun p b => b.swapBase p.1 p.2) b

theorem State.applySwaps_append (L₁ L₂ : List (Anchor × Anchor)) (st : State) :
    State.applySwaps (L₁ ++ L₂) st
      = State.applySwaps L₂ (State.applySwaps L₁ st) := by
  show (L₁ ++ L₂).foldl _ st = _
  exact List.foldl_append

theorem State.applySwaps_piles (L : List (Anchor × Anchor)) :
    ∀ (st : State) (a : Anchor),
    (State.applySwaps L st).deal.piles a
      = st.deal.piles (Anchor.applySwaps L a) := by
  induction L with
  | nil => intro _ _; rfl
  | cons p L ih =>
      intro st a
      have hS : State.applySwaps (p :: L) st
          = State.applySwaps L (st.swapPiles p.1 p.2) := rfl
      rw [hS, ih]
      exact State.swapPiles_deal_piles st p.1 p.2 _

theorem State.applySwaps_depths (L : List (Anchor × Anchor)) :
    ∀ (st : State) (a : Anchor),
    (State.applySwaps L st).depths a
      = st.depths (Anchor.applySwaps L a) := by
  induction L with
  | nil => intro _ _; rfl
  | cons p L ih =>
      intro st a
      have hS : State.applySwaps (p :: L) st
          = State.applySwaps L (st.swapPiles p.1 p.2) := rfl
      rw [hS, ih]
      exact State.swapPiles_depths st p.1 p.2 _

theorem State.applySwaps_deal_stock (L : List (Anchor × Anchor)) :
    ∀ (st : State), (State.applySwaps L st).deal.stock = st.deal.stock := by
  induction L with
  | nil => intro _; rfl
  | cons p L ih =>
      intro st
      have hS : State.applySwaps (p :: L) st
          = State.applySwaps L (st.swapPiles p.1 p.2) := rfl
      rw [hS, ih]
      rfl

theorem State.applySwaps_heights (L : List (Anchor × Anchor)) :
    ∀ (st : State), (State.applySwaps L st).heights = st.heights := by
  induction L with
  | nil => intro _; rfl
  | cons p L ih =>
      intro st
      have hS : State.applySwaps (p :: L) st
          = State.applySwaps L (st.swapPiles p.1 p.2) := rfl
      rw [hS, ih]
      rfl

theorem State.applySwaps_stock (L : List (Anchor × Anchor)) :
    ∀ (st : State), (State.applySwaps L st).stock = st.stock := by
  induction L with
  | nil => intro _; rfl
  | cons p L ih =>
      intro st
      have hS : State.applySwaps (p :: L) st
          = State.applySwaps L (st.swapPiles p.1 p.2) := rfl
      rw [hS, ih]
      rfl

theorem State.applySwaps_drawStep (L : List (Anchor × Anchor)) :
    ∀ (st : State), (State.applySwaps L st).drawStep = st.drawStep := by
  induction L with
  | nil => intro _; rfl
  | cons p L ih =>
      intro st
      have hS : State.applySwaps (p :: L) st
          = State.applySwaps L (st.swapPiles p.1 p.2) := rfl
      rw [hS, ih]
      rfl

theorem Base.applySwaps_map (L : List (Anchor × Anchor)) :
    ∀ (b : Base),
    Base.applySwaps L b = Sum.map (Anchor.applySwaps L) id b := by
  induction L with
  | nil => intro b; cases b <;> rfl
  | cons p L ih =>
      intro b
      have hB : (Base.applySwaps L b).swapBase p.1 p.2
          = Base.applySwaps (p :: L) b := rfl
      rw [← hB, ih]
      cases b with
      | inl v => rfl
      | inr cd => rfl

theorem State.applySwaps_board_topOf (L : List (Anchor × Anchor)) :
    ∀ (st : State) (b : Base),
    (State.applySwaps L st).board.topOf b
      = st.board.topOf (Base.applySwaps L b) := by
  induction L with
  | nil => intro _ _; rfl
  | cons p L ih =>
      intro st b
      have hS : State.applySwaps (p :: L) st
          = State.applySwaps L (st.swapPiles p.1 p.2) := rfl
      rw [hS, ih]
      exact State.swapPiles_board_topOf st p.1 p.2 _

/-- **The orbit is a chain**: every pure-Π orbit membership is a
concrete list of transpositions. -/
theorem pileSwapOrbit_exists_applySwaps {a b : State} (h : PileSwapOrbit a b) :
    ∃ L, b = State.applySwaps L a := by
  induction h with
  | refl x => exact ⟨[], rfl⟩
  | @single x y hstep =>
      obtain ⟨i, j, hb⟩ := hstep
      refine ⟨[(i, j)], hb⟩
  | @trans x y z _ _ ih₁ ih₂ =>
      obtain ⟨L₁, hL₁⟩ := ih₁
      obtain ⟨L₂, hL₂⟩ := ih₂
      refine ⟨L₁ ++ L₂, ?_⟩
      rw [hL₂, hL₁]
      exact (State.applySwaps_append L₁ L₂ x).symm

/-- **THE SAME-DEAL FIBER**: at a WF-deal state, the pure-Π orbit
meets the same-deal fiber only at the state itself.  A swap chain
that permutes the deal slices back to themselves composes to the
identity: the seven slots have pairwise distinct lengths
(`Anchor.toIdx_inj`), so the composed index permutation fixes every
slot, and then every state component — board (via the composed base
permutation), depths, deal, stock, heights, draw step — returns
definitionally. -/
theorem applySwaps_eq_of_same_deal {st : State} (hd : st.deal.WF)
    (L : List (Anchor × Anchor))
    (hsame : (State.applySwaps L st).deal = st.deal) :
    State.applySwaps L st = st := by
  have hpiles : ∀ a, st.deal.piles (Anchor.applySwaps L a) = st.deal.piles a := by
    intro a
    have h := congrArg (fun (d : Deal) => d.piles a) hsame
    rw [State.applySwaps_piles L st a] at h
    exact h
  have hA : ∀ a, Anchor.applySwaps L a = a := by
    intro a
    have h1 := hd.1 (Anchor.applySwaps L a)
    have h2 := hd.1 a
    have h3 := congrArg (fun (l : List Card) => l.length) (hpiles a)
    rw [h1] at h3
    rw [h2] at h3
    exact Anchor.toIdx_inj (by omega)
  have hAid : Anchor.applySwaps L = fun a => a := funext hA
  have hb : ∀ b, Base.applySwaps L b = b := by
    intro b
    rw [Base.applySwaps_map]
    rw [hAid]
    cases b <;> rfl
  refine state_ext ?_ ?_ ?_ ?_ ?_ ?_
  · apply Deal.ext'
    · intro a
      rw [State.applySwaps_piles L st a, hA a]
    · rw [State.applySwaps_deal_stock L st]
  · refine Board.ext_topOf (funext (fun b => ?_))
    rw [State.applySwaps_board_topOf L st b, hb b]
  · rw [State.applySwaps_heights L st]
  · funext a
    rw [State.applySwaps_depths L st a, hA a]
  · rw [State.applySwaps_stock L st]
  · rw [State.applySwaps_drawStep L st]

/-- **The orbit-level same-deal collapse.** -/
theorem pileSwapOrbit_sameDeal_eq {s₁ s₂ : State} (hd : s₁.deal.WF)
    (h : PileSwapOrbit s₁ s₂) (hdeal : s₂.deal = s₁.deal) : s₁ = s₂ := by
  obtain ⟨L, hL⟩ := pileSwapOrbit_exists_applySwaps h
  have hsame : (State.applySwaps L s₁).deal = s₁.deal := by
    rw [← hL]
    exact hdeal
  have hback := applySwaps_eq_of_same_deal hd L hsame
  rw [← hL] at hback
  exact hback.symm

/-- **The content-level same-deal collapse (the survival engine)**:
off the all-emptied fragment, two states sharing a WF deal that are
content-related are EQUAL.  The wave-20 reachable corner
(`witnesses/PileSwapConsequences.lean` §2; `SuccLabeledWitness.rState`
underneath) instantiates the premises — distinct landed heads over
the same WF deal, all-emptied FALSE — so its countermodel pairs
survive in the FULL content quotient, not just under single
transpositions. -/
theorem pileContentOrbit_sameDeal_eq {s₁ s₂ : State} (hd : s₁.deal.WF)
    (hnz : ¬ s₁.depthsZero) (h : PileContentOrbit s₁ s₂)
    (hdeal : s₂.deal = s₁.deal) : s₁ = s₂ :=
  pileSwapOrbit_sameDeal_eq hd
    (pileSwapOrbit_of_contentOrbit_of_not_depthsZero h hnz) hdeal

/-! ## §7. The anchor landings' orbit carving (wave-22, king-graded kernel)

The `Draw(X)` commitment's ANCHOR landings — the states
`st.applyDrawTo X (Sum.inl a) = some L` — are the king-side graded
bound's carriers (kings land on anchors only,
`Klondike/C2Streamlined.lean`'s `king_tableau_base`).  This section
carves their orbit structure through both quotients, as far as state
content permits:

* **The same-deal fiber at landings** (`drawLand_pileSwapOrbit_iff`)
  — at a WF-deal state, two anchor landings are pure-Π-related
  EXACTLY on anchor equality: the §6 capstone read along
  `applyDrawTo` (the landing keeps the deal, so an orbit meeting
  two landings meets the same-deal fiber), plus the seat readback
  (the landing's own attach guard pins the card at its anchor-seat).
  The induced swap-orbit on usable vacant anchors is therefore the
  IDENTITY: each anchor its own orbit, the landing classes INDEXED
  by the anchors.  Card-general — the king enters the graded bound
  through the COVER (kings have no receiver landings), not the
  separation.
* **The content carve, both sides.**  Off the emptied fragment
  (`drawLand_contentOrbit_eq_of_not_depthsZero`,
  `drawLand_content_class_inj`) the content orbits coincide with the
  pure orbits (§4 purity, now at landings), so anchor names are
  content.  ON the emptied fragment the content classes of ANY two
  landings MERGE (`drawLand_content_eq_of_depthsZero`) — with no
  board-emptiness premise: the probe `probes/kingwash.lean` decided
  this first (at a depthsZero state with a card-edge seated on a
  card seat, the washed-swap composition equals the other landing
  field by field), and the proof keeps only what the probe used —
  the two anchor seats' emptiness (which the firings' own attach
  guards carry) and the all-zero depths (which the wash needs).
  This strictly generalizes §5's `emptyPiles_land_content_eq`: the
  empty board there was a proof-route artifact.

The induced content-orbit on usable vacant anchors is thus carved
exactly: SINGLETONS while deal content remains, ONE class when every
pile is fully emptied.  That is the full statement behind the first
cut's pristine instance
(`witnesses/PileQuotientCorollaries.lean` §2); the king-side graded
bound — the `1 + #swap-orbits` futures count — is assembled over
this kernel in `witnesses/PileQuotientOrbit.lean`. -/

/-- The landing's field shape, packaged (the per-field readings of
`applyDrawTo_eq`): a `Draw` landing rewrites board and stock only. -/
theorem drawLand_shape {st : State} {X : Card} {b : Base} {L : State}
    (h : st.applyDrawTo X b = some L) :
    ∃ i bd, st.reachablePos X = some i ∧ st.board.attach b X = some bd ∧
      L.deal = st.deal ∧ L.heights = st.heights ∧ L.depths = st.depths ∧
      L.board = bd ∧
      L.stock = ⟨Cycle.removeIdx st.stock.cards i, i⟩ := by
  obtain ⟨i, bd, hpos, hatt, hs⟩ := applyDrawTo_eq h
  subst hs
  exact ⟨i, bd, hpos, hatt, rfl, rfl, rfl, rfl, rfl⟩

/-- A Draw landing keeps the deal (the same-deal fiber's landing
side). -/
theorem drawLand_deal {st : State} {X : Card} {b : Base} {L : State}
    (h : st.applyDrawTo X b = some L) : L.deal = st.deal := by
  obtain ⟨-, -, -, -, hd, -, -, -, -⟩ := drawLand_shape h
  exact hd

/-- A Draw landing keeps the heights (the stack-vs-landing freshness
reads the difference). -/
theorem drawLand_heights {st : State} {X : Card} {b : Base} {L : State}
    (h : st.applyDrawTo X b = some L) : L.heights = st.heights := by
  obtain ⟨-, -, -, -, -, hh, -, -, -⟩ := drawLand_shape h
  exact hh

/-- The all-emptied flag is landing-invariant. -/
theorem drawLand_depthsZero_iff {st : State} {X : Card} {b : Base} {L : State}
    (h : st.applyDrawTo X b = some L) : st.depthsZero ↔ L.depthsZero := by
  obtain ⟨-, -, -, -, -, -, hdepths, -, -⟩ := drawLand_shape h
  constructor
  · intro hz a
    rw [hdepths]
    exact hz a
  · intro hz a
    rw [← hdepths]
    exact hz a

/-- A transposition whose two anchor seats agree is the identity on
the board — equal-content anchor seats are board-interchangeable. -/
theorem Board.mapByPileSwap_eq_of_anchorSeats {bd : Board} {i j : Anchor}
    (h : bd.topOf (Sum.inl i) = bd.topOf (Sum.inl j)) :
    bd.mapByPileSwap i j = bd := by
  refine Board.ext_topOf (funext (fun b => ?_))
  show bd.topOf (b.swapBase i j) = bd.topOf b
  cases b with
  | inr c => rfl
  | inl a =>
      by_cases hai : a = i
      · rw [hai, Base.swapBase_inl, Anchor.swap_self_left, h]
      · by_cases haj : a = j
        · rw [haj, Base.swapBase_inl, Anchor.swap_self_right, h.symm]
        · rw [Base.swapBase_inl, Anchor.swap_eq_self i j hai haj]

/-- The conjugated landing board: when the two anchor seats agree,
the transposition of the `a₁`-landing's board is exactly the
`a₂`-landing's board (`mapByPileSwap_attach` read at the agreeing
seats). -/
theorem attach_conj_of_anchorSeats {bd : Board} {a₁ a₂ : Anchor} {X : Card}
    {bd₁ bd₂ : Board}
    (h : bd.topOf (Sum.inl a₁) = bd.topOf (Sum.inl a₂))
    (h₁ : bd.attach (Sum.inl a₁) X = some bd₁)
    (h₂ : bd.attach (Sum.inl a₂) X = some bd₂) :
    bd₁.mapByPileSwap a₁ a₂ = bd₂ := by
  have hinv : bd.mapByPileSwap a₁ a₂ = bd :=
    Board.mapByPileSwap_eq_of_anchorSeats h
  have hc := mapByPileSwap_attach bd a₁ a₂ h₁
  rw [hinv] at hc
  have hbase : Base.swapBase (Sum.inl a₁) a₁ a₂ = Sum.inl a₂ := by
    rw [Base.swapBase_inl, Anchor.swap_self_left]
  rw [hbase] at hc
  exact (Option.some.inj (h₂.symm.trans hc)).symm

/-- **THE EMPTIED-FRAGMENT MERGE (no board premise).**  At an
all-emptied state, the `Draw` landings of one card on any two firing
anchor seats belong to ONE content class: the single washed
transposition of one landing IS the other.  The seats' emptiness is
carried by the firings' own attach guards, so NO board-emptiness
premise survives — the probe `probes/kingwash.lean` decided this
shape first.  Strictly generalizes §5's
`emptyPiles_land_content_eq` (its `st.board = Board.empty` was a
proof-route artifact). -/
theorem drawLand_content_eq_of_depthsZero {st : State} {X : Card}
    {a₁ a₂ : Anchor} {L₁ L₂ : State}
    (hz : st.depthsZero)
    (h₁ : st.applyDrawTo X (Sum.inl a₁) = some L₁)
    (h₂ : st.applyDrawTo X (Sum.inl a₂) = some L₂) :
    PileContentClass.mk L₁ = PileContentClass.mk L₂ := by
  obtain ⟨i₁, bd₁, hp₁, hatt₁, hs₁⟩ := applyDrawTo_eq h₁
  obtain ⟨i₂, bd₂, hp₂, hatt₂, hs₂⟩ := applyDrawTo_eq h₂
  have hii : i₁ = i₂ := Option.some.inj (hp₁.symm.trans hp₂)
  rw [hii] at hs₁
  have hfree₁ : st.board.topOf (Sum.inl a₁) = none :=
    ((Board.attach_eq_some_iff st.board (Sum.inl a₁) X).mp
      (by rw [hatt₁]; simp)).1
  have hfree₂ : st.board.topOf (Sum.inl a₂) = none :=
    ((Board.attach_eq_some_iff st.board (Sum.inl a₂) X).mp
      (by rw [hatt₂]; simp)).1
  have hbcbd : bd₁.mapByPileSwap a₁ a₂ = bd₂ :=
    attach_conj_of_anchorSeats (hfree₁.trans hfree₂.symm) hatt₁ hatt₂
  have hzL₁ : L₁.depthsZero := (drawLand_depthsZero_iff h₁).mp hz
  have hwash : (L₁.swapPiles a₁ a₂).setDeal st.deal = L₂ := by
    rw [hs₁, hs₂]
    refine state_ext rfl ?_ rfl ?_ rfl rfl
    · show bd₁.mapByPileSwap a₁ a₂ = bd₂
      exact hbcbd
    · funext x
      show st.depths (Anchor.swap a₁ a₂ x) = st.depths x
      rw [hz x]
      exact hz _
  have hor : PileContentOrbit L₁ ((L₁.swapPiles a₁ a₂).setDeal st.deal) :=
    EqvClosure.trans
      (EqvClosure.single (Or.inl ⟨a₁, a₂, rfl⟩))
      (EqvClosure.single (Or.inr ⟨State.depthsZero_swapPiles hzL₁ a₁ a₂, st.deal, rfl⟩))
  rw [hwash] at hor
  exact Quot.sound hor

/-- **The same-deal fiber at anchor landings**: at a WF-deal state, a
pure-Π relation between two anchor landings forces anchor equality —
the class remembers the landing seat. -/
theorem drawLand_pileSwapOrbit_eq {st : State} (hd : st.deal.WF) {X : Card}
    {a₁ a₂ : Anchor} {L₁ L₂ : State}
    (h₁ : st.applyDrawTo X (Sum.inl a₁) = some L₁)
    (h₂ : st.applyDrawTo X (Sum.inl a₂) = some L₂)
    (h : PileSwapOrbit L₁ L₂) : a₁ = a₂ := by
  by_cases hne : a₁ = a₂
  · exact hne
  · exfalso
    have hwf : L₁.deal.WF := by
      rw [drawLand_deal h₁]
      exact hd
    have hdeal : L₂.deal = L₁.deal :=
      (drawLand_deal h₂).trans (drawLand_deal h₁).symm
    have hstate : L₁ = L₂ := pileSwapOrbit_sameDeal_eq hwf h hdeal
    obtain ⟨-, bd₁, -, hatt₁, -, -, -, hbb₁, -⟩ := drawLand_shape h₁
    obtain ⟨-, bd₂, -, hatt₂, -, -, -, hbb₂, -⟩ := drawLand_shape h₂
    have hfree₂ : st.board.topOf (Sum.inl a₂) = none :=
      ((Board.attach_eq_some_iff st.board (Sum.inl a₂) X).mp
        (by rw [hatt₂]; simp)).1
    have hseat₂ : L₂.board.topOf (Sum.inl a₂) = some X := by
      rw [hbb₂]
      exact Board.attach_topOf st.board (Sum.inl a₂) X hatt₂
    have hnone₁ : L₁.board.topOf (Sum.inl a₂) = none := by
      have hneB : (Sum.inl a₂ : Base) ≠ Sum.inl a₁ :=
        fun hcon => hne (Sum.inl.inj hcon).symm
      rw [hbb₁, Board.attach_topOf_ne st.board (Sum.inl a₁) X hatt₁ hneB]
      exact hfree₂
    rw [hstate] at hnone₁
    rw [hseat₂] at hnone₁
    exact absurd hnone₁ (by simp)

/-- **The induced swap-orbit on anchor landings is trivial at WF-deal
states**: two landings are pure-Π-related exactly when they land on
the same anchor — each usable vacant anchor is its own orbit, and
the landing classes are INDEXED by the usable anchors. -/
theorem drawLand_pileSwapOrbit_iff {st : State} (hd : st.deal.WF) {X : Card}
    {a₁ a₂ : Anchor} {L₁ L₂ : State}
    (h₁ : st.applyDrawTo X (Sum.inl a₁) = some L₁)
    (h₂ : st.applyDrawTo X (Sum.inl a₂) = some L₂) :
    (PileSwapOrbit L₁ L₂) ↔ (a₁ = a₂) := by
  constructor
  · exact drawLand_pileSwapOrbit_eq hd h₁ h₂
  · intro hc
    subst hc
    have hLL : L₁ = L₂ := Option.some.inj (h₁.symm.trans h₂)
    rw [hLL]
    exact EqvClosure.refl L₂

/-- Distinct usable anchors carry distinct landing classes (the
class-injectivity of the anchor landing map). -/
theorem drawLand_pile_class_inj {st : State} (hd : st.deal.WF) {X : Card}
    {a₁ a₂ : Anchor} {L₁ L₂ : State}
    (h₁ : st.applyDrawTo X (Sum.inl a₁) = some L₁)
    (h₂ : st.applyDrawTo X (Sum.inl a₂) = some L₂)
    (hne : a₁ ≠ a₂) : PileClass.mk L₁ ≠ PileClass.mk L₂ := by
  intro hcon
  exact hne (drawLand_pileSwapOrbit_eq hd h₁ h₂ (PileClass.exact hcon))

/-- Off the emptied fragment the content orbit is the pure orbit, at
landings — the §4 purity exported through the firing shape. -/
theorem drawLand_contentOrbit_eq_of_not_depthsZero {st : State} (hd : st.deal.WF)
    (hnz : ¬ st.depthsZero) {X : Card} {a₁ a₂ : Anchor} {L₁ L₂ : State}
    (h₁ : st.applyDrawTo X (Sum.inl a₁) = some L₁)
    (h₂ : st.applyDrawTo X (Sum.inl a₂) = some L₂)
    (h : PileContentOrbit L₁ L₂) : a₁ = a₂ := by
  have hnzL : ¬ L₁.depthsZero :=
    fun hz => hnz ((drawLand_depthsZero_iff h₁).mpr hz)
  exact drawLand_pileSwapOrbit_eq hd h₁ h₂
    (pileSwapOrbit_of_contentOrbit_of_not_depthsZero h hnzL)

/-- **The content-class injectivity off the emptied fragment**: at a
WF-deal, not-all-emptied state, the anchor landings of distinct
usable anchors stay in distinct CONTENT classes — anchor names are
content, and the wave-20 countermodels are content-real down to the
class level. -/
theorem drawLand_content_class_inj {st : State} (hd : st.deal.WF)
    (hnz : ¬ st.depthsZero) {X : Card} {a₁ a₂ : Anchor} {L₁ L₂ : State}
    (h₁ : st.applyDrawTo X (Sum.inl a₁) = some L₁)
    (h₂ : st.applyDrawTo X (Sum.inl a₂) = some L₂)
    (hne : a₁ ≠ a₂) : PileContentClass.mk L₁ ≠ PileContentClass.mk L₂ := by
  intro hcon
  exact hne (drawLand_contentOrbit_eq_of_not_depthsZero hd hnz h₁ h₂
    (PileContentClass.exact hcon))
