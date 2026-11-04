import Orig2.Fork.Split.ForkSplit

set_option autoImplicit false
set_option linter.unusedVariables false

/-!
# Orig2/ForkMin - `ShortestPlayExists` is a pure `Nat` well-ordering fact

SCRATCH card (`Temp/`), read-only on the repository, nothing committed.
No `sorry`, no `native_decide`, no `Classical.choice`.

## What is proved here (all choice-free)

`ValleyElim.ShortestPlayExists` (`Orig2/Fork/Split/ForkSplit.lean:874`) is an
existential over a witness play PLUS a global length-minimality clause.

1. `sameOrbit_reachable` - the *existence* half is free.  The orbit
   relation is not a normal-form quotient: it is the reversible witness
   relation, `sameOrbitSetoid.r a b = RevEqW b a`
   (`Orig2/Substrate/Vocab.lean:323-326`), and `RevEqW s s'` is a *single*
   existential with a conjunctive body (`Orig2/Substrate/Vocab.lean:296-297`):

       `RevEqW s s' := ∃ ρ, ShufflePlayW s ρ s' ∧ ∃ ρ', ShufflePlayW s' ρ' s`.

   At `s = v`, `s' = u` its second component is literally
   `∃ ρ, ShufflePlayW u ρ v`.  So "same orbit ⇒ some play" is a
   projection, not a chess theorem.

2. `playLenMin_of_natHasMin` / `shortestPlayExists_of_playLenMin` /
   `shortestPlayExists_of_natHasMin` - the *whole remaining content* is
   the least element of `{n | ∃ ρ, ShufflePlayW u ρ v ∧ ρ.length = n}`.
   The gates `u.WF`, `SSaturated u`, `SSaturated v` and the rung
   difference `∃ σ, rungAt u σ ≠ rungAt v σ` are **never used**: the
   ungated statement holds from the same residual
   (`shortestPlayExists_ungated`).

3. `em_of_natHasMin`, `natHasMin_of_em`, `natHasMin_iff_em` - the
   minimum principle is **exactly excluded middle**.  So the campaign's
   last interface hypothesis is not a chess fact AND not a free
   well-ordering fact: it is EM in a play costume.

4. `natHasMin_of_uniformPlayLenMin` - sharpening of 3: the shortest-play
   principle *taken uniformly in the play relation* already implies
   `NatHasMin`, hence EM.  The only non-EM content of
   `ShortestPlayExists` is the reachability supplied by `RevEqW`.

`Temp/Min_Choice.lean` prices the classical route: `NatHasMin` from
`Classical.em`, then `ShortestPlayExists`, with `#print axioms =
[propext, Classical.choice, Quot.sound]`.
-/

namespace MinKit

/-! ## 1. Existence is a projection of the orbit relation -/

/-! ## 2. The residual: the pure well-ordering fact, and the reduction -/

/-- **THE PURE `Nat` MINIMUM PRINCIPLE.**  Every inhabited set of naturals
has a least element.  This is the campaign's entire remaining non-chess
content (see `natHasMin_iff_em`: it is excluded middle). -/
def NatHasMin : Prop :=
  ∀ P : Nat → Prop, (∃ n, P n) → ∃ n, P n ∧ ∀ m, m < n → ¬ P m

/-- **THE STRICTLY WEAKER NAMED RESIDUAL.**  The minimum principle
*only* for the actual play-length predicate: no `WF`, no `SSaturated`, no
rung difference.  Strictly weaker than `ShortestPlayExists`: it drops
every gate and takes reachability as a hypothesis. -/
def PlayLenMin : Prop :=
  ∀ u v : State, (∃ ρ : List Move, ShufflePlayW u ρ v) →
    ∃ m : Nat,
      (∃ ρ : List Move, ShufflePlayW u ρ v ∧ ρ.length = m) ∧
        ∀ k : Nat, k < m → ¬ ∃ ρ : List Move, ShufflePlayW u ρ v ∧ ρ.length = k

/-- The residual is an instance of the pure principle. -/
theorem playLenMin_of_natHasMin (h : NatHasMin) : PlayLenMin := by
  intro u v hex
  obtain ⟨ρ, hρ⟩ := hex
  exact h (fun n => ∃ ρ : List Move, ShufflePlayW u ρ v ∧ ρ.length = n)
    ⟨ρ.length, ρ, hρ, rfl⟩

/-- **THE REDUCTION.**  The residual gives the interface hypothesis.
Note the proof never touches `huwf`, `hsu`, `hsv` or `hdiff`. -/
theorem shortestPlayExists_of_playLenMin (h : PlayLenMin) :
    ValleyElim.ShortestPlayExists := by
  intro u v _huwf _hsu _hsv hcls _hdiff
  obtain ⟨m, ⟨ρ, hρ, hlen⟩, hmin⟩ := h u v (sameOrbit_reachable hcls)
  refine ⟨ρ, hρ, fun ρ' hρ' => ?_⟩
  have hnot : ¬ ρ'.length < m :=
    fun hlt => hmin ρ'.length hlt ⟨ρ', hρ', rfl⟩
  rw [hlen]
  exact Nat.le_of_not_lt hnot

/-- The same conclusion without the gates and without the rung difference:
the interface hypothesis is the *gated* shadow of a statement that needs no
hypothesis at all beyond reachability. -/
theorem shortestPlayExists_ungated (h : PlayLenMin) (u v : State)
    (hcls : sameOrbitSetoid.r u v) :
    ∃ ρ : List Move, ShufflePlayW u ρ v ∧
      ∀ ρ' : List Move, ShufflePlayW u ρ' v → ρ.length ≤ ρ'.length := by
  obtain ⟨m, ⟨ρ, hρ, hlen⟩, hmin⟩ := h u v (sameOrbit_reachable hcls)
  refine ⟨ρ, hρ, fun ρ' hρ' => ?_⟩
  have hnot : ¬ ρ'.length < m :=
    fun hlt => hmin ρ'.length hlt ⟨ρ', hρ', rfl⟩
  rw [hlen]
  exact Nat.le_of_not_lt hnot

/-- Composed form: pure `Nat` well-ordering implies `ShortestPlayExists`. -/
theorem shortestPlayExists_of_natHasMin (h : NatHasMin) :
    ValleyElim.ShortestPlayExists :=
  shortestPlayExists_of_playLenMin (playLenMin_of_natHasMin h)

/-! ## 3. The residual is exactly excluded middle -/

/-- **EXCLUDED MIDDLE.**  Stated as a definition because this file proves the
equivalence with `NatHasMin` and nothing else. -/
def ExcludedMiddle : Prop :=
  ∀ p : Prop, p ∨ ¬ p

/-- **WELL-ORDERING OF `Nat` IMPLIES EM.**  The classic two-point set
`{0 if p} ∪ {1}`: its minimum is `0` exactly when `p`. -/
theorem em_of_natHasMin (h : NatHasMin) : ExcludedMiddle := by
  intro p
  let P : Nat → Prop := fun n => (n = 0 ∧ p) ∨ n = 1
  have hne : ∃ n, P n := ⟨1, Or.inr rfl⟩
  obtain ⟨m, hm, hmin⟩ := h P hne
  rcases hm with ⟨_, hp⟩ | hm1
  · exact Or.inl hp
  · refine Or.inr (fun hp => ?_)
    have hlt : 0 < m := by
      rw [hm1]
      exact Nat.zero_lt_one
    exact hmin 0 hlt (Or.inl ⟨rfl, hp⟩)

/-- **EM GIVES WELL-ORDERING OF `Nat`** (choice-free, given EM as a
hypothesis): strong recursion at a witness bound. -/
theorem natHasMin_of_em (h : ExcludedMiddle) : NatHasMin := by
  intro P hne
  obtain ⟨N, hN⟩ := hne
  have key : ∀ N : Nat, P N → ∃ n, P n ∧ ∀ m, m < n → ¬ P m := by
    intro N
    induction N using Nat.strongRecOn with
    | ind N ih =>
      intro hPN
      rcases h (∃ k, k < N ∧ P k) with ⟨k, hklt, hkP⟩ | hnone
      · exact ih k hklt hkP
      · exact ⟨N, hPN, fun m hm hmP => hnone ⟨m, hm, hmP⟩⟩
  exact key N hN

/-- **THE MEASUREMENT.**  `NatHasMin` and excluded middle are the same
proposition.  Hence no choice-free proof of the minimum clause exists: a
choice-free `NatHasMin` would be a choice-free EM (`Classical.em` is not
derivable from `propext`/`Quot.sound` alone - the setoid model refutes it). -/
theorem natHasMin_iff_em : NatHasMin ↔ ExcludedMiddle :=
  ⟨em_of_natHasMin, natHasMin_of_em⟩

/-- **SHARPNESS.**  The shortest-play principle *uniformly in the play
relation* already yields `NatHasMin`: instantiate at
`R ρ := P ρ.length` and use that every natural is the length of some list
(`List.replicate n Move.draw`).  So the campaign interface contains no chess
content beyond the reachability of `RevEqW`. -/
theorem natHasMin_of_uniformPlayLenMin
    (h : ∀ (R : List Move → Prop), (∃ ρ : List Move, R ρ) →
      ∃ ρ : List Move, R ρ ∧ ∀ ρ' : List Move, R ρ' → ρ.length ≤ ρ'.length) :
    NatHasMin := by
  intro P hne
  obtain ⟨n, hn⟩ := hne
  let R : List Move → Prop := fun ρ => P ρ.length
  have hR : ∃ ρ : List Move, R ρ :=
    ⟨List.replicate n Move.draw, by
      show P (List.replicate n Move.draw).length
      rw [List.length_replicate]
      exact hn⟩
  obtain ⟨ρ, hρ, hmin⟩ := h R hR
  refine ⟨ρ.length, hρ, fun k hk hkP => ?_⟩
  have hle : ρ.length ≤ k := by
    have hh := hmin (List.replicate k Move.draw) (by
      show P (List.replicate k Move.draw).length
      rw [List.length_replicate]
      exact hkP)
    rwa [List.length_replicate] at hh
  exact Nat.lt_irrefl ρ.length (Nat.lt_of_le_of_lt hle hk)
end MinKit

/-! ## Axiom battery

`propext` shows up on every row whose *statement* mentions the carrier:
`State.step` itself depends on `[propext]` (its `if`/`decEq` layer), and
`Walk` - hence `ShufflePlayW`, `RevEqW`, `SSaturated`, `sameOrbitSetoid` -
carries it (`#print axioms Walk`, `#print axioms State.step`).  It enters
through the vocabulary, not through the proofs: `fun h => h` at type
`RevEqW v u → RevEqW v u` already prints `[propext]`, while the pure-logic
rows (`em_of_natHasMin`, `natHasMin_of_em`, `natHasMin_iff_em`) are exactly
`[]`.  No row uses `Classical.choice` or `Quot.sound`. -/

#print axioms MinKit.playLenMin_of_natHasMin
#print axioms MinKit.shortestPlayExists_of_playLenMin
#print axioms MinKit.shortestPlayExists_ungated
#print axioms MinKit.shortestPlayExists_of_natHasMin
#print axioms MinKit.em_of_natHasMin
#print axioms MinKit.natHasMin_of_em
#print axioms MinKit.natHasMin_iff_em
#print axioms MinKit.natHasMin_of_uniformPlayLenMin
#print axioms ValleyElim.ShortestPlayExists
