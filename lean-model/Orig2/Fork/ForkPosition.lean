import Orig2.Fiber.LockRung

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

/-!
# Orig2.ForkPosition — fork states and the Position grid

THE SAME-POSITION QUESTION.  At `WF`, two class-mates present the same
`Position` exactly when they have the same rung vector, equivalently the
same `found` tuple (`rungEq_iff_found_eq`, `position_eq_iff`).  The
question is whether all `forkState` states of one class are Position-rigid.

* NO counterexample: ~317 probed witness classes (~10^5 states), incl.
  vcS (60 states/16 forks at `(3,0,3,3)`), Plan-4 (397/8 at `(3,0,2,2)`),
  and 249 planted-fork classes up to 10 768 states — every class carries
  all its forks at one rung vector (`Temp/ForkPos_probe.py`).
* The S grade really is stronger than the retired weak grade: the frozen
  craft is NOT a fork at either end (its S-live set is not a twin pair).
* `fork_under_cards` is the structural reason: at a non-king S-fork,
  BOTH twins sit directly on a card of the opposite colour family one
  rank above.  Hence both opposite-family `r+1` cards are consumed under
  the twins, starving the weak-grade ascent of a landing base.

The exact missing row is `ForkThirdRigid` (the two non-pair suits), the
same `hthird` hypothesis carried at `Orig/PairClassZones.lean:128`.
`forkPositionRigid_of_third` reduces `ForkPositionRigid` to it; the pair
half is `fork_label_class` + `forkState_witness_rungs`.

Caveat: `fork_under_cards` excludes the king rank (`r = 12`); the probes
show rigidity there too, but a proof must handle that shape separately.

House compliance: additive leaf (`Orig2.LockRung` for the unconditional
class theorem); zero `sorry`, zero `Classical.choice`; battery at tail.
-/

/-! ## §0. The target -/

/-- **ForkPositionRigid** — the question, stated: two `ForkWitness`
states of one macro class have the same rung vector (hence, at `WF`,
the same `found` tuple — §4).  No pair-side hypothesis: the pair
identity is itself a theorem (`Orig2/Fork/ForkClass.lean:225
fork_label_class_of_token_and_oneFounding`). -/
def ForkPositionRigid : Prop :=
  ∀ (F G : State) (x y : Card), F.WF → G.WF → sameOrbitSetoid.r F G →
    ForkWitness F x → ForkWitness G y → RungEq F G

/-- The `found`-tuple spelling (the question's second form). -/
def ForkFoundRigid : Prop :=
  ∀ (F G : State) (x y : Card), F.WF → G.WF → sameOrbitSetoid.r F G →
    ForkWitness F x → ForkWitness G y → ∀ s : Suit, F.found s = G.found s

/-! ## §1. The pair half (proved) -/

/-- **THE PAIR-SUIT RUNG PIN** — at a witness of the pair named by `x`,
both pair suits read `x.rank.toIdx`.  Orig2 re-derivation of the frozen
`Orig/PairClassZones.lean:98 pcz_pair_rung` from
`forkState_witness_rungs` (`Orig2/Substrate/PairClassSeed.lean:320`) and the twin
card algebra (`Orig2/Fork/Cover.lean:36`/`:39`). -/
theorem pair_rung_pin {u : State} {x y : Card} (hy : ForkWitness u y)
    (hxy : y = x ∨ y = x.twin) (σ : Suit)
    (hσ : σ = x.suit ∨ σ = x.twin.suit) :
    rungAt u σ = x.rank.toIdx := by
  obtain ⟨h1, h2⟩ := forkState_witness_rungs hy
  rcases hxy with h | h
  · rw [h] at h1 h2
    rcases hσ with hσ | hσ
    · rw [hσ]; exact h1
    · rw [hσ]; exact h2
  · rw [h] at h1 h2
    rcases hσ with hσ | hσ
    · rw [hσ]
      rw [tfc_card_twin_twin, Card.twin_rank] at h2
      exact h2
    · rw [hσ]
      rw [Card.twin_rank] at h1
      exact h1

/-- **THE PAIR HALF** — given the class pair identity (`y = x` or
`y = x.twin`), the two fork states agree on both pair-suit rungs. -/
theorem pair_half {F G : State} {x y : Card}
    (hx : ForkWitness F x) (hy : ForkWitness G y)
    (hpair : y = x ∨ y = x.twin) (σ : Suit)
    (hσ : σ = x.suit ∨ σ = x.twin.suit) :
    rungAt F σ = rungAt G σ :=
  (pair_rung_pin hx (Or.inl rfl) σ hσ).trans
    (pair_rung_pin hy hpair σ hσ).symm

/-- The pair identity, in the exact form §1 consumes — the frozen
`fork_label_class` (`Orig/ForkCensus.lean:520`), which Orig2 reduces to
the two residues `CoverToken` + `OneFounding`
(`Orig2/Fork/ForkClass.lean:225`). -/
def ForkPairClass : Prop :=
  ∀ (F G : State) (x y : Card), F.WF → G.WF → sameOrbitSetoid.r F G →
    ForkWitness F x → ForkWitness G y → (y = x ∨ y = x.twin)
/-- `ForkPairClass` is the unconditional `fork_label_class`. -/
theorem forkPairClass : ForkPairClass :=
  fun F G x y hF hG hcls hx hy => fork_label_class hF hG hcls hx hy

/-! ## §2. The structural lemma (proved): the twins sit ON the opposite
family's `r+1` cards -/

/-- Split the last card off a nonempty list. -/
private theorem exists_split_last : ∀ (l : List Card), l ≠ [] →
    ∃ (P : List Card) (u : Card), l = P ++ [u]
  | [], h => absurd rfl h
  | [a], _ => ⟨[], a, rfl⟩
  | a :: b :: t, _ => by
      obtain ⟨P, u, hP⟩ := exists_split_last (b :: t) (by simp)
      exact ⟨a :: P, u, by simp [hP]⟩

/-- **THE LIVE CARD'S UNDER-CARD** — an S-live card that is not a king
sits directly on a card one rank above it, of the OPPOSITE colour
family.  (`canRaiseS_flat_necessity`, `Orig2/Substrate/CargoRaise.lean:329`,
gives `faceUp = bs ++ c :: run` with `bs ≠ []`; `runOK` then prices the
adjacency through `SeedKit.runOK_adjacent_fit`,
`Orig2/Substrate/PairClassSeed.lean:99`.) -/
theorem live_under_card {st : State} (hwf : st.WF) {c : Card}
    (hk : c.rank ≠ Rank.king) (h : CanRaiseS st c) :
    ∃ (a : Anchor) (u : Card) (P S : List Card),
      (st.piles a).faceUp = P ++ u :: c :: S ∧
      u.rank.toIdx = c.rank.toIdx + 1 ∧ u.suit.color ≠ c.suit.color := by
  obtain ⟨-, a, bs, run, hshape, hbs, -⟩ := canRaiseS_flat_necessity hwf h
  -- `bs` is nonempty (the king case is excluded)
  have hbsne : bs ≠ [] := by
    rcases hbs with h | ⟨-, hk'⟩
    · exact h
    · exact absurd hk' hk
  obtain ⟨P, u, hP⟩ := exists_split_last bs hbsne
  subst hP
  have hshape' : (st.piles a).faceUp = P ++ u :: c :: run := by
    rw [hshape]
    simp [List.append_assoc]
  -- the adjacency is a legal fit
  have hrok : runOK (st.piles a).faceUp = true := hwf.2.1 a
  have hfit : canSitOn c u = true := by
    refine SeedKit.runOK_adjacent_fit u c P run ?_
    rw [← hshape']
    exact hrok
  obtain ⟨hr, hcol⟩ := (canSitOn_eq c u).mp hfit
  exact ⟨a, u, P, run, hshape', by omega, fun h => hcol h.symm⟩

/-- **THE FORK'S UNDER-CARDS** — at a `WF` fork of non-king rank both
the witness and its twin sit directly on a card of the opposite colour
family, one rank above them.  (These are the two cards the weak-grade
craft leaves one of free — and the reason its ascent cannot land.) -/
theorem fork_under_cards {st : State} (hwf : st.WF) {x : Card}
    (hx : ForkWitness st x) (hk : x.rank ≠ Rank.king) :
    (∃ (a : Anchor) (u : Card) (P S : List Card),
        (st.piles a).faceUp = P ++ u :: x :: S ∧
        u.rank.toIdx = x.rank.toIdx + 1 ∧ u.suit.color ≠ x.suit.color) ∧
    (∃ (a : Anchor) (v : Card) (P S : List Card),
        (st.piles a).faceUp = P ++ v :: x.twin :: S ∧
        v.rank.toIdx = x.rank.toIdx + 1 ∧ v.suit.color ≠ x.suit.color) := by
  have hxk : CanRaiseS st x := (hx.1 x).mp (Or.inl rfl)
  have hyt : CanRaiseS st x.twin := (hx.1 x.twin).mp (Or.inr rfl)
  have hkT : x.twin.rank ≠ Rank.king := by
    rw [Card.twin_rank]; exact hk
  refine ⟨live_under_card hwf hk hxk, ?_⟩
  obtain ⟨a, v, P, S, hshape, hr, hcol⟩ := live_under_card hwf hkT hyt
  have hcx : x.twin.suit.color = x.suit.color := by
    rw [Card.twin_suit]; exact Suit.color_twin x.suit
  refine ⟨a, v, P, S, hshape, ?_, fun hc => hcol ?_⟩
  · rw [hr, Card.twin_rank]
  · rw [hcx]; exact hc

/-! ## §3. The missing third-suit row, and the assembly -/

/-- **ForkThirdRigid** — THE EXACT MISSING ROW (hthird).  Two
`ForkWitness` states of one class whose pairs are identified name the
same two non-pair suits, and those two suit rungs agree.  This is the
hypothesis `Orig/PairClassZones.lean:128 hthird` carries "explicitly,
not assumed-proved". -/
def ForkThirdRigid : Prop :=
  ∀ (F G : State) (x y : Card), F.WF → G.WF → sameOrbitSetoid.r F G →
    ForkWitness F x → ForkWitness G y → (y = x ∨ y = x.twin) →
    ∀ σ : Suit, σ ≠ x.suit → σ ≠ x.twin.suit → rungAt F σ = rungAt G σ

/-- **THE ASSEMBLY** — pair identity + third-suit rigidity ⇒
`ForkPositionRigid`.  Nothing else is used: on the pair suits the pin
`pair_rung_pin` closes both ends, on the other two `hthird` is spent
verbatim. -/
theorem forkPositionRigid_of_pairClass_third
    (hpair : ForkPairClass) (hthird : ForkThirdRigid) : ForkPositionRigid := by
  intro F G x y hF hG hcls hx hy σ
  have hxy : y = x ∨ y = x.twin := hpair F G x y hF hG hcls hx hy
  by_cases h1 : σ = x.suit
  · rw [h1]
    exact pair_half hx hy hxy x.suit (Or.inl rfl)
  · by_cases h2 : σ = x.twin.suit
    · rw [h2]
      exact pair_half hx hy hxy x.twin.suit (Or.inr rfl)
    · exact hthird F G x y hF hG hcls hx hy hxy σ h1 h2

/-- **THE TARGET, REDUCED TO ONE ROW.**  The pair half is now
unconditional (`forkPairClass`), so `ForkPositionRigid` is exactly
`ForkThirdRigid`. -/
theorem forkPositionRigid_of_third (hthird : ForkThirdRigid) :
    ForkPositionRigid :=
  forkPositionRigid_of_pairClass_third forkPairClass hthird

/-! ## §4. The `Position` relationship (confirmed, proved) -/

/-- **RungEq ⇔ found equality at `WF`** — the forward direction is the
rung→found congruence (`Orig2/Fork/CeilingBridge.lean:70
found_congr_of_rungs`, the Orig2 landing of the frozen
`Orig/MacroInternal.lean:760 rung_found_congr`); the converse is the
length of the same list.  So "same rung vector" and "same found tuple"
are the same relation on `WF` class-mates — the question's two
spellings coincide. -/
theorem rungEq_iff_found_eq {u v : State} (hu : u.WF) (hv : v.WF) :
    RungEq u v ↔ ∀ s : Suit, u.found s = v.found s := by
  constructor
  · intro h s
    exact found_congr_of_rungs hu hv (h s)
  · intro h σ
    show (u.found σ).length = (v.found σ).length
    rw [h σ]

/-- `ForkFoundRigid` ⇔ `ForkPositionRigid` at `WF`. -/
theorem forkFoundRigid_iff_forkPositionRigid :
    ForkFoundRigid ↔ ForkPositionRigid := by
  constructor
  · intro h F G x y hF hG hcls hx hy
    exact (rungEq_iff_found_eq hF hG).mpr (h F G x y hF hG hcls hx hy)
  · intro h F G x y hF hG hcls hx hy s
    exact (rungEq_iff_found_eq hF hG).mp (h F G x y hF hG hcls hx hy) s

/-- **`Position` = class ∧ `RungEq`** — confirmed: `Position` is the
quotient by `orbitRungSetoid`, whose relation is *defined* as
`sameOrbitSetoid.r ∧ RungEq` (`Orig2/Substrate/Vocab.lean:361`), so two `WF`
states present the same `Position` exactly when they are orbit-mates at
equal rungs. -/
theorem position_eq_iff (p q : WFState) :
    (Quotient.mk orbitRungSetoid p = Quotient.mk orbitRungSetoid q) ↔
      (sameOrbitSetoid.r p.1 q.1 ∧ RungEq p.1 q.1) :=
  ⟨Quotient.exact, fun h => Quotient.sound (s := orbitRungSetoid) h⟩

/-- **THE CONSEQUENCE FOR `Position`** — `ForkPositionRigid` says a
class carries AT MOST ONE fork `Position`: all its fork states are the
same grid vertex. -/
theorem fork_one_position_of_rigid (h : ForkPositionRigid)
    {F G : State} (x y : Card) (hF : F.WF) (hG : G.WF)
    (hcls : sameOrbitSetoid.r F G) (hx : ForkWitness F x) (hy : ForkWitness G y) :
    (Quotient.mk orbitRungSetoid ⟨F, hF⟩ : Position) =
      Quotient.mk orbitRungSetoid ⟨G, hG⟩ :=
  (position_eq_iff ⟨F, hF⟩ ⟨G, hG⟩).mpr ⟨hcls, h F G x y hF hG hcls hx hy⟩

/-! ## §5. The battery -/

/-! ## §5. The battery -/

#print axioms pair_rung_pin
#print axioms pair_half
#print axioms forkPairClass
#print axioms live_under_card
#print axioms fork_under_cards
#print axioms forkPositionRigid_of_pairClass_third
#print axioms forkPositionRigid_of_third
#print axioms rungEq_iff_found_eq
#print axioms forkFoundRigid_iff_forkPositionRigid
#print axioms position_eq_iff
#print axioms fork_one_position_of_rigid