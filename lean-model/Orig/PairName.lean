import Orig.ForkWeaker

/-!
# Orig.PairName — THE PAIR-NAMING CARD (Stage 1 of the conjugate family)

Both witnesses of one `forkState` agree up to the twin flip: the
rank and the suit pair are invariants of the STATE, not of the
witness (`forkState_pairUnique`).  The witness parcel is packaged as
`ForkWitness` (the two-conjunct `forkState` body, per-witness), the
trivial bridge `forkState_iff` connects the grades, the name rows
read the invariants (`forkState_nameUnique`, `forkState_witness_rungs`),
and the orientations canvas closes with `forkState_orientationUnique`:
at most ONE orientation of the pair can fork a given state — the
witness's vanilla liveness (the banked `forkState_witness_canRaise`
geometry) kills the tilted pin.
-/

/-! ## §0. The witness parcel, packaged

The per-witness body of `forkState`: the pair-saturation iff at the
{slide · raise} grade, plus the orientation pin.  Naming it lets the
rows below phrase geometry over a WITNESS, not over the existential
state predicate. -/

/-- One witness's parcel: `x` names the S-live pair (up to the twin
flip) and its twin is vanilla-blocked. -/
def ForkWitness (st : State) (x : Card) : Prop :=
  (∀ c, (c = x ∨ c = x.twin) ↔ CanRaiseS st c) ∧ ¬ CanRaise st x.twin

/-- The trivial bridge: the existential state predicate unpacks into
the per-witness parcel. -/
theorem forkState_iff {st : State} :
    forkState st ↔ ∃ x, ForkWitness st x :=
  ⟨fun ⟨x, hiff, hnt⟩ => ⟨x, hiff, hnt⟩, fun ⟨x, hiff, hnt⟩ => ⟨x, hiff, hnt⟩⟩

/-! ## §1. The main pair-naming theorem -/

/-- **THE PAIR-NAME THEOREM** — both witnesses of one forkState agree
up to the twin flip: the rank and the suit pair are invariants of the
STATE, not of the witness. -/
theorem forkState_pairUnique {st : State} (hwf : st.WF)
    (h₁ : forkState st) (h₂ : forkState st) :
    ∃ x y, (∀ c, (c = x ∨ c = x.twin) ↔ CanRaiseS st c) ∧
           (¬ CanRaise st x.twin) ∧
           (∀ c, (c = y ∨ c = y.twin) ↔ CanRaiseS st c) ∧
           (¬ CanRaise st y.twin) ∧
           (y = x ∨ y = x.twin) := by
  obtain ⟨x, hiff₁, hnt₁⟩ := h₁
  obtain ⟨y, hiff₂, hnt₂⟩ := h₂
  -- y names itself in its own pair, so y is S-live;
  -- x's iff reads that liveness as membership in x's pair.
  have hxy : y = x ∨ y = x.twin :=
    (hiff₁ y).mpr ((hiff₂ y).mp (Or.inl rfl))
  exact ⟨x, y, hiff₁, hnt₁, hiff₂, hnt₂, hxy⟩

/-! ## §2. The state-level name

The iff already is the no-second-pair row (any S-live card lands in
the named pair); the informative corollary is the name read at the
level of the state: all witnesses share the rank, and the suits form
one twin family. -/

/-- **THE STATE-LEVEL NAME** — any two witnesses agree on the rank
(the twin involution keeps it), and their suits either match or are
twin suits: the pair IN THE ABSTRACT {rank, suit-family} is a state
invariant, not the choice of orienting witness. -/
theorem forkState_nameUnique {st : State} {x y : Card}
    (hx : ForkWitness st x) (hy : ForkWitness st y) :
    y.rank = x.rank ∧ (y.suit = x.suit ∨ y.suit = x.twin.suit) := by
  have hxy : y = x ∨ y = x.twin :=
    (hx.1 y).mpr ((hy.1 y).mp (Or.inl rfl))
  rcases hxy with rfl | h
  · exact ⟨rfl, Or.inl rfl⟩
  · rw [h]
    exact ⟨Card.twin_rank x, Or.inr rfl⟩

/-! ## §3. The rank re-read -/

/-- All witnesses' rungs pin the same rank (canRaiseS_rung both ways,
the twin keeping the rank across the orientation): the rungs read
`x.rank.toIdx` no matter which witness named them. -/
theorem forkState_witness_rungs {st : State} {x y : Card}
    (hx : ForkWitness st x) (hy : ForkWitness st y) :
    rungAt st y.suit = x.rank.toIdx ∧
    rungAt st y.twin.suit = x.rank.toIdx := by
  have hyS : CanRaiseS st y := (hy.1 y).mp (Or.inl rfl)
  have hytS : CanRaiseS st y.twin := (hy.1 y.twin).mp (Or.inr rfl)
  have hr : y.rank = x.rank := (forkState_nameUnique hx hy).1
  constructor
  · rw [← hr]
    exact canRaiseS_rung hyS
  · have ht := canRaiseS_rung hytS
    rwa [Card.twin_rank, hr] at ht

/-! ## §4. The mate-orientations canvas

Could BOTH orientations of the pair fork the SAME state — the iff
permits it (both read the same pair-set {x, x.twin}); the PINS must
decide.  And they do, through the banked engine alone: the upright
witness's parcel FORCES its vanilla liveness
(`forkState_witness_canRaise`, the covered-twin geometry), while the
tilted parcel's pin is exactly the negation of that liveness (the
twin involution reads `x.twin.twin` back as `x`).  So at most ONE
orientation can be a forkState: **the orientation is unique too** —
the mate flip available to the family is a move BETWEEN states, not
an ambiguity WITHIN one. -/

/-- **THE ORIENTATION UNIQUENESS** — the two pins of the two
orientations contradict through the witness geometry: no state admits
both `x` and `x.twin` as fork witnesses. -/
theorem forkState_orientationUnique {st : State} (hwf : st.WF) {x : Card}
    (h₁ : ForkWitness st x) (h₂ : ForkWitness st x.twin) : False := by
  have hnt₂ : ¬ CanRaise st x := by
    have h := h₂.2
    rwa [Card.twin_twin] at h
  exact hnt₂ (forkState_witness_canRaise hwf h₁.1 h₁.2)

/-! ## The audit battery -/

#print axioms forkState_iff
#print axioms forkState_pairUnique
#print axioms forkState_nameUnique
#print axioms forkState_witness_rungs
#print axioms forkState_orientationUnique
