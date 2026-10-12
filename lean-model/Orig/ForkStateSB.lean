import Orig.ForkWeaker

/-!
# Orig.ForkStateSB — the strong detection, decidable

`forkState` (the maneuver-stable two-conjunct detection) made
computable.  The per-card S-license is read as a Bool (`canRaiseSB`)
by mirroring the flat characterization of `Orig.ForkStateS`'s
`canRaiseS_iff` through the `below`/`aboveIn` vocabulary: over the
piles that hold `c` face up, the canonical first-occurrence split
witnesses the existential (under `st.WF` the run discipline bans
duplicate cards, so every split IS the canonical one).  The witness
search (`forkWitnessSB`) and the census (`forkStateSB`) follow
`Orig.ConjugateProof`'s `forkWitnessB`/`forkStateB` pattern: the two
rung pins are retired (they travel free through the S-iff), the
only-raiser clause widens to the pair-membership biconditional over
`Card.universe`, and the orientation pin stays — at the vanilla grade,
through the banked `canRaiseB`.  NO `Classical`, NO `noncomputable`.
-/

/-! ## §0. The private kit -/

/-- A mid-run nodup bar: an element of the snoc-after-position is not
in the prefix (the private-copy pattern; the home sits beside
`canRaiseS_iff_or` in `Orig.ForkStateS`). -/
private theorem nodup_mid_notmem (d : Card) :
    ∀ (l rest : List Card), (l ++ d :: rest).Nodup → d ∉ l := by
  intro l
  induction l with
  | nil => intro rest _ hm; exact absurd hm (by simp)
  | cons x xs ih =>
      intro rest hnd hm
      rcases List.mem_cons.mp hm with rfl | hin
      · exact absurd (List.mem_append.mpr (Or.inr (List.mem_cons_self ..)))
          ((List.nodup_cons.mp hnd).1)
      · exact ih rest (List.nodup_cons.mp hnd).2 hin

/-! ## §1. The per-card Bool read -/

/-- The flat characterization's read at one pile: `c` sits face up
there, over seat content (or bare over an emptied stock as a king),
with the exit clause (empty run, or the twin's pile found).  The
`below`/`aboveIn` reads are the canonical split of the flat form's
existential. -/
private def canRaiseSBat (st : State) (c : Card) (a : Anchor) : Bool :=
  decide (c ∈ (st.piles a).faceUp) &&
  ((decide (below c (st.piles a).faceUp ≠ []) ||
    (decide ((st.piles a).hidden = []) && decide (c.rank = Rank.king))) &&
  (decide (aboveIn c (st.piles a).faceUp = []) ||
    decide (st.pileOfTop c.twin ≠ none)))

/-- The one-pile read's bridge: pure decide unpacking, no `WF`. -/
private theorem canRaiseSBat_true_iff {st : State} (c : Card) (a : Anchor) :
    canRaiseSBat st c a = true ↔
      ((c ∈ (st.piles a).faceUp) ∧
        (below c (st.piles a).faceUp ≠ [] ∨
          ((st.piles a).hidden = [] ∧ c.rank = Rank.king)) ∧
        (aboveIn c (st.piles a).faceUp = [] ∨
          st.pileOfTop c.twin ≠ none)) := by
  rw [canRaiseSBat]
  constructor
  · intro h
    rw [Bool.and_eq_true] at h
    obtain ⟨hmem, hrest⟩ := h
    rw [Bool.and_eq_true] at hrest
    obtain ⟨hseat, hexit⟩ := hrest
    refine ⟨of_decide_eq_true hmem, ?_, ?_⟩
    · rw [Bool.or_eq_true] at hseat
      rcases hseat with h1 | h2
      · exact Or.inl (of_decide_eq_true h1)
      · rw [Bool.and_eq_true] at h2
        exact Or.inr ⟨of_decide_eq_true h2.1, of_decide_eq_true h2.2⟩
    · rw [Bool.or_eq_true] at hexit
      rcases hexit with h4 | h5
      · exact Or.inl (of_decide_eq_true h4)
      · exact Or.inr (of_decide_eq_true h5)
  · rintro ⟨hmem, (h1 | ⟨h2, h3⟩), (h4 | h5)⟩ <;>
      rw [Bool.and_eq_true, Bool.and_eq_true, Bool.or_eq_true,
        Bool.or_eq_true, Bool.and_eq_true]
    · exact ⟨decide_eq_true hmem, Or.inl (decide_eq_true h1),
        Or.inl (decide_eq_true h4)⟩
    · exact ⟨decide_eq_true hmem, Or.inl (decide_eq_true h1),
        Or.inr (decide_eq_true h5)⟩
    · exact ⟨decide_eq_true hmem, Or.inr ⟨decide_eq_true h2,
        decide_eq_true h3⟩, Or.inl (decide_eq_true h4)⟩
    · exact ⟨decide_eq_true hmem, Or.inr ⟨decide_eq_true h2,
        decide_eq_true h3⟩, Or.inr (decide_eq_true h5)⟩

/-- The computable S-license probe: the flat characterization
(`canRaiseS_iff`) as a Bool — the rung pin `nextUp`, then some pile
read passing the seat and exit clauses. -/
def canRaiseSB (st : State) (c : Card) : Bool :=
  st.nextUp c && Anchor.all.any (fun a => canRaiseSBat st c a)

/-- The probe's bridge to the S-license (the `WF` premise is the flat
characterization's own). -/
theorem canRaiseSB_true_iff {st : State} (hwf : st.WF) {c : Card} :
    canRaiseSB st c = true ↔ CanRaiseS st c := by
  constructor
  · intro h
    rw [canRaiseSB, Bool.and_eq_true, List.any_eq_true] at h
    obtain ⟨hnext, a, _, hbody⟩ := h
    obtain ⟨hcmem, hseat, hexit⟩ := (canRaiseSBat_true_iff c a).1 hbody
    refine (canRaiseS_iff hwf).2
      ⟨hnext, a, below c ((st.piles a).faceUp),
        aboveIn c ((st.piles a).faceUp),
        below_aboveIn_split hcmem, hseat, hexit⟩
  · intro hs
    obtain ⟨hnext, a, bs, run, hshape, hseat, hdisj⟩ := (canRaiseS_iff hwf).1 hs
    have hcmem : c ∈ (st.piles a).faceUp := by
      rw [hshape]
      exact List.mem_append.mpr (Or.inr (List.mem_cons_self ..))
    have hcNbs : c ∉ bs := by
      have hnd : (bs ++ c :: run).Nodup := by
        have h := runOK_nodup (hwf.2.1 a)
        rw [hshape] at h
        exact h
      exact nodup_mid_notmem c bs run hnd
    have hseat' : (below c (st.piles a).faceUp ≠ [] ∨
        ((st.piles a).hidden = [] ∧ c.rank = Rank.king)) := by
      rcases hseat with hbs | hhk
      · refine Or.inl ?_
        rw [hshape, below_append_stop hcNbs]
        exact hbs
      · exact Or.inr hhk
    have hexit' : (aboveIn c (st.piles a).faceUp = [] ∨
        st.pileOfTop c.twin ≠ none) := by
      rcases hdisj with rfl | htwin
      · refine Or.inl ?_
        rw [aboveIn, hshape, fromCard_append_stop hcNbs]
        rfl
      · exact Or.inr htwin
    rw [canRaiseSB, hnext, Bool.true_and, List.any_eq_true]
    exact ⟨a, Anchor.mem_all a,
      (canRaiseSBat_true_iff c a).2 ⟨hcmem, hseat', hexit'⟩⟩

/-! ## §2. The pair-iff clause, decidable -/

/-- The pair predicate's Bool form: membership in the fork pair. -/
private theorem pairSB_true_iff (c x : Card) :
    ((c == x) || (c == x.twin)) = true ↔ (c = x ∨ c = x.twin) := by
  constructor
  · intro h
    rw [Bool.or_eq_true] at h
    rcases h with h1 | h2
    · exact Or.inl (of_decide_eq_true
        (show decide (c = x) = true from by
          rw [show decide (c = x) = (c == x) from rfl, h1]))
    · exact Or.inr (of_decide_eq_true
        (show decide (c = x.twin) = true from by
          rw [show decide (c = x.twin) = (c == x.twin) from rfl, h2]))
  · intro hdp
    rcases hdp with hcx | hctx
    · rw [hcx, Bool.or_eq_true]
      refine Or.inl ?_
      rw [show (x == x) = decide (x = x) from rfl, decide_eq_true rfl]
    · rw [hctx, Bool.or_eq_true]
      refine Or.inr ?_
      rw [show (x.twin == x.twin) = decide (x.twin = x.twin) from rfl,
        decide_eq_true rfl]

/-- The per-card iff of the fork pair, as a Bool: over the whole
universe the pair predicate and the S-probe agree.  The retired rung
pins travel free through `canRaiseS_iff`, so this single clause
replaces the two rung pins of the weak `forkWitnessB`. -/
def forkClause2SB (st : State) (x : Card) : Bool :=
  Card.universe.all (fun c => ((c == x) || (c == x.twin)) == canRaiseSB st c)

/-- The clause's bridge. -/
theorem forkClause2SB_iff {st : State} (hwf : st.WF) {x : Card} :
    forkClause2SB st x = true ↔
      (∀ c, (c = x ∨ c = x.twin) ↔ CanRaiseS st c) := by
  rw [forkClause2SB, List.all_eq_true]
  constructor
  · intro hall c
    have hb : (((c == x) || (c == x.twin)) == canRaiseSB st c) = true :=
      hall c (Card.mem_universe c)
    have hab : ((c == x) || (c == x.twin)) = canRaiseSB st c :=
      beq_iff_eq.mp hb
    constructor
    · intro hpair
      have hpt : ((c == x) || (c == x.twin)) = true :=
        (pairSB_true_iff c x).2 hpair
      rw [hpt] at hab
      exact (canRaiseSB_true_iff hwf).1 hab.symm
    · intro hs
      have hSB : canRaiseSB st c = true := (canRaiseSB_true_iff hwf).2 hs
      exact (pairSB_true_iff c x).1 (hab.trans hSB)
  · intro hriff d _
    cases hp : ((d == x) || (d == x.twin)) with
    | true =>
        have hSB : canRaiseSB st d = true :=
          (canRaiseSB_true_iff hwf).2 ((hriff d).mp
            ((pairSB_true_iff d x).1 hp))
        rw [hSB]
        rfl
    | false =>
        have hnpair : ¬(d = x ∨ d = x.twin) := by
          intro hdp
          rw [(pairSB_true_iff d x).2 hdp] at hp
          exact absurd hp (by simp)
        cases hh : canRaiseSB st d with
        | true =>
            exact absurd
              ((hriff d).mpr ((canRaiseSB_true_iff hwf).1 hh)) hnpair
        | false => rfl

/-! ## §3. The witness row, the search, the census -/

/-- The orientation pin in Bool form: the twin has no vanilla lift
(the banked `canRaiseB`, read at its false side). -/
private theorem canRaiseB_not_iff {st : State} {c : Card} :
    (!(canRaiseB st c)) = true ↔ ¬ CanRaise st c := by
  constructor
  · intro h hcan
    rw [canRaiseB_true_iff.2 hcan] at h
    exact absurd h (by simp)
  · intro h
    cases hb : canRaiseB st c with
    | true => exact absurd (canRaiseB_true_iff.1 hb) h
    | false => rfl

/-- The witness row: the pair-iff clause plus the orientation pin. -/
def forkWitnessRowSB (st : State) (x : Card) : Bool :=
  forkClause2SB st x && !(canRaiseB st x.twin)

/-- The row's conjunction bridge at the definition's grouping. -/
theorem forkWitnessRowSB_and2 {st : State} {x : Card} :
    forkWitnessRowSB st x = true ↔
      (forkClause2SB st x = true ∧ (!(canRaiseB st x.twin)) = true) := by
  constructor
  · intro h
    rw [forkWitnessRowSB] at h
    simp only [Bool.and_eq_true] at h
    exact h
  · intro h
    rw [forkWitnessRowSB]
    simp only [Bool.and_eq_true]
    exact h

/-- The row is the `forkState` parcel: the pair-saturation iff and
the orientation pin. -/
theorem forkWitnessRowSB_iff {st : State} (hwf : st.WF) {x : Card} :
    forkWitnessRowSB st x = true ↔
      ((∀ c, (c = x ∨ c = x.twin) ↔ CanRaiseS st c) ∧
        ¬ CanRaise st x.twin) := by
  rw [forkWitnessRowSB_and2, forkClause2SB_iff hwf, canRaiseB_not_iff]

/-- **The computable witness search** for the strong detection. -/
def forkWitnessSB (st : State) : Option Card :=
  firstWhere (forkWitnessRowSB st) Card.universe

/-- A found SB witness carries the parcel. -/
theorem forkWitnessSB_sound {st : State} (hwf : st.WF) {x : Card}
    (h : forkWitnessSB st = some x) :
    (∀ c, (c = x ∨ c = x.twin) ↔ CanRaiseS st c) ∧
      ¬ CanRaise st x.twin :=
  (forkWitnessRowSB_iff hwf).1
    (firstWhere_sound (p := forkWitnessRowSB st) (l := Card.universe) h)

/-- **The strong detection census** — decidable grade. -/
def forkStateSB (st : State) : Bool :=
  Card.universe.any (forkWitnessRowSB st)

/-- **THE REQUIRED END PRODUCT** — the census is the predicate, both
ways: a true fold exhibits a verified witness (the parcel, sound by
the row bridge), and a `forkState` witness verifies the fold. -/
theorem forkStateSB_true_iff {st : State} (hwf : st.WF) :
    forkStateSB st = true ↔ forkState st := by
  rw [forkStateSB, List.any_eq_true]
  constructor
  · rintro ⟨x, _, hxb⟩
    obtain ⟨hriff, hnt⟩ := (forkWitnessRowSB_iff hwf).1 hxb
    exact ⟨x, hriff, hnt⟩
  · rintro ⟨x, hriff, hnt⟩
    exact ⟨x, Card.mem_universe x,
      (forkWitnessRowSB_iff hwf).2 ⟨hriff, hnt⟩⟩

#print axioms canRaiseSB_true_iff
#print axioms forkClause2SB_iff
#print axioms forkWitnessRowSB_iff
#print axioms forkWitnessSB_sound
#print axioms forkStateSB_true_iff
