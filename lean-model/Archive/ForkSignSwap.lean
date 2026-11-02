import Orig2.Fork.ForkTwinJoin

set_option autoImplicit false

/-!
# FS_SignSwap — the arithmetic core of V-prime, kernel-checked

Scratch card (`Temp/`), READ-ONLY on `Orig2/`; nothing committed.  No `sorry`,
no `Classical.choice`, no `nativeDecide`; axiom battery at the tail.

`TwinJoin.SignSwap` reads only the two rung vectors, so V-prime is a statement
of pure `Nat` arithmetic.  Four facts, all constructive:

* `signSwap_of_tie` — **A TIE AT ONE ENDPOINT IS A SIGN SWAP.**  If the twin
  pair `{t, t.twin}` is tied at `s`, then `SignSwap s s' t` holds for *every*
  `s'`.  (A fork state has its twin pair tied at the fork rank, so the fork
  supplies the target's hypothesis against any class-mate, for free.)

* `signSwap_of_twin_exchange` — **AN EXCHANGE OF THE TWIN COLUMNS IS A SIGN
  SWAP.**  If the two states swap the values of the twin pair, `SignSwap`.

* `signSwap_iff_same_strict_order` — **THE EXACT FAILURE FORM.**  There is no
  sign swap at `t` exactly when both states order the twin pair *strictly* and
  in the *same* direction.  (This is the whole content of V-prime: it can only
  fail on a pair whose strict order is preserved, on that suit pair, with no
  tie at either endpoint.)

* `not_signSwap_tie_free` / `strict_orders_agree` — the two halves used in the
  report's reading of the failure.
-/

namespace TwinJoin

/-- **A tie at `s` gives a sign swap against every `s'`.** -/
theorem signSwap_of_tie {s s' : State} {t : Suit}
    (h : rungAt s t = rungAt s t.twin) : SignSwap s s' t := by
  unfold SignSwap
  have h' : rungAt s t.twin ≤ rungAt s t := Nat.le_of_eq h.symm
  rcases Nat.le_total (rungAt s' t) (rungAt s' t.twin) with hle | hle
  · exact Or.inl ⟨h', hle⟩
  · exact Or.inr ⟨hle, Nat.le_of_eq h⟩

/-- **Swapping the twin columns between the two states is a sign swap.** -/
theorem signSwap_of_twin_exchange {s s' : State} {t : Suit}
    (h1 : rungAt s' t = rungAt s t.twin)
    (h2 : rungAt s' t.twin = rungAt s t) : SignSwap s s' t := by
  unfold SignSwap
  rw [h1, h2]
  rcases Nat.le_total (rungAt s t.twin) (rungAt s t) with hle | hle
  · exact Or.inl ⟨hle, hle⟩
  · exact Or.inr ⟨hle, hle⟩

/-- **THE FAILURE FORM.**  No sign swap at `t` iff both states order the twin
pair strictly and in the same direction. -/
theorem signSwap_iff_same_strict_order {s s' : State} {t : Suit} :
    ¬ SignSwap s s' t ↔
      ((rungAt s t < rungAt s t.twin ∧ rungAt s' t < rungAt s' t.twin) ∨
       (rungAt s t.twin < rungAt s t ∧ rungAt s' t.twin < rungAt s' t)) := by
  unfold SignSwap
  constructor
  · intro h
    have hd1 : ¬ (rungAt s t.twin ≤ rungAt s t ∧ rungAt s' t ≤ rungAt s' t.twin) :=
      fun x => h (Or.inl x)
    have hd2 : ¬ (rungAt s' t.twin ≤ rungAt s' t ∧ rungAt s t ≤ rungAt s t.twin) :=
      fun x => h (Or.inr x)
    by_cases h1 : rungAt s t.twin < rungAt s t
    · have hb : rungAt s t.twin ≤ rungAt s t := Nat.le_of_lt h1
      have hlt : ¬ (rungAt s' t ≤ rungAt s' t.twin) :=
        fun hx => hd1 ⟨hb, hx⟩
      exact Or.inr ⟨h1, Nat.lt_of_not_le hlt⟩
    · by_cases h2 : rungAt s t < rungAt s t.twin
      · have ha : rungAt s t ≤ rungAt s t.twin := Nat.le_of_lt h2
        have hlt : ¬ (rungAt s' t.twin ≤ rungAt s' t) :=
          fun hx => hd2 ⟨hx, ha⟩
        exact Or.inl ⟨h2, Nat.lt_of_not_le hlt⟩
      · have e : rungAt s t = rungAt s t.twin :=
          Nat.le_antisymm (Nat.le_of_not_lt h1) (Nat.le_of_not_lt h2)
        exact absurd (signSwap_of_tie (s' := s') e) h
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · rintro (⟨x1, x2⟩ | ⟨x1, x2⟩)
      · exact absurd x1 (Nat.not_le.mpr h1)
      · exact absurd x1 (Nat.not_le.mpr h2)
    · rintro (⟨x1, x2⟩ | ⟨x1, x2⟩)
      · exact absurd x2 (Nat.not_le.mpr h2)
      · exact absurd x2 (Nat.not_le.mpr h1)

/-- **NO SIGN SWAP ⟹ NO TIE** at either endpoint. -/
theorem not_signSwap_tie_free {s s' : State} {t : Suit}
    (h : ¬ SignSwap s s' t) : rungAt s t ≠ rungAt s t.twin :=
  fun he => h (signSwap_of_tie he)

/-- **NO SIGN SWAP ⟹ THE STRICT ORDERS AGREE.**  If `s` orders the pair
strictly one way, so does `s'`. -/
theorem strict_orders_agree {s s' : State} {t : Suit}
    (h : ¬ SignSwap s s' t) :
    (rungAt s t < rungAt s t.twin → rungAt s' t < rungAt s' t.twin) ∧
    (rungAt s t.twin < rungAt s t → rungAt s' t.twin < rungAt s' t) := by
  have h' := (signSwap_iff_same_strict_order (s := s) (s' := s') (t := t)).mp h
  constructor
  · intro h1
    rcases h' with ⟨-, h2⟩ | ⟨h2, -⟩
    · exact h2
    · exact absurd h2 (Nat.lt_asymm h1)
  · intro h1
    rcases h' with ⟨h2, -⟩ | ⟨-, h2⟩
    · exact absurd h1 (Nat.lt_asymm h2)
    · exact h2

end TwinJoin

namespace TwinJoin

/-! ## §2. The fork supplies the hypothesis — and the target's fork branch

`ForkWitness F x` pins `x` and `x.twin` as the S-live pair, hence (by the
S-license rung pin `canRaiseS_rung`, cargo legs never write foundations) both
columns sit at `x.rank` at `F`: the twin pair is **tied** at the fork.  By
`signSwap_of_tie` that alone gives `SignSwap F G x.suit` for *every* `G`. -/

/-- **THE FORK'S TWIN PAIR IS TIED AT THE FORK RANK.** -/
theorem forkWitness_twin_tied {F : State} {x : Card} (h : ForkWitness F x) :
    rungAt F x.suit = rungAt F x.twin.suit := by
  have h1 : rungAt F x.suit = x.rank.toIdx :=
    canRaiseS_rung ((h.1 x).mp (Or.inl rfl))
  have h2 : rungAt F x.twin.suit = x.twin.rank.toIdx :=
    canRaiseS_rung ((h.1 x.twin).mp (Or.inr rfl))
  rw [h1, h2, Card.twin_rank]

/-- **THE FORK SUPPLIES THE SIGN SWAP AGAINST EVERY CLASS-MATE.**  No
hypothesis on `G` at all (not `WF`, not saturation, not `sameOrbitSetoid`). -/
theorem signSwap_of_forkWitness {F G : State} {x : Card} (h : ForkWitness F x) :
    SignSwap F G x.suit := by
  refine signSwap_of_tie (s' := G) ?_
  rw [← Card.twin_suit]
  exact forkWitness_twin_tied h

/-- **THE TARGET'S FORK BRANCH IS IMMEDIATE.**  At `s := F` the second
disjunct of `TwinJoinOrForkTarget` holds outright. -/
theorem target_conclusion_at_fork {F s' : State} {t : Suit} {x : Card}
    (hx : ForkWitness F x) :
    (∃ s''', JoinAt F s' s''' t) ∨
      (∃ H y, sameOrbitSetoid.r F H ∧ ForkWitness H y) :=
  Or.inr ⟨F, x, sameOrbitSetoid.iseqv.refl F, hx⟩

/-- **AN EQUAL-RUNG PAIR JOINS TO ITSELF.**  If the two states carry the same
rung vector, the componentwise maximum is that vector, attained at `s` itself.
(So on the equal-rung stratum the target's join disjunct needs no construction
and no sign swap.) -/
theorem joinAt_self_of_rung_eq {s s' : State} {t : Suit}
    (h : ∀ σ, rungAt s σ = rungAt s' σ) : JoinAt s s' s t := by
  refine ⟨sameOrbitSetoid.iseqv.refl s, ?_, ?_⟩
  · show rungAt s t = Nat.max (rungAt s t) (rungAt s' t)
    rw [h t]
    exact (Nat.max_self _).symm
  · show rungAt s t.twin = Nat.max (rungAt s t.twin) (rungAt s' t.twin)
    rw [h t.twin]
    exact (Nat.max_self _).symm

/-- **THE JOIN IS FREE FOR A COMPARABLE PAIR.**  If `s ≤ s'` componentwise, the
componentwise maximum of the pair columns is already `s'`'s, attained at `s'`. -/
theorem joinAt_right_of_rung_le {s s' : State} {t : Suit}
    (hcls : sameOrbitSetoid.r s s') (h : ∀ σ, rungAt s σ ≤ rungAt s' σ) :
    JoinAt s s' s' t := by
  refine ⟨hcls, ?_, ?_⟩
  · show rungAt s' t = Nat.max (rungAt s t) (rungAt s' t)
    exact (Nat.max_eq_right (h t)).symm
  · show rungAt s' t.twin = Nat.max (rungAt s t.twin) (rungAt s' t.twin)
    exact (Nat.max_eq_right (h t.twin)).symm

end TwinJoin
#print axioms TwinJoin.signSwap_of_tie
#print axioms TwinJoin.signSwap_of_twin_exchange
#print axioms TwinJoin.signSwap_iff_same_strict_order
#print axioms TwinJoin.not_signSwap_tie_free
#print axioms TwinJoin.strict_orders_agree
#print axioms TwinJoin.forkWitness_twin_tied
#print axioms TwinJoin.signSwap_of_forkWitness
#print axioms TwinJoin.target_conclusion_at_fork
#print axioms TwinJoin.joinAt_self_of_rung_eq

#print axioms TwinJoin.joinAt_right_of_rung_le
