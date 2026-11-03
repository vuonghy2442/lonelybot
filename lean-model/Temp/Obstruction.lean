import Orig2.Fork.Local.ForkCriticalPair
import Orig2.Substrate.CargoRaise

set_option autoImplicit false
set_option linter.unusedVariables false

/-!
# Temp/Obstruction — why a card is not `raiseS`-able

At a `WF` state the S-licence splits (`canRaiseS_split`):

    CanRaiseS st c  ↔  st.nextUp c = true ∧ freeCardS st c = true

so `¬ CanRaiseS` is a pure `Bool` read: the foundation gate is closed, or the
tableau-readiness probe `freeCardS` is `false`.  Unfolding `freeCardS` at the
card's holding pile gives exactly three local obstructions:

* the holding pile is missing: the card is not face-up in any pile at all (in
  the stock, the waste, the foundations, or still face-down).  This is *not*
  covered by `nextUp = false`, since such a card can well be next-up (a stock
  ace at an empty foundation is the cheapest witness);
* the card is buried (`run ≠ []` above it) and its twin tops no pile;
* the card bottoms its pile's face-up run and either has hidden cards beneath
  it (raising it would flip them: a *commit*) or is a lone non-king (the empty
  seat is not open to it).

No `sorry`, no `Classical`, no `noncomputable`, no new `Prop`.
-/

/-- **The converse of the split**: foundation gate + tableau readiness give the
S-licence.  This is `canRaiseS_split.mpr`, recorded as a named projection. -/
theorem canRaiseS_of_nextUp_of_freeCardS {z : State} (hz : z.WF) {x : Card}
    (hn : z.nextUp x = true) (hf : freeCardS z x = true) : CanRaiseS z x :=
  (canRaiseS_split hz).mpr ⟨hn, hf⟩

/-- **The obstruction trichotomy.**  At a `WF` state, a card that is not
`raiseS`-able is obstructed in one of three ways:

1. the foundation gate is closed (`nextUp = false`) **or** the card is
   face-up in no pile (`pileHolding = none`: stock, waste, foundation, or still
   face-down) — no cargo slide can expose such a card as a pile top;
2. it is buried: it sits in pile `a` under a nonempty run, and its twin tops
   no pile (so neither it nor the mate-slide can expose it);
3. it bottoms its pile's face-up run (`below = []`) and either the pile has
   hidden cards (raising it would reveal — a commit) or it is not a king (a
   lone non-king has no empty seat).

The three clauses are the three ways `freeCardS` can be `false`, read at the
holding pile: the seat clause `(below ≠ [] ∨ hidden = [] ∧ x king)` and the
cover clause `(above = [] ∨ x.twin tops a pile)`. -/
theorem not_canRaiseS_cases {z : State} (hz : z.WF) {x : Card}
    (h : ¬ CanRaiseS z x) :
    z.nextUp x = false ∨ z.pileHolding x = none
      ∨ (∃ a bs run, z.pileHolding x = some a ∧
          (z.piles a).faceUp = bs ++ x :: run ∧ run ≠ [] ∧ z.pileOfTop x.twin = none)
      ∨ (∃ a, z.pileHolding x = some a ∧ below x (z.piles a).faceUp = [] ∧
          ((z.piles a).hidden ≠ [] ∨ x.rank ≠ Rank.king)) := by
  have hsp : ¬ (z.nextUp x = true ∧ freeCardS z x = true) :=
    fun hp => h ((canRaiseS_split hz).mpr hp)
  cases hn : z.nextUp x with
  | false => exact Or.inl rfl
  | true =>
      have hf : freeCardS z x = false := by
        cases hb : freeCardS z x with
        | false => rfl
        | true => exact absurd ⟨hn, hb⟩ hsp
      cases hh : z.pileHolding x with
      | none => exact Or.inr (Or.inl rfl)
      | some a =>
          have hmem : x ∈ (z.piles a).faceUp := pileHolding_mem hh
          obtain ⟨run₀, hfc⟩ := tfc_fromCard_cons_head _ hmem
          -- the readiness probe, unfolded at the holding pile and at `fromCard`
          have hbody :
              ((decide (below x ((z.piles a).faceUp) ≠ []) ||
                  (decide ((z.piles a).hidden = []) && decide (x.rank = Rank.king))) &&
                (decide (run₀ = []) || (z.pileOfTop x.twin).isSome)) = false := by
            have h0 : freeCardS z x = false := hf
            simp only [freeCardS, hh] at h0
            rw [hfc] at h0
            simpa using h0
          -- split the seat clause
          cases hS1 : (decide (below x ((z.piles a).faceUp) ≠ []) ||
              (decide ((z.piles a).hidden = []) && decide (x.rank = Rank.king))) with
          | false =>
              -- (3) the card bottoms its run
              have hbel : below x ((z.piles a).faceUp) = [] := by
                cases hbl : below x ((z.piles a).faceUp) with
                | nil => rfl
                | cons y ys =>
                    rw [hbl] at hS1
                    simp at hS1
              have hb2 :
                  (decide ((z.piles a).hidden = []) && decide (x.rank = Rank.king)) = false := by
                rw [hbel] at hS1
                simpa using hS1
              have hk : (z.piles a).hidden ≠ [] ∨ x.rank ≠ Rank.king := by
                cases hhid : (z.piles a).hidden with
                | cons y ys => exact Or.inl (by simp)
                | nil =>
                    refine Or.inr (of_decide_eq_false ?_)
                    have h1 : decide (x.rank = Rank.king) = false := by
                      rw [hhid] at hb2
                      simpa using hb2
                    exact h1
              exact Or.inr (Or.inr (Or.inr ⟨a, rfl, hbel, hk⟩))
          | true =>
              -- (2) the card is buried and the twin tops no pile
              have hS2 : (decide (run₀ = []) || (z.pileOfTop x.twin).isSome) = false := by
                cases h2 : (decide (run₀ = []) || (z.pileOfTop x.twin).isSome) with
                | false => rfl
                | true =>
                    rw [hS1, h2] at hbody
                    exact absurd hbody (by simp)
              have hrun : run₀ ≠ [] := by
                intro hc
                rw [hc] at hS2
                simp at hS2
              have htwin : z.pileOfTop x.twin = none := by
                cases hp : z.pileOfTop x.twin with
                | none => rfl
                | some k =>
                    rw [hp] at hS2
                    simp at hS2
              have hface : (z.piles a).faceUp =
                  below x ((z.piles a).faceUp) ++ x :: run₀ := by
                have hb := tfc_below_fromCard x ((z.piles a).faceUp)
                rw [hfc] at hb
                exact hb.symm
              exact Or.inr (Or.inr (Or.inl
                ⟨a, below x ((z.piles a).faceUp), run₀, rfl, hface, hrun, htwin⟩))

/-- **Case (2) is a cover.**  A card buried under a nonempty face-up run sits
under a card: the run's head is directly on top of it, i.e. `CoveredAt z x`.

This is the `CoveredAt` projection of case (2) of `not_canRaiseS_cases`
(the twin clause is irrelevant to the cover and is not required). -/
theorem covered_of_not_canRaiseS {z : State} (hz : z.WF) {x : Card} {a : Anchor}
    {bs run : List Card}
    (hhold : z.pileHolding x = some a)
    (hface : (z.piles a).faceUp = bs ++ x :: run)
    (hrun : run ≠ []) :
    CoveredAt z x := by
  cases run with
  | nil => exact absurd rfl hrun
  | cons d rest =>
    have hnd : (bs ++ x :: d :: rest).Nodup := by
      rw [← hface]
      exact runOK_nodup (hz.2.1 a)
    have hdnotbs : d ∉ bs := by
      intro hmem
      exact ((List.nodup_append.1 hnd).2.2 d hmem) d (by simp) rfl
    have hnd2 : (x :: d :: rest).Nodup := (List.nodup_append.1 hnd).2.1
    have hxnd : x ≠ d := by
      intro hxd
      exact (List.nodup_cons.1 hnd2).1 (by rw [hxd]; exact List.mem_cons_self ..)
    have hdmem : d ∈ (z.piles a).faceUp := by
      rw [hface]
      exact List.mem_append.mpr (Or.inr (by simp))
    have hholdd : z.pileHolding d = some a := (pileHolding_eq_some_iff hz).2 hdmem
    have hbd : below d ((z.piles a).faceUp) = bs ++ [x] := by
      rw [hface, below_append_notmem hdnotbs, below_cons, ite_eq_right hxnd,
        below_cons_self]
    refine ⟨d, ?_⟩
    rw [tfc_seatOf_pair hholdd]
    show (match (below d (z.piles a).faceUp).getLast? with
      | none => some (Sum.inl a)
      | some z => some (Sum.inr z)) = some (Sum.inr x)
    rw [hbd, tfc_getLast?_lastOf, lastOf_snoc]

#print axioms canRaiseS_of_nextUp_of_freeCardS
#print axioms not_canRaiseS_cases
#print axioms covered_of_not_canRaiseS
