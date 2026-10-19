import Orig2.KingTrace
import Orig2.KingOrbitFull
import Orig2.TwinPointFunctor

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# Temp/KingSwapStrict — the strict king-seat swap from the anchor swap

At a bare king pair seated on the anchors `a` and `a'`, the anchor
transposition `AnchorPerm.swap a a'` produces exactly the strict twin
swap of `x` and `x.twin`: both bare piles are singletons, so no other
card changes seat, and `State.permute` changes only the pile indexing.

Zero `sorry`, zero `Classical.choice`.
-/

/-- Every card resting in a bare singleton pile is that singleton. -/
private theorem eq_of_seatOf_inl_of_bare {u : State} {y z : Card} {a : Anchor}
    (hse : seatOf u y = some (Sum.inl a))
    (hbare : (u.piles a).faceUp = [z]) : y = z := by
  have hmem : y ∈ (u.piles a).faceUp :=
    pileHolding_mem (tfc_seatOf_of_inl hse).1
  simpa [hbare] using hmem

/-- **`twinPairSwapStrict_permute_swap`** — the anchor transposition of the
two bare king piles is the strict pair exchange. -/
theorem twinPairSwapStrict_permute_swap
    {u : State} {x : Card} {a a' : Anchor}
    (hwf : u.WF) (hking : x.rank = Rank.king)
    (hx : seatOf u x = some (Sum.inl a))
    (hxt : seatOf u x.twin = some (Sum.inl a'))
    (hne : a ≠ a')
    (hbareA : (u.piles a).faceUp = [x] ∧ (u.piles a).hidden = [])
    (hbareB : (u.piles a').faceUp = [x.twin] ∧ (u.piles a').hidden = []) :
    twinPairSwapStrict u (u.permute (AnchorPerm.swap a a')) x := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [State.seatOf_permute (σ := AnchorPerm.swap a a') (st := u) hwf x, hx]
    simp [Base.permute, hxt]
  · rw [State.seatOf_permute (σ := AnchorPerm.swap a a') (st := u) hwf x.twin, hxt]
    simp [Base.permute, hx]
  · intro y hyx hyt
    rw [State.seatOf_permute (σ := AnchorPerm.swap a a') (st := u) hwf y]
    cases hse : seatOf u y with
    | none => rfl
    | some b =>
        cases b with
        | inr z => simp [Base.permute]
        | inl c =>
            have hca : c ≠ a := by
              intro hca
              subst hca
              exact hyx (eq_of_seatOf_inl_of_bare hse hbareA.1)
            have hca' : c ≠ a' := by
              intro hca'
              subst hca'
              exact hyt (eq_of_seatOf_inl_of_bare hse hbareB.1)
            have hfix : AnchorPerm.swapFun a a' c = c :=
              AnchorPerm.swapFun_of_ne hca hca'
            simp [Base.permute, hfix]
  · constructor
    · intro j
      by_cases hja : j = a
      · subst hja
        simp only [State.permute, AnchorPerm.swap_invFun, AnchorPerm.swapFun_a]
        rw [hbareA.2, hbareB.2]
      · by_cases hja' : j = a'
        · subst hja'
          simp only [State.permute, AnchorPerm.swap_invFun, AnchorPerm.swapFun_e]
          rw [hbareB.2, hbareA.2]
        · simp only [State.permute, AnchorPerm.swap_invFun,
            AnchorPerm.swapFun_of_ne hja hja']
    · rfl
  · intro s
    rfl
  · rfl
  · rfl
  · rfl

#check twinPairSwapStrict_permute_swap

/-- **`swappableIn_king_of_permute_swap`** — the strict swap realized by a
`KingShuffle` lands in the reversible orbit, giving `SwappableIn`. -/
theorem swappableIn_king_of_permute_swap
    {u : State} {x : Card} {a a' : Anchor}
    (hwf : u.WF) (hking : x.rank = Rank.king)
    (hx : seatOf u x = some (Sum.inl a))
    (hxt : seatOf u x.twin = some (Sum.inl a'))
    (hne : a ≠ a')
    (hbareA : (u.piles a).faceUp = [x] ∧ (u.piles a).hidden = [])
    (hbareB : (u.piles a').faceUp = [x.twin] ∧ (u.piles a').hidden = [])
    (hshuffle : KingShuffle u (u.permute (AnchorPerm.swap a a'))) :
    SwappableIn u x := by
  refine ⟨u.permute (AnchorPerm.swap a a'), ?_, ?_⟩
  · exact twinPairSwapStrict_permute_swap hwf hking hx hxt hne hbareA hbareB
  · exact bareCargo_sameOrbit (king_shuffle_closure hwf hshuffle)

#print axioms twinPairSwapStrict_permute_swap
#print axioms swappableIn_king_of_permute_swap
