# Withdrawn definitions removed from the live tree (2026-11-02)

These definitions were explicitly marked WITHDRAWN / FALSE and were not used by
any live proof.  They are preserved verbatim here so the archived refutation
cards that name them stay understandable (copy the definition back into the
named source card to restore).

* `InrExposeResidual` - the live file now points at the archived refutation
  `ForkInrExpRefute.inrExposeResidual_false`.
* `RaiseDeficientGame` - its only consumer was `argmin_of_deficient`, which was
  vacuous (a true implication from a false premise) and was removed with it.

## from `Orig2/Fork/Class/ForkTwinJoin.lean`

```lean
/-- **WITHDRAWN — FALSE.**  Kernel-adjacent model refutation in
`Temp/AS_Report.md` (verified over the 2308-state component and the full
`valley_probe` component; 520/1605 crossed instances fail, 332 components):

```text
s  rungs (10,12,13,0)        s' rungs (11,10,12,0)
σ = H,  M = (11,12,13,0)     target (11,12,13,0) is ABSENT
```

The obstruction is the **twin pull**: `JH` is buried under `TC`; `TC` needs a
rank-10 red base, and the only one is `JD`, which is on the `D` FOUNDATION.
Exposing `JH` therefore forces `pull JD`, which lowers the twin `D` from 12.
So the twin cannot stay fixed: the colour-pinned version fails too.

Consequence: the gap-closer is dead in this form, and `argmin_of_deficient`
below is vacuous (a true implication from a false premise).  Do not cite this
definition as a dischargeable hypothesis. -/
def RaiseDeficientGame : Prop :=
  ∀ (s s' : State) (M : Suit → Nat) (σ : Suit),
    sameOrbitSetoid.r s s' →
    rungAt s σ.twin = M σ.twin →
    rungAt s σ < M σ →
    M σ ≤ rungAt s' σ →
    ∃ s'', sameOrbitSetoid.r s s'' ∧
      rungAt s'' σ = rungAt s σ + 1 ∧
      rungAt s'' σ.twin = rungAt s σ.twin
```

## from `Orig2/Fork/Class/ForkTwinJoin.lean`

```lean
/-- **The deficient step implies the argmin step.**  Given the argmin
hypotheses, set `M` to the current rungs everywhere except the raised twin,
where `M twin` is the endpoint's twin rung.  The other twin is `t`, already at
`M t = rungAt s t`; the endpoint supplies the room.  Note the `twin ≤ t` and
`t ≤ s' t` hypotheses are not even needed: the deficient step is strictly
stronger. -/
theorem argmin_of_deficient (h : RaiseDeficientGame) : ArgminStepGame := by
  intro s s' t hcls hle ht hlt
  have htwin_ne : t ≠ t.twin := by cases t <;> decide
  let M : Suit → Nat :=
    fun τ => if τ = t.twin then rungAt s' t.twin else rungAt s τ
  have hM : M t.twin = rungAt s' t.twin := by simp [M]
  have hMt : M t = rungAt s t := by simp [M, htwin_ne]
  have hmatch : rungAt s (t.twin).twin = M (t.twin).twin := by
    simp [Suit.twin_twin, hMt]
  have hdefc : rungAt s t.twin < M t.twin := by rw [hM]; exact hlt
  have hroom : M t.twin ≤ rungAt s' t.twin := by rw [hM]; exact Nat.le_refl _
  obtain ⟨s'', hss'', hrung, hother⟩ :=
    h s s' M t.twin hcls hmatch hdefc hroom
  refine ⟨s'', hss'', ?_, hrung⟩
  simpa [Suit.twin_twin] using hother
```

## from `Orig2/Fork/Split/ForkBaseEnabling.lean`

```lean
/-- **WITHDRAWN — FALSE.**  Kernel refutation
(`InrExpRefute.inrExposeResidual_false`, and independently
`InrExpRefute.inrExposeResidual_false_via_Perm`): the Perm witness
(`Orig2/ForkPermRefute.lean`) has its pull base `5♥` buried under `4♣`, the
interior slides `4♣` away, and the play is still shortest.  So "exposure during
the interior shortens" is not a theorem, and the `inr` half of `BaseEnabling`
has NO instances (`InrExpRefute.baseEnabling_inr_vacuous`).  The live statement
needs the legal-at-origin gate (`InrExpRefute.InrExpHeadGated`).  Kept so the
refutation can name it; do not cite as a residual. -/
def InrExposeResidual : Prop :=
  ∀ (u v : State) (ρ pre γ₁ γ₂ post : List Move) (c z : Card) (A E : State),
    u.WF → ShufflePlayW u ρ v →
    ρ = pre ++ Move.tabToFound c :: γ₁ ++ Move.foundToTab c (Sum.inr z) :: post →
    ShufflePlayW u pre A →
    (∀ q ∈ γ₁, SlideFwd.ReadSafe c q) →
    (∀ q ∈ γ₁, MtnPr.SeatInert (Sum.inr z) q) →
    A.pileOfTop z = none →
    (∃ k, E.pileOfTop z = some k) →
    ∃ ρ' : List Move, ShufflePlayW u ρ' v ∧ ρ'.length < ρ.length
```

