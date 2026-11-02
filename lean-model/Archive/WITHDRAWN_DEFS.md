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



## Refuted closed Props removed from the live tree (2026-11-02)

Each was a closed `Prop` with a kernel-checked refutation in the live tree andno non-vacuous live consumer.  Text preserved verbatim.

### `LandingBracketAllLive` - from `Orig2/Fork/Third/ForkSurvivor.lean`

```lean
/-- The residual's syntactic shape **without** the `SplitHyp` gate and
**without** the third-suit hypotheses. -/
def LandingBracketAllLive : Prop :=
  ∀ (u v : State) (rho : List Move) (F : State)
    (left right : List Move) (c d : Card) (b : Base)
    (pre post tail : List Move),
    u.WF → SSaturated u → SSaturated v → ShufflePlayW u rho v →
    ValleyElim.ValleySplitAt u v rho F →
    rho = left ++ right →
    left = pre ++ Move.foundToTab c b :: post →
    (∀ m ∈ post, ValleyElim.FreeMove m) →
    right = Move.tabToFound d :: tail →
    ∀ (A' B : State), ShufflePlayW u pre A' →
      State.step A' (Move.foundToTab c b) = some B →
      ∀ e : Card, CanRaiseS B e →
      ∃ (α γ β : List Move) (z : Card) (bz : Base) (P Q : State),
        rho = α ++ Move.foundToTab z bz :: γ ++ Move.tabToFound z :: β ∧
        (∀ q ∈ γ, R12.ReadOK z q)

/-- **THE THIRD-SUIT HYPOTHESES CANNOT BE DROPPED** (at the ungated level): the
loop is a valley split whose landing has the S-live card `5H` but no read-safe
same-card bracket anywhere (`ExistRefute.no_bracket_data`). -/
```

### `not_landingBracketAllLive` - from `Orig2/Fork/Third/ForkSurvivor.lean`

```lean
theorem not_landingBracketAllLive : ¬ LandingBracketAllLive := by
  intro h
  have hb := h ExistRefute.u ExistRefute.V ExistRefute.rho ExistRefute.F
    [ExistRefute.mPull, ExistRefute.mS1, ExistRefute.mS2] [ExistRefute.mRaise]
    ExistRefute.H5 ExistRefute.H5 (Sum.inr ExistRefute.C6) []
    [ExistRefute.mS1, ExistRefute.mS2] []
    ExistRefute.u_wf ExistRefute.u_sat ExistRefute.V_sat ExistRefute.play
    ExistRefute.split rfl rfl ?_ rfl
    ExistRefute.u ExistRefute.B (Walk.nil ExistRefute.u) ExistRefute.step_pull
    ExistRefute.H5 loop_B_H5_live
  · obtain ⟨α, γ, β, z, bz, P, Q, hρ, hread⟩ := hb
    exact ExistRefute.no_bracket_data ⟨α, γ, β, z, bz, hρ, hread⟩
  · intro m hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl
    · exact free_slide ExistRefute.C4 (Sum.inr ExistRefute.H5)
    · exact free_slide ExistRefute.C4 (Sum.inr ExistRefute.D5)

/-! ## 2. The kill taxonomy -/

/-- `R12.ReadOK` is decidable: all its clauses are decidable equalities on the
finite card/suit/base types.  This keeps the kill search constructive. -/
instance readOKDecidable (z : Card) (q : Move) : Decidable (R12.ReadOK z q) := by
  cases q <;> simp only [R12.ReadOK] <;> infer_instance

/-- A play whose every letter is read-safe for `e` preserves `CanRaise e`. -/
```

### `SelfPullRaiseInPre` - from `Orig2/Fork/Third/ForkMate.lean`

```lean
/-- **THE TARGET'S RAISE CLAUSE IS NOT A THEOREM.**  If `pre` is free-or-pull,
contains `pull e`, and ends with `e` S-live, one cannot conclude that `raise e`
occurs in `pre` after the pull.  (`PairPullRaiseInPre`'s existence half, with
exactly the brief's survivor hypothesis `CanRaiseS`.) -/
def SelfPullRaiseInPre : Prop :=
  ∀ (u A' : State) (pre : List Move) (e : Card) (bz : Base),
    ShufflePlayW u pre A' →
    (∀ m ∈ pre, LandKit.FreeOrPull m) →
    (∃ γ₁ γ₂ : List Move, pre = γ₁ ++ Move.foundToTab e bz :: γ₂) →
    CanRaiseS A' e →
    ∃ γ₁ γ₂ : List Move,
      pre = γ₁ ++ Move.foundToTab e bz :: γ₂ ∧ Move.tabToFound e ∈ γ₂
```

### `not_selfPullRaiseInPre` - from `Orig2/Fork/Third/ForkMate.lean`

```lean
theorem not_selfPullRaiseInPre : ¬ SelfPullRaiseInPre := by
  intro h
  obtain ⟨u, A', pre, e, bz, -, hplay, hall, hmem, hlive, hcon⟩ :=
    self_pull_raise_not_forced
  exact hcon (h u A' pre e bz hplay hall hmem hlive)

/-- The same refutation with the survivor hypothesis weakened to `nextUp`
(which `CanRaiseS` implies); this is the strongest form of the local claim. -/
```

### `SelfPullRaiseInPreNextUp` - from `Orig2/Fork/Third/ForkMate.lean`

```lean
def SelfPullRaiseInPreNextUp : Prop :=
  ∀ (u A' : State) (pre : List Move) (e : Card) (bz : Base),
    ShufflePlayW u pre A' →
    (∀ m ∈ pre, LandKit.FreeOrPull m) →
    (∃ γ₁ γ₂ : List Move, pre = γ₁ ++ Move.foundToTab e bz :: γ₂) →
    A'.nextUp e = true →
    ∃ γ₁ γ₂ : List Move,
      pre = γ₁ ++ Move.foundToTab e bz :: γ₂ ∧ Move.tabToFound e ∈ γ₂
```

### `not_selfPullRaiseInPre_nextUp` - from `Orig2/Fork/Third/ForkMate.lean`

```lean
theorem not_selfPullRaiseInPre_nextUp : ¬ SelfPullRaiseInPreNextUp := by
  intro h
  obtain ⟨u, A', pre, e, bz, huwf, hplay, hall, hmem, hlive, hcon⟩ :=
    self_pull_raise_not_forced
  have hA'wf : A'.WF := SatDifferCensus.ShufflePlayW.wf_end hplay huwf
  have hnext : A'.nextUp e = true := ThirdLive.nextUp_of_canRaiseS hA'wf hlive
  exact hcon (h u A' pre e bz hplay hall hmem hnext)
```

### `PullReadyAtImage` - from `Orig2/Fork/Local/ForkPullSwaps.lean`

```lean
/-- **THE READINESS GAP, NAMED.**  "The pull is legal at the image of the
raise, whenever the window is read-safe and the base is seat-inert."  This is
the one hypothesis the pull-bubble route consumes beyond the residual's own
assumptions.  It is free when `canPlace c b` holds at the raise's origin
(`pullable_raiseSt_of_canPlace`) and is **false in general**
(`Temp/PullSw_Gap.lean`: a bare-king raise inside the window empties the
`inl` base, enabling the pull). -/
def PullReadyAtImage : Prop :=
  ∀ (u v : State) (ρ pre γ post : List Move) (c : Card) (b : Base) (A B : State),
    u.WF → ShufflePlayW u ρ v →
    ρ = pre ++ Move.tabToFound c :: γ ++ Move.foundToTab c b :: post →
    ShufflePlayW u pre A →
    State.step A (Move.tabToFound c) = some B →
    (∀ q ∈ γ, SlideFwd.ReadSafe c q) →
    (∀ q ∈ γ, MtnPr.SeatInert b q) → Pullable B c b

/-- **THE REDUCTION.**  If pull readiness at the raise's image is available
as a lemma (`PullReadyAtImage`), then `MtnPr.SameCardRelocation` follows. -/
```

### `pullReadyAtImage_false` - from `Orig2/Fork/Local/ForkPullSwaps.lean`

```lean
/-- **THE READINESS GAP IS GENUINE.** -/
theorem pullReadyAtImage_false : ¬ PullReadyAtImage := by
  intro h
  have hpull : Pullable gapB GAPK_C (Sum.inl Anchor.p1) :=
    h gapState gapD
      [Move.tabToFound GAPK_C, Move.tabToFound GAPK_W,
        Move.foundToTab GAPK_C (Sum.inl Anchor.p1)]
      [] [Move.tabToFound GAPK_W] [] GAPK_C (Sum.inl Anchor.p1) gapState gapB
      gapState_wf gap_play rfl (Walk.nil gapState) step_raiseC
      (by
        intro q hq
        rw [List.mem_singleton] at hq
        subst hq
        exact gap_readSafe)
      (by
        intro q hq
        rw [List.mem_singleton] at hq
        subst hq
        exact gap_seatInert)
  have hcp := hpull.2
  rw [gapB_not_pullable_C] at hcp
  exact absurd hcp (by simp)


/-! ## §7. The gap instance is still shortenable (the residual is not refuted)

The `§6` configuration has a two-letter witness play to the same endpoint:
`raise SK ; slide HK -> Sum.inl p1`.  So `SameCardRelocation` itself survives
this instance; what §6 kills is only the *pull-bubble route* to it. -/
```

### `sameCardRelocation_of_pullReadyAtImage` - from `Orig2/Fork/Local/ForkPullSwaps.lean`

```lean
theorem sameCardRelocation_of_pullReadyAtImage
    (h : PullReadyAtImage) : MtnPr.SameCardRelocation := by
  intro u v ρ pre γ post c b huwf hplay hρ hread hseat
  exact sameCardRelocation_ready u v ρ pre γ post c b huwf hplay hρ hread hseat
    (fun A B hpre hstep => h u v ρ pre γ post c b A B huwf hplay hρ hpre hstep hread hseat)

/-- **READINESS IS FREE WHEN THE SLIDE IS LEGAL.**  If `canPlace c b` already
holds at the raise's origin, then the pull is ready at the raise's image
(`R12.canPlace_raiseSt` + `foundTop_raiseSt_self`).  Hence the only case the
bubble route misses is the `canPlace c b = false` (exceptional-seat) side —
which is exactly the base-enabling gap of §6. -/
```

### `CoverChainResidual` - from `Orig2/Fork/Local/ForkChain.lean`

```lean
/-- **WITHDRAWN — FALSE.**  Kernel refutation: `Sat.not_coverChainResidual`
(`Orig2/ForkSatChain.lean`), with `Sat.not_noChainRaise` refuting the first
clause on the promoted twin board (`B = Seat.uT`, `v = Seat.BT`, and `BT` IS
`SSaturated`), `d = z' = ♠3`, `tail = [raise ♠3]`.  `Sat.not_noChainRaiseCorr`
even refutes the "exclude the trivial `s1 = [], z' = d` case" repair.

ROOT CAUSE: this residual quantifies over **arbitrary** plays `B → v`; neither
shortest-ness nor the corridor decomposition appears in it, so no event-level
patch can work.  `freeCorridor_of_coverChain` below is therefore a kernel-checked
implication from a FALSE premise.  Cross-suit vacuity is NOT closed by this
route; the live reduction is `NoSeatMateCrossSuit` (`Orig2/Fork/Local/ForkBlocks.lean`),
with the twin/pull-free corner closed modulo `Sat.TwinRelocationResidual`
(`Orig2/ForkSatChain.lean`). -/
def CoverChainResidual : Prop :=
  ∀ (B v : State) (tail : List Move) (d : Card),
    B.WF → SSaturated v → CanRaise B d → ShufflePlayW B tail v →
    ∀ (z' : Card) (s1 s2 : List Move) (A Z : State) (m : Move),
      z'.rank.toIdx ≤ d.rank.toIdx →
      tail = s1 ++ m :: s2 → ShufflePlayW B s1 A → CanRaise A z' →
      State.step A m = some Z → ¬ CanRaise Z z' →
      (m = Move.tabToFound z' ∨
        ∃ x : Card, m = Move.tabToTab x (Sum.inr z') ∧ ¬ CanRaise Z x) → False

/-- **`NoChainRaise`** — the first endpoint of the chain: no chain card of rank
at most `d`'s is *raised* after being raisable.  (This is the same-card
relocation lane: the chain card was pulled and goes straight back up; the
campaign's `PullKit`/`Relocate` machinery owns it.) -/
```

### `NoChainRaise` - from `Orig2/Fork/Local/ForkChain.lean`

```lean
def NoChainRaise : Prop :=
  ∀ (B v : State) (tail : List Move) (d : Card),
    B.WF → SSaturated v → CanRaise B d → ShufflePlayW B tail v →
    ∀ (z' : Card) (s1 s2 : List Move) (A Z : State),
      z'.rank.toIdx ≤ d.rank.toIdx →
      tail = s1 ++ Move.tabToFound z' :: s2 → ShufflePlayW B s1 A →
      CanRaise A z' → State.step A (Move.tabToFound z') = some Z →
      ¬ CanRaise Z z' → False

/-- **`NoCoverStall`** — the second endpoint: no cover of a chain card of rank
at most `d`'s is followed by a mover that is *not* raisable.  This is the
opposite-coloured cover stall. -/
```

### `NoCoverStall` - from `Orig2/Fork/Local/ForkChain.lean`

```lean
def NoCoverStall : Prop :=
  ∀ (B v : State) (tail : List Move) (d : Card),
    B.WF → SSaturated v → CanRaise B d → ShufflePlayW B tail v →
    ∀ (z' x : Card) (s1 s2 : List Move) (A Z : State),
      z'.rank.toIdx ≤ d.rank.toIdx →
      tail = s1 ++ Move.tabToTab x (Sum.inr z') :: s2 → ShufflePlayW B s1 A →
      CanRaise A z' → State.step A (Move.tabToTab x (Sum.inr z')) = some Z →
      ¬ CanRaise Z z' → ¬ CanRaise Z x → False

/-- **THE RESIDUAL DECOMPOSES INTO ITS TWO ENDPOINTS.** -/
```

### `coverChainResidual_iff` - from `Orig2/Fork/Local/ForkChain.lean`

```lean
theorem coverChainResidual_iff :
    CoverChainResidual ↔ NoChainRaise ∧ NoCoverStall := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro B v tail d hB hv hcan hplay z' s1 s2 A Z hle heq hp hcanA hstep hblk
      exact h B v tail d hB hv hcan hplay z' s1 s2 A Z (m := Move.tabToFound z')
        hle heq hp hcanA hstep hblk (Or.inl rfl)
    · intro B v tail d hB hv hcan hplay z' x s1 s2 A Z hle heq hp hcanA hstep hblk hx
      exact h B v tail d hB hv hcan hplay z' s1 s2 A Z (m := Move.tabToTab x (Sum.inr z'))
        hle heq hp hcanA hstep hblk (Or.inr ⟨x, rfl, hx⟩)
  · rintro ⟨h1, h2⟩ B v tail d hB hv hcan hplay z' s1 s2 A Z m hle heq hp hcanA hstep hblk hshape
    rcases hshape with hm | ⟨x, hm, hx⟩
    · have hstep' : State.step A (Move.tabToFound z') = some Z := by rw [← hm]; exact hstep
      exact h1 B v tail d hB hv hcan hplay z' s1 s2 A Z hle
        (hm ▸ heq) hp hcanA hstep' hblk
    · have hstep' : State.step A (Move.tabToTab x (Sum.inr z')) = some Z := by
        rw [← hm]; exact hstep
      exact h2 B v tail d hB hv hcan hplay z' x s1 s2 A Z hle
        (hm ▸ heq) hp hcanA hstep' hblk hx
```

