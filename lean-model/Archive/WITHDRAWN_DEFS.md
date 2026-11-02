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



## Vacuous consumers of the refuted split/read-bracket residuals (2026-11-02)

Removed: the `SplitLivePair` / `ReadBracketElim` / `NonforkBracketLocal` consumers.
The three residual DEFINITIONS and the live refutation `not_splitLivePair_of_corner`
are kept as evidence anchors.

### `splitLivePair_of_landing_ne` - from `Orig2/Fork/Class/ForkLivePair.lean`

```lean
/-- **`SplitLivePair` FROM THE LANDING CONTAINMENT PLUS `c ≠ d`.**  At `F`,
`d` is live, so containment puts it in `{c, c.twin}`; `c ≠ d` excludes
`d = c`, so `d = c.twin` and the live set is the twin pair of `d`. -/
theorem splitLivePair_of_landing_ne
    (hland : SplitLiveAtLanding) (hne : SplitNe) : SplitLivePair := by
  intro u v ρ F left right c d b pre post tail h
  have hcontF := contained_at_F_of_landing h
    (fun A' B hpre hstep =>
      hland u v ρ F left right c d b pre post tail A' B h hpre hstep)
  have hcd : c ≠ d := hne u v ρ F left right c d b pre post tail h
  obtain ⟨-, hSFc, hcanD, hSFd⟩ := splitHyp_green h
  have hdt : d = c.twin := by
    rcases hcontF d hSFd with h' | h'
    · exact absurd h' (Ne.symm hcd)
    · exact h'
  have hdtc : d.twin = c := by rw [hdt, card_twin_twin]
  have hSFdt : CanRaiseS F d.twin := by
    rw [hdtc]; exact hSFc
  intro e
  constructor
  · intro he
    rcases hcontF e he with h' | h'
    · exact Or.inr (h'.trans hdtc.symm)
    · exact Or.inl (h'.trans hdt.symm)
  · rintro (h' | h')
    · rw [h']; exact hSFd
    · rw [h']; exact hSFdt
```

### `splitLivePair_of_landing_block` - from `Orig2/Fork/Class/ForkLivePair.lean`

```lean
/-- **`SplitLivePair` FROM THE LANDING CONTAINMENT PLUS `SplitBlock`.**  The
block gives `¬ CanRaise F c`, and `d` is vanilla-raisable at `F`, so `c ≠ d`. -/
theorem splitLivePair_of_landing_block
    (hland : SplitLiveAtLanding) (hblock : SplitBlock) : SplitLivePair := by
  refine splitLivePair_of_landing_ne hland ?_
  intro u v ρ F left right c d b pre post tail h
  obtain ⟨-, -, hcanD, -⟩ := splitHyp_green h
  intro hcd
  exact hblock u v ρ F left right c d b pre post tail h
    (by rw [hcd]; exact hcanD)
```

### `splitLivePair_of_forkAtRaise` - from `Orig2/Fork/Class/ForkLivePair.lean`

```lean
/-- **`SplitLivePair` FROM THE PINNED RESIDUAL.**  The fork branch *is* the
live-pair clause; the shortening branch contradicts the shortest-play
conjunct of `SplitHyp`. -/
theorem splitLivePair_of_forkAtRaise
    (hf : ValleyElimForkAtRaise) : SplitLivePair := by
  intro u v ρ F left right c d b pre post tail h
  obtain ⟨huwf, hsu, hsv, hplay, hsplitAt, hmin, hρ, hleft, hright, hshape,
    hfree, hrightShape⟩ := h
  rcases hf u v ρ F left right c d b pre post tail
      ⟨huwf, hsu, hsv, hplay, hsplitAt, hmin, hρ, hleft, hright, hshape,
        hfree, hrightShape⟩ with hx | ⟨ρ', hρ', hlen⟩
  · exact ((forkWitness_iff F d).mp hx).1
  · exact absurd hlen (Nat.not_lt.mpr (hmin ρ' hρ'))
```

### `splitLivePair_of_valleyElim` - from `Orig2/Fork/Class/ForkLivePair.lean`

```lean
/-- **THE MAIN REDUCTION.**  `ValleyElim.ValleyElimNonfork` alone gives
`SplitLivePair`: minimality kills the elimination branch, and at the fork the
raise card `d` is the fork's raisable card `x` (it cannot be the blocked
`x.twin`), so the live set at `F` is exactly `{d, d.twin}`.

No `SplitBlock`, no `SplitNe`, no extra geometric input. -/
theorem splitLivePair_of_valleyElim
    (helim : ValleyElim.ValleyElimNonfork) : SplitLivePair :=
  splitLivePair_of_forkAtRaise (valleyElimForkAtRaise_of_valleyElim helim)
```

### `readBracketElimMin_of_readBracket` - from `Orig2/Fork/Class/ForkMinCross.lean`

```lean
theorem readBracketElimMin_of_readBracket (h : R12.ReadBracketElim) :
    ReadBracketElimMin := by
  intro u v ρ F huwf hsu hsv hplay _ hsplit
  exact h u v ρ F huwf hsu hsv hplay hsplit
```

### `readBracketElim_of_windowExists` - from `Orig2/Fork/Class/ForkMinCross.lean`

```lean
theorem readBracketElim_of_windowExists (h : ReadWindowExists) :
    R12.ReadBracketElim := by
  intro u v ρ F huwf hsu hsv hplay hsplit
  rcases h u v ρ F huwf hsu hsv hplay hsplit with
    hf | ⟨α, γ, β, z, bz, hρ, hread⟩
  · exact Or.inl hf
  · exact Or.inr (bracket_of_samecard_window huwf hplay hρ hread)
```

### `nonforkBracketLocal_of_readBracket` - from `Orig2/Fork/Class/ForkReadBracket.lean`

```lean
/-- **READ-SAFE BRACKET IMPLIES THE LOCAL RESIDUAL.** -/
theorem nonforkBracketLocal_of_readBracket (h : ReadBracketElim) :
    NonforkBracketLocal := by
  intro u v ρ F huwf hsu hsv hplay hsplit
  rcases h u v ρ F huwf hsu hsv hplay hsplit with
    hf | ⟨α, γ, β, z, bz, P, Q, hρ, hα, hstep, hcan, hread⟩
  · exact Or.inl hf
  · have hPwf : P.WF := SatDifferCensus.ShufflePlayW.wf_end hα huwf
    have hQwf : Q.WF := step_wf hPwf hstep
    have hplayQ : ShufflePlayW Q (γ ++ Move.tabToFound z :: β) v :=
      bracket_landing_play hplay hρ hα hstep
    exact Or.inr ⟨α, γ, β, z, bz, P, Q, hρ, hα, hstep,
      raiseSwaps_of_read hQwf hplayQ hcan hread⟩
```

### `valleyElimNonfork_of_readBracket` - from `Orig2/Fork/Class/ForkReadBracket.lean`

```lean
/-- **THE CAMPAIGN REDUCTION FROM THE READ-SAFE BRACKET RESIDUAL.** -/
theorem valleyElimNonfork_of_readBracket (h : ReadBracketElim) :
    ValleyElimNonfork :=
  NonforkKit.valleyElimNonfork_of_local (nonforkBracketLocal_of_readBracket h)
```

### `splitPairRungEq_of_splitLivePair` - from `Orig2/Fork/Class/ForkTwinAt.lean`

```lean
/-- **`SplitPairRungEq` FROM THE LIVE PAIR** — both halves at once, since both
rungs are pinned to `c.rank.toIdx`.  No `SplitBlock`, no `SplitContainment`. -/
theorem splitPairRungEq_of_splitLivePair (hl : SplitKit.SplitLivePair) :
    SplitPairRungEq := by
  intro u v ρ F left right c d b pre post tail h
  obtain ⟨-, hSc, -, -⟩ := SplitKit.splitHyp_green h
  have htwin : CanRaiseS F c.twin :=
    canRaiseS_twin_of_livePair hSc
      (hl u v ρ F left right c d b pre post tail h)
  rw [rungAt_twin_eq_of_live htwin, canRaiseS_rung hSc]
```

### `splitTwinRungPin_of_splitLivePair` - from `Orig2/Fork/Class/ForkTwinAt.lean`

```lean
/-- The `nextUp`-form of the same statement (`TwinKit.SplitTwinRungPin`). -/
theorem splitTwinRungPin_of_splitLivePair (hl : SplitKit.SplitLivePair) :
    TwinKit.SplitTwinRungPin := by
  intro u v ρ F left right c d b pre post tail h
  obtain ⟨-, hSc, -, -⟩ := SplitKit.splitHyp_green h
  exact nextUp_twin_of_live (canRaiseS_twin_of_livePair hSc
    (hl u v ρ F left right c d b pre post tail h))
```

### `twinLiveAtBottom_of_splitLivePair` - from `Orig2/Fork/Class/ForkTwinAt.lean`

```lean
/-- `SplitLivePair` gives the bottom's twin liveness (the §2 case analysis,
read as a residual-level implication). -/
theorem twinLiveAtBottom_of_splitLivePair (hl : SplitKit.SplitLivePair) :
    SplitTwinLiveAtBottom :=
  fun u v ρ F left right c d b pre post tail h =>
    canRaiseS_twin_of_livePair (SplitKit.splitHyp_green h).2.1
      (hl u v ρ F left right c d b pre post tail h)
```

### `splitLivePair_iff_pairRungEq_of_block_containment` - from `Orig2/Fork/Class/ForkTwinAt.lean`

```lean
/-- **THE EXACT EQUIVALENCE.**  Given `SplitBlock` and `SplitContainment`, the
pair-rung residual and the live-pair residual are the same statement.  The
forward direction is this card's §2 (no hypotheses); the backward one is
`TwinKit.splitLivePair_of_block_containment_of_pin`. -/
theorem splitLivePair_iff_pairRungEq_of_block_containment
    (hb : SplitKit.SplitBlock) (hc : TwinKit.SplitContainment) :
    SplitKit.SplitLivePair ↔ SplitPairRungEq :=
  ⟨splitPairRungEq_of_splitLivePair,
    fun hr => TwinKit.splitLivePair_of_block_containment_of_pin hb hc
      (TwinKit.splitPairRungEq_iff_splitTwinRungPin.mp hr)⟩
```

### `satDifferForkWF_of_livePair_block_containment` - from `Orig2/Fork/Class/ForkTwinAt.lean`

```lean
/-- **THE CAMPAIGN WITHOUT THE PAIR-RUNG CLAUSE.**  `SplitBlock` +
`SplitContainment` + the live-pair residual + the choice-free shortest-play
interface give `SatDifferForkWF`.  (The pin is *derived*, not assumed.) -/
theorem satDifferForkWF_of_livePair_block_containment
    (hl : SplitKit.SplitLivePair) (hb : SplitKit.SplitBlock)
    (hc : TwinKit.SplitContainment)
    (hmin : ValleyElim.ShortestPlayExists) : SatDifferForkWF :=
  TwinKit.satDifferForkWF_of_block_containment_of_pairRungEq hb hc
    (splitPairRungEq_of_splitLivePair hl) hmin
```

### `splitLivePair_of_block_containment_of_pin` - from `Orig2/Fork/Class/ForkTwinLive.lean`

```lean
/-- **THE LIVE PAIR AT EVERY SPLIT.**  `SplitKit.SplitLivePair` from the same
three clauses: the pull card `c` is S-live and is the twin of the raise card
`d = c.twin`. -/
theorem splitLivePair_of_block_containment_of_pin
    (hb : SplitKit.SplitBlock) (hc : SplitContainment) (hp : SplitTwinRungPin) :
    SplitKit.SplitLivePair := by
  intro u v ρ F left right c d b pre post tail hh
  obtain ⟨-, hSc, hcanD, -⟩ := SplitKit.splitHyp_green hh
  have hblock : ¬ CanRaise F c := hb u v ρ F left right c d b pre post tail hh
  have hcont : ∀ e, CanRaiseS F e → e.suit = c.suit ∨ e.suit = c.twin.suit :=
    hc u v ρ F left right c d b pre post tail hh
  have hpin : F.nextUp c.twin = true := hp u v ρ F left right c d b pre post tail hh
  have htwin : CanRaiseS F c.twin :=
    canRaiseS_twin_of_block_containment hSc hblock hcont hpin hcanD
  have hd : d = c.twin :=
    raise_eq_twin_of_block_containment hSc hblock hcont (nextUp_true_iff.mp hpin) hcanD
  intro e
  rw [hd, card_twin_twin]
  constructor
  · intro he
    rcases hcont e he with hs | hs
    · exact Or.inr (Mech.live_eq_of_suit_left (canRaiseS_rung hSc) he hs)
    · exact Or.inl (Mech.live_eq_of_suit_twin (nextUp_true_iff.mp hpin) he hs)
  · rintro (h | h)
    · rw [h]; exact htwin
    · rw [h]; exact hSc
```

### `splitLivePair_of_mechanismResidual` - from `Orig2/Fork/Local/ForkMechanism.lean`

```lean
/-- `MechanismResidual` gives `SplitLivePair`. -/
theorem splitLivePair_of_mechanismResidual (h : MechanismResidual) :
    SplitKit.SplitLivePair := by
  intro u v ρ F left right c d b pre post tail hh
  exact (mechanism_yields hh (h u v ρ F left right c d b pre post tail hh)).2.1
```

### `dipPin_of_parts` - from `Orig2/Fork/Split/ForkDipPin.lean`

```lean
/-- **`SplitLivePair` + the gated residual give `DipPin`.**  `SplitLivePair`
supplies the bottom's spectrum; the fibre dichotomy gives a blocked
representative; the orbit chain `u → F₀ → F` puts it in `u`'s orbit. -/
theorem dipPin_of_parts (hl : SplitLivePair) (hd : BottomFibreBlock) : DipPin := by
  intro u v ρ F₀ left right c d b pre post tail h
  have hkeep := h
  obtain ⟨huwf, -, -, -, -, -, -, hleft, -, -, -, -⟩ := hkeep
  have hF₀ : F₀.WF := SatDifferCensus.ShufflePlayW.wf_end hleft huwf
  have hpair : TwinLivePair F₀ d := hl u v ρ F₀ left right c d b pre post tail h
  have hdata : FibreBlockData F₀ :=
    hd u v ρ F₀ left right c d b pre post tail h
  obtain ⟨F, z, hrev, hrung, hfork⟩ := forkWitness_of_data hF₀ hdata hpair
  obtain ⟨hspec, hpin⟩ := (forkWitness_iff F z).mp hfork
  have huF₀ : RevEqW u F₀ := shufflePlayW_revEqW hleft
  have huF : RevEqW u F := RevEqW_trans huF₀ hrev
  exact ⟨F, z, RevEqW_symm huF, hrung, hspec, hpin⟩
```

### `dipPin_of_bothRaisable` - from `Orig2/Fork/Split/ForkDipPin.lean`

```lean
/-- **THE RESIDUAL GIVES `DipPin`.** -/
theorem dipPin_of_bothRaisable (hl : SplitLivePair) (hd : BottomBothRaisableBlock) :
    DipPin :=
  dipPin_of_parts hl (bottomFibreBlock_of_bothRaisable hd)
```

### `dipPin_of_livePair_block` - from `Orig2/Fork/Split/ForkDipPin.lean`

```lean
/-- **THE ORIGINAL PINNED BOTTOM IMPLIES THE RESIDUAL.**  `SplitBlock` plus
`SplitLivePair` pin the pull card at the play's own bottom (`SplitTwin` turns it
into the raise card's twin), so the gated fibre dichotomy holds trivially and
`DipPin` is at most as hard as `SplitBlock`. -/
theorem dipPin_of_livePair_block (hl : SplitLivePair) (hb : SplitBlock) : DipPin := by
  intro u v ρ F₀ left right c d b pre post tail h
  have hkeep := h
  obtain ⟨huwf, -, -, -, -, -, -, hleft, -, -, -, -⟩ := hkeep
  have hF₀ : F₀.WF := SatDifferCensus.ShufflePlayW.wf_end hleft huwf
  have hpair : TwinLivePair F₀ d := hl u v ρ F₀ left right c d b pre post tail h
  have htwin : d = c.twin :=
    splitTwin_of_livePair_block hl hb u v ρ F₀ left right c d b pre post tail h
  have hblock : ¬ CanRaise F₀ c :=
    hb u v ρ F₀ left right c d b pre post tail h
  have hpin : ¬ CanRaise F₀ d.twin := by
    rw [htwin, card_twin_twin]
    exact hblock
  have huF₀ : RevEqW u F₀ := shufflePlayW_revEqW hleft
  exact ⟨F₀, d, RevEqW_symm huF₀, fun _ => rfl, hpair, hpin⟩
```

### `satDifferForkWF_of_bothRaisable_drainClosed` - from `Orig2/Fork/Split/ForkDipPin.lean`

```lean
/-- **THE CAMPAIGN CHAIN FROM THE RESIDUAL.**  `SplitLivePair` plus the gated
both-raisable block, plus the choice-free shortest-play interface. -/
theorem satDifferForkWF_of_bothRaisable_drainClosed
    (hl : SplitLivePair) (hd : BottomBothRaisableBlock)
    (hmin : ValleyElim.ShortestPlayExists) : SatDifferForkWF :=
  satDifferForkWF_of_dipPin (dipPin_of_bothRaisable hl hd) hmin
```

### `twinLivePair_at_F_of_splitLivePair` - from `Orig2/Fork/Split/ForkLanding.lean`

```lean
/-- The live pair at the bottom, with the pull card as pivot, from the
campaign's `SplitLivePair`.  The raise card `d` is live at the bottom, hence
the pull card `c` is one of `{d, d.twin}`; moving the pivot to the twin
preserves the live pair. -/
theorem twinLivePair_at_F_of_splitLivePair
    {u v : State} {ρ : List Move} {F : State}
    {left right : List Move} {c d : Card} {b : Base}
    {pre post tail : List Move}
    (hl : SplitKit.SplitLivePair)
    (h : SplitKit.SplitHyp u v ρ F left right c d b pre post tail) :
    TwinLivePair F c := by
  have hk := h
  obtain ⟨huwf, -, -, -, -, -, -, hleft, -, hshape, hfree, -⟩ := h
  have hd : TwinLivePair F d := hl u v ρ F left right c d b pre post tail hk
  have hcF : CanRaiseS F c := Bridge.bottom_pull_live huwf hleft hshape hfree
  rcases (hd c).mp hcF with hcd | hcd
  · subst hcd
    exact hd
  · subst hcd
    exact ThirdRigid.twinLivePair_twin hd
```

### `landing_parts_of_splitLivePair` - from `Orig2/Fork/Split/ForkLanding.lean`

```lean
/-- `SplitLivePair` gives both landing clauses. -/
theorem landing_parts_of_splitLivePair (hl : SplitKit.SplitLivePair) :
    LandingTwinLive ∧ LandingThirdSuitFree := by
  refine ⟨?_, ?_⟩
  · intro u v ρ F left right c d b pre post tail h A' B hpre hstep
    obtain ⟨hpost, hB⟩ := post_play_of_landing h hpre hstep
    have hk := h
    obtain ⟨-, -, -, -, -, -, -, -, -, -, hfree, -⟩ := h
    have htwin := twinLivePair_at_F_of_splitLivePair hl hk
    exact (Mech.canRaiseS_landing_iff hB hpost hfree c.twin).mpr
      ((htwin c.twin).mpr (Or.inr rfl))
  · intro u v ρ F left right c d b pre post tail h A' B hpre hstep e he h1 h2
    obtain ⟨hpost, hB⟩ := post_play_of_landing h hpre hstep
    have hk := h
    obtain ⟨-, -, -, -, -, -, -, -, -, -, hfree, -⟩ := h
    have htwin := twinLivePair_at_F_of_splitLivePair hl hk
    have heF : CanRaiseS F e :=
      (Mech.canRaiseS_landing_iff hB hpost hfree e).mp he
    rcases (htwin e).mp heF with h' | h'
    · exact h1 (congrArg Card.suit h')
    · exact h2 (congrArg Card.suit h')
```

### `splitLivePair_of_landing_parts` - from `Orig2/Fork/Split/ForkLanding.lean`

```lean
/-- Both landing clauses give `SplitLivePair`: transport the two clauses to
the bottom, use the landing rung pins to upgrade the suit containment to card
equality (`Mech.live_eq_of_suit_left` / `_twin`), and move the pivot to `d`. -/
theorem splitLivePair_of_landing_parts
    (ht : LandingTwinLive) (hf : LandingThirdSuitFree) :
    SplitKit.SplitLivePair := by
  intro u v ρ F left right c d b pre post tail h
  have hk := h
  obtain ⟨huwf, -, -, -, -, -, -, hleft, -, hshape, hfree, -⟩ := h
  obtain ⟨A', hpre, hrest⟩ :=
    ValleyElim.ShufflePlayW_split hleft pre (Move.foundToTab c b :: post) hshape
  have hA' : A'.WF := SatDifferCensus.ShufflePlayW.wf_end hpre huwf
  cases hrest with
  | @cons _ B _ _ _ hrev hstep hpost =>
      have hB : B.WF := step_wf hA' hstep
      have hcF : CanRaiseS F c := Bridge.bottom_pull_live huwf hleft hshape hfree
      have hctF : CanRaiseS F c.twin :=
        (Mech.canRaiseS_landing_iff hB hpost hfree c.twin).mp
          (ht u v ρ F left right c d b pre post tail hk A' B hpre hstep)
      have hrungBF : rungAt F c.suit = c.rank.toIdx := by
        rw [ValleyElim.rungAt_eq_of_free_play hpost hfree c.suit]
        exact Mech.rungAt_landing_eq hA' hstep
      have hrungTF : rungAt F c.twin.suit = c.rank.toIdx := by
        have h1 := canRaiseS_rung hctF
        rw [Card.twin_rank] at h1
        exact h1
      have hTwinC : TwinLivePair F c := by
        intro e
        constructor
        · intro he
          have heB : CanRaiseS B e :=
            (Mech.canRaiseS_landing_iff hB hpost hfree e).mpr he
          by_cases hs1 : e.suit = c.suit
          · exact Or.inl (Mech.live_eq_of_suit_left hrungBF he hs1)
          · by_cases hs2 : e.suit = c.twin.suit
            · exact Or.inr (Mech.live_eq_of_suit_twin hrungTF he hs2)
            · exact (hf u v ρ F left right c d b pre post tail hk A' B hpre hstep
                e heB hs1 hs2).elim
        · rintro (rfl | rfl)
          · exact hcF
          · exact hctF
      obtain ⟨-, -, -, hSFd⟩ := SplitKit.splitHyp_green hk
      rcases (hTwinC d).mp hSFd with hdc | hdc
      · subst hdc
        exact hTwinC
      · exact Mech.twinLivePair_of_eq_twin hTwinC hdc
```

### `landingAll_iff_splitLivePair` - from `Orig2/Fork/Split/ForkLanding.lean`

```lean
/-- **THE EXACT EQUIVALENCE.**  The landing live pair (over every split) is
exactly the campaign's `SplitKit.SplitLivePair`; there is no weaker local
landing statement. -/
theorem landingAll_iff_splitLivePair :
    LandingAll ↔ SplitKit.SplitLivePair := by
  constructor
  · intro h
    obtain ⟨ht, hf⟩ := landingAll_iff_parts.mp h
    exact splitLivePair_of_landing_parts ht hf
  · intro hl
    exact landingAll_iff_parts.mpr (landing_parts_of_splitLivePair hl)
```

### `splitLivePair_of_splitLandingResidual` - from `Orig2/Fork/Split/ForkLandingLocal.lean`

```lean
/-- **THE RESIDUAL IS EXACTLY `SplitLivePair`** (via
`Landing.landingAll_iff_splitLivePair`). -/
theorem splitLivePair_of_splitLandingResidual (h : SplitLandingResidual) :
    SplitKit.SplitLivePair :=
  Landing.landingAll_iff_splitLivePair.mp (landingAll_of_splitLandingResidual h)
```

### `splitLivePair_of_free_pre_twin` - from `Orig2/Fork/Split/ForkLandingLocal.lean`

```lean
/-- **THE CAMPAIGN THEOREM MODULO THE TWIN CLAUSE, WHEN `pre` IS FREE.** -/
theorem splitLivePair_of_free_pre_twin
    (hpre : ∀ (u v : State) (ρ : List Move) (F : State)
      (left right : List Move) (c d : Card) (b : Base)
      (pre post tail : List Move),
      SplitKit.SplitHyp u v ρ F left right c d b pre post tail →
      ∀ m ∈ pre, ValleyElim.FreeMove m)
    (htwin : SplitLandingTwin) : SplitKit.SplitLivePair :=
  splitLivePair_of_splitLandingResidual (splitLandingResidual_of_free_pre_twin hpre htwin)
```

### `dipPin_of_notBoth` - from `Orig2/Fork/Split/ForkPin.lean`

```lean
/-- **THE CAMPAIGN CHAIN FROM THE VACUITY.** -/
theorem dipPin_of_notBoth (hl : SplitLivePair) (h : BottomNotBothRaisable) :
    DipPin :=
  dipPin_of_bothRaisable hl (bottomBothRaisableBlock_of_notBoth h)
```

### `dipPin_of_splitBlock` - from `Orig2/Fork/Split/ForkPin.lean`

```lean
/-- **THE CAMPAIGN CHAIN FROM `SplitBlock`** (re-derived through the residual). -/
theorem dipPin_of_splitBlock (hl : SplitLivePair) (hb : SplitBlock) : DipPin :=
  dipPin_of_notBoth hl (bottomNotBoth_of_splitBlock hb)
```

### `satDifferForkWF_of_notBoth` - from `Orig2/Fork/Split/ForkPin.lean`

```lean
/-- **THE FULL CHAIN FROM THE VACUITY.** -/
theorem satDifferForkWF_of_notBoth (hl : SplitLivePair) (h : BottomNotBothRaisable)
    (hmin : ValleyElim.ShortestPlayExists) : SatDifferForkWF :=
  satDifferForkWF_of_bothRaisable_drainClosed hl
    (bottomBothRaisableBlock_of_notBoth h) hmin
```

### `splitTwin_of_livePair_block` - from `Orig2/Fork/Split/ForkSplitResidual.lean`

```lean
/-- **THE TWIN CLAUSE IS PROVED.**  From `TwinLivePair F d` (the live set
is exactly `{d, d.twin}`), the green `CanRaise F d` (the raise fires at
the bottom) and the block of `c`: `c` cannot be `d`, hence `c = d.twin`
and `d = c.twin`. -/
theorem splitTwin_of_livePair_block (hl : SplitLivePair) (hb : SplitBlock) :
    SplitTwin := by
  intro u v ρ F left right c d b pre post tail h
  obtain ⟨-, hSc, hcanD, -⟩ := splitHyp_green h
  rcases (hl u v ρ F left right c d b pre post tail h c).mp hSc with h' | h'
  · have hc : CanRaise F c := by rw [h']; exact hcanD
    exact absurd hc (hb u v ρ F left right c d b pre post tail h)
  · rw [h', card_twin_twin]
```

### `splitFloor_of_livePair_twin` - from `Orig2/Fork/Split/ForkSplitResidual.lean`

```lean
/-- **THE RANK FLOOR IS PROVED** — indeed, from the twin clause the live
pair's rank equals `c.rank`, so the floor holds with equality.  The floor
needs `SplitLivePair` plus `SplitTwin` (which is itself derived from
`SplitLivePair` + `SplitBlock` above). -/
theorem splitFloor_of_livePair_twin (hl : SplitLivePair) (ht : SplitTwin) :
    SplitFloor := by
  intro u v ρ F left right c d b pre post tail h e he
  have hdc : d.rank.toIdx = c.rank.toIdx := by
    rw [ht u v ρ F left right c d b pre post tail h, Card.twin_rank]
  rcases (hl u v ρ F left right c d b pre post tail h e).mp he with h' | h'
  · rw [h']
    omega
  · rw [h', Card.twin_rank]
    omega
```

### `splitResidualData_of_livePair_block` - from `Orig2/Fork/Split/ForkSplitResidual.lean`

```lean
/-- **THE STRICT REDUCTION (3 clauses → 2).**  `SplitLivePair` (the
bottom's live set is the raise card's twin pair) plus `SplitBlock` (the
pull card is blocked) implies the whole corrected residual: the twin
clause and the rank floor are *proved*, not assumed. -/
theorem splitResidualData_of_livePair_block (hl : SplitLivePair) (hb : SplitBlock) :
    SplitResidualData := by
  intro u v ρ F left right c d b pre post tail h
  have ht : SplitTwin := splitTwin_of_livePair_block hl hb
  exact ⟨ht u v ρ F left right c d b pre post tail h,
    hb u v ρ F left right c d b pre post tail h,
    splitFloor_of_livePair_twin hl ht u v ρ F left right c d b pre post tail h⟩
```

### `splitLivePair_of_fork` - from `Orig2/Fork/Split/ForkSplitResidual.lean`

```lean
/-- **THE FORK'S LIVE-SET HALF IS `SplitLivePair`** — the fork witness pins
the live set outright (`forkWitness_iff`,
`Orig2/Fork/Local/ForkCriticalPair.lean:50`). -/
theorem splitLivePair_of_fork (hf : SplitFork) : SplitLivePair := by
  intro u v ρ F left right c d b pre post tail h
  exact ((forkWitness_iff F d).mp (hf u v ρ F left right c d b pre post tail h)).1
```

### `splitFork_of_livePair_block` - from `Orig2/Fork/Split/ForkSplitResidual.lean`

```lean
/-- `SplitLivePair ∧ SplitBlock` yields the fork form: the live set is
exactly the twin pair and the blocked member is the pull card. -/
theorem splitFork_of_livePair_block (hl : SplitLivePair) (hb : SplitBlock) :
    SplitFork := by
  intro u v ρ F left right c d b pre post tail h
  have htwin : d = c.twin := splitTwin_of_livePair_block hl hb
    u v ρ F left right c d b pre post tail h
  have hdtc : d.twin = c := by rw [htwin, card_twin_twin]
  refine ⟨?_, ?_⟩
  · intro z
    exact (hl u v ρ F left right c d b pre post tail h z).symm
  · rw [hdtc]
    exact hb u v ρ F left right c d b pre post tail h
```

### `satDifferForkWF_of_livePair_block_drainClosed` - from `Orig2/Fork/Split/ForkSplitResidual.lean`

```lean
/-- The same chain from the two-clause form. -/
theorem satDifferForkWF_of_livePair_block_drainClosed
    (hl : SplitLivePair) (hb : SplitBlock) (hmin : ValleyElim.ShortestPlayExists) :
    SatDifferForkWF :=
  satDifferForkWF_of_splitResidualData_drainClosed
    (splitResidualData_of_livePair_block hl hb) hmin
```

### `satDifferForkWF_of_livePair_parts` - from `Orig2/Fork/Split/ForkTailCover.lean`

```lean
/-- **THE CAMPAIGN CHAIN FROM THE TWO GEOMETRIC HALVES.**  `SplitLivePair`
plus the two halves of the block clause (nonempty free tail, cover) plus the
choice-free shortest-play interface give `SatDifferForkWF`; the twin clause
and the rank floor are derived (`splitResidualData_of_livePair_block`), and
the drain is discharged (`Bridge.forkExistenceFromAsymmetry_drainClosed`). -/
theorem satDifferForkWF_of_livePair_parts
    (hl : SplitLivePair) (h1 : NoEmptyTail) (h2 : TailCovers)
    (hmin : ValleyElim.ShortestPlayExists) : SatDifferForkWF :=
  satDifferForkWF_of_livePair_block_drainClosed hl (splitBlock_of_parts h1 h2) hmin
```

### `nonforkBracketElim_of_local` - from `Orig2/Fork/Third/ForkNonfork.lean`

```lean
/-- **THE REDUCTION.**  `NonforkBracketLocal` implies the campaign's
`Elim.NonforkBracketElim`. -/
theorem nonforkBracketElim_of_local (h : NonforkBracketLocal) :
    Elim.NonforkBracketElim := by
  intro u v ρ F huwf hsu hsv hplay hsplit
  rcases h u v ρ F huwf hsu hsv hplay hsplit with
    hf | ⟨α, γ, β, z, bz, P, Q, hρ, hα, hstep, hsw⟩
  · exact Or.inl hf
  · exact Or.inr ⟨α, γ, β, z, bz, P, Q, hρ, hα, hstep,
      bracket_play_of_swaps hplay hρ hα hstep hsw⟩
```

### `valleyElimNonfork_of_local` - from `Orig2/Fork/Third/ForkNonfork.lean`

```lean
/-- **THE LOCAL RESIDUAL IMPLIES THE VALLEY ELIMINATION.**  Composing with
`Elim.valleyElimNonfork_of_nonforkBracket`. -/
theorem valleyElimNonfork_of_local (h : NonforkBracketLocal) :
    ValleyElimNonfork :=
  Elim.valleyElimNonfork_of_nonforkBracket (nonforkBracketElim_of_local h)
```



## Downstream vacuous users (2026-11-02)

### `splitTwin_of_valleyElim_block` - from `Orig2\Fork\Class\ForkLivePair.lean`

```lean
/-- **The same reduction for the twin clause**, routed through
`splitTwin_of_livePair_block`. -/
theorem splitTwin_of_valleyElim_block
    (helim : ValleyElim.ValleyElimNonfork) (hblock : SplitBlock) : SplitTwin :=
  splitTwin_of_livePair_block (splitLivePair_of_valleyElim helim) hblock
```

### `splitResidualData_of_valleyElim_postCommutes` - from `Orig2\Fork\Class\ForkLivePair.lean`

```lean
/-- **`SplitResidualData` FROM `ValleyElimNonfork` + THE COMMUTATION.**  This
is the sharpest capstone here: the live-pair clause needs only the existing
valley-elimination residual, and the block clause needs the single explicit
commutation premise that lets W3 cancel the same-card bracket. -/
theorem splitResidualData_of_valleyElim_postCommutes
    (helim : ValleyElim.ValleyElimNonfork) (hc : PostCommutesRaise) :
    SplitResidualData :=
  splitResidualData_of_livePair_block
    (splitLivePair_of_valleyElim helim)
    (splitBlock_of_valleyElim_postCommutes helim hc)
```

### `splitResidualData_of_valleyElim_block` - from `Orig2\Fork\Class\ForkLivePair.lean`

```lean
/-- **`SplitResidualData` FROM `ValleyElimNonfork` + `SplitBlock`.** -/
theorem splitResidualData_of_valleyElim_block
    (helim : ValleyElim.ValleyElimNonfork) (hblock : SplitBlock) :
    SplitResidualData :=
  splitResidualData_of_livePair_block (splitLivePair_of_valleyElim helim) hblock
```

### `splitResidualData_of_landing_block` - from `Orig2\Fork\Class\ForkLivePair.lean`

```lean
/-- **`SplitResidualData` FROM THE LOCAL LANDING RESIDUAL + `SplitBlock`.** -/
theorem splitResidualData_of_landing_block
    (hland : SplitLiveAtLanding) (hblock : SplitBlock) : SplitResidualData :=
  splitResidualData_of_livePair_block
    (splitLivePair_of_landing_block hland hblock) hblock
```

### `splitResidualData_of_mechanismResidual` - from `Orig2\Fork\Local\ForkMechanism.lean`

```lean
/-- `MechanismResidual` gives the corrected residual. -/
theorem splitResidualData_of_mechanismResidual (h : MechanismResidual) :
    SplitKit.SplitResidualData :=
  SplitKit.splitResidualData_of_livePair_block
    (splitLivePair_of_mechanismResidual h) (splitBlock_of_mechanismResidual h)
```

### `bottomDip_of_landing_block` - from `Orig2\Fork\Class\ForkLivePair.lean`

```lean
/-- The bridge residual from the landing-containment reduction. -/
theorem bottomDip_of_landing_block
    (hland : SplitLiveAtLanding) (hblock : SplitBlock) : Bridge.BottomDip :=
  bottomDip_of_splitResidualData (splitResidualData_of_landing_block hland hblock)
```

### `bottomDip_of_valleyElim_block` - from `Orig2\Fork\Class\ForkLivePair.lean`

```lean
/-- The bridge residual from the valley-elimination reduction. -/
theorem bottomDip_of_valleyElim_block
    (helim : ValleyElim.ValleyElimNonfork) (hblock : SplitBlock) :
    Bridge.BottomDip :=
  bottomDip_of_splitResidualData (splitResidualData_of_valleyElim_block helim hblock)
```

### `satDifferForkWF_of_valleyElim_postCommutes_drainClosed` - from `Orig2\Fork\Class\ForkLivePair.lean`

```lean
/-- **THE FULL CHAIN from `ValleyElimNonfork` + the commutation.** -/
theorem satDifferForkWF_of_valleyElim_postCommutes_drainClosed
    (helim : ValleyElim.ValleyElimNonfork) (hc : PostCommutesRaise)
    (hmin : ValleyElim.ShortestPlayExists) : SatDifferForkWF :=
  satDifferForkWF_of_splitResidualData_drainClosed
    (splitResidualData_of_valleyElim_postCommutes helim hc) hmin
```

### `satDifferForkWF_of_landing_block_drainClosed` - from `Orig2\Fork\Class\ForkLivePair.lean`

```lean
/-- **THE FULL CHAIN from the local landing residual + `SplitBlock`.** -/
theorem satDifferForkWF_of_landing_block_drainClosed
    (hland : SplitLiveAtLanding) (hblock : SplitBlock)
    (hmin : ValleyElim.ShortestPlayExists) : SatDifferForkWF :=
  satDifferForkWF_of_splitResidualData_drainClosed
    (splitResidualData_of_landing_block hland hblock) hmin
```

### `satDifferForkWF_of_valleyElim_block_drainClosed` - from `Orig2\Fork\Class\ForkLivePair.lean`

```lean
/-- **THE FULL CHAIN from `ValleyElimNonfork` + `SplitBlock`** (the drain is
discharged by `Bridge.forkExistenceFromAsymmetry_drainClosed`). -/
theorem satDifferForkWF_of_valleyElim_block_drainClosed
    (helim : ValleyElim.ValleyElimNonfork) (hblock : SplitBlock)
    (hmin : ValleyElim.ShortestPlayExists) : SatDifferForkWF :=
  satDifferForkWF_of_splitResidualData_drainClosed
    (splitResidualData_of_valleyElim_block helim hblock) hmin
```

### `bottomDip_of_valleyElim_postCommutes` - from `Orig2\Fork\Class\ForkLivePair.lean`

```lean
/-- The bridge residual from `ValleyElimNonfork` + the commutation. -/
theorem bottomDip_of_valleyElim_postCommutes
    (helim : ValleyElim.ValleyElimNonfork) (hc : PostCommutesRaise) :
    Bridge.BottomDip :=
  bottomDip_of_splitResidualData
    (splitResidualData_of_valleyElim_postCommutes helim hc)
```

### `satDifferForkWF_of_mechanismResidual_drainClosed` - from `Orig2\Fork\Local\ForkMechanism.lean`

```lean
/-- **THE FULL CHAIN FROM THE MECHANISM.**  The two local landing facts
(`LandingLivePair` + `CoverEvent`, bundled as `MechanismResidual`) plus the
choice-free shortest-play interface give `SatDifferForkWF`; the drain is
already discharged. -/
theorem satDifferForkWF_of_mechanismResidual_drainClosed
    (h : MechanismResidual) (hmin : ValleyElim.ShortestPlayExists) :
    SatDifferForkWF :=
  SplitKit.satDifferForkWF_of_splitResidualData_drainClosed
    (splitResidualData_of_mechanismResidual h) hmin
```

### `landingAll_of_valleyElim` - from `Orig2\Fork\Split\ForkLanding.lean`

```lean
/-- **THE LANDING LIVE PAIR FROM THE CAMPAIGN'S RESIDUAL.**  `ValleyElimNonfork`
already gives `SplitLivePair` (`LiveKit.splitLivePair_of_valleyElim`), hence
`LandingLivePair` at every pull landing, with no extra input. -/
theorem landingAll_of_valleyElim
    (helim : ValleyElim.ValleyElimNonfork) : LandingAll :=
  landingAll_iff_splitLivePair.mpr (LiveKit.splitLivePair_of_valleyElim helim)
```

### `twinLivePair_at_landing_of_valleyElim` - from `Orig2\Fork\Split\ForkLanding.lean`

```lean
/-- **THE LIVE-PAIR ITSELF AT THE LANDING.**  With the landing rung pin
(`Mech.rungAt_landing_eq`) and the pull card's vanilla raisability
(`ValleyStep.pull_card_canRaise`), `LandingLivePair` upgrades to
`TwinLivePair B c` (`Mech.twinLivePair_of_landing`).  Hence, from
`ValleyElimNonfork`, the landing's S-live set is exactly `{c, c.twin}`. -/
theorem twinLivePair_at_landing_of_valleyElim
    (helim : ValleyElim.ValleyElimNonfork) :
    ∀ (u v : State) (ρ : List Move) (F : State)
      (left right : List Move) (c d : Card) (b : Base)
      (pre post tail : List Move),
      SplitKit.SplitHyp u v ρ F left right c d b pre post tail →
      ∀ (A' B : State), ShufflePlayW u pre A' →
        State.step A' (Move.foundToTab c b) = some B →
        TwinLivePair B c := by
  intro u v ρ F left right c d b pre post tail h A' B hpre hstep
  have hk := h
  obtain ⟨huwf, -, -, -, -, -, -, -, -, -, -, -⟩ := h
  have hA' : A'.WF := SatDifferCensus.ShufflePlayW.wf_end hpre huwf
  exact Mech.twinLivePair_of_landing
    (ValleyStep.pull_card_canRaise hA' hstep)
    (Mech.rungAt_landing_eq hA' hstep)
    (landingAll_of_valleyElim helim u v ρ F left right c d b pre post tail hk
      A' B hpre hstep)
```

### `mechanismLivePair_of_valleyElim` - from `Orig2\Fork\Split\ForkLanding.lean`

```lean
/-- **`MechanismLivePair` from the campaign's residual.** -/
theorem mechanismLivePair_of_valleyElim
    (helim : ValleyElim.ValleyElimNonfork) : MechanismLivePair :=
  mechanismLivePair_iff_landingAll.mpr (landingAll_of_valleyElim helim)
```

### `satDifferForkWF_of_splitLanding_drainClosed` - from `Orig2\Fork\Split\ForkLandingLocal.lean`

```lean
/-- **THE FULL CHAIN FROM THIS CARD'S RESIDUAL.**  `SplitLandingResidual`
(the exact landing reduction) plus `SplitBlock` (the cover half) plus the
choice-free shortest-play interface give `SatDifferForkWF`. -/
theorem satDifferForkWF_of_splitLanding_drainClosed
    (hl : SplitLandingResidual) (hb : SplitKit.SplitBlock)
    (hmin : ValleyElim.ShortestPlayExists) : SatDifferForkWF :=
  Mech.satDifferForkWF_of_mechanismResidual_drainClosed
    (mechanismResidual_of_splitLanding_and_block hl hb) hmin
```

### `satDifferForkWF_of_block_containment_of_pin` - from `Orig2\Fork\Class\ForkTwinLive.lean`

```lean
/-- **THE CAMPAIGN FROM THREE CLAUSES.**  `SplitBlock` + `SplitContainment` +
`SplitTwinRungPin`, together with the choice-free shortest-play interface,
give `SatDifferForkWF`. -/
theorem satDifferForkWF_of_block_containment_of_pin
    (hb : SplitKit.SplitBlock) (hc : SplitContainment) (hp : SplitTwinRungPin)
    (hmin : ValleyElim.ShortestPlayExists) : SatDifferForkWF :=
  Mech.satDifferForkWF_of_mechanismResidual_drainClosed
    (mechanismResidual_of_block_containment_of_pin hb hc hp) hmin
```

### `satDifferForkWF_of_block_containment_of_pairRungEq` - from `Orig2\Fork\Class\ForkTwinLive.lean`

```lean
/-- **THE CAMPAIGN FROM THREE CLAUSES, IN LEDGER FORM** (with the
choice-free shortest-play interface). -/
theorem satDifferForkWF_of_block_containment_of_pairRungEq
    (hb : SplitKit.SplitBlock) (hc : SplitContainment) (hr : SplitPairRungEq)
    (hmin : ValleyElim.ShortestPlayExists) : SatDifferForkWF :=
  Mech.satDifferForkWF_of_mechanismResidual_drainClosed
    (mechanismResidual_of_block_containment_of_pairRungEq hb hc hr) hmin
```

### `satDifferForkWF_of_block_containment_of_ge_pin` - from `Orig2\Fork\Class\ForkPairRung.lean`

```lean
/-- The same in `TwinKit.SplitTwinRungPin` form (the campaign's own spelling). -/
theorem satDifferForkWF_of_block_containment_of_ge_pin
    (hb : SplitKit.SplitBlock) (hc : TwinKit.SplitContainment)
    (hg : SplitTwinRungGe) (hmin : ValleyElim.ShortestPlayExists) :
    SatDifferForkWF := by
  have hpair : SplitPairRungEq := splitPairRungEq_of_block_of_ge hb hg
  exact TwinKit.satDifferForkWF_of_block_containment_of_pin hb hc
    (splitPairRungEq_iff_splitTwinRungPin.mp hpair) hmin
```

### `satDifferForkWF_of_block_containment_of_ge` - from `Orig2\Fork\Class\ForkPairRung.lean`

```lean
/-- **THE CAMPAIGN FROM THE ONE-SIDED RESIDUAL** (with the choice-free
shortest-play interface). -/
theorem satDifferForkWF_of_block_containment_of_ge
    (hb : SplitKit.SplitBlock) (hc : TwinKit.SplitContainment)
    (hg : SplitTwinRungGe) (hmin : ValleyElim.ShortestPlayExists) :
    SatDifferForkWF :=
  TwinKit.satDifferForkWF_of_block_containment_of_pairRungEq hb hc
    (splitPairRungEq_of_block_of_ge hb hg) hmin
```

### `not_splitLivePair_of_corner` - from `Orig2\Fork\Class\ForkTwinAt.lean`

```lean
/-- **A CORNER SPLIT REFUTES THE CAMPAIGN'S LIVE PAIR.**  If any split's bottom
realised the corner, `SplitKit.SplitLivePair` would be false: the live pair
forces the raise card to be the twin (`splitTwin_of_livePair_block`), and at a
corner that card is not raisable.  So the residual is exactly load-bearing for
`SplitLivePair` — it is not a technicality. -/
theorem not_splitLivePair_of_corner (hb : SplitKit.SplitBlock)
    {u v : State} {ρ : List Move} {F : State} {left right : List Move}
    {c d : Card} {b : Base} {pre post tail : List Move}
    (hh : SplitKit.SplitHyp u v ρ F left right c d b pre post tail)
    (halone : TwinAlone F c) : ¬ SplitKit.SplitLivePair := by
  intro hl
  exact corner_split_raise_ne_twin hh halone
    (SplitKit.splitTwin_of_livePair_block hl hb u v ρ F left right c d b pre post tail hh)
```

### `satDifferForkWF_of_pin_only` - from `Orig2\Fork\Class\ForkTwinAt.lean`

```lean
/-- **THE CAMPAIGN NEEDS ONLY THE PIN.**  `SplitBlock` + `SplitContainment` +
`SplitTwinRungPin` + the shortest-play interface already give
`SatDifferForkWF` (`TwinKit.satDifferForkWF_of_block_containment_of_pin`,
`Orig2/Fork/Class/ForkTwinLive.lean:515`).  So `SplitTwinSited` — the only clause of the
target that is not already the pin (`twinLive_iff_pin_and_sited`) — is consumed
only by the *stronger* residual `SplitKit.SplitLivePair`
(`not_splitLivePair_of_corner`), not by the campaign assembly. -/
theorem satDifferForkWF_of_pin_only (hb : SplitKit.SplitBlock)
    (hc : SplitContainment) (hpin : SplitTwinRungPin)
    (hmin : ValleyElim.ShortestPlayExists) : SatDifferForkWF :=
  TwinKit.satDifferForkWF_of_block_containment_of_pin hb hc hpin hmin
```

### `satDifferForkWF_of_valleyElim_block_containment` - from `Orig2\Fork\Class\ForkTwinAt.lean`

```lean
/-- The same from the repository's valley-elimination residual. -/
theorem satDifferForkWF_of_valleyElim_block_containment
    (helim : ValleyElim.ValleyElimNonfork) (hb : SplitKit.SplitBlock)
    (hc : TwinKit.SplitContainment)
    (hmin : ValleyElim.ShortestPlayExists) : SatDifferForkWF :=
  satDifferForkWF_of_livePair_block_containment
    (LiveKit.splitLivePair_of_valleyElim helim) hb hc hmin
```

### `splitPairRungEq_of_valleyElim` - from `Orig2\Fork\Class\ForkTwinAt.lean`

```lean
/-- **THE PIN FROM `ValleyElimNonfork`.**  The repository's valley-elimination
residual already yields `SplitLivePair` (`LiveKit.splitLivePair_of_valleyElim`),
so it yields the pair-rung equality too. -/
theorem splitPairRungEq_of_valleyElim (h : ValleyElim.ValleyElimNonfork) :
    SplitPairRungEq :=
  splitPairRungEq_of_splitLivePair (LiveKit.splitLivePair_of_valleyElim h)
```

