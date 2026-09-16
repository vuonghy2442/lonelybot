import Klondike.TwinBridge

/-!
# The merge's re-firing — the guards-survival across the schedules

The firing-half of the double-clear schedule's re-firing premise,
by schedule shape: State.merge_refires_clean (the CleanStack
column-run, moved here from TwinBridge for iteration speed) and —
incoming — State.merge_refires_mixed (the CleanStack prefix plus
the z'-detour, the landing riding along; the contains-guard via the
walk-entry kit: Board.RunChain + Board.aboveOf_run_root_of_chain +
Board.aboveOf_card_base, all in TwinQuotient).  With these, the
mixed consumers' re-firing reduces to the source firing + the
schedule's own premises. -/

/-- **The merge's guards survive the CleanStack column-run**: a firing
merge at the source re-fires at the cleared state, provided the run's
stacked cards stay off the merge's touch-set (the root `c`, and the
landing base's card `d` when the landing is a card base) — the run's
moves are detach-only `pileStack`s, so the root's base, the landing
base's freeness, and the landing card's visibility are carried
verbatim, and the run-walk only shrinks (`aboveOf_shrink_run`).  This
derives the FIRING half of the double-clear schedule's re-firing
premise; the successor's window-solvability (the L1/O0 transfer) is
the other half. -/
theorem State.merge_refires_clean {st S₀ : State} {c : Card} {b : Base}
    {π : List Move} {a₁ : State}
    (hrun : st.run π = some S₀)
    (hkind : ∀ m ∈ π, ∃ q : Card, m = Move.pileStack q)
    (hoff : ∀ q : Card, Move.pileStack q ∈ π →
      q ≠ c ∧ ∀ d : Card, b = Sum.inr d → q ≠ d)
    (hstep : st.apply (Move.pilePile c b) = some a₁) :
    ∃ a₁' : State, S₀.apply (Move.pilePile c b) = some a₁' := by
  -- the source firing's shape
  have hP := hstep
  rw [apply_pilePile_iff] at hP
  obtain ⟨β₀, hbotβ, hneβ, hcmr, -, -⟩ := hP
  -- the source guards, unpacked per landing shape
  have htopb : st.board.topOf b = none := by
    cases b with
    | inl a =>
        have h2 := canMoveRun_inl_iff.mp hcmr
        rw [canPlace_inl_iff] at h2
        exact h2.1
    | inr d =>
        have h2 := canMoveRun_inr_iff.mp hcmr
        rw [canPlace_inr_iff] at h2
        exact h2.1.1
  have hisvd : ∀ d : Card, b = Sum.inr d → st.isVis d = true ∧ canSitOn c d = true := by
    intro d hb
    have h := hcmr
    rw [hb, canMoveRun_inr_iff] at h
    obtain ⟨hcp, -⟩ := h
    rw [canPlace_inr_iff] at hcp
    exact ⟨hcp.2.1, hcp.2.2⟩
  have hcont : ∀ d : Card, b = Sum.inr d → d ∉ st.board.aboveOf c := by
    intro d hb hmem
    have h := hcmr
    rw [hb, canMoveRun_inr_iff] at h
    obtain ⟨-, hnc⟩ := h
    rw [List.contains_iff_mem.mpr hmem] at hnc
    simp at hnc
  -- the carried invariant, by induction over the run
  have key : ∀ (π' : List Move) (S T : State), S.run π' = some T →
      (∀ m ∈ π', ∃ q : Card, m = Move.pileStack q) →
      (∀ q : Card, Move.pileStack q ∈ π' →
        q ≠ c ∧ ∀ d : Card, b = Sum.inr d → q ≠ d) →
      S.board.bottomOf c = some β₀ ∧ S.board.topOf b = none ∧
      (∀ d : Card, b = Sum.inr d → S.isVis d = true) →
      T.board.bottomOf c = some β₀ ∧ T.board.topOf b = none ∧
      (∀ d : Card, b = Sum.inr d → T.isVis d = true) := by
    intro π'
    induction π' with
    | nil =>
        intro S T hrun _ _ hINV
        obtain rfl := run_nil_elim hrun
        exact hINV
    | cons m rest ih =>
        intro S T hrun hkind' hoff' hINV
        obtain ⟨q, hq⟩ := hkind' m (by simp)
        rw [hq] at hrun
        obtain ⟨R, hm, hrest⟩ := run_cons_elim hrun
        have hqc := (hoff' q (by simp [hq])).1
        have hqd : ∀ d : Card, b = Sum.inr d → q ≠ d :=
          fun d hb => (hoff' q (by simp [hq])).2 d hb
        obtain ⟨hbotS', htopbS', hisvS'⟩ := hINV
        -- the step's firing shape: the detach at q's own base
        have hf := hm
        rw [apply_pileStack_iff] at hf
        obtain ⟨-, bq, hbq, -, hR⟩ := hf
        have htopq : S.board.topOf bq = some q := (Board.bottomOf_eq S.board q bq).mp hbq
        -- the invariant at the step's successor
        have hbotR : R.board.bottomOf c = some β₀ := by
          rw [hR]; show (S.board.detach bq).bottomOf c = some β₀
          rw [bottomOf_detach_ne htopq (Ne.symm hqc)]
          exact hbotS'
        have htopbR : R.board.topOf b = none := by
          rw [hR]; show (S.board.detach bq).topOf b = none
          have hbne : b ≠ bq := by
            intro hcon
            rw [hcon] at htopbS'
            exact absurd htopq (by rw [htopbS']; simp)
          rw [Board.detach_topOf_ne _ _ _ hbne]
          exact htopbS'
        have hisvR : ∀ d : Card, b = Sum.inr d → R.isVis d = true := by
          intro d hb
          rw [hR]; show ((S.board.detach bq).bottomOf d).isSome = true
          have hdq : d ≠ q := fun hcon => hqd d hb hcon.symm
          rw [bottomOf_detach_ne htopq hdq]
          exact hisvS' d hb
        exact ih R T hrest (fun m' hm' => hkind' m' (List.mem_cons_of_mem _ hm'))
          (fun q' hq' => hoff' q' (List.mem_cons_of_mem _ hq'))
          ⟨hbotR, htopbR, hisvR⟩
  obtain ⟨hbotS, htopbS, hisvS⟩ :=
    key π st S₀ hrun hkind (fun q hq => hoff q hq)
      ⟨hbotβ, htopb, fun d hb => (hisvd d hb).1⟩
  -- the walk only shrinks along the run
  have hshrink : ∀ y ∈ S₀.board.aboveOf c, y ∈ st.board.aboveOf c :=
    State.aboveOf_shrink_run c π st S₀ hrun hkind
  -- the guards reassemble
  have hcmrS : S₀.canMoveRun c b = true := by
    cases b with
    | inl a =>
        rw [canMoveRun_inl_iff, canPlace_inl_iff]
        have h2 := canMoveRun_inl_iff.mp hcmr
        rw [canPlace_inl_iff] at h2
        exact ⟨htopbS, h2.2⟩
    | inr d =>
        rw [canMoveRun_inr_iff, canPlace_inr_iff]
        refine ⟨⟨htopbS, hisvS d rfl, (hisvd d rfl).2⟩, ?_⟩
        show (S₀.board.aboveOf c).contains d = false
        by_cases hmem : d ∈ S₀.board.aboveOf c
        · exact absurd (hshrink d hmem) (hcont d rfl)
        · cases hcon : (S₀.board.aboveOf c).contains d with
          | false => rfl
          | true => exact absurd (List.contains_iff_mem.mp hcon) hmem
  -- the attach succeeds: the landing is free, the root unplaced after
  -- its own detach
  have hatt : (S₀.board.detach β₀).attach b c ≠ none := by
    rw [Board.attach_eq_some_iff]
    constructor
    · rw [Board.detach_topOf_ne _ _ _ (Ne.symm hneβ)]
      exact htopbS
    · exact Board.bottomOf_detach_self
        ((Board.bottomOf_eq S₀.board c β₀).mp hbotS)
  obtain ⟨bd', hatt'⟩ : ∃ bd', (S₀.board.detach β₀).attach b c = some bd' := by
    cases hA : (S₀.board.detach β₀).attach b c with
    | none => exact absurd hA hatt
    | some bd' => exact ⟨bd', rfl⟩
  refine ⟨{ S₀ with board := bd' }, ?_⟩
  rw [apply_pilePile_iff]
  exact ⟨β₀, hbotS, hneβ, hcmrS, bd', hatt', rfl⟩

