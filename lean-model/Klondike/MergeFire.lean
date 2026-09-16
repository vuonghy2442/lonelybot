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
  have hatt₀ : (S₀.board.detach β₀).attach b c ≠ none := by
    rw [Board.attach_eq_some_iff]
    constructor
    · rw [Board.detach_topOf_ne _ _ _ (Ne.symm hneβ)]
      exact htopbS
    · exact Board.bottomOf_detach_self
        ((Board.bottomOf_eq S₀.board c β₀).mp hbotS)
  obtain ⟨bd', hatt₀'⟩ : ∃ bd', (S₀.board.detach β₀).attach b c = some bd' := by
    cases hA : (S₀.board.detach β₀).attach b c with
    | none => exact absurd hA hatt₀
    | some bd' => exact ⟨bd', rfl⟩
  refine ⟨{ S₀ with board := bd' }, ?_⟩
  rw [apply_pilePile_iff]
  exact ⟨β₀, hbotS, hneβ, hcmrS, bd', hatt₀', rfl⟩

/-- **The merge's guards survive the MIXED schedule** (the CleanStack
prefix + the z'-detour, `exchangeDoubleClear_of_sched_mixed`'s shape):
a firing merge at the source re-fires at the detoured state.  The
CleanStack segment's transfer is `merge_refires_clean` verbatim; the
DETOUR segment's: the root's base survives (`apply_pilePile_bottomOf`,
`r₁ ≠ c`), the landing base's freeness survives (the two edited seats
are the detour's own — both excluded by `hβne`/the firing's shape),
the landing card's visibility survives (re-seated within the moved
run — its base is either the run's internal seat, untouched, or, for
`d = r₁`-adjacent shapes, excluded by `hr₁card`).  The
CONTAINS-GUARD is the walk-ENTRY argument: a card entering the merge
root's walk from the re-homed run forces the run's root in
(`aboveOf_run_root_of_chain`), whose base card is then the detour's
landing (`aboveOf_card_base_of_mem` + the seat's uniqueness) — and
the landing card is off the merge root's walk and the run by
`hβcard`.  This derives the FIRING half of the mixed schedule's
re-firing premise; the successor's window-solvability (L1/O0)
remains the other half. -/
theorem State.merge_refires_mixed {st Sₛ S₀ : State} {c r₁ : Card} {b β : Base}
    {πₛ : List Move} {a₁ : State} {run : List Card}
    (hrunₛ : st.run πₛ = some Sₛ)
    (hkindₛ : ∀ m ∈ πₛ, ∃ q : Card, m = Move.pileStack q)
    (hoffₛ : ∀ q : Card, Move.pileStack q ∈ πₛ →
      q ≠ c ∧ ∀ d : Card, b = Sum.inr d → q ≠ d)
    (hstep : st.apply (Move.pilePile c b) = some a₁)
    (hdetour : Sₛ.apply (Move.pilePile r₁ β) = some S₀)
    (hr₁ne : r₁ ≠ c)
    (hβne : β ≠ b)
    (hself : β ≠ Sum.inr r₁)
    (hr₁card : ∀ d : Card, b = Sum.inr d → r₁ ≠ d)
    (hβcard : ∀ y : Card, β = Sum.inr y → y ≠ c ∧
      y ∉ Sₛ.board.aboveOf c ∧ y ∉ Sₛ.board.aboveOf r₁)
    (hc₀ : c ∉ S₀.board.aboveOf r₁)
    (hchain : S₀.board.RunChain r₁ run)
    (hride : ∀ d : Card, b = Sum.inr d → d = r₁ ∨ d ∈ run) :
    ∃ a₁' : State, S₀.apply (Move.pilePile c b) = some a₁' := by
  -- part 1: the clean firing at the schedule's intermediate state
  obtain ⟨aₛ, hfireₛ⟩ := State.merge_refires_clean hrunₛ hkindₛ hoffₛ hstep
  -- part 2: the firing's guards at Sₛ
  have hP := hfireₛ
  rw [apply_pilePile_iff] at hP
  obtain ⟨β₀, hbotβ, hneβ, hcmr, -, -⟩ := hP
  have htopb : Sₛ.board.topOf b = none := by
    cases b with
    | inl a =>
        have h2 := canMoveRun_inl_iff.mp hcmr
        rw [canPlace_inl_iff] at h2
        exact h2.1
    | inr d =>
        have h2 := canMoveRun_inr_iff.mp hcmr
        rw [canPlace_inr_iff] at h2
        exact h2.1.1
  have hisvd : ∀ d : Card, b = Sum.inr d → Sₛ.isVis d = true ∧ canSitOn c d = true := by
    intro d hb
    have h := hcmr
    rw [hb, canMoveRun_inr_iff] at h
    obtain ⟨hcp, -⟩ := h
    rw [canPlace_inr_iff] at hcp
    exact ⟨hcp.2.1, hcp.2.2⟩
  have hcont : ∀ d : Card, b = Sum.inr d → d ∉ Sₛ.board.aboveOf c := by
    intro d hb hmem
    have h := hcmr
    rw [hb, canMoveRun_inr_iff] at h
    obtain ⟨-, hnc⟩ := h
    have hmem' : (Sₛ.board.aboveOf c).contains d = true :=
      List.contains_iff_mem.mpr hmem
    rw [hmem'] at hnc
    simp at hnc
  -- part 3: the detour's shape (S₀ kept abstract; the board equation
  -- for the attach-side lemmas)
  have hD := hdetour
  rw [apply_pilePile_iff] at hD
  obtain ⟨b₀, hbotr, hne₀, hcmr₀, bd₀, hatt₀, hS₀⟩ := hD
  have hSb : S₀.board = bd₀ := by rw [hS₀]
  -- part 4: the root's base survives the detour
  have hbotS : S₀.board.bottomOf c = some β₀ := by
    rw [State.apply_pilePile_bottomOf hdetour (Ne.symm hr₁ne)]
    exact hbotβ
  -- part 5: the landing base's freeness survives
  have htopbS : S₀.board.topOf b = none := by
    rw [hSb]
    have hbβ : b ≠ β := fun hcon => hβne hcon.symm
    have h1 : bd₀.topOf b = (Sₛ.board.detach b₀).topOf b :=
      Board.attach_topOf_ne _ _ _ hatt₀ hbβ
    by_cases hbb : b = b₀
    · rw [h1, hbb, Board.detach_topOf]
    · rw [h1, Board.detach_topOf_ne _ _ _ hbb]
      exact htopb
  -- part 6: the landing card's visibility survives
  have hisvS : ∀ d : Card, b = Sum.inr d → S₀.isVis d = true ∧ canSitOn c d = true := by
    intro d hb
    have hd : d ≠ r₁ := fun hcon => hr₁card d hb hcon.symm
    have hbotd : S₀.board.bottomOf d = Sₛ.board.bottomOf d :=
      State.apply_pilePile_bottomOf hdetour hd
    exact ⟨by
        show (S₀.board.bottomOf d).isSome = true
        rw [hbotd]
        exact (hisvd d hb).1,
      (hisvd d hb).2⟩
  -- part 7: the contains-guard — the walk-entry argument
  have hcontS : ∀ d : Card, b = Sum.inr d → d ∉ S₀.board.aboveOf c := by
    intro d hb hmem
    rw [hSb] at hmem hchain hc₀
    rcases Board.mem_aboveOf_attach hatt₀ hmem with h1 | h2 | h3
    · exact hcont d hb (Board.aboveOf_sub_detach 52 c [] d h1)
    · exact hr₁card d hb h2.symm
    · -- the landing rides the run: the walk entered it — at the root
      have hr₁c : r₁ ∈ bd₀.aboveOf c :=
        Board.aboveOf_run_root_of_chain run d hchain (hride d hb) hmem hr₁ne hc₀
      -- the run's root sits on a card — and the seat is the detour's
      -- landing (the attach's own seat, by the board's injectivity)
      obtain ⟨u, hu⟩ := Board.aboveOf_card_base_of_mem hr₁c
      have hβu : β = Sum.inr u := by
        have h1 : bd₀.topOf β = some r₁ := Board.attach_topOf _ _ _ hatt₀
        exact bd₀.inj β (Sum.inr u) r₁ h1 hu
      rcases Board.aboveOf_pred hu hr₁c with h4 | h4
      · exact (hβcard u hβu).1 h4
      · rcases Board.mem_aboveOf_attach hatt₀ h4 with h5 | h6 | h7
        · exact (hβcard u hβu).2.1 (Board.aboveOf_sub_detach 52 c [] u h5)
        · exact hself (hβu.trans (congrArg Sum.inr h6))
        · exact (hβcard u hβu).2.2 (Board.aboveOf_sub_detach 52 r₁ [] u h7)
  -- part 8: the guards reassemble
  have hcmrS : S₀.canMoveRun c b = true := by
    cases b with
    | inl a =>
        rw [canMoveRun_inl_iff, canPlace_inl_iff]
        have h2 := canMoveRun_inl_iff.mp hcmr
        rw [canPlace_inl_iff] at h2
        exact ⟨htopbS, h2.2⟩
    | inr d =>
        rw [canMoveRun_inr_iff, canPlace_inr_iff]
        obtain ⟨hvis, hcs⟩ := hisvS d rfl
        refine ⟨⟨htopbS, hvis, hcs⟩, ?_⟩
        show (S₀.board.aboveOf c).contains d = false
        cases hcon : (S₀.board.aboveOf c).contains d with
        | false => rfl
        | true => exact absurd (List.contains_iff_mem.mp hcon) (hcontS d rfl)
  -- part 9: the final attach + the iff
  have hattfin : (S₀.board.detach β₀).attach b c ≠ none := by
    rw [Board.attach_eq_some_iff]
    constructor
    · have htopq : S₀.board.topOf β₀ = some c :=
        (Board.bottomOf_eq S₀.board c β₀).mp hbotS
      rw [Board.detach_topOf_ne _ _ _ (Ne.symm hneβ)]
      exact htopbS
    · exact Board.bottomOf_detach_self
        ((Board.bottomOf_eq S₀.board c β₀).mp hbotS)
  obtain ⟨bd', hatt'⟩ : ∃ bd', (S₀.board.detach β₀).attach b c = some bd' := by
    cases hA : (S₀.board.detach β₀).attach b c with
    | none => exact absurd hA hattfin
    | some bd' => exact ⟨bd', rfl⟩
  refine ⟨{ S₀ with board := bd' }, ?_⟩
  rw [apply_pilePile_iff]
  exact ⟨β₀, hbotS, hneβ, hcmrS, bd', hatt', rfl⟩

/-- **The board only gets cleaner** (the user's "clearVis"): every
WONKY edge at a move's successor — a visible-base edge violating the
chaining rule — already existed, identically, at the source.  An
edge's wonkiness is immutable while it persists (`canSitOn` is
card-level); the only transitions are destroy-and-recreate, and
every re-creation on a visible base is a placement, which is
`canSitOn`-guarded.  The one wonky-creator — the reveal, seating
the boundary card on its hidden under-card — creates only on HIDDEN
bases (excluded here by the visibility premise, `vis_not_hidden`),
and a hidden base's own promotion to visibility requires its seat
vacated (the bare rule): no wonky edge ever survives into
visibility.  Wonky → correct (by replacement), never the reverse.

The run-level consequence: the wonky set only shrinks along plays —
every wonky edge at any state descends, unchanged, from the
source's (the "old money" property).  With `merge_rank_arith` (the
merge run ascends two ranks) this grades the merge case: a live
merge needs ≥1 wonky edge in its run, and those edges are old
money — consumable by the repairs, never replenished. -/
theorem State.wonky_sub {st st' : State} {m : Move}
    (hwf : st.WF) (h : st.apply m = some st') :
    ∀ (x y : Card), st'.board.topOf (Sum.inr y) = some x →
      st'.isVis y = true → canSitOn x y = false →
      st.board.topOf (Sum.inr y) = some x ∧ st.isVis y = true := by
  intro x y htop' hvis' hwonky
  cases m with
  | draw =>
      rw [apply_draw_iff] at h
      obtain rfl := h
      exact ⟨htop', hvis'⟩
  | deckStack q =>
      rw [apply_deckStack_iff] at h
      obtain ⟨-, -, rfl⟩ := h
      exact ⟨htop', hvis'⟩
  | pileStack q =>
      rw [apply_pileStack_iff] at h
      obtain ⟨-, b, hbq, -, rfl⟩ := h
      have htopb : st.board.topOf b = some q :=
        (Board.bottomOf_eq st.board q b).mp hbq
      change (st.board.detach b).topOf (Sum.inr y) = some x at htop'
      change ((st.board.detach b).bottomOf y).isSome = true at hvis'
      by_cases hbb : b = Sum.inr y
      · rw [hbb, Board.detach_topOf] at htop'
        exact absurd htop' (by simp)
      · rw [Board.detach_topOf_ne _ _ _ (Ne.symm hbb)] at htop'
        have hyq : y ≠ q := by
          intro hcon
          have hnone : (st.board.detach b).bottomOf q = none :=
            Board.bottomOf_detach_self htopb
          rw [hcon] at hvis'
          rw [hnone] at hvis'
          exact absurd hvis' (by simp)
        exact ⟨htop', by
          show (st.board.bottomOf y).isSome = true
          rw [← bottomOf_detach_ne htopb hyq]
          exact hvis'⟩
  | reveal a =>
      have hstep := h
      rw [apply_reveal_iff] at h
      obtain ⟨r, bd, htoph, hbare, hatt, hS⟩ := h
      have hSb : st'.board = bd := by rw [hS]
      have hSd : st'.depths a = st.depths a - 1 := by rw [hS]; simp
      rw [hSb] at htop'
      change (st'.board.bottomOf y).isSome = true at hvis'
      rw [hSb] at hvis'
      by_cases hbb : st.hiddenBase a = Sum.inr y
      · -- the new edge: the base is the hidden under-card — never visible
        obtain ⟨pre, hpre⟩ := hiddenBase_split hbb htoph
        have hdpy : st.depths a = pre.length + 2 := by
          have h1 : (st.hidden a).length = st.depths a := by
            show ((st.deal.piles a).take (st.depths a)).length = st.depths a
            rw [List.length_take]
            have := hwf.depths_le a
            omega
          rw [hpre] at h1
          simp at h1
          omega
        have hmem : y ∈ st'.hidden a := by
          show y ∈ (st'.deal.piles a).take (st'.depths a)
          rw [show st'.deal = st.deal from by rw [hS], hSd]
          rw [show st.hidden a = (st.deal.piles a).take (st.depths a) from rfl] at hpre
          have hsplit : st.deal.piles a = pre ++ [y, r] ++
              (st.deal.piles a).drop (st.depths a) := by
            rw [← hpre]
            exact (List.take_append_drop _ _).symm
          rw [hsplit, hdpy, List.take_append, List.take_append]
          simp
        have hnv : st'.isVis y = false := by
          cases hc : st'.isVis y with
          | false => rfl
          | true => exact absurd hmem ((apply_wf hwf _ _ hstep).vis_not_hidden y hc a)
        have hcontrad : (bd.bottomOf y).isSome = false := by
          rw [← hSb]
          exact hnv
        rw [hcontrad] at hvis'
        exact Bool.noConfusion hvis'
      · -- a preserved edge: the seat is untouched by the attach
        have hne : (Sum.inr y : Base) ≠ st.hiddenBase a :=
          fun hcon => hbb hcon.symm
        rw [Board.attach_topOf_ne _ _ _ hatt hne] at htop'
        by_cases hyr : y = r
        · rw [hyr] at htop'
          exact absurd htop' (by rw [hbare]; simp)
        · exact ⟨htop', by
            show (st.board.bottomOf y).isSome = true
            rw [← bottomOf_attach_ne hatt hyr]
            exact hvis'⟩
  | deckPile c b =>
      rw [apply_deckPile_iff] at h
      obtain ⟨hprev, hcp, bd, hatt, rfl⟩ := h
      change bd.topOf (Sum.inr y) = some x at htop'
      change (bd.bottomOf y).isSome = true at hvis'
      by_cases hbb : b = Sum.inr y
      · -- the new edge: placement-guarded — never wonky
        have hxc : x = c := by
          have h1 : bd.topOf b = some c := Board.attach_topOf _ _ _ hatt
          rw [hbb] at h1
          exact Option.some.inj (htop'.symm.trans h1)
        rw [hxc] at hwonky
        rw [hbb] at hcp
        rw [canPlace_inr_iff] at hcp
        exact Bool.noConfusion (hcp.2.2.symm.trans hwonky)
      · have hne : (Sum.inr y : Base) ≠ b := fun hcon => hbb hcon.symm
        rw [Board.attach_topOf_ne _ _ _ hatt hne] at htop'
        by_cases hyc : y = c
        · -- the fresh card came from the stock: it hosts no edges
          rw [hyc] at htop' ⊢
          have hcmem : c ∈ st.stock.cards := by
            simp only [Cycle.prev] at hprev
            split at hprev
            · exact absurd hprev (by simp)
            · exact List.mem_iff_getElem?.mpr
                ⟨st.stock.cursor - 1, by simpa using hprev⟩
          have hnvis : st.isVis c = false := by
            cases hc : st.isVis c with
            | false => rfl
            | true =>
                have hnone := hwf.vis_off_cycle c hc
                exact absurd hnone (Cycle.posOf_ne_none_of_mem hcmem)
          have hnvis' : (st.board.bottomOf c).isSome = false := hnvis
          have hnb : st.board.bottomOf c = none := by
            cases hb : st.board.bottomOf c with
            | none => rfl
            | some b' =>
                rw [hb] at hnvis'
                exact absurd hnvis' (by simp)
          have hnh : ∀ a, c ∉ st.hidden a := by
            intro a hcm
            exact Deal.piles_stock_disj hwf.deal_wf
              (List.take_subset _ _ hcm) ((hwf.stock_wf).2 c hcmem)
          exact absurd htop' (by rw [State.topOf_inr_eq_none hwf hnb hnh]; simp)
        · exact ⟨htop', by
            show (st.board.bottomOf y).isSome = true
            rw [← bottomOf_attach_ne hatt hyc]
            exact hvis'⟩
  | stackPile c b =>
      rw [apply_stackPile_iff] at h
      obtain ⟨hrk, hcp, bd, hatt, rfl⟩ := h
      change bd.topOf (Sum.inr y) = some x at htop'
      change (bd.bottomOf y).isSome = true at hvis'
      by_cases hbb : b = Sum.inr y
      · have hxc : x = c := by
          have h1 : bd.topOf b = some c := Board.attach_topOf _ _ _ hatt
          rw [hbb] at h1
          exact Option.some.inj (htop'.symm.trans h1)
        rw [hxc] at hwonky
        rw [hbb] at hcp
        rw [canPlace_inr_iff] at hcp
        exact Bool.noConfusion (hcp.2.2.symm.trans hwonky)
      · have hne : (Sum.inr y : Base) ≠ b := fun hcon => hbb hcon.symm
        rw [Board.attach_topOf_ne _ _ _ hatt hne] at htop'
        by_cases hyc : y = c
        · -- the fresh card came from the foundation: founded, hosts no edges
          rw [hyc] at htop' ⊢
          have hfounded : c.rank.toIdx < st.heights c.suit := by omega
          have hg := hwf.founds_gone c hfounded
          have hnvis' : (st.board.bottomOf c).isSome = false := hg.1
          have hnb : st.board.bottomOf c = none := by
            cases hb : st.board.bottomOf c with
            | none => rfl
            | some b' =>
                rw [hb] at hnvis'
                exact absurd hnvis' (by simp)
          have hnh : ∀ a, c ∉ st.hidden a := fun a => hg.2.2 a
          exact absurd htop' (by rw [State.topOf_inr_eq_none hwf hnb hnh]; simp)
        · exact ⟨htop', by
            show (st.board.bottomOf y).isSome = true
            rw [← bottomOf_attach_ne hatt hyc]
            exact hvis'⟩
  | pilePile c b =>
      rw [apply_pilePile_iff] at h
      obtain ⟨b₀, hbot, hne₀, hcmr, bd, hatt, rfl⟩ := h
      change bd.topOf (Sum.inr y) = some x at htop'
      change (bd.bottomOf y).isSome = true at hvis'
      have hcp : st.canPlace c b = true := by
        have h1 := hcmr
        simp only [State.canMoveRun, Bool.and_eq_true_iff] at h1
        exact h1.1
      by_cases hbb : b = Sum.inr y
      · have hxc : x = c := by
          have h1 : bd.topOf b = some c := Board.attach_topOf _ _ _ hatt
          rw [hbb] at h1
          exact Option.some.inj (htop'.symm.trans h1)
        rw [hxc] at hwonky
        rw [hbb] at hcp
        rw [canPlace_inr_iff] at hcp
        exact Bool.noConfusion (hcp.2.2.symm.trans hwonky)
      · have hne : (Sum.inr y : Base) ≠ b := fun hcon => hbb hcon.symm
        rw [Board.attach_topOf_ne _ _ _ hatt hne] at htop'
        by_cases hb₀ : b₀ = Sum.inr y
        · rw [hb₀, Board.detach_topOf] at htop'
          exact absurd htop' (by simp)
        · have hne' : (Sum.inr y : Base) ≠ b₀ := fun hcon => hb₀ hcon.symm
          rw [Board.detach_topOf_ne _ _ _ hne'] at htop'
          have htopb₀ : st.board.topOf b₀ = some c :=
            (Board.bottomOf_eq st.board c b₀).mp hbot
          by_cases hyc : y = c
          · rw [hyc] at htop' ⊢
            exact ⟨htop', by
              show (st.board.bottomOf c).isSome = true
              rw [hbot]
              rfl⟩
          · exact ⟨htop', by
              show (st.board.bottomOf y).isSome = true
              rw [← bottomOf_detach_ne htopb₀ hyc,
                ← bottomOf_attach_ne hatt (fun hcon => hyc hcon)]
              exact hvis'⟩

