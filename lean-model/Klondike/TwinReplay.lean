import Klondike.TwinFrame

/-!
# The twin replay - the window assembly

The active file: the no-twin-foundation window and the growing-rho
assembly (solvable_of_twinCorr_window) land here; the machinery
(twin maps, board kit, correspondence, move translation, the
crossed-set frame and its step lemmas) lives in TwinFrame.lean.
-/
/-! ## §8. The window assembly — the no-twin-foundation replay -/
/-- **The pilePile step in the frame** (the detach+attach run move):
the source moves the run rooted at `c` from its base `b₀` to the base
`b`, and the mirror moves the image run [rooted at `ρ c`] from
`relabel ρ b₀` to `relabel ρ b` — the detach empties the vacated seat
on both sides, the attach seats the root at the landing.  The L1/L2
family is taken at BOTH ends (`hL2`/`hwalk` at the landing, `hL2₀`/
`hwalk₀` at the vacated seat — each with the run-shape third
component, a forest-fact true on every deal-reachable WF board), and
the run-placement premise `hplace` carries the conjugated run-walk
correspondence (any run-image in the composite mirror walk places
its pre-image in the composite source walk) — the walk-structure
core the frame cannot see. -/
theorem State.TwinCorrX.apply_pilePile_X {ρ σ S M X R c b b₀}
    (h : State.TwinCorrX ρ σ S M X)
    (hcX : c ∉ X.map ρ)
    (hS : S.apply (Move.pilePile c b) = some R)
    (hbot : S.board.bottomOf c = some b₀)
    (hne : b₀ ≠ b)
    (hfree : ∀ x ∈ X, M.board.bottomOf x ≠ some (Base.relabel ρ b))
    (hwalk : ∀ x ∈ X, ∀ y ∈ x :: M.board.aboveOf x, Base.relabel ρ b ≠ Sum.inr y)
    (hL2 : ∀ d : Card, b = Sum.inr d →
      (ρ d ∉ X ∧ (∀ x ∈ X, d ∉ S.board.aboveOf (ρ x)) ∧ d ∉ c :: S.board.aboveOf c))
    (hL2₀ : ∀ d : Card, b₀ = Sum.inr d →
      (ρ d ∉ X ∧ (∀ x ∈ X, d ∉ S.board.aboveOf (ρ x)) ∧ d ∉ c :: S.board.aboveOf c))
    (hwalk₀ : ∀ x ∈ X, ∀ y ∈ x :: M.board.aboveOf x, Base.relabel ρ b₀ ≠ Sum.inr y)
    (hread : ∀ (c' d : Card), b = Sum.inr d → d ∈ S.board.aboveOf (ρ c') →
      d ∈ (S.board.detach b₀).aboveOf (ρ c'))
    (hplace : ∀ (c₂ e : Card), e ∈ c :: S.board.aboveOf c →
      ρ e ∈ (((M.board.detach (Base.relabel ρ b₀)).attach
          (Base.relabel ρ b) (ρ c)).getD M.board).aboveOf c₂ →
        e ∈ (((S.board.detach b₀).attach b c).getD S.board).aboveOf (ρ c₂)) :
    ∃ N, M.apply (Move.pilePile (ρ c) (Base.relabel ρ b)) = some N ∧
      State.TwinCorrX ρ σ R N X := by
  rw [apply_pilePile_iff] at hS
  obtain ⟨b₀', hbot', hne', hcmr, bd, hatt, rfl⟩ := hS
  have hb₀' : b₀ = b₀' := Option.some.inj (hbot.symm.trans hbot')
  subst hb₀'
  have hcρX : ρ c ∉ X := by
    intro hcon
    exact hcX (List.mem_map.mpr ⟨ρ c, hcon, h.core.isTwinMap.invol c⟩)
  have hbotc : S.board.topOf b₀ = some c := (Board.bottomOf_eq S.board c b₀).mp hbot
  have hbq : S.board.topOf b = none := by
    cases b with
    | inl a => exact (canPlace_inl_iff.mp (canPlace_of_canMoveRun hcmr)).1
    | inr d => exact (canPlace_inr_iff.mp (canPlace_of_canMoveRun hcmr)).1
  -- the mirror's firing pieces
  have hbotc' : M.board.topOf (Base.relabel ρ b₀) = some (ρ c) :=
    h.top_some b₀ c hbotc hcX
  have hbotcM : M.board.bottomOf (ρ c) = some (Base.relabel ρ b₀) :=
    (Board.bottomOf_eq M.board (ρ c) (Base.relabel ρ b₀)).mpr hbotc'
  have hneM : Base.relabel ρ b₀ ≠ Base.relabel ρ b :=
    fun hcon => hne (Base.relabel_inj h.core.isTwinMap hcon)
  have hfree' : M.board.topOf (Base.relabel ρ b) = none := h.top_none b hbq hfree
  have hcpM : M.canPlace (ρ c) (Base.relabel ρ b) = true := by
    cases b with
    | inl a =>
        rw [show Base.relabel ρ (Sum.inl a) = Sum.inl a from rfl]
        refine canPlace_inl_iff.mpr ⟨hfree', ?_⟩
        show (ρ c).rank = Rank.king
        rw [Card.IsTwinMap.rank h.core.isTwinMap c]
        exact (canPlace_inl_iff.mp (canPlace_of_canMoveRun hcmr)).2
    | inr d =>
        rw [show Base.relabel ρ (Sum.inr d) = Sum.inr (ρ d) from rfl]
        have h1 := canPlace_inr_iff.mp (canPlace_of_canMoveRun hcmr)
        refine canPlace_inr_iff.mpr ⟨hfree', ?_, ?_⟩
        · rw [h.vis_iff (ρ d), h.core.isTwinMap.invol d]
          exact h1.2.1
        · have hc2 := canSitOn_twinMap h.core.isTwinMap c d
          rw [hc2]
          exact h1.2.2
  have hcmrM : M.canMoveRun (ρ c) (Base.relabel ρ b) = true := by
    cases b with
    | inl a =>
        rw [show Base.relabel ρ (Sum.inl a) = Sum.inl a from rfl]
        exact canMoveRun_inl_iff.mpr hcpM
    | inr d =>
        rw [show Base.relabel ρ (Sum.inr d) = Sum.inr (ρ d) from rfl]
        refine canMoveRun_inr_iff.mpr ⟨hcpM, ?_⟩
        -- the guard transfer: the M-run contains no image of the landing coordinate
        have hguard : (S.board.aboveOf c).contains d = false :=
          (canMoveRun_inr_iff.mp hcmr).2
        have hnotmem : d ∉ S.board.aboveOf c := fun hm => by
          rw [List.contains_iff_mem.mpr hm] at hguard
          exact absurd hguard (by simp)
        show (M.board.aboveOf (ρ c)).contains (ρ d) = false
        by_cases hcon : (M.board.aboveOf (ρ c)).contains (ρ d) = true
        · exfalso
          have hmem : ρ d ∈ M.board.aboveOf (ρ c) := List.contains_iff_mem.mp hcon
          rcases h.above_sub (ρ c) (ρ d) hmem with h2 | h2 | ⟨x, hxX, h2⟩
          · obtain ⟨z, hz, hzz⟩ := List.mem_map.mp h2
            rw [h.core.isTwinMap.invol c] at hz
            have hzd : d = z := h.core.isTwinMap.inj hzz.symm
            exact hnotmem (by rw [hzd]; exact hz)
          · exact absurd h2 (hL2 d rfl).1
          · rw [h.above_strand x hxX] at h2
            obtain ⟨z, hz, hzz⟩ := List.mem_map.mp h2
            have hzd : d = z := h.core.isTwinMap.inj hzz.symm
            exact absurd (by rw [hzd]; exact hz) ((hL2 d rfl).2.1 x hxX)
        · exact Bool.eq_false_iff.mpr hcon
  -- the mirror's composite firing
  have hdetFree : (M.board.detach (Base.relabel ρ b₀)).topOf (Base.relabel ρ b)
      = none := by
    rw [Board.detach_topOf_ne M.board (Base.relabel ρ b₀) (Base.relabel ρ b) hneM.symm]
    exact hfree'
  have hdetUnseat : (M.board.detach (Base.relabel ρ b₀)).bottomOf (ρ c) = none :=
    Board.bottomOf_detach_self hbotc'
  obtain ⟨bd', hattM⟩ : ∃ bd', (M.board.detach (Base.relabel ρ b₀)).attach
      (Base.relabel ρ b) (ρ c) = some bd' := by
    have hne : (M.board.detach (Base.relabel ρ b₀)).attach
        (Base.relabel ρ b) (ρ c) ≠ none :=
      (Board.attach_eq_some_iff _ _ _).mpr ⟨hdetFree, hdetUnseat⟩
    cases hatt2 : (M.board.detach (Base.relabel ρ b₀)).attach
        (Base.relabel ρ b) (ρ c) with
    | none => exact absurd hatt2 hne
    | some bd'' => exact ⟨bd'', rfl⟩
  refine ⟨{M with board := bd'},
    apply_pilePile_iff.mpr ⟨Base.relabel ρ b₀, hbotcM, hneM, hcmrM, bd', hattM, rfl⟩, ?_⟩
  -- the successor's seat kits
  have htopR : bd.topOf b = some c := Board.attach_topOf _ _ _ hatt
  have htopN : bd'.topOf (Base.relabel ρ b) = some (ρ c) := Board.attach_topOf _ _ _ hattM
  have hRne : ∀ b' : Base, b' ≠ b → b' ≠ b₀ → bd.topOf b' = S.board.topOf b' := by
    intro b' hb hb₀
    rw [Board.attach_topOf_ne _ _ _ hatt hb, Board.detach_topOf_ne _ _ _ hb₀]
  have hNne : ∀ b' : Base, b' ≠ Base.relabel ρ b → b' ≠ Base.relabel ρ b₀ →
      bd'.topOf b' = M.board.topOf b' := by
    intro b' hb hb₀
    rw [Board.attach_topOf_ne _ _ _ hattM hb,
      Board.detach_topOf_ne M.board (Base.relabel ρ b₀) b' hb₀]
  have hrelabel : ∀ b₁ b₂ : Base, Base.relabel ρ b₁ = Base.relabel ρ b₂ → b₁ = b₂ :=
    fun _ _ hcon => Base.relabel_inj h.core.isTwinMap hcon
  have hbotcS : S.board.topOf b₀ = some c := hbotc
  refine ⟨⟨h.core.isTwinMap, h.core.fixes_off, h.core.deal_eq, h.core.depths_eq,
    h.core.stock_eq, h.core.step_eq, h.core.heights_off, h.core.stacked_iff⟩,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- strand_vis
    intro x hx
    have hxc : x ≠ ρ c := by
      intro hcon
      exact hcρX (by rw [← hcon]; exact hx)
    have h1 : ((M.board.detach (Base.relabel ρ b₀)).bottomOf x).isSome
        = (M.board.bottomOf x).isSome :=
      Board.isVis_detach_eq hbotc' hxc
    have h2 : (bd'.bottomOf x).isSome
        = ((M.board.detach (Base.relabel ρ b₀)).bottomOf x).isSome :=
      Board.isVis_attach_eq hattM hdetFree hxc
    show (bd'.bottomOf x).isSome = true
    rw [h2, h1]
    exact h.strand_vis x hx
  · -- vis_iff
    intro c₂
    by_cases hcq : c₂ = ρ c
    · rw [hcq]
      show (bd'.bottomOf (ρ c)).isSome = (bd.bottomOf (ρ (ρ c))).isSome
      rw [h.core.isTwinMap.invol c, (Board.bottomOf_eq bd' (ρ c) (Base.relabel ρ b)).mpr htopN,
        (Board.bottomOf_eq bd c b).mpr htopR]
      rfl
    · have h1 : (bd'.bottomOf c₂).isSome = (M.board.bottomOf c₂).isSome := by
        have ha : ((M.board.detach (Base.relabel ρ b₀)).bottomOf c₂).isSome
            = (M.board.bottomOf c₂).isSome :=
          Board.isVis_detach_eq hbotc' hcq
        have hb : (bd'.bottomOf c₂).isSome
            = ((M.board.detach (Base.relabel ρ b₀)).bottomOf c₂).isSome :=
          Board.isVis_attach_eq hattM hdetFree hcq
        rw [hb, ha]
      have h2 : (bd.bottomOf (ρ c₂)).isSome = (S.board.bottomOf (ρ c₂)).isSome := by
        have hρc : ρ c₂ ≠ c := by
          intro hcon
          have h3 : c₂ = ρ (ρ c₂) := (h.core.isTwinMap.invol c₂).symm
          rw [hcon] at h3
          exact hcq h3
        have ha : ((S.board.detach b₀).bottomOf (ρ c₂)).isSome
            = (S.board.bottomOf (ρ c₂)).isSome :=
          Board.isVis_detach_eq hbotcS hρc
        have hbdetb : (S.board.detach b₀).topOf b = none := by
          rw [Board.detach_topOf_ne S.board b₀ b hne.symm]
          exact hbq
        have hb : (bd.bottomOf (ρ c₂)).isSome
            = ((S.board.detach b₀).bottomOf (ρ c₂)).isSome :=
          Board.isVis_attach_eq hatt hbdetb hρc
        rw [hb, ha]
      show (bd'.bottomOf c₂).isSome = (bd.bottomOf (ρ c₂)).isSome
      rw [h1, h2]
      exact h.vis_iff c₂
  · -- top_some
    intro b' c' hb' hc'
    by_cases hbb : b' = b
    · rw [hbb] at hb' ⊢
      have hc'c : c' = c := Option.some.inj ((show bd.topOf b = some c' from hb').symm.trans htopR)
      rw [hc'c]
      show bd'.topOf (Base.relabel ρ b) = some (ρ c)
      exact htopN
    · by_cases hbb₀ : b' = b₀
      · rw [hbb₀] at hb'
        have hb'3 : bd.topOf b₀ = some c' := hb'
        rw [Board.attach_topOf_ne _ _ _ hatt (fun hcon => hbb (hbb₀ ▸ hcon)),
          Board.detach_topOf] at hb'3
        exact absurd hb'3 (by simp)
      · have hb'2 : S.board.topOf b' = some c' := by
          rw [← hRne b' hbb hbb₀]
          exact hb'
        show bd'.topOf (Base.relabel ρ b') = some (ρ c')
        rw [hNne (Base.relabel ρ b')
          (fun hcon => hbb (hrelabel _ _ hcon))
          (fun hcon => hbb₀ (hrelabel _ _ hcon))]
        exact h.top_some b' c' hb'2 hc'
  · -- top_none
    intro b' hb' hnb
    by_cases hbb : b' = b
    · rw [hbb] at hb'
      exact absurd (show bd.topOf b = none from hb') (by rw [htopR]; simp)
    · have hne' : Base.relabel ρ b' ≠ Base.relabel ρ b := fun hcon => hbb (hrelabel _ _ hcon)
      by_cases hbb₀ : b' = b₀
      · rw [hbb₀]
        rw [Board.attach_topOf_ne _ _ _ hattM hneM]
        exact Board.detach_topOf _ _
      · have hne₀' : Base.relabel ρ b' ≠ Base.relabel ρ b₀ :=
          fun hcon => hbb₀ (hrelabel _ _ hcon)
        have hb'2 : S.board.topOf b' = none := by
          rw [← hRne b' hbb hbb₀]
          exact hb'
        have hnb2 : ∀ x ∈ X, M.board.bottomOf x ≠ some (Base.relabel ρ b') := by
          intro x hx hcon
          refine hnb x hx ?_
          rw [Board.bottomOf_eq M.board x (Base.relabel ρ b')] at hcon
          exact (Board.bottomOf_eq bd' x (Base.relabel ρ b')).mpr (by
            rw [hNne (Base.relabel ρ b') hne' hne₀']
            exact hcon)
        show bd'.topOf (Base.relabel ρ b') = none
        rw [hNne (Base.relabel ρ b') hne' hne₀']
        exact h.top_none b' hb'2 hnb2
  · -- top_wanted
    intro x hx b' hb'
    by_cases hbb : b' = b
    · rw [hbb] at hb'
      have h1 : bd.topOf b = some (ρ x) :=
        (Board.bottomOf_eq bd (ρ x) b).mp (show bd.bottomOf (ρ x) = some b from hb')
      have h2 : ρ x = c := Option.some.inj (h1.symm.trans htopR)
      have h3 : x = ρ c := by
        have h4 : x = ρ (ρ x) := (h.core.isTwinMap.invol x).symm
        rw [h2] at h4
        exact h4
      exact absurd (by rw [← h3]; exact hx) hcρX
    · by_cases hbb₀ : b' = b₀
      · rw [hbb₀]
        rw [Board.attach_topOf_ne _ _ _ hattM hneM]
        exact Board.detach_topOf _ _
      · have hne' : Base.relabel ρ b' ≠ Base.relabel ρ b := fun hcon => hbb (hrelabel _ _ hcon)
        have hne₀' : Base.relabel ρ b' ≠ Base.relabel ρ b₀ :=
          fun hcon => hbb₀ (hrelabel _ _ hcon)
        have hb'2 : S.board.bottomOf (ρ x) = some b' := by
          rw [Board.bottomOf_eq S.board (ρ x) b', ← hRne b' hbb hbb₀]
          exact (Board.bottomOf_eq bd (ρ x) b').mp (show bd.bottomOf (ρ x) = some b' from hb')
        show bd'.topOf (Base.relabel ρ b') = none
        rw [hNne (Base.relabel ρ b') hne' hne₀']
        exact h.top_wanted x hx b' hb'2
  · -- above_strand
    intro x hx
    have h1 : bd'.aboveOf x = M.board.aboveOf x := by
      refine Board.aboveOf_congr ?_
      intro y hy
      have hdet : (M.board.detach (Base.relabel ρ b₀)).topOf (Sum.inr y)
          = M.board.topOf (Sum.inr y) := by
        refine Board.detach_topOf_ne M.board (Base.relabel ρ b₀) (Sum.inr y) ?_
        intro hcon
        cases b₀ with
        | inl a =>
            rw [show Base.relabel ρ (Sum.inl a) = Sum.inl a from rfl] at hcon
            exact hwalk₀ x hx y hy hcon.symm
        | inr d =>
            rw [show Base.relabel ρ (Sum.inr d) = Sum.inr (ρ d) from rfl] at hcon
            exact hwalk₀ x hx y hy hcon.symm
      have hatt : bd'.topOf (Sum.inr y)
          = (M.board.detach (Base.relabel ρ b₀)).topOf (Sum.inr y) := by
        refine Board.attach_topOf_ne _ _ _ hattM ?_
        intro hcon
        cases b with
        | inl a =>
            rw [show Base.relabel ρ (Sum.inl a) = Sum.inl a from rfl] at hcon
            exact hwalk x hx y hy hcon.symm
        | inr d =>
            rw [show Base.relabel ρ (Sum.inr d) = Sum.inr (ρ d) from rfl] at hcon
            exact hwalk x hx y hy hcon.symm
      exact hdet.symm.trans hatt.symm
    have hSread : ∀ y ∈ ρ x :: S.board.aboveOf (ρ x), b ≠ Sum.inr y := by
      intro y hy hcon
      obtain ⟨h1, h2, -⟩ := hL2 y hcon
      rcases List.mem_cons.mp hy with hyy | hy'
      · exact h1 (by
          show ρ y ∈ X
          rw [hyy, h.core.isTwinMap.invol x]
          exact hx)
      · exact absurd hy' (h2 x hx)
    have hSread₀ : ∀ y ∈ ρ x :: S.board.aboveOf (ρ x), b₀ ≠ Sum.inr y := by
      intro y hy hcon
      obtain ⟨h1, h2, -⟩ := hL2₀ y hcon
      rcases List.mem_cons.mp hy with hyy | hy'
      · exact h1 (by
          show ρ y ∈ X
          rw [hyy, h.core.isTwinMap.invol x]
          exact hx)
      · exact absurd hy' (h2 x hx)
    have h2 : bd.aboveOf (ρ x) = S.board.aboveOf (ρ x) := by
      refine Board.aboveOf_congr ?_
      intro y hy
      rw [Board.attach_topOf_ne _ _ _ hatt (fun hcon => hSread y hy hcon.symm),
        Board.detach_topOf_ne _ _ _ (fun hcon => hSread₀ y hy hcon.symm)]
    show bd'.aboveOf x = (bd.aboveOf (ρ x)).map ρ
    rw [h1, h2]
    exact h.above_strand x hx
  · -- above_sub
    intro c₂ y hy
    -- the detached-mirror sub: bd₁ ⊆ M
    have hsub1 : ∀ (z : Card) (w : Card), w ∈ (M.board.detach (Base.relabel ρ b₀)).aboveOf z →
        w ∈ M.board.aboveOf z := by
      intro z w hw
      refine Board.aboveOf_sub (bd := M.board) ?_ w hw
      intro B
      by_cases hB : B = Base.relabel ρ b₀
      · rw [hB]
        exact Or.inl (Board.detach_topOf _ _)
      · rw [Board.detach_topOf_ne _ _ _ hB]
        exact Or.inr rfl
    -- the strand walks are untouched
    have hstrc : ∀ x ∈ X, bd'.aboveOf x = M.board.aboveOf x := by
      intro x hx
      refine Board.aboveOf_congr ?_
      intro y hy
      have hdet : (M.board.detach (Base.relabel ρ b₀)).topOf (Sum.inr y)
          = M.board.topOf (Sum.inr y) := by
        refine Board.detach_topOf_ne M.board (Base.relabel ρ b₀) (Sum.inr y) ?_
        intro hcon
        cases b₀ with
        | inl a =>
            rw [show Base.relabel ρ (Sum.inl a) = Sum.inl a from rfl] at hcon
            exact hwalk₀ x hx y hy hcon.symm
        | inr d =>
            rw [show Base.relabel ρ (Sum.inr d) = Sum.inr (ρ d) from rfl] at hcon
            exact hwalk₀ x hx y hy hcon.symm
      have hatt : bd'.topOf (Sum.inr y)
          = (M.board.detach (Base.relabel ρ b₀)).topOf (Sum.inr y) := by
        refine Board.attach_topOf_ne _ _ _ hattM ?_
        intro hcon
        cases b with
        | inl a =>
            rw [show Base.relabel ρ (Sum.inl a) = Sum.inl a from rfl] at hcon
            exact hwalk x hx y hy hcon.symm
        | inr d =>
            rw [show Base.relabel ρ (Sum.inr d) = Sum.inr (ρ d) from rfl] at hcon
            exact hwalk x hx y hy hcon.symm
      exact hdet.symm.trans hatt.symm
    -- the S-detached sub: ⊆ the composite
    have hsubS : ∀ (z : Card) (w : Card), w ∈ (S.board.detach b₀).aboveOf z →
        w ∈ bd.aboveOf z := by
      intro z w hw
      refine Board.aboveOf_sub (bd := bd) ?_ w hw
      intro B
      by_cases hB : B = b₀
      · rw [hB]
        exact Or.inl (Board.detach_topOf _ _)
      · by_cases hBb : B = b
        · rw [hBb]
          exact Or.inl (by
            rw [Board.detach_topOf_ne S.board b₀ b hne.symm]
            exact hbq)
        · rw [Board.attach_topOf_ne _ _ _ hatt hBb,
            Board.detach_topOf_ne _ _ _ hB]
          exact Or.inr rfl
    -- the getD-unfolds of the composite witnesses
    have hgetD : (((M.board.detach (Base.relabel ρ b₀)).attach
        (Base.relabel ρ b) (ρ c)).getD M.board) = bd' := by
      rw [hattM]
      rfl
    have hgetS : (((S.board.detach b₀).attach b c).getD S.board) = bd := by
      rw [hatt]
      rfl
    -- the composite-M sub: bd₁ ⊆ bd'
    have hsub2 : ∀ (z : Card) (w : Card),
        w ∈ (M.board.detach (Base.relabel ρ b₀)).aboveOf z →
          w ∈ (((M.board.detach (Base.relabel ρ b₀)).attach
            (Base.relabel ρ b) (ρ c)).getD M.board).aboveOf z := by
      intro z w hw
      refine Board.aboveOf_sub (bd := (((M.board.detach (Base.relabel ρ b₀)).attach
        (Base.relabel ρ b) (ρ c)).getD M.board)) ?_ w hw
      intro B
      by_cases hB : B = Base.relabel ρ b
      · rw [hB]
        exact Or.inl hdetFree
      · rw [hgetD]
        rw [Board.attach_topOf_ne _ _ _ hattM hB]
        exact Or.inr rfl
    -- the run-coordinate exclusion: a card excluded from the S-run and
    -- the X-family has no image on the M-run
    have hrundet : ∀ (d : Card), d ∉ c :: S.board.aboveOf c → ρ d ∉ X →
        (∀ x ∈ X, d ∉ S.board.aboveOf (ρ x)) → ρ d ∉ ρ c :: M.board.aboveOf (ρ c) := by
      intro d hd hXx hstr hmem
      rcases List.mem_cons.mp hmem with hhd | htail
      · exact hd (by
          rw [show d = c from h.core.isTwinMap.inj hhd]
          exact List.mem_cons_self)
      · rcases h.above_sub (ρ c) (ρ d) htail with h2 | h2 | ⟨x, hxX, h2⟩
        · obtain ⟨z, hz, hzz⟩ := List.mem_map.mp h2
          rw [h.core.isTwinMap.invol c] at hz
          exact hd (List.mem_cons_of_mem _ (by
            rw [show d = z from h.core.isTwinMap.inj hzz.symm]
            exact hz))
        · exact hXx h2
        · rw [h.above_strand x hxX] at h2
          obtain ⟨z, hz, hzz⟩ := List.mem_map.mp h2
          exact hstr x hxX (by
            rw [show d = z from h.core.isTwinMap.inj hzz.symm]
            exact hz)
    -- the run-congruence of the mirror composite: bd'.walk(ρ c) = M.walk(ρ c)
    have hrunM : bd'.aboveOf (ρ c) = M.board.aboveOf (ρ c) := by
      refine Board.aboveOf_congr ?_
      intro y hy
      rw [Board.attach_topOf_ne _ _ _ hattM ?_,
        Board.detach_topOf_ne M.board (Base.relabel ρ b₀) (Sum.inr y) ?_]
      · intro hcon
        have hb₀y : b₀ = Sum.inr (ρ y) := by
          have h1 := congrArg (Base.relabel ρ) hcon.symm
          rw [Base.relabel_invol h.core.isTwinMap b₀,
            show Base.relabel ρ (Sum.inr y) = Sum.inr (ρ y) from rfl] at h1
          exact h1
        have hy2 : y ∉ ρ c :: M.board.aboveOf (ρ c) := by
          rw [show y = ρ (ρ y) from (h.core.isTwinMap.invol y).symm]
          exact hrundet (ρ y) (hL2₀ (ρ y) hb₀y).2.2 (hL2₀ (ρ y) hb₀y).1
            (hL2₀ (ρ y) hb₀y).2.1
        exact hy2 hy
      · intro hcon
        have hby : b = Sum.inr (ρ y) := by
          have h1 := congrArg (Base.relabel ρ) hcon.symm
          rw [Base.relabel_invol h.core.isTwinMap b,
            show Base.relabel ρ (Sum.inr y) = Sum.inr (ρ y) from rfl] at h1
          exact h1
        have hy2 : y ∉ ρ c :: M.board.aboveOf (ρ c) := by
          rw [show y = ρ (ρ y) from (h.core.isTwinMap.invol y).symm]
          exact hrundet (ρ y) (hL2 (ρ y) hby).2.2 (hL2 (ρ y) hby).1
            (hL2 (ρ y) hby).2.1
        exact hy2 hy
    have hy' : y ∈ bd'.aboveOf c₂ := hy
    rcases Board.mem_aboveOf_attach_run hattM hdetFree hy' with h1 | h1 | h1
    · -- y ∈ bd₁.walk(c₂)
      rcases h.above_sub c₂ y (hsub1 c₂ y h1) with h2 | h2 | ⟨x, hxX, h2⟩
      · -- y = ρ e, e ∈ S.walk(ρ c₂)
        obtain ⟨e, he, hhey⟩ := List.mem_map.mp h2
        show y ∈ (bd.aboveOf (ρ c₂)).map ρ ∨ y ∈ X ∨
          ∃ x ∈ X, y ∈ bd'.aboveOf x
        rcases Board.aboveOf_go_detach_split hbotc 52 (ρ c₂) [] e he with hacc | hdet | hrun
        · exact absurd hacc (by simp)
        · rw [← Board.aboveOf_eq_go (n := 52) (by omega)] at hdet
          exact Or.inl (List.mem_map.mpr ⟨e, hsubS (ρ c₂) e hdet, hhey⟩)
        · refine Or.inl (List.mem_map.mpr ⟨e, ?_, hhey⟩)
          rw [← hgetS]
          have h5 := hsub2 c₂ y h1
          rw [← hhey] at h5
          exact hplace c₂ e hrun h5
      · exact Or.inr (Or.inl h2)
      · refine Or.inr (Or.inr ⟨x, hxX, ?_⟩)
        show y ∈ bd'.aboveOf x
        rw [hstrc x hxX]
        exact h2
    · -- y = ρ c: the reader-forcing through the landing
      rw [h1] at hy' ⊢
      obtain ⟨pred, hmem, hcell⟩ : ∃ pred : Card, pred ∈ c₂ :: bd'.aboveOf c₂ ∧
          bd'.topOf (Sum.inr pred) = some (ρ c) := by
        rcases Board.aboveOf_go_pred 52 c₂ [] (ρ c)
          (by rw [← Board.aboveOf_eq_go (n := 52) (by omega)]; exact hy') with
          hacc | ⟨pred, hmem, hcell⟩
        · exact absurd hacc (by simp)
        rw [← Board.aboveOf_eq_go (n := 52) (by omega)] at hmem
        exact ⟨pred, hmem, hcell⟩
      have hpin : Sum.inr pred = Base.relabel ρ b :=
        Option.some.inj (((Board.bottomOf_eq bd' (ρ c) (Sum.inr pred)).mpr hcell).symm.trans
          ((Board.bottomOf_eq bd' (ρ c) (Base.relabel ρ b)).mpr htopN))
      cases b with
      | inl a =>
          rw [show Base.relabel ρ (Sum.inl a) = Sum.inl a from rfl] at hpin
          exact absurd hpin (by simp)
      | inr d =>
          rw [show Base.relabel ρ (Sum.inr d) = Sum.inr (ρ d) from rfl] at hpin
          have hpredd : pred = ρ d := (Sum.inr.inj hpin)
          rw [hpredd] at hmem
          rcases List.mem_cons.mp hmem with hc₂d | htail
          · -- the walk STARTED at ρ d
            rw [← hc₂d, h.core.isTwinMap.invol d]
            refine Or.inl (List.mem_map.mpr ⟨c, ?_, rfl⟩)
            exact Board.mem_aboveOf_of_topOf htopR
          · -- ρ d ∈ bd'.walk(c₂)
            rcases Board.mem_aboveOf_attach_run hattM hdetFree htail with h3 | h3 | h3
            · -- ρ d ∈ bd₁.walk(c₂) ⊆ M.walk(c₂): the S-reader
              rcases h.above_sub c₂ (ρ d) (hsub1 c₂ (ρ d) h3) with h4 | h4 | ⟨x, hxX, h4⟩
              · obtain ⟨z, hz, hzz⟩ := List.mem_map.mp h4
                rw [show z = d from h.core.isTwinMap.inj hzz] at hz
                have hstop : (S.board.detach b₀).topOf (Sum.inr d) = none := by
                  rw [Board.detach_topOf_ne S.board b₀ (Sum.inr d) hne.symm]
                  exact hbq
                refine Or.inl (List.mem_map.mpr ⟨c, ?_, rfl⟩)
                exact Board.mem_aboveOf_attach_new
                  (bd := S.board.detach b₀) (bd' := bd) (d := d) (q := c) (c₀ := ρ c₂)
                  hatt hstop (List.mem_cons_of_mem _ (hread c₂ d rfl hz))
              · exact absurd h4 (hL2 d rfl).1
              · rw [h.above_strand x hxX] at h4
                obtain ⟨z, hz, hzz⟩ := List.mem_map.mp h4
                rw [show z = d from h.core.isTwinMap.inj hzz] at hz
                exact absurd hz ((hL2 d rfl).2.1 x hxX)
            · -- ρ d = ρ c: d = c, excluded by the run-shape
              have hdc : d = c := h.core.isTwinMap.inj h3
              exact absurd (show d ∈ c :: S.board.aboveOf c from by
                rw [hdc]
                exact List.mem_cons_self) ((hL2 d rfl).2.2)
            · -- ρ d on the M-run: excluded
              rw [hrunM] at h3
              exact absurd (List.mem_cons_of_mem _ h3)
                (hrundet d (hL2 d rfl).2.2 (hL2 d rfl).1 (hL2 d rfl).2.1)
    · -- y ∈ bd'.walk(ρ c) [the run]
      rw [hrunM] at h1
      rcases h.above_sub (ρ c) y h1 with h2 | h2 | ⟨x, hxX, h2⟩
      · obtain ⟨e, he, hhey⟩ := List.mem_map.mp h2
        rw [h.core.isTwinMap.invol c] at he
        refine Or.inl (List.mem_map.mpr ⟨e, ?_, hhey⟩)
        rw [← hgetS]
        have h5 : y ∈ (((M.board.detach (Base.relabel ρ b₀)).attach
          (Base.relabel ρ b) (ρ c)).getD M.board).aboveOf c₂ := by
          rw [hgetD]
          exact hy'
        rw [← hhey] at h5
        exact hplace c₂ e (List.mem_cons_of_mem _ he) h5
      · exact Or.inr (Or.inl h2)
      · refine Or.inr (Or.inr ⟨x, hxX, ?_⟩)
        show y ∈ bd'.aboveOf x
        rw [hstrc x hxX]
        exact h2

/-- **The 52-count, one step**: a firing move never pushes a foundation
height past 13 — the two stack kinds land the moved suit's height at
`rank.toIdx + 1 ≤ 13` (the exact-rung guard), the un-stack steps one
DOWN, and the height-blind kinds leave the heights alone. -/
theorem State.heights_le_apply {st st' : State} {m : Move}
    (hle : ∀ s, st.heights s ≤ 13) (hfire : st.apply m = some st') :
    ∀ s, st'.heights s ≤ 13 := by
  intro s
  cases m with
  | draw =>
      rw [apply_draw_iff] at hfire
      obtain rfl := hfire
      exact hle s
  | reveal c =>
      rw [apply_reveal_iff] at hfire
      obtain ⟨_, r, a, bd, _, _, _, rfl⟩ := hfire
      exact hle s
  | deckPile c b =>
      rw [apply_deckPile_iff] at hfire
      obtain ⟨_, _, bd, _, _, rfl⟩ := hfire
      exact hle s
  | deckStack c =>
      rw [apply_deckStack_iff] at hfire
      obtain ⟨_, hrk, rfl⟩ := hfire
      show (if s = c.suit then st.heights s + 1 else st.heights s) ≤ 13
      by_cases hs : s = c.suit
      · rw [if_pos hs]
        have hlt := Rank.toIdx_lt c.rank
        have hss : st.heights s = c.rank.toIdx := by rw [hs, hrk]
        omega
      · rw [if_neg hs]
        exact hle s
  | pileStack c =>
      rw [apply_pileStack_iff] at hfire
      obtain ⟨_, b, _, hrk, rfl⟩ := hfire
      show (if s = c.suit then st.heights s + 1 else st.heights s) ≤ 13
      by_cases hs : s = c.suit
      · rw [if_pos hs]
        have hlt := Rank.toIdx_lt c.rank
        have hss : st.heights s = c.rank.toIdx := by rw [hs, hrk]
        omega
      · rw [if_neg hs]
        exact hle s
  | stackPile c b =>
      rw [apply_stackPile_iff] at hfire
      obtain ⟨hrk, _, bd, _, _, rfl⟩ := hfire
      show (if s = c.suit then st.heights s - 1 else st.heights s) ≤ 13
      by_cases hs : s = c.suit
      · rw [if_pos hs]
        have hle := hle s
        omega
      · rw [if_neg hs]
        exact hle s
  | pilePile c b =>
      rw [apply_pilePile_iff] at hfire
      obtain ⟨b₀, _, _, _, bd, _, rfl⟩ := hfire
      exact hle s

/-- **The run version of the 52-count**: heights stay ≤ 13 along every
firing play from a bounded state (induction over the play). -/
theorem State.heights_le_run {st : State} {play : List Move} {st' : State}
    (hle : ∀ s, st.heights s ≤ 13) (hrun : st.run play = some st') :
    ∀ s, st'.heights s ≤ 13 := by
  induction play generalizing st with
  | nil =>
      rw [show st.run [] = some st from rfl] at hrun
      obtain rfl : st = st' := Option.some.inj hrun
      exact hle
  | cons m ms ih =>
      simp only [State.run] at hrun
      cases hS : st.apply m with
      | none => rw [hS] at hrun; exact absurd hrun (by simp)
      | some R =>
          rw [hS] at hrun
          exact ih (State.heights_le_apply hle hS) hrun

/-- **The endgame read of the correspondence**: if the SOURCE has won
(all four heights 13), then a twin-correlated MIRROR has won too —
the off-suit heights agree outright, and the twin-suit heights read
off the stacked-set invariant at the two on-suit KINGS: ρ preserves
rank and the two kings are distinct, so their images are the two
DISTINCT twin-suit kings — BOTH twin suits' rungs sit above the king
(at least 13) — and the 52-count caps them at exactly 13.  No
height-tracking along the play is needed: the correspondence's own
shape carries the endgame. -/
theorem State.twinCorr_isWin_of_le {ρ σ W N}
    (hcorr : State.TwinCorr ρ σ W N) (hW : W.isWin = true)
    (hNle : ∀ s, N.heights s ≤ 13) : N.isWin = true := by
  have hall := List.all_eq_true.mp
    (show Suit.all.all (fun s => decide (W.heights s = 13)) = true from hW)
  have hW13 : ∀ s, W.heights s = 13 := fun s =>
    decide_eq_true_iff.mp (hall s s.mem_all)
  have hking1 := hcorr.isTwinMap.rank (Card.mk σ Rank.king)
  have hking2 := hcorr.isTwinMap.rank (Card.mk σ.flipPair Rank.king)
  have hon1 : (Card.mk σ Rank.king).suit = σ ∨ (Card.mk σ Rank.king).suit = σ.flipPair :=
    Or.inl rfl
  have hon2 : (Card.mk σ.flipPair Rank.king).suit = σ ∨
      (Card.mk σ.flipPair Rank.king).suit = σ.flipPair := Or.inr rfl
  have hs1 : (ρ (Card.mk σ Rank.king)).suit = σ ∨
      (ρ (Card.mk σ Rank.king)).suit = σ.flipPair := hcorr.isTwinMap.suit_mem hon1
  have hs2 : (ρ (Card.mk σ.flipPair Rank.king)).suit = σ ∨
      (ρ (Card.mk σ.flipPair Rank.king)).suit = σ.flipPair :=
    hcorr.isTwinMap.suit_mem hon2
  have hne : (ρ (Card.mk σ Rank.king)).suit ≠ (ρ (Card.mk σ.flipPair Rank.king)).suit := by
    intro hcon
    have hcard : ρ (Card.mk σ Rank.king) = ρ (Card.mk σ.flipPair Rank.king) := by
      have h1 : ρ (Card.mk σ Rank.king)
          = Card.mk (ρ (Card.mk σ Rank.king)).suit (ρ (Card.mk σ Rank.king)).rank := rfl
      have h2 : ρ (Card.mk σ.flipPair Rank.king)
          = Card.mk (ρ (Card.mk σ.flipPair Rank.king)).suit
              (ρ (Card.mk σ.flipPair Rank.king)).rank := rfl
      rw [h1, h2, hcon, hking1, hking2]
    have hq : Card.mk σ Rank.king = Card.mk σ.flipPair Rank.king :=
      hcorr.isTwinMap.inj hcard
    exact absurd (show σ = σ.flipPair from congrArg Card.suit hq) (Suit.flipPair_ne σ).symm
  have hgt1 : W.heights (Card.mk σ Rank.king).suit
      > (Card.mk σ Rank.king).rank.toIdx := by
    show W.heights σ > Rank.king.toIdx
    rw [hW13 σ]
    have hk : Rank.king.toIdx = 12 := rfl
    omega
  have hgt2 : W.heights (Card.mk σ.flipPair Rank.king).suit
      > (Card.mk σ.flipPair Rank.king).rank.toIdx := by
    show W.heights σ.flipPair > Rank.king.toIdx
    rw [hW13 σ.flipPair]
    have hk : Rank.king.toIdx = 12 := rfl
    omega
  have hN1 : N.heights (ρ (Card.mk σ Rank.king)).suit > 12 := by
    have h := (hcorr.stacked_iff (Card.mk σ Rank.king) hon1).mpr hgt1
    rw [hking1] at h
    exact h
  have hN2 : N.heights (ρ (Card.mk σ.flipPair Rank.king)).suit > 12 := by
    have h := (hcorr.stacked_iff (Card.mk σ.flipPair Rank.king) hon2).mpr hgt2
    rw [hking2] at h
    exact h
  show Suit.all.all (fun s => decide (N.heights s = 13)) = true
  refine List.all_eq_true.mpr ?_
  intro s _
  refine decide_eq_true_iff.mpr ?_
  by_cases hon : s = σ ∨ s = σ.flipPair
  · have hcover : (ρ (Card.mk σ Rank.king)).suit = s ∨
      (ρ (Card.mk σ.flipPair Rank.king)).suit = s := by
      rcases hs1 with h1 | h1 <;> rcases hs2 with h2 | h2
      · exact absurd (h1.trans h2.symm) hne
      · rcases hon with hs | hs
        · exact Or.inl (h1.trans hs.symm)
        · exact Or.inr (h2.trans hs.symm)
      · rcases hon with hs | hs
        · exact Or.inr (h2.trans hs.symm)
        · exact Or.inl (h1.trans hs.symm)
      · exact absurd (h1.trans h2.symm) hne
    rcases hcover with hc | hc
    · have h := hN1
      rw [hc] at h
      have hle := hNle s
      omega
    · have h := hN2
      rw [hc] at h
      have hle := hNle s
      omega
  · have h1 : s ≠ σ := fun h => hon (Or.inl h)
    have h2 : s ≠ σ.flipPair := fun h => hon (Or.inr h)
    rw [hcorr.heights_off s h1 h2]
    exact hW13 s

/-- **The clean run**: a clean play translates wholesale — the mirror
runs the ρ-relabeled play, and the correspondence itself is preserved
stepwise (the twin-suit rungs never move under a clean play, so no
height-tracking is needed). -/
theorem State.twinCorr_run_clean (ρ : Card → Card) (σ : Suit) :
    ∀ (play : List Move) (S M : State),
    State.TwinCorr ρ σ S M →
    (∀ a, ∀ c ∈ S.hidden a, ρ c = c) → (∀ c ∈ S.stock.cards, ρ c = c) →
    (∀ m ∈ play, Move.twinClean σ m = true) →
    ∀ {W : State}, S.run play = some W →
    ∃ N, M.run (play.map (Move.relabelTwin ρ)) = some N ∧ State.TwinCorr ρ σ W N := by
  intro play
  induction play with
  | nil =>
      intro S M hcorr _ _ _ W hrun
      have h1 : S.run [] = some S := rfl
      have hW : W = S := (Option.some.inj (h1.symm.trans hrun)).symm
      subst hW
      refine ⟨M, ?_, hcorr⟩
      rfl
  | cons m ms ih =>
      intro S M hcorr hhid hstock hclean W hrun
      simp only [State.run] at hrun
      cases hS : S.apply m with
      | none => rw [hS] at hrun; exact absurd hrun (by simp)
      | some R =>
          rw [hS] at hrun
          obtain ⟨N, hfire, hcorr'⟩ := State.TwinCorr.apply_clean hcorr hhid hstock
            (hclean m List.mem_cons_self) hS
          have hhidR : ∀ a, ∀ c ∈ R.hidden a, ρ c = c := by
            intro a c hc
            exact hhid a c (State.hidden_sub_apply hS a c hc)
          have hstockR : ∀ c ∈ R.stock.cards, ρ c = c := by
            intro c hc
            exact hstock c (State.stock_cards_sub_apply hS c hc)
          obtain ⟨N', hrun', hcorr''⟩ := ih R N hcorr' hhidR hstockR
            (fun m' hm' => hclean m' (List.mem_cons_of_mem _ hm')) hrun
          refine ⟨N', ?_, hcorr''⟩
          simp only [List.map_cons, State.run, hfire]
          exact hrun'

/-- **The no-twin-foundation window** (the climb-out's clean core,
board-only): if the source's winning play never makes a twin-suit
foundation move, the twin-correlated mirror replays the translated
play and wins — no height-tracking premise: the endgame reads the
correspondence's own shape (off-suit heights agree; the twin suits'
rungs sit above the on-suit kings by the stacked-set invariant, and
the 52-count caps them at 13).  The ply result's board-only swap
(`exchange_merge_ply_root`) enters here at `ρ = τ_z`; the `hhid`/
`hstock` premises are WF-consequences (z/z' seated). -/
theorem State.solvable_of_twinCorr_clean {ρ σ S M}
    (hcorr : State.TwinCorr ρ σ S M)
    (hMle : ∀ s, M.heights s ≤ 13)
    (hhid : ∀ a, ∀ c ∈ S.hidden a, ρ c = c)
    (hstock : ∀ c ∈ S.stock.cards, ρ c = c)
    {play : List Move} (hclean : ∀ m ∈ play, Move.twinClean σ m = true)
    {W : State} (hrun : S.run play = some W) (hwin : W.isWin = true) :
    M.solvableFrom := by
  obtain ⟨N, hrun', hcorr'⟩ := State.twinCorr_run_clean ρ σ play S M hcorr hhid hstock
    hclean hrun
  exact ⟨play.map (Move.relabelTwin ρ), N, hrun',
    State.twinCorr_isWin_of_le hcorr' hwin (State.heights_le_run hMle hrun')⟩

/-- **The window, backward**: the same statement with the two games
exchanged (the correspondence is symmetric; the hidden/stock
premises transfer along the equal deals and stock cycles). -/
theorem State.solvable_of_twinCorr_clean_back {ρ σ S M}
    (hcorr : State.TwinCorr ρ σ S M)
    (hSle : ∀ s, S.heights s ≤ 13)
    (hhid : ∀ a, ∀ c ∈ S.hidden a, ρ c = c)
    (hstock : ∀ c ∈ S.stock.cards, ρ c = c)
    {play : List Move} (hclean : ∀ m ∈ play, Move.twinClean σ m = true)
    {W : State} (hrun : M.run play = some W) (hwin : W.isWin = true) :
    S.solvableFrom := by
  have hhid' : ∀ a, ∀ c ∈ M.hidden a, ρ c = c := by
    intro a c hc
    refine hhid a c ?_
    have hm : S.hidden a = M.hidden a := by
      show (S.deal.piles a).take (S.depths a) = (M.deal.piles a).take (M.depths a)
      rw [show S.deal.piles a = M.deal.piles a from by rw [hcorr.deal_eq],
        ← hcorr.depths_eq]
    rw [hm]
    exact hc
  have hstock' : ∀ c ∈ M.stock.cards, ρ c = c := by
    intro c hc
    refine hstock c ?_
    have hcs : S.stock.cards = M.stock.cards := by
      rw [show S.stock = M.stock from hcorr.stock_eq.symm]
    rw [hcs]
    exact hc
  exact State.solvable_of_twinCorr_clean hcorr.symm hSle hhid' hstock' hclean hrun hwin

/-! ## §9. The window -/

/-- **The window's move condition**: the moves the mirror can answer
in kind, one-for-one, preserving the correspondence verbatim.  The
height-blind kinds (draw/reveal/deckPile/pilePile) always; an
off-suit foundation move always (its guard reads only the off-suit
heights, where the games agree).  A twin-suit foundation move needs
its rung condition: an on-suit STACK (`deckStack`/`pileStack`) needs
the partner suit's rung at or above the moved rank (the skew —
`State.TwinCore.rung_of_skew` then pins the mirror's rung, so the
answer is the aligned verbatim stack and the growth never engages),
an on-suit UNSTACK (`stackPile`) needs the partner suit's rung at or
below the moved rank plus one (`State.TwinCore.stackPile_rung`), and
an on-suit `deckStack` needs the moved card `ρ`-fixed (the non-pair
card — the PAIR card's deckStack has no in-kind response: the run
level residual, excluded here). -/
def Move.windowOK (ρ : Card → Card) (σ : Suit) (st : State) (m : Move) : Bool :=
  match m with
  | .draw | .reveal _ | .deckPile _ _ | .pilePile _ _ => true
  | .deckStack q =>
      decide (q.suit ≠ σ ∧ q.suit ≠ σ.flipPair) ||
      (decide (q.rank.toIdx ≤ st.heights (Card.flipSuit q).suit) &&
       decide (ρ q = q))
  | .pileStack q =>
      decide (q.suit ≠ σ ∧ q.suit ≠ σ.flipPair) ||
      decide (q.rank.toIdx ≤ st.heights (Card.flipSuit q).suit)
  | .stackPile c _ =>
      decide (c.suit ≠ σ ∧ c.suit ≠ σ.flipPair) ||
      decide (st.heights (Card.flipSuit c).suit ≤ c.rank.toIdx + 1)

/-- **The window's play condition**: every move of the play satisfies
`Move.windowOK` at the state it is played from. -/
def State.playWindow (ρ : Card → Card) (σ : Suit) (st : State) : List Move → Bool
  | [] => true
  | m :: ms =>
      Move.windowOK ρ σ st m &&
      match st.apply m with
      | none => false
      | some st' => State.playWindow ρ σ st' ms

/-- The play condition's one-step unfolding at a firing move. -/
theorem State.playWindow_cons_of {ρ σ st m ms R} (hS : st.apply m = some R) :
    State.playWindow ρ σ st (m :: ms)
      = (Move.windowOK ρ σ st m && State.playWindow ρ σ R ms) := by
  simp only [State.playWindow, hS]

/-- **Window-solvability**: the source wins by a play the window
admits. -/
def State.solvableWindow (ρ : Card → Card) (σ : Suit) (S : State) : Prop :=
  ∃ play W, S.run play = some W ∧ W.isWin = true ∧
    State.playWindow ρ σ S play = true

/-- The empty-crossing frame IS the full correspondence (every escape
is vacuous, so the seat clauses give back the board conjugation). -/
theorem State.TwinCorrX.toCorr {ρ σ S M} (h : State.TwinCorrX ρ σ S M []) :
    State.TwinCorr ρ σ S M :=
  ⟨h.core, by
    intro b
    cases hS : S.board.topOf (Base.relabel ρ b) with
    | some c =>
        have h1 := h.top_some (Base.relabel ρ b) c hS (by simp)
        rw [Base.relabel_invol h.core.isTwinMap b] at h1
        rw [Option.map_some]
        exact h1
    | none =>
        have h1 := h.top_none (Base.relabel ρ b) hS (by simp)
        rw [Base.relabel_invol h.core.isTwinMap b] at h1
        rw [Option.map_none]
        exact h1⟩

/-- **The window step**: one move the window admits is translated and
answered in kind — the mirror's response is the `relabelTwin` image,
firing, and the correspondence is preserved verbatim.  The dispatch:
the clean kinds verbatim; an on-suit stack by the pinned rung (the
skew derivation `rung_of_skew`); an on-suit deckStack of a non-pair
card by the same card at the pinned rung; an on-suit unstack by the
aligned rung (`stackPile_rung`, the 52-count capping the mirror). -/
theorem State.twinCorr_step_window {ρ σ S M R m}
    (hcorr : State.TwinCorr ρ σ S M)
    (hMle : ∀ s, M.heights s ≤ 13)
    (hwf : S.WF)
    (hhid : ∀ a, ∀ c ∈ S.hidden a, ρ c = c)
    (hstock : ∀ c ∈ S.stock.cards, ρ c = c)
    (hok : Move.windowOK ρ σ S m = true)
    (hS : S.apply m = some R) :
    ∃ N, M.apply (Move.relabelTwin ρ m) = some N ∧ State.TwinCorr ρ σ R N := by
  cases m with
  | draw => exact State.TwinCorr.apply_clean hcorr hhid hstock rfl hS
  | reveal c => exact State.TwinCorr.apply_clean hcorr hhid hstock rfl hS
  | deckPile c b => exact State.TwinCorr.apply_clean hcorr hhid hstock rfl hS
  | pilePile c b => exact State.TwinCorr.apply_clean hcorr hhid hstock rfl hS
  | deckStack q =>
      by_cases hon : q.suit = σ ∨ q.suit = σ.flipPair
      · simp only [Move.windowOK, Bool.or_eq_true, Bool.and_eq_true,
        decide_eq_true_iff] at hok
        rcases hok with hoff | ⟨hskew, hqρ⟩
        · rcases hon with hs | hs
          · exact absurd hs hoff.1
          · exact absurd hs hoff.2
        · have hSiff := apply_deckStack_iff.mp hS
          obtain ⟨hprev, hrk, rfl⟩ := hSiff
          have hrung := State.TwinCore.rung_of_skew hcorr.toTwinCore hon hrk.symm hskew
          rw [hqρ] at hrung
          obtain ⟨N, hfire, hX⟩ := State.TwinCorrX.apply_deckStack_onsuit
            (State.TwinCorr.toTwinCorrX hcorr) hon hqρ hS hrung
          refine ⟨N, ?_, hX.toCorr⟩
          show M.apply (Move.deckStack (ρ q)) = some N
          rw [hqρ]
          exact hfire
      · exact State.TwinCorr.apply_clean hcorr hhid hstock
          (by simp only [Move.twinClean, decide_eq_true_iff]
              exact ⟨fun h => hon (Or.inl h), fun h => hon (Or.inr h)⟩) hS
  | pileStack q =>
      by_cases hon : q.suit = σ ∨ q.suit = σ.flipPair
      · simp only [Move.windowOK, Bool.or_eq_true, decide_eq_true_iff] at hok
        rcases hok with hoff | hskew
        · rcases hon with hs | hs
          · exact absurd hs hoff.1
          · exact absurd hs hoff.2
        · have hSiff := apply_pileStack_iff.mp hS
          obtain ⟨htop, bq, hbot, hrk, rfl⟩ := hSiff
          have halign := State.TwinCore.rung_of_skew hcorr.toTwinCore hon hrk.symm hskew
          obtain ⟨N, hfire, hX⟩ := State.TwinCorrX.apply_pileStack_onsuit
            (State.TwinCorr.toTwinCorrX hcorr) hon hS halign (by simp) (by simp)
          exact ⟨N, hfire, hX.toCorr⟩
      · exact State.TwinCorr.apply_clean hcorr hhid hstock
          (by simp only [Move.twinClean, decide_eq_true_iff]
              exact ⟨fun h => hon (Or.inl h), fun h => hon (Or.inr h)⟩) hS
  | stackPile c b =>
      by_cases hon : c.suit = σ ∨ c.suit = σ.flipPair
      · simp only [Move.windowOK, Bool.or_eq_true, decide_eq_true_iff] at hok
        rcases hok with hoff | hanti
        · rcases hon with hs | hs
          · exact absurd hs hoff.1
          · exact absurd hs hoff.2
        · have hSiff := apply_stackPile_iff.mp hS
          obtain ⟨hrk, hcp, bd, hatt, rfl⟩ := hSiff
          have halign := State.TwinCore.stackPile_rung hcorr.toTwinCore hon hrk.symm hanti
            (hMle (ρ c).suit)
          obtain ⟨N, hfire, hX⟩ := State.TwinCorrX.apply_stackPile_onsuit
            (State.TwinCorr.toTwinCorrX hcorr) hwf hon (by simp) hS halign
            (by simp) (by simp) (by simp) (by simp)
          exact ⟨N, hfire, hX.toCorr⟩
      · exact State.TwinCorr.apply_clean hcorr hhid hstock
          (by simp only [Move.twinClean, decide_eq_true_iff]
              exact ⟨fun h => hon (Or.inl h), fun h => hon (Or.inr h)⟩) hS

/-- **The window run**: a play the window admits translates wholesale
— the mirror runs the `relabelTwin` image, the correspondence is
preserved at every step, and the invariants (the mirror's 52-count,
the source's WF, the hidden/stock `ρ`-freeness) ride along. -/
theorem State.twinCorr_run_window (ρ : Card → Card) (σ : Suit) :
    ∀ (play : List Move) (S M : State),
    State.TwinCorr ρ σ S M →
    (∀ s, M.heights s ≤ 13) →
    S.WF →
    (∀ a, ∀ c ∈ S.hidden a, ρ c = c) → (∀ c ∈ S.stock.cards, ρ c = c) →
    State.playWindow ρ σ S play = true →
    ∀ {W : State}, S.run play = some W →
    ∃ N, M.run (play.map (Move.relabelTwin ρ)) = some N ∧ State.TwinCorr ρ σ W N := by
  intro play
  induction play with
  | nil =>
      intro S M hcorr _ _ _ _ _ W hrun
      have h1 : S.run [] = some S := rfl
      have hW : W = S := (Option.some.inj (h1.symm.trans hrun)).symm
      subst hW
      exact ⟨M, rfl, hcorr⟩
  | cons m ms ih =>
      intro S M hcorr hMle hwf hhid hstock hwin W hrun
      simp only [State.run] at hrun
      cases hS : S.apply m with
      | none => rw [hS] at hrun; exact absurd hrun (by simp)
      | some R =>
          rw [hS] at hrun
          rw [State.playWindow_cons_of hS] at hwin
          simp only [Bool.and_eq_true] at hwin
          obtain ⟨hok, hwin'⟩ := hwin
          obtain ⟨N, hfire, hcorr'⟩ :=
            State.twinCorr_step_window hcorr hMle hwf hhid hstock hok hS
          obtain ⟨N', hrun', hcorr''⟩ := ih R N hcorr'
            (State.heights_le_apply hMle hfire)
            (apply_wf hwf m R hS)
            (fun a c hc => hhid a c (State.hidden_sub_apply hS a c hc))
            (fun c hc => hstock c (State.stock_cards_sub_apply hS c hc))
            hwin' hrun
          refine ⟨N', ?_, hcorr''⟩
          simp only [List.map_cons, State.run, hfire]
          exact hrun'

/-- **THE WINDOW** (the climb-out replay, conditional form): a
twin-correlated mirror of a WF source that can win by a play the
window admits is itself solvable — the mirror replays the
ρ-translated play verbatim, the correspondence preserved at every
step (no growth: the skew forces the aligned response, so the
crossed-set machinery never engages), and the endgame is the
correspondence's own shape (the two on-suit kings plus the
52-count).  The added premises over the target four-premise form,
each named and minimal: `hhid`/`hstock` (the hidden and stock cards
`ρ`-fixed — needed by the reveal/deckPile responses, WF-consequences
at the licensed exchange states, not derivable from the
correspondence alone) and `hsolw` in place of `hsol` (the winning
play must satisfy the window condition: every twin-suit foundation
move carries its rung condition — the skew for stacks, the anti-skew
for unstacks — and the pair card's deckStack is excluded). -/
theorem State.solvable_of_twinCorr_window {S M : State} {z : Card}
    (hcorr : State.TwinCorr (Card.swapTwin z) z.suit S M)
    (hMle : ∀ s, M.heights s ≤ 13)
    (hwf : S.WF)
    (hhid : ∀ a, ∀ c ∈ S.hidden a, Card.swapTwin z c = c)
    (hstock : ∀ c ∈ S.stock.cards, Card.swapTwin z c = c)
    (hsolw : S.solvableWindow (Card.swapTwin z) z.suit) :
    M.solvableFrom := by
  obtain ⟨play, W, hrun, hwin, hplay⟩ := hsolw
  obtain ⟨N, hrun', hcorr'⟩ := State.twinCorr_run_window (Card.swapTwin z) z.suit play S M
    hcorr hMle hwf hhid hstock hplay hrun
  exact ⟨play.map (Move.relabelTwin (Card.swapTwin z)), N, hrun',
    State.twinCorr_isWin_of_le hcorr' hwin (State.heights_le_run hMle hrun')⟩

/-! ## §10. The growth engagement -/

/-- **The pair-group cancellation**: composing the two swaps of the
SAME twin pair is the identity — so a growth at either member of the
window's pair `{z, flipSuit z}` (from the base map `swapTwin z`)
returns the correspondence to the identity map. -/
theorem Card.swapTwin_pair_comp (z : Card) :
    (Card.swapTwin (Card.flipSuit z) ∘ Card.swapTwin z) = id := by
  funext x
  by_cases hx : x = z
  · rw [hx]
    show Card.swapTwin (Card.flipSuit z) (Card.swapTwin z z) = z
    rw [Card.swapTwin_self_left, Card.swapTwin_self_left, Card.flipSuit_flipSuit]
  · by_cases hx' : x = Card.flipSuit z
    · rw [hx']
      show Card.swapTwin (Card.flipSuit z) (Card.swapTwin z (Card.flipSuit z))
        = Card.flipSuit z
      rw [Card.swapTwin_self_right]
      unfold Card.swapTwin
      rw [if_neg (Card.flipSuit_ne z).symm,
        if_pos (show z = Card.flipSuit (Card.flipSuit z) from (Card.flipSuit_flipSuit z).symm)]
    · show Card.swapTwin (Card.flipSuit z) (Card.swapTwin z x) = x
      rw [Card.swapTwin_of_ne hx hx',
        Card.swapTwin_of_ne hx' (fun hcon => absurd (hcon.trans (Card.flipSuit_flipSuit z)) hx)]

/-- **The rung equality under a pointwise-fixing map**: when the
correspondence's `ρ` fixes EVERY card (the post-growth identity — the
mid-episode and post-episode regime), the stacked-set iff is the
identity on every card, so the two games' heights are EQUAL at every
suit (the 52-count on both sides caps the cut argument).  This is the
rung alignment for the whole post-episode regime: no skew condition
is needed — the firing rung transfers directly. -/
theorem State.TwinCore.heights_eq_of_fix {ρ σ S M} (h : State.TwinCore ρ σ S M)
    (hfix : ∀ c, ρ c = c)
    (hMle : ∀ s, M.heights s ≤ 13) (hSle : ∀ s, S.heights s ≤ 13) :
    ∀ s, M.heights s = S.heights s := by
  intro s
  by_cases hon : s = σ ∨ s = σ.flipPair
  · have hcut : ∀ r : Rank, r.toIdx < 13 →
        (M.heights s > r.toIdx ↔ S.heights s > r.toIdx) := by
      intro r hr
      have honc : (Card.mk s r).suit = σ ∨ (Card.mk s r).suit = σ.flipPair := by
        show s = σ ∨ s = σ.flipPair
        exact hon
      have hiff := h.stacked_iff (Card.mk s r) honc
      rw [hfix (Card.mk s r)] at hiff
      exact hiff
    rcases Nat.lt_trichotomy (M.heights s) (S.heights s) with hlt | heq | hgt
    · exfalso
      have hM13 : M.heights s < 13 := Nat.lt_of_lt_of_le hlt (hSle s)
      obtain ⟨r, hr⟩ := Rank.exists_toIdx (M.heights s) hM13
      have h1 : ¬ (M.heights s > r.toIdx) := by rw [hr]; omega
      have h2 : S.heights s > r.toIdx := by rw [hr]; omega
      exact h1 ((hcut r (by rw [hr]; omega)).mpr h2)
    · exact heq
    · exfalso
      have hS13 : S.heights s < 13 := Nat.lt_of_lt_of_le hgt (hMle s)
      obtain ⟨r, hr⟩ := Rank.exists_toIdx (S.heights s) hS13
      have h1 : ¬ (S.heights s > r.toIdx) := by rw [hr]; omega
      have h2 : M.heights s > r.toIdx := by rw [hr]; omega
      exact h1 ((hcut r (by rw [hr]; omega)).mp h2)
  · exact h.heights_off s (fun hcon => hon (Or.inl hcon))
      (fun hcon => hon (Or.inr hcon))

/-- **The misalignment from the failed skew** (the growth's `hmis`
supply): for a PAIR card's on-suit stack (the moved card is `z` or its
twin), the failed skew — the partner suit's source rung strictly below
the moved rank — FORCES the mirror's misalignment.  The proof: the
stacked-set iff at the moved card caps the mirror's rung at the moved
rank, and the iff at every lower card of the partner suit (all of them
ρ-fixed — the pair members sit AT the moved rank, not below) would
push the partner rung up to the moved rank — so an aligned mirror
would re-derive the skew.  This is the dispatch hinge of the growth
engagement: `¬skew` legitimately routes the pair-stack to the
growth. -/
theorem State.TwinCore.rung_ne_of_noskew_pair {z : Card} {σ S M} {q : Card}
    (h : State.TwinCore (Card.swapTwin z) σ S M)
    (hon : q.suit = σ ∨ q.suit = σ.flipPair)
    (hq : S.heights q.suit = q.rank.toIdx)
    (hpair : q = z ∨ q = Card.flipSuit z)
    (hnoskew : ¬ (q.rank.toIdx ≤ S.heights (Card.flipSuit q).suit)) :
    M.heights (Card.swapTwin z q).suit ≠ q.rank.toIdx := by
  intro halign
  -- the alignment's suit/rank bookkeeping:
  have hρsuit : (Card.swapTwin z q).suit = (Card.flipSuit q).suit := by
    rcases hpair with hp | hp
    · rw [hp]
      show (Card.swapTwin z z).suit = (Card.flipSuit z).suit
      rw [Card.swapTwin_self_left]
    · rw [hp]
      show (Card.swapTwin z (Card.flipSuit z)).suit = (Card.flipSuit (Card.flipSuit z)).suit
      rw [Card.swapTwin_self_right, Card.flipSuit_flipSuit]
  have hρrank : (Card.swapTwin z q).rank = q.rank := by
    rcases hpair with hp | hp
    · rw [hp]
      show (Card.swapTwin z z).rank = z.rank
      rw [Card.swapTwin_self_left, Card.flipSuit_rank]
    · rw [hp]
      show (Card.swapTwin z (Card.flipSuit z)).rank = (Card.flipSuit z).rank
      rw [Card.swapTwin_self_right, Card.flipSuit_rank]
  -- the partner suit is on-suit (the twin of an on-suit suit):
  have honf : (Card.flipSuit q).suit = σ ∨ (Card.flipSuit q).suit = σ.flipPair := by
    show q.suit.flipPair = σ ∨ q.suit.flipPair = σ.flipPair
    rcases hon with hs | hs
    · rw [hs]; exact Or.inr rfl
    · rw [hs]; exact Or.inl (Suit.flipPair_flipPair σ)
  -- the skew re-derivation: every lower rank card of the partner suit is
  -- ρ-fixed and its iff pushes the source rung up
  have hgt : ∀ r : Rank, r.toIdx < q.rank.toIdx →
      S.heights (Card.flipSuit q).suit > r.toIdx := by
    intro r hr
    have honc : (Card.mk (Card.flipSuit q).suit r).suit = σ ∨
        (Card.mk (Card.flipSuit q).suit r).suit = σ.flipPair := by
      show (Card.flipSuit q).suit = σ ∨ (Card.flipSuit q).suit = σ.flipPair
      exact honf
    have hiff := h.stacked_iff (Card.mk (Card.flipSuit q).suit r) honc
    have hrk : z.rank.toIdx = q.rank.toIdx := by
      rcases hpair with hp | hp
      · rw [hp]
      · rw [hp, Card.flipSuit_rank]
    have hfix : Card.swapTwin z (Card.mk (Card.flipSuit q).suit r)
        = Card.mk (Card.flipSuit q).suit r := by
      refine Card.swapTwin_of_ne ?_ ?_
      · intro hcon
        have h1 : (Card.mk (Card.flipSuit q).suit r).rank.toIdx = z.rank.toIdx := by
          rw [show (Card.mk (Card.flipSuit q).suit r).rank = z.rank from
            congrArg Card.rank hcon]
        have h2 : (Card.mk (Card.flipSuit q).suit r).rank.toIdx = r.toIdx := rfl
        omega
      · intro hcon
        have h1 : (Card.mk (Card.flipSuit q).suit r).rank.toIdx = (Card.flipSuit z).rank.toIdx := by
          rw [show (Card.mk (Card.flipSuit q).suit r).rank = (Card.flipSuit z).rank from
            congrArg Card.rank hcon]
        have h2 : (Card.mk (Card.flipSuit q).suit r).rank.toIdx = r.toIdx := rfl
        rw [Card.flipSuit_rank] at h1
        omega
    rw [hfix] at hiff
    have hL : M.heights (Card.mk (Card.flipSuit q).suit r).suit
        > (Card.mk (Card.flipSuit q).suit r).rank.toIdx := by
      show M.heights (Card.flipSuit q).suit > r.toIdx
      rw [← hρsuit, halign]
      omega
    exact hiff.mp hL
  -- the pushed-up rung contradicts the failed skew
  have hk : q.rank.toIdx < 13 := Rank.toIdx_lt q.rank
  rcases Nat.eq_zero_or_pos q.rank.toIdx with h0 | hpos
  · exfalso
    have := hnoskew
    omega
  · obtain ⟨r, hr⟩ := Rank.exists_toIdx (q.rank.toIdx - 1) (by omega)
    have hpush := hgt r (by rw [hr]; omega)
    rw [hr] at hpush
    have := hnoskew
    omega

/-- **The unstack rung without the anti-skew** (the non-pair,
non-adjacent case): for a worry-back of a card that is neither pair
member and whose rank is not the pair rank minus one, the mirror's
rung is aligned REGARDLESS of the partner suit — the stacked-set iff
at the moved card pushes the mirror's rung up, and the iff at the
next card up (which the rank gap guarantees is `ρ`-fixed) caps it.
The anti-skew remains load-bearing only at the pair members and the
just-below-pair unstack: there the crossed configuration (the
partner member stacked in the source, this one not) puts the mirror
genuinely ahead, and the response would be a MULTI-unstack (the
mirror dropping its rung past the stranded pair card before the
verbatim) — not a single in-kind move, and not source-composable. -/
theorem State.TwinCore.rung_eq_unstack_of_ne {z : Card} {σ S M} {c : Card}
    (h : State.TwinCore (Card.swapTwin z) σ S M)
    (hon : c.suit = σ ∨ c.suit = σ.flipPair)
    (hSg : S.heights c.suit = c.rank.toIdx + 1)
    (hcρ : Card.swapTwin z c = c)
    (hrne : c.rank.toIdx + 1 ≠ z.rank.toIdx)
    (hMle : M.heights (Card.swapTwin z c).suit ≤ 13) :
    M.heights (Card.swapTwin z c).suit = c.rank.toIdx + 1 := by
  rw [hcρ] at hMle ⊢
  have hiff := h.stacked_iff c hon
  rw [Card.IsTwinMap.rank h.isTwinMap c, hcρ] at hiff
  have hge : M.heights c.suit > c.rank.toIdx := hiff.mpr (by rw [hSg]; omega)
  rcases Nat.eq_or_lt_of_le (show c.rank.toIdx + 1 ≤ 13 by
      have := Rank.toIdx_lt c.rank; omega) with h13 | hlt
  · omega
  · obtain ⟨rp, hrp⟩ := Rank.exists_toIdx (c.rank.toIdx + 1) hlt
    have hcp : Card.swapTwin z (Card.mk c.suit rp) = Card.mk c.suit rp := by
      refine Card.swapTwin_of_ne ?_ ?_
      · intro hcon
        have h1 : z.rank.toIdx = (Card.mk c.suit rp).rank.toIdx := by rw [hcon]
        rw [show (Card.mk c.suit rp).rank.toIdx = rp.toIdx from rfl, hrp] at h1
        exact hrne h1.symm
      · intro hcon
        have h1 : z.rank.toIdx = (Card.mk c.suit rp).rank.toIdx := by
          rw [hcon, Card.flipSuit_rank]
        rw [show (Card.mk c.suit rp).rank.toIdx = rp.toIdx from rfl, hrp] at h1
        exact hrne h1.symm
    have honp : (Card.mk c.suit rp).suit = σ ∨ (Card.mk c.suit rp).suit = σ.flipPair := by
      show c.suit = σ ∨ c.suit = σ.flipPair
      exact hon
    have hiffp := h.stacked_iff (Card.mk c.suit rp) honp
    rw [Card.IsTwinMap.rank h.isTwinMap (Card.mk c.suit rp), hcp] at hiffp
    have hcap : ¬ (S.heights c.suit > rp.toIdx) := by rw [hSg, hrp]; omega
    have hle : ¬ (M.heights c.suit > rp.toIdx) := fun hc => hcap (hiffp.mp hc)
    have h2 : rp.toIdx = c.rank.toIdx + 1 := hrp
    omega

/-- **The rung equality with the partner past the pair rank** (the
post-equalization climb): for a NON-pair on-suit stack whose partner
suit's rung sits strictly above the pair rank, the mirror's rung is
aligned REGARDLESS of the skew — the stacked-set iff at the moved
card caps the mirror, the iff at the partner-suit pair member (the
cross at the pair rank) pushes the mirror past the pair rank, and the
non-pair cards between cut identically on both sides.  This kills the
co-climb's ALTERNATION requirement: after the adjacent pair-stacking
`[pileStack z; pileStack z']` equalizes the twin rungs, a run of
same-suit climbs has the skew broken from the second climb on (the
partner rung stays at z.rank + 1 while the own suit climbs past it),
but the partner stays past the pair rank — so every climb of the run
is aligned and admits VERBATIM. -/
theorem State.TwinCore.rung_eq_of_partner_past {z : Card} {S M} {q : Card}
    (h : State.TwinCore (Card.swapTwin z) z.suit S M)
    (hon : q.suit = z.suit ∨ q.suit = z.suit.flipPair)
    (hq : S.heights q.suit = q.rank.toIdx)
    (hcρ : Card.swapTwin z q = q)
    (hpart : z.rank.toIdx < S.heights (Card.flipSuit q).suit)
    (_hMle : M.heights (Card.swapTwin z q).suit ≤ 13) :
    M.heights (Card.swapTwin z q).suit = q.rank.toIdx := by
  rw [hcρ]
  -- the cap: the iff at the moved card
  have hiff := h.stacked_iff q hon
  rw [Card.IsTwinMap.rank h.isTwinMap q, hcρ] at hiff
  have hle : ¬ (M.heights q.suit > q.rank.toIdx) := by
    intro hgt
    have h1 := hiff.mp hgt
    rw [hq] at h1
    exact Nat.lt_irrefl _ h1
  -- the push: the cross at the partner-suit pair member
  have hpush : M.heights q.suit > z.rank.toIdx := by
    rcases hon with hqz | hqz
    · -- q at z's suit: the cross reads flipSuit z (the partner suit)
      have honf : (Card.flipSuit z).suit = z.suit ∨
          (Card.flipSuit z).suit = z.suit.flipPair := by
        show z.suit.flipPair = z.suit ∨ z.suit.flipPair = z.suit.flipPair
        exact Or.inr rfl
      have hifff := h.stacked_iff (Card.flipSuit z) honf
      rw [Card.flipSuit_rank, Card.swapTwin_self_right] at hifff
      simp only [Card.flipSuit_suit] at hifff
      -- hifff : M.heights q.suit > z.rank ↔ S.heights z.suit.flipPair > z.rank
      rw [Card.flipSuit_suit, hqz] at hpart
      rw [hqz]
      exact hifff.mpr hpart
    · -- q at the partner suit: the cross reads z
      have honz : z.suit = z.suit ∨ z.suit = z.suit.flipPair := Or.inl rfl
      have hiffz := h.stacked_iff z honz
      rw [Card.IsTwinMap.rank h.isTwinMap z, Card.swapTwin_self_left] at hiffz
      simp only [Card.flipSuit_suit] at hiffz
      -- hiffz : M.heights z.suit.flipPair > z.rank ↔ S.heights z.suit > z.rank
      rw [Card.flipSuit_suit, hqz, Suit.flipPair_flipPair] at hpart
      rw [hqz]
      exact hiffz.mpr hpart
  -- the in-between non-pair cuts
  have hcuts : ∀ r : Rank, r.toIdx < q.rank.toIdx → r.toIdx ≠ z.rank.toIdx →
      M.heights q.suit > r.toIdx := by
    intro r hr hrne
    have honr : (Card.mk q.suit r).suit = z.suit ∨
        (Card.mk q.suit r).suit = z.suit.flipPair := by
      show q.suit = z.suit ∨ q.suit = z.suit.flipPair
      exact hon
    have hiffR := h.stacked_iff (Card.mk q.suit r) honr
    rw [Card.IsTwinMap.rank h.isTwinMap (Card.mk q.suit r)] at hiffR
    have hcR : Card.swapTwin z (Card.mk q.suit r) = Card.mk q.suit r := by
      refine Card.swapTwin_of_ne ?_ ?_
      · intro hcon
        have h1 : z.rank = (Card.mk q.suit r).rank := (congrArg Card.rank hcon).symm
        have h2 : (Card.mk q.suit r).rank = r := rfl
        rw [h2] at h1
        exact hrne (by rw [h1])
      · intro hcon
        have h1 : z.rank = (Card.mk q.suit r).rank := (congrArg Card.rank hcon).symm
        have h2 : (Card.mk q.suit r).rank = r := rfl
        rw [h2] at h1
        exact hrne (by rw [h1])
    rw [hcR] at hiffR
    have h2 : (Card.mk q.suit r).rank.toIdx = r.toIdx := rfl
    refine hiffR.mpr ?_
    rw [h2, hq]
    exact hr
  -- the assembly: the trichotomy on the mirror's rung — the cuts
  -- (with the push excluding the pair rank) close the low case
  rcases Nat.lt_trichotomy (M.heights q.suit) (q.rank.toIdx) with hlt' | heq' | hgt'
  · exfalso
    have hk13 := Rank.toIdx_lt q.rank
    have hk : M.heights q.suit < 13 :=
      Nat.lt_of_lt_of_le hlt' (Nat.le_of_lt hk13)
    obtain ⟨r, hr⟩ := Rank.exists_toIdx (M.heights q.suit) hk
    have hrne : r.toIdx ≠ z.rank.toIdx := by
      intro hcon
      have h1 : z.rank.toIdx < M.heights q.suit := hpush
      rw [← hcon, ← hr] at h1
      exact Nat.lt_irrefl _ h1
    have hc := hcuts r (hr ▸ hlt') hrne
    rw [hr] at hc
    exact absurd hc (Nat.lt_irrefl (M.heights q.suit))
  · exact heq'
  · exact absurd hgt' hle


/-! ## §11. The growth-engaged window -/

/-- **The window's episode phase**: the play's position relative to
the (at most one) growth episode.  `pre` — the correspondence is the
base `swapTwin z`; `mid strand β` — the growth fired (the mirror's
stranded copy `strand` sits at the mirror base `β`), the
correspondence is the identity frame with the single strand;
`post` — the catch-up drained, the correspondence is the plain
identity. -/
inductive State.WindowEp
  | pre
  | mid (strand : Card) (β : Base)
  | post

/-- **The phase invariant** the run induction carries: the
correspondence appropriate to the phase, plus the phase's side
conditions. -/
abbrev State.WindowInv (z : Card) (σ : Suit) (S M : State) : State.WindowEp → Prop
  | .pre => State.TwinCorr (Card.swapTwin z) σ S M ∧
      (∀ a, ∀ c ∈ S.hidden a, Card.swapTwin z c = c) ∧
      (∀ c ∈ S.stock.cards, Card.swapTwin z c = c)
  | .mid strand β => State.TwinCorrX id σ S M [strand] ∧
      M.board.bottomOf strand = some β ∧
      (strand = z ∨ strand = Card.flipSuit z)
  | .post => State.TwinCorr id σ S M

/-- **The growth-engaged play condition** (`playWindow'`): each move
must satisfy its phase's condition at the state it is played from.
PRE-episode: the old window's clauses, with the on-suit `pileStack`
skew WEAKENED — a PAIR card's stack may instead carry the growth's
source-side premises (the twin seated and bare, the two corner
freedoms), and a failed skew then ROUTES TO THE GROWTH (the phase
turns `mid`).  MID-episode: draws, `deckStack`s (any — their frame
lemmas carry no X-premises), `pileStack`s off the strand's mirror
base, and the TABLEAU kinds — reveals, deckPiles and stackPiles —
with their landing-seat clauses (the landing base and the moved
card off the strand's mirror base; the landing seat off the
strand's column; the landing card not in the strand's column);
pilePiles stay excluded mid-episode (the mirror-side run-placement
premise).  The CATCH-UP is the strand's own `pileStack` (with its
skew), draining to `post`.  POST-episode: no conditions (the
identity correspondence aligns everything —
`State.TwinCore.heights_eq_of_fix`).  The `[]` case demands the
episode drained. -/
def State.playWindow' (z : Card) (σ : Suit) (ep : State.WindowEp) (st : State) :
    List Move → Bool
  | [] => match ep with
    | .mid _ _ => false
    | _ => true
  | m :: ms =>
      match st.apply m with
      | none => false
      | some st' =>
          match ep, m with
          | .post, _ => State.playWindow' z σ .post st' ms
          | .pre, .draw | .pre, .reveal _ | .pre, .deckPile _ _ | .pre, .pilePile _ _ =>
              State.playWindow' z σ .pre st' ms
          | .pre, .deckStack q =>
              (decide (q.suit ≠ σ ∧ q.suit ≠ σ.flipPair) ||
                (decide (q.rank.toIdx ≤ st.heights (Card.flipSuit q).suit) &&
                 decide (Card.swapTwin z q = q))) &&
              State.playWindow' z σ .pre st' ms
          | .pre, .pileStack q =>
              (decide (q.suit ≠ σ ∧ q.suit ≠ σ.flipPair) ||
                decide (q.rank.toIdx ≤ st.heights (Card.flipSuit q).suit) ||
                decide ((q = z ∨ q = Card.flipSuit z) ∧
                  (st.board.bottomOf (Card.flipSuit q)).isSome ∧
                  st.board.topOf (Sum.inr (Card.flipSuit q)) = none ∧
                  (st.board.bottomOf q).elim true
                    (fun b => decide (b ≠ Sum.inr q ∧ b ≠ Sum.inr (Card.flipSuit q))) ∧
                  (st.board.bottomOf (Card.flipSuit q)).elim true
                    (fun b => decide (b ≠ Sum.inr q ∧ b ≠ Sum.inr (Card.flipSuit q)))) ||
                decide (Card.swapTwin z q = q ∧
                  z.rank.toIdx < st.heights (Card.flipSuit q).suit)) &&
              (if (q.suit ≠ σ ∧ q.suit ≠ σ.flipPair) ∨
                  (q.rank.toIdx ≤ st.heights (Card.flipSuit q).suit ∨
                  (Card.swapTwin z q = q ∧
                    z.rank.toIdx < st.heights (Card.flipSuit q).suit))
               then State.playWindow' z σ .pre st' ms
               else State.playWindow' z σ
                 (.mid (Card.swapTwin z q)
                   (match st.board.bottomOf q with
                    | some bq => Base.relabel (Card.swapTwin z) bq
                    | none => Sum.inr q)) st' ms)
          | .pre, .stackPile c _ =>
              (decide (c.suit ≠ σ ∧ c.suit ≠ σ.flipPair) ||
                decide (st.heights (Card.flipSuit c).suit ≤ c.rank.toIdx + 1) ||
                decide (Card.swapTwin z c = c ∧
                  c.rank.toIdx + 1 ≠ z.rank.toIdx)) &&
              State.playWindow' z σ .pre st' ms
          | .mid strand β, .draw => State.playWindow' z σ (.mid strand β) st' ms
          | .mid strand β, .deckStack _ => State.playWindow' z σ (.mid strand β) st' ms
          | .mid strand β, .reveal c =>
              decide (c ≠ strand ∧ β ≠ Sum.inr c ∧
                ((st.board.bottomOf c).elim true
                  (fun b => match b with
                   | Sum.inr r => (st.pileOfTopHidden r).elim true
                     (fun a => decide (β ≠ st.hiddenBase a))
                   | Sum.inl _ => true))) &&
              State.playWindow' z σ (.mid strand β) st' ms
          | .mid strand β, .deckPile q b =>
              decide (b ≠ β ∧ β ≠ Sum.inr q ∧
                (strand :: st.board.aboveOf strand).all
                  (fun y => decide (b ≠ Sum.inr y)) ∧
                (match b with
                 | Sum.inr d => decide (d ≠ strand ∧ d ∉ st.board.aboveOf strand)
                 | Sum.inl _ => true) == true) &&
              State.playWindow' z σ (.mid strand β) st' ms
          | .mid strand β, .stackPile c b =>
              decide (b ≠ β ∧ β ≠ Sum.inr c ∧
                (strand :: st.board.aboveOf strand).all
                  (fun y => decide (b ≠ Sum.inr y)) ∧
                (match b with
                 | Sum.inr d => decide (d ≠ strand ∧ d ∉ st.board.aboveOf strand)
                 | Sum.inl _ => true) == true) &&
              State.playWindow' z σ (.mid strand β) st' ms
          | .mid _ _, .pilePile _ _ => false
          | .mid strand β, .pileStack q =>
              if q = strand then
                (decide (q.rank.toIdx ≤ st.heights (Card.flipSuit q).suit) &&
                  State.playWindow' z σ .post st' ms)
              else
                (decide (Sum.inr q ≠ β) &&
                  State.playWindow' z σ (.mid strand β) st' ms)

/-- **Growth-engaged window-solvability**: the source wins by a play
the growth-engaged window admits (from the pre-episode phase). -/
def State.solvableWindow' (z : Card) (σ : Suit) (S : State) : Prop :=
  ∃ play W, S.run play = some W ∧ W.isWin = true ∧
    State.playWindow' z σ State.WindowEp.pre S play = true

/-- **The pointwise-fixed step**: at a correspondence whose `ρ` fixes
every card (the post-episode identity), EVERY move translates
verbatim — the clean kinds through `apply_clean` (the hidden/stock
premises are `hfix` instances), the on-suit foundation kinds with
the rung alignments derived from the rung equality
(`State.TwinCore.heights_eq_of_fix`): NO skew or anti-skew condition
remains. -/
theorem State.twinCorr_step_fix {ρ σ S M R m}
    (hcorr : State.TwinCorr ρ σ S M) (hfix : ∀ c, ρ c = c)
    (hMle : ∀ s, M.heights s ≤ 13) (hwf : S.WF)
    (hS : S.apply m = some R) :
    ∃ N, M.apply (Move.relabelTwin ρ m) = some N ∧ State.TwinCorr ρ σ R N := by
  have hrung : ∀ s, M.heights s = S.heights s :=
    State.TwinCore.heights_eq_of_fix hcorr.toTwinCore hfix hMle (fun s => hwf.heights_le s)
  have hhid' : ∀ a, ∀ c ∈ S.hidden a, ρ c = c := fun a c _ => hfix c
  have hstock' : ∀ c ∈ S.stock.cards, ρ c = c := fun c _ => hfix c
  cases m with
  | draw => exact State.TwinCorr.apply_clean hcorr hhid' hstock' rfl hS
  | reveal c => exact State.TwinCorr.apply_clean hcorr hhid' hstock' rfl hS
  | deckPile c b => exact State.TwinCorr.apply_clean hcorr hhid' hstock' rfl hS
  | pilePile c b => exact State.TwinCorr.apply_clean hcorr hhid' hstock' rfl hS
  | deckStack q =>
      by_cases hon : q.suit = σ ∨ q.suit = σ.flipPair
      · have hSiff := apply_deckStack_iff.mp hS
        obtain ⟨hprev, hrk, rfl⟩ := hSiff
        have hpinn : M.heights q.suit = q.rank.toIdx := by
          rw [hrung q.suit]; exact hrk.symm
        obtain ⟨N, hfire, hX⟩ := State.TwinCorrX.apply_deckStack_onsuit
          (State.TwinCorr.toTwinCorrX hcorr) hon (hfix q) hS hpinn
        refine ⟨N, ?_, hX.toCorr⟩
        show M.apply (Move.deckStack (ρ q)) = some N
        rw [hfix q]
        exact hfire
      · exact State.TwinCorr.apply_clean hcorr hhid' hstock'
          (by simp only [Move.twinClean, decide_eq_true_iff]
              exact ⟨fun h => hon (Or.inl h), fun h => hon (Or.inr h)⟩) hS
  | pileStack q =>
      by_cases hon : q.suit = σ ∨ q.suit = σ.flipPair
      · have hSiff := apply_pileStack_iff.mp hS
        obtain ⟨htop, bq, hbot, hrk, rfl⟩ := hSiff
        have halign : M.heights (ρ q).suit = q.rank.toIdx := by
          rw [hfix q, hrung q.suit]; exact hrk.symm
        obtain ⟨N, hfire, hX⟩ := State.TwinCorrX.apply_pileStack_onsuit
          (State.TwinCorr.toTwinCorrX hcorr) hon hS halign (by simp) (by simp)
        exact ⟨N, hfire, hX.toCorr⟩
      · exact State.TwinCorr.apply_clean hcorr hhid' hstock'
          (by simp only [Move.twinClean, decide_eq_true_iff]
              exact ⟨fun h => hon (Or.inl h), fun h => hon (Or.inr h)⟩) hS
  | stackPile c b =>
      by_cases hon : c.suit = σ ∨ c.suit = σ.flipPair
      · have hSiff := apply_stackPile_iff.mp hS
        obtain ⟨hrk, hcp, bd, hatt, rfl⟩ := hSiff
        have halign : M.heights (ρ c).suit = c.rank.toIdx + 1 := by
          rw [hfix c, hrung c.suit]; exact hrk.symm
        obtain ⟨N, hfire, hX⟩ := State.TwinCorrX.apply_stackPile_onsuit
          (State.TwinCorr.toTwinCorrX hcorr) hwf hon (by simp) hS halign
          (by simp) (by simp) (by simp) (by simp)
        exact ⟨N, hfire, hX.toCorr⟩
      · exact State.TwinCorr.apply_clean hcorr hhid' hstock'
          (by simp only [Move.twinClean, decide_eq_true_iff]
              exact ⟨fun h => hon (Or.inl h), fun h => hon (Or.inr h)⟩) hS

/-- The run composition: one firing response prepended to a winning
mirror suffix is a winning mirror run. -/
theorem State.run_cons_comp {M : State} {r : Move} {N Nf : State} {nplay' : List Move}
    (hfire : M.apply r = some N) (hrun' : N.run nplay' = some Nf) :
    M.run (r :: nplay') = some Nf := by
  simp only [State.run, hfire]
  exact hrun'

/-- **The growth-engaged run**: a play the growth-engaged window
admits replays through the correspondence — the mirror's play is
constructed PIECEWISE (the phase-appropriate response to each source
move), the invariants (the 52-count, the source's WF, the phase
correspondence, the strand's mirror base) ride along, and the final
correspondence exists at whatever map the phases reached. -/
theorem State.twinCorr_run_window' (z : Card) :
    ∀ (play : List Move) (S M : State) (ep : State.WindowEp),
    (∀ s, M.heights s ≤ 13) →
    S.WF →
    State.WindowInv z z.suit S M ep →
    State.playWindow' z z.suit ep S play = true →
    ∀ {W : State}, S.run play = some W →
    ∃ N nplay, M.run nplay = some N ∧ ∃ ρ', State.TwinCorr ρ' z.suit W N := by
  intro play
  induction play with
  | nil =>
      intro S M ep hMle hwf hinv hwin W hrun
      have h1 : S.run [] = some S := rfl
      have hW : W = S := (Option.some.inj (h1.symm.trans hrun)).symm
      subst hW
      rcases ep with _ | ⟨strand, β⟩ | _
      · rcases hinv with ⟨hcorr, -, -⟩
        exact ⟨M, [], rfl, Card.swapTwin z, hcorr⟩
      · simp only [State.playWindow'] at hwin
        exact absurd hwin (by simp)
      · have hcorr : State.TwinCorr id z.suit W M := hinv
        exact ⟨M, [], rfl, id, hcorr⟩
  | cons m ms ih =>
      intro S M ep hMle hwf hinv hwin W hrun
      simp only [State.run] at hrun
      cases hS : S.apply m with
      | none => rw [hS] at hrun; exact absurd hrun (by simp)
      | some R =>
          rw [hS] at hrun
          rcases ep with _ | ⟨strand, β⟩ | _
          · -- ===== PRE-EPISODE =====
            rcases hinv with ⟨hcorr, hhid, hstock⟩
            have hihpre := fun (N : State)
                (hfire : M.apply (Move.relabelTwin (Card.swapTwin z) m) = some N)
                (hcorrR : State.TwinCorr (Card.swapTwin z) z.suit R N)
                (hwin' : State.playWindow' z z.suit State.WindowEp.pre R ms = true) =>
              ih R N State.WindowEp.pre (State.heights_le_apply hMle hfire)
                (apply_wf hwf _ R hS)
                ⟨hcorrR, fun a c hc => hhid a c (State.hidden_sub_apply hS a c hc),
                  fun c hc => hstock c (State.stock_cards_sub_apply hS c hc)⟩ hwin' hrun
            cases m with
            | draw =>
                simp only [State.playWindow', hS] at hwin
                obtain ⟨N, hfire, hcorrR⟩ :=
                  State.TwinCorr.apply_clean hcorr hhid hstock rfl hS
                obtain ⟨Nf, nplay', hrun', ρ', hcorr'⟩ := hihpre N hfire hcorrR hwin
                exact ⟨Nf, Move.relabelTwin (Card.swapTwin z) Move.draw :: nplay',
                  State.run_cons_comp hfire hrun', ρ', hcorr'⟩
            | reveal c =>
                simp only [State.playWindow', hS] at hwin
                obtain ⟨N, hfire, hcorrR⟩ :=
                  State.TwinCorr.apply_clean hcorr hhid hstock rfl hS
                obtain ⟨Nf, nplay', hrun', ρ', hcorr'⟩ := hihpre N hfire hcorrR hwin
                exact ⟨Nf, Move.relabelTwin (Card.swapTwin z) (Move.reveal c) :: nplay',
                  State.run_cons_comp hfire hrun', ρ', hcorr'⟩
            | deckPile c b =>
                simp only [State.playWindow', hS] at hwin
                obtain ⟨N, hfire, hcorrR⟩ :=
                  State.TwinCorr.apply_clean hcorr hhid hstock rfl hS
                obtain ⟨Nf, nplay', hrun', ρ', hcorr'⟩ := hihpre N hfire hcorrR hwin
                exact ⟨Nf,
                  Move.relabelTwin (Card.swapTwin z) (Move.deckPile c b) :: nplay',
                  State.run_cons_comp hfire hrun', ρ', hcorr'⟩
            | pilePile c b =>
                simp only [State.playWindow', hS] at hwin
                obtain ⟨N, hfire, hcorrR⟩ :=
                  State.TwinCorr.apply_clean hcorr hhid hstock rfl hS
                obtain ⟨Nf, nplay', hrun', ρ', hcorr'⟩ := hihpre N hfire hcorrR hwin
                exact ⟨Nf,
                  Move.relabelTwin (Card.swapTwin z) (Move.pilePile c b) :: nplay',
                  State.run_cons_comp hfire hrun', ρ', hcorr'⟩
            | deckStack q =>
                simp only [State.playWindow', hS, Bool.and_eq_true, Bool.or_eq_true,
                  Bool.and_eq_true, decide_eq_true_iff] at hwin
                obtain ⟨hcl, hwin'⟩ := hwin
                have hok : Move.windowOK (Card.swapTwin z) z.suit S (Move.deckStack q)
                    = true := by
                  simp only [Move.windowOK, Bool.or_eq_true, Bool.and_eq_true,
                    decide_eq_true_iff]
                  exact hcl
                obtain ⟨N, hfire, hcorrR⟩ :=
                  State.twinCorr_step_window hcorr hMle hwf hhid hstock hok hS
                obtain ⟨Nf, nplay', hrun', ρ', hcorr'⟩ := hihpre N hfire hcorrR hwin'
                exact ⟨Nf,
                  Move.relabelTwin (Card.swapTwin z) (Move.deckStack q) :: nplay',
                  State.run_cons_comp hfire hrun', ρ', hcorr'⟩
            | stackPile c b =>
                simp only [State.playWindow', hS, Bool.and_eq_true, Bool.or_eq_true,
                  decide_eq_true_iff] at hwin
                obtain ⟨hcl, hwin'⟩ := hwin
                rcases hcl with (hoff | hanti) | hnew
                · obtain ⟨N, hfire, hcorrR⟩ :=
                    State.TwinCorr.apply_clean hcorr hhid hstock
                    (by simp only [Move.twinClean, decide_eq_true_iff]
                        exact hoff) hS
                  obtain ⟨Nf, nplay', hrun', ρ', hcorr'⟩ :=
                    hihpre N hfire hcorrR hwin'
                  exact ⟨Nf,
                    Move.relabelTwin (Card.swapTwin z) (Move.stackPile c b) :: nplay',
                    State.run_cons_comp hfire hrun', ρ', hcorr'⟩
                · have hok : Move.windowOK (Card.swapTwin z) z.suit S
                      (Move.stackPile c b) = true := by
                    simp only [Move.windowOK, Bool.or_eq_true, decide_eq_true_iff]
                    exact Or.inr hanti
                  obtain ⟨N, hfire, hcorrR⟩ :=
                    State.twinCorr_step_window hcorr hMle hwf hhid hstock hok hS
                  obtain ⟨Nf, nplay', hrun', ρ', hcorr'⟩ :=
                    hihpre N hfire hcorrR hwin'
                  exact ⟨Nf,
                    Move.relabelTwin (Card.swapTwin z) (Move.stackPile c b) :: nplay',
                    State.run_cons_comp hfire hrun', ρ', hcorr'⟩
                · -- the non-pair, non-adjacent worry-back: the rung DERIVED
                  obtain ⟨hcρ, hrne⟩ := hnew
                  by_cases hon : c.suit = z.suit ∨ c.suit = z.suit.flipPair
                  · have hSiff := apply_stackPile_iff.mp hS
                    obtain ⟨hrk, hcp, bd, hatt, rfl⟩ := hSiff
                    have halign : M.heights (Card.swapTwin z c).suit
                        = c.rank.toIdx + 1 :=
                      State.TwinCore.rung_eq_unstack_of_ne hcorr.toTwinCore hon hrk.symm
                        hcρ hrne (hMle (Card.swapTwin z c).suit)
                    obtain ⟨N, hfire, hX⟩ := State.TwinCorrX.apply_stackPile_onsuit
                      (State.TwinCorr.toTwinCorrX hcorr) hwf hon (by simp) hS halign
                      (by simp) (by simp) (by simp) (by simp)
                    obtain ⟨Nf, nplay', hrun', ρ', hcorr'⟩ :=
                      hihpre N hfire hX.toCorr hwin'
                    exact ⟨Nf,
                      Move.relabelTwin (Card.swapTwin z) (Move.stackPile c b) :: nplay',
                      State.run_cons_comp hfire hrun', ρ', hcorr'⟩
                  · obtain ⟨N, hfire, hcorrR⟩ :=
                      State.TwinCorr.apply_clean hcorr hhid hstock
                      (by simp only [Move.twinClean, decide_eq_true_iff]
                          exact ⟨fun h => hon (Or.inl h), fun h => hon (Or.inr h)⟩) hS
                    obtain ⟨Nf, nplay', hrun', ρ', hcorr'⟩ :=
                      hihpre N hfire hcorrR hwin'
                    exact ⟨Nf,
                      Move.relabelTwin (Card.swapTwin z) (Move.stackPile c b) :: nplay',
                      State.run_cons_comp hfire hrun', ρ', hcorr'⟩
            | pileStack q =>
                by_cases hif : (q.suit ≠ z.suit ∧ q.suit ≠ z.suit.flipPair) ∨
                  (q.rank.toIdx ≤ S.heights (Card.flipSuit q).suit ∨
                  (Card.swapTwin z q = q ∧
                    z.rank.toIdx < S.heights (Card.flipSuit q).suit))
                · -- the verbatim regime: off-suit, skewed, or the
                  -- partner-past post-equalization climb
                  simp only [State.playWindow', hS, if_pos hif, Bool.and_eq_true] at hwin
                  obtain ⟨-, hwin'⟩ := hwin
                  rcases hif with hoff | hmid
                  · have hok : Move.windowOK (Card.swapTwin z) z.suit S
                          (Move.pileStack q) = true := by
                      simp only [Move.windowOK, Bool.or_eq_true, decide_eq_true_iff]
                      exact Or.inl hoff
                    obtain ⟨N, hfire, hcorrR⟩ :=
                      State.twinCorr_step_window hcorr hMle hwf hhid hstock hok hS
                    obtain ⟨Nf, nplay', hrun', ρ', hcorr'⟩ :=
                      hihpre N hfire hcorrR hwin'
                    exact ⟨Nf,
                      Move.relabelTwin (Card.swapTwin z) (Move.pileStack q) :: nplay',
                      State.run_cons_comp hfire hrun', ρ', hcorr'⟩
                  rcases hmid with hskew | hnew
                  · have hok : Move.windowOK (Card.swapTwin z) z.suit S
                          (Move.pileStack q) = true := by
                      simp only [Move.windowOK, Bool.or_eq_true, decide_eq_true_iff]
                      exact Or.inr hskew
                    obtain ⟨N, hfire, hcorrR⟩ :=
                      State.twinCorr_step_window hcorr hMle hwf hhid hstock hok hS
                    obtain ⟨Nf, nplay', hrun', ρ', hcorr'⟩ :=
                      hihpre N hfire hcorrR hwin'
                    exact ⟨Nf,
                      Move.relabelTwin (Card.swapTwin z) (Move.pileStack q) :: nplay',
                      State.run_cons_comp hfire hrun', ρ', hcorr'⟩
                  · -- the non-pair post-equalization climb: the rung
                    -- derived (the partner past the pair rank)
                    obtain ⟨hcρ, hpart⟩ := hnew
                    by_cases hon : q.suit = z.suit ∨ q.suit = z.suit.flipPair
                    · have hSiff := apply_pileStack_iff.mp hS
                      obtain ⟨htop, bq, hbot, hrk, rfl⟩ := hSiff
                      have halign : M.heights (Card.swapTwin z q).suit
                          = q.rank.toIdx :=
                        State.TwinCore.rung_eq_of_partner_past hcorr.toTwinCore hon
                          hrk.symm hcρ hpart (hMle (Card.swapTwin z q).suit)
                      obtain ⟨N, hfire, hX⟩ := State.TwinCorrX.apply_pileStack_onsuit
                        (State.TwinCorr.toTwinCorrX hcorr) hon hS halign (by simp) (by simp)
                      obtain ⟨Nf, nplay', hrun', ρ', hcorr'⟩ :=
                        hihpre N hfire hX.toCorr hwin'
                      exact ⟨Nf,
                        Move.relabelTwin (Card.swapTwin z) (Move.pileStack q) :: nplay',
                        State.run_cons_comp hfire hrun', ρ', hcorr'⟩
                    · obtain ⟨N, hfire, hcorrR⟩ :=
                        State.TwinCorr.apply_clean hcorr hhid hstock
                        (by simp only [Move.twinClean, decide_eq_true_iff]
                            exact ⟨fun h => hon (Or.inl h), fun h => hon (Or.inr h)⟩) hS
                      obtain ⟨Nf, nplay', hrun', ρ', hcorr'⟩ :=
                        hihpre N hfire hcorrR hwin'
                      exact ⟨Nf,
                        Move.relabelTwin (Card.swapTwin z) (Move.pileStack q) :: nplay',
                        State.run_cons_comp hfire hrun', ρ', hcorr'⟩
                · -- the GROWTH: on-suit, failed skew, pair card
                  have hon : q.suit = z.suit ∨ q.suit = z.suit.flipPair := by
                    by_cases hq1 : q.suit = z.suit
                    · exact Or.inl hq1
                    · by_cases hq2 : q.suit = z.suit.flipPair
                      · exact Or.inr hq2
                      · exact absurd (Or.inl ⟨hq1, hq2⟩) hif
                  have hnoskew : ¬ (q.rank.toIdx ≤
                      S.heights (Card.flipSuit q).suit) := fun hskew => hif (Or.inr (Or.inl hskew))
                  simp only [State.playWindow', hS, if_neg hif, Bool.and_eq_true,
                    Bool.or_eq_true, Bool.or_eq_true, decide_eq_true_iff] at hwin
                  obtain ⟨hcl, hwin'⟩ := hwin
                  rcases hcl with ((hoff | hskew) | hgp) | hpp
                  · exact (hif (Or.inl hoff)).elim
                  · exact (hif (Or.inr (Or.inl hskew))).elim
                  · obtain ⟨hpair, hseated, hbareS, hcbqB, hcbq'B⟩ := hgp
                    obtain ⟨bq', hbq'⟩ : ∃ b, S.board.bottomOf (Card.flipSuit q)
                        = some b := by
                      cases hS2 : S.board.bottomOf (Card.flipSuit q) with
                      | none => rw [hS2] at hseated; exact absurd hseated (by simp)
                      | some b => exact ⟨b, rfl⟩
                    have hflip : S.board.topOf (Sum.inr (Card.flipSuit q)) = none :=
                      hbareS
                    have hSiff := apply_pileStack_iff.mp hS
                    obtain ⟨htop, bq, hbot, hrk, rfl⟩ := hSiff
                    have hcbq : bq ≠ Sum.inr q ∧ bq ≠ Sum.inr (Card.flipSuit q) := by
                      have h2 : decide (bq ≠ Sum.inr q ∧ bq ≠ Sum.inr (Card.flipSuit q))
                          = true := by
                        have h1 := hcbqB
                        rw [hbot] at h1
                        exact h1
                      exact decide_eq_true_iff.mp h2
                    have hcbq' : bq' ≠ Sum.inr q ∧ bq' ≠ Sum.inr (Card.flipSuit q) := by
                      have h2 : decide (bq' ≠ Sum.inr q ∧ bq' ≠ Sum.inr (Card.flipSuit q))
                          = true := by
                        have h1 := hcbq'B
                        rw [hbq'] at h1
                        exact h1
                      exact decide_eq_true_iff.mp h2
                    have hmis : M.heights (Card.swapTwin z q).suit ≠ q.rank.toIdx :=
                      State.TwinCore.rung_ne_of_noskew_pair hcorr.toTwinCore hon hrk.symm
                        hpair hnoskew
                    have hcompid : (Card.swapTwin (Card.swapTwin z q) ∘
                        Card.swapTwin z) = id := by
                      rcases hpair with hp | hp
                      · rw [hp]
                        show (Card.swapTwin (Card.swapTwin z z) ∘ Card.swapTwin z) = id
                        rw [Card.swapTwin_self_left, Card.swapTwin_pair_comp]
                      · rw [hp]
                        show (Card.swapTwin (Card.swapTwin z (Card.flipSuit z)) ∘
                          Card.swapTwin z) = id
                        rw [Card.swapTwin_self_right]
                        funext x
                        exact Card.swapTwin_swapTwin z x
                    obtain ⟨N, hfire, hX⟩ := State.TwinCorr.apply_pileStack_grow_X hcorr
                      hon hS hbot hbq' hflip hmis hcbq hcbq' hcompid.symm
                    -- the strand's mirror base, initialized from the pre-growth
                    -- conjugation and stable through the growth's response
                    have htopS : S.board.topOf bq = some q :=
                      (Board.bottomOf_eq S.board q bq).mp hbot
                    have htopM : M.board.topOf (Base.relabel (Card.swapTwin z) bq)
                        = some (Card.swapTwin z q) := by
                      have h1 := hcorr.board_eq (Base.relabel (Card.swapTwin z) bq)
                      rw [Base.relabel_invol hcorr.isTwinMap bq] at h1
                      rw [h1, htopS, Option.map_some]
                    have hbqρ : M.board.bottomOf (Card.swapTwin z q)
                        = some (Base.relabel (Card.swapTwin z) bq) :=
                      (Board.bottomOf_eq M.board (Card.swapTwin z q)
                        (Base.relabel (Card.swapTwin z) bq)).mpr htopM
                    have hSiffN := apply_pileStack_iff.mp hfire
                    obtain ⟨htopN, βr, hbotN, hrkN, hSN⟩ := hSiffN
                    have hbase : N.board.bottomOf (Card.swapTwin z q)
                        = some (Base.relabel (Card.swapTwin z) bq) := by
                      rw [hSN]
                      show (M.board.detach βr).bottomOf (Card.swapTwin z q)
                        = some (Base.relabel (Card.swapTwin z) bq)
                      refine Board.bottomOf_detach_ne hbqρ ?_
                      intro hcon
                      have h2 : M.board.topOf βr = some (Card.flipSuit (Card.swapTwin z q)) :=
                        (Board.bottomOf_eq M.board _ βr).mp hbotN
                      rw [← hcon] at h2
                      exact absurd (Option.some.inj (htopM.symm.trans h2))
                        (Card.flipSuit_ne (Card.swapTwin z q)).symm
                    have hstrand : Card.swapTwin z q = z ∨
                        Card.swapTwin z q = Card.flipSuit z := by
                      rcases hpair with hp | hp
                      · rw [hp, Card.swapTwin_self_left]
                        exact Or.inr rfl
                      · rw [hp, Card.swapTwin_self_right]
                        exact Or.inl rfl
                    rw [hbot] at hwin'
                    obtain ⟨Nf, nplay', hrun', ρ', hcorr'⟩ := ih _ N
                      (.mid (Card.swapTwin z q)
                        (Base.relabel (Card.swapTwin z) bq))
                      (State.heights_le_apply hMle hfire) (apply_wf hwf _ _ hS)
                      ⟨hX, hbase, hstrand⟩ hwin' hrun
                    exact ⟨Nf,
                      (Move.pileStack (Card.flipSuit (Card.swapTwin z q))) :: nplay',
                      State.run_cons_comp hfire hrun', ρ', hcorr'⟩
                  · -- the partner-past disjunct cannot reach the growth branch
                    exact (hif (Or.inr (Or.inr hpp))).elim
          · -- ===== MID-EPISODE =====
            rcases hinv with ⟨hframe, hbase, hstrand⟩
            have hrung : ∀ s, M.heights s = S.heights s :=
              State.TwinCore.heights_eq_of_fix hframe.core (fun _ => rfl) hMle
                (fun s => hwf.heights_le s)
            have honst : strand.suit = z.suit ∨ strand.suit = z.suit.flipPair := by
              rcases hstrand with hs | hs
              · rw [hs]; exact Or.inl rfl
              · rw [hs, Card.flipSuit_suit]; exact Or.inr rfl
            cases m with
            | draw =>
                simp only [State.playWindow', hS] at hwin
                obtain ⟨N, hfire, hX'⟩ := State.TwinCorrX.apply_draw hframe hS
                have hSN := apply_draw_iff.mp hfire
                have hbaseN : N.board.bottomOf strand = some β := by
                  rw [hSN]; exact hbase
                obtain ⟨Nf, nplay', hrun', ρ', hcorr'⟩ := ih _ N (.mid strand β)
                  (State.heights_le_apply hMle hfire) (apply_wf hwf _ _ hS)
                  ⟨hX', hbaseN, hstrand⟩ hwin hrun
                exact ⟨Nf, Move.draw :: nplay', State.run_cons_comp hfire hrun', ρ', hcorr'⟩
            | deckStack q =>
                simp only [State.playWindow', hS] at hwin
                by_cases hon : q.suit = z.suit ∨ q.suit = z.suit.flipPair
                · have hSiff := apply_deckStack_iff.mp hS
                  obtain ⟨hprev, hrk, rfl⟩ := hSiff
                  have hpinn : M.heights q.suit = q.rank.toIdx := by
                    rw [hrung q.suit]; exact hrk.symm
                  obtain ⟨N, hfire, hX'⟩ := State.TwinCorrX.apply_deckStack_onsuit
                    hframe hon rfl hS hpinn
                  obtain ⟨-, -, hSN⟩ := apply_deckStack_iff.mp hfire
                  have hbaseN : N.board.bottomOf strand = some β := by
                    rw [hSN]; exact hbase
                  obtain ⟨Nf, nplay', hrun', ρ', hcorr'⟩ := ih _ N (.mid strand β)
                    (State.heights_le_apply hMle hfire) (apply_wf hwf _ _ hS)
                    ⟨hX', hbaseN, hstrand⟩ hwin hrun
                  exact ⟨Nf, Move.relabelTwin id (Move.deckStack q) :: nplay',
                    State.run_cons_comp hfire hrun', ρ', hcorr'⟩
                · obtain ⟨N, hfire, hX'⟩ := State.TwinCorrX.apply_deckStack_off hframe
                    (⟨fun hcon => hon (Or.inl hcon), fun hcon => hon (Or.inr hcon)⟩ :
                      q.suit ≠ z.suit ∧ q.suit ≠ z.suit.flipPair) hS
                  obtain ⟨-, -, hSN⟩ := apply_deckStack_iff.mp hfire
                  have hbaseN : N.board.bottomOf strand = some β := by
                    rw [hSN]; exact hbase
                  obtain ⟨Nf, nplay', hrun', ρ', hcorr'⟩ := ih _ N (.mid strand β)
                    (State.heights_le_apply hMle hfire) (apply_wf hwf _ _ hS)
                    ⟨hX', hbaseN, hstrand⟩ hwin hrun
                  exact ⟨Nf, Move.relabelTwin id (Move.deckStack q) :: nplay',
                    State.run_cons_comp hfire hrun', ρ', hcorr'⟩
            | pileStack q =>
                simp only [State.playWindow', hS] at hwin
                by_cases hq : q = strand
                · -- the CATCH-UP: the drain
                  rw [if_pos hq] at hwin
                  simp only [Bool.and_eq_true, decide_eq_true_iff] at hwin
                  obtain ⟨hskew, hwin'⟩ := hwin
                  rw [hq] at hS hskew
                  obtain ⟨N, hfire, hX'⟩ := State.TwinCorrX.apply_pileStack_catchup hframe
                    honst (by simp) hS hskew
                  simp [List.filter] at hX'
                  obtain ⟨Nf, nplay', hrun', ρ', hcorr'⟩ := ih _ N .post
                    (State.heights_le_apply hMle hfire) (apply_wf hwf _ _ hS)
                    hX'.toCorr hwin' hrun
                  exact ⟨Nf, Move.relabelTwin id (Move.pileStack strand) :: nplay',
                    State.run_cons_comp hfire hrun', ρ', hcorr'⟩
                · rw [if_neg hq] at hwin
                  simp only [Bool.and_eq_true, decide_eq_true_iff] at hwin
                  obtain ⟨hβne, hwin'⟩ := hwin
                  have hbare : ∀ x ∈ [strand],
                      M.board.bottomOf x ≠ some (Sum.inr (id q)) := by
                    intro x hx hcon
                    rw [List.mem_singleton.mp hx] at hcon
                    rw [hbase] at hcon
                    exact hβne (Option.some.inj hcon).symm
                  have hqX : id q ∉ [strand] := by
                    rw [List.mem_singleton]
                    exact fun hcon => hq hcon
                  by_cases hon : q.suit = z.suit ∨ q.suit = z.suit.flipPair
                  · have hSiff := apply_pileStack_iff.mp hS
                    obtain ⟨htop, bq, hbot, hrk, rfl⟩ := hSiff
                    have halign : M.heights (id q).suit = q.rank.toIdx := by
                      show M.heights q.suit = q.rank.toIdx
                      rw [hrung q.suit]; exact hrk.symm
                    obtain ⟨N, hfire, hX'⟩ := State.TwinCorrX.apply_pileStack_onsuit
                      hframe hon hS halign hqX hbare
                    have hSiffN := apply_pileStack_iff.mp hfire
                    obtain ⟨htopN, βq, hbotN, hrkN, hSN⟩ := hSiffN
                    have hbase' : N.board.bottomOf strand = some β := by
                      rw [hSN]
                      show (M.board.detach βq).bottomOf strand = some β
                      refine Board.bottomOf_detach_ne hbase ?_
                      intro hcon
                      have h1 : M.board.topOf β = some strand :=
                        (Board.bottomOf_eq M.board strand β).mp hbase
                      have h2 : M.board.topOf βq = some (id q) :=
                        (Board.bottomOf_eq M.board _ βq).mp hbotN
                      rw [← hcon] at h2
                      exact absurd (Option.some.inj (h1.symm.trans h2)) (fun h => hq h.symm)
                    obtain ⟨Nf, nplay', hrun', ρ', hcorr'⟩ := ih _ _ (.mid strand β)
                      (State.heights_le_apply hMle hfire) (apply_wf hwf _ _ hS)
                      ⟨hX', hbase', hstrand⟩ hwin' hrun
                    exact ⟨Nf, Move.relabelTwin id (Move.pileStack q) :: nplay',
                      State.run_cons_comp hfire hrun', ρ', hcorr'⟩
                  · obtain ⟨N, hfire, hX'⟩ := State.TwinCorrX.apply_pileStack_off hframe
                      (⟨fun hcon => hon (Or.inl hcon), fun hcon => hon (Or.inr hcon)⟩ :
                        q.suit ≠ z.suit ∧ q.suit ≠ z.suit.flipPair) hqX hS hbare
                    have hSiffN := apply_pileStack_iff.mp hfire
                    obtain ⟨htopN, βq, hbotN, hrkN, hSN⟩ := hSiffN
                    have hbase' : N.board.bottomOf strand = some β := by
                      rw [hSN]
                      show (M.board.detach βq).bottomOf strand = some β
                      refine Board.bottomOf_detach_ne hbase ?_
                      intro hcon
                      have h1 : M.board.topOf β = some strand :=
                        (Board.bottomOf_eq M.board strand β).mp hbase
                      have h2 : M.board.topOf βq = some q :=
                        (Board.bottomOf_eq M.board _ βq).mp hbotN
                      rw [← hcon] at h2
                      exact absurd (Option.some.inj (h1.symm.trans h2)) (fun h => hq h.symm)
                    obtain ⟨Nf, nplay', hrun', ρ', hcorr'⟩ := ih _ _ (.mid strand β)
                      (State.heights_le_apply hMle hfire) (apply_wf hwf _ _ hS)
                      ⟨hX', hbase', hstrand⟩ hwin' hrun
                    exact ⟨Nf, Move.relabelTwin id (Move.pileStack q) :: nplay',
                      State.run_cons_comp hfire hrun', ρ', hcorr'⟩
            | reveal c =>
                simp only [State.playWindow', hS, Bool.and_eq_true, decide_eq_true_iff]
                  at hwin
                have hSiff := apply_reveal_iff.mp hS
                obtain ⟨htop, r, a, bd, hbot, hp, hatt, rfl⟩ := hSiff
                obtain ⟨⟨hcne, hβc, helim⟩, hwin'⟩ := hwin
                -- reduce the hiddenBase clause (defeq-iota through the option elims)
                have hβhb : β ≠ S.hiddenBase a := by
                  have hb1 := helim
                  rw [hbot] at hb1
                  have hb2 : ((S.pileOfTopHidden r).elim true
                      (fun a' => decide (β ≠ S.hiddenBase a'))) = true := hb1
                  rw [hp] at hb2
                  have hb3 : decide (β ≠ S.hiddenBase a) = true := hb2
                  exact decide_eq_true_iff.mp hb3
                have hcX : c ∉ List.map id [strand] := by
                  simp only [List.map_id]
                  exact fun hcon => hcne (List.mem_singleton.mp hcon)
                have hcov : ∀ x ∈ [strand],
                    M.board.bottomOf x ≠ some (Sum.inr (id c)) := by
                  intro x hx hcon
                  rw [List.mem_singleton.mp hx] at hcon
                  rw [hbase] at hcon
                  exact hβc (Option.some.inj hcon)
                have hfree : ∀ x ∈ [strand],
                    M.board.bottomOf x ≠ some (S.hiddenBase a) := by
                  intro x hx hcon
                  rw [List.mem_singleton.mp hx] at hcon
                  rw [hbase] at hcon
                  exact hβhb (Option.some.inj hcon)
                obtain ⟨N, hfire, hX'⟩ := State.TwinCorrX.apply_reveal_X hframe hwf
                  (fun _ _ _ => rfl) hcX hS hbot hp hcov hfree
                have hSiffM := apply_reveal_iff.mp hfire
                obtain ⟨htopM, rM, aM, bdM, hbotM, hpM, hattM, hNM⟩ := hSiffM
                have htopSr : S.board.topOf (Sum.inr r) = some c :=
                  (Board.bottomOf_eq S.board c (Sum.inr r)).mp hbot
                have htopMr : M.board.topOf (Sum.inr r) = some c :=
                  hframe.top_some (Sum.inr r) c htopSr
                    (by simp only [List.map_id, List.mem_singleton]; exact hcne)
                have hbotMc : M.board.bottomOf (id c) = some (Sum.inr r) :=
                  (Board.bottomOf_eq M.board (id c) (Sum.inr r)).mpr htopMr
                have hrMr : rM = r :=
                  Sum.inr.inj (Option.some.inj (hbotM.symm.trans hbotMc))
                have haMa : aM = a := by
                  have h1 : M.pileOfTopHidden r = S.pileOfTopHidden r :=
                    Frame.pileOfTopHidden_congr hframe.core.deal_eq
                      hframe.core.depths_eq r
                  rw [hrMr] at hpM
                  rw [h1] at hpM
                  exact Option.some.inj (hpM.symm.trans hp)
                have hbaseN : N.board.bottomOf strand = some β := by
                  rw [hNM]
                  have hβ : M.board.topOf β = some strand :=
                    (Board.bottomOf_eq M.board strand β).mp hbase
                  have hbM : M.hiddenBase aM = S.hiddenBase a := by
                    rw [haMa]
                    exact Frame.hiddenBase_congr hframe.core.deal_eq
                      hframe.core.depths_eq a
                  have h2 : bdM.topOf β = M.board.topOf β :=
                    Board.attach_topOf_ne M.board (M.hiddenBase aM) rM hattM
                      (by
                        intro hcon
                        rw [hbM] at hcon
                        exact hβhb hcon)
                  show bdM.bottomOf strand = some β
                  exact (Board.bottomOf_eq _ strand β).mpr (h2.trans hβ)
                obtain ⟨Nf, nplay', hrun', ρ', hcorr'⟩ := ih _ _ (.mid strand β)
                  (State.heights_le_apply hMle hfire) (apply_wf hwf _ _ hS)
                  ⟨hX', hbaseN, hstrand⟩ hwin' hrun
                exact ⟨Nf, Move.relabelTwin id (Move.reveal c) :: nplay',
                  State.run_cons_comp hfire hrun', ρ', hcorr'⟩
            | deckPile q b =>
                simp only [State.playWindow', hS, Bool.and_eq_true, decide_eq_true_iff,
                  List.all_eq_true] at hwin
                obtain ⟨⟨hbβ, hβq, hwall, hL2m⟩, hwin'⟩ := hwin
                have habove : M.board.aboveOf strand = S.board.aboveOf strand := by
                  have h1 := hframe.above_strand strand (by simp)
                  simpa using h1
                have hwalk : ∀ x ∈ [strand], ∀ y ∈ x :: M.board.aboveOf x,
                    Base.relabel id b ≠ Sum.inr y := by
                  intro x hx y hy
                  rw [List.mem_singleton.mp hx] at hy
                  rw [habove] at hy
                  have hrb : Base.relabel id b = b := by cases b <;> rfl
                  rw [hrb]
                  exact hwall y hy
                have hbare2 : ∀ x ∈ [strand],
                    M.board.bottomOf x ≠ some (Sum.inr q) := by
                  intro x hx hcon
                  rw [List.mem_singleton.mp hx] at hcon
                  rw [hbase] at hcon
                  exact hβq (Option.some.inj hcon)
                have hfree : ∀ x ∈ [strand],
                    M.board.bottomOf x ≠ some (Base.relabel id b) := by
                  intro x hx hcon
                  rw [List.mem_singleton.mp hx] at hcon
                  rw [hbase] at hcon
                  have hrb : Base.relabel id b = b := by cases b <;> rfl
                  rw [hrb] at hcon
                  exact hbβ (Option.some.inj hcon).symm
                have hL2 : ∀ d : Card, b = Sum.inr d →
                    (id d ∉ [strand] ∧ ∀ x ∈ [strand],
                      d ∉ S.board.aboveOf (id x)) := by
                  intro d hd
                  have h3 := hL2m
                  simp only [hd, beq_iff_eq, decide_eq_true_iff] at h3
                  refine ⟨fun hcon => h3.1 (List.mem_singleton.mp hcon), ?_⟩
                  intro x hx
                  rw [List.mem_singleton.mp hx]
                  exact h3.2
                obtain ⟨N, hfire, hX'⟩ := State.TwinCorrX.apply_deckPile hframe hwf
                  (fun c _ => rfl) hS hfree hbare2 hwalk hL2
                have hSiffM := apply_deckPile_iff.mp hfire
                obtain ⟨hprevM, hcpM, bdM, hattM, hNM⟩ := hSiffM
                have hbaseN : N.board.bottomOf strand = some β := by
                  rw [hNM]
                  have hβ : M.board.topOf β = some strand :=
                    (Board.bottomOf_eq M.board strand β).mp hbase
                  have h2 : bdM.topOf β = M.board.topOf β :=
                    Board.attach_topOf_ne M.board (Base.relabel id b) q hattM
                      (fun hcon => hbβ (by
                        have hrb : Base.relabel id b = b := by cases b <;> rfl
                        exact hrb.symm.trans hcon.symm))
                  show bdM.bottomOf strand = some β
                  exact (Board.bottomOf_eq _ strand β).mpr (h2.trans hβ)
                obtain ⟨Nf, nplay', hrun', ρ', hcorr'⟩ := ih _ _ (.mid strand β)
                  (State.heights_le_apply hMle hfire) (apply_wf hwf _ _ hS)
                  ⟨hX', hbaseN, hstrand⟩ hwin' hrun
                exact ⟨Nf, Move.relabelTwin id (Move.deckPile q b) :: nplay',
                  State.run_cons_comp hfire hrun', ρ', hcorr'⟩
            | stackPile c b =>
                simp only [State.playWindow', hS, Bool.and_eq_true, decide_eq_true_iff,
                  List.all_eq_true] at hwin
                obtain ⟨⟨hbβ, hβc, hwall, hL2m⟩, hwin'⟩ := hwin
                have habove : M.board.aboveOf strand = S.board.aboveOf strand := by
                  have h1 := hframe.above_strand strand (by simp)
                  simpa using h1
                have hwalk : ∀ x ∈ [strand], ∀ y ∈ x :: M.board.aboveOf x,
                    Base.relabel id b ≠ Sum.inr y := by
                  intro x hx y hy
                  rw [List.mem_singleton.mp hx] at hy
                  rw [habove] at hy
                  have hrb : Base.relabel id b = b := by cases b <;> rfl
                  rw [hrb]
                  exact hwall y hy
                have hbare2 : ∀ x ∈ [strand],
                    M.board.bottomOf x ≠ some (Sum.inr c) := by
                  intro x hx hcon
                  rw [List.mem_singleton.mp hx] at hcon
                  rw [hbase] at hcon
                  exact hβc (Option.some.inj hcon)
                have hfree : ∀ x ∈ [strand],
                    M.board.bottomOf x ≠ some (Base.relabel id b) := by
                  intro x hx hcon
                  rw [List.mem_singleton.mp hx] at hcon
                  rw [hbase] at hcon
                  have hrb : Base.relabel id b = b := by cases b <;> rfl
                  rw [hrb] at hcon
                  exact hbβ (Option.some.inj hcon).symm
                have hL2 : ∀ d : Card, b = Sum.inr d →
                    (id d ∉ [strand] ∧ ∀ x ∈ [strand],
                      d ∉ S.board.aboveOf (id x)) := by
                  intro d hd
                  have h3 := hL2m
                  simp only [hd, beq_iff_eq, decide_eq_true_iff] at h3
                  refine ⟨fun hcon => h3.1 (List.mem_singleton.mp hcon), ?_⟩
                  intro x hx
                  rw [List.mem_singleton.mp hx]
                  exact h3.2
                by_cases hon : c.suit = z.suit ∨ c.suit = z.suit.flipPair
                · have hSiff := apply_stackPile_iff.mp hS
                  obtain ⟨hrk, hcp, bd, hatt, rfl⟩ := hSiff
                  have halign : M.heights (id c).suit = c.rank.toIdx + 1 := by
                    show M.heights c.suit = c.rank.toIdx + 1
                    rw [hrung c.suit]; exact hrk.symm
                  have hcX : c ∉ List.map id [strand] := by
                    simp only [List.map_id]
                    intro hcon
                    have h1 : S.isVis c = true := by
                      have h2 : M.isVis strand = true :=
                        hframe.strand_vis strand (by simp)
                      rw [hframe.vis_iff strand] at h2
                      rw [← List.mem_singleton.mp hcon] at h2
                      exact h2
                    have hlt : c.rank.toIdx < S.heights c.suit := by omega
                    have h3 : S.isVis c = false := (hwf.founds_gone c hlt).1
                    rw [h3] at h1
                    exact absurd h1 (by simp)
                  obtain ⟨N, hfire, hX'⟩ := State.TwinCorrX.apply_stackPile_onsuit
                    hframe hwf hon hcX hS halign hfree hbare2 hwalk hL2
                  have hSiffM := apply_stackPile_iff.mp hfire
                  obtain ⟨hrkM, hcpM, bdM, hattM, hNM⟩ := hSiffM
                  have hbaseN : N.board.bottomOf strand = some β := by
                    rw [hNM]
                    have hβ : M.board.topOf β = some strand :=
                      (Board.bottomOf_eq M.board strand β).mp hbase
                    have h2 : bdM.topOf β = M.board.topOf β :=
                      Board.attach_topOf_ne M.board (Base.relabel id b) (id c) hattM
                        (fun hcon => hbβ (by
                        have hrb : Base.relabel id b = b := by cases b <;> rfl
                        exact hrb.symm.trans hcon.symm))
                    show bdM.bottomOf strand = some β
                    exact (Board.bottomOf_eq _ strand β).mpr (h2.trans hβ)
                  obtain ⟨Nf, nplay', hrun', ρ', hcorr'⟩ := ih _ _ (.mid strand β)
                    (State.heights_le_apply hMle hfire) (apply_wf hwf _ _ hS)
                    ⟨hX', hbaseN, hstrand⟩ hwin' hrun
                  exact ⟨Nf, Move.relabelTwin id (Move.stackPile c b) :: nplay',
                    State.run_cons_comp hfire hrun', ρ', hcorr'⟩
                · obtain ⟨N, hfire, hX'⟩ := State.TwinCorrX.apply_stackPile_off hframe
                    hwf
                    (⟨fun hcon => hon (Or.inl hcon), fun hcon => hon (Or.inr hcon)⟩ :
                      c.suit ≠ z.suit ∧ c.suit ≠ z.suit.flipPair) hS hfree hbare2
                    hwalk hL2
                  have hSiffM := apply_stackPile_iff.mp hfire
                  obtain ⟨hrkM, hcpM, bdM, hattM, hNM⟩ := hSiffM
                  have hbaseN : N.board.bottomOf strand = some β := by
                    rw [hNM]
                    have hβ : M.board.topOf β = some strand :=
                      (Board.bottomOf_eq M.board strand β).mp hbase
                    have h2 : bdM.topOf β = M.board.topOf β :=
                      Board.attach_topOf_ne M.board (Base.relabel id b) c hattM
                        (fun hcon => hbβ (by
                        have hrb : Base.relabel id b = b := by cases b <;> rfl
                        exact hrb.symm.trans hcon.symm))
                    show bdM.bottomOf strand = some β
                    exact (Board.bottomOf_eq _ strand β).mpr (h2.trans hβ)
                  obtain ⟨Nf, nplay', hrun', ρ', hcorr'⟩ := ih _ _ (.mid strand β)
                    (State.heights_le_apply hMle hfire) (apply_wf hwf _ _ hS)
                    ⟨hX', hbaseN, hstrand⟩ hwin' hrun
                  exact ⟨Nf, Move.relabelTwin id (Move.stackPile c b) :: nplay',
                    State.run_cons_comp hfire hrun', ρ', hcorr'⟩
            | pilePile c b =>
                simp only [State.playWindow', hS] at hwin
                exact absurd hwin (by simp)
          · -- ===== POST-EPISODE =====
            have hcorr : State.TwinCorr id z.suit S M := hinv
            simp only [State.playWindow', hS] at hwin
            obtain ⟨N, hfire, hcorrR⟩ :=
              State.twinCorr_step_fix hcorr (fun _ => rfl) hMle hwf hS
            obtain ⟨Nf, nplay', hrun', ρ', hcorr'⟩ := ih R N .post
              (State.heights_le_apply hMle hfire) (apply_wf hwf _ R hS) hcorrR hwin hrun
            exact ⟨Nf, Move.relabelTwin id m :: nplay', State.run_cons_comp hfire hrun',
              ρ', hcorr'⟩

/-! ## §12. The mid-episode pilePile — the walk-agreement substrate -/

/-- **The column transitivity**: a card above a walk member is a walk
member — the column above any card of `q`'s column stays inside the
column (the extend step iterated through the fuel induction). -/
theorem Board.mem_aboveOf_trans {bd : Board} : ∀ (m : Nat) (b : Base) (acc : List Card)
    (q _z e : Card), (∀ w ∈ acc, w ∈ q :: bd.aboveOf q) →
    (∃ z₀, b = Sum.inr z₀ ∧ z₀ ∈ q :: bd.aboveOf q) →
    e ∈ Board.aboveOf.go bd m b acc → e ∈ q :: bd.aboveOf q := by
  intro m
  induction m with
  | zero => intro b acc q z e hacc _ he; exact hacc e he
  | succ n ih =>
      intro b acc q z e hacc hseat he
      cases ht : bd.topOf b with
      | none => rw [Board.aboveOf_go_topOf_none ht] at he; exact hacc e he
      | some c' =>
          by_cases hcon : acc.contains c' = true
          · rw [Board.aboveOf_go_stop ht hcon] at he; exact hacc e he
          · rw [Board.aboveOf_go_step ht hcon] at he
            -- the new card is in the q-column (the extend step)
            have hcq : c' ∈ q :: bd.aboveOf q := by
              obtain ⟨z₀, hb, hz₀⟩ := hseat
              have hw : bd.topOf (Sum.inr z₀) = some c' := by rw [← hb]; exact ht
              exact Board.mem_aboveOf_extend hz₀ hw
            refine ih (Sum.inr c') (c' :: acc) q z e ?_ ⟨c', rfl, hcq⟩ he
            intro w hw
            rcases List.mem_cons.mp hw with rfl | hw'
            · exact hcq
            · exact hacc w hw'

/-- **The column membership invariant**: every member of a walk from a
card's seat is either an accumulator member or a member of the
card's canonical column (any fuel; the transitivity closes the
continuation case). -/
theorem Board.go_mem_or_column {bd : Board} :
    ∀ (m : Nat) (q : Card) (acc : List Card) (d : Card),
      d ∈ Board.aboveOf.go bd m (Sum.inr q) acc → d ∈ acc ∨ d ∈ bd.aboveOf q := by
  intro m
  induction m with
  | zero => intro q acc d hd; exact Or.inl hd
  | succ n ih =>
      intro q acc d hd
      cases hread : bd.topOf (Sum.inr q) with
      | none => rw [Board.aboveOf_go_topOf_none hread] at hd; exact Or.inl hd
      | some c' =>
          by_cases hcon : acc.contains c' = true
          · rw [Board.aboveOf_go_stop hread hcon] at hd; exact Or.inl hd
          · have hd0 := hd
            rw [Board.aboveOf_go_step hread hcon] at hd
            rcases ih c' (c' :: acc) d hd with h | h
            · rcases List.mem_cons.mp h with rfl | h
              · exact Or.inr (Board.mem_aboveOf_of_topOf hread)
              · exact Or.inl h
            · have h1 : c' ∈ q :: bd.aboveOf q :=
                List.mem_cons_of_mem _ (Board.mem_aboveOf_of_topOf hread)
              have h2 : d ∈ q :: bd.aboveOf q :=
                Board.mem_aboveOf_trans 52 (Sum.inr c') ([] : List Card) q c' d
                  (by intro w hw; exact absurd hw (by simp))
                  ⟨c', rfl, h1⟩ h
              rcases List.mem_cons.mp h2 with rfl | h3
              · -- the cyclic head: the card itself is an acc member or a
                -- plain walk member (the acc subsumption + saturation on
                -- the original walk from its own seat)
                rcases Board.aboveOf_go_acc_sub hd0 with h4 | h4
                · exact Or.inl h4
                · exact Or.inr (Board.aboveOf_go_sat h4)
              · exact Or.inr h3

/-- **The two-seat walk agreement**: if two boards differ at exactly
two seats — `bdM` holds the card `s` at `β` where `bdS` is empty, and
`bdS` holds `s` at `bq'` where `bdM` is empty, agreeing everywhere
else, with the columns above `s` agreeing — then every walk of `bdM`
stays inside the corresponding walk of `bdS` union the strand column
`s :: bdS.aboveOf s`.  This is the source-side reformulation of the
pilePile step's mirror-side `hplace` premise: the mirror walk's extra
members are exactly the strand column — at the mid-episode's
identity map the composite mirror walk enters the strand's column
only through `β`, and that whole column is the source's own strand
column (the `above_strand` field). -/
theorem Board.aboveOf_two_seat_sub {bdM bdS : Board} {β bq' : Base} {s : Card}
    (hβ : bdM.topOf β = some s) (hβ' : bdS.topOf β = none)
    (hbq : bdM.topOf bq' = none) (hbq' : bdS.topOf bq' = some s)
    (hagr : ∀ b, b ≠ β → b ≠ bq' → bdM.topOf b = bdS.topOf b)
    (hcol : bdM.aboveOf s = bdS.aboveOf s) :
    ∀ (m : Nat) (b : Base) (acc : List Card) (e : Card),
      e ∈ Board.aboveOf.go bdM m b acc →
        e ∈ acc ∨ e ∈ s :: bdS.aboveOf s ∨ e ∈ Board.aboveOf.go bdS m b acc := by
  intro m
  induction m with
  | zero => intro b acc e he; exact Or.inl he
  | succ n ih =>
      intro b acc e he
      cases ht : bdM.topOf b with
      | none =>
          rw [Board.aboveOf_go_topOf_none ht] at he
          exact Or.inl he
      | some c' =>
          by_cases hcon : acc.contains c' = true
          · rw [Board.aboveOf_go_stop ht hcon] at he; exact Or.inl he
          · rw [Board.aboveOf_go_step ht hcon] at he
            by_cases hb : b = β
            · -- the divergence seat: c' = s, the continuation is the
              -- strand column (the column lemma + the column agreement)
              subst hb
              rw [hβ] at ht
              have hcs : s = c' := Option.some.inj ht
              subst hcs
              rcases Board.go_mem_or_column n s (s :: acc) e he with h | h
              · rcases List.mem_cons.mp h with rfl | h
                · exact Or.inr (Or.inl (by simp))
                · exact Or.inl h
              · rw [hcol] at h
                exact Or.inr (Or.inl (List.mem_cons_of_mem _ h))
            · have hbq' : b ≠ bq' := by
                intro hcon2
                subst hcon2
                rw [hbq] at ht
                exact absurd ht (by simp)
              -- the agreeing seat: the source walk reads the same card
              have htS : bdS.topOf b = some c' := by
                rw [← hagr b hb hbq']; exact ht
              have hconS : acc.contains c' ≠ true := hcon
              rcases ih (Sum.inr c') (c' :: acc) e he with h | h | h
              · rcases List.mem_cons.mp h with rfl | h
                · refine Or.inr (Or.inr ?_)
                  rw [Board.aboveOf_go_step htS hconS]
                  exact Board.aboveOf_go_mem bdS n (Sum.inr e) (e :: acc) e
                    (by simp)
                · exact Or.inl h
              · exact Or.inr (Or.inl h)
              · refine Or.inr (Or.inr ?_)
                rw [Board.aboveOf_go_step htS hconS]
                exact h

/-- **THE GROWTH-ENGAGED WINDOW** (the climb-out replay, the
strengthened form): a twin-correlated mirror of a WF source that can
win by a play the growth-engaged window admits is itself solvable —
the misaligned pair-stack now routes to the GROWTH (the mirror
stacks the flipped image, the correspondence map becomes the
identity, the strand sits at its mirror base), the mid-episode runs
at the identity correspondence (draws, deckStacks, the strand-safe
pileStacks — the rung equality aligning everything), the catch-up
(the source's stacking of the strand's source-twin) drains the
episode, and the post-episode regime needs NO conditions at all
(the identity correspondence).  The endgame is the correspondence's
own shape (the two on-suit kings plus the 52-count).  Over the
original window, the STACK-SKEW premise is GONE: an on-suit
`pileStack` needs only the off-suitness, the skew, or the growth's
source-side premises (the pair card, the twin seated and bare, the
corner freedoms).  The UNSTACK ANTI-SKEW is now needed only at the
pair members and the JUST-BELOW-PAIR worry-back (rank one under the
pair card): there the crossed configuration (the partner member
stacked in the source, this one not) puts the mirror genuinely AHEAD,
and the response would be a MULTI-unstack — the mirror dropping its
rung past the stranded pair card before the verbatim — not a single
in-kind move, and not source-composable (the unstack-growth corner).
Every OTHER on-suit worry-back is admitted UNCONDITIONALLY — the rung
derivation `State.TwinCore.rung_eq_unstack_of_ne` (the iff at the
moved card pushes the mirror's rung up, the iff at the next card up —
ρ-fixed by the rank gap — caps it).  The pair-deckStack exclusion
(route (c)) stays.  MID-EPISODE TABLEAU: reveals, deckPiles and
stackPiles (off- and on-suit) are ADMITTED with their landing-seat
clauses (the landing base and the moved card off the strand's mirror
base β; the landing seat off the strand's column; the landing card
not in the strand's column — the source-side renderings of the L1/L2
family); only pilePiles remain excluded mid-episode — the
run-placement premise `hplace` of the pilePile step quantifies over
the composite MIRROR walk (not source-checkable), and the
strand-riding-the-run corner (the strand in the moved run: the run
carries it in the source but the mirror's copy sits at the strand
seat) has no in-kind response.  The walk-agreement SUBSTRATE for the
source-side reformulation is landed (`Board.aboveOf_two_seat_sub`:
at the two-seat board difference, the mirror walk stays inside the
source walk union the strand column) — the remaining residue is the
thin composite-board layer (the at-home case `β = bq'`, the strand
column's preservation under the detach/attach surgery) plus the
run/strand disjointness clause. -/
theorem State.solvable_of_twinCorr_window' {S M : State} {z : Card}
    (hcorr : State.TwinCorr (Card.swapTwin z) z.suit S M)
    (hMle : ∀ s, M.heights s ≤ 13)
    (hwf : S.WF)
    (hhid : ∀ a, ∀ c ∈ S.hidden a, Card.swapTwin z c = c)
    (hstock : ∀ c ∈ S.stock.cards, Card.swapTwin z c = c)
    (hsolw' : S.solvableWindow' z z.suit) :
    M.solvableFrom := by
  obtain ⟨play, W, hrun, hwin, hplay⟩ := hsolw'
  obtain ⟨N, nplay, hrunN, ρ', hcorr'⟩ := State.twinCorr_run_window' z play S M
    State.WindowEp.pre hMle hwf ⟨hcorr, hhid, hstock⟩ hplay hrun
  exact ⟨nplay, N, hrunN, State.twinCorr_isWin_of_le hcorr' hwin
    (State.heights_le_run hMle hrunN)⟩
