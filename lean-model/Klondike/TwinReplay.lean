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
