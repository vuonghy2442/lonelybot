import Klondike.TwinFrame

/-!
# The twin replay - the window assembly

The active file: the no-twin-foundation window and the growing-rho
assembly (solvable_of_twinCorr_window) land here; the machinery
(twin maps, board kit, correspondence, move translation, the
crossed-set frame and its step lemmas) lives in TwinFrame.lean.
-/
/-! ## §8. The window assembly — the no-twin-foundation replay -/

/-- **The clean run**: a clean play translates wholesale — the mirror
runs the ρ-relabeled play, and the two games' heights track (the
twin-suit rungs never move under a clean play, the off-suit heights
agree by the correspondence). -/
theorem State.twinCorr_run_clean (ρ : Card → Card) (σ : Suit) :
    ∀ (play : List Move) (S M : State),
    State.TwinCorr ρ σ S M → M.heights = S.heights →
    (∀ a, ∀ c ∈ S.hidden a, ρ c = c) → (∀ c ∈ S.stock.cards, ρ c = c) →
    (∀ m ∈ play, Move.twinClean σ m = true) →
    ∀ {W : State}, S.run play = some W →
    ∃ N, M.run (play.map (Move.relabelTwin ρ)) = some N ∧ N.heights = W.heights := by
  intro play
  induction play with
  | nil =>
      intro S M _ hheq _ _ _ W hrun
      have h1 : S.run [] = some S := rfl
      have hW : W = S := (Option.some.inj (h1.symm.trans hrun)).symm
      subst hW
      refine ⟨M, rfl, ?_⟩
      exact hheq
  | cons m ms ih =>
      intro S M hcorr hheq hhid hstock hclean W hrun
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
          have htwinS := Move.twinClean_heights (hclean m List.mem_cons_self) hS
          have htwinN := Move.twinClean_heights
            (Move.twinClean_relabelTwin hcorr.fixes_off (hclean m List.mem_cons_self)) hfire
          have hheqN : N.heights = R.heights := by
            funext s
            by_cases hs1 : s = σ
            · rw [hs1]
              show N.heights σ = R.heights σ
              rw [htwinN.1, htwinS.1, congrFun hheq σ]
            · by_cases hs2 : s = σ.flipPair
              · rw [hs2]
                show N.heights σ.flipPair = R.heights σ.flipPair
                rw [htwinN.2, htwinS.2, congrFun hheq σ.flipPair]
              · exact hcorr'.heights_off s hs1 hs2
          obtain ⟨N', hrun', hheq'⟩ := ih R N hcorr' hheqN hhidR hstockR
            (fun m' hm' => hclean m' (List.mem_cons_of_mem _ hm')) hrun
          refine ⟨N', ?_, hheq'⟩
          simp only [List.map_cons, State.run, hfire]
          exact hrun'

/-- **The no-twin-foundation window** (the climb-out's clean core,
board-only): if the source's winning play never makes a twin-suit
foundation move, the twin-correlated mirror replays the translated
play and wins — the heights track throughout, so `isWin` transfers.
The ply result's board-only swap (`exchange_merge_ply_root`) enters
here at `ρ = τ_z` with `M.heights = S.heights` definitionally and the
`hhid`/`hstock` premises WF-consequences (z/z' seated). -/
theorem State.solvable_of_twinCorr_clean {ρ σ S M}
    (hcorr : State.TwinCorr ρ σ S M)
    (hheq : M.heights = S.heights)
    (hhid : ∀ a, ∀ c ∈ S.hidden a, ρ c = c)
    (hstock : ∀ c ∈ S.stock.cards, ρ c = c)
    {play : List Move} (hclean : ∀ m ∈ play, Move.twinClean σ m = true)
    {W : State} (hrun : S.run play = some W) (hwin : W.isWin = true) :
    M.solvableFrom := by
  obtain ⟨N, hrun', hheq'⟩ := State.twinCorr_run_clean ρ σ play S M hcorr hheq hhid hstock
    hclean hrun
  exact ⟨play.map (Move.relabelTwin ρ), N, hrun', by
    show Suit.all.all (fun s => decide (N.heights s = 13)) = true
    rw [hheq']
    exact hwin⟩

/-- **The window, backward**: the same statement with the two games
exchanged (the correspondence is symmetric; the hidden/stock
premises transfer along the equal deals and stock cycles). -/
theorem State.solvable_of_twinCorr_clean_back {ρ σ S M}
    (hcorr : State.TwinCorr ρ σ S M)
    (hheq : M.heights = S.heights)
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
  exact State.solvable_of_twinCorr_clean hcorr.symm hheq.symm hhid' hstock' hclean hrun hwin
