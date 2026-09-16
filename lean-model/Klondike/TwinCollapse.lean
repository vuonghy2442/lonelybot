import Klondike.Tactics

/-!
# The anchor-relocation collapse kit (2026-09-16, the w15circ session)

The third mirror-repair mechanism's general lemmas.  The executable
evidence is `probes/w15circ.lean`: a licensed WF cast where st's forced
win goes through the cargo-top merge while the exchanged state wins
anyway by DISMANTLING the blocked run from the top.

The mechanism: when the exchanged state's mirror merge is blocked only
by the self-landing guard (the run from `c` passes `t` and ends at
`z'`, the other twin's cargo now riding `t`), and the twin `t` inside
the run is a KING, then the sub-run headed by `t` parks at any free
anchor (kings relocate freely — their card-landing set is empty), the
self-landing circle breaks, and `c` re-lands on the now-bare `z'`:  the
mirror merge, two moves later.  The re-landing detaches `c` from its
host `d`, exposing it — the burial chain's unlock.

Scope: pure board/move lemmas over the green core — no TwinExchange
dependency (that file is red under the v4.34 toolchain at the time of
writing).  The integration premise `hbotZ : bottomOf z' = some (inr t)`
is the exchange's aftermath; the [H] assembly supplies it from the
exchange lemmas when the tree greens (the w15mergecheck
re-verification pattern).  Sorry-free, no new axioms.
-/

/-! ## Base disjointness helpers (named once: `rw`'s explicit-argument
elaboration order needs the type concrete) -/

theorem base_inl_ne_inr {a : Anchor} {c : Card} : (Sum.inl a : Base) ≠ Sum.inr c :=
  fun h => nomatch h

theorem base_inr_ne_inl {c : Card} {a : Anchor} : (Sum.inr c : Base) ≠ Sum.inl a :=
  fun h => nomatch h

/-! ## The root fact: a king's landing set is the free anchors alone -/

/-- No king ever sits on a card by fit — `canSitOn`'s rank arithmetic
caps at queen.  (The w15circ design's t-is-a-king root fact.) -/
theorem canSitOn_of_king_eq_false {t d : Card} (hking : t.rank = Rank.king) :
    canSitOn t d = false := by
  have h2 := Rank.toIdx_lt d.rank
  have h12 : t.rank.toIdx = 12 := by rw [hking]; rfl
  by_cases h : canSitOn t d = true
  · obtain ⟨h1, -⟩ := (canSitOn_eq t d).mp h
    rw [h12] at h1
    omega
  · exact Bool.eq_false_of_ne_true h

/-- `canPlace`'s tableau arm dies for kings: a king's `pilePile` moves
land at free anchors only. -/
theorem canPlace_inr_of_king {st : State} {t d : Card}
    (hking : t.rank = Rank.king) : st.canPlace t (Sum.inr d) = false := by
  show (decide (st.board.topOf (Sum.inr d) = none) &&
      (st.isVis d && canSitOn t d)) = false
  rw [canSitOn_of_king_eq_false hking]
  simp

/-! ## Step 1: the park -/

/-- A seated king parks its sub-run at any free anchor, the board
factorized (consumed by `park_reland`). -/
theorem park_king_run {st : State} {t c : Card} {a : Anchor}
    (hbotT : st.board.bottomOf t = some (Sum.inr c))
    (hking : t.rank = Rank.king)
    (hfree : st.board.topOf (Sum.inl a) = none) :
    ∃ bd₁, (st.board.detach (Sum.inr c)).attach (Sum.inl a) t = some bd₁ ∧
      st.apply (Move.pilePile t (Sum.inl a)) = some { st with board := bd₁ } := by
  have hztop : st.board.topOf (Sum.inr c) = some t :=
    (Board.bottomOf_eq st.board t (Sum.inr c)).mp hbotT
  have hcmr : st.canMoveRun t (Sum.inl a) = true := by
    rw [canMoveRun_inl_iff]
    show (decide (st.board.topOf (Sum.inl a) = none) &&
        decide (t.rank = Rank.king)) = true
    rw [hfree, hking]
    rfl
  have hdet : (st.board.detach (Sum.inr c)).topOf (Sum.inl a) = none := by
    rw [Board.detach_topOf_ne _ _ _ base_inl_ne_inr]
    exact hfree
  have hdetBot : (st.board.detach (Sum.inr c)).bottomOf t = none :=
    Board.bottomOf_detach_self hztop
  have hatt : (st.board.detach (Sum.inr c)).attach (Sum.inl a) t ≠ none := by
    rw [Board.attach_eq_some_iff]
    exact ⟨hdet, hdetBot⟩
  cases hA : (st.board.detach (Sum.inr c)).attach (Sum.inl a) t with
  | none => exact absurd hA hatt
  | some bd₁ =>
      refine ⟨bd₁, rfl, ?_⟩
      rw [apply_pilePile_iff]
      exact ⟨Sum.inr c, hbotT, base_inr_ne_inl, hcmr, bd₁, hA, rfl⟩

/-! ## The composite: park, then re-land on the freed twin cargo -/

/-- **The anchor-relocation collapse, two moves.**  With the twin `t` a
king riding `c`, and `z'` riding `t` (the exchange's aftermath), and a
free anchor `a`:  the sub-run parks at `a`;  `c` then re-lands on the
now-bare `z'` (the self-landing guard died with the run — the walk
from `c` is empty after the park);  the re-landing exposes `d` (the
host under `c`) and touches nothing but the board (heights, stock and
depths preserved). -/
theorem park_reland {st : State} {t c z' d : Card} {a : Anchor}
    (hct : c ≠ t)
    (hbotT : st.board.bottomOf t = some (Sum.inr c))
    (hbotZ : st.board.bottomOf z' = some (Sum.inr t))
    (hbotC : st.board.bottomOf c = some (Sum.inr d))
    (hz'bare : st.board.topOf (Sum.inr z') = none)
    (hking : t.rank = Rank.king)
    (hfit : canSitOn c z' = true)
    (hfree : st.board.topOf (Sum.inl a) = none) :
    ∃ s₁ s₂, st.apply (Move.pilePile t (Sum.inl a)) = some s₁ ∧
      s₁.apply (Move.pilePile c (Sum.inr z')) = some s₂ ∧
      s₂.board.topOf (Sum.inr z') = some c ∧
      s₂.board.topOf (Sum.inr d) = none ∧
      s₂.heights = st.heights ∧ s₂.stock = st.stock ∧ s₂.depths = st.depths := by
  -- the st-level seats
  have hztop : st.board.topOf (Sum.inr c) = some t :=
    (Board.bottomOf_eq st.board t (Sum.inr c)).mp hbotT
  have hz'top : st.board.topOf (Sum.inr t) = some z' :=
    (Board.bottomOf_eq st.board z' (Sum.inr t)).mp hbotZ
  have hctop : st.board.topOf (Sum.inr d) = some c :=
    (Board.bottomOf_eq st.board c (Sum.inr d)).mp hbotC
  -- distinctness (from the matching's injectivity + the premises)
  have hz'c : z' ≠ c := by
    intro h
    rw [h] at hz'bare
    rw [hztop] at hz'bare
    simp at hz'bare
  have hdc : d ≠ c := by
    intro h
    have h1 : st.board.topOf (Sum.inr d) = some c :=
      (Board.bottomOf_eq st.board c (Sum.inr d)).mp hbotC
    rw [h] at h1
    rw [h1] at hztop
    exact hct (Option.some.inj hztop)
  have hdz' : d ≠ z' := by
    intro h
    have h1 : st.board.topOf (Sum.inr d) = some c :=
      (Board.bottomOf_eq st.board c (Sum.inr d)).mp hbotC
    rw [h] at h1
    rw [h1] at hz'bare
    simp at hz'bare
  -- step 1: the park, with its board
  obtain ⟨bd₁, hA, hstep₁⟩ := park_king_run hbotT hking hfree
  -- the parked board's seats
  have htop₁_c : bd₁.topOf (Sum.inr c) = none := by
    rw [Board.attach_topOf_ne _ _ _ hA base_inr_ne_inl, Board.detach_topOf]
  have htop₁_z' : bd₁.topOf (Sum.inr z') = none := by
    rw [Board.attach_topOf_ne _ _ _ hA base_inr_ne_inl,
        Board.detach_topOf_ne _ _ _ (fun h => hz'c (Sum.inr.inj h))]
    exact hz'bare
  have htop₁_t : bd₁.topOf (Sum.inr t) = some z' := by
    rw [Board.attach_topOf_ne _ _ _ hA base_inr_ne_inl,
        Board.detach_topOf_ne _ _ _ (fun h => hct (Sum.inr.inj h).symm)]
    exact hz'top
  have htop₁_d : bd₁.topOf (Sum.inr d) = some c := by
    rw [Board.attach_topOf_ne _ _ _ hA base_inr_ne_inl,
        Board.detach_topOf_ne _ _ _ (fun h => hdc (Sum.inr.inj h))]
    exact hctop
  -- step 2's guards, at the parked board
  have hbot₁_z' : bd₁.bottomOf z' = some (Sum.inr t) :=
    (Board.bottomOf_eq bd₁ z' (Sum.inr t)).mpr htop₁_t
  have hbot₁_c : bd₁.bottomOf c = some (Sum.inr d) :=
    (Board.bottomOf_eq bd₁ c (Sum.inr d)).mpr htop₁_d
  have hvis₁ : ({ st with board := bd₁ } : State).isVis z' = true := by
    show (bd₁.bottomOf z').isSome = true
    rw [hbot₁_z']
    rfl
  have habove₁ : bd₁.aboveOf c = [] := Board.aboveOf_step_none htop₁_c
  have hcont₁ : (bd₁.aboveOf c).contains z' = false := by
    rw [habove₁]
    rfl
  have hcp₁ : ({ st with board := bd₁ } : State).canPlace c (Sum.inr z') = true := by
    show (decide (bd₁.topOf (Sum.inr z') = none) &&
        (({ st with board := bd₁ } : State).isVis z' && canSitOn c z')) = true
    rw [htop₁_z', hvis₁, hfit]
    rfl
  have hcmr₂ : ({ st with board := bd₁ } : State).canMoveRun c (Sum.inr z') = true := by
    rw [canMoveRun_inr_iff]
    exact ⟨hcp₁, hcont₁⟩
  -- step 2's attach
  have hdet2Free : (bd₁.detach (Sum.inr d)).topOf (Sum.inr z') = none := by
    rw [Board.detach_topOf_ne _ _ _ (fun h => hdz' (Sum.inr.inj h).symm)]
    exact htop₁_z'
  have hdet2Bot : (bd₁.detach (Sum.inr d)).bottomOf c = none :=
    Board.bottomOf_detach_self htop₁_d
  have hatt₂ : (bd₁.detach (Sum.inr d)).attach (Sum.inr z') c ≠ none := by
    rw [Board.attach_eq_some_iff]
    exact ⟨hdet2Free, hdet2Bot⟩
  cases hB : (bd₁.detach (Sum.inr d)).attach (Sum.inr z') c with
  | none => exact absurd hB hatt₂
  | some bd₂ =>
      refine ⟨{ st with board := bd₁ }, { st with board := bd₂ }, hstep₁, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [apply_pilePile_iff]
        exact ⟨Sum.inr d, hbot₁_c, fun h => hdz' (Sum.inr.inj h), hcmr₂, bd₂, hB, rfl⟩
      · show bd₂.topOf (Sum.inr z') = some c
        exact Board.attach_topOf _ _ _ hB
      · show bd₂.topOf (Sum.inr d) = none
        rw [Board.attach_topOf_ne _ _ _ hB (fun h => hdz' (Sum.inr.inj h)),
            Board.detach_topOf]
      · rfl
      · rfl
      · rfl

/-! ## The solvability seed -/

/-- The collapse's solvability seed: solvability of the post-collapse
state transfers back through the two moves. -/
theorem solvable_of_park_reland {st s₁ s₂ : State} {t c z' : Card} {a : Anchor}
    (hstep₁ : st.apply (Move.pilePile t (Sum.inl a)) = some s₁)
    (hstep₂ : s₁.apply (Move.pilePile c (Sum.inr z')) = some s₂)
    (hs₂ : s₂.solvableFrom) : st.solvableFrom := by
  obtain ⟨π, s', hrun, hwin⟩ := hs₂
  exact ⟨Move.pilePile t (Sum.inl a) :: Move.pilePile c (Sum.inr z') :: π, s',
    run_cons_intro hstep₁ (run_cons_intro hstep₂ hrun), hwin⟩
