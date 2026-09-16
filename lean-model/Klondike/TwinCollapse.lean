import Klondike.Tactics
import Klondike.TwinSwap
import Klondike.TwinExchange

/-!
# The anchor-relocation collapse kit (2026-09-16, the w15circ session)

The third mirror-repair mechanism's general lemmas.  The executable
evidence is `probes/w15circ.lean`: a licensed WF cast where st's forced
win goes through the cargo-top merge while the exchanged state wins
anyway by DISMANTLING the blocked run from the top.

The mechanism: when the exchanged state's mirror merge is blocked only
by the self-landing guard (the run from `c` passes `t` and ends at
`z'`, the other twin's cargo now riding `t`), and the twin's sub-run
has ANY legal landing, the sub-run moves, the self-landing circle
breaks, and `c` re-lands on the now-bare `z'`:  the mirror merge, two
moves later.  `dislodge_reland` is the general form;  `park_reland` is
the king-at-a-free-anchor instance (`park_king_run`: kings always have
that landing — their card-landing set is empty,
`canPlace_inr_of_king`);  `aboveOf_contains_topOf` is the walk-entry
fact ruling the self-landing guard.  The re-landing exposes the host
under `c` — the burial chain's unlock.

Scope: pure board/move lemmas over the green core — no TwinExchange
dependency.  The sibling's visClean-level `merge_impossible` is the
reachable-state companion; this kit is the WF-level fallback (the
merge is live there, exactly what w15merge/w15circ exhibit).  The
integration premise `hbotZ : bottomOf z' = some (inr t)` is the
exchange's aftermath; the [H] assembly supplies it when the tree
greens (the w15mergecheck re-verification pattern).  Sorry-free, no
new axioms.
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

/-! ## The walk-entry fact (contains form) -/

/-- The membership-to-contains bridge (the mirror of TwinSwap's
`lcontains_false_of_notMem`). -/
theorem lcontains_true_of_mem {x : Card} : ∀ {l : List Card}, x ∈ l → l.contains x = true
  | [], h => nomatch h
  | a :: t, h => by
      rcases List.mem_cons.mp h with rfl | hrest
      · simp
      · rw [List.contains_cons]
        cases hax : (x == a) with
        | true => simp
        | false =>
            simp only [Bool.false_or]
            exact lcontains_true_of_mem hrest

/-- The walk-entry fact (contains form): whatever rides `x` is in the
run above `x` — the first walk step can never be dropped, whatever
cycles follow.  The self-landing guard's silent partner: a card
riding `t` is IN the run above `t`, so `t`'s own run can never land on
it. -/
theorem aboveOf_contains_topOf {bd : Board} {x y : Card}
    (h : bd.topOf (Sum.inr x) = some y) : (bd.aboveOf x).contains y = true := by
  have hgo : bd.aboveOf x = Board.aboveOf.go bd 53 (Sum.inr x) [] :=
    Board.aboveOf_eq_go 53 (by omega)
  rw [hgo]
  show (Board.aboveOf.go bd (52 + 1) (Sum.inr x) ([] : List Card)).contains y = true
  rw [Board.aboveOf_go_succ, h]
  show (if (([] : List Card).contains y) = true then ([] : List Card)
      else Board.aboveOf.go bd 52 (Sum.inr y) [y]).contains y = true
  rw [ite_eq_right (by simp : ¬(([] : List Card).contains y = true))]
  exact lcontains_true_of_mem
    (Board.aboveOf_go_mono 52 (Sum.inr y) [y] (List.mem_cons_self ..))

/-! ## The merge's forced arithmetic -/

/-- The premise arithmetic, formal: from the license fit (`z` rides `t`
by fit), the twin identity (`z' = z.flipSuit`), and the merge's own
landing fit (`canSitOn c z'`), the twin sits EXACTLY TWO RANKS ABOVE
the run head, in the SAME color.  The merge run therefore ASCENDS —
which is why visClean (descending runs) kills it and why live merges
at WF ride dirty deal-adjacent edges.  Immediate consequences: a KING
twin forces `c` to be the same-color jack (`c.rank` = 10);  a
same-suit twin forces the source's own merged stack into the
rank-inversion unwind (the winning-line discipline the trichotomy
consumes). -/
theorem merge_rank_arith {t c z z' : Card}
    (hz'z : z' = z.flipSuit)
    (hfit : canSitOn z t = true)
    (hmerge : canSitOn c z' = true) :
    t.rank.toIdx = c.rank.toIdx + 2 ∧ t.suit.color = c.suit.color := by
  obtain ⟨h1, h2⟩ := (canSitOn_eq z t).mp hfit
  obtain ⟨h5, h6⟩ := (canSitOn_eq c z').mp hmerge
  rw [hz'z, Card.flipSuit_rank] at h5
  rw [hz'z, Card.flipSuit_color] at h6
  refine ⟨?_, ?_⟩
  · omega
  · cases hc : c.suit.color <;> cases hz : z.suit.color <;>
      cases ht : t.suit.color <;> simp_all

/-! ## The liveness and fit bridges -/

/-- WF's `founds_gone` contrapositive: every VISIBLE card sits at or
above its suit's height — the blocker-on-`z` is LIVE (the w15wfmerge
mechanism's seed, the trichotomy's third arm). -/
theorem wf_vis_rank {st : State} (hwf : st.WF) {c : Card} (hvis : st.isVis c = true) :
    st.heights c.suit ≤ c.rank.toIdx := by
  by_cases hle : st.heights c.suit ≤ c.rank.toIdx
  · exact hle
  · have hlt : c.rank.toIdx < st.heights c.suit := by omega
    rw [(hwf.founds_gone c hlt).1] at hvis
    simp at hvis

/-! ## The founded-run exclusion (the same-suit discipline's core) -/

/-- **A founded card has an empty run at WF**: nothing can sit above a
foundation-passed card.  The first edge of any run would need its base
(the founded card) still seated (board_edges' buried-base clause) or a
hidden boundary — and `founds_gone` refutes both. -/
theorem founded_not_in_aboveOf {st : State} (hwf : st.WF) {c y : Card}
    (hc : c.rank.toIdx < st.heights c.suit) (hy : y ∈ st.board.aboveOf c) : False := by
  obtain ⟨hvis, -, hhid⟩ := hwf.founds_gone c hc
  rw [State.isVis] at hvis
  cases htop : st.board.topOf (Sum.inr c) with
  | none =>
      rw [Board.aboveOf_step_none htop] at hy
      cases hy
  | some w =>
      obtain ⟨-, hedge⟩ := hwf.board_edges (Sum.inr c) w htop
      rcases hedge with ⟨a, l, rest, -, hbase⟩ | ⟨hbcs, -⟩
      · rcases hbase with ⟨a', hth⟩ | hcs
        · exact hhid a' (mem_of_getLast hth)
        · rw [hvis] at hcs
          simp at hcs
      · rw [hvis] at hbcs
        simp at hbcs

/-- **The same-suit no-stack discipline**: at WF, the twin `t` inside a
same-suit merge run (where `merge_rank_arith` pins `t.rank =
c.rank + 2`) can NEVER stack while it sits above `c` — the stack exit
is closed, leaving the dislodge (`pilePile`) as the only way out.
The winning-line discipline's core, state-level;  the play-level
partner (every tableau card stacks in a win) is the §12.1 extraction
corollary — together they force a source-side dislodge for same-suit
winning merges. -/
theorem same_suit_no_stack {st : State} (hwf : st.WF) {t c : Card}
    (hsuit : t.suit = c.suit)
    (hrank : t.rank.toIdx = c.rank.toIdx + 2)
    (habove : t ∈ st.board.aboveOf c) :
    t.rank.toIdx ≠ st.heights t.suit := by
  intro hstack
  have hc : c.rank.toIdx < st.heights c.suit := by
    rw [← hsuit]; omega
  exact founded_not_in_aboveOf hwf hc habove

/-- The merge-ply form: with the license fits and the run passing `t`
above `c`, a same-suit twin is not at its rung — `merge_rank_arith`
composed with `same_suit_no_stack`. -/
theorem merge_run_not_stackable {st : State} (hwf : st.WF) {t c z z' : Card}
    (hsuit : t.suit = c.suit)
    (hz'z : z' = z.flipSuit)
    (hfit : canSitOn z t = true)
    (hmerge : canSitOn c z' = true)
    (habove : t ∈ st.board.aboveOf c) :
    t.rank.toIdx ≠ st.heights t.suit := by
  obtain ⟨hrank, -⟩ := merge_rank_arith hz'z hfit hmerge
  exact same_suit_no_stack hwf hsuit hrank habove

/-! ## The exchange connectors (the aftermath premises, standalone) -/

/-- The exchange's signature, seat form: the cargo `z'` of `t'` rides
`t` after the exchange — the `hbotZ` premise `dislodge_reland`
consumes.  (The derivation appears inline in TwinExchange's walk
lemmas; standalone here for the assembly.) -/
theorem exchangeTwinCargo_bottomOf_z' {st : State} {t z' : Card}
    (h₀' : st.board.bottomOf z' = some (Sum.inr t.flipSuit)) :
    (st.exchangeTwinCargo t).board.bottomOf z' = some (Sum.inr t) := by
  have hsw' : Base.swapTwin t (Sum.inr t) = Sum.inr t.flipSuit := by
    show Sum.inr (Card.swapTwin t t) = Sum.inr t.flipSuit
    rw [Card.swapTwin_self_left]
  have htop' : st.board.topOf (Sum.inr t.flipSuit) = some z' :=
    (Board.bottomOf_eq st.board z' (Sum.inr t.flipSuit)).mp h₀'
  refine (Board.bottomOf_eq _ z' (Sum.inr t)).mpr ?_
  rw [State.exchangeTwinCargo_board, Board.exchangeTwin_topOf, hsw']
  exact htop'

/-- The mirrored connector: the cargo `z` of `t` rides `t'` after the
exchange — the `hbotZ` premise `blocker_leaves_mirror` consumes. -/
theorem exchangeTwinCargo_bottomOf_z {st : State} {t z : Card}
    (h₀ : st.board.bottomOf z = some (Sum.inr t)) :
    (st.exchangeTwinCargo t).board.bottomOf z = some (Sum.inr t.flipSuit) := by
  have hsw : Base.swapTwin t (Sum.inr t.flipSuit) = Sum.inr t := by
    show Sum.inr (Card.swapTwin t t.flipSuit) = Sum.inr t
    rw [Card.swapTwin_self_right]
  have htop : st.board.topOf (Sum.inr t) = some z :=
    (Board.bottomOf_eq st.board z (Sum.inr t)).mp h₀
  refine (Board.bottomOf_eq _ z (Sum.inr t.flipSuit)).mpr ?_
  rw [State.exchangeTwinCargo_board, Board.exchangeTwin_topOf, hsw]
  exact htop

/-- Seats off the twin pair are untouched by the exchange (the
`hz'bare` transfer: the merge's own legality made `z'` bare in st, and
the exchange never reads `(inr z')`). -/
theorem exchangeTwinCargo_topOf_off_pair {st : State} {t w : Card}
    (hw₁ : w ≠ t) (hw₂ : w ≠ t.flipSuit) :
    (st.exchangeTwinCargo t).board.topOf (Sum.inr w) = st.board.topOf (Sum.inr w) := by
  rw [State.exchangeTwinCargo_board, Board.exchangeTwin_topOf,
    Base.swapTwin_eq_self (fun h => hw₁ (Sum.inr.inj h))
      (fun h => hw₂ (Sum.inr.inj h))]

/-- **The bare-cargo arm of the dislodge-existence trichotomy**: when
nothing rides `z` (the blocker absent), the mirror merge
`pilePile c (inr z)` fires immediately — the 0-move repair, board-only. -/
theorem mirror_fires_of_bare {st : State} {t' c z z' d : Card}
    (hdz : d ≠ z)
    (hbotZ : st.board.bottomOf z = some (Sum.inr t'))
    (hbotC : st.board.bottomOf c = some (Sum.inr d))
    (hz'z : z' = z.flipSuit)
    (hfit : canSitOn c z' = true)
    (hznot : z ∉ st.board.aboveOf c)
    (hzbare : st.board.topOf (Sum.inr z) = none) :
    ∃ s₂, st.apply (Move.pilePile c (Sum.inr z)) = some s₂ ∧
      s₂.board.topOf (Sum.inr z) = some c ∧
      s₂.board.topOf (Sum.inr d) = none ∧
      s₂.heights = st.heights ∧ s₂.stock = st.stock ∧ s₂.depths = st.depths := by
  have hvisz : st.isVis z = true := by
    show (st.board.bottomOf z).isSome = true
    rw [hbotZ]
    rfl
  have hfitM : canSitOn c z = true := by
    have h : canSitOn c z.flipSuit = true := by rw [← hz'z]; exact hfit
    rw [canSitOn_flipSuit_right c z] at h
    exact h
  have hcp : st.canPlace c (Sum.inr z) = true := by
    show (decide (st.board.topOf (Sum.inr z) = none) &&
        (st.isVis z && canSitOn c z)) = true
    rw [hzbare, hvisz, hfitM]
    rfl
  have hcont : (st.board.aboveOf c).contains z = false :=
    lcontains_false_of_notMem hznot
  have hcmr : st.canMoveRun c (Sum.inr z) = true := by
    rw [canMoveRun_inr_iff]
    exact ⟨hcp, hcont⟩
  have hdetFree : (st.board.detach (Sum.inr d)).topOf (Sum.inr z) = none := by
    rw [Board.detach_topOf_ne _ _ _ (fun h => hdz (Sum.inr.inj h).symm)]
    exact hzbare
  have hdetBot : (st.board.detach (Sum.inr d)).bottomOf c = none := by
    have htopD : st.board.topOf (Sum.inr d) = some c :=
      (Board.bottomOf_eq st.board c (Sum.inr d)).mp hbotC
    exact Board.bottomOf_detach_self htopD
  have hatt : (st.board.detach (Sum.inr d)).attach (Sum.inr z) c ≠ none := by
    rw [Board.attach_eq_some_iff]
    exact ⟨hdetFree, hdetBot⟩
  cases hB : (st.board.detach (Sum.inr d)).attach (Sum.inr z) c with
  | none => exact absurd hB hatt
  | some bd₂ =>
      refine ⟨{ st with board := bd₂ }, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [apply_pilePile_iff]
        exact ⟨Sum.inr d, hbotC, fun h => hdz (Sum.inr.inj h), hcmr, bd₂, hB, rfl⟩
      · show bd₂.topOf (Sum.inr z) = some c
        exact Board.attach_topOf _ _ _ hB
      · show bd₂.topOf (Sum.inr d) = none
        rw [Board.attach_topOf_ne _ _ _ hB (fun h => hdz (Sum.inr.inj h)),
            Board.detach_topOf]
      · rfl
      · rfl
      · rfl

/-! ## The second repair: the blocker stacks off, the mirror opens -/

/-- **The blocker-stacks-off mirror repair** (w15wfmerge's mechanism,
general form).  In the exchanged state the mirror merge
`pilePile c (inr z)` is blocked by the blocker `r` riding `z`.  When
`r` stacks off — the founds_gone cascade's terminal move (`r` live by
`wf_vis_rank`, its rung founded) — `z` bares and the mirror fires:
`c`'s run lands on `z`, the aftermath being the z↔z' twin-conjugate of
the source's post-merge state (the suit-gated switching point).  The
re-landing exposes the host `d`;  heights gain exactly `r`'s rung;
stock and depths are untouched. -/
theorem blocker_leaves_mirror {st : State} {t' c z z' d r : Card}
    (hdz : d ≠ z)
    (ht'z : t' ≠ z)
    (hbotZ : st.board.bottomOf z = some (Sum.inr t'))
    (hbotC : st.board.bottomOf c = some (Sum.inr d))
    (hz'z : z' = z.flipSuit)
    (hfit : canSitOn c z' = true)
    (hznot : z ∉ st.board.aboveOf c)
    (hrz : st.board.bottomOf r = some (Sum.inr z))
    (hrstacks : ∃ s₁, st.apply (Move.pileStack r) = some s₁) :
    ∃ s₁ s₂, st.apply (Move.pileStack r) = some s₁ ∧
      s₁.apply (Move.pilePile c (Sum.inr z)) = some s₂ ∧
      s₂.board.topOf (Sum.inr z) = some c ∧
      s₂.board.topOf (Sum.inr d) = none ∧
      s₂.heights = (fun s => if s = r.suit then st.heights s + 1 else st.heights s) ∧
      s₂.stock = st.stock ∧ s₂.depths = st.depths := by
  -- the st-level seats
  have htopT : st.board.topOf (Sum.inr t') = some z :=
    (Board.bottomOf_eq st.board z (Sum.inr t')).mp hbotZ
  have htopD : st.board.topOf (Sum.inr d) = some c :=
    (Board.bottomOf_eq st.board c (Sum.inr d)).mp hbotC
  -- the blocker's stacking, factored (the board is the detach at z's seat)
  obtain ⟨s₁, hs₁⟩ := hrstacks
  rw [apply_pileStack_iff] at hs₁
  obtain ⟨htopr, b, hb, hrk, -⟩ := hs₁
  have hbc : b = Sum.inr z := Option.some.inj (hb.symm.trans hrz)
  subst hbc
  -- z bares
  have hfree₁ : (st.board.detach (Sum.inr z)).topOf (Sum.inr z) = none :=
    Board.detach_topOf _ _
  -- z stays seated (its own seat is untouched)
  have htopT₁ : (st.board.detach (Sum.inr z)).topOf (Sum.inr t') = some z := by
    rw [Board.detach_topOf_ne _ _ _ (fun h => ht'z (Sum.inr.inj h))]
    exact htopT
  have hvisz₁ : ({ st with board := st.board.detach (Sum.inr z) } : State).isVis z = true := by
    show ((st.board.detach (Sum.inr z)).bottomOf z).isSome = true
    rw [(Board.bottomOf_eq _ z (Sum.inr t')).mpr htopT₁]
    rfl
  -- c's seat is untouched
  have htopD₁ : (st.board.detach (Sum.inr z)).topOf (Sum.inr d) = some c := by
    rw [Board.detach_topOf_ne _ _ _ (fun h => hdz (Sum.inr.inj h))]
    exact htopD
  have hbotC₁ : (st.board.detach (Sum.inr z)).bottomOf c = some (Sum.inr d) :=
    (Board.bottomOf_eq _ c (Sum.inr d)).mpr htopD₁
  -- the walk above c only shrinks under the detach: z stays out
  have hsub : ∀ b : Base, (st.board.detach (Sum.inr z)).topOf b = none ∨
      (st.board.detach (Sum.inr z)).topOf b = st.board.topOf b := by
    intro b
    by_cases hb : b = Sum.inr z
    · subst hb
      exact Or.inl (Board.detach_topOf _ _)
    · exact Or.inr (Board.detach_topOf_ne _ _ _ hb)
  have hznot₁ : z ∉ ({ st with board := st.board.detach (Sum.inr z) } : State).board.aboveOf c := by
    intro hy
    exact hznot (Board.aboveOf_sub hsub z hy)
  -- the mirror's guards (the fit is flip-blind: Theorems'
  -- `canSitOn_flipSuit_right`)
  have hfitM : canSitOn c z = true := by
    have h : canSitOn c z.flipSuit = true := by rw [← hz'z]; exact hfit
    rw [canSitOn_flipSuit_right c z] at h
    exact h
  have hcp : ({ st with board := st.board.detach (Sum.inr z) } : State).canPlace c (Sum.inr z) = true := by
    show (decide ((st.board.detach (Sum.inr z)).topOf (Sum.inr z) = none) &&
        (({ st with board := st.board.detach (Sum.inr z) } : State).isVis z &&
          canSitOn c z)) = true
    rw [hfree₁, hvisz₁, hfitM]
    rfl
  have hcont : (({ st with board := st.board.detach (Sum.inr z) } : State).board.aboveOf c).contains z = false :=
    lcontains_false_of_notMem hznot₁
  have hcmr : ({ st with board := st.board.detach (Sum.inr z) } : State).canMoveRun c (Sum.inr z) = true := by
    rw [canMoveRun_inr_iff]
    exact ⟨hcp, hcont⟩
  -- the mirror's attach
  have hdet2Free : ((st.board.detach (Sum.inr z)).detach (Sum.inr d)).topOf (Sum.inr z) = none := by
    rw [Board.detach_topOf_ne _ _ _ (fun h => hdz (Sum.inr.inj h).symm)]
    exact hfree₁
  have hdet2Bot : ((st.board.detach (Sum.inr z)).detach (Sum.inr d)).bottomOf c = none :=
    Board.bottomOf_detach_self htopD₁
  have hatt₂ : ((st.board.detach (Sum.inr z)).detach (Sum.inr d)).attach (Sum.inr z) c ≠ none := by
    rw [Board.attach_eq_some_iff]
    exact ⟨hdet2Free, hdet2Bot⟩
  cases hB : ((st.board.detach (Sum.inr z)).detach (Sum.inr d)).attach (Sum.inr z) c with
  | none => exact absurd hB hatt₂
  | some bd₂ =>
      refine ⟨{ st with
                board := st.board.detach (Sum.inr z)
                heights := fun s => if s = r.suit then st.heights s + 1 else st.heights s },
              { st with
                board := bd₂
                heights := fun s => if s = r.suit then st.heights s + 1 else st.heights s },
              apply_pileStack_iff.mpr ⟨htopr, Sum.inr z, hrz, hrk, rfl⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [apply_pilePile_iff]
        exact ⟨Sum.inr d, hbotC₁, fun h => hdz (Sum.inr.inj h), hcmr, bd₂, hB, rfl⟩
      · show bd₂.topOf (Sum.inr z) = some c
        exact Board.attach_topOf _ _ _ hB
      · show bd₂.topOf (Sum.inr d) = none
        rw [Board.attach_topOf_ne _ _ _ hB (fun h => hdz (Sum.inr.inj h)),
            Board.detach_topOf]
      · rfl
      · rfl
      · rfl

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

/-! ## The composite: dislodge, then re-land on the freed twin cargo -/

/-- **The dislodge-and-reland collapse, general form.**  Whenever the
twin's sub-run (whose head `t` carries `z'`, the other twin's cargo,
on its back) has ANY legal landing — a free anchor (the king case,
`park_king_run`), a fit, a deal-adjacent seat — the two-move collapse
fires: the sub-run moves (taking `z'` out of `c`'s walk), and `c`
re-lands on the now-bare `z'`:  the mirror merge, two moves later,
from ANY dislodge.  The re-landing exposes the host `d` under `c`
and touches nothing but the board (heights, stock, depths preserved).

The target exclusions are derived, not premises: the dislodge cannot
land on `t` or `d` (their seats are occupied — the attach's
freeness), nor on `z'` (the self-landing guard: `z'` rides `t`, so it
is IN the run above `t`, by `aboveOf_contains_topOf`). -/
theorem dislodge_reland {st : State} {t c z' d : Card} {b : Base}
    (hct : c ≠ t)
    (hbotT : st.board.bottomOf t = some (Sum.inr c))
    (hbotZ : st.board.bottomOf z' = some (Sum.inr t))
    (hbotC : st.board.bottomOf c = some (Sum.inr d))
    (hz'bare : st.board.topOf (Sum.inr z') = none)
    (hfit : canSitOn c z' = true)
    (hdislodge : ∃ s₁, st.apply (Move.pilePile t b) = some s₁) :
    ∃ s₁ s₂, st.apply (Move.pilePile t b) = some s₁ ∧
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
  -- the dislodge, factored
  obtain ⟨s₁, hs₁⟩ := hdislodge
  rw [apply_pilePile_iff] at hs₁
  obtain ⟨b₀, hb₀, hne, hcmr, bd₁, hatt, -⟩ := hs₁
  have hb₀c : b₀ = Sum.inr c := Option.some.inj (hb₀.symm.trans hbotT)
  subst hb₀c
  -- the target exclusions
  have hattne : (st.board.detach (Sum.inr c)).attach b t ≠ none := by
    intro hcon
    rw [hcon] at hatt
    simp at hatt
  have hfreeT := ((Board.attach_eq_some_iff _ _ _).mp hattne).1
  have hbt : b ≠ Sum.inr t := by
    intro h
    subst h
    rw [Board.detach_topOf_ne _ _ _ (fun h => hct (Sum.inr.inj h).symm), hz'top] at hfreeT
    simp at hfreeT
  have hbd : b ≠ Sum.inr d := by
    intro h
    subst h
    rw [Board.detach_topOf_ne _ _ _ (fun h => hdc (Sum.inr.inj h)), hctop] at hfreeT
    simp at hfreeT
  have hbz' : b ≠ Sum.inr z' := by
    intro h
    subst h
    rw [canMoveRun_inr_iff] at hcmr
    obtain ⟨-, hcont⟩ := hcmr
    rw [aboveOf_contains_topOf hz'top] at hcont
    simp at hcont
  -- the dislodged board's seats
  have htop₁_c : bd₁.topOf (Sum.inr c) = none := by
    rw [Board.attach_topOf_ne _ _ _ hatt hne, Board.detach_topOf]
  have htop₁_z' : bd₁.topOf (Sum.inr z') = none := by
    rw [Board.attach_topOf_ne _ _ _ hatt (fun h => hbz' h.symm),
        Board.detach_topOf_ne _ _ _ (fun h => hz'c (Sum.inr.inj h))]
    exact hz'bare
  have htop₁_t : bd₁.topOf (Sum.inr t) = some z' := by
    rw [Board.attach_topOf_ne _ _ _ hatt (fun h => hbt h.symm),
        Board.detach_topOf_ne _ _ _ (fun h => hct (Sum.inr.inj h).symm)]
    exact hz'top
  have htop₁_d : bd₁.topOf (Sum.inr d) = some c := by
    rw [Board.attach_topOf_ne _ _ _ hatt (fun h => hbd h.symm),
        Board.detach_topOf_ne _ _ _ (fun h => hdc (Sum.inr.inj h))]
    exact hctop
  -- the re-land's guards, at the dislodged board
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
  -- the re-land's attach
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
      refine ⟨{ st with board := bd₁ }, { st with board := bd₂ },
        apply_pilePile_iff.mpr ⟨Sum.inr c, hbotT, hne, hcmr, bd₁, hatt, rfl⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
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

/-- **The anchor-relocation collapse, king instance.**  With the twin
`t` a king and an anchor free: the sub-run parks there, then `c`
re-lands on the freed twin cargo.  (The instance of `dislodge_reland`
the probe exhibits; the general form needs only SOME landing.) -/
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
  obtain ⟨bd₁, -, hs₁⟩ := park_king_run hbotT hking hfree
  exact dislodge_reland hct hbotT hbotZ hbotC hz'bare hfit ⟨{ st with board := bd₁ }, hs₁⟩

/-! ## The bare-rung composition + the trichotomy skeleton -/

/-- The rung's stacking: a bare, seated, exactly-at-the-rung card
stacks off (`pileStack` fires) — the cascade's terminal move. -/
theorem rung_stacks {st : State} {r : Card}
    (hbot : ∃ b, st.board.bottomOf r = some b)
    (hrbar : st.board.topOf (Sum.inr r) = none)
    (hrk : r.rank.toIdx = st.heights r.suit) :
    ∃ s1, st.apply (Move.pileStack r) = some s1 := by
  obtain ⟨b, hb⟩ := hbot
  exact ⟨{ st with
    board := st.board.detach b
    heights := fun s => if s = r.suit then st.heights s + 1 else st.heights s },
    apply_pileStack_iff.mpr ⟨hrbar, b, hb, hrk, rfl⟩⟩

/-- **The w15wfmerge happy path, end-to-end**: when the blocker `r`
riding `z` is a BARE RUNG (`r.rank = heights(r.suit)`, nothing above
`r`), it stacks off and the mirror merge fires — two moves, no
founds_gone needed (the liveness content enters only when `r` is NOT
the rung: that is the cascade obligation). -/
theorem mirror_of_bare_rung {st : State} {t' c z z' d r : Card}
    (hdz : d ≠ z)
    (ht'z : t' ≠ z)
    (hbotZ : st.board.bottomOf z = some (Sum.inr t'))
    (hbotC : st.board.bottomOf c = some (Sum.inr d))
    (hz'z : z' = z.flipSuit)
    (hfit : canSitOn c z' = true)
    (hznot : z ∉ st.board.aboveOf c)
    (hrz : st.board.bottomOf r = some (Sum.inr z))
    (hrbar : st.board.topOf (Sum.inr r) = none)
    (hrk : r.rank.toIdx = st.heights r.suit) :
    ∃ s1 s2, st.apply (Move.pileStack r) = some s1 ∧
      s1.apply (Move.pilePile c (Sum.inr z)) = some s2 ∧
      s2.board.topOf (Sum.inr z) = some c ∧
      s2.board.topOf (Sum.inr d) = none ∧
      s2.heights = (fun s => if s = r.suit then st.heights s + 1 else st.heights s) ∧
      s2.stock = st.stock ∧ s2.depths = st.depths :=
  blocker_leaves_mirror hdz ht'z hbotZ hbotC hz'z hfit hznot hrz
    (rung_stacks ⟨_, hrz⟩ hrbar hrk)

/-- The merge-ply case skeleton: either the mirror target `z` is bare
(arm (a): `mirror_fires_of_bare`), or a blocker `r` rides it — and
when that blocker is a bare rung, `mirror_of_bare_rung` closes arm (b)
outright.  The remaining corner (a covered or non-rung blocker) is the
cascade obligation. -/
theorem merge_ply_cases {st : State} {z : Card} :
    st.board.topOf (Sum.inr z) = none ∨ ∃ r, st.board.bottomOf r = some (Sum.inr z) := by
  cases hz : st.board.topOf (Sum.inr z) with
  | none => exact Or.inl rfl
  | some r => exact Or.inr ⟨r, (Board.bottomOf_eq st.board r (Sum.inr z)).mpr hz⟩

/-- Arm (c)'s king case, in the existential form `dislodge_reland`
consumes: a king twin with a free anchor always has the dislodge. -/
theorem king_dislodge_exists {st : State} {t c : Card} {a : Anchor}
    (hbotT : st.board.bottomOf t = some (Sum.inr c))
    (hking : t.rank = Rank.king)
    (hfree : st.board.topOf (Sum.inl a) = none) :
    ∃ s1, st.apply (Move.pilePile t (Sum.inl a)) = some s1 := by
  obtain ⟨bd1, -, hs1⟩ := park_king_run hbotT hking hfree
  exact ⟨{ st with board := bd1 }, hs1⟩

/-! ## The fusion point: the merge-mirror conjugation -/

/-! ## The fusion point: the merge-mirror conjugation (DESIGNED, next pass) -/

/-! The next lemma, fully designed (the case analysis verified on paper;
the write is mechanical, ~150 lines): `merge_mirror_conjugate` —

    (hz'z : z' = z.flipSuit) (hznt : z ≠ t) (hznt' : z ≠ t.flipSuit)
    (hbotZ : st.board.bottomOf z = some (Sum.inr t))
    (hbotZ' : st.board.bottomOf z' = some (Sum.inr t.flipSuit))
    (hmerge : st.apply (Move.pilePile c (Sum.inr z')) = some a₁)
    (hmirror : (st.exchangeTwinCargo t).apply (Move.pilePile c (Sum.inr z)) = some s₂) :
    s₂ = { a₁ with board := a₁.board.mapByTwin z }

**The suit-gated switching point, formal**: both aftermaths are the
z↔z' RELABELING CONJUGATES of each other.  The merge bridge's
both-bare arm then reduces to the conjugated-solvability question —
the suit-reading correspondence the window machinery exists for.

Proof skeleton: unpack both moves (apply_pilePile_iff + canMoveRun_inr_iff:
z'/z bare, the fits); the off-pair grid (z ≠ z'; t ≠ z' via hznt' +
flipSuit_flipSuit; t' ≠ z; c ≠ z/z' via the fits' rank arithmetic);
b₀ off all four twin/cargo seats (topOf clashes); b₀' = b₀ (c's seat
survives the exchange); then Board.ext_topOf + funext with six seat
cases — (inr t): z' vs (some z).map = z' via swapTwin_self_left;
(inr t'): z vs z'.map via swapTwin_self_right; (inr z): c vs
attach_topOf; (inr z'): none vs none (both bare, seats off the other
pair); b₀: none vs none (both detaches); generic b: st.topOf b on
both sides (the card at b is off-pair by Board.inj — z sits only at
(inr t), z' only at (inr t')); the non-map side through
exchangeTwin_topOf + swapTwin_of_ne/swapTwin_eq_self at every step.
Close with state_ext (five rfl fields — the exchange and both merges
touch only boards). -/

/-! ## The unseating taxonomy (the play-level disciplines' keystone) -/

/-- The freeness of a successful attach (the `≠ none` bridge,
`attach_eq_some_iff`'s hidden conversion). -/
theorem attach_frees {bd : Board} {b : Base} {c : Card} {bd' : Board}
    (hatt : bd.attach b c = some bd') : bd.topOf b = none := by
  have hne : bd.attach b c ≠ none := by
    intro hcon
    rw [hcon] at hatt
    simp at hatt
  exact ((Board.attach_eq_some_iff bd b c).mp hne).1

/-- **The only move that unseats a card is `pileStack` of that card**:
every other move either leaves the board alone (draw, deckStack),
attaches at a free seat (reveal, deckPile, stackPile — a free seat
cannot be `t`'s occupied seat), or re-attaches the moved run
(`pilePile` — the run head re-seats, riders ride along).  The
keystone of the winning-line disciplines: "t must stack" (the §12.1
extraction corollary) composes with this to force
dislodge-before-stack orderings. -/
theorem unseats_imp_pileStack {st s' : State} {m : Move} {t : Card}
    (happly : st.apply m = some s')
    (hbot : st.board.bottomOf t ≠ none)
    (hbot' : s'.board.bottomOf t = none) :
    m = Move.pileStack t := by
  cases hb : st.board.bottomOf t with
  | none => exact absurd hb hbot
  | some b₀ =>
    have htop₀ : st.board.topOf b₀ = some t :=
      (Board.bottomOf_eq st.board t b₀).mp hb
    cases m with
    | draw =>
        rw [apply_draw_iff] at happly
        obtain rfl := happly
        have hnone : st.board.bottomOf t = none := hbot'
        rw [hnone] at hb
        simp at hb
    | reveal a =>
        rw [apply_reveal_iff] at happly
        obtain ⟨r, bd, -, -, hatt, rfl⟩ := happly
        have hf : st.board.topOf (st.hiddenBase a) = none := attach_frees hatt
        have hne : b₀ ≠ st.hiddenBase a := by
          intro heq
          rw [heq] at htop₀
          rw [htop₀] at hf
          simp at hf
        have eq1 : bd.topOf b₀ = some t := by
          rw [Board.attach_topOf_ne _ _ _ hatt hne]
          exact htop₀
        have hnone : bd.bottomOf t = none := hbot'
        rw [(Board.bottomOf_eq _ t b₀).mpr eq1] at hnone
        simp at hnone
    | deckPile c b =>
        rw [apply_deckPile_iff] at happly
        obtain ⟨-, -, bd, hatt, rfl⟩ := happly
        have hf : st.board.topOf b = none := attach_frees hatt
        have hne : b₀ ≠ b := by
          intro heq
          rw [heq] at htop₀
          rw [htop₀] at hf
          simp at hf
        have eq1 : bd.topOf b₀ = some t := by
          rw [Board.attach_topOf_ne _ _ _ hatt hne]
          exact htop₀
        have hnone : bd.bottomOf t = none := hbot'
        rw [(Board.bottomOf_eq _ t b₀).mpr eq1] at hnone
        simp at hnone
    | deckStack c =>
        rw [apply_deckStack_iff] at happly
        obtain ⟨-, -, rfl⟩ := happly
        have hnone : st.board.bottomOf t = none := hbot'
        rw [hnone] at hb
        simp at hb
    | pileStack c =>
        rw [apply_pileStack_iff] at happly
        obtain ⟨-, b, hb1, -, rfl⟩ := happly
        by_cases hct : c = t
        · subst hct
          rfl
        · have hne : b₀ ≠ b := by
            intro heq
            rw [heq] at htop₀
            rw [(Board.bottomOf_eq st.board c b).mp hb1] at htop₀
            exact hct (Option.some.inj htop₀)
          have eq1 : (st.board.detach b).topOf b₀ = some t := by
            rw [Board.detach_topOf_ne _ _ _ hne]
            exact htop₀
          have hnone : (st.board.detach b).bottomOf t = none := hbot'
          rw [(Board.bottomOf_eq _ t b₀).mpr eq1] at hnone
          simp at hnone
    | stackPile c b =>
        rw [apply_stackPile_iff] at happly
        obtain ⟨-, -, bd, hatt, rfl⟩ := happly
        have hf : st.board.topOf b = none := attach_frees hatt
        have hne : b₀ ≠ b := by
          intro heq
          rw [heq] at htop₀
          rw [htop₀] at hf
          simp at hf
        have eq1 : bd.topOf b₀ = some t := by
          rw [Board.attach_topOf_ne _ _ _ hatt hne]
          exact htop₀
        have hnone : bd.bottomOf t = none := hbot'
        rw [(Board.bottomOf_eq _ t b₀).mpr eq1] at hnone
        simp at hnone
    | pilePile c b =>
        rw [apply_pilePile_iff] at happly
        obtain ⟨b', hb', -, -, bd, hatt, rfl⟩ := happly
        by_cases hbb' : b₀ = b'
        · have hct : c = t := by
            have h1 : st.board.topOf b' = some c :=
              (Board.bottomOf_eq st.board c b').mp hb'
            rw [← hbb'] at h1
            rw [h1] at htop₀
            exact Option.some.inj htop₀
          rw [hct] at hatt
          have eq1 : bd.topOf b = some t := Board.attach_topOf _ _ _ hatt
          have hnone : bd.bottomOf t = none := hbot'
          rw [(Board.bottomOf_eq _ t b).mpr eq1] at hnone
          simp at hnone
        · have hf : (st.board.detach b').topOf b = none := attach_frees hatt
          have hne : b₀ ≠ b := by
            intro heq
            rw [← heq] at hf
            rw [Board.detach_topOf_ne _ _ _ (fun h => hbb' h)] at hf
            rw [htop₀] at hf
            simp at hf
          have eq1 : bd.topOf b₀ = some t := by
            rw [Board.attach_topOf_ne _ _ _ hatt hne,
                Board.detach_topOf_ne _ _ _ (fun h => hbb' h)]
            exact htop₀
          have hnone : bd.bottomOf t = none := hbot'
          rw [(Board.bottomOf_eq _ t b₀).mpr eq1] at hnone
          simp at hnone

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
