import Klondike.Initial

/-!
# The pile-to-pile restriction (B2) — scaffold

The engine never plays a bare pile-to-pile move: every run relocation
is *implicit* — either a shuffle detour (`pileStack`/`stackPile`, the
accommodation channel) or fused into a run-carrying `Reveal`
(state.rs:312 — "revealing a card by moving the top card to another
pile").  B2 is the claim that this restriction loses nothing: a dealt
game is winnable in the full physical game iff it is winnable with the
engine's move set.

**Why the naive form died** (witnesses/EngineWitness.lean, archived in
FARM.md's REFUTED section): the model's `reveal` is *bare-trigger* —
it seats the boundary card only while a visible card still sits on it —
while the engine's `Reveal` is run-carrying.  At arbitrary WF states
the concrete move subset is strictly weaker (the p2 = [♥3, ♠5, ♥4]
deadlock).  The repaired statement must therefore be scoped to what
the engine actually solves: **states reachable from a dealt game**.

**Where the twin swap enters** (already proven, ready to cite): the
B4 endgame's worry-back has *two* candidate bases — the rank-`r+1`,
opposite-colour twins (`Card.only_blocker_is_twin`).  The choice
between them is a placement equivalence, licensed exactly like §5.5's
`twinPair_placement_equi`: `solvable_relabel`/`solvable_flipAll`
(Relabel.lean, proven, axiom-clean) applied as a local swap under the
both-heights-equal condition.  No *local* two-card swap theorem is
needed for this skeleton.

## Proof route (the B2 main induction)

`←` of the headline is `solvable_of_engine` (Move.lean, proven).  `→`
is well-founded induction on `cascadeMeasure` (Dominance.lean —
proven, with `cascade_escape_progress`): at each state, case-split on
the first move of a winning play; every engine move is verbatim; a
`pilePile c b` is replayed per the step lemma below, and the escapes
(strict measure drops) are what make the induction well-founded rather
than circular.

The step's cases (the EngineWitness shapes are the fence posts):
1. **returnable base** (`canReturnBase`): the `stackPile`/`pileStack`
   detour — proven kits: `stackPile_pileStack_cancel`,
   `pileStack_comm_*` squares, `solvable_of_stackPile`.
2. **locked boundary carry** (the EngineWitness shape): the run sits
   on the hidden boundary — the worry-back ban routes through B4's
   `solvable_of_pileStack` (sorried crux, Theorems.lean) plus the
   rank-mate twin argument above.
3. **the deadlock escape hatch**: if a full-deck probe ever replays
   the EngineWitness state from `State.initial wdeal 1`, this file's
   statements fall and the model needs the run-carrying-reveal repair
   (track R, design decision — recorded in FARM.md).

Refute-first gate: reachability probe - reconstruct the EngineWitness
state by a play from `State.initial wdeal 1`.  **CLOSED 2026-09-15 -
unreachable**: `witnesses/EngineReachProbe.lean` proves
`EngineWitness.wstate_not_reachable : initialReachable wstate -> False` by a
four-way probe invariant on the mono-suit pile `p3` (its inner edges
form only through descending reveals, and digging past them breaks a
same-suit link that `canSitOn` can never re-form).  Stronger than the
gate asked: unreachability holds against the FULL move set.  The
statement below stands as written; the escape hatch (case 3) is empty.
-/

/-- Reachable from a dealt game: the domain the engine actually plays
on, and the domain under which the pile-to-pile restriction is
believed to hold. -/
def initialReachable (st : State) : Prop :=
  ∃ (d : Deal) (s : Nat) (play : List Move), d.WF ∧ 0 < s ∧
    (State.initial d s).run play = some st

/-- **B2, the engine's license**: on states reached from a deal, the
full physical game and the engine's restricted move set have the same
solvability.  The `→` direction is `solvable_of_engine` (proven);
`←` is the restriction.

TODO(proof) **[H]**: the well-founded `cascadeMeasure` induction whose
per-move replay is `engine_replay_of_pilePile` below (plus the B4 crux
for the boundary-carry case).  Witness fence: `EngineWitness`'s state
must not satisfy `initialReachable` — the refute-first probe above
decides whether this statement stands as written. -/
theorem solvableEngine_iff_solvable_of_reachable {st : State}
    (hreach : initialReachable st) (hwf : st.WF) :
    st.solvableFrom ↔ st.solvableEngine := sorry

/-- **The replay step**: from a dealt-reachable state, a winning play
headed by a pile-to-pile move can be replaced by an engine-only win —
every pile-to-pile is implicit.

TODO(proof) **[H]**: case-split per the header's ledger.  Case 1 is
assembled from proven pieces (`stackPile_pileStack_cancel` +
`pileStack_comm_*` + the roundtrips); case 2 reduces to the B4 crux
`solvable_of_pileStack` — note its `hnotlock` gate matches exactly the
boundary-carry shape here (a locked sitter IS the EngineWitness
trigger); case 3 is the probe's alarm.  The twin placement in case 2's
endgame cites `solvable_flipAll` under the both-heights-equal license —
the same pattern as `twinPair_placement_equi`. -/
theorem engine_replay_of_pilePile {st : State}
    (hreach : initialReachable st) (hwf : st.WF) {c : Card} {b : Base}
    (hlegal : st.legal (Move.pilePile c b) = true)
    (hsol : st.solvableFrom) : st.solvableEngine := sorry

/-! ## The clean-stacks theorem

Reachable states have clean visible stacks: every edge whose base
card is itself visible follows the chaining rule (one rank down,
alternating color), and anchors hold kings or the dealt head.  The
physical reveal rule (bare-boundary only) is what makes this TRUE:
under the old reveal-through the boundary seated under a
still-seated trigger, producing a dirty visible stack one move from
the initial state.  Under the repaired rule a deal-adjacent edge can
never gain a seated base — the boundary must be bare to be revealed,
so the sitter is always gone before the base seats, and the only
edges ever created on a seated base are canPlace-guarded placements.

The proof is the invariant argument: `visClean` holds at the initial
state (vacuously — the initial edges' bases are anchors and hidden
cards, never visible) and survives every move.  WF rides along (its
preservation is `apply_wf`, already proven): the three corners that
need it are the refutations of pre-existing edges on stock and
foundation cards (board_edges + noDup + vis_off_cycle / founds_gone)
and the reveal's under-card/boundary distinctness (the deal slice is
duplicate-free). -/

/-- The hiddenBase's card and the boundary decompose the hidden
slice: `hidden a = pre ++ [d, r]` — the under-card directly beneath
the boundary. -/
theorem hiddenBase_split {st : State} {a : Anchor} {d r : Card}
    (hbb : st.hiddenBase a = Sum.inr d) (hgt : st.topHidden a = some r) :
    ∃ pre, st.hidden a = pre ++ [d, r] := by
  have hrev : ((st.hidden a).reverse.drop 1).head? = some d := by
    simp only [State.hiddenBase] at hbb
    cases hh : ((st.hidden a).reverse.drop 1).head? with
    | none => rw [hh] at hbb; exact absurd hbb (by simp)
    | some d' =>
        rw [hh] at hbb
        exact congrArg some (Sum.inr.inj hbb)
  exact hidden_split hrev hgt

theorem hiddenBase_ne_topHidden {st : State} {a : Anchor} {d r : Card}
    (hwf : st.WF) (hbb : st.hiddenBase a = Sum.inr d)
    (hgt : st.topHidden a = some r) : d ≠ r := by
  intro hcon
  obtain ⟨pre, hpre⟩ := hiddenBase_split hbb hgt
  have hlen : (st.hidden a).length = pre.length + 2 := by rw [hpre]; simp
  have hdpt : (st.hidden a).length = st.depths a := by
    show ((st.deal.piles a).take (st.depths a)).length = st.depths a
    rw [List.length_take]
    have := hwf.depths_le a
    omega
  have hsub : st.depths a - 1 = pre.length + 1 := by omega
  have hsub2 : pre.length + 1 - pre.length = 1 := by omega
  have hs2 : st.deal.piles a = pre ++ d :: r :: (st.deal.piles a).drop (st.depths a) := by
    have htd : st.deal.piles a = st.hidden a ++ (st.deal.piles a).drop (st.depths a) :=
      (List.take_append_drop (st.depths a) (st.deal.piles a)).symm
    rw [hpre] at htd
    calc st.deal.piles a = (pre ++ [d, r]) ++ (st.deal.piles a).drop (st.depths a) := htd
      _ = pre ++ d :: r :: (st.deal.piles a).drop (st.depths a) := by simp
  have hnh : (st.deal.piles a).take (st.depths a - 1) = pre ++ [d] := by
    rw [hs2, hsub, List.take_append, take_length_succ_self, hsub2]
    rfl
  exact notMem_take_of_get (Deal.pile_noDup hwf.deal_wf a)
    (topHidden_get (hwf.depths_le a) hgt) (by rw [← hcon, hnh]; simp)

/-- The clean-stacks invariant: every edge whose base card is
itself visible (seated) follows the chaining rule. -/
def State.visClean (st : State) : Prop :=
  ∀ c d, st.board.topOf (Sum.inr d) = some c →
    st.isVis d = true → canSitOn c d = true

/-- One move preserves the invariant. -/
theorem apply_visClean {st st' : State} {m : Move}
    (hwf : st.WF) (hv : st.visClean) (h : st.apply m = some st') : st'.visClean := by
  intro c d htop hvis
  cases m with
  | draw =>
      rw [apply_draw_iff] at h
      obtain ⟨rfl⟩ := h
      exact hv c d htop hvis
  | deckStack q =>
      rw [apply_deckStack_iff] at h
      obtain ⟨-, -, rfl⟩ := h
      exact hv c d htop hvis
  | reveal a =>
      rw [apply_reveal_iff] at h
      obtain ⟨r, bd, htoph, hbare, hatt, rfl⟩ := h
      have htop' : bd.topOf (Sum.inr d) = some c := htop
      by_cases hbb : st.hiddenBase a = Sum.inr d
      · -- the new edge: the base is the hidden slice's under-card, never visible
        obtain ⟨pre, hpre⟩ := hiddenBase_split hbb htoph
        have hmem : d ∈ st.hidden a := by rw [hpre]; simp
        have hdc : d ≠ r := hiddenBase_ne_topHidden hwf hbb htoph
        have hbotd : bd.bottomOf d = st.board.bottomOf d := bottomOf_attach_ne hatt hdc
        have hnotvis : (bd.bottomOf d).isSome = false := by
          rw [hbotd]
          show (st.board.bottomOf d).isSome = false
          cases hh : st.board.bottomOf d with
          | none => rfl
          | some β =>
              have hvv : st.isVis d = true := by
                show (st.board.bottomOf d).isSome = true
                rw [hh]; rfl
              exact (hwf.vis_not_hidden d hvv a hmem).elim
        have hvis' : (bd.bottomOf d).isSome = true := hvis
        rw [hnotvis] at hvis'
        exact Bool.noConfusion hvis'
      · -- a surviving edge
        have hsurv : st.board.topOf (Sum.inr d) = some c := by
          rw [← Board.attach_topOf_ne _ _ _ hatt (fun hc => hbb hc.symm)]
          exact htop'
        have hdc : d ≠ r := by
          intro hcon
          rw [← hcon] at hbare
          rw [hbare] at hsurv
          exact absurd hsurv (by simp)
        have hbotd : bd.bottomOf d = st.board.bottomOf d := bottomOf_attach_ne hatt hdc
        have hvi : st.isVis d = true := by
          show (st.board.bottomOf d).isSome = true
          rw [← hbotd]
          exact hvis
        exact hv c d hsurv hvi
  | deckPile c₀ b =>
      rw [apply_deckPile_iff] at h
      obtain ⟨hprev, hcp, bd, hatt, rfl⟩ := h
      have htop' : bd.topOf (Sum.inr d) = some c := htop
      by_cases hbb : b = Sum.inr d
      · -- the new edge: canPlace gave the fit directly
        subst hbb
        have hcc : c = c₀ :=
          (Option.some.inj ((Board.attach_topOf _ _ _ hatt).symm.trans htop')).symm
        subst hcc
        simp only [State.canPlace, Bool.and_eq_true_iff, decide_eq_true_iff] at hcp
        obtain ⟨-, -, hcs⟩ := hcp
        exact hcs
      · -- a surviving edge
        have hsurv : st.board.topOf (Sum.inr d) = some c := by
          rw [← Board.attach_topOf_ne _ _ _ hatt (fun hc => hbb hc.symm)]
          exact htop'
        by_cases hdc : d = c₀
        · subst hdc
          by_cases hvisc : st.isVis d = true
          · exact hv c d hsurv hvisc
          · -- refute the pre-edge: a stock card carries no tableau edge
            exfalso
            obtain ⟨-, hleg⟩ := hwf.board_edges (Sum.inr d) c hsurv
            rcases hleg with ⟨a', t, rest, hadj, -⟩ | ⟨his, -⟩
            · exact Deal.piles_stock_disj hwf.deal_wf (by rw [hadj]; simp)
                (hwf.stock_wf.2 d (by
                  simp only [Cycle.prev] at hprev
                  split at hprev
                  · exact absurd hprev (by simp)
                  · exact List.mem_iff_getElem?.mpr ⟨st.stock.cursor - 1, hprev⟩))
            · exact absurd his hvisc
        · have hbotd : bd.bottomOf d = st.board.bottomOf d := bottomOf_attach_ne hatt hdc
          have hvi : st.isVis d = true := by
            show (st.board.bottomOf d).isSome = true
            rw [← hbotd]
            exact hvis
          exact hv c d hsurv hvi
  | stackPile c₀ b =>
      rw [apply_stackPile_iff] at h
      obtain ⟨hrk, hcp, bd, hatt, rfl⟩ := h
      have htop' : bd.topOf (Sum.inr d) = some c := htop
      by_cases hbb : b = Sum.inr d
      · subst hbb
        have hcc : c = c₀ :=
          (Option.some.inj ((Board.attach_topOf _ _ _ hatt).symm.trans htop')).symm
        subst hcc
        simp only [State.canPlace, Bool.and_eq_true_iff, decide_eq_true_iff] at hcp
        obtain ⟨-, -, hcs⟩ := hcp
        exact hcs
      · have hsurv : st.board.topOf (Sum.inr d) = some c := by
          rw [← Board.attach_topOf_ne _ _ _ hatt (fun hc => hbb hc.symm)]
          exact htop'
        by_cases hdc : d = c₀
        · subst hdc
          by_cases hvisc : st.isVis d = true
          · exact hv c d hsurv hvisc
          · -- refute the pre-edge: a foundation card carries no tableau edge
            exfalso
            have hof : d.rank.toIdx < st.heights d.suit := by omega
            obtain ⟨-, hleg⟩ := hwf.board_edges (Sum.inr d) c hsurv
            rcases hleg with ⟨a', t, rest, hadj, hbase⟩ | ⟨his, -⟩
            · rcases hbase with ⟨a'', hth⟩ | his₀
              · exact (hwf.founds_gone d hof).2.2 a'' (mem_of_getLast hth)
              · exact absurd his₀ hvisc
            · exact absurd his hvisc
        · have hbotd : bd.bottomOf d = st.board.bottomOf d := bottomOf_attach_ne hatt hdc
          have hvi : st.isVis d = true := by
            show (st.board.bottomOf d).isSome = true
            rw [← hbotd]
            exact hvis
          exact hv c d hsurv hvi
  | pileStack c₀ =>
      rw [apply_pileStack_iff] at h
      obtain ⟨htopn, b₀, hbot, hrk, rfl⟩ := h
      have htop' : (st.board.detach b₀).topOf (Sum.inr d) = some c := htop
      by_cases hbb : Sum.inr d = b₀
      · rw [hbb, Board.detach_topOf] at htop'
        exact absurd htop' (by simp)
      · have hsurv : st.board.topOf (Sum.inr d) = some c := by
          rw [← Board.detach_topOf_ne st.board b₀ _ hbb]
          exact htop'
        by_cases hdc : d = c₀
        · subst hdc
          -- nothing sits on the stacked card (its own guard)
          rw [Board.detach_topOf_ne st.board b₀ _ hbb, htopn] at htop'
          exact absurd htop' (by simp)
        · have hbotd : (st.board.detach b₀).bottomOf d = st.board.bottomOf d :=
            bottomOf_detach_ne ((Board.bottomOf_eq st.board c₀ b₀).mp hbot) hdc
          have hvi : st.isVis d = true := by
            show (st.board.bottomOf d).isSome = true
            rw [← hbotd]
            exact hvis
          exact hv c d hsurv hvi
  | pilePile c₀ b =>
      rw [apply_pilePile_iff] at h
      obtain ⟨b₀, hbot, hne, hcmr, bd, hatt, rfl⟩ := h
      have htop' : bd.topOf (Sum.inr d) = some c := htop
      by_cases hbb : b = Sum.inr d
      · -- the new root edge: canMoveRun gave the fit
        subst hbb
        have hcc : c = c₀ :=
          (Option.some.inj ((Board.attach_topOf _ _ _ hatt).symm.trans htop')).symm
        subst hcc
        simp only [State.canMoveRun, Bool.and_eq_true_iff] at hcmr
        obtain ⟨hcp, -⟩ := hcmr
        simp only [State.canPlace, Bool.and_eq_true_iff, decide_eq_true_iff] at hcp
        obtain ⟨-, -, hcs⟩ := hcp
        exact hcs
      · -- surviving edges: the old root's base is gone, everything else rides
        have hbb₀ : Sum.inr d ≠ b₀ := by
          intro hcon
          have h1 : bd.topOf (Sum.inr d) = none := by
            rw [hcon]
            rw [show bd.topOf b₀ = (st.board.detach b₀).topOf b₀ from
              Board.attach_topOf_ne _ _ _ hatt hne]
            exact Board.detach_topOf _ _
          rw [h1] at htop'
          exact absurd htop' (by simp)
        have hsurv : st.board.topOf (Sum.inr d) = some c := by
          rw [← Board.detach_topOf_ne st.board b₀ _ hbb₀,
              ← Board.attach_topOf_ne _ _ _ hatt (fun hc => hbb hc.symm)]
          exact htop'
        by_cases hdc : d = c₀
        · -- the run's own root edge: the base card was and stays seated
          subst hdc
          exact hv c d hsurv (by
            show (st.board.bottomOf d).isSome = true
            rw [hbot]; rfl)
        · have hbotd : bd.bottomOf d = st.board.bottomOf d := by
            rw [bottomOf_attach_ne hatt hdc,
              bottomOf_detach_ne ((Board.bottomOf_eq st.board c₀ b₀).mp hbot) hdc]
          have hvi : st.isVis d = true := by
            show (st.board.bottomOf d).isSome = true
            rw [← hbotd]
            exact hvis
          exact hv c d hsurv hvi

/-- The initial state has the invariant (vacuously: every initial
edge's base is an anchor or a hidden card, never a visible one — the
under-cards and the top cards are dealt-distinct). -/
theorem initial_visClean (d : Deal) (drawStep : Nat) (hd : d.WF) :
    (State.initial d drawStep).visClean := by
  obtain ⟨hlen, hstock, hnd⟩ := hd
  intro c d₀ htop hvis
  exfalso
  -- the edge c-on-d₀ comes from some pile's initStep
  obtain ⟨a, -, hbq, -⟩ := initialBoard_topOf d _ c htop
  -- d₀ being visible means some edge seats d₀: d₀ is some pile's top
  have hsome : ∃ β, (initialBoard d).bottomOf d₀ = some β := by
    have h1 : ((initialBoard d).bottomOf d₀).isSome = true := hvis
    cases hh : (initialBoard d).bottomOf d₀ with
    | none => rw [hh] at h1; simp at h1
    | some β => exact ⟨β, rfl⟩
  obtain ⟨β, hβ⟩ := hsome
  have htopβ : (initialBoard d).topOf β = some d₀ := (Board.bottomOf_eq _ _ _).mp hβ
  obtain ⟨a', -, hbq', hgt'⟩ := initialBoard_topOf d β d₀ htopβ
  -- d₀ = the under-card of pile a (initBase), and the top of pile a'
  cases hti : a.toIdx with
  | zero =>
      simp only [initBase, hti] at hbq
      exact absurd hbq (by simp)
  | succ k =>
      have hget : (d.piles a)[k]? = some d₀ := by
        simp only [initBase, hti] at hbq
        cases hh : (d.piles a)[k]? with
        | none => rw [hh] at hbq; exact absurd hbq (by simp)
        | some u =>
            rw [hh] at hbq
            exact congrArg some (Sum.inr.inj hbq).symm
      by_cases haa : a = a'
      · -- same pile: the under-card and the top are dealt-distinct
        subst haa
        have hlt : (d.piles a).length = k + 2 := by rw [hlen, hti]
        have hidx := getLast?_index (d.piles a) d₀ hgt'
        rw [hlen, hti, Nat.add_sub_cancel] at hidx
        exact absurd (Deal.pile_noDup ⟨hlen, hstock, hnd⟩ a k (k + 1)
          (by rw [hlt]; omega) (by rw [hlt]; omega) (by rw [hget, hidx])) (by omega)
      · -- different piles: the same dealt card can't be in both
        have hm1 : d₀ ∈ d.piles a := List.mem_iff_getElem?.mpr ⟨k, hget⟩
        have hm2 : d₀ ∈ d.piles a' := mem_of_getLast hgt'
        exact haa (Deal.piles_disj ⟨hlen, hstock, hnd⟩ hm1 hm2)

/-- The packaging: both invariants ride any play. -/
theorem run_visClean : ∀ (play : List Move) (st st' : State),
    st.WF → st.visClean → st.run play = some st' → st'.WF ∧ st'.visClean := by
  intro play
  induction play with
  | nil =>
      intro st st' hwf hv h
      have he : st = st' := Option.some.inj h
      subst he
      exact ⟨hwf, hv⟩
  | cons m ms ih =>
      intro st st' hwf hv h
      simp only [State.run] at h
      cases hm : st.apply m with
      | none => rw [hm] at h; exact absurd h (by simp)
      | some s₀ =>
          rw [hm] at h
          exact ih s₀ st' (apply_wf hwf m s₀ hm) (apply_visClean hwf hv hm) h

/-- Every reachable state has clean visible stacks and is WF. -/
theorem initialReachable_visClean {st : State} (hreach : initialReachable st) :
    st.WF ∧ st.visClean := by
  obtain ⟨d, s, play, hdw, hs, hrun⟩ := hreach
  exact run_visClean play (State.initial d s) st (initial_wf hdw hs)
    (initial_visClean d s hdw) hrun

/-- **The clean-stacks theorem**: every visible stack of a reachable
state follows the chaining rule — rank descending by one,
alternating colors. -/
theorem initialReachable_cleanStacks {st : State} (hreach : initialReachable st) :
    ∀ c d, st.board.topOf (Sum.inr d) = some c → st.isVis d = true →
      c.rank.toIdx + 1 = d.rank.toIdx ∧ c.suit.color ≠ d.suit.color := by
  intro c d htop hvis
  exact (canSitOn_eq c d).mp ((initialReachable_visClean hreach).2 c d htop hvis)

/-- Kings (or the dealt head) on the anchors of a reachable state. -/
theorem initialReachable_anchorOK {st : State} (hreach : initialReachable st) :
    ∀ a c, st.board.topOf (Sum.inl a) = some c →
      c.rank = Rank.king ∨ (st.deal.piles a).head? = some c := by
  intro a c htop
  exact ((initialReachable_visClean hreach).1.board_edges (Sum.inl a) c htop).2
