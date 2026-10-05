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

Besides B2, this file carries the reachability fences: the recurrence
presentation and the combinator (`initialReachableR`), `visClean`,
`anchorOK`, `cleanStacks` — and, from wave 21 (fragment 2's needs),
the stock-side fences `stockAccounted`, `cycleSelective` and
`seatedOrigins`, proven through the same combinator (see the section
below).

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
factors through the head-oracle induction
`solvableEngine_of_reachable_play` (wave 21: a plain induction on the
winning play's length — every engine move recurses, every pile-to-pile
head goes straight to the oracle) plus the single named residue
`replay_head_residue` (the per-move α-invariance content, its case
ledger recorded at its site).  The former cascadeMeasure plan is
retired: no measure on mid-game states is needed, because the
pile-to-pile head does not recurse at all.

The residue's cases (the EngineWitness shapes are the fence posts):
1. **returnable base** (`canReturnBase`): the `stackPile`/`pileStack`
   detour — proven kits: `stackPile_pileStack_cancel`,
   `pileStack_comm_*` squares, `solvable_of_stackPile`.
2. **locked boundary carry** (the EngineWitness shape): the run sits
   on the hidden boundary — the worry-back ban routes through B4's
   `solvable_of_pileStack'` (Theorems; the `rungNormal_or_forcedPark`
   residue rides there) plus the rank-mate twin argument above.
3. **the deadlock escape hatch**: EMPTY — see the refute-first gate
   below.

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

/-! ## The recurrence presentation (the induction infrastructure)

`initialReachable` is a *deposit* — a play from a dealt initial
state — which is what a witness hands over, but not what a proof
consumes.  Every fence over the reachable fragment (`cleanStacks`,
`anchorOK`, the probe's pile-card conservation, the planned B2
induction) has the same shape: an invariant holds at the dealt
initial states and survives one legal move.  The inductive below is
that shape, and the iff hands any deposit to any such induction —
the generic combinator every future gate-proof cites. -/

/-- Reachability by recurrence: the dealt initial states, closed
under one legal move.  No moves ever rewrite `deal` or `drawStep`, so
the closure never leaves the dealt game it started in. -/
inductive initialReachableR : State → Prop
  /-- A dealt game's start. -/
  | initial (d : Deal) (s : Nat) (hd : d.WF) (hs : 0 < s) :
      initialReachableR (State.initial d s)
  /-- One legal move preserves reachability. -/
  | step (st : State) (m : Move) (st' : State)
      (h : st.apply m = some st') (hprev : initialReachableR st) :
      initialReachableR st'

/-- The recurrence presents every deposit: replay the play backward,
step by step, from its end. -/
theorem initialReachableR_of_run : ∀ (play : List Move) (st₀ st : State),
    st₀.run play = some st → initialReachableR st₀ → initialReachableR st := by
  intro play
  induction play with
  | nil =>
      intro st₀ st h hprev
      simp only [State.run] at h
      have he : st₀ = st := Option.some.inj h
      subst he
      exact hprev
  | cons m ms ih =>
      intro st₀ st h hprev
      simp only [State.run] at h
      cases hm : st₀.apply m with
      | none => rw [hm] at h; exact absurd h (by simp)
      | some s₁ =>
          rw [hm] at h
          exact ih s₁ st h (initialReachableR.step st₀ m s₁ hm hprev)

/-- The recurrence has every deposit: exhibit the play, one
constructor per move, by induction on the derivation. -/
theorem initialReachable_of_initialReachableR {st : State}
    (h : initialReachableR st) : initialReachable st := by
  induction h with
  | initial d s hdw hs =>
      exact ⟨d, s, [], hdw, hs, rfl⟩
  | step s₀ m s₁ hap hprev ih =>
      obtain ⟨d, s, play, hdw, hs, hrun⟩ := ih
      refine ⟨d, s, play ++ [m], hdw, hs, ?_⟩
      rw [run_append, hrun]
      show s₀.run [m] = some s₁
      rw [run_singleton]
      exact hap

/-- **The iff** — the recurrence presentation and the deposit
presentation carry the same states. -/
theorem initialReachableR_iff {st : State} :
    initialReachableR st ↔ initialReachable st :=
  ⟨initialReachable_of_initialReachableR,
   fun ⟨d, s, play, hdw, hs, hrun⟩ =>
     initialReachableR_of_run play (State.initial d s) st hrun
       (initialReachableR.initial d s hdw hs)⟩

/-- **The generic combinator** (the recurrence's `rec`, packaged):
to prove `I` of every dealt-reachable state, show `I` at every dealt
initial state and that one legal move preserves it.  This is the
invariant-preservation form every future gate-proof over the
reachable fragment takes. -/
theorem invariant_of_initialReachableR {I : State → Prop}
    (hinit : ∀ (d : Deal) (s : Nat), d.WF → 0 < s → I (State.initial d s))
    (hstep : ∀ (st st' : State) (m : Move), st.apply m = some st' →
      I st → I st') :
    ∀ st, initialReachableR st → I st := by
  intro st h
  induction h with
  | initial d s hdw hs => exact hinit d s hdw hs
  | step st m st' hap hprev ih => exact hstep st st' m hap ih

/-- The combinator, deposit form: the reachability side of the iff
absorbed, so the gate-proof reads directly off `initialReachable`. -/
theorem invariant_of_initialReachable {I : State → Prop}
    (hinit : ∀ (d : Deal) (s : Nat), d.WF → 0 < s → I (State.initial d s))
    (hstep : ∀ (st st' : State) (m : Move), st.apply m = some st' →
      I st → I st') :
    ∀ st, initialReachable st → I st := fun st hr =>
  invariant_of_initialReachableR hinit hstep st (initialReachableR_iff.mpr hr)

/-! ### The B2 induction skeleton and the replay residue

**B2, the engine's license**: on states reached from a deal, the full
physical game and the engine's restricted move set have the same
solvability.  The `→` direction is `solvable_of_engine` (proven);
`←` factors through the head-oracle induction below plus the single
named residue `replay_head_residue` (the unpacked per-move content —
the wave-21 refinement of the two former pinned `[H]`s into one).
The witness fence held: `EngineWitness.wstate_not_reachable` (the
wave-19B refute-first probe) keeps the statement's reachable fragment
clear of the deadlock corner; the residue's case ledger is recorded at
its site. -/

/-- **The head-oracle induction** (the former cascadeMeasure plan,
wave-21 form): if every winning play whose FIRST move is a
pile-to-pile replays engine-only at its head, then every
dealt-reachable winning state is engine-solvable.  The induction is
on the winning play's length — every engine move recurses
(reachability and WF ride along: `initialReachableR.step`, `apply_wf`),
and every pile-to-pile head goes straight to the oracle (no recursion
at all — that is why a plain length induction suffices and no measure
on the mid-game states is needed). -/
theorem solvableEngine_of_reachable_play {st : State}
    (hreach : initialReachable st) (hwf : st.WF)
    (H : ∀ (s' : State) (c : Card) (b : Base) (rest : List Move),
      initialReachable s' → s'.WF → s'.legal (Move.pilePile c b) = true →
      ∀ w, s'.run (Move.pilePile c b :: rest) = some w → w.isWin = true →
      s'.solvableEngine)
    (hsol : st.solvableFrom) : st.solvableEngine := by
  obtain ⟨play, w, hrun, hwin⟩ := hsol
  have main : ∀ (n : Nat) (s : State) (π : List Move),
      initialReachable s → s.WF → π.length ≤ n →
      ∀ w', s.run π = some w' → w'.isWin = true → s.solvableEngine := by
    intro n
    induction n with
    | zero =>
        intro s π hreach' hwf' hlen w' hrun' hwin'
        have hnil : π = [] := by
          cases π with
          | nil => rfl
          | cons m ms => simp at hlen
        rw [hnil] at hrun'
        simp only [State.run] at hrun'
        have heq : s = w' := Option.some.inj hrun'
        subst heq
        have hnone : ∀ m : Move, m ∈ ([] : List Move) → m.isEngine = true := by
          intro m hm
          simp at hm
        exact ⟨[], hnone, s, rfl, hwin'⟩
    | succ n ih =>
        intro s π hreach' hwf' hlen w' hrun' hwin'
        cases hπ : π with
        | nil =>
            rw [hπ] at hrun'
            simp only [State.run] at hrun'
            have heq : s = w' := Option.some.inj hrun'
            subst heq
            have hnone : ∀ m : Move, m ∈ ([] : List Move) → m.isEngine = true := by
              intro m hm
              simp at hm
            exact ⟨[], hnone, s, rfl, hwin'⟩
        | cons m ms =>
            rw [hπ] at hrun' hlen
            obtain ⟨s₂, hap, hrest, -⟩ := run_cons_inv hrun'
            have hmslen : ms.length ≤ n := by simp at hlen; omega
            have hlegal : s.legal m = true := by
              simp only [State.legal, Option.isSome_iff_exists]
              exact ⟨s₂, hap⟩
            by_cases heng : m.isEngine = true
            · obtain ⟨τ, hallτ, w'', hrunτ, hwin''⟩ :=
                ih s₂ ms
                  (initialReachableR_iff.mp
                    (initialReachableR.step s m s₂ hap (initialReachableR_iff.mpr hreach')))
                  (apply_wf hwf' m s₂ hap)
                  hmslen w' hrest hwin'
              refine ⟨m :: τ, ?_, w'', ?_, hwin''⟩
              · intro x hx
                rcases List.mem_cons.mp hx with rfl | hx'
                · exact heng
                · exact hallτ x hx'
              · show s.run (m :: τ) = some w''
                simp only [State.run, hap]
                exact hrunτ
            · cases m with
              | draw => rw [Move.isEngine] at heng; simp at heng
              | reveal a => rw [Move.isEngine] at heng; simp at heng
              | deckPile c b => rw [Move.isEngine] at heng; simp at heng
              | deckStack c => rw [Move.isEngine] at heng; simp at heng
              | pileStack c => rw [Move.isEngine] at heng; simp at heng
              | stackPile c b => rw [Move.isEngine] at heng; simp at heng
              | pilePile c b => exact H s c b ms hreach' hwf' hlegal w' hrun' hwin'
  exact main play.length st play hreach hwf (Nat.le_refl _) w hrun hwin

/-- **The replay residue** (the single remaining `[H]` of the
Restriction program; the wave-21 refinement of the two former pinned
rows): at a dealt-reachable state, a legal pile-to-pile that heads a
winning play can be replayed engine-only.  This is precisely the
α-invariance content of the no-pile-to-pile restriction
(docs/no_pile_to_pile.md §4) localized to one head move — the
case-split ledger:

* **case 1 (returnable base / free routing)**: the run's root rides a
  seat whose worry-back channel is available — assemble from
  `stackPile_pileStack_cancel` (Dominance, the excursion pair nets to
  identity), the `pileStack_comm_*` squares (Theorems) and the
  foundation roundtrips (`solvable_of_pileStack_return`,
  `stackPile_pileStack_return`), routing the root through its
  foundation rung.
* **case 2 (locked boundary carry — the EngineWitness shape)**: the
  root sits on the hidden boundary; the worry-back ban routes through
  B4's crux `solvable_of_pileStack'` (Theorems; its unlocked-sitter
  gate is the `hnotlock` hedge, the `rungNormal_or_forcedPark` residue
  rides there), plus `solvable_flipAll` for the twin placement under
  the both-heights-equal license (as `twinPair_placement_equi`).
* **case 3 (the deadlock escape hatch)**: the probe is closed —
  `EngineWitness.wstate_not_reachable` (the wave-19B refute-first
  probe; all five refutation corners are off the dealt-reachable
  fragment).

The residue is genuinely open: the model's reveal is bare-trigger, so
the paper's run-carrying reveal is NOT available wholesale; what must
close instead is the arrangement-tail rewrite (the concretization /
reshape lemma, docs/no_pile_to_pile.md §5 [ ]) for the tail after the
head's park — the honest state of the art, now in one place. -/
private theorem replay_head_residue {st : State}
    (hreach : initialReachable st) (hwf : st.WF)
    {c : Card} {b : Base} {rest : List Move} {w : State}
    (hlegal : st.legal (Move.pilePile c b) = true)
    (hrun : st.run (Move.pilePile c b :: rest) = some w)
    (hwin : w.isWin = true) :
    st.solvableEngine := sorry

/-- **B2, the engine's license** — the pinned statement, proven modulo
the named residue above: on states reached from a deal, the full
physical game and the engine's restricted move set have the same
solvability. -/
theorem solvableEngine_iff_solvable_of_reachable {st : State}
    (hreach : initialReachable st) (hwf : st.WF) :
    st.solvableFrom ↔ st.solvableEngine := by
  constructor
  · intro hsol
    exact solvableEngine_of_reachable_play hreach hwf
      (fun s' c b rest hreach' hwf' hlegal w' hrun' hwin' =>
        replay_head_residue hreach' hwf' hlegal hrun' hwin')
      hsol
  · intro heng
    exact solvable_of_engine heng

/-- **The replay step**: from a dealt-reachable state, any winning
witness with a legal pile-to-pile is engine-solvable — every
pile-to-pile is implicit.  A corollary of the license above; the
legality hypothesis is not needed for this shape (the license covers
the whole state) and is kept for the statement's published form. -/
theorem engine_replay_of_pilePile {st : State}
    (hreach : initialReachable st) (hwf : st.WF) {c : Card} {b : Base}
    (_hlegal : st.legal (Move.pilePile c b) = true)
    (hsol : st.solvableFrom) : st.solvableEngine :=
  (solvableEngine_iff_solvable_of_reachable hreach hwf).mp hsol

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

/-- Every reachable state has clean visible stacks and is WF.

REFIT onto the combinator (2026-10-05, the wave-20 pattern proof):
the fence is exactly invariant-preservation — `I := fun st =>
st.WF ∧ st.visClean` seeds at the dealt initial states
(`initial_wf` + `initial_visClean`) and each step preserves it
(`apply_wf` + `apply_visClean`).  The combinator replays this for
every future gate; the old deposit-unpacking proof is retired. -/
theorem initialReachable_visClean {st : State} (hreach : initialReachable st) :
    st.WF ∧ st.visClean :=
  invariant_of_initialReachable
    (I := fun st => st.WF ∧ st.visClean)
    (fun d s hdw hs => ⟨initial_wf hdw hs, initial_visClean d s hdw⟩)
    (fun _ st' m hap hI => ⟨apply_wf hI.1 m st' hap, apply_visClean hI.1 hI.2 hap⟩)
    st hreach

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

/-! ## The stock-side fences (wave-21, fragment 2's distillate needs)

The fragment-2 sufficiency construction (Construction.lean) consumes
exactly the deal's stock cards that are *not* in the target's cycle.
Its distillate therefore needs three reachability fences beyond
`visClean`/`anchorOK` — each an invariant seeded at the dealt initial
state and preserved by one legal move, so each is proven through the
generic combinator (Task A's `invariant_of_initialReachable`):

* `stockAccounted` — stock-card conservation: every dealt stock card
  is in the cycle, visible on the tableau, or on a foundation.  The
  cycle only ever loses cards (spliced out by `deckPile` onto the
  board, by `deckStack` onto the foundation); a seated card never
  vanishes (boards only rewire), a founded card never vanishes
  (heights move by one rank at a time, the vacancy card being unique).
* `cycleSelective` — the end-state deck order: the cycle's card list
  is the deal's stock with the consumed cards spliced out, so it is
  precisely the *selection in deal order* of its own members —
  `st.stock.cards = st.deal.stock.filter (fun x => decide (x ∈
  st.stock.cards))`.  This is the list-level content behind the
  construction's final filter match; splices never reorder.
* `seatedOrigins` — every visible or founded card is one of the
  deal's cards, with the pile/stock origin tracking each new seat:
  `reveal` seats a pile card, `deckPile` seats a stock card,
  `stackPile` re-seats a founded card, `pileStack` founds a seated
  one — so the origin survives the whole move set.
-/

/-- **Stock-card conservation**: every dealt stock card is in the
cycle, visible on the tableau, or on a foundation — never destroyed,
never duplicated into the piles. -/
def State.stockAccounted (st : State) : Prop :=
  ∀ c ∈ st.deal.stock, c ∈ st.stock.cards ∨ st.isVis c = true ∨ st.onFound c = true

theorem stockAccounted_initial (d : Deal) (s : Nat) :
    (State.initial d s).stockAccounted := by
  intro c hc
  exact Or.inl hc

/-- The waste top's index facts: the cursor and the card under it. -/
theorem prev_cursor {cy : Cycle Card} {c : Card} (h : cy.prev = some c) :
    cy.cursor ≠ 0 ∧ cy.cards[cy.cursor - 1]? = some c := by
  simp only [Cycle.prev] at h
  split at h
  · exact absurd h (by simp)
  · exact ⟨by omega, h⟩

theorem stockAccounted_apply {st st' : State}
    (h : st.stockAccounted) {m : Move} (happ : st.apply m = some st') :
    st'.stockAccounted := by
  intro x hx
  cases m with
  | draw =>
      rw [apply_draw_iff] at happ
      obtain ⟨rfl⟩ := happ
      rcases h x hx with hc | hv | hf
      · exact Or.inl (by rw [Cycle.dealOnce_cards]; exact hc)
      · exact Or.inr (Or.inl hv)
      · exact Or.inr (Or.inr hf)
  | reveal a =>
      rw [apply_reveal_iff] at happ
      obtain ⟨r, bd, htop, -, hatt, rfl⟩ := happ
      rcases h x hx with hc | hv | hf
      · exact Or.inl hc
      · refine Or.inr (Or.inl ?_)
        show (bd.bottomOf x).isSome = true
        by_cases hxr : x = r
        · rw [hxr, (Board.bottomOf_eq bd r (st.hiddenBase a)).mpr (Board.attach_topOf _ _ _ hatt)]
          rfl
        · exact bottomOf_isSome_attach hatt hv
      · exact Or.inr (Or.inr hf)
  | deckPile c b =>
      rw [apply_deckPile_iff] at happ
      obtain ⟨hp, -, bd, hatt, rfl⟩ := happ
      have hcur := prev_cursor hp
      by_cases hmem' : x ∈ Cycle.removeIdx st.stock.cards (st.stock.cursor - 1)
      · exact Or.inl hmem'
      · by_cases hcyc : x ∈ st.stock.cards
        · by_cases hxc'' : x = c
          · have hxc : x = c := hxc''
            refine Or.inr (Or.inl ?_)
            rw [hxc]
            show (bd.bottomOf c).isSome = true
            rw [(Board.bottomOf_eq bd c b).mpr (Board.attach_topOf _ _ _ hatt)]
            rfl
          · exact absurd (Cycle.mem_removeIdx_of_ne _ _ x c hcur.2 hxc'' hcyc) hmem'
        · rcases h x hx with hc | hv | hf
          · exact absurd hc hcyc
          · refine Or.inr (Or.inl ?_)
            exact bottomOf_isSome_attach hatt hv
          · exact Or.inr (Or.inr hf)
  | deckStack c =>
      rw [apply_deckStack_iff] at happ
      obtain ⟨hp, hrk, rfl⟩ := happ
      have hcur := prev_cursor hp
      by_cases hmem' : x ∈ Cycle.removeIdx st.stock.cards (st.stock.cursor - 1)
      · exact Or.inl hmem'
      · by_cases hcyc : x ∈ st.stock.cards
        · by_cases hxc'' : x = c
          · refine Or.inr (Or.inr ?_)
            rw [hxc'']
            show decide (c.rank.toIdx <
              (if c.suit = c.suit then st.heights c.suit + 1 else st.heights c.suit)) = true
            rw [ite_eq_left rfl]
            exact decide_eq_true (by omega)
          · exact absurd (Cycle.mem_removeIdx_of_ne _ _ x c hcur.2 hxc'' hcyc) hmem'
        · rcases h x hx with hc | hv | hf
          · exact absurd hc hcyc
          · exact Or.inr (Or.inl hv)
          · refine Or.inr (Or.inr ?_)
            show decide (x.rank.toIdx <
              (if x.suit = c.suit then st.heights x.suit + 1 else st.heights x.suit)) = true
            have hlt : x.rank.toIdx < st.heights x.suit := by
              have hf' : decide (x.rank.toIdx < st.heights x.suit) = true := hf
              exact of_decide_eq_true hf'
            by_cases hsc : x.suit = c.suit
            · rw [ite_eq_left hsc]
              exact decide_eq_true (by omega)
            · rw [ite_eq_right hsc]
              exact decide_eq_true (by omega)
  | pileStack c =>
      rw [apply_pileStack_iff] at happ
      obtain ⟨-, b, hb, hrk, rfl⟩ := happ
      have hbot : st.board.topOf b = some c := (Board.bottomOf_eq st.board c b).mp hb
      rcases h x hx with hc | hv | hf
      · exact Or.inl hc
      · by_cases hxc : x = c
        · refine Or.inr (Or.inr ?_)
          rw [hxc]
          show decide (c.rank.toIdx <
            (if c.suit = c.suit then st.heights c.suit + 1 else st.heights c.suit)) = true
          rw [ite_eq_left rfl]
          exact decide_eq_true (by omega)
        · refine Or.inr (Or.inl ?_)
          show ((st.board.detach b).bottomOf x).isSome = true
          rw [bottomOf_detach_ne hbot hxc]
          exact hv
      · refine Or.inr (Or.inr ?_)
        show decide (x.rank.toIdx <
          (if x.suit = c.suit then st.heights x.suit + 1 else st.heights x.suit)) = true
        have hlt : x.rank.toIdx < st.heights x.suit := by
          have hf' : decide (x.rank.toIdx < st.heights x.suit) = true := hf
          exact of_decide_eq_true hf'
        by_cases hsc : x.suit = c.suit
        · rw [ite_eq_left hsc]
          exact decide_eq_true (by omega)
        · rw [ite_eq_right hsc]
          exact decide_eq_true (by omega)
  | stackPile c b =>
      rw [apply_stackPile_iff] at happ
      obtain ⟨hrk, -, bd, hatt, rfl⟩ := happ
      rcases h x hx with hc | hv | hf
      · exact Or.inl hc
      · refine Or.inr (Or.inl ?_)
        exact bottomOf_isSome_attach hatt hv
      · by_cases hxc : x = c
        · refine Or.inr (Or.inl ?_)
          rw [hxc]
          show (bd.bottomOf c).isSome = true
          rw [(Board.bottomOf_eq bd c b).mpr (Board.attach_topOf _ _ _ hatt)]
          rfl
        · refine Or.inr (Or.inr ?_)
          show decide (x.rank.toIdx <
            (if x.suit = c.suit then st.heights x.suit - 1 else st.heights x.suit)) = true
          have hlt : x.rank.toIdx < st.heights x.suit := by
            have hf' : decide (x.rank.toIdx < st.heights x.suit) = true := hf
            exact of_decide_eq_true hf'
          by_cases hsc : x.suit = c.suit
          · rw [ite_eq_left hsc]
            have hhh : st.heights x.suit = st.heights c.suit := by rw [hsc]
            have hne : x.rank.toIdx ≠ c.rank.toIdx := by
              intro hcon
              exact hxc (by
                cases x with
                | mk sx rx =>
                    cases c with
                    | mk sc rc =>
                        rw [Card.mk.injEq]
                        exact ⟨hsc, Rank.toIdx_inj hcon⟩)
            exact decide_eq_true (by omega)
          · rw [ite_eq_right hsc]
            exact decide_eq_true (by omega)
  | pilePile c b =>
      rw [apply_pilePile_iff] at happ
      obtain ⟨b₀, hb, hbne, hcmr, bd, hatt, rfl⟩ := happ
      have hbot₀ : st.board.topOf b₀ = some c := (Board.bottomOf_eq st.board c b₀).mp hb
      have hfree : st.board.topOf b = none := topOf_of_canPlace (canPlace_of_canMoveRun hcmr)
      rcases h x hx with hcyc | hv | hf
      · exact Or.inl hcyc
      · refine Or.inr (Or.inl ?_)
        show (bd.bottomOf x).isSome = true
        cases hbx : st.board.bottomOf x with
        | none =>
            exfalso
            have hv' : (st.board.bottomOf x).isSome = true := hv
            rw [hbx] at hv'
            simp at hv'
        | some b' =>
            have hb'top : st.board.topOf b' = some x :=
              (Board.bottomOf_eq st.board x b').mp hbx
            by_cases hbb' : b' = b₀
            · have hxc : x = c := by
                rw [hbb'] at hb'top
                exact Option.some.inj (hb'top.symm.trans hbot₀)
              rw [hxc]
              rw [(Board.bottomOf_eq bd c b).mpr (Board.attach_topOf _ _ _ hatt)]
              rfl
            · have hb'b : b' ≠ b := by
                intro hcon
                rw [hcon] at hb'top
                rw [hb'top] at hfree
                exact absurd hfree (by simp)
              have hdiag : bd.topOf b' = some x := by
                rw [Board.attach_topOf_ne _ _ _ hatt hb'b,
                  Board.detach_topOf_ne st.board b₀ b' hbb']
                exact hb'top
              rw [(Board.bottomOf_eq bd x b').mpr hdiag]
              rfl
      · exact Or.inr (Or.inr hf)

/-- Every dealt-reachable state conserves its deal's stock cards. -/
theorem stockAccounted_of_initialReachable {st : State}
    (hr : initialReachable st) : st.stockAccounted :=
  invariant_of_initialReachable
    (I := fun st => st.stockAccounted)
    (fun d s _ _ => stockAccounted_initial d s)
    (fun _ _ _ hap h => stockAccounted_apply h hap)
    st hr

/-! ### The end-state deck order -/

/-- **The end-state deck order** (the construction's final deck match,
necessity side): the cycle's card list is its own membership
*selection in deal order* — splices never reorder, so the cycle is
the deal's stock with the consumed cards filtered out. -/
def State.cycleSelective (st : State) : Prop :=
  st.stock.cards = st.deal.stock.filter fun x => decide (x ∈ st.stock.cards)

theorem cycleSelective_initial (d : Deal) (s : Nat) (hd : d.WF) :
    (State.initial d s).cycleSelective := by
  show d.stock = d.stock.filter fun x => decide (x ∈ d.stock)
  exact filter_mem_idem d.stock (noDupCards_append_right hd.2.2)

/-- The splice-selection step: at a selective cycle, splicing out any
position keeps the cycle selective (a splice is a membership filter,
and membership filters compose). -/
theorem splice_selective {full L : List Card} {i : Nat}
    (hnd : noDupCards L) (h : L = full.filter fun x => decide (x ∈ L)) :
    Cycle.removeIdx L i
      = full.filter fun x => decide (x ∈ Cycle.removeIdx L i) := by
  obtain ⟨R, hR⟩ : ∃ R, R = Cycle.removeIdx L i := ⟨_, rfl⟩
  rw [← hR]
  have e1 : R = L.filter fun x => decide (x ∈ R) := by
    rw [hR]
    exact removeIdx_filter_mem _ _ hnd
  have e2 : L.filter (fun x => decide (x ∈ R))
      = full.filter (fun x => decide (x ∈ R)) := by
    rw [h, List.filter_filter]
    refine List.filter_congr fun x hx => ?_
    by_cases hxR : x ∈ R
    · have hxL : x ∈ L := by
        rw [hR] at hxR
        exact Cycle.mem_removeIdx _ _ hxR
      simp [hxL, hxR]
    · simp [hxR]
  exact e1.trans e2

theorem cycleSelective_apply {st st' : State} (hwf : st.WF)
    (h : st.cycleSelective) {m : Move} (happ : st.apply m = some st') :
    st'.cycleSelective := by
  cases m with
  | draw =>
      rw [apply_draw_iff] at happ
      obtain ⟨rfl⟩ := happ
      show (Cycle.dealOnce st.drawStep st.stock).cards
          = st.deal.stock.filter
              fun x => decide (x ∈ (Cycle.dealOnce st.drawStep st.stock).cards)
      rw [Cycle.dealOnce_cards]
      exact h
  | reveal a =>
      rw [apply_reveal_iff] at happ
      obtain ⟨-, -, -, -, -, rfl⟩ := happ
      exact h
  | deckPile c b =>
      rw [apply_deckPile_iff] at happ
      obtain ⟨-, -, -, -, rfl⟩ := happ
      exact splice_selective hwf.stock_wf.1 h
  | deckStack c =>
      rw [apply_deckStack_iff] at happ
      obtain ⟨-, -, rfl⟩ := happ
      exact splice_selective hwf.stock_wf.1 h
  | pileStack c =>
      rw [apply_pileStack_iff] at happ
      obtain ⟨-, -, -, -, rfl⟩ := happ
      exact h
  | stackPile c b =>
      rw [apply_stackPile_iff] at happ
      obtain ⟨-, -, -, -, rfl⟩ := happ
      exact h
  | pilePile c b =>
      rw [apply_pilePile_iff] at happ
      obtain ⟨-, -, -, -, -, _, rfl⟩ := happ
      exact h

/-- Every dealt-reachable state's cycle is the in-order selection of
its own members from the deal's stock. -/
theorem cycleSelective_of_initialReachable {st : State}
    (hr : initialReachable st) : st.cycleSelective :=
  (invariant_of_initialReachable
    (I := fun st => st.WF ∧ st.cycleSelective)
    (fun d s hdw hs => ⟨initial_wf hdw hs, cycleSelective_initial d s hdw⟩)
    (fun _ _ m hap h => ⟨apply_wf h.1 m _ hap, cycleSelective_apply h.1 h.2 hap⟩)
    st hr).2

/-! ### The seated origins -/

/-- **Seated origins**: every visible or founded card is one of the
deal's cards — a pile card or a stock card.  The origin is created by
the deal and never invented by a move: `reveal` seats a pile card,
`deckPile` seats a stock card, `deckStack`/`pileStack` found stock/
seated cards, `stackPile` re-seats a founded card. -/
def State.seatedOrigins (st : State) : Prop :=
  ∀ c, st.isVis c = true ∨ st.onFound c = true →
    (∃ a, c ∈ st.deal.piles a) ∨ c ∈ st.deal.stock

theorem seatedOrigins_initial (d : Deal) (s : Nat) :
    (State.initial d s).seatedOrigins := by
  intro c hc
  rcases hc with hv | hf
  · refine Or.inl ?_
    have hex : ∃ b, (State.initial d s).board.topOf b = some c := by
      simp only [State.isVis] at hv
      cases hbot : ((State.initial d s).board.bottomOf c) with
      | none => rw [hbot] at hv; simp at hv
      | some b => exact ⟨b, (Board.bottomOf_eq _ _ _).mp hbot⟩
    obtain ⟨b, hb⟩ := hex
    obtain ⟨a, -, -, hgt⟩ := initialBoard_topOf d b c hb
    exact ⟨a, mem_of_getLast hgt⟩
  · exfalso
    have h0 : (State.initial d s).heights c.suit = 0 := rfl
    have hlt : c.rank.toIdx < (State.initial d s).heights c.suit := of_decide_eq_true hf
    rw [h0] at hlt
    omega

theorem seatedOrigins_apply {st st' : State} (hwf : st.WF)
    (h : st.seatedOrigins) {m : Move} (happ : st.apply m = some st') :
    st'.seatedOrigins := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, ⟨-, hmem⟩⟩ := id hwf
  intro x hx
  cases m with
  | draw =>
      rw [apply_draw_iff] at happ
      obtain ⟨rfl⟩ := happ
      exact h x hx
  | reveal a =>
      rw [apply_reveal_iff] at happ
      obtain ⟨r, bd, htop, -, hatt, rfl⟩ := happ
      rcases hx with hv | hf
      · by_cases hxr : x = r
        · have hmemr : r ∈ st.hidden a := mem_of_getLast htop
          rw [hxr]
          exact Or.inl ⟨a, List.take_subset _ _ hmemr⟩
        · refine h x (Or.inl ?_)
          exact bottomOf_isSome_attach_of_ne hatt hxr hv
      · exact h x (Or.inr hf)
  | deckPile c b =>
      rw [apply_deckPile_iff] at happ
      obtain ⟨hp, -, bd, hatt, rfl⟩ := happ
      have hcur := prev_cursor hp
      rcases hx with hv | hf
      · by_cases hxc : x = c
        · refine Or.inr ?_
          rw [hxc]
          exact hmem c (List.mem_iff_getElem?.mpr ⟨st.stock.cursor - 1, hcur.2⟩)
        · refine h x (Or.inl ?_)
          exact bottomOf_isSome_attach_of_ne hatt hxc hv
      · exact h x (Or.inr hf)
  | deckStack c =>
      rw [apply_deckStack_iff] at happ
      obtain ⟨hp, hrk, rfl⟩ := happ
      rcases hx with hv | hf
      · exact h x (Or.inl hv)
      · by_cases hsc : x.suit = c.suit
        · have hlt : x.rank.toIdx <
              (if x.suit = c.suit then st.heights x.suit + 1 else st.heights x.suit) :=
              of_decide_eq_true hf
          rw [ite_eq_left hsc] at hlt
          rcases Nat.lt_or_ge x.rank.toIdx (st.heights x.suit) with hlt' | hge
          · exact h x (Or.inr (by
              show decide (x.rank.toIdx < st.heights x.suit) = true
              exact decide_eq_true hlt'))
          · have hhh : st.heights x.suit = st.heights c.suit := by rw [hsc]
            have hxc' : x = c := by
              cases x with
              | mk sx rx =>
                  cases c with
                  | mk sc rc =>
                      have hsu : sx = sc := hsc
                      have hhs : st.heights sx = st.heights sc := by rw [hsu]
                      have hlt' : rx.toIdx < st.heights sx + 1 := hlt
                      have hge' : st.heights sx ≤ rx.toIdx := by omega
                      have hrk' : rc.toIdx = st.heights sc := by omega
                      rw [Card.mk.injEq]
                      refine ⟨hsu, Rank.toIdx_inj (by omega)⟩
            rw [hxc']
            exact Or.inr (hmem c
              (List.mem_iff_getElem?.mpr ⟨st.stock.cursor - 1, (prev_cursor hp).2⟩))
        · have hlt : x.rank.toIdx <
            (if x.suit = c.suit then st.heights x.suit + 1 else st.heights x.suit) :=
            of_decide_eq_true hf
          rw [ite_eq_right hsc] at hlt
          exact h x (Or.inr (by
            show decide (x.rank.toIdx < st.heights x.suit) = true
            exact decide_eq_true hlt))
  | pileStack c =>
      rw [apply_pileStack_iff] at happ
      obtain ⟨-, b, hb, hrk, rfl⟩ := happ
      have hbot : st.board.topOf b = some c := (Board.bottomOf_eq st.board c b).mp hb
      have hcvis : st.isVis c = true := by
        show (st.board.bottomOf c).isSome = true
        rw [hb]
        rfl
      rcases hx with hv | hf
      · by_cases hxc : x = c
        · exfalso
          have hseated : ((st.board.detach b).bottomOf x).isSome = true := hv
          rw [hxc] at hseated
          rw [Board.bottomOf_detach_self hbot] at hseated
          simp at hseated
        · refine h x (Or.inl ?_)
          show (st.board.bottomOf x).isSome = true
          have hv' : ((st.board.detach b).bottomOf x).isSome = true := hv
          rw [bottomOf_detach_ne hbot hxc] at hv'
          exact hv'
      · by_cases hxc : x = c
        · rw [hxc]
          exact h c (Or.inl hcvis)
        · refine h x (Or.inr ?_)
          show decide (x.rank.toIdx < st.heights x.suit) = true
          have hlt : x.rank.toIdx <
              (if x.suit = c.suit then st.heights x.suit + 1 else st.heights x.suit) :=
              of_decide_eq_true hf
          by_cases hsc : x.suit = c.suit
          · rw [ite_eq_left hsc] at hlt
            have hhh : st.heights x.suit = st.heights c.suit := by rw [hsc]
            have hne : x.rank.toIdx ≠ c.rank.toIdx := by
              intro hcon
              exact hxc (by
                cases x with
                | mk sx rx =>
                    cases c with
                    | mk sc rc =>
                        rw [Card.mk.injEq]
                        exact ⟨hsc, Rank.toIdx_inj hcon⟩)
            exact decide_eq_true (by omega)
          · rw [ite_eq_right hsc] at hlt
            exact decide_eq_true (by omega)
  | stackPile c b =>
      rw [apply_stackPile_iff] at happ
      obtain ⟨hrk, -, bd, hatt, rfl⟩ := happ
      rcases hx with hv | hf
      · by_cases hxc : x = c
        · refine h x (Or.inr ?_)
          rw [hxc]
          show decide (c.rank.toIdx < st.heights c.suit) = true
          exact decide_eq_true (by omega)
        · refine h x (Or.inl ?_)
          exact bottomOf_isSome_attach_of_ne hatt hxc hv
      · refine h x (Or.inr ?_)
        show decide (x.rank.toIdx < st.heights x.suit) = true
        have hlt : x.rank.toIdx <
            (if x.suit = c.suit then st.heights x.suit - 1 else st.heights x.suit) :=
            of_decide_eq_true hf
        by_cases hsc : x.suit = c.suit
        · rw [ite_eq_left hsc] at hlt
          exact decide_eq_true (by omega)
        · rw [ite_eq_right hsc] at hlt
          exact decide_eq_true (by omega)
  | pilePile c b =>
      rw [apply_pilePile_iff] at happ
      obtain ⟨b₀, hb, hbne, hcmr, bd, hatt, rfl⟩ := happ
      have hbot₀ : st.board.topOf b₀ = some c :=
        (Board.bottomOf_eq st.board c b₀).mp hb
      have hfree : st.board.topOf b = none :=
        topOf_of_canPlace (canPlace_of_canMoveRun hcmr)
      rcases hx with hv | hf
      · cases hbx : st.board.bottomOf x with
        | some b'' =>
            refine h x (Or.inl ?_)
            show (st.board.bottomOf x).isSome = true
            rw [hbx]
            rfl
        | none =>
            exfalso
            have hseated : (bd.bottomOf x).isSome = true := hv
            cases hbd : bd.bottomOf x with
            | none => rw [hbd] at hseated; simp at hseated
            | some b'' =>
                have hb''top : bd.topOf b'' = some x :=
                  (Board.bottomOf_eq bd x b'').mp hbd
                by_cases hbb : b'' = b
                · have hxc : x = c := by
                    rw [hbb] at hb''top
                    exact Option.some.inj (hb''top.symm.trans (Board.attach_topOf _ _ _ hatt))
                  subst hxc
                  rw [hb] at hbx
                  simp at hbx
                · by_cases hbb₀ : b'' = b₀
                  · rw [hbb₀] at hb''top
                    rw [Board.attach_topOf_ne _ _ _ hatt hbne,
                      Board.detach_topOf] at hb''top
                    simp at hb''top
                  · rw [Board.attach_topOf_ne _ _ _ hatt hbb,
                      Board.detach_topOf_ne st.board b₀ b'' hbb₀] at hb''top
                    have hbbx : st.board.bottomOf x = some b'' :=
                      (Board.bottomOf_eq st.board x b'').mpr hb''top
                    rw [hbbx] at hbx
                    simp at hbx
      · exact h x (Or.inr hf)

/-- Every dealt-reachable state seats only the deal's cards. -/
theorem seatedOrigins_of_initialReachable {st : State}
    (hr : initialReachable st) : st.seatedOrigins :=
  (invariant_of_initialReachable
    (I := fun st => st.WF ∧ st.seatedOrigins)
    (fun d s hdw hs => ⟨initial_wf hdw hs, seatedOrigins_initial d s⟩)
    (fun _ _ m hap h => ⟨apply_wf h.1 m _ hap, seatedOrigins_apply h.1 h.2 hap⟩)
    st hr).2

/-- The walk collects only rank-descending cards: at a board whose
every edge with a visible base is clean (`canSitOn`), each member of
a run is strictly below the root in rank.  Fuel induction carrying
the root and the current root's visibility; the accumulator
condition rides the collection. -/
theorem Board.aboveOf_go_rank_lt {bd : Board}
    (hclean : ∀ a b, bd.topOf (Sum.inr b) = some a → (bd.bottomOf b).isSome = true →
      canSitOn a b = true) :
    ∀ (n : Nat) (root c : Card) (acc : List Card),
      (bd.bottomOf c).isSome = true →
      c.rank.toIdx < root.rank.toIdx →
      (∀ y ∈ acc, y.rank.toIdx < root.rank.toIdx) →
      ∀ x, x ∈ Board.aboveOf.go bd n (Sum.inr c) acc →
        x.rank.toIdx < root.rank.toIdx := by
  intro n
  induction n with
  | zero =>
      intro root c acc _ _ hacc x hx
      exact hacc x hx
  | succ n ih =>
      intro root c acc hvis hc hacc x hx
      rw [aboveOf_go_succ] at hx
      cases hb : bd.topOf (Sum.inr c) with
      | none => rw [hb] at hx; exact hacc x hx
      | some c' =>
          simp only [hb] at hx
          have hvisc' : (bd.bottomOf c').isSome = true := by
            have hbot := (Board.bottomOf_eq bd c' (Sum.inr c)).mpr hb
            rw [hbot]; rfl
          have hcc' : canSitOn c' c = true := hclean c' c hb hvis
          have hrank : c'.rank.toIdx + 1 = c.rank.toIdx := (canSitOn_eq _ _).mp hcc' |>.1
          have hc'lt : c'.rank.toIdx < root.rank.toIdx := by omega
          have hacc' : ∀ y ∈ c' :: acc, y.rank.toIdx < root.rank.toIdx := by
            intro y hy
            rcases List.mem_cons.mp hy with rfl | hy'
            · exact hc'lt
            · exact hacc y hy'
          by_cases hcont : acc.contains c' = true
          · rw [if_pos hcont] at hx; exact hacc x hx
          · rw [if_neg hcont] at hx
            exact ih root c' (c' :: acc) hvisc' hc'lt hacc' x hx

/-- Every member of a visible card's run is strictly below it in
rank — the clean-stacks corollary for reachable states. -/
theorem rank_lt_of_mem_aboveOf {st : State} (hv : st.visClean) {c x : Card}
    (hc : st.isVis c = true) (hmem : x ∈ st.board.aboveOf c) :
    x.rank.toIdx < c.rank.toIdx := by
  have hmem' : x ∈ Board.aboveOf.go st.board 52 (Sum.inr c) [] := hmem
  rw [show (52 : Nat) = 51 + 1 from rfl] at hmem'
  rw [aboveOf_go_succ] at hmem'
  cases hb : st.board.topOf (Sum.inr c) with
  | none => rw [hb] at hmem'; simp at hmem'
  | some c₁ =>
      simp only [hb] at hmem'
      rw [if_neg (by simp)] at hmem'
      have hvisc₁ : (st.board.bottomOf c₁).isSome = true := by
        have hbot := (Board.bottomOf_eq st.board c₁ (Sum.inr c)).mpr hb
        rw [hbot]; rfl
      have hcc₁ : canSitOn c₁ c = true := hv c₁ c hb hc
      have hrank : c₁.rank.toIdx + 1 = c.rank.toIdx := (canSitOn_eq _ _).mp hcc₁ |>.1
      have hc₁lt : c₁.rank.toIdx < c.rank.toIdx := by omega
      have hacc : ∀ y ∈ [c₁], y.rank.toIdx < c.rank.toIdx := by
        intro y hy
        simp only [List.mem_singleton] at hy
        rw [hy]; exact hc₁lt
      exact Board.aboveOf_go_rank_lt hv 51 c c₁ [c₁] hvisc₁ hc₁lt hacc x hmem'

/-- **The merge is impossible at clean-stacks states** — the [H]
crux, vacuous under `visClean` (hence under `initialReachable`).  A
pilePile whose run passes a twin cannot land on either twin's cargo
stack: the run is strictly rank-descending (the clean-stacks
corollary), so the twin inside the run sits strictly below the root
in rank, while the cargo landing demands the root sit two below the
twin.  At merely-WF states the deal-adjacent branch of
`board_edges` admits dirty visible edges (the old reveal-through's
artifacts) — there the merge was live, and it is exactly what the
w15merge witness exhibited. -/
theorem merge_impossible_of_visClean {st a₁ : State} {t z z' c : Card} {b : Base}
    (hv : st.visClean)
    (h₀ : st.board.bottomOf z = some (Sum.inr t))
    (h₀' : st.board.bottomOf z' = some (Sum.inr t.flipSuit))
    (hfit : canSitOn z t = true) (hfit' : canSitOn z' t.flipSuit = true)
    (hstep : st.apply (Move.pilePile c b) = some a₁)
    (hmerge : t ∈ st.board.aboveOf c ∨ t.flipSuit ∈ st.board.aboveOf c)
    (hland : ∃ d, b = Sum.inr d ∧
      (d = z ∨ d ∈ st.board.aboveOf z ∨ d = z' ∨ d ∈ st.board.aboveOf z')) :
    False := by
  obtain ⟨d, hb, hd⟩ := hland
  rw [apply_pilePile_iff] at hstep
  obtain ⟨b₀, hb₀, -, hcmr, -, -, -⟩ := hstep
  have hvc : st.isVis c = true := by
    show (st.board.bottomOf c).isSome = true
    rw [hb₀]; rfl
  simp only [State.canMoveRun] at hcmr
  obtain ⟨hcp, -⟩ := Bool.and_eq_true_iff.mp hcmr
  simp only [State.canPlace, hb, Bool.and_eq_true_iff, decide_eq_true_iff] at hcp
  obtain ⟨-, -, hcs⟩ := hcp
  obtain ⟨hcrk, -⟩ := (canSitOn_eq c d).mp hcs
  obtain ⟨hzrk, -⟩ := (canSitOn_eq z t).mp hfit
  obtain ⟨hz'rk, -⟩ := (canSitOn_eq z' t.flipSuit).mp hfit'
  have htwin : t.flipSuit.rank.toIdx = t.rank.toIdx :=
    congrArg Rank.toIdx (Card.flipSuit_rank t)
  -- the landing card is at or below the cargo rank
  have hdle : d.rank.toIdx ≤ t.rank.toIdx - 1 := by
    rcases hd with rfl | hd | rfl | hd
    · omega
    · have hvz : st.isVis z = true := by
        show (st.board.bottomOf z).isSome = true
        rw [h₀]; rfl
      have hlt := rank_lt_of_mem_aboveOf hv hvz hd
      omega
    · omega
    · have hvz' : st.isVis z' = true := by
        show (st.board.bottomOf z').isSome = true
        rw [h₀']; rfl
      have hlt := rank_lt_of_mem_aboveOf hv hvz' hd
      omega
  rcases hmerge with hmem | hmem
  · by_cases hct : c = t
    · subst hct; omega
    · have hlt := rank_lt_of_mem_aboveOf hv hvc hmem
      omega
  · by_cases hct : c = t.flipSuit
    · subst hct; omega
    · have hlt := rank_lt_of_mem_aboveOf hv hvc hmem
      omega

/-- The reachability corollary: every reachable state is
visClean, so the merge is impossible there too. -/
theorem merge_impossible_of_initialReachable {st a₁ : State} {t z z' c : Card} {b : Base}
    (hreach : initialReachable st)
    (h₀ : st.board.bottomOf z = some (Sum.inr t))
    (h₀' : st.board.bottomOf z' = some (Sum.inr t.flipSuit))
    (hfit : canSitOn z t = true) (hfit' : canSitOn z' t.flipSuit = true)
    (hstep : st.apply (Move.pilePile c b) = some a₁)
    (hmerge : t ∈ st.board.aboveOf c ∨ t.flipSuit ∈ st.board.aboveOf c)
    (hland : ∃ d, b = Sum.inr d ∧
      (d = z ∨ d ∈ st.board.aboveOf z ∨ d = z' ∨ d ∈ st.board.aboveOf z')) :
    False :=
  merge_impossible_of_visClean (initialReachable_visClean hreach).2
    h₀ h₀' hfit hfit' hstep hmerge hland

/-- **The twin-rooted merge is impossible at clean-stacks states** —
the rooted companion of `merge_impossible_of_visClean`: a `pilePile`
whose run IS the twin itself (rooted at `c = t`), landing on the other
twin's cargo run, cannot fire.  The walk descent (the clean-stacks
corollary) pins the landing card strictly below the other cargo in
rank, while the landing fit demands it one ABOVE the twin. -/
theorem merge_rooted_impossible_of_visClean {st a₁ : State} {t z' c : Card} {b : Base}
    (hv : st.visClean)
    (h₀' : st.board.bottomOf z' = some (Sum.inr t.flipSuit))
    (hfit' : canSitOn z' t.flipSuit = true)
    (hstep : st.apply (Move.pilePile c b) = some a₁)
    (hc : c = t)
    (hland : ∃ d, b = Sum.inr d ∧ d ∈ st.board.aboveOf z') :
    False := by
  obtain ⟨d, hb, hdz'⟩ := hland
  rw [hc, apply_pilePile_iff] at hstep
  obtain ⟨-, -, -, hcmr, -, -, -⟩ := hstep
  simp only [State.canMoveRun, Bool.and_eq_true_iff] at hcmr
  obtain ⟨hcp, -⟩ := hcmr
  simp only [State.canPlace, hb, Bool.and_eq_true_iff, decide_eq_true_iff] at hcp
  obtain ⟨-, -, hcs⟩ := hcp
  obtain ⟨hrk, -⟩ := (canSitOn_eq t d).mp hcs
  obtain ⟨hrk', -⟩ := (canSitOn_eq z' t.flipSuit).mp hfit'
  have hvz' : st.isVis z' = true := by
    show (st.board.bottomOf z').isSome = true
    rw [h₀']; rfl
  have hlt := rank_lt_of_mem_aboveOf hv hvz' hdz'
  rw [Card.flipSuit_rank] at hrk'
  omega

