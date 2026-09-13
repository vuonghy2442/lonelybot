import Klondike.Move
import Klondike.Relabel
import Klondike.Commutation

/-!
# The theorem farm - formalized

The statement layer for the results beyond the kernel: the
reversibility/commitment structure (their Lemma A1), the structural
acyclicity of the matching (the forest potential), and the deck
integration.  The relabeling group lives in `Klondike.Relabel` and the
commutation schema in `Klondike.Commutation`; this module re-exports both,
so downstream importers see the union unchanged.
-/

/-! ## 2. Reversibility and commitments — their Lemma A1, model side

`pilePile` is an involution; `draw` is cyclically invertible;
`pileStack`∘`stackPile` is a *near*-inverse — the anchor case (a
fully-revealed non-king bottom card cannot return to the empty pile)
is exactly why safe-stacking (C1) is a theorem in the engine rather
than trivia, and where the reshape lemma (B4) earns its keep.
-/

/-- The return-base condition for un-stacking: a king may return to
an anchor; a card that sat on `d` may return onto `d`. -/
def canReturnBase (c : Card) (b₀ : Base) : Bool :=
  match b₀ with
  | Sum.inl _ => decide (c.rank = Rank.king)
  | Sum.inr d => canSitOn c d

/-- The round trip through the foundations is the identity: detach via
`pileStack`, come back with `stackPile` to the same base — the board
re-attaches (attach after detach at the same base restores the
matching pointwise), the heights return (+1 then -1). -/
theorem pileStack_stackPile_roundtrip {st : State} {c : Card} {b₀ : Base}
    {st₁ st₂ : State}
    (h₀ : st.board.bottomOf c = some b₀)
    (hret : canReturnBase c b₀ = true)
    (h₁ : st.apply (Move.pileStack c) = some st₁)
    (h₂ : st₁.apply (Move.stackPile c b₀) = some st₂) : st₂ = st := by
  have htop : st.board.topOf b₀ = some c := (Board.bottomOf_eq st.board c b₀).mp h₀
  simp only [State.apply, State.applyPileStack] at h₁
  cases ht : st.board.topOf (Sum.inr c) with
  | some x =>
    rw [ht] at h₁
    exact absurd h₁ (by simp)
  | none =>
    rw [ht, h₀] at h₁
    have h₁' : (if c.rank.toIdx = st.heights c.suit then
        some { st with
          board := st.board.detach b₀,
          heights := fun s => if s = c.suit then st.heights s + 1 else st.heights s }
        else none) = some st₁ := h₁
    split at h₁'
    · rw [Option.some.injEq] at h₁'
      subst h₁'
      simp only [State.apply, State.applyStackPile] at h₂
      cases hatt : (st.board.detach b₀).attach b₀ c with
      | none => rw [hatt] at h₂; exact absurd h₂ (by simp)
      | some bd =>
        rw [hatt] at h₂
        simp at h₂
        obtain ⟨-, h'⟩ := h₂
        subst h'
        have hbdeq : bd.topOf = st.board.topOf := by
          funext b'
          by_cases hbb : b' = b₀
          · subst hbb
            rw [Board.attach_topOf _ _ _ hatt]
            exact htop.symm
          · rw [Board.attach_topOf_ne _ _ _ hatt hbb, Board.detach_topOf_ne _ _ _ hbb]
        have hbd : bd = st.board := Board.ext_topOf hbdeq
        have hh : (fun s => if s = c.suit then
            (if s = c.suit then st.heights s + 1 else st.heights s) - 1
            else (if s = c.suit then st.heights s + 1 else st.heights s)) = st.heights := by
          funext s
          by_cases hsc : s = c.suit
          · subst hsc
            rw [if_pos rfl, if_pos rfl]
            omega
          · rw [if_neg hsc, if_neg hsc]
        cases st with
        | mk d b hgt dpt stck ds =>
          rw [hbd, hh]
    · exact absurd h₁' (by simp)

/-- The moved run carries back; `aboveOf` is unchanged.  The first move
detaches `b₀` and attaches `b`; the second (given legal) detaches `b`
and attaches `b₀` — the composition's `topOf` is pointwise the
original's, and pilePile writes only the board. -/
theorem pilePile_roundtrip {st : State} {c : Card} {b b₀ : Base} {st₁ st₂ : State}
    (h₀ : st.board.bottomOf c = some b₀)
    (h₁ : st.apply (Move.pilePile c b) = some st₁)
    (h₂ : st₁.apply (Move.pilePile c b₀) = some st₂) : st₂ = st := by
  have htop₀ : st.board.topOf b₀ = some c := (Board.bottomOf_eq st.board c b₀).mp h₀
  rw [apply_pilePile_iff] at h₁
  obtain ⟨b₀', hb₀', hne, _, bd, hatt, hst₁⟩ := h₁
  rw [h₀] at hb₀'
  have hb₀e : b₀' = b₀ := (Option.some.inj hb₀').symm
  rw [hb₀e] at hne hatt
  rw [hst₁] at h₂
  rw [apply_pilePile_iff] at h₂
  obtain ⟨b₁, hb₁, _, _, bd₂, hatt₂, hst₂⟩ := h₂
  have hb₁' : bd.bottomOf c = some b₁ := hb₁
  have hatt₂' : (bd.detach b₁).attach b₀ c = some bd₂ := hatt₂
  have hbb₁ : b₁ = b :=
    bd.inj b₁ b c ((Board.bottomOf_eq bd c b₁).mp hb₁') (Board.attach_topOf _ _ _ hatt)
  rw [hbb₁] at hatt₂'
  have hneA : (st.board.detach b₀).attach b c ≠ none := by rw [hatt]; simp
  obtain ⟨hta, _⟩ := (Board.attach_eq_some_iff _ _ _).mp hneA
  have htb : st.board.topOf b = none := by
    rw [← Board.detach_topOf_ne st.board b₀ b (Ne.symm hne)]
    exact hta
  have hbd₂ : bd₂ = st.board := by
    refine Board.ext_topOf (funext (fun b' => ?_))
    by_cases hbb₀ : b' = b₀
    · rw [hbb₀, Board.attach_topOf _ _ _ hatt₂', htop₀]
    · rw [Board.attach_topOf_ne _ _ _ hatt₂' hbb₀]
      by_cases hbb : b' = b
      · rw [hbb, Board.detach_topOf, htb]
      · rw [Board.detach_topOf_ne _ _ _ hbb, Board.attach_topOf_ne _ _ _ hatt hbb,
          Board.detach_topOf_ne _ _ _ hbb₀]
  rw [hst₂, hbd₂]

/- A full pass plus the wrap deal returns to the pass start: from
cursor 0, dealing everything (the clamp passes the last card) and
wrapping lands home — the deal cycle's period is `⌈n/s⌉ + 1`, at any
step `s ≥ 1` (deck.rs `offset`'s periodicity).  Supersedes the old
rotate-form "a full rotation is the identity", an artifact of the
jump semantics.  PROVEN below, with the deal-iteration kit (§5's
`run_dealIter` is the unpacking step — the statement lives there,
after the kit it needs). -/

/-- A commitment: no play returns to the state after it. -/
def irreversibleAt (st : State) (m : Move) : Prop :=
  ∀ st₁ play, st.apply m = some st₁ → st₁.run play ≠ some st

/-! The irreversibility trio — `irreversible_reveal`,
`irreversible_deckPile`, `irreversible_deckStack` — is proved in
Progress.lean (relocated 2026-09-13): the run-level monotonicity
lemmas it consumes (`run_totalDepth_le`, `run_stockLen_le`) live
there, and Progress imports this file, so the statements moved down
the import edge rather than duplicating the machinery. -/

/-- The accommodation moves (their Lemma A): stack↔pile shuffling. -/
def Move.isAccommodation : Move → Bool
  | .pileStack _ => true
  | .stackPile _ _ => true
  | _ => false

/-- The commitment moves (their Lemma A1). -/
def Move.isCommit : Move → Bool
  | .reveal _ => true
  | .deckPile _ _ => true
  | .deckStack _ => true
  | _ => false

/-- The accommodation relation (their Lemma A's shuffle reachability). -/
def accommodates (st st' : State) : Prop :=
  ∃ play, st.run play = some st' ∧ ∀ m ∈ play, m.isAccommodation = true

/-- The safety condition on an accommodation play: every `pileStack`
in it fires on an *unlocked* card, at the state it fires from (the
run walks the play's own states; `getD` is total, and on a successful
run it is the actual successor).  A locked `pileStack` is a commit,
not a shuffle — it strands the hidden boundary under the stacked card
forever (the dead-pile witness, `witnesses/B4LockedWitness.lean`). -/
def playSafeAccomm (st : State) : List Move → Prop
  | [] => True
  | m :: ms => (∀ c, m = Move.pileStack c → st.isLocked c = false) ∧
      playSafeAccomm ((st.apply m).getD st) ms

/-- The safe accommodation relation (B4's repaired domain): an
accommodation play whose `pileStack`s all fire unlocked. -/
def safeAccommodates (st st' : State) : Prop :=
  ∃ play, st.run play = some st' ∧ (∀ m ∈ play, m.isAccommodation = true) ∧
    playSafeAccomm st play

/-- Prepending plays: `run` distributes over `++` (the append lemma —
Progress's `run_append` restated for the upstream file, under the
`State` namespace to keep the names distinct). -/
theorem State.run_append (st : State) (l₁ l₂ : List Move) :
    st.run (l₁ ++ l₂) = (st.run l₁) >>= fun s => s.run l₂ := by
  revert st
  induction l₁ with
  | nil => intro st; rfl
  | cons m ms ih =>
      intro st
      simp only [List.cons_append, State.run]
      cases st.apply m with
      | none => rfl
      | some st' => exact ih st'

/-- The accommodation reduction, easy direction — prepend the shuffle
play: an accommodation play from `st'` to `st`, then the win. -/
theorem solvable_of_accommodates {st st' : State}
    (hacc : accommodates st' st) (hsol : st.solvableFrom) : st'.solvableFrom := by
  obtain ⟨play, hrun, _⟩ := hacc
  obtain ⟨win, w, hwrun, hwin⟩ := hsol
  refine ⟨play ++ win, w, ?_, hwin⟩
  rw [State.run_append, hrun]
  exact hwrun

/-- The worry-back return: after a `stackPile`, the taken-back card is
the foundation top and (WF: a foundation-passed card carries no tenant
— `founds_gone` + `board_edges`) nothing sits on it, so `pileStack`
takes the successor straight back.  Dominance's
`stackPile_pileStack_cancel` restated for the upstream file (Dominance
imports this one). -/
theorem stackPile_pileStack_return {st : State} {c : Card} {b : Base} {s₁ : State}
    (hwf : st.WF) (hsp : st.apply (Move.stackPile c b) = some s₁) :
    s₁.apply (Move.pileStack c) = some st := by
  rw [apply_stackPile_iff] at hsp
  obtain ⟨hg, hcp, bd, hatt, hs₁⟩ := hsp
  -- c is foundation-passed: neither visible nor hidden anywhere
  have hlt : c.rank.toIdx < st.heights c.suit := by omega
  obtain ⟨hvis, _, hhid⟩ := hwf.founds_gone c hlt
  have hnc : st.board.topOf (Sum.inr c) = none := by
    by_cases ht : st.board.topOf (Sum.inr c) = none
    · exact ht
    · exfalso
      obtain ⟨y, hy⟩ : ∃ y, st.board.topOf (Sum.inr c) = some y := by
        cases hh : st.board.topOf (Sum.inr c) with
        | none => rw [hh] at ht; exact absurd ht (by simp)
        | some y => exact ⟨y, rfl⟩
      obtain ⟨_, hbase⟩ := hwf.board_edges (Sum.inr c) y hy
      rcases hbase with ⟨_, _, _, _, hbc⟩ | ⟨hbd, _⟩
      · rcases hbc with ⟨a', hth⟩ | hbd
        · exact hhid a' (mem_of_getLast hth)
        · have hiv : (st.board.bottomOf c).isSome = false := hvis
          rw [hiv] at hbd
          exact Bool.noConfusion hbd
      · have hiv : (st.board.bottomOf c).isSome = false := hvis
        rw [hiv] at hbd
        exact Bool.noConfusion hbd
  -- b was free (the worry-back's own guard) and is not c's seat
  have hcpf := hcp
  simp only [State.canPlace] at hcpf
  have hfree : st.board.topOf b = none :=
    of_decide_eq_true (Bool.and_eq_true_iff.mp hcpf).1
  have hbne : Sum.inr c ≠ b := by
    cases b with
    | inl a => intro hcon; simp at hcon
    | inr d =>
        have hcp' := hcp
        simp only [State.canPlace] at hcp'
        obtain ⟨_, hivd⟩ := Bool.and_eq_true_iff.mp hcp'
        obtain ⟨hivd, _⟩ := Bool.and_eq_true_iff.mp hivd
        intro hcon
        injection hcon with hcd
        rw [← hcd] at hivd
        rw [hvis] at hivd
        exact Bool.noConfusion hivd
  -- the re-stack at the successor
  rw [hs₁]
  rw [apply_pileStack_iff]
  refine ⟨?_, b, ?_, ?_, ?_⟩
  · show bd.topOf (Sum.inr c) = none
    rw [Board.attach_topOf_ne _ _ _ hatt hbne]
    exact hnc
  · show bd.bottomOf c = some b
    exact (Board.bottomOf_eq bd c b).mpr (Board.attach_topOf _ _ _ hatt)
  · show c.rank.toIdx =
      (if c.suit = c.suit then st.heights c.suit - 1 else st.heights c.suit)
    rw [if_pos rfl]
    omega
  · show st = { { st with
        board := bd,
        heights := fun s => if s = c.suit then st.heights s - 1 else st.heights s } with
      board := bd.detach b,
      heights := fun s => if s = c.suit then
        (if s = c.suit then st.heights s - 1 else st.heights s) + 1
        else (if s = c.suit then st.heights s - 1 else st.heights s) }
    have hbdb : bd.detach b = st.board := by
      refine Board.ext_topOf (funext (fun b' => ?_))
      by_cases hbb : b' = b
      · rw [hbb, Board.detach_topOf, hfree]
      · rw [Board.detach_topOf_ne _ _ _ hbb, Board.attach_topOf_ne _ _ _ hatt hbb]
    have hhh : (fun s => if s = c.suit then
        (if s = c.suit then st.heights s - 1 else st.heights s) + 1
        else (if s = c.suit then st.heights s - 1 else st.heights s)) = st.heights := by
      funext s
      by_cases hsc : s = c.suit
      · subst hsc
        rw [if_pos rfl, if_pos rfl]
        omega
      · rw [if_neg hsc, if_neg hsc]
    exact state_ext rfl hbdb.symm hhh.symm rfl rfl rfl

/-- The worry-back half of the accommodation step: a legal `stackPile`
never hurts — `pileStack` takes the successor straight back (nothing
sits on a foundation-passed card), and the winning play prepends. -/
theorem solvable_of_stackPile {st : State} {c : Card} {b : Base} {s₁ : State}
    (hwf : st.WF) (hm : st.apply (Move.stackPile c b) = some s₁)
    (hsol : st.solvableFrom) : s₁.solvableFrom := by
  obtain ⟨win, w, hwrun, hwin⟩ := hsol
  refine ⟨Move.pileStack c :: win, w, ?_, hwin⟩
  show (match s₁.apply (Move.pileStack c) with
    | some st' => st'.run win
    | none => none) = some w
  rw [stackPile_pileStack_return hwf hm]
  exact hwrun

/-! ### The `¬locked` ⇒ visible-base lemma (the dead-pile trichotomy)

Relocated 2026-09-13 from Dominance.lean: the B4 crux below needs it,
and Dominance imports this file (not the other way).  Its ingredients
now live upstream too — `State.isLocked` (State.lean) and
`findFirst_ne_none_of_mem` (Board.lean). -/

/-- In a WF state, an unlocked visible card's card-base is itself
visible — the trichotomy behind the dead-pile repair: a visible card's
base is an anchor, a visible card, or its pile's hidden boundary, and
only the boundary case is `isLocked` (stacking onto it strands it).
The proof is the boundary half read contrapositively: `board_edges`
forces the base `d` of `c` to be placed (`bottomOf d` set — visible) or
deal-adjacent with `d` itself a hidden boundary or placed; if `d` is
*not* placed, some pile's `topHidden` is `d`, so `pileOfTopHidden d ≠
none` and `c` is locked after all.  (That `d` is never a limbo card —
revealed but neither visible nor on a foundation — also falls out: both
seating disjuncts of `board_edges` would fail for `c`'s edge.) -/
theorem vis_base_of_notLocked {st : State} {c d : Card} (hwf : st.WF)
    (hb : st.board.bottomOf c = some (Sum.inr d))
    (hnotlock : st.isLocked c = false) : st.isVis d = true := by
  have htop : st.board.topOf (Sum.inr d) = some c :=
    (Board.bottomOf_eq st.board c (Sum.inr d)).mp hb
  obtain ⟨_, hbase⟩ := hwf.board_edges (Sum.inr d) c htop
  rcases hbase with ⟨_, _, _, _, hbc⟩ | ⟨hbd, _⟩
  · rcases hbc with ⟨a', hth⟩ | hbd
    · exfalso
      have hlk : st.isLocked c = true := by
        simp only [State.isLocked, hb]
        exact decide_eq_true (fun h =>
          findFirst_ne_none_of_mem (fun a => decide (st.topHidden a = some d))
            Anchor.all a' a'.mem_all (decide_eq_true hth) h)
      simp [hlk] at hnotlock
    · exact hbd
  · exact hbd

/-! ### The stack-accommodation case lemmas

The crux below (the B4 reshape) splits by Dominance's R/N analysis on
`canReturnBase c b₀`, and within the N-half by the winning play's
first move.  Two of those cases close outright and are proven here,
upstream of the crux, as citable standalone lemmas:

* the **R-half** (`solvable_of_pileStack_return`): when `c` can return
  to its base, the foundation successor wins by returning first — the
  roundtrip takes it exactly back to `st`;
* the **run-root square** (`pileStack_pilePile_stackPile`): when the
  winning play itself re-homes `c` (`pilePile c b''`), the foundation
  successor replays it as `stackPile c b''` and lands on the very same
  successor — no induction, no return-base condition.  (In the
  first-move induction this case needs no IH at all: the tail runs
  unchanged.) -/

/-- The returnable half of the stack-accommodation step: when `c` can
return to its base (`canReturnBase`), the foundation successor wins by
returning first and replaying the winning play — `stackPile c b₀` is
legal at the successor (the base is free since `c` left it, and
fitting by `canReturnBase`; the card under an unlocked stackable is
visible, `vis_base_of_notLocked`), and `pileStack_stackPile_roundtrip`
takes the return exactly back to `st`. -/
theorem solvable_of_pileStack_return {st : State} (hwf : st.WF) {c : Card} {b₀ : Base}
    {s₁ : State} (hnotlock : st.isLocked c = false)
    (hbot : st.board.bottomOf c = some b₀) (hret : canReturnBase c b₀ = true)
    (hm : st.apply (Move.pileStack c) = some s₁) (hsol : st.solvableFrom) :
    s₁.solvableFrom := by
  have hmo := hm
  rw [apply_pileStack_iff] at hm
  obtain ⟨htopn, b, hb, hrk, hs₁⟩ := hm
  have hbb : b = b₀ := (Option.some.inj (hb.symm.trans hbot))
  rw [hbb] at hs₁
  have htop : st.board.topOf b₀ = some c := (Board.bottomOf_eq st.board c b₀).mp hbot
  -- the un-stack guard at the successor: the rung has moved one up
  have hrk' : c.rank.toIdx + 1 = s₁.heights c.suit := by
    rw [hs₁]
    show c.rank.toIdx + 1 =
      (if c.suit = c.suit then st.heights c.suit + 1 else st.heights c.suit)
    rw [if_pos rfl]
    omega
  have hfree : s₁.board.topOf b₀ = none := by
    rw [hs₁]
    exact Board.detach_topOf st.board b₀
  have hbotc : (st.board.detach b₀).bottomOf c = none :=
    Board.bottomOf_detach_self htop
  -- the return's landing rule at the successor
  have hcp : s₁.canPlace c b₀ = true := by
    cases b₀ with
    | inl a =>
        have hk : c.rank = Rank.king := of_decide_eq_true hret
        show (decide (s₁.board.topOf (Sum.inl a) = none) &&
            decide (c.rank = Rank.king)) = true
        rw [hfree]
        exact Bool.and_eq_true_iff.mpr ⟨rfl, decide_eq_true hk⟩
    | inr d =>
        have hdc : d ≠ c := by
          intro hde
          rw [hde] at hbot
          have hX : st.board.topOf (Sum.inr c) = some c :=
            (Board.bottomOf_eq st.board c (Sum.inr c)).mp hbot
          rw [htopn] at hX
          exact absurd hX (by simp)
        have hvisd : s₁.isVis d = true := by
          show (s₁.board.bottomOf d).isSome = true
          rw [hs₁]
          show ((st.board.detach (Sum.inr d)).bottomOf d).isSome = true
          rw [bottomOf_detach_ne htop hdc]
          exact vis_base_of_notLocked hwf hbot hnotlock
        have hsc : canSitOn c d = true := hret
        show (decide (s₁.board.topOf (Sum.inr d) = none) &&
            (s₁.isVis d && canSitOn c d)) = true
        rw [hfree]
        exact Bool.and_eq_true_iff.mpr ⟨rfl, Bool.and_eq_true_iff.mpr ⟨hvisd, hsc⟩⟩
  have hatt : (st.board.detach b₀).attach b₀ c = some st.board := by
    have hne : (st.board.detach b₀).attach b₀ c ≠ none :=
      (Board.attach_eq_some_iff _ _ _).mpr ⟨Board.detach_topOf st.board b₀, hbotc⟩
    cases hca : (st.board.detach b₀).attach b₀ c with
    | none => rw [hca] at hne; simp at hne
    | some bd =>
        have hbdeq : bd = st.board := by
          refine Board.ext_topOf (funext (fun b' => ?_))
          by_cases hbb : b' = b₀
          · subst hbb
            rw [Board.attach_topOf _ _ _ hca, htop]
          · rw [Board.attach_topOf_ne _ _ _ hca hbb,
              Board.detach_topOf_ne st.board b₀ b' hbb]
        rw [hbdeq]
  have hatt' : s₁.board.attach b₀ c = some st.board := by
    rw [hs₁]
    exact hatt
  have hsucc : s₁.apply (Move.stackPile c b₀) = some {s₁ with
      board := st.board,
      heights := fun s => if s = c.suit then s₁.heights s - 1 else s₁.heights s } :=
    (apply_stackPile_iff).mpr ⟨hrk', hcp, st.board, hatt', rfl⟩
  have hrt : {s₁ with
      board := st.board,
      heights := fun s => if s = c.suit then s₁.heights s - 1 else s₁.heights s } = st :=
    pileStack_stackPile_roundtrip hbot hret hmo hsucc
  obtain ⟨win, w, hwrun, hwin⟩ := hsol
  refine ⟨Move.stackPile c b₀ :: win, w, ?_, hwin⟩
  show (match s₁.apply (Move.stackPile c b₀) with
    | some st' => st'.run win
    | none => none) = some w
  rw [hsucc.trans (congrArg some hrt)]
  exact hwrun

/-! ### The commute squares (the N-half's replay steps)

For each move shape that does not touch `c`'s seat, tenancy, or rung,
the stack difference replays: both orders — stack-then-move and
move-then-stack — land on the same state `t`.  The induction then
applies at `s₂` (the move's successor, with the winning tail) and
lifts `t`'s solvability back to `s₁` through the replayed move. -/

/-- The draw square: the deal writes only the stock cursor, the stack
only the board and one height, so both orders land on the same
state. -/
theorem pileStack_comm_draw {st : State} {c : Card} {b₀ : Base} {s₁ s₂ : State}
    (hbot : st.board.bottomOf c = some b₀) (hrk : c.rank.toIdx = st.heights c.suit)
    (hm : st.apply (Move.pileStack c) = some s₁)
    (hmd : st.apply Move.draw = some s₂) :
    ∃ t, s₁.apply Move.draw = some t ∧ s₂.apply (Move.pileStack c) = some t := by
  rw [apply_pileStack_iff] at hm
  obtain ⟨htopn, b, hb, hrk', hs₁⟩ := hm
  have hbb : b = b₀ := (Option.some.inj (hb.symm.trans hbot))
  rw [hbb] at hs₁
  rw [apply_draw_iff] at hmd
  obtain rfl := hmd
  subst hs₁
  refine ⟨{st with
    board := st.board.detach b₀,
    heights := fun s => if s = c.suit then st.heights s + 1 else st.heights s,
    stock := st.stock.dealOnce st.drawStep }, ?_, ?_⟩
  · exact (apply_draw_iff).mpr rfl
  · exact (apply_pileStack_iff).mpr ⟨htopn, b₀, hbot, hrk, rfl⟩

/-- The reveal square: revealing under `x` commutes with the stack.  The
reveal writes the board at `hiddenBase a` (never `c`'s seat `b₀` — `c`
occupies it, so the attach that would sit there is dead on arrival)
and one depth; the stack writes the board at `b₀` and one height.
`x = c` cannot occur (`reveal c` needs `c`'s own base hidden, i.e.
`c` locked), and `hiddenBase a`'s card is hidden, hence not the
visible `c`.  The equality of the two ends is `comm_reveal_pileStack`
(`Commutation.lean`), whose disjointness premise is derived here. -/
theorem pileStack_comm_reveal {st : State} {c x : Card} {b₀ : Base} {s₁ s₂ : State}
    (hwf : st.WF) (hnotlock : st.isLocked c = false)
    (hbot : st.board.bottomOf c = some b₀) (hrk : c.rank.toIdx = st.heights c.suit)
    (hm : st.apply (Move.pileStack c) = some s₁)
    (hmr : st.apply (Move.reveal x) = some s₂) :
    ∃ t, s₁.apply (Move.reveal x) = some t ∧ s₂.apply (Move.pileStack c) = some t := by
  have hmo := hm
  have hmo2 := hmr
  rw [apply_pileStack_iff] at hm
  obtain ⟨htopn, b, hb, hrk', hs₁⟩ := hm
  have hbb : b = b₀ := (Option.some.inj (hb.symm.trans hbot))
  rw [hbb] at hs₁
  have htop : st.board.topOf b₀ = some c := (Board.bottomOf_eq st.board c b₀).mp hbot
  rw [apply_reveal_iff] at hmr
  obtain ⟨htopx, r, a, bd, hbx, hpile, hatt, hs₂⟩ := hmr
  -- the disjointness facts
  have hgt : (st.hidden a).getLast? = some r :=
    of_decide_eq_true ((findFirst_mem _ _ _ hpile).2)
  have hxc : x ≠ c := by
    intro hxe
    rw [hxe] at hbx
    have hlk : st.isLocked c = true := by
      simp [State.isLocked, hbx, hpile]
    rw [hlk] at hnotlock
    exact Bool.noConfusion hnotlock
  have hrc : r ≠ c := by
    intro hre
    have hX : st.board.topOf (Sum.inr r) = some x :=
      (Board.bottomOf_eq st.board x (Sum.inr r)).mp hbx
    rw [hre] at hX
    rw [htopn] at hX
    exact absurd hX (by simp)
  have hβ : st.hiddenBase a ≠ b₀ := by
    intro hbe
    have hfree : st.board.topOf (st.hiddenBase a) = none := by
      have h := (Board.attach_eq_some_iff st.board (st.hiddenBase a) r).mp (by rw [hatt]; simp)
      exact h.1
    rw [hbe, htop] at hfree
    exact absurd hfree (by simp)
  have hbxne : Sum.inr x ≠ b₀ := by
    intro hbe
    rw [← hbe] at htop
    rw [htopx] at htop
    exact absurd htop (by simp)
  -- the boundary's parent is hidden, hence not the visible c
  have hbc : Sum.inr c ≠ st.hiddenBase a := by
    intro hbe
    have hcvis : st.isVis c = true := by
      show (st.board.bottomOf c).isSome = true
      rw [hbot]
      rfl
    simp only [State.hiddenBase] at hbe
    cases hrev : ((st.hidden a).reverse.drop 1).head? with
    | none => rw [hrev] at hbe; exact absurd hbe (by simp)
    | some z =>
        have hzz : (Sum.inr z : Base) = Sum.inr c := by
          rw [hrev] at hbe
          exact hbe.symm
        have hzc : z = c := by injection hzz
        rw [hzc] at hrev
        obtain ⟨pre, hpre⟩ := hidden_split hrev hgt
        exact hwf.vis_not_hidden c hcvis a (by rw [hpre]; simp)
  -- the boundary card is not visible, so the reveal's attach is safe
  have hbrn : st.board.bottomOf r = none := by
    cases hbb : st.board.bottomOf r with
    | none => rfl
    | some b' =>
        exfalso
        have hrv : st.isVis r = true := by
          show (st.board.bottomOf r).isSome = true
          rw [hbb]
          rfl
        have hrmem : r ∈ st.hidden a := mem_of_getLast hgt
        exact hwf.vis_not_hidden r hrv a hrmem
  -- the reveal replays from the stack successor
  have hfreen : (st.board.detach b₀).topOf (st.hiddenBase a) = none := by
    rw [Board.detach_topOf_ne st.board b₀ _ hβ]
    have h := (Board.attach_eq_some_iff st.board (st.hiddenBase a) r).mp (by rw [hatt]; simp)
    exact h.1
  have hbotrn : (st.board.detach b₀).bottomOf r = none := by
    rw [bottomOf_detach_ne htop hrc]
    exact hbrn
  have hne : (st.board.detach b₀).attach (st.hiddenBase a) r ≠ none :=
    (Board.attach_eq_some_iff _ _ _).mpr ⟨hfreen, hbotrn⟩
  cases hatt₁ : (st.board.detach b₀).attach (st.hiddenBase a) r with
  | none => rw [hatt₁] at hne; simp at hne
  | some bd₁ =>
      have hL : s₁.apply (Move.reveal x) = some {s₁ with
          board := bd₁,
          depths := fun a' => if a' = a then s₁.depths a - 1 else s₁.depths a' } := by
        rw [hs₁, apply_reveal_iff]
        refine ⟨?_, r, a, bd₁, ?_, ?_, hatt₁, rfl⟩
        · show (st.board.detach b₀).topOf (Sum.inr x) = none
          rw [Board.detach_topOf_ne st.board b₀ _ hbxne]
          exact htopx
        · show (st.board.detach b₀).bottomOf x = some (Sum.inr r)
          rw [bottomOf_detach_ne htop hxc]
          exact hbx
        · exact (pileOfTopHidden_congr rfl rfl r).symm.trans hpile
      -- the stack replays from the reveal successor
      have htopn₂ : bd.topOf (Sum.inr c) = none := by
        rw [Board.attach_topOf_ne _ _ _ hatt hbc]
        exact htopn
      have hbot₂ : bd.bottomOf c = some b₀ :=
        (Board.bottomOf_eq bd c b₀).mpr (by
          rw [Board.attach_topOf_ne _ _ _ hatt (fun hcon => hβ hcon.symm)]
          exact htop)
      have hR : s₂.apply (Move.pileStack c) = some {s₂ with
          board := bd.detach b₀,
          heights := fun s => if s = c.suit then s₂.heights s + 1 else s₂.heights s } := by
        rw [hs₂, apply_pileStack_iff]
        exact ⟨htopn₂, b₀, hbot₂, hrk, rfl⟩
      -- the two orders end in the same state (the commutation kit)
      have hcomp₁ : (st.apply (Move.pileStack c) >>= fun s => s.apply (Move.reveal x)) =
          some {s₁ with
            board := bd₁,
            depths := fun a' => if a' = a then s₁.depths a - 1 else s₁.depths a' } := by
        rw [hmo]
        exact hL
      have hcomp₂ : (st.apply (Move.reveal x) >>= fun s => s.apply (Move.pileStack c)) =
          some {s₂ with
            board := bd.detach b₀,
            heights := fun s => if s = c.suit then s₂.heights s + 1 else s₂.heights s } := by
        rw [hmo2]
        exact hR
      have heq := comm_reveal_pileStack
        (by
          have hRt : (Move.reveal x).touch st = ([st.hiddenBase a], [x, r]) := by
            simp only [Move.touch, hbx, hpile]
          have hPSt : (Move.pileStack c).touch st = ([b₀], [c]) := by
            simp only [Move.touch, hbot, Option.toList_some]
          rw [hRt, hPSt]
          refine ⟨?_, ?_⟩
          · intro bb hbmem hxmem
            simp only [List.mem_singleton] at hbmem hxmem
            rw [hbmem] at hxmem
            exact hβ hxmem
          · intro cc ccmem cxmem
            simp only [List.mem_cons, List.not_mem_nil] at ccmem
            simp only [List.mem_singleton] at cxmem
            rcases ccmem with hc | hc | hc
            · rw [hc] at cxmem; exact hxc cxmem
            · rw [hc] at cxmem; exact hrc cxmem
            · exact hc.elim)
        hcomp₂ hcomp₁
      exact ⟨_, hL, hR.trans (congrArg some heq)⟩

/-- The deckStack square: stacking the stock card `x` commutes with
the stack — the deck move writes the stock and `x`'s suit height, the
stack the board and `c`'s suit height, and the suits differ (`x` is in
the stock, `c` is visible hence off the cycle, and a shared suit
would force `x = c` through the two rank guards).  The equality of
the ends is `comm_deckStack_pileStack`. -/
theorem pileStack_comm_deckStack {st : State} {c x : Card} {b₀ : Base} {s₁ s₂ : State}
    (hwf : st.WF)
    (hbot : st.board.bottomOf c = some b₀) (hrk : c.rank.toIdx = st.heights c.suit)
    (hm : st.apply (Move.pileStack c) = some s₁)
    (hmd : st.apply (Move.deckStack x) = some s₂) :
    ∃ t, s₁.apply (Move.deckStack x) = some t ∧ s₂.apply (Move.pileStack c) = some t := by
  have hmo := hm
  have hmo2 := hmd
  rw [apply_pileStack_iff] at hm
  obtain ⟨htopn, b, hb, hrk', hs₁⟩ := hm
  have hbb : b = b₀ := (Option.some.inj (hb.symm.trans hbot))
  rw [hbb] at hs₁
  rw [apply_deckStack_iff] at hmd
  obtain ⟨hprev, hrkx, hs₂⟩ := hmd
  -- x is in the stock, c is visible (hence off the cycle): x ≠ c
  have hmem : x ∈ st.stock.cards := by
    simp only [Cycle.prev] at hprev
    split at hprev
    · exact absurd hprev (by simp)
    · exact List.mem_iff_getElem?.mpr ⟨st.stock.cursor - 1, hprev⟩
  have hxc : x ≠ c := by
    intro hxe
    rw [hxe] at hmem
    exact Cycle.posOf_mem hmem (hwf.vis_off_cycle c (by
      show (st.board.bottomOf c).isSome = true
      rw [hbot]
      rfl))
  have hσ : x.suit ≠ c.suit := by
    intro hse
    have h1 : x.rank.toIdx = c.rank.toIdx := by rw [hrkx, hrk, hse]
    have h2 : x.rank = c.rank := Rank.toIdx_inj h1
    exact hxc (by cases x; cases c; simp_all)
  -- the deck move replays from the stack successor
  have hL : s₁.apply (Move.deckStack x) = some {s₁ with
      stock := st.stock.removeAt (st.stock.cursor - 1),
      heights := fun s => if s = x.suit then s₁.heights s + 1 else s₁.heights s } := by
    rw [hs₁, apply_deckStack_iff]
    refine ⟨hprev, ?_, rfl⟩
    show x.rank.toIdx =
      (if x.suit = c.suit then st.heights x.suit + 1 else st.heights x.suit)
    rw [if_neg hσ]
    exact hrkx
  -- the stack replays from the deck successor
  have hR : s₂.apply (Move.pileStack c) = some {s₂ with
      board := st.board.detach b₀,
      heights := fun s => if s = c.suit then s₂.heights s + 1 else s₂.heights s } := by
    rw [hs₂, apply_pileStack_iff]
    refine ⟨htopn, b₀, hbot, ?_, rfl⟩
    show c.rank.toIdx =
      (if c.suit = x.suit then st.heights c.suit + 1 else st.heights c.suit)
    rw [if_neg (Ne.symm hσ)]
    exact hrk
  -- the two orders end in the same state (the commutation kit)
  have hcomp₁ : (st.apply (Move.pileStack c) >>= fun s => s.apply (Move.deckStack x)) =
      some {s₁ with
        stock := st.stock.removeAt (st.stock.cursor - 1),
        heights := fun s => if s = x.suit then s₁.heights s + 1 else s₁.heights s } := by
    rw [hmo]
    exact hL
  have hcomp₂ : (st.apply (Move.deckStack x) >>= fun s => s.apply (Move.pileStack c)) =
      some {s₂ with
        board := st.board.detach b₀,
        heights := fun s => if s = c.suit then s₂.heights s + 1 else s₂.heights s } := by
    rw [hmo2]
    exact hR
  have heq := comm_deckStack_pileStack
    (by
      have hDSt : (Move.deckStack x).touch st = ([], [x]) := rfl
      have hPSt : (Move.pileStack c).touch st = ([b₀], [c]) := by
        simp only [Move.touch, hbot, Option.toList_some]
      rw [hDSt, hPSt]
      refine ⟨?_, ?_⟩
      · intro bb hbm
        simp at hbm
      · intro cc ccmem cxmem
        simp only [List.mem_singleton] at ccmem cxmem
        rw [ccmem] at cxmem
        exact hxc cxmem)
    hcomp₂ hcomp₁
  exact ⟨_, hL, hR.trans (congrArg some heq)⟩

/-- The deckPile square: playing the stock card `x` onto a base that is
neither `c`'s seat `b₀` (occupied, so unreachable in the winning play)
nor `c` itself (`inr c` — the park, the blocked residue) commutes with
the stack.  The board relation between the two orders is
`attach_detach_comm`; the equality of the ends is
`comm_deckPile_pileStack`. -/
theorem pileStack_comm_deckPile {st : State} {c x : Card} {b₀ b'' : Base} {s₁ s₂ : State}
    (hwf : st.WF)
    (hbot : st.board.bottomOf c = some b₀) (hrk : c.rank.toIdx = st.heights c.suit)
    (hm : st.apply (Move.pileStack c) = some s₁)
    (hmd : st.apply (Move.deckPile x b'') = some s₂)
    (hnc : b'' ≠ Sum.inr c) :
    ∃ t, s₁.apply (Move.deckPile x b'') = some t ∧ s₂.apply (Move.pileStack c) = some t := by
  have hmo := hm
  have hmo2 := hmd
  rw [apply_pileStack_iff] at hm
  obtain ⟨htopn, b, hb, hrk', hs₁⟩ := hm
  have hbb : b = b₀ := (Option.some.inj (hb.symm.trans hbot))
  rw [hbb] at hs₁
  have htop : st.board.topOf b₀ = some c := (Board.bottomOf_eq st.board c b₀).mp hbot
  rw [apply_deckPile_iff] at hmd
  obtain ⟨hprev, hcp, bd, hatt, hs₂⟩ := hmd
  -- the landing base is not c's seat (c occupies it, so canPlace fails)
  have hnb : b'' ≠ b₀ := by
    intro hbe
    have hcp' := hcp
    simp only [State.canPlace] at hcp'
    rw [hbe] at hcp'
    rw [htop] at hcp'
    exact absurd hcp' (by simp)
  -- x ≠ c: x is in the stock, c is visible (hence off the cycle)
  have hmem : x ∈ st.stock.cards := by
    simp only [Cycle.prev] at hprev
    split at hprev
    · exact absurd hprev (by simp)
    · exact List.mem_iff_getElem?.mpr ⟨st.stock.cursor - 1, hprev⟩
  have hxc : x ≠ c := by
    intro hxe
    rw [hxe] at hmem
    exact Cycle.posOf_mem hmem (hwf.vis_off_cycle c (by
      show (st.board.bottomOf c).isSome = true
      rw [hbot]
      rfl))
  -- the deck move replays from the stack successor
  have hfreen : (st.board.detach b₀).topOf b'' = none := by
    rw [Board.detach_topOf_ne st.board b₀ _ hnb]
    have h1 : st.board.topOf b'' = none := by
      have hcp' := hcp
      simp only [State.canPlace] at hcp'
      exact of_decide_eq_true (Bool.and_eq_true_iff.mp hcp').1
    exact h1
  have hbotxn : (st.board.detach b₀).bottomOf x = none := by
    rw [bottomOf_detach_ne htop hxc]
    exact ((Board.attach_eq_some_iff st.board b'' x).mp (by rw [hatt]; simp)).2
  have hne : (st.board.detach b₀).attach b'' x ≠ none :=
    (Board.attach_eq_some_iff _ _ _).mpr ⟨hfreen, hbotxn⟩
  cases hatt₁ : (st.board.detach b₀).attach b'' x with
  | none => rw [hatt₁] at hne; simp at hne
  | some bd₁ =>
      have htopst : st.board.topOf b'' = none := by
        have hcp'' := hcp
        simp only [State.canPlace] at hcp''
        exact of_decide_eq_true (Bool.and_eq_true_iff.mp hcp'').1
      have hcp' : s₁.canPlace x b'' = true := by
        cases b'' with
        | inl a =>
            have hcp'' := hcp
            simp only [State.canPlace] at hcp''
            have hf : s₁.board.topOf (Sum.inl a) = none := by
              rw [hs₁]
              show (st.board.detach b₀).topOf (Sum.inl a) = none
              rw [Board.detach_topOf_ne st.board b₀ _ hnb]
              exact htopst
            show (decide (s₁.board.topOf (Sum.inl a) = none) &&
              decide (x.rank = Rank.king)) = true
            rw [hf]
            exact Bool.and_eq_true_iff.mpr ⟨rfl, (Bool.and_eq_true_iff.mp hcp'').2⟩
        | inr d =>
            have hcp'' := hcp
            simp only [State.canPlace] at hcp''
            obtain ⟨hvisd, hcs⟩ := Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hcp'').2
            have hdne : d ≠ c := by
              intro hde
              exact hnc (by rw [hde])
            have hvisd' : (s₁.board.bottomOf d).isSome = true := by
              rw [hs₁]
              show ((st.board.detach b₀).bottomOf d).isSome = true
              rw [bottomOf_detach_ne htop hdne]
              exact hvisd
            have hf : s₁.board.topOf (Sum.inr d) = none := by
              rw [hs₁]
              show (st.board.detach b₀).topOf (Sum.inr d) = none
              exact hfreen
            show (decide (s₁.board.topOf (Sum.inr d) = none) &&
              ((s₁.board.bottomOf d).isSome && canSitOn x d)) = true
            rw [hf]
            exact Bool.and_eq_true_iff.mpr ⟨rfl, Bool.and_eq_true_iff.mpr ⟨hvisd', hcs⟩⟩
      have hprev' : s₁.stock.prev = some x := by rw [hs₁]; exact hprev
      have hatt₁' : s₁.board.attach b'' x = some bd₁ := by rw [hs₁]; exact hatt₁
      have hL : s₁.apply (Move.deckPile x b'') = some {s₁ with
          board := bd₁,
          stock := s₁.stock.removeAt (s₁.stock.cursor - 1) } := by
        rw [apply_deckPile_iff]
        exact ⟨hprev', hcp', bd₁, hatt₁', rfl⟩
      -- the stack replays from the deck successor
      have htopn₂ : bd.topOf (Sum.inr c) = none := by
        rw [Board.attach_topOf_ne _ _ _ hatt (Ne.symm hnc)]
        exact htopn
      have hbot₂ : bd.bottomOf c = some b₀ :=
        (Board.bottomOf_eq bd c b₀).mpr (by
          rw [Board.attach_topOf_ne _ _ _ hatt (Ne.symm hnb)]
          exact htop)
      have hR : s₂.apply (Move.pileStack c) = some {s₂ with
          board := bd.detach b₀,
          heights := fun s => if s = c.suit then s₂.heights s + 1 else s₂.heights s } := by
        rw [hs₂, apply_pileStack_iff]
        exact ⟨htopn₂, b₀, hbot₂, hrk, rfl⟩
      -- the two orders end in the same state (the commutation kit)
      have hcomp₁ : (st.apply (Move.pileStack c) >>= fun s => s.apply (Move.deckPile x b'')) =
          some {s₁ with
            board := bd₁,
            stock := s₁.stock.removeAt (s₁.stock.cursor - 1) } := by
        rw [hmo]
        exact hL
      have hcomp₂ : (st.apply (Move.deckPile x b'') >>= fun s => s.apply (Move.pileStack c)) =
          some {s₂ with
            board := bd.detach b₀,
            heights := fun s => if s = c.suit then s₂.heights s + 1 else s₂.heights s } := by
        rw [hmo2]
        exact hR
      have heq := comm_deckPile_pileStack
        (by
          have hDPt : (Move.deckPile x b'').touch st = ([b''], [x]) := rfl
          have hPSt : (Move.pileStack c).touch st = ([b₀], [c]) := by
            simp only [Move.touch, hbot, Option.toList_some]
          rw [hDPt, hPSt]
          refine ⟨?_, ?_⟩
          · intro bb hbmem hxmem
            simp only [List.mem_singleton] at hbmem hxmem
            rw [hbmem] at hxmem
            exact hnb hxmem
          · intro cc ccmem cxmem
            simp only [List.mem_singleton] at ccmem cxmem
            rw [ccmem] at cxmem
            exact hxc cxmem)
        hcomp₂ hcomp₁
      exact ⟨_, hL, hR.trans (congrArg some heq)⟩

/-- The run-root square: if the winning play's own move re-homes `c`
(`pilePile c b''` — legal at `st`), the foundation successor replays it
as `stackPile c b''` and lands on exactly the same successor.  The
un-stack guard `toIdx c + 1` is the stacked heights; the heights
un-bump; the board is the same detach-then-attach; the stock, deal and
depths are untouched by both moves. -/
theorem pileStack_pilePile_stackPile {st : State} {c : Card} {b₀ b'' : Base} {s₁ s₂ : State}
    (hbot : st.board.bottomOf c = some b₀) (hrk : c.rank.toIdx = st.heights c.suit)
    (hm : st.apply (Move.pileStack c) = some s₁)
    (hmp : st.apply (Move.pilePile c b'') = some s₂) :
    s₁.apply (Move.stackPile c b'') = some s₂ := by
  rw [apply_pileStack_iff] at hm
  obtain ⟨htopn, b, hb, hrk', hs₁⟩ := hm
  have hbb : b = b₀ := (Option.some.inj (hb.symm.trans hbot))
  rw [hbb] at hs₁
  rw [apply_pilePile_iff] at hmp
  obtain ⟨b₀', hb₀', hne, hcm, bd, hatt, hs₂⟩ := hmp
  have hbb₀ : b₀' = b₀ := (Option.some.inj (hb₀'.symm.trans hbot))
  rw [hbb₀] at hne hatt
  -- the landing rule `c` satisfied at `st` transfers to the successor
  have hcp := hcm
  simp only [State.canMoveRun] at hcp
  obtain ⟨hcp, -⟩ := Bool.and_eq_true_iff.mp hcp
  simp only [State.canPlace] at hcp
  obtain ⟨htopb'', hbody⟩ := Bool.and_eq_true_iff.mp hcp
  have htopst : st.board.topOf b'' = none := of_decide_eq_true htopb''
  -- the un-stack guard at the successor
  have hrk'' : c.rank.toIdx + 1 = s₁.heights c.suit := by
    rw [hs₁]
    show c.rank.toIdx + 1 =
      (if c.suit = c.suit then st.heights c.suit + 1 else st.heights c.suit)
    rw [if_pos rfl]
    omega
  -- the base is still free (c's old base is not the target) and still fitting
  have hneb : b₀ ≠ b'' := hne
  have hfree' : s₁.board.topOf b'' = none := by
    rw [hs₁]
    show (st.board.detach b₀).topOf b'' = none
    rw [Board.detach_topOf_ne st.board b₀ b'' (Ne.symm hneb)]
    exact htopst
  have hbotc : (st.board.detach b₀).bottomOf c = none :=
    Board.bottomOf_detach_self ((Board.bottomOf_eq st.board c b₀).mp hbot)
  have hcp' : s₁.canPlace c b'' = true := by
    cases b'' with
    | inl a =>
        have hk : c.rank = Rank.king := of_decide_eq_true hbody
        show (decide (s₁.board.topOf (Sum.inl a) = none) &&
            decide (c.rank = Rank.king)) = true
        rw [hfree']
        exact Bool.and_eq_true_iff.mpr ⟨rfl, decide_eq_true hk⟩
    | inr d =>
        obtain ⟨hvisd₀, hcs⟩ := Bool.and_eq_true_iff.mp hbody
        have hdc : d ≠ c := by
          intro hde
          rw [hde] at hcs
          simp only [canSitOn_eq] at hcs
          obtain ⟨h1, -⟩ := hcs
          omega
        have hvisd : s₁.isVis d = true := by
          show (s₁.board.bottomOf d).isSome = true
          rw [hs₁]
          show ((st.board.detach b₀).bottomOf d).isSome = true
          rw [bottomOf_detach_ne ((Board.bottomOf_eq st.board c b₀).mp hbot) hdc]
          exact hvisd₀
        show (decide (s₁.board.topOf (Sum.inr d) = none) &&
            (s₁.isVis d && canSitOn c d)) = true
        rw [hfree']
        exact Bool.and_eq_true_iff.mpr ⟨rfl, Bool.and_eq_true_iff.mpr ⟨hvisd, hcs⟩⟩
  have hatt' : s₁.board.attach b'' c = some bd := by
    rw [hs₁]
    exact hatt
  refine (apply_stackPile_iff).mpr ⟨hrk'', hcp', bd, hatt', ?_⟩
  rw [hs₂, hs₁]
  refine state_ext rfl rfl ?_ rfl rfl rfl
  funext s
  by_cases hsc : s = c.suit
  · show st.heights s =
      (if s = c.suit then
          (if s = c.suit then st.heights s + 1 else st.heights s) - 1
          else (if s = c.suit then st.heights s + 1 else st.heights s))
    rw [if_pos hsc, if_pos hsc]
    omega
  · show st.heights s =
      (if s = c.suit then
          (if s = c.suit then st.heights s + 1 else st.heights s) - 1
          else (if s = c.suit then st.heights s + 1 else st.heights s))
    rw [if_neg hsc, if_neg hsc]

set_option linter.unusedVariables false in
/-- The stack half of the accommodation step — the isolated B4 reshape
crux (this file's only `sorry`): a legal `pileStack` of an *unlocked*
card never hurts solvability.  Together with `solvable_of_stackPile`
this is the whole content of the hard direction; the play-level
lifting below is proved.

STATEMENT REPAIRED (2026-09-13, prover-confirmed witness
`witnesses/B4LockedWitness.lean`, facts axiom-clean): as staged (no
lockedness) it was FALSE — the dead-pile hole, the same one that
repaired `safe_pileStack_dominant` (Dominance's accepted `hnotlock`
guard).  When `c` sits on its pile's hidden boundary, stacking it
strands the boundary card forever: no tenant can ever sit on it again
(`canPlace` demands a visible base, `reveal` demands a visible card on
the boundary), so it can never reach the foundation and the successor
is unsolvable — while the source state wins by revealing through `c`
first (the witness: reveal ♦K, stack ♦K, stack ♣K — three moves).
The same witness refutes `solvable_accommodates` as staged (the
accommodation play `[pileStack ♦K]`), so the repair carries through the
whole chain below (`playSafeAccomm`).  Repair: `+ (hnotlock :
st.isLocked c = false)`, conclusion unchanged — a locked stack is a
commit, not a shuffle.

TODO(proof) [H].  PLAN (verify, don't trust): the R/N split first —

* R (`canReturnBase c b₀ = true`): DONE, `solvable_of_pileStack_return`
  above — return and replay.
* N (non-returnable: `c`'s base deal-adjacent with `canSitOn c d`
  false, or a non-king pile-bottom on its anchor): induct on the
  winning play π from `st`, splitting on π's first move.
  * `pileStack c` itself — delete it: `s₁` runs π's tail directly.
  * `pilePile c b''` — DONE, `pileStack_pilePile_stackPile` above: the
    successor replays it as `stackPile c b''` onto the very same
    successor; the tail runs unchanged (no IH needed).
  * Moves commuting with the `c`-difference — replay and induct: no move
    of π can seat at `c`'s base `b₀` while `c` occupies it, and the
    blindness kit covers the components `c` does not touch.  (`reveal
    c` cannot occur — its trigger needs `c`'s base hidden, excluded by
    `hnotlock`; `deckStack` of a phantom stock copy of `c` is excluded
    by `vis_off_cycle`.)  LANDED as the commute squares
    `pileStack_comm_draw`, `pileStack_comm_reveal`,
    `pileStack_comm_deckStack`, `pileStack_comm_deckPile` (the `∃ t`
    form: both orders land on the same state; the equality half is the
    Commutation kit's `comm_*_pileStack`, with the disjointness premise
    derived here); REMAINING: `stackPile x b''` (`x.suit ≠ c.suit`) and
    `pilePile x b''` (`x ≠ c`), both with `b'' ∉ {b₀, inr c}` — same
    pattern (equality halves `comm_pileStack_stackPile`,
    `comm_pileStack_pilePile` exist; the deckPile square is the closest
    template).
  * Moves seating ON `c` (`deckPile`/`stackPile`/`pilePile` x `(inr c)`)
    — the park.  KEY STRUCTURE (the catch-22 that makes the reshape
    work): every park is transient — `c`'s suit must pass rung
    `toIdx c` before winning, the rung card is `c` itself, and a stacked
    `c` admits no tenant, so the parked `x` leaves before the rung
    passes; `x`'s exit is its own `pileStack` (rung-gated but
    `c`-suit-independent — fires equally from `s₁`) or a reseat on a
    rank-mate; delay the rung past the park and the delete-strategy
    applies from the other side.
  * `stackPile` of `c`'s suit at the shifted rung `toIdx c - 1` — the
    excursion pair (net identity): replay at the shifted height.  (Both
    this and the park reduce to the endgame: the excursion fires from
    `s₁` only after a return drops the rung back.)

The endgame is the return-base crux: when `c`'s base was deal-adjacent,
`canReturnBase` fails and the worry-back lands on a rank-mate instead —
the Dominance ledger's N-half, the same root (the three blocked shapes
recorded there: storage parks, run-carrying re-homes, rung-offset
reads — all needing the compliant-play normal form).  The gate lifts
are done (2026-09-13): `State.isLocked` in State.lean,
`findFirst_ne_none_of_mem` and `Board.bottomOf_detach_self` in
Board.lean. -/
theorem solvable_of_pileStack {st : State} (hwf : st.WF) {c : Card} {s₁ : State}
    (hnotlock : st.isLocked c = false)
    (hm : st.apply (Move.pileStack c) = some s₁) (hsol : st.solvableFrom) :
    s₁.solvableFrom := sorry

/-- The one-step core: an accommodation move that succeeds preserves
solvability — dispatch to the two halves.  REPAIRED 2026-09-13 with
the crux (`hnl`, the per-move `playSafeAccomm` head): a locked
`pileStack` is not a solvability-preserving shuffle (the dead-pile
witness). -/
theorem solvable_of_accomm_step {st : State} {m : Move} {s₂ : State}
    (hwf : st.WF) (hm : st.apply m = some s₂) (hsol : st.solvableFrom)
    (hmacc : m.isAccommodation = true)
    (hnl : ∀ c, m = Move.pileStack c → st.isLocked c = false) : s₂.solvableFrom := by
  cases m with
  | pileStack c => exact solvable_of_pileStack hwf (hnl c rfl) hm hsol
  | stackPile c b => exact solvable_of_stackPile hwf hm hsol
  | draw | reveal _ | deckPile _ _ | deckStack _ | pilePile _ _ =>
      exact absurd hmacc (by simp [Move.isAccommodation])

/-- The accommodation reduction, hard direction — the reshape lemma
(B4): a winning play survives the cards having been shuffled through
the foundations.

STATEMENT REPAIRED (2026-09-13): as staged (no WF hypothesis) it was
FALSE — prover-confirmed witness `Temp/opencode/B4Witness.lean`
(axiom-clean facts): a WON state with a *phantom tenant* (♠2 seated on
base `inr ♠K` while ♠K is unplaced — exactly what WF's `board_edges`
forbids) and junk occupying every anchor but p0; the accommodation
`[stackPile ♠K p0]` seats the king under its tenant, and the successor
is a total deadlock (only `draw` fires, as the identity) — ♠K can never
re-stack, so it is unsolvable while the source is already won.  Repair:
add `(hwf : st.WF)` — the design docs' invariant, preserved by the
accommodation moves themselves (`apply_wf`).  No downstream users of
the old statement existed.

STATEMENT REPAIRED AGAIN (2026-09-13, witness `witnesses/
B4LockedWitness.lean`): the phantom-tenant guard did not close the
*locked* stack — the dead-pile hole (see the crux's repair note): the
accommodation play `[pileStack ♦K]` from a WF, three-moves-from-win
state lands in an unsolvable successor.  Repair: the hypothesis is now
`safeAccommodates` — the accommodation play's `pileStack`s must all
fire on unlocked cards (`playSafeAccomm`).  No downstream users
existed.

The proof decomposes over the accommodation play (each move is a
`pileStack` or a `stackPile`): each step preserves WF (`apply_wf`) and
solvability (`solvable_of_accomm_step` — with the play's safety, every
`pileStack` unlocked), and the induction carries the winning play
through the shuffle. -/
private theorem solvable_accommodates_aux {st' : State} : ∀ (play : List Move),
    (∀ m ∈ play, m.isAccommodation = true) → ∀ (st : State),
    st.WF → st.solvableFrom → playSafeAccomm st play →
    st.run play = some st' → st'.solvableFrom := by
  intro play
  induction play with
  | nil =>
      intro _hall st _hwf hsol _hsafe hrun
      have hst : st = st' := Option.some.inj hrun
      subst hst
      exact hsol
  | cons m ms ih =>
      intro hall st hwf hsol hsafe hrun
      obtain ⟨hnl, hsafe2⟩ := hsafe
      simp only [State.run] at hrun
      cases hm : st.apply m with
      | none =>
          rw [hm] at hrun
          simp at hrun
      | some s₂ =>
          rw [hm] at hrun
          have hrun₂ : s₂.run ms = some st' := hrun
          have hs₂ := solvable_of_accomm_step hwf hm hsol (hall m (by simp)) hnl
          have hsafe' : playSafeAccomm s₂ ms := by
            have hgs : (st.apply m).getD st = s₂ := by rw [hm]; rfl
            rw [hgs] at hsafe2
            exact hsafe2
          exact ih (fun m' hm' => hall m' (by simp [hm'])) s₂
            (apply_wf hwf m s₂ hm) hs₂ hsafe' hrun₂

theorem solvable_accommodates {st st' : State} (hwf : st.WF)
    (hacc : safeAccommodates st st') (hsol : st.solvableFrom) : st'.solvableFrom := by
  obtain ⟨play, hrun, hall, hsafe⟩ := hacc
  exact solvable_accommodates_aux play hall st hwf hsol hsafe hrun

/-! ## 4. Structure — the matching is a forest

STATEMENT REPAIR (2026-09-13, prover-confirmed witness
`Temp\opencode\AboveIrreflWitness.lean`, axiom-clean): the staged
grading — everything above a card is strictly lower rank, hence
acyclicity, from `WF` alone — is FALSE.  `board_edges` admits
deal-adjacency edges, and the deal stacks arbitrarily, so a
deal-adjacency edge can invert a `canSitOn` edge between the same two
cards.  Witness: pile p1 dealt `[♥5, ♠6]` fully revealed, board
`inr ♥5 ↦ ♠6` (deal-adjacency, base visible) and `inr ♠6 ↦ ♥5`
(`canSitOn ♥5 ♠6`: 5+1=6, colors differ) — the state is WF, and
`aboveOf ♥5 = [♥5, ♠6]` contains `♥5`.  Longer alternating cycles
(deal-adjacency and canSitOn edges alternating across two piles, e.g.
`♥5 ↦ ♦9 ↦ ♣8 ↦ ♠6 ↦ ♥5` with the first and third edges deal-adjacent)
defeat every per-edge or global-deal-order repair: the acyclicity is
genuinely historical (which edge was attached last), not a state-only
consequence of the edge predicates.

The defensible acyclicity — the original design intent — is the
*forest potential*: a strictly decreasing measure along the matching's
card-edges.  Every play from `State.initial` maintains one (the deal's
own chains grade by within-pile position; every attach renumbers the
moved tree below its new base — the self-landing guard makes the trees
disjoint; reveal shifts the boundary into the gap) — that
play-induction is a later wave's item; here the potential is the
hypothesis, and the grading + acyclicity follow from it.
-/

/-- The forest potential: `φ` strictly decreases along every
card-to-card edge of the matching (`topOf (inr c) = some y` — `y` sits
on `c`).  The state-only shadow of play-reachability: WF alone does
not imply it (see the section note); every state reachable from
`State.initial` admits one. -/
def State.board_forest (st : State) : Prop :=
  ∃ φ : Card → Nat, ∀ c y, st.board.topOf (Sum.inr c) = some y → φ y < φ c

/-- The grading, rescoped: along the run above `c`, every card is
strictly below `c` in the forest potential (the staged rank-form is
false — deals stack arbitrarily; see the section note). -/
theorem aboveOf_rank_grading {st : State} (hwf : st.WF) {φ : Card → Nat}
    (hφ : ∀ c y, st.board.topOf (Sum.inr c) = some y → φ y < φ c) (c : Card) :
    ∀ d ∈ st.board.aboveOf c, φ d < φ c := by
  have := hwf
  have main : ∀ (fuel : Nat) (x : Card) (acc : List Card),
      (∀ z ∈ acc, φ z < φ c) → (φ x < φ c ∨ x = c) →
        ∀ d ∈ Board.aboveOf.go st.board fuel (Sum.inr x) acc, φ d < φ c := by
    intro fuel
    induction fuel with
    | zero =>
        intro x acc hacc _ d hd
        have hd' : d ∈ acc := hd
        exact hacc d hd'
    | succ f ih =>
        intro x acc hacc hx d hd
        rw [aboveOf_go_succ] at hd
        cases ht : st.board.topOf (Sum.inr x) with
        | none =>
            rw [ht] at hd
            have hd' : d ∈ acc := hd
            exact hacc d hd'
        | some y =>
            rw [ht] at hd
            have hd' : d ∈ (if acc.contains y then acc
                else Board.aboveOf.go st.board f (Sum.inr y) (y :: acc)) := hd
            by_cases hcy : acc.contains y = true
            · rw [if_pos hcy] at hd'
              exact hacc d hd'
            · rw [if_neg hcy] at hd'
              have hxy : φ y < φ x := hφ x y ht
              have hyc : φ y < φ c := by
                rcases hx with h | h
                · omega
                · exact h ▸ hxy
              refine ih y (y :: acc) (fun z hz => ?_) (Or.inl hyc) d hd'
              rcases List.mem_cons.mp hz with rfl | hz'
              · exact hyc
              · exact hacc z hz'
  intro d hd
  exact main 52 c [] (by simp) (Or.inr rfl) d hd

/-- Acyclicity, from the grading: no card is above itself when the
matching admits a forest potential. -/
theorem aboveOf_irrefl {st : State} (hwf : st.WF) (hfor : st.board_forest) (c : Card) :
    c ∉ st.board.aboveOf c := by
  obtain ⟨φ, hφ⟩ := hfor
  have hgr := aboveOf_rank_grading hwf hφ c
  intro hmem
  exact absurd (hgr c hmem) (Nat.lt_irrefl _)

/-! ## 5. The deck integration — the jump IS the physical game

The Draw commitments (`applyDrawTo`, `applyDrawStackTo`) are the
derived jumps; these are the statements that the guard makes them
exactly the physical game: jump-then-play ≡ deal-until-then-play.
C9's premise, as theorems, at every draw step (at step 1 the guard is
trivial — `reachablePos_step1`).  The bridge to `toEngine_simulates`
consumes these. -/

/-! ### The deal-iteration kit — the jump-soundness machinery

`Cycle.dealIter` is `k` deals (Macro.lean's `Cycle.dealN` restated —
this file cannot import Macro), with the orbit correspondence: → every
accessible position is dealt to (`dealReach_maskPos`), ← every cursor
the chain reaches lands in the original mask (`dealIter_orbit` +
`dealIter_mask`), which with `stock_wf`'s duplicate-freeness pins the
position. -/

/-- `k` deals from `cy`. -/
def Cycle.dealIter (s : Nat) : Nat → Cycle Card → Cycle Card
  | 0, cy => cy
  | k + 1, cy => dealOnce s (dealIter s k cy)

theorem Cycle.dealIter_zero (s : Nat) (cy : Cycle Card) : dealIter s 0 cy = cy := rfl

theorem Cycle.dealIter_succ (s : Nat) (k : Nat) (cy : Cycle Card) :
    dealIter s (k + 1) cy = dealOnce s (dealIter s k cy) := rfl

theorem Cycle.dealIter_one (s : Nat) (cy : Cycle Card) :
    dealIter s 1 cy = dealOnce s cy := rfl

theorem Cycle.dealIter_add (s : Nat) : ∀ (k j : Nat) (cy : Cycle Card),
    dealIter s (k + j) cy = dealIter s k (dealIter s j cy) := by
  intro k
  induction k with
  | zero => intro j cy; rw [Nat.zero_add, dealIter_zero]
  | succ k ih =>
    intro j cy
    rw [Nat.succ_add, dealIter_succ, dealIter_succ, ih]

theorem Cycle.dealIter_shift (s : Nat) : ∀ (k : Nat) (cy : Cycle Card),
    dealIter s k (dealOnce s cy) = dealOnce s (dealIter s k cy) := by
  intro k
  induction k with
  | zero => intro cy; rfl
  | succ k ih => intro cy; rw [dealIter_succ, ih, ← dealIter_succ]

theorem Cycle.dealIter_cards (s : Nat) : ∀ (k : Nat) (cy : Cycle Card),
    (dealIter s k cy).cards = cy.cards := by
  intro k
  induction k with
  | zero => intro cy; rfl
  | succ k ih => intro cy; rw [dealIter_succ, Cycle.dealOnce_cards, ih]

theorem dealIter_cards' (s : Nat) (k : Nat) (l : List Card) (c₀ : Nat) :
    (Cycle.dealIter s k ⟨l, c₀⟩).cards = l :=
  Cycle.dealIter_cards s k ⟨l, c₀⟩

theorem jump_mul_mod (k s : Nat) : k * s % s = 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.succ_mul, Nat.add_mod, ih, Nat.mod_self, Nat.zero_add, Nat.zero_mod]

theorem jump_mul_sub_mod (k s : Nat) : (k * s - s) % s = 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h1 : (k + 1) * s = k * s + s := by rw [Nat.add_mul, Nat.one_mul]
    rw [h1, Nat.add_sub_cancel]
    exact jump_mul_mod k s

theorem jump_exists_mul {a s : Nat} (hmod : a % s = 0) : ∃ q, a = q * s := by
  refine ⟨a / s, ?_⟩
  have hdiv := Nat.div_add_mod a s
  rw [hmod, Nat.add_zero] at hdiv
  rw [Nat.mul_comm]
  exact hdiv.symm

theorem le_mul_self {j s : Nat} (hj : 1 ≤ j) : s ≤ j * s := by
  have h1 : j - 1 + 1 = j := by omega
  rw [← h1, Nat.add_mul, Nat.one_mul]
  exact Nat.le_add_left s ((j - 1) * s)

/-- One deal from the pass end (or past it) wraps to 0. -/
theorem dealOnce_wrap (s : Nat) (l : List Card) (κ : Nat) (hκ : κ ≥ l.length) :
    (Cycle.dealOnce s ⟨l, κ⟩).cursor = 0 := by
  show (if κ ≥ l.length then (⟨l, 0⟩ : Cycle Card)
      else ⟨l, min (κ + s) l.length⟩).cursor = 0
  rw [if_pos hκ]

/-- One deal below the pass end clamps at `min (κ + s)`. -/
theorem dealOnce_step (s : Nat) (l : List Card) (κ : Nat) (hκ : ¬(κ ≥ l.length)) :
    (Cycle.dealOnce s ⟨l, κ⟩).cursor = min (κ + s) l.length := by
  show (if κ ≥ l.length then (⟨l, 0⟩ : Cycle Card)
      else ⟨l, min (κ + s) l.length⟩).cursor = min (κ + s) l.length
  rw [if_neg hκ]

theorem dealIter_cursor_le (s : Nat) : ∀ (k : Nat) (cy : Cycle Card),
    cy.cursor ≤ cy.cards.length → (Cycle.dealIter s k cy).cursor ≤ cy.cards.length := by
  intro k
  induction k with
  | zero => intro cy h; exact h
  | succ f ih =>
    intro cy h
    by_cases hguard : (Cycle.dealIter s f cy).cursor ≥ (Cycle.dealIter s f cy).cards.length
    · rw [Cycle.dealIter_succ, dealOnce_wrap s _ _ hguard]
      exact Nat.zero_le _
    · rw [Cycle.dealIter_succ, dealOnce_step s _ _ hguard, Cycle.dealIter_cards]
      exact Nat.min_le_right _ _

/-- The orbit form: every cursor the deal chain reaches is either on
the first pass from `c₀` (`c₀ + m·s`, clamped at the length) or on a
fresh pass (`j·s`, clamped). -/
theorem dealIter_orbit (s : Nat) : ∀ (k : Nat) (l : List Card) (c₀ : Nat),
    c₀ ≤ l.length →
    (∃ m, (Cycle.dealIter s k ⟨l, c₀⟩).cursor = min (c₀ + m * s) l.length)
      ∨ (∃ j, (Cycle.dealIter s k ⟨l, c₀⟩).cursor = min (j * s) l.length) := by
  intro k
  induction k with
  | zero =>
    intro l c₀ hle
    refine Or.inl ⟨0, ?_⟩
    rw [Cycle.dealIter_zero, Nat.zero_mul, Nat.add_zero, Nat.min_eq_left hle]
  | succ f ih =>
    intro l c₀ hle
    obtain hc | hc := ih l c₀ hle
    · obtain ⟨m, hm⟩ := hc
      by_cases hsat : l.length ≤ c₀ + m * s
      · refine Or.inr ⟨0, ?_⟩
        have hκn : (Cycle.dealIter s f ⟨l, c₀⟩).cursor = l.length := by
          rw [hm, Nat.min_eq_right hsat]
        have hguard : (Cycle.dealIter s f ⟨l, c₀⟩).cursor
            ≥ (Cycle.dealIter s f ⟨l, c₀⟩).cards.length := by
          rw [hκn, dealIter_cards']
          omega
        rw [Cycle.dealIter_succ, Nat.zero_mul, Nat.min_eq_left (Nat.zero_le l.length),
          dealOnce_wrap s _ _ hguard]
      · refine Or.inl ⟨m + 1, ?_⟩
        have hκc : (Cycle.dealIter s f ⟨l, c₀⟩).cursor = c₀ + m * s := by
          rw [hm, Nat.min_eq_left (by omega)]
        have hguard : ¬((Cycle.dealIter s f ⟨l, c₀⟩).cursor
            ≥ (Cycle.dealIter s f ⟨l, c₀⟩).cards.length) := by
          rw [hκc, dealIter_cards']
          omega
        have hexp : c₀ + (m + 1) * s = c₀ + m * s + s := by
          rw [Nat.add_mul, Nat.one_mul]; omega
        rw [Cycle.dealIter_succ, dealOnce_step s _ _ hguard, hκc, dealIter_cards', hexp]
    · obtain ⟨j, hj⟩ := hc
      by_cases hsat : l.length ≤ j * s
      · refine Or.inr ⟨0, ?_⟩
        have hκn : (Cycle.dealIter s f ⟨l, c₀⟩).cursor = l.length := by
          rw [hj, Nat.min_eq_right hsat]
        have hguard : (Cycle.dealIter s f ⟨l, c₀⟩).cursor
            ≥ (Cycle.dealIter s f ⟨l, c₀⟩).cards.length := by
          rw [hκn, dealIter_cards']
          omega
        rw [Cycle.dealIter_succ, Nat.zero_mul, Nat.min_eq_left (Nat.zero_le l.length),
          dealOnce_wrap s _ _ hguard]
      · refine Or.inr ⟨j + 1, ?_⟩
        have hκc : (Cycle.dealIter s f ⟨l, c₀⟩).cursor = j * s := by
          rw [hj, Nat.min_eq_left (by omega)]
        have hguard : ¬((Cycle.dealIter s f ⟨l, c₀⟩).cursor
            ≥ (Cycle.dealIter s f ⟨l, c₀⟩).cards.length) := by
          rw [hκc, dealIter_cards']
          omega
        have hexp : (j + 1) * s = j * s + s := by rw [Nat.add_mul, Nat.one_mul]
        rw [Cycle.dealIter_succ, dealOnce_step s _ _ hguard, hκc, dealIter_cards', hexp]

/-- The current-pass advance: `q` deals from `c` land exactly at
`c + q·s` within the length (no clamp, no wrap). -/
theorem dealChain_add {s : Nat} (hs : 0 < s) (l : List Card) :
    ∀ (q c : Nat), c + q * s ≤ l.length →
      Cycle.dealIter s q ⟨l, c⟩ = ⟨l, c + q * s⟩ := by
  intro q
  induction q with
  | zero => intro c _; rw [Nat.zero_mul, Nat.add_zero]; rfl
  | succ q ih =>
    intro c hle
    have hexp : (q + 1) * s = q * s + s := by rw [Nat.add_mul, Nat.one_mul]
    rw [hexp] at hle
    have hstep : Cycle.dealOnce s ⟨l, c⟩ = ⟨l, c + s⟩ := by
      show (if c ≥ l.length then (⟨l, 0⟩ : Cycle Card) else ⟨l, min (c + s) l.length⟩)
          = (⟨l, c + s⟩ : Cycle Card)
      rw [if_neg (by omega), Nat.min_eq_left (by omega)]
    rw [Cycle.dealIter_succ, ← Cycle.dealIter_shift, hstep, ih (c + s) (by omega), hexp]
    exact congrArg (Cycle.mk l) (by omega)

/-- Every cursor reaches the pass end: the chain of clamped deals. -/
theorem dealChain_to_end {s : Nat} (hs : 0 < s) (l : List Card) :
    ∀ (d c : Nat), c ≤ l.length → l.length - c ≤ d →
      ∃ k, Cycle.dealIter s k ⟨l, c⟩ = ⟨l, l.length⟩ := by
  intro d
  induction d with
  | zero =>
    intro c _ hd
    have hc : c = l.length := by omega
    subst hc
    exact ⟨0, rfl⟩
  | succ d ih =>
    intro c _ hd
    by_cases hc : c = l.length
    · subst hc; exact ⟨0, rfl⟩
    · by_cases hcs : c + s < l.length
      · have hstep : Cycle.dealOnce s ⟨l, c⟩ = ⟨l, c + s⟩ := by
          show (if c ≥ l.length then (⟨l, 0⟩ : Cycle Card) else ⟨l, min (c + s) l.length⟩)
              = (⟨l, c + s⟩ : Cycle Card)
          rw [if_neg (by omega), Nat.min_eq_left (by omega)]
        obtain ⟨k, hk⟩ := ih (c + s) (by omega) (by omega)
        refine ⟨k + 1, ?_⟩
        rw [Cycle.dealIter_succ, ← Cycle.dealIter_shift, hstep]
        exact hk
      · have hstep : Cycle.dealOnce s ⟨l, c⟩ = ⟨l, l.length⟩ := by
          show (if c ≥ l.length then (⟨l, 0⟩ : Cycle Card) else ⟨l, min (c + s) l.length⟩)
              = (⟨l, l.length⟩ : Cycle Card)
          rw [if_neg (by omega), Nat.min_eq_right (by omega)]
        exact ⟨1, hstep⟩

/-- The pass end is reached from any cursor, even past it (one wrap). -/
theorem dealChain_to_end_any {s : Nat} (hs : 0 < s) (l : List Card) (c : Nat) :
    ∃ k, Cycle.dealIter s k ⟨l, c⟩ = ⟨l, l.length⟩ := by
  by_cases hcl : c ≤ l.length
  · exact dealChain_to_end hs l (l.length - c) c hcl (by omega)
  · have hwrap : Cycle.dealOnce s ⟨l, c⟩ = ⟨l, 0⟩ := by
      show (if c ≥ l.length then (⟨l, 0⟩ : Cycle Card) else ⟨l, min (c + s) l.length⟩)
          = (⟨l, 0⟩ : Cycle Card)
      rw [if_pos (by omega : c ≥ l.length)]
    obtain ⟨k₀, hk₀⟩ := dealChain_to_end hs l l.length 0 (Nat.zero_le _) (by omega)
    refine ⟨k₀ + 1, ?_⟩
    rw [Cycle.dealIter_succ, ← Cycle.dealIter_shift, hwrap, hk₀]

/-- The wrapped advance: reach the pass end, wrap to 0, then climb to
`i + 1` on the batch-top lane. -/
theorem dealChain_wrap {s : Nat} (hs : 0 < s) (l : List Card) (c i : Nat)
    (hlt : i < l.length) (hle : s - 1 ≤ i) (hmod : (i - (s - 1)) % s = 0) :
    ∃ k, Cycle.dealIter s k ⟨l, c⟩ = ⟨l, i + 1⟩ := by
  obtain ⟨k₀, hk₀⟩ := dealChain_to_end_any hs l c
  have hwrap : Cycle.dealOnce s ⟨l, l.length⟩ = ⟨l, 0⟩ := by
    show (if l.length ≥ l.length then (⟨l, 0⟩ : Cycle Card)
        else ⟨l, min (l.length + s) l.length⟩) = (⟨l, 0⟩ : Cycle Card)
    rw [if_pos (Nat.le_refl l.length)]
  obtain ⟨q, hq⟩ := jump_exists_mul hmod
  have hexp : (q + 1) * s = q * s + s := by rw [Nat.add_mul, Nat.one_mul]
  have hadv : 0 + (q + 1) * s ≤ l.length := by rw [hexp]; omega
  have hlast : 0 + (q + 1) * s = i + 1 := by rw [hexp]; omega
  refine ⟨(q + 1) + (1 + k₀), ?_⟩
  have hcomp1 : Cycle.dealIter s (1 + k₀) ⟨l, c⟩
      = Cycle.dealOnce s (Cycle.dealIter s k₀ ⟨l, c⟩) := by
    rw [Cycle.dealIter_add, Cycle.dealIter_one]
  have hcomp2 : Cycle.dealIter s ((q + 1) + (1 + k₀)) ⟨l, c⟩
      = Cycle.dealIter s (q + 1) (Cycle.dealOnce s (Cycle.dealIter s k₀ ⟨l, c⟩)) := by
    rw [Cycle.dealIter_add, hcomp1]
  rw [hcomp2, hk₀, hwrap, dealChain_add hs l (q + 1) 0 hadv, hlast]

/-- The deal-orbit correspondence, witness half: every accessible
position is dealt to — `dealIter` realizes the jump. -/
theorem dealReach_maskPos {s : Nat} (hs : 0 < s) {cy : Cycle Card} {i : Nat}
    (hlt : i < cy.cards.length) (hmem : i ∈ Pace.maskPos cy s hs) :
    ∃ k, Cycle.dealIter s k cy = { cy with cursor := i + 1 } := by
  rcases cy with ⟨l, c⟩
  show ∃ k, Cycle.dealIter s k ⟨l, c⟩ = ⟨l, i + 1⟩
  have hlt : i < l.length := hlt
  simp only [Pace.maskPos] at hmem
  rcases List.mem_append.mp hmem with h12 | h3
  · rcases List.mem_append.mp h12 with h1 | h2
    · obtain ⟨hle, hlt2, hmod⟩ := (Pace.laneUp_mem s hs _ _ i).mp h1
      by_cases hc0 : c = 0
      · subst hc0
        rw [if_pos rfl] at hle hmod
        exact dealChain_wrap hs l 0 i hlt hle hmod
      · rw [if_neg hc0] at hle hmod
        obtain ⟨q, hq⟩ := jump_exists_mul hmod
        have hle2 : c + q * s ≤ l.length := by omega
        have hkey : c + q * s = i + 1 := by omega
        refine ⟨q, ?_⟩
        rw [dealChain_add hs l q c hle2]
        exact congrArg (Cycle.mk l) hkey
    · rw [if_pos (by omega : 0 < l.length)] at h2
      simp only [List.mem_singleton] at h2
      obtain ⟨k, hk⟩ := dealChain_to_end_any hs l c
      refine ⟨k, ?_⟩
      rw [hk]
      exact congrArg (Cycle.mk l) (by omega)
  · obtain ⟨hle, -, hmod⟩ := (Pace.laneUp_mem s hs _ _ i).mp h3
    exact dealChain_wrap hs l c i hlt hle hmod

/-- `maskPos`, lane 1: the leading lane from the cursor's waste top. -/
theorem maskPos_lane1_mem {α : Type} {l : List α} {c₀ s : Nat} (hs : 0 < s) {p : Nat}
    (hle : (if c₀ = 0 then s - 1 else c₀ - 1) ≤ p)
    (hlt : p < l.length - 1)
    (hmod : (p - (if c₀ = 0 then s - 1 else c₀ - 1)) % s = 0) :
    p ∈ Pace.maskPos ⟨l, c₀⟩ s hs := by
  have h : p ∈ Pace.laneUp s hs (if c₀ = 0 then s - 1 else c₀ - 1) (l.length - 1) :=
    (Pace.laneUp_mem s hs _ _ p).mpr ⟨hle, hlt, hmod⟩
  show p ∈ (Pace.laneUp s hs _ (l.length - 1)
    ++ (if 0 < l.length then [l.length - 1] else [])
    ++ Pace.laneUp s hs (s - 1)
        ((if c₀ % s != 0 then l.length else c₀) - 1))
  simp only [List.mem_append]
  exact Or.inl (Or.inl h)

/-- `maskPos`, lane 2: the batch-top lane below the wrap end. -/
theorem maskPos_lane2_mem {α : Type} {l : List α} {c₀ s : Nat} (hs : 0 < s) {p : Nat}
    (hle : s - 1 ≤ p)
    (hlt : p < (if c₀ % s != 0 then l.length else c₀) - 1)
    (hmod : (p - (s - 1)) % s = 0) :
    p ∈ Pace.maskPos ⟨l, c₀⟩ s hs := by
  have h : p ∈ Pace.laneUp s hs (s - 1) ((if c₀ % s != 0 then l.length else c₀) - 1) :=
    (Pace.laneUp_mem s hs _ _ p).mpr ⟨hle, hlt, hmod⟩
  show p ∈ (Pace.laneUp s hs _ (l.length - 1)
    ++ (if 0 < l.length then [l.length - 1] else [])
    ++ Pace.laneUp s hs (s - 1)
        ((if c₀ % s != 0 then l.length else c₀) - 1))
  simp only [List.mem_append]
  exact Or.inr h

/-- `maskPos`, the last card (the pass-end saturation). -/
theorem maskPos_last_mem {α : Type} {l : List α} {c₀ s : Nat} (hs : 0 < s)
    (hn : 0 < l.length) : l.length - 1 ∈ Pace.maskPos ⟨l, c₀⟩ s hs := by
  show l.length - 1 ∈ (Pace.laneUp s hs _ (l.length - 1)
    ++ (if 0 < l.length then [l.length - 1] else [])
    ++ Pace.laneUp s hs (s - 1) _)
  rw [if_pos hn]
  simp only [List.mem_append]
  exact Or.inl (Or.inr (List.mem_singleton.mpr rfl))

/-- The orbit lands in the mask: every cursor the deal chain reaches
(other than a fresh 0) exposes, at `κ - 1`, a position of the
*original* cycle's accessible set. -/
theorem dealIter_mask {s : Nat} (hs : 0 < s) {l : List Card} {c₀ κ : Nat}
    (hcur : c₀ ≤ l.length) (hκ : κ ≤ l.length) (h0 : κ ≠ 0)
    (hform : (∃ m, κ = min (c₀ + m * s) l.length) ∨ (∃ j, κ = min (j * s) l.length)) :
    κ - 1 ∈ Pace.maskPos ⟨l, c₀⟩ s hs := by
  have := hκ
  have := hcur
  rcases hform with ⟨m, hm⟩ | ⟨j, hj⟩
  · by_cases hsat : l.length ≤ c₀ + m * s
    · have hκn : κ = l.length := by rw [hm, Nat.min_eq_right hsat]
      rw [hκn]
      exact maskPos_last_mem hs (by omega)
    · rw [hm, Nat.min_eq_left (by omega)]
      rcases Nat.eq_zero_or_pos m with rfl | hm0
      · have hc0 : c₀ ≠ 0 := by omega
        refine maskPos_lane1_mem hs ?_ ?_ ?_
        · rw [if_neg hc0]; omega
        · omega
        · rw [if_neg hc0]
          rw [show c₀ + 0 * s - 1 - (c₀ - 1) = 0 from by omega, Nat.zero_mod]
      · have hsle : s ≤ m * s := le_mul_self (by omega)
        by_cases hc0 : c₀ = 0
        · subst hc0
          refine maskPos_lane1_mem hs ?_ ?_ ?_
          · rw [if_pos rfl]
            omega
          · omega
          · rw [if_pos rfl]
            have hsub : 0 + m * s - 1 - (s - 1) = m * s - s := by omega
            rw [hsub]
            exact jump_mul_sub_mod m s
        · refine maskPos_lane1_mem hs ?_ ?_ ?_
          · rw [if_neg hc0]; omega
          · omega
          · rw [if_neg hc0]
            have hsub : c₀ + m * s - 1 - (c₀ - 1) = m * s := by omega
            rw [hsub]
            exact jump_mul_mod m s
  · rcases Nat.eq_zero_or_pos j with rfl | hj0
    · have hκ0 : κ = 0 := by
        rw [hj, Nat.zero_mul, Nat.min_eq_left (Nat.zero_le l.length)]
      exact absurd hκ0 h0
    · have hsle : s ≤ j * s := le_mul_self (by omega)
      by_cases hsat : l.length ≤ j * s
      · have hκn : κ = l.length := by rw [hj, Nat.min_eq_right hsat]
        rw [hκn]
        exact maskPos_last_mem hs (by omega)
      · rw [hj, Nat.min_eq_left (by omega)]
        rcases Nat.eq_zero_or_pos (c₀ % s) with hmod0 | hpos
        · have hne : ¬((c₀ % s != 0) = true) := by
            rw [hmod0]
            simp
          by_cases hbelow : j * s - 1 < c₀ - 1
          · refine maskPos_lane2_mem hs ?_ ?_ ?_
            · show s - 1 ≤ j * s - 1
              omega
            · rw [if_neg hne]; omega
            · have hsub : j * s - 1 - (s - 1) = j * s - s := by omega
              rw [hsub]
              exact jump_mul_sub_mod j s
          · by_cases hc0 : c₀ = 0
            · subst hc0
              refine maskPos_lane1_mem hs ?_ ?_ ?_
              · rw [if_pos rfl]
                omega
              · omega
              · rw [if_pos rfl]
                have hsub : j * s - 1 - (s - 1) = j * s - s := by omega
                rw [hsub]
                exact jump_mul_sub_mod j s
            · obtain ⟨q, hq⟩ := jump_exists_mul hmod0
              refine maskPos_lane1_mem hs ?_ ?_ ?_
              · rw [if_neg hc0]; omega
              · omega
              · rw [if_neg hc0]
                have hsub : j * s - 1 - (c₀ - 1) = j * s - c₀ := by omega
                rw [hsub, hq, ← Nat.sub_mul]
                exact jump_mul_mod (j - q) s
        · have hres : (c₀ % s != 0) = true := by simp [Nat.ne_of_gt hpos]
          refine maskPos_lane2_mem hs ?_ ?_ ?_
          · show s - 1 ≤ j * s - 1
            omega
          · rw [if_pos hres]; omega
          · have hsub : j * s - 1 - (s - 1) = j * s - s := by omega
            rw [hsub]
            exact jump_mul_sub_mod j s

/-- A found position points at the card. -/
theorem posOf_get {c : Card} : ∀ (l : List Card) (cur i : Nat),
    Cycle.posOf c ⟨l, cur⟩ = some i → l[i]? = some c := by
  intro l
  induction l with
  | nil => intro cur i h; simp [Cycle.posOf, Cycle.findFirstIdx] at h
  | cons a t ih =>
    intro cur i h
    simp only [Cycle.posOf, Cycle.findFirstIdx] at h
    by_cases ha : a = c
    · rw [if_pos (decide_eq_true ha), Option.some.injEq] at h
      subst h
      rw [ha]
      rfl
    · rw [if_neg (fun hcon => ha (of_decide_eq_true hcon))] at h
      cases hf : Cycle.findFirstIdx (fun c' => decide (c' = c)) t with
      | none => rw [hf] at h; simp at h
      | some j =>
        rw [hf, Option.map_some, Option.some.injEq] at h
        subst h
        rw [List.getElem?_cons_succ]
        exact ih 0 j hf

/-- Running a pure-deal play lands on the iterated deal. -/
theorem run_dealIter : ∀ (k : Nat) (st : State),
    st.run (List.replicate k Move.draw) =
      some { st with stock := Cycle.dealIter st.drawStep k st.stock } := by
  intro k
  induction k with
  | zero => intro st; rfl
  | succ f ih =>
    intro st
    rw [List.replicate_succ, State.run,
      show st.apply Move.draw =
        some { st with stock := Cycle.dealOnce st.drawStep st.stock } from rfl]
    show ({ st with stock := Cycle.dealOnce st.drawStep st.stock } : State).run
        (List.replicate f Move.draw) = _
    rw [ih { st with stock := Cycle.dealOnce st.drawStep st.stock }]
    show some { st with stock := Cycle.dealIter st.drawStep f (Cycle.dealOnce st.drawStep st.stock) }
       = some { st with stock := Cycle.dealIter st.drawStep (f + 1) st.stock }
    rw [Cycle.dealIter_shift, Cycle.dealIter_succ]

/-- A full pass plus the wrap deal returns to the pass start: from
cursor 0, dealing everything (the clamp passes the last card) and
wrapping lands home — the deal cycle's period is `⌈n/s⌉ + 1`, at any
step `s ≥ 1` (deck.rs `offset`'s periodicity).  Supersedes the old
rotate-form "a full rotation is the identity", an artifact of the
jump semantics.

Route: `run_dealIter` unpacks the play; `q = (n+s-1)/s` is exactly
`⌈n/s⌉` (`q·s ≥ n` and `d·s ≥ n → d ≥ q`, both from
`Nat.div_add_mod` + `Nat.mod_lt`), so `d ≤ q` deals from cursor 0 stay
on the first pass at `min (d·s, n)` (the induction's step needs
`d·s < n`, i.e. minimality), the `q`-th deal clamps at `n`, and the
wrap deal returns to `0` — the stock, and with it the state, is
unchanged. -/
theorem draw_full_pass {st : State} (hc : st.stock.cursor = 0)
    (hs : 0 < st.drawStep) {st' : State}
    (h : st.run (List.replicate
        ((st.stock.cards.length + st.drawStep - 1) / st.drawStep + 1) Move.draw)
      = some st') :
    st' = st := by
  obtain ⟨K, hK⟩ : ∃ K, (st.stock.cards.length + st.drawStep - 1) / st.drawStep + 1 = K :=
    ⟨_, rfl⟩
  rw [hK] at h
  rw [run_dealIter] at h
  have hst' : { st with stock := Cycle.dealIter st.drawStep K st.stock } = st' :=
    Option.some.inj h
  rw [← hst']
  refine state_ext rfl rfl rfl rfl ?_ rfl
  cases hst : st.stock with
  | mk l c =>
    rw [hst] at hc hK
    have hc' : c = 0 := hc
    subst hc'
    have hK' : (l.length + st.drawStep - 1) / st.drawStep + 1 = K := hK
    obtain ⟨q, hqdef⟩ : ∃ q, (l.length + st.drawStep - 1) / st.drawStep = q := ⟨_, rfl⟩
    have hKq : K = q + 1 := by rw [← hK', hqdef]
    rw [hKq]
    have hdm := Nat.div_add_mod (l.length + st.drawStep - 1) st.drawStep
    rw [Nat.mul_comm, hqdef] at hdm
    have hmlt := Nat.mod_lt (l.length + st.drawStep - 1) hs
    have hqge : l.length ≤ q * st.drawStep := by omega
    have hqmin : ∀ d : Nat, l.length ≤ d * st.drawStep → q ≤ d := by
      intro d hd
      rcases Nat.lt_or_ge d q with hlt | hge
      · exfalso
        have hmono : (d + 1) * st.drawStep ≤ q * st.drawStep :=
          Nat.mul_le_mul (by omega) (Nat.le_refl _)
        have hexp : (d + 1) * st.drawStep = d * st.drawStep + st.drawStep := by
          rw [Nat.add_mul, Nat.one_mul]
        omega
      · exact hge
    have main : ∀ d : Nat, d ≤ q →
        Cycle.dealIter st.drawStep d ⟨l, 0⟩ = ⟨l, min (d * st.drawStep) l.length⟩ := by
      intro d
      induction d with
      | zero =>
          intro _
          show (⟨l, 0⟩ : Cycle Card) = ⟨l, min (0 * st.drawStep) l.length⟩
          rw [Nat.zero_mul, Nat.min_eq_left (Nat.zero_le _)]
      | succ d ih =>
          intro hd
          have hdlt : d * st.drawStep < l.length := by
            by_cases hbig : l.length ≤ d * st.drawStep
            · exact absurd (hqmin d hbig) (by omega)
            · omega
          rw [Cycle.dealIter_succ, ih (by omega)]
          rw [Nat.min_eq_left (by omega : d * st.drawStep ≤ l.length)]
          show (if d * st.drawStep ≥ l.length then (⟨l, 0⟩ : Cycle Card)
              else ⟨l, min (d * st.drawStep + st.drawStep) l.length⟩)
            = ⟨l, min ((d + 1) * st.drawStep) l.length⟩
          rw [if_neg (by omega : ¬ (d * st.drawStep ≥ l.length)), Nat.add_mul, Nat.one_mul]
    have hpass : Cycle.dealIter st.drawStep q ⟨l, 0⟩ = ⟨l, l.length⟩ := by
      rw [main q (Nat.le_refl q), Nat.min_eq_right hqge]
    rw [Cycle.dealIter_succ, hpass]
    show (if l.length ≥ l.length then (⟨l, 0⟩ : Cycle Card)
        else ⟨l, min (l.length + st.drawStep) l.length⟩) = ⟨l, 0⟩
    rw [if_pos (Nat.le_refl l.length)]

/-- `reachablePos`, introduction form. -/
theorem reachablePos_intro {st : State} {c : Card} {i : Nat} (hs : 0 < st.drawStep)
    (hpos : st.stock.posOf c = some i) (hmem : i ∈ Pace.maskPos st.stock st.drawStep hs) :
    st.reachablePos c = some i := by
  simp only [State.reachablePos, dif_pos hs, hpos, if_pos hmem]

/-- The tableau deck move after the deals brought `c` to the top. -/
theorem deckPile_after_deals {st : State} {c : Card} {b : Base} {i : Nat} {bd : Board}
    (hget : st.stock.cards[i]? = some c) (hcan : st.canPlace c b = true)
    (hatt : st.board.attach b c = some bd) :
    ({ st with stock := { st.stock with cursor := i + 1 } }).apply (Move.deckPile c b)
      = some { st with board := bd, stock := (st.stock.drawTo i).removeAt i } := by
  have hprev : ({ st with stock := { st.stock with cursor := i + 1 } } : State).stock.prev
      = some c := by
    show (Cycle.prev { st.stock with cursor := i + 1 }) = some c
    show (if i + 1 = 0 then none else st.stock.cards[i + 1 - 1]?) = some c
    rw [if_neg (by omega : ¬ (i + 1 = 0))]
    have hi : i + 1 - 1 = i := by omega
    rw [hi]
    exact hget
  have e1 : (({ st with stock := { st.stock with cursor := i + 1 } } : State).stock.cursor - 1)
      = i := by
    show i + 1 - 1 = i
    omega
  have e2 : ({ st with stock := { st.stock with cursor := i + 1 } } : State).stock
      = { st.stock with cursor := i + 1 } := rfl
  have e3 : st.stock.drawTo i = { st.stock with cursor := i + 1 } := rfl
  refine (apply_deckPile_iff).mpr ⟨hprev, hcan, bd, hatt, ?_⟩
  rw [e1, e2, e3]

/-- The stack deck move after the deals. -/
theorem deckStack_after_deals {st : State} {c : Card} {i : Nat}
    (hget : st.stock.cards[i]? = some c) (hrank : c.rank.toIdx = st.heights c.suit) :
    ({ st with stock := { st.stock with cursor := i + 1 } }).apply (Move.deckStack c)
      = some { st with
        stock := (st.stock.drawTo i).removeAt i,
        heights := fun s => if s = c.suit then st.heights s + 1 else st.heights s } := by
  have hprev : ({ st with stock := { st.stock with cursor := i + 1 } } : State).stock.prev
      = some c := by
    show (Cycle.prev { st.stock with cursor := i + 1 }) = some c
    show (if i + 1 = 0 then none else st.stock.cards[i + 1 - 1]?) = some c
    rw [if_neg (by omega : ¬ (i + 1 = 0))]
    have hi : i + 1 - 1 = i := by omega
    rw [hi]
    exact hget
  have e1 : (({ st with stock := { st.stock with cursor := i + 1 } } : State).stock.cursor - 1)
      = i := by
    show i + 1 - 1 = i
    omega
  have e2 : ({ st with stock := { st.stock with cursor := i + 1 } } : State).stock
      = { st.stock with cursor := i + 1 } := rfl
  have e3 : st.stock.drawTo i = { st.stock with cursor := i + 1 } := rfl
  refine (apply_deckStack_iff).mpr ⟨hprev, hrank, ?_⟩
  show { st with
    stock := (st.stock.drawTo i).removeAt i,
    heights := fun s => if s = c.suit then st.heights s + 1 else st.heights s }
     = { st with
    stock := (({ st with stock := { st.stock with cursor := i + 1 } } : State).stock).removeAt
        ((({ st with stock := { st.stock with cursor := i + 1 } } : State).stock.cursor - 1)),
    heights := fun s => if s = c.suit
      then ({ st with stock := { st.stock with cursor := i + 1 } } : State).heights s + 1
      else ({ st with stock := { st.stock with cursor := i + 1 } } : State).heights s }
  rw [e1, e2, e3]

/-- `applyDrawStackTo`'s shape (the stack landing needs no canPlace:
its rank guard is `deckStack`'s own). -/
theorem applyDrawStackTo_shape {st : State} {c : Card} {st' : State} :
    st.applyDrawStackTo c = some st' ↔
      ∃ i, st.reachablePos c = some i ∧ c.rank.toIdx = st.heights c.suit ∧
        st' = { st with
          stock := (st.stock.drawTo i).removeAt i,
          heights := fun s => if s = c.suit then st.heights s + 1 else st.heights s } := by
  constructor
  · intro h
    simp only [State.applyDrawStackTo] at h
    cases hpos : st.reachablePos c with
    | none => rw [hpos] at h; simp at h
    | some i =>
      rw [hpos] at h
      have h' : (if c.rank.toIdx = st.heights c.suit then
          some { st with
            stock := (st.stock.drawTo i).removeAt i,
            heights := fun s => if s = c.suit then st.heights s + 1 else st.heights s }
          else none) = some st' := h
      by_cases hrk : c.rank.toIdx = st.heights c.suit
      · rw [if_pos hrk, Option.some.injEq] at h'
        exact ⟨i, rfl, hrk, h'.symm⟩
      · rw [if_neg hrk] at h'; simp at h'
  · intro ⟨i, hpos, hrk, hst⟩
    rw [hst]
    simp only [State.applyDrawStackTo, hpos, if_pos hrk]

/-- The ← direction's core, shared by both jump-soundness theorems:
a deck move after `k` deals implies the guard — the dealt card sits at
an accessible position, and the splice agrees with the jump's. -/
theorem dealIter_prev_reachable {st : State} (hwf : st.WF) {c : Card} {k : Nat}
    (hprev : (Cycle.dealIter st.drawStep k st.stock).prev = some c) :
    ∃ i, st.reachablePos c = some i ∧
      (Cycle.dealIter st.drawStep k st.stock).removeAt
          ((Cycle.dealIter st.drawStep k st.stock).cursor - 1)
        = (st.stock.drawTo i).removeAt i := by
  have hs : 0 < st.drawStep := hwf.step_pos
  have hcards : (Cycle.dealIter st.drawStep k st.stock).cards = st.stock.cards :=
    Cycle.dealIter_cards _ _ _
  have hκle : (Cycle.dealIter st.drawStep k st.stock).cursor ≤ st.stock.cards.length :=
    dealIter_cursor_le _ _ _ hwf.cursor_le
  simp only [Cycle.prev] at hprev
  split at hprev
  · exact absurd hprev (by simp)
  · rename_i hκ0
    have hκne : (Cycle.dealIter st.drawStep k st.stock).cursor ≠ 0 := hκ0
    rw [hcards] at hprev
    have hmem : (Cycle.dealIter st.drawStep k st.stock).cursor - 1
        ∈ Pace.maskPos st.stock st.drawStep hs := by
      obtain (⟨m, hm⟩ | ⟨j, hj⟩) :=
        dealIter_orbit _ k st.stock.cards st.stock.cursor hwf.cursor_le
      · exact dealIter_mask hs hwf.cursor_le hκle hκne (Or.inl ⟨m, hm⟩)
      · exact dealIter_mask hs hwf.cursor_le hκle hκne (Or.inr ⟨j, hj⟩)
    have hpos : st.stock.posOf c
        = some ((Cycle.dealIter st.drawStep k st.stock).cursor - 1) := by
      cases hp : st.stock.posOf c with
      | none =>
          exfalso
          exact Cycle.posOf_mem (List.mem_iff_getElem?.mpr ⟨_, hprev⟩) hp
      | some i₀ =>
          have hget₂ : st.stock.cards[i₀]? = some c := posOf_get _ _ _ hp
          have hi₀ : i₀ < st.stock.cards.length := Cycle.posOf_lt hp
          have hκm1 : (Cycle.dealIter st.drawStep k st.stock).cursor - 1
              < st.stock.cards.length := (List.getElem?_eq_some_iff.mp hprev).1
          have heq : (Cycle.dealIter st.drawStep k st.stock).cursor - 1 = i₀ :=
            hwf.stock_wf.1 _ _ hκm1 hi₀ (hprev.trans hget₂.symm)
          exact congrArg some heq.symm
    refine ⟨(Cycle.dealIter st.drawStep k st.stock).cursor - 1,
      reachablePos_intro hs hpos hmem, ?_⟩
    show ({ cards := Cycle.removeIdx (Cycle.dealIter st.drawStep k st.stock).cards
              ((Cycle.dealIter st.drawStep k st.stock).cursor - 1),
            cursor := if (Cycle.dealIter st.drawStep k st.stock).cursor - 1
                < (Cycle.dealIter st.drawStep k st.stock).cursor
              then (Cycle.dealIter st.drawStep k st.stock).cursor - 1
              else (Cycle.dealIter st.drawStep k st.stock).cursor } : Cycle Card)
      = (st.stock.drawTo ((Cycle.dealIter st.drawStep k st.stock).cursor - 1)).removeAt
          ((Cycle.dealIter st.drawStep k st.stock).cursor - 1)
    rw [hcards, if_pos (by omega : (Cycle.dealIter st.drawStep k st.stock).cursor - 1
        < (Cycle.dealIter st.drawStep k st.stock).cursor), removeAt_drawTo]

/-- **The jump-soundness theorem**: the tableau-outcome Draw
commitment equals dealing until `c` is the waste top, then playing it
with the physical deck move — the reachable-position guard is exactly
the reachability of that deal sequence.

STATEMENT REPAIR (2026-09-13, the Wave-9 alert — the same hole as
Macro's `commitApplies` repair, witness there): the → direction needed
`st.canPlace c b = true` — `applyDrawTo`'s own guard (accessible
position + free base) does not check the landing rule, so without the
conjunct the theorem admitted Draw-commitment landings no play can
produce (♠7 pile-0's sole visible card, ♥5 the last stock card at the
pass-end cursor, base `inr ♠7`: the jump succeeds, `canSitOn ♥5 ♠7` is
false, so no `deckPile` ever reaches the successor).  With the guard:
→ the mask gives the deal count (`dealReach_maskPos`), then
`deckPile_after_deals`; ← the orbit lands in the mask
(`dealIter_prev_reachable`: `dealIter_mask` + the duplicate-freeness
pin). -/
theorem applyDrawTo_eq_dealPlay {st : State} (hwf : st.WF) {c : Card} {b : Base}
    (hcan : st.canPlace c b = true) {st'' : State} :
    st.applyDrawTo c b = some st'' ↔
      ∃ k st₁, st.run (List.replicate k Move.draw) = some st₁ ∧
        st₁.apply (Move.deckPile c b) = some st'' := by
  constructor
  · intro h
    obtain ⟨i, bd, hr, hatt, hst''⟩ := applyDrawTo_eq h
    have hs : 0 < st.drawStep := hwf.step_pos
    have hpos : st.stock.posOf c = some i := reachablePos_posOf hr
    have hmem := reachablePos_mask hs hr
    have hlt : i < st.stock.cards.length := Cycle.posOf_lt hpos
    obtain ⟨kk, hkk⟩ := dealReach_maskPos hs hlt hmem
    refine ⟨kk, { st with stock := Cycle.dealIter st.drawStep kk st.stock }, ?_, ?_⟩
    · rw [run_dealIter]
    · show ({ st with stock := Cycle.dealIter st.drawStep kk st.stock } : State).apply
          (Move.deckPile c b) = some st''
      rw [hkk]
      have hdp := deckPile_after_deals (posOf_get _ _ _ hpos) hcan hatt
      rw [hdp, removeAt_drawTo, hst'']
  · rintro ⟨k, st₁, hrun, hdp⟩
    rw [run_dealIter] at hrun
    have hst₁ : { st with stock := Cycle.dealIter st.drawStep k st.stock } = st₁ :=
      Option.some.inj hrun
    subst hst₁
    rw [apply_deckPile_iff] at hdp
    obtain ⟨hprev, -, bd, hatt, hst''⟩ := hdp
    obtain ⟨i, hrep, hstock⟩ := dealIter_prev_reachable hwf hprev
    have hatt' : st.board.attach b c = some bd := hatt
    have hXstock : ({ st with stock := Cycle.dealIter st.drawStep k st.stock } : State).stock
        = Cycle.dealIter st.drawStep k st.stock := rfl
    rw [hXstock] at hst''
    rw [hstock] at hst''
    rw [hst'']
    simp only [State.applyDrawTo, hrep, hatt']

/-- The stack-outcome twin: the safe-stack commitment equals dealing
to `c`, then the physical `deckStack` — no repair needed (the rank
guard is `deckStack`'s own). -/
theorem applyDrawStackTo_eq_dealPlay {st : State} (hwf : st.WF) {c : Card}
    {st'' : State} :
    st.applyDrawStackTo c = some st'' ↔
      ∃ k st₁, st.run (List.replicate k Move.draw) = some st₁ ∧
        st₁.apply (Move.deckStack c) = some st'' := by
  constructor
  · intro h
    obtain ⟨i, hr, hrk, hst''⟩ := (applyDrawStackTo_shape).mp h
    have hs : 0 < st.drawStep := hwf.step_pos
    have hpos : st.stock.posOf c = some i := reachablePos_posOf hr
    have hmem := reachablePos_mask hs hr
    have hlt : i < st.stock.cards.length := Cycle.posOf_lt hpos
    obtain ⟨kk, hkk⟩ := dealReach_maskPos hs hlt hmem
    refine ⟨kk, { st with stock := Cycle.dealIter st.drawStep kk st.stock }, ?_, ?_⟩
    · rw [run_dealIter]
    · show ({ st with stock := Cycle.dealIter st.drawStep kk st.stock } : State).apply
          (Move.deckStack c) = some st''
      rw [hkk]
      have hdp := deckStack_after_deals (posOf_get _ _ _ hpos) hrk
      rw [hdp, hst'']
  · rintro ⟨k, st₁, hrun, hds⟩
    rw [run_dealIter] at hrun
    have hst₁ : { st with stock := Cycle.dealIter st.drawStep k st.stock } = st₁ :=
      Option.some.inj hrun
    subst hst₁
    rw [apply_deckStack_iff] at hds
    obtain ⟨hprev, hrk, hst''⟩ := hds
    obtain ⟨i, hrep, hstock⟩ := dealIter_prev_reachable hwf hprev
    have hrk' : c.rank.toIdx = st.heights c.suit := hrk
    have hXstock : ({ st with stock := Cycle.dealIter st.drawStep k st.stock } : State).stock
        = Cycle.dealIter st.drawStep k st.stock := rfl
    rw [hXstock] at hst''
    rw [hstock] at hst''
    rw [hst'']
    simp only [State.applyDrawStackTo, hrep, if_pos hrk']
