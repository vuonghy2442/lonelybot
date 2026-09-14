import Klondike.Move
import Klondike.Relabel
import Klondike.Commutation
import Klondike.Frame

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

/-! ### The `aboveOf` walk kit (local — consolidation candidates)

The self-landing guard of `pilePile` reads `aboveOf`, the fuel walk up
the matching.  Two facts about the walk under a board edit: the
accumulator only grows, and detaching a base only shortens the walk
(the detached walk is a prefix of the original).  With the `contains`
reflection of membership, this carries the guard across `c`'s
departure — the run above `x` shrinks when `c` leaves it, so what did
not land on the run before does not land on it after.  LOCAL this
round (Board/Cycle-level in spirit) — flagged for the consolidation
pass. -/

/-- `List.contains` reflects membership (the `instBEqOfDecidableEq`
instance — the same route as `beq_relabel`). -/
theorem contains_iff_mem : ∀ (l : List Card) (d : Card), l.contains d = true ↔ d ∈ l := by
  intro l
  induction l with
  | nil =>
      intro d
      constructor
      · intro hc; exact Bool.noConfusion hc
      · intro hm; exact nomatch hm
  | cons a t ih =>
      intro d
      constructor
      · intro hc
        have hc' : (d == a || t.contains d) = true := hc
        cases hb : (d == a) with
        | true => exact List.mem_cons.mpr (Or.inl (of_decide_eq_true hb))
        | false =>
            rw [hb, Bool.false_or] at hc'
            exact List.mem_cons.mpr (Or.inr ((ih d).mp hc'))
      · intro hm
        show (d == a || t.contains d) = true
        rcases List.mem_cons.mp hm with hda | hm'
        · have h1 : (d == a) = true := by rw [hda]; exact decide_eq_true rfl
          rw [h1, Bool.true_or]
        · rw [(ih d).mpr hm', Bool.or_true]

/-- The walk's accumulator only grows: everything in `acc` survives
into the walk's result. -/
theorem aboveOf_go_mono (bd : Board) : ∀ (fuel : Nat) (b : Base) (acc : List Card) (y : Card),
    y ∈ acc → y ∈ Board.aboveOf.go bd fuel b acc := by
  intro fuel
  induction fuel with
  | zero => intro b acc y hy; exact hy
  | succ n ih =>
      intro b acc y hy
      rw [aboveOf_go_succ]
      cases ht : bd.topOf b with
      | none => exact hy
      | some c' =>
          show y ∈ (if acc.contains c' = true then acc
            else Board.aboveOf.go bd n (Sum.inr c') (c' :: acc))
          by_cases hc : acc.contains c' = true
          · rw [if_pos hc]; exact hy
          · rw [if_neg hc]
            exact ih (Sum.inr c') (c' :: acc) y (by simp [hy])

/-- One walk step over a matched card (the reduced form, for rewriting
past the constructor-headed match). -/
theorem aboveOf_go_step {bd : Board} {b₀ : Base} {c' : Card} {n : Nat} {acc : List Card}
    (hbd : bd.topOf b₀ = some c') (hc : acc.contains c' ≠ true) :
    Board.aboveOf.go bd (n + 1) b₀ acc = Board.aboveOf.go bd n (Sum.inr c') (c' :: acc) := by
  rw [aboveOf_go_succ, hbd]
  show (if acc.contains c' = true then acc else Board.aboveOf.go bd n (Sum.inr c') (c' :: acc))
      = Board.aboveOf.go bd n (Sum.inr c') (c' :: acc)
  rw [if_neg hc]

/-- Detaching a base only shortens the run walk: every card the
detached board's walk reaches was already reached by the original's
(the two walks coincide until the detached base, where the shortened
one stops first). -/
theorem aboveOf_go_detach {bd : Board} {b : Base} :
    ∀ (fuel : Nat) (b₀ : Base) (acc : List Card) (y : Card),
      y ∈ Board.aboveOf.go (bd.detach b) fuel b₀ acc →
      y ∈ acc ∨ y ∈ Board.aboveOf.go bd fuel b₀ acc := by
  intro fuel
  induction fuel with
  | zero => intro b₀ acc y hy; exact Or.inl hy
  | succ n ih =>
      intro b₀ acc y hy
      rw [aboveOf_go_succ] at hy
      cases ht : (bd.detach b).topOf b₀ with
      | none =>
          rw [ht] at hy
          exact Or.inl hy
      | some c' =>
          rw [ht] at hy
          have hbne : b₀ ≠ b := by
            intro hbe
            rw [hbe, Board.detach_topOf] at ht
            exact absurd ht (by simp)
          have hbd : bd.topOf b₀ = some c' := by
            rw [← Board.detach_topOf_ne bd b b₀ hbne]
            exact ht
          have hy' : y ∈ (if acc.contains c' = true then acc
              else Board.aboveOf.go (bd.detach b) n (Sum.inr c') (c' :: acc)) := hy
          by_cases hc : acc.contains c' = true
          · rw [if_pos hc] at hy'
            exact Or.inl hy'
          · rw [if_neg hc] at hy'
            rcases ih (Sum.inr c') (c' :: acc) y hy' with hy₁ | hy₁
            · rcases List.mem_cons.mp hy₁ with hya | hy₂
              · refine Or.inr ?_
                rw [aboveOf_go_step hbd hc]
                exact aboveOf_go_mono bd n (Sum.inr c') (c' :: acc) y (by rw [hya]; simp)
              · exact Or.inl hy₂
            · refine Or.inr ?_
              rw [aboveOf_go_step hbd hc]
              exact hy₁

/-- Detaching a base only shrinks the run above a card (the walk
corollary of `aboveOf_go_detach`). -/
theorem aboveOf_detach_subset {bd : Board} {b : Base} {x y : Card}
    (hy : y ∈ (bd.detach b).aboveOf x) : y ∈ bd.aboveOf x := by
  rcases aboveOf_go_detach 52 (Sum.inr x) [] y hy with h | h
  · exact nomatch h
  · exact h

/-- The pileStack square: stacking another card `x` commutes with the
stack — both moves are single detaches at distinct bases (each base
holds one card) plus one-height bumps at distinct suits (a shared suit
would force `x = c` through the two rung guards).  The equality of the
ends is `comm_pileStack_pileStack`.  (The ledger's remaining-squares
list missed this one — `pileStack x` with `x ≠ c` is also a first-move
case of the π-induction.) -/
theorem pileStack_comm_pileStack {st : State} {c x : Card} {b₀ bx : Base} {s₁ s₂ : State}
    (hbot : st.board.bottomOf c = some b₀)
    (hbx : st.board.bottomOf x = some bx)
    (hm : st.apply (Move.pileStack c) = some s₁)
    (hmx : st.apply (Move.pileStack x) = some s₂)
    (hxc : x ≠ c) :
    ∃ t, s₁.apply (Move.pileStack x) = some t ∧ s₂.apply (Move.pileStack c) = some t := by
  have hmo := hm
  have hmo2 := hmx
  rw [apply_pileStack_iff] at hm
  obtain ⟨htopn, b, hb, hrk, hs₁⟩ := hm
  have hbb : b = b₀ := (Option.some.inj (hb.symm.trans hbot))
  rw [hbb] at hs₁
  rw [apply_pileStack_iff] at hmx
  obtain ⟨htopn', b', hb', hrkx, hs₂⟩ := hmx
  have hbb' : b' = bx := (Option.some.inj (hb'.symm.trans hbx))
  rw [hbb'] at hs₂
  have htop : st.board.topOf b₀ = some c := (Board.bottomOf_eq st.board c b₀).mp hbot
  have htopx : st.board.topOf bx = some x := (Board.bottomOf_eq st.board x bx).mp hbx
  -- the suits differ (else the rungs force x = c)
  have hσ : x.suit ≠ c.suit := by
    intro hse
    refine hxc ?_
    have h1 : x.rank.toIdx = c.rank.toIdx := by rw [hrkx, hrk, hse]
    have h2 : x.rank = c.rank := Rank.toIdx_inj h1
    cases x; cases c; simp_all
  -- the bases differ (each base holds one card)
  have hnb : bx ≠ b₀ := by
    intro hbe
    rw [hbe] at htopx
    rw [htop] at htopx
    exact hxc (Option.some.inj htopx).symm
  -- neither card sits in the other's seat
  have hbxne : Sum.inr x ≠ b₀ := by
    intro hbe
    rw [← hbe] at htop
    rw [htopn'] at htop
    exact absurd htop (by simp)
  have hbcne : Sum.inr c ≠ bx := by
    intro hbe
    rw [← hbe] at htopx
    rw [htopn] at htopx
    exact absurd htopx (by simp)
  -- the stack of x from the stack successor of c
  have hL : s₁.apply (Move.pileStack x) = some {s₁ with
      board := s₁.board.detach bx,
      heights := fun s => if s = x.suit then s₁.heights s + 1 else s₁.heights s } := by
    rw [hs₁, apply_pileStack_iff]
    refine ⟨?_, bx, ?_, ?_, rfl⟩
    · show (st.board.detach b₀).topOf (Sum.inr x) = none
      rw [Board.detach_topOf_ne st.board b₀ _ hbxne]
      exact htopn'
    · show (st.board.detach b₀).bottomOf x = some bx
      rw [bottomOf_detach_ne htop hxc]
      exact hbx
    · show x.rank.toIdx =
        (if x.suit = c.suit then st.heights x.suit + 1 else st.heights x.suit)
      rw [if_neg hσ]
      exact hrkx
  -- the stack of c from the stack successor of x
  have hR : s₂.apply (Move.pileStack c) = some {s₂ with
      board := s₂.board.detach b₀,
      heights := fun s => if s = c.suit then s₂.heights s + 1 else s₂.heights s } := by
    rw [hs₂, apply_pileStack_iff]
    refine ⟨?_, b₀, ?_, ?_, rfl⟩
    · show (st.board.detach bx).topOf (Sum.inr c) = none
      rw [Board.detach_topOf_ne st.board bx _ hbcne]
      exact htopn
    · show (st.board.detach bx).bottomOf c = some b₀
      rw [bottomOf_detach_ne htopx hxc.symm]
      exact hbot
    · show c.rank.toIdx =
        (if c.suit = x.suit then st.heights c.suit + 1 else st.heights c.suit)
      rw [if_neg (Ne.symm hσ)]
      exact hrk
  -- the two orders end in the same state (the commutation kit)
  have hcomp₁ : (st.apply (Move.pileStack c) >>= fun s => s.apply (Move.pileStack x)) =
      some {s₁ with
        board := s₁.board.detach bx,
        heights := fun s => if s = x.suit then s₁.heights s + 1 else s₁.heights s } := by
    rw [hmo]
    exact hL
  have hcomp₂ : (st.apply (Move.pileStack x) >>= fun s => s.apply (Move.pileStack c)) =
      some {s₂ with
        board := s₂.board.detach b₀,
        heights := fun s => if s = c.suit then s₂.heights s + 1 else s₂.heights s } := by
    rw [hmo2]
    exact hR
  have heq := comm_pileStack_pileStack
    (by
      have hPSt : (Move.pileStack c).touch st = ([b₀], [c]) := by
        simp only [Move.touch, hbot, Option.toList_some]
      have hPSt' : (Move.pileStack x).touch st = ([bx], [x]) := by
        simp only [Move.touch, hbx, Option.toList_some]
      rw [hPSt, hPSt']
      refine ⟨?_, ?_⟩
      · intro β hβm hβm2
        simp only [List.mem_singleton] at hβm hβm2
        rw [hβm] at hβm2
        exact hnb hβm2.symm
      · intro cc ccmem cxmem
        simp only [List.mem_singleton] at ccmem cxmem
        rw [ccmem] at cxmem
        exact hxc cxmem.symm)
    hcomp₁ hcomp₂
  exact ⟨_, hL, hR.trans (congrArg some heq.symm)⟩

/-- The stackPile square: the worry-back `stackPile x b''` of a
different-suit card commutes with the stack — the worry writes the
board at `b''` and `x`'s suit height, the stack the board at `b₀` and
`c`'s suit height.  A shared suit is excluded by hypothesis (a shared
suit forces `x = c` through the two height guards: the drop reads the
pre-bump height — that shape is the *excursion*, the blocked residue);
`b''` is neither `c`'s seat `b₀` (occupied, so `canPlace` fails there)
nor `c` itself (`inr c` — the park, the blocked residue).  The equality
of the ends is `comm_pileStack_stackPile`. -/
theorem pileStack_comm_stackPile {st : State} {c x : Card} {b₀ b'' : Base} {s₁ s₂ : State}
    (hbot : st.board.bottomOf c = some b₀)
    (hm : st.apply (Move.pileStack c) = some s₁)
    (hms : st.apply (Move.stackPile x b'') = some s₂)
    (hnc : b'' ≠ Sum.inr c) (hσ : x.suit ≠ c.suit) :
    ∃ t, s₁.apply (Move.stackPile x b'') = some t ∧ s₂.apply (Move.pileStack c) = some t := by
  have hmo := hm
  have hmo2 := hms
  rw [apply_pileStack_iff] at hm
  obtain ⟨htopn, b, hb, hrk, hs₁⟩ := hm
  have hbb : b = b₀ := (Option.some.inj (hb.symm.trans hbot))
  rw [hbb] at hs₁
  have htop : st.board.topOf b₀ = some c := (Board.bottomOf_eq st.board c b₀).mp hbot
  rw [apply_stackPile_iff] at hms
  obtain ⟨hrkx, hcp, bd, hatt, hs₂⟩ := hms
  -- x is not c (a shared suit would force it through the two guards)
  have hxc : x ≠ c := fun h => hσ (by rw [h])
  -- the landing base is free (hence not c's seat)
  have htopst : st.board.topOf b'' = none := by
    simp only [State.canPlace] at hcp
    exact of_decide_eq_true (Bool.and_eq_true_iff.mp hcp).1
  have hnb : b₀ ≠ b'' := by
    intro hbe
    rw [← hbe] at htopst
    rw [htop] at htopst
    exact absurd htopst (by simp)
  -- the heights guard at the stack successor reads the pre-bump height
  -- at a different suit
  have hrkx' : x.rank.toIdx + 1 = s₁.heights x.suit := by
    rw [hs₁]
    show x.rank.toIdx + 1 =
      (if x.suit = c.suit then st.heights x.suit + 1 else st.heights x.suit)
    rw [if_neg hσ]
    exact hrkx
  have hfreen' : (st.board.detach b₀).topOf b'' = none := by
    rw [Board.detach_topOf_ne st.board b₀ b'' (Ne.symm hnb)]
    exact htopst
  have hfreen : s₁.board.topOf b'' = none := by rw [hs₁]; exact hfreen'
  -- the landing rule at the stack successor (the isVis part transfers)
  have hcp' : s₁.canPlace x b'' = true := by
    cases b'' with
    | inl a =>
        have hk : x.rank = Rank.king := by
          simp only [State.canPlace] at hcp
          exact of_decide_eq_true (Bool.and_eq_true_iff.mp hcp).2
        show (decide (s₁.board.topOf (Sum.inl a) = none) &&
          decide (x.rank = Rank.king)) = true
        rw [hfreen]
        exact Bool.and_eq_true_iff.mpr ⟨rfl, decide_eq_true hk⟩
    | inr d =>
        simp only [State.canPlace] at hcp
        obtain ⟨_, hvisd⟩ := Bool.and_eq_true_iff.mp hcp
        obtain ⟨hvisd, hcs⟩ := Bool.and_eq_true_iff.mp hvisd
        have hdne : d ≠ c := by
          intro hde
          exact hnc (by rw [hde])
        have hvisd' : (s₁.board.bottomOf d).isSome = true := by
          rw [hs₁]
          show ((st.board.detach b₀).bottomOf d).isSome = true
          rw [bottomOf_detach_ne htop hdne]
          exact hvisd
        show (decide (s₁.board.topOf (Sum.inr d) = none) &&
          ((s₁.board.bottomOf d).isSome && canSitOn x d)) = true
        rw [hfreen]
        exact Bool.and_eq_true_iff.mpr ⟨rfl, Bool.and_eq_true_iff.mpr ⟨hvisd', hcs⟩⟩
  -- the same attach from the detached board
  have hne : (st.board.detach b₀).attach b'' x ≠ none := by
    have hbotxn : (st.board.detach b₀).bottomOf x = none := by
      rw [bottomOf_detach_ne htop hxc]
      exact ((Board.attach_eq_some_iff st.board b'' x).mp (by rw [hatt]; simp)).2
    exact (Board.attach_eq_some_iff _ _ _).mpr ⟨hfreen', hbotxn⟩
  cases hatt₁ : (st.board.detach b₀).attach b'' x with
  | none => rw [hatt₁] at hne; simp at hne
  | some bd₁ =>
      have hatt₁' : s₁.board.attach b'' x = some bd₁ := by rw [hs₁]; exact hatt₁
      have hL : s₁.apply (Move.stackPile x b'') = some {s₁ with
          board := bd₁,
          heights := fun s => if s = x.suit then s₁.heights s - 1 else s₁.heights s } := by
        rw [apply_stackPile_iff]
        exact ⟨hrkx', hcp', bd₁, hatt₁', rfl⟩
      -- the stack from the worry-back successor
      have htopn₂ : bd.topOf (Sum.inr c) = none := by
        rw [Board.attach_topOf_ne _ _ _ hatt (Ne.symm hnc)]
        exact htopn
      have hbot₂ : bd.bottomOf c = some b₀ :=
        (Board.bottomOf_eq bd c b₀).mpr (by
          rw [Board.attach_topOf_ne _ _ _ hatt hnb]
          exact htop)
      have hR : s₂.apply (Move.pileStack c) = some {s₂ with
          board := bd.detach b₀,
          heights := fun s => if s = c.suit then s₂.heights s + 1 else s₂.heights s } := by
        rw [hs₂, apply_pileStack_iff]
        refine ⟨htopn₂, b₀, hbot₂, ?_, rfl⟩
        show c.rank.toIdx = (if c.suit = x.suit then st.heights c.suit - 1 else st.heights c.suit)
        rw [if_neg (Ne.symm hσ)]
        exact hrk
      -- the two orders end in the same state (the commutation kit)
      have hcomp₁ : (st.apply (Move.pileStack c) >>= fun s => s.apply (Move.stackPile x b'')) =
          some {s₁ with
            board := bd₁,
            heights := fun s => if s = x.suit then s₁.heights s - 1 else s₁.heights s } := by
        rw [hmo]
        exact hL
      have hcomp₂ : (st.apply (Move.stackPile x b'') >>= fun s => s.apply (Move.pileStack c)) =
          some {s₂ with
            board := bd.detach b₀,
            heights := fun s => if s = c.suit then s₂.heights s + 1 else s₂.heights s } := by
        rw [hmo2]
        exact hR
      have heq := comm_pileStack_stackPile
        (by
          have hPSt : (Move.pileStack c).touch st = ([b₀], [c]) := by
            simp only [Move.touch, hbot, Option.toList_some]
          have hSSt : (Move.stackPile x b'').touch st = ([b''], [x]) := rfl
          rw [hPSt, hSSt]
          refine ⟨?_, ?_⟩
          · intro β hβm hβm2
            simp only [List.mem_singleton] at hβm hβm2
            rw [hβm] at hβm2
            exact hnb hβm2
          · intro cc ccmem cxmem
            simp only [List.mem_singleton] at ccmem cxmem
            rw [ccmem] at cxmem
            exact hxc cxmem.symm)
        hcomp₁ hcomp₂
      exact ⟨_, hL, hR.trans (congrArg some heq.symm)⟩

/-- The pilePile square: re-homing another card's run commutes with
the stack — the rewire writes the board at `x`'s old base and `b''`,
never at `c`'s seat, and does not touch the heights.  This covers BOTH
run shapes: `c` outside the moved run (the commutation kit's
`comm_pileStack_pilePile` shape) and `c` as the moved run's top card
(the run only shortens — `aboveOf_detach_subset` carries the
self-landing guard, and the end boards agree by
`detach_detach_comm`/`attach_detach_comm`); a uniform direct proof
covers the two.  The landing base is neither `c`'s seat `b₀`
(occupied, so `canPlace` fails there) nor `c` itself (`inr c` — the
park, the blocked residue). -/
theorem pileStack_comm_pilePile {st : State} {c x : Card} {b₀ b'' : Base} {s₁ s₂ : State}
    (hbot : st.board.bottomOf c = some b₀)
    (hm : st.apply (Move.pileStack c) = some s₁)
    (hmp : st.apply (Move.pilePile x b'') = some s₂)
    (hnc : b'' ≠ Sum.inr c) (hxc : x ≠ c) :
    ∃ t, s₁.apply (Move.pilePile x b'') = some t ∧ s₂.apply (Move.pileStack c) = some t := by
  have hmo := hm
  rw [apply_pileStack_iff] at hm
  obtain ⟨htopn, b, hb, hrk, hs₁⟩ := hm
  have hbb : b = b₀ := (Option.some.inj (hb.symm.trans hbot))
  rw [hbb] at hs₁
  have htop : st.board.topOf b₀ = some c := (Board.bottomOf_eq st.board c b₀).mp hbot
  rw [apply_pilePile_iff] at hmp
  obtain ⟨b₀x, hbx, hneb, hcmr, bd, hatt, hs₂⟩ := hmp
  have htopx : st.board.topOf b₀x = some x := (Board.bottomOf_eq st.board x b₀x).mp hbx
  -- the landing base is free (hence not c's seat)
  have htopst : st.board.topOf b'' = none := by
    have hcp := hcmr
    simp only [State.canMoveRun] at hcp
    obtain ⟨hcp, _⟩ := Bool.and_eq_true_iff.mp hcp
    simp only [State.canPlace] at hcp
    exact of_decide_eq_true (Bool.and_eq_true_iff.mp hcp).1
  have hnb : b₀ ≠ b'' := by
    intro hbe
    rw [← hbe] at htopst
    rw [htop] at htopst
    exact absurd htopst (by simp)
  have hbbx : b₀ ≠ b₀x := by
    intro hbe
    rw [← hbe] at htopx
    rw [htop] at htopx
    exact hxc (Option.some.inj htopx).symm
  -- x's seat and the landing base survive c's departure
  have hbx₁ : (st.board.detach b₀).bottomOf x = some b₀x := by
    rw [bottomOf_detach_ne htop hxc]
    exact hbx
  have hfreen' : (st.board.detach b₀).topOf b'' = none := by
    rw [Board.detach_topOf_ne st.board b₀ b'' (Ne.symm hnb)]
    exact htopst
  -- the landing rule at the stack successor (the isVis part transfers)
  have hcp' : s₁.canPlace x b'' = true := by
    cases b'' with
    | inl a =>
        have hk : x.rank = Rank.king := by
          have hcp := hcmr
          simp only [State.canMoveRun] at hcp
          obtain ⟨hcp, _⟩ := Bool.and_eq_true_iff.mp hcp
          simp only [State.canPlace] at hcp
          exact of_decide_eq_true (Bool.and_eq_true_iff.mp hcp).2
        show (decide (s₁.board.topOf (Sum.inl a) = none) &&
          decide (x.rank = Rank.king)) = true
        rw [show s₁.board.topOf (Sum.inl a) = none from by
          rw [hs₁]; exact hfreen']
        exact Bool.and_eq_true_iff.mpr ⟨rfl, decide_eq_true hk⟩
    | inr d =>
        have hcp := hcmr
        simp only [State.canMoveRun] at hcp
        obtain ⟨hcp, _⟩ := Bool.and_eq_true_iff.mp hcp
        simp only [State.canPlace] at hcp
        obtain ⟨_, hvisd⟩ := Bool.and_eq_true_iff.mp hcp
        obtain ⟨hvisd, hcs⟩ := Bool.and_eq_true_iff.mp hvisd
        have hdne : d ≠ c := by
          intro hde
          exact hnc (by rw [hde])
        have hvisd' : (s₁.board.bottomOf d).isSome = true := by
          rw [hs₁]
          show ((st.board.detach b₀).bottomOf d).isSome = true
          rw [bottomOf_detach_ne htop hdne]
          exact hvisd
        show (decide (s₁.board.topOf (Sum.inr d) = none) &&
          ((s₁.board.bottomOf d).isSome && canSitOn x d)) = true
        rw [show s₁.board.topOf (Sum.inr d) = none from by
          rw [hs₁]; exact hfreen']
        exact Bool.and_eq_true_iff.mpr ⟨rfl, Bool.and_eq_true_iff.mpr ⟨hvisd', hcs⟩⟩
  -- the self-landing guard transfers (the run above x only shrinks)
  have hcmr' : s₁.canMoveRun x b'' = true := by
    simp only [State.canMoveRun, hcp', Bool.true_and]
    cases b'' with
    | inl a => rfl
    | inr d =>
        have hsub : ∀ y ∈ s₁.board.aboveOf x, y ∈ st.board.aboveOf x := by
          intro y hy
          rw [hs₁] at hy
          exact aboveOf_detach_subset hy
        have hgd : (st.board.aboveOf x).contains d = false := by
          have hcp := hcmr
          simp only [State.canMoveRun] at hcp
          obtain ⟨_, hgd⟩ := Bool.and_eq_true_iff.mp hcp
          cases hbb : (st.board.aboveOf x).contains d with
          | true =>
              rw [hbb] at hgd
              exact absurd hgd (by simp)
          | false => rfl
        show (!((s₁.board.aboveOf x).contains d)) = true
        cases hbc : (s₁.board.aboveOf x).contains d with
        | true =>
            exfalso
            have hmem : d ∈ s₁.board.aboveOf x := (contains_iff_mem _ _).mp hbc
            have hmem' : d ∈ st.board.aboveOf x := hsub d hmem
            rw [(contains_iff_mem _ _).mpr hmem'] at hgd
            exact Bool.noConfusion hgd
        | false => rfl
  -- the rewire from the stack successor: x's base detaches, the run re-lands
  have hne' : ((st.board.detach b₀).detach b₀x).attach b'' x ≠ none := by
    refine (Board.attach_eq_some_iff _ _ _).mpr ⟨?_, ?_⟩
    · show ((st.board.detach b₀).detach b₀x).topOf b'' = none
      rw [Board.detach_topOf_ne (st.board.detach b₀) b₀x b'' (Ne.symm hneb)]
      exact hfreen'
    · show ((st.board.detach b₀).detach b₀x).bottomOf x = none
      exact Board.bottomOf_detach_self
        (by rw [Board.detach_topOf_ne st.board b₀ b₀x (Ne.symm hbbx)]; exact htopx)
  cases hatt₁ : ((st.board.detach b₀).detach b₀x).attach b'' x with
  | none => rw [hatt₁] at hne'; simp at hne'
  | some bd₁ =>
      -- the LHS: the rewire from the stack successor
      have hbx₁' : s₁.board.bottomOf x = some b₀x := by rw [hs₁]; exact hbx₁
      have hatt₁' : (s₁.board.detach b₀x).attach b'' x = some bd₁ := by
        rw [hs₁]
        exact hatt₁
      have hL : s₁.apply (Move.pilePile x b'') = some {s₁ with board := bd₁} := by
        rw [apply_pilePile_iff]
        exact ⟨b₀x, hbx₁', hneb, hcmr', bd₁, hatt₁', rfl⟩
      -- the RHS: the stack from the rewire successor
      have hb0xne : Sum.inr c ≠ b₀x := by
        intro hbe
        rw [← hbe] at htopx
        rw [htopn] at htopx
        exact absurd htopx (by simp)
      have htopn₂ : bd.topOf (Sum.inr c) = none := by
        rw [Board.attach_topOf_ne _ _ _ hatt (Ne.symm hnc)]
        rw [Board.detach_topOf_ne st.board b₀x _ hb0xne]
        exact htopn
      have hbot₂ : bd.bottomOf c = some b₀ := by
        rw [bottomOf_attach_ne hatt hxc.symm]
        rw [bottomOf_detach_ne htopx hxc.symm]
        exact hbot
      have hR : s₂.apply (Move.pileStack c) = some {s₂ with
          board := bd.detach b₀,
          heights := fun s => if s = c.suit then s₂.heights s + 1 else s₂.heights s } := by
        rw [hs₂, apply_pileStack_iff]
        exact ⟨htopn₂, b₀, hbot₂, hrk, rfl⟩
      -- the ends agree (uniform direct proof — covers c inside the
      -- moved run too: the detach/attach commutations)
      have h2 : ((st.board.detach b₀x).detach b₀).attach b'' x = some bd₁ := by
        rw [← detach_detach_comm hbbx]
        exact hatt₁
      have hbd : bd₁ = bd.detach b₀ := (attach_detach_comm (Ne.symm hnb) hatt h2).symm
      have hTL : {s₁ with board := bd₁} = {s₂ with
          board := bd.detach b₀,
          heights := fun s => if s = c.suit then s₂.heights s + 1 else s₂.heights s } := by
        rw [hs₁, hs₂]
        refine state_ext rfl ?_ ?_ rfl rfl rfl
        · rw [hbd]
        · rfl
      exact ⟨_, hL, hR.trans (congrArg some hTL.symm)⟩

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

/-- A successful `reveal` preserves another card's unlockedness (when
that card is a run top — the π-induction's `c`): the reveal steps one
pile's boundary depth and seats the old boundary card; `c`'s seat
survives (the landing base `hiddenBase a` is free, and `c` occupies
its own), and for the boundary search to newly find `c`'s parent, the
stepped pile's new boundary would have to be exactly that parent — but
the reveal's own attach targets precisely that base and demands it
free, while `c` sits there.  The reveal case of the crux's
π-induction applies its IH at the reveal successor, where this is the
lockedness side condition. -/
theorem reveal_notLocked {st s₂ : State} {c x : Card} (hnotlock : st.isLocked c = false)
    (htopn : st.board.topOf (Sum.inr c) = none)
    (hmr : st.apply (Move.reveal x) = some s₂) : s₂.isLocked c = false := by
  rw [apply_reveal_iff] at hmr
  obtain ⟨htopx, r, a, bd, hbx, hpile, hatt, hs₂⟩ := hmr
  -- c is not the revealed boundary (x sits on r; nothing sits on c)
  have hcr : c ≠ r := by
    intro hce
    rw [← hce] at hbx
    have hX : st.board.topOf (Sum.inr c) = some x :=
      (Board.bottomOf_eq st.board x (Sum.inr c)).mp hbx
    rw [htopn] at hX
    exact absurd hX (by simp)
  -- c's seat survives the reveal's attach
  have hb : bd.bottomOf c = st.board.bottomOf c := bottomOf_attach_ne hatt hcr
  -- the old boundary of the stepped pile
  have hgt : (st.hidden a).getLast? = some r :=
    of_decide_eq_true ((findFirst_mem _ _ _ hpile).2)
  rw [hs₂]
  simp only [State.isLocked]
  rw [hb]
  cases hb₀ : st.board.bottomOf c with
  | none => rfl
  | some b =>
      cases b with
      | inl a' => rfl
      | inr d =>
          -- the old search missed d
          have hpd : st.pileOfTopHidden d = none := by
            have h := hnotlock
            simp only [State.isLocked, hb₀] at h
            cases hp : st.pileOfTopHidden d with
            | none => rfl
            | some a'' =>
                rw [hp] at h
                simp at h
          -- r ≠ d (else the reveal's trigger x shares d's seat with c,
          -- making the trigger c itself — locked)
          have hrd : r ≠ d := by
            intro hde
            rw [hde] at hbx hpile
            have hx : st.board.topOf (Sum.inr d) = some x :=
              (Board.bottomOf_eq st.board x (Sum.inr d)).mp hbx
            have hc : st.board.topOf (Sum.inr d) = some c :=
              (Board.bottomOf_eq st.board c (Sum.inr d)).mp hb₀
            have hxc : x = c := Option.some.inj (hx.symm.trans hc)
            rw [hxc] at hbx
            have hlk : st.isLocked c = true := by
              simp only [State.isLocked, hbx]
              exact decide_eq_true (by rw [hpile]; simp)
            rw [hlk] at hnotlock
            exact Bool.noConfusion hnotlock
          -- the new search still misses d at every pile
          have hkey : ({ st with
              board := bd,
              depths := fun a' => if a' = a then st.depths a - 1 else st.depths a' }).pileOfTopHidden d = none := by
            show findFirst (fun a' => decide ((({ st with
                board := bd,
                depths := fun a' => if a' = a then st.depths a - 1 else st.depths a' }).topHidden a') = some d)) Anchor.all = none
            refine findFirst_eq_none _ Anchor.all (fun a' ha' => ?_)
            by_cases haa : a' = a
            · intro htd
              have hd₂ : ((st.deal.piles a).take (st.depths a - 1)).getLast? = some d := by
                have h : ((({ st with
                    board := bd,
                    depths := fun a' => if a' = a then st.depths a - 1 else st.depths a' }).topHidden) a') = some d :=
                  of_decide_eq_true htd
                rw [haa] at h
                have h' : ((st.deal.piles a).take
                    (if a = a then st.depths a - 1 else st.depths a)).getLast? = some d := h
                rw [if_pos rfl] at h'
                exact h'
              have hgt' : ((st.deal.piles a).take (st.depths a)).getLast? = some r := hgt
              have hhead : (((st.deal.piles a).take (st.depths a)).reverse.drop 1).head? = some d :=
                take_reverse_drop1 hgt' hd₂ hrd
              have hhb : st.hiddenBase a = Sum.inr d := by
                simp only [State.hiddenBase, State.hidden, hhead]
              have hfree : st.board.topOf (Sum.inr d) = none := by
                have h := (Board.attach_eq_some_iff st.board (st.hiddenBase a) r).mp
                  (by rw [hatt]; simp)
                rw [hhb] at h
                exact h.1
              exact absurd hfree (by rw [(Board.bottomOf_eq st.board c (Sum.inr d)).mp hb₀]; simp)
            · intro htd
              have h' : ((st.deal.piles a').take (st.depths a')).getLast? = some d := by
                have hc : ((st.deal.piles a').take
                    (if a' = a then st.depths a - 1 else st.depths a')).getLast? = some d :=
                  of_decide_eq_true htd
                rw [if_neg haa] at hc
                exact hc
              have h'' : st.topHidden a' = some d := h'
              exact findFirst_ne_none_of_mem
                (fun a'' => decide (st.topHidden a'' = some d)) Anchor.all a' ha'
                (decide_eq_true h'') hpd
          show (decide (({ st with
            board := bd,
            depths := fun a' => if a' = a then st.depths a - 1 else st.depths a' }).pileOfTopHidden d ≠ none)) = false
          rw [hkey]
          simp

/-! ### The IH-transfer one-liners (the π-induction's guards)

The crux's induction feeds its IH at each first-move successor `s₂`;
the guards — `s₂.isLocked c = false` and `s₂.board.bottomOf c =
some b₀` — follow from the source facts plus these one-liners.  The
six non-reveal shapes (`draw`, `deckStack`, `deckPile`, `pileStack x`,
`stackPile x b''`, `pilePile x b''`) write neither the deal nor the
depths, so the hidden-pile views are untouched and only the seat has
to survive the board edit; the reveal shape's lockedness half is
`reveal_notLocked` above, with the seat half (`bottomOf_of_reveal`)
repeated here.  ENDGAME.md §5 W1. -/

/-- Lockedness congruence: the same seat (via `bottomOf`) and the same
deal/depths give the same lockedness — the search reads nothing else. -/
theorem isLocked_congr {st s₂ : State} {c : Card}
    (hbot : s₂.board.bottomOf c = st.board.bottomOf c)
    (hdeal : s₂.deal = st.deal) (hdpt : s₂.depths = st.depths) :
    s₂.isLocked c = st.isLocked c := by
  simp only [State.isLocked, hbot]
  cases st.board.bottomOf c with
  | none => rfl
  | some b =>
      cases b with
      | inl _ => rfl
      | inr r =>
          show decide (s₂.pileOfTopHidden r ≠ none) = decide (st.pileOfTopHidden r ≠ none)
          rw [pileOfTopHidden_congr hdeal hdpt r]

/-- `draw`: the stock advance touches nothing the lockedness or seat
searches read. -/
theorem lockedness_draw {st s₂ : State} {c : Card}
    (hmd : st.apply Move.draw = some s₂) :
    s₂.isLocked c = st.isLocked c ∧ s₂.board.bottomOf c = st.board.bottomOf c := by
  rw [apply_draw_iff] at hmd
  obtain rfl := hmd
  exact ⟨isLocked_congr rfl rfl rfl, rfl⟩

/-- `deckStack`: the foundation draw writes the stock and one height —
not the seat or the hidden piles. -/
theorem lockedness_deckStack {st s₂ : State} {c x : Card}
    (hmd : st.apply (Move.deckStack x) = some s₂) :
    s₂.isLocked c = st.isLocked c ∧ s₂.board.bottomOf c = st.board.bottomOf c := by
  rw [apply_deckStack_iff] at hmd
  obtain ⟨_, _, rfl⟩ := hmd
  exact ⟨isLocked_congr rfl rfl rfl, rfl⟩

/-- `deckPile` onto another card's base: the seat and the hidden piles
survive the attach (the played card itself is stocked, so it is not
`c` — that exclusion is the caller's job). -/
theorem lockedness_deckPile {st s₂ : State} {c x : Card} {b'' : Base}
    (hmd : st.apply (Move.deckPile x b'') = some s₂) (hxc : c ≠ x) :
    s₂.isLocked c = st.isLocked c ∧ s₂.board.bottomOf c = st.board.bottomOf c := by
  rw [apply_deckPile_iff] at hmd
  obtain ⟨_, _, bd, hatt, rfl⟩ := hmd
  exact ⟨isLocked_congr (bottomOf_attach_ne hatt hxc) rfl rfl,
    bottomOf_attach_ne hatt hxc⟩

/-- `pileStack` of another card `x`: `c`'s seat survives the detach at
`x`'s base. -/
theorem lockedness_pileStack {st s₂ : State} {c x : Card}
    (hmx : st.apply (Move.pileStack x) = some s₂) (hxc : c ≠ x) :
    s₂.isLocked c = st.isLocked c ∧ s₂.board.bottomOf c = st.board.bottomOf c := by
  rw [apply_pileStack_iff] at hmx
  obtain ⟨_, bx, hbx, _, rfl⟩ := hmx
  exact ⟨isLocked_congr
      (bottomOf_detach_ne ((Board.bottomOf_eq st.board x bx).mp hbx) hxc) rfl rfl,
    bottomOf_detach_ne ((Board.bottomOf_eq st.board x bx).mp hbx) hxc⟩

/-- `stackPile` of another card `x`: `c`'s seat survives the attach at
the landing base. -/
theorem lockedness_stackPile {st s₂ : State} {c x : Card} {b'' : Base}
    (hms : st.apply (Move.stackPile x b'') = some s₂) (hxc : c ≠ x) :
    s₂.isLocked c = st.isLocked c ∧ s₂.board.bottomOf c = st.board.bottomOf c := by
  rw [apply_stackPile_iff] at hms
  obtain ⟨_, _, bd, hatt, rfl⟩ := hms
  exact ⟨isLocked_congr (bottomOf_attach_ne hatt hxc) rfl rfl,
    bottomOf_attach_ne hatt hxc⟩

/-- `pilePile` of another card `x`: `c`'s seat survives both the
detach at `x`'s old base and the attach at the landing base. -/
theorem lockedness_pilePile {st s₂ : State} {c x : Card} {b'' : Base}
    (hmp : st.apply (Move.pilePile x b'') = some s₂) (hxc : c ≠ x) :
    s₂.isLocked c = st.isLocked c ∧ s₂.board.bottomOf c = st.board.bottomOf c := by
  rw [apply_pilePile_iff] at hmp
  obtain ⟨bx, hbx, _, _, bd, hatt, rfl⟩ := hmp
  have hstep : (st.board.detach bx).bottomOf c = st.board.bottomOf c :=
    bottomOf_detach_ne ((Board.bottomOf_eq st.board x bx).mp hbx) hxc
  exact ⟨isLocked_congr ((bottomOf_attach_ne hatt hxc).trans hstep) rfl rfl,
    (bottomOf_attach_ne hatt hxc).trans hstep⟩

/-- The reveal's seat half (the lockedness half is
`reveal_notLocked`): `c`'s seat survives the boundary card's attach —
if the boundary `r` were `c`, the trigger `x` would sit on `c`,
excluded by `c`'s top-freeness (the stack's own guard). -/
theorem bottomOf_of_reveal {st s₂ : State} {c x : Card}
    (htopn : st.board.topOf (Sum.inr c) = none)
    (hmr : st.apply (Move.reveal x) = some s₂) :
    s₂.board.bottomOf c = st.board.bottomOf c := by
  rw [apply_reveal_iff] at hmr
  obtain ⟨_, r, a, bd, hbx, _, hatt, rfl⟩ := hmr
  have hcr : c ≠ r := by
    intro hce
    rw [← hce] at hbx
    have hX : st.board.topOf (Sum.inr c) = some x :=
      (Board.bottomOf_eq st.board x (Sum.inr c)).mp hbx
    rw [htopn] at hX
    exact absurd hX (by simp)
  exact bottomOf_attach_ne hatt hcr

/-! ### The first-move steps (the π-induction's square cases)

For each non-blocked first move of the winning play, the commute
squares turn the crux at `st` into the crux at the move's successor:
the square replays the move from the stack successor, landing on the
common state `t`, and the (shorter-tail) induction hypothesis at `s₂`
— packaged here as `ih : ∀ t, s₂.apply (Move.pileStack c) = some t →
t.solvableFrom` — supplies `t`'s solvability; prepending the replayed
move then wins from `s₁`.  With the vacuity (`not_pileStack_of_win`),
the delete case (`solvable_of_pileStack_step_delete`), the run-root
replay (`pileStack_pilePile_stackPile`), and these seven steps, every
first move is covered except the parks on `inr c` and the same-suit
excursion — the endgame's residue. -/

/-- A won state admits no `pileStack`: every height is 13, past every
rung.  The π-induction's nil case is vacuous. -/
theorem not_pileStack_of_win {st : State} (hw : st.isWin = true) (c : Card)
    (s₁ : State) (hm : st.apply (Move.pileStack c) = some s₁) : False := by
  rw [apply_pileStack_iff] at hm
  obtain ⟨_, _, _, hrk, _⟩ := hm
  have h13 : st.heights c.suit = 13 := by
    have h := hw
    simp only [State.isWin] at h
    exact of_decide_eq_true (List.all_eq_true.mp h c.suit (Suit.mem_all c.suit))
  rw [h13] at hrk
  have := Rank.toIdx_lt c.rank
  omega

/-- The delete case: the winning play itself starts with `pileStack c`
— the stack successor runs the tail unchanged (apply is deterministic,
so the two runs coincide). -/
theorem solvable_of_pileStack_step_delete {st : State} {c : Card} {s₁ : State}
    (hm : st.apply (Move.pileStack c) = some s₁)
    {π : List Move} {w : State} (hw : st.run (Move.pileStack c :: π) = some w)
    (hwin : w.isWin = true) : s₁.solvableFrom := by
  refine ⟨π, w, ?_, hwin⟩
  have hw' : (match st.apply (Move.pileStack c) with
    | some st' => st'.run π
    | none => none) = some w := hw
  rw [hm] at hw'
  exact hw'

/-- The draw step: replay the deal from the stack successor. -/
theorem solvable_of_pileStack_step_draw {st : State} {c : Card} {b₀ : Base} {s₁ s₂ : State}
    (hbot : st.board.bottomOf c = some b₀)
    (hm : st.apply (Move.pileStack c) = some s₁)
    (hmd : st.apply Move.draw = some s₂)
    (ih : ∀ t, s₂.apply (Move.pileStack c) = some t → t.solvableFrom) :
    s₁.solvableFrom := by
  have hmo := hm
  rw [apply_pileStack_iff] at hmo
  obtain ⟨_, _, _, hrk, _⟩ := hmo
  obtain ⟨t, hL, hR⟩ := pileStack_comm_draw hbot hrk hm hmd
  obtain ⟨win, w, hwrun, hwin⟩ := ih t hR
  refine ⟨Move.draw :: win, w, ?_, hwin⟩
  simp only [State.run, hL]
  exact hwrun

/-- The reveal step: replay the reveal from the stack successor. -/
theorem solvable_of_pileStack_step_reveal {st : State} {c : Card} (hwf : st.WF)
    (hnotlock : st.isLocked c = false) {x : Card} {b₀ : Base} {s₁ s₂ : State}
    (hbot : st.board.bottomOf c = some b₀)
    (hm : st.apply (Move.pileStack c) = some s₁)
    (hmr : st.apply (Move.reveal x) = some s₂)
    (ih : ∀ t, s₂.apply (Move.pileStack c) = some t → t.solvableFrom) :
    s₁.solvableFrom := by
  have hmo := hm
  rw [apply_pileStack_iff] at hmo
  obtain ⟨_, _, _, hrk, _⟩ := hmo
  obtain ⟨t, hL, hR⟩ := pileStack_comm_reveal hwf hnotlock hbot hrk hm hmr
  obtain ⟨win, w, hwrun, hwin⟩ := ih t hR
  refine ⟨Move.reveal x :: win, w, ?_, hwin⟩
  simp only [State.run, hL]
  exact hwrun

/-- The deckStack step: replay the foundation draw from the stack
successor. -/
theorem solvable_of_pileStack_step_deckStack {st : State} (hwf : st.WF)
    {c x : Card} {b₀ : Base} {s₁ s₂ : State}
    (hbot : st.board.bottomOf c = some b₀)
    (hm : st.apply (Move.pileStack c) = some s₁)
    (hmd : st.apply (Move.deckStack x) = some s₂)
    (ih : ∀ t, s₂.apply (Move.pileStack c) = some t → t.solvableFrom) :
    s₁.solvableFrom := by
  have hmo := hm
  rw [apply_pileStack_iff] at hmo
  obtain ⟨_, _, _, hrk, _⟩ := hmo
  obtain ⟨t, hL, hR⟩ := pileStack_comm_deckStack hwf hbot hrk hm hmd
  obtain ⟨win, w, hwrun, hwin⟩ := ih t hR
  refine ⟨Move.deckStack x :: win, w, ?_, hwin⟩
  simp only [State.run, hL]
  exact hwrun

/-- The deckPile step: replay the waste play (the landing base is not
`c` itself — the park, the blocked residue) from the stack successor. -/
theorem solvable_of_pileStack_step_deckPile {st : State} (hwf : st.WF)
    {c x : Card} {b₀ b'' : Base} {s₁ s₂ : State}
    (hbot : st.board.bottomOf c = some b₀)
    (hm : st.apply (Move.pileStack c) = some s₁)
    (hmd : st.apply (Move.deckPile x b'') = some s₂)
    (hnc : b'' ≠ Sum.inr c)
    (ih : ∀ t, s₂.apply (Move.pileStack c) = some t → t.solvableFrom) :
    s₁.solvableFrom := by
  have hmo := hm
  rw [apply_pileStack_iff] at hmo
  obtain ⟨_, _, _, hrk, _⟩ := hmo
  obtain ⟨t, hL, hR⟩ := pileStack_comm_deckPile hwf hbot hrk hm hmd hnc
  obtain ⟨win, w, hwrun, hwin⟩ := ih t hR
  refine ⟨Move.deckPile x b'' :: win, w, ?_, hwin⟩
  simp only [State.run, hL]
  exact hwrun

/-- The pileStack step: stacking another card `x` also commutes (a
shared suit would force `x = c` through the rungs). -/
theorem solvable_of_pileStack_step_pileStack {st : State} {c x : Card} {b₀ bx : Base}
    {s₁ s₂ : State}
    (hbot : st.board.bottomOf c = some b₀)
    (hbx : st.board.bottomOf x = some bx)
    (hm : st.apply (Move.pileStack c) = some s₁)
    (hmx : st.apply (Move.pileStack x) = some s₂)
    (hxc : x ≠ c)
    (ih : ∀ t, s₂.apply (Move.pileStack c) = some t → t.solvableFrom) :
    s₁.solvableFrom := by
  obtain ⟨t, hL, hR⟩ := pileStack_comm_pileStack hbot hbx hm hmx hxc
  obtain ⟨win, w, hwrun, hwin⟩ := ih t hR
  refine ⟨Move.pileStack x :: win, w, ?_, hwin⟩
  simp only [State.run, hL]
  exact hwrun

/-- The stackPile step: the worry-back of a different-suit card
commutes (the same-suit shape is the excursion, the blocked residue). -/
theorem solvable_of_pileStack_step_stackPile {st : State} {c x : Card} {b₀ b'' : Base}
    {s₁ s₂ : State}
    (hbot : st.board.bottomOf c = some b₀)
    (hm : st.apply (Move.pileStack c) = some s₁)
    (hms : st.apply (Move.stackPile x b'') = some s₂)
    (hnc : b'' ≠ Sum.inr c) (hσ : x.suit ≠ c.suit)
    (ih : ∀ t, s₂.apply (Move.pileStack c) = some t → t.solvableFrom) :
    s₁.solvableFrom := by
  obtain ⟨t, hL, hR⟩ := pileStack_comm_stackPile hbot hm hms hnc hσ
  obtain ⟨win, w, hwrun, hwin⟩ := ih t hR
  refine ⟨Move.stackPile x b'' :: win, w, ?_, hwin⟩
  simp only [State.run, hL]
  exact hwrun

/-- The pilePile step: re-homing another card's run commutes (covers
both run shapes — `c` outside the run and `c` as its top card). -/
theorem solvable_of_pileStack_step_pilePile {st : State} {c x : Card} {b₀ b'' : Base}
    {s₁ s₂ : State}
    (hbot : st.board.bottomOf c = some b₀)
    (hm : st.apply (Move.pileStack c) = some s₁)
    (hmp : st.apply (Move.pilePile x b'') = some s₂)
    (hnc : b'' ≠ Sum.inr c) (hxc : x ≠ c)
    (ih : ∀ t, s₂.apply (Move.pileStack c) = some t → t.solvableFrom) :
    s₁.solvableFrom := by
  obtain ⟨t, hL, hR⟩ := pileStack_comm_pilePile hbot hm hmp hnc hxc
  obtain ⟨win, w, hwrun, hwin⟩ := ih t hR
  refine ⟨Move.pilePile x b'' :: win, w, ?_, hwin⟩
  simp only [State.run, hL]
  exact hwrun

/-! ### The π-scaffold (ENDGAME.md §5: W1's aux, W2's rung pass, W3's
adjacent pair)

`cBlocked` is the blocked-shape predicate of the crux's π-induction;
`solvable_of_pileStack_aux` packages the closed dispatch (vacuity,
delete, run-root, seven commuting steps) under the no-blocked-move
hypothesis — the park/excursion residue (W3/W4) is EXCLUDED, not
assumed away: the statement is assembled only from proven cases, so
it carries no new `sorry`.  `rung_pass_of_win` is the rung-pass
existence (every winning play fires `pileStack c`, the first
exceedance of `c`'s rung). -/

/-- The blocked shapes of the crux's π-induction (ENDGAME.md §3): a
placement move seating a card *on* `c` (the park), and a `stackPile`
of `c`'s suit (the same-suit worry-back — the excursion; the landing
base is irrelevant, any same-suit worry-back drops the rung before the
pass).  Everything else — including `pileStack c` itself (the rung
pass, the delete case) and `pilePile c b''` (the run-root re-home) —
is unblocked. -/
def cBlocked (c : Card) : Move → Bool
  | .deckPile _ b'' => decide (b'' = Sum.inr c)
  | .stackPile x b'' => decide (b'' = Sum.inr c) || decide (x.suit = c.suit)
  | .pilePile _ b'' => decide (b'' = Sum.inr c)
  | _ => false

theorem cBlocked_deckPile {c x : Card} {b'' : Base}
    (h : cBlocked c (Move.deckPile x b'') = false) : b'' ≠ Sum.inr c := by
  intro hbe
  have hc : cBlocked c (Move.deckPile x b'') = true := by
    show (decide (b'' = Sum.inr c) : Bool) = true
    rw [hbe]
    simp
  rw [hc] at h
  exact Bool.noConfusion h

theorem cBlocked_pilePile {c x : Card} {b'' : Base}
    (h : cBlocked c (Move.pilePile x b'') = false) : b'' ≠ Sum.inr c := by
  intro hbe
  have hc : cBlocked c (Move.pilePile x b'') = true := by
    show (decide (b'' = Sum.inr c) : Bool) = true
    rw [hbe]
    simp
  rw [hc] at h
  exact Bool.noConfusion h

theorem cBlocked_stackPile {c x : Card} {b'' : Base}
    (h : cBlocked c (Move.stackPile x b'') = false) :
    b'' ≠ Sum.inr c ∧ x.suit ≠ c.suit := by
  constructor
  · intro hbe
    have hc : cBlocked c (Move.stackPile x b'') = true := by
      show (decide (b'' = Sum.inr c) || decide (x.suit = c.suit)) = true
      rw [hbe]
      simp
    rw [hc] at h
    exact Bool.noConfusion h
  · intro hse
    have hc : cBlocked c (Move.stackPile x b'') = true := by
      show (decide (b'' = Sum.inr c) || decide (x.suit = c.suit)) = true
      rw [hse]
      simp
    rw [hc] at h
    exact Bool.noConfusion h

/-- The π-scaffold of the crux's N-half (ENDGAME.md §5, W1): a winning
play whose prefix before the rung pass is unblocked replays from the
stack successor `s₁` — by induction on the play's length, dispatching
each first move to the landed machinery: the rung pass itself (the
delete case, `solvable_of_pileStack_step_delete`), the run-root
re-home (`pileStack_pilePile_stackPile`), and the seven commuting
steps (`solvable_of_pileStack_step_*`), with the IH's guards —
`s₂.WF` (`apply_wf`), `s₂.isLocked c = false` and
`s₂.board.bottomOf c = some b₀` (the transfer one-liners above) —
carried per case.  The hypothesis is the `rungNormal` substance (the
rung pass occurs, and nothing parks on `c` nor worries back `c`'s
suit before it — `cBlocked`); moves AFTER the pass are unconstrained,
matching `rung_pass_of_win`'s conclusion shape, so W5 composes the
normal-form existence, this aux, and the delete case without touching
the tail.  No new `sorry`: every dispatched case is proven. -/
private theorem solvable_of_pileStack_aux : ∀ (n : Nat) (st : State) (c : Card)
    (b₀ : Base) (s₁ : State), st.WF → st.isLocked c = false →
    st.board.bottomOf c = some b₀ → st.apply (Move.pileStack c) = some s₁ →
    ∀ π : List Move, π.length ≤ n →
    (∃ π₁ π₂, π = π₁ ++ Move.pileStack c :: π₂ ∧ ∀ m ∈ π₁, cBlocked c m = false) →
    ∀ w, st.run π = some w → w.isWin = true → s₁.solvableFrom := by
  intro n
  induction n with
  | zero =>
      intro st c b₀ s₁ _ _ _ hm π hlen hep w hrun hwin
      cases π with
      | nil => obtain ⟨_, _, hsplit, _⟩ := hep; simp at hsplit
      | cons m rest =>
          simp only [List.length_cons] at hlen
          exact absurd hlen (by omega)
  | succ n ih =>
      intro st c b₀ s₁ hwf hnotlock hbot hm π hlen hep w hrun hwin
      obtain ⟨π₁, π₂, hsplit, hclr₁⟩ := hep
      cases π with
      | nil => simp at hsplit
      | cons m rest =>
          have hlenr : rest.length ≤ n := by
            simp only [List.length_cons] at hlen
            omega
          have hmo := hm
          rw [apply_pileStack_iff] at hmo
          obtain ⟨htopn, _, _, hrk, _⟩ := hmo
          by_cases hfirst : π₁ = []
          · -- the rung pass is the first move: the delete case, no IH
            subst hfirst
            simp only [List.nil_append, List.cons.injEq] at hsplit
            obtain ⟨rfl, rfl⟩ := hsplit
            exact solvable_of_pileStack_step_delete hm hrun hwin
          · -- the first move precedes the pass: it is unblocked
            obtain ⟨m', rest₁, rfl⟩ : ∃ m' rest₁, π₁ = m' :: rest₁ := by
              cases π₁ with
              | nil => exact absurd rfl hfirst
              | cons m' rest₁ => exact ⟨m', rest₁, rfl⟩
            simp only [List.cons_append, List.cons.injEq] at hsplit
            obtain ⟨hmeq, hrest'⟩ := hsplit
            have hcm : cBlocked c m = false := by
              rw [hmeq]
              exact hclr₁ m' (by simp)
            have hep' : ∃ ρ₁ ρ₂, rest = ρ₁ ++ Move.pileStack c :: ρ₂ ∧
                ∀ m'' ∈ ρ₁, cBlocked c m'' = false :=
              ⟨rest₁, π₂, hrest', fun m'' hm'' => hclr₁ m'' (by simp [hm''])⟩
            have hrun' := hrun
            simp only [State.run] at hrun'
            cases hm2 : st.apply m with
            | none => rw [hm2] at hrun'; simp at hrun'
            | some s₂ =>
                rw [hm2] at hrun'
                have hrest : s₂.run rest = some w := hrun'
                have hwf₂ := apply_wf hwf m s₂ hm2
                cases m with
                | draw =>
                    obtain ⟨hlk, hb2⟩ := lockedness_draw hm2
                    refine solvable_of_pileStack_step_draw hbot hm hm2 ?_
                    intro t hR
                    exact ih s₂ c b₀ t hwf₂ (hlk.trans hnotlock)
                      (hb2.trans hbot) hR rest hlenr hep' w hrest hwin
                | reveal x =>
                    have hlock₂ : s₂.isLocked c = false :=
                      reveal_notLocked hnotlock htopn hm2
                    have hb2 : s₂.board.bottomOf c = some b₀ :=
                      (bottomOf_of_reveal htopn hm2).trans hbot
                    refine solvable_of_pileStack_step_reveal hwf hnotlock hbot hm hm2 ?_
                    intro t hR
                    exact ih s₂ c b₀ t hwf₂ hlock₂ hb2 hR rest hlenr hep' w hrest hwin
                | deckStack x =>
                    obtain ⟨hlk, hb2⟩ := lockedness_deckStack hm2
                    refine solvable_of_pileStack_step_deckStack hwf hbot hm hm2 ?_
                    intro t hR
                    exact ih s₂ c b₀ t hwf₂ (hlk.trans hnotlock)
                      (hb2.trans hbot) hR rest hlenr hep' w hrest hwin
                | deckPile x b'' =>
                    have hnc : b'' ≠ Sum.inr c := cBlocked_deckPile hcm
                    -- the played card is stocked, c is visible: c ≠ x
                    have hmd2 := hm2
                    rw [apply_deckPile_iff] at hmd2
                    obtain ⟨hprev, _, _, _, _⟩ := hmd2
                    have hmem : x ∈ st.stock.cards := by
                      simp only [Cycle.prev] at hprev
                      split at hprev
                      · exact absurd hprev (by simp)
                      · exact List.mem_iff_getElem?.mpr ⟨st.stock.cursor - 1, hprev⟩
                    have hxc : c ≠ x := by
                      intro hxe
                      rw [← hxe] at hmem
                      exact Cycle.posOf_mem hmem (hwf.vis_off_cycle c (by
                        show (st.board.bottomOf c).isSome = true
                        rw [hbot]
                        rfl))
                    obtain ⟨hlk, hb2⟩ := lockedness_deckPile hm2 hxc
                    refine solvable_of_pileStack_step_deckPile hwf hbot hm hm2 hnc ?_
                    intro t hR
                    exact ih s₂ c b₀ t hwf₂ (hlk.trans hnotlock)
                      (hb2.trans hbot) hR rest hlenr hep' w hrest hwin
                | pileStack x =>
                    by_cases hxc : x = c
                    · subst hxc
                      exact solvable_of_pileStack_step_delete hm hrun hwin
                    · have hmx2 := hm2
                      rw [apply_pileStack_iff] at hmx2
                      obtain ⟨_, bx, hbx, _, _⟩ := hmx2
                      obtain ⟨hlk, hb2⟩ := lockedness_pileStack hm2 (Ne.symm hxc)
                      refine solvable_of_pileStack_step_pileStack hbot hbx hm hm2 hxc ?_
                      intro t hR
                      exact ih s₂ c b₀ t hwf₂ (hlk.trans hnotlock)
                        (hb2.trans hbot) hR rest hlenr hep' w hrest hwin
                | stackPile x b'' =>
                    obtain ⟨hnc, hσ⟩ := cBlocked_stackPile hcm
                    have hxc : c ≠ x := by
                      intro hxe
                      exact hσ (by rw [hxe])
                    obtain ⟨hlk, hb2⟩ := lockedness_stackPile hm2 hxc
                    refine solvable_of_pileStack_step_stackPile hbot hm hm2 hnc hσ ?_
                    intro t hR
                    exact ih s₂ c b₀ t hwf₂ (hlk.trans hnotlock)
                      (hb2.trans hbot) hR rest hlenr hep' w hrest hwin
                | pilePile x b'' =>
                    have hnc : b'' ≠ Sum.inr c := cBlocked_pilePile hcm
                    by_cases hxc : x = c
                    · rw [hxc] at hm2
                      -- the run-root replay: no IH needed
                      refine ⟨Move.stackPile c b'' :: rest, w, ?_, hwin⟩
                      simp only [State.run, pileStack_pilePile_stackPile hbot hrk hm hm2]
                      exact hrest
                    · obtain ⟨hlk, hb2⟩ := lockedness_pilePile hm2 (Ne.symm hxc)
                      refine solvable_of_pileStack_step_pilePile hbot hm hm2 hnc hxc ?_
                      intro t hR
                      exact ih s₂ c b₀ t hwf₂ (hlk.trans hnotlock)
                        (hb2.trans hbot) hR rest hlenr hep' w hrest hwin

/-- The induction step's common tail for the rung-pass search:
prefixing the (already replayed) first move onto the IH's
decomposition. -/
private theorem rung_prefix_cons {u s₂ : State} {m : Move} {c : Card} {R : Nat}
    {rest π₁ π₂ : List Move}
    (hm : u.apply m = some s₂)
    (hsplit : rest = π₁ ++ Move.pileStack c :: π₂)
    (hconj : ∀ u', s₂.run π₁ = some u' → u'.heights c.suit ≤ R) :
    ∃ ρ₁ ρ₂, (m :: rest) = ρ₁ ++ Move.pileStack c :: ρ₂ ∧
      (∀ u', u.run ρ₁ = some u' → u'.heights c.suit ≤ R) :=
  ⟨m :: π₁, π₂, by rw [hsplit]; simp, fun u' hu' => hconj u' (by
    simp only [State.run, hm] at hu'
    exact hu')⟩

/-- W2's core: a play whose end state strictly exceeds the bound `R`
(≥ the start's `c`-suit height) must contain the rung pass
`pileStack c` — the exceedance can only be the bump at `c`'s own
rung: a same-suit bump past `R` needs the unique `c`-suit card at
`toIdx R = toIdx c`, i.e. `c` itself, and `deckStack c` is impossible
(`c` never enters the stock cycle — the cycle only loses cards).  The
prefix up to the exhibited pass never exceeds `R`: the first
exceedance IS the pass. -/
private theorem rung_pass_aux {c : Card} {R : Nat} (hrk : c.rank.toIdx = R) :
    ∀ (π : List Move) (u : State) (w : State), u.run π = some w →
    u.heights c.suit ≤ R → c ∉ u.stock.cards → w.heights c.suit > R →
    ∃ π₁ π₂, π = π₁ ++ Move.pileStack c :: π₂ ∧
      (∀ u', u.run π₁ = some u' → u'.heights c.suit ≤ R) := by
  intro π
  induction π with
  | nil =>
      intro u w hrun hle _ hgt
      simp only [State.run] at hrun
      have hu : u = w := Option.some.inj hrun
      subst hu
      omega
  | cons m rest ih =>
      intro u w hrun hle hc hgt
      have hrun' := hrun
      simp only [State.run] at hrun'
      cases hm : u.apply m with
      | none => rw [hm] at hrun'; simp at hrun'
      | some s₂ =>
          rw [hm] at hrun'
          have hrest : s₂.run rest = some w := hrun'
          cases m with
          | pileStack x =>
              by_cases hxc : x = c
              · subst hxc
                refine ⟨[], rest, by simp, ?_⟩
                intro u' hu'
                simp only [State.run] at hu'
                have huu : u = u' := Option.some.inj hu'
                subst huu
                exact hle
              · have hmx := hm
                rw [apply_pileStack_iff] at hmx
                obtain ⟨_, _, _, hrkx, hsp⟩ := hmx
                have hle₂ : s₂.heights c.suit ≤ R := by
                  rw [hsp]
                  show (if c.suit = x.suit then u.heights c.suit + 1 else u.heights c.suit) ≤ R
                  by_cases hσ : c.suit = x.suit
                  · rw [if_pos hσ]
                    by_cases hlt : u.heights c.suit < R
                    · omega
                    · have hR : u.heights c.suit = R := by omega
                      have h1 : x.rank.toIdx = u.heights c.suit := by
                        rw [hσ]; exact hrkx
                      have h2 : x.rank.toIdx = c.rank.toIdx := by rw [h1, hR, hrk]
                      have h3 : x.rank = c.rank := Rank.toIdx_inj h2
                      exact absurd (show x = c by cases x; cases c; simp_all) hxc
                  · rw [if_neg hσ]; exact hle
                have hc₂ : c ∉ s₂.stock.cards := by rw [hsp]; exact hc
                obtain ⟨π₁, π₂, hsplit, hconj⟩ := ih s₂ w hrest hle₂ hc₂ hgt
                exact rung_prefix_cons hm hsplit hconj
          | draw =>
              have hmd := hm
              rw [apply_draw_iff] at hmd
              have hle₂ : s₂.heights c.suit ≤ R := by rw [hmd]; exact hle
              have hc₂ : c ∉ s₂.stock.cards := by
                rw [hmd]
                show c ∉ (u.stock.dealOnce u.drawStep).cards
                rw [Cycle.dealOnce_cards]
                exact hc
              obtain ⟨π₁, π₂, hsplit, hconj⟩ := ih s₂ w hrest hle₂ hc₂ hgt
              exact rung_prefix_cons hm hsplit hconj
          | reveal _ =>
              have hmr := hm
              rw [apply_reveal_iff] at hmr
              obtain ⟨_, _, _, _, _, _, _, hsr⟩ := hmr
              have hle₂ : s₂.heights c.suit ≤ R := by rw [hsr]; exact hle
              have hc₂ : c ∉ s₂.stock.cards := by rw [hsr]; exact hc
              obtain ⟨π₁, π₂, hsplit, hconj⟩ := ih s₂ w hrest hle₂ hc₂ hgt
              exact rung_prefix_cons hm hsplit hconj
          | deckPile _ _ =>
              have hmd := hm
              rw [apply_deckPile_iff] at hmd
              obtain ⟨_, _, _, _, hsd⟩ := hmd
              have hle₂ : s₂.heights c.suit ≤ R := by rw [hsd]; exact hle
              have hc₂ : c ∉ s₂.stock.cards := by
                rw [hsd]
                intro hmem
                exact hc (Cycle.mem_removeIdx _ _ hmem)
              obtain ⟨π₁, π₂, hsplit, hconj⟩ := ih s₂ w hrest hle₂ hc₂ hgt
              exact rung_prefix_cons hm hsplit hconj
          | deckStack x =>
              have hmd := hm
              rw [apply_deckStack_iff] at hmd
              obtain ⟨hprev, hrkx, hsd⟩ := hmd
              have hxc : x ≠ c := by
                intro hxe
                rw [hxe] at hprev
                have hmem : c ∈ u.stock.cards := by
                  simp only [Cycle.prev] at hprev
                  split at hprev
                  · exact absurd hprev (by simp)
                  · exact List.mem_iff_getElem?.mpr ⟨u.stock.cursor - 1, hprev⟩
                exact hc hmem
              have hle₂ : s₂.heights c.suit ≤ R := by
                rw [hsd]
                show (if c.suit = x.suit then u.heights c.suit + 1 else u.heights c.suit) ≤ R
                by_cases hσ : c.suit = x.suit
                · rw [if_pos hσ]
                  by_cases hlt : u.heights c.suit < R
                  · omega
                  · have hR : u.heights c.suit = R := by omega
                    have h1 : x.rank.toIdx = u.heights c.suit := by
                      rw [hσ]; exact hrkx
                    have h2 : x.rank.toIdx = c.rank.toIdx := by rw [h1, hR, hrk]
                    have h3 : x.rank = c.rank := Rank.toIdx_inj h2
                    exact absurd (show x = c by cases x; cases c; simp_all) hxc
                · rw [if_neg hσ]; exact hle
              have hc₂ : c ∉ s₂.stock.cards := by
                rw [hsd]
                intro hmem
                exact hc (Cycle.mem_removeIdx _ _ hmem)
              obtain ⟨π₁, π₂, hsplit, hconj⟩ := ih s₂ w hrest hle₂ hc₂ hgt
              exact rung_prefix_cons hm hsplit hconj
          | stackPile x _ =>
              have hms := hm
              rw [apply_stackPile_iff] at hms
              obtain ⟨_, _, _, _, hss⟩ := hms
              have hle₂ : s₂.heights c.suit ≤ R := by
                rw [hss]
                show (if c.suit = x.suit then u.heights c.suit - 1 else u.heights c.suit) ≤ R
                by_cases hσ : c.suit = x.suit
                · rw [if_pos hσ]; omega
                · rw [if_neg hσ]; exact hle
              have hc₂ : c ∉ s₂.stock.cards := by rw [hss]; exact hc
              obtain ⟨π₁, π₂, hsplit, hconj⟩ := ih s₂ w hrest hle₂ hc₂ hgt
              exact rung_prefix_cons hm hsplit hconj
          | pilePile _ _ =>
              have hmp := hm
              rw [apply_pilePile_iff] at hmp
              obtain ⟨_, _, _, _, _, _, hsp⟩ := hmp
              have hle₂ : s₂.heights c.suit ≤ R := by rw [hsp]; exact hle
              have hc₂ : c ∉ s₂.stock.cards := by rw [hsp]; exact hc
              obtain ⟨π₁, π₂, hsplit, hconj⟩ := ih s₂ w hrest hle₂ hc₂ hgt
              exact rung_prefix_cons hm hsplit hconj

/-- The rung pass exists (ENDGAME.md §5, W2 — first-exceedance form):
every winning play from a WF state where `pileStack c` is legal fires
`pileStack c` at some position, and no state on the prefix before the
exhibited pass has `c`'s suit height above the rung `st.heights
c.suit = toIdx c`.  (The height may dip below the rung before the
pass — an excursion — but never exceed it: the bump past the rung
reads `c`'s own card.)  STATEMENT REPAIRED (2026-09-14,
prover-confirmed witness `Temp/opencode/w2probe.lean`, #eval): the
draft's equality conjunct `u.heights c.suit = st.heights c.suit` was
FALSE — a worry-back of `c`'s suit before the rung pass (an excursion)
dips the height to `r - 1` on the forced prefix; the honest form is
`≤`, matching ENDGAME's own "first exceedance" reading. -/
theorem rung_pass_of_win {st : State} (hwf : st.WF) {c : Card} {s₁ : State}
    (hm : st.apply (Move.pileStack c) = some s₁) {π : List Move} {w : State}
    (hw : st.run π = some w) (hwin : w.isWin = true) :
    ∃ π₁ π₂, π = π₁ ++ Move.pileStack c :: π₂ ∧
      ∀ u, st.run π₁ = some u → u.heights c.suit ≤ st.heights c.suit := by
  have hmo := hm
  rw [apply_pileStack_iff] at hmo
  obtain ⟨_, _, hb, hrk, _⟩ := hmo
  have hvis : st.isVis c = true := by
    show (st.board.bottomOf c).isSome = true
    rw [hb]
    rfl
  have hc : c ∉ st.stock.cards := fun hmem =>
    Cycle.posOf_mem hmem (hwf.vis_off_cycle c hvis)
  have h13 : w.heights c.suit = 13 := by
    have h := hwin
    simp only [State.isWin] at h
    exact of_decide_eq_true (List.all_eq_true.mp h c.suit (Suit.mem_all c.suit))
  have hr : st.heights c.suit < 13 := by
    rw [← hrk]
    exact Rank.toIdx_lt c.rank
  have hgt : w.heights c.suit > st.heights c.suit := by rw [h13]; omega
  exact rung_pass_aux hrk π st w hw (Nat.le_refl _) hc hgt

/-- W3's adjacent case at the run level (ENDGAME.md §5 W3; the spread
version — the excursion pair with an intermediate blind segment — is
the next agent's: its `seatsOrReads` blindness predicate is a def-level
design choice, ENDGAME §7.2, and is state-dependent for the
run-carrying `pilePile` shapes): deleting a worry-back immediately
followed by its re-stack changes nothing — the composition is the
identity, so the rest of the play runs from the source state itself.
The apply-level cancellation is a hypothesis because its home
(`stackPile_pileStack_cancel`) is Dominance's, downstream of this
file: there, instantiate it with
`excursion_pair_delete_adjacent (stackPile_pileStack_cancel hwf hsp)`. -/
theorem excursion_pair_delete_adjacent {st : State} {x : Card}
    {s₁ : State} {π : List Move} {w : State}
    (hcancel : s₁.apply (Move.pileStack x) = some st)
    (hrun : s₁.run (Move.pileStack x :: π) = some w) :
    st.run π = some w := by
  simp only [State.run, hcancel] at hrun
  exact hrun

/-! ### W3's spread excursion pair (ENDGAME.md §5): the φ-simulation

The intermediate segment γ of an excursion pair replays from the
source state once the pair is deleted: replaying γ from `st` tracks
the source line `s₁ → …` through `excursionSim` (Frame.lean's φ — the
source minus `x`'s single board edge, the `x`-suit height one higher),
the pair's `pileStack x` CONVERGES the lines (the successor is the
replay state — the pair nets to identity), and the tail runs
verbatim.  The blindness guards are ENDGAME §7.2's move-only choice
(`seatsOrReads`, Frame.lean) plus the height-cell blindness
(`cSuitMove` below, frame-native by `Move.heightsOf_mem_reads_iff`).
The `aboveOf` corner (pilePile's self-landing guard reading THROUGH
`x`'s edge) is the walk-agreement form W3 consumes —
`aboveOf_detach_subset` above: the replay board's walk is CONTAINED in
the source's.  GREP-FIRST FINDING (2026-09-14): that subset form
already landed 2026-09-13 as `pileStack_comm_pilePile`'s guard, so no
duplicate walk lemma is written here.  What Frame's honest boundary
left open — the one-step replay itself — is closed below; its reveal
corner is WF's `vis_not_hidden` (`x`, seated at `b`, is never a hidden
pile's base card), which the move-only guard cannot see. -/

/-- The false half of `contains_iff_mem` (TwinSwap's
`lcontains_false_of_notMem`, upstream form — flagged for
consolidation with the contains kit above). -/
theorem contains_false_of_notMem {l : List Card} {d : Card} (h : d ∉ l) :
    l.contains d = false := by
  cases hb : l.contains d with
  | false => rfl
  | true => exact absurd ((contains_iff_mem l d).mp hb) h

/-- ENDGAME §7.2's height half of W3's blindness, frame-native: `m` is
a `c`-suit move when it reads `c`'s height cell — by
`Move.heightsOf_mem_reads_iff`, exactly the foundation moves
(`deckStack`/`pileStack`/`stackPile`) of a `c`-suit card. -/
def cSuitMove (c : Card) (m : Move) : Prop := Frame.heightsOf c.suit ∈ m.reads

/-- The hidden base card is hidden: `hiddenBase a = inr d` puts `d` in
the pile's hidden slice (the reveal corner's WF fact — a `seatsOrReads`-
clean move can still read the board through a hidden base, and `x`'s
exclusion from those is `vis_not_hidden`, not the move-only guard). -/
theorem hidden_mem_of_hiddenBase {st : State} {a : Anchor} {r d : Card}
    (hgt : st.topHidden a = some r) (hb : st.hiddenBase a = Sum.inr d) :
    d ∈ st.hidden a := by
  simp only [State.hiddenBase] at hb
  revert hb
  cases hs : ((st.hidden a).reverse.drop 1).head? with
  | none => intro hb; exact absurd hb (by simp)
  | some d' =>
      intro hb
      have hdd : d' = d := Sum.inr.inj hb
      obtain ⟨pre, hpre⟩ := hidden_split hs hgt
      rw [hpre, hdd]
      exact List.mem_append_right _ (by simp)

/-- φ at step 0: the worry-back successor and the source are already
in the simulation relation — the roundtrip `stackPile_pileStack_return`
carries the height/edge round trip wholesale (nothing sits on a
foundation-passed card, so the fresh seat is `x`'s only edge). -/
theorem excursionSim_of_stackPile {st : State} (hwf : st.WF) {x : Card} {b : Base}
    {s₁ : State} (hm : st.apply (Move.stackPile x b) = some s₁) :
    excursionSim x b s₁ st := by
  have hret := stackPile_pileStack_return hwf hm
  rw [apply_pileStack_iff] at hret
  obtain ⟨htopx, b', hb', -, hst⟩ := hret
  rw [apply_stackPile_iff] at hm
  obtain ⟨-, -, bd, hatt, hs₁⟩ := hm
  have hsb : s₁.board = bd := by rw [hs₁]
  have htopb : bd.topOf b = some x := Board.attach_topOf st.board b x hatt
  have hbb : b' = b := by
    have hbot : bd.bottomOf x = some b := (Board.bottomOf_eq bd x b).mpr htopb
    rw [← hsb] at hbot
    rw [hbot] at hb'
    exact (Option.some.inj hb').symm
  subst hbb
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, htopx⟩
  · rw [hst]
  · rw [hst]
  · rw [hst]
  · rw [hst]
  · rw [hst]
    show s₁.heights x.suit + 1 =
        (if x.suit = x.suit then s₁.heights x.suit + 1 else s₁.heights x.suit)
    rw [if_pos rfl]
  · intro s hs
    rw [hst]
    show s₁.heights s = (if s = x.suit then s₁.heights s + 1 else s₁.heights s)
    rw [if_neg hs]
  · rw [hsb]; exact htopb
  · rw [hst]

/-- The convergence at the pair's end: from a φ-pair, the source's
`pileStack x` lands exactly on the target — the excursion pair nets to
the identity, so the replay state after γ IS the source state after the
pair. -/
theorem excursionSim_converge {x : Card} {b : Base} {σ τ σ₂ : State}
    (hsim : excursionSim x b σ τ) (h : σ.apply (Move.pileStack x) = some σ₂) :
    σ₂ = τ := by
  obtain ⟨hdeal, hdpt, hstock, hds, hhx, hho, htopb, hbrw, -⟩ := hsim
  rw [apply_pileStack_iff] at h
  obtain ⟨-, b', hb', -, hst⟩ := h
  have hb : σ.board.bottomOf x = some b := (Board.bottomOf_eq σ.board x b).mpr htopb
  rw [hb] at hb'
  obtain rfl := Option.some.inj hb'
  rw [hst]
  refine state_ext hdeal ?_ ?_ hdpt hstock hds
  · show σ.board.detach b = τ.board
    exact hbrw.symm
  · funext s
    by_cases hss : s = x.suit
    · subst hss
      show (if x.suit = x.suit then σ.heights x.suit + 1 else σ.heights x.suit)
          = τ.heights x.suit
      rw [if_pos rfl]
      exact hhx
    · show (if s = x.suit then σ.heights s + 1 else σ.heights s) = τ.heights s
      rw [if_neg hss]
      exact hho s hss

/-- The W3 one-step replay — Frame's honest boundary, closed: a
γ-move that neither mentions `x` (moved card or base card —
`seatsOrReads`) nor reads the `x`-suit height cell replays from the
φ-target, and the successors are φ-related.  The corners:
pilePile's self-landing guard reads the run walk through `x`'s edge —
`aboveOf_detach_subset` (the replay's walk is contained in the
source's, so the guard passes a fortiori); the board edits are
single-base updates away from `b`, commuting with the `detach b`
(`attach_detach_comm`, `detach_detach_comm`); reveal's hidden base is
never `x` (WF's `vis_not_hidden`). -/
theorem excursionSim_step {x : Card} {b : Base} {σ τ : State} (hwf : σ.WF)
    (hsim : excursionSim x b σ τ) {m : Move}
    (hseats : m.seatsOrReads x = false) (hblind : Frame.heightsOf x.suit ∉ m.reads)
    {σ' : State} (h : σ.apply m = some σ') :
    ∃ τ', τ.apply m = some τ' ∧ excursionSim x b σ' τ' := by
  obtain ⟨hdeal, hdpt, hstock, hds, hhx, hho, htopb, hbrw, htopx⟩ := hsim
  have hvisx : σ.isVis x = true := by
    show (σ.board.bottomOf x).isSome = true
    rw [(Board.bottomOf_eq σ.board x b).mpr htopb]
    rfl
  -- the boards differ at `b` only, the τ-side being the detach
  have htopeq : ∀ b' : Base, b' ≠ b → τ.board.topOf b' = σ.board.topOf b' := by
    intro b' hb'ne
    rw [hbrw]
    exact Board.detach_topOf_ne _ _ _ hb'ne
  have hboteq : ∀ d : Card, d ≠ x → τ.board.bottomOf d = σ.board.bottomOf d := by
    intro d hdne
    rw [hbrw]
    exact bottomOf_detach_ne htopb hdne
  have hisVis : ∀ d : Card, d ≠ x → σ.isVis d = τ.isVis d := by
    intro d hdne
    show (σ.board.bottomOf d).isSome = (τ.board.bottomOf d).isSome
    rw [hboteq d hdne]
  have hcanPlace : ∀ (c : Card) (b' : Base), b' ≠ b → b' ≠ Sum.inr x →
      σ.canPlace c b' = τ.canPlace c b' := by
    intro c b' hb'ne hb'x
    have htop' : τ.board.topOf b' = σ.board.topOf b' := htopeq b' hb'ne
    cases b' with
    | inl a =>
        simp only [State.canPlace]
        rw [htop']
    | inr d =>
        have hdne : d ≠ x := by
          intro hcon
          exact hb'x (by rw [hcon])
        simp only [State.canPlace]
        rw [htop'.symm, hisVis d hdne]
  cases m with
  | draw =>
      obtain rfl := apply_draw_iff.mp h
      refine ⟨{τ with stock := τ.stock.dealOnce τ.drawStep},
        apply_draw_iff.mpr rfl, ?_⟩
      refine ⟨hdeal, hdpt, ?_, hds, hhx, fun s hs => hho s hs, htopb, hbrw, htopx⟩
      show σ.stock.dealOnce σ.drawStep = τ.stock.dealOnce τ.drawStep
      rw [hstock, hds]
  | reveal c =>
      have hcx : c ≠ x := by
        have h1 : decide (c = x) = false := hseats
        exact of_decide_eq_false h1
      rw [apply_reveal_iff] at h
      obtain ⟨htop, r, a, bd, hbot, hpile, hatt, rfl⟩ := h
      -- the deal/depths-blind views agree on the τ side
      have hpileτ : τ.pileOfTopHidden r = some a := by
        rw [pileOfTopHidden_congr hdeal.symm hdpt.symm r]
        exact hpile
      have hhbτ : τ.hiddenBase a = σ.hiddenBase a :=
        hiddenBase_congr hdeal.symm hdpt.symm a
      have hth : σ.topHidden a = some r :=
        of_decide_eq_true (findFirst_mem _ _ _ hpile).2
      have hrmem : r ∈ σ.hidden a := mem_of_getLast hth
      have hrne : r ≠ x := by
        intro hcon
        rw [hcon] at hrmem
        exact hwf.vis_not_hidden x hvisx a hrmem
      -- τ's guards
      have hinr : (Sum.inr c : Base) ≠ b := by
        intro hcon
        rw [← hcon] at htopb
        rw [htop] at htopb
        exact absurd htopb (by simp)
      have htopτ : τ.board.topOf (Sum.inr c) = none := by
        rw [htopeq _ hinr]
        exact htop
      have hbotτ : τ.board.bottomOf c = some (Sum.inr r) := by
        rw [hboteq c hcx]
        exact hbot
      obtain ⟨htopb'', hbotr⟩ := (Board.attach_eq_some_iff _ _ _).mp (by rw [hatt]; simp)
      have hbne : σ.hiddenBase a ≠ b := by
        intro hcon
        rw [hcon] at htopb''
        rw [htopb] at htopb''
        exact absurd htopb'' (by simp)
      have hbasein : σ.hiddenBase a ≠ Sum.inr x := by
        intro hcon
        exact hwf.vis_not_hidden x hvisx a (hidden_mem_of_hiddenBase hth hcon)
      have htoph : τ.board.topOf (σ.hiddenBase a) = none := by
        rw [htopeq _ hbne]
        exact htopb''
      have hbotrτ : τ.board.bottomOf r = none := by
        rw [hboteq r hrne]
        exact hbotr
      obtain ⟨bdτ, hattτ⟩ : ∃ bdτ, τ.board.attach (σ.hiddenBase a) r = some bdτ := by
        have hne : τ.board.attach (σ.hiddenBase a) r ≠ none :=
          (Board.attach_eq_some_iff _ _ _).mpr ⟨htoph, hbotrτ⟩
        cases hh : τ.board.attach (σ.hiddenBase a) r with
        | none => rw [hh] at hne; simp at hne
        | some bdτ => exact ⟨bdτ, rfl⟩
      have hattτ' : τ.board.attach (τ.hiddenBase a) r = some bdτ := by
        rw [hhbτ]
        exact hattτ
      refine ⟨{τ with
        board := bdτ,
        depths := fun a' => if a' = a then τ.depths a - 1 else τ.depths a'}, ?_, ?_⟩
      · rw [apply_reveal_iff]
        exact ⟨htopτ, r, a, bdτ, hbotτ, hpileτ, hattτ', rfl⟩
      · refine ⟨hdeal, ?_, hstock, hds, hhx, fun s hs => hho s hs, ?_, ?_, ?_⟩
        · show (fun a' => if a' = a then σ.depths a - 1 else σ.depths a') =
              (fun a' => if a' = a then τ.depths a - 1 else τ.depths a')
          rw [hdpt]
        · show bd.topOf b = some x
          rw [Board.attach_topOf_ne _ _ _ hatt hbne.symm]
          exact htopb
        · show bdτ = bd.detach b
          rw [hbrw] at hattτ
          exact (attach_detach_comm hbne hatt hattτ).symm
        · show bd.topOf (Sum.inr x) = none
          rw [Board.attach_topOf_ne _ _ _ hatt hbasein.symm]
          exact htopx
  | deckPile c b'' =>
      have h1 : decide (c = x) = false ∧ (b''.seats x) = false := by
        have h2 := hseats
        simp only [Move.seatsOrReads, Bool.or_eq_false_iff] at h2
        exact h2
      obtain ⟨hcx', hseatsb⟩ := h1
      have hcx : c ≠ x := of_decide_eq_false hcx'
      have hb''x : b'' ≠ Sum.inr x := by
        intro hcon
        rw [hcon] at hseatsb
        simp [Base.seats] at hseatsb
      rw [apply_deckPile_iff] at h
      obtain ⟨hprev, hcp, bd, hatt, rfl⟩ := h
      obtain ⟨htopb'', hbotc⟩ := (Board.attach_eq_some_iff _ _ _).mp (by rw [hatt]; simp)
      have hb''ne : b'' ≠ b := by
        intro hcon
        rw [hcon] at htopb''
        rw [htopb] at htopb''
        exact absurd htopb'' (by simp)
      have hbotcτ : τ.board.bottomOf c = none := by
        rw [hboteq c hcx]
        exact hbotc
      obtain ⟨bdτ, hattτ⟩ : ∃ bdτ, τ.board.attach b'' c = some bdτ := by
        have hne : τ.board.attach b'' c ≠ none :=
          (Board.attach_eq_some_iff _ _ _).mpr
            ⟨by rw [htopeq b'' hb''ne]; exact htopb'', hbotcτ⟩
        cases hh : τ.board.attach b'' c with
        | none => rw [hh] at hne; simp at hne
        | some bdτ => exact ⟨bdτ, rfl⟩
      refine ⟨{τ with
        board := bdτ,
        stock := τ.stock.removeAt (τ.stock.cursor - 1)}, ?_, ?_⟩
      · rw [apply_deckPile_iff]
        exact ⟨by rw [← hstock]; exact hprev,
          by rw [← hcanPlace c b'' hb''ne hb''x]; exact hcp, bdτ, hattτ, rfl⟩
      · refine ⟨hdeal, hdpt, ?_, hds, hhx, fun s hs => hho s hs, ?_, ?_, ?_⟩
        · show σ.stock.removeAt (σ.stock.cursor - 1) =
              τ.stock.removeAt (τ.stock.cursor - 1)
          rw [hstock]
        · show bd.topOf b = some x
          rw [Board.attach_topOf_ne _ _ _ hatt (Ne.symm hb''ne)]
          exact htopb
        · show bdτ = bd.detach b
          rw [hbrw] at hattτ
          exact (attach_detach_comm hb''ne hatt hattτ).symm
        · show bd.topOf (Sum.inr x) = none
          rw [Board.attach_topOf_ne _ _ _ hatt (Ne.symm hb''x)]
          exact htopx
  | deckStack c =>
      have hsc : x.suit ≠ c.suit := by
        intro hcon
        exact hblind (by rw [hcon]; simp [Move.reads])
      rw [apply_deckStack_iff] at h
      obtain ⟨hprev, hrk, rfl⟩ := h
      refine ⟨{τ with
        stock := τ.stock.removeAt (τ.stock.cursor - 1),
        heights := fun s => if s = c.suit then τ.heights s + 1 else τ.heights s}, ?_, ?_⟩
      · rw [apply_deckStack_iff]
        exact ⟨by rw [← hstock]; exact hprev,
          by rw [← hho c.suit (Ne.symm hsc)]; exact hrk, rfl⟩
      · refine ⟨hdeal, hdpt, ?_, hds, ?_, ?_, htopb, hbrw, htopx⟩
        · show σ.stock.removeAt (σ.stock.cursor - 1) =
              τ.stock.removeAt (τ.stock.cursor - 1)
          rw [hstock]
        · show (if x.suit = c.suit then σ.heights x.suit + 1 else σ.heights x.suit) + 1 =
              (if x.suit = c.suit then τ.heights x.suit + 1 else τ.heights x.suit)
          rw [if_neg hsc, if_neg hsc]
          exact hhx
        · intro s hs
          show (if s = c.suit then σ.heights s + 1 else σ.heights s) =
              (if s = c.suit then τ.heights s + 1 else τ.heights s)
          by_cases hsc' : s = c.suit
          · rw [if_pos hsc', if_pos hsc', hho s hs]
          · rw [if_neg hsc', if_neg hsc']
            exact hho s hs
  | pileStack c =>
      have hcx : c ≠ x := by
        have h1 : decide (c = x) = false := hseats
        exact of_decide_eq_false h1
      have hsc : x.suit ≠ c.suit := by
        intro hcon
        exact hblind (by rw [hcon]; simp [Move.reads])
      rw [apply_pileStack_iff] at h
      obtain ⟨htop, b₀, hb₀, hrk, rfl⟩ := h
      have hinr : (Sum.inr c : Base) ≠ b := by
        intro hcon
        rw [← hcon] at htopb
        rw [htop] at htopb
        exact absurd htopb (by simp)
      have htopτ : τ.board.topOf (Sum.inr c) = none := by
        rw [htopeq _ hinr]
        exact htop
      have hb₀τ : τ.board.bottomOf c = some b₀ := by
        rw [hboteq c hcx]
        exact hb₀
      have hbbne : b ≠ b₀ := by
        intro hcon
        rw [hcon] at htopb
        exact hcx (Option.some.inj
          (htopb.symm.trans ((Board.bottomOf_eq σ.board c b₀).mp hb₀))).symm
      have hb₀x : (Sum.inr x : Base) ≠ b₀ := by
        intro hcon
        rw [hcon] at htopx
        exact absurd (htopx.symm.trans ((Board.bottomOf_eq σ.board c b₀).mp hb₀)) (by simp)
      refine ⟨{τ with
        board := τ.board.detach b₀,
        heights := fun s => if s = c.suit then τ.heights s + 1 else τ.heights s}, ?_, ?_⟩
      · rw [apply_pileStack_iff]
        exact ⟨htopτ, b₀, hb₀τ,
          by rw [← hho c.suit (Ne.symm hsc)]; exact hrk, rfl⟩
      · refine ⟨hdeal, hdpt, hstock, hds, ?_, ?_, ?_, ?_, ?_⟩
        · show (if x.suit = c.suit then σ.heights x.suit + 1 else σ.heights x.suit) + 1 =
              (if x.suit = c.suit then τ.heights x.suit + 1 else τ.heights x.suit)
          rw [if_neg hsc, if_neg hsc]
          exact hhx
        · intro s hs
          show (if s = c.suit then σ.heights s + 1 else σ.heights s) =
              (if s = c.suit then τ.heights s + 1 else τ.heights s)
          by_cases hsc' : s = c.suit
          · rw [if_pos hsc', if_pos hsc', hho s hs]
          · rw [if_neg hsc', if_neg hsc']
            exact hho s hs
        · show (σ.board.detach b₀).topOf b = some x
          rw [Board.detach_topOf_ne _ _ _ hbbne]
          exact htopb
        · show τ.board.detach b₀ = (σ.board.detach b₀).detach b
          rw [hbrw]
          exact detach_detach_comm hbbne
        · show (σ.board.detach b₀).topOf (Sum.inr x) = none
          rw [Board.detach_topOf_ne _ _ _ hb₀x]
          exact htopx
  | stackPile c b'' =>
      have h1 : decide (c = x) = false ∧ (b''.seats x) = false := by
        have h2 := hseats
        simp only [Move.seatsOrReads, Bool.or_eq_false_iff] at h2
        exact h2
      obtain ⟨hcx', hseatsb⟩ := h1
      have hcx : c ≠ x := of_decide_eq_false hcx'
      have hb''x : b'' ≠ Sum.inr x := by
        intro hcon
        rw [hcon] at hseatsb
        simp [Base.seats] at hseatsb
      have hsc : x.suit ≠ c.suit := by
        intro hcon
        exact hblind (by rw [hcon]; simp [Move.reads])
      rw [apply_stackPile_iff] at h
      obtain ⟨hrk, hcp, bd, hatt, rfl⟩ := h
      obtain ⟨htopb'', hbotc⟩ := (Board.attach_eq_some_iff _ _ _).mp (by rw [hatt]; simp)
      have hb''ne : b'' ≠ b := by
        intro hcon
        rw [hcon] at htopb''
        rw [htopb] at htopb''
        exact absurd htopb'' (by simp)
      have hbotcτ : τ.board.bottomOf c = none := by
        rw [hboteq c hcx]
        exact hbotc
      obtain ⟨bdτ, hattτ⟩ : ∃ bdτ, τ.board.attach b'' c = some bdτ := by
        have hne : τ.board.attach b'' c ≠ none :=
          (Board.attach_eq_some_iff _ _ _).mpr
            ⟨by rw [htopeq b'' hb''ne]; exact htopb'', hbotcτ⟩
        cases hh : τ.board.attach b'' c with
        | none => rw [hh] at hne; simp at hne
        | some bdτ => exact ⟨bdτ, rfl⟩
      refine ⟨{τ with
        board := bdτ,
        heights := fun s => if s = c.suit then τ.heights s - 1 else τ.heights s}, ?_, ?_⟩
      · rw [apply_stackPile_iff]
        exact ⟨by rw [← hho c.suit (Ne.symm hsc)]; exact hrk,
          by rw [← hcanPlace c b'' hb''ne hb''x]; exact hcp, bdτ, hattτ, rfl⟩
      · refine ⟨hdeal, hdpt, hstock, hds, ?_, ?_, ?_, ?_, ?_⟩
        · show (if x.suit = c.suit then σ.heights x.suit - 1 else σ.heights x.suit) + 1 =
              (if x.suit = c.suit then τ.heights x.suit - 1 else τ.heights x.suit)
          rw [if_neg hsc, if_neg hsc]
          exact hhx
        · intro s hs
          show (if s = c.suit then σ.heights s - 1 else σ.heights s) =
              (if s = c.suit then τ.heights s - 1 else τ.heights s)
          by_cases hsc' : s = c.suit
          · rw [if_pos hsc', if_pos hsc', hho s hs]
          · rw [if_neg hsc', if_neg hsc']
            exact hho s hs
        · show bd.topOf b = some x
          rw [Board.attach_topOf_ne _ _ _ hatt (Ne.symm hb''ne)]
          exact htopb
        · show bdτ = bd.detach b
          rw [hbrw] at hattτ
          exact (attach_detach_comm hb''ne hatt hattτ).symm
        · show bd.topOf (Sum.inr x) = none
          rw [Board.attach_topOf_ne _ _ _ hatt (Ne.symm hb''x)]
          exact htopx
  | pilePile c b'' =>
      have h1 : decide (c = x) = false ∧ (b''.seats x) = false := by
        have h2 := hseats
        simp only [Move.seatsOrReads, Bool.or_eq_false_iff] at h2
        exact h2
      obtain ⟨hcx', hseatsb⟩ := h1
      have hcx : c ≠ x := of_decide_eq_false hcx'
      have hb''x : b'' ≠ Sum.inr x := by
        intro hcon
        rw [hcon] at hseatsb
        simp [Base.seats] at hseatsb
      rw [apply_pilePile_iff] at h
      obtain ⟨b₀, hb₀, hne, hcmr, bd, hatt, rfl⟩ := h
      -- the self-landing guard's σ-side, b''-shaped
      have hguardmem : ∀ d : Card, b'' = Sum.inr d →
          (σ.board.aboveOf c).contains d = false := by
        intro d hd
        have hg := hcmr
        simp only [State.canMoveRun, hd] at hg
        have h2 := (Bool.and_eq_true_iff.mp hg).2
        have h3 : (!(σ.board.aboveOf c).contains d) = true := h2
        rw [Bool.not_eq_true'] at h3
        exact h3
      have hcpσ : σ.canPlace c b'' = true := by
        have hg := hcmr
        simp only [State.canMoveRun] at hg
        exact (Bool.and_eq_true_iff.mp hg).1
      have htopb'' : σ.board.topOf b'' = none := by
        have hg := hcpσ
        simp only [State.canPlace] at hg
        exact of_decide_eq_true (Bool.and_eq_true_iff.mp hg).1
      have hb''ne : b'' ≠ b := by
        intro hcon
        rw [hcon] at htopb''
        rw [htopb] at htopb''
        exact absurd htopb'' (by simp)
      have hb₀τ : τ.board.bottomOf c = some b₀ := by
        rw [hboteq c hcx]
        exact hb₀
      have htopb₀τ : τ.board.topOf b₀ = some c :=
        (Board.bottomOf_eq τ.board c b₀).mp hb₀τ
      have hbbne : b ≠ b₀ := by
        intro hcon
        rw [hcon] at htopb
        exact hcx (Option.some.inj
          (htopb.symm.trans ((Board.bottomOf_eq σ.board c b₀).mp hb₀))).symm
      have hcmrτ : τ.canMoveRun c b'' = true := by
        simp only [State.canMoveRun, Bool.and_eq_true_iff]
        refine ⟨by rw [← hcanPlace c b'' hb''ne hb''x]; exact hcpσ, ?_⟩
        cases b'' with
        | inl a => rfl
        | inr d'' =>
            have hct : (τ.board.aboveOf c).contains d'' = false := by
              refine contains_false_of_notMem (fun hm => ?_)
              rw [hbrw] at hm
              exact absurd ((contains_iff_mem _ _).mpr (aboveOf_detach_subset hm))
                (by rw [hguardmem d'' rfl]; simp)
            show (!(τ.board.aboveOf c).contains d'') = true
            rw [hct]
            rfl
      have hbdettop : (τ.board.detach b₀).topOf b'' = none := by
        rw [Board.detach_topOf_ne _ _ _ (Ne.symm hne), htopeq b'' hb''ne]
        exact htopb''
      have hbdetbot : (τ.board.detach b₀).bottomOf c = none :=
        Board.bottomOf_detach_self htopb₀τ
      obtain ⟨bdτ, hattτ⟩ : ∃ bdτ, (τ.board.detach b₀).attach b'' c = some bdτ := by
        have hne' : (τ.board.detach b₀).attach b'' c ≠ none :=
          (Board.attach_eq_some_iff _ _ _).mpr ⟨hbdettop, hbdetbot⟩
        cases hh : (τ.board.detach b₀).attach b'' c with
        | none => rw [hh] at hne'; simp at hne'
        | some bdτ => exact ⟨bdτ, rfl⟩
      refine ⟨{τ with board := bdτ}, ?_, ?_⟩
      · rw [apply_pilePile_iff]
        exact ⟨b₀, hb₀τ, hne, hcmrτ, bdτ, hattτ, rfl⟩
      · refine ⟨hdeal, hdpt, hstock, hds, hhx, fun s hs => hho s hs, ?_, ?_, ?_⟩
        · show bd.topOf b = some x
          rw [Board.attach_topOf_ne _ _ _ hatt (Ne.symm hb''ne),
              Board.detach_topOf_ne _ _ _ hbbne]
          exact htopb
        · show bdτ = bd.detach b
          rw [hbrw] at hattτ
          have hattτ' : ((σ.board.detach b₀).detach b).attach b'' c = some bdτ := by
            rw [← detach_detach_comm hbbne]
            exact hattτ
          exact (attach_detach_comm hb''ne hatt hattτ').symm
        · show bd.topOf (Sum.inr x) = none
          have hb₀x : (Sum.inr x : Base) ≠ b₀ := by
            intro hcon
            rw [hcon] at htopx
            exact absurd (htopx.symm.trans ((Board.bottomOf_eq σ.board c b₀).mp hb₀))
              (by simp)
          rw [Board.attach_topOf_ne _ _ _ hatt (Ne.symm hb''x),
              Board.detach_topOf_ne _ _ _ hb₀x]
          exact htopx

/-- The φ-simulation along a whole segment: a γ of `seatsOrReads`-clean,
`x`-suit-height-blind moves replays from the φ-target, ending φ-related —
the induction packaging of `excursionSim_step`. -/
theorem excursionSim_run {x : Card} {b : Base} :
    ∀ (γ : List Move) (σ τ : State), σ.WF → excursionSim x b σ τ →
      ∀ (σend : State), σ.run γ = some σend →
        (∀ m ∈ γ, m.seatsOrReads x = false ∧ Frame.heightsOf x.suit ∉ m.reads) →
        ∃ τend, τ.run γ = some τend ∧ excursionSim x b σend τend := by
  intro γ
  induction γ with
  | nil =>
      intro σ τ _ hsim σend hγ _
      simp only [State.run] at hγ
      obtain rfl := Option.some.inj hγ
      exact ⟨τ, rfl, hsim⟩
  | cons m ms ih =>
      intro σ τ hwf hsim σend hγ hgd
      simp only [State.run] at hγ
      cases hm : σ.apply m with
      | none => rw [hm] at hγ; simp at hγ
      | some σ' =>
          rw [hm] at hγ
          have hrest : σ'.run ms = some σend := hγ
          obtain ⟨hseats, hblind⟩ := hgd m (by simp)
          obtain ⟨τ', hτ', hsim'⟩ := excursionSim_step hwf hsim hseats hblind hm
          obtain ⟨τend, hrun', hsim''⟩ :=
            ih σ' τ' (apply_wf hwf m σ' hm) hsim' σend hrest
              (fun m' hm' => hgd m' (by simp [hm']))
          refine ⟨τend, ?_, hsim''⟩
          simp only [State.run]
          rw [hτ']
          exact hrun'

set_option linter.unusedVariables false in
/-- **W3, the spread excursion pair (ENDGAME.md §5)**: deleting a
worry-back/re-stack pair `[stackPile x b, γ…, pileStack x]` from a
winning play keeps the run — the composition is the identity through
the φ-simulation: the intermediate γ is blind to exactly the two things
the pair changes (`seatsOrReads x`: no move mentions `x`'s seat;
`cSuitMove c`: no move reads the dropped `x`-suit height cell), so it
replays from the source state itself, and the pair's second half
converges the lines — the state after the pair IS the state after γ
alone, so the tail `π₂` runs verbatim to the same `w`.

STATEMENT REPAIRED (2026-09-14): ENDGAME §5's draft concluded
`∃ π', st.run (γ ++ π₂) = some w ∧ …` — the ellipsis was never spelled
out and the binder was dangling (π' never appears again).  The honest
conclusion is the concrete deletion `st.run (γ ++ π₂) = some w`, with
`π' := γ ++ π₂` witnessing any existential packaging and
`(γ ++ π₂).length + 2` = the original play's length supplying W5's
`L ↓` by arithmetic.  `hrk` (the draft's shifted rung guard) is kept
for the draft's shape; it is derivable from `hrun` (the worry-back's
own legality). -/
theorem excursion_pair_delete {st : State} (hwf : st.WF) {c x : Card} {b : Base}
    {γ π₂ : List Move} {w : State} (hσ : x.suit = c.suit)
    (hrk : x.rank.toIdx + 1 = st.heights x.suit)
    (hrun : st.run (Move.stackPile x b :: γ ++ Move.pileStack x :: π₂) = some w)
    (hblind : ∀ m ∈ γ, m.seatsOrReads x = false ∧ ¬ cSuitMove c m) :
    st.run (γ ++ π₂) = some w := by
  -- the draft's surface `stackPile x b :: γ ++ pileStack x :: π₂` parses
  -- append-headed (`::` binds tighter than `++`); the cons form is the
  -- same list by `List.cons_append`
  rw [List.cons_append] at hrun
  simp only [State.run] at hrun
  cases hst : st.apply (Move.stackPile x b) with
  | none => rw [hst] at hrun; simp at hrun
  | some s₁ =>
      rw [hst] at hrun
      have hrest : s₁.run (γ ++ Move.pileStack x :: π₂) = some w := hrun
      rw [State.run_append] at hrest
      obtain ⟨u, hu, hv⟩ := Option.bind_eq_some_iff.mp hrest
      simp only [State.run] at hv
      cases hq : u.apply (Move.pileStack x) with
      | none => rw [hq] at hv; simp at hv
      | some v =>
          rw [hq] at hv
          have hpx : u.apply (Move.pileStack x) = some v := hq
          have hπ₂ : v.run π₂ = some w := hv
          have hgd : ∀ m ∈ γ, m.seatsOrReads x = false ∧
              Frame.heightsOf x.suit ∉ m.reads := by
            intro m hm
            obtain ⟨hseats, hcsm⟩ := hblind m hm
            refine ⟨hseats, ?_⟩
            intro hmem
            rw [hσ] at hmem
            exact hcsm hmem
          obtain ⟨τ₁, hτrun, hsim₁⟩ :=
            excursionSim_run γ s₁ st (apply_wf hwf (Move.stackPile x b) s₁ hst)
              (excursionSim_of_stackPile hwf hst) u hu hgd
          have hconv : v = τ₁ := excursionSim_converge hsim₁ hpx
          rw [State.run_append, hτrun, ← hconv]
          exact hπ₂

/-! ### W4 — the certificate form (ENDGAME.md §8.3, candidate (c) as
picked 2026-09-14): the forced-park certificate, the repaired crux.

TOMBSTONE (2026-09-14, the REFUTED-archive discipline; the falsity
knowledge is the user's, the decision recorded in FARM.md's crux ledger
"REFORMULATION DECISION"; the design is ENDGAME.md §8).  The staged
crux

    theorem solvable_of_pileStack {st : State} (hwf : st.WF) {c : Card}
        {s₁ : State} (hnotlock : st.isLocked c = false)
        (hm : st.apply (Move.pileStack c) = some s₁)
        (hsol : st.solvableFrom) : s₁.solvableFrom

is FALSE at the forced-park corner (ENDGAME §8.0's (iii)): the twin
seat unavailable (hidden / foundation-passed / a deal-inherited
non-fitting occupier), the tenant unstackable (no `hsafe` here, by
design), no rank-mate return for `c` — F2 (`Card.only_blocker_is_twin`)
makes the twin the ONLY alternative seat, so a park on `c` can be
forced: the source's win may ride the parked run through `c`'s seat,
which `s₁` (c detached, the seat gone) cannot reproduce.  The repair is
NOT a guard (no `+hsafe`, no `initialReachable` scoping): the
certificate below is an ADDED CONCLUSION — the falsity quarantined in
a named, probe-able predicate, the crux's hypotheses untouched. -/

/-- The forced-park certificate (ENDGAME §8.3 (c), the draft def): the
    corner where no pre-pass canonicalization removes a park on `c` —
    the twin seat is unavailable (hidden, foundation-passed, or
    occupied: not visible-AND-bare) AND no rank-mate return for `c`
    exists (no visible, free `d` with `canSitOn c d`).  The two arms
    are the negations of the old W4a/W4c licenses (§5's `hlic` first
    and third disjuncts); the tenant-unstackability arm (W4b's, the
    second disjunct) is play-level and stays OUT — the
    `toEngine_lifts` mistake class (ENDGAME §6, W4c's note).  Probed
    2026-09-14 (`Temp/opencode/fpprobe.lean`, #eval): TRUE at the
    unavailable-, occupied- and non-fitting-occupier-twin corners,
    FALSE under either license.  Width note (the (c-γ) exactness gate):
    the occupied-by-FITTING-cargo corner (ii) satisfies arm 1 without
    being a true corner — the descent's exchange step absorbs it, and
    under `hsafe` channel A does (the Dominance bridge's [GAP]); the
    width is the price of state-level probe-ability. -/
def State.forcedPark (st : State) (c : Card) : Prop :=
  ¬(st.isVis c.flipSuit = true ∧ st.board.topOf (Sum.inr c.flipSuit) = none) ∧
  ∀ d, canSitOn c d = true → ¬(st.isVis d = true ∧ st.board.topOf (Sum.inr d) = none)

/-- Exactness probe (c1), the twin half: a visible, BARE twin seat —
    the redirect target — falsifies the certificate (with the twin
    licensed, a park on `c` is never forced). -/
theorem State.not_forcedPark_of_twin_seat {st : State} {c : Card}
    (hvis : st.isVis c.flipSuit = true)
    (hfree : st.board.topOf (Sum.inr c.flipSuit) = none) : ¬st.forcedPark c := by
  intro ⟨harm, _⟩
  exact harm ⟨hvis, hfree⟩

/-- Exactness probe (c1), the rank-mate half: a visible, free rank-mate
    return for `c` falsifies the certificate (the worry-back lands
    there — the old W4c channel). -/
theorem State.not_forcedPark_of_rank_mate {st : State} {c d : Card}
    (hfit : canSitOn c d = true) (hvis : st.isVis d = true)
    (hfree : st.board.topOf (Sum.inr d) = none) : ¬st.forcedPark c := by
  intro ⟨_, harm⟩
  exact harm d hfit ⟨hvis, hfree⟩

/-- The repaired crux's disjunct-1, standalone: a winning play whose
    pre-rung-pass prefix is `cBlocked`-clean replays from the stack
    successor — the W1 scaffold (`solvable_of_pileStack_aux`)
    consumed VERBATIM (its ∃-hypothesis IS the clean decomposition;
    ENDGAME §8.3: the LANDED aux IS disjunct-1), the base extracted
    from `hm` itself.  Everything the repaired crux still owes lives in
    `rungNormal_or_forcedPark` below. -/
theorem solvable_of_pileStack_of_rungNormal {st : State} (hwf : st.WF) {c : Card}
    {s₁ : State}
    (hnotlock : st.isLocked c = false)
    (hm : st.apply (Move.pileStack c) = some s₁)
    (hnorm : ∃ π w, st.run π = some w ∧ w.isWin = true ∧
      ∃ π₁ π₂, π = π₁ ++ Move.pileStack c :: π₂ ∧
        ∀ m ∈ π₁, cBlocked c m = false) :
    s₁.solvableFrom := by
  obtain ⟨π, w, hrun, hwin, π₁, π₂, hsplit, hclr⟩ := hnorm
  have hmo := hm
  rw [apply_pileStack_iff] at hmo
  obtain ⟨_, b₀, hb₀, _, _⟩ := hmo
  exact solvable_of_pileStack_aux π.length st c b₀ s₁ hwf hnotlock hb₀ hm π
    (Nat.le_refl _) ⟨π₁, π₂, hsplit, hclr⟩ w hrun hwin

set_option linter.unusedVariables false in
/-- ENDGAME §8.3 (c)'s normal-form characterization — the certificate
    route's remaining `sorry`: from a WF, unlocked, rung-legal source,
    either some winning play is rung-normal for `c` (its pre-pass
    prefix `cBlocked`-clean — exactly what
    `solvable_of_pileStack_of_rungNormal` consumes), or the state
    carries the forced-park certificate.  The hypotheses are the staged
    crux's own, unchanged (the falsity is quarantined in the
    conclusion, not guarded away).

TODO(proof) [H] — the §4 (B, L) descent, B = `cBlocked` moves strictly
before the rung pass, L = the play's length (`rung_pass_of_win`
supplies the pass, at the first exceedance).  Work the LAST blocked
move before the pass:

* excursion (`stackPile x b`, `x.suit = c.suit`): its return
  `pileStack x` fires before the pass — the height path back to the
  rung climbs through `x`'s own rung, and `deckStack x` is dead (`x`
  sits on the board; `vis_off_cycle`); delete the pair.  The spread
  form (`excursion_pair_delete`) needs the in-between segment
  `x`-seat/`x`-height blind, and the last-blocked window may still
  park ON `x` (free, unblocked, but seat-reading) — **(c-α)** the
  divergence-window one-step replay for that shape (template:
  `excursionSim_step`, which closed the excursion φ's version; the
  park window's φ is the twin-seat divergence, not the edge-removal).
* park (seating on `c`): redirect to the twin — (i) bare+visible: the
  plain redirect (fit by `canSitOn_swapTwin_right`); (ii) occupied by
  a fitting cargo: transfer-then-redirect (`State.solvable_cargoTwin`,
  TwinSwap.lean — executable, `c`'s seat being bare by `hm`'s own
  guard; the move-free strengthening
  `State.solvable_cargoTwin_exchange_bare`, TwinExchange.lean), the
  transfer itself B-neutral (it replaces one blocked move with
  another) — **(c-β)** the measure stalls (fix: last-noncompliant-
  first, or a third component); (iii) twin unavailable: the descent
  stalls and emits the certificate — arm 1 exactly.  Arm 2 is the
  rank-mate escape's negation (the old W4c license).
* storage elimination: the safety instances only — the Dominance rows'
  own channel, not needed for the crux itself.

The redirect-cycle hazard (§6 W4a) and the certificate's exactness
are the taker's refute-first gates ((c1) α/β): a staged-falsity shape
where `forcedPark` is FALSE at `st` yet the park is forced mid-play
(the certificate reads the SOURCE state; a mid-play twin occupancy is
the (c-α) window's business — such a witness makes the certificate too
narrow); and an `hsafe` state matching the certificate (too wide — the
corner-(ii) width is the known instance, absorbed by channel A under
the bridge's [GAP]). -/
theorem rungNormal_or_forcedPark {st : State} (hwf : st.WF) {c : Card} {s₁ : State}
    (hnotlock : st.isLocked c = false)
    (hm : st.apply (Move.pileStack c) = some s₁) (hsol : st.solvableFrom) :
    (∃ π w, st.run π = some w ∧ w.isWin = true ∧
      ∃ π₁ π₂, π = π₁ ++ Move.pileStack c :: π₂ ∧
        ∀ m ∈ π₁, cBlocked c m = false) ∨ st.forcedPark c := sorry

/-- The repaired crux (ENDGAME §8.3 (c), the picked form): a legal
    `pileStack` of an unlocked card never hurts solvability — EXCEPT
    at the forced-park corner, where the certificate fires.  Disjunct-1
    is `solvable_of_pileStack_of_rungNormal` (the W1 scaffold consumed
    verbatim); disjunct-2 is the quarantine.  The reduction to
    `rungNormal_or_forcedPark` is PROVEN here — the crux's remaining
    content is exactly the normal-form characterization's `sorry`
    above. -/
theorem solvable_of_pileStack' {st : State} (hwf : st.WF) {c : Card} {s₁ : State}
    (hnotlock : st.isLocked c = false)
    (hm : st.apply (Move.pileStack c) = some s₁) (hsol : st.solvableFrom) :
    s₁.solvableFrom ∨ st.forcedPark c := by
  rcases rungNormal_or_forcedPark hwf hnotlock hm hsol with
    ⟨π, w, hrun, hwin, π₁, π₂, hsplit, hclr⟩ | hfp
  · exact Or.inl (solvable_of_pileStack_of_rungNormal hwf hnotlock hm
      ⟨π, w, hrun, hwin, π₁, π₂, hsplit, hclr⟩)
  · exact Or.inr hfp

/-- The one-step core: an accommodation move that succeeds preserves
solvability — dispatch to the two halves.  REPAIRED 2026-09-13 with
the crux (`hnl`, the per-move `playSafeAccomm` head): a locked
`pileStack` is not a solvability-preserving shuffle (the dead-pile
witness).  REPAIRED AGAIN (2026-09-14, the certificate form —
ENDGAME §8.4's propagation note): the `pileStack` half carries the
repaired crux's disjunct — the stack successor is solvable OR the
source state holds the forced-park certificate for the moved card
(the mid-accommodation corner-exclusion is the flagged [GAP]; the
alternative — the certificate vacuous on accommodation-reachable
states — is B2-side, unstarted).  Hypotheses untouched. -/
theorem solvable_of_accomm_step {st : State} {m : Move} {s₂ : State}
    (hwf : st.WF) (hm : st.apply m = some s₂) (hsol : st.solvableFrom)
    (hmacc : m.isAccommodation = true)
    (hnl : ∀ c, m = Move.pileStack c → st.isLocked c = false) :
    s₂.solvableFrom ∨ ∃ c, m = Move.pileStack c ∧ st.forcedPark c := by
  cases m with
  | pileStack c =>
      rcases solvable_of_pileStack' hwf (hnl c rfl) hm hsol with h | hfp
      · exact Or.inl h
      · exact Or.inr ⟨c, rfl, hfp⟩
  | stackPile c b => exact Or.inl (solvable_of_stackPile hwf hm hsol)
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
solvability up to the forced-park disjunct (`solvable_of_accomm_step`
— with the play's safety, every `pileStack` unlocked), and the
induction carries the winning play through the shuffle; a certificate
firing mid-play is witnessed by the play's own prefix (the state it
fires from, reached by that prefix, with the `pileStack c` step next).
REPAIRED (2026-09-14, the certificate form): the conclusion carries
the disjunct — see the crux's tombstone above; corner-exclusion
mid-accommodation is ENDGAME §8.4's flagged [GAP]. -/
private theorem solvable_accommodates_aux {st' : State} : ∀ (play : List Move),
    (∀ m ∈ play, m.isAccommodation = true) → ∀ (st : State),
    st.WF → st.solvableFrom → playSafeAccomm st play →
    st.run play = some st' →
    st'.solvableFrom ∨
      ∃ (c : Card) (σ : State) (pre sub : List Move),
        play = pre ++ Move.pileStack c :: sub ∧
          st.run pre = some σ ∧ σ.forcedPark c := by
  intro play
  induction play with
  | nil =>
      intro _hall st _hwf hsol _hsafe hrun
      have hst : st = st' := Option.some.inj hrun
      subst hst
      exact Or.inl hsol
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
          rcases solvable_of_accomm_step hwf hm hsol (hall m (by simp)) hnl with
            hs₂ | ⟨c, rfl, hfp⟩
          · have hsafe' : playSafeAccomm s₂ ms := by
              have hgs : (st.apply m).getD st = s₂ := by rw [hm]; rfl
              rw [hgs] at hsafe2
              exact hsafe2
            rcases ih (fun m' hm' => hall m' (by simp [hm'])) s₂
              (apply_wf hwf m s₂ hm) hs₂ hsafe' hrun₂ with
              h | ⟨c, σ, pre, sub, hsplit, hpre, hfp⟩
            · exact Or.inl h
            · refine Or.inr ⟨c, σ, m :: pre, sub, ?_, ?_, hfp⟩
              · rw [hsplit]; simp
              · simp only [State.run, hm]; exact hpre
          · -- the certificate fires at THIS step: the play's own
            -- prefix (empty — the state is `st` itself) witnesses it
            refine Or.inr ⟨c, st, [], ms, ?_, ?_, hfp⟩
            · simp
            · rfl

theorem solvable_accommodates {st st' : State} (hwf : st.WF)
    (hacc : safeAccommodates st st') (hsol : st.solvableFrom) :
    st'.solvableFrom ∨
      ∃ (c : Card) (σ : State) (pre sub : List Move),
        st.run (pre ++ Move.pileStack c :: sub) = some st' ∧
          st.run pre = some σ ∧ σ.forcedPark c := by
  obtain ⟨play, hrun, hall, hsafe⟩ := hacc
  rcases solvable_accommodates_aux play hall st hwf hsol hsafe hrun with
    h | ⟨c, σ, pre, sub, hsplit, hpre, hfp⟩
  · exact Or.inl h
  · exact Or.inr ⟨c, σ, pre, sub, by rw [← hsplit]; exact hrun, hpre, hfp⟩

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
        < (Cycle.dealIter st.drawStep k st.stock).cursor), Cycle.removeAt_drawTo]

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
      rw [hdp, Cycle.removeAt_drawTo, hst'']
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
