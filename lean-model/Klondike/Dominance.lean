import Klondike.Theorems
import Klondike.Progress

/-!
# Dominances — the rules that are known to be good

method.md §5's cascade, formalized.  Distinct from commutation (C-IND,
`Klondike/Theorems.lean` §3): dominance is a *preference* claim —
playing the move never loses solutions.  The routes are worry-back
reversibility (§5.1), safe-irrelevance (Blake & Gent), canonical
representatives (§5.2/§5.5), and — one direction only — commutation
(`dominant_of_commutesWithAll`, the POR bridge).
-/

/-- Playing `m` at `st` never hurts: solvability is preserved. -/
def dominantAt (st : State) (m : Move) : Prop :=
  st.solvableFrom → ∃ st₁, st.apply m = some st₁ ∧ st₁.solvableFrom

/-- Omitting `m` at `st` never hurts (some winning play avoids
starting with it). -/
def prunableAt (st : State) (m : Move) : Prop :=
  st.solvableFrom → ∃ play st', st.run play = some st' ∧ st'.isWin = true ∧ play.head? ≠ some m

/-- `m` dominates `m'` at `st`: prune `m'`, prefer `m`. -/
def dominates (st : State) (m m' : Move) : Prop := prunableAt st m' ∧ dominantAt st m

/-- Solvability under a move filter (the generator fragment). -/
def State.solvableWith (P : Move → Bool) (st : State) : Prop :=
  ∃ play, (∀ m ∈ play, P m = true) ∧ ∃ st', st.run play = some st' ∧ st'.isWin = true

/-! ## The POR bridge — dominance vs commutation, one direction -/

/-- Full commutation *implies* dominance, one direction: a move that
can be bubbled past any other move (reaching the same composite state)
can be forced first — provided some winning play actually uses `m`.
The bubbling pushes `m`'s first occurrence in the winning play to the
front, one exchange at a time; each exchange is `h` at the state just
before the occurrence.  The converse fails — a safe stack is dominant
via worry-back yet commutes with nothing (it changes `heights`, which
changes every other stack's legality).

REPAIR (2026-09-13, wrong-theorem protocol): the staged statement had
the exchange at `st` only and no occurrence premise — refuted by a
prover-checked witness (scratch `RefuteCommutesAll`, axiom-clean): a
won state (empty board, all heights 13, empty stock) with
`m = .pileStack ♥2` — the exchange hypothesis holds vacuously (♥2 is
on no board at `st` nor at any one-step successor), the state is
solvable via `[]`, and `dominantAt` fails since `m` is illegal at
`st`.  The exchange is now at every state (the bubbling applies it at
each prefix state of the play), and `huse` supplies the missing
occurrence: some winning play must contain `m` — without it no
exchange ever fires, and a play avoiding `m` leaves nothing to
bubble. -/
theorem dominant_of_commutesWithAll {st : State} {m : Move}
    (h : ∀ (s : State) (m' : Move) (s₁ s₂ : State),
      s.apply m' = some s₁ → s₁.apply m = some s₂ →
      ∃ s₃, s.apply m = some s₃ ∧ s₃.apply m' = some s₂)
    (huse : ∃ play w, st.run play = some w ∧ w.isWin = true ∧ m ∈ play) :
    dominantAt st m := by
  intro _
  obtain ⟨play, w, hrun, hwin, hmem⟩ := huse
  have main : ∀ (play : List Move) (s w : State),
      s.run play = some w → w.isWin = true → m ∈ play →
      ∃ s₃, s.apply m = some s₃ ∧ s₃.solvableFrom := by
    intro play
    induction play with
    | nil => intro s w _ _ hmem; exact absurd hmem (by simp)
    | cons m₁ rest ih =>
        intro s w hrun hwin hmem
        obtain ⟨t₁, hap₁, hrest, _⟩ := run_cons_inv hrun
        by_cases hm₁ : m₁ = m
        · subst hm₁
          exact ⟨t₁, hap₁, rest, w, hrest, hwin⟩
        · have hmem' : m ∈ rest := by
            simp only [List.mem_cons] at hmem
            rcases hmem with h | h
            · exact absurd h.symm hm₁
            · exact h
          obtain ⟨s₃, hap₃, hs₃⟩ := ih t₁ w hrest hwin hmem'
          obtain ⟨s₄, hap₄, ham₄⟩ := h s m₁ t₁ s₃ hap₁ hap₃
          refine ⟨s₄, hap₄, ?_⟩
          exact solvable_of_reaches ⟨[m₁], by
            simp only [State.run, ham₄]⟩ hs₃
  exact main play st w hrun hwin hmem

/-! ## §5.1 Forced safe stacking -/

/-- The classical safe-automove condition (Blake & Gent; method.md
§5.1): a card of rank `r` and color `κ` is safe ⟺ both `κ`-colored
foundations are at `r−2` and both `κ̄`-colored at `r−1`.  Aces and
twos are always safe. -/
def safeToStack (st : State) (c : Card) : Bool :=
  Suit.all.all fun s =>
    if s.color = c.suit.color
    then decide (c.rank.toIdx ≤ st.heights s + 2)
    else decide (c.rank.toIdx ≤ st.heights s + 1)

/-- The returnable case of `safe_pileStack_dominant` (the R/N
reduction, returnable half): when the worry-back to `c`'s own base is
admissible — `canReturnBase c b`, the return-base crux — the dominance
is the roundtrip plus the accommodation lifting: the stacked successor
`st₁` *accommodates* `st` (one `stackPile c b` lands back at `st`
exactly), so `solvable_of_accommodates` transports any winning play.
Safety is not needed in this half (the worry-back is unconditional
here); the unlocked guard supplies the base's visibility
(`vis_base_of_notLocked`).  The non-returnable complement —
deal-adjacent bases, non-king bottoms on anchors — is the B4-shaped
reshape; see the main theorem's note. -/
theorem safe_pileStack_dominant_of_return {st : State} {c : Card} {b : Base}
    (hwf : st.WF) (hnotlock : st.isLocked c = false)
    (hlegal : st.legal (Move.pileStack c) = true)
    (hb : st.board.bottomOf c = some b)
    (hret : canReturnBase c b = true) :
    dominantAt st (Move.pileStack c) := by
  intro hsolv
  obtain ⟨_, htopc, hrk⟩ := legal_pileStack_iff.mp hlegal
  have hap : st.apply (Move.pileStack c) = some { st with
      board := st.board.detach b,
      heights := fun s => if s = c.suit then st.heights s + 1 else st.heights s } := by
    rw [apply_pileStack_iff]
    exact ⟨htopc, b, hb, hrk, rfl⟩
  refine ⟨{ st with
      board := st.board.detach b,
      heights := fun s => if s = c.suit then st.heights s + 1 else st.heights s },
    hap, ?_⟩
  -- the guard bundle for `stackPile c b` at the stacked successor
  have hg1 : c.rank.toIdx + 1 = ({ st with
      board := st.board.detach b,
      heights := fun s => if s = c.suit then st.heights s + 1 else st.heights s } :
      State).heights c.suit := by
    show c.rank.toIdx + 1 =
      (if c.suit = c.suit then st.heights c.suit + 1 else st.heights c.suit)
    rw [if_pos rfl]
    omega
  have htopb : st.board.topOf b = some c := (Board.bottomOf_eq st.board c b).mp hb
  have hatt : ∃ bd, (st.board.detach b).attach b c = some bd := by
    have hfree : (st.board.detach b).topOf b = none := Board.detach_topOf st.board b
    have hnew : (st.board.detach b).bottomOf c = none := Board.bottomOf_detach_self htopb
    have hne : (st.board.detach b).attach b c ≠ none :=
      (Board.attach_eq_some_iff _ _ _).mpr ⟨hfree, hnew⟩
    cases hh : (st.board.detach b).attach b c with
    | none => rw [hh] at hne; exact absurd hne (by simp)
    | some bd => exact ⟨bd, rfl⟩
  -- `canPlace c b` at the successor, by the base's shape
  have hcp : ({ st with
      board := st.board.detach b,
      heights := fun s => if s = c.suit then st.heights s + 1 else st.heights s } :
      State).canPlace c b = true := by
    cases b with
    | inl a =>
        have hking : c.rank = Rank.king := of_decide_eq_true hret
        show (decide ((st.board.detach (Sum.inl a)).topOf (Sum.inl a) = none) &&
          decide (c.rank = Rank.king)) = true
        rw [Board.detach_topOf, hking]
        rfl
    | inr d =>
        have hcs : canSitOn c d = true := hret
        have hdc : d ≠ c := by
          intro h
          obtain ⟨hrank, _⟩ := (canSitOn_eq c d).mp hcs
          rw [h] at hrank
          omega
        have hvisσ : ((st.board.detach (Sum.inr d)).bottomOf d).isSome = true := by
          rw [bottomOf_detach_ne htopb hdc]
          exact vis_base_of_notLocked hwf hb hnotlock
        show (decide ((st.board.detach (Sum.inr d)).topOf (Sum.inr d) = none) &&
          (((st.board.detach (Sum.inr d)).bottomOf d).isSome && canSitOn c d)) = true
        rw [Board.detach_topOf, hvisσ, hcs]
        rfl
  -- the worry-back fires, and the roundtrip lands home
  obtain ⟨st₂, hsp⟩ : ∃ st₂, ({ st with
      board := st.board.detach b,
      heights := fun s => if s = c.suit then st.heights s + 1 else st.heights s } :
      State).apply (Move.stackPile c b) = some st₂ := by
    obtain ⟨bd, hatt⟩ := hatt
    exact ⟨_, (apply_stackPile_iff).mpr ⟨hg1, hcp, bd, hatt, rfl⟩⟩
  have hrt : st₂ = st := pileStack_stackPile_roundtrip hb hret hap hsp
  have hrun : ({ st with
      board := st.board.detach b,
      heights := fun s => if s = c.suit then st.heights s + 1 else st.heights s } :
      State).run [Move.stackPile c b] = some st := by
    show (match ({ st with
      board := st.board.detach b,
      heights := fun s => if s = c.suit then st.heights s + 1 else st.heights s } :
      State).apply (Move.stackPile c b) with
      | some st' => st'.run []
      | none => none) = some st
    rw [hsp, hrt]
    rfl
  exact solvable_of_accommodates ⟨[Move.stackPile c b], hrun, fun m hm => by
    simp only [List.mem_singleton] at hm
    rw [hm]
    rfl⟩ hsolv

/-- §5.1: a legal pileStack of a safe, *unlocked* card is dominant —
the worry-back argument: a safe card can always be brought back later,
and stacking strictly grows the foundation (progress).

REPAIR (2026-09-13, wrong-theorem protocol): the staged statement (no
`hnotlock`) was FALSE.  Prover-confirmed witness (scratch
`DeadPileWitness`, axiom-clean, exit 0): `reveal c` seats the hidden
boundary card under `c` *while `c` still sits on it* — so a card that
is the sole visible card of a live pile (exactly `isLocked c`) must be
revealed through BEFORE it is stacked.  Stacking it first kills the
boundary card permanently (no move can seat a hidden card except
`reveal`, which needs a visible card on the boundary), so it can never
reach the foundation and the successor is unsolvable — witnessed by a
WF state three moves from the win whose safe, legally stackable ♦K
sits alone on the hidden ♣K.  The `hnotlock` guard — §5.2's own
`isRedundantStack` vocabulary — excludes exactly the trigger cards
(`vis_base_of_notLocked`, lifted upstream to Theorems.lean, is the
trichotomy, now a lemma).

STATUS (2026-09-13, the R/N reduction): the RETURNABLE case — the
base admits `canReturnBase c b` — is PROVEN
(`safe_pileStack_dominant_of_return`: one `stackPile` accommodates
`st`, `solvable_of_accommodates` lifts the win; safety is not even
needed there).  The NON-RETURNABLE residue (deal-adjacent bases,
non-king bottoms on anchors) is exactly the B4-shaped reshape, and
no accommodation play bridges it: every accommodation play from the
stacked successor back to `st` must at some point fire `stackPile c b`
(the only move that re-seats `c` at `b`; excursion pairs
`stackPile x`/`pileStack x` are net identities), whose `canPlace c b`
fails on precisely the non-`canReturnBase` bases.  The reshape
itself — replay the winning play substituting the foundation channel
for placements onto `c` (channel A: the only cards that can sit on `c`
are rank `r−1`, opposite colour, foundation-able by `hsafe`'s
opposite-colour conjunct) and skipping the worry-backs of `c`'s
suit-prefix (channel B: those cards are safe by `hsafe`'s same-colour
conjunct) — needs a divergence-tracking simulation between the play's
states and the replay's states (placements onto `c` when the placed
card is not yet stackable are *storage*, and run-carrying `pilePile`
placements onto `c` re-home whole runs: both need the compliant-play
normal form, the same root as `solvable_accommodates`).  That
connection — §5.1's residue and B4 share one reshape lemma — is the
finding; TODO(proof) for the non-returnable case. -/
theorem safe_pileStack_dominant {st : State} {c : Card} (hwf : st.WF)
    (hnotlock : st.isLocked c = false)
    (hsafe : safeToStack st c = true) (hlegal : st.legal (Move.pileStack c) = true) :
    dominantAt st (Move.pileStack c) := sorry

/-! ## §5.2 Three-or-more redundant stackables -/

/-- `redundant_stack = pile_stack & !locked` (§5.2): a stackable card
whose stacking reveals nothing. -/
def State.isRedundantStack (st : State) (c : Card) : Bool :=
  st.legal (Move.pileStack c) && !st.isLocked c

/-- The redundant stackables of the state. -/
def State.redundantStacks (st : State) : List Card :=
  Card.universe.filter fun c => st.isRedundantStack c

/-- §5.2: with ≥3 redundant stackables, stacking the lowest-rank *safe*
one is dominant — a canonical representative; the others remain
available later (stack moves into the foundation commute, and what is
safe is recoverable per §5.1).

Note (2026-09-13): `isRedundantStack` already carries the `¬locked`
guard, so this statement is consistent with the dead-pile witness that
refuted the unguarded §5.1 (see `safe_pileStack_dominant`'s repair
note) — the trigger cards are excluded here by construction.

REPAIR (2026-09-13, wrong-theorem protocol): the staged statement
(no `hsafe`) was FALSE.  The ≥3 stackables sit in three distinct suits
(a suit's foundation has at most one stackable card: its height), so
exactly one of the four suits is *not* among theirs, and nothing in
the hypotheses constrains that fourth suit's height — while
`safeToStack st c` demands it be ≥ r−1 (opposite colour to c) or
≥ r−2 (same colour).  The staged `hlow`/`hlen` premises therefore
leave the §5.1 safety of the lowest stackable unproved, and stacking
it is not dominant: the danger card of the unconstrained suit (rank
r−1, opposite colour — the unique card class that can ever sit on `c`)
may be *live*, forced to transit the tableau through `c`'s seat, and
`c`'s worry-back is itself blocked by the same suit gap.  Minimal
repair: add `hsafe : safeToStack st c = true` (the §5.1 hypothesis),
exactly what the countermodel demands; the conclusion is unchanged.
With it, the row is an instance of §5.1: `isRedundantStack` supplies
the legality and the `¬locked` guard, and the §5.1 core
(`safe_pileStack_dominant`, whose non-returnable half is the B4 root)
carries the content.  The ≥3-redundancy itself buys nothing the §5.1
hypotheses don't — the "others remain available" half is inside §5.1's
worry-back argument (channel A: the only cards that can sit on `c` are
foundation-able by `hsafe`'s opposite-colour conjunct).  Countermodel:
`witnesses/LeastRedundantWitness.lean`. -/
theorem least_redundantStack_dominant {st : State} {c : Card} (hwf : st.WF)
    (hsafe : safeToStack st c = true)
    (hmem : c ∈ st.redundantStacks)
    (hlen : 3 ≤ st.redundantStacks.length)
    (hlow : ∀ c' ∈ st.redundantStacks, c.rank.toIdx ≤ c'.rank.toIdx) :
    dominantAt st (Move.pileStack c) := by
  have := hlen
  have := hlow
  -- the redundancy premise unpacks to §5.1's legality and lockedness
  simp only [State.redundantStacks, List.mem_filter] at hmem
  obtain ⟨-, hrl⟩ := hmem
  simp only [State.isRedundantStack, Bool.and_eq_true] at hrl
  obtain ⟨hlegal, hlock⟩ := hrl
  have hnotlock : st.isLocked c = false := by
    simpa only [Bool.not_eq_true'] using hlock
  exact safe_pileStack_dominant hwf hnotlock hsafe hlegal

/-! ## §5.3 Deck dominance -/

/-- §5.3, draw-1 form: with one card per draw, every drawable card is
equally reachable, so front-loading the safe stack of a drawable card
loses nothing.  The general (draw-3) form needs the deck `is_pure`
condition (offset alignment).  TODO: the reshaping argument. -/
theorem deck_dominance_draw1 {st : State} {c : Card} (hwf : st.WF)
    (hstep : st.drawStep = 1) (hsafe : safeToStack st c = true)
    (hdraw : st.stock.posOf c ≠ none) (hleg : st.applyDrawStackTo c ≠ none) :
    st.solvableFrom → ∃ st₁, st.applyDrawStackTo c = some st₁ ∧ st₁.solvableFrom := sorry

/-! ## §5.4 Unstack only what is not safe to restack -/

/-- The worry-back cancellation: un-stacking `c` to `b` then re-stacking
is the identity — §5.4's pair-deletion step.  Unlike the converse
(`pileStack_stackPile_roundtrip`, which needs `canReturnBase`), this
direction is unconditional: the composition is attach-then-detach at
the same base.  WF supplies the side fact that no card sits on a
foundation card (`founds_gone` + `board_edges`), so `topOf (inr c)` is
free at the successor. -/
theorem stackPile_pileStack_cancel {st : State} {c : Card} {b : Base} {s₁ : State}
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

/-- §5.4, first half: never worry back a dominantly-stackable card —
omitting `stackPile` of a safe card loses nothing.  The statement is
head-only (`prunableAt`): SOME winning play must merely avoid
*starting* with the worry-back.

Route notes (2026-09-13, partial analysis): the second move of a
worry-headed winning play can be swapped to the front in every case
except one — `draw` commutes (`draw_comm_stackPile`, proved);
`deckStack x` swaps (x = c is impossible: c is foundation-passed,
hence off the stock); `deckPile x b'` swaps (b' ≠ b forced, `attach_attach_comm`);
`pileStack x` with x ≠ c swaps (x.suit ≠ c.suit forced; b = inr x would
block x's own stacking); `reveal y` swaps (its attach target ≠ b); and
`pilePile c b''` right after the worry collapses to worrying directly
to `b''` (b'' ≠ b).  The prefix `[stackPile c b, pileStack c]` is an
UNCONDITIONAL identity (attach-then-detach at the same base — no
`canReturnBase` needed, unlike the proven converse roundtrip; it is
now `stackPile_pileStack_cancel` below), so it can be cancelled with a
play-length induction.

The residual blocked shapes: (i) the immediate same-suit worry-chain —
π = stackPile c b :: stackPile x b' :: … with x the card just below c
in c's suit (x cannot be worried before c leaves; c cannot take x's
destination — same color kills `canSitOn`); (ii) `deckPile x (inr c)` as
the second move — placing the drawn card onto the just-worried card
(`b' = inr c` is NOT excluded by the b' ≠ b argument: at st the
placement fails since c is on the foundation; the substitute —
`deckStack x`, legal because `hsafe`'s opposite-colour conjunct puts
x's foundation exactly at toIdx x for a stocked x — reshapes the whole
tail through the foundation channel); and at drawStep ≥ 2 with
the cursor off the deal's 0-orbit, no number of `draw`s returns to
`st` (dealOnce's orbit), so no always-legal alternative head can be
prepended.  Closing those needs the classical worry-back ban (B&G
Theorem-1-compliant solutions never worry a safely-buildable card —
the same channels-A/B rank induction as the repaired §5.1, see
`safe_pileStack_dominant`'s note).  TODO. -/
theorem stackPile_safe_prunable {st : State} {c : Card} {b : Base} (hwf : st.WF)
    (hsafe : safeToStack st c = true) : prunableAt st (Move.stackPile c b) := sorry

/-- §5.4, second half (`deck_pile excludes dom_sm & sm`): never draw a
card to the tableau when it could safely go to the foundation.

Proof: a winning play starting with `deckPile c b` is replayed as
`deckStack c` then `stackPile c b` — the two-move composition produces
exactly the `deckPile` successor (same stock splice, same attach, the
bumped height un-bumped), so the rest of the play still wins, and the
new head is the stack move, not the draw-to-tableau.  A play that
already avoids the head needs nothing.  (Safety and WF are not needed
for the exchange; they are kept for the rule's reading.) -/
theorem deckPile_safe_prunable {st : State} {c : Card} {b : Base} (hwf : st.WF)
    (hsafe : safeToStack st c = true) (hstack : st.legal (Move.deckStack c) = true) :
    prunableAt st (Move.deckPile c b) := by
  have := hwf
  have := hsafe
  intro hsolv
  obtain ⟨play, w, hrun, hwin⟩ := hsolv
  cases play with
  | nil =>
      have h' : (some st : Option State) = some w := hrun
      rw [← Option.some.inj h'] at hwin
      exact ⟨[], st, rfl, hwin, by simp⟩
  | cons m rest =>
    by_cases hm : m = Move.deckPile c b
    · subst hm
      obtain ⟨s₁, hap, hrest⟩ := run_cons_inv hrun
      rw [apply_deckPile_iff] at hap
      obtain ⟨hprev, hcp, bd, hatt, hs₁⟩ := hap
      cases htd : st.apply (Move.deckStack c) with
      | none => simp [State.legal, htd] at hstack
      | some t =>
          have htd2 := htd
          rw [apply_deckStack_iff] at htd2
          obtain ⟨-, hrk, ht⟩ := htd2
          have hsp : t.apply (Move.stackPile c b) = some s₁ := by
            rw [ht, apply_stackPile_iff]
            refine ⟨?_, hcp, bd, hatt, ?_⟩
            · show c.rank.toIdx + 1 =
                (if c.suit = c.suit then st.heights c.suit + 1 else st.heights c.suit)
              rw [if_pos rfl]
              omega
            · rw [hs₁]
              refine state_ext rfl rfl ?_ rfl rfl rfl
              funext s
              by_cases hsc : s = c.suit
              · subst hsc
                show st.heights c.suit = (if c.suit = c.suit then
                    (if c.suit = c.suit then st.heights c.suit + 1 else st.heights c.suit) - 1
                    else (if c.suit = c.suit then st.heights c.suit + 1 else st.heights c.suit))
                rw [if_pos rfl, if_pos rfl]
                omega
              · show st.heights s = (if s = c.suit then
                    (if s = c.suit then st.heights s + 1 else st.heights s) - 1
                    else (if s = c.suit then st.heights s + 1 else st.heights s))
                rw [if_neg hsc, if_neg hsc]
          have hrun2 : st.run (Move.deckStack c :: Move.stackPile c b :: rest) = some w := by
            simp only [State.run, htd, hsp]
            exact hrest.1
          exact ⟨Move.deckStack c :: Move.stackPile c b :: rest, w, hrun2, hwin, by simp⟩
    · exact ⟨m :: rest, w, hrun, hwin, by simp [hm]⟩

/-! ## §5.5 Twin-pair collapse -/

/-- §5.5: when a card and its twin are both unnecessarily stackable,
placing onto one of the pair is equivalent to placing onto the other —
the twin-swap theorem applied as a dominance rule (the pair condition
is what makes the local swap a symmetry: both foundations sit at the
same height, so the suit difference is invisible).  TODO. -/
theorem twinPair_placement_equi {st : State} {x c : Card} {st₁ st₂ : State}
    (hpairc : st.isRedundantStack c = true)
    (hpairt : st.isRedundantStack c.flipSuit = true)
    (h₁ : st.apply (Move.deckPile x (Sum.inr c)) = some st₁)
    (h₂ : st.apply (Move.deckPile x (Sum.inr c.flipSuit)) = some st₂) :
    st₁.solvableFrom ↔ st₂.solvableFrom := sorry

/-! ## The cascade, composed -/

/-- The four-way case split on suits (the factored structure has no
`cases`; this is the enumeration). -/
theorem suit_cases (s : Suit) :
    s = Suit.heart ∨ s = Suit.spade ∨ s = Suit.diamond ∨ s = Suit.club := by
  rcases s with ⟨c, p⟩
  cases c with
  | red =>
      cases p with
      | false => exact Or.inl rfl
      | true => exact Or.inr (Or.inr (Or.inl rfl))
  | black =>
      cases p with
      | false => exact Or.inr (Or.inl rfl)
      | true => exact Or.inr (Or.inr (Or.inr rfl))

/-- The foundation debt: how many cards the foundations still owe
(per-suit `13 − height`, summed).  `pileStack`/`deckStack` pay one
down; no other move raises a height. -/
def heightDebt (st : State) : Nat :=
  (13 - st.heights Suit.heart) + (13 - st.heights Suit.spade) +
    (13 - st.heights Suit.diamond) + (13 - st.heights Suit.club)

/-- The cascade progress measure (§9.4): foundation debt + total
hidden depth + remaining stock.  Every escape the §5 cascade actually
offers strictly decreases it — `pileStack`/`deckStack` grow a
foundation (the debt falls), `deckPile` consumes the stock, `reveal`
uncovers — while the reversible shuffles (`.draw`, `.pilePile`,
worry-back `stackPile`) leave it untouched or raise it. -/
def cascadeMeasure (st : State) : Nat :=
  heightDebt st + st.totalDepth + st.stock.cards.length

/-- The bump case of the debt: a successor whose heights are the
`pileStack`/`deckStack` bump (one suit +1, the rest verbatim) under
the stack guard `toIdx c = heights c.suit` — the rank index caps the
bumped suit at 12, so the debt strictly falls. -/
theorem heightDebt_bump {st : State} {c : Card}
    (hrk : c.rank.toIdx = st.heights c.suit) (st' : State)
    (hF : ∀ s', st'.heights s' = if s' = c.suit then st.heights s' + 1 else st.heights s') :
    heightDebt st' < heightDebt st := by
  have hle : st.heights c.suit ≤ 12 := by
    have hlt := Rank.toIdx_lt c.rank
    omega
  show (13 - st'.heights Suit.heart) + (13 - st'.heights Suit.spade) +
      (13 - st'.heights Suit.diamond) + (13 - st'.heights Suit.club) <
    (13 - st.heights Suit.heart) + (13 - st.heights Suit.spade) +
    (13 - st.heights Suit.diamond) + (13 - st.heights Suit.club)
  rcases suit_cases c.suit with hcs | hcs | hcs | hcs
  · rw [hcs] at hF hle
    have h1 : st'.heights Suit.heart = st.heights Suit.heart + 1 := hF Suit.heart
    have h2 : st'.heights Suit.spade = st.heights Suit.spade := hF Suit.spade
    have h3 : st'.heights Suit.diamond = st.heights Suit.diamond := hF Suit.diamond
    have h4 : st'.heights Suit.club = st.heights Suit.club := hF Suit.club
    rw [h1, h2, h3, h4]
    omega
  · rw [hcs] at hF hle
    have h1 : st'.heights Suit.heart = st.heights Suit.heart := hF Suit.heart
    have h2 : st'.heights Suit.spade = st.heights Suit.spade + 1 := hF Suit.spade
    have h3 : st'.heights Suit.diamond = st.heights Suit.diamond := hF Suit.diamond
    have h4 : st'.heights Suit.club = st.heights Suit.club := hF Suit.club
    rw [h1, h2, h3, h4]
    omega
  · rw [hcs] at hF hle
    have h1 : st'.heights Suit.heart = st.heights Suit.heart := hF Suit.heart
    have h2 : st'.heights Suit.spade = st.heights Suit.spade := hF Suit.spade
    have h3 : st'.heights Suit.diamond = st.heights Suit.diamond + 1 := hF Suit.diamond
    have h4 : st'.heights Suit.club = st.heights Suit.club := hF Suit.club
    rw [h1, h2, h3, h4]
    omega
  · rw [hcs] at hF hle
    have h1 : st'.heights Suit.heart = st.heights Suit.heart := hF Suit.heart
    have h2 : st'.heights Suit.spade = st.heights Suit.spade := hF Suit.spade
    have h3 : st'.heights Suit.diamond = st.heights Suit.diamond := hF Suit.diamond
    have h4 : st'.heights Suit.club = st.heights Suit.club + 1 := hF Suit.club
    rw [h1, h2, h3, h4]
    omega

/-- The §5 escapes do force progress: every commitment move (`reveal`,
`deckPile`, `deckStack`) or foundation stack (`pileStack`) strictly
decreases the cascade measure — the instantiation kit for the repaired
`cascade_sound` below.  No WF needed: the stack guards pin the bumped
suit's height at a rank index ≤ 12 (`heightDebt_bump`), `reveal`'s
strict totalDepth drop and the deck moves' stock shrink are the proven
Progress monotonicities. -/
theorem cascade_escape_progress {st st' : State} {m : Move}
    (hes : m.isCommit = true ∨ ∃ c, m = Move.pileStack c)
    (hap : st.apply m = some st') :
    cascadeMeasure st' < cascadeMeasure st := by
  have hTD := apply_totalDepth_le hap
  have hSL := apply_stockLen_le hap
  rcases hes with hcom | ⟨c, hm⟩
  · cases m with
    | draw => simp [Move.isCommit] at hcom
    | pileStack c => simp [Move.isCommit] at hcom
    | stackPile c b => simp [Move.isCommit] at hcom
    | pilePile c b => simp [Move.isCommit] at hcom
    | reveal c =>
        obtain ⟨_, r, a, bd, _, _, _, hs⟩ := (apply_reveal_iff (st := st) (st' := st')).mp hap
        have hd : heightDebt st' = heightDebt st := by rw [hs]; rfl
        have := apply_reveal_totalDepth_lt hap
        simp only [cascadeMeasure]
        omega
    | deckPile c b =>
        obtain ⟨_, _, _, _, hs⟩ := (apply_deckPile_iff (st := st) (st' := st')).mp hap
        have hd : heightDebt st' = heightDebt st := by rw [hs]; rfl
        have := apply_deckPile_shortens hap
        simp only [cascadeMeasure]
        omega
    | deckStack c =>
        obtain ⟨_, hrk, hs⟩ := (apply_deckStack_iff (st := st) (st' := st')).mp hap
        have hd : heightDebt st' < heightDebt st := by
          refine heightDebt_bump hrk st' ?_
          intro s'
          rw [hs]
        have := apply_deckStack_shortens hap
        simp only [cascadeMeasure]
        omega
  · subst hm
    obtain ⟨_, b, _, hrk, hs⟩ := (apply_pileStack_iff (st := st) (st' := st')).mp hap
    have hd : heightDebt st' < heightDebt st := by
      refine heightDebt_bump hrk st' ?_
      intro s'
      rw [hs]
    simp only [cascadeMeasure]
    omega

/-- The dominance cascade (§5 + pruning_dominance_interaction): a
filter that, at every reachable solvable state, leaves either the win
or a dominant, *progress-forcing* P-move, preserves solvability.

REPAIR (2026-09-13, wrong-statement protocol — the wave's finding):
the staged statement (escape = `dominantAt` alone) was FALSE.
Prover-confirmed witness (witnesses/CascadeWitness.lean, exit 0, the
core facts axiom-clean): a WF state one `pileStack ♦K` from the win
with the stock exhausted — `applyDraw` is unconditionally `some`, and
`dealOnce` on the empty cycle is the identity, so `draw` is *trivially
dominant* there (the successor is the state itself) — and the
hypothesis therefore holds for the draw-only filter at every reachable
solvable state, while no all-draw play can win (draws never touch
`heights`).  The same hole yawns for any reversible non-commit:
`pilePile` (kings between free anchors) and worry-back `stackPile`
(via `stackPile_pileStack_cancel`) are dominant by invertibility and
make no progress.  `dominantAt` alone carries no termination content;
the induction needs the progress measure this docstring's predecessor
already announced (§9.4: the dominances force progress — foundation
growth, reveals — so states do not repeat: the DAG argument), and the
staged hypothesis simply forgot to demand it.  Repair: the escape must
additionally strictly decrease `cascadeMeasure` — every §5 escape
satisfies it (`cascade_escape_progress`, the instantiation kit);
draws are excluded, matching the engine's own division of labor (its
draw-loops are terminated by the CyclePruner/TP layer, which this
model does not carry — a draw-inclusive cascade would need the
deal-orbit's finite period; deferred with the reading).

The proof is a bounded induction on the measure: the escape move
takes the recursion strictly down it, `dominantAt` keeps the successor
solvable, and the win is the base case (the empty play). -/
theorem cascade_sound {P : Move → Bool} (st : State)
    (h : ∀ st₁ play, st.run play = some st₁ → st₁.solvableFrom →
      st₁.isWin = true ∨ ∃ m, P m = true ∧ st₁.legal m = true ∧ dominantAt st₁ m ∧
        ∀ st₂, st₁.apply m = some st₂ → cascadeMeasure st₂ < cascadeMeasure st₁) :
    st.solvableFrom → st.solvableWith P := by
  intro hsolv
  have main : ∀ (n : Nat) (s : State) (π : List Move),
      st.run π = some s → cascadeMeasure s ≤ n → s.solvableFrom → s.solvableWith P := by
    intro n
    induction n with
    | zero =>
        intro s π hrun hμ hsolv
        rcases h s π hrun hsolv with hw | ⟨m, hP, _, hdom, hprog⟩
        · exact ⟨[], by simp, s, rfl, hw⟩
        · exfalso
          obtain ⟨s', hap, _⟩ := hdom hsolv
          have := hprog s' hap
          omega
    | succ n ih =>
        intro s π hrun hμ hsolv
        rcases h s π hrun hsolv with hw | ⟨m, hP, _, hdom, hprog⟩
        · exact ⟨[], by simp, s, rfl, hw⟩
        · obtain ⟨s', hap, hsol'⟩ := hdom hsolv
          have hμ' : cascadeMeasure s' ≤ n := by
            have := hprog s' hap
            omega
          have hreach : st.run (π ++ [m]) = some s' := by
            rw [run_append st π [m], hrun]
            show (match s.apply m with | some x => x.run [] | none => none) = some s'
            rw [hap]
            rfl
          obtain ⟨play₁, hall₁, w, hrw, hww⟩ := ih s' (π ++ [m]) hreach hμ' hsol'
          refine ⟨m :: play₁, ?_, w, ?_, hww⟩
          · intro m' hm'
            rcases List.mem_cons.mp hm' with rfl | hmt
            · exact hP
            · exact hall₁ m' hmt
          · show (match s.apply m with | some x => x.run play₁ | none => none) = some w
            rw [hap]
            exact hrw
  exact main (cascadeMeasure st) st [] (by rfl) (Nat.le_refl _) hsolv

/-! §5.6 (the least-stack cascade) is deferred — it is the most
intricate dominance and carries its own TODO in method.md.
§5.7 (kings only on actually-free piles) is already definitional in
`State.canPlace`. -/