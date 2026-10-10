import Klondike.Theorems
import Klondike.Progress
import Klondike.Tactics

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
    rw [ite_eq_left rfl]
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

/-- The step-1 addition lemma for the deal orbit (Macro's
`dealOnce_iterate_add` re-proved here — Dominance sits above Macro in
the import DAG, so the upstream copy is not citable). -/
theorem dealOnce_iterate_add1 (l : List Card) :
    ∀ (q c : Nat), c + q ≤ l.length →
      Cycle.dealIter 1 q ⟨l, c⟩ = ⟨l, c + q⟩ := by
  intro q
  induction q with
  | zero => intro c _; rfl
  | succ q ih =>
      intro c hle
      have hstep : Cycle.dealOnce 1 ⟨l, c⟩ = ⟨l, c + 1⟩ := by
        show (if c ≥ l.length then (⟨l, 0⟩ : Cycle Card)
            else ⟨l, min (c + 1) l.length⟩) = ⟨l, c + 1⟩
        rw [ite_eq_right (by omega), Nat.min_eq_left (by omega)]
      rw [Cycle.dealIter_succ, ← Cycle.dealIter_shift, hstep, ih (c + 1) (by omega)]
      exact congrArg (Cycle.mk l) (by omega)

/-- At step 1, pure deals reach any cursor in `[0, length]` from any
starting cursor (the saturating climb, the wrap from the pass end,
then the climb) — every waste position is addressable. -/
theorem dealIter_reach1 {l : List Card} {u v : Nat} (hv : v ≤ l.length) :
    ∃ k, Cycle.dealIter 1 k ⟨l, u⟩ = ⟨l, v⟩ := by
  have climb : ∀ (a b : Nat), a ≤ b → b ≤ l.length →
      Cycle.dealIter 1 (b - a) ⟨l, a⟩ = ⟨l, b⟩ := fun a b hle hb => by
    rw [dealOnce_iterate_add1 l (b - a) a (by omega)]
    exact congrArg (Cycle.mk l) (by omega)
  have wrap : Cycle.dealIter 1 1 ⟨l, l.length⟩ = ⟨l, 0⟩ := by
    show (if l.length ≥ l.length then (⟨l, 0⟩ : Cycle Card)
        else ⟨l, min (l.length + 1) l.length⟩) = ⟨l, 0⟩
    rw [ite_eq_left (Nat.le_refl l.length)]
  by_cases hu : u ≤ l.length
  · by_cases hle : u ≤ v
    · exact ⟨v - u, climb u v hle hv⟩
    · refine ⟨v + 1 + (l.length - u), ?_⟩
      rw [Cycle.dealIter_add, Cycle.dealIter_add,
        climb u l.length hu (Nat.le_refl _), wrap]
      have hclimb := climb 0 v (Nat.zero_le _) hv
      rw [Nat.sub_zero] at hclimb
      exact hclimb
  · have hwrap : Cycle.dealOnce 1 ⟨l, u⟩ = ⟨l, 0⟩ := by
      show (if u ≥ l.length then (⟨l, 0⟩ : Cycle Card)
          else ⟨l, min (u + 1) l.length⟩) = ⟨l, 0⟩
      rw [ite_eq_left (by omega)]
    refine ⟨v + 1, ?_⟩
    rw [Cycle.dealIter_add]
    show Cycle.dealIter 1 v (Cycle.dealOnce 1 ⟨l, u⟩) = _
    rw [hwrap]
    have hclimb := climb 0 v (Nat.zero_le _) hv
    rw [Nat.sub_zero] at hclimb
    exact hclimb

/-- **The reserve lemma (draw-1)**: at `drawStep = 1`, states differing
only in the stock cursor are equi-solvable — the stock behaves as a
reserve from which any card can be picked at any time.  This is the
formal content of B&G's exception clause ("the stock can be treated as
if it were a reserve when the draw size is 1 and redeals are
unlimited") and the premise C9 cites.

The replay of a winning play from the cursor-twin: every non-consuming
move fires verbatim (its guards never read the cursor —
`apply_nonConsuming_cursor_blind`), and before each consuming move the
inserted pure deals bring the cursor to exactly the source's, where the
twins agree on `prev` and the splice index, so the deck move lands on
the very same successor (full state equality — the cursor
resynchronizes at every consumption).  `isWin` reads heights only. -/
theorem draw1_cursor_solvable {s t : State} (hstep : s.drawStep = 1)
    (hd : s.diffCursor t) : s.solvableFrom → t.solvableFrom := by
  -- moves never change the draw step
  have hds : ∀ {s s₁ : State} {m : Move}, s.apply m = some s₁ →
      s₁.drawStep = s.drawStep := by
    intro s s₁ m h
    move_cases h with
    | draw => rfl
    | reveal _ => rfl
    | deckPile _ _ => rfl
    | deckStack _ => rfl
    | pileStack _ => rfl
    | stackPile _ _ => rfl
    | pilePile _ _ => rfl
  have main : ∀ (π : List Move) (s t : State), s.drawStep = 1 →
      s.diffCursor t → ∀ w, s.run π = some w → w.isWin = true →
      ∃ π' w', t.run π' = some w' ∧ w'.isWin = true := by
    intro π
    induction π with
    | nil =>
        intro s t _ hd w hrun hwin
        have hw : w = s := by
          have h' : (some s : Option State) = some w := hrun
          exact (Option.some.inj h').symm
        have hth : t.heights = w.heights :=
          ((hd.2.2.1).symm).trans ((congrArg State.heights hw).symm)
        refine ⟨[], t, rfl, ?_⟩
        show (Suit.all.all fun σ => decide (t.heights σ = 13)) = true
        rw [hth]
        exact hwin
    | cons m rest ih =>
        intro s t hstep hd w hrun hwin
        obtain ⟨s₁, hap, hrest⟩ := run_cons_inv hrun
        have hs1 : s₁.drawStep = 1 := by rw [hds hap]; exact hstep
        by_cases hc : m.consumesStock = true
        · -- the consuming move: sync the cursor, land exactly on s₁
          have hprev : ∃ x, s.stock.prev = some x := by
            cases m with
            | draw => simp [Move.consumesStock] at hc
            | reveal _ => simp [Move.consumesStock] at hc
            | pileStack _ => simp [Move.consumesStock] at hc
            | stackPile _ _ => simp [Move.consumesStock] at hc
            | pilePile _ _ => simp [Move.consumesStock] at hc
            | deckPile x _ =>
                rw [apply_deckPile_iff] at hap
                exact ⟨x, hap.1⟩
            | deckStack x =>
                rw [apply_deckStack_iff] at hap
                exact ⟨x, hap.1⟩
          obtain ⟨x, hp⟩ := hprev
          -- the source cursor is within the pass (prev is some)
          have hcur : s.stock.cursor ≤ s.stock.cards.length := by
            simp only [Cycle.prev] at hp
            split at hp
            · exact absurd hp (by simp)
            · have hlt := (List.getElem?_eq_some_iff.mp hp).1
              omega
          obtain ⟨k, hk⟩ := dealIter_reach1 (l := t.stock.cards)
            (u := t.stock.cursor) (v := s.stock.cursor) (by
              rw [← hd.2.2.2.2.1]; exact hcur)
          have hk' : Cycle.dealIter 1 k t.stock
              = ⟨t.stock.cards, s.stock.cursor⟩ := hk
          have htstep : t.drawStep = 1 := by
            rw [← hstep]; exact (hd.2.2.2.2.2).symm
          -- the drawn twin is exactly the source state
          have hdrawn : t.run (List.replicate k Move.draw)
              = some { t with stock := Cycle.dealIter t.drawStep k t.stock } :=
            run_dealIter k t
          have hstock : Cycle.dealIter t.drawStep k t.stock = s.stock := by
            rw [htstep, hk', ← hd.2.2.2.2.1]
          have hdeq : { t with stock := Cycle.dealIter t.drawStep k t.stock } = s :=
            state_ext hd.1.symm hd.2.1.symm hd.2.2.1.symm hd.2.2.2.1.symm
              hstock hd.2.2.2.2.2.symm
          obtain ⟨π', w', hrun', hwin'⟩ :=
            ih s₁ s₁ hs1 (⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ : s₁.diffCursor s₁) w hrest.1 hwin
          refine ⟨List.replicate k Move.draw ++ m :: π', w', ?_, hwin'⟩
          rw [run_append t (List.replicate k Move.draw) (m :: π'), hdrawn, hdeq]
          show (match s.apply m with
            | some st' => st'.run π' | none => none) = some w'
          rw [hap]
          exact hrun'
        · have hcf : m.consumesStock = false := by
            cases hcb : m.consumesStock with
            | false => rfl
            | true => exact absurd hcb hc
          obtain ⟨t₁, htap, hdd⟩ := apply_nonConsuming_cursor_blind hcf hd hap
          obtain ⟨π', w', hrun', hwin'⟩ :=
            ih s₁ t₁ hs1 hdd w hrest.1 hwin
          refine ⟨m :: π', w', ?_, hwin'⟩
          show (match t.apply m with
            | some st' => st'.run π' | none => none) = some w'
          rw [htap]
          exact hrun'
  intro hsolv
  obtain ⟨π, w, hrun, hwin⟩ := hsolv
  obtain ⟨π', w', hrun', hwin'⟩ := main π s t hstep hd w hrun hwin
  exact ⟨π', w', hrun', hwin'⟩

/-- §5.3, draw-1 form: with one card per draw, every drawable card is
equally reachable, so front-loading the safe stack of a drawable card
loses nothing.  The general (draw-3) form needs the deck `is_pure`
condition (offset alignment).

Route notes (2026-09-14, the reserve decomposition — B&G's "the
stock is a reserve at draw size 1 with unlimited redeals").  By
`applyDrawStackTo_eq_dealPlay` (Theorems), the jump successor is
`st · draw^k · deckStack c`, so the task is to replay a winning play
π from the jump successor.  Three layers:

**(A) The reserve lemma** — **PROVEN** below (`draw1_cursor_solvable`,
with `dealOnce_iterate_add1` and `dealIter_reach1` as its orbit kit):
at `drawStep = 1`, `diffCursor`-related states are equi-solvable.
The replay skips nothing and inserts draws: every non-consuming move
fires verbatim (`apply_nonConsuming_cursor_blind` — its guards read
board/heights/depths only), and before each consuming move the
inserted pure deals bring the cursor to exactly the source's — where
the twins agree on `prev` and the splice index, so the deck move lands
on the very same successor (full state equality; the cursor
resynchronizes at every consumption).  The addition lemma
`dealOnce_iterate_add1` re-proves Macro's `dealOnce_iterate_add`
locally (Dominance sits above Macro in the DAG).  This is the
stock-is-a-reserve theorem — the premise C9 cites
(`reachablePos_step1`'s docstring).

**(B) The first-move exchanges** (induction on π's length; every
case either closes or recurses at `st · m₁` with the c-hypotheses
preserved — the key auto-facts: m₁'s stackable card has m₁'s suit ≠
c.suit, since c's suit's stackable is c itself and c is stocked):
`draw` absorbs (the jump's `drawTo` resets the cursor absolutely:
`(st · draw) · jump = st · jump`); `reveal`/`pilePile` commute with
the jump by equality (their guards never read the stock or c's
height slot); `pileStack d` commutes by equality (`bump_bump`);
`deckStack x` / `deckPile x b'` (x ≠ c) commute up to `diffCursor`
(layer A transports the win); the c-exit as the first move:
`deckStack c` — the cursor is already at `posOf c + 1`, so the jump
IS `[deckStack c]`; `deckPile c b` — the worry-back identity
`[jump c, stackPile c b] ≡ [deckPile c b]` (`bump_drop`: bump then
drop restores the height, same splice index by noDup, same attach).

**(C) The blocked case**: m₁ = `stackPile d b` — a worry-back before
c's exit.  The IH's `hsafe` can break at `st · stackPile d b` (the
d-suit drop), so the induction cannot proceed.  B&G's normal form
(their safemoves proof) eliminates pre-exit worry-backs: c stays
safely-buildable until its exit (no c-suit stack can fire — c is
stocked; heights only rise under the non-worry prefix), so any
pre-exit worry is noncompliant and is swapped past the safe builds
(`comm_pileStack_stackPile`) or cancelled against its immediate
restack (`stackPile_pileStack_cancel`).  That normal form is the
§5.1 core — the same root as `safe_pileStack_dominant`'s N-half and
the B4 crux's endgame.  So: deck_dominance_draw1 = (the §5.1 normal
form) + (A) + (B).  TODO(proof): A and B are self-contained; C is
the shared root. -/
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
  have hfree : st.board.topOf b = none := topOf_of_canPlace hcp
  have hbne : Sum.inr c ≠ b := by
    cases b with
    | inl a => intro hcon; simp at hcon
    | inr d =>
        intro hcon
        injection hcon with hcd
        have hivd := isVis_of_canPlace_inr hcp
        rw [← hcd, hvis] at hivd
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
    rw [ite_eq_left rfl]
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
        rw [ite_eq_left rfl, ite_eq_left rfl]
        omega
      · rw [ite_eq_right hsc, ite_eq_right hsc]
    exact state_ext rfl hbdb.symm hhh.symm rfl rfl rfl

/-- §5.4, first half: never worry back a dominantly-stackable card —
omitting `stackPile` of a safe card loses nothing.  The statement is
head-only (`prunableAt`): SOME winning play must merely avoid
*starting* with the worry-back — so a single front-swap of the second
move closes every case but one.

Route notes (2026-09-14, the complete second-move ledger; B&G's
appendix proof of the worry-back corollary, ported): let π be a
winning play.  If π's head is not the worry, done.  π = [stackPile c b]
alone is vacuous — the worry drops `heights c.suit` below 13, so the
one-move successor cannot be a win.  Otherwise π = stackPile c b ::
m₂ :: γ, and m₂ can be pulled in front:

* m₂ = `pileStack c` — the pair is the identity
  (`stackPile_pileStack_cancel`, proven below); recurse on γ (the
  play shortened by two; γ's head may be the worry again — the
  length induction absorbs this).
* m₂ = `pilePile c b''` — the worry-collapse: b'' ≠ b is forced
  (the move's own `b₀ ≠ b''` guard at the worried-back state, where
  c's base is b), and `[stackPile c b, pilePile c b'' c-run] ≡
  [stackPile c b'']` — c's run at the successor is `[c]` alone (the
  worry just seated it, nothing on it), so the composition is
  detach-at-b-then-attach-at-b''.  The head becomes `stackPile c b''`
  ≠ the pruned move.  [A custom two-move square; the pieces are the
  cancel's.]
* m₂ = `pilePile x b''` with c inside x's run (the worry seated c on
  the run's top d, and the run then re-homes) — the swap
  `[pilePile x b'', stackPile c b]` lands c on the re-homed d and
  reaches the same composite state; the run keeps its internal edges
  under `detach`/`attach`.  The head becomes `pilePile x b''`.
  [Custom square: the worry's target b = inr d with d in x's run.]
* m₂ = `pileStack d` (d ≠ c: the re-stack of c is the bullet above,
  and any other d has d.suit ≠ c.suit — the stack guards read
  different suits) — `comm_pileStack_stackPile` (Commutation).
* m₂ = `draw` — `draw_comm_stackPile` (Commutation).
* m₂ = `reveal y` — `comm_reveal_stackPile` (Commutation); the
  reveal's attach target is never b (b's top is the just-worried c).
* m₂ = `deckStack x` — x ≠ c (c is foundation-passed, hence off the
  stock); `comm_deckStack_stackPile` (Commutation).
* m₂ = `deckPile x b'` with b' ≠ inr c — b' = b is impossible (b's
  top is c at the successor, so `canPlace` fails there, so the move
  was not legal); `comm_deckPile_stackPile` (Commutation).
* m₂ = `stackPile x b'` (x ≠ c — the height guard at the successor
  reads `toIdx x + 1 = heights x.suit`, which for x = c fails since
  the first worry already dropped it) — `comm_stackPile_stackPile`
  (Commutation); the head becomes a *different* worry, done.
* m₂ = `deckPile x (inr c)` — **the storage case, the sole blocker**:
  placing the drawn x directly onto the just-worried c.  At st the
  placement is illegal (c is on the foundation, `isVis c` fails), so
  no commutation applies — the worry CREATED the seat.  `hsafe`'s
  opposite-colour conjunct puts x's foundation exactly at `toIdx x`
  (a stocked x cannot be foundation-passed, and cannot sit below
  it), so `deckStack x` is legal at st — but replaying the tail
  through the foundation channel is the B&G "channel A" reshape: the
  cards placed on x-on-c are foundation-able too (the safety bounds
  descend exactly two ranks), and the descent meets the worry-back
  chain — the same compliant-play normal form as
  `solvable_of_pileStack`'s endgame and §5.1's N-half.

So the row reduces to: the nine swap cases above (each a direct
citation of the proven commutation kit plus two custom squares) plus
the storage case, which is the §5.1/B4 root.  TODO(proof). -/
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
              rw [ite_eq_left rfl]
              omega
            · rw [hs₁]
              refine state_ext rfl rfl ?_ rfl rfl rfl
              funext s
              by_cases hsc : s = c.suit
              · subst hsc
                show st.heights c.suit = (if c.suit = c.suit then
                    (if c.suit = c.suit then st.heights c.suit + 1 else st.heights c.suit) - 1
                    else (if c.suit = c.suit then st.heights c.suit + 1 else st.heights c.suit))
                rw [ite_eq_left rfl, ite_eq_left rfl]
                omega
              · show st.heights s = (if s = c.suit then
                    (if s = c.suit then st.heights s + 1 else st.heights s) - 1
                    else (if s = c.suit then st.heights s + 1 else st.heights s))
                rw [ite_eq_right hsc, ite_eq_right hsc]
          have hrun2 : st.run (Move.deckStack c :: Move.stackPile c b :: rest) = some w := by
            simp only [State.run, htd, hsp]
            exact hrest.1
          exact ⟨Move.deckStack c :: Move.stackPile c b :: rest, w, hrun2, hwin, by simp⟩
    · exact ⟨m :: rest, w, hrun, hwin, by simp [hm]⟩

/-! ## §5.4b The vacate prunability — the empty-slot boundary

The vacate row (2026-10-10, the farm-vacate-prunable session): at a
WF state that ALREADY has a free anchor, a non-king tab-to-tab whose
run root sits on an anchor floor need never be played first.  The
row is staged over one named residue, `vacate_secondMove_residue`
below, in the `replay_head_residue` house pattern (Restriction's
wave-21 split): everything the two front moves can settle is done
here, the second-move ledger's hard half is the residue.  The
co-realizability and corner-legality exhibit lives in
`witnesses/VacateCoReal.lean` (decide-anchored, the pristine
`uState`/`ofList` family). -/

/-- The vacate kit's floor fact (the [E] row): a NON-KING seated on
an anchor is the deal's own dealt head of that pile with the hidden
boundary already empty — the pile below the seat is fully revealed.
`board_edges`'s anchor arm offers a king or the dealt head (`wf.board_edges`
plus `Board.bottomOf_eq`); the king arm is exactly what `hnk` kills
(an anchored king parked OVER a hidden stack is legal WF, and there
the conclusion is false — `hnk` is load-bearing).  With the head
deal-adjacent, a positive depth would put the visible head inside the
hidden prefix, against `vis_not_hidden`.  Consequences: no `reveal`
of pile `a` can ever fire (dead boundary — `State.depthsZero`'s
`topHidden` argument), and the slot the vacate leaves is a genuinely
empty pile, whatever sits hidden under the pre-existing hole. -/
theorem depths_zero_of_floor_seated {st : State} {c : Card} {a : Anchor}
    (hwf : st.WF) (hnk : c.rank ≠ Rank.king)
    (hfloor : st.board.bottomOf c = some (Sum.inl a)) :
    st.depths a = 0 ∧ (st.deal.piles a).head? = some c := by
  have htop : st.board.topOf (Sum.inl a) = some c :=
    (Board.bottomOf_eq st.board c (Sum.inl a)).mp hfloor
  obtain ⟨-, hbase⟩ := hwf.board_edges (Sum.inl a) c htop
  rcases hbase with hking | hhcell
  · exact absurd hking hnk
  · cases hpl : st.deal.piles a with
    | nil =>
        rw [hpl] at hhcell
        exact absurd hhcell (by simp [List.head?])
    | cons x rst =>
        rw [hpl] at hhcell
        have hxc : x = c := by
          have hx : some x = some c := hhcell
          exact Option.some.inj hx
        cases hdep : st.depths a with
        | zero => exact ⟨rfl, hhcell⟩
        | succ n =>
            exfalso
            have hvis : st.isVis c = true := by
              show (st.board.bottomOf c).isSome = true
              rw [hfloor]
              rfl
            refine absurd ?_ (hwf.vis_not_hidden c hvis a)
            show c ∈ st.hidden a
            show c ∈ (st.deal.piles a).take (st.depths a)
            rw [hdep, hpl, hxc]
            show c ∈ c :: rst.take n
            exact List.mem_cons.mpr (Or.inl rfl)

/-- The vacate kit's target fact (the [E] row's twin): a non-king's
run can only land on a card seat — anchor landings demand a king
(`king_of_canPlace_inl` through `canPlace_of_canMoveRun`).
So a legal vacate never consumes the free anchor it is licensed
by: before the vacate the free anchors are the hole set, after it
they are the hole set PLUS the vacated pile. -/
theorem exists_inr_of_canMoveRun_of_ne_king {st : State} {c : Card} {b : Base}
    (hnk : c.rank ≠ Rank.king) (hcmr : st.canMoveRun c b = true) :
    ∃ d, b = Sum.inr d := by
  cases b with
  | inl a' => exact absurd (king_of_canPlace_inl (canPlace_of_canMoveRun hcmr)) hnk
  | inr d => exact ⟨d, rfl⟩

/-- `pilePile` is a pure tableau rewire: heights read the same at
either end of a successful application (the vacate-alone case's win
transfer — a one-move win through a `pilePile` means the start was
already won). -/
theorem heights_eq_of_apply_pilePile {st s₁ : State} {c : Card} {b : Base}
    (h : st.apply (Move.pilePile c b) = some s₁) :
    s₁.heights = st.heights := by
  rw [apply_pilePile_iff] at h
  obtain ⟨-, -, -, -, -, -, rfl⟩ := h
  rfl

theorem isWin_congr_heights {st s₁ : State} (h : s₁.heights = st.heights) :
    s₁.isWin = st.isWin := by
  show (Suit.all.all fun s => decide (s₁.heights s = 13))
    = (Suit.all.all fun s => decide (st.heights s = 13))
  rw [h]

/-- The generic front swap (the head-only machinery's engine): when
swapping the two orderings of `m` and `m₂` at `st` yields the same
`Option`, a successful run of `m :: m₂ :: …` IS a run of
`m₂ :: m :: …` to the same state — the tail needs no replay at all.
With `m₂ ≠ m` this alone discharges prunability's head-only demand. -/
theorem run_swap_front_of_commEq {st : State} {m m₂ : Move} {rest : List Move} {w : State}
    (hcomm : (st.apply m₂ >>= fun s => s.apply m) = (st.apply m >>= fun s => s.apply m₂))
    (hrun : st.run (m :: m₂ :: rest) = some w) :
    st.run (m₂ :: m :: rest) = some w := by
  obtain ⟨s₁, hap₁, hrest, -⟩ := run_cons_inv hrun
  obtain ⟨s₂, hap₂, htail, -⟩ := run_cons_inv hrest
  have hr : (st.apply m >>= fun s => s.apply m₂) = some s₂ := by
    rw [hap₁]
    exact hap₂
  rw [← hcomm] at hr
  obtain ⟨t₁, ht₁, ht₂⟩ := Option.bind_eq_some_iff.mp hr
  show (match st.apply m₂ with
    | some st' => st'.run (m :: rest)
    | none => none) = some w
  rw [ht₁]
  show (match t₁.apply m with
    | some st' => st'.run rest
    | none => none) = some w
  rw [ht₂]
  exact htail

/-- **VACATE RESIDUE** — the second-move ledger's hard half (named,
the honest split of `vacate_pilePile_prunable_of_hole`; the
`replay_head_residue` house pattern): the vacate is prunable at `st`
when a winning play [`vacate; m₂; …`] with `m₂` outside the
guard-free commutation sector (`.draw`, `.deckStack`) is given.

Then `m₂` touches the tableau, and the front swap is of one of these
shapes (the per-kind ledger, each verified against the kit's actual
guards this session):

* `m₂ = reveal x` — `x ≠ a` automatically (depths a = 0 kills the
  boundary, `depths_zero_of_floor_seated`); the guards coincide at
  `st` and at the vacate successor, and `comm_reveal_pilePile`
  (Commutation:1106) applies with `disjointTouch` derived from WF
  alone (the boundary card is hidden hence not on the visible run;
  the second-hidden base card is hidden hence not the vacate's target
  card, which is visible).  [Closable; cite + one h₂ construction.]
* `m₂ = deckPile x b'` — unless `b' = Sum.inl a` (the corner, below),
  `comm_deckPile_pilePile` (Commutation:1301) applies: the waste
  card is off-cycle hence off the visible run (`vis_off_cycle`);
  a landing on the moved run's TOP card survives the guard (the
  mid-run cards are never bare); the same-base clash (`b' = b₀`) is
  dead in the given order.  [Closable.]
* `m₂ = pileStack x` — `x = c` is the same-root MERGE: the whole
  issued shape collapses to `pileStack c` at `st` (the vacate is the
  no-op detour; head `pileStack c` ≠ the token); `x` = the run's top
  card is the rider-stack square (detach at the rider's seat, then
  the shortened run follows); other `x` via
  `comm_pileStack_pilePile` (Commutation:1527, also Theorems:1164
  `pileStack_comm_pilePile` for the both-shapes form).
  [Closable; two custom squares + one cite.]
* `m₂ = stackPile x b'` — unless `b' = Sum.inl a` (the corner), cite
  `comm_stackPile_pilePile` (Commutation:1606); the foundation card
  is invisible hence off the run (`founds_gone`).  [Closable.]
* `m₂ = pilePile x b''` — same-root (`x = c`) merges into the single
  token `pilePile c b''` (different from the vacate: the vacate's
  own target guard `b₀ ≠ b''`); `x` inside the moved run is the
  sub-run jettison square (the detach base `StoreKey` — the
  `Board.aboveOf_sub`/`aboveOf_congr` splits; the jettison onto
  `Sum.inl a` is the in-run king corner, again below); disjoint
  roots go through `comm_pilePile_pilePile` (Commutation:1659) —
  its `hdisj` card half needs the two runs disjoint, which the WF
  cycle tolerance does NOT give for free (`AboveIrreflWitness`), so
  the square is proved directly, `aboveOf_sub` style.  [Real work,
  sketched.]
* `m₂` = a king landing on `Sum.inl a` (base inl, the VACATED
  anchor) — **the corner**: kings are the only consumers of an empty
  anchor (`king_of_canPlace_inl`, Move:522; `canPlace_inl_iff`,
  Move:492).  Sources: `deckPile K (Sum.inl a)` from the waste,
  `stackPile K (Sum.inl a)` from a completed foundation, `pilePile
  K/x (Sum.inl a)` from a seated king — including a king seated
  INSIDE the moved run (the jettison that consumes the vacancy).
  The σ-corner (the orchestrator's plan): with `h` the pre-existing
  hole, replace [`vacate; K→a`] with [`K→h`; `vacate`].  Both
  prefix moves are legal at `st` and the composite enjoys the
  two-side identity
      `st ⬝ [K→h; vacate] = (st ⬝ vacate) ⬝ K→h`
  cellwise (both sides are `st`'s board with `inl a` cleared (no
  reveal ever reads pile `a`: its depth is 0), `inl h` set to `K`,
  `b₀ = inr d` sealed by the run, and `K`'s old seat cleared) —
  machine-checked facts at every king source in
  `witnesses/VacateCoReal.lean`.  The stopper is the TAIL: the two
  two-move composites differ by which anchor slot carries the king
  (`a` vs `h`), and the PileSwap-replay of the tail wants the two
  composites to be `swapPiles a h`-conjugate as WHOLE states — they
  are not: `swapPiles` also permutes the deal slices and depths
  (the slates), and no play can permute slates.  The conjugate
  world `σ(W_A)`'s continuation (`map swapM tail`, sound by
  `run_swapPiles`/`solvable_swapPiles_iff`, run-preserved by
  `isWin`'s blindness) sits behind the slate permutation, while
  the reachable composite `W_B` keeps `st`'s slates; the verbatim
  tail replay from `W_B` breaks exactly at (α) any FURTHER king
  landing that reads the swapped `inl`-seat (free at `W_A`, kinged
  at `W_B`, and mirrored at the other slot) and (β) the final strip
  of pile `h` when `depths h = 1` (its attach target `inl h` is
  bare at `W_A`, kinged at `W_B`) — no move mirrors an anchor-seat
  write across a slate position.  Whether `W_B` is solvable
  whenever `W_A` is — equivalently, whether the row holds when the
  second move consumes the vacated anchor with a live slate under
  the pre-existing hole — is the residue's open core.  NOT refuted:
  no countermodel was findable this session (the falsity would need
  the tight all-alternative-heads-lose world, outside decide reach;
  the exchange-claim probes and the SuccLabeledWitness no-hole
  boundary datum live in the wave-FARM row and
  `witnesses/VacateCoReal.lean`).
* `m₂` arbitrary with NO king ever landing on `Sum.inl a` — the
  drop-at-end route (§5.4's third prong): bubble the vacate to the
  end and drop it — `c`'s consumers are seat-relative (`inr`-seat
  reads follow the run; the seated root's own moves read `bottomOf`,
  some at both park and issued shapes), no heights read a
  `pilePile`, and the parked `c` blocks exactly the king landings
  the absent vacate would have freed (route 3 of the plan; its own
  replay invariant is sketched in the FARM row).  [Not elaborated
  here; belongs to the residue only once the corner world's
  excluded.] -/
theorem vacate_secondMove_residue {st : State} {c : Card} {a : Anchor} {b₀ : Base}
    {m₂ : Move} {rest : List Move} {w : State}
    (hwf : st.WF) (hnk : c.rank ≠ Rank.king)
    (hfloor : st.board.bottomOf c = some (Sum.inl a))
    (hfree : ∃ h, st.board.topOf (Sum.inl h) = none)
    (hnod : m₂ ≠ Move.draw) (hnodeck : ∀ x, m₂ ≠ Move.deckStack x)
    (hwin : st.run (Move.pilePile c b₀ :: m₂ :: rest) = some w ∧ w.isWin = true) :
    ∃ play st', st.run play = some st' ∧ st'.isWin = true ∧
      play.head? ≠ some (Move.pilePile c b₀) := sorry

/-- §5.4's third row (the vacate prunability, the empty-slot
boundary): at a WF state that ALREADY has a free anchor, a non-king
tab-to-tab move whose run root sits on an anchor floor — a move that
VACATES a pile, leaving an empty slot — need never be played first.
`hfree` is the sole license for the king-consumer corner: without
it the claim is FALSE — `witnesses/SuccLabeledWitness.lean`'s
anchored-head unseat (all seven anchors occupied, the promotion must
fire first, the king lands on the vacated anchor) is the no-hole
boundary datum in tree.  `hnk` excludes the §5.7/C2KingAnchor
territory (up to seven anchor landings, witnesses/
C2KingAnchorWitness.lean).  No legality premise: an illegal `m` is
vacuously prunable.

Proof (head-only, assembled over the named residue): the vacate is
pure board surgery (`heights_eq_of_apply_pilePile`), so a win
through the vacate ALONE means `st` was already won (`[]` avoids
the head); a winning play that does not start with the vacate is
already the witness; otherwise the play is [`vacate; m₂; …`] and the
two guard-free commutation sectors — `.draw` (`draw_comm_pilePile`,
Commutation:225) and `.deckStack`
(`commute_of_compsDisjoint`'s deckStack×pilePile arm, Commutation:243
/ Frame:912) — swap `m₂` in front by `run_swap_front_of_commEq`
with the SAME end state, and the new head differs.  Every other
second-move kind routes to the named residue above. -/
theorem vacate_pilePile_prunable_of_hole {st : State} {c : Card} {a : Anchor} {b₀ : Base}
    (hwf : st.WF) (hnk : c.rank ≠ Rank.king)
    (hfloor : st.board.bottomOf c = some (Sum.inl a))
    (hfree : ∃ h, st.board.topOf (Sum.inl h) = none) :
    prunableAt st (Move.pilePile c b₀) := by
  intro hsolv
  obtain ⟨play, w, hrun, hwin⟩ := hsolv
  cases play with
  | nil =>
      have h' : (some st : Option State) = some w := hrun
      rw [← Option.some.inj h'] at hwin
      exact ⟨[], st, rfl, hwin, by simp⟩
  | cons m rest =>
      by_cases hm : m = Move.pilePile c b₀
      · subst hm
        cases rest with
        | nil =>
            obtain ⟨s₁, hap, hrest, -⟩ := run_cons_inv hrun
            have hs1w : s₁ = w := by
              have h' : (some s₁ : Option State) = some w := hrest
              exact Option.some.inj h'
            have hhs := heights_eq_of_apply_pilePile hap
            refine ⟨[], st, rfl, ?_, by simp⟩
            rw [← hs1w] at hwin
            rw [isWin_congr_heights hhs] at hwin
            exact hwin
        | cons m₂ rest' =>
            cases m₂ with
            | draw =>
                refine ⟨Move.draw :: Move.pilePile c b₀ :: rest', w,
                  run_swap_front_of_commEq (draw_comm_pilePile st c b₀) hrun, hwin, ?_⟩
                intro hcon
                exact Move.noConfusion (Option.some.inj hcon)
            | deckStack x =>
                have hcomm : (st.apply (Move.deckStack x) >>= fun s =>
                    s.apply (Move.pilePile c b₀))
                    = (st.apply (Move.pilePile c b₀) >>= fun s => s.apply (Move.deckStack x)) := by
                  refine commute_of_compsDisjoint st (Move.deckStack x) (Move.pilePile c b₀) ?_
                  intro x₂ hx hx'
                  simp only [Move.comps] at hx hx'
                  cases x₂ <;> simp_all
                refine ⟨Move.deckStack x :: Move.pilePile c b₀ :: rest', w,
                  run_swap_front_of_commEq hcomm hrun, hwin, ?_⟩
                intro hcon
                exact Move.noConfusion (Option.some.inj hcon)
            | reveal x' =>
                exact vacate_secondMove_residue hwf hnk hfloor hfree
                  (by intro hcon; cases hcon) (by intro _ hcon; cases hcon) ⟨hrun, hwin⟩
            | deckPile x' b' =>
                exact vacate_secondMove_residue hwf hnk hfloor hfree
                  (by intro hcon; cases hcon) (by intro _ hcon; cases hcon) ⟨hrun, hwin⟩
            | pileStack x' =>
                exact vacate_secondMove_residue hwf hnk hfloor hfree
                  (by intro hcon; cases hcon) (by intro _ hcon; cases hcon) ⟨hrun, hwin⟩
            | stackPile x' b' =>
                exact vacate_secondMove_residue hwf hnk hfloor hfree
                  (by intro hcon; cases hcon) (by intro _ hcon; cases hcon) ⟨hrun, hwin⟩
            | pilePile x' b' =>
                exact vacate_secondMove_residue hwf hnk hfloor hfree
                  (by intro hcon; cases hcon) (by intro _ hcon; cases hcon) ⟨hrun, hwin⟩
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
    | reveal a =>
        obtain ⟨_, _, _, _, _, hs⟩ := (apply_reveal_iff (st := st) (st' := st')).mp hap
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


