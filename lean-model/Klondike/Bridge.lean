import Klondike.Realizability
import Klondike.Macro

/-!
# The engine bridge — the abstract game and the projection

The engine's side of the ledger: the state forgets where visible
cards sit (the visible set + depths + heights + deck order/offset),
and the deck moves are jump-then-play (no raw draw — the offset
advances through them; the model-side counterpart is the guarded jump
`State.applyDrawTo` and the jump-soundness theorems).  Legality is
*witness-existential over realizing boards* — the spec the engine's
mask algebra implements.  At draw-1 the offset constrains nothing
(`reachablePos_step1`: every remaining card is drawable) — it
matters at draw ≥ 2, the pacing the accessible-set guard carries,
and for the engine's transposition identity, which is why the
sweep/canonicalization is sound there.
-/

/-- The engine's abstract state: the model's state with the matching
quotiented to the visible set; the deck carried as (order, offset) —
the pair the 61-bit encode packs. -/
structure EState where
  /-- The fixed deal. -/
  deal : Deal
  /-- The visible tableau set (positions forgotten). -/
  vis : Card → Bool
  /-- The hidden boundary per pile. -/
  depths : Anchor → Nat
  /-- Foundation heights per suit. -/
  heights : Suit → Nat
  /-- The remaining deck, in order. -/
  order : List Card
  /-- The draw offset: cards before it have been passed. -/
  offset : Nat
  /-- The game's draw step. -/
  drawStep : Nat

namespace EState

/-- The topmost hidden card of pile `a` (deal-determined). -/
def topHiddenOf (e : EState) (a : Anchor) : Option Card :=
  ((e.deal.piles a).take (e.depths a)).getLast?

/-- A board realizes the abstract state: a fitting matching whose
image is exactly the visible set. -/
def realizedBy (e : EState) (bd : Board) : Prop :=
  bd.Fits e.deal e.depths ∧ ∀ c, (bd.bottomOf c).isSome = e.vis c

/-- Realizable: some realizing board exists (B1's invariant). -/
def realizable (e : EState) : Prop := ∃ bd, e.realizedBy bd

/-- Won: all foundations complete. -/
def isWin (e : EState) : Bool :=
  Suit.all.all fun s => decide (e.heights s = 13)

end EState

/-- Board-level placement legality (the model's `State.canPlace`
lifted off the state). -/
def Board.canPlaceOn (bd : Board) (c : Card) (b : Base) : Bool :=
  decide (bd.topOf b = none) &&
  match b with
  | Sum.inl _ => decide (c.rank = Rank.king)
  | Sum.inr d => (bd.bottomOf d).isSome && canSitOn c d

/-- The engine's five moves. -/
inductive EMove : Type where
  /-- Flip the hidden card under the visible `c`. -/
  | reveal (c : Card)
  /-- Rotate to `c`, play it to the tableau (visible, no position). -/
  | deckPile (c : Card)
  /-- Rotate to `c`, stack it. -/
  | deckStack (c : Card)
  /-- A visible top to the foundation. -/
  | pileStack (c : Card)
  /-- The foundation top back to the tableau. -/
  | stackPile (c : Card)
  deriving DecidableEq

/-- The abstract transition — witness-existential semantics: each
guard demands a realizing board that justifies the move (no_pile §3's
maintenance table). -/
def eStep : EState → EMove → EState → Prop
  | e, .pileStack c, e' =>
      e.vis c = true ∧ c.rank.toIdx = e.heights c.suit ∧
      ∃ bd, e.realizedBy bd ∧ bd.topOf (Sum.inr c) = none ∧
      e' = { e with
        vis := fun c' => decide (c' ≠ c) && e.vis c',
        heights := fun s => if s = c.suit then e.heights s + 1 else e.heights s }
  | e, .deckPile c, e' =>
      (∃ bd, e.realizedBy bd ∧ ∃ b, bd.canPlaceOn c b = true) ∧
      ∃ i, e.order[i]? = some c ∧
      e' = { e with
        vis := fun c' => e.vis c' || decide (c' = c),
        order := Cycle.removeIdx e.order i,
        offset := i }
  | e, .deckStack c, e' =>
      c.rank.toIdx = e.heights c.suit ∧
      ∃ i, e.order[i]? = some c ∧
      e' = { e with
        order := Cycle.removeIdx e.order i,
        offset := i,
        heights := fun s => if s = c.suit then e.heights s + 1 else e.heights s }
  | e, .stackPile c, e' =>
      c.rank.toIdx + 1 = e.heights c.suit ∧
      (∃ bd, e.realizedBy bd ∧ ∃ b, bd.canPlaceOn c b = true) ∧
      e' = { e with
        vis := fun c' => e.vis c' || decide (c' = c),
        heights := fun s => if s = c.suit then e.heights s - 1 else e.heights s }
  | e, .reveal c, e' =>
      e.vis c = true ∧
      ∃ bd a r, e.realizedBy bd ∧ bd.topOf (Sum.inr c) = none ∧
        bd.bottomOf c = some (Sum.inr r) ∧ e.topHiddenOf a = some r ∧
        e' = { e with
          vis := fun c' => e.vis c' || decide (c' = r),
          depths := fun a' => if a' = a then e.depths a - 1 else e.depths a' }

/-- Chaining abstract plays. -/
def eRun : EState → List EMove → EState → Prop
  | e, [], e' => e = e'
  | e, m :: ms, e' => ∃ e'', eStep e m e'' ∧ eRun e'' ms e'

/-- Abstract solvability: a winning abstract play exists. -/
def EState.esolvable (e : EState) : Prop :=
  ∃ play w, eRun e play w ∧ w.isWin = true

/-- The projection: forget the matching, keep its image — the Cycle
unpacks directly into the engine's order/offset pair. -/
def toEngine (st : State) : EState where
  deal := st.deal
  vis := st.isVis
  depths := st.depths
  heights := st.heights
  order := st.stock.cards
  offset := st.stock.cursor
  drawStep := st.drawStep

/-! ## The bridge theorems -/

/-- No `eStep` guard reads the offset: a move legal in `e` is legal in
the offset-rewritten `e`, and the successors correspond the same way
(the deck moves overwrite the offset with the draw index; every other
move carries the rewrite through). -/
theorem eStep_offset {e e' : EState} {m : EMove} (h : eStep e m e') (k : Nat) :
    ∃ e'' j, eStep { e with offset := k } m e'' ∧ e'' = { e' with offset := j } := by
  cases m with
  | pileStack c =>
    simp only [eStep] at h
    obtain ⟨hv, hr, bd, hbd, htop, he'⟩ := h
    subst he'
    exact ⟨_, k, ⟨hv, hr, bd, hbd, htop, rfl⟩, rfl⟩
  | deckPile c =>
    simp only [eStep] at h
    obtain ⟨⟨bd, hbd, b, hb⟩, i, hc, he'⟩ := h
    subst he'
    exact ⟨_, i, ⟨⟨bd, hbd, b, hb⟩, i, hc, rfl⟩, rfl⟩
  | deckStack c =>
    simp only [eStep] at h
    obtain ⟨hr, i, hc, he'⟩ := h
    subst he'
    exact ⟨_, i, ⟨hr, i, hc, rfl⟩, rfl⟩
  | stackPile c =>
    simp only [eStep] at h
    obtain ⟨hr, ⟨bd, hbd, b, hb⟩, he'⟩ := h
    subst he'
    exact ⟨_, k, ⟨hr, ⟨bd, hbd, b, hb⟩, rfl⟩, rfl⟩
  | reveal c =>
    simp only [eStep] at h
    obtain ⟨hv, bd, a, r, hbd, htop, hbot, hth, he'⟩ := h
    subst he'
    exact ⟨_, k, ⟨hv, bd, a, r, hbd, htop, hbot, hth, rfl⟩, rfl⟩

/-- The play-level lift: a play from `e` runs from the offset-rewritten
state too, ending likewise offset-rewritten. -/
theorem eRun_offset :
    ∀ (play : List EMove) (e w : EState), eRun e play w → ∀ (k : Nat),
      ∃ w' j, eRun { e with offset := k } play w' ∧ w' = { w with offset := j } := by
  intro play
  induction play with
  | nil =>
    intro e w h k
    have he : e = w := h
    have hk : { e with offset := k } = { w with offset := k } := by rw [he]
    exact ⟨_, k, rfl, hk⟩
  | cons m ms ih =>
    intro e w h k
    obtain ⟨e₁, hs, hr⟩ := h
    obtain ⟨e₂, j, hs', he₂⟩ := eStep_offset hs k
    obtain ⟨w', j', hr', hw'⟩ := ih e₁ w hr j
    subst he₂
    exact ⟨w', j', ⟨_, hs', hr'⟩, hw'⟩

/-- The win predicate reads only the heights. -/
theorem isWin_offset (e : EState) (j : Nat) : ({ e with offset := j }).isWin = e.isWin := rfl

/-- The offset is solvability-irrelevant at draw-1 — the engine's
pure-deck fact, the sweep's license (the canonicalization rotating
the deck to a fixed offset).  In this v1 encoding it is nearly
definitional (no guard reads the offset); the content arrives with
the draw-3 pacing rules. -/
theorem esolvable_offset_irrel {e : EState} (_hstep : e.drawStep = 1) (k : Nat) :
    e.esolvable ↔ { e with offset := k }.esolvable := by
  constructor
  · intro hsol
    obtain ⟨play, w, hr, hw⟩ := hsol
    obtain ⟨w', j, hr', hw'⟩ := eRun_offset play e w hr k
    exact ⟨play, w', hr', by rw [hw', isWin_offset]; exact hw⟩
  · intro hsol
    obtain ⟨play, w, hr, hw⟩ := hsol
    obtain ⟨w', j, hr', hw'⟩ := eRun_offset play { e with offset := k } w hr e.offset
    exact ⟨play, w', hr', by rw [hw', isWin_offset]; exact hw⟩

/-! ## The simulation toolkit -/

/-- The ext lemma for abstract states (function fields via `funext`). -/
theorem estate_ext {e₁ e₂ : EState} (h1 : e₁.deal = e₂.deal)
    (h2 : ∀ c, e₁.vis c = e₂.vis c) (h3 : ∀ a, e₁.depths a = e₂.depths a)
    (h4 : ∀ s, e₁.heights s = e₂.heights s) (h5 : e₁.order = e₂.order)
    (h6 : e₁.offset = e₂.offset) (h7 : e₁.drawStep = e₂.drawStep) :
    e₁ = e₂ := by
  cases e₁ with
  | mk d1 v1 dp1 hg1 o1 of1 ds1 =>
    cases e₂ with
    | mk d2 v2 dp2 hg2 o2 of2 ds2 =>
      simp only [EState.mk.injEq]
      exact ⟨h1, funext h2, funext h3, funext h4, h5, h6, h7⟩

/-- After detaching at `b`: the detached card itself is no longer seated
(the `bottomOf_detach_ne` sibling). -/
theorem bottomOf_detach_self {bd : Board} {b : Base} {c : Card}
    (hbot : bd.topOf b = some c) : (bd.detach b).bottomOf c = none := by
  refine (Board.bottomOf_eq_none _ c).mpr (fun b' hb' => ?_)
  by_cases hbb : b' = b
  · subst hbb
    rw [Board.detach_topOf] at hb'
    simp at hb'
  · rw [Board.detach_topOf_ne _ _ _ hbb] at hb'
    exact hbb (bd.inj b' b c hb' hbot)

/-- The model's own board realizes its projection — WF's board-edges
conjunction *is* `Fits` (Realizability's `realizable_of_wf`, at the
board level). -/
theorem toEngine_realizedBy_board {st : State} (hwf : st.WF) :
    (toEngine st).realizedBy st.board := by
  refine ⟨?_, fun _ => rfl⟩
  intro b c hb
  exact (hwf.board_edges b c hb).2

/-- One model `pileStack` is one abstract `pileStack` (the model's own
board is the realizing witness). -/
theorem toEngine_step_pileStack {st st' : State} {c : Card} (hwf : st.WF)
    (h : st.apply (Move.pileStack c) = some st') :
    eStep (toEngine st) (EMove.pileStack c) (toEngine st') := by
  rw [apply_pileStack_iff] at h
  obtain ⟨htop, b, hbot, hrk, hst⟩ := h
  have htb : st.board.topOf b = some c := (Board.bottomOf_eq st.board c b).mp hbot
  have hvis : (toEngine st).vis c = true := by
    show (st.board.bottomOf c).isSome = true
    rw [hbot]
    rfl
  refine ⟨hvis, hrk, st.board, toEngine_realizedBy_board hwf, htop, ?_⟩
  rw [hst]
  apply estate_ext
  · rfl
  · intro c'
    show ((st.board.detach b).bottomOf c').isSome
      = (decide (c' ≠ c) && (st.board.bottomOf c').isSome)
    by_cases hcc : c' = c
    · subst hcc
      rw [bottomOf_detach_self htb, decide_eq_false (fun hh => hh rfl), Bool.false_and]
      rfl
    · rw [bottomOf_detach_ne htb hcc, decide_eq_true hcc, Bool.true_and]
  · intro _; rfl
  · intro s; rfl
  · rfl
  · rfl
  · rfl

/-- One model `deckPile` is one abstract `deckPile`, the drawn index
being the cursor step-down. -/
theorem toEngine_step_deckPile {st st' : State} {c : Card} {b : Base} (hwf : st.WF)
    (h : st.apply (Move.deckPile c b) = some st') :
    eStep (toEngine st) (EMove.deckPile c) (toEngine st') := by
  rw [apply_deckPile_iff] at h
  obtain ⟨hprev, hcp, bd, hatt, hst⟩ := h
  simp only [Cycle.prev] at hprev
  by_cases hcur : st.stock.cursor = 0
  · rw [if_pos hcur] at hprev; simp at hprev
  · rw [if_neg hcur] at hprev
    refine ⟨⟨st.board, toEngine_realizedBy_board hwf, b, hcp⟩, st.stock.cursor - 1, hprev, ?_⟩
    rw [hst]
    apply estate_ext
    · rfl
    · intro c'
      show (bd.bottomOf c').isSome
        = ((st.board.bottomOf c').isSome || decide (c' = c))
      by_cases hcc : c' = c
      · subst hcc
        rw [(Board.bottomOf_eq _ _ _).mpr (Board.attach_topOf _ _ _ hatt),
          decide_eq_true rfl, Bool.or_true]
        rfl
      · rw [decide_eq_false hcc, Bool.or_false, bottomOf_attach_of_ne hatt hcc]
    · intro _; rfl
    · intro _; rfl
    · rfl
    · show (if st.stock.cursor - 1 < st.stock.cursor then st.stock.cursor - 1
        else st.stock.cursor) = st.stock.cursor - 1
      rw [if_pos (by omega)]
    · rfl

/-- One model `deckStack` is one abstract `deckStack` (no realizing
witness is needed — the guard is rank and position only). -/
theorem toEngine_step_deckStack {st st' : State} {c : Card}
    (h : st.apply (Move.deckStack c) = some st') :
    eStep (toEngine st) (EMove.deckStack c) (toEngine st') := by
  rw [apply_deckStack_iff] at h
  obtain ⟨hprev, hrk, hst⟩ := h
  simp only [Cycle.prev] at hprev
  by_cases hcur : st.stock.cursor = 0
  · rw [if_pos hcur] at hprev; simp at hprev
  · rw [if_neg hcur] at hprev
    refine ⟨hrk, st.stock.cursor - 1, hprev, ?_⟩
    rw [hst]
    apply estate_ext
    · rfl
    · intro _; rfl
    · intro _; rfl
    · intro s; rfl
    · rfl
    · show (if st.stock.cursor - 1 < st.stock.cursor then st.stock.cursor - 1
        else st.stock.cursor) = st.stock.cursor - 1
      rw [if_pos (by omega)]
    · rfl

/-- One model `stackPile` is one abstract `stackPile`. -/
theorem toEngine_step_stackPile {st st' : State} {c : Card} {b : Base} (hwf : st.WF)
    (h : st.apply (Move.stackPile c b) = some st') :
    eStep (toEngine st) (EMove.stackPile c) (toEngine st') := by
  rw [apply_stackPile_iff] at h
  obtain ⟨hrk, hcp, bd, hatt, hst⟩ := h
  refine ⟨hrk, ⟨st.board, toEngine_realizedBy_board hwf, b, hcp⟩, ?_⟩
  rw [hst]
  apply estate_ext
  · rfl
  · intro c'
    show (bd.bottomOf c').isSome
      = ((st.board.bottomOf c').isSome || decide (c' = c))
    by_cases hcc : c' = c
    · subst hcc
      rw [(Board.bottomOf_eq _ _ _).mpr (Board.attach_topOf _ _ _ hatt),
        decide_eq_true rfl, Bool.or_true]
      rfl
    · rw [decide_eq_false hcc, Bool.or_false, bottomOf_attach_of_ne hatt hcc]
  · intro _; rfl
  · intro s; rfl
  · rfl
  · rfl
  · rfl

/-- One model `reveal` is one abstract `reveal` (the trigger's pile's
boundary card is the abstract `topHiddenOf`). -/
theorem toEngine_step_reveal {st st' : State} {c : Card} (hwf : st.WF)
    (h : st.apply (Move.reveal c) = some st') :
    eStep (toEngine st) (EMove.reveal c) (toEngine st') := by
  rw [apply_reveal_iff] at h
  obtain ⟨htop, r, a, bd, hbot, hpth, hatt, hst⟩ := h
  have hth : (toEngine st).topHiddenOf a = some r :=
    of_decide_eq_true (findFirst_mem _ _ _ hpth).2
  have hvis : (toEngine st).vis c = true := by
    show (st.board.bottomOf c).isSome = true
    rw [hbot]
    rfl
  refine ⟨hvis, st.board, a, r, toEngine_realizedBy_board hwf, htop, hbot, hth, ?_⟩
  rw [hst]
  apply estate_ext
  · rfl
  · intro c'
    show (bd.bottomOf c').isSome
      = ((st.board.bottomOf c').isSome || decide (c' = r))
    by_cases hcc : c' = r
    · subst hcc
      rw [(Board.bottomOf_eq _ _ _).mpr (Board.attach_topOf _ _ _ hatt),
        decide_eq_true rfl, Bool.or_true]
      rfl
    · rw [decide_eq_false hcc, Bool.or_false, bottomOf_attach_of_ne hatt hcc]
  · intro a'; rfl
  · intro _; rfl
  · rfl
  · rfl
  · rfl

/-- The play-level simulation invariant: an engine play from `st`
projects to an abstract play that tracks everything but the offset
(draws collapse into offset shifts, `eRun_offset`'s content). -/
theorem toEngine_run : ∀ (play : List Move) (st st' : State), st.WF →
    (∀ m ∈ play, m.isEngine = true) → st.run play = some st' →
    ∃ eplay w j, eRun (toEngine st) eplay w ∧ w = {toEngine st' with offset := j} := by
  intro play
  induction play with
  | nil =>
      intro st st' _ _ h
      have heq : st = st' := Option.some.inj h
      subst heq
      exact ⟨[], toEngine st, st.stock.cursor, rfl, rfl⟩
  | cons m ms ih =>
      intro st st' hwf heng h
      obtain ⟨s₁, hap, hrest, _⟩ := run_cons_inv h
      have hwf₁ := apply_wf hwf m s₁ hap
      have hms : ∀ m' ∈ ms, m'.isEngine = true :=
        fun m' hm' => heng m' (List.mem_cons_of_mem _ hm')
      have hmeng := heng m (by simp)
      obtain ⟨eplay, w, j, hr, hw⟩ := ih s₁ st' hwf₁ hms hrest
      cases m with
      | draw =>
          rw [apply_draw_iff] at hap
          subst hap
          obtain ⟨w', j', hr', hw'⟩ :=
            eRun_offset eplay (toEngine {st with stock := st.stock.dealOnce st.drawStep}) w hr
              st.stock.cursor
          have hkey : {toEngine {st with stock := st.stock.dealOnce st.drawStep} with
              offset := st.stock.cursor} = toEngine st := by
            apply estate_ext
            · rfl
            · intro _; rfl
            · intro _; rfl
            · intro _; rfl
            · show (st.stock.dealOnce st.drawStep).cards = st.stock.cards
              exact Cycle.dealOnce_cards _ _
            · rfl
            · rfl
          rw [hkey] at hr'
          refine ⟨eplay, w', j', hr', ?_⟩
          rw [hw', hw]
      | pileStack c =>
          exact ⟨EMove.pileStack c :: eplay, w, j,
            ⟨toEngine s₁, toEngine_step_pileStack hwf hap, hr⟩, hw⟩
      | deckPile c b =>
          exact ⟨EMove.deckPile c :: eplay, w, j,
            ⟨toEngine s₁, toEngine_step_deckPile hwf hap, hr⟩, hw⟩
      | deckStack c =>
          exact ⟨EMove.deckStack c :: eplay, w, j,
            ⟨toEngine s₁, toEngine_step_deckStack hap, hr⟩, hw⟩
      | reveal c =>
          exact ⟨EMove.reveal c :: eplay, w, j,
            ⟨toEngine s₁, toEngine_step_reveal hwf hap, hr⟩, hw⟩
      | stackPile c b =>
          exact ⟨EMove.stackPile c :: eplay, w, j,
            ⟨toEngine s₁, toEngine_step_stackPile hwf hap, hr⟩, hw⟩
      | pilePile c b => simp [Move.isEngine] at hmeng

/-- The simulation: every model engine play projects to an abstract
play with the same winning outcome.  Draws before a deck move
collapse into its rotation; trailing draws shift only the offset,
which the win predicate does not read.

Statement repair (2026-09-13): gained `(hwf : st.WF)` — without it
the theorem is FALSE (prover-confirmed witness in the session
scratch `Temp\opencode\SimWitness.lean`): a non-WF state whose board
seats a card on an unseatable base wins by model `pileStack`s while
the abstract game is frozen (no realizing board exists, so every
witness-demanding `eStep` guard fails).  WF supplies the witness:
the model's own board realizes `toEngine st`
(`toEngine_realizedBy_board`). -/
theorem toEngine_simulates {st st' : State} {play : List Move}
    (hwf : st.WF) (hengine : ∀ m ∈ play, m.isEngine = true) (h : st.run play = some st') :
    ∃ eplay w, eRun (toEngine st) eplay w ∧ w.isWin = st'.isWin := by
  obtain ⟨eplay, w, j, hr, hw⟩ := toEngine_run play st st' hwf hengine h
  exact ⟨eplay, w, hr, by rw [hw, isWin_offset]; rfl⟩

/-- The lift — the B-legs' content: every abstract winning play lifts
to a model engine play.  Each abstract move's witness board may
differ from the model's current arrangement, and the bridging plays
are exactly the accommodations (stack↔pile shuffling) — the
compression/reshape arguments.

Statement repair (2026-09-13): gated to draw-1.  The model's engine
game is physically paced (`dealOnce`/`prev`); the abstract deck
moves are still free jumps — at draw ≥ 2 the abstract game can jump
to positions the physical deal cannot reach, and the lift fails.
The all-steps generalization needs the `eStep` pacing guard (the
order/offset `maskPos`) plus the offset-rewrite lemma's replacement
— deck.rs's `equivalent_to` (accessible-set equality), not raw offset
irrelevance.  That is reading work, not farm work (the deferred
list).

**REFUTED AS STATED (prover-confirmed 2026-09-13, orchestrator
sign-off pending — scratch `Temp\opencode\LiftWitness.lean`, exit 0)**:
UNSOUND even draw-1-gated on a WF state.  Witness `stX`: ♥/♦/♣
complete, ♠ at 12; the model board seats ♥Q on ♠K (a legal
`canSitOn` edge), so the model's `pileStack ♠K` is blocked and ♥Q is
immovable; every other engine move is illegal and `.draw` is the
identity (empty stock) — so `¬ stX.solvableEngine`.  Yet the abstract
game wins in ONE move: `pileStack ♠K` through the witness board `bdW`
seating ♥Q on ♣5 — its deal-adjacent neighbor in pile p2 — which
`Board.Fits`'s deal-adjacency clause accepts WITHOUT requiring the
base to be hidden or visible.  The model's `canPlace` demands a
visible card base, so that arrangement is unreachable: the witness
boards are strictly more permissive than the model's game.

Root cause: the deal-adjacency clause of `Fits` (shared with
`Realizability.realizable_of_wf`, where it mirrors WF's
`board_edges`).  A repair — e.g. the deal-adjacent base must lie
within the hidden prefix (`t.length < depths a`) or be visible —
cascades: `realizable_of_wf` (proven) would need WF to track
deal-adjacent bases, and `toEngine_simulates`'s witnesses (the
model's own board) would need the strengthened condition, which WF
does not give.  This is a design-level decision (the abstraction's
honest-invariant), beyond a farm statement repair; with it in place
the remaining work is still the B4 accommodation argument. -/
theorem toEngine_lifts {st : State} {eplay : List EMove} {w : EState} (hwf : st.WF)
    (hstep : st.drawStep = 1)
    (hrun : eRun (toEngine st) eplay w) (hwin : w.isWin = true) :
    st.solvableEngine := sorry

/-- **The bridge theorem**: the model's engine game and the abstract
game agree on solvability — `toEngine` is a solvability-isomorphism.
Combines the simulation with the lift.  Draw-1 gated as the lift
(the all-steps form awaits the `eStep` pacing guard — see
`toEngine_lifts`'s note).

**The ← direction is REFUTED** by `toEngine_lifts`'s witness (same
scratch): `(toEngine stX).esolvable` holds while
`¬ stX.solvableEngine`.  The → direction (the simulation) is proven
below; the remaining `sorry` is exactly the refuted half. -/
theorem engine_iff {st : State} (hwf : st.WF) (hstep : st.drawStep = 1) :
    st.solvableEngine ↔ (toEngine st).esolvable := by
  constructor
  · intro hsol
    obtain ⟨play, heng, st', hrun, hwin⟩ := hsol
    obtain ⟨eplay, w, hrun', hw⟩ := toEngine_simulates hwf heng hrun
    exact ⟨eplay, w, hrun', by rw [hw, hwin]⟩
  · sorry

/-! ## C2, EMove level

Each EMove's successor is unique — the realizing witness *justifies*
but does not *shape* the successor.  (`reveal`'s successor varies
only by the witness pile, definitionally in this encoding; the
macro-level ≤2 — tableau vs stack closure classes — needs the
commitment closure on EState, deferred to the macro layer.) -/

/-- A `pileStack`'s successor is unique: the realizing witness only
justifies the guard; the successor is the same literal either way. -/
theorem eStep_pileStack_unique {e e' e'' : EState} {c : Card}
    (h₁ : eStep e (.pileStack c) e') (h₂ : eStep e (.pileStack c) e'') : e' = e'' := by
  simp only [eStep] at h₁ h₂
  obtain ⟨-, -, ⟨-, -, -, he'⟩⟩ := h₁
  obtain ⟨-, -, ⟨-, -, -, he''⟩⟩ := h₂
  exact he'.trans he''.symm

/-- A `deckPile`'s successor is unique: the draw position is pinned
by `noDupCards` (the order holds each card at most once), and the
successor is a literal of it. -/
theorem eStep_deckPile_unique {e e' e'' : EState} {c : Card}
    (hnd : noDupCards e.order)
    (h₁ : eStep e (.deckPile c) e') (h₂ : eStep e (.deckPile c) e'') : e' = e'' := by
  simp only [eStep] at h₁ h₂
  obtain ⟨⟨-, -, -, -⟩, i₁, hc₁, he'⟩ := h₁
  obtain ⟨⟨-, -, -, -⟩, i₂, hc₂, he''⟩ := h₂
  have hlt₁ : i₁ < e.order.length := (List.getElem?_eq_some_iff.mp hc₁).1
  have hlt₂ : i₂ < e.order.length := (List.getElem?_eq_some_iff.mp hc₂).1
  have hij : i₁ = i₂ := hnd i₁ i₂ hlt₁ hlt₂ (hc₁.trans hc₂.symm)
  subst hij
  exact he'.trans he''.symm

/-- A `deckStack`'s successor is unique: as `deckPile`, the draw
position is pinned by `noDupCards` (the successor reads it through
`order`/`offset`, so uniqueness needs the order duplicate-free). -/
theorem eStep_deckStack_unique {e e' e'' : EState} {c : Card}
    (hnd : noDupCards e.order)
    (h₁ : eStep e (.deckStack c) e') (h₂ : eStep e (.deckStack c) e'') : e' = e'' := by
  simp only [eStep] at h₁ h₂
  obtain ⟨-, i₁, hc₁, he'⟩ := h₁
  obtain ⟨-, i₂, hc₂, he''⟩ := h₂
  have hlt₁ : i₁ < e.order.length := (List.getElem?_eq_some_iff.mp hc₁).1
  have hlt₂ : i₂ < e.order.length := (List.getElem?_eq_some_iff.mp hc₂).1
  have hij : i₁ = i₂ := hnd i₁ i₂ hlt₁ hlt₂ (hc₁.trans hc₂.symm)
  subst hij
  exact he'.trans he''.symm

/-- A `stackPile`'s successor is unique: as `pileStack`, the witness
only justifies; the successor is a literal of `e` and `c`. -/
theorem eStep_stackPile_unique {e e' e'' : EState} {c : Card}
    (h₁ : eStep e (.stackPile c) e') (h₂ : eStep e (.stackPile c) e'') : e' = e'' := by
  simp only [eStep] at h₁ h₂
  obtain ⟨-, ⟨-, -, -⟩, he'⟩ := h₁
  obtain ⟨-, ⟨-, -, -⟩, he''⟩ := h₂
  exact he'.trans he''.symm

/-! Deferred and recorded:

- **The `bm` XOR algebra** (B1's engine side): the literal mask
  computation of `uncovered_t > 0` on EState's tracked masks, proved
  equal to the witness-existential guards here.  Needs the engine's
  mask-maintenance reading (state.rs) — do not guess.
- **The 61-bit encode**: packing/injectivity of EState — the
  cross-validation enabler against the Rust solver.
- **The draw-3 pacing** (last_draw_rules.md): which offsets are
  playable per pass — the constraint that makes the offset
  non-vestigial. -/
