import Klondike.Realizability

/-!
# The engine bridge — the abstract game and the projection

The engine's side of the ledger: the state forgets where visible
cards sit (the visible set + depths + heights + deck order/offset),
and the deck moves are rotate-then-play (no raw draw — the offset
advances through them).  Legality is *witness-existential over
realizing boards* — the spec the engine's mask algebra implements.
At draw-1 the offset constrains nothing (every card is drawable by
rotating; the worry-back is unlimited) — it matters only for the
draw-3 pacing rules and the engine's transposition identity, which is
why the sweep/canonicalization is sound there.
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

/-- The offset is solvability-irrelevant at draw-1 — the engine's
pure-deck fact, the sweep's license (the canonicalization rotating
the deck to a fixed offset).  In this v1 encoding it is nearly
definitional (no guard reads the offset); the content arrives with
the draw-3 pacing rules.  TODO. -/
theorem esolvable_offset_irrel {e : EState} (hstep : e.drawStep = 1) (k : Nat) :
    e.esolvable ↔ { e with offset := k }.esolvable := sorry

/-- The simulation: every model engine play projects to an abstract
play with the same winning outcome.  Draws before a deck move
collapse into its rotation; trailing draws shift only the offset,
which the win predicate does not read.  TODO: induction on the play. -/
theorem toEngine_simulates {st st' : State} {play : List Move}
    (hengine : ∀ m ∈ play, m.isEngine = true) (h : st.run play = some st') :
    ∃ eplay w, eRun (toEngine st) eplay w ∧ w.isWin = st'.isWin := sorry

/-- The lift — the B-legs' content: every abstract winning play lifts
to a model engine play.  Each abstract move's witness board may
differ from the model's current arrangement, and the bridging plays
are exactly the accommodations (stack↔pile shuffling) — the
compression/reshape arguments.  TODO. -/
theorem toEngine_lifts {st : State} {eplay : List EMove} {w : EState} (hwf : st.WF)
    (hrun : eRun (toEngine st) eplay w) (hwin : w.isWin = true) :
    st.solvableEngine := sorry

/-- **The bridge theorem**: the model's engine game and the abstract
game agree on solvability — `toEngine` is a solvability-isomorphism.
Combines the simulation with the lift.  TODO. -/
theorem engine_iff {st : State} (hwf : st.WF) :
    st.solvableEngine ↔ (toEngine st).esolvable := sorry

/-! ## C2, EMove level

Each EMove's successor is unique — the realizing witness *justifies*
but does not *shape* the successor.  (`reveal`'s successor varies
only by the witness pile, definitionally in this encoding; the
macro-level ≤2 — tableau vs stack closure classes — needs the
commitment closure on EState, deferred to the macro layer.) -/

/-- TODO. -/
theorem eStep_pileStack_unique {e e' e'' : EState} {c : Card}
    (h₁ : eStep e (.pileStack c) e') (h₂ : eStep e (.pileStack c) e'') : e' = e'' := sorry

/-- TODO: the draw position is unique — the order has no duplicates
under WF. -/
theorem eStep_deckPile_unique {e e' e'' : EState} {c : Card}
    (hnd : noDupCards e.order)
    (h₁ : eStep e (.deckPile c) e') (h₂ : eStep e (.deckPile c) e'') : e' = e'' := sorry

/-- TODO. -/
theorem eStep_deckStack_unique {e e' e'' : EState} {c : Card}
    (h₁ : eStep e (.deckStack c) e') (h₂ : eStep e (.deckStack c) e'') : e' = e'' := sorry

/-- TODO. -/
theorem eStep_stackPile_unique {e e' e'' : EState} {c : Card}
    (h₁ : eStep e (.stackPile c) e') (h₂ : eStep e (.stackPile c) e'') : e' = e'' := sorry

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
