import Klondike.State

/-!
# Moves: the one semantic function

The model is the *full physical game* — `pilePile` included.  The
engine's restricted move set (no pile→pile; no_pile_to_pile.md) is the
predicate `Move.isEngine`, and the restriction's soundness — the
ledger's B-legs — is the theorem `solvable_engine_iff`: one model, a
move subset, an equivalence — not two formalizations and a
correspondence.

`apply : Move → State → Option State` is the single source of truth;
`legal`, and everything downstream, derives from it.
-/

/-- A move in the physical game. -/
inductive Move : Type where
  /-- Advance the stock cursor by `drawStep` (worry-back on wrap). -/
  | draw
  /-- Reveal the hidden card under the visible card `c`. -/
  | reveal (c : Card)
  /-- Waste top `c` onto the tableau base `b`. -/
  | deckPile (c : Card) (b : Base)
  /-- Waste top `c` onto the foundation. -/
  | deckStack (c : Card)
  /-- Visible top `c` onto the foundation. -/
  | pileStack (c : Card)
  /-- Foundation top `c` back onto the tableau base `b`. -/
  | stackPile (c : Card) (b : Base)
  /-- Move the visible card `c` — with its whole run — onto the
  tableau base `b`.  In the matching this is a one-edge rewire: the
  cards above `c` keep their edges to `c` and follow for free. -/
  | pilePile (c : Card) (b : Base)
  deriving DecidableEq

/-- The engine's restricted move set: everything but pile→pile. -/
def Move.isEngine : Move → Bool
  | .draw => true
  | .reveal _ => true
  | .deckPile _ _ => true
  | .deckStack _ => true
  | .pileStack _ => true
  | .stackPile _ _ => true
  | .pilePile _ _ => false

/-- Twin-swap on moves. -/
def Move.flipMove : Move → Move
  | .draw => .draw
  | .reveal c => .reveal c.flipSuit
  | .deckPile c b => .deckPile c.flipSuit b.flipBase
  | .deckStack c => .deckStack c.flipSuit
  | .pileStack c => .pileStack c.flipSuit
  | .stackPile c b => .stackPile c.flipSuit b.flipBase
  | .pilePile c b => .pilePile c.flipSuit b.flipBase

namespace State

def applyDraw (st : State) : Option State :=
  some { st with stock := st.stock.rotate st.drawStep }

def applyReveal (st : State) (c : Card) : Option State :=
  match st.board.topOf (Sum.inr c) with
  | some _ => none
  | none =>
    match st.board.bottomOf c with
    | some (Sum.inr r) =>
      match st.pileOfTopHidden r with
      | none => none
      | some a =>
        match st.board.attach (st.hiddenBase a) r with
        | none => none
        | some bd =>
          some { st with
            board := bd,
            depths := fun a' => if a' = a then st.depths a - 1 else st.depths a' }
    | _ => none

def applyDeckPile (st : State) (c : Card) (b : Base) : Option State :=
  match st.stock.prev with
  | none => none
  | some c' =>
      if c' = c ∧ st.canPlace c b then
        match st.board.attach b c with
        | none => none
        | some bd =>
            some { st with board := bd, stock := st.stock.removeAt (st.stock.cursor - 1) }
      else none

def applyDeckStack (st : State) (c : Card) : Option State :=
  match st.stock.prev with
  | none => none
  | some c' =>
      if c' = c ∧ c.rank.toIdx = st.heights c.suit then
        some { st with
          stock := st.stock.removeAt (st.stock.cursor - 1),
          heights := fun s => if s = c.suit then st.heights s + 1 else st.heights s }
      else none

def applyPileStack (st : State) (c : Card) : Option State :=
  match st.board.topOf (Sum.inr c), st.board.bottomOf c with
  | none, some b =>
      if c.rank.toIdx = st.heights c.suit then
        some { st with
          board := st.board.detach b,
          heights := fun s => if s = c.suit then st.heights s + 1 else st.heights s }
      else none
  | _, _ => none

def applyStackPile (st : State) (c : Card) (b : Base) : Option State :=
  if c.rank.toIdx + 1 = st.heights c.suit ∧ st.canPlace c b then
    match st.board.attach b c with
    | none => none
    | some bd =>
        some { st with
          board := bd,
          heights := fun s => if s = c.suit then st.heights s - 1 else st.heights s }
  else none

/-- Can the run rooted at `c` land on `b`?  (`b` free, `c` fits, and
`b` is not part of the run being moved — the self-landing guard.) -/
def canMoveRun (st : State) (c : Card) (b : Base) : Bool :=
  st.canPlace c b &&
  match b with
  | Sum.inl _ => true
  | Sum.inr d => !(st.board.aboveOf c).contains d

def applyPilePile (st : State) (c : Card) (b : Base) : Option State :=
  match st.board.bottomOf c with
  | none => none
  | some b₀ =>
      if b₀ ≠ b ∧ st.canMoveRun c b then
        match (st.board.detach b₀).attach b c with
        | some bd => some { st with board := bd }
        | none => none
      else none

/-- The one semantic function: apply a move, or `none` if illegal.
`legal` and everything downstream derives from this. -/
def apply : Move → State → Option State
  | .draw, st => st.applyDraw
  | .reveal c, st => st.applyReveal c
  | .deckPile c b, st => st.applyDeckPile c b
  | .deckStack c, st => st.applyDeckStack c
  | .pileStack c, st => st.applyPileStack c
  | .stackPile c b, st => st.applyStackPile c b
  | .pilePile c b, st => st.applyPilePile c b

/-- Legality, derived from `apply` (single source of truth). -/
def legal (st : State) (m : Move) : Bool := (st.apply m).isSome

/-- Running a play. -/
def run (st : State) : List Move → Option State
  | [] => some st
  | m :: ms => match st.apply m with
    | some st' => st'.run ms
    | none => none

/-- All four foundations complete. -/
def isWin (st : State) : Bool :=
  Suit.all.all fun s => decide (st.heights s = 13)

/-- Solvability: a winning play exists (witness-as-data). -/
def solvableFrom (st : State) : Prop :=
  ∃ play : List Move, ∃ st', st.run play = some st' ∧ st'.isWin = true

/-- Solvability using only engine moves (the no-pile-to-pile
restriction). -/
def solvableEngine (st : State) : Prop :=
  ∃ play : List Move, (∀ m ∈ play, m.isEngine = true) ∧
    ∃ st', st.run play = some st' ∧ st'.isWin = true

/-- The macro-style Draw-commitment: rotate until `c` is the waste top,
then place it at `b` (the engine's `DeckPile` before the sweep
optimization; `drawTo` handles the worry-back wrap). -/
def applyDrawTo (st : State) (c : Card) (b : Base) : Option State :=
  match st.stock.posOf c with
  | none => none
  | some i =>
    match st.board.attach b c with
    | none => none
    | some bd =>
      some { st with board := bd, stock := (st.stock.drawTo i).removeAt i }

end State

/-! ## The farmable statements -/

/-- TODO(proof): legality characterization of `pileStack` — the engine
bridge (`gen_moves` PileStack: visible, top of pile, rank = height). -/
theorem legal_pileStack_iff {st : State} {c : Card} :
    st.legal (Move.pileStack c) = true ↔
      (st.board.bottomOf c ≠ none ∧ st.board.topOf (Sum.inr c) = none ∧
       c.rank.toIdx = st.heights c.suit) := sorry

/-- **T (twin swap), conjugation step**: applying a flipped move to
the flipped state is applying the move to the state, flipped.
TODO: seven move cases. -/
theorem apply_flipAll (m : Move) (st : State) :
    st.flipAll.apply m.flipMove = (st.apply m).map State.flipAll := sorry

/-- **T (twin swap)**: solvability is invariant under the relabeling.
TODO: induction on the play via `apply_flipAll`. -/
theorem solvable_flipAll {st : State} (h : st.solvableFrom) :
    st.flipAll.solvableFrom := sorry

/-- **The no-pile-to-pile restriction (ledger B-legs)**: on
well-formed states, the full physical game and the engine's restricted
move set have the same solvability.  TODO: the compression/reshape
arguments of no_pile_to_pile.md — now a statement about a move subset
of ONE model, not a correspondence between two formalizations. -/
theorem solvable_engine_iff {st : State} (hwf : st.WF) :
    st.solvableFrom ↔ st.solvableEngine := sorry

/-- TODO(proof): `WF` is preserved by every legal move — the
maintenance lemma, per move case. -/
theorem apply_wf {st : State} (hwf : st.WF) (m : Move) (st' : State)
    (h : st.apply m = some st') : st'.WF := sorry

/-- **C13 pilot (model level)**: adjacent Draw-commitments commute
(distinct bases).  Cycle content: `Cycle.removeIdx_comm`; the board
part: `attach` on distinct bases.  NOTE: non-adjacent pairs land on
*different cursors* — the engine's sweep/canonicalization is what
recovers commutation there (the C-IND landscape).  TODO. -/
theorem drawTo_comm_adjacent {st : State} {c c' : Card} {b b' : Base}
    (hbb : b ≠ b') {i : Nat}
    (hic : st.stock.posOf c = some i)
    (hic' : st.stock.posOf c' = some (i + 1))
    {st₂ st₄ : State}
    (h₂ : (st.applyDrawTo c b >>= fun s => s.applyDrawTo c' b') = some st₂)
    (h₄ : (st.applyDrawTo c' b' >>= fun s => s.applyDrawTo c b) = some st₄) :
    st₂ = st₄ := sorry
