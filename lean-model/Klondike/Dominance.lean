import Klondike.Theorems

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

/-- Full commutation *implies* dominance: a move that can be bubbled
past any other move (reaching the same state) can be forced first in
any winning play.  The converse fails — a safe stack is dominant via
worry-back yet commutes with nothing (it changes `heights`, which
changes every other stack's legality).  TODO(proof): play induction. -/
theorem dominant_of_commutesWithAll {st : State} {m : Move}
    (h : ∀ m' : Move, ∀ st₁ st₂ : State,
      st.apply m' = some st₁ → st₁.apply m = some st₂ →
      ∃ st₃, st.apply m = some st₃ ∧ st₃.apply m' = some st₂) :
    dominantAt st m := sorry

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

/-- §5.1: a legal pileStack of a safe card is dominant — the
worry-back argument: a safe card can always be brought back later, and
stacking strictly grows the foundation (progress).  TODO(proof): the
return-base availability is the crux (cf.
`pileStack_stackPile_roundtrip`'s anchor case). -/
theorem safe_pileStack_dominant {st : State} {c : Card} (hwf : st.WF)
    (hsafe : safeToStack st c = true) (hlegal : st.legal (Move.pileStack c) = true) :
    dominantAt st (Move.pileStack c) := sorry

/-! ## §5.2 Three-or-more redundant stackables -/

/-- A card is locked when it sits on its pile's hidden boundary
(moving it would reveal). -/
def State.isLocked (st : State) (c : Card) : Bool :=
  match st.board.bottomOf c with
  | some (Sum.inr r) => st.pileOfTopHidden r ≠ none
  | _ => false

/-- `redundant_stack = pile_stack & !locked` (§5.2): a stackable card
whose stacking reveals nothing. -/
def State.isRedundantStack (st : State) (c : Card) : Bool :=
  st.legal (Move.pileStack c) && !st.isLocked c

/-- The redundant stackables of the state. -/
def State.redundantStacks (st : State) : List Card :=
  Card.universe.filter fun c => st.isRedundantStack c

/-- §5.2: with ≥3 redundant stackables, stacking the lowest-rank one is
dominant — a canonical representative; the others remain available
later (stack moves into the foundation commute, and what is safe is
recoverable per §5.1).  TODO. -/
theorem least_redundantStack_dominant {st : State} {c : Card} (hwf : st.WF)
    (hmem : c ∈ st.redundantStacks)
    (hlen : 3 ≤ st.redundantStacks.length)
    (hlow : ∀ c' ∈ st.redundantStacks, c.rank.toIdx ≤ c'.rank.toIdx) :
    dominantAt st (Move.pileStack c) := sorry

/-! ## §5.3 Deck dominance -/

/-- The safe-stack draw commitment: rotate to `c`, stack it on the
foundation. -/
def State.applyDrawStackTo (st : State) (c : Card) : Option State :=
  match st.stock.posOf c with
  | none => none
  | some i =>
    if c.rank.toIdx = st.heights c.suit then
      some { st with
        stock := (st.stock.drawTo i).removeAt i,
        heights := fun s => if s = c.suit then st.heights s + 1 else st.heights s }
    else none

/-- §5.3, draw-1 form: with one card per draw, every drawable card is
equally reachable, so front-loading the safe stack of a drawable card
loses nothing.  The general (draw-3) form needs the deck `is_pure`
condition (offset alignment).  TODO: the reshaping argument. -/
theorem deck_dominance_draw1 {st : State} {c : Card} (hwf : st.WF)
    (hstep : st.drawStep = 1) (hsafe : safeToStack st c = true)
    (hdraw : st.stock.posOf c ≠ none) (hleg : st.applyDrawStackTo c ≠ none) :
    st.solvableFrom → ∃ st₁, st.applyDrawStackTo c = some st₁ ∧ st₁.solvableFrom := sorry

/-! ## §5.4 Unstack only what is not safe to restack -/

/-- §5.4, first half: never worry back a dominantly-stackable card —
omitting `stackPile` of a safe card loses nothing.  TODO. -/
theorem stackPile_safe_prunable {st : State} {c : Card} {b : Base} (hwf : st.WF)
    (hsafe : safeToStack st c = true) : prunableAt st (Move.stackPile c b) := sorry

/-- §5.4, second half (`deck_pile excludes dom_sm & sm`): never draw a
card to the tableau when it could safely go to the foundation.  TODO. -/
theorem deckPile_safe_prunable {st : State} {c : Card} {b : Base} (hwf : st.WF)
    (hsafe : safeToStack st c = true) (hstack : st.legal (Move.deckStack c) = true) :
    prunableAt st (Move.deckPile c b) := sorry

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

/-- The dominance cascade (§5 + pruning_dominance_interaction): a
filter that, at every reachable solvable state, leaves either the win
or a dominant `P`-move, preserves solvability.

WARNING (their §9): the individual rules are argued separately, and
individually-sound filters can be jointly unsound — this composition
is the repo's main open soundness question.  The hypothesis here is
the strong all-reachable-states form, and the induction needs the
progress measure (§9.4: the dominances force progress — foundation
growth, reveals, draws — so states do not repeat: the DAG argument).
TODO. -/
theorem cascade_sound {P : Move → Bool} (st : State)
    (h : ∀ st₁ play, st.run play = some st₁ → st₁.solvableFrom →
      st₁.isWin = true ∨ ∃ m, P m = true ∧ st₁.legal m = true ∧ dominantAt st₁ m) :
    st.solvableFrom → st.solvableWith P := sorry

/-! §5.6 (the least-stack cascade) is deferred — it is the most
intricate dominance and carries its own TODO in method.md.
§5.7 (kings only on actually-free piles) is already definitional in
`State.canPlace`. -/
