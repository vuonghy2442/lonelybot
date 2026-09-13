import Klondike.Board
import Klondike.Cycle
import Klondike.Kit

/-!
# Game state: the free parameters + derived views

The state is what history chose and the rules don't determine (see
the README's table): the visible matching, the foundation heights,
the hidden boundary depths, the stock cursor — everything else is a
derived view (`hidden`, `topHidden`, `up`, …).
-/

/-- A deal: the fixed arrangement the game is played from.

`piles a` is pile `a`'s cards in deal order, bottom first (the head is
the bottom card); `stock` is the stock slice in draw order. -/
structure Deal where
  /-- Each pile's dealt cards, bottom first. -/
  piles : Anchor → List Card
  /-- The stock slice, in draw order. -/
  stock : List Card

/-- Deal well-formedness: standard Klondike shape (pile `a` has
`a.toIdx + 1` cards), 24 stock cards, all 52 distinct.
TODO(proof): constructors for the standard deal. -/
def Deal.WF (d : Deal) : Prop :=
  (∀ a, (d.piles a).length = a.toIdx + 1) ∧
  d.stock.length = 24 ∧
  noDupCards ((Anchor.all.flatMap d.piles) ++ d.stock)

/-- The game state: the free parameters only. -/
structure State where
  /-- The fixed deal. -/
  deal : Deal
  /-- The visible tableau matching (the only free sit-on structure). -/
  board : Board
  /-- Foundation prefix lengths per suit. -/
  heights : Suit → Nat
  /-- Hidden cards remaining per pile (the reveal boundary). -/
  depths : Anchor → Nat
  /-- The stock as a pointed cycle (remaining cards + draw cursor). -/
  stock : Cycle Card
  /-- The game's draw step (1 or 3). -/
  drawStep : Nat

namespace State

/-- The hidden cards of pile `a` (the deal slice, truncated by
reveals). -/
def hidden (st : State) (a : Anchor) : List Card := (st.deal.piles a).take (st.depths a)

/-- The topmost hidden card of pile `a` (the reveal boundary). -/
def topHidden (st : State) (a : Anchor) : Option Card := (st.hidden a).getLast?

/-- The pile whose hidden boundary card is `r`, if any. -/
def pileOfTopHidden (st : State) (r : Card) : Option Anchor :=
  findFirst (fun a => decide (st.topHidden a = some r)) Anchor.all

/-- The base under the top hidden card of `a`: the next hidden card
down, or the anchor when the pile is down to its last hidden card. -/
def hiddenBase (st : State) (a : Anchor) : Base :=
  match (st.hidden a).reverse.drop 1 |>.head? with
  | some d => Sum.inr d
  | none => Sum.inl a

/-- Is `c` on the foundation? -/
def onFound (st : State) (c : Card) : Bool := decide (c.rank.toIdx < st.heights c.suit)

/-- Is `c` visible on the tableau (in the matching's image)? -/
def isVis (st : State) (c : Card) : Bool := (st.board.bottomOf c).isSome

/-- The physical face-up predicate, as a derived view:
visible ∨ on foundation ∨ passed (waste).  Restricted to tableau
cards, this is the engine's `vis` mask (the bridge lemma). -/
def up (st : State) (c : Card) : Bool :=
  st.isVis c || st.onFound c || st.stock.passed c

/-- Can `c` be placed on the free base `b`?  (Kings on anchors,
`canSitOn` on a visible card.) -/
def canPlace (st : State) (c : Card) (b : Base) : Bool :=
  decide (st.board.topOf b = none) &&
  match b with
  | Sum.inl _ => decide (c.rank = Rank.king)
  | Sum.inr d => st.isVis d && canSitOn c d

/-- Depths within the deal slices (the reveal boundary never runs past
the deal). -/
def depths_le (st : State) : Prop :=
  ∀ a, st.depths a ≤ (st.deal.piles a).length

/-- The visible matching's edge legality: the `topOf`/`bottomOf` round
trip, and every edge sits on the card it was dealt directly onto (the
initial deal stacks by fiat; `reveal` keeps the cover sitting on its
freshly-revealed card) or on a fitting visible card; kings or
fully-revealed bottoms on anchors. -/
def board_edges (st : State) : Prop :=
  ∀ b c, st.board.topOf b = some c →
    st.board.bottomOf c = some b ∧
    (match b with
     | Sum.inl a => c.rank = Rank.king ∨ (st.deal.piles a).head? = some c
     | Sum.inr d =>
       (∃ a t rest, st.deal.piles a = t ++ d :: c :: rest) ∨
       ((st.board.bottomOf d).isSome = true ∧ canSitOn c d = true))

/-- Visible cards are not in the stock cycle. -/
def vis_off_cycle (st : State) : Prop :=
  ∀ c, st.isVis c = true → st.stock.posOf c = none

/-- Foundation cards are not in the stock cycle. -/
def found_off_cycle (st : State) : Prop :=
  ∀ c, st.onFound c = true → st.stock.posOf c = none

/-- Foundation heights within range. -/
def heights_le (st : State) : Prop := ∀ s, st.heights s ≤ 13

/-- The cursor within the cycle (the pass end included). -/
def cursor_le (st : State) : Prop := st.stock.cursor ≤ st.stock.cards.length

/-- The draw step is positive (the engine's `NonZeroU8`): at 0 the
deal never advances and the accessible set is undefined. -/
def step_pos (st : State) : Prop := 0 < st.drawStep

/-- Two states differing (at most) in the stock cursor — the pace
family's source relation (the pace dominances, the window lemmas, and
the replay API's `diffCursor`-preservation lemmas). -/
def diffCursor (st st' : State) : Prop :=
  st.deal = st'.deal ∧ st.board = st'.board ∧ st.heights = st'.heights ∧
    st.depths = st'.depths ∧ st.stock.cards = st'.stock.cards ∧
    st.drawStep = st'.drawStep

/-- The stock cycle: duplicate-free, and a sub-list of the deal's
stock (the state's cycle only ever loses cards from the deal's). -/
def stock_wf (st : State) : Prop :=
  noDupCards st.stock.cards ∧ ∀ c ∈ st.stock.cards, c ∈ st.deal.stock

/-- State well-formedness — the invariant the moves preserve (`apply_wf`)
and the deal's exhibit satisfies (`initial_wf`): slice-bounded depths,
legal board edges, off-cycle visible/foundation cards, bounded
heights and cursor, a positive draw step, and a clean stock. -/
def WF (st : State) : Prop :=
  st.deal.WF ∧ st.depths_le ∧ st.board_edges ∧ st.vis_off_cycle ∧
  st.found_off_cycle ∧ st.heights_le ∧ st.cursor_le ∧ st.step_pos ∧
  st.stock_wf

/-! ### WF accessors — the conjunct positions, written once -/

theorem WF.deal_wf {st : State} (h : st.WF) : st.deal.WF := h.1

theorem WF.depths_le {st : State} (h : st.WF) : st.depths_le := h.2.1

theorem WF.board_edges {st : State} (h : st.WF) : st.board_edges := h.2.2.1

theorem WF.vis_off_cycle {st : State} (h : st.WF) : st.vis_off_cycle := h.2.2.2.1

theorem WF.found_off_cycle {st : State} (h : st.WF) : st.found_off_cycle := h.2.2.2.2.1

theorem WF.heights_le {st : State} (h : st.WF) : st.heights_le := h.2.2.2.2.2.1

theorem WF.cursor_le {st : State} (h : st.WF) : st.cursor_le := h.2.2.2.2.2.2.1

theorem WF.step_pos {st : State} (h : st.WF) : st.step_pos := h.2.2.2.2.2.2.2.1

theorem WF.stock_wf {st : State} (h : st.WF) : st.stock_wf := h.2.2.2.2.2.2.2.2

/-- Conjugate the whole state by the twin-swap relabeling (T's action
on every component). -/
def flipAll (st : State) : State :=
  { st with
    deal := { piles := fun a => (st.deal.piles a).map Card.flipSuit,
              stock := st.deal.stock.map Card.flipSuit },
    board := st.board.mapBy,
    heights := fun s => st.heights s.flipPair,
    stock := { cards := st.stock.cards.map Card.flipSuit, cursor := st.stock.cursor } }

end State
