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

/-- A card is locked when it sits on its pile's hidden boundary
(moving it would strand the boundary — see `safe_pileStack_dominant`'s
repair note in Dominance.lean: the model's `reveal` seats the boundary
while the card is still on it, so a locked card must be revealed
*through* before it moves).  RELOCATED 2026-09-13 from Dominance.lean —
the B4 crux (`solvable_of_pileStack`, Theorems.lean) and
`vis_base_of_notLocked` need it upstream of Dominance. -/
def isLocked (st : State) (c : Card) : Bool :=
  match st.board.bottomOf c with
  | some (Sum.inr r) => st.pileOfTopHidden r ≠ none
  | _ => false

/-- The per-suit climb frontier (the engine closure context's
`frontier[s]`, macro_game.rs): the first rank at or above the
foundation height whose card is not visible-and-unlocked — 13 when the
climb is open.  The goal-kill tests read `st.frontier s < X.rank.toIdx`
(K1's blockedness, K6's climb-blocked twin; see Klondike/Kills.lean). -/
def frontier (st : State) (s : Suit) : Nat :=
  match (Rank.all.filter fun r => st.heights s ≤ r.toIdx).find?
      (fun r => !(st.isVis ⟨s, r⟩) || st.isLocked ⟨s, r⟩) with
  | some r => r.toIdx
  | none => 13

/-- Depths within the deal slices (the reveal boundary never runs past
the deal). -/
def depths_le (st : State) : Prop :=
  ∀ a, st.depths a ≤ (st.deal.piles a).length

/-- The visible matching's edge legality: the `topOf`/`bottomOf` round
trip, and every edge sits on the card it was dealt directly onto — with
that base either still the pile's hidden boundary or itself placed
(the two shapes a dealt-adjacent base has in every reachable state:
`reveal` attaches the boundary before anything can sit on it, and an
attached card stays attached) — or on a fitting visible card; kings or
fully-revealed bottoms on anchors.  The base condition is the buried-base
clause: without it, WF admits edges onto foundation/limbo cards that no
play can produce (the Bridge lift witness). -/
def board_edges (st : State) : Prop :=
  ∀ b c, st.board.topOf b = some c →
    st.board.bottomOf c = some b ∧
    (match b with
     | Sum.inl a => c.rank = Rank.king ∨ (st.deal.piles a).head? = some c
     | Sum.inr d =>
       (∃ a t rest, st.deal.piles a = t ++ d :: c :: rest ∧
          ((∃ a', st.topHidden a' = some d) ∨ (st.board.bottomOf d).isSome = true)) ∨
       ((st.board.bottomOf d).isSome = true ∧ canSitOn c d = true))

/-- Visible cards are not in the stock cycle. -/
def vis_off_cycle (st : State) : Prop :=
  ∀ c, st.isVis c = true → st.stock.posOf c = none

/-- Foundation cards are not in the stock cycle. -/
def found_off_cycle (st : State) : Prop :=
  ∀ c, st.onFound c = true → st.stock.posOf c = none

/-- Foundation-passed cards are really gone: a card below its suit's
foundation height is neither visible on the tableau, nor in the stock
cycle, nor hidden in a pile — it can only sit on the foundation.  This
is the no-passing invariant (contrapositively, every visible, stocked,
or hidden card sits at or above its suit's height); the third
conjunct is required for `reveal`, which seats a boundary card and so
must know that no hidden card is foundation-passed. -/
def founds_gone (st : State) : Prop :=
  ∀ c, c.rank.toIdx < st.heights c.suit →
    st.isVis c = false ∧ st.stock.posOf c = none ∧ ∀ a, c ∉ st.hidden a

/-- Visible cards are not hidden: the board's image and the piles'
hidden slices are disjoint (a deal-adjacent seat on the boundary is
not a placement; `reveal` is what turns one on). -/
def vis_not_hidden (st : State) : Prop :=
  ∀ c, st.isVis c = true → ∀ a, c ∉ st.hidden a

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
legal board edges (deal-adjacency with a hidden-boundary-or-placed
base), off-cycle visible/foundation cards, gone foundation cards,
visible-not-hidden, bounded heights and cursor, a positive draw step,
and a clean stock. -/
def WF (st : State) : Prop :=
  st.deal.WF ∧ st.depths_le ∧ st.board_edges ∧ st.vis_off_cycle ∧
  st.found_off_cycle ∧ st.founds_gone ∧ st.vis_not_hidden ∧ st.heights_le ∧
  st.cursor_le ∧ st.step_pos ∧ st.stock_wf

/-! ### WF accessors — the conjunct positions, written once -/

theorem WF.deal_wf {st : State} (h : st.WF) : st.deal.WF := h.1

theorem WF.depths_le {st : State} (h : st.WF) : st.depths_le := h.2.1

theorem WF.board_edges {st : State} (h : st.WF) : st.board_edges := h.2.2.1

theorem WF.vis_off_cycle {st : State} (h : st.WF) : st.vis_off_cycle := h.2.2.2.1

theorem WF.found_off_cycle {st : State} (h : st.WF) : st.found_off_cycle := h.2.2.2.2.1

theorem WF.founds_gone {st : State} (h : st.WF) : st.founds_gone := h.2.2.2.2.2.1

theorem WF.vis_not_hidden {st : State} (h : st.WF) : st.vis_not_hidden := h.2.2.2.2.2.2.1

theorem WF.heights_le {st : State} (h : st.WF) : st.heights_le := h.2.2.2.2.2.2.2.1

theorem WF.cursor_le {st : State} (h : st.WF) : st.cursor_le := h.2.2.2.2.2.2.2.2.1

theorem WF.step_pos {st : State} (h : st.WF) : st.step_pos := h.2.2.2.2.2.2.2.2.2.1

theorem WF.stock_wf {st : State} (h : st.WF) : st.stock_wf := h.2.2.2.2.2.2.2.2.2.2

/-- WF by named conjuncts — construction without positional slots
(the anonymous-constructor spelling `⟨_, _, …⟩` is positional and
silent under reordering; the 11 slots here are, in order: `deal_wf`,
`depths_le`, `board_edges`, `vis_off_cycle`, `found_off_cycle`,
`founds_gone`, `vis_not_hidden`, `heights_le`, `cursor_le`,
`step_pos`, `stock_wf`). -/
theorem WF.intro {st : State} (deal_wf : st.deal.WF) (depths_le : st.depths_le)
    (board_edges : st.board_edges) (vis_off_cycle : st.vis_off_cycle)
    (found_off_cycle : st.found_off_cycle) (founds_gone : st.founds_gone)
    (vis_not_hidden : st.vis_not_hidden) (heights_le : st.heights_le)
    (cursor_le : st.cursor_le) (step_pos : st.step_pos)
    (stock_wf : st.stock_wf) : st.WF :=
  ⟨deal_wf, depths_le, board_edges, vis_off_cycle, found_off_cycle, founds_gone,
    vis_not_hidden, heights_le, cursor_le, step_pos, stock_wf⟩

/-! ### The heights combinators

The named form of the successors' height updates — the raw spelling
`fun s => if s = c.suit then st.heights s ± 1 else st.heights s`
appeared ~28× across the farm.  DEFEQ to that raw lambda, with the
simp/composition kit ready.  SITES DEFERRED (2026-09-13, the
next pass): the `apply` def bodies and the `apply_*_iff` statements
stay raw — their unfolded/literal shapes are load-bearing in
rw-pattern consumers this pass may not edit (Theorems' roundtrip
unfolds and the `applyDrawStackTo_eq_dealPlay` tail; Relabel's
`relabelBy_heights_bump` rewrites).  Theorems/Relabel/Macro/Bridge
sites are the next pass's inventory. -/

/-- Bump one suit's foundation height by one (the `pileStack` /
`deckStack` / `applyDrawStackTo` successors' heights). -/
def bumpHeight (st : State) (σ : Suit) : Suit → Nat :=
  fun s => if s = σ then st.heights s + 1 else st.heights s

/-- Drop one suit's foundation height by one (the `stackPile`
successor's heights). -/
def dropHeight (st : State) (σ : Suit) : Suit → Nat :=
  fun s => if s = σ then st.heights s - 1 else st.heights s

@[simp] theorem bumpHeight_self (st : State) (σ : Suit) :
    st.bumpHeight σ σ = st.heights σ + 1 := by
  show (if σ = σ then st.heights σ + 1 else st.heights σ) = _
  rw [if_pos rfl]

@[simp] theorem bumpHeight_ne {st : State} {σ : Suit} (s : Suit) (h : s ≠ σ) :
    st.bumpHeight σ s = st.heights s := by
  show (if s = σ then st.heights s + 1 else st.heights s) = _
  rw [if_neg h]

@[simp] theorem dropHeight_self (st : State) (σ : Suit) :
    st.dropHeight σ σ = st.heights σ - 1 := by
  show (if σ = σ then st.heights σ - 1 else st.heights σ) = _
  rw [if_pos rfl]

@[simp] theorem dropHeight_ne {st : State} {σ : Suit} (s : Suit) (h : s ≠ σ) :
    st.dropHeight σ s = st.heights s := by
  show (if s = σ then st.heights s - 1 else st.heights s) = _
  rw [if_neg h]

/-- The ± composition kit — the with-update forms of Commutation's
generic `heights_bump_bump`/`bump_drop`/`drop_drop` (which stay for the
`depths` steps).  Two bumps always commute; a bump past a drop at the
shared suit needs that suit's height positive (every `stackPile` guard
supplies it). -/
theorem bump_bump (st : State) (σ σ' : Suit) :
    { st with heights := st.bumpHeight σ' }.bumpHeight σ
      = { st with heights := st.bumpHeight σ }.bumpHeight σ' := by
  funext s
  by_cases h1 : s = σ
  · by_cases h2 : s = σ'
    · show (if s = σ then (if s = σ' then st.heights s + 1 else st.heights s) + 1
          else if s = σ' then st.heights s + 1 else st.heights s)
          = (if s = σ' then (if s = σ then st.heights s + 1 else st.heights s) + 1
          else if s = σ then st.heights s + 1 else st.heights s)
      rw [if_pos h1, if_pos h2, if_pos h2, if_pos h1]
    · show (if s = σ then (if s = σ' then st.heights s + 1 else st.heights s) + 1
          else if s = σ' then st.heights s + 1 else st.heights s)
          = (if s = σ' then (if s = σ then st.heights s + 1 else st.heights s) + 1
          else if s = σ then st.heights s + 1 else st.heights s)
      rw [if_pos h1, if_neg h2, if_neg h2, if_pos h1]
  · by_cases h2 : s = σ'
    · show (if s = σ then (if s = σ' then st.heights s + 1 else st.heights s) + 1
          else if s = σ' then st.heights s + 1 else st.heights s)
          = (if s = σ' then (if s = σ then st.heights s + 1 else st.heights s) + 1
          else if s = σ then st.heights s + 1 else st.heights s)
      rw [if_neg h1, if_pos h2, if_neg h1, if_pos h2]
    · show (if s = σ then (if s = σ' then st.heights s + 1 else st.heights s) + 1
          else if s = σ' then st.heights s + 1 else st.heights s)
          = (if s = σ' then (if s = σ then st.heights s + 1 else st.heights s) + 1
          else if s = σ then st.heights s + 1 else st.heights s)
      rw [if_neg h1, if_neg h2, if_neg h1, if_neg h2]

theorem bump_drop {st : State} (σ σ' : Suit) (hpos : σ = σ' → 0 < st.heights σ) :
    { st with heights := st.dropHeight σ' }.bumpHeight σ
      = { st with heights := st.bumpHeight σ }.dropHeight σ' := by
  funext s
  by_cases h1 : s = σ
  · by_cases h2 : s = σ'
    · show (if s = σ then (if s = σ' then st.heights s - 1 else st.heights s) + 1
          else if s = σ' then st.heights s - 1 else st.heights s)
          = (if s = σ' then (if s = σ then st.heights s + 1 else st.heights s) - 1
          else if s = σ then st.heights s + 1 else st.heights s)
      rw [if_pos h1, if_pos h2, if_pos h2, if_pos h1, h1]
      have hpos' := hpos (h1.symm.trans h2)
      omega
    · show (if s = σ then (if s = σ' then st.heights s - 1 else st.heights s) + 1
          else if s = σ' then st.heights s - 1 else st.heights s)
          = (if s = σ' then (if s = σ then st.heights s + 1 else st.heights s) - 1
          else if s = σ then st.heights s + 1 else st.heights s)
      rw [if_pos h1, if_neg h2, if_neg h2, if_pos h1]
  · by_cases h2 : s = σ'
    · show (if s = σ then (if s = σ' then st.heights s - 1 else st.heights s) + 1
          else if s = σ' then st.heights s - 1 else st.heights s)
          = (if s = σ' then (if s = σ then st.heights s + 1 else st.heights s) - 1
          else if s = σ then st.heights s + 1 else st.heights s)
      rw [if_neg h1, if_pos h2, if_neg h1, if_pos h2]
    · show (if s = σ then (if s = σ' then st.heights s - 1 else st.heights s) + 1
          else if s = σ' then st.heights s - 1 else st.heights s)
          = (if s = σ' then (if s = σ then st.heights s + 1 else st.heights s) - 1
          else if s = σ then st.heights s + 1 else st.heights s)
      rw [if_neg h1, if_neg h2, if_neg h1, if_neg h2]

theorem drop_drop (st : State) (σ σ' : Suit) :
    { st with heights := st.dropHeight σ' }.dropHeight σ
      = { st with heights := st.dropHeight σ }.dropHeight σ' := by
  funext s
  by_cases h1 : s = σ
  · by_cases h2 : s = σ'
    · show (if s = σ then (if s = σ' then st.heights s - 1 else st.heights s) - 1
          else if s = σ' then st.heights s - 1 else st.heights s)
          = (if s = σ' then (if s = σ then st.heights s - 1 else st.heights s) - 1
          else if s = σ then st.heights s - 1 else st.heights s)
      rw [if_pos h1, if_pos h2, if_pos h2, if_pos h1]
    · show (if s = σ then (if s = σ' then st.heights s - 1 else st.heights s) - 1
          else if s = σ' then st.heights s - 1 else st.heights s)
          = (if s = σ' then (if s = σ then st.heights s - 1 else st.heights s) - 1
          else if s = σ then st.heights s - 1 else st.heights s)
      rw [if_pos h1, if_neg h2, if_neg h2, if_pos h1]
  · by_cases h2 : s = σ'
    · show (if s = σ then (if s = σ' then st.heights s - 1 else st.heights s) - 1
          else if s = σ' then st.heights s - 1 else st.heights s)
          = (if s = σ' then (if s = σ then st.heights s - 1 else st.heights s) - 1
          else if s = σ then st.heights s - 1 else st.heights s)
      rw [if_neg h1, if_pos h2, if_neg h1, if_pos h2]
    · show (if s = σ then (if s = σ' then st.heights s - 1 else st.heights s) - 1
          else if s = σ' then st.heights s - 1 else st.heights s)
          = (if s = σ' then (if s = σ then st.heights s - 1 else st.heights s) - 1
          else if s = σ then st.heights s - 1 else st.heights s)
      rw [if_neg h1, if_neg h2, if_neg h1, if_neg h2]

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
