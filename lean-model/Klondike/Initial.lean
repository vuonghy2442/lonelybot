import Klondike.Bridge

/-!
# The initial state — exhibiting WF states

Every theorem so far is quantified over `st.WF` states that were never
exhibited: without a constructor, the entire development risks
vacuity.  This module builds the standard game — deal splitting, the
initial board (each pile's top dealt card face-up on the boundary),
empty foundations, fresh stock — and states `initial_wf`.

It also carries runnable sanity checks (`by decide`), the seed of the
cross-validation oracle: the model executes.
-/

/-- Where pile `a`'s slice starts in the deal list (0, 1, 3, 6, 10,
15, 21 — the triangular numbers; the 28 dealt cards precede the
24-card stock). -/
def Anchor.start : Anchor → Nat
  | .p0 => 0 | .p1 => 1 | .p2 => 3 | .p3 => 6 | .p4 => 10 | .p5 => 15 | .p6 => 21

/-- Deal from a card list: pile `a` takes the next `a.toIdx + 1`
cards, the remainder is the stock.  Any list works; well-formedness
needs 52 distinct cards. -/
def Deal.ofList (l : List Card) : Deal where
  piles := fun a => (l.drop a.start).take (a.toIdx + 1)
  stock := l.drop 28

/-- The standard deal: the universe order, split triangularly. -/
def Deal.standard : Deal := Deal.ofList Card.universe

/-- The initial board: each pile's top dealt card, face-up, sitting
on the boundary (the card beneath it, or the anchor for the
single-card pile). -/
def initialBoard (d : Deal) : Board :=
  Anchor.all.foldl (fun bd a =>
    let base : Base :=
      match a.toIdx with
      | 0 => Sum.inl a
      | k + 1 => match (d.piles a)[k]? with
        | some under => Sum.inr under
        | none => Sum.inl a
    match (d.piles a).getLast? with
    | some top => (bd.attach base top).getD bd
    | none => bd) Board.empty

/-- The initial state of a dealt game: hidden boundary at `a.toIdx`
per pile, foundations empty, stock fresh at the start of its first
pass. -/
def State.initial (d : Deal) (drawStep : Nat) : State where
  deal := d
  board := initialBoard d
  heights := fun _ => 0
  depths := fun a => a.toIdx
  stock := ⟨d.stock, 0⟩
  drawStep := drawStep

/-! ## Statements -/

/-- TODO: the 52 cards are distinct (index-wise, over the factored
product). -/
theorem Card.universe_noDup : noDupCards Card.universe := sorry

/-- TODO: `ofList` on 52 distinct cards is well-formed (lengths by
the triangular split, distinctness preserved by `drop`/`take`). -/
theorem Deal.ofList_wf {l : List Card} (hlen : l.length = 52) (hnd : noDupCards l) :
    (Deal.ofList l).WF := sorry

/-- **The exhibit**: a well-formed deal's initial state is WF — the
theorems' hypotheses are non-vacuous, and `State.initial` is the
witness constructor.  TODO: the edge legality is `canSitOn`-free by
construction (top cards sit on the hidden boundary or the anchor,
the WF's exempt disjuncts). -/
theorem initial_wf {d : Deal} (hd : d.WF) (drawStep : Nat) :
    (State.initial d drawStep).WF := sorry

/-! ## Runnable sanity checks — the oracle seed -/

example : (Deal.standard.piles Anchor.p6).length = 7 := by decide

example : Deal.standard.stock.length = 24 := by decide

example : (State.initial Deal.standard 1).depths Anchor.p6 = 6 := by decide

/-- The standard game's single-card pile: its ace of hearts sits
directly on the anchor, and the derived `bottomOf` search finds it —
the matching machinery executes correctly on a concrete state. -/
example : (State.initial Deal.standard 1).board.bottomOf ⟨Suit.heart, Rank.ace⟩
    = some (Sum.inl Anchor.p0) := by decide
