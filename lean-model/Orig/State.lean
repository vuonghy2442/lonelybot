import Orig.Basic

/-!
# The original game — state

The state carries the piles' cards *directly*: the dealt face-down
cards live in the pile, not behind deal bookkeeping.  The deal enters
only through `State.initial`.  The conservation invariant `State.WF`
counts every card exactly once.
-/

/-! ## Tableau positions -/

/-- The seven tableau positions. -/
inductive Anchor : Type where
  | p0 | p1 | p2 | p3 | p4 | p5 | p6
  deriving DecidableEq, Repr

/-- All anchors. -/
def Anchor.all : List Anchor := [.p0, .p1, .p2, .p3, .p4, .p5, .p6]

theorem Anchor.mem_all (a : Anchor) : a ∈ Anchor.all := by
  cases a <;> simp [Anchor.all]

/-- The pile index (position in the deal). -/
def Anchor.toIdx : Anchor → Nat
  | .p0 => 0 | .p1 => 1 | .p2 => 2 | .p3 => 3 | .p4 => 4 | .p5 => 5 | .p6 => 6

/-- What a card may be placed on: an empty tableau position, or a
pile-top card. -/
abbrev Base := Sum Anchor Card

/-- The first item of `l` satisfying `p`. -/
def firstWhere {α : Type} (p : α → Bool) : List α → Option α
  | [] => none
  | x :: t =>
      match p x with
      | true => some x
      | false => firstWhere p t

theorem firstWhere_sound {α : Type} (p : α → Bool) :
    ∀ {l : List α} {x : α}, firstWhere p l = some x → p x = true
  | [], _, h => by simp [firstWhere] at h
  | y :: t, _, h => by
      rw [firstWhere] at h
      split at h
      · rename_i hy
        injection h with hxy
        subst hxy
        exact hy
      · exact firstWhere_sound p h

/-! ## List helpers (self-contained) -/

/-- The last element of a list. -/
def lastOf : List Card → Option Card
  | [] => none
  | [c] => some c
  | _ :: c :: t => lastOf (c :: t)

/-- A list without its last element. -/
def chop : List Card → List Card
  | [] => []
  | [_] => []
  | x :: t => x :: chop t

/-- The part of a face-up run strictly below `c`. -/
def below (c : Card) : List Card → List Card
  | [] => []
  | x :: t => if x = c then [] else x :: below c t

/-- The face-up run from `c` upward, inclusive. -/
def fromCard (c : Card) : List Card → List Card
  | [] => []
  | x :: t => if x = c then x :: t else fromCard c t

/-! ## Piles -/

/-- One tableau pile.  `hidden` keeps the next-to-flip card at its
head; `faceUp` is bottom-first, so the pile top is the *last* element
of `faceUp`. -/
@[ext]
structure Pile : Type where
  hidden : List Card
  faceUp : List Card
  deriving DecidableEq

namespace Pile

/-- The pile's top card. -/
def top (p : Pile) : Option Card := lastOf p.faceUp

/-- A pile with no cards at all. -/
def isEmpty (p : Pile) : Bool :=
  match p.hidden, p.faceUp with
  | [], [] => true
  | _, _ => false

/-- Flip the top hidden card, if any, onto the face-up run (the
automatic reveal of the physical game). -/
def revealTop (p : Pile) : Pile :=
  match p.hidden with
  | h :: t => { p with hidden := t, faceUp := p.faceUp ++ [h] }
  | [] => p

/-- The pile after a face-up run is removed and only `pre` remains
below it — flipping the next hidden card exactly when the face-up
run empties. -/
def afterRunRemoved (p : Pile) (pre : List Card) : Pile :=
  match pre with
  | [] => Pile.revealTop { p with faceUp := [] }
  | _ => { p with faceUp := pre }

/-- The pile a dealt hand becomes: every card but the last lies
hidden, the last is dealt face up. -/
def ofDealt (l : List Card) : Pile :=
  { hidden := (l.take (l.length - 1)).reverse
    faceUp := match lastOf l with
      | some c => [c]
      | none => [] }

end Pile

/-- A face-up run is legal: each card sits exactly one rank below and
opposite in color to the one under it (read bottom-first). -/
def runOK : List Card → Bool
  | [] => true
  | [_] => true
  | x :: y :: t => canSitOn y x && runOK (y :: t)

/-! ## The state -/

/-- A game position.  Everything the physical game needs is here:
the foundations as built-up lists, the piles with their own hidden
cards, the stock in draw order, the waste with its top at the head. -/
@[ext]
structure State : Type where
  /-- Cards built onto each foundation, in build order (ace first,
  top last). -/
  found : Suit → List Card
  /-- The seven tableau piles. -/
  piles : Anchor → Pile
  /-- The stock, in draw order (the head is dealt next). -/
  stock : List Card
  /-- The waste, top at the head. -/
  waste : List Card
  /-- Cards dealt per draw: 1 or 3. -/
  drawStep : Nat

namespace State

/-- The height of `s`'s foundation. -/
def foundHeight (st : State) (s : Suit) : Nat := (st.found s).length

/-- The top card of pile `a`. -/
def topOf (st : State) (a : Anchor) : Option Card := (st.piles a).top

/-- The pile whose top card is `z`, if any. -/
def pileOfTop (st : State) (z : Card) : Option Anchor :=
  firstWhere (fun a => decide (st.topOf a = some z)) Anchor.all

/-- The pile holding `c` face up, if any. -/
def pileHolding (st : State) (c : Card) : Option Anchor :=
  firstWhere (fun a => decide (c ∈ (st.piles a).faceUp)) Anchor.all

/-- May `c` be placed on `b` right now?  A king onto an empty
position; otherwise onto a pile top it fits under.  The fit rules
make illegal same-pile targets unreachable, so no side conditions
are needed (a later chapter proves this at `WF` states). -/
def canPlace (st : State) (c : Card) (b : Base) : Bool :=
  match b with
  | .inl a => (st.piles a).isEmpty && decide (c.rank = .king)
  | .inr z =>
      match st.pileOfTop z with
      | some _ => canSitOn c z
      | none => false

/-- Is `c` the current waste top? -/
def wasteIs (st : State) (c : Card) : Bool :=
  match st.waste with
  | [] => false
  | c' :: _ => decide (c' = c)

/-- The waste top test at an empty waste. -/
theorem wasteIs_nil {st : State} {c : Card} (h : st.waste = []) :
    st.wasteIs c = false := by
  rw [show st.wasteIs c =
      (match st.waste with
        | [] => false
        | c' :: _ => decide (c' = c)) from rfl, h]

/-- The waste top test at a nonempty waste: it compares the heads. -/
theorem wasteIs_cons {st : State} {x : Card} {t : List Card} (h : st.waste = x :: t)
    (c : Card) : st.wasteIs c = decide (x = c) := by
  rw [show st.wasteIs c =
      (match st.waste with
        | [] => false
        | c' :: _ => decide (c' = c)) from rfl, h]

/-- Is `c` the next card for its suit's foundation? -/
def nextUp (st : State) (c : Card) : Bool :=
  decide (c.rank.toIdx = st.foundHeight c.suit)

/-- The current top card of `s`'s foundation. -/
def foundTop (st : State) (s : Suit) : Option Card := lastOf (st.found s)

/-- Updated pile contents. -/
def setPile (st : State) (a : Anchor) (p : Pile) : State :=
  { st with piles := fun a' => if a' = a then p else st.piles a' }

/-- Updated foundation contents. -/
def setFound (st : State) (s : Suit) (l : List Card) : State :=
  { st with found := fun s' => if s' = s then l else st.found s' }

/-- Every card-holding zone, for the conservation invariant. -/
def zones (st : State) : List (List Card) :=
  Suit.all.map st.found ++
  Anchor.all.map (fun a => (st.piles a).hidden ++ (st.piles a).faceUp) ++
  [st.stock, st.waste]

/-- How many times `c` appears in the position. -/
def cardCount (st : State) (c : Card) : Nat :=
  ((st.zones.flatMap id).filter fun x => decide (x = c)).length

/-- The goal: all 52 cards onto the foundations. -/
def isWin (st : State) : Bool :=
  Suit.all.all fun s => decide ((st.found s).length = 13)

/-- The conservation invariant: foundations hold correct prefixes
of their build order, face-up runs are legal, every card appears
exactly once, and the draw step is 1 or 3. -/
def WF (st : State) : Prop :=
  (∀ s, ∃ n, st.found s = s.upCards.take n) ∧
  (∀ a, runOK (st.piles a).faceUp = true) ∧
  (∀ c ∈ Card.universe, st.cardCount c = 1) ∧
  (0 < st.drawStep)

/-! ## The deal -/

/-- A deal: each pile's cards bottom-first (the last is dealt face
up), plus the stock in draw order. -/
structure Deal : Type where
  piles : Anchor → List Card
  stock : List Card

/-- A standard deal: pile `a` holds `a.toIdx + 1` cards, 24 lie in
the stock, and all 52 cards appear exactly once. -/
def Deal.WF (d : Deal) : Prop :=
  (∀ a, (d.piles a).length = a.toIdx + 1) ∧
  d.stock.length = 24 ∧
  (∀ c ∈ Card.universe,
    (((Anchor.all.map d.piles).flatMap id ++ d.stock).filter
      fun x => decide (x = c)).length = 1)

/-- The starting position of a dealt game. -/
def initial (d : State.Deal) (drawStep : Nat) : State :=
  { found := fun _ => []
    piles := fun a => Pile.ofDealt (d.piles a)
    stock := d.stock
    waste := []
    drawStep := drawStep }

end State

/-! ## Record readers

The update lemmas for `State.setPile`, `State.canPlace` and
`Pile.afterRunRemoved`, landed beside the defs so the exchange
chapters cite them once instead of carrying private copies (the
copies in `Orig/TwinExchange.lean` and `Orig.TwinExchangeBoth` are
dedup-marked against this section). -/

/-- A pile update leaves every other pile's top alone. -/
theorem setPile_topOf_ne {st : State} {k b : Anchor} {Q : Pile} (h : k ≠ b) :
    (st.setPile b Q).topOf k = st.topOf k := by
  show (if k = b then Q else st.piles k).top = st.topOf k
  rw [ite_eq_right h]
  rfl

/-- A pile update leaves every other pile alone. -/
theorem setPile_piles_ne {st : State} {k b : Anchor} {Q : Pile} (h : k ≠ b) :
    (st.setPile b Q).piles k = st.piles k := by
  show (if k = b then Q else st.piles k) = st.piles k
  rw [ite_eq_right h]

/-- A pile update writes exactly the given pile. -/
theorem setPile_piles_self {st : State} {a : Anchor} {p : Pile} :
    (st.setPile a p).piles a = p :=
  show (if a = a then p else st.piles a) = p from ite_eq_left rfl

/-- A pile update writes no foundation. -/
theorem setPile_found (st : State) (a : Anchor) (p : Pile) :
    (st.setPile a p).found = st.found := rfl

/-- The empty-seat branch of the placement guard. -/
theorem canPlace_inl_unfold (st : State) (c : Card) (a : Anchor) :
    st.canPlace c (Sum.inl a) =
      ((st.piles a).isEmpty && decide (c.rank = Rank.king)) := rfl

/-- The top-directed branch of the placement guard, unfolded. -/
theorem canPlace_inr_eq (st : State) (c : Card) (z : Card) :
    st.canPlace c (Sum.inr z) =
      (match st.pileOfTop z with
       | some _ => canSitOn c z
       | none => false) := rfl

/-- The top-directed branch, already located: the guard is the fit. -/
theorem canPlace_inr_located {st : State} {c z : Card} {k : Anchor}
    (h : st.pileOfTop z = some k) :
    st.canPlace c (Sum.inr z) = canSitOn c z := by
  rw [show st.canPlace c (Sum.inr z) = canSitOn c z from by
    simp only [State.canPlace, h]]

/-- `afterRunRemoved` at a nonempty prefix keeps the hidden deck and
relocates the face-up run to the prefix alone. -/
theorem afterRunRemoved_ne {p : Pile} {pre : List Card} (h : pre ≠ []) :
    Pile.afterRunRemoved p pre = { p with faceUp := pre } := by
  cases pre with
  | nil => exact absurd rfl h
  | cons w ws => rfl
