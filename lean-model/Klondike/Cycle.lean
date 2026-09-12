import Klondike.Basic

/-!
# The stock as a pointed cycle

With unlimited worrying (the engine's variant), stock/waste membership
is derived state: the remaining deck cards form one cyclic order with a
cursor.  Drawing rotates the cursor; playing a card splices it out.

The C13 commutation premise lives here: `removeIdx_comm` is its
list-level core (splicing out two cards in either order leaves the
same cyclic order).
-/

/-- The stock/waste.  `cards` holds the remaining cards in cyclic deal
order; `cursor` counts how many have been passed (the card at index
`cursor` is next to draw; index `cursor - 1` is the waste top). -/
structure Cycle (α : Type) where
  /-- The remaining cards, in cyclic order. -/
  cards : List α
  /-- The draw boundary: how many cards have been passed. -/
  cursor : Nat
  deriving DecidableEq

namespace Cycle

/-- Remove the element at index `i` (identity when out of range). -/
def removeIdx {α : Type} : List α → Nat → List α
  | [], _ => []
  | _ :: t, 0 => t
  | h :: t, n + 1 => h :: removeIdx t n

@[simp] theorem removeIdx_nil {α : Type} (i : Nat) : removeIdx ([] : List α) i = [] := rfl

@[simp] theorem removeIdx_zero {α : Type} (h : α) (t : List α) :
    removeIdx (h :: t) 0 = t := rfl

@[simp] theorem removeIdx_succ {α : Type} (h : α) (t : List α) (n : Nat) :
    removeIdx (h :: t) (n + 1) = h :: removeIdx t n := rfl

theorem removeIdx_length {α : Type} : ∀ (l : List α) (i : Nat), i < l.length →
    (removeIdx l i).length + 1 = l.length
  | [], _, h => by simp at h
  | _ :: _, 0, _ => rfl
  | _ :: t, i + 1, h => by
      simp only [List.length_cons] at h
      have ih := removeIdx_length t i (by omega)
      simp only [removeIdx, List.length_cons]
      omega

/-- The C13 premise, list level: splicing out two cards in either
order leaves the same list (the later index adjusts down by one). -/
theorem removeIdx_comm {α : Type} : ∀ (l : List α) (i j : Nat), i ≤ j → j + 1 < l.length →
    removeIdx (removeIdx l i) j = removeIdx (removeIdx l (j + 1)) i
  | [], _, _, _, h => by simp at h
  | _ :: _, 0, _, _, _ => rfl
  | x :: t, i + 1, j + 1, _, h => by
      have hij : i ≤ j := by omega
      have hjt : j + 1 < t.length := by
        simp only [List.length_cons] at h; omega
      have ih := removeIdx_comm t i j hij hjt
      simp only [removeIdx]
      exact congrArg (fun r => x :: r) ih

/-- Rotate the cursor past `k` cards (drawing; wrapping past the end
is the worry-back). -/
def rotate (k : Nat) (c : Cycle α) : Cycle α where
  cards := c.cards
  cursor := (c.cursor + k) % c.cards.length

@[simp] theorem rotate_cards (k : Nat) (c : Cycle α) : (c.rotate k).cards = c.cards := rfl

@[simp] theorem rotate_add (k₁ k₂ : Nat) (c : Cycle α) :
    (c.rotate k₁).rotate k₂ = c.rotate (k₁ + k₂) := by
  cases c
  simp [rotate, Nat.mod_add_mod, Nat.add_assoc]

/-- The next card to draw (at the cursor). -/
def next (c : Cycle α) : Option α := c.cards[c.cursor]?

/-- The waste top: the most recently passed card (playable by
DeckPile/DeckStack).  `none` when nothing has been passed. -/
def prev (c : Cycle α) : Option α :=
  if c.cursor = 0 then none else c.cards[c.cursor - 1]?

/-- Splice out the card at index `i`; the cursor follows when the
removed card had been passed. -/
def removeAt (i : Nat) (c : Cycle α) : Cycle α where
  cards := removeIdx c.cards i
  cursor := if i < c.cursor then c.cursor - 1 else c.cursor

/-- The index of the first element satisfying `p`. -/
def findFirstIdx {α : Type} (p : α → Bool) : List α → Option Nat
  | [] => none
  | a :: t => if p a then some 0 else (findFirstIdx p t).map Nat.succ

/-- The position of `c` among the cycle's remaining cards, if present. -/
def posOf (c : Card) (cy : Cycle Card) : Option Nat :=
  findFirstIdx (fun c' => decide (c' = c)) cy.cards

/-- Has `c` been passed (is it in the waste)? -/
def passed (c : Card) (cy : Cycle Card) : Bool :=
  match cy.posOf c with
  | some i => decide (i < cy.cursor)
  | none => false

/-- Rotate so that the card at index `i` is the waste top (the cursor
lands just past `i`; wrapping through the worry-back). -/
def drawTo (i : Nat) (cy : Cycle α) : Cycle α :=
  cy.rotate ((i + 1 + cy.cards.length - cy.cursor) % cy.cards.length)

/-- TODO(proof): mechanical corollary of `removeIdx_comm` plus the two
cursor `if` adjustments. -/
theorem removeAt_comm {α : Type} (cy : Cycle α) (i j : Nat)
    (hij : i < j) (hj : j < cy.cursor) (hl : j < cy.cards.length) :
    (cy.removeAt j).removeAt i = (cy.removeAt i).removeAt (j - 1) := sorry

end Cycle
