import Klondike.Basic

/-!
# The stock as a physical deck: the cursor machine

The stock/waste is the deal-order list with a cursor — cards before
the cursor are the waste (top at `cursor - 1`), from it the deck.  The
physical game has exactly two stock operations: **deal** — pass the
next `s` cards, clamped at the pass end (the partial final deal passes
the last card), wrapping from the end to a fresh pass (`dealOnce`,
deck.rs's `offset_once`) — and **play the top** — splice out the waste
top (`removeAt`).  The cursor range `[0, length]` includes the
pass-end state (all passed, last card exposed).

The jump (`drawTo`, deck.rs's `draw(id)`) is the *derived* macro
shortcut — "deal until position `i` is the top" — legal exactly when
`i` is in the accessible set (`Pace.maskPos`).

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

/-- One deal (deck.rs `offset_once`): pass the next `s` cards, clamped
at the pass end — the final, partial deal passes the last card (the
last-card rule) — and from the pass end, wrap to a fresh pass.  The
only way the cursor advances in the physical game, at any step
`s ≥ 1`. -/
def dealOnce (s : Nat) (cy : Cycle α) : Cycle α :=
  if cy.cursor ≥ cy.cards.length then { cy with cursor := 0 }
  else { cy with cursor := min (cy.cursor + s) cy.cards.length }

@[simp] theorem dealOnce_cards (s : Nat) (cy : Cycle α) :
    (cy.dealOnce s).cards = cy.cards := by
  simp only [dealOnce]
  split <;> rfl

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

/-- A found index is in range. -/
theorem findFirstIdx_lt {α : Type} (p : α → Bool) : ∀ (l : List α) (i : Nat),
    findFirstIdx p l = some i → i < l.length := by
  intro l
  induction l with
  | nil => intro i h; simp [findFirstIdx] at h
  | cons a t ih =>
    intro i h
    simp only [findFirstIdx] at h
    by_cases pa : p a = true
    · rw [if_pos pa, Option.some.injEq] at h
      subst h
      simp
    · rw [if_neg pa] at h
      cases hf : findFirstIdx p t with
      | none => rw [hf] at h; simp at h
      | some j =>
        rw [hf, Option.map_some, Option.some.injEq] at h
        subst h
        have hj := ih j hf
        simp only [List.length_cons]
        omega

/-- A found position is in range. -/
theorem posOf_lt {c : Card} {cy : Cycle Card} {i : Nat}
    (h : cy.posOf c = some i) : i < cy.cards.length :=
  findFirstIdx_lt _ cy.cards i h

/-- Has `c` been passed (is it in the waste)? -/
def passed (c : Card) (cy : Cycle Card) : Bool :=
  match cy.posOf c with
  | some i => decide (i < cy.cursor)
  | none => false

/-- The jump: land the cursor just past position `i` (deck.rs `draw(id)`
= `set_offset (id + 1)`) — the derived shortcut for "deal until the
card at `i` is the waste top", legal exactly when `i` is in the
accessible set (`Pace.maskPos`).  At the last position the cursor
saturates at `length` (the pass-end state), not 0. -/
def drawTo (i : Nat) (cy : Cycle α) : Cycle α :=
  { cy with cursor := i + 1 }

theorem removeAt_comm {α : Type} (cy : Cycle α) (i j : Nat)
    (hij : i < j) (hj : j < cy.cursor) (hl : j < cy.cards.length) :
    (cy.removeAt j).removeAt i = (cy.removeAt i).removeAt (j - 1) := by
  have hj1 : j - 1 + 1 = j := by omega
  have hic : i < cy.cursor := by omega
  have hic1 : i < cy.cursor - 1 := by omega
  have hjc1 : j - 1 < cy.cursor - 1 := by omega
  have hcards : removeIdx (removeIdx cy.cards j) i
      = removeIdx (removeIdx cy.cards i) (j - 1) := by
    have h := removeIdx_comm cy.cards i (j - 1) (by omega) (by omega)
    rw [hj1] at h
    exact h.symm
  simp only [removeAt]
  simp only [if_pos hj, if_pos hic, if_pos hic1, if_pos hjc1, hcards]

end Cycle
