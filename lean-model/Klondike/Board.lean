import Klondike.Basic

/-!
# The tableau as a partial bijection (the matching)

`Base = Anchor ⊕ Card` — what a card can sit on.  The board stores
`topOf` (what sits on each base) with the single matching law `inj`;
the inverse `bottomOf` is derived by search over the (complete) base
enumeration.  One field, one law, the other direction free.

The matching stores only the *visible* edges: hidden-pile edges are
derived from the deal (see `Klondike.State`), foundation edges from
the heights.
-/

/-- The seven tableau pile anchors: a base position at the bottom of
each pile. -/
inductive Anchor : Type where
  | p0 | p1 | p2 | p3 | p4 | p5 | p6
  deriving DecidableEq, Repr

/-- All anchors. -/
def Anchor.all : List Anchor := [.p0, .p1, .p2, .p3, .p4, .p5, .p6]

theorem Anchor.mem_all (a : Anchor) : a ∈ Anchor.all := by cases a <;> simp [Anchor.all]

/-- Numeric view (pile index). -/
def Anchor.toIdx : Anchor → Nat
  | .p0 => 0 | .p1 => 1 | .p2 => 2 | .p3 => 3 | .p4 => 4 | .p5 => 5 | .p6 => 6

/-- What a card can sit on: a pile anchor, or another card. -/
abbrev Base := Sum Anchor Card

/-- Twin-swap on bases. -/
def Base.flipBase : Base → Base := Sum.map id Card.flipSuit

/-- The first element of `l` satisfying `p`. -/
def findFirst {α : Type} (p : α → Bool) : List α → Option α
  | [] => none
  | a :: t => if p a then some a else findFirst p t

@[simp] theorem findFirst_nil {α : Type} (p : α → Bool) : findFirst p [] = none := rfl

@[simp] theorem findFirst_cons {α : Type} (p : α → Bool) (a : α) (t : List α) :
    findFirst p (a :: t) = if p a then some a else findFirst p t := rfl

theorem findFirst_mem {α : Type} (p : α → Bool) :
    ∀ (l : List α) (a : α), findFirst p l = some a → a ∈ l ∧ p a = true
  | [], _, h => by simp at h
  | b :: t, a, h => by
      by_cases hb : p b = true
      · rw [findFirst_cons, if_pos hb, Option.some.injEq] at h
        subst h
        exact ⟨by simp, hb⟩
      · rw [findFirst_cons, if_neg hb] at h
        obtain ⟨hm, hp⟩ := findFirst_mem p t a h
        exact ⟨by simp [hm], hp⟩

theorem findFirst_of_unique {α : Type} (p : α → Bool) :
    ∀ (l : List α) (a : α), a ∈ l → p a = true → (∀ b ∈ l, p b = true → b = a) →
      findFirst p l = some a
  | [], _, h, _, _ => by simp at h
  | b :: t, a, hm, hp, hu => by
      rw [findFirst_cons]
      by_cases hb : p b = true
      · rw [if_pos hb, hu b (by simp) hb]
      · rw [if_neg hb]
        simp only [List.mem_cons] at hm
        refine findFirst_of_unique p t a ?_ hp ?_
        · rcases hm with h | h
          · subst h
            exact absurd hp hb
          · exact h
        · exact fun b' hb' hpb' => hu b' (by simp [hb']) hpb'

theorem findFirst_eq_none {α : Type} (p : α → Bool) :
    ∀ (l : List α), (∀ a ∈ l, p a ≠ true) → findFirst p l = none
  | [], _ => rfl
  | b :: t, h => by
      rw [findFirst_cons, if_neg (h b (by simp))]
      exact findFirst_eq_none p t (fun a ha => h a (by simp [ha]))

/-- The tableau board: a partial bijation read through `topOf` — for
each base, the card sitting on it.  The single law `inj` makes it a
matching: at most one card per base, hence `topOf` injective on its
support. -/
structure Board where
  /-- What sits on each base (`none` = empty base). -/
  topOf : Base → Option Card
  /-- The matching law: a card sits on at most one base. -/
  inj : ∀ b₁ b₂ c, topOf b₁ = some c → topOf b₂ = some c → b₁ = b₂

namespace Board

/-- Every base, for the derived search. -/
def enumBase : List Base := Anchor.all.map Sum.inl ++ Card.universe.map Sum.inr

theorem enumBase_complete (b : Base) : b ∈ enumBase := by
  cases b with
  | inl a =>
      simp only [enumBase, List.mem_append, List.mem_map]
      exact Or.inl ⟨a, a.mem_all, rfl⟩
  | inr c =>
      simp only [enumBase, List.mem_append, List.mem_map]
      exact Or.inr ⟨c, c.mem_universe, rfl⟩

/-- The derived inverse: the base under `c`, by search. -/
def bottomOf (bd : Board) (c : Card) : Option Base :=
  findFirst (fun b => decide (bd.topOf b = some c)) enumBase

/-- TODO(proof): the characterization of the derived inverse —
`findFirst_mem` + `enumBase_complete` + `inj` (mechanical). -/
theorem bottomOf_eq (bd : Board) (c : Card) (b : Base) :
    bd.bottomOf c = some b ↔ bd.topOf b = some c := sorry

/-- TODO(proof): the none half of the characterization. -/
theorem bottomOf_eq_none (bd : Board) (c : Card) :
    bd.bottomOf c = none ↔ ∀ b, bd.topOf b ≠ some c := sorry

/-- The empty board. -/
def empty : Board where
  topOf := fun _ => none
  inj := by intro b₁ b₂ c h₁ _; simp at h₁

@[simp] theorem empty_topOf (b : Base) : Board.empty.topOf b = none := rfl

/-- TODO(proof): via `findFirst_eq_none` + `empty_topOf`. -/
@[simp] theorem empty_bottomOf (c : Card) : Board.empty.bottomOf c = none := sorry

/-- Pointwise update at a base. -/
def update (f : Base → Option Card) (b : Base) (o : Option Card) : Base → Option Card :=
  fun b' => if b' = b then o else f b'

theorem update_self (f : Base → Option Card) (b : Base) (o : Option Card) :
    update f b o b = o := by simp [update]

theorem update_ne (f : Base → Option Card) (b b' : Base) (o : Option Card) (h : b' ≠ b) :
    update f b o b' = f b' := by simp [update, h]

/-- Detach whatever sits at `b`. -/
def detach (bd : Board) (b : Base) : Board where
  topOf := update bd.topOf b none
  inj := by
    intro b₁ b₂ c h₁ h₂
    by_cases hb₁ : b₁ = b
    · subst hb₁
      rw [update_self] at h₁
      simp at h₁
    · rw [update_ne _ _ _ _ hb₁] at h₁
      by_cases hb₂ : b₂ = b
      · subst hb₂
        rw [update_self] at h₂
        simp at h₂
      · rw [update_ne _ _ _ _ hb₂] at h₂
        exact bd.inj b₁ b₂ c h₁ h₂

@[simp] theorem detach_topOf (bd : Board) (b : Base) : (bd.detach b).topOf b = none := by
  simp [Board.detach, update_self]

@[simp] theorem detach_topOf_ne (bd : Board) (b b' : Base) (h : b' ≠ b) :
    (bd.detach b).topOf b' = bd.topOf b' := by
  simp [Board.detach, update_ne, h]

/-- Attach `c` at `b` — total, guarded (fails unless `b` is free and
`c` is unplaced). -/
def attach (bd : Board) (b : Base) (c : Card) : Option Board :=
  if hfree : bd.topOf b = none then
    if hnew : bd.bottomOf c = none then
      some { topOf := update bd.topOf b (some c), inj := by sorry }
    else none
  else none

/-- TODO(proof): what a successful attach does at the base. -/
theorem attach_topOf (bd : Board) (b : Base) (c : Card) {bd' : Board}
    (h : bd.attach b c = some bd') : bd'.topOf b = some c := sorry

/-- TODO(proof): what a successful attach leaves alone. -/
theorem attach_topOf_ne (bd : Board) (b : Base) (c : Card) {bd' : Board}
    (h : bd.attach b c = some bd') (hne : b' ≠ b) : bd'.topOf b' = bd.topOf b' := sorry

/-- TODO(proof): the attach guard is exactly the precondition. -/
theorem attach_eq_some_iff (bd : Board) (b : Base) (c : Card) :
    bd.attach b c ≠ none ↔ bd.topOf b = none ∧ bd.bottomOf c = none := sorry

/-- Conjugate the board by the twin-swap relabeling (T's action).
TODO(proof of inj): conjugation preserves the matching law. -/
def mapBy (bd : Board) : Board where
  topOf := fun b => (bd.topOf b.flipBase).map Card.flipSuit
  inj := by sorry

/-- The cards transitively above `c` (the run sitting on it), walked
with fuel (defensive against ill-formed cycles: the walk stops early).
Used by `pilePile`'s self-landing guard. -/
def aboveOf (bd : Board) (c : Card) : List Card :=
  let rec go : Nat → Base → List Card → List Card
    | 0, _, acc => acc
    | fuel + 1, b, acc =>
        match bd.topOf b with
        | none => acc
        | some c' => if acc.contains c' then acc else go fuel (Sum.inr c') (c' :: acc)
  go 52 (Sum.inr c) []

end Board
