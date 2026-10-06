/-!
# The original game — cards

Self-contained: suits are an unfactored four-way enumeration, and
color, twins, and the foundation build order are *derived* notions.
No engine vocabulary appears at this layer.
-/

/-! ## Colors and suits -/

/-- Card colors. -/
inductive Color : Type where
  | red | black
  deriving DecidableEq, Repr

/-- The four suits of a standard deck. -/
inductive Suit : Type where
  | spade | heart | diamond | club
  deriving DecidableEq, Repr

/-- All suits. -/
def Suit.all : List Suit := [.spade, .heart, .diamond, .club]

theorem Suit.mem_all (s : Suit) : s ∈ Suit.all := by
  cases s <;> simp [Suit.all]

/-- A suit's color: hearts and diamonds are red. -/
def Suit.color : Suit → Color
  | .heart | .diamond => .red
  | .spade | .club => .black

/-- The other suit of the same color (the twin). -/
def Suit.twin : Suit → Suit
  | .spade => .club
  | .club => .spade
  | .heart => .diamond
  | .diamond => .heart

@[simp] theorem Suit.twin_twin (s : Suit) : s.twin.twin = s := by
  cases s <;> rfl

@[simp] theorem Suit.color_twin (s : Suit) : s.twin.color = s.color := by
  cases s <;> rfl

theorem Suit.twin_ne (s : Suit) : s.twin ≠ s := by
  cases s <;> simp [Suit.twin]

/-! ## Ranks -/

/-- Card ranks: ace low through king. -/
inductive Rank : Type where
  | ace | two | three | four | five | six | seven | eight | nine | ten
  | jack | queen | king
  deriving DecidableEq, Repr

/-- The zero-based rank index: ace = 0, king = 12. -/
def Rank.toIdx : Rank → Nat
  | .ace => 0 | .two => 1 | .three => 2 | .four => 3 | .five => 4 | .six => 5
  | .seven => 6 | .eight => 7 | .nine => 8 | .ten => 9 | .jack => 10
  | .queen => 11 | .king => 12

theorem Rank.toIdx_lt (r : Rank) : r.toIdx < 13 := by
  cases r <;> decide

theorem Rank.toIdx_inj {r r' : Rank} (h : r.toIdx = r'.toIdx) : r = r' := by
  cases r <;> cases r' <;> simp_all [Rank.toIdx]

/-- All ranks, ace first. -/
def Rank.all : List Rank :=
  [.ace, .two, .three, .four, .five, .six, .seven, .eight, .nine, .ten,
    .jack, .queen, .king]

theorem Rank.mem_all (r : Rank) : r ∈ Rank.all := by
  cases r <;> simp [Rank.all]

/-! ## Cards -/

/-- A playing card. -/
structure Card : Type where
  suit : Suit
  rank : Rank
  deriving DecidableEq

/-- A suit's foundation order: ace, two, …, king. -/
def Suit.upCards (s : Suit) : List Card := Rank.all.map (Card.mk s)

theorem Suit.upCards_length (s : Suit) : s.upCards.length = 13 := by
  cases s <;> decide

theorem Suit.mem_upCards {s : Suit} {r : Rank} : Card.mk s r ∈ s.upCards :=
  List.mem_map.2 ⟨r, r.mem_all, rfl⟩

/-- The full 52-card deck. -/
def Card.universe : List Card := Suit.all.flatMap Suit.upCards

theorem Card.mem_universe (c : Card) : c ∈ Card.universe := by
  rcases c with ⟨s, r⟩
  simp only [Card.universe, List.mem_flatMap]
  exact ⟨s, s.mem_all, Suit.mem_upCards⟩

theorem Card.universe_length : Card.universe.length = 52 := by
  decide

/-! ## The tableau fit -/

/-- Tableau stacking: `c` may sit directly on `b` iff `c` is exactly
one rank below `b` and the colors differ. -/
def canSitOn (c b : Card) : Bool :=
  decide (c.rank.toIdx + 1 = b.rank.toIdx) && decide (c.suit.color ≠ b.suit.color)

@[simp] theorem canSitOn_eq (c b : Card) :
    canSitOn c b = true ↔
      c.rank.toIdx + 1 = b.rank.toIdx ∧ c.suit.color ≠ b.suit.color := by
  simp [canSitOn]

/-- The tableau rules cannot tell twins apart: swapping the target's
twin suits does not change where a card may sit (the seed of the
twin machinery, here a one-line fact of the original rules). -/
@[simp] theorem canSitOn_twin_right (c z : Card) :
    canSitOn c { z with suit := z.suit.twin } = canSitOn c z := by
  simp [canSitOn]
