/-!
# Cards: color, suit, rank

The suit is *factored*: `Suit = Color × pair`, where `pair` selects
which of a color's two suits.  This makes the fibration the rules live
on definitional rather than proved:

* tableau rules see only `(rank, color)` — `Suit.color` is a projection,
  so the pair coordinate is invisible to them *by `rfl`*;
* twin-swap (theorem T) is the `pair` flip `Suit.flipPair`;
* foundations see the full four-way suit (`Color × Bool`).

Ranks are a plain 13-way enumeration with the numeric view `Rank.toIdx`
(0 = ace … 12 = king) — no proof fields, so equality stays literal and
`cases` stays total.
-/

/-- Card colors. -/
inductive Color : Type where
  | red | black
  deriving DecidableEq, Repr

/-- A suit, factored as a color plus a pair index. -/
structure Suit : Type where
  /-- The color — everything the tableau rules see. -/
  color : Color
  /-- Which of the color's two suits — invisible to the tableau rules,
  tracked by the foundations. -/
  pair : Bool
  deriving DecidableEq, Repr

/-- Hearts. -/
def Suit.heart : Suit := ⟨.red, false⟩

/-- Spades. -/
def Suit.spade : Suit := ⟨.black, false⟩

/-- Diamonds. -/
def Suit.diamond : Suit := ⟨.red, true⟩

/-- Clubs. -/
def Suit.club : Suit := ⟨.black, true⟩

/-- All four suits. -/
def Suit.all : List Suit := [Suit.heart, Suit.spade, Suit.diamond, Suit.club]

theorem Suit.mem_all (s : Suit) : s ∈ Suit.all := by
  rcases s with ⟨c, p⟩
  cases c <;> cases p <;>
    simp [Suit.all, Suit.heart, Suit.spade, Suit.diamond, Suit.club]

/-- The twin-swap relabeling (theorem T): exchange the two suits of a
color, fixing rank and color. -/
def Suit.flipPair (s : Suit) : Suit := ⟨s.color, !s.pair⟩

/-- Twin-swap preserves color *definitionally*: the tableau rules
cannot see the pair coordinate. -/
@[simp]
theorem Suit.flipPair_color (s : Suit) : s.flipPair.color = s.color := rfl

@[simp]
theorem Suit.flipPair_flipPair (s : Suit) : s.flipPair.flipPair = s := by
  rcases s with ⟨_, p⟩
  simp [Suit.flipPair, Bool.not_not]

theorem Suit.flipPair_ne (s : Suit) : s.flipPair ≠ s := by
  rcases s with ⟨_, p⟩
  cases p <;> simp [Suit.flipPair]

/-- Card ranks: ace is 0, king is 12 (see `Rank.toIdx`). -/
inductive Rank : Type where
  | ace | two | three | four | five | six | seven | eight | nine | ten
  | jack | queen | king
  deriving DecidableEq, Repr

/-- Numeric view: ace = 0, …, king = 12. -/
def Rank.toIdx : Rank → Nat
  | .ace => 0 | .two => 1 | .three => 2 | .four => 3 | .five => 4 | .six => 5
  | .seven => 6 | .eight => 7 | .nine => 8 | .ten => 9 | .jack => 10
  | .queen => 11 | .king => 12

theorem Rank.toIdx_lt (r : Rank) : r.toIdx < 13 := by cases r <;> decide

/-- Ranks are determined by their numeric view. -/
theorem Rank.toIdx_inj {r r' : Rank} (h : r.toIdx = r'.toIdx) : r = r' := by
  cases r <;> cases r' <;> simp_all [Rank.toIdx]

/-- All ranks. -/
def Rank.all : List Rank :=
  [.ace, .two, .three, .four, .five, .six, .seven, .eight, .nine, .ten, .jack, .queen, .king]

theorem Rank.mem_all (r : Rank) : r ∈ Rank.all := by cases r <;> simp [Rank.all]

/-- A playing card. -/
structure Card : Type where
  /-- The suit (color + pair). -/
  suit : Suit
  /-- The rank. -/
  rank : Rank
  deriving DecidableEq

/-- Twin-swap on cards: flip the suit's pair, keep the rank. -/
def Card.flipSuit (c : Card) : Card := ⟨c.suit.flipPair, c.rank⟩

@[simp]
theorem Card.flipSuit_flipSuit (c : Card) : c.flipSuit.flipSuit = c := by
  rcases c with ⟨⟨_, _⟩, _⟩
  simp [Card.flipSuit, Suit.flipPair, Bool.not_not]

/-- Twin-swap preserves the color projection definitionally. -/
@[simp]
theorem Card.flipSuit_color (c : Card) : c.flipSuit.suit.color = c.suit.color := rfl

theorem Card.flipSuit_ne (c : Card) : c.flipSuit ≠ c :=
  fun h => Suit.flipPair_ne c.suit (congrArg Card.suit h)

/-- Tableau stacking: `c` may be placed directly on `b` iff `c` is
exactly one rank below `b` and the colors differ. -/
def canSitOn (c b : Card) : Bool :=
  decide (c.rank.toIdx + 1 = b.rank.toIdx) && decide (c.suit.color ≠ b.suit.color)

@[simp]
theorem canSitOn_eq (c b : Card) :
    canSitOn c b = true ↔ c.rank.toIdx + 1 = b.rank.toIdx ∧ c.suit.color ≠ b.suit.color := by
  simp [canSitOn]

/-- Runs are rank-graded: nothing can sit both above and below the same
card (the seed of run acyclicity). -/
theorem canSitOn_antisymm {c b : Card} (h : canSitOn c b = true) : canSitOn b c ≠ true := by
  simp only [canSitOn_eq] at h
  obtain ⟨h1, -⟩ := h
  intro hcon
  simp only [canSitOn_eq] at hcon
  obtain ⟨h2, -⟩ := hcon
  omega

/-- The seat-locality fact (macro_formalization §6.2): a base `b` has at
most two tenants — `c` and its twin.  The receiver analysis (the K2/K6
goal kills) is built on this. -/
theorem Card.only_blocker_is_twin {c b z : Card}
    (hc : canSitOn c b = true) (hz : canSitOn z b = true) : z = c ∨ z = c.flipSuit := by
  rcases c with ⟨⟨cc, cp⟩, cr⟩
  rcases z with ⟨⟨zc, zp⟩, zr⟩
  rcases b with ⟨⟨bc, _bp⟩, br⟩
  obtain ⟨hcr, hcc⟩ := (canSitOn_eq _ _).mp hc
  obtain ⟨hzr, hzc⟩ := (canSitOn_eq _ _).mp hz
  have hcc' : cc ≠ bc := hcc
  have hzc' : zc ≠ bc := hzc
  have hcr' : cr.toIdx + 1 = br.toIdx := hcr
  have hzr' : zr.toIdx + 1 = br.toIdx := hzr
  have hrank : zr = cr := Rank.toIdx_inj (by omega)
  have hcolor : zc = cc := by
    cases cc <;> cases zc <;> cases bc <;> simp_all
  subst hrank hcolor
  cases cp <;> cases zp <;> simp [Card.flipSuit, Suit.flipPair]

/-- All 52 cards. -/
def Card.universe : List Card :=
  Suit.all.flatMap fun s => Rank.all.map fun r => Card.mk s r

theorem Card.mem_universe (c : Card) : c ∈ Card.universe := by
  rcases c with ⟨s, r⟩
  simp only [Card.universe, List.mem_flatMap, List.mem_map]
  exact ⟨s, s.mem_all, r, r.mem_all, rfl⟩

theorem Card.universe_length : Card.universe.length = 52 := by decide

/-- The receiver set of `X`: the cards `X` could sit directly on —
rank one up, opposite color (`canSitOn X`); empty for kings.  At most
two members (`only_blocker_is_twin`; exactly two for non-kings — the
twin suits of the other color).  The engine's receiver-type analysis
(K2/K6) reads this set. -/
def Card.receivers (X : Card) : List Card := Card.universe.filter fun r => canSitOn X r

theorem Card.mem_receivers_iff (X r : Card) : r ∈ X.receivers ↔ canSitOn X r = true := by
  simp [Card.receivers, Card.mem_universe]
