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

/-- Twin-swap preserves the rank, definitionally. -/
@[simp]
theorem Card.flipSuit_rank (c : Card) : c.flipSuit.rank = c.rank := rfl

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

/-- The *local* twin swap: exchange just the pair `c`, `c.flipSuit`,
leaving every other card fixed.  Unlike `flipSuit` (the global
relabeling — every card of the flipped suit, everywhere), this swaps
the two cards in place: the representation-canonicalization license —
when the twin suits' foundations sit at equal heights, which twin
occupies a seat (or covers one) is invisible (Klondike/TwinSwap.lean). -/
def Card.swapTwin (c x : Card) : Card :=
  if x = c then c.flipSuit else if x = c.flipSuit then c else x

@[simp] theorem Card.swapTwin_self_left (c : Card) : Card.swapTwin c c = c.flipSuit := by
  simp [Card.swapTwin]

@[simp] theorem Card.swapTwin_self_right (c : Card) : Card.swapTwin c c.flipSuit = c := by
  unfold Card.swapTwin
  rw [if_neg (Card.flipSuit_ne c), if_pos rfl]

/-- The local swap is an involution. -/
@[simp]
theorem Card.swapTwin_swapTwin (c x : Card) : Card.swapTwin c (Card.swapTwin c x) = x := by
  by_cases h₁ : x = c
  · subst h₁; rw [Card.swapTwin_self_left, Card.swapTwin_self_right]
  · by_cases h₂ : x = c.flipSuit
    · subst h₂; rw [Card.swapTwin_self_right, Card.swapTwin_self_left]
    · have h₃ : Card.swapTwin c x = x := by
        unfold Card.swapTwin; rw [if_neg h₁, if_neg h₂]
      rw [h₃]; unfold Card.swapTwin; rw [if_neg h₁, if_neg h₂]

/-- Outside the pair, the local swap is the identity: exactly the two
cards `t`, `t.flipSuit` are exchanged, the other 50 are fixed. -/
theorem Card.swapTwin_of_ne {t x : Card} (h₁ : x ≠ t) (h₂ : x ≠ t.flipSuit) :
    Card.swapTwin t x = x := by
  unfold Card.swapTwin
  rw [if_neg h₁, if_neg h₂]

/-- The local swap is invisible to the tableau rules (color). -/
@[simp] theorem Card.swapTwin_color (c x : Card) :
    (Card.swapTwin c x).suit.color = x.suit.color := by
  by_cases h₁ : x = c
  · rw [h₁]; simp
  · by_cases h₂ : x = c.flipSuit
    · rw [h₂]; simp [Card.flipSuit_color]
    · unfold Card.swapTwin; rw [if_neg h₁, if_neg h₂]

/-- The local swap preserves rank. -/
@[simp] theorem Card.swapTwin_rank (c x : Card) :
    (Card.swapTwin c x).rank = x.rank := by
  by_cases h₁ : x = c
  · rw [h₁]; simp
  · by_cases h₂ : x = c.flipSuit
    · rw [h₂]; simp
    · unfold Card.swapTwin; rw [if_neg h₁, if_neg h₂]

/-- The local swap is injective (an involution is). -/
theorem Card.swapTwin_inj (c : Card) : Function.Injective (Card.swapTwin c) := by
  intro x y h
  have h' := congrArg (Card.swapTwin c) h
  rwa [Card.swapTwin_swapTwin, Card.swapTwin_swapTwin] at h'

/-- The transfer fact behind the twin-transposition mechanism: a card
that sits on `y` sits equally on either twin — a bare twin's load can
always be re-homed onto the other twin (tableau rules are twin-blind). -/
@[simp] theorem canSitOn_swapTwin_right (t x y : Card) :
    canSitOn x (Card.swapTwin t y) = canSitOn x y := by
  simp [canSitOn]

/-- The other half: the twin swap on the *moving* card preserves
where it can sit. -/
@[simp] theorem canSitOn_swapTwin_left (t x y : Card) :
    canSitOn (Card.swapTwin t x) y = canSitOn x y := by
  simp [canSitOn]

/-! ### The full twin swap (the automorphism Φ)

`swapFull t` exchanges the two suits of `t`'s color *except* that the
pair `t`, `t.flipSuit` stays pinned — equivalently, the relabeling by
the color's suit swap with the pair un-swapped.  Unlike the local pin
(`swapTwin`), this map commutes with `apply` (TwinSwap.lean,
`State.apply_swapFull`): the suit counters move with the cards, so the
foundation guards translate — under the license that the pinned pair's
two suits sit at equal heights (which §5.5's redundant-pair premise
supplies, `State.redundantTwins_heights_eq`). -/

/-- The suit permutation backing `swapFull`'s heights: flip the pair
bit on `t`'s color, fix the other color.  An involution. -/
def Suit.swapColorOf (t : Card) (s : Suit) : Suit :=
  if s.color = t.suit.color then s.flipPair else s

/-- The full twin swap on cards. -/
def Card.swapFull (t x : Card) : Card :=
  if x = t ∨ x = t.flipSuit then x
  else if x.suit.color = t.suit.color then x.flipSuit else x

@[simp] theorem Suit.swapColorOf_color (t : Card) (s : Suit) :
    (Suit.swapColorOf t s).color = s.color := by
  unfold Suit.swapColorOf
  split <;> rfl

theorem Suit.swapColorOf_swapColorOf (t : Card) (s : Suit) :
    Suit.swapColorOf t (Suit.swapColorOf t s) = s := by
  unfold Suit.swapColorOf
  by_cases h : s.color = t.suit.color
  · rw [if_pos h, if_pos (by rw [Suit.flipPair_color]; exact h), Suit.flipPair_flipPair]
  · rw [if_neg h, if_neg h]

theorem Suit.swapColorOf_inj (t : Card) : Function.Injective (Suit.swapColorOf t) := by
  intro a b h
  have h' := congrArg (Suit.swapColorOf t) h
  rwa [Suit.swapColorOf_swapColorOf, Suit.swapColorOf_swapColorOf] at h'

/-- The pinned pair, left. -/
@[simp] theorem Card.swapFull_self_left (t : Card) : Card.swapFull t t = t := by
  unfold Card.swapFull
  rw [if_pos (Or.inl rfl)]

/-- The pinned pair, right. -/
@[simp] theorem Card.swapFull_self_right (t : Card) : Card.swapFull t t.flipSuit = t.flipSuit := by
  unfold Card.swapFull
  rw [if_pos (Or.inr rfl)]

/-- The pinned pair exhausts the rank-`t.rank` cards of `t`'s color. -/
theorem Card.eq_or_flipSuit_eq_of_color_rank {t x : Card}
    (hr : x.rank = t.rank) (hc : x.suit.color = t.suit.color) :
    x = t ∨ x = t.flipSuit := by
  rcases t with ⟨⟨tc, tp⟩, tr⟩
  rcases x with ⟨⟨xc, xp⟩, xr⟩
  have hrr : xr = tr := hr
  have hcc : xc = tc := hc
  subst hrr; subst hcc
  cases tp <;> cases xp <;> simp [Card.flipSuit, Suit.flipPair]

/-- Flipping preserves non-membership of the pinned pair. -/
theorem Card.flipSuit_not_pair {t x : Card} (hp : ¬ (x = t ∨ x = t.flipSuit)) :
    ¬ (x.flipSuit = t ∨ x.flipSuit = t.flipSuit) := by
  rintro (h | h)
  · exact hp (Or.inr (by
      have h' := congrArg Card.flipSuit h
      rwa [Card.flipSuit_flipSuit] at h'))
  · exact hp (Or.inl (by
      have h' := congrArg Card.flipSuit h
      rwa [Card.flipSuit_flipSuit, Card.flipSuit_flipSuit] at h'))

/-- Outside the pinned pair, a card of `t`'s color is the plain flip. -/
theorem Card.swapFull_of_not_pair {t x : Card}
    (hp : ¬ (x = t ∨ x = t.flipSuit)) (hc : x.suit.color = t.suit.color) :
    Card.swapFull t x = x.flipSuit := by
  rw [Card.swapFull, if_neg hp, if_pos hc]

/-- A card of the other color is fixed. -/
theorem Card.swapFull_of_color_ne {t x : Card} (hc : x.suit.color ≠ t.suit.color) :
    Card.swapFull t x = x := by
  have hp : ¬ (x = t ∨ x = t.flipSuit) := by
    rintro (h | h)
    · exact hc (h ▸ rfl)
    · exact hc (by rw [h, Card.flipSuit_color])
  rw [Card.swapFull, if_neg hp, if_neg hc]

/-- The full swap commutes with the global twin flip. -/
@[simp] theorem Card.swapFull_flipSuit (t x : Card) :
    Card.swapFull t x.flipSuit = (Card.swapFull t x).flipSuit := by
  by_cases hp : x = t ∨ x = t.flipSuit
  · rcases hp with rfl | rfl <;> simp
  · have hp2 := Card.flipSuit_not_pair (t := t) (x := x) hp
    by_cases hc : x.suit.color = t.suit.color
    · have hc2 : (x.flipSuit).suit.color = t.suit.color := by
        rw [Card.flipSuit_color]
        exact hc
      rw [show Card.swapFull t x = x.flipSuit from Card.swapFull_of_not_pair hp hc,
        Card.swapFull_of_not_pair hp2 hc2, Card.flipSuit_flipSuit]
    · have hc2 : ¬ ((x.flipSuit).suit.color = t.suit.color) := by
        rw [Card.flipSuit_color]
        exact hc
      rw [show Card.swapFull t x = x from Card.swapFull_of_color_ne hc,
        Card.swapFull_of_color_ne hc2]

/-- The full swap is an involution. -/
@[simp] theorem Card.swapFull_swapFull (t x : Card) :
    Card.swapFull t (Card.swapFull t x) = x := by
  by_cases hp : x = t ∨ x = t.flipSuit
  · rcases hp with rfl | rfl <;> simp [Card.swapFull_self_left, Card.swapFull_self_right]
  · have hp2 := Card.flipSuit_not_pair (t := t) (x := x) hp
    by_cases hc : x.suit.color = t.suit.color
    · have hc2 : (x.flipSuit).suit.color = t.suit.color := by
        rw [Card.flipSuit_color]
        exact hc
      rw [Card.swapFull_of_not_pair hp hc, Card.swapFull_of_not_pair hp2 hc2,
        Card.flipSuit_flipSuit]
    · rw [Card.swapFull_of_color_ne hc, Card.swapFull_of_color_ne hc]

/-- The full swap is invisible to the tableau rules (color). -/
@[simp] theorem Card.swapFull_color (t x : Card) :
    (Card.swapFull t x).suit.color = x.suit.color := by
  by_cases hp : x = t ∨ x = t.flipSuit
  · rcases hp with rfl | rfl <;> simp [Card.swapFull_self_left, Card.swapFull_self_right]
  · by_cases hc : x.suit.color = t.suit.color
    · rw [Card.swapFull_of_not_pair hp hc, Card.flipSuit_color]
    · rw [Card.swapFull_of_color_ne hc]

/-- The full swap preserves rank. -/
@[simp] theorem Card.swapFull_rank (t x : Card) :
    (Card.swapFull t x).rank = x.rank := by
  by_cases hp : x = t ∨ x = t.flipSuit
  · rcases hp with rfl | rfl <;> simp [Card.swapFull_self_left, Card.swapFull_self_right]
  · by_cases hc : x.suit.color = t.suit.color
    · rw [Card.swapFull_of_not_pair hp hc, Card.flipSuit_rank]
    · rw [Card.swapFull_of_color_ne hc]

/-- The full swap is injective (an involution is). -/
theorem Card.swapFull_inj (t : Card) : Function.Injective (Card.swapFull t) := by
  intro x y h
  have h' := congrArg (Card.swapFull t) h
  rwa [Card.swapFull_swapFull, Card.swapFull_swapFull] at h'

/-- The heights permutation sends `t`'s suit to the twin's. -/
@[simp] theorem Suit.swapColorOf_left (t : Card) :
    Suit.swapColorOf t t.suit = t.flipSuit.suit := by
  unfold Suit.swapColorOf
  rw [if_pos rfl]
  rfl

/-- The heights permutation sends the twin's suit back. -/
@[simp] theorem Suit.swapColorOf_right (t : Card) :
    Suit.swapColorOf t (t.flipSuit).suit = t.suit := by
  have : (t.flipSuit).suit = t.suit.flipPair := rfl
  unfold Suit.swapColorOf
  rw [this, if_pos (by rw [Suit.flipPair_color]), Suit.flipPair_flipPair]

/-- A suit of the other color is fixed by the heights permutation. -/
theorem Suit.swapColorOf_of_color_ne {t : Card} {s : Suit} (hc : s.color ≠ t.suit.color) :
    Suit.swapColorOf t s = s := by
  unfold Suit.swapColorOf
  rw [if_neg hc]

/-- The heights probe under the full swap: the swapped card's suit,
permuted, is the card's own suit — except for the pinned pair, where it
crosses to the twin's (exactly where the equal-heights license fires). -/
theorem Suit.swapColorOf_swapFull_suit {t : Card} (x : Card) :
    Suit.swapColorOf t (Card.swapFull t x).suit =
      if x = t then t.flipSuit.suit
      else if x = t.flipSuit then t.suit
      else x.suit := by
  by_cases ht : x = t
  · rw [ht, Card.swapFull_self_left, Suit.swapColorOf_left, if_pos rfl]
  · by_cases ht' : x = t.flipSuit
    · rw [ht', Card.swapFull_self_right, Suit.swapColorOf_right,
        if_neg (Card.flipSuit_ne t), if_pos rfl]
    · rw [if_neg ht, if_neg ht']
      by_cases hc : x.suit.color = t.suit.color
      · rw [Card.swapFull_of_not_pair (not_or.mpr ⟨ht, ht'⟩) hc]
        show Suit.swapColorOf t (x.flipSuit).suit = x.suit
        have hs : (x.flipSuit).suit = x.suit.flipPair := rfl
        rw [hs]
        unfold Suit.swapColorOf
        rw [if_pos (by rw [Suit.flipPair_color]; exact hc), Suit.flipPair_flipPair]
      · rw [Card.swapFull_of_color_ne hc, Suit.swapColorOf_of_color_ne hc]
