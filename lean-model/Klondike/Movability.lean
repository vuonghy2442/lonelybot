import Klondike.State

/-!
# The per-card movability algebra (§8.1 — the `bm` decoding)

`macro_formalization.md` §8.1 (ledger C15): the engine's
`bottom_mask_of` (src/state.rs:40 — `get_bottom_mask`) decodes, per
card `c` with twin `t = c.flipSuit` and under-pair `u₁, u₂` (the twin
pair at `rank(c) − 1`, opposite color — the cards that can sit
directly on `c`), to

    bm ∋ c  ⟺  (vis c ∨ vis t)
              ∧ ( ¬free u₁ ∧ ¬free u₂
                  ∨ (vis c ⊕ vis t ⊕ free u₁ ⊕ free u₂) )

with `free = vis ∧ ¬locked`.  Aces have no under-pair (the `<< 4` arm
shifts below the word) — movable whenever the type-pair is visible.
The shipped `× 0b11` spread makes movability a *type-pair property*:
either twin carries it (`Card.movableOf_flipSuit`), which is why the
receiver side of every landing question reads a *pair*
(`Card.orVis_of_movableOf` is the `or_vis` door K2's §8.5 argument
names).

Per §8.7's standing caveat, this file DEFINES movability by the
formula — the shipped mask arithmetic is the *reference* (bound to
the code by the Rust `bm_algebra_matches` instrument, 2,000 random
masks × 52 cards).  The equivalence with the engine's mask arithmetic
is the separate owed lemma `Mask.bottomMask_matches_movableOf`
below — stated, not claimed proven.
-/

/-! ## The under-pair -/

/-- The under-pair of `c` (§8.1's `u₁, u₂`): the twin pair one rank
below, opposite color — the engine's `reduce_rank_swap_color` /
`swap_suit` pair (`u₁` keeps `c`'s suit pair and flips the color,
`u₂ = u₁.flipSuit`); `none` for aces (no rank below — the `<< 4` arm
of the word shifts out).  Exactly the cards that can sit directly on
`c` (`canSitOn_iff_underPair`). -/
def Card.underPair (c : Card) : Option (Card × Card) :=
  c.rank.pred.map fun r =>
    let u1 : Card := ⟨⟨c.suit.color.flip, c.suit.pair⟩, r⟩
    (u1, u1.flipSuit)

/-- The under-pair's general shape at a present predecessor: the
engine order `u₁ = reduce_rank_swap_color`, `u₂ = u₁.swap_suit`. -/
theorem Card.underPair_of_pred {c : Card} {r : Rank} (h : c.rank.pred = some r) :
    c.underPair = some (⟨⟨c.suit.color.flip, c.suit.pair⟩, r⟩,
                        Card.flipSuit ⟨⟨c.suit.color.flip, c.suit.pair⟩, r⟩) := by
  unfold Card.underPair
  rw [h]
  rfl

/-- The twin's under-pair is the same pair, order-swapped (§8.1's
type-pair geometry: `reduce_rank_swap_color (twin c) = u₂`). -/
theorem Card.underPair_flipSuit_of_pred {c : Card} {r : Rank}
    (h : c.rank.pred = some r) :
    c.flipSuit.underPair = some (Card.flipSuit ⟨⟨c.suit.color.flip, c.suit.pair⟩, r⟩,
                                  ⟨⟨c.suit.color.flip, c.suit.pair⟩, r⟩) := by
  have h1 : (c.flipSuit).rank.pred = some r := h
  have h2 := Card.underPair_of_pred (c := c.flipSuit) (r := r) h1
  simp only [Card.flipSuit, Suit.flipPair, Bool.not_not] at h2
  exact h2

/-- The under-pair members sit on `c` — the pair is exactly the
can-sit-on set, read back by the word's `<< 4` twin spread. -/
theorem Card.canSitOn_underPair {c u1 u2 : Card}
    (h : c.underPair = some (u1, u2)) :
    canSitOn u1 c = true ∧ canSitOn u2 c = true := by
  cases hpr : c.rank.pred with
  | none =>
      simp only [Card.underPair] at h
      rw [hpr] at h
      simp at h
  | some r =>
      simp only [Card.underPair] at h
      rw [hpr] at h
      obtain ⟨rfl, rfl⟩ := Option.some.inj h
      have hr := (rank_pred_iff c.rank r).mp hpr
      constructor
      · exact (canSitOn_eq _ c).mpr ⟨hr, by
          cases c.suit.color <;> simp [Color.flip]⟩
      · exact (canSitOn_eq _ c).mpr ⟨hr, by
          cases c.suit.color <;>
            simp [Color.flip, Card.flipSuit, Suit.flipPair]⟩

/-- The sitter recognition: the cards that can sit directly on `c`
are exactly the under-pair members (vacuous for aces — no card sits
on an ace, the engine's `reduce_rank_swap_color` underflow). -/
theorem Card.canSitOn_iff_underPair (c d : Card) :
    canSitOn d c = true ↔
      ∃ u : Card × Card, c.underPair = some u ∧ (d = u.1 ∨ d = u.2) := by
  constructor
  · intro hcs
    obtain ⟨hrk, hcol⟩ := (canSitOn_eq d c).mp hcs
    cases hpr : c.rank.pred with
    | none =>
        exfalso
        have hpred : c.rank.pred = some d.rank := (rank_pred_iff c.rank d.rank).mpr hrk
        rw [hpr] at hpred
        simp at hpred
    | some r =>
        have hrd : d.rank = r := Rank.toIdx_inj (by
          have hr := (rank_pred_iff c.rank r).mp hpr
          omega)
        refine ⟨(⟨⟨c.suit.color.flip, c.suit.pair⟩, r⟩,
                 Card.flipSuit ⟨⟨c.suit.color.flip, c.suit.pair⟩, r⟩),
          Card.underPair_of_pred hpr, ?_⟩
        rcases d with ⟨⟨dc, dp⟩, dr⟩
        have hdc : dc = c.suit.color.flip := color_ne_flip hcol
        have hdr : dr = r := hrd
        subst hdc
        subst hdr
        cases dp <;> cases hpp : c.suit.pair <;>
          simp [Card.flipSuit, Suit.flipPair, Color.flip]
  · rintro ⟨⟨u1, u2⟩, hu, rfl | rfl⟩
    · exact (canSitOn_underPair hu).1
    · exact (canSitOn_underPair hu).2

/-! ## The formula -/

/-- §8.1's per-card movability, on raw visibility/lockedness
functions:

    (vis c ∨ vis c.flipSuit) ∧ ( ¬free u₁ ∧ ¬free u₂
                                 ∨ (vis c ⊕ vis t ⊕ free u₁ ⊕ free u₂) )

with `free = vis ∧ ¬locked` inlined; aces (the absent under-pair)
movable whenever the type-pair is visible. -/
def Card.movableOf (vis locked : Card → Bool) (c : Card) : Bool :=
  (vis c || vis c.flipSuit) &&
    (match c.underPair with
     | none => true
     | some (u1, u2) =>
         (!(vis u1 && !locked u1) && !(vis u2 && !locked u2)
           || (((vis c ^^ vis c.flipSuit) ^^ (vis u1 && !locked u1))
                 ^^ (vis u2 && !locked u2))))

/-- §8.1's free-ness: `free = vis ∧ ¬locked`. -/
def State.free (st : State) (c : Card) : Bool := st.isVis c && !st.isLocked c

/-- The state-level movability: §8.1's algebra evaluated on the
board's own visibility and lockedness (the engine's
`bottom_mask_of(get_visible_mask(), get_locked_mask())`). -/
def State.movable (st : State) (c : Card) : Bool :=
  Card.movableOf st.isVis st.isLocked c

/-- The `or_vis` door: a movable card's type-pair is visible
somewhere — §8.1's first conjunct, the premise of K2's §8.5 receiver
argument ("`bm ∋` that pair requires `or_vis` on it"). -/
theorem Card.orVis_of_movableOf {vis locked : Card → Bool} {c : Card}
    (h : movableOf vis locked c = true) :
    vis c = true ∨ vis c.flipSuit = true := by
  simp only [Card.movableOf, Bool.and_eq_true_iff] at h
  exact Bool.or_eq_true_iff.mp h.1

/-- §8.1's aces: no under-pair (the `<< 4` arm shifts below the
word) — movable exactly when the type-pair is visible. -/
theorem Card.movableOf_ace (vis locked : Card → Bool) {c : Card}
    (hrank : c.rank = Rank.ace) :
    movableOf vis locked c = true ↔
      vis c = true ∨ vis c.flipSuit = true := by
  have h : c.underPair = none := by
    unfold Card.underPair
    rw [hrank]
    rfl
  simp only [Card.movableOf, h, Bool.and_true]
  exact Bool.or_eq_true_iff

/-- The §8.1 second-conjunct skeleton, symmetric in the twin (read
this off the four bits for the `× 0b11` type-pair property). -/
private theorem movable_pair_symm (a b f1 f2 : Bool) :
    ((b || a) && (!(f2) && !(f1) || (((b ^^ a) ^^ f2) ^^ f1)))
      = ((a || b) && (!(f1) && !(f2) || (((a ^^ b) ^^ f1) ^^ f2))) := by
  cases a <;> cases b <;> cases f1 <;> cases f2 <;> rfl

/-- The ×0b11 spread's Lean-side half: movability is a type-pair
property — either twin carries it, whichever card you ask. -/
theorem Card.movableOf_flipSuit (vis locked : Card → Bool) (c : Card) :
    movableOf vis locked c.flipSuit = movableOf vis locked c := by
  cases hpr : c.rank.pred with
  | none =>
      have hrank : c.rank = Rank.ace := by
        cases hrk2 : c.rank <;> simp_all [Rank.pred]
      have hprF : c.flipSuit.rank = c.rank := rfl
      have hL2 : c.flipSuit.underPair = none := by
        unfold Card.underPair
        rw [hprF, hrank]
        rfl
      have hR2 : c.underPair = none := by
        unfold Card.underPair
        rw [hrank]
        rfl
      simp only [Card.movableOf, hR2, hL2, Card.flipSuit_flipSuit, Bool.and_true]
      cases h1 : vis c <;> cases h2 : vis c.flipSuit <;> simp
  | some r =>
      have hL := Card.underPair_of_pred hpr
      have hR := Card.underPair_flipSuit_of_pred hpr
      simp only [Card.movableOf, hL, hR, Card.flipSuit_flipSuit]
      exact movable_pair_symm (vis c) (vis c.flipSuit)
        (vis ⟨⟨c.suit.color.flip, c.suit.pair⟩, r⟩
          && !locked ⟨⟨c.suit.color.flip, c.suit.pair⟩, r⟩)
        (vis (Card.flipSuit ⟨⟨c.suit.color.flip, c.suit.pair⟩, r⟩)
          && !locked (Card.flipSuit ⟨⟨c.suit.color.flip, c.suit.pair⟩, r⟩))

/-! ## The engine's mask arithmetic (the reference, §8.7) -/

/-- The engine's suit code (src/card.rs): pair at bit 0, color at bit
1 — house order hearts 0, diamonds 1, spades 2, clubs 3 (any
color/pair-respecting bijection gives the same algebra). -/
def Suit.code (s : Suit) : Nat :=
  match s with
  | ⟨.red, false⟩ => 0 | ⟨.red, true⟩ => 1
  | ⟨.black, false⟩ => 2 | ⟨.black, true⟩ => 3

/-- The engine's card-position layout (src/card.rs `Card::new` /
`mask_index`): a card's word bit is `4 * rank.toIdx + suitCode`, with
the color bit (the suit code's bit 1) xored by the rank's parity —
the interleave that makes `± 4` in the word the rank∓1/color-flip
move (`go_after`'s `(self + 4) ^ other < 2`), and `± 1` the twin. -/
def Card.maskIndex (c : Card) : Nat :=
  4 * c.rank.toIdx + (c.suit.code + 2 * (c.rank.toIdx % 2)) % 4

/-!
Little-endian mask words (`Nat → Bool`, `w i` = bit `i`),
truncated at 64 exactly as `u64`: the engine's 52-card words never
come within 4 of the truncation line here, but the guards below keep
the transcription honest.
-/
namespace Mask

/-- A word from a card-indexed bit function: position `i` is on iff
the position's owner card carries the bit (`maskIndex` is a bijection
Card ↔ position — the owed lemma's decode step). -/
def maskOf (f : Card → Bool) : Nat → Bool :=
  fun i => Card.universe.any fun c => (c.maskIndex == i) && f c

/-- u64 logical shift right by 1: bit `i` reads `i + 1`. -/
def shr1 (w : Nat → Bool) : Nat → Bool := fun i => w (i + 1)

/-- u64 shift left by 4 (the under-pair read's master move): bits
below 4 read 0 — aces shift out. -/
def shl4 (w : Nat → Bool) : Nat → Bool :=
  fun i => if i < 64 ∧ 4 ≤ i then w (i - 4) else false

/-- The `ALT_MASK` cut (0x5555…): even positions — the type
representatives, pair bit 0. -/
def alt (i : Nat) : Bool := decide (i % 2 = 0 ∧ i < 64)

/-- The `× 0b11` twin spread: on an ALT-cut (even-only) word the u64
product `y * 3` is the carry-free `y ||| y <<< 1` — each odd position
joins its twin below (bit `i` reads `i` or `i - 1`). -/
def spread (y : Nat → Bool) : Nat → Bool :=
  fun i => if i < 64 then y i || (if 1 ≤ i then y (i - 1) else false) else false

/-- The engine's `bottom_mask_of` (src/state.rs:40), transcribed on
little-endian position words — the *reference* for §8.1's parity
lemma: the `free = vis & !locked` cut, the twin reads `>>> 1`, the
under-pair reads `<<< 4` (rank − 1, color-flipped), the ALT
representative cut, the `× 0b11` spread. -/
def bottomMask (vis locked : Nat → Bool) : Nat → Bool :=
  let free : Nat → Bool := fun i => vis i && !locked i
  let xorVis : Nat → Bool :=
    fun i => (vis i ^^ (shr1 vis) i)
  let xorFreeUp : Nat → Bool :=
    fun i => if 4 ≤ i then (free (i - 4) ^^ free (i - 3)) else false
  let orFreeUp : Nat → Bool :=
    fun i => if 4 ≤ i then (free (i - 4) || free (i - 3)) else false
  let orVis : Nat → Bool := fun i => vis i || (shr1 vis) i
  spread (fun i => ((xorVis i ^^ xorFreeUp i) || !orFreeUp i) && orVis i && alt i)

/-- **The owed engine equivalence (§8.7)**: the shipped mask
arithmetic and §8.1's formula agree, per card, at every
`(vis, locked)` grid — the Lean form of `bm_algebra_matches` (the
Rust binding instrument, 2,000 random masks × 52 cards).  NOT
PROVEN: this row is the §8.7 standing caveat, the mask layer's
parity debt — do not cite as established.

TODO(proof) [M]: per-position decode.  (1) Layout: `maskIndex` is
injective (52 distinct positions — rank block by `/ 4`, code recovery
by the parity's own mod-4 inverse; `decide`-able per rank×suit grid)
and, at a fixed rank block `4r`, the four positions differ only in
the low two bits, with bit 0 = the suit's pair (the parity xor
touches only bit 1) — so `maskIndex c` is even iff `c.suit.pair =
false`, the ALT/spread representatives are the pair-false twins, and
`maskIndex c.flipSuit = maskIndex c + 1` (the twin is the adjacent
bit).  (2) Reads: `(maskOf f) (maskIndex c) = f c` and
`(maskOf f) (maskIndex c + 1) = f c.flipSuit` for every card (the
position owner's uniqueness); the `<<< 4` reads at
`maskIndex c - 4, - 3` land exactly on the two `underPair` members of
`c` — the ±4 block arithmetic plus the code's color flip identify
them (`canSitOn_iff_underPair` closes the identification) — while
below block 0 (aces, `maskIndex < 4`) the `shl4` reads are `false`
and the `¬free ∧ ¬free` arm fires vacuously, matching
`underPair = none` (`movableOf_ace`).  No u64 truncation ever fires
(all touched positions are ≤ 52 + 4 < 64), so the `if i < 64` guards
never bite.  (3) Finish: both sides read the same four bits
`A = vis c`, `B = vis c.flipSuit`, `F1 = free u₁`, `F2 = free u₂` —
the identical §8.1 skeleton — by Bool exhaustion (16 cases, the
`(A ∨ B) ∧ (¬F1 ∧ ¬F2 ∨ A ⊕ B ⊕ F1 ⊕ F2)` truth table), with the odd
representative routed through `movableOf_flipSuit`. -/
theorem bottomMask_matches_movableOf (vis locked : Card → Bool) (c : Card) :
    bottomMask (maskOf vis) (maskOf locked) (c.maskIndex) = true ↔
      Card.movableOf vis locked c = true := sorry

end Mask
