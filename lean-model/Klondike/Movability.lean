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
`Mask.bottomMask_matches_movableOf` below is now PROVEN (2026-10-05,
file-sorry-free): the §8.7 caveat is discharged and the mask layer's
parity debt paid — the layout decode (plan step 1), the owner-unique
reads and the ACE/under-pair position arithmetic (step 2), and the
16-case skeleton over the four read bits (step 3), with the
pair-true twins routed through `movableOf_flipSuit`.
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

/-! ### The layout decode (the owed lemma's plan, step 1)

Grid-decided facts about `maskIndex`: the pair bit is the position's
bit 0, the twin is the adjacent position, aces sit below the `<<< 4`
read's guard, every other card at or above it — and the layout is
injective, so every position bit has exactly one owner card.  Each is
a closed numeric identity on the 52-cell rank-by-suit grid. -/

/-- The suit code is a two-bit number. -/
theorem Suit.code_lt (s : Suit) : s.code < 4 := by
  rcases s with ⟨c, p⟩ <;> cases c <;> cases p <;> decide

/-- The suit code is injective — the layout's low two bits are the
suit. -/
theorem Suit.code_inj {s t : Suit} (h : s.code = t.code) : s = t := by
  rcases s with ⟨c, p⟩ <;> rcases t with ⟨c', p'⟩ <;>
    cases c <;> cases c' <;> cases p <;> cases p' <;> simp_all [Suit.code]

/-- `maskIndex` is injective — every position word bit has exactly one
owner card: the rank block is `i / 4`, the suit code the parity's own
mod-4 inverse (`canSitOn_iff_underPair`'s partner block). -/
theorem Card.maskIndex_inj {e d : Card} (h : e.maskIndex = d.maskIndex) : e = d := by
  rcases e with ⟨se, re⟩
  rcases d with ⟨sd, rd⟩
  have hb1 : Suit.code se < 4 := Suit.code_lt se
  have hb2 : Suit.code sd < 4 := Suit.code_lt sd
  simp only [Card.maskIndex] at h
  have hcode : (Suit.code se + 2 * (re.toIdx % 2)) % 4
          = (Suit.code sd + 2 * (rd.toIdx % 2)) % 4 := by omega
  have hre : re.toIdx = rd.toIdx := by omega
  have her : re = rd := Rank.toIdx_inj hre
  subst her
  have hse : se = sd := Suit.code_inj (by omega)
  rw [hse]

/-- The layout's bit 0 is the suit's pair: `maskIndex` is even
exactly on the pair-`false` representatives — the ALT/spread half of
each twin pair. -/
theorem Card.even_maskIndex {d : Card} (h : d.suit.pair = false) :
    d.maskIndex % 2 = 0 := by
  rcases d with ⟨⟨c, p⟩, r⟩
  cases c <;> cases p <;> cases r <;>
    simp_all [Card.maskIndex, Suit.code, Rank.toIdx] <;> decide

/-- The pair-`true` twins own the odd positions. -/
theorem Card.odd_maskIndex {d : Card} (h : d.suit.pair = true) :
    d.maskIndex % 2 = 1 := by
  rcases d with ⟨⟨c, p⟩, r⟩
  cases c <;> cases p <;> cases r <;>
    simp_all [Card.maskIndex, Suit.code, Rank.toIdx] <;> decide

/-- The 52 positions sit far below the u64 truncation line — no
guard in the machinery ever fires (52 + 4 < 64). -/
theorem Card.maskIndex_lt64 (d : Card) : d.maskIndex < 64 := by
  rcases d with ⟨⟨c, p⟩, r⟩
  cases c <;> cases p <;> cases r <;> decide

/-- The twin is the adjacent bit: one position up from the
pair-`false` representative. -/
theorem Card.maskIndex_flip_pair_false {d : Card} (h : d.suit.pair = false) :
    d.flipSuit.maskIndex = d.maskIndex + 1 := by
  rcases d with ⟨⟨c, p⟩, r⟩
  cases c <;> cases p <;> cases r <;>
    simp_all [Card.flipSuit, Suit.flipPair, Card.maskIndex, Suit.code, Rank.toIdx] <;> decide

/-- …and one position down from the pair-`true` twin. -/
theorem Card.maskIndex_flip_pair_true {d : Card} (h : d.suit.pair = true) :
    d.flipSuit.maskIndex = d.maskIndex - 1 := by
  rcases d with ⟨⟨c, p⟩, r⟩
  cases c <;> cases p <;> cases r <;>
    simp_all [Card.flipSuit, Suit.flipPair, Card.maskIndex, Suit.code, Rank.toIdx] <;> decide

/-- Aces sit below the `<<< 4` line: the under-pair arms shift below
the word and read zero. -/
theorem Card.maskIndex_lt4 {d : Card} (h : d.rank = Rank.ace) :
    d.maskIndex < 4 := by
  rcases d with ⟨⟨c, p⟩, r⟩
  cases c <;> cases p <;> cases r <;>
    simp_all [Card.maskIndex, Suit.code, Rank.toIdx] <;> decide

/-- Every other card sits at or above the under-pair read's guard
`(4 ≤ i)`. -/
theorem Card.maskIndex_ge4 {d : Card} (h : d.rank ≠ Rank.ace) :
    4 ≤ d.maskIndex := by
  rcases d with ⟨⟨c, p⟩, r⟩
  cases c <;> cases p <;> cases r <;>
    simp_all [Card.maskIndex, Suit.code, Rank.toIdx] <;> decide

/-- The `± 4` under-pair reads (the owed lemma's plan, step 2): at a
pair-false representative `c` with present predecessor rank `r`, the
two under-pair members own exactly the positions `maskIndex c - 4`
and `maskIndex c - 3` — the rank-block arithmetic plus the code's
color flip land on the sitters. -/
theorem Card.maskIndex_underPair_positions {c : Card} {r : Rank}
    (hpair : c.suit.pair = false) (hpred : c.rank.pred = some r) :
    (⟨⟨c.suit.color.flip, c.suit.pair⟩, r⟩ : Card).maskIndex + 4 = c.maskIndex ∧
      (Card.flipSuit ⟨⟨c.suit.color.flip, c.suit.pair⟩, r⟩).maskIndex + 3 = c.maskIndex := by
  rcases c with ⟨⟨col, p⟩, rk⟩
  have hp : p = false := hpair
  subst hp
  have hptr : r.toIdx + 1 = rk.toIdx := (rank_pred_iff _ _).mp hpred
  cases col with
  | red =>
      simp only [Card.maskIndex, Card.flipSuit, Suit.flipPair, Suit.code,
        Color.flip, Bool.not_false]
      refine ⟨?_, ?_⟩ <;> omega
  | black =>
      simp only [Card.maskIndex, Card.flipSuit, Suit.flipPair, Suit.code,
        Color.flip, Bool.not_false]
      refine ⟨?_, ?_⟩ <;> omega

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

/-! ### The decode (the owed lemma's plan, steps 2 and 3) -/

/-- The read lemma (plan step 2): the owner card reads its own bit —
`maskOf f` at `d.maskIndex` is `f d`, by `maskIndex`'s injectivity
(the position owner's uniqueness). -/
theorem maskOf_maskIndex (f : Card → Bool) (d : Card) :
    maskOf f d.maskIndex = f d := by
  unfold maskOf
  have hmem : d ∈ Card.universe := Card.mem_universe d
  cases hf : f d with
  | true =>
      have hw : (Card.universe.any fun e => (e.maskIndex == d.maskIndex) && f e) = true :=
        List.any_eq_true.mpr ⟨d, hmem, by
          rw [hf, Bool.and_true]
          exact decide_eq_true_iff.mpr rfl⟩
      exact hw
  | false =>
      cases hany : Card.universe.any fun e => (e.maskIndex == d.maskIndex) && f e with
      | true =>
          obtain ⟨e, _, he⟩ := List.any_eq_true.mp hany
          rw [Bool.and_eq_true] at he
          have hed : e = d := Card.maskIndex_inj (decide_eq_true_iff.mp he.1)
          rw [hed, hf] at he
          exact absurd he.2 (by simp)
      | false => rfl

/-- The ALT gate opens on even positions below the truncation line
(the pair-`false` representatives). -/
theorem alt_of_even {i : Nat} (hmod : i % 2 = 0) (hlt : i < 64) :
    alt i = true :=
  decide_eq_true_iff.mpr ⟨hmod, hlt⟩

/-- The ALT gate is shut on odd positions — the pair-`true` twins
carry no representative bit of their own. -/
theorem alt_of_odd {i : Nat} (hmod : i % 2 = 1) :
    alt i = false := by
  have hn : ¬(i % 2 = 0 ∧ i < 64) := by
    intro hc
    omega
  exact decide_eq_false_iff_not.mpr hn

/-- `bottomMask`'s pre-spread word, zeta-spelled without the `let`s so
the per-position reads unfold in one `simp only`: bit `i` is the §8.1
parity algebra masked by ALT (the `free` cut, the `>>> 1` twin reads,
the `<<< 4` under-pair reads).  Definitional; exists to be unfolded. -/
private def coreWord (v l : Nat → Bool) : Nat → Bool :=
  fun i =>
    ((((v i ^^ shr1 v i) ^^
        (if 4 ≤ i then (v (i - 4) && !l (i - 4)) ^^ (v (i - 3) && !l (i - 3))
         else false))
      || !(if 4 ≤ i then (v (i - 4) && !l (i - 4)) || (v (i - 3) && !l (i - 3))
           else false))
      && (v i || shr1 v i)
      && alt i)

/-- The bridge: the engine word is the ALT-masked core under the
`× 0b11` twin spread (definitional — the `let` zeta). -/
theorem bottomMask_eq (v l : Nat → Bool) (i : Nat) :
    bottomMask v l i = spread (coreWord v l) i := rfl

/-- The spread read at an even position ignores the odd position
beneath it: the ALT cut inside the core has shut the twin bit, so the
position's own bit is everything (`x * 0b11` only ever spreads UP
into the twin — plan step 2's `y (i-1)` arm). -/
private theorem spread_even {v l : Nat → Bool} {i : Nat}
    (hmod : i % 2 = 0) (hlt : i < 64) :
    spread (coreWord v l) i = coreWord v l i := by
  simp only [spread]
  rw [if_pos hlt]
  rcases Nat.lt_or_ge i 1 with h01 | h1
  · rw [if_neg (by omega : ¬(1 ≤ i)), Bool.or_false]
  · rw [if_pos h1]
    have hkill : coreWord v l (i - 1) = false := by
      have hOdd : (i - 1) % 2 = 1 := by omega
      simp only [coreWord, alt_of_odd hOdd, Bool.and_false]
    rw [hkill, Bool.or_false]

/-- The §8.1 skeleton identity (plan step 3): the engine's parity form
and the formula's blocked-unders form read the same four bits — the
xor chain re-associates onto the two arms. -/
private theorem bm_skeleton (a b f1 f2 : Bool) :
    ((((a ^^ b) ^^ (f1 ^^ f2)) || !(f1 || f2)) && (a || b)) =
      ((a || b) && (!(f1) && !(f2) || (((a ^^ b) ^^ f1) ^^ f2))) := by
  cases a <;> cases b <;> cases f1 <;> cases f2 <;> rfl

/-- The decode at the pair-`false` (ALT) representative: the engine
word at the representative's own position reads §8.1's formula of
that card — plan step 2's reads (self, twin, twin's under-pair, the
ace underflow) and step 3's skeleton finish, all at `P`. -/
private theorem bm_rep {vis locked : Card → Bool} {P : Card}
    (hpair : P.suit.pair = false) :
    bottomMask (maskOf vis) (maskOf locked) P.maskIndex = true ↔
      Card.movableOf vis locked P = true := by
  -- plan step 1: the layout facts at the representative
  have hlt : P.maskIndex < 64 := Card.maskIndex_lt64 P
  have hmod : P.maskIndex % 2 = 0 := Card.even_maskIndex hpair
  have hAlt : alt P.maskIndex = true := alt_of_even hmod hlt
  have hTwin : P.flipSuit.maskIndex = P.maskIndex + 1 :=
    Card.maskIndex_flip_pair_false hpair
  -- plan step 2: the self and twin reads (the word reads `locked`
  -- only inside the under-pair `free` cut — never at the positions)
  have hRself : maskOf vis P.maskIndex = vis P := maskOf_maskIndex vis P
  have hRtwin : maskOf vis (P.maskIndex + 1) = vis P.flipSuit := by
    rw [← hTwin]; exact maskOf_maskIndex vis P.flipSuit
  rw [bottomMask_eq, spread_even hmod hlt]
  cases hpred : P.rank.pred with
  | none =>
      -- aces: the `<<< 4` arms read below the word — underflow to zero
      have hrk : P.rank = Rank.ace := by
        cases hrk2 : P.rank <;> simp_all [Rank.pred]
      have h4n : ¬(4 ≤ P.maskIndex) := by
        have := Card.maskIndex_lt4 hrk
        omega
      simp only [coreWord, shr1, if_neg h4n, hAlt, Bool.xor_false, Bool.not_false,
        Bool.or_true, Bool.true_and, Bool.and_true]
      rw [hRself, hRtwin]
      rw [Card.movableOf_ace vis locked hrk]
      exact Bool.or_eq_true_iff
  | some ρ =>
      -- the under-pair reads land exactly on the two sitters
      have h4 : 4 ≤ P.maskIndex := by
        have hp : ρ.toIdx + 1 = P.rank.toIdx := (rank_pred_iff _ _).mp hpred
        refine Card.maskIndex_ge4 (fun heq => ?_)
        have hlt := Rank.toIdx_lt ρ
        rw [heq] at hp
        simp only [Rank.toIdx] at hp
        omega
      obtain ⟨hpos1, hpos2⟩ := Card.maskIndex_underPair_positions hpair hpred
      have hu1 : P.maskIndex - 4
          = (⟨⟨P.suit.color.flip, P.suit.pair⟩, ρ⟩ : Card).maskIndex := by omega
      have hu2 : P.maskIndex - 3
          = (Card.flipSuit ⟨⟨P.suit.color.flip, P.suit.pair⟩, ρ⟩ : Card).maskIndex := by omega
      have hRu1 : maskOf vis (P.maskIndex - 4)
          = vis ⟨⟨P.suit.color.flip, P.suit.pair⟩, ρ⟩ := by
        rw [hu1]; exact maskOf_maskIndex vis _
      have hLu1 : maskOf locked (P.maskIndex - 4)
          = locked ⟨⟨P.suit.color.flip, P.suit.pair⟩, ρ⟩ := by
        rw [hu1]; exact maskOf_maskIndex locked _
      have hRu2 : maskOf vis (P.maskIndex - 3)
          = vis (Card.flipSuit ⟨⟨P.suit.color.flip, P.suit.pair⟩, ρ⟩) := by
        rw [hu2]; exact maskOf_maskIndex vis _
      have hLu2 : maskOf locked (P.maskIndex - 3)
          = locked (Card.flipSuit ⟨⟨P.suit.color.flip, P.suit.pair⟩, ρ⟩) := by
        rw [hu2]; exact maskOf_maskIndex locked _
      simp only [coreWord, shr1, if_pos h4, hAlt, Bool.and_true]
      rw [hRself, hRtwin, hRu1, hLu1, hRu2, hLu2]
      have hsk := bm_skeleton (vis P) (vis P.flipSuit)
        (vis ⟨⟨P.suit.color.flip, P.suit.pair⟩, ρ⟩
          && !locked ⟨⟨P.suit.color.flip, P.suit.pair⟩, ρ⟩)
        (vis (Card.flipSuit ⟨⟨P.suit.color.flip, P.suit.pair⟩, ρ⟩)
          && !locked (Card.flipSuit ⟨⟨P.suit.color.flip, P.suit.pair⟩, ρ⟩))
      -- both sides now read the same four bits — the skeleton closes
      simp only [Card.movableOf, Card.underPair_of_pred hpred]
      rw [hsk]

/-- **The engine equivalence (§8.7), PROVEN (2026-10-05)**: the
shipped mask arithmetic and §8.1's formula agree, per card, at every
`(vis, locked)` grid — the Lean form of `bm_algebra_matches` (the
Rust binding instrument, 2,000 random masks × 52 cards) is now
established: the §8.7 standing caveat is discharged, the mask layer's
parity debt paid.  Axiom-clean `[propext, Quot.sound]`.

The proof is the docstring's decode plan verbatim.  Step 1, layout:
`maskIndex` is injective (`Card.maskIndex_inj`), bit 0 is the suit's
pair (`Card.even_maskIndex`), the twin is the adjacent position
(`Card.maskIndex_flip_pair_false/_true`), aces below the `<<< 4`
line (`Card.maskIndex_lt4`), everything else at or above it
(`Card.maskIndex_ge4`), and the `± 4` block arithmetic lands the
under-pair reads exactly on the two sitters
(`Card.maskIndex_underPair_positions`).  Step 2, reads: the owner
uniqueness gives `maskOf_maskIndex`; `spread_even` kills the
position's `y (i-1)` twin arm by the ALT parity (and `if 4 ≤ i`
decides the underflow: aces read zero and the `¬free ∧ ¬free` arm
fires vacuously, matching `underPair = none`).  Step 3, finish:
`bm_skeleton` — the identical §8.1 skeleton over the four read bits,
16-case Bool exhaustion — with the odd (pair-`true`) representative
routed through `movableOf_flipSuit`.  No u64 truncation event ever
fires: all touched positions are below 52 + 4 < 64. -/
theorem bottomMask_matches_movableOf (vis locked : Card → Bool) (c : Card) :
    bottomMask (maskOf vis) (maskOf locked) (c.maskIndex) = true ↔
      Card.movableOf vis locked c = true := by
  cases hpair : c.suit.pair with
  | false => exact bm_rep hpair
  | true =>
      -- the pair-true twin: the word bit belongs to the ALT
      -- representative `c.flipSuit` — route through it
      have hpF : c.flipSuit.suit.pair = false := by
        simp [Card.flipSuit, Suit.flipPair, hpair]
      have hf : c.flipSuit.maskIndex = c.maskIndex - 1 :=
        Card.maskIndex_flip_pair_true hpair
      have h := bm_rep (vis := vis) (locked := locked) (P := c.flipSuit) hpF
      rw [bottomMask_eq, spread_even (Card.even_maskIndex hpF)
        (Card.maskIndex_lt64 c.flipSuit)] at h
      rw [← Card.movableOf_flipSuit vis locked c]
      have h1 : 1 ≤ c.maskIndex := by
        have := Card.odd_maskIndex hpair
        omega
      simp only [bottomMask_eq, spread, if_pos (Card.maskIndex_lt64 c), if_pos h1,
        coreWord, alt_of_odd (Card.odd_maskIndex hpair), Bool.and_false, Bool.false_or]
      rw [← hf]
      exact h

end Mask
