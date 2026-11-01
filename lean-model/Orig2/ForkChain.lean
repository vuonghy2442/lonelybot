import Orig2.ForkCrossSuitPure
import Orig2.ForkReadBracket
import Orig2.ForkEmptyTail
import Orig2.ForkPinAt

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-!
# Orig2/ForkChain — the cover obligation and the cover chain

READ-ONLY scratch card (no source edits, no commit).  Zero `sorry`, zero
`Classical.choice`, zero `native_decide`; battery at the tail.

## The problem

`CrossSuit.CrossSuitFreeCorridorResidual` (`Orig2/ForkCrossSuitPure.lean:417`) asks:

```text
ρ = (pre ++ raise c :: γ) ++ pull d b :: tail,   c.suit ≠ d.suit,
γ free,  u, v SSaturated and WF,  ρ shortest          ⟹  False.
```

The state immediately after the pull is NOT saturated: the pulled card `d` is
vanilla-raisable there (`ValleyStep.pull_card_canRaise`, re-exported as
`Bridge.pull_landing_raisable`, `Orig2/ForkBridge.lean:129`).  Since `v` is
saturated, the **tail** must block `d`.

## What this card proves

* **§1 `first_blocking_letter`** — a play that starts with `z` raisable and ends
  with `z` blocked has a *first* blocking letter, with the witness play split
  around it and the suffix play retained (`ShufflePlayW Z s2 v`).

* **§2 `blocking_letter_shape`** — the first blocking letter is exactly one of

  1. `raise z` (a raise in `z`'s own suit, hence `z` itself);
  2. a **pull in `z`'s suit** (`foundToTab e b` with `e.suit = z.suit`) — the
     foundation top of `z`'s column, i.e. the card directly below `z`;
  3. a **pull landing on `z`** (`foundToTab e (inr z)`);
  4. a **slide landing on `z`** (`tabToTab x (inr z)`) — the *cover*.

  Proof: `R12.canRaise_survives_read` makes every `ReadOK z` letter harmless,
  and `EmptyTail.canRaise_survives_own_slide` removes the self-slide `z`.
  This is THE COVER OBLIGATION, unconditional (no pull-freeness).

* **§3 `corridor_tail_blocker`** — the corridor instantiation: at the pull
  landing `B` of a free cross-suit corridor into a saturated endpoint, the tail
  carries such a blocking letter for `d`.  So the corridor's tail must carry a
  raise of `d`, a pull in `d`'s suit, a pull landing on `d`, or a cover slide on
  `d`.

* **§4 `pullFree_raise_or_cover`** — the sharpening used by the `TailHead`
  regime: if the tail is pull-free the pull shapes vanish
  (`EmptyTail.raise_or_slide_onto`), leaving exactly *raise of `d`* or *cover
  slide on `d`*.

* **§5 the cover geometry** — a cover of `z` is a card of rank `z.rank − 1`
  whose suit has the colour *opposite* to `z.suit` (`slide_onto_rank`,
  `cover_suit_ne`, `cover_suit_not_twin`).  So a cover NEVER stays in `z`'s
  column or its twin: the chain always jumps to an opposite-coloured column.
  The two pull shapes give the same one-rank descent
  (`pull_onto_rank`, `pull_below_rank`) and the pulled card is raisable at the
  landing (`pull_landing_of_pull`).

* **§6 `chain_exists`** — THE CHAIN.  By strong recursion on `z.rank.toIdx`:
  from `CanRaise B z` into a saturated endpoint, the tail carries a chain card
  `z'` with `z'.rank.toIdx ≤ z.rank.toIdx`, raisable at some state and blocked
  by either `raise z'` or a cover slide of `z'` whose mover is NOT raisable at
  the slide's image.  Every non-raise branch descends the rank by exactly one,
  so the recursion is well founded and the chain length is at most
  `z.rank.toIdx + 1 ≤ 13`.

* **§7 `CoverChainResidual`** — the exact residual: the chain never terminates
  at `raise z'` and never stalls at a non-raisable cover mover.  Proved:
  `CoverChainResidual → CrossSuitFreeCorridorResidual`
  (`freeCorridor_of_coverChain`).

## What is NOT done

The residual is not refuted.  Its two clauses are exactly the two ways the
chain can stop: the same-card relocation (`raise z'` after `z'` was pulled,
owned by the campaign's `PullKit`/`Relocate` machinery) and the opposite-colour
cover stall.  See `Temp/Chain_Report.md` §5 for why the stall cannot be
avoided by rank counting alone.
-/

namespace Chain

open CrossSuit

/-- **`CanRaise` IS DECIDABLE** (through the campaign's Bool probe
`PinAt.canRaiseBL`, `Orig2/ForkPinAt.lean:278`).  This keeps every `by_cases` on
a raisability licence constructive — no `Classical.choice`. -/
instance decidableCanRaise (st : State) (c : Card) : Decidable (CanRaise st c) :=
  decidable_of_iff (PinAt.canRaiseBL st c = true) PinAt.canRaiseBL_true_iff

/-!
## §1. The first blocking letter
-/

/-- **A PLAY THAT BLOCKS `z` HAS A FIRST BLOCKING LETTER.**  The play is split
around the first letter at which `CanRaise · z` fails; the prefix and the suffix
are both witness plays. -/
theorem first_blocking_letter {B v : State} {τ : List Move}
    (hplay : ShufflePlayW B τ v) :
    ∀ {z : Card}, CanRaise B z → ¬ CanRaise v z →
      ∃ (s1 s2 : List Move) (A Z : State) (m : Move),
        τ = s1 ++ m :: s2 ∧ ShufflePlayW B s1 A ∧ CanRaise A z ∧
        reversibleAtW A m ∧ State.step A m = some Z ∧ ShufflePlayW Z s2 v ∧
        ¬ CanRaise Z z := by
  induction hplay with
  | nil st =>
      intro z hcan hblock
      exact absurd hcan hblock
  | @cons st s₁ W m ρ hrev hstep hrest ih =>
      intro z hcan hblock
      by_cases h1 : CanRaise s₁ z
      · obtain ⟨s1, s2, A, Z, m', heq, hp', hc', hr', hs', hp2', hb'⟩ := ih h1 hblock
        exact ⟨m :: s1, s2, A, Z, m', by rw [heq]; rfl,
          Walk.cons hrev hstep hp', hc', hr', hs', hp2', hb'⟩
      · exact ⟨[], ρ, st, s₁, m, rfl, Walk.nil st, hcan, hrev, hstep, hrest, h1⟩

/-!
## §2. The shape of the blocking letter — the cover obligation
-/

/-- A blocking letter is not read-safe for `z`. -/
theorem not_readOK_of_block {A Z : State} {m : Move} {z : Card}
    (hA : A.WF) (hrev : reversibleAtW A m) (hstep : State.step A m = some Z)
    (hcan : CanRaise A z) (hblock : ¬ CanRaise Z z) : ¬ R12.ReadOK z m :=
  fun hr => hblock (R12.canRaise_survives_read hA hstep hrev hr hcan)

/-- **THE COVER OBLIGATION.**  A first blocking letter for `z` is one of:

1. `raise z`;
2. a pull in `z`'s suit (of the foundation top below `z`);
3. a pull landing on `z`;
4. a slide landing on `z` (a cover). -/
theorem blocking_letter_shape {A Z : State} {m : Move} {z : Card}
    (hA : A.WF) (hrev : reversibleAtW A m) (hstep : State.step A m = some Z)
    (hcan : CanRaise A z) (hblock : ¬ CanRaise Z z) :
    m = Move.tabToFound z ∨
      (∃ (c : Card) (b : Base), m = Move.foundToTab c b ∧
        (c.suit = z.suit ∨ b = Sum.inr z)) ∨
      (∃ x : Card, m = Move.tabToTab x (Sum.inr z)) := by
  have hnotread : ¬ R12.ReadOK z m := not_readOK_of_block hA hrev hstep hcan hblock
  cases m with
  | draw => exact absurd trivial hnotread
  | wasteToFound c => exact absurd hrev (wasteToFound_not_reversibleAtW A c)
  | wasteToTab c b => exact absurd hrev (wasteToTab_not_reversibleAtW A c b)
  | tabToFound w =>
      have hsu : w.suit = z.suit := by
        by_cases h : w.suit = z.suit
        · exact h
        · exact absurd h hnotread
      have hwcan : CanRaise A w := Bridge.canRaise_of_reversible_raise hA hrev
      have hwz : w = z := SlideFwd.readSafe_raise_of_canRaise_same_suit hwcan hcan hsu
      exact Or.inl (by rw [hwz])
  | foundToTab c b =>
      by_cases h1 : c.suit = z.suit
      · exact Or.inr (Or.inl ⟨c, b, rfl, Or.inl h1⟩)
      · by_cases h2 : b = Sum.inr z
        · exact Or.inr (Or.inl ⟨c, b, rfl, Or.inr h2⟩)
        · exact absurd (show R12.ReadOK z (Move.foundToTab c b) from ⟨h1, h2⟩) hnotread
  | tabToTab c b =>
      by_cases h1 : c = z
      · exact absurd (h1 ▸ EmptyTail.canRaise_survives_own_slide hA hstep hrev
          (h1.symm ▸ hcan)) hblock
      · by_cases h2 : b = Sum.inr z
        · exact Or.inr (Or.inr ⟨c, by rw [h2]⟩)
        · exact absurd (show R12.ReadOK z (Move.tabToTab c b) from ⟨h1, h2⟩) hnotread

/-!
## §3. The corridor instantiation
-/

/-- **THE CORRIDOR'S TAIL BLOCKS THE PULLED CARD.**  Split a free cross-suit
corridor at its pull: the landing `B` has `d` raisable, while the saturated
endpoint has `d` blocked; hence the tail carries a first blocking letter for
`d`, and that letter is one of §2's four shapes. -/
theorem corridor_tail_blocker
    {u v : State} {pre γ tail : List Move} {c d : Card} {b : Base}
    (hplay : ShufflePlayW u
      ((pre ++ Move.tabToFound c :: γ) ++ Move.foundToTab d b :: tail) v)
    (huwf : u.WF) (hv : SSaturated v) :
    ∃ (B : State) (s1 s2 : List Move) (A Z : State) (m : Move),
      ShufflePlayW B tail v ∧ B.WF ∧ CanRaise B d ∧
      tail = s1 ++ m :: s2 ∧ ShufflePlayW B s1 A ∧ CanRaise A d ∧
      reversibleAtW A m ∧ State.step A m = some Z ∧ ¬ CanRaise Z d ∧
      (m = Move.tabToFound d ∨
        (∃ (c' : Card) (b' : Base), m = Move.foundToTab c' b' ∧
          (c'.suit = d.suit ∨ b' = Sum.inr d)) ∨
        (∃ x : Card, m = Move.tabToTab x (Sum.inr d))) := by
  obtain ⟨P, hpre, hrest⟩ := ValleyElim.ShufflePlayW_split hplay
    (pre ++ Move.tabToFound c :: γ) (Move.foundToTab d b :: tail) rfl
  obtain ⟨B, -, hstepP, htail⟩ := Bubble.walk_cons_inv hrest
  have hP : P.WF := SatDifferCensus.ShufflePlayW.wf_end hpre huwf
  have hB : B.WF := step_wf hP hstepP
  have hcanB : CanRaise B d := ValleyStep.pull_card_canRaise hP hstepP
  have hblock : ¬ CanRaise v d := fun h => hv d (CanRaiseS.now d h)
  obtain ⟨s1, s2, A, Z, m, heq, hp1, hcanA, hrevA, hstepA, -, hblockA⟩ :=
    first_blocking_letter htail hcanB hblock
  have hAwf : A.WF := SatDifferCensus.ShufflePlayW.wf_end hp1 hB
  exact ⟨B, s1, s2, A, Z, m, htail, hB, hcanB, heq, hp1, hcanA, hrevA, hstepA,
    hblockA, blocking_letter_shape hAwf hrevA hstepA hcanA hblockA⟩

/-!
## §4. The pull-free sharpening: raise `d` or cover `d`
-/

/-- **IN A PULL-FREE TAIL THE COVER OBLIGATION IS TWO-WAY.**  Since
`EmptyTail.raise_or_slide_onto` classifies a pull-free witness leg from a state
where `z` is raisable into `RaisePartner ∨ TailCoverSlide ∨ CanRaise end`, and
saturation kills the third, the corridor's pull-free tail either raises `d` or
slides a card onto `d`. -/
theorem pullFree_raise_or_cover {B v : State} {tail : List Move} {d : Card}
    (hB : B.WF) (hv : SSaturated v) (hcan : CanRaise B d)
    (hplay : ShufflePlayW B tail v) (hpf : ∀ m ∈ tail, ¬ Bubble.IsPull m) :
    (∃ (s1 s2 : List Move), tail = s1 ++ Move.tabToFound d :: s2) ∨
      EmptyTail.TailCoverSlide B v tail d := by
  rcases EmptyTail.raise_or_slide_onto hplay hB hcan hpf with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · exact absurd (CanRaiseS.now d h) (hv d)

/-!
## §5. The cover geometry: rank descent and the cross-suit jump
-/

/-- **A COVER OF `z` IS ONE RANK BELOW `z`, IN AN OPPOSITE-COLOURED SUIT.** -/
theorem slide_onto_rank {A Z : State} {x z : Card}
    (hstep : State.step A (Move.tabToTab x (Sum.inr z)) = some Z) :
    x.rank.toIdx + 1 = z.rank.toIdx ∧ x.suit.color ≠ z.suit.color := by
  obtain ⟨a, -, hcp, -, -⟩ := step_tabToTab_inv hstep
  obtain ⟨k, -, hfit⟩ := canPlace_inr hcp
  exact (canSitOn_eq x z).mp hfit

/-- **A COVER NEVER LIVES IN `z`'s OWN SUIT.** -/
theorem cover_suit_ne {A Z : State} {x z : Card}
    (hstep : State.step A (Move.tabToTab x (Sum.inr z)) = some Z) :
    x.suit ≠ z.suit := by
  have h := (slide_onto_rank hstep).2
  intro hse
  rw [hse] at h
  exact h rfl

/-- **A COVER NEVER LIVES IN `z.twin`'s SUIT EITHER** (the twin has `z`'s colour).
So the cover jumps to a column of the opposite colour — for a cross-suit
corridor in suits `c ≠ d`, a cover of `d` is in a suit distinct from `d.suit`
and, when `c.suit ≠ d.suit.twin`, distinct from `c.suit` too. -/
theorem cover_suit_not_twin {A Z : State} {x z : Card}
    (hstep : State.step A (Move.tabToTab x (Sum.inr z)) = some Z) :
    x.suit ≠ z.suit.twin := by
  have h := (slide_onto_rank hstep).2
  intro hse
  rw [hse, Suit.color_twin] at h
  exact h rfl

/-- **THE COVER IS NEITHER `z` NOR `z.twin`.**  It is one rank below `z`, so it
cannot be `z` or `z`'s twin: the cover is a genuinely different card. -/
theorem cover_card_ne {A Z : State} {x z : Card}
    (hstep : State.step A (Move.tabToTab x (Sum.inr z)) = some Z) :
    x ≠ z ∧ x ≠ z.twin := by
  obtain ⟨hr, -⟩ := slide_onto_rank hstep
  constructor
  · intro h; rw [h] at hr; omega
  · intro h; rw [h, Card.twin_rank] at hr; omega

/-- **THE CORRIDOR'S PULL-FREE COVER OBLIGATION, AS ONE ROW.**  At the pull
landing `B` of a free cross-suit corridor whose tail is pull-free, the tail
either raises `d` or slides a card onto `d`. -/
theorem corridor_pullFree_raise_or_cover
    {u v : State} {pre γ tail : List Move} {c d : Card} {b : Base}
    (hplay : ShufflePlayW u
      ((pre ++ Move.tabToFound c :: γ) ++ Move.foundToTab d b :: tail) v)
    (huwf : u.WF) (hv : SSaturated v)
    (hpf : ∀ m ∈ tail, ¬ Bubble.IsPull m) :
    ∃ B : State, ShufflePlayW B tail v ∧ B.WF ∧ CanRaise B d ∧
      ((∃ (s1 s2 : List Move), tail = s1 ++ Move.tabToFound d :: s2) ∨
        EmptyTail.TailCoverSlide B v tail d) := by
  obtain ⟨P, hpre, hrest⟩ := ValleyElim.ShufflePlayW_split hplay
    (pre ++ Move.tabToFound c :: γ) (Move.foundToTab d b :: tail) rfl
  obtain ⟨B, -, hstepP, htail⟩ := Bubble.walk_cons_inv hrest
  have hP : P.WF := SatDifferCensus.ShufflePlayW.wf_end hpre huwf
  have hB : B.WF := step_wf hP hstepP
  have hcanB : CanRaise B d := ValleyStep.pull_card_canRaise hP hstepP
  exact ⟨B, htail, hB, hcanB,
    pullFree_raise_or_cover hB hv hcanB htail hpf⟩

/-- **A PULL LANDING ON `z` IS ONE RANK BELOW `z`.** -/
theorem pull_onto_rank {A Z : State} {e z : Card}
    (hstep : State.step A (Move.foundToTab e (Sum.inr z)) = some Z) :
    e.rank.toIdx + 1 = z.rank.toIdx ∧ e.suit.color ≠ z.suit.color := by
  obtain ⟨c', -, -, hcp, -⟩ := step_foundToTab_inv hstep
  obtain ⟨k, -, hfit⟩ := canPlace_inr hcp
  exact (canSitOn_eq e z).mp hfit

/-- **A PULL IN `z`'s SUIT PULLS THE CARD DIRECTLY BELOW `z`.** -/
theorem pull_below_rank {A Z : State} {e z : Card} {b : Base}
    (hA : A.WF) (hstep : State.step A (Move.foundToTab e b) = some Z)
    (hnext : A.nextUp z = true) (hsu : e.suit = z.suit) :
    e.rank.toIdx + 1 = z.rank.toIdx := by
  obtain ⟨c', htop, hc', -, -⟩ := step_foundToTab_inv hstep
  rw [hc'] at htop
  have h1 : e.rank.toIdx + 1 = rungAt A e.suit :=
    SatDifferCensus.foundTop_rank_succ hA htop
  have h2 : z.rank.toIdx = rungAt A z.suit := by
    simpa [State.nextUp, State.foundHeight, rungAt] using of_decide_eq_true hnext
  rw [hsu] at h1
  omega

/-- **THE PULLED CARD IS RAISABLE AT ITS LANDING** (re-exported for the chain). -/
theorem pull_landing_of_pull {A Z : State} {e : Card} {b : Base}
    (hA : A.WF) (hstep : State.step A (Move.foundToTab e b) = some Z) :
    CanRaise Z e :=
  ValleyStep.pull_card_canRaise hA hstep

/-!
## §6. The chain — strong recursion on the rank
-/

/-- **THE CHAIN EXISTS.**  From `CanRaise B z` into a saturated endpoint, the
tail carries a chain card `z'` of rank at most `z`'s rank, raisable at some
state `A` and blocked at `A`'s successor `Z` by either

* `raise z'` itself (the same-card relocation), or
* a slide `x → z'` landing on `z'` whose mover `x` is **not** raisable at the
  slide's image `Z` (the chain stall).

Every other branch of §2 produces a *fresh raisable card one rank lower*, so the
recursion descends `z.rank.toIdx`, hence terminates in at most 13 steps. -/
theorem chain_exists_aux (k : Nat) :
    ∀ (B v : State) (tail : List Move) (z : Card),
      z.rank.toIdx = k → B.WF → SSaturated v → CanRaise B z →
      ShufflePlayW B tail v →
      ∃ (z' : Card) (s1 s2 : List Move) (A Z : State) (m : Move),
        z'.rank.toIdx ≤ k ∧ tail = s1 ++ m :: s2 ∧ ShufflePlayW B s1 A ∧
        CanRaise A z' ∧ State.step A m = some Z ∧ ¬ CanRaise Z z' ∧
        (m = Move.tabToFound z' ∨
          ∃ x : Card, m = Move.tabToTab x (Sum.inr z') ∧ ¬ CanRaise Z x) := by
  induction k using Nat.strongRecOn with
  | ind k ih =>
      intro B v tail z hk hB hv hcan hplay
      have hblock : ¬ CanRaise v z := fun h => hv z (CanRaiseS.now z h)
      obtain ⟨s1, s2, A, Z, m, heq, hp1, hcanA, hrevA, hstepA, hp2, hblockA⟩ :=
        first_blocking_letter hplay hcan hblock
      have hAwf : A.WF := SatDifferCensus.ShufflePlayW.wf_end hp1 hB
      have hZwf : Z.WF := step_wf hAwf hstepA
      rcases blocking_letter_shape hAwf hrevA hstepA hcanA hblockA with
        hraise | ⟨e, b', hm, hcase⟩ | ⟨x, hm⟩
      · -- a raise of `z` itself
        exact ⟨z, s1, s2, A, Z, m, by omega, heq, hp1, hcanA, hstepA, hblockA,
          Or.inl hraise⟩
      · -- a pull: substitute the shape
        subst hm
        rcases hcase with hsu | hbz
        · -- a pull in `z`'s suit: `e` is the predecessor and is raisable at `Z`
          have hrank : e.rank.toIdx + 1 = z.rank.toIdx :=
            pull_below_rank hAwf hstepA hcanA.1 hsu
          have hcanZ : CanRaise Z e := ValleyStep.pull_card_canRaise hAwf hstepA
          have hlt : e.rank.toIdx < k := by omega
          obtain ⟨z', s1', s2', A', Z', m', hle, heq', hp1', hcanA', hstepA',
            hblockA', hshape'⟩ :=
            ih e.rank.toIdx hlt Z v s2 e rfl hZwf hv hcanZ hp2
          refine ⟨z', s1 ++ Move.foundToTab e b' :: s1', s2', A', Z', m',
            by omega, ?_, ?_, hcanA', hstepA', hblockA', hshape'⟩
          · rw [heq, heq']
            simp only [List.append_assoc, List.cons_append]
          · exact ShufflePlayW_append hp1 (Walk.cons hrevA hstepA hp1')
        · -- a pull landing on `z`: `e` is one rank below `z`, raisable at `Z`
          subst hbz
          have hrank : e.rank.toIdx + 1 = z.rank.toIdx :=
            (pull_onto_rank hstepA).1
          have hcanZ : CanRaise Z e := ValleyStep.pull_card_canRaise hAwf hstepA
          have hlt : e.rank.toIdx < k := by omega
          obtain ⟨z', s1', s2', A', Z', m', hle, heq', hp1', hcanA', hstepA',
            hblockA', hshape'⟩ :=
            ih e.rank.toIdx hlt Z v s2 e rfl hZwf hv hcanZ hp2
          refine ⟨z', s1 ++ Move.foundToTab e (Sum.inr z) :: s1', s2', A', Z', m',
            by omega, ?_, ?_, hcanA', hstepA', hblockA', hshape'⟩
          · rw [heq, heq']
            simp only [List.append_assoc, List.cons_append]
          · exact ShufflePlayW_append hp1 (Walk.cons hrevA hstepA hp1')
      · -- a cover slide of `z`
        have hstepX : State.step A (Move.tabToTab x (Sum.inr z)) = some Z := by
          rw [← hm]; exact hstepA
        have hrank : x.rank.toIdx + 1 = z.rank.toIdx := (slide_onto_rank hstepX).1
        by_cases hxcan : CanRaise Z x
        · have hlt : x.rank.toIdx < k := by omega
          obtain ⟨z', s1', s2', A', Z', m', hle, heq', hp1', hcanA', hstepA',
            hblockA', hshape'⟩ :=
            ih x.rank.toIdx hlt Z v s2 x rfl hZwf hv hxcan hp2
          refine ⟨z', s1 ++ Move.tabToTab x (Sum.inr z) :: s1', s2', A', Z', m',
            by omega, ?_, ?_, hcanA', hstepA', hblockA', hshape'⟩
          · rw [heq, hm, heq']
            simp only [List.append_assoc, List.cons_append]
          · refine ShufflePlayW_append hp1 (Walk.cons ?_ hstepX hp1')
            rw [← hm]; exact hrevA
        · -- the chain stalls here
          exact ⟨z, s1, s2, A, Z, m, by omega, heq, hp1, hcanA, hstepA, hblockA,
            Or.inr ⟨x, hm, hxcan⟩⟩

/-- **THE CHAIN EXISTENCE THEOREM.** -/
theorem chain_exists {B v : State} {tail : List Move} {z : Card}
    (hB : B.WF) (hv : SSaturated v) (hcan : CanRaise B z)
    (hplay : ShufflePlayW B tail v) :
    ∃ (z' : Card) (s1 s2 : List Move) (A Z : State) (m : Move),
      z'.rank.toIdx ≤ z.rank.toIdx ∧ tail = s1 ++ m :: s2 ∧
      ShufflePlayW B s1 A ∧ CanRaise A z' ∧ State.step A m = some Z ∧
      ¬ CanRaise Z z' ∧
      (m = Move.tabToFound z' ∨
        ∃ x : Card, m = Move.tabToTab x (Sum.inr z') ∧ ¬ CanRaise Z x) :=
  chain_exists_aux z.rank.toIdx B v tail z rfl hB hv hcan hplay

/-- **THE CHAIN'S RANK IS BOUNDED BY 12.**  Every chain card has rank index at
most the starting card's, and there are at most 13 of them. -/
theorem chain_rank_lt_thirteen {B v : State} {tail : List Move} {z z' : Card}
    (hB : B.WF) (hv : SSaturated v) (hcan : CanRaise B z)
    (hplay : ShufflePlayW B tail v) (h : z'.rank.toIdx ≤ z.rank.toIdx) :
    z'.rank.toIdx < 13 :=
  Nat.lt_of_le_of_lt h (Rank.toIdx_lt z.rank)

/-!
## §7. The residual, and the reduction
-/

/-- **`CoverChainResidual`** — THE EXACT RESIDUAL OF THE COVER CHAIN.  In the
tail of a play from a state where `d` is raisable into a saturated endpoint, no
chain card `z'` (of rank at most `d`'s) is blocked by

* a raise of `z'`, or
* a slide `x → z'` whose mover `x` is not raisable at the slide's image.

This is a `∀` over the tail: it forbids exactly the two endpoints of the chain
descending from `d`.  The first clause is the same-card relocation lane
(`PullKit`/`Relocate` own it: `z'` was pulled and is raised straight back); the
second is the opposite-coloured cover stall. -/
def CoverChainResidual : Prop :=
  ∀ (B v : State) (tail : List Move) (d : Card),
    B.WF → SSaturated v → CanRaise B d → ShufflePlayW B tail v →
    ∀ (z' : Card) (s1 s2 : List Move) (A Z : State) (m : Move),
      z'.rank.toIdx ≤ d.rank.toIdx →
      tail = s1 ++ m :: s2 → ShufflePlayW B s1 A → CanRaise A z' →
      State.step A m = some Z → ¬ CanRaise Z z' →
      (m = Move.tabToFound z' ∨
        ∃ x : Card, m = Move.tabToTab x (Sum.inr z') ∧ ¬ CanRaise Z x) → False

/-- **`NoChainRaise`** — the first endpoint of the chain: no chain card of rank
at most `d`'s is *raised* after being raisable.  (This is the same-card
relocation lane: the chain card was pulled and goes straight back up; the
campaign's `PullKit`/`Relocate` machinery owns it.) -/
def NoChainRaise : Prop :=
  ∀ (B v : State) (tail : List Move) (d : Card),
    B.WF → SSaturated v → CanRaise B d → ShufflePlayW B tail v →
    ∀ (z' : Card) (s1 s2 : List Move) (A Z : State),
      z'.rank.toIdx ≤ d.rank.toIdx →
      tail = s1 ++ Move.tabToFound z' :: s2 → ShufflePlayW B s1 A →
      CanRaise A z' → State.step A (Move.tabToFound z') = some Z →
      ¬ CanRaise Z z' → False

/-- **`NoCoverStall`** — the second endpoint: no cover of a chain card of rank
at most `d`'s is followed by a mover that is *not* raisable.  This is the
opposite-coloured cover stall. -/
def NoCoverStall : Prop :=
  ∀ (B v : State) (tail : List Move) (d : Card),
    B.WF → SSaturated v → CanRaise B d → ShufflePlayW B tail v →
    ∀ (z' x : Card) (s1 s2 : List Move) (A Z : State),
      z'.rank.toIdx ≤ d.rank.toIdx →
      tail = s1 ++ Move.tabToTab x (Sum.inr z') :: s2 → ShufflePlayW B s1 A →
      CanRaise A z' → State.step A (Move.tabToTab x (Sum.inr z')) = some Z →
      ¬ CanRaise Z z' → ¬ CanRaise Z x → False

/-- **THE RESIDUAL DECOMPOSES INTO ITS TWO ENDPOINTS.** -/
theorem coverChainResidual_iff :
    CoverChainResidual ↔ NoChainRaise ∧ NoCoverStall := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro B v tail d hB hv hcan hplay z' s1 s2 A Z hle heq hp hcanA hstep hblk
      exact h B v tail d hB hv hcan hplay z' s1 s2 A Z (m := Move.tabToFound z')
        hle heq hp hcanA hstep hblk (Or.inl rfl)
    · intro B v tail d hB hv hcan hplay z' x s1 s2 A Z hle heq hp hcanA hstep hblk hx
      exact h B v tail d hB hv hcan hplay z' s1 s2 A Z (m := Move.tabToTab x (Sum.inr z'))
        hle heq hp hcanA hstep hblk (Or.inr ⟨x, rfl, hx⟩)
  · rintro ⟨h1, h2⟩ B v tail d hB hv hcan hplay z' s1 s2 A Z m hle heq hp hcanA hstep hblk hshape
    rcases hshape with hm | ⟨x, hm, hx⟩
    · have hstep' : State.step A (Move.tabToFound z') = some Z := by rw [← hm]; exact hstep
      exact h1 B v tail d hB hv hcan hplay z' s1 s2 A Z hle
        (hm ▸ heq) hp hcanA hstep' hblk
    · have hstep' : State.step A (Move.tabToTab x (Sum.inr z')) = some Z := by
        rw [← hm]; exact hstep
      exact h2 B v tail d hB hv hcan hplay z' x s1 s2 A Z hle
        (hm ▸ heq) hp hcanA hstep' hblk hx

/-- **THE CHAIN CLOSES THE CORRIDOR.**  `CoverChainResidual` plus the corridor's
saturation makes every free cross-suit corridor impossible. -/
theorem freeCorridor_of_coverChain (h : CoverChainResidual) :
    CrossSuitFreeCorridorResidual := by
  intro u v ρ pre γ tail c d b huwf hu hv hplay hmin heq hne hfree
  subst heq
  obtain ⟨B, -, -, -, -, -, htail, hB, hcanB, -, -, -, -, -, -, -⟩ :=
    corridor_tail_blocker hplay huwf hv
  obtain ⟨z', s1', s2', A', Z', m', hle, heq', hp1', hcanA', hstepA', hblockA',
    hshape'⟩ := chain_exists hB hv hcanB htail
  exact h B v tail d hB hv hcanB htail z' s1' s2' A' Z' m' hle heq' hp1'
    hcanA' hstepA' hblockA' hshape'

end Chain

/-! ## §8. Axiom battery -/

#print axioms Chain.first_blocking_letter
#print axioms Chain.not_readOK_of_block
#print axioms Chain.blocking_letter_shape
#print axioms Chain.corridor_tail_blocker
#print axioms Chain.pullFree_raise_or_cover
#print axioms Chain.slide_onto_rank
#print axioms Chain.cover_suit_ne
#print axioms Chain.cover_suit_not_twin
#print axioms Chain.pull_onto_rank
#print axioms Chain.pull_below_rank
#print axioms Chain.pull_landing_of_pull
#print axioms Chain.cover_card_ne
#print axioms Chain.corridor_pullFree_raise_or_cover
#print axioms Chain.chain_exists_aux
#print axioms Chain.chain_exists
#print axioms Chain.chain_rank_lt_thirteen
#print axioms Chain.coverChainResidual_iff
#print axioms Chain.freeCorridor_of_coverChain

#check @Chain.CoverChainResidual
#check @Chain.NoChainRaise
#check @Chain.NoCoverStall

