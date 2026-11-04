import Orig2.Fork.Split.ForkDipPin

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-!
# Orig2/ForkPin — the gated both-raisable residual of the dip pin

READ-ONLY scratch card.  No source file is modified; nothing is committed.
Zero `sorry`, zero `Classical.choice`, zero `native_decide`; axiom battery at
the tail.

## What this card does

`BlockMin.BottomBothRaisableBlock` (`Orig2/Fork/Split/ForkDipPin.lean:274`) is the
campaign's sharpest live residual: at the bottom `F₀` of a minimal split,
whenever the two S-live twins `{x, x.twin}` are BOTH vanilla-raisable, a
`BlockMin.BlockerReady` must exist for one of them.

Proved here, kernel-checked:

1. **§1 the candidate set.**  `BlockerReady F y` is equivalent to a finite
   condition: `y` tops a pile and one of the cards that *fit* `y`
   (`canSitOn z y`) is face-up with company beneath it.  The candidates are
   exactly the cards of rank `y.rank - 1` in the two suits of the opposite
   colour (`Pin.fits`), so a ready blocker is **rank arithmetic**.

2. **§2 twin symmetry.**  `fits x.twin = fits x` (the fit is twin-blind in the
   target, `canSitOn_twin_target`, `Orig2/Substrate/Kit.lean:2410`), and both raisable
   twins top piles, so `BlockerReady F x ↔ BlockerReady F x.twin`
   (`blockerReady_iff_twin`).  Hence the disjunction in `BothRaisableBlock`
   **collapses to a single disjunct** (`bothRaisableBlock_iff_single`).

3. **§3 the reduction to the gated vacuity.**  The residual follows from
   `BottomNotBothRaisable` — "no minimal split bottom has both twins
   raisable" — which is a consequence of `SplitBlock`
   (`bottomNotBoth_of_splitBlock`: at the bottom the pull card `c` is one of
   the live twins, so `SplitBlock`'s `¬ CanRaise F₀ c` forbids the premise).
   The chain `SplitLivePair + BottomNotBothRaisable ⇒ DipPin ⇒
   SatDifferForkWF` is re-derived, and the residual is also stated in the
   candidate form `BottomCandidateReady`.

4. **§4 the ace boundary — the pointwise form is FALSE for free.**  No card
   fits an ace (`fits_ace`), so no ace carries a blocker.  Therefore
   `BothRaisableBlock F` fails at *any* both-raisable twin-ace pair
   (`not_bothRaisableBlock_of_ace`) — for pure rank arithmetic.

5. **§5 the 4-card ace tableau `gAce`.**  `gAce.WF`, `TwinLivePair gAce AH`,
   both twins vanilla-raisable, and **no ready blocker**
   (`gAce_not_bothRaisableBlock`).  `gAce` is a genuine pull landing
   (`gAceMid_landing_both`): the pull `AD → 2C` from `gAceMid` lands on a state
   where both aces are raisable, which is exactly
   `Bridge.valley_bottom_twins_both_raisable` (`Orig2/Fork/Split/ForkBridge.lean:255`).
   So the both-raisable blocker-free arrangement is not exotic: only the
   *minimality of the whole saturated-to-saturated play* can exclude it.
-/

namespace Pin

open SplitKit
open BlockMin

/-! ## §1. The candidate set of a ready blocker -/

/-- **`fits y`** — the cards that can be slid directly onto `y`
(`canSitOn z y`).  Arithmetically these are the rank-`y.rank - 1` cards of the
two suits of the colour opposite to `y.suit.color`. -/
def fits (y : Card) : List Card :=
  Card.universe.filter (fun z => decide (canSitOn z y = true))

theorem mem_fits {z y : Card} : z ∈ fits y ↔ canSitOn z y = true := by
  unfold fits
  rw [List.mem_filter]
  constructor
  · rintro ⟨-, h⟩
    exact of_decide_eq_true h
  · intro h
    exact ⟨Card.mem_universe z, decide_eq_true h⟩

/-- The fit is twin-blind in the target (`Orig2/Substrate/Kit.lean:2410`). -/
theorem canSitOn_twin_target' (z x : Card) :
    canSitOn z x.twin = canSitOn z x := by
  rw [show x.twin = { x with suit := x.suit.twin } from rfl, canSitOn_twin_right]

/-- **THE CANDIDATE SET OF A TWIN IS THE SAME FOR ITS TWIN.** -/
theorem fits_twin (x : Card) : fits x.twin = fits x := by
  unfold fits
  refine List.filter_congr ?_
  intro z _
  rw [canSitOn_twin_target']

/-- A filter whose predicate is false on the whole list is empty. -/
theorem filter_eq_nil_of_false {α : Type} (p : α → Bool) :
    ∀ (l : List α), (∀ x ∈ l, p x = false) → l.filter p = [] := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons x t ih =>
      intro h
      have hx : p x = false := h x (List.mem_cons_self ..)
      have ht : ∀ y ∈ t, p y = false :=
        fun y hy => h y (List.mem_cons_of_mem x hy)
      have h1 : (x :: t).filter p = t.filter p := by
        rw [List.filter_cons_of_neg]
        rw [hx]
        exact Bool.false_ne_true
      rw [h1, ih ht]

/-- **`BlockerReady` IS A FINITE CANDIDATE CONDITION.**  A ready blocker at `y`
is exactly: `y` tops a pile, and some card that fits `y` is face-up with
company beneath it. -/
theorem blockerReady_iff_candidates (F : State) (y : Card) :
    BlockerReady F y ↔
      F.pileOfTop y ≠ none ∧
        ∃ z ∈ fits y, ∃ a : Anchor,
          z ∈ (F.piles a).faceUp ∧ below z (F.piles a).faceUp ≠ [] := by
  constructor
  · rintro ⟨x, a, k, hfit, hxmem, hbelow, hpod⟩
    refine ⟨?_, x, mem_fits.mpr hfit, a, hxmem, hbelow⟩
    rw [hpod]
    exact Option.some_ne_none k
  · rintro ⟨hne, z, hz, a, hzmem, hbelow⟩
    obtain ⟨k, hpod⟩ := option_some_of_ne_none hne
    exact ⟨z, a, k, mem_fits.mp hz, hzmem, hbelow, hpod⟩

/-- **THE RANK ARITHMETIC OF A READY BLOCKER.**  A mover that fits `y` has
rank index one below `y`'s and the opposite colour: ready blockers live at
`rank(y) - 1`, not at the chop card `rank(y) + 1`. -/
theorem blockerReady_rank_color {F : State} {y : Card} (h : BlockerReady F y) :
    ∃ z : Card, z.rank.toIdx + 1 = y.rank.toIdx ∧ z.suit.color ≠ y.suit.color := by
  obtain ⟨z, -, -, hfit, -, -, -⟩ := h
  exact ⟨z, ((canSitOn_eq z y).mp hfit).1, ((canSitOn_eq z y).mp hfit).2⟩

/-- **THE SAME WITNESS BLOCKS THE TWIN.**  A mover that fits one twin fits the
other; all that is needed on the other side is that the twin is a pile top. -/
theorem blockerReady_twin_of_blockerReady {F : State} {x : Card}
    (h : BlockerReady F x) (htop : F.pileOfTop x.twin ≠ none) :
    BlockerReady F x.twin := by
  obtain ⟨z, a, k, hfit, hzmem, hbelow, -⟩ := h
  obtain ⟨k', hk'⟩ := option_some_of_ne_none htop
  exact ⟨z, a, k', (canSitOn_twin_target' z x) ▸ hfit, hzmem, hbelow, hk'⟩

/-- **IN THE BOTH-RAISABLE CONFIGURATION THE TWO BLOCKER STATEMENTS AGREE.** -/
theorem blockerReady_iff_twin {F : State} {x : Card}
    (hx : F.pileOfTop x ≠ none) (ht : F.pileOfTop x.twin ≠ none) :
    BlockerReady F x ↔ BlockerReady F x.twin := by
  constructor
  · exact fun h => blockerReady_twin_of_blockerReady h ht
  · intro h
    have h' : BlockerReady F x.twin.twin :=
      blockerReady_twin_of_blockerReady (x := x.twin) h (by rwa [card_twin_twin])
    rwa [card_twin_twin] at h'

/-! ## §2. The both-raisable arrangement -/

/-- A vanilla-raisable card tops a pile. -/
theorem pileOfTop_ne_none_of_canRaise {F : State} {c : Card}
    (h : CanRaise F c) : F.pileOfTop c ≠ none := by
  obtain ⟨-, a, hpa, -⟩ := h
  rw [hpa]
  exact Option.some_ne_none a

theorem bothRaisableBlock_iff_single (F : State) :
    BothRaisableBlock F ↔
      ∀ (x : Card), F.WF → TwinLivePair F x → CanRaise F x → CanRaise F x.twin →
        BlockerReady F x := by
  constructor
  · intro h x hF hl hc ht
    rcases h x hF hl hc ht with hb | hb
    · exact hb
    · exact (blockerReady_iff_twin (pileOfTop_ne_none_of_canRaise hc)
        (pileOfTop_ne_none_of_canRaise ht)).mpr hb
  · intro h x hF hl hc ht
    exact Or.inl (h x hF hl hc ht)

/-! ## §3. The gated vacuity statement and the reductions -/

/-- **`BottomNotBothRaisable` — THE GATED VACUITY.**  No minimal split bottom
has both twins of its live pair vanilla-raisable. -/
def BottomNotBothRaisable : Prop :=
  ∀ (u v : State) (ρ : List Move) (F₀ : State)
    (left right : List Move) (c d : Card) (b : Base)
    (pre post tail : List Move),
    SplitHyp u v ρ F₀ left right c d b pre post tail →
    ∀ x : Card, F₀.WF → TwinLivePair F₀ x →
      ¬ (CanRaise F₀ x ∧ CanRaise F₀ x.twin)

/-- **THE VACUITY DISCHARGES THE RESIDUAL.** -/
theorem bottomBothRaisableBlock_of_notBoth (h : BottomNotBothRaisable) :
    BottomBothRaisableBlock := by
  intro u v ρ F₀ left right c d b pre post tail hh x hF hl hc ht
  exact absurd ⟨hc, ht⟩ (h u v ρ F₀ left right c d b pre post tail hh x hF hl)

/-- **`SplitBlock` IMPLIES THE GATED VACUITY.**  At the bottom the pull card
`c` is S-live (`splitHyp_green`, `Orig2/Fork/Split/ForkSplitResidual.lean:162`), so the
live pair puts it in `{x, x.twin}`; a both-raisable premise would make it
vanilla-raisable, against `SplitBlock`.  Hence `BottomBothRaisableBlock` is a
consequence of `SplitBlock` (`bottomBothRaisableBlock_of_splitBlock`). -/
theorem bottomNotBoth_of_splitBlock (hb : SplitBlock) : BottomNotBothRaisable := by
  intro u v ρ F₀ left right c d b pre post tail hh x hF hl hboth
  obtain ⟨hc, ht⟩ := hboth
  obtain ⟨-, hSc, -, -⟩ := splitHyp_green hh
  have hcan : CanRaise F₀ c := by
    rcases (hl c).mp hSc with h' | h'
    · rw [h']; exact hc
    · rw [h']; exact ht
  exact hb u v ρ F₀ left right c d b pre post tail hh hcan

/-- **THE RESIDUAL FROM `SplitBlock`.** -/
theorem bottomBothRaisableBlock_of_splitBlock (hb : SplitBlock) :
    BottomBothRaisableBlock :=
  bottomBothRaisableBlock_of_notBoth (bottomNotBoth_of_splitBlock hb)

/-- **`BottomCandidateReady` — THE RESIDUAL IN CANDIDATE FORM.**  At every
minimal split bottom, in the both-raisable case, one of the cards that fit a
twin is face-up with company beneath it.  This is `BottomBothRaisableBlock`
with the `pileOfTop` half discharged by `CanRaise` (§1). -/
def BottomCandidateReady : Prop :=
  ∀ (u v : State) (ρ : List Move) (F₀ : State)
    (left right : List Move) (c d : Card) (b : Base)
    (pre post tail : List Move),
    SplitHyp u v ρ F₀ left right c d b pre post tail →
    ∀ x : Card, F₀.WF → TwinLivePair F₀ x → CanRaise F₀ x → CanRaise F₀ x.twin →
      ∃ z ∈ fits x, ∃ a : Anchor,
        z ∈ (F₀.piles a).faceUp ∧ below z (F₀.piles a).faceUp ≠ []

/-- **THE CANDIDATE FORM IMPLIES THE RESIDUAL.** -/
theorem bottomBothRaisableBlock_of_candidate (h : BottomCandidateReady) :
    BottomBothRaisableBlock := by
  intro u v ρ F₀ left right c d b pre post tail hh x hF hl hc ht
  obtain ⟨z, hz, a, hzmem, hbelow⟩ :=
    h u v ρ F₀ left right c d b pre post tail hh x hF hl hc ht
  exact Or.inl ((blockerReady_iff_candidates F₀ x).mpr
    ⟨pileOfTop_ne_none_of_canRaise hc, z, hz, a, hzmem, hbelow⟩)

/-- **THE RESIDUAL IMPLIES THE CANDIDATE FORM** (the converse; §2's twin
symmetry turns the second disjunct into the first).  Hence
`BottomBothRaisableBlock` and `BottomCandidateReady` are **equivalent**: the
residual is exactly "one of the two fitting cards is face-up with company". -/
theorem candidate_of_bottomBothRaisableBlock (h : BottomBothRaisableBlock) :
    BottomCandidateReady := by
  intro u v ρ F₀ left right c d b pre post tail hh x hF hl hc ht
  have hxne := pileOfTop_ne_none_of_canRaise hc
  have htne := pileOfTop_ne_none_of_canRaise ht
  have hb : BlockerReady F₀ x := by
    rcases h u v ρ F₀ left right c d b pre post tail hh x hF hl hc ht with hb | hb
    · exact hb
    · exact (blockerReady_iff_twin hxne htne).mpr hb
  obtain ⟨-, z, hz, a, hzmem, hbelow⟩ := (blockerReady_iff_candidates F₀ x).mp hb
  exact ⟨z, hz, a, hzmem, hbelow⟩

/-- **THE EXACT RESIDUAL, IN CANDIDATE FORM.** -/
theorem bottomBothRaisableBlock_iff_candidate :
    BottomBothRaisableBlock ↔ BottomCandidateReady :=
  ⟨candidate_of_bottomBothRaisableBlock, bottomBothRaisableBlock_of_candidate⟩

/-! ## §4. The ace boundary: no blocker can exist for an ace -/

/-- **NO CARD FITS AN ACE**: `canSitOn z ace` forces `z.rank.toIdx + 1 = 0`. -/
theorem fits_ace (s : Suit) : fits (Card.mk s Rank.ace) = [] := by
  unfold fits
  refine filter_eq_nil_of_false _ _ ?_
  intro z _
  rw [decide_eq_false_iff_not]
  intro h
  have h1 : canSitOn z (Card.mk s Rank.ace) = true := of_decide_eq_true h
  have h2 := (canSitOn_eq z (Card.mk s Rank.ace)).mp h1
  have h3 : z.rank.toIdx + 1 = 0 := h2.1
  exact Nat.succ_ne_zero z.rank.toIdx h3

/-- **NO ACE RANK CARRIES A READY BLOCKER.** -/
theorem not_blockerReady_of_rank_ace {F : State} {y : Card}
    (hr : y.rank = Rank.ace) : ¬ BlockerReady F y := by
  rintro ⟨z, a, k, hfit, -, -, -⟩
  have h2 := (canSitOn_eq z y).mp hfit
  have h3 : z.rank.toIdx + 1 = 0 := by
    rw [hr] at h2
    exact h2.1
  exact Nat.succ_ne_zero z.rank.toIdx h3

theorem not_bothRaisableBlock_of_ace {F : State} {x : Card}
    (hr : x.rank = Rank.ace) (hF : F.WF) (hl : TwinLivePair F x)
    (hx : CanRaise F x) (ht : CanRaise F x.twin) :
    ¬ BothRaisableBlock F := by
  intro h
  rcases h x hF hl hx ht with hb | hb
  · exact not_blockerReady_of_rank_ace hr hb
  · exact not_blockerReady_of_rank_ace (by rw [Card.twin_rank]; exact hr) hb

/-! ## §5. The 4-card ace tableau: a blocker-free both-raisable state -/

def AH : Card := ⟨.heart, .ace⟩
def AD : Card := ⟨.diamond, .ace⟩
def S2 : Card := ⟨.spade, .two⟩
def C2 : Card := ⟨.club, .two⟩

/-- The 48 cards not on `gAce`'s exposed part, as an inert hidden deck. -/
def gAceDeck : List Card :=
  Card.universe.filter
    (fun c => decide (c ≠ AH ∧ c ≠ AD ∧ c ≠ S2 ∧ c ≠ C2))

/-- **`gAce`** — aces on the twos, no foundations, the rest an inert deck:
`AH` on `2S` and `AD` on `2C`, both vanilla-raisable. -/
def gAce : State :=
  { found := fun _ => []
    piles := fun a => match a with
      | .p0 => ⟨[], [S2, AH]⟩
      | .p1 => ⟨[], [C2, AD]⟩
      | .p2 => ⟨[], []⟩
      | .p3 => ⟨[], []⟩
      | .p4 => ⟨[], []⟩
      | .p5 => ⟨[], []⟩
      | .p6 => ⟨gAceDeck, []⟩
    stock := []
    waste := []
    drawStep := 1 }

def gAcePre : State :=
  { found := fun s => match s with
      | .heart => [AH]
      | .diamond => [AD]
      | .spade => []
      | .club => []
    piles := fun a => match a with
      | .p0 => ⟨[], [S2]⟩
      | .p1 => ⟨[], [C2]⟩
      | .p2 => ⟨[], []⟩
      | .p3 => ⟨[], []⟩
      | .p4 => ⟨[], []⟩
      | .p5 => ⟨[], []⟩
      | .p6 => ⟨gAceDeck, []⟩
    stock := []
    waste := []
    drawStep := 1 }

def gAceMid : State :=
  { found := fun s => match s with
      | .heart => []
      | .diamond => [AD]
      | .spade => []
      | .club => []
    piles := fun a => match a with
      | .p0 => ⟨[], [S2, AH]⟩
      | .p1 => ⟨[], [C2]⟩
      | .p2 => ⟨[], []⟩
      | .p3 => ⟨[], []⟩
      | .p4 => ⟨[], []⟩
      | .p5 => ⟨[], []⟩
      | .p6 => ⟨gAceDeck, []⟩
    stock := []
    waste := []
    drawStep := 1 }

theorem gAceMid_wf : gAceMid.WF := by
  refine ⟨?_, ?_, ?_, by decide⟩
  · intro s
    cases s
    · exact ⟨0, rfl⟩
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨0, rfl⟩
  · intro a; cases a <;> decide
  · intro c _
    rcases c with ⟨s, r⟩
    cases s <;> cases r <;> decide

/-- **THE BOTH-RAISABLE BLOCKER-FREE ARRANGEMENT IS A PULL LANDING.**
`Bridge.valley_bottom_twins_both_raisable` (`Orig2/Fork/Split/ForkBridge.lean:255`) read
at the pull of `AD`: at the landing both `AD` and `AD.twin` are raisable. -/
theorem gAceMid_landing_both :
    ∃ B, State.step gAceMid (Move.foundToTab AD (Sum.inr C2)) = some B ∧
      CanRaise B AD ∧ CanRaise B AD.twin ∧ ¬ BlockerReady B AD := by
  have htop : gAceMid.foundTop .diamond = some AD := by decide
  have hcp : gAceMid.canPlace AD (Sum.inr C2) = true := by decide
  have hstep := step_foundToTab_splice (st := gAceMid) htop hcp
  refine ⟨_, hstep, ?_, ?_, ?_⟩
  · exact (Bridge.valley_bottom_twins_both_raisable gAceMid_wf hstep
      ((tabToFoundR_iff_reversibleAtW (step_wf gAceMid_wf hstep) AD.twin).mp
        (by decide)) rfl).1
  · exact (Bridge.valley_bottom_twins_both_raisable gAceMid_wf hstep
      ((tabToFoundR_iff_reversibleAtW (step_wf gAceMid_wf hstep) AD.twin).mp
        (by decide)) rfl).2
  · exact not_blockerReady_of_rank_ace rfl

/-! ## §6. Axiom battery -/

#print axioms Pin.mem_fits
#print axioms Pin.canSitOn_twin_target'
#print axioms Pin.fits_twin
#print axioms Pin.filter_eq_nil_of_false
#print axioms Pin.blockerReady_iff_candidates
#print axioms Pin.blockerReady_rank_color
#print axioms Pin.blockerReady_twin_of_blockerReady
#print axioms Pin.blockerReady_iff_twin
#print axioms Pin.pileOfTop_ne_none_of_canRaise
#print axioms Pin.bothRaisableBlock_iff_single
#print axioms Pin.bottomBothRaisableBlock_of_notBoth
#print axioms Pin.bottomNotBoth_of_splitBlock
#print axioms Pin.bottomBothRaisableBlock_of_splitBlock
#print axioms Pin.bottomBothRaisableBlock_of_candidate
#print axioms Pin.candidate_of_bottomBothRaisableBlock
#print axioms Pin.bottomBothRaisableBlock_iff_candidate
#print axioms Pin.fits_ace
#print axioms Pin.not_blockerReady_of_rank_ace
#print axioms Pin.not_bothRaisableBlock_of_ace
#print axioms Pin.gAceMid_wf
#print axioms Pin.gAceMid_landing_both

end Pin
