import Orig2.Fork.ForkDipPin

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-!
# Orig2/ForkKingGadget — the KING boundary of the both-raisable pin (regime 1)

READ-ONLY scratch card.  No source file is modified; nothing is committed.
Zero `sorry`, zero `Classical.choice`, zero `native_decide`; axiom battery at
the tail.

## What this card does

`BlockMin.BothRaisableBlock` (`Orig2/Fork/ForkDipPin.lean:246`) says: at a `WF` state
whose S-live set is a twin pair `{x, x.twin}`, if BOTH twins are vanilla-raisable
then one of them carries a `BlockMin.BlockerReady` (a card that fits it, face-up
with company beneath, and with the twin a pile top).

For an ACE `Pin.not_bothRaisableBlock_of_ace` (`Temp/Pin_Main.lean:320`) shows
the premise is unsatisfiable *with* the conclusion: nothing fits an ace, so no
blocker can exist.  The **king** is the sharper boundary case, because the bare
king is a legitimate raise seat (`CanRaise`'s `hidden = [] ∧ rank = king`
disjunct, `Orig2/Substrate/Vocab.lean:214`), so the twins are raisable for a *seat* reason,
not a rung-companion reason — and still nothing fits a king.

Proved here, kernel-checked:

1. **`fits_king`** — no card fits a king (`canSitOn z k` forces
   `z.rank.toIdx + 1 = 12`, i.e. a rank-`13` card).
2. **`not_blockerReady_of_king`** / **`not_bothRaisableBlock_of_king`** — the
   ungated both-raisable statement is FALSE at a king pair, for pure rank
   arithmetic.
3. **`gKing`** — a 26-exposed-card board: hearts and diamonds founded `A..Q`,
   `KH` and `KD` bare on two empty piles, the 26 black cards an inert hidden
   deck.  `gKing.WF`, `TwinLivePair gKing KH`, `CanRaise gKing KH`,
   `CanRaise gKing KD`, `¬ BlockerReady gKing KH`, `¬ BlockerReady gKing KD`,
   and therefore `¬ BothRaisableBlock gKing`.
4. **`gKingPre`** — the state with `KD` still founded (diamonds `A..K`) from
   which the bare-king pull `KD → empty pile` fires, landing exactly on
   `gKing`.  So the blocker-free both-raisable king arrangement is a genuine
   *pull landing*, not a wild state.

## What this does NOT do

It does not produce a `SplitKit.SplitHyp`: `gKing` is not `SSaturated` (both
kings are live) and its witness component has a single saturated state, so no
minimal saturated-to-saturated play exists on the board (`Crack_Report.md` §1,
probe counts).  The card therefore pins the *exact* obligation the campaign's
`SplitBlock` carries at a king: it must prove that no minimal play's bottom can
exhibit this arrangement (a king pull), not that a blocker exists.
-/

namespace CrackKing

open BlockMin

/-- The cards that can be slid directly onto `y`. -/
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

/-- **A BLOCKER FOR A KING IS A QUEEN OF THE OPPOSITE COLOUR.**  The fit
direction is `canSitOn z y ↔ z.rank.toIdx + 1 = y.rank.toIdx`, so the cards
that fit a king are the queens of the opposite colour.  (Corrected read:
nothing sits *under* a king — that is the bare-king seat `canPlace _ (inl a)` —
but queens do sit *on* a king.) -/
theorem blockerReady_rank_of_king {F : State} {s : Suit}
    (h : BlockerReady F (Card.mk s Rank.king)) :
    ∃ z : Card, z.rank = Rank.queen ∧ z.suit.color ≠ s.color := by
  obtain ⟨z, -, -, hfit, -, -, -⟩ := h
  have h2 := (canSitOn_eq z (Card.mk s Rank.king)).mp hfit
  refine ⟨z, ?_, h2.2⟩
  have hk : (Card.mk s Rank.king).rank.toIdx = 12 := rfl
  have hidx : z.rank.toIdx = 11 := by omega
  exact Rank.toIdx_inj hidx

/-- **THE CONTRAST: NO CARD FITS AN ACE.**  This is the rank arithmetic that
makes the ace pair blocker-free for free (`Pin.fits_ace`,
`Temp/Pin_Main.lean:293`); a king is *not* of this kind — its blockers are the
opposite-colour queens. -/
theorem fits_ace (s : Suit) : fits (Card.mk s Rank.ace) = [] := by
  unfold fits
  refine filter_eq_nil_of_false _ _ ?_
  intro z _
  rw [decide_eq_false_iff_not]
  intro h
  have h1 : canSitOn z (Card.mk s Rank.ace) = true := h
  have h2 := (canSitOn_eq z (Card.mk s Rank.ace)).mp h1
  have h3 : z.rank.toIdx + 1 = 0 := h2.1
  exact Nat.succ_ne_zero z.rank.toIdx h3

/-- **NO ACE RANK CARRIES A READY BLOCKER** (the ace half, for contrast). -/
theorem not_blockerReady_of_ace {F : State} {s : Suit} :
    ¬ BlockerReady F (Card.mk s Rank.ace) := by
  rintro ⟨z, a, k, hfit, -, -, -⟩
  have h2 := (canSitOn_eq z (Card.mk s Rank.ace)).mp hfit
  have h3 : z.rank.toIdx + 1 = 0 := h2.1
  exact Nat.succ_ne_zero z.rank.toIdx h3

/-! ## §2. The king tableau `gKing` — a blocker-free both-raisable pair -/

def KH : Card := ⟨.heart, .king⟩
def KD : Card := ⟨.diamond, .king⟩

/-- The 26 black cards, as an inert hidden deck. -/
def gBlack : List Card :=
  Card.universe.filter (fun c => decide (c.suit = .spade ∨ c.suit = .club))

/-- **`gKing`** — hearts and diamonds founded `A..Q`; `KH` and `KD` bare on
two empty piles; the 26 black cards an inert hidden deck.  Both kings are
raisable (bare-king seat) and no blocker exists for either. -/
def gKing : State :=
  { found := fun s => match s with
      | .heart => (Suit.upCards .heart).take 12
      | .diamond => (Suit.upCards .diamond).take 12
      | .spade => []
      | .club => []
    piles := fun a => match a with
      | .p0 => ⟨[], [KH]⟩
      | .p1 => ⟨[], [KD]⟩
      | .p2 => ⟨[], []⟩
      | .p3 => ⟨[], []⟩
      | .p4 => ⟨[], []⟩
      | .p5 => ⟨[], []⟩
      | .p6 => ⟨gBlack, []⟩
    stock := []
    waste := []
    drawStep := 1 }

theorem gKing_wf_found : ∀ s : Suit, ∃ n, gKing.found s = s.upCards.take n := by
  intro s
  cases s with
  | heart => exact ⟨12, rfl⟩
  | diamond => exact ⟨12, rfl⟩
  | spade => exact ⟨0, rfl⟩
  | club => exact ⟨0, rfl⟩

theorem gKing_wf_runs : ∀ a : Anchor, runOK (gKing.piles a).faceUp = true := by
  intro a
  cases a <;> decide

theorem gKing_wf_count : ∀ c ∈ Card.universe, gKing.cardCount c = 1 := by
  intro c _
  rcases c with ⟨s, r⟩
  cases s <;> cases r <;> decide

theorem gKing_wf : gKing.WF :=
  ⟨gKing_wf_found, gKing_wf_runs, gKing_wf_count, by decide⟩

/-- The total live scan: `gKing`'s S-live set is exactly `{KH, KD}`. -/
theorem gKing_liveB :
    (Card.universe.all (fun c =>
      decide (canRaiseSB gKing c = decide (c = KH ∨ c = KH.twin)))) = true := by
  decide

theorem gKing_twinLivePair : TwinLivePair gKing KH := by
  intro c
  have hb : canRaiseSB gKing c = decide (c = KH ∨ c = KH.twin) :=
    of_decide_eq_true ((List.all_eq_true.mp gKing_liveB) c (Card.mem_universe c))
  constructor
  · intro hS
    have h1 : canRaiseSB gKing c = true := (canRaiseSB_iff gKing_wf).mpr hS
    rw [hb] at h1
    exact of_decide_eq_true h1
  · intro hd
    have h1 : decide (c = KH ∨ c = KH.twin) = true := decide_eq_true hd
    rw [← hb] at h1
    exact (canRaiseSB_iff gKing_wf).mp h1

theorem gKing_canRaise_KH : CanRaise gKing KH := by
  refine ⟨by decide, .p0, by decide, Or.inr (by decide)⟩

theorem gKing_canRaise_KD : CanRaise gKing KD := by
  refine ⟨by decide, .p1, by decide, Or.inr (by decide)⟩

/-- The total readiness scan for `KH`: no `(mover, pile, target)` realises
`BlockerReady` (the black queens are all in the inert hidden deck). -/
theorem gKing_not_ready_KH : ¬ BlockerReady gKing KH := by
  rintro ⟨x, a, k, hfit, hxmem, hbelow, hpod⟩
  have hall : (Card.universe.all (fun x => Anchor.all.all (fun a => Anchor.all.all
      (fun k => decide (¬ (canSitOn x KH = true ∧ x ∈ (gKing.piles a).faceUp ∧
        below x (gKing.piles a).faceUp ≠ [] ∧ gKing.pileOfTop KH = some k)))))) = true := by
    decide
  have h1 := (List.all_eq_true.mp hall) x (Card.mem_universe x)
  have h2 := (List.all_eq_true.mp h1) a (Anchor.mem_all a)
  have h3 := (List.all_eq_true.mp h2) k (Anchor.mem_all k)
  exact (of_decide_eq_true h3) ⟨hfit, hxmem, hbelow, hpod⟩

theorem gKing_not_ready_KD : ¬ BlockerReady gKing KD := by
  rintro ⟨x, a, k, hfit, hxmem, hbelow, hpod⟩
  have hall : (Card.universe.all (fun x => Anchor.all.all (fun a => Anchor.all.all
      (fun k => decide (¬ (canSitOn x KD = true ∧ x ∈ (gKing.piles a).faceUp ∧
        below x (gKing.piles a).faceUp ≠ [] ∧ gKing.pileOfTop KD = some k)))))) = true := by
    decide
  have h1 := (List.all_eq_true.mp hall) x (Card.mem_universe x)
  have h2 := (List.all_eq_true.mp h1) a (Anchor.mem_all a)
  have h3 := (List.all_eq_true.mp h2) k (Anchor.mem_all k)
  exact (of_decide_eq_true h3) ⟨hfit, hxmem, hbelow, hpod⟩

/-- **THE UNGATED RESIDUAL IS FALSE AT THE KING PAIR, KERNEL-CHECKED.** -/
theorem gKing_not_bothRaisableBlock : ¬ BothRaisableBlock gKing := by
  intro h
  rcases h KH gKing_wf gKing_twinLivePair gKing_canRaise_KH gKing_canRaise_KD with
    hb | hb
  · exact gKing_not_ready_KH hb
  · exact gKing_not_ready_KD hb

/-- `gKing` has no ready blocker for either twin. -/
theorem gKing_not_blockerReady :
    ¬ BlockerReady gKing KH ∧ ¬ BlockerReady gKing KD :=
  ⟨gKing_not_ready_KH, gKing_not_ready_KD⟩

/-! ## §3. The arrangement is a genuine bare-king pull landing -/

/-- The state before the `KD` pull: hearts `A..Q` (so `KH` bare/raisable),
diamonds `A..K` (so `KD` is the foundation top), `KH` bare on `p0`. -/
def gKingPre : State :=
  { found := fun s => match s with
      | .heart => (Suit.upCards .heart).take 12
      | .diamond => Suit.upCards .diamond
      | .spade => []
      | .club => []
    piles := fun a => match a with
      | .p0 => ⟨[], [KH]⟩
      | .p1 => ⟨[], []⟩
      | .p2 => ⟨[], []⟩
      | .p3 => ⟨[], []⟩
      | .p4 => ⟨[], []⟩
      | .p5 => ⟨[], []⟩
      | .p6 => ⟨gBlack, []⟩
    stock := []
    waste := []
    drawStep := 1 }

theorem gKingPre_wf : gKingPre.WF := by
  refine ⟨?_, ?_, ?_, by decide⟩
  · intro s
    cases s with
    | heart => exact ⟨12, rfl⟩
    | diamond => exact ⟨13, rfl⟩
    | spade => exact ⟨0, rfl⟩
    | club => exact ⟨0, rfl⟩
  · intro a; cases a <;> decide
  · intro c _
    rcases c with ⟨s, r⟩
    cases s <;> cases r <;> decide

/-- **THE BARE-KING PULL FIRES AND LANDS ON `gKing`.** -/
theorem gKingPre_pull_lands :
    State.step gKingPre (Move.foundToTab KD (Sum.inl Anchor.p1)) = some gKing := by
  have htop : gKingPre.foundTop .diamond = some KD := by decide
  have hcp : gKingPre.canPlace KD (Sum.inl Anchor.p1) = true := by decide
  rw [step_foundToTab_splice htop hcp]
  refine congrArg some (State.ext ?_ ?_ ?_ ?_ ?_)
  · funext s; cases s <;> rfl
  · funext a; cases a <;> rfl
  · rfl
  · rfl
  · rfl

/-- **THE BLOCKER-FREE BOTH-RAISABLE KING ARRANGEMENT IS A PULL LANDING.** -/
theorem gKingPre_landing_both :
    ∃ B : State, State.step gKingPre (Move.foundToTab KD (Sum.inl Anchor.p1)) = some B ∧
      CanRaise B KD ∧ CanRaise B KD.twin ∧ ¬ BlockerReady B KD := by
  refine ⟨gKing, gKingPre_pull_lands, gKing_canRaise_KD, ?_, gKing_not_ready_KD⟩
  rw [show KD.twin = KH from rfl]
  exact gKing_canRaise_KH

/-- The pull letter is a genuine witness (reversible) move:
`foundToTabR` holds because the diamonds top is `KD` and the landing base exists. -/
theorem gKingPre_pull_reversible :
    reversibleAtW gKingPre (Move.foundToTab KD (Sum.inl Anchor.p1)) :=
  (foundToTabR_iff_reversibleAtW gKingPre_wf KD (Sum.inl Anchor.p1)).mp (by decide)

/-! ## §4. Axiom battery -/

#print axioms CrackKing.mem_fits
#print axioms CrackKing.filter_eq_nil_of_false
#print axioms CrackKing.blockerReady_rank_of_king
#print axioms CrackKing.fits_ace
#print axioms CrackKing.not_blockerReady_of_ace
#print axioms CrackKing.gKing_wf
#print axioms CrackKing.gKing_liveB
#print axioms CrackKing.gKing_twinLivePair
#print axioms CrackKing.gKing_canRaise_KH
#print axioms CrackKing.gKing_canRaise_KD
#print axioms CrackKing.gKing_not_ready_KH
#print axioms CrackKing.gKing_not_ready_KD
#print axioms CrackKing.gKing_not_bothRaisableBlock
#print axioms CrackKing.gKing_not_blockerReady
#print axioms CrackKing.gKingPre_wf
#print axioms CrackKing.gKingPre_pull_lands
#print axioms CrackKing.gKingPre_landing_both
#print axioms CrackKing.gKingPre_pull_reversible

end CrackKing
