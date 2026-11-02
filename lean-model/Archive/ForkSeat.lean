import Orig2.Fork.ForkBlocks
import Orig2.Fork.ForkRelocate
import Orig2.Substrate.Position
import Orig2.Substrate.StepWF
import Orig2.Substrate.Classification

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-!
# Orig2/ForkSeat — the two surviving seat-mate corridors, realized in the kernel

Scratch card.  READ-ONLY on `Orig2/`; no source edit, no commit.
Zero `sorry`, zero `Classical.choice`, zero `nativeDecide`, no `decide` on
`State` equality.

## What this card does

`Blocks.NoSeatMateCrossSuit` (`Orig2/Fork/ForkBlocks.lean:499`) is the last
surviving shape of cross-suit vacuity:

> no canonical (shortest, min-`inv`) cross-suit free corridor between two
> `WF`, `SSaturated` endpoints has seat-mate cards (`Blocks.SeatMate c d`).

Its two cases are shape 3 (`Blocks.inr_expose_shape`, `:164`: `d = c.twin`,
the pull lands on the card directly below `c`) and shape 1
(`Blocks.inl_shape`, `:140`: both cards kings, the pull lands on the emptied
bare seat).

This card proves that **both corridor shapes are realizable in a canonical
play**, i.e. in a `WF` origin, shortest, `inv`-minimal witness play carrying
**all** the corridor hypotheses of `Blocks.canonical_corridor_seatMate`
(`FreeOnly γ`, cross-suit, `Pullable` at the raise's image, read-safety and
seat-inertness vacuous at `γ = []`) — with the two `SSaturated` endpoint
hypotheses deleted.  So the *entire* content of `NoSeatMateCrossSuit` is the
saturation lock, not the geometry: the corridor is not a shortening
(the raise and the pull move two different rungs, `twoSuit_gap_is_shortest`),
and it is `inv`-minimal because in any shortest play its raise must precede
its pull (the rung ledger).

The witnesses:

```text
TWIN  raise ♠3 ; pull ♣3 onto ♥4      (♣3 = (♠3).twin, ♥4 directly below ♠3)
KING  raise ♠K ; pull ♣K onto empty p0 (both kings, the bare-king seat swap)
```

Each is certified: `WF` at both ends, `ShufflePlayW`, minimal length from the
rung gap, `inv = 1` with every shortest play having `inv ≥ 1` (rung ledger).
-/

namespace Seat

/-! ## §0. Cards for the twin board -/

def AS : Card := ⟨.spade, .ace⟩
def S2 : Card := ⟨.spade, .two⟩
def S3 : Card := ⟨.spade, .three⟩
def AC : Card := ⟨.club, .ace⟩
def C2 : Card := ⟨.club, .two⟩
def C3 : Card := ⟨.club, .three⟩
def H4 : Card := ⟨.heart, .four⟩

/-- The twin board's stock: every card not on the tableau or the foundations. -/
def stockT : List Card :=
  Card.universe.filter (fun c =>
    decide (c ≠ AS) && decide (c ≠ S2) && decide (c ≠ AC) &&
      decide (c ≠ C2) && decide (c ≠ C3) && decide (c ≠ H4) &&
      decide (c ≠ S3))

/-- **THE TWIN BOARD.**  Pile `p0` carries `♥4` under `♠3`; the spade
foundation is at height 2 (`♠3` is `nextUp`), the club foundation at height 3
with `♣3 = (♠3).twin` on top. -/
def uT : State :=
  { found := fun s => match s with
      | .spade => [AS, S2]
      | .club => [AC, C2, C3]
      | _ => []
    piles := fun a => match a with
      | .p0 => ⟨[], [H4, S3]⟩
      | _ => ⟨[], []⟩
    stock := stockT
    waste := []
    drawStep := 1 }

theorem uT_wf_found : ∀ s : Suit, ∃ n, uT.found s = s.upCards.take n := by
  intro s
  cases s with
  | spade => exact ⟨2, rfl⟩
  | club => exact ⟨3, rfl⟩
  | heart => exact ⟨0, rfl⟩
  | diamond => exact ⟨0, rfl⟩

theorem uT_wf_runs : ∀ a : Anchor, runOK (uT.piles a).faceUp = true := by
  intro a
  cases a <;> decide

theorem uT_wf_count : ∀ c ∈ Card.universe, uT.cardCount c = 1 := by
  intro c _
  rcases c with ⟨s, r⟩
  cases s <;> cases r <;> decide

theorem uT_wf : uT.WF := ⟨uT_wf_found, uT_wf_runs, uT_wf_count, by decide⟩

/-! ## §1. The twin corridor's two letters -/

def mRT : Move := Move.tabToFound S3
def mPT : Move := Move.foundToTab C3 (Sum.inr H4)

/-- The raise's image. -/
def BT : State :=
  (uT.setFound .spade (uT.found .spade ++ [S3])).setPile .p0
    (Pile.afterRunRemoved (uT.piles .p0) (chop (uT.piles .p0).faceUp))

/-- The pull's landing. -/
def vT : State := (BT.setFound .club (chop (BT.found .club))).putCard C3 (Sum.inr H4)

theorem uT_next : uT.nextUp S3 = true := by decide
theorem uT_pileOfTop : uT.pileOfTop S3 = some .p0 := by decide
theorem uT_chop : chop (uT.piles .p0).faceUp = [H4] := rfl

theorem stepR_T : State.step uT mRT = some BT := by
  show State.step uT (Move.tabToFound S3) = some BT
  rw [step_tabToFound_splice uT_next uT_pileOfTop]
  rfl

theorem BT_found_club : BT.found .club = [AC, C2, C3] := rfl
theorem BT_piles_p0 : BT.piles .p0 = ⟨[], [H4]⟩ := rfl
theorem BT_foundTop_club : BT.foundTop .club = some C3 := by decide
theorem BT_canPlace : BT.canPlace C3 (Sum.inr H4) = true := by decide

theorem stepP_T : State.step BT mPT = some vT := by
  show State.step BT (Move.foundToTab C3 (Sum.inr H4)) = some vT
  rw [step_foundToTab_splice BT_foundTop_club BT_canPlace]
  rfl

theorem BT_wf : BT.WF := step_wf uT_wf stepR_T
theorem vT_wf : vT.WF := step_wf BT_wf stepP_T

theorem revR_T : reversibleAtW uT mRT :=
  (tabToFoundR_iff_reversibleAtW uT_wf S3).mp (by decide)

theorem revP_T : reversibleAtW BT mPT :=
  (foundToTabR_iff_reversibleAtW BT_wf C3 (Sum.inr H4)).mp (by decide)

/-- **THE TWIN WITNESS PLAY.** -/
theorem playT : ShufflePlayW uT [mRT, mPT] vT :=
  Walk.cons revR_T stepR_T (Walk.cons revP_T stepP_T (Walk.nil vT))

/-- The exposed card is `♥4`, directly below `♠3`, and `♣3 = (♠3).twin`. -/
theorem corridorT :
    uT.piles .p0 = ⟨[], [H4, S3]⟩ ∧ uT.pileOfTop S3 = some .p0 ∧
      uT.pileOfTop H4 = none ∧ BT.pileOfTop H4 = some .p0 ∧
      C3 = (S3).twin := by
  refine ⟨rfl, uT_pileOfTop, by decide, by decide, ?_⟩
  rfl

/-! ## §2. The corridor hypotheses of `Blocks.canonical_corridor_seatMate`, all met

The corridor decomposition is `pre = []`, `γ = []`, `tail = []`, the raise at
`A = uT` (image `BT`) and the pull `foundToTab C3 (inr H4)` at `BT`. -/

theorem freeOnlyT : Canon.FreeOnly ([] : List Move) := fun m hm => (List.not_mem_nil hm).elim

theorem crossSuitT : S3.suit ≠ C3.suit := by decide

theorem pullableT : PullKit.Pullable BT C3 (Sum.inr H4) :=
  ⟨BT_foundTop_club, BT_canPlace⟩

/-- The corridor's cards are seat-mates: `♣3 = (♠3).twin`, and `♠3` is no king. -/
theorem seatMateT : SeatMate S3 C3 := by
  refine Or.inr ⟨?_, Or.inr rfl⟩
  decide

/-! ## §3. The rung ledger: every shortest play has `inv ≥ 1`

`rungAt uT = (2, 0, 0, 3)` (spade, heart, diamond, club) and
`rungAt vT = (3, 0, 0, 2)`.  In a two-letter play the spade `+1` and the club
`−1` must be produced by one raise and one pull; a pull of `♣3` is illegal at
`uT` (no base accepts it), so the raise strictly precedes the pull — a
cross-suit raise-before-pull pair. -/

/-! ### §3.0 A pull of `♣3` is illegal at `uT` -/

theorem uT_pileOfTop_eq {y : Card} {k : Anchor} (h : uT.pileOfTop y = some k) : y = S3 := by
  have htop : (uT.piles k).top = some y := (pileOfTop_eq_some_iff uT_wf).mp h
  cases k with
  | p0 =>
      have h1 : lastOf [H4, S3] = some y := htop
      have h2 : lastOf [H4, S3] = some S3 := by decide
      rw [h2] at h1
      exact (Option.some.inj h1).symm
  | p1 => rw [show (uT.piles .p1).top = none from rfl] at htop; nomatch htop
  | p2 => rw [show (uT.piles .p2).top = none from rfl] at htop; nomatch htop
  | p3 => rw [show (uT.piles .p3).top = none from rfl] at htop; nomatch htop
  | p4 => rw [show (uT.piles .p4).top = none from rfl] at htop; nomatch htop
  | p5 => rw [show (uT.piles .p5).top = none from rfl] at htop; nomatch htop
  | p6 => rw [show (uT.piles .p6).top = none from rfl] at htop; nomatch htop

theorem uT_canPlace_club_false : ∀ b : Base, uT.canPlace C3 b = false := by
  intro b
  cases b with
  | inl a =>
      rw [canPlace_inl_unfold]
      rw [show decide (C3.rank = Rank.king) = false from by decide]
      simp
  | inr y =>
      rw [canPlace_inr_eq]
      cases h : uT.pileOfTop y with
      | none => rfl
      | some k =>
          have hy : y = S3 := uT_pileOfTop_eq h
          subst hy
          exact show canSitOn C3 S3 = false from by decide

theorem uT_pull_club_none (b : Base) : State.step uT (Move.foundToTab C3 b) = none := by
  have hft : uT.foundTop C3.suit = some C3 := by decide
  have hcp : uT.canPlace C3 b = false := uT_canPlace_club_false b
  rw [show State.step uT (Move.foundToTab C3 b) =
    (match uT.foundTop C3.suit with
     | some c' => if decide (c' = C3) && uT.canPlace C3 b then
         some ((uT.setFound C3.suit (chop (uT.found C3.suit))).putCard C3 b)
       else none
     | none => none) from rfl]
  rw [hft, hcp]
  simp

/-! ### §3.1 Rung-step shape lemmas -/

/-- A single step changes at most one suit's rung. -/
theorem rung_single_suit {a b : State} {m : Move} (h : State.step a m = some b)
    {σ τ : Suit} (hστ : σ ≠ τ) (hchg : rungAt a σ ≠ rungAt b σ) :
    rungAt b τ = rungAt a τ := by
  cases m with
  | draw => exact absurd (rungAt_draw h σ).symm hchg
  | wasteToFound X =>
      by_cases hσX : σ = X.suit
      · rw [rungAt_wasteToFound h τ,
          ite_eq_right (fun hh => hστ (hσX.trans hh.symm))]
      · exfalso
        rw [rungAt_wasteToFound h σ, ite_eq_right hσX] at hchg
        exact hchg rfl
  | wasteToTab X bb => exact rungAt_wasteToTab h τ
  | tabToFound X =>
      by_cases hσX : σ = X.suit
      · rw [rungAt_tabToFound h τ, ite_eq_right (fun hh => hστ (hσX.trans hh.symm))]
      · exfalso
        rw [rungAt_tabToFound h σ, ite_eq_right hσX] at hchg
        exact hchg rfl
  | foundToTab X bb =>
      by_cases hσX : σ = X.suit
      · rw [rungAt_foundToTab h τ, ite_eq_right (fun hh => hστ (hσX.trans hh.symm))]
      · exfalso
        rw [rungAt_foundToTab h σ, ite_eq_right hσX] at hchg
        exact hchg rfl
  | tabToTab X bb => exact rungAt_tabToTab h τ

/-- A rung increment is produced by a raise in that suit. -/
theorem rung_inc_shape {a b : State} {m : Move} (h : State.step a m = some b) {σ : Suit}
    (hinc : rungAt b σ = rungAt a σ + 1) :
    (∃ X : Card, m = Move.tabToFound X ∧ X.suit = σ) ∨
      (∃ X : Card, m = Move.wasteToFound X ∧ X.suit = σ) := by
  cases m with
  | draw => rw [rungAt_draw h σ] at hinc; exfalso; omega
  | wasteToFound X =>
      right
      rw [rungAt_wasteToFound h σ] at hinc
      by_cases hX : σ = X.suit
      · exact ⟨X, rfl, hX.symm⟩
      · rw [ite_eq_right hX] at hinc; exfalso; omega
  | wasteToTab X bb =>
      rw [rungAt_wasteToTab h σ] at hinc; exfalso; omega
  | tabToFound X =>
      left
      rw [rungAt_tabToFound h σ] at hinc
      by_cases hX : σ = X.suit
      · exact ⟨X, rfl, hX.symm⟩
      · rw [ite_eq_right hX] at hinc; exfalso; omega
  | foundToTab X bb =>
      rw [rungAt_foundToTab h σ] at hinc
      by_cases hX : σ = X.suit
      · rw [ite_eq_left hX] at hinc; exfalso; omega
      · rw [ite_eq_right hX] at hinc; exfalso; omega
  | tabToTab X bb =>
      rw [rungAt_tabToTab h σ] at hinc; exfalso; omega

/-- A rung decrement is produced by a pull in that suit. -/
theorem rung_dec_shape {a b : State} {m : Move} (h : State.step a m = some b) {σ : Suit}
    (hdec : rungAt b σ + 1 = rungAt a σ) :
    ∃ (X : Card) (bb : Base), m = Move.foundToTab X bb ∧ X.suit = σ := by
  cases m with
  | draw => rw [rungAt_draw h σ] at hdec; exact absurd hdec (Nat.succ_ne_self _)
  | wasteToFound X =>
      rw [rungAt_wasteToFound h σ] at hdec
      by_cases hX : σ = X.suit
      · rw [ite_eq_left hX] at hdec; exact absurd hdec (by omega)
      · rw [ite_eq_right hX] at hdec; exact absurd hdec (Nat.succ_ne_self _)
  | wasteToTab X bb =>
      rw [rungAt_wasteToTab h σ] at hdec; exact absurd hdec (Nat.succ_ne_self _)
  | tabToFound X =>
      rw [rungAt_tabToFound h σ] at hdec
      by_cases hX : σ = X.suit
      · rw [ite_eq_left hX] at hdec; exact absurd hdec (by omega)
      · rw [ite_eq_right hX] at hdec; exact absurd hdec (Nat.succ_ne_self _)
  | foundToTab X bb =>
      rw [rungAt_foundToTab h σ] at hdec
      by_cases hX : σ = X.suit
      · exact ⟨X, bb, rfl, hX.symm⟩
      · rw [ite_eq_right hX] at hdec; exact absurd hdec (Nat.succ_ne_self _)
  | tabToTab X bb =>
      rw [rungAt_tabToTab h σ] at hdec; exact absurd hdec (Nat.succ_ne_self _)

/-- A rung is unchanged by a raise/pull only in another suit. -/
theorem rung_eq_shape {a b : State} {m : Move} (h : State.step a m = some b) {σ : Suit}
    (heq : rungAt b σ = rungAt a σ) :
    (∀ X : Card, m = Move.tabToFound X → X.suit ≠ σ) ∧
      (∀ (X : Card) (bb : Base), m = Move.foundToTab X bb → X.suit ≠ σ) := by
  constructor
  · intro X hX
    subst hX
    intro hc
    rw [rungAt_tabToFound h σ, ite_eq_left hc.symm] at heq
    omega
  · intro X bb hX
    subst hX
    intro hc
    obtain ⟨c', htop, hc', -, -⟩ := step_foundToTab_inv h
    have htopX : a.foundTop X.suit = some X := by rw [hc'] at htop; exact htop
    have hposX : 0 < rungAt a X.suit := LedgerKit.rungAt_pos_of_foundTop htopX
    rw [rungAt_foundToTab h σ, ite_eq_left hc.symm] at heq
    rw [hc] at hposX
    omega

/-- A step moves each rung by at most one, in either direction. -/
theorem rung_step_tri {a b : State} {m : Move} (h : State.step a m = some b) (σ : Suit) :
    rungAt b σ = rungAt a σ ∨ rungAt b σ + 1 = rungAt a σ ∨
      rungAt b σ = rungAt a σ + 1 := by
  cases m with
  | draw => left; exact rungAt_draw h σ
  | wasteToFound X =>
      rw [rungAt_wasteToFound h σ]
      by_cases hX : σ = X.suit
      · rw [ite_eq_left hX]; right; right; omega
      · rw [ite_eq_right hX]; left; rfl
  | wasteToTab X bb => left; exact rungAt_wasteToTab h σ
  | tabToFound X =>
      rw [rungAt_tabToFound h σ]
      by_cases hX : σ = X.suit
      · rw [ite_eq_left hX]; right; right; omega
      · rw [ite_eq_right hX]; left; rfl
  | foundToTab X bb =>
      obtain ⟨c', htop, hc', -, -⟩ := step_foundToTab_inv h
      have htopX : a.foundTop X.suit = some X := by rw [hc'] at htop; exact htop
      have hposX : 0 < rungAt a X.suit := LedgerKit.rungAt_pos_of_foundTop htopX
      rw [rungAt_foundToTab h σ]
      by_cases hX : σ = X.suit
      · rw [ite_eq_left hX]
        rw [← hX] at hposX
        right; left; omega
      · rw [ite_eq_right hX]; left; rfl
  | tabToTab X bb => left; exact rungAt_tabToTab h σ

theorem rung_uT_spade : rungAt uT .spade = 2 := by decide
theorem rung_uT_club : rungAt uT .club = 3 := by decide
theorem rung_vT_spade : rungAt vT .spade = 3 := by decide
theorem rung_vT_club : rungAt vT .club = 2 := by decide

/-! ## §3.2 A generic two-letter `inv` lower bound -/

/-- **THE GENERIC RUNG ARGUMENT.**  If on a two-letter play the spade rung climbs
by exactly one and the club rung drops by exactly one, and no club pull is legal
at the origin, then the raise precedes the pull — so `inv ≥ 1`. -/
theorem inv_two_ge_generic {u v : State} {m1 m2 : Move}
    (hplay : ShufflePlayW u [m1, m2] v)
    (hspade : rungAt u .spade + 1 = rungAt v .spade)
    (hclub : rungAt v .club + 1 = rungAt u .club)
    (hnopull : ∀ (X : Card) (bb : Base), X.suit = .club →
      State.step u (Move.foundToTab X bb) = none) :
    1 ≤ Canon.inv [m1, m2] := by
  obtain ⟨s1, hrev1, hstep1, hplay2⟩ := Bubble.walk_cons_inv hplay
  obtain ⟨s2, hrev2, hstep2, -⟩ := Bubble.walk_cons_inv hplay2
  have hs2 : s2 = v := by
    have hr := Walk_run (fun st m => reversibleAtW st m) hplay2
    simp only [State.run, hstep2] at hr
    exact Option.some.inj hr
  rw [hs2] at hstep2
  have htri1 := rung_step_tri hstep1 .spade
  have htri2 := rung_step_tri hstep2 .spade
  have hmain : (∃ X : Card, m1 = Move.tabToFound X ∧ X.suit = .spade) ∨
      (∃ (X : Card) (bb : Base), m1 = Move.foundToTab X bb ∧ X.suit = .club) := by
    by_cases hinc : rungAt s1 .spade = rungAt u .spade + 1
    · rcases rung_inc_shape hstep1 hinc with ⟨X, hX, hs⟩ | ⟨X, hX, hs⟩
      · exact Or.inl ⟨X, hX, hs⟩
      · exact absurd (hX ▸ hrev1) (wasteToFound_not_reversibleAtW u X)
    · have hclimb : rungAt v .spade = rungAt s1 .spade + 1 := by omega
      rcases rung_inc_shape hstep2 hclimb with ⟨X, hX, hs⟩ | ⟨X, hX, hs⟩
      · have hchg : rungAt s1 .spade ≠ rungAt v .spade := by omega
        have hsame : rungAt s1 .club = rungAt v .club :=
          (rung_single_suit hstep2 (σ := .spade) (τ := .club) (by decide) hchg).symm
        have hdec : rungAt s1 .club + 1 = rungAt u .club := by
          rw [hsame]; exact hclub
        exact Or.inr (rung_dec_shape hstep1 hdec)
      · exact absurd (hX ▸ hrev2) (wasteToFound_not_reversibleAtW s1 X)
  rcases hmain with ⟨X, hX, hs⟩ | ⟨X, bb, hX, hs⟩
  · have hstep1' : State.step u (Move.tabToFound X) = some s1 := by
      rw [← hX]; exact hstep1
    have hsp1 : rungAt s1 .spade = rungAt u .spade + 1 := by
      rw [rungAt_tabToFound hstep1' .spade, ite_eq_left hs.symm]
    have hcl1 : rungAt s1 .club = rungAt u .club :=
      rung_single_suit hstep1' (σ := .spade) (τ := .club) (by decide) (by omega)
    have hdec : rungAt v .club + 1 = rungAt s1 .club := by
      rw [hcl1]; exact hclub
    obtain ⟨X2, bb2, hX2, hs2'⟩ := rung_dec_shape hstep2 hdec
    subst hX
    subst hX2
    have hne : X.suit ≠ X2.suit := by rw [hs, hs2']; decide
    show 1 ≤ Canon.inv [Move.tabToFound X, Move.foundToTab X2 bb2]
    simp [Canon.inv, Canon.invAux, Canon.cnt, hne]
  · rw [hX] at hstep1
    rw [hnopull X bb hs] at hstep1
    cases hstep1

/-- **THE TWIN BOARD'S TWO-LETTER `inv` LOWER BOUND.** -/
theorem inv_two_ge (m1 m2 : Move) (hplay : ShufflePlayW uT [m1, m2] vT) :
    1 ≤ Canon.inv [m1, m2] := by
  refine inv_two_ge_generic hplay ?_ ?_ ?_
  · rw [rung_uT_spade, rung_vT_spade]
  · rw [rung_vT_club, rung_uT_club]
  · intro X bb hX
    cases h : State.step uT (Move.foundToTab X bb) with
    | none => rfl
    | some s' =>
        obtain ⟨c', htop, hc', -, -⟩ := step_foundToTab_inv h
        have hft : uT.foundTop X.suit = some X := by rw [hc'] at htop; exact htop
        rw [hX] at hft
        have hftC : uT.foundTop .club = some C3 := by decide
        rw [hftC] at hft
        have hX3 : X = C3 := (Option.some.inj hft).symm
        rw [hX3] at h
        rw [uT_pull_club_none bb] at h
        cases h

/-- **EVERY SHORTEST PLAY HAS `inv ≥ 1`.** -/
theorem inv_ge_T (ρ' : List Move) (hplay : ShufflePlayW uT ρ' vT)
    (hlen : ρ'.length = [mRT, mPT].length) : Canon.inv [mRT, mPT] ≤ Canon.inv ρ' := by
  have hlen2 : ρ'.length = 2 := by simpa using hlen
  have hinv : Canon.inv [mRT, mPT] = 1 := by decide
  rw [hinv]
  cases ρ' with
  | nil => simp at hlen2
  | cons m1 t =>
      cases t with
      | nil => simp at hlen2
      | cons m2 rest =>
          have hrest : rest = [] := by simpa using hlen2
          subst hrest
          exact inv_two_ge m1 m2 hplay

/-- **THE TWIN CORRIDOR IS SHORTEST.** -/
theorem shortest_T (ρ' : List Move) (hplay : ShufflePlayW uT ρ' vT) :
    [mRT, mPT].length ≤ ρ'.length := by
  have h := MtnPr.twoSuit_gap_is_shortest stepR_T stepP_T crossSuitT ρ' hplay
  simpa using h
/-! ## §4. The residual minus its `SSaturated` endpoints is FALSE -/

/-- **`NoSeatMateCrossSuitUnsat`** — `Blocks.NoSeatMateCrossSuit` with only the
two `SSaturated` endpoint hypotheses deleted.  Everything else is kept: `WF`
origin, witness play, shortest, `inv`-minimal among shortest plays, the exact
corridor decomposition, `FreeOnly`, cross-suit, `Pullable` at the raise's image,
read-safety and seat-inertness, and seat-mate cards. -/
def NoSeatMateCrossSuitUnsat : Prop :=
  ∀ (u v : State) (ρ pre γ tail : List Move) (c d : Card) (b : Base) (A B : State),
    u.WF →
    ShufflePlayW u ρ v →
    (∀ ρ' : List Move, ShufflePlayW u ρ' v → ρ.length ≤ ρ'.length) →
    (∀ ρ' : List Move, ShufflePlayW u ρ' v → ρ'.length = ρ.length →
      Canon.inv ρ ≤ Canon.inv ρ') →
    ρ = pre ++ (Move.tabToFound c :: (γ ++ (Move.foundToTab d b :: tail))) →
    Canon.FreeOnly γ → c.suit ≠ d.suit → ShufflePlayW u pre A →
    State.step A (Move.tabToFound c) = some B → PullKit.Pullable B d b →
    (∀ q ∈ γ, SlideFwd.ReadSafe d q) → (∀ q ∈ γ, MtnPr.SeatInert b q) →
    SeatMate c d → False

/-- **SHAPE 3 (TWIN) IS REAL IN A CANONICAL PLAY.**  The twin corridor
`raise ♠3 ; pull ♣3 onto ♥4` is a `WF`, shortest, `inv`-minimal witness play
with every corridor hypothesis of `Blocks.canonical_corridor_seatMate`, and
`♣3 = (♠3).twin`.  Only the `SSaturated` endpoints fail — `uT` has `♠3`
raisable and `vT` has `♣3` raisable. -/
theorem twin_refutes_unsat : ¬ NoSeatMateCrossSuitUnsat := by
  intro h
  exact h uT vT [mRT, mPT] [] [] [] S3 C3 (Sum.inr H4) uT BT
    uT_wf playT shortest_T inv_ge_T rfl freeOnlyT crossSuitT
    (Walk.nil uT) stepR_T pullableT
    (fun q hq => (List.not_mem_nil hq).elim)
    (fun q hq => (List.not_mem_nil hq).elim)
    seatMateT

/-! ## §5. Shape 1 (the king swap) is real too -/

def SK : Card := ⟨.spade, .king⟩
def CK : Card := ⟨.club, .king⟩

def H2 : Card := ⟨.heart, .two⟩
def H3 : Card := ⟨.heart, .three⟩
def H4f : Card := ⟨.heart, .four⟩
def H5f : Card := ⟨.heart, .five⟩
def H6f : Card := ⟨.heart, .six⟩
def H7f : Card := ⟨.heart, .seven⟩

def stockK : List Card :=
  Card.universe.filter (fun c =>
    decide (c.suit ≠ .spade) && decide (c.suit ≠ .club) &&
      decide (c ≠ H2) && decide (c ≠ H3) && decide (c ≠ H4f) &&
      decide (c ≠ H5f) && decide (c ≠ H6f) && decide (c ≠ H7f))

/-- **THE KING BOARD.**  `p0` is the bare king seat `⟨[], [♠K]⟩`, the spade
foundation is at height 12 (`♠K` is `nextUp`), the club foundation is complete
with `♣K` on top.  Every other pile holds a filler card, so no `inl` base is
empty and `♣K` is pullable nowhere at the origin. -/
def uK : State :=
  { found := fun s => match s with
      | .spade => (Suit.upCards .spade).take 12
      | .club => Suit.upCards .club
      | _ => []
    piles := fun a => match a with
      | .p0 => ⟨[], [SK]⟩
      | .p1 => ⟨[], [H2]⟩
      | .p2 => ⟨[], [H3]⟩
      | .p3 => ⟨[], [H4f]⟩
      | .p4 => ⟨[], [H5f]⟩
      | .p5 => ⟨[], [H6f]⟩
      | .p6 => ⟨[], [H7f]⟩
    stock := stockK
    waste := []
    drawStep := 1 }

theorem uK_wf_found : ∀ s : Suit, ∃ n, uK.found s = s.upCards.take n := by
  intro s
  cases s with
  | spade => exact ⟨12, rfl⟩
  | club => exact ⟨13, by rw [← Suit.upCards_length]; exact (List.take_length).symm⟩
  | heart => exact ⟨0, rfl⟩
  | diamond => exact ⟨0, rfl⟩

theorem uK_wf_runs : ∀ a : Anchor, runOK (uK.piles a).faceUp = true := by
  intro a
  cases a <;> decide

theorem uK_wf_count : ∀ c ∈ Card.universe, uK.cardCount c = 1 := by
  intro c _
  rcases c with ⟨s, r⟩
  cases s <;> cases r <;> decide

theorem uK_wf : uK.WF := ⟨uK_wf_found, uK_wf_runs, uK_wf_count, by decide⟩

def mRK : Move := Move.tabToFound SK
def mPK : Move := Move.foundToTab CK (Sum.inl .p0)

def BK : State :=
  (uK.setFound .spade (uK.found .spade ++ [SK])).setPile .p0
    (Pile.afterRunRemoved (uK.piles .p0) (chop (uK.piles .p0).faceUp))

def vK : State := (BK.setFound .club (chop (BK.found .club))).putCard CK (Sum.inl .p0)

theorem uK_next : uK.nextUp SK = true := by decide
theorem uK_pileOfTop : uK.pileOfTop SK = some .p0 := by decide
theorem uK_chop : chop (uK.piles .p0).faceUp = [] := rfl

theorem stepR_K : State.step uK mRK = some BK := by
  show State.step uK (Move.tabToFound SK) = some BK
  rw [step_tabToFound_splice uK_next uK_pileOfTop]
  rfl

theorem BK_foundTop_club : BK.foundTop .club = some CK := by decide
theorem BK_canPlace : BK.canPlace CK (Sum.inl .p0) = true := by decide

theorem stepP_K : State.step BK mPK = some vK := by
  show State.step BK (Move.foundToTab CK (Sum.inl .p0)) = some vK
  rw [step_foundToTab_splice BK_foundTop_club BK_canPlace]
  rfl

theorem BK_wf : BK.WF := step_wf uK_wf stepR_K
theorem vK_wf : vK.WF := step_wf BK_wf stepP_K

theorem revR_K : reversibleAtW uK mRK :=
  (tabToFoundR_iff_reversibleAtW uK_wf SK).mp (by decide)

theorem revP_K : reversibleAtW BK mPK :=
  (foundToTabR_iff_reversibleAtW BK_wf CK (Sum.inl .p0)).mp (by decide)

theorem playK : ShufflePlayW uK [mRK, mPK] vK :=
  Walk.cons revR_K stepR_K (Walk.cons revP_K stepP_K (Walk.nil vK))

theorem freeOnlyK : Canon.FreeOnly ([] : List Move) := fun m hm => (List.not_mem_nil hm).elim
theorem crossSuitK : SK.suit ≠ CK.suit := by decide
theorem pullableK : PullKit.Pullable BK CK (Sum.inl .p0) :=
  ⟨BK_foundTop_club, BK_canPlace⟩
theorem seatMateK : SeatMate SK CK := Or.inl ⟨rfl, rfl⟩

theorem rung_uK_spade : rungAt uK .spade = 12 := by decide
theorem rung_uK_club : rungAt uK .club = 13 := by decide
theorem rung_vK_spade : rungAt vK .spade = 13 := by decide
theorem rung_vK_club : rungAt vK .club = 12 := by decide

theorem uK_canPlace_CK_false : ∀ b : Base, uK.canPlace CK b = false := by
  intro b
  cases b with
  | inl a =>
      rw [canPlace_inl_unfold]
      rw [show (uK.piles a).isEmpty = false from by cases a <;> decide]
      simp
  | inr y =>
      rw [canPlace_inr_eq]
      cases h : uK.pileOfTop y with
      | none => rfl
      | some k =>
          show canSitOn CK y = false
          have hnt : CK.rank.toIdx + 1 ≠ y.rank.toIdx := by
            intro hh
            have h12 : CK.rank.toIdx = 12 := rfl
            rw [h12] at hh
            have := Rank.toIdx_lt y.rank
            omega
          unfold canSitOn
          rw [decide_eq_false_iff_not.mpr hnt]
          simp

theorem uK_pull_CK_none (b : Base) : State.step uK (Move.foundToTab CK b) = none := by
  have hft : uK.foundTop CK.suit = some CK := by decide
  have hcp : uK.canPlace CK b = false := uK_canPlace_CK_false b
  rw [show State.step uK (Move.foundToTab CK b) =
    (match uK.foundTop CK.suit with
     | some c' => if decide (c' = CK) && uK.canPlace CK b then
         some ((uK.setFound CK.suit (chop (uK.found CK.suit))).putCard CK b)
       else none
     | none => none) from rfl]
  rw [hft, hcp]
  simp

/-- **THE KING BOARD'S TWO-LETTER `inv` LOWER BOUND.** -/
theorem inv_two_ge_K (m1 m2 : Move) (hplay : ShufflePlayW uK [m1, m2] vK) :
    1 ≤ Canon.inv [m1, m2] := by
  refine inv_two_ge_generic hplay ?_ ?_ ?_
  · rw [rung_uK_spade, rung_vK_spade]
  · rw [rung_vK_club, rung_uK_club]
  · intro X bb hX
    cases h : State.step uK (Move.foundToTab X bb) with
    | none => rfl
    | some s' =>
        obtain ⟨c', htop, hc', -, -⟩ := step_foundToTab_inv h
        have hft : uK.foundTop X.suit = some X := by rw [hc'] at htop; exact htop
        rw [hX] at hft
        have hftC : uK.foundTop .club = some CK := by decide
        rw [hftC] at hft
        have hX3 : X = CK := (Option.some.inj hft).symm
        rw [hX3] at h
        rw [uK_pull_CK_none bb] at h
        cases h

theorem inv_ge_K (ρ' : List Move) (hplay : ShufflePlayW uK ρ' vK)
    (hlen : ρ'.length = [mRK, mPK].length) : Canon.inv [mRK, mPK] ≤ Canon.inv ρ' := by
  have hlen2 : ρ'.length = 2 := by simpa using hlen
  have hinv : Canon.inv [mRK, mPK] = 1 := by decide
  rw [hinv]
  cases ρ' with
  | nil => simp at hlen2
  | cons m1 t =>
      cases t with
      | nil => simp at hlen2
      | cons m2 rest =>
          have hrest : rest = [] := by simpa using hlen2
          subst hrest
          exact inv_two_ge_K m1 m2 hplay

theorem shortest_K (ρ' : List Move) (hplay : ShufflePlayW uK ρ' vK) :
    [mRK, mPK].length ≤ ρ'.length := by
  have h := MtnPr.twoSuit_gap_is_shortest stepR_K stepP_K crossSuitK ρ' hplay
  simpa using h

/-- **SHAPE 1 (BOTH KINGS) IS REAL IN A CANONICAL PLAY.**  `raise ♠K ; pull ♣K
onto the emptied bare seat` is a `WF`, shortest, `inv`-minimal witness play
meeting every corridor hypothesis of `Blocks.canonical_corridor_seatMate`, with
both cards kings.  Only the `SSaturated` endpoints fail. -/
theorem king_refutes_unsat : ¬ NoSeatMateCrossSuitUnsat := by
  intro h
  exact h uK vK [mRK, mPK] [] [] [] SK CK (Sum.inl .p0) uK BK
    uK_wf playK shortest_K inv_ge_K rfl freeOnlyK crossSuitK
    (Walk.nil uK) stepR_K pullableK
    (fun q hq => (List.not_mem_nil hq).elim)
    (fun q hq => (List.not_mem_nil hq).elim)
    seatMateK

/-! ## §6. The card-class count, done correctly

CORRECTION (load-bearing for the twin lane).  In this game the face-up run is
**bottom-first and ranks strictly INCREASE downward**: `canSitOn x y` unfolds to
`x.rank.toIdx + 1 = y.rank.toIdx`, i.e. the card ABOVE has the LOWER rank.  With
`z` directly BELOW `c` (shape 3 of `Blocks.inr_expose_shape`) the fit is
therefore

```text
c.rank.toIdx + 1 = z.rank.toIdx      (z is one rank ABOVE c)
z.suit.color ≠ c.suit.color
```

(`expose_z_fit`).  A card that may be placed on `d = c.twin` satisfies
`x.rank.toIdx + 1 = d.rank.toIdx` with `x`'s colour opposite `d`'s, and
`d.rank = c.rank` — hence

```text
x.rank.toIdx + 2 = z.rank.toIdx      and      x.suit.color = z.suit.color
```

(`twin_cover_rank`).  So the `d`-cover class is the twin pair of cards of rank
`c.rank − 1` in `z`'s colour (`twin_cover_pair`), and in particular the exposed
card `z` and its twin are NEVER placements on `d` (`twin_cover_ne`).  The class
count therefore does not produce a collision with `z`: the chain descends two
ranks at a time and cannot repeat a card.  This is why the handoff's counting
argument does not close the twin case (see `Temp/Seat_Report.md` §3).
-/

/-- Cards of one rank and one colour are a two-card class: a card is itself or
its twin. -/
theorem eq_or_twin_of_rank_color {x y : Card} (hr : x.rank = y.rank)
    (hc : x.suit.color = y.suit.color) : x = y ∨ x = y.twin := by
  rcases x with ⟨sx, rx⟩
  rcases y with ⟨sy, ry⟩
  simp only at hr hc
  subst hr
  by_cases h : sx = sy
  · left; rw [h]
  · right
    have hsym : sy = sx.twin := by
      cases sx <;> cases sy <;> simp_all [Suit.color, Suit.twin]
    simp [Card.twin, hsym]

/-- **THE EXPOSURE'S FIT.**  `z` sits directly below `c` in a legal run, so `z`
is one rank ABOVE `c` and of the opposite colour. -/
theorem expose_z_fit {A : State} {c z : Card} {a : Anchor} {front : List Card}
    (hrun : runOK (A.piles a).faceUp = true)
    (hface : (A.piles a).faceUp = front ++ [z, c]) :
    c.rank.toIdx + 1 = z.rank.toIdx ∧ z.suit.color ≠ c.suit.color := by
  have hcz : canSitOn c z = true := by
    rw [hface] at hrun
    exact SeedKit.runOK_adjacent_fit z c front [] hrun
  obtain ⟨h1, h2⟩ := (canSitOn_eq c z).mp hcz
  exact ⟨h1, Ne.symm h2⟩

/-- **THE `d`-COVER CLASS SITS TWO RANKS BELOW `z`, IN `z`'s COLOUR.** -/
theorem twin_cover_rank {c d z x : Card} (hd : d = c.twin)
    (hzr : c.rank.toIdx + 1 = z.rank.toIdx) (hzc : z.suit.color ≠ c.suit.color)
    (hxr : x.rank.toIdx + 1 = d.rank.toIdx) (hxc : x.suit.color ≠ d.suit.color) :
    x.rank.toIdx + 2 = z.rank.toIdx ∧ x.suit.color = z.suit.color := by
  have hdr : d.rank.toIdx = c.rank.toIdx := by rw [hd, Card.twin]
  have hdcol : d.suit.color = c.suit.color := by
    rw [hd, Card.twin]; exact Suit.color_twin c.suit
  have hzc' : z.suit.color ≠ d.suit.color := by rw [hdcol]; exact hzc
  refine ⟨by omega, ?_⟩
  exact Blocks.color_eq_of_ne_ne hxc hzc'

/-- **THE `d`-COVER CLASS IS A TWIN PAIR.**  Any two cards that may sit on `d`
are equal or twins. -/
theorem twin_cover_pair {d x y : Card}
    (hxr : x.rank.toIdx + 1 = d.rank.toIdx) (hxc : x.suit.color ≠ d.suit.color)
    (hyr : y.rank.toIdx + 1 = d.rank.toIdx) (hyc : y.suit.color ≠ d.suit.color) :
    x = y ∨ x = y.twin := by
  have hrank : x.rank = y.rank := by
    apply Rank.toIdx_inj
    omega
  have hcol : x.suit.color = y.suit.color :=
    Blocks.color_eq_of_ne_ne hxc hyc
  exact eq_or_twin_of_rank_color hrank hcol

/-- **THE EXPOSED CARD IS NEVER A COVER OF THE TWIN'S PULL.**  With `z` one rank
above `c` and `d.rank = c.rank`, a card that may sit on `d` has rank `c.rank − 1`
— never `z`'s rank and never its twin's. -/
theorem twin_cover_ne {c d z x : Card} (hd : d = c.twin)
    (hzr : c.rank.toIdx + 1 = z.rank.toIdx)
    (hxr : x.rank.toIdx + 1 = d.rank.toIdx) :
    x ≠ z ∧ x ≠ z.twin := by
  have hdr : d.rank.toIdx = c.rank.toIdx := by rw [hd, Card.twin]
  constructor
  · intro h
    rw [h] at hxr
    omega
  · intro h
    have hrank : x.rank = z.rank := by rw [h, Card.twin_rank]
    rw [hrank] at hxr
    omega

/-- **A COVER OF A KING IS A QUEEN.**  In the king corridor (`d` a king), every
card that may sit on `d` — cover-slide mover or pull-onto card — has rank
`queen`; its two-card class is the queen pair of the opposite colour.  So the
chain descending from a king starts one full rank below it. -/
theorem king_cover_is_queen {d x : Card} (hd : d.rank = Rank.king)
    (hxr : x.rank.toIdx + 1 = d.rank.toIdx) : x.rank = Rank.queen := by
  have hd12 : d.rank.toIdx = 12 := by rw [hd]; rfl
  apply Rank.toIdx_inj
  rw [show Rank.queen.toIdx = 11 from rfl]
  omega

/-! ## §7. The witness endpoints are not saturated -/

theorem uT_canRaise_S3 : CanRaise uT S3 :=
  ⟨uT_next, .p0, uT_pileOfTop, Or.inl (by decide)⟩

theorem uT_not_sat : ¬ SSaturated uT := fun h => h S3 (CanRaiseS.now S3 uT_canRaise_S3)

theorem vT_canRaise_C3 : CanRaise vT C3 :=
  ⟨(by decide : vT.nextUp C3 = true), .p0,
    (by decide : vT.pileOfTop C3 = some .p0), Or.inl (by decide)⟩

theorem vT_not_sat : ¬ SSaturated vT := fun h => h C3 (CanRaiseS.now C3 vT_canRaise_C3)

theorem uK_canRaise_SK : CanRaise uK SK :=
  ⟨uK_next, .p0, uK_pileOfTop, Or.inr ⟨rfl, rfl⟩⟩

theorem uK_not_sat : ¬ SSaturated uK := fun h => h SK (CanRaiseS.now SK uK_canRaise_SK)

theorem vK_canRaise_CK : CanRaise vK CK :=
  ⟨(by decide : vK.nextUp CK = true), .p0,
    (by decide : vK.pileOfTop CK = some .p0), Or.inr ⟨rfl, rfl⟩⟩

theorem vK_not_sat : ¬ SSaturated vK := fun h => h CK (CanRaiseS.now CK vK_canRaise_CK)

end Seat

/-! ## §8. Axiom battery

Expected: every row `[]`, `[propext]` or `[propext, Quot.sound]` — no
`sorryAx`, no `Classical.choice`, no `Lean.ofReduceBool` (`native_decide`). -/

#print axioms Seat.uT_wf
#print axioms Seat.BT_wf
#print axioms Seat.vT_wf
#print axioms Seat.playT
#print axioms Seat.pullableT
#print axioms Seat.seatMateT
#print axioms Seat.freeOnlyT
#print axioms Seat.rung_single_suit
#print axioms Seat.rung_inc_shape
#print axioms Seat.rung_dec_shape
#print axioms Seat.rung_step_tri
#print axioms Seat.uT_canPlace_club_false
#print axioms Seat.uT_pull_club_none
#print axioms Seat.inv_two_ge_generic
#print axioms Seat.inv_two_ge
#print axioms Seat.inv_ge_T
#print axioms Seat.shortest_T
#print axioms Seat.NoSeatMateCrossSuitUnsat
#print axioms Seat.twin_refutes_unsat
#print axioms Seat.uK_wf
#print axioms Seat.BK_wf
#print axioms Seat.vK_wf
#print axioms Seat.playK
#print axioms Seat.pullableK
#print axioms Seat.seatMateK
#print axioms Seat.uK_canPlace_CK_false
#print axioms Seat.inv_two_ge_K
#print axioms Seat.inv_ge_K
#print axioms Seat.shortest_K
#print axioms Seat.king_refutes_unsat
#print axioms Seat.eq_or_twin_of_rank_color
#print axioms Seat.expose_z_fit
#print axioms Seat.twin_cover_rank
#print axioms Seat.twin_cover_pair
#print axioms Seat.twin_cover_ne
#print axioms Seat.king_cover_is_queen
#print axioms Seat.uT_not_sat
#print axioms Seat.vT_not_sat
#print axioms Seat.uK_not_sat
#print axioms Seat.vK_not_sat
