import Orig2.ForkSeat
import Orig2.FiberTransfer

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-!
# Orig2/ForkSatChain — the cover-chain residual is FALSE, and what is left

Scratch card.  READ-ONLY on `Orig2/`; no source edit, no commit.
Zero `sorry`, zero `Classical.choice`, zero `nativeDecide`, no `decide` on
`State` equality.

## Verdict

`Chain.CoverChainResidual` (`Orig2/ForkChain.lean:441`) — the "exact residual"
of the cover chain, and the hypothesis of the campaign's only chain-to-corridor
reduction `Chain.freeCorridor_of_coverChain` — is **FALSE**, and it is false at
its *first* disjunct.

`Chain.NoChainRaise` (`:455`) is refuted by the twin board of
`Orig2/ForkSeat.lean` itself: take `B = Seat.uT`, `v = Seat.BT` (the raise
image, which IS `SSaturated`), `d = z' = ♠3`, `tail = [raise ♠3]`.  Every
hypothesis holds.  This is *not* an artefact of a weird board: `Seat.BT` is
exactly the state the promoted twin witness raises into.

`Chain.NoChainRaise` cannot be repaired by excluding the trivial
`(s1 = [], z' = d)` case either: a two-raise board (two singleton-headed
raisable cells) gives `s1 = [raise ♠3] ≠ []`, `z' = ♦3 ≠ d`, into a saturated
endpoint.  The chain residual quantifies over **arbitrary plays** `B → v`, not
over corridor tails, so no patching of the raise clause can save it:
shortest-ness (the corridor's own minimality) is nowhere in its hypotheses.

Consequence: `Chain.freeCorridor_of_coverChain` is vacuously true and carries
no information; `Temp/Chain_Report.md` §4's "the residual is genuinely the
saturation lock, now stated at event level" is withdrawn by this card.

## What survives

The chain idea is **right at the corridor and wrong in the abstract**.  Two
kernel-checked rows say exactly how much survives:

* `corridor_tail_head_ne_raise` — in a *shortest* corridor play the tail does
  not begin with `raise d`: that would be an adjacent `pull d ; raise d`, and
  `Bridge.adjacent_same_turn_shortens` deletes it.  (`SSaturated v` is not even
  needed.)  This is the one part of the raise case shortest-ness kills.
* `twin_tail_raises_d` — in the **twin** branch (`d = c.twin`) with a
  **pull-free** tail, the tail *must* raise `d`.  Reason: `Direct`'s
  `canRaiseS_end_or_bad_raise` says a pull-free leg can only kill `d`'s
  S-licence by `raise d` or `raise d.twin`; but `d.twin = c` is the corridor's
  raised card, hence a foundation top for the whole tail (no pulls), hence never
  a pile top, hence never raised.  So the cover obligation collapses from four
  shapes to the single same-card relocation `pull d ; (pull-free) ; raise d`.

`TwinRelocationResidual` names that one shape.  It is the honest residual of the
twin/pull-free corner, and it is what `NoSeatMateCrossSuit` reduces to there.
-/

namespace Sat

/-! ## §0. `Seat.BT` — the twin witness's raise image — is saturated -/

/-- The `canRaiseSB` licence probe is false at every card of `Seat.BT`. -/
theorem BT_liveB_false (c : Card) : canRaiseSB Seat.BT c = false := by
  rcases c with ⟨s, r⟩
  cases s <;> cases r <;> decide

/-- **THE TWIN WITNESS'S RAISE IMAGE IS `SSaturated`** (cascade grade: the
probe is the flat characterization, so the cargo closure is already read). -/
theorem BT_sat : SSaturated Seat.BT := by
  intro c hS
  have h1 : canRaiseSB Seat.BT c = true := (canRaiseSB_iff Seat.BT_wf).mpr hS
  have h2 : canRaiseSB Seat.BT c = false := BT_liveB_false c
  rw [h2] at h1
  cases h1

/-- `♠3` is nowhere a pile top at `Seat.BT`: the raise founded it. -/
theorem BT_pileOfTop_S3 : Seat.BT.pileOfTop Seat.S3 = none := by decide

/-- Hence `♠3` is not raisable at `Seat.BT`. -/
theorem not_canRaise_BT_S3 : ¬ CanRaise Seat.BT Seat.S3 := by
  rintro ⟨-, a, ha, -⟩
  rw [BT_pileOfTop_S3] at ha
  exact absurd ha (by simp)

/-- The one-letter witness play `♠3`-raise from the twin board to its image. -/
theorem playTail : ShufflePlayW Seat.uT [Move.tabToFound Seat.S3] Seat.BT :=
  Walk.cons Seat.revR_T Seat.stepR_T (Walk.nil Seat.BT)

/-- **`Chain.NoChainRaise` IS FALSE.**  The counterexample is the promoted twin
board's own first letter: `B = Seat.uT`, `v = Seat.BT` (saturated), `d = z' = ♠3`,
`tail = [raise ♠3]`, `s1 = s2 = []`, `A = Seat.uT`, `Z = Seat.BT`.  Every
hypothesis of the definition holds, and its conclusion is `False`. -/
theorem not_noChainRaise : ¬ Chain.NoChainRaise := by
  intro h
  exact h Seat.uT Seat.BT [Move.tabToFound Seat.S3] Seat.S3
    Seat.uT_wf BT_sat Seat.uT_canRaise_S3 playTail
    Seat.S3 [] [] Seat.uT Seat.BT (Nat.le_refl _) rfl (Walk.nil Seat.uT)
    Seat.uT_canRaise_S3 Seat.stepR_T not_canRaise_BT_S3

/-- **`Chain.CoverChainResidual` IS FALSE**: its first disjunct already is. -/
theorem not_coverChainResidual : ¬ Chain.CoverChainResidual := fun h =>
  not_noChainRaise (Chain.coverChainResidual_iff.mp h).1

/-- The reduction's hypothesis is unsatisfiable, so the reduction proves
nothing: it is a kernel-checked implication from a false premise. -/
theorem coverChain_reduction_vacuous :
    (Chain.CoverChainResidual → CrossSuit.CrossSuitFreeCorridorResidual) ∧
      ¬ Chain.CoverChainResidual :=
  ⟨Chain.freeCorridor_of_coverChain, not_coverChainResidual⟩

/-! ## §1. The trivial-case repair does not help

The obvious patch is to demand `¬ (s1 = [] ∧ z' = d)`, i.e. to exclude the
case where the tail's *first* letter re-raises the card just pulled.  A board
with two raisable singleton-headed cells refutes even that: raise the spade
cell, then raise the diamond cell, and the second raise is the chain's
terminal with `s1 = [raise ♠3] ≠ []` and `z' = ♦3 ≠ ♠3`.

Board `u2`: `p0 = ⟨[], [♥4, ♠3]⟩`, `p1 = ⟨[], [♣4, ♦3]⟩`, spade and diamond
foundations at height 2, everything else in the stock.  After both raises every
pile top (`♥4`, `♣4`) is unraisable and no cargo leg exists. -/

def SH4 : Card := ⟨.heart, .four⟩
def C4c : Card := ⟨.club, .four⟩
def D3c : Card := ⟨.diamond, .three⟩
def SAc : Card := ⟨.spade, .ace⟩
def S2c : Card := ⟨.spade, .two⟩
def DAc : Card := ⟨.diamond, .ace⟩
def D2c : Card := ⟨.diamond, .two⟩

def stock2 : List Card :=
  Card.universe.filter (fun c =>
    decide (c ≠ SAc) && decide (c ≠ S2c) && decide (c ≠ Seat.S3) &&
      decide (c ≠ DAc) && decide (c ≠ D2c) && decide (c ≠ D3c) &&
      decide (c ≠ SH4) && decide (c ≠ C4c))

/-- The two-cell board. -/
def u2 : State :=
  { found := fun s => match s with
      | .spade => [SAc, S2c]
      | .diamond => [DAc, D2c]
      | _ => []
    piles := fun a => match a with
      | .p0 => ⟨[], [SH4, Seat.S3]⟩
      | .p1 => ⟨[], [C4c, D3c]⟩
      | _ => ⟨[], []⟩
    stock := stock2
    waste := []
    drawStep := 1 }

theorem u2_wf_found : ∀ s : Suit, ∃ n, u2.found s = s.upCards.take n := by
  intro s
  cases s with
  | spade => exact ⟨2, rfl⟩
  | diamond => exact ⟨2, rfl⟩
  | heart => exact ⟨0, rfl⟩
  | club => exact ⟨0, rfl⟩

theorem u2_wf_runs : ∀ a : Anchor, runOK (u2.piles a).faceUp = true := by
  intro a
  cases a <;> decide

theorem u2_wf_count : ∀ c ∈ Card.universe, u2.cardCount c = 1 := by
  intro c _
  rcases c with ⟨s, r⟩
  cases s <;> cases r <;> decide

theorem u2_wf : u2.WF := ⟨u2_wf_found, u2_wf_runs, u2_wf_count, by decide⟩

/-- The intermediate state: `♠3` raised. -/
def u2A : State :=
  (u2.setFound .spade (u2.found .spade ++ [Seat.S3])).setPile .p0
    (Pile.afterRunRemoved (u2.piles .p0) (chop (u2.piles .p0).faceUp))

/-- The endpoint: both `♠3` and `♦3` raised. -/
def u2v : State :=
  (u2A.setFound .diamond (u2A.found .diamond ++ [D3c])).setPile .p1
    (Pile.afterRunRemoved (u2A.piles .p1) (chop (u2A.piles .p1).faceUp))

theorem u2_next_S3 : u2.nextUp Seat.S3 = true := by decide
theorem u2_pileOfTop_S3 : u2.pileOfTop Seat.S3 = some .p0 := by decide
theorem u2_chop_p0 : chop (u2.piles .p0).faceUp = [SH4] := rfl

theorem u2_step_raise_S3 : State.step u2 (Move.tabToFound Seat.S3) = some u2A := by
  show State.step u2 (Move.tabToFound Seat.S3) = some u2A
  rw [step_tabToFound_splice u2_next_S3 u2_pileOfTop_S3]
  rfl

theorem u2_rev_raise_S3 : reversibleAtW u2 (Move.tabToFound Seat.S3) :=
  (tabToFoundR_iff_reversibleAtW u2_wf Seat.S3).mp (by decide)

theorem u2A_wf : u2A.WF := step_wf u2_wf u2_step_raise_S3

theorem u2A_next_D3 : u2A.nextUp D3c = true := by decide
theorem u2A_pileOfTop_D3 : u2A.pileOfTop D3c = some .p1 := by decide
theorem u2A_chop_p1 : chop (u2A.piles .p1).faceUp = [C4c] := rfl

theorem u2A_step_raise_D3 : State.step u2A (Move.tabToFound D3c) = some u2v := by
  show State.step u2A (Move.tabToFound D3c) = some u2v
  rw [step_tabToFound_splice u2A_next_D3 u2A_pileOfTop_D3]
  rfl

theorem u2A_rev_raise_D3 : reversibleAtW u2A (Move.tabToFound D3c) :=
  (tabToFoundR_iff_reversibleAtW u2A_wf D3c).mp (by decide)

theorem u2v_wf : u2v.WF := step_wf u2A_wf u2A_step_raise_D3

theorem u2v_liveB_false (c : Card) : canRaiseSB u2v c = false := by
  rcases c with ⟨s, r⟩
  cases s <;> cases r <;> decide

/-- The two-raise endpoint is saturated. -/
theorem u2v_sat : SSaturated u2v := by
  intro c hS
  have h1 : canRaiseSB u2v c = true := (canRaiseSB_iff u2v_wf).mpr hS
  have h2 : canRaiseSB u2v c = false := u2v_liveB_false c
  rw [h2] at h1
  cases h1

theorem u2_play_raise : ShufflePlayW u2 [Move.tabToFound Seat.S3] u2A :=
  Walk.cons u2_rev_raise_S3 u2_step_raise_S3 (Walk.nil u2A)

/-- `♦3` is not raisable at the two-raise endpoint. -/
theorem u2v_not_canRaise_D3 : ¬ CanRaise u2v D3c := by
  rintro ⟨-, a, ha, -⟩
  rw [show u2v.pileOfTop D3c = none from by decide] at ha
  exact absurd ha (by simp)

/-- **THE TRIVIAL-CASE REPAIR IS FALSE TOO.**  `s1 = [raise ♠3] ≠ []` and
`z' = ♦3 ≠ ♠3`, into the saturated endpoint `u2v`. -/
theorem not_noChainRaiseCorr :
    ¬ (∀ (B v : State) (tail : List Move) (d : Card),
        B.WF → SSaturated v → CanRaise B d → ShufflePlayW B tail v →
        ∀ (z' : Card) (s1 s2 : List Move) (A Z : State),
          z'.rank.toIdx ≤ d.rank.toIdx →
          tail = s1 ++ Move.tabToFound z' :: s2 → ShufflePlayW B s1 A →
          CanRaise A z' → State.step A (Move.tabToFound z') = some Z →
          ¬ CanRaise Z z' → ¬ (s1 = [] ∧ z' = d) → False) := by
  intro h
  refine h u2 u2v [Move.tabToFound Seat.S3, Move.tabToFound D3c] Seat.S3
    u2_wf u2v_sat ⟨u2_next_S3, .p0, u2_pileOfTop_S3, Or.inl (by decide)⟩
    (Walk.cons u2_rev_raise_S3 u2_step_raise_S3
      (Walk.cons u2A_rev_raise_D3 u2A_step_raise_D3 (Walk.nil u2v)))
    D3c [Move.tabToFound Seat.S3] [] u2A u2v
    (by decide) rfl u2_play_raise
    ⟨u2A_next_D3, .p1, u2A_pileOfTop_D3, Or.inl (by decide)⟩
    u2A_step_raise_D3 u2v_not_canRaise_D3 ?_
  rintro ⟨-, hz⟩
  exact absurd hz (by decide)

/-! ## §2. What shortest-ness really kills at the corridor -/

/-- **THE CORRIDOR'S TAIL NEVER BEGINS WITH `raise d`.**  A tail
`raise d :: s2` immediately after the corridor's own `pull d b` is an adjacent
same-card turn, deleted by `Bridge.adjacent_same_turn_shortens`; minimality is
contradicted.  Neither saturation hypothesis is used. -/
theorem corridor_tail_head_ne_raise
    {u v : State} {ρ pre γ tail : List Move} {c d : Card} {b : Base}
    (huwf : u.WF)
    (hplay : ShufflePlayW u ρ v)
    (hmin : ∀ ρ' : List Move, ShufflePlayW u ρ' v → ρ.length ≤ ρ'.length)
    (heq : ρ = (pre ++ Move.tabToFound c :: γ) ++ Move.foundToTab d b :: tail)
    (s2 : List Move) (htail : tail = Move.tabToFound d :: s2) : False := by
  have hρX : ρ = (pre ++ Move.tabToFound c :: γ) ++
      (Move.foundToTab d b :: Move.tabToFound d :: s2) := by
    rw [heq, htail]
  have hplay' : ShufflePlayW u
      ((pre ++ Move.tabToFound c :: γ) ++
        (Move.foundToTab d b :: Move.tabToFound d :: s2)) v := hρX ▸ hplay
  obtain ⟨F, hpre, hrest⟩ := ValleyElim.ShufflePlayW_split hplay'
    (pre ++ Move.tabToFound c :: γ)
    (Move.foundToTab d b :: Move.tabToFound d :: s2) rfl
  obtain ⟨ρ', hρ'play, hlen⟩ :=
    Bridge.adjacent_same_turn_shortens (u := u) (v := v) (F := F)
      (pre := pre ++ Move.tabToFound c :: γ) (post := s2)
      (c := d) (b := b) huwf hpre hplay'
  have hlenρ : ρ'.length < ρ.length := by rw [hρX]; exact hlen
  exact absurd (hmin ρ' hρ'play) (Nat.not_le.mpr hlenρ)

/-- **`Chain.chain_exists` AT A CORRIDOR.**  The chain exists, and its terminal
is not the adjacent `raise d` (that case is exactly `corridor_tail_head_ne_raise`).
Everything else is `Chain.chain_exists` verbatim. -/
theorem chain_exists_corridor
    {u v B : State} {ρ pre γ tail : List Move} {c d : Card} {b : Base}
    (huwf : u.WF) (hv : SSaturated v)
    (hplay : ShufflePlayW u ρ v)
    (hmin : ∀ ρ' : List Move, ShufflePlayW u ρ' v → ρ.length ≤ ρ'.length)
    (heq : ρ = (pre ++ Move.tabToFound c :: γ) ++ Move.foundToTab d b :: tail)
    (hB : B.WF) (hcan : CanRaise B d) (htail : ShufflePlayW B tail v) :
    ∃ (z' : Card) (s1 s2 : List Move) (A Z : State) (m : Move),
      z'.rank.toIdx ≤ d.rank.toIdx ∧ tail = s1 ++ m :: s2 ∧
      ShufflePlayW B s1 A ∧ CanRaise A z' ∧ State.step A m = some Z ∧
      ¬ CanRaise Z z' ∧
      (m = Move.tabToFound z' ∨
        ∃ x : Card, m = Move.tabToTab x (Sum.inr z') ∧ ¬ CanRaise Z x) ∧
      ¬ (s1 = [] ∧ m = Move.tabToFound d) := by
  obtain ⟨z', s1, s2, A, Z, m, hle, heqtail, hp1, hcanA, hstepA, hblk, hshape⟩ :=
    Chain.chain_exists hB hv hcan htail
  refine ⟨z', s1, s2, A, Z, m, hle, heqtail, hp1, hcanA, hstepA, hblk, hshape, ?_⟩
  rintro ⟨hs1, hm⟩
  have htail' : tail = Move.tabToFound d :: s2 := by
    rw [heqtail, hs1, hm]; rfl
  exact corridor_tail_head_ne_raise huwf hplay hmin heq s2 htail'

/-! ## §3. The twin branch with a pull-free tail: the tail MUST raise `d`

`Direct.canRaiseS_end_or_bad_raise` (`Orig2/ForkDirect.lean:301`) is the
pull-free kill dichotomy: a pull-free leg can destroy `e`'s S-licence only by
`raise e` or `raise e.twin`.  In the twin branch `d = c.twin`, so `d.twin = c` —
and `c` is the corridor's *raised* card, hence a foundation top for the entire
pull-free tail, hence never a pile top, hence never raised.  So the only
surviving kill is `raise d`. -/

/-- **THE TWIN / PULL-FREE TAIL RAISES `d`.** -/
theorem twin_tail_raises_d
    {u v : State} {ρ pre γ tail : List Move} {c d : Card} {b : Base}
    (huwf : u.WF) (hv : SSaturated v)
    (hplay : ShufflePlayW u ρ v)
    (heq : ρ = (pre ++ Move.tabToFound c :: γ) ++ Move.foundToTab d b :: tail)
    (hfree : CrossSuit.FreeOnly γ)
    (hd : d = c.twin)
    (hpf : ∀ m ∈ tail, ¬ Bubble.IsPull m) :
    ∃ s1 s2 : List Move, tail = s1 ++ Move.tabToFound d :: s2 := by
  have hplay' : ShufflePlayW u
      ((pre ++ Move.tabToFound c :: γ) ++ (Move.foundToTab d b :: tail)) v := heq ▸ hplay
  -- split off the raise
  have hsplitEq : (pre ++ Move.tabToFound c :: γ) ++ (Move.foundToTab d b :: tail)
      = pre ++ (Move.tabToFound c :: (γ ++ (Move.foundToTab d b :: tail))) := by
    simp only [List.append_assoc, List.cons_append]
  obtain ⟨A0, hpreR, hrestR⟩ := ValleyElim.ShufflePlayW_split hplay'
    pre (Move.tabToFound c :: (γ ++ (Move.foundToTab d b :: tail))) hsplitEq
  obtain ⟨B0, hrevR, hstepR, hrestγ⟩ := Bubble.walk_cons_inv hrestR
  have hA0wf : A0.WF := SatDifferCensus.ShufflePlayW.wf_end hpreR huwf
  have hB0wf : B0.WF := step_wf hA0wf hstepR
  obtain ⟨hnext0, a0, hca0, -⟩ := step_tabToFound_inv hstepR
  have hB0eq : B0 = raiseSt A0 c a0 := Blocks.eq_raiseSt_of_step hnext0 hca0 hstepR
  have hfoundB0 : B0.foundTop c.suit = some c := by
    rw [hB0eq]; exact BaseEn.foundTop_raiseSt_self A0 c a0
  have hmemB0 : c ∈ B0.found c.suit := lastOf_mem hfoundB0
  -- split off the free interior and the pull
  obtain ⟨P, hγ, hrestP⟩ :=
    ValleyElim.ShufflePlayW_split hrestγ γ (Move.foundToTab d b :: tail) rfl
  obtain ⟨B, hrevP, hstepP, htail⟩ := Bubble.walk_cons_inv hrestP
  have hPwf : P.WF := SatDifferCensus.ShufflePlayW.wf_end hγ hB0wf
  have hBwf : B.WF := step_wf hPwf hstepP
  have hcanS : CanRaiseS B d := CanRaiseS.now d (ValleyStep.pull_card_canRaise hPwf hstepP)
  have hblock : ¬ CanRaiseS v d := hv d
  -- the pull-free kill dichotomy
  rcases Direct.canRaiseS_end_or_bad_raise htail hBwf hpf hcanS with hsv | hocc | hocc
  · exact absurd hsv hblock
  · exact hocc
  · -- `raise c` cannot fire: `c` stays in a foundation row
    exfalso
    have hdt : d.twin = c := by rw [hd, card_twin_twin]
    rw [hdt] at hocc
    obtain ⟨s1, s2, hs1s2⟩ := hocc
    obtain ⟨As, hs1play, hrest3⟩ :=
      ValleyElim.ShufflePlayW_split htail s1 (Move.tabToFound c :: s2) hs1s2
    have hAswf : As.WF := SatDifferCensus.ShufflePlayW.wf_end hs1play hBwf
    have hseg : ShufflePlayW B0 (γ ++ (Move.foundToTab d b :: s1)) As :=
      ShufflePlayW_append hγ (Walk.cons hrevP hstepP hs1play)
    have hdc : d ≠ c := by
      intro h
      have h2 : c.suit.twin = c.suit := by
        have h3 : c.twin = c := by rw [← hd]; exact h
        exact congrArg Card.suit h3
      exact Suit.twin_ne c.suit h2
    have hno : ∀ k ∈ γ ++ (Move.foundToTab d b :: s1), ∀ b' : Base,
        k ≠ Move.foundToTab c b' := by
      intro k hk b' hkc
      rcases List.mem_append.mp hk with hk | hk
      · rcases hfree k hk with hd' | ⟨x, bb, hx⟩
        · rw [hkc] at hd'; cases hd'
        · rw [hkc] at hx; cases hx
      · rcases List.mem_cons.mp hk with hk | hk
        · subst hk
          injection hkc with hdc' _
          exact hdc hdc'
        · have hkt : k ∈ tail := by
            rw [hs1s2]; exact List.mem_append_left _ hk
          exact hpf k hkt ⟨c, b', hkc⟩
    have hmemAs : c ∈ As.found c.suit :=
      found_mem_play_of_not_pull hseg hmemB0 hno
    cases hrest3 with
    | cons hrev3 hstep3 hrest4 =>
        obtain ⟨-, a', hpo', -⟩ := step_tabToFound_inv hstep3
        exact CommuteStep.not_top_of_found hAswf hmemAs a'
          ((pileOfTop_eq_some_iff hAswf).mp hpo')

/-! ## §4. The exact residual of the twin / pull-free corner -/

/-- **`TwinRelocationResidual`** — THE EXACT RESIDUAL: in a shortest corridor
play with a saturated endpoint, in the twin branch, with a pull-free tail, the
tail is never a same-card relocation `(pull-free prefix) ; raise d` with a
nonempty prefix.  `twin_tail_raises_d` forces the shape and
`corridor_tail_head_ne_raise` forces the prefix nonempty, so this is exactly
what is left of the twin/pull-free corner. -/
def TwinRelocationResidual : Prop :=
  ∀ (u v : State) (ρ pre γ tail s1 s2 : List Move) (c d : Card) (b : Base),
    u.WF → SSaturated v → ShufflePlayW u ρ v →
    (∀ ρ' : List Move, ShufflePlayW u ρ' v → ρ.length ≤ ρ'.length) →
    ρ = (pre ++ Move.tabToFound c :: γ) ++ Move.foundToTab d b :: tail →
    CrossSuit.FreeOnly γ → c.suit ≠ d.suit →
    d = c.twin → (∀ m ∈ tail, ¬ Bubble.IsPull m) →
    tail = s1 ++ Move.tabToFound d :: s2 → s1 ≠ [] → False

/-- **THE TWIN / PULL-FREE CORRIDOR IS CLOSED MODULO RELOCATION.**  From the
residual: no shortest cross-suit corridor into a saturated endpoint, in the twin
branch, with a pull-free tail. -/
theorem twin_pullFree_no_corridor (hres : TwinRelocationResidual)
    {u v : State} {ρ pre γ tail : List Move} {c d : Card} {b : Base}
    (huwf : u.WF) (hv : SSaturated v)
    (hplay : ShufflePlayW u ρ v)
    (hmin : ∀ ρ' : List Move, ShufflePlayW u ρ' v → ρ.length ≤ ρ'.length)
    (heq : ρ = (pre ++ Move.tabToFound c :: γ) ++ Move.foundToTab d b :: tail)
    (hfree : CrossSuit.FreeOnly γ) (hsu : c.suit ≠ d.suit)
    (hd : d = c.twin) (hpf : ∀ m ∈ tail, ¬ Bubble.IsPull m) : False := by
  obtain ⟨s1, s2, hs1s2⟩ := twin_tail_raises_d huwf hv hplay heq hfree hd hpf
  have hs1ne : s1 ≠ [] := by
    intro hs1
    subst hs1
    exact corridor_tail_head_ne_raise huwf hplay hmin heq s2 (by simpa using hs1s2)
  exact hres u v ρ pre γ tail s1 s2 c d b huwf hv hplay hmin heq hfree hsu hd hpf hs1s2 hs1ne

/-- **THE TWIN SEAT-MATE CORRIDOR WITH A PULL-FREE TAIL IS CLOSED MODULO
RELOCATION.**  `SeatMate c d` with `c` not a king and `c.suit ≠ d.suit` forces
the twin branch `d = c.twin` (`Blocks`'s shape 3); `twin_pullFree_no_corridor`
then applies.  So on the twin branch, a pull-free tail leaves only
`TwinRelocationResidual`. -/
theorem noSeatMate_twin_pullFree (hres : TwinRelocationResidual)
    {u v : State} {ρ pre γ tail : List Move} {c d : Card} {b : Base}
    (huwf : u.WF) (hv : SSaturated v)
    (hplay : ShufflePlayW u ρ v)
    (hmin : ∀ ρ' : List Move, ShufflePlayW u ρ' v → ρ.length ≤ ρ'.length)
    (heq : ρ = (pre ++ Move.tabToFound c :: γ) ++ Move.foundToTab d b :: tail)
    (hfree : CrossSuit.FreeOnly γ) (hsu : c.suit ≠ d.suit)
    (hpf : ∀ m ∈ tail, ¬ Bubble.IsPull m)
    (hsm : SeatMate c d) (hk : c.rank ≠ Rank.king) : False := by
  rcases hsm with ⟨hck, -⟩ | ⟨-, hd | hd⟩
  · exact absurd hck hk
  · rw [hd] at hsu; exact hsu rfl
  · exact twin_pullFree_no_corridor hres huwf hv hplay hmin heq hfree hsu hd hpf

end Sat

/-! ## §5. Axiom battery

Expected: every row `[]`, `[propext]` or `[propext, Quot.sound]`. -/

#print axioms Sat.BT_liveB_false
#print axioms Sat.BT_sat
#print axioms Sat.not_canRaise_BT_S3
#print axioms Sat.playTail
#print axioms Sat.not_noChainRaise
#print axioms Sat.not_coverChainResidual
#print axioms Sat.coverChain_reduction_vacuous
#print axioms Sat.u2_wf
#print axioms Sat.u2v_wf
#print axioms Sat.u2v_sat
#print axioms Sat.not_noChainRaiseCorr
#print axioms Sat.corridor_tail_head_ne_raise
#print axioms Sat.chain_exists_corridor
#print axioms Sat.twin_tail_raises_d
#print axioms Sat.twin_pullFree_no_corridor
#print axioms Sat.noSeatMate_twin_pullFree

#check @Sat.not_noChainRaise
#check @Sat.not_coverChainResidual
#check @Sat.corridor_tail_head_ne_raise
#check @Sat.twin_tail_raises_d
#check @Sat.TwinRelocationResidual
