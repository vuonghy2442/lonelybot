import Orig2.Fork.Class.ForkPairRung
import Orig2.Fork.Class.ForkLivePair

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

/-!
# Orig2/ForkRungGePair — `SplitTwinRungGe` discharged by the live-pair residual

READ-ONLY scratch card.  No source file is modified; nothing committed.
Zero `sorry`, zero `Classical.choice`, zero `native_decide`; axiom battery at
the tail.

This card is the `PairRungKit`-spelled half of `Temp/RungGe_Core.lean` (the
three core lines are repeated here so the file stands alone, in the house
scratch style):

* `PairRungKit.SplitTwinRungGe` (`Orig2/Fork/Class/ForkPairRung.lean:168`) — and, indeed,
  the *full* pair-rung equality `TwinKit.SplitPairRungEq` — follows from
  `SplitKit.SplitLivePair` **alone**, with no `SplitBlock`, no
  `SplitContainment`, no siting and no cover datum
  (`splitTwinRungGe_of_splitLivePair`, `splitPrePullGe_of_splitLivePair`);
* hence from the repository's existing valley-elimination residual
  `ValleyElim.ValleyElimNonfork` (`splitTwinRungGe_of_valleyElim`);
* and the campaign chain runs on `SplitBlock + SplitContainment + SplitLivePair`
  (`satDifferForkWF_of_livePair_block_containment`,
  `satDifferForkWF_of_valleyElim_block_containment`).

The residual is therefore **not an independent obligation**: any proof of the
live-pair (fork) residual discharges it.  See `Temp/RungGe_Report.md`.
-/

namespace RungGePair

open TwinKit

/-! ## §1. The three core lines (repeated from `Temp/RungGe_Core.lean`) -/

/-- An S-live `c.twin` sits on its suit's frontier, which is `c`'s rank index. -/
theorem rungAt_twin_eq_of_live {F : State} {c : Card}
    (h : CanRaiseS F c.twin) : rungAt F c.twin.suit = c.rank.toIdx := by
  have hh := canRaiseS_rung (st := F) (c := c.twin) h
  rwa [show c.twin.rank = c.rank from rfl] at hh

/-- `CanRaiseS F c` + `TwinLivePair F d` force `c.twin` to be S-live. -/
theorem canRaiseS_twin_of_livePair {F : State} {c d : Card}
    (hS : CanRaiseS F c) (hl : TwinLivePair F d) :
    CanRaiseS F c.twin := by
  rcases (hl c).mp hS with h | h
  · rw [h]
    exact (hl d.twin).mpr (Or.inr rfl)
  · rw [h, card_twin_twin]
    exact (hl d).mpr (Or.inl rfl)

/-- **`SplitTwinRungGe` FROM THE LIVE PAIR** — the target, one-sided form. -/
theorem splitTwinRungGe_of_splitLivePair (hl : SplitKit.SplitLivePair) :
    PairRungKit.SplitTwinRungGe := by
  intro u v ρ F left right c d b pre post tail h
  obtain ⟨-, hSc, -, -⟩ := SplitKit.splitHyp_green h
  have htwin : CanRaiseS F c.twin :=
    canRaiseS_twin_of_livePair hSc
      (hl u v ρ F left right c d b pre post tail h)
  rw [rungAt_twin_eq_of_live htwin, canRaiseS_rung hSc]
  exact Nat.le_refl _

/-- **THE FULL PAIR-RUNG EQUALITY FROM THE LIVE PAIR** — both halves. -/
theorem splitPairRungEq_of_splitLivePair (hl : SplitKit.SplitLivePair) :
    SplitPairRungEq := by
  intro u v ρ F left right c d b pre post tail h
  obtain ⟨-, hSc, -, -⟩ := SplitKit.splitHyp_green h
  have htwin : CanRaiseS F c.twin :=
    canRaiseS_twin_of_livePair hSc
      (hl u v ρ F left right c d b pre post tail h)
  rw [rungAt_twin_eq_of_live htwin, canRaiseS_rung hSc]

/-! ## §2. The sharpest (pre-pull) form -/

/-- **`SplitPrePullGe` FROM THE LIVE PAIR** — before the pull, the twin suit
already carries `c`'s rank index (`c.rank.toIdx ≤ rungAt A' c.twin.suit`), via
`PairRungKit.splitTwinRungGe_iff_prePullGe`. -/
theorem splitPrePullGe_of_splitLivePair (hl : SplitKit.SplitLivePair) :
    PairRungKit.SplitPrePullGe :=
  PairRungKit.splitTwinRungGe_iff_prePullGe.mp
    (splitTwinRungGe_of_splitLivePair hl)

/-- The same from the valley-elimination residual. -/
theorem splitPrePullGe_of_valleyElim (h : ValleyElim.ValleyElimNonfork) :
    PairRungKit.SplitPrePullGe :=
  splitPrePullGe_of_splitLivePair (LiveKit.splitLivePair_of_valleyElim h)

/-! ## §3. `ValleyElimNonfork` discharges the target -/

/-- **THE TARGET FROM THE REPOSITORY'S VALLEY-ELIMINATION RESIDUAL.** -/
theorem splitTwinRungGe_of_valleyElim (h : ValleyElim.ValleyElimNonfork) :
    PairRungKit.SplitTwinRungGe :=
  splitTwinRungGe_of_splitLivePair (LiveKit.splitLivePair_of_valleyElim h)

/-- The pair-rung equality from the same residual. -/
theorem splitPairRungEq_of_valleyElim (h : ValleyElim.ValleyElimNonfork) :
    SplitPairRungEq :=
  splitPairRungEq_of_splitLivePair (LiveKit.splitLivePair_of_valleyElim h)

/-! ## §4. The campaign in `PairRungKit` form -/

/-- **THE CAMPAIGN FROM THE ONE-SIDED TARGET** (`SplitBlock` +
`SplitContainment` + `SplitTwinRungGe`), with the pin *derived* from the live
pair. -/
theorem satDifferForkWF_of_livePair_block_containment
    (hl : SplitKit.SplitLivePair) (hb : SplitKit.SplitBlock)
    (hc : TwinKit.SplitContainment)
    (hmin : ValleyElim.ShortestPlayExists) : SatDifferForkWF :=
  PairRungKit.satDifferForkWF_of_block_containment_of_ge hb hc
    (splitTwinRungGe_of_splitLivePair hl) hmin

/-- The same from `ValleyElimNonfork`. -/
theorem satDifferForkWF_of_valleyElim_block_containment
    (helim : ValleyElim.ValleyElimNonfork) (hb : SplitKit.SplitBlock)
    (hc : TwinKit.SplitContainment)
    (hmin : ValleyElim.ShortestPlayExists) : SatDifferForkWF :=
  satDifferForkWF_of_livePair_block_containment
    (LiveKit.splitLivePair_of_valleyElim helim) hb hc hmin

/-- The mechanism residual from the same three clauses. -/
theorem mechanismResidual_of_livePair_block_containment
    (hl : SplitKit.SplitLivePair) (hb : SplitKit.SplitBlock)
    (hc : TwinKit.SplitContainment) : Mech.MechanismResidual :=
  PairRungKit.mechanismResidual_of_block_containment_of_ge hb hc
    (splitTwinRungGe_of_splitLivePair hl)

/-! ## §5. Battery -/

#print axioms RungGePair.rungAt_twin_eq_of_live
#print axioms RungGePair.canRaiseS_twin_of_livePair
#print axioms RungGePair.splitTwinRungGe_of_splitLivePair
#print axioms RungGePair.splitPairRungEq_of_splitLivePair
#print axioms RungGePair.splitPrePullGe_of_splitLivePair
#print axioms RungGePair.splitPrePullGe_of_valleyElim
#print axioms RungGePair.splitTwinRungGe_of_valleyElim
#print axioms RungGePair.splitPairRungEq_of_valleyElim
#print axioms RungGePair.satDifferForkWF_of_livePair_block_containment
#print axioms RungGePair.satDifferForkWF_of_valleyElim_block_containment
#print axioms RungGePair.mechanismResidual_of_livePair_block_containment

end RungGePair

