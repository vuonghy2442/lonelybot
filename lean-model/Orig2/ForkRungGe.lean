import Orig2.ForkTwinLive
import Orig2.ForkLivePair

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

/-!
# Orig2/ForkRungGe — the twin-suit rung is not an independent residual

READ-ONLY scratch card.  No source file is modified; nothing committed.
Zero `sorry`, zero `Classical.choice`, zero `native_decide`; axiom battery at
the tail.

## What this card proves

`TwinKit.SplitPairRungEq` (`Orig2/ForkTwinLive.lean:411`), equivalently the
one-sided `PairRungKit.SplitTwinRungGe` (`Orig2/ForkPairRung.lean:176`), is the
campaign's last purely arithmetic clause:

    at every split:  rungAt F c.twin.suit = rungAt F c.suit.

**The main theorem of this card: the residual is not an independent
obligation.**  The *S-liveness of the twin at the bottom* pins it outright
(`canRaiseS_rung`), and that liveness is already the content of the campaign's
own live-pair residual:

    `SplitKit.SplitLivePair → TwinKit.SplitPairRungEq`
      (`splitPairRungEq_of_splitLivePair`),

i.e. the pair-rung equality — both halves, not merely the one-sided target —
follows from `SplitKit.SplitLivePair` *alone*: **no `SplitBlock`, no
`SplitContainment`, no siting, no cover datum.**  In particular it follows from
the repository's existing valley-elimination residual
`ValleyElim.ValleyElimNonfork` (`LiveKit.splitLivePair_of_valleyElim`):

    `splitPairRungEq_of_valleyElim`.

## The mechanism

Three lines:

* `CanRaiseS F c` is green at every split (`SplitKit.splitHyp_green`);
* `TwinLivePair F d` says the live set is exactly `{d, d.twin}`, so
  `c ∈ {d, d.twin}`;
* in *either* arm `c.twin` is one of the two live cards
  (`canRaiseS_twin_of_livePair` — the arm `c = d` reads the twin `d.twin`).

Two `canRaiseS_rung` instances then give
`rungAt F c.twin.suit = c.rank.toIdx = rungAt F c.suit`.

This is *sharper* than the repository's `TwinKit.rungAt_twin_of_landingLivePair`
(`Orig2/ForkTwinLive.lean:308`), which needs the whole `LandingLivePair`
(twin liveness **plus** the third-suit containment) as input: here the single
`TwinLivePair` conjunct suffices, and the containment clause is not consulted.

Provenance: the repository already carried every ingredient
(`Landing.twinLivePair_at_F_of_splitLivePair`, `Orig2/ForkLanding.lean:295`,
re-pivots the live pair to `c`; `canRaiseS_rung` then pins the rung) but never
the implication.  What is new here is the statement itself, the pivot-free
proof (`canRaiseS_twin_of_livePair` handles both arms), the exact `↔` with the
pin under `SplitBlock + SplitContainment`, and the negative result
(`Temp/RungGe_Gadget.lean`) showing the cover-source datum cannot supply it.

## Exactness

With `SplitBlock` + `SplitContainment` the converse is the repository's
`TwinKit.splitLivePair_of_block_containment_of_pin`
(`Orig2/ForkTwinLive.lean:602`), so the pair-rung residual *is* the live-pair
residual in the presence of the other two clauses:

    `splitLivePair_iff_pairRungEq_of_block_containment`.
-/

namespace RungGe

open TwinKit

/-! ## §1. Twin liveness pins the twin-suit rung -/

/-- **TWIN LIVENESS PINS THE TWIN RUNG.**  An S-live `c.twin` sits on the
frontier of its own suit (`canRaiseS_rung`), and the twin keeps `c`'s rank. -/
theorem rungAt_twin_eq_of_live {F : State} {c : Card}
    (h : CanRaiseS F c.twin) : rungAt F c.twin.suit = c.rank.toIdx := by
  have hh := canRaiseS_rung (st := F) (c := c.twin) h
  rwa [show c.twin.rank = c.rank from rfl] at hh

/-- The same read as `nextUp`, i.e. the `TwinKit.SplitTwinRungPin` clause. -/
theorem nextUp_twin_of_live {F : State} {c : Card}
    (h : CanRaiseS F c.twin) : F.nextUp c.twin = true :=
  TwinKit.nextUp_true_iff.mpr (rungAt_twin_eq_of_live h)

/-! ## §2. The live-pair residual supplies the twin's liveness -/

/-- **THE CASE ANALYSIS.**  `CanRaiseS F c` puts the pull card in the live pair
`{d, d.twin}`; in both arms the twin `c.twin` is one of the two live cards, so
it is S-live.  Nothing is assumed about `c` and `d` beyond `TwinLivePair`. -/
theorem canRaiseS_twin_of_livePair {F : State} {c d : Card}
    (hS : CanRaiseS F c) (hl : TwinLivePair F d) :
    CanRaiseS F c.twin := by
  rcases (hl c).mp hS with h | h
  · -- `c = d`: the twin is the *other* card of the pair
    rw [h]
    exact (hl d.twin).mpr (Or.inr rfl)
  · -- `c = d.twin`: the twin is the raise card itself
    rw [h, card_twin_twin]
    exact (hl d).mpr (Or.inl rfl)

/-- **`SplitPairRungEq` FROM THE LIVE PAIR** — both halves at once, since both
rungs are pinned to `c.rank.toIdx`.  No `SplitBlock`, no `SplitContainment`. -/
theorem splitPairRungEq_of_splitLivePair (hl : SplitKit.SplitLivePair) :
    SplitPairRungEq := by
  intro u v ρ F left right c d b pre post tail h
  obtain ⟨-, hSc, -, -⟩ := SplitKit.splitHyp_green h
  have htwin : CanRaiseS F c.twin :=
    canRaiseS_twin_of_livePair hSc
      (hl u v ρ F left right c d b pre post tail h)
  rw [rungAt_twin_eq_of_live htwin, canRaiseS_rung hSc]

/-- The `nextUp`-form of the same statement (`TwinKit.SplitTwinRungPin`). -/
theorem splitTwinRungPin_of_splitLivePair (hl : SplitKit.SplitLivePair) :
    TwinKit.SplitTwinRungPin := by
  intro u v ρ F left right c d b pre post tail h
  obtain ⟨-, hSc, -, -⟩ := SplitKit.splitHyp_green h
  exact nextUp_twin_of_live (canRaiseS_twin_of_livePair hSc
    (hl u v ρ F left right c d b pre post tail h))

/-- The twin's S-liveness at every split's bottom — the *single* missing
datum, named (it is the first conjunct of `Mech.LandingLivePair`). -/
def SplitTwinLiveAtBottom : Prop :=
  ∀ (u v : State) (ρ : List Move) (F : State)
    (left right : List Move) (c d : Card) (b : Base)
    (pre post tail : List Move),
    SplitKit.SplitHyp u v ρ F left right c d b pre post tail →
    CanRaiseS F c.twin

/-- **THE PIN FROM THE TWIN'S LIVENESS.**  The one datum `SplitTwinLiveAtBottom`
gives the pair-rung equality outright. -/
theorem splitPairRungEq_of_twinLiveAtBottom (hl : SplitTwinLiveAtBottom) :
    SplitPairRungEq := by
  intro u v ρ F left right c d b pre post tail h
  obtain ⟨-, hSc, -, -⟩ := SplitKit.splitHyp_green h
  rw [rungAt_twin_eq_of_live (hl u v ρ F left right c d b pre post tail h),
    canRaiseS_rung hSc]

/-- `SplitLivePair` gives the bottom's twin liveness (the §2 case analysis,
read as a residual-level implication). -/
theorem twinLiveAtBottom_of_splitLivePair (hl : SplitKit.SplitLivePair) :
    SplitTwinLiveAtBottom :=
  fun u v ρ F left right c d b pre post tail h =>
    canRaiseS_twin_of_livePair (SplitKit.splitHyp_green h).2.1
      (hl u v ρ F left right c d b pre post tail h)

/-! ## §3. The existing valley-elimination residual discharges it -/

/-- **THE PIN FROM `ValleyElimNonfork`.**  The repository's valley-elimination
residual already yields `SplitLivePair` (`LiveKit.splitLivePair_of_valleyElim`),
so it yields the pair-rung equality too. -/
theorem splitPairRungEq_of_valleyElim (h : ValleyElim.ValleyElimNonfork) :
    SplitPairRungEq :=
  splitPairRungEq_of_splitLivePair (LiveKit.splitLivePair_of_valleyElim h)

/-! ## §4. Exactness: with the other two clauses the pin *is* the live pair -/

/-- **THE EXACT EQUIVALENCE.**  Given `SplitBlock` and `SplitContainment`, the
pair-rung residual and the live-pair residual are the same statement.  The
forward direction is this card's §2 (no hypotheses); the backward one is
`TwinKit.splitLivePair_of_block_containment_of_pin`. -/
theorem splitLivePair_iff_pairRungEq_of_block_containment
    (hb : SplitKit.SplitBlock) (hc : TwinKit.SplitContainment) :
    SplitKit.SplitLivePair ↔ SplitPairRungEq :=
  ⟨splitPairRungEq_of_splitLivePair,
    fun hr => TwinKit.splitLivePair_of_block_containment_of_pin hb hc
      (TwinKit.splitPairRungEq_iff_splitTwinRungPin.mp hr)⟩

/-! ## §5. The campaign consumes it -/

/-- **THE CAMPAIGN WITHOUT THE PAIR-RUNG CLAUSE.**  `SplitBlock` +
`SplitContainment` + the live-pair residual + the choice-free shortest-play
interface give `SatDifferForkWF`.  (The pin is *derived*, not assumed.) -/
theorem satDifferForkWF_of_livePair_block_containment
    (hl : SplitKit.SplitLivePair) (hb : SplitKit.SplitBlock)
    (hc : TwinKit.SplitContainment)
    (hmin : ValleyElim.ShortestPlayExists) : SatDifferForkWF :=
  TwinKit.satDifferForkWF_of_block_containment_of_pairRungEq hb hc
    (splitPairRungEq_of_splitLivePair hl) hmin

/-- The same from the repository's valley-elimination residual. -/
theorem satDifferForkWF_of_valleyElim_block_containment
    (helim : ValleyElim.ValleyElimNonfork) (hb : SplitKit.SplitBlock)
    (hc : TwinKit.SplitContainment)
    (hmin : ValleyElim.ShortestPlayExists) : SatDifferForkWF :=
  satDifferForkWF_of_livePair_block_containment
    (LiveKit.splitLivePair_of_valleyElim helim) hb hc hmin

/-! ## §6. Battery -/

#print axioms RungGe.rungAt_twin_eq_of_live
#print axioms RungGe.nextUp_twin_of_live
#print axioms RungGe.canRaiseS_twin_of_livePair
#print axioms RungGe.splitPairRungEq_of_splitLivePair
#print axioms RungGe.splitTwinRungPin_of_splitLivePair
#print axioms RungGe.splitPairRungEq_of_twinLiveAtBottom
#print axioms RungGe.twinLiveAtBottom_of_splitLivePair
#print axioms RungGe.splitPairRungEq_of_valleyElim
#print axioms RungGe.splitLivePair_iff_pairRungEq_of_block_containment
#print axioms RungGe.satDifferForkWF_of_livePair_block_containment
#print axioms RungGe.satDifferForkWF_of_valleyElim_block_containment

end RungGe
