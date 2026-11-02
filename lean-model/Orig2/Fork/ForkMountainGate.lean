import Orig2.Fork.ForkDirect
import Orig2.Fork.ForkFrontier

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

/-!
# ForkMountainGate — the mountain hypothesis, RE-GATED

`Direct.MountainAtSplits` and `Frontier.MountainSplitHyp` are the same statement:

```text
∀ (split data), SplitHyp … → MountainSplit left right
```

`SplitKit.SplitHyp` carries `u.WF`, `SSaturated u`, `SSaturated v`, the play,
the valley split and the SHORTEST-PLAY conjunct — but **no rung hypothesis**.  So
both defs also quantify over the **equal-rung** stratum, and that stratum is
exactly where the mountain has no reason to hold:

* the mountain's force is the accounting identity
  `length = Σσ(h_u + h_v − 2m_σ) + #free`, whose "budget" is the L1 rung gap —
  which is **zero** when the endpoints agree;
* every census (`51 116 + 9 966` minimal plays) enumerated only **differing-rung**
  pairs, so the equal-rung stratum was never probed;
* the one equal-rung datum we have is a **candidate relocation** (13 moves,
  unit-shortest, saturated endpoints at equal rungs `(4,0,3,2)`, containing
  `raise 5C … pull 5C → 6D`; probe only, see `Temp/Crack_Report.md` regime R4,
  being kernel-certified in `Temp/EqualRung_*`).

So the un-gated forms are **FALSE** (`EqualRung.mountainAtSplits_false`,
`Orig2/ForkEqualRungMain.lean`): the equal-rung stratum is now probed and
refuted, and their consumers must not be cited as conditional on a hypothesis
the campaign can discharge.  The campaign's own endpoint hypothesis already
supplies the missing gate — `SatDifferForkWF` literally carries
`∃ σ, rungAt u σ ≠ rungAt v σ` — so the corrected forms below are the ones to
use.

The two un-gated definitions are kept (marked FALSE in their docstrings) only so
the refutation and the historical consumers can name them; every theorem that
assumes one is vacuous.
-/

namespace MountainGate

open ValleyElim

/-- **The gate.** The campaign's own endpoint hypothesis, as its own name. -/
def RungDiffers (u v : State) : Prop := ∃ σ : Suit, rungAt u σ ≠ rungAt v σ

/-- **`MountainAtSplitsDiffering` — THE GATED MOUNTAIN.**  The down-then-up shape,
asked only where the campaign actually uses it: at a minimal play between
saturated endpoints whose rung vectors DIFFER.  This is the form that has
census support (`M1` 100 % on both cost models) and the only form whose "budget"
is non-zero. -/
def MountainAtSplitsDiffering : Prop :=
  ∀ (u v : State) (ρ : List Move) (F : State)
    (left right : List Move) (c d : Card) (b : Base)
    (pre post tail : List Move),
    RungDiffers u v →
    SplitKit.SplitHyp u v ρ F left right c d b pre post tail →
    MountainKit.MountainSplit left right

/-- The frontier spelling of the same gated statement. -/
def MountainSplitHypDiffering : Prop :=
  MountainAtSplitsDiffering

/-- The two spellings agree. -/
theorem mountainSplitHypDiffering_eq : MountainSplitHypDiffering = MountainAtSplitsDiffering :=
  rfl

/-- **VACUOUS: the un-gated hypothesis is FALSE.**  This implication is
vacuously true (`EqualRung.mountainAtSplits_false`), so it is NOT a way to
obtain the gate and it does NOT show "gating loses nothing".  The gate is
load-bearing: the equal-rung 13-move relocation refutes the un-gated form while
`EqualRung.not_rungDiffers` keeps it outside the gated form.  Kept only for
interface archaeology; do not cite. -/
theorem mountainAtSplitsDiffering_of_ungated
    (h : Direct.MountainAtSplits) : MountainAtSplitsDiffering :=
  fun u v ρ F left right c d b pre post tail _ hs =>
    h u v ρ F left right c d b pre post tail hs

/-- **VACUOUS**: same statement for the frontier spelling
(`Direct.MountainAtSplits = Frontier.MountainSplitHyp`, which is FALSE). -/
theorem mountainSplitHypDiffering_of_ungated
    (h : Frontier.MountainSplitHyp) : MountainSplitHypDiffering :=
  fun u v ρ F left right c d b pre post tail _ hs =>
    h u v ρ F left right c d b pre post tail hs

/-- **Sanity: the gate is exactly the campaign's endpoint hypothesis.**  This is the
witness `SatDifferForkWF` already carries, so the gated mountain is instantiable
wherever the campaign applies it. -/
theorem rungDiffers_of_satDiffer
    {u v : State} (h : ∃ σ : Suit, rungAt u σ ≠ rungAt v σ) : RungDiffers u v :=
  h

#print axioms MountainGate.mountainAtSplitsDiffering_of_ungated
#print axioms MountainGate.mountainSplitHypDiffering_of_ungated

end MountainGate
