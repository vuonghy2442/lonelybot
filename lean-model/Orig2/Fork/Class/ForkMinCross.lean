import Orig2.Fork.Class.ForkExist

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

/-!
# ForkMinCross — the fork may occur ANYWHERE on the minimal play

`ExistKit.ValleyForkAtMin` pins the fork to the valley bottom `F`.  That is
strictly stronger than the campaign needs: `SatDifferForkWF` asks only for a
fork state in `u`'s orbit, and EVERY state on a witness play from `u` is in
that orbit (`ShufflePlayW u α F → RevEqW u F`).

So the honest residual is the weaker

  `MinCrossesFork`: every minimal witness play between differing-rung
  saturated class-mates visits a fork somewhere.

Its contrapositive is the statement the fork-free-path probes actually
compute: *a fork-free witness play is not minimal* (the kernel's own
`Orig2/Boundary/BoundaryForkFree.lean` play is the canonical test object: 14 moves,
fork-free, while the fork-crossing play has 12).

Two facts here:

1. `ValleyForkAtMin → MinCrossesFork` (the split's left leg is the prefix);
2. `MinCrossesFork → ShortestPlayExists → SatDifferForkWF`.

This card changes no existing statement; it only records that the pinned
bottom is not needed.
-/

namespace MinKit

open ValleyElim

/-- **A fork occurs at a state on the play**: `α` is a prefix landing at `F`. -/
def ForkOnPrefix (u : State) (ρ : List Move) : Prop :=
  ∃ (F : State) (x : Card) (α β : List Move),
    ρ = α ++ β ∧ ShufflePlayW u α F ∧ ForkWitness F x

/-- **`MinCrossesFork`** — every minimal witness play between differing-rung
saturated states visits a fork.  Weaker than `ExistKit.ValleyForkAtMin`, which
demands the fork at the valley bottom. -/
def MinCrossesFork : Prop :=
  ∀ (u v : State) (ρ : List Move),
    u.WF → SSaturated u → SSaturated v →
    ShufflePlayW u ρ v →
    (∃ σ : Suit, rungAt u σ ≠ rungAt v σ) →
    (∀ ρ' : List Move, ShufflePlayW u ρ' v → ρ.length ≤ ρ'.length) →
    ForkOnPrefix u ρ

/-- **`ValleyForkAtMin` IMPLIES `MinCrossesFork`.**  `valley_exists` supplies
the split; its left leg is the prefix, and `ValleyForkAtMin` puts the fork at
the bottom `F`. -/
theorem minCrossesFork_of_valleyForkAtMin (h : ExistKit.ValleyForkAtMin) :
    MinCrossesFork := by
  intro u v ρ huwf hsu hsv hplay hdiff hmin
  obtain ⟨F, hF⟩ := valley_exists huwf hsu hsv hdiff hplay
  obtain ⟨left, right, c, d, b, pre, post, tail,
    hsplitEq, hleft, hright, hshape, hfree, hrightShape⟩ := hF
  obtain ⟨x, hx⟩ :=
    h u v ρ F huwf hsu hsv hplay hmin
      ⟨left, right, c, d, b, pre, post, tail,
        hsplitEq, hleft, hright, hshape, hfree, hrightShape⟩
  exact ⟨F, x, left, right, hsplitEq, hleft, hx⟩

/-- **THE CAMPAIGN REDUCTION FROM THE WEAKER RESIDUAL.**  Any state on a
witness play from `u` is in `u`'s orbit, so a fork anywhere on the minimal
play discharges `SatDifferForkWF`. -/
theorem satDifferForkWF_of_minCrossesFork
    (h : MinCrossesFork) (hmin : ShortestPlayExists) : SatDifferForkWF := by
  intro u v huwf hsu hsv hcls hdiff
  obtain ⟨ρ, hρ, hminlen⟩ := hmin u v huwf hsu hsv hcls hdiff
  obtain ⟨F, x, α, β, _heq, hα, hx⟩ :=
    h u v ρ huwf hsu hsv hρ hdiff hminlen
  exact ⟨F, x, RevEqW_symm (shufflePlayW_revEqW hα), hx⟩

#print axioms MinKit.minCrossesFork_of_valleyForkAtMin
#print axioms MinKit.satDifferForkWF_of_minCrossesFork

end MinKit
