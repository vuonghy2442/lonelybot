import Orig2.Fork.ForkMinCross

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

/-!
# ForkMountain — the mountain shape and what it forces at the bottom

`Temp/Mountain_probe.py` (13 boards, **51 116 minimal plays**, both the
unit-cost and the bracket-cost model) measured:

```
M1  mountain order      no raise occurs before a pull          51 116/51 116
M2  per-suit unimodal   each suit's height has no up-then-down  51 116/51 116
M3  free tail           a free letter sits between the last
                        pull and the first raise                51 116/51 116
INT dip vector          every minimal play of a given ordered pair
                        has the SAME componentwise minimum m(u,v)
INT turn rung           … and the same rung vector just before
                        the last pull
```

This card proves what the shape *forces*, unconditionally (no minimality
needed): if the valley's left leg has no raise and its right leg has no pull,
then the bottom's rung vector is **componentwise below both endpoints** — the
bottom is the dip.  Given the probe's INT rows (the dip and the turn are
functions of the endpoint pair alone), the whole campaign question then lives
at ONE fibre: the dip fibre.

The two play-level monotonicity rows are the reusable content:
`rungAt_le_of_no_raise` and `rungAt_le_of_no_pull`.
-/

namespace MountainKit

open ValleyElim
open Bubble

/-- **The mountain legs.**  The left leg contains no raise, the right leg no
pull — i.e. the play descends, turns, then ascends.  (`M1` measured.) -/
def MountainSplit (α β : List Move) : Prop :=
  (∀ m ∈ α, ¬ IsRaise m) ∧ (∀ m ∈ β, ¬ IsPull m)

/-! ## §1. Rung monotonicity of the legs -/

/-- **A raise-free witness play cannot lift a rung.** -/
theorem rungAt_le_of_no_raise {u v : State} {ρ : List Move} {σ : Suit}
    (hplay : ShufflePlayW u ρ v) (hno : ∀ m ∈ ρ, ¬ IsRaise m) :
    rungAt v σ ≤ rungAt u σ := by
  induction hplay with
  | nil => exact Nat.le_refl _
  | @cons st s₁ W m ρ' _hrev hstep _hrest ih =>
      have hm : ¬ IsRaise m := hno m List.mem_cons_self
      have htail : ∀ m' ∈ ρ', ¬ IsRaise m' :=
        fun m' hm' => hno m' (List.mem_cons_of_mem m hm')
      have hIH := ih htail
      cases m with
      | draw =>
          have h := rungAt_draw hstep σ
          omega
      | tabToFound c => exact absurd ⟨c, rfl⟩ hm
      | tabToTab c b =>
          have h := rungAt_tabToTab hstep σ
          omega
      | foundToTab c b =>
          have h := rungAt_foundToTab hstep σ
          split at h <;> omega
      | wasteToFound c => exact absurd _hrev (wasteToFound_not_reversibleAtW st c)
      | wasteToTab c b => exact absurd _hrev (wasteToTab_not_reversibleAtW st c b)

/-- **A pull-free witness play cannot lower a rung.** -/
theorem rungAt_le_of_no_pull {u v : State} {ρ : List Move} {σ : Suit}
    (hplay : ShufflePlayW u ρ v) (hno : ∀ m ∈ ρ, ¬ IsPull m) :
    rungAt u σ ≤ rungAt v σ := by
  induction hplay with
  | nil => exact Nat.le_refl _
  | @cons st s₁ W m ρ' _hrev hstep _hrest ih =>
      have hm : ¬ IsPull m := hno m List.mem_cons_self
      have htail : ∀ m' ∈ ρ', ¬ IsPull m' :=
        fun m' hm' => hno m' (List.mem_cons_of_mem m hm')
      have hIH := ih htail
      cases m with
      | draw =>
          have h := rungAt_draw hstep σ
          omega
      | tabToFound c =>
          have h := rungAt_tabToFound hstep σ
          split at h <;> omega
      | tabToTab c b =>
          have h := rungAt_tabToTab hstep σ
          omega
      | foundToTab c b => exact absurd ⟨c, b, rfl⟩ hm
      | wasteToFound c => exact absurd _hrev (wasteToFound_not_reversibleAtW st c)
      | wasteToTab c b => exact absurd _hrev (wasteToTab_not_reversibleAtW st c b)

/-! ## §2. The bottom is the dip -/

/-- **THE MOUNTAIN BOTTOM IS A DIP.**  Left leg raise-free, right leg
pull-free: the valley bottom's rung is componentwise below both endpoints.
This is the formal content of the probe's `M1` + its turn rows. -/
theorem mountain_bottom_le {u v F : State} {left right : List Move} {σ : Suit}
    (hleft : ShufflePlayW u left F) (hright : ShufflePlayW F right v)
    (hnoRaise : ∀ m ∈ left, ¬ IsRaise m) (hnoPull : ∀ m ∈ right, ¬ IsPull m) :
    rungAt F σ ≤ rungAt u σ ∧ rungAt F σ ≤ rungAt v σ :=
  ⟨rungAt_le_of_no_raise hleft hnoRaise,
    rungAt_le_of_no_pull hright hnoPull⟩

/-- The same, for the whole rung vector, from a `MountainSplit` of the play. -/
theorem mountain_bottom_le_vec {u v F : State} {left right : List Move}
    (hleft : ShufflePlayW u left F) (hright : ShufflePlayW F right v)
    (hms : MountainSplit left right) :
    ∀ σ : Suit, rungAt F σ ≤ rungAt u σ ∧ rungAt F σ ≤ rungAt v σ :=
  fun σ => mountain_bottom_le hleft hright hms.1 hms.2

#print axioms MountainKit.rungAt_le_of_no_raise
#print axioms MountainKit.rungAt_le_of_no_pull
#print axioms MountainKit.mountain_bottom_le
#print axioms MountainKit.mountain_bottom_le_vec

end MountainKit
