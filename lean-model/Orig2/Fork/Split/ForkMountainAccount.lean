import Orig2.Fork.Split.ForkMountain
import Orig2.Fork.Split.ForkLedger
import Orig2.Fork.Split.ForkSplit

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-!
# Mountain2_Account — the accounting identity of a mountain play

READ-ONLY scratch card (`Temp/`).  No source file is modified; nothing is
committed.  `sorry`-free, `Classical.choice`-free, `native_decide`-free.

`Temp/Mountain_Report.md` measured, over 51 116 minimal plays, that under the
mountain shape the per-suit height walk `h_σ(t) = rungAt (state t) σ` is
unimodal, so the total variation of each walk is

```
#pulls_σ + #raises_σ  =  (h_σ(u) − m_σ) + (h_σ(v) − m_σ)
```

with `m_σ` the minimum of the walk (the dip).  This card proves exactly that,
with `MountainSplit α β` (`Orig2/Fork/Split/ForkMountain.lean:42`) supplying the split,
and it proves that the split's state `F` realises the *componentwise minimum*
of the walk (`RungMinAlong`).  Nothing here consumes minimality.

## Naming

* `pullsOf` / `raisesOf` / `pullTotal` / `raiseTotal` are `Orig2/Substrate/Vocab.lean:65-89`;
* `rungAt_ledger` is `Orig2/Fork/Split/ForkLedger.lean:133`;
* the per-letter rung transport rows are `Orig2/Substrate/Position.lean:166-221`.
-/

namespace MountainKit

open ValleyElim
open Bubble

/-! ## §0. Two prefixes of one list are comparable -/

/-- If `a` and `α` are both prefixes of the same list `α ++ β = a ++ b`, then
one is a prefix of the other.  (The alignment lemma the whole card runs on.) -/
theorem append_prefix_cases :
    ∀ (α a : List Move) (β b : List Move), α ++ β = a ++ b →
      (∃ δ : List Move, α = a ++ δ) ∨ (∃ δ : List Move, a = α ++ δ)
  | [], a, β, b, h => by
      exact Or.inr ⟨a, rfl⟩
  | x :: xs, [], β, b, h => by
      exact Or.inl ⟨x :: xs, rfl⟩
  | x :: xs, y :: ys, β, b, h => by
      simp only [List.cons_append] at h
      obtain ⟨hxy, htail⟩ := List.cons.inj h
      subst hxy
      rcases append_prefix_cases xs ys β b htail with ⟨δ, hδ⟩ | ⟨δ, hδ⟩
      · exact Or.inl ⟨δ, by rw [hδ, List.cons_append]⟩
      · exact Or.inr ⟨δ, by rw [hδ, List.cons_append]⟩

/-! ## §1. The play-taxonomy counters split over concatenation -/

theorem pullsOf_append (a b : List Move) (σ : Suit) :
    pullsOf (a ++ b) σ = pullsOf a σ + pullsOf b σ := by
  induction a with
  | nil => simp [pullsOf]
  | cons m t ih =>
      cases m with
      | draw => simpa [pullsOf] using ih
      | wasteToFound c => simpa [pullsOf] using ih
      | wasteToTab c b' => simpa [pullsOf] using ih
      | tabToFound c => simpa [pullsOf] using ih
      | tabToTab c b' => simpa [pullsOf] using ih
      | foundToTab c b' =>
          simp only [List.cons_append, pullsOf, ih]
          omega

theorem raisesOf_append (a b : List Move) (σ : Suit) :
    raisesOf (a ++ b) σ = raisesOf a σ + raisesOf b σ := by
  induction a with
  | nil => simp [raisesOf]
  | cons m t ih =>
      cases m with
      | draw => simpa [raisesOf] using ih
      | wasteToFound c => simpa [raisesOf] using ih
      | wasteToTab c b' => simpa [raisesOf] using ih
      | tabToFound c =>
          simp only [List.cons_append, raisesOf, ih]
          omega
      | tabToTab c b' => simpa [raisesOf] using ih
      | foundToTab c b' => simpa [raisesOf] using ih

theorem pullTotal_append (a b : List Move) :
    pullTotal (a ++ b) = pullTotal a + pullTotal b := by
  induction a with
  | nil => simp [pullTotal]
  | cons m t ih =>
      cases m with
      | draw => simpa [pullTotal] using ih
      | wasteToFound c => simpa [pullTotal] using ih
      | wasteToTab c b' => simpa [pullTotal] using ih
      | tabToFound c => simpa [pullTotal] using ih
      | tabToTab c b' => simpa [pullTotal] using ih
      | foundToTab c b' =>
          simp only [List.cons_append, pullTotal, ih]
          omega

theorem raiseTotal_append (a b : List Move) :
    raiseTotal (a ++ b) = raiseTotal a + raiseTotal b := by
  induction a with
  | nil => simp [raiseTotal]
  | cons m t ih =>
      cases m with
      | draw => simpa [raiseTotal] using ih
      | wasteToFound c => simpa [raiseTotal] using ih
      | wasteToTab c b' => simpa [raiseTotal] using ih
      | tabToFound c =>
          simp only [List.cons_append, raiseTotal, ih]
          omega
      | tabToTab c b' => simpa [raiseTotal] using ih
      | foundToTab c b' => simpa [raiseTotal] using ih

/-! ## §2. One-sided counting: a raise-free leg only pulls, a pull-free leg
only raises -/

theorem raisesOf_eq_zero_of_no_raise {ρ : List Move} {σ : Suit}
    (hno : ∀ m ∈ ρ, ¬ IsRaise m) : raisesOf ρ σ = 0 := by
  induction ρ with
  | nil => rfl
  | cons m t ih =>
      have hm : ¬ IsRaise m := hno m (List.mem_cons_self ..)
      have ht : ∀ m' ∈ t, ¬ IsRaise m' :=
        fun m' hm' => hno m' (List.mem_cons_of_mem m hm')
      cases m with
      | tabToFound c => exact absurd ⟨c, rfl⟩ hm
      | draw => simpa [raisesOf] using ih ht
      | wasteToFound c => simpa [raisesOf] using ih ht
      | wasteToTab c b' => simpa [raisesOf] using ih ht
      | tabToTab c b' => simpa [raisesOf] using ih ht
      | foundToTab c b' => simpa [raisesOf] using ih ht

theorem pullsOf_eq_zero_of_no_pull {ρ : List Move} {σ : Suit}
    (hno : ∀ m ∈ ρ, ¬ IsPull m) : pullsOf ρ σ = 0 := by
  induction ρ with
  | nil => rfl
  | cons m t ih =>
      have hm : ¬ IsPull m := hno m (List.mem_cons_self ..)
      have ht : ∀ m' ∈ t, ¬ IsPull m' :=
        fun m' hm' => hno m' (List.mem_cons_of_mem m hm')
      cases m with
      | foundToTab c b' => exact absurd ⟨c, b', rfl⟩ hm
      | draw => simpa [pullsOf] using ih ht
      | wasteToFound c => simpa [pullsOf] using ih ht
      | wasteToTab c b' => simpa [pullsOf] using ih ht
      | tabToFound c => simpa [pullsOf] using ih ht
      | tabToTab c b' => simpa [pullsOf] using ih ht

/-- On a raise-free leg the pulls are exactly the total drop. -/
theorem pullsOf_add_rung_eq_of_no_raise {u v : State} {ρ : List Move} {σ : Suit}
    (hplay : ShufflePlayW u ρ v) (hno : ∀ m ∈ ρ, ¬ IsRaise m) :
    pullsOf ρ σ + rungAt v σ = rungAt u σ := by
  induction hplay with
  | nil st => simp [pullsOf]
  | @cons st s₁ W m ρ' hrev hstep hrest ih =>
      have hm : ¬ IsRaise m := hno m (List.mem_cons_self ..)
      have htail : ∀ m' ∈ ρ', ¬ IsRaise m' :=
        fun m' hm' => hno m' (List.mem_cons_of_mem m hm')
      have hIH := ih htail
      cases m with
      | draw =>
          have hr := rungAt_draw hstep σ
          simp only [pullsOf]
          omega
      | tabToFound c => exact absurd ⟨c, rfl⟩ hm
      | tabToTab c b' =>
          have hr := rungAt_tabToTab hstep σ
          simp only [pullsOf]
          omega
      | wasteToFound c => exact absurd hrev (wasteToFound_not_reversibleAtW st c)
      | wasteToTab c b' => exact absurd hrev (wasteToTab_not_reversibleAtW st c b')
      | foundToTab c b' =>
          by_cases hc : c.suit = σ
          · obtain ⟨c', htop, hc', -, -⟩ := step_foundToTab_inv hstep
            rw [hc'] at htop
            have hpos : 0 < rungAt st σ := by
              rw [← hc]; exact LedgerKit.rungAt_pos_of_foundTop htop
            have hrs : rungAt s₁ σ = rungAt st σ - 1 := by
              rw [rungAt_foundToTab hstep σ, ite_eq_left hc.symm]
            simp only [pullsOf, ite_eq_left hc]
            omega
          · have hrs : rungAt s₁ σ = rungAt st σ := by
              rw [rungAt_foundToTab hstep σ, ite_eq_right (fun h => hc h.symm)]
            simp only [pullsOf, ite_eq_right hc]
            omega

/-- On a pull-free leg the raises are exactly the total climb. -/
theorem raisesOf_add_rung_eq_of_no_pull {u v : State} {ρ : List Move} {σ : Suit}
    (hplay : ShufflePlayW u ρ v) (hno : ∀ m ∈ ρ, ¬ IsPull m) :
    raisesOf ρ σ + rungAt u σ = rungAt v σ := by
  induction hplay with
  | nil st => simp [raisesOf]
  | @cons st s₁ W m ρ' hrev hstep hrest ih =>
      have hm : ¬ IsPull m := hno m (List.mem_cons_self ..)
      have htail : ∀ m' ∈ ρ', ¬ IsPull m' :=
        fun m' hm' => hno m' (List.mem_cons_of_mem m hm')
      have hIH := ih htail
      cases m with
      | draw =>
          have hr := rungAt_draw hstep σ
          simp only [raisesOf]
          omega
      | foundToTab c b' => exact absurd ⟨c, b', rfl⟩ hm
      | tabToTab c b' =>
          have hr := rungAt_tabToTab hstep σ
          simp only [raisesOf]
          omega
      | wasteToFound c => exact absurd hrev (wasteToFound_not_reversibleAtW st c)
      | wasteToTab c b' => exact absurd hrev (wasteToTab_not_reversibleAtW st c b')
      | tabToFound c =>
          by_cases hc : c.suit = σ
          · have hrs : rungAt s₁ σ = rungAt st σ + 1 := by
              rw [rungAt_tabToFound hstep σ, ite_eq_left hc.symm]
            simp only [raisesOf, ite_eq_left hc]
            omega
          · have hrs : rungAt s₁ σ = rungAt st σ := by
              rw [rungAt_tabToFound hstep σ, ite_eq_right (fun h => hc h.symm)]
            simp only [raisesOf, ite_eq_right hc]
            omega

/-- **THE ONE-SIDED COUNT (pulls).**  A raise-free leg pulls exactly the total
drop of the `σ`-rung. -/
theorem pullsOf_eq_sub_of_no_raise {u v : State} {ρ : List Move} {σ : Suit}
    (hplay : ShufflePlayW u ρ v) (hno : ∀ m ∈ ρ, ¬ IsRaise m) :
    pullsOf ρ σ = rungAt u σ - rungAt v σ := by
  have hle : rungAt v σ ≤ rungAt u σ := rungAt_le_of_no_raise hplay hno
  have hadd := pullsOf_add_rung_eq_of_no_raise (σ := σ) hplay hno
  omega

/-- **THE ONE-SIDED COUNT (raises).**  A pull-free leg raises exactly the total
climb of the `σ`-rung. -/
theorem raisesOf_eq_sub_of_no_pull {u v : State} {ρ : List Move} {σ : Suit}
    (hplay : ShufflePlayW u ρ v) (hno : ∀ m ∈ ρ, ¬ IsPull m) :
    raisesOf ρ σ = rungAt v σ - rungAt u σ := by
  have hle : rungAt u σ ≤ rungAt v σ := rungAt_le_of_no_pull hplay hno
  have hadd := raisesOf_add_rung_eq_of_no_pull (σ := σ) hplay hno
  omega

/-! ## §3. THE ACCOUNTING IDENTITY -/

/-- **THE ACCOUNTING IDENTITY (mountain form).**  If `ρ = α ++ β` with the left
leg raise-free and the right leg pull-free, then for every suit the number of
`σ`-braces is exactly the sum of the two drops to the turn value:

```
pullsOf ρ σ + raisesOf ρ σ
  = (rungAt u σ − rungAt F σ) + (rungAt v σ − rungAt F σ)
```

This is `Temp/Mountain_Report.md:27-31`'s `TV(h_σ)` formula, unconditionally —
no minimality is consumed.  It composes with `MountainSplit` by construction. -/
theorem accounting_of_mountainSplit {u v F : State} {α β : List Move} {σ : Suit}
    (hα : ShufflePlayW u α F) (hβ : ShufflePlayW F β v)
    (hms : MountainSplit α β) :
    pullsOf (α ++ β) σ + raisesOf (α ++ β) σ =
      (rungAt u σ - rungAt F σ) + (rungAt v σ - rungAt F σ) := by
  rw [pullsOf_append, raisesOf_append]
  have hpα : pullsOf α σ = rungAt u σ - rungAt F σ :=
    pullsOf_eq_sub_of_no_raise hα hms.1
  have hrα : raisesOf α σ = 0 := raisesOf_eq_zero_of_no_raise hms.1
  have hrβ : raisesOf β σ = rungAt v σ - rungAt F σ :=
    raisesOf_eq_sub_of_no_pull hβ hms.2
  have hpβ : pullsOf β σ = 0 := pullsOf_eq_zero_of_no_pull hms.2
  rw [hpα, hrα, hrβ, hpβ]
  omega

/-! ## §4. The turn state is the componentwise minimum of the walk -/

/-- **`RungAboveFrom u ref ρ σ`** — every state reached by a prefix of the play
`ρ` (performed from `u`) has `σ`-rung at least `rungAt ref σ`.  This is the
"`ref` is a floor of the walk" read. -/
def RungAboveFrom (u ref : State) (ρ : List Move) (σ : Suit) : Prop :=
  ∀ (a b : List Move) (y : State), ρ = a ++ b → u.run a = some y →
    rungAt ref σ ≤ rungAt y σ

/-- **`RungMinAlong u ρ σ m`** — `m` is the *minimum of the `σ`-rung along the
play*: all visited rungs are `≥ m`, and `m` is attained.  This is the probe's
`m_σ` (`Temp/Mountain_Report.md:27-38`). -/
def RungMinAlong (u : State) (ρ : List Move) (σ : Suit) (m : Nat) : Prop :=
  (∀ (a b : List Move) (y : State), ρ = a ++ b → u.run a = some y →
      m ≤ rungAt y σ) ∧
    (∃ (a b : List Move) (y : State), ρ = a ++ b ∧ u.run a = some y ∧
      rungAt y σ = m)

/-- A raise-free leg never returns above its endpoint. -/
theorem rungAboveFrom_of_no_raise {u F : State} {α : List Move} {σ : Suit}
    (hα : ShufflePlayW u α F) (hno : ∀ m ∈ α, ¬ IsRaise m) :
    RungAboveFrom u F α σ := by
  intro a b y hab hrun
  obtain ⟨F', h1, h2⟩ := ShufflePlayW_split hα a b hab
  have hF'y : F' = y := Option.some.inj ((Walk_run _ h1).symm.trans hrun)
  subst hF'y
  exact rungAt_le_of_no_raise h2
    (fun m' hm' => hno m' (by rw [hab]; exact List.mem_append_right _ hm'))

/-- A pull-free leg never returns below its origin. -/
theorem rungAboveFrom_of_no_pull {F v : State} {β : List Move} {σ : Suit}
    (hβ : ShufflePlayW F β v) (hno : ∀ m ∈ β, ¬ IsPull m) :
    RungAboveFrom F F β σ := by
  intro a b y hab hrun
  obtain ⟨F', h1, h2⟩ := ShufflePlayW_split hβ a b hab
  have hF'y : F' = y := Option.some.inj ((Walk_run _ h1).symm.trans hrun)
  subst hF'y
  exact rungAt_le_of_no_pull h1
    (fun m' hm' => hno m' (by rw [hab]; exact List.mem_append_left _ hm'))

/-- The two floors glue: the turn value floors the whole play. -/
theorem rungAboveFrom_append {u v F : State} {α β : List Move} {σ : Suit}
    (hα : ShufflePlayW u α F) (hβ : ShufflePlayW F β v)
    (hL : RungAboveFrom u F α σ) (hR : RungAboveFrom F F β σ) :
    RungAboveFrom u F (α ++ β) σ := by
  intro a b y hab hrun
  rcases append_prefix_cases α a β b hab with ⟨δ, hδ⟩ | ⟨δ, hδ⟩
  · -- `a` is a prefix of the left leg
    exact hL a δ y hδ hrun
  · -- `a` runs through the left leg and into the right one
    subst hδ
    have hrunα : u.run α = some F := Walk_run _ hα
    have hβEq : β = δ ++ b := by
      have hhab : α ++ β = α ++ (δ ++ b) := by
        rw [hab, List.append_assoc]
      exact List.append_cancel_left hhab
    obtain ⟨z, hz1, hz2⟩ := run_append_split u α δ y hrun
    have hzF : z = F := Option.some.inj (hz1.symm.trans hrunα)
    subst hzF
    exact hR δ b y hβEq hz2

/-- **THE TURN REALISES THE DIP.**  Under `MountainSplit` the turn state's rung
vector is the componentwise minimum of the whole play's rung walk. -/
theorem rungMinAlong_of_mountainSplit {u v F : State} {α β : List Move} {σ : Suit}
    (hα : ShufflePlayW u α F) (hβ : ShufflePlayW F β v)
    (hms : MountainSplit α β) :
    RungMinAlong u (α ++ β) σ (rungAt F σ) := by
  refine ⟨?_, ⟨α, β, F, rfl, Walk_run _ hα, rfl⟩⟩
  exact rungAboveFrom_append hα hβ (rungAboveFrom_of_no_raise hα hms.1)
    (rungAboveFrom_of_no_pull hβ hms.2)

/-- The dip, stated with an abstract minimum `m`: it can only be the turn value. -/
theorem accounting_of_rungMinAlong {u v F : State} {α β : List Move} {σ : Suit}
    {m : Nat} (hα : ShufflePlayW u α F) (hβ : ShufflePlayW F β v)
    (hms : MountainSplit α β) (hmin : RungMinAlong u (α ++ β) σ m) :
    pullsOf (α ++ β) σ + raisesOf (α ++ β) σ =
      (rungAt u σ - m) + (rungAt v σ - m) := by
  have hF : rungAt F σ = m := by
    have h1 : m ≤ rungAt F σ := hmin.1 α β F rfl (Walk_run _ hα)
    have h2 : rungAt F σ ≤ m := by
      obtain ⟨a, b, y, hab, hrun, hy⟩ := hmin.2
      have := (rungMinAlong_of_mountainSplit (σ := σ) hα hβ hms).1 a b y hab hrun
      omega
    omega
  rw [accounting_of_mountainSplit hα hβ hms, hF]

/-! ## §5. The census form: brackets + free letters = length, and the dip -/

/-- Letters of a witness play are free, pulls or raises. -/
theorem free_or_pull_or_raise_of_reversible {st : State} {m : Move}
    (hrev : reversibleAtW st m) : FreeMove m ∨ IsPull m ∨ IsRaise m := by
  cases m with
  | draw => exact Or.inl (Or.inl rfl)
  | tabToTab c b => exact Or.inl (Or.inr ⟨c, b, rfl⟩)
  | foundToTab c b => exact Or.inr (Or.inl ⟨c, b, rfl⟩)
  | tabToFound c => exact Or.inr (Or.inr ⟨c, rfl⟩)
  | wasteToFound c => exact absurd hrev (wasteToFound_not_reversibleAtW st c)
  | wasteToTab c b => exact absurd hrev (wasteToTab_not_reversibleAtW st c b)

theorem free_or_pull_or_raise_of_play {u v : State} {ρ : List Move}
    (hplay : ShufflePlayW u ρ v) :
    ∀ m ∈ ρ, FreeMove m ∨ IsPull m ∨ IsRaise m := by
  induction hplay with
  | nil st => intro m hm; simp at hm
  | @cons st s₁ W m ρ' hrev hstep hrest ih =>
      intro m' hm'
      rcases List.mem_cons.mp hm' with rfl | hm''
      · exact free_or_pull_or_raise_of_reversible hrev
      · exact ih m' hm''

/-- The free letters of a play (`draw` and `tabToTab` — the reversibility
filter, so the waste letters never contribute). -/
def freeCount : List Move → Nat
  | [] => 0
  | Move.draw :: t => freeCount t + 1
  | Move.tabToTab _ _ :: t => freeCount t + 1
  | _ :: t => freeCount t

/-- **LENGTH = BRACKETS + FREE LETTERS.**  A first-cut reading of
`Temp/Mountain_Report.md:30-36`'s `length = bracket count + #free`. -/
theorem length_eq_counters {ρ : List Move}
    (h : ∀ m ∈ ρ, FreeMove m ∨ IsPull m ∨ IsRaise m) :
    pullTotal ρ + raiseTotal ρ + freeCount ρ = ρ.length := by
  induction ρ with
  | nil => rfl
  | cons m t ih =>
      have hm := h m (List.mem_cons_self ..)
      have ht : ∀ m' ∈ t, FreeMove m' ∨ IsPull m' ∨ IsRaise m' :=
        fun m' hm' => h m' (List.mem_cons_of_mem m hm')
      have hIH := ih ht
      cases m with
      | draw =>
          simp only [pullTotal, raiseTotal, freeCount, List.length_cons]
          omega
      | tabToTab c b =>
          simp only [pullTotal, raiseTotal, freeCount, List.length_cons]
          omega
      | foundToTab c b =>
          simp only [pullTotal, raiseTotal, freeCount, List.length_cons]
          omega
      | tabToFound c =>
          simp only [pullTotal, raiseTotal, freeCount, List.length_cons]
          omega
      | wasteToFound c => simp [FreeMove, IsPull, IsRaise] at hm
      | wasteToTab c b => simp [FreeMove, IsPull, IsRaise] at hm

/-- Total pulls, per suit. -/
theorem pullTotal_eq_suits (ρ : List Move) :
    pullTotal ρ = pullsOf ρ .spade + pullsOf ρ .heart
      + pullsOf ρ .diamond + pullsOf ρ .club := by
  induction ρ with
  | nil => rfl
  | cons m t ih =>
      cases m with
      | draw => simpa [pullTotal, pullsOf] using ih
      | wasteToFound c => simpa [pullTotal, pullsOf] using ih
      | wasteToTab c b => simpa [pullTotal, pullsOf] using ih
      | tabToFound c => simpa [pullTotal, pullsOf] using ih
      | tabToTab c b => simpa [pullTotal, pullsOf] using ih
      | foundToTab c b =>
          cases h : c.suit with
          | spade => simp [pullTotal, pullsOf, h]; omega
          | heart => simp [pullTotal, pullsOf, h]; omega
          | diamond => simp [pullTotal, pullsOf, h]; omega
          | club => simp [pullTotal, pullsOf, h]; omega

/-- Total raises, per suit. -/
theorem raiseTotal_eq_suits (ρ : List Move) :
    raiseTotal ρ = raisesOf ρ .spade + raisesOf ρ .heart
      + raisesOf ρ .diamond + raisesOf ρ .club := by
  induction ρ with
  | nil => rfl
  | cons m t ih =>
      cases m with
      | draw => simpa [raiseTotal, raisesOf] using ih
      | wasteToFound c => simpa [raiseTotal, raisesOf] using ih
      | wasteToTab c b => simpa [raiseTotal, raisesOf] using ih
      | foundToTab c b => simpa [raiseTotal, raisesOf] using ih
      | tabToTab c b => simpa [raiseTotal, raisesOf] using ih
      | tabToFound c =>
          cases h : c.suit with
          | spade => simp [raiseTotal, raisesOf, h]; omega
          | heart => simp [raiseTotal, raisesOf, h]; omega
          | diamond => simp [raiseTotal, raisesOf, h]; omega
          | club => simp [raiseTotal, raisesOf, h]; omega

/-- **THE BRACKET COUNT IS THE DIP SUM.**  The total number of bracket letters
between the endpoints is `Σ_σ (h_σ(u) + h_σ(v) − 2 h_σ(F))`, the dip formula of
`Temp/Mountain_Report.md:34`. -/
def bracketDip (u v F : State) : Nat :=
  ((rungAt u .spade - rungAt F .spade) + (rungAt v .spade - rungAt F .spade))
  + ((rungAt u .heart - rungAt F .heart) + (rungAt v .heart - rungAt F .heart))
  + ((rungAt u .diamond - rungAt F .diamond) + (rungAt v .diamond - rungAt F .diamond))
  + ((rungAt u .club - rungAt F .club) + (rungAt v .club - rungAt F .club))

theorem bracketTotal_eq_bracketDip {u v F : State} {α β : List Move}
    (hα : ShufflePlayW u α F) (hβ : ShufflePlayW F β v)
    (hms : MountainSplit α β) :
    pullTotal (α ++ β) + raiseTotal (α ++ β) = bracketDip u v F := by
  rw [pullTotal_eq_suits, raiseTotal_eq_suits]
  unfold bracketDip
  have hs := accounting_of_mountainSplit (σ := .spade) hα hβ hms
  have hh := accounting_of_mountainSplit (σ := .heart) hα hβ hms
  have hd := accounting_of_mountainSplit (σ := .diamond) hα hβ hms
  have hc := accounting_of_mountainSplit (σ := .club) hα hβ hms
  omega

/-- **THE CENSUS IDENTITY.**  `length = Σ_σ (h_σ(u) + h_σ(v) − 2 m_σ) + #free`.
`Temp/Mountain_Report.md:30-36`, proved. -/
theorem length_eq_bracketDip_plus_free {u v F : State} {α β : List Move}
    (hα : ShufflePlayW u α F) (hβ : ShufflePlayW F β v)
    (hms : MountainSplit α β) :
    (α ++ β).length = bracketDip u v F + freeCount (α ++ β) := by
  have hplay : ShufflePlayW u (α ++ β) v := ShufflePlayW_append hα hβ
  have hlen := length_eq_counters (free_or_pull_or_raise_of_play hplay)
  have hbr := bracketTotal_eq_bracketDip hα hβ hms
  omega

/-- The L1 ledger of the ordered pair. -/
def l1Rung (u v : State) : Nat :=
  (max (rungAt u .spade) (rungAt v .spade)
    - min (rungAt u .spade) (rungAt v .spade))
  + (max (rungAt u .heart) (rungAt v .heart)
    - min (rungAt u .heart) (rungAt v .heart))
  + (max (rungAt u .diamond) (rungAt v .diamond)
    - min (rungAt u .diamond) (rungAt v .diamond))
  + (max (rungAt u .club) (rungAt v .club)
    - min (rungAt u .club) (rungAt v .club))

/-- The componentwise dip below the pair's L1 ledger. -/
def dipVec (u v F : State) : Nat :=
  (min (rungAt u .spade) (rungAt v .spade) - rungAt F .spade)
  + (min (rungAt u .heart) (rungAt v .heart) - rungAt F .heart)
  + (min (rungAt u .diamond) (rungAt v .diamond) - rungAt F .diamond)
  + (min (rungAt u .club) (rungAt v .club) - rungAt F .club)

/-- **THE SURPLUS OVER THE L1 LEDGER IS `2 · dip`.**  Given the mountain bottom
is componentwise below both endpoints, the bracket count exceeds the plain L1
ledger by exactly twice the dip vector — the measured surplus of
`Temp/Mountain_Report.md:38-40`. -/
theorem bracketDip_eq_l1_add_two_dip {u v F : State}
    (hb : ∀ σ : Suit, rungAt F σ ≤ rungAt u σ ∧ rungAt F σ ≤ rungAt v σ) :
    bracketDip u v F = l1Rung u v + 2 * dipVec u v F := by
  have hsp := hb .spade
  have hhe := hb .heart
  have hdi := hb .diamond
  have hcl := hb .club
  unfold bracketDip l1Rung dipVec
  omega

/-- **THE CENSUS IS PAIR-INTRINSIC ONCE THE DIP IS.**  Two census identities with
the same dip sum and the same free-letter count give equal lengths.  This is the
arithmetic face of the probe's INT rows (`Temp/Mountain_Report.md:16-17`): the
dip and the free count are what determine a minimal length. -/
theorem length_eq_of_census {u v F₁ F₂ : State} {ρ₁ ρ₂ : List Move}
    (h₁ : ρ₁.length = bracketDip u v F₁ + freeCount ρ₁)
    (h₂ : ρ₂.length = bracketDip u v F₂ + freeCount ρ₂)
    (hd : bracketDip u v F₁ = bracketDip u v F₂)
    (hf : freeCount ρ₁ = freeCount ρ₂) : ρ₁.length = ρ₂.length := by
  omega

/-! ## §6. Axiom battery -/

#print axioms MountainKit.append_prefix_cases
#print axioms MountainKit.pullsOf_append
#print axioms MountainKit.raisesOf_append
#print axioms MountainKit.pullTotal_append
#print axioms MountainKit.raiseTotal_append
#print axioms MountainKit.raisesOf_eq_zero_of_no_raise
#print axioms MountainKit.pullsOf_eq_zero_of_no_pull
#print axioms MountainKit.pullsOf_eq_sub_of_no_raise
#print axioms MountainKit.raisesOf_eq_sub_of_no_pull
#print axioms MountainKit.accounting_of_mountainSplit
#print axioms MountainKit.rungAboveFrom_of_no_raise
#print axioms MountainKit.rungAboveFrom_of_no_pull
#print axioms MountainKit.rungAboveFrom_append
#print axioms MountainKit.rungMinAlong_of_mountainSplit
#print axioms MountainKit.accounting_of_rungMinAlong
#print axioms MountainKit.free_or_pull_or_raise_of_play
#print axioms MountainKit.length_eq_counters
#print axioms MountainKit.pullTotal_eq_suits
#print axioms MountainKit.raiseTotal_eq_suits
#print axioms MountainKit.bracketTotal_eq_bracketDip
#print axioms MountainKit.length_eq_bracketDip_plus_free
#print axioms MountainKit.length_eq_of_census
#print axioms MountainKit.bracketDip_eq_l1_add_two_dip

end MountainKit


