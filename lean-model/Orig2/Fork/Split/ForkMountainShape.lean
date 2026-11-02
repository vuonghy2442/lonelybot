import Orig2.Fork.Split.ForkMountain
import Orig2.Fork.Split.ForkLedger
import Orig2.Fork.Split.ForkSplit
import Orig2.Fork.Class.ForkMinCross
import Orig2.Fork.Class.ForkExist
import Orig2.Fork.Class.ForkLivePair
import Orig2.Fork.Third.ForkNonfork
import Orig2.Fork.Split.ForkMountainAccount

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-!
# Mountain2_Shape — M1 / M2 / M3 as named residuals, and what they buy

READ-ONLY scratch card (`Temp/`).  No source edit, no commit.  `sorry`-free,
`Classical.choice`-free, `native_decide`-free.

`Temp/Mountain_Report.md` measured three shape statements over 51 116 minimal
plays:

```
M1  no raise occurs before a later pull
M2  each suit's rung walk has no up-then-down (unimodal)
M3  a free letter sits between the last pull and the first raise
```

Here:

* **§1**  M1 is a *letter-order* statement and is EXACTLY a `MountainSplit`
  decomposition (`noRaiseBeforePull_iff_split`).  Nothing about minimality.
* **§2**  M1 ⇒ M2, proved: a raise-free leg descends and a pull-free leg
  ascends, so no up-then-down can occur (`noUpThenDown_of_mountainSplit`).
* **§3**  `MountainShape` — the named residual (M1 + M3, with M2 derived), and
  its unconditional consequences: the turn is the componentwise dip
  (`dip_of_mountainShape`), the accounting identity, and the census identity
  `length = Σ_σ (h u + h v − 2m) + #free`.
* **§4**  the M1 reduction: `RaiseBeforePullShortens` (a deletion residual)
  ⇒ M1 for minimal plays ⇒ `MountainShape`.
* **§5**  the joint residual with the dip-fibre fork: `MountainShape` together
  with `DipFibreFork` gives `MinKit.MinCrossesFork`, hence (with
  `ShortestPlayExists`) `SatDifferForkWF`.  `DipFibreFork` is the *only*
  missing conjunct.
-/

namespace MountainKit

open ValleyElim
open Bubble

/-! ## §1. M1 is exactly a `MountainSplit` decomposition -/

/-- **A raise before a later pull.**  `ρ` splits as `pre ++ raise c :: post`
and some `σ`-pull sits in `post`. -/
def RaiseBeforePull (ρ : List Move) : Prop :=
  ∃ (pre post : List Move) (c : Card) (d : Card) (b : Base),
    ρ = pre ++ Move.tabToFound c :: post ∧ Move.foundToTab d b ∈ post

/-- Cancelling a common prefix of lists. -/
theorem append_cancel_pre {a b c : List Move} (h : a ++ b = a ++ c) : b = c := by
  induction a with
  | nil => simpa using h
  | cons x xs ih =>
      simp only [List.cons_append, List.cons.injEq] at h
      exact ih h.2

/-- **M1's letter-order read** — no raise occurs before a later pull. -/
def NoRaiseBeforePull (ρ : List Move) : Prop := ¬ RaiseBeforePull ρ

/-- Prepending any letter preserves a raise-before-pull witness inside the
tail. -/
theorem raiseBeforePull_cons {m : Move} {t : List Move}
    (h : RaiseBeforePull t) : RaiseBeforePull (m :: t) := by
  obtain ⟨pre, post, c, d, b, heq, hmem⟩ := h
  exact ⟨m :: pre, post, c, d, b, by rw [heq, List.cons_append], hmem⟩

/-- Prepending a letter of ANY kind to a no-violation list keeps it a
no-violation list. -/
theorem raiseBeforePull_tail {m : Move} {t : List Move}
    (hm : ¬ IsRaise m) (h : RaiseBeforePull (m :: t)) : RaiseBeforePull t := by
  obtain ⟨pre, post, c, d, b, heq, hmem⟩ := h
  cases pre with
  | nil =>
      simp only [List.nil_append, List.cons.injEq] at heq
      exact absurd ⟨c, heq.1⟩ hm
  | cons x pre' =>
      simp only [List.cons_append, List.cons.injEq] at heq
      exact ⟨pre', post, c, d, b, heq.2, hmem⟩

/-- The induction step of `split_of_noRaiseBeforePull`, for a non-raise head. -/
theorem split_cons_of_not_raise {m : Move} {t : List Move}
    (hm : ¬ IsRaise m) (h : NoRaiseBeforePull (m :: t))
    (ih : NoRaiseBeforePull t → ∃ α β : List Move, t = α ++ β ∧ MountainSplit α β) :
    ∃ α β : List Move, (m :: t) = α ++ β ∧ MountainSplit α β := by
  have htail : NoRaiseBeforePull t := fun hbad => h (raiseBeforePull_cons hbad)
  obtain ⟨α, β, heq, hms⟩ := ih htail
  refine ⟨m :: α, β, by rw [heq, List.cons_append], ⟨?_, hms.2⟩⟩
  intro m' hm'
  rcases List.mem_cons.mp hm' with rfl | hm''
  · exact hm
  · exact hms.1 m' hm''

/-- **M1 → a `MountainSplit` decomposition.** -/
theorem split_of_noRaiseBeforePull :
    ∀ {ρ : List Move}, NoRaiseBeforePull ρ →
      ∃ α β : List Move, ρ = α ++ β ∧ MountainSplit α β
  | [], _ => ⟨[], [], rfl, ⟨by intro m hm; simp at hm, by intro m hm; simp at hm⟩⟩
  | m :: t, h => by
      cases m with
      | tabToFound c =>
          refine ⟨[], Move.tabToFound c :: t, rfl, ⟨?_, ?_⟩⟩
          · intro m' hm'; simp at hm'
          · intro m' hm' hpull
            obtain ⟨d, b, rfl⟩ := hpull
            rcases List.mem_cons.mp hm' with heq | hmem
            · cases heq
            · exact h ⟨[], t, c, d, b, rfl, hmem⟩
      | draw => exact split_cons_of_not_raise (by simp [IsRaise]) h split_of_noRaiseBeforePull
      | wasteToFound c =>
          exact split_cons_of_not_raise (by simp [IsRaise]) h split_of_noRaiseBeforePull
      | wasteToTab c b =>
          exact split_cons_of_not_raise (by simp [IsRaise]) h split_of_noRaiseBeforePull
      | tabToTab c b =>
          exact split_cons_of_not_raise (by simp [IsRaise]) h split_of_noRaiseBeforePull
      | foundToTab c b =>
          exact split_cons_of_not_raise (by simp [IsRaise]) h split_of_noRaiseBeforePull

/-- **A `MountainSplit` decomposition → M1.**  This is the easy direction: a
raise can only live in the right leg, a pull only in the left one, and the left
leg precedes the right one. -/
theorem noRaiseBeforePull_of_split {ρ α β : List Move}
    (heq : ρ = α ++ β) (hms : MountainSplit α β) : NoRaiseBeforePull ρ := by
  intro hbad
  obtain ⟨pre, post, c, d, b, hρ, hmem⟩ := hbad
  have h : α ++ β = pre ++ Move.tabToFound c :: post := by rw [← heq, hρ]
  rcases append_prefix_cases α pre β (Move.tabToFound c :: post) h with
    ⟨δ, hδ⟩ | ⟨δ, hδ⟩
  · -- the raise is at or inside the left leg, or opens the right leg
    subst hδ
    have hsplit : δ ++ β = Move.tabToFound c :: post := by
      have h2 : pre ++ (δ ++ β) = pre ++ (Move.tabToFound c :: post) := by
        rw [← List.append_assoc]; exact h
      exact append_cancel_pre h2
    cases δ with
    | nil =>
        -- `raise c` opens the right leg; the pull is in `post ⊆ β`
        have hβ : β = Move.tabToFound c :: post := hsplit
        exact hms.2 (Move.foundToTab d b)
          (by rw [hβ]; exact List.mem_cons_of_mem _ hmem) ⟨d, b, rfl⟩
    | cons x xs =>
        -- `x = raise c` is the head of `δ`, hence inside the left leg
        have hx : x = Move.tabToFound c := (List.cons.inj hsplit).1
        have hmemα : Move.tabToFound c ∈ pre ++ (x :: xs) := by
          apply List.mem_append_right
          rw [hx]
          exact List.mem_cons_self ..
        exact hms.1 _ hmemα ⟨c, rfl⟩
  · -- the pull sits past the left leg, inside the right one
    have hβ : β = δ ++ Move.tabToFound c :: post := by
      have h2 : α ++ β = α ++ (δ ++ Move.tabToFound c :: post) := by
        calc α ++ β = pre ++ Move.tabToFound c :: post := h
          _ = (α ++ δ) ++ Move.tabToFound c :: post := by rw [hδ]
          _ = α ++ (δ ++ Move.tabToFound c :: post) := List.append_assoc ..
      exact append_cancel_pre h2
    refine hms.2 (Move.foundToTab d b) ?_ ⟨d, b, rfl⟩
    rw [hβ]
    exact List.mem_append_right δ (List.mem_cons_of_mem _ hmem)

/-- **M1 ⟺ `MountainSplit`.** -/
theorem noRaiseBeforePull_iff_split {ρ : List Move} :
    NoRaiseBeforePull ρ ↔ ∃ α β : List Move, ρ = α ++ β ∧ MountainSplit α β := by
  constructor
  · exact split_of_noRaiseBeforePull
  · rintro ⟨α, β, heq, hms⟩
    exact noRaiseBeforePull_of_split heq hms

/-! ## §2. M1 ⇒ M2: monotone legs have no up-then-down -/

/-- **M2's content.**  The `σ`-walk of a play has no up-then-down: there are no
three visited positions `y` (earlier), `z` (middle), `w` (later) with
`h y < h z` and `h w < h z`. -/
def NoUpThenDown (u : State) (ρ : List Move) (σ : Suit) : Prop :=
  ¬ ∃ (a b c : List Move) (y z w : State),
      ρ = a ++ b ++ c ∧ u.run a = some y ∧ u.run (a ++ b) = some z ∧
        u.run ((a ++ b) ++ c) = some w ∧
        rungAt y σ < rungAt z σ ∧ rungAt w σ < rungAt z σ

/-- On a raise-free leg, a LATER prefix has a `≤` rung. -/
theorem rung_le_later_of_no_raise {u F : State} {α : List Move} {σ : Suit}
    (hα : ShufflePlayW u α F) (hno : ∀ m ∈ α, ¬ IsRaise m)
    {a b c : List Move} (hac : α = a ++ b ++ c) {y z : State}
    (hy : u.run a = some y) (hz : u.run (a ++ b) = some z) :
    rungAt z σ ≤ rungAt y σ := by
  have hab : α = a ++ (b ++ c) := by rw [hac, List.append_assoc]
  obtain ⟨A, hA, hbc⟩ := ShufflePlayW_split hα a (b ++ c) hab
  have hAy : A = y := Option.some.inj ((Walk_run _ hA).symm.trans hy)
  obtain ⟨B, hB, hC⟩ := ShufflePlayW_split hbc b c rfl
  have hB' : ShufflePlayW y b B := hAy ▸ hB
  have hb : y.run b = some z := by
    obtain ⟨y', hy', hyb⟩ := run_append_split u a b z hz
    have hyy : y' = y := Option.some.inj (hy'.symm.trans hy)
    rw [← hyy]
    exact hyb
  have hBz : B = z := Option.some.inj ((Walk_run _ hB').symm.trans hb)
  have hle := rungAt_le_of_no_raise (σ := σ) hB'
    (fun m' hm' => hno m' (by
      rw [hab]
      simp only [List.mem_append]
      exact Or.inr (Or.inl hm')))
  rw [hBz] at hle
  exact hle

/-- On a pull-free leg, a LATER prefix has a `≥` rung. -/
theorem rung_le_later_of_no_pull {F v : State} {β : List Move} {σ : Suit}
    (hβ : ShufflePlayW F β v) (hno : ∀ m ∈ β, ¬ IsPull m)
    {a b c : List Move} (hac : β = a ++ b ++ c) {y z : State}
    (hy : F.run a = some y) (hz : F.run (a ++ b) = some z) :
    rungAt y σ ≤ rungAt z σ := by
  have hab : β = a ++ (b ++ c) := by rw [hac, List.append_assoc]
  obtain ⟨A, hA, hbc⟩ := ShufflePlayW_split hβ a (b ++ c) hab
  have hAy : A = y := Option.some.inj ((Walk_run _ hA).symm.trans hy)
  obtain ⟨B, hB, hC⟩ := ShufflePlayW_split hbc b c rfl
  have hB' : ShufflePlayW y b B := hAy ▸ hB
  have hb : y.run b = some z := by
    obtain ⟨y', hy', hyb⟩ := run_append_split F a b z hz
    have hyy : y' = y := Option.some.inj (hy'.symm.trans hy)
    rw [← hyy]
    exact hyb
  have hBz : B = z := Option.some.inj ((Walk_run _ hB').symm.trans hb)
  have hle := rungAt_le_of_no_pull (σ := σ) hB'
    (fun m' hm' => hno m' (by
      rw [hab]
      simp only [List.mem_append]
      exact Or.inr (Or.inl hm')))
  rw [hBz] at hle
  exact hle

/-- **M1 ⇒ M2** (per suit): a raise-free left leg and a pull-free right leg leave
no room for an up-then-down. -/
theorem noUpThenDown_of_mountainSplit {u v F : State} {α β : List Move}
    (hα : ShufflePlayW u α F) (hβ : ShufflePlayW F β v) (hms : MountainSplit α β)
    (σ : Suit) : NoUpThenDown u (α ++ β) σ := by
  rintro ⟨a, b, c, y, z, w, heq, hy, hz, hw, hyz, hwz⟩
  -- align the middle prefix `a ++ b` against the split point
  have h : α ++ β = (a ++ b) ++ c := heq
  rcases append_prefix_cases α (a ++ b) β c h with ⟨δ, hδ⟩ | ⟨δ, hδ⟩
  · -- the middle position `z` is on the descending leg
    have hac : α = a ++ b ++ δ := hδ
    have hle := rung_le_later_of_no_raise (σ := σ) hα hms.1 hac hy hz
    omega
  · -- both `z` and `w` are on the ascending leg
    have hβEq : β = δ ++ c := by
      have h2 : α ++ β = α ++ (δ ++ c) := by rw [heq, hδ, List.append_assoc]
      exact append_cancel_pre h2
    have hzα : u.run (α ++ δ) = some z := by rw [← hδ]; exact hz
    have hz' : F.run δ = some z := by
      obtain ⟨z', hz1, hz2⟩ := run_append_split u α δ z hzα
      have hzF : z' = F := Option.some.inj (hz1.symm.trans (Walk_run _ hα))
      rw [← hzF]
      exact hz2
    have hwα : u.run (α ++ (δ ++ c)) = some w := by
      rw [← List.append_assoc, ← hδ]
      exact hw
    have hw' : F.run (δ ++ c) = some w := by
      obtain ⟨w', hw1, hw2⟩ := run_append_split u α (δ ++ c) w hwα
      have hwF : w' = F := Option.some.inj (hw1.symm.trans (Walk_run _ hα))
      rw [← hwF]
      exact hw2
    have hac : β = δ ++ c ++ [] := by rw [hβEq]; simp
    have hle := rung_le_later_of_no_pull (σ := σ) hβ hms.2 hac hz' hw'
    omega

/-! ## §3. The named residual `MountainShape` and its consequences -/

/-- **M3's letter form.**  No pull is immediately followed by a raise.  Inside a
mountain play (all pulls before all raises) this is exactly M3: the only
adjacency that can straddle the turn is a `pull ; raise` pair, so "a free letter
sits between the last pull and the first raise" says precisely that no such pair
occurs.  (`adjacent_at_turn_of_mountainSplit` proves the alignment.) -/
def NoAdjacentPullRaise (ρ : List Move) : Prop :=
  ¬ ∃ (pre tail : List Move) (c d : Card) (b : Base),
      ρ = pre ++ Move.foundToTab c b :: Move.tabToFound d :: tail

/-- The last element of a `pre ++ [x]` decomposition lies in the nonempty right
summand of any other decomposition. -/
theorem last_mem_right {pre α δ : List Move} {x : Move}
    (h : pre ++ [x] = α ++ δ) (hne : δ ≠ []) : x ∈ δ := by
  induction pre generalizing α with
  | nil =>
      cases α with
      | nil =>
          have h' : ([x] : List Move) = δ := by simpa using h
          rw [← h']
          exact List.mem_cons_self ..
      | cons a as =>
          exfalso
          have h1 : ([x] : List Move) = a :: (as ++ δ) := by simpa only [List.nil_append, List.cons_append] using h
          have htail : as ++ δ = [] := (List.cons.inj h1).2.symm
          exact hne (List.append_eq_nil_iff.mp htail).2
  | cons p ps ih =>
      cases α with
      | nil =>
          have h' : p :: (ps ++ [x]) = δ := by simpa only [List.nil_append, List.cons_append] using h
          rw [← h']
          exact List.mem_cons_of_mem p (List.mem_append_right ps (List.mem_cons_self ..))
      | cons a as =>
          have htail : ps ++ [x] = as ++ δ := by
            have h1 : p :: (ps ++ [x]) = a :: (as ++ δ) := by
              simpa only [List.cons_append] using h
            exact (List.cons.inj h1).2
          exact ih htail

/-- **THE TURN IS WHERE AN ADJACENT `pull ; raise` CAN LIVE.**  In a mountain
play an adjacent pull/raise pair necessarily straddles the turn: the left leg
ends with the pull and the right leg opens with the raise.  This is the
alignment that identifies `NoAdjacentPullRaise` with M3. -/
theorem adjacent_at_turn_of_mountainSplit {ρ α β : List Move} (heq : ρ = α ++ β)
    (hms : MountainSplit α β) {pre tail : List Move} {c d : Card} {b : Base}
    (h : ρ = pre ++ Move.foundToTab c b :: Move.tabToFound d :: tail) :
    α = pre ++ [Move.foundToTab c b] ∧ β = Move.tabToFound d :: tail := by
  have h2 : α ++ β = (pre ++ [Move.foundToTab c b]) ++ (Move.tabToFound d :: tail) := by
    rw [← heq, h, List.append_assoc]
    rfl
  rcases append_prefix_cases α (pre ++ [Move.foundToTab c b]) β
    (Move.tabToFound d :: tail) h2 with ⟨δ, hδ⟩ | ⟨δ, hδ⟩
  · -- the left leg contains the whole prefix `pre ++ [pull]`
    have hsplit : Move.tabToFound d :: tail = δ ++ β := by
      have hh : (pre ++ [Move.foundToTab c b]) ++ (δ ++ β) =
          (pre ++ [Move.foundToTab c b]) ++ (Move.tabToFound d :: tail) := by
        rw [← List.append_assoc, ← hδ]
        exact h2
      exact (append_cancel_pre hh).symm
    cases δ with
    | nil => exact ⟨by rw [hδ, List.append_nil], hsplit.symm⟩
    | cons x xs =>
        exfalso
        have hx : x = Move.tabToFound d := (List.cons.inj hsplit).1.symm
        have hmem : Move.tabToFound d ∈ (pre ++ [Move.foundToTab c b]) ++ (x :: xs) := by
          apply List.mem_append_right
          rw [hx]
          exact List.mem_cons_self ..
        exact hms.1 _ (hδ ▸ hmem) ⟨d, rfl⟩
  · -- the pull lies beyond the left leg
    cases δ with
    | nil =>
        refine ⟨?_, ?_⟩
        · rw [hδ]; simp
        · have hh : α ++ β = α ++ (Move.tabToFound d :: tail) := by
            rw [h2, hδ, List.append_assoc]
            simp
          exact append_cancel_pre hh
    | cons x xs =>
        exfalso
        have hpullδ : Move.foundToTab c b ∈ (x :: xs) :=
          last_mem_right hδ (by simp)
        have hβ : β = (x :: xs) ++ Move.tabToFound d :: tail := by
          have hh : α ++ β = α ++ ((x :: xs) ++ Move.tabToFound d :: tail) := by
            rw [h2, hδ, List.append_assoc]
          exact append_cancel_pre hh
        exact hms.2 _ (by rw [hβ]; exact List.mem_append_left _ hpullδ) ⟨c, b, rfl⟩

/-- **THE MOUNTAIN SHAPE — the named residual.**  Every minimal witness play
between saturated, differing-rung `WF` states is a mountain: it splits at a turn
`F` into a raise-free left leg and a pull-free right leg (M1), with no adjacent
pull/raise at the turn (M3).  M2 (each suit's walk is unimodal) is *proved*
from M1 in §2, so it is not a conjunct here.

This is exactly the measured shape of `Temp/Mountain_Report.md:11-17` (51 116 /
51 116 plays).  It is *not* proved: §4 reduces it to two deletion residuals
(`RaiseBeforePullShortens` for M1, `AdjacentPullRaiseShortens` for M3). -/
def MountainShape : Prop :=
  ∀ (u v : State) (ρ : List Move),
    u.WF → SSaturated u → SSaturated v →
    ShufflePlayW u ρ v →
    (∃ σ : Suit, rungAt u σ ≠ rungAt v σ) →
    (∀ ρ' : List Move, ShufflePlayW u ρ' v → ρ.length ≤ ρ'.length) →
    ∃ (F : State) (α β : List Move),
      ρ = α ++ β ∧ ShufflePlayW u α F ∧ ShufflePlayW F β v ∧
        MountainSplit α β ∧ NoAdjacentPullRaise ρ

/-- **`MountainShape` gives the turn.**  Direct projection of the residual. -/
theorem turn_of_mountainShape (h : MountainShape) {u v : State} {ρ : List Move}
    (huwf : u.WF) (hsu : SSaturated u) (hsv : SSaturated v)
    (hplay : ShufflePlayW u ρ v)
    (hdiff : ∃ σ : Suit, rungAt u σ ≠ rungAt v σ)
    (hmin : ∀ ρ' : List Move, ShufflePlayW u ρ' v → ρ.length ≤ ρ'.length) :
    ∃ (F : State) (α β : List Move),
      ρ = α ++ β ∧ ShufflePlayW u α F ∧ ShufflePlayW F β v ∧
        MountainSplit α β ∧ NoAdjacentPullRaise ρ :=
  h u v ρ huwf hsu hsv hplay hdiff hmin

/-- **THE DIP (from `MountainShape`).**  The turn is the componentwise minimum of
every suit's walk, and it lies below both endpoint rungs.  This is what makes the
dip a *function of the pair* once the turn is unique. -/
theorem dip_of_mountainShape (h : MountainShape) {u v : State} {ρ : List Move}
    (huwf : u.WF) (hsu : SSaturated u) (hsv : SSaturated v)
    (hplay : ShufflePlayW u ρ v)
    (hdiff : ∃ σ : Suit, rungAt u σ ≠ rungAt v σ)
    (hmin : ∀ ρ' : List Move, ShufflePlayW u ρ' v → ρ.length ≤ ρ'.length) :
    ∃ (F : State) (α β : List Move),
      ρ = α ++ β ∧ ShufflePlayW u α F ∧ ShufflePlayW F β v ∧
        MountainSplit α β ∧
        (∀ σ : Suit, RungMinAlong u ρ σ (rungAt F σ)) ∧
        (∀ σ : Suit, rungAt F σ ≤ rungAt u σ ∧ rungAt F σ ≤ rungAt v σ) := by
  obtain ⟨F, α, β, heq, hα, hβ, hms, -⟩ := h u v ρ huwf hsu hsv hplay hdiff hmin
  refine ⟨F, α, β, heq, hα, hβ, hms, ?_, ?_⟩
  · intro σ
    rw [heq]
    exact rungMinAlong_of_mountainSplit hα hβ hms
  · intro σ
    exact mountain_bottom_le hα hβ hms.1 hms.2

/-- **M2 for every suit (from `MountainShape`).** -/
theorem m2_of_mountainShape (h : MountainShape) {u v : State} {ρ : List Move}
    (huwf : u.WF) (hsu : SSaturated u) (hsv : SSaturated v)
    (hplay : ShufflePlayW u ρ v)
    (hdiff : ∃ σ : Suit, rungAt u σ ≠ rungAt v σ)
    (hmin : ∀ ρ' : List Move, ShufflePlayW u ρ' v → ρ.length ≤ ρ'.length) :
    ∀ σ : Suit, NoUpThenDown u ρ σ := by
  obtain ⟨F, α, β, heq, hα, hβ, hms, -⟩ := h u v ρ huwf hsu hsv hplay hdiff hmin
  intro σ
  rw [heq]
  exact noUpThenDown_of_mountainSplit hα hβ hms σ

/-- **THE ACCOUNTING IDENTITY (from `MountainShape`).**  Per suit, the bracket
count is the sum of the two drops to the dip. -/
theorem accounting_of_mountainShape (h : MountainShape) {u v : State} {ρ : List Move}
    (huwf : u.WF) (hsu : SSaturated u) (hsv : SSaturated v)
    (hplay : ShufflePlayW u ρ v)
    (hdiff : ∃ σ : Suit, rungAt u σ ≠ rungAt v σ)
    (hmin : ∀ ρ' : List Move, ShufflePlayW u ρ' v → ρ.length ≤ ρ'.length) :
    ∃ (F : State) (α β : List Move),
      ρ = α ++ β ∧ ShufflePlayW u α F ∧ ShufflePlayW F β v ∧
        MountainSplit α β ∧
        (∀ σ : Suit, pullsOf ρ σ + raisesOf ρ σ =
          (rungAt u σ - rungAt F σ) + (rungAt v σ - rungAt F σ)) := by
  obtain ⟨F, α, β, heq, hα, hβ, hms, -⟩ := h u v ρ huwf hsu hsv hplay hdiff hmin
  refine ⟨F, α, β, heq, hα, hβ, hms, ?_⟩
  intro σ
  rw [heq]
  exact accounting_of_mountainSplit hα hβ hms

/-- **THE CENSUS IDENTITY (from `MountainShape`).**  `length = ` bracket count
` + `#free`, with the bracket count the dip sum.  `Temp/Mountain_Report.md:30-36`. -/
theorem census_of_mountainShape (h : MountainShape) {u v : State} {ρ : List Move}
    (huwf : u.WF) (hsu : SSaturated u) (hsv : SSaturated v)
    (hplay : ShufflePlayW u ρ v)
    (hdiff : ∃ σ : Suit, rungAt u σ ≠ rungAt v σ)
    (hmin : ∀ ρ' : List Move, ShufflePlayW u ρ' v → ρ.length ≤ ρ'.length) :
    ∃ (F : State) (α β : List Move),
      ρ = α ++ β ∧ ShufflePlayW u α F ∧ ShufflePlayW F β v ∧
        MountainSplit α β ∧ ρ.length = bracketDip u v F + freeCount ρ := by
  obtain ⟨F, α, β, heq, hα, hβ, hms, -⟩ := h u v ρ huwf hsu hsv hplay hdiff hmin
  refine ⟨F, α, β, heq, hα, hβ, hms, ?_⟩
  rw [heq]
  exact length_eq_bracketDip_plus_free hα hβ hms

/-! ## §3b. M3: the free letter between the last pull and the first raise -/

/-- **M3 FROM M1 + NO-ADJACENT.**  If the play is a mountain (M1) and carries no
adjacent pull/raise (the `NoAdjacentPullRaise` conjunct of `MountainShape`),
then between the last pull and the first raise there is a FREE letter — provided
the middle block contains no pull and no raise (which is what "last pull" and
"first raise" mean).

This is the exact letter form of M3 (`Temp/Mountain_Report.md:16-17`). -/
theorem exists_free_between_of_noAdjacent {u v : State} {ρ : List Move}
    (hplay : ShufflePlayW u ρ v)
    (_hm1 : NoRaiseBeforePull ρ) (hm3 : NoAdjacentPullRaise ρ)
    {pre mid post : List Move} {c d : Card} {b : Base}
    (heq : ρ = pre ++ Move.foundToTab c b :: mid ++ Move.tabToFound d :: post)
    (hnpull : ∀ (c' : Card) (b' : Base), Move.foundToTab c' b' ∉ mid)
    (hnraise : ∀ e : Card, Move.tabToFound e ∉ mid) :
    ∃ m ∈ mid, FreeMove m := by
  cases mid with
  | nil =>
      exfalso
      exact hm3 ⟨pre, post, c, d, b, by simpa using heq⟩
  | cons m ms =>
      refine ⟨m, List.mem_cons_self .., ?_⟩
      have hmem : m ∈ ρ := by
        rw [heq]
        simp
      rcases free_or_pull_or_raise_of_play hplay m hmem with hf | hp | hr
      · exact hf
      · obtain ⟨c', b', rfl⟩ := hp
        exact absurd (List.mem_cons_self ..) (hnpull c' b')
      · obtain ⟨e, rfl⟩ := hr
        exact absurd (List.mem_cons_self ..) (hnraise e)

/-! ## §4. The M1 reduction: one deletion residual -/

/-- **THE M1 RESIDUAL — WITHDRAWN, FALSE AS STATED.**

A raise followed later by a pull does NOT in general make the play non-minimal.
Kernel counterexample (`Orig2/ForkMountainRefute.lean`, `CrackM1.not_raiseBeforePullShortens`):
a **7-card** board and the two-letter play

```text
raise 5H   ;   pull AD → 2S          rungs (4,1,0,0) → (5,0,0,0)
```

The rung vector moves on TWO coordinates (L1 = 2) while every witness letter
changes at most one suit's rung (`step_rung_support`), so **no shorter play
exists** — yet it is a raise followed by a later pull.  `Temp/MtnPr_Report.md`
finding (1) proves the same obstruction independently (for `c.suit ≠ d.suit` the
two-letter play is shortest and the letters commute).

WHY THE CAMPAIGN SURVIVES.  Those endpoints are **not saturated**, so the
witness is outside `SplitHyp` (which requires `SSaturated` endpoints).  Note
that `Direct.MountainAtSplits` itself carries **no** rung gate and is now
**FALSE** (`EqualRung.mountainAtSplits_false`); only the gated
`MountainGate.MountainAtSplitsDiffering` is restricted to differing rungs, and
the local non-saturated witness does not reach either form.  `SatDifferForkWF`
is untouched — but the ungated definition must NOT be used as a proof target.  The
honest mountain residual is `Relocate.SameCardRelocation` + `Relocate.SeatInert`
(same-card only, via the net-one identity `raise_pull_eq_slide`), whose missing
machine is the pull-side `PullSwaps` certificate.

Kept only so the refutation can name it. -/
def RaiseBeforePullShortens : Prop :=
  ∀ (u v : State) (ρ pre post : List Move) (c d : Card) (b : Base),
    u.WF →
    ShufflePlayW u ρ v →
    ρ = pre ++ Move.tabToFound c :: post →
    Move.foundToTab d b ∈ post →
    ∃ ρ' : List Move, ShufflePlayW u ρ' v ∧ ρ'.length < ρ.length

/-- **THE M3 RESIDUAL.**  An adjacent `pull ; raise` at the turn (with different
cards) makes the play non-minimal.  The same-card case is already kernel
(`LiveKit.pull_raise_pair_shortens`, `Orig2/Fork/Class/ForkLivePair.lean:355`), so this is
exactly the `c ≠ d` corner of M3. -/
def AdjacentPullRaiseShortens : Prop :=
  ∀ (u v : State) (ρ pre tail : List Move) (c d : Card) (b : Base),
    u.WF →
    ShufflePlayW u ρ v →
    ρ = pre ++ Move.foundToTab c b :: Move.tabToFound d :: tail →
    c ≠ d →
    ∃ ρ' : List Move, ShufflePlayW u ρ' v ∧ ρ'.length < ρ.length

/-- `RaiseBeforePullShortens` contradicts minimality. -/
theorem not_minimal_of_raiseBeforePull (h : RaiseBeforePullShortens)
    {u v : State} {ρ : List Move} (huwf : u.WF) (hplay : ShufflePlayW u ρ v)
    (hmin : ∀ ρ' : List Move, ShufflePlayW u ρ' v → ρ.length ≤ ρ'.length)
    (hbad : RaiseBeforePull ρ) : False := by
  obtain ⟨pre, post, c, d, b, heq, hmem⟩ := hbad
  obtain ⟨ρ', hρ', hlen⟩ := h u v ρ pre post c d b huwf hplay heq hmem
  have := hmin ρ' hρ'
  omega

/-- **M1 for minimal plays, from the deletion residual.** -/
theorem noRaiseBeforePull_of_minimal (h : RaiseBeforePullShortens)
    {u v : State} {ρ : List Move} (huwf : u.WF) (hplay : ShufflePlayW u ρ v)
    (hmin : ∀ ρ' : List Move, ShufflePlayW u ρ' v → ρ.length ≤ ρ'.length) :
    NoRaiseBeforePull ρ :=
  fun hbad => not_minimal_of_raiseBeforePull h huwf hplay hmin hbad

/-- **`MountainShape` IS REDUCED TO TWO DELETION RESIDUALS.**  M1 comes from
`RaiseBeforePullShortens`; M3 from `AdjacentPullRaiseShortens`.  The split itself
is then pure list bookkeeping (`split_of_noRaiseBeforePull`). -/
theorem mountainShape_of_shortens (h1 : RaiseBeforePullShortens)
    (h3 : AdjacentPullRaiseShortens) : MountainShape := by
  intro u v ρ huwf hsu hsv hplay hdiff hmin
  have hm1 : NoRaiseBeforePull ρ := noRaiseBeforePull_of_minimal h1 huwf hplay hmin
  have hm3 : NoAdjacentPullRaise ρ := by
    rintro ⟨pre, tail, c, d, b, heq⟩
    by_cases hcd : c = d
    · subst hcd
      -- the same-card pair is an identity pair: delete it
      obtain ⟨A, hpre, hrest⟩ := ShufflePlayW_split hplay pre
        (Move.foundToTab c b :: Move.tabToFound c :: tail) heq
      obtain ⟨B, _hrev, hstep, _⟩ := Bubble.walk_cons_inv hrest
      have hAwf : A.WF := SatDifferCensus.ShufflePlayW.wf_end hpre huwf
      obtain ⟨ρ', hρ', hlen⟩ := LiveKit.pull_raise_pair_shortens
        (u := u) (v := v) (ρ := pre ++ Move.foundToTab c b :: Move.tabToFound c :: tail)
        (α := pre) (β := tail) (c := c) (b := b) (A := A) (B := B)
        (by rw [← heq]; exact hplay) rfl hpre hAwf hstep
      have hle := hmin ρ' hρ'
      rw [heq] at hle
      exact absurd hle (Nat.not_le.mpr hlen)
    · obtain ⟨ρ', hρ', hlen⟩ := h3 u v ρ pre tail c d b huwf hplay heq hcd
      have hle := hmin ρ' hρ'
      exact absurd hle (Nat.not_le.mpr hlen)
  obtain ⟨α, β, heq, hms⟩ := split_of_noRaiseBeforePull hm1
  obtain ⟨F, hα, hβ⟩ := ShufflePlayW_split hplay α β heq
  exact ⟨F, α, β, heq, hα, hβ, hms, hm3⟩

/-- **§4b — the provable fragment of the M1 residual.**  A raise that is
*immediately* undone by a pull of the same card back to the same state is an
identity pair (`LiveKit.IdentityPair`) and deletes.  The missing case of
`RaiseBeforePullShortens` is therefore exactly "the pull does not return the
card to the raise's origin" (and the non-adjacent case). -/
theorem raise_pull_undo_shortens {u v : State} {ρ α β : List Move} {c : Card}
    {b : Base} {A T : State}
    (hplay : ShufflePlayW u ρ v)
    (hρ : ρ = α ++ Move.tabToFound c :: Move.foundToTab c b :: β)
    (hα : ShufflePlayW u α A)
    (h1 : State.step A (Move.tabToFound c) = some T)
    (h2 : State.step T (Move.foundToTab c b) = some A) :
    ∃ ρ' : List Move, ShufflePlayW u ρ' v ∧ ρ'.length < ρ.length :=
  LiveKit.identity_pair_delete hplay hρ hα ⟨h1, h2⟩

/-! ## §5. The joint residual with the dip-fibre fork -/

/-- **THE MISSING CONJUNCT.**  In a minimal mountain play the turn state `F` is
a fork.  `MountainShape` supplies everything else for `MinKit.MinCrossesFork`:
the prefix `α` of the split is a witness play from `u` landing at `F`, so a fork
at `F` *is* a fork on a prefix of `ρ`. -/
def DipFibreFork : Prop :=
  ∀ (u v : State) (ρ : List Move) (F : State) (α β : List Move),
    u.WF → SSaturated u → SSaturated v →
    ShufflePlayW u ρ v →
    (∃ σ : Suit, rungAt u σ ≠ rungAt v σ) →
    (∀ ρ' : List Move, ShufflePlayW u ρ' v → ρ.length ≤ ρ'.length) →
    ρ = α ++ β → ShufflePlayW u α F → ShufflePlayW F β v →
    MountainSplit α β →
    ∃ x : Card, ForkWitness F x

/-- **THE JOINT RESIDUAL IMPLIES `MinKit.MinCrossesFork`.**  `MountainShape`
gives the split and its prefix; `DipFibreFork` puts the fork at the turn. -/
theorem minCrossesFork_of_mountainShape_dip (hs : MountainShape) (hd : DipFibreFork) :
    MinKit.MinCrossesFork := by
  intro u v ρ huwf hsu hsv hplay hdiff hmin
  obtain ⟨F, α, β, heq, hα, hβ, hms, _hm3⟩ := hs u v ρ huwf hsu hsv hplay hdiff hmin
  obtain ⟨x, hx⟩ := hd u v ρ F α β huwf hsu hsv hplay hdiff hmin heq hα hβ hms
  exact ⟨F, x, α, β, heq, hα, hx⟩

/-- **THE CAMPAIGN TARGET FROM THE JOINT RESIDUAL.** -/
theorem satDifferForkWF_of_mountainShape_dip (hs : MountainShape)
    (hd : DipFibreFork) (hmin : ShortestPlayExists) : SatDifferForkWF :=
  MinKit.satDifferForkWF_of_minCrossesFork (minCrossesFork_of_mountainShape_dip hs hd) hmin

/-! ## §6. Axiom battery -/

#print axioms MountainKit.raiseBeforePull_tail
#print axioms MountainKit.split_cons_of_not_raise
#print axioms MountainKit.split_of_noRaiseBeforePull
#print axioms MountainKit.noRaiseBeforePull_of_split
#print axioms MountainKit.noRaiseBeforePull_iff_split
#print axioms MountainKit.rung_le_later_of_no_raise
#print axioms MountainKit.rung_le_later_of_no_pull
#print axioms MountainKit.noUpThenDown_of_mountainSplit
#print axioms MountainKit.last_mem_right
#print axioms MountainKit.adjacent_at_turn_of_mountainSplit
#print axioms MountainKit.exists_free_between_of_noAdjacent
#print axioms MountainKit.turn_of_mountainShape
#print axioms MountainKit.dip_of_mountainShape
#print axioms MountainKit.m2_of_mountainShape
#print axioms MountainKit.accounting_of_mountainShape
#print axioms MountainKit.census_of_mountainShape
#print axioms MountainKit.not_minimal_of_raiseBeforePull
#print axioms MountainKit.noRaiseBeforePull_of_minimal
#print axioms MountainKit.mountainShape_of_shortens
#print axioms MountainKit.raise_pull_undo_shortens
#print axioms MountainKit.minCrossesFork_of_mountainShape_dip
#print axioms MountainKit.satDifferForkWF_of_mountainShape_dip

end MountainKit
