import Orig2.TwinRelabel
import Orig2.Integrity
import Orig2.SeatMateStack

set_option linter.unusedSectionVars false

/-!
# Orig2.TwinSplice (temp) — the rider-general strict twin swap

`Card.relabelTwin` rewrites card values in place and therefore drags a
rider seated on a twin along with the relabeled value.  The correct
rider-general operation swaps the two face-up *runs* above the twins:
the run headed at `x` moves onto the prefix below `x.twin`, and vice
versa, so every rider keeps its parent card.

This file defines `State.spliceTwinRuns`, proves the three seat
equations, and derives the strict bridge
`twinPairSwapStrict_splice`.  Zero `sorry`, zero `Classical.choice`.

WF NOTE: the seat equations carry `st.WF`.  Without occurrence
uniqueness the equations are FALSE: with duplicate copies of `x` in
the twin's pile, the holding search can still answer the old anchor
and the exchanged run reads the wrong parent.  `WF` supplies exactly
the uniqueness used by the holding and `below` computations.
-/

namespace State

/-- **`State.spliceTwinRuns x st`** — swap the face-up runs above the
two twins.  In the both-held case with `pileHolding x = some a` and
`pileHolding x.twin = some b` (and `a ≠ b`), pile `a` keeps its hidden
deck and receives `below x faceUpA ++ fromCard x.twin faceUpB`, while
pile `b` receives `below x.twin faceUpB ++ fromCard x faceUpA`.  If
either twin is not held face up, or both are held by the same pile,
the state is returned unchanged. -/
def spliceTwinRuns (x : Card) (st : State) : State :=
  match st.pileHolding x, st.pileHolding x.twin with
  | some a, some b =>
      if a = b then st
      else
        { st with
          piles := fun a' =>
            if a' = a then
              { hidden := (st.piles a).hidden
                faceUp := below x (st.piles a).faceUp ++
                  fromCard x.twin (st.piles b).faceUp }
            else if a' = b then
              { hidden := (st.piles b).hidden
                faceUp := below x.twin (st.piles b).faceUp ++
                  fromCard x (st.piles a).faceUp }
            else st.piles a' }
  | _, _ => st

variable {st : State} {x : Card} {a b : Anchor}

theorem spliceTwinRuns_of_none_left
    (ha : st.pileHolding x = none) :
    st.spliceTwinRuns x = st := by
  unfold State.spliceTwinRuns
  rw [ha]

theorem spliceTwinRuns_of_none_right
    (hb : st.pileHolding x.twin = none) :
    st.spliceTwinRuns x = st := by
  unfold State.spliceTwinRuns
  cases hh : st.pileHolding x with
  | none => rfl
  | some c =>
      rw [hb]

theorem spliceTwinRuns_of_eq
    (ha : st.pileHolding x = some a) (hb : st.pileHolding x.twin = some a) :
    st.spliceTwinRuns x = st := by
  simp [State.spliceTwinRuns, ha, hb]

theorem spliceTwinRuns_piles_self
    (ha : st.pileHolding x = some a) (hb : st.pileHolding x.twin = some b)
    (hab : a ≠ b) :
    (st.spliceTwinRuns x).piles a =
      { hidden := (st.piles a).hidden
        faceUp := below x (st.piles a).faceUp ++
          fromCard x.twin (st.piles b).faceUp } := by
  simp [State.spliceTwinRuns, ha, hb, hab]

theorem spliceTwinRuns_piles_other
    (ha : st.pileHolding x = some a) (hb : st.pileHolding x.twin = some b)
    (hab : a ≠ b) {a' : Anchor} (h₁ : a' ≠ a) (h₂ : a' ≠ b) :
    (st.spliceTwinRuns x).piles a' = st.piles a' := by
  simp [State.spliceTwinRuns, ha, hb, hab, h₁, h₂]

theorem spliceTwinRuns_piles_second
    (ha : st.pileHolding x = some a) (hb : st.pileHolding x.twin = some b)
    (hab : a ≠ b) :
    (st.spliceTwinRuns x).piles b =
      { hidden := (st.piles b).hidden
        faceUp := below x.twin (st.piles b).faceUp ++
          fromCard x (st.piles a).faceUp } := by
  simp [State.spliceTwinRuns, ha, hb, hab, Ne.symm hab]

theorem spliceTwinRuns_found
    (ha : st.pileHolding x = some a) (hb : st.pileHolding x.twin = some b)
    (hab : a ≠ b) :
    (st.spliceTwinRuns x).found = st.found := by
  simp [State.spliceTwinRuns, ha, hb, hab]

theorem spliceTwinRuns_stock
    (ha : st.pileHolding x = some a) (hb : st.pileHolding x.twin = some b)
    (hab : a ≠ b) :
    (st.spliceTwinRuns x).stock = st.stock := by
  simp [State.spliceTwinRuns, ha, hb, hab]

theorem spliceTwinRuns_waste
    (ha : st.pileHolding x = some a) (hb : st.pileHolding x.twin = some b)
    (hab : a ≠ b) :
    (st.spliceTwinRuns x).waste = st.waste := by
  simp [State.spliceTwinRuns, ha, hb, hab]

theorem spliceTwinRuns_drawStep
    (ha : st.pileHolding x = some a) (hb : st.pileHolding x.twin = some b)
    (hab : a ≠ b) :
    (st.spliceTwinRuns x).drawStep = st.drawStep := by
  simp [State.spliceTwinRuns, ha, hb, hab]
end State

open State

/-! ## §1. List facts for the run swap -/

/-- The prefix strictly below a card meeting it head-on is empty. -/
private theorem below_cons_self (c : Card) (t : List Card) :
    below c (c :: t) = [] := by
  rw [below_cons, ite_eq_left rfl]

/-- A legal run's `below` part and `fromCard` part are disjoint: a card
in both would be strictly below itself by the run descent. -/
private theorem run_split_disjoint {l : List Card} (hok : runOK l = true)
    {c y : Card} (hyP : y ∈ below c l) (hyR : y ∈ fromCard c l) : False := by
  have hrun : runOK (below c l ++ fromCard c l) = true := by
    rw [tfc_below_fromCard c l]
    exact hok
  have hlt := runOK_desc hrun hyP hyR
  omega

/-- A card in the `fromCard` run of a non-head member sits strictly
above the run's head: the `below` part of the run is nonempty. -/
private theorem below_fromCard_ne_nil {l : List Card} {c y : Card}
    (hhead : ∃ r, fromCard c l = c :: r) (hy : y ∈ fromCard c l) (hyc : y ≠ c) :
    below y (fromCard c l) ≠ [] := by
  obtain ⟨r, hr⟩ := hhead
  rw [hr] at hy ⊢
  have hyr : y ∈ r := by
    rcases List.mem_cons.mp hy with h | h
    · exact absurd h hyc
    · exact h
  rw [below_cons, ite_eq_right (fun hcy => hyc hcy.symm)]
  exact List.cons_ne_nil _ _

/-- `getLast?` of an append with a nonempty right summand is the right
summand's `getLast?`. -/
private theorem getLast?_append_right {A R : List Card} (hR : R ≠ []) :
    List.getLast? (A ++ R) = List.getLast? R := by
  rw [tfc_getLast?_lastOf, tfc_getLast?_lastOf, tfc_lastOf_append_ne A hR]

/-- A nonempty list's `getLast?` is not `none`. -/
private theorem getLast?_ne_none_of_ne_nil {l : List Card} (h : l ≠ []) :
    List.getLast? l ≠ none := by
  intro hc
  rw [tfc_getLast?_lastOf] at hc
  cases l with
  | nil => exact h rfl
  | cons x t => exact tfc_lastOf_cons_ne t x hc

/-! ## §2. The seat equations -/

/-- **`seatOf_splice_self`** — after the splice, `x` sits exactly
where `x.twin` sat.  (The `WF` hypothesis supplies occurrence
uniqueness; see the file header.) -/
theorem seatOf_splice_self {st : State} {x : Card} {a b : Anchor}
    (hwf : st.WF)
    (ha : st.pileHolding x = some a) (hb : st.pileHolding x.twin = some b)
    (hab : a ≠ b) :
    seatOf (st.spliceTwinRuns x) x = seatOf st x.twin := by
  have hxmem : x ∈ (st.piles a).faceUp := pileHolding_mem ha
  have hxB : x ∉ (st.piles b).faceUp :=
    (mem_faceUp_unique hwf hxmem b (Ne.symm hab)).1
  obtain ⟨rA, hrunA⟩ := tfc_fromCard_cons_head (c := x) _ hxmem
  have hxpreB : x ∉ below x.twin (st.piles b).faceUp :=
    fun h => hxB (mem_below _ h)
  have hnew : (st.spliceTwinRuns x).pileHolding x = some b := by
    refine tfc_pileHolding_pin ?_ ?_
    · rw [spliceTwinRuns_piles_second ha hb hab]
      exact List.mem_append.mpr
        (Or.inr (by rw [hrunA]; exact List.mem_cons_self))
    · intro j hj
      by_cases hja : j = a
      · subst hja
        rw [spliceTwinRuns_piles_self ha hb hab]
        intro hm
        rcases List.mem_append.mp hm with hpre | hrun
        · exact tfc_below_not_mem_self x _ hpre
        · exact hxB (tfc_mem_fromCard _ hrun)
      · rw [spliceTwinRuns_piles_other ha hb hab hja hj]
        exact (mem_faceUp_unique hwf hxmem j hja).1
  rw [tfc_seatOf_pair hnew, tfc_seatOf_pair hb]
  have hbelow_new : below x ((st.spliceTwinRuns x).piles b).faceUp =
      below x.twin (st.piles b).faceUp := by
    rw [spliceTwinRuns_piles_second ha hb hab]
    rw [(tfc_below_fromCard_excl x (below x.twin (st.piles b).faceUp)
      (fromCard x (st.piles a).faceUp) hxpreB).1]
    rw [hrunA, below_cons_self, List.append_nil]
  rw [hbelow_new]

/-- **`seatOf_splice_twin`** — after the splice, `x.twin` sits exactly
where `x` sat. -/
theorem seatOf_splice_twin {st : State} {x : Card} {a b : Anchor}
    (hwf : st.WF)
    (ha : st.pileHolding x = some a) (hb : st.pileHolding x.twin = some b)
    (hab : a ≠ b) :
    seatOf (st.spliceTwinRuns x) x.twin = seatOf st x := by
  have htmem : x.twin ∈ (st.piles b).faceUp := pileHolding_mem hb
  have htA : x.twin ∉ (st.piles a).faceUp :=
    (mem_faceUp_unique hwf htmem a hab).1
  obtain ⟨rB, hrunB⟩ := tfc_fromCard_cons_head (c := x.twin) _ htmem
  have htpreA : x.twin ∉ below x (st.piles a).faceUp :=
    fun h => htA (mem_below _ h)
  have hnew : (st.spliceTwinRuns x).pileHolding x.twin = some a := by
    refine tfc_pileHolding_pin ?_ ?_
    · rw [spliceTwinRuns_piles_self ha hb hab]
      exact List.mem_append.mpr
        (Or.inr (by rw [hrunB]; exact List.mem_cons_self))
    · intro j hj
      by_cases hjb : j = b
      · subst hjb
        rw [spliceTwinRuns_piles_second ha hb hab]
        intro hm
        rcases List.mem_append.mp hm with hpre | hrun
        · exact tfc_below_not_mem_self x.twin _ hpre
        · exact htA (tfc_mem_fromCard _ hrun)
      · rw [spliceTwinRuns_piles_other ha hb hab hj hjb]
        exact (mem_faceUp_unique hwf htmem j hjb).1
  rw [tfc_seatOf_pair hnew, tfc_seatOf_pair ha]
  have hbelow_new : below x.twin ((st.spliceTwinRuns x).piles a).faceUp =
      below x (st.piles a).faceUp := by
    rw [spliceTwinRuns_piles_self ha hb hab]
    rw [(tfc_below_fromCard_excl x.twin (below x (st.piles a).faceUp)
      (fromCard x.twin (st.piles b).faceUp) htpreA).1]
    rw [hrunB, below_cons_self, List.append_nil]
  rw [hbelow_new]

/-! ## §3. Holding and seat kit for the run swap -/

section SpliceKit

variable {st : State} {x : Card} {a b : Anchor}
variable (hwf : st.WF)
variable (ha : st.pileHolding x = some a) (hb : st.pileHolding x.twin = some b)
variable (hab : a ≠ b)

include hwf ha hb hab

/-- The new `a`-pile's face-up run lies in the union of the two old runs. -/
private theorem mem_faceUp_of_mem_new_a {y : Card}
    (hy : y ∈ ((st.spliceTwinRuns x).piles a).faceUp) :
    y ∈ (st.piles a).faceUp ∨ y ∈ (st.piles b).faceUp := by
  rw [spliceTwinRuns_piles_self ha hb hab] at hy
  rcases List.mem_append.mp hy with h | h
  · exact Or.inl (mem_below _ h)
  · exact Or.inr (tfc_mem_fromCard _ h)

/-- The new `b`-pile's face-up run lies in the union of the two old runs. -/
private theorem mem_faceUp_of_mem_new_b {y : Card}
    (hy : y ∈ ((st.spliceTwinRuns x).piles b).faceUp) :
    y ∈ (st.piles a).faceUp ∨ y ∈ (st.piles b).faceUp := by
  rw [spliceTwinRuns_piles_second ha hb hab] at hy
  rcases List.mem_append.mp hy with h | h
  · exact Or.inr (mem_below _ h)
  · exact Or.inl (tfc_mem_fromCard _ h)

/-! ### The player positions -/

/-- A non-head member of `runA` lands in pile `b` after the splice. -/
private theorem hold_runA {y : Card}
    (hyRA : y ∈ fromCard x (st.piles a).faceUp) :
    (st.spliceTwinRuns x).pileHolding y = some b := by
  have hxmem : x ∈ (st.piles a).faceUp := pileHolding_mem ha
  have hxA : y ∈ (st.piles a).faceUp := tfc_mem_fromCard _ hyRA
  have hyB : y ∉ (st.piles b).faceUp :=
    (mem_faceUp_unique hwf hxA b (Ne.symm hab)).1
  have hy_not_preA : y ∉ below x (st.piles a).faceUp :=
    fun h => run_split_disjoint (hwf.runOK_of a) h hyRA
  have hy_not_preB : y ∉ below x.twin (st.piles b).faceUp :=
    fun h => hyB (mem_below _ h)
  refine tfc_pileHolding_pin ?_ ?_
  · rw [spliceTwinRuns_piles_second ha hb hab]
    exact List.mem_append.mpr (Or.inr hyRA)
  · intro j hj
    by_cases hja : j = a
    · subst hja
      rw [spliceTwinRuns_piles_self ha hb hab]
      intro hm
      rcases List.mem_append.mp hm with h | h
      · exact hy_not_preA h
      · exact hyB (tfc_mem_fromCard _ h)
    · rw [spliceTwinRuns_piles_other ha hb hab hja hj]
      exact (mem_faceUp_unique hwf hxA j hja).1

/-- A non-head member of `runB` lands in pile `a` after the splice. -/
private theorem hold_runB {y : Card}
    (hyRB : y ∈ fromCard x.twin (st.piles b).faceUp) :
    (st.spliceTwinRuns x).pileHolding y = some a := by
  have htmem : x.twin ∈ (st.piles b).faceUp := pileHolding_mem hb
  have hxB : y ∈ (st.piles b).faceUp := tfc_mem_fromCard _ hyRB
  have hyA : y ∉ (st.piles a).faceUp :=
    (mem_faceUp_unique hwf hxB a hab).1
  have hy_not_preB : y ∉ below x.twin (st.piles b).faceUp :=
    fun h => run_split_disjoint (hwf.runOK_of b) h hyRB
  have hy_not_preA : y ∉ below x (st.piles a).faceUp :=
    fun h => hyA (mem_below _ h)
  refine tfc_pileHolding_pin ?_ ?_
  · rw [spliceTwinRuns_piles_self ha hb hab]
    exact List.mem_append.mpr (Or.inr hyRB)
  · intro j hj
    by_cases hjb : j = b
    · subst hjb
      rw [spliceTwinRuns_piles_second ha hb hab]
      intro hm
      rcases List.mem_append.mp hm with h | h
      · exact hy_not_preB h
      · exact hyA (tfc_mem_fromCard _ h)
    · rw [spliceTwinRuns_piles_other ha hb hab hj hjb]
      exact (mem_faceUp_unique hwf hxB j hjb).1

/-- A member of `preA` stays in pile `a`. -/
private theorem hold_preA {y : Card} (hy : y ∈ below x (st.piles a).faceUp) :
    (st.spliceTwinRuns x).pileHolding y = some a := by
  have hxA : y ∈ (st.piles a).faceUp := mem_below _ hy
  have hyB : y ∉ (st.piles b).faceUp :=
    (mem_faceUp_unique hwf hxA b (Ne.symm hab)).1
  have hy_not_runA : y ∉ fromCard x (st.piles a).faceUp :=
    fun h => run_split_disjoint (hwf.runOK_of a) hy h
  refine tfc_pileHolding_pin ?_ ?_
  · rw [spliceTwinRuns_piles_self ha hb hab]
    exact List.mem_append.mpr (Or.inl hy)
  · intro j hj
    by_cases hjb : j = b
    · subst hjb
      rw [spliceTwinRuns_piles_second ha hb hab]
      intro hm
      rcases List.mem_append.mp hm with h | h
      · exact hyB (mem_below _ h)
      · exact hy_not_runA h
    · rw [spliceTwinRuns_piles_other ha hb hab hj hjb]
      exact (mem_faceUp_unique hwf hxA j hj).1

/-- A member of `preB` stays in pile `b`. -/
private theorem hold_preB {y : Card} (hy : y ∈ below x.twin (st.piles b).faceUp) :
    (st.spliceTwinRuns x).pileHolding y = some b := by
  have hxB : y ∈ (st.piles b).faceUp := mem_below _ hy
  have hyA : y ∉ (st.piles a).faceUp :=
    (mem_faceUp_unique hwf hxB a hab).1
  have hy_not_runB : y ∉ fromCard x.twin (st.piles b).faceUp :=
    fun h => run_split_disjoint (hwf.runOK_of b) hy h
  refine tfc_pileHolding_pin ?_ ?_
  · rw [spliceTwinRuns_piles_second ha hb hab]
    exact List.mem_append.mpr (Or.inl hy)
  · intro j hj
    by_cases hja : j = a
    · subst hja
      rw [spliceTwinRuns_piles_self ha hb hab]
      intro hm
      rcases List.mem_append.mp hm with h | h
      · exact hyA (mem_below _ h)
      · exact hy_not_runB h
    · rw [spliceTwinRuns_piles_other ha hb hab hja hj]
      exact (mem_faceUp_unique hwf hxB j hj).1

/-- A card held by a third pile keeps its holding. -/
private theorem hold_other {y : Card} {c : Anchor} (hph : st.pileHolding y = some c)
    (hca : c ≠ a) (hcb : c ≠ b) :
    (st.spliceTwinRuns x).pileHolding y = some c := by
  have hymem : y ∈ (st.piles c).faceUp := pileHolding_mem hph
  have hyA : y ∉ (st.piles a).faceUp :=
    (mem_faceUp_unique hwf hymem a (Ne.symm hca)).1
  have hyB : y ∉ (st.piles b).faceUp :=
    (mem_faceUp_unique hwf hymem b (Ne.symm hcb)).1
  refine tfc_pileHolding_pin ?_ ?_
  · rw [spliceTwinRuns_piles_other ha hb hab hca hcb]
    exact hymem
  · intro j hj
    by_cases hja : j = a
    · subst hja
      rw [spliceTwinRuns_piles_self ha hb hab]
      intro hm
      rcases List.mem_append.mp hm with h | h
      · exact hyA (mem_below _ h)
      · exact hyB (tfc_mem_fromCard _ h)
    · by_cases hjb : j = b
      · subst hjb
        rw [spliceTwinRuns_piles_second ha hb hab]
        intro hm
        rcases List.mem_append.mp hm with h | h
        · exact hyB (mem_below _ h)
        · exact hyA (tfc_mem_fromCard _ h)
      · rw [spliceTwinRuns_piles_other ha hb hab hja hjb]
        exact (mem_faceUp_unique hwf hymem j hj).1

/-- An unheld card stays unheld. -/
private theorem hold_none {y : Card} (hnone : st.pileHolding y = none) :
    (st.spliceTwinRuns x).pileHolding y = none := by
  have hno : ∀ j, y ∉ (st.piles j).faceUp :=
    fun j => tfc_not_mem_faceUp_of_holdNone hnone j
  refine tfc_pileHolding_none ?_
  intro j
  by_cases hja : j = a
  · rw [hja]
    rw [spliceTwinRuns_piles_self ha hb hab]
    intro hm
    rcases List.mem_append.mp hm with h | h
    · exact hno a (mem_below _ h)
    · exact hno b (tfc_mem_fromCard _ h)
  · by_cases hjb : j = b
    · rw [hjb]
      rw [spliceTwinRuns_piles_second ha hb hab]
      intro hm
      rcases List.mem_append.mp hm with h | h
      · exact hno b (mem_below _ h)
      · exact hno a (tfc_mem_fromCard _ h)
    · rw [spliceTwinRuns_piles_other ha hb hab hja hjb]
      exact hno j

/-! ### The matching seat rows -/

private theorem seat_runA {y : Card}
    (hyRA : y ∈ fromCard x (st.piles a).faceUp) (hyx : y ≠ x) :
    seatOf (st.spliceTwinRuns x) y = seatOf st y := by
  have hxmem : x ∈ (st.piles a).faceUp := pileHolding_mem ha
  have hxA : y ∈ (st.piles a).faceUp := tfc_mem_fromCard _ hyRA
  have hyB : y ∉ (st.piles b).faceUp :=
    (mem_faceUp_unique hwf hxA b (Ne.symm hab)).1
  have hy_not_preA : y ∉ below x (st.piles a).faceUp :=
    fun h => run_split_disjoint (hwf.runOK_of a) h hyRA
  have hy_not_preB : y ∉ below x.twin (st.piles b).faceUp :=
    fun h => hyB (mem_below _ h)
  obtain ⟨r, hrunA⟩ := tfc_fromCard_cons_head (c := x) _ hxmem
  have hnew := hold_runA hwf ha hb hab hyRA
  have hold : st.pileHolding y = some a := (pileHolding_eq_some_iff hwf).2 hxA
  rw [tfc_seatOf_pair hnew, tfc_seatOf_pair hold]
  have hbelow_new : below y ((st.spliceTwinRuns x).piles b).faceUp =
      below x.twin (st.piles b).faceUp ++
        below y (fromCard x (st.piles a).faceUp) := by
    rw [spliceTwinRuns_piles_second ha hb hab]
    exact (tfc_below_fromCard_excl y (below x.twin (st.piles b).faceUp)
      (fromCard x (st.piles a).faceUp) hy_not_preB).1
  have hbelow_old : below y (st.piles a).faceUp =
      below x (st.piles a).faceUp ++
        below y (fromCard x (st.piles a).faceUp) := by
    conv =>
      lhs
      rw [← tfc_below_fromCard x (st.piles a).faceUp]
    exact (tfc_below_fromCard_excl y (below x (st.piles a).faceUp)
      (fromCard x (st.piles a).faceUp) hy_not_preA).1
  have hnonempty : below y (fromCard x (st.piles a).faceUp) ≠ [] :=
    below_fromCard_ne_nil ⟨r, hrunA⟩ hyRA hyx
  rw [hbelow_new, hbelow_old]
  simp only [getLast?_append_right hnonempty]
  have hne := getLast?_ne_none_of_ne_nil hnonempty
  cases hgl : List.getLast? (below y (fromCard x (st.piles a).faceUp)) with
  | none => exact absurd hgl hne
  | some z => rfl

private theorem seat_runB {y : Card}
    (hyRB : y ∈ fromCard x.twin (st.piles b).faceUp) (hyt : y ≠ x.twin) :
    seatOf (st.spliceTwinRuns x) y = seatOf st y := by
  have htmem : x.twin ∈ (st.piles b).faceUp := pileHolding_mem hb
  have hxB : y ∈ (st.piles b).faceUp := tfc_mem_fromCard _ hyRB
  have hyA : y ∉ (st.piles a).faceUp :=
    (mem_faceUp_unique hwf hxB a hab).1
  have hy_not_preB : y ∉ below x.twin (st.piles b).faceUp :=
    fun h => run_split_disjoint (hwf.runOK_of b) h hyRB
  have hy_not_preA : y ∉ below x (st.piles a).faceUp :=
    fun h => hyA (mem_below _ h)
  obtain ⟨r, hrunB⟩ := tfc_fromCard_cons_head (c := x.twin) _ htmem
  have hnew := hold_runB hwf ha hb hab hyRB
  have hold : st.pileHolding y = some b := (pileHolding_eq_some_iff hwf).2 hxB
  rw [tfc_seatOf_pair hnew, tfc_seatOf_pair hold]
  have hbelow_new : below y ((st.spliceTwinRuns x).piles a).faceUp =
      below x (st.piles a).faceUp ++
        below y (fromCard x.twin (st.piles b).faceUp) := by
    rw [spliceTwinRuns_piles_self ha hb hab]
    exact (tfc_below_fromCard_excl y (below x (st.piles a).faceUp)
      (fromCard x.twin (st.piles b).faceUp) hy_not_preA).1
  have hbelow_old : below y (st.piles b).faceUp =
      below x.twin (st.piles b).faceUp ++
        below y (fromCard x.twin (st.piles b).faceUp) := by
    conv =>
      lhs
      rw [← tfc_below_fromCard x.twin (st.piles b).faceUp]
    exact (tfc_below_fromCard_excl y (below x.twin (st.piles b).faceUp)
      (fromCard x.twin (st.piles b).faceUp) hy_not_preB).1
  have hnonempty : below y (fromCard x.twin (st.piles b).faceUp) ≠ [] :=
    below_fromCard_ne_nil ⟨r, hrunB⟩ hyRB hyt
  rw [hbelow_new, hbelow_old]
  simp only [getLast?_append_right hnonempty]
  have hne := getLast?_ne_none_of_ne_nil hnonempty
  cases hgl : List.getLast? (below y (fromCard x.twin (st.piles b).faceUp)) with
  | none => exact absurd hgl hne
  | some z => rfl

private theorem seat_preA {y : Card} (hy : y ∈ below x (st.piles a).faceUp) :
    seatOf (st.spliceTwinRuns x) y = seatOf st y := by
  have hxA : y ∈ (st.piles a).faceUp := mem_below _ hy
  have hnew := hold_preA hwf ha hb hab hy
  have hold : st.pileHolding y = some a := (pileHolding_eq_some_iff hwf).2 hxA
  rw [tfc_seatOf_pair hnew, tfc_seatOf_pair hold]
  have hbelow_new : below y ((st.spliceTwinRuns x).piles a).faceUp =
      below y (below x (st.piles a).faceUp) := by
    rw [spliceTwinRuns_piles_self ha hb hab]
    exact tfc_below_mem_append_left _ _ hy
  have hbelow_old : below y (st.piles a).faceUp =
      below y (below x (st.piles a).faceUp) := by
    conv =>
      lhs
      rw [← tfc_below_fromCard x (st.piles a).faceUp]
    exact tfc_below_mem_append_left _ _ hy
  rw [hbelow_new, hbelow_old]

private theorem seat_preB {y : Card} (hy : y ∈ below x.twin (st.piles b).faceUp) :
    seatOf (st.spliceTwinRuns x) y = seatOf st y := by
  have hxB : y ∈ (st.piles b).faceUp := mem_below _ hy
  have hnew := hold_preB hwf ha hb hab hy
  have hold : st.pileHolding y = some b := (pileHolding_eq_some_iff hwf).2 hxB
  rw [tfc_seatOf_pair hnew, tfc_seatOf_pair hold]
  have hbelow_new : below y ((st.spliceTwinRuns x).piles b).faceUp =
      below y (below x.twin (st.piles b).faceUp) := by
    rw [spliceTwinRuns_piles_second ha hb hab]
    exact tfc_below_mem_append_left _ _ hy
  have hbelow_old : below y (st.piles b).faceUp =
      below y (below x.twin (st.piles b).faceUp) := by
    conv =>
      lhs
      rw [← tfc_below_fromCard x.twin (st.piles b).faceUp]
    exact tfc_below_mem_append_left _ _ hy
  rw [hbelow_new, hbelow_old]

private theorem seat_other_hold {y : Card} {c : Anchor} (hph : st.pileHolding y = some c)
    (hca : c ≠ a) (hcb : c ≠ b) :
    seatOf (st.spliceTwinRuns x) y = seatOf st y := by
  have hnew := hold_other hwf ha hb hab hph hca hcb
  rw [tfc_seatOf_pair hnew, tfc_seatOf_pair hph]
  rw [spliceTwinRuns_piles_other ha hb hab hca hcb]

private theorem seat_none {y : Card} (hnone : st.pileHolding y = none) :
    seatOf (st.spliceTwinRuns x) y = seatOf st y := by
  rw [tfc_seatOf_none (hold_none hwf ha hb hab hnone), tfc_seatOf_none hnone]

end SpliceKit

/-- **`seatOf_splice_other`** — the splice fixes every seat off the
twin pair.  (A `WF` hypothesis is load-bearing: without occurrence
uniqueness a duplicate can change the reading.) -/
theorem seatOf_splice_other {st : State} {x y : Card}
    (hwf : st.WF) (hyx : y ≠ x) (hyt : y ≠ x.twin) :
    seatOf (st.spliceTwinRuns x) y = seatOf st y := by
  cases ha : st.pileHolding x with
  | none => rw [spliceTwinRuns_of_none_left ha]
  | some a =>
      cases hb : st.pileHolding x.twin with
      | none => rw [spliceTwinRuns_of_none_right hb]
      | some b =>
          by_cases hab : a = b
          · subst hab
            rw [spliceTwinRuns_of_eq ha hb]
          · cases hy : st.pileHolding y with
            | none => exact seat_none hwf ha hb hab hy
            | some c =>
                by_cases hca : c = a
                · rw [hca] at hy
                  have hymem : y ∈ (st.piles a).faceUp := pileHolding_mem hy
                  have hsplit : y ∈ below x (st.piles a).faceUp ∨
                      y ∈ fromCard x (st.piles a).faceUp := by
                    have h : y ∈ below x (st.piles a).faceUp ++
                        fromCard x (st.piles a).faceUp := by
                      rw [tfc_below_fromCard x (st.piles a).faceUp]
                      exact hymem
                    exact List.mem_append.mp h
                  rcases hsplit with hpre | hrun
                  · exact seat_preA hwf ha hb hab hpre
                  · exact seat_runA hwf ha hb hab hrun hyx
                · by_cases hcb : c = b
                  · rw [hcb] at hy
                    have hymem : y ∈ (st.piles b).faceUp := pileHolding_mem hy
                    have hsplit : y ∈ below x.twin (st.piles b).faceUp ∨
                        y ∈ fromCard x.twin (st.piles b).faceUp := by
                      have h : y ∈ below x.twin (st.piles b).faceUp ++
                          fromCard x.twin (st.piles b).faceUp := by
                        rw [tfc_below_fromCard x.twin (st.piles b).faceUp]
                        exact hymem
                      exact List.mem_append.mp h
                    rcases hsplit with hpre | hrun
                    · exact seat_preB hwf ha hb hab hpre
                    · exact seat_runB hwf ha hb hab hrun hyt
                  · exact seat_other_hold hwf ha hb hab hy hca hcb


/-! ## §4. The strict bridge -/

/-- Two cards of equal rank cannot occupy different positions of a legal
run: ranks strictly descend along it. -/
private theorem runOK_rank_distinct {l : List Card} (hok : runOK l = true)
    {u v : Card} (hu : u ∈ l) (hv : v ∈ l) (hr : u.rank = v.rank) : u = v := by
  induction l with
  | nil => cases hu
  | cons a t ih =>
      cases t with
      | nil =>
          rw [List.mem_singleton] at hu hv
          rw [hu, hv]
      | cons b t' =>
          have hok' : runOK (b :: t') = true := runOK_cons_tail hok
          rcases List.mem_cons.mp hu with rfl | hu'
          · rcases List.mem_cons.mp hv with rfl | hv'
            · rfl
            · have hlt := runOK_head_gt hok hv'
              have hidx : u.rank.toIdx = v.rank.toIdx := congrArg Rank.toIdx hr
              omega
          · rcases List.mem_cons.mp hv with rfl | hv'
            · have hlt := runOK_head_gt hok hu'
              have hidx : u.rank.toIdx = v.rank.toIdx := congrArg Rank.toIdx hr
              omega
            · exact ih hok' hu' hv'

/-- **`twinPairSwapStrict_splice`** — when both twins sit on parents
(the `.inr` seats, with the second parent the twin of the first), the
run splice realizes the exact strict twin swap: the pair's seats are
exchanged, every other seat is fixed, and the hidden decks,
foundations, stock, waste, and cut are untouched. -/
theorem twinPairSwapStrict_splice {st : State} {x : Card} (hwf : st.WF)
    (hx : ∃ z, seatOf st x = some (Sum.inr z))
    (hxt : ∃ z : Card, seatOf st x.twin = some (Sum.inr z.twin)) :
    twinPairSwapStrict st (st.spliceTwinRuns x) x := by
  obtain ⟨z, hzse⟩ := hx
  obtain ⟨a, ha, -, -⟩ := tfc_seatOf_of_inr hzse
  obtain ⟨w, hwse⟩ := hxt
  obtain ⟨b, hb, -, -⟩ := tfc_seatOf_of_inr hwse
  have hab : a ≠ b := by
    intro hab
    subst hab
    have htmem : x.twin ∈ (st.piles a).faceUp := pileHolding_mem hb
    have heq : x = x.twin :=
      runOK_rank_distinct (hwf.runOK_of a) (pileHolding_mem ha) htmem rfl
    exact card_twin_ne x heq.symm
  refine ⟨seatOf_splice_self hwf ha hb hab,
    seatOf_splice_twin hwf ha hb hab, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro y hyx hyt
    exact seatOf_splice_other hwf hyx hyt
  · refine ⟨?_, ?_⟩
    · intro a'
      by_cases h₁ : a' = a
      · subst h₁
        rw [spliceTwinRuns_piles_self ha hb hab]
      · by_cases h₂ : a' = b
        · subst h₂
          rw [spliceTwinRuns_piles_second ha hb hab]
        · rw [spliceTwinRuns_piles_other ha hb hab h₁ h₂]
    · exact (spliceTwinRuns_drawStep ha hb hab).symm
  · unfold foundsFixed
    intro s
    rw [spliceTwinRuns_found ha hb hab]
  · exact (spliceTwinRuns_stock ha hb hab).symm
  · exact (spliceTwinRuns_waste ha hb hab).symm
  · unfold cutOf
    rw [spliceTwinRuns_stock ha hb hab]

/-! ## §5. Audit battery -/

#print axioms seatOf_splice_self
#print axioms seatOf_splice_twin
#print axioms seatOf_splice_other
#print axioms twinPairSwapStrict_splice
