import Orig2.TwinFunctor
import Orig2.TwinSpliceWF

set_option linter.unusedSectionVars false

/-!
# Temp/TwinPointFunctor — the object-level point-swap functor

Both twins seated on card parents (`.inr` seats).  The run splice is an
involution on this subtype, so the point-swap is an object-level
involution of the twin tableau groupoid.

Zero `sorry`, zero `Classical.choice`.
-/

open State

/-- Both twins on card parents: `x` sits on some card and `x.twin` sits
on a card of twin shape. -/
def TwinObjInr (x : Card) : Type :=
  {s : State // s.WF ∧ (∃ z : Card, seatOf s x = some (Sum.inr z)) ∧
    (∃ z : Card, seatOf s x.twin = some (Sum.inr z.twin))}

/-- The object map: swap the two face-up runs rooted at the twins. -/
def pointObjFlip (x : Card) : TwinObjInr x → TwinObjInr x := fun s =>
  ⟨s.1.spliceTwinRuns x, by
    have hstrict := twinPairSwapStrict_splice s.2.1 s.2.2.1 s.2.2.2
    refine ⟨wf_spliceTwinRuns s.2.1 s.2.2.1 s.2.2.2, ?_, ?_⟩
    · obtain ⟨z, hz⟩ := s.2.2.2
      exact ⟨z.twin, by rw [hstrict.1, hz]⟩
    · obtain ⟨z, hz⟩ := s.2.2.1
      exact ⟨z.twin, by rw [hstrict.2.1, hz, card_twin_twin]⟩⟩

/-! ## §1. Holding pins after the first splice -/

private theorem holding_splice_self {st : State} {x : Card} {a b : Anchor}
    (hwf : st.WF)
    (ha : st.pileHolding x = some a) (hb : st.pileHolding x.twin = some b)
    (hab : a ≠ b) :
    (st.spliceTwinRuns x).pileHolding x = some b := by
  have hxmem : x ∈ (st.piles a).faceUp := pileHolding_mem ha
  have hxB : x ∉ (st.piles b).faceUp :=
    (mem_faceUp_unique hwf hxmem b (Ne.symm hab)).1
  obtain ⟨rA, hrunA⟩ := tfc_fromCard_cons_head (c := x) _ hxmem
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

private theorem holding_splice_twin {st : State} {x : Card} {a b : Anchor}
    (hwf : st.WF)
    (ha : st.pileHolding x = some a) (hb : st.pileHolding x.twin = some b)
    (hab : a ≠ b) :
    (st.spliceTwinRuns x).pileHolding x.twin = some a := by
  have htmem : x.twin ∈ (st.piles b).faceUp := pileHolding_mem hb
  have htA : x.twin ∉ (st.piles a).faceUp :=
    (mem_faceUp_unique hwf htmem a hab).1
  obtain ⟨rB, hrunB⟩ := tfc_fromCard_cons_head (c := x.twin) _ htmem
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

/-! ## §2. The run-splice involution -/

/-- Swapping the two runs twice restores the state. -/
theorem spliceTwinRuns_invol {s : State} {x : Card} (hwf : s.WF)
    (hx : ∃ z, seatOf s x = some (Sum.inr z))
    (hxt : ∃ z : Card, seatOf s x.twin = some (Sum.inr z.twin)) :
    (s.spliceTwinRuns x).spliceTwinRuns x = s := by
  obtain ⟨z, hz⟩ := hx
  obtain ⟨a, ha, -, -⟩ := tfc_seatOf_of_inr hz
  obtain ⟨w, hw⟩ := hxt
  obtain ⟨b, hb, -, -⟩ := tfc_seatOf_of_inr hw
  by_cases hab : a = b
  · subst hab
    rw [spliceTwinRuns_of_eq ha hb, spliceTwinRuns_of_eq ha hb]
  · have hxmem : x ∈ (s.piles a).faceUp := pileHolding_mem ha
    have htmem : x.twin ∈ (s.piles b).faceUp := pileHolding_mem hb
    have hxB : x ∉ (s.piles b).faceUp :=
      (mem_faceUp_unique hwf hxmem b (Ne.symm hab)).1
    have htA : x.twin ∉ (s.piles a).faceUp :=
      (mem_faceUp_unique hwf htmem a hab).1
    obtain ⟨rA, hrunA⟩ := tfc_fromCard_cons_head (c := x) _ hxmem
    obtain ⟨rB, hrunB⟩ := tfc_fromCard_cons_head (c := x.twin) _ htmem
    have hholdx : (s.spliceTwinRuns x).pileHolding x = some b :=
      holding_splice_self hwf ha hb hab
    have hholdt : (s.spliceTwinRuns x).pileHolding x.twin = some a :=
      holding_splice_twin hwf ha hb hab
    have hxB' : x ∉ below x.twin (s.piles b).faceUp :=
      fun h => hxB (mem_below _ h)
    have htA' : x.twin ∉ below x (s.piles a).faceUp :=
      fun h => htA (mem_below _ h)
    have hbelowA : below x (fromCard x (s.piles a).faceUp) = [] := by
      rw [hrunA, below_cons, ite_eq_left rfl]
    have hbelowB : below x.twin (fromCard x.twin (s.piles b).faceUp) = [] := by
      rw [hrunB, below_cons, ite_eq_left rfl]
    have hfromA : fromCard x (fromCard x (s.piles a).faceUp) =
        fromCard x (s.piles a).faceUp := by
      rw [hrunA, fromCard_head_eq]
    have hfromB : fromCard x.twin (fromCard x.twin (s.piles b).faceUp) =
        fromCard x.twin (s.piles b).faceUp := by
      rw [hrunB, fromCard_head_eq]
    have hbelow1 : below x (below x.twin (s.piles b).faceUp ++
        fromCard x (s.piles a).faceUp) = below x.twin (s.piles b).faceUp := by
      rw [(tfc_below_fromCard_excl x (below x.twin (s.piles b).faceUp)
        (fromCard x (s.piles a).faceUp) hxB').1, hbelowA, List.append_nil]
    have hfrom1 : fromCard x.twin (below x (s.piles a).faceUp ++
        fromCard x.twin (s.piles b).faceUp) =
        fromCard x.twin (s.piles b).faceUp := by
      rw [(tfc_below_fromCard_excl x.twin (below x (s.piles a).faceUp)
        (fromCard x.twin (s.piles b).faceUp) htA').2, hfromB]
    have hbelow2 : below x.twin (below x (s.piles a).faceUp ++
        fromCard x.twin (s.piles b).faceUp) = below x (s.piles a).faceUp := by
      rw [(tfc_below_fromCard_excl x.twin (below x (s.piles a).faceUp)
        (fromCard x.twin (s.piles b).faceUp) htA').1, hbelowB, List.append_nil]
    have hfrom2 : fromCard x (below x.twin (s.piles b).faceUp ++
        fromCard x (s.piles a).faceUp) =
        fromCard x (s.piles a).faceUp := by
      rw [(tfc_below_fromCard_excl x (below x.twin (s.piles b).faceUp)
        (fromCard x (s.piles a).faceUp) hxB').2, hfromA]
    have hfaceA : (((s.spliceTwinRuns x).spliceTwinRuns x).piles a).faceUp =
        (s.piles a).faceUp := by
      rw [spliceTwinRuns_piles_second hholdx hholdt (Ne.symm hab)]
      rw [spliceTwinRuns_piles_self ha hb hab,
        spliceTwinRuns_piles_second ha hb hab]
      simp only
      rw [hbelow2, hfrom2]
      exact tfc_below_fromCard x (s.piles a).faceUp
    have hfaceB : (((s.spliceTwinRuns x).spliceTwinRuns x).piles b).faceUp =
        (s.piles b).faceUp := by
      rw [spliceTwinRuns_piles_self hholdx hholdt (Ne.symm hab)]
      rw [spliceTwinRuns_piles_second ha hb hab,
        spliceTwinRuns_piles_self ha hb hab]
      simp only
      rw [hbelow1, hfrom1]
      exact tfc_below_fromCard x.twin (s.piles b).faceUp
    have hhiddenA : (((s.spliceTwinRuns x).spliceTwinRuns x).piles a).hidden =
        (s.piles a).hidden := by
      rw [spliceTwinRuns_piles_second hholdx hholdt (Ne.symm hab)]
      rw [spliceTwinRuns_piles_self ha hb hab]
    have hhiddenB : (((s.spliceTwinRuns x).spliceTwinRuns x).piles b).hidden =
        (s.piles b).hidden := by
      rw [spliceTwinRuns_piles_self hholdx hholdt (Ne.symm hab)]
      rw [spliceTwinRuns_piles_second ha hb hab]
    have hpiles : ((s.spliceTwinRuns x).spliceTwinRuns x).piles = s.piles := by
      funext j
      by_cases hja : j = a
      · subst hja
        exact Pile.ext hhiddenA hfaceA
      · by_cases hjb : j = b
        · subst hjb
          exact Pile.ext hhiddenB hfaceB
        · rw [spliceTwinRuns_piles_other hholdx hholdt (Ne.symm hab) hjb hja,
            spliceTwinRuns_piles_other ha hb hab hja hjb]
    apply State.ext
    · rw [spliceTwinRuns_found hholdx hholdt (Ne.symm hab),
        spliceTwinRuns_found ha hb hab]
    · exact hpiles
    · rw [spliceTwinRuns_stock hholdx hholdt (Ne.symm hab),
        spliceTwinRuns_stock ha hb hab]
    · rw [spliceTwinRuns_waste hholdx hholdt (Ne.symm hab),
        spliceTwinRuns_waste ha hb hab]
    · rw [spliceTwinRuns_drawStep hholdx hholdt (Ne.symm hab),
        spliceTwinRuns_drawStep ha hb hab]

/-! ## §3. The object involution -/

/-- The point-swap is an involution on the both-on-parents subtype. -/
theorem pointObjFlip_involutive (x : Card) (s : TwinObjInr x) :
    pointObjFlip x (pointObjFlip x s) = s := by
  apply Subtype.ext
  exact spliceTwinRuns_invol s.2.1 s.2.2.1 s.2.2.2

/-! ## §4. Audit -/

#print axioms spliceTwinRuns_invol
#print axioms pointObjFlip_involutive
