import Orig2.TwinSuffixExchange
import Orig2.TwinSplice
import Orig2.Integrity

set_option linter.unusedSectionVars false

/-!
# Orig2.TwinParentShift — the parent-shift identity

If the bottom rider above `x` is `y` and the bottom rider above
`x.twin` is `y.twin`, then crossing the full suffixes at `x` is the
same state edit as crossing the runs at `y`: the two operations agree
on both host piles and fix everything else.

Zero `sorry`, zero `Classical.choice`.
-/

open State

/-! ## List kit: cutting at the second of two consecutive members -/

private theorem below_fromCard_disjoint {l : List Card} (hok : runOK l = true)
    {c y : Card} (hyP : y ∈ below c l) (hyR : y ∈ fromCard c l) : False := by
  have hrun : runOK (below c l ++ fromCard c l) = true := by
    rw [tfc_below_fromCard c l]
    exact hok
  have hlt := runOK_desc hrun hyP hyR
  omega

/-- The `below`-prefix at a card immediately following another known
card, when nothing earlier in the prefix meets the cut. -/
private theorem below_second_cons (P R : List Card) {x y : Card}
    (hyP : y ∉ P) (hyx : y ≠ x) :
    below y (P ++ x :: y :: R) = P ++ [x] := by
  rw [(tfc_below_fromCard_excl y P (x :: y :: R) hyP).1]
  rw [below_cons, ite_eq_right (Ne.symm hyx)]
  rw [below_cons, ite_eq_left rfl]

/-- The `fromCard`-run at a card immediately following another known
card, when nothing earlier in the prefix meets the cut. -/
private theorem fromCard_second_cons (P R : List Card) {x y : Card}
    (hyP : y ∉ P) (hyx : y ≠ x) :
    fromCard y (P ++ x :: y :: R) = y :: R := by
  rw [(tfc_below_fromCard_excl y P (x :: y :: R) hyP).2]
  rw [tfc_fromCard_cons, ite_eq_right (Ne.symm hyx)]
  rw [tfc_fromCard_cons, ite_eq_left rfl]

/-- **`exchangeSuffix_eq_splice_bottom`** — exchanging the full
suffixes above the twin hosts `x` and `x.twin` is the same state edit
as splicing the runs headed at the bottom riders `y` and `y.twin`. -/
theorem exchangeSuffix_eq_splice_bottom
    {s : State} {x y : Card} {a b : Anchor} {restA restB : List Card}
    (hwf : s.WF)
    (ha : s.pileHolding x = some a) (hb : s.pileHolding x.twin = some b) (hab : a ≠ b)
    (hA : State.above x (s.piles a).faceUp = y :: restA)
    (hB : State.above x.twin (s.piles b).faceUp = y.twin :: restB) :
    s.exchangeSuffix x = s.spliceTwinRuns y := by
  have hxmemA : x ∈ (s.piles a).faceUp := pileHolding_mem ha
  have htmemB : x.twin ∈ (s.piles b).faceUp := pileHolding_mem hb
  have hcardA : fromCard x (s.piles a).faceUp = x :: y :: restA := by
    rw [fromCard_eq_cons_above hxmemA, hA]
  have hcardB : fromCard x.twin (s.piles b).faceUp = x.twin :: y.twin :: restB := by
    rw [fromCard_eq_cons_above htmemB, hB]
  have hsplitA : (s.piles a).faceUp =
      below x (s.piles a).faceUp ++ x :: y :: restA := by
    calc
      (s.piles a).faceUp =
          below x (s.piles a).faceUp ++ fromCard x (s.piles a).faceUp :=
        (tfc_below_fromCard x (s.piles a).faceUp).symm
      _ = below x (s.piles a).faceUp ++ x :: y :: restA := by rw [hcardA]
  have hsplitB : (s.piles b).faceUp =
      below x.twin (s.piles b).faceUp ++ x.twin :: y.twin :: restB := by
    calc
      (s.piles b).faceUp =
          below x.twin (s.piles b).faceUp ++ fromCard x.twin (s.piles b).faceUp :=
        (tfc_below_fromCard x.twin (s.piles b).faceUp).symm
      _ = below x.twin (s.piles b).faceUp ++ x.twin :: y.twin :: restB := by rw [hcardB]
  have hyFromA : y ∈ fromCard x (s.piles a).faceUp := by
    rw [hcardA]
    simp
  have hyA : y ∈ (s.piles a).faceUp := tfc_mem_fromCard _ hyFromA
  have hytFromB : y.twin ∈ fromCard x.twin (s.piles b).faceUp := by
    rw [hcardB]
    simp
  have hytB : y.twin ∈ (s.piles b).faceUp := tfc_mem_fromCard _ hytFromB
  have hyNotBelowA : y ∉ below x (s.piles a).faceUp :=
    fun h => below_fromCard_disjoint (hwf.runOK_of a) h hyFromA
  have hytNotBelowB : y.twin ∉ below x.twin (s.piles b).faceUp :=
    fun h => below_fromCard_disjoint (hwf.runOK_of b) h hytFromB
  have hokFromA : runOK (x :: y :: restA) = true := by
    rw [← hcardA]
    exact tfc_runOK_fromCard _ _ (hwf.runOK_of a)
  have hokFromB : runOK (x.twin :: y.twin :: restB) = true := by
    rw [← hcardB]
    exact tfc_runOK_fromCard _ _ (hwf.runOK_of b)
  have hyNeX : y ≠ x := by
    have hxnot : x ∉ y :: restA := (List.nodup_cons.mp (runOK_nodup hokFromA)).1
    intro hyx
    exact hxnot (by rw [← hyx]; exact List.mem_cons_self)
  have hytNeTwin : y.twin ≠ x.twin := by
    have htnot : x.twin ∉ y.twin :: restB :=
      (List.nodup_cons.mp (runOK_nodup hokFromB)).1
    intro hyt
    exact htnot (by rw [← hyt]; exact List.mem_cons_self)
  have hbelowA : below y (s.piles a).faceUp =
      below x (s.piles a).faceUp ++ [x] := by
    conv =>
      lhs
      rw [hsplitA]
    exact below_second_cons _ _ hyNotBelowA hyNeX
  have hfromA : fromCard y (s.piles a).faceUp = y :: restA := by
    conv =>
      lhs
      rw [hsplitA]
    exact fromCard_second_cons _ _ hyNotBelowA hyNeX
  have hbelowB : below y.twin (s.piles b).faceUp =
      below x.twin (s.piles b).faceUp ++ [x.twin] := by
    conv =>
      lhs
      rw [hsplitB]
    exact below_second_cons _ _ hytNotBelowB hytNeTwin
  have hfromB : fromCard y.twin (s.piles b).faceUp = y.twin :: restB := by
    conv =>
      lhs
      rw [hsplitB]
    exact fromCard_second_cons _ _ hytNotBelowB hytNeTwin
  have hya : s.pileHolding y = some a := (pileHolding_eq_some_iff hwf).2 hyA
  have hytb : s.pileHolding y.twin = some b := (pileHolding_eq_some_iff hwf).2 hytB
  apply State.ext
  · rw [exchangeSuffix_found ha hb hab, spliceTwinRuns_found hya hytb hab]
  · funext a'
    by_cases h1 : a' = a
    · rw [h1]
      apply Pile.ext
      · rw [exchangeSuffix_piles_hidden ha hb hab a,
          spliceTwinRuns_piles_self hya hytb hab]
      · rw [exchangeSuffix_piles_self ha hb hab,
          spliceTwinRuns_piles_self hya hytb hab]
        rw [hB, hbelowA, hfromB, List.append_assoc]
    · by_cases h2 : a' = b
      · rw [h2]
        apply Pile.ext
        · rw [exchangeSuffix_piles_hidden ha hb hab b,
            spliceTwinRuns_piles_second hya hytb hab]
        · rw [exchangeSuffix_piles_second ha hb hab,
            spliceTwinRuns_piles_second hya hytb hab]
          rw [hA, hbelowB, hfromA, List.append_assoc]
      · apply Pile.ext
        · rw [exchangeSuffix_piles_other ha hb hab h1 h2,
            spliceTwinRuns_piles_other hya hytb hab h1 h2]
        · rw [exchangeSuffix_piles_other ha hb hab h1 h2,
            spliceTwinRuns_piles_other hya hytb hab h1 h2]
  · rw [exchangeSuffix_stock ha hb hab, spliceTwinRuns_stock hya hytb hab]
  · rw [exchangeSuffix_waste ha hb hab, spliceTwinRuns_waste hya hytb hab]
  · rw [exchangeSuffix_drawStep ha hb hab, spliceTwinRuns_drawStep hya hytb hab]

#print axioms exchangeSuffix_eq_splice_bottom
