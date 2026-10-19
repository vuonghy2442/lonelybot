import Orig2.TwinSplice
import Orig2.TwinSpliceWF
import Orig2.TwinRelabel
import Orig2.TwinEquivariance
import Orig2.Integrity

set_option linter.unusedSectionVars false

/-!
# Orig2.TwinSuffixExchange — the suffix exchange `E_x` and `P_x = ρ_x ∘ E_x`

The suffix exchange `State.exchangeSuffix x` acts on the both-on-parents
case: the hosts `x` and `x.twin` keep the piles they sit in, while the
face-up suffixes strictly above them cross.  If `x` sits in pile `a` and
`x.twin` in pile `b`, the new runs are

* pile `a`: `below x faA ++ [x] ++ above x.twin faB`,
* pile `b`: `below x.twin faB ++ [x.twin] ++ above x faA`,

with the hidden decks untouched.

The main result is the decomposition `P_x = ρ_x ∘ E_x`: relabeling the
suffix exchange by the card involution gives the run splice
`State.spliceTwinRuns`, hence the strict twin swap at both-on-parents
pair seats.  Zero `sorry`, zero `Classical.choice`.
-/

namespace State

/-- The cards of the face-up run strictly above the first occurrence of
`c` (the tail of `fromCard`). -/
def above (c : Card) (l : List Card) : List Card := (fromCard c l).tail

/-- A member heads the `fromCard` run, whose tail is `above`. -/
theorem fromCard_eq_cons_above {c : Card} {l : List Card} (hmem : c ∈ l) :
    fromCard c l = c :: above c l := by
  obtain ⟨t, ht⟩ := tfc_fromCard_cons_head l hmem
  rw [ht]
  unfold above
  rw [ht]
  rfl

/-- **`State.exchangeSuffix x`** — cross the face-up suffixes strictly
above the twins, keeping the hosts pinned.  If either twin is not held
face up, or both are held by the same pile, the state is returned
unchanged. -/
def exchangeSuffix (x : Card) (st : State) : State :=
  match st.pileHolding x, st.pileHolding x.twin with
  | some a, some b =>
      if a = b then st
      else
        { st with
          piles := fun a' =>
            if a' = a then
              { hidden := (st.piles a).hidden
                faceUp := below x (st.piles a).faceUp ++ [x] ++
                  above x.twin (st.piles b).faceUp }
            else if a' = b then
              { hidden := (st.piles b).hidden
                faceUp := below x.twin (st.piles b).faceUp ++ [x.twin] ++
                  above x (st.piles a).faceUp }
            else st.piles a' }
  | _, _ => st

variable {st : State} {x : Card} {a b : Anchor}

theorem exchangeSuffix_piles_self
    (ha : st.pileHolding x = some a) (hb : st.pileHolding x.twin = some b)
    (hab : a ≠ b) :
    (st.exchangeSuffix x).piles a =
      { hidden := (st.piles a).hidden
        faceUp := below x (st.piles a).faceUp ++ [x] ++
          above x.twin (st.piles b).faceUp } := by
  simp [State.exchangeSuffix, ha, hb, hab]

theorem exchangeSuffix_piles_second
    (ha : st.pileHolding x = some a) (hb : st.pileHolding x.twin = some b)
    (hab : a ≠ b) :
    (st.exchangeSuffix x).piles b =
      { hidden := (st.piles b).hidden
        faceUp := below x.twin (st.piles b).faceUp ++ [x.twin] ++
          above x (st.piles a).faceUp } := by
  simp [State.exchangeSuffix, ha, hb, hab, Ne.symm hab]

theorem exchangeSuffix_piles_other
    (ha : st.pileHolding x = some a) (hb : st.pileHolding x.twin = some b)
    (hab : a ≠ b) {a' : Anchor} (h₁ : a' ≠ a) (h₂ : a' ≠ b) :
    (st.exchangeSuffix x).piles a' = st.piles a' := by
  simp [State.exchangeSuffix, ha, hb, hab, h₁, h₂]

theorem exchangeSuffix_piles_hidden
    (ha : st.pileHolding x = some a) (hb : st.pileHolding x.twin = some b)
    (hab : a ≠ b) (a' : Anchor) :
    ((st.exchangeSuffix x).piles a').hidden = (st.piles a').hidden := by
  by_cases h₁ : a' = a
  · subst h₁
    rw [exchangeSuffix_piles_self ha hb hab]
  · by_cases h₂ : a' = b
    · subst h₂
      rw [exchangeSuffix_piles_second ha hb hab]
    · rw [exchangeSuffix_piles_other ha hb hab h₁ h₂]

theorem exchangeSuffix_found
    (ha : st.pileHolding x = some a) (hb : st.pileHolding x.twin = some b)
    (hab : a ≠ b) : (st.exchangeSuffix x).found = st.found := by
  simp [State.exchangeSuffix, ha, hb, hab]

theorem exchangeSuffix_stock
    (ha : st.pileHolding x = some a) (hb : st.pileHolding x.twin = some b)
    (hab : a ≠ b) : (st.exchangeSuffix x).stock = st.stock := by
  simp [State.exchangeSuffix, ha, hb, hab]

theorem exchangeSuffix_waste
    (ha : st.pileHolding x = some a) (hb : st.pileHolding x.twin = some b)
    (hab : a ≠ b) : (st.exchangeSuffix x).waste = st.waste := by
  simp [State.exchangeSuffix, ha, hb, hab]

theorem exchangeSuffix_drawStep
    (ha : st.pileHolding x = some a) (hb : st.pileHolding x.twin = some b)
    (hab : a ≠ b) : (st.exchangeSuffix x).drawStep = st.drawStep := by
  simp [State.exchangeSuffix, ha, hb, hab]

end State

open State

/-! ## §1. List kit -/

/-- A member never occurs again strictly above itself in a legal run. -/
private theorem above_not_mem_self {c : Card} {l : List Card}
    (hok : runOK l = true) (hmem : c ∈ l) : c ∉ above c l := by
  have hr : fromCard c l = c :: above c l := fromCard_eq_cons_above hmem
  have hok' : runOK (c :: above c l) = true := by
    rw [← hr]
    exact tfc_runOK_fromCard l c hok
  have hnd := runOK_nodup hok'
  rw [List.nodup_cons] at hnd
  exact hnd.1

/-- A list all of whose entries are fixed by `f` is unchanged by
`List.map f`. -/
private theorem list_map_eq_self {α : Type} (f : α → α) :
    ∀ {l : List α}, (∀ a ∈ l, f a = a) → l.map f = l
  | [], _ => rfl
  | a :: t, h => by
      rw [List.map_cons, h a (by simp)]
      exact congrArg (a :: ·) (list_map_eq_self f (fun b hb => h b (by simp [hb])))

/-- Relabeling the joined suffix of the `x`-side turns it into the
`x.twin`-headed run splice. -/
private theorem map_relabel_join_self {x : Card} {P S : List Card}
    (hP : ∀ y ∈ P, Card.relabelTwin x y = y)
    (hS : ∀ y ∈ S, Card.relabelTwin x y = y) :
    (P ++ [x] ++ S).map (Card.relabelTwin x) = P ++ x.twin :: S := by
  rw [show P ++ [x] ++ S = P ++ ([x] ++ S) from List.append_assoc P [x] S]
  rw [List.map_append, list_map_eq_self _ hP, List.map_append,
    list_map_eq_self _ hS]
  simp only [List.map_cons, List.map_nil, card_relabelTwin_self,
    List.singleton_append]

/-- Relabeling the joined suffix of the `x.twin`-side turns it into the
`x`-headed run splice. -/
private theorem map_relabel_join_twin {x : Card} {P S : List Card}
    (hP : ∀ y ∈ P, Card.relabelTwin x y = y)
    (hS : ∀ y ∈ S, Card.relabelTwin x y = y) :
    (P ++ [x.twin] ++ S).map (Card.relabelTwin x) = P ++ x :: S := by
  rw [show P ++ [x.twin] ++ S = P ++ ([x.twin] ++ S)
    from List.append_assoc P [x.twin] S]
  rw [List.map_append, list_map_eq_self _ hP, List.map_append,
    list_map_eq_self _ hS]
  simp only [List.map_cons, List.map_nil, card_relabelTwin_twin,
    List.singleton_append]

/-! ## §2. The seat equations -/

/-- **`seatOf_exchangeSuffix_self`** — the exchange pins `x` in its
host pile, so its seat is unchanged. -/
theorem seatOf_exchangeSuffix_self {st : State} {x : Card} {a b : Anchor}
    (hwf : st.WF)
    (ha : st.pileHolding x = some a) (hb : st.pileHolding x.twin = some b)
    (hab : a ≠ b) :
    seatOf (st.exchangeSuffix x) x = seatOf st x := by
  have hxmem : x ∈ (st.piles a).faceUp := pileHolding_mem ha
  have hxB : x ∉ (st.piles b).faceUp :=
    (mem_faceUp_unique hwf hxmem b (Ne.symm hab)).1
  have hxabove : x ∉ above x (st.piles a).faceUp :=
    above_not_mem_self (hwf.runOK_of a) hxmem
  have hnew : (st.exchangeSuffix x).pileHolding x = some a := by
    refine tfc_pileHolding_pin ?_ ?_
    · rw [exchangeSuffix_piles_self ha hb hab]
      simp
    · intro j hj
      by_cases hjb : j = b
      · subst hjb
        rw [exchangeSuffix_piles_second ha hb hab]
        intro hm
        rcases List.mem_append.mp hm with hleft | hright
        · rcases List.mem_append.mp hleft with hpre | hsingle
          · exact hxB (mem_below _ hpre)
          · exact card_twin_ne x (List.mem_singleton.mp hsingle).symm
        · exact hxabove hright
      · rw [exchangeSuffix_piles_other ha hb hab hj hjb]
        exact (mem_faceUp_unique hwf hxmem j hj).1
  rw [tfc_seatOf_pair hnew, tfc_seatOf_pair ha]
  have hbelow : below x ((st.exchangeSuffix x).piles a).faceUp =
      below x (st.piles a).faceUp := by
    rw [exchangeSuffix_piles_self ha hb hab, List.append_assoc]
    rw [(tfc_below_fromCard_excl x (below x (st.piles a).faceUp)
      ([x] ++ above x.twin (st.piles b).faceUp)
      (tfc_below_not_mem_self x _)).1]
    rw [List.singleton_append, below_cons, ite_eq_left rfl, List.append_nil]
  rw [hbelow]

/-- **`seatOf_exchangeSuffix_twin`** — the exchange pins `x.twin` in
its host pile, so its seat is unchanged. -/
theorem seatOf_exchangeSuffix_twin {st : State} {x : Card} {a b : Anchor}
    (hwf : st.WF)
    (ha : st.pileHolding x = some a) (hb : st.pileHolding x.twin = some b)
    (hab : a ≠ b) :
    seatOf (st.exchangeSuffix x) x.twin = seatOf st x.twin := by
  have htmem : x.twin ∈ (st.piles b).faceUp := pileHolding_mem hb
  have htA : x.twin ∉ (st.piles a).faceUp :=
    (mem_faceUp_unique hwf htmem a hab).1
  have htabove : x.twin ∉ above x.twin (st.piles b).faceUp :=
    above_not_mem_self (hwf.runOK_of b) htmem
  have hnew : (st.exchangeSuffix x).pileHolding x.twin = some b := by
    refine tfc_pileHolding_pin ?_ ?_
    · rw [exchangeSuffix_piles_second ha hb hab]
      simp
    · intro j hj
      by_cases hja : j = a
      · subst hja
        rw [exchangeSuffix_piles_self ha hb hab]
        intro hm
        rcases List.mem_append.mp hm with hleft | hright
        · rcases List.mem_append.mp hleft with hpre | hsingle
          · exact htA (mem_below _ hpre)
          · exact card_twin_ne x (List.mem_singleton.mp hsingle)
        · exact htabove hright
      · rw [exchangeSuffix_piles_other ha hb hab hja hj]
        exact (mem_faceUp_unique hwf htmem j hj).1
  rw [tfc_seatOf_pair hnew, tfc_seatOf_pair hb]
  have hbelow : below x.twin ((st.exchangeSuffix x).piles b).faceUp =
      below x.twin (st.piles b).faceUp := by
    rw [exchangeSuffix_piles_second ha hb hab, List.append_assoc]
    rw [(tfc_below_fromCard_excl x.twin (below x.twin (st.piles b).faceUp)
      ([x.twin] ++ above x (st.piles a).faceUp)
      (tfc_below_not_mem_self x.twin _)).1]
    rw [List.singleton_append, below_cons, ite_eq_left rfl, List.append_nil]
  rw [hbelow]

/-! ## §3. The riders -/

/-- **`seatOf_exchangeSuffix_rider_A`** — the bottom rider `y` above
`x` moves onto the other host `x.twin`. -/
theorem seatOf_exchangeSuffix_rider_A {st : State} {x y : Card} {a b : Anchor}
    (hwf : st.WF)
    (ha : st.pileHolding x = some a) (hb : st.pileHolding x.twin = some b)
    (hab : a ≠ b)
    (hhead : ∃ r, fromCard x (st.piles a).faceUp = x :: y :: r) :
    seatOf (st.exchangeSuffix x) y = some (Sum.inr x.twin) := by
  obtain ⟨r, hr⟩ := hhead
  have hyFrom : y ∈ fromCard x (st.piles a).faceUp := by
    rw [hr]
    simp
  have hyA : y ∈ (st.piles a).faceUp := tfc_mem_fromCard _ hyFrom
  have hok_from : runOK (x :: y :: r) = true := by
    rw [← hr]
    exact tfc_runOK_fromCard _ _ (hwf.runOK_of a)
  have hx_not_yr : x ∉ y :: r := (List.nodup_cons.mp (runOK_nodup hok_from)).1
  have hy_ne_x : y ≠ x := by
    intro hyx
    exact hx_not_yr (by rw [← hyx]; simp)
  have hy_not_B : y ∉ (st.piles b).faceUp :=
    (mem_faceUp_unique hwf hyA b (Ne.symm hab)).1
  have hy_ne_twin : y ≠ x.twin :=
    fun h => (mem_faceUp_unique hwf (pileHolding_mem hb) a hab).1 (h ▸ hyA)
  have hy_not_preA : y ∉ below x (st.piles a).faceUp :=
    fun h => run_split_disjoint (hwf.runOK_of a) h hyFrom
  have hsufA : above x (st.piles a).faceUp = y :: r := by
    rw [above, hr]
    rfl
  have hnew : (st.exchangeSuffix x).pileHolding y = some b := by
    refine tfc_pileHolding_pin ?_ ?_
    · rw [exchangeSuffix_piles_second ha hb hab, hsufA]
      exact List.mem_append.mpr (Or.inr (by simp))
    · intro j hj
      by_cases hja : j = a
      · subst hja
        rw [exchangeSuffix_piles_self ha hb hab]
        intro hm
        rcases List.mem_append.mp hm with hleft | hright
        · rcases List.mem_append.mp hleft with hpre | hsingle
          · exact hy_not_preA hpre
          · exact hy_ne_x (List.mem_singleton.mp hsingle)
        · exact hy_not_B (tfc_mem_fromCard _ (List.mem_of_mem_tail hright))
      · rw [exchangeSuffix_piles_other ha hb hab hja hj]
        exact (mem_faceUp_unique hwf hyA j hja).1
  have hbelow : lastOf (below y ((st.exchangeSuffix x).piles b).faceUp) =
      some x.twin := by
    rw [exchangeSuffix_piles_second ha hb hab, hsufA, List.append_assoc]
    have hy_not_preB : y ∉ below x.twin (st.piles b).faceUp :=
      fun h => hy_not_B (mem_below _ h)
    rw [(tfc_below_fromCard_excl y (below x.twin (st.piles b).faceUp)
      ([x.twin] ++ y :: r) hy_not_preB).1]
    have hinner : below y (x.twin :: y :: r) = [x.twin] := by
      rw [below_cons, ite_eq_right (fun h => hy_ne_twin h.symm), below_cons,
        ite_eq_left rfl]
    rw [List.singleton_append, hinner, lastOf_snoc]
  exact tfc_seatOf_inr_intro hnew hbelow

/-- **`seatOf_exchangeSuffix_rider_B`** — the bottom rider `y` above
`x.twin` moves onto the other host `x`. -/
theorem seatOf_exchangeSuffix_rider_B {st : State} {x y : Card} {a b : Anchor}
    (hwf : st.WF)
    (ha : st.pileHolding x = some a) (hb : st.pileHolding x.twin = some b)
    (hab : a ≠ b)
    (hhead : ∃ r, fromCard x.twin (st.piles b).faceUp = x.twin :: y :: r) :
    seatOf (st.exchangeSuffix x) y = some (Sum.inr x) := by
  obtain ⟨r, hr⟩ := hhead
  have hyFrom : y ∈ fromCard x.twin (st.piles b).faceUp := by
    rw [hr]
    simp
  have hyB : y ∈ (st.piles b).faceUp := tfc_mem_fromCard _ hyFrom
  have hok_from : runOK (x.twin :: y :: r) = true := by
    rw [← hr]
    exact tfc_runOK_fromCard _ _ (hwf.runOK_of b)
  have ht_not_yr : x.twin ∉ y :: r :=
    (List.nodup_cons.mp (runOK_nodup hok_from)).1
  have hy_ne_twin : y ≠ x.twin := by
    intro hyt
    exact ht_not_yr (by rw [← hyt]; simp)
  have hy_not_A : y ∉ (st.piles a).faceUp :=
    (mem_faceUp_unique hwf hyB a hab).1
  have hy_ne_x : y ≠ x :=
    fun h => (mem_faceUp_unique hwf (pileHolding_mem ha) b (Ne.symm hab)).1 (h ▸ hyB)
  have hy_not_preB : y ∉ below x.twin (st.piles b).faceUp :=
    fun h => run_split_disjoint (hwf.runOK_of b) h hyFrom
  have hsufB : above x.twin (st.piles b).faceUp = y :: r := by
    rw [above, hr]
    rfl
  have hnew : (st.exchangeSuffix x).pileHolding y = some a := by
    refine tfc_pileHolding_pin ?_ ?_
    · rw [exchangeSuffix_piles_self ha hb hab, hsufB]
      exact List.mem_append.mpr (Or.inr (by simp))
    · intro j hj
      by_cases hjb : j = b
      · subst hjb
        rw [exchangeSuffix_piles_second ha hb hab]
        intro hm
        rcases List.mem_append.mp hm with hleft | hright
        · rcases List.mem_append.mp hleft with hpre | hsingle
          · exact hy_not_preB hpre
          · exact hy_ne_twin (List.mem_singleton.mp hsingle)
        · exact hy_not_A (tfc_mem_fromCard _ (List.mem_of_mem_tail hright))
      · rw [exchangeSuffix_piles_other ha hb hab hj hjb]
        exact (mem_faceUp_unique hwf hyB j hjb).1
  have hbelow : lastOf (below y ((st.exchangeSuffix x).piles a).faceUp) =
      some x := by
    rw [exchangeSuffix_piles_self ha hb hab, hsufB, List.append_assoc]
    have hy_not_preA : y ∉ below x (st.piles a).faceUp :=
      fun h => hy_not_A (mem_below _ h)
    rw [(tfc_below_fromCard_excl y (below x (st.piles a).faceUp)
      ([x] ++ y :: r) hy_not_preA).1]
    have hinner : below y (x :: y :: r) = [x] := by
      rw [below_cons, ite_eq_right (fun h => hy_ne_x h.symm), below_cons,
        ite_eq_left rfl]
    rw [List.singleton_append, hinner, lastOf_snoc]
  exact tfc_seatOf_inr_intro hnew hbelow

/-! ## §4. The decomposition `P_x = ρ_x ∘ E_x` -/

/-- **`relabelTwin_exchangeSuffix`** — relabeling the suffix exchange
by the card involution gives the run splice. -/
theorem relabelTwin_exchangeSuffix {st : State} {x : Card} (hwf : st.WF)
    (hx : ∃ z, seatOf st x = some (Sum.inr z))
    (hxt : ∃ z : Card, seatOf st x.twin = some (Sum.inr z.twin)) :
    State.relabelTwin x (st.exchangeSuffix x) = st.spliceTwinRuns x := by
  obtain ⟨z, hzse⟩ := hx
  obtain ⟨w, hwse⟩ := hxt
  obtain ⟨a, ha, -, -⟩ := tfc_seatOf_of_inr hzse
  obtain ⟨b, hb, -, -⟩ := tfc_seatOf_of_inr hwse
  have hxmem : x ∈ (st.piles a).faceUp := pileHolding_mem ha
  have htmem : x.twin ∈ (st.piles b).faceUp := pileHolding_mem hb
  have hab : a ≠ b := by
    intro hab
    subst hab
    have heq : x = x.twin :=
      runOK_rank_distinct (hwf.runOK_of a) hxmem htmem rfl
    exact card_twin_ne x heq.symm
  have hx_not_B : x ∉ (st.piles b).faceUp :=
    (mem_faceUp_unique hwf hxmem b (Ne.symm hab)).1
  have ht_not_A : x.twin ∉ (st.piles a).faceUp :=
    (mem_faceUp_unique hwf htmem a hab).1
  obtain ⟨hxA_other, hxA_hidden, hxA_stock, hxA_waste, hxA_found⟩ :=
    mem_faceUp_only hwf hxmem
  obtain ⟨htB_other, htB_hidden, htB_stock, htB_waste, htB_found⟩ :=
    mem_faceUp_only hwf htmem
  have hfix_hidden : ∀ a' (y : Card), y ∈ (st.piles a').hidden →
      Card.relabelTwin x y = y := by
    intro a' y hy
    refine card_relabelTwin_ne ?_ ?_
    · intro hyx
      subst y
      by_cases hAa : a' = a
      · subst hAa
        exact hxA_hidden hy
      · exact (hxA_other a' hAa).1 hy
    · intro hyt
      subst y
      by_cases hBb : a' = b
      · subst hBb
        exact htB_hidden hy
      · exact (htB_other a' hBb).1 hy
  have hfix_other_faceUp : ∀ a' (y : Card), a' ≠ a → a' ≠ b →
      y ∈ (st.piles a').faceUp → Card.relabelTwin x y = y := by
    intro a' y hAa hBb hy
    exact card_relabelTwin_ne
      (fun hyx => (hxA_other a' hAa).2 (hyx ▸ hy))
      (fun hyt => (htB_other a' hBb).2 (hyt ▸ hy))
  have hfix_found : ∀ s (y : Card), y ∈ st.found s →
      Card.relabelTwin x y = y := by
    intro s y hy
    exact card_relabelTwin_ne
      (fun hyx => hxA_found s (hyx ▸ hy))
      (fun hyt => htB_found s (hyt ▸ hy))
  have hfix_stock : ∀ y ∈ st.stock, Card.relabelTwin x y = y := by
    intro y hy
    exact card_relabelTwin_ne
      (fun hyx => hxA_stock (hyx ▸ hy))
      (fun hyt => htB_stock (hyt ▸ hy))
  have hfix_waste : ∀ y ∈ st.waste, Card.relabelTwin x y = y := by
    intro y hy
    exact card_relabelTwin_ne
      (fun hyx => hxA_waste (hyx ▸ hy))
      (fun hyt => htB_waste (hyt ▸ hy))
  have hpreA_fix : ∀ y ∈ below x (st.piles a).faceUp,
      Card.relabelTwin x y = y := by
    intro y hy
    refine card_relabelTwin_ne ?_ ?_
    · intro hyx
      subst y
      exact tfc_below_not_mem_self x _ hy
    · intro hyt
      subst y
      exact ht_not_A (mem_below _ hy)
  have hpreB_fix : ∀ y ∈ below x.twin (st.piles b).faceUp,
      Card.relabelTwin x y = y := by
    intro y hy
    refine card_relabelTwin_ne ?_ ?_
    · intro hyx
      subst y
      exact hx_not_B (mem_below _ hy)
    · intro hyt
      subst y
      exact tfc_below_not_mem_self x.twin _ hy
  have hsufA_fix : ∀ y ∈ above x (st.piles a).faceUp,
      Card.relabelTwin x y = y := by
    intro y hy
    have hyFrom : y ∈ fromCard x (st.piles a).faceUp := List.mem_of_mem_tail hy
    have hyA : y ∈ (st.piles a).faceUp := tfc_mem_fromCard _ hyFrom
    refine card_relabelTwin_ne ?_ ?_
    · intro hyx
      subst y
      exact above_not_mem_self (hwf.runOK_of a) hxmem hy
    · intro hyt
      subst y
      exact ht_not_A hyA
  have hsufB_fix : ∀ y ∈ above x.twin (st.piles b).faceUp,
      Card.relabelTwin x y = y := by
    intro y hy
    have hyFrom : y ∈ fromCard x.twin (st.piles b).faceUp := List.mem_of_mem_tail hy
    have hyB : y ∈ (st.piles b).faceUp := tfc_mem_fromCard _ hyFrom
    refine card_relabelTwin_ne ?_ ?_
    · intro hyx
      subst y
      exact hx_not_B hyB
    · intro hyt
      subst y
      exact above_not_mem_self (hwf.runOK_of b) htmem hy
  apply State.ext
  · funext s
    rw [state_relabelTwin_found, exchangeSuffix_found ha hb hab,
      spliceTwinRuns_found ha hb hab]
    exact list_map_eq_self _ (fun y hy => hfix_found s y hy)
  · funext a'
    by_cases h₁ : a' = a
    · subst a'
      apply Pile.ext
      · rw [state_relabelTwin_piles_hidden,
          exchangeSuffix_piles_hidden ha hb hab a,
          spliceTwinRuns_piles_self ha hb hab]
        exact list_map_eq_self _ (fun y hy => hfix_hidden a y hy)
      · rw [state_relabelTwin_piles_faceUp, exchangeSuffix_piles_self ha hb hab,
          spliceTwinRuns_piles_self ha hb hab]
        rw [fromCard_eq_cons_above htmem]
        exact map_relabel_join_self hpreA_fix hsufB_fix
    · by_cases h₂ : a' = b
      · subst a'
        apply Pile.ext
        · rw [state_relabelTwin_piles_hidden,
            exchangeSuffix_piles_hidden ha hb hab b,
            spliceTwinRuns_piles_second ha hb hab]
          exact list_map_eq_self _ (fun y hy => hfix_hidden b y hy)
        · rw [state_relabelTwin_piles_faceUp, exchangeSuffix_piles_second ha hb hab,
            spliceTwinRuns_piles_second ha hb hab]
          rw [fromCard_eq_cons_above hxmem]
          exact map_relabel_join_twin hpreB_fix hsufA_fix
      · apply Pile.ext
        · rw [state_relabelTwin_piles_hidden,
            exchangeSuffix_piles_other ha hb hab h₁ h₂,
            spliceTwinRuns_piles_other ha hb hab h₁ h₂]
          exact list_map_eq_self _ (fun y hy => hfix_hidden a' y hy)
        · rw [state_relabelTwin_piles_faceUp,
            exchangeSuffix_piles_other ha hb hab h₁ h₂,
            spliceTwinRuns_piles_other ha hb hab h₁ h₂]
          exact list_map_eq_self _ (fun y hy => hfix_other_faceUp a' y h₁ h₂ hy)
  · rw [state_relabelTwin_stock, exchangeSuffix_stock ha hb hab,
      spliceTwinRuns_stock ha hb hab]
    exact list_map_eq_self _ hfix_stock
  · rw [state_relabelTwin_waste, exchangeSuffix_waste ha hb hab,
      spliceTwinRuns_waste ha hb hab]
    exact list_map_eq_self _ hfix_waste
  · rw [state_relabelTwin_drawStep, exchangeSuffix_drawStep ha hb hab,
      spliceTwinRuns_drawStep ha hb hab]

/-! ## §5. The point-swap composition corollary -/

/-- **`splice_eq_relabel_exchange`** — `P_x` is the relabeling of the
suffix exchange, so the strict twin swap follows from the splice
bridge. -/
theorem splice_eq_relabel_exchange {st : State} {x : Card} (hwf : st.WF)
    (hx : ∃ z, seatOf st x = some (Sum.inr z))
    (hxt : ∃ z : Card, seatOf st x.twin = some (Sum.inr z.twin)) :
    twinPairSwapStrict st (State.relabelTwin x (st.exchangeSuffix x)) x := by
  rw [relabelTwin_exchangeSuffix hwf hx hxt]
  exact twinPairSwapStrict_splice hwf hx hxt

/-! ## §6. Audit battery -/

/-- The suffix exchange preserves WF.  This follows from the decomposition
`ρ_x(E_x) = P_x`, the WF of the run splice, and the WF of the relabel:
`E_x = ρ_x(P_x)`. -/
theorem wf_exchangeSuffix {st : State} {x : Card} (hwf : st.WF)
    (hx : ∃ z, seatOf st x = some (Sum.inr z))
    (hxt : ∃ z : Card, seatOf st x.twin = some (Sum.inr z.twin)) :
    (st.exchangeSuffix x).WF := by
  obtain ⟨zx, hzx⟩ := hx
  obtain ⟨zt, hzt⟩ := hxt
  obtain ⟨a, ha, -, -⟩ := tfc_seatOf_of_inr hzx
  obtain ⟨b, hb, -, -⟩ := tfc_seatOf_of_inr hzt
  have hab : a ≠ b := by
    intro hab
    subst hab
    have htmem : x.twin ∈ (st.piles a).faceUp := pileHolding_mem hb
    have heq : x = x.twin :=
      runOK_rank_distinct (hwf.runOK_of a) (pileHolding_mem ha) htmem rfl
    exact card_twin_ne x heq.symm
  have hPwf : (st.spliceTwinRuns x).WF := wf_spliceTwinRuns hwf ⟨zx, hzx⟩ ⟨zt, hzt⟩
  have hrel : State.relabelTwin x (st.exchangeSuffix x) = st.spliceTwinRuns x :=
    relabelTwin_exchangeSuffix hwf ⟨zx, hzx⟩ ⟨zt, hzt⟩
  have hEeq : st.exchangeSuffix x = State.relabelTwin x (st.spliceTwinRuns x) := by
    have h := congrArg (State.relabelTwin x) hrel
    rw [state_relabelTwin_involutive] at h
    exact h
  rw [hEeq]
  refine wf_relabelTwin hPwf ⟨Sum.inr zt.twin, ?_⟩ ⟨Sum.inr zx, ?_⟩
  · rw [seatOf_splice_self hwf ha hb hab]
    exact hzt
  · rw [seatOf_splice_twin hwf ha hb hab]
    exact hzx

#print axioms seatOf_exchangeSuffix_self
#print axioms seatOf_exchangeSuffix_twin
#print axioms seatOf_exchangeSuffix_rider_A
#print axioms seatOf_exchangeSuffix_rider_B
#print axioms relabelTwin_exchangeSuffix
#print axioms splice_eq_relabel_exchange
#print axioms wf_exchangeSuffix
