import Klondike.Basic
import Klondike.Cycle

/-!
# The kit: shared list/counting machinery

The generic lemmas the proofs share — the no-duplicate predicates,
list algebra, the splice (`Cycle.removeIdx`) kit, the filter lemmas,
the pigeonhole and bijection counts, and the radix encoding — one
home, so future proofs cite instead of re-declaring local copies.

Dependency floor: `Basic` and `Cycle` only.
-/

/-! ## No-duplicate predicates -/

/-- No duplicate cards (index-wise). -/
def noDupCards : List Card → Prop :=
  fun l => ∀ i j : Nat, i < l.length → j < l.length → l[i]? = l[j]? → i = j

/-! ## List algebra -/

/-- Reversal exchanges head and last (the `hiddenBase` walk). -/
theorem head?_reverse_eq_getLast? {α : Type} :
    ∀ (l : List α), l.reverse.head? = l.getLast? := by
  intro l
  induction l with
  | nil => rfl
  | cons a t ih =>
    cases t with
    | nil => rfl
    | cons b u =>
      cases hrev : (b :: u).reverse with
      | nil =>
        exfalso
        have ht := congrArg List.reverse hrev
        rw [List.reverse_reverse] at ht
        simp at ht
      | cons z zs =>
        rw [show (a :: b :: u).reverse = z :: (zs ++ [a]) from by
          rw [List.reverse_cons, hrev, List.cons_append]]
        rw [hrev] at ih
        exact ih

/-- Last-element membership. -/
theorem mem_of_getLast {l : List Card} {c : Card} (h : l.getLast? = some c) : c ∈ l := by
  rw [← head?_reverse_eq_getLast?] at h
  cases hrev : l.reverse with
  | nil => rw [hrev] at h; simp at h
  | cons x t =>
    rw [hrev] at h
    simp only [List.head?_cons, Option.some.injEq] at h
    subst h
    exact List.mem_reverse.mp (by rw [hrev]; exact List.mem_cons_self)

/-- Reassembling a chunk: the first `n` of `drop s`, followed by
`drop t` (with `s + n = t`), is `drop s` again. -/
theorem take_drop_chunk {α : Type} (l : List α) (s n t : Nat) (h : s + n = t) :
    (l.drop s).take n ++ l.drop t = l.drop s := by
  rw [← h, ← List.drop_drop, List.take_append_drop]

/-- The list splits around any member. -/
theorem mem_split {α : Type} : ∀ (l : List α) (x : α), x ∈ l →
    ∃ l₁ l₂, l = l₁ ++ x :: l₂ := by
  intro l
  induction l with
  | nil => intro x h; cases h
  | cons a t ih =>
      intro x h
      rcases List.mem_cons.mp h with rfl | h'
      · exact ⟨[], t, rfl⟩
      · obtain ⟨l₁, l₂, hs⟩ := ih x h'
        exact ⟨a :: l₁, l₂, by rw [hs, List.cons_append]⟩

/-- Membership gives an index. -/
theorem mem_index {a : Card} : ∀ (l : List Card), a ∈ l → ∃ i : Nat, l[i]? = some a := by
  intro l
  induction l with
  | nil => intro h; simp at h
  | cons x t ih =>
      intro h
      rcases List.mem_cons.mp h with rfl | h
      · exact ⟨0, rfl⟩
      · obtain ⟨i, hi⟩ := ih h
        exact ⟨i + 1, by rw [List.getElem?_cons_succ]; exact hi⟩

/-- Membership split: an element sits at some middle position. -/
theorem mem_middle_split {a : Card} : ∀ (l : List Card), a ∈ l →
    ∃ pre post : List Card, l = pre ++ a :: post := by
  intro l
  induction l with
  | nil => intro h; simp at h
  | cons x t ih =>
      intro h
      rcases List.mem_cons.mp h with rfl | h
      · exact ⟨[], t, rfl⟩
      · obtain ⟨pre, post, ht⟩ := ih h
        exact ⟨x :: pre, post, by simp [ht]⟩

/-! ## The NoDupP counting kit -/

/-- Head-style distinctness (the induction-friendly form). -/
def NoDupP : List Card → Prop
  | [] => True
  | a :: t => a ∉ t ∧ NoDupP t

/-- Distinctness: the marked element occurs nowhere else. -/
theorem nodupP_sub (a : Card) : ∀ (pre post : List Card),
    NoDupP (pre ++ a :: post) → a ∉ pre ++ post := by
  intro pre
  induction pre with
  | nil =>
      intro post hnd hap
      obtain ⟨h1, -⟩ := hnd
      exact h1 hap
  | cons p pre' ih =>
      intro post hnd hap
      obtain ⟨hp, hndp⟩ := hnd
      rcases List.mem_append.mp hap with hap | hap
      · rcases List.mem_cons.mp hap with hap | hap
        · exact hp (by simp [hap])
        · exact ih post hndp (List.mem_append.mpr (Or.inl hap))
      · exact ih post hndp (List.mem_append.mpr (Or.inr hap))

/-- Distinctness survives removing the marked element. -/
theorem nodupP_remove (a : Card) : ∀ (pre post : List Card),
    NoDupP (pre ++ a :: post) → NoDupP (pre ++ post) := by
  intro pre
  induction pre with
  | nil => intro post hnd; obtain ⟨-, h2⟩ := hnd; exact h2
  | cons p pre' ih =>
      intro post hnd
      obtain ⟨hp, hndp⟩ := hnd
      refine ⟨?_, ih post hndp⟩
      intro hpp
      rcases List.mem_append.mp hpp with h | h
      · exact hp (List.mem_append.mpr (Or.inl h))
      · exact hp (List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inr h))))

/-- The index-based distinctness implies the head-style one. -/
theorem noDupCards_NoDupP : ∀ {l : List Card}, noDupCards l → NoDupP l := by
  intro l
  induction l with
  | nil => intro _; trivial
  | cons a t ih =>
      intro hnd
      refine ⟨?_, ih ?_⟩
      · intro hat
        obtain ⟨i, hi⟩ := mem_index t hat
        obtain ⟨hib, -⟩ := List.getElem?_eq_some_iff.mp hi
        have h0 : (a :: t)[0]? = some a := rfl
        have h1 : (a :: t)[i + 1]? = some a := by
          rw [List.getElem?_cons_succ]; exact hi
        have hcon : 0 = i + 1 :=
          hnd 0 (i + 1) (by simp only [List.length_cons]; omega)
            (by simp only [List.length_cons]; omega) (h0.trans h1.symm)
        omega
      · intro i j hi hj heq
        have hlen : (a :: t).length = t.length + 1 := rfl
        have hcon : i + 1 = j + 1 :=
          hnd (i + 1) (j + 1) (by rw [hlen]; omega) (by rw [hlen]; omega)
            (by rw [List.getElem?_cons_succ, List.getElem?_cons_succ]; exact heq)
        omega

/-- The 52 cards are distinct (index-wise, over the factored product). -/
theorem universe_noDup : noDupCards Card.universe := by
  intro i j hi hj heq
  rw [Card.universe_length] at hi hj
  have hall : ∀ i ∈ List.range 52, ∀ j ∈ List.range 52,
      Card.universe[i]? = Card.universe[j]? → i = j := by decide
  exact hall i (List.mem_range.mpr hi) j (List.mem_range.mpr hj) heq

theorem universe_nodupP : NoDupP Card.universe :=
  noDupCards_NoDupP universe_noDup

/-- Filters of distinct lists stay distinct. -/
theorem nodupP_filter (p : Card → Bool) : ∀ {l : List Card}, NoDupP l → NoDupP (l.filter p) := by
  intro l
  induction l with
  | nil => intro _; trivial
  | cons a t ih =>
      intro hnd
      obtain ⟨ha, hndt⟩ := hnd
      by_cases hpa : p a = true
      · rw [List.filter_cons, if_pos hpa]
        exact ⟨fun hmem => ha (List.mem_filter.mp hmem).1, ih hndt⟩
      · rw [List.filter_cons, if_neg hpa]
        exact ih hndt

/-- **The bijection count**: two distinct lists with mutual inverse
maps between them have equal lengths (peel one side's head from the
other side's middle, induct). -/
theorem length_eq_of_bijection (f g : Card → Card) :
    ∀ (l₁ l₂ : List Card), NoDupP l₁ → NoDupP l₂ →
    (∀ x, x ∈ l₁ → f x ∈ l₂ ∧ g (f x) = x) →
    (∀ y, y ∈ l₂ → g y ∈ l₁ ∧ f (g y) = y) →
    l₁.length = l₂.length := by
  intro l₁
  induction l₁ with
  | nil =>
      intro l₂ _ hnd₂ _ h2
      cases l₂ with
      | nil => rfl
      | cons b t₂ =>
          obtain ⟨hgb, -⟩ := h2 b (by simp)
          exact absurd hgb (by simp)
  | cons a t ih =>
      intro l₂ hnd₁ hnd₂ h1 h2
      obtain ⟨ha, hndt⟩ := hnd₁
      obtain ⟨hfa, hgfa⟩ := h1 a (by simp)
      obtain ⟨pre, post, hsplit⟩ := mem_middle_split l₂ hfa
      have hnd₂' : NoDupP (pre ++ post) :=
        nodupP_remove _ _ _ (by rw [← hsplit]; exact hnd₂)
      have hfa' : f a ∉ pre ++ post :=
        nodupP_sub _ _ _ (by rw [← hsplit]; exact hnd₂)
      have hmem1 : ∀ x, x ∈ t → f x ∈ pre ++ post ∧ g (f x) = x := by
        intro x hx
        obtain ⟨hfx, hgfx⟩ := h1 x (List.mem_cons_of_mem a hx)
        refine ⟨?_, hgfx⟩
        have hne : f x ≠ f a := by
          intro hcon
          have hxa : x = a := by rw [← hgfx, ← hgfa, hcon]
          exact ha (hxa ▸ hx)
        have hfx2 : f x ∈ pre ++ f a :: post := by rw [← hsplit]; exact hfx
        rcases List.mem_append.mp hfx2 with h | h
        · exact List.mem_append.mpr (Or.inl h)
        · rcases List.mem_cons.mp h with h' | h'
          · exact absurd h' hne
          · exact List.mem_append.mpr (Or.inr h')
      have hmem2 : ∀ y, y ∈ pre ++ post → g y ∈ t ∧ f (g y) = y := by
        intro y hy
        have hy2 : y ∈ l₂ := by
          rw [hsplit]
          rcases List.mem_append.mp hy with h | h
          · exact List.mem_append.mpr (Or.inl h)
          · exact List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inr h)))
        obtain ⟨hgy, hfgy⟩ := h2 y hy2
        refine ⟨?_, hfgy⟩
        rcases List.mem_cons.mp hgy with h | h
        · exfalso
          have hyfa : y = f a := by rw [← hfgy, ← h]
          rw [hyfa] at hy
          exact hfa' hy
        · exact h
      have hrec := ih (pre ++ post) hndt hnd₂' hmem1 hmem2
      rw [hsplit]
      simp only [List.length_cons, List.length_append] at hrec ⊢
      omega

/-! ## The allDistinct kit -/

/-- No repeated elements, index-wise. -/
def allDistinct {α : Type} (l : List α) : Prop :=
  ∀ i j : Nat, i < l.length → j < l.length → l[i]? = l[j]? → i = j

/-- The head can be re-attached. -/
theorem allDistinct_cons {α : Type} {x : α} {t : List α}
    (h1 : x ∉ t) (h2 : allDistinct t) : allDistinct (x :: t) := by
  intro i j hi hj heq
  cases i with
  | zero =>
      cases j with
      | zero => rfl
      | succ k =>
          rw [List.getElem?_cons_zero, List.getElem?_cons_succ] at heq
          exact absurd (List.mem_iff_getElem?.mpr ⟨k, heq.symm⟩) h1
  | succ k =>
      cases j with
      | zero =>
          rw [List.getElem?_cons_zero, List.getElem?_cons_succ] at heq
          exact absurd (List.mem_iff_getElem?.mpr ⟨k, heq⟩) h1
      | succ k' =>
          rw [List.getElem?_cons_succ, List.getElem?_cons_succ] at heq
          have := h2 k k'
            (by simp only [List.length_cons] at hi; omega)
            (by simp only [List.length_cons] at hj; omega) heq
          omega

/-- The tail of a distinct list is distinct. -/
theorem allDistinct_cons_tail {α : Type} {x : α} {t : List α}
    (h : allDistinct (x :: t)) : allDistinct t := by
  intro i j hi hj heq
  have heq' : (x :: t)[i + 1]? = (x :: t)[j + 1]? := by
    rw [List.getElem?_cons_succ, List.getElem?_cons_succ]
    exact heq
  have := h (i + 1) (j + 1)
    (by simp only [List.length_cons]; omega)
    (by simp only [List.length_cons]; omega) heq'
  omega

/-- A distinct list's head is not in its tail. -/
theorem allDistinct_cons_notMem {α : Type} {x : α} {t : List α}
    (h : allDistinct (x :: t)) : x ∉ t := by
  intro hm
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hm
  have hb : j < t.length := (List.getElem?_eq_some_iff.mp hj).1
  have heq : (x :: t)[0]? = (x :: t)[j + 1]? := by
    rw [List.getElem?_cons_zero, List.getElem?_cons_succ]
    exact hj.symm
  have := h 0 (j + 1) (by simp)
    (by simp only [List.length_cons]; omega) heq
  omega

/-- Distinctness of the right summand. -/
theorem allDistinct_append_right {α : Type} {A B : List α}
    (h : allDistinct (A ++ B)) : allDistinct B := by
  intro i j hi hj heq
  have hb : (A ++ B).length = A.length + B.length := List.length_append
  have heq' : (A ++ B)[A.length + i]? = (A ++ B)[A.length + j]? := by
    rw [List.getElem?_append_right (by omega), List.getElem?_append_right (by omega)]
    rw [Nat.add_sub_cancel_left, Nat.add_sub_cancel_left]
    exact heq
  have := h (A.length + i) (A.length + j) (by omega) (by omega) heq'
  omega

/-- **The pigeonhole**: a distinct list contained in `t` is at most as
long as `t`. -/
theorem pigeonhole_le {α : Type} : ∀ (l t : List α), allDistinct l →
    (∀ x ∈ l, x ∈ t) → l.length ≤ t.length := by
  intro l
  induction l with
  | nil => intro t _ _; exact Nat.zero_le _
  | cons x l' ih =>
      intro t hdist hsub
      obtain ⟨t₁, t₂, hsplit⟩ := mem_split t x (hsub x (by simp))
      have hxnl : x ∉ l' := allDistinct_cons_notMem hdist
      have hsub' : ∀ y ∈ l', y ∈ t₁ ++ t₂ := by
        intro y hy
        have hyt : y ∈ t := hsub y (by simp [hy])
        rw [hsplit] at hyt
        rcases List.mem_append.mp hyt with h | h
        · exact List.mem_append_left _ h
        · rcases List.mem_cons.mp h with h' | h'
          · exact absurd (by rw [← h']; exact hy) hxnl
          · exact List.mem_append_right _ h'
      have hih := ih (t₁ ++ t₂) (allDistinct_cons_tail hdist) hsub'
      have hlen : t.length = t₁.length + 1 + t₂.length := by
        rw [hsplit, List.length_append, List.length_cons]
        omega
      have hla : (t₁ ++ t₂).length = t₁.length + t₂.length := List.length_append
      simp only [List.length_cons]
      omega

/-- Distinct naturals below `n` number at most `n`. -/
theorem distinct_nat_count_le (l : List Nat) (n : Nat) (hdist : allDistinct l)
    (hlt : ∀ x ∈ l, x < n) : l.length ≤ n := by
  have h := pigeonhole_le l (List.range n) hdist
    (fun x hx => List.mem_range.mpr (hlt x hx))
  rw [List.length_range] at h
  exact h

/-- Distinctness survives filtering. -/
theorem allDistinct_filter {α : Type} (p : α → Bool) : ∀ (l : List α),
    allDistinct l → allDistinct (l.filter p) := by
  intro l
  induction l with
  | nil => intro _; intro i j hi _ _; simp at hi
  | cons a t ih =>
      intro h
      by_cases hp : p a = true
      · rw [List.filter_cons, if_pos hp]
        refine allDistinct_cons ?_ (ih (allDistinct_cons_tail h))
        intro hm
        exact allDistinct_cons_notMem h (List.mem_filter.mp hm).1
      · rw [List.filter_cons, if_neg hp]
        exact ih (allDistinct_cons_tail h)

/-- The map of a distinct list under an injective-on-it function is
distinct. -/
theorem allDistinct_map {α β : Type} (f : α → β) {l : List α} (hd : allDistinct l)
    (hinj : ∀ x ∈ l, ∀ y ∈ l, f x = f y → x = y) : allDistinct (l.map f) := by
  intro i j hi hj heq
  have hl : (l.map f).length = l.length := List.length_map f
  rw [List.getElem?_map, List.getElem?_map] at heq
  cases h1 : l[i]? with
  | none =>
      rw [List.getElem?_eq_none_iff] at h1
      omega
  | some x =>
      cases h2 : l[j]? with
      | none =>
          rw [List.getElem?_eq_none_iff] at h2
          omega
      | some y =>
          rw [h1, h2, Option.map_some, Option.map_some, Option.some.injEq] at heq
          have hx : x ∈ l := List.mem_iff_getElem?.mpr ⟨i, h1⟩
          have hy : y ∈ l := List.mem_iff_getElem?.mpr ⟨j, h2⟩
          have hxy : x = y := hinj x hx y hy heq
          have hget : l[i]? = l[j]? := by
            rw [h1, hxy]
            exact h2.symm
          exact hd i j (by omega) (by omega) hget

/-! ## Filter lemmas -/

/-- A noDup list is its own membership filter (order included). -/
theorem filter_mem_idem : ∀ (l : List Card), noDupCards l →
    l = l.filter (fun x => decide (x ∈ l)) := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons a t ih =>
      intro hnd
      have hnot : a ∉ t := allDistinct_cons_notMem hnd
      rw [List.filter_cons, if_pos (decide_eq_true (by simp))]
      refine congrArg (a :: ·) ?_
      refine Eq.trans (ih (allDistinct_cons_tail hnd)) ?_
      exact (List.filter_congr (fun x hx => by
        by_cases hxa : x = a
        · exact absurd (by rw [← hxa]; exact hx) hnot
        · simp [List.mem_cons, hxa])).symm

/-- A filter of the list is the membership filter of itself. -/
theorem filter_mem_self {orig cur : List Card} {p : Card → Bool}
    (h : cur = orig.filter p) : cur = orig.filter (fun x => decide (x ∈ cur)) := by
  subst h
  refine List.filter_congr (fun x hx => ?_)
  cases hxp : p x with
  | true =>
      exact (decide_eq_true (List.mem_filter.mpr ⟨hx, hxp⟩)).symm
  | false =>
      exact (decide_eq_false (fun hmem =>
        Bool.noConfusion (hxp.symm.trans (List.mem_filter.mp hmem).2))).symm

/-- The filter split: a filtered length is its `q`-part plus its
`¬q`-part. -/
theorem filter_split_add (p q : Card → Bool) : ∀ (l : List Card),
    (l.filter p).length =
      (l.filter fun x => p x && q x).length + (l.filter fun x => p x && !q x).length := by
  intro l
  induction l with
  | nil => rfl
  | cons a t ih =>
      cases hpa : p a with
      | true =>
          have e1 : (a :: t).filter p = a :: t.filter p := by
            rw [List.filter_cons, if_pos hpa]
          cases hqa : q a with
          | true =>
              have e2 : (a :: t).filter (fun x => p x && q x)
                  = a :: t.filter (fun x => p x && q x) := by
                rw [List.filter_cons, if_pos (by simp [hpa, hqa])]
              have e3 : (a :: t).filter (fun x => p x && !q x)
                  = t.filter (fun x => p x && !q x) := by
                rw [List.filter_cons, if_neg (by simp [hpa, hqa])]
              rw [e1, e2, e3, List.length_cons, List.length_cons]
              omega
          | false =>
              have e2 : (a :: t).filter (fun x => p x && q x)
                  = t.filter (fun x => p x && q x) := by
                rw [List.filter_cons, if_neg (by simp [hpa, hqa])]
              have e3 : (a :: t).filter (fun x => p x && !q x)
                  = a :: t.filter (fun x => p x && !q x) := by
                rw [List.filter_cons, if_pos (by simp [hpa, hqa])]
              rw [e1, e2, e3, List.length_cons, List.length_cons]
              omega
      | false =>
          have e1 : (a :: t).filter p = t.filter p := by
            rw [List.filter_cons, if_neg (by simp [hpa])]
          have e2 : (a :: t).filter (fun x => p x && q x)
              = t.filter (fun x => p x && q x) := by
            rw [List.filter_cons, if_neg (by simp [hpa])]
          have e3 : (a :: t).filter (fun x => p x && !q x)
              = t.filter (fun x => p x && !q x) := by
            rw [List.filter_cons, if_neg (by simp [hpa])]
          rw [e1, e2, e3]
          omega

/-- A filter of always-false is empty. -/
theorem filter_len_zero (p : Card → Bool) : ∀ (l : List Card),
    (∀ x, x ∈ l → p x = false) → (l.filter p).length = 0 := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons a t ih =>
      intro h
      rw [List.filter_cons, if_neg (by simp [h a (by simp)])]
      exact ih (fun x hx => h x (by simp [hx]))

/-! ## The splice kit -/

namespace Cycle

/-- Splicing out index `i` shifts later indices down by one. -/
theorem getElem?_removeIdx {α : Type} :
    ∀ (l : List α) (i j : Nat),
      (removeIdx l i)[j]? = if j < i then l[j]? else l[j + 1]? := by
  intro l
  induction l with
  | nil =>
    intro i j
    simp only [removeIdx_nil, List.getElem?_nil]
    split <;> rfl
  | cons a t ih =>
    intro i
    cases i with
    | zero =>
      intro j
      simp only [removeIdx_zero, List.getElem?_cons_succ]
      rw [if_neg (Nat.not_lt_zero j)]
    | succ n =>
      intro j
      cases j with
      | zero =>
        simp only [removeIdx_succ, List.getElem?_cons_zero]
        rw [if_pos (Nat.zero_lt_succ n)]
      | succ m =>
        simp only [removeIdx_succ, List.getElem?_cons_succ]
        by_cases hm : m < n
        · rw [if_pos (by omega : m + 1 < n + 1)]
          exact (ih n m).trans (if_pos hm)
        · rw [if_neg (by omega : ¬(m + 1 < n + 1))]
          exact (ih n m).trans (if_neg hm)

end Cycle

/-- Splicing never lengthens. -/
theorem removeIdx_length_le {α : Type} : ∀ (l : List α) (i : Nat),
    (Cycle.removeIdx l i).length ≤ l.length := by
  intro l
  induction l with
  | nil => intro i; simp
  | cons a t ih =>
    intro i
    cases i with
    | zero => simp
    | succ n =>
      simp only [Cycle.removeIdx, List.length_cons]
      have := ih n
      omega

/-- Splicing out-of-range is the identity. -/
theorem removeIdx_of_length_le {α : Type} : ∀ (l : List α) (i : Nat),
    l.length ≤ i → Cycle.removeIdx l i = l := by
  intro l
  induction l with
  | nil => intro i _; rfl
  | cons a t ih =>
    intro i hi
    cases i with
    | zero => simp at hi
    | succ n =>
      simp only [Cycle.removeIdx, List.length_cons] at hi ⊢
      rw [ih n (by omega)]

/-- Splicing preserves index-wise distinctness. -/
theorem noDupCards_removeIdx : ∀ (l : List Card) (i : Nat),
    noDupCards l → noDupCards (Cycle.removeIdx l i) := by
  intro l
  induction l with
  | nil => intro i _ j j' hj _ _; simp at hj
  | cons a t ih =>
    intro i hnd j j' hj hj' heq
    have h1 := Cycle.getElem?_removeIdx (a :: t) i j
    have h2 := Cycle.getElem?_removeIdx (a :: t) i j'
    rw [h1, h2] at heq
    by_cases hic : i < (a :: t).length
    · have hbl : (Cycle.removeIdx (a :: t) i).length + 1 = (a :: t).length :=
        Cycle.removeIdx_length _ i hic
      by_cases hc1 : j < i
      · by_cases hc2 : j' < i
        · rw [if_pos hc1, if_pos hc2] at heq
          have := hnd j j' (by omega) (by omega) heq
          omega
        · rw [if_pos hc1, if_neg hc2] at heq
          have := hnd j (j' + 1) (by omega) (by omega) heq
          omega
      · by_cases hc2 : j' < i
        · rw [if_neg hc1, if_pos hc2] at heq
          have := hnd (j + 1) j' (by omega) (by omega) heq
          omega
        · rw [if_neg hc1, if_neg hc2] at heq
          have := hnd (j + 1) (j' + 1) (by omega) (by omega) heq
          omega
    · have hle : Cycle.removeIdx (a :: t) i = (a :: t) :=
        removeIdx_of_length_le _ i (by omega)
      rw [hle] at hj hj'
      by_cases hc1 : j < i
      · by_cases hc2 : j' < i
        · rw [if_pos hc1, if_pos hc2] at heq
          have := hnd j j' (by omega) (by omega) heq
          omega
        · rw [if_pos hc1, if_neg hc2] at heq
          have := hnd j (j' + 1) (by omega) (by omega) heq
          omega
      · by_cases hc2 : j' < i
        · rw [if_neg hc1, if_pos hc2] at heq
          have := hnd (j + 1) j' (by omega) (by omega) heq
          omega
        · rw [if_neg hc1, if_neg hc2] at heq
          have := hnd (j + 1) (j' + 1) (by omega) (by omega) heq
          omega

/-- Splicing out an index keeps exactly the remaining members, in
order. -/
theorem removeIdx_filter_mem : ∀ (l : List Card) (i : Nat), noDupCards l →
    Cycle.removeIdx l i = l.filter (fun x => decide (x ∈ Cycle.removeIdx l i)) := by
  intro l
  induction l with
  | nil => intro i _; rfl
  | cons a t ih =>
      intro i hnd
      have hnot : a ∉ t := allDistinct_cons_notMem hnd
      have hdt := allDistinct_cons_tail hnd
      cases i with
      | zero =>
          show t = (a :: t).filter (fun x => decide (x ∈ t))
          rw [List.filter_cons, if_neg (by simp [hnot])]
          exact filter_mem_idem t hdt
      | succ j =>
          show a :: Cycle.removeIdx t j
            = (a :: t).filter (fun x => decide (x ∈ a :: Cycle.removeIdx t j))
          rw [List.filter_cons, if_pos (decide_eq_true (by simp))]
          refine congrArg (a :: ·) ?_
          refine Eq.trans (ih j hdt) ?_
          exact (List.filter_congr (fun x hx => by
            by_cases hxa : x = a
            · exact absurd (by rw [← hxa]; exact hx) hnot
            · simp [List.mem_cons, hxa])).symm

/-! ## The radix encoding -/

/-- Little-endian radix value of `f` over `l`. -/
def encF (r : Nat) {α : Type} (l : List α) (f : α → Nat) : Nat :=
  (l.map f).foldr (fun x acc => x + r * acc) 0

theorem radix_peel {a a' r b b' : Nat} (hr : 0 < r) (ha : a < r) (ha' : a' < r)
    (h : a + r * b = a' + r * b') : a = a' ∧ b = b' := by
  have hm : (a + r * b) % r = (a' + r * b') % r := congrArg (fun k => k % r) h
  rw [Nat.add_mul_mod_self_left, Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt ha'] at hm
  refine ⟨hm, ?_⟩
  rw [hm] at h
  exact Nat.eq_of_mul_eq_mul_left hr (Nat.add_left_cancel h)

theorem nest_lt {a r b R : Nat} (ha : a < r) (hb : b < R) :
    a + r * b < r * R := by
  have h1 : a + r * b < r + r * b := Nat.add_lt_add_right ha _
  have h2 : r + r * b = r * (1 + b) := by rw [Nat.mul_add, Nat.mul_one]
  calc a + r * b < r + r * b := h1
    _ = r * (1 + b) := h2
    _ ≤ r * R := Nat.mul_le_mul (Nat.le_refl r) (by omega)

theorem encF_inj {α : Type} (r : Nat) (hr : 0 < r) : ∀ (l : List α) (f g : α → Nat),
    (∀ x ∈ l, f x < r) → (∀ x ∈ l, g x < r) →
    encF r l f = encF r l g → ∀ x ∈ l, f x = g x := by
  intro l
  induction l with
  | nil => intro f g _ _ _ x hx; cases hx
  | cons a t ih =>
      intro f g hf hg h x hx
      have hstep : f a + r * encF r t f = g a + r * encF r t g := h
      obtain ⟨ha, hrest⟩ := radix_peel hr (hf a (by simp)) (hg a (by simp)) hstep
      rcases List.mem_cons.mp hx with rfl | hxt
      · exact ha
      · exact ih f g (fun y hy => hf y (by simp [hy]))
          (fun y hy => hg y (by simp [hy])) hrest x hxt

theorem encF_lt {α : Type} (r : Nat) : ∀ (l : List α) (f : α → Nat),
    (∀ x ∈ l, f x < r) → encF r l f < r ^ l.length := by
  intro l
  induction l with
  | nil => intro f _; exact Nat.zero_lt_one
  | cons a t ih =>
      intro f hf
      have h1 := hf a (by simp)
      have h2 := ih f (fun y hy => hf y (by simp [hy]))
      show f a + r * encF r t f < r ^ (t.length + 1)
      rw [Nat.pow_add, Nat.pow_one]
      calc f a + r * encF r t f < r * r ^ t.length := nest_lt h1 h2
        _ = r ^ t.length * r := Nat.mul_comm _ _



