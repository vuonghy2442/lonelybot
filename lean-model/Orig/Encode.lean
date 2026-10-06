import Orig.Fate

/-!
# Orig — the encoding kit: distinctness, counting, the state code

The bounded-play spine's arithmetic floor, in three layers:

* the generic list kit — index-wise distinctness (`allDistinct`), the
  pigeonhole it feeds, `getElem?`-style list algebra, and list
  extensionality by `getElem?`;
* the counting kit — occurrences of one card in a list, a zone's
  slice of the flat zone multiset, and the pigeonhole a second time:
  at a `WF` state every zone holds every card at most once, so every
  zone has at most 52 cards;
* the code — a mixed-radix encoding of a position.  Each zone (four
  foundations, seven piles' hidden cards, their face-up runs, the
  stock, the waste) is written into a fixed 52-slot window as one
  53-valued digit per slot (the card's code plus one, `0` for an
  unused slot); the twenty windows plus the draw step fold into one
  number.  `stateEnc` is injective on `WF` states (each zone is
  literally re-read off its window) and bounded by `stateSpaceBound`
  — the pigeonhole input of the bounded-play decidability.

The radix algebra (`encF`, `radix_peel`, `nest_lt`) is the classic
little-endian peel kit.  Nothing here mentions moves or plays; the
chapter is consumed by `Orig.Progress`.
-/

set_option maxRecDepth 2048
set_option maxHeartbeats 1000000

/-! ## List algebra -/

/-- Powers of a positive base are positive. -/
theorem nat_pow_pos {b n : Nat} (hb : 0 < b) : 0 < b ^ n := by
  induction n with
  | zero => exact Nat.zero_lt_one
  | succ k ih => rw [Nat.pow_succ]; exact Nat.mul_pos ih hb

/-- Two lists with the same entry at every index are equal. -/
theorem list_ext_getElem? {α : Type} :
    ∀ {l₁ l₂ : List α}, (∀ i : Nat, l₁[i]? = l₂[i]?) → l₁ = l₂ := by
  intro l₁
  induction l₁ with
  | nil =>
      intro l₂ h
      cases l₂ with
      | nil => rfl
      | cons x t =>
          have h0 : none = some x := h 0
          exact absurd h0 (by simp)
  | cons x t ih =>
      intro l₂ h
      cases l₂ with
      | nil =>
          have h0 : some x = none := h 0
          exact absurd h0 (by simp)
      | cons y r =>
          have hxy : x = y := by
            have := h 0
            simp only [List.getElem?_cons_zero, Option.some.injEq] at this
            exact this
          have hrest : t = r := ih fun i => by
            have := h (i + 1)
            simpa only [List.getElem?_cons_succ] using this
          subst hrest
          rw [hxy]

/-- The length of `List.range`. -/
theorem range_len (n : Nat) : (List.range n).length = n := by
  induction n with
  | zero => rfl
  | succ k ih =>
      rw [List.range_succ, List.length_append, ih]
      simp only [List.length_cons, List.length_nil]

/-- A prefix index addresses the left summand. -/
theorem getElem?_appendL {α : Type} :
    ∀ (xs ys : List α) (i : Nat), i < xs.length → (xs ++ ys)[i]? = xs[i]? := by
  intro xs
  induction xs with
  | nil => intro ys i h; simp at h
  | cons x t ih =>
      intro ys i h
      cases i with
      | zero => rfl
      | succ k =>
          have hk : k < t.length := by
            simp only [List.length_cons] at h
            omega
          simpa only [List.cons_append, List.getElem?_cons_succ] using ih ys k hk

/-- A past-the-prefix index addresses the right summand. -/
theorem getElem?_appendR {α : Type} :
    ∀ (xs ys : List α) (i : Nat), xs.length ≤ i →
      (xs ++ ys)[i]? = ys[i - xs.length]? := by
  intro xs
  induction xs with
  | nil =>
      intro ys i _h
      simp only [List.length_nil, Nat.sub_zero]
      rfl
  | cons x t ih =>
      intro ys i h
      cases i with
      | zero => simp at h
      | succ k =>
          have hk : t.length ≤ k := by
            simp only [List.length_cons] at h
            omega
          have hcut := ih ys k hk
          have hsub : k + 1 - (x :: t).length = k - t.length := by
            simp only [List.length_cons, Nat.succ_sub_succ]
          show (x :: (t ++ ys))[k + 1]? = ys[k + 1 - (x :: t).length]?
          rw [List.getElem?_cons_succ, hsub]
          exact hcut

/-- The entry of a mapped list. -/
theorem list_map_getElem? {α β : Type} (f : α → β) :
    ∀ (l : List α) (i : Nat), (l.map f)[i]? = (l[i]?).map f := by
  intro l
  induction l with
  | nil => intro i; rfl
  | cons x t ih =>
      intro i
      cases i with
      | zero => rfl
      | succ k => simpa only [List.map_cons, List.getElem?_cons_succ] using ih k

/-- An index inside the list carries an entry. -/
theorem getElem?_some_of_lt {α : Type} : ∀ {l : List α} {i : Nat}, i < l.length →
    ∃ x : α, l[i]? = some x := by
  intro l
  induction l with
  | nil => intro i hi; simp at hi
  | cons x t ih =>
      intro i hi
      cases i with
      | zero => exact ⟨x, rfl⟩
      | succ k =>
          have hk : k < t.length := by
            simp only [List.length_cons] at hi
            omega
          obtain ⟨y, hy⟩ := ih hk
          exact ⟨y, by rw [List.getElem?_cons_succ, hy]⟩

/-! ## The allDistinct kit -/

/-- No repeated elements, index-wise. -/
def allDistinct {α : Type} (l : List α) : Prop :=
  ∀ i j : Nat, i < l.length → j < l.length → l[i]? = l[j]? → i = j

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
          have hik : k < t.length := by
            simp only [List.length_cons] at hi
            omega
          have hjk : k' < t.length := by
            simp only [List.length_cons] at hj
            omega
          have := h2 k k' hik hjk heq
          omega

/-- The tail of a distinct list is distinct. -/
theorem allDistinct_cons_tail {α : Type} {x : α} {t : List α}
    (h : allDistinct (x :: t)) : allDistinct t := by
  intro i j hi hj heq
  have heq' : (x :: t)[i + 1]? = (x :: t)[j + 1]? := by
    rw [List.getElem?_cons_succ, List.getElem?_cons_succ]
    exact heq
  have hi1 : i + 1 < (x :: t).length := by
    simp only [List.length_cons]
    omega
  have hj1 : j + 1 < (x :: t).length := by
    simp only [List.length_cons]
    omega
  have := h (i + 1) (j + 1) hi1 hj1 heq'
  omega

/-- A distinct list's head is not in its tail. -/
theorem allDistinct_cons_notMem {α : Type} {x : α} {t : List α}
    (h : allDistinct (x :: t)) : x ∉ t := by
  intro hm
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hm
  obtain ⟨hb, -⟩ := (List.getElem?_eq_some_iff (l := t) (i := j) (a := x)).mp hj
  have heq : (x :: t)[0]? = (x :: t)[j + 1]? := by
    rw [List.getElem?_cons_zero, List.getElem?_cons_succ]
    exact hj.symm
  have := h 0 (j + 1) (by simp)
    (by simp only [List.length_cons]; omega) heq
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
      simp only [List.length_cons]
      have hlen : t.length = t₁.length + 1 + t₂.length := by
        rw [hsplit, List.length_append, List.length_cons]
        omega
      have hla : (t₁ ++ t₂).length = t₁.length + t₂.length := List.length_append
      omega

/-- Distinct naturals below `n` number at most `n`. -/
theorem distinct_nat_count_le (l : List Nat) (n : Nat) (hdist : allDistinct l)
    (hlt : ∀ x ∈ l, x < n) : l.length ≤ n := by
  have h := pigeonhole_le l (List.range n) hdist
    (fun x hx => List.mem_range.mpr (hlt x hx))
  rw [range_len] at h
  exact h

/-- The map of a distinct list under an injective-on-it function is
distinct. -/
theorem allDistinct_map {α β : Type} (f : α → β) {l : List α} (hd : allDistinct l)
    (hinj : ∀ x ∈ l, ∀ y ∈ l, f x = f y → x = y) : allDistinct (l.map f) := by
  intro i j hi hj heq
  have hl : (l.map f).length = l.length := List.length_map f
  rw [list_map_getElem?, list_map_getElem?] at heq
  cases h1 : l[i]? with
  | none =>
      have hge := (List.getElem?_eq_none_iff (l := l) (i := i)).mp h1
      omega
  | some x =>
      cases h2 : l[j]? with
      | none =>
          have hge := (List.getElem?_eq_none_iff (l := l) (i := j)).mp h2
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

/-! ## Occurrence counting -/

/-- How many times `c` occurs in `l`. -/
def listCount (l : List Card) (c : Card) : Nat :=
  (l.filter fun x => decide (x = c)).length

theorem listCount_append (l₁ l₂ : List Card) (c : Card) :
    listCount (l₁ ++ l₂) c = listCount l₁ c + listCount l₂ c := by
  simp only [listCount, List.filter_append, List.length_append]

theorem listCount_reverse (l : List Card) (c : Card) :
    listCount l.reverse c = listCount l c := by
  simp only [listCount, List.filter_reverse, List.length_reverse]

theorem listCount_ge_one_of_mem {l : List Card} {c : Card} (h : c ∈ l) :
    1 ≤ listCount l c := by
  have hmem : c ∈ l.filter fun x => decide (x = c) :=
    List.mem_filter.mpr ⟨h, decide_eq_true rfl⟩
  obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hmem
  obtain ⟨hb, -⟩ :=
    (List.getElem?_eq_some_iff
      (l := l.filter fun x => decide (x = c)) (i := k) (a := c)).mp hk
  simp only [listCount]
  omega

/-- A list with the value at two positions holds it at least twice:
once in the `take`, once in the `drop`. -/
theorem listCount_ge_two_of_two_gets {l : List Card} {x : Card} {i j : Nat}
    (hij : i < j) (_hi : i < l.length) (_hj : j < l.length)
    (gi : l[i]? = some x) (gj : l[j]? = some x) :
    2 ≤ listCount l x := by
  have htl : (l.take j)[i]? = some x := by
    rw [List.getElem?_take]
    split
    · next hlt => exact gi
    · next _ => omega
  have hdr : (l.drop j)[0]? = some x := by
    rw [List.getElem?_drop, Nat.add_zero]
    exact gj
  have hmem1 : x ∈ l.take j := List.mem_iff_getElem?.mpr ⟨i, htl⟩
  have hmem2 : x ∈ l.drop j := List.mem_iff_getElem?.mpr ⟨0, hdr⟩
  have hsplit : listCount l x = listCount (l.take j) x + listCount (l.drop j) x := by
    rw [← listCount_append, List.take_append_drop]
  have h1 := listCount_ge_one_of_mem hmem1
  have h2 := listCount_ge_one_of_mem hmem2
  omega

/-- One flatMap cons step. -/
theorem flatMap_cons_eq {α β : Type} (f : α → List β) (x : α) (t : List α) :
    (x :: t).flatMap f = f x ++ t.flatMap f := by
  induction t generalizing x with
  | nil => simp
  | cons y r ih => simp [ih]

/-! ## Zone counting at `WF` states -/

/-- The card census is the occurrence count of the flat zone list. -/
theorem cardCount_eq_listCount (st : State) (c : Card) :
    st.cardCount c = listCount (st.zones.flatMap id) c :=
  rfl

/-- A member zone splits the flat census. -/
theorem zone_slice_count {zs : List (List Card)} {z : List Card}
    (hmem : z ∈ zs) (c : Card) :
    ∃ a b, listCount (zs.flatMap id) c = a + listCount z c + b := by
  obtain ⟨pre, post, hsplit⟩ := mem_split zs z hmem
  have hid : (id z : List Card) = z := rfl
  have hflat : (pre ++ z :: post).flatMap id = pre.flatMap id ++ (id z ++ post.flatMap id) := by
    rw [List.flatMap_append, flatMap_cons_eq]
  refine ⟨listCount (pre.flatMap id) c, listCount (post.flatMap id) c, ?_⟩
  rw [hsplit, hflat, hid, listCount_append, listCount_append]
  omega

/-- Every card of a member zone meets the census head-on. -/
theorem listCount_zone_le_cardCount {st : State} {z : List Card}
    (hmem : z ∈ st.zones) (c : Card) :
    listCount z c ≤ st.cardCount c := by
  rw [cardCount_eq_listCount]
  obtain ⟨a, b, hsplit⟩ := zone_slice_count hmem c
  omega

/-- A `WF` zone holds every card at most once. -/
theorem wf_zone_distinct {st : State} (hwf : st.WF) {z : List Card}
    (hmem : z ∈ st.zones) : allDistinct z := by
  intro i j hi hj heq
  cases hlt : z[i]? with
  | none =>
      have hge := (List.getElem?_eq_none_iff (l := z) (i := i)).mp hlt
      omega
  | some x =>
      cases hrt : z[j]? with
      | none =>
          have hge := (List.getElem?_eq_none_iff (l := z) (i := j)).mp hrt
          omega
      | some y =>
          have hxy : y = x :=
            Option.some.inj (hrt.symm.trans (heq.symm.trans hlt))
          have hone : listCount z x ≤ 1 := by
            have h0 := listCount_zone_le_cardCount hmem x
            have h1 := hwf.2.2.1 x (Card.mem_universe x)
            omega
          cases Nat.lt_or_ge i j with
          | inl hlt2 =>
              have gj : z[j]? = some x := by rw [hrt, hxy]
              have htwo := listCount_ge_two_of_two_gets hlt2 hi hj hlt gj
              exact absurd htwo (by omega)
          | inr hge2 =>
              rcases Nat.eq_or_lt_of_le hge2 with rfl | hlt2
              · rfl
              · have gj : z[j]? = some x := by rw [hrt, hxy]
                have htwo := listCount_ge_two_of_two_gets hlt2 hj hi gj hlt
                exact absurd htwo (by omega)

/-- **The zone bound**: at a `WF` state every zone has at most 52
cards — its cards are distinct and all belong to the universe. -/
theorem wf_zone_le {st : State} (hwf : st.WF) :
    ∀ z ∈ st.zones, z.length ≤ 52 := by
  intro z hmem
  exact pigeonhole_le z Card.universe (wf_zone_distinct hwf hmem)
    (fun x _ => Card.mem_universe x)

/-- Zone membership, each zone by name — the zone list is
`(founds ++ pile joints) ++ [stock, waste]`. -/
theorem found_mem_zones (st : State) (s : Suit) : st.found s ∈ st.zones := by
  have h1 : st.found s ∈ Suit.all.map st.found :=
    List.mem_map_of_mem (Suit.mem_all s)
  exact List.mem_append_left _ (List.mem_append_left _ h1)

/-- A pile's whole zone (hidden below face-up) is one census zone. -/
theorem pileJoint_mem_zones (st : State) (a : Anchor) :
    (st.piles a).hidden ++ (st.piles a).faceUp ∈ st.zones := by
  have hmap : (st.piles a).hidden ++ (st.piles a).faceUp ∈
      Anchor.all.map (fun a' => (st.piles a').hidden ++ (st.piles a').faceUp) :=
    List.mem_map_of_mem (Anchor.mem_all a)
  exact List.mem_append_left _ (List.mem_append_right _ hmap)

theorem stock_mem_zones (st : State) : st.stock ∈ st.zones := by
  have h1 : st.stock ∈ [st.stock, st.waste] := List.mem_cons.mpr (Or.inl rfl)
  exact List.mem_append_right _ h1

theorem waste_mem_zones (st : State) : st.waste ∈ st.zones := by
  have h1 : st.waste ∈ [st.stock, st.waste] :=
    List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))
  exact List.mem_append_right _ h1

/-- A pile's halves each stay within the joint zone bound. -/
theorem wf_hidden_le {st : State} (hwf : st.WF) (a : Anchor) :
    (st.piles a).hidden.length ≤ 52 := by
  have hjoint := wf_zone_le hwf _ (pileJoint_mem_zones st a)
  have hlen : ((st.piles a).hidden ++ (st.piles a).faceUp).length
      = (st.piles a).hidden.length + (st.piles a).faceUp.length :=
    List.length_append
  omega

theorem wf_faceUp_le {st : State} (hwf : st.WF) (a : Anchor) :
    (st.piles a).faceUp.length ≤ 52 := by
  have hjoint := wf_zone_le hwf _ (pileJoint_mem_zones st a)
  have hlen : ((st.piles a).hidden ++ (st.piles a).faceUp).length
      = (st.piles a).hidden.length + (st.piles a).faceUp.length :=
    List.length_append
  omega

/-! ## The radix kit -/

/-- Little-endian radix value of `f` over `l`. -/
def encF (r : Nat) {α : Type} (l : List α) (f : α → Nat) : Nat :=
  (l.map f).foldr (fun x acc => x + r * acc) 0

/-- Peel one little-endian digit off an equality. -/
theorem radix_peel {a a' r b b' : Nat} (hr : 0 < r) (ha : a < r) (ha' : a' < r)
    (h : a + r * b = a' + r * b') : a = a' ∧ b = b' := by
  have hm : (a + r * b) % r = (a' + r * b') % r := congrArg (fun k => k % r) h
  rw [Nat.add_mul_mod_self_left, Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt ha'] at hm
  refine ⟨hm, ?_⟩
  rw [hm] at h
  exact Nat.eq_of_mul_eq_mul_left hr (Nat.add_left_cancel h)

/-- Nest one radix bound. -/
theorem nest_lt {a r b R : Nat} (ha : a < r) (hb : b < R) :
    a + r * b < r * R := by
  have h1 : a + r * b < r + r * b := Nat.add_lt_add_right ha _
  have h2 : r + r * b = r * (1 + b) := by rw [Nat.mul_add, Nat.mul_one]
  calc a + r * b < r + r * b := h1
    _ = r * (1 + b) := h2
    _ ≤ r * R := Nat.mul_le_mul (Nat.le_refl r) (by omega)

/-- Equal radix values agree digit-wise. -/
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

/-- The radix value of digits below `r` is below `r ^ n`. -/
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

/-! ## Card digits -/

/-- The suit's numeric view (0..3). -/
def suitCode (s : Suit) : Nat :=
  match s with
  | .spade => 0
  | .heart => 1
  | .diamond => 2
  | .club => 3

theorem suitCode_lt (s : Suit) : suitCode s < 4 := by
  cases s <;> decide

theorem suitCode_inj {s s' : Suit} (h : suitCode s = suitCode s') : s = s' := by
  cases s <;> cases s' <;> simp_all [suitCode]

/-- The card's numeric view (0..51), injective. -/
def cardCode (c : Card) : Nat := c.rank.toIdx + 13 * suitCode c.suit

theorem cardCode_lt (c : Card) : cardCode c < 52 := by
  rcases c with ⟨s, r⟩
  have h1 := Rank.toIdx_lt r
  have h2 := suitCode_lt s
  show r.toIdx + 13 * suitCode s < 52
  omega

theorem cardCode_inj {c c' : Card} (h : cardCode c = cardCode c') : c = c' := by
  rcases c with ⟨s, r⟩
  rcases c' with ⟨s', r'⟩
  have h1 := Rank.toIdx_lt r
  have h2 := Rank.toIdx_lt r'
  have h3 : r.toIdx + 13 * suitCode s = r'.toIdx + 13 * suitCode s' := h
  have hs : suitCode s = suitCode s' := by omega
  have hr : r.toIdx = r'.toIdx := by omega
  rw [Card.mk.injEq]
  exact ⟨suitCode_inj hs, Rank.toIdx_inj hr⟩

/-! ## The padded window -/

/-- The list's `i`-th slot: `0` for unused, the card's code plus one
otherwise. -/
def winDigit (l : List Card) (i : Nat) : Nat :=
  match l[i]? with
  | some c => 1 + cardCode c
  | none => 0

theorem winDigit_lt (l : List Card) (i : Nat) : winDigit l i < 53 := by
  unfold winDigit
  cases h : l[i]? with
  | none => decide
  | some c =>
      have := cardCode_lt c
      show 1 + cardCode c < 53
      omega

theorem winDigit_of_get {l : List Card} {i : Nat} {c : Card}
    (h : l[i]? = some c) : winDigit l i = 1 + cardCode c := by
  rw [winDigit, h]

theorem winDigit_eq_zero {l : List Card} {i : Nat}
    (h : l[i]? = none) : winDigit l i = 0 := by
  rw [winDigit, h]

/-- The fixed-width window code of a list of at most 52 cards. -/
def padEnc (l : List Card) : Nat := encF 53 (List.range 52) (winDigit l)

theorem padEnc_lt (l : List Card) : padEnc l < 53 ^ 52 := by
  have h := encF_lt 53 (List.range 52) (winDigit l)
    (fun i _ => winDigit_lt l i)
  rw [range_len] at h
  exact h

/-- **Window reconstructability**: a list of at most 52 cards is
re-read off its window. -/
theorem padEnc_inj {l₁ l₂ : List Card} (h1 : l₁.length ≤ 52) (h2 : l₂.length ≤ 52)
    (h : padEnc l₁ = padEnc l₂) : l₁ = l₂ := by
  have hdigits : ∀ i ∈ List.range 52, winDigit l₁ i = winDigit l₂ i :=
    encF_inj 53 (by decide) (List.range 52) (winDigit l₁) (winDigit l₂)
      (fun i _ => winDigit_lt l₁ i) (fun i _ => winDigit_lt l₂ i) h
  refine list_ext_getElem? fun i => ?_
  cases Nat.lt_or_ge i 52 with
  | inl hi52 =>
      have hd := hdigits i (List.mem_range.mpr hi52)
      cases g1 : l₁[i]? with
      | none =>
          rw [winDigit_eq_zero g1] at hd
          cases g2 : l₂[i]? with
          | none => rfl
          | some c =>
              have hcc := cardCode_lt c
              rw [winDigit_of_get g2] at hd
              omega
      | some c =>
          rw [winDigit_of_get g1] at hd
          cases g2 : l₂[i]? with
          | none =>
              rw [winDigit_eq_zero g2] at hd
              simp at hd
          | some c' =>
              have hcc : 1 + cardCode c = 1 + cardCode c' := by
                rw [winDigit_of_get g2] at hd
                exact hd
              have hccq : c = c' := cardCode_inj (Nat.add_left_cancel hcc)
              exact congrArg some hccq
  | inr hi52 =>
      have hnone1 : l₁[i]? = none :=
        (List.getElem?_eq_none_iff (l := l₁) (i := i)).mpr (by omega)
      have hnone2 : l₂[i]? = none :=
        (List.getElem?_eq_none_iff (l := l₂) (i := i)).mpr (by omega)
      rw [hnone1, hnone2]

/-! ## The state code -/

/-- The suit's window index. -/
def suitIdx (s : Suit) : Nat :=
  match s with
  | .spade => 0
  | .heart => 1
  | .diamond => 2
  | .club => 3

theorem suit_all_get (s : Suit) : Suit.all[suitIdx s]? = some s := by
  cases s <;> rfl

/-- A member of a window map is below the window radix. -/
theorem mem_mapPad_lt {l : List (List Card)} {d : Nat}
    (h : d ∈ l.map padEnc) :
    d < 53 ^ 52 := by
  cases l with
  | nil => cases h
  | cons x t =>
      rcases List.mem_cons.mp h with hd | hd
      · rw [hd]
        exact padEnc_lt x
      · have hd' : d ∈ t.map padEnc := hd
        exact mem_mapPad_lt hd'

theorem suitIdx_lt (s : Suit) : suitIdx s < 4 := by cases s <;> decide

/-- The anchor's window index. -/
def anchorIdx (a : Anchor) : Nat :=
  match a with
  | .p0 => 0 | .p1 => 1 | .p2 => 2 | .p3 => 3 | .p4 => 4 | .p5 => 5 | .p6 => 6

theorem anchor_all_get (a : Anchor) : Anchor.all[anchorIdx a]? = some a := by
  cases a <;> rfl

theorem anchorIdx_lt (a : Anchor) : anchorIdx a < 7 := by cases a <;> decide

theorem suit_all_length : Suit.all.length = 4 := by decide
theorem anchor_all_length : Anchor.all.length = 7 := by decide

namespace State

/-- The radix of one window: one 53-valued digit per slot, fifty-two
slots (`(53 ^ 52)`, kept as a name so the code stays symbolic). -/
def winRad : Nat := 53 ^ 52

theorem winRad_pos : 0 < winRad := nat_pow_pos (by decide)

/-- The four foundations' windows. -/
def foundWindows (st : State) : List Nat :=
  (Suit.all.map st.found).map padEnc

/-- The seven hidden piles' windows. -/
def hiddenWindows (st : State) : List Nat :=
  (Anchor.all.map (fun a => (st.piles a).hidden)).map padEnc

/-- The seven face-up runs' windows. -/
def faceUpWindows (st : State) : List Nat :=
  (Anchor.all.map (fun a => (st.piles a).faceUp)).map padEnc

/-- The twenty zone windows, in a fixed left-nested order. -/
def zoneWindows (st : State) : List Nat :=
  st.foundWindows ++ st.hiddenWindows ++ st.faceUpWindows ++
    [padEnc st.stock, padEnc st.waste]

theorem foundWindows_length (st : State) : st.foundWindows.length = 4 := by
  simp only [foundWindows, List.length_map, suit_all_length]
theorem hiddenWindows_length (st : State) : st.hiddenWindows.length = 7 := by
  simp only [hiddenWindows, List.length_map, anchor_all_length]
theorem faceUpWindows_length (st : State) : st.faceUpWindows.length = 7 := by
  simp only [faceUpWindows, List.length_map, anchor_all_length]

theorem zones9_length (st : State) :
    ((st.foundWindows ++ st.hiddenWindows) ++ st.faceUpWindows).length = 18 := by
  rw [List.length_append, List.length_append, foundWindows_length,
    hiddenWindows_length, faceUpWindows_length]

theorem zoneWindows_length (st : State) : st.zoneWindows.length = 20 := by
  show (((st.foundWindows ++ st.hiddenWindows) ++ st.faceUpWindows) ++
      [padEnc st.stock, padEnc st.waste]).length = 20
  rw [List.length_append, zones9_length, List.length_cons, List.length_cons,
    List.length_nil]

/-- Shared cuts, packaged once: the three window groups' lengths. -/
theorem foundWin_len (st : State) : st.foundWindows.length = 4 :=
  foundWindows_length st

theorem hiddenWin_len (st : State) : st.hiddenWindows.length = 7 :=
  hiddenWindows_length st

theorem faceUpWin_len (st : State) : st.faceUpWindows.length = 7 :=
  faceUpWindows_length st

theorem nineWin_len (st : State) :
    (st.foundWindows ++ st.hiddenWindows).length = 11 := by
  rw [List.length_append, foundWin_len, hiddenWin_len]

theorem eighteenWin_len (st : State) :
    ((st.foundWindows ++ st.hiddenWindows) ++ st.faceUpWindows).length = 18 := by
  rw [List.length_append, nineWin_len, faceUpWin_len]

/-! ### The twenty slot addresses -/

/-- A foundation's slot: `0..3`. -/
theorem zoneWindows_found (st : State) (s : Suit) :
    st.zoneWindows[suitIdx s]? = some (padEnc (st.found s)) := by
  simp only [zoneWindows]
  have hu := suitIdx_lt s
  have hb18 : suitIdx s < ((st.foundWindows ++ st.hiddenWindows) ++ st.faceUpWindows).length := by
    rw [eighteenWin_len]; omega
  have hb11 : suitIdx s < (st.foundWindows ++ st.hiddenWindows).length := by
    rw [nineWin_len]; omega
  have hb4 : suitIdx s < st.foundWindows.length := by
    rw [foundWin_len]; omega
  have cut1 :
      ((((st.foundWindows ++ st.hiddenWindows) ++ st.faceUpWindows) ++
        [padEnc st.stock, padEnc st.waste])[suitIdx s]?
      = ((st.foundWindows ++ st.hiddenWindows) ++ st.faceUpWindows)[suitIdx s]?) :=
    getElem?_appendL _ _ _ hb18
  have cut2 :
      (((st.foundWindows ++ st.hiddenWindows) ++ st.faceUpWindows)[suitIdx s]?
      = (st.foundWindows ++ st.hiddenWindows)[suitIdx s]?) :=
    getElem?_appendL _ _ _ hb11
  have cut3 :
      ((st.foundWindows ++ st.hiddenWindows)[suitIdx s]? = st.foundWindows[suitIdx s]?) :=
    getElem?_appendL _ _ _ hb4
  rw [cut1, cut2, cut3]
  simp only [foundWindows]
  rw [list_map_getElem?, list_map_getElem?, suit_all_get s, Option.map_some,
    Option.map_some]

/-- A hidden pile's slot: `4..10`. -/
theorem zoneWindows_hidden (st : State) (a : Anchor) :
    st.zoneWindows[4 + anchorIdx a]? = some (padEnc (st.piles a).hidden) := by
  simp only [zoneWindows]
  have hu := anchorIdx_lt a
  have hb18 : 4 + anchorIdx a < ((st.foundWindows ++ st.hiddenWindows) ++ st.faceUpWindows).length := by
    rw [eighteenWin_len]; omega
  have hb11 : 4 + anchorIdx a < (st.foundWindows ++ st.hiddenWindows).length := by
    rw [nineWin_len]; omega
  have hbR : st.foundWindows.length ≤ 4 + anchorIdx a := by
    rw [foundWin_len]; omega
  have cut1 :
      ((((st.foundWindows ++ st.hiddenWindows) ++ st.faceUpWindows) ++
        [padEnc st.stock, padEnc st.waste])[4 + anchorIdx a]?
      = ((st.foundWindows ++ st.hiddenWindows) ++ st.faceUpWindows)[4 + anchorIdx a]?) :=
    getElem?_appendL _ _ _ hb18
  have cut2 :
      (((st.foundWindows ++ st.hiddenWindows) ++ st.faceUpWindows)[4 + anchorIdx a]?
      = (st.foundWindows ++ st.hiddenWindows)[4 + anchorIdx a]?) :=
    getElem?_appendL _ _ _ hb11
  have cut3 :
      ((st.foundWindows ++ st.hiddenWindows)[4 + anchorIdx a]?
      = st.hiddenWindows[4 + anchorIdx a - st.foundWindows.length]?) :=
    getElem?_appendR _ _ _ hbR
  rw [cut1, cut2, cut3, foundWin_len,
    show 4 + anchorIdx a - 4 = anchorIdx a from by omega]
  simp only [hiddenWindows]
  rw [list_map_getElem?, list_map_getElem?, anchor_all_get a, Option.map_some,
    Option.map_some]

/-- A face-up run's slot: `11..17`. -/
theorem zoneWindows_faceUp (st : State) (a : Anchor) :
    st.zoneWindows[11 + anchorIdx a]? = some (padEnc (st.piles a).faceUp) := by
  simp only [zoneWindows]
  have hu := anchorIdx_lt a
  have hb18 : 11 + anchorIdx a < ((st.foundWindows ++ st.hiddenWindows) ++ st.faceUpWindows).length := by
    rw [eighteenWin_len]; omega
  have hbR : (st.foundWindows ++ st.hiddenWindows).length ≤ 11 + anchorIdx a := by
    rw [nineWin_len]; omega
  have cut1 :
      ((((st.foundWindows ++ st.hiddenWindows) ++ st.faceUpWindows) ++
        [padEnc st.stock, padEnc st.waste])[11 + anchorIdx a]?
      = ((st.foundWindows ++ st.hiddenWindows) ++ st.faceUpWindows)[11 + anchorIdx a]?) :=
    getElem?_appendL _ _ _ hb18
  have cut2 :
      (((st.foundWindows ++ st.hiddenWindows) ++ st.faceUpWindows)[11 + anchorIdx a]?
      = st.faceUpWindows[11 + anchorIdx a - (st.foundWindows ++ st.hiddenWindows).length]?) :=
    getElem?_appendR _ _ _ hbR
  rw [cut1, cut2, nineWin_len,
    show 11 + anchorIdx a - 11 = anchorIdx a from by omega]
  simp only [faceUpWindows]
  rw [list_map_getElem?, list_map_getElem?, anchor_all_get a, Option.map_some,
    Option.map_some]

/-- The stock's slot: `18`. -/
theorem zoneWindows_stock (st : State) :
    st.zoneWindows[18]? = some (padEnc st.stock) := by
  simp only [zoneWindows]
  have hbR : ((st.foundWindows ++ st.hiddenWindows) ++ st.faceUpWindows).length ≤ 18 := by
    rw [eighteenWin_len]; omega
  have cut1 :
      ((((st.foundWindows ++ st.hiddenWindows) ++ st.faceUpWindows) ++
        [padEnc st.stock, padEnc st.waste])[18]?
      = ([padEnc st.stock, padEnc st.waste])[18 - ((st.foundWindows ++ st.hiddenWindows) ++ st.faceUpWindows).length]?) :=
    getElem?_appendR _ _ _ hbR
  have hidx : 18 - ((st.foundWindows ++ st.hiddenWindows) ++ st.faceUpWindows).length = 0 := by
    rw [eighteenWin_len]
  rw [cut1, hidx]
  rfl

/-- The waste's slot: `19`. -/
theorem zoneWindows_waste (st : State) :
    st.zoneWindows[19]? = some (padEnc st.waste) := by
  simp only [zoneWindows]
  have hbR : ((st.foundWindows ++ st.hiddenWindows) ++ st.faceUpWindows).length ≤ 19 := by
    rw [eighteenWin_len]; omega
  have cut1 :
      ((((st.foundWindows ++ st.hiddenWindows) ++ st.faceUpWindows) ++
        [padEnc st.stock, padEnc st.waste])[19]?
      = ([padEnc st.stock, padEnc st.waste])[19 - ((st.foundWindows ++ st.hiddenWindows) ++ st.faceUpWindows).length]?) :=
    getElem?_appendR _ _ _ hbR
  have hidx : 19 - ((st.foundWindows ++ st.hiddenWindows) ++ st.faceUpWindows).length = 1 := by
    rw [eighteenWin_len]
  rw [cut1, hidx]
  rfl

/-- Every window member is below the window radix. -/
theorem zoneWindows_mem_lt {st : State} : ∀ d ∈ st.zoneWindows, d < winRad := by
  intro d hd
  have hu : d ∈ (st.foundWindows ++ st.hiddenWindows) ++ st.faceUpWindows ++
      [padEnc st.stock, padEnc st.waste] := hd
  rcases List.mem_append.mp hu with hd | hd
  · rcases List.mem_append.mp hd with hd | hd
    · rcases List.mem_append.mp hd with hd | hd
      · exact mem_mapPad_lt hd
      · exact mem_mapPad_lt hd
    · exact mem_mapPad_lt hd
  · rcases List.mem_cons.mp hd with hd | hd
    · rw [hd]
      exact padEnc_lt _
    · have hde : d = padEnc st.waste := List.mem_singleton.mp hd
      rw [hde]
      exact padEnc_lt _

/-- The digit at slot `i` of the state's twenty windows (`0` off the
end). -/
def windowDigit (st : State) (i : Nat) : Nat :=
  match st.zoneWindows[i]? with
  | some d => d
  | none => 0

theorem windowDigit_of_get {st : State} {i : Nat} {d : Nat}
    (h : st.zoneWindows[i]? = some d) : windowDigit st i = d := by
  rw [windowDigit, h]

theorem windowDigit_eq_zero {st : State} {i : Nat}
    (h : st.zoneWindows[i]? = none) : windowDigit st i = 0 := by
  rw [windowDigit, h]

/-- Every window digit sits below the window radix. -/
theorem windowDigit_lt (st : State) (i : Nat) (_hi : i < 20) :
    windowDigit st i < winRad := by
  cases h : st.zoneWindows[i]? with
  | none =>
      rw [windowDigit_eq_zero h]
      exact winRad_pos
  | some d =>
      have hmem : d ∈ st.zoneWindows := List.mem_iff_getElem?.mpr ⟨i, h⟩
      have hd := zoneWindows_mem_lt d hmem
      rw [windowDigit_of_get h]
      exact hd

/-- The twenty windows folded little-endian stay below the twentieth
power of the window radix. -/
theorem stateEncStep_lt (st : State) :
    encF winRad (List.range 20) (windowDigit st) < winRad ^ 20 := by
  have h := encF_lt winRad (List.range 20) (windowDigit st)
    (fun i hi => windowDigit_lt st i (List.mem_range.mp hi))
  rw [range_len] at h
  exact h

/-- The explicit pigeonhole bound: twenty window radices plus one
draw-step digit.  Since `winRad` is `53 ^ 52` the bound is exactly
`53 ^ (52 * 20 + 1) = 53 ^ 1041`.  Astronomical; any finite bound
would do. -/
def stateSpaceBound : Nat := winRad ^ 20 * 53

/-- The state's code: the twenty windows plus the draw step. -/
def stateEnc (st : State) : Nat :=
  encF winRad (List.range 20) (windowDigit st) + winRad ^ 20 * st.drawStep

theorem stateEnc_lt {st : State} (hwf : st.WF) :
    st.stateEnc < stateSpaceBound := by
  have hstep := stateEncStep_lt st
  have hdraw : st.drawStep < 4 := by
    rcases hwf.2.2.2 with h | h
    · rw [h]; decide
    · rw [h]; decide
  unfold stateEnc stateSpaceBound
  have hnest : encF winRad (List.range 20) (windowDigit st)
      + winRad ^ 20 * st.drawStep < winRad ^ 20 * 4 :=
    nest_lt hstep hdraw
  have hpow : winRad ^ 20 * 4 ≤ winRad ^ 20 * 53 := Nat.mul_le_mul_left _ (by decide)
  calc encF winRad (List.range 20) (windowDigit st) + winRad ^ 20 * st.drawStep
        < winRad ^ 20 * 4 := hnest
    _ ≤ winRad ^ 20 * 53 := hpow

/-- The nat-indexed injectivity read, with the twenty-slot carrier
fixed: digit bounds below the radix give digit-wise equality. -/
theorem encF_inj_nat (f g : Nat → Nat)
    (hf : ∀ i, i < 20 → f i < winRad) (hg : ∀ i, i < 20 → g i < winRad)
    (h : encF winRad (List.range 20) f = encF winRad (List.range 20) g) :
    ∀ i, i < 20 → f i = g i := by
  have hgen := encF_inj winRad winRad_pos (List.range 20) f g
    (fun i hi => hf i (List.mem_range.mp hi))
    (fun i hi => hg i (List.mem_range.mp hi)) h
  intro i hi
  exact hgen i (List.mem_range.mpr hi)

/-- **Code reconstructability**: at `WF` states the code determines the
position — every zone is re-read off its window, the draw step off
its digit. -/
theorem stateEnc_inj {s₁ s₂ : State} (h₁ : s₁.WF) (h₂ : s₂.WF)
    (h : s₁.stateEnc = s₂.stateEnc) : s₁ = s₂ := by
  obtain ⟨hstep, hdg⟩ :=
    radix_peel (r := winRad ^ 20) (nat_pow_pos winRad_pos)
      (stateEncStep_lt s₁) (stateEncStep_lt s₂) (by unfold stateEnc at *; exact h)
  have hdigits : ∀ i, i < 20 → windowDigit s₁ i = windowDigit s₂ i :=
    encF_inj_nat (windowDigit s₁) (windowDigit s₂)
      (fun i hi => windowDigit_lt s₁ i hi)
      (fun i hi => windowDigit_lt s₂ i hi) hstep
  -- the slot readings agree, zone by zone
  have hfound : ∀ s, padEnc (s₁.found s) = padEnc (s₂.found s) := by
    intro s
    have g1 := zoneWindows_found s₁ s
    have g2 := zoneWindows_found s₂ s
    rw [← windowDigit_of_get g1, ← windowDigit_of_get g2]
    exact hdigits (suitIdx s) (by cases s <;> decide)
  have hhidden : ∀ a, padEnc (s₁.piles a).hidden = padEnc (s₂.piles a).hidden := by
    intro a
    have g1 := zoneWindows_hidden s₁ a
    have g2 := zoneWindows_hidden s₂ a
    rw [← windowDigit_of_get g1, ← windowDigit_of_get g2]
    exact hdigits (4 + anchorIdx a) (by cases a <;> decide)
  have hfaceUp : ∀ a, padEnc (s₁.piles a).faceUp = padEnc (s₂.piles a).faceUp := by
    intro a
    have g1 := zoneWindows_faceUp s₁ a
    have g2 := zoneWindows_faceUp s₂ a
    rw [← windowDigit_of_get g1, ← windowDigit_of_get g2]
    exact hdigits (11 + anchorIdx a) (by cases a <;> decide)
  have hstock : padEnc s₁.stock = padEnc s₂.stock := by
    have g1 := zoneWindows_stock s₁
    have g2 := zoneWindows_stock s₂
    rw [← windowDigit_of_get g1, ← windowDigit_of_get g2]
    exact hdigits 18 (by decide)
  have hwaste : padEnc s₁.waste = padEnc s₂.waste := by
    have g1 := zoneWindows_waste s₁
    have g2 := zoneWindows_waste s₂
    rw [← windowDigit_of_get g1, ← windowDigit_of_get g2]
    exact hdigits 19 (by decide)
  -- window reconstructability, zone by zone
  have hfoundz : s₁.found = s₂.found := by
    funext s
    exact padEnc_inj
      (wf_zone_le h₁ _ (found_mem_zones s₁ s))
      (wf_zone_le h₂ _ (found_mem_zones s₂ s)) (hfound s)
  have hhiddenz : ∀ a, (s₁.piles a).hidden = (s₂.piles a).hidden := fun a =>
    padEnc_inj
      (wf_hidden_le h₁ a) (wf_hidden_le h₂ a) (hhidden a)
  have hfaceUpz : ∀ a, (s₁.piles a).faceUp = (s₂.piles a).faceUp := fun a =>
    padEnc_inj
      (wf_faceUp_le h₁ a) (wf_faceUp_le h₂ a) (hfaceUp a)
  have hstockz : s₁.stock = s₂.stock :=
    padEnc_inj (wf_zone_le h₁ _ (stock_mem_zones s₁))
      (wf_zone_le h₂ _ (stock_mem_zones s₂)) hstock
  have hwastez : s₁.waste = s₂.waste :=
    padEnc_inj (wf_zone_le h₁ _ (waste_mem_zones s₁))
      (wf_zone_le h₂ _ (waste_mem_zones s₂)) hwaste
  have hpiles : s₁.piles = s₂.piles := by
    funext a
    have hhh := hhiddenz a
    have hff := hfaceUpz a
    show Pile.mk (s₁.piles a).hidden (s₁.piles a).faceUp
      = Pile.mk (s₂.piles a).hidden (s₂.piles a).faceUp
    rw [hhh, hff]
  show State.mk s₁.found s₁.piles s₁.stock s₁.waste s₁.drawStep
    = State.mk s₂.found s₂.piles s₂.stock s₂.waste s₂.drawStep
  rw [hfoundz, hpiles, hstockz, hwastez, hdg]
end State
