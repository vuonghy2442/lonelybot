import Orig.Twin

/-!# Orig — the local twin exchangeThe *local* twin exchange, the second symmetry of the tableau and thegenerator of the accommodation family this program is about: twoface-up twin hosts — `t` and `Card.twin t` — sitting in two *distinct*piles have their strictly-above suffixes swapped.A pile's face-up run splits at a twin host as `P₁ ++ t :: S`; theexchange re-agglutinates the joints, `P₁ ++ t :: S'` on one side and`P₂ ++ t.twin :: S` on the other.
  The prefix through each host isuntouched — the hosts keep their piles through their own exchange —and only the suffixes ride.
  The fit rules are already twin-blind onthe right (`canSitOn_twin_right`), so the two re-made joints arelegal wherever the old ones were.The kit:* `aboveIn` — the suffix strictly above a card;
  `below_aboveIn_split` — the decomposition of any face-up run at
  one of its cards;* `State.exchangeTwin` — the total exchange: locate the two hosts by
  `State.pileHolding` *at the argument state* (the hosts are read
  dynamically, wherever they now sit), swap the suffixes when both
  are face-up in distinct piles, and fall back to the identity in
  every other shape;* the structural exports — `State.exchangeTwin_pair`,
  `State.exchangeTwin_eq_of_located`, the pile characterizations,
  `State.exchangeTwin_eq_self_of_both_bare`,
  `State.exchangeTwin_invol`, and the search-stability facts
  (`State.exchangeTwin_hosts_stable`) that let later chapters
  re-anchor hosts after intermediate play;* the hygiene transfer — runOK and `cardCount` through the exchange,
  `State.wf_exchangeTwin`, `State.isWin_exchangeTwin`;* the region exports for the replay engine: the slot identities
  (`State.exchangeTwin_aboveIn_self` and mirror) and
  `State.exchangeTwin_region_unique` — regional uniqueness (each
  twin, each suffix card counted once, confined to its slots)
  survives the exchange;* `twin_exchange_bare_iff` — the first migrated theorem: at the
  *one-bare-twin* shape (at least one host bare), the exchange
  preserves the verdict.
  Both directions are one-move
  realizations: the cargo rides onto the bare host as a plain
  `Move.tabToTab`, and rides back the same way.The both-occupied row (both suffixes nonempty) is deliberately NOTattacked here; it belongs to a later mirroring engine, and thischapter's characterizations are its substrate.-/

/-! ## The above-suffix and the split -/

/-- The cards strictly above the first `t` of `l` — the part of theface-up run that rides in `fromCard`, detached from its host. -/
def aboveIn (t : Card) (l : List Card) : List Card := (fromCard t l).tail
theorem below_cons_self (t : Card) (xs : List Card) : below t (t :: xs) = [] := by
  rw [below, ite_eq_left rfl]
theorem below_cons_ne {t x : Card} (xs : List Card) (h : x ≠ t) :
    below t (x :: xs) = x :: below t xs := by
  rw [below, ite_eq_right h]
theorem fromCard_cons_self (t : Card) (xs : List Card) : fromCard t (t :: xs) = t :: xs := by
  rw [fromCard, ite_eq_left rfl]
theorem fromCard_cons_ne {t x : Card} (xs : List Card) (h : x ≠ t) :
    fromCard t (x :: xs) = fromCard t xs := by
  rw [fromCard, ite_eq_right h]
theorem aboveIn_cons_self (t : Card) (xs : List Card) : aboveIn t (t :: xs) = xs := by
  rw [aboveIn, fromCard_cons_self]
  rfl
theorem aboveIn_cons_ne {t x : Card} (xs : List Card) (h : x ≠ t) :
    aboveIn t (x :: xs) = aboveIn t xs := by
  rw [aboveIn, fromCard_cons_ne xs h, aboveIn]
theorem fromCard_eq_of_mem {t : Card} {l : List Card} (h : t ∈ l) :
    fromCard t l = t :: aboveIn t l := by
  have hhead : ∃ s, fromCard t l = t :: s := by
    induction l with
    | nil => cases h
    | cons x xs ih =>
        by_cases hx : x = t
        · subst hx
          exact ⟨xs, fromCard_cons_self _ xs⟩
        · have htx : t ∈ xs := (List.mem_cons.mp h).resolve_left (fun hc => hx hc.symm)
          rcases ih htx with ⟨s, hs⟩
          exact ⟨s, by rw [fromCard_cons_ne xs hx]; exact hs⟩
  rcases hhead with ⟨s, hs⟩
  unfold aboveIn
  rw [hs]
  exact congrArg (t :: ·) rfl

/-- The face-up split at a member card: below-prefix, host, and thesuffix strictly above. -/
theorem below_aboveIn_split {t : Card} {l : List Card} (h : t ∈ l) :
    l = below t l ++ t :: aboveIn t l := by
  induction l with
  | nil => cases h
  | cons x xs ih =>
      by_cases hx : x = t
      · subst hx
        rw [below_cons_self, aboveIn_cons_self, List.nil_append]
      · have htx : t ∈ xs := (List.mem_cons.mp h).resolve_left (fun hc => hx hc.symm)
        have ihL := ih htx
        rw [below_cons_ne xs hx, aboveIn_cons_ne xs hx, List.cons_append]
        exact congrArg (x :: ·) ihL

/-- A below-prefix never contains its own cut card. -/
theorem below_not_mem (t : Card) : ∀ l : List Card, t ∉ below t l
  | [] => by simp [below]
  | x :: xs => by
      intro hmem
      by_cases hx : x = t
      · subst hx
        rw [below_cons_self] at hmem
        cases hmem
      · rw [below_cons_ne xs hx] at hmem
        rcases List.mem_cons.mp hmem with heq | hxs
        · exact hx heq.symm
        · exact below_not_mem t xs hxs

/-- Walking an append whose head part does not contain the cut card:the below-prefix keeps the head part. -/
theorem below_append_notmem {t : Card} : ∀ {xs l : List Card}, t ∉ xs →
    below t (xs ++ l) = xs ++ below t l
  | [], _ => fun _ => rfl
  | x :: xs, l => fun h => by
      have hxt : x ≠ t := fun hc => h (List.mem_cons.mpr (Or.inl hc.symm))
      have hrest : t ∉ xs := fun hmemb => h (List.mem_cons.mpr (Or.inr hmemb))
      rw [List.cons_append, below_cons_ne _ hxt, below_append_notmem hrest]
      rfl

/-- Walking an append whose head part does not contain the target:`fromCard` starts in the tail. -/
theorem fromCard_append_notmem {t : Card} : ∀ {xs l : List Card}, t ∉ xs →
    fromCard t (xs ++ l) = fromCard t l
  | [], _ => fun _ => rfl
  | x :: xs, l => fun h => by
      have hxt : x ≠ t := fun hc => h (List.mem_cons.mpr (Or.inl hc.symm))
      have hrest : t ∉ xs := fun hmemb => h (List.mem_cons.mpr (Or.inr hmemb))
      rw [List.cons_append, fromCard_cons_ne _ hxt, fromCard_append_notmem hrest]

/-- Below stops exactly at the first occurrence of the cut card. -/
theorem below_append_stop {t : Card} {xs ys : List Card} (h : t ∉ xs) :
    below t (xs ++ t :: ys) = xs := by
  rw [below_append_notmem h, below_cons_self, List.append_nil]

/-- `fromCard` cuts exactly at the first occurrence. -/
theorem fromCard_append_stop {t : Card} {xs ys : List Card} (h : t ∉ xs) :
    fromCard t (xs ++ t :: ys) = t :: ys := by
  rw [fromCard_append_notmem h, fromCard_cons_self]
theorem below_subset_mem {t : Card} : ∀ {l : List Card} {x : Card},
    x ∈ below t l → x ∈ l
  | [], _ => by simp [below]
  | y :: ys, x => by
      by_cases hy : y = t
      · subst hy; rw [below_cons_self]; intro hm; cases hm
      · rw [below_cons_ne ys hy]
        intro hm
        rcases List.mem_cons.mp hm with h | h
        · exact h ▸ List.mem_cons_self ..
        · exact List.mem_cons_of_mem _ (below_subset_mem h)
theorem fromCard_subset_mem {t : Card} : ∀ {l : List Card} {x : Card},
    x ∈ fromCard t l → x ∈ l
  | [], _ => by simp [fromCard]
  | y :: ys, x => by
      by_cases hy : y = t
      · subst hy; rw [fromCard_cons_self]
        intro hm
        rcases List.mem_cons.mp hm with h | h
        · exact h ▸ List.mem_cons_self ..
        · exact List.mem_cons_of_mem _ h
      · rw [fromCard_cons_ne ys hy]
        intro hm
        exact List.mem_cons_of_mem _ (fromCard_subset_mem hm)
private theorem tail_mem {α : Type} {x : α} : ∀ {l : List α}, x ∈ l.tail → x ∈ l
  | [] => fun h => absurd h (by simp)
  | y :: ys => fun h => List.mem_cons_of_mem y h
theorem aboveIn_subset_mem {t : Card} {l : List Card} {x : Card}
    (h : x ∈ aboveIn t l) : x ∈ l := by
  have h' : x ∈ (fromCard t l).tail := h
  exact fromCard_subset_mem (tail_mem h')

/-! ## lastOf kit -/
private theorem lastOf_mem : ∀ {l : List Card} {x : Card},
    lastOf l = some x → x ∈ l
  | [], _, h => by simp [lastOf] at h
  | [y], _, h => by
      rw [lastOf] at h
      cases h
      exact List.mem_cons_self ..
  | y :: z :: zs, _, h => by
      rw [show lastOf (y :: z :: zs) = lastOf (z :: zs) from rfl] at h
      exact List.mem_cons_of_mem _ (lastOf_mem h)
private theorem lastOf_append_singleton : ∀ (l : List Card) (x : Card),
    lastOf (l ++ [x]) = some x
  | [], _ => rfl
  | [_], _ => rfl
  | _ :: z :: zs, x => lastOf_append_singleton (z :: zs) x

/-! ## runOK kit -/
theorem runOK_cons_cons (x y : Card) (t : List Card) :
    runOK (x :: y :: t) = (canSitOn y x && runOK (y :: t)) := rfl

/-- The exact legibility of a spliced run: the piece through thehost and the piece from the host. -/
theorem runOK_append_exact (x : Card) : ∀ (pre suf : List Card),
    runOK (pre ++ x :: suf) = true ↔
      (runOK (pre ++ [x]) = true ∧ runOK (x :: suf) = true) := by
  intro pre
  induction pre with
  | nil =>
      intro suf
      rw [List.nil_append, List.nil_append]
      rw [show runOK [x] = true from rfl]
      constructor
      · intro h
        exact ⟨rfl, h⟩
      · rintro ⟨_, h₂⟩
        exact h₂
  | cons y ys ih =>
      intro suf
      cases ys with
      | nil =>
          rw [List.cons_append, List.cons_append, List.nil_append, List.nil_append]
          rw [runOK_cons_cons, runOK_cons_cons]
          rw [show runOK [x] = true from rfl]
          rw [Bool.and_eq_true, Bool.and_eq_true]
          constructor
          · rintro ⟨h₁, h₂⟩
            exact ⟨⟨h₁, rfl⟩, h₂⟩
          · rintro ⟨⟨h₁, _⟩, h₂⟩
            exact ⟨h₁, h₂⟩
      | cons w ws =>
          have hL : runOK ((y :: w :: ws) ++ (x :: suf))
              = (canSitOn w y && runOK ((w :: ws) ++ (x :: suf))) := rfl
          have hR : runOK ((y :: w :: ws) ++ [x])
              = (canSitOn w y && runOK ((w :: ws) ++ [x])) := rfl
          rw [hL, hR, Bool.and_eq_true, Bool.and_eq_true, ih]
          constructor
          · rintro ⟨hA, hR', hC⟩
            exact ⟨⟨hA, hR'⟩, hC⟩
          · rintro ⟨⟨hA, hR'⟩, hC⟩
            exact ⟨hA, hR', hC⟩

/-- A host wrote its suffix-leg back: the joint under a spliced run. -/
theorem runOK_joint_of_splice {pre : List Card} {t z : Card} {rest : List Card}
    (h : runOK (pre ++ t :: z :: rest) = true) : canSitOn z t = true := by
  have h2 := ((runOK_append_exact t pre (z :: rest)).mp h).2
  rw [runOK_cons_cons, Bool.and_eq_true] at h2
  exact h2.1

/-! ## Search kit -/
private theorem firstWhere_none {α : Type} (p : α → Bool) : ∀ {l : List α},
    firstWhere p l = none → ∀ x ∈ l, p x = false := by
  intro l
  induction l with
  | nil => intro h x hx; cases hx
  | cons y t ih =>
      intro h x hx
      rw [firstWhere] at h
      cases hp : p y with
      | true =>
          rw [hp] at h
          exact absurd h (by simp)
      | false =>
          rw [hp] at h
          have hyf : p y = false := hp
          rcases List.mem_cons.mp hx with heq | hxt
          · rw [heq]; exact hyf
          · exact ih h x hxt
private theorem firstWhere_eq_of_unique {p : Anchor → Bool} {k : Anchor}
    (hmem : k ∈ Anchor.all) (hp : p k = true)
    (huni : ∀ j, p j = true → j = k) : firstWhere p Anchor.all = some k := by
  cases hf : firstWhere p Anchor.all with
  | none =>
      have hc := firstWhere_none p hf k hmem
      rw [hp] at hc
      exact absurd hc (by simp)
  | some m =>
      have hpm : p m = true := firstWhere_sound p hf
      exact congrArg some (huni m hpm)

/-- Reading a search result back: the holding pile's face-up containsthe card. -/
theorem pileHolding_mem {st : State} {c : Card} {a : Anchor}
    (h : st.pileHolding c = some a) : c ∈ (st.piles a).faceUp :=
  of_decide_eq_true (firstWhere_sound (p := fun a' => decide (c ∈ (st.piles a').faceUp)) h)

/-- Reading a top search back: the pile's face-up contains the card. -/
theorem pileOfTop_mem {st : State} {z : Card} {a : Anchor}
    (h : st.pileOfTop z = some a) : z ∈ (st.piles a).faceUp := by
  have h2 : st.topOf a = some z :=
    of_decide_eq_true (firstWhere_sound (p := fun a' => decide (st.topOf a' = some z)) h)
  exact lastOf_mem h2
private theorem pileHolding_eq_of_unique {st : State} {c : Card} {a : Anchor}
    (hmem : a ∈ Anchor.all) (hc : c ∈ (st.piles a).faceUp)
    (huni : ∀ j, c ∈ (st.piles j).faceUp → j = a) :
    st.pileHolding c = some a := by
  simp only [State.pileHolding]
  exact firstWhere_eq_of_unique hmem (by simp [hc]) (fun j hj => huni j (of_decide_eq_true hj))
private theorem pileOfTop_eq_of_unique {st : State} {z : Card} {a : Anchor}
    (hmem : a ∈ Anchor.all) (htop : st.topOf a = some z)
    (huni : ∀ j, st.topOf j = some z → j = a) :
    st.pileOfTop z = some a := by
  simp only [State.pileOfTop]
  exact firstWhere_eq_of_unique hmem (by simp [htop])
    (fun j hj => huni j (of_decide_eq_true hj))

/-! ## The count kit (private) -/
private def ccn (c : Card) (l : List Card) : Nat :=
  (l.filter fun x => decide (x = c)).length
private theorem ccn_split (c : Card) (xs ys : List Card) :
    ccn c (xs ++ ys) = ccn c xs + ccn c ys := by
  unfold ccn
  rw [List.filter_append, List.length_append]
private theorem ccn_cons (c x : Card) (l : List Card) :
    ccn c (x :: l) = ccn c [x] + ccn c l := ccn_split c [x] l
private theorem ccn_pos {c : Card} : ∀ {l : List Card}, c ∈ l → 1 ≤ ccn c l
  | [] => fun h => absurd h (by simp)
  | x :: xs => by
      intro hmem
      rcases List.mem_cons.mp hmem with heq | hxs
      · subst heq
        rw [ccn_cons]
        have h1 : 1 ≤ ccn c [c] := by simp [ccn]
        omega
      · have ih := ccn_pos hxs
        rw [ccn_cons]
        omega
private theorem ccn_rechunk {c x x' : Card} {ha hb hs ht : List Card}
    {S S' : List Card} :
    ccn c (ha ++ (hb ++ x :: S')) + ccn c (hs ++ (ht ++ x' :: S)) =
      ccn c (ha ++ (hb ++ x :: S)) + ccn c (hs ++ (ht ++ x' :: S')) := by
  rw [ccn_split c ha (hb ++ x :: S'), ccn_split c hs (ht ++ x' :: S),
      ccn_split c ha (hb ++ x :: S), ccn_split c hs (ht ++ x' :: S'),
      ccn_split c hb (x :: S'), ccn_split c ht (x' :: S),
      ccn_split c hb (x :: S), ccn_split c ht (x' :: S'),
      ccn_cons c x S', ccn_cons c x' S, ccn_cons c x S, ccn_cons c x' S']
  omega
private theorem flat_ccn_lower {zone : Anchor → List Card} {c : Card} :
    ∀ {l : List Anchor} {a : Anchor}, a ∈ l →
      ccn c (zone a) ≤ ccn c ((l.map zone).flatMap id)
  | [], a => fun h => by cases h
  | k :: t, a => by
      intro hmem
      have hsplit : ccn c (((k :: t).map zone).flatMap id)
          = ccn c (zone k) + ccn c ((t.map zone).flatMap id) := by
        rw [List.map_cons]
        rw [show List.flatMap id (zone k :: List.map zone t) =
              zone k ++ List.flatMap id (List.map zone t) from rfl]
        rw [ccn_split]
      rw [hsplit]
      rcases List.mem_cons.mp hmem with h | h
      · rw [h]
        omega
      · have ih := flat_ccn_lower (zone := zone) (c := c) (l := t) (a := a) h
        omega
private theorem flat_ccn_two {zone : Anchor → List Card} {c : Card} :
    ∀ {l : List Anchor} {a j : Anchor}, a ∈ l → j ∈ l → a ≠ j →
      ccn c (zone a) + ccn c (zone j) ≤ ccn c ((l.map zone).flatMap id) := by
  intro l
  induction l with
  | nil => intro a j ha; cases ha
  | cons k t ih =>
      intro a j ha hj hne
      have hsplit : ccn c (((k :: t).map zone).flatMap id)
          = ccn c (zone k) + ccn c ((t.map zone).flatMap id) := by
        rw [List.map_cons]
        rw [show List.flatMap id (zone k :: List.map zone t) =
              zone k ++ List.flatMap id (List.map zone t) from rfl]
        rw [ccn_split]
      rw [hsplit]
      by_cases hka : k = a
      · subst hka
        have hjt : j ∈ t := (List.mem_cons.mp hj).resolve_left (fun hc => hne hc.symm)
        have hlow := flat_ccn_lower (zone := zone) (c := c) (l := t) (a := j) hjt
        omega
      · by_cases hkj : k = j
        · subst hkj
          have hat : a ∈ t := (List.mem_cons.mp ha).resolve_left (fun hc => hne hc)
          have hlow := flat_ccn_lower (zone := zone) (c := c) (l := t) (a := a) hat
          omega
        · have hat : a ∈ t := (List.mem_cons.mp ha).resolve_left (fun hc => hka hc.symm)
          have hjt : j ∈ t := (List.mem_cons.mp hj).resolve_left (fun hc => hkj hc.symm)
          have hih := ih (a := a) (j := j) hat hjt hne
          omega

/-- flatMap of an append of card-lists: contents concatenate. -/
private theorem flat_id_append (xs ys : List (List Card)) :
    (xs ++ ys).flatMap id = xs.flatMap id ++ ys.flatMap id := by
  simp only [List.flatMap, List.map_append, List.flatten_append]

/-- The zones-list split of the total count. -/
private theorem cardCount_split_zones (st : State) (c : Card) :
    st.cardCount c =
      ccn c ((Suit.all.map st.found).flatMap id) +
      (ccn c ((Anchor.all.map
        (fun a => (st.piles a).hidden ++ (st.piles a).faceUp)).flatMap id) +
      ccn c ([st.stock, st.waste].flatMap id)) := by
  show ccn c ((st.zones).flatMap id) =
      ccn c ((Suit.all.map st.found).flatMap id) +
      (ccn c ((Anchor.all.map
        (fun a => (st.piles a).hidden ++ (st.piles a).faceUp)).flatMap id) +
      ccn c ([st.stock, st.waste].flatMap id))
  rw [State.zones]
  rw [flat_id_append, flat_id_append]
  rw [ccn_split, ccn_split]
  omega

/-- A zone count is bounded by the total. -/
private theorem cardCount_ge_of_zone {st : State} {c : Card} {a : Anchor} {n : Nat}
    (hmem : a ∈ Anchor.all)
    (h : n ≤ ccn c ((st.piles a).hidden ++ (st.piles a).faceUp)) :
    n ≤ st.cardCount c := by
  rw [cardCount_split_zones]
  have hmid := flat_ccn_lower (l := Anchor.all) (a := a) (c := c)
    (zone := fun j => (st.piles j).hidden ++ (st.piles j).faceUp) hmem
  have h0 : 0 ≤ ccn c ((Suit.all.map st.found).flatMap id) := Nat.zero_le _
  have h0' : 0 ≤ ccn c ([st.stock, st.waste].flatMap id) := Nat.zero_le _
  omega

/-- Two distinct face-up holdings would double the count. -/
theorem pile_mem_unique {st : State} {c : Card} (hcc : st.cardCount c = 1)
    {a j : Anchor} (ha : c ∈ (st.piles a).faceUp) (hj : c ∈ (st.piles j).faceUp) :
    a = j := by
  cases hde : decide (a = j) with
  | true => exact of_decide_eq_true hde
  | false =>
      exfalso
      have hne : a ≠ j := fun hcon => by
        have := decide_eq_true hcon
        rw [hde] at this
        exact absurd this (by simp)
      have hza : c ∈ (st.piles a).hidden ++ (st.piles a).faceUp :=
        List.mem_append.mpr (Or.inr ha)
      have hzj : c ∈ (st.piles j).hidden ++ (st.piles j).faceUp :=
        List.mem_append.mpr (Or.inr hj)
      have h2 : 2 ≤ st.cardCount c := by
        have hmid : 2 ≤ ccn c ((Anchor.all.map
            (fun j => (st.piles j).hidden ++ (st.piles j).faceUp)).flatMap id) := by
          have hboth := flat_ccn_two (l := Anchor.all) (a := a) (j := j) (c := c)
            (zone := fun j => (st.piles j).hidden ++ (st.piles j).faceUp)
            (Anchor.mem_all a) (Anchor.mem_all j) hne
          have h1 : 1 ≤ ccn c ((st.piles a).hidden ++ (st.piles a).faceUp) := ccn_pos hza
          have h2' : 1 ≤ ccn c ((st.piles j).hidden ++ (st.piles j).faceUp) := ccn_pos hzj
          omega
        rw [cardCount_split_zones]
        have h0 : 0 ≤ ccn c ((Suit.all.map st.found).flatMap id) := Nat.zero_le _
        have h0' : 0 ≤ ccn c ([st.stock, st.waste].flatMap id) := Nat.zero_le _
        omega
      omega

/-- A card occurring in both parts of an append is counted twice. -/
private theorem ccn_ge_two_of_double {c : Card} {xs ys : List Card}
    (hx : c ∈ xs) (hy : c ∈ ys) : 2 ≤ ccn c (xs ++ ys) := by
  rw [ccn_split]
  have h1 := ccn_pos hx
  have h2 := ccn_pos hy
  omega

/-- At a once-counted state, no card rides twice in one face-up run:not below its first occurrence, and not above it. -/
private theorem not_mem_own_aboveIn {st : State} {c : Card} {a : Anchor}
    (hcc : st.cardCount c = 1) (hmem : c ∈ (st.piles a).faceUp) :
    c ∉ aboveIn c (st.piles a).faceUp := by
  intro hcon
  have hsplit := below_aboveIn_split hmem
  have hzone : 2 ≤ ccn c ((st.piles a).hidden ++ (st.piles a).faceUp) := by
    have hfapart : 2 ≤ ccn c ((st.piles a).faceUp) := by
      rw [hsplit, ccn_split, show c :: aboveIn c ((st.piles a).faceUp) =
        [c] ++ aboveIn c ((st.piles a).faceUp) from rfl, ccn_split]
      have h1 : 1 ≤ ccn c [c] := by simp [ccn]
      have h2 : 1 ≤ ccn c (aboveIn c ((st.piles a).faceUp)) := ccn_pos hcon
      omega
    have hz : ccn c ((st.piles a).hidden ++ (st.piles a).faceUp) =
        ccn c ((st.piles a).hidden) + ccn c ((st.piles a).faceUp) := ccn_split c _ _
    omega
  have := cardCount_ge_of_zone (Anchor.mem_all a) hzone
  omega

/-! ## The exchange -/
private def exchangeAt (st : State) (t : Card) : Option Anchor → Option Anchor → State
  | none, _ => st
  | some _, none => st
  | some a, some a' =>
      if a = a' then st
      else { st with piles := fun k =>
        if k = a then ⟨(st.piles a).hidden,
            below t (st.piles a).faceUp ++ t :: aboveIn t.twin (st.piles a').faceUp⟩
        else if k = a' then ⟨(st.piles a').hidden,
            below t.twin (st.piles a').faceUp ++ t.twin :: aboveIn t (st.piles a).faceUp⟩
        else st.piles k }

/-- The local twin exchange: locate the two hosts by search at thisstate and swap their above-suffixes; the identity in every othershape.
  Total.
  Host-dynamic: no position is baked in — eachapplication reads `State.pileHolding` afresh. -/
def State.exchangeTwin (st : State) (t : Card) : State :=
  exchangeAt st t (st.pileHolding t) (st.pileHolding t.twin)
private theorem exchangeAt_none (st : State) (t : Card) (b : Option Anchor) :
    exchangeAt st t none b = st := by cases b <;> rfl
private theorem exchangeAt_some_none (st : State) (t : Card) (c : Anchor) :
    exchangeAt st t (some c) none = st := rfl
private theorem exchangeAt_some_some (st : State) (t : Card) (a a' : Anchor) :
    exchangeAt st t (some a) (some a') =
      if a = a' then st
      else { st with piles := fun k =>
        if k = a then ⟨(st.piles a).hidden,
            below t (st.piles a).faceUp ++ t :: aboveIn t.twin (st.piles a').faceUp⟩
        else if k = a' then ⟨(st.piles a').hidden,
            below t.twin (st.piles a').faceUp ++ t.twin :: aboveIn t (st.piles a).faceUp⟩
        else st.piles k } := rfl

/-- The pair names the exchange: asking at the twin is asking at thecard. -/
theorem State.exchangeTwin_pair (st : State) (t : Card) :
    st.exchangeTwin t.twin = st.exchangeTwin t := by
  rw [State.exchangeTwin, State.exchangeTwin]
  simp only [Card.twin_twin]
  cases h₁ : st.pileHolding t with
  | none =>
      cases h₂ : st.pileHolding t.twin with
      | none => rfl
      | some a' => rfl
  | some a =>
      cases h₂ : st.pileHolding t.twin with
      | none => rfl
      | some a' =>
          rw [exchangeAt_some_some, exchangeAt_some_some]
          simp only [Card.twin_twin]
          by_cases hne : a = a'
          · rw [ite_eq_left hne, ite_eq_left hne.symm]
          · rw [ite_eq_right hne, ite_eq_right (fun hc => hne hc.symm)]
            apply State.ext
            · rfl
            · funext k
              simp only []
              by_cases hka : k = a
              · have hka' : k ≠ a' := fun hc => hne (hc.symm.trans hka).symm
                rw [ite_eq_right hka', ite_eq_left hka, ite_eq_left hka]
              · by_cases hkb : k = a'
                · rw [ite_eq_left hkb, ite_eq_right hka, ite_eq_left hkb]
                · rw [ite_eq_right hkb, ite_eq_right hkb]
            · rfl
            · rfl
            · rfl

/-- At the located shape, the exchange is the explicit two-pilerecord update. -/
theorem State.exchangeTwin_eq_of_located {st : State} {t : Card} {a a' : Anchor}
    (h₁ : st.pileHolding t = some a) (h₂ : st.pileHolding t.twin = some a') (hne : a ≠ a') :
    st.exchangeTwin t =
      { st with piles := fun k =>
        if k = a then ⟨(st.piles a).hidden,
            below t (st.piles a).faceUp ++ t :: aboveIn t.twin (st.piles a').faceUp⟩
        else if k = a' then ⟨(st.piles a').hidden,
            below t.twin (st.piles a').faceUp ++ t.twin :: aboveIn t (st.piles a).faceUp⟩
        else st.piles k } := by
  rw [State.exchangeTwin, h₁, h₂, exchangeAt_some_some, ite_eq_right hne]

/-- Missing host: the exchange is the identity. -/
theorem State.exchangeTwin_eq_self_of_missing {st : State} {t : Card}
    (h : st.pileHolding t = none ∨ st.pileHolding t.twin = none) :
    st.exchangeTwin t = st := by
  rw [State.exchangeTwin]
  rcases h with h | h
  · rw [h, exchangeAt_none]
  · cases hc : st.pileHolding t with
    | none => rw [exchangeAt_none]
    | some c => rw [h, exchangeAt_some_none]

/-- Same pile: the exchange is the identity. -/
theorem State.exchangeTwin_eq_self_of_same {st : State} {t : Card} {a : Anchor}
    (h₁ : st.pileHolding t = some a) (h₂ : st.pileHolding t.twin = some a) :
    st.exchangeTwin t = st := by
  rw [State.exchangeTwin, h₁, h₂, exchangeAt_some_some, ite_eq_left rfl]
namespace State

/-- The host `t`'s pile, as written by the exchange: prefix through thehost, then the twin host's old suffix. -/
theorem exchangeTwin_pile_self {st : State} {t : Card} {a a' : Anchor}
    (h₁ : st.pileHolding t = some a) (h₂ : st.pileHolding t.twin = some a') (hne : a ≠ a') :
    (st.exchangeTwin t).piles a = ⟨(st.piles a).hidden,
      below t (st.piles a).faceUp ++ t :: aboveIn t.twin (st.piles a').faceUp⟩ := by
  rw [State.exchangeTwin_eq_of_located h₁ h₂ hne]
  show (if a = a then _ else _) = _
  rw [ite_eq_left rfl]

/-- The twin host's pile, as written by the exchange: prefix throughthe twin host, then `t`'s old suffix. -/
theorem exchangeTwin_pile_other {st : State} {t : Card} {a a' : Anchor}
    (h₁ : st.pileHolding t = some a) (h₂ : st.pileHolding t.twin = some a') (hne : a ≠ a') :
    (st.exchangeTwin t).piles a' = ⟨(st.piles a').hidden,
      below t.twin (st.piles a').faceUp ++ t.twin :: aboveIn t (st.piles a).faceUp⟩ := by
  rw [State.exchangeTwin_eq_of_located h₁ h₂ hne]
  show (if a' = a then _ else if a' = a' then _ else _) = _
  rw [ite_eq_right (Ne.symm hne), ite_eq_left rfl]

/-- Every pile off the twin pair is untouched. -/
theorem exchangeTwin_pile_ne {st : State} {t : Card} {a a' k : Anchor}
    (h₁ : st.pileHolding t = some a) (h₂ : st.pileHolding t.twin = some a') (hne : a ≠ a')
    (hk : k ≠ a) (hk' : k ≠ a') :
    (st.exchangeTwin t).piles k = st.piles k := by
  rw [State.exchangeTwin_eq_of_located h₁ h₂ hne]
  show (if k = a then _ else _) = _
  rw [ite_eq_right hk, ite_eq_right hk']
theorem exchangeTwin_found {st : State} {t : Card} :
    (st.exchangeTwin t).found = st.found := by
  cases h₁ : st.pileHolding t with
  | none => rw [State.exchangeTwin_eq_self_of_missing (Or.inl h₁)]
  | some a =>
      cases h₂ : st.pileHolding t.twin with
      | none => rw [State.exchangeTwin_eq_self_of_missing (Or.inr h₂)]
      | some a' =>
          by_cases hne : a = a'
          · subst hne
            rw [State.exchangeTwin_eq_self_of_same h₁ h₂]
          · rw [State.exchangeTwin_eq_of_located h₁ h₂ hne]
theorem exchangeTwin_stock {st : State} {t : Card} :
    (st.exchangeTwin t).stock = st.stock := by
  cases h₁ : st.pileHolding t with
  | none => rw [State.exchangeTwin_eq_self_of_missing (Or.inl h₁)]
  | some a =>
      cases h₂ : st.pileHolding t.twin with
      | none => rw [State.exchangeTwin_eq_self_of_missing (Or.inr h₂)]
      | some a' =>
          by_cases hne : a = a'
          · subst hne
            rw [State.exchangeTwin_eq_self_of_same h₁ h₂]
          · rw [State.exchangeTwin_eq_of_located h₁ h₂ hne]
theorem exchangeTwin_waste {st : State} {t : Card} :
    (st.exchangeTwin t).waste = st.waste := by
  cases h₁ : st.pileHolding t with
  | none => rw [State.exchangeTwin_eq_self_of_missing (Or.inl h₁)]
  | some a =>
      cases h₂ : st.pileHolding t.twin with
      | none => rw [State.exchangeTwin_eq_self_of_missing (Or.inr h₂)]
      | some a' =>
          by_cases hne : a = a'
          · subst hne
            rw [State.exchangeTwin_eq_self_of_same h₁ h₂]
          · rw [State.exchangeTwin_eq_of_located h₁ h₂ hne]
theorem exchangeTwin_drawStep {st : State} {t : Card} :
    (st.exchangeTwin t).drawStep = st.drawStep := by
  cases h₁ : st.pileHolding t with
  | none => rw [State.exchangeTwin_eq_self_of_missing (Or.inl h₁)]
  | some a =>
      cases h₂ : st.pileHolding t.twin with
      | none => rw [State.exchangeTwin_eq_self_of_missing (Or.inr h₂)]
      | some a' =>
          by_cases hne : a = a'
          · subst hne
            rw [State.exchangeTwin_eq_self_of_same h₁ h₂]
          · rw [State.exchangeTwin_eq_of_located h₁ h₂ hne]

/-- Both suffixes empty: the exchange is literally the state. -/
theorem exchangeTwin_eq_self_of_both_bare {st : State} {t : Card} {a a' : Anchor}
    (h₁ : st.pileHolding t = some a) (h₂ : st.pileHolding t.twin = some a')
    (hne : a ≠ a')
    (hS : aboveIn t (st.piles a).faceUp = [])
    (hS' : aboveIn t.twin (st.piles a').faceUp = []) :
    st.exchangeTwin t = st := by
  have hTa : t ∈ (st.piles a).faceUp := pileHolding_mem h₁
  have hTb : t.twin ∈ (st.piles a').faceUp := pileHolding_mem h₂
  have hfa : (st.piles a).faceUp = below t ((st.piles a).faceUp) ++ [t] := by
    have hs := below_aboveIn_split hTa
    rw [hS] at hs
    exact hs
  have hfa' : (st.piles a').faceUp = below t.twin ((st.piles a').faceUp) ++ [t.twin] := by
    have hs := below_aboveIn_split hTb
    rw [hS'] at hs
    exact hs
  rw [State.exchangeTwin_eq_of_located h₁ h₂ hne]
  apply State.ext
  · rfl
  · funext k
    simp only []
    by_cases hk : k = a
    · rw [hk, ite_eq_left rfl]
      apply Pile.ext
      · rfl
      · rw [hS']
        exact hfa.symm
    · by_cases hk' : k = a'
      · rw [ite_eq_right hk, hk', ite_eq_left rfl]
        apply Pile.ext
        · rfl
        · rw [hS]
          exact hfa'.symm
      · rw [ite_eq_right hk, ite_eq_right hk']
  · rfl
  · rfl
  · rfl
end State
private theorem setPile_pair (st : State) (a a' : Anchor) (A B : Pile) (hne : a ≠ a') :
    (st.setPile a A).setPile a' B = { st with piles := fun k =>
      if k = a then A else if k = a' then B else st.piles k } := by
  apply State.ext
  · rfl
  · funext k
    show (if k = a' then B else if k = a then A else st.piles k) =
        (if k = a then A else if k = a' then B else st.piles k)
    by_cases hk : k = a
    · have hka' : k ≠ a' := fun hc => hne (hc.symm.trans hk).symm
      rw [ite_eq_left hk, ite_eq_left hk, ite_eq_right hka']
    · by_cases hk' : k = a'
      · have hka : k ≠ a := fun hc => hne (hc.symm.trans hk')
        rw [ite_eq_left hk', ite_eq_right hka, ite_eq_left hk']
      · rw [ite_eq_right hk', ite_eq_right hk, ite_eq_right hk, ite_eq_right hk']
  · rfl
  · rfl
  · rfl

/-! ## The counts through the exchange -/
private theorem cardCount_setPile_add (st : State) (k : Anchor) (hz hf : List Card) (c : Card) :
    st.cardCount c + ccn c (hz ++ hf) =
    (st.setPile k ⟨hz, hf⟩).cardCount c + ccn c ((st.piles k).hidden ++ (st.piles k).faceUp) := by
  cases k <;>
    simp only [State.setPile, State.cardCount, State.zones, ccn, Anchor.all,
      List.map_cons, List.map_nil, List.map_id, List.flatMap, List.flatten_cons,
      List.flatten_append, List.flatten_nil, List.filter_append, List.filter_nil,
      List.length_append, List.length_nil, ite_true, ite_false,
      show ¬ (Anchor.p1 = Anchor.p0) from by decide,
      show ¬ (Anchor.p2 = Anchor.p0) from by decide,
      show ¬ (Anchor.p3 = Anchor.p0) from by decide,
      show ¬ (Anchor.p4 = Anchor.p0) from by decide,
      show ¬ (Anchor.p5 = Anchor.p0) from by decide,
      show ¬ (Anchor.p6 = Anchor.p0) from by decide,
      show ¬ (Anchor.p0 = Anchor.p1) from by decide,
      show ¬ (Anchor.p2 = Anchor.p1) from by decide,
      show ¬ (Anchor.p3 = Anchor.p1) from by decide,
      show ¬ (Anchor.p4 = Anchor.p1) from by decide,
      show ¬ (Anchor.p5 = Anchor.p1) from by decide,
      show ¬ (Anchor.p6 = Anchor.p1) from by decide,
      show ¬ (Anchor.p0 = Anchor.p2) from by decide,
      show ¬ (Anchor.p1 = Anchor.p2) from by decide,
      show ¬ (Anchor.p3 = Anchor.p2) from by decide,
      show ¬ (Anchor.p4 = Anchor.p2) from by decide,
      show ¬ (Anchor.p5 = Anchor.p2) from by decide,
      show ¬ (Anchor.p6 = Anchor.p2) from by decide,
      show ¬ (Anchor.p0 = Anchor.p3) from by decide,
      show ¬ (Anchor.p1 = Anchor.p3) from by decide,
      show ¬ (Anchor.p2 = Anchor.p3) from by decide,
      show ¬ (Anchor.p4 = Anchor.p3) from by decide,
      show ¬ (Anchor.p5 = Anchor.p3) from by decide,
      show ¬ (Anchor.p6 = Anchor.p3) from by decide,
      show ¬ (Anchor.p0 = Anchor.p4) from by decide,
      show ¬ (Anchor.p1 = Anchor.p4) from by decide,
      show ¬ (Anchor.p2 = Anchor.p4) from by decide,
      show ¬ (Anchor.p3 = Anchor.p4) from by decide,
      show ¬ (Anchor.p5 = Anchor.p4) from by decide,
      show ¬ (Anchor.p6 = Anchor.p4) from by decide,
      show ¬ (Anchor.p0 = Anchor.p5) from by decide,
      show ¬ (Anchor.p1 = Anchor.p5) from by decide,
      show ¬ (Anchor.p2 = Anchor.p5) from by decide,
      show ¬ (Anchor.p3 = Anchor.p5) from by decide,
      show ¬ (Anchor.p4 = Anchor.p5) from by decide,
      show ¬ (Anchor.p6 = Anchor.p5) from by decide,
      show ¬ (Anchor.p0 = Anchor.p6) from by decide,
      show ¬ (Anchor.p1 = Anchor.p6) from by decide,
      show ¬ (Anchor.p2 = Anchor.p6) from by decide,
      show ¬ (Anchor.p3 = Anchor.p6) from by decide,
      show ¬ (Anchor.p4 = Anchor.p6) from by decide,
      show ¬ (Anchor.p5 = Anchor.p6) from by decide] <;>
    omega

/-- Every card keeps its count through the exchange: the very samecards, suffix-swapped between the two piles. -/
theorem State.exchangeTwin_cardCount {st : State} {t : Card} {a a' : Anchor}
    (h₁ : st.pileHolding t = some a) (h₂ : st.pileHolding t.twin = some a') (hne : a ≠ a') :
    ∀ c, (st.exchangeTwin t).cardCount c = st.cardCount c := by
  intro c
  have hTa : t ∈ (st.piles a).faceUp := pileHolding_mem h₁
  have hTb : t.twin ∈ (st.piles a').faceUp := pileHolding_mem h₂
  have hfa : (st.piles a).faceUp = below t ((st.piles a).faceUp) ++
      t :: aboveIn t ((st.piles a).faceUp) := below_aboveIn_split hTa
  have hfa' : (st.piles a').faceUp = below t.twin ((st.piles a').faceUp) ++
      t.twin :: aboveIn t.twin ((st.piles a').faceUp) := below_aboveIn_split hTb
  have hpair : ccn c ((st.piles a).hidden ++
        (below t ((st.piles a).faceUp) ++ t :: aboveIn t.twin ((st.piles a').faceUp))) +
      ccn c ((st.piles a').hidden ++
        (below t.twin ((st.piles a').faceUp) ++ t.twin :: aboveIn t ((st.piles a).faceUp))) =
      ccn c ((st.piles a).hidden ++ (st.piles a).faceUp) +
      ccn c ((st.piles a').hidden ++ (st.piles a').faceUp) := by
    have hr := ccn_rechunk (c := c) (x := t) (x' := t.twin)
      (ha := (st.piles a).hidden) (hb := below t ((st.piles a).faceUp))
      (hs := (st.piles a').hidden) (ht := below t.twin ((st.piles a').faceUp))
      (S := aboveIn t ((st.piles a).faceUp)) (S' := aboveIn t.twin ((st.piles a').faceUp))
    rw [← hfa, ← hfa'] at hr
    exact hr
  have hupd : st.exchangeTwin t =
      (st.setPile a ⟨(st.piles a).hidden,
        below t ((st.piles a).faceUp) ++ t :: aboveIn t.twin ((st.piles a').faceUp)⟩).setPile a'
      ⟨(st.piles a').hidden,
        below t.twin ((st.piles a').faceUp) ++ t.twin :: aboveIn t ((st.piles a).faceUp)⟩ := by
    rw [State.exchangeTwin_eq_of_located h₁ h₂ hne, setPile_pair st a a' _ _ hne]
  rw [hupd]
  have E1 := cardCount_setPile_add st a ((st.piles a).hidden)
    (below t ((st.piles a).faceUp) ++ t :: aboveIn t.twin ((st.piles a').faceUp)) c
  have E2 := cardCount_setPile_add (st.setPile a ⟨(st.piles a).hidden,
    below t ((st.piles a).faceUp) ++ t :: aboveIn t.twin ((st.piles a').faceUp)⟩) a'
    ((st.piles a').hidden)
    (below t.twin ((st.piles a').faceUp) ++ t.twin :: aboveIn t ((st.piles a).faceUp)) c
  have hz2 : (((st.setPile a ⟨(st.piles a).hidden,
        below t ((st.piles a).faceUp) ++ t :: aboveIn t.twin ((st.piles a').faceUp)⟩ : State)).piles a').hidden ++
      (((st.setPile a ⟨(st.piles a).hidden,
        below t ((st.piles a).faceUp) ++ t :: aboveIn t.twin ((st.piles a').faceUp)⟩ : State)).piles a').faceUp =
      (st.piles a').hidden ++ (st.piles a').faceUp := by
    show (if a' = a then
        ⟨(st.piles a).hidden,
          below t ((st.piles a).faceUp) ++ t :: aboveIn t.twin ((st.piles a').faceUp)⟩
        else st.piles a').hidden ++
      (if a' = a then
        ⟨(st.piles a).hidden,
          below t ((st.piles a).faceUp) ++ t :: aboveIn t.twin ((st.piles a').faceUp)⟩
        else st.piles a').faceUp = _
    rw [ite_eq_right (Ne.symm hne)]
  rw [hz2] at E2
  omega

/-! ## Hygiene through the exchange -/

/-- No card is its own twin. -/
theorem Card.twin_ne (c : Card) : c.twin ≠ c := by
  intro hcon
  have hs : c.suit.twin = c.suit := by
    calc c.suit.twin = (Card.twin c).suit := rfl
      _ = c.suit := by rw [hcon]
  exact Suit.twin_ne c.suit hs

/-- A fitting card is distinct from its host. -/
private theorem ne_of_canSitOn {z y : Card} (h : canSitOn z y = true) : z ≠ y := by
  intro hcon
  subst hcon
  simp only [canSitOn_eq] at h
  omega

/-- `afterRunRemoved` at a nonempty prefix keeps the hidden deck andrelocates the face-up run to the prefix alone. -/
private theorem afterRunRemoved_ne {p : Pile} {pre : List Card} (h : pre ≠ []) :
    Pile.afterRunRemoved p pre = { p with faceUp := pre } := by
  cases pre with
  | nil => exact absurd rfl h
  | cons w ws => rfl
private theorem canPlace_inr_eq {st : State} {c z : Card} {k : Anchor}
    (h : st.pileOfTop z = some k) :
    st.canPlace c (Sum.inr z) = canSitOn c z := by
  rw [show st.canPlace c (Sum.inr z) = canSitOn c z from by
    simp only [State.canPlace, h]]
private theorem putRun_inr_eq {st : State} {run : List Card} {z : Card} {k : Anchor}
    (h : st.pileOfTop z = some k) :
    st.putRun run (Sum.inr z) =
    st.setPile k { st.piles k with faceUp := (st.piles k).faceUp ++ run } := by
  rw [show st.putRun run (Sum.inr z) =
    st.setPile k { st.piles k with faceUp := (st.piles k).faceUp ++ run } from by
    simp only [State.putRun, h]]
private theorem exists_cons {l : List Card} (h : l ≠ []) :
    ∃ z r, l = z :: r := by
  cases hl : l with
  | nil => exact absurd hl h
  | cons z r => exact ⟨z, r, rfl⟩

/-- Appending a fixed tail respects list equality. -/
private theorem append_congr_right {xs ys : List Card} (h : xs = ys) (zs : List Card) :
    xs ++ zs = ys ++ zs := by rw [h]

/-- Counting respects list equality. -/
private theorem ccn_congr {xs ys : List Card} (h : xs = ys) (c : Card) :
    ccn c xs = ccn c ys := by rw [h]

/-- A pile update leaves every other pile's top alone. -/
private theorem setPile_topOf_ne {st : State} {k b : Anchor} {Q : Pile} (h : k ≠ b) :
    (st.setPile b Q).topOf k = st.topOf k := by
  show (if k = b then Q else st.piles k).top = st.topOf k
  rw [ite_eq_right h]
  rfl

/-- A pile update leaves every other pile alone. -/
private theorem setPile_piles_ne {st : State} {k b : Anchor} {Q : Pile} (h : k ≠ b) :
    (st.setPile b Q).piles k = st.piles k := by
  show (if k = b then Q else st.piles k) = st.piles k
  rw [ite_eq_right h]

/-- A pile update writes exactly the given pile. -/
private theorem setPile_piles_self (st : State) (b : Anchor) (Q : Pile) :
    (st.setPile b Q).piles b = Q := by
  show (if b = b then Q else st.piles b) = Q
  rw [ite_eq_left rfl]

/-- The tabToTab branch of `State.step`, read at an explicit locatedshape. -/
private theorem step_tabToTab_eq {st : State} {z : Card} {b : Base} {a : Anchor}
    {w : Card} {rest : List Card}
    (h1 : st.pileHolding z = some a) (h2 : st.canPlace z b = true)
    (h3 : fromCard z (st.piles a).faceUp = w :: rest) :
    st.step (Move.tabToTab z b) =
    some ((st.setPile a (Pile.afterRunRemoved (st.piles a) (below z (st.piles a).faceUp))).putRun
      (w :: rest) b) := by
  rw [show st.step (Move.tabToTab z b) =
    some ((st.setPile a (Pile.afterRunRemoved (st.piles a) (below z (st.piles a).faceUp))).putRun
      (w :: rest) b) from by
    simp only [State.step, h1, h2, h3, ite_true]]

/-- The first written pile's legibility: the prefix through `t`, thenthe twin host's whole old suffix.
  The joint carries by`canSitOn_twin_right` from the original `t`-joint. -/
private theorem runOK_write_self {t : Card} {fa fa' : List Card}
    (hTa : t ∈ fa) (hTb : t.twin ∈ fa')
    (hA : runOK fa = true) (hB : runOK fa' = true) :
    runOK (below t fa ++ t :: aboveIn t.twin fa') = true := by
  have hRA := (runOK_append_exact t (below t fa) (aboveIn t fa)).mp
    (by rw [show below t fa ++ t :: aboveIn t fa = fa from (below_aboveIn_split hTa).symm]
        exact hA)
  have hRB := (runOK_append_exact t.twin (below t.twin fa') (aboveIn t.twin fa')).mp
    (by rw [show below t.twin fa' ++ t.twin :: aboveIn t.twin fa' = fa'
            from (below_aboveIn_split hTb).symm]
        exact hB)
  refine (runOK_append_exact t (below t fa) (aboveIn t.twin fa')).mpr ⟨hRA.1, ?_⟩
  cases hS' : aboveIn t.twin fa' with
  | nil => rfl
  | cons z r =>
    have h2 := hRB.2
    rw [hS'] at h2
    rw [runOK_cons_cons, Bool.and_eq_true] at h2
    rw [runOK_cons_cons, Bool.and_eq_true]
    refine ⟨?_, h2.2⟩
    rw [← canSitOn_twin_right z t, show {t with suit := t.suit.twin} = t.twin from rfl]
    exact h2.1

/-- The second written pile's legibility: the prefix through `t.twin`,then `t`'s whole old suffix. -/
private theorem runOK_write_other {t : Card} {fa fa' : List Card}
    (hTa : t ∈ fa) (hTb : t.twin ∈ fa')
    (hA : runOK fa = true) (hB : runOK fa' = true) :
    runOK (below t.twin fa' ++ t.twin :: aboveIn t fa) = true := by
  have hRA := (runOK_append_exact t (below t fa) (aboveIn t fa)).mp
    (by rw [show below t fa ++ t :: aboveIn t fa = fa from (below_aboveIn_split hTa).symm]
        exact hA)
  have hRB := (runOK_append_exact t.twin (below t.twin fa') (aboveIn t.twin fa')).mp
    (by rw [show below t.twin fa' ++ t.twin :: aboveIn t.twin fa' = fa'
            from (below_aboveIn_split hTb).symm]
        exact hB)
  refine (runOK_append_exact t.twin (below t.twin fa') (aboveIn t fa)).mpr ⟨hRB.1, ?_⟩
  cases hS : aboveIn t fa with
  | nil => rfl
  | cons z r =>
    have h2 := hRA.2
    rw [hS] at h2
    rw [runOK_cons_cons, Bool.and_eq_true] at h2
    rw [runOK_cons_cons, Bool.and_eq_true]
    refine ⟨?_, h2.2⟩
    rw [show t.twin = {t with suit := t.suit.twin} from rfl, canSitOn_twin_right z t]
    exact h2.1

/-- The exchange preserves the whole hygiene clause: founds anddrawStep are untouched, the two rewritten piles are legible by thetwin-blindness of the fit rules, and every card keeps its count. -/
theorem State.wf_exchangeTwin {st : State} {t : Card} {a a' : Anchor}
    (hwf : st.WF) (h₁ : st.pileHolding t = some a) (h₂ : st.pileHolding t.twin = some a')
    (hne : a ≠ a') : (st.exchangeTwin t).WF := by
  obtain ⟨hf, hr, hc, hd⟩ := hwf
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- founds per-run legibility
    intro s
    have : (st.exchangeTwin t).found s = st.found s := by rw [State.exchangeTwin_found]
    rw [this]
    exact hf s
  · intro k
    have hTa : t ∈ (st.piles a).faceUp := pileHolding_mem h₁
    have hTb : t.twin ∈ (st.piles a').faceUp := pileHolding_mem h₂
    by_cases hk : k = a
    · rw [hk]
      rw [State.exchangeTwin_pile_self h₁ h₂ hne]
      exact runOK_write_self hTa hTb (hr a) (hr a')
    · by_cases hk' : k = a'
      · rw [hk']
        rw [State.exchangeTwin_pile_other h₁ h₂ hne]
        exact runOK_write_other hTa hTb (hr a) (hr a')
      · rw [State.exchangeTwin_pile_ne h₁ h₂ hne hk hk']
        exact hr k
  · intro c hcuniv
    rw [State.exchangeTwin_cardCount h₁ h₂ hne c]
    exact hc c hcuniv
  · rw [State.exchangeTwin_drawStep]
    exact hd

/-- The verdict predicate is untouched: the founds are. -/
theorem State.isWin_exchangeTwin {st : State} {t : Card} :
    (st.exchangeTwin t).isWin = st.isWin := by
  rw [State.isWin, State.isWin, State.exchangeTwin_found]

/-! ## Hosts keep their piles through their own exchange -/

/-- The hosts keep their face-up membership through the exchange: theprefix through each host is untouched, so the searches re-locate thesame anchors.
  The premium content is the search-hygiene transfer —dynamic re-anchoring works because the hosts are still where theywere. -/
theorem State.exchangeTwin_hosts_stable {st : State} {t : Card} {a a' : Anchor}
    (h₁ : st.pileHolding t = some a) (h₂ : st.pileHolding t.twin = some a') (hne : a ≠ a')
    (ht : st.cardCount t = 1) (htw : st.cardCount t.twin = 1) :
    (st.exchangeTwin t).pileHolding t = some a ∧
      (st.exchangeTwin t).pileHolding t.twin = some a' := by
  have hTa : t ∈ (st.piles a).faceUp := pileHolding_mem h₁
  have hTb : t.twin ∈ (st.piles a').faceUp := pileHolding_mem h₂
  have hza : t ∈ ((st.exchangeTwin t).piles a).faceUp := by
    rw [State.exchangeTwin_pile_self h₁ h₂ hne]
    exact List.mem_append.mpr (Or.inr (List.mem_cons_self ..))
  have hzb : t.twin ∈ ((st.exchangeTwin t).piles a').faceUp := by
    rw [State.exchangeTwin_pile_other h₁ h₂ hne]
    exact List.mem_append.mpr (Or.inr (List.mem_cons_self ..))
  constructor
  · apply pileHolding_eq_of_unique
    · exact Anchor.mem_all a
    · exact hza
    · intro j hj
      cases hde : decide (j = a) with
      | true => exact of_decide_eq_true hde
      | false =>
          exfalso
          have hja : j ≠ a := fun hcon => by
            have := decide_eq_true hcon
            rw [hde] at this
            exact absurd this (by simp)
          by_cases hja' : j = a'
          · rw [hja'] at hj
            rw [State.exchangeTwin_pile_other h₁ h₂ hne] at hj
            rcases List.mem_append.mp hj with hlow | hup
            · -- t in the twin host's below: would double-t in st
              exact absurd (pile_mem_unique ht hTa
                (show t ∈ (st.piles a').faceUp from below_subset_mem hlow)) (fun hc => hne hc)
            · rcases List.mem_cons.mp hup with heq | hsuf
              · exact absurd heq.symm (Card.twin_ne t)
              · exact absurd hsuf (not_mem_own_aboveIn ht hTa)
          · rw [State.exchangeTwin_pile_ne h₁ h₂ hne hja hja'] at hj
            exact absurd (pile_mem_unique ht hTa hj) (fun hc => hja hc.symm)
  · apply pileHolding_eq_of_unique
    · exact Anchor.mem_all a'
    · exact hzb
    · intro j hj
      cases hde : decide (j = a') with
      | true => exact of_decide_eq_true hde
      | false =>
          exfalso
          have hja' : j ≠ a' := fun hcon => by
            have := decide_eq_true hcon
            rw [hde] at this
            exact absurd this (by simp)
          by_cases hja : j = a
          · rw [hja] at hj
            rw [State.exchangeTwin_pile_self h₁ h₂ hne] at hj
            rcases List.mem_append.mp hj with hlow | hup
            · exact absurd (pile_mem_unique htw hTb
                (show t.twin ∈ (st.piles a).faceUp from below_subset_mem hlow)) (fun hc => hne hc.symm)
            · rcases List.mem_cons.mp hup with heq | hsuf
              · exact absurd heq (Card.twin_ne t)
              · exact absurd hsuf (not_mem_own_aboveIn htw hTb)
          · rw [State.exchangeTwin_pile_ne h₁ h₂ hne hja hja'] at hj
            exact absurd (pile_mem_unique htw hTb hj) (fun hc => hja' hc.symm)

/-- The involution at the licensed shape: exchanging twice at the sametwin pair is no operation.
  The hosts keep their piles, so the secondask re-locates and re-swaps identically. -/
theorem State.exchangeTwin_invol {st : State} {t : Card} {a a' : Anchor}
    (h₁ : st.pileHolding t = some a) (h₂ : st.pileHolding t.twin = some a') (hne : a ≠ a')
    (ht : st.cardCount t = 1) (htw : st.cardCount t.twin = 1) :
    (st.exchangeTwin t).exchangeTwin t = st := by
  obtain ⟨hs₁, hs₂⟩ := State.exchangeTwin_hosts_stable h₁ h₂ hne ht htw
  have hTa : t ∈ (st.piles a).faceUp := pileHolding_mem h₁
  have hTb : t.twin ∈ (st.piles a').faceUp := pileHolding_mem h₂
  have hfa : (st.piles a).faceUp = below t ((st.piles a).faceUp) ++
      t :: aboveIn t ((st.piles a).faceUp) := below_aboveIn_split hTa
  have hfa' : (st.piles a').faceUp = below t.twin ((st.piles a').faceUp) ++
      t.twin :: aboveIn t.twin ((st.piles a').faceUp) := below_aboveIn_split hTb
  rw [State.exchangeTwin_eq_of_located hs₁ hs₂ hne]
  apply State.ext
  · rw [State.exchangeTwin_found]
  · funext k
    simp only []
    by_cases hk : k = a
    · rw [hk, ite_eq_left rfl]
      rw [State.exchangeTwin_pile_self h₁ h₂ hne, State.exchangeTwin_pile_other h₁ h₂ hne]
      apply Pile.ext
      · rfl
      · have hS2 : aboveIn t.twin (below t.twin ((st.piles a').faceUp) ++ t.twin
            :: aboveIn t ((st.piles a).faceUp)) = aboveIn t ((st.piles a).faceUp) := by
          rw [aboveIn, fromCard_append_stop (below_not_mem t.twin ((st.piles a').faceUp))]
          rfl
        rw [hS2, below_append_stop (below_not_mem t ((st.piles a).faceUp))]
        exact hfa.symm
    · by_cases hk' : k = a'
      · rw [ite_eq_right hk, hk', ite_eq_left rfl]
        rw [State.exchangeTwin_pile_self h₁ h₂ hne, State.exchangeTwin_pile_other h₁ h₂ hne]
        apply Pile.ext
        · rfl
        · have hS2 : aboveIn t (below t ((st.piles a).faceUp) ++ t
              :: aboveIn t.twin ((st.piles a').faceUp)) = aboveIn t.twin ((st.piles a').faceUp) := by
            rw [aboveIn, fromCard_append_stop (below_not_mem t ((st.piles a).faceUp))]
            rfl
          rw [hS2, below_append_stop (below_not_mem t.twin ((st.piles a').faceUp))]
          exact hfa'.symm
      · rw [ite_eq_right hk, ite_eq_right hk']
        exact State.exchangeTwin_pile_ne h₁ h₂ hne hk hk'
  · rw [State.exchangeTwin_stock]
  · rw [State.exchangeTwin_waste]
  · rw [State.exchangeTwin_drawStep]

/-! ## The region survives: the slots swap, not the content -/

/-- The suffix above `t` in the exchanged state's `t`-pile *is* theold suffix of the twin host. -/
theorem State.exchangeTwin_aboveIn_self {st : State} {t : Card} {a a' : Anchor}
    (h₁ : st.pileHolding t = some a) (h₂ : st.pileHolding t.twin = some a') (hne : a ≠ a') :
    aboveIn t ((st.exchangeTwin t).piles a).faceUp = aboveIn t.twin ((st.piles a').faceUp) := by
  rw [State.exchangeTwin_pile_self h₁ h₂ hne, aboveIn]
  show (fromCard t (below t ((st.piles a).faceUp) ++ t ::
      aboveIn t.twin ((st.piles a').faceUp))).tail
    = aboveIn t.twin ((st.piles a').faceUp)
  rw [fromCard_append_stop (below_not_mem t ((st.piles a).faceUp))]
  rfl

/-- The suffix above `t.twin` in the exchanged state's twin pile *is*the old suffix of `t`. -/
theorem State.exchangeTwin_aboveIn_other {st : State} {t : Card} {a a' : Anchor}
    (h₁ : st.pileHolding t = some a) (h₂ : st.pileHolding t.twin = some a') (hne : a ≠ a') :
    aboveIn t.twin ((st.exchangeTwin t).piles a').faceUp = aboveIn t ((st.piles a).faceUp) := by
  rw [State.exchangeTwin_pile_other h₁ h₂ hne, aboveIn]
  show (fromCard t.twin (below t.twin ((st.piles a').faceUp) ++ t.twin ::
      aboveIn t ((st.piles a).faceUp))).tail
    = aboveIn t ((st.piles a).faceUp)
  rw [fromCard_append_stop (below_not_mem t.twin ((st.piles a').faceUp))]
  rfl

/-- Regional uniqueness transfer: every card of the twin region — thepair plus the two riding suffixes — that is counted once in `st` isstill counted once in the exchanged state, and each sits in one of the(possibly swapped) region slots. -/
theorem State.exchangeTwin_region_unique {st : State} {t : Card} {a a' : Anchor}
    (h₁ : st.pileHolding t = some a) (h₂ : st.pileHolding t.twin = some a') (hne : a ≠ a')
    (hreg : ∀ c, c = t ∨ c = t.twin ∨ c ∈ aboveIn t ((st.piles a).faceUp) ∨
      c ∈ aboveIn t.twin ((st.piles a').faceUp) → st.cardCount c = 1) :
    ∀ c, c = t ∨ c = t.twin ∨ c ∈ aboveIn t (((st.exchangeTwin t).piles a).faceUp) ∨
      c ∈ aboveIn t.twin (((st.exchangeTwin t).piles a').faceUp) →
      (st.exchangeTwin t).cardCount c = 1 := by
  intro c hc
  rw [State.exchangeTwin_aboveIn_self h₁ h₂ hne,
    State.exchangeTwin_aboveIn_other h₁ h₂ hne] at hc
  rw [State.exchangeTwin_cardCount h₁ h₂ hne c]
  rcases hc with hc | hc | hc | hc
  · exact hreg c (Or.inl hc)
  · exact hreg c (Or.inr (Or.inl hc))
  · exact hreg c (Or.inr (Or.inr (Or.inr hc)))
  · exact hreg c (Or.inr (Or.inr (Or.inl hc)))

/-! ## The bare-twin iff -/

/-- One bare twin, cargo-side realization: the cargo run above `t`rides onto the bare twin host as a plain `Move.tabToTab`, landingexactly at the exchange. -/
private theorem step_realize_fwd {st : State} {t : Card} {a a' : Anchor} {z : Card}
    {rest : List Card}
    (hwf : st.WF)
    (h₁ : st.pileHolding t = some a) (h₂ : st.pileHolding t.twin = some a') (hne : a ≠ a')
    (hS : aboveIn t ((st.piles a).faceUp) = z :: rest)
    (hS' : aboveIn t.twin ((st.piles a').faceUp) = []) :
    st.step (Move.tabToTab z (Sum.inr t.twin)) = some (st.exchangeTwin t) := by
  obtain ⟨hf, hr, hc, hd⟩ := hwf
  have hTa : t ∈ (st.piles a).faceUp := pileHolding_mem h₁
  have hTb : t.twin ∈ (st.piles a').faceUp := pileHolding_mem h₂
  have cz1 := hc z (Card.mem_universe z)
  have ct1 := hc t (Card.mem_universe t)
  have cttw1 := hc t.twin (Card.mem_universe t.twin)
  have hfa : (st.piles a).faceUp = below t ((st.piles a).faceUp) ++
      t :: (z :: rest) := by
    have h := below_aboveIn_split hTa
    rw [hS] at h
    exact h
  have hfa' : (st.piles a').faceUp = below t.twin ((st.piles a').faceUp) ++
      t.twin :: [] := by
    have h := below_aboveIn_split hTb
    rw [hS'] at h
    exact h
  -- the joint under the cargo head, and its twin-blind mirror
  have hjt : canSitOn z t = true := runOK_joint_of_splice (h := by
    rw [← hfa]
    exact hr a)
  have hzt : z ≠ t := ne_of_canSitOn hjt
  have hfit : canSitOn z t.twin = true := by
    rw [show t.twin = {t with suit := t.suit.twin} from rfl, canSitOn_twin_right z t]
    exact hjt
  have hzttw : z ≠ t.twin := ne_of_canSitOn hfit
  -- z occurs only in the cargo slot of pile a
  have hZfa : z ∈ (st.piles a).faceUp := by
    have := aboveIn_subset_mem (l := (st.piles a).faceUp) (x := z)
      (show z ∈ aboveIn t ((st.piles a).faceUp) from by rw [hS]; exact List.mem_cons_self ..)
    exact this
  have hZP1 : z ∉ below t ((st.piles a).faceUp) := fun hmemb => by
    have h2 : 2 ≤ ccn z ((st.piles a).hidden ++ (st.piles a).faceUp) := by
      have hcut : ccn z ((st.piles a).faceUp) =
          ccn z (below t ((st.piles a).faceUp)) + ccn z (t :: z :: rest) := by
        rw [ccn_congr hfa z, ccn_split]
      have e1 : 1 ≤ ccn z (below t ((st.piles a).faceUp)) := ccn_pos hmemb
      have e2 : 1 ≤ ccn z (t :: z :: rest) := by
        rw [ccn_cons]
        have h3 : 1 ≤ ccn z (z :: rest) := by
          rw [ccn_cons]
          have e2' : 1 ≤ ccn z [z] := by simp [ccn]
          omega
        omega
      have hA : 2 ≤ ccn z ((st.piles a).faceUp) := by
        rw [hcut]
        omega
      have hz : ccn z ((st.piles a).hidden ++ (st.piles a).faceUp) =
          ccn z ((st.piles a).hidden) + ccn z ((st.piles a).faceUp) := ccn_split z _ _
      omega
    have := cardCount_ge_of_zone (Anchor.mem_all a) h2
    omega
  have hZP2 : z ∉ below t.twin ((st.piles a').faceUp) := fun hmemb => by
    exact absurd (pile_mem_unique cz1 hZfa (below_subset_mem hmemb)) (fun hcon => hne hcon)
  -- searches and placements at st
  have htopb : st.topOf a' = some t.twin := by
    show lastOf ((st.piles a').faceUp) = some t.twin
    rw [hfa', lastOf_append_singleton]
  have hptb : st.pileOfTop t.twin = some a' := by
    apply pileOfTop_eq_of_unique
    · exact Anchor.mem_all a'
    · exact htopb
    · intro j hj
      have hjm : t.twin ∈ (st.piles j).faceUp := lastOf_mem hj
      exact pile_mem_unique cttw1 hjm hTb
  have hcp : st.canPlace z (Sum.inr t.twin) = true := by
    rw [canPlace_inr_eq hptb]
    exact hfit
  have hphz : st.pileHolding z = some a := by
    apply pileHolding_eq_of_unique
    · exact Anchor.mem_all a
    · exact hZfa
    · intro j hj
      cases hde : decide (j = a) with
      | true => exact of_decide_eq_true hde
      | false =>
          exfalso
          have hja : j ≠ a := fun hcon => by
            have := decide_eq_true hcon
            rw [hde] at this
            exact absurd this (by simp)
          exact absurd (pile_mem_unique cz1 hZfa hj) (fun hcon => hja hcon.symm)
  -- the run below the cargo head, and the prefix after the lift
  have hrun : fromCard z ((st.piles a).faceUp) = z :: rest := by
    rw [hfa, fromCard_append_notmem hZP1, fromCard_cons_ne _ (fun hcon => hzt hcon.symm),
      fromCard_cons_self]
  have hpre : below z ((st.piles a).faceUp) =
      below t ((st.piles a).faceUp) ++ [t] := by
    rw [hfa, below_append_notmem hZP1, below_cons_ne _ (fun hcon => hzt hcon.symm),
      below_cons_self, below_append_stop (below_not_mem t ((st.piles a).faceUp))]
  have hprene : below t ((st.piles a).faceUp) ++ [t] ≠ [] := by
    intro hc
    cases hb : below t ((st.piles a).faceUp) with
    | nil =>
        rw [hb] at hc
        simp at hc
    | cons w ws =>
        rw [hb] at hc
        simp at hc
  -- unfold the step
  rw [step_tabToTab_eq hphz hcp hrun, hpre, afterRunRemoved_ne hprene]
  -- the intermediate pile got exactly the prefix through t; the run
  -- rides onto the twin host's pile
  have hσpt : (st.setPile a { st.piles a with
      faceUp := below t ((st.piles a).faceUp) ++ [t] }).pileOfTop t.twin = some a' := by
    apply pileOfTop_eq_of_unique
    · exact Anchor.mem_all a'
    · rw [setPile_topOf_ne (Ne.symm hne)]
      show lastOf ((st.piles a').faceUp) = some t.twin
      rw [hfa', lastOf_append_singleton]
    · intro j hj
      by_cases hja : j = a
      · exfalso
        rw [hja] at hj
        have hjb : ((st.setPile a { st.piles a with
            faceUp := below t ((st.piles a).faceUp) ++ [t] }).piles a).top
            = some t.twin := hj
        rw [setPile_piles_self] at hjb
        have hjc : lastOf (below t ((st.piles a).faceUp) ++ [t]) = some t.twin := hjb
        rw [lastOf_append_singleton] at hjc
        exact Card.twin_ne t (Option.some.inj hjc).symm
      · by_cases hja' : j = a'
        · exact hja'
        · exfalso
          rw [setPile_topOf_ne hja] at hj
          exact absurd (pile_mem_unique cttw1 (lastOf_mem hj) hTb) hja'
  rw [putRun_inr_eq hσpt]
  rw [State.exchangeTwin_eq_of_located h₁ h₂ hne]
  rw [Option.some.injEq]
  apply State.ext
  · rfl
  · funext k
    simp only []
    by_cases hk : k = a
    · rw [hk, ite_eq_left rfl]
      rw [setPile_piles_ne hne, setPile_piles_self, hS']
    · by_cases hk' : k = a'
      · rw [ite_eq_right hk, hk', ite_eq_left rfl]
        rw [setPile_piles_self, setPile_piles_ne (Ne.symm hne)]
        apply Pile.ext
        · rfl
        · rw [append_congr_right hfa' (z :: rest), List.append_assoc,
            List.cons_append, List.nil_append, hS]
      · rw [ite_eq_right hk, ite_eq_right hk']
        rw [setPile_piles_ne hk', setPile_piles_ne hk]
  · rfl
  · rfl
  · rfl

/-- One bare twin, mirror realization: from the exchanged state, thecargo rides back onto the bare host `t`, landing exactly at theoriginal state. -/
private theorem step_realize_bwd {st : State} {t : Card} {a a' : Anchor} {z : Card}
    {rest : List Card}
    (hwf : st.WF)
    (h₁ : st.pileHolding t = some a) (h₂ : st.pileHolding t.twin = some a') (hne : a ≠ a')
    (hS : aboveIn t ((st.piles a).faceUp) = z :: rest)
    (hS' : aboveIn t.twin ((st.piles a').faceUp) = []) :
    (st.exchangeTwin t).step (Move.tabToTab z (Sum.inr t)) = some st := by
  obtain ⟨hf, hr, hc, hd⟩ := hwf
  have hTa : t ∈ (st.piles a).faceUp := pileHolding_mem h₁
  have hTb : t.twin ∈ (st.piles a').faceUp := pileHolding_mem h₂
  have cz1 := hc z (Card.mem_universe z)
  have ct1 := hc t (Card.mem_universe t)
  have cttw1 := hc t.twin (Card.mem_universe t.twin)
  have hfa : (st.piles a).faceUp = below t ((st.piles a).faceUp) ++
      t :: (z :: rest) := by
    have h := below_aboveIn_split hTa
    rw [hS] at h
    exact h
  have hfa' : (st.piles a').faceUp = below t.twin ((st.piles a').faceUp) ++
      t.twin :: [] := by
    have h := below_aboveIn_split hTb
    rw [hS'] at h
    exact h
  have hjt : canSitOn z t = true := runOK_joint_of_splice (h := by
    rw [← hfa]
    exact hr a)
  have hzt : z ≠ t := ne_of_canSitOn hjt
  have hfit : canSitOn z t.twin = true := by
    rw [show t.twin = {t with suit := t.suit.twin} from rfl, canSitOn_twin_right z t]
    exact hjt
  have hzttw : z ≠ t.twin := ne_of_canSitOn hfit
  have hZfa : z ∈ (st.piles a).faceUp := by
    have := aboveIn_subset_mem (l := (st.piles a).faceUp) (x := z)
      (show z ∈ aboveIn t ((st.piles a).faceUp) from by rw [hS]; exact List.mem_cons_self ..)
    exact this
  have hZP1 : z ∉ below t ((st.piles a).faceUp) := fun hmemb => by
    have h2 : 2 ≤ ccn z ((st.piles a).hidden ++ (st.piles a).faceUp) := by
      have hcut : ccn z ((st.piles a).faceUp) =
          ccn z (below t ((st.piles a).faceUp)) + ccn z (t :: z :: rest) := by
        rw [ccn_congr hfa z, ccn_split]
      have e1 : 1 ≤ ccn z (below t ((st.piles a).faceUp)) := ccn_pos hmemb
      have e2 : 1 ≤ ccn z (t :: z :: rest) := by
        rw [ccn_cons]
        have h3 : 1 ≤ ccn z (z :: rest) := by
          rw [ccn_cons]
          have e2' : 1 ≤ ccn z [z] := by simp [ccn]
          omega
        omega
      have hA : 2 ≤ ccn z ((st.piles a).faceUp) := by
        rw [hcut]
        omega
      have hz : ccn z ((st.piles a).hidden ++ (st.piles a).faceUp) =
          ccn z ((st.piles a).hidden) + ccn z ((st.piles a).faceUp) := ccn_split z _ _
      omega
    have := cardCount_ge_of_zone (Anchor.mem_all a) h2
    omega
  have hZP2 : z ∉ below t.twin ((st.piles a').faceUp) := fun hmemb => by
    exact absurd (pile_mem_unique cz1 hZfa (below_subset_mem hmemb)) (fun hcon => hne hcon)
  -- cardCount hygiene carried through the exchange
  have cz1' : (st.exchangeTwin t).cardCount z = 1 := by
    rw [State.exchangeTwin_cardCount h₁ h₂ hne z]
    exact cz1
  -- the exchanged state's pile a hosts the bare `t` face up
  have hσza : z ∈ ((st.exchangeTwin t).piles a').faceUp := by
    rw [State.exchangeTwin_pile_other h₁ h₂ hne, hS]
    exact List.mem_append.mpr (Or.inr (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
  have hphz : (st.exchangeTwin t).pileHolding z = some a' := by
    apply pileHolding_eq_of_unique
    · exact Anchor.mem_all a'
    · exact hσza
    · intro j hj
      cases hde : decide (j = a') with
      | true => exact of_decide_eq_true hde
      | false =>
          exfalso
          have hja' : j ≠ a' := fun hcon => by
            have := decide_eq_true hcon
            rw [hde] at this
            exact absurd this (by simp)
          by_cases hja : j = a
          · rw [hja] at hj
            rw [State.exchangeTwin_pile_self h₁ h₂ hne, hS'] at hj
            rcases List.mem_append.mp hj with hlow | hup
            · exact absurd hlow hZP1
            · rcases List.mem_cons.mp hup with heq | hsuf
              · exact absurd heq hzt
              · exact absurd hsuf (by simp)
          · rw [State.exchangeTwin_pile_ne h₁ h₂ hne hja hja'] at hj
            exact absurd (pile_mem_unique cz1 hZfa hj) (fun hcon => hja hcon.symm)
  -- the exchanged state's pile a tops at the bare host `t`
  have htopa : (st.exchangeTwin t).topOf a = some t := by
    show lastOf (((st.exchangeTwin t).piles a).faceUp) = some t
    rw [State.exchangeTwin_pile_self h₁ h₂ hne, hS']
    show lastOf (below t ((st.piles a).faceUp) ++ [t]) = some t
    exact lastOf_append_singleton _ _
  have hpta : (st.exchangeTwin t).pileOfTop t = some a := by
    apply pileOfTop_eq_of_unique
    · exact Anchor.mem_all a
    · exact htopa
    · intro j hj
      cases hde : decide (j = a) with
      | true => exact of_decide_eq_true hde
      | false =>
          exfalso
          have hja : j ≠ a := fun hcon => by
            have := decide_eq_true hcon
            rw [hde] at this
            exact absurd this (by simp)
          by_cases hja' : j = a'
          · rw [hja'] at hj
            have hjb : ((st.exchangeTwin t).piles a').top = some t := hj
            rw [State.exchangeTwin_pile_other h₁ h₂ hne, hS] at hjb
            rcases List.mem_append.mp (lastOf_mem hjb) with hlow | hup
            · -- t inside the twin host's below: doubles t
              exact absurd (pile_mem_unique ct1 hTa
                (below_subset_mem hlow)) (fun hcon => hne hcon)
            · rcases List.mem_cons.mp hup with heq | hsuf
              · exact absurd heq (fun hcon => Card.twin_ne t hcon.symm)
              · rcases List.mem_cons.mp hsuf with heq | hrest
                · exact absurd heq.symm hzt
                · have hm : t ∈ aboveIn t ((st.piles a).faceUp) := by
                    rw [hS]
                    exact List.mem_cons_of_mem _ hrest
                  exact absurd hm (not_mem_own_aboveIn ct1 hTa)
          · exfalso
            have hjb : ((st.exchangeTwin t).piles j).top = some t := hj
            rw [State.exchangeTwin_pile_ne h₁ h₂ hne hja hja'] at hjb
            exact absurd (pile_mem_unique ct1 (lastOf_mem hjb) hTa) hja
  -- placement and searches at the exchanged state
  have hcp : (st.exchangeTwin t).canPlace z (Sum.inr t) = true := by
    rw [canPlace_inr_eq hpta]
    exact hjt
  have hrun : fromCard z (((st.exchangeTwin t).piles a').faceUp) = z :: rest := by
    rw [State.exchangeTwin_pile_other h₁ h₂ hne]
    simp only []
    rw [hS, fromCard_append_notmem hZP2, fromCard_cons_ne _ (fun hcon => hzttw hcon.symm),
      fromCard_cons_self]
  have hpre : below z (((st.exchangeTwin t).piles a').faceUp) =
      below t.twin ((st.piles a').faceUp) ++ [t.twin] := by
    rw [State.exchangeTwin_pile_other h₁ h₂ hne]
    simp only []
    rw [hS, below_append_notmem hZP2, below_cons_ne _ (fun hcon => hzttw hcon.symm),
      below_cons_self]
  have hprene : below t.twin ((st.piles a').faceUp) ++ [t.twin] ≠ [] := by
    intro hc
    cases hb : below t.twin ((st.piles a').faceUp) with
    | nil =>
        rw [hb] at hc
        simp at hc
    | cons w ws =>
        rw [hb] at hc
        simp at hc
  -- unfold the mirrored step
  rw [step_tabToTab_eq hphz hcp hrun, hpre, afterRunRemoved_ne hprene]
  -- intermediate: the twin host pile back to bare; the cargo rides
  -- back onto the bare host `t`
  have hσpt : ((st.exchangeTwin t).setPile a'
        ⟨((st.exchangeTwin t).piles a').hidden,
          below t.twin ((st.piles a').faceUp) ++ [t.twin]⟩).pileOfTop t = some a := by
    apply pileOfTop_eq_of_unique
    · exact Anchor.mem_all a
    · rw [setPile_topOf_ne hne]
      show lastOf ((st.exchangeTwin t).piles a).faceUp = some t
      rw [State.exchangeTwin_pile_self h₁ h₂ hne, hS']
      show lastOf (below t ((st.piles a).faceUp) ++ [t]) = some t
      exact lastOf_append_singleton _ _
    · intro j hj
      by_cases hja : j = a
      · exact hja
      · exfalso
        by_cases hja' : j = a'
        · rw [hja'] at hj
          have hjb : (((st.exchangeTwin t).setPile a'
                ⟨((st.exchangeTwin t).piles a').hidden,
                  below t.twin ((st.piles a').faceUp) ++ [t.twin]⟩).piles a').top
              = some t := hj
          rw [setPile_piles_self] at hjb
          have hjc : lastOf (below t.twin ((st.piles a').faceUp) ++ [t.twin]) = some t := hjb
          rw [lastOf_append_singleton] at hjc
          exact Card.twin_ne t (Option.some.inj hjc)
        · rw [setPile_topOf_ne hja'] at hj
          have hjb : ((st.exchangeTwin t).piles j).top = some t := hj
          rw [State.exchangeTwin_pile_ne h₁ h₂ hne hja hja'] at hjb
          exact absurd (pile_mem_unique ct1 (lastOf_mem hjb) hTa) hja
  rw [putRun_inr_eq hσpt]
  rw [Option.some.injEq]
  -- final congruence: the mirrored construction is the original state
  apply State.ext
  · show (st.exchangeTwin t).found = st.found
    rw [State.exchangeTwin_found]
  · funext k
    simp only []
    by_cases hk : k = a
    · rw [hk]
      rw [setPile_piles_self, setPile_piles_ne hne]
      rw [State.exchangeTwin_pile_self h₁ h₂ hne, hS']
      apply Pile.ext
      · rfl
      · show (below t ((st.piles a).faceUp) ++ [t]) ++ (z :: rest) = (st.piles a).faceUp
        rw [show (below t ((st.piles a).faceUp) ++ [t]) ++ (z :: rest) =
              below t ((st.piles a).faceUp) ++ (t :: z :: rest) from
            (List.append_assoc _ _ _).trans (by rw [List.cons_append, List.nil_append])]
        exact hfa.symm
    · by_cases hk' : k = a'
      · rw [hk']
        rw [setPile_piles_ne (Ne.symm hne), setPile_piles_self]
        rw [State.exchangeTwin_pile_other h₁ h₂ hne]
        apply Pile.ext
        · rfl
        · show below t.twin ((st.piles a').faceUp) ++ [t.twin] = (st.piles a').faceUp
          rw [← hfa']
      · rw [setPile_piles_ne hk, setPile_piles_ne hk']
        exact State.exchangeTwin_pile_ne h₁ h₂ hne hk hk'
  · show (st.exchangeTwin t).stock = st.stock
    rw [State.exchangeTwin_stock]
  · show (st.exchangeTwin t).waste = st.waste
    rw [State.exchangeTwin_waste]
  · show (st.exchangeTwin t).drawStep = st.drawStep
    rw [State.exchangeTwin_drawStep]

/-- The bare-twin iff, core orientation: the cargo sits above `t`and the twin host is bare. -/
private theorem bare_iff_core {st : State} {t : Card} {a a' : Anchor} {z : Card}
    {rest : List Card}
    (hwf : st.WF)
    (h₁ : st.pileHolding t = some a) (h₂ : st.pileHolding t.twin = some a') (hne : a ≠ a')
    (hS : aboveIn t ((st.piles a).faceUp) = z :: rest)
    (hS' : aboveIn t.twin ((st.piles a').faceUp) = []) :
    (WinFrom st ↔ WinFrom (st.exchangeTwin t)) := by
  have h1 := step_realize_fwd hwf h₁ h₂ hne hS hS'
  have h2 := step_realize_bwd hwf h₁ h₂ hne hS hS'
  constructor
  · intro hwin
    exact WinFrom_of_succ ⟨_, h2⟩ hwin
  · intro hwin
    exact WinFrom_of_succ ⟨_, h1⟩ hwin

/-- **The bare-twin iff.**
  At a well-formed state where the twin pair`t`, `t.twin` sits face-up in distinct piles and at least one host isbare (nothing above it), the local twin exchange preserves the verdict:`st` is winning iff the exchanged state is.
  One direction realizesthe move through `State.step` as a plain `Move.tabToTab` of the cargoonto the bare host, the other direction as its mirror.
  Theboth-bare case is the identity. -/
theorem twin_exchange_bare_iff {st : State} {t : Card} {a a' : Anchor}
    (hwf : st.WF)
    (h₁ : st.pileHolding t = some a) (h₂ : st.pileHolding t.twin = some a')
    (hne : a ≠ a')
    (hbare : aboveIn t ((st.piles a).faceUp) = [] ∨
      aboveIn t.twin ((st.piles a').faceUp) = []) :
    WinFrom st ↔ WinFrom (st.exchangeTwin t) := by
  cases hL : aboveIn t ((st.piles a).faceUp) with
  | nil =>
      cases hR : aboveIn t.twin ((st.piles a').faceUp) with
      | nil =>
          rw [State.exchangeTwin_eq_self_of_both_bare h₁ h₂ hne hL hR]
      | cons z rest =>
          -- the mirror orientation: ask at the twin, then the pair law
          have := bare_iff_core (st := st) (t := t.twin) (a := a') (a' := a)
            (hwf := hwf) (h₁ := h₂)
            (h₂ := by rw [Card.twin_twin]; exact h₁)
            (hne := fun hc => hne hc.symm)
            (hS := hR)
            (hS' := by rw [Card.twin_twin]; exact hL)
          rw [State.exchangeTwin_pair st t] at this
          exact this
  | cons z rest =>
      cases hR : aboveIn t.twin ((st.piles a').faceUp) with
      | nil =>
          exact bare_iff_core hwf h₁ h₂ hne hL hR
      | cons w ws =>
          -- both suffixes nonempty contradicts the bareness premise
          rcases hbare with hb | hb
          · rw [hL] at hb
            exact absurd hb (by simp)
          · rw [hR] at hb
            exact absurd hb (by simp)