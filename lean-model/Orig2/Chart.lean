import Orig2.Kit

/-!
# Orig2.Chart — THE CHART BOOK'S DISCHARGE CARD (the §1E claims
ledger's first landings, 2026-10-18)

WHAT THIS FILE IS: the discharge home for the chart book's CUT row
(`chart_draw`, discharged VERBATIM — the ungated stub is true) and the
book's keystone (`chart_round_trip`, discharged RE-GATED — the ungated
stub is FALSE at wild states, refuted here by a compiled kernel
witness, `chart_round_trip_ungated_false`, and re-landed at the
WF-both-sides grade per the 2026-10-17 `chart_tabToTab` precedent).

## THE RE-GATING PROVENANCE (2026-10-18)

The ledger's original stub read `chartAgree st w → st = w`, ungated.
The witness below kills it: the seat search (`pileHolding`) stops at
a card's FIRST face-up pile, so in any LATER pile a card is
CHART-MASKED — a duplicated card value in a late pile (or a second
copy within the same pile after its first occurrence) changes no
readout: seats, hidden decks, foundations, pool and cut all agree
while the face-up lists differ.  (The kernel pair of
`chart_round_trip_ungated_false` is the two-card wild board with the
late pile's order swapped.)  WF on BOTH sides kills exactly this:
occurrence uniqueness makes every face-up occurrence the first, so
the seat map reads every placement.  The discharged statement carries
`st.WF` and `w.WF` as honest premises.

DEBT-LINKAGE CONSEQUENCE (recorded for the floater books): their
hoists read `∀ A B, chartAgree A B → A = B` ungated, with the
mate-side WF not derivable from the spec — the hoists do NOT drop
verbatim; they await their own re-gating (the honest `SeatEdit`
consumption needs the mate's WF as a premise, cf. the wild doppel-
:ra gänger analysis in the ledger note dated 2026-10-18).

## ROWS

* `chart_round_trip_ungated_false` — the kernel refutation (fence);
* `chart_round_trip` — the re-gated keystone: states ARE their
  readouts whenever both are WF;
* `chart_draw` — the CUT row, discharged exactly as stated: the
  draw moves the cut alone, the pool conserved, no pair change.

## THE METHOD (private kit, per the closed-seam discipline — every
frozen/certified home cited at its row)

The below/fromCard split-calculus (`Orig2/Classification.lean:1383`,
frozen `Orig/Classify.lean:282`; the CargoKit ports at §B/§E2), the
lastOf/getLast? bridge and the seat unpacks
(`Orig2/CargoKit.lean:305,:312,:1186-1283`), the occurrence-count kit
(`Orig2/CargoKit.lean §A`, frozen `Orig/Reach.lean:131-329`), the
draw field-keepers (`Orig2/Kit.lean §1d`), and the dealUpTo split
(frozen template `Orig/Canonical.lean:2619 draw_pool_keep`).  The
keystone's engine is ONE induction: a card's below-profile (its
position data) transfers to any chart-mate at the same anchor,
position by position — the WF occurrence kill feeding every step —
and the below-profile at the TOP card pins the whole face-up list.

IMPORT SURFACE: exactly `Orig2.Kit` (hence `Orig2.Vocab`, hence the
certified core seam).  House compliance: zero sorry, zero
`Classical.choice`; the audit battery at the tail.
-/

/-! ## §1. The below/fromCard calculus

The split pair (`below`/`fromCard`) is the position calculus: `below`
is the strict prefix before a card's first occurrence, `fromCard`
the run from it. -/

/-- The cons row for the run locator (PORT of `Orig2/CargoKit.lean:333`,
frozen `Orig/Reach.lean:357`). -/
private theorem chk_fromCard_cons (c x : Card) (t : List Card) :
    fromCard c (x :: t) = if x = c then x :: t else fromCard c t := rfl

/-- THE SPLIT IDENTITY: a list is its below-plus-run (PORT of
`Orig2/CargoKit.lean:338` via `Orig2/Classification.lean:1383`,
frozen `Orig/Classify.lean:282`). -/
private theorem chk_below_fromCard (c : Card) : ∀ (l : List Card),
    below c l ++ fromCard c l = l := by
  intro l
  induction l with
  | nil => rfl
  | cons x t ih =>
      rw [below_cons, chk_fromCard_cons]
      by_cases hxc : x = c
      · rw [ite_eq_left hxc, ite_eq_left hxc, List.nil_append]
      · rw [ite_eq_right hxc, ite_eq_right hxc]
        exact congrArg (x :: ·) ih

/-- `below` never hosts its own card (fresh; the first occurrence
truncates). -/
private theorem chk_below_not_mem (c : Card) : ∀ (l : List Card), c ∉ below c l := by
  intro l
  induction l with
  | nil => intro h; exact absurd h (by simp [below])
  | cons x t ih =>
      intro h
      rw [below_cons] at h
      by_cases hxc : x = c
      · rw [ite_eq_left hxc] at h; exact absurd h List.not_mem_nil
      · rw [ite_eq_right hxc] at h
        rcases List.mem_cons.mp h with h' | h'
        · exact hxc h'.symm
        · exact ih h'

/-- A member host absorbs the tail: below reads only to the first
occurrence (fresh). -/
private theorem chk_below_absorb (c : Card) :
    ∀ (X Y : List Card), c ∈ X → below c (X ++ Y) = below c X := by
  intro X
  induction X with
  | nil => intro Y h; exact absurd h List.not_mem_nil
  | cons x t ih =>
      intro Y h
      rw [List.cons_append, below_cons, below_cons]
      by_cases hxc : x = c
      · rw [ite_eq_left hxc, ite_eq_left hxc]
      · rw [ite_eq_right hxc, ite_eq_right hxc]
        rcases List.mem_cons.mp h with h' | h'
        · exact absurd h'.symm hxc
        · rw [ih Y h']

/-- A clear host extends verbatim (fresh). -/
private theorem chk_below_extend (c : Card) :
    ∀ (X Y : List Card), c ∉ X → below c (X ++ Y) = X ++ below c Y := by
  intro X
  induction X with
  | nil => intro Y _; rfl
  | cons x t ih =>
      intro Y h
      have hxc : x ≠ c := fun hxx =>
        h (by rw [← hxx]; exact List.mem_cons_self)
      rw [List.cons_append, below_cons, ite_eq_right hxc,
        ih Y (fun h' => h (List.mem_cons_of_mem _ h')), List.cons_append]

/-- Every member splits its host (fresh). -/
private theorem chk_mem_split {x : Card} :
    ∀ (l : List Card), x ∈ l → ∃ A B, l = A ++ x :: B := by
  intro l
  induction l with
  | nil => intro h; exact absurd h List.not_mem_nil
  | cons y t ih =>
      intro h
      rcases List.mem_cons.mp h with h' | h'
      · refine ⟨[], t, ?_⟩
        rw [List.nil_append]
        exact congrArg (· :: t) h'.symm
      · obtain ⟨A, B, hAB⟩ := ih h'
        refine ⟨y :: A, B, ?_⟩
        rw [List.cons_append]
        exact congrArg (y :: ·) hAB

/-! ## §2. The lastOf/getLast? bridge and the seat unpacks -/

/-- `getLast?` IS the house `lastOf` (PORT of `Orig2/CargoKit.lean:305`). -/
private theorem chk_getLast?_lastOf : ∀ (l : List Card), l.getLast? = lastOf l := by
  intro l
  cases l with
  | nil => rfl
  | cons x t =>
      cases t with
      | nil => rfl
      | cons y t' => exact chk_getLast?_lastOf (y :: t')

/-- The last of an append with nonempty tail reads the tail (PORT of
`Orig2/CargoKit.lean:312`, pattern `Orig/Classify.lean:195`). -/
private theorem chk_lastOf_append_ne : ∀ (A : List Card) {r : List Card},
    r ≠ [] → lastOf (A ++ r) = lastOf r := by
  intro A
  induction A with
  | nil => intro r _; rfl
  | cons x t ih =>
      intro r hr
      have hne : t ++ r ≠ [] := by
        intro hc
        have hl := congrArg List.length hc
        rw [List.length_append, List.length_nil] at hl
        exact hr (List.length_eq_zero_iff.mp (show r.length = 0 by omega))
      have hlast : lastOf (x :: (t ++ r)) = lastOf (t ++ r) := by
        obtain ⟨y, ys, hc⟩ := list_cons_of_ne_nil hne
        rw [hc]
        rfl
      rw [List.cons_append, hlast]
      exact ih hr

/-- A cons tail always answers (PORT of `Orig2/CargoKit.lean:1202`). -/
private theorem chk_lastOf_cons_ne : ∀ (t : List Card) (y : Card), lastOf (y :: t) ≠ none := by
  intro t
  induction t with
  | nil => intro y; exact (by simp [lastOf])
  | cons z t' ih =>
      intro y
      show (lastOf (y :: z :: t') = none) → False
      rw [show lastOf (y :: z :: t') = lastOf (z :: t') from rfl]
      exact ih z

/-- The seat map raw unfold (PORT of `Orig2/CargoKit.lean:1180`). -/
private theorem chk_seatOf_eq (st : State) (c : Card) :
    seatOf st c =
      match st.pileHolding c with
      | none => none
      | some a => match List.getLast? (below c (st.piles a).faceUp) with
        | none => some (Sum.inl a)
        | some z => some (Sum.inr z) := rfl

/-- No holding pile: no seat (PORT of `Orig2/CargoKit.lean:1186`). -/
private theorem chk_seatOf_none {st : State} {c : Card} (hh : st.pileHolding c = none) :
    seatOf st c = none := by rw [chk_seatOf_eq, hh]

/-- The located pair form (PORT of `Orig2/CargoKit.lean:1192`). -/
private theorem chk_seatOf_pair {st : State} {c : Card} {a : Anchor}
    (hh : st.pileHolding c = some a) :
    seatOf st c = match List.getLast? (below c (st.piles a).faceUp) with
      | none => some (Sum.inl a)
      | some z => some (Sum.inr z) := by rw [chk_seatOf_eq, hh]

/-- The `.inl` unpack (PORT of `Orig2/CargoKit.lean:1241`). -/
private theorem chk_seatOf_of_inl {st : State} {c : Card} {a : Anchor}
    (h : seatOf st c = some (Sum.inl a)) :
    st.pileHolding c = some a ∧ below c (st.piles a).faceUp = [] := by
  rw [chk_seatOf_eq] at h
  cases hh : st.pileHolding c with
  | none =>
      rw [hh] at h
      exact absurd h (by simp)
  | some a₀ =>
      simp only [hh] at h
      cases hg : List.getLast? (below c (st.piles a₀).faceUp) with
      | some q =>
          rw [hg] at h
          exact absurd h (by simp)
      | none =>
          simp only [hg] at h
          have haeq : a₀ = a := by
            injection h with h1
            cases h1
            rfl
          subst haeq
          have hbl : below c (st.piles a₀).faceUp = [] := by
            cases hc : below c (st.piles a₀).faceUp with
            | nil => rfl
            | cons y ys =>
                rw [hc, chk_getLast?_lastOf] at hg
                exact absurd hg (chk_lastOf_cons_ne _ _)
          exact ⟨rfl, hbl⟩

/-- The `.inr` unpack (PORT of `Orig2/CargoKit.lean:1212`). -/
private theorem chk_seatOf_of_inr {st : State} {c z : Card}
    (h : seatOf st c = some (Sum.inr z)) :
    ∃ a, st.pileHolding c = some a ∧ below c (st.piles a).faceUp ≠ [] ∧
      lastOf (below c (st.piles a).faceUp) = some z := by
  rw [chk_seatOf_eq] at h
  cases hh : st.pileHolding c with
  | none =>
      rw [hh] at h
      exact absurd h (by simp)
  | some a =>
      simp only [hh] at h
      cases hg : List.getLast? (below c (st.piles a).faceUp) with
      | none =>
          rw [hg] at h
          exact absurd h (by simp)
      | some q =>
          simp only [hg] at h
          have hqz : q = z := by
            injection h with h1
            cases h1
            rfl
          subst hqz
          refine ⟨a, rfl, ?_, ?_⟩
          · intro hc
            rw [hc, chk_getLast?_lastOf] at hg
            exact absurd hg (by simp [lastOf])
          · rw [chk_getLast?_lastOf] at hg
            exact hg

/-! ## §3. The occurrence-count kit

PORT (verbatim bodies) of the §A kit at `Orig2/CargoKit.lean:53-298`
plus `:232-246` — frozen lineages `Orig/Reach.lean:131-329` — the
WF-lane occurrence machinery: the count word, its additivity, the
zone decomposition of `cardCount`, and the two absurd rows the
keystone rides. -/

private def chk_cnt (c : Card) : List Card → Nat
  | [] => 0
  | x :: t => (if x = c then 1 else 0) + chk_cnt c t

private theorem chk_cnt_nil (c : Card) : chk_cnt c [] = 0 := rfl

private theorem chk_cnt_def (c x : Card) (t : List Card) :
    chk_cnt c (x :: t) = (if x = c then 1 else 0) + chk_cnt c t := rfl

/-- PORT of `Orig2/CargoKit.lean:66` (`Orig/Reach.lean:146`). -/
private theorem chk_cnt_app (c : Card) : ∀ (l₁ l₂ : List Card),
    chk_cnt c (l₁ ++ l₂) = chk_cnt c l₁ + chk_cnt c l₂ := by
  intro l₁ l₂
  induction l₁ with
  | nil => rw [List.nil_append, chk_cnt_nil]; omega
  | cons x t ih =>
      show (if x = c then 1 else 0) + chk_cnt c (t ++ l₂) = _
      rw [ih, chk_cnt_def]
      omega

/-- PORT of `Orig2/CargoKit.lean:81` (`Orig/Reach.lean:167`). -/
private theorem chk_mem_le_cnt {c : Card} : ∀ (l : List Card), c ∈ l → 1 ≤ chk_cnt c l := by
  intro l
  induction l with
  | nil => intro h; exact absurd h List.not_mem_nil
  | cons x t ih =>
      intro h
      show 1 ≤ (if x = c then 1 else 0) + chk_cnt c t
      rcases List.mem_cons.mp h with h' | h'
      · rw [ite_eq_left h'.symm]
        omega
      · have h1 : 1 ≤ chk_cnt c t := ih h'
        by_cases hx : x = c
        · rw [ite_eq_left hx]; omega
        · rw [ite_eq_right hx]; omega

/-- PORT of `Orig2/CargoKit.lean:97` (`Orig/Reach.lean:190`). -/
private theorem chk_cnt_filter (c : Card) : ∀ (l : List Card),
    chk_cnt c l = (l.filter fun x => decide (x = c)).length := by
  intro l
  induction l with
  | nil => rfl
  | cons x t ih =>
      show ((if x = c then 1 else 0) + chk_cnt c t) = _
      rw [List.filter_cons]
      by_cases hxc : x = c
      · rw [decide_eq_true hxc, ite_eq_left rfl, List.length_cons, ite_eq_left hxc, ih]
        omega
      · have hdec : (decide (x = c)) = false := by rw [decide_false_of_not hxc]
        rw [hdec, ite_eq_right (fun h => Bool.noConfusion h),
          ite_eq_right hxc, ih]
        omega

/-- PORT of `Orig2/CargoKit.lean:114` (`Orig/Reach.lean:206`). -/
private theorem chk_cardCount_eq_cnt (st : State) (c : Card) :
    st.cardCount c = chk_cnt c (st.zones.flatMap id) :=
  (chk_cnt_filter c (st.zones.flatMap id)).symm

private def chk_cntFlat (c : Card) : List (List Card) → Nat
  | [] => 0
  | z :: zs => chk_cnt c z + chk_cntFlat c zs

private theorem chk_cntFlat_cons (c : Card) (z : List Card) (zs : List (List Card)) :
    chk_cntFlat c (z :: zs) = chk_cnt c z + chk_cntFlat c zs := rfl

/-- PORT of `Orig2/CargoKit.lean:128` (`Orig/Reach.lean:218`). -/
private theorem chk_cntFlat_flatMap (c : Card) : ∀ (zs : List (List Card)),
    chk_cntFlat c zs = chk_cnt c (zs.flatMap id) := by
  intro zs
  induction zs with
  | nil => rfl
  | cons z t ih =>
      rw [chk_cntFlat_cons, List.flatMap_cons, chk_cnt_app c, ih]
      rfl

/-- PORT of `Orig2/CargoKit.lean:190` (`Orig/Reach.lean:299`). -/
private theorem chk_flatMap_id_append : ∀ (A B : List (List Card)),
    (A ++ B).flatMap id = (A.flatMap id) ++ (B.flatMap id) := by
  intro A B
  induction A with
  | nil => rfl
  | cons z t ih =>
      show (z ++ ((t ++ B).flatMap id)) = (z ++ (t.flatMap id)) ++ (B.flatMap id)
      rw [show (t ++ B).flatMap id = (t.flatMap id) ++ (B.flatMap id) from ih]
      exact (List.append_assoc z (t.flatMap id) (B.flatMap id)).symm

/-- PORT of `Orig2/CargoKit.lean:201` (`Orig/Reach.lean:312`). -/
private theorem chk_cardCount_zones (st : State) (c : Card) :
    st.cardCount c =
      chk_cntFlat c (Suit.all.map st.found)
      + chk_cntFlat c (Anchor.all.map fun a => (st.piles a).hidden ++ (st.piles a).faceUp)
      + (chk_cnt c st.stock + chk_cnt c st.waste) := by
  rw [chk_cardCount_eq_cnt]
  have h2 : ([st.stock, st.waste] : List (List Card)).flatMap id
      = st.stock ++ st.waste :=
    congrArg (st.stock ++ ·) (List.append_nil st.waste)
  show chk_cnt c ((Suit.all.map st.found ++ (Anchor.all.map
      (fun a => (st.piles a).hidden ++ (st.piles a).faceUp) ++ [st.stock, st.waste])).flatMap id) = _
  rw [chk_flatMap_id_append, chk_flatMap_id_append, h2, chk_cnt_app c, chk_cnt_app c,
    chk_cnt_app c, chk_cntFlat_flatMap c, chk_cntFlat_flatMap c]
  omega

/-- PORT of `Orig2/CargoKit.lean:218`. -/
private theorem chk_cntFlat_list_mem_ge {c : Card} {zn : List Card} :
    ∀ (zs : List (List Card)), zn ∈ zs → chk_cnt c zn ≤ chk_cntFlat c zs := by
  intro zs
  induction zs with
  | nil => intro hmem; exact absurd hmem (by simp)
  | cons z t ih =>
      intro hmem
      rcases List.mem_cons.mp hmem with h' | h'
      · rw [h']
        exact Nat.le_add_right _ _
      · have h1 : chk_cnt c zn ≤ chk_cntFlat c t := ih h'
        show chk_cnt c zn ≤ chk_cnt c z + chk_cntFlat c t
        omega

/-- PORT of `Orig2/CargoKit.lean:249` (`Orig/Reach.lean:1569`). -/
private theorem chk_cntFlat_map_ge1 {α : Type} {z : Card} (F : α → List Card) :
    ∀ (L : List α) (b : α), b ∈ L → z ∈ F b → 1 ≤ chk_cntFlat z (L.map F) := by
  intro L
  induction L with
  | nil => intro b h; exact absurd h List.not_mem_nil
  | cons x t ih =>
      intro b hmem hz
      rw [List.map_cons, chk_cntFlat_cons]
      rcases List.mem_cons.mp hmem with h' | h'
      · rw [h'] at hz
        have := chk_mem_le_cnt _ hz
        omega
      · have := ih b h' hz
        omega

/-- PORT of `Orig2/CargoKit.lean:265` (`Orig/Reach.lean:1586`). -/
private theorem chk_cntFlat_map_two_mem {α : Type} {z : Card} (F : α → List Card) :
    ∀ (L : List α) (b₁ b₂ : α), b₁ ∈ L → b₂ ∈ L → b₁ ≠ b₂ →
      z ∈ F b₁ → z ∈ F b₂ → 2 ≤ chk_cntFlat z (L.map F) := by
  intro L
  induction L with
  | nil => intro b₁ b₂ h₁; exact absurd h₁ List.not_mem_nil
  | cons x t ih =>
      intro b₁ b₂ h₁ h₂ hne hz₁ hz₂
      rw [List.map_cons, chk_cntFlat_cons]
      rcases List.mem_cons.mp h₁ with h₁' | h₁'
      · rw [h₁'] at hne hz₁
        rcases List.mem_cons.mp h₂ with h₂' | h₂'
        · exact absurd h₂'.symm hne
        · have e₁ : 1 ≤ chk_cnt z (F x) := chk_mem_le_cnt _ hz₁
          have e₂ : 1 ≤ chk_cntFlat z (List.map F t) := chk_cntFlat_map_ge1 F t b₂ h₂' hz₂
          omega
      · rcases List.mem_cons.mp h₂ with h₂' | h₂'
        · rw [h₂'] at hz₂
          have e₂ : 1 ≤ chk_cnt z (F x) := chk_mem_le_cnt _ hz₂
          have e₁ : 1 ≤ chk_cntFlat z (List.map F t) := chk_cntFlat_map_ge1 F t b₁ h₁' hz₁
          omega
        · have := ih b₁ b₂ h₁' h₂' hne hz₁ hz₂
          omega

/-- PORT of `Orig2/CargoKit.lean:290` (`Orig/Reach.lean:1612`). -/
private theorem chk_two_pile_zone_absurd {st : State} {z : Card} {j k : Anchor} (hjk : j ≠ k)
    (hcc : st.cardCount z = 1)
    (hzj : z ∈ (st.piles j).hidden ++ (st.piles j).faceUp)
    (hzk : z ∈ (st.piles k).hidden ++ (st.piles k).faceUp) : False := by
  rw [chk_cardCount_zones] at hcc
  have h2 := chk_cntFlat_map_two_mem
    (fun a => (st.piles a).hidden ++ (st.piles a).faceUp) Anchor.all j k
    (Anchor.mem_all j) (Anchor.mem_all k) hjk hzj hzk
  omega

/-- PORT of `Orig2/CargoKit.lean:234`. -/
private theorem chk_faceUp_cnt_le_cardCount {st : State} {x : Card} {a : Anchor} :
    chk_cnt x (st.piles a).faceUp ≤ st.cardCount x := by
  have h1 : chk_cnt x (st.piles a).faceUp
      ≤ chk_cnt x ((st.piles a).hidden ++ (st.piles a).faceUp) := by
    rw [chk_cnt_app x]
    omega
  have h2 : chk_cnt x ((st.piles a).hidden ++ (st.piles a).faceUp)
      ≤ chk_cntFlat x (Anchor.all.map fun a' => (st.piles a').hidden ++ (st.piles a').faceUp) :=
    chk_cntFlat_list_mem_ge
      (Anchor.all.map fun a' => (st.piles a').hidden ++ (st.piles a').faceUp)
      (List.mem_map.2 ⟨a, Anchor.mem_all a, rfl⟩)
  have h3 := chk_cardCount_zones st x
  omega

/-- PORT of `Orig2/CargoKit.lean:1531`, re-parameterized at the
occurrence grade (the load-bearing extraction; the frozen home is
WF-gated but consumes exactly this row). -/
private theorem chk_two_mem_faceUp_absurd {st : State}
    (hcc : ∀ c, st.cardCount c = 1) {x : Card} {a : Anchor}
    {L R : List Card} (hsplit : (st.piles a).faceUp = L ++ R)
    (hl : x ∈ L) (hr : x ∈ R) : False := by
  have h0 : st.cardCount x = 1 := hcc x
  have h1 : 1 ≤ chk_cnt x L := chk_mem_le_cnt _ hl
  have h2 : 1 ≤ chk_cnt x R := chk_mem_le_cnt _ hr
  have h3 : chk_cnt x (L ++ R) = chk_cnt x L + chk_cnt x R := chk_cnt_app x L R
  have h4 : chk_cnt x (st.piles a).faceUp ≤ st.cardCount x :=
    chk_faceUp_cnt_le_cardCount
  rw [hsplit, h3] at h4
  omega

/-! ## §4. The search pins

The holding search's decline inversion and the WF holding pin
(`Orig2/CargoKit.lean:1505-1527`). -/

/-- A firstWhere that fails declines everything (fresh inversion;
the pack `Orig/State.lean:40`). -/
private theorem chk_firstWhere_none_inv {α : Type} (p : α → Bool) :
    ∀ (l : List α), firstWhere p l = none → ∀ j ∈ l, p j = false := by
  intro l
  induction l with
  | nil => intro _ j hj; exact absurd hj (by simp)
  | cons x t ih =>
      intro h j hj
      have hred : (match p x with
          | true => some x
          | false => firstWhere p t) = none := by
        show firstWhere p (x :: t) = none
        rw [h]
      cases hp : p x with
      | true => rw [hp] at hred; exact absurd hred (by simp)
      | false =>
          rw [hp] at hred
          have : firstWhere p t = none := by
            simpa only using hred
          rcases List.mem_cons.mp hj with rfl | hj'
          · exact hp
          · exact ih this j hj'

/-- THE HOLDING PIN: at occurrence-unique boards, the face-up member's
search answer is its pile (`Orig2/CargoKit.lean:1516`, pattern
`Orig2/Integrity.lean`'s `wf_two_piles_ne`; re-parameterized at the
occurrence grade — the extraction is the only WF use). -/
private theorem chk_holding_pin {st : State} (hcc : ∀ c, st.cardCount c = 1)
    {c : Card} {a : Anchor}
    (hmem : c ∈ (st.piles a).faceUp) : st.pileHolding c = some a := by
  cases hh : st.pileHolding c with
  | some q =>
      by_cases hqa : q = a
      · exact congrArg some hqa
      · exfalso
        have hccx : st.cardCount c = 1 := hcc c
        have hm : c ∈ (st.piles q).faceUp := pileHolding_mem hh
        exact chk_two_pile_zone_absurd hqa hccx
          (List.mem_append.mpr (Or.inr hm))
          (List.mem_append.mpr (Or.inr hmem))
  | none =>
      exfalso
      have hdev : ∀ j ∈ Anchor.all, decide (c ∈ (st.piles j).faceUp) = false :=
        chk_firstWhere_none_inv _ Anchor.all hh
      have hdx := hdev a (Anchor.mem_all a)
      rw [decide_eq_true hmem] at hdx
      exact Bool.noConfusion hdx

/-! ## §5. The seat congruence between pile-equal states -/

/-- Full seat agreement is a pile congruence (fresh). -/
private theorem chk_seatOf_congr {S T : State} (hp : T.piles = S.piles) (c : Card) :
    seatOf T c = seatOf S c := by
  have hh : T.pileHolding c = S.pileHolding c := pileHolding_congr hp
  have hf : ∀ a, (T.piles a).faceUp = (S.piles a).faceUp :=
    fun a => congrArg Pile.faceUp (congrFun hp a)
  cases hq : S.pileHolding c with
  | none =>
      have hT : T.pileHolding c = none := by rw [hh, hq]
      rw [chk_seatOf_none hT, chk_seatOf_none hq]
  | some a =>
      have hT : T.pileHolding c = some a := by rw [hh, hq]
      have hbl : below c (T.piles a).faceUp = below c (S.piles a).faceUp := by rw [hf a]
      cases hb : below c (S.piles a).faceUp with
      | nil =>
          have hbT : below c (T.piles a).faceUp = [] := by rw [hbl, hb]
          rw [chk_seatOf_pair hT, hbT, chk_seatOf_pair hq, hb]
      | cons x xs =>
          have hbT : below c (T.piles a).faceUp = x :: xs := by rw [hbl, hb]
          rw [chk_seatOf_pair hT, hbT, chk_seatOf_pair hq, hb]

/-! ## §6. THE CUT ROW -/

/-- THE SPLIT: dealing is an ordered split (fresh constructive row;
frozen template `Orig/Canonical.lean:2619 draw_pool_keep`). -/
private theorem chk_dealUpTo_split (k : Nat) : ∀ (l : List Card),
    (State.dealUpTo k l).1 ++ (State.dealUpTo k l).2 = l := by
  induction k with
  | zero => intro l; rfl
  | succ k ih =>
      intro l
      cases l with
      | nil => rfl
      | cons x t => exact congrArg (x :: ·) (ih t)

/-- **CLAIM `chart_draw` DISCHARGED** — the CUT row, exactly as the
ledger states it: no pair change, no foundation change, the pool
conserved; only the split moves.  The record congruence is the
`draw_footprint` fold (`Orig2/Kit.lean` §1d); the pool clause is one
dealUpTo-split computation plus the recycle cases; the seam template
cited in the ledger's §1E PRICE holds. -/
theorem chart_draw {st s' : State}
    (hstep : State.step st Move.draw = some s') :
    (∀ c, seatOf s' c = seatOf st c) ∧ foundsFixed st s' ∧
    boardFixed st s' ∧ drawPool st = drawPool s' := by
  have hsd : st.stepDraw = some s' := by
    have h0 : State.step st Move.draw = st.stepDraw := rfl
    rw [h0] at hstep
    exact hstep
  have hfoot := draw_footprint hsd
  have hpiles : s'.piles = st.piles := hfoot.2.2.1
  have hfound : s'.found = st.found := hfoot.2.1
  have hds : s'.drawStep = st.drawStep := hfoot.1
  refine ⟨chk_seatOf_congr hpiles, ?_, ?_, ?_⟩
  · intro s0
    exact congrFun hfound.symm s0
  · refine ⟨fun a => ?_, hds.symm⟩
    have hpa : st.piles a = s'.piles a := congrFun hpiles.symm a
    rw [hpa]
  · obtain ⟨r, hrdef, hrne, hs'⟩ := draw_unfold hsd
    have hsplit : (State.dealUpTo r.drawStep r.stock).1 ++
        (State.dealUpTo r.drawStep r.stock).2 = r.stock :=
      chk_dealUpTo_split _ _
    have hdrool : drawPool s' = r.stock.reverse ++ r.waste := by
      show s'.stock.reverse ++ s'.waste = r.stock.reverse ++ r.waste
      rw [hs']
      show ((State.dealUpTo r.drawStep r.stock).2).reverse ++
          (((State.dealUpTo r.drawStep r.stock).1).reverse ++ r.waste) = _
      rw [← List.append_assoc, ← List.reverse_append, hsplit]
    have hpoolr : drawPool r = drawPool st := by
      cases hs : st.stock with
      | nil =>
          cases hw : st.waste with
          | nil =>
              exfalso
              rw [← hrdef, recycle_allEmpty st hs hw] at hrne
              exact hrne hs
          | cons x xs =>
              rw [← hrdef, recycle_nil st hs (by rw [hw]; exact List.cons_ne_nil x xs)]
              show (st.waste.reverse).reverse ++ ([] : List Card)
                = st.stock.reverse ++ st.waste
              rw [hs, hw, List.reverse_reverse, List.append_nil]
              rfl
      | cons y ys =>
          rw [← hrdef, recycle_keep st (by rw [hs]; exact List.cons_ne_nil y ys)]
    exact hpoolr.symm.trans hdrool.symm

/-! ## §7. The pool/cut recovery (the keystone's outside-the-board
half: the stock and the waste from the pool and the cut) -/

/-- Equal pools with equal-length heads split equally (fresh). -/
private theorem chk_append_eq_split {l₁ r₁ l₂ r₂ : List Card}
    (h : l₁ ++ r₁ = l₂ ++ r₂) (hlen : l₁.length = l₂.length) :
    l₁ = l₂ ∧ r₁ = r₂ := by
  have key : ∀ (l₁ l₂ : List Card) (r₁ r₂ : List Card),
      l₁ ++ r₁ = l₂ ++ r₂ → l₁.length = l₂.length → l₁ = l₂ ∧ r₁ = r₂ := by
    intro l₁
    induction l₁ with
    | nil =>
        intro l₂ r₁ r₂ h hlen
        cases l₂ with
        | nil => exact ⟨rfl, by simpa only [List.nil_append] using h⟩
        | cons y ys =>
            exfalso
            rw [List.length_cons, List.length_nil] at hlen
            omega
    | cons x xs ih =>
        intro l₂ r₁ r₂ h hlen
        cases l₂ with
        | nil =>
            exfalso
            rw [List.length_cons, List.length_nil] at hlen
            omega
        | cons y ys =>
            rw [List.cons_append, List.cons_append] at h
            injection h with hxy hrest
            have hlenn : xs.length = ys.length := by
              rw [List.length_cons, List.length_cons] at hlen
              omega
            obtain ⟨h1, h2⟩ := ih ys r₁ r₂ hrest hlenn
            refine ⟨?_, h2⟩
            rw [hxy]
            exact congrArg (y :: ·) h1
  exact key l₁ l₂ r₁ r₂ h hlen

/-- The pool and the cut together fix the stock and the waste (the
recovery row the round trip's outside-the-board half rides). -/
theorem chart_pool_cut_split {st w : State}
    (hpool : drawPool st = drawPool w) (hcut : cutOf st = cutOf w) :
    st.stock = w.stock ∧ st.waste = w.waste := by
  have hpool' : st.stock.reverse ++ st.waste = w.stock.reverse ++ w.waste := hpool
  have hcut' : st.stock.length = w.stock.length := hcut
  have hrlen : st.stock.reverse.length = w.stock.reverse.length := by
    rw [List.length_reverse, List.length_reverse, hcut']
  obtain ⟨h1, h2⟩ := chk_append_eq_split hpool' hrlen
  refine ⟨?_, h2⟩
  rw [← List.reverse_reverse st.stock, h1, List.reverse_reverse]

/-! ## §8. The keystone engine: below-profile transfer -/

/-- The member decomposition, fresh variables packed: a card's host
list splits at the card's first occurrence (the frame the finish and
the transfer ride; built on the split identity §1). -/
private theorem chk_member_decomp (c : Card) {l : List Card} (hmem : c ∈ l) :
    ∃ pre suf, pre = below c l ∧ l = pre ++ c :: suf := by
  have e := chk_below_fromCard c l
  obtain ⟨suf, hsuf⟩ := fromCard_eq_head_of_mem hmem
  rw [hsuf] at e
  exact ⟨below c l, suf, rfl, e.symm⟩

/-- THE PROFILE TRANSFER — the keystone's engine: at two WF states
agreeing on every seat, a card's below-profile (its position datum:
the strict prefix before its first occurrence in its pile's face-up
run) transfers to the mate, position by position.  The induction is
on the position itself (the below length); every step is an
occurrence kill plus the split calculus.  GATE: pure occurrence
uniqueness, both boards — no run legality, no foundation shape, no
draw-quantum content is consumed. -/
private theorem chk_profile_transfer {S T : State}
    (hScnt : ∀ c, S.cardCount c = 1) (hTcnt : ∀ c, T.cardCount c = 1)
    (hseat : ∀ c, seatOf S c = seatOf T c) (n : Nat) (a : Anchor) (c : Card)
    (hc : c ∈ (S.piles a).faceUp)
    (hlen : (below c (S.piles a).faceUp).length = n) :
    c ∈ (T.piles a).faceUp ∧
      below c (T.piles a).faceUp = below c (S.piles a).faceUp := by
  induction n generalizing a c with
  | zero =>
      have hbl : below c (S.piles a).faceUp = [] := by
        cases hb : below c (S.piles a).faceUp with
        | nil => rfl
        | cons x xs =>
            rw [hb, List.length_cons] at hlen
            omega
      have hpinS : S.pileHolding c = some a := chk_holding_pin hScnt hc
      have hseS : seatOf S c = some (Sum.inl a) := by
        rw [chk_seatOf_pair hpinS, hbl]
        rfl
      have hseT : seatOf T c = some (Sum.inl a) := by
        rw [← hseat c]; exact hseS
      obtain ⟨hholdT, hblT⟩ := chk_seatOf_of_inl hseT
      refine ⟨pileHolding_mem hholdT, ?_⟩
      rw [hblT]
      exact hbl.symm
  | succ n ih =>
      have hpinS : S.pileHolding c = some a := chk_holding_pin hScnt hc
      have hbne : below c (S.piles a).faceUp ≠ [] := by
        intro hnil
        rw [hnil, List.length_nil] at hlen
        omega
      obtain ⟨p, hpLast⟩ := lastOf_exists hbne
      obtain ⟨pre, hpre⟩ := lastOf_eq_snoc hpLast
      -- the S-side shape: pre ++ p :: c :: sufS
      have eS := chk_below_fromCard c ((S.piles a).faceUp)
      obtain ⟨sufS, hsufS⟩ := fromCard_eq_head_of_mem (pileHolding_mem hpinS)
      rw [hpre, hsufS] at eS
      have hlsS : (S.piles a).faceUp = pre ++ p :: c :: sufS := by
        rw [← eS, List.append_assoc, List.cons_append, List.nil_append]
      -- the parent's S-position is exactly one below the child's
      have hpmemS : p ∈ (S.piles a).faceUp := mem_below _ (lastOf_mem hpLast)
      have hppre : p ∉ pre := by
        intro hmem
        obtain ⟨A, B, hAB⟩ := chk_mem_split _ hmem
        have hspl : (S.piles a).faceUp = (A ++ [p]) ++ (B ++ p :: c :: sufS) := by
          rw [hlsS, hAB]
          have eL : (A ++ p :: B) ++ (p :: c :: sufS)
              = A ++ p :: (B ++ p :: c :: sufS) := by
            rw [List.append_assoc, List.cons_append]
          have eR : (A ++ [p]) ++ (B ++ p :: c :: sufS)
              = A ++ p :: (B ++ p :: c :: sufS) := by
            rw [List.append_assoc, List.cons_append, List.nil_append]
          rw [eL]
          exact eR.symm
        exact chk_two_mem_faceUp_absurd hScnt hspl
          (List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl)))
          (List.mem_append.mpr (Or.inr (List.mem_cons_self)))
      have hbelowpS : below p (S.piles a).faceUp = pre := by
        rw [hlsS, chk_below_extend p pre (p :: c :: sufS) hppre, below_cons,
          ite_eq_left rfl, List.append_nil]
      have hprelen : pre.length = n := by
        have hcl := hlen
        rw [hpre, List.length_append, List.length_singleton] at hcl
        omega
      have hbelowplen : (below p (S.piles a).faceUp).length = n := by
        rw [hbelowpS, hprelen]
      obtain ⟨hpmemT, hbelowpT⟩ := ih a p hpmemS hbelowplen
      -- the seat bridge: both states read c at .inr p
      have hseS : seatOf S c = some (Sum.inr p) := by
        rw [chk_seatOf_pair hpinS, chk_getLast?_lastOf, hpLast]
      have hseT : seatOf T c = some (Sum.inr p) := by
        rw [← hseat c]; exact hseS
      obtain ⟨a₀, hholdT, hbTne, hbTlast⟩ := chk_seatOf_of_inr hseT
      -- pin the T anchor by the parent
      have hpmemTa₀ : p ∈ (T.piles a₀).faceUp := mem_below _ (lastOf_mem hbTlast)
      have hpinpTa : T.pileHolding p = some a₀ := chk_holding_pin hTcnt hpmemTa₀
      have hpinpTb : T.pileHolding p = some a := chk_holding_pin hTcnt hpmemT
      have ha₀ : a₀ = a := by
        rw [hpinpTa] at hpinpTb
        exact Option.some.inj hpinpTb
      -- the T-side shape: pre ++ p :: sufT
      obtain ⟨preT, sufT, hbT2, eT2⟩ := chk_member_decomp p hpmemT
      have hpreT : preT = pre := (hbT2.trans hbelowpT).trans hbelowpS
      have hlsT : (T.piles a).faceUp = pre ++ p :: sufT := by
        rw [eT2, hpreT]
      have hcTa : c ∈ (T.piles a).faceUp := by
        rw [ha₀] at hholdT
        exact pileHolding_mem hholdT
      -- c is not in pre at the T-read, and c is not its own parent
      have hcpre : c ∉ pre := by
        intro hmem
        have hbT2' : lastOf (below c (T.piles a).faceUp) = some p := by
          rw [ha₀] at hbTlast; exact hbTlast
        rw [hlsT, chk_below_absorb c pre (p :: sufT) hmem] at hbT2'
        exact hppre (mem_below _ (lastOf_mem hbT2'))
      have hcp : c ≠ p := by
        intro hcp'
        rw [← hcp'] at hpLast
        exact chk_below_not_mem c _ (lastOf_mem hpLast)
      -- the T-side below of c is pre ++ [p]
      have hbeT : below c (T.piles a).faceUp = pre ++ [p] := by
        rw [hlsT, chk_below_extend c pre (p :: sufT) hcpre, below_cons,
          ite_eq_right (fun h => hcp h.symm)]
        have hd : below c sufT = [] := by
          cases hd0 : below c sufT with
          | nil => rfl
          | cons z zs =>
              exfalso
              have hlast0 : lastOf (below c (T.piles a).faceUp) = some p := by
                rw [ha₀] at hbTlast; exact hbTlast
              rw [hlsT, chk_below_extend c pre (p :: sufT) hcpre, below_cons,
                ite_eq_right (fun h => hcp h.symm), hd0] at hlast0
              rw [chk_lastOf_append_ne _ (List.cons_ne_nil p (z :: zs)),
                show lastOf (p :: z :: zs) = lastOf (z :: zs) from rfl] at hlast0
              have hpinSuf : p ∈ sufT := by
                have hz : p ∈ below c sufT := by
                  rw [hd0]; exact lastOf_mem hlast0
                exact mem_below _ hz
              have hsplT : (T.piles a).faceUp = (pre ++ [p]) ++ sufT := by
                rw [hlsT, List.append_assoc, List.cons_append, List.nil_append]
              exact chk_two_mem_faceUp_absurd hTcnt hsplT
                (List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl))) hpinSuf
        rw [hd]
      exact ⟨hcTa, hbeT.trans hpre.symm⟩

/-! ## §9. The finish: the face-up runs agree -/

/-- THE FACE-UP EQUALITY: at two occurrence-unique chart-twins, every
pile's face-up run is the same list.  The top card anchors the
comparison — its below-profile pins the whole run on both sides;
the two top kills and the length comparison are the only occurrence
counting. -/
private theorem chk_faceUp_eq {S T : State}
    (hScnt : ∀ c, S.cardCount c = 1) (hTcnt : ∀ c, T.cardCount c = 1)
    (hseat : ∀ c, seatOf S c = seatOf T c) (a : Anchor) :
    (S.piles a).faceUp = (T.piles a).faceUp := by
  have hP := chk_profile_transfer hScnt hTcnt hseat
  have hP' := chk_profile_transfer hTcnt hScnt (fun c => (hseat c).symm)
  have hmemS : ∀ c, c ∈ (S.piles a).faceUp → c ∈ (T.piles a).faceUp :=
    fun c hc => (hP _ a c hc rfl).1
  have hmemT : ∀ c, c ∈ (T.piles a).faceUp → c ∈ (S.piles a).faceUp :=
    fun c hc => (hP' _ a c hc rfl).1
  cases hls : (S.piles a).faceUp with
  | nil =>
      cases hlt : (T.piles a).faceUp with
      | nil => rfl
      | cons y ys =>
          exfalso
          have hy : y ∈ (S.piles a).faceUp :=
            hmemT y (by rw [hlt]; exact List.mem_cons_self)
          rw [hls] at hy
          exact absurd hy (by simp)
  | cons x xs =>
      cases hlt : (T.piles a).faceUp with
      | nil =>
          exfalso
          have hx : x ∈ (T.piles a).faceUp :=
            hmemS x (by rw [hls]; exact List.mem_cons_self)
          rw [hlt] at hx
          exact absurd hx (by simp)
      | cons y ys =>
          have hneS : (S.piles a).faceUp ≠ [] := by
            rw [hls]; exact List.cons_ne_nil x xs
          have hneT : (T.piles a).faceUp ≠ [] := by
            rw [hlt]; exact List.cons_ne_nil y ys
          -- the S-top drives the finish
          obtain ⟨ct, hctop⟩ := lastOf_exists hneS
          have hctS : ct ∈ (S.piles a).faceUp := lastOf_mem hctop
          obtain ⟨hctT, hbct⟩ := hP _ a ct hctS rfl
          obtain ⟨preS, sufS, hbS, eS⟩ := chk_member_decomp ct hctS
          have hsufSn : sufS = [] := by
            cases hs0 : sufS with
            | nil => rfl
            | cons z zs =>
                exfalso
                have hlast2 : lastOf (preS ++ ct :: z :: zs) = some ct := by
                  have h0 := congrArg lastOf eS
                  rw [hs0] at h0
                  exact h0.symm.trans hctop
                rw [chk_lastOf_append_ne _ (List.cons_ne_nil ct (z :: zs)),
                  show lastOf (ct :: z :: zs) = lastOf (z :: zs) from rfl] at hlast2
                have hspl : (S.piles a).faceUp = (preS ++ [ct]) ++ z :: zs := by
                  rw [eS, hs0, List.append_assoc, List.cons_append, List.nil_append]
                exact chk_two_mem_faceUp_absurd hScnt hspl
                  (List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl)))
                  (lastOf_mem hlast2)
          have hlenS : ((S.piles a).faceUp).length = preS.length + 1 := by
            have h0 := congrArg (List.length : List Card → Nat) eS
            rw [hsufSn, List.length_append, List.length_cons, List.length_nil] at h0
            exact h0
          obtain ⟨preT, sufT, hbT, eT⟩ := chk_member_decomp ct hctT
          have hbT' : preT = preS := (hbT.trans hbct).trans hbS.symm
          have hlenT : ((T.piles a).faceUp).length = preS.length + (sufT.length + 1) := by
            have h0 := congrArg (List.length : List Card → Nat) eT
            rw [List.length_append, List.length_cons] at h0
            rw [hbT'] at h0
            exact h0
          -- the T-top gives the upper bound
          obtain ⟨cq, hctopT⟩ := lastOf_exists hneT
          have hctT2 : cq ∈ (T.piles a).faceUp := lastOf_mem hctopT
          obtain ⟨hctS2, hbcq⟩ := hP' _ a cq hctT2 rfl
          obtain ⟨preT2, sufT2, hbT2, eT2⟩ := chk_member_decomp cq hctT2
          have hsufT2n : sufT2 = [] := by
            cases hs2 : sufT2 with
            | nil => rfl
            | cons w ws =>
                exfalso
                have hlast3 : lastOf (preT2 ++ cq :: w :: ws) = some cq := by
                  have h0 := congrArg lastOf eT2
                  rw [hs2] at h0
                  exact h0.symm.trans hctopT
                rw [chk_lastOf_append_ne _ (List.cons_ne_nil cq (w :: ws)),
                  show lastOf (cq :: w :: ws) = lastOf (w :: ws) from rfl] at hlast3
                have hspl2 : (T.piles a).faceUp = (preT2 ++ [cq]) ++ w :: ws := by
                  rw [eT2, hs2, List.append_assoc, List.cons_append, List.nil_append]
                exact chk_two_mem_faceUp_absurd hTcnt hspl2
                  (List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl)))
                  (lastOf_mem hlast3)
          have hlenT2 : ((T.piles a).faceUp).length = preT2.length + 1 := by
            have h0 := congrArg (List.length : List Card → Nat) eT2
            rw [hsufT2n, List.length_append, List.length_cons, List.length_nil] at h0
            exact h0
          obtain ⟨preS2, sufS2, hbS2, eS2⟩ := chk_member_decomp cq hctS2
          have hpre2 : preS2 = preT2 := (hbS2.trans hbcq).trans hbT2.symm
          have hlenS2 : ((S.piles a).faceUp).length = preT2.length + (sufS2.length + 1) := by
            have h0 := congrArg (List.length : List Card → Nat) eS2
            rw [List.length_append, List.length_cons] at h0
            rw [hpre2] at h0
            exact h0
          have hlenEq : ((T.piles a).faceUp).length = ((S.piles a).faceUp).length := by
            omega
          have hsufTn : sufT = [] :=
            List.length_eq_zero_iff.mp (show sufT.length = 0 by omega)
          -- assemble: both lists are preS ++ [ct]
          have hrwS : (S.piles a).faceUp = preS ++ [ct] := by rw [eS, hsufSn]
          have hrwT : (T.piles a).faceUp = preS ++ [ct] := by
            rw [eT, hsufTn, hbT']
          rw [← hls, hrwS, ← hlt]
          exact hrwT.symm

/-! ## §10. THE KEYSTONE AND ITS GRADES -/

/-- **THE OCCURRENCE-GRADE CORE (2026-10-18)** — the load-bearing row
stated bare: occurrence uniqueness, per side, is EXACTLY what the
chart's faithfulness costs.  No run legality, no foundation prefix,
no draw-quantum content is consumed anywhere below this — the whole
WF apparatus of the re-gated ledger claim reduces to the two count
hypotheses here. -/
theorem chart_round_trip_core (st w : State)
    (hcst : ∀ c, st.cardCount c = 1) (hcw : ∀ c, w.cardCount c = 1)
    (h : chartAgree st w) : st = w := by
  obtain ⟨hseat, ⟨hhid, hds⟩, hff, hpool, hcut⟩ := h
  obtain ⟨hstock, hwaste⟩ := chart_pool_cut_split hpool hcut
  apply State.ext
  · exact funext fun s => hff s
  · refine funext fun a => Pile.ext ?_ ?_
    · exact hhid a
    · exact chk_faceUp_eq hcst hcw hseat a
  · exact hstock
  · exact hwaste
  · exact hds

/-- **CLAIM `chart_round_trip` DISCHARGED, RE-GATED (2026-10-18)** —
the chart is faithful at WF: states ARE their readouts whenever both
sides are WF.  The re-gate replaces the ledger's original ungated
stub, refuted below at wild states; the gates are load-bearing.  The
proof is the occurrence core above, WF's count clause extracted. -/
theorem chart_round_trip (st w : State) (hwfst : st.WF) (hwfw : w.WF)
    (h : chartAgree st w) : st = w :=
  chart_round_trip_core st w (fun c => hwfst.2.2.1 c (Card.mem_universe c))
    (fun c => hwfw.2.2.1 c (Card.mem_universe c)) h

/-- **THE CONSERVATION GRADE (2026-10-18)** — one-side WF plus count
AGREEMENT: a chart-mate whose zone census matches the WF side's is
pinned, no mate-side gate.  This is the row the floater books'
hoists can ride instead of a mate-side WF premise: a SeatEdit-grade
spec gains `∀ c, w.cardCount c = st.cardCount c` (count NEUTRALITY —
an edit creates no cards, the natural conservation clause beside
the fixed readouts) and the chart-mate identification at
`floater_seat_to_equiv'`-style sites follows from the flat data. -/
theorem chart_round_trip_counts (st w : State) (hwfst : st.WF)
    (hcnt : ∀ c, st.cardCount c = w.cardCount c)
    (h : chartAgree st w) : st = w := by
  refine chart_round_trip_core st w
    (fun c => hwfst.2.2.1 c (Card.mem_universe c)) ?_ h
  intro c
  rw [← hcnt c]
  exact hwfst.2.2.1 c (Card.mem_universe c)

/-! ## §11. THE KERNEL REFUTATION OF THE UNGATED FORM -/

/-- The first masked card (a spade king). -/
private def crtC : Card := ⟨.spade, .king⟩
/-- The second masked card (a heart ace). -/
private def crtD : Card := ⟨.heart, .ace⟩

/-- The wild board A: c bottoms p0, d bottoms p1, both also ride
p5's face-up deck — c and d are CHART-MASKED there. -/
private def crtPilesA : Anchor → Pile
  | .p0 => ⟨[], [crtC]⟩
  | .p1 => ⟨[], [crtD]⟩
  | .p5 => ⟨[], [crtC, crtD]⟩
  | _ => ⟨[], ([] : List Card)⟩

/-- The wild board B: the same first-occurrence seats everywhere,
p5's masked tail swapped in order. -/
private def crtPilesB : Anchor → Pile
  | .p0 => ⟨[], [crtC]⟩
  | .p1 => ⟨[], [crtD]⟩
  | .p5 => ⟨[], [crtD, crtC]⟩
  | _ => ⟨[], ([] : List Card)⟩

private def crtS : State :=
  { found := fun _ => [], piles := crtPilesA, stock := [], waste := [],
    drawStep := 1 }
private def crtW : State :=
  { found := fun _ => [], piles := crtPilesB, stock := [], waste := [],
    drawStep := 1 }

/-- The firstWhere decline builder (the pack of `Orig/State.lean:40`,
mirror of `Orig2/CargoKit.lean:1544`). -/
private theorem chk_firstWhere_none {α : Type} (p : α → Bool) :
    ∀ (l : List α), (∀ j ∈ l, p j = false) → firstWhere p l = none := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons x t ih =>
      intro hf
      have hfx : p x = false := hf x List.mem_cons_self
      show (match p x with
          | true => some x
          | false => firstWhere p t) = none
      rw [hfx]
      exact ih (fun j hj => hf j (List.mem_cons_of_mem _ hj))

private theorem crt_declineS (c : Card) (hc : c ≠ crtC) (hd : c ≠ crtD) :
    ∀ j, c ∉ (crtS.piles j).faceUp := by
  intro j
  cases j with
  | p0 => intro h; exact hc (List.mem_singleton.mp h)
  | p1 => intro h; exact hd (List.mem_singleton.mp h)
  | p2 => intro h; exact absurd h List.not_mem_nil
  | p3 => intro h; exact absurd h List.not_mem_nil
  | p4 => intro h; exact absurd h List.not_mem_nil
  | p5 =>
      intro h
      rcases List.mem_cons.mp h with h1 | h2
      · exact hc h1
      · rcases List.mem_cons.mp h2 with h2' | h3
        · exact hd h2'
        · exact absurd h3 List.not_mem_nil
  | p6 => intro h; exact absurd h List.not_mem_nil

private theorem crt_declineW (c : Card) (hc : c ≠ crtC) (hd : c ≠ crtD) :
    ∀ j, c ∉ (crtW.piles j).faceUp := by
  intro j
  cases j with
  | p0 => intro h; exact hc (List.mem_singleton.mp h)
  | p1 => intro h; exact hd (List.mem_singleton.mp h)
  | p2 => intro h; exact absurd h List.not_mem_nil
  | p3 => intro h; exact absurd h List.not_mem_nil
  | p4 => intro h; exact absurd h List.not_mem_nil
  | p5 =>
      intro h
      rcases List.mem_cons.mp h with h1 | h2
      · exact hd h1
      · rcases List.mem_cons.mp h2 with h2' | h3
        · exact hc h2'
        · exact absurd h3 List.not_mem_nil
  | p6 => intro h; exact absurd h List.not_mem_nil

/-- The wild pair is chart-twinned: every seat readout agrees (the
masked copies are invisible to the search). -/
private theorem crt_seats_eq : ∀ c, seatOf crtS c = seatOf crtW c := by
  intro c
  by_cases hc : c = crtC
  · subst hc; rfl
  by_cases hd : c = crtD
  · subst hd; rfl
  · have hnoneS : crtS.pileHolding c = none := by
      show firstWhere (fun a => decide (c ∈ (crtS.piles a).faceUp)) Anchor.all
        = none
      exact chk_firstWhere_none _ _
        (fun j _ => decide_false_of_not (crt_declineS c hc hd j))
    have hnoneW : crtW.pileHolding c = none := by
      show firstWhere (fun a => decide (c ∈ (crtW.piles a).faceUp)) Anchor.all
        = none
      exact chk_firstWhere_none _ _
        (fun j _ => decide_false_of_not (crt_declineW c hc hd j))
    rw [chk_seatOf_none hnoneS, chk_seatOf_none hnoneW]

/-- The full chart agreement of the wild pair (the kernel premise of
the refutation). -/
private theorem crt_chartAgree : chartAgree crtS crtW := by
  refine ⟨crt_seats_eq, ⟨fun a => ?_, rfl⟩, fun _ => rfl, rfl, rfl⟩
  cases a <;> rfl

/-- The wild pair differs (the kernel fact). -/
private theorem crt_ne : crtS ≠ crtW := by
  intro h
  have h5 : (crtS.piles .p5).faceUp = (crtW.piles .p5).faceUp :=
    congrArg (fun x => (x.piles .p5).faceUp) h
  exact absurd h5 (by decide)

/-- **THE KERNEL WITNESS** — the ledger's ungated round trip is
FALSE: this wild pair agrees on every chart readout (seats, hidden
decks, foundations, pool, cut) yet the states differ.  The
first-occurrence mask is the mechanism: WF's occurrence uniqueness
(both sides gated in `chart_round_trip` above) is exactly what
kills it. -/
theorem chart_round_trip_ungated_false :
    ¬ (∀ st w : State, chartAgree st w → st = w) := by
  intro h
  exact absurd (h crtS crtW crt_chartAgree) crt_ne

/-! ## The audit battery

Per the per-file discipline: the public heads re-print
`#print axioms` at the tail (zero sorry; zero `Classical.choice`). -/

#print axioms chart_draw
#print axioms chart_pool_cut_split
#print axioms chart_round_trip_core
#print axioms chart_round_trip
#print axioms chart_round_trip_counts
#print axioms chart_round_trip_ungated_false
