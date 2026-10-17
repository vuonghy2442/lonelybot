import Orig2.Vocab
import Orig2.Classification
import Orig2.FloaterLadder

/-!
# Orig2.FloatFiber — THE FLOATER QUARTET (the agent dry-run
promoted to a chartered card at owner approval, 2026-10-17)

PROMOTION PROVENANCE: dry-ran as `Temp/float_agent_check.lean`
(the shared-board four-row program), re-verified against the live
tree at promotion time (all four heads `[propext, Quot.sound]`,
zero sorry, zero `Classical.choice`), installed at owner approval
("sure can you help me do that incorporate the new theorem for me"
— same hour).

THE FOUR ROWS (the address-and-structural tier of the floater program —
the seat-edit, lift, and classification companions of the
`Orig2.FloaterLadder` card's three public rows):

* `floater_seat_change_spec` (their "Row 3") — the one-point chart
  edit realized by a reversible slide, and the class-STEP fiber:
  twin-family reseating or a bare king vacate — the SeatEdit-grade
  restatement of `FloaterLadder.floater_seat_change` (renamed at
  installation; no name collision with the ladder's row);
* `floater_cargo_lift` — a live, fiber-valid cell with a
  placement license fires as an actual reversible cargo leg
  realizing the SeatEdit spec;
* `floater_seat_to_equiv'` — with the round-trip chart readout as
  a PRICED HYPOTHESIS (never sorry'd: the chart pivot row rides
  where it belongs — priced in the claims book — and this row
  consumes it as a hypothesis, per the house never-force rule):
  a valid one-point SeatEdit at a live, fiber-valid cell derives
  the bare-cargo class;
* `floater_classification` — the structural classification: the
  behavioral Floater iff `FloaterSpec` (the target-existence
  shape: the company cell with its twin-fiber target, or the
  bare-king vacate cell).

KIT DISCIPLINE: the `tfc_*` rows are the ladder card's private
kit re-proven privately in this copy (the per-file dedup
discipline; a module's privates are consumable only in-module,
hence the fresh copy with cites kept) — the cut-record and the
row briefs live in the §H header below, kept from the dry-run
verbatim.  The four rows ride the oracle bridge
(`tabToTabR_iff_reversibleAtW`), constructive placement rows, and
the conservation/hiding rows — no hand-assembled plays, no
`reversible_mirrorW`, no choice.

IMPORT SURFACE: `Orig2.Vocab` + `Orig2.Classification` +
`Orig2.FloaterLadder` (the ladder import is presentational —
this file's kit is its own private copy; nothing else enters
above the certified seam).

- the `cnt`/`cntFlat` occurrence bookkeeping and the `tabToTab` WF
  preservation (PORT from `Orig/Reach.lean:131-329`, `:1071-1164`,
  `:1569-2103` - the frozen tier's conservation ticket; the certified
  new-tier cards do NOT carry step-WF, so this dry-run ports it);
- the list/run kit rows `below_fromCard`/`below_not_mem_self`/
  `below_fromCard_excl` (PORT of `Orig2/Classification.lean` privates,
  themselves ports of `Orig/Classify.lean:282, :294, :310`);
- the run legality prefix row (PORT of `Orig/Classify.lean:392`)
  and the `getLast?`/`lastOf` bridge (fresh, over `Orig/State.lean:116`);
- the seat point-edit lemma `tfc_seat_point_edit` - the one-point-edit
  chart row RE-PROVED inline (a private port over the seam's
  `State.step` unfold for `tabToTab`,
  `Orig/Play.lean:129-140` + `Orig/State.lean:392-473`), NOT consumed
  from the priced stub `Orig2/Claims.lean` - and see
  `chart_tabToTab_ungated_false` at the tail: the stub's ungated
  statement is refuted by an explicit witness.

GATE DISCIPLINE: every private row states its own gate; the three
public rows are the ONLY public artifact.  Zero sorry; the battery at
the tail expects `[propext]`/`[propext, Quot.sound]` on all three heads.
-/

/-! ## §A. The occurrence-count kit  (PORT: `Orig/Reach.lean:131-329`) -/

/-- PORT verbatim from `Orig/Reach.lean:131`. -/
private def tfc_cnt (c : Card) : List Card → Nat
  | [] => 0
  | x :: t => (if x = c then 1 else 0) + tfc_cnt c t

/-- PORT verbatim from `Orig/Reach.lean:135`. -/
private theorem tfc_cnt_nil (c : Card) : tfc_cnt c [] = 0 := rfl

/-- PORT verbatim from `Orig/Reach.lean:138`. -/
private theorem tfc_cnt_def (c x : Card) (t : List Card) :
    tfc_cnt c (x :: t) = (if x = c then 1 else 0) + tfc_cnt c t := rfl

/-- PORT verbatim from `Orig/Reach.lean:141`. -/
private theorem tfc_cnt_singleton (c x : Card) : tfc_cnt c [x] = if x = c then 1 else 0 := by
  show ((if x = c then 1 else 0) + tfc_cnt c []) = if x = c then 1 else 0
  rw [tfc_cnt_nil]
  omega

/-- PORT verbatim from `Orig/Reach.lean:146`. -/
private theorem tfc_cnt_app (c : Card) : ∀ (l₁ l₂ : List Card),
    tfc_cnt c (l₁ ++ l₂) = tfc_cnt c l₁ + tfc_cnt c l₂ := by
  intro l₁ l₂
  induction l₁ with
  | nil => rw [List.nil_append, tfc_cnt_nil]; omega
  | cons x t ih =>
      show (if x = c then 1 else 0) + tfc_cnt c (t ++ l₂) = _
      rw [ih, tfc_cnt_def]
      omega

/-- PORT verbatim from `Orig/Reach.lean:156`. -/
private theorem tfc_cnt_snoc (c x : Card) (l : List Card) :
    tfc_cnt c (l ++ [x]) = tfc_cnt c l + tfc_cnt c [x] := tfc_cnt_app c l [x]

/-- PORT verbatim from `Orig/Reach.lean:167`. -/
private theorem tfc_mem_le_cnt {c : Card} : ∀ (l : List Card), c ∈ l → 1 ≤ tfc_cnt c l := by
  intro l
  induction l with
  | nil => intro h; exact absurd h List.not_mem_nil
  | cons x t ih =>
      intro h
      show 1 ≤ (if x = c then 1 else 0) + tfc_cnt c t
      rcases List.mem_cons.mp h with h' | h'
      · rw [ite_eq_left h'.symm]
        omega
      · have h1 : 1 ≤ tfc_cnt c t := ih h'
        by_cases hx : x = c
        · rw [ite_eq_left hx]; omega
        · rw [ite_eq_right hx]; omega

/-- PORT from `Orig/Reach.lean:190` (`cnt_filter`). -/
private theorem tfc_cnt_filter (c : Card) : ∀ (l : List Card),
    tfc_cnt c l = (l.filter fun x => decide (x = c)).length := by
  intro l
  induction l with
  | nil => rfl
  | cons x t ih =>
      show ((if x = c then 1 else 0) + tfc_cnt c t) = _
      rw [List.filter_cons]
      by_cases hxc : x = c
      · rw [decide_eq_true hxc, ite_eq_left rfl, List.length_cons, ite_eq_left hxc, ih]
        omega
      · have hdec : (decide (x = c)) = false := by rw [decide_false_of_not hxc]
        rw [hdec, ite_eq_right (fun h => Bool.noConfusion h),
          ite_eq_right hxc, ih]
        omega

/-- PORT verbatim from `Orig/Reach.lean:206` (`cardCount_eq_cnt`). -/
private theorem tfc_cardCount_eq_cnt (st : State) (c : Card) :
    st.cardCount c = tfc_cnt c (st.zones.flatMap id) :=
  (tfc_cnt_filter c (st.zones.flatMap id)).symm

/-- PORT verbatim from `Orig/Reach.lean:211`. -/
private def tfc_cntFlat (c : Card) : List (List Card) → Nat
  | [] => 0
  | z :: zs => tfc_cnt c z + tfc_cntFlat c zs

/-- PORT verbatim from `Orig/Reach.lean:215`. -/
private theorem tfc_cntFlat_cons (c : Card) (z : List Card) (zs : List (List Card)) :
    tfc_cntFlat c (z :: zs) = tfc_cnt c z + tfc_cntFlat c zs := rfl

/-- PORT verbatim from `Orig/Reach.lean:218`. -/
private theorem tfc_cntFlat_flatMap (c : Card) : ∀ (zs : List (List Card)),
    tfc_cntFlat c zs = tfc_cnt c (zs.flatMap id) := by
  intro zs
  induction zs with
  | nil => rfl
  | cons z t ih =>
      rw [tfc_cntFlat_cons, List.flatMap_cons, tfc_cnt_app c, ih]
      rfl

/-- PORT verbatim from `Orig/Reach.lean:227`. -/
private theorem tfc_cntFlat_map_congr (c : Card) : ∀ {α : Type} (F G : α → List Card)
    (as : List α), (∀ j ∈ as, tfc_cnt c (F j) = tfc_cnt c (G j)) →
    tfc_cntFlat c (as.map F) = tfc_cntFlat c (as.map G) := by
  intro α F G as
  induction as with
  | nil => intro _; rfl
  | cons x t ih =>
      intro h
      simp only [List.map_cons, tfc_cntFlat_cons]
      rw [h x List.mem_cons_self, ih (fun j hj => h j (List.mem_cons_of_mem _ hj))]

/-- PORT verbatim from `Orig/Reach.lean:248`. -/
private theorem tfc_cntFlat_map_delta (c : Card) : ∀ {α : Type} (F G : α → List Card)
    (as : List α) (δ : α → Nat), (∀ j ∈ as, tfc_cnt c (F j) + δ j = tfc_cnt c (G j)) →
    tfc_cntFlat c (as.map F) + (as.map δ).sum = tfc_cntFlat c (as.map G) := by
  intro α F G as
  induction as with
  | nil => intro δ _; rfl
  | cons x t ih =>
      intro δ h
      simp only [List.map_cons, tfc_cntFlat_cons, List.sum_cons]
      have hx : tfc_cnt c (F x) + δ x = tfc_cnt c (G x) := h x List.mem_cons_self
      have hr := ih δ (fun j hj => h j (List.mem_cons_of_mem _ hj))
      omega

/-- PORT verbatim from `Orig/Reach.lean:261`. -/
private theorem tfc_sum_map_zero {α : Type} : ∀ (L : List α) (δ : α → Nat),
    (∀ j ∈ L, δ j = 0) → (L.map δ).sum = 0 := by
  intro L δ
  induction L with
  | nil => intro _; rfl
  | cons x t ih =>
      intro h
      rw [List.map_cons, List.sum_cons, h x List.mem_cons_self]
      have := ih (fun j hj => h j (List.mem_cons_of_mem _ hj))
      omega

/-- PORT verbatim from `Orig/Reach.lean:274`. -/
private theorem tfc_sum_map_single {α : Type} [DecidableEq α] :
    ∀ (L : List α) (δ : α → Nat) (a : α), L.Nodup → a ∈ L →
    (∀ j ∈ L, j ≠ a → δ j = 0) → (L.map δ).sum = δ a := by
  intro L
  induction L with
  | nil => intro δ a _ hmem _; exact absurd hmem List.not_mem_nil
  | cons x t ih =>
      intro δ a hnd hmem hzero
      obtain ⟨hx, hnd'⟩ := List.nodup_cons.mp hnd
      rcases Decidable.em (x = a) with hxa | hxa
      · have hxa' : a = x := hxa.symm
        subst hxa'
        have hz : (List.map δ t).sum = 0 :=
          tfc_sum_map_zero t δ
            (fun j hj => hzero j (List.mem_cons_of_mem _ hj)
              (fun hje => hx (hje ▸ hj)))
        rw [List.map_cons, List.sum_cons]
        omega
      · rw [List.map_cons, List.sum_cons, hzero x List.mem_cons_self hxa]
        rcases List.mem_cons.mp hmem with hmem' | hmem'
        · exact absurd hmem'.symm hxa
        · have := ih δ a hnd' hmem'
            (fun j hj hne2 => hzero j (List.mem_cons_of_mem _ hj) hne2)
          omega

/-- PORT verbatim from `Orig/Reach.lean:299`. -/
private theorem tfc_flatMap_id_append : ∀ (A B : List (List Card)),
    (A ++ B).flatMap id = (A.flatMap id) ++ (B.flatMap id) := by
  intro A B
  induction A with
  | nil => rfl
  | cons z t ih =>
      show (z ++ ((t ++ B).flatMap id)) = (z ++ (t.flatMap id)) ++ (B.flatMap id)
      rw [show (t ++ B).flatMap id = (t.flatMap id) ++ (B.flatMap id) from ih]
      exact (List.append_assoc z (t.flatMap id) (B.flatMap id)).symm

/-- PORT verbatim from `Orig/Reach.lean:312`. -/
private theorem tfc_cardCount_zones (st : State) (c : Card) :
    st.cardCount c =
      tfc_cntFlat c (Suit.all.map st.found)
      + tfc_cntFlat c (Anchor.all.map fun a => (st.piles a).hidden ++ (st.piles a).faceUp)
      + (tfc_cnt c st.stock + tfc_cnt c st.waste) := by
  rw [tfc_cardCount_eq_cnt]
  have h2 : ([st.stock, st.waste] : List (List Card)).flatMap id
      = st.stock ++ st.waste :=
    congrArg (st.stock ++ ·) (List.append_nil st.waste)
  show tfc_cnt c ((Suit.all.map st.found ++ (Anchor.all.map
      (fun a => (st.piles a).hidden ++ (st.piles a).faceUp) ++ [st.stock, st.waste])).flatMap id) = _
  rw [tfc_flatMap_id_append, tfc_flatMap_id_append, h2, tfc_cnt_app c, tfc_cnt_app c,
    tfc_cnt_app c, tfc_cntFlat_flatMap c, tfc_cntFlat_flatMap c]
  omega

/-- A zone's count is bounded by the pile-flat total (the single-member
companion of `Orig/Reach.lean:1569`'s family). -/
private theorem tfc_cntFlat_list_mem_ge {c : Card} {zn : List Card} : ∀ (zs : List (List Card)),
    zn ∈ zs → tfc_cnt c zn ≤ tfc_cntFlat c zs := by
  intro zs
  induction zs with
  | nil => intro hmem; exact absurd hmem (by simp)
  | cons z t ih =>
      intro hmem
      rcases List.mem_cons.mp hmem with h' | h'
      · rw [h']
        exact Nat.le_add_right _ _
      · have h1 : tfc_cnt c zn ≤ tfc_cntFlat c t := ih h'
        show tfc_cnt c zn ≤ tfc_cnt c z + tfc_cntFlat c t
        omega

/-- A pile's face-up count is bounded by the state's card count
(the WF-free reading of the count lane). -/
private theorem tfc_faceUp_cnt_le_cardCount {st : State} {x : Card} {a : Anchor} :
    tfc_cnt x (st.piles a).faceUp ≤ st.cardCount x := by
  have h1 : tfc_cnt x (st.piles a).faceUp
      ≤ tfc_cnt x ((st.piles a).hidden ++ (st.piles a).faceUp) := by
    rw [tfc_cnt_app x]
    omega
  have h2 : tfc_cnt x ((st.piles a).hidden ++ (st.piles a).faceUp)
      ≤ tfc_cntFlat x (Anchor.all.map fun a' => (st.piles a').hidden ++ (st.piles a').faceUp) :=
    tfc_cntFlat_list_mem_ge
      (Anchor.all.map fun a' => (st.piles a').hidden ++ (st.piles a').faceUp)
      (List.mem_map.2 ⟨a, Anchor.mem_all a, rfl⟩)
  have h3 := tfc_cardCount_zones st x
  omega

/-- PORT verbatim from `Orig/Reach.lean:1569`. -/
private theorem tfc_cntFlat_map_ge1 {α : Type} {z : Card} (F : α → List Card) :
    ∀ (L : List α) (b : α), b ∈ L → z ∈ F b → 1 ≤ tfc_cntFlat z (L.map F) := by
  intro L
  induction L with
  | nil => intro b h; exact absurd h List.not_mem_nil
  | cons x t ih =>
      intro b hmem hz
      rw [List.map_cons, tfc_cntFlat_cons]
      rcases List.mem_cons.mp hmem with h' | h'
      · rw [h'] at hz
        have := tfc_mem_le_cnt _ hz
        omega
      · have := ih b h' hz
        omega

/-- PORT verbatim from `Orig/Reach.lean:1586`. -/
private theorem tfc_cntFlat_map_two_mem {α : Type} {z : Card} (F : α → List Card) :
    ∀ (L : List α) (b₁ b₂ : α), b₁ ∈ L → b₂ ∈ L → b₁ ≠ b₂ →
      z ∈ F b₁ → z ∈ F b₂ → 2 ≤ tfc_cntFlat z (L.map F) := by
  intro L
  induction L with
  | nil => intro b₁ b₂ h₁; exact absurd h₁ List.not_mem_nil
  | cons x t ih =>
      intro b₁ b₂ h₁ h₂ hne hz₁ hz₂
      rw [List.map_cons, tfc_cntFlat_cons]
      rcases List.mem_cons.mp h₁ with h₁' | h₁'
      · rw [h₁'] at hne hz₁
        rcases List.mem_cons.mp h₂ with h₂' | h₂'
        · exact absurd h₂'.symm hne
        · have e₁ : 1 ≤ tfc_cnt z (F x) := tfc_mem_le_cnt _ hz₁
          have e₂ : 1 ≤ tfc_cntFlat z (List.map F t) := tfc_cntFlat_map_ge1 F t b₂ h₂' hz₂
          omega
      · rcases List.mem_cons.mp h₂ with h₂' | h₂'
        · rw [h₂'] at hz₂
          have e₂ : 1 ≤ tfc_cnt z (F x) := tfc_mem_le_cnt _ hz₂
          have e₁ : 1 ≤ tfc_cntFlat z (List.map F t) := tfc_cntFlat_map_ge1 F t b₁ h₁' hz₁
          omega
        · have := ih b₁ b₂ h₁' h₂' hne hz₁ hz₂
          omega

/-- PORT verbatim from `Orig/Reach.lean:1612`. -/
private theorem tfc_two_pile_zone_absurd {st : State} {z : Card} {j k : Anchor} (hjk : j ≠ k)
    (hcc : st.cardCount z = 1)
    (hzj : z ∈ (st.piles j).hidden ++ (st.piles j).faceUp)
    (hzk : z ∈ (st.piles k).hidden ++ (st.piles k).faceUp) : False := by
  rw [tfc_cardCount_zones] at hcc
  have h2 := tfc_cntFlat_map_two_mem
    (fun a => (st.piles a).hidden ++ (st.piles a).faceUp) Anchor.all j k
    (Anchor.mem_all j) (Anchor.mem_all k) hjk hzj hzk
  omega

/-! ## §B. The list/run kit  (PORT: `Orig/Reach.lean:350-553`, `:1071-1164`
plus `Orig/Classify.lean:294, :310, :392` via `Orig2/Classification.lean`) -/

/-- The `getLast?`/`lastOf` bridge (fresh row over the seam's
`Orig/State.lean:116`: the two recursions are the same). -/
private theorem tfc_getLast?_lastOf : ∀ (l : List Card), l.getLast? = lastOf l
  | [] => rfl
  | [x] => rfl
  | x :: y :: t => tfc_getLast?_lastOf (y :: t)

/-- The last lands in an appended nonempty suffix (fresh row, the
`Orig/Classify.lean:195` pattern). -/
private theorem tfc_lastOf_append_ne : ∀ (A : List Card) {r : List Card},
    r ≠ [] → lastOf (A ++ r) = lastOf r := by
  intro A
  induction A with
  | nil => intro r _; rfl
  | cons x t ih =>
      intro r hr
      show lastOf (x :: (t ++ r)) = lastOf r
      have hne : t ++ r ≠ [] := by
        intro hc
        have hl := congrArg List.length hc
        rw [List.length_append, List.length_nil] at hl
        exact hr (List.length_eq_zero_iff.mp (show r.length = 0 by omega))
      have hlast : lastOf (x :: (t ++ r)) = lastOf (t ++ r) := by
        obtain ⟨y, ys, hc⟩ := list_cons_of_ne_nil hne
        rw [hc]
        rfl
      rw [hlast]
      exact ih hr

/-- PORT verbatim from `Orig/Reach.lean:357`. -/
private theorem tfc_fromCard_cons (c x : Card) (t : List Card) :
    fromCard c (x :: t) = if x = c then x :: t else fromCard c t := rfl

/-- PORT of `Orig2/Classification.lean:1383` (`below_join`, frozen home
`Orig/Classify.lean:282`; Reach's `below_fromCard` at `:360` identical). -/
private theorem tfc_below_fromCard (c : Card) : ∀ (l : List Card),
    below c l ++ fromCard c l = l := by
  intro l
  induction l with
  | nil => rfl
  | cons x t ih =>
      rw [below_cons, tfc_fromCard_cons]
      by_cases hxc : x = c
      · rw [ite_eq_left hxc, ite_eq_left hxc]; rfl
      · rw [ite_eq_right hxc, ite_eq_right hxc, List.cons_append, ih]

/-- PORT verbatim from `Orig/Reach.lean:371`. -/
private theorem tfc_mem_fromCard {c x : Card} : ∀ (l : List Card), x ∈ fromCard c l → x ∈ l := by
  intro l
  induction l with
  | nil => intro h; exact absurd h List.not_mem_nil
  | cons y t ih =>
      intro h
      rw [tfc_fromCard_cons] at h
      by_cases hyc : y = c
      · rw [ite_eq_left hyc] at h
        rcases List.mem_cons.mp h with h' | h'
        · exact List.mem_cons.mpr (Or.inl h')
        · exact List.mem_cons.mpr (Or.inr h')
      · rw [ite_eq_right hyc] at h
        exact List.mem_cons.mpr (Or.inr (ih h))

/-- PORT verbatim from `Orig/Reach.lean:388`. -/
private theorem tfc_fromCard_cons_head {c : Card} : ∀ (l : List Card), c ∈ l →
    ∃ r, fromCard c l = c :: r := by
  intro l
  induction l with
  | nil => intro h; exact absurd h List.not_mem_nil
  | cons x t ih =>
      intro h
      by_cases hxc : x = c
      · exact ⟨t, by rw [tfc_fromCard_cons, ite_eq_left hxc, hxc]⟩
      · obtain ⟨r, hr⟩ := ih (List.mem_cons.mp h |>.resolve_left (fun h' => hxc h'.symm))
        exact ⟨r, by rw [tfc_fromCard_cons, ite_eq_right hxc, hr]⟩

/-- PORT of `Orig2/Classification.lean:1396` (`below_not_mem_self`,
frozen home `Orig/Classify.lean:294`). -/
private theorem tfc_below_not_mem_self (c : Card) : ∀ (l : List Card), c ∉ below c l := by
  intro l
  induction l with
  | nil => intro h; cases h
  | cons y t ih =>
      rw [below_cons]
      split
      · intro h; cases h
      · rename_i hy
        intro h
        rcases List.mem_cons.1 h with hyc | hm
        · exact absurd hyc.symm hy
        · exact ih hm

/-- PORT of `Orig2/Classification.lean:1412` (`below_fromCard_excl`,
frozen home `Orig/Classify.lean:310`). -/
private theorem tfc_below_fromCard_excl (c : Card) : ∀ (X l : List Card), c ∉ X →
    below c (X ++ l) = X ++ below c l ∧ fromCard c (X ++ l) = fromCard c l := by
  intro X
  induction X with
  | nil => intro l _; exact ⟨rfl, rfl⟩
  | cons y t ih =>
      intro l hc
      have hy : y ≠ c := fun heq => hc (List.mem_cons.2 (Or.inl heq.symm))
      have hcT : c ∉ t := fun hm => hc (List.mem_cons.2 (Or.inr hm))
      constructor
      · show below c (y :: (t ++ l)) = y :: (t ++ below c l)
        rw [below_cons, ite_eq_right hy]
        exact congrArg (y :: ·) (ih l hcT).1
      · show fromCard c (y :: (t ++ l)) = fromCard c l
        rw [tfc_fromCard_cons, ite_eq_right hy]
        exact (ih l hcT).2

/-- A member of the front list stops `below` there (fresh row). -/
private theorem tfc_below_mem_append_left {c : Card} : ∀ (A B : List Card), c ∈ A →
    below c (A ++ B) = below c A := by
  intro A B
  induction A with
  | nil => intro h; cases h
  | cons x t ih =>
      intro h
      show below c (x :: (t ++ B)) = below c (x :: t)
      rw [below_cons, below_cons]
      by_cases hxc : x = c
      · rw [ite_eq_left hxc, ite_eq_left hxc]
      · rw [ite_eq_right hxc, ite_eq_right hxc]
        rcases List.mem_cons.mp h with heq | h'
        · exact absurd heq.symm hxc
        · exact congrArg (x :: ·) (ih h')

/-- PORT verbatim from `Orig/Reach.lean:479`. -/
private theorem tfc_runOK_two_true {x y : Card} {t : List Card}
    (h : runOK (x :: y :: t) = true) :
    canSitOn y x = true ∧ runOK (y :: t) = true := by
  rw [show runOK (x :: y :: t) = (canSitOn y x && runOK (y :: t)) from rfl,
    Bool.and_eq_true] at h
  exact h

/-- PORT verbatim from `Orig/Reach.lean:489`. -/
private theorem tfc_runOK_below : ∀ (l : List Card) (c : Card),
    runOK l = true → runOK (below c l) = true
  | [], _, _ => rfl
  | [x], c, _ => by
      rw [below_cons]
      by_cases hxc : x = c
      · rw [ite_eq_left hxc]; rfl
      · rw [ite_eq_right hxc]; rfl
  | x :: y :: t, c, h => by
      obtain ⟨h1, h2⟩ := tfc_runOK_two_true h
      have ih := tfc_runOK_below (y :: t) c h2
      rw [below_cons]
      by_cases hxc : x = c
      · rw [ite_eq_left hxc]; rfl
      · rw [ite_eq_right hxc]
        rw [below_cons]
        by_cases hyc : y = c
        · rw [ite_eq_left hyc]; rfl
        · rw [ite_eq_right hyc]
          have hc : below c (y :: t) = y :: below c t := by
            rw [below_cons, ite_eq_right hyc]
          have ih' : runOK (y :: below c t) = true := by
            rw [← hc]; exact ih
          show (canSitOn y x && runOK (y :: below c t)) = true
          rw [ih', h1]
          rfl

/-- PORT verbatim from `Orig/Reach.lean:518`. -/
private theorem tfc_runOK_fromCard : ∀ (l : List Card) (c : Card),
    runOK l = true → runOK (fromCard c l) = true
  | [], _, _ => rfl
  | [x], c, _ => by
      rw [tfc_fromCard_cons]
      by_cases hxc : x = c
      · rw [ite_eq_left hxc]; rfl
      · rw [ite_eq_right hxc]; rfl
  | x :: y :: t, c, h => by
      obtain ⟨h1, h2⟩ := tfc_runOK_two_true h
      rw [tfc_fromCard_cons]
      by_cases hxc : x = c
      · rw [ite_eq_left hxc]; exact h
      · rw [ite_eq_right hxc]
        exact tfc_runOK_fromCard (y :: t) c h2

/-- PORT verbatim from `Orig/Reach.lean:536`. -/
private theorem tfc_runOK_append_fit : ∀ (l : List Card) (c z : Card) (r : List Card),
    runOK l = true → runOK (c :: r) = true → lastOf l = some z →
    canSitOn c z = true → runOK (l ++ c :: r) = true
  | [], _, _, _, _, _, hlast, _ => absurd hlast (by simp [lastOf])
  | [y], c, z, r, h, hc, hlast, hfit => by
      show (canSitOn c y && runOK (c :: r)) = true
      rw [show y = z from Option.some.inj hlast, hfit, hc]
      rfl
  | x :: y :: t, c, z, r, h, hc, hlast, hfit => by
      obtain ⟨h1, h2⟩ := tfc_runOK_two_true h
      show (canSitOn y x && runOK ((y :: t) ++ c :: r)) = true
      rw [h1]
      exact tfc_runOK_append_fit (y :: t) c z r h2 hc
        (show lastOf (y :: t) = some z from hlast) hfit

/-- PORT of `Orig2/Classification.lean:679` (`runOK_append_right`,
frozen home `Orig/Classify.lean:392`). -/
private theorem tfc_runOK_prefix : ∀ (A B : List Card),
    runOK (A ++ B) = true → runOK A = true := by
  intro A
  induction A with
  | nil => intro _ _; rfl
  | cons y t ih =>
      intro B h
      match t with
      | [] => rfl
      | w :: t' =>
          have h' : runOK (y :: w :: (t' ++ B)) = true := h
          rw [runOK, Bool.and_eq_true] at h' ⊢
          exact ⟨h'.1, ih B h'.2⟩

/-- PORT verbatim from `Orig/Reach.lean:1118`. -/
private theorem tfc_runOK_tail_lt : ∀ (t : List Card) (x y : Card),
    runOK (x :: t) = true → y ∈ t → y.rank.toIdx < x.rank.toIdx := by
  intro t
  induction t with
  | nil => intro x y _ hmem; exact absurd hmem List.not_mem_nil
  | cons w ws ih =>
      intro x y hrun hmem
      have hsplit := tfc_runOK_two_true hrun
      obtain ⟨hsit, hrest⟩ := hsplit
      have hwlt : w.rank.toIdx + 1 = x.rank.toIdx := (canSitOn_eq w x).mp hsit |>.1
      rcases List.mem_cons.mp hmem with hmem' | hmem'
      · rw [hmem']
        omega
      · have hy := ih w y hrest hmem'
        omega

/-- PORT verbatim from `Orig/Reach.lean:1136`. -/
private theorem tfc_lastOf_mem_fromCard : ∀ (l : List Card) (c : Card),
    c ∈ l → ∀ z, lastOf l = some z → z ∈ fromCard c l
  | [], _, hmem, _, _ => absurd hmem List.not_mem_nil
  | [w], c, hmem, z, hlast => by
      have hc : w = c := (List.mem_cons.mp hmem).elim
        (fun h => h.symm) (fun h => absurd h List.not_mem_nil)
      have hwz : w = z := Option.some.inj hlast
      rw [← hwz, ← hc, tfc_fromCard_cons, ite_eq_left rfl]
      exact List.mem_cons.mpr (Or.inl rfl)
  | x :: y :: t, c, hmem, z, hlast => by
      by_cases hxc : x = c
      · rw [tfc_fromCard_cons, ite_eq_left hxc]
        exact lastOf_mem hlast
      · rw [tfc_fromCard_cons, ite_eq_right hxc]
        have hc2 : c ∈ (y :: t) :=
          (List.mem_cons.mp hmem).elim
            (fun h => absurd h.symm hxc) (fun h => h)
        have hlast2 : lastOf (y :: t) = some z := hlast
        exact tfc_lastOf_mem_fromCard (y :: t) c hc2 z hlast2

/-- PORT verbatim from `Orig/Reach.lean:1158`. -/
private theorem tfc_runOK_afterRunRemoved_nil (p : Pile) :
    runOK (Pile.afterRunRemoved p []).faceUp = true := by
  cases p with
  | mk hid fu =>
    cases hid with
    | nil => rfl
    | cons y t => rfl

/-- PORT verbatim from `Orig/Reach.lean:1080`. -/
private theorem tfc_afterRunRemoved_zone_cnt (p : Pile) (post : List Card) (c₀ : Card) :
    ∀ (pre : List Card), p.faceUp = pre ++ post →
    tfc_cnt c₀ ((Pile.afterRunRemoved p pre).hidden
        ++ (Pile.afterRunRemoved p pre).faceUp)
      + tfc_cnt c₀ post = tfc_cnt c₀ (p.hidden ++ p.faceUp) := by
  intro pre
  cases pre with
  | nil =>
      intro hsplit
      cases p with
      | mk hid fu =>
        cases hid with
        | nil =>
            have hf : fu = post := hsplit
            rw [hf]
            show tfc_cnt c₀ (([] : List Card) ++ ([] : List Card)) + tfc_cnt c₀ post
              = tfc_cnt c₀ (([] : List Card) ++ post)
            rw [tfc_cnt_app c₀, tfc_cnt_app c₀, tfc_cnt_nil c₀]
        | cons y t =>
            have hf : fu = post := hsplit
            rw [hf]
            show tfc_cnt c₀ (t ++ ([y] : List Card)) + tfc_cnt c₀ post
              = tfc_cnt c₀ ((y :: t) ++ post)
            rw [tfc_cnt_snoc c₀ y t, List.cons_append, tfc_cnt_def c₀ y (t ++ post),
              tfc_cnt_app c₀ t post, tfc_cnt_def c₀ y ([] : List Card), tfc_cnt_nil c₀]
            omega
  | cons w ws =>
      intro hsplit
      have hfm : Pile.afterRunRemoved p (w :: ws) = { p with faceUp := w :: ws } := rfl
      rw [hfm]
      have hf : p.faceUp = (w :: ws) ++ post := hsplit
      rw [hf]
      show tfc_cnt c₀ (p.hidden ++ (w :: ws)) + tfc_cnt c₀ post
        = tfc_cnt c₀ (p.hidden ++ ((w :: ws) ++ post))
      rw [← List.append_assoc, tfc_cnt_app c₀ (p.hidden ++ (w :: ws)) post]

/-- PORT verbatim from `Orig/Reach.lean:1637`. -/
private theorem tfc_mem_afterRunRemoved_zone_aux : ∀ (hid fu : List Card) (x c : Card)
    (pre : List Card), pre = below c fu →
    x ∈ (Pile.afterRunRemoved ⟨hid, fu⟩ pre).hidden
      ++ (Pile.afterRunRemoved ⟨hid, fu⟩ pre).faceUp →
    x ∈ hid ++ fu
  | hid, fu, x, c, [], _ => by
      intro hz
      cases hid with
      | nil => exact absurd hz List.not_mem_nil
      | cons y t =>
          have hy : x ∈ t ++ ([y] : List Card) := hz
          rcases List.mem_append.mp hy with h' | h'
          · exact List.mem_append.mpr (Or.inl (List.mem_cons.mpr (Or.inr h')))
          · have hx : x = y := by
              rcases List.mem_cons.mp h' with hq | hq
              · exact hq
              · exact absurd hq List.not_mem_nil
            rw [hx]
            exact List.mem_append.mpr (Or.inl List.mem_cons_self)
  | hid, fu, x, c, w :: ws, heq => by
      intro hz
      have hz2 : x ∈ hid ++ (w :: ws) := hz
      rcases List.mem_append.mp hz2 with h' | h'
      · exact List.mem_append.mpr (Or.inl h')
      · exact List.mem_append.mpr
          (Or.inr (mem_below _ (heq ▸ h')))

/-- PORT verbatim from `Orig/Reach.lean:1665`. -/
private theorem tfc_mem_afterRunRemoved_below_zone {p : Pile} {x c : Card}
    (hx : x ∈ (Pile.afterRunRemoved p (below c p.faceUp)).hidden
        ++ (Pile.afterRunRemoved p (below c p.faceUp)).faceUp) :
    x ∈ p.hidden ++ p.faceUp := by
  cases p with
  | mk hid fu => exact tfc_mem_afterRunRemoved_zone_aux hid fu x c _ rfl hx

/-! ## §C. The search rows  (PORT: `Orig/Reach.lean:1624-1635`,
`Orig2/Classification.lean:428` <- `Orig/Irreversible.lean:1272`) -/

/-- PORT of `Orig2/Classification.lean:428` (`pileOfTop_top`, frozen home
`Orig/Irreversible.lean:1272`) at the seam's public search kit. -/
private theorem tfc_pileOfTop_top {st : State} {z : Card} {k : Anchor}
    (h : st.pileOfTop z = some k) :
    (st.piles k).faceUp ≠ [] ∧ lastOf (st.piles k).faceUp = some z := by
  have hd := firstWhere_sound (p := fun a => decide (st.topOf a = some z)) h
  have htop : lastOf (st.piles k).faceUp = some z := of_decide_eq_true hd
  constructor
  · intro hc
    rw [hc] at htop
    exact absurd htop (by simp [lastOf])
  · exact htop

/-- PORT verbatim from `Orig/Reach.lean:1624`. -/
private theorem tfc_top_search_unique {st : State} {z : Card} {j k : Anchor}
    (hcc : st.cardCount z = 1)
    (hj : st.topOf j = some z) (hk : st.topOf k = some z) : j = k := by
  by_cases hne : j = k
  · exact hne
  · exfalso
    have hzj : z ∈ (st.piles j).hidden ++ (st.piles j).faceUp :=
      List.mem_append.mpr (Or.inr (lastOf_mem
        (show lastOf ((st.piles j).faceUp) = some z from hj)))
    have hzk : z ∈ (st.piles k).hidden ++ (st.piles k).faceUp :=
      List.mem_append.mpr (Or.inr (lastOf_mem
        (show lastOf ((st.piles k).faceUp) = some z from hk)))
    exact tfc_two_pile_zone_absurd hne hcc hzj hzk

/-! ## §D. The `tabToTab` conservation fence  (PORT:
`Orig/Reach.lean:1676-2103`; the frozen tier's private row behind the
public `step_wf` at `Orig/Reach.lean:2104`). -/

/-- **The `tabToTab` move preserves `WF`.**  PORT of `Orig/Reach.lean:1676`
(`tabToTab_wf`), restated at the seam's public inversions
(`Orig2/Kit.lean §1e`) and this file's §A-§C ports; statement verbatim. -/
private theorem tfc_tabToTab_wf {st st' : State} {c : Card} {b : Base}
    (hwf : st.WF) (h : State.step st (Move.tabToTab c b) = some st') : st'.WF := by
  obtain ⟨hpre, hpile, hcard, hsd⟩ := hwf
  obtain ⟨a, hhold, hcp, hfr, hrw⟩ := step_tabToTab_inv h
  have hmem : c ∈ (st.piles a).faceUp := pileHolding_mem hhold
  have hbl : below c ((st.piles a).faceUp) ++ fromCard c ((st.piles a).faceUp)
      = (st.piles a).faceUp := tfc_below_fromCard c _
  obtain ⟨r, hcrr⟩ := tfc_fromCard_cons_head _ hmem
  rw [hcrr] at hrw hbl
  have hsplit : (st.piles a).faceUp
      = below c ((st.piles a).faceUp) ++ (c :: r) := hbl.symm
  have hzone : ∀ c₀, tfc_cnt c₀
        ((Pile.afterRunRemoved (st.piles a) (below c (st.piles a).faceUp)).hidden
          ++ (Pile.afterRunRemoved (st.piles a) (below c (st.piles a).faceUp)).faceUp)
      + tfc_cnt c₀ (c :: r) = tfc_cnt c₀ ((st.piles a).hidden ++ (st.piles a).faceUp) :=
    fun c₀ => tfc_afterRunRemoved_zone_cnt (st.piles a) (c :: r) c₀
      (below c (st.piles a).faceUp) hsplit
  have hrok : runOK (c :: r) = true := by
    have hrunok := tfc_runOK_fromCard ((st.piles a).faceUp) c (hpile a)
    rw [hcrr] at hrunok
    exact hrunok
  have hmidne : ∀ j, j ≠ a →
      (st.setPile a
        (Pile.afterRunRemoved (st.piles a) (below c (st.piles a).faceUp))).piles j
      = st.piles j := fun j hj => setPile_piles_ne hj
  have hmidself :
      (st.setPile a
        (Pile.afterRunRemoved (st.piles a) (below c (st.piles a).faceUp))).piles a
      = Pile.afterRunRemoved (st.piles a) (below c (st.piles a).faceUp) :=
    setPile_piles_self
  cases b with
  | inl a₁ =>
      obtain ⟨hempty, -⟩ := canPlace_inl hcp
      have haa₁ : a ≠ a₁ := by
        intro heq
        subst heq
        obtain ⟨hid, hfu⟩ := (Pile.isEmpty_eq _).mp hempty
        rw [hfu] at hmem
        exact absurd hmem List.not_mem_nil
      have hstp : st'.piles
          = (st.setPile a (Pile.afterRunRemoved (st.piles a) (below c (st.piles a).faceUp))
            |>.setPile a₁ ⟨[], c :: r⟩).piles := by rw [hrw, putRun_eq_inl]
      have hfeq : st'.found = st.found := by rw [hrw, putRun_eq_inl]; rfl
      have hstock : st'.stock = st.stock := by rw [hrw, putRun_eq_inl]; rfl
      have hwaste : st'.waste = st.waste := by rw [hrw, putRun_eq_inl]; rfl
      have hsd' : 0 < st'.drawStep := by
        rw [hrw, putRun_eq_inl]
        exact hsd
      refine ⟨?_, ?_, ?_, hsd'⟩
      · intro σ; rw [hfeq]; exact hpre σ
      · intro j
        rcases Decidable.em (j = a₁) with hj | hj
        · rw [hj, show st'.piles a₁
              = (st.setPile a (Pile.afterRunRemoved (st.piles a) (below c (st.piles a).faceUp))
                  |>.setPile a₁ ⟨[], c :: r⟩).piles a₁ from by rw [hstp],
            setPile_piles_self]
          show runOK ((c :: r : List Card)) = true
          exact hrok
        · rw [show st'.piles j
              = (st.setPile a (Pile.afterRunRemoved (st.piles a) (below c (st.piles a).faceUp))
                  |>.setPile a₁ ⟨[], c :: r⟩).piles j from by rw [hstp],
            setPile_piles_ne hj]
          rcases Decidable.em (j = a) with hj2 | hj2
          · rw [hj2, hmidself]
            cases hb : below c ((st.piles a).faceUp) with
            | nil => exact tfc_runOK_afterRunRemoved_nil (st.piles a)
            | cons y t =>
                have hrun := tfc_runOK_below ((st.piles a).faceUp) c (hpile a)
                rw [hb] at hrun
                exact hrun
          · rw [hmidne j hj2]
            exact hpile j
      · intro c₀ hc₀
        have hcc := hcard c₀ hc₀
        rw [tfc_cardCount_zones] at hcc
        rw [tfc_cardCount_zones]
        have hA : tfc_cntFlat c₀ (Anchor.all.map fun j =>
                (st.setPile a (Pile.afterRunRemoved (st.piles a)
                  (below c (st.piles a).faceUp)) |>.piles j).hidden
                  ++ (st.setPile a (Pile.afterRunRemoved (st.piles a)
                  (below c (st.piles a).faceUp)) |>.piles j).faceUp)
            + tfc_cnt c₀ (c :: r)
            = tfc_cntFlat c₀ (Anchor.all.map fun j =>
                (st.piles j).hidden ++ (st.piles j).faceUp) := by
          have h1 := tfc_cntFlat_map_delta c₀
            (fun j => (st.setPile a (Pile.afterRunRemoved (st.piles a)
                (below c (st.piles a).faceUp)) |>.piles j).hidden
              ++ (st.setPile a (Pile.afterRunRemoved (st.piles a)
                (below c (st.piles a).faceUp)) |>.piles j).faceUp)
            (fun j => (st.piles j).hidden ++ (st.piles j).faceUp)
            Anchor.all
            (fun j => if j = a then tfc_cnt c₀ (c :: r) else 0)
            (by intro j _
                by_cases hj : j = a
                · rw [hj, hmidself, ite_eq_left rfl]
                  exact hzone c₀
                · rw [hmidne j hj, ite_eq_right hj]
                  omega)
          have h2 : (Anchor.all.map
              (fun j => if j = a then tfc_cnt c₀ (c :: r) else 0)).sum
              = tfc_cnt c₀ (c :: r) := by
            have h3 := tfc_sum_map_single Anchor.all
              (fun j => if j = a then tfc_cnt c₀ (c :: r) else 0) a
              Anchor.all_nodup (Anchor.mem_all a)
              (by intro j _ hjc; rw [ite_eq_right hjc])
            have h4 : (if a = a then tfc_cnt c₀ (c :: r) else 0) = tfc_cnt c₀ (c :: r) :=
              by rw [ite_eq_left rfl]
            rw [h3, h4]
          rw [← h1, h2]
        have hB : tfc_cntFlat c₀
                (Anchor.all.map fun j => (st'.piles j).hidden ++ (st'.piles j).faceUp)
            = tfc_cntFlat c₀ (Anchor.all.map fun j =>
                (st.setPile a (Pile.afterRunRemoved (st.piles a)
                  (below c (st.piles a).faceUp)) |>.piles j).hidden
                  ++ (st.setPile a (Pile.afterRunRemoved (st.piles a)
                  (below c (st.piles a).faceUp)) |>.piles j).faceUp)
              + tfc_cnt c₀ (c :: r) := by
          have h1 := tfc_cntFlat_map_delta c₀
            (fun j => (st.setPile a (Pile.afterRunRemoved (st.piles a)
                (below c (st.piles a).faceUp)) |>.piles j).hidden
              ++ (st.setPile a (Pile.afterRunRemoved (st.piles a)
                (below c (st.piles a).faceUp)) |>.piles j).faceUp)
            (fun j => ((st.setPile a (Pile.afterRunRemoved (st.piles a)
                  (below c (st.piles a).faceUp)) |>.setPile a₁ ⟨[], c :: r⟩).piles
                j).hidden
              ++ ((st.setPile a (Pile.afterRunRemoved (st.piles a)
                  (below c (st.piles a).faceUp)) |>.setPile a₁ ⟨[], c :: r⟩).piles
                j).faceUp)
            Anchor.all
            (fun j => if j = a₁ then tfc_cnt c₀ (c :: r) else 0)
            (by intro j _
                by_cases hj : j = a₁
                · rw [hj]
                  have hgo : tfc_cnt c₀
                        (((st.setPile a (Pile.afterRunRemoved (st.piles a)
                           (below c (st.piles a).faceUp)) |>.setPile a₁ ⟨[], c :: r⟩).piles
                           a₁).hidden
                        ++ ((st.setPile a (Pile.afterRunRemoved (st.piles a)
                           (below c (st.piles a).faceUp)) |>.setPile a₁ ⟨[], c :: r⟩).piles
                           a₁).faceUp)
                      = tfc_cnt c₀ (c :: r) := by
                    rw [setPile_piles_self]
                    show tfc_cnt c₀ (([] : List Card) ++ ((c :: r : List Card))) = _
                    rw [tfc_cnt_app c₀, tfc_cnt_nil c₀]
                    omega
                  have hzero : tfc_cnt c₀
                        ((st.setPile a (Pile.afterRunRemoved (st.piles a)
                         (below c (st.piles a).faceUp)) |>.piles a₁).hidden
                        ++ (st.setPile a (Pile.afterRunRemoved (st.piles a)
                         (below c (st.piles a).faceUp)) |>.piles a₁).faceUp)
                      = 0 := by
                    have hpma₁ : (st.setPile a (Pile.afterRunRemoved (st.piles a)
                         (below c (st.piles a).faceUp))).piles a₁ = st.piles a₁ :=
                      hmidne a₁ (fun hh => haa₁ hh.symm)
                    rw [hpma₁]
                    obtain ⟨hid, hfu⟩ := (Pile.isEmpty_eq _).mp hempty
                    rw [hid, hfu, tfc_cnt_app c₀, tfc_cnt_nil c₀]
                  rw [ite_eq_left rfl, hzero, hgo]
                  omega
                · rw [ite_eq_right hj]
                  have hident : tfc_cnt c₀
                        (((st.setPile a (Pile.afterRunRemoved (st.piles a)
                          (below c (st.piles a).faceUp))).piles j).hidden
                        ++ ((st.setPile a (Pile.afterRunRemoved (st.piles a)
                          (below c (st.piles a).faceUp))).piles j).faceUp)
                      = tfc_cnt c₀
                        (((st.setPile a (Pile.afterRunRemoved (st.piles a)
                          (below c (st.piles a).faceUp)) |>.setPile a₁ ⟨[], c :: r⟩).piles
                          j).hidden
                        ++ ((st.setPile a (Pile.afterRunRemoved (st.piles a)
                          (below c (st.piles a).faceUp)) |>.setPile a₁ ⟨[], c :: r⟩).piles
                          j).faceUp) := by
                    rw [show ((st.setPile a (Pile.afterRunRemoved (st.piles a)
                        (below c (st.piles a).faceUp)) |>.setPile a₁ ⟨[], c :: r⟩).piles j)
                        = ((st.setPile a (Pile.afterRunRemoved (st.piles a)
                        (below c (st.piles a).faceUp))).piles j)
                        from setPile_piles_ne hj]
                  rw [hident]
                  omega)
          have h2 : (Anchor.all.map
              (fun j => if j = a₁ then tfc_cnt c₀ (c :: r) else 0)).sum
              = tfc_cnt c₀ (c :: r) := by
            have h3 := tfc_sum_map_single Anchor.all
              (fun j => if j = a₁ then tfc_cnt c₀ (c :: r) else 0) a₁
              Anchor.all_nodup (Anchor.mem_all a₁)
              (by intro j _ hjc; rw [ite_eq_right hjc])
            have h4 : (if a₁ = a₁ then tfc_cnt c₀ (c :: r) else 0) = tfc_cnt c₀ (c :: r) :=
              by rw [ite_eq_left rfl]
            rw [h3, h4]
          have hfold : tfc_cntFlat c₀ (Anchor.all.map fun j =>
                (st'.piles j).hidden ++ (st'.piles j).faceUp)
              = tfc_cntFlat c₀ (Anchor.all.map fun j =>
                  ((st.setPile a (Pile.afterRunRemoved (st.piles a)
                    (below c (st.piles a).faceUp)) |>.setPile a₁ ⟨[], c :: r⟩).piles
                    j).hidden
                  ++ ((st.setPile a (Pile.afterRunRemoved (st.piles a)
                    (below c (st.piles a).faceUp)) |>.setPile a₁ ⟨[], c :: r⟩).piles
                    j).faceUp) := by
            rw [hstp]
          rw [hfold, ← h1, h2]
        have hfcnt : tfc_cntFlat c₀ (Suit.all.map st'.found)
            = tfc_cntFlat c₀ (Suit.all.map st.found) := by rw [hfeq]
        have hstockc : tfc_cnt c₀ st'.stock = tfc_cnt c₀ st.stock := by rw [hstock]
        have hwastec : tfc_cnt c₀ st'.waste = tfc_cnt c₀ st.waste := by rw [hwaste]
        omega
  | inr z =>
      obtain ⟨k, hps, hfit⟩ := canPlace_inr hcp
      have hkmem : st.topOf k = some z := (tfc_pileOfTop_top hps).2
      have hzuni : z ∈ Card.universe := Card.mem_universe z
      have hccz : st.cardCount z = 1 := hcard z hzuni
      have hfitidx : c.rank.toIdx + 1 = z.rank.toIdx := (canSitOn_eq c z).mp hfit |>.1
      have hak : a ≠ k := by
        intro heq
        subst heq
        have hlast : lastOf ((st.piles a).faceUp) = some z := (tfc_pileOfTop_top hps).2
        have hzr := tfc_lastOf_mem_fromCard ((st.piles a).faceUp) c hmem z hlast
        rw [hcrr] at hzr
        rcases List.mem_cons.mp hzr with hz | hz
        · rw [← hz] at hfitidx
          omega
        · have hlt := tfc_runOK_tail_lt r c z hrok hz
          omega
      have hpmid : (st.setPile a (Pile.afterRunRemoved (st.piles a)
            (below c (st.piles a).faceUp))).pileOfTop z = some k := by
        have hmidk : (st.setPile a (Pile.afterRunRemoved (st.piles a)
              (below c (st.piles a).faceUp))).topOf k = st.topOf k := by
          show ((st.setPile a (Pile.afterRunRemoved (st.piles a)
              (below c (st.piles a).faceUp))).piles k).top = ((st.piles k).top)
          rw [show (st.setPile a (Pile.afterRunRemoved (st.piles a)
              (below c (st.piles a).faceUp))).piles k = (st.piles k)
              from hmidne k (fun hh => hak hh.symm)]
        refine firstWhere_find (Anchor.mem_all k) ?_ ?_
        · rw [hmidk, hkmem]
          exact decide_eq_true rfl
        · intro j _ hjk
          by_cases hja : j = a
          · rw [hja]
            have hnot : (st.setPile a (Pile.afterRunRemoved (st.piles a)
                  (below c (st.piles a).faceUp))).topOf a ≠ some z := by
              intro hcon
              have hznew : z ∈ ((st.setPile a (Pile.afterRunRemoved (st.piles a)
                     (below c (st.piles a).faceUp))).piles a).hidden
                  ++ ((st.setPile a (Pile.afterRunRemoved (st.piles a)
                     (below c (st.piles a).faceUp))).piles a).faceUp :=
                List.mem_append.mpr (Or.inr (lastOf_mem hcon))
              rw [hmidself] at hznew
              have hzold : z ∈ (st.piles a).hidden ++ (st.piles a).faceUp :=
                tfc_mem_afterRunRemoved_below_zone hznew
              have hzk : z ∈ (st.piles k).hidden ++ (st.piles k).faceUp :=
                List.mem_append.mpr (Or.inr (lastOf_mem hkmem))
              exact tfc_two_pile_zone_absurd hak hccz hzold hzk
            exact decide_false_of_not hnot
          · have hnot : (st.setPile a (Pile.afterRunRemoved (st.piles a)
                  (below c (st.piles a).faceUp))).topOf j ≠ some z := by
              intro hcon
              have hx := congrArg Pile.top (hmidne j hja)
              have hcon2 : (st.piles j).top = some z := by
                rw [← hx]; exact hcon
              exact hjk (tfc_top_search_unique hccz hcon2 hkmem)
            exact decide_false_of_not hnot
      have hstp : st'.piles
          = (st.setPile a (Pile.afterRunRemoved (st.piles a) (below c (st.piles a).faceUp))
            |>.setPile k { (st.setPile a (Pile.afterRunRemoved (st.piles a)
              (below c (st.piles a).faceUp))).piles k with faceUp :=
                ((st.setPile a (Pile.afterRunRemoved (st.piles a)
              (below c (st.piles a).faceUp))).piles k).faceUp ++ (c :: r) }).piles := by
        rw [hrw, putRun_inr_eq hpmid]
      have hfeq : st'.found = st.found := by rw [hrw, putRun_inr_eq hpmid]; rfl
      have hstock : st'.stock = st.stock := by rw [hrw, putRun_inr_eq hpmid]; rfl
      have hwaste : st'.waste = st.waste := by rw [hrw, putRun_inr_eq hpmid]; rfl
      have hsd' : 0 < st'.drawStep := by
        rw [hrw, putRun_inr_eq hpmid]
        exact hsd
      refine ⟨?_, ?_, ?_, hsd'⟩
      · intro σ; rw [hfeq]; exact hpre σ
      · intro j
        rcases Decidable.em (j = k) with hj | hj
        · rw [hj, show st'.piles k
              = (st.setPile a (Pile.afterRunRemoved (st.piles a) (below c (st.piles a).faceUp))
                  |>.setPile k { (st.setPile a (Pile.afterRunRemoved (st.piles a)
                      (below c (st.piles a).faceUp))).piles k with faceUp :=
                        ((st.setPile a (Pile.afterRunRemoved (st.piles a)
                      (below c (st.piles a).faceUp))).piles k).faceUp ++ (c :: r) }).piles k
              from by rw [hstp],
            setPile_piles_self, hmidne k (fun hh => hak hh.symm)]
          show runOK (((st.piles k).faceUp) ++ (c :: r)) = true
          exact tfc_runOK_append_fit ((st.piles k).faceUp) c z r
            (hpile k) hrok hkmem hfit
        · rw [show st'.piles j
              = (st.setPile a (Pile.afterRunRemoved (st.piles a) (below c (st.piles a).faceUp))
                  |>.setPile k { (st.setPile a (Pile.afterRunRemoved (st.piles a)
                      (below c (st.piles a).faceUp))).piles k with faceUp :=
                        ((st.setPile a (Pile.afterRunRemoved (st.piles a)
                      (below c (st.piles a).faceUp))).piles k).faceUp ++ (c :: r) }).piles j
              from by rw [hstp],
            setPile_piles_ne hj]
          rcases Decidable.em (j = a) with hj2 | hj2
          · rw [hj2, hmidself]
            cases hb : below c ((st.piles a).faceUp) with
            | nil => exact tfc_runOK_afterRunRemoved_nil (st.piles a)
            | cons y t =>
                have hrun := tfc_runOK_below ((st.piles a).faceUp) c (hpile a)
                rw [hb] at hrun
                exact hrun
          · rw [hmidne j hj2]
            exact hpile j
      · intro c₀ hc₀
        have hcc := hcard c₀ hc₀
        rw [tfc_cardCount_zones] at hcc
        rw [tfc_cardCount_zones]
        have hA : tfc_cntFlat c₀ (Anchor.all.map fun j =>
                (st.setPile a (Pile.afterRunRemoved (st.piles a)
                  (below c (st.piles a).faceUp)) |>.piles j).hidden
                  ++ (st.setPile a (Pile.afterRunRemoved (st.piles a)
                  (below c (st.piles a).faceUp)) |>.piles j).faceUp)
            + tfc_cnt c₀ (c :: r)
            = tfc_cntFlat c₀ (Anchor.all.map fun j =>
                (st.piles j).hidden ++ (st.piles j).faceUp) := by
          have h1 := tfc_cntFlat_map_delta c₀
            (fun j => (st.setPile a (Pile.afterRunRemoved (st.piles a)
                (below c (st.piles a).faceUp)) |>.piles j).hidden
              ++ (st.setPile a (Pile.afterRunRemoved (st.piles a)
                (below c (st.piles a).faceUp)) |>.piles j).faceUp)
            (fun j => (st.piles j).hidden ++ (st.piles j).faceUp)
            Anchor.all
            (fun j => if j = a then tfc_cnt c₀ (c :: r) else 0)
            (by intro j _
                by_cases hj : j = a
                · rw [hj, hmidself, ite_eq_left rfl]
                  exact hzone c₀
                · rw [hmidne j hj, ite_eq_right hj]
                  omega)
          have h2 : (Anchor.all.map
              (fun j => if j = a then tfc_cnt c₀ (c :: r) else 0)).sum
              = tfc_cnt c₀ (c :: r) := by
            have h3 := tfc_sum_map_single Anchor.all
              (fun j => if j = a then tfc_cnt c₀ (c :: r) else 0) a
              Anchor.all_nodup (Anchor.mem_all a)
              (by intro j _ hjc; rw [ite_eq_right hjc])
            have h4 : (if a = a then tfc_cnt c₀ (c :: r) else 0) = tfc_cnt c₀ (c :: r) :=
              by rw [ite_eq_left rfl]
            rw [h3, h4]
          rw [← h1, h2]
        have hB : tfc_cntFlat c₀
                (Anchor.all.map fun j => (st'.piles j).hidden ++ (st'.piles j).faceUp)
            = tfc_cntFlat c₀ (Anchor.all.map fun j =>
                (st.setPile a (Pile.afterRunRemoved (st.piles a)
                  (below c (st.piles a).faceUp)) |>.piles j).hidden
                  ++ (st.setPile a (Pile.afterRunRemoved (st.piles a)
                  (below c (st.piles a).faceUp)) |>.piles j).faceUp)
              + tfc_cnt c₀ (c :: r) := by
          have h1 := tfc_cntFlat_map_delta c₀
            (fun j => (st.setPile a (Pile.afterRunRemoved (st.piles a)
                (below c (st.piles a).faceUp)) |>.piles j).hidden
              ++ (st.setPile a (Pile.afterRunRemoved (st.piles a)
                (below c (st.piles a).faceUp)) |>.piles j).faceUp)
            (fun j => ((st.setPile a (Pile.afterRunRemoved (st.piles a)
                  (below c (st.piles a).faceUp)) |>.setPile k { (st.setPile a
                  (Pile.afterRunRemoved (st.piles a) (below c (st.piles a).faceUp))).piles k with
                    faceUp := ((st.setPile a (Pile.afterRunRemoved (st.piles a)
                  (below c (st.piles a).faceUp))).piles k).faceUp ++ (c :: r) }).piles
                j).hidden
              ++ ((st.setPile a (Pile.afterRunRemoved (st.piles a)
                  (below c (st.piles a).faceUp)) |>.setPile k { (st.setPile a
                  (Pile.afterRunRemoved (st.piles a) (below c (st.piles a).faceUp))).piles k with
                    faceUp := ((st.setPile a (Pile.afterRunRemoved (st.piles a)
                  (below c (st.piles a).faceUp))).piles k).faceUp ++ (c :: r) }).piles
                j).faceUp)
            Anchor.all
            (fun j => if j = k then tfc_cnt c₀ (c :: r) else 0)
            (by intro j _
                by_cases hj : j = k
                · have hgo : tfc_cnt c₀
                         (((st.setPile a (Pile.afterRunRemoved (st.piles a)
                            (below c (st.piles a).faceUp)) |>.setPile k { (st.setPile a
                            (Pile.afterRunRemoved (st.piles a) (below c (st.piles a).faceUp))).piles k with
                              faceUp := ((st.setPile a (Pile.afterRunRemoved (st.piles a)
                            (below c (st.piles a).faceUp))).piles k).faceUp ++ (c :: r) }).piles
                            k).hidden
                          ++ ((st.setPile a (Pile.afterRunRemoved (st.piles a)
                            (below c (st.piles a).faceUp)) |>.setPile k { (st.setPile a
                            (Pile.afterRunRemoved (st.piles a) (below c (st.piles a).faceUp))).piles k with
                              faceUp := ((st.setPile a (Pile.afterRunRemoved (st.piles a)
                            (below c (st.piles a).faceUp))).piles k).faceUp ++ (c :: r) }).piles
                            k).faceUp)
                      = tfc_cnt c₀
                         (((st.setPile a (Pile.afterRunRemoved (st.piles a)
                            (below c (st.piles a).faceUp))).piles k).hidden
                          ++ (((st.setPile a (Pile.afterRunRemoved (st.piles a)
                            (below c (st.piles a).faceUp))).piles k).faceUp ++ (c :: r))) := by
                    rw [setPile_piles_self]
                  rw [hj, hgo, ite_eq_left rfl, hmidne k (fun hh => hak hh.symm),
                    ← List.append_assoc, tfc_cnt_app c₀, tfc_cnt_app c₀, tfc_cnt_app c₀]
                · rw [ite_eq_right hj]
                  have hident : tfc_cnt c₀
                         (((st.setPile a (Pile.afterRunRemoved (st.piles a)
                           (below c (st.piles a).faceUp))).piles j).hidden
                          ++ ((st.setPile a (Pile.afterRunRemoved (st.piles a)
                           (below c (st.piles a).faceUp))).piles j).faceUp)
                      = tfc_cnt c₀
                         (((st.setPile a (Pile.afterRunRemoved (st.piles a)
                           (below c (st.piles a).faceUp)) |>.setPile k { (st.setPile a
                           (Pile.afterRunRemoved (st.piles a) (below c (st.piles a).faceUp))).piles k with
                             faceUp := ((st.setPile a (Pile.afterRunRemoved (st.piles a)
                           (below c (st.piles a).faceUp))).piles k).faceUp ++ (c :: r) }).piles
                           j).hidden
                          ++ ((st.setPile a (Pile.afterRunRemoved (st.piles a)
                           (below c (st.piles a).faceUp)) |>.setPile k { (st.setPile a
                           (Pile.afterRunRemoved (st.piles a) (below c (st.piles a).faceUp))).piles k with
                             faceUp := ((st.setPile a (Pile.afterRunRemoved (st.piles a)
                           (below c (st.piles a).faceUp))).piles k).faceUp ++ (c :: r) }).piles
                           j).faceUp) := by
                    rw [show ((st.setPile a (Pile.afterRunRemoved (st.piles a)
                        (below c (st.piles a).faceUp)) |>.setPile k { (st.setPile a
                        (Pile.afterRunRemoved (st.piles a) (below c (st.piles a).faceUp))).piles k with
                          faceUp := ((st.setPile a (Pile.afterRunRemoved (st.piles a)
                        (below c (st.piles a).faceUp))).piles k).faceUp ++ (c :: r) }).piles j)
                        = ((st.setPile a (Pile.afterRunRemoved (st.piles a)
                        (below c (st.piles a).faceUp))).piles j)
                        from setPile_piles_ne hj]
                  rw [hident]
                  omega)
          have h2 : (Anchor.all.map
              (fun j => if j = k then tfc_cnt c₀ (c :: r) else 0)).sum
              = tfc_cnt c₀ (c :: r) := by
            have h3 := tfc_sum_map_single Anchor.all
              (fun j => if j = k then tfc_cnt c₀ (c :: r) else 0) k
              Anchor.all_nodup (Anchor.mem_all k)
              (by intro j _ hjc; rw [ite_eq_right hjc])
            have h4 : (if k = k then tfc_cnt c₀ (c :: r) else 0) = tfc_cnt c₀ (c :: r) :=
              by rw [ite_eq_left rfl]
            rw [h3, h4]
          have hfold : tfc_cntFlat c₀ (Anchor.all.map fun j =>
                (st'.piles j).hidden ++ (st'.piles j).faceUp)
              = tfc_cntFlat c₀ (Anchor.all.map fun j =>
                  ((st.setPile a (Pile.afterRunRemoved (st.piles a)
                    (below c (st.piles a).faceUp)) |>.setPile k { (st.setPile a
                    (Pile.afterRunRemoved (st.piles a) (below c (st.piles a).faceUp))).piles k with
                      faceUp := ((st.setPile a (Pile.afterRunRemoved (st.piles a)
                    (below c (st.piles a).faceUp))).piles k).faceUp ++ (c :: r) }).piles
                    j).hidden
                  ++ ((st.setPile a (Pile.afterRunRemoved (st.piles a)
                    (below c (st.piles a).faceUp)) |>.setPile k { (st.setPile a
                    (Pile.afterRunRemoved (st.piles a) (below c (st.piles a).faceUp))).piles k with
                      faceUp := ((st.setPile a (Pile.afterRunRemoved (st.piles a)
                    (below c (st.piles a).faceUp))).piles k).faceUp ++ (c :: r) }).piles
                    j).faceUp) := by
            rw [hstp]
          rw [hfold, ← h1, h2]
        have hfcnt : tfc_cntFlat c₀ (Suit.all.map st'.found)
            = tfc_cntFlat c₀ (Suit.all.map st.found) := by rw [hfeq]
        have hstockc : tfc_cnt c₀ st'.stock = tfc_cnt c₀ st.stock := by rw [hstock]
        have hwastec : tfc_cnt c₀ st'.waste = tfc_cnt c₀ st.waste := by rw [hwaste]
        omega

/-! ## §E. The search-completeness and seat rows -/

/-- Fresh row at the seam's `firstWhere` (`Orig/State.lean:40`): a
satisfied item means the search answers. -/
private theorem tfc_firstWhere_mem_true {α : Type} {p : α → Bool} : ∀ (L : List α) (y : α),
    y ∈ L → p y = true → firstWhere p L ≠ none := by
  intro L
  induction L with
  | nil => intro y hmem; exact absurd hmem (by simp)
  | cons x t ih =>
      intro y hmem hp
      rw [firstWhere]
      by_cases hpx : p x = true
      · rw [hpx]
        exact (by simp)
      · have hpx' : p x = false := by
          cases hxp : p x with
          | true => exact absurd hxp hpx
          | false => rfl
        rw [hpx']
        rcases List.mem_cons.mp hmem with heq | hta
        · rw [heq] at hp
          rw [hp] at hpx
          exact absurd hpx (by simp)
        · exact ih y hta hp

/-- Fresh row: the completed search's converse (all false, none found). -/
private theorem tfc_firstWhere_none {α : Type} {p : α → Bool} : ∀ (L : List α),
    (∀ y ∈ L, p y = false) → firstWhere p L = none
  | [], _ => rfl
  | x :: t, h => by
      rw [firstWhere, h x (by simp)]
      exact tfc_firstWhere_none t (fun y hy => h y (by simp [hy]))

/-- A hidden card is not face-up anywhere: the holding search sees
face-up content only (fresh row over `Orig/State.lean:339`). -/
private theorem tfc_not_mem_faceUp_of_holdNone {st : State} {x : Card}
    (hj : st.pileHolding x = none) (j : Anchor) : x ∉ (st.piles j).faceUp := by
  intro hmem
  have h1 := tfc_firstWhere_mem_true
    (p := fun a => decide (x ∈ (st.piles a).faceUp)) Anchor.all j
    (Anchor.mem_all j) (decide_eq_true hmem)
  rw [show st.pileHolding x
        = firstWhere (fun a => decide (x ∈ (st.piles a).faceUp)) Anchor.all from rfl] at hj
  rw [hj] at h1
  exact h1 rfl

/-! ### §E2. The seat readers (fresh unfolds at `Orig2/Vocab.lean §9`) -/

/-- The canonical form of the seat map (fresh; `rfl` at the registry def). -/
private theorem tfc_seatOf_eq (st : State) (c : Card) :
    seatOf st c = match st.pileHolding c with
      | none => none
      | some a => match List.getLast? (below c (st.piles a).faceUp) with
        | none => some (Sum.inl a)
        | some z => some (Sum.inr z) := rfl

/-- No holding pile: no seat (the `none` arm). -/
private theorem tfc_seatOf_none {st : State} {c : Card} (hh : st.pileHolding c = none) :
    seatOf st c = none := by
  rw [tfc_seatOf_eq, hh]

/-- The located pair form: with the holding pile pinned, the seat is
the below-parts readout (fresh). -/
private theorem tfc_seatOf_pair {st : State} {c : Card} {a : Anchor}
    (hh : st.pileHolding c = some a) :
    seatOf st c = match List.getLast? (below c (st.piles a).faceUp) with
      | none => some (Sum.inl a)
      | some z => some (Sum.inr z) := by
  rw [tfc_seatOf_eq]
  rw [hh]

/-- Fresh row: a cons always has a last (the `Orig/State.lean:116`
recursion never answers `none` on nonempty input). -/
private theorem tfc_lastOf_cons_ne : ∀ (t : List Card) (y : Card), lastOf (y :: t) ≠ none := by
  intro t
  induction t with
  | nil => intro y; exact (by simp [lastOf])
  | cons z t' ih =>
      intro y
      show (lastOf (y :: z :: t') = none) → False
      rw [show lastOf (y :: z :: t') = lastOf (z :: t') from rfl]
      exact ih z

private theorem tfc_seatOf_of_inr {st : State} {c z : Card}
    (h : seatOf st c = some (Sum.inr z)) :
    ∃ a, st.pileHolding c = some a ∧ below c (st.piles a).faceUp ≠ [] ∧
      lastOf (below c (st.piles a).faceUp) = some z := by
  rw [tfc_seatOf_eq] at h
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
            rw [hc, tfc_getLast?_lastOf] at hg
            exact absurd hg (by simp [lastOf])
          · rw [tfc_getLast?_lastOf] at hg
            exact hg

private theorem tfc_seatOf_of_inl {st : State} {c : Card} {a : Anchor}
    (h : seatOf st c = some (Sum.inl a)) :
    st.pileHolding c = some a ∧ below c (st.piles a).faceUp = [] := by
  rw [tfc_seatOf_eq] at h
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
                rw [hc, tfc_getLast?_lastOf] at hg
                exact absurd hg (tfc_lastOf_cons_ne _ _)
          exact ⟨rfl, hbl⟩

/-- The `.inr` introduction. -/
private theorem tfc_seatOf_inr_intro {st : State} {c z : Card} {a : Anchor}
    (hh : st.pileHolding c = some a)
    (hz : lastOf (below c (st.piles a).faceUp) = some z) :
    seatOf st c = some (Sum.inr z) := by
  rw [tfc_seatOf_pair hh, tfc_getLast?_lastOf, hz]

/-- The `.inl` introduction. -/
private theorem tfc_seatOf_inl_intro {st : State} {c : Card} {a : Anchor}
    (hh : st.pileHolding c = some a)
    (hb : below c (st.piles a).faceUp = []) :
    seatOf st c = some (Sum.inl a) := by
  rw [tfc_seatOf_pair hh, hb]
  rfl

/-! ### §E3. The twin algebra and the fitting arithmetic
(the claim-side involution rows `Orig2/Vocab.lean §4.5` anticipated:
"The involution lemmas ride at the Claims layer when needed"). -/

/-- The card-level twin involution (fresh; rides `Suit.twin_twin`,
`Orig/Basic.lean:39`). -/
private theorem tfc_card_twin_twin (c : Card) : c.twin.twin = c := by
  simp [Card.twin]

/-- Same-color suits are equal-or-twin (fresh 16-way kernel row at
`Orig/Basic.lean:28-45`). -/
private theorem tfc_suit_same_color_or_twin {s s' : Suit} (h : s.color = s'.color) :
    s = s' ∨ s = s'.twin := by
  cases s <;> cases s' <;> simp_all [Suit.color, Suit.twin]

/-- THE FITTING PARENTS: any two bases that both fit under `c` are
each other, or twins of each other (rank pin + color pin + the suit
row; fresh, riding `canSitOn_eq` at `Orig/Basic.lean:111`). -/
private theorem tfc_fitting_parent {c w z : Card}
    (hw : canSitOn c w = true) (hz : canSitOn c z = true) :
    w = z ∨ w = z.twin := by
  obtain ⟨hw1, hw2⟩ := (canSitOn_eq c w).mp hw
  obtain ⟨hz1, hz2⟩ := (canSitOn_eq c z).mp hz
  have hrank : w.rank = z.rank := Rank.toIdx_inj (by omega)
  have hcol : w.suit.color = z.suit.color := by
    cases hc : c.suit.color with
    | red =>
        have h1 : w.suit.color = Color.black := by
          cases hwc : w.suit.color with
          | black => rfl
          | red => rw [hwc] at hw2; exact absurd hc hw2
        have h2 : z.suit.color = Color.black := by
          cases hzc : z.suit.color with
          | black => rfl
          | red => rw [hzc] at hz2; exact absurd hc hz2
        rw [h1, h2]
    | black =>
        have h1 : w.suit.color = Color.red := by
          cases hwc : w.suit.color with
          | red => rfl
          | black => rw [hwc] at hw2; exact absurd hc hw2
        have h2 : z.suit.color = Color.red := by
          cases hzc : z.suit.color with
          | red => rfl
          | black => rw [hzc] at hz2; exact absurd hc hz2
        rw [h1, h2]
  rcases tfc_suit_same_color_or_twin hcol with h' | h'
  · left
    rcases w with ⟨ws, wr⟩
    rcases z with ⟨zs, zr⟩
    have hs : ws = zs := h'
    have hr : wr = zr := hrank
    rw [hs, hr]
  · right
    rcases w with ⟨ws, wr⟩
    rcases z with ⟨zs, zr⟩
    have hs : ws = zs.twin := h'
    have hr : wr = zr := hrank
    rw [hs, hr]
    rfl

/-- THE TWO OCCURRENCE LANES: a face-up card that is a below-parent
also carries the seam fit, and tops NO pile (occurrence uniqueness;
the fitting exclusion behind Row 2's hop arithmetic and Row 3's
class fiber). -/
private theorem tfc_seat_parent {st : State} {c z : Card} {a : Anchor}
    (hwf : st.WF) (hh : st.pileHolding c = some a)
    (hz : lastOf (below c (st.piles a).faceUp) = some z) :
    canSitOn c z = true ∧ st.pileOfTop z = none := by
  have hmem : c ∈ (st.piles a).faceUp := pileHolding_mem hh
  have hrok : runOK ((st.piles a).faceUp) = true := hwf.2.1 a
  obtain ⟨tr, hcrr⟩ := tfc_fromCard_cons_head _ hmem
  have hbl : below c ((st.piles a).faceUp) ++ (c :: tr) = (st.piles a).faceUp := by
    have h0 := tfc_below_fromCard c ((st.piles a).faceUp)
    rw [hcrr] at h0
    exact h0
  have hrok2 : runOK (below c ((st.piles a).faceUp) ++ [c]) = true := by
    have hE : (below c ((st.piles a).faceUp) ++ [c]) ++ tr
        = (st.piles a).faceUp := by
      rw [List.append_assoc, List.cons_append, List.nil_append, hbl]
    have hrokX : runOK ((below c ((st.piles a).faceUp) ++ [c]) ++ tr) = true := by
      rw [hE]
      exact hrok
    exact tfc_runOK_prefix _ tr hrokX
  have hbne : below c ((st.piles a).faceUp) ≠ [] := by
    cases hc : below c ((st.piles a).faceUp) with
    | nil => rw [hc] at hz; exact absurd hz (by simp [lastOf])
    | cons y ys => exact fun hcon => absurd hcon (by simp)
  obtain ⟨q, hq, hsit⟩ := runOK_snoc_sit hbne hrok2
  rw [hz] at hq
  injection hq with hq'
  cases hq'
  refine ⟨hsit, ?_⟩
  have hccz : st.cardCount z = 1 := hwf.2.2.1 z (Card.mem_universe z)
  cases hloc : st.pileOfTop z with
  | none => rfl
  | some k =>
      exfalso
      obtain ⟨-, hlzk⟩ := tfc_pileOfTop_top hloc
      by_cases hka : k = a
      · rw [hka] at hloc
        obtain ⟨-, hlz⟩ := tfc_pileOfTop_top hloc
        have hzr := tfc_lastOf_mem_fromCard ((st.piles a).faceUp) c hmem z hlz
        rw [hcrr] at hzr
        rcases List.mem_cons.mp hzr with he | hm
        · rw [he] at hsit
          obtain ⟨h1, -⟩ := (canSitOn_eq c c).mp hsit
          omega
        · have hrokr : runOK (c :: tr) = true := by
            have := tfc_runOK_fromCard ((st.piles a).faceUp) c hrok
            rw [hcrr] at this
            exact this
          have hlt := tfc_runOK_tail_lt tr c z hrokr hm
          obtain ⟨h1, -⟩ := (canSitOn_eq c z).mp hsit
          omega
      · have hzA : z ∈ (st.piles a).hidden ++ (st.piles a).faceUp :=
          List.mem_append.mpr (Or.inr (mem_below _ (lastOf_mem hz)))
        have hzK : z ∈ (st.piles k).hidden ++ (st.piles k).faceUp :=
          List.mem_append.mpr (Or.inr (lastOf_mem hlzk))
        exact tfc_two_pile_zone_absurd (fun h => hka h.symm) hccz hzA hzK

/-- The run head never lands a located `inr`-base on its own holding
pile: the descent exclusion behind `tfc_tabToTab_wf`'s `hak` (fresh
reading of `Orig2/Classification.lean:381` <- `Orig/Integrity.lean:649`). -/
private theorem tfc_mover_pile_not_target {st : State} {c w : Card} {a : Anchor} {k : Anchor}
    (hwf : st.WF) (hh : st.pileHolding c = some a)
    (hloc : st.pileOfTop w = some k)
    (hsit : canSitOn c w = true) : k ≠ a := by
  intro heq
  subst heq
  obtain ⟨-, hlast⟩ := tfc_pileOfTop_top hloc
  obtain ⟨h1, -⟩ := (canSitOn_eq c w).mp hsit
  have hmem : c ∈ (st.piles k).faceUp := pileHolding_mem hh
  have hzr := tfc_lastOf_mem_fromCard ((st.piles k).faceUp) c hmem w hlast
  obtain ⟨tr, hcrr⟩ := tfc_fromCard_cons_head _ hmem
  rw [hcrr] at hzr
  rcases List.mem_cons.mp hzr with he | hm
  · rw [he] at hsit
    obtain ⟨h1', -⟩ := (canSitOn_eq c c).mp hsit
    omega
  · have hrok : runOK (c :: tr) = true := by
      have := tfc_runOK_fromCard ((st.piles k).faceUp) c (hwf.2.1 k)
      rw [hcrr] at this
      exact this
    have hlt := tfc_runOK_tail_lt tr c w hrok hm
    omega

/-! ### §E4. The certified cell inversion and the honest leg shape -/

/-- The certified `tabToTabR` cell, unpacked (fresh inversion riding
`Orig2/Classification.lean`'s public `tabToTabR_iff_reversibleAtW`
and the registry def `Orig2/Vocab.lean §1.6`). -/
private theorem tfc_tabToTabR_inv {st : State} {c : Card} {b : Base}
    (h : tabToTabR st c b = true) :
    ∃ a, st.pileHolding c = some a ∧ st.canPlace c b = true ∧
      ((below c (st.piles a).faceUp ≠ []) ∨
       (below c (st.piles a).faceUp = [] ∧ (st.piles a).hidden = [] ∧
         c.rank = Rank.king)) := by
  cases hh : st.pileHolding c with
  | none =>
      rw [show tabToTabR st c b = false by simp only [tabToTabR, hh]] at h
      exact Bool.noConfusion h
  | some a =>
      cases hcp : st.canPlace c b with
      | false =>
          rw [show tabToTabR st c b = false by simp only [tabToTabR, hh, hcp]] at h
          exact Bool.noConfusion h
      | true =>
          cases hbl : below c (st.piles a).faceUp with
          | cons z0 pre' =>
              exact ⟨a, rfl, rfl, Or.inl (by rw [hbl]; simp)⟩
          | nil =>
              cases hhid : (st.piles a).hidden with
              | cons h1 t1 =>
                  rw [show tabToTabR st c b = false by
                    simp only [tabToTabR, hh, hcp, hbl, hhid]] at h
                  exact Bool.noConfusion h
              | nil =>
                  have hcell : tabToTabR st c b = decide (c.rank = Rank.king) := by
                    simp only [tabToTabR, hh, hcp, hbl, hhid]
                  rw [hcell] at h
                  exact ⟨a, rfl, rfl, Or.inr ⟨hbl, hhid, of_decide_eq_true h⟩⟩

/-- THE HONEST LEG SHAPE at a WF origin: a reversible slide holds at
`a`, fires on `b`, and is either the whole-segment under-relocation
(company beneath) or the bare-king vacate (NO REVEAL: the hidden deck
is empty).  Fresh packaging of the certified cell for the rows below. -/
private theorem tfc_leg_shape {st : State} {c : Card} {b : Base}
    (hwf : st.WF) (hrev : reversibleAtW st (Move.tabToTab c b)) :
    ∃ a tr s',
      st.pileHolding c = some a ∧ st.canPlace c b = true ∧
      (st.piles a).faceUp = below c (st.piles a).faceUp ++ (c :: tr) ∧
      fromCard c ((st.piles a).faceUp) = c :: tr ∧
      (below c (st.piles a).faceUp ≠ [] ∨
        (below c (st.piles a).faceUp = [] ∧ (st.piles a).hidden = [] ∧
          c.rank = Rank.king)) ∧
      State.step st (Move.tabToTab c b) = some s' := by
  have hcell := (tabToTabR_iff_reversibleAtW hwf c b).mpr hrev
  obtain ⟨a', hh', hcp', hbcell⟩ := tfc_tabToTabR_inv hcell
  obtain ⟨s1, play, hstep, -⟩ := hrev
  have hstepC := hstep
  obtain ⟨a, hhold, hcp, hfr, hs1⟩ := step_tabToTab_inv hstepC
  obtain ⟨tr, hcrr⟩ := tfc_fromCard_cons_head _ (pileHolding_mem hhold)
  have haeq : a' = a := by
    have hx : some a = some a' := hhold.symm.trans hh'
    injection hx with hx'
    exact hx'.symm
  rw [haeq] at hbcell
  refine ⟨a, tr, s1, hhold, hcp, ?_, hcrr, ?_, hstep⟩
  · have h0 := tfc_below_fromCard c ((st.piles a).faceUp)
    rw [hcrr] at h0
    exact h0.symm
  · rcases hbcell with hbne | ⟨hb0, hhid, hkng⟩
    · exact Or.inl hbne
    · exact Or.inr ⟨hb0, hhid, hkng⟩

/-! ### §E5. The search pins and the one-point-edit seat row -/

/-- The search pin: a located pane holding the card, all others
declined (the `firstWhere_find` pack of `Orig/State.lean:78`). -/
private theorem tfc_pileHolding_pin {st : State} {x : Card} {k : Anchor}
    (hmem : x ∈ (st.piles k).faceUp)
    (hno : ∀ j, j ≠ k → x ∉ (st.piles j).faceUp) :
    st.pileHolding x = some k := by
  show firstWhere (fun a => decide (x ∈ (st.piles a).faceUp)) Anchor.all = some k
  exact firstWhere_find (Anchor.mem_all k) (decide_eq_true hmem)
    (fun j _ hjk => decide_false_of_not (hno j hjk))

/-- The found pile is the only candidate: membership elsewhere is
absurd (occurrence uniqueness; `Orig2/Classification.lean:217`'s
`wf_two_piles_ne` pattern). -/
private theorem tfc_holding_pin' {st : State} (hwf : st.WF) {x : Card} {q : Anchor}
    (hh : st.pileHolding x = some q) {j : Anchor} (hmem : x ∈ (st.piles j).faceUp) :
    j = q := by
  by_cases hjq : j = q
  · exact hjq
  · exfalso
    have hccx : st.cardCount x = 1 := hwf.2.2.1 x (Card.mem_universe x)
    have hq : x ∈ (st.piles q).hidden ++ (st.piles q).faceUp :=
      List.mem_append.mpr (Or.inr (pileHolding_mem hh))
    have hj : x ∈ (st.piles j).hidden ++ (st.piles j).faceUp :=
      List.mem_append.mpr (Or.inr hmem)
    exact tfc_two_pile_zone_absurd hjq hccx hj hq

/-- Two memberships in one face-up list double the count (the WF-free
count lane). -/
private theorem tfc_two_mem_faceUp_absurd {st : State} (hwf : st.WF) {x : Card} {a : Anchor}
    {L R : List Card} (hsplit : (st.piles a).faceUp = L ++ R)
    (hl : x ∈ L) (hr : x ∈ R) : False := by
  have h0 : st.cardCount x = 1 := hwf.2.2.1 x (Card.mem_universe x)
  have h1 : 1 ≤ tfc_cnt x L := tfc_mem_le_cnt _ hl
  have h2 : 1 ≤ tfc_cnt x R := tfc_mem_le_cnt _ hr
  have h3 : tfc_cnt x (L ++ R) = tfc_cnt x L + tfc_cnt x R := tfc_cnt_app x L R
  have h4 : tfc_cnt x (st.piles a).faceUp ≤ st.cardCount x :=
    tfc_faceUp_cnt_le_cardCount
  rw [hsplit, h3] at h4
  omega


/-- The holding search declines all (the `firstWhere` pack of `Orig/State.lean:40`). -/
private theorem tfc_pileHolding_none {st : State} {x : Card}
    (hno : ∀ j, x ∉ (st.piles j).faceUp) : st.pileHolding x = none := by
  show firstWhere (fun a => decide (x ∈ (st.piles a).faceUp)) Anchor.all = none
  exact tfc_firstWhere_none Anchor.all (fun j _ => decide_false_of_not (hno j))

/-- Face-up occurrence uniqueness, both lanes explicit (the
`Orig2/Classification.lean:217` `wf_two_piles_ne` pattern at the seam). -/
private theorem tfc_faceUp_uniq_other {st : State} (hwf : st.WF) {x : Card} {q j : Anchor}
    (hmemq : x ∈ (st.piles q).faceUp) (hjq : j ≠ q) : x ∉ (st.piles j).faceUp := by
  intro hmem
  have hccx : st.cardCount x = 1 := hwf.2.2.1 x (Card.mem_universe x)
  exact tfc_two_pile_zone_absurd hjq hccx
    (List.mem_append.mpr (Or.inr hmem))
    (List.mem_append.mpr (Or.inr hmemq))

/-- THE ONE-POINT-EDIT SEAT ROW (the chart's UPDATE claim, re-proved
inline over the seam's step unfold `Orig/Play.lean:129-140` and
`Orig/State.lean:392-473`; GATED as it must be: a reversible slide at
a WF origin never reveals, so exactly the mover's seat changes, to the
base).  This is the row the priced stub `chart_tabToTab` of
`Orig2/Claims.lean` gestures at; see `chart_tabToTab_ungated_false`
at the tail for why the gates are load-bearing. -/
private theorem tfc_seat_point_edit {st s' : State} {c : Card} {b : Base}
    (hwf : st.WF) (hstep : State.step st (Move.tabToTab c b) = some s')
    (hrev : reversibleAtW st (Move.tabToTab c b)) :
    ∀ x, seatOf s' x = if x = c then some b else seatOf st x := by
  obtain ⟨a, tr, s1, hhold, hcp, hface, hcrr, hcell, hstep1⟩ := tfc_leg_shape hwf hrev
  obtain ⟨a0, hhold0, hcp0, hfr, hs1shape⟩ := step_tabToTab_inv hstep
  have ha0 : a0 = a := by
    have hx : some a = some a0 := hhold.symm.trans hhold0
    injection hx with hx'
    exact hx'.symm
  rw [ha0] at hs1shape
  rw [hcrr] at hs1shape
  have hcctx : c ∈ (st.piles a).faceUp := pileHolding_mem hhold
  cases b with
  | inl a' =>
      rw [putRun_eq_inl] at hs1shape
      obtain ⟨hhE, -⟩ := canPlace_inl hcp
      obtain ⟨hhidE, hfF⟩ := (Pile.isEmpty_eq _).mp hhE
      have haa' : a ≠ a' := by
        intro heq
        rw [heq] at hcctx
        rw [hfF] at hcctx
        exact absurd hcctx (by simp)
      have hreadA : ((st.setPile a (Pile.afterRunRemoved (st.piles a) (below c ((st.piles a).faceUp)))).setPile a' ⟨[], c :: tr⟩).piles a
          = Pile.afterRunRemoved (st.piles a) (below c ((st.piles a).faceUp)) := by
        rw [setPile_piles_ne haa', setPile_piles_self]
      have hresFaceF : (s'.piles a).faceUp = (below c ((st.piles a).faceUp)) := by
        rw [hs1shape, hreadA]
        rcases hcell with hbne | ⟨hb0, hhid, -⟩
        · rw [afterRunRemoved_ne hbne]
        · rw [hb0, Pile.afterRunRemoved_bare hhid]
      have hresFaceH : (s'.piles a).hidden = (st.piles a).hidden := by
        rw [hs1shape, hreadA]
        rcases hcell with hbne | ⟨hb0, hhid, -⟩
        · rw [afterRunRemoved_ne hbne]
        · rw [hb0, Pile.afterRunRemoved_bare hhid, hhid]
      have hLface : (s'.piles a').faceUp = c :: tr := by
        rw [hs1shape, setPile_piles_self]
      have hother : ∀ j, j ≠ a → j ≠ a' → (s'.piles j).faceUp = (st.piles j).faceUp := by
        intro j hja hja'
        rw [hs1shape, setPile_piles_ne hja', setPile_piles_ne hja]
      -- (P1) every non-mover keeps its seat
      have hP1 : ∀ x, x ≠ c → seatOf s' x = seatOf st x := by
        intro x hxc
        cases hqx : st.pileHolding x with
        | none =>
            have hxst : ∀ j, x ∉ (st.piles j).faceUp := fun j => tfc_not_mem_faceUp_of_holdNone hqx j
            have hno : ∀ j, x ∉ (s'.piles j).faceUp := by
              intro j
              rcases Decidable.em (j = a) with hja | hja
              · rw [hja, hresFaceF]
                intro hmem
                exact hxst a (mem_below _ hmem)
              · rcases Decidable.em (j = a') with hja' | hja'
                · rw [hja', hLface]
                  intro hmem
                  rcases List.mem_cons.mp hmem with heq | htrm
                  · exact absurd heq hxc
                  · exact hxst a (tfc_mem_fromCard _ (by rw [hcrr]; exact List.mem_cons.2 (Or.inr htrm)))
                · rw [hother j hja hja']
                  exact hxst j
            rw [tfc_seatOf_none (tfc_pileHolding_none hno), tfc_seatOf_none hqx]
        | some q =>
            have hxq : x ∈ (st.piles q).faceUp := pileHolding_mem hqx
            by_cases hxin : x ∈ tr
            · -- the ride: the in-run predecessor is kept
              have hxinA : x ∈ (st.piles a).faceUp := by
                have h1 : x ∈ fromCard c ((st.piles a).faceUp) := by
                  rw [hcrr]
                  exact List.mem_cons.2 (Or.inr hxin)
                exact tfc_mem_fromCard _ h1
              have hqA : q = a := (tfc_holding_pin' hwf hqx hxinA).symm
              rw [hqA] at hqx hxq
              have hxnBl : x ∉ (below c ((st.piles a).faceUp)) := by
                intro hmem
                exact tfc_two_mem_faceUp_absurd hwf hface hmem (List.mem_cons.2 (Or.inr hxin))
              have holdBelow : below x ((st.piles a).faceUp) = (below c ((st.piles a).faceUp)) ++ below x (c :: tr) := by
                have h2 : below x ((st.piles a).faceUp)
                    = below x ((below c ((st.piles a).faceUp)) ++ c :: tr) :=
                  congrArg (below x) hface
                rw [h2]
                exact (tfc_below_fromCard_excl x (below c ((st.piles a).faceUp)) (c :: tr) hxnBl).1
              have hbxCne : below x (c :: tr) ≠ [] := by
                have hbxC' : below x (c :: tr) = c :: below x tr := by
                  rw [below_cons, ite_eq_right (fun hce => hxc hce.symm)]
                rw [hbxC']
                exact fun hcon => absurd hcon (by simp)
              obtain ⟨y, hy⟩ := lastOf_exists hbxCne
              have hnewBelow : below x ((s'.piles a').faceUp) = below x (c :: tr) := by
                rw [hLface]
              have hmemS : x ∈ (s'.piles a').faceUp := by
                rw [hLface]
                exact List.mem_cons.2 (Or.inr hxin)
              have hnoS : ∀ j, j ≠ a' → x ∉ (s'.piles j).faceUp := by
                intro j hja'
                rcases Decidable.em (j = a) with hja | hja
                · rw [hja, hresFaceF]
                  exact hxnBl
                · rw [hother j hja hja']
                  exact tfc_faceUp_uniq_other hwf hxinA hja
              have hnews := tfc_pileHolding_pin hmemS hnoS
              have hL1 : lastOf (below x ((s'.piles a').faceUp)) = some y := by
                rw [hnewBelow, ← hy]
              have hR1 : lastOf (below x ((st.piles a).faceUp)) = some y := by
                rw [holdBelow, tfc_lastOf_append_ne (below c ((st.piles a).faceUp)) hbxCne, ← hy]
              rw [tfc_seatOf_inr_intro hnews hL1, tfc_seatOf_inr_intro hqx hR1]
            · -- a non-mover outside the run
              rcases Decidable.em (q = a) with hqa | hqa
              · rw [hqa] at hqx hxq
                have hxnBl : x ∈ (below c ((st.piles a).faceUp)) := by
                  have hmem : x ∈ (below c ((st.piles a).faceUp)) ++ (c :: tr) := by rw [← hface]; exact hxq
                  rcases List.mem_append.mp hmem with h1 | h2
                  · exact h1
                  · exfalso
                    rcases List.mem_cons.mp h2 with heq | htrm
                    · exact absurd heq hxc
                    · exact absurd htrm hxin
                have hxA : x ∈ (st.piles a).faceUp := mem_below _ hxnBl
                have hmemS : x ∈ (s'.piles a).faceUp := by
                  rw [hresFaceF]
                  exact hxnBl
                have hnoS : ∀ j, j ≠ a → x ∉ (s'.piles j).faceUp := by
                  intro j hja
                  rcases Decidable.em (j = a') with hja' | hja'
                  · rw [hja', hLface]
                    intro hmem
                    rcases List.mem_cons.mp hmem with heq | htrm
                    · exact absurd heq hxc
                    · exact absurd htrm hxin
                  · rw [hother j hja hja']
                    exact tfc_faceUp_uniq_other hwf hxA hja
                have hnews := tfc_pileHolding_pin hmemS hnoS
                rw [tfc_seatOf_pair hnews, tfc_seatOf_pair hqx, hresFaceF]
                have hbb : below x ((st.piles a).faceUp)
                    = below x (below c ((st.piles a).faceUp)) := by
                  have h2 : below x ((st.piles a).faceUp)
                      = below x (below c ((st.piles a).faceUp) ++ c :: tr) :=
                    congrArg (below x) hface
                  rw [h2]
                  exact tfc_below_mem_append_left (below c ((st.piles a).faceUp)) (c :: tr) hxnBl
                rw [hbb]
              · have hqa' : q ≠ a' := by
                  intro heq
                  rw [heq] at hxq
                  rw [hfF] at hxq
                  exact absurd hxq (by simp)
                have hSfaceq : (s'.piles q).faceUp = (st.piles q).faceUp :=
                  hother q hqa hqa'
                have hmemS : x ∈ (s'.piles q).faceUp := by rw [hSfaceq]; exact hxq
                have hnoS : ∀ j, j ≠ q → x ∉ (s'.piles j).faceUp := by
                  intro j hjq
                  rcases Decidable.em (j = a) with hja | hja
                  · rw [hja, hresFaceF]
                    intro hmem
                    exact tfc_faceUp_uniq_other hwf hxq (fun hh => hqa hh.symm) (mem_below _ hmem)
                  · rcases Decidable.em (j = a') with hja' | hja'
                    · rw [hja', hLface]
                      intro hmem
                      rcases List.mem_cons.mp hmem with heq | htrm
                      · exact absurd heq hxc
                      · exact absurd htrm hxin
                    · rw [hother j hja hja']
                      exact tfc_faceUp_uniq_other hwf hxq hjq
                have hnews := tfc_pileHolding_pin hmemS hnoS
                rw [tfc_seatOf_pair hnews, tfc_seatOf_pair hqx, hSfaceq]
      -- (P2) the mover lands at the base
      have hP2 : seatOf s' c = some (Sum.inl a') := by
        have hmemC : c ∈ (s'.piles a').faceUp := by
          rw [hLface]
          exact List.mem_cons.mpr (Or.inl rfl)
        have hnoC : ∀ j, j ≠ a' → c ∉ (s'.piles j).faceUp := by
          intro j hja'
          rcases Decidable.em (j = a) with hja | hja
          · rw [hja, hresFaceF]
            exact tfc_below_not_mem_self c _
          · rw [hother j hja hja']
            exact tfc_faceUp_uniq_other hwf hcctx hja
        exact tfc_seatOf_inl_intro (tfc_pileHolding_pin hmemC hnoC)
          (by rw [hLface, below_cons, ite_eq_left rfl])
      intro x
      by_cases hxc : x = c
      · rw [hxc]
        rw [ite_eq_left rfl]
        exact hP2
      · rw [ite_eq_right hxc]
        exact hP1 x hxc
  | inr w =>
      obtain ⟨k, hlocst, hfit⟩ := canPlace_inr hcp
      have hka : k ≠ a := tfc_mover_pile_not_target hwf hhold hlocst hfit
      have hak : a ≠ k := fun hh => hka hh.symm
      have hccw : st.cardCount w = 1 := hwf.2.2.1 w (Card.mem_universe w)
      have hcnk : c ∉ (st.piles k).faceUp := tfc_faceUp_uniq_other hwf hcctx hka
      have hMk : (st.setPile a (Pile.afterRunRemoved (st.piles a) (below c ((st.piles a).faceUp)))).piles k
          = st.piles k := setPile_piles_ne hka
      have hktop : lastOf ((st.piles k).faceUp) = some w := (tfc_pileOfTop_top hlocst).2
      have hlocM : (st.setPile a (Pile.afterRunRemoved (st.piles a) (below c ((st.piles a).faceUp)))).pileOfTop w = some k := by
        have hmidk : (st.setPile a (Pile.afterRunRemoved (st.piles a) (below c ((st.piles a).faceUp)))).topOf k
            = (st.piles k).top := by
          show ((st.setPile a (Pile.afterRunRemoved (st.piles a) (below c ((st.piles a).faceUp)))).piles k).top
              = (st.piles k).top
          rw [hMk]
        have htpk : (st.piles k).top = some w := hktop
        refine firstWhere_find (Anchor.mem_all k) ?_ ?_
        · rw [hmidk, htpk]
          exact decide_eq_true rfl
        · intro j _ hjk
          by_cases hja : j = a
          · rw [hja]
            have hnot : (st.setPile a (Pile.afterRunRemoved (st.piles a) (below c ((st.piles a).faceUp)))).topOf a
                ≠ some w := by
              intro hcon
              have hcon0 : ((st.setPile a (Pile.afterRunRemoved (st.piles a)
                  (below c ((st.piles a).faceUp)))).piles a).top = some w := hcon
              rw [setPile_piles_self] at hcon0
              have hcon' : lastOf (Pile.afterRunRemoved (st.piles a)
                  (below c ((st.piles a).faceUp))).faceUp = some w := hcon0
              have hznew : w ∈ (Pile.afterRunRemoved (st.piles a) (below c ((st.piles a).faceUp))).faceUp :=
                lastOf_mem hcon'
              have hzone : w ∈ (Pile.afterRunRemoved (st.piles a) (below c ((st.piles a).faceUp))).hidden
                  ++ (Pile.afterRunRemoved (st.piles a) (below c ((st.piles a).faceUp))).faceUp :=
                List.mem_append.mpr (Or.inr hznew)
              have hzold : w ∈ (st.piles a).hidden ++ (st.piles a).faceUp :=
                tfc_mem_afterRunRemoved_below_zone hzone
              have hzk : w ∈ (st.piles k).hidden ++ (st.piles k).faceUp :=
                List.mem_append.mpr (Or.inr (lastOf_mem htpk))
              exact tfc_two_pile_zone_absurd hak hccw hzold hzk
            exact decide_false_of_not hnot
          · have hnot : (st.setPile a (Pile.afterRunRemoved (st.piles a) (below c ((st.piles a).faceUp)))).topOf j
                ≠ some w := by
              intro hcon
              have hcon0 : ((st.setPile a (Pile.afterRunRemoved (st.piles a) (below c ((st.piles a).faceUp)))).piles j).top
                  = some w := hcon
              rw [setPile_piles_ne hja] at hcon0
              have hcon2 : st.topOf j = some w := hcon0
              exact hjk (tfc_top_search_unique hccw hcon2 htpk)
            exact decide_false_of_not hnot
      have hs1s' : s' = (st.setPile a (Pile.afterRunRemoved (st.piles a) (below c ((st.piles a).faceUp)))).setPile k
          { (st.setPile a (Pile.afterRunRemoved (st.piles a) (below c ((st.piles a).faceUp)))).piles k with
            faceUp := ((st.setPile a (Pile.afterRunRemoved (st.piles a) (below c ((st.piles a).faceUp)))).piles k).faceUp
              ++ (c :: tr) } := by
        rw [hs1shape, putRun_inr_eq hlocM]
      have hLKface : (s'.piles k).faceUp = (st.piles k).faceUp ++ (c :: tr) := by
        rw [hs1s', setPile_piles_self, hMk]
      have hother : ∀ j, j ≠ a → j ≠ k → (s'.piles j).faceUp = (st.piles j).faceUp := by
        intro j hja hjk
        rw [hs1s', setPile_piles_ne hjk, setPile_piles_ne hja]
      have hreadA : ((st.setPile a (Pile.afterRunRemoved (st.piles a) (below c ((st.piles a).faceUp)))).setPile k
          { (st.setPile a (Pile.afterRunRemoved (st.piles a) (below c ((st.piles a).faceUp)))).piles k with
            faceUp := ((st.setPile a (Pile.afterRunRemoved (st.piles a) (below c ((st.piles a).faceUp)))).piles k).faceUp
              ++ (c :: tr) }).piles a
          = Pile.afterRunRemoved (st.piles a) (below c ((st.piles a).faceUp)) := by
        rw [setPile_piles_ne hak, setPile_piles_self]
      have hresFaceF : (s'.piles a).faceUp = (below c ((st.piles a).faceUp)) := by
        rw [hs1s', hreadA]
        rcases hcell with hbne | ⟨hb0, hhid, -⟩
        · rw [afterRunRemoved_ne hbne]
        · rw [hb0, Pile.afterRunRemoved_bare hhid]
      have hresFaceH : (s'.piles a).hidden = (st.piles a).hidden := by
        rw [hs1s', hreadA]
        rcases hcell with hbne | ⟨hb0, hhid, -⟩
        · rw [afterRunRemoved_ne hbne]
        · rw [hb0, Pile.afterRunRemoved_bare hhid, hhid]
      have hP1 : ∀ x, x ≠ c → seatOf s' x = seatOf st x := by
        intro x hxc
        cases hqx : st.pileHolding x with
        | none =>
            have hxst : ∀ j, x ∉ (st.piles j).faceUp := fun j => tfc_not_mem_faceUp_of_holdNone hqx j
            have hno : ∀ j, x ∉ (s'.piles j).faceUp := by
              intro j
              rcases Decidable.em (j = a) with hja | hja
              · rw [hja, hresFaceF]
                intro hmem
                exact hxst a (mem_below _ hmem)
              · rcases Decidable.em (j = k) with hjk | hjk
                · rw [hjk, hLKface]
                  intro hmem
                  rcases List.mem_append.mp hmem with h1 | h2
                  · exact hxst k h1
                  · rcases List.mem_cons.mp h2 with heq | htrm
                    · exact absurd heq hxc
                    · exact hxst a (tfc_mem_fromCard _ (by rw [hcrr]; exact List.mem_cons.2 (Or.inr htrm)))
                · rw [hother j hja hjk]
                  exact hxst j
            rw [tfc_seatOf_none (tfc_pileHolding_none hno), tfc_seatOf_none hqx]
        | some q =>
            have hxq : x ∈ (st.piles q).faceUp := pileHolding_mem hqx
            by_cases hxin : x ∈ tr
            · -- the ride: the in-run predecessor is kept, the prefix relabels
              have hxinA : x ∈ (st.piles a).faceUp := by
                have h1 : x ∈ fromCard c ((st.piles a).faceUp) := by
                  rw [hcrr]
                  exact List.mem_cons.2 (Or.inr hxin)
                exact tfc_mem_fromCard _ h1
              have hqA : q = a := (tfc_holding_pin' hwf hqx hxinA).symm
              rw [hqA] at hqx hxq
              have hxnBl : x ∉ (below c ((st.piles a).faceUp)) := by
                intro hmem
                exact tfc_two_mem_faceUp_absurd hwf hface hmem (List.mem_cons.2 (Or.inr hxin))
              have holdBelow : below x ((st.piles a).faceUp) = (below c ((st.piles a).faceUp)) ++ below x (c :: tr) := by
                have h2 : below x ((st.piles a).faceUp)
                    = below x ((below c ((st.piles a).faceUp)) ++ c :: tr) :=
                  congrArg (below x) hface
                rw [h2]
                exact (tfc_below_fromCard_excl x (below c ((st.piles a).faceUp)) (c :: tr) hxnBl).1
              have hbxCne : below x (c :: tr) ≠ [] := by
                have hbxC' : below x (c :: tr) = c :: below x tr := by
                  rw [below_cons, ite_eq_right (fun hce => hxc hce.symm)]
                rw [hbxC']
                exact fun hcon => absurd hcon (by simp)
              obtain ⟨y, hy⟩ := lastOf_exists hbxCne
              have hxnk : x ∉ (st.piles k).faceUp := tfc_faceUp_uniq_other hwf hxinA hka
              have hnewBelow : below x ((s'.piles k).faceUp)
                  = (st.piles k).faceUp ++ below x (c :: tr) := by
                rw [hLKface, (tfc_below_fromCard_excl x (st.piles k).faceUp (c :: tr) hxnk).1]
              have hmemS : x ∈ (s'.piles k).faceUp := by
                rw [hLKface]
                exact List.mem_append.2 (Or.inr (List.mem_cons.2 (Or.inr hxin)))
              have hnoS : ∀ j, j ≠ k → x ∉ (s'.piles j).faceUp := by
                intro j hjk
                rcases Decidable.em (j = a) with hja | hja
                · rw [hja, hresFaceF]
                  exact hxnBl
                · rw [hother j hja hjk]
                  exact tfc_faceUp_uniq_other hwf hxinA hja
              have hnews := tfc_pileHolding_pin hmemS hnoS
              have hL1 : lastOf (below x ((s'.piles k).faceUp)) = some y := by
                rw [hnewBelow, tfc_lastOf_append_ne _ hbxCne, ← hy]
              have hR1 : lastOf (below x ((st.piles a).faceUp)) = some y := by
                rw [holdBelow, tfc_lastOf_append_ne (below c ((st.piles a).faceUp)) hbxCne, ← hy]
              rw [tfc_seatOf_inr_intro hnews hL1, tfc_seatOf_inr_intro hqx hR1]
            · rcases Decidable.em (q = a) with hqa | hqa
              · rw [hqa] at hqx hxq
                have hxnBl : x ∈ (below c ((st.piles a).faceUp)) := by
                  have hmem : x ∈ (below c ((st.piles a).faceUp)) ++ (c :: tr) := by rw [← hface]; exact hxq
                  rcases List.mem_append.mp hmem with h1 | h2
                  · exact h1
                  · exfalso
                    rcases List.mem_cons.mp h2 with heq | htrm
                    · exact absurd heq hxc
                    · exact absurd htrm hxin
                have hxA : x ∈ (st.piles a).faceUp := mem_below _ hxnBl
                have hmemS : x ∈ (s'.piles a).faceUp := by
                  rw [hresFaceF]
                  exact hxnBl
                have hnoS : ∀ j, j ≠ a → x ∉ (s'.piles j).faceUp := by
                  intro j hja
                  rcases Decidable.em (j = k) with hjk | hjk
                  · rw [hjk, hLKface]
                    intro hmem
                    rcases List.mem_append.mp hmem with h1 | h2
                    · exact tfc_faceUp_uniq_other hwf hxA hka h1
                    · rcases List.mem_cons.mp h2 with heq | htrm
                      · exact absurd heq hxc
                      · exact absurd htrm hxin
                  · rw [hother j hja hjk]
                    exact tfc_faceUp_uniq_other hwf hxA hja
                have hnews := tfc_pileHolding_pin hmemS hnoS
                rw [tfc_seatOf_pair hnews, tfc_seatOf_pair hqx, hresFaceF]
                have hbb : below x ((st.piles a).faceUp)
                    = below x (below c ((st.piles a).faceUp)) := by
                  have h2 : below x ((st.piles a).faceUp)
                      = below x (below c ((st.piles a).faceUp) ++ c :: tr) :=
                    congrArg (below x) hface
                  rw [h2]
                  exact tfc_below_mem_append_left (below c ((st.piles a).faceUp)) (c :: tr) hxnBl
                rw [hbb]
              · rcases Decidable.em (q = k) with hqk | hqk
                · rw [hqk] at hqx hxq
                  have hmemS : x ∈ (s'.piles k).faceUp := by
                    rw [hLKface]
                    exact List.mem_append.2 (Or.inl hxq)
                  have hnoS : ∀ j, j ≠ k → x ∉ (s'.piles j).faceUp := by
                    intro j hjq
                    rcases Decidable.em (j = a) with hja | hja
                    · rw [hja, hresFaceF]
                      intro hmem
                      exact tfc_faceUp_uniq_other hwf hxq hak (mem_below _ hmem)
                    · rw [hother j hja hjq]
                      exact tfc_faceUp_uniq_other hwf hxq hjq
                  have hnews := tfc_pileHolding_pin hmemS hnoS
                  rw [tfc_seatOf_pair hnews, tfc_seatOf_pair hqx, hLKface]
                  rw [tfc_below_mem_append_left (st.piles k).faceUp (c :: tr) hxq]
                · have hSfaceq : (s'.piles q).faceUp = (st.piles q).faceUp :=
                    hother q hqa hqk
                  have hmemS : x ∈ (s'.piles q).faceUp := by rw [hSfaceq]; exact hxq
                  have hnoS : ∀ j, j ≠ q → x ∉ (s'.piles j).faceUp := by
                    intro j hjq
                    rcases Decidable.em (j = a) with hja | hja
                    · rw [hja, hresFaceF]
                      intro hmem
                      exact tfc_faceUp_uniq_other hwf hxq (fun hh => hqa hh.symm) (mem_below _ hmem)
                    · rcases Decidable.em (j = k) with hjk | hjk
                      · rw [hjk, hLKface]
                        intro hmem
                        rcases List.mem_append.mp hmem with h1 | h2
                        · exact tfc_faceUp_uniq_other hwf hxq (Ne.symm hqk) h1
                        · rcases List.mem_cons.mp h2 with heq | htrm
                          · exact absurd heq hxc
                          · exact absurd htrm hxin
                      · rw [hother j hja hjk]
                        exact tfc_faceUp_uniq_other hwf hxq hjq
                  have hnews := tfc_pileHolding_pin hmemS hnoS
                  rw [tfc_seatOf_pair hnews, tfc_seatOf_pair hqx, hSfaceq]
      have hP2 : seatOf s' c = some (Sum.inr w) := by
        have hmemC : c ∈ (s'.piles k).faceUp := by
          rw [hLKface]
          exact List.mem_append.2 (Or.inr (List.mem_cons.mpr (Or.inl rfl)))
        have hnoC : ∀ j, j ≠ k → c ∉ (s'.piles j).faceUp := by
          intro j hjk
          rcases Decidable.em (j = a) with hja | hja
          · rw [hja, hresFaceF]
            exact tfc_below_not_mem_self c _
          · rw [hother j hja hjk]
            exact tfc_faceUp_uniq_other hwf hcctx hja
        have hnews := tfc_pileHolding_pin hmemC hnoC
        refine tfc_seatOf_inr_intro hnews ?_
        rw [hLKface, (tfc_below_fromCard_excl c (st.piles k).faceUp (c :: tr) hcnk).1, below_cons, ite_eq_left rfl,
          List.append_nil]
        exact hktop
      intro x
      by_cases hxc : x = c
      · rw [hxc]
        rw [ite_eq_left rfl]
        exact hP2
      · rw [ite_eq_right hxc]
        exact hP1 x hxc
/-! ### §E6. The per-leg seat relation and the chain invariant -/

/-- The seat decomposer (fresh; the two arms of the seat map at a
located holding pile). -/
private theorem tfc_seat_cases {st : State} {c : Card} {a : Anchor}
    (hhold : st.pileHolding c = some a) :
    (∃ z, seatOf st c = some (Sum.inr z)) ∨ seatOf st c = some (Sum.inl a) := by
  rw [tfc_seatOf_pair hhold]
  cases hg : List.getLast? (below c (st.piles a).faceUp) with
  | none => exact Or.inr rfl
  | some z => exact Or.inl ⟨z, rfl⟩

/-- THE PER-LEG SEAT RELATION: one reversible slide changes only the
mover's seat (the one-point edit above), the mover's change is a
twin-hop or a king-vacate, and every other card keeps its seat.  The
mixed seat crossings die on the fit arithmetic: a king has no fitting
parent (`canSitOn` forbids it), and an empty-seat landing requires a
king. -/
private theorem tfc_leg_seat_rel {A M : State} {cm : Card} {b : Base}
    (hwf : A.WF) (hstep : A.step (Move.tabToTab cm b) = some M)
    (hrev : reversibleAtW A (Move.tabToTab cm b)) :
    ∀ c, (seatOf M c = seatOf A c) ∨
      (∃ z, seatOf A c = some (Sum.inr z) ∧ seatOf M c = some (Sum.inr z.twin)) ∨
      (c.rank = Rank.king ∧ ∃ a a', seatOf A c = some (Sum.inl a) ∧
         seatOf M c = some (Sum.inl a')) := by
  have hed := tfc_seat_point_edit hwf hstep hrev
  obtain ⟨a, tr, s1, hhold, hcp, hface, hcrr, hcell, hstep1⟩ := tfc_leg_shape hwf hrev
  intro c
  by_cases hc : c = cm
  · rw [hc]
    have hbM : seatOf M cm = some b := by
      have hbc := hed cm
      rw [ite_eq_left rfl] at hbc
      exact hbc
    rcases tfc_seat_cases hhold with ⟨z, hse⟩ | hse
    · -- seated on z: company beneath, never a king
      obtain ⟨a1, hh1, hbNE, hlz⟩ := tfc_seatOf_of_inr hse
      have ha1 : a1 = a := by
        have hx : some a = some a1 := hhold.symm.trans hh1
        injection hx with hx'
        exact hx'.symm
      rw [ha1] at hlz
      obtain ⟨hsit, htopNone⟩ := tfc_seat_parent hwf hhold hlz
      obtain ⟨hidx, -⟩ := (canSitOn_eq cm z).mp hsit
      have hzlt := Rank.toIdx_lt z.rank
      have hcmnk : cm.rank ≠ Rank.king := by
        intro hk
        have h12 : cm.rank.toIdx = 12 := by rw [hk]; rfl
        omega
      cases b with
      | inl a' =>
          obtain ⟨-, hking⟩ := canPlace_inl hcp
          exact absurd hking hcmnk
      | inr w =>
          obtain ⟨k, hlocw, hfitw⟩ := canPlace_inr hcp
          rcases tfc_fitting_parent hfitw hsit with heq | heq
          · rw [heq] at hlocw
            rw [htopNone] at hlocw
            exact absurd hlocw (by simp)
          · exact Or.inr (Or.inl ⟨z, hse, by rw [hbM, heq]⟩)
    · -- bottomed at a: the bare cell forces a king
      obtain ⟨hh2, hbE⟩ := tfc_seatOf_of_inl hse
      have hkng : cm.rank = Rank.king := by
        rcases hcell with hbne | ⟨hb0, hhid, hk⟩
        · exact absurd hbE hbne
        · exact hk
      cases b with
      | inr w =>
          obtain ⟨k, -, hfitw⟩ := canPlace_inr hcp
          obtain ⟨hidx, -⟩ := (canSitOn_eq cm w).mp hfitw
          have hlt := Rank.toIdx_lt w.rank
          have h12 : cm.rank.toIdx = 12 := by rw [hkng]; rfl
          exfalso
          omega
      | inl a' =>
          exact Or.inr (Or.inr ⟨hkng, a, a', hse, hbM⟩)
  · have hc' := hed c
    rw [ite_eq_right hc] at hc'
    exact Or.inl hc'

/-- The three-way seat relation composes along cargo legs. -/
private theorem tfc_rel_trans {A M u : State}
    (h1 : ∀ c, (seatOf M c = seatOf A c) ∨
      (∃ z, seatOf A c = some (Sum.inr z) ∧ seatOf M c = some (Sum.inr z.twin)) ∨
      (c.rank = Rank.king ∧ ∃ a a', seatOf A c = some (Sum.inl a) ∧
        seatOf M c = some (Sum.inl a')))
    (h2 : ∀ c, (seatOf u c = seatOf M c) ∨
      (∃ z, seatOf M c = some (Sum.inr z) ∧ seatOf u c = some (Sum.inr z.twin)) ∨
      (c.rank = Rank.king ∧ ∃ a a', seatOf M c = some (Sum.inl a) ∧
        seatOf u c = some (Sum.inl a'))) :
    ∀ c, (seatOf u c = seatOf A c) ∨
      (∃ z, seatOf A c = some (Sum.inr z) ∧ seatOf u c = some (Sum.inr z.twin)) ∨
      (c.rank = Rank.king ∧ ∃ a a', seatOf A c = some (Sum.inl a) ∧
        seatOf u c = some (Sum.inl a')) := by
  intro c
  rcases h1 c with e1 | ⟨z1, hA1, hM1⟩ | ⟨k1, a1, a1', hA1, hM1⟩
  · rcases h2 c with e2 | ⟨z2, hM2, hu2⟩ | ⟨k2, b1, b2, hM2, hu2⟩
    · exact Or.inl (e2.trans e1)
    · exact Or.inr (Or.inl ⟨z2, e1.symm.trans hM2, hu2⟩)
    · exact Or.inr (Or.inr ⟨k2, b1, b2, e1.symm.trans hM2, hu2⟩)
  · rcases h2 c with e2 | ⟨z2, hM2, hu2⟩ | ⟨k2, b1, b2, hM2, hu2⟩
    · exact Or.inr (Or.inl ⟨z1, hA1, by rw [e2]; exact hM1⟩)
    · have hz2 : z2 = z1.twin := by
        have he : some (Sum.inr z2) = some (Sum.inr z1.twin) := hM2.symm.trans hM1
        injection he with i1
        cases i1
        rfl
      have hzz : z2.twin = z1 := by rw [hz2]; exact tfc_card_twin_twin z1
      refine Or.inl ?_
      have hu' : seatOf u c = some (Sum.inr z1) := by rw [hu2, hzz]
      rw [hu', hA1]
    · have hcruz : some (Sum.inl b1) = some (Sum.inr z1.twin) := hM2.symm.trans hM1
      exact absurd hcruz (by simp)
  · rcases h2 c with e2 | ⟨z2, hM2, hu2⟩ | ⟨k2, b1, b2, hM2, hu2⟩
    · exact Or.inr (Or.inr ⟨k1, a1, a1', hA1, by rw [e2]; exact hM1⟩)
    · have hcruz : some (Sum.inr z2) = some (Sum.inl a1') := hM2.symm.trans hM1
      exact absurd hcruz (by simp)
    · exact Or.inr (Or.inr ⟨k1, a1, b2, hA1, hu2⟩)

/-- The chain invariant: WF rides the legs (every cargo leg is a
tabToTab witness, preserved by `tfc_tabToTab_wf`), and the three-way
seat relation accumulates from the origin. -/
private theorem tfc_chain_inv : ∀ {w u : State}, Steps CargoLeg w u → w.WF →
    u.WF ∧ ∀ c, (seatOf u c = seatOf w c) ∨
      (∃ z, seatOf w c = some (Sum.inr z) ∧ seatOf u c = some (Sum.inr z.twin)) ∨
      (c.rank = Rank.king ∧ ∃ a a', seatOf w c = some (Sum.inl a) ∧
        seatOf u c = some (Sum.inl a')) := by
  intro w u h
  induction h with
  | refl s =>
      intro hwf
      exact ⟨hwf, fun c => Or.inl rfl⟩
  | @cons s1 s2 s3 hleg t ih =>
      intro hwf
      obtain ⟨c₀, b₀, hstep, hrev⟩ := hleg
      have hwf2 := tfc_tabToTab_wf hwf hstep
      obtain ⟨hwf3, hrel23⟩ := ih hwf2
      exact ⟨hwf3, fun c => tfc_rel_trans (tfc_leg_seat_rel hwf hstep hrev) hrel23 c⟩


/-! ## §H. THE AGENT DRY-RUN ADDENDUM (this copy only)

Snapshot protocol: everything above is a fresh verbatim snapshot of
the owner's `Temp/float_check.lean` kit regions (§A-§E6, frozen
docstrings kept).  Cut record: the owner's §F public rows
(`floater_iff`, `floater_hop_targets`, `floater_seat_change`, with
their battery) and §G (the wild-duplicate refutation around
`wild`/`wild'`) are NOT re-landed here — they are the owner's live
drafting, and this file's own `floater_seat_change` statement differs
from theirs (no name room); every `tfc_*` kit row they ride is kept
above and suffices without them.

The four rows under test here:

* Row 3  `floater_seat_change`  - the one-point chart edit realized by a
  reversible slide, and the class-STEP fiber: twin-family reseating or
  a bare king vacate;
* Row R1 `floater_cargo_lift`   - the reverse layer 1: a live, fiber-valid
  cell with a placement license fires as an actual reversible cargo
  leg realizing the spec;
* Row 2' `floater_seat_to_equiv'` - the reverse layer 2 modulo the priced
  keystone: with the round-trip chart readout as a HYPOTHESIS, a valid
  one-point seat spec derives the bare-cargo class;
* Row 1' `floater_classification` - the structural classification: the
  Floater iff the target-existence shape.

Method note, honestly recorded: every reversibility promise below is
carried by the oracle bridge `tabToTabR_iff_reversibleAtW` (public,
`Orig2/Classification.lean:2627`) — no hand-assembled witness plays,
and `Orig2.Kit.reversible_mirrorW` is not needed for them.  The priced
round-trip hypothesis of `floater_seat_to_equiv'` is hoisted TWICE:
once to identify the spec-mate with the real successor, and once to
pin the mirror's own successor to the origin — so the canonical mirror
never needs pile-level state surgery.  The reversible cells never
reveal, which is what the hidden-deck conservation row rides. -/

/-- **SeatEdit st w c β** — the one-point chart spec: w's chart is
st's with exactly the mover's value replaced by β; fixed readouts
agree. -/
def SeatEdit (st w : State) (c : Card) (β : Base) : Prop :=
  (∀ x, seatOf w x = if x = c then some β else seatOf st x) ∧
    boardFixed st w ∧ foundsFixed st w ∧
    drawPool st = drawPool w ∧ cutOf st = cutOf w

/-! ### §H1. The placement constructors and the conservation row
(fresh; the converses Kit's `canPlace_inl`/`canPlace_inr` do not
carry, plus the reversible-cell hidden conservation) -/

/-- The empty-seat placement, constructed (the converse of Kit's
`canPlace_inl`; the registry placement arm, `Orig/State.lean:348`). -/
private theorem tfa_canPlace_inl {st : State} {c : Card} {a : Anchor}
    (hemp : (st.piles a).isEmpty = true) (hkng : c.rank = Rank.king) :
    st.canPlace c (Sum.inl a) = true := by
  simp only [State.canPlace, Bool.and_eq_true]
  exact ⟨hemp, decide_eq_true hkng⟩

/-- The located card-on-card placement, constructed (the converse of
Kit's `canPlace_inr`; the located arm, `Orig/State.lean:349`). -/
private theorem tfa_canPlace_inr {st : State} {c z : Card} {k : Anchor}
    (hloc : st.pileOfTop z = some k) (hfit : canSitOn c z = true) :
    st.canPlace c (Sum.inr z) = true := by
  simp only [State.canPlace, hloc]
  exact hfit

/-- The twin relabeling keeps the fit (twin-blindness; rides
`canSitOn_twin_right` at `Orig/Basic.lean:119` through `Card.twin`'s
`Suit.twin` shape, `Orig2/Vocab.lean:425`). -/
private theorem tfa_fit_twin {c z : Card} (hfit : canSitOn c z = true) :
    canSitOn c z.twin = true := by
  have hz : z.twin = { z with suit := z.suit.twin } := rfl
  rw [hz, canSitOn_twin_right]
  exact hfit

/-- The run removal keeps the hidden deck at both reversible cells
(the nonempty-prefix arm and the empty-hidden bare arm of the
trichotomy `Orig2/Kit.lean:207`, restricted). -/
private theorem tfa_donor_hidden {st : State} {a : Anchor} {c : Card}
    (hbcell : (below c ((st.piles a).faceUp) ≠ []) ∨
      (below c ((st.piles a).faceUp) = [] ∧ (st.piles a).hidden = [] ∧
        c.rank = Rank.king)) :
    (Pile.afterRunRemoved (st.piles a) (below c ((st.piles a).faceUp))).hidden
      = (st.piles a).hidden := by
  rcases afterRunRemoved_hidden (st.piles a) (below c ((st.piles a).faceUp)) with
    ⟨-, h1⟩ | ⟨hpre, -, h1⟩ | ⟨hpre, hne, -⟩
  · exact h1
  · rcases hbcell with hbne | ⟨hb0, hhid, -⟩
    · exact (hbne hpre).elim
    · exact h1
  · rcases hbcell with hbne | ⟨hb0, hhid, -⟩
    · exact (hbne hpre).elim
    · exact (hne hhid).elim

/-- THE SLIDE'S FIXED-READOUT CONSERVATION: a reversible slide at a
WF origin agrees on every hidden deck and the deal quantum, on every
foundation row, on the pool and on the cut (the reversible cells
never reveal).  Fresh; rides `step_tabToTab_inv` (`Orig2/Kit.lean:727`),
the `putRun` readers (`Orig/Play.lean:455-480`), the donor-hidden row
above, and the registry's chart-support kit (`Orig2/Vocab.lean §9`). -/
private theorem tfa_slide_conserves {st s' : State} {c : Card} {b : Base}
    (hwf : st.WF) (hstep : State.step st (Move.tabToTab c b) = some s')
    (hrev : reversibleAtW st (Move.tabToTab c b)) :
    boardFixed st s' ∧ foundsFixed st s' ∧
      drawPool st = drawPool s' ∧ cutOf st = cutOf s' := by
  obtain ⟨a, hhold, hcp, hbcell⟩ :=
    tfc_tabToTabR_inv ((tabToTabR_iff_reversibleAtW hwf c b).mpr hrev)
  obtain ⟨a0, hhold0, hcp0, hfr, hs1shape⟩ := step_tabToTab_inv hstep
  have ha0 : a0 = a := by
    have hx : some a = some a0 := hhold.symm.trans hhold0
    injection hx with hx'
    exact hx'.symm
  rw [ha0] at hs1shape
  obtain ⟨tr, hcrr⟩ := tfc_fromCard_cons_head _ (pileHolding_mem hhold)
  rw [hcrr] at hs1shape
  cases b with
  | inl a' =>
      rw [putRun_eq_inl] at hs1shape
      refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩
      · intro j
        rw [hs1shape]
        by_cases hja' : j = a'
        · rw [hja', setPile_piles_self]
          have hhid' : (st.piles a').hidden = [] :=
            ((Pile.isEmpty_eq _).mp (canPlace_inl hcp0).1).1
          exact hhid'
        · rw [setPile_piles_ne hja']
          by_cases hja : j = a
          · rw [hja, setPile_piles_self, tfa_donor_hidden hbcell]
          · rw [setPile_piles_ne hja]
      · rw [hs1shape]; rfl
      · intro s0; rw [hs1shape]; rfl
      · rw [hs1shape]; rfl
      · rw [hs1shape]; rfl
  | inr w₀ =>
      cases hptX : (st.setPile a
          (Pile.afterRunRemoved (st.piles a)
            (below c ((st.piles a).faceUp)))).pileOfTop w₀ with
      | none =>
          rw [putRun_inr_none hptX] at hs1shape
          refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩
          · intro j
            rw [hs1shape]
            by_cases hja : j = a
            · rw [hja, setPile_piles_self, tfa_donor_hidden hbcell]
            · rw [setPile_piles_ne hja]
          · rw [hs1shape]; rfl
          · intro s0; rw [hs1shape]; rfl
          · rw [hs1shape]; rfl
          · rw [hs1shape]; rfl
      | some k =>
          rw [putRun_inr_eq hptX] at hs1shape
          refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩
          · intro j
            rw [hs1shape]
            by_cases hjk : j = k
            · rw [hjk, setPile_piles_self]
              show (st.piles k).hidden = ((st.setPile a (Pile.afterRunRemoved (st.piles a)
                  (below c ((st.piles a).faceUp)))).piles k).hidden
              by_cases hka : k = a
              · rw [hka, setPile_piles_self, tfa_donor_hidden hbcell]
              · rw [setPile_piles_ne hka]
            · rw [setPile_piles_ne hjk]
              by_cases hja : j = a
              · rw [hja, setPile_piles_self, tfa_donor_hidden hbcell]
              · rw [setPile_piles_ne hja]
          · rw [hs1shape]; rfl
          · intro s0; rw [hs1shape]; rfl
          · rw [hs1shape]; rfl
          · rw [hs1shape]; rfl

/-! ### §H2. The four rows under test (the only public artifact of
the addendum) -/

/-- **floater_seat_change** — Row 3, the class-STEP fiber: a
reversible slide realizes the one-point chart edit at the mover (the
point-edit row plus the conservation row above), and the changed pair
is twin-family — the mover reseated at its parent's twin (two fitting
parents are equal-or-twin at `tfc_fitting_parent`, and the parent
itself tops no pile at `tfc_seat_parent`, so the strict parent is
excluded) — or the mover is a bare king vacating to an empty seat. -/
theorem floater_seat_change_spec {st s' : State} {c : Card} {b : Base}
    (hwf : st.WF) (hstep : State.step st (Move.tabToTab c b) = some s')
    (hrev : reversibleAtW st (Move.tabToTab c b)) :
    SeatEdit st s' c b ∧
    ((∃ z z', seatOf st c = some (Sum.inr z) ∧ b = Sum.inr z' ∧
        (z' = z ∨ z' = z.twin)) ∨
     (∃ a a', seatOf st c = some (Sum.inl a) ∧ b = Sum.inl a' ∧
        c.rank = Rank.king ∧ (st.piles a).hidden = [])) := by
  have hed := tfc_seat_point_edit hwf hstep hrev
  obtain ⟨hbf, hff, hdp, hco⟩ := tfa_slide_conserves hwf hstep hrev
  refine ⟨⟨hed, hbf, hff, hdp, hco⟩, ?_⟩
  obtain ⟨a, hhold, hcp, hbcell⟩ :=
    tfc_tabToTabR_inv ((tabToTabR_iff_reversibleAtW hwf c b).mpr hrev)
  rcases tfc_seat_cases hhold with ⟨z, hse⟩ | hse
  · obtain ⟨a1, hh1, hbNE, hlz⟩ := tfc_seatOf_of_inr hse
    obtain ⟨hsit, htopNone⟩ := tfc_seat_parent hwf hh1 hlz
    have hcnk : c.rank ≠ Rank.king := by
      obtain ⟨hidx, -⟩ := (canSitOn_eq c z).mp hsit
      have hzlt := Rank.toIdx_lt z.rank
      intro hk
      have h12 : c.rank.toIdx = 12 := by rw [hk]; rfl
      omega
    cases b with
    | inl a' =>
        obtain ⟨-, hking⟩ := canPlace_inl hcp
        exact (hcnk hking).elim
    | inr w =>
        obtain ⟨k, hlocw, hfitw⟩ := canPlace_inr hcp
        rcases tfc_fitting_parent hfitw hsit with heq | heq
        · exfalso
          rw [heq] at hlocw
          rw [htopNone] at hlocw
          nomatch hlocw
        · exact Or.inl ⟨z, w, hse, by rw [heq], by rw [heq]; exact Or.inr rfl⟩
  · obtain ⟨-, hbE⟩ := tfc_seatOf_of_inl hse
    have hkng : c.rank = Rank.king := by
      rcases hbcell with hbne | ⟨hb0, hhid, hk⟩
      · exact (hbne hbE).elim
      · exact hk
    cases b with
    | inr w =>
        exfalso
        obtain ⟨k, -, hfitw⟩ := canPlace_inr hcp
        obtain ⟨hidx, -⟩ := (canSitOn_eq c w).mp hfitw
        have hlt := Rank.toIdx_lt w.rank
        have h12 : c.rank.toIdx = 12 := by rw [hkng]; rfl
        omega
    | inl a' =>
        rcases hbcell with hbne | ⟨hb0, hhid, -⟩
        · exact (hbne hbE).elim
        · exact Or.inr ⟨a, a', hse, rfl, hkng, hhid⟩

/-- **floater_cargo_lift** — the reverse layer 1: a live, fiber-valid
cell plus a placement license FIRES as an actual reversible cargo leg
whose successor realizes the chart spec (the oracle bridge carries
the reversibility; the point-edit row and the conservation row carry
the SeatEdit). -/
theorem floater_cargo_lift {st : State} {c : Card} {β : Base} (hwf : st.WF)
    (hmove : st.canPlace c β = true)
    (hcell : (∃ z, seatOf st c = some (Sum.inr z)) ∨
      ∃ a, seatOf st c = some (Sum.inl a) ∧ c.rank = Rank.king ∧
        (st.piles a).hidden = []) :
    ∃ w, st.step (Move.tabToTab c β) = some w ∧
      reversibleAtW st (Move.tabToTab c β) ∧ SeatEdit st w c β := by
  have hR : tabToTabR st c β = true := by
    rcases hcell with ⟨z, hse⟩ | ⟨a, hse, hkng, hhid⟩
    · obtain ⟨a1, hh1, hbNE, -⟩ := tfc_seatOf_of_inr hse
      show tabToTabR st c β = true
      simp only [tabToTabR, hh1, hmove]
      cases hb : below c ((st.piles a1).faceUp) with
      | cons y ys => rfl
      | nil => exact (hbNE hb).elim
    · obtain ⟨hh2, hbE⟩ := tfc_seatOf_of_inl hse
      show tabToTabR st c β = true
      simp only [tabToTabR, hh2, hmove, hbE, hhid]
      rw [hkng]
      rfl
  have hrev : reversibleAtW st (Move.tabToTab c β) :=
    (tabToTabR_iff_reversibleAtW hwf c β).mp hR
  obtain ⟨w, play, hstep, hrun⟩ := hrev
  obtain ⟨hbf, hff, hdp, hco⟩ :=
    tfa_slide_conserves hwf hstep ⟨w, play, hstep, hrun⟩
  exact ⟨w, hstep, ⟨w, play, hstep, hrun⟩,
    ⟨tfc_seat_point_edit hwf hstep ⟨w, play, hstep, hrun⟩, hbf, hff, hdp, hco⟩⟩

/-! ### §H3. Row 1' — the classification -/

/-- **FloaterSpec st c** — the structural read of the floater: the
company cell (c seated on a parent whose twin tops some pile — the
twin-fiber target exists) or the bare-king cell on an empty-hidden
pile with a second empty pile to vacate to. -/
def FloaterSpec (st : State) (c : Card) : Prop :=
  (∃ z a, seatOf st c = some (Sum.inr z) ∧ st.pileHolding c = some a ∧
      ((∃ k, st.pileOfTop z.twin = some k) ∨
        (c.rank = Rank.king ∧ ∃ a', (st.piles a').isEmpty = true))) ∨
  (∃ a, seatOf st c = some (Sum.inl a) ∧ c.rank = Rank.king ∧
      (st.piles a).hidden = [] ∧ ∃ a', (st.piles a').isEmpty = true)

/-- **floater_classification** — Row 1': the behavioral Floater (some
reversible slide exists) iff the target-existence shape.  Forward:
the oracle cell unpacked by `tfc_tabToTabR_inv` places the mover, and
the fitting-parent arithmetic names the target (the twin pile or the
empty seat).  Backward: the named target licenses the placement
(constructed), the cell licenses the oracle, and the bridge
re-exports the witness. -/
theorem floater_classification (st : State) (hwf : st.WF) (c : Card) :
    Floater st c ↔ FloaterSpec st c := by
  constructor
  · intro hF
    obtain ⟨b₀, hrev⟩ := hF
    obtain ⟨a, hhold, hcp, hbcell⟩ :=
      tfc_tabToTabR_inv ((tabToTabR_iff_reversibleAtW hwf c b₀).mpr hrev)
    rcases hbcell with hbne | ⟨hb0, hhid, hkng⟩
    · obtain ⟨z, hlz⟩ := lastOf_exists hbne
      have hse : seatOf st c = some (Sum.inr z) := tfc_seatOf_inr_intro hhold hlz
      obtain ⟨hsit, htopNone⟩ := tfc_seat_parent hwf hhold hlz
      have hcnk : c.rank ≠ Rank.king := by
        obtain ⟨hidx, -⟩ := (canSitOn_eq c z).mp hsit
        have hzlt := Rank.toIdx_lt z.rank
        intro hk
        have h12 : c.rank.toIdx = 12 := by rw [hk]; rfl
        omega
      cases b₀ with
      | inl a' =>
          obtain ⟨-, hking⟩ := canPlace_inl hcp
          exact (hcnk hking).elim
      | inr w₀ =>
          obtain ⟨k, hlocw, hfitw⟩ := canPlace_inr hcp
          rcases tfc_fitting_parent hfitw hsit with heq | heq
          · exfalso
            rw [heq] at hlocw
            rw [htopNone] at hlocw
            nomatch hlocw
          · refine Or.inl ⟨z, a, hse, hhold, Or.inl ⟨k, ?_⟩⟩
            rw [← heq]
            exact hlocw
    · have hse : seatOf st c = some (Sum.inl a) := tfc_seatOf_inl_intro hhold hb0
      cases b₀ with
      | inr w₀ =>
          exfalso
          obtain ⟨k, -, hfitw⟩ := canPlace_inr hcp
          obtain ⟨hidx, -⟩ := (canSitOn_eq c w₀).mp hfitw
          have hlt := Rank.toIdx_lt w₀.rank
          have h12 : c.rank.toIdx = 12 := by rw [hkng]; rfl
          omega
      | inl a' =>
          obtain ⟨hE, -⟩ := canPlace_inl hcp
          exact Or.inr ⟨a, hse, hkng, hhid, a', hE⟩
  · intro hspec
    rcases hspec with ⟨z, a, hse, hhold, harm⟩ | ⟨a, hse, hkng, hhid, a', hempty⟩
    · rcases harm with ⟨k, hlocT⟩ | ⟨hkng2, -⟩
      · obtain ⟨a1, hh1, hbNE, hlz⟩ := tfc_seatOf_of_inr hse
        obtain ⟨hsit, -⟩ := tfc_seat_parent hwf hh1 hlz
        have hfitT : canSitOn c z.twin = true := tfa_fit_twin hsit
        have hcp : st.canPlace c (Sum.inr z.twin) = true :=
          tfa_canPlace_inr hlocT hfitT
        refine ⟨Sum.inr z.twin, (tabToTabR_iff_reversibleAtW hwf c _).mp ?_⟩
        show tabToTabR st c (Sum.inr z.twin) = true
        simp only [tabToTabR, hh1, hcp]
        cases hb : below c ((st.piles a1).faceUp) with
        | cons y ys => rfl
        | nil => exact (hbNE hb).elim
      · exfalso
        obtain ⟨a1, hh1, hbNE, hlz⟩ := tfc_seatOf_of_inr hse
        obtain ⟨hsit, -⟩ := tfc_seat_parent hwf hh1 hlz
        obtain ⟨hidx, -⟩ := (canSitOn_eq c z).mp hsit
        have hzlt := Rank.toIdx_lt z.rank
        have h12 : c.rank.toIdx = 12 := by rw [hkng2]; rfl
        omega
    · obtain ⟨hh2, hbE⟩ := tfc_seatOf_of_inl hse
      have hcp : st.canPlace c (Sum.inl a') = true :=
        tfa_canPlace_inl hempty hkng
      refine ⟨Sum.inl a', (tabToTabR_iff_reversibleAtW hwf c _).mp ?_⟩
      show tabToTabR st c (Sum.inl a') = true
      simp only [tabToTabR, hh2, hcp, hbE, hhid]
      rw [hkng]
      rfl

/-! ### §H4. Row 2' — the reverse layer 2, modulo the priced keystone -/

/-- **floater_seat_to_equiv'** — the reverse layer 2 modulo the priced
round trip (the registry prices it as `chart_round_trip`; here it is
a HYPOTHESIS, not a sorry): a valid one-point seat spec at a live,
fiber-valid cell derives the bare-cargo class.  Strategy: the lift
(the reverse layer 1) produces the real successor; the two chart-mates
coincide by the hypothesis; the canonical mirror at the successor
(the old seat as the base) certifies by the ORACLE at the successor,
and the chartAgree-ladder plus the hypothesis pin ITS successor to the
origin — the two legs then assemble the class by hand. -/
theorem floater_seat_to_equiv' {st w : State} {c : Card} {β : Base}
    (hwf : st.WF)
    (hroundtrip : ∀ A B, chartAgree A B → A = B)
    (hspec : SeatEdit st w c β)
    (hmove : st.canPlace c β = true)
    (hcell : (∃ z, seatOf st c = some (Sum.inr z)) ∨
      ∃ a, seatOf st c = some (Sum.inl a) ∧ c.rank = Rank.king ∧
        (st.piles a).hidden = []) :
    BareCargoEquiv st w := by
  obtain ⟨s1, hstepL, hrevL, ⟨hedL, hbfL, hffL, hdpL, hcoL⟩⟩ :=
    floater_cargo_lift hwf hmove hcell
  obtain ⟨hseatW, hbfW, hffW, hdpW, hcoW⟩ := hspec
  have hchart : chartAgree w s1 := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro x
      rw [hseatW x, hedL x]
    · obtain ⟨h1, h2⟩ := hbfW
      obtain ⟨h3, h4⟩ := hbfL
      exact ⟨fun j => (h1 j).symm.trans (h3 j), h2.symm.trans h4⟩
    · intro s0
      exact (hffW s0).symm.trans (hffL s0)
    · exact hdpW.symm.trans hdpL
    · exact hcoW.symm.trans hcoL
  have hws : w = s1 := hroundtrip w s1 hchart
  rw [← hws] at hstepL hedL hbfL hffL hdpL hcoL
  have WWF : w.WF := tfc_tabToTab_wf hwf hstepL
  obtain ⟨a0, hhold0, hcp0, hfr, hs1shape⟩ := step_tabToTab_inv hstepL
  obtain ⟨tr, hcrr⟩ := tfc_fromCard_cons_head _ (pileHolding_mem hhold0)
  rw [hcrr] at hs1shape
  have hcctx : c ∈ (st.piles a0).faceUp := pileHolding_mem hhold0
  rcases hcell with ⟨z, hse⟩ | ⟨aC, hseC, hkngC, hhidC⟩
  · obtain ⟨a1, hh1, hbNE, hlz⟩ := tfc_seatOf_of_inr hse
    have ha1 : a1 = a0 := Option.some.inj (hh1.symm.trans hhold0)
    rw [ha1] at hh1 hbNE hlz
    obtain ⟨hsit, htopNone⟩ := tfc_seat_parent hwf hh1 hlz
    have hcnk : c.rank ≠ Rank.king := by
      obtain ⟨hidx, -⟩ := (canSitOn_eq c z).mp hsit
      have hzlt := Rank.toIdx_lt z.rank
      intro hk
      have h12 : c.rank.toIdx = 12 := by rw [hk]; rfl
      omega
    cases β with
    | inl a' =>
        exfalso
        obtain ⟨-, hking⟩ := canPlace_inl hcp0
        exact (hcnk hking).elim
    | inr w₀ =>
        obtain ⟨k, hlocw, hfitw⟩ := canPlace_inr hcp0
        have hka : k ≠ a0 := tfc_mover_pile_not_target hwf hhold0 hlocw hfitw
        have hak0 : a0 ≠ k := fun hh => hka hh.symm
        have hccw : st.cardCount w₀ = 1 := hwf.2.2.1 w₀ (Card.mem_universe w₀)
        have hktopk : lastOf ((st.piles k).faceUp) = some w₀ :=
          (tfc_pileOfTop_top hlocw).2
        have hMk : (st.setPile a0 (Pile.afterRunRemoved (st.piles a0)
            (below c ((st.piles a0).faceUp)))).piles k = st.piles k :=
          setPile_piles_ne hka
        have hlocM : (st.setPile a0 (Pile.afterRunRemoved (st.piles a0)
            (below c ((st.piles a0).faceUp)))).pileOfTop w₀ = some k := by
          have hmidk : (st.setPile a0 (Pile.afterRunRemoved (st.piles a0)
              (below c ((st.piles a0).faceUp)))).topOf k = some w₀ := by
            show lastOf ((st.setPile a0 (Pile.afterRunRemoved (st.piles a0)
              (below c ((st.piles a0).faceUp)))).piles k).faceUp = some w₀
            rw [hMk]
            exact hktopk
          refine firstWhere_find (Anchor.mem_all k) (decide_eq_true hmidk) ?_
          intro j _ hjk
          by_cases hja : j = a0
          · rw [hja]
            refine decide_false_of_not ?_
            intro hcon
            have hset : (st.setPile a0 (Pile.afterRunRemoved (st.piles a0)
                (below c ((st.piles a0).faceUp)))).piles a0
                = Pile.afterRunRemoved (st.piles a0)
                    (below c ((st.piles a0).faceUp)) :=
              setPile_piles_self
            have hcon0 : lastOf (Pile.afterRunRemoved (st.piles a0)
                (below c ((st.piles a0).faceUp))).faceUp = some w₀ := by
              have hp : ((st.setPile a0 (Pile.afterRunRemoved (st.piles a0)
                  (below c ((st.piles a0).faceUp)))).piles a0).top = some w₀ := hcon
              rw [hset] at hp
              exact hp
            have hznew : w₀ ∈ (Pile.afterRunRemoved (st.piles a0)
                (below c ((st.piles a0).faceUp))).faceUp := lastOf_mem hcon0
            have hzone : w₀ ∈ (Pile.afterRunRemoved (st.piles a0)
                (below c ((st.piles a0).faceUp))).hidden
                ++ (Pile.afterRunRemoved (st.piles a0)
                  (below c ((st.piles a0).faceUp))).faceUp :=
              List.mem_append.mpr (Or.inr hznew)
            have hzold : w₀ ∈ (st.piles a0).hidden ++ (st.piles a0).faceUp :=
              tfc_mem_afterRunRemoved_below_zone hzone
            have hzk : w₀ ∈ (st.piles k).hidden ++ (st.piles k).faceUp :=
              List.mem_append.mpr (Or.inr (lastOf_mem hktopk))
            exact tfc_two_pile_zone_absurd hak0 hccw hzold hzk
          · refine decide_false_of_not ?_
            intro hcon
            have hcon2 : st.topOf j = some w₀ := by
              have hp : ((st.setPile a0 (Pile.afterRunRemoved (st.piles a0)
                  (below c ((st.piles a0).faceUp)))).piles j).top = some w₀ := hcon
              rw [setPile_piles_ne hja] at hp
              exact hp
            exact hjk (tfc_top_search_unique hccw hcon2 hktopk)
        rw [putRun_inr_eq hlocM] at hs1shape
        have hface : (st.piles a0).faceUp
            = below c ((st.piles a0).faceUp) ++ (c :: tr) := by
          have h0 := tfc_below_fromCard c ((st.piles a0).faceUp)
          rw [hcrr] at h0
          exact h0.symm
        have hAface : (w.piles a0).faceUp
            = below c ((st.piles a0).faceUp) := by
          rw [hs1shape, setPile_piles_ne hak0, setPile_piles_self,
            afterRunRemoved_ne hbNE]
        have hKface : (w.piles k).faceUp = (st.piles k).faceUp ++ (c :: tr) := by
          rw [hs1shape, setPile_piles_self, hMk]
        have hOther : ∀ j, j ≠ a0 → j ≠ k →
            (w.piles j).faceUp = (st.piles j).faceUp := by
          intro j hja0 hjk
          rw [hs1shape, setPile_piles_ne hjk, setPile_piles_ne hja0]
        have hwseat : seatOf w c = some (Sum.inr w₀) := by
          have hbc := hedL c
          rwa [ite_eq_left rfl] at hbc
        have hwHold : w.pileHolding c = some k := by
          cases hq : w.pileHolding c with
          | none =>
              exfalso
              have hnone := tfc_seatOf_none hq
              rw [hwseat] at hnone
              nomatch hnone
          | some q =>
              have hmemk : c ∈ (w.piles k).faceUp := by
                rw [hKface]
                exact List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))
              rw [tfc_holding_pin' WWF hq hmemk]
        have hlocWz : w.pileOfTop z = some a0 := by
          show firstWhere (fun a => decide (w.topOf a = some z)) Anchor.all
            = some a0
          have hmidk : w.topOf a0 = some z := by
            show lastOf ((w.piles a0).faceUp) = some z
            rw [hAface]
            exact hlz
          refine firstWhere_find (Anchor.mem_all a0) (decide_eq_true hmidk) ?_
          intro j _ hja0
          by_cases hjk : j = k
          · rw [hjk]
            refine decide_false_of_not ?_
            intro hcon
            have hcon0 : lastOf ((st.piles k).faceUp ++ (c :: tr)) = some z := by
              have hp : lastOf ((w.piles k).faceUp) = some z := hcon
              rw [hKface] at hp
              exact hp
            have hzne : (c :: tr : List Card) ≠ [] := by simp
            rw [tfc_lastOf_append_ne _ hzne] at hcon0
            have hlast : z ∈ (c :: tr) := lastOf_mem hcon0
            exact tfc_two_mem_faceUp_absurd hwf hface (lastOf_mem hlz) hlast
          · refine decide_false_of_not ?_
            intro hjj
            have hp0 : lastOf ((w.piles j).faceUp) = some z := hjj
            rw [hOther j hja0 hjk] at hp0
            have h1 := tfc_firstWhere_mem_true
              (p := fun a => decide (st.topOf a = some z)) Anchor.all j
              (Anchor.mem_all j)
              (decide_eq_true (show st.topOf j = some z from hp0))
            rw [show st.pileOfTop z
                  = firstWhere (fun a => decide (st.topOf a = some z)) Anchor.all
                from rfl] at htopNone
            rw [htopNone] at h1
            exact h1 rfl
        have hcpWz : w.canPlace c (Sum.inr z) = true :=
          tfa_canPlace_inr hlocWz hsit
        have hcnk' : c ∉ (st.piles k).faceUp := tfc_faceUp_uniq_other hwf hcctx hka
        have hbelowEq : below c ((w.piles k).faceUp)
            = (st.piles k).faceUp := by
          have h1 : below c ((w.piles k).faceUp)
              = below c ((st.piles k).faceUp ++ (c :: tr)) := by
            rw [← hKface]
          rw [h1, (tfc_below_fromCard_excl c (st.piles k).faceUp (c :: tr) hcnk').1,
            below_cons, ite_eq_left rfl, List.append_nil]
        have hbelowWne : below c ((w.piles k).faceUp) ≠ [] := by
          rw [hbelowEq]
          exact (tfc_pileOfTop_top hlocw).1
        have hRw : tabToTabR w c (Sum.inr z) = true := by
          show tabToTabR w c (Sum.inr z) = true
          simp only [tabToTabR, hwHold, hcpWz]
          cases hb : below c ((w.piles k).faceUp) with
          | cons y ys => rfl
          | nil => exact (hbelowWne hb).elim
        have hrevW := (tabToTabR_iff_reversibleAtW WWF c (Sum.inr z)).mp hRw
        obtain ⟨u, playU, hstepU, hrunU⟩ := hrevW
        have hedU := tfc_seat_point_edit WWF hstepU ⟨u, playU, hstepU, hrunU⟩
        obtain ⟨hbfWU, hffWU, hdpWU, hcoWU⟩ :=
          tfa_slide_conserves WWF hstepU ⟨u, playU, hstepU, hrunU⟩
        have hchartU : chartAgree u st := by
          refine ⟨?_, ?_, ?_, ?_, ?_⟩
          · intro x
            by_cases hxc : x = c
            · rw [hxc]
              have hxU := hedU c
              rw [hxU, ite_eq_left rfl]
              exact hse.symm
            · have hxU := hedU x
              have hxW := hedL x
              rw [hxU, ite_eq_right hxc, hxW, ite_eq_right hxc]
          · obtain ⟨h1, h2⟩ := hbfL
            obtain ⟨h3, h4⟩ := hbfWU
            exact ⟨fun j => (h3 j).symm.trans (h1 j).symm, h4.symm.trans h2.symm⟩
          · intro s0
            exact (hffWU s0).symm.trans (hffL s0).symm
          · exact hdpWU.symm.trans hdpL.symm
          · exact hcoWU.symm.trans hcoL.symm
        have hu : u = st := hroundtrip u st hchartU
        rw [hu] at hstepU hrunU
        exact ⟨Steps.cons ⟨c, Sum.inr w₀, hstepL, hrevL⟩ (Steps.refl w),
          Steps.cons ⟨c, Sum.inr z, hstepU, ⟨st, playU, hstepU, hrunU⟩⟩ (Steps.refl st)⟩
  · obtain ⟨hh2C, hbE⟩ := tfc_seatOf_of_inl hseC
    have haC : aC = a0 := Option.some.inj (hh2C.symm.trans hhold0)
    rw [haC] at hseC hbE hhidC
    cases β with
    | inr w₀ =>
        exfalso
        obtain ⟨k, -, hfitw⟩ := canPlace_inr hcp0
        obtain ⟨hidx, -⟩ := (canSitOn_eq c w₀).mp hfitw
        have hlt := Rank.toIdx_lt w₀.rank
        have h12 : c.rank.toIdx = 12 := by rw [hkngC]; rfl
        omega
    | inl a' =>
        have hA0a' : a0 ≠ a' := by
          intro heq
          rw [heq] at hhold0
          have hmem : c ∈ (st.piles a').faceUp := pileHolding_mem hhold0
          have hemp : (st.piles a').isEmpty = true := (canPlace_inl hcp0).1
          rw [Pile.isEmpty_eq_false_of_mem hmem] at hemp
          exact Bool.noConfusion hemp
        rw [putRun_eq_inl] at hs1shape
        have hAempty : (w.piles a0) = ⟨[], ([] : List Card)⟩ := by
          rw [hs1shape, setPile_piles_ne hA0a', setPile_piles_self, hbE,
            Pile.afterRunRemoved_bare hhidC]
        have hWface : (w.piles a').faceUp = c :: tr := by
          rw [hs1shape, setPile_piles_self]
        have hwseat : seatOf w c = some (Sum.inl a') := by
          have hbc := hedL c
          rwa [ite_eq_left rfl] at hbc
        have hwHold : w.pileHolding c = some a' := by
          cases hq : w.pileHolding c with
          | none =>
              exfalso
              have hnone := tfc_seatOf_none hq
              rw [hwseat] at hnone
              nomatch hnone
          | some q =>
              have hmemk : c ∈ (w.piles a').faceUp := by
                rw [hWface]
                exact List.mem_cons_self
              rw [tfc_holding_pin' WWF hq hmemk]
        have hipsA0 : (w.piles a0).isEmpty = true := by
          rw [hAempty]
          rfl
        have hcpW : w.canPlace c (Sum.inl a0) = true :=
          tfa_canPlace_inl hipsA0 hkngC
        have hbelowW : below c ((w.piles a').faceUp) = [] := by
          rw [hWface, below_cons, ite_eq_left rfl]
        have hhiddenW : (w.piles a').hidden = [] := by
          rw [hs1shape, setPile_piles_self]
        have hRw : tabToTabR w c (Sum.inl a0) = true := by
          show tabToTabR w c (Sum.inl a0) = true
          simp only [tabToTabR, hwHold, hcpW, hbelowW, hhiddenW]
          rw [hkngC]
          rfl
        have hrevW := (tabToTabR_iff_reversibleAtW WWF c (Sum.inl a0)).mp hRw
        obtain ⟨u, playU, hstepU, hrunU⟩ := hrevW
        have hedU := tfc_seat_point_edit WWF hstepU ⟨u, playU, hstepU, hrunU⟩
        obtain ⟨hbfWU, hffWU, hdpWU, hcoWU⟩ :=
          tfa_slide_conserves WWF hstepU ⟨u, playU, hstepU, hrunU⟩
        have hchartU : chartAgree u st := by
          refine ⟨?_, ?_, ?_, ?_, ?_⟩
          · intro x
            by_cases hxc : x = c
            · rw [hxc]
              have hxU := hedU c
              rw [hxU, ite_eq_left rfl]
              exact hseC.symm
            · have hxU := hedU x
              have hxW := hedL x
              rw [hxU, ite_eq_right hxc, hxW, ite_eq_right hxc]
          · obtain ⟨h1, h2⟩ := hbfL
            obtain ⟨h3, h4⟩ := hbfWU
            exact ⟨fun j => (h3 j).symm.trans (h1 j).symm, h4.symm.trans h2.symm⟩
          · intro s0
            exact (hffWU s0).symm.trans (hffL s0).symm
          · exact hdpWU.symm.trans hdpL.symm
          · exact hcoWU.symm.trans hcoL.symm
        have hu : u = st := hroundtrip u st hchartU
        rw [hu] at hstepU hrunU
        exact ⟨Steps.cons ⟨c, Sum.inl a', hstepL, hrevL⟩ (Steps.refl w),
          Steps.cons ⟨c, Sum.inl a0, hstepU, ⟨st, playU, hstepU, hrunU⟩⟩ (Steps.refl st)⟩

/-! ## The battery (the four new heads) -/

#print axioms floater_seat_change_spec
#print axioms floater_cargo_lift
#print axioms floater_seat_to_equiv'
#print axioms floater_classification
