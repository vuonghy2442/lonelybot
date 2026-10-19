import Orig2.TwinSplice
import Orig2.Integrity
import Orig2.StepWF

/-!
# Temp/TwinSpliceWF — the run splice preserves `WF`

`State.spliceTwinRuns` swaps the two face-up runs above a twin pair
between their piles.  This file proves the splice preserves `State.WF`
when both twins are seated on parents (`seatOf` answers `.inr`):

* `found`, `hidden`, `stock`, `waste`, and `drawStep` are untouched, so
  the foundation-prefix and draw-step clauses transport directly;
* the card census is preserved because the two runs are concatenated
  in opposite piles (`cardCount_splice`);
* the only edited face-up runs are `below x A ++ fromCard x.twin B`
  and `below x.twin B ++ fromCard x A`; the new junctions fit by the
  twin-blindness of `canSitOn` and the parents read off the `.inr`
  seats (`runOK_splice_piles`).

Zero `sorry`, zero `Classical.choice`.
-/

/-! ## §0. Count and fit kit -/

/-- Twin-blindness on the mover side of the fit (a restatement of the
frozen `Orig/Twin.lean:74`; `Orig2/SeatMateStack.lean` keeps its own
private copy). -/
private theorem canSitOn_twin_left (c b : Card) :
    canSitOn c.twin b = canSitOn c b := by
  rcases c with ⟨s, r⟩
  rcases b with ⟨s', r'⟩
  cases s <;> cases s' <;> rfl

/-- `tfc_cntFlat` is the sum of the per-zone counts. -/
private theorem cntFlat_eq_sum_map (c : Card) :
    ∀ zs : List (List Card), tfc_cntFlat c zs = (zs.map (tfc_cnt c)).sum
  | [] => rfl
  | z :: zs => by
      rw [tfc_cntFlat_cons, List.map_cons, List.sum_cons,
        cntFlat_eq_sum_map c zs]

/-- Two entries of a nodup list may be exchanged whenever the two
counts balance: the sum of a mapped nodup list only reads the two
special entries and the rest unchanged. -/
private theorem sum_map_two_eq {α : Type} [DecidableEq α] (L : List α)
    (F G : α → Nat) (a b : α) (hnd : L.Nodup)
    (hout : ∀ j ∈ L, j ≠ a → j ≠ b → G j = F j)
    (ha : a ∈ L) (hb : b ∈ L)
    (hab : a ≠ b) (hpair : G a + G b = F a + F b) :
    (L.map G).sum = (L.map F).sum := by
  have aux : ∀ (L : List α), L.Nodup →
      (∀ j ∈ L, j ≠ a → j ≠ b → G j = F j) →
      (L.map G).sum + (if a ∈ L then F a else 0) + (if b ∈ L then F b else 0)
        = (L.map F).sum + (if a ∈ L then G a else 0)
          + (if b ∈ L then G b else 0) := by
    intro L
    induction L with
    | nil => intro _ _; rfl
    | cons x t ih =>
        intro hnd hout
        obtain ⟨hxnot, hnd'⟩ := List.nodup_cons.mp hnd
        have hout' : ∀ j ∈ t, j ≠ a → j ≠ b → G j = F j :=
          fun j hj hja hjb => hout j (List.mem_cons_of_mem _ hj) hja hjb
        have ih' := ih hnd' hout'
        by_cases hxa : x = a
        · cases hxa
          have hta : a ∉ t := hxnot
          have hba : b ≠ a := fun h => hab h.symm
          by_cases hbt : b ∈ t
          · rw [if_neg hta, if_neg hta, if_pos hbt, if_pos hbt] at ih'
            simp [List.map_cons, List.sum_cons, List.mem_cons, hba, hbt] at ih' ⊢
            omega
          · rw [if_neg hta, if_neg hta, if_neg hbt, if_neg hbt] at ih'
            simp [List.map_cons, List.sum_cons, List.mem_cons, hba, hbt] at ih' ⊢
            omega
        · by_cases hxb : x = b
          · cases hxb
            have htb : b ∉ t := hxnot
            have hab' : a ≠ b := hab
            by_cases hat : a ∈ t
            · rw [if_pos hat, if_pos hat, if_neg htb, if_neg htb] at ih'
              simp [List.map_cons, List.sum_cons, List.mem_cons, hab', hat] at ih' ⊢
              omega
            · rw [if_neg hat, if_neg hat, if_neg htb, if_neg htb] at ih'
              simp [List.map_cons, List.sum_cons, List.mem_cons, hab', hat] at ih' ⊢
              omega
          · have houtx : G x = F x := hout x List.mem_cons_self hxa hxb
            have hax : a ≠ x := fun h => hxa h.symm
            have hbx : b ≠ x := fun h => hxb h.symm
            by_cases hat : a ∈ t
            · by_cases hbt : b ∈ t
              · rw [if_pos hat, if_pos hat, if_pos hbt, if_pos hbt] at ih'
                simp [List.map_cons, List.sum_cons, List.mem_cons, hax, hbx, hat, hbt,
                  houtx] at ih' ⊢
                omega
              · rw [if_pos hat, if_pos hat, if_neg hbt, if_neg hbt] at ih'
                simp [List.map_cons, List.sum_cons, List.mem_cons, hax, hbx, hat, hbt,
                  houtx] at ih' ⊢
                omega
            · by_cases hbt : b ∈ t
              · rw [if_neg hat, if_neg hat, if_pos hbt, if_pos hbt] at ih'
                simp [List.map_cons, List.sum_cons, List.mem_cons, hax, hbx, hat, hbt,
                  houtx] at ih' ⊢
                omega
              · rw [if_neg hat, if_neg hat, if_neg hbt, if_neg hbt] at ih'
                simp [List.map_cons, List.sum_cons, List.mem_cons, hax, hbx, hat, hbt,
                  houtx] at ih' ⊢
                omega
  have h := aux L hnd hout
  have hia : (if a ∈ L then F a else 0) = F a := if_pos ha
  have hib : (if b ∈ L then F b else 0) = F b := if_pos hb
  have hga : (if a ∈ L then G a else 0) = G a := if_pos ha
  have hgb : (if b ∈ L then G b else 0) = G b := if_pos hb
  rw [hia, hib, hga, hgb] at h
  omega

namespace State

/-! ## §1. The card census -/

/-- **`cardCount_splice`** — the run swap moves the two runs between
the piles without changing the multiset of cards in the zones, so every
card's count is untouched. -/
theorem cardCount_splice {st : State} {x : Card} {a b : Anchor}
    (ha : st.pileHolding x = some a) (hb : st.pileHolding x.twin = some b)
    (hab : a ≠ b) (c₀ : Card) :
    (st.spliceTwinRuns x).cardCount c₀ = st.cardCount c₀ := by
  have hfound := spliceTwinRuns_found ha hb hab
  have hstock := spliceTwinRuns_stock ha hb hab
  have hwaste := spliceTwinRuns_waste ha hb hab
  have hAp : tfc_cnt c₀ (st.piles a).faceUp =
      tfc_cnt c₀ (below x (st.piles a).faceUp) +
        tfc_cnt c₀ (fromCard x (st.piles a).faceUp) := by
    calc
      tfc_cnt c₀ (st.piles a).faceUp
          = tfc_cnt c₀ (below x (st.piles a).faceUp ++
              fromCard x (st.piles a).faceUp) := by
            rw [tfc_below_fromCard x (st.piles a).faceUp]
      _ = tfc_cnt c₀ (below x (st.piles a).faceUp) +
            tfc_cnt c₀ (fromCard x (st.piles a).faceUp) :=
            tfc_cnt_app c₀ _ _
  have hBp : tfc_cnt c₀ (st.piles b).faceUp =
      tfc_cnt c₀ (below x.twin (st.piles b).faceUp) +
        tfc_cnt c₀ (fromCard x.twin (st.piles b).faceUp) := by
    calc
      tfc_cnt c₀ (st.piles b).faceUp
          = tfc_cnt c₀ (below x.twin (st.piles b).faceUp ++
              fromCard x.twin (st.piles b).faceUp) := by
            rw [tfc_below_fromCard x.twin (st.piles b).faceUp]
      _ = tfc_cnt c₀ (below x.twin (st.piles b).faceUp) +
            tfc_cnt c₀ (fromCard x.twin (st.piles b).faceUp) :=
            tfc_cnt_app c₀ _ _
  have hpair :
      tfc_cnt c₀ (((st.spliceTwinRuns x).piles a).hidden ++
          ((st.spliceTwinRuns x).piles a).faceUp) +
        tfc_cnt c₀ (((st.spliceTwinRuns x).piles b).hidden ++
          ((st.spliceTwinRuns x).piles b).faceUp)
      = tfc_cnt c₀ ((st.piles a).hidden ++ (st.piles a).faceUp) +
        tfc_cnt c₀ ((st.piles b).hidden ++ (st.piles b).faceUp) := by
    rw [spliceTwinRuns_piles_self ha hb hab,
      spliceTwinRuns_piles_second ha hb hab]
    simp only [tfc_cnt_app]
    rw [hAp, hBp]
    omega
  have hflat : tfc_cntFlat c₀ (Anchor.all.map fun j =>
        ((st.spliceTwinRuns x).piles j).hidden ++
          ((st.spliceTwinRuns x).piles j).faceUp)
      = tfc_cntFlat c₀ (Anchor.all.map fun j =>
        (st.piles j).hidden ++ (st.piles j).faceUp) := by
    simp only [cntFlat_eq_sum_map]
    rw [List.map_map, List.map_map]
    exact sum_map_two_eq Anchor.all
      (fun j => tfc_cnt c₀ ((st.piles j).hidden ++ (st.piles j).faceUp))
      (fun j => tfc_cnt c₀ (((st.spliceTwinRuns x).piles j).hidden ++
        ((st.spliceTwinRuns x).piles j).faceUp))
      a b Anchor.all_nodup
      (fun j _ hja hjb => by rw [spliceTwinRuns_piles_other ha hb hab hja hjb])
      (Anchor.mem_all a) (Anchor.mem_all b) hab hpair
  rw [tfc_cardCount_zones, tfc_cardCount_zones, hfound, hstock, hwaste, hflat]

/-! ## §2. The two edited runs -/

/-- **`runOK_splice_piles`** — every pile's face-up run is still legal
after the splice.  The only new junctions are
`preA ++ fromCard x.twin B` and `preB ++ fromCard x A`; the run heads
are the twins themselves, and the parents read off the `.inr` seats fit
the twins by the fit's twin-blindness. -/
theorem runOK_splice_piles {st : State} {x : Card} {a b : Anchor}
    (hwf : st.WF) (ha : st.pileHolding x = some a)
    (hb : st.pileHolding x.twin = some b) (hab : a ≠ b)
    (hx : ∃ z, seatOf st x = some (Sum.inr z))
    (hxt : ∃ z : Card, seatOf st x.twin = some (Sum.inr z.twin))
    (j : Anchor) :
    runOK ((st.spliceTwinRuns x).piles j).faceUp = true := by
  obtain ⟨zA, hseA⟩ := hx
  obtain ⟨a', hhA, -, hlastA⟩ := tfc_seatOf_of_inr hseA
  have haa : a' = a := by
    rw [ha] at hhA
    exact (Option.some.inj hhA).symm
  rw [haa] at hlastA
  have hcanA : canSitOn x zA = true := (tfc_seat_parent hwf ha hlastA).1
  obtain ⟨zB, hseB⟩ := hxt
  obtain ⟨b', hhB, -, hlastB⟩ := tfc_seatOf_of_inr hseB
  have hbb : b' = b := by
    rw [hb] at hhB
    exact (Option.some.inj hhB).symm
  rw [hbb] at hlastB
  have hcanB : canSitOn x.twin zB.twin = true := (tfc_seat_parent hwf hb hlastB).1
  by_cases hja : j = a
  · rw [hja] at *
    rw [spliceTwinRuns_piles_self ha hb hab]
    have hpreOK := tfc_runOK_below (st.piles a).faceUp x (hwf.runOK_of a)
    obtain ⟨rB, hrB⟩ :=
      tfc_fromCard_cons_head (c := x.twin) (st.piles b).faceUp (pileHolding_mem hb)
    have hrunB' : runOK (x.twin :: rB) = true := by
      have h := tfc_runOK_fromCard (st.piles b).faceUp x.twin (hwf.runOK_of b)
      rw [hrB] at h
      exact h
    have hfit : canSitOn x.twin zA = true := by
      simpa [canSitOn_twin_left] using hcanA
    rw [hrB]
    exact tfc_runOK_append_fit (below x (st.piles a).faceUp) x.twin zA rB
      hpreOK hrunB' hlastA hfit
  · by_cases hjb : j = b
    · rw [hjb] at *
      rw [spliceTwinRuns_piles_second ha hb hab]
      have hpreOK := tfc_runOK_below (st.piles b).faceUp x.twin (hwf.runOK_of b)
      obtain ⟨rA, hrA⟩ :=
        tfc_fromCard_cons_head (c := x) (st.piles a).faceUp (pileHolding_mem ha)
      have hrunA' : runOK (x :: rA) = true := by
        have h := tfc_runOK_fromCard (st.piles a).faceUp x (hwf.runOK_of a)
        rw [hrA] at h
        exact h
      have hfit : canSitOn x zB.twin = true := by
        simpa [canSitOn_twin_left] using hcanB
      rw [hrA]
      exact tfc_runOK_append_fit (below x.twin (st.piles b).faceUp) x zB.twin rA
        hpreOK hrunA' hlastB hfit
    · rw [spliceTwinRuns_piles_other ha hb hab hja hjb]
      exact hwf.runOK_of j

end State

open State

/-! ## §3. The WF capstone -/

/-- **`wf_spliceTwinRuns`** — the strict twin run splice preserves
well-formedness. -/
theorem wf_spliceTwinRuns {st : State} {x : Card} (hwf : st.WF)
    (hx : ∃ z, seatOf st x = some (Sum.inr z))
    (hxt : ∃ z : Card, seatOf st x.twin = some (Sum.inr z.twin)) :
    (st.spliceTwinRuns x).WF := by
  have hwf' : st.WF := hwf
  obtain ⟨hpre, hpile, hcard, hsd⟩ := hwf
  cases ha : st.pileHolding x with
  | none =>
      rw [spliceTwinRuns_of_none_left ha]
      exact ⟨hpre, hpile, hcard, hsd⟩
  | some a =>
      cases hb : st.pileHolding x.twin with
      | none =>
          rw [spliceTwinRuns_of_none_right hb]
          exact ⟨hpre, hpile, hcard, hsd⟩
      | some b =>
          by_cases hab : a = b
          · have hba : b = a := hab.symm
            rw [hba] at hb
            rw [spliceTwinRuns_of_eq ha hb]
            exact ⟨hpre, hpile, hcard, hsd⟩
          · refine ⟨?_, ?_, ?_, ?_⟩
            · intro s
              rw [spliceTwinRuns_found ha hb hab]
              exact hpre s
            · intro j
              exact runOK_splice_piles hwf' ha hb hab hx hxt j
            · intro c₀ hc₀
              rw [cardCount_splice ha hb hab c₀]
              exact hcard c₀ hc₀
            · rw [spliceTwinRuns_drawStep ha hb hab]
              exact hsd

/-! ## §4. Audit -/

#print axioms wf_spliceTwinRuns
