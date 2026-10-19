import Orig2.TwinPointFunctor
import Orig2.TwinSwapUnique
import Orig2.Integrity

set_option linter.unusedSectionVars false

open State

/-!
# Temp/TwinSpliceUnique — with riders, the WF strict target is the run splice

The rider-free counterpart `Orig2.TwinSwapUnique` identifies a `WF`
strict twin-swap target with the value relabeling `State.relabelTwin`.
That relabeling drags riders along with the relabeled card values.  The
rider-general operation is `State.spliceTwinRuns`, which swaps the two
face-up runs above the twins and leaves every rider on its parent card.

This card proves the matching uniqueness row: if both twins sit on card
parents (`seatOf ... = some (.inr _)`), `v` is a `WF` strict twin-swap
target of `s`, then `v` is exactly the run splice.  The proof is the
`eq_relabelTwin_of_twinPairSwapStrict` chart round trip with the seat
readout supplied by `seatOf_splice_self` / `_twin` / `_other`; the
occurrence counts on both sides pin the face-up contents.

House compliance: new file only; zero `sorry`; zero
`Classical.choice`.
-/

/-! ## §1. Private run kit -/

/-- Two cards of equal rank cannot occupy different positions of a
legal run: ranks strictly descend along it.  (The splice rule needs
`Card.twin`'s rank preservation to keep the twins in different piles.) -/
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

/-! ## §2. The uniqueness row -/

/-- **THE RIDER-GENERAL BRIDGE** — with both twins on `.inr` parents and
`v.WF`, every strict twin-swap target of `s` is the run splice. -/
theorem eq_splice_of_twinPairSwapStrict {s v : State} {x : Card}
    (hwf : s.WF) (hwv : v.WF)
    (hx : ∃ z, seatOf s x = some (Sum.inr z))
    (hxt : ∃ z : Card, seatOf s x.twin = some (Sum.inr z.twin))
    (h : twinPairSwapStrict s v x) :
    v = s.spliceTwinRuns x := by
  obtain ⟨hvx, hvt, hvother, hbf, hff, hstock, hwaste, _hcut⟩ := h
  have hxkeep := hx
  have hxtkeep := hxt
  obtain ⟨z, hzse⟩ := hx
  obtain ⟨a, ha, -, -⟩ := tfc_seatOf_of_inr hzse
  obtain ⟨zt, hztse⟩ := hxt
  obtain ⟨b, hb, -, -⟩ := tfc_seatOf_of_inr hztse
  have hab : a ≠ b := by
    intro hab
    rw [hab] at ha
    have hxmem : x ∈ (s.piles b).faceUp := pileHolding_mem ha
    have htmem : x.twin ∈ (s.piles b).faceUp := pileHolding_mem hb
    have heq : x = x.twin :=
      runOK_rank_distinct (hwf.runOK_of b) hxmem htmem rfl
    exact (card_twin_ne x) heq.symm
  let w : State := s.spliceTwinRuns x
  have hwhidden : ∀ a', (w.piles a').hidden = (s.piles a').hidden := by
    intro a'
    by_cases h₁ : a' = a
    · rw [h₁]
      rw [show w.piles a = (s.spliceTwinRuns x).piles a from rfl,
        spliceTwinRuns_piles_self ha hb hab]
    · by_cases h₂ : a' = b
      · rw [h₂]
        rw [show w.piles b = (s.spliceTwinRuns x).piles b from rfl,
          spliceTwinRuns_piles_second ha hb hab]
      · rw [show w.piles a' = (s.spliceTwinRuns x).piles a' from rfl,
          spliceTwinRuns_piles_other ha hb hab h₁ h₂]
  have hseat : ∀ y, seatOf v y = seatOf w y := by
    intro y
    by_cases hyx : y = x
    · rw [hyx]
      rw [hvx, show seatOf w x = seatOf s x.twin from
        seatOf_splice_self hwf ha hb hab]
    · by_cases hyt : y = x.twin
      · rw [hyt]
        rw [hvt, show seatOf w x.twin = seatOf s x from
          seatOf_splice_twin hwf ha hb hab]
      · rw [hvother y hyx hyt, show seatOf w y = seatOf s y from
          seatOf_splice_other hwf hyx hyt]
  have hhidden : ∀ a', (v.piles a').hidden = (w.piles a').hidden := by
    intro a'
    rw [← hbf.1 a', hwhidden a']
  have hds : v.drawStep = w.drawStep := by
    rw [← hbf.2, show w.drawStep = s.drawStep from spliceTwinRuns_drawStep ha hb hab]
  have hfound : foundsFixed v w := by
    intro su
    rw [← hff su, show w.found su = s.found su from
      congrFun (spliceTwinRuns_found ha hb hab) su]
  have hpool : drawPool v = drawPool w := by
    unfold drawPool
    rw [← hstock, ← hwaste,
      show w.stock = s.stock from spliceTwinRuns_stock ha hb hab,
      show w.waste = s.waste from spliceTwinRuns_waste ha hb hab]
  have hcut : cutOf v = cutOf w := by
    unfold cutOf
    rw [← hstock, show w.stock = s.stock from spliceTwinRuns_stock ha hb hab]
  have hcv : ∀ c, v.cardCount c = 1 :=
    fun c => hwv.2.2.1 c (Card.mem_universe c)
  have hcw : ∀ c, w.cardCount c = 1 := by
    intro c
    exact (wf_spliceTwinRuns hwf hxkeep hxtkeep).2.2.1 c (Card.mem_universe c)
  exact chart_round_trip_core v w hcv hcw
    ⟨hseat, ⟨hhidden, hds⟩, hfound, hpool, hcut⟩

/-! ## §3. Audit -/

/-- **`SwappableIn` is exactly the point object's orbit at `s`.**  By
rider-general uniqueness, any strict target is the run splice, so the
existential swap predicate is the orbit relation to the point object. -/
theorem swappableIn_iff_orbit_splice {s : State} {x : Card}
    (hwf : s.WF)
    (hx : ∃ z, seatOf s x = some (Sum.inr z))
    (hxt : ∃ z : Card, seatOf s x.twin = some (Sum.inr z.twin)) :
    SwappableIn s x ↔ sameOrbitSetoid.r s (s.spliceTwinRuns x) := by
  constructor
  · rintro ⟨v, hstrict, horb⟩
    obtain ⟨σ, hσ, τ, hτ⟩ := horb
    have hvWF : v.WF := run_wf hwf (Walk_run _ hτ)
    have hveq : v = s.spliceTwinRuns x :=
      eq_splice_of_twinPairSwapStrict hwf hvWF hx hxt hstrict
    rw [← hveq]
    exact ⟨σ, hσ, τ, hτ⟩
  · intro horb
    exact ⟨s.spliceTwinRuns x, twinPairSwapStrict_splice hwf hx hxt, horb⟩

#print axioms eq_splice_of_twinPairSwapStrict
#print axioms swappableIn_iff_orbit_splice
