import Orig2.TwinLastPull
import Orig2.TwinPreludeFunctor
import Orig2.TwinRecipeRiders
import Orig2.TwinPreludeAssembly

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# Orig2.TwinPreludeCollapse — the PreludePath normal form

A `PreludePath` is a concatenation of pair-free blocks and swap blocks
(recipe / self-swap).  Since every swap block's endpoint is exactly the
run splice of its source, two swap blocks cancel modulo pair-free moves
using the pair-free splice functor.  Hence every `PreludePath` collapses
to the semidirect-product normal form

```text
PairFreeOrbit x s' s  ∨  PairFreeOrbit x s' (s.spliceTwinRuns x).
```

This is the orbit normal form on the segmented grammar, independent of
the raw last-pull induction.
-/

open State

/-- Pair-free reversal, with the readiness hypotheses at the source. -/
private theorem pairFreeOrbit_symm {x : Card} {s t : State}
    (hwf : s.WF)
    (hx : ∃ z, seatOf s x = some (Sum.inr z))
    (hxt : ∃ z : Card, seatOf s x.twin = some (Sum.inr z.twin))
    (h : PairFreeOrbit x s t) : PairFreeOrbit x t s := by
  obtain ⟨z, hz⟩ := hx
  obtain ⟨zt, hzt⟩ := hxt
  have hztz : zt = z := twin_parent_eq_of_seats hwf hz hzt
  have hzt' : seatOf s x.twin = some (Sum.inr z.twin) := by
    simpa [hztz] using hzt
  obtain ⟨play, hplay, hno⟩ := h
  exact TwinPairFreeRev.pairFreeReversal (x := x) hwf hz hzt' hplay hno

/-- **The `PreludePath` collapse.**  Every prelude path is pair-free
equivalent to its source or to the source's run splice. -/
theorem pairFreeOrbit_of_preludePath {x : Card} :
    ∀ {s s' : State} {play : List Move}, PreludePath x s play s' →
      s.WF →
      (∃ z, seatOf s x = some (Sum.inr z)) →
      (∃ z : Card, seatOf s x.twin = some (Sum.inr z.twin)) →
      PairFreeOrbit x s' s ∨ PairFreeOrbit x s' (s.spliceTwinRuns x)
  | _, _, _, .nil _, _, _, _ => Or.inl (pairFreeOrbit_refl x _)
  | _, _, _, .pairFree hwf hxs hxts _hxu _hxtu hplay hno, _, _, _ =>
      Or.inl (pairFreeOrbit_symm hwf hxs hxts ⟨_, hplay, hno⟩)
  | _, _, _, @PreludePath.recipeTwin _ u w seg h, _, _, _ => by
      obtain ⟨hwfu, _hxu, _hxtu, _hxw, _hxtw, z, a, hc, hct, hpa, hraise,
        hseg, hplay⟩ := h
      have hwfw : w.WF := run_wf hwfu (Walk_run _ hplay)
      have hstrict : twinPairSwapStrict u w x :=
        twinPairSwapStrict_recipe_endpoint_riders hwfu hwfw hc hct hpa hraise
          (by simpa [hseg] using hplay)
      have hw : w = u.spliceTwinRuns x :=
        eq_splice_of_twinPairSwapStrict hwfu hwfw ⟨z, hc⟩ ⟨z, hct⟩ hstrict
      exact Or.inr (by rw [hw]; exact pairFreeOrbit_refl x (u.spliceTwinRuns x))
  | _, _, _, @PreludePath.recipeSelf _ u w seg h, _, _, _ => by
      obtain ⟨hwfu, _hxu, _hxtu, _hxw, _hxtw, z, a, hc, hct, hpa, hraise,
        hseg, hplay⟩ := h
      have hwfw : w.WF := run_wf hwfu (Walk_run _ hplay)
      have hstrictT : twinPairSwapStrict u w x.twin :=
        twinPairSwapStrict_recipe_endpoint_riders (x := x.twin) (z := z.twin)
          (a := a) hwfu hwfw hct
          (by simpa [card_twin_twin] using hc)
          (by simpa [card_twin_twin] using hpa)
          (by simpa [card_twin_twin] using hraise)
          (by simpa [hseg, card_twin_twin] using hplay)
      have hstrict : twinPairSwapStrict u w x :=
        (twinPairSwapStrict_twin_iff (u := u) (v := w) (c := x)).mpr hstrictT
      have hw : w = u.spliceTwinRuns x :=
        eq_splice_of_twinPairSwapStrict hwfu hwfw ⟨z, hc⟩ ⟨z, hct⟩ hstrict
      exact Or.inr (by rw [hw]; exact pairFreeOrbit_refl x (u.spliceTwinRuns x))
  | _, _, _, @PreludePath.selfSwap _ u w seg h, _, _, _ => by
      obtain ⟨_hwfu, _hxu, _hxtu, _hplay, hw⟩ := h
      exact Or.inr (by rw [hw]; exact pairFreeOrbit_refl x (u.spliceTwinRuns x))
  | _, _, _, @PreludePath.trans _ s u v l1 l2 h1 h2, hwf, hx, hxt => by
      have hmid := preludePath_target_wf_seats h1 hwf hx hxt
      have huWF : u.WF := hmid.1
      have hux : ∃ z, seatOf u x = some (Sum.inr z) := hmid.2.1
      have huxt : ∃ z : Card, seatOf u x.twin = some (Sum.inr z.twin) := hmid.2.2
      have r1 := pairFreeOrbit_of_preludePath h1 hwf hx hxt
      have r2 := pairFreeOrbit_of_preludePath h2 huWF hux huxt
      rcases r1 with r1 | r1
      · -- u ~pf s
        rcases r2 with r2 | r2
        · exact Or.inl (PairFreeOrbit.trans r2 r1)
        · -- v ~pf u.splice, and splice is functorial on u ~pf s
          obtain ⟨play1, hplay1, hno1⟩ := r1
          have hcongr : PairFreeOrbit x (u.spliceTwinRuns x) (s.spliceTwinRuns x) :=
            TwinLastPull.pairFreeOrbit_splice_of_pairFree (x := x) huWF hux huxt hplay1 hno1
          exact Or.inr (PairFreeOrbit.trans r2 hcongr)
      · -- u ~pf s.splice
        rcases r2 with r2 | r2
        · exact Or.inr (PairFreeOrbit.trans r2 r1)
        · -- v ~pf u.splice, u ~pf s.splice; splice again to cancel
          obtain ⟨play1, hplay1, hno1⟩ := r1
          have hcongr : PairFreeOrbit x (u.spliceTwinRuns x)
              ((s.spliceTwinRuns x).spliceTwinRuns x) :=
            TwinLastPull.pairFreeOrbit_splice_of_pairFree (x := x) huWF hux huxt hplay1 hno1
          rw [spliceTwinRuns_invol hwf hx hxt] at hcongr
          exact Or.inl (PairFreeOrbit.trans r2 hcongr)

/-- **The two cosets are disjoint.**  A both-`.inr`-seated state is never
pair-free-equivalent to its run splice: pair-free plays preserve the direct
seats exactly, while the splice exchanges the two parents. -/
theorem pairFreeOrbit_splice_disjoint {x : Card} {s : State}
    (hwf : s.WF)
    (hx : ∃ z, seatOf s x = some (Sum.inr z))
    (hxt : ∃ z : Card, seatOf s x.twin = some (Sum.inr z.twin)) :
    ¬ PairFreeOrbit x s (s.spliceTwinRuns x) := by
  intro h
  obtain ⟨z, hz⟩ := hx
  obtain ⟨zt, hzt⟩ := hxt
  obtain ⟨play, hplay, hno⟩ := h
  have hseats := TwinLastPull.seat_eq_of_pairFree_play hwf hplay hno ⟨z, hz⟩ ⟨zt, hzt⟩
  obtain ⟨a, b, zs, ha, hb, hab, _hza, _hzb⟩ :=
    TwinSpliceComm.splice_setup hwf ⟨z, hz⟩ ⟨zt, hzt⟩
  have hxS : seatOf (s.spliceTwinRuns x) x = some (Sum.inr zt.twin) := by
    rw [seatOf_splice_self hwf ha hb hab]
    exact hzt
  rw [hseats.1, hz] at hxS
  have hzt_eq : z = zt.twin := by
    injection hxS with h
    exact Sum.inr.inj h
  have hztz : zt = z := twin_parent_eq_of_seats hwf hz hzt
  have hztwin : z = z.twin := hzt_eq.trans (congrArg Card.twin hztz)
  exact (card_twin_ne z) hztwin.symm

/-- **The two cosets are mutually exclusive**, hence the swap bit in the
normal form is unique. -/
theorem pairFreeOrbit_cosets_exclusive {x : Card} {s s' : State}
    (hwf : s.WF)
    (hx : ∃ z, seatOf s x = some (Sum.inr z))
    (hxt : ∃ z : Card, seatOf s x.twin = some (Sum.inr z.twin))
    (hwf' : s'.WF)
    (hx' : ∃ z, seatOf s' x = some (Sum.inr z))
    (hxt' : ∃ z : Card, seatOf s' x.twin = some (Sum.inr z.twin))
    (h1 : PairFreeOrbit x s' s)
    (h2 : PairFreeOrbit x s' (s.spliceTwinRuns x)) : False := by
  have htrans : PairFreeOrbit x s (s.spliceTwinRuns x) :=
    PairFreeOrbit.trans (pairFreeOrbit_symm hwf' hx' hxt' h1) h2
  exact pairFreeOrbit_splice_disjoint hwf hx hxt htrans

/-- **The orbit normal form from the WF-gated prelude normalization.**
The board play is segmented into a `PreludePath` and collapsed; the
draws-only rotation is pair-free and reverses to the endpoint. -/
theorem orbit_normal_form_of_preludeNormalization {x : Card}
    (hnorm : PreludeNormalizationWF x)
    {s s' : State} (hwf : s.WF) (hwf' : s'.WF)
    (hx : ∃ z, seatOf s x = some (Sum.inr z))
    (hxt : ∃ z : Card, seatOf s x.twin = some (Sum.inr z.twin))
    (hx' : ∃ z, seatOf s' x = some (Sum.inr z))
    (hxt' : ∃ z : Card, seatOf s' x.twin = some (Sum.inr z.twin))
    (hclass : sameOrbitSetoid.r s s') :
    PairFreeOrbit x s' s ∨ PairFreeOrbit x s' (s.spliceTwinRuns x) := by
  obtain ⟨z, hnd, hrot⟩ := (sameOrbit_factor hwf hwf').mp hclass
  obtain ⟨σ, τ, hσ, hτ⟩ := hrot
  obtain ⟨hσW, hσdraw⟩ := hσ
  obtain ⟨hτW, hτdraw⟩ := hτ
  have hnoσ : ∀ m ∈ σ, NotFoundPair x m := by
    intro m hm
    rw [hσdraw m hm]
    simp [NotFoundPair]
  have hnoτ : ∀ m ∈ τ, NotFoundPair x m := by
    intro m hm
    rw [hτdraw m hm]
    simp [NotFoundPair]
  have hzwf : z.WF := run_wf hwf' (Walk_run _ hτW)
  have hseats :=
    TwinLastPull.seat_eq_of_pairFree_play hwf' hτW hnoτ hx' hxt'
  have hzx : ∃ z', seatOf z x = some (Sum.inr z') := by
    obtain ⟨w, hw⟩ := hx'
    exact ⟨w, by rw [hseats.1, hw]⟩
  have hzxt : ∃ z' : Card, seatOf z x.twin = some (Sum.inr z'.twin) := by
    obtain ⟨w, hw⟩ := hxt'
    exact ⟨w, by rw [hseats.2, hw]⟩
  obtain ⟨play, hpath⟩ := hnorm hwf hnd hx hxt hzx hzxt
  have hcoll := pairFreeOrbit_of_preludePath hpath hwf hx hxt
  have hdrawBack : PairFreeOrbit x s' z :=
    pairFreeOrbit_symm hzwf hzx hzxt ⟨σ, hσW, hnoσ⟩
  rcases hcoll with hcoll | hcoll
  · exact Or.inl (PairFreeOrbit.trans hdrawBack hcoll)
  · exact Or.inr (PairFreeOrbit.trans hdrawBack hcoll)

/-- **The orbit normal form from the last-pull residual.** -/
theorem orbit_normal_form_of_lastPull {x : Card}
    (hlast : ∀ x : Card, LastPullCancellation x)
    {s s' : State} (hwf : s.WF) (hwf' : s'.WF)
    (hx : ∃ z, seatOf s x = some (Sum.inr z))
    (hxt : ∃ z : Card, seatOf s x.twin = some (Sum.inr z.twin))
    (hx' : ∃ z, seatOf s' x = some (Sum.inr z))
    (hxt' : ∃ z : Card, seatOf s' x.twin = some (Sum.inr z.twin))
    (hclass : sameOrbitSetoid.r s s') :
    PairFreeOrbit x s' s ∨ PairFreeOrbit x s' (s.spliceTwinRuns x) :=
  orbit_normal_form_of_preludeNormalization
    (preludeNormalizationWF_of_lastPull hlast x)
    hwf hwf' hx hxt hx' hxt' hclass

/-- **The groupoid characterization (split-extension form).**  At a
both-`.inr` pair, the orbit class of `s` is the disjoint union of the
pair-free orbit of `s` and, when the swap is available, the pair-free
orbit of `s.spliceTwinRuns x`.  This is a genuine iff, not just a
one-way normal form. -/
theorem sameOrbit_iff_pairFree_or_swappable {x : Card}
    (hlast : ∀ x : Card, LastPullCancellation x)
    {s t : State} (hwf : s.WF) (hwf' : t.WF)
    (hx : ∃ z, seatOf s x = some (Sum.inr z))
    (hxt : ∃ z : Card, seatOf s x.twin = some (Sum.inr z.twin))
    (hx' : ∃ z, seatOf t x = some (Sum.inr z))
    (hxt' : ∃ z : Card, seatOf t x.twin = some (Sum.inr z.twin)) :
    sameOrbitSetoid.r s t ↔
      PairFreeOrbit x t s ∨
        (SwappableIn s x ∧ PairFreeOrbit x t (s.spliceTwinRuns x)) := by
  constructor
  · intro hclass
    rcases orbit_normal_form_of_lastPull hlast hwf hwf' hx hxt hx' hxt' hclass with
      hleft | hright
    · exact Or.inl hleft
    · refine Or.inr ⟨?_, hright⟩
      obtain ⟨play, hplay, _hno⟩ := hright
      have hsp : sameOrbitSetoid.r s (s.spliceTwinRuns x) := by
        show RevEqW (s.spliceTwinRuns x) s
        exact RevEqW_trans (RevEqW_symm (shufflePlayW_revEqW hplay)) hclass
      exact (swappableIn_iff_orbit_splice hwf hx hxt).mpr hsp
  · intro h
    rcases h with hleft | ⟨hswap, hright⟩
    · obtain ⟨play, hplay, _hno⟩ := hleft
      show RevEqW t s
      exact shufflePlayW_revEqW hplay
    · obtain ⟨play, hplay, _hno⟩ := hright
      have h1 : RevEqW t (s.spliceTwinRuns x) := shufflePlayW_revEqW hplay
      have h2 : RevEqW (s.spliceTwinRuns x) s :=
        (swappableIn_iff_orbit_splice hwf hx hxt).mp hswap
      exact RevEqW_trans h1 h2

#print axioms pairFreeOrbit_splice_disjoint
#print axioms pairFreeOrbit_cosets_exclusive
#print axioms pairFreeOrbit_of_preludePath
#print axioms orbit_normal_form_of_preludeNormalization
#print axioms orbit_normal_form_of_lastPull
#print axioms sameOrbit_iff_pairFree_or_swappable




