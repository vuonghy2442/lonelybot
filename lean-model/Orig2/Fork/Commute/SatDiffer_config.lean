import Orig2.Fork.Class.ForkRaiseReorderProof
import Orig2.Fork.Split.FirstPassage

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

/-!
# Temp/SatDiffer_config — the slim licence configuration card

The final chain consumes exactly three rows from this card:

* `SatDifferConfig.licence_lost_only_by_twin` — a same-rank raise of a card
  other than `c` or `c.twin` preserves `c`'s `S`-licence;
* `SatDifferConfig.canRaise_after_pull` — the pulled card is vanilla-raisable
  at the pull's landing;
* `SatDifferConfig.canRaiseS_after_pull` — the same card is `S`-live there.

Everything else (the `SatDifferForkWF_of_*` assembly tail and the
`Drain_transport_rows` dependency) has been removed; the commutation route in
`PullExtension`/`PullCommute` supersedes it.

House compliance: zero `sorry`, zero `Classical.choice`, zero
`noncomputable`, zero `native_decide`.
-/

namespace SatDifferConfig

open OneColourClosure

/-! ## §1. Step 1 — a same-rank raise never kills the licence

The leaf row: a card of the raised card's rank, other than the card
itself and its twin, cannot sit on the raised pile nor on the twin's
top, so neither `freeCardS` read moves. -/

/-- **A same-rank card other than the top is not in the top's pile.**
(`rank_lt_of_mem_of_lastOf` with the strict inequality collapsed to
equality by the same-rank hypothesis.) -/
theorem not_mem_pileOfTop_of_rank_eq {z : State} (hz : z.WF) {e d : Card} {a : Anchor}
    (hpa : z.pileOfTop e = some a) (hde : d ≠ e) (hr : d.rank = e.rank) :
    d ∉ (z.piles a).faceUp := by
  intro hmem
  have hlast : lastOf (z.piles a).faceUp = some e := (pileOfTop_top hpa).2
  have hlt := OneColourClosure.rank_lt_of_mem_of_lastOf (hz.2.1 a) hlast hmem hde
  rw [hr] at hlt
  exact absurd hlt (by omega)

/-- **`freeCardS` is preserved (forward) by a same-rank raise.**
`freeCardS` reads `c`'s holding pile and `pileOfTop c.twin`; the raised
pile is neither, and the twin's top cannot vanish.  (Equality can fail
in one direction only: a raise may *reveal* `c.twin` from the hidden
deck of the raised pile, which turns `none` into `some` — harmless for
the forward read used by the licence.) -/
theorem freeCardS_fwd_of_rank_eq {z z' : State} {e d : Card}
    (hz : z.WF) (hstep : State.step z (Move.tabToFound e) = some z')
    (hde : d ≠ e) (hdt : d.twin ≠ e) (hr : d.rank = e.rank) :
    freeCardS z d = true → freeCardS z' d = true := by
  obtain ⟨a0, hpa0, hpiles⟩ := OneColourClosure.piles_tabToFound hstep
  have hz' : z'.WF := step_wf hz hstep
  have hd0 : d ∉ (z.piles a0).faceUp := not_mem_pileOfTop_of_rank_eq hz hpa0 hde hr
  have hdt0 : d.twin ∉ (z.piles a0).faceUp := by
    refine not_mem_pileOfTop_of_rank_eq hz hpa0 hdt ?_
    show d.twin.rank = e.rank
    rw [Card.twin_rank]
    exact hr
  intro hf
  unfold freeCardS at hf ⊢
  cases hhold : z.pileHolding d with
  | none => rw [hhold] at hf; exact absurd hf (by simp)
  | some a =>
      simp only [hhold] at hf
      have hmem : d ∈ (z.piles a).faceUp := pileHolding_mem hhold
      have ha0 : a ≠ a0 := by
        intro h
        subst h
        exact hd0 hmem
      have hp_a : z'.piles a = z.piles a := by
        rw [hpiles a, ite_eq_right ha0]
      have hhold' : z'.pileHolding d = some a :=
        (pileHolding_eq_some_iff hz').2 (by rw [hp_a]; exact hmem)
      simp only [hhold']
      have hfrom : fromCard d (z'.piles a).faceUp = fromCard d (z.piles a).faceUp := by
        rw [hp_a]
      have hbelow : below d (z'.piles a).faceUp = below d (z.piles a).faceUp := by
        rw [hp_a]
      have hhidden : (z'.piles a).hidden = (z.piles a).hidden := by
        rw [hp_a]
      rw [hfrom, hbelow, hhidden]
      cases hfc : fromCard d (z.piles a).faceUp with
      | nil => rw [hfc] at hf; exact absurd hf (by simp)
      | cons c0 run =>
          simp only [hfc] at hf ⊢
          rw [Bool.and_eq_true] at hf ⊢
          obtain ⟨hA, hrot⟩ := hf
          refine ⟨hA, ?_⟩
          rw [Bool.or_eq_true] at hrot ⊢
          rcases hrot with hre | his
          · exact Or.inl hre
          · refine Or.inr ?_
            have hne : z.pileOfTop d.twin ≠ none := by
              intro hn
              rw [hn] at his
              exact absurd his (by simp)
            obtain ⟨q, hq⟩ := option_some_of_ne_none hne
            have htop : (z.piles q).top = some d.twin := (pileOfTop_eq_some_iff hz).mp hq
            have hq0 : q ≠ a0 := by
              intro h
              subst h
              exact hdt0 (Pile.mem_of_top htop)
            have htop' : (z'.piles q).top = some d.twin := by
              rw [hpiles q, ite_eq_right hq0]
              exact htop
            have hq' : z'.pileOfTop d.twin = some q :=
              (pileOfTop_eq_some_iff hz').mpr htop'
            show (z'.pileOfTop d.twin).isSome = true
            rw [hq']
            rfl

/-- **`CanRaiseS` is preserved (forward) by a same-rank raise.**  The
foundation gate `nextUp` is untouched because a distinct card of equal
rank has a different suit; the tableau readiness is the previous row. -/
theorem canRaiseS_tabToFound_fwd_of_rank_eq {z z' : State} {e d : Card}
    (hz : z.WF) (hstep : State.step z (Move.tabToFound e) = some z')
    (hde : d ≠ e) (hdt : d.twin ≠ e) (hr : d.rank = e.rank) :
    CanRaiseS z d → CanRaiseS z' d := by
  intro hS
  have hz' : z'.WF := step_wf hz hstep
  rw [canRaiseS_split hz] at hS
  rw [canRaiseS_split hz']
  obtain ⟨hnext, hfree⟩ := hS
  have hsuit : d.suit ≠ e.suit := by
    intro hse
    have hdeq : d = e := by
      cases d with
      | mk ds dr =>
          cases e with
          | mk es er => simp_all
    exact hde hdeq
  have hnext' : z'.nextUp d = true := by
    unfold State.nextUp State.foundHeight at hnext ⊢
    rw [OneColourClosure.found_tabToFound hstep d.suit, ite_eq_right hsuit]
    exact hnext
  exact ⟨hnext', freeCardS_fwd_of_rank_eq hz hstep hde hdt hr hfree⟩

/-- **STEP 1 — `licence_lost_only_by_twin`.**  A `RaiseStepS u u' d`
letter (`CargoPath` then a `tabToFound d`) with `d.rank = c.rank`,
`d ≠ c`, `d ≠ c.twin` preserves `CanRaiseS · c`.

The cargo prefix is an equal-rung orbit move, so the licence transfers
across it (`canRaiseS_orbit_rung`); the raise is the leaf row above. -/
theorem licence_lost_only_by_twin {u u' : State} {d c : Card}
    (hu : u.WF) (hstep : RaiseStepS u u' d)
    (hr : d.rank = c.rank) (hdc : d ≠ c) (hdt : d ≠ c.twin) :
    CanRaiseS u c → CanRaiseS u' c := by
  intro hS
  obtain ⟨z0, hpath, hfire⟩ := hstep
  have hz0 : z0.WF := cargoPath_wf hu hpath
  have horb : sameOrbitSetoid.r u z0 := OneColourClosure.sameOrbit_of_cargoPath hpath
  have hrung : ∀ σ, rungAt u σ = rungAt z0 σ := rungAt_cargoPath hpath
  have h1 : CanRaiseS u c ↔ CanRaiseS z0 c := canRaiseS_orbit_rung hu horb hrung
  exact canRaiseS_tabToFound_fwd_of_rank_eq hz0 hfire hdc.symm hdt.symm hr.symm (h1.mp hS)

/-! ## §2. The pull's landing is a live configuration

A `WF` pull re-founds the pulled card in the tableau with the suit's
rung exactly at its rank index, so it is `nextUp` and vanilla-raisable
at the landing.  These are the two rows the commutation route consumes. -/

/-- **`nextUp` after a pull.**  The pulled card is next-up at the
landing: the rung has dropped from `c.rank.toIdx + 1` to
`c.rank.toIdx`. -/
theorem nextUp_after_pull {F A : State} {c : Card} {b : Base}
    (hF : F.WF) (hstep : State.step F (Move.foundToTab c b) = some A) :
    A.nextUp c = true := by
  obtain ⟨c0, htop0, hc0, -, -⟩ := step_foundToTab_inv hstep
  have htop : F.foundTop c.suit = some c := by
    have h := htop0
    rw [hc0] at h
    exact h
  have hrF : c.rank.toIdx + 1 = rungAt F c.suit :=
    SatDifferCensus.foundTop_rank_succ hF htop
  have hrA : rungAt A c.suit = c.rank.toIdx := by
    have h1 := rungAt_foundToTab hstep c.suit
    rw [ite_eq_left rfl] at h1
    omega
  unfold State.nextUp State.foundHeight
  apply decide_eq_true
  show c.rank.toIdx = (A.found c.suit).length
  exact hrA.symm

/-- **The pull's card is vanilla-raisable at the landing.** -/
theorem canRaise_after_pull {F A : State} {c : Card} {b : Base}
    (hF : F.WF) (hstep : State.step F (Move.foundToTab c b) = some A) :
    CanRaise A c :=
  SatDifferCensus.canRaise_post_of_pull hF hstep (nextUp_after_pull hF hstep)

/-- **The pull's card is S-live at the landing.** -/
theorem canRaiseS_after_pull {F A : State} {c : Card} {b : Base}
    (hF : F.WF) (hstep : State.step F (Move.foundToTab c b) = some A) :
    CanRaiseS A c :=
  CanRaiseS.now c (canRaise_after_pull hF hstep)

end SatDifferConfig

#print axioms SatDifferConfig.not_mem_pileOfTop_of_rank_eq
#print axioms SatDifferConfig.freeCardS_fwd_of_rank_eq
#print axioms SatDifferConfig.canRaiseS_tabToFound_fwd_of_rank_eq
#print axioms SatDifferConfig.licence_lost_only_by_twin
#print axioms SatDifferConfig.nextUp_after_pull
#print axioms SatDifferConfig.canRaise_after_pull
#print axioms SatDifferConfig.canRaiseS_after_pull
