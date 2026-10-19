import Orig2.TwinTransferRiderFree
import Orig2.TwinEquivariance
import Orig2.TwinRelabel

/-!
# Orig2.TwinGroupoid — the tableau subgroupoid and its twin flip

The owner sketch: on the subgroupoid of states where both twins are on the
tableau, the twin flip is an isomorphism, so a swap witness transports
across the flip.  This card formalizes the **rider-free incarnation** of
that groupoid isomorphism; the rider-general flip is the run-splice card.
-/

/-- **TwinBothSeated s x** — the tableau subgroupoid: both twins are
face-up on the tableau at `s`. -/
def TwinBothSeated (s : State) (x : Card) : Prop :=
  (∃ b, seatOf s x = some b) ∧ (∃ b, seatOf s x.twin = some b)

/-- **twinFlip x s** — the rider-free twin flip (the card relabeling).  It is
the identity on the foundations/pool (the twins are on the tableau) and
exchanges the twins' seats. -/
def twinFlip (x : Card) (s : State) : State := State.relabelTwin x s

/-- The flip is an involution on the subgroupoid. -/
theorem twinFlip_involutive (x : Card) (s : State) :
    twinFlip x (twinFlip x s) = s :=
  state_relabelTwin_involutive x s

/-- **The subgroupoid isomorphism on plays.**  A pair-free play between
both-seated states maps to an orbit between the flipped endpoints. -/
theorem twinFlip_play_iso {s t : State} {x : Card} {play : List Move}
    (hwf : s.WF) (hseated : TwinBothSeated s x)
    (hplay : ShufflePlayW s play t)
    (hno : ∀ m ∈ play, NotFoundPair x m) :
    sameOrbitSetoid.r (twinFlip x s) (twinFlip x t) :=
  sameOrbit_relabel_of_play hwf hseated.1 hseated.2 hplay hno

private theorem twinSwapStrict_symm {u v : State} {c : Card}
    (h : twinPairSwapStrict u v c) : twinPairSwapStrict v u c := by
  obtain ⟨h1, h2, h3, hb, hf, hs, hw, hc⟩ := h
  exact ⟨h2.symm, h1.symm, fun y hyz hyt => (h3 y hyz hyt).symm,
    ⟨fun a => (hb.1 a).symm, hb.2.symm⟩,
    fun s => (hf s).symm, hs.symm, hw.symm, hc.symm⟩

/-- **The swap transports across the flip.**  If the strict twin swap of
`⟨x, x.twin⟩` is in-class at a rider-free both-seated `s`, then it is
in-class at the flipped state `twinFlip x s` (with witness `s`). -/
theorem twinFlip_swap_transfer {s : State} {x : Card}
    (hwf : s.WF) (hseated : TwinBothSeated s x)
    (hrx : ∀ y, y ≠ x → seatOf s y ≠ some (Sum.inr x))
    (hrt : ∀ y, y ≠ x.twin → seatOf s y ≠ some (Sum.inr x.twin))
    (hswap : SwappableIn s x) :
    SwappableIn (twinFlip x s) x := by
  obtain ⟨v, hstrict, horb⟩ := hswap
  obtain ⟨σ, hσ, τ, hτ⟩ := horb
  have hvWF : v.WF := run_wf hwf (Walk_run _ hτ)
  have hveq : v = twinFlip x s :=
    eq_relabelTwin_of_twinPairSwapStrict hwf hvWF hseated.1 hseated.2 hrx hrt hstrict
  have hflip : twinPairSwapStrict (twinFlip x s) s x := by
    rw [← hveq]
    exact twinSwapStrict_symm hstrict
  refine ⟨s, hflip, ?_⟩
  have horb' : RevEqW (twinFlip x s) s := by
    rw [← hveq]
    exact ⟨σ, hσ, τ, hτ⟩
  exact RevEqW_symm horb'

#print axioms twinFlip_involutive
#print axioms twinFlip_play_iso
#print axioms twinFlip_swap_transfer
