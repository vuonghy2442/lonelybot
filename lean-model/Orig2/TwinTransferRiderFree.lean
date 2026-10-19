import Orig2.TwinEquivariance
import Orig2.TwinSwapUnique

/-!
# Orig2.TwinTransferRiderFree — the rider-free both-seated transfer

`SwappableIn` is the existential strict-swap predicate.  At a rider-free pair,
the strict-swap target is exactly the relabeling state (`TwinSwapUnique`), so
the relabeling equivariance (`TwinEquivariance`) gives the transfer:

  same orbit + both twins rider-free and seated + the play never raises/pulls
  a twin  =>  SwappableIn transfers.

The pair-foundation detour is deliberately excluded here; that is the next
card's content.
-/

/-- **Rider-free both-seated transfer.**  If the twins are rider-free and
seated at `s` and `s'`, the play from `s` to `s'` never raises or pulls a
twin, and the strict twin swap is in-class at `s`, then it is in-class at
`s'`. -/
theorem swappableIn_transfer_of_seated_riderFree
    {s s' : State} {x : Card} {play : List Move}
    (hwf : s.WF) (hwf' : s'.WF)
    (hx : ∃ b, seatOf s x = some b) (hxt : ∃ b, seatOf s x.twin = some b)
    (hx' : ∃ b, seatOf s' x = some b) (hxt' : ∃ b, seatOf s' x.twin = some b)
    (hrx : ∀ y, y ≠ x → seatOf s y ≠ some (Sum.inr x))
    (hrt : ∀ y, y ≠ x.twin → seatOf s y ≠ some (Sum.inr x.twin))
    (hrx' : ∀ y, y ≠ x → seatOf s' y ≠ some (Sum.inr x))
    (hrt' : ∀ y, y ≠ x.twin → seatOf s' y ≠ some (Sum.inr x.twin))
    (hplay : ShufflePlayW s play s')
    (hno : ∀ m ∈ play, NotFoundPair x m)
    (hswap : SwappableIn s x) :
    SwappableIn s' x := by
  obtain ⟨v, hstrict, horb⟩ := hswap
  obtain ⟨σ, hσ, τ, hτ⟩ := horb
  have hvWF : v.WF := run_wf hwf (Walk_run _ hτ)
  have hveq : v = State.relabelTwin x s :=
    eq_relabelTwin_of_twinPairSwapStrict hwf hvWF hx hxt hrx hrt hstrict
  have hrel : sameOrbitSetoid.r s (State.relabelTwin x s) := by
    rw [← hveq]
    exact ⟨σ, hσ, τ, hτ⟩
  exact swappableIn_transfer_seated_riderFree hwf hwf' hx hxt hx' hxt'
    hrx hrt hrx' hrt' hrel hplay hno

#print axioms swappableIn_transfer_of_seated_riderFree
