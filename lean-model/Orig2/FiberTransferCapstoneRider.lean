import Orig2.FiberTransferCapstone
import Orig2.TwinRiderPath
import Orig2.TwinDrawTransfer
import Orig2.OrbitFactor

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# Temp/FiberTransferCapstoneRider — the fiber transfer, conditional on the
rider normalization

This capstone is the rider-general twin of `Orig2/FiberTransferCapstone.lean`.
The one open normalization obligation is weakened from `SegNormalization`
to `RiderNormalization`: the draw-free board play only has to be segmented
into the rider-general `RiderPath` grammar (one twin a pile top per recipe
block), not the rider-free `SegPath` grammar (both twins pile tops).

* the non-king arm factors a class membership through `sameOrbit_factor`
  into a draw-free board play `s → z` followed by a draw rotation
  `z ↝ s'`, consumes `RiderNormalization x` for the board play, transports
  `SwappableIn` along `RiderPath`, and carries it across the draws;
* the king arm is the capstone's king arm verbatim: the bare pair at `s`
  constructively forces a class vacancy, which is transported to `s'` and
  fed to the landed vacancy arm.

Zero `sorry`, zero `Classical.choice`.
-/

/-! ## §1. The rider normalization hypothesis -/

/-- **`RiderNormalization x`** — the open normalization obligation: every
draw-free board play whose endpoints seat both `x` and `x.twin` on `.inr`
parents is segmented into the rider-general `RiderPath` grammar.  This
covers exactly the blocks where **at least one** twin is a pile top; the
excluded residue is the block where both twins carry riders. -/
def RiderNormalization (x : Card) : Prop :=
  ∀ {s s' : State}, NoDrawPlayW s s' →
    (∃ z, seatOf s x = some (Sum.inr z)) →
    (∃ z : Card, seatOf s x.twin = some (Sum.inr z.twin)) →
    (∃ z, seatOf s' x = some (Sum.inr z)) →
    (∃ z : Card, seatOf s' x.twin = some (Sum.inr z.twin)) →
    ∃ play : List Move, RiderPath x s play s'

/-! ## §2. Seats are constant along a draws-only witness play -/

/-- A draws-only witness play keeps every seat verbatim (private copy of the
capstone's lemma; private names do not cross modules). -/
private theorem seatOf_drawPlayW {u v : State} {play : List Move}
    (h : ShufflePlayW u play v) (hdraw : ∀ m ∈ play, m = Move.draw)
    (c : Card) : seatOf v c = seatOf u c := by
  induction h with
  | nil s => rfl
  | @cons st mid stEnd m rest hrev hstep hrest ih =>
      have hm : m = Move.draw := hdraw m (List.mem_cons_self ..)
      subst hm
      have hmid : seatOf mid c = seatOf st c := (chart_draw hstep).1 c
      have htail : seatOf stEnd c = seatOf mid c :=
        ih (fun m' hm' => hdraw m' (List.mem_cons_of_mem _ hm'))
      exact htail.trans hmid

/-! ## §3. The non-king arm -/

/-- **The non-king transfer, conditional on rider normalization.**  The
class factor of `s` and `s'` supplies a draw-free board play `s → z`; the
draw rotation `z ↝ s'` supplies the `.inr` seats at `z` (draws keep the
piles).  `RiderNormalization` segments the board play into a `RiderPath`,
which carries `SwappableIn`, and the draw rotation carries it to `s'`. -/
theorem swappableIn_transfer_nonKing_of_riderNormalization
    {s s' : State} {x : Card}
    (hnorm : RiderNormalization x)
    (hwf : s.WF) (hwf' : s'.WF)
    (hclass : sameOrbitSetoid.r s s')
    (hfound : s.found = s'.found)
    (hxs : ∃ z, seatOf s x = some (Sum.inr z))
    (hxts : ∃ z : Card, seatOf s x.twin = some (Sum.inr z.twin))
    (hxs' : ∃ z, seatOf s' x = some (Sum.inr z))
    (hxts' : ∃ z : Card, seatOf s' x.twin = some (Sum.inr z.twin))
    (hswap : SwappableIn s x) :
    SwappableIn s' x := by
  obtain ⟨zF, hnd, hrot⟩ := (sameOrbit_factor hwf hwf').mp hclass
  have hrotKeep : SWRotW zF s' := hrot
  obtain ⟨σ, _τ, ⟨hσ, hdσ⟩, _hback⟩ := hrot
  have hzx : ∃ z, seatOf zF x = some (Sum.inr z) := by
    obtain ⟨z, hz⟩ := hxs'
    exact ⟨z, (seatOf_drawPlayW hσ hdσ x).symm.trans hz⟩
  have hzxt : ∃ z : Card, seatOf zF x.twin = some (Sum.inr z.twin) := by
    obtain ⟨z, hz⟩ := hxts'
    exact ⟨z, (seatOf_drawPlayW hσ hdσ x.twin).symm.trans hz⟩
  obtain ⟨play, hpath⟩ := hnorm hnd hxs hxts hzx hzxt
  exact (swappableIn_draw_transfer hrotKeep).mp
    (swappableIn_transfer_riderPath hpath hswap)

/-! ## §4. The dispatch data and the assembled transfer -/

/-- **The fiber transfer, conditional on the rider normalization.**
Dispatch on `x.rank`: the non-king branch consumes `RiderNormalization`,
the king branch consumes the capstone's `FiberSeatData` king parcel and
reuses `swappableIn_transfer_king` verbatim. -/
theorem fiber_transfer_corrected_of_riderNormalization
    (hnorm : ∀ x : Card, RiderNormalization x)
    {s s' : State} (hwf : s.WF) (hwf' : s'.WF) {x : Card}
    (hclass : sameOrbitSetoid.r s s') (hfound : s.found = s'.found)
    (hswap : SwappableIn s x)
    (hdata : FiberSeatData s s' x) :
    SwappableIn s' x := by
  by_cases hking : x.rank = Rank.king
  · rcases hdata with ⟨hnk, -⟩ |
      ⟨-, ⟨a, a', hx, hxt, hne, hhidA, hhidB⟩, b, b', hx', hxt', hne', hfa, hha, hfb, hhb⟩
    · exact absurd hking hnk
    · exact swappableIn_transfer_king hwf hwf' hclass hking
        hx hxt hne hhidA hhidB hx' hxt' hne' ⟨hfa, hha⟩ ⟨hfb, hhb⟩ hswap
  · rcases hdata with ⟨-, hxs, hxts, hxs', hxts'⟩ | ⟨hking', -⟩
    · exact swappableIn_transfer_nonKing_of_riderNormalization (hnorm x) hwf hwf'
        hclass hfound hxs hxts hxs' hxts' hswap
    · exact absurd hking' hking

/-! ## §5. Audit -/

#print axioms swappableIn_transfer_nonKing_of_riderNormalization
#print axioms fiber_transfer_corrected_of_riderNormalization

/-! ## §6. Report

The final theorem takes

* `hnorm : ∀ x, RiderNormalization x`;
* `s.WF`, `s'.WF`;
* `hclass : sameOrbitSetoid.r s s'` and `hfound : s.found = s'.found`;
* `hswap : SwappableIn s x`;
* `hdata : FiberSeatData s s' x` (the capstone's dispatch parcel: in the
  non-king branch the four `.inr` seat witnesses at `s` and `s'`; in the
  king branch the two bare king pairs).

`RiderNormalization` excludes only the blocks where **both** twins carry
riders (neither is a pile top): those are not recipe ends of `RiderPath`,
and they need the 5L/7L prelude/ladder layer to expose a top first.  Every
other draw-free block is covered by the rider-general recipe segments
(`RiderRecipeTwin` / `RiderRecipeSelf`) and pair-free legs.

Zero `sorry`, zero `Classical.choice`: both heads print only
`[propext, Quot.sound]`.
-/
