import Orig2.TwinPointNormalize
import Orig2.TwinPointOrbit
import Orig2.TwinDrawTransfer
import Orig2.OrbitFactor
import Orig2.KingSwapAssembly

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# Temp/FiberTransferCapstone — the fiber transfer, conditional on normalization

This capstone assembles the two arms of the `fiber_transfer_corrected`
statement:

* the non-king arm factors a class membership through `sameOrbit_factor`
  into a draw-free board play `s → z` followed by a draw rotation
  `z ↝ s'`, consumes the one normalization hypothesis `SegNormalization x`
  for the board play, and transports `SwappableIn` along `SegPath` and
  the draws;
* the king arm constructs the class vacancy from the swap itself
  (`sameOrbitVacant_of_swappableIn_king`: the witness play moves `x`
  to the twin's seat, and the first seat-changing step exposes an
  empty pile or empties a raised bare king's pile), transports the
  vacancy along the class, and applies the landed vacancy arm at `s'`.

The final theorem dispatches on the rank of `x`; the branch data is
packaged in `FiberSeatData`.  The exact hypothesis list is reported at
the bottom of the file.

Zero `sorry`, zero `Classical.choice`.
-/

/-! ## §1. The normalization hypothesis -/

/-- **`SegNormalization x`** — the one open normalization obligation:
every draw-free board play whose endpoints seat both `x` and `x.twin`
on `.inr` parents is segmented into the `SegPath` grammar. -/
def SegNormalization (x : Card) : Prop :=
  ∀ {s s' : State}, NoDrawPlayW s s' →
    (∃ z, seatOf s x = some (Sum.inr z)) →
    (∃ z : Card, seatOf s x.twin = some (Sum.inr z.twin)) →
    (∃ z, seatOf s' x = some (Sum.inr z)) →
    (∃ z : Card, seatOf s' x.twin = some (Sum.inr z.twin)) →
    ∃ play : List Move, SegPath x s play s'

/-! ## §2. Seats are constant along a draws-only witness play -/

/-- A draws-only witness play keeps every seat verbatim. -/
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

/-- **The non-king transfer, conditional on normalization.**  The class
factor of `s` and `s'` supplies a draw-free board play `s → z`; the
draw rotation `z ↝ s'` supplies the `.inr` seats at `z` (draws keep the
piles).  Normalization segments the board play, `SegPath` carries
`SwappableIn`, and the draw rotation carries it to `s'`. -/
theorem swappableIn_transfer_nonKing_of_normalization
    {s s' : State} {x : Card}
    (hnorm : SegNormalization x)
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
  obtain ⟨play, hseg⟩ := hnorm hnd hxs hxts hzx hzxt
  exact (swappableIn_draw_transfer hrotKeep).mp
    (swappableIn_transfer_segPath hseg hswap)

/-! ## §4. The king arm -/

/-- One reversible step that changes a bare king's seat either has an
empty target pile at its source, or empties the raised king's pile at its
landing.  Either witness is a class-mate of the source. -/
private theorem vacancy_of_seat_change_step
    {u v : State} {m : Move} {c : Card} {a : Anchor}
    (hwf : u.WF) (hstep : State.step u m = some v)
    (hrev : reversibleAtW u m)
    (hking : c.rank = Rank.king)
    (hseat : seatOf u c = some (Sum.inl a))
    (hhid : (u.piles a).hidden = [])
    (hchange : seatOf v c ≠ seatOf u c) :
    ∃ z, sameOrbitSetoid.r u z ∧ HasVacancy z := by
  have hclassStep : sameOrbitSetoid.r u v :=
    RevEqW_symm (shufflePlayW_revEqW (Walk.cons hrev hstep (Walk.nil v)))
  cases m with
  | draw =>
      exact absurd ((chart_draw hstep).1 c) hchange
  | wasteToFound y =>
      obtain ⟨-, y', ys, hw, hv⟩ := step_wasteToFound_inv hstep
      have hp : v.piles = u.piles := by rw [hv]; rfl
      exact absurd (seatOf_congr_piles hp c) hchange
  | wasteToTab y b =>
      exact absurd hrev (wasteToTab_not_reversibleAtW u y b)
  | tabToFound y =>
      by_cases hyc : y = c
      · subst y
        obtain ⟨hnxt, a', hpa, hv⟩ := step_tabToFound_inv hstep
        have hhold : u.pileHolding c = some a := (tfc_seatOf_of_inl hseat).1
        have hmem_a : c ∈ (u.piles a).faceUp := pileHolding_mem hhold
        have hlast : lastOf (u.piles a').faceUp = some c := (tfc_pileOfTop_top hpa).2
        have hmem_a' : c ∈ (u.piles a').faceUp := lastOf_mem hlast
        have haa : a' = a := by
          by_cases h : a' = a
          · exact h
          · exact absurd hmem_a' ((mem_faceUp_unique hwf hmem_a a' h).1)
        have hhid' : (u.piles a').hidden = [] := by rw [haa]; exact hhid
        have hbelow' : below c (u.piles a').faceUp = [] := by
          rw [haa]; exact (tfc_seatOf_of_inl hseat).2
        have hnd : (u.piles a').faceUp.Nodup := runOK_nodup (hwf.2.1 a')
        have hface : (u.piles a').faceUp = [c] :=
          eq_singleton_of_below_nil_lastOf hnd hbelow' hlast
        have hvac : (v.piles a').isEmpty = true :=
          (KingFuel.raise_empties_iff hstep hpa).mpr ⟨hface, hhid'⟩
        exact ⟨v, hclassStep, a', hvac⟩
      · have hse_ne : seatOf u c ≠ none := by rw [hseat]; simp
        have heq : seatOf v c = seatOf u c :=
          raise_seat_change_of_seated hstep hrev hse_ne (fun h => hyc h.symm)
        exact absurd heq hchange
  | foundToTab y b =>
      by_cases hyc : y = c
      · subst y
        obtain ⟨c', htop, hc', hcp, hv⟩ := step_foundToTab_inv hstep
        cases b with
        | inl a' =>
            have hempty : (u.piles a').isEmpty = true := (canPlace_inl hcp).1
            exact ⟨u, sameOrbitSetoid.iseqv.refl u, a', hempty⟩
        | inr z =>
            obtain ⟨k, hz, hfit⟩ := canPlace_inr hcp
            have hfalse : canSitOn c z = false := canSitOn_king_false hking
            rw [hfalse] at hfit
            exact absurd hfit (by simp)
      · have heq : seatOf v c = seatOf u c :=
          pull_seat_change hstep c (fun h => hyc h.symm)
        exact absurd heq hchange
  | tabToTab y b =>
      by_cases hyc : y = c
      · subst y
        obtain ⟨a0, hh, hcp, hfr, hv⟩ := step_tabToTab_inv hstep
        cases b with
        | inl e =>
            have hempty : (u.piles e).isEmpty = true := (canPlace_inl hcp).1
            exact ⟨u, sameOrbitSetoid.iseqv.refl u, e, hempty⟩
        | inr z =>
            obtain ⟨k, hz, hfit⟩ := canPlace_inr hcp
            have hfalse : canSitOn c z = false := canSitOn_king_false hking
            rw [hfalse] at hfit
            exact absurd hfit (by simp)
      · have hed := tfc_seat_point_edit hwf hstep hrev c
        have heq : seatOf v c = seatOf u c := by
          rw [hed, ite_eq_right (fun h : c = y => hyc h.symm)]
        exact absurd heq hchange

/-- Along a witness play, a bare king whose seat changes forces a
vacancy in the class of the play's source. -/
private theorem vacancy_of_walk_change :
    ∀ {u w : State} {play : List Move}, ShufflePlayW u play w →
      ∀ (c : Card) (a : Anchor),
        u.WF → c.rank = Rank.king →
        seatOf u c = some (Sum.inl a) →
        (u.piles a).hidden = [] →
        seatOf w c ≠ seatOf u c →
        ∃ z, sameOrbitSetoid.r u z ∧ HasVacancy z := by
  intro u w play hwalk
  induction hwalk with
  | nil s =>
      intro c a _ _ hseat _ hchange
      exact absurd rfl hchange
  | @cons st mid stEnd m rest hrev hstep hrest ih =>
      intro c a hwf hking hseat hhid hchange
      have hclassStep : sameOrbitSetoid.r st mid :=
        RevEqW_symm (shufflePlayW_revEqW (Walk.cons hrev hstep (Walk.nil mid)))
      by_cases hstepchange : seatOf mid c ≠ seatOf st c
      · exact vacancy_of_seat_change_step hwf hstep hrev hking hseat hhid hstepchange
      · have hmidseat : seatOf mid c = seatOf st c := by
          by_cases h : seatOf mid c = seatOf st c
          · exact h
          · exact absurd h hstepchange
        have hmidne : seatOf stEnd c ≠ seatOf mid c := by
          intro hEq
          exact hchange (hEq.trans hmidseat)
        have hwfmid : mid.WF := step_wf hwf hstep
        have hseatmid : seatOf mid c = some (Sum.inl a) := by
          rw [hmidseat]; exact hseat
        have hhidmid : (mid.piles a).hidden = [] := by
          rw [TwinSpliceComm.hidden_eq_of_rev_step hwf hstep hrev a]; exact hhid
        obtain ⟨z, hcz, hvac⟩ := ih c a hwfmid hking hseatmid hhidmid hmidne
        exact ⟨z, sameOrbitSetoid.iseqv.trans hclassStep hcz, hvac⟩

/-- **The swap forces a class vacancy.**  A bare king pair that is
strictly swappable inside its class cannot live in a vacancy-free
class; constructively, the witness play that moves `x` to the twin's
seat supplies the vacancy. -/
theorem sameOrbitVacant_of_swappableIn_king
    {s : State} {x : Card} {a a' : Anchor}
    (hwf : s.WF) (hking : x.rank = Rank.king)
    (hx : seatOf s x = some (Sum.inl a))
    (hxt : seatOf s x.twin = some (Sum.inl a'))
    (hne : a ≠ a')
    (hhidA : (s.piles a).hidden = [])
    (hswap : SwappableIn s x) :
    SameOrbitVacant s := by
  obtain ⟨v, hstrict, horb⟩ := hswap
  obtain ⟨σ, hσ, τ, hτ⟩ := horb
  have hvx : seatOf v x = some (Sum.inl a') := hstrict.1.trans hxt
  have hchange : seatOf v x ≠ seatOf s x := by
    rw [hvx, hx]
    intro h
    exact hne (Sum.inl.inj (Option.some.inj h)).symm
  exact vacancy_of_walk_change hτ x a hwf hking hx hhidA hchange

/-- **The king transfer.**  The `s`-side bare pair plus `SwappableIn`
constructively force a class vacancy (`sameOrbitVacant_of_swappableIn_king`),
which is transported to `s'` and fed to the landed vacancy arm. -/
theorem swappableIn_transfer_king
    {s s' : State} {x : Card} {a a' b b' : Anchor}
    (hwf : s.WF) (hwf' : s'.WF)
    (hclass : sameOrbitSetoid.r s s')
    (hking : x.rank = Rank.king)
    (hx : seatOf s x = some (Sum.inl a))
    (hxt : seatOf s x.twin = some (Sum.inl a'))
    (hne : a ≠ a')
    (hhidA : (s.piles a).hidden = [])
    (hhidB : (s.piles a').hidden = [])
    (hx' : seatOf s' x = some (Sum.inl b))
    (hxt' : seatOf s' x.twin = some (Sum.inl b'))
    (hne' : b ≠ b')
    (hbareA' : (s'.piles b).faceUp = [x] ∧ (s'.piles b).hidden = [])
    (hbareB' : (s'.piles b').faceUp = [x.twin] ∧ (s'.piles b').hidden = [])
    (hswap : SwappableIn s x) :
    SwappableIn s' x := by
  have hvac : SameOrbitVacant s :=
    sameOrbitVacant_of_swappableIn_king hwf hking hx hxt hne hhidA hswap
  have hvac' : SameOrbitVacant s' := (sameOrbitVacant_iff hclass).mp hvac
  exact swappableIn_king_of_vacancy hwf' hking hx' hxt' hne' hbareA' hbareB' hvac'

/-! ## §5. The dispatch data -/

/-- **`FiberSeatData s s' x`** — the branch data the dispatch consumes.

* non-king branch: all four `.inr` seat witnesses (at `s` and at `s'`);
* king branch: both bare king pairs, at `s` (two `.inl` anchors,
  distinct, empty hidden decks) and at `s'` (two bare singleton piles
  at distinct anchors). -/
def FiberSeatData (s s' : State) (x : Card) : Prop :=
  (x.rank ≠ Rank.king ∧
    (∃ z, seatOf s x = some (Sum.inr z)) ∧
    (∃ z : Card, seatOf s x.twin = some (Sum.inr z.twin)) ∧
    (∃ z, seatOf s' x = some (Sum.inr z)) ∧
    (∃ z : Card, seatOf s' x.twin = some (Sum.inr z.twin))) ∨
  (x.rank = Rank.king ∧
    (∃ a a' : Anchor,
      seatOf s x = some (Sum.inl a) ∧
      seatOf s x.twin = some (Sum.inl a') ∧
      a ≠ a' ∧
      (s.piles a).hidden = [] ∧ (s.piles a').hidden = []) ∧
    ∃ b b' : Anchor,
      seatOf s' x = some (Sum.inl b) ∧
      seatOf s' x.twin = some (Sum.inl b') ∧
      b ≠ b' ∧
      (s'.piles b).faceUp = [x] ∧ (s'.piles b).hidden = [] ∧
      (s'.piles b').faceUp = [x.twin] ∧ (s'.piles b').hidden = [])

/-- The `hseats'` shadow of `FiberSeatData`: both twins are seated at
`s'`. -/
theorem fiberSeatData_seats {s s' : State} {x : Card}
    (h : FiberSeatData s s' x) :
    (∃ z : Base, seatOf s' x = some z) ∧
      (∃ z : Base, seatOf s' x.twin = some z) := by
  rcases h with ⟨-, -, -, hx, hxt⟩ | ⟨-, ⟨a, a', -, -, -, -, -⟩, b, b', hx, hxt, -, -, -, -, -⟩
  · obtain ⟨z, hz⟩ := hx
    obtain ⟨z', hz'⟩ := hxt
    exact ⟨⟨Sum.inr z, hz⟩, ⟨Sum.inr z'.twin, hz'⟩⟩
  · exact ⟨⟨Sum.inl b, hx⟩, ⟨Sum.inl b', hxt⟩⟩

/-! ## §6. The assembled transfer -/

/-- **The fiber transfer, conditional on normalization.**  Dispatch on
`x.rank`: the non-king branch consumes `SegNormalization`, the king
branch consumes the bare pair at `s` (which forces the class vacancy
constructively) and the bare pair at `s'`. -/
theorem fiber_transfer_corrected_of_normalization
    (hnorm : ∀ x : Card, SegNormalization x)
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
    · exact swappableIn_transfer_nonKing_of_normalization (hnorm x) hwf hwf' hclass
        hfound hxs hxts hxs' hxts' hswap
    · exact absurd hking' hking

/-! ## §7. Audit -/

#print axioms sameOrbitVacant_of_swappableIn_king
#print axioms swappableIn_transfer_nonKing_of_normalization
#print axioms swappableIn_transfer_king
#print axioms fiber_transfer_corrected_of_normalization

/-! ## §8. Report — the exact final hypothesis list

The final theorem takes

* `hnorm : ∀ x, SegNormalization x`;
* `s.WF`, `s'.WF`;
* `hclass : sameOrbitSetoid.r s s'` and `hfound : s.found = s'.found`;
* `hswap : SwappableIn s x`;
* `FiberSeatData s s' x`, whose two branches are

  - non-king: `x.rank ≠ Rank.king` and the four `.inr` seat witnesses
    (at `s` and at `s'`); or
  - king: `x.rank = Rank.king`, the bare pair at `s` (two `.inl`
    anchors, distinct, empty hidden decks), and at `s'` the two bare
    singleton king piles `[x]` and `[x.twin]` at distinct `.inl`
    anchors (with empty hidden decks).

`FiberSeatData` implies the requested `hseats'` pair of seat witnesses
(`fiberSeatData_seats`).  The class vacancy needed by the king branch is
*not* an extra hypothesis: `sameOrbitVacant_of_swappableIn_king` derives
`SameOrbitVacant s` from `hswap` and the bare pair at `s`, then
`sameOrbitVacant_iff hclass` transports it to `s'`.

Deviations from the literal task route, and why:

1. The normalization hypothesis is used in the exact factor orientation
   of `sameOrbit_factor` (`NoDrawPlayW s z`, then `SWRotW z s'`).  The
   `.inr` seats at `z` are *derived* from the seats at `s'` and the
   draws-only half of `SWRotW` (draws keep piles), so the segmentation
   predicate is unchanged.
2. The king arm does **not** split on `SameOrbitVacant` with `by_cases`:
   that split introduces `Classical.choice` (verified on a probe),
   violating the house axiom budget.  Instead the positive extraction
   `sameOrbitVacant_of_swappableIn_king` is proved constructively by
   walking the witness play from `s` to the strict target and analyzing
   the first seat-changing reversible step (`vacancy_of_seat_change_step`
   / `vacancy_of_walk_change`).
3. The no-vacancy row `not_swappableIn_king_of_not_vacant`
   (`Orig2/KingSwapAssembly.lean`) and the class-invariance
   `sameOrbitVacant_iff` (`Orig2/KingOrbitFull.lean`) are both available;
   the constructive route above makes the negative arm unnecessary.
4. The king pair data is stronger than `hseats'`: the landed vacancy arm
   needs both twins to bottom singleton piles at distinct anchors with
   empty hidden decks (at `s'`), and the constructive extraction needs
   the `s`-side bare pair (seat anchors and empty hidden decks).  Without
   these, `pileHolding` alone does not identify the anchor/distinctness/
   bareness facts.

Zero `sorry`, zero `Classical.choice`: all three heads print only
`[propext, Quot.sound]`.
-/
