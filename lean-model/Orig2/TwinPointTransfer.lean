import Orig2.DetourKit
import Orig2.Integrity
import Orig2.TwinEquivariance
import Orig2.TwinRelabel
import Orig2.TwinSplice
import Orig2.TwinSpliceWF
import Orig2.TwinSwapUnique

/-!
# Orig2.TwinPointTransfer — the point-object stack (merged)

The point-transfer and everything it rides, in one file: the
rider-free transfer row (`TwinTransferRiderFree`), the tableau
subgroupoid and twin flip (`TwinGroupoid`), the twin functor
(`TwinFunctor`), the point functor (`TwinPointFunctor`), the splice
uniqueness (`TwinSpliceUnique`), and the point transfer itself —
six short cards merged per the owner's file-count directive, each
section keeping its original docstrings and batteries verbatim.
-/


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


/-!
# Orig2.TwinGroupoid — the tableau subgroupoid and its twin flip

The owner sketch: on the subgroupoid of states where both twins are on the
tableau, the twin flip is an isomorphism, so a swap witness transports
across the flip.

THE LOCAL FLIP IS A RELATION, not a global card relabeling:
`LocalTwinFlip x s v := twinPairSwapStrict s v x` — two states differing
only in the pair's seats (and the fixed board/founds/pool).  The global
`twinFlip` (card relabeling) is its rider-free implementation; the run
splice `localTwinFlip` is the rider-general implementation.
-/

/-- **The local twin flip relation**: `s` and `v` differ by the strict twin
swap of `⟨x, x.twin⟩`. -/
def LocalTwinFlip (x : Card) (s v : State) : Prop := twinPairSwapStrict s v x

/-- **The local twin flip function** (rider-general implementation): swap
the two runs rooted at the twins. -/
def localTwinFlip (x : Card) (s : State) : State := State.spliceTwinRuns x s

private theorem twinSwapStrict_symm {u v : State} {c : Card}
    (h : twinPairSwapStrict u v c) : twinPairSwapStrict v u c := by
  obtain ⟨h1, h2, h3, hb, hf, hs, hw, hc⟩ := h
  exact ⟨h2.symm, h1.symm, fun y hyz hyt => (h3 y hyz hyt).symm,
    ⟨fun a => (hb.1 a).symm, hb.2.symm⟩,
    fun s => (hf s).symm, hs.symm, hw.symm, hc.symm⟩

/-- The local flip relation is symmetric. -/
theorem LocalTwinFlip_symm {x : Card} {s v : State}
    (h : LocalTwinFlip x s v) : LocalTwinFlip x v s :=
  twinSwapStrict_symm h

/-- The run splice realizes the local flip relation (both twins on
parents). -/
theorem twinPairSwapStrict_localTwinFlip {s : State} {x : Card}
    (hwf : s.WF)
    (hx : ∃ z, seatOf s x = some (Sum.inr z))
    (hxt : ∃ z : Card, seatOf s x.twin = some (Sum.inr z.twin)) :
    LocalTwinFlip x s (localTwinFlip x s) :=
  twinPairSwapStrict_splice hwf hx hxt

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


/-!
# Orig2.TwinFunctor — the rider-free twin flip as a tableau-groupoid isomorphism

The twin flip is an automorphism of the pair-free tableau subgroupoid.  This
card packages it as an object/morphism map and records the transfer corollary.

The local/rider-general version replaces `twinFlip` by `localTwinFlip`
(the run splice) once the local commutation lands.
-/

/-- The tableau subgroupoid where both twins are seated. -/
def TwinObj (x : Card) : Type :=
  { s : State // s.WF ∧ TwinBothSeated s x }

/-- Pair-free witness shuffles between both-seated states. -/
def TwinHom (x : Card) (s t : TwinObj x) : Prop :=
  ∃ play : List Move, ShufflePlayW s.1 play t.1 ∧
    ∀ m ∈ play, NotFoundPair x m

/-- The rider-free twin flip on objects. -/
def twinObjFlip (x : Card) : TwinObj x → TwinObj x := fun s =>
  ⟨twinFlip x s.1,
    by simpa [twinFlip] using wf_relabelTwin s.2.1 s.2.2.1 s.2.2.2,
    ⟨by
       simpa [twinFlip, state_relabelTwin_seat_x s.2.1] using s.2.2.2,
     by
       simpa [twinFlip, state_relabelTwin_seat_twin s.2.1] using s.2.2.1⟩⟩

/-- A pair-free move stays pair-free after the twin relabeling. -/
theorem notFoundPair_relabelTwin {x : Card} {m : Move}
    (h : NotFoundPair x m) :
    NotFoundPair x (Move.relabelTwin x m) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  cases m with
  | draw => simp [Move.relabelTwin, NotFoundPair]
  | wasteToFound c => simp [Move.relabelTwin, NotFoundPair]
  | wasteToTab c b => simp [Move.relabelTwin, NotFoundPair]
  | tabToFound c =>
      have hcx : c ≠ x := fun hc => h1 (by rw [hc])
      have hct : c ≠ x.twin := fun hc => h2 (by rw [hc])
      have hrel : Card.relabelTwin x c = c := card_relabelTwin_ne hcx hct
      simp [Move.relabelTwin, NotFoundPair, hrel, hcx, hct]
  | foundToTab c b =>
      have hcx : c ≠ x := fun hc => h3 b (by rw [hc])
      have hct : c ≠ x.twin := fun hc => h4 b (by rw [hc])
      have hrel : Card.relabelTwin x c = c := card_relabelTwin_ne hcx hct
      refine ⟨by simp [Move.relabelTwin], by simp [Move.relabelTwin], ?_, ?_⟩
      · intro b' hb'
        injection hb' with hc hb
        exact hcx (hrel.symm.trans hc)
      · intro b' hb'
        injection hb' with hc hb
        exact hct (hrel.symm.trans hc)
  | tabToTab c b => simp [Move.relabelTwin, NotFoundPair]

/-- The explicit-play strengthening of `sameOrbit_relabel_of_play`. -/
theorem relabelPlay {s t : State} {x : Card} {play : List Move}
    (hwf : s.WF) (hseated : TwinBothSeated s x)
    (hplay : ShufflePlayW s play t)
    (hno : ∀ m ∈ play, NotFoundPair x m) :
    ShufflePlayW (twinFlip x s) (play.map (Move.relabelTwin x)) (twinFlip x t) := by
  simpa [twinFlip] using
    shufflePlayW_relabel_of_no_pair hplay hwf hseated.1 hseated.2 hno

/-- The relabeled play stays pair-free. -/
theorem relabelPlay_notFoundPair {x : Card} {play : List Move}
    (hno : ∀ m ∈ play, NotFoundPair x m) :
    ∀ m' ∈ play.map (Move.relabelTwin x), NotFoundPair x m' := by
  induction play with
  | nil => simp
  | cons m rest ih =>
      intro m' hm'
      rw [List.map_cons] at hm'
      rcases List.mem_cons.mp hm' with rfl | hm'
      · exact notFoundPair_relabelTwin (hno m (List.mem_cons_self ..))
      · exact ih (fun m hm => hno m (List.mem_cons_of_mem _ hm)) m' hm'

/-- Functoriality: pair-free homomorphisms map to pair-free homomorphisms. -/
theorem twinObjFlip_hom {x : Card} {s t : TwinObj x}
    (h : TwinHom x s t) :
    TwinHom x (twinObjFlip x s) (twinObjFlip x t) := by
  obtain ⟨play, hplay, hno⟩ := h
  refine ⟨play.map (Move.relabelTwin x), ?_, ?_⟩
  · exact relabelPlay s.2.1 s.2.2 hplay hno
  · exact relabelPlay_notFoundPair hno

/-- The flip is an involution on objects. -/
theorem twinObjFlip_involutive (x : Card) (s : TwinObj x) :
    twinObjFlip x (twinObjFlip x s) = s := by
  apply Subtype.ext
  exact twinFlip_involutive x s.1

/-- Transfer corollary: `SwappableIn` transports along a pair-free play. -/
theorem twinFunctor_swappableIn {x : Card} {s t : TwinObj x}
    (h : TwinHom x s t)
    (hrx : ∀ y, y ≠ x → seatOf s.1 y ≠ some (Sum.inr x))
    (hrt : ∀ y, y ≠ x.twin → seatOf s.1 y ≠ some (Sum.inr x.twin))
    (hrx' : ∀ y, y ≠ x → seatOf t.1 y ≠ some (Sum.inr x))
    (hrt' : ∀ y, y ≠ x.twin → seatOf t.1 y ≠ some (Sum.inr x.twin))
    (hswap : SwappableIn s.1 x) :
    SwappableIn t.1 x := by
  obtain ⟨play, hplay, hno⟩ := h
  exact swappableIn_transfer_of_seated_riderFree s.2.1 t.2.1
    s.2.2.1 s.2.2.2 t.2.2.1 t.2.2.2 hrx hrt hrx' hrt' hplay hno hswap

#print axioms relabelPlay
#print axioms twinObjFlip_hom
#print axioms twinObjFlip_involutive
#print axioms twinFunctor_swappableIn


set_option linter.unusedSectionVars false

/-!
# Temp/TwinPointFunctor — the object-level point-swap functor

Both twins seated on card parents (`.inr` seats).  The run splice is an
involution on this subtype, so the point-swap is an object-level
involution of the twin tableau groupoid.

Zero `sorry`, zero `Classical.choice`.
-/

open State

/-- Both twins on card parents: `x` sits on some card and `x.twin` sits
on a card of twin shape. -/
def TwinObjInr (x : Card) : Type :=
  {s : State // s.WF ∧ (∃ z : Card, seatOf s x = some (Sum.inr z)) ∧
    (∃ z : Card, seatOf s x.twin = some (Sum.inr z.twin))}

/-- The object map: swap the two face-up runs rooted at the twins. -/
def pointObjFlip (x : Card) : TwinObjInr x → TwinObjInr x := fun s =>
  ⟨s.1.spliceTwinRuns x, by
    have hstrict := twinPairSwapStrict_splice s.2.1 s.2.2.1 s.2.2.2
    refine ⟨wf_spliceTwinRuns s.2.1 s.2.2.1 s.2.2.2, ?_, ?_⟩
    · obtain ⟨z, hz⟩ := s.2.2.2
      exact ⟨z.twin, by rw [hstrict.1, hz]⟩
    · obtain ⟨z, hz⟩ := s.2.2.1
      exact ⟨z.twin, by rw [hstrict.2.1, hz, card_twin_twin]⟩⟩

/-! ## §1. Holding pins after the first splice -/

private theorem holding_splice_self {st : State} {x : Card} {a b : Anchor}
    (hwf : st.WF)
    (ha : st.pileHolding x = some a) (hb : st.pileHolding x.twin = some b)
    (hab : a ≠ b) :
    (st.spliceTwinRuns x).pileHolding x = some b := by
  have hxmem : x ∈ (st.piles a).faceUp := pileHolding_mem ha
  have hxB : x ∉ (st.piles b).faceUp :=
    (mem_faceUp_unique hwf hxmem b (Ne.symm hab)).1
  obtain ⟨rA, hrunA⟩ := tfc_fromCard_cons_head (c := x) _ hxmem
  refine tfc_pileHolding_pin ?_ ?_
  · rw [spliceTwinRuns_piles_second ha hb hab]
    exact List.mem_append.mpr
      (Or.inr (by rw [hrunA]; exact List.mem_cons_self))
  · intro j hj
    by_cases hja : j = a
    · subst hja
      rw [spliceTwinRuns_piles_self ha hb hab]
      intro hm
      rcases List.mem_append.mp hm with hpre | hrun
      · exact tfc_below_not_mem_self x _ hpre
      · exact hxB (tfc_mem_fromCard _ hrun)
    · rw [spliceTwinRuns_piles_other ha hb hab hja hj]
      exact (mem_faceUp_unique hwf hxmem j hja).1

private theorem holding_splice_twin {st : State} {x : Card} {a b : Anchor}
    (hwf : st.WF)
    (ha : st.pileHolding x = some a) (hb : st.pileHolding x.twin = some b)
    (hab : a ≠ b) :
    (st.spliceTwinRuns x).pileHolding x.twin = some a := by
  have htmem : x.twin ∈ (st.piles b).faceUp := pileHolding_mem hb
  have htA : x.twin ∉ (st.piles a).faceUp :=
    (mem_faceUp_unique hwf htmem a hab).1
  obtain ⟨rB, hrunB⟩ := tfc_fromCard_cons_head (c := x.twin) _ htmem
  refine tfc_pileHolding_pin ?_ ?_
  · rw [spliceTwinRuns_piles_self ha hb hab]
    exact List.mem_append.mpr
      (Or.inr (by rw [hrunB]; exact List.mem_cons_self))
  · intro j hj
    by_cases hjb : j = b
    · subst hjb
      rw [spliceTwinRuns_piles_second ha hb hab]
      intro hm
      rcases List.mem_append.mp hm with hpre | hrun
      · exact tfc_below_not_mem_self x.twin _ hpre
      · exact htA (tfc_mem_fromCard _ hrun)
    · rw [spliceTwinRuns_piles_other ha hb hab hj hjb]
      exact (mem_faceUp_unique hwf htmem j hjb).1

/-! ## §2. The run-splice involution -/

/-- Swapping the two runs twice restores the state. -/
theorem spliceTwinRuns_invol {s : State} {x : Card} (hwf : s.WF)
    (hx : ∃ z, seatOf s x = some (Sum.inr z))
    (hxt : ∃ z : Card, seatOf s x.twin = some (Sum.inr z.twin)) :
    (s.spliceTwinRuns x).spliceTwinRuns x = s := by
  obtain ⟨z, hz⟩ := hx
  obtain ⟨a, ha, -, -⟩ := tfc_seatOf_of_inr hz
  obtain ⟨w, hw⟩ := hxt
  obtain ⟨b, hb, -, -⟩ := tfc_seatOf_of_inr hw
  by_cases hab : a = b
  · subst hab
    rw [spliceTwinRuns_of_eq ha hb, spliceTwinRuns_of_eq ha hb]
  · have hxmem : x ∈ (s.piles a).faceUp := pileHolding_mem ha
    have htmem : x.twin ∈ (s.piles b).faceUp := pileHolding_mem hb
    have hxB : x ∉ (s.piles b).faceUp :=
      (mem_faceUp_unique hwf hxmem b (Ne.symm hab)).1
    have htA : x.twin ∉ (s.piles a).faceUp :=
      (mem_faceUp_unique hwf htmem a hab).1
    obtain ⟨rA, hrunA⟩ := tfc_fromCard_cons_head (c := x) _ hxmem
    obtain ⟨rB, hrunB⟩ := tfc_fromCard_cons_head (c := x.twin) _ htmem
    have hholdx : (s.spliceTwinRuns x).pileHolding x = some b :=
      holding_splice_self hwf ha hb hab
    have hholdt : (s.spliceTwinRuns x).pileHolding x.twin = some a :=
      holding_splice_twin hwf ha hb hab
    have hxB' : x ∉ below x.twin (s.piles b).faceUp :=
      fun h => hxB (mem_below _ h)
    have htA' : x.twin ∉ below x (s.piles a).faceUp :=
      fun h => htA (mem_below _ h)
    have hbelowA : below x (fromCard x (s.piles a).faceUp) = [] := by
      rw [hrunA, below_cons, ite_eq_left rfl]
    have hbelowB : below x.twin (fromCard x.twin (s.piles b).faceUp) = [] := by
      rw [hrunB, below_cons, ite_eq_left rfl]
    have hfromA : fromCard x (fromCard x (s.piles a).faceUp) =
        fromCard x (s.piles a).faceUp := by
      rw [hrunA, fromCard_head_eq]
    have hfromB : fromCard x.twin (fromCard x.twin (s.piles b).faceUp) =
        fromCard x.twin (s.piles b).faceUp := by
      rw [hrunB, fromCard_head_eq]
    have hbelow1 : below x (below x.twin (s.piles b).faceUp ++
        fromCard x (s.piles a).faceUp) = below x.twin (s.piles b).faceUp := by
      rw [(tfc_below_fromCard_excl x (below x.twin (s.piles b).faceUp)
        (fromCard x (s.piles a).faceUp) hxB').1, hbelowA, List.append_nil]
    have hfrom1 : fromCard x.twin (below x (s.piles a).faceUp ++
        fromCard x.twin (s.piles b).faceUp) =
        fromCard x.twin (s.piles b).faceUp := by
      rw [(tfc_below_fromCard_excl x.twin (below x (s.piles a).faceUp)
        (fromCard x.twin (s.piles b).faceUp) htA').2, hfromB]
    have hbelow2 : below x.twin (below x (s.piles a).faceUp ++
        fromCard x.twin (s.piles b).faceUp) = below x (s.piles a).faceUp := by
      rw [(tfc_below_fromCard_excl x.twin (below x (s.piles a).faceUp)
        (fromCard x.twin (s.piles b).faceUp) htA').1, hbelowB, List.append_nil]
    have hfrom2 : fromCard x (below x.twin (s.piles b).faceUp ++
        fromCard x (s.piles a).faceUp) =
        fromCard x (s.piles a).faceUp := by
      rw [(tfc_below_fromCard_excl x (below x.twin (s.piles b).faceUp)
        (fromCard x (s.piles a).faceUp) hxB').2, hfromA]
    have hfaceA : (((s.spliceTwinRuns x).spliceTwinRuns x).piles a).faceUp =
        (s.piles a).faceUp := by
      rw [spliceTwinRuns_piles_second hholdx hholdt (Ne.symm hab)]
      rw [spliceTwinRuns_piles_self ha hb hab,
        spliceTwinRuns_piles_second ha hb hab]
      simp only
      rw [hbelow2, hfrom2]
      exact tfc_below_fromCard x (s.piles a).faceUp
    have hfaceB : (((s.spliceTwinRuns x).spliceTwinRuns x).piles b).faceUp =
        (s.piles b).faceUp := by
      rw [spliceTwinRuns_piles_self hholdx hholdt (Ne.symm hab)]
      rw [spliceTwinRuns_piles_second ha hb hab,
        spliceTwinRuns_piles_self ha hb hab]
      simp only
      rw [hbelow1, hfrom1]
      exact tfc_below_fromCard x.twin (s.piles b).faceUp
    have hhiddenA : (((s.spliceTwinRuns x).spliceTwinRuns x).piles a).hidden =
        (s.piles a).hidden := by
      rw [spliceTwinRuns_piles_second hholdx hholdt (Ne.symm hab)]
      rw [spliceTwinRuns_piles_self ha hb hab]
    have hhiddenB : (((s.spliceTwinRuns x).spliceTwinRuns x).piles b).hidden =
        (s.piles b).hidden := by
      rw [spliceTwinRuns_piles_self hholdx hholdt (Ne.symm hab)]
      rw [spliceTwinRuns_piles_second ha hb hab]
    have hpiles : ((s.spliceTwinRuns x).spliceTwinRuns x).piles = s.piles := by
      funext j
      by_cases hja : j = a
      · subst hja
        exact Pile.ext hhiddenA hfaceA
      · by_cases hjb : j = b
        · subst hjb
          exact Pile.ext hhiddenB hfaceB
        · rw [spliceTwinRuns_piles_other hholdx hholdt (Ne.symm hab) hjb hja,
            spliceTwinRuns_piles_other ha hb hab hja hjb]
    apply State.ext
    · rw [spliceTwinRuns_found hholdx hholdt (Ne.symm hab),
        spliceTwinRuns_found ha hb hab]
    · exact hpiles
    · rw [spliceTwinRuns_stock hholdx hholdt (Ne.symm hab),
        spliceTwinRuns_stock ha hb hab]
    · rw [spliceTwinRuns_waste hholdx hholdt (Ne.symm hab),
        spliceTwinRuns_waste ha hb hab]
    · rw [spliceTwinRuns_drawStep hholdx hholdt (Ne.symm hab),
        spliceTwinRuns_drawStep ha hb hab]

/-! ## §3. The object involution -/

/-- The point-swap is an involution on the both-on-parents subtype. -/
theorem pointObjFlip_involutive (x : Card) (s : TwinObjInr x) :
    pointObjFlip x (pointObjFlip x s) = s := by
  apply Subtype.ext
  exact spliceTwinRuns_invol s.2.1 s.2.2.1 s.2.2.2

/-! ## §4. Audit -/

#print axioms spliceTwinRuns_invol
#print axioms pointObjFlip_involutive


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


set_option linter.unusedSectionVars false

/-!
# Temp/TwinPointTransfer — the pair-free transfer of `SwappableIn`

The point object `s.spliceTwinRuns x` carries the swap of `x` and
`x.twin`; by `swappableIn_iff_orbit_splice`, `SwappableIn s x` is
exactly the orbit of that object at `s`.  A witness play `s → t` gives
`sameOrbitSetoid.r t s`, and the point-hom hypothesis
`sameOrbitSetoid.r (s.spliceTwinRuns x) (t.spliceTwinRuns x)` supplies
the corresponding orbit at `t`.  Transitivity of the reversible quotient
then yields `SwappableIn t x`.

Zero `sorry`, zero `Classical.choice`.
-/

open State

/-- **The pair-free point transfer.**  `SwappableIn` transfers along a
pair-free reversible play, given that the two run splices are in the
same orbit. -/
theorem swappableIn_transfer_point_pairFree
    {s t : State} {x : Card} {play : List Move}
    (hwf : s.WF) (hwf' : t.WF)
    (hxs : ∃ z, seatOf s x = some (Sum.inr z))
    (hxts : ∃ z : Card, seatOf s x.twin = some (Sum.inr z.twin))
    (hxt : ∃ z, seatOf t x = some (Sum.inr z))
    (hxtt : ∃ z : Card, seatOf t x.twin = some (Sum.inr z.twin))
    (hplay : ShufflePlayW s play t)
    (_hno : ∀ m ∈ play, NotFoundPair x m)
    (hpoint : sameOrbitSetoid.r (s.spliceTwinRuns x) (t.spliceTwinRuns x))
    (hswap : SwappableIn s x) :
    SwappableIn t x := by
  have h1 : sameOrbitSetoid.r s (s.spliceTwinRuns x) :=
    (swappableIn_iff_orbit_splice hwf hxs hxts).mp hswap
  have h2 : sameOrbitSetoid.r t s := shufflePlayW_revEqW hplay
  have h3 : sameOrbitSetoid.r t (s.spliceTwinRuns x) :=
    RevEqW_trans h1 h2
  have h4 : sameOrbitSetoid.r t (t.spliceTwinRuns x) :=
    RevEqW_trans hpoint h3
  exact (swappableIn_iff_orbit_splice hwf' hxt hxtt).mpr h4

#print axioms swappableIn_transfer_point_pairFree
