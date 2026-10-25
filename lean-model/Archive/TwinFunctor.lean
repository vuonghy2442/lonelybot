import Orig2.TwinGroupoid
import Orig2.TwinEquivariance
import Orig2.DetourKit

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
