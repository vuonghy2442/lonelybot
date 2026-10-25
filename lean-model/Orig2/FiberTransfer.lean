import Orig2.Kit
import Orig2.Chart
import Orig2.Integrity
import Orig2.StepWF
import Orig2.CargoKit
import Orig2.Classification
import Orig2.SeatMateStack
import Orig2.DetourKit
import Orig2.TwinEquivariance
import Orig2.TwinSpliceComm
import Orig2.TwinPointTransfer
import Orig2.TwinSwapRecipe
import Orig2.PairClassSeed

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 2000000

/-!
# Orig2.FiberTransfer — the consolidated corrected fiber transfer

The owner's last-return route in ONE card.  This is the whole proof:

* `fiber_transfer_corrected_of_lastReturn` — **THE CORRECTED FIBER
  TRANSFER** (the `.inr`-seat grade): swap availability transfers along
  the class.
* `firstTouchRestart` — the `FirstTouchRestart` residual, proved: the
  excursion is never entered; the swap is RECONSTRUCTED at the last
  return.
* `swappableIn_transfer_of_pairFreePath` /
  `fiber_transfer_corrected_of_pairFreePath` — the pair-free transfer
  (the stepping-stone the reduction consumes).
* `seat_inr_of_swappable_nonking` — **THE OWNER'S SEAT LEMMA** (§8,
  fresh 2026-10-25): a swappable non-king pair that is seated at all
  sits on card parents — the wedge for the OPEN original statement.

The card rides ONLY the certified tracked substrate (the fifteen
imports above).  Every row restated from the retired dependency cards
carries its source citation, per the per-file private-kit norm:

* §1 — `PairFreeOrbit` and its kit (restated from
  `Orig2/TwinPairFreeClass.lean`), the splice functor
  `pairFreeOrbit_splice_of_pairFree` and `notFoundPair_relabelMover`
  (restated from `Orig2/TwinLastPull.lean:75,201`).
* §2 — the foundation arithmetic `upCards_nodup`,
  `posOf_take_of_mem`, `posOf_last_eq_length_sub_one`,
  `found_chop_length_eq_rank` (restated from
  `Orig2/TwinPairFreeRev.lean:43–135`).
* §3 — the self-arming keystone `nextUp_of_foundToTab`,
  `reversibleAtW_tabToFound_of_foundToTab` (restated from
  `Orig2/TwinSelfArm.lean`).
* §5 — the seat & parent kit: `walk_cons_inv`,
  `seatOf_none_of_mem_found` (from `Orig2/TwinForcedCancel.lean`),
  `raise_found_self`, `seated_inr_rank_ne_king` (from
  `Orig2/TwinFoundationRow.lean`), `canSitOn_twin_left'`,
  `not_twin_same_parent`, `twin_parent_eq_of_seats` (from
  `Orig2/TwinPreludeFunctor.lean`), and the two foundation-membership
  rows of §7 (`found_mem_step` from `Orig2/TwinAttShapes.lean:1026`,
  `found_mem_play_of_not_pull` from
  `Orig2/TwinExcursionClosure.lean:832`).

The four-card arc this consolidates (`TwinPairFreeTransfer`,
`TwinFirstTouchReduction`, `TwinSelfArm`, `TwinLastReturn`) and the
thirteen dependency cards whose rows are restated here are retired to
`Archive/`.

Zero `sorry`, zero `Classical.choice`, no new axioms.
-/

open State

/-! ## §1. Pair-free kit (restated from `Orig2/TwinPairFreeClass.lean`
and `Orig2/TwinLastPull.lean` — the per-file kit norm) -/

/-- **`PairFreeOrbit x u v`** — `v` is reachable from `u` by a witness
shuffle that never raises or pulls either twin.
(restated from `Orig2/TwinPairFreeClass.lean:55` — the per-file kit norm) -/
private def PairFreeOrbit (x : Card) (u v : State) : Prop :=
  ∃ play : List Move, ShufflePlayW u play v ∧ ∀ m ∈ play, NotFoundPair x m

/-- The empty play is pair-free.
(restated from `Orig2/TwinPairFreeClass.lean:60` — the per-file kit norm) -/
private theorem pairFreeOrbit_refl (x : Card) (u : State) :
    PairFreeOrbit x u u :=
  ⟨[], Walk.nil u, by simp⟩

/-- Pair-free orbits compose by concatenating the plays.
(restated from `Orig2/TwinPairFreeClass.lean:65` — the per-file kit norm) -/
private theorem PairFreeOrbit.trans {x : Card} {u v w : State}
    (h₁ : PairFreeOrbit x u v) (h₂ : PairFreeOrbit x v w) :
    PairFreeOrbit x u w := by
  obtain ⟨p, hp, hnp⟩ := h₁
  obtain ⟨q, hq, hnq⟩ := h₂
  exact ⟨p ++ q, ShufflePlayW_append hp hq, by
    intro m hm
    rcases List.mem_append.mp hm with hm | hm
    · exact hnp m hm
    · exact hnq m hm⟩

/-- A concrete pair-free shuffle is a `PairFreeOrbit` row.
(restated from `Orig2/TwinPairFreeClass.lean:77` — the per-file kit norm) -/
private theorem pairFreeOrbit_of_play {x : Card} {u v : State} {play : List Move}
    (hplay : ShufflePlayW u play v)
    (hno : ∀ m ∈ play, NotFoundPair x m) :
    PairFreeOrbit x u v :=
  ⟨play, hplay, hno⟩

/-- A pair-free move stays pair-free after relabelling its mover.
(restated from `Orig2/TwinLastPull.lean:75` — the per-file kit norm) -/
private theorem notFoundPair_relabelMover {x : Card} {m : Move}
    (h : NotFoundPair x m) : NotFoundPair x (Move.relabelMover x m) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  cases m with
  | draw => simp [Move.relabelMover, NotFoundPair]
  | wasteToFound c => simp [Move.relabelMover, NotFoundPair]
  | wasteToTab c b => simp [Move.relabelMover, NotFoundPair]
  | tabToFound c =>
      have hcx : c ≠ x := fun hc => h1 (by rw [hc])
      have hct : c ≠ x.twin := fun hc => h2 (by rw [hc])
      rw [Move.relabelMover, card_relabelTwin_ne hcx hct]
      exact ⟨h1, h2, h3, h4⟩
  | foundToTab c b =>
      have hcx : c ≠ x := fun hc => h3 b (by rw [hc])
      have hct : c ≠ x.twin := fun hc => h4 b (by rw [hc])
      rw [Move.relabelMover, card_relabelTwin_ne hcx hct]
      exact ⟨h1, h2, h3, h4⟩
  | tabToTab c b =>
      simp [Move.relabelMover, NotFoundPair]

/-- **The splice functor on pair-free plays.**  A pair-free witness
shuffle `s → t` maps to a pair-free witness shuffle of the run splices.
(restated from `Orig2/TwinLastPull.lean:201` — the per-file kit norm) -/
private theorem pairFreeOrbit_splice_of_pairFree {x : Card} {s t : State} {play : List Move}
    (hwf : s.WF) (hx : ∃ z, seatOf s x = some (Sum.inr z))
    (hxt : ∃ z : Card, seatOf s x.twin = some (Sum.inr z.twin))
    (hplay : ShufflePlayW s play t)
    (hno : ∀ m ∈ play, NotFoundPair x m) :
    PairFreeOrbit x (s.spliceTwinRuns x) (t.spliceTwinRuns x) := by
  revert hwf hx hxt hno
  induction hplay with
  | nil st =>
      intro _ _ _ _
      exact pairFreeOrbit_refl x (st.spliceTwinRuns x)
  | @cons st s₁ W m ρ hrev hstep hrest ih =>
      intro hwf hx hxt hno
      have hm : NotFoundPair x m := hno m (by simp)
      have hstepS :=
        TwinSpliceComm.splice_step_comm_rev hwf hx hxt hstep hrev hm
      have hrevS := reversibleAtW_splice_relabelMover hwf hx hxt hrev hm
      have hnoS := notFoundPair_relabelMover hm
      have hseats := seat_inr_of_pairFree_step hwf hstep hrev hm hx hxt
      have hwf₁ : s₁.WF := step_wf hwf hstep
      have hsingle : PairFreeOrbit x (st.spliceTwinRuns x) (s₁.spliceTwinRuns x) := by
        refine pairFreeOrbit_of_play (Walk.cons hrevS hstepS (Walk.nil _)) ?_
        intro n hn
        rw [List.mem_singleton] at hn
        subst hn
        exact hnoS
      have htail : PairFreeOrbit x (s₁.spliceTwinRuns x) (W.spliceTwinRuns x) :=
        ih hwf₁ hseats.1 hseats.2
          (fun n hn => hno n (List.mem_cons_of_mem m hn))
      exact PairFreeOrbit.trans hsingle htail

/-! ## §2. Foundation arithmetic (restated from
`Orig2/TwinPairFreeRev.lean:43–133` — the per-file kit norm) -/

/-- The build-order list is nodup.
(restated from `Orig2/TwinPairFreeRev.lean:43` — the per-file kit norm) -/
private theorem upCards_nodup (s : Suit) : s.upCards.Nodup := by
  cases s <;> decide

/-- The first-occurrence position of a member is unchanged by taking a
prefix that still contains it.
(restated from `Orig2/TwinPairFreeRev.lean:48` — the per-file kit norm) -/
private theorem posOf_take_of_mem {α : Type} [DecidableEq α] :
    ∀ (l : List α) (x : α), x ∈ l → ∀ n, x ∈ l.take n →
      FoundKit.posOf x (l.take n) = FoundKit.posOf x l := by
  intro l
  induction l with
  | nil =>
      intro x hx
      cases hx
  | cons y t ih =>
      intro x hx n hn
      cases n with
      | zero =>
          rw [List.take_zero] at hn
          exact absurd hn (by simp)
      | succ m =>
          rw [List.take_succ_cons] at hn ⊢
          rcases List.mem_cons.mp hn with hxy | hxt
          · subst x
            rw [FoundKit.posOf, ite_eq_left rfl, FoundKit.posOf, ite_eq_left rfl]
          · by_cases hyx : y = x
            · subst hyx
              rw [FoundKit.posOf, ite_eq_left rfl, FoundKit.posOf, ite_eq_left rfl]
            · have hxt' : x ∈ t := by
                rcases List.mem_cons.mp hx with hxy2 | hxt2
                · exact absurd hxy2.symm hyx
                · exact hxt2
              rw [FoundKit.posOf, ite_eq_right hyx, FoundKit.posOf, ite_eq_right hyx,
                ih x hxt' m hxt]

/-- In a nodup list, the last element sits at the final index.
(restated from `Orig2/TwinPairFreeRev.lean:78` — the per-file kit norm) -/
private theorem posOf_last_eq_length_sub_one {l : List Card} {c : Card}
    (hnd : l.Nodup) (hlast : lastOf l = some c) :
    FoundKit.posOf c l = l.length - 1 := by
  induction l with
  | nil =>
      rw [lastOf] at hlast
      exact absurd hlast (by simp)
  | cons y t ih =>
      cases t with
      | nil =>
          rw [lastOf] at hlast
          injection hlast with hcy
          subst hcy
          rw [FoundKit.posOf, ite_eq_left rfl]
          rfl
      | cons z t' =>
          rw [show lastOf (y :: z :: t') = lastOf (z :: t') from rfl] at hlast
          have hnd' : (z :: t').Nodup := (List.nodup_cons.mp hnd).2
          have hih := ih hnd' hlast
          have hyc : y ≠ c := by
            intro hcon
            subst hcon
            exact (List.nodup_cons.mp hnd).1 (lastOf_mem hlast)
          rw [FoundKit.posOf, ite_eq_right hyc, hih]
          rfl

/-- A `WF` foundation's chop length is the rank index of its top card.
(restated from `Orig2/TwinPairFreeRev.lean:105` — the per-file kit norm) -/
private theorem found_chop_length_eq_rank {st : State} {s : Suit} {c : Card}
    (hwf : st.WF) (htop : st.foundTop s = some c) :
    (chop (st.found s)).length = c.rank.toIdx := by
  obtain ⟨n, hn⟩ := hwf.found_prefix s
  have hlast : lastOf (st.found s) = some c := htop
  have hmemFound : c ∈ st.found s := lastOf_mem hlast
  have hmem : c ∈ s.upCards.take n := by rw [← hn]; exact hmemFound
  have hmemU : c ∈ s.upCards := List.mem_of_mem_take hmem
  obtain ⟨r, -, hcr⟩ := List.mem_map.mp hmemU
  have hc : c = Card.mk s r := hcr.symm
  subst hc
  have hnd : (s.upCards.take n).Nodup := List.Pairwise.take (i := n) (upCards_nodup s)
  have hposLast : FoundKit.posOf (Card.mk s r) (s.upCards.take n) =
      (s.upCards.take n).length - 1 :=
    posOf_last_eq_length_sub_one hnd (by rw [← hn]; exact hlast)
  have hposEq : FoundKit.posOf (Card.mk s r) (s.upCards.take n) =
      FoundKit.posOf (Card.mk s r) s.upCards :=
    posOf_take_of_mem s.upCards (Card.mk s r) hmemU n hmem
  have hrank : FoundKit.posOf (Card.mk s r) s.upCards = r.toIdx :=
    FoundKit.posOf_upCards s r
  have hcl : (chop (st.found s)).length + 1 = (st.found s).length := by
    have hlc := congrArg List.length (lastOf_chop hlast)
    rw [List.length_append] at hlc
    simp at hlc
    omega
  have htakeLen : (s.upCards.take n).length = (st.found s).length := by rw [← hn]
  calc
    (chop (st.found s)).length = (s.upCards.take n).length - 1 := by omega
    _ = FoundKit.posOf (Card.mk s r) (s.upCards.take n) := hposLast.symm
    _ = FoundKit.posOf (Card.mk s r) s.upCards := hposEq
    _ = r.toIdx := hrank

/-! ## §3. The self-arming keystone (restated from
`Orig2/TwinSelfArm.lean` — the per-file kit norm) -/

/-- **The self-arming law.**  A successful `foundToTab c b` leaves the
post-state next-up for `c`: the chop re-arms the raise.
(restated from `Orig2/TwinSelfArm.lean:30` — the per-file kit norm) -/
private theorem nextUp_of_foundToTab {u s : State} {c : Card} {b : Base}
    (hwf : u.WF) (hstep : State.step u (Move.foundToTab c b) = some s) :
    s.nextUp c = true := by
  obtain ⟨c', htop, hc'c, -, hs⟩ := step_foundToTab_inv hstep
  rw [hc'c] at htop
  have hsf : s.found c.suit = chop (u.found c.suit) := by
    rw [hs, putCard_found]
    simp [State.setFound]
  have hchop := found_chop_length_eq_rank hwf htop
  show decide (c.rank.toIdx = (s.found c.suit).length)
  rw [hsf, hchop]
  simp

/-- **The self-armed reversibility.**  After a successful return
(`foundToTab c b`), the post-state can raise `c` reversibly: the
chop re-arms the raise (the previous row), and the raised card
always has a giveback seat — the card beneath it (the chop-cons
cell), or the king's vacate (the anchor landing, kings only).
This is the `hraise` cell the twin-swap recipe consumes, satisfied
by the return itself.
(restated from `Orig2/TwinSelfArm.lean:50` — the per-file kit norm) -/
private theorem reversibleAtW_tabToFound_of_foundToTab {u s : State} {c : Card} {b : Base}
    (hwf : u.WF) (hstep : State.step u (Move.foundToTab c b) = some s) :
    reversibleAtW s (Move.tabToFound c) := by
  have hwfs : s.WF := step_wf hwf hstep
  have hn : s.nextUp c = true := nextUp_of_foundToTab hwf hstep
  refine (tabToFoundR_iff_reversibleAtW hwfs c).mp ?_
  obtain ⟨c', htop, hc'c, hcp, hs⟩ := step_foundToTab_inv hstep
  rw [hc'c] at htop
  cases b with
  | inl a' =>
      have hking : c.rank = Rank.king := (canPlace_inl hcp).2
      have hpiles : s.piles a' = { hidden := [], faceUp := [c] } := by
        rw [hs, putCard_piles_inl]
        simp
      have hpt : s.pileOfTop c = some a' :=
        (pileOfTop_eq_some_iff hwfs).mpr (by rw [hpiles]; rfl)
      simp only [tabToFoundR, hn, hpt, hpiles, chop]
      rw [hking]
      rfl
  | inr z =>
      obtain ⟨k, hloc, -⟩ := canPlace_inr hcp
      have hpiles : (s.piles k).faceUp = (u.piles k).faceUp ++ [c] := by
        rw [hs, putCard_piles_inr (u.setFound c.suit (chop (u.found c.suit))) c z k hloc]
        simp [State.setFound]
      have hpt : s.pileOfTop c = some k :=
        (pileOfTop_eq_some_iff hwfs).mpr (by
          show lastOf (s.piles k).faceUp = some c
          rw [hpiles, lastOf_snoc])
      have hzmem : z ∈ (u.piles k).faceUp :=
        lastOf_mem ((pileOfTop_eq_some_iff hwf).mp hloc)
      have hchop : chop (s.piles k).faceUp = (u.piles k).faceUp := by
        rw [hpiles, chop_snoc]
      cases hu : (u.piles k).faceUp with
      | nil => exact absurd hzmem (by rw [hu]; simp)
      | cons hd tl =>
          simp only [tabToFoundR, hn, hpt, hchop, hu]

#print axioms nextUp_of_foundToTab
#print axioms reversibleAtW_tabToFound_of_foundToTab

/-! ## §4. The pair-free transfer (restated from
`Orig2/TwinPairFreeTransfer.lean` — the per-file kit norm;
`swappableIn_transfer_point_pairFree` rides `TwinPointTransfer`
directly, and the twin-comm row below is restated from
`Orig2/TwinBothCovered.lean:249`). -/

/-- `SwappableIn` is symmetric in the two members of the pair
(restated from `Orig2/TwinBothCovered.lean:249` — the per-file kit norm). -/
theorem swappableIn_twin_comm {s : State} {x : Card} :
    SwappableIn s x ↔ SwappableIn s x.twin := by
  constructor
  · rintro ⟨v, h, horb⟩
    obtain ⟨h1, h2, h3, hb, hf, hs, hw, hc⟩ := h
    refine ⟨v, ⟨?_, ?_, ?_, hb, hf, hs, hw, hc⟩, horb⟩
    · simpa [card_twin_twin] using h2
    · simpa [card_twin_twin] using h1
    · intro y hy1 hy2
      exact h3 y (by simpa [card_twin_twin] using hy2) hy1
  · rintro ⟨v, h, horb⟩
    obtain ⟨h1, h2, h3, hb, hf, hs, hw, hc⟩ := h
    refine ⟨v, ⟨?_, ?_, ?_, hb, hf, hs, hw, hc⟩, horb⟩
    · simpa [card_twin_twin] using h2
    · simpa [card_twin_twin] using h1
    · intro y hy1 hy2
      exact h3 y hy2 (by simpa [card_twin_twin] using hy1)

/-- **The pair-free transfer, discharged (the owner's stepping-stone).**
If the twins are seated on `.inr` parents at both ends of a `NotFoundPair`
witness play `s → t`, then `SwappableIn` transfers — the point-hom
square of `swappableIn_transfer_point_pairFree` follows from the play by
the splice functor.
(restated from `Orig2/TwinPairFreeTransfer.lean:60` — the per-file kit norm) -/
theorem swappableIn_transfer_of_pairFreePath
    {s t : State} {x : Card} {play : List Move}
    (hwf : s.WF) (hwf' : t.WF)
    (hxs : ∃ z, seatOf s x = some (Sum.inr z))
    (hxts : ∃ z : Card, seatOf s x.twin = some (Sum.inr z.twin))
    (hxt : ∃ z, seatOf t x = some (Sum.inr z))
    (hxtt : ∃ z : Card, seatOf t x.twin = some (Sum.inr z.twin))
    (hplay : ShufflePlayW s play t)
    (hno : ∀ m ∈ play, NotFoundPair x m)
    (hswap : SwappableIn s x) :
    SwappableIn t x := by
  obtain ⟨play', hplay', -⟩ :=
    pairFreeOrbit_splice_of_pairFree hwf hxs hxts hplay hno
  exact swappableIn_transfer_point_pairFree hwf hwf' hxs hxts hxt hxtt hplay hno
    (sameOrbitSetoid.symm (shufflePlayW_revEqW hplay')) hswap

#print axioms swappableIn_transfer_of_pairFreePath

/-- **The ledger-stub shape, restricted to pair-free journeys.**  The
corrected fiber transfer's statement with the class row STRENGTHENED to
`PairFreeOrbit x s s'` (a witness play that never raises or pulls either
twin); the founds row is dropped — the proof does not read it, so the
journey may change founds via other cards' letters.  `SwappableIn` is
definitionally the stub's existential shape (`Orig2/Vocab.lean`), so the
conclusion is the stub's verbatim.
(restated from `Orig2/TwinPairFreeTransfer.lean:85` — the per-file kit norm) -/
theorem fiber_transfer_corrected_of_pairFreePath :
    ∀ (s s' : State) (x : Card), s.WF → s'.WF →
      PairFreeOrbit x s s' →
      (∃ z, seatOf s x = some (Sum.inr z)) →
      (∃ z : Card, seatOf s x.twin = some (Sum.inr z.twin)) →
      (∃ z, seatOf s' x = some (Sum.inr z)) →
      (∃ z : Card, seatOf s' x.twin = some (Sum.inr z.twin)) →
      (∃ v, twinPairSwapStrict s v x ∧ sameOrbitSetoid.r s v) →
      (∃ v', twinPairSwapStrict s' v' x ∧ sameOrbitSetoid.r s' v') := by
  intro s s' x hwf hwf' hfree hxs hxts hxt hxtt hswap
  obtain ⟨play, hplay, hno⟩ := hfree
  exact swappableIn_transfer_of_pairFreePath hwf hwf' hxs hxts hxt hxtt
    hplay hno hswap

#print axioms fiber_transfer_corrected_of_pairFreePath

/-! ## §5. Seat & parent kit (restated from `Orig2/TwinForcedCancel.lean`,
`Orig2/TwinFoundationRow.lean`, `Orig2/TwinPreludeFunctor.lean` — the
per-file kit norm) -/

/-- Expose the first letter of a witness walk.
(restated from `Orig2/TwinForcedCancel.lean:81` — the per-file kit norm) -/
private theorem walk_cons_inv {P : State → Move → Prop} {st s' : State}
    {m : Move} {ρ : List Move} (h : Walk P st (m :: ρ) s') :
    ∃ s1, P st m ∧ State.step st m = some s1 ∧ Walk P s1 ρ s' := by
  cases h with
  | cons hlet hstep hrest => exact ⟨_, hlet, hstep, hrest⟩

/-- A foundation card is off the tableau, hence unseated.
(restated from `Orig2/TwinForcedCancel.lean:90` — the per-file kit norm) -/
private theorem seatOf_none_of_mem_found {s : State} (hwf : s.WF) {c : Card}
    (h : c ∈ s.found c.suit) : seatOf s c = none := by
  apply tfc_seatOf_none
  apply tfc_pileHolding_none
  intro a hmem
  exact ((mem_found_unique hwf h).1 a).2 hmem

/-- A successful raise appends the raised card to its foundation row.
(restated from `Orig2/TwinFoundationRow.lean:107` — the per-file kit norm) -/
private theorem raise_found_self {s s1 : State} {c : Card}
    (hraise : State.step s (Move.tabToFound c) = some s1) :
    s1.found c.suit = s.found c.suit ++ [c] := by
  obtain ⟨-, a, -, hs1⟩ := step_tabToFound_inv hraise
  rw [hs1]
  exact setFound_found_self

/-- A card seated `.inr` on a card parent is not a king.
(restated from `Orig2/TwinFoundationRow.lean:180` — the per-file kit norm) -/
private theorem seated_inr_rank_ne_king {s : State} {c r : Card}
    (hwf : s.WF) (hseat : seatOf s c = some (Sum.inr r)) :
    c.rank ≠ Rank.king := by
  obtain ⟨a, hhold, -, hlast⟩ := tfc_seatOf_of_inr hseat
  have hfit : canSitOn c r = true := (tfc_seat_parent hwf hhold hlast).1
  intro hking
  have hlt := ((canSitOn_eq c r).mp hfit).1
  have hidx : c.rank.toIdx = 12 := by rw [hking]; rfl
  have hlt' := Rank.toIdx_lt r.rank
  omega

/-- The twin-left fitting law, copied from the seam-private rows: the
mover's suit twin does not change the pile-fit predicate.
(restated from `Orig2/TwinPreludeFunctor.lean:433` — the per-file kit norm) -/
private theorem canSitOn_twin_left' (c b : Card) :
    canSitOn c.twin b = canSitOn c b := by
  rcases c with ⟨s, r⟩
  rcases b with ⟨s', r'⟩
  cases s <;> cases s' <;> rfl

/-- Two distinct twins cannot share the same direct parent: both would sit
at the same successor position in one legal run, contradicting the strict
rank descent.
(restated from `Orig2/TwinPreludeFunctor.lean:442` — the per-file kit norm) -/
private theorem not_twin_same_parent {u : State} {x z : Card}
    (hwf : u.WF)
    (hx : seatOf u x = some (Sum.inr z))
    (hxt : seatOf u x.twin = some (Sum.inr z)) : False := by
  obtain ⟨a, hhold, -, hlast⟩ := tfc_seatOf_of_inr hx
  obtain ⟨a', hhold', -, hlast'⟩ := tfc_seatOf_of_inr hxt
  have hz_a : z ∈ (u.piles a).faceUp := mem_below _ (lastOf_mem hlast)
  have hz_a' : z ∈ (u.piles a').faceUp := mem_below _ (lastOf_mem hlast')
  have haa' : a = a' := by
    by_cases h : a = a'
    · exact h
    · exact absurd hz_a'
        ((mem_faceUp_unique hwf hz_a a' (fun hh => h hh.symm)).1)
  have hxmem : x ∈ (u.piles a).faceUp := pileHolding_mem hhold
  have htmem : x.twin ∈ (u.piles a).faceUp := by
    simpa [haa'] using pileHolding_mem hhold'
  have heq : x = x.twin :=
    runOK_rank_distinct (hwf.runOK_of a) hxmem htmem (by rfl)
  exact (card_twin_ne x) heq.symm

/-- **The two parent witnesses align.**  If `x` is on `z` and `x.twin` is
on `zt.twin`, then `zt = z`: the only other fitting parent is the twin of
the first, and the same-parent alternative is impossible.
(restated from `Orig2/TwinPreludeFunctor.lean:465` — the per-file kit norm) -/
private theorem twin_parent_eq_of_seats {u : State} {x z zt : Card}
    (hwf : u.WF)
    (hx : seatOf u x = some (Sum.inr z))
    (hxt : seatOf u x.twin = some (Sum.inr zt.twin)) :
    zt = z := by
  have hz : canSitOn x z = true := by
    obtain ⟨a, hhold, -, hlast⟩ := tfc_seatOf_of_inr hx
    exact (tfc_seat_parent hwf hhold hlast).1
  have hzt : canSitOn x zt.twin = true := by
    obtain ⟨a, hhold, -, hlast⟩ := tfc_seatOf_of_inr hxt
    have h := (tfc_seat_parent hwf hhold hlast).1
    simpa [canSitOn_twin_left'] using h
  rcases tfc_fitting_parent hzt hz with h | h
  · exfalso
    exact not_twin_same_parent hwf hx (by simpa [h] using hxt)
  · have := congrArg Card.twin h
    simpa [card_twin_twin] using this

/-! ## §6. The first-touch reduction (restated from
`Orig2/TwinFirstTouchReduction.lean` — the per-file kit norm) -/

/-! ### Kit — splitting a walk over an appended list -/

/-- Split a witness walk over an appended list.
(restated from `Orig2/TwinFirstTouchReduction.lean:58` — the per-file
kit norm) -/
private theorem walk_append_split {P : State → Move → Prop}
    {a c : State} {l1 l2 : List Move} (h : Walk P a (l1 ++ l2) c) :
    ∃ b, Walk P a l1 b ∧ Walk P b l2 c := by
  induction l1 generalizing a with
  | nil => exact ⟨a, Walk.nil a, h⟩
  | cons m rest ih =>
      obtain ⟨s1, hlet, hstep, hrest⟩ :=
        walk_cons_inv (by simpa using h)
      obtain ⟨b, hb1, hb2⟩ := ih hrest
      exact ⟨b, Walk.cons hlet hstep hb1, hb2⟩

/-! ### Kit — WF and the `.inr` seats are maintained along pair-free walks -/

private theorem wf_seats_of_pairFreeWalk {u v : State} {x : Card} {play : List Move}
    (hwf : u.WF) (hplay : ShufflePlayW u play v)
    (hx : ∃ z, seatOf u x = some (Sum.inr z))
    (hxt : ∃ z : Card, seatOf u x.twin = some (Sum.inr z.twin))
    (hno : ∀ m ∈ play, NotFoundPair x m) :
    v.WF ∧ (∃ z, seatOf v x = some (Sum.inr z)) ∧
      (∃ z : Card, seatOf v x.twin = some (Sum.inr z.twin)) := by
  revert hwf hx hxt hno
  induction hplay with
  | nil st =>
      intro hwf hx hxt _
      exact ⟨hwf, hx, hxt⟩
  | @cons st s1 W m rest' hrev hstep hrest ih =>
      intro hwf hx hxt hno
      obtain ⟨hs1, hst1⟩ :=
        seat_inr_of_pairFree_step hwf hstep hrev (hno m (by simp)) hx hxt
      exact ih (step_wf hwf hstep) hs1 hst1
        (fun n hn => hno n (List.mem_cons_of_mem _ hn))

/-! ### The sharpening — the first touch is necessarily a raise -/

private theorem not_notFoundPair_of_isPairFound {x : Card} {m : Move}
    (hm : IsPairFound x m) : ¬ NotFoundPair x m := fun h =>
  (notFoundPair_iff_not_isPairFound x m).mp h hm

/-- At a state where both twins are `.inr`-seated, a touching move
that fires is necessarily a RAISE of a twin: the pull shapes
(`foundToTab x b` / `foundToTab x.twin b`) cannot fire, because a
seated card is not on the foundation.
(restated from `Orig2/TwinFirstTouchReduction.lean:100` — the per-file
kit norm) -/
private theorem firstTouch_is_raise {w w' : State} {x : Card} {m : Move}
    (hwf : w.WF)
    (hx : ∃ z, seatOf w x = some (Sum.inr z))
    (hxt : ∃ z : Card, seatOf w x.twin = some (Sum.inr z.twin))
    (hstep : State.step w m = some w')
    (hm : IsPairFound x m) :
    m = Move.tabToFound x ∨ m = Move.tabToFound x.twin := by
  rcases hm with h | h | ⟨b, hb⟩ | ⟨b, hb⟩
  · exact Or.inl h
  · exact Or.inr h
  · subst hb
    obtain ⟨c', htop, hc'c, -, -⟩ := step_foundToTab_inv hstep
    rw [hc'c] at htop
    have hmem : x ∈ w.found x.suit := by
      simpa [State.foundTop] using lastOf_mem htop
    obtain ⟨z, hz⟩ := hx
    rw [seatOf_none_of_mem_found hwf hmem] at hz
    simp at hz
  · subst hb
    obtain ⟨c', htop, hc'c, -, -⟩ := step_foundToTab_inv hstep
    rw [hc'c] at htop
    have hmem : x.twin ∈ w.found x.twin.suit := by
      simpa [State.foundTop] using lastOf_mem htop
    obtain ⟨z, hz⟩ := hxt
    rw [seatOf_none_of_mem_found hwf hmem] at hz
    simp at hz

/-! ### The residual and the reduction -/

/-- **`FirstTouchRestart`** — the owner's named residual: the full
transfer with the FIRST touching move made explicit.  The swap is
already available at the pre-touch state `w` (provided by the pair-free
prefix in the reduction); one reversible touching move fires; the
suffix to the seated end `v` is arbitrary.
(restated from `Orig2/TwinFirstTouchReduction.lean:134` — the per-file
kit norm) -/
def FirstTouchRestart : Prop :=
  ∀ (w w' v : State) (x : Card) (rest : List Move),
    w.WF → v.WF →
    (∃ z, seatOf w x = some (Sum.inr z)) →
    (∃ z : Card, seatOf w x.twin = some (Sum.inr z.twin)) →
    (∃ z, seatOf v x = some (Sum.inr z)) →
    (∃ z : Card, seatOf v x.twin = some (Sum.inr z.twin)) →
    SwappableIn w x →
    (∃ m, ¬ NotFoundPair x m ∧ reversibleAtW w m ∧
        State.step w m = some w' ∧ ShufflePlayW w' rest v) →
    SwappableIn v x

/-- **THE REDUCTION (witness-journey form).**  Every witness journey
from seated, swap-available `s` to seated `t` either never touches the
twin — the landed pair-free card — or its first touching move is
reached with availability already transferred to the pre-touch state;
`FirstTouchRestart` finishes.
(restated from `Orig2/TwinFirstTouchReduction.lean:151` — the per-file
kit norm) -/
private theorem swappableIn_transfer_of_firstTouchRestart
    (hR : FirstTouchRestart)
    {s t : State} {x : Card} {play : List Move}
    (hwf : s.WF) (hwft : t.WF)
    (hsx : ∃ z, seatOf s x = some (Sum.inr z))
    (hstx : ∃ z : Card, seatOf s x.twin = some (Sum.inr z.twin))
    (htx : ∃ z, seatOf t x = some (Sum.inr z))
    (httx : ∃ z : Card, seatOf t x.twin = some (Sum.inr z.twin))
    (hplay : ShufflePlayW s play t)
    (hswap : SwappableIn s x) :
    SwappableIn t x := by
  rcases exists_pairFound_split x play with hall | ⟨pre, m, post, hsplit, hm, hpre⟩
  · refine swappableIn_transfer_of_pairFreePath hwf hwft hsx hstx htx httx hplay ?_ hswap
    intro n hn
    exact (notFoundPair_iff_not_isPairFound x n).mpr (hall n hn)
  · subst hsplit
    obtain ⟨w, hwpre, hwpost⟩ := walk_append_split hplay
    have hnoPre : ∀ n ∈ pre, NotFoundPair x n := fun n hn =>
      (notFoundPair_iff_not_isPairFound x n).mpr (hpre n hn)
    obtain ⟨hwfw, hwx, hwtx⟩ :=
      wf_seats_of_pairFreeWalk hwf hwpre hsx hstx hnoPre
    have hswapw : SwappableIn w x :=
      swappableIn_transfer_of_pairFreePath hwf hwfw hsx hstx hwx hwtx hwpre hnoPre hswap
    obtain ⟨w', hrev, hstep, hrest⟩ := walk_cons_inv hwpost
    exact hR w w' t x post hwfw hwft hwx hwtx htx httx hswapw
      ⟨m, not_notFoundPair_of_isPairFound hm, hrev, hstep, hrest⟩

/-- **THE REDUCTION (class form).**  The campaign's rigidity row at the
`BitWellDefined` grade: availability transfers along the class.
(restated from `Orig2/TwinFirstTouchReduction.lean:180` — the per-file
kit norm) -/
private theorem swappableIn_transfer_class_of_firstTouchRestart
    (hR : FirstTouchRestart)
    {s s' : State} {x : Card}
    (hwf : s.WF) (hwf' : s'.WF)
    (hclass : sameOrbitSetoid.r s s')
    (hsx : ∃ z, seatOf s x = some (Sum.inr z))
    (hstx : ∃ z : Card, seatOf s x.twin = some (Sum.inr z.twin))
    (htx : ∃ z, seatOf s' x = some (Sum.inr z))
    (httx : ∃ z : Card, seatOf s' x.twin = some (Sum.inr z.twin))
    (hswap : SwappableIn s x) :
    SwappableIn s' x := by
  obtain ⟨π, hπ, -⟩ := sameOrbitSetoid.iseqv.symm hclass
  exact swappableIn_transfer_of_firstTouchRestart hR hwf hwf' hsx hstx htx httx hπ hswap

#print axioms firstTouch_is_raise
#print axioms swappableIn_transfer_of_firstTouchRestart
#print axioms swappableIn_transfer_class_of_firstTouchRestart

/-! ## §7. The last-return main proof (restated from
`Orig2/TwinLastReturn.lean` — the per-file kit norm) -/

/-! ### The per-letter pair-foundation dichotomy (choice-free) -/

private theorem isPairFound_or_not {x : Card} {m : Move} :
    IsPairFound x m ∨ ¬ IsPairFound x m := by
  cases m with
  | draw => exact Or.inr (fun h => by
    rcases h with h | h | ⟨b, h⟩ | ⟨b, h⟩ <;> exact Move.noConfusion h)
  | wasteToFound y => exact Or.inr (fun h => by
    rcases h with h | h | ⟨b, h⟩ | ⟨b, h⟩ <;> exact Move.noConfusion h)
  | wasteToTab y b => exact Or.inr (fun h => by
    rcases h with h | h | ⟨b', h⟩ | ⟨b', h⟩ <;> exact Move.noConfusion h)
  | tabToFound y =>
      by_cases hy : y = x
      · exact Or.inl (Or.inl (congrArg Move.tabToFound hy))
      · by_cases hyt : y = x.twin
        · exact Or.inl (Or.inr (Or.inl (congrArg Move.tabToFound hyt)))
        · exact Or.inr (fun h => by
            rcases h with h | h | ⟨b, h⟩ | ⟨b, h⟩
            · exact hy (Move.tabToFound.inj h)
            · exact hyt (Move.tabToFound.inj h)
            · exact Move.noConfusion h
            · exact Move.noConfusion h)
  | foundToTab y b =>
      by_cases hy : y = x
      · exact Or.inl (Or.inr (Or.inr (Or.inl
          ⟨b, congrArg (fun y => Move.foundToTab y b) hy⟩)))
      · by_cases hyt : y = x.twin
        · exact Or.inl (Or.inr (Or.inr (Or.inr
            ⟨b, congrArg (fun y => Move.foundToTab y b) hyt⟩)))
        · exact Or.inr (fun h => by
            rcases h with h | h | ⟨b', h⟩ | ⟨b', h⟩
            · exact Move.noConfusion h
            · exact Move.noConfusion h
            · exact hy (Move.foundToTab.inj h).1
            · exact hyt (Move.foundToTab.inj h).1)
  | tabToTab y b => exact Or.inr (fun h => by
    rcases h with h | h | ⟨b', h⟩ | ⟨b', h⟩ <;> exact Move.noConfusion h)

private theorem isPairFound_of_not_notFoundPair {x : Card} {m : Move}
    (h : ¬ NotFoundPair x m) : IsPairFound x m := by
  rcases isPairFound_or_not (x := x) (m := m) with hc | hc
  · exact hc
  · exact absurd hc (fun hip' => h ((notFoundPair_iff_not_isPairFound x m).mpr hip'))

/-! ### The last-touch split -/

private theorem exists_lastPairFound_split (x : Card) (play : List Move) :
    (∀ n ∈ play, ¬ IsPairFound x n) ∨
    ∃ pre r post, play = pre ++ r :: post ∧ IsPairFound x r ∧
      (∀ n ∈ post, ¬ IsPairFound x n) := by
  induction play with
  | nil => exact Or.inl (by simp)
  | cons k t ih =>
      rcases isPairFound_or_not (x := x) (m := k) with hk | hk
      · rcases ih with hall | ⟨pre, r, post, hsplit, hr, hpost⟩
        · exact Or.inr ⟨[], k, t, rfl, hk, hall⟩
        · exact Or.inr ⟨k :: pre, r, post, by
            rw [List.cons_append, hsplit], hr, hpost⟩
      · rcases ih with hall | ⟨pre, r, post, hsplit, hr, hpost⟩
        · exact Or.inl (by
            intro n hn
            rcases List.mem_cons.mp hn with rfl | hn
            · exact hk
            · exact hall n hn)
        · exact Or.inr ⟨k :: pre, r, post, by
            rw [List.cons_append, hsplit], hr, hpost⟩

/-! ### The not-pull read of pair-freeness -/

private theorem not_pull_play_of_notFoundPair {x : Card} {play : List Move}
    (hno : ∀ n ∈ play, NotFoundPair x n) {y : Card} (hy : y = x ∨ y = x.twin) :
    ∀ k ∈ play, ∀ b : Base, k ≠ Move.foundToTab y b := by
  intro k hk b hb
  rcases hy with rfl | rfl
  · exact (hno k hk).2.2.1 b hb
  · exact (hno k hk).2.2.2 b hb

/-- Pair-freeness is twin-symmetric: the predicate names the pair, and
`x` and `x.twin` name the same pair. -/
private theorem notFoundPair_twin' {x : Card} {m : Move}
    (h : NotFoundPair x m) : NotFoundPair x.twin m := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact ⟨h2, fun hb => h1 (by rw [hb, card_twin_twin]),
    h4, fun b hb => h3 b (by rw [hb, card_twin_twin])⟩

/-! ### The foundation-membership rows (restated kit)

Two private kit rows restated in-card, per the house norm, with their
sources cited — this card carries no attachment-world import for a
single row. -/

/-- Foundation membership survives every letter except the pull of
that very card.  Restated private port of
`TwinAttShapes.found_mem_step_of_not_pullOf`
(`Orig2/TwinAttShapes.lean:1026`). -/
private theorem found_mem_step {u v : State} {m : Move} {y : Card}
    (hstep : State.step u m = some v)
    (hmem : y ∈ u.found y.suit)
    (hnot : ∀ b : Base, m ≠ Move.foundToTab y b) :
    y ∈ v.found y.suit := by
  cases m with
  | draw =>
      rw [← (chart_draw hstep).2.1 y.suit]
      exact hmem
  | wasteToFound c =>
      obtain ⟨-, z, zs, hw, hs⟩ := step_wasteToFound_inv hstep
      rw [hs]
      by_cases hys : c.suit = y.suit
      · rw [← hys]
        rw [← hys] at hmem
        rw [setFound_found_self]
        exact List.mem_append_left _ hmem
      · rw [setFound_found_ne (fun h => hys h.symm)]
        exact hmem
  | wasteToTab c b =>
      obtain ⟨-, z, zs, hw, hs⟩ := step_wasteToTab_inv hstep
      rw [hs]
      cases b with
      | inl t => rw [putCard_inl_found]; exact hmem
      | inr z => rw [putCard_inr_found]; exact hmem
  | tabToFound c =>
      obtain ⟨-, a, hpa, hs⟩ := step_tabToFound_inv hstep
      rw [hs]
      by_cases hys : c.suit = y.suit
      · rw [← hys]
        rw [← hys] at hmem
        rw [setFound_found_self]
        exact List.mem_append_left _ hmem
      · rw [setFound_found_ne (fun h => hys h.symm)]
        exact hmem
  | foundToTab c b =>
      obtain ⟨c', htop, hc'c, hcp, hs⟩ := step_foundToTab_inv hstep
      rw [hs]
      have hfound : ((u.setFound c.suit (chop (u.found c.suit))).putCard c b).found
          = (u.setFound c.suit (chop (u.found c.suit))).found := by
        cases b with
        | inl t => rw [putCard_inl_found]
        | inr z => rw [putCard_inr_found]
      rw [hfound]
      by_cases hys : c.suit = y.suit
      · rw [← hys]
        rw [← hys] at hmem
        have hlast : lastOf (u.found c.suit) = some c := by
          unfold State.foundTop at htop
          rw [hc'c] at htop
          exact htop
        have hyc : y ≠ c := by
          intro hyc
          exact hnot b (by rw [hyc])
        have hsnoc : u.found c.suit = chop (u.found c.suit) ++ [c] :=
          lastOf_chop hlast
        have hchop : y ∈ chop (u.found c.suit) := by
          rw [hsnoc, List.mem_append] at hmem
          rcases hmem with h | h
          · exact h
          · rw [List.mem_singleton] at h
            exact False.elim (hyc h)
        rw [setFound_found_self]
        exact hchop
      · rw [setFound_found_ne (fun h => hys h.symm)]
        exact hmem
  | tabToTab c b =>
      obtain ⟨a, hhold, hcp, -, hs⟩ := step_tabToTab_inv hstep
      rw [hs]
      rw [putRun_found, setPile_found]
      exact hmem

/-- A card on its foundation row stays there across any play that never
pulls it.  Restated private port of
`TwinExcursionClosure.found_mem_play_of_not_pull`
(`Orig2/TwinExcursionClosure.lean:832`), proved from the step row above. -/
private theorem found_mem_play_of_not_pull {u t : State} {play : List Move} {y : Card}
    (hplay : ShufflePlayW u play t)
    (hmem : y ∈ u.found y.suit)
    (hno : ∀ k ∈ play, ∀ b : Base, k ≠ Move.foundToTab y b) :
    y ∈ t.found y.suit := by
  induction play generalizing u t with
  | nil => cases hplay; exact hmem
  | cons k rest ih =>
      obtain ⟨u1, hrevK, hstepK, hrest⟩ := walk_cons_inv hplay
      have hmem1 : y ∈ u1.found y.suit :=
        found_mem_step hstepK hmem (hno k (by simp))
      exact ih hrest hmem1
        (fun n hn => hno n (List.mem_cons_of_mem k hn))

/-! ### The seat tracker -/

/-- A non-royal card that is `.inr`-seated or on its foundation row
stays so through any reversible letter. -/
private theorem seat_track_step {u v : State} {m : Move} {c : Card}
    (hwf : u.WF) (hstep : State.step u m = some v) (hrev : reversibleAtW u m)
    (hking : c.rank ≠ Rank.king)
    (h : (∃ z, seatOf u c = some (Sum.inr z)) ∨ c ∈ u.found c.suit) :
    (∃ z, seatOf v c = some (Sum.inr z)) ∨ c ∈ v.found c.suit := by
  cases m with
  | draw =>
      have hse := (chart_draw hstep).1
      have hfo := (chart_draw hstep).2.1 c.suit
      rcases h with ⟨z, hz⟩ | hmem
      · exact Or.inl ⟨z, by rw [hse c]; exact hz⟩
      · exact Or.inr (by rw [← hfo]; exact hmem)
  | wasteToFound y => exact absurd hrev (wasteToFound_not_reversibleAtW u y)
  | wasteToTab y b => exact absurd hrev (wasteToTab_not_reversibleAtW u y b)
  | tabToFound d =>
      by_cases hcd : c = d
      · subst hcd
        refine Or.inr ?_
        rw [raise_found_self hstep]
        exact List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl))
      · rcases h with ⟨z, hz⟩ | hmem
        · refine Or.inl ⟨z, ?_⟩
          rw [raise_seat_change_of_seated hstep hrev (by rw [hz]; simp) hcd]
          exact hz
        · exact Or.inr (found_mem_step hstep hmem
            (fun b hb => Move.noConfusion hb))
  | foundToTab y b =>
      by_cases hcy : c = y
      · subst hcy
        obtain ⟨-, -, -, hcp, -⟩ := step_foundToTab_inv hstep
        cases b with
        | inl a => exact absurd (canPlace_inl hcp).2 hking
        | inr z => exact Or.inl ⟨z, TwinSpliceComm.seatOf_foundToTab_mover hwf hstep⟩
      · rcases h with ⟨z, hz⟩ | hmem
        · refine Or.inl ⟨z, ?_⟩
          rw [pull_seat_change hstep c hcy]
          exact hz
        · exact Or.inr (found_mem_step hstep hmem
            (fun b' hb' => hcy (by injection hb' with h1 h2; exact h1.symm)))
  | tabToTab y b =>
      obtain ⟨a, hhold, hcp, -, hs⟩ := step_tabToTab_inv hstep
      have hfound : ∀ s', v.found s' = u.found s' := by
        rw [hs]
        intro s'
        rw [putRun_found, setPile_found]
      by_cases hcy : c = y
      · subst hcy
        cases b with
        | inl a' => exact absurd (canPlace_inl hcp).2 hking
        | inr z' =>
            refine Or.inl ⟨z', ?_⟩
            rw [tfc_seat_point_edit hwf hstep hrev c, if_pos rfl]
      · rcases h with ⟨z, hz⟩ | hmem
        · refine Or.inl ⟨z, ?_⟩
          rw [tfc_seat_point_edit hwf hstep hrev c, if_neg hcy]
          exact hz
        · exact Or.inr (by rw [hfound c.suit]; exact hmem)

private theorem seat_track_play {u v : State} {c : Card} {play : List Move}
    (hwf : u.WF) (hplay : ShufflePlayW u play v)
    (hking : c.rank ≠ Rank.king)
    (h : (∃ z, seatOf u c = some (Sum.inr z)) ∨ c ∈ u.found c.suit) :
    (∃ z, seatOf v c = some (Sum.inr z)) ∨ c ∈ v.found c.suit := by
  revert hwf h
  induction hplay with
  | nil st =>
      intro hwf h
      exact h
  | @cons st s1 W m rest' hrev hstep hrest ih =>
      intro hwf h
      exact ih (step_wf hwf hstep) (seat_track_step hwf hstep hrev hking h)

/-! ### The main theorem -/

private theorem firstTouchRestart_aux {w w' v : State} {x T : Card}
    {rest : List Move}
    (hwf : w.WF) (hvfv : v.WF)
    (hpair : T = x ∨ T = x.twin)
    (hseatTw : ∃ z, seatOf w T = some (Sum.inr z))
    (hseatTw' : ∃ z, seatOf w T.twin = some (Sum.inr z))
    (hseatTv : ∃ z, seatOf v T = some (Sum.inr z))
    (hseatTv' : ∃ z, seatOf v T.twin = some (Sum.inr z))
    (hrev : reversibleAtW w (Move.tabToFound T))
    (hstep : State.step w (Move.tabToFound T) = some w')
    (hrest : ShufflePlayW w' rest v) :
    SwappableIn v T := by
  -- the four plain seat facts for the pair, hoisted
  have hxw : ∃ z, seatOf w x = some (Sum.inr z) := by
    rcases hpair with rfl | rfl
    · exact hseatTw
    · obtain ⟨z, hz⟩ := hseatTw'
      rw [card_twin_twin] at hz
      exact ⟨z, hz⟩
  have hxtw : ∃ z, seatOf w x.twin = some (Sum.inr z) := by
    rcases hpair with rfl | rfl
    · obtain ⟨z, hz⟩ := hseatTw'
      exact ⟨z, hz⟩
    · obtain ⟨z, hz⟩ := hseatTw
      exact ⟨z, hz⟩
  have hxv : ∃ z, seatOf v x = some (Sum.inr z) := by
    rcases hpair with rfl | rfl
    · exact hseatTv
    · obtain ⟨z, hz⟩ := hseatTv'
      rw [card_twin_twin] at hz
      exact ⟨z, hz⟩
  have hxtv : ∃ z, seatOf v x.twin = some (Sum.inr z) := by
    rcases hpair with rfl | rfl
    · obtain ⟨z, hz⟩ := hseatTv'
      exact ⟨z, hz⟩
    · obtain ⟨z, hz⟩ := hseatTv
      exact ⟨z, hz⟩
  have ⟨zx, hzx⟩ := hxw
  have hxnr : x.rank ≠ Rank.king :=
    seated_inr_rank_ne_king hwf hzx
  have hTfound : T ∈ w'.found T.suit := by
    rw [raise_found_self hstep]
    exact List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl))
  rcases exists_lastPairFound_split x rest with hall | ⟨pre, r, post, hsplit, hr, hpost⟩
  · exfalso
    have hstays : T ∈ v.found T.suit :=
      found_mem_play_of_not_pull hrest hTfound
        (not_pull_play_of_notFoundPair
          (fun n hn => (notFoundPair_iff_not_isPairFound x n).mpr (hall n hn)) hpair)
    obtain ⟨z, hz⟩ := hseatTv
    exact absurd (seatOf_none_of_mem_found hvfv hstays) (by rw [hz]; simp)
  · subst hsplit
    obtain ⟨sm, hpre, hrpost⟩ := walk_append_split hrest
    obtain ⟨s, hrevr, hrstep, hpostw⟩ := walk_cons_inv hrpost
    have hwfw' : w'.WF := step_wf hwf hstep
    have hwfsm : sm.WF := run_wf hwfw'
      (Walk_run (P := fun st m => reversibleAtW st m) (st := w') (W := sm) hpre)
    have hwfs : s.WF := step_wf hwfsm hrstep
    have hpost' : ∀ n ∈ post, NotFoundPair x n :=
      fun n hn => (notFoundPair_iff_not_isPairFound x n).mpr (hpost n hn)
    rcases hr with rfl | rfl | ⟨b, hb⟩ | ⟨b, hb⟩
    · exfalso
      have hxstay : x ∈ v.found x.suit :=
        found_mem_play_of_not_pull hpostw (by
          rw [raise_found_self hrstep]
          exact List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl)))
          (not_pull_play_of_notFoundPair hpost' (Or.inl rfl))
      obtain ⟨z, hz⟩ := hxv
      exact absurd (seatOf_none_of_mem_found hvfv hxstay) (by rw [hz]; simp)
    · exfalso
      have hxtstay : x.twin ∈ v.found x.twin.suit :=
        found_mem_play_of_not_pull hpostw (by
          rw [raise_found_self hrstep]
          exact List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl)))
          (not_pull_play_of_notFoundPair hpost' (Or.inr rfl))
      obtain ⟨z, hz⟩ := hxtv
      exact absurd (seatOf_none_of_mem_found hvfv hxtstay) (by rw [hz]; simp)
    · -- r = foundToTab x b
      subst hb
      obtain ⟨-, -, -, hcp, -⟩ := step_foundToTab_inv hrstep
      cases b with
      | inl a => exact absurd (canPlace_inl hcp).2 hxnr
      | inr q =>
          have hRseat : seatOf s x = some (Sum.inr q) :=
            TwinSpliceComm.seatOf_foundToTab_mover hwfsm hrstep
          have hw2 : ShufflePlayW w
              ([Move.tabToFound T] ++ pre ++ [Move.foundToTab x (Sum.inr q)]) s :=
            ShufflePlayW_append
              (ShufflePlayW_append (Walk.cons hrev hstep (Walk.nil w')) hpre)
              (Walk.cons hrevr hrstep (Walk.nil s))
          have htrack := seat_track_play (c := x.twin) hwf hw2 hxnr (Or.inl hxtw)
          rcases htrack with ⟨z2, hxtseat⟩ | hxtfound
          · have halign : q.twin = z2 :=
              twin_parent_eq_of_seats hwfs hxtseat
                (show seatOf s x.twin.twin = some (Sum.inr q.twin.twin) from by
                  rw [card_twin_twin, card_twin_twin]
                  exact hRseat)
            have hct : seatOf s x.twin.twin = some (Sum.inr z2.twin) := by
              rw [card_twin_twin, ← halign, card_twin_twin]
              exact hRseat
            have hraise : reversibleAtW s (Move.tabToFound x.twin.twin) := by
              rw [card_twin_twin]
              exact reversibleAtW_tabToFound_of_foundToTab hwfsm hrstep
            have hswapO : SwappableIn s x.twin :=
              swappableIn_of_twin_raise hwfs hxtseat hct hraise
            have hxvT : ∃ z : Card, seatOf v x.twin.twin = some (Sum.inr z.twin) := by
              obtain ⟨z, hz⟩ := hxv
              exact ⟨z.twin, by rw [card_twin_twin, card_twin_twin]; exact hz⟩
            have hswapv : SwappableIn v x.twin :=
              swappableIn_transfer_of_pairFreePath hwfs hvfv ⟨z2, hxtseat⟩
                ⟨z2, hct⟩ hxtv hxvT hpostw
                (fun n hn => notFoundPair_twin' (hpost' n hn)) hswapO
            rcases hpair with rfl | rfl
            · rw [← card_twin_twin T]
              exact swappableIn_twin_comm.mp hswapv
            · exact hswapv
          · exfalso
            have hxtstay : x.twin ∈ v.found x.twin.suit :=
              found_mem_play_of_not_pull hpostw hxtfound
                (not_pull_play_of_notFoundPair hpost' (Or.inr rfl))
            obtain ⟨z, hz⟩ := hxtv
            exact absurd (seatOf_none_of_mem_found hvfv hxtstay)
              (by rw [hz]; simp)
    · -- r = foundToTab x.twin b
      subst hb
      obtain ⟨-, -, -, hcp, -⟩ := step_foundToTab_inv hrstep
      cases b with
      | inl a => exact absurd (canPlace_inl hcp).2 hxnr
      | inr q =>
          have hRseat : seatOf s x.twin = some (Sum.inr q) :=
            TwinSpliceComm.seatOf_foundToTab_mover hwfsm hrstep
          have hw2 : ShufflePlayW w
              ([Move.tabToFound T] ++ pre ++ [Move.foundToTab x.twin (Sum.inr q)]) s :=
            ShufflePlayW_append
              (ShufflePlayW_append (Walk.cons hrev hstep (Walk.nil w')) hpre)
              (Walk.cons hrevr hrstep (Walk.nil s))
          have htrack := seat_track_play (c := x) hwf hw2 hxnr (Or.inl hxw)
          rcases htrack with ⟨z2, hxseat⟩ | hxfound
          · have halign : q.twin = z2 :=
              twin_parent_eq_of_seats hwfs hxseat
                (show seatOf s x.twin = some (Sum.inr q.twin.twin) from by
                  rw [card_twin_twin]
                  exact hRseat)
            have hct : seatOf s x.twin = some (Sum.inr z2.twin) := by
              rw [← halign, card_twin_twin]
              exact hRseat
            have hraise : reversibleAtW s (Move.tabToFound x.twin) :=
              reversibleAtW_tabToFound_of_foundToTab hwfsm hrstep
            have hswapO : SwappableIn s x :=
              swappableIn_of_twin_raise hwfs hxseat hct hraise
            have hxtvT : ∃ z : Card, seatOf v x.twin = some (Sum.inr z.twin) := by
              obtain ⟨z, hz⟩ := hxtv
              exact ⟨z.twin, by rw [card_twin_twin]; exact hz⟩
            have hswapv : SwappableIn v x :=
              swappableIn_transfer_of_pairFreePath hwfs hvfv ⟨z2, hxseat⟩
                ⟨z2, hct⟩ hxv hxtvT hpostw hpost' hswapO
            rcases hpair with rfl | rfl
            · exact hswapv
            · exact swappableIn_twin_comm.mp hswapv
          · exfalso
            have hxstay : x ∈ v.found x.suit :=
              found_mem_play_of_not_pull hpostw hxfound
                (not_pull_play_of_notFoundPair hpost' (Or.inl rfl))
            obtain ⟨z, hz⟩ := hxv
            exact absurd (seatOf_none_of_mem_found hvfv hxstay)
              (by rw [hz]; simp)

/-- **`FirstTouchRestart` proved: the last-return route.**  The owner's
route, completed: the transfer is NOT carried through the excursion — it
is RECONSTRUCTED at the last return.
(restated from `Orig2/TwinLastReturn.lean:487` — the per-file kit norm) -/
theorem firstTouchRestart : FirstTouchRestart := by
  intro w w' v x rest hwf hvf hsx hstx htx httx hswap htouch
  obtain ⟨m, hm, hrev, hstep, hrest⟩ := htouch
  have hip : IsPairFound x m := isPairFound_of_not_notFoundPair hm
  have hsx' : ∃ z, seatOf w x = some (Sum.inr z) := hsx
  have hstx' : ∃ z, seatOf w x.twin = some (Sum.inr z) := by
    obtain ⟨z, hz⟩ := hstx
    exact ⟨z.twin, hz⟩
  have htx' : ∃ z, seatOf v x = some (Sum.inr z) := htx
  have httx' : ∃ z, seatOf v x.twin = some (Sum.inr z) := by
    obtain ⟨z, hz⟩ := httx
    exact ⟨z.twin, hz⟩
  rcases firstTouch_is_raise hwf hsx hstx hstep hip with rfl | rfl
  · exact firstTouchRestart_aux hwf hvf (Or.inl rfl) hsx' hstx' htx' httx'
      hrev hstep hrest
  · rw [← card_twin_twin x]
    exact swappableIn_twin_comm.mp (firstTouchRestart_aux hwf hvf (Or.inr rfl)
      hstx' (by obtain ⟨z, hz⟩ := hsx'; exact ⟨z, by rw [card_twin_twin]; exact hz⟩)
      httx' (by obtain ⟨z, hz⟩ := htx'; exact ⟨z, by rw [card_twin_twin]; exact hz⟩)
      hrev hstep hrest)

/-- **THE CORRECTED FIBER TRANSFER** (the `.inr`-seat grade): swap
availability transfers along the class.
(restated from `Orig2/TwinLastReturn.lean:510` — the per-file kit norm) -/
theorem fiber_transfer_corrected_of_lastReturn :
    ∀ (s s' : State) (x : Card), s.WF → s'.WF →
      sameOrbitSetoid.r s s' →
      (∃ z, seatOf s x = some (Sum.inr z)) →
      (∃ z : Card, seatOf s x.twin = some (Sum.inr z.twin)) →
      (∃ z, seatOf s' x = some (Sum.inr z)) →
      (∃ z : Card, seatOf s' x.twin = some (Sum.inr z.twin)) →
      SwappableIn s x → SwappableIn s' x := by
  intro s s' x hwf hwf' hclass hsx hstx htx httx hswap
  obtain ⟨π, hπ, -⟩ := sameOrbitSetoid.iseqv.symm hclass
  exact swappableIn_transfer_of_firstTouchRestart firstTouchRestart hwf hwf'
    hsx hstx htx httx hπ hswap

#print axioms firstTouchRestart
#print axioms fiber_transfer_corrected_of_lastReturn

/-! ## §8. The owner's seat lemma (fresh, 2026-10-25)

The wedge for the OPEN original statement (`Orig2/ClaimsScrutiny.lean`):
a swappable non-king pair that is seated at all sits on card
parents.  The `.inl` corners are impossible — a non-king at a pile
bottom cannot reach a DIFFERENT bottom (anchor landings are
king-gated, `canPlace_inl`), cannot leave the board except upward
(`tabToFound`), and the two twins cannot share one bottom (the
bottom seat is unique).  The mixed `.inl`/`.inr` corners die by the
`.inr` tracker above (`seat_track_play`): a non-king on a card
parent never lands on an anchor. -/

/-- An empty `below` at a cons pins the head: the search stopped at
the very first card. -/
private theorem head_of_below_nil {c y : Card} {t : List Card}
    (h : below c (y :: t) = []) : y = c := by
  rw [below_cons] at h
  by_cases hyc : y = c
  · exact hyc
  · rw [if_neg hyc] at h
    exact absurd h (by simp)

/-- The `.inl` seat is unique: two cards at the same pile bottom are
the same card (the bottom is one position). -/
private theorem seat_inl_unique {s : State} {c₁ c₂ : Card} {p : Anchor}
    (h1 : seatOf s c₁ = some (Sum.inl p)) (h2 : seatOf s c₂ = some (Sum.inl p)) :
    c₁ = c₂ := by
  obtain ⟨hh1, hb1⟩ := tfc_seatOf_of_inl h1
  obtain ⟨hh2, hb2⟩ := tfc_seatOf_of_inl h2
  have hm1 : c₁ ∈ (s.piles p).faceUp := pileHolding_mem hh1
  cases hl : (s.piles p).faceUp with
  | nil => exact absurd hm1 (by rw [hl]; simp)
  | cons y t =>
      rw [hl] at hb1 hb2
      exact (head_of_below_nil hb1).symm.trans (head_of_below_nil hb2)

/-- A non-king seated at a pile bottom keeps that bottom, moves to a
card parent, or reaches its foundation row — through any reversible
letter.  The `.inl` anchor is invariant: every other `.inl` landing
is king-gated (`canPlace_inl`), and no letter unseats a face-up card
except the raise. -/
private theorem seat_inl_track_step {u v : State} {m : Move} {c : Card}
    (hwf : u.WF) (hstep : State.step u m = some v) (hrev : reversibleAtW u m)
    (hking : c.rank ≠ Rank.king) {p : Anchor}
    (h : seatOf u c = some (Sum.inl p)) :
    seatOf v c = some (Sum.inl p) ∨
      (∃ z, seatOf v c = some (Sum.inr z)) ∨ c ∈ v.found c.suit := by
  have hcseat : seatOf u c ≠ none := by rw [h]; simp
  have hcnotfound : c ∉ u.found c.suit := fun hmem =>
    hcseat (seatOf_none_of_mem_found hwf hmem)
  cases m with
  | draw =>
      have hse := (chart_draw hstep).1
      exact Or.inl (by rw [hse c]; exact h)
  | wasteToFound y => exact absurd hrev (wasteToFound_not_reversibleAtW u y)
  | wasteToTab y b => exact absurd hrev (wasteToTab_not_reversibleAtW u y b)
  | tabToFound d =>
      by_cases hcd : c = d
      · subst hcd
        refine Or.inr (Or.inr ?_)
        rw [raise_found_self hstep]
        exact List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl))
      · refine Or.inl ?_
        rw [raise_seat_change_of_seated hstep hrev hcseat hcd]
        exact h
  | foundToTab y b =>
      have hcy : c ≠ y := by
        intro hcy
        obtain ⟨c', htop, hc'c, -, -⟩ := step_foundToTab_inv hstep
        rw [hc'c] at htop
        subst hcy
        exact hcnotfound (by simpa [State.foundTop] using lastOf_mem htop)
      refine Or.inl ?_
      rw [pull_seat_change hstep c hcy]
      exact h
  | tabToTab y b =>
      obtain ⟨-, -, hcp, -, -⟩ := step_tabToTab_inv hstep
      by_cases hcy : c = y
      · subst hcy
        cases b with
        | inl a' => exact absurd (canPlace_inl hcp).2 hking
        | inr z' =>
            refine Or.inr (Or.inl ⟨z', ?_⟩)
            rw [tfc_seat_point_edit hwf hstep hrev c, if_pos rfl]
      · refine Or.inl ?_
        rw [tfc_seat_point_edit hwf hstep hrev c, if_neg hcy]
        exact h

/-- The play-grade `.inl` tracker: the three-way seat disjunction is
carried along a whole reversible play (the `.inr`/foundation arms
ride the existing tracker, the `.inl` arm the step row above). -/
private theorem seat_track3_play {u v : State} {c : Card} {play : List Move}
    (hwf : u.WF) (hplay : ShufflePlayW u play v)
    (hking : c.rank ≠ Rank.king) {p : Anchor}
    (h : seatOf u c = some (Sum.inl p) ∨
      (∃ z, seatOf u c = some (Sum.inr z)) ∨ c ∈ u.found c.suit) :
    seatOf v c = some (Sum.inl p) ∨
      (∃ z, seatOf v c = some (Sum.inr z)) ∨ c ∈ v.found c.suit := by
  revert hwf h
  induction hplay with
  | nil st =>
      intro _ h
      exact h
  | @cons st s1 W m rest' hrev hstep hrest ih =>
      intro hwf h
      rcases h with h0 | h1 | h2
      · exact ih (step_wf hwf hstep) (seat_inl_track_step hwf hstep hrev hking h0)
      · exact ih (step_wf hwf hstep)
          (Or.inr (seat_track_step hwf hstep hrev hking (Or.inl h1)))
      · exact ih (step_wf hwf hstep)
          (Or.inr (seat_track_step hwf hstep hrev hking (Or.inr h2)))

/-- **The owner's seat lemma (2026-10-25).**  A swappable non-king
pair that is seated at all sits on card parents: `SwappableIn` +
non-king + both twins seated ⟹ both `.inr`-seated.  This is the
wedge for the OPEN original `fiber_transfer_corrected`
(`Orig2/ClaimsScrutiny.lean`): it upgrades the original's seat-blind
`pileHolding` premises to the `.inr` grade the proven transfer
rides on — the only swappable non-king pair that is not on cards is
a pair that is not on the board at all (the vacuous case,
`Orig2/VacuousSwap.lean`). -/
theorem seat_inr_of_swappable_nonking {s : State} {x : Card}
    (hwf : s.WF) (hnk : x.rank ≠ Rank.king)
    (hswap : SwappableIn s x)
    (hx : seatOf s x ≠ none) (hxt : seatOf s x.twin ≠ none) :
    (∃ z, seatOf s x = some (Sum.inr z)) ∧
      (∃ z : Card, seatOf s x.twin = some (Sum.inr z.twin)) := by
  obtain ⟨v, hrel, horb⟩ := hswap
  obtain ⟨h1, h2, -, -, -, -, -, -⟩ := hrel
  have hnkt : x.twin.rank ≠ Rank.king := by
    have htr : x.twin.rank = x.rank := by cases x; rfl
    rw [htr]
    exact hnk
  obtain ⟨π, hπ, -⟩ := sameOrbitSetoid.iseqv.symm horb
  have hwfv : v.WF :=
    run_wf hwf (Walk_run (P := fun st m => reversibleAtW st m) (st := s) (W := v) hπ)
  -- the seats, extracted without equation-casing a goal-occurring term
  -- (a `cases h : seatOf s x` would generalize the seat out of the
  -- goal itself; the have-blocks below keep the conclusion pristine)
  have hbx : ∃ bx : Base, seatOf s x = some bx := by
    cases hsx : seatOf s x with
    | none => exact absurd hsx hx
    | some bx => exact ⟨bx, rfl⟩
  obtain ⟨bx, hsx⟩ := hbx
  have hbt : ∃ bt : Base, seatOf s x.twin = some bt := by
    cases hstx : seatOf s x.twin with
    | none => exact absurd hstx hxt
    | some bt => exact ⟨bt, rfl⟩
  obtain ⟨bt, hstx⟩ := hbt
  cases bx with
  | inl p =>
      cases bt with
      | inl q =>
          exfalso
          have hpq : p ≠ q := by
            intro he
            have hstx' : seatOf s x.twin = some (Sum.inl p) := by rw [he]; exact hstx
            exact card_twin_ne x (seat_inl_unique hstx' hsx)
          have h1' : seatOf v x = some (Sum.inl q) := by rw [h1, hstx]
          rcases seat_track3_play hwf hπ hnk (Or.inl hsx) with hxv | ⟨z, hz⟩ | hmem
          · rw [hxv] at h1'
            injection h1' with e1
            injection e1 with e2
            exact hpq e2
          · rw [hz] at h1'; simp at h1'
          · exact absurd (seatOf_none_of_mem_found hwfv hmem) (by rw [h1']; simp)
      | inr w =>
          exfalso
          have h2' : seatOf v x.twin = some (Sum.inl p) := by rw [h2, hsx]
          rcases seat_track_play hwf hπ hnkt (Or.inl ⟨w, hstx⟩) with ⟨z, hz⟩ | hmem
          · rw [hz] at h2'; simp at h2'
          · exact absurd (seatOf_none_of_mem_found hwfv hmem) (by rw [h2']; simp)
  | inr z =>
      cases bt with
      | inl q =>
          exfalso
          have h1' : seatOf v x = some (Sum.inl q) := by rw [h1, hstx]
          rcases seat_track_play hwf hπ hnk (Or.inl ⟨z, hsx⟩) with ⟨z2, hz⟩ | hmem
          · rw [hz] at h1'; simp at h1'
          · exact absurd (seatOf_none_of_mem_found hwfv hmem) (by rw [h1']; simp)
      | inr w =>
          have hgoal : seatOf s x.twin = some (Sum.inr w.twin.twin) := by
            rw [card_twin_twin]
            exact hstx
          exact ⟨⟨z, hsx⟩, ⟨w.twin, hgoal⟩⟩

#print axioms seat_inr_of_swappable_nonking
