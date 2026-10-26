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
import Orig2.KingOrbitFull
import Orig2.KingSwapAssembly
import Orig2.VacuousSwap

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 2000000

/-!
# Orig2.FiberTransfer — the consolidated corrected fiber transfer

The owner's last-return route in ONE card.  This is the whole proof:

* `fiber_transfer_of_last_return` — **THE CORRECTED FIBER
  TRANSFER** (the `.inr`-seat grade): swap availability transfers along
  the class.
* `firstTouchRestart` — the `FirstTouchRestart` residual, proved: the
  excursion is never entered; the swap is RECONSTRUCTED at the last
  return.
* `swappableIn_transfer_of_pairFreePath` /
  `fiber_transfer_of_pair_free_path` — the pair-free transfer
  (the stepping-stone the reduction consumes).
* `seat_inr_of_swappable_nonking` — **THE OWNER'S SEAT LEMMA** (§8,
  fresh 2026-10-25): a swappable non-king pair that is seated at all
  sits on card parents — the wedge for the OPEN original statement.
* `fiber_transfer_of_nonking` — **THE NON-KING WRAPPER**
  (§9, fresh 2026-10-25): the OPEN original statement, proven under
  the single added hypothesis that the pair is non-king.
* `not_swappableIn_of_frozen` / `seat_inl_of_seated_king` — **THE
  FROZEN KING** (§10, fresh 2026-10-25, the owner's observation): a
  seated pair with either twin bottomed over a nonempty hidden deck
  is never strictly swappable — the king-grade parallel of §8's
  `.inl` corner; and a seated king always bottoms a pile.
* `sameOrbitVacant_of_swappableIn_king` — **THE CONSTRUCTIVE VACANCY
  SOURCE** (§12, fresh 2026-10-25): a swappable king pair forces the
  class to carry a vacancy — the first-seat-change extraction, the
  classical-free route the wrapper rides.
* `fiber_transfer_of_king` / `fiber_transfer_full`
  — **THE KING WRAPPER and THE FULL DISCHARGE** (§12, fresh
  2026-10-25): the king case closes (frozen corners vacuous, the
  transport carries `KingBottom` to the far end, the KingBottom-grade
  vacancy arm fires), and the full wrapper — the ORIGINAL statement
  verbatim, no rank split in the statement — is DISCHARGED.
* `fiber_transfer_seat_free` — **THE SEAT-FREE
  STRENGTHENING** (§13, fresh 2026-10-25, the owner's second
  observation): the original minus BOTH `pileHolding` premises —
  they are derivable (the strict letter's `foundsFixed` field kills
  mixed pairs; the founds row pins the seats both ways; the
  both-unseated corner is the certified vacuous swap).
* `fiber_transfer_founds_necessary` — **THE FOUNDS ROW IS
  NECESSARY** (§14, fresh 2026-10-25, the owner's challenge): the
  founds-free statement is FALSE, refuted by the twin-kings witness
  world (both kings on full foundations; one reversible pull onto
  the empty anchor strands a mixed pair at the far end).
* `fiber_transfer_twin_membership` — **THE TWIN-MEMBERSHIP
  WEAKENING** (§15, fresh 2026-10-25, the owner's third
  observation): the founds row collapses to twin-membership
  preservation — every read in the certified stack is a per-card
  membership transfer of the two twins, so the other fifty cards'
  foundation traffic is unconstrained.

The card rides ONLY the certified tracked substrate (the fifteen
imports above).  Every row restated from the retired dependency cards
carries its source citation, per the per-file private-kit norm:

* §1 — `PairFreeOrbit` and its kit (restated from
  `Orig2/TwinPairFreeClass.lean`), the splice functor
  `pairFreeOrbit_splice_of_pairFree` and `notFoundPair_relabelMover`
  (restated from `Archive/TwinLastPull.lean:75,201`).
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

/-! ## §1. Pair-free kit (restated from `Archive/TwinPairFreeClass.lean`
and `Orig2/TwinLastPull.lean` — the per-file kit norm) -/

/-- **`PairFreeOrbit x u v`** — `v` is reachable from `u` by a witness
shuffle that never raises or pulls either twin.
(restated from `Archive/TwinPairFreeClass.lean:55` — the per-file kit norm) -/
private def PairFreeOrbit (x : Card) (u v : State) : Prop :=
  ∃ play : List Move, ShufflePlayW u play v ∧ ∀ m ∈ play, NotFoundPair x m

/-- The empty play is pair-free.
(restated from `Archive/TwinPairFreeClass.lean:60` — the per-file kit norm) -/
private theorem pairFreeOrbit_refl (x : Card) (u : State) :
    PairFreeOrbit x u u :=
  ⟨[], Walk.nil u, by simp⟩

/-- Pair-free orbits compose by concatenating the plays.
(restated from `Archive/TwinPairFreeClass.lean:65` — the per-file kit norm) -/
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
(restated from `Archive/TwinPairFreeClass.lean:77` — the per-file kit norm) -/
private theorem pairFreeOrbit_of_play {x : Card} {u v : State} {play : List Move}
    (hplay : ShufflePlayW u play v)
    (hno : ∀ m ∈ play, NotFoundPair x m) :
    PairFreeOrbit x u v :=
  ⟨play, hplay, hno⟩

/-- A pair-free move stays pair-free after relabelling its mover.
(restated from `Archive/TwinLastPull.lean:75` — the per-file kit norm) -/
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
(restated from `Archive/TwinLastPull.lean:201` — the per-file kit norm) -/
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
`Orig2/TwinPairFreeRev.lean:43–133` — the per-file kit norm; the
`upCards_nodup` restatement retired 2026-10-25 — the public row
arrives by the `Orig2.KingSwapAssembly` import's transitive closure) -/

/-- The first-occurrence position of a member is unchanged by taking a
prefix that still contains it.
(restated from `Archive/TwinPairFreeRev.lean:48` — the per-file kit norm) -/
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
(restated from `Archive/TwinPairFreeRev.lean:78` — the per-file kit norm) -/
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
(restated from `Archive/TwinPairFreeRev.lean:105` — the per-file kit norm) -/
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
(restated from `Archive/TwinSelfArm.lean:30` — the per-file kit norm) -/
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
(restated from `Archive/TwinSelfArm.lean:50` — the per-file kit norm) -/
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
(restated from `Archive/TwinBothCovered.lean:249` — the per-file kit norm). -/
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
(restated from `Archive/TwinPairFreeTransfer.lean:60` — the per-file kit norm) -/
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
(restated from `Archive/TwinPairFreeTransfer.lean:85` — the per-file kit norm) -/
theorem fiber_transfer_of_pair_free_path :
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

#print axioms fiber_transfer_of_pair_free_path

/-! ## §5. Seat & parent kit (restated from `Archive/TwinForcedCancel.lean`,
`Orig2/TwinFoundationRow.lean`, `Orig2/TwinPreludeFunctor.lean` — the
per-file kit norm) -/

/-- Expose the first letter of a witness walk.
(restated from `Archive/TwinForcedCancel.lean:81` — the per-file kit norm) -/
private theorem walk_cons_inv {P : State → Move → Prop} {st s' : State}
    {m : Move} {ρ : List Move} (h : Walk P st (m :: ρ) s') :
    ∃ s1, P st m ∧ State.step st m = some s1 ∧ Walk P s1 ρ s' := by
  cases h with
  | cons hlet hstep hrest => exact ⟨_, hlet, hstep, hrest⟩

/-- A foundation card is off the tableau, hence unseated.
(restated from `Archive/TwinForcedCancel.lean:90` — the per-file kit norm) -/
private theorem seatOf_none_of_mem_found {s : State} (hwf : s.WF) {c : Card}
    (h : c ∈ s.found c.suit) : seatOf s c = none := by
  apply tfc_seatOf_none
  apply tfc_pileHolding_none
  intro a hmem
  exact ((mem_found_unique hwf h).1 a).2 hmem

/-- A successful raise appends the raised card to its foundation row.
(restated from `Archive/TwinFoundationRow.lean:107` — the per-file kit norm) -/
private theorem raise_found_self {s s1 : State} {c : Card}
    (hraise : State.step s (Move.tabToFound c) = some s1) :
    s1.found c.suit = s.found c.suit ++ [c] := by
  obtain ⟨-, a, -, hs1⟩ := step_tabToFound_inv hraise
  rw [hs1]
  exact setFound_found_self

/-- A card seated `.inr` on a card parent is not a king.
(restated from `Archive/TwinFoundationRow.lean:180` — the per-file kit norm) -/
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
(restated from `Archive/TwinPreludeFunctor.lean:433` — the per-file kit norm) -/
private theorem canSitOn_twin_left' (c b : Card) :
    canSitOn c.twin b = canSitOn c b := by
  rcases c with ⟨s, r⟩
  rcases b with ⟨s', r'⟩
  cases s <;> cases s' <;> rfl

/-- Two distinct twins cannot share the same direct parent: both would sit
at the same successor position in one legal run, contradicting the strict
rank descent.
(restated from `Archive/TwinPreludeFunctor.lean:442` — the per-file kit norm) -/
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
(restated from `Archive/TwinPreludeFunctor.lean:465` — the per-file kit norm) -/
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
(restated from `Archive/TwinFirstTouchReduction.lean:58` — the per-file
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
(restated from `Archive/TwinFirstTouchReduction.lean:100` — the per-file
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
(restated from `Archive/TwinFirstTouchReduction.lean:134` — the per-file
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
(restated from `Archive/TwinFirstTouchReduction.lean:151` — the per-file
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
(restated from `Archive/TwinFirstTouchReduction.lean:180` — the per-file
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
(restated from `Archive/TwinLastReturn.lean:487` — the per-file kit norm) -/
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
(restated from `Archive/TwinLastReturn.lean:510` — the per-file kit norm) -/
theorem fiber_transfer_of_last_return :
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
#print axioms fiber_transfer_of_last_return

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
wedge for the OPEN original `fiber_transfer`
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

/-! ## §9. The boarding lemma and the non-king wrapper (fresh,
2026-10-25)

The original statement's unseated corners die twice over: a twin on
its foundation row is pinned by the founds-equality premise (it is
still on the foundation at `s'`, contradicting `pileHolding`), and a
twin off the board anywhere else (stock, waste, hidden) can never
BOARD reversibly — every boarding letter except the pull is
irreversible (`wasteToFound`/`wasteToTab` never undo; a reveal
strictly drops `hiddenTotal`, and `not_W_of_desc` kills it), and the
pull itself needs foundation membership.  With those corners gone
and the owner's seat lemma supplying the `.inr` grade at the source,
the proven transfer applies — the original statement follows for
non-king pairs.  Kings remain the open corner. -/

/-- The none-seat pins the holding search: an unseated card is held
by no pile. -/
private theorem pileHolding_none_of_seatOf_none {s : State} {c : Card}
    (h : seatOf s c = none) : s.pileHolding c = none := by
  cases hph : s.pileHolding c with
  | none => rfl
  | some k =>
      rw [tfc_seatOf_pair hph] at h
      cases hg : List.getLast? (below c (s.piles k).faceUp) with
      | none => rw [hg] at h; exact absurd h (by simp)
      | some z => rw [hg] at h; exact absurd h (by simp)

/-- A face-up member is seated. -/
private theorem seatOf_ne_none_of_mem_faceUp {s : State} {c : Card} {a : Anchor}
    (h : c ∈ (s.piles a).faceUp) : seatOf s c ≠ none := by
  intro hse
  exact (tfc_not_mem_faceUp_of_holdNone (pileHolding_none_of_seatOf_none hse) a) h

/-- A card held by a pile is seated. -/
private theorem seatOf_ne_none_of_pileHolding {s : State} {c : Card} {a : Anchor}
    (h : s.pileHolding c = some a) : seatOf s c ≠ none := by
  rw [tfc_seatOf_pair h]
  cases hg : List.getLast? (below c (s.piles a).faceUp) with
  | none => simp [hg]
  | some z => simp [hg]

/-- An unseated card is in no face-up pile. -/
private theorem not_mem_faceUp_of_seatOf_none {s : State} {c : Card}
    (h : seatOf s c = none) (a : Anchor) : c ∉ (s.piles a).faceUp :=
  tfc_not_mem_faceUp_of_holdNone (pileHolding_none_of_seatOf_none h) a

/-- **The boarding step lemma.**  Through a reversible letter, an
off-board card that is not on its foundation row stays off the
board: every boarding route except the pull is irreversible (the
waste routes never undo; a reveal strictly drops `hiddenTotal`, and
`not_W_of_desc` kills it), and the pull needs foundation membership,
which only the raise of that very card could grant — and the raise
needs the card seated. -/
private theorem unseated_track_step {u v : State} {m : Move} {c : Card}
    (hwf : u.WF) (hstep : State.step u m = some v) (hrev : reversibleAtW u m)
    (hseat : seatOf u c = none) (hnotfound : c ∉ u.found c.suit) :
    seatOf v c = none ∧ c ∉ v.found c.suit := by
  cases m with
  | draw =>
      have hse := (chart_draw hstep).1
      have hfo := (chart_draw hstep).2.1
      refine ⟨by rw [hse c]; exact hseat, ?_⟩
      intro hmem
      exact hnotfound (by rw [hfo c.suit]; exact hmem)
  | wasteToFound y => exact absurd hrev (wasteToFound_not_reversibleAtW u y)
  | wasteToTab y b => exact absurd hrev (wasteToTab_not_reversibleAtW u y b)
  | tabToFound y =>
      obtain ⟨-, a, hpa, hs⟩ := step_tabToFound_inv hstep
      have hcy : c ≠ y := by
        intro hcy
        subst hcy
        obtain ⟨-, hlast⟩ := tfc_pileOfTop_top hpa
        exact (seatOf_ne_none_of_mem_faceUp (lastOf_mem hlast)) hseat
      refine ⟨?_, ?_⟩
      · apply tfc_seatOf_none
        apply tfc_pileHolding_none
        intro a'
        by_cases haa' : a' = a
        · rw [haa']
          have hpilea : v.piles a =
              Pile.afterRunRemoved (u.piles a) (chop (u.piles a).faceUp) := by
            rw [hs]
            show (if a = a then
                Pile.afterRunRemoved (u.piles a) (chop (u.piles a).faceUp)
              else u.piles a) =
              Pile.afterRunRemoved (u.piles a) (chop (u.piles a).faceUp)
            rw [ite_eq_left rfl]
          cases hchop : chop (u.piles a).faceUp with
          | cons z zs =>
              have hcchop : c ∉ z :: zs := by
                have hmchop : c ∉ chop (u.piles a).faceUp := fun hc =>
                  not_mem_faceUp_of_seatOf_none hseat a (chop_mem hc)
                rw [hchop] at hmchop
                exact hmchop
              rw [hpilea, hchop]
              exact hcchop
          | nil =>
              cases hhidden : (u.piles a).hidden with
              | cons h t =>
                  exfalso
                  have hdrop : hiddenTotal v + 1 ≤ hiddenTotal u :=
                    hiddenTotal_step_tabToFound_reveal hstep hpa hchop
                      (by rw [hhidden]; simp)
                  exact absurd hrev (not_W_of_desc hiddenTotal
                    (fun s m s' hst => hiddenTotal_step hst) hstep
                    (Nat.lt_of_succ_le hdrop))
              | nil =>
                  rw [hpilea, hchop]
                  simp [Pile.afterRunRemoved, Pile.revealTop, hhidden]
        · rw [hs]
          show c ∉ (if a' = a then
              Pile.afterRunRemoved (u.piles a) (chop (u.piles a).faceUp)
            else u.piles a').faceUp
          rw [ite_eq_right haa']
          exact not_mem_faceUp_of_seatOf_none hseat a'
      · intro hmem
        rw [hs] at hmem
        by_cases hys : c.suit = y.suit
        · rw [hys] at hmem hnotfound
          rw [setFound_found_self] at hmem
          rcases List.mem_append.mp hmem with h' | h'
          · exact hnotfound h'
          · exact hcy (List.mem_singleton.mp h')
        · rw [setFound_found_ne hys] at hmem
          exact hnotfound hmem
  | foundToTab y b =>
      have hcy : c ≠ y := by
        intro hcy
        obtain ⟨c', htop, hc'c, -, -⟩ := step_foundToTab_inv hstep
        rw [hc'c] at htop
        subst hcy
        exact hnotfound (by simpa [State.foundTop] using lastOf_mem htop)
      refine ⟨by rw [pull_seat_change hstep c hcy]; exact hseat, ?_⟩
      intro hmem
      obtain ⟨-, -, -, -, hs⟩ := step_foundToTab_inv hstep
      rw [hs] at hmem
      have hfound : ((u.setFound y.suit (chop (u.found y.suit))).putCard y b).found
          = (u.setFound y.suit (chop (u.found y.suit))).found := by
        cases b with
        | inl t => rw [putCard_inl_found]
        | inr z => rw [putCard_inr_found]
      rw [hfound] at hmem
      by_cases hys : c.suit = y.suit
      · rw [hys] at hmem hnotfound
        rw [setFound_found_self] at hmem
        exact hnotfound (chop_mem hmem)
      · rw [setFound_found_ne hys] at hmem
        exact hnotfound hmem
  | tabToTab y b =>
      obtain ⟨a0, hhold, -, -, hs⟩ := step_tabToTab_inv hstep
      have hcy : c ≠ y := by
        intro hcon
        subst hcon
        exact (seatOf_ne_none_of_mem_faceUp (pileHolding_mem hhold)) hseat
      refine ⟨by
          rw [tfc_seat_point_edit hwf hstep hrev c, ite_eq_right hcy]
          exact hseat, ?_⟩
      intro hmem
      rw [hs, putRun_found, setPile_found] at hmem
      exact hnotfound hmem

/-- **The boarding play lemma.**  Along a whole reversible play, an
off-board card that is not on its foundation row stays off the
board. -/
private theorem unseated_track_play {u v : State} {c : Card} {play : List Move}
    (hwf : u.WF) (hplay : ShufflePlayW u play v)
    (hseat : seatOf u c = none) (hnotfound : c ∉ u.found c.suit) :
    seatOf v c = none ∧ c ∉ v.found c.suit := by
  revert hwf hseat hnotfound
  induction hplay with
  | nil st =>
      intro _ hseat hnotfound
      exact ⟨hseat, hnotfound⟩
  | @cons st s1 W m rest' hrev hstep hrest ih =>
      intro hwf hseat hnotfound
      obtain ⟨hseat1, hnotfound1⟩ := unseated_track_step hwf hstep hrev hseat hnotfound
      exact ih (step_wf hwf hstep) hseat1 hnotfound1

/-- **THE NON-KING WRAPPER.**  The OPEN original statement
(`Orig2/ClaimsScrutiny.lean` — the `pileHolding`-grade seats,
verbatim except the founds row WEAKENED to twin-membership
preservation, §15) under the single added hypothesis that the
pair is non-king.  Route: the owner's seat lemma (§8) upgrades the
source to the `.inr` grade; the existing tracker carries both twins
to `.inr`-or-foundation at `s'`, where `pileHolding` kills the
foundation arm; the unseated corners are vacuous (a foundation twin
is pinned by the forward membership arrow; stock/waste/hidden twins
can never board reversibly — §9's boarding lemma); the proven
`.inr`-grade transfer finishes.  Kings remain the open corner. -/
theorem fiber_transfer_of_nonking :
    ∀ (s s' : State) (x : Card), s.WF → s'.WF →
      sameOrbitSetoid.r s s' →
      (x ∈ s.found x.suit → x ∈ s'.found x.suit) →
      (x.twin ∈ s.found x.twin.suit → x.twin ∈ s'.found x.twin.suit) →
      x.rank ≠ Rank.king →
      (∃ v, twinPairSwapStrict s v x ∧ sameOrbitSetoid.r s v) →
      (∃ seatA, s'.pileHolding x = some seatA) →
      (∃ seatA', s'.pileHolding x.twin = some seatA') →
      (∃ v', twinPairSwapStrict s' v' x ∧ sameOrbitSetoid.r s' v') := by
  intro s s' x hwf hwf' hclass hxw hxtw hnk hswap hholdx hholdxt
  obtain ⟨seatA, hseatA⟩ := hholdx
  obtain ⟨seatA', hseatA'⟩ := hholdxt
  have hseatx' : seatOf s' x ≠ none := seatOf_ne_none_of_pileHolding hseatA
  have hseatxt' : seatOf s' x.twin ≠ none := seatOf_ne_none_of_pileHolding hseatA'
  obtain ⟨π, hπ, -⟩ := sameOrbitSetoid.iseqv.symm hclass
  have hnkt : x.twin.rank ≠ Rank.king := by
    have htr : x.twin.rank = x.rank := by cases x; rfl
    rw [htr]
    exact hnk
  by_cases hseats : seatOf s x = none
  · exfalso
    by_cases hnotf : x ∈ s.found x.suit
    · exact hseatx' (seatOf_none_of_mem_found hwf' (hxw hnotf))
    · obtain ⟨hseat', -⟩ := unseated_track_play hwf hπ hseats hnotf
      exact hseatx' hseat'
  · by_cases hseatst : seatOf s x.twin = none
    · exfalso
      by_cases hnotft : x.twin ∈ s.found x.twin.suit
      · exact hseatxt' (seatOf_none_of_mem_found hwf' (hxtw hnotft))
      · obtain ⟨hseatt', -⟩ := unseated_track_play hwf hπ hseatst hnotft
        exact hseatxt' hseatt'
    · obtain ⟨hsx, hstx⟩ :=
        seat_inr_of_swappable_nonking hwf hnk hswap hseats hseatst
      have hstx' : (∃ z, seatOf s x.twin = some (Sum.inr z)) := by
        obtain ⟨z, hz⟩ := hstx
        exact ⟨z.twin, hz⟩
      rcases seat_track_play hwf hπ hnk (Or.inl hsx) with ⟨z1, hz1⟩ | hfx
      · rcases seat_track_play hwf hπ hnkt (Or.inl hstx') with ⟨z2, hz2⟩ | hfxt
        · have hz2t : ∃ z : Card, seatOf s' x.twin = some (Sum.inr z.twin) :=
            ⟨z2.twin, by rw [card_twin_twin]; exact hz2⟩
          exact fiber_transfer_of_last_return s s' x hwf hwf' hclass
            hsx hstx ⟨z1, hz1⟩ hz2t hswap
        · exfalso
          exact hseatxt' (seatOf_none_of_mem_found hwf' hfxt)
      · exfalso
        exact hseatx' (seatOf_none_of_mem_found hwf' hfx)

#print axioms fiber_transfer_of_nonking

/-! ## §10. The frozen king (the owner's observation, 2026-10-25)

A bottomed card over a nonempty hidden deck can never leave its
anchor through a reversible play: every exit — the whole-pile slide
(the run from the bottom) or the raise of that very card (firing
forces it to be the pile top too, hence a singleton by `WF`'s
no-duplicate clause) — empties the face-up run and fires the reveal,
strictly dropping `hiddenTotal`; the certified ratchet
(`not_W_of_desc`) kills the letter.  This is the king-grade parallel
of the owner's non-king wedge (§8): a non-king at a pile bottom
cannot ENTER another anchor; a non-`KingBottom` king cannot LEAVE
its own.  Either way the strict exchange witness cannot exist. -/

/-- **The frozen-anchor step.**  Through a reversible letter, a card
bottomed at anchor `a` over a nonempty hidden deck stays there, and
the hidden deck is untouched. -/
private theorem frozen_king_step {u v : State} {m : Move} {c : Card} {a : Anchor}
    (hwf : u.WF) (hstep : State.step u m = some v) (hrev : reversibleAtW u m)
    (hseat : seatOf u c = some (Sum.inl a)) (hhid : (u.piles a).hidden ≠ []) :
    seatOf v c = some (Sum.inl a) ∧ (v.piles a).hidden = (u.piles a).hidden := by
  have hcseat : seatOf u c ≠ none := by rw [hseat]; simp
  have hhold : u.pileHolding c = some a := (tfc_seatOf_of_inl hseat).1
  have hbelow : below c (u.piles a).faceUp = [] := (tfc_seatOf_of_inl hseat).2
  have hmema : c ∈ (u.piles a).faceUp := pileHolding_mem hhold
  cases m with
  | draw =>
      have hse := (chart_draw hstep).1
      obtain ⟨⟨hhidp, -⟩, -⟩ := (chart_draw hstep).2.2
      exact ⟨by rw [hse c]; exact hseat, (hhidp a).symm⟩
  | wasteToFound y => exact absurd hrev (wasteToFound_not_reversibleAtW u y)
  | wasteToTab y b => exact absurd hrev (wasteToTab_not_reversibleAtW u y b)
  | tabToFound d =>
      obtain ⟨-, a₀, hpa, hs⟩ := step_tabToFound_inv hstep
      by_cases hcd : c = d
      · -- the raise of the frozen card itself: firing forces it to be the
        -- pile top; bottoming the pile too, WF's no-duplicate clause makes
        -- the pile the singleton [c] — the reveal fires — irreversible
        exfalso
        have hpa' : u.pileOfTop c = some a₀ := by rw [hcd]; exact hpa
        have hmem₀ : c ∈ (u.piles a₀).faceUp := by
          obtain ⟨-, hlast⟩ := tfc_pileOfTop_top hpa'
          exact lastOf_mem hlast
        have haa₀ : a = a₀ := by
          by_cases h : a = a₀
          · exact h
          · exact absurd hmem₀ ((mem_faceUp_unique hwf hmema a₀ (fun h' => h h'.symm)).1)
        have hlasta : lastOf (u.piles a).faceUp = some c := by
          rw [haa₀]; exact (tfc_pileOfTop_top hpa').2
        have hnd : (u.piles a).faceUp.Nodup := runOK_nodup (hwf.runOK_of a)
        have hsingle : (u.piles a).faceUp = [c] :=
          eq_singleton_of_below_nil_lastOf hnd hbelow hlasta
        have hdrop : hiddenTotal v + 1 ≤ hiddenTotal u :=
          hiddenTotal_step_tabToFound_reveal hstep hpa
            (by rw [← haa₀, hsingle]; rfl) (by rw [← haa₀]; exact hhid)
        exact absurd hrev (not_W_of_desc hiddenTotal
          (fun s m s' hst => hiddenTotal_step hst) hstep (Nat.lt_of_succ_le hdrop))
      · refine ⟨by
            rw [raise_seat_change_of_seated hstep hrev hcseat hcd]
            exact hseat, ?_⟩
        rw [hs]
        show (if a = a₀ then
            Pile.afterRunRemoved (u.piles a₀) (chop (u.piles a₀).faceUp)
          else u.piles a).hidden = (u.piles a).hidden
        by_cases haa₀ : a = a₀
        · rw [haa₀, ite_eq_left rfl]
          rcases afterRunRemoved_hidden (u.piles a₀) (chop (u.piles a₀).faceUp) with
            ⟨hne, heq⟩ | ⟨-, hhd, -⟩ | ⟨hch, -, -⟩
          · exact heq
          · exact absurd (by rw [haa₀]; exact hhd) hhid
          · exfalso
            exact absurd hrev (not_W_of_desc hiddenTotal
              (fun s m s' hst => hiddenTotal_step hst) hstep
              (Nat.lt_of_succ_le (hiddenTotal_step_tabToFound_reveal hstep hpa hch
                (by rw [← haa₀]; exact hhid))))
        · rw [ite_eq_right haa₀]
  | foundToTab y b =>
      obtain ⟨c', htop, hc'c, hcp, hs⟩ := step_foundToTab_inv hstep
      rw [hc'c] at htop
      have hcy : c ≠ y := by
        intro hcy
        rw [← hcy] at htop
        have hcf : c ∈ u.found c.suit := by
          simpa [State.foundTop] using lastOf_mem htop
        exact ((mem_found_unique hwf hcf).1 a).2 hmema
      refine ⟨by rw [pull_seat_change hstep c hcy]; exact hseat, ?_⟩
      rw [hs]
      cases b with
      | inl t =>
          have ht : t ≠ a := by
            intro ht
            obtain ⟨hemp, -⟩ := canPlace_inl hcp
            rw [ht] at hemp
            exact absurd (Pile.isEmpty_eq_false_of_mem hmema) (by rw [hemp]; simp)
          rw [putCard_piles_inl]
          show (if a = t then ({ hidden := [], faceUp := [y] } : Pile)
            else (u.setFound y.suit (chop (u.found y.suit))).piles a).hidden
            = (u.piles a).hidden
          rw [ite_eq_right (fun h => ht h.symm)]
          rfl
      | inr z =>
          cases hz : (u.setFound y.suit (chop (u.found y.suit))).pileOfTop z with
          | none =>
              have hid : (u.setFound y.suit (chop (u.found y.suit))).putCard y (Sum.inr z)
                  = u.setFound y.suit (chop (u.found y.suit)) := by
                simp only [State.putCard, hz]
              rw [hid]
              rfl
          | some k =>
              rw [putCard_piles_inr _ _ _ _ hz]
              by_cases hka : a = k
              · rw [hka]
                show (if k = k then
                    { (u.setFound y.suit (chop (u.found y.suit))).piles k with
                      faceUp := ((u.setFound y.suit (chop (u.found y.suit))).piles k).faceUp ++ [y] }
                  else (u.setFound y.suit (chop (u.found y.suit))).piles k).hidden
                  = (u.piles k).hidden
                rw [ite_eq_left rfl]
                rfl
              · show (if a = k then
                    { (u.setFound y.suit (chop (u.found y.suit))).piles k with
                      faceUp := ((u.setFound y.suit (chop (u.found y.suit))).piles k).faceUp ++ [y] }
                  else (u.setFound y.suit (chop (u.found y.suit))).piles a).hidden
                  = (u.piles a).hidden
                rw [ite_eq_right hka]
                rfl
  | tabToTab y b =>
      obtain ⟨a₀, hhold₀, hcp, -, hs⟩ := step_tabToTab_inv hstep
      by_cases hcy : c = y
      · -- the whole-pile slide of the frozen card: the below-run is
        -- empty (it bottoms the pile) — the reveal fires — irreversible
        exfalso
        rw [← hcy] at hhold₀
        have haa : a₀ = a := Option.some.inj (hhold₀.symm.trans hhold)
        rw [haa] at hhold₀
        have hholdy : u.pileHolding y = some a := by rw [← hcy]; exact hhold₀
        have hbelowy : below y (u.piles a).faceUp = [] := by
          rw [← hcy]; exact hbelow
        have hdrop : hiddenTotal v + 1 ≤ hiddenTotal u :=
          hiddenTotal_step_tabToTab_reveal hstep hholdy hbelowy hhid
        exact absurd hrev (not_W_of_desc hiddenTotal
          (fun s m s' hst => hiddenTotal_step hst) hstep (Nat.lt_of_succ_le hdrop))
      · refine ⟨by
            rw [tfc_seat_point_edit hwf hstep hrev c, ite_eq_right hcy]
            exact hseat, ?_⟩
        have hmemy : y ∈ (u.piles a₀).faceUp := pileHolding_mem hhold₀
        rw [hs]
        by_cases haa₀ : a = a₀
        · -- the source pile is ours: y is not the bottom (c is), so the
          -- below-run is nonempty — no reveal — hidden preserved
          rw [haa₀, tabToTab_a_hidden u a₀ y b hmemy hcp]
          rcases afterRunRemoved_hidden (u.piles a₀) (below y (u.piles a₀).faceUp) with
            ⟨hne, heq⟩ | ⟨-, hhd, -⟩ | ⟨hbl, -, -⟩
          · exact heq
          · exact absurd (by rw [haa₀]; exact hhd) hhid
          · exfalso
            have hbc : below c (u.piles a₀).faceUp = [] := by
              rw [← haa₀]; exact hbelow
            cases hl : (u.piles a₀).faceUp with
            | nil => exact absurd hmemy (by rw [hl]; simp)
            | cons z t =>
                have h1 : z = y := by
                  have hb := hbl
                  rw [hl] at hb
                  exact head_of_below_nil hb
                have h2 : z = c := by
                  have hb := hbc
                  rw [hl] at hb
                  exact head_of_below_nil hb
                exact hcy (h2.symm.trans h1)
        · -- our pile is not the source: setPile leaves it; the putRun
          -- destination either is not it, or appends without touching
          -- the hidden deck (an .inl landing needs the pile empty, and
          -- c sits there)
          cases b with
          | inl t =>
              have ht : t ≠ a := by
                intro ht
                obtain ⟨hemp, -⟩ := canPlace_inl hcp
                rw [ht] at hemp
                exact absurd (Pile.isEmpty_eq_false_of_mem hmema)
                  (by rw [hemp]; simp)
              rw [putRun_piles_inl_ne _ _ t a (fun h => ht h.symm)]
              rw [setPile_piles_ne haa₀]
          | inr z =>
              cases hz : (u.setPile a₀
                  (Pile.afterRunRemoved (u.piles a₀)
                    (below y (u.piles a₀).faceUp))).pileOfTop z with
              | none =>
                  have hid : (u.setPile a₀ (Pile.afterRunRemoved (u.piles a₀)
                      (below y (u.piles a₀).faceUp))).putRun
                      (fromCard y (u.piles a₀).faceUp) (Sum.inr z)
                      = u.setPile a₀ (Pile.afterRunRemoved (u.piles a₀)
                        (below y (u.piles a₀).faceUp)) := by
                    simp only [State.putRun, hz]
                  rw [hid, setPile_piles_ne haa₀]
              | some k =>
                  by_cases hka : a = k
                  · rw [hka, putRun_piles_inr_self _ _ _ _ hz]
                    show ((u.setPile a₀ (Pile.afterRunRemoved (u.piles a₀)
                      (below y (u.piles a₀).faceUp))).piles k).hidden
                      = (u.piles k).hidden
                    rw [setPile_piles_ne (fun h => haa₀ (hka.trans h))]
                  · rw [putRun_piles_inr_ne _ _ _ _ hz hka, setPile_piles_ne haa₀]

/-- **The frozen-anchor play.**  Along a whole reversible play, a card
bottomed at anchor `a` over a nonempty hidden deck never leaves it. -/
private theorem frozen_king_play {u v : State} {c : Card} {a : Anchor} {play : List Move}
    (hwf : u.WF) (hplay : ShufflePlayW u play v)
    (hseat : seatOf u c = some (Sum.inl a)) (hhid : (u.piles a).hidden ≠ []) :
    seatOf v c = some (Sum.inl a) := by
  revert hwf hseat hhid
  induction hplay with
  | nil st => intro _ hseat _; exact hseat
  | @cons st s1 W m rest' hrev hstep hrest ih =>
      intro hwf hseat hhid
      obtain ⟨hseat1, hhid1⟩ := frozen_king_step hwf hstep hrev hseat hhid
      exact ih (step_wf hwf hstep) hseat1 (fun h => hhid (hhid1.symm.trans h))

/-- **The owner's frozen-king row (2026-10-25).**  A seated pair with
either twin bottomed over a nonempty hidden deck is never strictly
swappable — the king-grade parallel of the non-king `.inl` corner
(§8): a non-king at a pile bottom cannot ENTER another anchor; a
non-`KingBottom` king cannot LEAVE its own.  Either way the strict
exchange witness cannot exist. -/
theorem not_swappableIn_of_frozen {s : State} {x : Card} {a a' : Anchor}
    (hwf : s.WF)
    (hx : seatOf s x = some (Sum.inl a)) (hxt : seatOf s x.twin = some (Sum.inl a'))
    (hne : a ≠ a')
    (hhid : (s.piles a).hidden ≠ []) :
    ¬ SwappableIn s x := by
  rintro ⟨v, hstrict, horb⟩
  obtain ⟨π, hπ, -⟩ := sameOrbitSetoid.iseqv.symm horb
  have hfrozen := frozen_king_play hwf hπ hx hhid
  have h1 : seatOf v x = some (Sum.inl a') := by rw [hstrict.1]; exact hxt
  exact hne (Sum.inl.inj (Option.some.inj (hfrozen.symm.trans h1)))

/-- **A seated king bottoms a pile** — kings never sit on card
parents (nothing ranks above a king), so a seated king is always
`.inl`-seated. -/
theorem seat_inl_of_seated_king {s : State} {x : Card}
    (hwf : s.WF) (hking : x.rank = Rank.king) (hx : seatOf s x ≠ none) :
    ∃ a, seatOf s x = some (Sum.inl a) := by
  have hbx : ∃ bx : Base, seatOf s x = some bx := by
    cases hbx' : seatOf s x with
    | none => exact absurd hbx' hx
    | some bx => exact ⟨bx, rfl⟩
  obtain ⟨bx, hbx⟩ := hbx
  cases bx with
  | inl a => exact ⟨a, hbx⟩
  | inr z => exact absurd hking (seated_inr_rank_ne_king hwf hbx)

#print axioms not_swappableIn_of_frozen
#print axioms seat_inl_of_seated_king

/-! ## §11. The hidden transport (fresh, 2026-10-25)

Reversible plays never touch a hidden deck (the certified ledger
row `rev_step_hidden_eq`, promoted at `Orig2/SeatMateStack.lean` for
consumption by name), and a king only takes a tableau seat by an
`.inl` landing on an EMPTY pile (nothing sits on a king), where the
landing letter itself writes `hidden := []`.  So the `KingBottom`
property rides along the class: a king that bottoms a `hidden = []`
pile at the start of a reversible journey — or takes seat afresh
along it — ends (if seated at all) bottomed over an empty hidden
deck.  This is the row the run-topped king arm consumes: it makes
the twins' piles `KingBottom` at the far end of the class. -/

/-- The transport step, seated case: a king bottomed over an empty
hidden deck ends (if seated) over an empty hidden deck — the seat is
preserved (and the reversible letter keeps every hidden deck) or
re-taken by an `.inl` landing (which writes `hidden := []`). -/
private theorem king_hidden_step_seated {u v : State} {m : Move} {c : Card}
    (hwf : u.WF) (hstep : State.step u m = some v) (hrev : reversibleAtW u m)
    (hking : c.rank = Rank.king) {a : Anchor}
    (hseat : seatOf u c = some (Sum.inl a)) (hhid : (u.piles a).hidden = [])
    (hseated : seatOf v c ≠ none) :
    ∃ â, seatOf v c = some (Sum.inl â) ∧ (v.piles â).hidden = [] := by
  cases m with
  | draw =>
      have hse := (chart_draw hstep).1
      exact ⟨a, by rw [hse c]; exact hseat,
        by rw [rev_step_hidden_eq hwf hstep hrev a]; exact hhid⟩
  | wasteToFound y => exact absurd hrev (wasteToFound_not_reversibleAtW u y)
  | wasteToTab y b => exact absurd hrev (wasteToTab_not_reversibleAtW u y b)
  | tabToFound d =>
      by_cases hcd : c = d
      · -- the raise of the king itself: it leaves the board
        exfalso
        subst hcd
        have hmem : c ∈ v.found c.suit := by
          rw [raise_found_self hstep]
          exact List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl))
        exact hseated (seatOf_none_of_mem_found (step_wf hwf hstep) hmem)
      · exact ⟨a, by
            rw [raise_seat_change_of_seated hstep hrev (by rw [hseat]; simp) hcd]
            exact hseat,
          by rw [rev_step_hidden_eq hwf hstep hrev a]; exact hhid⟩
  | foundToTab y b =>
      -- a seated card is not on its foundation row: the pull of c
      -- itself cannot fire
      have hcy : c ≠ y := by
        intro hcy
        subst hcy
        obtain ⟨c', htop, hc'c, -, -⟩ := step_foundToTab_inv hstep
        rw [hc'c] at htop
        have hmem : c ∈ u.found c.suit := by
          simpa [State.foundTop] using lastOf_mem htop
        exact ((mem_found_unique hwf hmem).1 a).2
          (pileHolding_mem (tfc_seatOf_of_inl hseat).1)
      exact ⟨a, by rw [pull_seat_change hstep c hcy]; exact hseat,
        by rw [rev_step_hidden_eq hwf hstep hrev a]; exact hhid⟩
  | tabToTab y b =>
      by_cases hcy : c = y
      · subst hcy
        obtain ⟨a₀, hhold₀, hcp, hrun, hs⟩ := step_tabToTab_inv hstep
        cases b with
        | inl t =>
            refine ⟨t, by rw [tfc_seat_point_edit hwf hstep hrev c, ite_eq_left rfl], ?_⟩
            rw [hs, putRun_piles_inl_self]
        | inr z =>
            exfalso
            obtain ⟨-, -, hfit⟩ := canPlace_inr hcp
            rw [canSitOn_king_false hking] at hfit
            exact Bool.noConfusion hfit
      · exact ⟨a, by
            rw [tfc_seat_point_edit hwf hstep hrev c, ite_eq_right hcy]
            exact hseat,
          by rw [rev_step_hidden_eq hwf hstep hrev a]; exact hhid⟩

/-- The transport step, off-board case: a king off the board only
re-lands by the pull of itself onto an empty anchor, whose pile the
letter writes `hidden := []`. -/
private theorem king_hidden_step_off {u v : State} {m : Move} {c : Card}
    (hwf : u.WF) (hstep : State.step u m = some v) (hrev : reversibleAtW u m)
    (hking : c.rank = Rank.king) (hnone : seatOf u c = none)
    (hseated : seatOf v c ≠ none) :
    ∃ â, seatOf v c = some (Sum.inl â) ∧ (v.piles â).hidden = [] := by
  by_cases hnf : c ∈ u.found c.suit
  · cases m with
    | draw =>
        exfalso
        have hfo := (chart_draw hstep).2.1
        exact hseated (seatOf_none_of_mem_found (step_wf hwf hstep)
          (by rw [← hfo c.suit]; exact hnf))
    | wasteToFound y => exact absurd hrev (wasteToFound_not_reversibleAtW u y)
    | wasteToTab y b => exact absurd hrev (wasteToTab_not_reversibleAtW u y b)
    | tabToFound d =>
        exfalso
        have hmem : c ∈ v.found c.suit :=
          found_mem_step hstep hnf (fun b' hb' => Move.noConfusion hb')
        exact hseated (seatOf_none_of_mem_found (step_wf hwf hstep) hmem)
    | foundToTab y b =>
        by_cases hcy : c = y
        · subst hcy
          obtain ⟨-, -, -, hcp, hs⟩ := step_foundToTab_inv hstep
          cases b with
          | inl t =>
              refine ⟨t, ?_, ?_⟩
              · have hface : (v.piles t).faceUp = [c] ∧ (v.piles t).hidden = [] := by
                  rw [hs, putCard_piles_inl]
                  show (if t = t then ({ hidden := [], faceUp := [c] } : Pile)
                    else (u.setFound c.suit (chop (u.found c.suit))).piles t).faceUp = [c] ∧
                    (if t = t then ({ hidden := [], faceUp := [c] } : Pile)
                    else (u.setFound c.suit (chop (u.found c.suit))).piles t).hidden = []
                  rw [ite_eq_left rfl]
                  exact ⟨rfl, rfl⟩
                have hmemb : c ∈ (v.piles t).faceUp := by
                  rw [hface.1]; exact List.mem_singleton.mpr rfl
                have hbelow : below c (v.piles t).faceUp = [] := by
                  rw [hface.1, below_cons, ite_eq_left rfl]
                have hhold : v.pileHolding c = some t :=
                  tfc_pileHolding_pin hmemb
                    (fun j hj => (mem_faceUp_unique (step_wf hwf hstep) hmemb j hj).1)
                exact tfc_seatOf_inl_intro hhold hbelow
              · rw [hs, putCard_piles_inl]
                show (if t = t then ({ hidden := [], faceUp := [c] } : Pile)
                  else (u.setFound c.suit (chop (u.found c.suit))).piles t).hidden = []
                rw [ite_eq_left rfl]
          | inr z =>
              exfalso
              obtain ⟨-, -, hfit⟩ := canPlace_inr hcp
              rw [canSitOn_king_false hking] at hfit
              exact Bool.noConfusion hfit
        · exfalso
          have hmem : c ∈ v.found c.suit :=
            found_mem_step hstep hnf
              (fun b' hb' => hcy (Move.foundToTab.inj hb').1.symm)
          exact hseated (seatOf_none_of_mem_found (step_wf hwf hstep) hmem)
    | tabToTab y b =>
        exfalso
        have hmem : c ∈ v.found c.suit :=
          found_mem_step hstep hnf (fun b' hb' => Move.noConfusion hb')
        exact hseated (seatOf_none_of_mem_found (step_wf hwf hstep) hmem)
  · exfalso
    obtain ⟨hseat', -⟩ := unseated_track_step hwf hstep hrev hnone hnf
    exact hseated hseat'

/-- **The hidden transport.**  Along a whole reversible play, a king
ends (if seated at all) bottomed over an empty hidden deck, provided
it started so — or started off-board (re-landings write
`hidden := []` themselves). -/
theorem king_pile_hidden_empty_play {u v : State} {c : Card} {play : List Move}
    (hwf : u.WF) (hplay : ShufflePlayW u play v) (hking : c.rank = Rank.king)
    (hbase : seatOf u c ≠ none → ∃ a, seatOf u c = some (Sum.inl a) ∧
      (u.piles a).hidden = []) :
    seatOf v c ≠ none → ∃ â, seatOf v c = some (Sum.inl â) ∧ (v.piles â).hidden = [] := by
  revert hwf hbase
  induction hplay with
  | nil st =>
      intro _ hbase hseated
      exact hbase hseated
  | @cons st s1 W m rest' hrev hstep hrest ih =>
      intro hwf hbase hseated
      refine ih (step_wf hwf hstep) ?_ hseated
      intro hs1seated
      cases hst : seatOf st c with
      | none =>
          exact king_hidden_step_off hwf hstep hrev hking hst hs1seated
      | some bx =>
          obtain ⟨a, hseat, hhid⟩ := hbase (by rw [hst]; simp)
          exact king_hidden_step_seated hwf hstep hrev hking hseat hhid hs1seated

#print axioms king_pile_hidden_empty_play

/-! ## §12. The king wrapper and the full discharge (fresh, 2026-10-25)

With §8-§11 and the KingBottom-grade vacancy arm
(`swappableIn_king_of_vacancy'`, `Orig2/KingSwapAssembly.lean` §5 —
the owner's dichotomy completed: the arm's bare hypotheses were
unused by the certified proof), the king case closes.  The unseated
corners are vacuous (§9), the frozen corners are vacuous (§10), and
the live case — both twins `KingBottom` at distinct anchors in a
class carrying a vacancy — follows at `s'`: the negative arm gives
class-vacancy from the premise, the §11 transport makes the twins'
`s'`-piles `KingBottom`, and the arm fires.  The full wrapper splits
on the rank and discharges the ORIGINAL statement verbatim. -/

/-- Reversible plays keep every hidden deck (the play-grade ledger,
riding `rev_step_hidden_eq` per letter). -/
private theorem rev_play_hidden_eq {u w : State} {play : List Move}
    (hwf : u.WF) (hplay : ShufflePlayW u play w) :
    ∀ a, (w.piles a).hidden = (u.piles a).hidden := by
  revert hwf
  induction hplay with
  | nil st => intro _ a; rfl
  | @cons st s1 W m rest' hrev hstep hrest ih =>
      intro hwf a
      rw [ih (step_wf hwf hstep) a]
      exact rev_step_hidden_eq hwf hstep hrev a

/-- The first seat-change split: a play along which x's seat leaves
`.inl a` has a first letter where it does so (the §6/§7 split
pattern, at the anchor grade). -/
private theorem exists_seatChange_split (x : Card) (a : Anchor) :
    ∀ {s w : State} {play : List Move}, ShufflePlayW s play w →
      seatOf s x = some (Sum.inl a) → seatOf w x ≠ some (Sum.inl a) →
      ∃ pre m post u u', play = pre ++ m :: post ∧ ShufflePlayW s pre u ∧
        reversibleAtW u m ∧ State.step u m = some u' ∧
        ShufflePlayW u' post w ∧
        seatOf u x = some (Sum.inl a) ∧ seatOf u' x ≠ some (Sum.inl a) := by
  intro s w play hplay
  induction hplay with
  | nil st =>
      intro hseat hne
      exact absurd hseat hne
  | @cons st s1 W m rest' hrev hstep hrest ih =>
      intro hseat hne
      by_cases hc : seatOf s1 x = some (Sum.inl a)
      · obtain ⟨pre, m₀, post, u, u', hspl, hpre, hrev₀, hstep₀, hpost, huseat, hu'seat⟩ :=
          ih hc hne
        exact ⟨m :: pre, m₀, post, u, u', by rw [hspl]; rfl,
          Walk.cons hrev hstep hpre, hrev₀, hstep₀, hpost, huseat, hu'seat⟩
      · exact ⟨[], m, rest', st, s1, rfl, Walk.nil st, hrev, hstep, hrest, hseat, hc⟩

/-- **The constructive vacancy source** (the wrapper's classical-free
route): a swappable king pair forces the class to carry a vacancy.
The premise's witness play exchanges the twins, so x's seat changes;
at the FIRST change, either x's whole pile slides onto an EMPTY
anchor (the `.inl` gate — a vacancy right there), or x itself is
raised — and a raised king was necessarily alone (top and bottom),
so its anchor empties behind it. -/
theorem sameOrbitVacant_of_swappableIn_king {s : State} {x : Card} {a a' : Anchor}
    (hwf : s.WF) (hking : x.rank = Rank.king)
    (hx : seatOf s x = some (Sum.inl a)) (hxt : seatOf s x.twin = some (Sum.inl a'))
    (hne : a ≠ a') (hhidA : (s.piles a).hidden = [])
    (hswap : SwappableIn s x) : SameOrbitVacant s := by
  obtain ⟨v, hstrict, horb⟩ := hswap
  obtain ⟨-, -, ρ', hback⟩ := horb
  have hxdiff : seatOf v x ≠ some (Sum.inl a) := by
    intro hc
    have h1 : seatOf v x = some (Sum.inl a') := by rw [hstrict.1]; exact hxt
    exact hne (Sum.inl.inj (Option.some.inj (hc.symm.trans h1)))
  obtain ⟨pre, m, post, u, u', hspl, hpre, hrev, hstep, hpost, huseat, hu'seat⟩ :=
    exists_seatChange_split x a hback hx hxdiff
  have hwfu : u.WF := run_wf hwf
    (Walk_run (P := fun st m => reversibleAtW st m) (st := s) (W := u) hpre)
  have hhidu : (u.piles a).hidden = [] := by
    rw [rev_play_hidden_eq hwf hpre a]; exact hhidA
  have hru : sameOrbitSetoid.r s u := RevEqW_symm (shufflePlayW_revEqW hpre)
  cases m with
  | draw =>
      have hse := (chart_draw hstep).1
      exact absurd (show seatOf u' x = some (Sum.inl a) from by
        rw [hse x]; exact huseat) hu'seat
  | wasteToFound y => exact absurd hrev (wasteToFound_not_reversibleAtW u y)
  | wasteToTab y b => exact absurd hrev (wasteToTab_not_reversibleAtW u y b)
  | tabToFound d =>
      by_cases hcd : x = d
      · -- x raised: it was necessarily alone (top and bottom), so its
        -- anchor empties behind it — a vacancy at u'
        subst hcd
        obtain ⟨-, a₀, hpa, hs⟩ := step_tabToFound_inv hstep
        have hmem₀ : x ∈ (u.piles a₀).faceUp := by
          obtain ⟨-, hlast⟩ := tfc_pileOfTop_top hpa
          exact lastOf_mem hlast
        have hmema : x ∈ (u.piles a).faceUp := pileHolding_mem (tfc_seatOf_of_inl huseat).1
        have haa₀ : a = a₀ := by
          by_cases h : a = a₀
          · exact h
          · exact absurd hmem₀
              ((mem_faceUp_unique hwfu hmema a₀ (fun h' => h h'.symm)).1)
        have hlasta : lastOf (u.piles a).faceUp = some x := by
          rw [haa₀]; exact (tfc_pileOfTop_top hpa).2
        have hbelow : below x (u.piles a).faceUp = [] := (tfc_seatOf_of_inl huseat).2
        have hnd : (u.piles a).faceUp.Nodup := runOK_nodup (hwfu.runOK_of a)
        have hsingle : (u.piles a).faceUp = [x] :=
          eq_singleton_of_below_nil_lastOf hnd hbelow hlasta
        have hhid₀ : (u.piles a₀).hidden = [] := by rw [← haa₀]; exact hhidu
        rw [haa₀] at hsingle
        have hface' : (u'.piles a).faceUp = [] := by
          rw [hs, haa₀]
          show (if a₀ = a₀ then Pile.afterRunRemoved (u.piles a₀)
              (chop (u.piles a₀).faceUp) else u.piles a₀).faceUp = []
          rw [ite_eq_left rfl, hsingle]
          show (Pile.revealTop
            { hidden := (u.piles a₀).hidden, faceUp := ([] : List Card) }).faceUp = []
          rw [hhid₀]
          rfl
        have hhidden' : (u'.piles a).hidden = [] := by
          rw [rev_step_hidden_eq hwfu hstep hrev a]; exact hhidu
        exact ⟨u', RevEqW_symm (shufflePlayW_revEqW
            (ShufflePlayW_append hpre (Walk.cons hrev hstep (Walk.nil u')))),
          ⟨a, (Pile.isEmpty_eq _).mpr ⟨hhidden', hface'⟩⟩⟩
      · exact absurd (show seatOf u' x = some (Sum.inl a) from by
          rw [raise_seat_change_of_seated hstep hrev (by rw [huseat]; simp) hcd]
          exact huseat) hu'seat
  | foundToTab y b =>
      obtain ⟨c', htop, hc'c, -, -⟩ := step_foundToTab_inv hstep
      rw [hc'c] at htop
      have hcy : x ≠ y := by
        intro hxy
        rw [← hxy] at htop
        have hxmem : x ∈ u.found x.suit := by
          simpa [State.foundTop] using lastOf_mem htop
        exact ((mem_found_unique hwfu hxmem).1 a).2
          (pileHolding_mem (tfc_seatOf_of_inl huseat).1)
      exact absurd (show seatOf u' x = some (Sum.inl a) from by
        rw [pull_seat_change hstep x hcy]; exact huseat) hu'seat
  | tabToTab y b =>
      by_cases hcy : x = y
      · subst hcy
        obtain ⟨a₀, hhold₀, hcp, -, -⟩ := step_tabToTab_inv hstep
        cases b with
        | inl e =>
            obtain ⟨hemp, -⟩ := canPlace_inl hcp
            exact ⟨u, hru, ⟨e, hemp⟩⟩
        | inr z =>
            exfalso
            obtain ⟨-, -, hfit⟩ := canPlace_inr hcp
            rw [canSitOn_king_false hking] at hfit
            exact Bool.noConfusion hfit
      · exact absurd (show seatOf u' x = some (Sum.inl a) from by
          rw [tfc_seat_point_edit hwfu hstep hrev x, ite_eq_right hcy]
          exact huseat) hu'seat

/-- **THE KING WRAPPER.**  The original statement's shape under the
added hypothesis that the pair is a king pair, with the founds row
WEAKENED to twin-membership preservation (§15 — the only founds
fact the route reads). -/
theorem fiber_transfer_of_king :
    ∀ (s s' : State) (x : Card), s.WF → s'.WF →
      sameOrbitSetoid.r s s' →
      (x ∈ s.found x.suit → x ∈ s'.found x.suit) →
      (x.twin ∈ s.found x.twin.suit → x.twin ∈ s'.found x.twin.suit) →
      x.rank = Rank.king →
      (∃ v, twinPairSwapStrict s v x ∧ sameOrbitSetoid.r s v) →
      (∃ seatA, s'.pileHolding x = some seatA) →
      (∃ seatA', s'.pileHolding x.twin = some seatA') →
      (∃ v', twinPairSwapStrict s' v' x ∧ sameOrbitSetoid.r s' v') := by
  intro s s' x hwf hwf' hclass hxw hxtw hking hswap hholdx hholdxt
  obtain ⟨seatA, hseatA⟩ := hholdx
  obtain ⟨seatA', hseatA'⟩ := hholdxt
  have hseatx' : seatOf s' x ≠ none := seatOf_ne_none_of_pileHolding hseatA
  have hseatxt' : seatOf s' x.twin ≠ none := seatOf_ne_none_of_pileHolding hseatA'
  obtain ⟨π, hπ, -⟩ := sameOrbitSetoid.iseqv.symm hclass
  by_cases hseats : seatOf s x = none
  · exfalso
    by_cases hnotf : x ∈ s.found x.suit
    · exact hseatx' (seatOf_none_of_mem_found hwf' (hxw hnotf))
    · obtain ⟨hseat', -⟩ := unseated_track_play hwf hπ hseats hnotf
      exact hseatx' hseat'
  · by_cases hseatst : seatOf s x.twin = none
    · exfalso
      by_cases hnotft : x.twin ∈ s.found x.twin.suit
      · exact hseatxt' (seatOf_none_of_mem_found hwf' (hxtw hnotft))
      · obtain ⟨hseatt', -⟩ := unseated_track_play hwf hπ hseatst hnotft
        exact hseatxt' hseatt'
    · obtain ⟨a, hx⟩ := seat_inl_of_seated_king hwf hking hseats
      have hnkt : x.twin.rank = Rank.king := by
        have htr : x.twin.rank = x.rank := by cases x; rfl
        rw [htr]
        exact hking
      obtain ⟨a', hxt⟩ := seat_inl_of_seated_king hwf hnkt hseatst
      have hne : a ≠ a' := by
        intro h
        rw [show a' = a from h.symm] at hxt
        exact card_twin_ne x (seat_inl_unique hxt hx)
      by_cases hhidA : (s.piles a).hidden = []
      · by_cases hhidB : (s.piles a').hidden = []
        · -- the live case: class-vacancy from the premise (the negative
          -- arm), the transport makes the twins' s'-piles KingBottom,
          -- the KingBottom-grade arm fires at s'
          have hvac : SameOrbitVacant s :=
            sameOrbitVacant_of_swappableIn_king hwf hking hx hxt hne hhidA hswap
          have hvac' : SameOrbitVacant s' := (sameOrbitVacant_iff hclass).mp hvac
          obtain ⟨â, hx'⟩ := seat_inl_of_seated_king hwf' hking hseatx'
          obtain ⟨â', hxt'⟩ := seat_inl_of_seated_king hwf' hnkt hseatxt'
          have hne' : â ≠ â' := by
            intro h
            rw [show â' = â from h.symm] at hxt'
            exact card_twin_ne x (seat_inl_unique hxt' hx')
          have hbase : seatOf s x ≠ none → ∃ a, seatOf s x = some (Sum.inl a) ∧
              (s.piles a).hidden = [] := fun _ => ⟨a, hx, hhidA⟩
          obtain ⟨â₀, hx₀, hhidâ⟩ :=
            king_pile_hidden_empty_play hwf hπ hking hbase hseatx'
          have hâ : â₀ = â := Sum.inl.inj (Option.some.inj (hx₀.symm.trans hx'))
          rw [hâ] at hhidâ
          have hbaseT : seatOf s x.twin ≠ none → ∃ a, seatOf s x.twin = some (Sum.inl a) ∧
              (s.piles a).hidden = [] := fun _ => ⟨a', hxt, hhidB⟩
          obtain ⟨â₁, hxt₁, hhidâ'⟩ :=
            king_pile_hidden_empty_play hwf hπ hnkt hbaseT hseatxt'
          have hâ' : â₁ = â' := Sum.inl.inj (Option.some.inj (hxt₁.symm.trans hxt'))
          rw [hâ'] at hhidâ'
          exact swappableIn_king_of_vacancy' hwf' hking hx' hxt' hne' hhidâ hhidâ' hvac'
        · exact absurd (swappableIn_twin_comm.mp hswap)
            (not_swappableIn_of_frozen hwf hxt
              (show seatOf s x.twin.twin = some (Sum.inl a) from by
                rw [card_twin_twin]; exact hx)
              hne.symm hhidB)
      · exact absurd hswap (not_swappableIn_of_frozen hwf hx hxt hne hhidA)

/-- The per-card membership iff implied by full founds equality
(the §15 insight, packaged): the row's only content, per card. -/
private theorem mem_found_of_eq {s s' : State} (hfounds : s.found = s'.found)
    (c : Card) : c ∈ s.found c.suit ↔ c ∈ s'.found c.suit :=
  ⟨fun h => by rw [← hfounds]; exact h, fun h => by rw [hfounds]; exact h⟩

/-- **THE ORIGINAL `fiber_transfer`, DISCHARGED.**  The
ledger stub's statement VERBATIM — every hypothesis, the conclusion
verbatim, no rank split in the statement — proven by splitting on the
rank in the proof: the non-king case rides §9, the king case rides
§12. -/
theorem fiber_transfer_full :
    ∀ (s s' : State) (x : Card), s.WF → s'.WF →
      sameOrbitSetoid.r s s' → s.found = s'.found →
      (∃ v, twinPairSwapStrict s v x ∧ sameOrbitSetoid.r s v) →
      (∃ seatA, s'.pileHolding x = some seatA) →
      (∃ seatA', s'.pileHolding x.twin = some seatA') →
      (∃ v', twinPairSwapStrict s' v' x ∧ sameOrbitSetoid.r s' v') := by
  intro s s' x hwf hwf' hclass hfounds hswap hholdx hholdxt
  have hxw : x ∈ s.found x.suit → x ∈ s'.found x.suit :=
    (mem_found_of_eq hfounds x).mp
  have hxtw : x.twin ∈ s.found x.twin.suit →
      x.twin ∈ s'.found x.twin.suit :=
    (mem_found_of_eq hfounds x.twin).mp
  by_cases hking : x.rank = Rank.king
  · exact fiber_transfer_of_king s s' x hwf hwf' hclass hxw hxtw hking hswap
      hholdx hholdxt
  · exact fiber_transfer_of_nonking s s' x hwf hwf' hclass hxw hxtw hking
      hswap hholdx hholdxt

#print axioms fiber_transfer_of_king
#print axioms fiber_transfer_full

/-! ## §13. The seat-free strengthening (fresh, 2026-10-25, the
owner's second observation)

The `pileHolding` premises are REDUNDANT.  The strict letter's own
`foundsFixed` field kills MIXED pairs at the source (the off-board
twin must board at the witness; boarding either moves a foundation
row — the letter pins the rows — or rides an irreversible letter,
the §9 boarding lemma), so swappability forces both-or-neither.
Both-seated rides the seated pin (the only exit from the tableau
is a raise, which lands on the foundation, which the founds row
pins); both-unseated rides the boarding lemma and the pins — and
the conclusion is the certified vacuous swap.  The founds row,
never read by the last-return route, is now LOAD-BEARING. -/

/-- A seated card is held by a pile (the `pileHolding` premise
grade, from the seat grade). -/
private theorem pileHolding_of_seatOf_ne_none {s : State} {c : Card}
    (h : seatOf s c ≠ none) : ∃ a, s.pileHolding c = some a := by
  cases hph : s.pileHolding c with
  | none => exact absurd (tfc_seatOf_none hph) h
  | some a => exact ⟨a, rfl⟩

/-- **The seat dichotomy at the source**: a strictly swappable pair
is both-seated or both-unseated — never mixed.  A mixed pair's
off-board twin must board at the witness; boarding either moves a
foundation row (killed by the letter's own `foundsFixed`) or rides
an irreversible letter (the §9 boarding lemma). -/
theorem seats_both_or_neither_of_swappable {s : State} {x : Card}
    (hwf : s.WF) (hswap : SwappableIn s x) :
    (seatOf s x ≠ none ∧ seatOf s x.twin ≠ none) ∨
      (seatOf s x = none ∧ seatOf s x.twin = none) := by
  by_cases hx : seatOf s x = none
  · by_cases hxt : seatOf s x.twin = none
    · exact Or.inr ⟨hx, hxt⟩
    · exfalso
      obtain ⟨v, hstrict, horb⟩ := hswap
      obtain ⟨-, -, ρ, hback⟩ := horb
      have hwfv : v.WF :=
        run_wf hwf (Walk_run (P := fun st m => reversibleAtW st m)
          (st := s) (W := v) hback)
      obtain ⟨h1, -, -, -, hff, -, -, -⟩ := hstrict
      have hxv : seatOf v x ≠ none := by rw [h1]; exact hxt
      by_cases hmem : x ∈ s.found x.suit
      · exact hxv (seatOf_none_of_mem_found hwfv
          (by rw [← hff x.suit]; exact hmem))
      · obtain ⟨hseatv, -⟩ := unseated_track_play hwf hback hx hmem
        exact hxv hseatv
  · by_cases hxt : seatOf s x.twin = none
    · exfalso
      obtain ⟨v, hstrict, horb⟩ := hswap
      obtain ⟨-, -, ρ, hback⟩ := horb
      have hwfv : v.WF :=
        run_wf hwf (Walk_run (P := fun st m => reversibleAtW st m)
          (st := s) (W := v) hback)
      obtain ⟨-, h2, -, -, hff, -, -, -⟩ := hstrict
      have hxtv : seatOf v x.twin ≠ none := by rw [h2]; exact hx
      by_cases hmemt : x.twin ∈ s.found x.twin.suit
      · exact hxtv (seatOf_none_of_mem_found hwfv
          (by rw [← hff x.twin.suit]; exact hmemt))
      · obtain ⟨hseattv, -⟩ := unseated_track_play hwf hback hxt hmemt
        exact hxtv hseattv
    · exact Or.inl ⟨hx, hxt⟩

/-- **The seated pin**: a seated card stays seated across the class
journey — the only exit from the tableau is a raise, which lands
on the foundation, pinned by the backward membership arrow. -/
theorem seated_of_orbit {s s' : State} {x : Card}
    (hwf : s.WF) (hwf' : s'.WF) (hclass : sameOrbitSetoid.r s s')
    (hxb : x ∈ s'.found x.suit → x ∈ s.found x.suit)
    (hx : seatOf s x ≠ none) : seatOf s' x ≠ none := by
  intro hnone
  by_cases hmem : x ∈ s'.found x.suit
  · exact hx (seatOf_none_of_mem_found hwf (hxb hmem))
  · obtain ⟨ρ, hfor, -⟩ := hclass
    obtain ⟨hseats, -⟩ := unseated_track_play hwf' hfor hnone hmem
    exact hx hseats

/-- **The unseated pin**: an off-board card stays off-board across
the class journey — the foundation row is pinned by the forward
membership arrow, and stock/waste/hidden boarding is irreversible
(§9). -/
theorem unseated_of_orbit {s s' : State} {x : Card}
    (hwf : s.WF) (hwf' : s'.WF) (hclass : sameOrbitSetoid.r s s')
    (hxf : x ∈ s.found x.suit → x ∈ s'.found x.suit)
    (hx : seatOf s x = none) : seatOf s' x = none := by
  by_cases hmem : x ∈ s.found x.suit
  · exact seatOf_none_of_mem_found hwf' (hxf hmem)
  · obtain ⟨π, hπ, -⟩ := sameOrbitSetoid.iseqv.symm hclass
    obtain ⟨hseat', -⟩ := unseated_track_play hwf hπ hx hmem
    exact hseat'

/-- **The shared arrows route**: the dichotomy at the source, the
pins to the far end, then the rank-split wrappers or the vacuous
swap — the single home of the §13/§15 skeleton. -/
private theorem fiber_transfer_of_arrows {s s' : State} {x : Card}
    (hwf : s.WF) (hwf' : s'.WF) (hclass : sameOrbitSetoid.r s s')
    (hxw : x ∈ s.found x.suit ↔ x ∈ s'.found x.suit)
    (hxtw : x.twin ∈ s.found x.twin.suit ↔ x.twin ∈ s'.found x.twin.suit)
    (hswap : ∃ v, twinPairSwapStrict s v x ∧ sameOrbitSetoid.r s v) :
    ∃ v', twinPairSwapStrict s' v' x ∧ sameOrbitSetoid.r s' v' := by
  rcases seats_both_or_neither_of_swappable hwf hswap with ⟨hxs, hxts⟩ | ⟨hxs, hxts⟩
  · have hseatx' : seatOf s' x ≠ none :=
      seated_of_orbit hwf hwf' hclass hxw.mpr hxs
    have hseatt' : seatOf s' x.twin ≠ none :=
      seated_of_orbit hwf hwf' hclass hxtw.mpr hxts
    by_cases hking : x.rank = Rank.king
    · exact fiber_transfer_of_king s s' x hwf hwf' hclass
        hxw.mp hxtw.mp hking hswap
        (pileHolding_of_seatOf_ne_none hseatx')
        (pileHolding_of_seatOf_ne_none hseatt')
    · exact fiber_transfer_of_nonking s s' x hwf hwf' hclass
        hxw.mp hxtw.mp hking hswap
        (pileHolding_of_seatOf_ne_none hseatx')
        (pileHolding_of_seatOf_ne_none hseatt')
  · exact swappableIn_of_both_unseated
      (unseated_of_orbit hwf hwf' hclass hxw.mp hxs)
      (unseated_of_orbit hwf hwf' hclass hxtw.mp hxts)

/-- **THE SEAT-FREE STRENGTHENING** — the original statement minus
BOTH `pileHolding` premises (the owner's second observation,
2026-10-25): the premises are derivable.  The founds row, never
read by the last-return route, is load-bearing here. -/
theorem fiber_transfer_seat_free :
    ∀ (s s' : State) (x : Card), s.WF → s'.WF →
      sameOrbitSetoid.r s s' → s.found = s'.found →
      (∃ v, twinPairSwapStrict s v x ∧ sameOrbitSetoid.r s v) →
      (∃ v', twinPairSwapStrict s' v' x ∧ sameOrbitSetoid.r s' v') := by
  intro s s' x hwf hwf' hclass hfounds hswap
  exact fiber_transfer_of_arrows hwf hwf' hclass
    (mem_found_of_eq hfounds x) (mem_found_of_eq hfounds x.twin) hswap

#print axioms seats_both_or_neither_of_swappable
#print axioms seated_of_orbit
#print axioms unseated_of_orbit
#print axioms fiber_transfer_seat_free

/-! ## §14. The founds row is necessary — the refutation witness
(fresh, 2026-10-25, the owner's challenge)

The founds-free strengthening of §13 is FALSE, machine-checked.
Witness world: both twin kings on FULL foundations (hearts and
diamonds rows complete), all piles empty, the 26 black cards in
stock.  The swap premise holds VACUOUSLY (both twins off-board —
the certified `swappableIn_of_both_unseated`).  The class journey
is ONE reversible letter — pull the heart king onto the empty
anchor (the king-gated `.inl` landing), whose undo is the
re-armed raise (§3's self-arming row).  At the far end the pair
is MIXED — the heart king seated at the anchor, the diamond king
still on its foundation — and the §13 dichotomy kills the
conclusion there.  The journey moves the hearts row, so the
founds premise is exactly what forbids it. -/

/-- The mover: the heart king (twin: the diamond king). -/
private def refK : Card := Card.mk Suit.heart Rank.king

/-- The witness world: both twin kings on full foundations, all
piles empty, the black cards in stock. -/
private def kworld : State :=
  { found := fun su => match su with
      | .heart => Suit.upCards .heart
      | .diamond => Suit.upCards .diamond
      | .spade => []
      | .club => [],
    piles := fun _ => ⟨[], []⟩,
    stock := Suit.upCards .spade ++ Suit.upCards .club,
    waste := [],
    drawStep := 1 }

private theorem kworld_wf : kworld.WF := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro su
    cases su with
    | spade => exact ⟨0, rfl⟩
    | heart => exact ⟨13, rfl⟩
    | diamond => exact ⟨13, rfl⟩
    | club => exact ⟨0, rfl⟩
  · intro a
    rfl
  · intro c hc
    rcases c with ⟨su, r⟩
    cases su <;> cases r <;> decide
  · decide

/-- The far end: one reversible pull of the heart king onto the
empty anchor. -/
private def kworld' : State :=
  (kworld.setFound Suit.heart (chop (kworld.found Suit.heart))).putCard refK
    (Sum.inl Anchor.p0)

private theorem step_pull :
    State.step kworld (Move.foundToTab refK (Sum.inl Anchor.p0)) = some kworld' := rfl

private theorem step_raise :
    State.step kworld' (Move.tabToFound refK) = some kworld := by
  have hrw : State.step kworld' (Move.tabToFound refK) =
      some { kworld'.setFound refK.suit (kworld'.found refK.suit ++ [refK]) with
        piles := fun a' =>
          if a' = Anchor.p0 then Pile.afterRunRemoved (kworld'.piles Anchor.p0)
              (chop (kworld'.piles Anchor.p0).faceUp)
          else kworld'.piles a' } := rfl
  rw [hrw]
  refine congrArg some (State.ext ?_ ?_ rfl rfl rfl)
  · funext su
    cases su <;> rfl
  · funext a'
    by_cases ha' : a' = Anchor.p0
    · rw [ha']
      rfl
    · simp only []
      rw [if_neg ha']
      have hk : kworld'.piles a' =
          if a' = Anchor.p0 then (⟨[], [refK]⟩ : Pile) else kworld.piles a' := rfl
      rw [hk, if_neg ha']

/-- **THE FOUNDS ROW IS NECESSARY** — the statement without it is
FALSE.  Witness: the twin kings on full foundations; one reversible
pull strands the heart king at the anchor while the diamond king
stays upstairs — a mixed pair at the far end, never strictly
swappable (the §13 dichotomy); every premise except the founds row
holds at the pair. -/
theorem fiber_transfer_founds_necessary :
    ¬ (∀ (s s' : State) (x : Card), s.WF → s'.WF →
        sameOrbitSetoid.r s s' →
        (∃ v, twinPairSwapStrict s v x ∧ sameOrbitSetoid.r s v) →
        (∃ v', twinPairSwapStrict s' v' x ∧ sameOrbitSetoid.r s' v')) := by
  intro h
  have hwf' : kworld'.WF := step_wf kworld_wf step_pull
  have hrev_raise : reversibleAtW kworld' (Move.tabToFound refK) :=
    reversibleAtW_tabToFound_of_foundToTab kworld_wf step_pull
  have hrev_pull : reversibleAtW kworld (Move.foundToTab refK (Sum.inl Anchor.p0)) :=
    ⟨kworld', [Move.tabToFound refK], step_pull,
      Walk_run (P := fun st m => reversibleAtW st m) (st := kworld')
        (W := kworld) (Walk.cons hrev_raise step_raise (Walk.nil kworld))⟩
  have horb : sameOrbitSetoid.r kworld kworld' :=
    ⟨[Move.tabToFound refK], Walk.cons hrev_raise step_raise (Walk.nil kworld),
      [Move.foundToTab refK (Sum.inl Anchor.p0)],
      Walk.cons hrev_pull step_pull (Walk.nil kworld')⟩
  have hseatK : seatOf kworld refK = none := tfc_seatOf_none (by decide)
  have hseatKT : seatOf kworld refK.twin = none := tfc_seatOf_none (by decide)
  have hswap : (∃ v, twinPairSwapStrict kworld v refK ∧ sameOrbitSetoid.r kworld v) :=
    swappableIn_of_both_unseated hseatK hseatKT
  have hconcl := h kworld kworld' refK kworld_wf hwf' horb hswap
  -- the far end is mixed: the dichotomy kills the conclusion
  have hseatKT' : seatOf kworld' refK.twin = none := tfc_seatOf_none (by decide)
  have hseatK' : seatOf kworld' refK ≠ none := by
    have hhold : kworld'.pileHolding refK = some Anchor.p0 := by decide
    rw [tfc_seatOf_inl_intro hhold
      (rfl : below refK (kworld'.piles Anchor.p0).faceUp = [])]
    simp
  rcases seats_both_or_neither_of_swappable hwf' hconcl with ⟨-, h2⟩ | ⟨h1, -⟩
  · exact h2 hseatKT'
  · exact hseatK' h1

#print axioms fiber_transfer_founds_necessary

/-! ## §15. The twin-membership weakening (fresh, 2026-10-25, the
owner's third observation)

The founds row is READ only as per-card membership transfer of the
two twins: every use in the whole certified stack — the §9 and §12
corner-kills, the §13 pins — is an implication `x ∈ s.found x.suit
→ x ∈ s'.found x.suit` or its converse, for `x` or `x.twin`.  So
the row can be WEAKENED to exactly that: TWIN-MEMBERSHIP
PRESERVATION, with no constraint at all on the other fifty cards'
foundation positions.  Each direction of the iff kills one
counterexample family — the forward arrow forbids pulling a twin
DOWN (the §14 witness: the pulled king leaves the hearts row), the
backward arrow forbids net-raising a twin (the stranded-raiser
world).  With the seat premises kept, the backward direction is
vacuous (a seated card is on no foundation row), so the
original-shaped statement needs only the forward pair. -/

/-- **THE TWIN-MEMBERSHIP WEAKENING** — the seat-free statement with
the founds row collapsed to twin-membership preservation: each twin
is on its foundation row at `s` iff it is at `s'`.  Strictly
stronger than §13's `fiber_transfer_seat_free` (founds
equality implies both iffs) and consistent with §14's refutation
(the twin-kings witness violates the heart king's iff). -/
theorem fiber_transfer_twin_membership :
    ∀ (s s' : State) (x : Card), s.WF → s'.WF →
      sameOrbitSetoid.r s s' →
      (x ∈ s.found x.suit ↔ x ∈ s'.found x.suit) →
      (x.twin ∈ s.found x.twin.suit ↔ x.twin ∈ s'.found x.twin.suit) →
      (∃ v, twinPairSwapStrict s v x ∧ sameOrbitSetoid.r s v) →
      (∃ v', twinPairSwapStrict s' v' x ∧ sameOrbitSetoid.r s' v') := by
  intro s s' x hwf hwf' hclass hxw hxtw hswap
  exact fiber_transfer_of_arrows hwf hwf' hclass hxw hxtw hswap

#print axioms fiber_transfer_twin_membership
