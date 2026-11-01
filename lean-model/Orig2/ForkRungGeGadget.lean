import Orig2.ForkDipPin

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

/-!
# Orig2/ForkRungGeGadget — the cover-source datum does NOT give the twin-rung bound

READ-ONLY scratch card.  No source file is modified; nothing committed.
Zero `sorry`, zero `Classical.choice`, zero `native_decide`; axiom battery at
the tail.

## The question

`Mech.coverEvent_of_block` (`Orig2/ForkMechanism.lean:210`) is a theorem: at a
split's bottom `F`, `SplitBlock` + the green facts produce a
`Mech.CoverEvent` whose slide takes a mover `x` **off `c.twin`** and lands it on
`c` (`seatOf A x = some (inr c.twin)`, `seatOf F x = some (inr c)`).  The open
question for `PairRungKit.SplitTwinRungGe` is whether that source datum already
forces the twin-suit rung up to `c`'s rank.

## The answer: NO — kernel-checked

The board below is a `WF` state `A` (the cover slide's *source*) and its landing
`F`, both with the standard deck:

* `found` = hearts to the four; hearts rung `4`, all other rungs `0`;
* `p0 = [6C, 5H]` — the pull card `c = 5H` tops it with company below;
* `p1 = [5D, 4S]` — the mover `x = 4S` sits on `c.twin = 5D`;
* `p2 = [2D, AC]` — a **vanilla-raisable** card (the split's raise card `d`
  exists at the bottom too);
* the rest is stock.

At `A`: `c` is S-live (`CanRaiseS A 5H`, in fact vanilla), `c.twin` is the exact
**source** of the cover slide (`seatOf A 4S = some (inr 5D)`), and the whole
`BlockMin.BlockerReady` datum of `BlockMin.blockerReady_of_coverEvent` holds for
`c` — yet the twin suit is at rung `0`, four below `c`'s rank index `4`.

At `F` (the slide's landing, where a real split measures the pin):

| datum | value |
|---|---|
| `F.WF` | ✓ |
| `Mech.CoverEvent A F [slide] 5H` | ✓ |
| `¬ CanRaise F 5H` (the block) | ✓ |
| `CanRaiseS F 5H` (green licence) | ✓ |
| `∃ d, CanRaise F d` (the raise card `d = AC`) | ✓ |
| `rungAt F 5H.suit = 4` | ✓ |
| `rungAt F 5D.suit = 0` — **the pin fails** | ✓ |
| `¬ CanRaiseS F 5D` — the twin is not live | ✓ |

So every *local* datum the mechanism kit can supply at the bottom is present and
the pin still fails.  The one missing input is exactly the twin's own
S-liveness at `F`, `RungGe.SplitTwinLiveAtBottom` — which
`Temp/RungGe_Core.lean` consumes to prove the pin outright.
-/

namespace RungGeGadget

def AH : Card := ⟨.heart, .ace⟩
def H2 : Card := ⟨.heart, .two⟩
def H3 : Card := ⟨.heart, .three⟩
def H4 : Card := ⟨.heart, .four⟩
def H5 : Card := ⟨.heart, .five⟩
def D2 : Card := ⟨.diamond, .two⟩
def D5 : Card := ⟨.diamond, .five⟩
def AC : Card := ⟨.club, .ace⟩
def C6 : Card := ⟨.club, .six⟩
def S4 : Card := ⟨.spade, .four⟩

/-- The ten cards the gadget puts on the board; everything else is stock. -/
def fixed : List Card := [AH, H2, H3, H4, H5, D2, D5, AC, C6, S4]

/-- The 42-card stock (the complement of `fixed` in the deck). -/
def rest : List Card := Card.universe.filter (fun c => !(decide (c ∈ fixed)))

/-- The board builder: hearts founded to the four, `p0`/`p1`/`p2` as given. -/
def mkState (p0 p1 p2 : List Card) : State :=
  { found := fun s => match s with
      | .heart => [AH, H2, H3, H4]
      | .diamond => []
      | .spade => []
      | .club => []
    piles := fun a => match a with
      | .p0 => ⟨[], p0⟩
      | .p1 => ⟨[], p1⟩
      | .p2 => ⟨[], p2⟩
      | _ => ⟨[], []⟩
    stock := rest
    waste := []
    drawStep := 1 }

/-- **`A` — the cover slide's SOURCE state.**  `5H` tops `p0` with `6C` below;
`5D` (= `(5H).twin`) carries `4S`; `AC` tops `p2` with `2D` below. -/
def A : State := mkState [C6, H5] [D5, S4] [D2, AC]

/-- **`F` — the cover slide's LANDING.**  `4S` has moved off `5D` onto `5H`. -/
def F : State := mkState [C6, H5, S4] [D5] [D2, AC]

/-! ## §1. Well-formedness -/

theorem A_wf : A.WF := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s
    cases s <;> first | exact ⟨4, rfl⟩ | exact ⟨0, rfl⟩
  · intro a; cases a <;> decide
  · intro c _; rcases c with ⟨s, r⟩; cases s <;> cases r <;> decide
  · decide

theorem F_wf : F.WF := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s
    cases s <;> first | exact ⟨4, rfl⟩ | exact ⟨0, rfl⟩
  · intro a; cases a <;> decide
  · intro c _; rcases c with ⟨s, r⟩; cases s <;> cases r <;> decide
  · decide

/-! ## §2. The cover slide and its reversibility -/

theorem A_holds : A.pileHolding S4 = some .p1 := by decide
theorem A_canPlace : A.canPlace S4 (Sum.inr H5) = true := by decide
theorem A_below : below S4 (A.piles .p1).faceUp ≠ [] := by decide
theorem F_holds : F.pileHolding S4 = some .p0 := by decide
theorem F_canPlace : F.canPlace S4 (Sum.inr D5) = true := by decide
theorem F_below : below S4 (F.piles .p0).faceUp ≠ [] := by decide

theorem A_rev : reversibleAtW A (Move.tabToTab S4 (Sum.inr H5)) :=
  (tabToTabR_iff_reversibleAtW A_wf S4 (Sum.inr H5)).mp
    (R12.tabToTabR_true_of A_holds A_canPlace (Or.inl A_below))

theorem F_rev : reversibleAtW F (Move.tabToTab S4 (Sum.inr D5)) :=
  (tabToTabR_iff_reversibleAtW F_wf S4 (Sum.inr D5)).mp
    (R12.tabToTabR_true_of F_holds F_canPlace (Or.inl F_below))

/-- **THE COVER SLIDE FIRES.** -/
theorem A_step : State.step A (Move.tabToTab S4 (Sum.inr H5)) = some F := by
  rw [step_tabToTab_eq]
  rw [A_holds, A_canPlace]
  refine congrArg some (State.ext ?_ ?_ ?_ ?_ ?_)
  · funext s; cases s <;> rfl
  · funext a; cases a <;> rfl
  · rfl
  · rfl
  · rfl

/-- The slide back (the undo). -/
theorem F_step : State.step F (Move.tabToTab S4 (Sum.inr D5)) = some A := by
  rw [step_tabToTab_eq]
  rw [F_holds, F_canPlace]
  refine congrArg some (State.ext ?_ ?_ ?_ ?_ ?_)
  · funext s; cases s <;> rfl
  · funext a; cases a <;> rfl
  · rfl
  · rfl
  · rfl

/-! ## §3. The rungs: the twin is four behind -/

theorem A_rung_own : rungAt A H5.suit = H5.rank.toIdx := rfl
theorem F_rung_own : rungAt F H5.suit = H5.rank.toIdx := rfl
theorem A_rung_twin : rungAt A D5.suit = 0 := rfl
theorem F_rung_twin : rungAt F D5.suit = 0 := rfl

/-- `5H.rank.toIdx = 4`. -/
theorem H5_rank : H5.rank.toIdx = 4 := rfl

/-- **THE PIN FAILS at the cover's source.** -/
theorem A_pin_fails : rungAt A D5.suit < rungAt A H5.suit := by
  rw [A_rung_twin, A_rung_own, H5_rank]; decide

/-- **THE PIN FAILS at the cover's landing.** -/
theorem F_pin_fails : rungAt F D5.suit < rungAt F H5.suit := by
  rw [F_rung_twin, F_rung_own, H5_rank]; decide

/-! ## §4. The licences at the source -/

theorem A_pileOfTop : A.pileOfTop H5 = some .p0 := by decide
theorem A_nextUp : A.nextUp H5 = true := by decide
theorem A_chop : chop (A.piles .p0).faceUp ≠ [] := by decide

/-- **`c` IS VANILLA-RAISABLE AT THE SOURCE.** -/
theorem A_canRaise : CanRaise A H5 :=
  ⟨A_nextUp, .p0, A_pileOfTop, Or.inl A_chop⟩

/-- **`c` IS S-LIVE AT THE SOURCE** (the green licence of `splitHyp_green`). -/
theorem A_live : CanRaiseS A H5 := CanRaiseS.now H5 A_canRaise

/-- The twin is *not* raisable at the source: its suit's rung is not its rank. -/
theorem A_twin_not_raisable : ¬ CanRaise A D5 := by
  intro h
  have hf : A.nextUp D5 = false := by decide
  have h1 : A.nextUp D5 = true := h.1
  rw [hf] at h1
  exact Bool.false_ne_true h1

/-! ## §5. The licences at the landing -/

/-- **`c` IS BLOCKED AT THE LANDING** — `4S` sits on it. -/
theorem F_block : ¬ CanRaise F H5 := by
  intro h
  obtain ⟨-, a, ha, -⟩ := h
  have hnone : F.pileOfTop H5 = none := by decide
  rw [hnone] at ha
  exact absurd ha (by simp)

/-- **`c` IS STILL S-LIVE AT THE LANDING** (the slide is reversible). -/
theorem F_live : CanRaiseS F H5 :=
  CanRaiseS.via H5 ⟨S4, Sum.inr D5, F_step, F_rev⟩ A_live

/-- **THE RAISE CARD EXISTS AT THE LANDING**: `AC` is vanilla-raisable there. -/
theorem F_canRaise_AC : CanRaise F AC :=
  ⟨by decide, .p2, by decide, Or.inl (by decide)⟩

/-- **THE TWIN IS NOT S-LIVE AT THE LANDING.**  Any S-live card sits on its
suit's frontier (`canRaiseS_rung`); `5D`'s suit is at rung `0`, not `4`.  So the
gadget's pin failure is *exactly* a twin-liveness failure. -/
theorem F_twin_not_live : ¬ CanRaiseS F D5 := by
  intro h
  have h1 := canRaiseS_rung (st := F) (c := D5) h
  rw [F_rung_twin] at h1
  exact absurd h1 (by decide)

/-! ## §6. The cover event and the refutation -/

theorem A_seat : seatOf A S4 = some (Sum.inr D5) := by decide
theorem F_seat : seatOf F S4 = some (Sum.inr H5) := by decide

/-- **THE COVER EVENT OF THE GADGET** — verbatim `Mech.CoverEvent`: the mover
`4S` sits on `c.twin = 5D` at `A`, slides onto `c = 5H`, and stays there. -/
theorem A_coverEvent :
    Mech.CoverEvent A F [Move.tabToTab S4 (Sum.inr H5)] H5 :=
  ⟨S4, [], [], A, F, rfl, Walk.nil A, A_seat, A_rev, A_step, Walk.nil F, F_seat⟩

/-- **`coverEvent_of_block` APPLIES TO THE GADGET.**  All six hypotheses of the
mechanism theorem (`B.WF`, the free play, freeness, `CanRaise B c`,
`CanRaiseS F c`, `¬ CanRaise F c`) hold here, so the gadget sits inside the
mechanism's regime — not outside it. -/
theorem A_coverEvent_via_block :
    Mech.CoverEvent A F [Move.tabToTab S4 (Sum.inr H5)] H5 :=
  Mech.coverEvent_of_block A_wf
    (Walk.cons A_rev A_step (Walk.nil F))
    (by
      intro m hm
      rw [List.mem_singleton] at hm
      subst hm
      exact ValleyElim.free_slide S4 (Sum.inr H5))
    A_canRaise F_live F_block

/-- **THE WHOLE LOCAL DATUM, WITH THE PIN FAILING.**  `A`/`F` are `WF`; the
cover event holds; `c` is S-live and blocked at the landing; a raise card exists
there; the cover's source is `c.twin`; the twin suit is strictly behind; and the
twin is not even S-live. -/
theorem coverEvent_with_failing_pin :
    ∃ (B F' : State) (post : List Move) (c x : Card),
      B.WF ∧ F'.WF ∧ Mech.CoverEvent B F' post c ∧
      CanRaiseS F' c ∧ ¬ CanRaise F' c ∧
      (∃ d : Card, CanRaise F' d) ∧
      seatOf B x = some (Sum.inr c.twin) ∧
      rungAt F' c.twin.suit < rungAt F' c.suit ∧
      ¬ CanRaiseS F' c.twin :=
  ⟨A, F, [Move.tabToTab S4 (Sum.inr H5)], H5, S4,
    A_wf, F_wf, A_coverEvent, F_live, F_block, ⟨AC, F_canRaise_AC⟩,
    A_seat, F_pin_fails, F_twin_not_live⟩

/-- **THE COVER-SOURCE DATUM DOES NOT IMPLY THE PIN.**  There is a `WF` state and
a genuine `Mech.CoverEvent` from it whose landing is S-live and blocked but
whose twin suit is strictly behind `c`'s suit.  So `SplitBlock` +
`CanRaiseS F c` + the mechanism's cover event are *not* enough for
`PairRungKit.SplitTwinRungGe`; the twin's liveness is genuinely additional. -/
theorem coverEvent_does_not_imply_pin :
    ¬ (∀ (B F' : State) (post : List Move) (c : Card),
        B.WF → Mech.CoverEvent B F' post c → CanRaiseS F' c →
          rungAt F' c.twin.suit = rungAt F' c.suit) := by
  intro h
  obtain ⟨B, F', post, c, x, hB, -, hcov, hlive, -, -, -, hlt, -⟩ :=
    coverEvent_with_failing_pin
  exact absurd (h B F' post c hB hcov hlive) (Nat.ne_of_lt hlt)

/-- **THE `BlockMin.BlockerReady` DATUM AT THE SOURCE.**  `4S` is a ready blocker
for `5H`: it fits, it is face up in `p1` with `5D` beneath it, and `5H` tops
`p0`. -/
theorem A_blockerReady : BlockMin.BlockerReady A H5 :=
  ⟨S4, .p1, .p0, by decide, by decide, by decide, by decide⟩

/-- The same datum is exactly what `blockerReady_of_coverEvent` extracts from the
cover event (the tie to `Orig2/ForkDipPin.lean:229`). -/
theorem blockerReady_from_coverEvent :
    ∃ A' : State, BlockMin.BlockerReady A' H5 :=
  BlockMin.blockerReady_of_coverEvent A_wf A_coverEvent

/-- **THE WHOLE DATUM `blockerReady_of_coverEvent` EXTRACTS, WITH THE PIN
FAILING**: the source state, the ready blocker, the cover's source seat, the
green licence, and the twin strictly behind. -/
theorem blockerReady_with_failing_pin :
    ∃ (A' : State) (c x : Card),
      A'.WF ∧ BlockMin.BlockerReady A' c ∧
      seatOf A' x = some (Sum.inr c.twin) ∧
      CanRaiseS A' c ∧
      rungAt A' c.twin.suit < rungAt A' c.suit :=
  ⟨A, H5, S4, A_wf, A_blockerReady, A_seat, A_live, A_pin_fails⟩

/-! ## §7. Battery -/

#print axioms RungGeGadget.A_wf
#print axioms RungGeGadget.F_wf
#print axioms RungGeGadget.A_rev
#print axioms RungGeGadget.F_rev
#print axioms RungGeGadget.A_step
#print axioms RungGeGadget.F_step
#print axioms RungGeGadget.A_pin_fails
#print axioms RungGeGadget.F_pin_fails
#print axioms RungGeGadget.A_canRaise
#print axioms RungGeGadget.A_live
#print axioms RungGeGadget.A_twin_not_raisable
#print axioms RungGeGadget.F_block
#print axioms RungGeGadget.F_live
#print axioms RungGeGadget.F_canRaise_AC
#print axioms RungGeGadget.F_twin_not_live
#print axioms RungGeGadget.A_coverEvent
#print axioms RungGeGadget.A_coverEvent_via_block
#print axioms RungGeGadget.coverEvent_with_failing_pin
#print axioms RungGeGadget.coverEvent_does_not_imply_pin
#print axioms RungGeGadget.A_blockerReady
#print axioms RungGeGadget.blockerReady_from_coverEvent
#print axioms RungGeGadget.blockerReady_with_failing_pin

end RungGeGadget


