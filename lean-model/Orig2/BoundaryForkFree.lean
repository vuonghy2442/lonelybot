import Orig2.Boundary

set_option autoImplicit false
set_option maxHeartbeats 4000000

/-!
# Orig2.BoundaryForkFree — the fork-free journey, kernel-checked

THE JOURNEY-LOCAL DIP IS FALSE.  The Plan-4 saturated boards `s1`
(rungs `(5,0,4,2)`) and `t1` (`(5,0,2,5)`) are connected by a 15-state /
14-move witness play that avoids all eight fork states of the class.
This card replays the play in Lean and proves:

* both endpoints are `WF` and `SSaturated`;
* every leg is legal and reversible, so the endpoints are
  `sameOrbitSetoid` mates;
* the first crossing of the club rung is at `F7` with rungs
  `(2,0,2,2)`, and `F7` is not a fork;
* every state on the play is fork-free.

Hence neither `SatJourneyFork` (the weakest journey-local residue) nor
`SatDip` (the first-passage dip) can hold.  The surviving residue is the
class-global `SatDifferFork` / `SatDifferForkWF`.

House compliance: additive boundary leaf (`Orig2.Boundary`); zero
`sorry`, zero `native_decide`, zero `Classical.choice`; battery at tail.
-/

namespace ForkFree

/-! ## §1. The two Plan-4 explicit boards -/

def crd (s : Suit) (r : Rank) : Card := ⟨s, r⟩

def s1 : State where
  found := fun s => s.upCards.take (match s with
    | .heart => 5
    | .diamond => 0
    | .spade => 4
    | .club => 2
    )
  piles := fun a => match a with
    | .p0 => ⟨[], [crd .diamond .four, crd .club .three, crd .diamond .two]⟩
    | .p1 => ⟨[], [crd .diamond .eight, crd .spade .seven]⟩
    | .p2 => ⟨[], [crd .diamond .five, crd .club .four]⟩
    | .p3 => ⟨[], [crd .heart .six, crd .club .five]⟩
    | .p4 => ⟨[], [crd .club .six]⟩
    | .p5 => ⟨[], [crd .spade .eight, crd .diamond .seven]⟩
    | .p6 => ⟨[crd .diamond .ace, crd .diamond .three, crd .spade .five, crd .diamond .six, crd .spade .six, crd .heart .seven, crd .club .seven, crd .heart .eight, crd .club .eight, crd .heart .nine, crd .diamond .nine, crd .spade .nine, crd .club .nine, crd .heart .ten, crd .diamond .ten, crd .spade .ten, crd .club .ten, crd .heart .jack, crd .diamond .jack, crd .spade .jack, crd .club .jack, crd .heart .queen, crd .diamond .queen, crd .spade .queen, crd .club .queen, crd .heart .king, crd .diamond .king, crd .spade .king, crd .club .king], []⟩
  stock := []
  waste := []
  drawStep := 1

def t1 : State where
  found := fun s => s.upCards.take (match s with
    | .heart => 5
    | .diamond => 0
    | .spade => 2
    | .club => 5
    )
  piles := fun a => match a with
    | .p0 => ⟨[], [crd .diamond .four, crd .spade .three, crd .diamond .two]⟩
    | .p1 => ⟨[], [crd .diamond .eight, crd .spade .seven]⟩
    | .p2 => ⟨[], [crd .diamond .five, crd .spade .four]⟩
    | .p3 => ⟨[], [crd .heart .six]⟩
    | .p4 => ⟨[], [crd .club .six]⟩
    | .p5 => ⟨[], [crd .spade .eight, crd .diamond .seven]⟩
    | .p6 => ⟨[crd .diamond .ace, crd .diamond .three, crd .spade .five, crd .diamond .six, crd .spade .six, crd .heart .seven, crd .club .seven, crd .heart .eight, crd .club .eight, crd .heart .nine, crd .diamond .nine, crd .spade .nine, crd .club .nine, crd .heart .ten, crd .diamond .ten, crd .spade .ten, crd .club .ten, crd .heart .jack, crd .diamond .jack, crd .spade .jack, crd .club .jack, crd .heart .queen, crd .diamond .queen, crd .spade .queen, crd .club .queen, crd .heart .king, crd .diamond .king, crd .spade .king, crd .club .king], []⟩
  stock := []
  waste := []
  drawStep := 1

/-! ## §2. The 14 moves printed by `Temp/SatDiffer_avoid_probe.py` -/

def m1 : Move := Move.foundToTab (crd .heart .five) (Sum.inr (crd .club .six))
def m2 : Move := Move.foundToTab (crd .heart .four) (Sum.inr (crd .club .five))
def m3 : Move := Move.foundToTab (crd .heart .three) (Sum.inr (crd .club .four))
def m4 : Move := Move.tabToTab (crd .club .three) (Sum.inr (crd .heart .four))
def m5 : Move := Move.foundToTab (crd .spade .four) (Sum.inr (crd .heart .five))
def m6 : Move := Move.foundToTab (crd .spade .three) (Sum.inr (crd .diamond .four))
def m7 : Move := Move.tabToTab (crd .diamond .two) (Sum.inr (crd .spade .three))
def m8 : Move := Move.tabToFound (crd .club .three)
def m9 : Move := Move.tabToFound (crd .heart .three)
def m10 : Move := Move.tabToFound (crd .heart .four)
def m11 : Move := Move.tabToFound (crd .club .four)
def m12 : Move := Move.tabToTab (crd .spade .four) (Sum.inr (crd .diamond .five))
def m13 : Move := Move.tabToFound (crd .heart .five)
def m14 : Move := Move.tabToFound (crd .club .five)

def play : List Move := [m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14]

def p7 : List Move := [m1, m2, m3, m4, m5, m6, m7]
def q7 : List Move := [m8, m9, m10, m11, m12, m13, m14]
def q8 : List Move := [m9, m10, m11, m12, m13, m14]

theorem play_decomp : play = p7 ++ q7 := rfl
theorem q7_decomp : q7 = m8 :: q8 := rfl

/-! ## §3. The 15 concrete states along the play -/

def vstep (st : State) (m : Move) : State :=
  match st.step m with
  | none => st
  | some s' => s'

def F0 : State := s1
def F1 : State := vstep F0 m1
def F2 : State := vstep F1 m2
def F3 : State := vstep F2 m3
def F4 : State := vstep F3 m4
def F5 : State := vstep F4 m5
def F6 : State := vstep F5 m6
def F7 : State := vstep F6 m7
def F8 : State := vstep F7 m8
def F9 : State := vstep F8 m9
def F10 : State := vstep F9 m10
def F11 : State := vstep F10 m11
def F12 : State := vstep F11 m12
def F13 : State := vstep F12 m13
def F14 : State := vstep F13 m14

def states : List State := [F0, F1, F2, F3, F4, F5, F6, F7, F8, F9, F10, F11, F12, F13, F14]

def prefixStates : List State :=
  (List.range 15).map (fun k => (s1.run (play.take k)).getD s1)

theorem prefixStates_eq_states : prefixStates = states := by rfl

theorem F14_eq_t1 : F14 = t1 := by
  refine State.ext (funext fun s => ?_) (funext fun a => ?_) rfl rfl rfl
  · cases s <;> rfl
  · cases a <;> rfl

/-! ## §4. Legality of every leg -/

theorem step_1 : State.step F0 m1 = some F1 := by rfl
theorem step_2 : State.step F1 m2 = some F2 := by rfl
theorem step_3 : State.step F2 m3 = some F3 := by rfl
theorem step_4 : State.step F3 m4 = some F4 := by rfl
theorem step_5 : State.step F4 m5 = some F5 := by rfl
theorem step_6 : State.step F5 m6 = some F6 := by rfl
theorem step_7 : State.step F6 m7 = some F7 := by rfl
theorem step_8 : State.step F7 m8 = some F8 := by rfl
theorem step_9 : State.step F8 m9 = some F9 := by rfl
theorem step_10 : State.step F9 m10 = some F10 := by rfl
theorem step_11 : State.step F10 m11 = some F11 := by rfl
theorem step_12 : State.step F11 m12 = some F12 := by rfl
theorem step_13 : State.step F12 m13 = some F13 := by rfl
theorem step_14 : State.step F13 m14 = some F14 := by rfl

/-! ## §5. WF at the endpoints and along the play -/

theorem s1_wf : s1.WF := by
  refine ⟨fun s => ?_, ?_, ?_, ?_⟩
  · cases s with
    | heart => exact ⟨5, rfl⟩
    | diamond => exact ⟨0, rfl⟩
    | spade => exact ⟨4, rfl⟩
    | club => exact ⟨2, rfl⟩
  · intro a
    cases a <;> decide
  · intro c _
    rcases c with ⟨s, r⟩
    cases s <;> cases r <;> decide
  · decide

theorem t1_wf : t1.WF := by
  refine ⟨fun s => ?_, ?_, ?_, ?_⟩
  · cases s with
    | heart => exact ⟨5, rfl⟩
    | diamond => exact ⟨0, rfl⟩
    | spade => exact ⟨2, rfl⟩
    | club => exact ⟨5, rfl⟩
  · intro a
    cases a <;> decide
  · intro c _
    rcases c with ⟨s, r⟩
    cases s <;> cases r <;> decide
  · decide

theorem wf_0 : F0.WF := s1_wf
theorem wf_1 : F1.WF := step_wf wf_0 step_1
theorem wf_2 : F2.WF := step_wf wf_1 step_2
theorem wf_3 : F3.WF := step_wf wf_2 step_3
theorem wf_4 : F4.WF := step_wf wf_3 step_4
theorem wf_5 : F5.WF := step_wf wf_4 step_5
theorem wf_6 : F6.WF := step_wf wf_5 step_6
theorem wf_7 : F7.WF := step_wf wf_6 step_7
theorem wf_8 : F8.WF := step_wf wf_7 step_8
theorem wf_9 : F9.WF := step_wf wf_8 step_9
theorem wf_10 : F10.WF := step_wf wf_9 step_10
theorem wf_11 : F11.WF := step_wf wf_10 step_11
theorem wf_12 : F12.WF := step_wf wf_11 step_12
theorem wf_13 : F13.WF := step_wf wf_12 step_13
theorem wf_14 : F14.WF := step_wf wf_13 step_14

theorem wf_t1 : t1.WF := t1_wf

/-! ## §6. Saturation of the two endpoints -/

theorem s1_sat : SSaturated s1 := by
  have h : rankSatB 12 s1 = true := by decide
  have hRS := (rankSatB_iff s1_wf 12).mp h
  intro c hc
  exact hRS c (by have := Rank.toIdx_lt c.rank; omega) hc

theorem t1_sat : SSaturated t1 := by
  have h : rankSatB 12 t1 = true := by decide
  have hRS := (rankSatB_iff t1_wf 12).mp h
  intro c hc
  exact hRS c (by have := Rank.toIdx_lt c.rank; omega) hc

/-! ## §7. A computable state-equality certificate

The forward states are chained through `vstep`, so `State.step Fi mi = some
Fi+1` is definitional.  The reverse steps land on a *literal earlier*
state, which the kernel would have to fully evaluate to see; instead we
compare the two states componentwise and run the comparison by `decide`.
-/

def samePileB (p q : Pile) : Bool :=
  decide (p.hidden = q.hidden) && decide (p.faceUp = q.faceUp)

def sameStateB (a b : State) : Bool :=
  (Suit.all.all (fun s => decide (a.found s = b.found s))) &&
  (Anchor.all.all (fun x => samePileB (a.piles x) (b.piles x))) &&
  decide (a.stock = b.stock) && decide (a.waste = b.waste) &&
  decide (a.drawStep = b.drawStep)

def sameOptB (o : Option State) (b : State) : Bool :=
  match o with
  | some a => sameStateB a b
  | none => false

theorem samePileB_true {p q : Pile} (h : samePileB p q = true) : p = q := by
  unfold samePileB at h
  rw [Bool.and_eq_true] at h
  exact Pile.ext (of_decide_eq_true h.1) (of_decide_eq_true h.2)

theorem sameStateB_true {a b : State} (h : sameStateB a b = true) : a = b := by
  unfold sameStateB at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨hfound, hpiles⟩, hstock⟩, hwaste⟩, hdraw⟩ := h
  have hf : a.found = b.found := funext fun s => by
    have hs := List.all_eq_true.mp hfound s (Suit.mem_all s)
    exact of_decide_eq_true hs
  have hp : a.piles = b.piles := funext fun x => by
    have hs := List.all_eq_true.mp hpiles x (Anchor.mem_all x)
    exact samePileB_true hs
  exact State.ext hf hp (of_decide_eq_true hstock) (of_decide_eq_true hwaste)
    (of_decide_eq_true hdraw)

theorem sameOptB_true {o : Option State} {b : State}
    (h : sameOptB o b = true) : o = some b := by
  unfold sameOptB at h
  cases o with
  | none => simp at h
  | some a =>
      simp only [Option.some.injEq]
      rw [sameStateB_true h]

/-! ## §8. The explicit one-move returns -/

def r1 : Move := Move.tabToFound (crd .heart .five)
def r2 : Move := Move.tabToFound (crd .heart .four)
def r3 : Move := Move.tabToFound (crd .heart .three)
def r4 : Move := Move.tabToTab (crd .club .three) (Sum.inr (crd .diamond .four))
def r5 : Move := Move.tabToFound (crd .spade .four)
def r6 : Move := Move.tabToFound (crd .spade .three)
def r7 : Move := Move.tabToTab (crd .diamond .two) (Sum.inr (crd .club .three))
def r8 : Move := Move.foundToTab (crd .club .three) (Sum.inr (crd .heart .four))
def r9 : Move := Move.foundToTab (crd .heart .three) (Sum.inr (crd .club .four))
def r10 : Move := Move.foundToTab (crd .heart .four) (Sum.inr (crd .club .five))
def r11 : Move := Move.foundToTab (crd .club .four) (Sum.inr (crd .diamond .five))
def r12 : Move := Move.tabToTab (crd .spade .four) (Sum.inr (crd .heart .five))
def r13 : Move := Move.foundToTab (crd .heart .five) (Sum.inr (crd .club .six))
def r14 : Move := Move.foundToTab (crd .club .five) (Sum.inr (crd .heart .six))

theorem ret_1 : State.step F1 r1 = some F0 := sameOptB_true (by decide)
theorem ret_2 : State.step F2 r2 = some F1 := sameOptB_true (by decide)
theorem ret_3 : State.step F3 r3 = some F2 := sameOptB_true (by decide)
theorem ret_4 : State.step F4 r4 = some F3 := sameOptB_true (by decide)
theorem ret_5 : State.step F5 r5 = some F4 := sameOptB_true (by decide)
theorem ret_6 : State.step F6 r6 = some F5 := sameOptB_true (by decide)
theorem ret_7 : State.step F7 r7 = some F6 := sameOptB_true (by decide)
theorem ret_8 : State.step F8 r8 = some F7 := sameOptB_true (by decide)
theorem ret_9 : State.step F9 r9 = some F8 := sameOptB_true (by decide)
theorem ret_10 : State.step F10 r10 = some F9 := sameOptB_true (by decide)
theorem ret_11 : State.step F11 r11 = some F10 := sameOptB_true (by decide)
theorem ret_12 : State.step F12 r12 = some F11 := sameOptB_true (by decide)
theorem ret_13 : State.step F13 r13 = some F12 := sameOptB_true (by decide)
theorem ret_14 : State.step F14 r14 = some F13 := sameOptB_true (by decide)

theorem rev_1 : reversibleAtW F0 m1 := ⟨F1, [r1], step_1, run_one ret_1⟩
theorem rev_2 : reversibleAtW F1 m2 := ⟨F2, [r2], step_2, run_one ret_2⟩
theorem rev_3 : reversibleAtW F2 m3 := ⟨F3, [r3], step_3, run_one ret_3⟩
theorem rev_4 : reversibleAtW F3 m4 := ⟨F4, [r4], step_4, run_one ret_4⟩
theorem rev_5 : reversibleAtW F4 m5 := ⟨F5, [r5], step_5, run_one ret_5⟩
theorem rev_6 : reversibleAtW F5 m6 := ⟨F6, [r6], step_6, run_one ret_6⟩
theorem rev_7 : reversibleAtW F6 m7 := ⟨F7, [r7], step_7, run_one ret_7⟩
theorem rev_8 : reversibleAtW F7 m8 := ⟨F8, [r8], step_8, run_one ret_8⟩
theorem rev_9 : reversibleAtW F8 m9 := ⟨F9, [r9], step_9, run_one ret_9⟩
theorem rev_10 : reversibleAtW F9 m10 := ⟨F10, [r10], step_10, run_one ret_10⟩
theorem rev_11 : reversibleAtW F10 m11 := ⟨F11, [r11], step_11, run_one ret_11⟩
theorem rev_12 : reversibleAtW F11 m12 := ⟨F12, [r12], step_12, run_one ret_12⟩
theorem rev_13 : reversibleAtW F12 m13 := ⟨F13, [r13], step_13, run_one ret_13⟩
theorem rev_14 : reversibleAtW F13 m14 := ⟨F14, [r14], step_14, run_one ret_14⟩

/-! ## §8. The witness shuffles and the class relation -/

theorem shuffle_0_7 : ShufflePlayW s1 p7 F7 :=
  (.cons rev_1 step_1 (.cons rev_2 step_2 (.cons rev_3 step_3 (.cons rev_4 step_4
    (.cons rev_5 step_5 (.cons rev_6 step_6 (.cons rev_7 step_7 (.nil F7))))))))

theorem shuffle_7_14 : ShufflePlayW F7 q7 F14 :=
  (.cons rev_8 step_8 (.cons rev_9 step_9 (.cons rev_10 step_10 (.cons rev_11 step_11
    (.cons rev_12 step_12 (.cons rev_13 step_13 (.cons rev_14 step_14 (.nil F14))))))))

theorem shuffle_0_14 : ShufflePlayW s1 play F14 := by
  rw [play_decomp]
  exact ShufflePlayW_append shuffle_0_7 shuffle_7_14

theorem run_play : s1.run play = some F14 := Walk_run _ shuffle_0_14

theorem sameOrbit_t1_s1 : sameOrbitSetoid.r t1 s1 := by
  have h : RevEqW s1 F14 := shufflePlayW_revEqW shuffle_0_14
  rw [F14_eq_t1] at h
  exact h

theorem sameOrbit_s1_t1 : sameOrbitSetoid.r s1 t1 := RevEqW_symm sameOrbit_t1_s1

theorem differing_rungs : ∃ σ : Suit, rungAt s1 σ ≠ rungAt t1 σ := by
  refine ⟨.club, ?_⟩
  decide

/-! ## §9. A computable live-set certificate -/

/-- The S-live set computed by the certified flat probe (`canRaiseSB_iff`). -/
def liveB (st : State) : List Card :=
  Card.universe.filter (fun c => canRaiseSB st c)

theorem mem_liveB {st : State} (hwf : st.WF) {c : Card} :
    c ∈ liveB st ↔ CanRaiseS st c := by
  unfold liveB
  rw [List.mem_filter]
  constructor
  · rintro ⟨-, h⟩
    exact (canRaiseSB_iff hwf).mp h
  · intro h
    exact ⟨Card.mem_universe c, (canRaiseSB_iff hwf).mpr h⟩

/- KIT-RULE STRIKE (2026-10-31, the new-material audit): the
namespace-local restatements `forkWitness_forkState` (canonical home:
`Orig2/ArmSplit.lean`, visible through the Boundary import) and
`card_twin_ne` (canonical home: `Orig2/Kit.lean:2329`) are struck;
the cites below resolve through the imports. -/

/-- Three distinct cards cannot all lie in one twin pair `{x, x.twin}`. -/
theorem three_in_twin_pair {x a b c : Card}
    (ha : a = x ∨ a = x.twin) (hb : b = x ∨ b = x.twin)
    (hc : c = x ∨ c = x.twin)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) : False := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
    rcases hc with rfl | rfl <;>
    first | exact hab rfl | exact hac rfl | exact hbc rfl

theorem no_fork_of_liveB_nil {st : State} (hwf : st.WF)
    (hlive : liveB st = []) : ¬ forkState st := by
  rintro ⟨x, hx, -⟩
  have hxS : CanRaiseS st x := (hx x).mp (Or.inl rfl)
  have hmem : x ∈ liveB st := (mem_liveB hwf).mpr hxS
  rw [hlive] at hmem
  exact absurd hmem (by simp)

theorem no_fork_of_liveB_single {st : State} (hwf : st.WF) {a : Card}
    (hlive : liveB st = [a]) : ¬ forkState st := by
  rintro ⟨x, hx, -⟩
  have hxS : CanRaiseS st x := (hx x).mp (Or.inl rfl)
  have hxmem : x ∈ liveB st := (mem_liveB hwf).mpr hxS
  have hxeq : x = a := by simpa [hlive] using hxmem
  have hxtS : CanRaiseS st x.twin := (hx x.twin).mp (Or.inr rfl)
  have hxtmem : x.twin ∈ liveB st := (mem_liveB hwf).mpr hxtS
  have hxteq : x.twin = a := by simpa [hlive] using hxtmem
  have h : x = x.twin := hxeq.trans hxteq.symm
  exact (card_twin_ne x) h.symm

theorem no_fork_of_liveB_pair {st : State} (hwf : st.WF) {a b : Card}
    (hab : a ≠ b) (hat : a.twin ≠ b) (hbt : b.twin ≠ a)
    (hlive : liveB st = [a, b]) : ¬ forkState st := by
  rintro ⟨x, hx, -⟩
  have hxS : CanRaiseS st x := (hx x).mp (Or.inl rfl)
  have hxmem : x ∈ liveB st := (mem_liveB hwf).mpr hxS
  have hxeq : x = a ∨ x = b := by simpa [hlive] using hxmem
  have hxtS : CanRaiseS st x.twin := (hx x.twin).mp (Or.inr rfl)
  have hxtmem : x.twin ∈ liveB st := (mem_liveB hwf).mpr hxtS
  have hxteq : x.twin = a ∨ x.twin = b := by simpa [hlive] using hxtmem
  rcases hxeq with rfl | rfl <;> rcases hxteq with h | h
  · exact (card_twin_ne _) h
  · exact hat h
  · exact hbt h
  · exact (card_twin_ne _) h

theorem no_fork_of_liveB_three {st : State} (hwf : st.WF) {a b c : Card}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hlive : liveB st = [a, b, c]) : ¬ forkState st := by
  rintro ⟨x, hx, -⟩
  have ha : a ∈ liveB st := by rw [hlive]; simp
  have hb : b ∈ liveB st := by rw [hlive]; simp
  have hc : c ∈ liveB st := by rw [hlive]; simp
  have hxa : a = x ∨ a = x.twin := (hx a).mpr ((mem_liveB hwf).mp ha)
  have hxb : b = x ∨ b = x.twin := (hx b).mpr ((mem_liveB hwf).mp hb)
  have hxc : c = x ∨ c = x.twin := (hx c).mpr ((mem_liveB hwf).mp hc)
  exact three_in_twin_pair hxa hxb hxc hab hac hbc

/-! ### The 15 live sets (printed by the probe) -/

theorem live_0 : liveB F0 = [] := by decide
theorem live_1 : liveB F1 = [crd .heart .five] := by decide
theorem live_2 : liveB F2 = [crd .heart .four] := by decide
theorem live_3 : liveB F3 = [crd .heart .three] := by decide
theorem live_4 : liveB F4 = [crd .heart .three] := by decide
theorem live_5 : liveB F5 = [crd .spade .four, crd .heart .three] := by decide
theorem live_6 : liveB F6 = [crd .spade .three, crd .heart .three, crd .club .three] := by decide
theorem live_7 : liveB F7 = [crd .spade .three, crd .heart .three, crd .club .three] := by decide
theorem live_8 : liveB F8 = [crd .heart .three, crd .club .four] := by decide
theorem live_9 : liveB F9 = [crd .heart .four, crd .club .four] := by decide
theorem live_10 : liveB F10 = [crd .club .four] := by decide
theorem live_11 : liveB F11 = [crd .heart .five, crd .club .five] := by decide
theorem live_12 : liveB F12 = [crd .heart .five, crd .club .five] := by decide
theorem live_13 : liveB F13 = [crd .club .five] := by decide
theorem live_14 : liveB F14 = [] := by decide

theorem no_fork_0 : ¬ forkState F0 := no_fork_of_liveB_nil wf_0 live_0
theorem no_fork_1 : ¬ forkState F1 := no_fork_of_liveB_single wf_1 live_1
theorem no_fork_2 : ¬ forkState F2 := no_fork_of_liveB_single wf_2 live_2
theorem no_fork_3 : ¬ forkState F3 := no_fork_of_liveB_single wf_3 live_3
theorem no_fork_4 : ¬ forkState F4 := no_fork_of_liveB_single wf_4 live_4
theorem no_fork_5 : ¬ forkState F5 :=
  no_fork_of_liveB_pair wf_5 (by decide) (by decide) (by decide) live_5
theorem no_fork_6 : ¬ forkState F6 :=
  no_fork_of_liveB_three wf_6 (by decide) (by decide) (by decide) live_6
theorem no_fork_7 : ¬ forkState F7 :=
  no_fork_of_liveB_three wf_7 (by decide) (by decide) (by decide) live_7
theorem no_fork_8 : ¬ forkState F8 :=
  no_fork_of_liveB_pair wf_8 (by decide) (by decide) (by decide) live_8
theorem no_fork_9 : ¬ forkState F9 :=
  no_fork_of_liveB_pair wf_9 (by decide) (by decide) (by decide) live_9
theorem no_fork_10 : ¬ forkState F10 := no_fork_of_liveB_single wf_10 live_10
theorem no_fork_11 : ¬ forkState F11 :=
  no_fork_of_liveB_pair wf_11 (by decide) (by decide) (by decide) live_11
theorem no_fork_12 : ¬ forkState F12 :=
  no_fork_of_liveB_pair wf_12 (by decide) (by decide) (by decide) live_12
theorem no_fork_13 : ¬ forkState F13 := no_fork_of_liveB_single wf_13 live_13
theorem no_fork_14 : ¬ forkState F14 := no_fork_of_liveB_nil wf_14 live_14

theorem no_fork_states : ∀ F, F ∈ states → ¬ forkState F := by
  intro F hF
  simp only [states, List.mem_cons, List.not_mem_nil, or_false] at hF
  rcases hF with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact no_fork_0
  · exact no_fork_1
  · exact no_fork_2
  · exact no_fork_3
  · exact no_fork_4
  · exact no_fork_5
  · exact no_fork_6
  · exact no_fork_7
  · exact no_fork_8
  · exact no_fork_9
  · exact no_fork_10
  · exact no_fork_11
  · exact no_fork_12
  · exact no_fork_13
  · exact no_fork_14

/-! ## §10. Every prefix state of the play is fork-free -/

theorem prefix_mem {a b : List Move} (h : play = a ++ b) :
    ∃ F, F ∈ states ∧ s1.run a = some F := by
  have hle : a.length ≤ play.length := by
    rw [h, List.length_append]
    omega
  have hlen : play.length = 14 := rfl
  have hk : a.length < 15 := by omega
  have htake : play.take a.length = a := by
    rw [h, List.take_left]
  have hmemPS : (s1.run (play.take a.length)).getD s1 ∈ prefixStates :=
    List.mem_map.mpr ⟨a.length, List.mem_range.mpr hk, rfl⟩
  rw [prefixStates_eq_states, htake] at hmemPS
  obtain ⟨F, hFa, -⟩ := run_append_split s1 a b F14 (by rw [← h]; exact run_play)
  refine ⟨F, ?_, hFa⟩
  simpa [hFa] using hmemPS

theorem no_fork_prefix {a b : List Move} (h : play = a ++ b) :
    ∀ F, s1.run a = some F → ¬ forkState F := by
  intro F hF
  obtain ⟨G, hGmem, hGrun⟩ := prefix_mem h
  have hGF : G = F := Option.some.inj (hGrun.symm.trans hF)
  subst hGF
  exact no_fork_states G hGmem

/-! ## §11. The first passage of the club rung is at `F7` -/

theorem rungs_F7 :
    rungAt F7 .heart = 2 ∧ rungAt F7 .diamond = 0 ∧
      rungAt F7 .spade = 2 ∧ rungAt F7 .club = 2 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

theorem rungs_F8_club : rungAt F8 .club = 3 := by decide

theorem rungs_before_club :
    rungAt F0 .club = 2 ∧ rungAt F1 .club = 2 ∧ rungAt F2 .club = 2 ∧
      rungAt F3 .club = 2 ∧ rungAt F4 .club = 2 ∧ rungAt F5 .club = 2 ∧
      rungAt F6 .club = 2 ∧ rungAt F7 .club = 2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- The first crossing of the club rung: the verbatim split. -/
theorem first_passage_club :
    play = p7 ++ Move.tabToFound (crd .club .three) :: q8 ∧
      ShufflePlayW s1 p7 F7 ∧
      ShufflePlayW F7 (Move.tabToFound (crd .club .three) :: q8) F14 ∧
      rungAt F7 .club = 2 ∧
      State.step F7 (Move.tabToFound (crd .club .three)) = some F8 ∧
      rungAt F8 .club = 3 := by
  refine ⟨?_, shuffle_0_7, ?_, (rungs_F7.2.2.2), step_8, rungs_F8_club⟩
  · rw [play_decomp, q7_decomp]
    rfl
  · show ShufflePlayW F7 q7 F14
    exact shuffle_7_14

theorem first_passage_not_fork : ¬ forkState F7 := no_fork_7

/-! ## §12. The journey-local forms and their refutation -/

/-- `SatDip` verbatim from `Temp/SatDiffer_Dip_1.lean:309` (local copy:
the source scratch card is not compiled as a library). -/
def SatDip : Prop :=
  ∀ (v u : State) (ρ : List Move) (σ : Suit),
    v.WF → SSaturated v → SSaturated u → ShufflePlayW v ρ u →
    rungAt v σ < rungAt u σ →
    ∃ (ρ₁ ρ₂ : List Move) (F : State) (c x : Card),
      ρ = ρ₁ ++ Move.tabToFound c :: ρ₂ ∧
      ShufflePlayW v ρ₁ F ∧
      ShufflePlayW F (Move.tabToFound c :: ρ₂) u ∧
      c.suit = σ ∧ c.rank.toIdx = rungAt v σ ∧ rungAt F σ = rungAt v σ ∧
      ForkWitness F x

/-- `SatJourneyFork` verbatim from `Temp/SatDiffer_Dip_1.lean:458`. -/
def SatJourneyFork : Prop :=
  ∀ (v u : State) (ρ : List Move) (σ : Suit),
    v.WF → SSaturated v → SSaturated u → ShufflePlayW v ρ u →
    rungAt v σ < rungAt u σ →
    ∃ (ρ₁ ρ₂ : List Move) (F : State) (x : Card),
      ρ = ρ₁ ++ ρ₂ ∧ ShufflePlayW v ρ₁ F ∧ ShufflePlayW F ρ₂ u ∧
      ForkWitness F x

theorem satJourneyFork_of_satDip (h : SatDip) : SatJourneyFork := by
  intro v u ρ σ hwf hsv hsu hρ hlt
  obtain ⟨ρ₁, ρ₂, F, c, x, hsplit, h1, h2, -, -, -, hfork⟩ :=
    h v u ρ σ hwf hsv hsu hρ hlt
  exact ⟨ρ₁, Move.tabToFound c :: ρ₂, F, x, hsplit, h1, h2, hfork⟩

theorem club_rung_rise : rungAt s1 .club < rungAt t1 .club := by decide

/-- **No journey-local form survives on the Plan-4 class.**  The exact
14-move witness play from `s1` to `t1` has no fork state at any of its
15 prefix positions. -/
theorem not_satJourneyFork : ¬ SatJourneyFork := by
  intro h
  have hplay : ShufflePlayW s1 play t1 := by
    rw [← F14_eq_t1]
    exact shuffle_0_14
  obtain ⟨ρ₁, ρ₂, F, x, hsplit, h1, h2, hfork⟩ :=
    h s1 t1 play Suit.club s1_wf s1_sat t1_sat hplay club_rung_rise
  have hrun : s1.run ρ₁ = some F := Walk_run _ h1
  exact no_fork_prefix hsplit F hrun (forkWitness_forkState hfork)

/-- The first-passage dip is false too: it implies the journey-local
form, which the play refutes. -/
theorem not_satDip : ¬ SatDip :=
  fun hd => not_satJourneyFork (satJourneyFork_of_satDip hd)

/-! ## §13. The boundary theorem -/

/-- **THE PLAN-4 BOUNDARY CERTIFICATE.**  Two `WF`, `SSaturated`,
same-orbit states with differing rungs, joined by an explicit witness
play whose every prefix state is fork-free.  The club rung first crosses
at `F7` (rungs `(2,0,2,2)`), which is not a fork.  Consequently neither
the first-passage dip (`SatDip`) nor the weakest journey-local residue
(`SatJourneyFork`) holds. -/
theorem journey_local_dip_false :
    s1.WF ∧ t1.WF ∧ SSaturated s1 ∧ SSaturated t1 ∧
      sameOrbitSetoid.r s1 t1 ∧
      (∃ σ : Suit, rungAt s1 σ ≠ rungAt t1 σ) ∧
      ShufflePlayW s1 play t1 ∧
      rungAt s1 .club < rungAt t1 .club ∧
      rungAt F7 .club = 2 ∧ rungAt F8 .club = 3 ∧
      (∀ G, G ∈ states → ¬ forkState G) ∧
      ¬ forkState F7 ∧ ¬ SatJourneyFork ∧ ¬ SatDip := by
  refine ⟨s1_wf, t1_wf, s1_sat, t1_sat, sameOrbit_s1_t1,
    differing_rungs, ?_, club_rung_rise, rungs_F7.2.2.2, rungs_F8_club,
    no_fork_states, no_fork_7, not_satJourneyFork, not_satDip⟩
  rw [← F14_eq_t1]
  exact shuffle_0_14

end ForkFree

/-! ## §14. Axiom battery -/

#print axioms ForkFree.s1_wf
#print axioms ForkFree.t1_wf
#print axioms ForkFree.s1_sat
#print axioms ForkFree.t1_sat
#print axioms ForkFree.rev_1
#print axioms ForkFree.rev_7
#print axioms ForkFree.rev_14
#print axioms ForkFree.shuffle_0_14
#print axioms ForkFree.sameOrbit_s1_t1
#print axioms ForkFree.live_7
#print axioms ForkFree.no_fork_7
#print axioms ForkFree.no_fork_states
#print axioms ForkFree.no_fork_prefix
#print axioms ForkFree.first_passage_club
#print axioms ForkFree.not_satJourneyFork
#print axioms ForkFree.not_satDip
#print axioms ForkFree.journey_local_dip_false
