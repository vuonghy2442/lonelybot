import Orig2.BoundaryForkFree

set_option autoImplicit false
set_option maxHeartbeats 4000000

/-!
# Orig2.BoundaryMinPath — the 9-bracket path crosses the Plan-4 fork

THE MINIMAL-PATH BOUNDARY FACT.  The Plan-4 saturated boards `s1`
(`(5,0,4,2)`) and `t1` (`(5,0,2,5)`) have:

* a 12-move / 9-bracket witness play `minPlay` that crosses the fork at
  `(3,0,2,2)` (`N6`, witness `3S`; `N7`, witness `3C`);
* the 14-move / 11-bracket fork-free play of `Orig2.BoundaryForkFree`.

So the fork-free route is not bracket-minimal: it pays one extra
pull+raise pair.  This is the kernel-checked representative of the
finite-model census (every 9-bracket path crosses a fork; the minimum
fork-free cost is 11).

The universal lower bound ("no fork-free play costs ≤ 10", "all 32
minimal walks cross a fork") remains the finite-model census
(`Temp/SatDiffer_MinPath_Report.md`); this card certifies the concrete
representative.

House compliance: additive boundary leaf (`Orig2.BoundaryForkFree`);
zero `sorry`, zero `Classical.choice`, zero `native_decide`; battery at
tail.
-/

open ForkFree

namespace SatDifferMin9P

/-! ## §1. The 12 moves of the 9-bracket path -/

def a1 : Move := Move.foundToTab (crd .heart .five) (Sum.inr (crd .club .six))
def a2 : Move := Move.foundToTab (crd .heart .four) (Sum.inr (crd .club .five))
def a3 : Move := Move.tabToTab (crd .club .three) (Sum.inr (crd .heart .four))
def a4 : Move := Move.tabToTab (crd .club .four) (Sum.inr (crd .heart .five))
def a5 : Move := Move.foundToTab (crd .spade .four) (Sum.inr (crd .diamond .five))
def a6 : Move := Move.foundToTab (crd .spade .three) (Sum.inr (crd .diamond .four))
def a7 : Move := Move.tabToTab (crd .diamond .two) (Sum.inr (crd .spade .three))
def a8 : Move := Move.tabToFound (crd .club .three)
def a9 : Move := Move.tabToFound (crd .heart .four)
def a10 : Move := Move.tabToFound (crd .club .four)
def a11 : Move := Move.tabToFound (crd .heart .five)
def a12 : Move := Move.tabToFound (crd .club .five)

def minPlay : List Move := [a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12]
def prefix6 : List Move := [a1, a2, a3, a4, a5, a6]
def suffix6 : List Move := [a7, a8, a9, a10, a11, a12]

theorem minPlay_decomp : minPlay = prefix6 ++ suffix6 := rfl
theorem minPlay_length : minPlay.length = 12 := rfl

/-! ## §2. The 13 states -/

def N0 : State := s1
def N1 : State := vstep N0 a1
def N2 : State := vstep N1 a2
def N3 : State := vstep N2 a3
def N4 : State := vstep N3 a4
def N5 : State := vstep N4 a5
def N6 : State := vstep N5 a6
def N7 : State := vstep N6 a7
def N8 : State := vstep N7 a8
def N9 : State := vstep N8 a9
def N10 : State := vstep N9 a10
def N11 : State := vstep N10 a11
def N12 : State := vstep N11 a12

theorem step_1 : State.step N0 a1 = some N1 := by rfl
theorem step_2 : State.step N1 a2 = some N2 := by rfl
theorem step_3 : State.step N2 a3 = some N3 := by rfl
theorem step_4 : State.step N3 a4 = some N4 := by rfl
theorem step_5 : State.step N4 a5 = some N5 := by rfl
theorem step_6 : State.step N5 a6 = some N6 := by rfl
theorem step_7 : State.step N6 a7 = some N7 := by rfl
theorem step_8 : State.step N7 a8 = some N8 := by rfl
theorem step_9 : State.step N8 a9 = some N9 := by rfl
theorem step_10 : State.step N9 a10 = some N10 := by rfl
theorem step_11 : State.step N10 a11 = some N11 := by rfl
theorem step_12 : State.step N11 a12 = some N12 := by rfl

theorem N12_eq_t1 : N12 = t1 := by
  refine State.ext (funext fun s => ?_) (funext fun a => ?_) rfl rfl rfl
  · cases s <;> rfl
  · cases a <;> rfl

theorem run_minPlay : s1.run minPlay = some t1 := by
  rw [show t1 = N12 from N12_eq_t1.symm]
  rfl

theorem run_prefix6 : s1.run prefix6 = some N6 := by rfl

/-! ## §3. Bracket count -/

def bracketCount (l : List Move) : Nat := raiseTotal l + pullTotal l

theorem bracketCount_minPlay : bracketCount minPlay = 9 := by decide
theorem play_length : play.length = 14 := rfl
theorem bracketCount_play : bracketCount play = 11 := by decide

/-! ## §4. WF and the fork at `N6` -/

theorem wf_N0 : N0.WF := s1_wf
theorem wf_N1 : N1.WF := step_wf wf_N0 step_1
theorem wf_N2 : N2.WF := step_wf wf_N1 step_2
theorem wf_N3 : N3.WF := step_wf wf_N2 step_3
theorem wf_N4 : N4.WF := step_wf wf_N3 step_4
theorem wf_N5 : N5.WF := step_wf wf_N4 step_5
theorem wf_N6 : N6.WF := step_wf wf_N5 step_6
theorem wf_N7 : N7.WF := step_wf wf_N6 step_7

theorem twin_S3 : (crd .spade .three).twin = crd .club .three := by decide
theorem twin_C3 : (crd .club .three).twin = crd .spade .three := by decide

/-- One twin pair in the live set + blocked twin ⇒ fork witness. -/
theorem forkWitness_of_liveB_twin_pair {st : State} (hwf : st.WF) {x : Card}
    (hlive : liveB st = [x, x.twin]) (hblock : ¬ CanRaise st x.twin) :
    ForkWitness st x := by
  constructor
  · intro c
    constructor
    · intro h
      rcases h with rfl | rfl
      · exact (mem_liveB hwf).mp (by rw [hlive]; simp)
      · exact (mem_liveB hwf).mp (by rw [hlive]; simp)
    · intro hc
      have hmem : c ∈ liveB st := (mem_liveB hwf).mpr hc
      rw [hlive] at hmem
      simpa using hmem
  · exact hblock

theorem forkWitness_of_liveB_twin_pair_swap {st : State} (hwf : st.WF) {x : Card}
    (hlive : liveB st = [x.twin, x]) (hblock : ¬ CanRaise st x.twin) :
    ForkWitness st x := by
  constructor
  · intro c
    constructor
    · intro h
      rcases h with rfl | rfl
      · exact (mem_liveB hwf).mp (by rw [hlive]; simp)
      · exact (mem_liveB hwf).mp (by rw [hlive]; simp)
    · intro hc
      have hmem : c ∈ liveB st := (mem_liveB hwf).mpr hc
      rw [hlive] at hmem
      simpa [or_comm] using hmem
  · exact hblock

theorem live_N6 : liveB N6 = [crd .spade .three, crd .club .three] := by decide
theorem live_N7 : liveB N7 = [crd .spade .three, crd .club .three] := by decide

theorem covered_N6_C3 : CoveredAt N6 (crd .club .three) := by
  refine ⟨crd .diamond .two, ?_⟩
  decide

theorem covered_N7_S3 : CoveredAt N7 (crd .spade .three) := by
  refine ⟨crd .diamond .two, ?_⟩
  decide

theorem blocked_N6_C3 : ¬ CanRaise N6 (crd .club .three) :=
  not_canRaise_of_covered wf_N6 covered_N6_C3

theorem blocked_N7_S3 : ¬ CanRaise N7 (crd .spade .three) :=
  not_canRaise_of_covered wf_N7 covered_N7_S3

theorem forkWitness_N6 : ForkWitness N6 (crd .spade .three) := by
  apply forkWitness_of_liveB_twin_pair wf_N6
  · simpa [twin_S3] using live_N6
  · simpa [twin_S3] using blocked_N6_C3

theorem forkWitness_N7 : ForkWitness N7 (crd .club .three) := by
  apply forkWitness_of_liveB_twin_pair_swap wf_N7
  · simpa [twin_C3] using live_N7
  · simpa [twin_C3] using blocked_N7_S3

theorem fork_N6 : forkState N6 := ⟨_, forkWitness_N6⟩
theorem fork_N7 : forkState N7 := ⟨_, forkWitness_N7⟩

/-! ## §5. First fork, rungs, split -/

theorem live_N0 : liveB N0 = [] := by decide
theorem live_N1 : liveB N1 = [crd .heart .five] := by decide
theorem live_N2 : liveB N2 = [crd .heart .four] := by decide
theorem live_N3 : liveB N3 = [crd .heart .four] := by decide
theorem live_N4 : liveB N4 = [crd .heart .four] := by decide
theorem live_N5 : liveB N5 = [crd .spade .four, crd .heart .four] := by decide

theorem no_fork_N0 : ¬ forkState N0 := no_fork_of_liveB_nil wf_N0 live_N0
theorem no_fork_N1 : ¬ forkState N1 := no_fork_of_liveB_single wf_N1 live_N1
theorem no_fork_N2 : ¬ forkState N2 := no_fork_of_liveB_single wf_N2 live_N2
theorem no_fork_N3 : ¬ forkState N3 := no_fork_of_liveB_single wf_N3 live_N3
theorem no_fork_N4 : ¬ forkState N4 := no_fork_of_liveB_single wf_N4 live_N4
theorem no_fork_N5 : ¬ forkState N5 :=
  no_fork_of_liveB_pair wf_N5 (by decide) (by decide) (by decide) live_N5

theorem no_fork_before_N6 :
    ¬ forkState N0 ∧ ¬ forkState N1 ∧ ¬ forkState N2 ∧
      ¬ forkState N3 ∧ ¬ forkState N4 ∧ ¬ forkState N5 ∧ forkState N6 :=
  ⟨no_fork_N0, no_fork_N1, no_fork_N2, no_fork_N3, no_fork_N4, no_fork_N5, fork_N6⟩

theorem rungs_N6 :
    rungAt N6 .heart = 3 ∧ rungAt N6 .diamond = 0 ∧
      rungAt N6 .spade = 2 ∧ rungAt N6 .club = 2 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-! ## §6. The boundary theorem -/

/-- **THE PLAN-4 MINIMAL-PATH BOUNDARY.**  A 12-move, 9-bracket witness
play from `s1` to `t1` crosses a `(3,0,2,2)` fork at its sixth state (the
first fork on the path); the kernel 14-move play costs 11 brackets and
is fork-free throughout. -/
theorem minimal_play_crosses_fork_plan4 :
    s1.run minPlay = some t1 ∧
      minPlay.length = 12 ∧
      bracketCount minPlay = 9 ∧
      (∃ p q F, minPlay = p ++ q ∧ s1.run p = some F ∧ forkState F ∧
        rungAt F .heart = 3 ∧ rungAt F .diamond = 0 ∧
        rungAt F .spade = 2 ∧ rungAt F .club = 2) ∧
      (¬ forkState N0 ∧ ¬ forkState N1 ∧ ¬ forkState N2 ∧
        ¬ forkState N3 ∧ ¬ forkState N4 ∧ ¬ forkState N5 ∧ forkState N6) ∧
      s1.run play = some t1 ∧
      play.length = 14 ∧
      bracketCount play = 11 ∧
      (∀ G, G ∈ states → ¬ forkState G) ∧
      bracketCount minPlay < bracketCount play := by
  have hplay : s1.run play = some t1 := by
    rw [← F14_eq_t1]
    exact run_play
  refine ⟨run_minPlay, minPlay_length, bracketCount_minPlay,
    ⟨prefix6, suffix6, N6, minPlay_decomp, run_prefix6, fork_N6,
      rungs_N6.1, rungs_N6.2.1, rungs_N6.2.2.1, rungs_N6.2.2.2⟩,
    no_fork_before_N6,
    hplay, play_length, bracketCount_play, no_fork_states, ?_⟩
  decide

end SatDifferMin9P

#print axioms SatDifferMin9P.run_minPlay
#print axioms SatDifferMin9P.bracketCount_minPlay
#print axioms SatDifferMin9P.fork_N6
#print axioms SatDifferMin9P.fork_N7
#print axioms SatDifferMin9P.rungs_N6
#print axioms SatDifferMin9P.no_fork_before_N6
#print axioms SatDifferMin9P.minimal_play_crosses_fork_plan4