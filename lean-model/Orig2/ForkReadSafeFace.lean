import Orig2.ForkCrossSuitPartition
import Orig2.ForkFace1
import Orig2.ForkOffWindow

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-!
# CrossSuit_ReadSafe — the read-unsafe face is EMPTY

READ-ONLY scratch card (`Temp/`).  No source edit, no commit.  Zero `sorry`,
zero `Classical.choice`, zero `native_decide`; battery at the tail.

## The vacuity, in one paragraph

The partition card (`Orig2/ForkCrossSuitPartition.lean`) split the cross-suit
corridor universe into four faces.  Face 2 — `NoReadUnsafe` — is the
`Pullable B d b` corridors whose free window breaks `SlideFwd.ReadSafe d`.
**This face is empty, unconditionally** (no saturation, no minimality): in a
free window every letter is a draw or a slide, `ReadSafe d` only forbids
slides **headed by `d`** and slides **landing on `d`**, and both are
*illegal* while `d` is founded — which it is, throughout the window, because
`Pullable B d b` founds it at the window's start and a free window fixes the
foundation (`CrossSuitPart.foundTop_free_window`).  A slide headed by `d`
needs `d` face-up on a pile (`step_tabToTab_inv`'s `pileHolding`), a slide
landing on `d` needs `d` to top a pile (`canPlace`'s `inr` branch); `WF`'s
`mem_found_unique` forbids both for a founded card.

So the corridor universe is **three faces**, not four: the seat-mate face
(the parallel lane's), the prepared-seat face (the twin exchange), and the
seat-acting face (`NoSeatActing` — which is *not* vacuous: `z` tops a pile
in the `Pullable` case, so slides headed by `z` are legal).  The next move
there is recorded below: the seat-relocation slide is twin-constrained by
the twin-source law.
-/

namespace CrossSuitRS

open ValleyElim

/-! ## §1. The letter: a free slide at a founded-`d` state is read-safe -/

/-- **A SLIDE AT A STATE WHERE `d` TOPS ITS FOUNDATION COLUMN IS READ-SAFE
FOR `d`.**  The slide's mover must be face-up on its source pile and its
base must accept it; if the mover were `d` itself, `d` would be face-up
*and* founded (contradicting `WF`'s `mem_found_unique`), and if the base
were `inr d`, `d` would have to top a pile (`canPlace`'s `inr` branch) —
again impossible for a founded card. -/
theorem readSafe_slide {M M' : State} {x : Card} {b' : Base} {d : Card}
    (hstep : State.step M (Move.tabToTab x b') = some M')
    (hwfM : M.WF) (htop : M.foundTop d.suit = some d) :
    SlideFwd.ReadSafe d (Move.tabToTab x b') := by
  obtain ⟨a, hh, hcp, -, -⟩ := step_tabToTab_inv hstep
  refine ⟨?_, ?_⟩
  · intro hxd
    rw [hxd] at hh
    exact (mem_found_unique hwfM (lastOf_mem htop)).1 a |>.2 (pileHolding_mem hh)
  · cases b' with
    | inl a₀ => exact fun h => by cases h
    | inr w =>
        intro hw
        injection hw with hwd
        rw [hwd] at hcp
        have hnone : M.pileOfTop d = none := by
          cases h : M.pileOfTop d with
          | none => rfl
          | some k =>
              exfalso
              have hp' : firstWhere (fun a' => decide (M.topOf a' = some d)) Anchor.all
                  = some k := h
              have h3 : lastOf ((M.piles k).faceUp) = some d :=
                of_decide_eq_true
                  (firstWhere_sound (fun a' => decide (M.topOf a' = some d)) hp')
              exact (mem_found_unique hwfM (lastOf_mem htop)).1 k |>.2 (lastOf_mem h3)
        exact (CrossSuitF1.canPlace_inr_true_iff.mp hcp).1 hnone

/-! ## §2. The window: a free window over a founded card is read-safe -/

/-- **A FREE WINDOW IS READ-SAFE FOR A CARD IT CARRIES FOUNDED.**  Each
letter is a draw (read-safe by definition) or a slide (§1); the foundation
top — hence `d`'s foundedness — transports through the window. -/
theorem readSafe_free_window (d : Card) :
    ∀ (γ : List Move) {B P : State},
      ShufflePlayW B γ P → Canon.FreeOnly γ → B.WF →
      B.foundTop d.suit = some d →
      ∀ q ∈ γ, SlideFwd.ReadSafe d q := by
  intro γ
  induction γ with
  | nil => intro B P _ _ _ _ q hq; exact absurd hq (by simp)
  | cons m t ih =>
      intro B P hplay hfree hwfB htop q hq
      obtain ⟨M, hγ1, hrest⟩ := ValleyElim.ShufflePlayW_split hplay [m] t rfl
      obtain ⟨M2, hrevA, hstep, hnil⟩ := Bubble.walk_cons_inv hγ1
      cases hnil
      have hrd : SlideFwd.ReadSafe d m := by
        rcases hfree m (List.mem_cons_self ..) with rfl | ⟨x, b', rfl⟩
        · trivial
        · exact readSafe_slide hstep hwfB htop
      rcases List.mem_cons.mp hq with rfl | hq'
      · exact hrd
      · have hfree1 : ∀ q' ∈ [m], ValleyElim.FreeMove q' := by
          intro q' hq'
          rw [List.mem_singleton.mp hq']
          exact hfree m (List.mem_cons_self ..)
        have htopM : M.foundTop d.suit = some d :=
          (CrossSuitPart.foundTop_free_window d.suit hγ1 hfree1).symm.trans htop
        exact ih hrest (fun q' hq' => hfree q' (List.mem_cons_of_mem _ hq'))
          (step_wf hwfB hstep) htopM q hq'

/-! ## §3. The face collapse -/

/-- **THE READ-UNSAFE FACE IS EMPTY — UNCONDITIONALLY.**  No saturation, no
minimality, no cross-suit hypothesis: any corridor of the partition's shape
whose pull is ready at the raise's landing has an automatically read-safe
free window.  The partition's four faces are three: seat-mate,
prepared-seat, seat-acting. -/
theorem noReadUnsafe : CrossSuitPart.NoReadUnsafe := by
  intro u v ρ pre γ tail c d b A B hwf hu hv hplay hminlen hmininv heq hfree hsu
    hpre hstepR hpull hnr
  have hplay' : ShufflePlayW u
      (pre ++ (Move.tabToFound c :: (γ ++ (Move.foundToTab d b :: tail)))) v := by
    rw [← heq]; exact hplay
  have hdecomp : ρ = (pre ++ [Move.tabToFound c]) ++
      (γ ++ (Move.foundToTab d b :: tail)) := by
    rw [heq]; simp [List.append_assoc]
  obtain ⟨B', hleft, hright⟩ := ValleyElim.ShufflePlayW_split hplay _ _ hdecomp
  obtain ⟨M, hupre, hraise⟩ := Bubble.walk_split pre hleft
  have hMA : M = A := OffWindow.walk_end_unique hupre hpre
  obtain ⟨s1, -, hstep1, hnil⟩ := Bubble.walk_cons_inv hraise
  cases hnil
  have hB'B : B' = B := by
    rw [hMA] at hstep1
    exact Option.some.inj (hstep1.symm.trans hstepR)
  rw [hB'B] at hright
  obtain ⟨P, hγwalk, hrest2⟩ := Bubble.walk_split γ hright
  have hAwf : A.WF := SatDifferCensus.ShufflePlayW.wf_end hpre hwf
  have hBwf : B.WF := step_wf hAwf hstepR
  exact hnr (readSafe_free_window d γ hγwalk hfree hBwf hpull.1)

end CrossSuitRS

#print axioms CrossSuitRS.readSafe_slide
#print axioms CrossSuitRS.readSafe_free_window
#print axioms CrossSuitRS.noReadUnsafe
