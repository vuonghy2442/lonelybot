import Orig2.Fork.Class.ForkRaiseReorderProof
import Orig2.Fork.Commute.RungMono
import Orig2.Fork.Commute.PullRaiseId
import Orig2.Fork.Commute.Obstruction
import Orig2.Fork.Commute.FrozenSuit
import Orig2.Fork.Commute.RaisesOrFork
import Orig2.Fork.Commute.BlockHousing

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

namespace OneColourClosure

theorem sameOrbit_of_revStep {s u : State} {m : Move}
    (hrev : reversibleAtW s m) (hstep : State.step s m = some u) :
    sameOrbitSetoid.r u s :=
  shufflePlayW_revEqW (Walk.cons hrev hstep (Walk.nil u))

theorem sameOrbit_of_revStep' {s u : State} {m : Move}
    (hrev : reversibleAtW s m) (hstep : State.step s m = some u) :
    sameOrbitSetoid.r s u :=
  sameOrbitSetoid.iseqv.symm (sameOrbit_of_revStep hrev hstep)

theorem fork_of_sameOrbit {u v : State} (h : sameOrbitSetoid.r u v) (hf : Fork u) :
    Fork v := by
  obtain ⟨F, x, hF, hw⟩ := hf
  exact ⟨F, x, sameOrbitSetoid.iseqv.trans (sameOrbitSetoid.iseqv.symm h) hF, hw⟩

theorem rungLe_of_rung_eq {u v : State} (h : ∀ σ, rungAt u σ = rungAt v σ)
    {w : State} (hw : RungLe w u) : RungLe w v :=
  fun σ => by rw [← h σ]; exact hw σ

theorem replay_of_orbit_rung {a b v : State} {ws : List Card}
    (ha : a.WF) (horb : sameOrbitSetoid.r a b)
    (hrung : ∀ σ, rungAt a σ = rungAt b σ)
    (h : RaiseSSeqLicensed b ws v) :
    ∃ v', RaiseSSeqLicensed a ws v' ∧
      (∀ σ, rungAt v σ = rungAt v' σ) ∧ sameOrbitSetoid.r v v' := by
  have hb : b.WF := by
    obtain ⟨_, _, τ, hτ⟩ := horb
    exact walk_wf ha hτ
  induction h generalizing a with
  | nil =>
      exact ⟨a, RaiseSSeqLicensed.nil a, fun σ => (hrung σ).symm,
        sameOrbitSetoid.iseqv.symm horb⟩
  | cons htail hS hp hstep ih =>
      rename_i zz z0 z' c wws
      have hzwf : zz.WF := RaiseSSeqLicensed.wf htail hb
      obtain ⟨z1, hplay1, hrung1, horb1⟩ := ih ha horb hrung
      have hcan1 : CanRaiseS z1 c :=
        (canRaiseS_orbit_rung hzwf horb1 hrung1).mp hS
      obtain ⟨z1', hsingle⟩ := raiseSSeqLicensed_step_of_canRaiseS hcan1
      have hfullNew : RaiseSSeqLicensed a (c :: wws) z1' :=
        RaiseSSeqLicensed.append hplay1 hsingle
      have hfullOld : RaiseSSeqLicensed b (c :: wws) z' :=
        RaiseSSeqLicensed.cons htail hS hp hstep
      refine ⟨z1', hfullNew, ?_, ?_⟩
      · intro σ
        rw [hfullOld.rungAt_eq σ, hfullNew.rungAt_eq σ, hrung σ]
      · have h1 : sameOrbitSetoid.r z' b := hfullOld.revEqW hb
        have h2 : sameOrbitSetoid.r b a := sameOrbitSetoid.iseqv.symm horb
        have h3 : sameOrbitSetoid.r a z1' :=
          sameOrbitSetoid.iseqv.symm (hfullNew.revEqW ha)
        exact sameOrbitSetoid.iseqv.trans (sameOrbitSetoid.iseqv.trans h1 h2) h3

/-- **Counting after `erase`.**  Removing an occurrence of `c` drops the count of
any predicate true at `c` by exactly one, and leaves the others alone.  (The
additive form, so no truncated subtraction appears.) -/
theorem countP_erase_add {l : List Card} {c : Card} (h : c ∈ l) (p : Card → Bool) :
    (l.erase c).countP p + (if p c then 1 else 0) = l.countP p := by
  induction l with
  | nil => simp at h
  | cons a t ih =>
      by_cases hac : a = c
      · subst hac
        rw [List.erase_cons_head, List.countP_cons]
      · have hc : c ∈ t := by
          rcases List.mem_cons.mp h with h' | h'
          · exact absurd h'.symm hac
          · exact h'
        have hbeq : (a == c) = false := by
          cases hb : (a == c) with
          | false => rfl
          | true => exact absurd (beq_iff_eq.mp hb) hac
        have hih := ih hc
        rw [List.erase_cons_tail (a := c) (b := a) (by rw [hbeq]; simp),
          List.countP_cons, List.countP_cons]
        omega

/-! ## §3. The path induction -/

/-- **The path induction.**  Along any witness shuffle `s ⇝ t`, either there is
a licensed `raiseS` play from `s` dominating both endpoints rungwise, or `s`
is already a fork.

The cases are the five reversible letters (`wasteToFound`/`wasteToTab` are
never reversible).  Raises are prepended, slides and draws are replayed across
an orbit-rung mate (`replay_of_orbit_rung`), and the pull case is exactly
`hPull`. -/
theorem raises_or_fork_play
    (hPull : ∀ {s u t v : State} {c : Card} {b : Base} {ws : List Card},
      s.WF → State.step s (Move.foundToTab c b) = some u →
      RaiseSSeqLicensed u ws v → RungLe t v →
      (∃ ws' v', RaiseSSeqLicensed s ws' v' ∧ RungLe s v' ∧ RungLe t v')
      ∨ Fork s)
    {s t : State} {play : List Move} (hplay : ShufflePlayW s play t) (hs : s.WF) :
    (∃ ws v, RaiseSSeqLicensed s ws v ∧ RungLe s v ∧ RungLe t v) ∨ Fork s := by
  revert hs
  refine Walk.rec
    (motive := fun st _ W _ =>
      st.WF → (∃ ws v, RaiseSSeqLicensed st ws v ∧ RungLe st v ∧ RungLe W v)
        ∨ Fork st)
    ?_ ?_ hplay
  · intro st hst
    exact Or.inl ⟨[], st, RaiseSSeqLicensed.nil st, fun _ => Nat.le_refl _,
      fun _ => Nat.le_refl _⟩
  · intro st s1 W m ρ hlet hstep hrest ih hst
    have hs1 : s1.WF := step_wf hst hstep
    have horb : sameOrbitSetoid.r st s1 := sameOrbit_of_revStep' hlet hstep
    have hsymm : sameOrbitSetoid.r s1 st := sameOrbitSetoid.iseqv.symm horb
    cases m with
    | draw =>
        rcases ih hs1 with ⟨ws, v, hρ, hsv, htv⟩ | hfork
        · obtain ⟨v', hplay', hrung', _⟩ :=
            replay_of_orbit_rung hst horb (fun σ => (rungAt_draw hstep σ).symm) hρ
          exact Or.inl ⟨_, v', hplay', rungLe_of_raiseSSeqLicensed hplay',
            rungLe_of_rung_eq hrung' htv⟩
        · exact Or.inr (fork_of_sameOrbit hsymm hfork)
    | wasteToFound c =>
        exact absurd hlet (wasteToFound_not_reversibleAtW st c)
    | wasteToTab c b =>
        exact absurd hlet (wasteToTab_not_reversibleAtW st c b)
    | tabToFound c =>
        have hcan : CanRaise st c := canRaise_of_reversibleAtW hst hlet
        have hsingle : RaiseSSeqLicensed st [c] s1 :=
          RaiseSSeqLicensed.cons (RaiseSSeqLicensed.nil st)
            (CanRaiseS.now c hcan) (Steps.refl st) hstep
        rcases ih hs1 with ⟨ws, v, hρ, hsv, htv⟩ | hfork
        · have hfull : RaiseSSeqLicensed st (ws ++ [c]) v :=
            RaiseSSeqLicensed.append hsingle hρ
          exact Or.inl ⟨_, v, hfull, rungLe_of_raiseSSeqLicensed hfull, htv⟩
        · exact Or.inr (fork_of_sameOrbit hsymm hfork)
    | foundToTab c b =>
        rcases ih hs1 with ⟨ws, v, hρ, huv, htv⟩ | hfork
        · rcases hPull hst hstep hρ htv with ⟨ws', v', hplay', hsv', htv'⟩ | hfork'
          · exact Or.inl ⟨ws', v', hplay', hsv', htv'⟩
          · exact Or.inr hfork'
        · exact Or.inr (fork_of_sameOrbit hsymm hfork)
    | tabToTab c b =>
        rcases ih hs1 with ⟨ws, v, hρ, hsv, htv⟩ | hfork
        · obtain ⟨v', hplay', hrung', _⟩ :=
            replay_of_orbit_rung hst horb (fun σ => (rungAt_tabToTab hstep σ).symm) hρ
          exact Or.inl ⟨_, v', hplay', rungLe_of_raiseSSeqLicensed hplay',
            rungLe_of_rung_eq hrung' htv⟩
        · exact Or.inr (fork_of_sameOrbit hsymm hfork)

end OneColourClosure

#print axioms OneColourClosure.sameOrbit_of_revStep
#print axioms OneColourClosure.sameOrbit_of_revStep'
#print axioms OneColourClosure.fork_of_sameOrbit
#print axioms OneColourClosure.rungLe_of_rung_eq
#print axioms OneColourClosure.replay_of_orbit_rung
#print axioms OneColourClosure.countP_erase_add
#print axioms OneColourClosure.raises_or_fork_play
