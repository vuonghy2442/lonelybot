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

/-! ## §2. The pull case: append the pulled card, hoist, cancel -/

/-- **The pull case, given the endpoint licence.**  If `c` is still `S`-live at
the endpoint `v` of a licensed play from the pull's landing `u`, then `c` can be
appended, hoisted to the front (`raiseS_rankfront_L`), and cancelled against the
pull (`cancel_prefix_is_play_from_source`).  The result is a play from the pull
source `s` whose endpoint is `v + e_c`. -/
theorem pull_case_of_end_live {s u v : State} {c : Card} {b : Base}
    {ws : List Card}
    (hs : s.WF) (hpull : State.step s (Move.foundToTab c b) = some u)
    (hρ : RaiseSSeqLicensed u ws v) (hcz : CanRaiseS v c) :
    ∃ v', RaiseSSeqLicensed s (playWord (sortByRank ws)) v' ∧
      (∀ σ, σ ≠ c.suit → rungAt v' σ = rungAt v σ) ∧
      rungAt v' c.suit = rungAt v c.suit + 1 := by
  have hu : u.WF := step_wf hs hpull
  have hcanU : CanRaiseS u c := SatDifferConfig.canRaiseS_after_pull hs hpull
  have hcan : CanRaise u c := SatDifferConfig.canRaise_after_pull hs hpull
  obtain ⟨v₁, happ⟩ := exists_append_raise hρ hcz
  have hmem : c ∈ c :: ws := List.mem_cons_self ..
  obtain ⟨z, hz⟩ := raiseS_rankfront_L hu hcanU happ hmem
  have hword : rankFrontWord c (c :: ws) = playWord (c :: sortByRank ws) := by
    simp [rankFrontWord, playWord, List.erase_cons_head]
  have hz' : RaiseSSeqLicensed u (playWord (c :: sortByRank ws)) z := by
    rwa [hword] at hz
  obtain ⟨v', hv'⟩ := cancel_prefix_is_play_from_source hs hpull hcan hz'
  have hstepUS : State.step u (Move.tabToFound c) = some s :=
    step_tabToFound_of_foundToTab hs hpull
  have hperm : (playWord (sortByRank ws)).Perm ws := by
    rw [playWord]
    exact (reverse_perm (sortByRank ws)).trans (sortByRank_perm ws)
  refine ⟨v', hv', ?_, ?_⟩
  · intro σ hσ
    rw [hv'.rungAt_eq σ, hρ.rungAt_eq σ,
      hperm.countP_eq (fun d => decide (d.suit = σ)),
      rungAt_foundToTab hpull σ, ite_eq_right hσ]
  · rw [hv'.rungAt_eq c.suit, hρ.rungAt_eq c.suit,
      hperm.countP_eq (fun d => decide (d.suit = c.suit)),
      rungAt_tabToFound hstepUS c.suit, ite_eq_left rfl]
    omega

/-- **The pull case when the play already raises `c`.**  Hoisting the existing
`raise c` to the front and cancelling against the pull yields a play from `s`
with the *same* endpoint rungs (`ws.erase c` is the remaining word). -/
theorem pull_case_mem {s u v : State} {c : Card} {b : Base} {ws : List Card}
    (hs : s.WF) (hpull : State.step s (Move.foundToTab c b) = some u)
    (hρ : RaiseSSeqLicensed u ws v) (hmem : c ∈ ws) :
    ∃ v', RaiseSSeqLicensed s (playWord (sortByRank (ws.erase c))) v' ∧
      (∀ σ, rungAt v' σ = rungAt v σ) := by
  have hu : u.WF := step_wf hs hpull
  have hcanU : CanRaiseS u c := SatDifferConfig.canRaiseS_after_pull hs hpull
  have hcan : CanRaise u c := SatDifferConfig.canRaise_after_pull hs hpull
  obtain ⟨z, hz⟩ := raiseS_rankfront_L hu hcanU hρ hmem
  have hword : rankFrontWord c ws = playWord (c :: sortByRank (ws.erase c)) := by
    simp [rankFrontWord, playWord]
  have hz' : RaiseSSeqLicensed u (playWord (c :: sortByRank (ws.erase c))) z := by
    rwa [hword] at hz
  obtain ⟨v', hv'⟩ := cancel_prefix_is_play_from_source hs hpull hcan hz'
  have hstepUS : State.step u (Move.tabToFound c) = some s :=
    step_tabToFound_of_foundToTab hs hpull
  have hperm : (playWord (sortByRank (ws.erase c))).Perm (ws.erase c) := by
    rw [playWord]
    exact (reverse_perm (sortByRank (ws.erase c))).trans (sortByRank_perm (ws.erase c))
  refine ⟨v', hv', ?_⟩
  intro σ
  rw [hv'.rungAt_eq σ, hρ.rungAt_eq σ,
    hperm.countP_eq (fun d => decide (d.suit = σ))]
  have herase := countP_erase_add hmem (fun d => decide (d.suit = σ))
  by_cases hσ : σ = c.suit
  · have hp1 : (if decide (c.suit = σ) = true then 1 else 0) = 1 := by
      rw [hσ]; simp
    rw [hp1] at herase
    have hsR : rungAt s σ = rungAt u σ + 1 := by
      rw [rungAt_tabToFound hstepUS σ, ite_eq_left hσ]
    omega
  · have hp0 : (if decide (c.suit = σ) = true then 1 else 0) = 0 := by
      have hne : c.suit ≠ σ := fun h => hσ h.symm
      rw [decide_eq_false hne]; rfl
    rw [hp0] at herase
    rw [rungAt_foundToTab hpull σ, ite_eq_right hσ]
    omega

/-- **THE PULL CASE, non-twin, CLOSED UNCONDITIONALLY.**  This is the fragment
of `hPull` that needs no in-flight input: the tail play avoids `c`'s suit and
`c.twin`, so `c` stays `S`-live at the endpoint (`canRaiseS_of_word_notMem`),
and `pull_case_of_end_live` supplies the play from `s`; its endpoint is
`v + e_c`, hence dominates both `s` and `t`.

The only surviving pull sub-case is `c.twin ∈ ws` (and `c ∉ ws`), which is
exactly the `∨ Fork s` arm of `hPull`. -/
theorem pull_case_noTwin {s u v t : State} {c : Card} {b : Base} {ws : List Card}
    (hs : s.WF) (hpull : State.step s (Move.foundToTab c b) = some u)
    (hρ : RaiseSSeqLicensed u ws v)
    (hno : ∀ d ∈ ws, d.suit ≠ c.suit) (htwin : c.twin ∉ ws) (ht : RungLe t v) :
    ∃ v', RaiseSSeqLicensed s (playWord (sortByRank ws)) v' ∧
      RungLe s v' ∧ RungLe t v' := by
  have hu : u.WF := step_wf hs hpull
  have hcanU : CanRaiseS u c := SatDifferConfig.canRaiseS_after_pull hs hpull
  have hself : c ∉ ws := fun hmem => hno c hmem rfl
  have hcz : CanRaiseS v c := canRaiseS_of_word_notMem hρ hu hcanU hself htwin
  obtain ⟨v', hplay', hoff, hon⟩ := pull_case_of_end_live hs hpull hρ hcz
  refine ⟨v', hplay', rungLe_of_raiseSSeqLicensed hplay', fun σ => ?_⟩
  by_cases hσ : σ = c.suit
  · subst hσ
    rw [hon]
    exact Nat.le_trans (ht c.suit) (Nat.le_succ _)
  · rw [hoff σ hσ]
    exact ht σ

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

/-- **RAISE-OR-FORK, from the two sub-goals.**

`hPull` is the pull step (append `raise c` to the tail, hoist it to the front,
cancel against the pull; the `∨ Fork s` arm carries the twin-stuck case).
`hspectrum` is the spectrum dichotomy; the induction below does not consume it
— the fork disjunct is only ever *lifted* along the orbit — and it is carried
to match the interface.

The target's `RungLe s v` conjunct is free (`rungLe_of_raiseSSeqLicensed`). -/
theorem raises_or_fork_of
    (hPull : ∀ {s u t v : State} {c : Card} {b : Base} {ws : List Card},
      s.WF → State.step s (Move.foundToTab c b) = some u →
      RaiseSSeqLicensed u ws v → RungLe t v →
      (∃ ws' v', RaiseSSeqLicensed s ws' v' ∧ RungLe s v' ∧ RungLe t v')
      ∨ Fork s)
    (hspectrum : ∀ {z : State} {x : Card}, z.WF → CanRaiseS z x → CanRaiseS z x.twin →
      Fork z ∨
        ∃ z', sameOrbitSetoid.r z z' ∧
          (∀ c, CanRaiseS z' c → c = x ∨ c = x.twin) ∧
          CanRaise z' x ∧ CanRaise z' x.twin)
    {s t : State} (hs : s.WF) (h : sameOrbitSetoid.r s t) :
    (∃ ws v, RaiseSSeqLicensed s ws v ∧ RungLe s v ∧ RungLe t v) ∨ Fork s := by
  obtain ⟨_, _, play, hplay⟩ := h
  exact raises_or_fork_play hPull hplay hs

/-- **THE ROUTE'S PAYOFF.**  The conditional raise-or-fork theorem implies
`FullJoinAtLeastOrFork` with the join witness `w := v` supplied by the play
itself (via `fullJoinAtLeastOrFork_of_raises_or_fork`, no residue). -/
theorem fullJoinAtLeastOrFork_of_hPull
    (hPull : ∀ {s u t v : State} {c : Card} {b : Base} {ws : List Card},
      s.WF → State.step s (Move.foundToTab c b) = some u →
      RaiseSSeqLicensed u ws v → RungLe t v →
      (∃ ws' v', RaiseSSeqLicensed s ws' v' ∧ RungLe s v' ∧ RungLe t v')
      ∨ Fork s)
    (hspectrum : ∀ {z : State} {x : Card}, z.WF → CanRaiseS z x → CanRaiseS z x.twin →
      Fork z ∨
        ∃ z', sameOrbitSetoid.r z z' ∧
          (∀ c, CanRaiseS z' c → c = x ∨ c = x.twin) ∧
          CanRaise z' x ∧ CanRaise z' x.twin) :
    FullJoinAtLeastOrFork :=
  fullJoinAtLeastOrFork_of_raises_or_fork
    (fun s t hs h => raises_or_fork_of hPull hspectrum hs h)

end OneColourClosure

#print axioms OneColourClosure.sameOrbit_of_revStep
#print axioms OneColourClosure.sameOrbit_of_revStep'
#print axioms OneColourClosure.fork_of_sameOrbit
#print axioms OneColourClosure.rungLe_of_rung_eq
#print axioms OneColourClosure.replay_of_orbit_rung
#print axioms OneColourClosure.countP_erase_add
#print axioms OneColourClosure.pull_case_of_end_live
#print axioms OneColourClosure.pull_case_mem
#print axioms OneColourClosure.pull_case_noTwin
#print axioms OneColourClosure.raises_or_fork_play
#print axioms OneColourClosure.raises_or_fork_of
#print axioms OneColourClosure.fullJoinAtLeastOrFork_of_hPull
