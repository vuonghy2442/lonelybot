import Orig2.Fork.Commute.BoundedFlatPath
import Orig2.Fork.Commute.ForklessTop
import Orig2.Fork.Commute.PullCommute
import Orig2.Fiber.ArmSplit
import Orig2.Fork.Local.ForkCriticalPair

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# Orig2.Fork.Commute.FlatFailureFork - the constructive explicit-witness form

A saturated same-orbit pair outside the flat fiber exhibits a `ForkWitness`
somewhere in its class.  The proof is constructive: a finite scan of the
actual connecting play extracts any state that overshoots the origin rung,
that state is saturated above, and `satDifferForkWF_proved` yields the fork.
No `Classical.choice` is used.
-/

open OneColourClosure

/-- `RungLe` is decidable by the four-suit enumeration (no `Fintype`). -/
private instance instDecidableRungLe (z u : State) : Decidable (RungLe z u) :=
  decidable_of_iff
    (rungAt z .spade ≤ rungAt u .spade ∧
     rungAt z .heart ≤ rungAt u .heart ∧
     rungAt z .diamond ≤ rungAt u .diamond ∧
     rungAt z .club ≤ rungAt u .club)
    (by
      constructor
      · rintro ⟨h1, h2, h3, h4⟩ s
        cases s
        · exact h1
        · exact h2
        · exact h3
        · exact h4
      · intro h
        exact ⟨h .spade, h .heart, h .diamond, h .club⟩)

/-- The states on a nonempty play are the start or states on the tail. -/
private theorem stateOnPlay_cons {s s1 : State} {m : Move} {rest : List Move}
    (hstep : State.step s m = some s1) {z : State} :
    StateOnPlay s (m :: rest) z ↔ z = s ∨ StateOnPlay s1 rest z := by
  constructor
  · rintro ⟨pre, post, hspl, hrun⟩
    cases pre with
    | nil =>
        left
        have hz' : s.run [] = some z := hrun
        rw [show s.run [] = some s from rfl] at hz'
        exact (Option.some.inj hz').symm
    | cons m' pre' =>
        right
        have hspl' : m :: rest = m' :: (pre' ++ post) := by
          simpa using hspl
        injection hspl' with hm hrest
        rw [← hm] at hrun
        have hrun' : s1.run pre' = some z := by
          simpa only [State.run, hstep] using hrun
        exact ⟨pre', post, hrest, hrun'⟩
  · rintro (rfl | ⟨pre, post, hspl, hrun⟩)
    · exact ⟨[], m :: rest, rfl, rfl⟩
    · refine ⟨m :: pre, post, ?_, ?_⟩
      · simp [hspl]
      · simpa only [State.run, hstep] using hrun

/-- From a failed pointwise bound, extract the suit that overshoots. -/
private theorem exists_gt_of_not_rungLe {z u : State} (h : ¬ RungLe z u) :
    ∃ σ : Suit, rungAt u σ < rungAt z σ := by
  by_cases h1 : rungAt u .spade < rungAt z .spade
  · exact ⟨.spade, h1⟩
  · by_cases h2 : rungAt u .heart < rungAt z .heart
    · exact ⟨.heart, h2⟩
    · by_cases h3 : rungAt u .diamond < rungAt z .diamond
      · exact ⟨.diamond, h3⟩
      · by_cases h4 : rungAt u .club < rungAt z .club
        · exact ⟨.club, h4⟩
        · exfalso
          apply h
          intro σ
          cases σ
          · exact Nat.le_of_not_lt h1
          · exact Nat.le_of_not_lt h2
          · exact Nat.le_of_not_lt h3
          · exact Nat.le_of_not_lt h4

/-- A finite scan: either every visited state stays below `u`, or one visited
state overshoots.  Constructive: the case split is a decidable `RungLe`. -/
private theorem onPlay_bounded_or_witness {u : State} {s W : State} {play : List Move}
    (hplay : ShufflePlayW s play W) :
    (∀ z, StateOnPlay s play z → RungLe z u) ∨
      ∃ z, StateOnPlay s play z ∧ ¬ RungLe z u := by
  induction hplay with
  | nil st =>
      by_cases hle : RungLe st u
      · left
        intro z hz
        obtain ⟨pre, post, hspl, hrun⟩ := hz
        have hpre : pre = [] := (List.append_eq_nil_iff.mp hspl.symm).1
        subst hpre
        have hz' : st.run [] = some z := hrun
        rw [show st.run [] = some st from rfl] at hz'
        have hzeq : z = st := (Option.some.inj hz').symm
        simpa [hzeq] using hle
      · right
        exact ⟨st, ⟨[], [], rfl, rfl⟩, hle⟩
  | @cons st s1 W m rest hrev hstep hrest ih =>
      by_cases hle : RungLe st u
      · rcases ih with hb | ⟨z, hz, hzle⟩
        · left
          intro w hw
          have hw' : w = st ∨ StateOnPlay s1 rest w :=
            (stateOnPlay_cons hstep).mp hw
          rcases hw' with rfl | hw'
          · exact hle
          · exact hb w hw'
        · right
          refine ⟨z, ?_, hzle⟩
          exact (stateOnPlay_cons hstep).mpr (Or.inr hz)
      · right
        refine ⟨st, ?_, hle⟩
        exact (stateOnPlay_cons hstep).mpr (Or.inl rfl)

/-- An unbounded state on a witness play yields a class fork. -/
private theorem fork_of_unbounded_onPlay
    {u v : State} {play : List Move}
    (hu : u.WF) (hsu : SSaturated u)
    (hplay : ShufflePlayW u play v) {z : State}
    (hzOn : StateOnPlay u play z) (hzUnb : ¬ RungLe z u) :
    ∃ F x, sameOrbitSetoid.r u F ∧ ForkWitness F x := by
  obtain ⟨pre, post, hspl, hrun⟩ := hzOn
  obtain ⟨z0, hpre, _hpost⟩ :=
    ValleyElim.ShufflePlayW_split hplay pre post hspl
  have hz0z : z0 = z :=
    Option.some.inj ((Walk_run _ hpre).symm.trans hrun)
  have huz0 : sameOrbitSetoid.r u z0 :=
    RevEqW_symm (shufflePlayW_revEqW hpre)
  have huz : sameOrbitSetoid.r u z := hz0z ▸ huz0
  have hzwf : z.WF := wf_of_sameOrbit huz hu
  obtain ⟨z', hzz', _hz'wf, hz'sat, hz'le⟩ :=
    ForklessTop.exists_saturated_above z hzwf
  have huz' : sameOrbitSetoid.r u z' :=
    sameOrbitSetoid.iseqv.trans huz hzz'
  obtain ⟨σ, hσ⟩ := exists_gt_of_not_rungLe hzUnb
  have hlt : rungAt u σ < rungAt z' σ :=
    Nat.lt_of_lt_of_le hσ (hz'le σ)
  exact OneColourClosure.satDifferForkWF_proved u z' hu hsu hz'sat huz'
    ⟨σ, Nat.ne_of_lt hlt⟩

/-- **Constructive flat-or-fork dichotomy on a given play.** -/
theorem flat_or_fork_on_play
    {u v : State} {play : List Move}
    (hu : u.WF) (hsu : SSaturated u) (hsv : SSaturated v)
    (horb : sameOrbitSetoid.r u v)
    (hplay : ShufflePlayW u play v) :
    BareFlatEquiv u v ∨
      ∃ F x, sameOrbitSetoid.r u F ∧ ForkWitness F x := by
  by_cases hdiff : ∃ σ : Suit, rungAt u σ ≠ rungAt v σ
  · exact Or.inr (OneColourClosure.satDifferForkWF_proved u v hu hsu hsv horb hdiff)
  · have hrung : RungEq u v := rungEq_of_no_differing hdiff
    have hv : v.WF := wf_of_sameOrbit horb hu
    rcases onPlay_bounded_or_witness (u := u) hplay with hb | ⟨z, hzOn, hzUnb⟩
    · exact Or.inl
        (bareFlatEquiv_of_rungBoundedPath hu hv ⟨play, hplay, hb⟩ hrung)
    · exact Or.inr (fork_of_unbounded_onPlay hu hsu hplay hzOn hzUnb)

/-- **Constructive flat-or-fork dichotomy.**  No forkless hypothesis: the
fork branch carries an explicit witness. -/
theorem flat_or_fork
    {u v : State}
    (hu : u.WF) (hsu : SSaturated u) (hsv : SSaturated v)
    (horb : sameOrbitSetoid.r u v) :
    BareFlatEquiv u v ∨
      ∃ F x, sameOrbitSetoid.r u F ∧ ForkWitness F x := by
  obtain ⟨-, -, play, hplay⟩ := horb
  have horb' : sameOrbitSetoid.r u v :=
    sameOrbitSetoid.iseqv.symm (shufflePlayW_revEqW hplay)
  exact flat_or_fork_on_play hu hsu hsv horb' hplay
/-- **Choice-free explicit-witness fork.** -/
theorem flat_failure_fork
    {u v : State}
    (hu : u.WF) (hsu : SSaturated u) (hsv : SSaturated v)
    (horb : sameOrbitSetoid.r u v)
    (hnf : ¬ BareFlatEquiv u v) :
    ∃ F x, sameOrbitSetoid.r u F ∧ ForkWitness F x := by
  obtain ⟨-, -, play, hplay⟩ := horb
  have horb' : sameOrbitSetoid.r u v :=
    sameOrbitSetoid.iseqv.symm (shufflePlayW_revEqW hplay)
  rcases flat_or_fork_on_play hu hsu hsv horb' hplay with hflat | hfork
  · exact False.elim (hnf hflat)
  · exact hfork


/-- `ForklessFlatNormalWF` implies the class-global witness form. -/
theorem satFlatFiberFork_of_forklessFlatNormalWF
    (_h : ForklessFlatNormalWF) : SatFlatFiberFork := by
  intro u v hu hsu hsv horb hnf
  exact flat_failure_fork hu hsu hsv horb hnf

/-- The unconditional instance of the class-global invariant. -/
theorem satFlatFiberFork_proved : SatFlatFiberFork := by
  intro u v hu hsu hsv horb hnf
  exact flat_failure_fork hu hsu hsv horb hnf

/-! ## Audit battery -/

#print axioms flat_or_fork_on_play
#print axioms flat_or_fork
#print axioms flat_failure_fork
#print axioms satFlatFiberFork_of_forklessFlatNormalWF
#print axioms satFlatFiberFork_proved
