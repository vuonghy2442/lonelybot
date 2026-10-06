import Orig.Macro
import Orig.Twin

/-!
# Orig — the reversible quotient and the macro descent

The combination chapter: the witness-form reversible quotient
(`RevEqW`), the twin-extended setoid (`sameOrbitSetoid` /
`SameOrbit`), and the descent of the verdicts onto both.

* `ShufflePlayW` — the witness form of `Macro.ShufflePlay`: every
  step carries not merely the negative fact `reversibleAt` but an
  explicit returning play (`Fate.reversibleAtW`).  The whole
  chapter is witness-driven, so the construction-side proofs are
  intuitionistic; the only classical step anywhere downstream is
  the one already inside `Macro.win_iff_macro`.
* `RevEqW` — positions joined by witness shuffles in both
  directions.  The verdict descends:
  `RevEqW_sameFate`.
* `sameOrbitSetoid` — the join of the twin relabeling with
  `RevEqW`.  Two positions are related when they are equal, twin,
  `RevEqW`-related, or `RevEqW`-related through a twin.  All four
  disjuncts are necessary: the twin of a `RevEqW`-class is again a
  class, so a twin hop followed by a class hop composes back into a
  plain `RevEqW` hop between source and target — a disjunct the
  2-disjunct "equal or twin-class" shape drops, and that shape is
  therefore not transitive.
* The macro descent: `MacroStep_of_RevEqW`, `MacroWin_of_RevEqW` —
  a witness shuffle at the front rebases any window without
  touching its tip; the rebase slides only the start, so the inner
  phases stack unchanged and the induction never needs to cross a
  commitment.
* The negative-form twin transports (`reversibleAt_twin` by
  direct contraposition, `ShufflePlay_twin`, `irreversibleAt_twin`
  by untwinning hypothetical returns, `MacroStep_twin`,
  `MacroWin_twin`) and the orbit-level descent
  `sameFate_orbit`, `MacroWin_sameFate_descend`.
* The quotient lifts `WinFromQ₂`, `MacroWinQ₂`, and
  `macro_on_classes`: on classes, the macro verdict and the play
  verdict coincide.
-/

/-! ## Witness shuffles -/

/-- A witness shuffle: a legal play whose every move carries an
explicit undoubling play back to the position it was played from
(the constructive content of `reversibleAt`). -/
inductive ShufflePlayW : State → List Move → State → Prop
  | nil (st : State) : ShufflePlayW st [] st
  | cons {st : State} {m : Move} {s₁ : State} {rest : List Move} {st' : State}
      (hw : reversibleAtW st m) (hstep : State.step st m = some s₁)
      (hrest : ShufflePlayW s₁ rest st') :
      ShufflePlayW st (m :: rest) st'

/-- A witness shuffle is, in particular, a legal play. -/
theorem ShufflePlayW_run {st : State} : ∀ {play : List Move} {st' : State},
    ShufflePlayW st play st' → st.run play = some st' := by
  intro play st' h
  induction h with
  | nil s => rfl
  | cons hw hstep hrest ih =>
      simp only [State.run, hstep]
      exact ih

/-- Witness shuffles concatenate: one to `b`, then one from `b` to
`c`, is one to `c`.  The induction re-roots at each cons, threading
the second shuffle through the recursion. -/
theorem ShufflePlayW_append {a : State} : ∀ {l₁ : List Move} {b : State},
    ShufflePlayW a l₁ b → ∀ {l₂ : List Move} {c : State},
    ShufflePlayW b l₂ c → ShufflePlayW a (l₁ ++ l₂) c := by
  intro l₁ b h
  induction h with
  | nil s =>
      intro l₂ c h₂
      exact h₂
  | cons hw hstep hrest ih =>
      intro l₂ c h₂
      exact .cons hw hstep (ih h₂)

/-- The forgetful map: erasing the returning-play witnesses of a
witness shuffle leaves a negative-form shuffle. -/
theorem ShufflePlayW_toNeg {st : State} : ∀ {play : List Move} {st' : State},
    ShufflePlayW st play st' → ShufflePlay st play st' := by
  intro play st' h
  induction h with
  | nil s => exact .nil s
  | cons hw hstep hrest ih =>
      exact .cons (reversibleAt_of_W hw) hstep ih

/-- The twin relabeling carries witness reversibility across the
conjugation: the step and the returning play twin step for step. -/
theorem reversibleAtW_twin {st : State} {m : Move} (h : reversibleAtW st m) :
    reversibleAtW st.twinMap m.twinMove := by
  obtain ⟨s₁, play, hstep, hrun⟩ := h
  refine ⟨s₁.twinMap, play.map Move.twinMove, ?_, ?_⟩
  · rw [← State.twin_step st m, hstep]
    rfl
  · exact twin_run s₁ play st hrun

/-- A whole witness shuffle twins: every guard by
`reversibleAtW_twin`, every step by `State.twin_step`. -/
theorem ShufflePlayW_twin {st : State} : ∀ {play : List Move} {st' : State},
    ShufflePlayW st play st' →
    ShufflePlayW st.twinMap (play.map Move.twinMove) st'.twinMap := by
  intro play st' h
  induction h with
  | nil s => exact .nil _
  | @cons st m s₁ rest st' hw hstep hrest ih =>
      have hstept : State.step st.twinMap m.twinMove = some s₁.twinMap := by
        rw [← State.twin_step st m, hstep]
        rfl
      exact .cons (reversibleAtW_twin hw) hstept ih

/-! ## The witness reversible quotient relation -/

/-- The reversible quotient in witness form: two positions joined
by witness shuffles in both directions. -/
def RevEqW (s s' : State) : Prop :=
  ∃ σ, ShufflePlayW s σ s' ∧ ∃ τ, ShufflePlayW s' τ s

/-- Reflexivity: the empty shuffles on both sides. -/
theorem RevEqW_refl (s : State) : RevEqW s s :=
  ⟨[], ShufflePlayW.nil s, [], ShufflePlayW.nil s⟩

/-- Symmetry: the definition is symmetric in shape — the two
shuffles swap. -/
theorem RevEqW_symm {s s' : State} (h : RevEqW s s') : RevEqW s' s := by
  obtain ⟨σ, hσ, τ, hτ⟩ := h
  exact ⟨τ, hτ, σ, hσ⟩

/-- Transitivity: the shuffles concatenate per direction. -/
theorem RevEqW_trans {a b c : State} (h₁ : RevEqW a b) (h₂ : RevEqW b c) :
    RevEqW a c := by
  obtain ⟨σ, hσ, ρ, hρ⟩ := h₁
  obtain ⟨ν, hν, μ, hμ⟩ := h₂
  exact ⟨σ ++ ν, ShufflePlayW_append hσ hν, μ ++ ρ, ShufflePlayW_append hμ hρ⟩

/-- The twin relabeling preserves `RevEqW`: both shuffle plays twin
wholesale. -/
theorem RevEqW_twin_pair {s s' : State} (h : RevEqW s s') :
    RevEqW s.twinMap s'.twinMap := by
  obtain ⟨σ, hσ, τ, hτ⟩ := h
  exact ⟨σ.map Move.twinMove, ShufflePlayW_twin hσ,
    τ.map Move.twinMove, ShufflePlayW_twin hτ⟩

/-! ## The twin-extended setoid -/

/-- The same-orbit setoid: the join of the twin relabeling
(`Orig.twinSetoid`'s relation) with the witness reversible
quotient.  Two positions are related when equal, twin,
`RevEqW`-related, or `RevEqW`-related through a twin. -/
instance sameOrbitSetoid : Setoid State where
  r a b := a = b ∨ b = a.twinMap ∨ RevEqW b a ∨ RevEqW b.twinMap a
  iseqv := by
    constructor
    · intro a
      exact Or.inl rfl
    · rintro a b (h1 | h2 | h3 | h4)
      · exact Or.inl h1.symm
      · refine Or.inr (Or.inl ?_)
        have hb := congrArg State.twinMap h2
        rw [State.twinMap_twinMap a] at hb
        exact hb.symm
      · exact Or.inr (Or.inr (Or.inl (RevEqW_symm h3)))
      · refine Or.inr (Or.inr (Or.inr ?_))
        have h := RevEqW_twin_pair h4
        rw [State.twinMap_twinMap b] at h
        exact RevEqW_symm h
    · rintro a b c (h1 | h2 | h3 | h4) (k1 | k2 | k3 | k4)
      · exact Or.inl (h1.trans k1)
      · subst h1
        exact Or.inr (Or.inl k2)
      · subst h1
        exact Or.inr (Or.inr (Or.inl k3))
      · subst h1
        exact Or.inr (Or.inr (Or.inr k4))
      · subst k1
        exact Or.inr (Or.inl h2)
      · subst h2
        rw [State.twinMap_twinMap a] at k2
        exact Or.inl k2.symm
      · rw [h2] at k3
        refine Or.inr (Or.inr (Or.inr ?_))
        have h := RevEqW_twin_pair k3
        rw [State.twinMap_twinMap a] at h
        exact h
      · rw [h2] at k4
        refine Or.inr (Or.inr (Or.inl ?_))
        have h := RevEqW_twin_pair k4
        rw [State.twinMap_twinMap c, State.twinMap_twinMap a] at h
        exact h
      · subst k1
        exact Or.inr (Or.inr (Or.inl h3))
      · subst k2
        refine Or.inr (Or.inr (Or.inr ?_))
        rw [State.twinMap_twinMap b]
        exact h3
      · exact Or.inr (Or.inr (Or.inl (RevEqW_trans k3 h3)))
      · exact Or.inr (Or.inr (Or.inr (RevEqW_trans k4 h3)))
      · subst k1
        exact Or.inr (Or.inr (Or.inr h4))
      · subst k2
        exact Or.inr (Or.inr (Or.inl h4))
      · exact Or.inr (Or.inr (Or.inr (RevEqW_trans (RevEqW_twin_pair k3) h4)))
      · refine Or.inr (Or.inr (Or.inl ?_))
        have h5 : RevEqW c.twinMap a.twinMap :=
          RevEqW_trans k4 (by
            have h := RevEqW_twin_pair h4
            rw [State.twinMap_twinMap b] at h
            exact h)
        have h6 := RevEqW_twin_pair h5
        rw [State.twinMap_twinMap c, State.twinMap_twinMap a] at h6
        exact h6

/-- Positions modulo the same-orbit relation. -/
abbrev SameOrbit := Quotient sameOrbitSetoid

/-! ## The verdict descends to the reversible quotient -/

/-- The reversible quotient refines `sameFate`: the two witness
shuffles carry a winning play across in both directions. -/
theorem RevEqW_sameFate {s s' : State} (h : RevEqW s s') : sameFate s s' := by
  obtain ⟨σ, hσ, τ, hτ⟩ := h
  have h1 := ShufflePlayW_run hσ
  have h2 := ShufflePlayW_run hτ
  constructor
  · rintro ⟨play, w, hrun, hwin⟩
    exact ⟨τ ++ play, w, run_split τ s' s play w h2 hrun, hwin⟩
  · rintro ⟨play, w, hrun, hwin⟩
    exact ⟨σ ++ play, w, run_split σ s s' play w h1 hrun, hwin⟩

/-! ## The macro descent -/

/-- Negative-form shuffles concatenate, exactly as the witness
form does. -/
theorem ShufflePlay_append {a : State} : ∀ {l₁ : List Move} {b : State},
    ShufflePlay a l₁ b → ∀ {l₂ : List Move} {c : State},
    ShufflePlay b l₂ c → ShufflePlay a (l₁ ++ l₂) c := by
  intro l₁ b h
  induction h with
  | nil s =>
      intro l₂ c h₂
      exact h₂
  | cons hrev hstep hrest ih =>
      intro l₂ c h₂
      exact .cons hrev hstep (ih h₂)

/-- A macro step rebases along a witness shuffle: the window tip is
untouched, only the front accommodation grows. -/
theorem MacroStep_of_RevEqW {st₀ : State} : ∀ {σ₀ : List Move} {st : State},
    ShufflePlayW st₀ σ₀ st → ∀ {m : Move} {st'' : State},
    MacroStep st m st'' → MacroStep st₀ m st'' := by
  intro σ₀ st hσ₀ m st'' hms
  obtain ⟨st', σ, hsh, hstep, hirr⟩ := hms
  exact ⟨st', σ₀ ++ σ, ShufflePlay_append (ShufflePlayW_toNeg hσ₀) hsh,
    hstep, hirr⟩

/-- The macro descent: a winning phased play at `st` rebases along
any witness shuffle to `st`.  Each phase's window slides intact —
the inner phased play is reused as-is, so no rebase ever crosses a
commitment. -/
theorem MacroWin_of_RevEqW {st₀ : State} : ∀ {st w : State},
    MacroWin st w → ∀ {σ₀ : List Move},
    ShufflePlayW st₀ σ₀ st → MacroWin st₀ w := by
  intro st w hwin
  induction hwin with
  | @finish st1 st' sig hs hw =>
      intro σ₀ hσ₀
      exact .finish (ShufflePlay_append (ShufflePlayW_toNeg hσ₀) hs) hw
  | @phase st1 st'' wm mv hms hinner _ih =>
      intro σ₀ hσ₀
      exact .phase (MacroStep_of_RevEqW hσ₀ hms) hinner

/-! ## The negative form under the twin relabeling -/

/-- The twin move relabeling is an involution. -/
theorem Move.twinMove_twinMove (m : Move) : m.twinMove.twinMove = m := by
  cases m with
  | draw => rfl
  | wasteToFound c => simp [Move.twinMove, Card.twin_twin]
  | wasteToTab c b =>
      cases b <;> simp [Move.twinMove, Card.twin_twin, Base.twinMap]
  | tabToFound c => simp [Move.twinMove, Card.twin_twin]
  | foundToTab c b =>
      cases b <;> simp [Move.twinMove, Card.twin_twin, Base.twinMap]
  | tabToTab c b =>
      cases b <;> simp [Move.twinMove, Card.twin_twin, Base.twinMap]

/-- The negative reversible fact twins, by contraposition: a
commitment at the twin would undo itself into a commitment at the
base. -/
theorem reversibleAt_twin {st : State} {m : Move} (h : reversibleAt st m) :
    reversibleAt st.twinMap m.twinMove := by
  intro contra
  refine h (fun s₁ play hstep hrun => ?_)
  exact absurd (twin_run s₁ play st hrun)
    (contra s₁.twinMap (play.map Move.twinMove)
      (by rw [← State.twin_step st m, hstep]; rfl))

/-- A negative-form shuffle twins wholesale: every guard by
`reversibleAt_twin`, every step by `State.twin_step`. -/
theorem ShufflePlay_twin {st : State} : ∀ {play : List Move} {st' : State},
    ShufflePlay st play st' →
    ShufflePlay st.twinMap (play.map Move.twinMove) st'.twinMap := by
  intro play st' h
  induction h with
  | nil s => exact .nil _
  | @cons st m s₁ rest st' hrev hstep hrest ih =>
      have hstept : State.step st.twinMap m.twinMove = some s₁.twinMap := by
        rw [← State.twin_step st m, hstep]
        rfl
      exact .cons (reversibleAt_twin hrev) hstept ih

/-- Irreversibility twins: a hypothetical return at the twin
untwins — through `State.twin_step` and `twin_run` — into a
return at the base, contradicting the base commitment. -/
theorem irreversibleAt_twin {st : State} {m : Move} (h : irreversibleAt st m) :
    irreversibleAt st.twinMap m.twinMove := by
  intro s₁' play' hstep2 hrun2
  have hstepbase : State.step st m = some s₁'.twinMap := by
    have h2 := State.twin_step st.twinMap m.twinMove
    rw [State.twinMap_twinMap st, Move.twinMove_twinMove m] at h2
    rw [hstep2] at h2
    exact h2.symm
  apply h s₁'.twinMap (play'.map Move.twinMove) hstepbase
  have h3 := twin_run s₁' play' st.twinMap hrun2
  rwa [State.twinMap_twinMap st] at h3

/-- A commitment twins: the window's shuffle, step, and
irreversibility all conjugate. -/
theorem MacroStep_twin {st : State} {m : Move} {st'' : State}
    (h : MacroStep st m st'') :
    MacroStep st.twinMap m.twinMove st''.twinMap := by
  obtain ⟨st', σ, hsh, hstep, hirr⟩ := h
  refine ⟨st'.twinMap, σ.map Move.twinMove, ShufflePlay_twin hsh, ?_,
    irreversibleAt_twin hirr⟩
  rw [← State.twin_step st' m, hstep]
  rfl

/-- The phased verdict twins wholesale: the finish and every phase
conjugate, so the macro game cannot tell twins apart. -/
theorem MacroWin_twin {st w : State} (h : MacroWin st w) :
    MacroWin st.twinMap w.twinMap := by
  induction h with
  | @finish st1 st' sig hs hw =>
      refine .finish (ShufflePlay_twin hs) ?_
      rw [State.isWin_twinMap]
      exact hw
  | @phase st1 st'' wm mv hms hinner ih =>
      exact .phase (MacroStep_twin hms) ih

/-! ## Descent onto the orbit -/

/-- The orbit relation refines `sameFate`: every identification the
setoid makes preserves the verdict. -/
theorem sameFate_orbit {a b : State} (h : sameOrbitSetoid.r a b) :
    sameFate a b := by
  rcases h with rfl | h2 | h3 | h4
  · exact Iff.rfl
  · subst h2
    exact twin_fate a
  · exact (RevEqW_sameFate h3).symm
  · exact (RevEqW_sameFate h4).symm.trans (twin_fate b).symm

/-- The macro verdict descends onto the orbit: a phased win exists
at one member of the orbit iff it exists at the other. -/
theorem MacroWin_sameFate_descend {a b : State} (h : sameOrbitSetoid.r a b) :
    (∃ w, MacroWin a w) ↔ (∃ w, MacroWin b w) := by
  rcases h with rfl | h2 | h3 | h4
  · exact Iff.rfl
  · subst h2
    constructor
    · rintro ⟨w, hw⟩
      exact ⟨w.twinMap, MacroWin_twin hw⟩
    · rintro ⟨w, hw⟩
      have h' := MacroWin_twin hw
      rw [State.twinMap_twinMap a] at h'
      exact ⟨_, h'⟩
  · constructor
    · rintro ⟨w, hw⟩
      obtain ⟨σ, hσ, ν, hν⟩ := h3
      exact ⟨w, MacroWin_of_RevEqW hw hσ⟩
    · rintro ⟨w, hw⟩
      obtain ⟨σ, hσ, ν, hν⟩ := h3
      exact ⟨w, MacroWin_of_RevEqW hw hν⟩
  · constructor
    · rintro ⟨w, hw⟩
      obtain ⟨σ, hσ, ν, hν⟩ := h4
      have h' := MacroWin_twin (MacroWin_of_RevEqW hw hσ)
      rw [State.twinMap_twinMap b] at h'
      exact ⟨_, h'⟩
    · rintro ⟨w, hw⟩
      obtain ⟨σ, hσ, ν, hν⟩ := h4
      exact ⟨_, MacroWin_of_RevEqW (MacroWin_twin hw) hν⟩

/-! ## The quotient lifts -/

/-- Winnability on the orbit classes: the play verdict descends to
the quotient. -/
def WinFromQ₂ (q : SameOrbit) : Prop :=
  Quotient.lift WinFrom (fun _ _ h => propext (sameFate_orbit h)) q

/-- The macro verdict on the orbit classes: a phased win exists at
one member iff at any other. -/
def MacroWinQ₂ (q : SameOrbit) : Prop :=
  Quotient.lift (fun st => ∃ w, MacroWin st w)
    (fun _ _ h => propext (MacroWin_sameFate_descend h)) q

/-- On classes, the macro verdict and the play verdict coincide —
`win_iff_macro` descends to the quotient.  (The classical step is
inherited from `win_iff_macro`'s single `by_cases` on
`irreversibleAt`; nothing in this file adds one.) -/
theorem macro_on_classes : ∀ q : SameOrbit, MacroWinQ₂ q ↔ WinFromQ₂ q := by
  intro q
  refine Quotient.inductionOn q (fun a => ?_)
  show (∃ w, MacroWin a w) ↔ WinFrom a
  exact (win_iff_macro a).symm
