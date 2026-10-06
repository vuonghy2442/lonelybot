import Orig.Fate

/-!
# Orig — the macro game

The commitment game, stated on the original game with no syntactic
move-set split:

* `ShufflePlay` — a play whose every move is `reversibleAt` where it
  is played (an accommodation);
* `MacroStep` — reach an accommodation, then fire an
  `irreversibleAt` move (a commitment, in the semantic reading);
* `MacroWin` — a winning *phased* play: zero or more commitment
  phases, ending in a shuffle onto a won position.

The regrouping theorem (`twin-free counterpart of the macro
correspondence, proven here for the original game):

* `win_iff_macro` — `WinFrom st ↔ ∃ w, MacroWin st w`: every
  winning play factors as shuffle / commit / shuffle / commit / … /
  shuffle.  The factorization is by the *first* semantic commitment
  of the remaining play, so nothing about *which* moves are
  irreversible is assumed anywhere — the classification theorems of
  later chapters only refine this.

The futures count ("a commitment leaves at most two
`sameFate`-distinct successors, per accommodation window") is
stated and attacked in later chapters, on top of these
definitions.
-/

/-! ## Shuffles -/

/-- A shuffle: a legal play in which every move is reversible at the
state it is played from. -/
inductive ShufflePlay : State → List Move → State → Prop
  | nil (st : State) : ShufflePlay st [] st
  | cons {st : State} {m : Move} {s₁ : State} {rest : List Move} {st' : State}
      (hrev : reversibleAt st m) (hstep : State.step st m = some s₁)
      (hrest : ShufflePlay s₁ rest st') :
      ShufflePlay st (m :: rest) st'

/-- A shuffle is, in particular, a legal play. -/
theorem ShufflePlay_run {st : State} : ∀ {play : List Move} {st' : State},
    ShufflePlay st play st' → st.run play = some st' := by
  intro play st' h
  induction h with
  | nil s => rfl
  | cons hrev hstep hrest ih =>
      simp only [State.run, hstep]
      exact ih

/-- Appending a reversible move to the end of a shuffle is a
shuffle. -/
theorem ShufflePlay_snoc {origin : State} : ∀ {pre : List Move} {cur : State},
    ShufflePlay origin pre cur → ∀ {m : Move} {s₁ : State},
    reversibleAt cur m → State.step cur m = some s₁ →
    ShufflePlay origin (pre ++ [m]) s₁ := by
  intro pre cur h
  induction h with
  | nil s =>
      intro m s₁ hrev hstep
      exact .cons hrev hstep (.nil s₁)
  | cons hrev hstep hrest ih =>
      intro m s₁ hrev' hstep'
      exact .cons hrev hstep (ih hrev' hstep')

/-! ## The phased game -/

/-- One commitment: some accommodation, then an irreversible move. -/
def MacroStep (st : State) (m : Move) (st'' : State) : Prop :=
  ∃ st' σ, ShufflePlay st σ st' ∧ State.step st' m = some st'' ∧ irreversibleAt st' m

/-- A winning phased play: engagements separated by commitments,
with a (possibly empty) trailing shuffle landing on the win. -/
inductive MacroWin : State → State → Prop
  | finish {st st' : State} {σ : List Move} :
      ShufflePlay st σ st' → st'.isWin = true → MacroWin st st'
  | phase {st st'' w : State} {m : Move} :
      MacroStep st m st'' → MacroWin st'' w → MacroWin st w

/-- Joining two plays along a shared state. -/
theorem run_split : ∀ (l₁ : List Move) (st s₁ : State) (l₂ : List Move) (w : State),
    st.run l₁ = some s₁ → s₁.run l₂ = some w → st.run (l₁ ++ l₂) = some w := by
  intro l₁
  induction l₁ with
  | nil =>
      intro st s₁ l₂ w h₁ h₂
      injection h₁ with h
      subst h
      exact h₂
  | cons m t ih =>
      intro st s₁ l₂ w h₁ h₂
      obtain ⟨r, hstep, hrest⟩ := State.run_cons h₁
      show st.run (m :: (t ++ l₂)) = some w
      rw [show st.run (m :: (t ++ l₂)) = (match State.step st m with
        | some st' => st'.run (t ++ l₂)
        | none => none) from rfl, hstep]
      exact ih r s₁ l₂ w hrest h₂

/-! ## The regrouping theorem -/

/-- The forward direction of the macro correspondence, by induction
on the outstanding play: the first move that is a semantic
commitment at its own state opens a phase; reversible moves
accumulate into the accommodation. -/
theorem win_macro_aux : ∀ (play : List Move) (origin cur : State) (pre : List Move)
    (w : State),
    ShufflePlay origin pre cur → cur.run play = some w → w.isWin = true →
    ∃ w', MacroWin origin w' := by
  intro play
  induction play with
  | nil =>
      intro origin cur pre w hs hrun hwin
      injection hrun with h'
      subst h'
      exact ⟨_, MacroWin.finish hs hwin⟩
  | cons m rest ih =>
      intro origin cur pre w hs hrun hwin
      obtain ⟨s₁, hstep, hrest⟩ := State.run_cons hrun
      by_cases hirr : irreversibleAt cur m
      · obtain ⟨w', hw'⟩ := ih s₁ s₁ [] w (ShufflePlay.nil s₁) hrest hwin
        exact ⟨w', MacroWin.phase ⟨cur, pre, hs, hstep, hirr⟩ hw'⟩
      · exact ih origin s₁ (pre ++ [m]) w (ShufflePlay_snoc hs hirr hstep) hrest hwin

/-- The backward direction: a phased play assembles into a legal
one. -/
theorem macro_win (st : State) (w : State) (h : MacroWin st w) : WinFrom st := by
  induction h with
  | @finish st0 st1 sig hs hwin =>
      exact ⟨sig, st1, ShufflePlay_run hs, hwin⟩
  | @phase st0 st2 wm mv hms _hinner ih =>
      obtain ⟨st', hrest⟩ := hms
      obtain ⟨sig, hrest2⟩ := hrest
      have hsh := hrest2.1
      have hstep := hrest2.2.1
      refine ih.elim fun playt ih1 => ih1.elim fun wt ih2 => ?_
      obtain ⟨hrt, hwint⟩ := ih2
      refine ⟨sig ++ mv :: playt, wt, ?_, hwint⟩
      refine run_split sig st0 st' (mv :: playt) wt (ShufflePlay_run hsh) ?_
      show st'.run (mv :: playt) = some wt
      rw [show st'.run (mv :: playt) = (match State.step st' mv with
        | some s'' => s''.run playt
        | none => none) from rfl]
      rw [hstep]
      exact hrt

/-- The macro correspondence on the original game: winning exists
iff a winning phased play exists.  No move-set restriction, no
commitment vocabulary — `irreversibleAt` does all the work. -/
theorem win_iff_macro (st : State) : WinFrom st ↔ ∃ w, MacroWin st w := by
  constructor
  · rintro ⟨play, w, hrun, hwin⟩
    exact win_macro_aux play st st [] w (.nil st) hrun hwin
  · rintro ⟨w, hw⟩
    exact macro_win st w hw
