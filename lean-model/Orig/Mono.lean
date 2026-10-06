import Orig.Fate

/-!
# Orig — the monotone bridge to irreversibility

The ticket this chapter pays off: *immediately irreversible ⇒
fully irreversible*.  `irreversibleAt st m` is an arbitrary-play
fact — no continued play from the commit successor returns — while
every concrete argument a later chapter can make in one line is a
*one-step* fact about some natural-number measure `Q`
(`State → Nat`) on positions.  This file is the converter family:

* `mono_run` / `mono_run_asc` — a play whose every step descends
  (resp. ascends) in `Q` ends no higher (resp. no lower) than it
  started, by induction on the play with `State.step`'s
  determinism doing nothing: only the walk matters;
* `irr_of_desc` / `irr_of_asc` — a *strict* one-step move in `Q`,
  down or up, is a full commitment: any would-be return play from
  the successor would force the impossible `Q st < Q s₁ ≤ … ≤ Q st`
  (or its dual).  The bridge uses that `State.step` is a function:
  the successor the arbitrary-play side names *is* the successor
  the one-step side measured, by `Option.some.injEq`;
* the *fragment* variants — plays restricted to a permitted-move
  predicate `P` (`runIn`, `irreversibleAtIn`, and the same two
  bridge instances `irr_of_descIn` / `irr_of_ascIn`) for the later
  no-worry-back regime, where only the licensed move fragment is
  available to "undo with"; `runIn_true` ties the fragment to the
  unrestricted `State.run` — the always-true fragment is the old
  game.

Later chapters supply the measures (foundation progress,
stock/reveal accounting, …) and read their commitments off these
bridges; nothing here knows a single Klondike rule.
-/

/-- A play whose every legal step descends in `Q` (`Q s' ≤ Q s`)
ends at a position no higher than its start.  The one-step measure
hypothesis is stated for *all* moves, so the walk chain composes
by induction on the play, generalizing the position. -/
theorem mono_run (Q : State → Nat)
    (h : ∀ s m s', State.step s m = some s' → Q s' ≤ Q s) :
    ∀ {s play w}, s.run play = some w → Q w ≤ Q s := by
  intro s play
  induction play generalizing s with
  | nil =>
      intro w hw
      have hw' : some s = some w := hw
      injection hw' with he
      subst he
      exact Nat.le_refl _
  | cons m rest ih =>
      intro w hw
      obtain ⟨s₁, hstep, hrun⟩ := State.run_cons hw
      have h1 : Q s₁ ≤ Q s := h s m s₁ hstep
      have h2 : Q w ≤ Q s₁ := ih hrun
      omega

/-- The dual walk: every legal step ascends in `Q` (`Q s ≤ Q s'`),
so the play's end is no lower than its start. -/
theorem mono_run_asc (Q : State → Nat)
    (h : ∀ s m s', State.step s m = some s' → Q s ≤ Q s') :
    ∀ {s play w}, s.run play = some w → Q s ≤ Q w := by
  intro s play
  induction play generalizing s with
  | nil =>
      intro w hw
      have hw' : some s = some w := hw
      injection hw' with he
      subst he
      exact Nat.le_refl _
  | cons m rest ih =>
      intro w hw
      obtain ⟨s₁, hstep, hrun⟩ := State.run_cons hw
      have h1 : Q s ≤ Q s₁ := h s m s₁ hstep
      have h2 : Q s₁ ≤ Q w := ih hrun
      omega

/-- A strictly descending one-step move is a full commitment: no
play from the successor can return, because the return would walk
`Q` back up from below `Q st` to `Q st` while every step only
descends. -/
theorem irr_of_desc (Q : State → Nat)
    (h : ∀ s m s', State.step s m = some s' → Q s' ≤ Q s)
    {st : State} {m : Move} {s₁ : State}
    (hstep : State.step st m = some s₁) (hdrop : Q s₁ < Q st) :
    irreversibleAt st m := by
  intro s₁' play hstep' hrun
  rw [hstep] at hstep'
  injection hstep' with heq
  subst heq
  have hle : Q st ≤ Q s₁ := mono_run Q h hrun
  omega

/-- The dual commitment: a strictly ascending one-step move in `Q`
cannot be undone by any play, since the attempted return would
climb back down from above. -/
theorem irr_of_asc (Q : State → Nat)
    (h : ∀ s m s', State.step s m = some s' → Q s ≤ Q s')
    {st : State} {m : Move} {s₁ : State}
    (hstep : State.step st m = some s₁) (hrise : Q st < Q s₁) :
    irreversibleAt st m := by
  intro s₁' play hstep' hrun
  rw [hstep] at hstep'
  injection hstep' with heq
  subst heq
  have hle : Q s₁ ≤ Q st := mono_run_asc Q h hrun
  omega

/-- Plays restricted to a permitted-move fragment `P`: an
unpermitted move or a failed step aborts the play (`none`).  This
is the walking function every later restricted regime instantiates
with its own `P`. -/
def runIn (P : Move → Prop) [DecidablePred P] (st : State) : List Move → Option State
  | [] => some st
  | m :: ms =>
      if P m then
        (match State.step st m with
          | some st' => runIn P st' ms
          | none => none)
      else none

/-- A move is a commitment *inside the fragment `P`*: no
`P`-restricted play from the commit successor returns. -/
def irreversibleAtIn (P : Move → Prop) [DecidablePred P] (st : State) (m : Move) : Prop :=
  ∀ s₁ play, State.step st m = some s₁ → runIn P s₁ play ≠ some st

/-- Decomposition of a `runIn` step for proofs: a successful head
of the play is a permitted legal move whose continuation
succeeds.  The fragment analog of `State.run_cons`. -/
theorem runIn_cons {P : Move → Prop} [DecidablePred P] {st : State} {m : Move}
    {rest : List Move} {w : State} (h : runIn P st (m :: rest) = some w) :
    ∃ s₁, P m ∧ State.step st m = some s₁ ∧ runIn P s₁ rest = some w := by
  rw [runIn] at h
  split at h
  · next hm =>
      split at h
      · next s₁ hstep => exact ⟨s₁, hm, hstep, h⟩
      · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- The fragment walk descends in `Q` too: only the permitted
moves are ever taken, so a descent hypothesis restricted to `P`
already chains along a `runIn` play. -/
theorem mono_runIn (P : Move → Prop) [DecidablePred P] (Q : State → Nat)
    (h : ∀ s m s', P m → State.step s m = some s' → Q s' ≤ Q s) :
    ∀ {s play w}, runIn P s play = some w → Q w ≤ Q s := by
  intro s play
  induction play generalizing s with
  | nil =>
      intro w hw
      have hw' : some s = some w := hw
      injection hw' with he
      subst he
      exact Nat.le_refl _
  | cons m rest ih =>
      intro w hw
      obtain ⟨s₁, hm, hstep, hrun⟩ := runIn_cons hw
      have h1 : Q s₁ ≤ Q s := h s m s₁ hm hstep
      have h2 : Q w ≤ Q s₁ := ih hrun
      omega

/-- The fragment dual: an ascending-in-`Q` permitted-move set
keeps a `runIn` play no lower than its start. -/
theorem mono_runIn_asc (P : Move → Prop) [DecidablePred P] (Q : State → Nat)
    (h : ∀ s m s', P m → State.step s m = some s' → Q s ≤ Q s') :
    ∀ {s play w}, runIn P s play = some w → Q s ≤ Q w := by
  intro s play
  induction play generalizing s with
  | nil =>
      intro w hw
      have hw' : some s = some w := hw
      injection hw' with he
      subst he
      exact Nat.le_refl _
  | cons m rest ih =>
      intro w hw
      obtain ⟨s₁, hm, hstep, hrun⟩ := runIn_cons hw
      have h1 : Q s ≤ Q s₁ := h s m s₁ hm hstep
      have h2 : Q s₁ ≤ Q w := ih hrun
      omega

/-- The fragment instance of `irr_of_desc`: a strictly `Q`-dropping
move stays irreversible for the `P`-restricted player as well —
there is even less to undo with. -/
theorem irr_of_descIn (P : Move → Prop) [DecidablePred P] (Q : State → Nat)
    (h : ∀ s m s', P m → State.step s m = some s' → Q s' ≤ Q s)
    {st : State} {m : Move} {s₁ : State}
    (hstep : State.step st m = some s₁) (hdrop : Q s₁ < Q st) :
    irreversibleAtIn P st m := by
  intro s₁' play hstep' hrun
  rw [hstep] at hstep'
  injection hstep' with heq
  subst heq
  have hle : Q st ≤ Q s₁ := mono_runIn P Q h hrun
  omega

/-- The fragment instance of `irr_of_asc`. -/
theorem irr_of_ascIn (P : Move → Prop) [DecidablePred P] (Q : State → Nat)
    (h : ∀ s m s', P m → State.step s m = some s' → Q s ≤ Q s')
    {st : State} {m : Move} {s₁ : State}
    (hstep : State.step st m = some s₁) (hrise : Q st < Q s₁) :
    irreversibleAtIn P st m := by
  intro s₁' play hstep' hrun
  rw [hstep] at hstep'
  injection hstep' with heq
  subst heq
  have hle : Q s₁ ≤ Q st := mono_runIn_asc P Q h hrun
  omega

/-- The always-true fragment is the unrestricted game: permitting
every move changes nothing, the `if` guard passing through each
position of the walk.  This ties the fragment machinery to
`State.run` and back. -/
theorem runIn_true (st : State) (play : List Move) :
    runIn (fun _ => True) st play = st.run play := by
  induction play generalizing st with
  | nil => rfl
  | cons m rest ih =>
      rw [runIn, ite_eq_left True.intro]
      cases hstep : State.step st m with
      | none =>
          rw [show st.run (m :: rest) = none from by rw [State.run, hstep]]
      | some s₁ =>
          rw [show st.run (m :: rest) = s₁.run rest from by rw [State.run, hstep]]
          exact ih s₁
