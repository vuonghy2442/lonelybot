import Klondike.Dominance

/-!
# The macro (commitment) game — C1 and C2

macro_formalization.md §0, model side.  A play regroups as
"shuffle, commit, shuffle, commit, …" (their Lemma A3): a
*commitment* is the first irreversible move after a reversible
accommodation, and the macro game's moves are just the two
commitment kinds — `Draw(c)` (the guarded jump to `c`, then play it:
tableau or stack outcome) and `Reveal(c)`.  The machinery this needs
is already in the kernel: `accommodates` (Lemma A's shuffle
reachability), `State.applyDrawTo` / `State.applyDrawStackTo` (the
Draw commitment's two outcomes — the accessible-set-guarded jumps,
whose soundness is `applyDrawTo_eq_dealPlay`: jump-then-play ≡
deal-until-then-play).
-/

/-- A macro move: one commitment. -/
inductive MacroMove : Type where
  /-- The `Draw(c)` commitment: deal until `c` is the waste top (the
  guarded jump), then play it — tableau landing (some base) or stack
  landing. -/
  | drawCommit (c : Card)
  /-- The `Reveal(c)` commitment: flip the hidden card under `c`. -/
  | revealCommit (c : Card)
  deriving DecidableEq

/-- The commitment application from a (already accommodated) state. -/
def commitApplies (st : State) (k : MacroMove) (st'' : State) : Prop :=
  match k with
  | .drawCommit c =>
      ∃ b : Base, st.applyDrawTo c b = some st'' ∨ st.applyDrawStackTo c = some st''
  | .revealCommit c => st.apply (Move.reveal c) = some st''

/-- One macro step: an accommodation, then the commitment. -/
def macroStep (st : State) (k : MacroMove) (st'' : State) : Prop :=
  ∃ st', accommodates st st' ∧ commitApplies st' k st''

/-- Chaining macro steps. -/
def macroSteps : State → List MacroMove → State → Prop
  | st, [], st' => st = st'
  | st, k :: ks, st' => ∃ st'', macroStep st k st'' ∧ macroSteps st'' ks st'

/-- Macro solvability: a winning commitment sequence exists (the
shuffles are existentially witnessed by `macroStep`). -/
def State.macroSolvable (st : State) : Prop :=
  ∃ ks w, macroSteps st ks w ∧ w.isWin = true

/-- A macro step is an engine play: the accommodation is
stack↔pile shuffling, the Draw commitment is rotations plus the deck
move, all within the engine's move set.  TODO. -/
theorem macroStep_engine_play {st : State} {k : MacroMove} {st'' : State}
    (h : macroStep st k st'') :
    ∃ play, st.run play = some st'' ∧ ∀ m ∈ play, m.isEngine = true := sorry

/-- **C1 (the macro reduction)**: on well-formed states, the engine's
restricted game and the macro commitment game have the same
solvability.  ← is `macroStep_engine_play` + induction.  → is their
Lemma A3's regrouping: draws commute with accommodations (component
disjointness — `commute_of_compsDisjoint`), so they can be pushed
into the commitment's rotation; trailing draws drop (`isWin` reads
only heights, which draws never touch).  TODO. -/
theorem solvableEngine_iff_macro {st : State} (hwf : st.WF) :
    st.solvableEngine ↔ st.macroSolvable := sorry

/-- **C2, model seed**: the tableau-landing outcomes of a Draw
commitment (from one fixed state) agree on everything but the board —
deal, heights, depths, stock, draw step, and the visible set.  The
full C2 — at most two *reversible-closure classes* per commitment —
is the engine-side form, stated at the bridge (the destination
collapse / macro_parking.md P.6 is the search policy that exploits
it; corpus-gated there, not proven).  TODO: from `applyDrawTo`'s
definition + the `attach` consumption lemmas. -/
theorem drawTo_tableau_outcomes_agree {st : State} {c : Card} {b b' : Base}
    {st₁ st₂ : State}
    (h₁ : st.applyDrawTo c b = some st₁) (h₂ : st.applyDrawTo c b' = some st₂) :
    st₁.deal = st₂.deal ∧ st₁.heights = st₂.heights ∧ st₁.depths = st₂.depths ∧
      st₁.stock = st₂.stock ∧ st₁.drawStep = st₂.drawStep ∧
      ∀ c'', st₁.isVis c'' = st₂.isVis c'' := sorry

/-! Deferred macro statements, recorded:

- **C12 (forced-commitment dominance)** — the locked
  dominantly-stackable surface's Reveal-stack line as sole successor.
  Needs macro_formalization §6.5b's exact statement to formalize
  without guessing; the model-side ingredients (`isLocked`,
  `safeToStack`) already exist.
- **C13 (sleep-set POR)** — the pilot is staged
  (`drawTo_comm_modAdjacent`, `drawTo_nonadjacent_diverge`); the
  full sleep-set layer needs the fold/search formulation first.
- **The parking lemma / destination collapse** (macro_parking.md) —
  a search policy, corpus-gated in the engine; formalizing its
  soundness is B4-adjacent (the reshape argument).
-/
