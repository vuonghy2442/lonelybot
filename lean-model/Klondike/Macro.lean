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

/-! ## The pace dominance — the offset-dominance registry's soundness

The search-side exploit of Pace's pace order: the engine's
refuted-offset registry (rules R1/R2, measured at 43.8% of seed-32
draw-3 states; the Rust falsifier `pace_dominance_order` and the
property test `pace_dominance_order` in src/macro_game.rs).  The state
space factors as *board × pace*: reveal commitments are pace-inert
(they never touch the stock), draws reset the pace to the drawn
card's position — a function of the cards alone. -/

/-- **Pace dominance (the simulation)**: states identical but for the
stock cursor, where the first's accessible set contains the second's —
every macro win from the second lifts to the first.  The replay:
reveal commitments are cursor-inert and legal in both (identical
boards); the line's first Draw commitment is replayable
(`reachablePos`'s guard holds by the superset), and both jumps land on
the *identical* successor stock (`drawCard_cursor_indep`), after
which the plays coincide.

TODO(proof) [H]: induction on the winning commitment list; invariant:
the states are equal (after the first draw) or differ only in the
cursor with the maskPos superset — reveals preserve it (the stock's
cards are untouched, so `hK` persists; `apply`'s reveal arm never
consults the stock), the draw case merges via `drawCard_cursor_indep`
(the commitment's board/heights effect is cursor-blind).  The
accommodation witnesses replay verbatim: `accommodates` shuffles
stock-cards only, never the cursor.  `hstep` from `hwf.step_pos`,
`hcur` from `hwf.cursor_le`. -/
theorem pace_dominance {st : State} {o' : Nat} (hwf : st.WF)
    (hcur' : o' ≤ st.stock.cards.length)
    (hK : ∀ p, p ∈ Pace.maskPos { cards := st.stock.cards, cursor := o' }
        st.drawStep hwf.step_pos →
      p ∈ Pace.maskPos st.stock st.drawStep hwf.step_pos)
    (hsol : { st with stock := { st.stock with cursor := o' } }.macroSolvable) :
    st.macroSolvable := sorry

/-- **R1 (registry rule 1)**: within an impure residue class the
earlier cursor dominates — a win from the later pace lifts to the
earlier.  This is the soundness of skipping the larger-offset state
when the minimal same-residue state was refuted.

TODO(proof) [M]: `pace_dominance` at the `o`-variant (reconstruct its
WF from `hwf` minus/plus the cursor conjuncts) with
`maskPos_residue_mono` as `hK`. -/
theorem pace_dominance_residue {st : State} {o o' : Nat} (hwf : st.WF)
    (hle : o ≤ o')
    (hres : o % st.drawStep = o' % st.drawStep)
    (himp : o' % st.drawStep ≠ 0)
    (hcur : o ≤ st.stock.cards.length) (hcur' : o' ≤ st.stock.cards.length)
    (hsol : { st with stock := { st.stock with cursor := o' } }.macroSolvable) :
    { st with stock := { st.stock with cursor := o } }.macroSolvable := sorry

/-- **R2 (registry rule 2)**: the pass-boundary (pure) cursor is
dominated by any impure cursor on the same cards — a win from the
pass-end state lifts to the mid-pass one.  This is the soundness of
skipping the pure state when a same-cards impure state was refuted
(the measured bigger half of the prize: 912k of the 1.38M doomed
seed-32 draw-3 states).

TODO(proof) [M]: `pace_dominance` at the `o`-variant with
`maskPos_impure_sup_pure` as `hK`. -/
theorem pace_dominance_impure_pure {st : State} {o o' : Nat} (hwf : st.WF)
    (himp : o % st.drawStep ≠ 0)
    (hpure' : o' % st.drawStep = 0 ∨ o' = st.stock.cards.length)
    (hcur : o ≤ st.stock.cards.length) (hcur' : o' ≤ st.stock.cards.length)
    (hsol : { st with stock := { st.stock with cursor := o' } }.macroSolvable) :
    { st with stock := { st.stock with cursor := o } }.macroSolvable := sorry

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
