import Klondike.Dominance
import Klondike.Progress

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

/-! ### The reachability route (the physical game)

In the *physical* game the cursor advances without consuming — one
`.draw` is `dealOnce` — so the better state **reaches** the worse one
and the dominance is a `solvable_of_reaches` instance: no simulation,
one-line compositions.  The macro game (above) has no deal move — its
jumps consume — so same-mask different-cursor states are mutually
unreachable there, and that residue is the simulation's own content. -/

/-- The deal chain: `k` pure deals advance the cursor from `o` to `o'`
whenever `o ≤ o'` with the same residue (`o' − o` a multiple of the
step).  The chain never clamps: every intermediate cursor is `≤ o' ≤
length`.

TODO(proof) [E]: the play is `k` `.draw` moves with `o + k·s = o'`;
induction on `k` — each `dealOnce` from `c < n` gives
`min (c + s) n = c + s` (no clamp, the chain stays ≤ o'). -/
theorem deal_chain_reaches {st : State} {o o' : Nat}
    (hle : o ≤ o') (hres : o % st.drawStep = o' % st.drawStep)
    (hcur' : o' ≤ st.stock.cards.length) :
    ∃ play, ({ st with stock := { st.stock with cursor := o } }).run play
      = some { st with stock := { st.stock with cursor := o' } } := sorry

/-- The pass-end reachability: every cursor reaches the pass end — the
final deal clamps at `length` from *anywhere*, so the residue condition
drops.  This is why the pass-end state is the worst same-cards state.

TODO(proof) [E]: deals step by `s` until `c + s ≥ n`, then `min`
clamps; induction on the remaining distance (the wrap is never taken —
the chain stops at `n`). -/
theorem deal_passEnd_reaches {st : State} {o : Nat}
    (hcur : o ≤ st.stock.cards.length) :
    ∃ play, ({ st with stock := { st.stock with cursor := o } }).run play
      = some { st with stock := { st.stock with cursor := st.stock.cards.length } } := sorry

/-- **R1, physical-game route**: same residue, earlier cursor —
dominance by reachability (the deal chain), not simulation.

TODO(proof) [E]: `solvable_of_reaches` + `deal_chain_reaches`. -/
theorem pace_dominance_phys_residue {st : State} {o o' : Nat}
    (hle : o ≤ o') (hres : o % st.drawStep = o' % st.drawStep)
    (hcur : o ≤ st.stock.cards.length) (hcur' : o' ≤ st.stock.cards.length)
    (hsol : { st with stock := { st.stock with cursor := o' } }.solvableFrom) :
    { st with stock := { st.stock with cursor := o } }.solvableFrom := sorry

/-- **R2a, physical-game route**: the pass-end cursor is dominated by
every same-cards state — the clamp reaches it from anywhere, so no
residue condition.  (The macro-game `pace_dominance_impure_pure`
additionally covers mid-pass pure cursors via the accessible-superset
— those are *not* reachable from impure ones, which is the
simulation's own content.)

TODO(proof) [E]: `solvable_of_reaches` + `deal_passEnd_reaches`. -/
theorem pace_dominance_phys_passEnd {st : State} {o : Nat}
    (hcur : o ≤ st.stock.cards.length)
    (hsol : ({ st with stock :=
        { st.stock with cursor := st.stock.cards.length } }).solvableFrom) :
    { st with stock := { st.stock with cursor := o } }.solvableFrom := sorry

/-- The pure-orbit cycle: all pure cursors are mutually reachable by
pure deals — each reaches the pass end (`deal_passEnd_reaches`), the
wrap deal lands 0, and the fresh-pass chain reaches any pure cursor
(`deal_chain_reaches`) — so their solvability is *equivalent*.  This is
the game-level derivation of the engine's `is_pure`/`normalized_offset`
encode merge (the offset normalization draw-3 gets on the pure class);
`maskPos_pure_indep` is its accessibility-level shadow.

TODO(proof) [E]: `solvable_iff_mutuallyReaches` + the two deal chains
composing through the pass end and the wrap (the wrap is one `.draw`
from the saturated cursor). -/
theorem solvable_iff_pure_cursors {st : State} {o o' : Nat}
    (hp : o % st.drawStep = 0 ∨ o = st.stock.cards.length)
    (hp' : o' % st.drawStep = 0 ∨ o' = st.stock.cards.length)
    (hcur : o ≤ st.stock.cards.length) (hcur' : o' ≤ st.stock.cards.length) :
    ({ st with stock := { st.stock with cursor := o } }).solvableFrom ↔
    ({ st with stock := { st.stock with cursor := o' } }).solvableFrom := sorry

/-! ### The window obligation — the gap structure of the pace dominance

When the better state wins and the worse is refuted, the witness of
the difference is a *window card*: a draw the worse cursor cannot
make.  The replay mechanism is the deal commutation
(`deal_commutes_nonStock`): deals float through the non-consuming
prefix, so the cursor at the first consumption is well-defined, and
the worse state replays the line by trimming the deal count. -/

/-- **The hurry lemma (physical game)**: with the later same-residue
state `B = (board, M, o')` refuted, every win from the earlier
`A = (board, M, o)` must draw a card *before its cursor first passes
`o'` — some stock-draw happens at a pre-`o'` cursor.  Mechanism: a
win whose first draw waits until the cursor has reached `o'` or
beyond can be replayed from `B` — the deal commutation floats the
prefix's deals past its reveals and shuffles
(`deal_commutes_nonStock`), `B` trims the deal count to land on the
same cursor, the draw merges (`drawCard_cursor_indep` — the successor
is position-determined), and the suffix follows verbatim.

TODO(proof) [M]: decompose the winning play at its first
`consumesStock` move; the pre-draw prefix replays from `B` with the
deals trimmed (same residue, no wrap below `o'`); a stock-free win
contradicts `B` directly (non-consuming plays are cursor-blind). -/
theorem window_firstDraw {st : State} {o o' : Nat}
    (hle : o ≤ o') (hres : o % st.drawStep = o' % st.drawStep)
    (hcur : o ≤ st.stock.cards.length) (hcur' : o' ≤ st.stock.cards.length)
    (hA : ({ st with stock := { st.stock with cursor := o } }).solvableFrom)
    (hB : ¬ ({ st with stock := { st.stock with cursor := o' } }).solvableFrom) :
    ∀ play w, ({ st with stock := { st.stock with cursor := o } }).run play = some w →
      w.isWin = true →
      ∃ pre m rest st₁,
        play = pre ++ m :: rest ∧ m.consumesStock = true ∧
        ({ st with stock := { st.stock with cursor := o } }).run pre = some st₁ ∧
        st₁.stock.cursor < o' := sorry

/-- **The window obligation (macro game)**: with the later state
refuted, every winning macro line's first `drawCommit` draws a card
from the *exclusive window* — a position the later cursor cannot
access.  Mechanism: the prefix of reveal commitments and
accommodations is cursor-blind (the deal commutation's other half), so
the later state replays it verbatim; if the first drawn card were also
accessible there, the successors would merge (`drawCard_cursor_indep`)
and the suffix would lift — the later state would win.  This
characterizes the gap between `pace_dominance`'s two sides: when the
better state wins and the worse is refuted, the difference is witnessed
by a window card — the engine's "limit the next draw to the window".

TODO(proof) [M]: decompose `ks` at the first `drawCommit` (the prefix
is all `revealCommit` — the two-kind move set); replay the prefix from
the o'-state (reveals and accommodations are cursor-blind); the merge
gives the successor; the suffix lifts verbatim. -/
theorem window_firstDraw_macro {st : State} {o o' : Nat} (hwf : st.WF)
    (hcur : o ≤ st.stock.cards.length) (hcur' : o' ≤ st.stock.cards.length)
    (hA : ({ st with stock := { st.stock with cursor := o } }).macroSolvable)
    (hB : ¬ ({ st with stock := { st.stock with cursor := o' } }).macroSolvable) :
    ∀ ks w, macroSteps ({ st with stock := { st.stock with cursor := o } }) ks w →
      w.isWin = true →
      ∃ pre x rest,
        ks = pre ++ MacroMove.drawCommit x :: rest ∧
        (∀ k ∈ pre, ∃ c, k = MacroMove.revealCommit c) ∧
        (∀ p, st.stock.posOf x = some p →
          p ∉ Pace.maskPos { cards := st.stock.cards, cursor := o' }
            st.drawStep hwf.step_pos) := sorry

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
