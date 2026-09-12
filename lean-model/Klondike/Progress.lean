import Klondike.Theorems

/-!
# Progress: the cycle theorem, loop-cutting, decidability

Two monotone measures make the commitments strict-progress; plays are
state-deterministic, so loops cut; the state space is finite, so the
verdict is decidable.

- their §9.4 DAG argument: every cycle is a shuffle — the
  visited-list soundness of the search;
- the bounded-witness decidability of `solvableFrom`.
-/

/-- The total hidden depth: `reveal` strictly decreases it, nothing
increases it. -/
def State.totalDepth (st : State) : Nat := (Anchor.all.map st.depths).sum

/-- TODO(proof): only `reveal` changes depths, and only downward. -/
theorem apply_reveal_totalDepth_lt {st st' : State} {c : Card}
    (h : st.apply (Move.reveal c) = some st') : st'.totalDepth < st.totalDepth := sorry

/-- TODO(proof): no move raises any depth. -/
theorem apply_totalDepth_le {st st' : State} {m : Move}
    (h : st.apply m = some st') : st'.totalDepth ≤ st.totalDepth := sorry

/-- TODO(proof): no move adds a card to the cycle. -/
theorem apply_stockLen_le {st st' : State} {m : Move}
    (h : st.apply m = some st') : st'.stock.cards.length ≤ st.stock.cards.length := sorry

/-- TODO(proof): a successful `deckPile` splices the waste top out of
the cycle (the WF cursor bound makes `cursor − 1` a valid index). -/
theorem apply_deckPile_shortens {st st' : State} {c : Card} {b : Base}
    (h : st.apply (Move.deckPile c b) = some st') :
    st'.stock.cards.length < st.stock.cards.length := sorry

/-- TODO(proof): as `deckPile`. -/
theorem apply_deckStack_shortens {st st' : State} {c : Card}
    (h : st.apply (Move.deckStack c) = some st') :
    st'.stock.cards.length < st.stock.cards.length := sorry

/-- **The cycle theorem** (their §9.4 DAG argument): every play that
returns to its own start state is commitment-free.  Depths never
increase (kills `reveal`); nothing returns a card to the cycle (kills
`deckPile`/`deckStack`) — so a net-zero round trip cannot contain any
commitment.  The commitment game is a DAG, and the visited-list
search is sound.  TODO: induction on the play over the two measures. -/
theorem play_self_is_shuffle {st : State} (hwf : st.WF) {play : List Move}
    (h : st.run play = some st) : ∀ m ∈ play, m.isCommit = false := sorry

/-! ## Loop-cutting and the state trace -/

/-- TODO(proof): `run` is a left fold. -/
theorem run_append (st : State) (l₁ l₂ : List Move) :
    st.run (l₁ ++ l₂) = (st.run l₁) >>= fun s => s.run l₂ := sorry

/-- The states a play passes through (empty suffix if it dies). -/
def State.trace (st : State) : List Move → List State
  | [] => [st]
  | m :: ms => st :: match st.apply m with
    | some st' => st'.trace ms
    | none => []

/-- No repeated elements, index-wise. -/
def allDistinct {α : Type} (l : List α) : Prop :=
  ∀ i j : Nat, i < l.length → j < l.length → l[i]? = l[j]? → i = j

/-- The trace's last state is `run`'s result.  TODO: induction on the
play. -/
theorem run_eq_trace_last (st : State) (play : List Move) :
    st.run play = (st.trace play).getLast? := sorry

/-- **The distinct-trace form**: solvability is witnessed by a play
whose trace never repeats a state — apply `play_cut_loop` until no
loop remains.  The middle link of
`solvableFrom → distinctTrace → boundedPlay → decidable`.  TODO. -/
theorem solvable_iff_distinctTrace {st : State} (hwf : st.WF) :
    st.solvableFrom ↔ ∃ play w, st.run play = some w ∧ w.isWin = true ∧
      allDistinct (st.trace play) := sorry

/-- **Loop-cutting**: plays are state-deterministic, so a sub-play that
returns to its own start contributes nothing — cutting it preserves
the destination.  TODO: `run_append` and the fold cancellation. -/
theorem play_cut_loop {st : State} {π₁ π₂ π₃ : List Move} {w : State}
    (hwin : st.run (π₁ ++ π₂ ++ π₃) = some w ∧ w.isWin = true)
    (hrep : ∃ s, st.run π₁ = some s ∧ s.run π₂ = some s) :
    st.run (π₁ ++ π₃) = some w ∧ w.isWin = true := sorry

/-! ## The bound and decidability -/

/-- A deliberately crude over-approximation of the reachable state
space: the deal and draw step are game-fixed; heights have ≤ 14
options each, depths ≤ 29 per pile, the cursor ≤ 53, the remaining
stock contents are determined by the removed subset (≤ 2^52), and the
board is a function from 59 bases to ≤ 53 options (matching legality
ignored).  Astronomical, but any finite bound suffices. -/
def stateSpaceBound : Nat :=
  (14 : Nat)^4 * (29 : Nat)^7 * 53 * (2 : Nat)^52 * (53 : Nat)^59

/-- **Decidability of the verdict**: solvability is witnessed by a
bounded play — cut every loop (`play_cut_loop`); a loop-free play
visits each distinct state at most once, so its length is at most the
state space.  TODO: trace distinctness + the shape count (WF
preservation, `apply_wf`). -/
theorem solvable_iff_boundedPlay {st : State} (hwf : st.WF) :
    st.solvableFrom ↔ ∃ play w, st.run play = some w ∧ w.isWin = true ∧
      play.length ≤ stateSpaceBound := sorry

/-- The verdict is decidable: exhaustive search over bounded plays.
TODO: a `Decidable` instance by bounded enumeration. -/
theorem solvable_decidable (st : State) (hwf : st.WF) :
    st.solvableFrom ∨ ¬ st.solvableFrom := sorry
