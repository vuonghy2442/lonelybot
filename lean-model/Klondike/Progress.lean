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

theorem apply_reveal_totalDepth_lt {st st' : State} {c : Card}
    (h : st.apply (Move.reveal c) = some st') : st'.totalDepth < st.totalDepth := by
  simp only [State.apply] at h
  simp only [State.applyReveal] at h
  cases ht : st.board.topOf (Sum.inr c) with
  | some _ =>
    rw [ht] at h
    simp at h
  | none =>
    cases hb : st.board.bottomOf c with
    | none =>
      rw [ht, hb] at h
      simp at h
    | some b =>
      cases b with
      | inl _ =>
        rw [ht, hb] at h
        simp at h
      | inr r =>
        rw [ht, hb] at h
        simp at h
        cases hp : st.pileOfTopHidden r with
        | none =>
          rw [hp] at h
          simp at h
        | some a =>
          rw [hp] at h
          simp at h
          cases ha : st.board.attach (st.hiddenBase a) r with
          | none =>
            rw [ha] at h
            simp at h
          | some bd =>
            rw [ha] at h
            simp at h
            subst h
            have hta : st.topHidden a = some r := by
              simp only [State.pileOfTopHidden] at hp
              simpa using (findFirst_mem _ _ a hp).2
            have hpos : 0 < st.depths a := by
              simp only [State.topHidden, State.hidden] at hta
              cases hdp : st.depths a with
              | zero =>
                rw [hdp] at hta
                simp at hta
              | succ n => omega
            show (Anchor.all.map (fun a' => if a' = a then st.depths a - 1 else st.depths a')).sum
              < (Anchor.all.map st.depths).sum
            cases a <;> simp [Anchor.all, List.map_cons, List.map_nil,
              List.sum_cons, List.sum_nil] <;> omega

theorem apply_totalDepth_le {st st' : State} {m : Move}
    (h : st.apply m = some st') : st'.totalDepth ≤ st.totalDepth := by
  cases m with
  | draw =>
    simp only [State.apply, State.applyDraw, Option.some.injEq] at h
    subst h
    exact Nat.le_of_eq rfl
  | reveal c =>
    exact Nat.le_of_lt (apply_reveal_totalDepth_lt h)
  | deckPile c b =>
    simp only [State.apply] at h
    simp only [State.applyDeckPile] at h
    cases hp : st.stock.prev with
    | none =>
      rw [hp] at h
      simp at h
    | some c' =>
      rw [hp] at h
      simp at h
      split at h
      · simp at h
      · simp at h
        obtain ⟨-, h'⟩ := h
        subst h'
        exact Nat.le_of_eq rfl
  | deckStack c =>
    simp only [State.apply] at h
    simp only [State.applyDeckStack] at h
    cases hp : st.stock.prev with
    | none =>
      rw [hp] at h
      simp at h
    | some c' =>
      rw [hp] at h
      simp at h
      obtain ⟨-, h'⟩ := h
      subst h'
      exact Nat.le_of_eq rfl
  | pileStack c =>
    simp only [State.apply] at h
    simp only [State.applyPileStack] at h
    cases ht : st.board.topOf (Sum.inr c) with
    | some _ =>
      rw [ht] at h
      simp at h
    | none =>
      rw [ht] at h
      cases hb : st.board.bottomOf c with
      | none =>
        rw [hb] at h
        simp at h
      | some b =>
        rw [hb] at h
        simp at h
        obtain ⟨-, h'⟩ := h
        subst h'
        exact Nat.le_of_eq rfl
  | stackPile c b =>
    simp only [State.apply] at h
    simp only [State.applyStackPile] at h
    simp at h
    split at h
    · simp at h
    · simp at h
      obtain ⟨-, h'⟩ := h
      subst h'
      exact Nat.le_of_eq rfl
  | pilePile c b =>
    simp only [State.apply] at h
    simp only [State.applyPilePile] at h
    cases hb : st.board.bottomOf c with
    | none =>
      rw [hb] at h
      simp at h
    | some b₀ =>
      rw [hb] at h
      simp at h
      split at h
      · simp at h
        obtain ⟨-, h'⟩ := h
        subst h'
        exact Nat.le_of_eq rfl
      · simp at h

theorem apply_deckPile_shortens {st st' : State} {c : Card} {b : Base}
    (h : st.apply (Move.deckPile c b) = some st') :
    st'.stock.cards.length < st.stock.cards.length := by
  simp only [State.apply] at h
  simp only [State.applyDeckPile] at h
  cases hp : st.stock.prev with
  | none =>
    rw [hp] at h
    simp at h
  | some c' =>
    rw [hp] at h
    simp at h
    split at h
    · simp at h
    · simp at h
      obtain ⟨-, h'⟩ := h
      subst h'
      have hidx : st.stock.cursor - 1 < st.stock.cards.length := by
        simp only [Cycle.prev] at hp
        split at hp
        · simp at hp
        · exact (List.getElem?_eq_some_iff.mp hp).1
      show (Cycle.removeIdx st.stock.cards (st.stock.cursor - 1)).length
        < st.stock.cards.length
      have hlen := Cycle.removeIdx_length st.stock.cards (st.stock.cursor - 1) hidx
      omega

theorem apply_deckStack_shortens {st st' : State} {c : Card}
    (h : st.apply (Move.deckStack c) = some st') :
    st'.stock.cards.length < st.stock.cards.length := by
  simp only [State.apply] at h
  simp only [State.applyDeckStack] at h
  cases hp : st.stock.prev with
  | none =>
    rw [hp] at h
    simp at h
  | some c' =>
    rw [hp] at h
    simp at h
    obtain ⟨-, h'⟩ := h
    subst h'
    have hidx : st.stock.cursor - 1 < st.stock.cards.length := by
      simp only [Cycle.prev] at hp
      split at hp
      · simp at hp
      · exact (List.getElem?_eq_some_iff.mp hp).1
    show (Cycle.removeIdx st.stock.cards (st.stock.cursor - 1)).length
      < st.stock.cards.length
    have hlen := Cycle.removeIdx_length st.stock.cards (st.stock.cursor - 1) hidx
    omega

theorem apply_stockLen_le {st st' : State} {m : Move}
    (h : st.apply m = some st') : st'.stock.cards.length ≤ st.stock.cards.length := by
  cases m with
  | draw =>
    simp only [State.apply, State.applyDraw, Option.some.injEq] at h
    subst h
    exact Nat.le_of_eq (by rw [Cycle.dealOnce_cards])
  | reveal c =>
    simp only [State.apply] at h
    simp only [State.applyReveal] at h
    cases ht : st.board.topOf (Sum.inr c) with
    | some _ =>
      rw [ht] at h
      simp at h
    | none =>
      cases hb : st.board.bottomOf c with
      | none =>
        rw [ht, hb] at h
        simp at h
      | some b =>
        cases b with
        | inl _ =>
          rw [ht, hb] at h
          simp at h
        | inr r =>
          rw [ht, hb] at h
          simp at h
          cases hp : st.pileOfTopHidden r with
          | none =>
            rw [hp] at h
            simp at h
          | some a =>
            rw [hp] at h
            simp at h
            cases ha : st.board.attach (st.hiddenBase a) r with
            | none =>
              rw [ha] at h
              simp at h
            | some bd =>
              rw [ha] at h
              simp at h
              subst h
              exact Nat.le_of_eq rfl
  | deckPile c b =>
    exact Nat.le_of_lt (apply_deckPile_shortens h)
  | deckStack c =>
    exact Nat.le_of_lt (apply_deckStack_shortens h)
  | pileStack c =>
    simp only [State.apply] at h
    simp only [State.applyPileStack] at h
    cases ht : st.board.topOf (Sum.inr c) with
    | some _ =>
      rw [ht] at h
      simp at h
    | none =>
      rw [ht] at h
      cases hb : st.board.bottomOf c with
      | none =>
        rw [hb] at h
        simp at h
      | some b =>
        rw [hb] at h
        simp at h
        obtain ⟨-, h'⟩ := h
        subst h'
        exact Nat.le_of_eq rfl
  | stackPile c b =>
    simp only [State.apply] at h
    simp only [State.applyStackPile] at h
    simp at h
    split at h
    · simp at h
    · simp at h
      obtain ⟨-, h'⟩ := h
      subst h'
      exact Nat.le_of_eq rfl
  | pilePile c b =>
    simp only [State.apply] at h
    simp only [State.applyPilePile] at h
    cases hb : st.board.bottomOf c with
    | none =>
      rw [hb] at h
      simp at h
    | some b₀ =>
      rw [hb] at h
      simp at h
      split at h
      · simp at h
        obtain ⟨-, h'⟩ := h
        subst h'
        exact Nat.le_of_eq rfl
      · simp at h

/-- Running a play never raises the total hidden depth. -/
theorem run_totalDepth_le : ∀ (play : List Move) (st st' : State),
    st.run play = some st' → st'.totalDepth ≤ st.totalDepth := by
  intro play
  induction play with
  | nil =>
      intro st st' h
      simp only [State.run, Option.some.injEq] at h
      subst h
      exact Nat.le_refl _
  | cons m ms ih =>
      intro st st' h
      simp only [State.run] at h
      cases h₀ : st.apply m with
      | none =>
          rw [h₀] at h
          simp at h
      | some s₀ =>
          rw [h₀] at h
          have hrest : s₀.run ms = some st' := h
          have h1 := ih s₀ st' hrest
          have h2 := apply_totalDepth_le h₀
          omega

/-- Running a play never adds a card to the cycle. -/
theorem run_stockLen_le : ∀ (play : List Move) (st st' : State),
    st.run play = some st' → st'.stock.cards.length ≤ st.stock.cards.length := by
  intro play
  induction play with
  | nil =>
      intro st st' h
      simp only [State.run, Option.some.injEq] at h
      subst h
      exact Nat.le_refl _
  | cons m ms ih =>
      intro st st' h
      simp only [State.run] at h
      cases h₀ : st.apply m with
      | none =>
          rw [h₀] at h
          simp at h
      | some s₀ =>
          rw [h₀] at h
          have hrest : s₀.run ms = some st' := h
          have h1 := ih s₀ st' hrest
          have h2 := apply_stockLen_le h₀
          omega

/-- A committed move inside a successful play strictly advances at
least one of the two measures by the play's end. -/
theorem run_commit_measures : ∀ (play : List Move) (st st' : State),
    st.run play = some st' → ∀ m ∈ play, m.isCommit = true →
    st'.totalDepth < st.totalDepth ∨ st'.stock.cards.length < st.stock.cards.length := by
  intro play
  induction play with
  | nil =>
      intro st st' _ m hm
      simp at hm
  | cons m₀ ms ih =>
      intro st st' h m hm hmc
      simp only [State.run] at h
      cases h₀ : st.apply m₀ with
      | none =>
          rw [h₀] at h
          simp at h
      | some s₀ =>
          rw [h₀] at h
          have hrest : s₀.run ms = some st' := h
          simp only [List.mem_cons] at hm
          cases hm with
          | inl heq =>
              rw [heq] at hmc
              cases m₀ with
              | draw => simp [Move.isCommit] at hmc
              | reveal c =>
                  left
                  have h1 := apply_reveal_totalDepth_lt h₀
                  have h2 := run_totalDepth_le ms s₀ st' hrest
                  omega
              | deckPile c b =>
                  right
                  have h1 := apply_deckPile_shortens h₀
                  have h2 := run_stockLen_le ms s₀ st' hrest
                  omega
              | deckStack c =>
                  right
                  have h1 := apply_deckStack_shortens h₀
                  have h2 := run_stockLen_le ms s₀ st' hrest
                  omega
              | pileStack c => simp [Move.isCommit] at hmc
              | stackPile c b => simp [Move.isCommit] at hmc
              | pilePile c b => simp [Move.isCommit] at hmc
          | inr hmms =>
              have hih := ih s₀ st' hrest m hmms hmc
              cases hih with
              | inl hlt =>
                  left
                  have h2 := apply_totalDepth_le h₀
                  omega
              | inr hlt =>
                  right
                  have h2 := apply_stockLen_le h₀
                  omega

/-- **The cycle theorem** (their §9.4 DAG argument): every play that
returns to its own start state is commitment-free.  Depths never
increase (kills `reveal`); nothing returns a card to the cycle (kills
`deckPile`/`deckStack`) — so a net-zero round trip cannot contain any
commitment.  The commitment game is a DAG, and the visited-list
search is sound. -/
theorem play_self_is_shuffle {st : State} (hwf : st.WF) {play : List Move}
    (h : st.run play = some st) : ∀ m ∈ play, m.isCommit = false := by
  have := hwf
  intro m hm
  cases hb : m.isCommit with
  | false => rfl
  | true =>
      have hmeas := run_commit_measures play st st h m hm hb
      cases hmeas with
      | inl hlt => exact absurd hlt (Nat.lt_irrefl _)
      | inr hlt => exact absurd hlt (Nat.lt_irrefl _)

/-! ## Loop-cutting and the state trace -/

theorem run_append (st : State) (l₁ l₂ : List Move) :
    st.run (l₁ ++ l₂) = (st.run l₁) >>= fun s => s.run l₂ := by
  revert st
  induction l₁ with
  | nil =>
      intro st
      rfl
  | cons m ms ih =>
      intro st
      simp only [List.cons_append, State.run]
      cases st.apply m with
      | none => rfl
      | some st' => exact ih st'

/-- **Reachability dominance (the general prefix principle)**: if `a`
reaches `b` by any play, every win from `b` lifts to `a` — prefix the
reaching play.  The state-level parent of `solvable_of_accommodates`
(Theorems.lean — which restricts the reaching play to shuffles) and of
the physical-game pace dominances (Macro.lean's
`pace_dominance_phys_*`: the better cursor *reaches* the worse one by
pure deals).  It does *not* subsume the macro-game pace dominance
(`pace_dominance`): the macro game has no deal move — its jumps
consume — so same-mask states at different cursors are mutually
unreachable there, and the simulation/replay argument is genuinely
more general than reachability. -/
theorem solvable_of_reaches {a b : State}
    (hr : ∃ play, a.run play = some b) (hsol : b.solvableFrom) :
    a.solvableFrom := by
  obtain ⟨play, hrun⟩ := hr
  obtain ⟨wplay, w, hwrun, hwin⟩ := hsol
  refine ⟨play ++ wplay, w, ?_, hwin⟩
  rw [run_append, hrun]
  exact hwrun

/-- Mutual reachability is solvability equivalence — the two-sided
prefix principle.  This is the "reversible move ⇒ equivalence" fact
(a reversible move's orbit: the move, then its reverse, gives the two
plays — cf. `pileStack_stackPile_roundtrip`), and the parent of the
same-pace-class equivalences (Macro.lean's `solvable_iff_pure_cursors`:
the pure cursors are mutually reachable through the deal-orbit cycle
pass-end → wrap → fresh pass). -/
theorem solvable_iff_mutuallyReaches {a b : State}
    (hab : ∃ play, a.run play = some b) (hba : ∃ play, b.run play = some a) :
    a.solvableFrom ↔ b.solvableFrom :=
  ⟨fun h => solvable_of_reaches hba h, fun h => solvable_of_reaches hab h⟩

/-- The contrapositive — the engine-facing pruning form: a refuted
state kills everything it reaches (why a refuted state's successors
are all dead, and the registry's "skip" rules' justification). -/
theorem unsolvable_of_reaches {a b : State}
    (hr : ∃ play, a.run play = some b) (hna : ¬ a.solvableFrom) :
    ¬ b.solvableFrom := fun hb => hna (solvable_of_reaches hr hb)

/-- **The one-step simulation theorem**: if `R` relates `a` to `b`,
every `b`-move can be matched on the `a` side by some move landing
*equal or `R`-related*, and `R` preserves wins — then every win from
`b` lifts to `a`.

The parent of the replay arguments: `pace_dominance` (R = same
board/mask, maskPos-superset; reveals preserve R, draws merge — the
`a' = b'` disjunct), the window lemmas' replays, and — with the move
map read existentially — the relabeling lifts (`solvable_relabel`: the
matched move is the relabeled one).  `solvable_of_reaches` is the
degenerate instance where the matching play is fixed in advance. -/
theorem solvable_of_simulates {a b : State} (R : State → State → Prop)
    (hR : R a b)
    (hstep : ∀ x y m b', R x y → y.apply m = some b' →
      ∃ m' a', x.apply m' = some a' ∧ (a' = b' ∨ R a' b'))
    (hwin : ∀ x y, R x y → y.isWin = true → x.isWin = true)
    (hsol : b.solvableFrom) : a.solvableFrom := by
  obtain ⟨play, w, hwrun, hwinw⟩ := hsol
  have main : ∀ (x y : State) (play : List Move), R x y →
      y.run play = some w → w.isWin = true →
      ∃ play' w', x.run play' = some w' ∧ w'.isWin = true := by
    intro x y play hRxy
    induction play generalizing x y with
    | nil =>
        intro hrun hwin'
        have hyw : y = w := by
          simp only [State.run] at hrun
          exact Option.some.inj hrun
        rw [← hyw] at hwin'
        exact ⟨[], x, rfl, hwin x y hRxy hwin'⟩
    | cons m ms ih =>
        intro hrun hwin'
        simp only [State.run] at hrun
        cases hm : y.apply m with
        | none =>
            rw [hm] at hrun
            simp at hrun
        | some b'' =>
            rw [hm] at hrun
            obtain ⟨m', a', ha', hcase⟩ := hstep x y m b'' hRxy hm
            rcases hcase with rfl | hR'
            · exact ⟨m' :: ms, w, by simp only [State.run, ha']; exact hrun, hwin'⟩
            · obtain ⟨play'', w'', hrun'', hwin''⟩ := ih a' b'' hR' hrun hwin'
              exact ⟨m' :: play'', w'', by simp only [State.run, ha']; exact hrun'',
                hwin''⟩
  obtain ⟨play', w', hrun', hwin'⟩ := main a b play hR hwrun hwinw
  exact ⟨play', w', hrun', hwin'⟩

/-- The states a play passes through (empty suffix if it dies). -/
def State.trace (st : State) : List Move → List State
  | [] => [st]
  | m :: ms =>
    match st.apply m with
    | some st' =>
      match st'.trace ms with
      | [] => []
      | rest => st :: rest
    | none => []

/-- No repeated elements, index-wise. -/
def allDistinct {α : Type} (l : List α) : Prop :=
  ∀ i j : Nat, i < l.length → j < l.length → l[i]? = l[j]? → i = j

/-- The trace's last state is `run`'s result. -/
theorem run_eq_trace_last (st : State) (play : List Move) :
    st.run play = (st.trace play).getLast? := by
  revert st
  induction play with
  | nil =>
      intro st
      rfl
  | cons m ms ih =>
      intro st
      simp only [State.run, State.trace]
      cases st.apply m with
      | none => rfl
      | some st' =>
          simp
          cases htr : st'.trace ms with
          | nil =>
              have ih' := ih st'
              rw [htr] at ih'
              exact ih'
          | cons s rest =>
              have ih' := ih st'
              rw [htr] at ih'
              exact ih'

/-- **Loop-cutting**: plays are state-deterministic, so a sub-play that
returns to its own start contributes nothing — cutting it preserves
the destination. -/
theorem play_cut_loop {st : State} {π₁ π₂ π₃ : List Move} {w : State}
    (hwin : st.run (π₁ ++ π₂ ++ π₃) = some w ∧ w.isWin = true)
    (hrep : ∃ s, st.run π₁ = some s ∧ s.run π₂ = some s) :
    st.run (π₁ ++ π₃) = some w ∧ w.isWin = true := by
  obtain ⟨s, hr₁, hr₂⟩ := hrep
  obtain ⟨hw, hwinw⟩ := hwin
  refine ⟨?_, hwinw⟩
  rw [run_append st (π₁ ++ π₂) π₃, run_append st π₁ π₂, hr₁] at hw
  have hw' : (s.run π₂ >>= fun x => x.run π₃) = some w := hw
  rw [hr₂] at hw'
  have hw'' : s.run π₃ = some w := hw'
  rw [run_append st π₁ π₃, hr₁]
  exact hw''

/-- Inverting a successful cons run: the move applies, the rest runs,
and the trace extends by the start state. -/
theorem run_cons_inv {st : State} {m : Move} {ms : List Move} {w : State}
    (h : st.run (m :: ms) = some w) :
    ∃ s', st.apply m = some s' ∧ s'.run ms = some w ∧ st.trace (m :: ms) = st :: s'.trace ms := by
  simp only [State.run] at h
  cases hm : st.apply m with
  | none =>
      rw [hm] at h
      simp at h
  | some s' =>
      rw [hm] at h
      have hrest : s'.run ms = some w := h
      have hlast' : (s'.trace ms).getLast? = some w := (run_eq_trace_last s' ms).symm.trans hrest
      refine ⟨s', rfl, hrest, ?_⟩
      simp only [State.trace]
      rw [hm]
      simp
      cases htl : s'.trace ms with
      | nil =>
          rw [htl] at hlast'
          simp at hlast'
      | cons x t => rfl

/-- A successful split run: the first segment reaches `s` and the
second continues to `w`. -/
theorem run_split {st s w : State} {A B : List Move}
    (h : st.run (A ++ B) = some w) (hA : st.run A = some s) : s.run B = some w := by
  rw [run_append st A B, hA] at h
  exact h

/-- The i-th trace state is where the first i moves land. -/
theorem run_take_trace : ∀ (play : List Move) (st w : State),
    st.run play = some w → ∀ i, i ≤ play.length →
    st.run (play.take i) = (st.trace play)[i]? := by
  intro play
  induction play with
  | nil =>
      intro st w h i hi
      cases i with
      | zero => rfl
      | succ k => simp at hi
  | cons m ms ih =>
      intro st w h i hi
      obtain ⟨s', hm, hrest, htr⟩ := run_cons_inv h
      cases i with
      | zero =>
          rw [htr]
          rfl
      | succ k =>
          rw [htr]
          show st.run (m :: ms.take k) = (s'.trace ms)[k]?
          have hL : st.run (m :: ms.take k) = s'.run (ms.take k) := by
            simp only [State.run]
            rw [hm]
          rw [hL]
          have hk : k ≤ ms.length := by
            simp only [List.length_cons] at hi
            omega
          exact ih s' w hrest k hk

/-- A successful play's trace has one state per move, plus the start. -/
theorem trace_length_succ : ∀ (play : List Move) (st w : State),
    st.run play = some w → (st.trace play).length = play.length + 1 := by
  intro play
  induction play with
  | nil =>
      intro st w h
      rfl
  | cons m ms ih =>
      intro st w h
      obtain ⟨s', hm, hrest, htr⟩ := run_cons_inv h
      rw [htr]
      simp only [List.length_cons]
      rw [ih s' w hrest]

/-- Loop-cutting terminates: a winning play of bounded length yields a
winning play with a distinct trace. -/
theorem solvable_distinct_aux : ∀ (n : Nat) (st : State) (play : List Move) (w : State),
    play.length ≤ n → st.run play = some w → w.isWin = true →
    ∃ play' w', st.run play' = some w' ∧ w'.isWin = true ∧ allDistinct (st.trace play') := by
  intro n
  induction n with
  | zero =>
      intro st play w hlen hrun hwin
      cases play with
      | nil =>
          simp only [State.run, Option.some.injEq] at hrun
          subst hrun
          refine ⟨[], st, rfl, hwin, ?_⟩
          intro i j hi hj _
          simp only [State.trace, List.length_cons, List.length_nil] at hi hj
          omega
      | cons m ms => simp at hlen
  | succ n ih =>
      intro st play w hlen hrun hwin
      by_cases hdist : allDistinct (st.trace play)
      · exact ⟨play, w, hrun, hwin, hdist⟩
      · have hlen1 : (st.trace play).length = play.length + 1 := trace_length_succ play st w hrun
        have hrep0 : ∃ i j, i < (st.trace play).length ∧ j < (st.trace play).length ∧
            (st.trace play)[i]? = (st.trace play)[j]? ∧ i ≠ j := by
          apply Classical.byContradiction
          intro hcon
          apply hdist
          intro i j hi hj hget
          apply Classical.byContradiction
          intro hne
          exact hcon ⟨i, j, hi, hj, hget, hne⟩
        have hrep : ∃ i j, i < j ∧ j < (st.trace play).length ∧
            (st.trace play)[i]? = (st.trace play)[j]? := by
          obtain ⟨i, j, hi, hj, hget, hne⟩ := hrep0
          cases Nat.lt_or_ge i j with
          | inl hlt => exact ⟨i, j, hlt, hj, hget⟩
          | inr hge => exact ⟨j, i, by omega, hi, hget.symm⟩
        obtain ⟨i, j, hij, hjlen, hget⟩ := hrep
        have hile : i ≤ play.length := by omega
        have hjle : j ≤ play.length := by omega
        have hine : (st.trace play)[i]? ≠ none := by
          intro hx
          have hx' := List.getElem?_eq_none_iff.mp hx
          omega
        cases hx : (st.trace play)[i]? with
        | none => exact absurd hx hine
        | some si =>
            have hri : st.run (play.take i) = some si := by
              rw [run_take_trace play st w hrun i hile, hx]
            have hrj : st.run (play.take j) = some si := by
              rw [run_take_trace play st w hrun j hjle, ← hget, hx]
            have htj : play.take j = play.take i ++ (play.drop i).take (j - i) := by
              have h : play.take (i + (j - i)) = play.take i ++ (play.drop i).take (j - i) :=
                List.take_add
              rw [show i + (j - i) = j by omega] at h
              exact h
            have hrunij : st.run (play.take i ++ (play.drop i).take (j - i)) = some si := by
              rw [← htj]
              exact hrj
            have hmid : si.run ((play.drop i).take (j - i)) = some si :=
              run_split hrunij hri
            have h4 : play.take i ++ (play.drop i).take (j - i) ++ play.drop j = play := by
              rw [← htj]
              exact List.take_append_drop j play
            obtain ⟨hcutrun, hcutwin⟩ := play_cut_loop (π₁ := play.take i)
                (π₂ := (play.drop i).take (j - i)) (π₃ := play.drop j)
                (⟨by rw [h4]; exact hrun, hwin⟩) ⟨si, hri, hmid⟩
            have hnewlen : (play.take i ++ play.drop j).length ≤ n := by
              have hL : (play.take i ++ play.drop j).length
                  = (play.take i).length + (play.drop j).length := List.length_append
              have h1 : (play.take i).length = min i play.length := List.length_take
              have h2 : (play.drop j).length = play.length - j := List.length_drop
              omega
            obtain ⟨play', w', hr', hw', hd'⟩ :=
              ih st (play.take i ++ play.drop j) w hnewlen hcutrun hcutwin
            exact ⟨play', w', hr', hw', hd'⟩

/-- **The distinct-trace form**: solvability is witnessed by a play
whose trace never repeats a state — apply `play_cut_loop` until no
loop remains.  The middle link of
`solvableFrom → distinctTrace → boundedPlay → decidable`. -/
theorem solvable_iff_distinctTrace {st : State} (hwf : st.WF) :
    st.solvableFrom ↔ ∃ play w, st.run play = some w ∧ w.isWin = true ∧
      allDistinct (st.trace play) := by
  have := hwf
  constructor
  · intro hsol
    obtain ⟨play, w, hrun, hwin⟩ := hsol
    exact solvable_distinct_aux play.length st play w (Nat.le_refl _) hrun hwin
  · intro h
    obtain ⟨play, w, hrun, hwin, -⟩ := h
    exact ⟨play, w, hrun, hwin⟩

/-! ## The bound and decidability -/

/-- A deliberately crude over-approximation of the reachable state
space: the deal and draw step are game-fixed; heights have ≤ 14
options each, depths ≤ 29 per pile, the cursor ≤ 53, the remaining
stock contents are determined by the removed subset (≤ 2^52), and the
board is a function from 59 bases to ≤ 53 options (matching legality
ignored).  Astronomical, but any finite bound suffices. -/
def stateSpaceBound : Nat :=
  (14 : Nat)^4 * (29 : Nat)^7 * 53 * (2 : Nat)^52 * (53 : Nat)^59

/-! ### Distinctness plumbing -/

/-- The head can be re-attached. -/
theorem allDistinct_cons {α : Type} {x : α} {t : List α}
    (h1 : x ∉ t) (h2 : allDistinct t) : allDistinct (x :: t) := by
  intro i j hi hj heq
  cases i with
  | zero =>
      cases j with
      | zero => rfl
      | succ k =>
          rw [List.getElem?_cons_zero, List.getElem?_cons_succ] at heq
          exact absurd (List.mem_iff_getElem?.mpr ⟨k, heq.symm⟩) h1
  | succ k =>
      cases j with
      | zero =>
          rw [List.getElem?_cons_zero, List.getElem?_cons_succ] at heq
          exact absurd (List.mem_iff_getElem?.mpr ⟨k, heq⟩) h1
      | succ k' =>
          rw [List.getElem?_cons_succ, List.getElem?_cons_succ] at heq
          have := h2 k k'
            (by simp only [List.length_cons] at hi; omega)
            (by simp only [List.length_cons] at hj; omega) heq
          omega

/-- The tail of a distinct list is distinct. -/
theorem allDistinct_cons_tail {α : Type} {x : α} {t : List α}
    (h : allDistinct (x :: t)) : allDistinct t := by
  intro i j hi hj heq
  have heq' : (x :: t)[i + 1]? = (x :: t)[j + 1]? := by
    rw [List.getElem?_cons_succ, List.getElem?_cons_succ]
    exact heq
  have := h (i + 1) (j + 1)
    (by simp only [List.length_cons]; omega)
    (by simp only [List.length_cons]; omega) heq'
  omega

/-- A distinct list's head is not in its tail. -/
theorem allDistinct_cons_notMem {α : Type} {x : α} {t : List α}
    (h : allDistinct (x :: t)) : x ∉ t := by
  intro hm
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hm
  have hb : j < t.length := (List.getElem?_eq_some_iff.mp hj).1
  have heq : (x :: t)[0]? = (x :: t)[j + 1]? := by
    rw [List.getElem?_cons_zero, List.getElem?_cons_succ]
    exact hj.symm
  have := h 0 (j + 1) (by simp)
    (by simp only [List.length_cons]; omega) heq
  omega

/-- Distinctness of the right summand. -/
theorem allDistinct_append_right {α : Type} {A B : List α}
    (h : allDistinct (A ++ B)) : allDistinct B := by
  intro i j hi hj heq
  have hb : (A ++ B).length = A.length + B.length := List.length_append
  have heq' : (A ++ B)[A.length + i]? = (A ++ B)[A.length + j]? := by
    rw [List.getElem?_append_right (by omega), List.getElem?_append_right (by omega)]
    rw [Nat.add_sub_cancel_left, Nat.add_sub_cancel_left]
    exact heq
  have := h (A.length + i) (A.length + j) (by omega) (by omega) heq'
  omega

/-- The list splits around any member. -/
theorem mem_split {α : Type} : ∀ (l : List α) (x : α), x ∈ l →
    ∃ l₁ l₂, l = l₁ ++ x :: l₂ := by
  intro l
  induction l with
  | nil => intro x h; cases h
  | cons a t ih =>
      intro x h
      rcases List.mem_cons.mp h with rfl | h'
      · exact ⟨[], t, rfl⟩
      · obtain ⟨l₁, l₂, hs⟩ := ih x h'
        exact ⟨a :: l₁, l₂, by rw [hs, List.cons_append]⟩

/-- **The pigeonhole**: a distinct list contained in `t` is at most as
long as `t`. -/
theorem pigeonhole_le {α : Type} : ∀ (l t : List α), allDistinct l →
    (∀ x ∈ l, x ∈ t) → l.length ≤ t.length := by
  intro l
  induction l with
  | nil => intro t _ _; exact Nat.zero_le _
  | cons x l' ih =>
      intro t hdist hsub
      obtain ⟨t₁, t₂, hsplit⟩ := mem_split t x (hsub x (by simp))
      have hxnl : x ∉ l' := allDistinct_cons_notMem hdist
      have hsub' : ∀ y ∈ l', y ∈ t₁ ++ t₂ := by
        intro y hy
        have hyt : y ∈ t := hsub y (by simp [hy])
        rw [hsplit] at hyt
        rcases List.mem_append.mp hyt with h | h
        · exact List.mem_append_left _ h
        · rcases List.mem_cons.mp h with h' | h'
          · exact absurd (by rw [← h']; exact hy) hxnl
          · exact List.mem_append_right _ h'
      have hih := ih (t₁ ++ t₂) (allDistinct_cons_tail hdist) hsub'
      have hlen : t.length = t₁.length + 1 + t₂.length := by
        rw [hsplit, List.length_append, List.length_cons]
        omega
      have hla : (t₁ ++ t₂).length = t₁.length + t₂.length := List.length_append
      simp only [List.length_cons]
      omega

/-- Distinct naturals below `n` number at most `n`. -/
theorem distinct_nat_count_le (l : List Nat) (n : Nat) (hdist : allDistinct l)
    (hlt : ∀ x ∈ l, x < n) : l.length ≤ n := by
  have h := pigeonhole_le l (List.range n) hdist
    (fun x hx => List.mem_range.mpr (hlt x hx))
  rw [List.length_range] at h
  exact h

/-- Distinctness survives filtering. -/
theorem allDistinct_filter {α : Type} (p : α → Bool) : ∀ (l : List α),
    allDistinct l → allDistinct (l.filter p) := by
  intro l
  induction l with
  | nil => intro _; intro i j hi _ _; simp at hi
  | cons a t ih =>
      intro h
      by_cases hp : p a = true
      · rw [List.filter_cons, if_pos hp]
        refine allDistinct_cons ?_ (ih (allDistinct_cons_tail h))
        intro hm
        exact allDistinct_cons_notMem h (List.mem_filter.mp hm).1
      · rw [List.filter_cons, if_neg hp]
        exact ih (allDistinct_cons_tail h)

/-! ### The stock filter invariant -/

/-- A noDup list is its own membership filter (order included). -/
theorem filter_mem_idem : ∀ (l : List Card), noDupCards l →
    l = l.filter (fun x => decide (x ∈ l)) := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons a t ih =>
      intro hnd
      have hnot : a ∉ t := allDistinct_cons_notMem hnd
      rw [List.filter_cons, if_pos (decide_eq_true (by simp))]
      refine congrArg (a :: ·) ?_
      refine Eq.trans (ih (allDistinct_cons_tail hnd)) ?_
      exact (List.filter_congr (fun x hx => by
        by_cases hxa : x = a
        · exact absurd (by rw [← hxa]; exact hx) hnot
        · simp [List.mem_cons, hxa])).symm

/-- A filter of the list is the membership filter of itself. -/
theorem filter_mem_self {orig cur : List Card} {p : Card → Bool}
    (h : cur = orig.filter p) : cur = orig.filter (fun x => decide (x ∈ cur)) := by
  subst h
  refine List.filter_congr (fun x hx => ?_)
  cases hxp : p x with
  | true =>
      exact (decide_eq_true (List.mem_filter.mpr ⟨hx, hxp⟩)).symm
  | false =>
      exact (decide_eq_false (fun hmem =>
        Bool.noConfusion (hxp.symm.trans (List.mem_filter.mp hmem).2))).symm

/-- Splicing out an index keeps exactly the remaining members, in
order. -/
theorem removeIdx_filter_mem : ∀ (l : List Card) (i : Nat), noDupCards l →
    Cycle.removeIdx l i = l.filter (fun x => decide (x ∈ Cycle.removeIdx l i)) := by
  intro l
  induction l with
  | nil => intro i _; rfl
  | cons a t ih =>
      intro i hnd
      have hnot : a ∉ t := allDistinct_cons_notMem hnd
      have hdt := allDistinct_cons_tail hnd
      cases i with
      | zero =>
          show t = (a :: t).filter (fun x => decide (x ∈ t))
          rw [List.filter_cons, if_neg (by simp [hnot])]
          exact filter_mem_idem t hdt
      | succ j =>
          show a :: Cycle.removeIdx t j
            = (a :: t).filter (fun x => decide (x ∈ a :: Cycle.removeIdx t j))
          rw [List.filter_cons, if_pos (decide_eq_true (by simp))]
          refine congrArg (a :: ·) ?_
          refine Eq.trans (ih j hdt) ?_
          exact (List.filter_congr (fun x hx => by
            by_cases hxa : x = a
            · exact absurd (by rw [← hxa]; exact hx) hnot
            · simp [List.mem_cons, hxa])).symm

/-! ### The radix encoding -/

/-- Little-endian radix value of `f` over `l`. -/
def encF (r : Nat) {α : Type} (l : List α) (f : α → Nat) : Nat :=
  (l.map f).foldr (fun x acc => x + r * acc) 0

theorem radix_peel {a a' r b b' : Nat} (hr : 0 < r) (ha : a < r) (ha' : a' < r)
    (h : a + r * b = a' + r * b') : a = a' ∧ b = b' := by
  have hm : (a + r * b) % r = (a' + r * b') % r := congrArg (fun k => k % r) h
  rw [Nat.add_mul_mod_self_left, Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt ha'] at hm
  refine ⟨hm, ?_⟩
  rw [hm] at h
  exact Nat.eq_of_mul_eq_mul_left hr (Nat.add_left_cancel h)

theorem nest_lt {a r b R : Nat} (ha : a < r) (hb : b < R) :
    a + r * b < r * R := by
  have h1 : a + r * b < r + r * b := Nat.add_lt_add_right ha _
  have h2 : r + r * b = r * (1 + b) := by rw [Nat.mul_add, Nat.mul_one]
  calc a + r * b < r + r * b := h1
    _ = r * (1 + b) := h2
    _ ≤ r * R := Nat.mul_le_mul (Nat.le_refl r) (by omega)

theorem encF_inj {α : Type} (r : Nat) (hr : 0 < r) : ∀ (l : List α) (f g : α → Nat),
    (∀ x ∈ l, f x < r) → (∀ x ∈ l, g x < r) →
    encF r l f = encF r l g → ∀ x ∈ l, f x = g x := by
  intro l
  induction l with
  | nil => intro f g _ _ _ x hx; cases hx
  | cons a t ih =>
      intro f g hf hg h x hx
      have hstep : f a + r * encF r t f = g a + r * encF r t g := h
      obtain ⟨ha, hrest⟩ := radix_peel hr (hf a (by simp)) (hg a (by simp)) hstep
      rcases List.mem_cons.mp hx with rfl | hxt
      · exact ha
      · exact ih f g (fun y hy => hf y (by simp [hy]))
          (fun y hy => hg y (by simp [hy])) hrest x hxt

theorem encF_lt {α : Type} (r : Nat) : ∀ (l : List α) (f : α → Nat),
    (∀ x ∈ l, f x < r) → encF r l f < r ^ l.length := by
  intro l
  induction l with
  | nil => intro f _; exact Nat.zero_lt_one
  | cons a t ih =>
      intro f hf
      have h1 := hf a (by simp)
      have h2 := ih f (fun y hy => hf y (by simp [hy]))
      show f a + r * encF r t f < r ^ (t.length + 1)
      rw [Nat.pow_add, Nat.pow_one]
      calc f a + r * encF r t f < r * r ^ t.length := nest_lt h1 h2
        _ = r ^ t.length * r := Nat.mul_comm _ _

/-- The map of a distinct list under an injective-on-it function is
distinct. -/
theorem allDistinct_map {α β : Type} (f : α → β) {l : List α} (hd : allDistinct l)
    (hinj : ∀ x ∈ l, ∀ y ∈ l, f x = f y → x = y) : allDistinct (l.map f) := by
  intro i j hi hj heq
  have hl : (l.map f).length = l.length := List.length_map f
  rw [List.getElem?_map, List.getElem?_map] at heq
  cases h1 : l[i]? with
  | none =>
      rw [List.getElem?_eq_none_iff] at h1
      omega
  | some x =>
      cases h2 : l[j]? with
      | none =>
          rw [List.getElem?_eq_none_iff] at h2
          omega
      | some y =>
          rw [h1, h2, Option.map_some, Option.map_some, Option.some.injEq] at heq
          have hx : x ∈ l := List.mem_iff_getElem?.mpr ⟨i, h1⟩
          have hy : y ∈ l := List.mem_iff_getElem?.mpr ⟨j, h2⟩
          have hxy : x = y := hinj x hx y hy heq
          have hget : l[i]? = l[j]? := by
            rw [h1, hxy]
            exact h2.symm
          exact hd i j (by omega) (by omega) hget

/-! ### The state code -/

/-- The suit's numeric view (0..3). -/
def suitCode (s : Suit) : Nat :=
  match s with
  | ⟨Color.red, false⟩ => 0
  | ⟨Color.red, true⟩ => 1
  | ⟨Color.black, false⟩ => 2
  | ⟨Color.black, true⟩ => 3

theorem suitCode_lt (s : Suit) : suitCode s < 4 := by
  rcases s with ⟨c, p⟩
  cases c <;> cases p <;> decide

theorem suitCode_inj {s s' : Suit} (h : suitCode s = suitCode s') : s = s' := by
  rcases s with ⟨c, p⟩
  rcases s' with ⟨c', p'⟩
  cases c <;> cases c' <;> cases p <;> cases p' <;> simp_all [suitCode]

/-- The card's numeric view (0..51), injective. -/
def cardCode (c : Card) : Nat := c.rank.toIdx + 13 * suitCode c.suit

theorem cardCode_lt (c : Card) : cardCode c < 52 := by
  rcases c with ⟨s, r⟩
  have h1 := Rank.toIdx_lt r
  have h2 := suitCode_lt s
  show r.toIdx + 13 * suitCode s < 52
  omega

theorem cardCode_inj {c c' : Card} (h : cardCode c = cardCode c') : c = c' := by
  rcases c with ⟨s, r⟩
  rcases c' with ⟨s', r'⟩
  have h1 := Rank.toIdx_lt r
  have h2 := Rank.toIdx_lt r'
  have h3 : r.toIdx + 13 * suitCode s = r'.toIdx + 13 * suitCode s' := h
  have hs : suitCode s = suitCode s' := by omega
  have hr : r.toIdx = r'.toIdx := by omega
  rw [Card.mk.injEq]
  exact ⟨suitCode_inj hs, Rank.toIdx_inj hr⟩

/-- The base-digit: `none ↦ 0`, `some c ↦ 1 + cardCode c`. -/
def optCode (o : Option Card) : Nat :=
  match o with
  | none => 0
  | some c => 1 + cardCode c

theorem optCode_lt (o : Option Card) : optCode o < 53 := by
  cases o with
  | none => decide
  | some c =>
      have := cardCode_lt c
      show 1 + cardCode c < 53
      omega

theorem optCode_inj {o o' : Option Card} (h : optCode o = optCode o') : o = o' := by
  cases o with
  | none =>
      cases o' with
      | none => rfl
      | some c =>
          have h2 : (0 : Nat) = 1 + cardCode c := h
          exact absurd h2 (by omega)
  | some c =>
      cases o' with
      | none =>
          have h2 : (1 : Nat) + cardCode c = 0 := h
          exact absurd h2 (by omega)
      | some c' =>
          have h2 : (1 : Nat) + cardCode c = 1 + cardCode c' := h
          rw [cardCode_inj (Nat.add_left_cancel h2)]

/-- The stock bit: is the card still in the cycle. -/
def stockBits (cur : List Card) (x : Card) : Nat :=
  if x ∈ cur then 1 else 0

theorem stockBits_lt (cur : List Card) (x : Card) : stockBits cur x < 2 := by
  unfold stockBits
  split <;> omega

theorem stockBits_eq_decide {cur₁ cur₂ : List Card} {x : Card}
    (h : stockBits cur₁ x = stockBits cur₂ x) :
    decide (x ∈ cur₁) = decide (x ∈ cur₂) := by
  unfold stockBits at h
  by_cases c₁ : x ∈ cur₁
  · by_cases c₂ : x ∈ cur₂
    · rw [decide_eq_true c₁, decide_eq_true c₂]
    · rw [if_pos c₁, if_neg c₂] at h
      exact absurd h (by omega)
  · by_cases c₂ : x ∈ cur₂
    · rw [if_neg c₁, if_pos c₂] at h
      exact absurd h.symm (by omega)
    · rw [decide_eq_false c₁, decide_eq_false c₂]

theorem Anchor.toIdx_lt (a : Anchor) : a.toIdx < 7 := by cases a <;> decide

theorem Board.enumBase_length : Board.enumBase.length = 59 := by decide

/-- The carried shape invariant along a trace from `st`: the deal and
draw step are fixed, the state stays WF, and the stock cycle is a
filter of the start state's stock (the deal order inherited — the
contents are determined by the removed subset). -/
def traceOK (st s : State) : Prop :=
  s.deal = st.deal ∧ s.drawStep = st.drawStep ∧ s.WF ∧
    ∃ p : Card → Bool, s.stock.cards = st.stock.cards.filter p

theorem traceOK_self {st : State} (hwf : st.WF) : traceOK st st := by
  refine ⟨rfl, rfl, hwf, ?_⟩
  exact ⟨fun x => decide (x ∈ st.stock.cards),
    filter_mem_idem st.stock.cards hwf.stock_wf.1⟩

theorem traceOK_step {ST s s' : State} (m : Move) (hok : traceOK ST s)
    (h : s.apply m = some s') : traceOK ST s' := by
  obtain ⟨hdeal, hstep, hwf, p, hp⟩ := hok
  have hwf' := apply_wf hwf m s' h
  cases m with
  | draw =>
      rw [apply_draw_iff] at h
      obtain ⟨rfl⟩ := h
      refine ⟨hdeal, hstep, hwf', ?_⟩
      refine ⟨p, ?_⟩
      show (s.stock.dealOnce s.drawStep).cards = ST.stock.cards.filter p
      rw [Cycle.dealOnce_cards]
      exact hp
  | reveal c =>
      rw [apply_reveal_iff] at h
      obtain ⟨_, _, _, _, _, _, _, hst⟩ := h
      refine ⟨?_, ?_, hwf', ?_⟩
      · rw [hst]; exact hdeal
      · rw [hst]; exact hstep
      · exact ⟨p, by rw [hst]; exact hp⟩
  | deckPile c b =>
      rw [apply_deckPile_iff] at h
      obtain ⟨_, _, _, _, hst⟩ := h
      refine ⟨?_, ?_, hwf', ?_⟩
      · rw [hst]; exact hdeal
      · rw [hst]; exact hstep
      · refine ⟨fun x => decide (x ∈ Cycle.removeIdx s.stock.cards (s.stock.cursor - 1))
          && p x, ?_⟩
        rw [hst]
        show Cycle.removeIdx s.stock.cards (s.stock.cursor - 1)
          = ST.stock.cards.filter (fun x =>
              decide (x ∈ Cycle.removeIdx s.stock.cards (s.stock.cursor - 1)) && p x)
        have hA := removeIdx_filter_mem s.stock.cards (s.stock.cursor - 1) hwf.stock_wf.1
        rw [hp] at hA
        rw [List.filter_filter] at hA
        rw [← hp] at hA
        exact hA
  | deckStack c =>
      rw [apply_deckStack_iff] at h
      obtain ⟨_, _, hst⟩ := h
      refine ⟨?_, ?_, hwf', ?_⟩
      · rw [hst]; exact hdeal
      · rw [hst]; exact hstep
      · refine ⟨fun x => decide (x ∈ Cycle.removeIdx s.stock.cards (s.stock.cursor - 1))
          && p x, ?_⟩
        rw [hst]
        show Cycle.removeIdx s.stock.cards (s.stock.cursor - 1)
          = ST.stock.cards.filter (fun x =>
              decide (x ∈ Cycle.removeIdx s.stock.cards (s.stock.cursor - 1)) && p x)
        have hA := removeIdx_filter_mem s.stock.cards (s.stock.cursor - 1) hwf.stock_wf.1
        rw [hp] at hA
        rw [List.filter_filter] at hA
        rw [← hp] at hA
        exact hA
  | pileStack c =>
      rw [apply_pileStack_iff] at h
      obtain ⟨_, _, _, _, hst⟩ := h
      refine ⟨?_, ?_, hwf', ?_⟩
      · rw [hst]; exact hdeal
      · rw [hst]; exact hstep
      · exact ⟨p, by rw [hst]; exact hp⟩
  | stackPile c b =>
      rw [apply_stackPile_iff] at h
      obtain ⟨_, _, _, _, hst⟩ := h
      refine ⟨?_, ?_, hwf', ?_⟩
      · rw [hst]; exact hdeal
      · rw [hst]; exact hstep
      · exact ⟨p, by rw [hst]; exact hp⟩
  | pilePile c b =>
      rw [apply_pilePile_iff] at h
      obtain ⟨_, _, _, _, _, _, hst⟩ := h
      refine ⟨?_, ?_, hwf', ?_⟩
      · rw [hst]; exact hdeal
      · rw [hst]; exact hstep
      · exact ⟨p, by rw [hst]; exact hp⟩

theorem trace_traceOK (ST : State) : ∀ (play : List Move) (st w : State),
    traceOK ST st → st.run play = some w → ∀ s ∈ st.trace play, traceOK ST s := by
  intro play
  induction play with
  | nil =>
      intro st w hok hrun s hs
      rcases List.mem_singleton.mp hs with rfl
      exact hok
  | cons m ms ih =>
      intro st w hok hrun s hs
      obtain ⟨s', happl, hrest, htr⟩ := run_cons_inv hrun
      rw [htr] at hs
      rcases List.mem_cons.mp hs with rfl | hs'
      · exact hok
      · exact ih s' w (traceOK_step m hok happl) hrest s hs'

/-! ### WF digit bounds -/

theorem heights_digit_lt {s : State} (hwf : s.WF) (x : Suit) : s.heights x < 14 := by
  have := hwf.heights_le x
  omega

theorem depths_digit_lt {s : State} (hwf : s.WF) (x : Anchor) : s.depths x < 29 := by
  have h1 : s.depths x ≤ (s.deal.piles x).length := hwf.depths_le x
  have h2 : (s.deal.piles x).length = x.toIdx + 1 := hwf.deal_wf.1 x
  have h3 := Anchor.toIdx_lt x
  omega

theorem stockLen_le {s : State} (hwf : s.WF) : s.stock.cards.length ≤ 24 := by
  obtain ⟨hnd, hmem⟩ := hwf.stock_wf
  have h1 := pigeonhole_le s.stock.cards s.deal.stock hnd hmem
  have h24 : s.deal.stock.length = 24 := hwf.deal_wf.2.1
  omega

theorem cursor_lt_53 {s : State} (hwf : s.WF) : s.stock.cursor < 53 := by
  have h1 : s.stock.cursor ≤ s.stock.cards.length := hwf.cursor_le
  have h2 := stockLen_le hwf
  omega

/-- The state's mixed-radix code, relative to the start state's stock
order: heights (radix 14, 4 suits), depths (radix 29, 7 piles),
cursor (radix 53), stock bits (radix 2, ≤ 52 positions — the filter
invariant pins the order), board tops (radix 53, 59 bases). -/
def stateEncAux (orig : List Card) (s : State) : Nat :=
  encF 14 Suit.all s.heights
    + 14 ^ 4 * (encF 29 Anchor.all s.depths
    + 29 ^ 7 * (s.stock.cursor
    + 53 * (encF 2 orig (stockBits s.stock.cards)
    + 2 ^ 52 * encF 53 Board.enumBase (fun b => optCode (s.board.topOf b)))))

theorem stateEnc_component_lt {ST s : State} (hwfST : ST.WF) (hok : traceOK ST s) :
    encF 14 Suit.all s.heights < 14 ^ 4 ∧
    encF 29 Anchor.all s.depths < 29 ^ 7 ∧
    s.stock.cursor < 53 ∧
    encF 2 ST.stock.cards (stockBits s.stock.cards) < 2 ^ 52 ∧
    encF 53 Board.enumBase (fun b => optCode (s.board.topOf b)) < 53 ^ 59 := by
  obtain ⟨-, -, hwf, -, -⟩ := hok
  refine ⟨?_, ?_, cursor_lt_53 hwf, ?_, ?_⟩
  · have h := encF_lt 14 Suit.all s.heights
      (fun x _ => heights_digit_lt hwf x)
    rw [show Suit.all.length = 4 by decide] at h
    exact h
  · have h := encF_lt 29 Anchor.all s.depths
      (fun x _ => depths_digit_lt hwf x)
    rw [show Anchor.all.length = 7 by decide] at h
    exact h
  · have h1 := encF_lt 2 ST.stock.cards (stockBits s.stock.cards)
      (fun x _ => stockBits_lt _ x)
    have h2 : ST.stock.cards.length ≤ 52 := by
      have := stockLen_le hwfST
      omega
    have h3 : (2 : Nat) ^ ST.stock.cards.length ≤ 2 ^ 52 :=
      Nat.pow_le_pow_right (by omega) h2
    omega
  · have h := encF_lt 53 Board.enumBase
      (fun b => optCode (s.board.topOf b)) (fun b _ => optCode_lt (s.board.topOf b))
    rw [Board.enumBase_length] at h
    exact h

theorem stateEnc_lt {ST s : State} (hwfST : ST.WF) (hok : traceOK ST s) :
    stateEncAux ST.stock.cards s < stateSpaceBound := by
  obtain ⟨bH, bD, bC, bK, bB⟩ := stateEnc_component_lt hwfST hok
  have e3 : encF 2 ST.stock.cards (stockBits s.stock.cards)
      + 2 ^ 52 * encF 53 Board.enumBase (fun b => optCode (s.board.topOf b))
      < 2 ^ 52 * 53 ^ 59 := nest_lt bK bB
  have e2 : s.stock.cursor + 53 * (encF 2 ST.stock.cards (stockBits s.stock.cards)
      + 2 ^ 52 * encF 53 Board.enumBase (fun b => optCode (s.board.topOf b)))
      < 53 * (2 ^ 52 * 53 ^ 59) := nest_lt bC e3
  have e1 : encF 29 Anchor.all s.depths + 29 ^ 7 * (s.stock.cursor
      + 53 * (encF 2 ST.stock.cards (stockBits s.stock.cards)
      + 2 ^ 52 * encF 53 Board.enumBase (fun b => optCode (s.board.topOf b))))
      < 29 ^ 7 * (53 * (2 ^ 52 * 53 ^ 59)) := nest_lt bD e2
  have e0 : encF 14 Suit.all s.heights + 14 ^ 4 * (encF 29 Anchor.all s.depths
      + 29 ^ 7 * (s.stock.cursor
      + 53 * (encF 2 ST.stock.cards (stockBits s.stock.cards)
      + 2 ^ 52 * encF 53 Board.enumBase (fun b => optCode (s.board.topOf b)))))
      < 14 ^ 4 * (29 ^ 7 * (53 * (2 ^ 52 * 53 ^ 59))) := nest_lt bH e1
  have hresh : 14 ^ 4 * (29 ^ 7 * (53 * (2 ^ 52 * 53 ^ 59))) = stateSpaceBound := by
    unfold stateSpaceBound
    simp only [Nat.mul_assoc]
  exact Nat.lt_of_lt_of_le e0 (Nat.le_of_eq hresh)

theorem stateEnc_inj {ST s1 s2 : State} (hwfST : ST.WF)
    (h1 : traceOK ST s1) (h2 : traceOK ST s2)
    (h : stateEncAux ST.stock.cards s1 = stateEncAux ST.stock.cards s2) : s1 = s2 := by
  obtain ⟨bH1, bD1, bC1, bK1, -⟩ := stateEnc_component_lt hwfST h1
  obtain ⟨bH2, bD2, bC2, bK2, -⟩ := stateEnc_component_lt hwfST h2
  obtain ⟨hdeal1, hstep1, hwf1, p1, hp1⟩ := h1
  obtain ⟨hdeal2, hstep2, hwf2, p2, hp2⟩ := h2
  unfold stateEncAux at h
  obtain ⟨hHeq, hR1⟩ := radix_peel (by omega) bH1 bH2 h
  obtain ⟨hDeq, hR2⟩ := radix_peel (by omega) bD1 bD2 hR1
  obtain ⟨hCeq, hR3⟩ := radix_peel (by omega) bC1 bC2 hR2
  obtain ⟨hKeq, hBeq⟩ := radix_peel (by omega) bK1 bK2 hR3
  have hheights : s1.heights = s2.heights :=
    funext (fun x => encF_inj 14 (by omega) Suit.all s1.heights s2.heights
      (fun y _ => heights_digit_lt hwf1 y) (fun y _ => heights_digit_lt hwf2 y) hHeq x
      (Suit.mem_all x))
  have hdepths : s1.depths = s2.depths :=
    funext (fun x => encF_inj 29 (by omega) Anchor.all s1.depths s2.depths
      (fun y _ => depths_digit_lt hwf1 y) (fun y _ => depths_digit_lt hwf2 y) hDeq x
      (Anchor.mem_all x))
  have hcards : s1.stock.cards = s2.stock.cards := by
    have hbits : ∀ x ∈ ST.stock.cards,
        stockBits s1.stock.cards x = stockBits s2.stock.cards x :=
      encF_inj 2 (by omega) ST.stock.cards (stockBits s1.stock.cards)
        (stockBits s2.stock.cards) (fun x _ => stockBits_lt _ x)
        (fun x _ => stockBits_lt _ x) hKeq
    have hfilt : ST.stock.cards.filter (fun x => decide (x ∈ s1.stock.cards))
        = ST.stock.cards.filter (fun x => decide (x ∈ s2.stock.cards)) :=
      List.filter_congr (fun x hx => stockBits_eq_decide (hbits x hx))
    exact (filter_mem_self hp1).trans (hfilt.trans (filter_mem_self hp2).symm)
  have hboard : s1.board = s2.board := by
    refine Board.ext_topOf (funext (fun b => ?_))
    exact optCode_inj (encF_inj 53 (by omega) Board.enumBase
      (fun b => optCode (s1.board.topOf b)) (fun b => optCode (s2.board.topOf b))
      (fun b _ => optCode_lt _) (fun b _ => optCode_lt _) hBeq b
      (Board.enumBase_complete b))
  have hstock : s1.stock = s2.stock := by
    show Cycle.mk s1.stock.cards s1.stock.cursor
      = Cycle.mk s2.stock.cards s2.stock.cursor
    rw [hcards, hCeq]
  have hdd : s1.deal = s2.deal := hdeal1.trans hdeal2.symm
  have hss : s1.drawStep = s2.drawStep := hstep1.trans hstep2.symm
  show State.mk s1.deal s1.board s1.heights s1.depths s1.stock s1.drawStep
    = State.mk s2.deal s2.board s2.heights s2.depths s2.stock s2.drawStep
  rw [hdd, hboard, hheights, hdepths, hstock, hss]

/-- A distinct, all-WF trace is at most `stateSpaceBound` long. -/
theorem trace_length_le {ST : State} (hwf : ST.WF) {play : List Move} {w : State}
    (hrun : ST.run play = some w) (hdist : allDistinct (ST.trace play)) :
    (ST.trace play).length ≤ stateSpaceBound := by
  have hok : ∀ s ∈ ST.trace play, traceOK ST s :=
    trace_traceOK ST play ST w (traceOK_self hwf) hrun
  have hmap : allDistinct ((ST.trace play).map (stateEncAux ST.stock.cards)) :=
    allDistinct_map (stateEncAux ST.stock.cards) hdist
      (fun x hx y hy h => stateEnc_inj hwf (hok x hx) (hok y hy) h)
  have hmem : ∀ v ∈ (ST.trace play).map (stateEncAux ST.stock.cards),
      v < stateSpaceBound := by
    intro v hv
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hv
    exact stateEnc_lt hwf (hok s hs)
  have hlm : ((ST.trace play).map (stateEncAux ST.stock.cards)).length
      = (ST.trace play).length := List.length_map _
  rw [← hlm]
  exact distinct_nat_count_le _ stateSpaceBound hmap hmem

/-- **Decidability of the verdict**: solvability is witnessed by a
bounded play — cut every loop (`play_cut_loop`); a loop-free play
visits each distinct state at most once (the codes are distinct and
below `stateSpaceBound`), so its length is at most the state space. -/
theorem solvable_iff_boundedPlay {st : State} (hwf : st.WF) :
    st.solvableFrom ↔ ∃ play w, st.run play = some w ∧ w.isWin = true ∧
      play.length ≤ stateSpaceBound := by
  constructor
  · intro hsol
    obtain ⟨play, w, hrun, hwin, hdist⟩ := (solvable_iff_distinctTrace hwf).mp hsol
    have hcount := trace_length_le hwf hrun hdist
    have hlen := trace_length_succ play st w hrun
    refine ⟨play, w, hrun, hwin, ?_⟩
    omega
  · intro hbound
    obtain ⟨play, w, hrun, hwin, -⟩ := hbound
    exact ⟨play, w, hrun, hwin⟩

/-- The verdict is decidable: exhaustive search over bounded plays. -/
theorem solvable_decidable (st : State) (hwf : st.WF) :
    st.solvableFrom ∨ ¬ st.solvableFrom := by
  by_cases hb : ∃ play w, st.run play = some w ∧ w.isWin = true ∧
    play.length ≤ stateSpaceBound
  · exact Or.inl ((solvable_iff_boundedPlay hwf).mpr hb)
  · refine Or.inr (fun hsol => ?_)
    exact hb ((solvable_iff_boundedPlay hwf).mp hsol)
