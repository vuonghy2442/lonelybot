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
