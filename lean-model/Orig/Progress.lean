import Orig.Reach
import Orig.Encode
import Orig.Fate

/-!
# Orig.Progress — the bounded-play spine

The chapter's strongest global theorem, ported to the `Orig` game:
winning needs only a play shorter than the state space, and the
verdict is constructively decidable at every dealt-and-played
position.

The spine, in its four installments:

* *loop-cutting* (`play_cut_loop`) — pure run determinism: a winning
  play that revisits a state along the way can be cut at the repeat.
  No `WF`, no finiteness, no classical reasoning anywhere; the cut is
  `State.run`'s functional shape (`State.run_cons` / `run_split`).
* *the distinct-trace corollary* (`win_iff_distinctTrace`) — every
  winning play reshapes into one whose trace never revisits a
  state.  The repeat is located by a total scanner (`repPair?`)
  over a Boolean state equality (`stateEqb`), so the extraction the
  old chapter took by classical contradiction is here constructive
  data — the scanner either certifies distinctness or hands back
  indices to cut at.
* *the encode consumption* (`distinct_trace_bound`) — a pairwise
  distinct trace out of a `WF` start with the honest digit premise
  `st.drawStep < 53` has one state per code below
  `State.stateSpaceBound` (the pigeonhole of `Orig.Encode`), so it
  is shorter than the state space.
* *the assembly* (`boundedPlay`, `winFrom_em`) — the iff: `WinFrom`
  iff a win exists within `play.length < State.stateSpaceBound`;
  and the verdict's constructive excluded middle by a total
  bounded-DFS `Bool` over that depth.  The reachability bridge
  (`initialReachable_wf`, cited from `Orig.Reach`) carries both to
  every dealt-and-played state, the deal's draw step as the honest
  parameter premise.

Axiom discipline: `[propext, Quot.sound]` targets only, per-lemma
`#print axioms` audits.  The house's recorded choice-draggers are
avoided structurally: no classical `by_cases`, no unguarded `simp`
proof-shaping — match splits by `cases` on the deciding `Bool` or
`Option`, absurdity explicit, `omega` only on `Nat` goals.  One
core kit lemma (`List.take_add`) was found by audit to drag
`Classical.choice`; it is replaced by a private induction copy
(`take_split`).
-/

set_option maxRecDepth 2048
set_option maxHeartbeats 1000000

/-! ## The private run kit -/

/-- No option equals nothing and something at once — the constructor
inversion the dead-step branches close by. -/
private theorem none_eq_some_false {α : Type} {a : α}
    (h : (none : Option α) = some a) : False := by
  cases h

/-- No list equals a cons and nil at once. -/
private theorem cons_eq_nil_false {α : Type} {y : α} {t : List α}
    (h : (y :: t : List α) = []) : False := by
  cases h

/-- Composing one verified step with a verified rest play (the
constructor direction of `State.run_cons`). -/
private theorem run_cons_of {st : State} {m : Move} {s₁ : State}
    (hstep : State.step st m = some s₁)
    {ms : List Move} {w : State} (hrest : s₁.run ms = some w) :
    st.run (m :: ms) = some w := by
  show (match State.step st m with
    | some st' => st'.run ms
    | none => none) = some w
  rw [hstep]
  exact hrest

/-- The elimination direction of `run` over an append: a successful
run through `A ++ B` passes through the state `A` lands on. -/
private theorem run_append_elim : ∀ (A : List Move) (st : State) (w : State)
    (B : List Move), st.run (A ++ B) = some w →
    ∃ s, st.run A = some s ∧ s.run B = some w := by
  intro A
  induction A with
  | nil =>
      intro st w B h
      exact ⟨st, rfl, h⟩
  | cons m t ih =>
      intro st w B h
      rw [List.cons_append] at h
      obtain ⟨s₁, hstep, hrest⟩ := State.run_cons h
      obtain ⟨s, hA, hB⟩ := ih s₁ w B hrest
      exact ⟨s, run_cons_of hstep hA, hB⟩

/-- `take` at a split index (isolation copy of the core kit's
`take_add`, whose proof drags `Classical.choice` — the audit's one
recorded substitution). -/
private theorem take_split {α : Type} (l : List α) (i j : Nat) :
    l.take (i + j) = l.take i ++ (l.drop i).take j := by
  induction i generalizing l with
  | zero =>
      rw [List.take_zero, List.drop_zero, Nat.zero_add, List.nil_append]
  | succ i ih =>
      cases l with
      | nil =>
          have h1 : List.take (i + 1 + j) ([] : List α) = [] := List.take_nil
          have h2 : List.take (i + 1) ([] : List α) = [] := List.take_nil
          have h3 : List.drop (i + 1) ([] : List α) = [] := List.drop_nil
          have h4 : List.take j ([] : List α) = [] := List.take_nil
          rw [h1, h2, h3, h4, List.nil_append]
      | cons y t =>
          have h1 : (y :: t).take (i + 1 + j) = (y :: t).take (i + j + 1) := by
            rw [show i + 1 + j = i + j + 1 from Nat.add_right_comm _ 1 _]
          have h2 := List.take_succ_cons (a := y) (as := t) (i := i + j)
          have h3 := List.take_succ_cons (a := y) (as := t) (i := i)
          have h4 := List.drop_succ_cons (a := y) (l := t) (i := i)
          rw [h1, h2, h3, h4, List.cons_append]
          exact congrArg (y :: ·) (ih t)

/-! ## The play trace -/

/-- The states a play passes through from `st`: the start state, then
one state per move as it is played. -/
def playTrace (st : State) : List Move → List State
  | [] => [st]
  | m :: ms =>
      match State.step st m with
      | none => []
      | some s' => st :: playTrace s' ms

private theorem playTrace_stepNone {st : State} {m : Move} {ms : List Move}
    (h : State.step st m = none) : playTrace st (m :: ms) = [] := by
  rw [playTrace, h]

private theorem playTrace_stepCons {st : State} {m : Move} {ms : List Move}
    {s' : State} (h : State.step st m = some s') :
    playTrace st (m :: ms) = st :: playTrace s' ms := by
  rw [playTrace, h]

/-- A successful play's trace has one state per move, plus the
start. -/
private theorem trace_length_succ : ∀ (play : List Move) (st w : State),
    st.run play = some w → (playTrace st play).length = play.length + 1 := by
  intro play
  induction play with
  | nil => intro st w _h; rfl
  | cons m ms ih =>
      intro st w h
      obtain ⟨s', hstep, hrest⟩ := State.run_cons h
      rw [playTrace_stepCons hstep, List.length_cons,
        show (m :: ms).length = ms.length + 1 from rfl]
      exact congrArg (· + 1) (ih s' w hrest)

/-- The trace's `i`-th state is where the first `i` moves land. -/
private theorem run_take_trace : ∀ (play : List Move) (st w : State),
    st.run play = some w → ∀ i, i ≤ play.length →
    st.run (play.take i) = (playTrace st play)[i]? := by
  intro play
  induction play with
  | nil =>
      intro st w h i hi
      cases i with
      | zero => rfl
      | succ k =>
          have hl : ([] : List Move).length = 0 := rfl
          rw [hl] at hi
          exact absurd hi (by omega)
  | cons m ms ih =>
      intro st w h i hi
      obtain ⟨s', hstep, hrest⟩ := State.run_cons h
      cases i with
      | zero =>
          rw [playTrace_stepCons hstep]
          rfl
      | succ k =>
          rw [playTrace_stepCons hstep, List.getElem?_cons_succ]
          have hl : (m :: ms).length = ms.length + 1 := rfl
          rw [hl] at hi
          have hk : k ≤ ms.length := by omega
          have htak : (m :: ms).take (k + 1) = m :: ms.take k :=
            List.take_succ_cons
          rw [htak]
          have hrw : st.run (m :: ms.take k) = s'.run (ms.take k) := by
            rw [show st.run (m :: ms.take k) = (match State.step st m with
              | some st' => st'.run (ms.take k)
              | none => none) from rfl, hstep]
          rw [hrw]
          exact ih s' w hrest k hk

/-! ## Loop-cutting (M1) -/

/-- **Loop-cutting**: runs are state-deterministic, so any segment of
a winning play that returns to its own start contributes nothing —
cutting the loop out preserves the destination and the win.  Pure
`State.run` determinism (`State.run_cons`, `run_split`); no `WF`, no
finiteness. -/
theorem play_cut_loop {st : State} {π₁ π₂ π₃ : List Move} {w : State}
    (hwin : st.run (π₁ ++ (π₂ ++ π₃)) = some w ∧ w.isWin = true)
    (hrep : ∃ s, st.run π₁ = some s ∧ s.run π₂ = some s) :
    st.run (π₁ ++ π₃) = some w ∧ w.isWin = true := by
  obtain ⟨s₀, hr₀, hr₂⟩ := hrep
  obtain ⟨hw, hwinw⟩ := hwin
  refine ⟨?_, hwinw⟩
  -- split off the outermost segment: `π₁`, then `π₂ ++ π₃`
  obtain ⟨s, hr₁, hrest⟩ := run_append_elim π₁ st w (π₂ ++ π₃) hw
  have hes : s = s₀ := Option.some.inj (hr₁.symm.trans hr₀)
  rw [hes] at hrest
  -- the middle pocket: `π₂` lands back where it started
  obtain ⟨s₂, h₂, h₃⟩ := run_append_elim π₂ s₀ w π₃ hrest
  have hes₂ : s₂ = s₀ := Option.some.inj (h₂.symm.trans hr₂)
  rw [hes₂] at h₃
  exact run_split π₁ st s₀ π₃ w hr₀ h₃

/-! ## The state scanner

The distinct-trace corollary needs to locate a repeated state in a
trace, or certify that none exists — constructively.  The scan is
data: a Boolean state equality, a positional search over the
already-seen prefix, and a front-to-back walk that hands back the
first repeat with both positions. -/

/-- Decidable state equality as data: both sides agree on every
suit's foundation, every pile, both zones, and the draw step. -/
private def stateEqb (s₁ s₂ : State) : Bool :=
  (Suit.all.all fun σ => decide (s₁.found σ = s₂.found σ)) &&
  ((Anchor.all.all fun a => decide (s₁.piles a = s₂.piles a)) &&
  (decide (s₁.stock = s₂.stock) &&
  (decide (s₁.waste = s₂.waste) &&
  decide (s₁.drawStep = s₂.drawStep))))

private theorem stateEqb_refl (s : State) : stateEqb s s = true := by
  have hF : (Suit.all.all fun σ => decide (s.found σ = s.found σ)) = true :=
    List.all_eq_true.mpr fun σ _ => decide_eq_true rfl
  have hP : (Anchor.all.all fun a => decide (s.piles a = s.piles a)) = true :=
    List.all_eq_true.mpr fun a _ => decide_eq_true rfl
  have hSt : decide (s.stock = s.stock) = true := decide_eq_true rfl
  have hW : decide (s.waste = s.waste) = true := decide_eq_true rfl
  have hD : decide (s.drawStep = s.drawStep) = true := decide_eq_true rfl
  rw [stateEqb, hF, hP, hSt, hW, hD]
  rfl

private theorem stateEqb_of_eq {x y : State} (h : x = y) : stateEqb x y = true := by
  subst h
  exact stateEqb_refl _

private theorem stateEqb_eq {s₁ s₂ : State} (h : stateEqb s₁ s₂ = true) : s₁ = s₂ := by
  rw [stateEqb, Bool.and_eq_true] at h
  obtain ⟨hF, hP⟩ := h
  rw [Bool.and_eq_true] at hP
  obtain ⟨hPa, hSW⟩ := hP
  rw [Bool.and_eq_true] at hSW
  obtain ⟨hSt, hW⟩ := hSW
  rw [Bool.and_eq_true] at hW
  obtain ⟨hWa, hD⟩ := hW
  have hf : s₁.found = s₂.found :=
    funext fun σ => of_decide_eq_true (List.all_eq_true.mp hF σ (Suit.mem_all σ))
  have hp : s₁.piles = s₂.piles :=
    funext fun a => of_decide_eq_true (List.all_eq_true.mp hPa a (Anchor.mem_all a))
  have hsto : s₁.stock = s₂.stock := of_decide_eq_true hSt
  have hwa : s₁.waste = s₂.waste := of_decide_eq_true hWa
  have hd : s₁.drawStep = s₂.drawStep := of_decide_eq_true hD
  show State.mk s₁.found s₁.piles s₁.stock s₁.waste s₁.drawStep
      = State.mk s₂.found s₂.piles s₂.stock s₂.waste s₂.drawStep
  rw [hf, hp, hsto, hwa, hd]

private theorem stateEqb_refute {x y : State} (hxy : x ≠ y)
    (hb : stateEqb x y = true) : False := hxy (stateEqb_eq hb)

/-- The first index of `x` in `l`, compared by `stateEqb`. -/
private def posOf? (x : State) : List State → Option Nat
  | [] => none
  | y :: t =>
      match stateEqb x y with
      | true => some 0
      | false =>
          match posOf? x t with
          | some k => some (k + 1)
          | none => none

private theorem posOf?_eq_zero {x y : State} (hxy : x = y) (t : List State) :
    posOf? x (y :: t) = some 0 := by
  rw [posOf?, stateEqb_of_eq hxy]

private theorem posOf?_some {x y : State} (hxy : x ≠ y) {t : List State} {k : Nat}
    (h : posOf? x t = some k) : posOf? x (y :: t) = some (k + 1) := by
  have hb : stateEqb x y = false := by
    cases hcon : stateEqb x y with
    | true => exact absurd hcon (fun hc => stateEqb_refute hxy hc)
    | false => rfl
  rw [posOf?, hb, h]

private theorem posOf?_lt {x : State} : ∀ (l : List State) (j : Nat),
    posOf? x l = some j → j < l.length := by
  intro l
  induction l with
  | nil =>
      intro j h
      rw [show posOf? x [] = none from rfl] at h
      exact absurd h none_eq_some_false
  | cons y t ih =>
      intro j h
      rw [posOf?] at h
      cases hb : stateEqb x y with
      | true =>
          rw [hb] at h
          have hj : j = 0 := (Option.some.inj h).symm
          subst hj
          have hl : (y :: t).length = t.length + 1 := by rw [List.length_cons]
          omega
      | false =>
          rw [hb] at h
          cases hrest : posOf? x t with
          | none =>
              rw [hrest] at h
              exact absurd h none_eq_some_false
          | some k =>
              rw [hrest] at h
              have hj : j = k + 1 := (Option.some.inj h).symm
              subst hj
              have hik := ih k hrest
              have hl : (y :: t).length = t.length + 1 := by rw [List.length_cons]
              omega

private theorem posOf?_get {x : State} : ∀ (l : List State) (j : Nat),
    posOf? x l = some j → l[j]? = some x := by
  intro l
  induction l with
  | nil =>
      intro j h
      rw [show posOf? x [] = none from rfl] at h
      exact absurd h none_eq_some_false
  | cons y t ih =>
      intro j h
      rw [posOf?] at h
      cases hb : stateEqb x y with
      | true =>
          rw [hb] at h
          have hj : j = 0 := (Option.some.inj h).symm
          subst hj
          have hxeq : x = y := stateEqb_eq hb
          rw [hxeq]
          rfl
      | false =>
          rw [hb] at h
          cases hrest : posOf? x t with
          | none =>
              rw [hrest] at h
              exact absurd h none_eq_some_false
          | some k =>
              rw [hrest] at h
              have hj : j = k + 1 := (Option.some.inj h).symm
              subst hj
              rw [List.getElem?_cons_succ]
              exact ih k hrest

private theorem posOf?_ne_none {x : State} : ∀ (l : List State), x ∈ l →
    posOf? x l ≠ none := by
  intro l
  induction l with
  | nil => intro h; exact absurd h List.not_mem_nil
  | cons y t ih =>
      intro h
      cases hb : stateEqb x y with
      | true =>
          intro hcon
          rw [posOf?_eq_zero (stateEqb_eq hb) t] at hcon
          exact absurd hcon.symm none_eq_some_false
      | false =>
          intro hcon
          rw [posOf?] at hcon
          rw [hb] at hcon
          cases hrest : posOf? x t with
          | none =>
              rcases List.mem_cons.mp h with hxy | ht
              · have hc : stateEqb x y = true := by
                  rw [hxy]
                  exact stateEqb_refl y
                rw [hb] at hc
                exact Bool.noConfusion hc
              · exact ih ht hrest
          | some k =>
              rw [hrest] at hcon
              exact absurd hcon.symm none_eq_some_false

/-- Appending a fresh entry to a distinct list keeps it distinct. -/
private theorem allDistinct_snoc {seen : List State} {x : State}
    (hdist : allDistinct seen) (hx : x ∉ seen) : allDistinct (seen ++ [x]) := by
  have hlenL : (seen ++ [x]).length = seen.length + 1 := by
    rw [List.length_append, List.length_cons, List.length_nil]
  have hend : (seen ++ [x])[seen.length]? = some x := by
    rw [getElem?_appendR seen [x] seen.length (Nat.le_refl seen.length),
      Nat.sub_self]
    rfl
  intro i j hi hj heq
  rcases Nat.lt_or_ge j seen.length with hjl | hjge
  · rcases Nat.lt_or_ge i seen.length with hil | hige
    · have himemi : (seen ++ [x])[i]? = seen[i]? := getElem?_appendL _ _ i hil
      have himemj : (seen ++ [x])[j]? = seen[j]? := getElem?_appendL _ _ j hjl
      rw [himemi, himemj] at heq
      exact hdist i j hil hjl heq
    · have hie : i = seen.length := by omega
      rw [hie, hend] at heq
      have himemj : (seen ++ [x])[j]? = seen[j]? := getElem?_appendL _ _ j hjl
      rw [himemj] at heq
      exact absurd (List.mem_iff_getElem?.mpr ⟨j, heq.symm⟩) hx
  · have hje : j = seen.length := by omega
    rcases Nat.lt_or_ge i seen.length with hil | hige
    · have himemi : (seen ++ [x])[i]? = seen[i]? := getElem?_appendL _ _ i hil
      rw [hje, hend] at heq
      rw [himemi] at heq
      exact absurd (List.mem_iff_getElem?.mpr ⟨i, heq⟩) hx
    · have hie : i = seen.length := by omega
      exact hie.trans hje.symm

/-- The repeat walk: scan the trace front to back against the entries
already seen (in order); the first entry that occurred before hands
back the repeated state with the earlier and the later position. -/
private def repScan? : List State → List State → Option ((State × Nat) × Nat)
  | [], _ => none
  | x :: t, seen =>
      match posOf? x seen with
      | some i => some ((x, i), seen.length)
      | none => repScan? t (seen ++ [x])

private theorem repScan?_none : ∀ (l seen : List State), allDistinct seen →
    repScan? l seen = none → allDistinct (seen ++ l) := by
  intro l
  induction l with
  | nil =>
      intro seen hseen _h
      rw [List.append_nil]
      exact hseen
  | cons x t ih =>
      intro seen hseen h
      rw [repScan?] at h
      cases hp : posOf? x seen with
      | some i =>
          rw [hp] at h
          exact absurd (show none = some ((x, i), seen.length) from h.symm)
            none_eq_some_false
      | none =>
          rw [hp] at h
          have hseen' : allDistinct (seen ++ [x]) :=
            allDistinct_snoc hseen (fun hmem => posOf?_ne_none seen hmem hp)
          have hrec := ih (seen ++ [x]) hseen' h
          rw [List.append_assoc] at hrec
          exact hrec

private theorem repScan?_spec : ∀ (l seen : List State) (x : State) (i j : Nat),
    repScan? l seen = some ((x, i), j) →
    i < j ∧ j < (seen ++ l).length ∧
      (seen ++ l)[i]? = some x ∧ (seen ++ l)[j]? = some x := by
  intro l
  induction l with
  | nil =>
      intro seen x i j h
      rw [show repScan? [] seen = none from rfl] at h
      exact absurd h none_eq_some_false
  | cons y t ih =>
      intro seen x i j h
      rw [repScan?] at h
      cases hp : posOf? y seen with
      | some k =>
          rw [hp] at h
          have htrip : ((y, k), seen.length) = ((x, i), j) := Option.some.inj h
          obtain ⟨h1, h2⟩ := Prod.mk.inj htrip
          obtain ⟨h3, h4⟩ := Prod.mk.inj h1
          have hik := posOf?_lt seen k hp
          have hget := posOf?_get seen k hp
          rw [← h4, ← h2, ← h3]
          refine ⟨hik, ?_, ?_, ?_⟩
          · have hl : (seen ++ y :: t).length = seen.length + (y :: t).length :=
              List.length_append
            have hyt : (y :: t).length = t.length + 1 := by rw [List.length_cons]
            omega
          · rw [getElem?_appendL seen (y :: t) k hik]
            exact hget
          · rw [getElem?_appendR seen (y :: t) seen.length
              (Nat.le_refl seen.length), Nat.sub_self]
            rfl
      | none =>
          rw [hp] at h
          have hrec := ih (seen ++ [y]) x i j h
          rw [List.append_assoc] at hrec
          exact hrec

/-- The repeat search over a whole trace: `none` certifies pairwise
distinctness; `some ((x, i), j)` exhibits a repeat with positions. -/
private def repPair? (l : List State) : Option ((State × Nat) × Nat) :=
  repScan? l []

private theorem repPair?_none {l : List State} (h : repPair? l = none) :
    allDistinct l :=
  repScan?_none l [] (fun i _ hi _ _ => absurd hi (Nat.not_lt_zero i)) h

private theorem repPair?_spec {l : List State} {x : State} {i j : Nat}
    (h : repPair? l = some ((x, i), j)) :
    i < j ∧ j < l.length ∧ l[i]? = some x ∧ l[j]? = some x :=
  repScan?_spec l [] x i j h

/-! ## The distinct-trace corollary -/

/-- Loop-cutting terminates: a winning play of length bounded by `n`
yields a winning play of strictly shorter length whenever a repeat
exists, so strong induction bottoms out in a winning play with a
pairwise distinct trace. -/
private theorem win_distinct_aux : ∀ (n : Nat) (st : State) (play : List Move)
    (w : State), play.length ≤ n → st.run play = some w → w.isWin = true →
    ∃ play' w', st.run play' = some w' ∧ w'.isWin = true ∧
      allDistinct (playTrace st play') := by
  intro n
  induction n with
  | zero =>
      intro st play w hlen hrun hwin
      cases play with
      | nil =>
          have he : st = w := Option.some.inj hrun
          subst he
          refine ⟨[], st, rfl, hwin, ?_⟩
          have ht : playTrace st [] = [st] := rfl
          rw [ht]
          intro i j hi hj _
          have hl : ([st] : List State).length = 1 := rfl
          omega
      | cons m ms =>
          have hl : (m :: ms).length = ms.length + 1 := rfl
          rw [hl] at hlen
          exact absurd hlen (by omega)
  | succ n ih =>
      intro st play w hlen hrun hwin
      cases hscan : repPair? (playTrace st play) with
      | none =>
          exact ⟨play, w, hrun, hwin, repPair?_none hscan⟩
      | some tri =>
          obtain ⟨⟨x, i⟩, j⟩ := tri
          obtain ⟨hij, hjlen, hgeti, hgetj⟩ :=
            repPair?_spec (l := playTrace st play) hscan
          have htrlen := trace_length_succ play st w hrun
          have hjle : j ≤ play.length := by omega
          have hile : i ≤ play.length := by omega
          have hri : st.run (play.take i) = some x := by
            rw [run_take_trace play st w hrun i hile]
            exact hgeti
          have hrj : st.run (play.take j) = some x := by
            rw [run_take_trace play st w hrun j hjle]
            exact hgetj
          have hsplit : play.take j = play.take i ++ (play.drop i).take (j - i) := by
            have hts := take_split play i (j - i)
            have hij2 : i + (j - i) = j := by omega
            rw [hij2] at hts
            exact hts
          have hmid : x.run ((play.drop i).take (j - i)) = some x := by
            obtain ⟨s'', hA, hB⟩ :=
              run_append_elim (play.take i) st x ((play.drop i).take (j - i))
                (by rw [← hsplit]; exact hrj)
            have hsx : s'' = x := Option.some.inj (hA.symm.trans hri)
            subst hsx
            exact hB
          have hwhole : play.take i ++ ((play.drop i).take (j - i) ++ play.drop j)
              = play := by
            rw [← List.append_assoc, ← hsplit, List.take_append_drop]
          obtain ⟨hcutrun, hcutwin⟩ :=
            play_cut_loop (π₁ := play.take i)
              (π₂ := (play.drop i).take (j - i)) (π₃ := play.drop j)
              ⟨by rw [hwhole]; exact hrun, hwin⟩ ⟨x, hri, hmid⟩
          have hnewlen : (play.take i ++ play.drop j).length < play.length := by
            have hL : (play.take i ++ play.drop j).length
                = (play.take i).length + (play.drop j).length := List.length_append
            have h1 : (play.take i).length = min i play.length := List.length_take
            have hmin : (play.take i).length = i := by
              rw [h1]
              exact Nat.min_eq_left hile
            have h2 : (play.drop j).length = play.length - j := List.length_drop
            omega
          have hlen' : (play.take i ++ play.drop j).length ≤ n := by omega
          exact ih st (play.take i ++ play.drop j) w hlen' hcutrun hcutwin

/-- **The distinct-trace corollary**: any winning play reshapes into
one whose trace never revisits a state.  No `WF`, no finiteness —
`play_cut_loop` until the scanner certifies no repeat remains. -/
theorem win_iff_distinctTrace {st : State} :
    WinFrom st ↔ ∃ play w, st.run play = some w ∧ w.isWin = true ∧
      allDistinct (playTrace st play) := by
  constructor
  · intro hwin
    obtain ⟨play, w, hrun, hwinw⟩ := hwin
    exact win_distinct_aux play.length st play w (Nat.le_refl _) hrun hwinw
  · intro h
    obtain ⟨play, w, hrun, hwinw, -⟩ := h
    exact ⟨play, w, hrun, hwinw⟩
