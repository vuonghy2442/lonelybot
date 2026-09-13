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

/-- The commitment application from a (already accommodated) state.

Statement repair (2026-09-13, this agent — orchestrator sign-off
pending): the tableau disjunct gained `st.canPlace c b = true`.
`State.applyDrawTo`'s own guard is the accessible-set jump plus
`Board.attach` (base free, card unplaced) — it does *not* check the
landing rule — so without the conjunct the macro game admitted Draw
commitments whose successor no play can ever produce: every
edge-creating move (`deckPile`, `stackPile`, `pilePile`) demands
`canPlace`, whose tableau half (`canSitOn` / king) is pure and
state-independent, and `reveal` attaches only hidden deal cards.
Prover-confirmed witness: ♠7 visible as pile 0's sole card, ♥5 the
last stock card at the pass-end cursor (so reachable), base `inr ♠7`:
`canSitOn ♥5 ♠7 = false` (5 ≠ 7−1), `applyDrawTo` succeeds, and every
move except `.draw` is illegal from the state. -/
def commitApplies (st : State) (k : MacroMove) (st'' : State) : Prop :=
  match k with
  | .drawCommit c =>
      ∃ b : Base, (st.canPlace c b = true ∧ st.applyDrawTo c b = some st'')
        ∨ st.applyDrawStackTo c = some st''
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

/-- **The one-step simulation, macro level**: the commitment-game
form of Progress.lean's `solvable_of_simulates` — if `R` relates the
two states and every `b`-side commitment is matched on the `a` side
(landing equal or `R`-related), wins lift.  This is the parent
`pace_dominance` instantiates. -/
theorem macroSolvable_of_simulates {a b : State} (R : State → State → Prop)
    (hR : R a b)
    (hstep : ∀ x y k b', R x y → macroStep y k b' →
      ∃ k' a', macroStep x k' a' ∧ (a' = b' ∨ R a' b'))
    (hwin : ∀ x y, R x y → y.isWin = true → x.isWin = true)
    (hsol : b.macroSolvable) : a.macroSolvable := by
  obtain ⟨ks, w, hsteps, hwinw⟩ := hsol
  have main : ∀ (x y : State) (ks : List MacroMove), R x y →
      macroSteps y ks w → w.isWin = true →
      ∃ ks' w', macroSteps x ks' w' ∧ w'.isWin = true := by
    intro x y ks hRxy
    induction ks generalizing x y with
    | nil =>
        intro hsteps hwin'
        have hyw : y = w := hsteps
        rw [← hyw] at hwin'
        exact ⟨[], x, rfl, hwin x y hRxy hwin'⟩
    | cons k krest ih =>
        intro hsteps hwin'
        obtain ⟨st'', hstep'', hrest⟩ := hsteps
        obtain ⟨k', a', ha', hcase⟩ := hstep x y k st'' hRxy hstep''
        rcases hcase with rfl | hR'
        · exact ⟨k' :: krest, w, ⟨a', ha', hrest⟩, hwin'⟩
        · obtain ⟨ks'', w'', hsteps'', hwin''⟩ := ih a' st'' hR' hrest hwin'
          exact ⟨k' :: ks'', w'', ⟨a', ha', hsteps''⟩, hwin''⟩
  obtain ⟨ks', w', hsteps', hwin'⟩ := main a b ks hR hsteps hwinw
  exact ⟨ks', w', hsteps', hwin'⟩

/-! ## The draw-decomposition toolkit

The pieces `macroStep_engine_play` and `drawTo_tableau_outcomes_agree`
are built from: the `reachablePos` / `applyDrawTo` / `applyDrawStackTo`
shape lemmas, the deal iteration `Cycle.dealN` with its orbit
correspondence (every accessible position is reached by pure deals —
the witness half of `applyDrawTo_eq_dealPlay`, with `posOf`'s range
bound standing in for the WF cursor invariant), and the after-deals
deck moves. -/

/-- `k` deals from `cy`. -/
def Cycle.dealN (s : Nat) : Nat → Cycle Card → Cycle Card
  | 0, cy => cy
  | k + 1, cy => dealOnce s (dealN s k cy)

theorem Cycle.dealN_zero (s : Nat) (cy : Cycle Card) : dealN s 0 cy = cy := rfl

theorem Cycle.dealN_succ (s : Nat) (k : Nat) (cy : Cycle Card) :
    dealN s (k + 1) cy = dealOnce s (dealN s k cy) := rfl

theorem Cycle.dealN_one (s : Nat) (cy : Cycle Card) :
    dealN s 1 cy = dealOnce s cy := rfl

theorem Cycle.dealN_add (s : Nat) : ∀ (k j : Nat) (cy : Cycle Card),
    dealN s (k + j) cy = dealN s k (dealN s j cy) := by
  intro k
  induction k with
  | zero => intro j cy; rw [Nat.zero_add, dealN_zero]
  | succ k ih =>
    intro j cy
    rw [Nat.succ_add, dealN_succ, dealN_succ, ih]

theorem Cycle.dealN_shift (s : Nat) : ∀ (k : Nat) (cy : Cycle Card),
    dealN s k (dealOnce s cy) = dealOnce s (dealN s k cy) := by
  intro k
  induction k with
  | zero => intro cy; rfl
  | succ k ih => intro cy; rw [dealN_succ, ih, ← dealN_succ]

/-- A zero residue witnesses the multiple. -/
theorem exists_mul_of_mod_zero {a s : Nat} (hmod : a % s = 0) : ∃ q, a = q * s := by
  refine ⟨a / s, ?_⟩
  have hdiv := Nat.div_add_mod a s
  rw [hmod, Nat.add_zero] at hdiv
  rw [Nat.mul_comm]
  exact hdiv.symm

/-- The current-pass advance: `q` deals from `c` land exactly at
`c + q·s` whenever that stays within the length (no clamp, no wrap). -/
theorem dealOnce_iterate_add {s : Nat} (hs : 0 < s) (l : List Card) :
    ∀ (q c : Nat), c + q * s ≤ l.length →
      Cycle.dealN s q ⟨l, c⟩ = ⟨l, c + q * s⟩ := by
  intro q
  induction q with
  | zero => intro c _; rw [Nat.zero_mul, Nat.add_zero]; rfl
  | succ q ih =>
    intro c hle
    have hexp : (q + 1) * s = q * s + s := by rw [Nat.add_mul, Nat.one_mul]
    rw [hexp] at hle
    have hstep : Cycle.dealOnce s ⟨l, c⟩ = ⟨l, c + s⟩ := by
      show (if c ≥ l.length then (⟨l, 0⟩ : Cycle Card) else ⟨l, min (c + s) l.length⟩)
          = (⟨l, c + s⟩ : Cycle Card)
      rw [if_neg (by omega), Nat.min_eq_left (by omega)]
    rw [Cycle.dealN_succ, ← Cycle.dealN_shift, hstep, ih (c + s) (by omega), hexp]
    exact congrArg (Cycle.mk l) (by omega)

/-- Every cursor reaches the pass end: the chain of clamped deals. -/
theorem dealOnce_reach_end {s : Nat} (hs : 0 < s) (l : List Card) :
    ∀ (d c : Nat), c ≤ l.length → l.length - c ≤ d →
      ∃ k, Cycle.dealN s k ⟨l, c⟩ = ⟨l, l.length⟩ := by
  intro d
  induction d with
  | zero =>
    intro c _ hd
    have hc : c = l.length := by omega
    subst hc
    exact ⟨0, rfl⟩
  | succ d ih =>
    intro c _ hd
    by_cases hc : c = l.length
    · subst hc; exact ⟨0, rfl⟩
    · by_cases hcs : c + s < l.length
      · have hstep : Cycle.dealOnce s ⟨l, c⟩ = ⟨l, c + s⟩ := by
          show (if c ≥ l.length then (⟨l, 0⟩ : Cycle Card) else ⟨l, min (c + s) l.length⟩)
              = (⟨l, c + s⟩ : Cycle Card)
          rw [if_neg (by omega), Nat.min_eq_left (by omega)]
        obtain ⟨k, hk⟩ := ih (c + s) (by omega) (by omega)
        refine ⟨k + 1, ?_⟩
        rw [Cycle.dealN_succ, ← Cycle.dealN_shift, hstep]
        exact hk
      · have hstep : Cycle.dealOnce s ⟨l, c⟩ = ⟨l, l.length⟩ := by
          show (if c ≥ l.length then (⟨l, 0⟩ : Cycle Card) else ⟨l, min (c + s) l.length⟩)
              = (⟨l, l.length⟩ : Cycle Card)
          rw [if_neg (by omega), Nat.min_eq_right (by omega)]
        exact ⟨1, hstep⟩

/-- The pass end is reached from any cursor, even past it (one wrap). -/
theorem dealOnce_reach_end_any {s : Nat} (hs : 0 < s) (l : List Card) (c : Nat) :
    ∃ k, Cycle.dealN s k ⟨l, c⟩ = ⟨l, l.length⟩ := by
  by_cases hcl : c ≤ l.length
  · exact dealOnce_reach_end hs l (l.length - c) c hcl (by omega)
  · have hwrap : Cycle.dealOnce s ⟨l, c⟩ = ⟨l, 0⟩ := by
      show (if c ≥ l.length then (⟨l, 0⟩ : Cycle Card) else ⟨l, min (c + s) l.length⟩)
          = (⟨l, 0⟩ : Cycle Card)
      rw [if_pos (by omega : c ≥ l.length)]
    obtain ⟨k₀, hk₀⟩ := dealOnce_reach_end hs l l.length 0 (Nat.zero_le _) (by omega)
    refine ⟨k₀ + 1, ?_⟩
    rw [Cycle.dealN_succ, ← Cycle.dealN_shift, hwrap, hk₀]

/-- The wrapped advance: reach the pass end, wrap to 0, then climb to
`i + 1` on the batch-top lane (`i + 1` a multiple of `s`). -/
theorem dealOnce_wrap_advance {s : Nat} (hs : 0 < s) (l : List Card) (c i : Nat)
    (hlt : i < l.length) (hle : s - 1 ≤ i) (hmod : (i - (s - 1)) % s = 0) :
    ∃ k, Cycle.dealN s k ⟨l, c⟩ = ⟨l, i + 1⟩ := by
  obtain ⟨k₀, hk₀⟩ := dealOnce_reach_end_any hs l c
  have hwrap : Cycle.dealOnce s ⟨l, l.length⟩ = ⟨l, 0⟩ := by
    show (if l.length ≥ l.length then (⟨l, 0⟩ : Cycle Card)
        else ⟨l, min (l.length + s) l.length⟩) = (⟨l, 0⟩ : Cycle Card)
    rw [if_pos (Nat.le_refl l.length)]
  obtain ⟨q, hq⟩ := exists_mul_of_mod_zero hmod
  have hexp : (q + 1) * s = q * s + s := by rw [Nat.add_mul, Nat.one_mul]
  have hadv : 0 + (q + 1) * s ≤ l.length := by rw [hexp]; omega
  have hlast : 0 + (q + 1) * s = i + 1 := by rw [hexp]; omega
  refine ⟨(q + 1) + (1 + k₀), ?_⟩
  have hcomp1 : Cycle.dealN s (1 + k₀) ⟨l, c⟩
      = Cycle.dealOnce s (Cycle.dealN s k₀ ⟨l, c⟩) := by
    rw [Cycle.dealN_add, Cycle.dealN_one]
  have hcomp2 : Cycle.dealN s ((q + 1) + (1 + k₀)) ⟨l, c⟩
      = Cycle.dealN s (q + 1) (Cycle.dealOnce s (Cycle.dealN s k₀ ⟨l, c⟩)) := by
    rw [Cycle.dealN_add, hcomp1]
  rw [hcomp2, hk₀, hwrap,
    dealOnce_iterate_add hs l (q + 1) 0 hadv, hlast]

/-- The deal-orbit correspondence, witness half: every accessible
position is dealt to — `dealN` realizes the jump `drawTo i`.  `posOf`'s
range bound (`hlt`) replaces the WF cursor invariant: the mask's
leading-lane bound and the wrapped lane's truncation are never needed
in this direction (out-of-range positions never have a position). -/
theorem maskPos_deal_reach {s : Nat} (hs : 0 < s) {cy : Cycle Card} {i : Nat}
    (hlt : i < cy.cards.length) (hmem : i ∈ Pace.maskPos cy s hs) :
    ∃ k, Cycle.dealN s k cy = { cy with cursor := i + 1 } := by
  rcases cy with ⟨l, c⟩
  show ∃ k, Cycle.dealN s k ⟨l, c⟩ = ⟨l, i + 1⟩
  have hlt : i < l.length := hlt
  simp only [Pace.maskPos] at hmem
  rcases List.mem_append.mp hmem with h12 | h3
  · rcases List.mem_append.mp h12 with h1 | h2
    · obtain ⟨hle, hlt2, hmod⟩ := (Pace.laneUp_mem s hs _ _ i).mp h1
      by_cases hc0 : c = 0
      · subst hc0
        rw [if_pos rfl] at hle hmod
        exact dealOnce_wrap_advance hs l 0 i hlt hle hmod
      · rw [if_neg hc0] at hle hmod
        obtain ⟨q, hq⟩ := exists_mul_of_mod_zero hmod
        have hle2 : c + q * s ≤ l.length := by omega
        have hkey : c + q * s = i + 1 := by omega
        refine ⟨q, ?_⟩
        rw [dealOnce_iterate_add hs l q c hle2]
        exact congrArg (Cycle.mk l) hkey
    · rw [if_pos (by omega : 0 < l.length)] at h2
      simp only [List.mem_singleton] at h2
      obtain ⟨k, hk⟩ := dealOnce_reach_end_any hs l c
      refine ⟨k, ?_⟩
      rw [hk]
      exact congrArg (Cycle.mk l) (by omega)
  · obtain ⟨hle, -, hmod⟩ := (Pace.laneUp_mem s hs _ _ i).mp h3
    exact dealOnce_wrap_advance hs l c i hlt hle hmod

/-- A found index points at a satisfying element. -/
theorem findFirstIdx_getElem? {α : Type} (p : α → Bool) :
    ∀ (l : List α) (i : Nat), Cycle.findFirstIdx p l = some i →
      ∃ a, l[i]? = some a ∧ p a = true := by
  intro l
  induction l with
  | nil => intro i h; simp [Cycle.findFirstIdx] at h
  | cons a t ih =>
    intro i h
    simp only [Cycle.findFirstIdx] at h
    by_cases hp : p a = true
    · rw [if_pos hp, Option.some.injEq] at h
      subst h
      exact ⟨a, rfl, hp⟩
    · rw [if_neg hp] at h
      cases hf : Cycle.findFirstIdx p t with
      | none => rw [hf] at h; simp at h
      | some j =>
        rw [hf, Option.map_some, Option.some.injEq] at h
        obtain ⟨b, hb, hpb⟩ := ih j hf
        subst h
        exact ⟨b, by rw [List.getElem?_cons_succ]; exact hb, hpb⟩

/-- A found position points at the card. -/
theorem posOf_getElem? {c : Card} {cy : Cycle Card} {i : Nat}
    (h : cy.posOf c = some i) : cy.cards[i]? = some c := by
  simp only [Cycle.posOf] at h
  obtain ⟨a, ha, hpa⟩ := findFirstIdx_getElem? _ cy.cards i h
  rw [ha]
  have hac : a = c := of_decide_eq_true hpa
  rw [hac]

/-- `reachablePos`'s shape: the step guard, the position, the mask. -/
theorem reachablePos_eq_some_iff {st : State} {c : Card} {i : Nat} :
    st.reachablePos c = some i ↔
      ∃ hstep : 0 < st.drawStep, st.stock.posOf c = some i ∧
        i ∈ Pace.maskPos st.stock st.drawStep hstep := by
  constructor
  · intro h
    simp only [State.reachablePos] at h
    split at h
    · rename_i hstep
      cases hpo : st.stock.posOf c with
      | none => rw [hpo] at h; simp at h
      | some j =>
        rw [hpo] at h
        have h' : (if j ∈ Pace.maskPos st.stock st.drawStep hstep then some j else none) = some i := h
        by_cases hmem : j ∈ Pace.maskPos st.stock st.drawStep hstep
        · rw [if_pos hmem, Option.some.injEq] at h'
          subst h'
          exact ⟨hstep, rfl, hmem⟩
        · rw [if_neg hmem] at h'; simp at h'
    · simp at h
  · intro ⟨hstep, hpo, hmem⟩
    simp only [State.reachablePos, dif_pos hstep, hpo, if_pos hmem]

/-- `applyDrawTo`'s shape: the reachable guard selects the index, the
attach the board, the successor the spliced jump. -/
theorem applyDrawTo_iff {st : State} {c : Card} {b : Base} {st' : State} :
    st.applyDrawTo c b = some st' ↔
      ∃ i bd, st.reachablePos c = some i ∧ st.board.attach b c = some bd ∧
        st' = { st with board := bd, stock := (st.stock.drawTo i).removeAt i } := by
  constructor
  · intro h
    simp only [State.applyDrawTo] at h
    cases hpos : st.reachablePos c with
    | none => rw [hpos] at h; simp at h
    | some i =>
      rw [hpos] at h
      have h' : (match st.board.attach b c with
          | none => none
          | some bd => some { st with board := bd, stock := (st.stock.drawTo i).removeAt i }) = some st' := h
      cases hatt : st.board.attach b c with
      | none => rw [hatt] at h'; simp at h'
      | some bd =>
        rw [hatt] at h'
        simp at h'
        exact ⟨i, bd, rfl, rfl, h'.symm⟩
  · intro ⟨i, bd, hpos, hatt, hst⟩
    rw [hst]
    simp only [State.applyDrawTo, hpos, hatt]

/-- `applyDrawStackTo`'s shape: the guard selects the index and checks
the foundation rank; the successor splices the jump and bumps. -/
theorem applyDrawStackTo_iff {st : State} {c : Card} {st' : State} :
    st.applyDrawStackTo c = some st' ↔
      ∃ i, st.reachablePos c = some i ∧ c.rank.toIdx = st.heights c.suit ∧
        st' = { st with
          stock := (st.stock.drawTo i).removeAt i,
          heights := fun s => if s = c.suit then st.heights s + 1 else st.heights s } := by
  constructor
  · intro h
    simp only [State.applyDrawStackTo] at h
    cases hpos : st.reachablePos c with
    | none => rw [hpos] at h; simp at h
    | some i =>
      rw [hpos] at h
      have h' : (if c.rank.toIdx = st.heights c.suit then
          some { st with
            stock := (st.stock.drawTo i).removeAt i,
            heights := fun s => if s = c.suit then st.heights s + 1 else st.heights s }
          else none) = some st' := h
      by_cases hrk : c.rank.toIdx = st.heights c.suit
      · rw [if_pos hrk, Option.some.injEq] at h'
        exact ⟨i, rfl, hrk, h'.symm⟩
      · rw [if_neg hrk] at h'; simp at h'
  · intro ⟨i, hpos, hrk, hst⟩
    rw [hst]
    simp only [State.applyDrawStackTo, hpos, if_pos hrk]

/-- Pointwise agreement of the search predicates. -/
theorem findFirst_congr_mem {α : Type} (p q : α → Bool) :
    ∀ (l : List α), (∀ a ∈ l, p a = q a) → findFirst p l = findFirst q l := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons a t ih =>
    intro h
    rw [findFirst_cons, findFirst_cons, h a List.mem_cons_self]
    by_cases hq : q a = true
    · rw [if_pos hq, if_pos hq]
    · rw [if_neg hq, if_neg hq]
      exact ih (fun a' ha' => h a' (List.mem_cons_of_mem _ ha'))

/-- Attaching `c` at `b` leaves every other card's `bottomOf` alone. -/
theorem bottomOf_attach_of_ne {bd : Board} {b : Base} {c x : Card} {bd' : Board}
    (hatt : bd.attach b c = some bd') (hne : x ≠ c) :
    bd'.bottomOf x = bd.bottomOf x := by
  have hfree : bd.topOf b = none := ((Board.attach_eq_some_iff bd b c).mp (by simp [hatt])).1
  have hself : bd'.topOf b = some c := Board.attach_topOf bd b c hatt
  show findFirst (fun β => decide (bd'.topOf β = some x)) Board.enumBase
     = findFirst (fun β => decide (bd.topOf β = some x)) Board.enumBase
  refine findFirst_congr_mem _ _ _ (fun β _ => ?_)
  by_cases hβ : β = b
  · subst hβ
    have hcx : c ≠ x := fun hh => hne hh.symm
    rw [hself, hfree]
    simp [hcx]
  · rw [Board.attach_topOf_ne bd b c hatt hβ]

/-- Running a one-move play is applying the move. -/
theorem run_singleton (st : State) (m : Move) : st.run [m] = st.apply m := by
  show (match st.apply m with | some st' => st'.run [] | none => none) = st.apply m
  cases st.apply m <;> rfl

/-- A run of pure deals lands on the iterated deal. -/
theorem run_replicate_draw : ∀ (k : Nat) (st : State),
    st.run (List.replicate k Move.draw) =
      some { st with stock := Cycle.dealN st.drawStep k st.stock } := by
  intro k
  induction k with
  | zero => intro st; rfl
  | succ k ih =>
    intro st
    rw [List.replicate_succ, State.run, show st.apply Move.draw =
      some { st with stock := Cycle.dealOnce st.drawStep st.stock } from rfl]
    show ({ st with stock := Cycle.dealOnce st.drawStep st.stock } : State).run
        (List.replicate k Move.draw) = _
    rw [ih { st with stock := Cycle.dealOnce st.drawStep st.stock }]
    show some { st with stock := Cycle.dealN st.drawStep k (Cycle.dealOnce st.drawStep st.stock) }
       = some { st with stock := Cycle.dealN st.drawStep (k + 1) st.stock }
    rw [Cycle.dealN_shift, Cycle.dealN_succ]

/-- The tableau deck move after the deals brought `c` to the top:
the successor is exactly `applyDrawTo`'s. -/
theorem deckPile_after_draws {st : State} {c : Card} {b : Base} {i : Nat} {bd : Board}
    (hget : st.stock.cards[i]? = some c) (hcan : st.canPlace c b = true)
    (hatt : st.board.attach b c = some bd) :
    ({ st with stock := { st.stock with cursor := i + 1 } }).apply (Move.deckPile c b)
      = some { st with board := bd, stock := (st.stock.drawTo i).removeAt i } := by
  have hprev : ({ st with stock := { st.stock with cursor := i + 1 } } : State).stock.prev = some c := by
    show (Cycle.prev { st.stock with cursor := i + 1 }) = some c
    show (if i + 1 = 0 then none else st.stock.cards[i + 1 - 1]?) = some c
    rw [if_neg (by omega : ¬ (i + 1 = 0))]
    have hi : i + 1 - 1 = i := by omega
    rw [hi]
    exact hget
  have e1 : (({ st with stock := { st.stock with cursor := i + 1 } } : State).stock.cursor - 1) = i := by
    show i + 1 - 1 = i
    omega
  have e2 : ({ st with stock := { st.stock with cursor := i + 1 } } : State).stock
      = { st.stock with cursor := i + 1 } := rfl
  have e3 : st.stock.drawTo i = { st.stock with cursor := i + 1 } := rfl
  refine (apply_deckPile_iff).mpr ⟨hprev, hcan, bd, hatt, ?_⟩
  rw [e1, e2, e3]

/-- The stack deck move after the deals: as `deckPile_after_draws`. -/
theorem deckStack_after_draws {st : State} {c : Card} {i : Nat}
    (hget : st.stock.cards[i]? = some c) (hrank : c.rank.toIdx = st.heights c.suit) :
    ({ st with stock := { st.stock with cursor := i + 1 } }).apply (Move.deckStack c)
      = some { st with
        stock := (st.stock.drawTo i).removeAt i,
        heights := fun s => if s = c.suit then st.heights s + 1 else st.heights s } := by
  have hprev : ({ st with stock := { st.stock with cursor := i + 1 } } : State).stock.prev = some c := by
    show (Cycle.prev { st.stock with cursor := i + 1 }) = some c
    show (if i + 1 = 0 then none else st.stock.cards[i + 1 - 1]?) = some c
    rw [if_neg (by omega : ¬ (i + 1 = 0))]
    have hi : i + 1 - 1 = i := by omega
    rw [hi]
    exact hget
  have e1 : (({ st with stock := { st.stock with cursor := i + 1 } } : State).stock.cursor - 1) = i := by
    show i + 1 - 1 = i
    omega
  have e2 : ({ st with stock := { st.stock with cursor := i + 1 } } : State).stock
      = { st.stock with cursor := i + 1 } := rfl
  have e3 : st.stock.drawTo i = { st.stock with cursor := i + 1 } := rfl
  refine (apply_deckStack_iff).mpr ⟨hprev, hrank, ?_⟩
  show { st with
    stock := (st.stock.drawTo i).removeAt i,
    heights := fun s => if s = c.suit then st.heights s + 1 else st.heights s }
     = { st with
    stock := (({ st with stock := { st.stock with cursor := i + 1 } } : State).stock).removeAt
        ((({ st with stock := { st.stock with cursor := i + 1 } } : State).stock.cursor - 1)),
    heights := fun s => if s = c.suit
      then ({ st with stock := { st.stock with cursor := i + 1 } } : State).heights s + 1
      else ({ st with stock := { st.stock with cursor := i + 1 } } : State).heights s }
  rw [e1, e2, e3]

/-- A macro step is an engine play: the accommodation is
stack↔pile shuffling, the Draw commitment is deals plus the deck
move, all within the engine's move set.  The Draw commitment's deal
count comes from the mask's lane structure (`maskPos_deal_reach`:
every accessible position is dealt to — the witness half of
`applyDrawTo_eq_dealPlay`, no WF needed).  The tableau landing's
`canPlace` is `commitApplies`'s guard — without it this theorem is
false (see that def's repair note). -/
theorem macroStep_engine_play {st : State} {k : MacroMove} {st'' : State}
    (h : macroStep st k st'') :
    ∃ play, st.run play = some st'' ∧ ∀ m ∈ play, m.isEngine = true := by
  simp only [macroStep] at h
  obtain ⟨st', hacc, hcom⟩ := h
  simp only [accommodates] at hacc
  obtain ⟨play₁, hr₁, heng₁⟩ := hacc
  have hengall : ∀ m ∈ play₁, m.isEngine = true := by
    intro m hm
    have hac := heng₁ m hm
    cases m <;> simp_all [Move.isAccommodation, Move.isEngine]
  cases k with
  | revealCommit c =>
    simp only [commitApplies] at hcom
    refine ⟨play₁ ++ [Move.reveal c], ?_, ?_⟩
    · rw [run_append, hr₁]
      show st'.run [Move.reveal c] = some st''
      rw [run_singleton]
      exact hcom
    · intro m hm
      rcases List.mem_append.mp hm with hm | hm
      · exact hengall m hm
      · obtain rfl := List.mem_singleton.mp hm
        rfl
  | drawCommit c =>
    simp only [commitApplies] at hcom
    obtain ⟨b, hb⟩ := hcom
    rcases hb with ⟨hcan, hdt⟩ | hds
    · obtain ⟨i, bd, hp, hatt, hst''⟩ := (applyDrawTo_iff).mp hdt
      subst hst''
      obtain ⟨hstep, hpos, hmem⟩ := (reachablePos_eq_some_iff).mp hp
      obtain ⟨kk, hkk⟩ := maskPos_deal_reach hstep (Cycle.posOf_lt hpos) hmem
      have hrun : st'.run (List.replicate kk Move.draw) =
          some { st' with stock := { st'.stock with cursor := i + 1 } } := by
        rw [run_replicate_draw, hkk]
      have hdp := deckPile_after_draws (posOf_getElem? hpos) hcan hatt
      refine ⟨play₁ ++ (List.replicate kk Move.draw ++ [Move.deckPile c b]), ?_, ?_⟩
      · rw [run_append, hr₁]
        show st'.run (List.replicate kk Move.draw ++ [Move.deckPile c b])
          = some { st' with board := bd, stock := (st'.stock.drawTo i).removeAt i }
        rw [run_append, hrun]
        show ({ st' with stock := { st'.stock with cursor := i + 1 } } : State).run
            [Move.deckPile c b] = _
        rw [run_singleton]
        exact hdp
      · intro m hm
        rcases List.mem_append.mp hm with hm | hm
        · exact hengall m hm
        · rcases List.mem_append.mp hm with hm | hm
          · obtain ⟨-, rfl⟩ := List.mem_replicate.mp hm
            rfl
          · obtain rfl := List.mem_singleton.mp hm
            rfl
    · obtain ⟨i, hp, hrank, hst''⟩ := (applyDrawStackTo_iff).mp hds
      subst hst''
      obtain ⟨hstep, hpos, hmem⟩ := (reachablePos_eq_some_iff).mp hp
      obtain ⟨kk, hkk⟩ := maskPos_deal_reach hstep (Cycle.posOf_lt hpos) hmem
      have hrun : st'.run (List.replicate kk Move.draw) =
          some { st' with stock := { st'.stock with cursor := i + 1 } } := by
        rw [run_replicate_draw, hkk]
      have hdp := deckStack_after_draws (posOf_getElem? hpos) hrank
      refine ⟨play₁ ++ (List.replicate kk Move.draw ++ [Move.deckStack c]), ?_, ?_⟩
      · rw [run_append, hr₁]
        show st'.run (List.replicate kk Move.draw ++ [Move.deckStack c])
          = some { st' with
            stock := (st'.stock.drawTo i).removeAt i,
            heights := fun s => if s = c.suit then st'.heights s + 1 else st'.heights s }
        rw [run_append, hrun]
        show ({ st' with stock := { st'.stock with cursor := i + 1 } } : State).run
            [Move.deckStack c] = _
        rw [run_singleton]
        exact hdp
      · intro m hm
        rcases List.mem_append.mp hm with hm | hm
        · exact hengall m hm
        · rcases List.mem_append.mp hm with hm | hm
          · obtain ⟨-, rfl⟩ := List.mem_replicate.mp hm
            rfl
          · obtain rfl := List.mem_singleton.mp hm
            rfl

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
it; corpus-gated there, not proven).  From `applyDrawTo`'s definition
(the guard selects the same `i` both times) + the `attach` consumption
lemmas. -/
theorem drawTo_tableau_outcomes_agree {st : State} {c : Card} {b b' : Base}
    {st₁ st₂ : State}
    (h₁ : st.applyDrawTo c b = some st₁) (h₂ : st.applyDrawTo c b' = some st₂) :
    st₁.deal = st₂.deal ∧ st₁.heights = st₂.heights ∧ st₁.depths = st₂.depths ∧
      st₁.stock = st₂.stock ∧ st₁.drawStep = st₂.drawStep ∧
      ∀ c'', st₁.isVis c'' = st₂.isVis c'' := by
  obtain ⟨i₁, bd₁, hp₁, hatt₁, hst₁⟩ := (applyDrawTo_iff).mp h₁
  obtain ⟨i₂, bd₂, hp₂, hatt₂, hst₂⟩ := (applyDrawTo_iff).mp h₂
  have hii : i₁ = i₂ := Option.some.inj (hp₁.symm.trans hp₂)
  subst hii
  subst hst₁
  subst hst₂
  refine ⟨rfl, rfl, rfl, rfl, rfl, ?_⟩
  intro c''
  show (bd₁.bottomOf c'').isSome = (bd₂.bottomOf c'').isSome
  by_cases hcc : c'' = c
  · subst hcc
    rw [(Board.bottomOf_eq _ _ _).mpr (Board.attach_topOf _ _ _ hatt₁),
       (Board.bottomOf_eq _ _ _).mpr (Board.attach_topOf _ _ _ hatt₂)]
    rfl
  · rw [bottomOf_attach_of_ne hatt₁ hcc, bottomOf_attach_of_ne hatt₂ hcc]

/-! ### The pace-replay toolkit

The pieces the pace dominances repeat, named: the cursor relation's
symmetry, the two game-wide invariants no move breaks (draw step,
board-only reading of `canPlace`), the mask-membership transport (the
positivity argument is proof-irrelevant), the cursor variant's WF, and
the run-level accommodation replay.  Consolidation note: these are
Macro-local for the wave (the file was the only consumer); moving them
upstream (State/Commutation) is the orchestrator's call. -/

/-- The pace relation's symmetry (all six conjuncts are equalities). -/
theorem diffCursor_symm {st st' : State} (h : st.diffCursor st') : st'.diffCursor st :=
  ⟨h.1.symm, h.2.1.symm, h.2.2.1.symm, h.2.2.2.1.symm, h.2.2.2.2.1.symm,
    h.2.2.2.2.2.symm⟩

/-- No move ever writes the draw step — the pacing parameter is fixed
for the whole game (every apply's successor is a with-update that never
names it). -/
theorem apply_drawStep_invar {st st₁ : State} {m : Move}
    (h : st.apply m = some st₁) : st₁.drawStep = st.drawStep := by
  cases m with
  | draw =>
      rw [apply_draw_iff] at h
      rw [h]
  | reveal c =>
      rw [apply_reveal_iff] at h
      obtain ⟨-, r, a, bd, -, -, -, hst⟩ := h
      rw [hst]
  | deckPile c b =>
      rw [apply_deckPile_iff] at h
      obtain ⟨-, -, bd, -, hst⟩ := h
      rw [hst]
  | deckStack c =>
      rw [apply_deckStack_iff] at h
      obtain ⟨-, -, hst⟩ := h
      rw [hst]
  | pileStack c =>
      rw [apply_pileStack_iff] at h
      obtain ⟨-, b, -, -, hst⟩ := h
      rw [hst]
  | stackPile c b =>
      rw [apply_stackPile_iff] at h
      obtain ⟨-, -, bd, -, hst⟩ := h
      rw [hst]
  | pilePile c b =>
      rw [apply_pilePile_iff] at h
      obtain ⟨b₀, -, -, -, bd, -, hst⟩ := h
      rw [hst]

/-- `canPlace` reads the board alone — the stock cursor never enters
the landing rule. -/
theorem canPlace_board_congr {st st' : State} {c : Card} {b : Base}
    (hb : st.board = st'.board) : st.canPlace c b = st'.canPlace c b := by
  simp only [State.canPlace, State.isVis, hb]

/-- `maskPos` memberships transport along equalities of the cycle and
the step: the positivity argument is proof-irrelevant, the data rides
the equalities. -/
theorem maskPos_mem_trans {α : Type} {cy cy' : Cycle α} {s s' : Nat}
    {hp : 0 < s} {hp' : 0 < s'} (hcy : cy = cy') (hss : s = s')
    (i : Nat) (h : i ∈ Pace.maskPos cy s hp) :
    i ∈ Pace.maskPos cy' s' hp' := by
  subst hcy
  subst hss
  exact h

/-- The cursor variant of a well-formed state is well-formed — only
`cursor_le` reads the cursor, and that is the supplied bound. -/
theorem wf_of_cursor {st : State} {o : Nat} (hwf : st.WF)
    (hcur : o ≤ st.stock.cards.length) :
    ({ st with stock := { st.stock with cursor := o } } : State).WF := by
  refine ⟨hwf.1, hwf.2.1, hwf.2.2.1, hwf.2.2.2.1, hwf.2.2.2.2.1,
    hwf.2.2.2.2.2.1, hwf.2.2.2.2.2.2.1, hwf.2.2.2.2.2.2.2.1, ?_,
    hwf.2.2.2.2.2.2.2.2.2.1, hwf.2.2.2.2.2.2.2.2.2.2⟩
  show o ≤ st.stock.cards.length
  exact hcur

/-- One blind replay step: the accommodation move applies from the
partner state too, landing on partners (used under both shuffles). -/
theorem acc_step_blind {st st' s : State} {m : Move} {ms : List Move}
    (hind : ∀ m' ∈ ms, m'.isAccommodation = true)
    (hc : m.consumesStock = false) (hmd : m ≠ Move.draw)
    (hd : st.diffCursor st') (hrun : st.run (m :: ms) = some s)
    (ih : ∀ (st st' s : State), (∀ m ∈ ms, m.isAccommodation = true) →
      st.diffCursor st' → st.run ms = some s →
      ∃ t, st'.run ms = some t ∧ s.diffCursor t ∧ t.stock = st'.stock ∧
        s.stock = st.stock ∧ s.drawStep = st.drawStep ∧ t.drawStep = st'.drawStep) :
    ∃ t, st'.run (m :: ms) = some t ∧ s.diffCursor t ∧ t.stock = st'.stock ∧
      s.stock = st.stock ∧ s.drawStep = st.drawStep ∧ t.drawStep = st'.drawStep := by
  simp only [State.run] at hrun
  cases hsm : st.apply m with
  | none => rw [hsm] at hrun; simp at hrun
  | some s₁ =>
      rw [hsm] at hrun
      have hrest : s₁.run ms = some s := hrun
      obtain ⟨s₁', hs₁', hds₁⟩ := apply_nonConsuming_cursor_blind hc hd hsm
      have hs₁stock : s₁.stock = st.stock := apply_nonConsuming_stock_invar hc hmd hsm
      have hs₁'stock : s₁'.stock = st'.stock :=
        apply_nonConsuming_stock_invar hc hmd hs₁'
      have hs₁ds : s₁.drawStep = st.drawStep := apply_drawStep_invar hsm
      have hs₁'ds : s₁'.drawStep = st'.drawStep := apply_drawStep_invar hs₁'
      obtain ⟨t, htrun, hdt, htstock, hsstock, hsds, htds⟩ :=
        ih s₁ s₁' s hind hds₁ hrest
      refine ⟨t, ?_, hdt, ?_, ?_, ?_, ?_⟩
      · simp only [State.run]
        rw [hs₁']
        exact htrun
      · rw [htstock]; exact hs₁'stock
      · rw [hsstock]; exact hs₁stock
      · rw [hsds]; exact hs₁ds
      · rw [htds]; exact hs₁'ds

/-- The accommodation replay, run level: a shuffle play from a state
replays verbatim from any cursor-partner, landing on partners — the
prefix step of every pace-dominance replay. -/
theorem accommodates_cursor_blind : ∀ (st st' s : State) (play : List Move),
    (∀ m ∈ play, m.isAccommodation = true) → st.diffCursor st' →
    st.run play = some s →
    ∃ t, st'.run play = some t ∧ s.diffCursor t ∧ t.stock = st'.stock ∧
      s.stock = st.stock ∧ s.drawStep = st.drawStep ∧ t.drawStep = st'.drawStep := by
  intro st st' s play
  induction play generalizing st st' s with
  | nil =>
      intro _ hd hrun
      have h0 : st.run [] = some st := rfl
      rw [h0] at hrun
      have hss : st = s := Option.some.inj hrun
      subst hss
      exact ⟨st', rfl, hd, rfl, rfl, rfl, rfl⟩
  | cons m ms ih =>
      intro hind hd hrun
      have hmac : m.isAccommodation = true := hind m (List.mem_cons.mpr (Or.inl rfl))
      cases m with
      | draw => simp [Move.isAccommodation] at hmac
      | reveal c => simp [Move.isAccommodation] at hmac
      | deckPile c b => simp [Move.isAccommodation] at hmac
      | deckStack c => simp [Move.isAccommodation] at hmac
      | pilePile c b => simp [Move.isAccommodation] at hmac
      | pileStack c =>
          exact acc_step_blind (fun m' hm' => hind m' (List.mem_cons.mpr (Or.inr hm')))
            rfl (by intro h; simp at h) hd hrun ih
      | stackPile c b =>
          exact acc_step_blind (fun m' hm' => hind m' (List.mem_cons.mpr (Or.inr hm')))
            rfl (by intro h; simp at h) hd hrun ih

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

Proof: `macroSolvable_of_simulates` at the stock-pinned relation
`diffCursor ∧ drawStep = st.drawStep ∧ x.stock = st.stock ∧
y.stock = the o'-stock` — the pins never need re-establishing (reveals
preserve stocks, draws merge past the relation), so the superset `hK`
only ever applies at the original cursor pair.  The accommodation
prefix replays verbatim (`accommodates_cursor_blind`); the draw guard
is rebuilt cards-only (`posOf_cards_eq`) with the mask transported
(`maskPos_mem_trans`); the successors merge
(`applyDrawTo_merge`/`applyDrawStackTo_merge`).  `hcur'` is vestigial
(the superset subsumes it). -/
theorem pace_dominance {st : State} {o' : Nat} (hwf : st.WF)
    (hcur' : o' ≤ st.stock.cards.length)
    (hK : ∀ p, p ∈ Pace.maskPos { cards := st.stock.cards, cursor := o' }
        st.drawStep hwf.step_pos →
      p ∈ Pace.maskPos st.stock st.drawStep hwf.step_pos)
    (hsol : { st with stock := { st.stock with cursor := o' } }.macroSolvable) :
    st.macroSolvable := by
  have := hcur'
  -- The pace relation: identical but for the cursor, both stocks pinned
  -- to the two constants.  The pins never need re-establishing: reveals
  -- preserve the stocks (non-consuming), and the draw case merges past
  -- the relation entirely (the successors are equal), so the superset
  -- only ever applies at the original cursor pair.
  refine macroSolvable_of_simulates (a := st)
    (b := { st with stock := { st.stock with cursor := o' } })
    (fun x y => x.diffCursor y ∧ x.drawStep = st.drawStep ∧
      x.stock = st.stock ∧ y.stock = { st.stock with cursor := o' })
    ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, rfl⟩ ?_ ?_ hsol
  · -- the one-step simulation
    intro x y k b' hRxy hms
    obtain ⟨hdc, hds, hxs, hys⟩ := hRxy
    have hyd : y.drawStep = st.drawStep := by rw [← hdc.2.2.2.2.2]; exact hds
    simp only [macroStep] at hms
    obtain ⟨y₁, hacc, hcom⟩ := hms
    obtain ⟨play, hplay, haccm⟩ := hacc
    -- the accommodation replays verbatim from the partner state
    obtain ⟨x₁, hx₁run, hdx₁, hx₁s, hy₁s, hy₁d, hx₁d⟩ :=
      accommodates_cursor_blind y x y₁ play haccm (diffCursor_symm hdc) hplay
    have haccx : accommodates x x₁ := ⟨play, hx₁run, haccm⟩
    have hy₁ds : y₁.drawStep = st.drawStep := by rw [hy₁d, hyd]
    have hx₁ds : x₁.drawStep = st.drawStep := by rw [hx₁d, hds]
    have hx₁stock : x₁.stock = st.stock := by rw [hx₁s, hxs]
    have hy₁stock : y₁.stock = { st.stock with cursor := o' } := by rw [hy₁s, hys]
    have hcardseq : st.stock.cards = y₁.stock.cards := by rw [hy₁stock]
    cases k with
    | revealCommit c =>
        -- cursor-inert: the same reveal applies from the partner, the
        -- successors stay partners
        simp only [commitApplies] at hcom
        obtain ⟨a', ha', hda'⟩ :=
          apply_nonConsuming_cursor_blind rfl hdx₁ hcom
        have ha's : a'.stock = x₁.stock :=
          apply_nonConsuming_stock_invar rfl (by intro h; simp at h) ha'
        have hb's : b'.stock = y₁.stock :=
          apply_nonConsuming_stock_invar rfl (by intro h; simp at h) hcom
        have ha'd : a'.drawStep = x₁.drawStep := apply_drawStep_invar ha'
        refine ⟨MacroMove.revealCommit c, a', ⟨x₁, haccx, ha'⟩, Or.inr
          ⟨diffCursor_symm hda', by rw [ha'd, hx₁ds], by rw [ha's, hx₁stock],
            by rw [hb's, hy₁stock]⟩⟩
    | drawCommit c =>
        -- the guard's position is cards-only; the superset carries the
        -- mask; the successors merge
        simp only [commitApplies] at hcom
        obtain ⟨base, hb⟩ := hcom
        rcases hb with ⟨hcan, hdt⟩ | hdst
        · -- tableau landing
          obtain ⟨i, bd, hr, hatt, _⟩ := applyDrawTo_iff.mp hdt
          obtain ⟨_, hpos', hmem'⟩ := reachablePos_eq_some_iff.mp hr
          have hstepx : 0 < x₁.drawStep := by rw [hx₁ds]; exact hwf.step_pos
          have hposx : x₁.stock.posOf c = some i := by
            rw [hx₁stock, posOf_cards_eq hcardseq]
            exact hpos'
          have hmemx : i ∈ Pace.maskPos x₁.stock x₁.drawStep hstepx :=
            maskPos_mem_trans (show st.stock = x₁.stock from hx₁stock.symm)
              (show st.drawStep = x₁.drawStep from hx₁ds.symm) i
              (hK i (maskPos_mem_trans hy₁stock hy₁ds i hmem'))
          have hxr : x₁.reachablePos c = some i :=
            reachablePos_eq_some_iff.mpr ⟨hstepx, hposx, hmemx⟩
          have hattx : x₁.board.attach base c = some bd := by
            rw [← hdx₁.2.1]; exact hatt
          have hxdt : x₁.applyDrawTo c base =
              some { x₁ with board := bd, stock := (x₁.stock.drawTo i).removeAt i } :=
            applyDrawTo_iff.mpr ⟨i, bd, hxr, hattx, rfl⟩
          have hmerge : b' =
              { x₁ with board := bd, stock := (x₁.stock.drawTo i).removeAt i } :=
            applyDrawTo_merge hdx₁ hdt hxdt
          rw [← hmerge] at hxdt
          refine ⟨MacroMove.drawCommit c, b', ⟨x₁, haccx, ⟨base, Or.inl ⟨by
            rw [← canPlace_board_congr hdx₁.2.1]; exact hcan, hxdt⟩⟩⟩, Or.inl rfl⟩
        · -- stack landing
          obtain ⟨i, hr, hrk, _⟩ := applyDrawStackTo_iff.mp hdst
          obtain ⟨_, hpos', hmem'⟩ := reachablePos_eq_some_iff.mp hr
          have hstepx : 0 < x₁.drawStep := by rw [hx₁ds]; exact hwf.step_pos
          have hposx : x₁.stock.posOf c = some i := by
            rw [hx₁stock, posOf_cards_eq hcardseq]
            exact hpos'
          have hmemx : i ∈ Pace.maskPos x₁.stock x₁.drawStep hstepx :=
            maskPos_mem_trans (show st.stock = x₁.stock from hx₁stock.symm)
              (show st.drawStep = x₁.drawStep from hx₁ds.symm) i
              (hK i (maskPos_mem_trans hy₁stock hy₁ds i hmem'))
          have hxr : x₁.reachablePos c = some i :=
            reachablePos_eq_some_iff.mpr ⟨hstepx, hposx, hmemx⟩
          have hrkx : c.rank.toIdx = x₁.heights c.suit := by
            rw [← hdx₁.2.2.1]; exact hrk
          have hxds' : x₁.applyDrawStackTo c =
              some { x₁ with
                stock := (x₁.stock.drawTo i).removeAt i,
                heights := fun s => if s = c.suit then x₁.heights s + 1 else x₁.heights s } :=
            applyDrawStackTo_iff.mpr ⟨i, hxr, hrkx, rfl⟩
          have hmerge : b' = { x₁ with
                stock := (x₁.stock.drawTo i).removeAt i,
                heights := fun s => if s = c.suit then x₁.heights s + 1 else x₁.heights s } :=
            applyDrawStackTo_merge hdx₁ hdst hxds'
          rw [← hmerge] at hxds'
          exact ⟨MacroMove.drawCommit c, b', ⟨x₁, haccx, ⟨base, Or.inr hxds'⟩⟩, Or.inl rfl⟩
  · -- wins are heights-only
    intro x y hRxy hyw
    have hh : x.heights = y.heights := hRxy.1.2.2.1
    have hisw : State.isWin x = State.isWin y := by
      simp only [State.isWin, hh]
    rw [hisw]
    exact hyw

/-- **R1 (registry rule 1)**: within an impure residue class the
earlier cursor dominates — a win from the later pace lifts to the
earlier.  This is the soundness of skipping the larger-offset state
when the minimal same-residue state was refuted.

Proof: `pace_dominance` at the `o`-variant (whose WF is `wf_of_cursor`,
only `cursor_le` reads the cursor) with `Pace.maskPos_residue_mono`
as `hK`. -/
theorem pace_dominance_residue {st : State} {o o' : Nat} (hwf : st.WF)
    (hle : o ≤ o')
    (hres : o % st.drawStep = o' % st.drawStep)
    (himp : o' % st.drawStep ≠ 0)
    (hcur : o ≤ st.stock.cards.length) (hcur' : o' ≤ st.stock.cards.length)
    (hsol : { st with stock := { st.stock with cursor := o' } }.macroSolvable) :
    { st with stock := { st.stock with cursor := o } }.macroSolvable := by
  refine pace_dominance (st := { st with stock := { st.stock with cursor := o } })
    (o' := o') (wf_of_cursor hwf hcur) hcur' ?_ hsol
  intro p hp
  exact Pace.maskPos_residue_mono (c := ⟨st.stock.cards, o⟩)
    (c' := ⟨st.stock.cards, o'⟩) st.drawStep hwf.step_pos rfl
    hle hres himp hcur hcur' p hp

/-- **R2 (registry rule 2)**: the pass-boundary (pure) cursor is
dominated by any impure cursor on the same cards — a win from the
pass-end state lifts to the mid-pass one.  This is the soundness of
skipping the pure state when a same-cards impure state was refuted
(the measured bigger half of the prize: 912k of the 1.38M doomed
seed-32 draw-3 states).

Proof: `pace_dominance` at the `o`-variant with
`Pace.maskPos_impure_sup_pure` as `hK`. -/
theorem pace_dominance_impure_pure {st : State} {o o' : Nat} (hwf : st.WF)
    (himp : o % st.drawStep ≠ 0)
    (hpure' : o' % st.drawStep = 0 ∨ o' = st.stock.cards.length)
    (hcur : o ≤ st.stock.cards.length) (hcur' : o' ≤ st.stock.cards.length)
    (hsol : { st with stock := { st.stock with cursor := o' } }.macroSolvable) :
    { st with stock := { st.stock with cursor := o } }.macroSolvable := by
  refine pace_dominance (st := { st with stock := { st.stock with cursor := o } })
    (o' := o') (wf_of_cursor hwf hcur) hcur' ?_ hsol
  intro p hp
  exact Pace.maskPos_impure_sup_pure (c := ⟨st.stock.cards, o⟩)
    (c' := ⟨st.stock.cards, o'⟩) st.drawStep hwf.step_pos rfl
    himp hpure' hcur hcur' p hp

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
length`.  At `drawStep = 0` the residue hypothesis forces `o = o'`
(`Nat.mod_zero`), so the statement holds at every step. -/
theorem deal_chain_reaches {st : State} {o o' : Nat}
    (hle : o ≤ o') (hres : o % st.drawStep = o' % st.drawStep)
    (hcur' : o' ≤ st.stock.cards.length) :
    ∃ play, ({ st with stock := { st.stock with cursor := o } }).run play
      = some { st with stock := { st.stock with cursor := o' } } := by
  by_cases hs : 0 < st.drawStep
  · -- extract the deal count: `o' - o` is a multiple of the step
    obtain ⟨k, hkey⟩ : ∃ k, o + k * st.drawStep = o' := by
      have hzm : (o' - o) % st.drawStep = 0 := by
        have hsplit : o' = o + (o' - o) := by omega
        rw [hsplit, Nat.add_mod] at hres
        have hr : o % st.drawStep < st.drawStep := Nat.mod_lt _ hs
        have ht : (o' - o) % st.drawStep < st.drawStep := Nat.mod_lt _ hs
        by_cases hlt : o % st.drawStep + (o' - o) % st.drawStep < st.drawStep
        · rw [Nat.mod_eq_of_lt hlt] at hres
          omega
        · have hams : ∀ (u v : Nat), (u + v) % u = v % u := by
            intro u v
            rw [Nat.add_comm u v,
              show v + u = v + u * 1 from by rw [Nat.mul_one],
              Nat.add_mul_mod_self_left]
          have hred : (o % st.drawStep + (o' - o) % st.drawStep) % st.drawStep
              = o % st.drawStep + (o' - o) % st.drawStep - st.drawStep := by
            have hlt2 : o % st.drawStep + (o' - o) % st.drawStep - st.drawStep
                < st.drawStep := by omega
            have h1 : (o % st.drawStep + (o' - o) % st.drawStep) % st.drawStep
                = (st.drawStep + (o % st.drawStep + (o' - o) % st.drawStep
                    - st.drawStep)) % st.drawStep := by
              have hsum : st.drawStep + (o % st.drawStep + (o' - o) % st.drawStep
                  - st.drawStep) = o % st.drawStep + (o' - o) % st.drawStep := by omega
              rw [hsum]
            rw [h1, hams, Nat.mod_eq_of_lt hlt2]
          rw [hred] at hres
          omega
      refine ⟨(o' - o) / st.drawStep, ?_⟩
      have hdm := Nat.div_add_mod (o' - o) st.drawStep
      rw [hzm, Nat.add_zero, Nat.mul_comm] at hdm
      rw [hdm]
      omega
    have hle2 : o + k * st.drawStep ≤ st.stock.cards.length := by
      rw [hkey]; exact hcur'
    refine ⟨List.replicate k Move.draw, ?_⟩
    rw [run_replicate_draw]
    show some { st with stock := Cycle.dealN st.drawStep k ⟨st.stock.cards, o⟩ }
      = some { st with stock := ⟨st.stock.cards, o'⟩ }
    have hiter := dealOnce_iterate_add hs st.stock.cards k o hle2
    rw [hkey] at hiter
    rw [hiter]
  · have hs0 : st.drawStep = 0 := by omega
    rw [hs0, Nat.mod_zero, Nat.mod_zero] at hres
    subst hres
    exact ⟨[], rfl⟩

/-- The pass-end reachability: every cursor reaches the pass end — the
final deal clamps at `length` from *anywhere*, so the residue condition
drops.  This is why the pass-end state is the worst same-cards state.

Statement repair (2026-09-13, this agent — witness
`witnesses/PaceStepZeroWitness.lean`, machine-checked): gained
`(hstep : 0 < st.drawStep)`.  At step 0 every deal is the identity
below the pass end (`min (c + 0) n = c`), so the pass end is
unreachable from a mid-pass cursor — the clamped chain genuinely needs
a positive step. -/
theorem deal_passEnd_reaches {st : State} {o : Nat}
    (hstep : 0 < st.drawStep)
    (hcur : o ≤ st.stock.cards.length) :
    ∃ play, ({ st with stock := { st.stock with cursor := o } }).run play
      = some { st with stock := { st.stock with cursor := st.stock.cards.length } } := by
  obtain ⟨k, hk⟩ := dealOnce_reach_end hstep st.stock.cards
    (st.stock.cards.length - o) o hcur (Nat.le_refl _)
  refine ⟨List.replicate k Move.draw, ?_⟩
  rw [run_replicate_draw]
  show some { st with stock := Cycle.dealN st.drawStep k ⟨st.stock.cards, o⟩ }
    = some { st with stock := ⟨st.stock.cards, st.stock.cards.length⟩ }
  rw [hk]

/-- **R1, physical-game route**: same residue, earlier cursor —
dominance by reachability (the deal chain), not simulation. -/
theorem pace_dominance_phys_residue {st : State} {o o' : Nat}
    (hle : o ≤ o') (hres : o % st.drawStep = o' % st.drawStep)
    (hcur : o ≤ st.stock.cards.length) (hcur' : o' ≤ st.stock.cards.length)
    (hsol : { st with stock := { st.stock with cursor := o' } }.solvableFrom) :
    { st with stock := { st.stock with cursor := o } }.solvableFrom := by
  have := hcur
  exact solvable_of_reaches (deal_chain_reaches hle hres hcur') hsol

/-- **R2a, physical-game route**: the pass-end cursor is dominated by
every same-cards state — the clamp reaches it from anywhere, so no
residue condition.  (The macro-game `pace_dominance_impure_pure`
additionally covers mid-pass pure cursors via the accessible-superset
— those are *not* reachable from impure ones, which is the
simulation's own content.)

Statement repair (2026-09-13, this agent — witness
`witnesses/PaceStepZeroWitness.lean`): gained `(hstep : 0 <
st.drawStep)`, inherited from `deal_passEnd_reaches` (at step 0 the
pass end is unreachable and the pass-end state can be solvable while
the mid-pass one is not). -/
theorem pace_dominance_phys_passEnd {st : State} {o : Nat}
    (hstep : 0 < st.drawStep)
    (hcur : o ≤ st.stock.cards.length)
    (hsol : ({ st with stock :=
        { st.stock with cursor := st.stock.cards.length } }).solvableFrom) :
    { st with stock := { st.stock with cursor := o } }.solvableFrom :=
  solvable_of_reaches (deal_passEnd_reaches hstep hcur) hsol

/-- The pure-orbit cycle: all pure cursors are mutually reachable by
pure deals — each reaches the pass end (`deal_passEnd_reaches`), the
wrap deal lands 0, and the fresh-pass chain reaches any pure cursor
(`deal_chain_reaches`) — so their solvability is *equivalent*.  This is
the game-level derivation of the engine's `is_pure`/`normalized_offset`
encode merge (the offset normalization draw-3 gets on the pure class);
`maskPos_pure_indep` is its accessibility-level shadow.

Statement repair (2026-09-13, this agent — witness
`witnesses/PaceStepZeroWitness.lean`, machine-checked): gained
`(hstep : 0 < st.drawStep)`.  At step 0 the pure cursors 0 and the pass
end are *not* equivalent (the deal is frozen; the pass-end twin wins by
`deckStack`s the frozen cursor cannot make). -/
theorem solvable_iff_pure_cursors {st : State} {o o' : Nat}
    (hstep : 0 < st.drawStep)
    (hp : o % st.drawStep = 0 ∨ o = st.stock.cards.length)
    (hp' : o' % st.drawStep = 0 ∨ o' = st.stock.cards.length)
    (hcur : o ≤ st.stock.cards.length) (hcur' : o' ≤ st.stock.cards.length) :
    ({ st with stock := { st.stock with cursor := o } }).solvableFrom ↔
    ({ st with stock := { st.stock with cursor := o' } }).solvableFrom := by
  -- the wrap: one deal from the saturated cursor lands the fresh pass
  have hwc : Cycle.dealOnce st.drawStep { st.stock with cursor := st.stock.cards.length }
      = { st.stock with cursor := 0 } := by
    show (if st.stock.cards.length ≥ st.stock.cards.length
        then (⟨st.stock.cards, 0⟩ : Cycle Card)
        else ⟨st.stock.cards, min (st.stock.cards.length + st.drawStep) st.stock.cards.length⟩)
      = ⟨st.stock.cards, 0⟩
    rw [if_pos (Nat.le_refl _)]
  have hwraprun : ({ st with stock := { st.stock with cursor := st.stock.cards.length } } : State).run [Move.draw]
      = some { st with stock := { st.stock with cursor := 0 } } := by
    rw [run_singleton]
    show some { st with stock := Cycle.dealOnce st.drawStep { st.stock with cursor := st.stock.cards.length } }
      = some { st with stock := { st.stock with cursor := 0 } }
    rw [hwc]
  -- every pure cursor is reachable from *every* cursor: through the
  -- pass end, the wrap, and the fresh-pass chain (source purity is not
  -- needed — only the target's, for the last leg)
  have chain : ∀ (x y : Nat), (y % st.drawStep = 0 ∨ y = st.stock.cards.length) →
      x ≤ st.stock.cards.length → y ≤ st.stock.cards.length →
      ∃ play, ({ st with stock := { st.stock with cursor := x } }).run play
        = some { st with stock := { st.stock with cursor := y } } := by
    intro x y hy hxcur hycur
    rcases hy with hym | hye
    · obtain ⟨playA, hA⟩ := deal_passEnd_reaches hstep hxcur
      obtain ⟨playB, hB⟩ := deal_chain_reaches (Nat.zero_le y)
        (by rw [Nat.zero_mod, hym] : 0 % st.drawStep = y % st.drawStep) hycur
      have hstep1 : ({ st with stock := { st.stock with cursor := x } } : State).run
          (playA ++ [Move.draw])
          = some { st with stock := { st.stock with cursor := 0 } } := by
        rw [run_append, hA]
        exact hwraprun
      exact ⟨(playA ++ [Move.draw]) ++ playB, by
        rw [run_append, hstep1]
        exact hB⟩
    · obtain ⟨playA, hA⟩ := deal_passEnd_reaches hstep hxcur
      exact ⟨playA, by rw [hye]; exact hA⟩
  exact solvable_iff_mutuallyReaches (chain o o' hp' hcur hcur') (chain o' o hp hcur' hcur)

/-! ### The window obligation — the gap structure of the pace dominance

When the better state wins and the worse is refuted, the witness of
the difference is a *window card*: a draw the worse cursor cannot
make.  The replay mechanism is the deal commutation
(`deal_commutes_nonStock`): deals float through the non-consuming
prefix, so the cursor at the first consumption is well-defined, and
the worse state replays the line by trimming the deal count. -/

/-- Chaining macro steps distributes over append. -/
theorem macroSteps_append : ∀ (l₁ l₂ : List MacroMove) (s w : State),
    (∃ m, macroSteps s l₁ m ∧ macroSteps m l₂ w) →
    macroSteps s (l₁ ++ l₂) w := by
  intro l₁
  induction l₁ with
  | nil =>
      intro l₂ s w ⟨m, hm, hr⟩
      have hs : s = m := hm
      subst hs
      exact hr
  | cons k krest ih =>
      intro l₂ s w ⟨m, hstepm, hrm⟩
      obtain ⟨st'', hstep, hrest⟩ := hstepm
      exact ⟨st'', hstep, ih l₂ st'' w ⟨m, hrest, hrm⟩⟩

/-- The macro line's shape: either every commitment is a reveal, or the
line splits at the first `drawCommit` with an all-reveal prefix. -/
theorem macroSteps_first_drawCommit : ∀ (ks : List MacroMove) (s w : State),
    macroSteps s ks w →
    (∀ k ∈ ks, ∃ c, k = MacroMove.revealCommit c) ∨
    ∃ pre x rest s₂ s₃, ks = pre ++ MacroMove.drawCommit x :: rest ∧
      (∀ k ∈ pre, ∃ c, k = MacroMove.revealCommit c) ∧
      macroSteps s pre s₂ ∧ macroStep s₂ (MacroMove.drawCommit x) s₃ ∧
      macroSteps s₃ rest w := by
  intro ks
  induction ks with
  | nil => intro s w _; exact Or.inl (fun k hk => nomatch hk)
  | cons k krest ih =>
      intro s w hsteps
      obtain ⟨s', hstep, hrest⟩ := hsteps
      cases k with
      | revealCommit c =>
          rcases ih s' w hrest with
            hall | ⟨pre, x, rest, s₂, s₃, hsplit, hpre, hp₂, hd, hsuf⟩
          · refine Or.inl (fun k' hk' => by
              rcases List.mem_cons.mp hk' with hke | hm
              · exact ⟨c, hke⟩
              · exact hall k' hm)
          · refine Or.inr ⟨MacroMove.revealCommit c :: pre, x, rest, s₂, s₃,
              by simp [hsplit], fun k' hk' => by
                rcases List.mem_cons.mp hk' with hke | hm
                · exact ⟨c, hke⟩
                · exact hpre k' hm,
              ⟨s', hstep, hp₂⟩, hd, hsuf⟩
      | drawCommit x =>
          refine Or.inr ⟨[], x, krest, s, s', rfl, (fun k hk => nomatch hk),
            rfl, hstep, hrest⟩

/-- The reveal-commit prefix replays from any cursor-partner: each
step's accommodation and reveal are cursor-blind, and the stocks and
draw steps are preserved. -/
theorem macroSteps_reveal_blind : ∀ (pre : List MacroMove) (s s' s₁ : State),
    (∀ k ∈ pre, ∃ c, k = MacroMove.revealCommit c) →
    macroSteps s pre s₁ → s.diffCursor s' →
    ∃ s₁', macroSteps s' pre s₁' ∧ s₁.diffCursor s₁' ∧
      s₁.stock = s.stock ∧ s₁'.stock = s'.stock ∧
      s₁.drawStep = s.drawStep ∧ s₁'.drawStep = s'.drawStep := by
  intro pre
  induction pre with
  | nil =>
      intro s s' s₁ _ hsteps hd
      have hs : s = s₁ := hsteps
      subst hs
      exact ⟨s', rfl, hd, rfl, rfl, rfl, rfl⟩
  | cons k krest ih =>
      intro s s' s₁ hall hsteps hd
      obtain ⟨s₂, hstep, hrest⟩ := hsteps
      obtain ⟨c, hc⟩ := hall k (List.mem_cons.mpr (Or.inl rfl))
      subst hc
      obtain ⟨am, hacc, hcom⟩ := hstep
      obtain ⟨play, hplay, hplaym⟩ := hacc
      obtain ⟨t, htrun, hdt, htstock, hsstock, hsds, htds⟩ :=
        accommodates_cursor_blind s s' am play hplaym hd hplay
      have hacct : accommodates s' t := ⟨play, htrun, hplaym⟩
      have hcom' : am.apply (Move.reveal c) = some s₂ := hcom
      obtain ⟨s₂', hs₂', hds₂⟩ := apply_nonConsuming_cursor_blind rfl hdt hcom'
      have hs₂stock : s₂.stock = am.stock :=
        apply_nonConsuming_stock_invar rfl (by intro h; simp at h) hcom'
      have hs₂'stock : s₂'.stock = t.stock :=
        apply_nonConsuming_stock_invar rfl (by intro h; simp at h) hs₂'
      have hs₂ds : s₂.drawStep = am.drawStep := apply_drawStep_invar hcom'
      have hs₂'ds : s₂'.drawStep = t.drawStep := apply_drawStep_invar hs₂'
      obtain ⟨s₁', hrest', hds, hsstock', hs'stock', hsds', hs'ds'⟩ :=
        ih s₂ s₂' s₁ (fun k' hk' => hall k' (List.mem_cons.mpr (Or.inr hk'))) hrest hds₂
      exact ⟨s₁', ⟨s₂', ⟨t, hacct, hs₂'⟩, hrest'⟩, hds,
        by rw [hsstock', hs₂stock, hsstock],
        by rw [hs'stock', hs₂'stock, htstock],
        by rw [hsds', hs₂ds, hsds],
        by rw [hs'ds', hs₂'ds, htds]⟩

/-- A same-residue pair within a positive step: the distance is a step
multiple (the deal-count extraction, shared by the hurry lemma). -/
theorem exists_dealCount {o o' s : Nat} (hs : 0 < s) (hle : o ≤ o')
    (hres : o % s = o' % s) : ∃ k₀, o + k₀ * s = o' := by
  have hzm : (o' - o) % s = 0 := by
    have hsplit : o' = o + (o' - o) := by omega
    rw [hsplit, Nat.add_mod] at hres
    have hr : o % s < s := Nat.mod_lt _ hs
    have ht : (o' - o) % s < s := Nat.mod_lt _ hs
    by_cases hlt : o % s + (o' - o) % s < s
    · rw [Nat.mod_eq_of_lt hlt] at hres
      omega
    · have hams : ∀ (u v : Nat), (u + v) % u = v % u := by
        intro u v
        rw [Nat.add_comm u v,
          show v + u = v + u * 1 from by rw [Nat.mul_one],
          Nat.add_mul_mod_self_left]
      have hred : (o % s + (o' - o) % s) % s
          = o % s + (o' - o) % s - s := by
        have hlt2 : o % s + (o' - o) % s - s < s := by omega
        have h1 : (o % s + (o' - o) % s) % s
            = (s + (o % s + (o' - o) % s - s)) % s := by
          have hsum : s + (o % s + (o' - o) % s - s)
              = o % s + (o' - o) % s := by omega
          rw [hsum]
        rw [h1, hams, Nat.mod_eq_of_lt hlt2]
      rw [hred] at hres
      omega
  refine ⟨(o' - o) / s, ?_⟩
  have hdm := Nat.div_add_mod (o' - o) s
  rw [hzm, Nat.add_zero, Nat.mul_comm] at hdm
  rw [hdm]
  omega

/-- The number of pure deals in a play. -/
def countDraw : List Move → Nat
  | [] => 0
  | Move.draw :: t => countDraw t + 1
  | Move.reveal _ :: t => countDraw t
  | Move.deckPile _ _ :: t => countDraw t
  | Move.deckStack _ :: t => countDraw t
  | Move.pileStack _ :: t => countDraw t
  | Move.stackPile _ _ :: t => countDraw t
  | Move.pilePile _ _ :: t => countDraw t

/-- The first stock-consuming move splits a play. -/
theorem play_first_consumes : ∀ (l : List Move),
    (∃ m, m ∈ l ∧ m.consumesStock = true) →
    ∃ pre m rest, l = pre ++ m :: rest ∧ m.consumesStock = true ∧
      (∀ m' ∈ pre, m'.consumesStock = false) := by
  intro l
  induction l with
  | nil => intro ⟨m, hm, _⟩; exact absurd hm (by simp)
  | cons m t ih =>
      intro hex
      by_cases hc : m.consumesStock = true
      · exact ⟨[], m, t, rfl, hc, fun m' hm' => nomatch hm'⟩
      · obtain ⟨pre, m', rest, hsplit, hc', hnc⟩ := ih (by
          obtain ⟨mm, hmm, hcm⟩ := hex
          refine ⟨mm, ?_, hcm⟩
          rcases List.mem_cons.mp hmm with he | hmem
          · rw [he] at hcm; exact absurd hcm hc
          · exact hmem)
        exact ⟨m :: pre, m', rest, by simp [hsplit], hc', fun m' hm' => by
          rcases List.mem_cons.mp hm' with he | hmem
          · rw [he]
            cases hbool : m.consumesStock with
            | false => rfl
            | true => exact absurd hbool hc
          · exact hnc m' hmem⟩

/-- A non-consuming play replays from any cursor-partner (the draw arm
included — its successor is again a partner). -/
theorem run_nonConsuming_blind : ∀ (l : List Move) (st st' s : State),
    (∀ m ∈ l, m.consumesStock = false) → st.diffCursor st' → st.run l = some s →
    ∃ t, st'.run l = some t ∧ s.diffCursor t := by
  intro l
  induction l with
  | nil =>
      intro st st' s _ hd hrun
      have h0 : st.run [] = some st := rfl
      rw [h0] at hrun
      have hss : st = s := Option.some.inj hrun
      subst hss
      exact ⟨st', rfl, hd⟩
  | cons m t ih =>
      intro st st' s hind hd hrun
      simp only [State.run] at hrun
      cases hsm : st.apply m with
      | none => rw [hsm] at hrun; simp at hrun
      | some s₁ =>
          rw [hsm] at hrun
          have hrest : s₁.run t = some s := hrun
          have hc := hind m (List.mem_cons.mpr (Or.inl rfl))
          obtain ⟨s₁', hs₁', hds₁⟩ := apply_nonConsuming_cursor_blind hc hd hsm
          obtain ⟨u, htrun, hdu⟩ :=
            ih s₁ s₁' s (fun m' hm' => hind m' (List.mem_cons.mpr (Or.inr hm'))) hds₁ hrest
          refine ⟨u, ?_, hdu⟩
          simp only [State.run]
          rw [hs₁']
          exact htrun

/-- An interleaved non-consuming prefix's stock effect is the pure deal
count: the cursor after the prefix is `countDraw` deals from the start. -/
theorem run_stock_deals : ∀ (l : List Move) (st y : State),
    (∀ m ∈ l, m.consumesStock = false) → st.run l = some y →
    y.stock = Cycle.dealN st.drawStep (countDraw l) st.stock ∧
      y.drawStep = st.drawStep := by
  intro l
  induction l with
  | nil =>
      intro st y _ hrun
      have h0 : st.run [] = some st := rfl
      rw [h0] at hrun
      have hss : st = y := Option.some.inj hrun
      subst hss
      exact ⟨rfl, rfl⟩
  | cons m t ih =>
      intro st y hind hrun
      simp only [State.run] at hrun
      cases hsm : st.apply m with
      | none => rw [hsm] at hrun; simp at hrun
      | some s₁ =>
          rw [hsm] at hrun
          have hrest : s₁.run t = some y := hrun
          have hc := hind m (List.mem_cons.mpr (Or.inl rfl))
          obtain ⟨hstock, hds⟩ :=
            ih s₁ y (fun m' hm' => hind m' (List.mem_cons.mpr (Or.inr hm'))) hrest
          cases m with
          | draw =>
              have ha₁ : s₁ = { st with stock := Cycle.dealOnce st.drawStep st.stock } :=
                apply_draw_iff.mp hsm
              rw [ha₁] at hstock hds
              rw [show ({ st with stock := Cycle.dealOnce st.drawStep st.stock } : State).drawStep
                    = st.drawStep from rfl] at hstock hds
              refine ⟨?_, hds⟩
              rw [countDraw, hstock, ← Cycle.dealN_one, Cycle.dealN_add]
          | deckPile c b => simp [Move.consumesStock] at hc
          | deckStack c => simp [Move.consumesStock] at hc
          | reveal c =>
              rw [apply_nonConsuming_stock_invar hc (by intro h; simp at h) hsm] at hstock
              rw [apply_drawStep_invar hsm] at hstock hds
              exact ⟨hstock, hds⟩
          | pileStack c =>
              rw [apply_nonConsuming_stock_invar hc (by intro h; simp at h) hsm] at hstock
              rw [apply_drawStep_invar hsm] at hstock hds
              exact ⟨hstock, hds⟩
          | stackPile c b =>
              rw [apply_nonConsuming_stock_invar hc (by intro h; simp at h) hsm] at hstock
              rw [apply_drawStep_invar hsm] at hstock hds
              exact ⟨hstock, hds⟩
          | pilePile c b =>
              rw [apply_nonConsuming_stock_invar hc (by intro h; simp at h) hsm] at hstock
              rw [apply_drawStep_invar hsm] at hstock hds
              exact ⟨hstock, hds⟩

/-- The paired replay with deal-skipping: from a cursor-partner `b`
whose stock is `j` deals ahead of `a`'s, a non-consuming play replays
with those `j` draws skipped — the end states are partners, and `b`'s
end stock is `j - countDraw l` deals ahead of `a`'s end stock (zero
once the play exhausts the budget, which is the hurry lemma's merge). -/
theorem trim_pair : ∀ (l : List Move) (j : Nat) (a b y : State),
    a.diffCursor b → b.stock = Cycle.dealN a.drawStep j a.stock →
    (∀ m ∈ l, m.consumesStock = false) → a.run l = some y →
    ∃ l' y', b.run l' = some y' ∧ y.diffCursor y' ∧
      y'.stock = Cycle.dealN y.drawStep (j - countDraw l) y.stock := by
  intro l
  induction l with
  | nil =>
      intro j a b y hd hj _ hrun
      have h0 : a.run [] = some a := rfl
      rw [h0] at hrun
      have hss : a = y := Option.some.inj hrun
      subst hss
      refine ⟨[], b, rfl, hd, ?_⟩
      rw [countDraw, Nat.sub_zero]
      exact hj
  | cons m t ih =>
      intro j a b y hd hj hind hrun
      simp only [State.run] at hrun
      cases hsm : a.apply m with
      | none => rw [hsm] at hrun; simp at hrun
      | some a₁ =>
          rw [hsm] at hrun
          have hrest : a₁.run t = some y := hrun
          have hc := hind m (List.mem_cons.mpr (Or.inl rfl))
          cases j with
          | zero =>
              -- the budgets coincide: b *is* a (same stock, same fields)
              have hba : b = a := by
                refine state_ext hd.1.symm hd.2.1.symm hd.2.2.1.symm hd.2.2.2.1.symm ?_
                  hd.2.2.2.2.2.symm
                rw [hj, Cycle.dealN_zero]
              have hself : y.diffCursor y := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
              refine ⟨m :: t, y, ?_, hself, ?_⟩
              · rw [hba]
                simp only [State.run]
                rw [hsm]
                exact hrest
              · rw [Nat.zero_sub, Cycle.dealN_zero]
          | succ j' =>
              cases m with
              | draw =>
              -- b skips this deal
              have ha₁ : a₁ = { a with stock := Cycle.dealOnce a.drawStep a.stock } :=
                apply_draw_iff.mp hsm
              have hda₁ : a₁.diffCursor b := by
                rw [ha₁]
                show a.deal = b.deal ∧ a.board = b.board ∧ a.heights = b.heights ∧
                  a.depths = b.depths ∧
                  (Cycle.dealOnce a.drawStep a.stock).cards = b.stock.cards ∧
                  a.drawStep = b.drawStep
                refine ⟨hd.1, hd.2.1, hd.2.2.1, hd.2.2.2.1, ?_, hd.2.2.2.2.2⟩
                rw [Cycle.dealOnce_cards a.drawStep a.stock]
                exact hd.2.2.2.2.1
              have hinvar : b.stock = Cycle.dealN a₁.drawStep j' a₁.stock := by
                rw [ha₁]
                show b.stock = Cycle.dealN a.drawStep j'
                    (Cycle.dealOnce a.drawStep a.stock)
                rw [hj, ← Cycle.dealN_one, Cycle.dealN_add]
              obtain ⟨l', y', hbrest, hdy, hystock⟩ :=
                ih j' a₁ b y hda₁ hinvar
                  (fun m' hm' => hind m' (List.mem_cons.mpr (Or.inr hm'))) hrest
              refine ⟨l', y', hbrest, hdy, ?_⟩
              rw [countDraw]
              have hsub : j' + 1 - (countDraw t + 1) = j' - countDraw t := by omega
              rw [hsub, hystock]
              | deckPile c b' => simp [Move.consumesStock] at hc
              | deckStack c => simp [Move.consumesStock] at hc
              | reveal c =>
                  obtain ⟨b₁, hb₁, hdb₁⟩ := apply_nonConsuming_cursor_blind hc hd hsm
                  have hinv₁ : b₁.stock = Cycle.dealN a₁.drawStep (j' + 1) a₁.stock := by
                    rw [apply_nonConsuming_stock_invar hc (by intro h; simp at h) hb₁, hj,
                      apply_nonConsuming_stock_invar hc (by intro h; simp at h) hsm,
                      apply_drawStep_invar hsm]
                  obtain ⟨l', y', hbrest, hdy, hystock⟩ :=
                    ih (j' + 1) a₁ b₁ y hdb₁ hinv₁
                      (fun m' hm' => hind m' (List.mem_cons.mpr (Or.inr hm'))) hrest
                  refine ⟨Move.reveal c :: l', y', ?_, hdy, hystock⟩
                  simp only [State.run]
                  rw [hb₁]
                  exact hbrest
              | pileStack c =>
                  obtain ⟨b₁, hb₁, hdb₁⟩ := apply_nonConsuming_cursor_blind hc hd hsm
                  have hinv₁ : b₁.stock = Cycle.dealN a₁.drawStep (j' + 1) a₁.stock := by
                    rw [apply_nonConsuming_stock_invar hc (by intro h; simp at h) hb₁, hj,
                      apply_nonConsuming_stock_invar hc (by intro h; simp at h) hsm,
                      apply_drawStep_invar hsm]
                  obtain ⟨l', y', hbrest, hdy, hystock⟩ :=
                    ih (j' + 1) a₁ b₁ y hdb₁ hinv₁
                      (fun m' hm' => hind m' (List.mem_cons.mpr (Or.inr hm'))) hrest
                  refine ⟨Move.pileStack c :: l', y', ?_, hdy, hystock⟩
                  simp only [State.run]
                  rw [hb₁]
                  exact hbrest
              | stackPile c b' =>
                  obtain ⟨b₁, hb₁, hdb₁⟩ := apply_nonConsuming_cursor_blind hc hd hsm
                  have hinv₁ : b₁.stock = Cycle.dealN a₁.drawStep (j' + 1) a₁.stock := by
                    rw [apply_nonConsuming_stock_invar hc (by intro h; simp at h) hb₁, hj,
                      apply_nonConsuming_stock_invar hc (by intro h; simp at h) hsm,
                      apply_drawStep_invar hsm]
                  obtain ⟨l', y', hbrest, hdy, hystock⟩ :=
                    ih (j' + 1) a₁ b₁ y hdb₁ hinv₁
                      (fun m' hm' => hind m' (List.mem_cons.mpr (Or.inr hm'))) hrest
                  refine ⟨Move.stackPile c b' :: l', y', ?_, hdy, hystock⟩
                  simp only [State.run]
                  rw [hb₁]
                  exact hbrest
              | pilePile c b' =>
                  obtain ⟨b₁, hb₁, hdb₁⟩ := apply_nonConsuming_cursor_blind hc hd hsm
                  have hinv₁ : b₁.stock = Cycle.dealN a₁.drawStep (j' + 1) a₁.stock := by
                    rw [apply_nonConsuming_stock_invar hc (by intro h; simp at h) hb₁, hj,
                      apply_nonConsuming_stock_invar hc (by intro h; simp at h) hsm,
                      apply_drawStep_invar hsm]
                  obtain ⟨l', y', hbrest, hdy, hystock⟩ :=
                    ih (j' + 1) a₁ b₁ y hdb₁ hinv₁
                      (fun m' hm' => hind m' (List.mem_cons.mpr (Or.inr hm'))) hrest
                  refine ⟨Move.pilePile c b' :: l', y', ?_, hdy, hystock⟩
                  simp only [State.run]
                  rw [hb₁]
                  exact hbrest

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

Proof: split at the first consuming move (`play_first_consumes`).  A
stock-free win replays from B verbatim (`run_nonConsuming_blind`) —
contradiction.  Otherwise, if the pre-consumption state's cursor has
reached `o'`, the cursor got there by `countDraw pre` deals; the same
residue means B's stock is `k₀ = (o' − o)/s` deals ahead
(`exists_dealCount`), so B replays the prefix with those `k₀` draws
skipped (`trim_pair` — the budget invariant `b.stock = dealN j a.stock`),
and since the play exhausts the budget (`run_stock_deals` + the
iterate bound — fewer deals would leave the cursor below `o'`), the
end states coincide and B wins — contradiction.  At step 0 the residue
hypothesis forces `o = o'` (Nat.mod_zero), so A is B — vacuous. -/
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
        st₁.stock.cursor < o' := by
  have := hcur
  intro play w hrun hw
  by_cases hex : ∃ m, m ∈ play ∧ m.consumesStock = true
  · -- split at the first consuming move
    obtain ⟨pre, m, rest, hsplit, hcm, hnc⟩ := play_first_consumes play hex
    rw [hsplit, run_append] at hrun
    cases hpre : ({ st with stock := { st.stock with cursor := o } } : State).run pre with
    | none => rw [hpre] at hrun; simp at hrun
    | some st₁ =>
        rw [hpre] at hrun
        have hsuf : st₁.run (m :: rest) = some w := hrun
        by_cases hlt : st₁.stock.cursor < o'
        · exact ⟨pre, m, rest, st₁, hsplit, hcm, hpre, hlt⟩
        · -- the cursor has reached o': B replays the prefix with the
          -- deals trimmed and wins — contradiction
          exfalso
          by_cases hs : 0 < st.drawStep
          · obtain ⟨k₀, hk₀⟩ := exists_dealCount hs hle hres
            have hdiff : ({ st with stock := { st.stock with cursor := o } } : State).diffCursor
                { st with stock := { st.stock with cursor := o' } } :=
              ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
            -- the budget: B's stock is k₀ deals ahead of A's
            have hinv : ({ st with stock := { st.stock with cursor := o' } } : State).stock
                = Cycle.dealN st.drawStep k₀
                  ({ st with stock := { st.stock with cursor := o } } : State).stock := by
              show (⟨st.stock.cards, o'⟩ : Cycle Card)
                  = Cycle.dealN st.drawStep k₀ (⟨st.stock.cards, o⟩ : Cycle Card)
              rw [dealOnce_iterate_add hs st.stock.cards k₀ o
                (by rw [hk₀]; exact hcur'), hk₀]
            obtain ⟨l', y', hy'run, hdy, hystock⟩ :=
              trim_pair pre k₀ { st with stock := { st.stock with cursor := o } }
                { st with stock := { st.stock with cursor := o' } } st₁ hdiff hinv hnc hpre
            -- the play exhausted the budget (else st₁'s cursor < o')
            obtain ⟨hstockcount, _⟩ :=
              run_stock_deals pre { st with stock := { st.stock with cursor := o } } st₁
                hnc hpre
            have hk₀le : k₀ ≤ countDraw pre := by
              apply Classical.byContradiction
              intro hnot
              have h1 : (countDraw pre + 1) * st.drawStep
                  = countDraw pre * st.drawStep + st.drawStep := by
                rw [Nat.add_mul, Nat.one_mul]
              have h2 : (countDraw pre + 1) * st.drawStep ≤ k₀ * st.drawStep :=
                Nat.mul_le_mul (by omega) (Nat.le_refl _)
              have hcontra : o + countDraw pre * st.drawStep < o' := by omega
              rw [show ({ st with stock := { st.stock with cursor := o } } : State).stock
                    = (⟨st.stock.cards, o⟩ : Cycle Card) from rfl] at hstockcount
              rw [dealOnce_iterate_add hs st.stock.cards (countDraw pre) o
                (by omega)] at hstockcount
              exact hlt (by rw [hstockcount]; exact hcontra)
            have hsub : k₀ - countDraw pre = 0 := by omega
            rw [hsub, Cycle.dealN_zero] at hystock
            have hy'eq : y' = st₁ :=
              state_ext hdy.1.symm hdy.2.1.symm hdy.2.2.1.symm hdy.2.2.2.1.symm
                hystock hdy.2.2.2.2.2.symm
            refine hB ⟨l' ++ m :: rest, w, ?_, hw⟩
            rw [run_append, hy'run, hy'eq]
            exact hsuf
          · -- step zero: the residue forces o = o', so A is B
            have hs0 : st.drawStep = 0 := by omega
            rw [hs0, Nat.mod_zero, Nat.mod_zero] at hres
            subst hres
            exact hB hA
  · -- no consuming move: the whole play is cursor-blind — B wins
    exfalso
    have hnc' : ∀ m' ∈ play, m'.consumesStock = false := by
      intro m' hm'
      cases hcb : m'.consumesStock with
      | false => rfl
      | true => exact absurd ⟨m', hm', hcb⟩ hex
    have hdiff : ({ st with stock := { st.stock with cursor := o } } : State).diffCursor
        { st with stock := { st.stock with cursor := o' } } :=
      ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
    obtain ⟨w', hrun', hdw⟩ :=
      run_nonConsuming_blind play { st with stock := { st.stock with cursor := o } }
        { st with stock := { st.stock with cursor := o' } } w hnc' hdiff hrun
    have hh : w.heights = w'.heights := hdw.2.2.1
    have hisw : State.isWin w = State.isWin w' := by
      simp only [State.isWin, hh]
    exact hB ⟨play, w', hrun', by rw [← hisw]; exact hw⟩

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

Proof: split `ks` at the first `drawCommit` (`macroSteps_first_drawCommit`).
An all-reveal line replays from the later state
(`macroSteps_reveal_blind`) and wins — contradiction.  Otherwise the
first `drawCommit`'s card, if accessible at the later cursor, lets the
later state replay the prefix, make the same draw (the merge
`applyDrawTo_merge` / `applyDrawStackTo_merge`), and lift the suffix —
again a contradiction; so the drawn position is outside the later
mask.  No residue condition is needed: the merge works from any
`diffCursor` pair.  `hcur`/`hcur'`/`hA` are vestigial (the argument
runs off the supplied line alone). -/
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
            st.drawStep hwf.step_pos) := by
  have := hcur
  have := hcur'
  have := hA
  have hdiff : ({ st with stock := { st.stock with cursor := o } } : State).diffCursor
      { st with stock := { st.stock with cursor := o' } } :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  intro ks w hsteps hw
  rcases macroSteps_first_drawCommit ks
      { st with stock := { st.stock with cursor := o } } w hsteps with
    hall | ⟨pre, x, rest, s₂, s₃, hsplit, hpre, hpres₂, hdraw, hsuf⟩
  · -- all reveals: the later state replays the line and wins
    exfalso
    obtain ⟨w', hsteps', hdw, _, _, _, _⟩ :=
      macroSteps_reveal_blind ks { st with stock := { st.stock with cursor := o } }
        { st with stock := { st.stock with cursor := o' } } w hall hsteps hdiff
    have hh : w.heights = w'.heights := hdw.2.2.1
    have hisw : State.isWin w = State.isWin w' := by
      simp only [State.isWin, hh]
    exact hB ⟨ks, w', hsteps', by rw [← hisw]; exact hw⟩
  · -- the first drawCommit: the window card
    refine ⟨pre, x, rest, hsplit, hpre, ?_⟩
    intro p hpos hmem
    exfalso
    -- replay the reveal prefix from the later state
    obtain ⟨B₂, hstepsB₂, hdAB₂, hB₂stock, hs₂stock, hs₂ds, hB₂ds⟩ :=
      macroSteps_reveal_blind pre { st with stock := { st.stock with cursor := o } }
        { st with stock := { st.stock with cursor := o' } } s₂ hpre hpres₂ hdiff
    obtain ⟨A₃, haccA, hcomA⟩ := hdraw
    obtain ⟨play, hplay, hplaym⟩ := haccA
    obtain ⟨B₃, hB₃run, hA₃B₃, hB₃stock, hA₃stock, hA₃ds, hB₃ds⟩ :=
      accommodates_cursor_blind s₂ B₂ A₃ play hplaym hdAB₂ hplay
    have hacct : accommodates B₂ B₃ := ⟨play, hB₃run, hplaym⟩
    have hB₃stock' : B₃.stock = { st.stock with cursor := o' } := by
      rw [hB₃stock, hs₂stock]
    have hB₃ds' : B₃.drawStep = st.drawStep := by rw [hB₃ds, hB₂ds]
    have hstepx : 0 < B₃.drawStep := by rw [hB₃ds']; exact hwf.step_pos
    have hposx : B₃.stock.posOf x = some p := by
      rw [hB₃stock', posOf_cards_eq rfl]
      exact hpos
    have hmemx : p ∈ Pace.maskPos B₃.stock B₃.drawStep hstepx :=
      maskPos_mem_trans (show { st.stock with cursor := o' } = B₃.stock from hB₃stock'.symm)
        (show st.drawStep = B₃.drawStep from hB₃ds'.symm) p hmem
    have hxr : B₃.reachablePos x = some p :=
      reachablePos_eq_some_iff.mpr ⟨hstepx, hposx, hmemx⟩
    simp only [commitApplies] at hcomA
    obtain ⟨base, hb⟩ := hcomA
    rcases hb with ⟨hcan, hdt⟩ | hdst
    · -- tableau landing: the same base, the merged successor
      obtain ⟨_, bd, _, hatt, _⟩ := applyDrawTo_iff.mp hdt
      have hattx : B₃.board.attach base x = some bd := by
        rw [← hA₃B₃.2.1]; exact hatt
      have hxdt : B₃.applyDrawTo x base =
          some { B₃ with board := bd, stock := (B₃.stock.drawTo p).removeAt p } :=
        applyDrawTo_iff.mpr ⟨p, bd, hxr, hattx, rfl⟩
      have hmerge : s₃ = { B₃ with board := bd, stock := (B₃.stock.drawTo p).removeAt p } :=
        applyDrawTo_merge hA₃B₃ hdt hxdt
      rw [← hmerge] at hxdt
      exact hB ⟨pre ++ MacroMove.drawCommit x :: rest, w,
        macroSteps_append _ _ _ _ ⟨B₂, hstepsB₂, ⟨s₃, ⟨B₃, hacct, ⟨base, Or.inl ⟨by
          rw [← canPlace_board_congr hA₃B₃.2.1]; exact hcan, hxdt⟩⟩⟩, hsuf⟩⟩, hw⟩
    · -- stack landing
      obtain ⟨_, _, hrk, _⟩ := applyDrawStackTo_iff.mp hdst
      have hrkx : x.rank.toIdx = B₃.heights x.suit := by
        rw [← hA₃B₃.2.2.1]; exact hrk
      have hxds' : B₃.applyDrawStackTo x =
          some { B₃ with
            stock := (B₃.stock.drawTo p).removeAt p,
            heights := fun s => if s = x.suit then B₃.heights s + 1 else B₃.heights s } :=
        applyDrawStackTo_iff.mpr ⟨p, hxr, hrkx, rfl⟩
      have hmerge : s₃ = { B₃ with
            stock := (B₃.stock.drawTo p).removeAt p,
            heights := fun s => if s = x.suit then B₃.heights s + 1 else B₃.heights s } :=
        applyDrawStackTo_merge hA₃B₃ hdst hxds'
      rw [← hmerge] at hxds'
      exact hB ⟨pre ++ MacroMove.drawCommit x :: rest, w,
        macroSteps_append _ _ _ _ ⟨B₂, hstepsB₂, ⟨s₃, ⟨B₃, hacct, ⟨base, Or.inr hxds'⟩⟩,
          hsuf⟩⟩, hw⟩

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
