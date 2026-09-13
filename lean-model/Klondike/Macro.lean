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

TODO(proof) [M] (downgraded — the simulation is proved): instantiate
`macroSolvable_of_simulates` with `R := diffCursor ∧ the maskPos
superset`; the reveal case via `apply_nonConsuming_cursor_blind`
(accommodations too — the shuffles are non-consuming), the draw case
via `applyDrawTo_merge` / `applyDrawStackTo_merge` — the merge
disjunct: after one draw the states are equal and the superset is
moot.  `hstep` from `hwf.step_pos`, `hcur` from `hwf.cursor_le`. -/
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
is all `revealCommit` — the two-kind move set); replay it from the
o'-state (`apply_nonConsuming_cursor_blind` — the reveals and the
accommodation shuffles); the merge (`applyDrawTo_merge` /
`applyDrawStackTo_merge`) gives the successor; the suffix lifts
verbatim. -/
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
