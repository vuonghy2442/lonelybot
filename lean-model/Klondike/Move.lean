import Klondike.Pace

/-!
# Moves: the one semantic function

The model is the *full physical game* — `pilePile` included.  The
engine's restricted move set (no pile→pile; no_pile_to_pile.md) is the
predicate `Move.isEngine`, and the restriction's soundness — the
ledger's B-legs — is the theorem `solvable_engine_iff`: one model, a
move subset, an equivalence — not two formalizations and a
correspondence.

`apply : Move → State → Option State` is the single source of truth;
`legal`, and everything downstream, derives from it.  The stock moves
are the physical pair — deal (`draw`, clamped at the pass end and
wrapping from it, deck.rs's `offset_once`) and play the waste top
(`deckPile`/`deckStack`) — correct at every draw step.  The
Draw-commitment jump (`applyDrawTo`) is the derived macro, guarded by
the accessible set (Pace's K+ mask).
-/

/-- A move in the physical game. -/
inductive Move : Type where
  /-- Deal `drawStep` cards to the waste: clamped at the pass end (the
  partial final deal passes the last card), wrapping from the end to a
  fresh pass. -/
  | draw
  /-- Reveal the hidden card under the visible card `c`. -/
  | reveal (c : Card)
  /-- Waste top `c` onto the tableau base `b`. -/
  | deckPile (c : Card) (b : Base)
  /-- Waste top `c` onto the foundation. -/
  | deckStack (c : Card)
  /-- Visible top `c` onto the foundation. -/
  | pileStack (c : Card)
  /-- Foundation top `c` back onto the tableau base `b`. -/
  | stackPile (c : Card) (b : Base)
  /-- Move the visible card `c` — with its whole run — onto the
  tableau base `b`.  In the matching this is a one-edge rewire: the
  cards above `c` keep their edges to `c` and follow for free. -/
  | pilePile (c : Card) (b : Base)
  deriving DecidableEq

/-- The engine's restricted move set: everything but pile→pile. -/
def Move.isEngine : Move → Bool
  | .draw => true
  | .reveal _ => true
  | .deckPile _ _ => true
  | .deckStack _ => true
  | .pileStack _ => true
  | .stackPile _ _ => true
  | .pilePile _ _ => false

/-- Twin-swap on moves. -/
def Move.flipMove : Move → Move
  | .draw => .draw
  | .reveal c => .reveal c.flipSuit
  | .deckPile c b => .deckPile c.flipSuit b.flipBase
  | .deckStack c => .deckStack c.flipSuit
  | .pileStack c => .pileStack c.flipSuit
  | .stackPile c b => .stackPile c.flipSuit b.flipBase
  | .pilePile c b => .pilePile c.flipSuit b.flipBase

namespace State

/-- One deal: the physical stock advance (deck.rs `offset_once`). -/
def applyDraw (st : State) : Option State :=
  some { st with stock := st.stock.dealOnce st.drawStep }

def applyReveal (st : State) (c : Card) : Option State :=
  match st.board.topOf (Sum.inr c) with
  | some _ => none
  | none =>
    match st.board.bottomOf c with
    | some (Sum.inr r) =>
      match st.pileOfTopHidden r with
      | none => none
      | some a =>
        match st.board.attach (st.hiddenBase a) r with
        | none => none
        | some bd =>
          some { st with
            board := bd,
            depths := fun a' => if a' = a then st.depths a - 1 else st.depths a' }
    | _ => none

def applyDeckPile (st : State) (c : Card) (b : Base) : Option State :=
  match st.stock.prev with
  | none => none
  | some c' =>
      if c' = c ∧ st.canPlace c b then
        match st.board.attach b c with
        | none => none
        | some bd =>
            some { st with board := bd, stock := st.stock.removeAt (st.stock.cursor - 1) }
      else none

def applyDeckStack (st : State) (c : Card) : Option State :=
  match st.stock.prev with
  | none => none
  | some c' =>
      if c' = c ∧ c.rank.toIdx = st.heights c.suit then
        some { st with
          stock := st.stock.removeAt (st.stock.cursor - 1),
          heights := fun s => if s = c.suit then st.heights s + 1 else st.heights s }
      else none

def applyPileStack (st : State) (c : Card) : Option State :=
  match st.board.topOf (Sum.inr c), st.board.bottomOf c with
  | none, some b =>
      if c.rank.toIdx = st.heights c.suit then
        some { st with
          board := st.board.detach b,
          heights := fun s => if s = c.suit then st.heights s + 1 else st.heights s }
      else none
  | _, _ => none

def applyStackPile (st : State) (c : Card) (b : Base) : Option State :=
  if c.rank.toIdx + 1 = st.heights c.suit ∧ st.canPlace c b then
    match st.board.attach b c with
    | none => none
    | some bd =>
        some { st with
          board := bd,
          heights := fun s => if s = c.suit then st.heights s - 1 else st.heights s }
  else none

/-- Can the run rooted at `c` land on `b`?  (`b` free, `c` fits, and
`b` is not part of the run being moved — the self-landing guard.) -/
def canMoveRun (st : State) (c : Card) (b : Base) : Bool :=
  st.canPlace c b &&
  match b with
  | Sum.inl _ => true
  | Sum.inr d => !(st.board.aboveOf c).contains d

def applyPilePile (st : State) (c : Card) (b : Base) : Option State :=
  match st.board.bottomOf c with
  | none => none
  | some b₀ =>
      if b₀ ≠ b ∧ st.canMoveRun c b then
        match (st.board.detach b₀).attach b c with
        | some bd => some { st with board := bd }
        | none => none
      else none

/-- The one semantic function: apply a move, or `none` if illegal.
`legal` and everything downstream derives from this. -/
def apply : Move → State → Option State
  | .draw, st => st.applyDraw
  | .reveal c, st => st.applyReveal c
  | .deckPile c b, st => st.applyDeckPile c b
  | .deckStack c, st => st.applyDeckStack c
  | .pileStack c, st => st.applyPileStack c
  | .stackPile c b, st => st.applyStackPile c b
  | .pilePile c b, st => st.applyPilePile c b

/-- Legality, derived from `apply` (single source of truth). -/
def legal (st : State) (m : Move) : Bool := (st.apply m).isSome

/-- Running a play. -/
def run (st : State) : List Move → Option State
  | [] => some st
  | m :: ms => match st.apply m with
    | some st' => st'.run ms
    | none => none

/-- All four foundations complete. -/
def isWin (st : State) : Bool :=
  Suit.all.all fun s => decide (st.heights s = 13)

/-- Solvability: a winning play exists (witness-as-data). -/
def solvableFrom (st : State) : Prop :=
  ∃ play : List Move, ∃ st', st.run play = some st' ∧ st'.isWin = true

/-- Solvability using only engine moves (the no-pile-to-pile
restriction). -/
def solvableEngine (st : State) : Prop :=
  ∃ play : List Move, (∀ m ∈ play, m.isEngine = true) ∧
    ∃ st', st.run play = some st' ∧ st'.isWin = true

/-- The reachable position of `c`: its stock position, when the
physical deal can bring `c` to the waste top — the K+ accessible-set
guard (`Pace.maskPos`; `0 < drawStep` per WF's `step_pos`).  The Draw
commitments jump there; at draw-1 it is always the plain position
(`reachablePos_step1`, the free-set degeneration). -/
def reachablePos (st : State) (c : Card) : Option Nat :=
  if hstep : 0 < st.drawStep then
    match st.stock.posOf c with
    | none => none
    | some i => if i ∈ Pace.maskPos st.stock st.drawStep hstep then some i else none
  else none

/-- The macro-style `Draw(c)` commitment — the derived jump: deal
until `c` is the waste top, then place it at `b` (the engine's
`DeckPile` before the sweep optimization).  The jump is legal exactly
when `c` is reachable (`reachablePos`, the K+ mask) — the pacing
guard that makes the commitment engine-faithful at every draw step.
Last-position draws saturate the cursor at the pass end. -/
def applyDrawTo (st : State) (c : Card) (b : Base) : Option State :=
  match st.reachablePos c with
  | none => none
  | some i =>
    match st.board.attach b c with
    | none => none
    | some bd =>
      some { st with board := bd, stock := (st.stock.drawTo i).removeAt i }

/-- The safe-stack `Draw(c)` commitment — the derived jump with the
reachable-position guard (as `applyDrawTo`): deal until `c` is the
waste top, then stack it on the foundation. -/
def applyDrawStackTo (st : State) (c : Card) : Option State :=
  match st.reachablePos c with
  | none => none
  | some i =>
    if c.rank.toIdx = st.heights c.suit then
      some { st with
        stock := (st.stock.drawTo i).removeAt i,
        heights := fun s => if s = c.suit then st.heights s + 1 else st.heights s }
    else none

/-- The draw-1 degeneration, game level: every in-stock card is
reachable — the guard is trivial and the Draw commitment is the plain
jump.  C9's premise ("jumping the offset never forfeits a card"),
definitional at step 1; the deal-side content is `Pace.maskPos_step1`. -/
theorem reachablePos_step1 {st : State} (hwf : st.WF) (hstep : st.drawStep = 1)
    (c : Card) : st.reachablePos c = st.stock.posOf c := by
  have hcur := hwf.cursor_le
  simp only [reachablePos, hstep]
  cases hp : st.stock.posOf c with
  | none => rfl
  | some i =>
    have hlt : i < st.stock.cards.length := Cycle.posOf_lt hp
    have hmem : i ∈ Pace.maskPos st.stock 1 (by omega : (0 : Nat) < 1) :=
      (Pace.maskPos_step1 st.stock (by omega) hcur i).mpr hlt
    rw [dif_pos (by omega : (0 : Nat) < 1)]
    exact if_pos hmem

end State

/-! ## The farmable statements -/

/-- Legality characterization of `pileStack` — the engine bridge
(`gen_moves` PileStack: visible, top of pile, rank = height). -/
theorem legal_pileStack_iff {st : State} {c : Card} :
    st.legal (Move.pileStack c) = true ↔
      (st.board.bottomOf c ≠ none ∧ st.board.topOf (Sum.inr c) = none ∧
       c.rank.toIdx = st.heights c.suit) := by
  constructor
  · intro h
    simp only [State.legal, State.apply, State.applyPileStack] at h
    split at h
    · split at h
      · simp_all
      · exact absurd h (by decide)
    · exact absurd h (by decide)
  · intro h
    obtain ⟨hb, ht, hr⟩ := h
    simp only [State.legal, State.apply, State.applyPileStack]
    cases hbot : st.board.bottomOf c with
    | none => exact absurd hbot hb
    | some b =>
        rw [ht]
        show (if c.rank.toIdx = st.heights c.suit then some { st with
              board := st.board.detach b,
              heights := fun s => if s = c.suit then st.heights s + 1 else st.heights s }
            else none).isSome = true
        rw [if_pos hr]
        rfl



/-! ## The move inversions — one shape lemma per move

The unpacking ritual (`simp only [State.apply, applyXxx]`, per-
discriminant `cases h : e` + `rw [h] at h`, full `simp at h` to
decompose the ite-vs-some) paid once, here, for every consumer:
future proofs open with `rw [apply_X_iff] at h` and destructure the
conjuncts — no more case bash per theorem.  The guard conjuncts are
chosen decidable-flat (equalities and `= true`s) so `obtain` splits
them in one step. -/

/-- `draw` always succeeds: one deal. -/
theorem apply_draw_iff {st st' : State} :
    st.apply Move.draw = some st' ↔
      st' = { st with stock := st.stock.dealOnce st.drawStep } := by
  constructor
  · intro h
    exact (Option.some.inj h).symm
  · intro h
    rw [h]
    rfl

/-- `reveal`'s shape: the trigger card's top must be free, and the
reveal chain (bottom is a hidden card, that card is a pile's boundary,
the attach succeeds) delivers the boundary as the new board top with
the pile's depth stepped down. -/
theorem apply_reveal_iff {st st' : State} {c : Card} :
    st.apply (Move.reveal c) = some st' ↔
      (st.board.topOf (Sum.inr c) = none ∧
       ∃ r a bd, st.board.bottomOf c = some (Sum.inr r) ∧
         st.pileOfTopHidden r = some a ∧
         st.board.attach (st.hiddenBase a) r = some bd ∧
         st' = { st with
           board := bd,
           depths := fun a' => if a' = a then st.depths a - 1 else st.depths a' }) := by
  constructor
  · intro h
    simp only [State.apply, State.applyReveal] at h
    cases ht : st.board.topOf (Sum.inr c) with
    | some _ => rw [ht] at h; exact absurd h (by simp)
    | none =>
      cases hb : st.board.bottomOf c with
      | none => rw [ht, hb] at h; exact absurd h (by simp)
      | some b =>
        cases b with
        | inl _ => rw [ht, hb] at h; exact absurd h (by simp)
        | inr r =>
          rw [ht, hb] at h
          simp at h
          cases hp : st.pileOfTopHidden r with
          | none => rw [hp] at h; exact absurd h (by simp)
          | some a =>
            rw [hp] at h
            simp at h
            cases ha : st.board.attach (st.hiddenBase a) r with
            | none => rw [ha] at h; exact absurd h (by simp)
            | some bd =>
              rw [ha] at h
              have h' : some { st with
                  board := bd,
                  depths := fun a' => if a' = a then st.depths a - 1 else st.depths a' }
                  = some st' := h
              rw [Option.some.injEq] at h'
              exact ⟨rfl, r, a, bd, rfl, hp, ha, h'.symm⟩
  · intro ⟨ht, r, a, bd, hb, hp, ha, hst⟩
    rw [hst]
    simp only [State.apply, State.applyReveal, ht, hb, hp, ha]

/-- `deckPile`'s shape: the waste top is the played card, the base is
free and fitting, and the spliced-out stock. -/
theorem apply_deckPile_iff {st st' : State} {c : Card} {b : Base} :
    st.apply (Move.deckPile c b) = some st' ↔
      (st.stock.prev = some c ∧ st.canPlace c b = true ∧
       ∃ bd, st.board.attach b c = some bd ∧
         st' = { st with
                 board := bd,
                 stock := st.stock.removeAt (st.stock.cursor - 1) }) := by
  constructor
  · intro h
    simp only [State.apply, State.applyDeckPile] at h
    cases hp : st.stock.prev with
    | none => rw [hp] at h; exact absurd h (by simp)
    | some c' =>
      rw [hp] at h
      cases hatt : st.board.attach b c with
      | none => rw [hatt] at h; exact absurd h (by simp)
      | some bd =>
        rw [hatt] at h
        simp at h
        obtain ⟨⟨h1, h2⟩, h3⟩ := h
        exact ⟨congrArg some h1, h2, bd, rfl, h3.symm⟩
  · intro ⟨hp, hcp, bd, hatt, hst⟩
    rw [hst]
    simp only [State.apply, State.applyDeckPile, hp, hatt]
    split
    · rfl
    · rename_i hcond
      simp [hcp] at hcond

/-- `deckStack`'s shape: the waste top is the next foundation card. -/
theorem apply_deckStack_iff {st st' : State} {c : Card} :
    st.apply (Move.deckStack c) = some st' ↔
      (st.stock.prev = some c ∧ c.rank.toIdx = st.heights c.suit ∧
       st' = { st with
         stock := st.stock.removeAt (st.stock.cursor - 1),
         heights := fun s => if s = c.suit then st.heights s + 1 else st.heights s }) := by
  constructor
  · intro h
    simp only [State.apply, State.applyDeckStack] at h
    cases hp : st.stock.prev with
    | none => rw [hp] at h; exact absurd h (by simp)
    | some c' =>
      rw [hp] at h
      simp at h
      obtain ⟨⟨h1, h2⟩, h3⟩ := h
      exact ⟨congrArg some h1, h2, h3.symm⟩
  · intro ⟨hp, hrk, hst⟩
    rw [hst]
    simp only [State.apply, State.applyDeckStack, hp]
    split
    · rfl
    · rename_i hcond
      simp [hrk] at hcond

/-- `pileStack`'s shape (the successor form of `legal_pileStack_iff`). -/
theorem apply_pileStack_iff {st st' : State} {c : Card} :
    st.apply (Move.pileStack c) = some st' ↔
      (st.board.topOf (Sum.inr c) = none ∧
       ∃ b, st.board.bottomOf c = some b ∧
         c.rank.toIdx = st.heights c.suit ∧
         st' = { st with
           board := st.board.detach b,
           heights := fun s => if s = c.suit then st.heights s + 1 else st.heights s }) := by
  constructor
  · intro h
    simp only [State.apply, State.applyPileStack] at h
    cases ht : st.board.topOf (Sum.inr c) with
    | some _ => rw [ht] at h; exact absurd h (by simp)
    | none =>
      cases hb : st.board.bottomOf c with
      | none => rw [ht, hb] at h; exact absurd h (by simp)
      | some b =>
        rw [ht, hb] at h
        simp at h
        obtain ⟨h1, h2⟩ := h
        exact ⟨rfl, b, rfl, h1, h2.symm⟩
  · intro ⟨ht, b, hb, hrk, hst⟩
    rw [hst]
    simp only [State.apply, State.applyPileStack, ht, hb]
    split
    · rfl
    · rename_i hcond
      simp [hrk] at hcond

/-- `stackPile`'s shape: the un-stack guard (`c` is exactly the card
the foundation expects back) plus the base conditions. -/
theorem apply_stackPile_iff {st st' : State} {c : Card} {b : Base} :
    st.apply (Move.stackPile c b) = some st' ↔
      (c.rank.toIdx + 1 = st.heights c.suit ∧ st.canPlace c b = true ∧
       ∃ bd, st.board.attach b c = some bd ∧
         st' = { st with
           board := bd,
           heights := fun s => if s = c.suit then st.heights s - 1 else st.heights s }) := by
  constructor
  · intro h
    simp only [State.apply, State.applyStackPile] at h
    cases hatt : st.board.attach b c with
    | none => rw [hatt] at h; exact absurd h (by simp)
    | some bd =>
      rw [hatt] at h
      simp at h
      obtain ⟨⟨h1, h2⟩, h3⟩ := h
      exact ⟨h1, h2, bd, rfl, h3.symm⟩
  · intro ⟨h1, h2, bd, hatt, hst⟩
    rw [hst]
    simp only [State.apply, State.applyStackPile, hatt]
    split
    · rfl
    · rename_i hcond
      simp [h1, h2] at hcond

/-- `pilePile`'s shape: the run-rooted move to a different, landable
base. -/
theorem apply_pilePile_iff {st st' : State} {c : Card} {b : Base} :
    st.apply (Move.pilePile c b) = some st' ↔
      (∃ b₀, st.board.bottomOf c = some b₀ ∧
         b₀ ≠ b ∧ st.canMoveRun c b = true ∧
         ∃ bd, (st.board.detach b₀).attach b c = some bd ∧
           st' = { st with board := bd }) := by
  constructor
  · intro h
    simp only [State.apply, State.applyPilePile] at h
    cases hb : st.board.bottomOf c with
    | none => rw [hb] at h; exact absurd h (by simp)
    | some b₀ =>
      rw [hb] at h
      simp at h
      cases hatt : (st.board.detach b₀).attach b c with
      | none => rw [hatt] at h; exact absurd h (by simp)
      | some bd =>
        rw [hatt] at h
        simp at h
        obtain ⟨⟨h1, h2⟩, h3⟩ := h
        exact ⟨b₀, rfl, h1, h2, bd, hatt, h3.symm⟩
  · intro ⟨b₀, hb, h1, h2, bd, hatt, hst⟩
    rw [hst]
    simp only [State.apply, State.applyPilePile, hb, hatt]
    split
    · rfl
    · rename_i hcond
      simp [h1, h2] at hcond

/-! ## Update arithmetic — the heights/depths step lemmas

The apply-successors carry `heights := fun s => if s = c.suit then …`
updates; symbolic ite conditions do not whnf, so every consumer paid
`rw [if_pos rfl]` / `if_neg` dances.  These fire on the exact literal
shapes (post-unfold, pre-simplification). -/

@[simp] theorem heights_bump_self {st : State} {c : Card} :
    ({ st with heights := fun s => if s = c.suit then st.heights s + 1 else st.heights s }
      : State).heights c.suit = st.heights c.suit + 1 := by
  show (if c.suit = c.suit then st.heights c.suit + 1 else st.heights c.suit) = _
  rw [if_pos rfl]

@[simp] theorem heights_bump_ne {st : State} {c : Card} {s : Suit} (h : s ≠ c.suit) :
    ({ st with heights := fun s' => if s' = c.suit then st.heights s' + 1 else st.heights s' }
      : State).heights s = st.heights s := by
  show (if s = c.suit then st.heights s + 1 else st.heights s) = st.heights s
  rw [if_neg h]

@[simp] theorem heights_drop_self {st : State} {c : Card} :
    ({ st with heights := fun s => if s = c.suit then st.heights s - 1 else st.heights s }
      : State).heights c.suit = st.heights c.suit - 1 := by
  show (if c.suit = c.suit then st.heights c.suit - 1 else st.heights c.suit) = _
  rw [if_pos rfl]

@[simp] theorem heights_drop_ne {st : State} {c : Card} {s : Suit} (h : s ≠ c.suit) :
    ({ st with heights := fun s' => if s' = c.suit then st.heights s' - 1 else st.heights s' }
      : State).heights s = st.heights s := by
  show (if s = c.suit then st.heights s - 1 else st.heights s) = st.heights s
  rw [if_neg h]

@[simp] theorem depths_step_self {st : State} {a : Anchor} :
    ({ st with depths := fun a' => if a' = a then st.depths a - 1 else st.depths a' }
      : State).depths a = st.depths a - 1 := by
  show (if a = a then st.depths a - 1 else st.depths a) = _
  rw [if_pos rfl]

@[simp] theorem depths_step_ne {st : State} {a a' : Anchor} (h : a' ≠ a) :
    ({ st with depths := fun a'' => if a'' = a then st.depths a - 1 else st.depths a'' }
      : State).depths a' = st.depths a' := by
  show (if a' = a then st.depths a - 1 else st.depths a') = st.depths a'
  rw [if_neg h]

/-! ## Maintenance helpers for `apply_wf`

Index-level facts the WF maintenance lemma needs: the `removeIdx`
splice, the `posOf`-membership bridge, rank injectivity (the +1
height bound), the deal's piles/stock disjointness, and `reveal`'s
hidden-slice lemmas (the boundary's dealt-parent decomposition). -/

/-- Ranks are determined by their numeric view. -/
theorem Rank.toIdx_inj {r r' : Rank} (h : r.toIdx = r'.toIdx) : r = r' := by
  cases r <;> cases r' <;> simp_all [Rank.toIdx]

namespace Cycle

/-- The none half of `findFirstIdx`. -/
theorem findFirstIdx_eq_none {α : Type} (p : α → Bool) : ∀ (l : List α),
    (∀ x ∈ l, p x ≠ true) → findFirstIdx p l = none := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons a t ih =>
    intro h
    simp only [findFirstIdx]
    rw [if_neg (h a List.mem_cons_self)]
    rw [ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]
    rfl

/-- A member is found by its finder. -/
theorem findFirstIdx_mem {α : Type} [DecidableEq α] (x : α) : ∀ (l : List α),
    x ∈ l → findFirstIdx (fun y => decide (y = x)) l ≠ none := by
  intro l
  induction l with
  | nil => intro h; cases h
  | cons a t ih =>
    intro h
    rcases List.mem_cons.mp h with rfl | h
    · simp [findFirstIdx]
    · have hind := ih h
      simp only [findFirstIdx]
      by_cases hdf : decide (a = x) = true
      · simp [hdf]
      · rw [if_neg hdf]
        cases hfind : findFirstIdx (fun y => decide (y = x)) t with
        | none => exact absurd hfind hind
        | some k => simp

/-- A card outside the cycle's cards has no position. -/
theorem posOf_eq_none {c : Card} {cy : Cycle Card} (h : c ∉ cy.cards) :
    cy.posOf c = none := by
  simp only [posOf]
  refine findFirstIdx_eq_none _ cy.cards (fun x hx => ?_)
  intro hcon
  rw [decide_eq_true_eq] at hcon
  exact h (hcon ▸ hx)

/-- A card in the cycle's cards has a position. -/
theorem posOf_mem {c : Card} {cy : Cycle Card} (h : c ∈ cy.cards) :
    cy.posOf c ≠ none :=
  findFirstIdx_mem c cy.cards h

/-- Splicing out index `i` shifts later indices down by one. -/
theorem getElem?_removeIdx {α : Type} :
    ∀ (l : List α) (i j : Nat),
      (removeIdx l i)[j]? = if j < i then l[j]? else l[j + 1]? := by
  intro l
  induction l with
  | nil =>
    intro i j
    simp only [removeIdx_nil, List.getElem?_nil]
    split <;> rfl
  | cons a t ih =>
    intro i
    cases i with
    | zero =>
      intro j
      simp only [removeIdx_zero, List.getElem?_cons_succ]
      rw [if_neg (Nat.not_lt_zero j)]
    | succ n =>
      intro j
      cases j with
      | zero =>
        simp only [removeIdx_succ, List.getElem?_cons_zero]
        rw [if_pos (Nat.zero_lt_succ n)]
      | succ m =>
        simp only [removeIdx_succ, List.getElem?_cons_succ]
        by_cases hm : m < n
        · rw [if_pos (by omega : m + 1 < n + 1)]
          exact (ih n m).trans (if_pos hm)
        · rw [if_neg (by omega : ¬(m + 1 < n + 1))]
          exact (ih n m).trans (if_neg hm)

/-- Splicing keeps only the original members. -/
theorem mem_removeIdx {α : Type} : ∀ (l : List α) (i : Nat) {x : α},
    x ∈ removeIdx l i → x ∈ l := by
  intro l
  induction l with
  | nil => intro i x h; simp only [removeIdx_nil] at h; cases h
  | cons a t ih =>
    intro i x hmem
    cases i with
    | zero =>
      simp only [removeIdx_zero] at hmem
      exact List.mem_cons_of_mem _ hmem
    | succ n =>
      simp only [removeIdx_succ] at hmem
      rcases List.mem_cons.mp hmem with rfl | hmem
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih n hmem)

/-- A card at a unique index does not survive its own splice. -/
theorem notMem_removeIdx_self {α : Type} {l : List α} {i : Nat} {x : α}
    (hind : ∀ j, l[j]? = some x → j = i) : x ∉ removeIdx l i := by
  intro hmem
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hmem
  rw [getElem?_removeIdx] at hj
  by_cases h : j < i
  · rw [if_pos h] at hj
    have := hind j hj
    omega
  · rw [if_neg h] at hj
    have := hind (j + 1) hj
    omega

end Cycle

/-- Reversal exchanges head and last (the `hiddenBase` walk). -/
theorem head?_reverse_eq_getLast? {α : Type} :
    ∀ (l : List α), l.reverse.head? = l.getLast? := by
  intro l
  induction l with
  | nil => rfl
  | cons a t ih =>
    cases t with
    | nil => rfl
    | cons b u =>
      cases hrev : (b :: u).reverse with
      | nil =>
        exfalso
        have ht := congrArg List.reverse hrev
        rw [List.reverse_reverse] at ht
        simp at ht
      | cons z zs =>
        rw [show (a :: b :: u).reverse = z :: (zs ++ [a]) from by
          rw [List.reverse_cons, hrev, List.cons_append]]
        rw [hrev] at ih
        exact ih

/-- A `take` slice that is a single card means the list starts there. -/
theorem head?_of_take_single {α : Type} {l : List α} {n : Nat} {x : α}
    (h : l.take n = [x]) : l.head? = some x := by
  cases l with
  | nil => simp at h
  | cons a t =>
    cases n with
    | zero => simp at h
    | succ m =>
      rw [show List.take (m + 1) (a :: t) = a :: List.take m t from rfl] at h
      rw [List.cons.injEq] at h
      obtain ⟨rfl, -⟩ := h
      rfl

/-- Splicing never lengthens. -/
theorem removeIdx_length_le {α : Type} : ∀ (l : List α) (i : Nat),
    (Cycle.removeIdx l i).length ≤ l.length := by
  intro l
  induction l with
  | nil => intro i; simp
  | cons a t ih =>
    intro i
    cases i with
    | zero => simp
    | succ n =>
      simp only [Cycle.removeIdx, List.length_cons]
      have := ih n
      omega

/-- Splicing out-of-range is the identity. -/
theorem removeIdx_of_length_le {α : Type} : ∀ (l : List α) (i : Nat),
    l.length ≤ i → Cycle.removeIdx l i = l := by
  intro l
  induction l with
  | nil => intro i _; rfl
  | cons a t ih =>
    intro i hi
    cases i with
    | zero => simp at hi
    | succ n =>
      simp only [Cycle.removeIdx, List.length_cons] at hi ⊢
      rw [ih n (by omega)]

/-- Splicing preserves index-wise distinctness. -/
theorem noDupCards_removeIdx : ∀ (l : List Card) (i : Nat),
    noDupCards l → noDupCards (Cycle.removeIdx l i) := by
  intro l
  induction l with
  | nil => intro i _ j j' hj _ _; simp at hj
  | cons a t ih =>
    intro i hnd j j' hj hj' heq
    have h1 := Cycle.getElem?_removeIdx (a :: t) i j
    have h2 := Cycle.getElem?_removeIdx (a :: t) i j'
    rw [h1, h2] at heq
    by_cases hic : i < (a :: t).length
    · have hbl : (Cycle.removeIdx (a :: t) i).length + 1 = (a :: t).length :=
        Cycle.removeIdx_length _ i hic
      by_cases hc1 : j < i
      · by_cases hc2 : j' < i
        · rw [if_pos hc1, if_pos hc2] at heq
          have := hnd j j' (by omega) (by omega) heq
          omega
        · rw [if_pos hc1, if_neg hc2] at heq
          have := hnd j (j' + 1) (by omega) (by omega) heq
          omega
      · by_cases hc2 : j' < i
        · rw [if_neg hc1, if_pos hc2] at heq
          have := hnd (j + 1) j' (by omega) (by omega) heq
          omega
        · rw [if_neg hc1, if_neg hc2] at heq
          have := hnd (j + 1) (j' + 1) (by omega) (by omega) heq
          omega
    · have hle : Cycle.removeIdx (a :: t) i = (a :: t) :=
        removeIdx_of_length_le _ i (by omega)
      rw [hle] at hj hj'
      by_cases hc1 : j < i
      · by_cases hc2 : j' < i
        · rw [if_pos hc1, if_pos hc2] at heq
          have := hnd j j' (by omega) (by omega) heq
          omega
        · rw [if_pos hc1, if_neg hc2] at heq
          have := hnd j (j' + 1) (by omega) (by omega) heq
          omega
      · by_cases hc2 : j' < i
        · rw [if_neg hc1, if_pos hc2] at heq
          have := hnd (j + 1) j' (by omega) (by omega) heq
          omega
        · rw [if_neg hc1, if_neg hc2] at heq
          have := hnd (j + 1) (j' + 1) (by omega) (by omega) heq
          omega

/-! ### `reveal`'s hidden-slice decomposition -/

/-- The hidden slice's last card and second-to-last card decompose it:
`hidden = pre ++ [d, r]`. -/
theorem hidden_split {st : State} {a : Anchor} {d r : Card}
    (hrev : ((st.hidden a).reverse.drop 1).head? = some d)
    (hgt : (st.hidden a).getLast? = some r) :
    ∃ pre, st.hidden a = pre ++ [d, r] := by
  have hh : (st.hidden a).reverse.head? = some r := by
    rw [head?_reverse_eq_getLast?]; exact hgt
  cases hr : (st.hidden a).reverse with
  | nil => rw [hr] at hh; simp at hh
  | cons x xs =>
    rw [hr] at hh
    simp only [List.head?_cons, Option.some.injEq] at hh
    subst hh
    have hd2 : xs.head? = some d := by
      rw [hr] at hrev
      simpa using hrev
    cases xs with
    | nil => simp at hd2
    | cons d' ds =>
      rw [List.head?_cons, Option.some.injEq] at hd2
      subst hd2
      refine ⟨ds.reverse, ?_⟩
      rw [← List.reverse_reverse (st.hidden a), hr]
      simp

/-- The hidden slice is a single card: the boundary is the pile's
bottom dealt card. -/
theorem hidden_single {st : State} {a : Anchor} {r : Card}
    (hrev : ((st.hidden a).reverse.drop 1).head? = none)
    (hgt : (st.hidden a).getLast? = some r) :
    st.hidden a = [r] := by
  cases hr : (st.hidden a).reverse with
  | nil =>
    exfalso
    cases hs : st.hidden a with
    | nil => rw [hs] at hgt; simp at hgt
    | cons y t => rw [hs] at hr; simp at hr
  | cons x xs =>
    cases xs with
    | nil =>
      have h1 : st.hidden a = [x] := by
        rw [← List.reverse_reverse (st.hidden a), hr]
        simp
      rw [h1] at hgt
      simp at hgt
      rw [h1, hgt]
    | cons y ys =>
      exfalso
      rw [hr] at hrev
      simp at hrev

/-- The boundary's dealt parent: the card under the top hidden card in
the hidden slice is directly under it in the deal. -/
theorem hidden_parent_dealt {st : State} {a : Anchor} {d r : Card}
    (hrev : ((st.hidden a).reverse.drop 1).head? = some d)
    (hgt : (st.hidden a).getLast? = some r) :
    ∃ t rest, st.deal.piles a = t ++ d :: r :: rest := by
  obtain ⟨pre, hpre⟩ := hidden_split hrev hgt
  refine ⟨pre, (st.deal.piles a).drop (st.depths a), ?_⟩
  have htd : st.deal.piles a = st.hidden a ++ (st.deal.piles a).drop (st.depths a) :=
    (List.take_append_drop (st.depths a) (st.deal.piles a)).symm
  rw [hpre] at htd
  calc st.deal.piles a = (pre ++ [d, r]) ++ (st.deal.piles a).drop (st.depths a) := htd
    _ = pre ++ d :: r :: (st.deal.piles a).drop (st.depths a) := by simp

namespace Deal

/-- The seven piles contribute 28 cards to the flatMap. -/
theorem flatMap_piles_length {d : Deal} (hd : d.WF) :
    (Anchor.all.flatMap d.piles).length = 28 := by
  simp only [List.length_flatMap, Anchor.all, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, hd.1, Anchor.toIdx]
  rfl

/-- Pile cards never belong to the deal's stock (index-wise
distinctness of the concatenated deal). -/
theorem piles_stock_disj {d : Deal} (hd : d.WF) {a : Anchor} {c : Card}
    (hc : c ∈ d.piles a) : c ∉ d.stock := by
  intro hcs
  have h28 : (Anchor.all.flatMap d.piles).length = 28 := d.flatMap_piles_length hd
  have h24 : d.stock.length = 24 := hd.2.1
  have hlen : (Anchor.all.flatMap d.piles ++ d.stock).length = 52 := by
    rw [List.length_append, h28, h24]
  have hmem : c ∈ Anchor.all.flatMap d.piles :=
    List.mem_flatMap.mpr ⟨a, a.mem_all, hc⟩
  obtain ⟨i₁, hi₁⟩ := List.mem_iff_getElem?.mp hmem
  obtain ⟨i₂, hi₂⟩ := List.mem_iff_getElem?.mp hcs
  have hb₁ : i₁ < (Anchor.all.flatMap d.piles).length :=
    (List.getElem?_eq_some_iff.mp hi₁).1
  have hb₂ : i₂ < d.stock.length := (List.getElem?_eq_some_iff.mp hi₂).1
  have hv₁ : (Anchor.all.flatMap d.piles ++ d.stock)[i₁]? = some c := by
    rw [List.getElem?_append_left hb₁]
    exact hi₁
  have hv₂ : (Anchor.all.flatMap d.piles ++ d.stock)[28 + i₂]? = some c := by
    rw [List.getElem?_append_right (by omega)]
    rw [h28, Nat.add_sub_cancel_left]
    exact hi₂
  have hnd := hd.2.2 i₁ (28 + i₂) (by omega) (by omega) (by rw [hv₁, hv₂])
  omega

end Deal

/-- **T (twin swap), conjugation step**: applying a flipped move to
the flipped state is applying the move to the state, flipped.
TODO: seven move cases. -/
theorem apply_flipAll (m : Move) (st : State) :
    st.flipAll.apply m.flipMove = (st.apply m).map State.flipAll := sorry

/-- **T (twin swap)**: solvability is invariant under the relabeling.
TODO: induction on the play via `apply_flipAll`. -/
theorem solvable_flipAll {st : State} (h : st.solvableFrom) :
    st.flipAll.solvableFrom := sorry

/-- **The no-pile-to-pile restriction (ledger B-legs)**: on
well-formed states, the full physical game and the engine's restricted
move set have the same solvability.  TODO: the compression/reshape
arguments of no_pile_to_pile.md — now a statement about a move subset
of ONE model, not a correspondence between two formalizations. -/
theorem solvable_engine_iff {st : State} (hwf : st.WF) :
    st.solvableFrom ↔ st.solvableEngine := sorry

/-- TODO(proof): `WF` is preserved by every legal move — the
maintenance lemma, per move case.  Prover-confirmed WF-design
witnesses: deal-adjacency grandfathers `reveal`'s cover-on-cover edge
(board {inr ♥2 ↦ ♥3}); stock ⊆ deal.stock carries `reveal`'s
freshly-visible boundary card out of the cycle (witness ⟨[♥2, ♠9], 1⟩).
RESIDUAL deckPile/deckStack blocker (prover-confirmed, escalated):
the membership conjunct does not see multiplicity — a state stock
[♢3, ♢3] of a deal-stock card survives it, and the splice leaves the
second copy while the card turns visible (witness #5: board
{inr ♠3 ↦ ♠4}, `deckPile ♢3 (inr ♠4)`) — restore
`noDupCards st.stock.cards` as an additional conjunct. -/
theorem apply_wf {st : State} (hwf : st.WF) (m : Move) (st' : State)
    (h : st.apply m = some st') : st'.WF := sorry

/-- **C13 pilot (model level)**: adjacent Draw-commitments commute
(distinct bases).  Cycle content: `Cycle.removeIdx_comm`; the board
part: `attach` on distinct bases.  NOTE: non-adjacent pairs land on
*different cursors* — the engine's sweep/canonicalization is what
recovers commutation there (the C-IND landscape).  TODO. -/
theorem drawTo_comm_adjacent {st : State} {c c' : Card} {b b' : Base}
    (hbb : b ≠ b') {i : Nat}
    (hic : st.stock.posOf c = some i)
    (hic' : st.stock.posOf c' = some (i + 1))
    {st₂ st₄ : State}
    (h₂ : (st.applyDrawTo c b >>= fun s => s.applyDrawTo c' b') = some st₂)
    (h₄ : (st.applyDrawTo c' b' >>= fun s => s.applyDrawTo c b) = some st₄) :
    st₂ = st₄ := sorry
