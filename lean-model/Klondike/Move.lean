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

/-! ## The twin-swap conjugation (theorem T's helpers)

`State.flipAll` is the componentwise twin-swap; these lemmas push it
through the move machinery — the board's conjugated matching, the
stock cycle's cursor operations, and the derived guards — so that
`apply_flipAll`'s seven arms reduce to pointwise conjugations. -/

/-- Twin-swap is injective on bases. -/
theorem Base.flipBase_inj {b₁ b₂ : Base} (h : b₁.flipBase = b₂.flipBase) : b₁ = b₂ := by
  have h2 := congrArg Base.flipBase h
  rw [Base.flipBase_flipBase, Base.flipBase_flipBase] at h2
  exact h2

/-- The containment check is twin-invariant. -/
theorem List.contains_map_flipSuit : ∀ (l : List Card) (d : Card),
    (l.map Card.flipSuit).contains d.flipSuit = l.contains d := by
  intro l
  induction l with
  | nil => intro d; rfl
  | cons x t ih =>
      intro d
      rw [List.map_cons, List.contains_cons, List.contains_cons, ih]
      by_cases hd : d = x
      · rw [hd]
        simp
      · have h5 : (d == x) = false := by
          cases hb2 : (d == x) with
          | true => exact absurd (eq_of_beq hb2) hd
          | false => rfl
        have h6 : (d.flipSuit == x.flipSuit) = false := by
          cases hb3 : (d.flipSuit == x.flipSuit) with
          | true =>
              exact absurd (by
                have h4 := congrArg Card.flipSuit (eq_of_beq hb3)
                rwa [Card.flipSuit_flipSuit, Card.flipSuit_flipSuit] at h4) hd
          | false => rfl
        rw [h5, h6]

/-- Splicing commutes with any relabeling. -/
theorem Cycle.removeIdx_map {α β : Type} (f : α → β) : ∀ (l : List α) (i : Nat),
    Cycle.removeIdx (l.map f) i = (Cycle.removeIdx l i).map f := by
  intro l
  induction l with
  | nil => intro i; rfl
  | cons a t ih =>
      intro i
      cases i with
      | zero => rfl
      | succ n =>
          show f a :: Cycle.removeIdx (t.map f) n = f a :: (Cycle.removeIdx t n).map f
          rw [ih n]

/-- Pointwise update conjugates by the twin-swap. -/
theorem Board.update_flipBase (f : Base → Option Card) (b : Base) (o : Option Card)
    (b'' : Base) :
    Board.update (fun b' => (f b'.flipBase).map Card.flipSuit) b.flipBase
        (o.map Card.flipSuit) b''
      = (Board.update f b o b''.flipBase).map Card.flipSuit := by
  by_cases hb : b'' = b.flipBase
  · subst hb
    show (if (b.flipBase) = b.flipBase then Option.map Card.flipSuit o
          else (f (b.flipBase).flipBase).map Card.flipSuit)
        = (Board.update f b o (b.flipBase).flipBase).map Card.flipSuit
    rw [if_pos rfl, Base.flipBase_flipBase, Board.update_self]
  · show (if b'' = b.flipBase then Option.map Card.flipSuit o
          else (f b''.flipBase).map Card.flipSuit)
        = (Board.update f b o b''.flipBase).map Card.flipSuit
    rw [if_neg hb]
    have hne : b''.flipBase ≠ b := fun hcon => hb (by rw [← hcon, Base.flipBase_flipBase])
    rw [Board.update_ne f b b''.flipBase o hne]

/-- The derived inverse conjugates by the twin-swap. -/
theorem Board.mapBy_bottomOf (bd : Board) (c : Card) :
    bd.mapBy.bottomOf c.flipSuit = (bd.bottomOf c).map Base.flipBase := by
  cases hb : bd.bottomOf c with
  | none =>
      have hgoal : bd.mapBy.bottomOf c.flipSuit = none := by
        rw [Board.bottomOf_eq_none]
        intro b' hb'
        rw [show bd.mapBy.topOf b' = (bd.topOf b'.flipBase).map Card.flipSuit from rfl] at hb'
        obtain ⟨d, hd, hd'⟩ := Option.map_eq_some_iff.mp hb'
        have hdc : d = c := by
          have h2 := congrArg Card.flipSuit hd'
          rw [Card.flipSuit_flipSuit, Card.flipSuit_flipSuit] at h2
          exact h2
        rw [hdc] at hd
        exact (Board.bottomOf_eq_none bd c).mp hb b'.flipBase hd
      exact hgoal
  | some b =>
      refine (Board.bottomOf_eq _ _ _).mpr ?_
      show (bd.topOf (b.flipBase).flipBase).map Card.flipSuit = _
      rw [Base.flipBase_flipBase, (Board.bottomOf_eq bd c b).mp hb]
      rfl

/-- Detach conjugates by the twin-swap. -/
theorem Board.mapBy_detach (bd : Board) (b : Base) :
    (bd.mapBy).detach b.flipBase = (bd.detach b).mapBy := by
  refine Board.ext_topOf ?_
  funext b''
  show Board.update (fun b' => (bd.topOf b'.flipBase).map Card.flipSuit) b.flipBase
        (Option.map Card.flipSuit none) b''
      = (Board.update bd.topOf b none b''.flipBase).map Card.flipSuit
  exact Board.update_flipBase bd.topOf b none b''

/-- Attach conjugates by the twin-swap. -/
theorem Board.mapBy_attach (bd : Board) (b : Base) (c : Card) :
    bd.mapBy.attach b.flipBase c.flipSuit = (bd.attach b c).map Board.mapBy := by
  by_cases hatt : bd.attach b c = none
  · by_cases hfl : bd.mapBy.attach b.flipBase c.flipSuit = none
    · rw [hfl, hatt]
      rfl
    · exfalso
      obtain ⟨h1, h2⟩ := (Board.attach_eq_some_iff _ _ _).mp hfl
      rw [show bd.mapBy.topOf b.flipBase
            = (bd.topOf (b.flipBase).flipBase).map Card.flipSuit from rfl] at h1
      rw [Base.flipBase_flipBase] at h1
      rw [Board.mapBy_bottomOf] at h2
      exact ((Board.attach_eq_some_iff bd b c).mpr
        ⟨Option.map_eq_none_iff.mp h1, Option.map_eq_none_iff.mp h2⟩) hatt
  · obtain ⟨hfree, hnew⟩ := (Board.attach_eq_some_iff bd b c).mp hatt
    have hf' : bd.mapBy.topOf b.flipBase = none := by
      show (bd.topOf (b.flipBase).flipBase).map Card.flipSuit = none
      rw [Base.flipBase_flipBase]
      exact Option.map_eq_none_iff.mpr hfree
    have hb' : bd.mapBy.bottomOf c.flipSuit = none := by
      rw [Board.mapBy_bottomOf]
      exact Option.map_eq_none_iff.mpr hnew
    cases hfl2 : bd.mapBy.attach b.flipBase c.flipSuit with
    | none =>
        exact absurd ((Board.attach_eq_some_iff _ _ _).mpr ⟨hf', hb'⟩) (fun hnn => hnn hfl2)
    | some bd'' =>
        cases hatt2 : bd.attach b c with
        | none => exact absurd hatt2 hatt
        | some bd' =>
            refine congrArg some ?_
            refine Board.ext_topOf ?_
            funext b''
            show bd''.topOf b'' = (bd'.topOf b''.flipBase).map Card.flipSuit
            by_cases hbb : b'' = b.flipBase
            · rw [hbb, attach_topOf bd.mapBy b.flipBase c.flipSuit hfl2,
                Base.flipBase_flipBase, attach_topOf bd b c hatt2]
              rfl
            · rw [attach_topOf_ne bd.mapBy b.flipBase c.flipSuit hfl2 hbb]
              by_cases hbb2 : b''.flipBase = b
              · exfalso
                exact hbb (by rw [← hbb2, Base.flipBase_flipBase])
              · rw [attach_topOf_ne bd b c hatt2 hbb2]
                rfl

/-- The run walk conjugates by the twin-swap (fuel induction). -/
theorem Board.mapBy_aboveOf_go (bd : Board) : ∀ (fuel : Nat) (b : Base) (acc : List Card),
    Board.aboveOf.go bd.mapBy fuel b.flipBase (acc.map Card.flipSuit)
      = (Board.aboveOf.go bd fuel b acc).map Card.flipSuit := by
  intro fuel
  induction fuel with
  | zero => intro b acc; rfl
  | succ n ih =>
      intro b acc
      show (match (bd.topOf (b.flipBase).flipBase).map Card.flipSuit with
            | none => acc.map Card.flipSuit
            | some c' => if (acc.map Card.flipSuit).contains c' then acc.map Card.flipSuit
                         else Board.aboveOf.go bd.mapBy n (Sum.inr c')
                             (c' :: acc.map Card.flipSuit))
          = (match bd.topOf b with
             | none => acc
             | some c' => if acc.contains c' then acc
                          else Board.aboveOf.go bd n (Sum.inr c') (c' :: acc)).map
              Card.flipSuit
      rw [Base.flipBase_flipBase]
      cases ht : bd.topOf b with
      | none => rfl
      | some d =>
          have hcc := List.contains_map_flipSuit acc d
          show (if (acc.map Card.flipSuit).contains (Card.flipSuit d) then acc.map Card.flipSuit
                else Board.aboveOf.go bd.mapBy n (Sum.inr (Card.flipSuit d))
                    (Card.flipSuit d :: acc.map Card.flipSuit))
              = ((if acc.contains d then acc
                  else Board.aboveOf.go bd n (Sum.inr d) (d :: acc)).map Card.flipSuit)
          by_cases hcont : acc.contains d = true
          · rw [if_pos (hcc.trans hcont), if_pos hcont]
          · rw [if_neg (fun hc => hcont (hcc.symm.trans hc)), if_neg hcont]
            exact ih (Sum.inr d) (d :: acc)

theorem Board.mapBy_aboveOf (bd : Board) (c : Card) :
    (bd.mapBy).aboveOf c.flipSuit = (bd.aboveOf c).map Card.flipSuit := by
  show Board.aboveOf.go bd.mapBy 52 (Base.flipBase (Sum.inr c)) ([] : List Card)
      = (Board.aboveOf.go bd 52 (Sum.inr c) []).map Card.flipSuit
  exact Board.mapBy_aboveOf_go bd 52 (Sum.inr c) []

/-! ### The state-level conjugations, spelled at the `flipAll` forms -/

theorem State.flipAll_board_topOf_inr (st : State) (c : Card) :
    st.flipAll.board.topOf (Sum.inr (Card.flipSuit c))
      = (st.board.topOf (Sum.inr c)).map Card.flipSuit := by
  show (st.board.topOf (Sum.inr (Card.flipSuit (Card.flipSuit c)))).map Card.flipSuit = _
  rw [Card.flipSuit_flipSuit]

theorem State.flipAll_board_bottomOf (st : State) (c : Card) :
    st.flipAll.board.bottomOf c.flipSuit = (st.board.bottomOf c).map Base.flipBase :=
  Board.mapBy_bottomOf st.board c

theorem State.flipAll_board_attach (st : State) (b : Base) (c : Card) :
    st.flipAll.board.attach b.flipBase c.flipSuit = (st.board.attach b c).map Board.mapBy :=
  Board.mapBy_attach st.board b c

theorem State.flipAll_board_detach (st : State) (b : Base) :
    st.flipAll.board.detach b.flipBase = (st.board.detach b).mapBy :=
  Board.mapBy_detach st.board b

theorem State.flipAll_board_aboveOf (st : State) (c : Card) :
    st.flipAll.board.aboveOf c.flipSuit = (st.board.aboveOf c).map Card.flipSuit :=
  Board.mapBy_aboveOf st.board c

/-- The foundation heights are probed through the twin involution. -/
theorem State.flipAll_heights_probe (st : State) (s : Suit) :
    st.flipAll.heights s.flipPair = st.heights s := by
  show st.heights s.flipPair.flipPair = _
  rw [Suit.flipPair_flipPair]

/-- The placement guard is twin-invariant. -/
theorem State.flipAll_canPlace (st : State) (c : Card) (b : Base) :
    st.flipAll.canPlace c.flipSuit b.flipBase = st.canPlace c b := by
  cases b with
  | inl a =>
      show (decide ((st.board.topOf (Sum.inl a)).map Card.flipSuit = none)
            && decide (c.flipSuit.rank = Rank.king))
          = (decide (st.board.topOf (Sum.inl a) = none) && decide (c.rank = Rank.king))
      cases hto : st.board.topOf (Sum.inl a) with
      | none => rfl
      | some x => rfl
  | inr d =>
      have hisSome : ∀ (o : Option Base), (o.map Base.flipBase).isSome = o.isSome := by
        intro o
        cases o with
        | none => rfl
        | some b => rfl
      show (decide ((st.board.topOf (Sum.inr (Card.flipSuit (Card.flipSuit d)))).map
            Card.flipSuit = none)
            && (((st.flipAll.board).bottomOf (Card.flipSuit d)).isSome
                && canSitOn (Card.flipSuit c) (Card.flipSuit d)))
          = (decide (st.board.topOf (Sum.inr d) = none)
             && ((st.board.bottomOf d).isSome && canSitOn c d))
      rw [Card.flipSuit_flipSuit, State.flipAll_board_bottomOf, hisSome _]
      cases hto : st.board.topOf (Sum.inr d) with
      | none => rfl
      | some x => rfl

/-- The run guard is twin-invariant. -/
theorem State.flipAll_canMoveRun (st : State) (c : Card) (b : Base) :
    st.flipAll.canMoveRun c.flipSuit b.flipBase = st.canMoveRun c b := by
  show (st.flipAll.canPlace c.flipSuit b.flipBase
        && (match b.flipBase with
            | Sum.inl _ => true
            | Sum.inr d => !(st.flipAll.board.aboveOf c.flipSuit).contains d))
      = (st.canPlace c b
         && (match b with
             | Sum.inl _ => true
             | Sum.inr d => !(st.board.aboveOf c).contains d))
  rw [State.flipAll_canPlace]
  cases b with
  | inl a => rfl
  | inr d =>
      show (st.canPlace c (Sum.inr d)
            && !(st.flipAll.board.aboveOf (Card.flipSuit c)).contains (Card.flipSuit d))
          = (st.canPlace c (Sum.inr d) && !(st.board.aboveOf c).contains d)
      rw [State.flipAll_board_aboveOf, List.contains_map_flipSuit]

/-- The waste top conjugates. -/
theorem State.flipAll_stock_prev (st : State) :
    st.flipAll.stock.prev = st.stock.prev.map Card.flipSuit := by
  show (if st.stock.cursor = 0 then none
        else (st.stock.cards.map Card.flipSuit)[st.stock.cursor - 1]?)
      = (if st.stock.cursor = 0 then none
          else st.stock.cards[st.stock.cursor - 1]?).map Card.flipSuit
  by_cases hcu : st.stock.cursor = 0
  · rw [if_pos hcu, if_pos hcu]
    rfl
  · rw [if_neg hcu, if_neg hcu]
    rw [List.getElem?_map]

/-- Splicing out the waste top conjugates. -/
theorem State.flipAll_stock_removeAt (st : State) (i : Nat) :
    st.flipAll.stock.removeAt i
      = { cards := (st.stock.removeAt i).cards.map Card.flipSuit,
          cursor := (st.stock.removeAt i).cursor } := by
  show Cycle.mk (Cycle.removeIdx (st.stock.cards.map Card.flipSuit) i)
         (if i < st.stock.cursor then st.stock.cursor - 1 else st.stock.cursor)
      = Cycle.mk ((Cycle.removeIdx st.stock.cards i).map Card.flipSuit)
          (if i < st.stock.cursor then st.stock.cursor - 1 else st.stock.cursor)
  rw [Cycle.removeIdx_map]

/-- One deal conjugates (the cursor compares against the mapped length). -/
theorem State.flipAll_stock_dealOnce (st : State) (s : Nat) :
    st.flipAll.stock.dealOnce s
      = { cards := (st.stock.dealOnce s).cards.map Card.flipSuit,
          cursor := (st.stock.dealOnce s).cursor } := by
  have hlen : (st.stock.cards.map Card.flipSuit).length = st.stock.cards.length := by
    rw [List.length_map]
  by_cases hcu : st.stock.cursor ≥ st.stock.cards.length
  · have hR : st.stock.dealOnce s = Cycle.mk st.stock.cards 0 := by
      show (if st.stock.cursor ≥ st.stock.cards.length then Cycle.mk st.stock.cards 0
            else Cycle.mk st.stock.cards
                   (min (st.stock.cursor + s) st.stock.cards.length))
          = Cycle.mk st.stock.cards 0
      rw [if_pos hcu]
    have hL : st.flipAll.stock.dealOnce s = Cycle.mk (st.stock.cards.map Card.flipSuit) 0 := by
      show (if st.stock.cursor ≥ (st.stock.cards.map Card.flipSuit).length
            then Cycle.mk (st.stock.cards.map Card.flipSuit) 0
            else Cycle.mk (st.stock.cards.map Card.flipSuit)
                   (min (st.stock.cursor + s) (st.stock.cards.map Card.flipSuit).length))
          = Cycle.mk (st.stock.cards.map Card.flipSuit) 0
      rw [hlen, if_pos hcu]
    rw [hL, hR]
  · have hR : st.stock.dealOnce s
        = Cycle.mk st.stock.cards (min (st.stock.cursor + s) st.stock.cards.length) := by
      show (if st.stock.cursor ≥ st.stock.cards.length then Cycle.mk st.stock.cards 0
            else Cycle.mk st.stock.cards
                   (min (st.stock.cursor + s) st.stock.cards.length))
          = Cycle.mk st.stock.cards (min (st.stock.cursor + s) st.stock.cards.length)
      rw [if_neg hcu]
    have hL : st.flipAll.stock.dealOnce s
        = Cycle.mk (st.stock.cards.map Card.flipSuit)
            (min (st.stock.cursor + s) st.stock.cards.length) := by
      show (if st.stock.cursor ≥ (st.stock.cards.map Card.flipSuit).length
            then Cycle.mk (st.stock.cards.map Card.flipSuit) 0
            else Cycle.mk (st.stock.cards.map Card.flipSuit)
                   (min (st.stock.cursor + s) (st.stock.cards.map Card.flipSuit).length))
          = Cycle.mk (st.stock.cards.map Card.flipSuit)
              (min (st.stock.cursor + s) st.stock.cards.length)
      rw [hlen, if_neg hcu]
    rw [hL, hR]

/-- The hidden slice conjugates. -/
theorem State.flipAll_hidden (st : State) (a : Anchor) :
    st.flipAll.hidden a = (st.hidden a).map Card.flipSuit := by
  show ((st.deal.piles a).map Card.flipSuit).take (st.depths a)
      = ((st.deal.piles a).take (st.depths a)).map Card.flipSuit
  rw [List.map_take]

/-- The hidden boundary conjugates. -/
theorem State.flipAll_topHidden (st : State) (a : Anchor) :
    st.flipAll.topHidden a = (st.topHidden a).map Card.flipSuit := by
  show (((st.deal.piles a).map Card.flipSuit).take (st.depths a)).getLast?
      = Option.map Card.flipSuit ((st.deal.piles a).take (st.depths a)).getLast?
  rw [← List.map_take, List.getLast?_map]

/-- The boundary-pile search conjugates. -/
theorem State.flipAll_pileOfTopHidden (st : State) (r : Card) :
    st.flipAll.pileOfTopHidden r.flipSuit = st.pileOfTopHidden r := by
  have hfun : (fun a => decide (st.flipAll.topHidden a = some r.flipSuit))
      = (fun a => decide (st.topHidden a = some r)) := by
    funext a
    have hS : st.flipAll.topHidden a = (st.topHidden a).map Card.flipSuit :=
      State.flipAll_topHidden st a
    by_cases hta : st.topHidden a = some r
    · rw [decide_eq_true hta]
      rw [decide_eq_true (by rw [hS, hta]; rfl)]
    · have hf : ¬(st.flipAll.topHidden a = some r.flipSuit) := by
        intro hcon
        rw [hS] at hcon
        obtain ⟨x, hx, hx'⟩ := Option.map_eq_some_iff.mp hcon
        have hxc : x = r := by
          have h2 := congrArg Card.flipSuit hx'
          rw [Card.flipSuit_flipSuit, Card.flipSuit_flipSuit] at h2
          exact h2
        rw [hxc] at hx
        exact hta hx
      rw [decide_eq_false hf, decide_eq_false hta]
  show findFirst (fun a => decide (st.flipAll.topHidden a = some r.flipSuit)) Anchor.all
      = findFirst (fun a => decide (st.topHidden a = some r)) Anchor.all
  rw [hfun]

/-- The hidden base conjugates. -/
theorem State.flipAll_hiddenBase (st : State) (a : Anchor) :
    st.flipAll.hiddenBase a = (st.hiddenBase a).flipBase := by
  show (match ((st.flipAll.hidden a).reverse.drop 1) |>.head? with
        | some d => Sum.inr d | none => Sum.inl a)
      = Base.flipBase
          (match ((st.hidden a).reverse.drop 1) |>.head? with
           | some d => Sum.inr d | none => Sum.inl a)
  rw [State.flipAll_hidden, ← List.map_reverse, ← List.map_drop, List.head?_map]
  cases hhd : ((st.hidden a).reverse.drop 1) |>.head? with
  | none => rfl
  | some d => rfl

/-- The heights bump conjugates. -/
theorem State.flipAll_bump (st : State) (c : Card) :
    (fun s => if s = (Card.flipSuit c).suit then st.flipAll.heights s + 1
              else st.flipAll.heights s)
      = (fun s => if s.flipPair = c.suit then st.heights s.flipPair + 1
                  else st.heights s.flipPair) := by
  funext s
  show (if s = c.suit.flipPair then st.heights s.flipPair + 1 else st.heights s.flipPair)
      = (if s.flipPair = c.suit then st.heights s.flipPair + 1 else st.heights s.flipPair)
  by_cases hs : s = c.suit.flipPair
  · rw [if_pos hs, if_pos (by rw [hs, Suit.flipPair_flipPair])]
  · rw [if_neg hs,
        if_neg (fun hcon => hs ((Suit.flipPair_flipPair s).symm.trans (congrArg Suit.flipPair hcon)))]

/-- The heights drop conjugates. -/
theorem State.flipAll_drop (st : State) (c : Card) :
    (fun s => if s = (Card.flipSuit c).suit then st.flipAll.heights s - 1
              else st.flipAll.heights s)
      = (fun s => if s.flipPair = c.suit then st.heights s.flipPair - 1
                  else st.heights s.flipPair) := by
  funext s
  show (if s = c.suit.flipPair then st.heights s.flipPair - 1 else st.heights s.flipPair)
      = (if s.flipPair = c.suit then st.heights s.flipPair - 1 else st.heights s.flipPair)
  by_cases hs : s = c.suit.flipPair
  · rw [if_pos hs, if_pos (by rw [hs, Suit.flipPair_flipPair])]
  · rw [if_neg hs,
        if_neg (fun hcon => hs ((Suit.flipPair_flipPair s).symm.trans (congrArg Suit.flipPair hcon)))]

/-- **T (twin swap), conjugation step**: applying a flipped move to
the flipped state is applying the move to the state, flipped.
Seven move cases, each reducing to the pointwise conjugations. -/
theorem apply_flipAll (m : Move) (st : State) :
    st.flipAll.apply m.flipMove = (st.apply m).map State.flipAll := by
  cases m with
  | draw =>
      show some { st.flipAll with stock := st.flipAll.stock.dealOnce st.drawStep }
        = Option.map State.flipAll (some { st with stock := st.stock.dealOnce st.drawStep })
      rw [State.flipAll_stock_dealOnce]
      rfl
  | reveal c =>
      show (match st.flipAll.board.topOf (Sum.inr (Card.flipSuit c)) with
            | some _ => none
            | none =>
                match st.flipAll.board.bottomOf (Card.flipSuit c) with
                | some (Sum.inr r) =>
                    match st.flipAll.pileOfTopHidden r with
                    | none => none
                    | some a =>
                        match st.flipAll.board.attach (st.flipAll.hiddenBase a) r with
                        | none => none
                        | some bd =>
                            some { st.flipAll with
                              board := bd,
                              depths := fun a' => if a' = a then st.flipAll.depths a - 1
                                                   else st.flipAll.depths a' }
                | _ => none)
          = Option.map State.flipAll
              (match st.board.topOf (Sum.inr c) with
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
                                 depths := fun a' => if a' = a then st.depths a - 1
                                                      else st.depths a' }
                   | _ => none)
      rw [State.flipAll_board_topOf_inr, State.flipAll_board_bottomOf]
      cases ht : st.board.topOf (Sum.inr c) with
      | some x => rfl
      | none =>
          cases hb : st.board.bottomOf c with
          | none => rfl
          | some b =>
              cases b with
              | inl a => rfl
              | inr r =>
                  show (match st.flipAll.pileOfTopHidden (Card.flipSuit r) with
                        | none => none
                        | some a =>
                            match st.flipAll.board.attach (st.flipAll.hiddenBase a)
                              (Card.flipSuit r) with
                            | none => none
                            | some bd =>
                                some { st.flipAll with
                                  board := bd,
                                  depths := fun a' => if a' = a then st.flipAll.depths a - 1
                                                       else st.flipAll.depths a' })
                    = Option.map State.flipAll
                        (match st.pileOfTopHidden r with
                         | none => none
                         | some a =>
                             match st.board.attach (st.hiddenBase a) r with
                             | none => none
                             | some bd =>
                                 some { st with
                                   board := bd,
                                   depths := fun a' => if a' = a then st.depths a - 1
                                                        else st.depths a' })
                  rw [State.flipAll_pileOfTopHidden]
                  cases hp : st.pileOfTopHidden r with
                  | none => rfl
                  | some a =>
                      show (match st.flipAll.board.attach (st.flipAll.hiddenBase a)
                              (Card.flipSuit r) with
                            | none => none
                            | some bd =>
                                some { st.flipAll with
                                  board := bd,
                                  depths := fun a' => if a' = a then st.flipAll.depths a - 1
                                                       else st.flipAll.depths a' })
                        = Option.map State.flipAll
                            (match st.board.attach (st.hiddenBase a) r with
                             | none => none
                             | some bd =>
                                 some { st with
                                   board := bd,
                                   depths := fun a' => if a' = a then st.depths a - 1
                                                        else st.depths a' })
                      rw [State.flipAll_hiddenBase, State.flipAll_board_attach]
                      cases hatt : st.board.attach (st.hiddenBase a) r with
                      | none => rfl
                      | some bd =>
                          show some { st.flipAll with
                                      board := Board.mapBy bd,
                                      depths := fun a' => if a' = a then st.flipAll.depths a - 1
                                                           else st.flipAll.depths a' }
                            = Option.map State.flipAll
                                (some { st with
                                  board := bd,
                                  depths := fun a' => if a' = a then st.depths a - 1
                                                       else st.depths a' })
                          rfl
  | deckPile c b =>
      show (match st.flipAll.stock.prev with
            | none => none
            | some c' =>
                if c' = Card.flipSuit c ∧ st.flipAll.canPlace (Card.flipSuit c) (b.flipBase) then
                  (match st.flipAll.board.attach b.flipBase (Card.flipSuit c) with
                   | none => none
                   | some bd => some { st.flipAll with
                     board := bd,
                     stock := st.flipAll.stock.removeAt (st.flipAll.stock.cursor - 1) })
                else none)
          = Option.map State.flipAll
              (match st.stock.prev with
               | none => none
               | some c' =>
                   if c' = c ∧ st.canPlace c b then
                     (match st.board.attach b c with
                      | none => none
                      | some bd => some { st with
                        board := bd,
                        stock := st.stock.removeAt (st.stock.cursor - 1) })
                   else none)
      rw [State.flipAll_stock_prev]
      cases hp : st.stock.prev with
      | none => rfl
      | some w =>
          show (if Card.flipSuit w = Card.flipSuit c ∧ st.flipAll.canPlace (Card.flipSuit c)
                    (b.flipBase) then
                  (match st.flipAll.board.attach b.flipBase (Card.flipSuit c) with
                   | none => none
                   | some bd => some { st.flipAll with
                     board := bd,
                     stock := st.flipAll.stock.removeAt (st.flipAll.stock.cursor - 1) })
                else none)
            = Option.map State.flipAll
                (if w = c ∧ st.canPlace c b then
                  (match st.board.attach b c with
                   | none => none
                   | some bd => some { st with
                     board := bd,
                     stock := st.stock.removeAt (st.stock.cursor - 1) })
                  else none)
          rw [State.flipAll_canPlace]
          by_cases hcond : w = c ∧ st.canPlace c b = true
          · rw [if_pos ⟨by rw [hcond.1], hcond.2⟩, if_pos hcond]
            rw [State.flipAll_board_attach]
            cases hatt : st.board.attach b c with
            | none => rfl
            | some bd =>
                rw [show st.flipAll.stock.cursor - 1 = st.stock.cursor - 1 from rfl,
                    State.flipAll_stock_removeAt]
                rfl
          · rw [if_neg (fun hc => hcond ⟨by
                have h2 := congrArg Card.flipSuit hc.1
                rw [Card.flipSuit_flipSuit, Card.flipSuit_flipSuit] at h2
                exact h2, hc.2⟩), if_neg hcond]
            rfl
  | deckStack c =>
      show (match st.flipAll.stock.prev with
            | none => none
            | some c' =>
                if c' = Card.flipSuit c ∧ (Card.flipSuit c).rank.toIdx
                    = st.flipAll.heights (Card.flipSuit c).suit then
                  some { st.flipAll with
                    stock := st.flipAll.stock.removeAt (st.flipAll.stock.cursor - 1),
                    heights := fun s => if s = (Card.flipSuit c).suit then st.flipAll.heights s + 1
                                      else st.flipAll.heights s }
                else none)
          = Option.map State.flipAll
              (match st.stock.prev with
               | none => none
               | some c' =>
                   if c' = c ∧ c.rank.toIdx = st.heights c.suit then
                     some { st with
                       stock := st.stock.removeAt (st.stock.cursor - 1),
                       heights := fun s => if s = c.suit then st.heights s + 1
                                           else st.heights s }
                   else none)
      rw [State.flipAll_stock_prev]
      cases hp : st.stock.prev with
      | none => rfl
      | some w =>
          show (if Card.flipSuit w = Card.flipSuit c ∧ (Card.flipSuit c).rank.toIdx
                    = st.flipAll.heights (Card.flipSuit c).suit then
                  some { st.flipAll with
                    stock := st.flipAll.stock.removeAt (st.flipAll.stock.cursor - 1),
                    heights := fun s => if s = (Card.flipSuit c).suit then st.flipAll.heights s + 1
                                      else st.flipAll.heights s }
                else none)
            = Option.map State.flipAll
                (if w = c ∧ c.rank.toIdx = st.heights c.suit then
                  some { st with
                    stock := st.stock.removeAt (st.stock.cursor - 1),
                    heights := fun s => if s = c.suit then st.heights s + 1
                                        else st.heights s }
                  else none)
          rw [show (Card.flipSuit c).rank.toIdx = c.rank.toIdx from rfl,
              show st.flipAll.heights (Card.flipSuit c).suit = st.heights c.suit from
                State.flipAll_heights_probe st c.suit]
          by_cases hcond : w = c ∧ c.rank.toIdx = st.heights c.suit
          · rw [if_pos ⟨by rw [hcond.1], hcond.2⟩, if_pos hcond]
            rw [show st.flipAll.stock.cursor - 1 = st.stock.cursor - 1 from rfl,
                State.flipAll_stock_removeAt,
                State.flipAll_bump]
            rfl
          · rw [if_neg (fun hc => hcond ⟨by
                have h2 := congrArg Card.flipSuit hc.1
                rw [Card.flipSuit_flipSuit, Card.flipSuit_flipSuit] at h2
                exact h2, hc.2⟩), if_neg hcond]
            rfl
  | pileStack c =>
      show (match st.flipAll.board.topOf (Sum.inr (Card.flipSuit c)),
                  st.flipAll.board.bottomOf (Card.flipSuit c) with
            | none, some b =>
                if (Card.flipSuit c).rank.toIdx = st.flipAll.heights (Card.flipSuit c).suit then
                  some { st.flipAll with
                    board := st.flipAll.board.detach b,
                    heights := fun s => if s = (Card.flipSuit c).suit then st.flipAll.heights s + 1
                                        else st.flipAll.heights s }
                else none
            | _, _ => none)
          = Option.map State.flipAll
              (match st.board.topOf (Sum.inr c), st.board.bottomOf c with
               | none, some b =>
                   if c.rank.toIdx = st.heights c.suit then
                     some { st with
                       board := st.board.detach b,
                       heights := fun s => if s = c.suit then st.heights s + 1
                                           else st.heights s }
                   else none
               | _, _ => none)
      rw [State.flipAll_board_topOf_inr, State.flipAll_board_bottomOf]
      cases ht : st.board.topOf (Sum.inr c) with
      | some x => rfl
      | none =>
          cases hb : st.board.bottomOf c with
          | none => rfl
          | some b =>
              show (if (Card.flipSuit c).rank.toIdx = st.flipAll.heights (Card.flipSuit c).suit
                    then some { st.flipAll with
                      board := st.flipAll.board.detach (Base.flipBase b),
                      heights := fun s => if s = (Card.flipSuit c).suit then st.flipAll.heights s + 1
                                          else st.flipAll.heights s }
                  else none)
                = Option.map State.flipAll
                    (if c.rank.toIdx = st.heights c.suit then
                      some { st with
                        board := st.board.detach b,
                        heights := fun s => if s = c.suit then st.heights s + 1
                                            else st.heights s }
                    else none)
              rw [show (Card.flipSuit c).rank.toIdx = c.rank.toIdx from rfl,
                  show st.flipAll.heights (Card.flipSuit c).suit = st.heights c.suit from
                    State.flipAll_heights_probe st c.suit,
                  State.flipAll_board_detach]
              by_cases hcond : c.rank.toIdx = st.heights c.suit
              · rw [if_pos hcond, if_pos hcond]
                rw [State.flipAll_bump]
                rfl
              · rw [if_neg hcond, if_neg hcond]
                rfl
  | stackPile c b =>
      show (if (Card.flipSuit c).rank.toIdx + 1 = st.flipAll.heights (Card.flipSuit c).suit
                ∧ st.flipAll.canPlace (Card.flipSuit c) (b.flipBase) then
              (match st.flipAll.board.attach b.flipBase (Card.flipSuit c) with
               | none => none
               | some bd => some { st.flipAll with
                 board := bd,
                 heights := fun s => if s = (Card.flipSuit c).suit then st.flipAll.heights s - 1
                                     else st.flipAll.heights s })
              else none)
          = Option.map State.flipAll
              (if c.rank.toIdx + 1 = st.heights c.suit ∧ st.canPlace c b then
                (match st.board.attach b c with
                 | none => none
                 | some bd => some { st with
                   board := bd,
                   heights := fun s => if s = c.suit then st.heights s - 1 else st.heights s })
                else none)
      rw [show (Card.flipSuit c).rank.toIdx = c.rank.toIdx from rfl,
          show st.flipAll.heights (Card.flipSuit c).suit = st.heights c.suit from
            State.flipAll_heights_probe st c.suit,
          State.flipAll_canPlace]
      by_cases hcond : c.rank.toIdx + 1 = st.heights c.suit ∧ st.canPlace c b = true
      · rw [if_pos hcond, if_pos hcond]
        rw [State.flipAll_board_attach]
        cases hatt : st.board.attach b c with
        | none => rfl
        | some bd =>
            rw [State.flipAll_drop]
            rfl
      · rw [if_neg hcond, if_neg hcond]
        rfl
  | pilePile c b =>
      show (match st.flipAll.board.bottomOf (Card.flipSuit c) with
            | none => none
            | some b₀ =>
                if b₀ ≠ b.flipBase ∧ st.flipAll.canMoveRun (Card.flipSuit c) (b.flipBase) then
                  (match (st.flipAll.board.detach b₀).attach b.flipBase (Card.flipSuit c) with
                   | some bd => some { st.flipAll with board := bd }
                   | none => none)
                else none)
          = Option.map State.flipAll
              (match st.board.bottomOf c with
               | none => none
               | some b₀ =>
                   if b₀ ≠ b ∧ st.canMoveRun c b then
                     (match (st.board.detach b₀).attach b c with
                      | some bd => some { st with board := bd }
                      | none => none)
                   else none)
      rw [State.flipAll_board_bottomOf]
      cases hb : st.board.bottomOf c with
      | none => rfl
      | some b₀ =>
          show (if (Base.flipBase b₀) ≠ b.flipBase
                    ∧ st.flipAll.canMoveRun (Card.flipSuit c) (b.flipBase) then
                  (match (st.flipAll.board.detach (Base.flipBase b₀)).attach b.flipBase
                        (Card.flipSuit c) with
                   | some bd => some { st.flipAll with board := bd }
                   | none => none)
                else none)
            = Option.map State.flipAll
                (if b₀ ≠ b ∧ st.canMoveRun c b then
                  (match (st.board.detach b₀).attach b c with
                   | some bd => some { st with board := bd }
                   | none => none)
                  else none)
          rw [State.flipAll_canMoveRun, State.flipAll_board_detach, Board.mapBy_attach]
          by_cases hcond : b₀ ≠ b ∧ st.canMoveRun c b = true
          · rw [if_pos ⟨fun hbeq => hcond.1 (Base.flipBase_inj hbeq), hcond.2⟩, if_pos hcond]
            cases hatt : (st.board.detach b₀).attach b c with
            | none => rfl
            | some bd =>
                show some { st.flipAll with board := Board.mapBy bd }
                  = Option.map State.flipAll (some { st with board := bd })
                rfl
          · rw [if_neg (fun hc => hcond ⟨fun hbeq => hc.1 (congrArg Base.flipBase hbeq), hc.2⟩),
               if_neg hcond]
            rfl

/-- The win predicate is twin-invariant. -/
theorem State.flipAll_isWin {st : State} (h : st.isWin = true) : st.flipAll.isWin = true := by
  have h' : ∀ s ∈ Suit.all, decide (st.heights s = 13) = true :=
    (List.all_eq_true.mp
      (show Suit.all.all (fun s => decide (st.heights s = 13)) = true from h))
  show Suit.all.all (fun s => decide (st.flipAll.heights s = 13)) = true
  rw [List.all_eq_true]
  intro s _
  exact h' s.flipPair (Suit.mem_all _)

/-- Running a flipped play is running the play, flipped. -/
theorem State.run_flipAll (st : State) : ∀ (play : List Move),
    st.flipAll.run (play.map Move.flipMove) = (st.run play).map State.flipAll := by
  intro play
  revert st
  induction play with
  | nil => intro st; rfl
  | cons m ms ih =>
      intro st
      show (match st.flipAll.apply (Move.flipMove m) with
            | some st' => st'.run (ms.map Move.flipMove)
            | none => none)
          = Option.map State.flipAll
              (match st.apply m with
               | some st' => st'.run ms
               | none => none)
      rw [apply_flipAll]
      cases hm : st.apply m with
      | none => rfl
      | some s'' =>
          show (State.flipAll s'').run (ms.map Move.flipMove)
              = Option.map State.flipAll (s''.run ms)
          exact ih s''

/-- **T (twin swap)**: solvability is invariant under the relabeling,
by induction on the play via `apply_flipAll`. -/
theorem solvable_flipAll {st : State} (h : st.solvableFrom) :
    st.flipAll.solvableFrom := by
  obtain ⟨play, st', hrun, hwin⟩ := h
  refine ⟨play.map Move.flipMove, State.flipAll st', ?_, ?_⟩
  · rw [State.run_flipAll, hrun]
    rfl
  · exact State.flipAll_isWin hwin

/-- **The no-pile-to-pile restriction (ledger B-legs)**: on
well-formed states, the full physical game and the engine's restricted
move set have the same solvability.  TODO: the compression/reshape
arguments of no_pile_to_pile.md — now a statement about a move subset
of ONE model, not a correspondence between two formalizations. -/
theorem solvable_engine_iff {st : State} (hwf : st.WF) :
    st.solvableFrom ↔ st.solvableEngine := sorry

/-- After attaching `c` at `b`: any card that had a base still has
one (the attachment only adds `c` to the image). -/
theorem bottomOf_isSome_attach {bd : Board} {b : Base} {c : Card}
    {bd' : Board} (hatt : bd.attach b c = some bd') {d : Card}
    (hds : (bd.bottomOf d).isSome = true) : (bd'.bottomOf d).isSome = true := by
  obtain ⟨b'', hb''⟩ : ∃ b'', bd.bottomOf d = some b'' := by
    cases hh : bd.bottomOf d with
    | none => rw [hh] at hds; simp at hds
    | some b'' => exact ⟨b'', rfl⟩
  have htb : bd.topOf b'' = some d := (Board.bottomOf_eq bd d b'').mp hb''
  by_cases hdb : d = c
  · rw [hdb, (Board.bottomOf_eq bd' c b).mpr (Board.attach_topOf _ _ _ hatt)]
    rfl
  · have hbbne : b'' ≠ b := by
      intro hcon
      have hfree : bd.topOf b = none :=
        (Board.attach_eq_some_iff bd b c).mp (by rw [hatt]; simp) |>.1
      rw [hcon] at htb
      rw [htb] at hfree
      simp at hfree
    rw [(Board.bottomOf_eq bd' d b'').mpr (by
      rw [Board.attach_topOf_ne _ _ _ hatt hbbne]
      exact htb)]
    rfl

/-- After detaching the card at `b`: a *different* card's base search
is unchanged. -/
theorem bottomOf_detach_ne {bd : Board} {b : Base} {c d : Card}
    (hbot : bd.topOf b = some c) (hdne : d ≠ c) :
    (bd.detach b).bottomOf d = bd.bottomOf d := by
  by_cases hh : bd.bottomOf d = none
  · rw [hh]
    refine (Board.bottomOf_eq_none _ d).mpr (fun b'' hb'' => ?_)
    by_cases hbb : b'' = b
    · subst hbb
      rw [Board.detach_topOf] at hb''
      exact absurd hb'' (by simp)
    · rw [Board.detach_topOf_ne _ _ _ hbb] at hb''
      exact ((Board.bottomOf_eq_none bd d).mp hh) b'' hb''
  · cases hbd : bd.bottomOf d with
    | none => exact absurd hbd hh
    | some b'' =>
      have htb : bd.topOf b'' = some d := (Board.bottomOf_eq bd d b'').mp hbd
      have hbbne : b'' ≠ b := by
        intro hcon; subst hcon
        exact hdne (Option.some.inj (hbot.symm.trans htb)).symm
      exact (Board.bottomOf_eq (bd.detach b) d b'').mpr (by
        rw [Board.detach_topOf_ne _ _ _ hbbne]
        exact htb)

/-- One deal step keeps the cursor in range. -/
theorem Cycle.dealOnce_cursor_le (s : Nat) (cy : Cycle Card) :
    (cy.dealOnce s).cursor ≤ cy.cards.length := by
  simp only [Cycle.dealOnce]
  split <;> simp <;> omega

/-- Last-element membership (local copy — `Initial`'s version is
upstream in the import order). -/
theorem mem_of_getLast' {l : List Card} {c : Card} (h : l.getLast? = some c) : c ∈ l := by
  rw [← head?_reverse_eq_getLast?] at h
  cases hrev : l.reverse with
  | nil => rw [hrev] at h; simp at h
  | cons x t =>
    rw [hrev] at h
    simp only [List.head?_cons, Option.some.injEq] at h
    have hx : c = x := h.symm
    subst hx
    have h1 : c ∈ l.reverse := by rw [hrev]; exact List.mem_cons_self
    exact List.mem_reverse.mp h1

/-- **WF is preserved by every legal move** — the maintenance lemma.
Arms: `draw` is a pure cursor rotation; `reveal` rides deal-adjacency
(cover on freshly-revealed boundary) and the piles/stock disjointness;
`deckPile`/`deckStack` splice the waste top out (noDup and membership
survive `removeIdx`; the cursor steps down); `pileStack`/`stackPile`
bump/drop the height of `c`'s suit within the rank bound;
`pilePile` moves the run within the matching (image unchanged). -/
theorem apply_wf {st : State} (hwf : st.WF) (m : Move) (st' : State)
    (h : st.apply m = some st') : st'.WF := by
  obtain ⟨hdeal, hdepths, hedges, hvis, hfound, hheights, hcursor, hstep, hnd, hmem⟩ := hwf
  cases m with
  | draw =>
    rw [apply_draw_iff] at h
    obtain ⟨rfl⟩ := h
    refine ⟨hdeal, hdepths, hedges, ?_, ?_, hheights, ?_, hstep, ?_⟩
    · intro c' hc'
      show Cycle.findFirstIdx (fun c'' => decide (c'' = c'))
          (Cycle.dealOnce st.drawStep st.stock).cards = none
      rw [Cycle.dealOnce_cards]
      exact hvis c' hc'
    · intro c' hc'
      show Cycle.findFirstIdx (fun c'' => decide (c'' = c'))
          (Cycle.dealOnce st.drawStep st.stock).cards = none
      rw [Cycle.dealOnce_cards]
      exact hfound c' hc'
    · show (Cycle.dealOnce st.drawStep st.stock).cursor
          ≤ (Cycle.dealOnce st.drawStep st.stock).cards.length
      rw [Cycle.dealOnce_cards]
      exact Cycle.dealOnce_cursor_le st.drawStep st.stock
    · refine ⟨?_, ?_⟩
      · show noDupCards (Cycle.dealOnce st.drawStep st.stock).cards
        rw [Cycle.dealOnce_cards]
        exact hnd
      · intro c'' hc''
        rw [Cycle.dealOnce_cards] at hc''
        exact hmem c'' hc''
  | reveal c =>
    rw [apply_reveal_iff] at h
    obtain ⟨ht, r, a, bd, hb, hp, ha, rfl⟩ := h
    have htop : st.topHidden a = some r :=
      of_decide_eq_true (findFirst_mem _ _ _ hp).2
    refine ⟨hdeal, ?_, ?_, ?_, hfound, hheights, hcursor, hstep, ⟨hnd, hmem⟩⟩
    · intro a'
      by_cases haa : a' = a
      · show (if a' = a then st.depths a - 1 else st.depths a') ≤ (st.deal.piles a').length
        rw [if_pos haa, haa]
        have := hdepths a
        omega
      · show (if a' = a then st.depths a - 1 else st.depths a') ≤ (st.deal.piles a').length
        rw [if_neg haa]
        exact hdepths a'
    · intro b c' hb'
      refine ⟨(Board.bottomOf_eq _ _ _).mpr hb', ?_⟩
      by_cases hbb : b = st.hiddenBase a
      · subst hbb
        have hnew : bd.topOf (st.hiddenBase a) = some r := Board.attach_topOf _ _ _ ha
        rw [hnew, Option.some.injEq] at hb'
        rw [← hb']
        simp only [State.hiddenBase]
        cases hb2 : ((st.hidden a).reverse.drop 1).head? with
        | none =>
            right
            exact head?_of_take_single (hidden_single hb2 htop)
        | some d =>
            exact Or.inl ⟨a, hidden_parent_dealt hb2 htop⟩
      · rw [Board.attach_topOf_ne _ _ _ ha hbb] at hb'
        obtain ⟨-, hleg⟩ := hedges b c' hb'
        cases b with
        | inl a => exact hleg
        | inr d =>
            rcases hleg with ⟨a, t, rest, hadj⟩ | ⟨his, hsit⟩
            · exact Or.inl ⟨a, t, rest, hadj⟩
            · exact Or.inr ⟨bottomOf_isSome_attach ha his, hsit⟩
    · intro c' hc'
      show (st.stock).posOf c' = none
      by_cases hcc : c' = r
      · rw [hcc]
        exact Cycle.posOf_eq_none (fun hcm =>
          Deal.piles_stock_disj hdeal (by
            rw [← List.take_append_drop (st.depths a) (st.deal.piles a)]
            exact List.mem_append_left _ (mem_of_getLast' htop)) (hmem r hcm))
      · have hbdr : ∃ b, bd.bottomOf c' = some b := by
          cases h : bd.bottomOf c' with
          | none =>
              simp only [State.isVis] at hc'
              rw [h] at hc'
              simp at hc'
          | some b => exact ⟨b, rfl⟩
        obtain ⟨b, hbr⟩ := hbdr
        have hbne : b ≠ st.hiddenBase a := by
          intro hcon
          have h1 : bd.topOf b = some c' := (Board.bottomOf_eq bd c' _).mp hbr
          have h2 : bd.topOf b = some r := by
            rw [hcon]
            exact Board.attach_topOf _ _ _ ha
          rw [h1] at h2
          exact hcc (Option.some.inj h2)
        have htb : bd.topOf b = some c' := (Board.bottomOf_eq bd c' b).mp hbr
        rw [Board.attach_topOf_ne _ _ _ ha hbne] at htb
        exact hvis c' (by
          show (st.board.bottomOf c').isSome = true
          rw [(Board.bottomOf_eq st.board c' b).mpr htb]
          rfl)
  | deckPile c b =>
    rw [apply_deckPile_iff] at h
    obtain ⟨hp, hcp, bd, hatt, rfl⟩ := h
    have hprev : st.stock.cursor ≠ 0 ∧ st.stock.cards[st.stock.cursor - 1]? = some c := by
      simp only [Cycle.prev] at hp
      split at hp
      · exact absurd hp (by simp)
      · exact ⟨by omega, hp⟩
    refine ⟨hdeal, hdepths, ?_, ?_, ?_, hheights, ?_, hstep, ?_⟩
    · intro b' c'' hb''
      refine ⟨(Board.bottomOf_eq _ _ _).mpr hb'', ?_⟩
      by_cases hbb : b' = b
      · rw [hbb, Board.attach_topOf _ _ _ hatt, Option.some.injEq] at hb''
        rw [hbb, ← hb'']
        obtain ⟨-, hcpm⟩ := Bool.and_eq_true_iff.mp hcp
        cases b with
        | inl a => exact Or.inl (of_decide_eq_true hcpm)
        | inr d =>
            obtain ⟨hvisd, hsit⟩ := Bool.and_eq_true_iff.mp hcpm
            refine Or.inr ⟨bottomOf_isSome_attach hatt ?_, hsit⟩
            show (st.board.bottomOf d).isSome = true
            exact hvisd
      · rw [Board.attach_topOf_ne _ _ _ hatt hbb] at hb''
        obtain ⟨-, hleg⟩ := hedges b' c'' hb''
        cases b' with
        | inl a => exact hleg
        | inr d =>
            rcases hleg with ⟨a, t, rest, hadj⟩ | ⟨his, hsit⟩
            · exact Or.inl ⟨a, t, rest, hadj⟩
            · exact Or.inr ⟨bottomOf_isSome_attach hatt his, hsit⟩
    · intro c' hc'
      show (st.stock.removeAt (st.stock.cursor - 1)).posOf c' = none
      by_cases hcc : c' = c
      · rw [hcc]
        have hmem2 : st.stock.cards[st.stock.cursor - 1]? = some c := hprev.2
        exact Cycle.posOf_eq_none (fun hcm =>
          Cycle.notMem_removeIdx_self (fun j hj => hnd j (st.stock.cursor - 1)
            (by have := (List.getElem?_eq_some_iff.mp hj).1
                have := (List.getElem?_eq_some_iff.mp hmem2).1
                omega)
            (by have := (List.getElem?_eq_some_iff.mp hmem2).1; omega)
            (by rw [hj, hmem2])) hcm)
      · have hbdr : ∃ bb, bd.bottomOf c' = some bb := by
          cases h : bd.bottomOf c' with
          | none =>
              simp only [State.isVis] at hc'
              rw [h] at hc'
              simp at hc'
          | some bb => exact ⟨bb, rfl⟩
        obtain ⟨bb, hbr⟩ := hbdr
        have hbbne : bb ≠ b := by
          intro hcon
          have h1 : bd.topOf bb = some c' := (Board.bottomOf_eq bd c' _).mp hbr
          rw [hcon, Board.attach_topOf _ _ _ hatt, Option.some.injEq] at h1
          exact hcc h1.symm
        have htb : bd.topOf bb = some c' := (Board.bottomOf_eq bd c' bb).mp hbr
        rw [Board.attach_topOf_ne _ _ _ hatt hbbne] at htb
        have hcold : st.isVis c' = true := by
          show (st.board.bottomOf c').isSome = true
          rw [(Board.bottomOf_eq st.board c' bb).mpr htb]
          rfl
        have hnc : c' ∉ st.stock.cards := by
          intro hcm
          have hpm := Cycle.posOf_mem hcm
          rw [hvis c' hcold] at hpm
          exact absurd hpm (by simp)
        exact Cycle.posOf_eq_none (fun hcm => hnc (Cycle.mem_removeIdx st.stock.cards (st.stock.cursor - 1) hcm))
    · intro c' hc'
      show (st.stock.removeAt (st.stock.cursor - 1)).posOf c' = none
      have hnc : c' ∉ st.stock.cards := by
        intro hcm
        have hpm := Cycle.posOf_mem hcm
        rw [hfound c' hc'] at hpm
        exact absurd hpm (by simp)
      exact Cycle.posOf_eq_none (fun hcm => hnc (Cycle.mem_removeIdx st.stock.cards (st.stock.cursor - 1) hcm))
    · show (if st.stock.cursor - 1 < st.stock.cursor then st.stock.cursor - 1
            else st.stock.cursor) ≤ (Cycle.removeIdx st.stock.cards (st.stock.cursor - 1)).length
      rw [if_pos (by omega)]
      have hilen : st.stock.cursor - 1 < st.stock.cards.length :=
        (List.getElem?_eq_some_iff.mp hprev.2).1
      have := Cycle.removeIdx_length st.stock.cards (st.stock.cursor - 1) hilen
      have := hcursor
      omega
    · refine ⟨noDupCards_removeIdx _ _ hnd, ?_⟩
      intro cc hcc
      exact hmem cc (Cycle.mem_removeIdx st.stock.cards (st.stock.cursor - 1) hcc)
  | deckStack c =>
    rw [apply_deckStack_iff] at h
    obtain ⟨hp, hrk, rfl⟩ := h
    have hprev : st.stock.cursor ≠ 0 ∧ st.stock.cards[st.stock.cursor - 1]? = some c := by
      simp only [Cycle.prev] at hp
      split at hp
      · exact absurd hp (by simp)
      · exact ⟨by omega, hp⟩
    refine ⟨hdeal, hdepths, hedges, ?_, ?_, ?_, ?_, hstep, ?_⟩
    · intro c' hc'
      show (st.stock.removeAt (st.stock.cursor - 1)).posOf c' = none
      have hnc : c' ∉ st.stock.cards := by
        intro hcm
        have hpm := Cycle.posOf_mem hcm
        rw [hvis c' hc'] at hpm
        exact absurd hpm (by simp)
      exact Cycle.posOf_eq_none (fun hcm => hnc (Cycle.mem_removeIdx st.stock.cards (st.stock.cursor - 1) hcm))
    · intro c' hc'
      show (st.stock.removeAt (st.stock.cursor - 1)).posOf c' = none
      by_cases hcc : c' = c
      · rw [hcc]
        have hmem2 : st.stock.cards[st.stock.cursor - 1]? = some c := hprev.2
        exact Cycle.posOf_eq_none (fun hcm =>
          Cycle.notMem_removeIdx_self (fun j hj => hnd j (st.stock.cursor - 1)
            (by have := (List.getElem?_eq_some_iff.mp hj).1
                have := (List.getElem?_eq_some_iff.mp hmem2).1
                omega)
            (by have := (List.getElem?_eq_some_iff.mp hmem2).1; omega)
            (by rw [hj, hmem2])) hcm)
      · have hon : c'.rank.toIdx <
            (if c'.suit = c.suit then st.heights c'.suit + 1 else st.heights c'.suit) :=
            of_decide_eq_true hc'
        have hold : st.onFound c' = true := by
          by_cases hsc : c'.suit = c.suit
          · rw [if_pos hsc] at hon
            rcases Nat.lt_or_ge c'.rank.toIdx (st.heights c'.suit) with hlt | heq
            · show decide (c'.rank.toIdx < st.heights c'.suit) = true
              exact decide_eq_true hlt
            · have heq2 : c'.rank.toIdx = st.heights c'.suit := by omega
              rw [hsc] at heq2
              have hr : c'.rank = c.rank := Rank.toIdx_inj (by rw [heq2, hrk])
              have hcard : c' = c := by
                cases c' with
                | mk s rk => cases c with
                  | mk s' rk' => rw [Card.mk.injEq]; exact ⟨hsc, hr⟩
              exact absurd hcard hcc
          · rw [if_neg hsc] at hon
            show decide (c'.rank.toIdx < st.heights c'.suit) = true
            exact decide_eq_true hon
        have hnc : c' ∉ st.stock.cards := by
          intro hcm
          have hpm := Cycle.posOf_mem hcm
          rw [hfound c' hold] at hpm
          exact absurd hpm (by simp)
        exact Cycle.posOf_eq_none (fun hcm => hnc (Cycle.mem_removeIdx st.stock.cards (st.stock.cursor - 1) hcm))
    · intro s
      by_cases hsc : s = c.suit
      · show (if s = c.suit then st.heights s + 1 else st.heights s) ≤ 13
        rw [if_pos hsc, hsc]
        have h1 : st.heights c.suit < 13 := by rw [← hrk]; exact Rank.toIdx_lt c.rank
        omega
      · show (if s = c.suit then st.heights s + 1 else st.heights s) ≤ 13
        rw [if_neg hsc]
        exact hheights s
    · show (if st.stock.cursor - 1 < st.stock.cursor then st.stock.cursor - 1
            else st.stock.cursor) ≤ (Cycle.removeIdx st.stock.cards (st.stock.cursor - 1)).length
      rw [if_pos (by omega)]
      have hilen : st.stock.cursor - 1 < st.stock.cards.length :=
        (List.getElem?_eq_some_iff.mp hprev.2).1
      have := Cycle.removeIdx_length st.stock.cards (st.stock.cursor - 1) hilen
      have := hcursor
      omega
    · refine ⟨noDupCards_removeIdx _ _ hnd, ?_⟩
      intro cc hcc
      exact hmem cc (Cycle.mem_removeIdx st.stock.cards (st.stock.cursor - 1) hcc)
  | pileStack c =>
    rw [apply_pileStack_iff] at h
    obtain ⟨ht, b, hb, hrk, rfl⟩ := h
    have hbot : st.board.topOf b = some c := (Board.bottomOf_eq st.board c b).mp hb
    refine ⟨hdeal, hdepths, ?_, ?_, ?_, ?_, hcursor, hstep, ⟨hnd, hmem⟩⟩
    · intro b' c' hb'
      refine ⟨(Board.bottomOf_eq _ _ _).mpr hb', ?_⟩
      have hb'ne : b' ≠ b := by
        intro hcon; subst hcon
        rw [Board.detach_topOf] at hb'
        exact absurd hb' (by simp)
      rw [Board.detach_topOf_ne _ _ _ hb'ne] at hb'
      obtain ⟨-, hleg⟩ := hedges b' c' hb'
      cases b' with
      | inl a => exact hleg
      | inr d =>
          have hdc : d ≠ c := by
            intro hcon
            rw [hcon] at hb'
            rw [ht] at hb'
            exact absurd hb' (by simp)
          rcases hleg with ⟨a, t, rest, hadj⟩ | ⟨his, hsit⟩
          · exact Or.inl ⟨a, t, rest, hadj⟩
          · refine Or.inr ⟨?_, hsit⟩
            rw [bottomOf_detach_ne hbot hdc]
            exact his
    · intro c' hc'
      show (st.stock).posOf c' = none
      by_cases hcc : c' = c
      · rw [hcc]
        exact hvis c (by
          show (st.board.bottomOf c).isSome = true
          rw [hb]
          rfl)
      · have hbdr : ∃ bb, (st.board.detach b).bottomOf c' = some bb := by
          cases h : (st.board.detach b).bottomOf c' with
          | none =>
              simp only [State.isVis] at hc'
              rw [h] at hc'
              simp at hc'
          | some bb => exact ⟨bb, rfl⟩
        obtain ⟨bb, hbr⟩ := hbdr
        have hbbne : bb ≠ b := by
          intro hcon
          have h1 : (st.board.detach b).topOf bb = some c' :=
            (Board.bottomOf_eq _ c' bb).mp hbr
          rw [hcon, Board.detach_topOf] at h1
          exact absurd h1 (by simp)
        have htb : (st.board.detach b).topOf bb = some c' :=
          (Board.bottomOf_eq _ c' bb).mp hbr
        rw [Board.detach_topOf_ne _ _ _ hbbne] at htb
        exact hvis c' (by
          show (st.board.bottomOf c').isSome = true
          rw [(Board.bottomOf_eq st.board c' bb).mpr htb]
          rfl)
    · intro c' hc'
      show (st.stock).posOf c' = none
      have hon : c'.rank.toIdx <
          (if c'.suit = c.suit then st.heights c'.suit + 1 else st.heights c'.suit) :=
          of_decide_eq_true hc'
      by_cases hsc : c'.suit = c.suit
      · rw [if_pos hsc] at hon
        rcases Nat.lt_or_ge c'.rank.toIdx (st.heights c'.suit) with hlt | heq
        · exact hfound c' (by
            show decide (c'.rank.toIdx < st.heights c'.suit) = true
            exact decide_eq_true hlt)
        · have heq2 : c'.rank.toIdx = st.heights c'.suit := by omega
          rw [hsc] at heq2
          have hr : c'.rank = c.rank := Rank.toIdx_inj (by rw [heq2, hrk])
          have hcard : c' = c := by
            cases c' with
            | mk s rk => cases c with
              | mk s' rk' => rw [Card.mk.injEq]; exact ⟨hsc, hr⟩
          rw [hcard]
          exact hvis c (by
            show (st.board.bottomOf c).isSome = true
            rw [hb]
            rfl)
      · rw [if_neg hsc] at hon
        exact hfound c' (by
          show decide (c'.rank.toIdx < st.heights c'.suit) = true
          exact decide_eq_true hon)
    · intro s
      by_cases hsc : s = c.suit
      · show (if s = c.suit then st.heights s + 1 else st.heights s) ≤ 13
        rw [if_pos hsc, hsc]
        have h1 : st.heights c.suit < 13 := by rw [← hrk]; exact Rank.toIdx_lt c.rank
        omega
      · show (if s = c.suit then st.heights s + 1 else st.heights s) ≤ 13
        rw [if_neg hsc]
        exact hheights s
  | stackPile c b =>
    rw [apply_stackPile_iff] at h
    obtain ⟨h1g, hcp, bd, hatt, rfl⟩ := h
    refine ⟨hdeal, hdepths, ?_, ?_, ?_, ?_, hcursor, hstep, ⟨hnd, hmem⟩⟩
    · intro b' c' hb'
      refine ⟨(Board.bottomOf_eq _ _ _).mpr hb', ?_⟩
      by_cases hbb : b' = b
      · rw [hbb, Board.attach_topOf _ _ _ hatt, Option.some.injEq] at hb'
        rw [hbb, ← hb']
        obtain ⟨-, hcpm⟩ := Bool.and_eq_true_iff.mp hcp
        cases b with
        | inl a => exact Or.inl (of_decide_eq_true hcpm)
        | inr d =>
            obtain ⟨hvisd, hsit⟩ := Bool.and_eq_true_iff.mp hcpm
            refine Or.inr ⟨bottomOf_isSome_attach hatt ?_, hsit⟩
            show (st.board.bottomOf d).isSome = true
            exact hvisd
      · rw [Board.attach_topOf_ne _ _ _ hatt hbb] at hb'
        obtain ⟨-, hleg⟩ := hedges b' c' hb'
        cases b' with
        | inl a => exact hleg
        | inr d =>
            rcases hleg with ⟨a, t, rest, hadj⟩ | ⟨his, hsit⟩
            · exact Or.inl ⟨a, t, rest, hadj⟩
            · exact Or.inr ⟨bottomOf_isSome_attach hatt his, hsit⟩
    · intro c' hc'
      show (st.stock).posOf c' = none
      by_cases hcc : c' = c
      · rw [hcc]
        have hold : st.onFound c = true := by
          show decide (c.rank.toIdx < st.heights c.suit) = true
          exact decide_eq_true (by omega)
        exact hfound c hold
      · have hbdr : ∃ b'', bd.bottomOf c' = some b'' := by
          cases h : bd.bottomOf c' with
          | none =>
              simp only [State.isVis] at hc'
              rw [h] at hc'
              simp at hc'
          | some b'' => exact ⟨b'', rfl⟩
        obtain ⟨b'', hbr⟩ := hbdr
        have hne2 : b'' ≠ b := by
          intro hcon
          have h1 : bd.topOf b'' = some c' := (Board.bottomOf_eq bd c' _).mp hbr
          rw [hcon, Board.attach_topOf _ _ _ hatt, Option.some.injEq] at h1
          exact hcc h1.symm
        have htb : bd.topOf b'' = some c' := (Board.bottomOf_eq bd c' b'').mp hbr
        rw [Board.attach_topOf_ne _ _ _ hatt hne2] at htb
        exact hvis c' (by
          show (st.board.bottomOf c').isSome = true
          rw [(Board.bottomOf_eq st.board c' b'').mpr htb]
          rfl)
    · intro c' hc'
      show (st.stock).posOf c' = none
      have hon : c'.rank.toIdx <
          (if c'.suit = c.suit then st.heights c'.suit - 1 else st.heights c'.suit) :=
          of_decide_eq_true hc'
      exact hfound c' (by
        by_cases hsc : c'.suit = c.suit
        · rw [if_pos hsc] at hon
          show decide (c'.rank.toIdx < st.heights c'.suit) = true
          exact decide_eq_true (by omega)
        · rw [if_neg hsc] at hon
          show decide (c'.rank.toIdx < st.heights c'.suit) = true
          exact decide_eq_true hon)
    · intro s
      by_cases hsc : s = c.suit
      · show (if s = c.suit then st.heights s - 1 else st.heights s) ≤ 13
        rw [if_pos hsc]
        have := hheights s
        omega
      · show (if s = c.suit then st.heights s - 1 else st.heights s) ≤ 13
        rw [if_neg hsc]
        exact hheights s
  | pilePile c b =>
    rw [apply_pilePile_iff] at h
    obtain ⟨b₀, hb, hbne, hcmr, bd, hatt, rfl⟩ := h
    obtain ⟨hcp, -⟩ := Bool.and_eq_true_iff.mp hcmr
    have hbot₀ : st.board.topOf b₀ = some c := (Board.bottomOf_eq st.board c b₀).mp hb
    refine ⟨hdeal, hdepths, ?_, ?_, hfound, hheights, hcursor, hstep, ⟨hnd, hmem⟩⟩
    · intro b' c' hb'
      refine ⟨(Board.bottomOf_eq _ _ _).mpr hb', ?_⟩
      by_cases hbb : b' = b
      · rw [hbb, Board.attach_topOf _ _ _ hatt, Option.some.injEq] at hb'
        rw [hbb, ← hb']
        obtain ⟨-, hcpm⟩ := Bool.and_eq_true_iff.mp hcp
        cases b with
        | inl a => exact Or.inl (of_decide_eq_true hcpm)
        | inr d =>
            obtain ⟨hvisd, hsit⟩ := Bool.and_eq_true_iff.mp hcpm
            refine Or.inr ⟨?_, hsit⟩
            by_cases hdc : d = c
            · rw [hdc, (Board.bottomOf_eq bd c (Sum.inr d)).mpr (Board.attach_topOf _ _ _ hatt)]
              rfl
            · exact bottomOf_isSome_attach hatt (by
                show ((st.board.detach b₀).bottomOf d).isSome = true
                rw [bottomOf_detach_ne hbot₀ hdc]
                exact hvisd)
      · have hbb'₀ : b' ≠ b₀ := by
          intro hcon
          have h1 : bd.topOf b' = some c' := hb'
          rw [hcon, Board.attach_topOf_ne _ _ _ hatt hbne, Board.detach_topOf] at h1
          exact absurd h1 (by simp)
        rw [Board.attach_topOf_ne _ _ _ hatt hbb, Board.detach_topOf_ne _ _ _ hbb'₀] at hb'
        obtain ⟨-, hleg⟩ := hedges b' c' hb'
        cases b' with
        | inl a => exact hleg
        | inr d =>
            rcases hleg with ⟨a, t, rest, hadj⟩ | ⟨his, hsit⟩
            · exact Or.inl ⟨a, t, rest, hadj⟩
            · refine Or.inr ⟨?_, hsit⟩
              by_cases hdc : d = c
              · rw [hdc, (Board.bottomOf_eq bd c b).mpr (Board.attach_topOf _ _ _ hatt)]
                rfl
              · exact bottomOf_isSome_attach hatt (by
                  show ((st.board.detach b₀).bottomOf d).isSome = true
                  rw [bottomOf_detach_ne hbot₀ hdc]
                  exact his)
    · intro c' hc'
      show (st.stock).posOf c' = none
      by_cases hcc : c' = c
      · rw [hcc]
        exact hvis c (by
          show (st.board.bottomOf c).isSome = true
          rw [hb]
          rfl)
      · have hbdr : ∃ b'', bd.bottomOf c' = some b'' := by
          cases h : bd.bottomOf c' with
          | none =>
              simp only [State.isVis] at hc'
              rw [h] at hc'
              simp at hc'
          | some b'' => exact ⟨b'', rfl⟩
        obtain ⟨b'', hbr⟩ := hbdr
        have hne1 : b'' ≠ b₀ := by
          intro hcon
          have h1 : bd.topOf b'' = some c' := (Board.bottomOf_eq bd c' _).mp hbr
          rw [hcon, Board.attach_topOf_ne _ _ _ hatt hbne, Board.detach_topOf] at h1
          exact absurd h1 (by simp)
        have hne2 : b'' ≠ b := by
          intro hcon
          have h1 : bd.topOf b'' = some c' := (Board.bottomOf_eq bd c' _).mp hbr
          rw [hcon, Board.attach_topOf _ _ _ hatt, Option.some.injEq] at h1
          exact hcc h1.symm
        have htb : bd.topOf b'' = some c' := (Board.bottomOf_eq bd c' b'').mp hbr
        rw [Board.attach_topOf_ne _ _ _ hatt hne2, Board.detach_topOf_ne _ _ _ hne1] at htb
        exact hvis c' (by
          show (st.board.bottomOf c').isSome = true
          rw [(Board.bottomOf_eq st.board c' b'').mpr htb]
          rfl)

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
