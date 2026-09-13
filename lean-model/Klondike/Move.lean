import Klondike.Pace
import Klondike.Kit

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

/-! ### The take/last index kit (Repair A/B maintenance) -/

/-- One past the length takes everything. -/
theorem take_length_succ_self {α : Type} : ∀ (l : List α), l.take (l.length + 1) = l
  | [] => rfl
  | a :: t => by
      show a :: t.take (t.length + 1) = a :: t
      exact congrArg (a :: ·) (take_length_succ_self t)

/-- The last element of an append-singleton. -/
theorem getLast?_append_single {α : Type} (t : List α) (u : α) :
    (t ++ [u]).getLast? = some u := by
  rw [← head?_reverse_eq_getLast?, List.reverse_append]
  rfl

/-- Membership in a `take` slice gives a bounded index. -/
theorem mem_take_index {α : Type} {l : List α} {n : Nat} {x : α} (h : x ∈ l.take n) :
    ∃ i, i < n ∧ l[i]? = some x := by
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp h
  have hib : i < n := by
    have hlen := (List.getElem?_eq_some_iff.mp hi).1
    rw [List.length_take] at hlen
    omega
  refine ⟨i, hib, ?_⟩
  rw [List.getElem?_take, if_pos hib] at hi
  exact hi

/-- An index into the list gives membership in any longer `take`. -/
theorem mem_take_of_index {α : Type} {l : List α} {n : Nat} {x : α} {i : Nat}
    (hlt : i < n) (hv : l[i]? = some x) : x ∈ l.take n := by
  refine List.mem_iff_getElem?.mpr ⟨i, ?_⟩
  rw [List.getElem?_take, if_pos hlt]
  exact hv

/-- The last element, by index. -/
theorem getLast?_index {α : Type} : ∀ (l : List α) (x : α), l.getLast? = some x →
    l[l.length - 1]? = some x := by
  intro l
  induction l with
  | nil => intro x h; simp at h
  | cons a t ih =>
      intro x h
      cases t with
      | nil => exact h
      | cons b t' =>
          have h' : (b :: t').getLast? = some x := h
          have hih := ih x h'
          have hidx : (a :: b :: t').length - 1 = ((b :: t').length - 1) + 1 := by
            simp only [List.length_cons]
            omega
          rw [hidx, List.getElem?_cons_succ]
          exact hih

/-- The element at position `m` is in no shorter `take` (uniqueness). -/
theorem notMem_take_of_get {l : List Card} {m : Nat} {x : Card}
    (hnd : noDupCards l) (hget : l[m]? = some x) : x ∉ l.take m := by
  intro hmem
  obtain ⟨i, hilt, hig⟩ := mem_take_index hmem
  have hb1 : i < l.length := (List.getElem?_eq_some_iff.mp hig).1
  have hb2 : m < l.length := (List.getElem?_eq_some_iff.mp hget).1
  have := hnd i m hb1 hb2 (hig.trans hget.symm)
  omega

/-- `take` is monotone in its bound. -/
theorem take_mono {α : Type} {m n : Nat} {l : List α} (hmn : m ≤ n) :
    l.take m ⊆ l.take n := by
  intro x hx
  obtain ⟨i, hilt, hig⟩ := mem_take_index hx
  exact mem_take_of_index (by omega) hig

/-- The boundary card, by index: `topHidden` reads position `depths − 1`. -/
theorem topHidden_get {st : State} {a : Anchor} {r : Card}
    (hle : st.depths a ≤ (st.deal.piles a).length) (h : st.topHidden a = some r) :
    (st.deal.piles a)[st.depths a - 1]? = some r := by
  have hlast : ((st.deal.piles a).take (st.depths a)).getLast? = some r := h
  have hlen : ((st.deal.piles a).take (st.depths a)).length = st.depths a := by
    rw [List.length_take]; omega
  have h1 := getLast?_index ((st.deal.piles a).take (st.depths a)) r hlast
  rw [hlen, List.getElem?_take] at h1
  by_cases hpos : st.depths a - 1 < st.depths a
  · rw [if_pos hpos] at h1; exact h1
  · exfalso
    have h0 : st.depths a = 0 := by omega
    rw [h0] at hlast
    simp at hlast

/-! ### The append/flatMap distinctness kit -/

/-- Distinctness of the left summand. -/
theorem noDupCards_append_left {l₁ l₂ : List Card} (h : noDupCards (l₁ ++ l₂)) :
    noDupCards l₁ := by
  intro i j hi hj heq
  have hb1 : i < (l₁ ++ l₂).length := by rw [List.length_append]; omega
  have hb2 : j < (l₁ ++ l₂).length := by rw [List.length_append]; omega
  have heq' : (l₁ ++ l₂)[i]? = (l₁ ++ l₂)[j]? := by
    rw [List.getElem?_append_left (by omega), List.getElem?_append_left (by omega)]
    exact heq
  have := h i j hb1 hb2 heq'
  omega

/-- Distinctness of the right summand. -/
theorem noDupCards_append_right {l₁ l₂ : List Card} (h : noDupCards (l₁ ++ l₂)) :
    noDupCards l₂ := by
  intro i j hi hj heq
  have hb1 : l₁.length + i < (l₁ ++ l₂).length := by rw [List.length_append]; omega
  have hb2 : l₁.length + j < (l₁ ++ l₂).length := by rw [List.length_append]; omega
  have heq' : (l₁ ++ l₂)[l₁.length + i]? = (l₁ ++ l₂)[l₁.length + j]? := by
    rw [List.getElem?_append_right (by omega), List.getElem?_append_right (by omega)]
    rw [Nat.add_sub_cancel_left, Nat.add_sub_cancel_left]
    exact heq
  have := h (l₁.length + i) (l₁.length + j) hb1 hb2 heq'
  omega

/-- The two summands of a distinct append are disjoint. -/
theorem noDupCards_append_disj {l₁ l₂ : List Card} (h : noDupCards (l₁ ++ l₂)) {c : Card}
    (h1 : c ∈ l₁) (h2 : c ∈ l₂) : False := by
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp h1
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp h2
  have hbi : i < l₁.length := (List.getElem?_eq_some_iff.mp hi).1
  have hbj : j < l₂.length := (List.getElem?_eq_some_iff.mp hj).1
  have hb1 : i < (l₁ ++ l₂).length := by rw [List.length_append]; omega
  have hb2 : l₁.length + j < (l₁ ++ l₂).length := by rw [List.length_append]; omega
  have v1 : (l₁ ++ l₂)[i]? = some c := by
    rw [List.getElem?_append_left (by omega)]; exact hi
  have v2 : (l₁ ++ l₂)[l₁.length + j]? = some c := by
    rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]; exact hj
  have := h i (l₁.length + j) hb1 hb2 (by rw [v1, v2])
  omega

/-- A member pile's slice is distinct. -/
theorem noDupCards_flatMap_of_mem {f : Anchor → List Card} : ∀ (as : List Anchor),
    noDupCards (as.flatMap f) → ∀ x ∈ as, noDupCards (f x) := by
  intro as
  induction as with
  | nil => intro _ x hx; cases hx
  | cons y t ih =>
      intro hnd x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact noDupCards_append_left hnd
      · exact ih (noDupCards_append_right hnd) x hx

/-- Different piles' slices are disjoint. -/
theorem piles_disj_aux {f : Anchor → List Card} : ∀ (as : List Anchor),
    noDupCards (as.flatMap f) → ∀ a a', a ∈ as → a' ∈ as → a ≠ a' →
      ∀ c, c ∈ f a → c ∈ f a' → False := by
  intro as
  induction as with
  | nil => intro _ a _ ha _ _ _; cases ha
  | cons y t ih =>
      intro hnd a a' ha ha' hne c hca hca'
      rcases List.mem_cons.mp ha with hae | ha
      · rcases List.mem_cons.mp ha' with hae' | ha'
        · exact hne (hae.trans hae'.symm)
        · refine noDupCards_append_disj hnd ?_ (List.mem_flatMap.mpr ⟨a', ha', hca'⟩)
          rw [← hae]
          exact hca
      · rcases List.mem_cons.mp ha' with hae' | ha'
        · refine noDupCards_append_disj hnd ?_ (List.mem_flatMap.mpr ⟨a, ha, hca⟩)
          rw [← hae']
          exact hca'
        · exact ih (noDupCards_append_right hnd) a a' ha ha' hne c hca hca'

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

/-- Each pile's slice is duplicate-free. -/
theorem pile_noDup {d : Deal} (hd : d.WF) (a : Anchor) : noDupCards (d.piles a) :=
  noDupCards_flatMap_of_mem Anchor.all (noDupCards_append_left hd.2.2) a a.mem_all

/-- The piles are pairwise disjoint (a card belongs to at most one pile). -/
theorem piles_disj {d : Deal} (hd : d.WF) {a a' : Anchor} {c : Card}
    (h1 : c ∈ d.piles a) (h2 : c ∈ d.piles a') : a = a' := by
  by_cases haa : a = a'
  · exact haa
  · exact (piles_disj_aux Anchor.all (noDupCards_append_left hd.2.2) a a'
      a.mem_all a'.mem_all haa c h1 h2).elim

end Deal

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

/-- The easy leg of the restriction: every engine play is a physical
play (`isEngine` is a move subset). -/
theorem solvable_of_engine {st : State} (h : st.solvableEngine) : st.solvableFrom := by
  obtain ⟨play, heng, st', hrun, hwin⟩ := h
  exact ⟨play, st', hrun, hwin⟩

/-- **The no-pile-to-pile restriction (ledger B-legs)**: on
well-formed states, the full physical game and the engine's restricted
move set have the same solvability.

REFUTED AS STATED (2026-09-13, prover-confirmed, axiom-clean — witness
`engine_iff_refuted` in `Temp\opencode\EngineWitness.lean`): the →
direction is FALSE.  The `pileStack∘stackPile` detour only relocates a
card that is *bare* (`topOf (inr c) = none`) *and* foundation-ready
(`c.rank.toIdx = heights c.suit`) — a `pilePile` of any other card has
no engine counterpart.  The witness: a WF state with pile p2 =
[♥3 (hidden), ♠5, ♥4] and hearts at 2.  Revealing ♥3 needs ♠5 bare
(♥4 must leave); ♥4's only non-`pilePile` exit is `pileStack`, which
needs hearts = 3, i.e. ♥3 stacked first — circular, so the engine is
stuck at hearts ≤ 2 forever (invariant along engine plays).  The full
game breaks the cycle with `pilePile ♥4 (♣5)` and wins in 31 moves.
Root cause: the abstract engine's `Reveal` is run-carrying (no_pile
§4, case 3) while the model's `reveal` demands a bare trigger — the
concrete move subset is strictly weaker.  Repair is an
orchestrator-level decision: state it for *initial* states (B2+B4's
content), or let `reveal` carry the run.  No downstream users. -/
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

/-- After detaching at `b`: the detached card itself is unseated. -/
theorem detach_bottomOf_self {bd : Board} {b : Base} {c : Card}
    (hbot : bd.topOf b = some c) : (bd.detach b).bottomOf c = none := by
  refine (Board.bottomOf_eq_none _ c).mpr (fun b' hb' => ?_)
  by_cases hbb : b' = b
  · rw [hbb, Board.detach_topOf] at hb'
    exact absurd hb' (by simp)
  · rw [Board.detach_topOf_ne _ _ _ hbb] at hb'
    exact hbb (bd.inj b' b c hb' hbot)

/-- After attaching `c` at `b`: a different card's seat is only gained,
never lost (the reverse of `bottomOf_isSome_attach`). -/
theorem bottomOf_isSome_attach_of_ne {bd : Board} {b : Base} {c d : Card}
    {bd' : Board} (hatt : bd.attach b c = some bd') (hne : d ≠ c) :
    (bd'.bottomOf d).isSome = true → (bd.bottomOf d).isSome = true := by
  intro hds
  obtain ⟨bb, hbb⟩ : ∃ bb, bd'.bottomOf d = some bb := by
    cases hh : bd'.bottomOf d with
    | none => rw [hh] at hds; simp at hds
    | some bb => exact ⟨bb, rfl⟩
  have h1 : bd'.topOf bb = some d := (Board.bottomOf_eq _ _ _).mp hbb
  by_cases hbb2 : bb = b
  · rw [hbb2, Board.attach_topOf _ _ _ hatt, Option.some.injEq] at h1
    exact absurd h1.symm hne
  · rw [Board.attach_topOf_ne _ _ _ hatt hbb2] at h1
    show (bd.bottomOf d).isSome = true
    rw [(Board.bottomOf_eq bd d bb).mpr h1]
    rfl

/-- One deal step keeps the cursor in range. -/
theorem Cycle.dealOnce_cursor_le (s : Nat) (cy : Cycle Card) :
    (cy.dealOnce s).cursor ≤ cy.cards.length := by
  simp only [Cycle.dealOnce]
  split <;> simp <;> omega

/-- **WF is preserved by every legal move** — the maintenance lemma.
Arms: `draw` is a pure cursor rotation; `reveal` rides deal-adjacency
(the freshly-seated boundary is the new `topHidden`, its cover's base
just became placed) and the piles/stock disjointness; `deckPile`/
`deckStack` splice the waste top out (noDup and membership survive
`removeIdx`; the cursor steps down); `pileStack`/`stackPile` bump/drop
the height of `c`'s suit within the rank bound — the bumped card leaves
the board/stock in the same move, so `founds_gone` holds; `pilePile`
moves the run within the matching (image unchanged).  The two new
conjuncts: `founds_gone` (foundation-passed cards are really gone)
and `vis_not_hidden` (the image and the hidden slices are disjoint). -/
theorem apply_wf {st : State} (hwf : st.WF) (m : Move) (st' : State)
    (h : st.apply m = some st') : st'.WF := by
  obtain ⟨hdeal, hdepths, hedges, hvis, hfound, hfgone, hvnh, hheights, hcursor, hstep, hnd, hmem⟩ := hwf
  cases m with
  | draw =>
    rw [apply_draw_iff] at h
    obtain ⟨rfl⟩ := h
    refine ⟨hdeal, hdepths, hedges, ?_, ?_, ?_, hvnh, hheights, ?_, hstep, ?_⟩
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
    · intro c' hc'
      refine ⟨(hfgone c' hc').1, ?_, (hfgone c' hc').2.2⟩
      show Cycle.findFirstIdx (fun c'' => decide (c'' = c'))
          (Cycle.dealOnce st.drawStep st.stock).cards = none
      rw [Cycle.dealOnce_cards]
      exact (hfgone c' hc').2.1
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
    have key : ∀ c'', c'' ≠ r → (bd.bottomOf c'').isSome = true →
        (st.board.bottomOf c'').isSome = true := by
      intro c'' hne hds
      obtain ⟨bb, hbb⟩ : ∃ bb, bd.bottomOf c'' = some bb := by
        cases hh : bd.bottomOf c'' with
        | none => rw [hh] at hds; simp at hds
        | some bb => exact ⟨bb, rfl⟩
      have h1 : bd.topOf bb = some c'' := (Board.bottomOf_eq _ _ _).mp hbb
      have hbne : bb ≠ st.hiddenBase a := by
        intro hcon
        rw [hcon] at h1
        rw [Board.attach_topOf _ _ _ ha] at h1
        exact hne (Option.some.inj h1.symm)
      rw [Board.attach_topOf_ne _ _ _ ha hbne] at h1
      show (st.board.bottomOf c'').isSome = true
      rw [(Board.bottomOf_eq st.board c'' bb).mpr h1]
      rfl
    refine ⟨hdeal, ?_, ?_, ?_, hfound, ?_, ?_, hheights, hcursor, hstep, ⟨hnd, hmem⟩⟩
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
            obtain ⟨pre, hpre⟩ := hidden_split hb2 htop
            have hlen2 : (st.hidden a).length = pre.length + 2 := by
              rw [hpre]
              simp only [List.length_append, List.length_cons, List.length_nil]
            have hmin : (st.hidden a).length = st.depths a := by
              show ((st.deal.piles a).take (st.depths a)).length = st.depths a
              rw [List.length_take]
              have := hdepths a
              omega
            have hplen : st.depths a = pre.length + 2 := by omega
            have hsub : st.depths a - 1 = pre.length + 1 := by omega
            have hsub2 : pre.length + 1 - pre.length = 1 := by omega
            have hs : st.deal.piles a = pre ++ d :: r :: (st.deal.piles a).drop (st.depths a) := by
              have htd : st.deal.piles a = st.hidden a ++ (st.deal.piles a).drop (st.depths a) :=
                (List.take_append_drop (st.depths a) (st.deal.piles a)).symm
              rw [hpre] at htd
              calc st.deal.piles a = (pre ++ [d, r]) ++ (st.deal.piles a).drop (st.depths a) := htd
                _ = pre ++ d :: r :: (st.deal.piles a).drop (st.depths a) := by simp
            have hnh : (st.deal.piles a).take (st.depths a - 1) = pre ++ [d] := by
              rw [hs, hsub, List.take_append, take_length_succ_self, hsub2]
              rfl
            obtain ⟨t, rest, hadj⟩ := hidden_parent_dealt hb2 htop
            refine Or.inl ⟨a, t, rest, hadj, Or.inl ⟨a, ?_⟩⟩
            show ((st.deal.piles a).take (if a = a then st.depths a - 1 else st.depths a)).getLast? = some d
            rw [if_pos rfl, hnh, getLast?_append_single]
      · rw [Board.attach_topOf_ne _ _ _ ha hbb] at hb'
        obtain ⟨-, hleg⟩ := hedges b c' hb'
        cases b with
        | inl a => exact hleg
        | inr d =>
            rcases hleg with ⟨a', t, rest, hadj, hbase⟩ | ⟨his, hsit⟩
            · refine Or.inl ⟨a', t, rest, hadj, ?_⟩
              rcases hbase with ⟨a'', hth⟩ | hpl
              · by_cases haa2 : a'' = a
                · refine Or.inr ?_
                  have hdr : d = r := by
                    have htra : st.topHidden a = some d := by rw [← haa2]; exact hth
                    exact Option.some.inj (htra.symm.trans htop)
                  rw [hdr]
                  show (bd.bottomOf r).isSome = true
                  rw [(Board.bottomOf_eq bd r (st.hiddenBase a)).mpr (Board.attach_topOf _ _ _ ha)]
                  rfl
                · refine Or.inl ⟨a'', ?_⟩
                  show ((st.deal.piles a'').take
                    (if a'' = a then st.depths a - 1 else st.depths a'')).getLast? = some d
                  rw [if_neg haa2]
                  exact hth
              · exact Or.inr (bottomOf_isSome_attach ha hpl)
            · exact Or.inr ⟨bottomOf_isSome_attach ha his, hsit⟩
    · intro c' hc'
      show (st.stock).posOf c' = none
      by_cases hcc : c' = r
      · rw [hcc]
        exact Cycle.posOf_eq_none (fun hcm =>
          Deal.piles_stock_disj hdeal (by
            rw [← List.take_append_drop (st.depths a) (st.deal.piles a)]
            exact List.mem_append_left _ (mem_of_getLast htop)) (hmem r hcm))
      · exact hvis c' (key c' hcc hc')
    · intro c' hc'
      by_cases hcc : c' = r
      · rw [hcc] at hc'
        exact absurd (mem_of_getLast htop) ((hfgone r hc').2.2 a)
      · refine ⟨?_, (hfgone c' hc').2.1, ?_⟩
        · show (bd.bottomOf c').isSome = false
          cases hh : (bd.bottomOf c').isSome with
          | false => rfl
          | true =>
              have hbo : (st.board.bottomOf c').isSome = true := key c' hcc hh
              have hf : (st.board.bottomOf c').isSome = false := (hfgone c' hc').1
              exact Bool.noConfusion (hf.symm.trans hbo)
        · intro a' hcm
          by_cases haa : a' = a
          · rw [haa] at hcm
            have hcm2 : c' ∈ (st.deal.piles a).take
                (if a = a then st.depths a - 1 else st.depths a) := hcm
            rw [if_pos rfl] at hcm2
            exact (hfgone c' hc').2.2 a (take_mono (by omega) hcm2)
          · have hcm2 : c' ∈ (st.deal.piles a').take
              (if a' = a then st.depths a - 1 else st.depths a') := hcm
            rw [if_neg haa] at hcm2
            exact (hfgone c' hc').2.2 a' hcm2
    · intro c' hc' a' hcm
      by_cases hcc : c' = r
      · rw [hcc] at hcm
        by_cases haa : a' = a
        · rw [haa] at hcm
          have hcm2 : r ∈ (st.deal.piles a).take
              (if a = a then st.depths a - 1 else st.depths a) := hcm
          rw [if_pos rfl] at hcm2
          exact notMem_take_of_get (Deal.pile_noDup hdeal a) (topHidden_get (hdepths a) htop) hcm2
        · have hcm2 : r ∈ (st.deal.piles a').take
            (if a' = a then st.depths a - 1 else st.depths a') := hcm
          rw [if_neg haa] at hcm2
          have hpm : r ∈ st.deal.piles a :=
            List.take_subset _ _ (show r ∈ (st.deal.piles a).take (st.depths a) from mem_of_getLast htop)
          have hpm2 : r ∈ st.deal.piles a' := List.take_subset _ _ hcm2
          exact haa (Deal.piles_disj hdeal hpm hpm2).symm
      · by_cases haa : a' = a
        · rw [haa] at hcm
          have hcm2 : c' ∈ (st.deal.piles a).take
              (if a = a then st.depths a - 1 else st.depths a) := hcm
          rw [if_pos rfl] at hcm2
          exact hvnh c' (key c' hcc hc') a (take_mono (by omega) hcm2)
        · have hcm2 : c' ∈ (st.deal.piles a').take
              (if a' = a then st.depths a - 1 else st.depths a') := hcm
          rw [if_neg haa] at hcm2
          exact hvnh c' (key c' hcc hc') a' hcm2
  | deckPile c b =>
    rw [apply_deckPile_iff] at h
    obtain ⟨hp, hcp, bd, hatt, rfl⟩ := h
    have hprev : st.stock.cursor ≠ 0 ∧ st.stock.cards[st.stock.cursor - 1]? = some c := by
      simp only [Cycle.prev] at hp
      split at hp
      · exact absurd hp (by simp)
      · exact ⟨by omega, hp⟩
    refine ⟨hdeal, hdepths, ?_, ?_, ?_, ?_, ?_, hheights, ?_, hstep, ?_⟩
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
            rcases hleg with ⟨a', t, rest, hadj, hbase⟩ | ⟨his, hsit⟩
            · refine Or.inl ⟨a', t, rest, hadj, ?_⟩
              rcases hbase with ⟨a'', hth⟩ | hpl
              · exact Or.inl ⟨a'', hth⟩
              · exact Or.inr (bottomOf_isSome_attach hatt hpl)
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
        exact Cycle.posOf_eq_none (fun hcm =>
          hnc (Cycle.mem_removeIdx st.stock.cards (st.stock.cursor - 1) hcm))
    · intro c' hc'
      show (st.stock.removeAt (st.stock.cursor - 1)).posOf c' = none
      have hnc : c' ∉ st.stock.cards := by
        intro hcm
        have hpm := Cycle.posOf_mem hcm
        rw [hfound c' hc'] at hpm
        exact absurd hpm (by simp)
      exact Cycle.posOf_eq_none (fun hcm => hnc (Cycle.mem_removeIdx st.stock.cards (st.stock.cursor - 1) hcm))
    · intro c' hc'
      by_cases hcc : c' = c
      · rw [hcc] at hc'
        have hpm : st.stock.posOf c ≠ none :=
          Cycle.posOf_mem (List.mem_iff_getElem?.mpr ⟨st.stock.cursor - 1, hprev.2⟩)
        rw [(hfgone c hc').2.1] at hpm
        exact (hpm rfl).elim
      · refine ⟨?_, ?_, (hfgone c' hc').2.2⟩
        · show (bd.bottomOf c').isSome = false
          cases hh : (bd.bottomOf c').isSome with
          | false => rfl
          | true =>
              have hbo : (st.board.bottomOf c').isSome = true :=
                bottomOf_isSome_attach_of_ne hatt hcc hh
              have hf : (st.board.bottomOf c').isSome = false := (hfgone c' hc').1
              exact Bool.noConfusion (hf.symm.trans hbo)
        · show (st.stock.removeAt (st.stock.cursor - 1)).posOf c' = none
          have hnc : c' ∉ st.stock.cards := by
            intro hcm
            have hpm := Cycle.posOf_mem hcm
            rw [(hfgone c' hc').2.1] at hpm
            exact absurd hpm (by simp)
          exact Cycle.posOf_eq_none (fun hcm =>
            hnc (Cycle.mem_removeIdx st.stock.cards (st.stock.cursor - 1) hcm))
    · intro c' hc' a' hcm
      by_cases hcc : c' = c
      · rw [hcc] at hcm
        have hcs : c ∈ st.deal.stock :=
          hmem c (List.mem_iff_getElem?.mpr ⟨st.stock.cursor - 1, hprev.2⟩)
        have hpp : c ∈ st.deal.piles a' :=
          List.take_subset _ _ (show c ∈ (st.deal.piles a').take (st.depths a') from hcm)
        exact (Deal.piles_stock_disj hdeal hpp hcs).elim
      · exact hvnh c' (bottomOf_isSome_attach_of_ne hatt hcc
          (show (bd.bottomOf c').isSome = true from hc')) a' hcm
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
    refine ⟨hdeal, hdepths, hedges, ?_, ?_, ?_, hvnh, ?_, ?_, hstep, ?_⟩
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
    · intro c' hc'
      by_cases hsc : c'.suit = c.suit
      · have hc2 : c'.rank.toIdx < st.heights c'.suit + 1 := by
          have h2 : c'.rank.toIdx <
              (if c'.suit = c.suit then st.heights c'.suit + 1 else st.heights c'.suit) := hc'
          rw [if_pos hsc] at h2
          exact h2
        rcases Nat.lt_or_ge c'.rank.toIdx (st.heights c'.suit) with hlt | hge
        · refine ⟨?_, ?_, (hfgone c' hlt).2.2⟩
          · exact (hfgone c' hlt).1
          · show (st.stock.removeAt (st.stock.cursor - 1)).posOf c' = none
            have hnc : c' ∉ st.stock.cards := by
              intro hcm
              have hpm := Cycle.posOf_mem hcm
              rw [(hfgone c' hlt).2.1] at hpm
              exact absurd hpm (by simp)
            exact Cycle.posOf_eq_none (fun hcm =>
              hnc (Cycle.mem_removeIdx st.stock.cards (st.stock.cursor - 1) hcm))
        · have heq2 : c'.rank.toIdx = st.heights c'.suit := by omega
          rw [hsc] at heq2
          have hr : c'.rank = c.rank := Rank.toIdx_inj (by rw [heq2, hrk])
          have hcard : c' = c := by
            cases c' with
            | mk s rk => cases c with
              | mk s' rk' => rw [Card.mk.injEq]; exact ⟨hsc, hr⟩
          rw [hcard]
          have hcs : c ∈ st.deal.stock :=
            hmem c (List.mem_iff_getElem?.mpr ⟨st.stock.cursor - 1, hprev.2⟩)
          refine ⟨?_, ?_, ?_⟩
          · show (st.board.bottomOf c).isSome = false
            cases hh : (st.board.bottomOf c).isSome with
            | false => rfl
            | true =>
                have hpm : st.stock.posOf c ≠ none :=
                  Cycle.posOf_mem (List.mem_iff_getElem?.mpr ⟨st.stock.cursor - 1, hprev.2⟩)
                rw [hvis c hh] at hpm
                exact absurd hpm (by simp)
          · have hmem2 : st.stock.cards[st.stock.cursor - 1]? = some c := hprev.2
            exact Cycle.posOf_eq_none (fun hcm =>
              Cycle.notMem_removeIdx_self (fun j hj => hnd j (st.stock.cursor - 1)
                (by have := (List.getElem?_eq_some_iff.mp hj).1
                    have := (List.getElem?_eq_some_iff.mp hmem2).1
                    omega)
                (by have := (List.getElem?_eq_some_iff.mp hmem2).1; omega)
                (by rw [hj, hmem2])) hcm)
          · intro a' hcm
            have hpp : c ∈ st.deal.piles a' :=
              List.take_subset _ _ (show c ∈ (st.deal.piles a').take (st.depths a') from hcm)
            exact (Deal.piles_stock_disj hdeal hpp hcs).elim
      · have hc2 : c'.rank.toIdx < st.heights c'.suit := by
          have h2 : c'.rank.toIdx <
              (if c'.suit = c.suit then st.heights c'.suit + 1 else st.heights c'.suit) := hc'
          rw [if_neg hsc] at h2
          exact h2
        refine ⟨(hfgone c' hc2).1, ?_, (hfgone c' hc2).2.2⟩
        show (st.stock.removeAt (st.stock.cursor - 1)).posOf c' = none
        have hnc : c' ∉ st.stock.cards := by
          intro hcm
          have hpm := Cycle.posOf_mem hcm
          rw [(hfgone c' hc2).2.1] at hpm
          exact absurd hpm (by simp)
        exact Cycle.posOf_eq_none (fun hcm =>
          hnc (Cycle.mem_removeIdx st.stock.cards (st.stock.cursor - 1) hcm))
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
    have key : ∀ c'', ((st.board.detach b).bottomOf c'').isSome = true →
        (st.board.bottomOf c'').isSome = true := by
      intro c'' hds
      obtain ⟨bb, hbb⟩ : ∃ bb, (st.board.detach b).bottomOf c'' = some bb := by
        cases hh : (st.board.detach b).bottomOf c'' with
        | none => rw [hh] at hds; simp at hds
        | some bb => exact ⟨bb, rfl⟩
      have h1 : (st.board.detach b).topOf bb = some c'' := (Board.bottomOf_eq _ _ _).mp hbb
      have hbne : bb ≠ b := by
        intro hcon
        rw [hcon, Board.detach_topOf] at h1
        exact absurd h1 (by simp)
      rw [Board.detach_topOf_ne _ _ _ hbne] at h1
      show (st.board.bottomOf c'').isSome = true
      rw [(Board.bottomOf_eq st.board c'' bb).mpr h1]
      rfl
    have hvisc : st.isVis c = true := by
      show (st.board.bottomOf c).isSome = true
      rw [hb]
      rfl
    refine ⟨hdeal, hdepths, ?_, ?_, ?_, ?_, ?_, ?_, hcursor, hstep, ⟨hnd, hmem⟩⟩
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
          rcases hleg with ⟨a', t, rest, hadj, hbase⟩ | ⟨his, hsit⟩
          · refine Or.inl ⟨a', t, rest, hadj, ?_⟩
            rcases hbase with ⟨a'', hth⟩ | hpl
            · exact Or.inl ⟨a'', hth⟩
            · refine Or.inr ?_
              show ((st.board.detach b).bottomOf d).isSome = true
              rw [bottomOf_detach_ne hbot hdc]
              exact hpl
          · refine Or.inr ⟨?_, hsit⟩
            rw [bottomOf_detach_ne hbot hdc]
            exact his
    · intro c' hc'
      show (st.stock).posOf c' = none
      by_cases hcc : c' = c
      · rw [hcc]
        exact hvis c hvisc
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
          exact hvis c hvisc
      · rw [if_neg hsc] at hon
        exact hfound c' (by
          show decide (c'.rank.toIdx < st.heights c'.suit) = true
          exact decide_eq_true hon)
    · intro c' hc'
      by_cases hsc : c'.suit = c.suit
      · have hc2 : c'.rank.toIdx < st.heights c'.suit + 1 := by
          have h2 : c'.rank.toIdx <
              (if c'.suit = c.suit then st.heights c'.suit + 1 else st.heights c'.suit) := hc'
          rw [if_pos hsc] at h2
          exact h2
        rcases Nat.lt_or_ge c'.rank.toIdx (st.heights c'.suit) with hlt | hge
        · refine ⟨?_, (hfgone c' hlt).2.1, (hfgone c' hlt).2.2⟩
          show ((st.board.detach b).bottomOf c').isSome = false
          cases hh : ((st.board.detach b).bottomOf c').isSome with
          | false => rfl
          | true =>
              have hbo : (st.board.bottomOf c').isSome = true := key c' hh
              have hf : (st.board.bottomOf c').isSome = false := (hfgone c' hlt).1
              exact Bool.noConfusion (hf.symm.trans hbo)
        · have heq2 : c'.rank.toIdx = st.heights c'.suit := by omega
          rw [hsc] at heq2
          have hr : c'.rank = c.rank := Rank.toIdx_inj (by rw [heq2, hrk])
          have hcard : c' = c := by
            cases c' with
            | mk s rk => cases c with
              | mk s' rk' => rw [Card.mk.injEq]; exact ⟨hsc, hr⟩
          rw [hcard]
          refine ⟨?_, hvis c hvisc, fun a' hcm => hvnh c hvisc a' hcm⟩
          show ((st.board.detach b).bottomOf c).isSome = false
          rw [detach_bottomOf_self hbot]
          rfl
      · have hc2 : c'.rank.toIdx < st.heights c'.suit := by
          have h2 : c'.rank.toIdx <
              (if c'.suit = c.suit then st.heights c'.suit + 1 else st.heights c'.suit) := hc'
          rw [if_neg hsc] at h2
          exact h2
        refine ⟨?_, (hfgone c' hc2).2.1, (hfgone c' hc2).2.2⟩
        show ((st.board.detach b).bottomOf c').isSome = false
        cases hh : ((st.board.detach b).bottomOf c').isSome with
        | false => rfl
        | true =>
            have hbo : (st.board.bottomOf c').isSome = true := key c' hh
            have hf : (st.board.bottomOf c').isSome = false := (hfgone c' hc2).1
            exact Bool.noConfusion (hf.symm.trans hbo)
    · intro c' hc' a' hcm
      exact hvnh c' (key c' (show ((st.board.detach b).bottomOf c').isSome = true from hc')) a' hcm
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
    refine ⟨hdeal, hdepths, ?_, ?_, ?_, ?_, ?_, ?_, hcursor, hstep, ⟨hnd, hmem⟩⟩
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
            rcases hleg with ⟨a', t, rest, hadj, hbase⟩ | ⟨his, hsit⟩
            · refine Or.inl ⟨a', t, rest, hadj, ?_⟩
              rcases hbase with ⟨a'', hth⟩ | hpl
              · exact Or.inl ⟨a'', hth⟩
              · exact Or.inr (bottomOf_isSome_attach hatt hpl)
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
    · intro c' hc'
      have hcold : c'.rank.toIdx < st.heights c'.suit := by
        have h2 : c'.rank.toIdx <
            (if c'.suit = c.suit then st.heights c'.suit - 1 else st.heights c'.suit) := hc'
        by_cases hsc : c'.suit = c.suit
        · rw [if_pos hsc] at h2; omega
        · rw [if_neg hsc] at h2; omega
      have hcne : c' ≠ c := by
        intro hcon
        rw [hcon] at hc'
        have h2 : c.rank.toIdx <
            (if c.suit = c.suit then st.heights c.suit - 1 else st.heights c.suit) := hc'
        rw [if_pos rfl] at h2
        omega
      refine ⟨?_, (hfgone c' hcold).2.1, (hfgone c' hcold).2.2⟩
      show (bd.bottomOf c').isSome = false
      cases hh : (bd.bottomOf c').isSome with
      | false => rfl
      | true =>
          have hbo : (st.board.bottomOf c').isSome = true :=
            bottomOf_isSome_attach_of_ne hatt hcne hh
          have hf : (st.board.bottomOf c').isSome = false := (hfgone c' hcold).1
          exact Bool.noConfusion (hf.symm.trans hbo)
    · intro c' hc' a' hcm
      by_cases hcc : c' = c
      · rw [hcc] at hcm
        exact (hfgone c (by rw [← h1g]; omega)).2.2 a' hcm
      · exact hvnh c' (bottomOf_isSome_attach_of_ne hatt hcc
          (show (bd.bottomOf c').isSome = true from hc')) a' hcm
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
    have key : ∀ c'', (bd.bottomOf c'').isSome = true →
        (st.board.bottomOf c'').isSome = true := by
      intro c'' hds
      obtain ⟨bb, hbb⟩ : ∃ bb, bd.bottomOf c'' = some bb := by
        cases hh : bd.bottomOf c'' with
        | none => rw [hh] at hds; simp at hds
        | some bb => exact ⟨bb, rfl⟩
      have h1 : bd.topOf bb = some c'' := (Board.bottomOf_eq _ _ _).mp hbb
      by_cases hbb2 : bb = b
      · rw [hbb2, Board.attach_topOf _ _ _ hatt, Option.some.injEq] at h1
        show (st.board.bottomOf c'').isSome = true
        rw [← h1, hb]
        rfl
      · have hbb0 : bb ≠ b₀ := by
          intro hcon
          rw [Board.attach_topOf_ne _ _ _ hatt hbb2] at h1
          rw [hcon, Board.detach_topOf] at h1
          exact absurd h1 (by simp)
        rw [Board.attach_topOf_ne _ _ _ hatt hbb2, Board.detach_topOf_ne _ _ _ hbb0] at h1
        show (st.board.bottomOf c'').isSome = true
        rw [(Board.bottomOf_eq st.board c'' bb).mpr h1]
        rfl
    have hkept : ∀ d, (st.board.bottomOf d).isSome = true → (bd.bottomOf d).isSome = true := by
      intro d hd0
      by_cases hdc : d = c
      · rw [hdc, (Board.bottomOf_eq bd c b).mpr (Board.attach_topOf _ _ _ hatt)]
        rfl
      · exact bottomOf_isSome_attach hatt (by
          show ((st.board.detach b₀).bottomOf d).isSome = true
          rw [bottomOf_detach_ne hbot₀ hdc]
          exact hd0)
    refine ⟨hdeal, hdepths, ?_, ?_, hfound, ?_, ?_, hheights, hcursor, hstep, ⟨hnd, hmem⟩⟩
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
            exact Or.inr ⟨hkept d hvisd, hsit⟩
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
            rcases hleg with ⟨a', t, rest, hadj, hbase⟩ | ⟨his, hsit⟩
            · refine Or.inl ⟨a', t, rest, hadj, ?_⟩
              rcases hbase with ⟨a'', hth⟩ | hpl
              · exact Or.inl ⟨a'', hth⟩
              · exact Or.inr (hkept d hpl)
            · exact Or.inr ⟨hkept d his, hsit⟩
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
    · intro c' hc'
      refine ⟨?_, (hfgone c' hc').2.1, (hfgone c' hc').2.2⟩
      show (bd.bottomOf c').isSome = false
      cases hh : (bd.bottomOf c').isSome with
      | false => rfl
      | true =>
          have hbo : (st.board.bottomOf c').isSome = true := key c' hh
          have hf : (st.board.bottomOf c').isSome = false := (hfgone c' hc').1
          exact Bool.noConfusion (hf.symm.trans hbo)
    · intro c' hc' a' hcm
      exact hvnh c' (key c' (show (bd.bottomOf c').isSome = true from hc')) a' hcm
/-! ### The Draw-commitment commutation kit (C13's adjacent half)

`applyDrawTo`'s stock op normalizes to `⟨removeIdx cards i, i⟩`
(`Cycle.removeAt_drawTo`); the *second* draw of each order finds its
card at the first-occurrence position of the spliced list (the shift
lemma for a card after the splice, the keep lemma for one before it);
the board part is two `attach`es at distinct bases.  Theorems.lean's
`drawTo_comm_modAdjacent` is the mod-adjacent generalization (with the
step guard for the wrap case); this file is its upstream, so the kit
lives here under `Cycle`/`Board` names. -/

/-- The Draw-commitment's stock successor: jump past `i`, splice `i`
out — the cursor lands exactly on `i`. -/
theorem Cycle.removeAt_drawTo {α : Type} (i : Nat) (cy : Cycle α) :
    (cy.drawTo i).removeAt i = { cards := Cycle.removeIdx cy.cards i, cursor := i } := by
  simp only [Cycle.removeAt, Cycle.drawTo, if_pos (by omega : i < i + 1),
    Nat.add_sub_cancel]

/-- Splicing out an earlier position shifts a later first occurrence
down by one. -/
theorem Cycle.findFirstIdx_removeIdx_shift {α : Type} (p : α → Bool) :
    ∀ (l : List α) (q r : Nat), Cycle.findFirstIdx p l = some r → q < r →
      Cycle.findFirstIdx p (Cycle.removeIdx l q) = some (r - 1) := by
  intro l
  induction l with
  | nil =>
      intro q r h _
      exact absurd h (by simp [Cycle.findFirstIdx])
  | cons a t ih =>
      intro q r h hqr
      have hc : (if p a then some 0 else (Cycle.findFirstIdx p t).map Nat.succ) = some r := h
      by_cases hpa : p a = true
      · rw [if_pos hpa, Option.some.injEq] at hc
        exact absurd hqr (by omega)
      · rw [if_neg hpa] at hc
        cases q with
        | zero =>
            rw [Cycle.removeIdx_zero]
            obtain ⟨r', hr', hrr⟩ := Option.map_eq_some_iff.mp hc
            rw [hr']
            exact congrArg some (by omega)
        | succ q' =>
            rw [Cycle.removeIdx_succ]
            obtain ⟨r', hr', hrr⟩ := Option.map_eq_some_iff.mp hc
            have hih := ih q' r' hr' (by omega)
            show (if p a then some 0
              else (Cycle.findFirstIdx p (Cycle.removeIdx t q')).map Nat.succ) = some (r - 1)
            rw [if_neg hpa, hih, Option.map_some]
            exact congrArg some (by omega)

/-- Splicing out a later position leaves an earlier first occurrence
where it was. -/
theorem Cycle.findFirstIdx_removeIdx_keep {α : Type} (p : α → Bool) :
    ∀ (l : List α) (p₀ q : Nat), Cycle.findFirstIdx p l = some p₀ → p₀ < q →
      Cycle.findFirstIdx p (Cycle.removeIdx l q) = some p₀ := by
  intro l
  induction l with
  | nil =>
      intro p₀ q h _
      exact absurd h (by simp [Cycle.findFirstIdx])
  | cons a t ih =>
      intro p₀ q h hpq
      have hc : (if p a then some 0 else (Cycle.findFirstIdx p t).map Nat.succ) = some p₀ := h
      cases q with
      | zero => exact absurd hpq (by omega)
      | succ q' =>
          rw [Cycle.removeIdx_succ]
          by_cases hpa : p a = true
          · rw [if_pos hpa, Option.some.injEq] at hc
            show (if p a then some 0
              else (Cycle.findFirstIdx p (Cycle.removeIdx t q')).map Nat.succ) = some p₀
            rw [if_pos hpa, ← hc]
          · rw [if_neg hpa] at hc
            obtain ⟨r', hr', hrr⟩ := Option.map_eq_some_iff.mp hc
            have hih := ih r' q' hr' (by omega)
            show (if p a then some 0
              else (Cycle.findFirstIdx p (Cycle.removeIdx t q')).map Nat.succ) = some p₀
            rw [if_neg hpa, hih, Option.map_some]
            exact congrArg some (by omega)

/-- The shift lemma, `posOf` packaging (the cursor is never read). -/
theorem Cycle.posOf_removeIdx_shift {x : Card} {l : List Card} {cur cur' : Nat} {q r : Nat}
    (h : Cycle.posOf x ⟨l, cur⟩ = some r) (hqr : q < r) :
    Cycle.posOf x ⟨Cycle.removeIdx l q, cur'⟩ = some (r - 1) :=
  Cycle.findFirstIdx_removeIdx_shift _ l q r h hqr

/-- The keep lemma, `posOf` packaging (the cursor is never read). -/
theorem Cycle.posOf_removeIdx_keep {x : Card} {l : List Card} {cur cur' : Nat} {p q : Nat}
    (h : Cycle.posOf x ⟨l, cur⟩ = some p) (hpq : p < q) :
    Cycle.posOf x ⟨Cycle.removeIdx l q, cur'⟩ = some p :=
  Cycle.findFirstIdx_removeIdx_keep _ l p q h hpq

/-- The guard's index is the plain stock position. -/
theorem State.reachablePos_posOf {st : State} {c : Card} {i : Nat}
    (h : st.reachablePos c = some i) : st.stock.posOf c = some i := by
  simp only [State.reachablePos] at h
  split at h
  · next hpos =>
      cases hp : st.stock.posOf c with
      | none => rw [hp] at h; simp at h
      | some i' =>
          rw [hp] at h
          simp at h
          rw [h.2]
  · simp at h

/-- A successful Draw commitment's shape: the guard's index, the
board attach, and the successor with the spliced stock. -/
theorem applyDrawTo_shape {st : State} {c : Card} {b : Base} {s' : State}
    (h : st.applyDrawTo c b = some s') :
    ∃ i bd, st.reachablePos c = some i ∧ st.board.attach b c = some bd ∧
      s' = { st with
             board := bd,
             stock := { cards := Cycle.removeIdx st.stock.cards i, cursor := i } } := by
  simp only [State.applyDrawTo] at h
  cases hr : st.reachablePos c with
  | none => rw [hr] at h; simp at h
  | some i =>
      rw [hr] at h
      cases ha : st.board.attach b c with
      | none => rw [ha] at h; simp at h
      | some bd =>
          rw [ha] at h
          simp at h
          refine ⟨i, bd, rfl, rfl, ?_⟩
          rw [← h, Cycle.removeAt_drawTo]

/-- Two attachments at distinct bases commute. -/
theorem Board.attach_attach_comm {bd : Board} {b b' : Base} {c c' : Card}
    {bd₁ bd₂ bd₃ bd₄ : Board} (hbb : b ≠ b')
    (h₁ : bd.attach b c = some bd₁) (h₂ : bd₁.attach b' c' = some bd₂)
    (h₃ : bd.attach b' c' = some bd₃) (h₄ : bd₃.attach b c = some bd₄) :
    bd₂ = bd₄ := by
  refine Board.ext_topOf (funext (fun x => ?_))
  by_cases hxb : x = b
  · rw [hxb, Board.attach_topOf_ne _ _ _ h₂ hbb, Board.attach_topOf _ _ _ h₁,
      Board.attach_topOf _ _ _ h₄]
  · by_cases hxb' : x = b'
    · rw [hxb', Board.attach_topOf _ _ _ h₂, Board.attach_topOf_ne _ _ _ h₄ (Ne.symm hbb),
        Board.attach_topOf _ _ _ h₃]
    · rw [Board.attach_topOf_ne _ _ _ h₂ hxb', Board.attach_topOf_ne _ _ _ h₁ hxb,
        Board.attach_topOf_ne _ _ _ h₄ hxb, Board.attach_topOf_ne _ _ _ h₃ hxb']

/-- **C13 pilot (model level)**: adjacent Draw-commitments commute
(distinct bases) — the non-wrap instance at every draw step, the
step-1 cover of Theorems' guarded `drawTo_comm_modAdjacent`.  Both
orders' second draws splice at position `i` (`c'` shifts down from
`i + 1`, `c` stays at `i`), the boards agree by `attach` commutation,
and the card splices by `Cycle.removeIdx_comm`.  NOTE: non-adjacent
pairs land on *different cursors* (`drawTo_nonadjacent_diverge`) — the
engine's sweep/canonicalization is what recovers commutation there
(the C-IND landscape). -/
theorem drawTo_comm_adjacent {st : State} {c c' : Card} {b b' : Base}
    (hbb : b ≠ b') {i : Nat}
    (hic : st.stock.posOf c = some i)
    (hic' : st.stock.posOf c' = some (i + 1))
    {st₂ st₄ : State}
    (h₂ : (st.applyDrawTo c b >>= fun s => s.applyDrawTo c' b') = some st₂)
    (h₄ : (st.applyDrawTo c' b' >>= fun s => s.applyDrawTo c b) = some st₄) :
    st₂ = st₄ := by
  have hilt : i + 1 < st.stock.cards.length := Cycle.posOf_lt hic'
  obtain ⟨s₁, hA, hB⟩ := Option.bind_eq_some_iff.mp h₂
  obtain ⟨s₃, hC, hD⟩ := Option.bind_eq_some_iff.mp h₄
  obtain ⟨i₀, bd₁, hr₀, ha₁, hs₁⟩ := applyDrawTo_shape hA
  obtain ⟨k, bd₂, hrk, ha₂, hs₂⟩ := applyDrawTo_shape hB
  obtain ⟨j₀, bd₃, hr₁, ha₃, hs₃⟩ := applyDrawTo_shape hC
  obtain ⟨k', bd₄, hrk', ha₄, hs₄⟩ := applyDrawTo_shape hD
  have hi₀ : i₀ = i := Option.some.inj ((State.reachablePos_posOf hr₀).symm.trans hic)
  have hj₀ : j₀ = i + 1 := Option.some.inj ((State.reachablePos_posOf hr₁).symm.trans hic')
  rw [hi₀] at hs₁
  rw [hj₀] at hs₃
  have hs₁s : s₁.stock = { cards := Cycle.removeIdx st.stock.cards i, cursor := i } := by
    rw [hs₁]; try rfl
  have hs₃s : s₃.stock = { cards := Cycle.removeIdx st.stock.cards (i + 1), cursor := i + 1 } := by
    rw [hs₃]; try rfl
  have hb₁ : s₁.board = bd₁ := by rw [hs₁]; try rfl
  have hb₃ : s₃.board = bd₃ := by rw [hs₃]; try rfl
  rw [hb₁] at ha₂
  rw [hb₃] at ha₄
  have hpk : s₁.stock.posOf c' = some k := State.reachablePos_posOf hrk
  rw [hs₁s] at hpk
  have hpk' : s₃.stock.posOf c = some k' := State.reachablePos_posOf hrk'
  rw [hs₃s] at hpk'
  have hk : k = i :=
    Option.some.inj (hpk.symm.trans (Cycle.posOf_removeIdx_shift hic' (by omega)))
  have hk' : k' = i :=
    Option.some.inj (hpk'.symm.trans (Cycle.posOf_removeIdx_keep hic (by omega)))
  have hbd : bd₂ = bd₄ := Board.attach_attach_comm hbb ha₁ ha₂ ha₃ ha₄
  have hcomp₂ : st₂ = { st with
      board := bd₂,
      stock := { cards := Cycle.removeIdx (Cycle.removeIdx st.stock.cards i) k, cursor := k } } := by
    rw [hs₂, hs₁]; try rfl
  have hcomp₄ : st₄ = { st with
      board := bd₄,
      stock := { cards := Cycle.removeIdx (Cycle.removeIdx st.stock.cards (i + 1)) k',
                 cursor := k' } } := by
    rw [hs₄, hs₃]; try rfl
  have hcards : Cycle.removeIdx (Cycle.removeIdx st.stock.cards i) k
      = Cycle.removeIdx (Cycle.removeIdx st.stock.cards (i + 1)) k' := by
    rw [hk, hk']
    exact Cycle.removeIdx_comm st.stock.cards i i (Nat.le_refl i) hilt
  rw [hcomp₂, hcomp₄, hbd, hcards, hk, hk']
