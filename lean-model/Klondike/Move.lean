import Klondike.State

/-!
# Moves: the one semantic function

The model is the *full physical game* — `pilePile` included.  The
engine's restricted move set (no pile→pile; no_pile_to_pile.md) is the
predicate `Move.isEngine`, and the restriction's soundness — the
ledger's B-legs — is the theorem `solvable_engine_iff`: one model, a
move subset, an equivalence — not two formalizations and a
correspondence.

`apply : Move → State → Option State` is the single source of truth;
`legal`, and everything downstream, derives from it.
-/

/-- A move in the physical game. -/
inductive Move : Type where
  /-- Advance the stock cursor by `drawStep` (worry-back on wrap). -/
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

def applyDraw (st : State) : Option State :=
  some { st with stock := st.stock.rotate st.drawStep }

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

/-- The macro-style Draw-commitment: rotate until `c` is the waste top,
then place it at `b` (the engine's `DeckPile` before the sweep
optimization; `drawTo` handles the worry-back wrap). -/
def applyDrawTo (st : State) (c : Card) (b : Base) : Option State :=
  match st.stock.posOf c with
  | none => none
  | some i =>
    match st.board.attach b c with
    | none => none
    | some bd =>
      some { st with board := bd, stock := (st.stock.drawTo i).removeAt i }

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
