import Klondike.Move

/-!
# The theorem farm — formalized, proofs pending

The statement layer for the results beyond the kernel: the relabeling
group (T's generalization), the reversibility/commitment structure
(their Lemma A1), the commutation schema (C-IND / C13), and the
structural acyclicity of the matching.  Every proof is `sorry` with a
`TODO(proof)`; every definition is final code.
-/

/-! ## 1. The relabeling group — T, generalized

The tableau rules see only `(rank, color)`, so the symmetry group acts
on the *suit coordinate*: each color's two suits may be exchanged and
the two colors may be swapped — 8 elements.  Twin swap (T) is the
element flipping both colors' pairs simultaneously.
-/

/-- A suit-level relabeling preserving the color partition, with its
inverse as data. -/
structure Relabel where
  /-- The suit relabeling. -/
  suit : Suit → Suit
  /-- Its inverse. -/
  suitInv : Suit → Suit
  left_inv : ∀ s, suitInv (suit s) = s
  right_inv : ∀ s, suit (suitInv s) = s
  /-- Color coherence: different colors stay different, so `canSitOn`
  is preserved. -/
  coherent : ∀ s s', (suit s).color ≠ (suit s').color ↔ s.color ≠ s'.color

/-- The induced card relabeling (rank-preserving by construction). -/
def Relabel.card (r : Relabel) : Card → Card := fun c => ⟨r.suit c.suit, c.rank⟩

/-- The induced base relabeling. -/
def Relabel.onBase (r : Relabel) : Base → Base := Sum.map id r.card

/-- The twin swap as a relabeling. -/
def Relabel.twin : Relabel where
  suit := Suit.flipPair
  suitInv := Suit.flipPair
  left_inv := Suit.flipPair_flipPair
  right_inv := Suit.flipPair_flipPair
  coherent := by
    intro s s'
    simp

/-- Conjugate a whole state by a relabeling (T's action, generalized). -/
def State.relabelBy (r : Relabel) (st : State) : State :=
  { st with
    deal := { piles := fun a => (st.deal.piles a).map r.card,
              stock := st.deal.stock.map r.card },
    board := { topOf := fun b => (st.board.topOf (r.onBase b)).map r.card,
               inj := by sorry }, -- TODO(proof): conjugation preserves the matching law
    heights := fun s => st.heights (r.suitInv s),
    stock := { cards := st.stock.cards.map r.card, cursor := st.stock.cursor } }

/-- Relabel a move. -/
def Move.relabel (r : Relabel) : Move → Move
  | .draw => .draw
  | .reveal c => .reveal (r.card c)
  | .deckPile c b => .deckPile (r.card c) (r.onBase b)
  | .deckStack c => .deckStack (r.card c)
  | .pileStack c => .pileStack (r.card c)
  | .stackPile c b => .stackPile (r.card c) (r.onBase b)
  | .pilePile c b => .pilePile (r.card c) (r.onBase b)

/-- **T's conjugation step, generalized**: applying a relabeled move
to the relabeled state is applying the move to the state, relabeled.
TODO: seven move cases — the factored suits make each near-`rfl`. -/
theorem apply_relabel (r : Relabel) (m : Move) (st : State) :
    (st.relabelBy r).apply (m.relabel r) = (st.apply m).map (State.relabelBy r) := sorry

/-- **T, generalized**: solvability is invariant under every coherent
suit relabeling — all 8 elements of the group at once.  TODO:
induction on the play via `apply_relabel`. -/
theorem solvable_relabel (r : Relabel) (st : State) :
    (st.relabelBy r).solvableFrom ↔ st.solvableFrom := sorry

/-- `flipAll` is the twin-swap instance. -/
theorem flipAll_eq_relabelTwin (st : State) : st.flipAll = st.relabelBy Relabel.twin := rfl

/-! ## 2. Reversibility and commitments — their Lemma A1, model side

`pilePile` is an involution; `draw` is cyclically invertible;
`pileStack`∘`stackPile` is a *near*-inverse — the anchor case (a
fully-revealed non-king bottom card cannot return to the empty pile)
is exactly why safe-stacking (C1) is a theorem in the engine rather
than trivia, and where the reshape lemma (B4) earns its keep.
-/

/-- The return-base condition for un-stacking: a king may return to
an anchor; a card that sat on `d` may return onto `d`. -/
def canReturnBase (c : Card) (b₀ : Base) : Bool :=
  match b₀ with
  | Sum.inl _ => decide (c.rank = Rank.king)
  | Sum.inr d => canSitOn c d

/-- TODO(proof): board/heights round-trip; the stock is untouched. -/
theorem pileStack_stackPile_roundtrip {st : State} {c : Card} {b₀ : Base}
    {st₁ st₂ : State}
    (h₀ : st.board.bottomOf c = some b₀)
    (hret : canReturnBase c b₀ = true)
    (h₁ : st.apply (Move.pileStack c) = some st₁)
    (h₂ : st₁.apply (Move.stackPile c b₀) = some st₂) : st₂ = st := sorry

/-- TODO(proof): the moved run carries back; `aboveOf` is unchanged. -/
theorem pilePile_roundtrip {st : State} {c : Card} {b b₀ : Base} {st₁ st₂ : State}
    (h₀ : st.board.bottomOf c = some b₀)
    (h₁ : st.apply (Move.pilePile c b) = some st₁)
    (h₂ : st₁.apply (Move.pilePile c b₀) = some st₂) : st₂ = st := sorry

/-- A full rotation of the stock is the identity (draw everything,
worry back).  TODO: `(cursor + len) % len = cursor` from the cursor
bound. -/
theorem draw_full_cycle {st : State} (hl : st.stock.cursor ≤ st.stock.cards.length)
    {st' : State}
    (h : st.run (List.replicate st.stock.cards.length Move.draw) = some st') :
    st' = st := sorry

/-- A commitment: no play returns to the state after it. -/
def irreversibleAt (st : State) (m : Move) : Prop :=
  ∀ st₁ play, st.apply m = some st₁ → st₁.run play ≠ some st

/-- TODO(proof): depths only decrease — no move raises the hidden
boundary. -/
theorem irreversible_reveal {st : State} {c : Card} {st₁ : State}
    (h : st.apply (Move.reveal c) = some st₁) : irreversibleAt st (Move.reveal c) := sorry

/-- TODO(proof): no move returns a card to the cycle. -/
theorem irreversible_deckPile {st : State} {c : Card} {b : Base} {st₁ : State}
    (h : st.apply (Move.deckPile c b) = some st₁) : irreversibleAt st (Move.deckPile c b) := sorry

/-- TODO(proof): as `deckPile`; the foundation is not the cycle. -/
theorem irreversible_deckStack {st : State} {c : Card} {st₁ : State}
    (h : st.apply (Move.deckStack c) = some st₁) : irreversibleAt st (Move.deckStack c) := sorry

/-- The accommodation moves (their Lemma A): stack↔pile shuffling. -/
def Move.isAccommodation : Move → Bool
  | .pileStack _ => true
  | .stackPile _ _ => true
  | _ => false

/-- The commitment moves (their Lemma A1). -/
def Move.isCommit : Move → Bool
  | .reveal _ => true
  | .deckPile _ _ => true
  | .deckStack _ => true
  | _ => false

/-- The accommodation relation (their Lemma A's shuffle reachability). -/
def accommodates (st st' : State) : Prop :=
  ∃ play, st.run play = some st' ∧ ∀ m ∈ play, m.isAccommodation = true

/-- The accommodation reduction, easy direction — prepend the shuffle
play.  TODO. -/
theorem solvable_of_accommodates {st st' : State}
    (hacc : accommodates st' st) (hsol : st.solvableFrom) : st'.solvableFrom := sorry

/-- The accommodation reduction, hard direction — this is the reshape
argument (B4): a winning play survives the cards having been shuffled
through the foundations.  TODO. -/
theorem solvable_accommodates {st st' : State}
    (hacc : accommodates st st') (hsol : st.solvableFrom) : st'.solvableFrom := sorry

/-! ## 3. Commutation — C-IND and C13

Coarse layer: component-disjoint moves commute unconditionally (draw
and reveal are the clean instance — the engine's ~92% measured
draw·reveal landscape is an interleaving artifact, not game structure).
Fine layer: disjoint touch-sets — the "type-ball interaction lemma"
the ledger names as C13's premise.
-/

/-- The four state components. -/
inductive Component : Type where
  | tableau | foundations | hidden | stock
  deriving DecidableEq, Repr

/-- Which components a move reads/writes. -/
def Move.comps : Move → List Component
  | .draw => [.stock]
  | .reveal _ => [.tableau, .hidden]
  | .deckPile _ _ => [.stock, .tableau]
  | .deckStack _ => [.stock, .foundations]
  | .pileStack _ => [.tableau, .foundations]
  | .stackPile _ _ => [.tableau, .foundations]
  | .pilePile _ _ => [.tableau]

/-- TODO(proof): each move's legality reads only its components, so
neither order sees the other's writes. -/
theorem commute_of_compsDisjoint (st : State) (m m' : Move)
    (h : ∀ x ∈ Move.comps m, x ∉ Move.comps m') :
    (st.apply m >>= fun s => s.apply m') = (st.apply m' >>= fun s => s.apply m) := sorry

/-- The C-IND clean sector: draw·reveal always commutes.
Instance of `commute_of_compsDisjoint`.  TODO. -/
theorem reveal_draw_comm (st : State) (c : Card) :
    (st.apply (Move.reveal c) >>= fun s => s.apply Move.draw) =
    (st.apply Move.draw >>= fun s => s.apply (Move.reveal c)) := sorry

/-- The bases and cards a move reads or writes (state-dependent — the
run under a `pilePile`, the boundary under a `reveal`). -/
def Move.touch (st : State) : Move → List Base × List Card
  | .draw => ([], [])
  | .reveal c =>
      (match st.board.bottomOf c with
       | some (Sum.inr r) =>
           (match st.pileOfTopHidden r with
            | some a => [st.hiddenBase a]
            | none => [Sum.inr r], [c, r])
       | _ => ([], [c]))
  | .deckPile c b => ([b], [c])
  | .deckStack c => ([], [c])
  | .pileStack c => ((st.board.bottomOf c).toList, [c])
  | .stackPile c b => ([b], [c])
  | .pilePile c b => (b :: (st.board.bottomOf c).toList, c :: st.board.aboveOf c)

/-- Disjoint touch-sets (bases and cards). -/
def disjointTouch (t₁ t₂ : List Base × List Card) : Prop :=
  (∀ b ∈ t₁.1, b ∉ t₂.1) ∧ (∀ c ∈ t₁.2, c ∉ t₂.2)

/-- The fine-grained commutation schema — the type-ball interaction
lemma.  Moves with disjoint touch-sets commute (given both orders are
defined).  TODO. -/
theorem commute_of_disjoint_touch {st : State} {m m' : Move} {st₂ st₃ : State}
    (hdisj : disjointTouch (m.touch st) (m'.touch st))
    (h₁ : (st.apply m >>= fun s => s.apply m') = some st₂)
    (h₂ : (st.apply m' >>= fun s => s.apply m) = some st₃) : st₂ = st₃ := sorry

/-- **C13, generalized**: Draw-commitments at cycle-adjacent positions
commute (adjacency modulo the cycle length — the wrap counts).
TODO: `Cycle.removeIdx_comm` + cursor arithmetic. -/
theorem drawTo_comm_modAdjacent {st : State} {c c' : Card} {b b' : Base} {i j len : Nat}
    (hlen : st.stock.cards.length = len) (hadj : (i + 1) % len = j)
    (hic : st.stock.posOf c = some i) (hjc : st.stock.posOf c' = some j)
    (hbb : b ≠ b') {st₂ st₄ : State}
    (h₂ : (st.applyDrawTo c b >>= fun s => s.applyDrawTo c' b') = some st₂)
    (h₄ : (st.applyDrawTo c' b' >>= fun s => s.applyDrawTo c b) = some st₄) :
    st₂ = st₄ := sorry

/-- **C13's boundary**: non-adjacent Draw-commitments land on different
cursors — the end states differ (the cards agree, by `removeIdx_comm`;
only the cursor position diverges).  The engine's sweep/
canonicalization is what recovers commutation beyond adjacency — the
C-IND landscape's residual.  TODO. -/
theorem drawTo_nonadjacent_diverge {st : State} {c c' : Card} {b b' : Base} {i j : Nat}
    (hij : i < j) (hne : i + 1 ≠ j)
    (hic : st.stock.posOf c = some i) (hjc : st.stock.posOf c' = some j)
    (hbb : b ≠ b') {st₂ st₄ : State}
    (h₂ : (st.applyDrawTo c b >>= fun s => s.applyDrawTo c' b') = some st₂)
    (h₄ : (st.applyDrawTo c' b' >>= fun s => s.applyDrawTo c b) = some st₄) :
    st₂ ≠ st₄ := sorry

/-! ## 4. Structure — the matching is a forest

The rank grading along `topOf`-edges: everything above a card is
strictly lower rank.  This kills cycles in the matching (the reason
`Base`'s typing alone did not need to).
-/

/-- TODO(proof): induction along `aboveOf` using the WF edge legality
(the `canSitOn` disjunct). -/
theorem aboveOf_rank_grading {st : State} (hwf : st.WF) (c : Card) :
    ∀ d ∈ st.board.aboveOf c, d.rank.toIdx < c.rank.toIdx := sorry

/-- Acyclicity, from the grading.  TODO. -/
theorem aboveOf_irrefl {st : State} (hwf : st.WF) (c : Card) :
    c ∉ st.board.aboveOf c := sorry
