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

/-- The inverse card relabeling (conjugation's backward probe). -/
def Relabel.cardInv (r : Relabel) : Card → Card := fun c => ⟨r.suitInv c.suit, c.rank⟩

theorem Relabel.cardInv_card (r : Relabel) (c : Card) : r.cardInv (r.card c) = c := by
  show ⟨r.suitInv (r.suit c.suit), c.rank⟩ = c
  rw [r.left_inv c.suit]

theorem Relabel.cardInv_inj (r : Relabel) {b₁ b₂ : Base}
    (h : Sum.map id r.cardInv b₁ = Sum.map id r.cardInv b₂) : b₁ = b₂ := by
  cases b₁ with
  | inl a₁ =>
      cases b₂ with
      | inl a₂ => exact congrArg Sum.inl (by simpa using h)
      | inr x₂ => exact absurd h (by simp)
  | inr x₁ =>
      cases b₂ with
      | inl a₂ => exact absurd h (by simp)
      | inr x₂ =>
          have hinj : r.cardInv x₁ = r.cardInv x₂ := by simpa using h
          obtain ⟨hs, hr⟩ := Card.mk.inj hinj
          have hsi : x₁.suit = x₂.suit := by
            have e1 := r.right_inv x₁.suit
            rw [hs] at e1
            exact e1.symm.trans (r.right_inv x₂.suit)
          cases x₁ with
          | mk s₁ rk₁ =>
              cases x₂ with
              | mk s₂ rk₂ =>
                  have hsi' : s₁ = s₂ := hsi
                  have hr' : rk₁ = rk₂ := hr
                  rw [hsi', hr']

/-- Conjugation preserves the matching law (standalone lemma —
`by`-blocks do not parse inside structure instances). -/
theorem Relabel.relabelBy_inj (r : Relabel) (st : State) :
    ∀ (b₁ b₂ : Base) (c : Card),
      (fun b => (st.board.topOf (Sum.map id r.cardInv b)).map r.card) b₁ = some c →
      (fun b => (st.board.topOf (Sum.map id r.cardInv b)).map r.card) b₂ = some c →
      b₁ = b₂ := by
  intro b₁ b₂ c h₁ h₂
  obtain ⟨c₁, hc₁, hc₁'⟩ := Option.map_eq_some_iff.mp h₁
  obtain ⟨c₂, hc₂, hc₂'⟩ := Option.map_eq_some_iff.mp h₂
  have hcc : c₁ = c₂ := by
    have hcard : r.card c₁ = r.card c₂ := hc₁'.trans hc₂'.symm
    obtain ⟨hs, hr⟩ := Card.mk.inj hcard
    have hsi : c₁.suit = c₂.suit := by
      have e1 := r.left_inv c₁.suit
      rw [hs] at e1
      exact e1.symm.trans (r.left_inv c₂.suit)
    cases c₁ with
    | mk s₁ rk₁ =>
        cases c₂ with
        | mk s₂ rk₂ =>
            have hsi' : s₁ = s₂ := hsi
            have hr' : rk₁ = rk₂ := hr
            rw [hsi', hr']
  subst hcc
  exact r.cardInv_inj (st.board.inj _ _ _ hc₁ hc₂)

/-- Conjugate a whole state by a relabeling (T's action, generalized).
The board probes at the *inverse* relabeled base — the conjugation
direction: the relabeled move `pileStack (r.card c)` guards at
`inr (r.card c)`, which must read off `st`'s guard at `c`, and
`cardInv ∘ card = id` is what makes it so; probing at `r.card`
instead breaks conjugation for the group's non-involutive elements
(the suit 4-cycles). -/
def State.relabelBy (r : Relabel) (st : State) : State :=
  { st with
    deal := { piles := fun a => (st.deal.piles a).map r.card,
              stock := st.deal.stock.map r.card },
    board := { topOf := fun b => (st.board.topOf (Sum.map id r.cardInv b)).map r.card,
               inj := Relabel.relabelBy_inj r st },
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

section Probe
example (bd : Board) (b : Base) (acc : List Card) : Board.aboveOf.go bd 0 b acc = acc := rfl
example (bd : Board) (fuel : Nat) (b : Base) (acc : List Card) :
    Board.aboveOf.go bd (fuel+1) b acc
      = match bd.topOf b with
        | none => acc
        | some c' => if acc.contains c' then acc else Board.aboveOf.go bd fuel (Sum.inr c') (c' :: acc) := rfl
example (bd : Board) (c : Card) :
    bd.aboveOf c = Board.aboveOf.go bd 52 (Sum.inr c) [] := rfl
end Probe

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

/-- The round trip through the foundations is the identity: detach via
`pileStack`, come back with `stackPile` to the same base — the board
re-attaches (attach after detach at the same base restores the
matching pointwise), the heights return (+1 then -1). -/
theorem pileStack_stackPile_roundtrip {st : State} {c : Card} {b₀ : Base}
    {st₁ st₂ : State}
    (h₀ : st.board.bottomOf c = some b₀)
    (hret : canReturnBase c b₀ = true)
    (h₁ : st.apply (Move.pileStack c) = some st₁)
    (h₂ : st₁.apply (Move.stackPile c b₀) = some st₂) : st₂ = st := by
  have htop : st.board.topOf b₀ = some c := (Board.bottomOf_eq st.board c b₀).mp h₀
  simp only [State.apply, State.applyPileStack] at h₁
  cases ht : st.board.topOf (Sum.inr c) with
  | some x =>
    rw [ht] at h₁
    exact absurd h₁ (by simp)
  | none =>
    rw [ht, h₀] at h₁
    have h₁' : (if c.rank.toIdx = st.heights c.suit then
        some { st with
          board := st.board.detach b₀,
          heights := fun s => if s = c.suit then st.heights s + 1 else st.heights s }
        else none) = some st₁ := h₁
    split at h₁'
    · rw [Option.some.injEq] at h₁'
      subst h₁'
      simp only [State.apply, State.applyStackPile] at h₂
      cases hatt : (st.board.detach b₀).attach b₀ c with
      | none => rw [hatt] at h₂; exact absurd h₂ (by simp)
      | some bd =>
        rw [hatt] at h₂
        simp at h₂
        obtain ⟨-, h'⟩ := h₂
        subst h'
        have hbdeq : bd.topOf = st.board.topOf := by
          funext b'
          by_cases hbb : b' = b₀
          · subst hbb
            rw [Board.attach_topOf _ _ _ hatt]
            exact htop.symm
          · rw [Board.attach_topOf_ne _ _ _ hatt hbb, Board.detach_topOf_ne _ _ _ hbb]
        have hbd : bd = st.board := Board.ext_topOf hbdeq
        have hh : (fun s => if s = c.suit then
            (if s = c.suit then st.heights s + 1 else st.heights s) - 1
            else (if s = c.suit then st.heights s + 1 else st.heights s)) = st.heights := by
          funext s
          by_cases hsc : s = c.suit
          · subst hsc
            rw [if_pos rfl, if_pos rfl]
            omega
          · rw [if_neg hsc, if_neg hsc]
        cases st with
        | mk d b hgt dpt stck ds =>
          rw [hbd, hh]
    · exact absurd h₁' (by simp)

/-- TODO(proof): the moved run carries back; `aboveOf` is unchanged. -/
theorem pilePile_roundtrip {st : State} {c : Card} {b b₀ : Base} {st₁ st₂ : State}
    (h₀ : st.board.bottomOf c = some b₀)
    (h₁ : st.apply (Move.pilePile c b) = some st₁)
    (h₂ : st₁.apply (Move.pilePile c b₀) = some st₂) : st₂ = st := sorry

/-- A full pass plus the wrap deal returns to the pass start: from
cursor 0, dealing everything (the clamp passes the last card) and
wrapping lands home — the deal cycle's period is `⌈n/s⌉ + 1`, at any
step `s ≥ 1` (deck.rs `offset`'s periodicity).  Supersedes the old
rotate-form "a full rotation is the identity", an artifact of the
jump semantics.

TODO(proof) [M]: the deal chain — each deal from `k·s` below `n`
lands at `min ((k+1)·s, n)`; the clamp reaches `n` at `k = ⌈n/s⌉`,
and the next deal wraps to `0`. -/
theorem draw_full_pass {st : State} (hc : st.stock.cursor = 0)
    (hs : 0 < st.drawStep) {st' : State}
    (h : st.run (List.replicate
        ((st.stock.cards.length + st.drawStep - 1) / st.drawStep + 1) Move.draw)
      = some st') :
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

/-- The stock-*consuming* moves: the card draws (`deckPile`,
`deckStack`).  `.draw` — the pure deal that advances the cursor —
consumes nothing: the pace advance, not a card down. -/
def Move.consumesStock : Move → Bool
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

/-- The deal commutes with every non-consuming move: `.draw`'s
component signature is `[.stock]` *alone* and its legality is
unconditional (dealing reads nothing), while the non-consuming moves —
reveal, the two shuffles, pilePile — never touch the stock.  The
generalization of `reveal_draw_comm` from reveal to the whole
non-consuming sector.  The consuming draws (deckPile, deckStack) are
the genuine exceptions: their legality reads the cursor (`maskPos`),
which the deal changes.

This is the canonical form behind the window lemma's replay — deals
float freely through a non-consuming prefix, so the cursor at the
first consumption is a pure function of the deal count — and behind
`solvableEngine_iff_macro`'s regrouping (A3: draws commute with
accommodations).

TODO(proof) [E]: case bash over the five non-consuming moves from the
`apply` defs (the deal writes only `stock.cursor`; the others never
read it), or `commute_of_compsDisjoint` — `.draw`'s comps is
`[.stock]` by definition, disjoint from every non-consuming move's. -/
theorem deal_commutes_nonStock (st : State) (m : Move)
    (hc : m.consumesStock = false) :
    (st.apply m >>= fun s => s.apply Move.draw) =
    (st.apply Move.draw >>= fun s => s.apply m) := sorry

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

/-! ## 5. The deck integration — the jump IS the physical game

The Draw commitments (`applyDrawTo`, `applyDrawStackTo`) are the
derived jumps; these are the statements that the guard makes them
exactly the physical game: jump-then-play ≡ deal-until-then-play.
C9's premise, as theorems, at every draw step (at step 1 the guard is
trivial — `reachablePos_step1`).  The bridge to `toEngine_simulates`
consumes these. -/

/-- **The jump-soundness theorem**: the tableau-outcome Draw
commitment equals dealing until `c` is the waste top, then playing it
with the physical deck move — the reachable-position guard is exactly
the reachability of that deal sequence.

TODO(proof) [H]: → the guard gives the deal count (maskPos ↔
deal-iteration reachability — the prefix walk of `realizes_iff_stepsOK`;
`pos_shift`/`cursor_after` supply the positions), then
`apply_deckPile_iff`'s shape.  ← contrapositive by the same
correspondence: a reaching sequence puts the position in the mask. -/
theorem applyDrawTo_eq_dealPlay {st : State} (hwf : st.WF) {c : Card} {b : Base}
    {st'' : State} :
    st.applyDrawTo c b = some st'' ↔
      ∃ k st₁, st.run (List.replicate k Move.draw) = some st₁ ∧
        st₁.apply (Move.deckPile c b) = some st'' := sorry

/-- The stack-outcome twin: the safe-stack commitment equals dealing
to `c`, then the physical `deckStack`.  TODO(proof) [H]: as
`applyDrawTo_eq_dealPlay`, through `apply_deckStack_iff`. -/
theorem applyDrawStackTo_eq_dealPlay {st : State} (hwf : st.WF) {c : Card}
    {st'' : State} :
    st.applyDrawStackTo c = some st'' ↔
      ∃ k st₁, st.run (List.replicate k Move.draw) = some st₁ ∧
        st₁.apply (Move.deckStack c) = some st'' := sorry
