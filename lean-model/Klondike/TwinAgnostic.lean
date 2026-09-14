import Klondike.Relabel

/-!
# The twin mirror — all moves are twin-agnostic except the foundation moves

The alternative route to the twin exchange (T), by move-level
decomposition (2026-09-14):

**§1 The clean predicate (`Move.cleanTwin`).** The exception set of the
local twin swap `State.swapTwin t`: the moves whose legality consults
`heights` — `pileStack`, `deckStack`, `stackPile` — are clean exactly
when the moved card is off the pair.  NOTHING tableau-side is an
exception: `draw`, `reveal`, `deckPile`, `pilePile` are unconditionally
clean (`canSitOn` is color-blind by construction, the run walk reads
seats the swap relabels, the deal/depths views map along).  This is the
sharpened form of "all moves are twin-agnostic except for moving to
foundation": the foundation moves of NON-twin cards are agnostic too
(their guards read their own suit's height, which the swap fixes); the
only failures are the pair's own foundation lifecycle — stacking or
worrying back a twin crosses to the OTHER suit's count
(`witnesses/TwinSwapWitness.lean`'s refutation of the unconditional
conjugation).

**§2 The mirror lemma (`apply_swapTwin_clean`).**  For a clean move,
applying the relabeled move to the exchanged state is applying the move
to the state, exchanged:
`(st.swapTwin t).apply (m.swapTwin t) = (st.apply m).map (State.swapTwin t)`.
Unconditional in the state (no WF, no height alignment) — the guard
transfer is pointwise per move kind.  The none-direction rides the
involution (the mirror of the mirror is the source), so only the
some-direction needs the construction.  The play-level form
(`run_swapTwin_clean`) iterates it.

**§3 The licensed pair (`run_swapTwin_pair`).**  Where the winning
play's twin foundation moves occur as ONE adjacent pair
`[pileStack t, pileStack t.flipSuit]` — the aligned shape, both twins
stackable at the same moment (the §5.5 redundant pair supplies it in
the engine) — the exchange preserves solvability, both directions
(`solvable_swapTwin_paired` / `_back`).  The alignment is not a premise:
the pair firing pins both suits' heights to the shared rank (each guard
probes its own suit).  After the pair the heights re-sync — each suit
gained its twin's rank exactly once in both games — so the
correspondence is `State.swapTwin` again on the tail: no skew survives
the back-to-back shape.

**What remains open** — T's general window (the [H] row's scheduling
argument): when the twin stacks are NOT adjacent, the source play
interleaves its same-color catch-up between them, and the mirrored
game cannot copy it verbatim — the ±1 height skew on the twin suits
blocks the s1-cascade in the mirror and vice versa.  The bridge —
reorderings plus reveal-relocations of the stuck twin — is the
interleaving lemma (L1/O3) of macro_formalization §3; this file is the
mechanical half of that decomposition, isolated so the window argument
consumes it.
-/

/-! ## §1. The clean predicate

The exception set, per the design: the three foundation kinds with the
moved card ON the pair; everything else — including `deckStack` of an
off-pair card, and every tableau move of any card, twin included —
conjugates. -/

/-- `true` iff `c` is off the twin pair of `t`. -/
def Card.offPair (t c : Card) : Bool := decide (c ≠ t) && decide (c ≠ t.flipSuit)

@[simp] theorem Card.offPair_true {t c : Card} (h₁ : c ≠ t) (h₂ : c ≠ t.flipSuit) :
    Card.offPair t c = true := by
  simp [Card.offPair, h₁, h₂]

theorem Card.offPair_iff {t c : Card} :
    Card.offPair t c = true ↔ c ≠ t ∧ c ≠ t.flipSuit := by
  simp [Card.offPair, Bool.and_eq_true]

/-- A CLEAN move: one the local twin swap conjugates.  Everything
tableau-side is unconditionally clean; the three foundation moves read
`heights`, which `State.swapTwin` does not relabel, so they are clean
exactly when the moved card is off the pair. -/
def Move.cleanTwin (t : Card) : Move → Bool
  | .draw | .reveal _ | .deckPile _ _ | .pilePile _ _ => true
  | .deckStack c | .pileStack c | .stackPile c _ => Card.offPair t c

@[simp] theorem Move.cleanTwin_draw (t : Card) : Move.cleanTwin t Move.draw = true := rfl

@[simp] theorem Move.cleanTwin_reveal (t : Card) (c : Card) :
    Move.cleanTwin t (Move.reveal c) = true := rfl

@[simp] theorem Move.cleanTwin_deckPile (t : Card) (c : Card) (b : Base) :
    Move.cleanTwin t (Move.deckPile c b) = true := rfl

@[simp] theorem Move.cleanTwin_pilePile (t : Card) (c : Card) (b : Base) :
    Move.cleanTwin t (Move.pilePile c b) = true := rfl

@[simp] theorem Move.cleanTwin_deckStack (t : Card) (c : Card) :
    Move.cleanTwin t (Move.deckStack c) = Card.offPair t c := rfl

@[simp] theorem Move.cleanTwin_pileStack (t : Card) (c : Card) :
    Move.cleanTwin t (Move.pileStack c) = Card.offPair t c := rfl

@[simp] theorem Move.cleanTwin_stackPile (t : Card) (c : Card) (b : Base) :
    Move.cleanTwin t (Move.stackPile c b) = Card.offPair t c := rfl

theorem Move.cleanTwin_flipSuit (t : Card) (m : Move) :
    Move.cleanTwin t m = Move.cleanTwin t.flipSuit m := by
  cases m with
  | draw | reveal _ | deckPile _ _ | pilePile _ _ => rfl
  | deckStack c | pileStack c | stackPile c _ =>
      simp only [Move.cleanTwin, Card.offPair, Bool.and_comm, Card.flipSuit_flipSuit]

theorem Move.cleanTwin_swapTwin {t : Card} {m : Move} (h : Move.cleanTwin t m = true) :
    Move.cleanTwin t (m.swapTwin t) = true := by
  cases m with
  | draw | reveal _ | deckPile _ _ | pilePile _ _ => rfl
  | deckStack c | pileStack c | stackPile c _ =>
      obtain ⟨h₁, h₂⟩ := Card.offPair_iff.mp (by simpa using h)
      have hsc : Card.swapTwin t c = c := Card.swapTwin_of_ne h₁ h₂
      simp only [Move.cleanTwin, Move.swapTwin, hsc]
      exact h

/-- The move-level involution: relabeling twice is the identity. -/
theorem Move.swapTwin_swapTwin (t : Card) (m : Move) :
    (m.swapTwin t).swapTwin t = m := by
  cases m <;> simp [Move.swapTwin, Card.swapTwin_swapTwin, Base.swapTwin_swapTwin]

theorem Base.swapTwin_inj (t : Card) {b₁ b₂ : Base}
    (h : b₁.swapTwin t = b₂.swapTwin t) : b₁ = b₂ := by
  have h2 := congrArg (fun b => b.swapTwin t) h
  rw [Base.swapTwin_swapTwin, Base.swapTwin_swapTwin] at h2
  exact h2

/-! ## §2. The transfer kit

Every derived view of the exchanged state is the exchanged view — the
board conjugation (`mapByTwin`), the cycle laws, the deal/depths views,
and the composed guards (`isVis`, `canPlace`, `canMoveRun`).  Mirrors
Relabel.lean's `relabelBy` kit, specialized to the local swap (the
simpler height story: `heights` is fixed, not remapped). -/

/-- The probe law: the exchanged board at `b` reads the source at the
exchanged seat. -/
@[simp] theorem mapByTwin_topOf (bd : Board) (t : Card) (b : Base) :
    (bd.mapByTwin t).topOf b = (bd.topOf (b.swapTwin t)).map (Card.swapTwin t) := rfl

theorem mapByTwin_topOf_swap (bd : Board) (t : Card) (b : Base) :
    (bd.mapByTwin t).topOf (b.swapTwin t) = (bd.topOf b).map (Card.swapTwin t) := by
  show (bd.topOf ((b.swapTwin t).swapTwin t)).map (Card.swapTwin t) = _
  rw [Base.swapTwin_swapTwin]

theorem mapByTwin_topOf_inr (bd : Board) (t : Card) (c : Card) :
    (bd.mapByTwin t).topOf (Sum.inr (Card.swapTwin t c)) = (bd.topOf (Sum.inr c)).map (Card.swapTwin t) := by
  show (bd.topOf (Base.swapTwin t (Sum.inr (Card.swapTwin t c)))).map (Card.swapTwin t) = _
  have h : Base.swapTwin t (Sum.inr (Card.swapTwin t c)) = Sum.inr c := by
    show Sum.inr (Card.swapTwin t (Card.swapTwin t c)) = Sum.inr c
    rw [Card.swapTwin_swapTwin]
  rw [h]

theorem mapByTwin_topOf_inl (bd : Board) (t : Card) (a : Anchor) :
    (bd.mapByTwin t).topOf (Sum.inl a) = (bd.topOf (Sum.inl a)).map (Card.swapTwin t) :=
  mapByTwin_topOf bd t (Sum.inl a)

theorem mapByTwin_bottomOf (bd : Board) (t : Card) (c : Card) :
    (bd.mapByTwin t).bottomOf (Card.swapTwin t c) = (bd.bottomOf c).map (Base.swapTwin t) := by
  cases hb : bd.bottomOf c with
  | none =>
      refine (Board.bottomOf_eq_none _ _).mpr (fun b' hb' => ?_)
      rw [mapByTwin_topOf] at hb'
      obtain ⟨x, hx, hx'⟩ := Option.map_eq_some_iff.mp hb'
      have hxc : x = c := Card.swapTwin_inj t hx'
      rw [hxc] at hx
      exact (Board.bottomOf_eq_none bd c).mp hb _ hx
  | some b =>
      show (bd.mapByTwin t).bottomOf (Card.swapTwin t c) = some (b.swapTwin t)
      refine (Board.bottomOf_eq _ _ _).mpr ?_
      rw [mapByTwin_topOf_swap, (Board.bottomOf_eq bd c b).mp hb, Option.map_some]

/-- The twin-seat probes: reading `t`'s seat in the exchanged board is
reading `t.flipSuit`'s seat in the source (and vice versa) — the seat
lemmas the pair's guards need, provable (not definitional) because the
pair's card-swap is an if-then-else. -/
theorem mapByTwin_topOf_flip (bd : Board) (t : Card) :
    (bd.mapByTwin t).topOf (Sum.inr t) = (bd.topOf (Sum.inr t.flipSuit)).map (Card.swapTwin t) := by
  have h : Base.swapTwin t (Sum.inr t.flipSuit) = Sum.inr t := by
    show Sum.inr (Card.swapTwin t t.flipSuit) = Sum.inr t
    rw [Card.swapTwin_self_right]
  rw [← h, mapByTwin_topOf, Base.swapTwin_swapTwin]

theorem mapByTwin_topOf_flipSuit (bd : Board) (t : Card) :
    (bd.mapByTwin t).topOf (Sum.inr t.flipSuit) = (bd.topOf (Sum.inr t)).map (Card.swapTwin t) := by
  have h : Base.swapTwin t (Sum.inr t) = Sum.inr t.flipSuit := by
    show Sum.inr (Card.swapTwin t t) = Sum.inr t.flipSuit
    rw [Card.swapTwin_self_left]
  rw [← h, mapByTwin_topOf, Base.swapTwin_swapTwin]

theorem mapByTwin_bottomOf_flip (bd : Board) (t : Card) {b : Base}
    (hb : bd.bottomOf t.flipSuit = some b) :
    (bd.mapByTwin t).bottomOf t = some (b.swapTwin t) := by
  have htop : bd.topOf b = some t.flipSuit := (Board.bottomOf_eq bd t.flipSuit b).mp hb
  refine (Board.bottomOf_eq _ _ _).mpr ?_
  rw [mapByTwin_topOf_swap, htop, Option.map_some]
  exact congrArg some (Card.swapTwin_self_right t)

theorem mapByTwin_bottomOf_flipSuit (bd : Board) (t : Card) {b : Base}
    (hb : bd.bottomOf t = some b) :
    (bd.mapByTwin t).bottomOf t.flipSuit = some (b.swapTwin t) := by
  have htop : bd.topOf b = some t := (Board.bottomOf_eq bd t b).mp hb
  refine (Board.bottomOf_eq _ _ _).mpr ?_
  rw [mapByTwin_topOf_swap, htop, Option.map_some]
  exact congrArg some (Card.swapTwin_self_left t)

theorem mapByTwin_attach {bd : Board} {t : Card} {b : Base} {c : Card} {bd' : Board}
    (h : bd.attach b c = some bd') :
    (bd.mapByTwin t).attach (b.swapTwin t) (Card.swapTwin t c) = some (bd'.mapByTwin t) := by
  have hne : bd.attach b c ≠ none := by rw [h]; simp
  obtain ⟨htop, hbot⟩ := (Board.attach_eq_some_iff bd b c).mp hne
  have htopR : (bd.mapByTwin t).topOf (b.swapTwin t) = none := by
    rw [mapByTwin_topOf_swap, htop]; rfl
  have hbotR : (bd.mapByTwin t).bottomOf (Card.swapTwin t c) = none := by
    rw [mapByTwin_bottomOf, hbot]; rfl
  have hneR : (bd.mapByTwin t).attach (b.swapTwin t) (Card.swapTwin t c) ≠ none :=
    Board.attach_eq_some_iff _ _ _ |>.mpr ⟨htopR, hbotR⟩
  cases hR : (bd.mapByTwin t).attach (b.swapTwin t) (Card.swapTwin t c) with
  | none => rw [hR] at hneR; simp at hneR
  | some bdR =>
      rw [Option.some.injEq]
      refine Board.ext_topOf (funext (fun b'' => ?_))
      by_cases hbb : b'' = b.swapTwin t
      · rw [hbb, Board.attach_topOf _ _ _ hR, mapByTwin_topOf_swap, Board.attach_topOf _ _ _ h,
          Option.map_some]
      · rw [Board.attach_topOf_ne _ _ _ hR hbb, mapByTwin_topOf]
        have hcb : (b''.swapTwin t) ≠ b := fun hcon => hbb (by
          have hc2 := Base.swapTwin_swapTwin t b''
          rw [hcon] at hc2
          exact hc2.symm)
        rw [mapByTwin_topOf, Board.attach_topOf_ne _ _ _ h hcb]

theorem mapByTwin_detach (bd : Board) (t : Card) (b : Base) :
    (bd.mapByTwin t).detach (b.swapTwin t) = (bd.detach b).mapByTwin t := by
  refine Board.ext_topOf (funext (fun b'' => ?_))
  by_cases hbb : b'' = b.swapTwin t
  · rw [hbb]
    show (if b.swapTwin t = b.swapTwin t then none else (bd.mapByTwin t).topOf (b.swapTwin t)) =
      ((bd.detach b).mapByTwin t).topOf (b.swapTwin t)
    rw [if_pos rfl, mapByTwin_topOf_swap, Board.detach_topOf]
    rfl
  · show (if b'' = b.swapTwin t then none else (bd.mapByTwin t).topOf b'') =
      ((bd.detach b).mapByTwin t).topOf b''
    have hcb : (b''.swapTwin t) ≠ b := fun hcon => hbb (by
      have hc2 := Base.swapTwin_swapTwin t b''
      rw [hcon] at hc2
      exact hc2.symm)
    rw [if_neg hbb, mapByTwin_topOf, mapByTwin_topOf, Board.detach_topOf_ne _ _ _ hcb]

theorem beq_swapTwin (t : Card) (x y : Card) :
    ((Card.swapTwin t x == Card.swapTwin t y) : Bool) = (x == y) := by
  by_cases hxy : x = y
  · rw [hxy]
    rw [show ((Card.swapTwin t y == Card.swapTwin t y)) = true from decide_eq_true rfl,
        show ((y == y)) = true from decide_eq_true rfl]
  · have h1 : (Card.swapTwin t x == Card.swapTwin t y) = false := by
      cases hb : (Card.swapTwin t x == Card.swapTwin t y) with
      | true => exact absurd (Card.swapTwin_inj t (of_decide_eq_true hb)) hxy
      | false => rfl
    have h2 : (x == y) = false := by
      cases hb : (x == y) with
      | true => exact absurd (of_decide_eq_true hb) hxy
      | false => rfl
    rw [h1, h2]

theorem contains_swapTwin (t : Card) : ∀ (l : List Card) (x : Card),
    (l.map (Card.swapTwin t)).contains (Card.swapTwin t x) = l.contains x := by
  intro l
  induction l with
  | nil => intro x; rfl
  | cons a tl ih =>
      intro x
      show ((Card.swapTwin t x == Card.swapTwin t a) || (tl.map (Card.swapTwin t)).contains (Card.swapTwin t x))
        = (x == a || tl.contains x)
      rw [ih x, beq_swapTwin t x a]

theorem mapByTwin_aboveOf_go (bd : Board) (t : Card) : ∀ (fuel : Nat) (b : Base) (acc : List Card),
    Board.aboveOf.go (bd.mapByTwin t) fuel (b.swapTwin t) (acc.map (Card.swapTwin t))
      = (Board.aboveOf.go bd fuel b acc).map (Card.swapTwin t) := by
  intro fuel
  induction fuel with
  | zero => intro b acc; rfl
  | succ n ih =>
      intro b acc
      rw [aboveOf_go_succ, aboveOf_go_succ, mapByTwin_topOf_swap]
      cases hb : bd.topOf b with
      | none => rfl
      | some x =>
          show (if (acc.map (Card.swapTwin t)).contains (Card.swapTwin t x) then acc.map (Card.swapTwin t)
                else Board.aboveOf.go (bd.mapByTwin t) n (Sum.inr (Card.swapTwin t x))
                  (Card.swapTwin t x :: acc.map (Card.swapTwin t)))
            = (if acc.contains x then acc
               else Board.aboveOf.go bd n (Sum.inr x) (x :: acc)).map (Card.swapTwin t)
          rw [contains_swapTwin t acc x]
          by_cases hac : acc.contains x = true
          · rw [if_pos hac, if_pos hac]
          · rw [if_neg hac, if_neg hac]
            exact ih (Sum.inr x) (x :: acc)

theorem mapByTwin_aboveOf (bd : Board) (t : Card) (c : Card) :
    (bd.mapByTwin t).aboveOf (Card.swapTwin t c) = (bd.aboveOf c).map (Card.swapTwin t) :=
  mapByTwin_aboveOf_go bd t 52 (Sum.inr c) []

@[simp] theorem swapTwin_board (st : State) (t : Card) :
    (st.swapTwin t).board = st.board.mapByTwin t := rfl

@[simp] theorem swapTwin_heights (st : State) (t : Card) :
    (st.swapTwin t).heights = st.heights := rfl

@[simp] theorem swapTwin_depths (st : State) (t : Card) :
    (st.swapTwin t).depths = st.depths := rfl

@[simp] theorem swapTwin_drawStep (st : State) (t : Card) :
    (st.swapTwin t).drawStep = st.drawStep := rfl

/-- The mapped stock cycle (the `swapTwin` stock field, named for the
cycle laws). -/
def twinCycle (t : Card) (cy : Cycle Card) : Cycle Card where
  cards := cy.cards.map (Card.swapTwin t)
  cursor := cy.cursor

@[simp] theorem swapTwin_stock (st : State) (t : Card) :
    (st.swapTwin t).stock = twinCycle t st.stock := rfl

theorem twinCycle_prev (t : Card) (cy : Cycle Card) :
    (twinCycle t cy).prev = cy.prev.map (Card.swapTwin t) := by
  show (if cy.cursor = 0 then none else (cy.cards.map (Card.swapTwin t))[cy.cursor - 1]?)
     = (if cy.cursor = 0 then none else cy.cards[cy.cursor - 1]?).map (Card.swapTwin t)
  by_cases h0 : cy.cursor = 0
  · rw [if_pos h0, if_pos h0]
    rfl
  · rw [if_neg h0, if_neg h0, List.getElem?_map]

theorem twinCycle_dealOnce (t : Card) (cy : Cycle Card) (s : Nat) :
    (twinCycle t cy).dealOnce s = twinCycle t (cy.dealOnce s) := by
  show (if cy.cursor ≥ (cy.cards.map (Card.swapTwin t)).length
        then { cards := cy.cards.map (Card.swapTwin t), cursor := 0 }
        else { cards := cy.cards.map (Card.swapTwin t),
               cursor := min (cy.cursor + s) (cy.cards.map (Card.swapTwin t)).length } : Cycle Card)
    = { cards := (cy.dealOnce s).cards.map (Card.swapTwin t), cursor := (cy.dealOnce s).cursor }
  simp only [List.length_map]
  split
  · rename_i h
    simp only [Cycle.dealOnce]
    rw [if_pos h]
  · rename_i h
    simp only [Cycle.dealOnce]
    rw [if_neg h]

theorem twinCycle_removeAt (t : Card) (cy : Cycle Card) (i : Nat) :
    (twinCycle t cy).removeAt i = twinCycle t (cy.removeAt i) := by
  show ({ cards := Cycle.removeIdx (cy.cards.map (Card.swapTwin t)) i,
           cursor := if i < cy.cursor then cy.cursor - 1 else cy.cursor } : Cycle Card)
    = { cards := (Cycle.removeIdx cy.cards i).map (Card.swapTwin t),
        cursor := if i < cy.cursor then cy.cursor - 1 else cy.cursor }
  rw [Cycle.removeIdx_map]

theorem swapTwin_hidden (st : State) (t : Card) (a : Anchor) :
    (st.swapTwin t).hidden a = (st.hidden a).map (Card.swapTwin t) := by
  show ((st.deal.piles a).map (Card.swapTwin t)).take (st.depths a)
    = ((st.deal.piles a).take (st.depths a)).map (Card.swapTwin t)
  rw [← List.map_take]

theorem swapTwin_topHidden (st : State) (t : Card) (a : Anchor) :
    (st.swapTwin t).topHidden a = (st.topHidden a).map (Card.swapTwin t) := by
  show ((st.swapTwin t).hidden a).getLast? = (st.topHidden a).map (Card.swapTwin t)
  rw [swapTwin_hidden, List.getLast?_map]
  rfl

theorem swapTwin_pileOfTopHidden (st : State) (t : Card) (r : Card) :
    (st.swapTwin t).pileOfTopHidden (Card.swapTwin t r) = st.pileOfTopHidden r := by
  show findFirst (fun a => decide ((st.swapTwin t).topHidden a = some (Card.swapTwin t r))) Anchor.all
     = findFirst (fun a => decide (st.topHidden a = some r)) Anchor.all
  exact findFirst_congr (fun a => by
    show decide ((st.swapTwin t).topHidden a = some (Card.swapTwin t r))
      = decide (st.topHidden a = some r)
    rw [swapTwin_topHidden]
    cases hst : st.topHidden a with
    | none => rfl
    | some x =>
        refine decide_congr ?_
        constructor
        · intro h
          have h1 : Card.swapTwin t x = Card.swapTwin t r := Option.some.inj h
          have h2 : x = r := Card.swapTwin_inj t h1
          rw [h2]
        · intro h
          have h1 : x = r := Option.some.inj h
          rw [h1]
          rfl) Anchor.all

theorem swapTwin_hiddenBase (st : State) (t : Card) (a : Anchor) :
    (st.swapTwin t).hiddenBase a = (st.hiddenBase a).swapTwin t := by
  show (match (((st.swapTwin t).hidden a).reverse.drop 1).head? with
        | some d => Sum.inr d
        | none => Sum.inl a)
      = Base.swapTwin t (match ((st.hidden a).reverse.drop 1).head? with
        | some d => Sum.inr d
        | none => Sum.inl a)
  rw [swapTwin_hidden, ← List.map_reverse, ← List.map_drop, List.head?_map]
  cases ((st.hidden a).reverse.drop 1).head? with
  | none => rfl
  | some d => rfl

theorem swapTwin_isVis (st : State) (t : Card) (d : Card) :
    (st.swapTwin t).isVis (Card.swapTwin t d) = st.isVis d := by
  simp only [State.isVis, swapTwin_board, mapByTwin_bottomOf]
  cases st.board.bottomOf d with
  | none => rfl
  | some b => rfl

theorem swapTwin_canPlace_inl (st : State) (t : Card) (c : Card) (a : Anchor) :
    (st.swapTwin t).canPlace (Card.swapTwin t c) (Sum.inl a) = st.canPlace c (Sum.inl a) := by
  show (decide ((st.board.mapByTwin t).topOf (Sum.inl a) = none)
        && decide ((Card.swapTwin t c).rank = Rank.king))
    = (decide (st.board.topOf (Sum.inl a) = none) && decide (c.rank = Rank.king))
  rw [mapByTwin_topOf_inl, Card.swapTwin_rank]
  cases st.board.topOf (Sum.inl a) with
  | none => rfl
  | some x => rfl

theorem swapTwin_canPlace_inr (st : State) (t : Card) (c d : Card) :
    (st.swapTwin t).canPlace (Card.swapTwin t c) (Sum.inr (Card.swapTwin t d))
      = st.canPlace c (Sum.inr d) := by
  show (decide ((st.board.mapByTwin t).topOf (Sum.inr (Card.swapTwin t d)) = none)
        && ((st.swapTwin t).isVis (Card.swapTwin t d)
          && canSitOn (Card.swapTwin t c) (Card.swapTwin t d)))
    = (decide (st.board.topOf (Sum.inr d) = none) && (st.isVis d && canSitOn c d))
  rw [mapByTwin_topOf_inr, swapTwin_isVis, canSitOn_swapTwin_right, canSitOn_swapTwin_left]
  cases st.board.topOf (Sum.inr d) with
  | none => rfl
  | some x => rfl

theorem swapTwin_canPlace (st : State) (t : Card) (c : Card) (b : Base) :
    (st.swapTwin t).canPlace (Card.swapTwin t c) (b.swapTwin t) = st.canPlace c b := by
  cases b with
  | inl a => exact swapTwin_canPlace_inl st t c a
  | inr d => exact swapTwin_canPlace_inr st t c d

/-- The off-pair form: after the clean rewrite of the moved card to
itself, the base still transfers. -/
theorem swapTwin_canPlace_off (st : State) (t c : Card) (b : Base)
    (hc : Card.offPair t c = true) :
    (st.swapTwin t).canPlace c (b.swapTwin t) = st.canPlace c b := by
  obtain ⟨hc₁, hc₂⟩ := Card.offPair_iff.mp hc
  have hsc : Card.swapTwin t c = c := Card.swapTwin_of_ne hc₁ hc₂
  calc (st.swapTwin t).canPlace c (b.swapTwin t)
      = (st.swapTwin t).canPlace (Card.swapTwin t c) (b.swapTwin t) := by rw [hsc]
    _ = st.canPlace c b := swapTwin_canPlace st t c b

theorem swapTwin_canMoveRun (st : State) (t : Card) (c : Card) (b : Base) :
    (st.swapTwin t).canMoveRun (Card.swapTwin t c) (b.swapTwin t) = st.canMoveRun c b := by
  cases b with
  | inl a =>
      show ((st.swapTwin t).canPlace (Card.swapTwin t c) (Sum.inl a) && true)
        = (st.canPlace c (Sum.inl a) && true)
      rw [swapTwin_canPlace_inl]
  | inr d =>
      show ((st.swapTwin t).canPlace (Card.swapTwin t c) (Sum.inr (Card.swapTwin t d))
            && !((st.board.mapByTwin t).aboveOf (Card.swapTwin t c)).contains (Card.swapTwin t d))
        = (st.canPlace c (Sum.inr d) && !(st.board.aboveOf c).contains d)
      rw [swapTwin_canPlace_inr, mapByTwin_aboveOf, contains_swapTwin t]

theorem swapTwin_with (t : Card) (st : State) (bd : Board) (hs : Suit → Nat)
    (dpt : Anchor → Nat) (cy : Cycle Card) :
    ({ st with board := bd, heights := hs, depths := dpt, stock := cy }).swapTwin t =
      { st.swapTwin t with
        board := bd.mapByTwin t,
        heights := hs,
        depths := dpt,
        stock := twinCycle t cy } := by
  apply state_ext <;> try rfl

/-! ## §3. The mirror lemma -/

/-- **The mirror lemma, some-direction**: a clean move's successor in the
exchanged game is the exchanged successor. -/
theorem apply_swapTwin_clean_some {st st' : State} {m : Move} {t : Card}
    (hclean : Move.cleanTwin t m = true) (hst : st.apply m = some st') :
    (st.swapTwin t).apply (m.swapTwin t) = some (st'.swapTwin t) := by
  cases m with
  | draw =>
      rw [apply_draw_iff] at hst
      obtain rfl := hst
      show some { st.swapTwin t with
        stock := (st.swapTwin t).stock.dealOnce (st.swapTwin t).drawStep }
        = some ({ st with stock := st.stock.dealOnce st.drawStep }.swapTwin t)
      apply congrArg some
      apply state_ext <;> try rfl
      exact twinCycle_dealOnce t st.stock st.drawStep
  | reveal c =>
      rw [apply_reveal_iff] at hst
      obtain ⟨htop, r, a, bd, hbot, hpile, hatt, hst'⟩ := hst
      show (st.swapTwin t).apply (Move.reveal (Card.swapTwin t c)) = some (st'.swapTwin t)
      rw [apply_reveal_iff]
      refine ⟨?_, Card.swapTwin t r, a, bd.mapByTwin t, ?_, ?_, ?_, ?_⟩
      · rw [swapTwin_board, mapByTwin_topOf_inr, htop]
        rfl
      · rw [swapTwin_board, mapByTwin_bottomOf, hbot, Option.map_some]
        rfl
      · rw [swapTwin_pileOfTopHidden, hpile]
      · rw [swapTwin_board, swapTwin_hiddenBase]
        exact mapByTwin_attach hatt
      · rw [hst']
        apply state_ext <;> try rfl
  | deckPile c b =>
      rw [apply_deckPile_iff] at hst
      obtain ⟨hp, hcp, bd, hatt, hst'⟩ := hst
      show (st.swapTwin t).apply (Move.deckPile (Card.swapTwin t c) (b.swapTwin t))
        = some (st'.swapTwin t)
      rw [apply_deckPile_iff]
      refine ⟨?_, ?_, bd.mapByTwin t, ?_, ?_⟩
      · rw [swapTwin_stock, twinCycle_prev, hp, Option.map_some]
      · rw [swapTwin_canPlace, hcp]
      · exact mapByTwin_attach hatt
      · rw [hst']
        apply state_ext <;> try rfl
        exact (twinCycle_removeAt t st.stock (st.stock.cursor - 1)).symm
  | deckStack c =>
      obtain ⟨hc₁, hc₂⟩ := Card.offPair_iff.mp (by simpa using hclean)
      have hsc : Card.swapTwin t c = c := Card.swapTwin_of_ne hc₁ hc₂
      rw [apply_deckStack_iff] at hst
      obtain ⟨hp, hrk, hst'⟩ := hst
      show (st.swapTwin t).apply (Move.deckStack (Card.swapTwin t c)) = some (st'.swapTwin t)
      rw [apply_deckStack_iff]
      refine ⟨?_, ?_, ?_⟩
      · rw [swapTwin_stock, twinCycle_prev, hp, Option.map_some]
      · rw [Card.swapTwin_rank, hsc]
        exact hrk
      · rw [hst', hsc]
        apply state_ext <;> try rfl
        exact (twinCycle_removeAt t st.stock (st.stock.cursor - 1)).symm
  | pileStack c =>
      obtain ⟨hc₁, hc₂⟩ := Card.offPair_iff.mp (by simpa using hclean)
      have hsc : Card.swapTwin t c = c := Card.swapTwin_of_ne hc₁ hc₂
      rw [apply_pileStack_iff] at hst
      obtain ⟨htop, b, hb, hrk, hst'⟩ := hst
      show (st.swapTwin t).apply (Move.pileStack (Card.swapTwin t c)) = some (st'.swapTwin t)
      rw [apply_pileStack_iff]
      refine ⟨?_, b.swapTwin t, ?_, ?_, ?_⟩
      · rw [swapTwin_board, mapByTwin_topOf_inr, htop]
        rfl
      · rw [swapTwin_board, mapByTwin_bottomOf, hb, Option.map_some]
      · rw [Card.swapTwin_rank, hsc]
        exact hrk
      · rw [hst', hsc]
        apply state_ext <;> try rfl
        exact (mapByTwin_detach st.board t b).symm
  | stackPile c b =>
      obtain ⟨hc₁, hc₂⟩ := Card.offPair_iff.mp (by simpa using hclean)
      have hsc : Card.swapTwin t c = c := Card.swapTwin_of_ne hc₁ hc₂
      rw [apply_stackPile_iff] at hst
      obtain ⟨hrk, hcp, bd, hatt, hst'⟩ := hst
      show (st.swapTwin t).apply (Move.stackPile (Card.swapTwin t c) (b.swapTwin t))
        = some (st'.swapTwin t)
      rw [apply_stackPile_iff]
      refine ⟨?_, ?_, bd.mapByTwin t, ?_, ?_⟩
      · rw [Card.swapTwin_rank, hsc]
        exact hrk
      · rw [swapTwin_canPlace, hcp]
      · exact mapByTwin_attach hatt
      · rw [hst', hsc]
        apply state_ext <;> try rfl
  | pilePile c b =>
      rw [apply_pilePile_iff] at hst
      obtain ⟨b₀, hb, hne, hcmr, bd, hatt, hst'⟩ := hst
      show (st.swapTwin t).apply (Move.pilePile (Card.swapTwin t c) (b.swapTwin t))
        = some (st'.swapTwin t)
      rw [apply_pilePile_iff]
      refine ⟨b₀.swapTwin t, ?_, ?_, ?_, bd.mapByTwin t, ?_, ?_⟩
      · rw [swapTwin_board, mapByTwin_bottomOf, hb, Option.map_some]
      · exact fun h => hne (Base.swapTwin_inj t h)
      · rw [swapTwin_canMoveRun, hcmr]
      · rw [swapTwin_board, mapByTwin_detach]
        exact mapByTwin_attach hatt
      · rw [hst']
        apply state_ext <;> try rfl

/-- **The mirror lemma**: for a clean move, applying the relabeled move
to the exchanged state is applying the move to the state, exchanged.
The none-direction rides the involution: if the mirror of a clean move
fired, then (the mirror of) THAT firing mirrors back to the source
firing — `Move.cleanTwin_swapTwin` supplies the cleanliness. -/
theorem apply_swapTwin_clean {st : State} {m : Move} {t : Card}
    (hclean : Move.cleanTwin t m = true) :
    (st.swapTwin t).apply (m.swapTwin t) = (st.apply m).map (State.swapTwin t) := by
  cases hst : st.apply m with
  | none =>
      cases hR : (st.swapTwin t).apply (m.swapTwin t) with
      | none => rfl
      | some st'' =>
          exfalso
          have h2 := apply_swapTwin_clean_some (st := st.swapTwin t) (m := m.swapTwin t)
            (st' := st'') (Move.cleanTwin_swapTwin hclean) hR
          rw [State.swapTwin_swapTwin, Move.swapTwin_swapTwin] at h2
          rw [hst] at h2
          exact absurd h2 (by simp)
  | some st₁ =>
      rw [apply_swapTwin_clean_some hclean hst]
      rfl

/-- The play-level mirror: a clean play runs, exchanged, to the
exchanged outcome. -/
theorem run_swapTwin_clean (t : Card) : ∀ (st : State) (play : List Move),
    (∀ m ∈ play, Move.cleanTwin t m = true) →
    (st.swapTwin t).run (play.map (Move.swapTwin t)) = (st.run play).map (State.swapTwin t) := by
  intro st play
  revert st
  induction play with
  | nil => intro st _; rfl
  | cons m ms ih =>
      intro st hclean
      simp only [List.map_cons, State.run]
      rw [apply_swapTwin_clean (hclean m List.mem_cons_self)]
      cases hst : st.apply m with
      | none => rfl
      | some st' =>
          exact ih st' (fun m' hm' => hclean m' (List.mem_cons_of_mem _ hm'))

/-! ## §4. The licensed pair — the aligned twin stacks -/

/-- The first mirror step's intermediate: the exchanged state with the
twin's base detached and the twin's suit bumped (the exchanged
successor of `pileStack t.flipSuit`). -/
def State.twinSkew (st : State) (t : Card) (b : Base) : State :=
  { st.swapTwin t with
    board := (st.swapTwin t).board.detach (b.swapTwin t),
    heights := fun s => if s = t.flipSuit.suit then (st.swapTwin t).heights s + 1
      else (st.swapTwin t).heights s }

theorem twinSkew_board (st : State) (t : Card) (b : Base) :
    (st.twinSkew t b).board = (st.board.detach b).mapByTwin t := by
  show (st.board.mapByTwin t).detach (b.swapTwin t) = (st.board.detach b).mapByTwin t
  exact mapByTwin_detach st.board t b

@[simp] theorem twinSkew_heights_self (st : State) (t : Card) (b : Base) :
    (st.twinSkew t b).heights t.flipSuit.suit = st.heights t.flipSuit.suit + 1 := by
  show (if t.flipSuit.suit = t.flipSuit.suit then (st.swapTwin t).heights t.flipSuit.suit + 1
      else (st.swapTwin t).heights t.flipSuit.suit) = _
  rw [if_pos rfl, swapTwin_heights]

@[simp] theorem twinSkew_heights_ne {st : State} {t : Card} {b : Base} {s : Suit}
    (h : s ≠ t.flipSuit.suit) :
    (st.twinSkew t b).heights s = st.heights s := by
  show (if s = t.flipSuit.suit then (st.swapTwin t).heights s + 1
      else (st.swapTwin t).heights s) = st.heights s
  rw [if_neg h, swapTwin_heights]

/-- **The back-to-back twin stacks mirror.**  If the source play stacks
`t` and then IMMEDIATELY `t.flipSuit` (the aligned double stack — both
guards pin their suit's height to the shared rank, so the heights are
aligned at no extra premise), the exchanged game plays the reversed
pair `[pileStack t.flipSuit, pileStack t]` and lands on the exchanged
successor.  After the pair the two games' heights re-sync (each suit
gained its twin's rank once in both), so the correspondence is
`State.swapTwin` again — no skew survives the back-to-back shape. -/
theorem run_swapTwin_pair {st A A₁ : State} {t : Card}
    (h₀ : st.apply (Move.pileStack t) = some A)
    (h₁ : A.apply (Move.pileStack t.flipSuit) = some A₁) :
    (st.swapTwin t).run [Move.pileStack t.flipSuit, Move.pileStack t] = some (A₁.swapTwin t) := by
  rw [apply_pileStack_iff] at h₀
  obtain ⟨htop, β, hβ, hrk, hA⟩ := h₀
  rw [apply_pileStack_iff] at h₁
  obtain ⟨htop', β', hβ', hrk', hA₁⟩ := h₁
  have hsne : t.flipSuit.suit ≠ t.suit := by
    intro h
    exact Suit.flipPair_ne t.suit h
  have hA' : A = { st with
      board := st.board.detach β,
      heights := fun s => if s = t.suit then st.heights s + 1 else st.heights s } := hA
  have hAboard : A.board = st.board.detach β := by rw [hA']
  have hAoff : A.heights t.flipSuit.suit = st.heights t.flipSuit.suit := by
    rw [hA']
    show (if t.flipSuit.suit = t.suit then st.heights t.flipSuit.suit + 1
        else st.heights t.flipSuit.suit) = st.heights t.flipSuit.suit
    rw [if_neg hsne]
  -- the derived alignment: h₀ pins s1, h₁ pins s2 (A's heights are st's off the bumped suit)
  have hs₂ : st.heights t.flipSuit.suit = t.rank.toIdx := by
    have h2 : t.flipSuit.rank.toIdx = A.heights t.flipSuit.suit := hrk'
    rw [Card.flipSuit_rank, hAoff] at h2
    exact h2.symm
  -- the mirror's first move: pileStack t.flipSuit, landing on the skew state
  have hM₁ : (st.swapTwin t).apply (Move.pileStack t.flipSuit) = some (st.twinSkew t β) := by
    rw [apply_pileStack_iff]
    refine ⟨?_, β.swapTwin t, ?_, ?_, rfl⟩
    · rw [swapTwin_board, mapByTwin_topOf_flipSuit, htop]
      rfl
    · rw [swapTwin_board, mapByTwin_bottomOf_flipSuit st.board t hβ]
    · rw [Card.flipSuit_rank, swapTwin_heights]
      exact hs₂.symm
  -- the mirror's second move: pileStack t at the skew state
  have hM₂ : (st.twinSkew t β).apply (Move.pileStack t) = some (A₁.swapTwin t) := by
    rw [apply_pileStack_iff]
    refine ⟨?_, β'.swapTwin t, ?_, ?_, ?_⟩
    · -- t's seat in the mirror reads t''s seat in A (both bare)
      rw [twinSkew_board, mapByTwin_topOf_flip, ← hAboard, htop']
      rfl
    · -- t's base in the mirror is β' exchanged
      rw [twinSkew_board]
      exact mapByTwin_bottomOf_flip (st.board.detach β) t (by rw [← hAboard]; exact hβ')
    · -- the rung: the skew state's t-suit height is st's (unbumped)
      rw [twinSkew_heights_ne (fun h => hsne h.symm)]
      exact hrk
    · -- the successor: exchanged
      obtain rfl := hA₁
      obtain rfl := hA'
      apply state_ext <;> try rfl
      · -- board: detach at the exchanged base, conjugated
        show ((st.board.detach β).detach β').mapByTwin t
          = ((st.board.mapByTwin t).detach (β.swapTwin t)).detach (β'.swapTwin t)
        rw [mapByTwin_detach, mapByTwin_detach]
      · -- heights: the two bumps commute
        funext s
        show (if s = t.flipSuit.suit then (if s = t.suit then st.heights s + 1 else st.heights s) + 1
            else if s = t.suit then st.heights s + 1 else st.heights s)
          = (if s = t.suit then (st.twinSkew t β).heights s + 1 else (st.twinSkew t β).heights s)
        by_cases h1 : s = t.suit
        · have h2 : s ≠ t.flipSuit.suit := fun h => hsne (h.symm.trans h1)
          have hsk : (st.twinSkew t β).heights s = st.heights s := twinSkew_heights_ne h2
          rw [if_neg h2, if_pos h1, if_pos h1, hsk]
        · by_cases h2 : s = t.flipSuit.suit
          · have hsk : (st.twinSkew t β).heights s = st.heights s + 1 := by
              rw [h2]; exact twinSkew_heights_self st t β
            rw [if_pos h2, if_neg h1, if_neg h1, hsk]
          · have hsk : (st.twinSkew t β).heights s = st.heights s := twinSkew_heights_ne h2
            rw [if_neg h2, if_neg h1, if_neg h1, hsk]
  -- assembly
  simp only [State.run]
  rw [hM₁]
  show (match State.apply (Move.pileStack t) (st.twinSkew t β) with
        | some st' => some st'
        | none => none) = some (A₁.swapTwin t)
  rw [hM₂]

/-- A run splits at the concatenation (the local bind form; Progress's
`run_append` sits above the Theorems chain — the name stays clear of
Progress's own `run_split`). -/
theorem run_split_bind (st : State) : ∀ (l₁ l₂ : List Move),
    st.run (l₁ ++ l₂) = (st.run l₁).bind (fun s => s.run l₂) := by
  intro l₁
  induction l₁ generalizing st with
  | nil => intro l₂; rfl
  | cons m ms ih =>
      intro l₂
      simp only [List.cons_append, State.run]
      cases h : st.apply m with
      | none => rfl
      | some st' => exact ih st' l₂

/-- The composition form: two runs in sequence assemble into the
concatenated run. -/
theorem run_append_some {st : State} {l₁ l₂ : List Move} {A W : State}
    (h₁ : st.run l₁ = some A) (h₂ : A.run l₂ = some W) :
    st.run (l₁ ++ l₂) = some W := by
  rw [run_split_bind st l₁ l₂, h₁]
  show A.run l₂ = some W
  exact h₂

/-- **The paired exchange, forward.**  If the source game wins via a
play whose twin foundation moves are exactly one adjacent pair —
`[pileStack t, pileStack t.flipSuit]`, everything else clean — then the
exchanged game is solvable: the clean prefix and tail mirror verbatim
(the mirror lemma), and the pair mirrors reversed onto the exchanged
successor (`run_swapTwin_pair`). -/
theorem solvable_swapTwin_paired {st : State} {t : Card} {p₁ p₂ : List Move}
    (hc₁ : ∀ m ∈ p₁, Move.cleanTwin t m = true)
    (hc₂ : ∀ m ∈ p₂, Move.cleanTwin t m = true)
    {W : State}
    (hrun : st.run (p₁ ++ [Move.pileStack t, Move.pileStack t.flipSuit] ++ p₂) = some W)
    (hwin : W.isWin = true) :
    (st.swapTwin t).solvableFrom := by
  rw [List.append_assoc p₁ [Move.pileStack t, Move.pileStack t.flipSuit] p₂] at hrun
  rw [run_split_bind st p₁ ([Move.pileStack t, Move.pileStack t.flipSuit] ++ p₂)] at hrun
  cases hA : st.run p₁ with
  | none => rw [hA] at hrun; simp at hrun
  | some A =>
      rw [hA] at hrun
      have hrun1 : A.run ([Move.pileStack t, Move.pileStack t.flipSuit] ++ p₂) = some W := hrun
      rw [run_split_bind A [Move.pileStack t, Move.pileStack t.flipSuit] p₂] at hrun1
      cases hA₁ : A.run [Move.pileStack t, Move.pileStack t.flipSuit] with
      | none => rw [hA₁] at hrun1; simp at hrun1
      | some A₁ =>
          have hrunA : A₁.run p₂ = some W := by
            rw [hA₁] at hrun1
            exact hrun1
          -- decompose the pair firing for `run_swapTwin_pair`
          simp only [State.run] at hA₁
          cases h₀ : A.apply (Move.pileStack t) with
          | none => rw [h₀] at hA₁; simp at hA₁
          | some A₀ =>
              rw [h₀] at hA₁
              have hA₁' : (match State.apply (Move.pileStack t.flipSuit) A₀ with
                  | some st' => some st'
                  | none => none) = some A₁ := hA₁
              cases h₁ : A₀.apply (Move.pileStack t.flipSuit) with
              | none => rw [h₁] at hA₁'; simp at hA₁'
              | some A₁' =>
                  have hAeq : A₁' = A₁ := by
                    rw [h₁] at hA₁'
                    exact Option.some.inj hA₁'
                  have hR1 : (st.swapTwin t).run (p₁.map (Move.swapTwin t))
                      = some (A.swapTwin t) := by
                    rw [run_swapTwin_clean t st p₁ hc₁, hA]
                    rfl
                  have hR2 : (A.swapTwin t).run [Move.pileStack t.flipSuit, Move.pileStack t]
                      = some (A₁.swapTwin t) := run_swapTwin_pair h₀ (hAeq ▸ h₁)
                  have hR3 : (A₁.swapTwin t).run (p₂.map (Move.swapTwin t))
                      = some (W.swapTwin t) := by
                    rw [run_swapTwin_clean t A₁ p₂ hc₂, hrunA]
                    rfl
                  exact ⟨p₁.map (Move.swapTwin t)
                    ++ [Move.pileStack t.flipSuit, Move.pileStack t]
                    ++ p₂.map (Move.swapTwin t),
                    W.swapTwin t, run_append_some (run_append_some hR1 hR2) hR3, hwin⟩

/-- **The paired exchange, backward.**  The same statement with the
pair reversed: if the EXCHANGED game wins via a play whose twin
foundation moves are the adjacent pair `[pileStack t.flipSuit,
pileStack t]` (the mirror image of the forward shape), the source game
is solvable — the forward theorem at the exchanged state with the pair
`t.flipSuit`, whose exchange is the source by the involution. -/
theorem solvable_swapTwin_paired_back {st : State} {t : Card} {q₁ q₂ : List Move}
    (hc₁ : ∀ m ∈ q₁, Move.cleanTwin t m = true)
    (hc₂ : ∀ m ∈ q₂, Move.cleanTwin t m = true)
    {W : State}
    (hrun : (st.swapTwin t).run (q₁ ++ [Move.pileStack t.flipSuit, Move.pileStack t] ++ q₂)
      = some W)
    (hwin : W.isWin = true) :
    st.solvableFrom := by
  have hc₁' : ∀ m ∈ q₁, Move.cleanTwin t.flipSuit m = true := by
    intro m hm
    rw [← Move.cleanTwin_flipSuit]
    exact hc₁ m hm
  have hc₂' : ∀ m ∈ q₂, Move.cleanTwin t.flipSuit m = true := by
    intro m hm
    rw [← Move.cleanTwin_flipSuit]
    exact hc₂ m hm
  have hrun' : (st.swapTwin t).run (q₁ ++ [Move.pileStack t.flipSuit,
      Move.pileStack t.flipSuit.flipSuit] ++ q₂) = some W := by
    rw [Card.flipSuit_flipSuit]
    exact hrun
  have h := solvable_swapTwin_paired (st := st.swapTwin t) (t := t.flipSuit)
    hc₁' hc₂' hrun' hwin
  rw [State.swapTwin_flipSuit, State.swapTwin_swapTwin] at h
  exact h
