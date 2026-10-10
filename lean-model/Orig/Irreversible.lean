import Orig.Fate
import Orig.Integrity

/-!
# Orig — the single-step measure tables and the constructive undos

The accounting half of the irreversibility classification.  Three
natural measures are defined on a position, and every legal single
move is tabulated against all three by reading `State.step`'s move
branches directly — no play induction happens here (the walk
combinators live in `Orig.Mono`, which consumes this file):

* `cycleCount` — stock plus waste.  Never rises; the two
  waste-consuming moves (`.wasteToFound`, `.wasteToTab`) drop it
  strictly, wherever they succeed.  The draw conserves it exactly:
  recycling reverses the waste into the stock, and `State.dealUpTo`
  splits the stock without loss (the two `dealUpTo` length halves
  add back to the whole), so a draw only reshapes stock/waste.

* `hiddenTotal` — the seven piles' face-down cards (a flat map over
  `Anchor.all`; the flat-map length is the chosen sum — it makes the
  pointwise pile lemmas usable verbatim).  Never rises.  It drops
  strictly exactly when a move uncovers a hidden card: the reveal
  inside `Pile.afterRunRemoved` fires only for the two run-removing
  moves (`.tabToFound` after a `chop`, `.tabToTab` after a `below`),
  and only when the moved card was the last face-up card of a pile
  that still had hidden cards.  `afterRunRemoved_hidden` is that
  trichotomy.

* `foundTotal` — the foundations' total.  Never falls, and it rises
  strictly at `.tabToFound` (and `.wasteToFound`); the only move
  that can take from a foundation is `.foundToTab`, which the
  no-worry statement excludes by hypothesis.

The reversible half: explicit one-move undo plays.  A successful
`.foundToTab` is undone by `.tabToFound` of the same card
(`foundToTab_undo`), and a no-reveal `.tabToFound` is undone by
`.foundToTab` back onto its original seat (`tabToFound_undo_under`,
`tabToFound_undo_bare`).  Both are stated with precise side
premises, each documented with the wild-state corner that makes it
*not* derivable from the step hypothesis alone: the physical game's
searches (`pileOfTop`, `nextUp` after a chop) consult the rest of
the position, and a wild (non-`WF`) state can double a card or
miscount a foundation so that the undo move would aim elsewhere or
be illegal.  Every premise is local — no `State.WF` anywhere.

Axiom audit (post-build `#print axioms`, every declaration of this
module, public and private): none depends on `Classical.choice` and
none on `sorryAx`; every head is axiom-free, `[propext]`,
`[Quot.sound]`, or `[propext, Quot.sound]`.  The three tables
(`cycleCount_step`, `hiddenTotal_step`, `foundTotal_step`), the
no-worry row (`foundTotal_step_noworry`), and the six undo heads
(`foundToTab_undo`, `foundToTab_reversible`,
`tabToFound_undo_under`, `tabToFound_reversible_under`,
`tabToFound_undo_bare`, `tabToFound_reversible_bare`) all audit
`[propext, Quot.sound]`; the early rfl-ladder heads are
axiom-free.  The strict flat-map lemma splits `Nat.lt_or_ge` at
the summed length — never an equality split on an abstract
element type — precisely so the whole chapter stays choice-free.
-/

/-! ## The three measures -/

/-- Cards in the draw cycle: the stock plus the waste.  A draw
conserves it exactly; a waste-consuming move pops it. -/
def cycleCount (st : State) : Nat := st.stock.length + st.waste.length

/-- The face-down cards across the seven piles, as one flat sum:
`(Anchor.all.flatMap …).length` — the flat-map form is chosen over a
numeric fold so pile-wise equalities can be pushed directly. -/
def hiddenTotal (st : State) : Nat := (Anchor.all.flatMap fun a => (st.piles a).hidden).length

/-- The foundation total: `(Suit.all.flatMap st.found).length`,
same flat-map convention as `hiddenTotal`. -/
def foundTotal (st : State) : Nat := (Suit.all.flatMap st.found).length

/-! ## Flat-map sums -/

/-- Flat map unrolls one head element.  `rfl` on sight: the
core definition matches on the list. -/
private theorem flatMap_cons {α β : Type} (f : α → List β) (x : α) (t : List α) :
    List.flatMap f (x :: t) = f x ++ List.flatMap f t := rfl

/-- Pointwise pile-hidden equality gives hidden-total equality. -/
theorem hiddenTotal_congr {s s' : State}
    (h : ∀ a, (s'.piles a).hidden = (s.piles a).hidden) :
    hiddenTotal s' = hiddenTotal s := by
  unfold hiddenTotal
  rw [show (fun a => (s'.piles a).hidden) = (fun a => (s.piles a).hidden) from funext h]

/-- Pointwise foundation equality gives found-total equality. -/
theorem foundTotal_congr {s s' : State}
    (h : ∀ σ, s'.found σ = s.found σ) :
    foundTotal s' = foundTotal s := by
  unfold foundTotal
  rw [show s'.found = s.found from funext h]

/-- A flat map is length-monotone in the summed function. -/
private theorem flatMap_length_mono {α : Type} (F G : α → List Card) (as : List α)
    (h : ∀ y, (G y).length ≤ (F y).length) :
    (as.flatMap G).length ≤ (as.flatMap F).length := by
  induction as with
  | nil => exact Nat.le_refl _
  | cons y t ih =>
      rw [flatMap_cons, flatMap_cons, List.length_append, List.length_append]
      exact Nat.add_le_add (h y) ih

/-- The strict version: if some witness point drops by one and
nothing grows anywhere, the total drops by at least one.  The
witness may occur several times in `as`; each occurrence is still
governed by the pointwise-nondecreasing hypothesis, so the sum
never falls more than claimed.  The one case split is
`Nat.lt_or_ge` at the summed length — never an equality split on
the (abstract) element type — so the lemma is constructive and
axiom-free. -/
private theorem flatMap_length_mono_lt {α : Type} (F G : α → List Card) (as : List α) (x : α)
    (hmem : x ∈ as) (hle : ∀ y, (G y).length ≤ (F y).length)
    (hlt : (G x).length + 1 ≤ (F x).length) :
    (as.flatMap G).length + 1 ≤ (as.flatMap F).length := by
  induction as with
  | nil => exact absurd hmem (by simp)
  | cons y t ih =>
      rw [flatMap_cons, flatMap_cons, List.length_append, List.length_append]
      rcases Nat.lt_or_ge ((G y).length) ((F y).length) with hlt' | hge
      · have htail := flatMap_length_mono F G t hle
        omega
      · have hy : (G y).length = (F y).length := Nat.le_antisymm (hle y) hge
        have hne : y = x → False := by
          intro heq
          subst heq
          omega
        have hxint : x ∈ t := (List.mem_cons.mp hmem).resolve_left (fun heq => hne heq.symm)
        have hp := ih hxint
        omega

/-- Pile-wise domination gives hidden-total domination. -/
theorem hiddenTotal_mono {s s' : State}
    (h : ∀ a, (s'.piles a).hidden.length ≤ (s.piles a).hidden.length) :
    hiddenTotal s' ≤ hiddenTotal s :=
  flatMap_length_mono _ _ _ h

/-- Foundation-wise domination gives found-total domination. -/
theorem foundTotal_mono {s s' : State}
    (h : ∀ σ, (s'.found σ).length ≤ (s.found σ).length) :
    foundTotal s' ≤ foundTotal s :=
  flatMap_length_mono _ _ _ h

/-! ## List-end helpers -/

/-- The last element of a snoc. -/
theorem lastOf_snoc : ∀ (l : List Card) (c : Card), lastOf (l ++ [c]) = some c := by
  intro l
  induction l with
  | nil => intro c; rfl
  | cons x t ih =>
      intro c
      cases t with
      | nil => rfl
      | cons y t' =>
          have h2 : lastOf ((x :: y :: t') ++ [c]) = lastOf ((y :: t') ++ [c]) := rfl
          rw [h2]
          exact ih c

/-- Snoc drops only the snocced element under `chop`. -/
theorem chop_snoc : ∀ (l : List Card) (c : Card), chop (l ++ [c]) = l := by
  intro l
  induction l with
  | nil => intro c; rfl
  | cons x t ih =>
      intro c
      cases t with
      | nil => rfl
      | cons y t' =>
          have e1 : chop ((x :: y :: t') ++ [c]) = x :: chop ((y :: t') ++ [c]) := rfl
          have e2 : chop ((y :: t') ++ [c]) = y :: t' := ih c
          rw [e1, e2]

/-- A list with a known last element decomposes as `chop` plus that
element — the foundation-prefix cancellation used by every undo. -/
theorem lastOf_chop {c : Card} : ∀ {l : List Card}, lastOf l = some c → l = chop l ++ [c] := by
  intro l
  induction l with
  | nil => intro h; exact absurd h (by simp [lastOf])
  | cons x t ih =>
      intro h
      cases t with
      | nil =>
          have hx : lastOf [x] = some x := rfl
          rw [hx, Option.some.injEq] at h
          rw [h]
          rfl
      | cons y t' =>
          have h2 : lastOf (y :: t') = some c := h
          have h3 : y :: t' = chop (y :: t') ++ [c] := ih h2
          have e1 : chop (x :: y :: t') = x :: chop (y :: t') := rfl
          rw [e1, List.cons_append, ← h3]

/-! ## Pile.afterRunRemoved -/

/-- The hidden-cards trichotomy of the run removal: with a
nonempty remainder the hidden cards never move; with an empty
face-up remainder the reveal fires exactly when hidden cards
remain, dropping the count by one; with no hidden cards nothing
changes. -/
theorem afterRunRemoved_hidden (p : Pile) (pre : List Card) :
    (pre ≠ [] ∧ (Pile.afterRunRemoved p pre).hidden = p.hidden) ∨
    (pre = [] ∧ p.hidden = [] ∧ (Pile.afterRunRemoved p pre).hidden = p.hidden) ∨
    (pre = [] ∧ p.hidden ≠ [] ∧
      (Pile.afterRunRemoved p pre).hidden.length + 1 = p.hidden.length) := by
  cases pre with
  | cons x xs => exact Or.inl ⟨by simp, rfl⟩
  | nil =>
      rcases p with ⟨h, f⟩
      cases h with
      | nil => exact Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)
      | cons g gs =>
          refine Or.inr (Or.inr ⟨rfl, by simp, ?_⟩)
          show (Pile.revealTop { hidden := g :: gs, faceUp := [] } : Pile).hidden.length + 1
            = (g :: gs).length
          simp only [Pile.revealTop, List.length_cons]

/-- The hidden-count never grows through a run removal. -/
theorem afterRunRemoved_hidden_le (p : Pile) (pre : List Card) :
    (Pile.afterRunRemoved p pre).hidden.length ≤ p.hidden.length := by
  rcases afterRunRemoved_hidden p pre with ⟨-, h⟩ | ⟨-, -, h⟩ | ⟨-, -, h⟩
  · rw [h]; exact Nat.le_refl _
  · rw [h]; exact Nat.le_refl _
  · omega

/-- `Pile.revealTop` of the run-emptied pile: hidden cards keep
their tail, so the face-up run heads stay irrelevant to the reveal.
Formalizes the drop-by-one as an explicit successor list. -/
theorem revealTop_hidden_tail {h : Card} {t f : List Card} :
    Pile.revealTop { hidden := h :: t, faceUp := f } = { hidden := t, faceUp := f ++ [h] } := rfl

/-! ## Projections of the placement combinators -/

/-- `setPile` keeps the stock. -/
theorem setPile_stock (st : State) (a : Anchor) (p : Pile) :
    (st.setPile a p).stock = st.stock := rfl

/-- `setPile` keeps the waste. -/
theorem setPile_waste (st : State) (a : Anchor) (p : Pile) :
    (st.setPile a p).waste = st.waste := rfl

/-- `setPile` keeps the draw step. -/
theorem setPile_drawStep (st : State) (a : Anchor) (p : Pile) :
    (st.setPile a p).drawStep = st.drawStep := rfl

/-- `setPile` writes exactly the one pile. -/
theorem setPile_piles (st : State) (a : Anchor) (p : Pile) :
    (st.setPile a p).piles =
      (fun a' => if a' = a then p else st.piles a') := rfl

/-- `setFound` keeps the stock. -/
theorem setFound_stock (st : State) (s : Suit) (l : List Card) :
    (st.setFound s l).stock = st.stock := rfl

/-- `setFound` keeps the waste. -/
theorem setFound_waste (st : State) (s : Suit) (l : List Card) :
    (st.setFound s l).waste = st.waste := rfl

/-- `setFound` keeps the tableau. -/
theorem setFound_piles (st : State) (s : Suit) (l : List Card) :
    (st.setFound s l).piles = st.piles := rfl

/-- `setFound` keeps the draw step. -/
theorem setFound_drawStep (st : State) (s : Suit) (l : List Card) :
    (st.setFound s l).drawStep = st.drawStep := rfl

/-- `setFound` writes exactly the one foundation. -/
theorem setFound_found_self (st : State) (s : Suit) (l : List Card) :
    (st.setFound s l).found s = l := by
  simp [State.setFound]

/-- `setFound` leaves every other foundation untouched. -/
theorem setFound_found_ne (st : State) (s : Suit) (l : List Card) (σ : Suit) (h : σ ≠ s) :
    (st.setFound s l).found σ = st.found σ := by
  simp only [State.setFound]
  rw [ite_eq_right h]

/-- `putCard` keeps the draw-zone contents (it rewrites piles only). -/
theorem putCard_stock (st : State) (c : Card) (b : Base) :
    (st.putCard c b).stock = st.stock := by
  cases b with
  | inl a => rfl
  | inr z => cases hz : st.pileOfTop z <;> simp [State.putCard, hz] <;> rfl

/-- `putCard` keeps the waste. -/
theorem putCard_waste (st : State) (c : Card) (b : Base) :
    (st.putCard c b).waste = st.waste := by
  cases b with
  | inl a => rfl
  | inr z => cases hz : st.pileOfTop z <;> simp [State.putCard, hz] <;> rfl

/-- `putCard` keeps the foundations. -/
theorem putCard_found (st : State) (c : Card) (b : Base) :
    (st.putCard c b).found = st.found := by
  cases b with
  | inl a => rfl
  | inr z => cases hz : st.pileOfTop z <;> simp [State.putCard, hz] <;> rfl

/-- `putCard` keeps the draw step. -/
theorem putCard_drawStep (st : State) (c : Card) (b : Base) :
    (st.putCard c b).drawStep = st.drawStep := by
  cases b with
  | inl a => rfl
  | inr z => cases hz : st.pileOfTop z <;> simp [State.putCard, hz] <;> rfl

/-- Putting a run keeps the draw-zone contents. -/
theorem putRun_stock (st : State) (run : List Card) (b : Base) :
    (st.putRun run b).stock = st.stock := by
  cases b with
  | inl a => rfl
  | inr z => cases hz : st.pileOfTop z <;> simp [State.putRun, hz] <;> rfl

/-- Putting a run keeps the waste. -/
theorem putRun_waste (st : State) (run : List Card) (b : Base) :
    (st.putRun run b).waste = st.waste := by
  cases b with
  | inl a => rfl
  | inr z => cases hz : st.pileOfTop z <;> simp [State.putRun, hz] <;> rfl

/-- Putting a run keeps the foundations. -/
theorem putRun_found (st : State) (run : List Card) (b : Base) :
    (st.putRun run b).found = st.found := by
  cases b with
  | inl a => rfl
  | inr z => cases hz : st.pileOfTop z <;> simp [State.putRun, hz] <;> rfl

/-- Putting a run keeps the draw step. -/
theorem putRun_drawStep (st : State) (run : List Card) (b : Base) :
    (st.putRun run b).drawStep = st.drawStep := by
  cases b with
  | inl a => rfl
  | inr z => cases hz : st.pileOfTop z <;> simp [State.putRun, hz] <;> rfl

/-- A single card onto an empty seat writes exactly that pile to
the singleton card. -/
theorem putCard_piles_inl (st : State) (c : Card) (a : Anchor) :
    (st.putCard c (Sum.inl a)).piles =
      (fun a' => if a' = a then ⟨[], [c]⟩ else st.piles a') := rfl

/-- A single card onto a card base appends to the located pile. -/
theorem putCard_piles_inr (st : State) (c : Card) (z : Card) (k : Anchor)
    (hz : st.pileOfTop z = some k) :
    (st.putCard c (Sum.inr z)).piles =
      (fun a' => if a' = k then { st.piles k with faceUp := (st.piles k).faceUp ++ [c] }
        else st.piles a') := by
  simp only [State.putCard, hz]
  rfl

/-- Putting a run onto an empty seat writes exactly that pile. -/
theorem putRun_piles_inl (st : State) (run : List Card) (a : Anchor) :
    (st.putRun run (Sum.inl a)).piles =
      (fun a' => if a' = a then ⟨[], run⟩ else st.piles a') := rfl

/-- Putting a run onto a card base appends to the located pile. -/
theorem putRun_piles_inr (st : State) (run : List Card) (z : Card) (k : Anchor)
    (hz : st.pileOfTop z = some k) :
    (st.putRun run (Sum.inr z)).piles =
      (fun a' => if a' = k then { st.piles k with faceUp := (st.piles k).faceUp ++ run }
        else st.piles a') := by
  simp only [State.putRun, hz]
  rfl

/-! ## Guard inversions -/

/-- The empty-seat placement guard: empty target, king card. -/
theorem canPlace_inl {st : State} {c : Card} {a : Anchor}
    (h : st.canPlace c (Sum.inl a) = true) :
    (st.piles a).isEmpty = true ∧ c.rank = Rank.king := by
  simp only [State.canPlace, Bool.and_eq_true] at h
  exact ⟨h.1, of_decide_eq_true h.2⟩

/-- The card-on-card placement guard: the base card tops some pile
and the mover fits under it. -/
theorem canPlace_inr {st : State} {c z : Card} (h : st.canPlace c (Sum.inr z) = true) :
    ∃ k, st.pileOfTop z = some k ∧ canSitOn c z = true := by
  simp only [State.canPlace] at h
  cases hz : st.pileOfTop z with
  | none => rw [hz] at h; exact absurd h (by simp)
  | some k => rw [hz] at h; exact ⟨k, rfl, h⟩

/-- The waste-top guard read off the step: the waste head is the
naming card. -/
theorem wasteIs_head {st : State} {c : Card}
    (h : st.wasteIs c = true) : ∃ xs, st.waste = c :: xs := by
  cases hw : st.waste with
  | nil => rw [State.wasteIs_nil hw] at h; exact absurd h (by simp)
  | cons x xs =>
      rw [State.wasteIs_cons hw c] at h
      have hxc : x = c := of_decide_eq_true h
      exact ⟨xs, by rw [hxc]⟩

/-! ## The draw pipeline -/

/-- `dealUpTo` splits without loss: the dealt cards and the
remaining stock add back to the whole. -/
theorem dealUpTo_length (k : Nat) : ∀ (l : List Card),
    (State.dealUpTo k l).1.length + (State.dealUpTo k l).2.length = l.length := by
  intro l
  induction k generalizing l with
  | zero => simp [State.dealUpTo]
  | succ n ih =>
      cases l with
      | nil => simp [State.dealUpTo]
      | cons x t =>
          show (x :: (State.dealUpTo n t).1).length + (State.dealUpTo n t).2.length
            = (x :: t).length
          have h1 : (x :: (State.dealUpTo n t).1).length = (State.dealUpTo n t).1.length + 1 := rfl
          have h2 : (x :: t).length = t.length + 1 := rfl
          rw [h1, h2]
          have h3 := ih t
          omega

/-- Recycling keeps the cycle count: it only reshapes stock and
waste. -/
theorem recycle_cycle (st : State) : cycleCount st.recycle = cycleCount st := by
  cases hs : st.stock with
  | nil =>
      cases hw : st.waste with
      | nil => rw [show st.recycle = st from by simp only [State.recycle, hs, hw]]
      | cons x t =>
          rw [show st.recycle = { st with stock := (x :: t).reverse, waste := [] } from by
              simp only [State.recycle, hs, hw]]
          simp only [cycleCount, List.length_reverse, hs, hw, List.length_cons, List.length_nil]
          omega
  | cons y s =>
      rw [show st.recycle = st from by simp only [State.recycle, hs]]

/-- Recycling keeps the piles. -/
theorem recycle_piles (st : State) : st.recycle.piles = st.piles := by
  cases hs : st.stock <;> cases hw : st.waste <;>
    simp only [State.recycle, hs, hw]

/-- Recycling keeps the foundations. -/
theorem recycle_found (st : State) : st.recycle.found = st.found := by
  cases hs : st.stock <;> cases hw : st.waste <;>
    simp only [State.recycle, hs, hw]

/-- A successful `dealStock` is the split literal: the dealt prefix
reversed onto the waste, the rest as stock. -/
private theorem dealStock_inv {rt : State} {s' : State}
    (h : State.dealStock rt = some s') :
    rt.stock ≠ [] ∧
      s' = { rt with
             stock := (State.dealUpTo rt.drawStep rt.stock).2,
             waste := (State.dealUpTo rt.drawStep rt.stock).1.reverse ++ rt.waste } := by
  cases hs : rt.stock with
  | nil =>
      rw [show State.dealStock rt = none from by simp only [State.dealStock, hs]] at h
      exact absurd h (by simp)
  | cons x t =>
      refine ⟨by simp, ?_⟩
      rw [show State.dealStock rt =
            some { rt with
                   stock := (State.dealUpTo rt.drawStep (x :: t)).2,
                   waste := (State.dealUpTo rt.drawStep (x :: t)).1.reverse ++ rt.waste } from by
              simp only [State.dealStock, hs]] at h
      injection h with hEq
      exact hEq.symm

/-- A successful draw keeps the piles (it touches stock/waste only). -/
theorem stepDraw_piles {st s' : State} (h : st.stepDraw = some s') : s'.piles = st.piles := by
  have hd : State.dealStock st.recycle = some s' := h
  obtain ⟨-, hEq⟩ := dealStock_inv hd
  rw [hEq]
  rw [show st.recycle.piles = st.piles from recycle_piles st]

/-- A successful draw keeps the foundations. -/
theorem stepDraw_found {st s' : State} (h : st.stepDraw = some s') : s'.found = st.found := by
  have hd : State.dealStock st.recycle = some s' := h
  obtain ⟨-, hEq⟩ := dealStock_inv hd
  rw [hEq]
  rw [show st.recycle.found = st.found from recycle_found st]

/-- A successful draw conserves the cycle count exactly: the split
instead of a loss is `dealUpTo_length`, and recycling already
conserves (`recycle_cycle`). -/
theorem stepDraw_cycle {st s' : State} (h : st.stepDraw = some s') :
    cycleCount s' = cycleCount st := by
  have hd : State.dealStock st.recycle = some s' := h
  obtain ⟨-, hEq⟩ := dealStock_inv hd
  have hsplit := dealUpTo_length (st.recycle).drawStep (st.recycle).stock
  have e1 : s'.stock = (State.dealUpTo (st.recycle).drawStep (st.recycle).stock).2 := by
    rw [hEq]
  have e2 : s'.waste =
      (State.dealUpTo (st.recycle).drawStep (st.recycle).stock).1.reverse
        ++ (st.recycle).waste := by
    rw [hEq]
  show s'.stock.length + s'.waste.length = st.stock.length + st.waste.length
  rw [e1, e2, List.length_append, List.length_reverse]
  have hrc : (st.recycle).stock.length + (st.recycle).waste.length
      = st.stock.length + st.waste.length := recycle_cycle st
  omega

/-! ## Step inversions, one per move constructor -/

/-- A successful `.wasteToFound`: the guard held, the waste was
nonempty, and the successor is the written foundation with the
waste popped. -/
private theorem step_wasteToFound_inv {st : State} {c : Card} {s' : State}
    (h : State.step st (Move.wasteToFound c) = some s') :
    (st.wasteIs c && st.nextUp c) = true ∧
    ∃ x xs, st.waste = x :: xs ∧
      s' = { st.setFound c.suit (st.found c.suit ++ [c]) with waste := xs } := by
  simp only [State.step] at h
  split at h
  · rename_i hg
    split at h
    · rename_i _ x xs hw
      injection h with hEq
      exact ⟨hg, x, xs, hw, hEq.symm⟩
    · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- A successful `.wasteToTab`: guard, nonempty waste, and the
placement with the waste popped. -/
private theorem step_wasteToTab_inv {st : State} {c : Card} {b : Base} {s' : State}
    (h : State.step st (Move.wasteToTab c b) = some s') :
    (st.wasteIs c && st.canPlace c b) = true ∧
    ∃ x xs, st.waste = x :: xs ∧
      s' = { st.putCard c b with waste := xs } := by
  simp only [State.step] at h
  split at h
  · rename_i hg
    split at h
    · rename_i _ x xs hw
      injection h with hEq
      exact ⟨hg, x, xs, hw, hEq.symm⟩
    · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- A successful `.tabToFound`: the card was next-up, its pile was
located, and the successor is the raised foundation with the
(chopped) run removed from that pile. -/
private theorem step_tabToFound_inv {st : State} {c : Card} {s' : State}
    (h : State.step st (Move.tabToFound c) = some s') :
    st.nextUp c = true ∧
    ∃ a, st.pileOfTop c = some a ∧
      s' = { st.setFound c.suit (st.found c.suit ++ [c]) with
             piles := fun a' =>
               if a' = a then Pile.afterRunRemoved (st.piles a) (chop (st.piles a).faceUp)
               else st.piles a' } := by
  simp only [State.step] at h
  split at h
  · rename_i hn
    split at h
    · exact absurd h (by simp)
    · rename_i _ a hp
      injection h with hEq
      exact ⟨hn, a, hp, hEq.symm⟩
  · exact absurd h (by simp)

/-- A successful `.foundToTab`: the named card is the foundation
top, the placement is legal, and the successor is the chopped
foundation with the card placed. -/
private theorem step_foundToTab_inv {st : State} {c : Card} {b : Base} {s' : State}
    (h : State.step st (Move.foundToTab c b) = some s') :
    ∃ c', st.foundTop c.suit = some c' ∧ c' = c ∧ st.canPlace c b = true ∧
      s' = (st.setFound c.suit (chop (st.found c.suit))).putCard c b := by
  simp only [State.step] at h
  split at h
  · split at h
    · rename_i _ c' ht hg
      rw [Bool.and_eq_true] at hg
      injection h with hEq
      exact ⟨c', ht, of_decide_eq_true hg.1, hg.2, hEq.symm⟩
    · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- A successful `.tabToTab`: the run head's pile was located, the
placement is legal, the face-up run from the head is nonempty, and
the successor is the pile-with-run-removed then the run placed. -/
private theorem step_tabToTab_inv {st : State} {c : Card} {b : Base} {s' : State}
    (h : State.step st (Move.tabToTab c b) = some s') :
    ∃ a, st.pileHolding c = some a ∧ st.canPlace c b = true ∧
      fromCard c (st.piles a).faceUp ≠ [] ∧
        s' = (st.setPile a
            (Pile.afterRunRemoved (st.piles a) (below c (st.piles a).faceUp))).putRun
              (fromCard c (st.piles a).faceUp) b := by
  simp only [State.step] at h
  split at h
  · exact absurd h (by simp)
  · rename_i _ a hh
    split at h
    · rename_i hcp
      split at h
      · exact absurd h (by simp)
      · rename_i _ hne
        injection h with hEq
        exact ⟨a, hh, hcp, hne, hEq.symm⟩
    · exact absurd h (by simp)

/-! ## Shared per-anchor facts about placements -/

/-- A legal placement never disturbs hidden cards: an empty-seat
landing targets only an (already empty) pile, and a card landing
only appends to a face-up run. -/
theorem putCard_hidden_eq {st : State} {c : Card} {b : Base}
    (hcp : st.canPlace c b = true) (a' : Anchor) :
    ((st.putCard c b).piles a').hidden = (st.piles a').hidden := by
  cases b with
  | inl a =>
      obtain ⟨hemp, -⟩ := canPlace_inl hcp
      obtain ⟨hhd, -⟩ := (Pile.isEmpty_eq _).mp hemp
      simp only [putCard_piles_inl]
      by_cases hae : a' = a
      · subst hae
        rw [ite_eq_left rfl, hhd]
      · rw [ite_eq_right hae]
  | inr z =>
      obtain ⟨k, hz, -⟩ := canPlace_inr hcp
      simp only [putCard_piles_inr _ _ _ _ hz]
      by_cases hae : a' = k
      · subst hae
        rw [ite_eq_left rfl]
      · rw [ite_eq_right hae]

/-- The intermediate `setPile` of the run removal never enlarges a
pile's hidden cards (the touched pile goes through
`Pile.afterRunRemoved`). -/
theorem setPile_afterRunRemoved_hidden_le (st : State) (a : Anchor) (c : Card) (a' : Anchor) :
    ((st.setPile a
      (Pile.afterRunRemoved (st.piles a) (below c (st.piles a).faceUp))).piles a').hidden.length
        ≤ (st.piles a').hidden.length := by
  by_cases hae : a' = a
  · subst hae
    simp only [State.setPile]
    rw [ite_true]
    exact afterRunRemoved_hidden_le _ _
  · simp only [State.setPile]
    rw [ite_eq_right hae]
    exact Nat.le_refl _

/-! ## Table 1: the draw-cycle count -/

/-- Same stock and waste give the same cycle count. -/
theorem cycleCount_eq_of_stock_waste {s s' : State}
    (hst : s'.stock = s.stock) (hwa : s'.waste = s.waste) : cycleCount s' = cycleCount s := by
  show s'.stock.length + s'.waste.length = s.stock.length + s.waste.length
  rw [hst, hwa]

/-- A successful `.wasteToFound` pops the waste, so the cycle count
strictly drops. -/
theorem cycleCount_step_wasteToFound {st : State} {c : Card} {s' : State}
    (h : State.step st (Move.wasteToFound c) = some s') :
    cycleCount s' + 1 ≤ cycleCount st := by
  obtain ⟨-, x, xs, hw, hs⟩ := step_wasteToFound_inv h
  rw [hs]
  show st.stock.length + xs.length + 1 ≤ st.stock.length + st.waste.length
  rw [hw]
  simp only [List.length_cons]
  omega

/-- A successful `.wasteToTab` pops the waste, so the cycle count
strictly drops. -/
theorem cycleCount_step_wasteToTab {st : State} {c : Card} {b : Base} {s' : State}
    (h : State.step st (Move.wasteToTab c b) = some s') :
    cycleCount s' + 1 ≤ cycleCount st := by
  obtain ⟨-, x, xs, hw, hs⟩ := step_wasteToTab_inv h
  rw [hs]
  show (st.putCard c b).stock.length + xs.length + 1 ≤ st.stock.length + st.waste.length
  rw [putCard_stock, hw]
  simp only [List.length_cons]
  omega

/-- Table 1: no legal single move ever raises the draw-cycle count
(stock plus waste).  The two waste consumers drop it strictly
(`cycleCount_step_wasteToFound`, `cycleCount_step_wasteToTab`);
the draw conserves it exactly (`stepDraw_cycle`). -/
theorem cycleCount_step {st : State} {m : Move} {s' : State}
    (h : State.step st m = some s') : cycleCount s' ≤ cycleCount st := by
  cases m with
  | draw => have := stepDraw_cycle h; omega
  | wasteToFound c => have := cycleCount_step_wasteToFound h; omega
  | wasteToTab c b => have := cycleCount_step_wasteToTab h; omega
  | tabToFound c =>
      obtain ⟨-, a, -, hs⟩ := step_tabToFound_inv h
      rw [hs]
      exact Nat.le_of_eq (cycleCount_eq_of_stock_waste rfl rfl)
  | foundToTab c b =>
      obtain ⟨-, -, -, -, hs⟩ := step_foundToTab_inv h
      rw [hs]
      exact Nat.le_of_eq (cycleCount_eq_of_stock_waste (putCard_stock _ _ _)
        (by rw [putCard_waste]; rfl))
  | tabToTab c b =>
      obtain ⟨a, -, -, -, hs⟩ := step_tabToTab_inv h
      rw [hs]
      exact Nat.le_of_eq (cycleCount_eq_of_stock_waste (putRun_stock _ _ _)
        (by rw [putRun_waste]; rfl))

/-! ## Table 2: the hidden-card total -/

/-- A pile holding `c` face up is not empty. -/
private theorem Pile.isEmpty_eq_false_of_mem {p : Pile} {c : Card} (h : c ∈ p.faceUp) :
    p.isEmpty = false := by
  rcases p with ⟨hd, f⟩
  cases f with
  | nil => cases h
  | cons x fs => cases hd <;> rfl

/-- The strict witness lemma for flat maps, at hidden-total scale:
dropping one pile's hidden count by one drops the total by at least
one, nothing anywhere growing. -/
theorem hiddenTotal_mono_lt {s s' : State} {a : Anchor}
    (hle : ∀ a', (s'.piles a').hidden.length ≤ (s.piles a').hidden.length)
    (hlt : (s'.piles a).hidden.length + 1 ≤ (s.piles a).hidden.length) :
    hiddenTotal s' + 1 ≤ hiddenTotal s :=
  flatMap_length_mono_lt _ _ Anchor.all a (Anchor.mem_all a) hle hlt

/-- The rise witness lemma for flat maps, at found-total scale:
growing one foundation by one card grows the total by at least one,
nothing anywhere shrinking. -/
theorem foundTotal_rise_lt {s s' : State} {σ : Suit}
    (hle : ∀ τ, (s.found τ).length ≤ (s'.found τ).length)
    (hlt : (s.found σ).length + 1 ≤ (s'.found σ).length) :
    foundTotal s + 1 ≤ foundTotal s' :=
  flatMap_length_mono_lt _ _ Suit.all σ (Suit.mem_all σ) hle hlt

/-- The from-pile hidden facts of a successful `.tabToFound`, per
anchor. -/
private theorem tabToFound_pile_le (st : State) (c : Card) (a : Anchor) (a' : Anchor) :
    (({ st.setFound c.suit (st.found c.suit ++ [c]) with
       piles := fun a'' =>
         if a'' = a then Pile.afterRunRemoved (st.piles a) (chop (st.piles a).faceUp)
         else st.piles a'' } : State).piles a').hidden.length
      ≤ (st.piles a').hidden.length := by
  show (if a' = a then Pile.afterRunRemoved (st.piles a) (chop (st.piles a).faceUp)
      else st.piles a').hidden.length ≤ (st.piles a').hidden.length
  by_cases hae : a' = a
  · subst hae
    rw [ite_eq_left rfl]
    exact afterRunRemoved_hidden_le _ _
  · rw [ite_eq_right hae]
    exact Nat.le_refl _

/-- Table 2: no legal single move ever turns a face-down card
face up. -/
theorem hiddenTotal_step {st : State} {m : Move} {s' : State}
    (h : State.step st m = some s') : hiddenTotal s' ≤ hiddenTotal st := by
  cases m with
  | draw =>
      have hp := stepDraw_piles h
      exact Nat.le_of_eq (hiddenTotal_congr (fun a => by rw [hp]))
  | wasteToFound c =>
      obtain ⟨-, x, xs, -, hs⟩ := step_wasteToFound_inv h
      rw [hs]
      exact Nat.le_of_eq (hiddenTotal_congr (fun _ => rfl))
  | wasteToTab c b =>
      obtain ⟨hg, x, xs, -, hs⟩ := step_wasteToTab_inv h
      have hcp : st.canPlace c b = true := by
        cases hcap : st.canPlace c b with
        | true => rfl
        | false => rw [hcap] at hg; simp at hg
      rw [hs]
      exact Nat.le_of_eq (hiddenTotal_congr (putCard_hidden_eq hcp))
  | tabToFound c =>
      obtain ⟨-, a, -, hs⟩ := step_tabToFound_inv h
      rw [hs]
      exact hiddenTotal_mono (fun a' => tabToFound_pile_le st c a a')
  | foundToTab c b =>
      obtain ⟨-, -, -, hcp, hs⟩ := step_foundToTab_inv h
      rw [hs]
      refine Nat.le_of_eq (hiddenTotal_congr (putCard_hidden_eq hcp))
  | tabToTab c b =>
      obtain ⟨a, hh, hcp, -, hs⟩ := step_tabToTab_inv h
      rw [hs]
      refine hiddenTotal_mono ?_
      intro a'
      cases b with
      | inl a₁ =>
          simp only [putRun_piles_inl]
          by_cases hae : a' = a₁
          · subst hae
            rw [ite_eq_left rfl]
            exact Nat.zero_le _
          · rw [ite_eq_right hae]
            exact setPile_afterRunRemoved_hidden_le st a c a'
      | inr z =>
          cases hz : (st.setPile a
              (Pile.afterRunRemoved (st.piles a) (below c (st.piles a).faceUp))).pileOfTop z with
          | none =>
              have hR : (st.setPile a
                  (Pile.afterRunRemoved (st.piles a) (below c (st.piles a).faceUp))).putRun
                    (fromCard c (st.piles a).faceUp) (Sum.inr z)
                  = (st.setPile a
                    (Pile.afterRunRemoved (st.piles a) (below c (st.piles a).faceUp))) := by
                simp only [State.putRun, hz]
              rw [hR]
              exact setPile_afterRunRemoved_hidden_le st a c a'
          | some k =>
              simp only [putRun_piles_inr _ _ _ _ hz]
              by_cases hae : a' = k
              · rw [hae, ite_eq_left rfl]
                show ((st.setPile a
                    (Pile.afterRunRemoved (st.piles a) (below c (st.piles a).faceUp))).piles k).hidden.length
                  ≤ (st.piles k).hidden.length
                exact setPile_afterRunRemoved_hidden_le st a c k
              · rw [ite_eq_right hae]
                exact setPile_afterRunRemoved_hidden_le st a c a'

/-- The run-removal `setPile`, read at its own pile. -/
theorem setPile_afterRunRemoved_piles_self (st : State) (a : Anchor) (c : Card) :
    (st.setPile a
      (Pile.afterRunRemoved (st.piles a) (below c (st.piles a).faceUp))).piles a
      = Pile.afterRunRemoved (st.piles a) (below c (st.piles a).faceUp) := by
  simp only [State.setPile]
  rw [ite_true]

/-- The run-removal `setPile` leaves every other pile alone. -/
theorem setPile_afterRunRemoved_piles_ne (st : State) (a : Anchor) (c : Card) (a' : Anchor)
    (hne : a' ≠ a) :
    (st.setPile a
      (Pile.afterRunRemoved (st.piles a) (below c (st.piles a).faceUp))).piles a'
      = st.piles a' := by
  simp only [State.setPile]
  rw [ite_eq_right hne]

/-- Per-anchor hidden domination for a `.tabToTab` successor. -/
private theorem tabToTab_pile_le (st : State) (a : Anchor) (c : Card) (b : Base) (a' : Anchor) :
    (((st.setPile a
        (Pile.afterRunRemoved (st.piles a) (below c (st.piles a).faceUp))).putRun
          (fromCard c (st.piles a).faceUp) b).piles a').hidden.length
      ≤ (st.piles a').hidden.length := by
  cases b with
  | inl a₁ =>
      simp only [putRun_piles_inl]
      by_cases hae : a' = a₁
      · rw [hae, ite_eq_left rfl]
        exact Nat.zero_le _
      · rw [ite_eq_right hae]
        exact setPile_afterRunRemoved_hidden_le st a c a'
  | inr z =>
      cases hz : (st.setPile a
          (Pile.afterRunRemoved (st.piles a) (below c (st.piles a).faceUp))).pileOfTop z with
      | none =>
          have hR : (st.setPile a
              (Pile.afterRunRemoved (st.piles a) (below c (st.piles a).faceUp))).putRun
                (fromCard c (st.piles a).faceUp) (Sum.inr z)
              = (st.setPile a
                (Pile.afterRunRemoved (st.piles a) (below c (st.piles a).faceUp))) := by
            simp only [State.putRun, hz]
          rw [hR]
          exact setPile_afterRunRemoved_hidden_le st a c a'
      | some k =>
          simp only [putRun_piles_inr _ _ _ _ hz]
          by_cases hae : a' = k
          · rw [hae, ite_eq_left rfl]
            show ((st.setPile a
                (Pile.afterRunRemoved (st.piles a) (below c (st.piles a).faceUp))).piles k).hidden.length
              ≤ (st.piles k).hidden.length
            exact setPile_afterRunRemoved_hidden_le st a c k
          · rw [ite_eq_right hae]
            exact setPile_afterRunRemoved_hidden_le st a c a'

/-- A successful `.tabToTab` moves the whole run headed by `c`, so
the source pile's hidden cards after the successor are exactly the
run removal's (a run can never land back on the pile it left — the
empty-seat branch targets an empty pile, but this pile holds `c`
face up). -/
private theorem tabToTab_a_hidden (st : State) (a : Anchor) (c : Card) (b : Base)
    (hmem : c ∈ (st.piles a).faceUp) (hcp : st.canPlace c b = true) :
    (((st.setPile a
        (Pile.afterRunRemoved (st.piles a) (below c (st.piles a).faceUp))).putRun
          (fromCard c (st.piles a).faceUp) b).piles a).hidden
      = (Pile.afterRunRemoved (st.piles a) (below c (st.piles a).faceUp)).hidden := by
  cases b with
  | inl a₁ =>
      obtain ⟨hemp, -⟩ := canPlace_inl hcp
      have hfa : (st.piles a).isEmpty = false := Pile.isEmpty_eq_false_of_mem hmem
      have hne : a₁ ≠ a := by
        intro heq
        rw [heq] at hemp
        exact absurd hemp (by rw [hfa]; simp)
      simp only [putRun_piles_inl]
      rw [ite_eq_right (Ne.symm hne), setPile_afterRunRemoved_piles_self st a c]
  | inr z =>
      cases hz : (st.setPile a
          (Pile.afterRunRemoved (st.piles a) (below c (st.piles a).faceUp))).pileOfTop z with
      | none =>
          have hR : (st.setPile a
              (Pile.afterRunRemoved (st.piles a) (below c (st.piles a).faceUp))).putRun
                (fromCard c (st.piles a).faceUp) (Sum.inr z)
              = (st.setPile a
                (Pile.afterRunRemoved (st.piles a) (below c (st.piles a).faceUp))) := by
            simp only [State.putRun, hz]
          rw [hR, setPile_afterRunRemoved_piles_self st a c]
      | some k =>
          by_cases hka : k = a
          · simp only [putRun_piles_inr _ _ _ _ hz]
            rw [hka, ite_eq_left rfl]
            show ((st.setPile a
                (Pile.afterRunRemoved (st.piles a) (below c (st.piles a).faceUp))).piles a).hidden
              = (Pile.afterRunRemoved (st.piles a) (below c (st.piles a).faceUp)).hidden
            rw [setPile_afterRunRemoved_piles_self st a c]
          · simp only [putRun_piles_inr _ _ _ _ hz]
            rw [ite_eq_right (Ne.symm hka)]
            show ((st.setPile a
                (Pile.afterRunRemoved (st.piles a) (below c (st.piles a).faceUp))).piles a).hidden
              = (Pile.afterRunRemoved (st.piles a) (below c (st.piles a).faceUp)).hidden
            rw [setPile_afterRunRemoved_piles_self st a c]

/-- A successful `.tabToTab` that empties the from-pile's face-up
prefix over a nonempty hidden stack reveals one card: the hidden
total drops by at least one. -/
theorem hiddenTotal_step_tabToTab_reveal {st : State} {c : Card} {b : Base} {a : Anchor}
    {s' : State} (h : State.step st (Move.tabToTab c b) = some s')
    (hh : st.pileHolding c = some a)
    (hrev : below c (st.piles a).faceUp = []) (hhne : (st.piles a).hidden ≠ []) :
    hiddenTotal s' + 1 ≤ hiddenTotal st := by
  obtain ⟨a₀, hh2, hcp, -, hs⟩ := step_tabToTab_inv h
  rw [hh2] at hh
  injection hh with haa
  rw [haa] at hs
  have hmem : c ∈ (st.piles a).faceUp := by
    have := pileHolding_mem hh2
    rw [haa] at this
    exact this
  rw [hs]
  refine hiddenTotal_mono_lt (a := a) ?_ ?_
  · intro a'
    exact tabToTab_pile_le st a c b a'
  · rw [tabToTab_a_hidden st a c b hmem hcp, hrev]
    rcases afterRunRemoved_hidden (st.piles a) [] with ⟨hne, -⟩ | ⟨-, hhd, -⟩ | ⟨-, -, hdrop⟩
    · exact absurd rfl hne
    · exact absurd hhne (by simp [hhd])
    · omega

/-- The run removal keeps hidden cards exactly when no reveal
fires. -/
theorem afterRunRemoved_hidden_eq_of_noreveal {p : Pile} {pre : List Card}
    (hnr : pre ≠ [] ∨ p.hidden = []) :
    (Pile.afterRunRemoved p pre).hidden = p.hidden := by
  rcases afterRunRemoved_hidden p pre with ⟨-, h⟩ | ⟨-, -, h⟩ | ⟨he, hhne, -⟩
  · exact h
  · exact h
  · rcases hnr with hne | hhd
    · exact absurd he hne
    · exact absurd hhd hhne

/-- The noreveal per-pile equality for a `.tabToTab` successor:
every pile keeps its hidden cards exactly. -/
private theorem tabToTab_pile_eq (st : State) (a : Anchor) (c : Card) (b : Base) (a' : Anchor)
    (hmem : c ∈ (st.piles a).faceUp) (hcp : st.canPlace c b = true)
    (hnr : below c (st.piles a).faceUp ≠ [] ∨ (st.piles a).hidden = []) :
    (((st.setPile a
        (Pile.afterRunRemoved (st.piles a) (below c (st.piles a).faceUp))).putRun
          (fromCard c (st.piles a).faceUp) b).piles a').hidden
      = (st.piles a').hidden := by
  have hSelfEq : (Pile.afterRunRemoved (st.piles a) (below c (st.piles a).faceUp)).hidden
      = (st.piles a).hidden :=
    afterRunRemoved_hidden_eq_of_noreveal (p := st.piles a) hnr
  cases b with
  | inl a₁ =>
      obtain ⟨hemp, -⟩ := canPlace_inl hcp
      obtain ⟨hhd1, -⟩ := (Pile.isEmpty_eq _).mp hemp
      have hfa : (st.piles a).isEmpty = false := Pile.isEmpty_eq_false_of_mem hmem
      have hne : a₁ ≠ a := by
        intro heq
        rw [heq] at hemp
        exact absurd hemp (by rw [hfa]; simp)
      simp only [putRun_piles_inl]
      by_cases hae : a' = a₁
      · rw [hae, ite_eq_left rfl, hhd1]
      · rw [ite_eq_right hae]
        by_cases haa : a' = a
        · rw [haa, setPile_afterRunRemoved_piles_self st a c, hSelfEq]
        · rw [setPile_afterRunRemoved_piles_ne st a c a' haa]
  | inr z =>
      cases hz : (st.setPile a
          (Pile.afterRunRemoved (st.piles a) (below c (st.piles a).faceUp))).pileOfTop z with
      | none =>
          have hR : (st.setPile a
              (Pile.afterRunRemoved (st.piles a) (below c (st.piles a).faceUp))).putRun
                (fromCard c (st.piles a).faceUp) (Sum.inr z)
              = (st.setPile a
                (Pile.afterRunRemoved (st.piles a) (below c (st.piles a).faceUp))) := by
            simp only [State.putRun, hz]
          rw [hR]
          by_cases haa : a' = a
          · rw [haa, setPile_afterRunRemoved_piles_self st a c, hSelfEq]
          · rw [setPile_afterRunRemoved_piles_ne st a c a' haa]
      | some k =>
          by_cases hka : k = a
          · rw [hka] at hz
            simp only [putRun_piles_inr _ _ _ _ hz]
            by_cases hae : a' = a
            · rw [hae, ite_eq_left rfl]
              rw [setPile_afterRunRemoved_piles_self st a c, hSelfEq]
            · rw [ite_eq_right hae, setPile_afterRunRemoved_piles_ne st a c a' hae]
          · simp only [putRun_piles_inr _ _ _ _ hz]
            by_cases hae : a' = k
            · rw [hae, ite_eq_left rfl]
              show ((st.setPile a
                  (Pile.afterRunRemoved (st.piles a) (below c (st.piles a).faceUp))).piles k).hidden
                = (st.piles k).hidden
              rw [setPile_afterRunRemoved_piles_ne st a c k hka]
            · rw [ite_eq_right hae]
              by_cases haa : a' = a
              · rw [haa, setPile_afterRunRemoved_piles_self st a c, hSelfEq]
              · rw [setPile_afterRunRemoved_piles_ne st a c a' haa]

/-- A successful `.tabToTab` that reveals nothing keeps the hidden
total exactly. -/
theorem hiddenTotal_step_tabToTab_noreveal {st : State} {c : Card} {b : Base} {a : Anchor}
    {s' : State} (h : State.step st (Move.tabToTab c b) = some s')
    (hh : st.pileHolding c = some a)
    (hnorev : below c (st.piles a).faceUp ≠ [] ∨ (st.piles a).hidden = []) :
    hiddenTotal s' = hiddenTotal st := by
  obtain ⟨a₀, hh2, hcp, -, hs⟩ := step_tabToTab_inv h
  rw [hh2] at hh
  injection hh with haa
  rw [haa] at hs
  have hmem : c ∈ (st.piles a).faceUp := by
    have hma := pileHolding_mem hh2
    rw [haa] at hma
    exact hma
  rw [hs]
  exact hiddenTotal_congr (fun a' => tabToTab_pile_eq st a c b a' hmem hcp hnorev)

/-! ## Table 3: the foundation total -/

/-- A successful waste-to-foundation raises the foundation total
strictly. -/
theorem foundTotal_step_wasteToFound {st : State} {c : Card} {s' : State}
    (h : State.step st (Move.wasteToFound c) = some s') :
    foundTotal st + 1 ≤ foundTotal s' := by
  obtain ⟨-, x, xs, -, hs⟩ := step_wasteToFound_inv h
  have hself := setFound_found_self st c.suit (st.found c.suit ++ [c])
  have hlen : [c].length = 1 := rfl
  rw [hs]
  refine foundTotal_rise_lt (σ := c.suit) ?_ ?_
  · intro τ
    by_cases hτ : τ = c.suit
    · rw [hτ, hself, List.length_append]
      omega
    · have hπ : (st.setFound c.suit (st.found c.suit ++ [c])).found τ
          = ({ st.setFound c.suit (st.found c.suit ++ [c]) with waste := xs } : State).found τ := rfl
      rw [hπ]
      rw [setFound_found_ne st c.suit _ τ hτ]
      exact Nat.le_refl _
  · rw [hself, List.length_append]
    omega

/-- The strict drop witness lemma for flat maps, at found-total
scale: one foundation shrinking by one card drops the total by at
least one, nothing elsewhere growing. -/
theorem foundTotal_mono_lt {s s' : State} {σ : Suit}
    (hle : ∀ τ, (s'.found τ).length ≤ (s.found τ).length)
    (hlt : (s'.found σ).length + 1 ≤ (s.found σ).length) :
    foundTotal s' + 1 ≤ foundTotal s :=
  flatMap_length_mono_lt _ _ Suit.all σ (Suit.mem_all σ) hle hlt

/-- A successful draw conserves the foundation total exactly (the
draw touches stock and waste only). -/
theorem foundTotal_step_draw {st : State} {s' : State}
    (h : State.step st Move.draw = some s') :
    foundTotal s' = foundTotal st := by
  have hd : st.stepDraw = some s' := h
  exact foundTotal_congr (fun σ => congrFun (stepDraw_found hd) σ)

/-- A successful pile-top-to-foundation raises the foundation total
strictly. -/
theorem foundTotal_step_tabToFound {st : State} {c : Card} {s' : State}
    (h : State.step st (Move.tabToFound c) = some s') :
    foundTotal st + 1 ≤ foundTotal s' := by
  obtain ⟨-, a, -, hs⟩ := step_tabToFound_inv h
  have hself := setFound_found_self st c.suit (st.found c.suit ++ [c])
  have hfound : ∀ σ, (s'.found σ).length
      = ((st.setFound c.suit (st.found c.suit ++ [c])).found σ).length := by
    intro σ
    rw [hs]
  refine foundTotal_rise_lt (σ := c.suit) ?_ ?_
  · intro τ
    rw [hfound τ]
    by_cases hτ : τ = c.suit
    · rw [hτ, hself, List.length_append]
      have h1 : ([c] : List Card).length = 1 := rfl
      omega
    · rw [setFound_found_ne st c.suit _ τ hτ]
      exact Nat.le_refl _
  · rw [hfound c.suit, hself, List.length_append]
    have h1 : ([c] : List Card).length = 1 := rfl
    omega

/-- A successful waste-to-tableau conserves the foundation total
exactly (the placement touches piles only). -/
theorem foundTotal_step_wasteToTab {st : State} {c : Card} {b : Base} {s' : State}
    (h : State.step st (Move.wasteToTab c b) = some s') :
    foundTotal s' = foundTotal st := by
  obtain ⟨-, x, xs, -, hs⟩ := step_wasteToTab_inv h
  rw [hs]
  refine foundTotal_congr (fun σ => ?_)
  rw [show (({ st.putCard c b with waste := xs } : State).found σ)
        = (st.putCard c b).found σ from rfl, putCard_found]

/-- A successful run-between-piles conserves the foundation total
exactly (the placement touches piles only). -/
theorem foundTotal_step_tabToTab {st : State} {c : Card} {b : Base} {s' : State}
    (h : State.step st (Move.tabToTab c b) = some s') :
    foundTotal s' = foundTotal st := by
  obtain ⟨a, -, -, -, hs⟩ := step_tabToTab_inv h
  rw [hs]
  refine foundTotal_congr (fun σ => ?_)
  rw [show (((st.setPile a
        (Pile.afterRunRemoved (st.piles a) (below c (st.piles a).faceUp))).putRun
          (fromCard c (st.piles a).faceUp) b).found σ)
      = st.found σ from by rw [putRun_found, setPile_found]]

/-- A successful `.foundToTab` strictly drops the foundation total:
the step's own guard (`foundTop = some c`) forces the foundation to
end at `c`, so the chop removes exactly one card. -/
theorem foundTotal_step_foundToTab {st : State} {c : Card} {b : Base} {s' : State}
    (h : State.step st (Move.foundToTab c b) = some s') :
    foundTotal s' + 1 ≤ foundTotal st := by
  obtain ⟨c', ht, hc'c, -, hs⟩ := step_foundToTab_inv h
  have hlast : lastOf (st.found c.suit) = some c := by
    have h2 : st.foundTop c.suit = some c := by rw [ht, hc'c]
    exact h2
  have hF : st.found c.suit = chop (st.found c.suit) ++ [c] := lastOf_chop hlast
  have hlen : (st.found c.suit).length = (chop (st.found c.suit)).length + 1 := by
    have hl := congrArg List.length hF
    rw [List.length_append] at hl
    have h1 : ([c] : List Card).length = 1 := rfl
    omega
  rw [hs]
  refine foundTotal_mono_lt (σ := c.suit) ?_ ?_
  · intro τ
    have hπ : (((st.setFound c.suit (chop (st.found c.suit))).putCard c b).found τ).length
        ≤ (st.found τ).length := by
      rw [putCard_found]
      by_cases hτ : τ = c.suit
      · rw [hτ, setFound_found_self]
        omega
      · rw [setFound_found_ne st c.suit _ τ hτ]
        exact Nat.le_refl _
    exact hπ
  · rw [show (((st.setFound c.suit (chop (st.found c.suit))).putCard c b).found c.suit)
        = chop (st.found c.suit) from by rw [putCard_found, setFound_found_self]]
    omega

/-- Table 3, constructor-aware: a legal single move never drops the
foundation total unless it is a `.foundToTab` — the exception the
no-worry statement excludes by hypothesis. -/
theorem foundTotal_step {st : State} {m : Move} {s' : State}
    (h : State.step st m = some s') :
    foundTotal st ≤ foundTotal s' ∨ ∃ c b, m = Move.foundToTab c b := by
  cases m with
  | draw => exact Or.inl (Nat.le_of_eq (foundTotal_step_draw h).symm)
  | wasteToFound c => exact Or.inl (by have := foundTotal_step_wasteToFound h; omega)
  | wasteToTab c b => exact Or.inl (Nat.le_of_eq (foundTotal_step_wasteToTab h).symm)
  | tabToFound c => exact Or.inl (by have := foundTotal_step_tabToFound h; omega)
  | foundToTab c b => exact Or.inr ⟨c, b, rfl⟩
  | tabToTab c b => exact Or.inl (Nat.le_of_eq (foundTotal_step_tabToTab h).symm)

/-- The no-worry row of Table 3: excluding `.foundToTab` by
hypothesis, the foundation total never falls through a legal single
move — the form the classification's no-worry-back fragment
consumes (a returning play may worry about `.foundToTab`; without
it the measure is monotone and the ascent bridge applies). -/
theorem foundTotal_step_noworry {st : State} {m : Move} {s' : State}
    (h : State.step st m = some s')
    (hnw : ∀ c b, m ≠ Move.foundToTab c b) :
    foundTotal st ≤ foundTotal s' := by
  rcases foundTotal_step h with hle | ⟨c, b, hm⟩
  · exact hle
  · exact absurd hm (hnw c b)

/-- A successful `.tabToFound` that empties the from-pile's face-up
run over a nonempty hidden stack reveals one card: the hidden total
drops by at least one. -/
theorem hiddenTotal_step_tabToFound_reveal {st : State} {c : Card} {a : Anchor} {s' : State}
    (h : State.step st (Move.tabToFound c) = some s') (hpa : st.pileOfTop c = some a)
    (hrev : chop (st.piles a).faceUp = []) (hhne : (st.piles a).hidden ≠ []) :
    hiddenTotal s' + 1 ≤ hiddenTotal st := by
  obtain ⟨-, a₀, hp2, hs⟩ := step_tabToFound_inv h
  rw [hp2] at hpa
  injection hpa with haa
  rw [haa] at hs
  rw [hs]
  refine hiddenTotal_mono_lt (a := a) ?_ ?_
  · intro a'
    exact tabToFound_pile_le st c a a'
  · simp only [ite_true]
    rw [hrev]
    rcases afterRunRemoved_hidden (st.piles a) [] with ⟨hne, -⟩ | ⟨-, hhd, -⟩ | ⟨-, -, hdrop⟩
    · exact absurd rfl hne
    · exact absurd hhne (by simp [hhd])
    · omega

/-- A successful `.tabToFound` that reveals nothing keeps the
hidden total exactly. -/
theorem hiddenTotal_step_tabToFound_noreveal {st : State} {c : Card} {a : Anchor} {s' : State}
    (h : State.step st (Move.tabToFound c) = some s') (hpa : st.pileOfTop c = some a)
    (hnorev : chop (st.piles a).faceUp ≠ [] ∨ (st.piles a).hidden = []) :
    hiddenTotal s' = hiddenTotal st := by
  obtain ⟨-, a₀, hp2, hs⟩ := step_tabToFound_inv h
  rw [hp2] at hpa
  injection hpa with haa
  rw [haa] at hs
  rw [hs]
  refine hiddenTotal_congr ?_
  intro a'
  show (if a' = a then Pile.afterRunRemoved (st.piles a) (chop (st.piles a).faceUp)
      else st.piles a').hidden = (st.piles a').hidden
  by_cases hae : a' = a
  · rw [hae, ite_eq_left rfl]
    rcases hnorev with hchop | hhd
    · rcases afterRunRemoved_hidden (st.piles a) (chop (st.piles a).faceUp)
          with ⟨-, hhe⟩ | ⟨he, -, -⟩ | ⟨he, -, -⟩
      · rw [hhe]
      · exact absurd he hchop
      · exact absurd he hchop
    · rcases afterRunRemoved_hidden (st.piles a) (chop (st.piles a).faceUp)
          with ⟨-, hhe⟩ | ⟨-, -, hhe2⟩ | ⟨-, hhne2, -⟩
      · rw [hhe]
      · rw [hhe2]
      · exact absurd hhd hhne2
  · rw [ite_eq_right hae]

/-! ## The constructive undos -/

/-- The pile-top search's sound reading: a located pile's face-up
run is nonempty and really ends at the searched card. -/
theorem pileOfTop_top {st : State} {z : Card} {k : Anchor}
    (h : st.pileOfTop z = some k) :
    (st.piles k).faceUp ≠ [] ∧ lastOf (st.piles k).faceUp = some z := by
  have hd := firstWhere_sound (p := fun a => decide (st.topOf a = some z)) h
  have htop : lastOf (st.piles k).faceUp = some z := of_decide_eq_true hd
  constructor
  · intro hc
    rw [hc] at htop
    exact absurd htop (by simp [lastOf])
  · exact htop

/-- The pile-level round trip of a card-on-card placement: removing
the just-appended top card — the seat's face-up run is nonempty by
the search's own soundness, so the removal takes the non-reveal
branch — restores the pile exactly. -/
private theorem putCard_inr_roundtrip (p : Pile) (c : Card) (hf : p.faceUp ≠ []) :
    Pile.afterRunRemoved { p with faceUp := p.faceUp ++ [c] } (chop (p.faceUp ++ [c])) = p := by
  rw [chop_snoc]
  cases hp : p.faceUp with
  | nil => exact absurd hp hf
  | cons x xs =>
      show ({ p with faceUp := x :: xs } : Pile) = p
      exact Pile.ext rfl hp.symm

/-- A placement onto an empty seat, written as one state update
(`putCard`'s inl case, as a state equality for the undo
assemblies). -/
private theorem putCard_inl_eq_setPile {st : State} {c : Card} {a : Anchor} :
    st.putCard c (Sum.inl a) =
      { st with piles := fun a' => if a' = a then ⟨[], [c]⟩ else st.piles a' } := by
  show (st.setPile a ⟨[], [c]⟩) = _
  rfl

/-- A placement onto a located card base, written as one state
update (`putCard`'s inr case, as a state equality for the undo
assemblies). -/
private theorem putCard_inr_eq_setPile {st : State} {c : Card} {z : Card} {k : Anchor}
    (hz : st.pileOfTop z = some k) :
    st.putCard c (Sum.inr z) =
      { st with piles := fun a' =>
          if a' = k then { st.piles k with faceUp := (st.piles k).faceUp ++ [c] }
          else st.piles a' } := by
  simp only [State.putCard, hz]
  rfl

/-- The state-level round trip behind `foundToTab_undo`: a
successful `.foundToTab` whose placed card is located by the
successor's pile-top search at the very seat the placement wrote,
whose search seat restores under the run removal while every other
pile and the whole draw zone are untouched, is undone by
`.tabToFound c` of the same card. -/
private theorem foundToTab_rtp {st : State} {c : Card} {b : Base} {s₁ : State} {k : Anchor}
    (hstep : State.step st (Move.foundToTab c b) = some s₁)
    (hidx : (chop (st.found c.suit)).length = c.rank.toIdx)
    (hfound : s₁.found c.suit = chop (st.found c.suit))
    (hotherfound : ∀ σ, σ ≠ c.suit → s₁.found σ = st.found σ)
    (hsearch : s₁.pileOfTop c = some k)
    (hkrest : Pile.afterRunRemoved (s₁.piles k) (chop (s₁.piles k).faceUp) = st.piles k)
    (hzkeep : ∀ a', a' ≠ k → s₁.piles a' = st.piles a')
    (hkeep : s₁.stock = st.stock ∧ s₁.waste = st.waste ∧ s₁.drawStep = st.drawStep) :
    reversibleAtW st (Move.foundToTab c b) := by
  obtain ⟨c', htop, hc'c, -, hs⟩ := step_foundToTab_inv hstep
  have hF : st.found c.suit = chop (st.found c.suit) ++ [c] := by
    have h2 : st.foundTop c.suit = some c := by rw [htop, hc'c]
    exact lastOf_chop h2
  have hnextup : s₁.nextUp c = true := by
    show decide (c.rank.toIdx = (s₁.found c.suit).length) = true
    rw [hfound, hidx]
    exact decide_eq_true rfl
  refine ⟨s₁, [Move.tabToFound c], hstep, ?_⟩
  have hstep2 : State.step s₁ (Move.tabToFound c) = some st := by
    show (if s₁.nextUp c = true then
        (match s₁.pileOfTop c with
        | none => none
        | some a =>
            (some { s₁.setFound c.suit (s₁.found c.suit ++ [c]) with
                     piles := fun a' =>
                       if a' = a then Pile.afterRunRemoved (s₁.piles a) (chop (s₁.piles a).faceUp)
                       else s₁.piles a' } : Option State))
        else none) = some st
    rw [hnextup, hsearch]
    refine congrArg some (?_ :
      { s₁.setFound c.suit (s₁.found c.suit ++ [c]) with
        piles := fun a' =>
          if a' = k then Pile.afterRunRemoved (s₁.piles k) (chop (s₁.piles k).faceUp)
          else s₁.piles a' } = st)
    refine State.ext (funext fun σ => ?_) (funext fun a' => ?_) ?_ ?_ ?_
    · show (if σ = c.suit then s₁.found c.suit ++ [c] else s₁.found σ) = st.found σ
      by_cases hσ : σ = c.suit
      · rw [hσ, ite_eq_left rfl, hfound, ← hF]
      · rw [ite_eq_right hσ]
        exact hotherfound σ hσ
    · show (if a' = k then Pile.afterRunRemoved (s₁.piles k) (chop (s₁.piles k).faceUp)
          else s₁.piles a') = st.piles a'
      by_cases ha' : a' = k
      · rw [ha', ite_eq_left rfl]
        exact hkrest
      · rw [ite_eq_right ha']
        exact hzkeep a' ha'
    · show (s₁.setFound c.suit (s₁.found c.suit ++ [c])).stock = st.stock
      rw [setFound_stock]
      exact hkeep.1
    · show (s₁.setFound c.suit (s₁.found c.suit ++ [c])).waste = st.waste
      rw [setFound_waste]
      exact hkeep.2.1
    · show (s₁.setFound c.suit (s₁.found c.suit ++ [c])).drawStep = st.drawStep
      rw [setFound_drawStep]
      exact hkeep.2.2
  simp only [State.run, hstep2]

/-- **The `.foundToTab` undo, witness form (primary).**  A
successful `Move.foundToTab c b` is undone by `Move.tabToFound c`
of the same card, returning to the origin in one move.

The premises are local (no `State.WF`) and each excludes a genuine
wild-state corner:

* `hnext` — nothing in the step ties the foundation's length to
  the card's rank index, so the undo's own `nextUp` guard can fail
  at a miscounted wild foundation (a king stacked on a one-card
  foundation of the wrong suit length cannot re-ascend).  The
  premise is the successor's next-up arithmetic exactly.
* `hsearch` + `hseat` — the successor's `pileOfTop` search
  consults all seven piles, and a wild state can hold a second
  copy of `c` on an *earlier* pile, so the undo move would aim at
  the wrong seat; together the two premises pin the search to the
  very seat the placement wrote (the step gives it: the empty seat
  for `b = .inl k`, the located base pile for `b = .inr z`). -/
theorem foundToTab_undo {st : State} {c : Card} {b : Base} {s₁ : State} {k : Anchor}
    (h : State.step st (Move.foundToTab c b) = some s₁)
    (hnext : (chop (st.found c.suit)).length = c.rank.toIdx)
    (hsearch : s₁.pileOfTop c = some k)
    (hseat : b = Sum.inl k ∨ ∃ z, b = Sum.inr z ∧ st.pileOfTop z = some k) :
    reversibleAtW st (Move.foundToTab c b) := by
  obtain ⟨c', htop, hc'c, hcp, hs⟩ := step_foundToTab_inv h
  have hkeep : s₁.stock = st.stock ∧ s₁.waste = st.waste ∧ s₁.drawStep = st.drawStep := by
    refine ⟨?_, ?_, ?_⟩
    · rw [hs, putCard_stock, setFound_stock]
    · rw [hs, putCard_waste, setFound_waste]
    · rw [hs, putCard_drawStep, setFound_drawStep]
  have hs₁found : s₁.found c.suit = chop (st.found c.suit) := by
    rw [hs, putCard_found]
    exact setFound_found_self st c.suit _
  have hs₁other : ∀ σ, σ ≠ c.suit → s₁.found σ = st.found σ := by
    intro σ hσ
    rw [hs, putCard_found]
    exact setFound_found_ne st c.suit _ σ hσ
  rcases hseat with hb | ⟨z, hb, hz⟩
  · subst hb
    obtain ⟨hemp, -⟩ := canPlace_inl hcp
    obtain ⟨hhd, hfu⟩ := (Pile.isEmpty_eq _).mp hemp
    have hPk : s₁.piles k = ⟨[], [c]⟩ := by
      rw [hs]
      simp only [putCard_piles_inl]
      rw [ite_true]
    have hzkeep : ∀ a', a' ≠ k → s₁.piles a' = st.piles a' := by
      intro a' hne
      rw [hs]
      simp only [putCard_piles_inl]
      rw [ite_eq_right hne, setFound_piles]
    exact foundToTab_rtp h hnext hs₁found hs₁other hsearch
      (by
        rw [hPk]
        show (⟨[], []⟩ : Pile) = st.piles k
        exact Pile.ext hhd.symm hfu.symm)
      hzkeep hkeep
  · subst hb
    obtain ⟨hfne, -⟩ := pileOfTop_top hz
    have hz' : (st.setFound c.suit (chop (st.found c.suit))).pileOfTop z = some k := hz
    have hPk : s₁.piles k = { st.piles k with faceUp := (st.piles k).faceUp ++ [c] } := by
      rw [hs]
      simp only [putCard_piles_inr _ _ _ _ hz']
      rw [setFound_piles, ite_true]
    have hzkeep : ∀ a', a' ≠ k → s₁.piles a' = st.piles a' := by
      intro a' hne
      rw [hs]
      simp only [putCard_piles_inr _ _ _ _ hz']
      rw [ite_eq_right hne, setFound_piles]
    exact foundToTab_rtp h hnext hs₁found hs₁other hsearch
      (by
        rw [hPk]
        exact putCard_inr_roundtrip _ c hfne)
      hzkeep hkeep

/-- The negative form of the `.foundToTab` undo.  Witness form:
`foundToTab_undo`. -/
theorem foundToTab_reversible {st : State} {c : Card} {b : Base} {s₁ : State} {k : Anchor}
    (h : State.step st (Move.foundToTab c b) = some s₁)
    (hnext : (chop (st.found c.suit)).length = c.rank.toIdx)
    (hsearch : s₁.pileOfTop c = some k)
    (hseat : b = Sum.inl k ∨ ∃ z, b = Sum.inr z ∧ st.pileOfTop z = some k) :
    reversibleAt st (Move.foundToTab c b) :=
  reversibleAt_of_W (foundToTab_undo h hnext hsearch hseat)

/-- The pile-level no-reveal-empty round trip: a pile with no
hidden cards and an emptied face-up run stays exactly the empty
pile through the removal. -/
private theorem afterRunRemoved_empty_eq : ∀ (p : Pile), p.hidden = [] →
    Pile.afterRunRemoved p ([] : List Card) = ⟨[], []⟩
  | ⟨[], pf⟩, _ => rfl
  | ⟨x :: xs, pf⟩, hhd => absurd hhd (by simp)

/-- **The under-seat `.tabToFound` undo, witness form (primary).**
A successful no-reveal `.tabToFound` whose source pile keeps a
face-up card below the moved one (`hz` pins that card, `z`) is
undone by `.foundToTab c (Sum.inr z)` onto `z`'s pile: the
foundation split puts `c` back on top, and the removal kept the
face-up run below intact.

The premises are local (no `State.WF`) and each excludes a genuine
wild-state corner:

* `hsit` — `canSitOn c z` does *not* follow from the step: a wild
  origin may stack `c` directly on `z` against the fit rules, and
  then the undo move's own guard fails.
* `hsearch` — the successor's base search consults all seven
  piles, and a wild state can hold another pile topping `z`
  earlier in the search order, sending the placement astray;
  the premise pins the search to the source seat. -/
theorem tabToFound_undo_under {st : State} {c : Card} {a : Anchor} {z : Card} {s₁ : State}
    (hstep : State.step st (Move.tabToFound c) = some s₁)
    (hpa : st.pileOfTop c = some a)
    (hz : lastOf (chop (st.piles a).faceUp) = some z)
    (hsit : canSitOn c z = true)
    (hsearch : s₁.pileOfTop z = some a) :
    reversibleAtW st (Move.tabToFound c) := by
  obtain ⟨-, a₀, hpa₀, hs₁⟩ := step_tabToFound_inv hstep
  rw [hpa] at hpa₀
  injection hpa₀ with haa
  subst haa
  obtain ⟨-, hlastc⟩ := pileOfTop_top hpa
  have hfull : (st.piles a).faceUp = chop (st.piles a).faceUp ++ [c] := lastOf_chop hlastc
  have hs₁found : s₁.found c.suit = st.found c.suit ++ [c] := by
    rw [hs₁]
    exact setFound_found_self st c.suit _
  have hs₁other : ∀ σ, σ ≠ c.suit → s₁.found σ = st.found σ := by
    intro σ hσ
    rw [hs₁]
    show (if σ = c.suit then st.found c.suit ++ [c] else st.found σ) = st.found σ
    rw [ite_eq_right hσ]
  have hft : s₁.foundTop c.suit = some c := by
    show lastOf (s₁.found c.suit) = some c
    rw [hs₁found]
    exact lastOf_snoc _ c
  have hcp : s₁.canPlace c (Sum.inr z) = true := by
    simp only [State.canPlace, hsearch]
    exact hsit
  refine ⟨s₁, [Move.foundToTab c (Sum.inr z)], hstep, ?_⟩
  have hstep2 : State.step s₁ (Move.foundToTab c (Sum.inr z)) = some st := by
    simp only [State.step, hft]
    rw [hcp]
    refine congrArg some (?_ :
      (s₁.setFound c.suit (chop (s₁.found c.suit))).putCard c (Sum.inr z) = st)
    have hz'' : (s₁.setFound c.suit (chop (s₁.found c.suit))).pileOfTop z = some a := hsearch
    rw [putCard_inr_eq_setPile hz'']
    refine State.ext (funext fun σ => ?_) (funext fun a'' => ?_) ?_ ?_ ?_
    · show (if σ = c.suit then chop (s₁.found c.suit) else s₁.found σ) = st.found σ
      by_cases hσ : σ = c.suit
      · rw [hσ, ite_eq_left rfl, hs₁found, chop_snoc]
      · rw [ite_eq_right hσ]
        exact hs₁other σ hσ
    · show (if a'' = a then
          { (s₁.setFound c.suit (chop (s₁.found c.suit))).piles a with
            faceUp := ((s₁.setFound c.suit (chop (s₁.found c.suit))).piles a).faceUp ++ [c] }
          else (s₁.setFound c.suit (chop (s₁.found c.suit))).piles a'') = st.piles a''
      have hQeq : (s₁.setFound c.suit (chop (s₁.found c.suit))).piles = s₁.piles := rfl
      rw [hQeq]
      by_cases ha'' : a'' = a
      · rw [ha'', ite_eq_left rfl]
        have hpla : s₁.piles a =
            Pile.afterRunRemoved (st.piles a) (chop (st.piles a).faceUp) := by
          rw [hs₁]
          show (if a = a then
              Pile.afterRunRemoved (st.piles a) (chop (st.piles a).faceUp)
              else st.piles a) = _
          rw [ite_eq_left rfl]
        rw [hpla]
        cases hc : chop (st.piles a).faceUp with
        | nil =>
            rw [hc] at hz
            exact absurd hz (by simp [lastOf])
        | cons y ys =>
            rw [hc] at hfull
            show (⟨(st.piles a).hidden, (y :: ys) ++ [c]⟩ : Pile) = st.piles a
            exact Pile.ext rfl hfull.symm
      · rw [ite_eq_right ha'']
        rw [hs₁]
        show (if a'' = a then
            Pile.afterRunRemoved (st.piles a) (chop (st.piles a).faceUp)
            else st.piles a'') = st.piles a''
        rw [ite_eq_right ha'']
    · show s₁.stock = st.stock
      rw [hs₁]
      rfl
    · show s₁.waste = st.waste
      rw [hs₁]
      rfl
    · show s₁.drawStep = st.drawStep
      rw [hs₁]
      rfl
  simp only [State.run, hstep2]

/-- The negative form of the under-seat `.tabToFound` undo.
Witness form: `tabToFound_undo_under`. -/
theorem tabToFound_reversible_under {st : State} {c : Card} {a : Anchor} {z : Card} {s₁ : State}
    (hstep : State.step st (Move.tabToFound c) = some s₁)
    (hpa : st.pileOfTop c = some a)
    (hz : lastOf (chop (st.piles a).faceUp) = some z)
    (hsit : canSitOn c z = true)
    (hsearch : s₁.pileOfTop z = some a) :
    reversibleAt st (Move.tabToFound c) :=
  reversibleAt_of_W (tabToFound_undo_under hstep hpa hz hsit hsearch)

/-- **The bare `.tabToFound` undo, witness form (primary).**  A
successful no-reveal `.tabToFound` whose source pile empties
completely (`hchop` : the chop is nil, `hhidden` : no hidden
cards — the afterRunRemoved trichotomy's no-reveal second leg) is
undone by `.foundToTab c (Sum.inl a)` onto the now-empty original
seat.  The `hking` premise is genuine: an empty-seat placement
demands a king, and at a wild state nothing ties the moved card's
rank to the seat it left. -/
theorem tabToFound_undo_bare {st : State} {c : Card} {a : Anchor} {s₁ : State}
    (hstep : State.step st (Move.tabToFound c) = some s₁)
    (hpa : st.pileOfTop c = some a)
    (hchop : chop (st.piles a).faceUp = [])
    (hhidden : (st.piles a).hidden = [])
    (hking : c.rank = Rank.king) :
    reversibleAtW st (Move.tabToFound c) := by
  obtain ⟨-, a₀, hpa₀, hs₁⟩ := step_tabToFound_inv hstep
  rw [hpa] at hpa₀
  injection hpa₀ with haa
  subst haa
  have hs₁found : s₁.found c.suit = st.found c.suit ++ [c] := by
    rw [hs₁]
    exact setFound_found_self st c.suit _
  have hs₁other : ∀ σ, σ ≠ c.suit → s₁.found σ = st.found σ := by
    intro σ hσ
    rw [hs₁]
    show (if σ = c.suit then st.found c.suit ++ [c] else st.found σ) = st.found σ
    rw [ite_eq_right hσ]
  have hft : s₁.foundTop c.suit = some c := by
    show lastOf (s₁.found c.suit) = some c
    rw [hs₁found]
    exact lastOf_snoc _ c
  have hface : (st.piles a).faceUp = [c] := by
    obtain ⟨-, hlastc⟩ := pileOfTop_top hpa
    have hc0 : (st.piles a).faceUp = chop (st.piles a).faceUp ++ [c] := lastOf_chop hlastc
    rw [hchop, List.nil_append] at hc0
    exact hc0
  have hpla : s₁.piles a = ⟨[], []⟩ := by
    rw [hs₁]
    show (if a = a then
        Pile.afterRunRemoved (st.piles a) (chop (st.piles a).faceUp)
        else st.piles a) = _
    rw [ite_eq_left rfl, hchop]
    exact afterRunRemoved_empty_eq _ hhidden
  have hcp : s₁.canPlace c (Sum.inl a) = true := by
    show ((s₁.piles a).isEmpty && decide (c.rank = Rank.king)) = true
    rw [hpla, decide_eq_true hking]
    rfl
  refine ⟨s₁, [Move.foundToTab c (Sum.inl a)], hstep, ?_⟩
  have hstep2 : State.step s₁ (Move.foundToTab c (Sum.inl a)) = some st := by
    simp only [State.step, hft]
    rw [hcp]
    refine congrArg some (?_ :
      (s₁.setFound c.suit (chop (s₁.found c.suit))).putCard c (Sum.inl a) = st)
    rw [putCard_inl_eq_setPile]
    refine State.ext (funext fun σ => ?_) (funext fun a'' => ?_) ?_ ?_ ?_
    · show (if σ = c.suit then chop (s₁.found c.suit) else s₁.found σ) = st.found σ
      by_cases hσ : σ = c.suit
      · rw [hσ, ite_eq_left rfl, hs₁found, chop_snoc]
      · rw [ite_eq_right hσ]
        exact hs₁other σ hσ
    · show (if a'' = a then (⟨[], [c]⟩ : Pile)
          else (s₁.setFound c.suit (chop (s₁.found c.suit))).piles a'') = st.piles a''
      by_cases ha'' : a'' = a
      · rw [ha'', ite_eq_left rfl]
        show (⟨[], [c]⟩ : Pile) = ⟨(st.piles a).hidden, (st.piles a).faceUp⟩
        rw [hhidden, hface]
      · rw [ite_eq_right ha'']
        show s₁.piles a'' = st.piles a''
        rw [hs₁]
        show (if a'' = a then
            Pile.afterRunRemoved (st.piles a) (chop (st.piles a).faceUp)
            else st.piles a'') = st.piles a''
        rw [ite_eq_right ha'']
    · show s₁.stock = st.stock
      rw [hs₁]
      rfl
    · show s₁.waste = st.waste
      rw [hs₁]
      rfl
    · show s₁.drawStep = st.drawStep
      rw [hs₁]
      rfl
  simp only [State.run, hstep2]

/-- The negative form of the bare `.tabToFound` undo.  Witness
form: `tabToFound_undo_bare`. -/
theorem tabToFound_reversible_bare {st : State} {c : Card} {a : Anchor} {s₁ : State}
    (hstep : State.step st (Move.tabToFound c) = some s₁)
    (hpa : st.pileOfTop c = some a)
    (hchop : chop (st.piles a).faceUp = [])
    (hhidden : (st.piles a).hidden = [])
    (hking : c.rank = Rank.king) :
    reversibleAt st (Move.tabToFound c) :=
  reversibleAt_of_W (tabToFound_undo_bare hstep hpa hchop hhidden hking)
