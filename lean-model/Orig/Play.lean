import Orig.State

/-!
# The original game — moves

The full physical rule set, with no restrictions: pile-to-pile run
moves are first-class, the reveal is automatic (flipping the newly
exposed card is part of the move that uncovers it, never a move of
its own), and the draw recycles the waste when the stock runs out.

Conventions (standard software Klondike):

* a draw deals up to `drawStep` cards — fewer if the (possibly
  recycled) stock runs short; it never recycles mid-draw;
* only a pile's top card may go to a foundation;
* a face-up card and everything above it move together as a run;
* the waste returns to the stock reversed, so the oldest passed card
  is dealt first after a recycle.
-/

/-- A move of the original game. -/
inductive Move : Type where
  /-- Deal from the stock to the waste, recycling first if the stock
  is empty. -/
  | draw
  /-- The waste top onto its foundation. -/
  | wasteToFound (c : Card)
  /-- The waste top onto the tableau. -/
  | wasteToTab (c : Card) (b : Base)
  /-- A pile top onto its foundation. -/
  | tabToFound (c : Card)
  /-- A foundation top back down onto the tableau. -/
  | foundToTab (c : Card) (b : Base)
  /-- The face-up run headed by `c` onto another pile. -/
  | tabToTab (c : Card) (b : Base)
  deriving DecidableEq

namespace State

/-! ## Placement helpers -/

/-- Put a single card onto base `b` (assumes `State.canPlace`). -/
def putCard (st : State) (c : Card) (b : Base) : State :=
  match b with
  | .inl a => st.setPile a ⟨[], [c]⟩
  | .inr z =>
      match st.pileOfTop z with
      | some k => st.setPile k { st.piles k with faceUp := (st.piles k).faceUp ++ [c] }
      | none => st

/-- Put a run onto base `b` (assumes `State.canPlace` for the run's
head; the run keeps its order, so the moving head lands lowest). -/
def putRun (st : State) (run : List Card) (b : Base) : State :=
  match b with
  | .inl a => st.setPile a ⟨[], run⟩
  | .inr z =>
      match st.pileOfTop z with
      | some k => st.setPile k { st.piles k with faceUp := (st.piles k).faceUp ++ run }
      | none => st

/-! ## The draw -/

/-- Deal up to `k` cards from `l`: the dealt cards, in deal order, and
the rest. -/
def dealUpTo (k : Nat) (l : List Card) : List Card × List Card :=
  match k, l with
  | 0, _ => ([], l)
  | _+1, [] => ([], l)
  | k+1, c :: cs => let r := dealUpTo k cs; (c :: r.1, r.2)

/-- Recycle the waste into the stock, if the stock is empty. -/
def recycle (st : State) : State :=
  match st.stock with
  | [] =>
      match st.waste with
      | [] => st
      | w => { st with stock := w.reverse, waste := [] }
  | _ => st

/-- Deal from a nonempty stock into the waste. -/
def dealStock (st : State) : Option State :=
  match st.stock with
  | [] => none
  | s =>
      let d := dealUpTo st.drawStep s
      some { st with stock := d.2, waste := d.1.reverse ++ st.waste }

/-- Recycle the waste into the stock when the stock is empty, then
deal up to `drawStep` cards. -/
def stepDraw (st : State) : Option State := dealStock st.recycle

/-! ## The step function -/

/-- The deterministic physical move function: `some s'` when `m` is
legal at `st`, `none` otherwise. -/
def step (st : State) (m : Move) : Option State :=
  match m with
  | .draw => st.stepDraw
  | .wasteToFound c =>
      if st.wasteIs c && st.nextUp c then
        match st.waste with
        | _ :: ws => some { st.setFound c.suit (st.found c.suit ++ [c]) with waste := ws }
        | [] => none
      else none
  | .wasteToTab c b =>
      if st.wasteIs c && st.canPlace c b then
        match st.waste with
        | _ :: ws => some { st.putCard c b with waste := ws }
        | [] => none
      else none
  | .tabToFound c =>
      if st.nextUp c then
        match st.pileOfTop c with
        | none => none
        | some a =>
            let p := st.piles a
            some { st.setFound c.suit (st.found c.suit ++ [c]) with
                     piles := fun a' =>
                       if a' = a then Pile.afterRunRemoved p (chop p.faceUp)
                       else st.piles a' }
      else none
  | .foundToTab c b =>
      match st.foundTop c.suit with
      | some c' =>
          if decide (c' = c) && st.canPlace c b then
            some ((st.setFound c.suit (chop (st.found c.suit))).putCard c b)
          else none
      | none => none
  | .tabToTab c b =>
      match st.pileHolding c with
      | none => none
      | some a =>
          if st.canPlace c b then
            match fromCard c (st.piles a).faceUp with
            | [] => none
            | run =>
                let pre := below c (st.piles a).faceUp
                some ((st.setPile a (Pile.afterRunRemoved (st.piles a) pre)).putRun run b)
          else none

/-- Is `m` a legal move at `st`? -/
def legal (st : State) (m : Move) : Bool := (State.step st m).isSome

/-- Playing a sequence of moves; `some st` at the empty play. -/
def run (st : State) : List Move → Option State
  | [] => some st
  | m :: ms =>
      match State.step st m with
      | some st' => State.run st' ms
      | none => none

/-- Decomposition of a `run` step for proofs. -/
theorem run_cons {st : State} {m : Move} {rest : List Move} {w : State}
    (h : st.run (m :: rest) = some w) :
    ∃ s₁, State.step st m = some s₁ ∧ s₁.run rest = some w := by
  cases hstep : State.step st m with
  | none =>
      rw [show st.run (m :: rest) = none by simp only [State.run, hstep]] at h
      exact absurd h (by simp)
  | some s₁ =>
      refine ⟨s₁, rfl, ?_⟩
      simpa only [State.run, hstep] using h

end State

/-- A single move runs by stepping it (the run glue beside
`State.run_cons`; landed at the dedup-collapse wave — the private
copies in `Orig/Shuttle.lean` and `Orig/Canonical.lean` cite this
home). -/
theorem run_one {st : State} {m : Move} {s : State}
    (h : State.step st m = some s) : st.run [m] = some s := by
  show (match State.step st m with
    | some st' => State.run st' []
    | none => none) = some s
  rw [h]
  rfl

/-! ## The first-passage split

The §12.1-family first-passage extraction, ported into this run
dialect from the `Klondike` side: `climb_firstPassage` there (see
`Klondike/Kills.lean`, the specialized heights-crossing — the first
play position where the climbing suit's height passes the frontier
rank) despecialized to an arbitrary decidable state predicate, with
the family's run apparatus (the `Klondike/Progress.lean` run-split
readers) restated over `State.run`/`State.run_cons`.

A successful play whose start fails `P` and whose end satisfies `P`
crosses the boundary at a first position: a prefix that lands on a
still-failing state, then ONE move onto a passing state — and every
state the prefix visits also fails `P` (first-passage minimality,
the generic replacement for `climb_firstPassage`'s carried
pre-passage invariants).

The consumers (both in `Orig/Dominance.lean`): the (N) win-lift's
rung-occurs extraction (under `ground_lifted_win`: the winning
play's first `c`-founded state is entered by `tabToFound c` — the
waste entry is then excluded by conservation) and the (C) residue
`draw1_worry_spread_residue` (the restack `tabToFound x` located
while the window is open).  The Dominance-internal mirrors of these
rows (`ground_run_split`, `run_append_split1`) stay private — their
dedup into this public home is a harvest-wave call. -/

/-- A successful run through `A ++ B` passes through the state `A`
lands on — the append-decomposition reader of the run dialect. -/
theorem run_append_split : ∀ (st : State) (A B : List Move) (w : State),
    st.run (A ++ B) = some w → ∃ z, st.run A = some z ∧ z.run B = some w := by
  intro st A
  induction A generalizing st with
  | nil =>
      intro B w h
      exact ⟨st, rfl, h⟩
  | cons m rest ih =>
      intro B w h
      rw [List.cons_append] at h
      obtain ⟨s₁, hstep, hrest⟩ := State.run_cons h
      obtain ⟨z, hA, hB⟩ := ih s₁ B w hrest
      refine ⟨z, ?_, hB⟩
      show (match State.step st m with
        | some st' => State.run st' rest
        | none => none) = some z
      rw [hstep]
      exact hA

/-- **The first-passage split**: a successful play whose start fails
`P` and whose end satisfies `P` crosses at a first position — a
prefix landing on a failing state, one crossing move onto a passing
state, and every state the prefix visits also fails `P` (each
splitting prefix lands on a failing state). -/
theorem run_firstPassage_split {P : State → Bool} :
    ∀ (st : State) (play : List Move) (w : State),
    st.run play = some w → P st = false → P w = true →
    ∃ π₁ m π₂ τ σ, play = π₁ ++ m :: π₂ ∧ st.run π₁ = some τ ∧
      State.step τ m = some σ ∧ P σ = true ∧
      (∀ pre post, π₁ = pre ++ post →
        ∀ u, st.run pre = some u → P u = false) := by
  intro st play
  induction play generalizing st with
  | nil =>
      intro w hrun hstart hend
      have h' : (some st : Option State) = some w := hrun
      have hsw : st = w := Option.some.inj h'
      rw [← hsw] at hend
      rw [hstart] at hend
      exact absurd hend (by simp)
  | cons m rest ih =>
      intro w hrun hstart hend
      obtain ⟨s₁, hstep, hrest⟩ := State.run_cons hrun
      cases hp : P s₁ with
      | true =>
          refine ⟨[], m, rest, st, s₁, rfl, rfl, hstep, hp, ?_⟩
          intro pre post hsplit u hrunpre
          cases pre with
          | nil =>
              have h' : (some st : Option State) = some u := hrunpre
              have hsu : st = u := Option.some.inj h'
              rw [← hsu]
              exact hstart
          | cons x t =>
              exact absurd hsplit.symm (by simp)
      | false =>
          obtain ⟨π₁, m', π₂, τ, σ, hdec, hrun₁, hstep', hpass, hmin⟩ :=
            ih s₁ w hrest hp hend
          refine ⟨m :: π₁, m', π₂, τ, σ, by
            rw [List.cons_append]; exact congrArg (m :: ·) hdec, ?_,
            hstep', hpass, ?_⟩
          · show (match State.step st m with
              | some st' => State.run st' π₁
              | none => none) = some τ
            rw [hstep]
            exact hrun₁
          · intro pre post hsplit u hrunpre
            cases pre with
            | nil =>
                have h' : (some st : Option State) = some u := hrunpre
                have hsu : st = u := Option.some.inj h'
                rw [← hsu]
                exact hstart
            | cons x t =>
                rw [List.cons_append] at hsplit
                injection hsplit with hxm htl
                have h3 : st.run (m :: t) = some u := by
                  rw [← hxm] at hrunpre
                  exact hrunpre
                have h2 : s₁.run t = some u := by
                  obtain ⟨s₁', hstep', htail⟩ := State.run_cons h3
                  have hs1 : s₁' = s₁ := Option.some.inj (hstep'.symm.trans hstep)
                  rw [hs1] at htail
                  exact htail
                exact hmin t post htl u h2

/-! ## The step branch readers

The raw branch unfoldings of `State.step`, landed beside the def at
the dedup-collapse wave so the exchange chapters (`Orig/TwinExchangeBoth`,
`Orig/MergeWalls`) and the guard-spliced forms below cite one home. -/

/-- The `wasteToTab` branch, read raw. -/
theorem step_wasteToTab_eq (st : State) (c : Card) (b : Base) :
    st.step (Move.wasteToTab c b) =
      (if st.wasteIs c && st.canPlace c b then
        match st.waste with
        | _ :: ws => some { st.putCard c b with waste := ws }
        | [] => none
      else none) := rfl

/-- The `tabToFound` branch, read raw. -/
theorem step_tabToFound_eq (st : State) (c : Card) :
    st.step (Move.tabToFound c) =
      (if st.nextUp c then
        match st.pileOfTop c with
        | none => none
        | some a =>
            some { st.setFound c.suit (st.found c.suit ++ [c]) with
                     piles := fun a' =>
                       if a' = a then Pile.afterRunRemoved (st.piles a) (chop (st.piles a).faceUp)
                       else st.piles a' }
      else none) := rfl

/-- The `foundToTab` branch, read raw. -/
theorem step_foundToTab_eq (st : State) (c : Card) (b : Base) :
    st.step (Move.foundToTab c b) =
      (match st.foundTop c.suit with
       | some c' =>
           if decide (c' = c) && st.canPlace c b then
             some ((st.setFound c.suit (chop (st.found c.suit))).putCard c b)
           else none
       | none => none) := rfl

/-- The `tabToTab` branch, read raw. -/
theorem step_tabToTab_eq (st : State) (c : Card) (b : Base) :
    st.step (Move.tabToTab c b) =
      (match st.pileHolding c with
       | none => none
       | some a =>
           if st.canPlace c b then
             match fromCard c (st.piles a).faceUp with
             | [] => none
             | run =>
                 some ((st.setPile a (Pile.afterRunRemoved (st.piles a)
                   (below c (st.piles a).faceUp))).putRun run b)
           else none) := rfl

/-! ## The guard-spliced step forms

With the rung and the search's answer in hand, the step is the
literal splice — the convenience forms the shuttle/dominance
chapters lean on (landed beside the raw rows; the former private
copies in `Orig/Shuttle.lean` and `Orig/Dominance.lean` cite this
home). -/

/-- The `tabToFound` computation at a located rung: the step is the
splice. -/
theorem step_tabToFound_splice {st : State} {c : Card} {k : Anchor}
    (hnext : st.nextUp c = true) (hpo : st.pileOfTop c = some k) :
    State.step st (Move.tabToFound c) =
      some { st.setFound c.suit (st.found c.suit ++ [c]) with
             piles := fun a' => if a' = k then
                 Pile.afterRunRemoved (st.piles k) (chop (st.piles k).faceUp)
               else st.piles a' } := by
  show (if st.nextUp c then
      match st.pileOfTop c with
      | none => none
      | some a => some { st.setFound c.suit (st.found c.suit ++ [c]) with
          piles := fun a' => if a' = a then
              Pile.afterRunRemoved (st.piles a) (chop (st.piles a).faceUp)
            else st.piles a' }
      else none) = _
  rw [ite_eq_left hnext, hpo]

/-- The `foundToTab` computation at the known top and guard: the step
is the chop-back and place (the split-arg fires-grade form). -/
theorem step_foundToTab_splice {st : State} {c : Card} {b : Base}
    (htop : st.foundTop c.suit = some c) (hcp : st.canPlace c b = true) :
    State.step st (Move.foundToTab c b) =
      some ((st.setFound c.suit (chop (st.found c.suit))).putCard c b) := by
  show (match st.foundTop c.suit with
      | some c' =>
          if decide (c' = c) && st.canPlace c b then
            some ((st.setFound c.suit (chop (st.found c.suit))).putCard c b)
          else none
      | none => none) = _
  rw [htop]
  show (if decide (c = c) && st.canPlace c b then
      some ((st.setFound c.suit (chop (st.found c.suit))).putCard c b)
    else none) = _
  rw [ite_eq_left (by
    rw [show decide (c = c) = true from decide_eq_true rfl, hcp]
    rfl)]

/-! ## Update readers

The located readers for `State.putCard` / `State.putRun`, and the
found-passthrough trio (`setPile_found` in `Orig/State.lean`,
`putCard_inl_found` / `putCard_inr_found` here) — staged for the
`foundToTab` transport row, and dedup-marked against the private
copies in the exchange chapters. -/

/-- `putCard` to an empty seat writes no foundation. -/
theorem putCard_inl_found {st : State} (c : Card) (a : Anchor) :
    (st.putCard c (Sum.inl a)).found = st.found := rfl

/-- `putCard`, wherever it lands, writes no foundation. -/
theorem putCard_inr_found {st : State} (c z : Card) :
    (st.putCard c (Sum.inr z)).found = st.found := by
  show (match st.pileOfTop z with
    | some k => st.setPile k { st.piles k with faceUp := (st.piles k).faceUp ++ [c] }
    | none => st).found = st.found
  cases h : st.pileOfTop z <;> rfl

/-- The located `putCard`: the top-directed landing appends the card
at the located pile. -/
theorem putCard_inr_eq {st : State} {c z : Card} {k : Anchor}
    (h : st.pileOfTop z = some k) :
    st.putCard c (Sum.inr z) =
    st.setPile k { st.piles k with faceUp := (st.piles k).faceUp ++ [c] } := by
  rw [show st.putCard c (Sum.inr z) =
    st.setPile k { st.piles k with faceUp := (st.piles k).faceUp ++ [c] } from by
    simp only [State.putCard, h]]

/-- `putCard` onto an empty seat is the singleton `setPile`. -/
theorem putCard_eq_inl (st : State) (c : Card) (a : Anchor) :
    st.putCard c (Sum.inl a) = st.setPile a ⟨[], [c]⟩ := rfl

/-- `putRun` onto an empty seat is the run record. -/
theorem putRun_eq_inl (st : State) (run : List Card) (a : Anchor) :
    st.putRun run (Sum.inl a) = st.setPile a ⟨[], run⟩ := rfl

/-- The located `putRun`: the top-directed landing appends the run at
the located pile. -/
theorem putRun_inr_eq {st : State} {run : List Card} {z : Card} {k : Anchor}
    (h : st.pileOfTop z = some k) :
    st.putRun run (Sum.inr z) =
    st.setPile k { st.piles k with faceUp := (st.piles k).faceUp ++ run } := by
  rw [show st.putRun run (Sum.inr z) =
    st.setPile k { st.piles k with faceUp := (st.piles k).faceUp ++ run } from by
    simp only [State.putRun, h]]

/-- A run landing with no search hit changes nothing — the `none`
companion of `putRun_inr_eq` (landed at the dedup-collapse wave; the
private copies in `Orig/Classify.lean` and `Orig/EdgeLabel.lean`'s
pointwise row below cite this home). -/
theorem putRun_inr_none {st : State} {run : List Card} {z : Card}
    (hz : st.pileOfTop z = none) : st.putRun run (Sum.inr z) = st := by
  simp only [State.putRun, hz]

/-- The pointwise-pile reading of `putRun_inr_none`. -/
theorem putRun_inr_none_piles {st : State} {run : List Card} {z : Card}
    (hz : st.pileOfTop z = none) (a' : Anchor) :
    (st.putRun run (Sum.inr z)).piles a' = st.piles a' :=
  congrArg (fun s => s.piles a') (putRun_inr_none hz)

/-! ## The draw readers

The `recycle` / `dealStock` / `dealUpTo` / draw-unfold readers,
landed beside their defs — formerly identical private copies in
`Orig/Phase.lean` and `Orig/Reach.lean` (plus `Progress`'s
`recycle_keep`), dedup-marked since the v2 era. -/

/-- An empty-board recycle is the identity. -/
theorem recycle_allEmpty (st : State) (h1 : st.stock = [])
    (h2 : st.waste = []) : State.recycle st = st := by
  simp only [State.recycle, h1, h2]

/-- A recycle at the end, with waste present, reverses the waste into
the stock. -/
theorem recycle_nil (st : State) (h1 : st.stock = [])
    (h2 : st.waste ≠ []) :
    State.recycle st = { st with stock := st.waste.reverse, waste := [] } := by
  obtain ⟨x, t, hcon⟩ := list_cons_of_ne_nil h2
  simp only [State.recycle, h1, hcon]

/-- A recycle with stock present is the identity. -/
theorem recycle_keep (st : State) (h : st.stock ≠ []) :
    State.recycle st = st := by
  obtain ⟨c, t, hcon⟩ := list_cons_of_ne_nil h
  simp only [State.recycle, hcon]

/-- Dealing from an empty stock fails. -/
theorem dealStock_nil (st : State) (h : st.stock = []) :
    State.dealStock st = none := by
  simp only [State.dealStock, h]

/-- Dealing from a nonempty stock has exactly the recorded shape: the
dealt cards reversed onto the waste, the remainder kept as the stock. -/
theorem dealStock_eq_of_ne_nil (st : State) (h : st.stock ≠ []) :
    State.dealStock st = some
      { st with stock := (State.dealUpTo st.drawStep st.stock).2, waste := (State.dealUpTo st.drawStep st.stock).1.reverse ++ st.waste } := by
  obtain ⟨c, t, hcon⟩ := list_cons_of_ne_nil h
  simp only [State.dealStock, hcon]

/-- `putCard` keeps the found, the stock, the waste, and the draw
step verbatim. -/
theorem putCard_keep {st : State} {c : Card} {b : Base} :
    (st.putCard c b).found = st.found ∧ (st.putCard c b).stock = st.stock ∧
      (st.putCard c b).waste = st.waste ∧ (st.putCard c b).drawStep = st.drawStep := by
  cases b with
  | inl a => exact ⟨rfl, rfl, rfl, rfl⟩
  | inr z =>
      simp only [State.putCard]
      split <;> exact ⟨rfl, rfl, rfl, rfl⟩

/-- `putRun` keeps the same four fields verbatim — the run form of
`putCard_keep` (landed at the dedup-collapse wave; the private copies
in `Orig/Phase.lean`, `Orig/TwinExchangeBoth.lean`, and
`Orig/Dominance.lean`'s three-field port at its wave cite this home;
the Dominance port keeps only stock/waste/drawStep). -/
theorem putRun_keep {st : State} {run : List Card} {b : Base} :
    (st.putRun run b).found = st.found ∧ (st.putRun run b).stock = st.stock ∧
      (st.putRun run b).waste = st.waste ∧ (st.putRun run b).drawStep = st.drawStep := by
  cases b with
  | inl a => exact ⟨rfl, rfl, rfl, rfl⟩
  | inr z =>
      simp only [State.putRun]
      split <;> exact ⟨rfl, rfl, rfl, rfl⟩

/-- The exact split of `dealUpTo` into take and drop: dealing `k` cards
from the front is taking `k` (clipped by `List.take` itself) and
dropping `k`. -/
theorem dealUpTo_eq_take_drop (k : Nat) : ∀ (l : List Card),
    State.dealUpTo k l = (l.take k, l.drop k) := by
  induction k with
  | zero => intro l; rfl
  | succ k ih =>
      intro l
      cases l with
      | nil => rfl
      | cons c cs =>
          rw [State.dealUpTo, ih cs]
          rfl

/-- One step of the draw cycle, unfolded: after recycling (the identity
unless the stock was empty), the deal happens from a nonempty stock and
has the recorded shape. -/
theorem draw_unfold {x y : State} (hsuc : x.stepDraw = some y) :
    ∃ r, State.recycle x = r ∧ r.stock ≠ [] ∧
      y = { r with stock := (State.dealUpTo r.drawStep r.stock).2,
                   waste := (State.dealUpTo r.drawStep r.stock).1.reverse ++ r.waste } := by
  have h0 : State.dealStock (State.recycle x) = some y :=
    hsuc
  have hrne : (State.recycle x).stock ≠ [] := by
    intro hc
    rw [dealStock_nil _ hc] at h0
    exact absurd h0 (by simp)
  refine ⟨State.recycle x, rfl, hrne, ?_⟩
  have hs := dealStock_eq_of_ne_nil _ hrne
  rw [hs] at h0
  simp only [Option.some.injEq] at h0
  exact h0.symm
