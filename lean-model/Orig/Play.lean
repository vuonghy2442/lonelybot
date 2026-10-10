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

/-- The located `putRun`: the top-directed landing appends the run at
the located pile. -/
theorem putRun_inr_eq {st : State} {run : List Card} {z : Card} {k : Anchor}
    (h : st.pileOfTop z = some k) :
    st.putRun run (Sum.inr z) =
    st.setPile k { st.piles k with faceUp := (st.piles k).faceUp ++ run } := by
  rw [show st.putRun run (Sum.inr z) =
    st.setPile k { st.piles k with faceUp := (st.piles k).faceUp ++ run } from by
    simp only [State.putRun, h]]
