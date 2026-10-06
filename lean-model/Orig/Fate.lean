import Orig.Play

/-!
# The original game — winnability and futures

The notions the whole program is *about*, stated on the original
game with no preprocessing:

* `Reach` — play-reachability;
* `WinFrom` — winnability, the verdict;
* `sameFate` — positions with the same verdict.  This is the
  primitive "same future": every later equivalence machinery (twin
  exchange, pile symmetries, arrangement-blind quotients) must
  *derive* its equalities from `sameFate`, never assume them;
* `succ` — the one-move successor relation, in terms of which any
  branching or futures count is stated;
* `irreversibleAt` — commitments, read semantically and
  state-dependently.  No syntactic move-set split exists at this
  layer; the engine's shuffle/commit vocabulary of later chapters
  must be licensed against this predicate.

Later chapters (each a derived construction, per `Orig.lean`'s
plan): the accounting invariants, the arrangement-blind bridge to
`Klondike.*`, the regrouping, and the futures count — "a commitment
leaves at most two `sameFate`-distinct successors, per
accommodation window" — stated with every restriction proved, not
baked in.

Tickets *from* this file:

1. the window/shuffle vocabulary on the original game (which
   reversible moves close, and when `irreversibleAt` matches the
   intuitive commitment kinds);
2. `WinFrom` reducibility along `succ` (started below:
   `WinFrom_of_succ`);
3. the count: `≤ 2` `sameFate`-classes among the successors of one
   irreversible spend, with the counterexample fences of the
   `Klondike` witness corpus re-derived here first.
-/

/-- `s'` is reachable from `s` by some legal play. -/
def Reach (s s' : State) : Prop := ∃ play, s.run play = some s'

/-- Winnability of a position — the verdict. -/
def WinFrom (s : State) : Prop :=
  ∃ play w, s.run play = some w ∧ w.isWin

/-- Two positions with the same verdict — the primitive "same
future". -/
def sameFate (s s' : State) : Prop := WinFrom s ↔ WinFrom s'

theorem sameFate_refl (s : State) : sameFate s s := Iff.rfl

theorem sameFate_symm {s s' : State} (h : sameFate s s') : sameFate s' s := h.symm

theorem sameFate_trans {a b c : State}
    (h₁ : sameFate a b) (h₂ : sameFate b c) : sameFate a c := h₁.trans h₂

/-- The one-move successor relation. -/
def succ (s s' : State) : Prop := ∃ m, State.step s m = some s'

/-- Any win witnessed from a successor is a win from the parent —
the bookend every futures-count argument plugs into. -/
theorem WinFrom_of_succ {s s' : State} (hs : succ s s') (h : WinFrom s') : WinFrom s := by
  obtain ⟨m, hm⟩ := hs
  obtain ⟨play, w, hrun, hwin⟩ := h
  refine ⟨m :: play, w, ?_, hwin⟩
  simp only [State.run, hm]
  exact hrun

/-- A move is a *commitment* at `st` iff no continued play ever
returns: the semantic, state-dependent reading. -/
def irreversibleAt (st : State) (m : Move) : Prop :=
  ∀ s₁ play, State.step st m = some s₁ → s₁.run play ≠ some st

/-- A move that is not a commitment: undoable in place. -/
def reversibleAt (st : State) (m : Move) : Prop := ¬ irreversibleAt st m
