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
  ∃ play w, s.run play = some w ∧ w.isWin = true

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

/-- The witness form of reversible: the move is legal and an
explicit play returns to the origin.  This is the constructive
content of `reversibleAt` — the program's reversible rows are
proved by producing these witnesses.  The two lemmas relating the
forms below are intuitionistic and axiom-free; the unconditioned
iff between the negative and witness forms is deliberately NOT
stated, because it is the one step that drags `Classical.choice`
through the vocabulary (pushing a negation through a universal
into an existential).  The program never needs that bridge: every
classification row supplies the effective dichotomy itself — a
decidable shape on the state proves `irreversibleAt` on one side
and hands an explicit witness (`reversibleAtW`) on the other, and
`irreversibleAt ∧ reversibleAtW` is refuted by the lemmas. -/
def reversibleAtW (st : State) (m : Move) : Prop :=
  ∃ s₁ play, State.step st m = some s₁ ∧ s₁.run play = some st

/-- A witness proves the negative form — intuitionistic, no
axioms. -/
theorem reversibleAt_of_W {st : State} {m : Move} (h : reversibleAtW st m) :
    reversibleAt st m := by
  obtain ⟨s₁, play, hstep, hrun⟩ := h
  intro contra
  exact contra s₁ play hstep hrun

/-- A commitment refutes every witness — intuitionistic, no
axioms. -/
theorem not_reversibleAtW_of_irreversibleAt {st : State} {m : Move}
    (h : irreversibleAt st m) : ¬ reversibleAtW st m := by
  rintro ⟨s₁, play, hstep, hrun⟩
  exact absurd hrun (h s₁ play hstep)
