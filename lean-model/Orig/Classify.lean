import Orig.Macro
import Orig.Mono
import Orig.Irreversible
import Orig.Phase

/-!
# Orig — the classification assembly

A tranche of the last ticket of the irreversibility lane: the
constructor rows of the decidable per-move oracle for
`irreversibleAt` (`Orig/Fate.lean:73` — the semantic,
arbitrary-play definition), built from the landed corpus (the
measure tables of `Orig.Irreversible`, the draw rows of
`Orig.Phase`, the bridges of `Orig.Mono`) plus the rows this file
establishes.

## What this file establishes

* **Universal rows** (no gate needed):
  * `irreversibleAt_wasteToFound` / `irreversibleAt_wasteToTab` —
    the waste consumers are commitments at every position, wild or
    WF: the cycle count strictly drops and never rises.
  * `irreversibleAt_of_illegal` — a refused move is vacuously
    irreversible at every position.
  * `tabToFound_irreversible_of_bare_nonking` and
    `tabToTab_irreversible_of_bare_nonking` — moving the whole
    face-up content of a hidden-free pile to the foundation, or
    away onto another pile, is a commitment whenever the mover is
    not a king: the emptied seat receives only king-headed writes
    (the `BareKing` invariant, proved preserved by every legal
    move in `bare_king_step` and ridden along plays in
    `bare_king_run`), so a non-king can never re-land.
* **The pass-base round trip** `draw_passBase_reversibleW` — the
  general pass-base draw (empty stock, waste larger than the draw
  step) is undone by a pure-draw drain (`drain_to_pass`): the
  Phase bank covered only wastes no larger than the draw step (the
  `selfRecycle` row); the drain closes the general case.
* **The classification rows** (WF-gated, since each consumes the
  conservation invariant):
  * `tabToFoundClass` — reveal rows irreversible (the hidden total
    strictly drops), the bare seat a commitment precisely for
    non-kings, the under row reversible at WF (the undo premises
    discharged by `runOK` seams and the successor search pins via
    the card-count uniqueness), illegal rows vacuous.
  * `foundToTabClass` — every legal `.foundToTab` is reversible at
    WF (the `foundToTab_undo` family with `hnext` discharged by
    `wf_found_chop_toIdx` — the positional arithmetic of the
    foundation prefix — and the search pin by
    `wf_found_not_pileTop`), so the shape is exactly the negated
    legality guard.
  * `tabToTabClass` *(tranche two)* — the `.tabToTab` rows:
    illegal rows (refused head search or placement guard) vacuous,
    the reveal row a commitment (the hidden total strictly drops),
    the bare seat split at the king (`tabToTab_undo_bare`
    reseatings for kings, `tabToTab_irreversible_of_bare_nonking`
    for the rest), the under row reversible at WF through
    `tabToTab_undo_under` — the mirror-move undos stated
    wild-state with each premise excluding a documented corner
    (`hhold` the undo's own head search, `hseat` the move's inner
    placement search at the half-updated board, `hcN`/`hzOnly`/
    `hzK` the occurrence-uniqueness pins), the WF grind
    discharging every premise through the conservation invariant.
  * `drawClass` — pristine and offset positions irreversible
    (Phase's `draw_irreversibility_class`), in-phase and pass-base
    positions reversible (Phase's `draw_reversible_inphaseW`,
    `draw_reversible_selfRecycleW`, and the pass-base drain above),
    the both-empty draw illegal.
* **The assembled oracle** *(tranche two)* — `irreversibleOf` (the
  per-move Bool: draw from `drawIrr`, the waste rows trivially
  true, the table moves from the three shape predicates) with its
  WF-gated specification `irreversible_iff_of` and the decider
  rider `decidable_irreversibleAt_of_wf` (a plain definition, not
  an instance gate: at wild states the shape and the semantics
  diverge in both directions — the fork exhibits).
* **The de-choice** *(tranche two)* — the positional kit's last
  `Classical.choice` carrier was the private `take_take_le` (the
  `omega` closing the `List.take`-bearing zero cell); explicit
  `Nat.not_succ_le_zero` / `Nat.le_of_succ_le_succ` cells replaced
  it and the whole spine now audits at `[propext, Quot.sound]`.
* **The WFRun-gated `win_macro_aux` companion** *(tranche two,
  the scrub shape)* — `win_macro_aux_wf`: plays whose intermediate
  states are all WF carry the successor's WF down the induction
  as data (`WFRun.cons`), so the head split goes through the gated
  oracle's Bool (`cases … irreversibleOf`) and audits
  `[propext, Quot.sound]`; the classical head at
  `Orig/Macro.lean:121` keeps its `by_cases` and its choice audit.

## What this tranche deliberately leaves open

Step-preserved `WF` (`s₁.WF` from `st.WF` and `State.step`, all
six move kinds) — the conservation ticket of `Orig.lean` — remains
open; the `WFRun` companion carries each successor's WF as data
so as not to depend on it.  A premiseless decider for the
semantic predicate at wild states remains impossible by design
(the freezer exhibit refutes the universal iff; the archive
`Witnesses.ClassificationForkWitness` holds both corners).

## The design fork and the `win_macro_aux` scrub

Two regimes are live for the oracle: the *universal* oracle (an
iff at every state) and the *WF-gated* oracle.  The digestion of
the landed corpus points to the corners that decide it (each
exhibited in tranche two as a hand-built wild record: see
`Witnesses.ClassificationForkWitness` — the diadem and the
freezer):

* a doubled-king, miscounted-foundation corner where a noreveal
  `.tabToFound` has `canSitOn` true for the seat's card yet the
  successor's pile-top search pins the *other* copy of that card —
  every static-undo premise row reads the move irreversible while
  a three-move shuttle (king up, card re-seated, king back)
  returns: a static shape computed from guards cannot see a
  returning *play*;
* a wild-stacked corner where no measure fires and every canonical
  undo dies yet the successor is frozen (no legal move at all), so
  the noreveal move is plainly irreversible — no fit condition
  explains it.

Together these kill both directions of a premiseless iff: at wild
states the semantic predicate tracks whole plays, not shapes.  The
oracle is therefore to be **gated by `State.WF`**:

```
st.WF → (irreversibleAt st m ↔ irreversibleOf st m = true)
```

with the decider derived at WF states only — deliberately no
global `Decidable (irreversibleAt _ _)` instance: it would be
unsound at wild states for exactly the doubled-king reason.  This
is the fork resolution the ticket records for FUTURES-ORIG §5.6.

Consequently `win_iff_macro`'s single classical step — the
`by_cases` at `Orig/Macro.lean:121`, splitting `irreversibleAt cur
m` at a state reached mid-induction — cannot honestly be decided:
the theorem's statement carries no WF hypothesis, and at a wild
`cur` no static shape decides the semantic predicate.  The planned
landing keeps the classical original untouched (the audits stay
`[propext, Classical.choice, Quot.sound]`, before = after) and
puts the scrub's substance in a `WFRun`-gated companion whose
single split goes through the gated decider, with each `WFRun.cons`
handing the successor's WF down the induction.

## Axiom discipline

Everything new here audits `[propext, Quot.sound]` or fewer — zero
`Classical.choice`, zero `sorryAx`, no `native_decide`.  The only
card splits go through decidable equality, the rank facts are
`omega` over `Rank.toIdx`, and the numeral facts about `Rank.all`
are discharged by kernel computation.

Private isolation copies of step inversions and list helpers are
farm-normal and dedup at merge.
-/

/-! ## Private copies of the step inversions -/

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
      s' = { found := fun σ =>
              if σ = c.suit then st.found c.suit ++ [c] else st.found σ,
             piles := fun a' =>
               if a' = a then Pile.afterRunRemoved (st.piles a) (chop (st.piles a).faceUp)
               else st.piles a',
             stock := st.stock,
             waste := st.waste,
             drawStep := st.drawStep } := by
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

/-! ## Small private kit -/

/-- A nonempty list splits at its head. -/
private theorem list_cons_of_ne_nil {α : Type} {l : List α} (h : l ≠ []) :
    ∃ x t, l = x :: t := by
  cases l with
  | nil => exact absurd rfl h
  | cons x t => exact ⟨x, t, rfl⟩

/-- A non-`none` option carries a value. -/
private theorem option_some_of_ne_none {α : Type} {o : Option α} (h : o ≠ none) :
    ∃ v, o = some v := by
  cases o with
  | none => exact absurd rfl h
  | some v => exact ⟨v, rfl⟩

/-- The head of a nonempty list never hides in `lastOf`: the tail
is the last element's. -/
private theorem lastOf_cons_of_ne {x : Card} {l : List Card} (h : l ≠ []) :
    lastOf (x :: l) = lastOf l := by
  obtain ⟨y, t, hc⟩ := list_cons_of_ne_nil h
  subst hc
  rfl

/-- Every nonempty list has a last element. -/
private theorem lastOf_cons_some : ∀ (l : List Card) (x : Card),
    ∃ z, lastOf (x :: l) = some z := by
  intro l
  induction l with
  | nil => intro x; exact ⟨x, rfl⟩
  | cons y t _ih => intro x; exact _ih y

/-- The last element of a list never hides in the empty option. -/
private theorem lastOf_cons_ne_none : ∀ (l : List Card), ∀ (x : Card),
    lastOf (x :: l) ≠ none := by
  intro l
  induction l with
  | nil => intro x h; simp [lastOf] at h
  | cons y t' ih =>
      intro x h
      exact ih y h

/-- The last element of a list belongs to it. -/
private theorem lastOf_mem {l : List Card} {z : Card} (h : lastOf l = some z) :
    z ∈ l := by
  induction l with
  | nil => simp [lastOf] at h
  | cons x t ih =>
      cases t with
      | nil =>
          have hx : some x = some z := h
          injection hx with hzc
          subst hzc
          exact List.mem_cons.2 (Or.inl rfl)
      | cons y t' =>
          exact List.mem_cons.2 (Or.inr (ih h))

/-- Every element of `chop` is an element. -/
private theorem chop_mem {l : List Card} {x : Card} (h : x ∈ chop l) : x ∈ l := by
  induction l with
  | nil => cases h
  | cons y t ih =>
      cases t with
      | nil => cases h
      | cons w t' =>
          have h' : x ∈ y :: chop (w :: t') := h
          rcases List.mem_cons.1 h' with hxy | hrest
          · exact List.mem_cons.2 (Or.inl hxy)
          · exact List.mem_cons.2 (Or.inr (ih hrest))

/-- Every element of `below c` is an element. -/
private theorem below_mem {c : Card} : ∀ {l : List Card} {x : Card},
    x ∈ below c l → x ∈ l := by
  intro l
  induction l with
  | nil => intro x h; cases h
  | cons y t ih =>
      intro x h
      rw [below] at h
      split at h
      · cases h
      · rcases List.mem_cons.1 h with rfl | hm
        · exact List.mem_cons.2 (Or.inl rfl)
        · exact List.mem_cons.2 (Or.inr (ih hm))

/-- Every element of `fromCard c` is an element. -/
private theorem fromCard_mem {c : Card} : ∀ {l : List Card} {x : Card},
    x ∈ fromCard c l → x ∈ l := by
  intro l
  induction l with
  | nil => intro x h; cases h
  | cons y t ih =>
      intro x h
      rw [fromCard] at h
      split at h
      · rcases List.mem_cons.1 h with rfl | hm
        · exact List.mem_cons.2 (Or.inl rfl)
        · exact List.mem_cons.2 (Or.inr hm)
      · exact List.mem_cons.2 (Or.inr (ih h))

/-- The run `fromCard c l`, when nonempty, starts at `c`. -/
private theorem fromCard_head {c : Card} : ∀ {l : List Card} {r : List Card},
    fromCard c l = r → r ≠ [] → ∃ t, r = c :: t := by
  intro l
  induction l with
  | nil =>
      intro r hr hne
      rw [fromCard] at hr
      exact absurd hr.symm hne
  | cons y t ih =>
      intro r hr hne
      rw [fromCard] at hr
      split at hr
      · rename_i hyc
        subst hr
        rw [hyc]
        exact ⟨t, rfl⟩
      · exact ih hr hne

/-- The below-part and the run from `c` reassemble the list. -/
private theorem below_join {c : Card} : ∀ (l : List Card),
    below c l ++ fromCard c l = l := by
  intro l
  induction l with
  | nil => rfl
  | cons y t ih =>
      rw [below, fromCard]
      split
      · rfl
      · rw [List.cons_append, ih]

/-- `c` never lies strictly below itself. -/
private theorem below_not_mem_self {c : Card} : ∀ (l : List Card), c ∉ below c l := by
  intro l
  induction l with
  | nil => intro h; cases h
  | cons y t ih =>
      rw [below]
      split
      · intro h; cases h
      · rename_i hy
        intro h
        rcases List.mem_cons.1 h with hyc | hm
        · exact absurd hyc.symm hy
        · exact ih hm

/-- With `c` absent from a prefix, below and fromCard only look
past it. -/
private theorem below_fromCard_excl {c : Card} : ∀ (X l : List Card), c ∉ X →
    below c (X ++ l) = X ++ below c l ∧ fromCard c (X ++ l) = fromCard c l := by
  intro X
  induction X with
  | nil => intro l _; exact ⟨rfl, rfl⟩
  | cons y t ih =>
      intro l hc
      have hy : y ≠ c := fun heq => hc (List.mem_cons.2 (Or.inl heq.symm))
      have hcT : c ∉ t := fun hm => hc (List.mem_cons.2 (Or.inr hm))
      constructor
      · show below c (y :: (t ++ l)) = y :: (t ++ below c l)
        rw [below, ite_eq_right hy]
        exact congrArg (y :: ·) (ih l hcT).1
      · show fromCard c (y :: (t ++ l)) = fromCard c l
        rw [fromCard, ite_eq_right hy]
        exact (ih l hcT).2

/-- With `c` absent from a list, below is the identity. -/
private theorem below_self_of_not_mem {c : Card} : ∀ {l : List Card}, c ∉ l →
    below c l = l := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons y t ih =>
      intro h
      have hy : y ≠ c := fun heq => h (List.mem_cons.2 (Or.inl heq.symm))
      have ht : c ∉ t := fun hm => h (List.mem_cons.2 (Or.inr hm))
      show below c (y :: t) = y :: t
      rw [below, ite_eq_right hy, ih ht]

/-- With `c` absent from a list, the run from `c` is empty. -/
private theorem fromCard_nil_of_not_mem {c : Card} : ∀ {l : List Card}, c ∉ l →
    fromCard c l = [] := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons y t ih =>
      intro h
      have hy : y ≠ c := fun heq => h (List.mem_cons.2 (Or.inl heq.symm))
      have ht : c ∉ t := fun hm => h (List.mem_cons.2 (Or.inr hm))
      show fromCard c (y :: t) = []
      rw [fromCard, ite_eq_right hy, ih ht]

/-- The run from `c` of a run that starts at `c` is the run. -/
private theorem fromCard_head_eq {c : Card} {t : List Card} :
    fromCard c (c :: t) = c :: t := by
  rw [fromCard, ite_eq_left rfl]

/-- The below-part of a run that starts at `c` is empty. -/
private theorem below_head_eq {c : Card} {t : List Card} :
    below c (c :: t) = [] := by
  rw [below, ite_eq_left rfl]

/-- A card present in a list has a nonempty run from it — the
`.tabToTab` step guard's nonemptiness, at one line. -/
private theorem fromCard_ne_of_mem {c : Card} : ∀ {l : List Card},
    c ∈ l → fromCard c l ≠ [] := by
  intro l
  induction l with
  | nil => intro hmem; cases hmem
  | cons y t ih =>
      intro hmem
      rw [fromCard]
      split
      · exact List.cons_ne_nil _ _
      · rename_i hy
        rcases List.mem_cons.1 hmem with heq | hta
        · exact absurd heq.symm hy
        · exact ih hta

/-- The tail of a legal run is legal. -/
private theorem runOK_cons_tail {x : Card} {t : List Card}
    (h : runOK (x :: t) = true) : runOK t = true := by
  cases t with
  | nil => rfl
  | cons w t' =>
      rw [runOK, Bool.and_eq_true] at h
      exact h.2

/-- Every suffix of a legal run is legal — the left-degradation of
`runOK` under append. -/
private theorem runOK_append_left : ∀ (A B : List Card),
    runOK (A ++ B) = true → runOK B = true := by
  intro A
  induction A with
  | nil => intro B h; exact h
  | cons y t ih =>
      intro B h
      exact ih B (runOK_cons_tail h)

/-- Every prefix of a legal run is legal — the right-degradation of
`runOK` under append, the other half used by the `.tabToTab` under
row (the snoc-adjacent fit of `runOK_adjacent_snoc` needs the
prefix `P ++ [c]` legal while the step hypothesis only hands over
`P ++ c :: T`). -/
private theorem runOK_append_right : ∀ (A B : List Card),
    runOK (A ++ B) = true → runOK A = true := by
  intro A
  induction A with
  | nil => intro _ _; rfl
  | cons y t ih =>
      intro B h
      match t with
      | [] => rfl
      | w :: t' =>
          have h' : runOK (y :: w :: (t' ++ B)) = true := h
          rw [runOK, Bool.and_eq_true] at h' ⊢
          exact ⟨h'.1, ih B h'.2⟩

/-- In a legal run, every tail card sits strictly below the head in
rank — a farm copy of `Orig.Integrity`'s private descent member
(dedup-marked; the upstream copy stays private in its file). -/
private theorem runOK_head_lt : ∀ {t : List Card} {x y : Card},
    runOK (x :: t) = true → y ∈ t → y.rank.toIdx < x.rank.toIdx := by
  intro t
  induction t with
  | nil => intro x y _ hmem; cases hmem
  | cons w t' ih =>
      intro x y hok hmem
      rw [runOK, Bool.and_eq_true] at hok
      obtain ⟨hsit, hrest⟩ := hok
      obtain ⟨heq, -⟩ := (canSitOn_eq w x).mp hsit
      have hwlt : w.rank.toIdx < x.rank.toIdx := by omega
      rcases List.mem_cons.1 hmem with rfl | hyt
      · exact hwlt
      · have := ih hrest hyt
        omega

/-- The seam fit: in a legal face-up run, each card fits on its
immediate predecessor, anywhere in the list. -/
private theorem runOK_seam : ∀ (A B : List Card) {x c : Card},
    runOK (A ++ x :: c :: B) = true → canSitOn c x = true := by
  intro A
  induction A with
  | nil =>
      intro B x c h
      rw [List.nil_append, runOK, Bool.and_eq_true] at h
      exact h.1
  | cons y t ih =>
      intro B x c h
      exact ih B (runOK_cons_tail h)

/-- A list (reassembly of `chop`) with a known last element keeps
that element adjacent to the snocced cards.  The concrete snoc form
used by the `.tabToFound` row. -/
private theorem runOK_adjacent_snoc {P : List Card} {z c : Card}
    (hlast : lastOf P = some z) (hok : runOK (P ++ [c]) = true) :
    canSitOn c z = true := by
  have hc1 : P ++ [c] = (chop P ++ [z]) ++ [c] :=
    congrArg (· ++ [c]) (lastOf_chop hlast)
  have hc2 : (chop P ++ [z]) ++ [c] = chop P ++ [z, c] := by
    rw [List.append_assoc]
    rfl
  rw [hc1.trans hc2] at hok
  exact runOK_seam _ _ hok

/-- The firstWhere-soundness adjunct: a refuted proposition decides
false. -/
private theorem decide_false_of_not {p : Prop} [Decidable p] (h : ¬p) :
    decide p = false := by
  cases hdec : decide p with
  | true => exact absurd (of_decide_eq_true hdec) h
  | false => rfl

/-- Completeness of `firstWhere`: the anchor satisfying the
predicate is found when every other anchor in the list fails it. -/
private theorem firstWhere_find {p : Anchor → Bool} :
    ∀ {l : List Anchor} {a : Anchor}, a ∈ l → p a = true →
      (∀ x ∈ l, x ≠ a → p x = false) → firstWhere p l = some a := by
  intro l
  induction l with
  | nil => intro a hmem; cases hmem
  | cons x t ih =>
      intro a hmem hp hfull
      by_cases hax : a = x
      · subst hax
        rw [firstWhere, hp]
      · have hpx : p x = false :=
          hfull x (List.mem_cons.2 (Or.inl rfl)) (fun h => hax h.symm)
        rcases List.mem_cons.1 hmem with heq | hta
        · exact absurd heq hax
        · rw [firstWhere, hpx]
          exact ih hta hp (fun y hy hyne =>
            hfull y (List.mem_cons.2 (Or.inr hy)) hyne)

/-! ## The found-vs-pile occurrence kit -/

/-- One pile's whole zone, hidden cards under face-up ones. -/
private def pileZoneC (st : State) (a : Anchor) : List Card :=
  (st.piles a).hidden ++ (st.piles a).faceUp

private theorem flatMapAppend {α β : Type} (f : α → List β) :
    ∀ (A B : List α), List.flatMap f (A ++ B) = List.flatMap f A ++ List.flatMap f B := by
  intro A
  induction A with
  | nil => intro B; rfl
  | cons x t ih =>
      intro B
      show f x ++ List.flatMap f (t ++ B) = (f x ++ List.flatMap f t) ++ List.flatMap f B
      rw [ih, List.append_assoc]

/-- Each occurrence of `c` in a list contributes one to the filtered
count. -/
private theorem count_filter_pos {c : Card} :
    ∀ {l : List Card}, c ∈ l → 1 ≤ (l.filter fun x => decide (x = c)).length := by
  intro l hmem
  have hm : c ∈ l.filter fun x => decide (x = c) := List.mem_filter.2 ⟨hmem, by simp⟩
  exact List.length_pos_of_mem hm

/-- Two occurrences in separate flatMap blocks make the count at
least two. -/
private theorem count_ge_two_of_split {st : State} {c : Card} {A B : List (List Card)}
    (hsplit : st.zones = A ++ B) (hl : c ∈ A.flatMap id) (hr : c ∈ B.flatMap id) :
    2 ≤ st.cardCount c := by
  show 2 ≤ ((st.zones.flatMap id).filter fun x => decide (x = c)).length
  rw [hsplit, flatMapAppend, List.filter_append, List.length_append]
  have hL := count_filter_pos hl
  have hR := count_filter_pos hr
  omega

/-- A WF state never holds a foundation card in a pile: the two
memberships would make the count two. -/
private theorem wf_found_not_in_pile {st : State} {c : Card} {a : Anchor} {σ : Suit}
    (hwf : st.WF) (hf : c ∈ st.found σ) (hp : c ∈ (st.piles a).hidden ∨ c ∈ (st.piles a).faceUp) :
    False := by
  have hcount : st.cardCount c = 1 := hwf.cardCount_eq (Card.mem_universe c)
  have hsplit : st.zones =
      (Suit.all.map st.found) ++
        ((Anchor.all.map (fun a' => pileZoneC st a')) ++ [st.stock, st.waste]) := rfl
  have hl : c ∈ (Suit.all.map st.found).flatMap id :=
    (List.mem_flatMap).2 ⟨st.found σ, List.mem_map.2 ⟨σ, Suit.mem_all σ, rfl⟩, hf⟩
  have hz : c ∈ pileZoneC st a := by
    rcases hp with h | h
    · exact (List.mem_append).2 (Or.inl h)
    · exact (List.mem_append).2 (Or.inr h)
  have hr : c ∈ ((Anchor.all.map (fun a' => pileZoneC st a')) ++ [st.stock, st.waste]).flatMap id :=
    (List.mem_flatMap).2 ⟨pileZoneC st a,
      (List.mem_append).2 (Or.inl (List.mem_map.2 ⟨a, Anchor.mem_all a, rfl⟩)), hz⟩
  have h2 : 2 ≤ st.cardCount c := count_ge_two_of_split hsplit hl hr
  omega

/-- A WF state's foundation top is no pile's top: the pile would
hold a foundation card face up. -/
private theorem wf_found_not_pileTop {st : State} {c : Card} {a : Anchor} {σ : Suit}
    (hwf : st.WF) (hf : lastOf (st.found σ) = some c) : (st.piles a).top ≠ some c := by
  intro htop
  have hmem : c ∈ (st.piles a).faceUp := Pile.mem_of_top htop
  exact wf_found_not_in_pile hwf (lastOf_mem hf) (Or.inr hmem)

/-! ## The positional kit: foundations end at their rank index -/

/-- The list-length take facts, as private copies. -/
private theorem take_length_min {α : Type} (l : List α) : ∀ (n : Nat),
    (l.take n).length = min n l.length := by
  induction l with
  | nil =>
      intro n
      simp only [List.take_nil, List.length_nil]
      omega
  | cons x t ih =>
      intro n
      match n with
      | 0 =>
          show (0 : Nat) = min 0 (x :: t).length
          omega
      | n' + 1 =>
          show (x :: t.take n').length = min (n' + 1) (t.length + 1)
          rw [List.length_cons, ih n']
          omega

/-- Taking no deeper than an earlier take reaches the same
prefix.  (Tranche two's de-choice: the landed proof closed the
`m' + 1 ≤ 0` cell with `omega`, and that `omega` call — atomizing a
`List.take`-bearing equation — is the single `Classical.choice`
carrier of the whole tranche-one spine, located by an
environment-wide private-constant axiom survey; `Suit.upCards_length`
was clean, the wrong suspect.  The explicit `Nat.not_succ_le_zero` /
`Nat.le_of_succ_le_succ` cells audit axiom-free.) -/
private theorem take_take_le {α : Type} (l : List α) : ∀ (m n : Nat), m ≤ n →
    (l.take n).take m = l.take m := by
  induction l with
  | nil => intro m n _; rw [List.take_nil]
  | cons x t ih =>
      intro m n
      match m with
      | 0 => intro _; rfl
      | m' + 1 =>
          match n with
          | 0 => intro hle; exact absurd hle (Nat.not_succ_le_zero m')
          | n' + 1 =>
              intro hle
              exact congrArg (x :: ·) (ih (m') (n') (Nat.le_of_succ_le_succ hle))

/-- Taking to a list's own length is the identity. -/
private theorem take_length_self {α : Type} (l : List α) : l.take l.length = l := by
  induction l with
  | nil => rfl
  | cons x t ih =>
      show x :: t.take t.length = x :: t
      exact congrArg (x :: ·) ih

/-- Mapping commutes with dropping. -/
private theorem drop_map_min {α β : Type} (f : α → β) : ∀ (l : List α) (i : Nat),
    (l.map f).drop i = (l.drop i).map f := by
  intro l
  induction l with
  | nil =>
      intro i
      cases i <;> rfl
  | cons x t ih =>
      intro i
      match i with
      | 0 => rfl
      | i' + 1 => exact ih i'

/-- The rank of a zero-based index, tabulated by kernel
computation. -/
private def Rk : Nat → Rank
  | 0 => .ace | 1 => .two | 2 => .three | 3 => .four | 4 => .five | 5 => .six
  | 6 => .seven | 7 => .eight | 8 => .nine | 9 => .ten | 10 => .jack | 11 => .queen
  | 12 => .king | _ => .ace

private theorem Rk_toIdx : ∀ (k : Nat), k < 13 → (Rk k).toIdx = k := by
  intro k hk
  match k with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | 3 => rfl
  | 4 => rfl
  | 5 => rfl
  | 6 => rfl
  | 7 => rfl
  | 8 => rfl
  | 9 => rfl
  | 10 => rfl
  | 11 => rfl
  | 12 => rfl
  | w + 13 => exact absurd hk (by omega)

private theorem rank_all_drop_cons : ∀ (k : Nat), k < 13 →
    Rank.all.drop k = Rk k :: Rank.all.drop (k + 1) := by
  intro k hk
  match k with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | 3 => rfl
  | 4 => rfl
  | 5 => rfl
  | 6 => rfl
  | 7 => rfl
  | 8 => rfl
  | 9 => rfl
  | 10 => rfl
  | 11 => rfl
  | 12 => rfl
  | w + 13 => exact absurd hk (by omega)

/-- The suits' up-card lists drop by cons, kernel-computed. -/
private theorem upCards_drop_cons (s : Suit) : ∀ (k : Nat), k < 13 →
    s.upCards.drop k = Card.mk s (Rk k) :: s.upCards.drop (k + 1) := by
  intro k hk
  have hd := rank_all_drop_cons k hk
  show (Rank.all.map (Card.mk s)).drop k
      = Card.mk s (Rk k) :: (Rank.all.map (Card.mk s)).drop (k + 1)
  have hrw2 : (Rank.all.map (Card.mk s)).drop (k + 1)
      = (Rank.all.drop (k + 1)).map (Card.mk s) :=
    drop_map_min (Card.mk s) Rank.all (k + 1)
  rw [drop_map_min, hrw2, hd]
  rfl

/-- A take of the up-card list, taken `n` deep from offset `k`,
ends at index `k + n - 1`. -/
private theorem upCards_last_of_take (s : Suit) : ∀ (n k : Nat), n + k ≤ 13 → 0 < n →
    lastOf ((s.upCards.drop k).take n) = some (Card.mk s (Rk (k + n - 1))) := by
  intro n
  induction n with
  | zero => intro k _ hn; omega
  | succ m ih =>
      intro k hle _hm
      have hk : k < 13 := by omega
      rw [upCards_drop_cons s k hk]
      match m with
      | 0 => rfl
      | m' + 1 =>
          have hih := ih (k + 1) (by omega) (by omega)
          have hne : (s.upCards.drop (k + 1)).take (m' + 1) ≠ [] := by
            intro hc
            have hlt := take_length_min ((s.upCards.drop (k + 1))) (m' + 1)
            rw [hc, List.length_nil] at hlt
            have hd := List.length_drop (l := s.upCards) (i := k + 1)
            have h13 : s.upCards.length = 13 := Suit.upCards_length s
            omega
          show lastOf (Card.mk s (Rk k) :: (s.upCards.drop (k + 1)).take (m' + 1)) =
            some (Card.mk s (Rk (k + (m' + 1 + 1) - 1)))
          rw [lastOf_cons_of_ne hne, hih]
          refine congrArg (fun q => some (Card.mk s (Rk q))) (by omega)

/-- The WF foundation arithmetic: a foundation's chop length is the
rank index of its top card — the `hnext` premise of the
`foundToTab` undo, discharged by the conservation invariant's
prefix property. -/
theorem wf_found_chop_toIdx {st : State} {s : Suit} {c : Card}
    (hwf : st.WF) (htop : st.foundTop s = some c) :
    (chop (st.found s)).length = c.rank.toIdx := by
  obtain ⟨n, hn⟩ := hwf.found_prefix s
  have hlast : lastOf (st.found s) = some c := htop
  have hne : st.found s ≠ [] := by
    intro hc
    rw [hc] at hlast
    exact absurd hlast (by simp [lastOf])
  have hpos : 0 < (st.found s).length := by
    obtain ⟨w0, xs, hcon⟩ := list_cons_of_ne_nil hne
    rw [hcon, List.length_cons]
    omega
  have hup : (Suit.upCards s).length = 13 := Suit.upCards_length s
  have h13 : (st.found s).length ≤ 13 := by
    rw [hn, take_length_min]
    omega
  have hN : st.found s = s.upCards.take ((st.found s).length) := by
    rw [hn]
    have htt := take_take_le (Suit.upCards s) ((s.upCards.take n).length) n
      (by rw [take_length_min]; omega)
    have hlself := take_length_self (s.upCards.take n)
    rw [htt] at hlself
    exact hlself.symm
  have hz := upCards_last_of_take s ((st.found s).length) 0 (by omega) (by omega)
  rw [List.drop_zero, Nat.zero_add] at hz
  rw [← hN] at hz
  have hEq : some c = some (Card.mk s (Rk ((st.found s).length - 1))) :=
    hlast.symm.trans hz
  injection hEq with hRk
  have hcl : (chop (st.found s)).length + 1 = (st.found s).length := by
    have hlc := congrArg List.length (lastOf_chop hlast)
    rw [List.length_append] at hlc
    have h1 : ([c] : List Card).length = 1 := rfl
    omega
  rw [hRk]
  show (chop (st.found s)).length = (Rk ((st.found s).length - 1)).toIdx
  rw [Rk_toIdx ((st.found s).length - 1) (by omega)]
  omega

/-! ## Search pins at successors -/

/-- The top search re-pins to the one changed pile: at `s₁`, whose
piles agree with `st` away from `a`, a card that at `st` tops no
pile other than `a` and at `s₁` tops pile `a`, is found by the
search exactly at `a`. -/
private theorem topPin {st s₁ : State} {a : Anchor} {z : Card}
    (hothers : ∀ a', a' ≠ a → s₁.piles a' = st.piles a')
    (htop : (s₁.piles a).top = some z)
    (hnost : ∀ a', a' ≠ a → (st.piles a').top ≠ some z) :
    s₁.pileOfTop z = some a := by
  show firstWhere (fun a' => decide ((s₁.piles a').top = some z)) Anchor.all = some a
  refine firstWhere_find (Anchor.mem_all a) (decide_eq_true htop) ?_
  intro y hy hyne
  have he : (s₁.piles y).top = (st.piles y).top := by rw [hothers y hyne]
  rw [he]
  exact decide_false_of_not (hnost y hyne)

/-- The same pin with two exception piles: one written by the move
(`k`), one whose content must be argued separately (the source,
`a`). -/
private theorem topPin2 {st s₁ : State} {a k : Anchor} {z : Card}
    (htop : (s₁.piles a).top = some z)
    (hothers : ∀ a', a' ≠ a → a' ≠ k → s₁.piles a' = st.piles a')
    (hknot : (s₁.piles k).top ≠ some z)
    (hno : ∀ a', a' ≠ a → a' ≠ k → (st.piles a').top ≠ some z) :
    s₁.pileOfTop z = some a := by
  show firstWhere (fun a' => decide ((s₁.piles a').top = some z)) Anchor.all = some a
  refine firstWhere_find (Anchor.mem_all a) (decide_eq_true htop) ?_
  intro y hy hyne
  by_cases hyk : y = k
  · rw [hyk]
    exact decide_false_of_not hknot
  · have he : (s₁.piles y).top = (st.piles y).top := by rw [hothers y hyne hyk]
    rw [he]
    exact decide_false_of_not (hno y hyne hyk)

/-- The holding search re-pins to the one changed pile. -/
private theorem holdingPin {st s₁ : State} {k : Anchor} {c : Card}
    (hothers : ∀ a', a' ≠ k → s₁.piles a' = st.piles a')
    (hholds : c ∈ (s₁.piles k).faceUp)
    (hno : ∀ a', a' ≠ k → c ∉ (st.piles a').faceUp) :
    s₁.pileHolding c = some k := by
  show firstWhere (fun a' => decide (c ∈ (s₁.piles a').faceUp)) Anchor.all = some k
  refine firstWhere_find (Anchor.mem_all k) (decide_eq_true hholds) ?_
  intro y hy hyne
  have he : (s₁.piles y).faceUp = (st.piles y).faceUp := by rw [hothers y hyne]
  rw [he]
  exact decide_false_of_not (hno y hyne)

/-- The holding pin with two exception piles (the landing pile `k`
and the source `a`). -/
private theorem holdingPin2 {st s₁ : State} {k a : Anchor} {c : Card}
    (ha : c ∉ (s₁.piles a).faceUp)
    (hothers : ∀ a', a' ≠ k → a' ≠ a → s₁.piles a' = st.piles a')
    (hholds : c ∈ (s₁.piles k).faceUp)
    (hno : ∀ a', a' ≠ k → a' ≠ a → c ∉ (st.piles a').faceUp) :
    s₁.pileHolding c = some k := by
  show firstWhere (fun a' => decide (c ∈ (s₁.piles a').faceUp)) Anchor.all = some k
  refine firstWhere_find (Anchor.mem_all k) (decide_eq_true hholds) ?_
  intro y hy hyne
  by_cases hya : y = a
  · rw [hya]
    exact decide_false_of_not ha
  · have he : (s₁.piles y).faceUp = (st.piles y).faceUp := by rw [hothers y hyne hya]
    rw [he]
    exact decide_false_of_not (hno y hyne hya)

/-- The WF fact behind the pile-side `hnost` premises: a card
face-up in one pile tops no other pile. -/
private theorem wf_no_other_top {st : State} {c : Card} {a : Anchor}
    (hwf : st.WF) (hmem : c ∈ (st.piles a).faceUp) (a' : Anchor) (hne : a' ≠ a) :
    (st.piles a').top ≠ some c := by
  intro htop
  have := Pile.mem_of_top htop
  exact (mem_faceUp_unique hwf hmem a' hne).1 this

/-! ## The king-anchored pile invariant -/

/-- The face-up content is empty or anchored by a king at the
bottom. -/
private def KingHead : List Card → Prop
  | [] => True
  | x :: _ => x.rank = Rank.king

/-- A pile with no hidden cards whose face-up content, when
present, is king-anchored: once emptied, such a pile can only ever
receive king-headed writes. -/
private def BareKing (p : Pile) : Prop :=
  p.hidden = [] ∧ KingHead p.faceUp

private theorem kingHead_append {l r : List Card} (hl : l ≠ []) (h : KingHead l) :
    KingHead (l ++ r) := by
  obtain ⟨x, t, hc⟩ := list_cons_of_ne_nil hl
  subst hc
  exact h

private theorem kingHead_chop {l : List Card} (h : KingHead l) : KingHead (chop l) := by
  cases l with
  | nil => exact True.intro
  | cons x t =>
      cases t with
      | nil => exact True.intro
      | cons y t' => exact h

private theorem kingHead_below {c : Card} {l : List Card} (h : KingHead l) :
    KingHead (below c l) := by
  cases l with
  | nil => exact True.intro
  | cons x t =>
      rw [below]
      split
      · exact True.intro
      · exact h

/-- The removal-with-remainder writes the remainder as the face-up
run. -/
private theorem afterRunRemoved_faceUp_ne {p : Pile} {pre : List Card} (h : pre ≠ []) :
    (Pile.afterRunRemoved p pre).faceUp = pre := by
  cases pre with
  | nil => exact absurd rfl h
  | cons w t => rfl

/-- With no hidden cards, removing the whole face-up run empties the
pile outright (no reveal fires). -/
private theorem afterRunRemoved_faceUp_empty_self {p : Pile} (hhd : p.hidden = []) :
    Pile.afterRunRemoved p [] = { p with faceUp := ([] : List Card) } := by
  rcases p with ⟨hlist, flist⟩
  cases hlist with
  | nil => rfl
  | cons h t => exact absurd hhd (by simp)

/-- A `putRun` whose base card tops nothing returns its state
unchanged. -/
private theorem putRun_inr_none {st : State} {run : List Card} {z : Card}
    (hz : st.pileOfTop z = none) : st.putRun run (Sum.inr z) = st := by
  simp only [State.putRun, hz]

/-- The one-card placement respects the invariant of an
already-bare pile. -/
private theorem bare_king_putCard {s : State} {c : Card} {b : Base} (a : Anchor)
    (hcp : s.canPlace c b = true)
    (hhd : (s.piles a).hidden = []) (hkh : KingHead (s.piles a).faceUp) :
    BareKing ((s.putCard c b).piles a) := by
  cases b with
  | inl k =>
      rw [putCard_piles_inl]
      show BareKing (if a = k then (⟨[], [c]⟩ : Pile) else s.piles a)
      by_cases hak : a = k
      · rw [ite_eq_left hak]
        obtain ⟨-, hking⟩ := canPlace_inl hcp
        exact ⟨rfl, hking⟩
      · rw [ite_eq_right hak]
        exact ⟨hhd, hkh⟩
  | inr z =>
      obtain ⟨j, hz, -⟩ := canPlace_inr hcp
      rw [putCard_piles_inr _ _ _ _ hz]
      show BareKing (if a = j then
          { s.piles j with faceUp := (s.piles j).faceUp ++ [c] } else s.piles a)
      by_cases hak : a = j
      · rw [ite_eq_left hak]
        obtain ⟨hf, -⟩ := pileOfTop_top hz
        have hkhj : KingHead (s.piles j).faceUp := by rw [← hak]; exact hkh
        have hhdj : (s.piles j).hidden = [] := by rw [← hak]; exact hhd
        exact ⟨hhdj, kingHead_append hf hkhj⟩
      · rw [ite_eq_right hak]
        exact ⟨hhd, hkh⟩

/-- Every legal single move preserves the bare-king discipline of
any one pile: the emptied-seat placements demand kings, the card
placements only extend nonempty (already-headed) contents, and the
run removals take a prefix of a king-headed content or take
everything (firing no reveal when no hidden cards remain). -/
private theorem bare_king_step : ∀ {s s' : State} {m : Move},
    State.step s m = some s' → ∀ (a : Anchor),
    BareKing (s.piles a) → BareKing (s'.piles a) := by
  intro s s' m hstep a ⟨hhd, hkh⟩
  match m with
  | .draw =>
      have hp := stepDraw_piles hstep
      rw [hp]
      exact ⟨hhd, hkh⟩
  | .wasteToFound c =>
      obtain ⟨-, x, xs, -, hs⟩ := step_wasteToFound_inv hstep
      rw [hs]
      exact ⟨hhd, hkh⟩
  | .wasteToTab c b =>
      obtain ⟨hg, x, xs, -, hs⟩ := step_wasteToTab_inv hstep
      rw [Bool.and_eq_true] at hg
      rw [hs]
      rw [show (({ s.putCard c b with waste := xs } : State).piles) a
          = (s.putCard c b).piles a from rfl]
      exact bare_king_putCard a hg.2 hhd hkh
  | .foundToTab c b =>
      obtain ⟨c', ht, hce, hcp, hs⟩ := step_foundToTab_inv hstep
      rw [hs]
      exact bare_king_putCard a hcp hhd hkh
  | .tabToFound c =>
      obtain ⟨-, a₀, hp, hs⟩ := step_tabToFound_inv hstep
      rw [hs]
      show BareKing
          ((fun a' =>
            if a' = a₀ then Pile.afterRunRemoved (s.piles a₀) (chop (s.piles a₀).faceUp)
            else s.piles a') a)
      show BareKing (if a = a₀ then
          Pile.afterRunRemoved (s.piles a₀) (chop (s.piles a₀).faceUp) else s.piles a)
      by_cases ha : a = a₀
      · rw [ite_eq_left ha]
        rw [ha] at hhd hkh
        rcases afterRunRemoved_hidden (s.piles a₀) (chop (s.piles a₀).faceUp) with
          ⟨hpre, hhidx⟩ | ⟨he, hhdd, hhidx⟩ | ⟨he, hhn, -⟩
        · show
            (Pile.afterRunRemoved (s.piles a₀) (chop (s.piles a₀).faceUp)).hidden = [] ∧
              KingHead (Pile.afterRunRemoved (s.piles a₀) (chop (s.piles a₀).faceUp)).faceUp
          refine ⟨?_, ?_⟩
          · rw [show (Pile.afterRunRemoved (s.piles a₀) (chop (s.piles a₀).faceUp)).hidden
                = (s.piles a₀).hidden from hhidx]
            exact hhd
          · rw [afterRunRemoved_faceUp_ne hpre]
            exact kingHead_chop hkh
        · rw [he, afterRunRemoved_faceUp_empty_self hhdd]
          exact ⟨hhdd, True.intro⟩
        · exact absurd hhd hhn
      · rw [ite_eq_right ha]
        exact ⟨hhd, hkh⟩
  | .tabToTab c b =>
      obtain ⟨a₀, hh, hcp, hne, hs⟩ := step_tabToTab_inv hstep
      rw [hs]
      have hmidfact : BareKing
          ((s.setPile a₀
              (Pile.afterRunRemoved (s.piles a₀) (below c (s.piles a₀).faceUp))).piles a) := by
        by_cases ha : a = a₀
        · rw [ha] at hhd hkh
          rw [ha]
          rw [setPile_afterRunRemoved_piles_self]
          rcases afterRunRemoved_hidden (s.piles a₀) (below c (s.piles a₀).faceUp) with
            ⟨hpre, hhidx⟩ | ⟨he, hhdd, hhidx⟩ | ⟨he, hhn, -⟩
          · show
              (Pile.afterRunRemoved (s.piles a₀) (below c (s.piles a₀).faceUp)).hidden = [] ∧
                KingHead (Pile.afterRunRemoved (s.piles a₀) (below c (s.piles a₀).faceUp)).faceUp
            refine ⟨?_, ?_⟩
            · rw [show (Pile.afterRunRemoved (s.piles a₀)
                    (below c (s.piles a₀).faceUp)).hidden = (s.piles a₀).hidden from hhidx]
              exact hhd
            · rw [afterRunRemoved_faceUp_ne hpre]
              exact kingHead_below hkh
          · rw [he, afterRunRemoved_faceUp_empty_self hhdd]
            exact ⟨hhdd, True.intro⟩
          · exact absurd hhd hhn
        · rw [setPile_afterRunRemoved_piles_ne _ _ _ _ ha]
          exact ⟨hhd, hkh⟩
      obtain ⟨ttr, hrt⟩ := fromCard_head rfl hne
      cases b with
      | inl k =>
          rw [putRun_piles_inl]
          show BareKing (if a = k then
              (⟨[], fromCard c (s.piles a₀).faceUp⟩ : Pile)
              else (s.setPile a₀
                (Pile.afterRunRemoved (s.piles a₀) (below c (s.piles a₀).faceUp))).piles a)
          by_cases hak : a = k
          · rw [ite_eq_left hak, hrt]
            obtain ⟨-, hking⟩ := canPlace_inl hcp
            exact ⟨rfl, hking⟩
          · rw [ite_eq_right hak]
            exact hmidfact
      | inr z =>
          cases hz : (s.setPile a₀
              (Pile.afterRunRemoved (s.piles a₀) (below c (s.piles a₀).faceUp))).pileOfTop z with
          | none =>
              rw [putRun_inr_none hz]
              exact hmidfact
          | some j =>
              rw [putRun_piles_inr _ _ _ _ hz]
              show BareKing (if a = j then
                  { (s.setPile a₀
                      (Pile.afterRunRemoved (s.piles a₀) (below c (s.piles a₀).faceUp))).piles j with
                    faceUp := ((s.setPile a₀
                        (Pile.afterRunRemoved (s.piles a₀) (below c (s.piles a₀).faceUp))).piles j).faceUp
                      ++ fromCard c (s.piles a₀).faceUp }
                  else (s.setPile a₀
                    (Pile.afterRunRemoved (s.piles a₀) (below c (s.piles a₀).faceUp))).piles a)
              by_cases hak : a = j
              · rw [ite_eq_left hak]
                obtain ⟨hfa, -⟩ := pileOfTop_top hz
                rw [hak] at hmidfact
                obtain ⟨hhdj, hkhj⟩ := hmidfact
                exact ⟨hhdj, kingHead_append hfa hkhj⟩
              · rw [ite_eq_right hak]
                exact hmidfact

/-- The invariant rides along arbitrary plays. -/
private theorem bare_king_run : ∀ (play : List Move) (s w : State) (a : Anchor),
    BareKing (s.piles a) → s.run play = some w → BareKing (w.piles a) := by
  intro play
  induction play with
  | nil =>
      intro s w a h hrun
      injection hrun with hu
      subst hu
      exact h
  | cons m rest ih =>
      intro s w a h hrun
      obtain ⟨s₁, hstep, hrest⟩ := State.run_cons hrun
      exact ih s₁ w a (bare_king_step hstep a h) hrest

/-- A self-located top search is impossible on an empty pile. -/
private theorem pileOfTop_ne_of_empty {st : State} {a : Anchor}
    (hE : st.piles a = ⟨[], ([] : List Card)⟩) (z : Card) :
    st.pileOfTop z ≠ some a := by
  intro hloc
  obtain ⟨hfa, -⟩ := pileOfTop_top hloc
  rw [hE] at hfa
  exact absurd rfl hfa

/-- `setPile` read at its own pile. -/
private theorem setPile_piles_self_any {st : State} {a : Anchor} {p : Pile} :
    (st.setPile a p).piles a = p := by
  show (if a = a then p else st.piles a) = p
  rw [ite_eq_left rfl]

/-- A bare `.tabToFound` of a non-king is a commitment: the emptied
seat never receives the card back — every write onto an empty seat
demands a king, every card-base write only extends nonempty
already-anchored contents, and the invariant along any play keeps
the pile empty or king-anchored, which the original content, headed
by the non-king mover, contradicts. -/
theorem tabToFound_irreversible_of_bare_nonking {st : State} {c : Card}
    {a : Anchor} {s₁ : State}
    (hstep : State.step st (Move.tabToFound c) = some s₁)
    (hpa : st.pileOfTop c = some a)
    (hchop : chop (st.piles a).faceUp = [])
    (hhidden : (st.piles a).hidden = [])
    (hking : c.rank ≠ Rank.king) :
    irreversibleAt st (Move.tabToFound c) := by
  intro s₁' play hstep' hrun
  rw [hstep] at hstep'
  injection hstep' with hEq
  subst hEq
  obtain ⟨-, a', hp', hs₁eq⟩ := step_tabToFound_inv hstep
  have hae : a' = a := by
    have hx : some a = some a' := hpa.symm.trans hp'
    injection hx with hxE
    exact hxE.symm
  have hbare : BareKing (s₁.piles a) := by
    rw [hs₁eq, hae]
    show BareKing (if a = a
        then Pile.afterRunRemoved (st.piles a) (chop (st.piles a).faceUp)
        else st.piles a)
    rw [ite_eq_left rfl, hchop, afterRunRemoved_faceUp_empty_self hhidden]
    exact ⟨hhidden, True.intro⟩
  have hd := bare_king_run play s₁ st a hbare hrun
  obtain ⟨-, hkc⟩ := hd
  have hface : (st.piles a).faceUp = [c] := by
    obtain ⟨-, hlast⟩ := pileOfTop_top hpa
    rw [lastOf_chop hlast, hchop, List.nil_append]
  rw [hface] at hkc
  exact absurd hkc hking

/-- The `.tabToTab` sibling: moving the *whole* face-up content of a
hidden-free pile away is a commitment whenever the moved run is not
king-headed — the emptied seat obeys the same receive-only-kings
discipline, and the run can never come back to an empty seat under
a non-king head. -/
theorem tabToTab_irreversible_of_bare_nonking {st : State} {c : Card} {b : Base}
    {a : Anchor} {s₁ : State}
    (hstep : State.step st (Move.tabToTab c b) = some s₁)
    (hh : st.pileHolding c = some a)
    (hpre : below c (st.piles a).faceUp = [])
    (hhidden : (st.piles a).hidden = [])
    (hfr : fromCard c (st.piles a).faceUp ≠ [])
    (hking : c.rank ≠ Rank.king) :
    irreversibleAt st (Move.tabToTab c b) := by
  intro s₁' play hstep' hrun
  rw [hstep] at hstep'
  injection hstep' with hEq
  subst hEq
  obtain ⟨a₀, hh₀, hcp, hfr₀, hs₁eq⟩ := step_tabToTab_inv hstep
  have hae : a₀ = a := by
    have hx : some a = some a₀ := hh.symm.trans hh₀
    injection hx with hxE
    exact hxE.symm
  rw [hae] at hfr₀
  have hbare : BareKing (s₁.piles a) := by
    rw [hs₁eq, hae, hpre]
    have hself : BareKing
        ((st.setPile a (Pile.afterRunRemoved (st.piles a) ([] : List Card))).piles a) := by
      rw [setPile_piles_self_any, afterRunRemoved_faceUp_empty_self hhidden]
      exact ⟨hhidden, True.intro⟩
    have hEmptyM1 : ((st.setPile a
        (Pile.afterRunRemoved (st.piles a) ([] : List Card))).piles) a
        = ⟨[], ([] : List Card)⟩ := by
      rw [setPile_piles_self_any, afterRunRemoved_faceUp_empty_self hhidden, hhidden]
    cases b with
    | inl k =>
        obtain ⟨his, -⟩ := canPlace_inl hcp
        have hka : k ≠ a := by
          intro hcon
          rw [hcon] at his
          obtain ⟨-, hfe⟩ := (Pile.isEmpty_eq (st.piles a)).mp his
          rw [hfe] at hfr₀
          exact absurd rfl hfr₀
        rw [putRun_piles_inl]
        show BareKing (if a = k
            then (⟨[], fromCard c (st.piles a).faceUp⟩ : Pile)
            else (st.setPile a (Pile.afterRunRemoved (st.piles a) ([] : List Card))).piles a)
        rw [ite_eq_right (fun hcon => hka hcon.symm)]
        exact hself
    | inr z =>
        cases hz' : (st.setPile a
            (Pile.afterRunRemoved (st.piles a) ([] : List Card))).pileOfTop z with
        | none =>
            rw [putRun_inr_none hz']
            exact hself
        | some j =>
            rw [putRun_piles_inr _ _ _ _ hz']
            show BareKing (if a = j
                then { (st.setPile a (Pile.afterRunRemoved (st.piles a) ([] : List Card))).piles j with
                       faceUp := ((st.setPile a
                         (Pile.afterRunRemoved (st.piles a) ([] : List Card))).piles j).faceUp
                         ++ fromCard c (st.piles a).faceUp }
                else (st.setPile a (Pile.afterRunRemoved (st.piles a) ([] : List Card))).piles a)
            by_cases hja : j = a
            · rw [hja] at hz'
              exact absurd hz' (pileOfTop_ne_of_empty hEmptyM1 z)
            · rw [ite_eq_right (fun hcon => hja hcon.symm)]
              exact hself
  have hd := bare_king_run play s₁ st a hbare hrun
  obtain ⟨-, hkc⟩ := hd
  have hface : (st.piles a).faceUp = fromCard c (st.piles a).faceUp := by
    have hj := below_join (c := c) ((st.piles a).faceUp)
    rw [hpre, List.nil_append] at hj
    exact hj.symm
  obtain ⟨ttr, hrt⟩ := fromCard_head rfl hfr
  rw [hface] at hkc
  rw [hrt] at hkc
  exact absurd hkc hking

/-! ## The universal waste rows -/

/-- Waste-consuming moves are full commitments at every position,
WF or wild: the cycle count strictly drops, and it never rises
along any play. -/
theorem irreversibleAt_wasteToFound (st : State) (c : Card) :
    irreversibleAt st (Move.wasteToFound c) := by
  intro s₁ play hstep hrun
  have hdrop := cycleCount_step_wasteToFound hstep
  have hle := mono_run cycleCount (fun _ _ _ hst => cycleCount_step hst) hrun
  omega

/-- The `.wasteToTab` sibling: same measure, same shape. -/
theorem irreversibleAt_wasteToTab (st : State) (c : Card) (b : Base) :
    irreversibleAt st (Move.wasteToTab c b) := by
  intro s₁ play hstep hrun
  have hdrop := cycleCount_step_wasteToTab hstep
  have hle := mono_run cycleCount (fun _ _ _ hst => cycleCount_step hst) hrun
  omega

/-! ## The draw rows -/

/-- The additive take-drop reassembly (farm-normal private copy of
the Phase helper; dedup at merge). -/
private theorem take_drop_join : ∀ (n : Nat) (l : List Card),
    l.take n ++ l.drop n = l := by
  intro n
  induction n with
  | zero => intro l; simp
  | succ m ih =>
      intro l
      cases l with
      | nil => rfl
      | cons x t =>
          show (x :: t).take (m + 1) ++ (x :: t).drop (m + 1) = x :: t
          show x :: t.take m ++ (x :: t).drop (m + 1) = x :: t
          show x :: (t.take m ++ t.drop m) = x :: t
          exact congrArg (x :: ·) (ih t)

/-- A recycle at the end, waste present (private copy of the Phase
helper). -/
private theorem recycle_nil' {st : State} (h1 : st.stock = ([] : List Card))
    (h2 : st.waste ≠ []) :
    State.recycle st = { st with stock := st.waste.reverse, waste := [] } := by
  obtain ⟨x, t, hcon⟩ := list_cons_of_ne_nil h2
  simp only [State.recycle, h1, hcon]

/-- A recycle with stock present is the identity (private copy). -/
private theorem recycle_keep' {st : State} (h : st.stock ≠ []) : State.recycle st = st := by
  obtain ⟨c, t, hcon⟩ := list_cons_of_ne_nil h
  simp only [State.recycle, hcon]

/-- Dealing from a nonempty stock has the recorded shape (private
copy). -/
private theorem dealStock_eq_of_ne_nil' {st : State} (h : st.stock ≠ []) :
    State.dealStock st = some
      { st with stock := (State.dealUpTo st.drawStep st.stock).2,
                waste := (State.dealUpTo st.drawStep st.stock).1.reverse ++ st.waste } := by
  obtain ⟨c, t, hcon⟩ := list_cons_of_ne_nil h
  simp only [State.dealStock, hcon]

/-- The deal cut is the take-drop split (private copy). -/
private theorem dealUpTo_eq_take_drop' (k : Nat) : ∀ (l : List Card),
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

/-- One plain draw (stock nonempty, no recycle): the recorded
take-drop shape (private copy). -/
private theorem plain_draw_shape' {x : State} (hne : x.stock ≠ []) :
    x.stepDraw = some
      { x with stock := x.stock.drop x.drawStep,
               waste := (x.stock.take x.drawStep).reverse ++ x.waste } := by
  rw [State.stepDraw, recycle_keep' hne, dealStock_eq_of_ne_nil' hne,
    dealUpTo_eq_take_drop']

/-- One pass-end draw (empty stock, nonempty waste): the recycle
then a clipped deal (private copy). -/
private theorem base_draw_shape' {x : State} (hstock : x.stock = ([] : List Card))
    (hw : x.waste ≠ []) :
    x.stepDraw = some
      { x with stock := x.waste.reverse.drop x.drawStep,
               waste := (x.waste.reverse.take x.drawStep).reverse ++ ([] : List Card) } := by
  have hrne : x.waste.reverse ≠ [] := by
    obtain ⟨w0, t0, hwcon⟩ := list_cons_of_ne_nil hw
    intro hc
    have hlen := congrArg List.length hc
    rw [List.length_reverse, List.length_nil] at hlen
    have h1 : x.waste.length = t0.length + 1 := by rw [hwcon, List.length_cons]
    omega
  rw [State.stepDraw, recycle_nil' hstock hw,
    dealStock_eq_of_ne_nil' hrne, dealUpTo_eq_take_drop']

/-- The run-composition shape. -/
private theorem run_cons_shape {s : State} {m : Move} {rest : List Move} {s' w : State}
    (hstep : State.step s m = some s') (hrun : s'.run rest = some w) :
    s.run (m :: rest) = some w := by
  simp only [State.run, hstep]
  exact hrun

/-- The pure-draw drain: from any stock-bearing position, some
pure-draw play drains the stock to the pass base, ending with the
whole recycle-reversed stock re-dealt onto the waste. -/
private theorem drain_to_pass : ∀ (n : Nat) (l : List Card) (s : State), l.length ≤ n →
    0 < s.drawStep → s.stock = l →
    ∃ play, s.run play = some
      { s with stock := ([] : List Card), waste := l.reverse ++ s.waste } := by
  intro n
  induction n with
  | zero =>
      intro l s hlen hd hstock
      have hnil : l = [] := by
        cases l with
        | nil => rfl
        | cons w t =>
            have h1 : (w :: t).length = t.length + 1 := rfl
            omega
      subst hnil
      refine ⟨[], ?_⟩
      have hrfl : s.run [] = some s := rfl
      rw [hrfl]
      refine congrArg some (State.ext rfl rfl hstock ?_ rfl)
      rfl
  | succ n ih =>
      intro l s hlen hd hstock
      have hsplit : l = [] ∨ ∃ w t, l = w :: t := by
        cases l with
        | nil => exact Or.inl rfl
        | cons w t => exact Or.inr ⟨w, t, rfl⟩
      rcases hsplit with hnil | ⟨w, t, hcon⟩
      · subst hnil
        refine ⟨[], ?_⟩
        have hrfl : s.run [] = some s := rfl
        rw [hrfl]
        refine congrArg some (State.ext rfl rfl hstock ?_ rfl)
        rfl
      · subst hcon
        have hne : s.stock ≠ [] := by
          intro hc
          rw [hstock] at hc
          exact absurd hc (by simp)
        have hstep : State.step s Move.draw = some
            { s with stock := s.stock.drop s.drawStep, waste := (s.stock.take s.drawStep).reverse ++ s.waste } :=
          plain_draw_shape' hne
        have hdrop : (s.stock.drop s.drawStep).length ≤ n := by
          rw [hstock]
          have hd2 := List.length_drop (l := w :: t) (i := s.drawStep)
          have hl : (w :: t).length = t.length + 1 := rfl
          omega
        have hstock₂ : { s with stock := s.stock.drop s.drawStep, waste := (s.stock.take s.drawStep).reverse ++ s.waste }.stock
            = s.stock.drop s.drawStep := rfl
        obtain ⟨play', hrun'⟩ := ih (s.stock.drop s.drawStep)
          { s with stock := s.stock.drop s.drawStep, waste := (s.stock.take s.drawStep).reverse ++ s.waste }
          hdrop hd hstock₂
        refine ⟨Move.draw :: play', ?_⟩
        refine run_cons_shape hstep ?_
        rw [hrun']
        have hEqd : (s.stock.drop s.drawStep).reverse
            ++ (s.stock.take s.drawStep).reverse = s.stock.reverse := by
          rw [show (s.stock.drop s.drawStep).reverse ++ (s.stock.take s.drawStep).reverse
                = ((s.stock.take s.drawStep) ++ s.stock.drop s.drawStep).reverse from
                by rw [List.reverse_append],
              take_drop_join]
        rw [show (s.stock.drop s.drawStep).reverse
              ++ ((s.stock.take s.drawStep).reverse ++ s.waste)
              = ((s.stock.drop s.drawStep).reverse ++ (s.stock.take s.drawStep).reverse) ++ s.waste from
              by rw [← List.append_assoc],
            hEqd]
        refine congrArg some (State.ext rfl rfl rfl ?_ rfl)
        rw [hstock]

/-- **The pass-base round trip.**  Drawing at the pass base (empty
stock, nonempty waste, positive draw step) is undone by a
pure-draw play: a small waste re-deals wholesale (the landed
`selfRecycle` row), a larger one drains the recycled remainder
back onto the waste in its original arrangement. -/
theorem draw_passBase_reversibleW {st : State}
    (hstock : st.stock = ([] : List Card)) (hw : st.waste ≠ []) (hd : 0 < st.drawStep) :
    reversibleAtW st Move.draw := by
  by_cases hsize : st.waste.length ≤ st.drawStep
  · exact draw_reversible_selfRecycleW hstock hw hsize
  · have hstep : State.step st Move.draw = some
        { st with stock := st.waste.reverse.drop st.drawStep,
                  waste := (st.waste.reverse.take st.drawStep).reverse ++ ([] : List Card) } :=
      base_draw_shape' hstock hw
    have hdropLen : (st.waste.reverse.drop st.drawStep).length ≤ st.waste.length := by
      have hd2 := List.length_drop (l := st.waste.reverse) (i := st.drawStep)
      have hrev : st.waste.reverse.length = st.waste.length := by rw [List.length_reverse]
      omega
    have hstock₂ : { st with stock := st.waste.reverse.drop st.drawStep, waste := (st.waste.reverse.take st.drawStep).reverse ++ ([] : List Card) }.stock
        = st.waste.reverse.drop st.drawStep := rfl
    have hstepPos : 0 < { st with stock := st.waste.reverse.drop st.drawStep, waste := (st.waste.reverse.take st.drawStep).reverse ++ ([] : List Card) }.drawStep := hd
    obtain ⟨play, hrun⟩ := drain_to_pass st.waste.length
      (st.waste.reverse.drop st.drawStep)
      { st with stock := st.waste.reverse.drop st.drawStep, waste := (st.waste.reverse.take st.drawStep).reverse ++ ([] : List Card) }
      hdropLen hstepPos hstock₂
    refine ⟨_, play, hstep, ?_⟩
    rw [hrun]
    have hwE : (st.waste.reverse.drop st.drawStep).reverse
        ++ ((st.waste.reverse.take st.drawStep).reverse ++ ([] : List Card))
        = st.waste := by
      rw [List.append_nil,
        show (st.waste.reverse.drop st.drawStep).reverse
            ++ (st.waste.reverse.take st.drawStep).reverse
            = ((st.waste.reverse.take st.drawStep) ++ st.waste.reverse.drop st.drawStep).reverse from
            by rw [List.reverse_append],
        take_drop_join, List.reverse_reverse]
    refine congrArg some (State.ext rfl rfl hstock.symm hwE rfl)

/-! ## The `.tabToTab` mirror-move undos

A successful `.tabToTab` is undone by moving the very run back.
Both undo lemmas are stated with local premises (no `State.WF`
anywhere), each excluding a genuine wild-state corner, mirroring
the `foundToTab_undo` / `tabToFound_undo_under` discipline of
`Orig.Irreversible`: the searches of the *successor* (and, one
level down, of the successor after its own run removal) consult
the whole position, and a doubled card or a self-aimed landing can
send them elsewhere.  At `WF` states every premise below is
discharged by the card-count uniqueness and the `runOK` fit — that
is `tabToTabClass`. -/

/-- A no-hidden run removal of an emptied pile is the empty pile
(farm copy of `Orig.Irreversible`'s private helper; dedup at
merge). -/
private theorem afterRunRemoved_empty_eq' (p : Pile) (h : p.hidden = []) :
    Pile.afterRunRemoved p ([] : List Card) = ⟨[], ([] : List Card)⟩ := by
  rcases p with ⟨hlist, flist⟩
  cases hlist with
  | nil => rfl
  | cons x xs => exact absurd h (by simp)

/-- A refused `.tabToTab` head search makes the move vacuously
irreversible. -/
private theorem step_tabToTab_none_of_holding {st : State} {c : Card} {b : Base}
    (h : st.pileHolding c = none) : State.step st (Move.tabToTab c b) = none := by
  simp only [State.step, h]

/-- A refused placement guard makes the move vacuously irreversible. -/
private theorem step_tabToTab_none_of_cp {st : State} {c : Card} {b : Base} {a : Anchor}
    (hh : st.pileHolding c = some a) (h : st.canPlace c b = false) :
    State.step st (Move.tabToTab c b) = none := by
  simp only [State.step, hh]
  rw [ite_eq_right (fun hcond => by rw [h] at hcond; exact Bool.noConfusion hcond)]

/-- A passing `.tabToTab` guard produces the recorded successor
(the run from the head card is nonempty because the head is
present). -/
private theorem step_tabToTab_some {st : State} {c : Card} {b : Base} {a : Anchor}
    (hh : st.pileHolding c = some a) (hcp : st.canPlace c b = true) :
    ∃ s₁, State.step st (Move.tabToTab c b) = some s₁ := by
  have hmem : c ∈ (st.piles a).faceUp := pileHolding_mem hh
  have hne : fromCard c (st.piles a).faceUp ≠ [] := fromCard_ne_of_mem hmem
  refine ⟨(st.setPile a
      (Pile.afterRunRemoved (st.piles a) (below c (st.piles a).faceUp))).putRun
    (fromCard c (st.piles a).faceUp) b, ?_⟩
  simp only [State.step, hh, hcp]
  cases hList : fromCard c (st.piles a).faceUp with
  | nil => exact absurd hList hne
  | cons w r => rfl

/-- The shared restoration body of the bare `.tabToTab` undo:
at `s₁` — read through the two exhumed facts `hs₁A` (the emptied
source seat) and `hs₁K` (the landing pile's exact successor
content) — the mirror move `.tabToTab c (Sum.inl a)` returns the
origin in one step.  Local (wild-state) lemma; every premise is
discharged at `WF` states by the classification. -/
private theorem tabToTab_bare_rtp {st : State} {c : Card} {b : Base} {a k : Anchor}
    {tr : List Card} {s₁ : State}
    (hs₁ : s₁ = (st.setPile a ⟨[], ([] : List Card)⟩).putRun
      (fromCard c (st.piles a).faceUp) b)
    (hrt : fromCard c (st.piles a).faceUp = c :: tr)
    (hface : (st.piles a).faceUp = c :: tr)
    (hhidden : (st.piles a).hidden = [])
    (hking : c.rank = Rank.king)
    (hhold : s₁.pileHolding c = some k)
    (hs₁A : s₁.piles a = ⟨[], ([] : List Card)⟩)
    (hs₁K : s₁.piles k = ⟨(st.piles k).hidden,
      (st.piles k).faceUp ++ fromCard c (st.piles a).faceUp⟩)
    (hkeep : ∀ y, y ≠ a → y ≠ k → s₁.piles y = st.piles y)
    (hcN : c ∉ (st.piles k).faceUp)
    (hka : k ≠ a)
    (hKE : (st.piles k).faceUp = [] → (st.piles k).hidden = []) :
    s₁.run [Move.tabToTab c (Sum.inl a)] = some st := by
  -- successor accessor facts
  have hsF : ∀ σ, s₁.found σ = st.found σ := by
    intro σ
    rw [hs₁, putRun_found, setPile_found]
  have hsS : s₁.stock = st.stock := by rw [hs₁, putRun_stock, setPile_stock]
  have hsW : s₁.waste = st.waste := by rw [hs₁, putRun_waste, setPile_waste]
  have hsD : s₁.drawStep = st.drawStep := by
    rw [hs₁, putRun_drawStep, setPile_drawStep]
  -- the landing pile read, as the mirror needs it
  have hKfaceUp : (s₁.piles k).faceUp =
      (st.piles k).faceUp ++ fromCard c (st.piles a).faceUp :=
    congrArg (fun p => p.faceUp) hs₁K
  have hKhidden : (s₁.piles k).hidden = (st.piles k).hidden :=
    congrArg (fun p => p.hidden) hs₁K
  have hexcl := below_fromCard_excl (c := c) ((st.piles k).faceUp)
    (fromCard c (st.piles a).faceUp) hcN
  have hbelowK : below c (s₁.piles k).faceUp = (st.piles k).faceUp := by
    have h1 : below c (s₁.piles k).faceUp
        = below c ((st.piles k).faceUp ++ fromCard c (st.piles a).faceUp) := by
      rw [hKfaceUp]
    rw [h1, hexcl.1, hrt, below_head_eq, List.append_nil]
  have hrunK : fromCard c (s₁.piles k).faceUp = c :: tr := by
    have h1 : fromCard c (s₁.piles k).faceUp
        = fromCard c ((st.piles k).faceUp ++ fromCard c (st.piles a).faceUp) := by
      rw [hKfaceUp]
    rw [h1, hexcl.2, hrt, fromCard_head_eq]
  have hcp1 : s₁.canPlace c (Sum.inl a) = true := by
    show ((s₁.piles a).isEmpty && decide (c.rank = Rank.king)) = true
    rw [hs₁A, decide_eq_true hking]
    rfl
  have hstep2 : State.step s₁ (Move.tabToTab c (Sum.inl a)) = some st := by
    simp only [State.step, hhold, hcp1, hrunK]
    refine congrArg some (?_ :
      (s₁.setPile k (Pile.afterRunRemoved (s₁.piles k)
          (below c (s₁.piles k).faceUp))).putRun (c :: tr) (Sum.inl a) = st)
    rw [show (s₁.setPile k (Pile.afterRunRemoved (s₁.piles k)
        (below c (s₁.piles k).faceUp))).putRun (c :: tr) (Sum.inl a)
        = (s₁.setPile k (Pile.afterRunRemoved (s₁.piles k)
            (below c (s₁.piles k).faceUp))).setPile a
            ⟨[], c :: tr⟩ from rfl]
    refine State.ext (funext fun σ => ?_) (funext fun y => ?_) ?_ ?_ ?_
    · rw [setPile_found, setPile_found, hsF σ]
    · by_cases hya : y = a
      · rw [hya]
        show (if a = a then ⟨[], c :: tr⟩
          else (if a = k then
              Pile.afterRunRemoved (s₁.piles k) (below c (s₁.piles k).faceUp)
            else s₁.piles a)) = st.piles a
        rw [ite_eq_left rfl]
        refine Pile.ext ?_ ?_
        · rw [hhidden]
        · rw [hface]
      · by_cases hyk : y = k
        · rw [hyk]
          show (if k = a then ⟨[], c :: tr⟩
            else (if k = k then
                Pile.afterRunRemoved (s₁.piles k) (below c (s₁.piles k).faceUp)
              else s₁.piles k)) = st.piles k
          rw [ite_eq_right hka, ite_eq_left rfl, hbelowK]
          cases hF2 : (st.piles k).faceUp with
          | nil =>
              rw [afterRunRemoved_empty_eq' _ (hKhidden.trans (hKE hF2))]
              exact Pile.ext (hKE hF2).symm hF2.symm
          | cons w r₂ =>
              exact Pile.ext hKhidden hF2.symm
        · show (if y = a then ⟨[], c :: tr⟩
            else (if y = k then
                Pile.afterRunRemoved (s₁.piles k) (below c (s₁.piles k).faceUp)
              else s₁.piles y)) = st.piles y
          rw [ite_eq_right hya, ite_eq_right hyk]
          exact hkeep y hya hyk
    · exact hsS
    · exact hsW
    · exact hsD
  simp only [State.run, hstep2]

/-- **The bare `.tabToTab` undo, witness form (primary).**  A
successful `.tabToTab` that empties its source pile outright
(`hpre` : nothing sits below the run head; `hhidden` : no hidden
cards under it — so the run out is the pile's whole face-up
content) is undone by the mirror move: run back onto the emptied
seat, `.tabToTab c (Sum.inl a)`.

The premises are local (no `State.WF` anywhere) and each excludes
a genuine wild-state corner:

* `hking` — the empty-seat placement demands a king; nothing at a
  wild state ties the run head's rank to the seat it left.
* `hhold` — the undo's own head search must locate the run at the
  landing pile `k`; a doubled `c` face up in an earlier pile would
  send the undo's removal at the wrong seat.
* `hseat` — the move's own inner placement search, run at the
  half-updated board `st.setPile a ⟨[], []⟩` (the source seat
  already emptied), pins the landing pile `k` — the `.tabToTab`
  analogue of `foundToTab_undo`'s search pin.  At a wild state the
  removal changes what that inner search sees; the premise hands
  the undo the landing seat as data.
* `hkeep` — every pile other than the source seat and the landing
  pile is untouched.
* `hcN` — the landing pile's prior content does not itself hold
  `c` (at a wild state it could, and the undo's removal at `k`
  would then cut into preexisting content); it also forces
  `k ≠ a`. -/
theorem tabToTab_undo_bare {st : State} {c : Card} {b : Base} {a k : Anchor} {s₁ : State}
    (hstep : State.step st (Move.tabToTab c b) = some s₁)
    (hh : st.pileHolding c = some a)
    (hpre : below c (st.piles a).faceUp = [])
    (hhidden : (st.piles a).hidden = [])
    (hking : c.rank = Rank.king)
    (hhold : s₁.pileHolding c = some k)
    (hseat : b = Sum.inl k ∨ ∃ z', b = Sum.inr z' ∧
      (st.setPile a ⟨[], ([] : List Card)⟩ : State).pileOfTop z' = some k)
    (hkeep : ∀ y, y ≠ a → y ≠ k → s₁.piles y = st.piles y)
    (hcN : c ∉ (st.piles k).faceUp) :
    reversibleAtW st (Move.tabToTab c b) := by
  obtain ⟨a₀, hh₀, hcp, hfr, hs₁⟩ := step_tabToTab_inv hstep
  rw [hh] at hh₀
  injection hh₀ with haa
  subst haa
  obtain ⟨tr, hrt⟩ := fromCard_head rfl hfr
  have hface : (st.piles a).faceUp = c :: tr := by
    have hj := below_join (c := c) ((st.piles a).faceUp)
    rw [hpre, List.nil_append] at hj
    rw [← hj, hrt]
  have hka : k ≠ a := fun hcon => hcN (by rw [hcon]; exact pileHolding_mem hh)
  -- the emptied source pile, as a literal
  have haremf : Pile.afterRunRemoved (st.piles a) (below c (st.piles a).faceUp) =
      ⟨[], ([] : List Card)⟩ := by
    rw [hpre]
    exact afterRunRemoved_empty_eq' _ hhidden
  rw [haremf] at hs₁
  have hmidK : (st.setPile a ⟨[], ([] : List Card)⟩ : State).piles k = st.piles k := by
    show (if k = a then ⟨[], ([] : List Card)⟩ else st.piles k) = _
    rw [ite_eq_right hka]
  have hs₁A : s₁.piles a = ⟨[], ([] : List Card)⟩ := by
    rw [hs₁]
    rcases hseat with rfl | ⟨z', rfl, hmidPin⟩
    · rw [putRun_piles_inl]
      show (if a = k then ⟨[], fromCard c (st.piles a).faceUp⟩
        else (st.setPile a ⟨[], ([] : List Card)⟩).piles a) = _
      rw [ite_eq_right (Ne.symm hka)]
      show (if a = a then ⟨[], ([] : List Card)⟩ else st.piles a) = _
      rw [ite_eq_left rfl]
    · rw [putRun_piles_inr _ _ _ _ hmidPin]
      show (if a = k then
          { (st.setPile a ⟨[], ([] : List Card)⟩).piles k with
            faceUp := ((st.setPile a ⟨[], ([] : List Card)⟩).piles k).faceUp
              ++ fromCard c (st.piles a).faceUp }
          else (st.setPile a ⟨[], ([] : List Card)⟩).piles a) = _
      rw [ite_eq_right (Ne.symm hka)]
      show (if a = a then ⟨[], ([] : List Card)⟩ else st.piles a) = _
      rw [ite_eq_left rfl]
  have hs₁K : s₁.piles k = ⟨(st.piles k).hidden,
      (st.piles k).faceUp ++ fromCard c (st.piles a).faceUp⟩ := by
    rcases hseat with rfl | ⟨z', rfl, hmidPin⟩
    · rw [hs₁, putRun_piles_inl]
      show (if k = k then ⟨[], fromCard c (st.piles a).faceUp⟩
        else (st.setPile a ⟨[], ([] : List Card)⟩).piles k) = _
      rw [ite_eq_left rfl]
      obtain ⟨hhE, hfE⟩ := (Pile.isEmpty_eq _).mp (canPlace_inl hcp).1
      refine Pile.ext ?_ ?_
      · rw [hhE]
      · rw [hfE, List.nil_append]
    · rw [hs₁, putRun_piles_inr _ _ _ _ hmidPin]
      show (if k = k then
          { (st.setPile a ⟨[], ([] : List Card)⟩).piles k with
            faceUp := ((st.setPile a ⟨[], ([] : List Card)⟩).piles k).faceUp
              ++ fromCard c (st.piles a).faceUp }
          else (st.setPile a ⟨[], ([] : List Card)⟩).piles k) = _
      rw [ite_eq_left rfl, hmidK]
  have hKE : (st.piles k).faceUp = [] → (st.piles k).hidden = [] := by
    rcases hseat with rfl | ⟨z', rfl, hmidPin⟩
    · intro _
      exact (Pile.isEmpty_eq _).mp (canPlace_inl hcp).1 |>.1
    · intro hcon
      have hne := (pileOfTop_top hmidPin).1
      rw [hmidK] at hne
      exact absurd hcon hne
  exact ⟨s₁, [Move.tabToTab c (Sum.inl a)], hstep,
    tabToTab_bare_rtp hs₁ hrt hface hhidden hking hhold hs₁A hs₁K hkeep hcN hka hKE⟩

/-- The negative form of the bare `.tabToTab` undo.  Witness
form: `tabToTab_undo_bare`. -/
theorem tabToTab_reversible_bare {st : State} {c : Card} {b : Base} {a k : Anchor}
    {s₁ : State}
    (hstep : State.step st (Move.tabToTab c b) = some s₁)
    (hh : st.pileHolding c = some a)
    (hpre : below c (st.piles a).faceUp = [])
    (hhidden : (st.piles a).hidden = [])
    (hking : c.rank = Rank.king)
    (hhold : s₁.pileHolding c = some k)
    (hseat : b = Sum.inl k ∨ ∃ z', b = Sum.inr z' ∧
      (st.setPile a ⟨[], ([] : List Card)⟩ : State).pileOfTop z' = some k)
    (hkeep : ∀ y, y ≠ a → y ≠ k → s₁.piles y = st.piles y)
    (hcN : c ∉ (st.piles k).faceUp) :
    reversibleAt st (Move.tabToTab c b) :=
  reversibleAt_of_W (tabToTab_undo_bare hstep hh hpre hhidden hking hhold hseat hkeep hcN)

/-- The shared restoration body of the under `.tabToTab` undo:
at `s₁`, with the seat card `z` pinned (`hz`), the fit `hsit`,
the successor-side search facts (`hzOnly`-derived), and the
landing pile's own search pin, the mirror move `.tabToTab c
(Sum.inr z)` — run back onto the card it left — returns `st`.
Local (wild-state) lemma; every premise is discharged at `WF`
states by the classification. -/
private theorem tabToTab_under_rtp {st : State} {c : Card} {b : Base} {a k : Anchor}
    {z : Card} {tr : List Card} {s₁ : State}
    (hs₁ : s₁ = (st.setPile a
        (Pile.afterRunRemoved (st.piles a) (below c (st.piles a).faceUp))).putRun
      (fromCard c (st.piles a).faceUp) b)
    (hrt : fromCard c (st.piles a).faceUp = c :: tr)
    (hz : lastOf (below c (st.piles a).faceUp) = some z)
    (hsit : canSitOn c z = true)
    (hhold : s₁.pileHolding c = some k)
    (hsA : s₁.piles a = ⟨(st.piles a).hidden, below c (st.piles a).faceUp⟩)
    (hs₁K : s₁.piles k = ⟨(st.piles k).hidden,
      (st.piles k).faceUp ++ fromCard c (st.piles a).faceUp⟩)
    (hkeep : ∀ y, y ≠ a → y ≠ k → s₁.piles y = st.piles y)
    (hcN : c ∉ (st.piles k).faceUp)
    (hka : k ≠ a)
    (hzOnly : ∀ y, y ≠ a → (s₁.piles y).top ≠ some z)
    (hzK : (st.piles k).top ≠ some z)
    (hKE : (st.piles k).faceUp = [] → (st.piles k).hidden = []) :
    s₁.run [Move.tabToTab c (Sum.inr z)] = some st := by
  -- successor accessor facts
  have hsF : ∀ σ, s₁.found σ = st.found σ := by
    intro σ
    rw [hs₁, putRun_found, setPile_found]
  have hsS : s₁.stock = st.stock := by rw [hs₁, putRun_stock, setPile_stock]
  have hsW : s₁.waste = st.waste := by rw [hs₁, putRun_waste, setPile_waste]
  have hsD : s₁.drawStep = st.drawStep := by
    rw [hs₁, putRun_drawStep, setPile_drawStep]
  -- the landing pile read, as the mirror needs it
  have hKfaceUp : (s₁.piles k).faceUp =
      (st.piles k).faceUp ++ fromCard c (st.piles a).faceUp :=
    congrArg (fun p => p.faceUp) hs₁K
  have hKhidden : (s₁.piles k).hidden = (st.piles k).hidden :=
    congrArg (fun p => p.hidden) hs₁K
  have hexcl := below_fromCard_excl (c := c) ((st.piles k).faceUp)
    (fromCard c (st.piles a).faceUp) hcN
  have hbelowK : below c (s₁.piles k).faceUp = (st.piles k).faceUp := by
    have h1 : below c (s₁.piles k).faceUp
        = below c ((st.piles k).faceUp ++ fromCard c (st.piles a).faceUp) := by
      rw [hKfaceUp]
    rw [h1, hexcl.1, hrt, below_head_eq, List.append_nil]
  have hrunK : fromCard c (s₁.piles k).faceUp = c :: tr := by
    have h1 : fromCard c (s₁.piles k).faceUp
        = fromCard c ((st.piles k).faceUp ++ fromCard c (st.piles a).faceUp) := by
      rw [hKfaceUp]
    rw [h1, hexcl.2, hrt, fromCard_head_eq]
  -- the base search pins, first at s₁, then after the mirror's own removal
  have haTop : (s₁.piles a).top = some z := by
    show lastOf ((s₁.piles a).faceUp) = some z
    rw [show (s₁.piles a).faceUp = below c (st.piles a).faceUp from
      congrArg (fun p => p.faceUp) hsA]
    exact hz
  have hsTop : s₁.pileOfTop z = some a := by
    show firstWhere (fun x => decide ((s₁.piles x).top = some z)) Anchor.all = some a
    exact firstWhere_find (Anchor.mem_all a) (decide_eq_true haTop)
      (fun y hy hyne => decide_false_of_not (hzOnly y hyne))
  have hmidA : (s₁.setPile k (Pile.afterRunRemoved (s₁.piles k)
      (below c (s₁.piles k).faceUp)) : State).piles a = s₁.piles a := by
    show (if a = k then Pile.afterRunRemoved (s₁.piles k)
        (below c (s₁.piles k).faceUp) else s₁.piles a) = _
    rw [ite_eq_right (Ne.symm hka)]
  have hmidTop : ((s₁.setPile k (Pile.afterRunRemoved (s₁.piles k)
      (below c (s₁.piles k).faceUp)) : State).piles a).top = some z := by
    rw [hmidA]
    exact haTop
  have hknotN : ((s₁.setPile k (Pile.afterRunRemoved (s₁.piles k)
      (below c (s₁.piles k).faceUp)) : State).piles k).top ≠ some z := by
    show (if k = k then Pile.afterRunRemoved (s₁.piles k)
        (below c (s₁.piles k).faceUp) else s₁.piles k).top ≠ some z
    rw [ite_eq_left rfl, hbelowK]
    cases hF2 : (st.piles k).faceUp with
    | nil =>
        rw [afterRunRemoved_empty_eq' _ (hKhidden.trans (hKE hF2))]
        intro htop
        nomatch htop
    | cons w r₂ =>
        exact fun htop => hzK (show (st.piles k).top = some z from by
          show lastOf ((st.piles k).faceUp) = some z
          rw [hF2]
          exact htop)
  have hzN' : (s₁.setPile k (Pile.afterRunRemoved (s₁.piles k)
      (below c (s₁.piles k).faceUp)) : State).pileOfTop z = some a :=
    topPin2 hmidTop (fun y hya hyk => by
      show (if y = k then Pile.afterRunRemoved (s₁.piles k)
          (below c (s₁.piles k).faceUp) else s₁.piles y) = s₁.piles y
      rw [ite_eq_right hyk])
      hknotN (fun y hya _ => hzOnly y hya)
  have hcp1 : s₁.canPlace c (Sum.inr z) = true := by
    show (match s₁.pileOfTop z with
      | some _ => canSitOn c z | none => false) = true
    rw [hsTop]
    exact hsit
  have hstep2 : State.step s₁ (Move.tabToTab c (Sum.inr z)) = some st := by
    simp only [State.step, hhold, hcp1, hrunK]
    refine congrArg some (?_ :
      (s₁.setPile k (Pile.afterRunRemoved (s₁.piles k)
          (below c (s₁.piles k).faceUp))).putRun (c :: tr) (Sum.inr z) = st)
    refine State.ext (funext fun σ => ?_) (funext fun y => ?_) ?_ ?_ ?_
    · rw [putRun_found, setPile_found, hsF σ]
    · by_cases hya : y = a
      · rw [hya, putRun_piles_inr _ _ _ _ hzN']
        show (if a = a then
            { (s₁.setPile k (Pile.afterRunRemoved (s₁.piles k)
                (below c (s₁.piles k).faceUp)) : State).piles a with
              faceUp := ((s₁.setPile k (Pile.afterRunRemoved (s₁.piles k)
                  (below c (s₁.piles k).faceUp)) : State).piles a).faceUp ++ c :: tr }
            else (s₁.setPile k (Pile.afterRunRemoved (s₁.piles k)
                (below c (s₁.piles k).faceUp)) : State).piles a) = st.piles a
        rw [ite_eq_left rfl, hmidA]
        refine Pile.ext ?_ ?_
        · exact congrArg (fun p => p.hidden) hsA
        · have hj := below_join (c := c) ((st.piles a).faceUp)
          rw [hrt] at hj
          rw [show (s₁.piles a).faceUp = below c (st.piles a).faceUp from
            congrArg (fun p => p.faceUp) hsA]
          exact hj
      · by_cases hyk : y = k
        · rw [hyk, putRun_piles_inr _ _ _ _ hzN']
          show (if k = a then
              { (s₁.setPile k (Pile.afterRunRemoved (s₁.piles k)
                  (below c (s₁.piles k).faceUp)) : State).piles a with
                faceUp := ((s₁.setPile k (Pile.afterRunRemoved (s₁.piles k)
                    (below c (s₁.piles k).faceUp)) : State).piles a).faceUp ++ c :: tr }
              else (s₁.setPile k (Pile.afterRunRemoved (s₁.piles k)
                  (below c (s₁.piles k).faceUp)) : State).piles k) = st.piles k
          rw [ite_eq_right hka]
          show (if k = k then Pile.afterRunRemoved (s₁.piles k)
              (below c (s₁.piles k).faceUp) else s₁.piles k) = st.piles k
          rw [ite_eq_left rfl, hbelowK]
          cases hF2 : (st.piles k).faceUp with
          | nil =>
              rw [afterRunRemoved_empty_eq' _ (hKhidden.trans (hKE hF2))]
              exact Pile.ext (hKE hF2).symm hF2.symm
          | cons w r₂ =>
              exact Pile.ext hKhidden hF2.symm
        · rw [putRun_piles_inr _ _ _ _ hzN']
          show (if y = a then
              { (s₁.setPile k (Pile.afterRunRemoved (s₁.piles k)
                  (below c (s₁.piles k).faceUp)) : State).piles a with
                faceUp := ((s₁.setPile k (Pile.afterRunRemoved (s₁.piles k)
                    (below c (s₁.piles k).faceUp)) : State).piles a).faceUp ++ c :: tr }
              else (s₁.setPile k (Pile.afterRunRemoved (s₁.piles k)
                  (below c (s₁.piles k).faceUp)) : State).piles y) = st.piles y
          rw [ite_eq_right hya]
          show (if y = k then Pile.afterRunRemoved (s₁.piles k)
              (below c (s₁.piles k).faceUp) else s₁.piles y) = st.piles y
          rw [ite_eq_right hyk]
          exact hkeep y hya hyk
    · rw [putRun_stock, setPile_stock]
      exact hsS
    · rw [putRun_waste, setPile_waste]
      exact hsW
    · rw [putRun_drawStep, setPile_drawStep]
      exact hsD
  simp only [State.run, hstep2]

/-- **The under-seat `.tabToTab` undo, witness form (primary).**  A
successful no-reveal `.tabToTab` whose source pile keeps face-up
content below the moved run (`hz` pins that content's top card,
`z`) is undone by the mirror move: run back onto `z`,
`.tabToTab c (Sum.inr z)`.

The premises are local (no `State.WF` anywhere) and each excludes
a genuine wild-state corner (mirroring
`tabToFound_undo_under`'s discipline):

* `hsit` — `canSitOn c z` does *not* follow from the step at a
  wild state: the source run may be freely stacked there.
* `hhold` — the undo's own head search must locate the run at the
  landing pile `k`.
* `hseat` — the move's own inner placement search, run at the
  half-updated board (source pile already chopped), pins the
  landing pile `k`.
* `hkeep` — every pile other than the source seat and the landing
  pile is untouched.
* `hcN` — the landing pile's prior content does not itself hold
  `c` (the undo's reassembly at `k` would otherwise cut into
  preexisting content); it also forces `k ≠ a`.
* `hzOnly` — at the successor, `z` tops the source seat and no
  other pile (a wild successor could hold another `z`-topping pile
  earlier in the search order).
* `hzK` — the landing pile's own prior top is not `z` (the
  mirror's placement asks for `z` through a search that the
  half-restored board presents the landing pile's top to). -/
theorem tabToTab_undo_under {st : State} {c : Card} {b : Base} {a k : Anchor} {z : Card}
    {s₁ : State}
    (hstep : State.step st (Move.tabToTab c b) = some s₁)
    (hh : st.pileHolding c = some a)
    (hz : lastOf (below c (st.piles a).faceUp) = some z)
    (hsit : canSitOn c z = true)
    (hhold : s₁.pileHolding c = some k)
    (hseat : b = Sum.inl k ∨ ∃ z', b = Sum.inr z' ∧
      (st.setPile a (Pile.afterRunRemoved (st.piles a)
        (below c (st.piles a).faceUp)) : State).pileOfTop z' = some k)
    (hkeep : ∀ y, y ≠ a → y ≠ k → s₁.piles y = st.piles y)
    (hcN : c ∉ (st.piles k).faceUp)
    (hzOnly : ∀ y, y ≠ a → (s₁.piles y).top ≠ some z)
    (hzK : (st.piles k).top ≠ some z) :
    reversibleAtW st (Move.tabToTab c b) := by
  obtain ⟨a₀, hh₀, hcp, hfr, hs₁⟩ := step_tabToTab_inv hstep
  rw [hh] at hh₀
  injection hh₀ with haa
  subst haa
  obtain ⟨tr, hrt⟩ := fromCard_head rfl hfr
  have hka : k ≠ a := fun hcon => hcN (by rw [hcon]; exact pileHolding_mem hh)
  have hprene : below c (st.piles a).faceUp ≠ [] := by
    intro hcon
    rw [hcon] at hz
    exact absurd hz (by simp [lastOf])
  -- the source seat keeps its hidden cards and its below part (no
  -- reveal: the below part is nonempty)
  have hsA : s₁.piles a = ⟨(st.piles a).hidden, below c (st.piles a).faceUp⟩ := by
    rw [hs₁]
    rcases hseat with rfl | ⟨z', rfl, hmidPin⟩
    · rw [putRun_piles_inl]
      show (if a = k then ⟨[], fromCard c (st.piles a).faceUp⟩
        else (st.setPile a (Pile.afterRunRemoved (st.piles a)
          (below c (st.piles a).faceUp)) : State).piles a) = _
      rw [ite_eq_right (Ne.symm hka)]
      show (if a = a then Pile.afterRunRemoved (st.piles a)
          (below c (st.piles a).faceUp) else st.piles a) = _
      rw [ite_eq_left rfl]
      cases hF : below c (st.piles a).faceUp with
      | nil => exact absurd hF hprene
      | cons w t₂ => rfl
    · rw [putRun_piles_inr _ _ _ _ hmidPin]
      show (if a = k then
          { (st.setPile a (Pile.afterRunRemoved (st.piles a)
              (below c (st.piles a).faceUp)) : State).piles k with
            faceUp := ((st.setPile a (Pile.afterRunRemoved (st.piles a)
              (below c (st.piles a).faceUp)) : State).piles k).faceUp
              ++ fromCard c (st.piles a).faceUp }
          else (st.setPile a (Pile.afterRunRemoved (st.piles a)
              (below c (st.piles a).faceUp)) : State).piles a) = _
      rw [ite_eq_right (Ne.symm hka)]
      show (if a = a then Pile.afterRunRemoved (st.piles a)
          (below c (st.piles a).faceUp) else st.piles a) = _
      rw [ite_eq_left rfl]
      cases hF : below c (st.piles a).faceUp with
      | nil => exact absurd hF hprene
      | cons w t₂ => rfl
  have hs₁K : s₁.piles k = ⟨(st.piles k).hidden,
      (st.piles k).faceUp ++ fromCard c (st.piles a).faceUp⟩ := by
    rw [hs₁]
    rcases hseat with rfl | ⟨z', rfl, hmidPin⟩
    · rw [putRun_piles_inl]
      show (if k = k then ⟨[], fromCard c (st.piles a).faceUp⟩
        else (st.setPile a (Pile.afterRunRemoved (st.piles a)
          (below c (st.piles a).faceUp)) : State).piles k) = _
      rw [ite_eq_left rfl]
      obtain ⟨hhE, hfE⟩ := (Pile.isEmpty_eq _).mp (canPlace_inl hcp).1
      refine Pile.ext ?_ ?_
      · rw [hhE]
      · rw [hfE, List.nil_append]
    · rw [putRun_piles_inr _ _ _ _ hmidPin]
      show (if k = k then
          { (st.setPile a (Pile.afterRunRemoved (st.piles a)
              (below c (st.piles a).faceUp)) : State).piles k with
            faceUp := ((st.setPile a (Pile.afterRunRemoved (st.piles a)
              (below c (st.piles a).faceUp)) : State).piles k).faceUp
              ++ fromCard c (st.piles a).faceUp }
          else (st.setPile a (Pile.afterRunRemoved (st.piles a)
              (below c (st.piles a).faceUp)) : State).piles k) = _
      rw [ite_eq_left rfl]
      have hmidK : (st.setPile a (Pile.afterRunRemoved (st.piles a)
          (below c (st.piles a).faceUp)) : State).piles k = st.piles k := by
        show (if k = a then Pile.afterRunRemoved (st.piles a)
            (below c (st.piles a).faceUp) else st.piles k) = _
        rw [ite_eq_right hka]
      rw [hmidK]
  have hKE : (st.piles k).faceUp = [] → (st.piles k).hidden = [] := by
    rcases hseat with rfl | ⟨z', rfl, hmidPin⟩
    · intro _
      exact (Pile.isEmpty_eq _).mp (canPlace_inl hcp).1 |>.1
    · intro hcon
      have hne := (pileOfTop_top hmidPin).1
      rw [show (st.setPile a (Pile.afterRunRemoved (st.piles a)
          (below c (st.piles a).faceUp)) : State).piles k = st.piles k from by
        show (if k = a then Pile.afterRunRemoved (st.piles a)
            (below c (st.piles a).faceUp) else st.piles k) = _
        rw [ite_eq_right hka]] at hne
      exact absurd hcon hne
  exact ⟨s₁, [Move.tabToTab c (Sum.inr z)], hstep,
    tabToTab_under_rtp hs₁ hrt hz hsit hhold hsA hs₁K hkeep hcN hka hzOnly hzK hKE⟩

/-- The negative form of the under `.tabToTab` undo.  Witness
form: `tabToTab_undo_under`. -/
theorem tabToTab_reversible_under {st : State} {c : Card} {b : Base} {a k : Anchor}
    {z : Card} {s₁ : State}
    (hstep : State.step st (Move.tabToTab c b) = some s₁)
    (hh : st.pileHolding c = some a)
    (hz : lastOf (below c (st.piles a).faceUp) = some z)
    (hsit : canSitOn c z = true)
    (hhold : s₁.pileHolding c = some k)
    (hseat : b = Sum.inl k ∨ ∃ z', b = Sum.inr z' ∧
      (st.setPile a (Pile.afterRunRemoved (st.piles a)
        (below c (st.piles a).faceUp)) : State).pileOfTop z' = some k)
    (hkeep : ∀ y, y ≠ a → y ≠ k → s₁.piles y = st.piles y)
    (hcN : c ∉ (st.piles k).faceUp)
    (hzOnly : ∀ y, y ≠ a → (s₁.piles y).top ≠ some z)
    (hzK : (st.piles k).top ≠ some z) :
    reversibleAt st (Move.tabToTab c b) :=
  reversibleAt_of_W (tabToTab_undo_under hstep hh hz hsit hhold hseat hkeep hcN hzOnly hzK)

/-! ## The oracle shapes and their classification rows -/


/-- An illegal move is vacuously irreversible: no successor ever
exists to return from. -/
theorem irreversibleAt_of_illegal {st : State} {m : Move}
    (h : State.step st m = none) : irreversibleAt st m := by
  intro s₁ play hstep _
  rw [h] at hstep
  exact absurd hstep (by simp)

/-- A refused `.tabToFound` guard makes the move vacuously
irreversible. -/
private theorem step_tabToFound_none_of_nextUp {st : State} {c : Card}
    (h : st.nextUp c = false) : State.step st (Move.tabToFound c) = none := by
  simp only [State.step, h]
  rfl

private theorem step_tabToFound_none_of_pileOfTop {st : State} {c : Card}
    (hn : st.nextUp c = true) (h : st.pileOfTop c = none) :
    State.step st (Move.tabToFound c) = none := by
  simp only [State.step, hn, h]
  rfl

/-- A passing `.tabToFound` guard produces the recorded successor. -/
private theorem step_tabToFound_some {st : State} {c : Card} {a : Anchor}
    (hn : st.nextUp c = true) (ha : st.pileOfTop c = some a) :
    ∃ s₁, State.step st (Move.tabToFound c) = some s₁ := by
  refine ⟨{ st.setFound c.suit (st.found c.suit ++ [c]) with
    piles := fun a' =>
      if a' = a then Pile.afterRunRemoved (st.piles a) (chop (st.piles a).faceUp)
      else st.piles a' }, ?_⟩
  simp only [State.step, hn, ha]
  rfl

/-- The `.tabToFound` shape: reveal rows irreversible; the bare row
irreversible precisely for non-kings (the landing-seat discipline,
`tabToFound_irreversible_of_bare_nonking`); the under row reversible
at WF (the `tabToFound_undo_under` family with its premises
discharged by the conservation invariant).  Illegal rows read
true. -/
private def tabToFoundIrr (st : State) (c : Card) : Bool :=
  match st.nextUp c with
  | false => true
  | true =>
      match st.pileOfTop c with
      | none => true
      | some a =>
          match chop (st.piles a).faceUp with
          | [] =>
              match (st.piles a).hidden with
              | [] => decide (c.rank ≠ Rank.king)
              | _ :: _ => true
          | _ :: _ => false

theorem tabToFoundClass {st : State} (hwf : st.WF) (c : Card) :
    irreversibleAt st (Move.tabToFound c) ↔ tabToFoundIrr st c = true := by
  by_cases hn : st.nextUp c = true
  · by_cases hloc : st.pileOfTop c = none
    · constructor
      · intro _
        rw [tabToFoundIrr, hn, hloc]
      · intro _
        exact irreversibleAt_of_illegal (step_tabToFound_none_of_pileOfTop hn hloc)
    · obtain ⟨a, ha⟩ := option_some_of_ne_none hloc
      have hred : tabToFoundIrr st c =
          (match chop (st.piles a).faceUp with
          | [] =>
              match (st.piles a).hidden with
              | [] => decide (c.rank ≠ Rank.king)
              | _ :: _ => true
          | _ :: _ => false) := by
        rw [tabToFoundIrr, hn, ha]
      have hstep : ∃ s₁, State.step st (Move.tabToFound c) = some s₁ :=
        step_tabToFound_some hn ha
      cases hchop : chop (st.piles a).faceUp with
      | nil =>
          cases hhidden : (st.piles a).hidden with
          | nil =>
              -- the bare seat: cell value decide (¬ king)
              rw [hred, hchop, hhidden]
              constructor
              · intro hirr
                by_cases hk : c.rank = Rank.king
                · exfalso
                  obtain ⟨s₁, hs₁⟩ := hstep
                  exact not_reversibleAtW_of_irreversibleAt hirr
                    (tabToFound_undo_bare hs₁ ha hchop hhidden hk)
                · exact decide_eq_true hk
              · intro hshape
                obtain ⟨s₁, hs₁⟩ := hstep
                exact tabToFound_irreversible_of_bare_nonking hs₁ ha hchop hhidden
                  (of_decide_eq_true hshape)
          | cons h t1 =>
              -- the reveal commit: hidden total strictly drops
              rw [hred, hchop, hhidden]
              constructor
              · intro _
                rfl
              · intro _
                obtain ⟨s₁, hs₁⟩ := hstep
                exact irr_of_desc hiddenTotal
                  (fun s m s' hst => hiddenTotal_step hst) hs₁
                  (hiddenTotal_step_tabToFound_reveal hs₁ ha hchop
                    (by rw [hhidden]; intro hh; exact absurd hh (by simp)))
      | cons z' preT =>
          -- the under row: reversible at WF, so the shape reads false and
          -- the semantic side can never be irreversible
          rw [hred, hchop]
          constructor
          · intro hirr
            exfalso
            obtain ⟨s₁, hs₁⟩ := hstep
            obtain ⟨zW, hzw0⟩ := lastOf_cons_some preT z'
            have hzw : lastOf (chop (st.piles a).faceUp) = some zW := by
              rw [hchop]
              exact hzw0
            have hsit : canSitOn c zW = true := by
              refine runOK_adjacent_snoc hzw0 ?_
              have hface : (st.piles a).faceUp = chop (st.piles a).faceUp ++ [c] :=
                lastOf_chop (pileOfTop_top ha).2
              have hrunk : runOK (st.piles a).faceUp = true := hwf.2.1 a
              rw [hface, hchop] at hrunk
              exact hrunk
            have hsearch : s₁.pileOfTop zW = some a := by
              obtain ⟨-, a', hp', hs'⟩ := step_tabToFound_inv hs₁
              have hae : a' = a := by
                have hx : some a = some a' := ha.symm.trans hp'
                injection hx with hxE
                exact hxE.symm
              rw [hs', hae]
              have hothers : ∀ a₂, a₂ ≠ a →
                  ((({ found := fun σ => if σ = c.suit then st.found c.suit ++ [c] else st.found σ, piles := fun a'' => if a'' = a then (Pile.afterRunRemoved (st.piles a) (chop (st.piles a).faceUp) : Pile) else st.piles a'', stock := st.stock, waste := st.waste, drawStep := st.drawStep } : State).piles) a₂) = st.piles a₂ := by
                intro a₂ hne₂
                show (if a₂ = a then
                  ((Pile.afterRunRemoved (st.piles a) (chop (st.piles a).faceUp) : Pile))
                  else st.piles a₂) = st.piles a₂
                rw [ite_eq_right hne₂]
              have htop2 : ((({ found := fun σ => if σ = c.suit then st.found c.suit ++ [c] else st.found σ, piles := fun a'' => if a'' = a then (Pile.afterRunRemoved (st.piles a) (chop (st.piles a).faceUp) : Pile) else st.piles a'', stock := st.stock, waste := st.waste, drawStep := st.drawStep } : State).piles a)).top = some zW := by
                show (if a = a then
                    ((Pile.afterRunRemoved (st.piles a) (chop (st.piles a).faceUp) : Pile))
                    else st.piles a).top = some zW
                rw [ite_eq_left rfl]
                show lastOf ((Pile.afterRunRemoved (st.piles a) (chop (st.piles a).faceUp)).faceUp) = some zW
                rw [afterRunRemoved_faceUp_ne (by
                    rw [hchop]; exact fun hh => absurd hh (by simp)), hchop]
                exact hzw0
              have hnost2 : ∀ a₂, a₂ ≠ a → (st.piles a₂).top ≠ some zW :=
                fun a₂ hne₂ => wf_no_other_top hwf (chop_mem (lastOf_mem hzw)) a₂ hne₂
              exact topPin hothers htop2 hnost2
            exact not_reversibleAtW_of_irreversibleAt hirr
              (tabToFound_undo_under hs₁ ha hzw hsit hsearch)
          · intro hfalse
            exact absurd hfalse (by simp)
  · have hf : st.nextUp c = false := by
      cases hnf : st.nextUp c with
      | true => exact absurd hnf hn
      | false => rfl
    constructor
    · intro _
      rw [tabToFoundIrr, hf]
    · intro _
      exact irreversibleAt_of_illegal (step_tabToFound_none_of_nextUp hf)

/-- A refused `.foundToTab` guard makes the move vacuously
irreversible. -/
private theorem step_foundToTab_none {st : State} {c' c : Card} {b : Base}
    (htop : st.foundTop c.suit = some c')
    (hcond : ((decide (c' = c) && st.canPlace c b) = true) → False) :
    State.step st (Move.foundToTab c b) = none := by
  simp only [State.step, htop]
  rw [ite_eq_right hcond]

/-- A passing `.foundToTab` guard produces the recorded successor. -/
private theorem step_foundToTab_legal {st : State} {c : Card} {b : Base}
    (htop : st.foundTop c.suit = some c) (hcp : st.canPlace c b = true) :
    ∃ s₁, State.step st (Move.foundToTab c b) = some s₁ := by
  refine ⟨((st.setFound c.suit (chop (st.found c.suit))).putCard c b), ?_⟩
  simp only [State.step, htop, hcp]
  rfl

/-- The `.foundToTab` shape: at WF every legal `.foundToTab` is
reversible (the `foundToTab_undo` family with `hnext` discharged by
the conservation invariant's prefix arithmetic and the search pin
discharged by the card-count uniqueness), so the shape negates the
legality guard. -/
private def foundToTabIrr (st : State) (c : Card) (b : Base) : Bool :=
  match st.foundTop c.suit with
  | none => true
  | some c' => if c' = c then !(st.canPlace c b) else true

theorem foundToTabClass {st : State} (hwf : st.WF) (c : Card) (b : Base) :
    irreversibleAt st (Move.foundToTab c b) ↔ foundToTabIrr st c b = true := by
  cases htop : st.foundTop c.suit with
  | none =>
      constructor
      · intro _
        rw [foundToTabIrr, htop]
      · intro _
        exact irreversibleAt_of_illegal (by simp only [State.step, htop])
  | some c' =>
      by_cases hcc : c' = c
      · rw [hcc] at htop
        by_cases hcp : st.canPlace c b = true
        · -- legal: reversible at WF; the shape reads false
          constructor
          · intro hirr
            exfalso
            obtain ⟨s₁, hs⟩ := step_foundToTab_legal htop hcp
            have hnext : (chop (st.found c.suit)).length = c.rank.toIdx :=
              wf_found_chop_toIdx hwf htop
            cases b with
            | inl k =>
                have hnost : ∀ a₂ : Anchor, a₂ ≠ k → (st.piles a₂).top ≠ some c :=
                  fun a₂ _ => @wf_found_not_pileTop st c a₂ c.suit hwf htop
                have hsearch : s₁.pileOfTop c = some k := by
                  obtain ⟨-, -, -, -, hs'⟩ := step_foundToTab_inv hs
                  rw [hs']
                  have hothers : ∀ a₂, a₂ ≠ k →
                      ((st.setFound c.suit (chop (st.found c.suit))).putCard c (Sum.inl k)).piles a₂
                        = st.piles a₂ := by
                    intro a₂ hne₂
                    rw [putCard_piles_inl]
                    show (if a₂ = k then ((⟨[], [c]⟩ : Pile)) else st.piles a₂) = st.piles a₂
                    rw [ite_eq_right hne₂]
                  have htop2 : (((st.setFound c.suit (chop (st.found c.suit))).putCard c (Sum.inl k)).piles k).top
                      = some c := by
                    rw [putCard_piles_inl]
                    show (if k = k then ((⟨[], [c]⟩ : Pile)) else st.piles k).top = some c
                    rw [ite_eq_left rfl]
                    rfl
                  exact topPin hothers htop2 hnost
                exact not_reversibleAtW_of_irreversibleAt hirr
                  (foundToTab_undo hs hnext hsearch (Or.inl rfl))
            | inr z =>
                obtain ⟨k, hz, -⟩ := canPlace_inr hcp
                have hnost : ∀ a₂ : Anchor, a₂ ≠ k → (st.piles a₂).top ≠ some c :=
                  fun a₂ _ => @wf_found_not_pileTop st c a₂ c.suit hwf htop
                have hsearch : s₁.pileOfTop c = some k := by
                  obtain ⟨-, -, -, -, hs'⟩ := step_foundToTab_inv hs
                  rw [hs']
                  have hz2 : (st.setFound c.suit (chop (st.found c.suit))).pileOfTop z
                      = some k := hz
                  have hothers : ∀ a₂, a₂ ≠ k →
                      ((st.setFound c.suit (chop (st.found c.suit))).putCard c (Sum.inr z)).piles a₂
                        = st.piles a₂ := by
                    intro a₂ hne₂
                    rw [putCard_piles_inr _ _ _ _ hz2]
                    show (if a₂ = k then
                        ({ st.piles k with faceUp := (st.piles k).faceUp ++ [c] } : Pile)
                        else st.piles a₂) = st.piles a₂
                    rw [ite_eq_right hne₂]
                  have htop2 : (((st.setFound c.suit (chop (st.found c.suit))).putCard c (Sum.inr z)).piles k).top
                      = some c := by
                    rw [putCard_piles_inr _ _ _ _ hz2]
                    show (if k = k then
                        ({ st.piles k with faceUp := (st.piles k).faceUp ++ [c] } : Pile)
                        else st.piles k).top = some c
                    rw [ite_eq_left rfl]
                    show lastOf ((st.piles k).faceUp ++ [c]) = some c
                    exact lastOf_snoc (st.piles k).faceUp c
                  exact topPin hothers htop2 hnost
                exact not_reversibleAtW_of_irreversibleAt hirr
                  (foundToTab_undo hs hnext hsearch (Or.inr ⟨z, rfl, hz⟩))
          · intro hshape
            -- the shape reads !(canPlace-true) = false here; contradiction:
            have hfalse : foundToTabIrr st c b = false := by
              rw [foundToTabIrr, htop]
              show (if c = c then !(st.canPlace c b) else true) = false
              rw [ite_eq_left rfl, hcp]
              rfl
            exact absurd hshape (by
              rw [hshape] at hfalse
              exact absurd hfalse (by simp))
        · -- matched top, refused placement: illegal; shape true
          constructor
          · intro _
            rw [foundToTabIrr, htop]
            show (if c = c then !(st.canPlace c b) else true) = true
            rw [ite_eq_left rfl]
            have hf2 : st.canPlace c b = false := by
              cases h2 : st.canPlace c b with
              | true => exact absurd h2 hcp
              | false => rfl
            rw [hf2, Bool.not_false]
          · intro _
            exact irreversibleAt_of_illegal (step_foundToTab_none htop (by
              intro hc
              rw [Bool.and_eq_true] at hc
              exact hcp hc.2))
      · -- mismatched top: illegal; shape true
        constructor
        · intro _
          rw [foundToTabIrr, htop]
          show (if c' = c then !(st.canPlace c b) else true) = true
          rw [ite_eq_right hcc]
        · intro _
          exact irreversibleAt_of_illegal (by
            have hd2 : decide (c' = c) = false := decide_eq_false hcc
            exact step_foundToTab_none htop (by
              intro hc
              rw [hd2, Bool.false_and] at hc
              exact absurd hc (by simp)))

/-- The `.tabToTab` shape: the reveal row irreversible (the
hidden total strictly drops); the bare row split at the king
(reversible for kings through the mirror reseating, irreversible
for non-kings through the landed bare non-king commitment); the
under row reversible at WF (the mirror-move undos with their
premises discharged by the conservation invariant); illegal rows
read true. -/
private def tabToTabIrr (st : State) (c : Card) (b : Base) : Bool :=
  match st.pileHolding c with
  | none => true
  | some a =>
      match st.canPlace c b with
      | false => true
      | true =>
          match below c (st.piles a).faceUp with
          | [] =>
              match (st.piles a).hidden with
              | [] => decide (c.rank ≠ Rank.king)
              | _ :: _ => true
          | _ :: _ => false

theorem tabToTabClass {st : State} (hwf : st.WF) (c : Card) (b : Base) :
    irreversibleAt st (Move.tabToTab c b) ↔ tabToTabIrr st c b = true := by
  cases hh : st.pileHolding c with
  | none =>
      constructor
      · intro _
        rw [tabToTabIrr, hh]
      · intro _
        exact irreversibleAt_of_illegal (step_tabToTab_none_of_holding hh)
  | some a =>
      cases hcp : st.canPlace c b with
      | false =>
          constructor
          · intro _
            rw [tabToTabIrr, hh, hcp]
          · intro _
            exact irreversibleAt_of_illegal (step_tabToTab_none_of_cp hh hcp)
      | true =>
          obtain ⟨s₁, hs⟩ := step_tabToTab_some hh hcp
          obtain ⟨a₂, hht, hct, hfr, hs₁⟩ := step_tabToTab_inv hs
          have haeq : a₂ = a := by
            have hx : some a = some a₂ := hh.symm.trans hht
            injection hx with hxE
            exact hxE.symm
          rw [haeq] at hs₁ hfr
          obtain ⟨tr, hrt⟩ := fromCard_head rfl hfr
          rw [tabToTabIrr, hh, hcp]
          show irreversibleAt st (Move.tabToTab c b) ↔
            (match below c (st.piles a).faceUp with
              | [] =>
                  match (st.piles a).hidden with
                  | [] => decide (c.rank ≠ Rank.king)
                  | _ :: _ => true
              | _ :: _ => false) = true
          cases hbelow : below c (st.piles a).faceUp with
          | nil =>
              show irreversibleAt st (Move.tabToTab c b) ↔
                (match (st.piles a).hidden with
                  | [] => decide (c.rank ≠ Rank.king)
                  | _ :: _ => true) = true
              cases hhid : (st.piles a).hidden with
              | nil =>
                  show irreversibleAt st (Move.tabToTab c b) ↔
                    decide (c.rank ≠ Rank.king) = true
                  constructor
                  · intro hirr
                    by_cases hkng : c.rank = Rank.king
                    · exfalso
                      -- the king: the whole source pile moved to the landing
                      -- pile, and the mirror move returns it
                      rw [hbelow, afterRunRemoved_empty_eq' _ hhid] at hs₁
                      cases b with
                      | inl k =>
                          have hka : k ≠ a :=
                            canPlace_inl_target_pile_ne hcp (pileHolding_mem hh)
                          have hcN : c ∉ (st.piles k).faceUp :=
                            (mem_faceUp_unique hwf (pileHolding_mem hh) k hka).1
                          have hkeep : ∀ y, y ≠ a → y ≠ k → s₁.piles y = st.piles y := by
                            intro y hya hyk
                            rw [hs₁, putRun_piles_inl]
                            show (if y = k then ⟨[], fromCard c (st.piles a).faceUp⟩
                                else (st.setPile a ⟨[], ([] : List Card)⟩ : State).piles y)
                              = st.piles y
                            rw [ite_eq_right hyk]
                            show (if y = a then ⟨[], ([] : List Card)⟩ else st.piles y)
                              = st.piles y
                            rw [ite_eq_right hya]
                          have hca : c ∉ (s₁.piles a).faceUp := by
                            rw [hs₁, putRun_piles_inl]
                            show c ∉ (if a = k then ⟨[], fromCard c (st.piles a).faceUp⟩
                                else (st.setPile a ⟨[], ([] : List Card)⟩ : State).piles a).faceUp
                            rw [ite_eq_right (Ne.symm hka)]
                            show c ∉ (if a = a then ⟨[], ([] : List Card)⟩ else st.piles a).faceUp
                            rw [ite_eq_left rfl]
                            intro hcon
                            cases hcon
                          have hhk : c ∈ (s₁.piles k).faceUp := by
                            rw [hs₁, putRun_piles_inl]
                            show c ∈ (if k = k then ⟨[], fromCard c (st.piles a).faceUp⟩
                                else (st.setPile a ⟨[], ([] : List Card)⟩ : State).piles k).faceUp
                            rw [ite_eq_left rfl, hrt]
                            exact List.mem_cons_self
                          have hhold : s₁.pileHolding c = some k :=
                            holdingPin2 hca (fun y hyk hya => hkeep y hya hyk) hhk
                              (fun y hyk hya =>
                                (mem_faceUp_unique hwf (pileHolding_mem hh) y hya).1)
                          exact not_reversibleAtW_of_irreversibleAt hirr
                            (tabToTab_undo_bare hs hh hbelow hhid hkng hhold (Or.inl rfl)
                              hkeep hcN)
                      | inr z' =>
                          obtain ⟨k, hk₀, -⟩ := canPlace_inr hcp
                          have hka : k ≠ a := fun hcon =>
                            canPlace_inr_target_pile_ne hwf hcp (pileHolding_mem hh)
                              (hk₀.trans (congrArg some hcon))
                          have hcN : c ∉ (st.piles k).faceUp :=
                            (mem_faceUp_unique hwf (pileHolding_mem hh) k hka).1
                          -- the mid pin: the source pile is topless at mid (it was
                          -- emptied), so the card search pins pile k alone
                          have hmidK : (st.setPile a ⟨[], ([] : List Card)⟩ : State).piles k
                              = st.piles k := by
                            show (if k = a then ⟨[], ([] : List Card)⟩ else st.piles k) = _
                            rw [ite_eq_right hka]
                          have hmidAtop : ((st.setPile a ⟨[], ([] : List Card)⟩ : State).piles a).top
                              ≠ some z' := by
                            show (if a = a then ⟨[], ([] : List Card)⟩ else st.piles a).top
                              ≠ some z'
                            rw [ite_eq_left rfl]
                            intro hcon
                            nomatch hcon
                          have hseatMid :
                              (st.setPile a ⟨[], ([] : List Card)⟩ : State).pileOfTop z'
                                = some k :=
                            topPin2 (by
                                rw [hmidK]
                                exact (pileOfTop_top hk₀).2)
                              (fun y hyk hya => by
                                show (if y = a then ⟨[], ([] : List Card)⟩
                                    else st.piles y) = st.piles y
                                rw [ite_eq_right hya])
                              hmidAtop (fun y hyk _ =>
                                wf_no_other_top hwf (lastOf_mem (pileOfTop_top hk₀).2) y hyk)
                          have hkeep : ∀ y, y ≠ a → y ≠ k → s₁.piles y = st.piles y := by
                            intro y hya hyk
                            rw [hs₁, putRun_piles_inr _ _ _ _ hseatMid]
                            show (if y = k then
                                { (st.setPile a ⟨[], ([] : List Card)⟩ : State).piles k with
                                  faceUp := ((st.setPile a ⟨[], ([] : List Card)⟩ : State).piles k).faceUp
                                    ++ fromCard c (st.piles a).faceUp }
                                else (st.setPile a ⟨[], ([] : List Card)⟩ : State).piles y)
                              = st.piles y
                            rw [ite_eq_right hyk]
                            show (if y = a then ⟨[], ([] : List Card)⟩ else st.piles y)
                              = st.piles y
                            rw [ite_eq_right hya]
                          have hca : c ∉ (s₁.piles a).faceUp := by
                            rw [hs₁, putRun_piles_inr _ _ _ _ hseatMid]
                            show c ∉ (if a = k then
                                { (st.setPile a ⟨[], ([] : List Card)⟩ : State).piles k with
                                  faceUp := ((st.setPile a ⟨[], ([] : List Card)⟩ : State).piles k).faceUp
                                    ++ fromCard c (st.piles a).faceUp }
                                else (st.setPile a ⟨[], ([] : List Card)⟩ : State).piles a).faceUp
                            rw [ite_eq_right (Ne.symm hka)]
                            show c ∉ (if a = a then ⟨[], ([] : List Card)⟩ else st.piles a).faceUp
                            rw [ite_eq_left rfl]
                            intro hcon
                            cases hcon
                          have hhk : c ∈ (s₁.piles k).faceUp := by
                            rw [hs₁, putRun_piles_inr _ _ _ _ hseatMid]
                            show c ∈ (if k = k then
                                { (st.setPile a ⟨[], ([] : List Card)⟩ : State).piles k with
                                  faceUp := ((st.setPile a ⟨[], ([] : List Card)⟩ : State).piles k).faceUp
                                    ++ fromCard c (st.piles a).faceUp }
                                else (st.setPile a ⟨[], ([] : List Card)⟩ : State).piles k).faceUp
                            rw [ite_eq_left rfl, hmidK, hrt]
                            exact (List.mem_append).2 (Or.inr List.mem_cons_self)
                          have hhold : s₁.pileHolding c = some k :=
                            holdingPin2 hca (fun y hyk hya => hkeep y hya hyk) hhk
                              (fun y hyk hya =>
                                (mem_faceUp_unique hwf (pileHolding_mem hh) y hya).1)
                          exact not_reversibleAtW_of_irreversibleAt hirr
                            (tabToTab_undo_bare hs hh hbelow hhid hkng hhold
                              (Or.inr ⟨z', rfl, hseatMid⟩) hkeep hcN)
                    · rw [decide_eq_true hkng]
                  · intro hshape
                    exact tabToTab_irreversible_of_bare_nonking hs hh hbelow hhid hfr
                      (of_decide_eq_true hshape)
              | cons w t =>
                  constructor
                  · intro _
                    rfl
                  · intro _
                    exact irr_of_desc hiddenTotal
                      (fun s m s' hst => hiddenTotal_step hst) hs
                      (hiddenTotal_step_tabToTab_reveal hs hh hbelow
                        (by rw [hhid]; intro hhcon; exact absurd hhcon (by simp)))
          | cons z₀ pre' =>
              show irreversibleAt st (Move.tabToTab c b) ↔ false = true
              constructor
              · intro hirr
                exfalso
                -- the seat card pin, the seam fit, and the tail legality
                obtain ⟨z, hz⟩ := lastOf_cons_some pre' z₀
                have hzB : lastOf (below c (st.piles a).faceUp) = some z := by
                  rw [hbelow]
                  exact hz
                have hzin : z ∈ below c (st.piles a).faceUp := lastOf_mem hzB
                have hzmem : z ∈ (st.piles a).faceUp := below_mem hzin
                have h1 := below_join (c := c) ((st.piles a).faceUp)
                rw [hbelow, hrt] at h1
                -- h1 : (z₀ :: pre') ++ (c :: tr) = (st.piles a).faceUp
                have hrunOK0 : runOK ((st.piles a).faceUp) = true := hwf.runOK_of a
                have hrunlit : runOK ((z₀ :: pre') ++ (c :: tr)) = true := by
                  rw [h1]
                  exact hrunOK0
                have hrunTail : runOK (c :: tr) = true :=
                  runOK_append_left (z₀ :: pre') (c :: tr) hrunlit
                have hfitpre : runOK (((z₀ :: pre') ++ [c]) ++ tr) = true := by
                  rw [List.append_assoc]
                  have hE : [c] ++ tr = c :: tr := by
                    rw [List.cons_append, List.nil_append]
                  rw [hE]
                  exact hrunlit
                have hsit : canSitOn c z = true :=
                  runOK_adjacent_snoc hz
                    (runOK_append_right ((z₀ :: pre') ++ [c]) tr hfitpre)
                cases b with
                | inl k =>
                    have hka : k ≠ a :=
                      canPlace_inl_target_pile_ne hcp (pileHolding_mem hh)
                    have hcN : c ∉ (st.piles k).faceUp :=
                      (mem_faceUp_unique hwf (pileHolding_mem hh) k hka).1
                    have hzK : (st.piles k).top ≠ some z :=
                      wf_no_other_top hwf hzmem k hka
                    have hkeep : ∀ y, y ≠ a → y ≠ k → s₁.piles y = st.piles y := by
                      intro y hya hyk
                      rw [hs₁, putRun_piles_inl]
                      show (if y = k then ⟨[], fromCard c (st.piles a).faceUp⟩
                          else (st.setPile a (Pile.afterRunRemoved (st.piles a)
                            (below c (st.piles a).faceUp)) : State).piles y)
                        = st.piles y
                      rw [ite_eq_right hyk]
                      show (if y = a then Pile.afterRunRemoved (st.piles a)
                          (below c (st.piles a).faceUp) else st.piles y) = st.piles y
                      rw [ite_eq_right hya]
                    have hca : c ∉ (s₁.piles a).faceUp := by
                      rw [hs₁, putRun_piles_inl]
                      show c ∉ (if a = k then ⟨[], fromCard c (st.piles a).faceUp⟩
                          else (st.setPile a (Pile.afterRunRemoved (st.piles a)
                            (below c (st.piles a).faceUp)) : State).piles a).faceUp
                      rw [ite_eq_right (Ne.symm hka)]
                      show c ∉ (if a = a then Pile.afterRunRemoved (st.piles a)
                          (below c (st.piles a).faceUp) else st.piles a).faceUp
                      rw [ite_eq_left rfl, hbelow]
                      show c ∉ (z₀ :: pre')
                      rw [← hbelow]
                      exact below_not_mem_self _
                    have hhk : c ∈ (s₁.piles k).faceUp := by
                      rw [hs₁, putRun_piles_inl]
                      show c ∈ (if k = k then ⟨[], fromCard c (st.piles a).faceUp⟩
                          else (st.setPile a (Pile.afterRunRemoved (st.piles a)
                            (below c (st.piles a).faceUp)) : State).piles k).faceUp
                      rw [ite_eq_left rfl, hrt]
                      exact List.mem_cons_self
                    have hhold : s₁.pileHolding c = some k :=
                      holdingPin2 hca (fun y hyk hya => hkeep y hya hyk) hhk
                        (fun y hyk hya =>
                          (mem_faceUp_unique hwf (pileHolding_mem hh) y hya).1)
                    have hzOnly : ∀ y, y ≠ a → (s₁.piles y).top ≠ some z := by
                      intro y hya
                      by_cases hyk : y = k
                      · rw [hyk]
                        intro htop
                        have hmemK : z ∈ (s₁.piles k).faceUp := Pile.mem_of_top htop
                        have hkFu : (s₁.piles k).faceUp
                            = fromCard c (st.piles a).faceUp := by
                          rw [hs₁, putRun_piles_inl]
                          show (if k = k then ⟨[], fromCard c (st.piles a).faceUp⟩
                              else (st.setPile a (Pile.afterRunRemoved (st.piles a)
                                (below c (st.piles a).faceUp)) : State).piles k).faceUp = _
                          rw [ite_eq_left rfl]
                        rw [hkFu, hrt] at hmemK
                        rcases List.mem_cons.1 hmemK with heq | htr2
                        · rw [heq] at hsit
                          obtain ⟨hrank, -⟩ := (canSitOn_eq c c).mp hsit
                          omega
                        · have hrk := runOK_head_lt hrunTail htr2
                          obtain ⟨hrank, -⟩ := (canSitOn_eq c z).mp hsit
                          omega
                      · intro htop
                        rw [hkeep y hya hyk] at htop
                        exact wf_no_other_top hwf hzmem y hya htop
                    exact not_reversibleAtW_of_irreversibleAt hirr
                      (tabToTab_undo_under hs hh hzB hsit hhold (Or.inl rfl)
                        hkeep hcN hzOnly hzK)
                | inr z' =>
                    obtain ⟨k, hk₀, -⟩ := canPlace_inr hcp
                    have hka : k ≠ a := fun hcon =>
                      canPlace_inr_target_pile_ne hwf hcp (pileHolding_mem hh)
                        (hk₀.trans (congrArg some hcon))
                    have hcN : c ∉ (st.piles k).faceUp :=
                      (mem_faceUp_unique hwf (pileHolding_mem hh) k hka).1
                    have hzK : (st.piles k).top ≠ some z :=
                      wf_no_other_top hwf hzmem k hka
                    have hz'mem : z' ∈ (st.piles k).faceUp :=
                      lastOf_mem (pileOfTop_top hk₀).2
                    have hnostK : ∀ y : Anchor, y ≠ k → (st.piles y).top ≠ some z' :=
                      fun y hy => wf_no_other_top hwf hz'mem y hy
                    have hmidK : (st.setPile a (Pile.afterRunRemoved (st.piles a)
                        (below c (st.piles a).faceUp)) : State).piles k = st.piles k := by
                      show (if k = a then Pile.afterRunRemoved (st.piles a)
                          (below c (st.piles a).faceUp) else st.piles k) = _
                      rw [ite_eq_right hka]
                    -- at mid, the source pile tops z (the below part survived),
                    -- and z ≠ z' by the occurrence uniqueness
                    have hmidAtop : ((st.setPile a (Pile.afterRunRemoved (st.piles a)
                        (below c (st.piles a).faceUp)) : State).piles a).top
                        ≠ some z' := by
                      show (if a = a then Pile.afterRunRemoved (st.piles a)
                          (below c (st.piles a).faceUp) else st.piles a).top ≠ some z'
                      rw [ite_eq_left rfl, hbelow]
                      show (⟨(st.piles a).hidden, z₀ :: pre'⟩ : Pile).top ≠ some z'
                      intro hcon
                      have hlt : lastOf (z₀ :: pre') = some z' := hcon
                      rw [hz] at hlt
                      injection hlt with hzz'
                      have hzc : z' ∈ (st.piles a).faceUp := by
                        rw [← hzz']
                        exact hzmem
                      exact absurd hz'mem ((mem_faceUp_unique hwf hzc k hka).1)
                    have hseatMid : (st.setPile a (Pile.afterRunRemoved (st.piles a)
                        (below c (st.piles a).faceUp)) : State).pileOfTop z' = some k :=
                      topPin2 (by
                          rw [hmidK]
                          exact (pileOfTop_top hk₀).2)
                        (fun y hyk hya => by
                          show (if y = a then Pile.afterRunRemoved (st.piles a)
                              (below c (st.piles a).faceUp) else st.piles y) = st.piles y
                          rw [ite_eq_right hya])
                        hmidAtop (fun y hyk _ => hnostK y hyk)
                    have hkeep : ∀ y, y ≠ a → y ≠ k → s₁.piles y = st.piles y := by
                      intro y hya hyk
                      rw [hs₁, putRun_piles_inr _ _ _ _ hseatMid]
                      show (if y = k then
                          { (st.setPile a (Pile.afterRunRemoved (st.piles a)
                              (below c (st.piles a).faceUp)) : State).piles k with
                            faceUp := ((st.setPile a (Pile.afterRunRemoved (st.piles a)
                              (below c (st.piles a).faceUp)) : State).piles k).faceUp
                              ++ fromCard c (st.piles a).faceUp }
                          else (st.setPile a (Pile.afterRunRemoved (st.piles a)
                              (below c (st.piles a).faceUp)) : State).piles y)
                        = st.piles y
                      rw [ite_eq_right hyk]
                      show (if y = a then Pile.afterRunRemoved (st.piles a)
                          (below c (st.piles a).faceUp) else st.piles y) = st.piles y
                      rw [ite_eq_right hya]
                    have hca : c ∉ (s₁.piles a).faceUp := by
                      rw [hs₁, putRun_piles_inr _ _ _ _ hseatMid]
                      show c ∉ (if a = k then
                          { (st.setPile a (Pile.afterRunRemoved (st.piles a)
                              (below c (st.piles a).faceUp)) : State).piles k with
                            faceUp := ((st.setPile a (Pile.afterRunRemoved (st.piles a)
                              (below c (st.piles a).faceUp)) : State).piles k).faceUp
                              ++ fromCard c (st.piles a).faceUp }
                          else (st.setPile a (Pile.afterRunRemoved (st.piles a)
                              (below c (st.piles a).faceUp)) : State).piles a).faceUp
                      rw [ite_eq_right (Ne.symm hka)]
                      show c ∉ (if a = a then Pile.afterRunRemoved (st.piles a)
                          (below c (st.piles a).faceUp) else st.piles a).faceUp
                      rw [ite_eq_left rfl, hbelow]
                      show c ∉ (z₀ :: pre')
                      rw [← hbelow]
                      exact below_not_mem_self _
                    have hhk : c ∈ (s₁.piles k).faceUp := by
                      rw [hs₁, putRun_piles_inr _ _ _ _ hseatMid]
                      show c ∈ (if k = k then
                          { (st.setPile a (Pile.afterRunRemoved (st.piles a)
                              (below c (st.piles a).faceUp)) : State).piles k with
                            faceUp := ((st.setPile a (Pile.afterRunRemoved (st.piles a)
                              (below c (st.piles a).faceUp)) : State).piles k).faceUp
                              ++ fromCard c (st.piles a).faceUp }
                          else (st.setPile a (Pile.afterRunRemoved (st.piles a)
                              (below c (st.piles a).faceUp)) : State).piles k).faceUp
                      rw [ite_eq_left rfl, hmidK, hrt]
                      exact (List.mem_append).2 (Or.inr List.mem_cons_self)
                    have hhold : s₁.pileHolding c = some k :=
                      holdingPin2 hca (fun y hyk hya => hkeep y hya hyk) hhk
                        (fun y hyk hya =>
                          (mem_faceUp_unique hwf (pileHolding_mem hh) y hya).1)
                    have hzOnly : ∀ y, y ≠ a → (s₁.piles y).top ≠ some z := by
                      intro y hya
                      by_cases hyk : y = k
                      · rw [hyk]
                        intro htop
                        have hmemK : z ∈ (s₁.piles k).faceUp := Pile.mem_of_top htop
                        have hkFu : (s₁.piles k).faceUp
                            = (st.piles k).faceUp ++ fromCard c (st.piles a).faceUp := by
                          rw [hs₁, putRun_piles_inr _ _ _ _ hseatMid]
                          show (if k = k then
                              { (st.setPile a (Pile.afterRunRemoved (st.piles a)
                                  (below c (st.piles a).faceUp)) : State).piles k with
                                faceUp := ((st.setPile a (Pile.afterRunRemoved (st.piles a)
                                  (below c (st.piles a).faceUp)) : State).piles k).faceUp
                                  ++ fromCard c (st.piles a).faceUp }
                              else (st.setPile a (Pile.afterRunRemoved (st.piles a)
                                  (below c (st.piles a).faceUp)) : State).piles k).faceUp = _
                          rw [ite_eq_left rfl, hmidK]
                        rw [hkFu, hrt] at hmemK
                        have hzrun2 : z ∈ (st.piles k).faceUp ++ (c :: tr) := hmemK
                        rcases (List.mem_append).1 hzrun2 with hL | hR
                        · exact absurd hL ((mem_faceUp_unique hwf hzmem k hka).1)
                        · rcases List.mem_cons.1 hR with heq | htr2
                          · rw [heq] at hsit
                            obtain ⟨hrank, -⟩ := (canSitOn_eq c c).mp hsit
                            omega
                          · have hrk := runOK_head_lt hrunTail htr2
                            obtain ⟨hrank, -⟩ := (canSitOn_eq c z).mp hsit
                            omega
                      · intro htop
                        rw [hkeep y hya hyk] at htop
                        exact wf_no_other_top hwf hzmem y hya htop
                    exact not_reversibleAtW_of_irreversibleAt hirr
                      (tabToTab_undo_under hs hh hzB hsit hhold
                        (Or.inr ⟨z', rfl, hseatMid⟩) hkeep hcN hzOnly hzK)
              · intro hshape
                exact absurd hshape (by simp)

/-! ## The draw shape -/

/-- The draw shape: pristine or offset positions are irreversible,
in-phase and pass-base positions are reversible (the landed
`draw_irreversibility_class` rows and the pass-base drain above),
and the both-empty draw is illegal (vacuously irreversible). -/
private def drawIrr (st : State) : Bool :=
  match st.stock with
  | [] => decide (st.waste = [])
  | _ => decide (st.waste = []) || decide (st.waste.length % st.drawStep ≠ 0)

theorem drawClass {st : State} (hwf : st.WF) :
    irreversibleAt st Move.draw ↔ drawIrr st = true := by
  have hd : 0 < st.drawStep := hwf.drawStep_pos
  cases hstock : st.stock with
  | nil =>
      rw [drawIrr, hstock]
      by_cases hw : st.waste = []
      · constructor
        · intro _
          exact decide_eq_true hw
        · intro _
          have hr : State.recycle st = st := by
            rw [State.recycle, hstock, hw]
          exact irreversibleAt_of_illegal (by
            show State.dealStock (State.recycle st) = none
            rw [hr, State.dealStock, hstock])
      · constructor
        · intro hirr
          exfalso
          exact not_reversibleAtW_of_irreversibleAt hirr
            (draw_passBase_reversibleW hstock hw hd)
        · intro hshape
          exact absurd (of_decide_eq_true hshape) hw
  | cons w t =>
      have hne : st.stock ≠ [] := by
        intro hc
        rw [hstock] at hc
        exact absurd hc (by simp)
      rw [drawIrr, hstock]
      by_cases hw : st.waste = []
      · constructor
        · intro _
          rw [decide_eq_true hw]
          rfl
        · intro _
          exact draw_irreversible_pristine hd hne hw
      · by_cases hoff : st.waste.length % st.drawStep = 0
        · -- in phase at a stock-bearing position: reversible
          constructor
          · intro hirr
            exfalso
            have hph : inPhase st = true := by
              rw [inPhase_eq_decide_of_cons hstock, decide_eq_true hoff]
            exact not_reversibleAtW_of_irreversibleAt hirr
              (draw_reversible_inphaseW hd hne hw hph)
          · intro hshape
            rw [decide_eq_false hw, Bool.false_or] at hshape
            have hcontra : st.waste.length % st.drawStep ≠ 0 := of_decide_eq_true hshape
            exact absurd hoff hcontra
        · constructor
          · intro _
            rw [decide_eq_false hw, Bool.false_or, decide_eq_true hoff]
          · intro hshape
            rw [decide_eq_false hw, Bool.false_or] at hshape
            exact draw_irreversible_offset hd hne
              (of_decide_eq_true hshape)

/-! ## The assembled oracle
-/

/-- The per-move oracle shape, assembled out of the classification
rows: the draw row from `drawIrr`, the waste rows trivially true
(the cycle count drops on every legal waste move, no gate), and
the three table moves from their shape predicates.  At `WF`
states `irreversible_iff_of` makes this decide the semantic
predicate exactly, and `decidable_irreversibleAt_of_wf` converts
the iff into a choice-free `Decidable`.  Deliberately *not* a
global instance-gate: at wild states the shape and the semantics
diverge in both directions — the design fork's witnessed corners
(the witness archive) — so the predicate is only an oracle where
the position is known to be `WF`. -/
def irreversibleOf (st : State) (m : Move) : Bool :=
  match m with
  | .draw => drawIrr st
  | .wasteToFound _ => true
  | .wasteToTab _ _ => true
  | .tabToFound c => tabToFoundIrr st c
  | .foundToTab c b => foundToTabIrr st c b
  | .tabToTab c b => tabToTabIrr st c b

/-- The oracle's WF-gated specification: at a `WF` state the bool
assembly decides the semantic irreversibility predicate exactly,
constructor by constructor through the landed classifications. -/
theorem irreversible_iff_of {st : State} (hwf : st.WF) (m : Move) :
    irreversibleAt st m ↔ irreversibleOf st m = true := by
  cases m with
  | draw => exact drawClass hwf
  | wasteToFound c =>
      constructor
      · intro _
        rfl
      · intro _
        exact irreversibleAt_wasteToFound st c
  | wasteToTab c b =>
      constructor
      · intro _
        rfl
      · intro _
        exact irreversibleAt_wasteToTab st c b
  | tabToFound c => exact tabToFoundClass hwf c
  | foundToTab c b => exact foundToTabClass hwf c b
  | tabToTab c b => exact tabToTabClass hwf c b

/-- The decider rider: at `WF` states the semantic predicate
`irreversibleAt st m` is decidable through the oracle's iff —
no `Classical.choice` anywhere in the decision.  Stated as a
plain definition (an instance gate would claim decidability at
wild states, where the shape and the semantics diverge). -/
def decidable_irreversibleAt_of_wf {st : State} (hwf : st.WF) (m : Move) :
    Decidable (irreversibleAt st m) := by
  cases h : irreversibleOf st m with
  | true => exact isTrue ((irreversible_iff_of hwf m).mpr h)
  | false =>
      exact isFalse (fun hirr => by
        rw [(irreversible_iff_of hwf m).mp hirr] at h
        exact Bool.noConfusion h)

/-! ## The WFRun-gated `win_macro_aux` companion
-/

/-- A play along which every intermediate state is `WF`: each
`cons` carries the successor's `WF` as data (step-preserved `WF`
is `Orig.lean`'s open ticket; the witness carries it), the head
split of the macro induction then never needs `by_cases`. -/
inductive WFRun : State → List Move → State → Prop
  | nil (st : State) (hwf : st.WF) : WFRun st [] st
  | cons {st s₁ w : State} {m : Move} {rest : List Move}
      (hwf : st.WF) (hstep : State.step st m = some s₁)
      (hwf₁ : s₁.WF) (hrest : WFRun s₁ rest w) : WFRun st (m :: rest) w

/-- A `WFRun` is, in particular, a run. -/
theorem WFRun_run {st : State} {play : List Move} {w : State}
    (h : WFRun st play w) : st.run play = some w := by
  induction h with
  | nil st hwf => rfl
  | @cons st s₁ w m rest hwf hstep hwf₁ hrest ih =>
      show st.run (m :: rest) = some w
      rw [show st.run (m :: rest) = (match State.step st m with
        | some st' => st'.run rest
        | none => none) from rfl, hstep]
      exact ih

/-- **The WFRun-gated `win_macro_aux` companion.**  With the play
carrying WF at every intermediate state, the macro induction's
head split goes through the gated oracle's Bool — decidable and
choice-free — instead of the classical `by_cases`: the classical
head at `Orig/Macro.lean:121` keeps its `by_cases` and its
`[propext, Classical.choice, Quot.sound]` audit; this companion is
the honest scrub shape for WF-anchored plays (step-preserved `WF`
being `Orig.lean`'s open ticket, the `WFRun` witness carries each
successor's WF down the induction). -/
theorem win_macro_aux_wf : ∀ (play : List Move) (origin cur w : State)
    (pre : List Move),
    WFRun cur play w → ShufflePlay origin pre cur → w.isWin = true →
    ∃ w', MacroWin origin w' := by
  intro play
  induction play with
  | nil =>
      intro origin cur w pre hrun hs hwin
      cases hrun with
      | nil st hwf => exact ⟨_, MacroWin.finish hs hwin⟩
  | cons m rest ih =>
      intro origin cur w pre hrun hs hwin
      cases hrun with
      | @cons _ s₁ _ _ _ hwf hstep hwf₁ hrest =>
          -- the gated, choice-free split: the Bool decides
          cases hshape : irreversibleOf cur m with
          | true =>
              obtain ⟨w', hw'⟩ := ih s₁ s₁ w [] hrest (ShufflePlay.nil s₁) hwin
              exact ⟨w', MacroWin.phase ⟨cur, pre, hs, hstep,
                (irreversible_iff_of hwf m).mpr hshape⟩ hw'⟩
          | false =>
              have hrev : reversibleAt cur m := fun hirr => by
                rw [(irreversible_iff_of hwf m).mp hirr] at hshape
                exact Bool.noConfusion hshape
              exact ih origin s₁ w (pre ++ [m]) hrest
                (ShufflePlay_snoc hs hrev hstep) hwin



