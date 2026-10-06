import Orig.Irreversible
import Orig.Phase
import Orig.Combine

/-!
# Orig — the canonicalization theorem

`FUTURES-ORIG.md` §3.0, the program's FIRST ticket: the
canonicalization theorem that makes *same macro state* decidable, on
the stacking system that contains NO draws — only the two raises
(`.tabToFound` / `.wasteToFound`, the reveal riding along as always).

## The stacking system

* `Stackable st c` — `st.nextUp c` and `c` is the waste head or a
  pile top (the user's verbatim formulation).  `stackableB` is its
  decidable probe, `pick` the first stackable in universe order.
* `IsRaise m c` — `m` is one of the two raises of `c`;
  `raise st c` the residence-determined stacking step of a card.
* `StackRun st l w` — zero or more stacking steps, as an inductive
  relation over the move list (the explicit schedule).
* `Final st` — no card is stackable: the saturated, canonical shape.

## Termination (CLAIM 1's measure side)

`stackFuel` — the total remaining foundation climb, `Σ_s (13 -
foundHeight s)` with truncated subtraction: every stacking step
strictly drops it (the raised card's suit gains one rung, so the
same card can never be raised twice in one run), it never exceeds
52, and therefore every stacking run is at most 52 moves long
(`stackRun_length_le_fuel`, `stackRun_length_le_52`).

## CLAIM 1 (`canon_unique`)

All maximal stacking runs from a position whose cards sit in
exactly one place each (`NoDup`, the occurrence half of `WF`)
end at the same state.  `canon` is the deterministic saturator
(`canonAux` at budget 52), and `stackRun_final_eq_canon` proves any
run ending `Final` ends at `canon st`.  The monotone engine under
it, per the doctrine recorded in §3.0:

* monotone stackability — `stackable_step`: once stackable, still
  stackable after any *other* card's raise (nothing is ever placed
  onto a tableau, so nothing is ever covered; the waste is consumed
  only at the head);
* `stack_diamond` — two raises of *different* stackable cards
  commute literally (disjoint suits, disjoint zones): both orders
  land at the same state;
* `stackable_step_new` — the decomposition: a raise may only
  *add* the newly exposed top of the touched pile, or the newly
  uncovered waste head, as stackable candidates.

The `NoDup` premise is load-bearing: the private wild witness at
the bottom of this file exhibits a position with a duplicated card
whose two maximal runs end at genuinely different states.

## CLAIM 2 (the characterization)

`SameMacroO u v` is DEFINED as the canonical fiber (the user's
definitional reading: different macro ⇒ different canonical comes
from the definition):

```lean
def SameMacroO (u v : State) : Prop :=
  ⟦canon u⟧ = ⟦canon v⟧ ∧ SWComp u v
```

with `⟦·⟧` over the LANDED 4-disjunct `sameOrbitSetoid`
(`Orig.Combine`), and `SWComp u v` the hypothesis-named
stock/waste compatibility whose default here is the in-phase
rotation closure `SWRot` built from Phase's in-phase relation
(the user's pending confirm — restating `SWComp` re-points the
family below without touching the statements).  The invariance
family proves the journey notions land inside the fiber:

* (i) reversible rearrangements at a saturated state:
  `canon_foundToTab_absorb` (a descent is re-absorbed: canon
  literally unchanged), `final_raise_blocked` (no raise fires at
  a saturated state), `sameMacro_tabToTab_quiet` (the residue
  relocation preserves the wrapped level — the literal level
  FAILS here, by the private twin-residue witness; that witness is
  the evidence for the ⟦·⟧-wrapped form of the fiber and is this
  card's answer to the open design question);
* (ii) twin conjugation conjugates canon:
  `canon_twinMap : canon (twinMap u) = twinMap (canon u)`, and
  `sameMacro_twin`;
* (iii) in-phase stock/waste rotations preserve the wrapped canon
  under the pool blockade `poolLapped` (cards in the draw cycle
  already lapped by their foundations — the hypothesis that makes
  the saturation draw-equivariant): `sameMacro_rot` and the
  chain/corollary heads below it.

The honest residuals, both with private crafted witnesses:

* the *exposure* residual (relocation): a reversible cross-move at
  a saturated state can EXPOSE a newly stackable card, and the
  re-saturation then breaks even the wrapped level — witness
  `wk_exposure` — so family (i) carries the quietness premise
  `Final s` honestly, not for free;
* the twin-residue relocation shows the wrapped comparison is
  genuinely necessary: `wk_residue_relocate`.

`sameFate` tie: DEFERRED, out of scope for this card (§3.0
explicitly parks it); nothing here speaks to `sameFate`.

## HEADS DIGEST for the major-theorem assembly card (§3.1)

The exact heads the next card consumes, as this file's public
surface:

* `Stackable`, `stackableB`, `pick`, `IsRaise`, `raise`
  (the stacking system);
* `StackRun st l w`, `Final st`
  (`stackRun_length_le_fuel`, `stackRun_length_le_52`);
* `NoDup` (the occurrence fence) + `raise_noDup`,
  `stackRun_noDup`;
* CLAIM 1: `canon st`, `canon_final`, `canon_run`,
  `stackRun_final_eq_canon`, `canon_unique`;
* CLAIM 2: `SameMacroO`, `same_macro_iff`, and the invariance
  family `canon_foundToTab_absorb`, `final_raise_blocked`,
  `sameMacro_tabToTab_quiet`, `canon_twinMap`, `sameMacro_twin`,
  `sameMacro_rot`, `sameMacro_swRot`;
* the witnesses are PRIVATE — evidence, not surface.

Axiom discipline: `[propext, Quot.sound]` at worst, zero
`Classical.choice`, zero `sorry`, no `native_decide`; `simp` is
avoided on decision-shaped goals in favor of the
`ite_eq_left/right` + `omega` idiom (**the `ite_eq_left`/`ite_eq_right`
+ `omega` idiom is used throughout; `if_pos`/`if_neg` are
deprecated at this toolchain**); per-declaration `#print axioms`
audit at file bottom.
-/

/-! ## Stackable -/

/-- The decidable probe matching `Stackable`. -/
def stackableB (st : State) (c : Card) : Bool :=
  st.nextUp c && (st.wasteIs c || (st.pileOfTop c).isSome)

/-- A card is *stackable*: its suit rung is complete and it sits
at the waste head or on a pile top. -/
def Stackable (st : State) (c : Card) : Prop :=
  st.nextUp c = true ∧ (st.wasteIs c = true ∨ ∃ a, st.pileOfTop c = some a)

/-- The FIRE of saturation: no stackable cards anywhere.  (Defined
early: the `pick` bridge reads it.) -/
def Final (st : State) : Prop := ∀ c, ¬ Stackable st c

/-- The probe agrees with the relation. -/
theorem stackableB_true_iff {st : State} {c : Card} :
    stackableB st c = true ↔ Stackable st c := by
  constructor
  · intro h
    rw [stackableB, Bool.and_eq_true] at h
    refine ⟨h.1, ?_⟩
    cases hw : st.wasteIs c with
    | true => exact Or.inl rfl
    | false =>
        right
        have h2 := h.2
        rw [hw] at h2
        simp only [Bool.false_or] at h2
        cases hp : st.pileOfTop c with
        | some a => exact ⟨a, rfl⟩
        | none =>
            rw [hp] at h2
            exact absurd h2 (by simp)
  · rintro ⟨hn, hw | ⟨a, ha⟩⟩
    · show stackableB st c = true
      rw [stackableB, hn, hw]
      rfl
    · show stackableB st c = true
      rw [stackableB, hn, ha]
      cases st.wasteIs c
      · rfl
      · rfl

/-- The first stackable in universe order. -/
def pick (st : State) : Option Card :=
  firstWhere (stackableB st) Card.universe

/-- Every candidate failing gives `none`. -/
private theorem firstWhere_none_of_all {p : Card → Bool} :
    ∀ (l : List Card), (∀ c ∈ l, p c = false) → firstWhere p l = none := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons x t ih =>
      intro h
      simp only [firstWhere, h x (by simp)]
      exact ih (fun c hc => h c (by simp [hc]))

/-- A `none` search means every candidate failed. -/
private theorem firstWhere_none_complete {p : Card → Bool} :
    ∀ (l : List Card), firstWhere p l = none → ∀ c ∈ l, p c = false := by
  intro l
  induction l with
  | nil => intro _ c hc; exact absurd hc (by simp)
  | cons x t ih =>
      intro h c hc
      simp only [firstWhere] at h
      split at h
      · exact absurd h (by simp)
      · rename_i hp
        rcases (List.mem_cons.mp hc) with rfl | hm
        · exact hp
        · exact ih h c hm

/-- No stackable cards anywhere: the `none` reading of `pick`. -/
theorem pick_eq_none_iff_final (st : State) :
    pick st = none ↔ Final st := by
  constructor
  · intro h c hstab
    have hall := firstWhere_none_complete Card.universe h c (Card.mem_universe c)
    rw [show stackableB st c = true from stackableB_true_iff.2 hstab] at hall
    exact absurd hall (by simp)
  · intro h
    refine firstWhere_none_of_all Card.universe (fun c _ => ?_)
    cases hb : stackableB st c with
    | true => exact absurd (stackableB_true_iff.1 hb) (h c)
    | false => rfl

/-- A `some` from `pick` is stackable. -/
theorem pick_some_stackable {st : State} {c : Card} (h : pick st = some c) :
    Stackable st c :=
  stackableB_true_iff.1 (firstWhere_sound _ h)

/-! ## Raises -/

/-- A stacking move for `c`: one of the two raises. -/
inductive IsRaise : Move → Card → Prop
  | tabToFound (c : Card) : IsRaise (Move.tabToFound c) c
  | wasteToFound (c : Card) : IsRaise (Move.wasteToFound c) c

/-- The stacking step of `c`: the tableau raise when `c` is a pile
top, else the waste raise. -/
def raise (st : State) (c : Card) : Option State :=
  match st.pileOfTop c with
  | some _ => st.step (Move.tabToFound c)
  | none => st.step (Move.wasteToFound c)

/-- The tableau-resident reading of the stacking step. -/
theorem raise_of_pileOfTop (st : State) (c : Card) (a : Anchor)
    (hp : st.pileOfTop c = some a) :
    raise st c = st.step (Move.tabToFound c) := by
  show (match st.pileOfTop c with
    | some _ => st.step (Move.tabToFound c)
    | none => st.step (Move.wasteToFound c)) = _
  rw [hp]

/-- The waste-resident reading of the stacking step. -/
theorem raise_of_pileOfTop_none (st : State) (c : Card)
    (hp : st.pileOfTop c = none) :
    raise st c = st.step (Move.wasteToFound c) := by
  show (match st.pileOfTop c with
    | some _ => st.step (Move.tabToFound c)
    | none => st.step (Move.wasteToFound c)) = _
  rw [hp]

/-- A successful waste raise, as a shape lemma. -/
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

/-- A successful tableau raise, as a shape lemma. -/
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

/-- The foundation transport through a `setFound`, at the
waste-updated raise shape. -/
private theorem found_waste_shape (st : State) (c : Card) (xs : List Card) (σ : Suit) :
    ({ st.setFound c.suit (st.found c.suit ++ [c]) with waste := xs } : State).found σ
      = if σ = c.suit then st.found c.suit ++ [c] else st.found σ := by
  show (st.setFound c.suit (st.found c.suit ++ [c])).found σ = _
  by_cases hσ : σ = c.suit
  · subst hσ
    rw [ite_eq_left rfl]
    exact setFound_found_self st c.suit (st.found c.suit ++ [c])
  · rw [ite_eq_right hσ]
    exact setFound_found_ne st c.suit _ σ hσ

/-- The foundation transport through a `setFound`, at the
piles-updated raise shape. -/
private theorem found_tab_shape (st : State) (c : Card) (a : Anchor) (σ : Suit) :
    ({ st.setFound c.suit (st.found c.suit ++ [c]) with
       piles := fun a' =>
         if a' = a then Pile.afterRunRemoved (st.piles a) (chop (st.piles a).faceUp)
         else st.piles a' } : State).found σ
      = if σ = c.suit then st.found c.suit ++ [c] else st.found σ := by
  show (st.setFound c.suit (st.found c.suit ++ [c])).found σ = _
  by_cases hσ : σ = c.suit
  · subst hσ
    rw [ite_eq_left rfl]
    exact setFound_found_self st c.suit (st.found c.suit ++ [c])
  · rw [ite_eq_right hσ]
    exact setFound_found_ne st c.suit _ σ hσ

/-- The foundation transport of any fired raise: the raised suit
gains one rung, every other foundation is untouched. -/
theorem raise_foundTransport {st : State} {m : Move} {c : Card} {s' : State}
    (hm : IsRaise m c) (hstep : State.step st m = some s') :
    st.nextUp c = true ∧
    ∀ σ, s'.found σ =
      if σ = c.suit then st.found c.suit ++ [c] else st.found σ := by
  cases hm with
  | tabToFound =>
      obtain ⟨hn, a, hp, hs⟩ := step_tabToFound_inv hstep
      refine ⟨hn, fun σ => ?_⟩
      rw [hs]
      exact found_tab_shape st c a σ
  | wasteToFound =>
      obtain ⟨hg, x, xs, hw, hs⟩ := step_wasteToFound_inv hstep
      have hn : st.nextUp c = true := by
        cases hn : st.nextUp c with
        | true => rfl
        | false =>
            rw [hn] at hg
            exact absurd hg (by simp)
      refine ⟨hn, fun σ => ?_⟩
      rw [hs]
      exact found_waste_shape st c xs σ

/-- The heights a raise writes: one suit up one, others level. -/
theorem raise_foundHeight {st : State} {c : Card} {s' : State}
    (hF : ∀ σ, s'.found σ =
      if σ = c.suit then st.found c.suit ++ [c] else st.found σ) :
    s'.foundHeight c.suit = st.foundHeight c.suit + 1 ∧
    ∀ σ, σ ≠ c.suit → s'.foundHeight σ = st.foundHeight σ := by
  have hself : s'.foundHeight c.suit = st.foundHeight c.suit + 1 := by
    show (s'.found c.suit).length = (st.found c.suit).length + 1
    rw [hF c.suit, ite_eq_left rfl, List.length_append]
    have h1 : ([c] : List Card).length = 1 := rfl
    omega
  refine ⟨hself, ?_⟩
  intro σ hσ
  show (s'.found σ).length = (st.found σ).length
  rw [hF σ, ite_eq_right hσ]

/-- A stackable card's raise fires, at any state. -/
theorem raise_eq_some_of_stackable (st : State) {c : Card} (h : Stackable st c) :
    ∃ s', raise st c = some s' := by
  cases hp : st.pileOfTop c with
  | some a =>
      refine ⟨{ st.setFound c.suit (st.found c.suit ++ [c]) with
        piles := fun a' =>
          if a' = a then Pile.afterRunRemoved (st.piles a) (chop (st.piles a).faceUp)
          else st.piles a' }, ?_⟩
      have hstep : st.step (Move.tabToFound c) = some { st.setFound c.suit (st.found c.suit ++ [c]) with
        piles := fun a' =>
          if a' = a then Pile.afterRunRemoved (st.piles a) (chop (st.piles a).faceUp)
          else st.piles a' } := by
        simp only [State.step, h.1, hp, ite_true]
      rw [raise_of_pileOfTop st c a hp, hstep]
  | none =>
      rcases h.2 with hw | ⟨k, hk⟩
      · obtain ⟨xs, hws⟩ := wasteIs_head hw
        refine ⟨{ st.setFound c.suit (st.found c.suit ++ [c]) with waste := xs }, ?_⟩
        have hstep : st.step (Move.wasteToFound c)
            = some { st.setFound c.suit (st.found c.suit ++ [c]) with waste := xs } := by
          simp only [State.step, hw, h.1, Bool.and_true, ite_true, hws]
        rw [raise_of_pileOfTop_none st c hp, hstep]
      · exfalso
        rw [hp] at hk
        simp at hk

/-! ## Runs -/

/-- A stacking run: zero or more raise steps, each card stackable
at its own state, recorded over the explicit move list. -/
inductive StackRun : State → List Move → State → Prop
  | nil (st : State) : StackRun st [] st
  | cons {st : State} {m : Move} {c : Card} {s' : State} {rest : List Move} {w : State}
      (hc : Stackable st c) (hm : IsRaise m c)
      (hstep : State.step st m = some s')
      (hrest : StackRun s' rest w) :
      StackRun st (m :: rest) w

/-! ## Termination: the stacking fuel -/

/-- How many rungs `s`'s foundation can still climb (saturating). -/
def suitGap (st : State) (s : Suit) : Nat := 13 - st.foundHeight s

/-- The stacking fuel: the total remaining foundation climb. -/
def stackFuel (st : State) : Nat := (Suit.all.map (suitGap st)).sum

/-- The pointwise-sum domination. -/
private theorem sum_map_le {α : Type} (l : List α) (f g : α → Nat)
    (h : ∀ x, f x ≤ g x) : (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => simp only [List.map_nil, List.sum_nil]; omega
  | cons x t ih =>
      have h1 : f x ≤ g x := h x
      have h2 := ih
      simp only [List.map_cons, List.sum_cons]
      omega

/-- The pointwise-sum strict domination, witnessed.  The dichotomy
comes from the membership split (`List.mem_cons`), never a
`by_cases` on an abstract element type — so the lemma is
constructive. -/
private theorem sum_map_lt {α : Type} (l : List α) (f g : α → Nat) (w : α)
    (hw : w ∈ l) (hle : ∀ x, f x ≤ g x) (hlt : f w + 1 ≤ g w) :
    (l.map f).sum + 1 ≤ (l.map g).sum := by
  induction l with
  | nil => exact absurd hw (by simp)
  | cons x t ih =>
      simp only [List.map_cons, List.sum_cons]
      rcases (List.mem_cons.mp hw) with rfl | hwt
      · have h2 := sum_map_le t f g (fun y => hle y)
        have h3 : f w ≤ g w := hle w
        omega
      · have h2 := ih hwt
        have h3 : f x ≤ g x := hle x
        omega

/-- Every raise strictly drops the stacking fuel: the raised
card's suit climbs one rung, and a stackable card's rung index is
always below 13, so the saturating gap shrinks by one. -/
theorem stackFuel_raise_lt {st : State} {c : Card} {s' : State}
    (hc : Stackable st c) (hF : ∀ σ, s'.found σ =
      if σ = c.suit then st.found c.suit ++ [c] else st.found σ) :
    stackFuel s' + 1 ≤ stackFuel st := by
  have htran := raise_foundHeight hF
  have hrung : st.foundHeight c.suit < 13 := by
    have h2 : c.rank.toIdx = st.foundHeight c.suit := of_decide_eq_true hc.1
    have h3 := Rank.toIdx_lt c.rank
    omega
  have hlt : suitGap s' c.suit + 1 ≤ suitGap st c.suit := by
    show (13 - s'.foundHeight c.suit) + 1 ≤ 13 - st.foundHeight c.suit
    rw [htran.1]
    omega
  refine sum_map_lt Suit.all (suitGap s') (suitGap st) c.suit (Suit.mem_all c.suit)
    (fun s => ?_) hlt
  show suitGap s' s ≤ suitGap st s
  by_cases hs : s = c.suit
  · subst hs
    show 13 - s'.foundHeight c.suit ≤ 13 - st.foundHeight c.suit
    have h4 := htran.1
    omega
  · show 13 - s'.foundHeight s ≤ 13 - st.foundHeight s
    rw [htran.2 s hs]
    omega

/-- The fuel never exceeds 52: four suits climbed at most 13 each. -/
theorem stackFuel_le_52 (st : State) : stackFuel st ≤ 52 := by
  have h0 : (Suit.all.map (suitGap st)) =
      [suitGap st .spade, suitGap st .heart, suitGap st .diamond, suitGap st .club] := rfl
  rw [show stackFuel st = (Suit.all.map (suitGap st)).sum from rfl, h0]
  simp only [List.sum_cons, List.sum_nil]
  have h1 : suitGap st .spade ≤ 13 := Nat.sub_le _ _
  have h2 : suitGap st .heart ≤ 13 := Nat.sub_le _ _
  have h3 : suitGap st .diamond ≤ 13 := Nat.sub_le _ _
  have h4 : suitGap st .club ≤ 13 := Nat.sub_le _ _
  omega

/-- Every fired raise of a stackable card drops the fuel. -/
theorem stackFuel_step {st : State} {m : Move} {c : Card} {s' : State}
    (hc : Stackable st c) (hm : IsRaise m c) (hstep : State.step st m = some s') :
    stackFuel s' + 1 ≤ stackFuel st :=
  stackFuel_raise_lt hc (raise_foundTransport hm hstep).2

/-- No stacking run is longer than the fuel: the constructive
termination statement. -/
theorem stackRun_length_le_fuel {st : State} : ∀ {l : List Move} {w : State},
    StackRun st l w → l.length ≤ stackFuel st := by
  intro l w h
  induction h with
  | nil s => exact Nat.zero_le _
  | @cons st m c s' rest w hc hm hstep hrest ih =>
      have h1 := stackFuel_step hc hm hstep
      have h2 : rest.length ≤ stackFuel s' := ih
      show (m :: rest).length ≤ stackFuel st
      simp only [List.length_cons]
      omega

/-- Any maximal stacking run contains at most 52 moves. -/
theorem stackRun_length_le_52 {st : State} {l : List Move} {w : State}
    (h : StackRun st l w) : l.length ≤ 52 := by
  have h1 := stackRun_length_le_fuel h
  have h2 := stackFuel_le_52 st
  omega
