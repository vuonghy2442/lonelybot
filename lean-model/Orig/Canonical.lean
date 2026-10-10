import Orig.Irreversible
import Orig.Phase
import Orig.Combine

/-!
# Orig — the canonicalization theorem

`FUTURES-ORIG.md` §3.0, the program's FIRST ticket, in the
formulation the user locked mid-card on 2026-10-06 (superseding
§3.0's sketch and the first M1 landing: *we only limit ourselves to
REVERSIBLE stacking, and at the same time we show the canonical
state is also in the same macro state, because everything is
reversible*).

## The stacking system (V2: reversible stacking only)

The canonicalizer contains only raises that are reversible at
their own state — each step carries its one-move undo from the
landed witness family (`Orig.Irreversible`):

* a tableau raise of a rung-ready pile top whose seat survives as a
  refillable base — the *under-seat* license
  (`chop (st.piles a).faceUp ≠ []`: undo by `foundToTab` onto the
  exposed base, `tabToFound_undo_under`), or
  the *bare king* license (`(st.piles a).hidden = [] ∧
  c.rank = .king`: undo slides the king back onto the emptied
  seat, `tabToFound_undo_bare`).

Explicitly EXCLUDED by the correction:

* revealing raises — a reveal strictly drops `hiddenTotal`, which
  no play ever raises, so a revealing step is a commitment: it
  crosses the macro boundary, and the fiber would split
  RevEqW-class-mates (a saturated mate obtained by reversibly
  COVERING the raisable top saturates differently, at a different
  hidden total — the two canons would be unjoinable);
* bare non-king raises — the emptied seat admits no non-king
  placement, the undo's `canPlace` guard dies, same split;
* waste raises — `wasteToFound` strictly drops `cycleCount` (never
  raised by any play): a popped card can never return to the
  waste head, so pops are commitments and stay out.

So the waste (and stock) are untouched by the canonicalizer
throughout, `Final` means *no licensed raise remains* (a saturated
state may still hold a raw-stackable waste head), and §3.0's
waste-prefix corner leaves CLAIM 1 entirely — it cannot arise in a
system with no pops.

Definitions:

* `Stackable` — the RAW §3.0 reading (rung complete, waste head or
  pile top), kept for reference and later chapters;
* `CanRaise` — the license (rung + seat + under/bare-king shape);
  `canRaiseB` its decidable probe, `pick` the first licensed card
  in universe order;
* `IsRaise m c` — the licensed move (`Move.tabToFound c`);
  `raise st c` the fired licensed lift;
* `StackRun st l w` — zero or more licensed lifts, inductive over
  the move list;
* `Final st` — no licensed lift remains.

## Termination (CLAIM 1's measure side)

`stackFuel` — the total remaining foundation climb, `Σ_s (13 -
foundHeight s)` with truncated subtraction: every licensed lift
strictly drops it (the raised card's suit gains one rung, so the
same card is never lifted twice in one run), it never exceeds 52,
and therefore every stacking run is at most 52 moves long
(`stackRun_length_le_fuel`, `stackRun_length_le_52`).  Wild-safe
at every state: `nextUp` alone pins the rung index below 13.

## CLAIM 1 (`canon_unique`)

All maximal licensed runs from a `WF` position end at the same
state: `stackRun_final_eq_canon` — every run ending `Final` ends
at `canon st` — via the literal local diamonds (`lift_diamond`:
two lifts of different cards touch disjoint suits and disjoint
anchors, so both orders land at the same state) and fuel
induction.  The `WF` fence (equivalently for this chapter: the
cardCount half) is load-bearing: the private wild witness at the
bottom of this file exhibits a duplicated-card position whose two
maximal licensed runs end at different states (the search hijack:
a duplicated card's `pileOfTop` pins the wrong bare seat and
freezes the license).

## The core new theorem (the user's second clause)

`canon_reversibleW : u.WF → ShufflePlayW u (canonical schedule)
(canon u)` — every licensed lift is `reversibleAtW` at `WF`
states (the landed undo family, premises discharged by the license
and WF), so the whole saturation is a witness shuffle with the
reverse ladder for the return; hence

* `canon_class : u.WF → RevEqW u (canon u)` — the canonical state
  is INSIDE the state's own reversible orbit: same macro state,
  literally;
* `canonQ_of_orbit` — the uniform fiber spine: `WF` states in one
  `sameOrbitSetoid` orbit have equal wrapped canons.

Because of the spine, CLAIM 2's invariance family lands through
one argument shape (whatever proves two states ⟦·⟧-equal proves
their canons ⟦·⟧-equal):

* `sameMacro_liftStep` — a licensed lift step;
* `sameMacro_foundToTab` — a reversible descent;
* `sameMacro_tabToTab_quiet` — a reversible residue relocation
  (the LITERAL canon level still fails on the twin-residue
  relocation — private witness at the bottom of the file — which
  is the evidence for the wrapped ⟦·⟧ form of the fiber and this
  card's answer to §3.0's open design question);
* `sameMacro_twin`, with the structural conjugation
  `canon (twinMap u) = twinMap (canon u)`;
* `sameMacro_swRot` — in-phase stock/waste rotations, through
  `SWComp u v`, the hypothesis-named draw-zone relation whose
  default is the witness-backed rotation closure built from
  Phase's in-phase relation (the user's pending confirm —
  restating `SWComp` re-points the family below without touching
  the statements).

`sameFate` tie: DEFERRED, out of scope for this card (§3.0
explicitly parks it); nothing here speaks to `sameFate`.

## HEADS DIGEST for the major-theorem assembly card (§3.1)

The exact heads the next card consumes, as this file's public
surface:

* the stacking system: `Stackable`, `CanRaise`, `canRaiseB`,
  `pick`, `IsRaise`, `raise`, `StackRun st l w`, `Final st`;
* termination: `stackFuel`, `stackRun_length_le_fuel`,
  `stackRun_length_le_52`;
* CLAIM 1: `canon st`, `canon_run`, `stackRun_final_eq_canon`,
  `canon_unique`;
* the class spine: `liftStep_reversibleW`, `canon_reversibleW`,
  `canon_class`, `canonQ_of_orbit`;
* CLAIM 2: `SameMacroO`, `same_macro_iff`, the family
  `sameMacro_liftStep`, `sameMacro_foundToTab`,
  `sameMacro_tabToTab_quiet`, `sameMacro_twin`, `canon_twinMap`,
  `sameMacro_swRot`;
* the witnesses are PRIVATE — evidence, not surface.

Axiom discipline: `[propext, Quot.sound]` at worst, zero
`Classical.choice`, zero `sorry`, no `native_decide`; `simp` is
avoided on decision-shaped goals in favor of the
`ite_eq_left`/`ite_eq_right` + `omega` idiom; per-declaration
`#print axioms` audit at file bottom.
-/

/-! ## The raw notion (§3.0's verbatim reading) -/

/-- The decidable probe matching `Stackable`. -/
def stackableB (st : State) (c : Card) : Bool :=
  st.nextUp c && (st.wasteIs c || (st.pileOfTop c).isSome)

/-- A card is *stackable* in the raw §3.0 sense: its suit rung is
complete and it sits at the waste head or on a pile top. -/
def Stackable (st : State) (c : Card) : Prop :=
  st.nextUp c = true ∧ (st.wasteIs c = true ∨ ∃ a, st.pileOfTop c = some a)

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
    · simp only [stackableB, hn, hw, Bool.true_and, Bool.true_or]
    · have hisSome : (st.pileOfTop c).isSome = true := by
        rw [ha]
        rfl
      simp only [stackableB, hn, hisSome, Bool.true_and, Bool.or_true]

/-! ## The license -/

/-- The reversible-stacking license: the card's rung is ready, it
tops a pile, and its seat survives as a refillable base —
under-seat (the face-up run keeps a card below, so the undo
`foundToTab` lands on that base), or bare king (the emptied seat
readmits the king by `canPlace`).  Revealing lifts and bare
non-king lifts are barred (they are commitments of the physical
game), and the waste is no part of the canonicalizer at all. -/
def CanRaise (st : State) (c : Card) : Prop :=
  st.nextUp c = true ∧ ∃ a, st.pileOfTop c = some a ∧
    (chop (st.piles a).faceUp ≠ [] ∨
      ((st.piles a).hidden = [] ∧ c.rank = Rank.king))

/-- The decidable probe of the license. -/
def canRaiseB (st : State) (c : Card) : Bool :=
  st.nextUp c &&
  match st.pileOfTop c with
  | none => false
  | some a =>
      decide (chop (st.piles a).faceUp ≠ []) ||
      (decide ((st.piles a).hidden = []) && decide (c.rank = Rank.king))

/-- The probe agrees with the license. -/
theorem canRaiseB_true_iff {st : State} {c : Card} :
    canRaiseB st c = true ↔ CanRaise st c := by
  constructor
  · intro h
    rw [canRaiseB] at h
    rw [Bool.and_eq_true] at h
    refine ⟨h.1, ?_⟩
    cases hp : st.pileOfTop c with
    | some a =>
        simp only [hp] at h
        rw [Bool.or_eq_true] at h
        refine ⟨a, rfl, ?_⟩
        rcases h.2 with h2 | h2
        · left
          exact of_decide_eq_true h2
        · rw [Bool.and_eq_true] at h2
          right
          exact ⟨of_decide_eq_true h2.1, of_decide_eq_true h2.2⟩
    | none =>
        simp only [hp] at h
        exact absurd h.2 (by simp)
  · rintro ⟨hn, a, hp, (hpre | ⟨hhid, hk⟩)⟩
    · rw [canRaiseB, hn, hp]
      simp only [Bool.true_and]
      rw [Bool.or_eq_true]
      exact Or.inl (decide_eq_true hpre)
    · rw [canRaiseB, hn, hp]
      simp only [Bool.true_and]
      rw [Bool.or_eq_true, Bool.and_eq_true]
      exact Or.inr ⟨decide_eq_true hhid, decide_eq_true hk⟩

/-- The FIRE of saturation: no licensed lift remains. -/
def Final (st : State) : Prop := ∀ c, ¬ CanRaise st c

/-- The first licensed card in universe order. -/
def pick (st : State) : Option Card :=
  firstWhere (canRaiseB st) Card.universe

/-- Every card is a search candidate: a `none` result means every
candidate failed. -/
private theorem firstWhere_none_complete {p : Card → Bool} :
    ∀ {l : List Card}, firstWhere p l = none → ∀ c ∈ l, p c = false := by
  intro l
  induction l with
  | nil => intro _ c hc; exact absurd hc (by simp)
  | cons x t ih =>
      intro h c hc
      rw [firstWhere] at h
      split at h
      · rename_i hp
        exact absurd h (by simp)
      · rename_i hp
        rcases (List.mem_cons.mp hc) with rfl | hm
        · exact hp
        · exact ih h c hm

/-- Every candidate failing gives `none`. -/
private theorem firstWhere_none_of_all {p : Card → Bool} :
    ∀ {l : List Card}, (∀ c ∈ l, p c = false) → firstWhere p l = none := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons x t ih =>
      intro h
      rw [firstWhere, h x (by simp), ih (fun c hc => h c (by simp [hc]))]

/-- No licensed lift anywhere: the `none` reading of `pick`. -/
theorem pick_eq_none_iff_final (st : State) :
    pick st = none ↔ Final st := by
  constructor
  · intro h c hlic
    have hall := firstWhere_none_complete (p := canRaiseB st)
      (l := Card.universe) h c (Card.mem_universe c)
    rw [show canRaiseB st c = true from canRaiseB_true_iff.2 hlic] at hall
    exact absurd hall (by simp)
  · intro h
    exact firstWhere_none_of_all (p := canRaiseB st) (fun c _ => by
      cases hb : canRaiseB st c with
      | true => exact absurd (canRaiseB_true_iff.1 hb) (h c)
      | false => rfl)

/-- A `some` from `pick` is licensed. -/
theorem pick_some_canRaise {st : State} {c : Card} (h : pick st = some c) :
    CanRaise st c :=
  canRaiseB_true_iff.1 (firstWhere_sound _ h)

/-! ## Licensed lifts -/

/-- A licensed move is always the tableau raise; waste raises are
outside the canonicalizer (the user's correction: a pop drops the
cycle count irreversibly). -/
inductive IsRaise : Move → Card → Prop
  | tabToFound (c : Card) : IsRaise (Move.tabToFound c) c

/-- The licensed stacking step of `c`, as an optional successor. -/
def raise (st : State) (c : Card) : Option State :=
  st.step (Move.tabToFound c)

/-- A successful tableau lift, as a shape lemma. -/
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
piles-updated lift shape. -/
private theorem found_lift_shape (st : State) (c : Card) (a : Anchor) (σ : Suit) :
    ({ st.setFound c.suit (st.found c.suit ++ [c]) with
       piles := fun a' =>
         if a' = a then Pile.afterRunRemoved (st.piles a) (chop (st.piles a).faceUp)
         else st.piles a' } : State).found σ
      = if σ = c.suit then st.found c.suit ++ [c] else st.found σ := by
  show (st.setFound c.suit (st.found c.suit ++ [c])).found σ = _
  by_cases hσ : σ = c.suit
  · rw [ite_eq_left hσ, hσ]
    exact setFound_found_self st c.suit (st.found c.suit ++ [c])
  · rw [ite_eq_right hσ]
    exact setFound_found_ne st c.suit _ σ hσ

/-- The foundation transport of any licensed lift: the raised suit
gains one rung, every other foundation is untouched. -/
theorem raise_foundTransport {st : State} {c : Card} {s' : State}
    (hstep : State.step st (Move.tabToFound c) = some s') :
    st.nextUp c = true ∧
    ∀ σ, s'.found σ =
      if σ = c.suit then st.found c.suit ++ [c] else st.found σ := by
  obtain ⟨hn, a, hp, hs⟩ := step_tabToFound_inv hstep
  refine ⟨hn, fun σ => ?_⟩
  rw [hs]
  exact found_lift_shape st c a σ

/-- The heights a licensed lift writes: one suit up one, others level. -/
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

/-- A licensed card's lift fires, at any state. -/
theorem raise_eq_some_of_canRaise (st : State) {c : Card} (h : CanRaise st c) :
    ∃ s', raise st c = some s' := by
  obtain ⟨hn, a, hp, -⟩ := h
  refine ⟨{ st.setFound c.suit (st.found c.suit ++ [c]) with
    piles := fun a' =>
      if a' = a then Pile.afterRunRemoved (st.piles a) (chop (st.piles a).faceUp)
      else st.piles a' }, ?_⟩
  show st.step (Move.tabToFound c) = _
  simp only [State.step, hn, hp, ite_true]

/-! ## Runs -/

/-- A stacking run: zero or more licensed lifts, each recorded over
the explicit move list. -/
inductive StackRun : State → List Move → State → Prop
  | nil (st : State) : StackRun st [] st
  | cons {st : State} {m : Move} {c : Card} {s' : State} {rest : List Move} {w : State}
      (hc : CanRaise st c) (hm : IsRaise m c)
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
  | nil => exact Nat.le_refl 0
  | cons x t ih =>
      have h1 : f x ≤ g x := h x
      have h2 := ih
      simp only [List.map_cons, List.sum_cons]
      omega

/-- The pointwise-sum strict domination, witnessed, with the
membership split done by `List.mem_cons` — no `by_cases` on an
abstract element type. -/
private theorem sum_map_lt {α : Type} (l : List α) (f g : α → Nat) (w : α)
    (hw : w ∈ l) (hle : ∀ x, f x ≤ g x) (hlt : f w + 1 ≤ g w) :
    (l.map f).sum + 1 ≤ (l.map g).sum := by
  induction l with
  | nil => exact absurd hw (by simp)
  | cons x t ih =>
      rcases (List.mem_cons.mp hw) with h' | h'
      · rw [h'] at hlt
        have h2 := sum_map_le t f g hle
        simp only [List.map_cons, List.sum_cons]
        omega
      · have h2 := ih h'
        have h3 : f x ≤ g x := hle x
        simp only [List.map_cons, List.sum_cons]
        omega

/-- Every licensed lift strictly drops the stacking fuel: the
raised card's suit climbs one rung, and a rung-ready card's index
is always below 13, so the saturating gap shrinks by one. -/
theorem stackFuel_raise_lt {st : State} {c : Card} {s' : State}
    (hn : st.nextUp c = true) (hF : ∀ σ, s'.found σ =
      if σ = c.suit then st.found c.suit ++ [c] else st.found σ) :
    stackFuel s' + 1 ≤ stackFuel st := by
  have htran := raise_foundHeight hF
  have hlt : suitGap s' c.suit + 1 ≤ suitGap st c.suit := by
    show (13 - s'.foundHeight c.suit) + 1 ≤ 13 - st.foundHeight c.suit
    have h1 : st.foundHeight c.suit < 13 := by
      have h2 : c.rank.toIdx = st.foundHeight c.suit := of_decide_eq_true hn
      have h3 := Rank.toIdx_lt c.rank
      omega
    rw [htran.1]
    omega
  refine sum_map_lt Suit.all (suitGap s') (suitGap st) c.suit (Suit.mem_all c.suit)
    (fun s => ?_) hlt
  show suitGap s' s ≤ suitGap st s
  by_cases hs : s = c.suit
  · subst hs
    have h1 : st.foundHeight c.suit < 13 := by
      have h2 : c.rank.toIdx = st.foundHeight c.suit := of_decide_eq_true hn
      have h3 := Rank.toIdx_lt c.rank
      omega
    have hg := htran.1
    show 13 - s'.foundHeight c.suit ≤ 13 - st.foundHeight c.suit
    omega
  · have hg := (htran.2 s hs).symm
    show 13 - s'.foundHeight s ≤ 13 - st.foundHeight s
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

/-- Every fired licensed lift drops the fuel. -/
theorem stackFuel_step {st : State} {m : Move} {c : Card} {s' : State}
    (hm : IsRaise m c) (hstep : State.step st m = some s') :
    stackFuel s' + 1 ≤ stackFuel st := by
  have hstep' : State.step st (Move.tabToFound c) = some s' := by
    cases hm
    exact hstep
  obtain ⟨hn, hF⟩ := raise_foundTransport hstep'
  exact stackFuel_raise_lt hn hF

/-- No stacking run is longer than the fuel: the constructive
termination statement. -/
theorem stackRun_length_le_fuel {st : State} : ∀ {l : List Move} {w : State},
    StackRun st l w → l.length ≤ stackFuel st := by
  intro l w h
  induction h with
  | nil s => exact Nat.zero_le _
  | @cons st m c s' rest w hc hm hstep hrest ih =>
      have h1 := stackFuel_step hm hstep
      have h2 : rest.length ≤ stackFuel s' := ih
      show (m :: rest).length ≤ stackFuel st
      simp only [List.length_cons]
      omega

/-- Any maximal licensed run contains at most 52 moves. -/
theorem stackRun_length_le_52 {st : State} {l : List Move} {w : State}
    (h : StackRun st l w) : l.length ≤ 52 := by
  have h1 := stackRun_length_le_fuel h
  have h2 := stackFuel_le_52 st
  omega

/-! ## The occurrence kit at `WF` states

The fences of this chapter consume the occurrence half of `WF`:
every real card sits in exactly one place.  The zone algebra below
re-derives, privately and locally, the small pieces the count
transport needs — the siblings of `Orig.Integrity`'s private
occurrence machinery are listed for the harvest desk's dedup.
-/

/-- The list-map congruence used to shuffle zone functions. -/
private theorem map_congr_eq {α β : Type} {l : List α} {f g : α → β}
    (h : ∀ x ∈ l, f x = g x) : l.map f = l.map g := by
  induction l with
  | nil => rfl
  | cons y t ih =>
      have h1 : f y = g y := h y (by simp)
      have h2 := ih (fun z hz => h z (by simp [hz]))
      simp only [List.map_cons, h1, h2]

/-- The flat-map append split (same lemma as `Orig.Integrity`'s
private `flatMapAppend` and witnesses elsewhere; a dedup
candidate). -/
private theorem flatMap_append {α β : Type} (f : α → List β) :
    ∀ (A B : List α), List.flatMap f (A ++ B) = List.flatMap f A ++ List.flatMap f B := by
  intro A
  induction A with
  | nil => intro B; rfl
  | cons x t ih =>
      intro B
      show f x ++ List.flatMap f (t ++ B) = (f x ++ List.flatMap f t) ++ List.flatMap f B
      rw [ih, List.append_assoc]

/-- The filtered flat map length, split at a list boundary. -/
private theorem flat_filter_length_split {x : Card} :
    ∀ (Z1 Z2 : List (List Card)),
    (((Z1 ++ Z2).flatMap id).filter fun y => decide (y = x)).length =
    ((Z1.flatMap id).filter fun y => decide (y = x)).length +
    ((Z2.flatMap id).filter fun y => decide (y = x)).length := by
  intro Z1 Z2
  show (((Z1 ++ Z2).flatMap id).filter fun y => decide (y = x)).length =
    ((Z1.flatMap id).filter fun y => decide (y = x)).length +
    ((Z2.flatMap id).filter fun y => decide (y = x)).length
  rw [flatMap_append, List.filter_append, List.length_append]

/-- Each occurrence of `c` contributes one to the filtered count
(`Orig.Integrity`'s private `count_filter_pos`; dedup candidate). -/
private theorem count_filter_pos {c : Card} :
    ∀ {l : List Card}, c ∈ l → 1 ≤ (l.filter fun y => decide (y = c)).length := by
  intro l hmem
  have hm : c ∈ l.filter fun y => decide (y = c) := List.mem_filter.2 ⟨hmem, by simp⟩
  exact List.length_pos_of_mem hm

/-- A card with no occurrence filters to length zero. -/
private theorem filter_length_zero_of_not_mem {c : Card} : ∀ {l : List Card},
    ¬ c ∈ l → (l.filter fun y => decide (y = c)).length = 0 := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons x t ih =>
      intro h
      cases hxc : decide (x = c) with
      | true =>
          have hx : x = c := of_decide_eq_true hxc
          have hxmem : c ∈ x :: t := by simp [hx]
          exact absurd hxmem h
      | false =>
          rw [List.filter_cons,
            ite_eq_right (show ¬(decide (x = c) = true) from by rw [hxc]; simp)]
          exact ih (fun hm => h (List.mem_cons_of_mem _ hm))

/-- The zero-terminal filter of a card under `if`-free tails. -/
private theorem filter_snoc_card {x c : Card} : ∀ {l : List Card},
    ((l ++ [c]).filter fun y => decide (y = x)).length =
    (l.filter fun y => decide (y = x)).length +
    (if x = c then 1 else 0) := by
  intro l
  have hsplit : ((l ++ [c]).filter fun y => decide (y = x)).length =
      (l.filter fun y => decide (y = x)).length +
      ([c].filter fun y => decide (y = x)).length := by
    rw [List.filter_append, List.length_append]
  rw [hsplit]
  cases hxc : (decide (x = c)) with
  | true =>
      have hx : x = c := of_decide_eq_true hxc
      rw [hx]
      have hfc : ([c].filter fun y => decide (y = c)) = [c] := by
        show (c :: ([] : List Card)).filter (fun y => decide (y = c)) = [c]
        rw [List.filter_cons, show decide (c = c) = true from decide_eq_true rfl]
        rfl
      rw [hfc, ite_eq_left rfl]
      rfl
  | false =>
      have hnc : ¬ (x = c) := by
        intro heq
        rw [heq] at hxc
        exact absurd hxc (by simp)
      have hfc : ([c].filter fun y => decide (y = x)) = [] := by
        show (c :: ([] : List Card)).filter (fun y => decide (y = x)) = []
        rw [List.filter_cons,
          show decide (c = x) = false from decide_eq_false (fun heq => hnc heq.symm)]
        rfl
      rw [hfc, ite_eq_right hnc]
      show (l.filter fun y => decide (y = x)).length + 0 =
        (l.filter fun y => decide (y = x)).length + 0
      rfl

/-! ### Zone splits and per-slot transports -/

private def preAnchors : Anchor → List Anchor
  | .p0 => [] | .p1 => [.p0] | .p2 => [.p0, .p1] | .p3 => [.p0, .p1, .p2]
  | .p4 => [.p0, .p1, .p2, .p3] | .p5 => [.p0, .p1, .p2, .p3, .p4]
  | .p6 => [.p0, .p1, .p2, .p3, .p4, .p5]

private def sufAnchors : Anchor → List Anchor
  | .p0 => [.p1, .p2, .p3, .p4, .p5, .p6] | .p1 => [.p2, .p3, .p4, .p5, .p6]
  | .p2 => [.p3, .p4, .p5, .p6] | .p3 => [.p4, .p5, .p6]
  | .p4 => [.p5, .p6] | .p5 => [.p6] | .p6 => []

/-- (A private copy of `Orig.Integrity`'s same-named private; a dedup
candidate.) -/
private theorem anchor_split (a : Anchor) :
    Anchor.all = preAnchors a ++ [a] ++ sufAnchors a := by cases a <;> rfl

private def preSuits : Suit → List Suit
  | .spade => [] | .heart => [.spade] | .diamond => [.spade, .heart]
  | .club => [.spade, .heart, .diamond]

private def sufSuits : Suit → List Suit
  | .spade => [.heart, .diamond, .club] | .heart => [.diamond, .club]
  | .diamond => [.club] | .club => []

private theorem suit_split (σ : Suit) :
    Suit.all = preSuits σ ++ [σ] ++ sufSuits σ := by cases σ <;> rfl

private theorem pre_suits_ne (σ : Suit) : ∀ τ ∈ preSuits σ, τ ≠ σ := by
  cases σ <;> intro τ hτ heq <;> rw [heq] at hτ <;> simp [preSuits] at hτ

private theorem suf_suits_ne (σ : Suit) : ∀ τ ∈ sufSuits σ, τ ≠ σ := by
  cases σ <;> intro τ hτ heq <;> rw [heq] at hτ <;> simp [sufSuits] at hτ

private theorem pre_anchors_ne (a : Anchor) : ∀ a' ∈ preAnchors a, a' ≠ a := by
  cases a <;> intro a' ha' heq <;> rw [heq] at ha' <;> simp [preAnchors] at ha'

private theorem suf_anchors_ne (a : Anchor) : ∀ a' ∈ sufAnchors a, a' ≠ a := by
  cases a <;> intro a' ha' heq <;> rw [heq] at ha' <;> simp [sufAnchors] at ha'

/-- One pile's whole zone, hidden cards under face up. -/
private def pileZone (st : State) (a : Anchor) : List Card :=
  (st.piles a).hidden ++ (st.piles a).faceUp

/-- The flat-map congruence over zone functions. -/
private theorem flat_congr {α β : Type} {l : List α} {f g : α → List β}
    (h : ∀ x ∈ l, f x = g x) : l.flatMap f = l.flatMap g := by
  induction l with
  | nil => rfl
  | cons y t ih =>
      have h1 : f y = g y := h y (by simp)
      have h2 := ih (fun z hz => h z (by simp [hz]))
      show f y ++ List.flatMap f t = g y ++ List.flatMap g t
      rw [h1, h2]

/-- The zones, cut down the middle at two winner slots: the `σ`
foundation and the `a` pile zone. -/
private theorem zones_split_two_slots (st : State) (σ : Suit) (a : Anchor) :
    st.zones =
      (preSuits σ).map st.found ++ [st.found σ] ++ (sufSuits σ).map st.found ++
      (preAnchors a).map (fun x => pileZone st x) ++ [pileZone st a] ++
      (sufAnchors a).map (fun x => pileZone st x) ++ [st.stock, st.waste] := by
  cases σ <;> cases a <;> rfl

/-- The count contribution of a group of zones. -/
private def zoneCount (Z : List (List Card)) (x : Card) : Nat :=
  ((Z.flatMap id).filter fun y => decide (y = x)).length

private theorem cardCount_split (st : State) {x : Card} {Z1 Z2 : List (List Card)}
    (h : st.zones = Z1 ++ Z2) :
    st.cardCount x = zoneCount Z1 x + zoneCount Z2 x := by
  show (((st.zones.flatMap id).filter fun y => decide (y = x)).length) =
    zoneCount Z1 x + zoneCount Z2 x
  rw [h, flatMap_append, List.filter_append, List.length_append]
  rfl

/-- The count of one zone: the flat census is the per-zone sum. -/
private theorem zoneCount_coll {Z : List (List Card)} (x : Card) :
    zoneCount Z x = (Z.map fun z => (z.filter fun y => decide (y = x)).length).sum := by
  unfold zoneCount
  induction Z with
  | nil => rfl
  | cons z t ih =>
      show ((z ++ t.flatMap id).filter fun y => decide (y = x)).length =
        ((z.filter fun y => decide (y = x)).length +
          (t.map fun z => (z.filter fun y => decide (y = x)).length).sum)
      rw [List.filter_append, List.length_append, ih]

/-- A zone group containing a membership-bearing zone list
contributes at least one. -/
private theorem zoneCount_ge_of_mem {Z : List (List Card)} {z : List Card} {c : Card}
    (hzin : z ∈ Z) (hmem : c ∈ z) : 1 ≤ zoneCount Z c := by
  induction Z with
  | nil => cases hzin
  | cons y t ih =>
      rcases (List.mem_cons.mp hzin) with rfl | hm
      · show 1 ≤ ((z ++ t.flatMap id).filter fun u => decide (u = c)).length
        rw [List.filter_append, List.length_append]
        have h1 := count_filter_pos hmem
        omega
      · have h1 := ih hm
        rw [zoneCount] at h1
        show 1 ≤ ((y ++ t.flatMap id).filter fun u => decide (u = c)).length
        rw [List.filter_append, List.length_append]
        omega

/-- A zone group holding `c` in a cons leaf contributes at least
the leaf's count: cons-guarded lowering. -/
private theorem zoneCount_cons_lower {z : List Card} {Z : List (List Card)} {c : Card}
    (hle : 1 ≤ (z.filter fun y => decide (y = c)).length) :
    1 ≤ zoneCount (z :: Z) c := by
  show 1 ≤ ((z ++ Z.flatMap id).filter fun y => decide (y = c)).length
  rw [List.filter_append, List.length_append]
  omega

/-- The plain two-part filter split. -/
private theorem filter_len_split {x : Card} : ∀ {l1 l2 : List Card},
    ((l1 ++ l2).filter fun y => decide (y = x)).length =
    (l1.filter fun y => decide (y = x)).length +
    (l2.filter fun y => decide (y = x)).length := by
  intro l1 l2
  rw [List.filter_append, List.length_append]

/-! ### The rank enumeration and the `runOK` chop -/

/-- The rank enumeration inversion: a rank is its table position. -/
private theorem rank_all_getIdx (r : Rank) {k : Nat} (h : r.toIdx = k) :
    r = Rank.all[k]'(by rw [← h]; exact Rank.toIdx_lt r) := by
  cases r <;> simp only [Rank.toIdx] at h <;> subst h <;> rfl

/-- `take (n+1)` is `take n` plus the next element. -/
private theorem take_snoc_get (n : Nat) : ∀ (l : List Card) (hl : n < l.length),
    l.take (n+1) = l.take n ++ [l[n]'hl] := by
  induction n with
  | zero =>
      intro l hl
      cases l with
      | nil => exact absurd hl (by simp)
      | cons y t => rfl
  | succ n ih =>
      intro l hl
      cases l with
      | nil => exact absurd hl (by simp)
      | cons y t =>
          have hlt : n < t.length := by
            simp only [List.length_cons] at hl
            omega
          have hrec := ih t hlt
          have e1 : (y :: t).take (n + 1 + 1) = y :: t.take (n + 1) := rfl
          have e2 : (y :: t).take (n + 1) = y :: t.take n := rfl
          have e3 : ((y :: t) : List Card)[n + 1]'(by show n + 1 < t.length + 1; omega) = t[n] := rfl
          rw [e1, e2, e3, hrec, List.cons_append]

/-- A legal run stays legal after chopping its top card. -/
private theorem runOK_chop : ∀ {l : List Card}, runOK l = true → runOK (chop l) = true := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons x t ih =>
      intro h
      cases t with
      | nil => rfl
      | cons y t' =>
          have hc0 : chop (x :: y :: t') = x :: chop (y :: t') := rfl
          rw [hc0]
          cases t' with
          | nil =>
              have hc1 : chop (y :: ([] : List Card)) = [] := rfl
              rw [hc1]
              rfl
          | cons z t'' =>
              have hexp : runOK (x :: y :: z :: t'') =
                  (canSitOn y x && runOK (y :: z :: t'')) := rfl
              rw [hexp, Bool.and_eq_true] at h
              have hi := ih h.2
              have hc2 : chop (y :: z :: t'') = y :: chop (z :: t'') := rfl
              rw [hc2] at hi
              show runOK (x :: y :: chop (z :: t'')) = true
              rw [runOK, h.1, hi]
              rfl

/-- A legal run sits each card on the one below: the premise of
the under-seat undo. -/
private theorem runOK_snoc_sit {c : Card} : ∀ {l : List Card}, l ≠ [] →
    runOK (l ++ [c]) = true → ∃ z, lastOf l = some z ∧ canSitOn c z = true := by
  intro l
  induction l with
  | nil => intro hne _; exact absurd rfl hne
  | cons x t ih =>
      intro _ h
      cases t with
      | nil =>
          refine ⟨x, rfl, ?_⟩
          have hexp : runOK (x :: ([] : List Card) ++ [c]) = (canSitOn c x && true) := rfl
          rw [hexp, Bool.and_true] at h
          exact h
      | cons y t' =>
          have hexp : runOK (x :: (y :: t') ++ [c]) =
              (canSitOn y x && runOK ((y :: t') ++ [c])) := rfl
          rw [hexp, Bool.and_eq_true] at h
          obtain ⟨z, hz, hsit⟩ := ih (by simp) h.2
          exact ⟨z, hz, hsit⟩

/-- A nonempty list has a last element. -/
private theorem lastOf_exists : ∀ {l : List Card}, l ≠ [] → ∃ z, lastOf l = some z := by
  intro l
  induction l with
  | nil => intro hne; exact absurd rfl hne
  | cons x t ih =>
      intro _
      cases t with
      | nil => exact ⟨x, rfl⟩
      | cons y t' =>
          obtain ⟨z, hz⟩ := ih (by simp)
          have hll : lastOf (x :: y :: t') = lastOf (y :: t') := rfl
          exact ⟨z, by rw [hll]; exact hz⟩

/-! ### The licensed lift preserves `WF` -/

private theorem zoneCount_split {Z1 Z2 : List (List Card)} (x : Card) :
    zoneCount (Z1 ++ Z2) x = zoneCount Z1 x + zoneCount Z2 x :=
  flat_filter_length_split Z1 Z2

private theorem zoneCount_single (z : List Card) (x : Card) :
    zoneCount [z] x = (z.filter fun y => decide (y = x)).length := by
  have h : ([z] : List (List Card)).flatMap id = z ++ ([] : List Card) := rfl
  rw [zoneCount, h, List.append_nil]

/-- The foundations, cut around the `σ` slot. -/
private theorem zoneCount_suits_inv {F : Suit → List Card} {σ : Suit} (x : Card) :
    zoneCount (Suit.all.map F) x =
    zoneCount ((preSuits σ).map F) x + zoneCount [F σ] x +
    zoneCount ((sufSuits σ).map F) x := by
  have hsplit : (preSuits σ).map F ++ [F σ] ++ (sufSuits σ).map F = Suit.all.map F := by
    cases σ <;> rfl
  rw [← hsplit, zoneCount_split, zoneCount_split]

/-- The foundations' slot arithmetic: appending one card in the `σ`
slot changes the census by exactly it. -/
private theorem zoneCount_suits_congr {F G : Suit → List Card} {σ : Suit} {c x : Card}
    (hne : ∀ τ, τ ≠ σ → F τ = G τ) (hsl : F σ = G σ ++ [c]) :
    zoneCount (Suit.all.map F) x =
    zoneCount (Suit.all.map G) x + (if x = c then 1 else 0) := by
  rw [zoneCount_suits_inv (F := F) (σ := σ), zoneCount_suits_inv (F := G) (σ := σ)]
  rw [map_congr_eq (fun τ hτ => hne τ (pre_suits_ne σ τ hτ)),
    map_congr_eq (fun τ hτ => hne τ (suf_suits_ne σ τ hτ)), hsl]
  rw [zoneCount_single, zoneCount_single, filter_snoc_card]
  cases hxc : (decide (x = c)) with
  | true =>
      have hx : x = c := of_decide_eq_true hxc
      rw [ite_eq_left hx]
      omega
  | false =>
      have hx : ¬ (x = c) := by
        intro heq
        rw [heq] at hxc
        exact absurd hxc (by simp)
      rw [ite_eq_right hx]
      omega

/-- The piles, cut around the `a` slot. -/
private theorem zoneCount_anchors_inv {F : Anchor → List Card} {a : Anchor} (x : Card) :
    zoneCount (Anchor.all.map F) x =
    zoneCount ((preAnchors a).map F) x + zoneCount [F a] x +
    zoneCount ((sufAnchors a).map F) x := by
  have hsplit : (preAnchors a).map F ++ [F a] ++ (sufAnchors a).map F = Anchor.all.map F := by
    cases a <;> rfl
  rw [← hsplit, zoneCount_split, zoneCount_split]

/-- A zone holding `c` both in a leading part and a trailing part
counts it at least twice. -/
private theorem zoneCount_ge_two_within (l1 l2 : List Card) (c : Card)
    (h1 : c ∈ l1) (h2 : c ∈ l2) {Z : List (List Card)} (hz : l1 ++ l2 ∈ Z) :
    2 ≤ zoneCount Z c := by
  induction Z with
  | nil => cases hz
  | cons y t ih =>
      rcases (List.mem_cons.mp hz) with heq | hm
      · subst heq
        show 2 ≤ (((l1 ++ l2) ++ t.flatMap id).filter fun u => decide (u = c)).length
        rw [show (l1 ++ l2 ++ t.flatMap id) = l1 ++ (l2 ++ t.flatMap id) from
            List.append_assoc l1 l2 (t.flatMap id),
          filter_len_split, filter_len_split]
        have g1 := count_filter_pos h1
        have g2 := count_filter_pos h2
        omega
      · have h2' := ih hm
        rw [zoneCount] at h2'
        show 2 ≤ ((y ++ t.flatMap id).filter fun u => decide (u = c)).length
        rw [List.filter_append, List.length_append]
        omega

/-- The piles' slot arithmetic: the seat that loses its top card
loses it exactly once, given the card sits nowhere else in the
seat's zone. -/
private theorem zoneCount_anchors_congr {F G : Anchor → List Card} {a : Anchor} {c x : Card}
    {hz zm : List Card}
    (hne : ∀ a', a' ≠ a → F a' = G a')
    (hslotF : F a = hz ++ (zm ++ [c])) (hslotG : G a = hz ++ zm)
    (hchz : c ∉ hz) (hczm : c ∉ zm) :
    zoneCount (Anchor.all.map F) x =
    zoneCount (Anchor.all.map G) x + (if x = c then 1 else 0) := by
  rw [zoneCount_anchors_inv (F := F) (a := a), zoneCount_anchors_inv (F := G) (a := a)]
  rw [map_congr_eq (fun a' h' => hne a' (pre_anchors_ne a a' h')),
    map_congr_eq (fun a' h' => hne a' (suf_anchors_ne a a' h')), hslotF, hslotG]
  rw [zoneCount_single, zoneCount_single, filter_len_split,
    filter_snoc_card, filter_len_split]
  have g1 : ∀ l : List Card, ¬ c ∈ l → (l.filter fun u => decide (u = c)).length = 0 :=
    fun l h => filter_length_zero_of_not_mem h
  have e1 := g1 _ hchz
  have e2 := g1 _ hczm
  cases hxc : (decide (x = c)) with
  | true =>
      have hx : x = c := of_decide_eq_true hxc
      rw [hx]
      rw [ite_eq_left rfl, e1, e2]
      omega
  | false =>
      have hx : ¬ (x = c) := by
        intro heq
        rw [heq] at hxc
        exact absurd hxc (by simp)
      rw [ite_eq_right hx]
      omega


/-- The zone of the raised seat, before and after: a licensed lift
permutes no hidden card and leaves the chopped face-up run. -/
theorem lift_seatZone_eq {st : State} {c : Card} {a : Anchor} {s' : State}
    (hshape : s' = { st.setFound c.suit (st.found c.suit ++ [c]) with
      piles := fun x => if x = a then
        Pile.afterRunRemoved (st.piles a) (chop (st.piles a).faceUp) else st.piles x })
    (hunder : chop (st.piles a).faceUp ≠ [] ∨ (st.piles a).hidden = []) :
    s'.piles a = { st.piles a with faceUp := chop (st.piles a).faceUp } := by
  rw [hshape]
  show (if a = a then
      Pile.afterRunRemoved (st.piles a) (chop (st.piles a).faceUp) else st.piles a) = _
  rw [ite_eq_left rfl]
  cases hchop : chop (st.piles a).faceUp with
  | cons z zs => rfl
  | nil =>
      rcases hunder with hne | hhid
      · exact absurd hchop hne
      · rcases hpcont : (st.piles a) with ⟨hdc, fdc⟩
        have hh2 : hdc = [] := by
          rw [hpcont] at hhid
          exact hhid
        rw [hh2]
        rfl

/-- A card is its own suit's next build slot (getD form, no index
side goals). -/
private theorem upCards_getD_eq_self (c : Card) :
    (Suit.upCards c.suit).getD c.rank.toIdx c = c := by
  rcases c with ⟨s, r⟩
  cases s <;> cases r <;> rfl

/-- **A licensed lift preserves `WF`** — the four clauses:
foundations stay prefixes of the build order (the raised card is
exactly the next rung), every face-up run stays legal (chopping
the top of a legal run is legal, and a licensed bare lift empties
an empty-hidden seat), the census is conserved (the card moves
from its seat to its foundation, and nothing else moves), and the
draw step stands. -/
theorem lift_wf {st : State} {c : Card} {s' : State}
    (hwf : st.WF) (hlic : CanRaise st c)
    (hstep : State.step st (Move.tabToFound c) = some s') : s'.WF := by
  obtain ⟨hn, al, hp, hbranch⟩ := hlic
  obtain ⟨-, a, hpa, hshape⟩ := step_tabToFound_inv hstep
  rw [hp] at hpa
  injection hpa with hal
  have hla : a = al := hal.symm
  subst hla
  obtain ⟨-, hF⟩ := raise_foundTransport hstep
  have hunderOr : chop (st.piles a).faceUp ≠ [] ∨ (st.piles a).hidden = [] := by
    rcases hbranch with h | ⟨h1, -⟩
    · exact Or.inl h
    · exact Or.inr h1
  have hpseat : s'.piles a = { st.piles a with faceUp := chop (st.piles a).faceUp } :=
    lift_seatZone_eq hshape hunderOr
  have hpother : ∀ x, x ≠ a → s'.piles x = st.piles x := by
    intro x hx
    rw [hshape]
    show (if x = a then
        Pile.afterRunRemoved (st.piles a) (chop (st.piles a).faceUp) else st.piles x) = _
    rw [ite_eq_right hx]
  obtain ⟨-, hfull⟩ := pileOfTop_top hp
  have hsnoc : (st.piles a).faceUp = chop (st.piles a).faceUp ++ [c] := lastOf_chop hfull
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro σ
    by_cases hσ : σ = c.suit
    · rw [hσ]
      obtain ⟨k, hk⟩ := hwf.1 c.suit
      have hklen : st.foundHeight c.suit = k := by
        show (st.found c.suit).length = k
        have hrk := Rank.toIdx_lt c.rank
        have hsu : c.rank.toIdx = (st.found c.suit).length := of_decide_eq_true hn
        have hlen := Suit.upCards_length c.suit
        have hsu2 : c.rank.toIdx = min k 13 := by
          rw [hsu, hk, List.length_take, hlen]
        rw [hk, List.length_take, hlen]
        omega
      have hidx : c.rank.toIdx = k := by
        have h2 : c.rank.toIdx = st.foundHeight c.suit := of_decide_eq_true hn
        rw [h2, hklen]
      have hlen13 : (Suit.upCards c.suit).length = 13 := Suit.upCards_length c.suit
      have hall : k < 13 := by
        have h1 := Rank.toIdx_lt c.rank
        have h2 : c.rank.toIdx = k := hidx
        omega
      have hkl : k < (Suit.upCards c.suit).length := by
        rw [hlen13]
        exact hall
      have hnext : (Suit.upCards c.suit).take (k+1) =
          (Suit.upCards c.suit).take k ++ [c] := by
        rw [take_snoc_get k (Suit.upCards c.suit) hkl]
        show (Suit.upCards c.suit).take k ++ [(Suit.upCards c.suit)[k]'hkl] = _
        rw [show (Suit.upCards c.suit)[k]'hkl =
              (Suit.upCards c.suit).getD k c from List.getElem_eq_getD c,
          show (Suit.upCards c.suit).getD k c = c from by
            rw [← hidx]
            exact upCards_getD_eq_self c]
      refine ⟨k + 1, ?_⟩
      rw [hF c.suit, ite_eq_left rfl]
      show st.found c.suit ++ [c] = (Suit.upCards c.suit).take (k+1)
      rw [hk, hnext]
    · obtain ⟨k, hk⟩ := hwf.1 σ
      exact ⟨k, by rw [hF σ, ite_eq_right hσ, hk]⟩
  · intro x
    by_cases hx : x = a
    · rw [hx]
      cases hchop : chop (st.piles a).faceUp with
      | cons z zs =>
          show runOK (s'.piles a).faceUp = true
          rw [hpseat]
          exact runOK_chop (hwf.2.1 a)
      | nil =>
          show runOK (s'.piles a).faceUp = true
          rw [hpseat, hchop]
          rfl
    · show runOK (s'.piles x).faceUp = true
      rw [hpother x hx]
      exact hwf.2.1 x
  · intro x hxu
    -- the raised card occurs only at its seat's top: three exclusions
    -- from the census, then the slot arithmetic cancels its move
    have hmemF : c ∈ pileZone st a := by
      show c ∈ (st.piles a).hidden ++ (st.piles a).faceUp
      rw [hsnoc]
      exact List.mem_append.mpr (Or.inr (by simp))
    have hszod : (st.piles a).hidden ++ (chop (st.piles a).faceUp ++ [c]) = pileZone st a := by
      show (st.piles a).hidden ++ (chop (st.piles a).faceUp ++ [c]) = _
      rw [← hsnoc]
      rfl
    have hsph : ((st.piles a).hidden ++ chop (st.piles a).faceUp) ++ [c] = pileZone st a := by
      rw [List.append_assoc]
      exact hszod
    have hsplitZones : st.zones = (Suit.all.map st.found) ++
        ((Anchor.all.map (fun x' => pileZone st x')) ++ [st.stock, st.waste]) := rfl
    have hT := cardCount_split st (x := c) hsplitZones
    have hcount1 := hwf.2.2.1 c (Card.mem_universe c)
    have hPZmem : pileZone st a ∈ Anchor.all.map (fun x' => pileZone st x') :=
      List.mem_map_of_mem (f := fun x' => pileZone st x') (Anchor.mem_all a)
    have hcF : c ∉ st.found c.suit := by
      intro hmem
      have hFslotmem : st.found c.suit ∈ Suit.all.map st.found :=
        List.mem_map_of_mem (f := st.found) (Suit.mem_all c.suit)
      have gz2 : pileZone st a ∈
          (Anchor.all.map (fun x' => pileZone st x')) ++ [st.stock, st.waste] :=
        List.mem_append.mpr (Or.inl hPZmem)
      have g1 := zoneCount_ge_of_mem hFslotmem hmem
      have g2 := zoneCount_ge_of_mem gz2 hmemF
      omega
    have hchz : c ∉ (st.piles a).hidden := by
      intro hmem
      have hmemhz : c ∈ (st.piles a).hidden ++ chop (st.piles a).faceUp :=
        List.mem_append.mpr (Or.inl hmem)
      have hmemtop : c ∈ [c] := by simp
      have g2 : 2 ≤ zoneCount (Anchor.all.map (fun x' => pileZone st x')) c := by
        refine zoneCount_ge_two_within ((st.piles a).hidden ++ chop (st.piles a).faceUp)
          [c] c hmemhz hmemtop ?_
        rw [hsph]
        exact hPZmem
      have hT2 : zoneCount (Anchor.all.map (fun x' => pileZone st x') ++ [st.stock, st.waste]) c =
          zoneCount (Anchor.all.map (fun x' => pileZone st x')) c +
          zoneCount [st.stock, st.waste] c :=
        zoneCount_split (Z1 := Anchor.all.map (fun x' => pileZone st x'))
          (Z2 := [st.stock, st.waste]) c
      rw [hT2] at hT
      omega
    have hczz : c ∉ chop (st.piles a).faceUp := by
      intro hmem
      have hmemloc : c ∈ (st.piles a).hidden ++ chop (st.piles a).faceUp :=
        List.mem_append.mpr (Or.inr hmem)
      have hmemtop : c ∈ [c] := by simp
      have g2 : 2 ≤ zoneCount (Anchor.all.map (fun x' => pileZone st x')) c := by
        refine zoneCount_ge_two_within ((st.piles a).hidden ++ chop (st.piles a).faceUp)
          [c] c hmemloc hmemtop ?_
        rw [hsph]
        exact hPZmem
      have hT2 : zoneCount (Anchor.all.map (fun x' => pileZone st x') ++ [st.stock, st.waste]) c =
          zoneCount (Anchor.all.map (fun x' => pileZone st x')) c +
          zoneCount [st.stock, st.waste] c :=
        zoneCount_split (Z1 := Anchor.all.map (fun x' => pileZone st x'))
          (Z2 := [st.stock, st.waste]) c
      rw [hT2] at hT
      omega
    -- the three-part census identities per side
    have hks : s'.stock = st.stock := by
      rw [hshape]
      exact setFound_stock st c.suit (st.found c.suit ++ [c])
    have hkw : s'.waste = st.waste := by
      rw [hshape]
      exact setFound_waste st c.suit (st.found c.suit ++ [c])
    have eF := zoneCount_suits_congr (F := s'.found) (G := st.found) (σ := c.suit)
      (c := c) (x := x) (fun τ hτ => by rw [hF τ, ite_eq_right hτ])
      (by rw [hF c.suit, ite_eq_left rfl])
    have hzP : pileZone st a = (st.piles a).hidden ++ (chop (st.piles a).faceUp ++ [c]) := by
      rw [← hszod]
    have hzP' : pileZone s' a = (st.piles a).hidden ++ chop (st.piles a).faceUp := by
      show (s'.piles a).hidden ++ (s'.piles a).faceUp = _
      rw [hpseat]
    have eP := zoneCount_anchors_congr (F := fun x' => pileZone st x')
      (G := fun x' => pileZone s' x') (a := a) (c := c) (x := x)
      (hz := (st.piles a).hidden) (zm := chop (st.piles a).faceUp)
      (fun a' ha' => by
        show (st.piles a').hidden ++ (st.piles a').faceUp =
          (s'.piles a').hidden ++ (s'.piles a').faceUp
        rw [hpother a' ha'])
      hzP (by rw [hzP'])
      hchz hczz
    have eDW : zoneCount [s'.stock, s'.waste] x = zoneCount [st.stock, st.waste] x := by
      rw [hks, hkw]
    have hTst : st.cardCount x = zoneCount (Suit.all.map st.found) x +
        (zoneCount (Anchor.all.map (fun x' => pileZone st x')) x +
        zoneCount [st.stock, st.waste] x) := by
      have h1 := cardCount_split st (x := x) hsplitZones
      have h2 : zoneCount (Anchor.all.map (fun x' => pileZone st x') ++ [st.stock, st.waste]) x =
          zoneCount (Anchor.all.map (fun x' => pileZone st x')) x +
          zoneCount [st.stock, st.waste] x :=
        zoneCount_split (Z1 := Anchor.all.map (fun x' => pileZone st x'))
          (Z2 := [st.stock, st.waste]) x
      omega
    have hTsx : s'.cardCount x = zoneCount (Suit.all.map s'.found) x +
        (zoneCount (Anchor.all.map (fun x' => pileZone s' x')) x +
        zoneCount [s'.stock, s'.waste] x) := by
      have hz2 : s'.zones = (Suit.all.map s'.found) ++
          ((Anchor.all.map (fun x' => pileZone s' x')) ++ [s'.stock, s'.waste]) := rfl
      have h1 := cardCount_split s' (x := x) hz2
      have h2 : zoneCount (Anchor.all.map (fun x' => pileZone s' x') ++ [s'.stock, s'.waste]) x =
          zoneCount (Anchor.all.map (fun x' => pileZone s' x')) x +
          zoneCount [s'.stock, s'.waste] x :=
        zoneCount_split (Z1 := Anchor.all.map (fun x' => pileZone s' x'))
          (Z2 := [s'.stock, s'.waste]) x
      omega
    have hxs1 : st.cardCount x = 1 := hwf.2.2.1 x hxu
    -- the goal, in the s' pieces
    show s'.cardCount x = 1
    rw [hTsx, eDW]
    cases hxc : (decide (x = c)) with
    | true =>
        have hx : x = c := of_decide_eq_true hxc
        rw [ite_eq_left hx] at eF eP
        omega
    | false =>
        have hx : ¬ (x = c) := by
          intro heq
          rw [heq] at hxc
          exact absurd hxc (by simp)
        rw [ite_eq_right hx] at eF eP
        omega
  · have hds : s'.drawStep = st.drawStep := by
      rw [hshape]
      exact setFound_drawStep st c.suit (st.found c.suit ++ [c])
    rw [hds]
    exact hwf.2.2.2

/-- Every state of a stacking run from a `WF` origin stays `WF`:
the licensed lift preserves all four clauses, so induction over
the run carries the origin's invariant.  The step-preservation
ticket of the open chapter list holds for the canonicalizer's
two raises. -/
theorem stackRun_wf {st : State} (hwf : st.WF) {l : List Move} {w : State}
    (h : StackRun st l w) : w.WF := by
  induction h with
  | nil s => exact hwf
  | @cons st₀ m c s' rest w hc hm hstep hrest ih =>
      have hstep' : State.step st₀ (Move.tabToFound c) = some s' := by
        cases hm
        exact hstep
      exact ih (lift_wf hwf hc hstep')

/-! ### Monone stackability: the license survives another lift -/

/-- Two rung-ready cards of one suit would be one card. -/
private theorem nextUp_suit_disjoint {st : State} {c d : Card}
    (hc : st.nextUp c = true) (hd : st.nextUp d = true) (hne : c ≠ d) :
    c.suit ≠ d.suit := by
  intro hs
  apply hne
  have h1 : c.rank.toIdx = st.foundHeight c.suit := of_decide_eq_true hc
  have h2 : d.rank.toIdx = st.foundHeight d.suit := of_decide_eq_true hd
  have h3 : st.foundHeight c.suit = st.foundHeight d.suit := by rw [hs]
  have h4 : c.rank.toIdx = d.rank.toIdx := by omega
  have h5 : c.rank = d.rank := Rank.toIdx_inj h4
  show c = d
  rcases c with ⟨s, r⟩
  rcases d with ⟨s', r'⟩
  have h1 : s = s' := hs
  have h2 : r = r' := h5
  rw [h1, h2]

/-- The foundation projection of a `setFound`. -/
private theorem setFound_field (st : State) (s : Suit) (l : List Card) (σ : Suit) :
    (st.setFound s l).found σ = if σ = s then l else st.found σ := by
  by_cases hσ : σ = s
  · rw [hσ, ite_eq_left rfl]
    exact setFound_found_self st s l
  · rw [ite_eq_right hσ]
    exact setFound_found_ne st s l σ hσ

/-- **(2a) Monotone stackability for the license**: after a
licensed lift of another card, `c`'s license survives — its suit's
foundation is untouched (different suit by rung injectivity), its
seat's shape is untouched (a different anchor, since two tops of
one pile would be one card), and the pile-top search still pins
the same seat. -/
theorem canRaise_lifted {st : State} {c d : Card} {s' : State}
    (hwf : st.WF) (hc : CanRaise st c) (hd : CanRaise st d) (hne : c ≠ d)
    (hstep : State.step st (Move.tabToFound d) = some s') :
    CanRaise s' c := by
  obtain ⟨hnc, ac, hpc, hsc⟩ := hc
  obtain ⟨-, ad', hpd', hshape⟩ := step_tabToFound_inv hstep
  have hs'wf : s'.WF := lift_wf hwf hd hstep
  obtain ⟨hnd, ad, hpd, -⟩ := hd
  rw [hpd] at hpd'
  injection hpd' with hdd
  rw [← hdd] at hshape
  -- the seats differ (two tops of one pile would be one card)
  have hane : ac ≠ ad := by
    intro heq
    apply hne
    have t1 := pileOfTop_top hpc
    have t2 := pileOfTop_top hpd
    rw [heq] at t1
    exact Option.some.inj (t1.2.symm.trans t2.2)
  have hsd : c.suit ≠ d.suit := nextUp_suit_disjoint hnc hnd hne
  have hnp : (s').nextUp c = true := by
    have hF := (raise_foundTransport hstep).2
    show decide (c.rank.toIdx = ((s').found c.suit).length) = true
    rw [hF c.suit, ite_eq_right hsd]
    exact hnc
  have hpac : (s').piles ac = st.piles ac := by
    rw [hshape]
    show (if ac = ad then
        Pile.afterRunRemoved (st.piles ad) (chop (st.piles ad).faceUp)
        else st.piles ac) = _
    rw [ite_eq_right hane]
  have hsr : (s').pileOfTop c = some ac :=
    (pileOfTop_eq_some_iff hs'wf).2 (by
      show ((s').piles ac).top = some c
      rw [hpac]
      exact (pileOfTop_eq_some_iff hwf).1 hpc)
  have hshp : chop ((s').piles ac).faceUp ≠ [] ∨
      ((s').piles ac).hidden = [] ∧ c.rank = Rank.king := by
    rw [hpac]
    exact hsc
  exact ⟨hnp, ac, hsr, hshp⟩

/-! ### The local diamond: licensed lifts commute literally -/

/-- The join comparison: two licensed lifts of different cards
update disjoint suits and disjoint seats, so the two composite
states coincide field by field. -/
private theorem lift_join_eq (st xc xd : State) (c d : Card) (ac ad : Anchor)
    (hsd : c.suit ≠ d.suit) (hane : ac ≠ ad)
    (hxcF : ∀ σ, xc.found σ = if σ = c.suit then st.found c.suit ++ [c] else st.found σ)
    (hxdF : ∀ σ, xd.found σ = if σ = d.suit then st.found d.suit ++ [d] else st.found σ)
    (hxcP : ∀ a, xc.piles a = if a = ac then
        Pile.afterRunRemoved (st.piles ac) (chop (st.piles ac).faceUp) else st.piles a)
    (hxdP : ∀ a, xd.piles a = if a = ad then
        Pile.afterRunRemoved (st.piles ad) (chop (st.piles ad).faceUp) else st.piles a)
    (hxcS : xc.stock = st.stock) (hxcW : xc.waste = st.waste) (hxcD : xc.drawStep = st.drawStep)
    (hxdS : xd.stock = st.stock) (hxdW : xd.waste = st.waste) (hxdD : xd.drawStep = st.drawStep)
    (M1 : State)
    (hM1 : M1 = { xc.setFound d.suit (xc.found d.suit ++ [d]) with
        piles := fun a => if a = ad then
          Pile.afterRunRemoved (xc.piles ad) (chop (xc.piles ad).faceUp)
          else xc.piles a })
    (M2 : State)
    (hM2 : M2 = { xd.setFound c.suit (xd.found c.suit ++ [c]) with
        piles := fun a => if a = ac then
          Pile.afterRunRemoved (xd.piles ac) (chop (xd.piles ac).faceUp)
          else xd.piles a }) :
    M1 = M2 := by
  have hxoad : xc.piles ad = st.piles ad := by
    rw [hxcP ad, ite_eq_right (fun h => hane h.symm)]
  have hdoad : xd.piles ad =
      Pile.afterRunRemoved (st.piles ad) (chop (st.piles ad).faceUp) := by
    rw [hxdP ad, ite_eq_left rfl]
  have hdoac : xd.piles ac = st.piles ac := by
    rw [hxdP ac, ite_eq_right hane]
  rw [hM1, hM2]
  refine State.ext (funext fun σ => ?_) (funext fun a => ?_) ?_ ?_ ?_
  · show ((xc.setFound d.suit (xc.found d.suit ++ [d])).found σ) =
        ((xd.setFound c.suit (xd.found c.suit ++ [c])).found σ)
    rw [setFound_field, setFound_field]
    by_cases hσc : σ = c.suit
    · rw [hσc, ite_eq_right hsd, hxcF c.suit, ite_eq_left rfl,
        ite_eq_left rfl, hxdF c.suit, ite_eq_right hsd]
    · by_cases hσd : σ = d.suit
      · rw [hσd, ite_eq_left rfl, hxcF d.suit, ite_eq_right (fun h => hsd h.symm),
          ite_eq_right (fun h => hsd h.symm), hxdF d.suit, ite_eq_left rfl]
      · rw [ite_eq_right hσd, hxcF σ, ite_eq_right hσc, hxdF σ,
          ite_eq_right hσc, ite_eq_right hσd]
  · -- piles projection: project through the record lets, then case
    show ((fun x => if x = ad then
        Pile.afterRunRemoved (xc.piles ad) (chop (xc.piles ad).faceUp)
        else xc.piles x) a) = ((fun x => if x = ac then
        Pile.afterRunRemoved (xd.piles ac) (chop (xd.piles ac).faceUp)
        else xd.piles x) a)
    show (if a = ad then
        Pile.afterRunRemoved (xc.piles ad) (chop (xc.piles ad).faceUp)
        else xc.piles a) = (if a = ac then
        Pile.afterRunRemoved (xd.piles ac) (chop (xd.piles ac).faceUp)
        else xd.piles a)
    rw [hxcP a, hxdP a]
    rw [hxoad, hdoac]
    by_cases ha : a = ad
    · rw [ha, ite_eq_left rfl, ite_eq_left rfl,
        ite_eq_right (fun h => hane h.symm)]
    · rw [ite_eq_right ha]
      by_cases hac : a = ac
      · rw [hac, ite_eq_left rfl, ite_eq_left rfl]
      · rw [ite_eq_right hac, ite_eq_right hac, ite_eq_right ha]
  · show ((xc.setFound d.suit (xc.found d.suit ++ [d])).stock) =
        ((xd.setFound c.suit (xd.found c.suit ++ [c])).stock)
    rw [setFound_stock, setFound_stock, hxcS, hxdS]
  · show ((xc.setFound d.suit (xc.found d.suit ++ [d])).waste) =
        ((xd.setFound c.suit (xd.found c.suit ++ [c])).waste)
    rw [setFound_waste, setFound_waste, hxcW, hxdW]
  · show ((xc.setFound d.suit (xc.found d.suit ++ [d])).drawStep) =
        ((xd.setFound c.suit (xd.found c.suit ++ [c])).drawStep)
    rw [setFound_drawStep, setFound_drawStep, hxcD, hxdD]

/-- **(2) The local diamond**: two licensed lifts of different
cards, in either order, land at literally the same state — the
join comparison above.  This is the commutation the confluence
induction pivots on. -/
theorem lift_comm {st : State} {c d : Card} {xc xd : State}
    (hwf : st.WF) (hc : CanRaise st c) (hd : CanRaise st d) (hne : c ≠ d)
    (hstepc : State.step st (Move.tabToFound c) = some xc)
    (hstepd : State.step st (Move.tabToFound d) = some xd) :
    ∃ m : State, State.step xc (Move.tabToFound d) = some m ∧
      State.step xd (Move.tabToFound c) = some m ∧
      CanRaise xc d ∧ CanRaise xd c := by
  have hxcwf : xc.WF := lift_wf hwf hc hstepc
  have hxdwf : xd.WF := lift_wf hwf hd hstepd
  -- the surviving licenses on both sides
  have hd' : CanRaise xc d := canRaise_lifted hwf hd hc (fun h => hne h.symm) hstepc
  have hc' : CanRaise xd c := canRaise_lifted hwf hc hd hne hstepd
  obtain ⟨hnc, ac, hpc, -⟩ := hc
  obtain ⟨-, ac0, hpc0, xcshape⟩ := step_tabToFound_inv hstepc
  rw [hpc] at hpc0
  injection hpc0 with hca0
  subst hca0
  obtain ⟨hnd, ad, hpd, -⟩ := hd
  obtain ⟨-, ad0, hpd0, xdshape⟩ := step_tabToFound_inv hstepd
  rw [hpd] at hpd0
  injection hpd0 with hda0
  subst hda0
  have hsd : c.suit ≠ d.suit := nextUp_suit_disjoint hnc hnd hne
  have hane : ac ≠ ad := by
    intro heq
    apply hne
    have t1 := pileOfTop_top hpc
    have t2 := pileOfTop_top hpd
    rw [heq] at t1
    exact Option.some.inj (t1.2.symm.trans t2.2)
  -- their fired steps, with the seat anchors pinned to the originals
  obtain ⟨M1, hm1⟩ := raise_eq_some_of_canRaise xc hd'
  obtain ⟨M2, hm2⟩ := raise_eq_some_of_canRaise xd hc'
  obtain ⟨-, adM1, hpin1, m1shape⟩ := step_tabToFound_inv hm1
  obtain ⟨-, acM2, hpin2, m2shape⟩ := step_tabToFound_inv hm2
  -- pin M1's inv anchor: the search at xc still finds d's seat, since c's
  -- lift touched only ac ≠ ad
  have hxcPad : xc.pileOfTop d = some ad := by
    refine (pileOfTop_eq_some_iff hxcwf).2 ?_
    rw [xcshape]
    show (if ad = ac then
        Pile.afterRunRemoved (st.piles ac) (chop (st.piles ac).faceUp)
        else st.piles ad).top = some d
    rw [ite_eq_right (fun h => hane h.symm)]
    exact (pileOfTop_eq_some_iff hwf).1 hpd
  have hxdPac : xd.pileOfTop c = some ac := by
    refine (pileOfTop_eq_some_iff hxdwf).2 ?_
    rw [xdshape]
    show (if ac = ad then
        Pile.afterRunRemoved (st.piles ad) (chop (st.piles ad).faceUp)
        else st.piles ac).top = some c
    rw [ite_eq_right hane]
    exact (pileOfTop_eq_some_iff hwf).1 hpc
  rw [pileOfTop_inj hpin1 hxcPad] at m1shape
  rw [pileOfTop_inj hpin2 hxdPac] at m2shape
  -- the six transports
  have hxcF := (raise_foundTransport hstepc).2
  have hxdF := (raise_foundTransport hstepd).2
  have hxcP : ∀ a, xc.piles a = if a = ac then
      Pile.afterRunRemoved (st.piles ac) (chop (st.piles ac).faceUp)
      else st.piles a := by
    intro a
    rw [xcshape]
  have hxdP : ∀ a, xd.piles a = if a = ad then
      Pile.afterRunRemoved (st.piles ad) (chop (st.piles ad).faceUp)
      else st.piles a := by
    intro a
    rw [xdshape]
  have hxcS : xc.stock = st.stock := by
    rw [xcshape]; exact setFound_stock st c.suit (st.found c.suit ++ [c])
  have hxcW : xc.waste = st.waste := by
    rw [xcshape]; exact setFound_waste st c.suit (st.found c.suit ++ [c])
  have hxcD : xc.drawStep = st.drawStep := by
    rw [xcshape]; exact setFound_drawStep st c.suit (st.found c.suit ++ [c])
  have hxdS : xd.stock = st.stock := by
    rw [xdshape]; exact setFound_stock st d.suit (st.found d.suit ++ [d])
  have hxdW : xd.waste = st.waste := by
    rw [xdshape]; exact setFound_waste st d.suit (st.found d.suit ++ [d])
  have hxdD : xd.drawStep = st.drawStep := by
    rw [xdshape]; exact setFound_drawStep st d.suit (st.found d.suit ++ [d])
  have h12 : M1 = M2 :=
    lift_join_eq st xc xd c d ac ad hsd hane hxcF hxdF hxcP hxdP
      hxcS hxcW hxcD hxdS hxdW hxdD M1 m1shape M2 m2shape
  rw [← h12] at hm2
  exact ⟨M1, hm1, hm2, hd', hc'⟩

/-! ### The canonicalizer -/

/-- One saturation step: lift the first licensed card in universe
order; a state with no license holds. -/
def satStep (st : State) : State :=
  match pick st with
  | none => st
  | some c => (raise st c).getD st

/-- The deterministic saturator at budget `n`. -/
def canonAux : Nat → State → State
  | 0, st => st
  | n+1, st => canonAux n (satStep st)

/-- The canonical form of a state: the saturator run to
exhaustion — 52 lifts always suffice, since every lift strictly
drops the fuel and the fuel never exceeds 52. -/
def canon (st : State) : State := canonAux 53 st

theorem satStep_none {st : State} (h : pick st = none) : satStep st = st := by
  simp only [satStep, h]

theorem satStep_some {st : State} {c : Card} {s' : State}
    (h : pick st = some c) (hs : raise st c = some s') :
    satStep st = s' := by
  simp only [satStep, h, hs]
  rfl

/-- The fuel sum, cut around one suit. -/
private theorem nat_sum_suits_inv (g : Suit → Nat) (s : Suit) :
    (Suit.all.map g).sum =
    ((preSuits s).map g).sum + (g s + ((sufSuits s).map g).sum) := by
  have hsplit : (preSuits s ++ [s] ++ sufSuits s).map g =
      ((preSuits s).map g) ++ (g s :: ((sufSuits s).map g)) := by
    cases s <;> rfl
  rw [suit_split s, hsplit, List.sum_append, List.sum_cons]

/-- A rung-ready card's suit gap is positive. -/
theorem suitGap_pos_of_nextUp {st : State} {c : Card} (hn : st.nextUp c = true) :
    1 ≤ suitGap st c.suit := by
  have h2 : c.rank.toIdx = st.foundHeight c.suit := of_decide_eq_true hn
  have hlt := Rank.toIdx_lt c.rank
  rw [h2] at hlt
  show 1 ≤ (13 - st.foundHeight c.suit)
  omega

theorem pick_none_of_fuel_zero {st : State} (h : stackFuel st = 0) :
    pick st = none := by
  refine firstWhere_none_of_all (p := canRaiseB st) (fun c _ => ?_)
  cases hb : canRaiseB st c with
  | false => rfl
  | true =>
      obtain ⟨hn, -, -, -⟩ := canRaiseB_true_iff.1 hb
      have hg := suitGap_pos_of_nextUp hn
      have hinv := nat_sum_suits_inv (suitGap st) c.suit
      have hpre : 0 ≤ ((preSuits c.suit).map (suitGap st)).sum := Nat.zero_le _
      have hsuf : 0 ≤ ((sufSuits c.suit).map (suitGap st)).sum := Nat.zero_le _
      have hz := h
      rw [stackFuel] at hz
      omega

theorem fuel_pos_of_canRaise {st : State} {c : Card} (hcr : CanRaise st c) :
    1 ≤ stackFuel st := by
  have h1 : 1 ≤ suitGap st c.suit := suitGap_pos_of_nextUp hcr.1
  have hinv := nat_sum_suits_inv (suitGap st) c.suit
  have hpre : 0 ≤ ((preSuits c.suit).map (suitGap st)).sum := Nat.zero_le _
  have hsuf : 0 ≤ ((sufSuits c.suit).map (suitGap st)).sum := Nat.zero_le _
  rw [stackFuel, hinv]
  omega

theorem canonAux_zero (st : State) : canonAux 0 st = st := rfl

theorem canonAux_succ (n : Nat) (st : State) :
    canonAux (n+1) st = canonAux n (satStep st) := rfl

/-- A frozen (fuel-zero) state never changes under the saturator. -/
theorem canonAux_fuel_zero {st : State} (h : stackFuel st = 0) :
    ∀ b, canonAux b st = st := by
  intro b
  induction b with
  | zero => rfl
  | succ b ih =>
      rw [canonAux_succ, satStep_none (pick_none_of_fuel_zero h)]
      exact ih

/-- A final state never changes under the saturator. -/
theorem canonAux_final {st : State} (hfin : Final st) :
    ∀ n, canonAux n st = st := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [canonAux_succ, satStep_none ((pick_eq_none_iff_final st).2 hfin)]
      exact ih

/-- Saturation within the budget: a state with at most `n` fuel is
saturated after at most `n` steps. -/
theorem canonAux_final_after_fuel : ∀ (n : Nat) (st : State),
    stackFuel st ≤ n → Final (canonAux n st) := by
  intro n
  induction n with
  | zero =>
      intro st hle
      rw [canonAux_zero]
      exact (pick_eq_none_iff_final st).1 (pick_none_of_fuel_zero (Nat.le_zero.mp hle))
  | succ n ih =>
      intro st hle
      rw [canonAux_succ]
      cases hp : pick st with
      | none =>
          have hfin : Final st := (pick_eq_none_iff_final st).1 hp
          rw [satStep_none hp, canonAux_final hfin]
          exact hfin
      | some c =>
          obtain ⟨s', hs'⟩ := raise_eq_some_of_canRaise st (pick_some_canRaise hp)
          rw [satStep_some hp hs']
          have hdrop : stackFuel s' + 1 ≤ stackFuel st :=
            stackFuel_step (IsRaise.tabToFound c) hs'
          exact ih s' (by omega)

/-- Any two budgets above the fuel give the same saturation. -/
theorem canonAux_stable : ∀ (k b : Nat) (st : State),
    stackFuel st ≤ k → k ≤ b → canonAux b st = canonAux k st := by
  intro k
  induction k with
  | zero =>
      intro b st hle hkb
      have h0 : stackFuel st = 0 := Nat.le_zero.mp hle
      rw [canonAux_fuel_zero h0 b, canonAux_fuel_zero h0 0]
  | succ k ih =>
      intro b st hle hkb
      cases b with
      | zero => exact absurd hkb (Nat.not_succ_le_zero k)
      | succ b' =>
          cases hp : pick st with
          | none =>
              have hfin : Final st := (pick_eq_none_iff_final st).1 hp
              rw [canonAux_final hfin (b'+1), canonAux_final hfin (k+1)]
          | some c =>
              obtain ⟨s', hs'⟩ := raise_eq_some_of_canRaise st (pick_some_canRaise hp)
              have hsat : satStep st = s' := satStep_some hp hs'
              have hdrop : stackFuel s' + 1 ≤ stackFuel st :=
                stackFuel_step (IsRaise.tabToFound c) hs'
              rw [canonAux_succ, canonAux_succ, hsat]
              exact ih b' s' (by omega) (by omega)

/-- The canonical schedule is a stacking run ending `Final` —
constructively: induction on the budget, building the move list in
parallel with the saturation with the `StackRun` witnesses. -/
theorem canonAux_run_fuel : ∀ (n : Nat) (st : State),
    stackFuel st ≤ n → ∃ l : List Move,
      StackRun st l (canonAux n st) ∧ Final (canonAux n st) := by
  intro n
  induction n with
  | zero =>
      intro st hle
      have hp : pick st = none := pick_none_of_fuel_zero (Nat.le_zero.mp hle)
      refine ⟨[], StackRun.nil st, ?_⟩
      rw [canonAux_zero]
      exact (pick_eq_none_iff_final st).1 hp
  | succ n ih =>
      intro st hle
      cases hp : pick st with
      | none =>
          have hfin : Final st := (pick_eq_none_iff_final st).1 hp
          rw [canonAux_succ, satStep_none hp, canonAux_final hfin n]
          exact ⟨[], StackRun.nil st, hfin⟩
      | some c =>
          obtain ⟨s', hs'⟩ := raise_eq_some_of_canRaise st (pick_some_canRaise hp)
          have hsat : satStep st = s' := satStep_some hp hs'
          have hdrop : stackFuel s' + 1 ≤ stackFuel st :=
            stackFuel_step (IsRaise.tabToFound c) hs'
          obtain ⟨l, hrun, hfin⟩ := ih s' (by omega)
          rw [canonAux_succ, hsat]
          exact ⟨Move.tabToFound c :: l,
            StackRun.cons (pick_some_canRaise hp) (IsRaise.tabToFound c) hs' hrun, hfin⟩

/-- From any state, the canonical schedule saturates and ends
`Final` (52 lifts always suffice). -/
theorem canon_run (st : State) : ∃ l : List Move, StackRun st l (canon st) ∧ Final (canon st) := by
  have h := canonAux_run_fuel 53 st (by
    have := stackFuel_le_52 st
    omega)
  exact h

/-! ### CLAIM 1: confluence by Newman-style induction on the fuel -/

/-- **CLAIM 1's engine**: every maximal licensed run from a `WF`
state ends at `canon st` — by strong induction on the fuel.  The
`nil` cases are final-state freezings; the `cons` cases are the
c₀-equals-pick short-circuit and the c₀-differs-from-pick local
diamond, both closing under the IH at the reduced fuel. -/
private theorem stackRun_final_eq_canon_aux (N : Nat) :
    ∀ (st : State) (l : List Move) (w : State),
      st.WF → stackFuel st ≤ N → StackRun st l w → Final w → w = canon st := by
  induction N with
  | zero =>
      intro st l w hwf hfuel hrun hfin
      have hp : pick st = none := pick_none_of_fuel_zero (Nat.le_zero.mp hfuel)
      have hfinal : Final st := (pick_eq_none_iff_final st).1 hp
      cases hrun with
      | nil s =>
          show st = canonAux 53 st
          rw [canonAux_final hfinal 53]
      | @cons st1 m c s' rest w0 hc hm hstep hrest =>
          exact absurd hc (hfinal c)
  | succ N ih =>
      intro st l w hwf hfuel hrun hfin
      cases hp : pick st with
      | none =>
          have hfinal : Final st := (pick_eq_none_iff_final st).1 hp
          cases hrun with
          | nil s =>
              show st = canonAux 53 st
              rw [canonAux_final hfinal 53]
          | @cons st1 m c s' rest w0 hc hm hstep hrest =>
              exact absurd hc (hfinal c)
      | some cd =>
          have hcd : CanRaise st cd := pick_some_canRaise hp
          obtain ⟨s_d, hs_d⟩ := raise_eq_some_of_canRaise st hcd
          have hsat : satStep st = s_d := satStep_some hp hs_d
          have hs_dstep : State.step st (Move.tabToFound cd) = some s_d := hs_d
          have hf_s_d : stackFuel s_d + 1 ≤ stackFuel st :=
            stackFuel_step (IsRaise.tabToFound cd) hs_d
          have hwf_s_d : s_d.WF := lift_wf hwf hcd hs_d
          cases hrun with
          | nil s => exact absurd hcd (hfin cd)
          | @cons st1 m c₀ s₁ rest w0 hc₀ hm hstep hrest =>
              cases hm with
              | tabToFound =>
                  have hf_s₁ : stackFuel s₁ + 1 ≤ stackFuel st :=
                    stackFuel_step (IsRaise.tabToFound c₀) hstep
                  have hwf_s₁ : s₁.WF := lift_wf hwf hc₀ hstep
                  by_cases heq : c₀ = cd
                  · -- same first card: the successors coincide
                      subst heq
                      have hsame : s₁ = s_d :=
                        Option.some.inj (hstep.symm.trans hs_dstep)
                      rw [hsame] at hrest
                      have hw_eq := ih s_d rest w hwf_s_d (by omega) hrest hfin
                      rw [hw_eq]
                      show canon s_d = canonAux 53 st
                      rw [canonAux_succ, hsat]
                      show canonAux 53 s_d = canonAux 52 s_d
                      exact canonAux_stable 52 53 s_d
                        (by have := stackFuel_le_52 s_d; omega) (by omega)
                  · -- different first cards: the local diamond
                      have hne : c₀ ≠ cd := heq

                      -- the surviving licenses after each first step
                      have hcr₁ : CanRaise s₁ cd :=
                        canRaise_lifted hwf hcd hc₀ (fun h => heq h.symm) hstep
                      have hcr₀ : CanRaise s_d c₀ :=
                        canRaise_lifted hwf hc₀ hcd hne hs_dstep

                      -- the diamond
                      obtain ⟨m, hm₁, hm₂, -, -⟩ :=
                        lift_comm hwf hc₀ hcd hne hstep hs_dstep

                      -- canon schedule from the midpoint
                      obtain ⟨lₘ, hrunₘ, hfinₘ⟩ := canon_run m

                      -- composite from s₁: cd-lift, then canon from m
                      have hcomp₁ : StackRun s₁ (Move.tabToFound cd :: lₘ) (canon m) :=
                        StackRun.cons hcr₁ (IsRaise.tabToFound cd) hm₁ hrunₘ

                      -- composite from s_d: c₀-lift, then canon from m
                      have hcomp₀ : StackRun s_d (Move.tabToFound c₀ :: lₘ) (canon m) :=
                        StackRun.cons hcr₀ (IsRaise.tabToFound c₀) hm₂ hrunₘ

                      -- IH at s₁ through the composite
                      have hcm₁ : canon m = canon s₁ :=
                        ih s₁ (Move.tabToFound cd :: lₘ) (canon m)
                          hwf_s₁ (by have := hf_s₁; omega) hcomp₁ hfinₘ

                      -- IH at s_d through the composite
                      have hcm₀ : canon m = canon s_d :=
                        ih s_d (Move.tabToFound c₀ :: lₘ) (canon m)
                          hwf_s_d (by have := hf_s_d; omega) hcomp₀ hfinₘ

                      -- the original run's tail
                      have hw_eq : w = canon s₁ :=
                        ih s₁ rest w hwf_s₁ (by have := hf_s₁; omega) hrest hfin

                      -- assemble: w = canon s₁ = canon m = canon s_d = canon st
                      rw [hw_eq, ← hcm₁, hcm₀]
                      -- goal: canon s_d = canon st
                      show canon s_d = canonAux 53 st
                      rw [canonAux_succ, hsat]
                      show canonAux 53 s_d = canonAux 52 s_d
                      exact canonAux_stable 52 53 s_d
                        (by have := stackFuel_le_52 s_d; omega) (by omega)

/-- **CLAIM 1 (`canon_unique`)**: any two maximal licensed runs
from a `WF` state end at the same state. -/
theorem canon_unique {u : State} (hwf : u.WF)
    {l₁ l₂ : List Move} {w₁ w₂ : State}
    (hr₁ : StackRun u l₁ w₁) (hf₁ : Final w₁)
    (hr₂ : StackRun u l₂ w₂) (hf₂ : Final w₂) :
    w₁ = w₂ := by
  have h1 := stackRun_final_eq_canon_aux 52 u l₁ w₁ hwf (stackFuel_le_52 u) hr₁ hf₁
  have h2 := stackRun_final_eq_canon_aux 52 u l₂ w₂ hwf (stackFuel_le_52 u) hr₂ hf₂
  rw [h1, h2]

/-- Any licensed lift preserves the canonical level. -/
theorem canon_lift_step {st : State} {c : Card} {s' : State}
    (hwf : st.WF) (hc : CanRaise st c)
    (hstep : State.step st (Move.tabToFound c) = some s') :
    canon s' = canon st := by
  obtain ⟨l', hrun', hfin'⟩ := canon_run s'
  have hcomp : StackRun st (Move.tabToFound c :: l') (canon s') :=
    StackRun.cons hc (IsRaise.tabToFound c) hstep hrun'
  have := stackRun_final_eq_canon_aux 52 st (Move.tabToFound c :: l') (canon s')
    hwf (stackFuel_le_52 st) hcomp hfin'
  rw [← this]

/-- The canonical form is idempotent. -/
theorem canon_idempotent (st : State) : canon (canon st) = canon st := by
  obtain ⟨l, hrun, hfin⟩ := canon_run st
  show canonAux 53 (canon st) = canon st
  rw [canonAux_final hfin]

/-- The canonical form is `Final`. -/
theorem canon_is_final (st : State) : Final (canon st) := by
  obtain ⟨l, hrun, hfin⟩ := canon_run st
  exact hfin

/-! ## The macro class, written

`Orig.Combine`'s `sameOrbitSetoid` is the LANDED macro state: two
positions are identified when they are equal, twin, `RevEqW`-related,
or `RevEqW`-related through a twin.  This chapter writes its
quotient classes with the `⟦·⟧` brackets. -/

/-- The macro class of a position: its `sameOrbitSetoid` quotient
class — the macro state of `FUTURES-ORIG.md` §3.1. -/
notation "⟦" s "⟧" => Quotient.mk sameOrbitSetoid s

/-! ## The licensed lift's undo, as an explicit step equation

The landed undo family `Orig.Irreversible.tabToFound_undo_under`/`_bare`
hands out `reversibleAtW` — each licensed raise carries its one-move
return — but the return's own STEP EQUATION lives inside those
proofs.  The reverse undo-ladder below needs it as data, so the two
equations are exposed here as local mirrors (DEDUP-marked: the bodies
follow the landed family's internals exactly; at harvest, promote the
family's own internals to public step lemmas and delete these). -/

/-- One move runs by stepping it (a local kin of the private helpers
in `Orig.Shuttle` / `Orig.Phase`; a dedup candidate). -/
private theorem run_one {st : State} {m : Move} {s : State}
    (h : State.step st m = some s) : st.run [m] = some s := by
  show (match State.step st m with
    | some st' => st'.run []
    | none => none) = some s
  rw [h]
  rfl

/-- An `inr` placement, written as one state update (the local kin of
`Orig.Irreversible`'s private `putCard_inr_eq_setPile`; dedup
candidate). -/
private theorem putCard_setPile_inr {st : State} {c z : Card} {k : Anchor}
    (hz : st.pileOfTop z = some k) :
    st.putCard c (Sum.inr z) =
      { st with piles := fun a' =>
          if a' = k then { st.piles k with faceUp := (st.piles k).faceUp ++ [c] }
          else st.piles a' } := by
  simp only [State.putCard, hz]
  rfl

/-- An `inl` placement, written as one state update (the local kin of
`Orig.Irreversible`'s private `putCard_inl_eq_setPile`; dedup
candidate). -/
private theorem putCard_setPile_inl {st : State} {c : Card} {a : Anchor} :
    st.putCard c (Sum.inl a) =
      { st with piles := fun a' => if a' = a then ⟨[], [c]⟩ else st.piles a' } := by
  show (st.setPile a ⟨[], [c]⟩) = _
  rfl

/-- Removing an empty run from an empty-hidden pile gives the empty
pile (the local kin of `Orig.Irreversible`'s private
`afterRunRemoved_empty_eq` / `Orig.Classify`'s private `_eq'` farm
copy; dedup candidate). -/
private theorem afterRunRemoved_empty_of_hidden (p : Pile)
    (h : p.hidden = []) : Pile.afterRunRemoved p [] = ⟨[], []⟩ := by
  rcases p with ⟨h', f⟩
  cases h' with
  | nil => rfl
  | cons x xs => exact absurd h (by simp)

/-- **The under-seat lift's one-move undo, as a step equation**: the
local mirror of `tabToFound_undo_under`'s internal return step.  The
premises are the landed family's own, verbatim. -/
theorem raise_undo_under_step {st : State} {c : Card} {a : Anchor} {z : Card} {s₁ : State}
    (hstep : State.step st (Move.tabToFound c) = some s₁)
    (hpa : st.pileOfTop c = some a)
    (hz : lastOf (chop (st.piles a).faceUp) = some z)
    (hsit : canSitOn c z = true)
    (hsearch : s₁.pileOfTop z = some a) :
    State.step s₁ (Move.foundToTab c (Sum.inr z)) = some st := by
  obtain ⟨-, a₀, hpa₀, hs₁⟩ := step_tabToFound_inv hstep
  rw [hpa] at hpa₀
  injection hpa₀ with haa
  subst haa
  have hfull : (st.piles a).faceUp = chop (st.piles a).faceUp ++ [c] :=
    lastOf_chop (pileOfTop_top hpa).2
  have hs₁found : s₁.found c.suit = st.found c.suit ++ [c] := by
    rw [hs₁]
    exact setFound_found_self st c.suit _
  have hs₁other : ∀ σ, σ ≠ c.suit → s₁.found σ = st.found σ := by
    intro σ hσ
    rw [hs₁]
    exact setFound_found_ne st c.suit _ σ hσ
  have hft : s₁.foundTop c.suit = some c := by
    show lastOf (s₁.found c.suit) = some c
    rw [hs₁found]
    exact lastOf_snoc _ c
  have hcp : s₁.canPlace c (Sum.inr z) = true := by
    simp only [State.canPlace, hsearch]
    exact hsit
  simp only [State.step, hft]
  rw [hcp]
  refine congrArg some (?_ :
    (s₁.setFound c.suit (chop (s₁.found c.suit))).putCard c (Sum.inr z) = st)
  have hz'' : (s₁.setFound c.suit (chop (s₁.found c.suit))).pileOfTop z = some a := hsearch
  rw [putCard_setPile_inr hz'']
  refine State.ext (funext fun σ => ?_) (funext fun a'' => ?_) ?_ ?_ ?_
  · show (if σ = c.suit then chop (s₁.found c.suit) else s₁.found σ) = st.found σ
    by_cases hσ : σ = c.suit
    · rw [hσ, ite_eq_left rfl, hs₁found, chop_snoc]
    · rw [ite_eq_right hσ]
      exact hs₁other σ hσ
  · have hQ : (s₁.setFound c.suit (chop (s₁.found c.suit))).piles = s₁.piles := rfl
    rw [hQ]
    show (if a'' = a then
        { s₁.piles a with faceUp := (s₁.piles a).faceUp ++ [c] }
        else s₁.piles a'') = st.piles a''
    by_cases haa'' : a'' = a
    · rw [haa'', ite_eq_left rfl]
      have hpla : s₁.piles a =
          Pile.afterRunRemoved (st.piles a) (chop (st.piles a).faceUp) := by
        rw [hs₁]
        show (if a = a then
            Pile.afterRunRemoved (st.piles a) (chop (st.piles a).faceUp)
            else st.piles a) = _
        rw [ite_eq_left rfl]
      rw [hpla]
      cases hch : chop (st.piles a).faceUp with
      | nil =>
          rw [hch] at hz
          exact absurd hz (by simp [lastOf])
      | cons y ys =>
          rw [hch] at hfull
          show (⟨(st.piles a).hidden, (y :: ys) ++ [c]⟩ : Pile) = st.piles a
          exact Pile.ext rfl hfull.symm
    · rw [ite_eq_right haa'']
      rw [hs₁]
      show (if a'' = a then
          Pile.afterRunRemoved (st.piles a) (chop (st.piles a).faceUp)
          else st.piles a'') = st.piles a''
      rw [ite_eq_right haa'']
  · show s₁.stock = st.stock
    rw [hs₁]
    rfl
  · show s₁.waste = st.waste
    rw [hs₁]
    rfl
  · show s₁.drawStep = st.drawStep
    rw [hs₁]
    rfl

/-- **The bare-king lift's one-move undo, as a step equation**: the
local mirror of `tabToFound_undo_bare`'s internal return step.  The
premises are the landed family's own, verbatim. -/
theorem raise_undo_bare_step {st : State} {c : Card} {a : Anchor} {s₁ : State}
    (hstep : State.step st (Move.tabToFound c) = some s₁)
    (hpa : st.pileOfTop c = some a)
    (hchop : chop (st.piles a).faceUp = [])
    (hhidden : (st.piles a).hidden = [])
    (hking : c.rank = Rank.king) :
    State.step s₁ (Move.foundToTab c (Sum.inl a)) = some st := by
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
    exact setFound_found_ne st c.suit _ σ hσ
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
    exact afterRunRemoved_empty_of_hidden _ hhidden
  have hcp : s₁.canPlace c (Sum.inl a) = true := by
    show ((s₁.piles a).isEmpty && decide (c.rank = Rank.king)) = true
    rw [hpla, decide_eq_true hking]
    rfl
  simp only [State.step, hft]
  rw [hcp]
  refine congrArg some (?_ :
    (s₁.setFound c.suit (chop (s₁.found c.suit))).putCard c (Sum.inl a) = st)
  rw [putCard_setPile_inl]
  have hQ : (s₁.setFound c.suit (chop (s₁.found c.suit))).piles = s₁.piles := rfl
  rw [hQ]
  refine State.ext (funext fun σ => ?_) (funext fun a'' => ?_) ?_ ?_ ?_
  · show (if σ = c.suit then chop (s₁.found c.suit) else s₁.found σ) = st.found σ
    by_cases hσ : σ = c.suit
    · rw [hσ, ite_eq_left rfl, hs₁found, chop_snoc]
    · rw [ite_eq_right hσ]
      exact hs₁other σ hσ
  · show (if a'' = a then (⟨[], [c]⟩ : Pile) else s₁.piles a'') = st.piles a''
    by_cases haa'' : a'' = a
    · rw [haa'', ite_eq_left rfl]
      show (⟨[], [c]⟩ : Pile) = st.piles a
      have hpE : st.piles a = ⟨(st.piles a).hidden, (st.piles a).faceUp⟩ := rfl
      rw [hpE, hhidden, hface]
    · rw [ite_eq_right haa'']
      rw [hs₁]
      show (if a'' = a then
          Pile.afterRunRemoved (st.piles a) (chop (st.piles a).faceUp)
          else st.piles a'') = st.piles a''
      rw [ite_eq_right haa'']
  · show s₁.stock = st.stock
    rw [hs₁]
    rfl
  · show s₁.waste = st.waste
    rw [hs₁]
    rfl
  · show s₁.drawStep = st.drawStep
    rw [hs₁]
    rfl

/-! ## The licensed lift's witnesses at `WF` -/

/-- The under-seat license's seat facts: the card below `c` on its
seat exists, fits it (the run's legality at `WF`), and still tops the
same seat after `c`'s lift (the seat write keeps the below part). -/
private theorem lift_under_facts {st : State} {c : Card} {a : Anchor} {s₁ : State}
    (hwf : st.WF) (hpa : st.pileOfTop c = some a)
    (hchop : chop (st.piles a).faceUp ≠ [])
    (hshape : s₁ = { st.setFound c.suit (st.found c.suit ++ [c]) with
        piles := fun a' => if a' = a then
          Pile.afterRunRemoved (st.piles a) (chop (st.piles a).faceUp) else st.piles a' })
    (hwf₁ : s₁.WF) :
    ∃ z, lastOf (chop (st.piles a).faceUp) = some z ∧ canSitOn c z = true ∧
      s₁.pileOfTop z = some a := by
  obtain ⟨z, hz⟩ := lastOf_exists hchop
  have hfull : (st.piles a).faceUp = chop (st.piles a).faceUp ++ [c] :=
    lastOf_chop (pileOfTop_top hpa).2
  have hrunok : runOK (chop (st.piles a).faceUp ++ [c]) = true := by
    rw [← hfull]
    exact hwf.2.1 a
  obtain ⟨z', hz', hsit⟩ := runOK_snoc_sit hchop hrunok
  have hzz : z = z' := Option.some.inj (hz.symm.trans hz')
  subst hzz
  have hseat : s₁.piles a = { st.piles a with faceUp := chop (st.piles a).faceUp } :=
    lift_seatZone_eq hshape (Or.inl hchop)
  have hzt : (s₁.piles a).top = some z := by
    show lastOf (s₁.piles a).faceUp = some z
    rw [hseat]
    exact hz
  exact ⟨z, hz, hsit, (pileOfTop_eq_some_iff hwf₁).2 hzt⟩

/-- **The licensed lift is `reversibleAtW` at `WF`** — the landed undo
family, premises discharged by the license and `WF`: the under-seat
raise through `tabToFound_undo_under`, the bare-king raise through
`tabToFound_undo_bare` (the license's shape disjunction forces the
bare branch exactly when the chop is empty). -/
theorem liftStep_reversibleW {st : State} {c : Card} {s₁ : State}
    (hwf : st.WF) (hc : CanRaise st c)
    (hstep : State.step st (Move.tabToFound c) = some s₁) :
    reversibleAtW st (Move.tabToFound c) := by
  have hwf₁ : s₁.WF := lift_wf hwf hc hstep
  obtain ⟨-, a, hp, hbr⟩ := hc
  obtain ⟨-, a', hp', hshape⟩ := step_tabToFound_inv hstep
  rw [hp] at hp'
  injection hp' with haa
  subst haa
  have hstep' : State.step st (Move.tabToFound c) = some s₁ := hstep
  have hshape' : s₁ = { st.setFound c.suit (st.found c.suit ++ [c]) with
      piles := fun a₂ => if a₂ = a then
        Pile.afterRunRemoved (st.piles a) (chop (st.piles a).faceUp) else st.piles a₂ } :=
    hshape
  cases hch : chop (st.piles a).faceUp with
  | cons y ys =>
      have hchop : chop (st.piles a).faceUp ≠ [] := by
        intro hcne
        rw [hcne] at hch
        exact absurd hch (by simp)
      obtain ⟨z, hz, hsit, hsearch⟩ :=
        lift_under_facts hwf hp hchop hshape' hwf₁
      exact tabToFound_undo_under hstep' hp hz hsit hsearch
  | nil =>
      rcases hbr with hne | ⟨hhid, hking⟩
      · exact absurd hch hne
      · exact tabToFound_undo_bare hstep' hp hch hhid hking

/-- **The licensed lift's undo, as data**: exactly one `foundToTab`
move — the local mirror equations above — fires back to the origin,
and carries its own one-move return (the very raise).  This is the
reverse undo-ladder's leg. -/
theorem lift_undoW {st : State} {c : Card} {s₁ : State}
    (hwf : st.WF) (hc : CanRaise st c)
    (hstep : State.step st (Move.tabToFound c) = some s₁) :
    ∃ m : Move, State.step s₁ m = some st ∧ reversibleAtW s₁ m := by
  have hwf₁ : s₁.WF := lift_wf hwf hc hstep
  obtain ⟨-, a, hp, hbr⟩ := hc
  obtain ⟨-, a', hp', hshape⟩ := step_tabToFound_inv hstep
  rw [hp] at hp'
  injection hp' with haa
  subst haa
  have hstep' : State.step st (Move.tabToFound c) = some s₁ := hstep
  have hshape' : s₁ = { st.setFound c.suit (st.found c.suit ++ [c]) with
      piles := fun a₂ => if a₂ = a then
        Pile.afterRunRemoved (st.piles a) (chop (st.piles a).faceUp) else st.piles a₂ } :=
    hshape
  cases hch : chop (st.piles a).faceUp with
  | cons y ys =>
      have hchop : chop (st.piles a).faceUp ≠ [] := by
        intro hcne
        rw [hcne] at hch
        exact absurd hch (by simp)
      obtain ⟨z, hz, hsit, hsearch⟩ :=
        lift_under_facts hwf hp hchop hshape' hwf₁
      refine ⟨Move.foundToTab c (Sum.inr z),
        raise_undo_under_step hstep' hp hz hsit hsearch, ?_⟩
      exact ⟨st, [Move.tabToFound c], raise_undo_under_step hstep' hp hz hsit hsearch,
        run_one hstep'⟩
  | nil =>
      rcases hbr with hne | ⟨hhid, hking⟩
      · exact absurd hch hne
      · refine ⟨Move.foundToTab c (Sum.inl a),
          raise_undo_bare_step hstep' hp hch hhid hking, ?_⟩
        exact ⟨st, [Move.tabToFound c], raise_undo_bare_step hstep' hp hch hhid hking,
          run_one hstep'⟩

/-! ## The canonical ladder: witness shuffles both ways -/

/-- **The forward ladder**: every licensed run is a witness shuffle
over its very schedule — each raise's `reversibleAtW` is the landed
undo family (through `liftStep_reversibleW`), and the `WF` rides down
the run inductively (the licensed lift preserves it). -/
theorem stackRun_reversibleW {st : State} (hwf : st.WF) {l : List Move} {w : State}
    (h : StackRun st l w) : ShufflePlayW st l w := by
  induction h with
  | nil s => exact .nil s
  | @cons st₀ m c s' rest w₀ hc hm hstep hrest ih =>
      cases hm
      exact .cons (liftStep_reversibleW hwf hc hstep) hstep
        (ih (lift_wf hwf hc hstep))

/-- **The reverse undo-ladder**: from any licensed run's end there is
a witness shuffle back to the origin — the undo moves fire in reverse
order (each at the exact state right after its raise), and each undo
carries the raise itself as its one-move return. -/
theorem stackRun_returnW {st : State} (hwf : st.WF) {l : List Move} {w : State}
    (h : StackRun st l w) : ∃ τ : List Move, ShufflePlayW w τ st := by
  induction h with
  | nil s => exact ⟨[], .nil s⟩
  | @cons st₀ m c s' rest w₀ hc hm hstep hrest ih =>
      cases hm
      obtain ⟨m', hback, hrev'⟩ := lift_undoW hwf hc hstep
      obtain ⟨τ₁, hτ₁⟩ := ih (lift_wf hwf hc hstep)
      exact ⟨τ₁ ++ [m'], ShufflePlayW_append hτ₁
        (ShufflePlayW.cons hrev' hback (.nil st₀))⟩

/-! ## §3.0's centerpiece: the canonical form inside its own macro class -/

/-- **`canon_reversibleW`**: the canonical schedule is a witness
shuffle from `u` to `canon u`. -/
theorem canon_reversibleW {u : State} (hwf : u.WF) :
    ∃ l : List Move, ShufflePlayW u l (canon u) := by
  obtain ⟨l, hrun, -⟩ := canon_run u
  exact ⟨l, stackRun_reversibleW hwf hrun⟩

/-- **`canon_class`**: the canonical form sits inside the position's
own witness reversible orbit — same macro state, literally. -/
theorem canon_class {u : State} (hwf : u.WF) : RevEqW u (canon u) := by
  obtain ⟨l, hrun, -⟩ := canon_run u
  exact ⟨l, stackRun_reversibleW hwf hrun, stackRun_returnW hwf hrun⟩

/-- **`canon_in_class`** (§3.0's centerpiece): the stack-run to the
canonical form is a `ShufflePlayW` — each licensed raise is
`reversibleAtW` through the landed undo family, the reverse
undo-ladder composes the return — so `⟦canon u⟧ = ⟦u⟧`: the
canonical form is a DISTINGUISHED MEMBER of its macro class, not a
commit-shifted descendant. -/
theorem canon_in_class {u : State} (hwf : u.WF) : ⟦canon u⟧ = ⟦u⟧ :=
  Quotient.sound (Or.inr (Or.inr (Or.inl (canon_class hwf))) :
    sameOrbitSetoid.r (canon u) u)

/-- **The uniform fiber spine**: `WF` positions in one
`sameOrbitSetoid` orbit have equal wrapped canons — "whatever proves
two positions ⟦·⟧-equal proves their canons ⟦·⟧-equal", the argument
shape the whole §3.0 invariance family lands through. -/
theorem canonQ_of_orbit {u v : State} (huwf : u.WF) (hvwf : v.WF)
    (h : sameOrbitSetoid.r u v) : ⟦canon u⟧ = ⟦canon v⟧ := by
  rw [show ⟦canon u⟧ = ⟦u⟧ from canon_in_class huwf,
      show ⟦canon v⟧ = ⟦v⟧ from canon_in_class hvwf]
  exact Quotient.sound h

/-! ## The twin conjugation

The canonicalizer is defined on cards; the twin relabeling
(`Orig.Twin`) maps cards to cards and conjugates step for step
(`State.twin_step`), so it carries the whole stacking system with it:
the license, the runs, the terminator, and — the structural
conjugation the §3.0 family claims — the canonicalizer itself:
`canon (twinMap u) = twinMap (canon u)`.  The `WF` bookkeeping
(foundation prefixes, run legality, the census, the draw step) twins
wholesale. -/

/-- `take` commutes with a pointwise map (the map-twinned prefix is
the prefix of the twinned list). -/
private theorem take_map_comm (f : Card → Card) : ∀ (n : Nat) (l : List Card),
    (l.take n).map f = (l.map f).take n := by
  intro n
  induction n with
  | zero =>
      intro l
      cases l with
      | nil => rfl
      | cons x t => rfl
  | succ n ih =>
      intro l
      cases l with
      | nil => rfl
      | cons x t =>
          show (f x :: (t.take n).map f) = f x :: (t.map f).take n
          rw [ih]

/-- A suit's build order, twinned, is the twin suit's build order. -/
private theorem upCards_twin (s : Suit) :
    (s.upCards).map Card.twin = (s.twin).upCards := by
  cases s <;> rfl

/-- A pile's twin-map: hidden and face-up rows twin elementwise. -/
private theorem pileZone_twinMap (st : State) (a : Anchor) :
    ((st.piles a).twinMap).hidden ++ ((st.piles a).twinMap).faceUp =
      (pileZone st a).map Card.twin := by
  show (st.piles a).hidden.map Card.twin ++ (st.piles a).faceUp.map Card.twin =
    ((st.piles a).hidden ++ (st.piles a).faceUp).map Card.twin
  rw [List.map_append]

/-- Filtered counts transfer across the twin relabeling: counting `c`
in a twinned list is counting `c.twin` in the original, re-twinned. -/
private theorem filter_map_twin (c : Card) : ∀ (l : List Card),
    (l.map Card.twin).filter (fun y => decide (y = c)) =
      (l.filter (fun y => decide (y = c.twin))).map Card.twin := by
  intro l
  induction l with
  | nil => rfl
  | cons x t ih =>
      have hdec : decide (x.twin = c) = decide (x = c.twin) := by
        have h := decide_twin_eq (c := x) (z := c.twin)
        rwa [Card.twin_twin c] at h
      show List.filter (fun y => decide (y = c)) (x.twin :: t.map Card.twin) =
        List.map Card.twin (List.filter (fun y => decide (y = c.twin)) (x :: t))
      simp only [List.filter_cons]
      rw [hdec]
      cases hd : decide (x = c.twin) with
      | true =>
          show x.twin :: List.filter (fun y => decide (y = c)) (t.map Card.twin) =
            List.map Card.twin (x :: List.filter (fun y => decide (y = c.twin)) t)
          rw [ih, List.map_cons]
      | false =>
          show List.filter (fun y => decide (y = c)) (t.map Card.twin) =
            List.map Card.twin (List.filter (fun y => decide (y = c.twin)) t)
          exact ih

/-- The suit block, twinned, is the suit block, permuted: the twin map
is an involution, so summing a per-suit measure over `s.twin` is
summing it over `s`. -/
private theorem sum_twin_perm (g : Suit → Nat) :
    (Suit.all.map (fun s => g s.twin)).sum = (Suit.all.map g).sum := by
  have hL : (Suit.all.map (fun s => g s.twin)) =
      [g .club, g .diamond, g .heart, g .spade] := rfl
  have hR : (Suit.all.map g) = [g .spade, g .heart, g .diamond, g .club] := rfl
  rw [hL, hR]
  simp only [List.sum_cons, List.sum_nil]
  omega

/-- **The zone census twins**: counting `c` across the twinned
position is counting `c.twin` across the original.  The pile blocks
and the draw tail twin in place; the found blocks sit in twin-suited
order, so the per-suit filtered lengths pass through the suit
permutation sum. -/
theorem cardCount_twinMap (st : State) (c : Card) :
    (State.twinMap st).cardCount c = st.cardCount c.twin := by
  have hz (z : List Card) :
      ((z.map Card.twin).filter (fun y => decide (y = c))).length =
        (z.filter (fun y => decide (y = c.twin))).length := by
    rw [filter_map_twin, List.length_map]
  have hS : zoneCount (Suit.all.map (fun s => (st.found s.twin).map Card.twin)) c =
      zoneCount (Suit.all.map st.found) c.twin := by
    rw [zoneCount_coll, zoneCount_coll]
    rw [show List.map (fun z => (List.filter (fun y => decide (y = c)) z).length)
          (List.map (fun s => List.map Card.twin (st.found s.twin)) Suit.all) =
        List.map (fun s => (List.filter (fun y => decide (y = c))
          (List.map Card.twin (st.found s.twin))).length) Suit.all from by
        rw [List.map_map]
        rfl]
    rw [map_congr_eq (fun (s : Suit) _ => hz (st.found s.twin))]
    exact sum_twin_perm (fun τ =>
      ((st.found τ).filter (fun y => decide (y = c.twin))).length)
  have hP : zoneCount (Anchor.all.map (fun a =>
        ((st.piles a).twinMap).hidden ++ ((st.piles a).twinMap).faceUp)) c =
      zoneCount (Anchor.all.map (fun a => pileZone st a)) c.twin := by
    have hmapmap {α : Type} (p : Card) (l : List α) (f : α → List Card) :
        List.map (fun z => (List.filter (fun y => decide (y = p)) z).length)
            (List.map f l) =
          List.map (fun x => (List.filter (fun y => decide (y = p)) (f x)).length) l := by
      induction l with
      | nil => rfl
      | cons x t ih =>
          show (List.filter (fun y => decide (y = p)) (f x)).length ::
              List.map (fun z => (List.filter (fun y => decide (y = p)) z).length)
                (List.map f t) =
            (List.filter (fun y => decide (y = p)) (f x)).length ::
              List.map (fun x' =>
                (List.filter (fun y => decide (y = p)) (f x')).length) t
          rw [ih]
    rw [zoneCount_coll, zoneCount_coll, hmapmap c Anchor.all _, hmapmap c.twin Anchor.all _]
    have hpz : ∀ (a : Anchor),
        (List.filter (fun y => decide (y = c))
          (((st.piles a).twinMap).hidden ++ ((st.piles a).twinMap).faceUp)).length =
        (List.filter (fun y => decide (y = c.twin)) (pileZone st a)).length := by
      intro a
      rw [pileZone_twinMap st a]
      exact hz (pileZone st a)
    rw [map_congr_eq (fun (a : Anchor) _ => hpz a)]
  have hT : zoneCount [st.stock.map Card.twin, st.waste.map Card.twin] c =
      zoneCount [st.stock, st.waste] c.twin := by
    have flat2 : ∀ (A B : List Card),
        List.flatMap id [A, B] = A ++ B := by
      intro A B
      show A ++ List.flatMap id [B] = A ++ B
      rw [show List.flatMap id [B] =
          B ++ List.flatMap id ([] : List (List Card)) from rfl,
        show List.flatMap id ([] : List (List Card)) = ([] : List Card) from rfl,
        List.append_nil]
    rw [zoneCount, zoneCount,
      flat2 (st.stock.map Card.twin) (st.waste.map Card.twin),
      flat2 st.stock st.waste]
    show ((st.stock.map Card.twin ++ st.waste.map Card.twin).filter
        (fun y => decide (y = c))).length =
      ((st.stock ++ st.waste).filter (fun y => decide (y = c.twin))).length
    rw [List.filter_append, List.length_append, List.filter_append,
      List.length_append]
    rw [hz st.stock, hz st.waste]
  have hL : (State.twinMap st).cardCount c =
      zoneCount (Suit.all.map (fun s => (st.found s.twin).map Card.twin) ++
        Anchor.all.map (fun a =>
          ((st.piles a).twinMap).hidden ++ ((st.piles a).twinMap).faceUp) ++
        [st.stock.map Card.twin, st.waste.map Card.twin]) c := rfl
  have hR : st.cardCount c.twin =
      zoneCount (Suit.all.map st.found ++
        Anchor.all.map (fun a => (st.piles a).hidden ++ (st.piles a).faceUp) ++
        [st.stock, st.waste]) c.twin := rfl
  rw [hL, hR, zoneCount_split, zoneCount_split, zoneCount_split,
    zoneCount_split, hS, hP, hT]
  rfl

/-- **The twin relabeling preserves `WF`**: foundation prefixes twin
into the twin suit's build order, run legality survives the
elementwise relabeling (`canSitOn` is twin-blind), the census twins
(`cardCount_twinMap`), and the draw step is untouched. -/
theorem twin_wf {st : State} (hwf : st.WF) : (State.twinMap st).WF := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s
    obtain ⟨n, hn⟩ := hwf.1 s.twin
    refine ⟨n, ?_⟩
    show (st.found s.twin).map Card.twin = s.upCards.take n
    rw [hn, take_map_comm, upCards_twin]
    cases s <;> simp [Suit.twin_twin]
  · intro a
    show runOK (((st.piles a).twinMap).faceUp) = true
    have h : ((st.piles a).twinMap).faceUp = ((st.piles a).faceUp).map Card.twin := rfl
    rw [h]
    have hrun : ∀ l : List Card, runOK (l.map Card.twin) = runOK l := by
      intro l
      induction l with
      | nil => rfl
      | cons x t ih =>
          cases t with
          | nil => rfl
          | cons y t' =>
              show (canSitOn y.twin x.twin && runOK (y.twin :: List.map Card.twin t')) =
                (canSitOn y x && runOK (y :: t'))
              rw [canSitOn_twin_twin, ← List.map_cons, ih]
    rw [hrun]
    exact hwf.2.1 a
  · intro c _
    rw [cardCount_twinMap]
    exact hwf.2.2.1 c.twin (Card.mem_universe c.twin)
  · exact hwf.2.2.2

/-- The license is twin-blind: `canRaiseB` at the twinned position
reads the same answer for the twinned card. -/
theorem canRaiseB_twinMap (st : State) (c : Card) :
    canRaiseB (State.twinMap st) c.twin = canRaiseB st c := by
  have hchop : ∀ (l : List Card), chop (l.map Card.twin) = (chop l).map Card.twin := by
    intro l
    induction l with
    | nil => rfl
    | cons x t ih =>
        cases t with
        | nil => rfl
        | cons y t' =>
            simp only [chop, List.map_cons]
            show x.twin :: chop (List.map Card.twin (y :: t')) =
              x.twin :: List.map Card.twin (chop (y :: t'))
            rw [ih]
  have hne : ∀ (l : List Card), decide (l.map Card.twin ≠ []) = decide (l ≠ []) := by
    intro l
    cases l with
    | nil => rfl
    | cons x t =>
        rw [decide_eq_true (show ((x :: t).map Card.twin ≠ []) from by simp),
            decide_eq_true (show ((x :: t) ≠ []) from by simp)]
  have hnil : ∀ (l : List Card), decide (l.map Card.twin = []) = decide (l = []) := by
    intro l
    cases l with
    | nil => rfl
    | cons x t =>
        rw [decide_eq_false (show ¬ (((x :: t).map Card.twin) = []) from by simp),
            decide_eq_false (show ¬ ((x :: t) = []) from by simp)]
  unfold canRaiseB
  rw [State.nextUp_twinMap, State.pileOfTop_twinMap]
  cases hp : st.pileOfTop c with
  | none => rfl
  | some a =>
      simp only [show ((State.twinMap st).piles a).faceUp =
          (st.piles a).faceUp.map Card.twin from rfl,
        show ((State.twinMap st).piles a).hidden =
          (st.piles a).hidden.map Card.twin from rfl,
        hchop, hne, hnil, Card.twin_rank]
      rfl

/-- The license is twin-blind, relation form. -/
theorem canRaise_twinMap_iff {st : State} {c : Card} :
    CanRaise (State.twinMap st) c.twin ↔ CanRaise st c := by
  rw [← canRaiseB_true_iff, ← canRaiseB_true_iff, canRaiseB_twinMap]

/-- `Final` is twin-blind. -/
theorem final_twinMap {w : State} (hfin : Final w) :
    Final (State.twinMap w) := by
  intro c hcr
  have hiff : CanRaise (State.twinMap w) (c.twin.twin) ↔ CanRaise w c.twin :=
    canRaise_twinMap_iff (st := w) (c := c.twin)
  rw [Card.twin_twin c] at hiff
  exact hfin c.twin (hiff.mp hcr)

/-- The whole stacking run twins: move for move, license for license. -/
theorem stackRun_twinMap {u : State} {l : List Move} {w : State}
    (h : StackRun u l w) :
    StackRun (State.twinMap u) (l.map Move.twinMove) (State.twinMap w) := by
  induction h with
  | nil s => exact .nil _
  | @cons st₀ m c s' rest w₀ hc hm hstep hrest ih =>
      cases hm
      have hstept : State.step (State.twinMap st₀) (Move.tabToFound c.twin) =
          some (State.twinMap s') := by
        have h2 := State.twin_step st₀ (Move.tabToFound c)
        rw [hstep] at h2
        exact h2.symm
      exact .cons (canRaise_twinMap_iff.2 hc) (IsRaise.tabToFound c.twin) hstept ih

/-- **`canon_twinMap`** — the structural conjugation: the
canonicalizer of the twin position is the twin of the canonical
position.  Route: the twinned canonical schedule is a maximal
licensed run at the (WF) twinned position ending `Final`, so
`canon_unique` pins it to the twinned position's own canonical
form. -/
theorem canon_twinMap {u : State} (hwf : u.WF) :
    canon (State.twinMap u) = State.twinMap (canon u) := by
  obtain ⟨l, hrun, hfin⟩ := canon_run u
  have hwft : (State.twinMap u).WF := twin_wf hwf
  obtain ⟨l₂, hrun₂, hfin₂⟩ := canon_run (State.twinMap u)
  have h1 := canon_unique hwft (stackRun_twinMap hrun) (final_twinMap hfin) hrun₂ hfin₂
  exact h1.symm

/-- **Twin conjugation lands inside the canon fiber**: the canonical
form of the twin position class-matches the canonical form (the
conjugation `canon_twinMap` plus the setoid's own twin disjunct). -/
theorem sameMacro_twin {u : State} (hwf : u.WF) :
    ⟦canon u⟧ = ⟦canon (State.twinMap u)⟧ := by
  rw [canon_twinMap hwf]
  exact Quotient.sound (show sameOrbitSetoid.r (canon u) (State.twinMap (canon u)) from
    Or.inr (Or.inl rfl))
