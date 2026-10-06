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





