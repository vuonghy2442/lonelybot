import Klondike.Basic

/-!
# The tableau as a partial bijection (the matching)

`Base = Anchor ⊕ Card` — what a card can sit on.  The board stores
`topOf` (what sits on each base) with the single matching law `inj`;
the inverse `bottomOf` is derived by search over the (complete) base
enumeration.  One field, one law, the other direction free.

The matching stores only the *visible* edges: hidden-pile edges are
derived from the deal (see `Klondike.State`), foundation edges from
the heights.
-/

/-- The seven tableau pile anchors: a base position at the bottom of
each pile. -/
inductive Anchor : Type where
  | p0 | p1 | p2 | p3 | p4 | p5 | p6
  deriving DecidableEq, Repr

/-- All anchors. -/
def Anchor.all : List Anchor := [.p0, .p1, .p2, .p3, .p4, .p5, .p6]

theorem Anchor.mem_all (a : Anchor) : a ∈ Anchor.all := by cases a <;> simp [Anchor.all]

/-- Numeric view (pile index). -/
def Anchor.toIdx : Anchor → Nat
  | .p0 => 0 | .p1 => 1 | .p2 => 2 | .p3 => 3 | .p4 => 4 | .p5 => 5 | .p6 => 6

/-- What a card can sit on: a pile anchor, or another card. -/
abbrev Base := Sum Anchor Card

/-- Twin-swap on bases. -/
def Base.flipBase : Base → Base := Sum.map id Card.flipSuit

theorem Base.flipBase_flipBase (b : Base) : b.flipBase.flipBase = b := by
  cases b <;> simp [Base.flipBase, Card.flipSuit_flipSuit]

/-- Local twin swap on bases (Klondike/TwinSwap.lean's substrate). -/
def Base.swapTwin (c : Card) : Base → Base := Sum.map id (Card.swapTwin c)

@[simp] theorem Base.swapTwin_swapTwin (c : Card) (b : Base) :
    (b.swapTwin c).swapTwin c = b := by
  cases b <;> simp [Base.swapTwin]

/-- The first element of `l` satisfying `p`. -/
def findFirst {α : Type} (p : α → Bool) : List α → Option α
  | [] => none
  | a :: t => if p a then some a else findFirst p t

@[simp] theorem findFirst_nil {α : Type} (p : α → Bool) : findFirst p [] = none := rfl

@[simp] theorem findFirst_cons {α : Type} (p : α → Bool) (a : α) (t : List α) :
    findFirst p (a :: t) = if p a then some a else findFirst p t := rfl

theorem findFirst_mem {α : Type} (p : α → Bool) :
    ∀ (l : List α) (a : α), findFirst p l = some a → a ∈ l ∧ p a = true
  | [], _, h => by simp at h
  | b :: t, a, h => by
      by_cases hb : p b = true
      · rw [findFirst_cons, if_pos hb, Option.some.injEq] at h
        subst h
        exact ⟨by simp, hb⟩
      · rw [findFirst_cons, if_neg hb] at h
        obtain ⟨hm, hp⟩ := findFirst_mem p t a h
        exact ⟨by simp [hm], hp⟩

theorem findFirst_of_unique {α : Type} (p : α → Bool) :
    ∀ (l : List α) (a : α), a ∈ l → p a = true → (∀ b ∈ l, p b = true → b = a) →
      findFirst p l = some a
  | [], _, h, _, _ => by simp at h
  | b :: t, a, hm, hp, hu => by
      rw [findFirst_cons]
      by_cases hb : p b = true
      · rw [if_pos hb, hu b (by simp) hb]
      · rw [if_neg hb]
        simp only [List.mem_cons] at hm
        refine findFirst_of_unique p t a ?_ hp ?_
        · rcases hm with h | h
          · subst h
            exact absurd hp hb
          · exact h
        · exact fun b' hb' hpb' => hu b' (by simp [hb']) hpb'

theorem findFirst_eq_none {α : Type} (p : α → Bool) :
    ∀ (l : List α), (∀ a ∈ l, p a ≠ true) → findFirst p l = none
  | [], _ => rfl
  | b :: t, h => by
      rw [findFirst_cons, if_neg (h b (by simp))]
      exact findFirst_eq_none p t (fun a ha => h a (by simp [ha]))

/-- `findFirst` finds: if some member satisfies `p`, the search is not
`none` (the missing converse half of `findFirst_eq_none`).  RELOCATED
2026-09-13 from Dominance.lean — `vis_base_of_notLocked` (Theorems)
needs it upstream of the B4 crux. -/
theorem findFirst_ne_none_of_mem {α : Type} (p : α → Bool) :
    ∀ (l : List α) (a : α), a ∈ l → p a = true → findFirst p l ≠ none := by
  intro l
  induction l with
  | nil => intro a ha; exact absurd ha (by simp)
  | cons b t ih =>
      intro a ha hp
      simp only [findFirst_cons]
      by_cases hb : p b = true
      · rw [if_pos hb]; simp
      · rw [if_neg hb]
        simp only [List.mem_cons] at ha
        rcases ha with h | h
        · rw [h] at hp; exact absurd hp hb
        · exact ih a h hp

/-- The tableau board: a partial bijation read through `topOf` — for
each base, the card sitting on it.  The single law `inj` makes it a
matching: at most one card per base, hence `topOf` injective on its
support. -/
structure Board where
  /-- What sits on each base (`none` = empty base). -/
  topOf : Base → Option Card
  /-- The matching law: a card sits on at most one base. -/
  inj : ∀ b₁ b₂ c, topOf b₁ = some c → topOf b₂ = some c → b₁ = b₂

namespace Board

/-- Every base, for the derived search. -/
def enumBase : List Base := Anchor.all.map Sum.inl ++ Card.universe.map Sum.inr

theorem enumBase_complete (b : Base) : b ∈ enumBase := by
  cases b with
  | inl a =>
      simp only [enumBase, List.mem_append, List.mem_map]
      exact Or.inl ⟨a, a.mem_all, rfl⟩
  | inr c =>
      simp only [enumBase, List.mem_append, List.mem_map]
      exact Or.inr ⟨c, c.mem_universe, rfl⟩

/-- The derived inverse: the base under `c`, by search. -/
def bottomOf (bd : Board) (c : Card) : Option Base :=
  findFirst (fun b => decide (bd.topOf b = some c)) enumBase

theorem bottomOf_eq (bd : Board) (c : Card) (b : Base) :
    bd.bottomOf c = some b ↔ bd.topOf b = some c := by
  constructor
  · intro h
    exact of_decide_eq_true (findFirst_mem _ _ _ h).2
  · intro h
    exact findFirst_of_unique _ _ b (enumBase_complete b) (decide_eq_true h)
      (fun b' _ hp' => bd.inj b' b c (of_decide_eq_true hp') h)

theorem bottomOf_eq_none (bd : Board) (c : Card) :
    bd.bottomOf c = none ↔ ∀ b, bd.topOf b ≠ some c := by
  constructor
  · intro h b hb
    have h2 := (bottomOf_eq bd c b).mpr hb
    rw [h] at h2
    simp at h2
  · intro h
    exact findFirst_eq_none _ _ (fun a _ hp => absurd (of_decide_eq_true hp) (h a))

/-- The empty board. -/
def empty : Board where
  topOf := fun _ => none
  inj := by intro b₁ b₂ c h₁ _; simp at h₁

@[simp] theorem empty_topOf (b : Base) : Board.empty.topOf b = none := rfl

@[simp] theorem empty_bottomOf (c : Card) : Board.empty.bottomOf c = none := by
  refine findFirst_eq_none _ _ (fun a _ hp => ?_)
  simp at hp

/-- Pointwise update at a base. -/
def update (f : Base → Option Card) (b : Base) (o : Option Card) : Base → Option Card :=
  fun b' => if b' = b then o else f b'

theorem update_self (f : Base → Option Card) (b : Base) (o : Option Card) :
    update f b o b = o := by simp [update]

theorem update_ne (f : Base → Option Card) (b b' : Base) (o : Option Card) (h : b' ≠ b) :
    update f b o b' = f b' := by simp [update, h]

/-- Detach whatever sits at `b`. -/
def detach (bd : Board) (b : Base) : Board where
  topOf := update bd.topOf b none
  inj := by
    intro b₁ b₂ c h₁ h₂
    by_cases hb₁ : b₁ = b
    · subst hb₁
      rw [update_self] at h₁
      simp at h₁
    · rw [update_ne _ _ _ _ hb₁] at h₁
      by_cases hb₂ : b₂ = b
      · subst hb₂
        rw [update_self] at h₂
        simp at h₂
      · rw [update_ne _ _ _ _ hb₂] at h₂
        exact bd.inj b₁ b₂ c h₁ h₂

@[simp] theorem detach_topOf (bd : Board) (b : Base) : (bd.detach b).topOf b = none := by
  simp [Board.detach, update_self]

@[simp] theorem detach_topOf_ne (bd : Board) (b b' : Base) (h : b' ≠ b) :
    (bd.detach b).topOf b' = bd.topOf b' := by
  simp [Board.detach, update_ne, h]

/-- After detaching at `b`: the detached card itself is no longer
seated (the `bottomOf_detach_ne` sibling, Move.lean).  Re-proved
upstream 2026-09-13 from Bridge.lean (Theorems cannot cite Bridge);
Bridge's root-level original stays — dedupe is a later wave's choice. -/
theorem bottomOf_detach_self {bd : Board} {b : Base} {c : Card}
    (hbot : bd.topOf b = some c) : (bd.detach b).bottomOf c = none := by
  refine (Board.bottomOf_eq_none _ c).mpr (fun b' hb' => ?_)
  by_cases hbb : b' = b
  · subst hbb
    rw [Board.detach_topOf] at hb'
    simp at hb'
  · rw [Board.detach_topOf_ne _ _ _ hbb] at hb'
    exact hbb (bd.inj b' b c hb' hbot)

theorem attach_inj (bd : Board) (b : Base) (c : Card) (hnew : bd.bottomOf c = none) :
    ∀ (b₁ b₂ : Base) (c' : Card), update bd.topOf b (some c) b₁ = some c' →
      update bd.topOf b (some c) b₂ = some c' → b₁ = b₂ := by
  intro b₁ b₂ c' h₁ h₂
  by_cases hb₁ : b₁ = b
  · by_cases hb₂ : b₂ = b
    · exact hb₁.trans hb₂.symm
    · subst hb₁
      rw [update_self] at h₁
      rw [update_ne _ _ _ _ hb₂] at h₂
      rw [Option.some.injEq] at h₁
      rw [← h₁] at h₂
      have hbot := (bottomOf_eq bd c b₂).mpr h₂
      rw [hnew] at hbot
      simp at hbot
  · rw [update_ne _ _ _ _ hb₁] at h₁
    by_cases hb₂ : b₂ = b
    · subst hb₂
      rw [update_self] at h₂
      rw [Option.some.injEq] at h₂
      rw [← h₂] at h₁
      have hbot := (bottomOf_eq bd c b₁).mpr h₁
      rw [hnew] at hbot
      simp at hbot
    · rw [update_ne _ _ _ _ hb₂] at h₂
      exact bd.inj b₁ b₂ c' h₁ h₂

/-- Attach `c` at `b` — total, guarded (fails unless `b` is free and
`c` is unplaced). -/
def attach (bd : Board) (b : Base) (c : Card) : Option Board :=
  if _hfree : bd.topOf b = none then
    if hnew : bd.bottomOf c = none then
      some { topOf := update bd.topOf b (some c), inj := attach_inj bd b c hnew }
    else none
  else none

theorem attach_topOf (bd : Board) (b : Base) (c : Card) {bd' : Board}
    (h : bd.attach b c = some bd') : bd'.topOf b = some c := by
  unfold attach at h
  split at h
  · split at h
    · rw [Option.some.injEq] at h
      subst h
      exact update_self bd.topOf b (some c)
    · simp at h
  · simp at h

theorem attach_topOf_ne (bd : Board) (b : Base) (c : Card) {bd' : Board}
    (h : bd.attach b c = some bd') (hne : b' ≠ b) : bd'.topOf b' = bd.topOf b' := by
  unfold attach at h
  split at h
  · split at h
    · rw [Option.some.injEq] at h
      subst h
      exact update_ne bd.topOf b b' (some c) hne
    · simp at h
  · simp at h

theorem attach_eq_some_iff (bd : Board) (b : Base) (c : Card) :
    bd.attach b c ≠ none ↔ bd.topOf b = none ∧ bd.bottomOf c = none := by
  constructor
  · intro h
    unfold attach at h
    split at h
    · split at h
      · constructor <;> assumption
      · simp at h
    · simp at h
  · intro h
    unfold attach
    rw [dif_pos h.1, dif_pos h.2]
    simp

/-- Boards with the same `topOf` are equal (the `inj` law is a proof
field — proof irrelevance). -/
theorem ext_topOf {bd₁ bd₂ : Board} (h : bd₁.topOf = bd₂.topOf) : bd₁ = bd₂ := by
  cases bd₁ with
  | mk t₁ i₁ =>
    cases bd₂ with
    | mk t₂ i₂ =>
      cases h
      rfl

/-- Two attachments at distinct bases commute.  CANONICAL HOME
(2026-09-13 consolidation): Move.lean's `Board.attach_attach_comm`
and Commutation.lean's root-level `attach_attach_comm` are deleted. -/
theorem attach_attach_comm {bd : Board} {b b' : Base} {c c' : Card}
    {bd₁ bd₂ bd₃ bd₄ : Board} (hbb : b ≠ b')
    (h₁ : bd.attach b c = some bd₁) (h₂ : bd₁.attach b' c' = some bd₂)
    (h₃ : bd.attach b' c' = some bd₃) (h₄ : bd₃.attach b c = some bd₄) :
    bd₂ = bd₄ := by
  refine Board.ext_topOf (funext (fun x => ?_))
  by_cases hxb : x = b
  · rw [hxb, Board.attach_topOf_ne _ _ _ h₂ hbb, Board.attach_topOf _ _ _ h₁,
      Board.attach_topOf _ _ _ h₄]
  · by_cases hxb' : x = b'
    · rw [hxb', Board.attach_topOf _ _ _ h₂, Board.attach_topOf_ne _ _ _ h₄ (Ne.symm hbb),
        Board.attach_topOf _ _ _ h₃]
    · rw [Board.attach_topOf_ne _ _ _ h₂ hxb', Board.attach_topOf_ne _ _ _ h₁ hxb,
        Board.attach_topOf_ne _ _ _ h₄ hxb, Board.attach_topOf_ne _ _ _ h₃ hxb']

theorem mapBy_inj (bd : Board) :
    ∀ (b₁ b₂ : Base) (c : Card), (bd.topOf b₁.flipBase).map Card.flipSuit = some c →
      (bd.topOf b₂.flipBase).map Card.flipSuit = some c → b₁ = b₂ := by
  intro b₁ b₂ c h₁ h₂
  obtain ⟨d₁, hd₁, hd₁'⟩ := Option.map_eq_some_iff.mp h₁
  obtain ⟨d₂, hd₂, hd₂'⟩ := Option.map_eq_some_iff.mp h₂
  have hd : d₁ = d₂ := by
    have h := congrArg Card.flipSuit (hd₁'.trans hd₂'.symm)
    rw [Card.flipSuit_flipSuit, Card.flipSuit_flipSuit] at h
    exact h
  rw [← hd] at hd₂
  have hb : b₁.flipBase = b₂.flipBase := bd.inj _ _ _ hd₁ hd₂
  have hb2 := congrArg Base.flipBase hb
  rw [Base.flipBase_flipBase, Base.flipBase_flipBase] at hb2
  exact hb2

/-- Conjugate the board by the twin-swap relabeling (T's action). -/
def mapBy (bd : Board) : Board where
  topOf := fun b => (bd.topOf b.flipBase).map Card.flipSuit
  inj := mapBy_inj bd

/-- Injectivity proof for the local-swap conjugation (mirrors
`mapBy_inj` — involution + `bd.inj` only). -/
theorem mapByTwin_inj (bd : Board) (t : Card) :
    ∀ (b₁ b₂ : Base) (c : Card), (bd.topOf (b₁.swapTwin t)).map (Card.swapTwin t) = some c →
      (bd.topOf (b₂.swapTwin t)).map (Card.swapTwin t) = some c → b₁ = b₂ := by
  intro b₁ b₂ c h₁ h₂
  obtain ⟨d₁, hd₁, hd₁'⟩ := Option.map_eq_some_iff.mp h₁
  obtain ⟨d₂, hd₂, hd₂'⟩ := Option.map_eq_some_iff.mp h₂
  have hd : d₁ = d₂ := by
    have h := congrArg (Card.swapTwin t) (hd₁'.trans hd₂'.symm)
    rw [Card.swapTwin_swapTwin, Card.swapTwin_swapTwin] at h
    exact h
  rw [← hd] at hd₂
  have hb : b₁.swapTwin t = b₂.swapTwin t := bd.inj _ _ _ hd₁ hd₂
  have hb2 := congrArg (fun b => Base.swapTwin t b) hb
  rw [Base.swapTwin_swapTwin, Base.swapTwin_swapTwin] at hb2
  exact hb2

/-- Conjugate the board by the local twin swap of the pair `t`,
`t.flipSuit` (mirrors `mapBy`'s involution conjugation) — the
representation-canonicalization action (Klondike/TwinSwap.lean). -/
def mapByTwin (bd : Board) (t : Card) : Board where
  topOf := fun b => (bd.topOf (b.swapTwin t)).map (Card.swapTwin t)
  inj := mapByTwin_inj bd t

-- `Base.swapFull`, `base_map_inj`, the generic `mapByWith`, and
-- `mapByFull` were added during the Φ-conjugation detour (2026-09-13)
-- and removed the same day with that design's refutation; `mapByTwin`
-- covers the live use.

/-- The cards transitively above `c` (the run sitting on it), walked
with fuel (defensive against ill-formed cycles: the walk stops early).
Used by `pilePile`'s self-landing guard.

R1 (2026-09-14): the kit below is the walk's public face — cite
`aboveOf_step_none`/`_some`, `aboveOf_congr`, `aboveOf_sub`,
`aboveOf_eq_go`, `aboveOf_self_disjoint`, not the internals.
`aboveOf.go` stays public only while TwinSwap/TwinExchange/Relabel/
TwinAgnostic still reference it directly
-- deprecation: cite the kit, private-ization pending. -/
def aboveOf (bd : Board) (c : Card) : List Card :=
  let rec go : Nat → Base → List Card → List Card
    | 0, _, acc => acc
    | fuel + 1, b, acc =>
        match bd.topOf b with
        | none => acc
        | some c' => if acc.contains c' then acc else go fuel (Sum.inr c') (c' :: acc)
  go 52 (Sum.inr c) []

/-! ### The `aboveOf` walk kit (R1, 2026-09-14)

The fuel is an implementation detail.  The kit proves, once and
fuel-free at the consumer face: the one-step expansion
(`aboveOf_step_none`/`_some`), the no-truncation bound
(`aboveOf_eq_go` — the ≤-52-distinct-cards argument, so 52 fuel is
provably never the binding constraint), the slot-agreement congruence
(`aboveOf_congr`, the general form; TwinSwap's `aboveOf_congr_off` is
the pair-shaped instance), the pointwise sub-board subset
(`aboveOf_sub`; the detach instances), and the forest kit
(`aboveOf_grading`/`aboveOf_self_disjoint`).  The go-level
unfold/step/stop lemmas are exposed for the inductions that still
need them, so that `aboveOf_go_succ` need not be re-homed per file
(Relabel's root-level copy stays until the coordinated pass). -/

/-- The definitional equation, for `show`-casts at consumer sites. -/
theorem aboveOf_eq (bd : Board) (c : Card) :
    bd.aboveOf c = aboveOf.go bd 52 (Sum.inr c) [] := rfl

/-- The one-step unfold (re-homed from Relabel.lean's root-level
`aboveOf_go_succ`; that copy stays until the coordinated pass). -/
theorem aboveOf_go_succ (bd : Board) (fuel : Nat) (b : Base) (acc : List Card) :
    aboveOf.go bd (fuel + 1) b acc
      = match bd.topOf b with
        | none => acc
        | some c' => if acc.contains c' then acc
                     else aboveOf.go bd fuel (Sum.inr c') (c' :: acc) := rfl

/-- The accumulator only grows: every card already seen survives into
the walk's result (the membership form; TwinSwap's subset-form
`Board.aboveOf_go_mono` is the same fact). -/
theorem aboveOf_go_mem (bd : Board) : ∀ (fuel : Nat) (b : Base) (acc : List Card) (y : Card),
    y ∈ acc → y ∈ aboveOf.go bd fuel b acc := by
  intro fuel
  induction fuel with
  | zero => intro b acc y hy; exact hy
  | succ n ih =>
      intro b acc y hy
      rw [aboveOf_go_succ]
      cases ht : bd.topOf b with
      | none => exact hy
      | some c' =>
          show y ∈ (if acc.contains c' = true then acc
            else aboveOf.go bd n (Sum.inr c') (c' :: acc))
          by_cases hc : acc.contains c' = true
          · rw [if_pos hc]; exact hy
          · rw [if_neg hc]
            exact ih (Sum.inr c') (c' :: acc) y (by simp [hy])

/-- One walk step over a matched card: the reduced form for rewriting
past the constructor-headed match (Theorems' `aboveOf_go_step`,
re-homed). -/
theorem aboveOf_go_step {bd : Board} {b₀ : Base} {c' : Card} {n : Nat} {acc : List Card}
    (hbd : bd.topOf b₀ = some c') (hc : acc.contains c' ≠ true) :
    aboveOf.go bd (n + 1) b₀ acc = aboveOf.go bd n (Sum.inr c') (c' :: acc) := by
  rw [aboveOf_go_succ, hbd]
  show (if acc.contains c' = true then acc else aboveOf.go bd n (Sum.inr c') (c' :: acc))
      = aboveOf.go bd n (Sum.inr c') (c' :: acc)
  rw [if_neg hc]

/-- The walk's first read: a `none` cell ends the walk at the
accumulator. -/
theorem aboveOf_go_topOf_none {bd : Board} {b : Base} (h : bd.topOf b = none)
    (fuel : Nat) (acc : List Card) :
    aboveOf.go bd (fuel + 1) b acc = acc := by
  rw [aboveOf_go_succ, h]

/-- The guard stop: reading a card already in the accumulator ends the
walk there. -/
theorem aboveOf_go_stop {bd : Board} {b₀ : Base} {c' : Card} {n : Nat} {acc : List Card}
    (hbd : bd.topOf b₀ = some c') (hc : acc.contains c' = true) :
    aboveOf.go bd (n + 1) b₀ acc = acc := by
  rw [aboveOf_go_succ, hbd]
  show (if acc.contains c' = true then acc else aboveOf.go bd n (Sum.inr c') (c' :: acc)) = acc
  rw [if_pos hc]

/-- The contains-guard keeps the accumulator duplicate-free. -/
theorem aboveOf_nodup (bd : Board) : ∀ (n : Nat) (b : Base) (acc : List Card),
    acc.Nodup → (aboveOf.go bd n b acc).Nodup := by
  intro n
  induction n with
  | zero => intro b acc hnd; exact hnd
  | succ n ih =>
      intro b acc hnd
      rw [aboveOf_go_succ]
      cases ht : bd.topOf b with
      | none => exact hnd
      | some c' =>
          show (if acc.contains c' = true then acc
            else aboveOf.go bd n (Sum.inr c') (c' :: acc)).Nodup
          by_cases hc : acc.contains c' = true
          · rw [if_pos hc]; exact hnd
          · rw [if_neg hc]
            refine ih (Sum.inr c') (c' :: acc) (List.nodup_cons.mpr ⟨?_, hnd⟩)
            intro hmem
            exact hc ((List.contains_iff_mem).mpr hmem)

private theorem mem_split_aux {α : Type} : ∀ (l : List α) (x : α), x ∈ l →
    ∃ l₁ l₂, l = l₁ ++ x :: l₂ := by
  intro l
  induction l with
  | nil => intro x h; cases h
  | cons a t ih =>
      intro x h
      rcases List.mem_cons.mp h with rfl | h'
      · exact ⟨[], t, rfl⟩
      · obtain ⟨l₁, l₂, hs⟩ := ih x h'
        exact ⟨a :: l₁, l₂, by rw [hs, List.cons_append]⟩

private theorem perm_mid_aux {α : Type} : ∀ (pre : List α) (a : α) (post : List α),
    (pre ++ a :: post).Perm (a :: (pre ++ post)) := by
  intro pre
  induction pre with
  | nil => intro a post; exact List.Perm.refl _
  | cons p pre' ih =>
      intro a post
      exact List.Perm.trans (List.Perm.cons p (ih a post)) (List.Perm.swap a p (pre' ++ post))

private theorem nodup_subset_length_le_aux : ∀ (L l : List Card), l.Nodup →
    (∀ z ∈ l, z ∈ L) → l.length ≤ L.length := by
  intro L
  induction L with
  | nil =>
      intro l hnd hsub
      cases l with
      | nil => exact Nat.le_refl _
      | cons a t => exact absurd (hsub a (by simp)) (by simp)
  | cons a L' ih =>
      intro l hnd hsub
      by_cases ha : a ∈ l
      · obtain ⟨pre, post, hs⟩ := mem_split_aux l a ha
        rw [hs] at hnd hsub ⊢
        have hnd' : (a :: (pre ++ post)).Nodup := hnd.perm (perm_mid_aux pre a post)
        obtain ⟨ha', hndpp⟩ := List.nodup_cons.mp hnd'
        have hsub' : ∀ z ∈ pre ++ post, z ∈ L' := by
          intro z hz
          have hzl : z ∈ pre ++ a :: post := by
            rcases List.mem_append.mp hz with h | h
            · exact List.mem_append.mpr (Or.inl h)
            · exact List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inr h)))
          rcases List.mem_cons.mp (hsub z hzl) with h | h
          · rw [h] at hz
            exact absurd hz ha'
          · exact h
        have hlen := ih (pre ++ post) hndpp hsub'
        simp only [List.length_append, List.length_cons] at hlen ⊢
        omega
      · have hsub' : ∀ z ∈ l, z ∈ L' := by
          intro z hz
          rcases List.mem_cons.mp (hsub z hz) with h | h
          · rw [h] at hz
            exact absurd hz ha
          · exact h
        have hlen := ih l hnd hsub'
        simp only [List.length_cons] at hlen ⊢
        omega

/-- **The 52-count** (pigeonhole): distinct cards are at most the
universe — the fact that keeps the walk's fuel from ever binding. -/
theorem nodup_cards_length_le {l : List Card} (hnd : l.Nodup) : l.length ≤ 52 := by
  have h := nodup_subset_length_le_aux Card.universe l hnd (fun z _ => z.mem_universe)
  rwa [Card.universe_length] at h

/-- Fuel saturation: once the seen-cards budget covers the deck, one
more unit of fuel changes nothing (the walk can only continue through
cards not yet seen, and there are but 52). -/
private theorem aboveOf_go_fuel_sat (bd : Board) : ∀ (m : Nat) (x : Card) (acc : List Card),
    acc.Nodup → 52 ≤ acc.length + m →
    aboveOf.go bd (m + 1) (Sum.inr x) acc = aboveOf.go bd m (Sum.inr x) acc := by
  intro m
  induction m with
  | zero =>
      intro x acc hnd hlen
      have h52 : acc.length = 52 :=
        Nat.le_antisymm (nodup_cards_length_le hnd) (by simpa using hlen)
      show aboveOf.go bd (0 + 1) (Sum.inr x) acc = acc
      rw [aboveOf_go_succ]
      cases ht : bd.topOf (Sum.inr x) with
      | none => rfl
      | some c' =>
          show (if acc.contains c' = true then acc
            else aboveOf.go bd 0 (Sum.inr c') (c' :: acc)) = acc
          by_cases hc : acc.contains c' = true
          · rw [if_pos hc]
          · exfalso
            have hmem : c' ∉ acc := fun hmem => hc ((List.contains_iff_mem).mpr hmem)
            have hcon := nodup_cards_length_le (List.nodup_cons.mpr ⟨hmem, hnd⟩)
            simp only [List.length_cons] at hcon
            omega
  | succ m ih =>
      intro x acc hnd hlen
      cases ht : bd.topOf (Sum.inr x) with
      | none => rw [aboveOf_go_topOf_none ht, aboveOf_go_topOf_none ht]
      | some c' =>
          by_cases hc : acc.contains c' = true
          · rw [aboveOf_go_stop ht hc (n := m + 1), aboveOf_go_stop ht hc (n := m)]
          · rw [aboveOf_go_step ht hc (n := m + 1), aboveOf_go_step ht hc (n := m)]
            refine ih c' (c' :: acc) (List.nodup_cons.mpr ⟨fun hmem => hc ((List.contains_iff_mem).mpr hmem), hnd⟩) ?_
            simp only [List.length_cons]
            omega

/-- **No fuel truncation**: the walk terminates before the fuel runs
out — any fuel beyond the deck's worth of cards gives the same list
(the ≤-52-distinct-cards argument).  `aboveOf`'s 52 is a definitional
choice, not a semantic constraint. -/
theorem aboveOf_eq_go {bd : Board} {c : Card} : ∀ n : Nat, 52 ≤ n →
    bd.aboveOf c = aboveOf.go bd n (Sum.inr c) [] := by
  intro n hn
  obtain ⟨k, hk⟩ := Nat.le.dest hn
  subst hk
  clear hn
  show aboveOf.go bd 52 (Sum.inr c) [] = aboveOf.go bd (52 + k) (Sum.inr c) []
  induction k with
  | zero => rfl
  | succ k ih =>
      show aboveOf.go bd 52 (Sum.inr c) [] = aboveOf.go bd (52 + (k + 1)) (Sum.inr c) []
      rw [show 52 + (k + 1) = (52 + k) + 1 from rfl]
      rw [aboveOf_go_fuel_sat bd (52 + k) c [] (by simp) (show 52 ≤ 0 + (52 + k) by omega)]
      exact ih

/-- The seeded walk: when the plain walk from `x` never revisits the
seed card `s` (every card it outputs differs from `s`), the walk with
`s` pre-seeded into the accumulator is the same list with `s`
appended at the end — the contains-guard sees the seed exactly when
the plain walk would have read it. -/
theorem aboveOf_go_seed (bd : Board) (s : Card) : ∀ (n : Nat) (x : Card) (l : List Card),
    (∀ z, z ∈ aboveOf.go bd n (Sum.inr x) l → z ≠ s) →
    aboveOf.go bd n (Sum.inr x) (l ++ [s]) = (aboveOf.go bd n (Sum.inr x) l) ++ [s] := by
  intro n
  induction n with
  | zero => intro x l _; rfl
  | succ n ih =>
      intro x l hout
      rw [aboveOf_go_succ bd n (Sum.inr x) (l ++ [s]), aboveOf_go_succ bd n (Sum.inr x) l]
      cases ht : bd.topOf (Sum.inr x) with
      | none => rfl
      | some y =>
          by_cases hcy : l.contains y = true
          · have hcy2 : (l ++ [s]).contains y = true :=
              (List.contains_iff_mem).mpr
                (List.mem_append.mpr (Or.inl ((List.contains_iff_mem).mp hcy)))
            show (if (l ++ [s]).contains y = true then l ++ [s]
                else aboveOf.go bd n (Sum.inr y) (y :: (l ++ [s])))
                = ((if l.contains y = true then l
                    else aboveOf.go bd n (Sum.inr y) (y :: l)) ++ [s])
            rw [if_pos hcy2, if_pos hcy]
          · by_cases hys : y = s
            · subst hys
              exfalso
              have hstep : aboveOf.go bd (n + 1) (Sum.inr x) l =
                  aboveOf.go bd n (Sum.inr y) (y :: l) :=
                aboveOf_go_step ht hcy
              have hmem : y ∈ aboveOf.go bd (n + 1) (Sum.inr x) l := by
                rw [hstep]
                exact aboveOf_go_mem bd n (Sum.inr y) (y :: l) y (by simp)
              exact absurd rfl (hout y hmem)
            · have hne : ¬ ((l ++ [s]).contains y = true) := by
                intro hcon
                rcases List.mem_append.mp ((List.contains_iff_mem).mp hcon) with h | h
                · exact hcy ((List.contains_iff_mem).mpr h)
                · exact hys (List.mem_singleton.mp h)
              show (if (l ++ [s]).contains y = true then l ++ [s]
                  else aboveOf.go bd n (Sum.inr y) (y :: (l ++ [s])))
                  = ((if l.contains y = true then l
                      else aboveOf.go bd n (Sum.inr y) (y :: l)) ++ [s])
              rw [if_neg hne, if_neg hcy]
              have hstep : aboveOf.go bd (n + 1) (Sum.inr x) l =
                  aboveOf.go bd n (Sum.inr y) (y :: l) :=
                aboveOf_go_step ht hcy
              exact ih y (y :: l) (fun z hz => hout z (by rw [hstep]; exact hz))

/-- The one-step expansion, bare arm (no fuel tokens): a `none` at
`c`'s own seat ends the run. -/
theorem aboveOf_step_none {bd : Board} {c : Card}
    (h : bd.topOf (Sum.inr c) = none) : bd.aboveOf c = [] := by
  show aboveOf.go bd (51 + 1) (Sum.inr c) ([] : List Card) = []
  rw [aboveOf_go_succ, h]

/-- The one-step expansion, seated arm (no fuel tokens): with `c'` on
`c` and no cycle back through `c'` (free on forest boards via
`aboveOf_self_disjoint`), the run above `c` is the run above `c'`
with `c'` appended at the bottom. -/
theorem aboveOf_step_some {bd : Board} {c c' : Card}
    (h : bd.topOf (Sum.inr c) = some c') (hnc : c' ∉ bd.aboveOf c') :
    bd.aboveOf c = bd.aboveOf c' ++ [c'] := by
  have h53 : bd.aboveOf c = aboveOf.go bd 53 (Sum.inr c) [] := aboveOf_eq_go 53 (by omega)
  rw [h53]
  show aboveOf.go bd (52 + 1) (Sum.inr c) ([] : List Card) = bd.aboveOf c' ++ [c']
  rw [aboveOf_go_succ, h]
  show (if ([] : List Card).contains c' = true then ([] : List Card)
      else aboveOf.go bd 52 (Sum.inr c') (c' :: ([] : List Card)))
      = bd.aboveOf c' ++ [c']
  rw [if_neg (by simp)]
  exact aboveOf_go_seed bd c' 52 c' [] (fun z hz heq => hnc (heq ▸ hz))

/-- The general walk congruence, fuel level (the induction form):
two boards that agree on every card-seat the walk probes — the start
seat and the seats of every card the plain walk outputs (the
self-maintaining invariant) — run the identical walk.  `P` is the
agreement set; TwinSwap's `aboveOf_go_congr_aux` is the pair-shaped
instance. -/
theorem aboveOf_go_congr {bd bd' : Board} {P : Card → Prop}
    (hagree : ∀ y, P y → bd.topOf (Sum.inr y) = bd'.topOf (Sum.inr y)) :
    ∀ (n : Nat) (x : Card) (acc : List Card), P x →
      (∀ z, z ∈ aboveOf.go bd n (Sum.inr x) acc → P z) →
      aboveOf.go bd' n (Sum.inr x) acc = aboveOf.go bd n (Sum.inr x) acc := by
  intro n
  induction n with
  | zero => intro x acc _ _; rfl
  | succ n ih =>
      intro x acc hPx hPout
      rw [aboveOf_go_succ bd, aboveOf_go_succ bd']
      rw [hagree x hPx]
      cases ht : bd'.topOf (Sum.inr x) with
      | none => rfl
      | some y =>
          have htbd : bd.topOf (Sum.inr x) = some y := (hagree x hPx).trans ht
          show (if acc.contains y = true then acc
              else aboveOf.go bd' n (Sum.inr y) (y :: acc))
              = (if acc.contains y = true then acc
                  else aboveOf.go bd n (Sum.inr y) (y :: acc))
          by_cases hcy : acc.contains y = true
          · rw [if_pos hcy, if_pos hcy]
          · rw [if_neg hcy, if_neg hcy]
            have hstep : aboveOf.go bd (n + 1) (Sum.inr x) acc =
                aboveOf.go bd n (Sum.inr y) (y :: acc) :=
              aboveOf_go_step htbd hcy
            refine ih y (y :: acc) ?_ (fun z hz => hPout z (by rw [hstep]; exact hz))
            have hymem : y ∈ aboveOf.go bd (n + 1) (Sum.inr x) acc := by
              rw [hstep]
              exact aboveOf_go_mem bd n (Sum.inr y) (y :: acc) y (by simp)
            exact hPout y hymem

/-- **The walk congruence** (the consumer-facing slot-agreement form):
if the boards agree on `c`'s own seat and on every card-seat the walk
from `c` reads — exactly the seats of `c` and of the cards in the run
— the two walks from `c` coincide.  TwinSwap's `Board.aboveOf_congr_off`
(agreement off a twin pair) is the pair-shaped instance. -/
theorem aboveOf_congr {bd bd' : Board} {c : Card}
    (hagree : ∀ x : Card, x ∈ c :: bd.aboveOf c →
      bd.topOf (Sum.inr x) = bd'.topOf (Sum.inr x)) :
    bd'.aboveOf c = bd.aboveOf c := by
  show aboveOf.go bd' 52 (Sum.inr c) [] = aboveOf.go bd 52 (Sum.inr c) []
  exact aboveOf_go_congr (P := fun x => x ∈ c :: bd.aboveOf c) hagree 52 c []
    (by simp) (fun z hz => List.mem_cons_of_mem _ hz)

/-- The one-sided walk congruence, fuel level: if every cell of `bd'`
is `bd`'s or empty, then `bd'`'s walk from any seat is contained in
`bd`'s — the walk either follows the same steps or stops earlier (at
a cell `bd` emptied); the accumulator is covered by both sides'
outputs. -/
theorem aboveOf_go_sub {bd bd' : Board}
    (hsub : ∀ b : Base, bd'.topOf b = none ∨ bd'.topOf b = bd.topOf b) :
    ∀ (n : Nat) (b : Base) (acc : List Card) (y : Card),
      y ∈ aboveOf.go bd' n b acc → y ∈ aboveOf.go bd n b acc := by
  intro n
  induction n with
  | zero => intro b acc y hy; exact hy
  | succ n ih =>
      intro b acc y hy
      rw [aboveOf_go_succ] at hy
      cases ht : bd'.topOf b with
      | none =>
          rw [ht] at hy
          exact aboveOf_go_mem bd (n + 1) b acc y hy
      | some c' =>
          rw [ht] at hy
          have hy' : y ∈ (if acc.contains c' = true then acc
              else aboveOf.go bd' n (Sum.inr c') (c' :: acc)) := hy
          by_cases hcy : acc.contains c' = true
          · rw [if_pos hcy] at hy'
            exact aboveOf_go_mem bd (n + 1) b acc y hy'
          · rw [if_neg hcy] at hy'
            have hbd : bd.topOf b = some c' := by
              rcases hsub b with h | h
              · rw [h] at ht; exact absurd ht (by simp)
              · rw [h] at ht; exact ht
            rw [aboveOf_go_step hbd hcy]
            exact ih (Sum.inr c') (c' :: acc) y hy'

/-- `aboveOf`-level subset: the run above `c` only shrinks under a
pointwise sub-board (every cell equal or emptied).  The detach
instances (`aboveOf_detach_subset`, Theorems; `Board.aboveOf_sub_detach`,
TwinExchange) are the shape's consumers. -/
theorem aboveOf_sub {bd bd' : Board} {c : Card}
    (hsub : ∀ b : Base, bd'.topOf b = none ∨ bd'.topOf b = bd.topOf b) :
    ∀ y ∈ bd'.aboveOf c, y ∈ bd.aboveOf c := fun _ hy =>
  aboveOf_go_sub hsub 52 (Sum.inr c) [] _ hy

/-- The forest grading, board level: along the run above `c`, every
card is strictly below `c` in any potential that decreases along the
matching's card-edges (the state-level form is Theorems'
`aboveOf_rank_grading`). -/
theorem aboveOf_grading {bd : Board} {φ : Card → Nat}
    (hφ : ∀ c y, bd.topOf (Sum.inr c) = some y → φ y < φ c) (c : Card) :
    ∀ d ∈ bd.aboveOf c, φ d < φ c := by
  have main : ∀ (fuel : Nat) (x : Card) (acc : List Card),
      (∀ z ∈ acc, φ z < φ c) → (φ x < φ c ∨ x = c) →
        ∀ d ∈ aboveOf.go bd fuel (Sum.inr x) acc, φ d < φ c := by
    intro fuel
    induction fuel with
    | zero =>
        intro x acc hacc _ d hd
        have hd' : d ∈ acc := hd
        exact hacc d hd'
    | succ f ih =>
        intro x acc hacc hx d hd
        rw [aboveOf_go_succ] at hd
        cases ht : bd.topOf (Sum.inr x) with
        | none =>
            rw [ht] at hd
            have hd' : d ∈ acc := hd
            exact hacc d hd'
        | some y =>
            rw [ht] at hd
            have hd' : d ∈ (if acc.contains y = true then acc
                else aboveOf.go bd f (Sum.inr y) (y :: acc)) := hd
            by_cases hcy : acc.contains y = true
            · rw [if_pos hcy] at hd'
              exact hacc d hd'
            · rw [if_neg hcy] at hd'
              have hxy : φ y < φ x := hφ x y ht
              have hyc : φ y < φ c := by
                rcases hx with h | h
                · omega
                · exact h ▸ hxy
              refine ih y (y :: acc) (fun z hz => ?_) (Or.inl hyc) d hd'
              rcases List.mem_cons.mp hz with rfl | hz'
              · exact hyc
              · exact hacc z hz'
  intro d hd
  exact main 52 c [] (by simp) (Or.inr rfl) d hd

/-- No card is above itself when the matching admits a forest
potential (the state-level packaging is `aboveOf_irrefl`, Theorems;
WF alone does NOT give this — the AboveIrreflWitness rescope). -/
theorem aboveOf_self_disjoint {bd : Board} {φ : Card → Nat}
    (hφ : ∀ c y, bd.topOf (Sum.inr c) = some y → φ y < φ c) (c : Card) :
    c ∉ bd.aboveOf c := fun hmem =>
  absurd (aboveOf_grading hφ c c hmem) (Nat.lt_irrefl _)

end Board
