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

/-- Full twin swap on bases (Φ's board action). -/
def Base.swapFull (t : Card) : Base → Base := Sum.map id (Card.swapFull t)

@[simp] theorem Base.swapFull_swapFull (t : Card) (b : Base) :
    (b.swapFull t).swapFull t = b := by
  cases b <;> simp [Base.swapFull]

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

/-- A card-mapped base map is injective when the card map is. -/
theorem base_map_inj {f : Card → Card} (hf : Function.Injective f) :
    Function.Injective (Sum.map id f : Base → Base) := by
  intro x y hxy
  cases x with
  | inl a =>
    cases y with
    | inl b =>
      have hab : a = b := by simpa [Sum.map] using hxy
      rw [hab]
    | inr d => simp [Sum.map] at hxy
  | inr c =>
    cases y with
    | inl b => simp [Sum.map] at hxy
    | inr d =>
      have hcd : f c = f d := by simpa [Sum.map] using hxy
      exact congrArg Sum.inr (hf hcd)

/-- An involution is injective (no `Function.Involutive` in this core —
proved inline). -/
theorem inj_of_involutive {f : Card → Card} (hf : ∀ x, f (f x) = x) :
    Function.Injective f := by
  intro x y h
  have h' := congrArg f h
  rwa [hf, hf] at h'

/-- The generic board conjugation by an involutive card permutation —
the one proof behind `mapBy`/`mapByTwin`/`mapByFull`. -/
theorem mapByWith_inj (bd : Board) {f : Card → Card} (hf : ∀ x, f (f x) = x) :
    ∀ (b₁ b₂ : Base) (c : Card), (bd.topOf (Sum.map id f b₁)).map f = some c →
      (bd.topOf (Sum.map id f b₂)).map f = some c → b₁ = b₂ := by
  intro b₁ b₂ c h₁ h₂
  obtain ⟨d₁, hd₁, hd₁'⟩ := Option.map_eq_some_iff.mp h₁
  obtain ⟨d₂, hd₂, hd₂'⟩ := Option.map_eq_some_iff.mp h₂
  have hd : d₁ = d₂ := inj_of_involutive hf (hd₁'.trans hd₂'.symm)
  rw [← hd] at hd₂
  exact base_map_inj (inj_of_involutive hf) (bd.inj _ _ _ hd₁ hd₂)

/-- Conjugate the board by an involutive card permutation `f`. -/
def mapByWith (bd : Board) (f : Card → Card) (hf : ∀ x, f (f x) = x) : Board where
  topOf := fun b => (bd.topOf (Sum.map id f b)).map f
  inj := mapByWith_inj bd hf

/-- Conjugate the board by the full twin swap `Card.swapFull t` (Φ's
board action — Klondike/TwinSwap.lean). -/
def mapByFull (bd : Board) (t : Card) : Board := bd.mapByWith (Card.swapFull t)
  (Card.swapFull_swapFull t)

/-- The cards transitively above `c` (the run sitting on it), walked
with fuel (defensive against ill-formed cycles: the walk stops early).
Used by `pilePile`'s self-landing guard. -/
def aboveOf (bd : Board) (c : Card) : List Card :=
  let rec go : Nat → Base → List Card → List Card
    | 0, _, acc => acc
    | fuel + 1, b, acc =>
        match bd.topOf b with
        | none => acc
        | some c' => if acc.contains c' then acc else go fuel (Sum.inr c') (c' :: acc)
  go 52 (Sum.inr c) []

end Board
