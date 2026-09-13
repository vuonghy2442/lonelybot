import Klondike.Bridge

/-!
# The initial state — exhibiting WF states

Every theorem so far is quantified over `st.WF` states that were never
exhibited: without a constructor, the entire development risks
vacuity.  This module builds the standard game — deal splitting, the
initial board (each pile's top dealt card face-up on the boundary),
empty foundations, fresh stock — and states `initial_wf`.

It also carries runnable sanity checks (`by decide`), the seed of the
cross-validation oracle: the model executes.
-/

/-- Where pile `a`'s slice starts in the deal list (0, 1, 3, 6, 10,
15, 21 — the triangular numbers; the 28 dealt cards precede the
24-card stock). -/
def Anchor.start : Anchor → Nat
  | .p0 => 0 | .p1 => 1 | .p2 => 3 | .p3 => 6 | .p4 => 10 | .p5 => 15 | .p6 => 21

/-- Deal from a card list: pile `a` takes the next `a.toIdx + 1`
cards, the remainder is the stock.  Any list works; well-formedness
needs 52 distinct cards. -/
def Deal.ofList (l : List Card) : Deal where
  piles := fun a => (l.drop a.start).take (a.toIdx + 1)
  stock := l.drop 28

/-- The standard deal: the universe order, split triangularly. -/
def Deal.standard : Deal := Deal.ofList Card.universe

/-- The base a pile's top dealt card sits on: the card beneath it, or
the anchor for the single-card pile. -/
def initBase (d : Deal) (a : Anchor) : Base :=
  match a.toIdx with
  | 0 => Sum.inl a
  | k + 1 => match (d.piles a)[k]? with
    | some under => Sum.inr under
    | none => Sum.inl a

/-- One deal step: attach pile `a`'s top dealt card on its base (a
no-op for an empty pile). -/
def initStep (d : Deal) (bd : Board) (a : Anchor) : Board :=
  match (d.piles a).getLast? with
  | some top => (bd.attach (initBase d a) top).getD bd
  | none => bd

/-- The initial board: each pile's top dealt card, face-up, sitting
on the boundary (the card beneath it, or the anchor for the
single-card pile). -/
def initialBoard (d : Deal) : Board :=
  Anchor.all.foldl (initStep d) Board.empty

/-- The initial state of a dealt game: hidden boundary at `a.toIdx`
per pile, foundations empty, stock fresh at the start of its first
pass. -/
def State.initial (d : Deal) (drawStep : Nat) : State where
  deal := d
  board := initialBoard d
  heights := fun _ => 0
  depths := fun a => a.toIdx
  stock := ⟨d.stock, 0⟩
  drawStep := drawStep

/-! ## Statements -/

/-- The 52 cards are distinct (index-wise, over the factored
product). -/
theorem Card.universe_noDup : noDupCards Card.universe := by
  intro i j hi hj heq
  rw [Card.universe_length] at hi hj
  have hall : ∀ i ∈ List.range 52, ∀ j ∈ List.range 52,
      Card.universe[i]? = Card.universe[j]? → i = j := by decide
  exact hall i (List.mem_range.mpr hi) j (List.mem_range.mpr hj) heq

/-- Reassembling a chunk: the first `n` of `drop s`, followed by
`drop t` (with `s + n = t`), is `drop s` again. -/
theorem take_drop_chunk {α : Type} (l : List α) (s n t : Nat) (h : s + n = t) :
    (l.drop s).take n ++ l.drop t = l.drop s := by
  rw [← h, ← List.drop_drop, List.take_append_drop]

/-- The `ofList` slices, exposed for rewriting. -/
theorem Deal.ofList_piles (l : List Card) (a : Anchor) :
    (Deal.ofList l).piles a = (l.drop a.start).take (a.toIdx + 1) := rfl

theorem Deal.ofList_stock (l : List Card) :
    (Deal.ofList l).stock = l.drop 28 := rfl

/-- The triangular split reassembles the list: the piles' concatenated
slices followed by the stock is `l` again, so `noDupCards` transfers
wholesale. -/
theorem Deal.ofList_split (l : List Card) :
    (Anchor.all.flatMap (Deal.ofList l).piles) ++ (Deal.ofList l).stock = l := by
  show (Anchor.all.flatMap fun a => (l.drop a.start).take (a.toIdx + 1)) ++ l.drop 28 = l
  simp only [Anchor.all, List.flatMap_cons, List.flatMap_nil, Anchor.start, Anchor.toIdx,
    Nat.reduceAdd, List.append_nil]
  rw [List.append_assoc, List.append_assoc, List.append_assoc, List.append_assoc,
    List.append_assoc, List.append_assoc,
    take_drop_chunk l 21 7 28 (by omega), take_drop_chunk l 15 6 21 (by omega),
    take_drop_chunk l 10 5 15 (by omega), take_drop_chunk l 6 4 10 (by omega),
    take_drop_chunk l 3 3 6 (by omega), take_drop_chunk l 1 2 3 (by omega),
    take_drop_chunk l 0 1 1 (by omega), List.drop_zero]

/-- `ofList` on 52 distinct cards is well-formed (lengths by the
triangular split, distinctness preserved by `drop`/`take`). -/
theorem Deal.ofList_wf {l : List Card} (hlen : l.length = 52) (hnd : noDupCards l) :
    (Deal.ofList l).WF := by
  refine ⟨fun a => ?_, ?_, ?_⟩
  · rw [Deal.ofList_piles, List.length_take, List.length_drop, hlen]
    cases a <;> decide
  · rw [Deal.ofList_stock, List.length_drop, hlen]
  · rw [Deal.ofList_split]
    exact hnd

/-- The step spec: one fold step either keeps a base's top or sets it
to the pile's top dealt card. -/
theorem initStep_topOf (d : Deal) (bd : Board) (a : Anchor) (b : Base) (c : Card)
    (h : (initStep d bd a).topOf b = some c) :
    bd.topOf b = some c ∨ (b = initBase d a ∧ (d.piles a).getLast? = some c) := by
  unfold initStep at h
  cases hgt : (d.piles a).getLast? with
  | none =>
    rw [hgt] at h
    exact Or.inl h
  | some top =>
    rw [hgt] at h
    have h2 : ((bd.attach (initBase d a) top).getD bd).topOf b = some c := h
    cases hat : bd.attach (initBase d a) top with
    | none =>
      rw [hat] at h2
      exact Or.inl h2
    | some bd' =>
      rw [hat] at h2
      have h' : bd'.topOf b = some c := h2
      by_cases hbb : b = initBase d a
      · subst hbb
        rw [Board.attach_topOf bd (initBase d a) top hat] at h'
        rw [Option.some.injEq] at h'
        exact Or.inr ⟨rfl, congrArg some h'⟩
      · rw [Board.attach_topOf_ne bd (initBase d a) top hat hbb] at h'
        exact Or.inl h'

/-- The fold spec: the final board's tops come either from the seed
or from some pile's top dealt card. -/
theorem initFold_topOf (d : Deal) : ∀ (as : List Anchor) (bs : Board) (b : Base) (c : Card),
    (as.foldl (initStep d) bs).topOf b = some c →
    bs.topOf b = some c ∨ ∃ a ∈ as, b = initBase d a ∧ (d.piles a).getLast? = some c := by
  intro as
  induction as with
  | nil => intro bs b c h; exact Or.inl h
  | cons a rest ih =>
    intro bs b c h
    rw [List.foldl_cons] at h
    rcases ih (initStep d bs a) b c h with hold | ⟨a', ha', hbq, hgt⟩
    · rcases initStep_topOf d bs a b c hold with hold' | ⟨hbq, hgt⟩
      · exact Or.inl hold'
      · exact Or.inr ⟨a, List.mem_cons_self, hbq, hgt⟩
    · exact Or.inr ⟨a', List.mem_cons_of_mem _ ha', hbq, hgt⟩

/-- The initial board's tops are exactly the piles' top dealt cards. -/
theorem initialBoard_topOf (d : Deal) (b : Base) (c : Card)
    (h : (initialBoard d).topOf b = some c) :
    ∃ a ∈ Anchor.all, b = initBase d a ∧ (d.piles a).getLast? = some c := by
  rcases initFold_topOf d Anchor.all Board.empty b c h with hold | hex
  · rw [Board.empty_topOf] at hold; simp at hold
  · exact hex

/-- A pile of length `k + 2` whose last is `c` and whose `k`-th card
is `under` decomposes with `under` directly beneath `c`. -/
theorem decompose_last : ∀ (k : Nat) (l : List Card) (u c : Card),
    l.length = k + 2 → l[k]? = some u → l.getLast? = some c →
    ∃ t, l = t ++ u :: c :: [] := by
  intro k
  induction k with
  | zero =>
    intro l u c hlen h0 hgt
    cases l with
    | nil => simp at hlen
    | cons a t =>
      cases t with
      | nil => simp only [List.length_cons, List.length_nil] at hlen; omega
      | cons b r =>
        cases r with
        | nil =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at h0
          simp at hgt
          subst h0
          subst hgt
          exact ⟨[], rfl⟩
        | cons z zs =>
          simp only [List.length_cons, List.length_cons] at hlen
          omega
  | succ k ih =>
    intro l u c hlen h0 hgt
    cases l with
    | nil => simp at hlen
    | cons a t =>
      simp only [List.length_cons] at hlen
      simp only [List.getElem?_cons_succ] at h0
      cases t with
      | nil => simp at h0
      | cons x t' =>
        obtain ⟨t₀, ht⟩ := ih (x :: t') u c
          (by simp only [List.length_cons] at hlen ⊢; omega) h0 hgt
        exact ⟨a :: t₀, by rw [ht]; rfl⟩

/-- Last-element membership. -/
theorem mem_of_getLast {l : List Card} {c : Card} (h : l.getLast? = some c) : c ∈ l := by
  rw [← head?_reverse_eq_getLast?] at h
  cases hrev : l.reverse with
  | nil => rw [hrev] at h; simp at h
  | cons x t =>
    rw [hrev] at h
    simp only [List.head?_cons, Option.some.injEq] at h
    subst h
    exact List.mem_reverse.mp (by rw [hrev]; exact List.mem_cons_self)

/-- Distinctness of a suffix, from distinctness of the concatenation. -/
theorem noDupCards_append_right {l₁ l₂ : List Card} (h : noDupCards (l₁ ++ l₂)) :
    noDupCards l₂ := by
  intro i j hi hj heq
  have hv : ∀ k, (l₁ ++ l₂)[l₁.length + k]? = l₂[k]? := by
    intro k
    rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]
  have hb1 : l₁.length + i < (l₁ ++ l₂).length := by
    simp only [List.length_append]; omega
  have hb2 : l₁.length + j < (l₁ ++ l₂).length := by
    simp only [List.length_append]; omega
  have hve : (l₁ ++ l₂)[l₁.length + i]? = (l₁ ++ l₂)[l₁.length + j]? := by
    rw [hv, hv]; exact heq
  have hres := h (l₁.length + i) (l₁.length + j) hb1 hb2 hve
  omega

/-- **The exhibit**: a well-formed deal's initial state is WF — the
theorems' hypotheses are non-vacuous, and `State.initial` is the
witness constructor: the top cards sit on the card they were dealt
onto (deal-adjacency), the fully-revealed single-card pile on its
anchor, the stock is the deal's stock. -/
theorem initial_wf {d : Deal} (hd : d.WF) (drawStep : Nat) :
    (State.initial d drawStep).WF := by
  obtain ⟨hlen, hstock, hnd⟩ := hd
  have hdw : d.WF := ⟨hlen, hstock, hnd⟩
  refine ⟨hdw, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a
    show a.toIdx ≤ (d.piles a).length
    have := hlen a
    omega
  · intro b c hb
    have hbo : (initialBoard d).bottomOf c = some b := (Board.bottomOf_eq _ _ _).mpr hb
    obtain ⟨a, -, hbq, hgt⟩ := initialBoard_topOf d b c hb
    subst hbq
    refine ⟨hbo, ?_⟩
    cases hti : a.toIdx with
    | zero =>
      simp only [initBase, hti]
      right
      have h1 : (d.piles a).length = 1 := by rw [hlen a, hti]
      cases hl : d.piles a with
      | nil => rw [hl] at h1; simp at h1
      | cons x t =>
        cases t with
        | nil =>
          rw [hl] at hgt
          simp at hgt
          show (d.piles a).head? = some c
          rw [hl]
          exact congrArg some hgt
        | cons y r =>
          rw [hl] at h1
          simp only [List.length_cons, List.length_cons] at h1
          omega
    | succ k =>
      have hlk : (d.piles a).length = k + 2 := by rw [hlen a, hti]
      simp only [initBase, hti]
      cases hget : (d.piles a)[k]? with
      | none =>
        have hn := List.getElem?_eq_none_iff.mp hget
        rw [hlk] at hn
        omega
      | some under =>
        obtain ⟨t, ht⟩ := decompose_last k (d.piles a) under c hlk hget hgt
        exact Or.inl ⟨a, t, [], ht⟩
  · intro c hc
    have hc' : ((initialBoard d).bottomOf c).isSome = true := hc
    cases h : (initialBoard d).bottomOf c with
    | none => rw [h] at hc'; simp at hc'
    | some b =>
      have htop : (initialBoard d).topOf b = some c := (Board.bottomOf_eq _ _ _).mp h
      obtain ⟨a, -, -, hgt⟩ := initialBoard_topOf d b c htop
      exact Cycle.posOf_eq_none (Deal.piles_stock_disj hdw (mem_of_getLast hgt))
  · intro c hc
    simp only [State.onFound] at hc
    rw [show (State.initial d drawStep).heights c.suit = 0 from rfl] at hc
    have : c.rank.toIdx < 0 := of_decide_eq_true hc
    omega
  · intro s
    show (0 : Nat) ≤ 13
    exact Nat.zero_le _
  · show (0 : Nat) ≤ d.stock.length
    exact Nat.zero_le _
  · exact noDupCards_append_right hnd
  · intro c hc
    exact hc

/-! ## Runnable sanity checks — the oracle seed -/

example : (Deal.standard.piles Anchor.p6).length = 7 := by decide

example : Deal.standard.stock.length = 24 := by decide

example : (State.initial Deal.standard 1).depths Anchor.p6 = 6 := by decide

/-- The standard game's single-card pile: its ace of hearts sits
directly on the anchor, and the derived `bottomOf` search finds it —
the matching machinery executes correctly on a concrete state. -/
example : (State.initial Deal.standard 1).board.bottomOf ⟨Suit.heart, Rank.ace⟩
    = some (Sum.inl Anchor.p0) := by decide
