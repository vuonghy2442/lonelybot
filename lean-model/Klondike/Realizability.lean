import Klondike.Progress

/-!
# B1: realizability and the parity lemma

no_pile_to_pile.md §3.  The engine's abstraction forgets where visible
cards sit; *realizability* — the existence of a legal matching with
the given visible set — is the invariant that makes the abstraction
truthful, and the parity lemma is its counting core:

    uncovered_t = present_t − placed_{t−4}   (the free count of type t)
-/

/-- The card's type: what the tableau rules see. -/
def Card.typeOf (c : Card) : Rank × Color := (c.rank, c.suit.color)

/-- Color negation. -/
def Color.flip : Color → Color
  | .red => .black
  | .black => .red

/-- Rank predecessor (aces have none). -/
def Rank.pred : Rank → Option Rank
  | .ace => none
  | .two => some .ace
  | .three => some .two
  | .four => some .three
  | .five => some .four
  | .six => some .five
  | .seven => some .six
  | .eight => some .seven
  | .nine => some .eight
  | .ten => some .nine
  | .jack => some .ten
  | .queen => some .jack
  | .king => some .queen

/-- The type of the cards that can sit directly on type-`t` cards
(`None` for aces) — their `t−4`. -/
def belowType (t : Rank × Color) : Option (Rank × Color) :=
  t.1.pred.map fun r => (r, t.2.flip)

/-! ## The counts -/

/-- The present count of type `t`: visible cards of that type. -/
def Board.presentType (bd : Board) (t : Rank × Color) : Nat :=
  (Card.universe.filter fun c =>
    decide (c.typeOf = t) && (bd.bottomOf c).isSome).length

/-- The placed-below count of type `t` (their `placed_{t−4}`): cards
of the below-type sitting on *present* type-`t` cards.  Anchor and
hidden-boundary bases do not count — only card-on-card placements. -/
def Board.placedBelow (bd : Board) (t : Rank × Color) : Nat :=
  match belowType t with
  | none => 0
  | some t' =>
      (Card.universe.filter fun c =>
        decide (c.typeOf = t') &&
        (match bd.bottomOf c with
         | some (Sum.inr d) => decide (d.typeOf = t) && (bd.bottomOf d).isSome
         | _ => false)).length

/-- Their `uncovered_t = present_t − placed_{t−4}`. -/
def Board.uncovered (bd : Board) (t : Rank × Color) : Nat :=
  bd.presentType t - bd.placedBelow t

/-- The free count of type `t`: present cards of the type with
nothing on them. -/
def Board.freeType (bd : Board) (t : Rank × Color) : Nat :=
  (Card.universe.filter fun c =>
    decide (c.typeOf = t) && (bd.bottomOf c).isSome &&
    decide (bd.topOf (Sum.inr c) = none)).length

/-- Edge legality, card-on-card part: a card sitting on a *present*
card fits it.  Anchor and hidden-boundary bases are exempt (the WF's
other disjuncts). -/
def Board.legalEdges (bd : Board) : Prop :=
  ∀ c d, bd.topOf (Sum.inr d) = some c → (bd.bottomOf d).isSome = true →
    canSitOn c d = true

/-- Boundary (a) of no_pile §3, definitional here: aces have no
below-type, so they are never counted as placed-below anything. -/
theorem placedBelow_ace (bd : Board) (κ : Color) :
    bd.placedBelow (Rank.ace, κ) = 0 := rfl

/-! ## The counting kit

Finite-cardinality plumbing, core-only: the universe's distinctness
(the index-based `noDupCards`, bridged to the head-style `NoDupP`), a
membership split, and the bijection-count principle — two distinct
lists with mutual inverse maps have equal lengths.  This is the
counting bijection the parity lemma needs: each below-type card
covers a distinct present type-`t` card, and the covered cards are
exactly the placed ones. -/

/-- The two colors: a color different from `κ` is its flip. -/
theorem color_ne_flip {κ κ' : Color} (h : κ ≠ κ') : κ = κ'.flip := by
  cases κ <;> cases κ' <;> simp [Color.flip] at h ⊢

/-- Rank predecessor ↔ the numeric view. -/
theorem rank_pred_iff (r r' : Rank) : r.pred = some r' ↔ r'.toIdx + 1 = r.toIdx := by
  cases r <;> cases r' <;> simp [Rank.pred, Rank.toIdx]

/-- Edge legality transports types: what sits on `d` has exactly
`d`'s below-type. -/
theorem canSitOn_belowType {c d : Card} (hcs : canSitOn c d = true) :
    belowType d.typeOf = some c.typeOf := by
  obtain ⟨hrank, hcol⟩ := (canSitOn_eq c d).mp hcs
  show d.rank.pred.map (fun r => (r, d.suit.color.flip)) = some (c.rank, c.suit.color)
  rw [(rank_pred_iff d.rank c.rank).mpr hrank]
  have hcol' : c.suit.color = d.suit.color.flip := color_ne_flip hcol
  rw [hcol']
  rfl

/-- Membership gives an index. -/
theorem mem_index {a : Card} : ∀ (l : List Card), a ∈ l → ∃ i : Nat, l[i]? = some a := by
  intro l
  induction l with
  | nil => intro h; simp at h
  | cons x t ih =>
      intro h
      rcases List.mem_cons.mp h with rfl | h
      · exact ⟨0, rfl⟩
      · obtain ⟨i, hi⟩ := ih h
        exact ⟨i + 1, by rw [List.getElem?_cons_succ]; exact hi⟩

/-- Membership split: an element sits at some middle position. -/
theorem mem_middle_split {a : Card} : ∀ (l : List Card), a ∈ l →
    ∃ pre post : List Card, l = pre ++ a :: post := by
  intro l
  induction l with
  | nil => intro h; simp at h
  | cons x t ih =>
      intro h
      rcases List.mem_cons.mp h with rfl | h
      · exact ⟨[], t, rfl⟩
      · obtain ⟨pre, post, ht⟩ := ih h
        exact ⟨x :: pre, post, by simp [ht]⟩

/-- Head-style distinctness (the induction-friendly form). -/
def NoDupP : List Card → Prop
  | [] => True
  | a :: t => a ∉ t ∧ NoDupP t

/-- Distinctness: the marked element occurs nowhere else. -/
theorem nodupP_sub (a : Card) : ∀ (pre post : List Card),
    NoDupP (pre ++ a :: post) → a ∉ pre ++ post := by
  intro pre
  induction pre with
  | nil =>
      intro post hnd hap
      obtain ⟨h1, -⟩ := hnd
      exact h1 hap
  | cons p pre' ih =>
      intro post hnd hap
      obtain ⟨hp, hndp⟩ := hnd
      rcases List.mem_append.mp hap with hap | hap
      · rcases List.mem_cons.mp hap with hap | hap
        · exact hp (by simp [hap])
        · exact ih post hndp (List.mem_append.mpr (Or.inl hap))
      · exact ih post hndp (List.mem_append.mpr (Or.inr hap))

/-- Distinctness survives removing the marked element. -/
theorem nodupP_remove (a : Card) : ∀ (pre post : List Card),
    NoDupP (pre ++ a :: post) → NoDupP (pre ++ post) := by
  intro pre
  induction pre with
  | nil => intro post hnd; obtain ⟨-, h2⟩ := hnd; exact h2
  | cons p pre' ih =>
      intro post hnd
      obtain ⟨hp, hndp⟩ := hnd
      refine ⟨?_, ih post hndp⟩
      intro hpp
      rcases List.mem_append.mp hpp with h | h
      · exact hp (List.mem_append.mpr (Or.inl h))
      · exact hp (List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inr h))))

/-- The index-based distinctness implies the head-style one. -/
theorem noDupCards_NoDupP : ∀ {l : List Card}, noDupCards l → NoDupP l := by
  intro l
  induction l with
  | nil => intro _; trivial
  | cons a t ih =>
      intro hnd
      refine ⟨?_, ih ?_⟩
      · intro hat
        obtain ⟨i, hi⟩ := mem_index t hat
        obtain ⟨hib, -⟩ := List.getElem?_eq_some_iff.mp hi
        have h0 : (a :: t)[0]? = some a := rfl
        have h1 : (a :: t)[i + 1]? = some a := by
          rw [List.getElem?_cons_succ]; exact hi
        have hcon : 0 = i + 1 :=
          hnd 0 (i + 1) (by simp only [List.length_cons]; omega)
            (by simp only [List.length_cons]; omega) (h0.trans h1.symm)
        omega
      · intro i j hi hj heq
        have hlen : (a :: t).length = t.length + 1 := rfl
        have hcon : i + 1 = j + 1 :=
          hnd (i + 1) (j + 1) (by rw [hlen]; omega) (by rw [hlen]; omega)
            (by rw [List.getElem?_cons_succ, List.getElem?_cons_succ]; exact heq)
        omega

/-- The 52 cards are distinct (index-wise, over the factored product). -/
theorem universe_noDup : noDupCards Card.universe := by
  intro i j hi hj heq
  rw [Card.universe_length] at hi hj
  have hall : ∀ i ∈ List.range 52, ∀ j ∈ List.range 52,
      Card.universe[i]? = Card.universe[j]? → i = j := by decide
  exact hall i (List.mem_range.mpr hi) j (List.mem_range.mpr hj) heq

theorem universe_nodupP : NoDupP Card.universe :=
  noDupCards_NoDupP universe_noDup

/-- Filters of distinct lists stay distinct. -/
theorem nodupP_filter (p : Card → Bool) : ∀ {l : List Card}, NoDupP l → NoDupP (l.filter p) := by
  intro l
  induction l with
  | nil => intro _; trivial
  | cons a t ih =>
      intro hnd
      obtain ⟨ha, hndt⟩ := hnd
      by_cases hpa : p a = true
      · rw [List.filter_cons, if_pos hpa]
        exact ⟨fun hmem => ha (List.mem_filter.mp hmem).1, ih hndt⟩
      · rw [List.filter_cons, if_neg hpa]
        exact ih hndt

/-- **The bijection count**: two distinct lists with mutual inverse
maps between them have equal lengths (peel one side's head from the
other side's middle, induct). -/
theorem length_eq_of_bijection (f g : Card → Card) :
    ∀ (l₁ l₂ : List Card), NoDupP l₁ → NoDupP l₂ →
    (∀ x, x ∈ l₁ → f x ∈ l₂ ∧ g (f x) = x) →
    (∀ y, y ∈ l₂ → g y ∈ l₁ ∧ f (g y) = y) →
    l₁.length = l₂.length := by
  intro l₁
  induction l₁ with
  | nil =>
      intro l₂ _ hnd₂ _ h2
      cases l₂ with
      | nil => rfl
      | cons b t₂ =>
          obtain ⟨hgb, -⟩ := h2 b (by simp)
          exact absurd hgb (by simp)
  | cons a t ih =>
      intro l₂ hnd₁ hnd₂ h1 h2
      obtain ⟨ha, hndt⟩ := hnd₁
      obtain ⟨hfa, hgfa⟩ := h1 a (by simp)
      obtain ⟨pre, post, hsplit⟩ := mem_middle_split l₂ hfa
      have hnd₂' : NoDupP (pre ++ post) :=
        nodupP_remove _ _ _ (by rw [← hsplit]; exact hnd₂)
      have hfa' : f a ∉ pre ++ post :=
        nodupP_sub _ _ _ (by rw [← hsplit]; exact hnd₂)
      have hmem1 : ∀ x, x ∈ t → f x ∈ pre ++ post ∧ g (f x) = x := by
        intro x hx
        obtain ⟨hfx, hgfx⟩ := h1 x (List.mem_cons_of_mem a hx)
        refine ⟨?_, hgfx⟩
        have hne : f x ≠ f a := by
          intro hcon
          have hxa : x = a := by rw [← hgfx, ← hgfa, hcon]
          exact ha (hxa ▸ hx)
        have hfx2 : f x ∈ pre ++ f a :: post := by rw [← hsplit]; exact hfx
        rcases List.mem_append.mp hfx2 with h | h
        · exact List.mem_append.mpr (Or.inl h)
        · rcases List.mem_cons.mp h with h' | h'
          · exact absurd h' hne
          · exact List.mem_append.mpr (Or.inr h')
      have hmem2 : ∀ y, y ∈ pre ++ post → g y ∈ t ∧ f (g y) = y := by
        intro y hy
        have hy2 : y ∈ l₂ := by
          rw [hsplit]
          rcases List.mem_append.mp hy with h | h
          · exact List.mem_append.mpr (Or.inl h)
          · exact List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inr h)))
        obtain ⟨hgy, hfgy⟩ := h2 y hy2
        refine ⟨?_, hfgy⟩
        rcases List.mem_cons.mp hgy with h | h
        · exfalso
          have hyfa : y = f a := by rw [← hfgy, ← h]
          rw [hyfa] at hy
          exact hfa' hy
        · exact h
      have hrec := ih (pre ++ post) hndt hnd₂' hmem1 hmem2
      rw [hsplit]
      simp only [List.length_cons, List.length_append] at hrec ⊢
      omega

/-- The filter split: a filtered length is its `q`-part plus its
`¬q`-part. -/
theorem filter_split_add (p q : Card → Bool) : ∀ (l : List Card),
    (l.filter p).length =
      (l.filter fun x => p x && q x).length + (l.filter fun x => p x && !q x).length := by
  intro l
  induction l with
  | nil => rfl
  | cons a t ih =>
      cases hpa : p a with
      | true =>
          have e1 : (a :: t).filter p = a :: t.filter p := by
            rw [List.filter_cons, if_pos hpa]
          cases hqa : q a with
          | true =>
              have e2 : (a :: t).filter (fun x => p x && q x)
                  = a :: t.filter (fun x => p x && q x) := by
                rw [List.filter_cons, if_pos (by simp [hpa, hqa])]
              have e3 : (a :: t).filter (fun x => p x && !q x)
                  = t.filter (fun x => p x && !q x) := by
                rw [List.filter_cons, if_neg (by simp [hpa, hqa])]
              rw [e1, e2, e3, List.length_cons, List.length_cons]
              omega
          | false =>
              have e2 : (a :: t).filter (fun x => p x && q x)
                  = t.filter (fun x => p x && q x) := by
                rw [List.filter_cons, if_neg (by simp [hpa, hqa])]
              have e3 : (a :: t).filter (fun x => p x && !q x)
                  = a :: t.filter (fun x => p x && !q x) := by
                rw [List.filter_cons, if_pos (by simp [hpa, hqa])]
              rw [e1, e2, e3, List.length_cons, List.length_cons]
              omega
      | false =>
          have e1 : (a :: t).filter p = t.filter p := by
            rw [List.filter_cons, if_neg (by simp [hpa])]
          have e2 : (a :: t).filter (fun x => p x && q x)
              = t.filter (fun x => p x && q x) := by
            rw [List.filter_cons, if_neg (by simp [hpa])]
          have e3 : (a :: t).filter (fun x => p x && !q x)
              = t.filter (fun x => p x && !q x) := by
            rw [List.filter_cons, if_neg (by simp [hpa])]
          rw [e1, e2, e3]
          omega

/-- A filter of always-false is empty. -/
theorem filter_len_zero (p : Card → Bool) : ∀ (l : List Card),
    (∀ x, x ∈ l → p x = false) → (l.filter p).length = 0 := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons a t ih =>
      intro h
      rw [List.filter_cons, if_neg (by simp [h a (by simp)])]
      exact ih (fun x hx => h x (by simp [hx]))

/-- **The parity lemma** (no_pile §3): `uncovered = present − placed`
counts exactly the free surfaces of the type.  Each below-type card
covers a *distinct* present type-`t` card (matching injectivity), and
covering cards are exactly below-type (edge legality) — so the
difference is the free count.  Their `bm` (`get_bottom_mask`)
computes `uncovered_t > 0`.  Proof: `present = free + covered` (the
filter split), and `covered = placed` (the bijection count —
`covered ↦ its top` and `placed ↦ its base` are mutual inverses; the
top of a present card is placed by edge legality; aces have no
below-type). -/
theorem uncovered_eq_freeType {bd : Board} (hleg : bd.legalEdges) (t : Rank × Color) :
    bd.uncovered t = bd.freeType t := by
  have hsplit : (Card.universe.filter fun c => decide (c.typeOf = t) && (bd.bottomOf c).isSome).length
      = (Card.universe.filter fun c =>
          (decide (c.typeOf = t) && (bd.bottomOf c).isSome) &&
          decide (bd.topOf (Sum.inr c) = none)).length
        + (Card.universe.filter fun c =>
          (decide (c.typeOf = t) && (bd.bottomOf c).isSome) &&
          !decide (bd.topOf (Sum.inr c) = none)).length :=
    filter_split_add (fun c => decide (c.typeOf = t) && (bd.bottomOf c).isSome)
      (fun c => decide (bd.topOf (Sum.inr c) = none)) Card.universe
  show (Card.universe.filter fun c => decide (c.typeOf = t) && (bd.bottomOf c).isSome).length
      - bd.placedBelow t
      = (Card.universe.filter fun c =>
          (decide (c.typeOf = t) && (bd.bottomOf c).isSome) &&
          decide (bd.topOf (Sum.inr c) = none)).length
  cases hbt : belowType t with
  | none =>
      have hpl : bd.placedBelow t = 0 := by
        have hunf : bd.placedBelow t = match belowType t with
          | none => 0
          | some s =>
              (Card.universe.filter fun c =>
                decide (c.typeOf = s) &&
                (match bd.bottomOf c with
                 | some (Sum.inr d) => decide (d.typeOf = t) && (bd.bottomOf d).isSome
                 | _ => false)).length := rfl
        rw [hunf, hbt]
      have hcov : (Card.universe.filter fun c =>
          (decide (c.typeOf = t) && (bd.bottomOf c).isSome) &&
          !decide (bd.topOf (Sum.inr c) = none)).length = 0 := by
        refine filter_len_zero _ Card.universe ?_
        intro c _
        show ((decide (c.typeOf = t) && (bd.bottomOf c).isSome) &&
          !decide (bd.topOf (Sum.inr c) = none)) = false
        cases hp : (decide (c.typeOf = t) && (bd.bottomOf c).isSome) with
        | false => simp
        | true =>
            obtain ⟨htyc, hbot⟩ := Bool.and_eq_true_iff.mp hp
            cases hq : decide (bd.topOf (Sum.inr c) = none) with
            | true => simp
            | false =>
                exfalso
                cases hT : bd.topOf (Sum.inr c) with
                | none => rw [hT] at hq; simp at hq
                | some e =>
                    have hcs : canSitOn e c = true := hleg e c hT hbot
                    have hbr := canSitOn_belowType hcs
                    rw [of_decide_eq_true htyc] at hbr
                    rw [hbt] at hbr
                    simp at hbr
      rw [hpl]
      omega
  | some t' =>
      have hpl : bd.placedBelow t = (Card.universe.filter fun c =>
          decide (c.typeOf = t') && (match bd.bottomOf c with
            | some (Sum.inr d) => decide (d.typeOf = t) && (bd.bottomOf d).isSome
            | _ => false)).length := by
        have hunf : bd.placedBelow t = match belowType t with
          | none => 0
          | some s =>
              (Card.universe.filter fun c =>
                decide (c.typeOf = s) &&
                (match bd.bottomOf c with
                 | some (Sum.inr d) => decide (d.typeOf = t) && (bd.bottomOf d).isSome
                 | _ => false)).length := rfl
        rw [hunf, hbt]
      have hbij : (Card.universe.filter fun c =>
          (decide (c.typeOf = t) && (bd.bottomOf c).isSome) &&
          !decide (bd.topOf (Sum.inr c) = none)).length
          = (Card.universe.filter fun c =>
          decide (c.typeOf = t') && (match bd.bottomOf c with
            | some (Sum.inr d) => decide (d.typeOf = t) && (bd.bottomOf d).isSome
            | _ => false)).length := by
        refine length_eq_of_bijection
          (fun c => match bd.topOf (Sum.inr c) with | some e => e | none => c)
          (fun e => match bd.bottomOf e with | some (Sum.inr d) => d | _ => e)
          _ _ (nodupP_filter _ universe_nodupP) (nodupP_filter _ universe_nodupP) ?_ ?_
        · intro x hx
          rw [List.mem_filter] at hx
          obtain ⟨hu, hp⟩ := hx
          have hp' : ((decide (x.typeOf = t) && (bd.bottomOf x).isSome) &&
              !decide (bd.topOf (Sum.inr x) = none)) = true := hp
          obtain ⟨hpres, hnq⟩ := Bool.and_eq_true_iff.mp hp'
          obtain ⟨htyc, hbot⟩ := Bool.and_eq_true_iff.mp hpres
          cases hT : bd.topOf (Sum.inr x) with
          | none => rw [hT] at hnq; simp at hnq
          | some e =>
              have hbe : bd.bottomOf e = some (Sum.inr x) :=
                (Board.bottomOf_eq bd e (Sum.inr x)).mpr hT
              have hcs : canSitOn e x = true := hleg e x hT hbot
              have hbr := canSitOn_belowType hcs
              rw [of_decide_eq_true htyc] at hbr
              rw [hbt] at hbr
              have htye : e.typeOf = t' := (Option.some.inj hbr).symm
              simp only [hT]
              refine ⟨List.mem_filter.mpr ⟨e.mem_universe, ?_⟩, ?_⟩
              · show (decide (e.typeOf = t') && (match bd.bottomOf e with
                    | some (Sum.inr d) => decide (d.typeOf = t) && (bd.bottomOf d).isSome
                    | _ => false)) = true
                refine Bool.and_eq_true_iff.mpr ⟨decide_eq_true htye, ?_⟩
                rw [hbe]
                exact Bool.and_eq_true_iff.mpr ⟨htyc, hbot⟩
              · rw [hbe]
        · intro y hy
          rw [List.mem_filter] at hy
          obtain ⟨hu, hp⟩ := hy
          have hp' : (decide (y.typeOf = t') && (match bd.bottomOf y with
              | some (Sum.inr d) => decide (d.typeOf = t) && (bd.bottomOf d).isSome
              | _ => false)) = true := hp
          obtain ⟨htye, hmatch⟩ := Bool.and_eq_true_iff.mp hp'
          cases hb : bd.bottomOf y with
          | none => rw [hb] at hmatch; simp at hmatch
          | some b =>
              cases b with
              | inl a => rw [hb] at hmatch; simp at hmatch
              | inr d =>
                  have hinner : (decide (d.typeOf = t) && (bd.bottomOf d).isSome) = true := by
                    rw [hb] at hmatch; exact hmatch
                  obtain ⟨htyd, hpresd⟩ := Bool.and_eq_true_iff.mp hinner
                  have hT : bd.topOf (Sum.inr d) = some y :=
                    (Board.bottomOf_eq bd y (Sum.inr d)).mp hb
                  simp only [hb]
                  refine ⟨List.mem_filter.mpr ⟨d.mem_universe, ?_⟩, ?_⟩
                  · show ((decide (d.typeOf = t) && (bd.bottomOf d).isSome) &&
                      !decide (bd.topOf (Sum.inr d) = none)) = true
                    refine Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨htyd, hpresd⟩, ?_⟩
                    rw [hT]
                    rfl
                  · rw [hT]
      rw [hpl]
      omega

/-! ## Realizability -/

/-- A board *fits* a deal/depths: the edge legality of the WF third
conjunct, lifted to boards (dealt-adjacent stack or fitting visible
card). -/
def Board.Fits (bd : Board) (deal : Deal) (depths : Anchor → Nat) : Prop :=
  ∀ b c, bd.topOf b = some c →
    match b with
    | Sum.inl a => c.rank = Rank.king ∨ (deal.piles a).head? = some c
    | Sum.inr d =>
      (∃ a t rest, deal.piles a = t ++ d :: c :: rest) ∨
      ((bd.bottomOf d).isSome = true ∧ canSitOn c d)

/-- **Realizability**: some fitting matching has exactly this visible
set — the invariant that makes the engine's abstraction truthful. -/
def Realizable (deal : Deal) (depths : Anchor → Nat) (vis : Card → Bool) : Prop :=
  ∃ bd : Board, bd.Fits deal depths ∧ ∀ c, (bd.bottomOf c).isSome = vis c

/-- Model states are realizable (their abstract content is truthful). -/
theorem realizable_of_wf {st : State} (hwf : st.WF) :
    Realizable st.deal st.depths (fun c => st.isVis c) := by
  obtain ⟨_, _, hmatch, _⟩ := hwf
  refine ⟨st.board, ?_, fun _ => rfl⟩
  intro b c hb
  exact (hmatch _ _ hb).2

/-- **B1's preservation** (no_pile §3's maintenance table): moves keep
the abstract data realizable — each generator guard is precisely the
witness requirement.  Model side this is `apply_wf`'s shadow; the
engine side (the `bm` XOR algebra computing `uncovered_t > 0` from the
tracked masks) belongs to the bridge milestone. -/
theorem apply_realizable {st st' : State} (hwf : st.WF) {m : Move}
    (h : st.apply m = some st') :
    Realizable st'.deal st'.depths (fun c => st'.isVis c) :=
  realizable_of_wf (apply_wf hwf m st' h)
