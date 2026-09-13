import Klondike.Move

/-!
# The theorem farm — formalized, proofs pending

The statement layer for the results beyond the kernel: the relabeling
group (T's generalization), the reversibility/commitment structure
(their Lemma A1), the commutation schema (C-IND / C13), and the
structural acyclicity of the matching.  Every proof is `sorry` with a
`TODO(proof)`; every definition is final code.
-/

/-! ## 1. The relabeling group — T, generalized

The tableau rules see only `(rank, color)`, so the symmetry group acts
on the *suit coordinate*: each color's two suits may be exchanged and
the two colors may be swapped — 8 elements.  Twin swap (T) is the
element flipping both colors' pairs simultaneously.
-/

/-- A suit-level relabeling preserving the color partition, with its
inverse as data. -/
structure Relabel where
  /-- The suit relabeling. -/
  suit : Suit → Suit
  /-- Its inverse. -/
  suitInv : Suit → Suit
  left_inv : ∀ s, suitInv (suit s) = s
  right_inv : ∀ s, suit (suitInv s) = s
  /-- Color coherence: different colors stay different, so `canSitOn`
  is preserved. -/
  coherent : ∀ s s', (suit s).color ≠ (suit s').color ↔ s.color ≠ s'.color

/-- The induced card relabeling (rank-preserving by construction). -/
def Relabel.card (r : Relabel) : Card → Card := fun c => ⟨r.suit c.suit, c.rank⟩

/-- The induced base relabeling. -/
def Relabel.onBase (r : Relabel) : Base → Base := Sum.map id r.card

/-- The twin swap as a relabeling. -/
def Relabel.twin : Relabel where
  suit := Suit.flipPair
  suitInv := Suit.flipPair
  left_inv := Suit.flipPair_flipPair
  right_inv := Suit.flipPair_flipPair
  coherent := by
    intro s s'
    simp

/-- The inverse card relabeling (conjugation's backward probe). -/
def Relabel.cardInv (r : Relabel) : Card → Card := fun c => ⟨r.suitInv c.suit, c.rank⟩

theorem Relabel.cardInv_card (r : Relabel) (c : Card) : r.cardInv (r.card c) = c := by
  show ⟨r.suitInv (r.suit c.suit), c.rank⟩ = c
  rw [r.left_inv c.suit]

theorem Relabel.cardInv_inj (r : Relabel) {b₁ b₂ : Base}
    (h : Sum.map id r.cardInv b₁ = Sum.map id r.cardInv b₂) : b₁ = b₂ := by
  cases b₁ with
  | inl a₁ =>
      cases b₂ with
      | inl a₂ => exact congrArg Sum.inl (by simpa using h)
      | inr x₂ => exact absurd h (by simp)
  | inr x₁ =>
      cases b₂ with
      | inl a₂ => exact absurd h (by simp)
      | inr x₂ =>
          have hinj : r.cardInv x₁ = r.cardInv x₂ := by simpa using h
          obtain ⟨hs, hr⟩ := Card.mk.inj hinj
          have hsi : x₁.suit = x₂.suit := by
            have e1 := r.right_inv x₁.suit
            rw [hs] at e1
            exact e1.symm.trans (r.right_inv x₂.suit)
          cases x₁ with
          | mk s₁ rk₁ =>
              cases x₂ with
              | mk s₂ rk₂ =>
                  have hsi' : s₁ = s₂ := hsi
                  have hr' : rk₁ = rk₂ := hr
                  rw [hsi', hr']

/-- Conjugation preserves the matching law (standalone lemma —
`by`-blocks do not parse inside structure instances). -/
theorem Relabel.relabelBy_inj (r : Relabel) (st : State) :
    ∀ (b₁ b₂ : Base) (c : Card),
      (fun b => (st.board.topOf (Sum.map id r.cardInv b)).map r.card) b₁ = some c →
      (fun b => (st.board.topOf (Sum.map id r.cardInv b)).map r.card) b₂ = some c →
      b₁ = b₂ := by
  intro b₁ b₂ c h₁ h₂
  obtain ⟨c₁, hc₁, hc₁'⟩ := Option.map_eq_some_iff.mp h₁
  obtain ⟨c₂, hc₂, hc₂'⟩ := Option.map_eq_some_iff.mp h₂
  have hcc : c₁ = c₂ := by
    have hcard : r.card c₁ = r.card c₂ := hc₁'.trans hc₂'.symm
    obtain ⟨hs, hr⟩ := Card.mk.inj hcard
    have hsi : c₁.suit = c₂.suit := by
      have e1 := r.left_inv c₁.suit
      rw [hs] at e1
      exact e1.symm.trans (r.left_inv c₂.suit)
    cases c₁ with
    | mk s₁ rk₁ =>
        cases c₂ with
        | mk s₂ rk₂ =>
            have hsi' : s₁ = s₂ := hsi
            have hr' : rk₁ = rk₂ := hr
            rw [hsi', hr']
  subst hcc
  exact r.cardInv_inj (st.board.inj _ _ _ hc₁ hc₂)

/-- Conjugate a whole state by a relabeling (T's action, generalized).
The board probes at the *inverse* relabeled base — the conjugation
direction: the relabeled move `pileStack (r.card c)` guards at
`inr (r.card c)`, which must read off `st`'s guard at `c`, and
`cardInv ∘ card = id` is what makes it so; probing at `r.card`
instead breaks conjugation for the group's non-involutive elements
(the suit 4-cycles). -/
def State.relabelBy (r : Relabel) (st : State) : State :=
  { st with
    deal := { piles := fun a => (st.deal.piles a).map r.card,
              stock := st.deal.stock.map r.card },
    board := { topOf := fun b => (st.board.topOf (Sum.map id r.cardInv b)).map r.card,
               inj := Relabel.relabelBy_inj r st },
    heights := fun s => st.heights (r.suitInv s),
    stock := { cards := st.stock.cards.map r.card, cursor := st.stock.cursor } }

/-- Relabel a move. -/
def Move.relabel (r : Relabel) : Move → Move
  | .draw => .draw
  | .reveal c => .reveal (r.card c)
  | .deckPile c b => .deckPile (r.card c) (r.onBase b)
  | .deckStack c => .deckStack (r.card c)
  | .pileStack c => .pileStack (r.card c)
  | .stackPile c b => .stackPile (r.card c) (r.onBase b)
  | .pilePile c b => .pilePile (r.card c) (r.onBase b)

/-! ### The relabeling transfer kit

Every derived view of a relabeled state is the relabeled view: the
guards translate through `cardInv` (the conjugation direction), the
board/stock/cycle views commute with their relabelings, and the
move-successors relabel componentwise (`relabelBy_with`). -/

theorem decide_congr {p q : Prop} [Decidable p] [Decidable q] (h : p ↔ q) : decide p = decide q := by
  cases hp : decide p with
  | true => rw [decide_eq_true (h.mp (of_decide_eq_true hp))]
  | false =>
      cases hq : decide q with
      | true =>
          exfalso
          rw [decide_eq_true (h.mpr (of_decide_eq_true hq))] at hp
          simp at hp
      | false => rfl

theorem findFirst_congr {α : Type} {p q : α → Bool} (h : ∀ a, p a = q a) :
    ∀ (l : List α), findFirst p l = findFirst q l := by
  intro l
  induction l with
  | nil => rfl
  | cons a t ih =>
      simp only [findFirst_cons, h a]
      split
      · rfl
      · exact ih

theorem Relabel.card_inj (r : Relabel) {x y : Card} (h : r.card x = r.card y) : x = y := by
  have h1 := congrArg r.cardInv h
  rw [Relabel.cardInv_card, Relabel.cardInv_card] at h1
  exact h1

theorem Relabel.card_cardInv (r : Relabel) (c : Card) : r.card (r.cardInv c) = c :=
  congrArg (fun s => Card.mk s c.rank) (r.right_inv c.suit)

theorem Relabel.suitInv_eq (r : Relabel) {s t : Suit} : r.suitInv s = t ↔ s = r.suit t := by
  constructor
  · intro h
    have e := congrArg r.suit h
    rw [r.right_inv s] at e
    exact e
  · intro h
    have e := congrArg r.suitInv h
    rw [r.left_inv t] at e
    exact e

theorem Relabel.cardInv_onBase (r : Relabel) : ∀ (b : Base),
    Sum.map id r.cardInv (r.onBase b) = b
  | Sum.inl _ => rfl
  | Sum.inr c => congrArg Sum.inr (r.cardInv_card c)

theorem Relabel.onBase_cardInv (r : Relabel) : ∀ (b : Base),
    r.onBase (Sum.map id r.cardInv b) = b
  | Sum.inl _ => rfl
  | Sum.inr x => congrArg Sum.inr (r.card_cardInv x)

theorem Relabel.onBase_inj (r : Relabel) {b₁ b₂ : Base} (h : r.onBase b₁ = r.onBase b₂) :
    b₁ = b₂ := by
  have e1 := congrArg (Sum.map id r.cardInv) h
  rw [Relabel.cardInv_onBase r b₁, Relabel.cardInv_onBase r b₂] at e1
  exact e1

theorem canSitOn_relabel (r : Relabel) (c d : Card) :
    canSitOn (r.card c) (r.card d) = canSitOn c d := by
  show (decide (c.rank.toIdx + 1 = d.rank.toIdx)
        && decide ((r.suit c.suit).color ≠ (r.suit d.suit).color))
    = (decide (c.rank.toIdx + 1 = d.rank.toIdx) && decide (c.suit.color ≠ d.suit.color))
  rw [decide_congr (r.coherent c.suit d.suit)]

/-- The relabeled stock cycle. -/
def relabelCycle (r : Relabel) (cy : Cycle Card) : Cycle Card :=
  { cards := cy.cards.map r.card, cursor := cy.cursor }

theorem relabelBoard_inj (r : Relabel) (bd : Board) :
    ∀ (b₁ b₂ : Base) (c : Card),
      (fun b => (bd.topOf (Sum.map id r.cardInv b)).map r.card) b₁ = some c →
      (fun b => (bd.topOf (Sum.map id r.cardInv b)).map r.card) b₂ = some c →
      b₁ = b₂ := by
  intro b₁ b₂ c h₁ h₂
  obtain ⟨c₁, hc₁, hc₁'⟩ := Option.map_eq_some_iff.mp h₁
  obtain ⟨c₂, hc₂, hc₂'⟩ := Option.map_eq_some_iff.mp h₂
  have hcc : c₁ = c₂ := by
    have hcard : r.card c₁ = r.card c₂ := hc₁'.trans hc₂'.symm
    obtain ⟨hs, hr⟩ := Card.mk.inj hcard
    have hsi : c₁.suit = c₂.suit := by
      have e1 := r.left_inv c₁.suit
      rw [hs] at e1
      exact e1.symm.trans (r.left_inv c₂.suit)
    cases c₁ with
    | mk s₁ rk₁ =>
        cases c₂ with
        | mk s₂ rk₂ =>
            have hsi' : s₁ = s₂ := hsi
            have hr' : rk₁ = rk₂ := hr
            rw [hsi', hr']
  subst hcc
  exact r.cardInv_inj (bd.inj _ _ _ hc₁ hc₂)

/-- The relabeled board (the same shape `State.relabelBy` builds). -/
def relabelBoard (r : Relabel) (bd : Board) : Board where
  topOf := fun b => (bd.topOf (Sum.map id r.cardInv b)).map r.card
  inj := relabelBoard_inj r bd

theorem relabelBoard_topOf (r : Relabel) (bd : Board) (b : Base) :
    (relabelBoard r bd).topOf (r.onBase b) = (bd.topOf b).map r.card := by
  show (bd.topOf (Sum.map id r.cardInv (r.onBase b))).map r.card = (bd.topOf b).map r.card
  rw [Relabel.cardInv_onBase r b]

theorem relabelBy_topOf (r : Relabel) (st : State) (b : Base) :
    (st.relabelBy r).board.topOf (r.onBase b) = (st.board.topOf b).map r.card :=
  relabelBoard_topOf r st.board b

theorem relabelBy_topOf_inr (r : Relabel) (st : State) (c : Card) :
    (st.relabelBy r).board.topOf (Sum.inr (r.card c)) = (st.board.topOf (Sum.inr c)).map r.card :=
  relabelBy_topOf r st (Sum.inr c)

theorem relabelBy_topOf_inl (r : Relabel) (st : State) (a : Anchor) :
    (st.relabelBy r).board.topOf (Sum.inl a) = (st.board.topOf (Sum.inl a)).map r.card :=
  relabelBy_topOf r st (Sum.inl a)

theorem relabelBoard_bottomOf (r : Relabel) (bd : Board) (c : Card) :
    (relabelBoard r bd).bottomOf c = (bd.bottomOf (r.cardInv c)).map r.onBase := by
  cases hb : bd.bottomOf (r.cardInv c) with
  | none =>
      show (relabelBoard r bd).bottomOf c = none
      refine (Board.bottomOf_eq_none _ _).mpr (fun b' hb'' => ?_)
      have hbr : (relabelBoard r bd).topOf b'
          = (bd.topOf (Sum.map id r.cardInv b')).map r.card := rfl
      rw [hbr] at hb''
      obtain ⟨x, hx, hx'⟩ := Option.map_eq_some_iff.mp hb''
      have hxc : x = r.cardInv c := Relabel.card_inj r (hx'.trans (Relabel.card_cardInv r c).symm)
      rw [hxc] at hx
      exact (Board.bottomOf_eq_none bd (r.cardInv c)).mp hb (Sum.map id r.cardInv b') hx
  | some b =>
      show (relabelBoard r bd).bottomOf c = some (r.onBase b)
      exact (Board.bottomOf_eq _ _ _).mpr (by
        rw [relabelBoard_topOf r bd b, (Board.bottomOf_eq bd (r.cardInv c) b).mp hb,
          Option.map_some]
        exact congrArg some (Relabel.card_cardInv r c))

theorem relabelBy_bottomOf (r : Relabel) (st : State) (c : Card) :
    (st.relabelBy r).board.bottomOf c = (st.board.bottomOf (r.cardInv c)).map r.onBase :=
  relabelBoard_bottomOf r st.board c

theorem relabelBy_bottomOf_card (r : Relabel) (st : State) (c : Card) :
    (st.relabelBy r).board.bottomOf (r.card c) = (st.board.bottomOf c).map r.onBase := by
  rw [relabelBy_bottomOf, Relabel.cardInv_card]

theorem relabelBy_heights (r : Relabel) (st : State) (c : Card) :
    (st.relabelBy r).heights (r.card c).suit = st.heights c.suit :=
  congrArg st.heights (r.left_inv c.suit)

theorem relabelBy_hidden (r : Relabel) (st : State) (a : Anchor) :
    (st.relabelBy r).hidden a = (st.hidden a).map r.card := by
  show ((st.deal.piles a).map r.card).take (st.depths a)
    = ((st.deal.piles a).take (st.depths a)).map r.card
  rw [← List.map_take]

theorem relabelBy_topHidden (r : Relabel) (st : State) (a : Anchor) :
    (st.relabelBy r).topHidden a = (st.topHidden a).map r.card := by
  show ((st.relabelBy r).hidden a).getLast? = ((st.hidden a).getLast?).map r.card
  rw [relabelBy_hidden, List.getLast?_map]

theorem relabelBy_pileOfTopHidden (r : Relabel) (st : State) (c : Card) :
    (st.relabelBy r).pileOfTopHidden c = st.pileOfTopHidden (r.cardInv c) := by
  show findFirst (fun a => decide ((st.relabelBy r).topHidden a = some c)) Anchor.all
     = findFirst (fun a => decide (st.topHidden a = some (r.cardInv c))) Anchor.all
  exact findFirst_congr (fun a => by
    show decide ((st.relabelBy r).topHidden a = some c)
      = decide (st.topHidden a = some (r.cardInv c))
    rw [relabelBy_topHidden r st a]
    cases hst : st.topHidden a with
    | none => rfl
    | some x =>
        refine decide_congr ?_
        constructor
        · intro h
          have h' : some (r.card x) = some c := h
          have h1 : r.card x = c := Option.some.inj h'
          have h2 : x = r.cardInv c :=
            Relabel.card_inj r (h1.trans (Relabel.card_cardInv r c).symm)
          rw [h2]
        · intro h
          have h1 : x = r.cardInv c := Option.some.inj h
          show some (r.card x) = some c
          rw [h1, Relabel.card_cardInv r c]) Anchor.all

theorem relabelBy_hiddenBase (r : Relabel) (st : State) (a : Anchor) :
    (st.relabelBy r).hiddenBase a = r.onBase (st.hiddenBase a) := by
  show (match (((st.relabelBy r).hidden a).reverse.drop 1).head? with
        | some d => Sum.inr d
        | none => Sum.inl a)
    = r.onBase (match ((st.hidden a).reverse.drop 1).head? with
        | some d => Sum.inr d
        | none => Sum.inl a)
  rw [relabelBy_hidden, ← List.map_reverse, ← List.map_drop, List.head?_map]
  cases ((st.hidden a).reverse.drop 1).head? with
  | none => rfl
  | some d => rfl

theorem relabelBoard_attach (r : Relabel) (bd : Board) {b : Base} {c : Card} {bd' : Board}
    (h : bd.attach b c = some bd') :
    (relabelBoard r bd).attach (r.onBase b) (r.card c) = some (relabelBoard r bd') := by
  have hne : bd.attach b c ≠ none := by rw [h]; simp
  obtain ⟨htop, hbot⟩ := (Board.attach_eq_some_iff bd b c).mp hne
  have htopR : (relabelBoard r bd).topOf (r.onBase b) = none := by
    rw [relabelBoard_topOf r bd b, htop]
    rfl
  have hbotR : (relabelBoard r bd).bottomOf (r.card c) = none := by
    rw [relabelBoard_bottomOf r bd (r.card c), Relabel.cardInv_card, hbot]
    rfl
  have hneR : (relabelBoard r bd).attach (r.onBase b) (r.card c) ≠ none :=
    Board.attach_eq_some_iff _ _ _ |>.mpr ⟨htopR, hbotR⟩
  cases hR : (relabelBoard r bd).attach (r.onBase b) (r.card c) with
  | none =>
      rw [hR] at hneR
      simp at hneR
  | some bdR =>
      rw [Option.some.injEq]
      refine Board.ext_topOf (funext (fun b'' => ?_))
      by_cases hbb : b'' = r.onBase b
      · rw [hbb]
        show bdR.topOf (r.onBase b)
          = (bd'.topOf (Sum.map id r.cardInv (r.onBase b))).map r.card
        rw [Board.attach_topOf _ _ _ hR, Relabel.cardInv_onBase r b, Board.attach_topOf _ _ _ h]
        rfl
      · show bdR.topOf b'' = (bd'.topOf (Sum.map id r.cardInv b'')).map r.card
        rw [Board.attach_topOf_ne _ _ _ hR hbb]
        have hcb : Sum.map id r.cardInv b'' ≠ b := fun hcon => hbb (by
          have hc2 := Relabel.onBase_cardInv r b''
          rw [hcon] at hc2
          exact hc2.symm)
        rw [Board.attach_topOf_ne _ _ _ h hcb]
        rfl

theorem relabelBoard_detach (r : Relabel) (bd : Board) (b : Base) :
    (relabelBoard r bd).detach (r.onBase b) = relabelBoard r (bd.detach b) := by
  refine Board.ext_topOf (funext (fun b'' => ?_))
  by_cases hbb : b'' = r.onBase b
  · rw [hbb]
    show (if r.onBase b = r.onBase b then none else (relabelBoard r bd).topOf (r.onBase b))
      = ((bd.detach b).topOf (Sum.map id r.cardInv (r.onBase b))).map r.card
    rw [if_pos rfl, Relabel.cardInv_onBase r b, Board.detach_topOf]
    rfl
  · show (if b'' = r.onBase b then none else (relabelBoard r bd).topOf b'')
      = ((bd.detach b).topOf (Sum.map id r.cardInv b'')).map r.card
    have hcb : Sum.map id r.cardInv b'' ≠ b := fun hcon => hbb (by
      have hc2 := Relabel.onBase_cardInv r b''
      rw [hcon] at hc2
      exact hc2.symm)
    rw [if_neg hbb, Board.detach_topOf_ne _ _ _ hcb]
    rfl

theorem relabelBy_isVis (r : Relabel) (st : State) (d : Card) :
    (st.relabelBy r).isVis (r.card d) = st.isVis d := by
  simp only [State.isVis]
  rw [relabelBy_bottomOf_card r st d]
  cases st.board.bottomOf d with
  | none => rfl
  | some b => rfl

theorem relabelBy_canPlace (r : Relabel) (st : State) (c : Card) (b : Base) :
    (st.relabelBy r).canPlace (r.card c) (r.onBase b) = st.canPlace c b := by
  cases b with
  | inl a =>
      show (decide ((st.relabelBy r).board.topOf (Sum.inl a) = none)
            && decide ((r.card c).rank = Rank.king))
        = (decide (st.board.topOf (Sum.inl a) = none) && decide (c.rank = Rank.king))
      rw [relabelBy_topOf_inl r st a]
      cases st.board.topOf (Sum.inl a) with
      | none => rfl
      | some x => rfl
  | inr d =>
      show (decide ((st.relabelBy r).board.topOf (Sum.inr (r.card d)) = none)
              && ((st.relabelBy r).isVis (r.card d) && canSitOn (r.card c) (r.card d)))
        = (decide (st.board.topOf (Sum.inr d) = none) && (st.isVis d && canSitOn c d))
      rw [relabelBy_topOf_inr r st d, relabelBy_isVis r st d, canSitOn_relabel]
      cases st.board.topOf (Sum.inr d) with
      | none => rfl
      | some x => rfl

theorem beq_relabel (r : Relabel) (x y : Card) : (r.card x == r.card y) = (x == y) := by
  by_cases hxy : x = y
  · rw [hxy]
    rw [show ((r.card y == r.card y)) = true from decide_eq_true rfl,
        show ((y == y)) = true from decide_eq_true rfl]
  · have h1 : (r.card x == r.card y) = false := by
      cases hb : (r.card x == r.card y) with
      | true => exact absurd (Relabel.card_inj r (of_decide_eq_true hb)) hxy
      | false => rfl
    have h2 : (x == y) = false := by
      cases hb : (x == y) with
      | true => exact absurd (of_decide_eq_true hb) hxy
      | false => rfl
    rw [h1, h2]

theorem contains_map (r : Relabel) : ∀ (l : List Card) (x : Card),
    (l.map r.card).contains (r.card x) = l.contains x := by
  intro l
  induction l with
  | nil => intro x; rfl
  | cons a t ih =>
      intro x
      show ((r.card x == r.card a) || (t.map r.card).contains (r.card x))
        = (x == a || t.contains x)
      rw [ih x, beq_relabel r x a]

theorem aboveOf_go_succ (bd : Board) (fuel : Nat) (b : Base) (acc : List Card) :
    Board.aboveOf.go bd (fuel + 1) b acc
      = match bd.topOf b with
        | none => acc
        | some c' => if acc.contains c' then acc
                     else Board.aboveOf.go bd fuel (Sum.inr c') (c' :: acc) := rfl

theorem relabelBy_aboveOf_go (r : Relabel) (st : State) : ∀ (fuel : Nat) (b : Base)
    (acc : List Card),
    Board.aboveOf.go (st.relabelBy r).board fuel (r.onBase b) (acc.map r.card)
    = (Board.aboveOf.go st.board fuel b acc).map r.card := by
  intro fuel
  induction fuel with
  | zero => intro b acc; rfl
  | succ n ih =>
      intro b acc
      rw [aboveOf_go_succ, aboveOf_go_succ, relabelBy_topOf r st b]
      cases hb : st.board.topOf b with
      | none => rfl
      | some x =>
          show (if (acc.map r.card).contains (r.card x) then acc.map r.card
                else Board.aboveOf.go (st.relabelBy r).board n (Sum.inr (r.card x))
                  (r.card x :: acc.map r.card))
            = (if acc.contains x then acc
               else Board.aboveOf.go st.board n (Sum.inr x) (x :: acc)).map r.card
          rw [contains_map r acc x]
          by_cases hac : acc.contains x = true
          · rw [if_pos hac, if_pos hac]
          · rw [if_neg hac, if_neg hac]
            exact ih (Sum.inr x) (x :: acc)

theorem relabelBy_aboveOf (r : Relabel) (st : State) (c : Card) :
    (st.relabelBy r).board.aboveOf (r.card c) = (st.board.aboveOf c).map r.card :=
  relabelBy_aboveOf_go r st 52 (Sum.inr c) []

theorem relabelBy_canMoveRun (r : Relabel) (st : State) (c : Card) (b : Base) :
    (st.relabelBy r).canMoveRun (r.card c) (r.onBase b) = st.canMoveRun c b := by
  cases b with
  | inl a =>
      show ((st.relabelBy r).canPlace (r.card c) (r.onBase (Sum.inl a)) && true)
        = (st.canPlace c (Sum.inl a) && true)
      rw [relabelBy_canPlace r st c (Sum.inl a)]
  | inr d =>
      show ((st.relabelBy r).canPlace (r.card c) (r.onBase (Sum.inr d))
            && !((st.relabelBy r).board.aboveOf (r.card c)).contains (r.card d))
        = (st.canPlace c (Sum.inr d) && !(st.board.aboveOf c).contains d)
      rw [relabelBy_canPlace r st c (Sum.inr d), relabelBy_aboveOf r st c, contains_map r]

theorem relabelCycle_dealOnce (r : Relabel) (cy : Cycle Card) (s : Nat) :
    (relabelCycle r cy).dealOnce s = relabelCycle r (cy.dealOnce s) := by
  show (if cy.cursor ≥ (cy.cards.map r.card).length
        then { cards := cy.cards.map r.card, cursor := 0 }
        else { cards := cy.cards.map r.card,
               cursor := min (cy.cursor + s) (cy.cards.map r.card).length } : Cycle Card)
    = { cards := (cy.dealOnce s).cards.map r.card, cursor := (cy.dealOnce s).cursor }
  simp only [List.length_map]
  split
  · rename_i h
    simp only [Cycle.dealOnce]
    rw [if_pos h]
  · rename_i h
    simp only [Cycle.dealOnce]
    rw [if_neg h]

theorem relabelBy_prev (r : Relabel) (st : State) :
    (st.relabelBy r).stock.prev = st.stock.prev.map r.card := by
  show (if st.stock.cursor = 0 then none else (st.stock.cards.map r.card)[st.stock.cursor - 1]?)
    = (if st.stock.cursor = 0 then none else st.stock.cards[st.stock.cursor - 1]?).map r.card
  by_cases h0 : st.stock.cursor = 0
  · rw [if_pos h0, if_pos h0]
    rfl
  · rw [if_neg h0, if_neg h0, List.getElem?_map]

theorem removeIdx_map (r : Relabel) : ∀ (l : List Card) (i : Nat),
    Cycle.removeIdx (l.map r.card) i = (Cycle.removeIdx l i).map r.card
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | h :: t, i + 1 => congrArg (fun x => r.card h :: x) (removeIdx_map r t i)

theorem relabelBy_removeAt (r : Relabel) (st : State) (i : Nat) :
    (st.relabelBy r).stock.removeAt i = relabelCycle r (st.stock.removeAt i) := by
  rw [show (st.relabelBy r).stock.removeAt i
      = { cards := Cycle.removeIdx (st.stock.cards.map r.card) i,
          cursor := if i < st.stock.cursor then st.stock.cursor - 1 else st.stock.cursor }
      from rfl,
    removeIdx_map]
  rfl

theorem relabelBy_stock_cursor (r : Relabel) (st : State) :
    (st.relabelBy r).stock.cursor = st.stock.cursor := rfl

/-- Successors relabel componentwise (the arm-assembly workhorse). -/
theorem relabelBy_with (r : Relabel) (st : State) (bd : Board) (hs : Suit → Nat)
    (dpt : Anchor → Nat) (cy : Cycle Card) :
    ({ st with board := bd, heights := hs, depths := dpt, stock := cy }).relabelBy r
    = { st.relabelBy r with
        board := relabelBoard r bd,
        heights := fun s => hs (r.suitInv s),
        depths := dpt,
        stock := relabelCycle r cy } := rfl

theorem relabelBy_heights_bump (r : Relabel) (st : State) (c : Card) :
    (fun s => if s = (r.card c).suit then (st.relabelBy r).heights s + 1
      else (st.relabelBy r).heights s)
    = (fun s => if r.suitInv s = c.suit then st.heights (r.suitInv s) + 1
      else st.heights (r.suitInv s)) := by
  funext s
  by_cases hs : r.suitInv s = c.suit
  · have hsc : s = (r.card c).suit := (Relabel.suitInv_eq r).mp hs
    rw [if_pos hsc, if_pos hs]
    rfl
  · have hsc : s ≠ (r.card c).suit := fun hcon => hs ((Relabel.suitInv_eq r).mpr hcon)
    rw [if_neg hsc, if_neg hs]
    rfl

theorem relabelBy_heights_drop (r : Relabel) (st : State) (c : Card) :
    (fun s => if s = (r.card c).suit then (st.relabelBy r).heights s - 1
      else (st.relabelBy r).heights s)
    = (fun s => if r.suitInv s = c.suit then st.heights (r.suitInv s) - 1
      else st.heights (r.suitInv s)) := by
  funext s
  by_cases hs : r.suitInv s = c.suit
  · have hsc : s = (r.card c).suit := (Relabel.suitInv_eq r).mp hs
    rw [if_pos hsc, if_pos hs]
    rfl
  · have hsc : s ≠ (r.card c).suit := fun hcon => hs ((Relabel.suitInv_eq r).mpr hcon)
    rw [if_neg hsc, if_neg hs]
    rfl

/-- **T's conjugation step, generalized**: applying a relabeled move
to the relabeled state is applying the move to the state, relabeled. -/
theorem apply_relabel (r : Relabel) (m : Move) (st : State) :
    (st.relabelBy r).apply (m.relabel r) = (st.apply m).map (State.relabelBy r) := by
  cases m with
  | draw =>
      show some { st.relabelBy r with stock := (st.relabelBy r).stock.dealOnce st.drawStep }
        = some (({ st with stock := st.stock.dealOnce st.drawStep }).relabelBy r)
      have hstock : (st.relabelBy r).stock = relabelCycle r st.stock := rfl
      rw [hstock, relabelCycle_dealOnce r st.stock st.drawStep]
      exact congrArg some (relabelBy_with r st st.board st.heights st.depths
        (st.stock.dealOnce st.drawStep)).symm
  | reveal c =>
      show (st.relabelBy r).apply (Move.reveal (r.card c))
        = (st.apply (Move.reveal c)).map (State.relabelBy r)
      cases hst : st.apply (Move.reveal c) with
      | none =>
          show (st.relabelBy r).apply (Move.reveal (r.card c)) = none
          cases hR : (st.relabelBy r).apply (Move.reveal (r.card c)) with
          | none => rfl
          | some st'' =>
              exfalso
              rw [apply_reveal_iff] at hR
              obtain ⟨htR, r', a, bdR, hbotR, hpileR, hattR, -⟩ := hR
              have htop : st.board.topOf (Sum.inr c) = none := by
                rw [relabelBy_topOf_inr r st c] at htR
                exact Option.map_eq_none_iff.mp htR
              have hbot : st.board.bottomOf c = some (Sum.inr (r.cardInv r')) := by
                rw [relabelBy_bottomOf_card r st c] at hbotR
                obtain ⟨b₀, hx, hx'⟩ := Option.map_eq_some_iff.mp hbotR
                cases b₀ with
                | inl aa =>
                    have hx'' : Sum.inl aa = Sum.inr r' := hx'
                    exact absurd hx'' (by simp)
                | inr y =>
                    have hcy : r.card y = r' := Sum.inr.inj hx'
                    have hyc : y = r.cardInv r' :=
                      Relabel.card_inj r (hcy.trans (Relabel.card_cardInv r r').symm)
                    rw [hyc] at hx
                    exact hx
              have hpile : st.pileOfTopHidden (r.cardInv r') = some a := by
                rw [relabelBy_pileOfTopHidden r st r'] at hpileR
                exact hpileR
              rw [relabelBy_hiddenBase r st a] at hattR
              obtain ⟨htopR2, hbotR2⟩ := (Board.attach_eq_some_iff _ _ _).mp (by rw [hattR]; simp)
              have htop2 : st.board.topOf (st.hiddenBase a) = none := by
                rw [relabelBy_topOf r st (st.hiddenBase a)] at htopR2
                exact Option.map_eq_none_iff.mp htopR2
              have hbot2 : st.board.bottomOf (r.cardInv r') = none := by
                rw [relabelBy_bottomOf r st r'] at hbotR2
                exact Option.map_eq_none_iff.mp hbotR2
              have hneS : st.board.attach (st.hiddenBase a) (r.cardInv r') ≠ none :=
                Board.attach_eq_some_iff _ _ _ |>.mpr ⟨htop2, hbot2⟩
              cases hS : st.board.attach (st.hiddenBase a) (r.cardInv r') with
              | none => rw [hS] at hneS; simp at hneS
              | some bd₀ =>
                  exact absurd (apply_reveal_iff.mpr
                    ⟨htop, r.cardInv r', a, bd₀, hbot, hpile, hS, rfl⟩) (by rw [hst]; simp)
      | some st' =>
          rw [apply_reveal_iff] at hst
          obtain ⟨htop, r', a, bd, hbot, hpile, hatt, hst'⟩ := hst
          show (st.relabelBy r).apply (Move.reveal (r.card c)) = some (st'.relabelBy r)
          rw [apply_reveal_iff]
          have htopR : (st.relabelBy r).board.topOf (Sum.inr (r.card c)) = none := by
            rw [relabelBy_topOf_inr r st c, htop]
            rfl
          have hbotR : (st.relabelBy r).board.bottomOf (r.card c)
              = some (Sum.inr (r.card r')) := by
            rw [relabelBy_bottomOf_card r st c, hbot, Option.map_some]
            rfl
          have hpileR : (st.relabelBy r).pileOfTopHidden (r.card r') = some a := by
            rw [relabelBy_pileOfTopHidden r st (r.card r'), Relabel.cardInv_card r r', hpile]
          have hattR : (st.relabelBy r).board.attach ((st.relabelBy r).hiddenBase a) (r.card r')
              = some (relabelBoard r bd) := by
            rw [relabelBy_hiddenBase r st a]
            exact relabelBoard_attach r st.board hatt
          refine ⟨htopR, r.card r', a, relabelBoard r bd, hbotR, hpileR, hattR, ?_⟩
          rw [hst']
          exact relabelBy_with r st bd st.heights
            (fun a' => if a' = a then st.depths a - 1 else st.depths a') st.stock
  | deckPile c b =>
      show (st.relabelBy r).apply (Move.deckPile (r.card c) (r.onBase b))
        = (st.apply (Move.deckPile c b)).map (State.relabelBy r)
      cases hst : st.apply (Move.deckPile c b) with
      | none =>
          show (st.relabelBy r).apply (Move.deckPile (r.card c) (r.onBase b)) = none
          cases hR : (st.relabelBy r).apply (Move.deckPile (r.card c) (r.onBase b)) with
          | none => rfl
          | some st'' =>
              exfalso
              rw [apply_deckPile_iff] at hR
              obtain ⟨hpR, hcpR, bdR, hattR, -⟩ := hR
              have hp : st.stock.prev = some c := by
                rw [relabelBy_prev r st] at hpR
                obtain ⟨x, hx, hx'⟩ := Option.map_eq_some_iff.mp hpR
                have hxc : x = c := Relabel.card_inj r hx'
                rw [hxc] at hx
                exact hx
              have hcp : st.canPlace c b = true := by
                rw [relabelBy_canPlace r st c b] at hcpR
                exact hcpR
              obtain ⟨htopR, hbotR⟩ := (Board.attach_eq_some_iff _ _ _).mp (by rw [hattR]; simp)
              have htop : st.board.topOf b = none := by
                rw [relabelBy_topOf r st b] at htopR
                exact Option.map_eq_none_iff.mp htopR
              have hbot : st.board.bottomOf c = none := by
                rw [relabelBy_bottomOf_card r st c] at hbotR
                exact Option.map_eq_none_iff.mp hbotR
              have hneS : st.board.attach b c ≠ none :=
                Board.attach_eq_some_iff _ _ _ |>.mpr ⟨htop, hbot⟩
              cases hS : st.board.attach b c with
              | none => rw [hS] at hneS; simp at hneS
              | some bd₀ =>
                  exact absurd (apply_deckPile_iff.mpr ⟨hp, hcp, bd₀, hS, rfl⟩)
                    (by rw [hst]; simp)
      | some st' =>
          rw [apply_deckPile_iff] at hst
          obtain ⟨hp, hcp, bd, hatt, hst'⟩ := hst
          show (st.relabelBy r).apply (Move.deckPile (r.card c) (r.onBase b))
            = some (st'.relabelBy r)
          rw [apply_deckPile_iff]
          have hpR : (st.relabelBy r).stock.prev = some (r.card c) := by
            rw [relabelBy_prev r st, hp, Option.map_some]
          have hcpR : (st.relabelBy r).canPlace (r.card c) (r.onBase b) = true := by
            rw [relabelBy_canPlace r st c b, hcp]
          have hattR : (st.relabelBy r).board.attach (r.onBase b) (r.card c)
              = some (relabelBoard r bd) := relabelBoard_attach r st.board hatt
          refine ⟨hpR, hcpR, relabelBoard r bd, hattR, ?_⟩
          rw [hst', relabelBy_stock_cursor r st,
            relabelBy_removeAt r st (st.stock.cursor - 1)]
          exact relabelBy_with r st bd st.heights st.depths
            (st.stock.removeAt (st.stock.cursor - 1))
  | deckStack c =>
      show (st.relabelBy r).apply (Move.deckStack (r.card c))
        = (st.apply (Move.deckStack c)).map (State.relabelBy r)
      cases hst : st.apply (Move.deckStack c) with
      | none =>
          show (st.relabelBy r).apply (Move.deckStack (r.card c)) = none
          cases hR : (st.relabelBy r).apply (Move.deckStack (r.card c)) with
          | none => rfl
          | some st'' =>
              exfalso
              rw [apply_deckStack_iff] at hR
              obtain ⟨hpR, hrkR, -⟩ := hR
              have hp : st.stock.prev = some c := by
                rw [relabelBy_prev r st] at hpR
                obtain ⟨x, hx, hx'⟩ := Option.map_eq_some_iff.mp hpR
                have hxc : x = c := Relabel.card_inj r hx'
                rw [hxc] at hx
                exact hx
              have hrk : c.rank.toIdx = st.heights c.suit := by
                rw [relabelBy_heights r st c] at hrkR
                exact hrkR
              exact absurd (apply_deckStack_iff.mpr ⟨hp, hrk, rfl⟩) (by rw [hst]; simp)
      | some st' =>
          rw [apply_deckStack_iff] at hst
          obtain ⟨hp, hrk, hst'⟩ := hst
          show (st.relabelBy r).apply (Move.deckStack (r.card c)) = some (st'.relabelBy r)
          rw [apply_deckStack_iff]
          have hpR : (st.relabelBy r).stock.prev = some (r.card c) := by
            rw [relabelBy_prev r st, hp, Option.map_some]
          have hrkR : (r.card c).rank.toIdx = (st.relabelBy r).heights (r.card c).suit := by
            rw [relabelBy_heights r st c]
            exact hrk
          refine ⟨hpR, hrkR, ?_⟩
          rw [hst', relabelBy_stock_cursor r st,
            relabelBy_removeAt r st (st.stock.cursor - 1), relabelBy_heights_bump r st c]
          exact relabelBy_with r st st.board
            (fun s => if s = c.suit then st.heights s + 1 else st.heights s) st.depths
            (st.stock.removeAt (st.stock.cursor - 1))
  | pileStack c =>
      show (st.relabelBy r).apply (Move.pileStack (r.card c))
        = (st.apply (Move.pileStack c)).map (State.relabelBy r)
      cases hst : st.apply (Move.pileStack c) with
      | none =>
          show (st.relabelBy r).apply (Move.pileStack (r.card c)) = none
          cases hR : (st.relabelBy r).apply (Move.pileStack (r.card c)) with
          | none => rfl
          | some st'' =>
              exfalso
              rw [apply_pileStack_iff] at hR
              obtain ⟨htR, b, hb, hrkR, -⟩ := hR
              have htop : st.board.topOf (Sum.inr c) = none := by
                rw [relabelBy_topOf_inr r st c] at htR
                exact Option.map_eq_none_iff.mp htR
              have hbot : st.board.bottomOf c = some (Sum.map id r.cardInv b) := by
                rw [relabelBy_bottomOf_card r st c] at hb
                cases hbb : st.board.bottomOf c with
                | none => rw [hbb] at hb; simp at hb
                | some x =>
                    rw [hbb] at hb
                    rw [Option.map_some, Option.some.injEq] at hb
                    have hx : x = Sum.map id r.cardInv b := by
                      rw [← Relabel.cardInv_onBase r x, hb]
                    rw [hx]
              have hrk : c.rank.toIdx = st.heights c.suit := by
                rw [relabelBy_heights r st c] at hrkR
                exact hrkR
              exact absurd (apply_pileStack_iff.mpr
                ⟨htop, Sum.map id r.cardInv b, hbot, hrk, rfl⟩) (by rw [hst]; simp)
      | some st' =>
          rw [apply_pileStack_iff] at hst
          obtain ⟨htop, b, hb, hrk, hst'⟩ := hst
          show (st.relabelBy r).apply (Move.pileStack (r.card c)) = some (st'.relabelBy r)
          rw [apply_pileStack_iff]
          have htopR : (st.relabelBy r).board.topOf (Sum.inr (r.card c)) = none := by
            rw [relabelBy_topOf_inr r st c, htop]
            rfl
          have hbotR : (st.relabelBy r).board.bottomOf (r.card c) = some (r.onBase b) := by
            rw [relabelBy_bottomOf_card r st c, hb, Option.map_some]
          have hrkR : (r.card c).rank.toIdx = (st.relabelBy r).heights (r.card c).suit := by
            rw [relabelBy_heights r st c]
            exact hrk
          refine ⟨htopR, r.onBase b, hbotR, hrkR, ?_⟩
          rw [hst']
          have hbb : (st.relabelBy r).board = relabelBoard r st.board := rfl
          rw [hbb, relabelBoard_detach r st.board b, relabelBy_heights_bump r st c]
          exact relabelBy_with r st (st.board.detach b)
            (fun s => if s = c.suit then st.heights s + 1 else st.heights s) st.depths st.stock
  | stackPile c b =>
      show (st.relabelBy r).apply (Move.stackPile (r.card c) (r.onBase b))
        = (st.apply (Move.stackPile c b)).map (State.relabelBy r)
      cases hst : st.apply (Move.stackPile c b) with
      | none =>
          show (st.relabelBy r).apply (Move.stackPile (r.card c) (r.onBase b)) = none
          cases hR : (st.relabelBy r).apply (Move.stackPile (r.card c) (r.onBase b)) with
          | none => rfl
          | some st'' =>
              exfalso
              rw [apply_stackPile_iff] at hR
              obtain ⟨hrkR, hcpR, bdR, hattR, -⟩ := hR
              have hrk : c.rank.toIdx + 1 = st.heights c.suit := by
                rw [relabelBy_heights r st c] at hrkR
                exact hrkR
              have hcp : st.canPlace c b = true := by
                rw [relabelBy_canPlace r st c b] at hcpR
                exact hcpR
              obtain ⟨htopR, hbotR⟩ := (Board.attach_eq_some_iff _ _ _).mp (by rw [hattR]; simp)
              have htop : st.board.topOf b = none := by
                rw [relabelBy_topOf r st b] at htopR
                exact Option.map_eq_none_iff.mp htopR
              have hbot : st.board.bottomOf c = none := by
                rw [relabelBy_bottomOf_card r st c] at hbotR
                exact Option.map_eq_none_iff.mp hbotR
              have hneS : st.board.attach b c ≠ none :=
                Board.attach_eq_some_iff _ _ _ |>.mpr ⟨htop, hbot⟩
              cases hS : st.board.attach b c with
              | none => rw [hS] at hneS; simp at hneS
              | some bd₀ =>
                  exact absurd (apply_stackPile_iff.mpr ⟨hrk, hcp, bd₀, hS, rfl⟩)
                    (by rw [hst]; simp)
      | some st' =>
          rw [apply_stackPile_iff] at hst
          obtain ⟨hrk, hcp, bd, hatt, hst'⟩ := hst
          show (st.relabelBy r).apply (Move.stackPile (r.card c) (r.onBase b))
            = some (st'.relabelBy r)
          rw [apply_stackPile_iff]
          have hrkR : (r.card c).rank.toIdx + 1 = (st.relabelBy r).heights (r.card c).suit := by
            rw [relabelBy_heights r st c]
            exact hrk
          have hcpR : (st.relabelBy r).canPlace (r.card c) (r.onBase b) = true := by
            rw [relabelBy_canPlace r st c b, hcp]
          have hattR : (st.relabelBy r).board.attach (r.onBase b) (r.card c)
              = some (relabelBoard r bd) := relabelBoard_attach r st.board hatt
          refine ⟨hrkR, hcpR, relabelBoard r bd, hattR, ?_⟩
          rw [hst', relabelBy_heights_drop r st c]
          exact relabelBy_with r st bd
            (fun s => if s = c.suit then st.heights s - 1 else st.heights s) st.depths st.stock
  | pilePile c b =>
      show (st.relabelBy r).apply (Move.pilePile (r.card c) (r.onBase b))
        = (st.apply (Move.pilePile c b)).map (State.relabelBy r)
      cases hst : st.apply (Move.pilePile c b) with
      | none =>
          show (st.relabelBy r).apply (Move.pilePile (r.card c) (r.onBase b)) = none
          cases hR : (st.relabelBy r).apply (Move.pilePile (r.card c) (r.onBase b)) with
          | none => rfl
          | some st'' =>
              exfalso
              rw [apply_pilePile_iff] at hR
              obtain ⟨b₀, hbR, hneR, hcmrR, bdR, hattR, -⟩ := hR
              have hbx : ∃ x, st.board.bottomOf c = some x ∧ r.onBase x = b₀ := by
                rw [relabelBy_bottomOf_card r st c] at hbR
                cases hbb : st.board.bottomOf c with
                | none => rw [hbb] at hbR; simp at hbR
                | some x =>
                    rw [hbb] at hbR
                    rw [Option.map_some, Option.some.injEq] at hbR
                    exact ⟨x, rfl, hbR⟩
              obtain ⟨x, hb₁, hox⟩ := hbx
              have hne : x ≠ b := by
                intro hcon
                rw [hcon] at hox
                exact hneR hox.symm
              have hcmr : st.canMoveRun c b = true := by
                rw [relabelBy_canMoveRun r st c b] at hcmrR
                exact hcmrR
              obtain ⟨htopR, hbotR⟩ := (Board.attach_eq_some_iff _ _ _).mp (by rw [hattR]; simp)
              have htop : (st.board.detach x).topOf b = none := by
                rw [show (st.relabelBy r).board = relabelBoard r st.board from rfl,
                  show b₀ = r.onBase x from hox.symm] at htopR
                rw [relabelBoard_detach r st.board x] at htopR
                rw [relabelBoard_topOf r (st.board.detach x) b] at htopR
                exact Option.map_eq_none_iff.mp htopR
              have hbot : (st.board.detach x).bottomOf c = none := by
                rw [show (st.relabelBy r).board = relabelBoard r st.board from rfl,
                  show b₀ = r.onBase x from hox.symm] at hbotR
                rw [relabelBoard_detach r st.board x] at hbotR
                rw [relabelBoard_bottomOf r (st.board.detach x) (r.card c),
                  Relabel.cardInv_card] at hbotR
                exact Option.map_eq_none_iff.mp hbotR
              have hneS : (st.board.detach x).attach b c ≠ none :=
                Board.attach_eq_some_iff _ _ _ |>.mpr ⟨htop, hbot⟩
              cases hS : (st.board.detach x).attach b c with
              | none => rw [hS] at hneS; simp at hneS
              | some bd₀ =>
                  exact absurd (apply_pilePile_iff.mpr
                    ⟨x, hb₁, hne, hcmr, bd₀, hS, rfl⟩) (by rw [hst]; simp)
      | some st' =>
          rw [apply_pilePile_iff] at hst
          obtain ⟨b₀, hb, hne, hcmr, bd, hatt, hst'⟩ := hst
          show (st.relabelBy r).apply (Move.pilePile (r.card c) (r.onBase b))
            = some (st'.relabelBy r)
          rw [apply_pilePile_iff]
          have hbR : (st.relabelBy r).board.bottomOf (r.card c) = some (r.onBase b₀) := by
            rw [relabelBy_bottomOf_card r st c, hb, Option.map_some]
          have hneR : r.onBase b₀ ≠ r.onBase b := fun hcon => hne (Relabel.onBase_inj r hcon)
          have hcmrR : (st.relabelBy r).canMoveRun (r.card c) (r.onBase b) = true := by
            rw [relabelBy_canMoveRun r st c b, hcmr]
          have hattR : ((st.relabelBy r).board.detach (r.onBase b₀)).attach (r.onBase b)
              (r.card c) = some (relabelBoard r bd) := by
            rw [show (st.relabelBy r).board = relabelBoard r st.board from rfl,
              relabelBoard_detach r st.board b₀]
            exact relabelBoard_attach r (st.board.detach b₀) hatt
          refine ⟨r.onBase b₀, hbR, hneR, hcmrR, relabelBoard r bd, hattR, ?_⟩
          rw [hst']
          exact relabelBy_with r st bd st.heights st.depths st.stock

theorem run_relabel (r : Relabel) : ∀ (st : State) (play : List Move),
    (st.relabelBy r).run (play.map (Move.relabel r)) = (st.run play).map (State.relabelBy r) := by
  intro st play
  revert st
  induction play with
  | nil => intro st; rfl
  | cons m ms ih =>
      intro st
      simp only [List.map_cons, State.run]
      rw [apply_relabel r m st]
      cases hst : st.apply m with
      | none => rfl
      | some st' => exact ih st'

theorem Relabel.inv_coherent (r : Relabel) :
    ∀ s s', (r.suitInv s).color ≠ (r.suitInv s').color ↔ s.color ≠ s'.color := by
  intro s s'
  have h := r.coherent (r.suitInv s) (r.suitInv s')
  rw [r.right_inv s, r.right_inv s'] at h
  exact h.symm

def Relabel.inv (r : Relabel) : Relabel where
  suit := r.suitInv
  suitInv := r.suit
  left_inv := r.right_inv
  right_inv := r.left_inv
  coherent := r.inv_coherent

theorem state_ext {st₁ st₂ : State}
    (hdeal : st₁.deal = st₂.deal) (hboard : st₁.board = st₂.board)
    (hheights : st₁.heights = st₂.heights) (hdepths : st₁.depths = st₂.depths)
    (hstock : st₁.stock = st₂.stock) (hdrawStep : st₁.drawStep = st₂.drawStep) :
    st₁ = st₂ := by
  cases st₁ with
  | mk d1 b1 hg1 dp1 s1 ds1 =>
    cases st₂ with
    | mk d2 b2 hg2 dp2 s2 ds2 =>
      simp only [State.mk.injEq]
      exact ⟨hdeal, hboard, hheights, hdepths, hstock, hdrawStep⟩

theorem Deal.ext' {d₁ d₂ : Deal} (hp : ∀ a, d₁.piles a = d₂.piles a)
    (hs : d₁.stock = d₂.stock) : d₁ = d₂ := by
  cases d₁ with
  | mk p1 s1 =>
    cases d₂ with
    | mk p2 s2 =>
      simp only [Deal.mk.injEq]
      exact ⟨funext hp, hs⟩

theorem relabelBy_inv (r : Relabel) (st : State) :
    (st.relabelBy r).relabelBy r.inv = st := by
  refine state_ext ?_ ?_ ?_ rfl ?_ rfl
  · -- deal
    show (⟨fun a => ((st.deal.piles a).map r.card).map r.inv.card,
           (st.deal.stock.map r.card).map r.inv.card⟩ : Deal) = st.deal
    cases hd : st.deal with
    | mk ps sk =>
        show (⟨fun a => ((ps a).map r.card).map r.inv.card,
               (sk.map r.card).map r.inv.card⟩ : Deal) = ⟨ps, sk⟩
        have h2 : r.inv.card = r.cardInv := rfl
        rw [h2]
        have hpt : r.cardInv ∘ r.card = id := funext (fun x => r.cardInv_card x)
        simp only [List.map_map, hpt, List.map_id]
  · -- board
    refine Board.ext_topOf (funext (fun b' => ?_))
    show ((st.relabelBy r).board.topOf (Sum.map id r.inv.cardInv b')).map r.inv.card
      = st.board.topOf b'
    have h1 : Sum.map id r.inv.cardInv = r.onBase := rfl
    have h2 : r.inv.card = r.cardInv := rfl
    have h3 : (st.relabelBy r).board = relabelBoard r st.board := rfl
    rw [h1, h2, h3, relabelBoard_topOf r st.board b']
    cases hx : st.board.topOf b' with
    | none => rfl
    | some x =>
        show some (r.cardInv (r.card x)) = some x
        rw [Relabel.cardInv_card r x]
  · -- heights
    funext s
    show st.heights (r.suitInv (r.suit s)) = st.heights s
    rw [r.left_inv s]
  · -- stock
    show ({ cards := ((st.stock.cards.map r.card).map r.inv.card),
            cursor := st.stock.cursor } : Cycle Card) = st.stock
    cases hst : st.stock with
    | mk cs cu =>
        show ({ cards := ((cs.map r.card).map r.inv.card), cursor := cu } : Cycle Card)
          = { cards := cs, cursor := cu }
        have h2 : r.inv.card = r.cardInv := rfl
        rw [h2]
        have hpt : r.cardInv ∘ r.card = id := funext (fun x => r.cardInv_card x)
        simp only [List.map_map, hpt, List.map_id]

theorem solvable_of_relabel {r : Relabel} {st : State} (h : st.solvableFrom) :
    (st.relabelBy r).solvableFrom := by
  obtain ⟨play, w, hrun, hwin⟩ := h
  refine ⟨play.map (Move.relabel r), w.relabelBy r, ?_, ?_⟩
  · rw [run_relabel r st play, hrun]
    rfl
  · have hall : ∀ s ∈ Suit.all, w.heights s = 13 :=
      fun s _ => of_decide_eq_true ((List.all_eq_true.mp hwin) s (Suit.mem_all s))
    exact List.all_eq_true.mpr (fun s _ =>
      decide_eq_true (hall (r.suitInv s) (Suit.mem_all _)))

/-- **T, generalized**: solvability is invariant under every coherent
suit relabeling — all 8 elements of the group at once. -/
theorem solvable_relabel (r : Relabel) (st : State) :
    (st.relabelBy r).solvableFrom ↔ st.solvableFrom := by
  constructor
  · intro h
    have h2 := solvable_of_relabel (r := r.inv) h
    rw [relabelBy_inv r st] at h2
    exact h2
  · exact solvable_of_relabel


/-- `flipAll` is the twin-swap instance. -/
theorem flipAll_eq_relabelTwin (st : State) : st.flipAll = st.relabelBy Relabel.twin := rfl

/-- **T (twin swap), conjugation step**: the twin instance of
`apply_relabel` — `flipAll` *is* `relabelBy Relabel.twin` (by `rfl`)
and `Move.flipMove` is `Move.relabel Relabel.twin` per constructor, so
the general conjugation transfers wholesale. -/
theorem apply_flipAll (m : Move) (st : State) :
    st.flipAll.apply m.flipMove = (st.apply m).map State.flipAll := by
  have h1 : m.flipMove = m.relabel Relabel.twin := by cases m <;> rfl
  have h2 : State.flipAll = State.relabelBy Relabel.twin :=
    funext flipAll_eq_relabelTwin
  rw [h1, h2]
  exact apply_relabel Relabel.twin m st

/-- **T (twin swap)**: solvability is invariant under the relabeling —
the twin instance of `solvable_relabel`. -/
theorem solvable_flipAll {st : State} (h : st.solvableFrom) :
    st.flipAll.solvableFrom := by
  rw [flipAll_eq_relabelTwin]
  exact (solvable_relabel Relabel.twin st).mpr h

section Probe
example (bd : Board) (b : Base) (acc : List Card) : Board.aboveOf.go bd 0 b acc = acc := rfl
example (bd : Board) (fuel : Nat) (b : Base) (acc : List Card) :
    Board.aboveOf.go bd (fuel+1) b acc
      = match bd.topOf b with
        | none => acc
        | some c' => if acc.contains c' then acc else Board.aboveOf.go bd fuel (Sum.inr c') (c' :: acc) := rfl
example (bd : Board) (c : Card) :
    bd.aboveOf c = Board.aboveOf.go bd 52 (Sum.inr c) [] := rfl
end Probe

/-! ## 2. Reversibility and commitments — their Lemma A1, model side

`pilePile` is an involution; `draw` is cyclically invertible;
`pileStack`∘`stackPile` is a *near*-inverse — the anchor case (a
fully-revealed non-king bottom card cannot return to the empty pile)
is exactly why safe-stacking (C1) is a theorem in the engine rather
than trivia, and where the reshape lemma (B4) earns its keep.
-/

/-- The return-base condition for un-stacking: a king may return to
an anchor; a card that sat on `d` may return onto `d`. -/
def canReturnBase (c : Card) (b₀ : Base) : Bool :=
  match b₀ with
  | Sum.inl _ => decide (c.rank = Rank.king)
  | Sum.inr d => canSitOn c d

/-- The round trip through the foundations is the identity: detach via
`pileStack`, come back with `stackPile` to the same base — the board
re-attaches (attach after detach at the same base restores the
matching pointwise), the heights return (+1 then -1). -/
theorem pileStack_stackPile_roundtrip {st : State} {c : Card} {b₀ : Base}
    {st₁ st₂ : State}
    (h₀ : st.board.bottomOf c = some b₀)
    (hret : canReturnBase c b₀ = true)
    (h₁ : st.apply (Move.pileStack c) = some st₁)
    (h₂ : st₁.apply (Move.stackPile c b₀) = some st₂) : st₂ = st := by
  have htop : st.board.topOf b₀ = some c := (Board.bottomOf_eq st.board c b₀).mp h₀
  simp only [State.apply, State.applyPileStack] at h₁
  cases ht : st.board.topOf (Sum.inr c) with
  | some x =>
    rw [ht] at h₁
    exact absurd h₁ (by simp)
  | none =>
    rw [ht, h₀] at h₁
    have h₁' : (if c.rank.toIdx = st.heights c.suit then
        some { st with
          board := st.board.detach b₀,
          heights := fun s => if s = c.suit then st.heights s + 1 else st.heights s }
        else none) = some st₁ := h₁
    split at h₁'
    · rw [Option.some.injEq] at h₁'
      subst h₁'
      simp only [State.apply, State.applyStackPile] at h₂
      cases hatt : (st.board.detach b₀).attach b₀ c with
      | none => rw [hatt] at h₂; exact absurd h₂ (by simp)
      | some bd =>
        rw [hatt] at h₂
        simp at h₂
        obtain ⟨-, h'⟩ := h₂
        subst h'
        have hbdeq : bd.topOf = st.board.topOf := by
          funext b'
          by_cases hbb : b' = b₀
          · subst hbb
            rw [Board.attach_topOf _ _ _ hatt]
            exact htop.symm
          · rw [Board.attach_topOf_ne _ _ _ hatt hbb, Board.detach_topOf_ne _ _ _ hbb]
        have hbd : bd = st.board := Board.ext_topOf hbdeq
        have hh : (fun s => if s = c.suit then
            (if s = c.suit then st.heights s + 1 else st.heights s) - 1
            else (if s = c.suit then st.heights s + 1 else st.heights s)) = st.heights := by
          funext s
          by_cases hsc : s = c.suit
          · subst hsc
            rw [if_pos rfl, if_pos rfl]
            omega
          · rw [if_neg hsc, if_neg hsc]
        cases st with
        | mk d b hgt dpt stck ds =>
          rw [hbd, hh]
    · exact absurd h₁' (by simp)

/-- The moved run carries back; `aboveOf` is unchanged.  The first move
detaches `b₀` and attaches `b`; the second (given legal) detaches `b`
and attaches `b₀` — the composition's `topOf` is pointwise the
original's, and pilePile writes only the board. -/
theorem pilePile_roundtrip {st : State} {c : Card} {b b₀ : Base} {st₁ st₂ : State}
    (h₀ : st.board.bottomOf c = some b₀)
    (h₁ : st.apply (Move.pilePile c b) = some st₁)
    (h₂ : st₁.apply (Move.pilePile c b₀) = some st₂) : st₂ = st := by
  have htop₀ : st.board.topOf b₀ = some c := (Board.bottomOf_eq st.board c b₀).mp h₀
  rw [apply_pilePile_iff] at h₁
  obtain ⟨b₀', hb₀', hne, _, bd, hatt, hst₁⟩ := h₁
  rw [h₀] at hb₀'
  have hb₀e : b₀' = b₀ := (Option.some.inj hb₀').symm
  rw [hb₀e] at hne hatt
  rw [hst₁] at h₂
  rw [apply_pilePile_iff] at h₂
  obtain ⟨b₁, hb₁, _, _, bd₂, hatt₂, hst₂⟩ := h₂
  have hb₁' : bd.bottomOf c = some b₁ := hb₁
  have hatt₂' : (bd.detach b₁).attach b₀ c = some bd₂ := hatt₂
  have hbb₁ : b₁ = b :=
    bd.inj b₁ b c ((Board.bottomOf_eq bd c b₁).mp hb₁') (Board.attach_topOf _ _ _ hatt)
  rw [hbb₁] at hatt₂'
  have hneA : (st.board.detach b₀).attach b c ≠ none := by rw [hatt]; simp
  obtain ⟨hta, _⟩ := (Board.attach_eq_some_iff _ _ _).mp hneA
  have htb : st.board.topOf b = none := by
    rw [← Board.detach_topOf_ne st.board b₀ b (Ne.symm hne)]
    exact hta
  have hbd₂ : bd₂ = st.board := by
    refine Board.ext_topOf (funext (fun b' => ?_))
    by_cases hbb₀ : b' = b₀
    · rw [hbb₀, Board.attach_topOf _ _ _ hatt₂', htop₀]
    · rw [Board.attach_topOf_ne _ _ _ hatt₂' hbb₀]
      by_cases hbb : b' = b
      · rw [hbb, Board.detach_topOf, htb]
      · rw [Board.detach_topOf_ne _ _ _ hbb, Board.attach_topOf_ne _ _ _ hatt hbb,
          Board.detach_topOf_ne _ _ _ hbb₀]
  rw [hst₂, hbd₂]

/-- A full pass plus the wrap deal returns to the pass start: from
cursor 0, dealing everything (the clamp passes the last card) and
wrapping lands home — the deal cycle's period is `⌈n/s⌉ + 1`, at any
step `s ≥ 1` (deck.rs `offset`'s periodicity).  Supersedes the old
rotate-form "a full rotation is the identity", an artifact of the
jump semantics.

TODO(proof) [M]: the deal chain — each deal from `k·s` below `n`
lands at `min ((k+1)·s, n)`; the clamp reaches `n` at `k = ⌈n/s⌉`,
and the next deal wraps to `0`. -/
theorem draw_full_pass {st : State} (hc : st.stock.cursor = 0)
    (hs : 0 < st.drawStep) {st' : State}
    (h : st.run (List.replicate
        ((st.stock.cards.length + st.drawStep - 1) / st.drawStep + 1) Move.draw)
      = some st') :
    st' = st := sorry

/-- A commitment: no play returns to the state after it. -/
def irreversibleAt (st : State) (m : Move) : Prop :=
  ∀ st₁ play, st.apply m = some st₁ → st₁.run play ≠ some st

/-- TODO(proof): depths only decrease — no move raises the hidden
boundary. -/
theorem irreversible_reveal {st : State} {c : Card} {st₁ : State}
    (h : st.apply (Move.reveal c) = some st₁) : irreversibleAt st (Move.reveal c) := sorry

/-- TODO(proof): no move returns a card to the cycle. -/
theorem irreversible_deckPile {st : State} {c : Card} {b : Base} {st₁ : State}
    (h : st.apply (Move.deckPile c b) = some st₁) : irreversibleAt st (Move.deckPile c b) := sorry

/-- TODO(proof): as `deckPile`; the foundation is not the cycle. -/
theorem irreversible_deckStack {st : State} {c : Card} {st₁ : State}
    (h : st.apply (Move.deckStack c) = some st₁) : irreversibleAt st (Move.deckStack c) := sorry

/-- The accommodation moves (their Lemma A): stack↔pile shuffling. -/
def Move.isAccommodation : Move → Bool
  | .pileStack _ => true
  | .stackPile _ _ => true
  | _ => false

/-- The commitment moves (their Lemma A1). -/
def Move.isCommit : Move → Bool
  | .reveal _ => true
  | .deckPile _ _ => true
  | .deckStack _ => true
  | _ => false

/-- The stock-*consuming* moves: the card draws (`deckPile`,
`deckStack`).  `.draw` — the pure deal that advances the cursor —
consumes nothing: the pace advance, not a card down. -/
def Move.consumesStock : Move → Bool
  | .deckPile _ _ => true
  | .deckStack _ => true
  | _ => false

/-- The accommodation relation (their Lemma A's shuffle reachability). -/
def accommodates (st st' : State) : Prop :=
  ∃ play, st.run play = some st' ∧ ∀ m ∈ play, m.isAccommodation = true

/-- Prepending plays: `run` distributes over `++` (the append lemma —
Progress's `run_append` restated for the upstream file, under the
`State` namespace to keep the names distinct). -/
theorem State.run_append (st : State) (l₁ l₂ : List Move) :
    st.run (l₁ ++ l₂) = (st.run l₁) >>= fun s => s.run l₂ := by
  revert st
  induction l₁ with
  | nil => intro st; rfl
  | cons m ms ih =>
      intro st
      simp only [List.cons_append, State.run]
      cases st.apply m with
      | none => rfl
      | some st' => exact ih st'

/-- The accommodation reduction, easy direction — prepend the shuffle
play: an accommodation play from `st'` to `st`, then the win. -/
theorem solvable_of_accommodates {st st' : State}
    (hacc : accommodates st' st) (hsol : st.solvableFrom) : st'.solvableFrom := by
  obtain ⟨play, hrun, _⟩ := hacc
  obtain ⟨win, w, hwrun, hwin⟩ := hsol
  refine ⟨play ++ win, w, ?_, hwin⟩
  rw [State.run_append, hrun]
  exact hwrun

/-- The accommodation reduction, hard direction — this is the reshape
argument (B4): a winning play survives the cards having been shuffled
through the foundations.  TODO. -/
theorem solvable_accommodates {st st' : State}
    (hacc : accommodates st st') (hsol : st.solvableFrom) : st'.solvableFrom := sorry

/-! ## 3. Commutation — C-IND and C13

Coarse layer: component-disjoint moves commute unconditionally (draw
and reveal are the clean instance — the engine's ~92% measured
draw·reveal landscape is an interleaving artifact, not game structure).
Fine layer: disjoint touch-sets — the "type-ball interaction lemma"
the ledger names as C13's premise.
-/

/-- The four state components. -/
inductive Component : Type where
  | tableau | foundations | hidden | stock
  deriving DecidableEq, Repr

/-- Which components a move reads/writes. -/
def Move.comps : Move → List Component
  | .draw => [.stock]
  | .reveal _ => [.tableau, .hidden]
  | .deckPile _ _ => [.stock, .tableau]
  | .deckStack _ => [.stock, .foundations]
  | .pileStack _ => [.tableau, .foundations]
  | .stackPile _ _ => [.tableau, .foundations]
  | .pilePile _ _ => [.tableau]

/-! ### The blindness kit — the commutation workhorse

A move's guards read only their own components, so replacing the fields
a move never reads preserves its outcome up to those fields: the
stock/heights-blind forms (reveal, pilePile — for the `draw` and
`deckStack` pairs), the board/depths-blind form (deckStack — for the
reveal/pilePile pairs), and the stock-blind none-forms (pileStack,
stackPile).  The `some`-forms carry the successor along with the
replaced fields. -/

theorem reveal_blind_some {st : State} {c : Card} {cy : Cycle Card} {hs : Suit → Nat}
    {s₁ : State} (h : st.apply (Move.reveal c) = some s₁) :
    ({ st with stock := cy, heights := hs } : State).apply (Move.reveal c)
      = some { s₁ with stock := cy, heights := hs } := by
  rw [apply_reveal_iff] at h
  obtain ⟨htop, r, a, bd, hbot, hpile, hatt, hst₁⟩ := h
  rw [hst₁]
  rw [apply_reveal_iff]
  exact ⟨htop, r, a, bd, hbot, hpile, hatt, rfl⟩

theorem reveal_blind_none {st : State} {c : Card} {cy : Cycle Card} {hs : Suit → Nat}
    (h : st.apply (Move.reveal c) = none) :
    ({ st with stock := cy, heights := hs } : State).apply (Move.reveal c) = none := by
  cases hr : ({ st with stock := cy, heights := hs } : State).apply (Move.reveal c) with
  | none => rfl
  | some _ =>
      exfalso
      rw [apply_reveal_iff] at hr
      obtain ⟨htop, r, a, bd, hbot, hpile, hatt, _⟩ := hr
      have hcontra : st.apply (Move.reveal c) = some { st with
          board := bd,
          depths := fun a' => if a' = a then st.depths a - 1 else st.depths a' } :=
        apply_reveal_iff.mpr ⟨htop, r, a, bd, hbot, hpile, hatt, rfl⟩
      exact absurd hcontra (by rw [h]; simp)

theorem pilePile_blind_some {st : State} {c : Card} {b : Base} {cy : Cycle Card}
    {hs : Suit → Nat} {s₁ : State} (h : st.apply (Move.pilePile c b) = some s₁) :
    ({ st with stock := cy, heights := hs } : State).apply (Move.pilePile c b)
      = some { s₁ with stock := cy, heights := hs } := by
  rw [apply_pilePile_iff] at h
  obtain ⟨b₀, hb₀, hne, hcmr, bd, hatt, hst₁⟩ := h
  rw [hst₁]
  rw [apply_pilePile_iff]
  exact ⟨b₀, hb₀, hne, hcmr, bd, hatt, rfl⟩

theorem pilePile_blind_none {st : State} {c : Card} {b : Base} {cy : Cycle Card}
    {hs : Suit → Nat} (h : st.apply (Move.pilePile c b) = none) :
    ({ st with stock := cy, heights := hs } : State).apply (Move.pilePile c b) = none := by
  cases hr : ({ st with stock := cy, heights := hs } : State).apply (Move.pilePile c b) with
  | none => rfl
  | some _ =>
      exfalso
      rw [apply_pilePile_iff] at hr
      obtain ⟨b₀, hb₀, hne, hcmr, bd, hatt, _⟩ := hr
      have hcontra : st.apply (Move.pilePile c b) = some { st with board := bd } :=
        apply_pilePile_iff.mpr ⟨b₀, hb₀, hne, hcmr, bd, hatt, rfl⟩
      exact absurd hcontra (by rw [h]; simp)

theorem deckStack_blind_some {st : State} {c : Card} {bd : Board} {dpt : Anchor → Nat}
    {sd : State} (h : st.apply (Move.deckStack c) = some sd) :
    ({ st with board := bd, depths := dpt } : State).apply (Move.deckStack c)
      = some { sd with board := bd, depths := dpt } := by
  rw [apply_deckStack_iff] at h
  obtain ⟨hp, hrk, hsd⟩ := h
  rw [hsd]
  rw [apply_deckStack_iff]
  exact ⟨hp, hrk, rfl⟩

theorem deckStack_blind_none {st : State} {c : Card} {bd : Board} {dpt : Anchor → Nat}
    (h : st.apply (Move.deckStack c) = none) :
    ({ st with board := bd, depths := dpt } : State).apply (Move.deckStack c) = none := by
  cases hr : ({ st with board := bd, depths := dpt } : State).apply (Move.deckStack c) with
  | none => rfl
  | some _ =>
      exfalso
      rw [apply_deckStack_iff] at hr
      obtain ⟨hp, hrk, _⟩ := hr
      have hcontra : st.apply (Move.deckStack c) = some { st with
          stock := st.stock.removeAt (st.stock.cursor - 1),
          heights := fun s => if s = c.suit then st.heights s + 1 else st.heights s } :=
        apply_deckStack_iff.mpr ⟨hp, hrk, rfl⟩
      exact absurd hcontra (by rw [h]; simp)

theorem pileStack_blind_none {st : State} {c : Card} {cy : Cycle Card}
    (h : st.apply (Move.pileStack c) = none) :
    ({ st with stock := cy } : State).apply (Move.pileStack c) = none := by
  cases hr : ({ st with stock := cy } : State).apply (Move.pileStack c) with
  | none => rfl
  | some _ =>
      exfalso
      rw [apply_pileStack_iff] at hr
      obtain ⟨htop, b, hb, hrk, _⟩ := hr
      have hcontra : st.apply (Move.pileStack c) = some { st with
          board := st.board.detach b,
          heights := fun s => if s = c.suit then st.heights s + 1 else st.heights s } :=
        apply_pileStack_iff.mpr ⟨htop, b, hb, hrk, rfl⟩
      exact absurd hcontra (by rw [h]; simp)

theorem stackPile_blind_none {st : State} {c : Card} {b : Base} {cy : Cycle Card}
    (h : st.apply (Move.stackPile c b) = none) :
    ({ st with stock := cy } : State).apply (Move.stackPile c b) = none := by
  cases hr : ({ st with stock := cy } : State).apply (Move.stackPile c b) with
  | none => rfl
  | some _ =>
      exfalso
      rw [apply_stackPile_iff] at hr
      obtain ⟨hrk, hcp, bd, hatt, _⟩ := hr
      have hcontra : st.apply (Move.stackPile c b) = some { st with
          board := bd,
          heights := fun s => if s = c.suit then st.heights s - 1 else st.heights s } :=
        apply_stackPile_iff.mpr ⟨hrk, hcp, bd, hatt, rfl⟩
      exact absurd hcontra (by rw [h]; simp)

/-- The `draw` half of every draw-pair: the deal always succeeds, so
only the other move's stock-blindness remains — failure persists, and
success carries the successor with the deal's stock. -/
theorem draw_comm_gen (st : State) (m : Move)
    (hn : st.apply m = none →
      ({ st with stock := st.stock.dealOnce st.drawStep } : State).apply m = none)
    (hs : ∀ s₁, st.apply m = some s₁ →
      ({ st with stock := st.stock.dealOnce st.drawStep } : State).apply m
        = some { s₁ with stock := s₁.stock.dealOnce s₁.drawStep }) :
    (st.apply Move.draw >>= fun s => s.apply m) = (st.apply m >>= fun s => s.apply Move.draw) := by
  have hD : st.apply Move.draw = some { st with stock := st.stock.dealOnce st.drawStep } := rfl
  rw [hD]
  cases hm : st.apply m with
  | none => exact hn hm
  | some s₁ => exact hs s₁ hm

theorem draw_comm_reveal (st : State) (c : Card) :
    (st.apply Move.draw >>= fun s => s.apply (Move.reveal c)) =
    (st.apply (Move.reveal c) >>= fun s => s.apply Move.draw) := by
  refine draw_comm_gen st (Move.reveal c) ?_ ?_
  · exact reveal_blind_none
  · intro s₁ h
    rw [apply_reveal_iff] at h
    obtain ⟨htop, r, a, bd, hbot, hpile, hatt, hst₁⟩ := h
    rw [hst₁]
    rw [apply_reveal_iff]
    exact ⟨htop, r, a, bd, hbot, hpile, hatt, rfl⟩

theorem draw_comm_pileStack (st : State) (c : Card) :
    (st.apply Move.draw >>= fun s => s.apply (Move.pileStack c)) =
    (st.apply (Move.pileStack c) >>= fun s => s.apply Move.draw) := by
  refine draw_comm_gen st (Move.pileStack c) ?_ ?_
  · exact pileStack_blind_none
  · intro s₁ h
    rw [apply_pileStack_iff] at h
    obtain ⟨htop, b, hb, hrk, hst₁⟩ := h
    rw [hst₁]
    rw [apply_pileStack_iff]
    exact ⟨htop, b, hb, hrk, rfl⟩

theorem draw_comm_stackPile (st : State) (c : Card) (b : Base) :
    (st.apply Move.draw >>= fun s => s.apply (Move.stackPile c b)) =
    (st.apply (Move.stackPile c b) >>= fun s => s.apply Move.draw) := by
  refine draw_comm_gen st (Move.stackPile c b) ?_ ?_
  · exact stackPile_blind_none
  · intro s₁ h
    rw [apply_stackPile_iff] at h
    obtain ⟨hrk, hcp, bd, hatt, hst₁⟩ := h
    rw [hst₁]
    rw [apply_stackPile_iff]
    exact ⟨hrk, hcp, bd, hatt, rfl⟩

theorem draw_comm_pilePile (st : State) (c : Card) (b : Base) :
    (st.apply Move.draw >>= fun s => s.apply (Move.pilePile c b)) =
    (st.apply (Move.pilePile c b) >>= fun s => s.apply Move.draw) := by
  refine draw_comm_gen st (Move.pilePile c b) ?_ ?_
  · exact pilePile_blind_none
  · intro s₁ h
    rw [apply_pilePile_iff] at h
    obtain ⟨b₀, hb₀, hne, hcmr, bd, hatt, hst₁⟩ := h
    rw [hst₁]
    rw [apply_pilePile_iff]
    exact ⟨b₀, hb₀, hne, hcmr, bd, hatt, rfl⟩

/-- Each move's legality reads only its components, so neither order
sees the other's writes.  The 49 move pairs split into the 37 with
overlapping components (the hypothesis is absurd — any shared component
witnesses it) and the 12 genuinely disjoint ones (draw with the four
non-stock moves via `draw_comm_*`; reveal/deckStack and deckStack/pilePile
via the blindness kit — both orders land on the same fieldwise merge). -/
theorem commute_of_compsDisjoint (st : State) (m m' : Move)
    (h : ∀ x ∈ Move.comps m, x ∉ Move.comps m') :
    (st.apply m >>= fun s => s.apply m') = (st.apply m' >>= fun s => s.apply m) := by
  cases m with
  | draw =>
      cases m' with
      | draw => exact (h Component.stock (by simp [Move.comps]) (by simp [Move.comps])).elim
      | reveal c => exact draw_comm_reveal st c
      | deckPile _ _ => exact (h Component.stock (by simp [Move.comps]) (by simp [Move.comps])).elim
      | deckStack _ => exact (h Component.stock (by simp [Move.comps]) (by simp [Move.comps])).elim
      | pileStack c => exact draw_comm_pileStack st c
      | stackPile c _ => exact draw_comm_stackPile st c _
      | pilePile c b => exact draw_comm_pilePile st c b
  | reveal c =>
      cases m' with
      | draw => exact (draw_comm_reveal st c).symm
      | reveal _ => exact (h Component.tableau (by simp [Move.comps]) (by simp [Move.comps])).elim
      | deckPile _ _ => exact (h Component.tableau (by simp [Move.comps]) (by simp [Move.comps])).elim
      | deckStack c' =>
          cases hr : st.apply (Move.reveal c) with
          | none =>
              cases hd : st.apply (Move.deckStack c') with
              | none => rfl
              | some sd =>
                  show none = sd.apply (Move.reveal c)
                  rw [apply_deckStack_iff] at hd
                  obtain ⟨hp, hrk, hsd⟩ := hd
                  rw [hsd]
                  exact (reveal_blind_none hr).symm
          | some s₁ =>
              cases hd : st.apply (Move.deckStack c') with
              | none =>
                  show s₁.apply (Move.deckStack c') = none
                  rw [apply_reveal_iff] at hr
                  obtain ⟨htop, r, a, bd, hbot, hpile, hatt, hst₁⟩ := hr
                  rw [hst₁]
                  exact deckStack_blind_none hd
              | some sd =>
                  show s₁.apply (Move.deckStack c') = sd.apply (Move.reveal c)
                  have hrw := hr
                  have hdw := hd
                  rw [apply_reveal_iff] at hr
                  obtain ⟨htop, r, a, bd, hbot, hpile, hatt, hst₁⟩ := hr
                  rw [apply_deckStack_iff] at hd
                  obtain ⟨hp, hrk, hsd⟩ := hd
                  rw [hst₁, hsd]
                  rw [deckStack_blind_some hdw, reveal_blind_some hrw]
                  rw [hst₁, hsd]
      | pileStack _ => exact (h Component.tableau (by simp [Move.comps]) (by simp [Move.comps])).elim
      | stackPile _ _ => exact (h Component.tableau (by simp [Move.comps]) (by simp [Move.comps])).elim
      | pilePile _ _ => exact (h Component.tableau (by simp [Move.comps]) (by simp [Move.comps])).elim
  | deckPile _ _ =>
      cases m' with
      | draw => exact (h Component.stock (by simp [Move.comps]) (by simp [Move.comps])).elim
      | reveal _ => exact (h Component.tableau (by simp [Move.comps]) (by simp [Move.comps])).elim
      | deckPile _ _ => exact (h Component.stock (by simp [Move.comps]) (by simp [Move.comps])).elim
      | deckStack _ => exact (h Component.stock (by simp [Move.comps]) (by simp [Move.comps])).elim
      | pileStack _ => exact (h Component.tableau (by simp [Move.comps]) (by simp [Move.comps])).elim
      | stackPile _ _ => exact (h Component.tableau (by simp [Move.comps]) (by simp [Move.comps])).elim
      | pilePile _ _ => exact (h Component.tableau (by simp [Move.comps]) (by simp [Move.comps])).elim
  | deckStack c =>
      cases m' with
      | draw => exact (h Component.stock (by simp [Move.comps]) (by simp [Move.comps])).elim
      | reveal c' =>
          cases hd : st.apply (Move.deckStack c) with
          | none =>
              cases hr : st.apply (Move.reveal c') with
              | none => rfl
              | some s₁ =>
                  show none = s₁.apply (Move.deckStack c)
                  rw [apply_reveal_iff] at hr
                  obtain ⟨htop, r, a, bd, hbot, hpile, hatt, hst₁⟩ := hr
                  rw [hst₁]
                  exact (deckStack_blind_none hd).symm
          | some sd =>
              cases hr : st.apply (Move.reveal c') with
              | none =>
                  show sd.apply (Move.reveal c') = none
                  rw [apply_deckStack_iff] at hd
                  obtain ⟨hp, hrk, hsd⟩ := hd
                  rw [hsd]
                  exact reveal_blind_none hr
              | some s₁ =>
                  show sd.apply (Move.reveal c') = s₁.apply (Move.deckStack c)
                  have hrw := hr
                  have hdw := hd
                  rw [apply_reveal_iff] at hr
                  obtain ⟨htop, r, a, bd, hbot, hpile, hatt, hst₁⟩ := hr
                  rw [apply_deckStack_iff] at hd
                  obtain ⟨hp, hrk, hsd⟩ := hd
                  rw [hst₁, hsd]
                  rw [reveal_blind_some hrw, deckStack_blind_some hdw]
                  rw [hst₁, hsd]
      | deckPile _ _ => exact (h Component.stock (by simp [Move.comps]) (by simp [Move.comps])).elim
      | deckStack _ => exact (h Component.stock (by simp [Move.comps]) (by simp [Move.comps])).elim
      | pileStack _ => exact (h Component.foundations (by simp [Move.comps]) (by simp [Move.comps])).elim
      | stackPile _ _ =>
          exact (h Component.foundations (by simp [Move.comps]) (by simp [Move.comps])).elim
      | pilePile c' b =>
          cases hd : st.apply (Move.deckStack c) with
          | none =>
              cases hpp : st.apply (Move.pilePile c' b) with
              | none => rfl
              | some s₁ =>
                  show none = s₁.apply (Move.deckStack c)
                  rw [apply_pilePile_iff] at hpp
                  obtain ⟨b₀, hb₀, hne, hcmr, bd, hatt, hst₁⟩ := hpp
                  rw [hst₁]
                  exact (deckStack_blind_none hd).symm
          | some sd =>
              cases hpp : st.apply (Move.pilePile c' b) with
              | none =>
                  show sd.apply (Move.pilePile c' b) = none
                  rw [apply_deckStack_iff] at hd
                  obtain ⟨hp, hrk, hsd⟩ := hd
                  rw [hsd]
                  exact pilePile_blind_none hpp
              | some s₁ =>
                  show sd.apply (Move.pilePile c' b) = s₁.apply (Move.deckStack c)
                  have hppw := hpp
                  have hdw := hd
                  rw [apply_pilePile_iff] at hpp
                  obtain ⟨b₀, hb₀, hne, hcmr, bd, hatt, hst₁⟩ := hpp
                  rw [apply_deckStack_iff] at hd
                  obtain ⟨hp, hrk, hsd⟩ := hd
                  rw [hst₁, hsd]
                  rw [pilePile_blind_some hppw]
                  have hb1 : ({ st with board := bd } : State).apply (Move.deckStack c)
                      = some { sd with board := bd, depths := st.depths } :=
                    deckStack_blind_some hdw
                  rw [hb1]
                  rw [hst₁, hsd]
  | pileStack c =>
      cases m' with
      | draw => exact (draw_comm_pileStack st c).symm
      | reveal _ => exact (h Component.tableau (by simp [Move.comps]) (by simp [Move.comps])).elim
      | deckPile _ _ => exact (h Component.tableau (by simp [Move.comps]) (by simp [Move.comps])).elim
      | deckStack _ => exact (h Component.foundations (by simp [Move.comps]) (by simp [Move.comps])).elim
      | pileStack _ => exact (h Component.tableau (by simp [Move.comps]) (by simp [Move.comps])).elim
      | stackPile _ _ => exact (h Component.tableau (by simp [Move.comps]) (by simp [Move.comps])).elim
      | pilePile _ _ => exact (h Component.tableau (by simp [Move.comps]) (by simp [Move.comps])).elim
  | stackPile c b =>
      cases m' with
      | draw => exact (draw_comm_stackPile st c b).symm
      | reveal _ => exact (h Component.tableau (by simp [Move.comps]) (by simp [Move.comps])).elim
      | deckPile _ _ => exact (h Component.tableau (by simp [Move.comps]) (by simp [Move.comps])).elim
      | deckStack _ => exact (h Component.foundations (by simp [Move.comps]) (by simp [Move.comps])).elim
      | pileStack _ => exact (h Component.tableau (by simp [Move.comps]) (by simp [Move.comps])).elim
      | stackPile _ _ => exact (h Component.tableau (by simp [Move.comps]) (by simp [Move.comps])).elim
      | pilePile _ _ => exact (h Component.tableau (by simp [Move.comps]) (by simp [Move.comps])).elim
  | pilePile c b =>
      cases m' with
      | draw => exact (draw_comm_pilePile st c b).symm
      | reveal _ => exact (h Component.tableau (by simp [Move.comps]) (by simp [Move.comps])).elim
      | deckPile _ _ => exact (h Component.tableau (by simp [Move.comps]) (by simp [Move.comps])).elim
      | deckStack c' =>
          cases hpp : st.apply (Move.pilePile c b) with
          | none =>
              cases hd : st.apply (Move.deckStack c') with
              | none => rfl
              | some sd =>
                  show none = sd.apply (Move.pilePile c b)
                  rw [apply_deckStack_iff] at hd
                  obtain ⟨hp, hrk, hsd⟩ := hd
                  rw [hsd]
                  exact (pilePile_blind_none hpp).symm
          | some s₁ =>
              cases hd : st.apply (Move.deckStack c') with
              | none =>
                  show s₁.apply (Move.deckStack c') = none
                  rw [apply_pilePile_iff] at hpp
                  obtain ⟨b₀, hb₀, hne, hcmr, bd, hatt, hst₁⟩ := hpp
                  rw [hst₁]
                  exact deckStack_blind_none hd
              | some sd =>
                  show s₁.apply (Move.deckStack c') = sd.apply (Move.pilePile c b)
                  have hppw := hpp
                  have hdw := hd
                  rw [apply_pilePile_iff] at hpp
                  obtain ⟨b₀, hb₀, hne, hcmr, bd, hatt, hst₁⟩ := hpp
                  rw [apply_deckStack_iff] at hd
                  obtain ⟨hp, hrk, hsd⟩ := hd
                  rw [hst₁, hsd]
                  have hb1 : ({ st with board := bd } : State).apply (Move.deckStack c')
                      = some { sd with board := bd, depths := st.depths } :=
                    deckStack_blind_some hdw
                  rw [hb1]
                  rw [pilePile_blind_some hppw]
                  rw [hst₁, hsd]
      | pileStack _ => exact (h Component.tableau (by simp [Move.comps]) (by simp [Move.comps])).elim
      | stackPile _ _ => exact (h Component.tableau (by simp [Move.comps]) (by simp [Move.comps])).elim
      | pilePile _ _ => exact (h Component.tableau (by simp [Move.comps]) (by simp [Move.comps])).elim

/-- The C-IND clean sector: draw·reveal always commutes.
Instance of `commute_of_compsDisjoint`. -/
theorem reveal_draw_comm (st : State) (c : Card) :
    (st.apply (Move.reveal c) >>= fun s => s.apply Move.draw) =
    (st.apply Move.draw >>= fun s => s.apply (Move.reveal c)) := by
  refine commute_of_compsDisjoint st (Move.reveal c) Move.draw ?_
  intro x hx
  cases x with
  | tableau => simp [Move.comps]
  | foundations => simp [Move.comps] at hx
  | hidden => simp [Move.comps]
  | stock => simp [Move.comps] at hx

/-- The deal commutes with every non-consuming move: `.draw`'s
component signature is `[.stock]` *alone* and its legality is
unconditional (dealing reads nothing), while the non-consuming moves —
reveal, the two shuffles, pilePile — never touch the stock.  The
generalization of `reveal_draw_comm` from reveal to the whole
non-consuming sector.  The consuming draws (deckPile, deckStack) are
the genuine exceptions: their legality reads the cursor (`maskPos`),
which the deal changes.

This is the canonical form behind the window lemma's replay — deals
float freely through a non-consuming prefix, so the cursor at the
first consumption is a pure function of the deal count — and behind
`solvableEngine_iff_macro`'s regrouping (A3: draws commute with
accommodations).

TODO(proof) [E]: case bash over the five non-consuming moves from the
`apply` defs (the deal writes only `stock.cursor`; the others never
read it), or `commute_of_compsDisjoint` — `.draw`'s comps is
`[.stock]` by definition, disjoint from every non-consuming move's. -/
theorem deal_commutes_nonStock (st : State) (m : Move)
    (hc : m.consumesStock = false) :
    (st.apply m >>= fun s => s.apply Move.draw) =
    (st.apply Move.draw >>= fun s => s.apply m) := sorry

/-! ### The cursor-blindness API — the replay steps, named

Every pace lemma's route repeats the same three steps: non-consuming
moves replay verbatim from a cursor-differing state, and the draw
commitments' successors merge.  Named here so the routes cite them. -/

/-- Non-consuming moves are stock-blind: the result's stock is
bit-for-bit the source's.

TODO(proof) [E]: case bash over the five non-consuming `apply` arms —
none writes the stock. -/
theorem apply_nonConsuming_stock_invar {st st₁ : State} {m : Move}
    (hc : m.consumesStock = false) (h : st.apply m = some st₁) :
    st₁.stock = st.stock := sorry

/-- Non-consuming moves are cursor-blind in legality: from two states
differing only in the stock cursor, the same move applies, with results
again differing only in the cursor.  This is the "replay the prefix
verbatim" step of every pace lemma, named.

TODO(proof) [E]: the legality case bash never reads the stock; the
results' relation follows from `apply_nonConsuming_stock_invar` (the
difference persists through). -/
theorem apply_nonConsuming_cursor_blind {st st' st₁ : State} {m : Move}
    (hc : m.consumesStock = false) (hd : st.diffCursor st')
    (h : st.apply m = some st₁) :
    ∃ st₁' : State, st'.apply m = some st₁' ∧ st₁.diffCursor st₁' := sorry

/-- **The merge, game level (tableau landing)**: from two
cursor-differing states, the same `Draw(c)` commitment to the same base
lands on the *identical* successor — the guard's position is
cards-determined, and the stock successor `(drawTo i).removeAt i` is
position-determined (`Pace.drawCard_cursor_indep`), so nothing of the
source cursor survives.  The "successors merge" step of every pace
lemma, named.

TODO(proof) [E]: unfold `applyDrawTo` — both guards succeed at the
same `i` (`posOf` is cards-only), the board attach is cursor-blind,
and the stock is `drawCard_cursor_indep`. -/
theorem applyDrawTo_merge {st st' st₁ st₁' : State} {c : Card} {b : Base}
    (hd : st.diffCursor st')
    (h₁ : st.applyDrawTo c b = some st₁) (h₂ : st'.applyDrawTo c b = some st₁') :
    st₁ = st₁' := sorry

/-- **The merge, game level (stack landing)**: as `applyDrawTo_merge`,
through `applyDrawStackTo`.

TODO(proof) [E]: as above; the heights step is cursor-blind. -/
theorem applyDrawStackTo_merge {st st' st₁ st₁' : State} {c : Card}
    (hd : st.diffCursor st')
    (h₁ : st.applyDrawStackTo c = some st₁) (h₂ : st'.applyDrawStackTo c = some st₁') :
    st₁ = st₁' := sorry

/-- The bases and cards a move reads or writes (state-dependent — the
run under a `pilePile`, the boundary under a `reveal`). -/
def Move.touch (st : State) : Move → List Base × List Card
  | .draw => ([], [])
  | .reveal c =>
      (match st.board.bottomOf c with
       | some (Sum.inr r) =>
           (match st.pileOfTopHidden r with
            | some a => [st.hiddenBase a]
            | none => [Sum.inr r], [c, r])
       | _ => ([], [c]))
  | .deckPile c b => ([b], [c])
  | .deckStack c => ([], [c])
  | .pileStack c => ((st.board.bottomOf c).toList, [c])
  | .stackPile c b => ([b], [c])
  | .pilePile c b => (b :: (st.board.bottomOf c).toList, c :: st.board.aboveOf c)

/-- Disjoint touch-sets (bases and cards). -/
def disjointTouch (t₁ t₂ : List Base × List Card) : Prop :=
  (∀ b ∈ t₁.1, b ∉ t₂.1) ∧ (∀ c ∈ t₁.2, c ∉ t₂.2)

/-- The fine-grained commutation schema — the type-ball interaction
lemma.  Moves with disjoint touch-sets commute (given both orders are
defined).  TODO. -/
theorem commute_of_disjoint_touch {st : State} {m m' : Move} {st₂ st₃ : State}
    (hdisj : disjointTouch (m.touch st) (m'.touch st))
    (h₁ : (st.apply m >>= fun s => s.apply m') = some st₂)
    (h₂ : (st.apply m' >>= fun s => s.apply m) = some st₃) : st₂ = st₃ := sorry

/-- **C13, generalized**: Draw-commitments at cycle-adjacent positions
commute (adjacency modulo the cycle length — the wrap counts).
TODO: `Cycle.removeIdx_comm` + cursor arithmetic. -/
theorem drawTo_comm_modAdjacent {st : State} {c c' : Card} {b b' : Base} {i j len : Nat}
    (hlen : st.stock.cards.length = len) (hadj : (i + 1) % len = j)
    (hic : st.stock.posOf c = some i) (hjc : st.stock.posOf c' = some j)
    (hbb : b ≠ b') {st₂ st₄ : State}
    (h₂ : (st.applyDrawTo c b >>= fun s => s.applyDrawTo c' b') = some st₂)
    (h₄ : (st.applyDrawTo c' b' >>= fun s => s.applyDrawTo c b) = some st₄) :
    st₂ = st₄ := sorry

/-- **C13's boundary**: non-adjacent Draw-commitments land on different
cursors — the end states differ (the cards agree, by `removeIdx_comm`;
only the cursor position diverges).  The engine's sweep/
canonicalization is what recovers commutation beyond adjacency — the
C-IND landscape's residual.  TODO. -/
theorem drawTo_nonadjacent_diverge {st : State} {c c' : Card} {b b' : Base} {i j : Nat}
    (hij : i < j) (hne : i + 1 ≠ j)
    (hic : st.stock.posOf c = some i) (hjc : st.stock.posOf c' = some j)
    (hbb : b ≠ b') {st₂ st₄ : State}
    (h₂ : (st.applyDrawTo c b >>= fun s => s.applyDrawTo c' b') = some st₂)
    (h₄ : (st.applyDrawTo c' b' >>= fun s => s.applyDrawTo c b) = some st₄) :
    st₂ ≠ st₄ := sorry

/-! ## 4. Structure — the matching is a forest

The rank grading along `topOf`-edges: everything above a card is
strictly lower rank.  This kills cycles in the matching (the reason
`Base`'s typing alone did not need to).
-/

/-- TODO(proof): induction along `aboveOf` using the WF edge legality
(the `canSitOn` disjunct). -/
theorem aboveOf_rank_grading {st : State} (hwf : st.WF) (c : Card) :
    ∀ d ∈ st.board.aboveOf c, d.rank.toIdx < c.rank.toIdx := sorry

/-- Acyclicity, from the grading.  TODO. -/
theorem aboveOf_irrefl {st : State} (hwf : st.WF) (c : Card) :
    c ∉ st.board.aboveOf c := sorry

/-! ## 5. The deck integration — the jump IS the physical game

The Draw commitments (`applyDrawTo`, `applyDrawStackTo`) are the
derived jumps; these are the statements that the guard makes them
exactly the physical game: jump-then-play ≡ deal-until-then-play.
C9's premise, as theorems, at every draw step (at step 1 the guard is
trivial — `reachablePos_step1`).  The bridge to `toEngine_simulates`
consumes these. -/

/-- **The jump-soundness theorem**: the tableau-outcome Draw
commitment equals dealing until `c` is the waste top, then playing it
with the physical deck move — the reachable-position guard is exactly
the reachability of that deal sequence.

TODO(proof) [H]: → the guard gives the deal count (maskPos ↔
deal-iteration reachability — the prefix walk of `realizes_iff_stepsOK`;
`pos_shift`/`cursor_after` supply the positions), then
`apply_deckPile_iff`'s shape.  ← contrapositive by the same
correspondence: a reaching sequence puts the position in the mask. -/
theorem applyDrawTo_eq_dealPlay {st : State} (hwf : st.WF) {c : Card} {b : Base}
    {st'' : State} :
    st.applyDrawTo c b = some st'' ↔
      ∃ k st₁, st.run (List.replicate k Move.draw) = some st₁ ∧
        st₁.apply (Move.deckPile c b) = some st'' := sorry

/-- The stack-outcome twin: the safe-stack commitment equals dealing
to `c`, then the physical `deckStack`.  TODO(proof) [H]: as
`applyDrawTo_eq_dealPlay`, through `apply_deckStack_iff`. -/
theorem applyDrawStackTo_eq_dealPlay {st : State} (hwf : st.WF) {c : Card}
    {st'' : State} :
    st.applyDrawStackTo c = some st'' ↔
      ∃ k st₁, st.run (List.replicate k Move.draw) = some st₁ ∧
        st₁.apply (Move.deckStack c) = some st'' := sorry
