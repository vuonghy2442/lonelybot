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

/- A full pass plus the wrap deal returns to the pass start: from
cursor 0, dealing everything (the clamp passes the last card) and
wrapping lands home — the deal cycle's period is `⌈n/s⌉ + 1`, at any
step `s ≥ 1` (deck.rs `offset`'s periodicity).  Supersedes the old
rotate-form "a full rotation is the identity", an artifact of the
jump semantics.  PROVEN below, with the deal-iteration kit (§5's
`run_dealIter` is the unpacking step — the statement lives there,
after the kit it needs). -/

/-- A commitment: no play returns to the state after it. -/
def irreversibleAt (st : State) (m : Move) : Prop :=
  ∀ st₁ play, st.apply m = some st₁ → st₁.run play ≠ some st

/-! The irreversibility trio — `irreversible_reveal`,
`irreversible_deckPile`, `irreversible_deckStack` — is proved in
Progress.lean (relocated 2026-09-13): the run-level monotonicity
lemmas it consumes (`run_totalDepth_le`, `run_stockLen_le`) live
there, and Progress imports this file, so the statements moved down
the import edge rather than duplicating the machinery. -/

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

/-- The worry-back return: after a `stackPile`, the taken-back card is
the foundation top and (WF: a foundation-passed card carries no tenant
— `founds_gone` + `board_edges`) nothing sits on it, so `pileStack`
takes the successor straight back.  Dominance's
`stackPile_pileStack_cancel` restated for the upstream file (Dominance
imports this one). -/
theorem stackPile_pileStack_return {st : State} {c : Card} {b : Base} {s₁ : State}
    (hwf : st.WF) (hsp : st.apply (Move.stackPile c b) = some s₁) :
    s₁.apply (Move.pileStack c) = some st := by
  rw [apply_stackPile_iff] at hsp
  obtain ⟨hg, hcp, bd, hatt, hs₁⟩ := hsp
  -- c is foundation-passed: neither visible nor hidden anywhere
  have hlt : c.rank.toIdx < st.heights c.suit := by omega
  obtain ⟨hvis, _, hhid⟩ := hwf.founds_gone c hlt
  have hnc : st.board.topOf (Sum.inr c) = none := by
    by_cases ht : st.board.topOf (Sum.inr c) = none
    · exact ht
    · exfalso
      obtain ⟨y, hy⟩ : ∃ y, st.board.topOf (Sum.inr c) = some y := by
        cases hh : st.board.topOf (Sum.inr c) with
        | none => rw [hh] at ht; exact absurd ht (by simp)
        | some y => exact ⟨y, rfl⟩
      obtain ⟨_, hbase⟩ := hwf.board_edges (Sum.inr c) y hy
      rcases hbase with ⟨_, _, _, _, hbc⟩ | ⟨hbd, _⟩
      · rcases hbc with ⟨a', hth⟩ | hbd
        · exact hhid a' (mem_of_getLast hth)
        · have hiv : (st.board.bottomOf c).isSome = false := hvis
          rw [hiv] at hbd
          exact Bool.noConfusion hbd
      · have hiv : (st.board.bottomOf c).isSome = false := hvis
        rw [hiv] at hbd
        exact Bool.noConfusion hbd
  -- b was free (the worry-back's own guard) and is not c's seat
  have hcpf := hcp
  simp only [State.canPlace] at hcpf
  have hfree : st.board.topOf b = none :=
    of_decide_eq_true (Bool.and_eq_true_iff.mp hcpf).1
  have hbne : Sum.inr c ≠ b := by
    cases b with
    | inl a => intro hcon; simp at hcon
    | inr d =>
        have hcp' := hcp
        simp only [State.canPlace] at hcp'
        obtain ⟨_, hivd⟩ := Bool.and_eq_true_iff.mp hcp'
        obtain ⟨hivd, _⟩ := Bool.and_eq_true_iff.mp hivd
        intro hcon
        injection hcon with hcd
        rw [← hcd] at hivd
        rw [hvis] at hivd
        exact Bool.noConfusion hivd
  -- the re-stack at the successor
  rw [hs₁]
  rw [apply_pileStack_iff]
  refine ⟨?_, b, ?_, ?_, ?_⟩
  · show bd.topOf (Sum.inr c) = none
    rw [Board.attach_topOf_ne _ _ _ hatt hbne]
    exact hnc
  · show bd.bottomOf c = some b
    exact (Board.bottomOf_eq bd c b).mpr (Board.attach_topOf _ _ _ hatt)
  · show c.rank.toIdx =
      (if c.suit = c.suit then st.heights c.suit - 1 else st.heights c.suit)
    rw [if_pos rfl]
    omega
  · show st = { { st with
        board := bd,
        heights := fun s => if s = c.suit then st.heights s - 1 else st.heights s } with
      board := bd.detach b,
      heights := fun s => if s = c.suit then
        (if s = c.suit then st.heights s - 1 else st.heights s) + 1
        else (if s = c.suit then st.heights s - 1 else st.heights s) }
    have hbdb : bd.detach b = st.board := by
      refine Board.ext_topOf (funext (fun b' => ?_))
      by_cases hbb : b' = b
      · rw [hbb, Board.detach_topOf, hfree]
      · rw [Board.detach_topOf_ne _ _ _ hbb, Board.attach_topOf_ne _ _ _ hatt hbb]
    have hhh : (fun s => if s = c.suit then
        (if s = c.suit then st.heights s - 1 else st.heights s) + 1
        else (if s = c.suit then st.heights s - 1 else st.heights s)) = st.heights := by
      funext s
      by_cases hsc : s = c.suit
      · subst hsc
        rw [if_pos rfl, if_pos rfl]
        omega
      · rw [if_neg hsc, if_neg hsc]
    exact state_ext rfl hbdb.symm hhh.symm rfl rfl rfl

/-- The worry-back half of the accommodation step: a legal `stackPile`
never hurts — `pileStack` takes the successor straight back (nothing
sits on a foundation-passed card), and the winning play prepends. -/
theorem solvable_of_stackPile {st : State} {c : Card} {b : Base} {s₁ : State}
    (hwf : st.WF) (hm : st.apply (Move.stackPile c b) = some s₁)
    (hsol : st.solvableFrom) : s₁.solvableFrom := by
  obtain ⟨win, w, hwrun, hwin⟩ := hsol
  refine ⟨Move.pileStack c :: win, w, ?_, hwin⟩
  show (match s₁.apply (Move.pileStack c) with
    | some st' => st'.run win
    | none => none) = some w
  rw [stackPile_pileStack_return hwf hm]
  exact hwrun

set_option linter.unusedVariables false in
/-- The stack half of the accommodation step — the isolated B4 reshape
crux (this file's only `sorry`): a legal `pileStack` never hurts
solvability.  Together with `solvable_of_stackPile` this is the whole
content of the hard direction; the play-level lifting below is proved.
TODO(proof) [H].  PLAN (verify, don't trust; the wave-8 sketch stands,
with one correction — the worry-back half is DONE above):

Induct on the winning play π from `st`, splitting on π's first move.
* `pileStack c` itself — delete it: `s₁` runs π's tail directly.
* Moves commuting with the `c`-difference — replay and induct: no move
  of π can seat at `c`'s base `b` while `c` occupies it, and the
  blindness kit covers the components `c` does not touch.
* Moves seating ON `c` (`deckPile`/`stackPile`/`pilePile` x `(inr c)`)
  — the park.  KEY STRUCTURE (the catch-22 that makes the reshape
  work): every park is transient — `c`'s suit must pass rung
  `toIdx c` before winning, the rung card is `c` itself, and a stacked
  `c` admits no tenant, so the parked `x` leaves before the rung
  passes; `x`'s exit is its own `pileStack` (rung-gated but
  `c`-suit-independent — fires equally from `s₁`) or a reseat on a
  rank-mate; delay the rung past the park and the delete-strategy
  applies from the other side.
* `stackPile` of `c`'s suit at the shifted rung `toIdx c - 1` — the
  excursion pair (net identity): replay at the shifted height.
  (`deckStack` of a phantom stock copy of `c` is excluded by
  `vis_off_cycle`.)

The endgame is the return-base crux: when `c`'s base was
deal-adjacent, `canReturnBase` fails and the worry-back lands on a
rank-mate instead — the Dominance ledger's N-half, the same root.  The
returnable half needs `pileStack_stackPile_roundtrip` plus the guard
bundle, whose visibility piece (`vis_base_of_notLocked`) currently
lives downstream in Dominance — lift it here first (re-proving
`bottomOf_detach_self` from Bridge on the way). -/
theorem solvable_of_pileStack {st : State} (hwf : st.WF) {c : Card} {s₁ : State}
    (hm : st.apply (Move.pileStack c) = some s₁) (hsol : st.solvableFrom) :
    s₁.solvableFrom := sorry

/-- The one-step core: an accommodation move that succeeds preserves
solvability — dispatch to the two halves. -/
theorem solvable_of_accomm_step {st : State} {m : Move} {s₂ : State}
    (hwf : st.WF) (hm : st.apply m = some s₂) (hsol : st.solvableFrom)
    (hmacc : m.isAccommodation = true) : s₂.solvableFrom := by
  cases m with
  | pileStack c => exact solvable_of_pileStack hwf hm hsol
  | stackPile c b => exact solvable_of_stackPile hwf hm hsol
  | draw | reveal _ | deckPile _ _ | deckStack _ | pilePile _ _ =>
      exact absurd hmacc (by simp [Move.isAccommodation])

/-- The accommodation reduction, hard direction — the reshape lemma
(B4): a winning play survives the cards having been shuffled through
the foundations.

STATEMENT REPAIRED (2026-09-13): as staged (no WF hypothesis) it was
FALSE — prover-confirmed witness `Temp/opencode/B4Witness.lean`
(axiom-clean facts): a WON state with a *phantom tenant* (♠2 seated on
base `inr ♠K` while ♠K is unplaced — exactly what WF's `board_edges`
forbids) and junk occupying every anchor but p0; the accommodation
`[stackPile ♠K p0]` seats the king under its tenant, and the successor
is a total deadlock (only `draw` fires, as the identity) — ♠K can never
re-stack, so it is unsolvable while the source is already won.  Repair:
add `(hwf : st.WF)` — the design docs' invariant, preserved by the
accommodation moves themselves (`apply_wf`).  No downstream users of
the old statement existed.

The proof decomposes over the accommodation play (each move is a
`pileStack` or a `stackPile`): each step preserves WF (`apply_wf`) and
solvability (`solvable_of_accomm_step`), and the induction carries
the winning play through the shuffle. -/
private theorem solvable_accommodates_aux {st' : State} : ∀ (play : List Move),
    (∀ m ∈ play, m.isAccommodation = true) → ∀ (st : State),
    st.WF → st.solvableFrom → st.run play = some st' → st'.solvableFrom := by
  intro play
  induction play with
  | nil =>
      intro _hall st _hwf hsol hrun
      have hst : st = st' := Option.some.inj hrun
      subst hst
      exact hsol
  | cons m ms ih =>
      intro hall st hwf hsol hrun
      simp only [State.run] at hrun
      cases hm : st.apply m with
      | none =>
          rw [hm] at hrun
          simp at hrun
      | some s₂ =>
          rw [hm] at hrun
          have hrun₂ : s₂.run ms = some st' := hrun
          have hs₂ := solvable_of_accomm_step hwf hm hsol (hall m (by simp))
          exact ih (fun m' hm' => hall m' (by simp [hm'])) s₂
            (apply_wf hwf m s₂ hm) hs₂ hrun₂

theorem solvable_accommodates {st st' : State} (hwf : st.WF)
    (hacc : accommodates st st') (hsol : st.solvableFrom) : st'.solvableFrom := by
  obtain ⟨play, hrun, hall⟩ := hacc
  exact solvable_accommodates_aux play hall st hwf hsol hrun

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

/-- `pileStack`'s some-form, stock-only replacement: the guards read
only the board and heights (both untouched by a stock with-update), and
the successor carries the replaced stock along. -/
theorem pileStack_blind_some {st : State} {c : Card} {cy : Cycle Card} {st₁ : State}
    (h : st.apply (Move.pileStack c) = some st₁) :
    ({ st with stock := cy } : State).apply (Move.pileStack c)
      = some { st₁ with stock := cy } := by
  rw [apply_pileStack_iff] at h
  obtain ⟨htop, b, hb, hrk, hst⟩ := h
  rw [hst]
  rw [apply_pileStack_iff]
  exact ⟨htop, b, hb, hrk, rfl⟩

/-- `stackPile`'s some-form, stock-only replacement. -/
theorem stackPile_blind_some {st : State} {c : Card} {b : Base} {cy : Cycle Card} {st₁ : State}
    (h : st.apply (Move.stackPile c b) = some st₁) :
    ({ st with stock := cy } : State).apply (Move.stackPile c b)
      = some { st₁ with stock := cy } := by
  rw [apply_stackPile_iff] at h
  obtain ⟨hrk, hcp, bd, hatt, hst⟩ := h
  rw [hst]
  rw [apply_stackPile_iff]
  exact ⟨hrk, hcp, bd, hatt, rfl⟩

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

Route: `draw` composed with itself is the same term on both sides; the
four other non-consuming moves are the proven `draw_comm_*` instances;
the two card draws contradict `consumesStock = false`. -/
theorem deal_commutes_nonStock (st : State) (m : Move)
    (hc : m.consumesStock = false) :
    (st.apply m >>= fun s => s.apply Move.draw) =
    (st.apply Move.draw >>= fun s => s.apply m) := by
  cases m with
  | draw => rfl
  | reveal c => exact (draw_comm_reveal st c).symm
  | deckPile c b => exact absurd hc (by simp [Move.consumesStock])
  | deckStack c => exact absurd hc (by simp [Move.consumesStock])
  | pileStack c => exact (draw_comm_pileStack st c).symm
  | stackPile c b => exact (draw_comm_stackPile st c b).symm
  | pilePile c b => exact (draw_comm_pilePile st c b).symm

/-! ### The cursor-blindness API — the replay steps, named

Every pace lemma's route repeats the same three steps: non-consuming
moves replay verbatim from a cursor-differing state, and the draw
commitments' successors merge.  Named here so the routes cite them. -/

/-- Non-consuming moves are stock-blind: the result's stock is
bit-for-bit the source's.

STATEMENT REPAIR (2026-09-13, prover-confirmed witness
`Temp\opencode\StockInvarWitness.lean`): as originally staged (the
`consumesStock = false` guard alone) this is FALSE for `m = Move.draw` —
the deal is non-consuming (it advances the pace, not a card down) but
it *writes* the stock cursor: from cursor 0 with a nonempty stock and
step 1 the deal lands at cursor 1, so `st₁.stock ≠ st.stock`.  Minimal
repair: the `m ≠ Move.draw` hypothesis.  The four remaining arms
(reveal, the two shuffles, pilePile) are with-updates off the stock. -/
theorem apply_nonConsuming_stock_invar {st st₁ : State} {m : Move}
    (hc : m.consumesStock = false) (hm : m ≠ Move.draw) (h : st.apply m = some st₁) :
    st₁.stock = st.stock := by
  cases m with
  | draw => exact absurd rfl hm
  | reveal c =>
      rw [apply_reveal_iff] at h
      obtain ⟨-, r, a, bd, -, -, -, hst⟩ := h
      rw [hst]
  | deckPile c b => exact absurd hc (by simp [Move.consumesStock])
  | deckStack c => exact absurd hc (by simp [Move.consumesStock])
  | pileStack c =>
      rw [apply_pileStack_iff] at h
      obtain ⟨-, b, -, -, hst⟩ := h
      rw [hst]
  | stackPile c b =>
      rw [apply_stackPile_iff] at h
      obtain ⟨-, -, bd, -, hst⟩ := h
      rw [hst]
  | pilePile c b =>
      rw [apply_pilePile_iff] at h
      obtain ⟨-, -, -, -, bd, -, hst⟩ := h
      rw [hst]

/-- Non-consuming moves are cursor-blind in legality: from two states
differing only in the stock cursor, the same move applies, with results
again differing only in the cursor.  This is the "replay the prefix
verbatim" step of every pace lemma, named.

Route: `st'` *is* `st` with the stock field replaced (all other fields
agree, by `diffCursor`), so the blindness kit applies the move from the
stock/heights-replaced state and carries the replacement into the
successor; the draw arm goes through `dealOnce_cards` directly. -/
theorem apply_nonConsuming_cursor_blind {st st' st₁ : State} {m : Move}
    (hc : m.consumesStock = false) (hd : st.diffCursor st')
    (h : st.apply m = some st₁) :
    ∃ st₁' : State, st'.apply m = some st₁' ∧ st₁.diffCursor st₁' := by
  have hst'eq : { st with stock := st'.stock } = st' :=
    state_ext hd.1 hd.2.1 hd.2.2.1 hd.2.2.2.1 rfl hd.2.2.2.2.2
  cases m with
  | draw =>
      rw [apply_draw_iff] at h
      have hs : st'.apply Move.draw
          = some { st' with stock := st'.stock.dealOnce st'.drawStep } := rfl
      refine ⟨{ st' with stock := st'.stock.dealOnce st'.drawStep }, hs, ?_⟩
      rw [h]
      refine ⟨hd.1, hd.2.1, hd.2.2.1, hd.2.2.2.1, ?_, hd.2.2.2.2.2⟩
      show (st.stock.dealOnce st.drawStep).cards
          = (st'.stock.dealOnce st'.drawStep).cards
      rw [Cycle.dealOnce_cards, Cycle.dealOnce_cards, hd.2.2.2.2.1]
  | reveal c =>
      have hblind := reveal_blind_some (cy := st'.stock) (hs := st.heights) h
      have hst'2 : { st with stock := st'.stock, heights := st.heights } = st' :=
        state_ext hd.1 hd.2.1 hd.2.2.1 hd.2.2.2.1 rfl hd.2.2.2.2.2
      rw [hst'2] at hblind
      rw [apply_reveal_iff] at h
      obtain ⟨-, r, a, bd, -, -, -, hst⟩ := h
      refine ⟨{ st₁ with stock := st'.stock, heights := st.heights }, hblind, ?_⟩
      rw [hst]
      exact ⟨rfl, rfl, rfl, rfl, hd.2.2.2.2.1, rfl⟩
  | deckPile c b => exact absurd hc (by simp [Move.consumesStock])
  | deckStack c => exact absurd hc (by simp [Move.consumesStock])
  | pileStack c =>
      have hblind := pileStack_blind_some (cy := st'.stock) h
      rw [hst'eq] at hblind
      rw [apply_pileStack_iff] at h
      obtain ⟨-, b, -, -, hst⟩ := h
      refine ⟨{ st₁ with stock := st'.stock }, hblind, ?_⟩
      rw [hst]
      exact ⟨rfl, rfl, rfl, rfl, hd.2.2.2.2.1, rfl⟩
  | stackPile c b =>
      have hblind := stackPile_blind_some (cy := st'.stock) h
      rw [hst'eq] at hblind
      rw [apply_stackPile_iff] at h
      obtain ⟨-, -, bd, -, hst⟩ := h
      refine ⟨{ st₁ with stock := st'.stock }, hblind, ?_⟩
      rw [hst]
      exact ⟨rfl, rfl, rfl, rfl, hd.2.2.2.2.1, rfl⟩
  | pilePile c b =>
      have hblind := pilePile_blind_some (cy := st'.stock) (hs := st.heights) h
      have hst'2 : { st with stock := st'.stock, heights := st.heights } = st' :=
        state_ext hd.1 hd.2.1 hd.2.2.1 hd.2.2.2.1 rfl hd.2.2.2.2.2
      rw [hst'2] at hblind
      rw [apply_pilePile_iff] at h
      obtain ⟨-, -, -, -, bd, -, hst⟩ := h
      refine ⟨{ st₁ with stock := st'.stock, heights := st.heights }, hblind, ?_⟩
      rw [hst]
      exact ⟨rfl, rfl, rfl, rfl, hd.2.2.2.2.1, rfl⟩

/-- `posOf` runs the finder over the cards alone (the cursor is never
read) — the `diffCursor` stock transfer. -/
theorem posOf_cards_eq {c : Card} {cy cy' : Cycle Card}
    (h : cy.cards = cy'.cards) : cy.posOf c = cy'.posOf c := by
  show Cycle.findFirstIdx (fun c' => decide (c' = c)) cy.cards
     = Cycle.findFirstIdx (fun c' => decide (c' = c)) cy'.cards
  rw [h]

/-- **The merge, game level (tableau landing)**: from two
cursor-differing states, the same `Draw(c)` commitment to the same base
lands on the *identical* successor — the guard's position is
cards-determined (`posOf` never reads the cursor), the attach is
cursor-blind, and the stock successor `(drawTo i).removeAt i` is
position-determined (`removeAt_drawTo`).  The "successors merge" step
of every pace lemma, named. -/
theorem applyDrawTo_merge {st st' st₁ st₁' : State} {c : Card} {b : Base}
    (hd : st.diffCursor st')
    (h₁ : st.applyDrawTo c b = some st₁) (h₂ : st'.applyDrawTo c b = some st₁') :
    st₁ = st₁' := by
  obtain ⟨i, bd, hr₁, hatt₁, hst₁⟩ := applyDrawTo_shape h₁
  obtain ⟨i', bd', hr₂, hatt₂, hst₂⟩ := applyDrawTo_shape h₂
  have hpos : st.stock.posOf c = st'.stock.posOf c := posOf_cards_eq hd.2.2.2.2.1
  have hii : i = i' := by
    have e1 := State.reachablePos_posOf hr₁
    have e2 := State.reachablePos_posOf hr₂
    rw [hpos] at e1
    exact Option.some.inj (e1.symm.trans e2)
  subst hii
  have hbb : st'.board.attach b c = st.board.attach b c := by rw [hd.2.1]
  rw [hbb] at hatt₂
  have hbd : bd = bd' := Option.some.inj (hatt₁.symm.trans hatt₂)
  subst hbd
  rw [hst₁, hst₂]
  refine state_ext hd.1 ?_ hd.2.2.1 hd.2.2.2.1 ?_ hd.2.2.2.2.2
  · rfl
  · rw [hd.2.2.2.2.1]

/-- **The merge, game level (stack landing)**: as `applyDrawTo_merge`,
through `applyDrawStackTo` — the rank guard reads the heights (equal by
`diffCursor`), the splice is position-determined, the heights bump is
cursor-blind. -/
theorem applyDrawStackTo_merge {st st' st₁ st₁' : State} {c : Card}
    (hd : st.diffCursor st')
    (h₁ : st.applyDrawStackTo c = some st₁) (h₂ : st'.applyDrawStackTo c = some st₁') :
    st₁ = st₁' := by
  have hpos : st.stock.posOf c = st'.stock.posOf c := posOf_cards_eq hd.2.2.2.2.1
  simp only [State.applyDrawStackTo] at h₁ h₂
  cases hr₁ : st.reachablePos c with
  | none => rw [hr₁] at h₁; exact absurd h₁ (by simp)
  | some i =>
      rw [hr₁] at h₁
      cases hr₂ : st'.reachablePos c with
      | none => rw [hr₂] at h₂; exact absurd h₂ (by simp)
      | some i' =>
          rw [hr₂] at h₂
          have hii : i = i' := by
            have e1 := State.reachablePos_posOf hr₁
            have e2 := State.reachablePos_posOf hr₂
            rw [hpos] at e1
            exact Option.some.inj (e1.symm.trans e2)
          subst hii
          have h₁' : (if c.rank.toIdx = st.heights c.suit then
              some { st with
                stock := (st.stock.drawTo i).removeAt i,
                heights := fun s => if s = c.suit then st.heights s + 1 else st.heights s }
              else none) = some st₁ := h₁
          have h₂' : (if c.rank.toIdx = st'.heights c.suit then
              some { st' with
                stock := (st'.stock.drawTo i).removeAt i,
                heights := fun s => if s = c.suit then st'.heights s + 1 else st'.heights s }
              else none) = some st₁' := h₂
          by_cases hrk : c.rank.toIdx = st.heights c.suit
          · rw [if_pos hrk, Option.some.injEq] at h₁'
            rw [if_pos (hrk.trans (congrFun (hd.2.2.1) c.suit)), Option.some.injEq] at h₂'
            rw [← h₁', ← h₂']
            refine state_ext hd.1 hd.2.1 ?_ hd.2.2.2.1 ?_ hd.2.2.2.2.2
            · funext s
              by_cases hsc : s = c.suit
              · show (if s = c.suit then st.heights s + 1 else st.heights s)
                  = (if s = c.suit then st'.heights s + 1 else st'.heights s)
                rw [if_pos hsc, if_pos hsc]
                exact congrArg (· + 1) (congrFun (hd.2.2.1) s)
              · show (if s = c.suit then st.heights s + 1 else st.heights s)
                  = (if s = c.suit then st'.heights s + 1 else st'.heights s)
                rw [if_neg hsc, if_neg hsc]
                exact congrFun (hd.2.2.1) s
            · rw [Cycle.removeAt_drawTo i st.stock, Cycle.removeAt_drawTo i st'.stock,
                hd.2.2.2.2.1]
          · rw [if_neg hrk] at h₁'; exact absurd h₁' (by simp)

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

/-! ### The fine-commutation kit

Board edits are single-base `topOf` updates (attach writes its base,
detach clears one), so edits at pairwise-distinct bases compose
order-independently (`attach_attach_comm`, and the attach/detach and
detach/detach forms below); a card's `bottomOf` survives every edit
that neither seats nor detaches it; the hidden-pile views
(`topHidden`, `pileOfTopHidden`, `hiddenBase`) read only the deal and
depths, so they are board/stock/heights-blind; and the heights
updates (`±1` at a suit) commute as function updates. -/

/-- Attach preserves another card's seat (the equality form; Macro's
`bottomOf_attach_of_ne` restated for the upstream file). -/
theorem bottomOf_attach_ne {bd : Board} {b : Base} {c x : Card} {bd' : Board}
    (hatt : bd.attach b c = some bd') (hne : x ≠ c) :
    bd'.bottomOf x = bd.bottomOf x := by
  have hfree : bd.topOf b = none := ((Board.attach_eq_some_iff bd b c).mp (by rw [hatt]; simp)).1
  have hself : bd'.topOf b = some c := Board.attach_topOf bd b c hatt
  show findFirst (fun β => decide (bd'.topOf β = some x)) Board.enumBase
     = findFirst (fun β => decide (bd.topOf β = some x)) Board.enumBase
  exact findFirst_congr (fun β => by
    by_cases hβ : β = b
    · subst hβ
      have hcx : c ≠ x := fun hh => hne hh.symm
      rw [hself, hfree]
      simp [hcx]
    · rw [Board.attach_topOf_ne bd b c hatt hβ]) Board.enumBase

/-- An attach and a detach at distinct bases commute (both orders'
attaches succeed — the commutation's own hypothesis shape). -/
theorem attach_detach_comm {bd : Board} {b b' : Base} {c : Card} {bd₁ bd₂ : Board}
    (hne : b ≠ b') (h₁ : bd.attach b c = some bd₁)
    (h₂ : (bd.detach b').attach b c = some bd₂) :
    bd₁.detach b' = bd₂ := by
  refine Board.ext_topOf (funext (fun x => ?_))
  by_cases hxb : x = b
  · rw [hxb, Board.detach_topOf_ne bd₁ b' b hne, Board.attach_topOf bd b c h₁,
      Board.attach_topOf (bd.detach b') b c h₂]
  · by_cases hxb' : x = b'
    · rw [hxb', Board.detach_topOf bd₁ b', Board.attach_topOf_ne (bd.detach b') b c h₂
          (Ne.symm hne), Board.detach_topOf bd b']
    · rw [Board.detach_topOf_ne bd₁ b' x hxb', Board.attach_topOf_ne bd b c h₁ hxb,
        Board.attach_topOf_ne (bd.detach b') b c h₂ hxb, Board.detach_topOf_ne bd b' x hxb']

/-- Two detaches at distinct bases commute. -/
theorem detach_detach_comm {bd : Board} {b b' : Base} (hne : b ≠ b') :
    (bd.detach b).detach b' = (bd.detach b').detach b := by
  refine Board.ext_topOf (funext (fun x => ?_))
  by_cases hxb : x = b
  · rw [hxb, Board.detach_topOf_ne (bd.detach b) b' b hne, Board.detach_topOf bd b,
      Board.detach_topOf (bd.detach b') b]
  · by_cases hxb' : x = b'
    · rw [hxb', Board.detach_topOf (bd.detach b) b',
        Board.detach_topOf_ne (bd.detach b') b b' (Ne.symm hne), Board.detach_topOf bd b']
    · rw [Board.detach_topOf_ne (bd.detach b) b' x hxb', Board.detach_topOf_ne bd b x hxb,
        Board.detach_topOf_ne (bd.detach b') b x hxb, Board.detach_topOf_ne bd b' x hxb']

/-- When the shorter take-slice's last differs from the longer's, the
longer slice ends `[…, r', r]` — reveal's redirect corner: the base
under the boundary is the slice the depth-step exposes. -/
theorem take_reverse_drop1 {l : List Card} {n : Nat} {r r' : Card}
    (hr : (l.take n).getLast? = some r) (hr' : (l.take (n-1)).getLast? = some r')
    (hne : r ≠ r') : ((l.take n).reverse.drop 1).head? = some r' := by
  have hn : 0 < n := by
    cases n with
    | zero => exact absurd hr (by simp)
    | succ m => omega
  have hsplit : l.take n = l.take (n-1) ++ (l.drop (n-1)).take 1 := by
    have h : l.take ((n-1) + 1) = l.take (n-1) ++ (l.drop (n-1)).take 1 := List.take_add
    have hn1 : (n-1) + 1 = n := by omega
    rw [hn1] at h
    exact h
  cases hdrop : (l.drop (n-1)) with
  | nil =>
      have h1 : (l.drop (n-1)).take 1 = ([] : List Card) := by rw [hdrop]; rfl
      rw [h1, List.append_nil] at hsplit
      rw [hsplit] at hr
      exact absurd (Option.some.inj (hr.symm.trans hr')) hne
  | cons d ds =>
      have h1 : (d :: ds).take 1 = [d] := rfl
      rw [hsplit, hdrop, h1, List.reverse_append, List.reverse_singleton, List.cons_append]
      show ((l.take (n-1)).reverse).head? = some r'
      rw [head?_reverse_eq_getLast?]
      exact hr'

/-- The hidden-pile views are blind to the board, stock, and heights:
two states agreeing on deal and depths have the same `topHidden`
pointwise (hence the same `pileOfTopHidden` and `hiddenBase`). -/
theorem topHidden_congr {st st' : State} (hdeal : st.deal = st'.deal)
    (hdpt : st.depths = st'.depths) (a : Anchor) :
    st.topHidden a = st'.topHidden a := by
  show ((st.deal.piles a).take (st.depths a)).getLast?
      = ((st'.deal.piles a).take (st'.depths a)).getLast?
  rw [show st'.deal.piles a = st.deal.piles a from by rw [hdeal], hdpt]

theorem pileOfTopHidden_congr {st st' : State} (hdeal : st.deal = st'.deal)
    (hdpt : st.depths = st'.depths) (r : Card) :
    st.pileOfTopHidden r = st'.pileOfTopHidden r := by
  show findFirst (fun a => decide (st.topHidden a = some r)) Anchor.all
     = findFirst (fun a => decide (st'.topHidden a = some r)) Anchor.all
  exact findFirst_congr (fun a => by
    rw [topHidden_congr hdeal hdpt a]) Anchor.all

theorem hiddenBase_congr {st st' : State} (hdeal : st.deal = st'.deal)
    (hdpt : st.depths = st'.depths) (a : Anchor) :
    st.hiddenBase a = st'.hiddenBase a := by
  show (match ((st.hidden a).reverse.drop 1).head? with
        | some d => Sum.inr d
        | none => Sum.inl a)
     = (match ((st'.hidden a).reverse.drop 1).head? with
        | some d => Sum.inr d
        | none => Sum.inl a)
  have hh : st.hidden a = st'.hidden a := by
    show (st.deal.piles a).take (st.depths a) = (st'.deal.piles a).take (st'.depths a)
    rw [show st'.deal.piles a = st.deal.piles a from by rw [hdeal], hdpt]
  rw [hh]

/-- Pointwise forms: the hidden-pile views at one pile read that
pile's depth alone. -/
theorem topHidden_congr' {st st' : State} (hdeal : st.deal = st'.deal) (a : Anchor)
    (h : st.depths a = st'.depths a) : st.topHidden a = st'.topHidden a := by
  show ((st.deal.piles a).take (st.depths a)).getLast?
      = ((st'.deal.piles a).take (st'.depths a)).getLast?
  rw [show st'.deal.piles a = st.deal.piles a from by rw [hdeal], h]

theorem hiddenBase_congr' {st st' : State} (hdeal : st.deal = st'.deal) (a : Anchor)
    (h : st.depths a = st'.depths a) : st.hiddenBase a = st'.hiddenBase a := by
  show (match ((st.hidden a).reverse.drop 1).head? with
        | some d => Sum.inr d
        | none => Sum.inl a)
     = (match ((st'.hidden a).reverse.drop 1).head? with
        | some d => Sum.inr d
        | none => Sum.inl a)
  have hh : st.hidden a = st'.hidden a := by
    show (st.deal.piles a).take (st.depths a) = (st'.deal.piles a).take (st'.depths a)
    rw [show st'.deal.piles a = st.deal.piles a from by rw [hdeal], h]
  rw [hh]

/-- The with-update form: the base at one pile survives a board change
and a depth change elsewhere. -/
theorem hiddenBase_congr'' {st : State} {bd : Board} {dpt : Anchor → Nat} (a : Anchor)
    (h : st.depths a = dpt a) :
    st.hiddenBase a = ({ st with board := bd, depths := dpt } : State).hiddenBase a := by
  show (match (((st.deal.piles a).take (st.depths a)).reverse.drop 1).head? with
        | some d => Sum.inr d
        | none => Sum.inl a)
     = (match (((st.deal.piles a).take (dpt a)).reverse.drop 1).head? with
        | some d => Sum.inr d
        | none => Sum.inl a)
  rw [h]

/-- The heights updates commute as function updates (bump∘bump and
drop∘drop unconditionally; bump∘drop at a shared suit needs the height
positive — every stackPile guard supplies it). -/
theorem heights_bump_bump {α : Type} [DecidableEq α] (f : α → Nat) (σ σ' : α) :
    (fun s => if s = σ' then (if s = σ then f s + 1 else f s) + 1
      else if s = σ then f s + 1 else f s)
    = (fun s => if s = σ then (if s = σ' then f s + 1 else f s) + 1
      else if s = σ' then f s + 1 else f s) := by
  funext s
  by_cases h1 : s = σ
  · by_cases h2 : s = σ'
    · rw [if_pos h2, if_pos h1, if_pos h1, if_pos h2]
    · rw [if_neg h2, if_pos h1, if_pos h1, if_neg h2]
  · by_cases h2 : s = σ'
    · rw [if_pos h2, if_neg h1, if_neg h1, if_pos h2]
    · rw [if_neg h2, if_neg h1, if_neg h1, if_neg h2]

theorem heights_bump_drop {α : Type} [DecidableEq α] (f : α → Nat) (σ σ' : α) (hpos : σ = σ' → 0 < f σ) :
    (fun s => if s = σ' then (if s = σ then f s - 1 else f s) + 1
      else if s = σ then f s - 1 else f s)
    = (fun s => if s = σ then (if s = σ' then f s + 1 else f s) - 1
      else if s = σ' then f s + 1 else f s) := by
  funext s
  by_cases h1 : s = σ
  · by_cases h2 : s = σ'
    · rw [if_pos h2, if_pos h1, if_pos h1, if_pos h2, h1]
      have hpos' := hpos (h1.symm.trans h2)
      omega
    · rw [if_neg h2, if_pos h1, if_pos h1, if_neg h2]
  · by_cases h2 : s = σ'
    · rw [if_pos h2, if_neg h1, if_neg h1, if_pos h2]
    · rw [if_neg h2, if_neg h1, if_neg h1, if_neg h2]

theorem heights_drop_drop {α : Type} [DecidableEq α] (f : α → Nat) (σ σ' : α) :
    (fun s => if s = σ' then (if s = σ then f s - 1 else f s) - 1
      else if s = σ then f s - 1 else f s)
    = (fun s => if s = σ then (if s = σ' then f s - 1 else f s) - 1
      else if s = σ' then f s - 1 else f s) := by
  funext s
  by_cases h1 : s = σ
  · by_cases h2 : s = σ'
    · rw [if_pos h2, if_pos h1, if_pos h1, if_pos h2]
    · rw [if_neg h2, if_pos h1, if_pos h1, if_neg h2]
  · by_cases h2 : s = σ'
    · rw [if_pos h2, if_neg h1, if_neg h1, if_pos h2]
    · rw [if_neg h2, if_neg h1, if_neg h1, if_neg h2]

theorem disjointTouch_symm {t₁ t₂ : List Base × List Card}
    (h : disjointTouch t₁ t₂) : disjointTouch t₂ t₁ :=
  ⟨fun b hb hc => h.1 b hc hb, fun c hc hcm => h.2 c hcm hc⟩

/-- Reveal's depth steps commute (two reveals, each stepping its own
pile's boundary). -/
theorem depths_step_step (dpt : Anchor → Nat) (a a' : Anchor) :
    (fun x => if x = a' then (if a' = a then dpt a - 1 else dpt a') - 1
      else (if x = a then dpt a - 1 else dpt x))
    = (fun x => if x = a then (if a = a' then dpt a' - 1 else dpt a) - 1
      else (if x = a' then dpt a' - 1 else dpt x)) := by
  funext x
  by_cases h1 : x = a
  · by_cases h2 : x = a'
    · rw [if_pos h2, if_pos (h2.symm.trans h1), if_pos h1, if_pos (h1.symm.trans h2),
        show a = a' from h1.symm.trans h2]
    · rw [if_neg h2, if_pos h1, if_pos h1, if_neg (fun hc => h2 (h1.trans hc))]
  · by_cases h2 : x = a'
    · rw [if_pos h2, if_neg (fun hc => h1 (h2.trans hc)), if_neg h1, if_pos h2]
    · rw [if_neg h2, if_neg h1, if_neg h1, if_neg h2]

/-! ### The pair lemmas — `commute_of_disjoint_touch`'s arms

One lemma per genuinely-fine unordered pair, at a canonical order; the
main theorem dispatches both orders (with `disjointTouch_symm`).  Each
follows the same route: unpack both compositions' shape witnesses,
transfer them across the other move's writes (the touch-disjointness
confines every board write to its own bases and every `bottomOf` change
to its own cards; the hidden-pile views read only deal and depths), and
assemble the common successor fieldwise (the board via the edit
commutations, the heights/depths via the update lemmas). -/

theorem comm_reveal_deckPile {st : State} {c c' : Card} {b' : Base} {st₂ st₃ : State}
    (hdisj : disjointTouch ((Move.reveal c).touch st) ((Move.deckPile c' b').touch st))
    (h₁ : (st.apply (Move.reveal c) >>= fun s => s.apply (Move.deckPile c' b')) = some st₂)
    (h₂ : (st.apply (Move.deckPile c' b') >>= fun s => s.apply (Move.reveal c)) = some st₃) :
    st₂ = st₃ := by
  obtain ⟨s₁, hR, hDP⟩ := Option.bind_eq_some_iff.mp h₁
  obtain ⟨s₃, hDP', hR'⟩ := Option.bind_eq_some_iff.mp h₂
  rw [apply_reveal_iff] at hR
  obtain ⟨htop, r, a, bd₁, hbot, hpile, hatt, hs₁⟩ := hR
  rw [apply_deckPile_iff] at hDP
  obtain ⟨hprev, hcp, bd', hatt', hs₂⟩ := hDP
  rw [apply_deckPile_iff] at hDP'
  obtain ⟨hprev', hcp', bd₁', hatt₁', hs₃⟩ := hDP'
  rw [apply_reveal_iff] at hR'
  obtain ⟨htop', r', a', bd₂', hbot', hpile', hatt₂', hs₄⟩ := hR'
  have hRt : (Move.reveal c).touch st = ([st.hiddenBase a], [c, r]) := by
    simp only [Move.touch, hbot, hpile]
  rw [hRt] at hdisj
  have hD1 : ∀ b ∈ [st.hiddenBase a], b ∉ [b'] := hdisj.1
  have hD2 : ∀ x ∈ [c, r], x ∉ [c'] := hdisj.2
  have hβ : st.hiddenBase a ≠ b' :=
    fun hcon => hD1 (st.hiddenBase a) (by simp) (by rw [hcon]; simp)
  have hcne : c ≠ c' := fun hcon => hD2 c (by simp) (by rw [hcon]; simp)
  have hrne : r ≠ c' := fun hcon => hD2 r (by simp) (by rw [hcon]; simp)
  -- the deckPile attach preserves c's and c''s seats; reveal's view is board-blind
  rw [hs₃] at hbot' hpile' hatt₂'
  have hbr : bd₁'.bottomOf c = some (Sum.inr r') := hbot'
  rw [bottomOf_attach_ne hatt₁' hcne, hbot] at hbr
  have hrr : r' = r := Sum.inr.inj (Option.some.inj hbr.symm)
  have hpl : st.pileOfTopHidden r' = some a' := hpile'
  rw [hrr] at hpl
  have haa : a' = a := Option.some.inj (hpl.symm.trans hpile)
  rw [hs₁] at hatt'
  have hatt'₂ : bd₁.attach b' c' = some bd' := hatt'
  rw [hrr, haa] at hatt₂'
  have hatt₂'' : bd₁'.attach (st.hiddenBase a) r = some bd₂' := hatt₂'
  have hbd : bd' = bd₂' := Board.attach_attach_comm hβ hatt hatt'₂ hatt₁' hatt₂''
  rw [hs₂, hs₁, hs₄, hs₃, haa, hbd]

theorem comm_reveal_pileStack {st : State} {c c' : Card} {st₂ st₃ : State}
    (hdisj : disjointTouch ((Move.reveal c).touch st) ((Move.pileStack c').touch st))
    (h₁ : (st.apply (Move.reveal c) >>= fun s => s.apply (Move.pileStack c')) = some st₂)
    (h₂ : (st.apply (Move.pileStack c') >>= fun s => s.apply (Move.reveal c)) = some st₃) :
    st₂ = st₃ := by
  obtain ⟨s₁, hR, hPS⟩ := Option.bind_eq_some_iff.mp h₁
  obtain ⟨s₃, hPS', hR'⟩ := Option.bind_eq_some_iff.mp h₂
  rw [apply_reveal_iff] at hR
  obtain ⟨htop, r, a, bd₁, hbot, hpile, hatt, hs₁⟩ := hR
  rw [apply_pileStack_iff] at hPS
  obtain ⟨htop', b₀', hb', hrk', hs₂⟩ := hPS
  rw [apply_pileStack_iff] at hPS'
  obtain ⟨htop₂, b₀, hb, hrk, hs₃⟩ := hPS'
  rw [apply_reveal_iff] at hR'
  obtain ⟨htop₃, r'', a'', bd₄, hbot₃, hpile₃, hatt₃, hs₄⟩ := hR'
  have hRt : (Move.reveal c).touch st = ([st.hiddenBase a], [c, r]) := by
    simp only [Move.touch, hbot, hpile]
  have hPSt : (Move.pileStack c').touch st = ([b₀], [c']) := by
    simp only [Move.touch, hb, Option.toList_some]
  rw [hRt, hPSt] at hdisj
  have hD1 : ∀ b ∈ [st.hiddenBase a], b ∉ [b₀] := hdisj.1
  have hD2 : ∀ x ∈ [c, r], x ∉ [c'] := hdisj.2
  have hβ : st.hiddenBase a ≠ b₀ :=
    fun hcon => hD1 (st.hiddenBase a) (by simp) (by rw [hcon]; simp)
  have hcne : c ≠ c' := fun hcon => hD2 c (by simp) (by rw [hcon]; simp)
  have hrne : r ≠ c' := fun hcon => hD2 r (by simp) (by rw [hcon]; simp)
  -- the detach preserves c's seat (c ≠ the detached card); reveal's view is board-blind
  rw [hs₃] at hbot₃ hpile₃ hatt₃
  have htb₀ : st.board.topOf b₀ = some c' := (Board.bottomOf_eq st.board c' b₀).mp hb
  have hbr : (st.board.detach b₀).bottomOf c = some (Sum.inr r'') := hbot₃
  rw [bottomOf_detach_ne htb₀ hcne, hbot] at hbr
  have hrr : r'' = r := Sum.inr.inj (Option.some.inj hbr.symm)
  have hpl : st.pileOfTopHidden r'' = some a'' := hpile₃
  rw [hrr] at hpl
  have haa : a'' = a := Option.some.inj (hpl.symm.trans hpile)
  -- pileStack's detach base is the same in both orders
  rw [hs₁] at hb'
  have hb₂ : bd₁.bottomOf c' = some b₀' := hb'
  rw [bottomOf_attach_ne hatt (Ne.symm hrne), hb] at hb₂
  have hb₀e : b₀' = b₀ := (Option.some.inj hb₂).symm
  rw [hrr, haa] at hatt₃
  have hatt₃' : (st.board.detach b₀).attach (st.hiddenBase a) r = some bd₄ := hatt₃
  rw [hs₂, hs₁, hs₄, hs₃, haa, hb₀e]
  refine state_ext rfl ?_ rfl rfl rfl rfl
  exact attach_detach_comm hβ hatt hatt₃'

theorem comm_reveal_stackPile {st : State} {c c' : Card} {b' : Base} {st₂ st₃ : State}
    (hdisj : disjointTouch ((Move.reveal c).touch st) ((Move.stackPile c' b').touch st))
    (h₁ : (st.apply (Move.reveal c) >>= fun s => s.apply (Move.stackPile c' b')) = some st₂)
    (h₂ : (st.apply (Move.stackPile c' b') >>= fun s => s.apply (Move.reveal c)) = some st₃) :
    st₂ = st₃ := by
  obtain ⟨s₁, hR, hSP⟩ := Option.bind_eq_some_iff.mp h₁
  obtain ⟨s₃, hSP', hR'⟩ := Option.bind_eq_some_iff.mp h₂
  rw [apply_reveal_iff] at hR
  obtain ⟨htop, r, a, bd₁, hbot, hpile, hatt, hs₁⟩ := hR
  rw [apply_stackPile_iff] at hSP
  obtain ⟨hrk', hcp', bd₂, hatt', hs₂⟩ := hSP
  rw [apply_stackPile_iff] at hSP'
  obtain ⟨hrk, hcp, bd₃, hatt₁, hs₃⟩ := hSP'
  rw [apply_reveal_iff] at hR'
  obtain ⟨htop₃, r'', a'', bd₄, hbot₃, hpile₃, hatt₃, hs₄⟩ := hR'
  have hRt : (Move.reveal c).touch st = ([st.hiddenBase a], [c, r]) := by
    simp only [Move.touch, hbot, hpile]
  rw [hRt] at hdisj
  have hD1 : ∀ b ∈ [st.hiddenBase a], b ∉ [b'] := hdisj.1
  have hD2 : ∀ x ∈ [c, r], x ∉ [c'] := hdisj.2
  have hβ : st.hiddenBase a ≠ b' :=
    fun hcon => hD1 (st.hiddenBase a) (by simp) (by rw [hcon]; simp)
  have hcne : c ≠ c' := fun hcon => hD2 c (by simp) (by rw [hcon]; simp)
  have hrne : r ≠ c' := fun hcon => hD2 r (by simp) (by rw [hcon]; simp)
  rw [hs₃] at hbot₃ hpile₃ hatt₃
  have hbr : bd₃.bottomOf c = some (Sum.inr r'') := hbot₃
  rw [bottomOf_attach_ne hatt₁ hcne, hbot] at hbr
  have hrr : r'' = r := Sum.inr.inj (Option.some.inj hbr.symm)
  have hpl : st.pileOfTopHidden r'' = some a'' := hpile₃
  rw [hrr] at hpl
  have haa : a'' = a := Option.some.inj (hpl.symm.trans hpile)
  rw [hs₁] at hatt'
  have hatt'₂ : bd₁.attach b' c' = some bd₂ := hatt'
  rw [hrr, haa] at hatt₃
  have hatt₃' : bd₃.attach (st.hiddenBase a) r = some bd₄ := hatt₃
  have hbd : bd₂ = bd₄ := Board.attach_attach_comm hβ hatt hatt'₂ hatt₁ hatt₃'
  rw [hs₂, hs₁, hs₄, hs₃, haa, hbd]

/-- `reveal`·`reveal`: the depth steps commute, the boundary searches
survive the other reveal's depth write *except* at the exposed pile —
and when the exposed card IS the other reveal's boundary card, the
first reveal's seating blocks the second's attach (vacuity, via
`take_reverse_drop1`: the base under the boundary is the card the
depth-step exposes). -/
theorem comm_reveal_reveal {st : State} {c c' : Card} {st₂ st₃ : State}
    (hdisj : disjointTouch ((Move.reveal c).touch st) ((Move.reveal c').touch st))
    (h₁ : (st.apply (Move.reveal c) >>= fun s => s.apply (Move.reveal c')) = some st₂)
    (h₂ : (st.apply (Move.reveal c') >>= fun s => s.apply (Move.reveal c)) = some st₃) :
    st₂ = st₃ := by
  obtain ⟨s₁, hRA, hRB⟩ := Option.bind_eq_some_iff.mp h₁
  obtain ⟨s₃, hRC, hRD⟩ := Option.bind_eq_some_iff.mp h₂
  rw [apply_reveal_iff] at hRA
  obtain ⟨htop, r, a, bd₁, hbot, hpile, hatt, hs₁⟩ := hRA
  rw [apply_reveal_iff] at hRB
  obtain ⟨htop', r₁, a₁, bd₂, hbot₁, hpile₁, hatt₁, hs₂⟩ := hRB
  rw [apply_reveal_iff] at hRC
  obtain ⟨htop₂, r', a', bd₃, hbot', hpile', hatt', hs₃⟩ := hRC
  rw [apply_reveal_iff] at hRD
  obtain ⟨htop₃, r₄, a₄, bd₄, hbot₄, hpile₄, hatt₄, hs₄⟩ := hRD
  have hRt : (Move.reveal c).touch st = ([st.hiddenBase a], [c, r]) := by
    simp only [Move.touch, hbot, hpile]
  have hRt' : (Move.reveal c').touch st = ([st.hiddenBase a'], [c', r']) := by
    simp only [Move.touch, hbot', hpile']
  rw [hRt, hRt'] at hdisj
  have hD1 : ∀ b ∈ [st.hiddenBase a], b ∉ [st.hiddenBase a'] := hdisj.1
  have hD2 : ∀ x ∈ [c, r], x ∉ [c', r'] := hdisj.2
  have hβ : st.hiddenBase a ≠ st.hiddenBase a' :=
    fun hcon => hD1 (st.hiddenBase a) (by simp) (by rw [hcon]; simp)
  have hrc' : r ≠ c' := fun hcon => hD2 r (by simp) (by rw [hcon]; simp)
  have hrr' : r ≠ r' := fun hcon => hD2 r (by simp) (by rw [hcon]; simp)
  have hcr' : c ≠ r' := fun hcon => hD2 c (by simp) (by rw [hcon]; simp)
  have hTa : st.topHidden a = some r := of_decide_eq_true (findFirst_mem _ _ _ hpile).2
  have hTa' : st.topHidden a' = some r' := of_decide_eq_true (findFirst_mem _ _ _ hpile').2
  have haa' : a ≠ a' := fun hcon => hβ (by rw [hcon])
  -- the triggers' under-cards are untouched (card-disjointness + the
  -- attach blindness)
  rw [hs₁] at hbot₁
  have hbr₁ : bd₁.bottomOf c' = some (Sum.inr r₁) := hbot₁
  rw [bottomOf_attach_ne hatt (Ne.symm hrc'), hbot'] at hbr₁
  have hr₁ : r₁ = r' := Sum.inr.inj (Option.some.inj hbr₁.symm)
  rw [hr₁] at hatt₁ hpile₁
  rw [hs₃] at hbot₄
  have hbr₄ : bd₃.bottomOf c = some (Sum.inr r₄) := hbot₄
  rw [bottomOf_attach_ne hatt' hcr', hbot] at hbr₄
  have hr₄ : r₄ = r := Sum.inr.inj (Option.some.inj hbr₄.symm)
  rw [hr₄] at hatt₄ hpile₄
  -- the boundary searches: both survive unless the exposed card is the
  -- other's boundary — and then the FIRST reveal's own attach dies (its
  -- base is the exposed card, which the other trigger already occupies)
  by_cases hred : s₁.topHidden a = some r'
  · exfalso
    have hreseq : s₁.topHidden a = ((st.deal.piles a).take (st.depths a - 1)).getLast? := by
      rw [hs₁]
      show ((st.deal.piles a).take (if a = a then st.depths a - 1 else st.depths a)).getLast?
          = ((st.deal.piles a).take (st.depths a - 1)).getLast?
      rw [if_pos rfl]
    have hred' : ((st.deal.piles a).take (st.depths a - 1)).getLast? = some r' :=
      hreseq.symm.trans hred
    have hseq : (((st.deal.piles a).take (st.depths a)).reverse.drop 1).head? = some r' :=
      take_reverse_drop1 hTa hred' hrr'
    have hhb : st.hiddenBase a = Sum.inr r' := by
      show (match (((st.deal.piles a).take (st.depths a)).reverse.drop 1).head? with
            | some d => Sum.inr d
            | none => Sum.inl a) = Sum.inr r'
      rw [hseq]
    rw [hhb] at hatt
    obtain ⟨htopg, -⟩ := (Board.attach_eq_some_iff st.board (Sum.inr r') r).mp
      (by rw [hatt]; simp)
    rw [(Board.bottomOf_eq st.board c' (Sum.inr r')).mp hbot'] at htopg
    exact absurd htopg (by simp)
  by_cases hred' : s₃.topHidden a' = some r
  · exfalso
    have hreseq : s₃.topHidden a' = ((st.deal.piles a').take (st.depths a' - 1)).getLast? := by
      rw [hs₃]
      show ((st.deal.piles a').take (if a' = a' then st.depths a' - 1 else st.depths a')).getLast?
          = ((st.deal.piles a').take (st.depths a' - 1)).getLast?
      rw [if_pos rfl]
    have hred'' : ((st.deal.piles a').take (st.depths a' - 1)).getLast? = some r :=
      hreseq.symm.trans hred'
    have hseq : (((st.deal.piles a').take (st.depths a')).reverse.drop 1).head? = some r :=
      take_reverse_drop1 hTa' hred'' (fun hcon => hrr' hcon.symm)
    have hhb : st.hiddenBase a' = Sum.inr r := by
      show (match (((st.deal.piles a').take (st.depths a')).reverse.drop 1).head? with
            | some d => Sum.inr d
            | none => Sum.inl a') = Sum.inr r
      rw [hseq]
    rw [hhb] at hatt'
    obtain ⟨htopg, -⟩ := (Board.attach_eq_some_iff st.board (Sum.inr r) r').mp
      (by rw [hatt']; simp)
    rw [(Board.bottomOf_eq st.board c (Sum.inr r)).mp hbot] at htopg
    exact absurd htopg (by simp)
  -- no redirects: the searches agree
  have hpp : s₁.pileOfTopHidden r' = st.pileOfTopHidden r' := by
    show findFirst (fun x => decide (s₁.topHidden x = some r')) Anchor.all
        = findFirst (fun x => decide (st.topHidden x = some r')) Anchor.all
    refine findFirst_congr (fun x => ?_) Anchor.all
    by_cases hxa : x = a
    · subst hxa
      rw [decide_congr (iff_of_false hred
        (fun (hp : st.topHidden x = some r') =>
          hrr' (Option.some.inj (hp.symm.trans hTa)).symm))]
    · have hdx : st.depths x = s₁.depths x := by
        rw [hs₁]
        show st.depths x = (if x = a then st.depths a - 1 else st.depths x)
        rw [if_neg hxa]
      rw [topHidden_congr' (by rw [hs₁]) x hdx]
  have hpp' : s₃.pileOfTopHidden r = st.pileOfTopHidden r := by
    show findFirst (fun x => decide (s₃.topHidden x = some r)) Anchor.all
        = findFirst (fun x => decide (st.topHidden x = some r)) Anchor.all
    refine findFirst_congr (fun x => ?_) Anchor.all
    by_cases hxa : x = a'
    · subst hxa
      rw [decide_congr (iff_of_false hred'
        (fun (hp : st.topHidden x = some r) =>
          hrr' (Option.some.inj (hp.symm.trans hTa'))))]
    · have hdx : st.depths x = s₃.depths x := by
        rw [hs₃]
        show st.depths x = (if x = a' then st.depths a' - 1 else st.depths x)
        rw [if_neg hxa]
      rw [topHidden_congr' (by rw [hs₃]) x hdx]
  rw [hpp] at hpile₁
  have haa₁ : a₁ = a' := Option.some.inj (hpile₁.symm.trans hpile')
  rw [hpp'] at hpile₄
  have haa₄ : a₄ = a := Option.some.inj (hpile₄.symm.trans hpile)
  -- the attach bases: each reveal's base survives the other's depth write
  have hdpa' : st.depths a' = (fun x => if x = a then st.depths a - 1 else st.depths x) a' := by
    show st.depths a' = (if a' = a then st.depths a - 1 else st.depths a')
    rw [if_neg (fun hcon => haa' hcon.symm)]
  have hbase₁ : s₁.hiddenBase a' = st.hiddenBase a' := by
    rw [hs₁, show st.hiddenBase a' = ({ st with board := bd₁, depths := fun x => if x = a then st.depths a - 1 else st.depths x } : State).hiddenBase a'
      from hiddenBase_congr'' a' hdpa']
  have hdpa : st.depths a = (fun x => if x = a' then st.depths a' - 1 else st.depths x) a := by
    show st.depths a = (if a = a' then st.depths a' - 1 else st.depths a)
    rw [if_neg haa']
  have hbase₄ : s₃.hiddenBase a = st.hiddenBase a := by
    rw [hs₃, show st.hiddenBase a = ({ st with board := bd₃, depths := fun x => if x = a' then st.depths a' - 1 else st.depths x } : State).hiddenBase a
      from hiddenBase_congr'' a hdpa]
  rw [haa₁, hbase₁, hs₁] at hatt₁
  have hatt₁' : bd₁.attach (st.hiddenBase a') r' = some bd₂ := hatt₁
  rw [haa₄, hbase₄, hs₃] at hatt₄
  have hatt₄' : bd₃.attach (st.hiddenBase a) r = some bd₄ := hatt₄
  have hbd : bd₂ = bd₄ := Board.attach_attach_comm hβ hatt hatt₁' hatt' hatt₄'
  rw [hs₂, hs₁, hs₄, hs₃, haa₁, haa₄, hbd]
  refine state_ext rfl rfl rfl ?_ rfl rfl
  exact depths_step_step st.depths a a'

theorem comm_reveal_pilePile {st : State} {c c' : Card} {b' : Base} {st₂ st₃ : State}
    (hdisj : disjointTouch ((Move.reveal c).touch st) ((Move.pilePile c' b').touch st))
    (h₁ : (st.apply (Move.reveal c) >>= fun s => s.apply (Move.pilePile c' b')) = some st₂)
    (h₂ : (st.apply (Move.pilePile c' b') >>= fun s => s.apply (Move.reveal c)) = some st₃) :
    st₂ = st₃ := by
  obtain ⟨s₁, hR, hPP⟩ := Option.bind_eq_some_iff.mp h₁
  obtain ⟨s₃, hPP', hR'⟩ := Option.bind_eq_some_iff.mp h₂
  rw [apply_reveal_iff] at hR
  obtain ⟨htop, r, a, bd₁, hbot, hpile, hatt, hs₁⟩ := hR
  rw [apply_pilePile_iff] at hPP
  obtain ⟨b₀', hb', hne', hcmr', bd₂, hatt', hs₂⟩ := hPP
  rw [apply_pilePile_iff] at hPP'
  obtain ⟨b₀, hb, hne, hcmr, bd₃, hatt₁, hs₃⟩ := hPP'
  rw [apply_reveal_iff] at hR'
  obtain ⟨htop₃, r'', a'', bd₄, hbot₃, hpile₃, hatt₃, hs₄⟩ := hR'
  have hRt : (Move.reveal c).touch st = ([st.hiddenBase a], [c, r]) := by
    simp only [Move.touch, hbot, hpile]
  have hPPt : (Move.pilePile c' b').touch st = (b' :: [b₀], c' :: st.board.aboveOf c') := by
    simp only [Move.touch, hb, Option.toList_some]
  rw [hRt, hPPt] at hdisj
  have hD1 : ∀ b ∈ [st.hiddenBase a], b ∉ (b' :: [b₀] : List Base) := hdisj.1
  have hD2 : ∀ x ∈ [c, r], x ∉ (c' :: st.board.aboveOf c') := hdisj.2
  have hβ₁ : st.hiddenBase a ≠ b' :=
    fun hcon => hD1 (st.hiddenBase a) (by simp) (by rw [hcon]; simp)
  have hβ₂ : st.hiddenBase a ≠ b₀ :=
    fun hcon => hD1 (st.hiddenBase a) (by simp) (by rw [hcon]; simp)
  have hcc' : c ≠ c' := fun hcon => hD2 c (by simp) (by rw [hcon]; simp)
  have hcAb : c ∉ st.board.aboveOf c' :=
    fun hcon => hD2 c (by simp) (by simp [hcon])
  have hrc' : r ≠ c' := fun hcon => hD2 r (by simp) (by rw [hcon]; simp)
  have hrAb : r ∉ st.board.aboveOf c' :=
    fun hcon => hD2 r (by simp) (by simp [hcon])
  -- reveal's trigger seat survives the pilePile edit; its view is board-blind
  rw [hs₃] at hbot₃ hpile₃ hatt₃
  have htb₀ : st.board.topOf b₀ = some c' := (Board.bottomOf_eq st.board c' b₀).mp hb
  have hbr : bd₃.bottomOf c = some (Sum.inr r'') := hbot₃
  rw [bottomOf_attach_ne hatt₁ hcc', bottomOf_detach_ne htb₀ hcc', hbot] at hbr
  have hrr : r'' = r := Sum.inr.inj (Option.some.inj hbr.symm)
  have hpl : st.pileOfTopHidden r'' = some a'' := hpile₃
  rw [hrr] at hpl
  have haa : a'' = a := Option.some.inj (hpl.symm.trans hpile)
  -- pilePile's detach base agrees in both orders
  rw [hs₁] at hb'
  have hb₂ : bd₁.bottomOf c' = some b₀' := hb'
  rw [bottomOf_attach_ne hatt (Ne.symm hrc'), hb] at hb₂
  have hb₀e : b₀' = b₀ := (Option.some.inj hb₂).symm
  rw [hrr, haa] at hatt₃
  have hatt₃' : bd₃.attach (st.hiddenBase a) r = some bd₄ := hatt₃
  rw [hs₁] at hatt'
  have hatt'₂ : (bd₁.detach b₀').attach b' c' = some bd₂ := hatt'
  rw [hb₀e] at hatt'₂
  -- the board: attach (hb a) r, detach b₀, attach b' c' — three distinct bases
  have hbd : bd₂ = bd₄ := by
    refine Board.ext_topOf (funext (fun x => ?_))
    by_cases hxb : x = st.hiddenBase a
    · rw [hxb, Board.attach_topOf_ne _ _ _ hatt'₂ hβ₁,
        Board.detach_topOf_ne bd₁ b₀ _ hβ₂,
        Board.attach_topOf st.board _ r hatt, Board.attach_topOf bd₃ _ r hatt₃']
    · by_cases hxb' : x = b'
      · rw [hxb', Board.attach_topOf _ _ _ hatt'₂, Board.attach_topOf_ne bd₃ _ r hatt₃'
          (fun hcon => hβ₁ hcon.symm), Board.attach_topOf _ _ _ hatt₁]
      · by_cases hxb₀ : x = b₀
        · rw [hxb₀, Board.attach_topOf_ne _ _ _ hatt'₂ hne,
            Board.detach_topOf, Board.attach_topOf_ne bd₃ _ r hatt₃' (Ne.symm hβ₂),
            Board.attach_topOf_ne _ _ _ hatt₁ hne, Board.detach_topOf]
        · rw [Board.attach_topOf_ne _ _ _ hatt'₂ hxb',
            Board.detach_topOf_ne _ _ _ hxb₀, Board.attach_topOf_ne _ _ _ hatt hxb,
            Board.attach_topOf_ne bd₃ _ r hatt₃' hxb,
            Board.attach_topOf_ne _ _ _ hatt₁ hxb', Board.detach_topOf_ne _ _ _ hxb₀]
  rw [hs₂, hs₁, hs₄, hs₃, haa, hbd]

theorem comm_deckPile_pileStack {st : State} {c c' : Card} {b : Base} {st₂ st₃ : State}
    (hdisj : disjointTouch ((Move.deckPile c b).touch st) ((Move.pileStack c').touch st))
    (h₁ : (st.apply (Move.deckPile c b) >>= fun s => s.apply (Move.pileStack c')) = some st₂)
    (h₂ : (st.apply (Move.pileStack c') >>= fun s => s.apply (Move.deckPile c b)) = some st₃) :
    st₂ = st₃ := by
  obtain ⟨s₁, hDP, hPS⟩ := Option.bind_eq_some_iff.mp h₁
  obtain ⟨s₃, hPS', hDP'⟩ := Option.bind_eq_some_iff.mp h₂
  rw [apply_deckPile_iff] at hDP
  obtain ⟨hprev, hcp, bd₁, hatt, hs₁⟩ := hDP
  rw [apply_pileStack_iff] at hPS
  obtain ⟨htop', b₀', hb', hrk', hs₂⟩ := hPS
  rw [apply_pileStack_iff] at hPS'
  obtain ⟨htop₂, b₀, hb, hrk, hs₃⟩ := hPS'
  rw [apply_deckPile_iff] at hDP'
  obtain ⟨hprev', hcp', bd₂, hatt', hs₄⟩ := hDP'
  have hPSt : (Move.pileStack c').touch st = ([b₀], [c']) := by
    simp only [Move.touch, hb, Option.toList_some]
  rw [hPSt] at hdisj
  have hD1 : ∀ β ∈ [b], β ∉ ([b₀] : List Base) := hdisj.1
  have hD2 : ∀ x ∈ [c], x ∉ [c'] := hdisj.2
  have hbb₀ : b ≠ b₀ := fun hcon => hD1 b (by simp) (by rw [hcon]; simp)
  have hcc' : c ≠ c' := fun hcon => hD2 c (by simp) (by rw [hcon]; simp)
  -- pileStack's guard at s₁: the same detach base
  rw [hs₁] at hb'
  have hb₂ : bd₁.bottomOf c' = some b₀' := hb'
  rw [bottomOf_attach_ne hatt (Ne.symm hcc'), hb] at hb₂
  have hb₀e : b₀' = b₀ := (Option.some.inj hb₂).symm
  -- deckPile's guard at s₃: the base is untouched (b ≠ b₀); the isVis
  -- read vacates only when it read the detached card itself
  rw [hs₃] at hcp' hatt'
  have hatt'₂ : (st.board.detach b₀).attach b c = some bd₂ := hatt'
  cases b with
  | inl _ =>
      rw [hs₂, hs₁, hs₄, hs₃, hb₀e]
      refine state_ext rfl ?_ rfl rfl rfl rfl
      exact attach_detach_comm hbb₀ hatt hatt'₂
  | inr d =>
      by_cases hdc : d = c'
      · exfalso
        rw [← hdc] at hb
        have h1 : (st.board.detach b₀).bottomOf d = none :=
          detach_bottomOf_self ((Board.bottomOf_eq st.board d b₀).mp hb)
        have h2 : ({ st with board := st.board.detach b₀, heights := fun s => if s = d.suit then st.heights s + 1 else st.heights s } : State).isVis d = true := by
          have := hcp'
          simp only [State.canPlace, Bool.and_eq_true_iff, decide_eq_true_iff] at this
          exact this.2.1
        rw [State.isVis, h1] at h2
        exact absurd h2 (by simp)
      · rw [hs₂, hs₁, hs₄, hs₃, hb₀e]
        refine state_ext rfl ?_ rfl rfl rfl rfl
        exact attach_detach_comm hbb₀ hatt hatt'₂

/-- `canPlace`'s tableau half: the base card is visible. -/
theorem canPlace_inr_isVis {st : State} {c d : Card}
    (h : st.canPlace c (Sum.inr d) = true) : st.isVis d = true := by
  simp only [State.canPlace, Bool.and_eq_true_iff, decide_eq_true_iff] at h
  exact h.2.1

theorem comm_deckPile_stackPile {st : State} {c c' : Card} {b b' : Base} {st₂ st₃ : State}
    (hdisj : disjointTouch ((Move.deckPile c b).touch st) ((Move.stackPile c' b').touch st))
    (h₁ : (st.apply (Move.deckPile c b) >>= fun s => s.apply (Move.stackPile c' b')) = some st₂)
    (h₂ : (st.apply (Move.stackPile c' b') >>= fun s => s.apply (Move.deckPile c b)) = some st₃) :
    st₂ = st₃ := by
  obtain ⟨s₁, hDP, hSP⟩ := Option.bind_eq_some_iff.mp h₁
  obtain ⟨s₃, hSP', hDP'⟩ := Option.bind_eq_some_iff.mp h₂
  rw [apply_deckPile_iff] at hDP
  obtain ⟨hprev, hcp, bd₁, hatt, hs₁⟩ := hDP
  rw [apply_stackPile_iff] at hSP
  obtain ⟨hrk', hcp', bd₂, hatt', hs₂⟩ := hSP
  rw [apply_stackPile_iff] at hSP'
  obtain ⟨hrk, hcp₂, bd₃, hatt₁, hs₃⟩ := hSP'
  rw [apply_deckPile_iff] at hDP'
  obtain ⟨hprev', hcp₃, bd₄, hatt₂', hs₄⟩ := hDP'
  have hD1 : ∀ β ∈ [b], β ∉ ([b'] : List Base) := hdisj.1
  have hD2 : ∀ x ∈ [c], x ∉ [c'] := hdisj.2
  have hbb' : b ≠ b' := fun hcon => hD1 b (by simp) (by rw [hcon]; simp)
  have hcc' : c ≠ c' := fun hcon => hD2 c (by simp) (by rw [hcon]; simp)
  -- vacuity corners: a base card equal to the other move's card is
  -- both required visible (its canPlace) and required unseated (the
  -- other's attach guard)
  have hatt₁g : st.board.bottomOf c' = none :=
    ((Board.attach_eq_some_iff st.board b' c').mp (by rw [hatt₁]; simp)).2
  have hattg : st.board.bottomOf c = none :=
    ((Board.attach_eq_some_iff st.board b c).mp (by rw [hatt]; simp)).2
  cases b with
  | inl a =>
      cases b' with
      | inl a' =>
          rw [hs₁] at hatt'
          rw [hs₃] at hatt₂'
          have hatt'₂ : bd₁.attach (Sum.inl a') c' = some bd₂ := hatt'
          have hatt₂'' : bd₃.attach (Sum.inl a) c = some bd₄ := hatt₂'
          have hbd : bd₂ = bd₄ := Board.attach_attach_comm hbb' hatt hatt'₂ hatt₁ hatt₂''
          rw [hs₂, hs₁, hs₄, hs₃, hbd]
      | inr d' =>
          by_cases hd' : d' = c
          · exfalso
            have h2 := canPlace_inr_isVis hcp₂
            rw [hd', State.isVis, hattg] at h2
            exact absurd h2 (by simp)
          · rw [hs₁] at hatt'
            rw [hs₃] at hatt₂'
            have hatt'₂ : bd₁.attach (Sum.inr d') c' = some bd₂ := hatt'
            have hatt₂'' : bd₃.attach (Sum.inl a) c = some bd₄ := hatt₂'
            have hbd : bd₂ = bd₄ := Board.attach_attach_comm hbb' hatt hatt'₂ hatt₁ hatt₂''
            rw [hs₂, hs₁, hs₄, hs₃, hbd]
  | inr d =>
      by_cases hd : d = c'
      · exfalso
        have h2 := canPlace_inr_isVis hcp
        rw [hd, State.isVis, hatt₁g] at h2
        exact absurd h2 (by simp)
      · cases b' with
        | inl a' =>
            rw [hs₁] at hatt'
            rw [hs₃] at hatt₂'
            have hatt'₂ : bd₁.attach (Sum.inl a') c' = some bd₂ := hatt'
            have hatt₂'' : bd₃.attach (Sum.inr d) c = some bd₄ := hatt₂'
            have hbd : bd₂ = bd₄ := Board.attach_attach_comm hbb' hatt hatt'₂ hatt₁ hatt₂''
            rw [hs₂, hs₁, hs₄, hs₃, hbd]
        | inr d' =>
            by_cases hd'' : d' = c
            · exfalso
              have h2 := canPlace_inr_isVis hcp₂
              rw [hd'', State.isVis, hattg] at h2
              exact absurd h2 (by simp)
            · rw [hs₁] at hatt'
              rw [hs₃] at hatt₂'
              have hatt'₂ : bd₁.attach (Sum.inr d') c' = some bd₂ := hatt'
              have hatt₂'' : bd₃.attach (Sum.inr d) c = some bd₄ := hatt₂'
              have hbd : bd₂ = bd₄ := Board.attach_attach_comm hbb' hatt hatt'₂ hatt₁ hatt₂''
              rw [hs₂, hs₁, hs₄, hs₃, hbd]

theorem comm_deckPile_pilePile {st : State} {c c' : Card} {b b' : Base} {st₂ st₃ : State}
    (hdisj : disjointTouch ((Move.deckPile c b).touch st) ((Move.pilePile c' b').touch st))
    (h₁ : (st.apply (Move.deckPile c b) >>= fun s => s.apply (Move.pilePile c' b')) = some st₂)
    (h₂ : (st.apply (Move.pilePile c' b') >>= fun s => s.apply (Move.deckPile c b)) = some st₃) :
    st₂ = st₃ := by
  obtain ⟨s₁, hDP, hPP⟩ := Option.bind_eq_some_iff.mp h₁
  obtain ⟨s₃, hPP', hDP'⟩ := Option.bind_eq_some_iff.mp h₂
  rw [apply_deckPile_iff] at hDP
  obtain ⟨hprev, hcp, bd₁, hatt, hs₁⟩ := hDP
  rw [apply_pilePile_iff] at hPP
  obtain ⟨b₀', hb', hne', hcmr', bd₂, hatt', hs₂⟩ := hPP
  rw [apply_pilePile_iff] at hPP'
  obtain ⟨b₀, hb, hne, hcmr, bd₃, hatt₁, hs₃⟩ := hPP'
  rw [apply_deckPile_iff] at hDP'
  obtain ⟨hprev', hcp', bd₄, hatt₂', hs₄⟩ := hDP'
  have hPPt : (Move.pilePile c' b').touch st = (b' :: [b₀], c' :: st.board.aboveOf c') := by
    simp only [Move.touch, hb, Option.toList_some]
  rw [hPPt] at hdisj
  have hD1 : ∀ β ∈ [b], β ∉ (b' :: [b₀] : List Base) := hdisj.1
  have hD2 : ∀ x ∈ [c], x ∉ (c' :: st.board.aboveOf c') := hdisj.2
  have hbb' : b ≠ b' := fun hcon => hD1 b (by simp) (by rw [hcon]; simp)
  have hbb₀ : b ≠ b₀ := fun hcon => hD1 b (by simp) (by simp [hcon])
  have hcc' : c ≠ c' := fun hcon => hD2 c (by simp) (by rw [hcon]; simp)
  -- pilePile's detach base agrees in both orders
  rw [hs₁] at hb'
  have hb₂ : bd₁.bottomOf c' = some b₀' := hb'
  rw [bottomOf_attach_ne hatt (Ne.symm hcc'), hb] at hb₂
  have hb₀e : b₀' = b₀ := (Option.some.inj hb₂).symm
  rw [hs₁, hb₀e] at hatt'
  have hatt'₂ : (bd₁.detach b₀).attach b' c' = some bd₂ := hatt'
  rw [hs₃] at hatt₂'
  have hatt₂'' : bd₃.attach b c = some bd₄ := hatt₂'
  -- the board: attach b c, detach b₀, attach b' c' — three distinct bases
  have hbd : bd₂ = bd₄ := by
    refine Board.ext_topOf (funext (fun x => ?_))
    by_cases hxb : x = b
    · rw [hxb, Board.attach_topOf_ne _ _ _ hatt'₂ hbb',
        Board.detach_topOf_ne _ _ _ hbb₀, Board.attach_topOf _ _ _ hatt,
        Board.attach_topOf _ _ _ hatt₂'']
    · by_cases hxb' : x = b'
      · rw [hxb', Board.attach_topOf _ _ _ hatt'₂, Board.attach_topOf_ne _ _ _ hatt₂'' (Ne.symm hbb'),
          Board.attach_topOf _ _ _ hatt₁]
      · by_cases hxb₀ : x = b₀
        · rw [hxb₀, Board.attach_topOf_ne _ _ _ hatt'₂ hne, Board.detach_topOf,
            Board.attach_topOf_ne _ _ _ hatt₂'' (Ne.symm hbb₀),
            Board.attach_topOf_ne _ _ _ hatt₁ hne, Board.detach_topOf]
        · rw [Board.attach_topOf_ne _ _ _ hatt'₂ hxb', Board.detach_topOf_ne _ _ _ hxb₀,
            Board.attach_topOf_ne _ _ _ hatt hxb,
            Board.attach_topOf_ne _ _ _ hatt₂'' hxb,
            Board.attach_topOf_ne _ _ _ hatt₁ hxb',
            Board.detach_topOf_ne _ _ _ hxb₀]
  rw [hs₂, hs₁, hs₄, hs₃, hbd]

theorem comm_deckStack_pileStack {st : State} {c c' : Card} {st₂ st₃ : State}
    (hdisj : disjointTouch ((Move.deckStack c).touch st) ((Move.pileStack c').touch st))
    (h₁ : (st.apply (Move.deckStack c) >>= fun s => s.apply (Move.pileStack c')) = some st₂)
    (h₂ : (st.apply (Move.pileStack c') >>= fun s => s.apply (Move.deckStack c)) = some st₃) :
    st₂ = st₃ := by
  obtain ⟨s₁, hDS, hPS⟩ := Option.bind_eq_some_iff.mp h₁
  obtain ⟨s₃, hPS', hDS'⟩ := Option.bind_eq_some_iff.mp h₂
  rw [apply_deckStack_iff] at hDS
  obtain ⟨hprev, hrk, hs₁⟩ := hDS
  rw [apply_pileStack_iff] at hPS
  obtain ⟨htop', b₀', hb', hrk', hs₂⟩ := hPS
  rw [apply_pileStack_iff] at hPS'
  obtain ⟨htop₂, b₀, hb, hrk₂, hs₃⟩ := hPS'
  rw [apply_deckStack_iff] at hDS'
  obtain ⟨hprev', hrk', hs₄⟩ := hDS'
  have hPSt : (Move.pileStack c').touch st = ([b₀], [c']) := by
    simp only [Move.touch, hb, Option.toList_some]
  rw [hPSt] at hdisj
  have hD2 : ∀ x ∈ [c], x ∉ [c'] := hdisj.2
  have hcc' : c ≠ c' := fun hcon => hD2 c (by simp) (by rw [hcon]; simp)
  -- a shared suit contradicts the two deckStack guards (one reads the
  -- pre-bump height, the other the post-bump)
  by_cases hσ : c'.suit = c.suit
  · exfalso
    rw [hs₃] at hrk'
    have hrk'' : c.rank.toIdx = (if c.suit = c'.suit then st.heights c.suit + 1
      else st.heights c.suit) := hrk'
    rw [if_pos hσ.symm] at hrk''
    omega
  -- the suits differ: the bumps land on independent coordinates
  have hb₂ : st.board.bottomOf c' = some b₀' := by
    rw [hs₁] at hb'
    exact hb'
  rw [hb] at hb₂
  have hb₀e : b₀' = b₀ := (Option.some.inj hb₂).symm
  rw [hs₂, hs₁, hs₄, hs₃, hb₀e]
  refine state_ext rfl rfl ?_ rfl rfl rfl
  exact heights_bump_bump st.heights c.suit c'.suit

theorem comm_deckStack_stackPile {st : State} {c c' : Card} {b' : Base} {st₂ st₃ : State}
    (hdisj : disjointTouch ((Move.deckStack c).touch st) ((Move.stackPile c' b').touch st))
    (h₁ : (st.apply (Move.deckStack c) >>= fun s => s.apply (Move.stackPile c' b')) = some st₂)
    (h₂ : (st.apply (Move.stackPile c' b') >>= fun s => s.apply (Move.deckStack c)) = some st₃) :
    st₂ = st₃ := by
  obtain ⟨s₁, hDS, hSP⟩ := Option.bind_eq_some_iff.mp h₁
  obtain ⟨s₃, hSP', hDS'⟩ := Option.bind_eq_some_iff.mp h₂
  rw [apply_deckStack_iff] at hDS
  obtain ⟨hprev, hrk, hs₁⟩ := hDS
  rw [apply_stackPile_iff] at hSP
  obtain ⟨hrk', hcp', bd₂, hatt', hs₂⟩ := hSP
  rw [apply_stackPile_iff] at hSP'
  obtain ⟨hrk₂, hcp, bd₃, hatt₁, hs₃⟩ := hSP'
  rw [apply_deckStack_iff] at hDS'
  obtain ⟨hprev', hrk'', hs₄⟩ := hDS'
  have hD2 : ∀ x ∈ [c], x ∉ [c'] := hdisj.2
  have hcc' : c ≠ c' := fun hcon => hD2 c (by simp) (by rw [hcon]; simp)
  -- a shared suit contradicts the deckStack guards through the drop
  have hvac : c.suit = c'.suit → False := by
    intro hσ
    rw [hs₃] at hrk''
    have hrk3 : c.rank.toIdx = (if c.suit = c'.suit then st.heights c.suit - 1
      else st.heights c.suit) := hrk''
    rw [if_pos hσ] at hrk3
    rw [← hσ] at hrk₂
    omega
  have hpos : c'.suit = c.suit → 0 < st.heights c'.suit := fun _ => by
    have := hrk₂
    omega
  -- the two stackPile attaches are the same op on the same board
  rw [hs₁] at hatt'
  have hatt'₂ : st.board.attach b' c' = some bd₂ := hatt'
  have hbd : bd₂ = bd₃ := Option.some.inj (hatt'₂.symm.trans hatt₁)
  rw [hs₂, hs₁, hs₄, hs₃, hbd]
  refine state_ext rfl rfl ?_ rfl rfl rfl
  exact (heights_bump_drop st.heights c'.suit c.suit hpos).symm

theorem comm_pileStack_pileStack {st : State} {c c' : Card} {st₂ st₃ : State}
    (hdisj : disjointTouch ((Move.pileStack c).touch st) ((Move.pileStack c').touch st))
    (h₁ : (st.apply (Move.pileStack c) >>= fun s => s.apply (Move.pileStack c')) = some st₂)
    (h₂ : (st.apply (Move.pileStack c') >>= fun s => s.apply (Move.pileStack c)) = some st₃) :
    st₂ = st₃ := by
  obtain ⟨s₁, hPS, hPS'⟩ := Option.bind_eq_some_iff.mp h₁
  obtain ⟨s₃, hPS'', hPS'''⟩ := Option.bind_eq_some_iff.mp h₂
  rw [apply_pileStack_iff] at hPS
  obtain ⟨htop, b₀, hb, hrk, hs₁⟩ := hPS
  rw [apply_pileStack_iff] at hPS'
  obtain ⟨htop', b₀', hb', hrk', hs₂⟩ := hPS'
  rw [apply_pileStack_iff] at hPS''
  obtain ⟨htop₂, b₀₂, hb₂, hrk₂, hs₃⟩ := hPS''
  rw [apply_pileStack_iff] at hPS'''
  obtain ⟨htop₃, b₀₃, hb₃, hrk₃, hs₄⟩ := hPS'''
  have hPSt : (Move.pileStack c).touch st = ([b₀], [c]) := by
    simp only [Move.touch, hb, Option.toList_some]
  have hPSt' : (Move.pileStack c').touch st = ([b₀₂], [c']) := by
    simp only [Move.touch, hb₂, Option.toList_some]
  rw [hPSt, hPSt'] at hdisj
  have hD1 : ∀ β ∈ [b₀], β ∉ ([b₀₂] : List Base) := hdisj.1
  have hD2 : ∀ x ∈ [c], x ∉ [c'] := hdisj.2
  have hbb₀ : b₀ ≠ b₀₂ := fun hcon => hD1 b₀ (by simp) (by rw [hcon]; simp)
  have hcc' : c ≠ c' := fun hcon => hD2 c (by simp) (by rw [hcon]; simp)
  -- a shared suit contradicts the two pileStack guards (one reads the
  -- pre-bump height, the other the post-bump)
  by_cases hσ : c'.suit = c.suit
  · exfalso
    rw [hs₃] at hrk₃
    have hrk4 : c.rank.toIdx = (if c.suit = c'.suit then st.heights c.suit + 1
      else st.heights c.suit) := hrk₃
    rw [if_pos hσ.symm] at hrk4
    omega
  -- the second detach reads the same seat in both orders
  have htb₀ : st.board.topOf b₀ = some c := (Board.bottomOf_eq st.board c b₀).mp hb
  have htb₀₂ : st.board.topOf b₀₂ = some c' := (Board.bottomOf_eq st.board c' b₀₂).mp hb₂
  rw [hs₁] at hb'
  have hb₁ : (st.board.detach b₀).bottomOf c' = some b₀' := hb'
  rw [bottomOf_detach_ne htb₀ (Ne.symm hcc'), hb₂] at hb₁
  have hb₀e : b₀' = b₀₂ := (Option.some.inj hb₁).symm
  rw [hs₃] at hb₃
  have hb₃' : (st.board.detach b₀₂).bottomOf c = some b₀₃ := hb₃
  rw [bottomOf_detach_ne htb₀₂ hcc', hb] at hb₃'
  have hb₀₃e : b₀₃ = b₀ := (Option.some.inj hb₃').symm
  rw [hs₂, hs₁, hs₄, hs₃, hb₀e, hb₀₃e]
  refine state_ext rfl ?_ ?_ rfl rfl rfl
  · exact detach_detach_comm hbb₀
  · exact heights_bump_bump st.heights c.suit c'.suit

theorem comm_pileStack_stackPile {st : State} {c c' : Card} {b' : Base} {st₂ st₃ : State}
    (hdisj : disjointTouch ((Move.pileStack c).touch st) ((Move.stackPile c' b').touch st))
    (h₁ : (st.apply (Move.pileStack c) >>= fun s => s.apply (Move.stackPile c' b')) = some st₂)
    (h₂ : (st.apply (Move.stackPile c' b') >>= fun s => s.apply (Move.pileStack c)) = some st₃) :
    st₂ = st₃ := by
  obtain ⟨s₁, hPS, hSP⟩ := Option.bind_eq_some_iff.mp h₁
  obtain ⟨s₃, hSP', hPS'⟩ := Option.bind_eq_some_iff.mp h₂
  rw [apply_pileStack_iff] at hPS
  obtain ⟨htop, b₀, hb, hrk, hs₁⟩ := hPS
  rw [apply_stackPile_iff] at hSP
  obtain ⟨hrk', hcp', bd₂, hatt', hs₂⟩ := hSP
  rw [apply_stackPile_iff] at hSP'
  obtain ⟨hrk₂, hcp, bd₃, hatt₁, hs₃⟩ := hSP'
  rw [apply_pileStack_iff] at hPS'
  obtain ⟨htop₃, b₀₃, hb₃, hrk₃, hs₄⟩ := hPS'
  have hPSt : (Move.pileStack c).touch st = ([b₀], [c]) := by
    simp only [Move.touch, hb, Option.toList_some]
  rw [hPSt] at hdisj
  have hD1 : ∀ β ∈ [b₀], β ∉ ([b'] : List Base) := hdisj.1
  have hD2 : ∀ x ∈ [c], x ∉ [c'] := hdisj.2
  have hb₀b' : b₀ ≠ b' := fun hcon => hD1 b₀ (by simp) (by rw [hcon]; simp)
  have hcc' : c ≠ c' := fun hcon => hD2 c (by simp) (by rw [hcon]; simp)
  -- a shared suit contradicts the guards through the drop
  have hvac : c'.suit = c.suit → False := by
    intro hσ
    rw [hs₃] at hrk₃
    have hrk4 : c.rank.toIdx = (if c.suit = c'.suit then st.heights c.suit - 1
      else st.heights c.suit) := hrk₃
    rw [if_pos hσ.symm] at hrk4
    rw [hσ] at hrk₂
    omega
  have hpos : c'.suit = c.suit → 0 < st.heights c'.suit := by
    intro _
    have := hrk₂
    omega
  -- the detach/attach bases agree in both orders
  have htb₀ : st.board.topOf b₀ = some c := (Board.bottomOf_eq st.board c b₀).mp hb
  rw [hs₃] at hb₃
  have hb₃' : bd₃.bottomOf c = some b₀₃ := hb₃
  rw [bottomOf_attach_ne hatt₁ hcc', hb] at hb₃'
  have hb₀₃e : b₀₃ = b₀ := (Option.some.inj hb₃').symm
  rw [hs₁] at hatt'
  have hatt'₂ : (st.board.detach b₀).attach b' c' = some bd₂ := hatt'
  rw [hs₂, hs₁, hs₄, hs₃, hb₀₃e]
  refine state_ext rfl ?_ ?_ rfl rfl rfl
  · exact (attach_detach_comm (Ne.symm hb₀b') hatt₁ hatt'₂).symm
  · exact (heights_bump_drop st.heights c'.suit c.suit hpos).symm

theorem comm_pileStack_pilePile {st : State} {c c' : Card} {b' : Base} {st₂ st₃ : State}
    (hdisj : disjointTouch ((Move.pileStack c).touch st) ((Move.pilePile c' b').touch st))
    (h₁ : (st.apply (Move.pileStack c) >>= fun s => s.apply (Move.pilePile c' b')) = some st₂)
    (h₂ : (st.apply (Move.pilePile c' b') >>= fun s => s.apply (Move.pileStack c)) = some st₃) :
    st₂ = st₃ := by
  obtain ⟨s₁, hPS, hPP⟩ := Option.bind_eq_some_iff.mp h₁
  obtain ⟨s₃, hPP', hPS'⟩ := Option.bind_eq_some_iff.mp h₂
  rw [apply_pileStack_iff] at hPS
  obtain ⟨htop, b₀, hb, hrk, hs₁⟩ := hPS
  rw [apply_pilePile_iff] at hPP
  obtain ⟨b₀', hb', hne', hcmr', bd₂, hatt', hs₂⟩ := hPP
  rw [apply_pilePile_iff] at hPP'
  obtain ⟨b₀₂, hb₂, hne, hcmr, bd₃, hatt₁, hs₃⟩ := hPP'
  rw [apply_pileStack_iff] at hPS'
  obtain ⟨htop₃, b₀₃, hb₃, hrk₃, hs₄⟩ := hPS'
  have hPSt : (Move.pileStack c).touch st = ([b₀], [c]) := by
    simp only [Move.touch, hb, Option.toList_some]
  have hPPt : (Move.pilePile c' b').touch st = (b' :: [b₀₂], c' :: st.board.aboveOf c') := by
    simp only [Move.touch, hb₂, Option.toList_some]
  rw [hPSt, hPPt] at hdisj
  have hD1 : ∀ β ∈ [b₀], β ∉ (b' :: [b₀₂] : List Base) := hdisj.1
  have hD2 : ∀ x ∈ [c], x ∉ (c' :: st.board.aboveOf c') := hdisj.2
  have hb₀b' : b₀ ≠ b' := fun hcon => hD1 b₀ (by simp) (by rw [hcon]; simp)
  have hb₀b₂ : b₀ ≠ b₀₂ := fun hcon => hD1 b₀ (by simp) (by simp [hcon])
  have hcc' : c ≠ c' := fun hcon => hD2 c (by simp) (by rw [hcon]; simp)
  -- the detach bases agree in both orders
  have htb₀ : st.board.topOf b₀ = some c := (Board.bottomOf_eq st.board c b₀).mp hb
  have htb₀₂ : st.board.topOf b₀₂ = some c' := (Board.bottomOf_eq st.board c' b₀₂).mp hb₂
  rw [hs₁] at hb'
  have hb₁ : (st.board.detach b₀).bottomOf c' = some b₀' := hb'
  rw [bottomOf_detach_ne htb₀ (Ne.symm hcc'), hb₂] at hb₁
  have hb₀e : b₀' = b₀₂ := (Option.some.inj hb₁).symm
  rw [hs₃] at hb₃
  have hb₃' : bd₃.bottomOf c = some b₀₃ := hb₃
  rw [bottomOf_attach_ne hatt₁ hcc', bottomOf_detach_ne htb₀₂ hcc', hb] at hb₃'
  have hb₀₃e : b₀₃ = b₀ := (Option.some.inj hb₃').symm
  rw [hs₁, hb₀e] at hatt'
  have hatt'₂ : ((st.board.detach b₀).detach b₀₂).attach b' c' = some bd₂ := hatt'
  rw [detach_detach_comm hb₀b₂] at hatt'₂
  rw [hs₂, hs₁, hs₄, hs₃, hb₀₃e]
  refine state_ext rfl ?_ rfl rfl rfl rfl
  exact (attach_detach_comm (Ne.symm hb₀b') hatt₁ hatt'₂).symm

theorem comm_stackPile_stackPile {st : State} {c c' : Card} {b b' : Base} {st₂ st₃ : State}
    (hdisj : disjointTouch ((Move.stackPile c b).touch st) ((Move.stackPile c' b').touch st))
    (h₁ : (st.apply (Move.stackPile c b) >>= fun s => s.apply (Move.stackPile c' b')) = some st₂)
    (h₂ : (st.apply (Move.stackPile c' b') >>= fun s => s.apply (Move.stackPile c b)) = some st₃) :
    st₂ = st₃ := by
  obtain ⟨s₁, hSP, hSP'⟩ := Option.bind_eq_some_iff.mp h₁
  obtain ⟨s₃, hSP'', hSP'''⟩ := Option.bind_eq_some_iff.mp h₂
  rw [apply_stackPile_iff] at hSP
  obtain ⟨hrk, hcp, bd₁, hatt, hs₁⟩ := hSP
  rw [apply_stackPile_iff] at hSP'
  obtain ⟨hrk', hcp', bd₂, hatt', hs₂⟩ := hSP'
  rw [apply_stackPile_iff] at hSP''
  obtain ⟨hrk₂, hcp₂, bd₃, hatt₁, hs₃⟩ := hSP''
  rw [apply_stackPile_iff] at hSP'''
  obtain ⟨hrk₃, hcp₃, bd₄, hatt₂', hs₄⟩ := hSP'''
  have hD1 : ∀ β ∈ [b], β ∉ ([b'] : List Base) := hdisj.1
  have hD2 : ∀ x ∈ [c], x ∉ [c'] := hdisj.2
  have hbb' : b ≠ b' := fun hcon => hD1 b (by simp) (by rw [hcon]; simp)
  have hcc' : c ≠ c' := fun hcon => hD2 c (by simp) (by rw [hcon]; simp)
  -- a shared suit contradicts the two guards through the drop
  by_cases hσ : c'.suit = c.suit
  · exfalso
    rw [hs₃] at hrk₃
    have hrk4 : c.rank.toIdx + 1 = (if c.suit = c'.suit then st.heights c.suit - 1
      else st.heights c.suit) := hrk₃
    rw [if_pos hσ.symm] at hrk4
    omega
  rw [hs₁] at hatt'
  have hatt'₂ : bd₁.attach b' c' = some bd₂ := hatt'
  rw [hs₃] at hatt₂'
  have hatt₂'' : bd₃.attach b c = some bd₄ := hatt₂'
  have hbd : bd₂ = bd₄ := Board.attach_attach_comm hbb' hatt hatt'₂ hatt₁ hatt₂''
  rw [hs₂, hs₁, hs₄, hs₃, hbd]
  refine state_ext rfl rfl ?_ rfl rfl rfl
  exact heights_drop_drop st.heights c.suit c'.suit

theorem comm_stackPile_pilePile {st : State} {c c' : Card} {b b' : Base} {st₂ st₃ : State}
    (hdisj : disjointTouch ((Move.stackPile c b).touch st) ((Move.pilePile c' b').touch st))
    (h₁ : (st.apply (Move.stackPile c b) >>= fun s => s.apply (Move.pilePile c' b')) = some st₂)
    (h₂ : (st.apply (Move.pilePile c' b') >>= fun s => s.apply (Move.stackPile c b)) = some st₃) :
    st₂ = st₃ := by
  obtain ⟨s₁, hSP, hPP⟩ := Option.bind_eq_some_iff.mp h₁
  obtain ⟨s₃, hPP', hSP'⟩ := Option.bind_eq_some_iff.mp h₂
  rw [apply_stackPile_iff] at hSP
  obtain ⟨hrk, hcp, bd₁, hatt, hs₁⟩ := hSP
  rw [apply_pilePile_iff] at hPP
  obtain ⟨b₀', hb', hne', hcmr', bd₂, hatt', hs₂⟩ := hPP
  rw [apply_pilePile_iff] at hPP'
  obtain ⟨b₀, hb, hne, hcmr, bd₃, hatt₁, hs₃⟩ := hPP'
  rw [apply_stackPile_iff] at hSP'
  obtain ⟨hrk', hcp', bd₄, hatt₂', hs₄⟩ := hSP'
  have hPPt : (Move.pilePile c' b').touch st = (b' :: [b₀], c' :: st.board.aboveOf c') := by
    simp only [Move.touch, hb, Option.toList_some]
  rw [hPPt] at hdisj
  have hD1 : ∀ β ∈ [b], β ∉ (b' :: [b₀] : List Base) := hdisj.1
  have hD2 : ∀ x ∈ [c], x ∉ (c' :: st.board.aboveOf c') := hdisj.2
  have hbb' : b ≠ b' := fun hcon => hD1 b (by simp) (by rw [hcon]; simp)
  have hbb₀ : b ≠ b₀ := fun hcon => hD1 b (by simp) (by simp [hcon])
  have hcc' : c ≠ c' := fun hcon => hD2 c (by simp) (by rw [hcon]; simp)
  -- pilePile's detach base agrees in both orders
  rw [hs₁] at hb'
  have hb₂ : bd₁.bottomOf c' = some b₀' := hb'
  rw [bottomOf_attach_ne hatt (Ne.symm hcc'), hb] at hb₂
  have hb₀e : b₀' = b₀ := (Option.some.inj hb₂).symm
  rw [hs₁, hb₀e] at hatt'
  have hatt'₂ : (bd₁.detach b₀).attach b' c' = some bd₂ := hatt'
  rw [hs₃] at hatt₂'
  have hatt₂'' : bd₃.attach b c = some bd₄ := hatt₂'
  -- the board: attach b c, detach b₀, attach b' c' — three distinct bases
  have hbd : bd₂ = bd₄ := by
    refine Board.ext_topOf (funext (fun x => ?_))
    by_cases hxb : x = b
    · rw [hxb, Board.attach_topOf_ne _ _ _ hatt'₂ hbb',
        Board.detach_topOf_ne _ _ _ hbb₀, Board.attach_topOf _ _ _ hatt,
        Board.attach_topOf _ _ _ hatt₂'']
    · by_cases hxb' : x = b'
      · rw [hxb', Board.attach_topOf _ _ _ hatt'₂, Board.attach_topOf_ne _ _ _ hatt₂'' (Ne.symm hbb'),
          Board.attach_topOf _ _ _ hatt₁]
      · by_cases hxb₀ : x = b₀
        · rw [hxb₀, Board.attach_topOf_ne _ _ _ hatt'₂ hne, Board.detach_topOf,
            Board.attach_topOf_ne _ _ _ hatt₂'' (Ne.symm hbb₀),
            Board.attach_topOf_ne _ _ _ hatt₁ hne, Board.detach_topOf]
        · rw [Board.attach_topOf_ne _ _ _ hatt'₂ hxb', Board.detach_topOf_ne _ _ _ hxb₀,
            Board.attach_topOf_ne _ _ _ hatt hxb,
            Board.attach_topOf_ne _ _ _ hatt₂'' hxb,
            Board.attach_topOf_ne _ _ _ hatt₁ hxb',
            Board.detach_topOf_ne _ _ _ hxb₀]
  rw [hs₂, hs₁, hs₄, hs₃, hbd]

theorem comm_pilePile_pilePile {st : State} {c c' : Card} {b b' : Base} {st₂ st₃ : State}
    (hdisj : disjointTouch ((Move.pilePile c b).touch st) ((Move.pilePile c' b').touch st))
    (h₁ : (st.apply (Move.pilePile c b) >>= fun s => s.apply (Move.pilePile c' b')) = some st₂)
    (h₂ : (st.apply (Move.pilePile c' b') >>= fun s => s.apply (Move.pilePile c b)) = some st₃) :
    st₂ = st₃ := by
  obtain ⟨s₁, hPP, hPP'⟩ := Option.bind_eq_some_iff.mp h₁
  obtain ⟨s₃, hPP'', hPP'''⟩ := Option.bind_eq_some_iff.mp h₂
  rw [apply_pilePile_iff] at hPP
  obtain ⟨b₀, hb, hne, hcmr, bd₁, hatt, hs₁⟩ := hPP
  rw [apply_pilePile_iff] at hPP'
  obtain ⟨b₀', hb', hne', hcmr', bd₂, hatt', hs₂⟩ := hPP'
  rw [apply_pilePile_iff] at hPP''
  obtain ⟨b₀'', hb'', hne'', hcmr'', bd₃, hatt₁, hs₃⟩ := hPP''
  rw [apply_pilePile_iff] at hPP'''
  obtain ⟨b₀''', hb''', hne''', hcmr''', bd₄, hatt₂', hs₄⟩ := hPP'''
  have hPPt : (Move.pilePile c b).touch st = (b :: [b₀], c :: st.board.aboveOf c) := by
    simp only [Move.touch, hb, Option.toList_some]
  have hPPt' : (Move.pilePile c' b').touch st = (b' :: [b₀''], c' :: st.board.aboveOf c') := by
    simp only [Move.touch, hb'', Option.toList_some]
  rw [hPPt, hPPt'] at hdisj
  have hD1 : ∀ β ∈ (b :: [b₀] : List Base), β ∉ (b' :: [b₀'']) := hdisj.1
  have hD2 : ∀ x ∈ (c :: st.board.aboveOf c), x ∉ (c' :: st.board.aboveOf c') := hdisj.2
  have hbb' : b ≠ b' := fun hcon => hD1 b (by simp) (by rw [hcon]; simp)
  have hbb'' : b ≠ b₀'' := fun hcon => hD1 b (by simp) (by simp [hcon])
  have hb₀b' : b₀ ≠ b' := fun hcon => hD1 b₀ (by simp) (by rw [hcon]; simp)
  have hb₀b'' : b₀ ≠ b₀'' := fun hcon => hD1 b₀ (by simp) (by simp [hcon])
  have hcc' : c ≠ c' := fun hcon => hD2 c (by simp) (by rw [hcon]; simp)
  -- the detach bases agree in both orders
  rw [hs₁] at hb'
  have hb₂ : bd₁.bottomOf c' = some b₀' := hb'
  rw [bottomOf_attach_ne hatt (Ne.symm hcc'), bottomOf_detach_ne
    ((Board.bottomOf_eq st.board c b₀).mp hb) (Ne.symm hcc'), hb''] at hb₂
  have hb₀e : b₀' = b₀'' := (Option.some.inj hb₂).symm
  rw [hs₃] at hb'''
  have hb₃ : bd₃.bottomOf c = some b₀''' := hb'''
  rw [bottomOf_attach_ne hatt₁ hcc', bottomOf_detach_ne
    ((Board.bottomOf_eq st.board c' b₀'').mp hb'') hcc', hb] at hb₃
  have hb₀₃e : b₀''' = b₀ := (Option.some.inj hb₃).symm
  rw [hs₁, hb₀e] at hatt'
  rw [hb₀e] at hne'
  have hatt'₂ : (bd₁.detach b₀'').attach b' c' = some bd₂ := hatt'
  rw [hs₃, hb₀₃e] at hatt₂'
  have hatt₂'' : (bd₃.detach b₀).attach b c = some bd₄ := hatt₂'
  have hb₀''b' : b₀'' ≠ b' := hne'
  -- the board: two detaches and two attaches at four distinct bases
  have hbd : bd₂ = bd₄ := by
    refine Board.ext_topOf (funext (fun x => ?_))
    by_cases hxb : x = b
    · rw [hxb, Board.attach_topOf_ne _ _ _ hatt'₂ hbb', Board.detach_topOf_ne _ _ _ hbb'',
        Board.attach_topOf _ _ _ hatt, Board.attach_topOf _ _ _ hatt₂'']
    · by_cases hxb' : x = b'
      · rw [hxb', Board.attach_topOf _ _ _ hatt'₂, Board.attach_topOf_ne _ _ _ hatt₂'' (Ne.symm hbb'),
          Board.detach_topOf_ne _ _ _ (Ne.symm hb₀b'), Board.attach_topOf _ _ _ hatt₁]
      · by_cases hxb₀ : x = b₀
        · rw [hxb₀, Board.attach_topOf_ne _ _ _ hatt'₂ hb₀b', Board.detach_topOf_ne _ _ _ hb₀b'',
            Board.attach_topOf_ne _ _ _ hatt hne, Board.detach_topOf,
            Board.attach_topOf_ne _ _ _ hatt₂'' hne, Board.detach_topOf]
        · by_cases hxb₀'' : x = b₀''
          · rw [hxb₀'', Board.attach_topOf_ne _ _ _ hatt'₂ hb₀''b', Board.detach_topOf,
              Board.attach_topOf_ne _ _ _ hatt₂'' (Ne.symm hbb''),
              Board.detach_topOf_ne _ _ _ (Ne.symm hb₀b''), Board.attach_topOf_ne _ _ _ hatt₁ hb₀''b',
              Board.detach_topOf]
          · rw [Board.attach_topOf_ne _ _ _ hatt'₂ hxb', Board.detach_topOf_ne _ _ _ hxb₀'',
              Board.attach_topOf_ne _ _ _ hatt hxb, Board.detach_topOf_ne _ _ _ hxb₀,
              Board.attach_topOf_ne _ _ _ hatt₂'' hxb, Board.detach_topOf_ne _ _ _ hxb₀,
              Board.attach_topOf_ne _ _ _ hatt₁ hxb', Board.detach_topOf_ne _ _ _ hxb₀'']
  rw [hs₂, hs₁, hs₄, hs₃, hbd]

/-- The fine-grained commutation schema — the type-ball interaction
lemma.  Moves with disjoint touch-sets commute (given both orders are
defined).

STATEMENT REPAIR (2026-09-13, prover-confirmed witness
`Temp\opencode\CommuteWitness.lean`): as originally staged (the
`hdisj` guard alone) this is FALSE for `{m, m'} = {draw, deckPile}`
(dually deckStack) — `.draw`'s touch set is ([], []), disjoint from
everything, but the deck moves' legality reads the waste top
(cursor-sensitive), which the deal changes: stock [cK, h2, cK, h4],
cursor 1, step 2, `cK` a king landing on a free anchor — both orders
succeed, landing on stocks [h2, cK, h4] and [cK, h2, h4].  Minimal
repair: the `hnc` guard — a deal only commutes with non-consuming
moves.  With it: `draw`-rows are `deal_commutes_nonStock`; the four
deck·deck pairs are vacuous (both first moves read the same `prev`);
reveal·deckStack and pilePile·deckStack fall to the coarse
`commute_of_compsDisjoint`; and the remaining sixteen fine pairs are
the `comm_*` lemmas above. -/
theorem commute_of_disjoint_touch {st : State} {m m' : Move} {st₂ st₃ : State}
    (hdisj : disjointTouch (m.touch st) (m'.touch st))
    (hnc : (m = Move.draw → m'.consumesStock = false) ∧
           (m' = Move.draw → m.consumesStock = false))
    (h₁ : (st.apply m >>= fun s => s.apply m') = some st₂)
    (h₂ : (st.apply m' >>= fun s => s.apply m) = some st₃) : st₂ = st₃ := by
  cases m with
  | draw =>
      cases m' with
      | draw => exact Option.some.inj (h₁.symm.trans h₂)
      | reveal c =>
          have hcomp := deal_commutes_nonStock st (Move.reveal c) (hnc.1 rfl)
          exact Option.some.inj (h₁.symm.trans (hcomp.symm.trans h₂))
      | deckPile c b => exact absurd (hnc.1 rfl) (by simp [Move.consumesStock])
      | deckStack c => exact absurd (hnc.1 rfl) (by simp [Move.consumesStock])
      | pileStack c =>
          have hcomp := deal_commutes_nonStock st (Move.pileStack c) (hnc.1 rfl)
          exact Option.some.inj (h₁.symm.trans (hcomp.symm.trans h₂))
      | stackPile c b =>
          have hcomp := deal_commutes_nonStock st (Move.stackPile c b) (hnc.1 rfl)
          exact Option.some.inj (h₁.symm.trans (hcomp.symm.trans h₂))
      | pilePile c b =>
          have hcomp := deal_commutes_nonStock st (Move.pilePile c b) (hnc.1 rfl)
          exact Option.some.inj (h₁.symm.trans (hcomp.symm.trans h₂))
  | reveal c =>
      cases m' with
      | draw =>
          have hcomp := deal_commutes_nonStock st (Move.reveal c) (hnc.2 rfl)
          exact Option.some.inj (h₁.symm.trans (hcomp.trans h₂))
      | reveal c' => exact comm_reveal_reveal hdisj h₁ h₂
      | deckPile c' b' => exact comm_reveal_deckPile hdisj h₁ h₂
      | deckStack c' =>
          have hcomp := commute_of_compsDisjoint st (Move.reveal c) (Move.deckStack c') (by
            intro x hx
            cases x with
            | tableau => simp [Move.comps]
            | foundations => simp [Move.comps] at hx
            | hidden => simp [Move.comps]
            | stock => simp [Move.comps] at hx)
          exact Option.some.inj (h₁.symm.trans (hcomp.trans h₂))
      | pileStack c' => exact comm_reveal_pileStack hdisj h₁ h₂
      | stackPile c' b' => exact comm_reveal_stackPile hdisj h₁ h₂
      | pilePile c' b' => exact comm_reveal_pilePile hdisj h₁ h₂
  | deckPile c b =>
      cases m' with
      | draw =>
          have hcomp := deal_commutes_nonStock st (Move.deckPile c b) (hnc.2 rfl)
          exact Option.some.inj (h₁.symm.trans (hcomp.trans h₂))
      | reveal c' => exact (comm_reveal_deckPile (disjointTouch_symm hdisj) h₂ h₁).symm
      | deckPile c' b' =>
          exfalso
          obtain ⟨s₁, hA, _⟩ := Option.bind_eq_some_iff.mp h₁
          obtain ⟨s₃, hC, _⟩ := Option.bind_eq_some_iff.mp h₂
          rw [apply_deckPile_iff] at hA hC
          obtain ⟨hprev, _, _, _, _⟩ := hA
          obtain ⟨hprev', _, _, _, _⟩ := hC
          rw [hprev] at hprev'
          have hcc' : c ≠ c' := fun hcon =>
            hdisj.2 c (by show c ∈ [c]; simp) (by rw [hcon]; show c' ∈ [c']; simp)
          exact hcc' (Option.some.inj hprev')
      | deckStack c' =>
          exfalso
          obtain ⟨s₁, hA, _⟩ := Option.bind_eq_some_iff.mp h₁
          obtain ⟨s₃, hC, _⟩ := Option.bind_eq_some_iff.mp h₂
          rw [apply_deckPile_iff] at hA
          rw [apply_deckStack_iff] at hC
          obtain ⟨hprev, _, _, _, _⟩ := hA
          obtain ⟨hprev', _, _⟩ := hC
          rw [hprev] at hprev'
          have hcc' : c ≠ c' := fun hcon =>
            hdisj.2 c (by show c ∈ [c]; simp) (by rw [hcon]; show c' ∈ [c']; simp)
          exact hcc' (Option.some.inj hprev')
      | pileStack c' => exact comm_deckPile_pileStack hdisj h₁ h₂
      | stackPile c' b' => exact comm_deckPile_stackPile hdisj h₁ h₂
      | pilePile c' b' => exact comm_deckPile_pilePile hdisj h₁ h₂
  | deckStack c =>
      cases m' with
      | draw =>
          have hcomp := deal_commutes_nonStock st (Move.deckStack c) (hnc.2 rfl)
          exact Option.some.inj (h₁.symm.trans (hcomp.trans h₂))
      | reveal c' =>
          have hcomp := commute_of_compsDisjoint st (Move.deckStack c) (Move.reveal c') (by
            intro x hx
            cases x with
            | tableau => simp [Move.comps] at hx
            | foundations => simp [Move.comps]
            | hidden => simp [Move.comps] at hx
            | stock => simp [Move.comps])
          exact Option.some.inj (h₁.symm.trans (hcomp.trans h₂))
      | deckPile c' b' =>
          exfalso
          obtain ⟨s₁, hA, _⟩ := Option.bind_eq_some_iff.mp h₁
          obtain ⟨s₃, hC, _⟩ := Option.bind_eq_some_iff.mp h₂
          rw [apply_deckStack_iff] at hA
          rw [apply_deckPile_iff] at hC
          obtain ⟨hprev, _, _⟩ := hA
          obtain ⟨hprev', _, _, _, _⟩ := hC
          rw [hprev] at hprev'
          have hcc' : c ≠ c' := fun hcon =>
            hdisj.2 c (by show c ∈ [c]; simp) (by rw [hcon]; show c' ∈ [c']; simp)
          exact hcc' (Option.some.inj hprev')
      | deckStack c' =>
          exfalso
          obtain ⟨s₁, hA, _⟩ := Option.bind_eq_some_iff.mp h₁
          obtain ⟨s₃, hC, _⟩ := Option.bind_eq_some_iff.mp h₂
          rw [apply_deckStack_iff] at hA hC
          obtain ⟨hprev, _, _⟩ := hA
          obtain ⟨hprev', _, _⟩ := hC
          rw [hprev] at hprev'
          have hcc' : c ≠ c' := fun hcon =>
            hdisj.2 c (by show c ∈ [c]; simp) (by rw [hcon]; show c' ∈ [c']; simp)
          exact hcc' (Option.some.inj hprev')
      | pileStack c' => exact comm_deckStack_pileStack hdisj h₁ h₂
      | stackPile c' b' => exact comm_deckStack_stackPile hdisj h₁ h₂
      | pilePile c' b' =>
          have hcomp := commute_of_compsDisjoint st (Move.deckStack c) (Move.pilePile c' b') (by
            intro x hx
            cases x with
            | tableau => simp [Move.comps] at hx
            | foundations => simp [Move.comps]
            | hidden => simp [Move.comps] at hx
            | stock => simp [Move.comps])
          exact Option.some.inj (h₁.symm.trans (hcomp.trans h₂))
  | pileStack c =>
      cases m' with
      | draw =>
          have hcomp := deal_commutes_nonStock st (Move.pileStack c) (hnc.2 rfl)
          exact Option.some.inj (h₁.symm.trans (hcomp.trans h₂))
      | reveal c' => exact (comm_reveal_pileStack (disjointTouch_symm hdisj) h₂ h₁).symm
      | deckPile c' b' => exact (comm_deckPile_pileStack (disjointTouch_symm hdisj) h₂ h₁).symm
      | deckStack c' => exact (comm_deckStack_pileStack (disjointTouch_symm hdisj) h₂ h₁).symm
      | pileStack c' => exact comm_pileStack_pileStack hdisj h₁ h₂
      | stackPile c' b' => exact comm_pileStack_stackPile hdisj h₁ h₂
      | pilePile c' b' => exact comm_pileStack_pilePile hdisj h₁ h₂
  | stackPile c b =>
      cases m' with
      | draw =>
          have hcomp := deal_commutes_nonStock st (Move.stackPile c b) (hnc.2 rfl)
          exact Option.some.inj (h₁.symm.trans (hcomp.trans h₂))
      | reveal c' => exact (comm_reveal_stackPile (disjointTouch_symm hdisj) h₂ h₁).symm
      | deckPile c' b' => exact (comm_deckPile_stackPile (disjointTouch_symm hdisj) h₂ h₁).symm
      | deckStack c' => exact (comm_deckStack_stackPile (disjointTouch_symm hdisj) h₂ h₁).symm
      | pileStack c' => exact (comm_pileStack_stackPile (disjointTouch_symm hdisj) h₂ h₁).symm
      | stackPile c' b' => exact comm_stackPile_stackPile hdisj h₁ h₂
      | pilePile c' b' => exact comm_stackPile_pilePile hdisj h₁ h₂
  | pilePile c b =>
      cases m' with
      | draw =>
          have hcomp := deal_commutes_nonStock st (Move.pilePile c b) (hnc.2 rfl)
          exact Option.some.inj (h₁.symm.trans (hcomp.trans h₂))
      | reveal c' => exact (comm_reveal_pilePile (disjointTouch_symm hdisj) h₂ h₁).symm
      | deckPile c' b' => exact (comm_deckPile_pilePile (disjointTouch_symm hdisj) h₂ h₁).symm
      | deckStack c' =>
          have hcomp := commute_of_compsDisjoint st (Move.pilePile c b) (Move.deckStack c') (by
            intro x hx
            cases x with
            | tableau => simp [Move.comps]
            | foundations => simp [Move.comps] at hx
            | hidden => simp [Move.comps] at hx
            | stock => simp [Move.comps] at hx)
          exact Option.some.inj (h₁.symm.trans (hcomp.trans h₂))
      | pileStack c' => exact (comm_pileStack_pilePile (disjointTouch_symm hdisj) h₂ h₁).symm
      | stackPile c' b' => exact (comm_stackPile_pilePile (disjointTouch_symm hdisj) h₂ h₁).symm
      | pilePile c' b' => exact comm_pilePile_pilePile hdisj h₁ h₂

/-! ### The Draw-commitment commutation kit

`applyDrawTo`'s stock op normalizes to `⟨removeIdx cards i, i⟩`
(`removeAt_drawTo`); the *second* draw of each order finds its card at
the first-occurrence position of the spliced list (`posOf_removeIdx_shift`
for a card after the splice, `..._keep` for one before it); the board
part is two `attach`es at distinct bases (`attach_attach_comm`). -/

/-- Splicing out an earlier position shifts a later first occurrence
down by one. -/
theorem findFirstIdx_removeIdx_shift {α : Type} (p : α → Bool) :
    ∀ (l : List α) (q r : Nat), Cycle.findFirstIdx p l = some r → q < r →
      Cycle.findFirstIdx p (Cycle.removeIdx l q) = some (r - 1) := by
  intro l
  induction l with
  | nil =>
      intro q r h _
      exact absurd h (by simp [Cycle.findFirstIdx])
  | cons a t ih =>
      intro q r h hqr
      have hc : (if p a then some 0 else (Cycle.findFirstIdx p t).map Nat.succ) = some r := h
      by_cases hpa : p a = true
      · rw [if_pos hpa, Option.some.injEq] at hc
        exact absurd hqr (by omega)
      · rw [if_neg hpa] at hc
        cases q with
        | zero =>
            rw [Cycle.removeIdx_zero]
            obtain ⟨r', hr', hrr⟩ := Option.map_eq_some_iff.mp hc
            rw [hr']
            exact congrArg some (by omega)
        | succ q' =>
            rw [Cycle.removeIdx_succ]
            obtain ⟨r', hr', hrr⟩ := Option.map_eq_some_iff.mp hc
            have hih := ih q' r' hr' (by omega)
            show (if p a then some 0
              else (Cycle.findFirstIdx p (Cycle.removeIdx t q')).map Nat.succ) = some (r - 1)
            rw [if_neg hpa, hih, Option.map_some]
            exact congrArg some (by omega)

/-- Splicing out a later position leaves an earlier first occurrence
where it was. -/
theorem findFirstIdx_removeIdx_keep {α : Type} (p : α → Bool) :
    ∀ (l : List α) (p₀ q : Nat), Cycle.findFirstIdx p l = some p₀ → p₀ < q →
      Cycle.findFirstIdx p (Cycle.removeIdx l q) = some p₀ := by
  intro l
  induction l with
  | nil =>
      intro p₀ q h _
      exact absurd h (by simp [Cycle.findFirstIdx])
  | cons a t ih =>
      intro p₀ q h hpq
      have hc : (if p a then some 0 else (Cycle.findFirstIdx p t).map Nat.succ) = some p₀ := h
      cases q with
      | zero => exact absurd hpq (by omega)
      | succ q' =>
          rw [Cycle.removeIdx_succ]
          by_cases hpa : p a = true
          · rw [if_pos hpa, Option.some.injEq] at hc
            show (if p a then some 0
              else (Cycle.findFirstIdx p (Cycle.removeIdx t q')).map Nat.succ) = some p₀
            rw [if_pos hpa, ← hc]
          · rw [if_neg hpa] at hc
            obtain ⟨r', hr', hrr⟩ := Option.map_eq_some_iff.mp hc
            have hih := ih r' q' hr' (by omega)
            show (if p a then some 0
              else (Cycle.findFirstIdx p (Cycle.removeIdx t q')).map Nat.succ) = some p₀
            rw [if_neg hpa, hih, Option.map_some]
            exact congrArg some (by omega)

/-- The shift lemma, `posOf` packaging (the cursor is never read). -/
theorem posOf_removeIdx_shift {x : Card} {l : List Card} {cur cur' : Nat} {q r : Nat}
    (h : Cycle.posOf x ⟨l, cur⟩ = some r) (hqr : q < r) :
    Cycle.posOf x ⟨Cycle.removeIdx l q, cur'⟩ = some (r - 1) :=
  findFirstIdx_removeIdx_shift _ l q r h hqr

/-- The keep lemma, `posOf` packaging (the cursor is never read). -/
theorem posOf_removeIdx_keep {x : Card} {l : List Card} {cur cur' : Nat} {p q : Nat}
    (h : Cycle.posOf x ⟨l, cur⟩ = some p) (hpq : p < q) :
    Cycle.posOf x ⟨Cycle.removeIdx l q, cur'⟩ = some p :=
  findFirstIdx_removeIdx_keep _ l p q h hpq

/-- The Draw-commitment's stock successor: jump past `i`, splice `i`
out — the cursor lands exactly on `i`. -/
theorem removeAt_drawTo {α : Type} (i : Nat) (cy : Cycle α) :
    (cy.drawTo i).removeAt i = { cards := Cycle.removeIdx cy.cards i, cursor := i } := by
  simp only [Cycle.removeAt, Cycle.drawTo]
  rw [if_pos (Nat.lt_succ_self i), Nat.add_sub_cancel]

/-- A successful Draw commitment's shape: the guard's index, the
board attach, and the successor with the spliced stock. -/
theorem applyDrawTo_eq {st : State} {c : Card} {b : Base} {s' : State}
    (h : st.applyDrawTo c b = some s') :
    ∃ i bd, st.reachablePos c = some i ∧ st.board.attach b c = some bd ∧
      s' = { st with
             board := bd,
             stock := { cards := Cycle.removeIdx st.stock.cards i, cursor := i } } := by
  simp only [State.applyDrawTo] at h
  cases hr : st.reachablePos c with
  | none => rw [hr] at h; simp at h
  | some i =>
      rw [hr] at h
      cases ha : st.board.attach b c with
      | none => rw [ha] at h; simp at h
      | some bd =>
          rw [ha] at h
          simp at h
          refine ⟨i, bd, rfl, rfl, ?_⟩
          rw [← h, removeAt_drawTo]

/-- The guard's index is the plain stock position. -/
theorem reachablePos_posOf {st : State} {c : Card} {i : Nat}
    (h : st.reachablePos c = some i) : st.stock.posOf c = some i := by
  simp only [State.reachablePos] at h
  split at h
  · next hpos =>
      cases hp : st.stock.posOf c with
      | none => rw [hp] at h; simp at h
      | some i' =>
          rw [hp] at h
          simp at h
          rw [h.2]
  · simp at h

/-- The guard's index is in the accessible set. -/
theorem reachablePos_mask {st : State} {c : Card} {i : Nat} (hpos : 0 < st.drawStep)
    (h : st.reachablePos c = some i) :
    i ∈ Pace.maskPos st.stock st.drawStep hpos := by
  simp only [State.reachablePos, dif_pos hpos] at h
  cases hp : st.stock.posOf c with
  | none => rw [hp] at h; simp at h
  | some i' =>
      rw [hp] at h
      simp at h
      rw [h.2] at h
      exact h.1

/-- Two attachments at distinct bases commute. -/
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

/-- At a saturated cursor (`cursor = length ≥ 2`) with a paced step
(`≥ 2`), position 0 is not accessible: every lane starts strictly
above 0. -/
theorem zero_notMem_maskPos {α : Type} {c : Cycle α} {step : Nat} (hstep : 0 < step)
    (h2 : 2 ≤ step) (hn : 2 ≤ c.cards.length) (hsat : c.cursor = c.cards.length) :
    0 ∉ Pace.maskPos c step hstep := by
  intro hmem
  have hmem' : 0 ∈ (Pace.laneUp step hstep
        (if c.cursor = 0 then step - 1 else c.cursor - 1) (c.cards.length - 1)
      ++ (if 0 < c.cards.length then [c.cards.length - 1] else [])
      ++ Pace.laneUp step hstep (step - 1)
        ((if c.cursor % step != 0 then c.cards.length else c.cursor) - 1)) := hmem
  simp only [List.mem_append] at hmem'
  rw [if_pos (by omega : 0 < c.cards.length), List.mem_singleton] at hmem'
  cases hmem' with
  | inl hmem'' =>
      cases hmem'' with
      | inl h1 =>
          obtain ⟨hle, -, -⟩ := (Pace.laneUp_mem step hstep _ _ 0).mp h1
          rw [hsat] at hle
          split at hle <;> omega
      | inr h01 => omega
  | inr h3 =>
      obtain ⟨hle, -, -⟩ := (Pace.laneUp_mem step hstep _ _ 0).mp h3
      omega

/-- **C13, generalized**: Draw-commitments at cycle-adjacent positions
commute (adjacency modulo the cycle length — the wrap counts), in the
paced game (`2 ≤ drawStep`).

STATEMENT REPAIR (2026-09-13, prover-confirmed): at step 1 the wrap
case (`i + 1 = len`, `j = 0`) is FALSE for `len ≥ 3` — the free-set
degeneration makes both orders legal and they land on different
cursors (`j` vs `len - 2`; witness: cards `[A,B,C]`, cursor 0, empty
board, `c` at 2, `c'` at 0 — end cursors 0 vs 1; the C-IND measurement's
`distinct` residual class).  The step guard is the minimal repair: with
it the wrap case at `len ≥ 3` is unreachable (order 1's second draw
would need position 0 in the mask of a saturated cursor —
`zero_notMem_maskPos`), and at `len = 2` both orders end at cursor 0
with the same (empty) splice. -/
theorem drawTo_comm_modAdjacent {st : State} {c c' : Card} {b b' : Base} {i j len : Nat}
    (hlen : st.stock.cards.length = len) (hadj : (i + 1) % len = j)
    (hic : st.stock.posOf c = some i) (hjc : st.stock.posOf c' = some j)
    (hbb : b ≠ b') (hstep : 2 ≤ st.drawStep) {st₂ st₄ : State}
    (h₂ : (st.applyDrawTo c b >>= fun s => s.applyDrawTo c' b') = some st₂)
    (h₄ : (st.applyDrawTo c' b' >>= fun s => s.applyDrawTo c b) = some st₄) :
    st₂ = st₄ := by
  have hilt : i < len := by rw [← hlen]; exact Cycle.posOf_lt hic
  obtain ⟨s₁, hA, hB⟩ := Option.bind_eq_some_iff.mp h₂
  obtain ⟨s₃, hC, hD⟩ := Option.bind_eq_some_iff.mp h₄
  obtain ⟨i₀, bd₁, hr₀, ha₁, hs₁⟩ := applyDrawTo_eq hA
  obtain ⟨k, bd₂, hrk, ha₂, hs₂⟩ := applyDrawTo_eq hB
  obtain ⟨j₀, bd₃, hr₁, ha₃, hs₃⟩ := applyDrawTo_eq hC
  obtain ⟨k', bd₄, hrk', ha₄, hs₄⟩ := applyDrawTo_eq hD
  have hi₀ : i₀ = i := Option.some.inj ((reachablePos_posOf hr₀).symm.trans hic)
  have hj₀ : j₀ = j := Option.some.inj ((reachablePos_posOf hr₁).symm.trans hjc)
  rw [hi₀] at hs₁
  rw [hj₀] at hs₃
  have hs₁s : s₁.stock = { cards := Cycle.removeIdx st.stock.cards i, cursor := i } := by
    rw [hs₁]; try rfl
  have hs₃s : s₃.stock = { cards := Cycle.removeIdx st.stock.cards j, cursor := j } := by
    rw [hs₃]; try rfl
  have hb₁ : s₁.board = bd₁ := by rw [hs₁]; try rfl
  have hb₃ : s₃.board = bd₃ := by rw [hs₃]; try rfl
  rw [hb₁] at ha₂
  rw [hb₃] at ha₄
  have hpk : s₁.stock.posOf c' = some k := reachablePos_posOf hrk
  rw [hs₁s] at hpk
  have hpk' : s₃.stock.posOf c = some k' := reachablePos_posOf hrk'
  rw [hs₃s] at hpk'
  by_cases hlt : i + 1 < len
  · -- non-wrap: j = i + 1 — both orders' second draws land on position i
    have hj1 : j = i + 1 := by rw [← hadj, Nat.mod_eq_of_lt hlt]
    have hk : k = j - 1 :=
      Option.some.inj (hpk.symm.trans (posOf_removeIdx_shift hjc (by omega)))
    have hk' : k' = i :=
      Option.some.inj (hpk'.symm.trans (posOf_removeIdx_keep hic (by omega)))
    have hbd : bd₂ = bd₄ := attach_attach_comm hbb ha₁ ha₂ ha₃ ha₄
    have hcomp₂ : st₂ = { st with
        board := bd₂,
        stock := { cards := Cycle.removeIdx (Cycle.removeIdx st.stock.cards i) k, cursor := k } } := by
      rw [hs₂, hs₁]; try rfl
    have hcomp₄ : st₄ = { st with
        board := bd₄,
        stock := { cards := Cycle.removeIdx (Cycle.removeIdx st.stock.cards j) k',
                   cursor := k' } } := by
      rw [hs₄, hs₃]; try rfl
    rw [hcomp₂, hcomp₄, hbd]
    have hcards : Cycle.removeIdx (Cycle.removeIdx st.stock.cards i) k
        = Cycle.removeIdx (Cycle.removeIdx st.stock.cards j) k' := by
      rw [show k = i from by omega, show k' = i from by omega, hj1]
      exact Cycle.removeIdx_comm st.stock.cards i i (Nat.le_refl i) (by rw [hlen]; exact hlt)
    rw [hcards, show k = k' from by omega]
  · -- wrap: i + 1 = len, j = 0
    have hlen1 : i + 1 = len := by omega
    have hj0 : j = 0 := by rw [← hadj, hlen1, Nat.mod_self]
    rcases (by omega : len = 1 ∨ len = 2 ∨ 3 ≤ len) with h1 | h2 | h3
    · -- len = 1: the successor stock is empty — the second draw dies at posOf
      have hi0' : i = 0 := by omega
      have h0 : 0 < st.stock.cards.length := by rw [hlen]; omega
      have hrlen := Cycle.removeIdx_length st.stock.cards 0 h0
      have hnil : Cycle.removeIdx st.stock.cards 0 = [] :=
        List.eq_nil_of_length_eq_zero (by omega)
      rw [hi0'] at hpk
      rw [hnil] at hpk
      have hnone : ({ cards := ([] : List Card), cursor := 0 } : Cycle Card).posOf c' = none :=
        Cycle.posOf_eq_none (by simp)
      rw [hnone] at hpk
      exact absurd hpk (by simp)
    · -- len = 2: both orders end at cursor 0 over the same (empty) splice
      have hk : k = 0 := by
        have hkeep : Cycle.posOf c' ⟨Cycle.removeIdx st.stock.cards i, i⟩ = some j :=
          posOf_removeIdx_keep hjc (by omega)
        have := Option.some.inj (hpk.symm.trans hkeep)
        omega
      have hk' : k' = 0 := by
        have hshift : Cycle.posOf c ⟨Cycle.removeIdx st.stock.cards j, j⟩ = some (i - 1) :=
          posOf_removeIdx_shift hic (by omega)
        have := Option.some.inj (hpk'.symm.trans hshift)
        omega
      have hbd : bd₂ = bd₄ := attach_attach_comm hbb ha₁ ha₂ ha₃ ha₄
      have hcomp₂ : st₂ = { st with
          board := bd₂,
          stock := { cards := Cycle.removeIdx (Cycle.removeIdx st.stock.cards i) k, cursor := k } } := by
        rw [hs₂, hs₁]; try rfl
      have hcomp₄ : st₄ = { st with
          board := bd₄,
          stock := { cards := Cycle.removeIdx (Cycle.removeIdx st.stock.cards j) k',
                     cursor := k' } } := by
        rw [hs₄, hs₃]; try rfl
      rw [hcomp₂, hcomp₄, hbd]
      have hcards : Cycle.removeIdx (Cycle.removeIdx st.stock.cards i) k
          = Cycle.removeIdx (Cycle.removeIdx st.stock.cards j) k' := by
        rw [show i = 1 from by omega, hj0, hk, hk']
        exact (Cycle.removeIdx_comm st.stock.cards 0 0 (Nat.le_refl 0) (by rw [hlen]; omega)).symm
      rw [hcards, hk, hk']
    · -- len ≥ 3: order 1's second draw needs position 0 in the mask of a
      -- saturated cursor — unreachable at step ≥ 2
      have hk0 : k = 0 := by
        have hkeep : Cycle.posOf c' ⟨Cycle.removeIdx st.stock.cards i, i⟩ = some j :=
          posOf_removeIdx_keep hjc (by omega)
        have := Option.some.inj (hpk.symm.trans hkeep)
        omega
      have hsd : s₁.drawStep = st.drawStep := by rw [hs₁]; try rfl
      have hmem := reachablePos_mask (by rw [hsd]; omega : 0 < s₁.drawStep) hrk
      rw [hs₁s] at hmem
      rw [hk0, hj0] at hmem
      have hrlen : (Cycle.removeIdx st.stock.cards i).length = i := by
        have h0 : i < st.stock.cards.length := by rw [hlen]; exact hilt
        have := Cycle.removeIdx_length st.stock.cards i h0
        omega
      exact absurd hmem (zero_notMem_maskPos (by omega : 0 < s₁.drawStep) (by omega : 2 ≤ s₁.drawStep)
        (by rw [hrlen]; omega : 2 ≤ (Cycle.removeIdx st.stock.cards i).length)
        (by rw [hrlen] : i = (Cycle.removeIdx st.stock.cards i).length))

/-- **C13's boundary**: non-adjacent Draw-commitments land on different
cursors — the end states differ (the cards agree, by `removeIdx_comm`;
only the cursor position diverges: `j - 1` vs `i`).  The engine's
sweep/canonicalization is what recovers commutation beyond adjacency —
the C-IND landscape's residual. -/
theorem drawTo_nonadjacent_diverge {st : State} {c c' : Card} {b b' : Base} {i j : Nat}
    (hij : i < j) (hne : i + 1 ≠ j)
    (hic : st.stock.posOf c = some i) (hjc : st.stock.posOf c' = some j)
    (hbb : b ≠ b') {st₂ st₄ : State}
    (h₂ : (st.applyDrawTo c b >>= fun s => s.applyDrawTo c' b') = some st₂)
    (h₄ : (st.applyDrawTo c' b' >>= fun s => s.applyDrawTo c b) = some st₄) :
    st₂ ≠ st₄ := by
  have := hbb
  obtain ⟨s₁, hA, hB⟩ := Option.bind_eq_some_iff.mp h₂
  obtain ⟨s₃, hC, hD⟩ := Option.bind_eq_some_iff.mp h₄
  obtain ⟨i₀, bd₁, hr₀, -, hs₁⟩ := applyDrawTo_eq hA
  obtain ⟨k, bd₂, hrk, -, hs₂⟩ := applyDrawTo_eq hB
  obtain ⟨j₀, bd₃, hr₁, -, hs₃⟩ := applyDrawTo_eq hC
  obtain ⟨k', bd₄, hrk', -, hs₄⟩ := applyDrawTo_eq hD
  have hi₀ : i₀ = i := Option.some.inj ((reachablePos_posOf hr₀).symm.trans hic)
  have hj₀ : j₀ = j := Option.some.inj ((reachablePos_posOf hr₁).symm.trans hjc)
  rw [hi₀] at hs₁
  rw [hj₀] at hs₃
  have hs₁s : s₁.stock = { cards := Cycle.removeIdx st.stock.cards i, cursor := i } := by
    rw [hs₁]; try rfl
  have hs₃s : s₃.stock = { cards := Cycle.removeIdx st.stock.cards j, cursor := j } := by
    rw [hs₃]; try rfl
  have hpk : s₁.stock.posOf c' = some k := reachablePos_posOf hrk
  rw [hs₁s] at hpk
  have hpk' : s₃.stock.posOf c = some k' := reachablePos_posOf hrk'
  rw [hs₃s] at hpk'
  have hk : k = j - 1 := Option.some.inj (hpk.symm.trans (posOf_removeIdx_shift hjc hij))
  have hk' : k' = i := Option.some.inj (hpk'.symm.trans (posOf_removeIdx_keep hic hij))
  have hc₂ : st₂.stock.cursor = j - 1 := by
    rw [hs₂]
    show k = j - 1
    exact hk
  have hc₄ : st₄.stock.cursor = i := by
    rw [hs₄]
    show k' = i
    exact hk'
  intro hcon
  have hcur : st₂.stock.cursor = st₄.stock.cursor := by rw [hcon]
  rw [hc₂, hc₄] at hcur
  omega

/-! ## 4. Structure — the matching is a forest

STATEMENT REPAIR (2026-09-13, prover-confirmed witness
`Temp\opencode\AboveIrreflWitness.lean`, axiom-clean): the staged
grading — everything above a card is strictly lower rank, hence
acyclicity, from `WF` alone — is FALSE.  `board_edges` admits
deal-adjacency edges, and the deal stacks arbitrarily, so a
deal-adjacency edge can invert a `canSitOn` edge between the same two
cards.  Witness: pile p1 dealt `[♥5, ♠6]` fully revealed, board
`inr ♥5 ↦ ♠6` (deal-adjacency, base visible) and `inr ♠6 ↦ ♥5`
(`canSitOn ♥5 ♠6`: 5+1=6, colors differ) — the state is WF, and
`aboveOf ♥5 = [♥5, ♠6]` contains `♥5`.  Longer alternating cycles
(deal-adjacency and canSitOn edges alternating across two piles, e.g.
`♥5 ↦ ♦9 ↦ ♣8 ↦ ♠6 ↦ ♥5` with the first and third edges deal-adjacent)
defeat every per-edge or global-deal-order repair: the acyclicity is
genuinely historical (which edge was attached last), not a state-only
consequence of the edge predicates.

The defensible acyclicity — the original design intent — is the
*forest potential*: a strictly decreasing measure along the matching's
card-edges.  Every play from `State.initial` maintains one (the deal's
own chains grade by within-pile position; every attach renumbers the
moved tree below its new base — the self-landing guard makes the trees
disjoint; reveal shifts the boundary into the gap) — that
play-induction is a later wave's item; here the potential is the
hypothesis, and the grading + acyclicity follow from it.
-/

/-- The forest potential: `φ` strictly decreases along every
card-to-card edge of the matching (`topOf (inr c) = some y` — `y` sits
on `c`).  The state-only shadow of play-reachability: WF alone does
not imply it (see the section note); every state reachable from
`State.initial` admits one. -/
def State.board_forest (st : State) : Prop :=
  ∃ φ : Card → Nat, ∀ c y, st.board.topOf (Sum.inr c) = some y → φ y < φ c

/-- The grading, rescoped: along the run above `c`, every card is
strictly below `c` in the forest potential (the staged rank-form is
false — deals stack arbitrarily; see the section note). -/
theorem aboveOf_rank_grading {st : State} (hwf : st.WF) {φ : Card → Nat}
    (hφ : ∀ c y, st.board.topOf (Sum.inr c) = some y → φ y < φ c) (c : Card) :
    ∀ d ∈ st.board.aboveOf c, φ d < φ c := by
  have := hwf
  have main : ∀ (fuel : Nat) (x : Card) (acc : List Card),
      (∀ z ∈ acc, φ z < φ c) → (φ x < φ c ∨ x = c) →
        ∀ d ∈ Board.aboveOf.go st.board fuel (Sum.inr x) acc, φ d < φ c := by
    intro fuel
    induction fuel with
    | zero =>
        intro x acc hacc _ d hd
        have hd' : d ∈ acc := hd
        exact hacc d hd'
    | succ f ih =>
        intro x acc hacc hx d hd
        rw [aboveOf_go_succ] at hd
        cases ht : st.board.topOf (Sum.inr x) with
        | none =>
            rw [ht] at hd
            have hd' : d ∈ acc := hd
            exact hacc d hd'
        | some y =>
            rw [ht] at hd
            have hd' : d ∈ (if acc.contains y then acc
                else Board.aboveOf.go st.board f (Sum.inr y) (y :: acc)) := hd
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

/-- Acyclicity, from the grading: no card is above itself when the
matching admits a forest potential. -/
theorem aboveOf_irrefl {st : State} (hwf : st.WF) (hfor : st.board_forest) (c : Card) :
    c ∉ st.board.aboveOf c := by
  obtain ⟨φ, hφ⟩ := hfor
  have hgr := aboveOf_rank_grading hwf hφ c
  intro hmem
  exact absurd (hgr c hmem) (Nat.lt_irrefl _)

/-! ## 5. The deck integration — the jump IS the physical game

The Draw commitments (`applyDrawTo`, `applyDrawStackTo`) are the
derived jumps; these are the statements that the guard makes them
exactly the physical game: jump-then-play ≡ deal-until-then-play.
C9's premise, as theorems, at every draw step (at step 1 the guard is
trivial — `reachablePos_step1`).  The bridge to `toEngine_simulates`
consumes these. -/

/-! ### The deal-iteration kit — the jump-soundness machinery

`Cycle.dealIter` is `k` deals (Macro.lean's `Cycle.dealN` restated —
this file cannot import Macro), with the orbit correspondence: → every
accessible position is dealt to (`dealReach_maskPos`), ← every cursor
the chain reaches lands in the original mask (`dealIter_orbit` +
`dealIter_mask`), which with `stock_wf`'s duplicate-freeness pins the
position. -/

/-- `k` deals from `cy`. -/
def Cycle.dealIter (s : Nat) : Nat → Cycle Card → Cycle Card
  | 0, cy => cy
  | k + 1, cy => dealOnce s (dealIter s k cy)

theorem Cycle.dealIter_zero (s : Nat) (cy : Cycle Card) : dealIter s 0 cy = cy := rfl

theorem Cycle.dealIter_succ (s : Nat) (k : Nat) (cy : Cycle Card) :
    dealIter s (k + 1) cy = dealOnce s (dealIter s k cy) := rfl

theorem Cycle.dealIter_one (s : Nat) (cy : Cycle Card) :
    dealIter s 1 cy = dealOnce s cy := rfl

theorem Cycle.dealIter_add (s : Nat) : ∀ (k j : Nat) (cy : Cycle Card),
    dealIter s (k + j) cy = dealIter s k (dealIter s j cy) := by
  intro k
  induction k with
  | zero => intro j cy; rw [Nat.zero_add, dealIter_zero]
  | succ k ih =>
    intro j cy
    rw [Nat.succ_add, dealIter_succ, dealIter_succ, ih]

theorem Cycle.dealIter_shift (s : Nat) : ∀ (k : Nat) (cy : Cycle Card),
    dealIter s k (dealOnce s cy) = dealOnce s (dealIter s k cy) := by
  intro k
  induction k with
  | zero => intro cy; rfl
  | succ k ih => intro cy; rw [dealIter_succ, ih, ← dealIter_succ]

theorem Cycle.dealIter_cards (s : Nat) : ∀ (k : Nat) (cy : Cycle Card),
    (dealIter s k cy).cards = cy.cards := by
  intro k
  induction k with
  | zero => intro cy; rfl
  | succ k ih => intro cy; rw [dealIter_succ, Cycle.dealOnce_cards, ih]

theorem dealIter_cards' (s : Nat) (k : Nat) (l : List Card) (c₀ : Nat) :
    (Cycle.dealIter s k ⟨l, c₀⟩).cards = l :=
  Cycle.dealIter_cards s k ⟨l, c₀⟩

theorem jump_mul_mod (k s : Nat) : k * s % s = 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.succ_mul, Nat.add_mod, ih, Nat.mod_self, Nat.zero_add, Nat.zero_mod]

theorem jump_mul_sub_mod (k s : Nat) : (k * s - s) % s = 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h1 : (k + 1) * s = k * s + s := by rw [Nat.add_mul, Nat.one_mul]
    rw [h1, Nat.add_sub_cancel]
    exact jump_mul_mod k s

theorem jump_exists_mul {a s : Nat} (hmod : a % s = 0) : ∃ q, a = q * s := by
  refine ⟨a / s, ?_⟩
  have hdiv := Nat.div_add_mod a s
  rw [hmod, Nat.add_zero] at hdiv
  rw [Nat.mul_comm]
  exact hdiv.symm

theorem le_mul_self {j s : Nat} (hj : 1 ≤ j) : s ≤ j * s := by
  have h1 : j - 1 + 1 = j := by omega
  rw [← h1, Nat.add_mul, Nat.one_mul]
  exact Nat.le_add_left s ((j - 1) * s)

/-- One deal from the pass end (or past it) wraps to 0. -/
theorem dealOnce_wrap (s : Nat) (l : List Card) (κ : Nat) (hκ : κ ≥ l.length) :
    (Cycle.dealOnce s ⟨l, κ⟩).cursor = 0 := by
  show (if κ ≥ l.length then (⟨l, 0⟩ : Cycle Card)
      else ⟨l, min (κ + s) l.length⟩).cursor = 0
  rw [if_pos hκ]

/-- One deal below the pass end clamps at `min (κ + s)`. -/
theorem dealOnce_step (s : Nat) (l : List Card) (κ : Nat) (hκ : ¬(κ ≥ l.length)) :
    (Cycle.dealOnce s ⟨l, κ⟩).cursor = min (κ + s) l.length := by
  show (if κ ≥ l.length then (⟨l, 0⟩ : Cycle Card)
      else ⟨l, min (κ + s) l.length⟩).cursor = min (κ + s) l.length
  rw [if_neg hκ]

theorem dealIter_cursor_le (s : Nat) : ∀ (k : Nat) (cy : Cycle Card),
    cy.cursor ≤ cy.cards.length → (Cycle.dealIter s k cy).cursor ≤ cy.cards.length := by
  intro k
  induction k with
  | zero => intro cy h; exact h
  | succ f ih =>
    intro cy h
    by_cases hguard : (Cycle.dealIter s f cy).cursor ≥ (Cycle.dealIter s f cy).cards.length
    · rw [Cycle.dealIter_succ, dealOnce_wrap s _ _ hguard]
      exact Nat.zero_le _
    · rw [Cycle.dealIter_succ, dealOnce_step s _ _ hguard, Cycle.dealIter_cards]
      exact Nat.min_le_right _ _

/-- The orbit form: every cursor the deal chain reaches is either on
the first pass from `c₀` (`c₀ + m·s`, clamped at the length) or on a
fresh pass (`j·s`, clamped). -/
theorem dealIter_orbit (s : Nat) : ∀ (k : Nat) (l : List Card) (c₀ : Nat),
    c₀ ≤ l.length →
    (∃ m, (Cycle.dealIter s k ⟨l, c₀⟩).cursor = min (c₀ + m * s) l.length)
      ∨ (∃ j, (Cycle.dealIter s k ⟨l, c₀⟩).cursor = min (j * s) l.length) := by
  intro k
  induction k with
  | zero =>
    intro l c₀ hle
    refine Or.inl ⟨0, ?_⟩
    rw [Cycle.dealIter_zero, Nat.zero_mul, Nat.add_zero, Nat.min_eq_left hle]
  | succ f ih =>
    intro l c₀ hle
    obtain hc | hc := ih l c₀ hle
    · obtain ⟨m, hm⟩ := hc
      by_cases hsat : l.length ≤ c₀ + m * s
      · refine Or.inr ⟨0, ?_⟩
        have hκn : (Cycle.dealIter s f ⟨l, c₀⟩).cursor = l.length := by
          rw [hm, Nat.min_eq_right hsat]
        have hguard : (Cycle.dealIter s f ⟨l, c₀⟩).cursor
            ≥ (Cycle.dealIter s f ⟨l, c₀⟩).cards.length := by
          rw [hκn, dealIter_cards']
          omega
        rw [Cycle.dealIter_succ, Nat.zero_mul, Nat.min_eq_left (Nat.zero_le l.length),
          dealOnce_wrap s _ _ hguard]
      · refine Or.inl ⟨m + 1, ?_⟩
        have hκc : (Cycle.dealIter s f ⟨l, c₀⟩).cursor = c₀ + m * s := by
          rw [hm, Nat.min_eq_left (by omega)]
        have hguard : ¬((Cycle.dealIter s f ⟨l, c₀⟩).cursor
            ≥ (Cycle.dealIter s f ⟨l, c₀⟩).cards.length) := by
          rw [hκc, dealIter_cards']
          omega
        have hexp : c₀ + (m + 1) * s = c₀ + m * s + s := by
          rw [Nat.add_mul, Nat.one_mul]; omega
        rw [Cycle.dealIter_succ, dealOnce_step s _ _ hguard, hκc, dealIter_cards', hexp]
    · obtain ⟨j, hj⟩ := hc
      by_cases hsat : l.length ≤ j * s
      · refine Or.inr ⟨0, ?_⟩
        have hκn : (Cycle.dealIter s f ⟨l, c₀⟩).cursor = l.length := by
          rw [hj, Nat.min_eq_right hsat]
        have hguard : (Cycle.dealIter s f ⟨l, c₀⟩).cursor
            ≥ (Cycle.dealIter s f ⟨l, c₀⟩).cards.length := by
          rw [hκn, dealIter_cards']
          omega
        rw [Cycle.dealIter_succ, Nat.zero_mul, Nat.min_eq_left (Nat.zero_le l.length),
          dealOnce_wrap s _ _ hguard]
      · refine Or.inr ⟨j + 1, ?_⟩
        have hκc : (Cycle.dealIter s f ⟨l, c₀⟩).cursor = j * s := by
          rw [hj, Nat.min_eq_left (by omega)]
        have hguard : ¬((Cycle.dealIter s f ⟨l, c₀⟩).cursor
            ≥ (Cycle.dealIter s f ⟨l, c₀⟩).cards.length) := by
          rw [hκc, dealIter_cards']
          omega
        have hexp : (j + 1) * s = j * s + s := by rw [Nat.add_mul, Nat.one_mul]
        rw [Cycle.dealIter_succ, dealOnce_step s _ _ hguard, hκc, dealIter_cards', hexp]

/-- The current-pass advance: `q` deals from `c` land exactly at
`c + q·s` within the length (no clamp, no wrap). -/
theorem dealChain_add {s : Nat} (hs : 0 < s) (l : List Card) :
    ∀ (q c : Nat), c + q * s ≤ l.length →
      Cycle.dealIter s q ⟨l, c⟩ = ⟨l, c + q * s⟩ := by
  intro q
  induction q with
  | zero => intro c _; rw [Nat.zero_mul, Nat.add_zero]; rfl
  | succ q ih =>
    intro c hle
    have hexp : (q + 1) * s = q * s + s := by rw [Nat.add_mul, Nat.one_mul]
    rw [hexp] at hle
    have hstep : Cycle.dealOnce s ⟨l, c⟩ = ⟨l, c + s⟩ := by
      show (if c ≥ l.length then (⟨l, 0⟩ : Cycle Card) else ⟨l, min (c + s) l.length⟩)
          = (⟨l, c + s⟩ : Cycle Card)
      rw [if_neg (by omega), Nat.min_eq_left (by omega)]
    rw [Cycle.dealIter_succ, ← Cycle.dealIter_shift, hstep, ih (c + s) (by omega), hexp]
    exact congrArg (Cycle.mk l) (by omega)

/-- Every cursor reaches the pass end: the chain of clamped deals. -/
theorem dealChain_to_end {s : Nat} (hs : 0 < s) (l : List Card) :
    ∀ (d c : Nat), c ≤ l.length → l.length - c ≤ d →
      ∃ k, Cycle.dealIter s k ⟨l, c⟩ = ⟨l, l.length⟩ := by
  intro d
  induction d with
  | zero =>
    intro c _ hd
    have hc : c = l.length := by omega
    subst hc
    exact ⟨0, rfl⟩
  | succ d ih =>
    intro c _ hd
    by_cases hc : c = l.length
    · subst hc; exact ⟨0, rfl⟩
    · by_cases hcs : c + s < l.length
      · have hstep : Cycle.dealOnce s ⟨l, c⟩ = ⟨l, c + s⟩ := by
          show (if c ≥ l.length then (⟨l, 0⟩ : Cycle Card) else ⟨l, min (c + s) l.length⟩)
              = (⟨l, c + s⟩ : Cycle Card)
          rw [if_neg (by omega), Nat.min_eq_left (by omega)]
        obtain ⟨k, hk⟩ := ih (c + s) (by omega) (by omega)
        refine ⟨k + 1, ?_⟩
        rw [Cycle.dealIter_succ, ← Cycle.dealIter_shift, hstep]
        exact hk
      · have hstep : Cycle.dealOnce s ⟨l, c⟩ = ⟨l, l.length⟩ := by
          show (if c ≥ l.length then (⟨l, 0⟩ : Cycle Card) else ⟨l, min (c + s) l.length⟩)
              = (⟨l, l.length⟩ : Cycle Card)
          rw [if_neg (by omega), Nat.min_eq_right (by omega)]
        exact ⟨1, hstep⟩

/-- The pass end is reached from any cursor, even past it (one wrap). -/
theorem dealChain_to_end_any {s : Nat} (hs : 0 < s) (l : List Card) (c : Nat) :
    ∃ k, Cycle.dealIter s k ⟨l, c⟩ = ⟨l, l.length⟩ := by
  by_cases hcl : c ≤ l.length
  · exact dealChain_to_end hs l (l.length - c) c hcl (by omega)
  · have hwrap : Cycle.dealOnce s ⟨l, c⟩ = ⟨l, 0⟩ := by
      show (if c ≥ l.length then (⟨l, 0⟩ : Cycle Card) else ⟨l, min (c + s) l.length⟩)
          = (⟨l, 0⟩ : Cycle Card)
      rw [if_pos (by omega : c ≥ l.length)]
    obtain ⟨k₀, hk₀⟩ := dealChain_to_end hs l l.length 0 (Nat.zero_le _) (by omega)
    refine ⟨k₀ + 1, ?_⟩
    rw [Cycle.dealIter_succ, ← Cycle.dealIter_shift, hwrap, hk₀]

/-- The wrapped advance: reach the pass end, wrap to 0, then climb to
`i + 1` on the batch-top lane. -/
theorem dealChain_wrap {s : Nat} (hs : 0 < s) (l : List Card) (c i : Nat)
    (hlt : i < l.length) (hle : s - 1 ≤ i) (hmod : (i - (s - 1)) % s = 0) :
    ∃ k, Cycle.dealIter s k ⟨l, c⟩ = ⟨l, i + 1⟩ := by
  obtain ⟨k₀, hk₀⟩ := dealChain_to_end_any hs l c
  have hwrap : Cycle.dealOnce s ⟨l, l.length⟩ = ⟨l, 0⟩ := by
    show (if l.length ≥ l.length then (⟨l, 0⟩ : Cycle Card)
        else ⟨l, min (l.length + s) l.length⟩) = (⟨l, 0⟩ : Cycle Card)
    rw [if_pos (Nat.le_refl l.length)]
  obtain ⟨q, hq⟩ := jump_exists_mul hmod
  have hexp : (q + 1) * s = q * s + s := by rw [Nat.add_mul, Nat.one_mul]
  have hadv : 0 + (q + 1) * s ≤ l.length := by rw [hexp]; omega
  have hlast : 0 + (q + 1) * s = i + 1 := by rw [hexp]; omega
  refine ⟨(q + 1) + (1 + k₀), ?_⟩
  have hcomp1 : Cycle.dealIter s (1 + k₀) ⟨l, c⟩
      = Cycle.dealOnce s (Cycle.dealIter s k₀ ⟨l, c⟩) := by
    rw [Cycle.dealIter_add, Cycle.dealIter_one]
  have hcomp2 : Cycle.dealIter s ((q + 1) + (1 + k₀)) ⟨l, c⟩
      = Cycle.dealIter s (q + 1) (Cycle.dealOnce s (Cycle.dealIter s k₀ ⟨l, c⟩)) := by
    rw [Cycle.dealIter_add, hcomp1]
  rw [hcomp2, hk₀, hwrap, dealChain_add hs l (q + 1) 0 hadv, hlast]

/-- The deal-orbit correspondence, witness half: every accessible
position is dealt to — `dealIter` realizes the jump. -/
theorem dealReach_maskPos {s : Nat} (hs : 0 < s) {cy : Cycle Card} {i : Nat}
    (hlt : i < cy.cards.length) (hmem : i ∈ Pace.maskPos cy s hs) :
    ∃ k, Cycle.dealIter s k cy = { cy with cursor := i + 1 } := by
  rcases cy with ⟨l, c⟩
  show ∃ k, Cycle.dealIter s k ⟨l, c⟩ = ⟨l, i + 1⟩
  have hlt : i < l.length := hlt
  simp only [Pace.maskPos] at hmem
  rcases List.mem_append.mp hmem with h12 | h3
  · rcases List.mem_append.mp h12 with h1 | h2
    · obtain ⟨hle, hlt2, hmod⟩ := (Pace.laneUp_mem s hs _ _ i).mp h1
      by_cases hc0 : c = 0
      · subst hc0
        rw [if_pos rfl] at hle hmod
        exact dealChain_wrap hs l 0 i hlt hle hmod
      · rw [if_neg hc0] at hle hmod
        obtain ⟨q, hq⟩ := jump_exists_mul hmod
        have hle2 : c + q * s ≤ l.length := by omega
        have hkey : c + q * s = i + 1 := by omega
        refine ⟨q, ?_⟩
        rw [dealChain_add hs l q c hle2]
        exact congrArg (Cycle.mk l) hkey
    · rw [if_pos (by omega : 0 < l.length)] at h2
      simp only [List.mem_singleton] at h2
      obtain ⟨k, hk⟩ := dealChain_to_end_any hs l c
      refine ⟨k, ?_⟩
      rw [hk]
      exact congrArg (Cycle.mk l) (by omega)
  · obtain ⟨hle, -, hmod⟩ := (Pace.laneUp_mem s hs _ _ i).mp h3
    exact dealChain_wrap hs l c i hlt hle hmod

/-- `maskPos`, lane 1: the leading lane from the cursor's waste top. -/
theorem maskPos_lane1_mem {α : Type} {l : List α} {c₀ s : Nat} (hs : 0 < s) {p : Nat}
    (hle : (if c₀ = 0 then s - 1 else c₀ - 1) ≤ p)
    (hlt : p < l.length - 1)
    (hmod : (p - (if c₀ = 0 then s - 1 else c₀ - 1)) % s = 0) :
    p ∈ Pace.maskPos ⟨l, c₀⟩ s hs := by
  have h : p ∈ Pace.laneUp s hs (if c₀ = 0 then s - 1 else c₀ - 1) (l.length - 1) :=
    (Pace.laneUp_mem s hs _ _ p).mpr ⟨hle, hlt, hmod⟩
  show p ∈ (Pace.laneUp s hs _ (l.length - 1)
    ++ (if 0 < l.length then [l.length - 1] else [])
    ++ Pace.laneUp s hs (s - 1)
        ((if c₀ % s != 0 then l.length else c₀) - 1))
  simp only [List.mem_append]
  exact Or.inl (Or.inl h)

/-- `maskPos`, lane 2: the batch-top lane below the wrap end. -/
theorem maskPos_lane2_mem {α : Type} {l : List α} {c₀ s : Nat} (hs : 0 < s) {p : Nat}
    (hle : s - 1 ≤ p)
    (hlt : p < (if c₀ % s != 0 then l.length else c₀) - 1)
    (hmod : (p - (s - 1)) % s = 0) :
    p ∈ Pace.maskPos ⟨l, c₀⟩ s hs := by
  have h : p ∈ Pace.laneUp s hs (s - 1) ((if c₀ % s != 0 then l.length else c₀) - 1) :=
    (Pace.laneUp_mem s hs _ _ p).mpr ⟨hle, hlt, hmod⟩
  show p ∈ (Pace.laneUp s hs _ (l.length - 1)
    ++ (if 0 < l.length then [l.length - 1] else [])
    ++ Pace.laneUp s hs (s - 1)
        ((if c₀ % s != 0 then l.length else c₀) - 1))
  simp only [List.mem_append]
  exact Or.inr h

/-- `maskPos`, the last card (the pass-end saturation). -/
theorem maskPos_last_mem {α : Type} {l : List α} {c₀ s : Nat} (hs : 0 < s)
    (hn : 0 < l.length) : l.length - 1 ∈ Pace.maskPos ⟨l, c₀⟩ s hs := by
  show l.length - 1 ∈ (Pace.laneUp s hs _ (l.length - 1)
    ++ (if 0 < l.length then [l.length - 1] else [])
    ++ Pace.laneUp s hs (s - 1) _)
  rw [if_pos hn]
  simp only [List.mem_append]
  exact Or.inl (Or.inr (List.mem_singleton.mpr rfl))

/-- The orbit lands in the mask: every cursor the deal chain reaches
(other than a fresh 0) exposes, at `κ - 1`, a position of the
*original* cycle's accessible set. -/
theorem dealIter_mask {s : Nat} (hs : 0 < s) {l : List Card} {c₀ κ : Nat}
    (hcur : c₀ ≤ l.length) (hκ : κ ≤ l.length) (h0 : κ ≠ 0)
    (hform : (∃ m, κ = min (c₀ + m * s) l.length) ∨ (∃ j, κ = min (j * s) l.length)) :
    κ - 1 ∈ Pace.maskPos ⟨l, c₀⟩ s hs := by
  have := hκ
  have := hcur
  rcases hform with ⟨m, hm⟩ | ⟨j, hj⟩
  · by_cases hsat : l.length ≤ c₀ + m * s
    · have hκn : κ = l.length := by rw [hm, Nat.min_eq_right hsat]
      rw [hκn]
      exact maskPos_last_mem hs (by omega)
    · rw [hm, Nat.min_eq_left (by omega)]
      rcases Nat.eq_zero_or_pos m with rfl | hm0
      · have hc0 : c₀ ≠ 0 := by omega
        refine maskPos_lane1_mem hs ?_ ?_ ?_
        · rw [if_neg hc0]; omega
        · omega
        · rw [if_neg hc0]
          rw [show c₀ + 0 * s - 1 - (c₀ - 1) = 0 from by omega, Nat.zero_mod]
      · have hsle : s ≤ m * s := le_mul_self (by omega)
        by_cases hc0 : c₀ = 0
        · subst hc0
          refine maskPos_lane1_mem hs ?_ ?_ ?_
          · rw [if_pos rfl]
            omega
          · omega
          · rw [if_pos rfl]
            have hsub : 0 + m * s - 1 - (s - 1) = m * s - s := by omega
            rw [hsub]
            exact jump_mul_sub_mod m s
        · refine maskPos_lane1_mem hs ?_ ?_ ?_
          · rw [if_neg hc0]; omega
          · omega
          · rw [if_neg hc0]
            have hsub : c₀ + m * s - 1 - (c₀ - 1) = m * s := by omega
            rw [hsub]
            exact jump_mul_mod m s
  · rcases Nat.eq_zero_or_pos j with rfl | hj0
    · have hκ0 : κ = 0 := by
        rw [hj, Nat.zero_mul, Nat.min_eq_left (Nat.zero_le l.length)]
      exact absurd hκ0 h0
    · have hsle : s ≤ j * s := le_mul_self (by omega)
      by_cases hsat : l.length ≤ j * s
      · have hκn : κ = l.length := by rw [hj, Nat.min_eq_right hsat]
        rw [hκn]
        exact maskPos_last_mem hs (by omega)
      · rw [hj, Nat.min_eq_left (by omega)]
        rcases Nat.eq_zero_or_pos (c₀ % s) with hmod0 | hpos
        · have hne : ¬((c₀ % s != 0) = true) := by
            rw [hmod0]
            simp
          by_cases hbelow : j * s - 1 < c₀ - 1
          · refine maskPos_lane2_mem hs ?_ ?_ ?_
            · show s - 1 ≤ j * s - 1
              omega
            · rw [if_neg hne]; omega
            · have hsub : j * s - 1 - (s - 1) = j * s - s := by omega
              rw [hsub]
              exact jump_mul_sub_mod j s
          · by_cases hc0 : c₀ = 0
            · subst hc0
              refine maskPos_lane1_mem hs ?_ ?_ ?_
              · rw [if_pos rfl]
                omega
              · omega
              · rw [if_pos rfl]
                have hsub : j * s - 1 - (s - 1) = j * s - s := by omega
                rw [hsub]
                exact jump_mul_sub_mod j s
            · obtain ⟨q, hq⟩ := jump_exists_mul hmod0
              refine maskPos_lane1_mem hs ?_ ?_ ?_
              · rw [if_neg hc0]; omega
              · omega
              · rw [if_neg hc0]
                have hsub : j * s - 1 - (c₀ - 1) = j * s - c₀ := by omega
                rw [hsub, hq, ← Nat.sub_mul]
                exact jump_mul_mod (j - q) s
        · have hres : (c₀ % s != 0) = true := by simp [Nat.ne_of_gt hpos]
          refine maskPos_lane2_mem hs ?_ ?_ ?_
          · show s - 1 ≤ j * s - 1
            omega
          · rw [if_pos hres]; omega
          · have hsub : j * s - 1 - (s - 1) = j * s - s := by omega
            rw [hsub]
            exact jump_mul_sub_mod j s

/-- A found position points at the card. -/
theorem posOf_get {c : Card} : ∀ (l : List Card) (cur i : Nat),
    Cycle.posOf c ⟨l, cur⟩ = some i → l[i]? = some c := by
  intro l
  induction l with
  | nil => intro cur i h; simp [Cycle.posOf, Cycle.findFirstIdx] at h
  | cons a t ih =>
    intro cur i h
    simp only [Cycle.posOf, Cycle.findFirstIdx] at h
    by_cases ha : a = c
    · rw [if_pos (decide_eq_true ha), Option.some.injEq] at h
      subst h
      rw [ha]
      rfl
    · rw [if_neg (fun hcon => ha (of_decide_eq_true hcon))] at h
      cases hf : Cycle.findFirstIdx (fun c' => decide (c' = c)) t with
      | none => rw [hf] at h; simp at h
      | some j =>
        rw [hf, Option.map_some, Option.some.injEq] at h
        subst h
        rw [List.getElem?_cons_succ]
        exact ih 0 j hf

/-- Running a pure-deal play lands on the iterated deal. -/
theorem run_dealIter : ∀ (k : Nat) (st : State),
    st.run (List.replicate k Move.draw) =
      some { st with stock := Cycle.dealIter st.drawStep k st.stock } := by
  intro k
  induction k with
  | zero => intro st; rfl
  | succ f ih =>
    intro st
    rw [List.replicate_succ, State.run,
      show st.apply Move.draw =
        some { st with stock := Cycle.dealOnce st.drawStep st.stock } from rfl]
    show ({ st with stock := Cycle.dealOnce st.drawStep st.stock } : State).run
        (List.replicate f Move.draw) = _
    rw [ih { st with stock := Cycle.dealOnce st.drawStep st.stock }]
    show some { st with stock := Cycle.dealIter st.drawStep f (Cycle.dealOnce st.drawStep st.stock) }
       = some { st with stock := Cycle.dealIter st.drawStep (f + 1) st.stock }
    rw [Cycle.dealIter_shift, Cycle.dealIter_succ]

/-- A full pass plus the wrap deal returns to the pass start: from
cursor 0, dealing everything (the clamp passes the last card) and
wrapping lands home — the deal cycle's period is `⌈n/s⌉ + 1`, at any
step `s ≥ 1` (deck.rs `offset`'s periodicity).  Supersedes the old
rotate-form "a full rotation is the identity", an artifact of the
jump semantics.

Route: `run_dealIter` unpacks the play; `q = (n+s-1)/s` is exactly
`⌈n/s⌉` (`q·s ≥ n` and `d·s ≥ n → d ≥ q`, both from
`Nat.div_add_mod` + `Nat.mod_lt`), so `d ≤ q` deals from cursor 0 stay
on the first pass at `min (d·s, n)` (the induction's step needs
`d·s < n`, i.e. minimality), the `q`-th deal clamps at `n`, and the
wrap deal returns to `0` — the stock, and with it the state, is
unchanged. -/
theorem draw_full_pass {st : State} (hc : st.stock.cursor = 0)
    (hs : 0 < st.drawStep) {st' : State}
    (h : st.run (List.replicate
        ((st.stock.cards.length + st.drawStep - 1) / st.drawStep + 1) Move.draw)
      = some st') :
    st' = st := by
  obtain ⟨K, hK⟩ : ∃ K, (st.stock.cards.length + st.drawStep - 1) / st.drawStep + 1 = K :=
    ⟨_, rfl⟩
  rw [hK] at h
  rw [run_dealIter] at h
  have hst' : { st with stock := Cycle.dealIter st.drawStep K st.stock } = st' :=
    Option.some.inj h
  rw [← hst']
  refine state_ext rfl rfl rfl rfl ?_ rfl
  cases hst : st.stock with
  | mk l c =>
    rw [hst] at hc hK
    have hc' : c = 0 := hc
    subst hc'
    have hK' : (l.length + st.drawStep - 1) / st.drawStep + 1 = K := hK
    obtain ⟨q, hqdef⟩ : ∃ q, (l.length + st.drawStep - 1) / st.drawStep = q := ⟨_, rfl⟩
    have hKq : K = q + 1 := by rw [← hK', hqdef]
    rw [hKq]
    have hdm := Nat.div_add_mod (l.length + st.drawStep - 1) st.drawStep
    rw [Nat.mul_comm, hqdef] at hdm
    have hmlt := Nat.mod_lt (l.length + st.drawStep - 1) hs
    have hqge : l.length ≤ q * st.drawStep := by omega
    have hqmin : ∀ d : Nat, l.length ≤ d * st.drawStep → q ≤ d := by
      intro d hd
      rcases Nat.lt_or_ge d q with hlt | hge
      · exfalso
        have hmono : (d + 1) * st.drawStep ≤ q * st.drawStep :=
          Nat.mul_le_mul (by omega) (Nat.le_refl _)
        have hexp : (d + 1) * st.drawStep = d * st.drawStep + st.drawStep := by
          rw [Nat.add_mul, Nat.one_mul]
        omega
      · exact hge
    have main : ∀ d : Nat, d ≤ q →
        Cycle.dealIter st.drawStep d ⟨l, 0⟩ = ⟨l, min (d * st.drawStep) l.length⟩ := by
      intro d
      induction d with
      | zero =>
          intro _
          show (⟨l, 0⟩ : Cycle Card) = ⟨l, min (0 * st.drawStep) l.length⟩
          rw [Nat.zero_mul, Nat.min_eq_left (Nat.zero_le _)]
      | succ d ih =>
          intro hd
          have hdlt : d * st.drawStep < l.length := by
            by_cases hbig : l.length ≤ d * st.drawStep
            · exact absurd (hqmin d hbig) (by omega)
            · omega
          rw [Cycle.dealIter_succ, ih (by omega)]
          rw [Nat.min_eq_left (by omega : d * st.drawStep ≤ l.length)]
          show (if d * st.drawStep ≥ l.length then (⟨l, 0⟩ : Cycle Card)
              else ⟨l, min (d * st.drawStep + st.drawStep) l.length⟩)
            = ⟨l, min ((d + 1) * st.drawStep) l.length⟩
          rw [if_neg (by omega : ¬ (d * st.drawStep ≥ l.length)), Nat.add_mul, Nat.one_mul]
    have hpass : Cycle.dealIter st.drawStep q ⟨l, 0⟩ = ⟨l, l.length⟩ := by
      rw [main q (Nat.le_refl q), Nat.min_eq_right hqge]
    rw [Cycle.dealIter_succ, hpass]
    show (if l.length ≥ l.length then (⟨l, 0⟩ : Cycle Card)
        else ⟨l, min (l.length + st.drawStep) l.length⟩) = ⟨l, 0⟩
    rw [if_pos (Nat.le_refl l.length)]

/-- `reachablePos`, introduction form. -/
theorem reachablePos_intro {st : State} {c : Card} {i : Nat} (hs : 0 < st.drawStep)
    (hpos : st.stock.posOf c = some i) (hmem : i ∈ Pace.maskPos st.stock st.drawStep hs) :
    st.reachablePos c = some i := by
  simp only [State.reachablePos, dif_pos hs, hpos, if_pos hmem]

/-- The tableau deck move after the deals brought `c` to the top. -/
theorem deckPile_after_deals {st : State} {c : Card} {b : Base} {i : Nat} {bd : Board}
    (hget : st.stock.cards[i]? = some c) (hcan : st.canPlace c b = true)
    (hatt : st.board.attach b c = some bd) :
    ({ st with stock := { st.stock with cursor := i + 1 } }).apply (Move.deckPile c b)
      = some { st with board := bd, stock := (st.stock.drawTo i).removeAt i } := by
  have hprev : ({ st with stock := { st.stock with cursor := i + 1 } } : State).stock.prev
      = some c := by
    show (Cycle.prev { st.stock with cursor := i + 1 }) = some c
    show (if i + 1 = 0 then none else st.stock.cards[i + 1 - 1]?) = some c
    rw [if_neg (by omega : ¬ (i + 1 = 0))]
    have hi : i + 1 - 1 = i := by omega
    rw [hi]
    exact hget
  have e1 : (({ st with stock := { st.stock with cursor := i + 1 } } : State).stock.cursor - 1)
      = i := by
    show i + 1 - 1 = i
    omega
  have e2 : ({ st with stock := { st.stock with cursor := i + 1 } } : State).stock
      = { st.stock with cursor := i + 1 } := rfl
  have e3 : st.stock.drawTo i = { st.stock with cursor := i + 1 } := rfl
  refine (apply_deckPile_iff).mpr ⟨hprev, hcan, bd, hatt, ?_⟩
  rw [e1, e2, e3]

/-- The stack deck move after the deals. -/
theorem deckStack_after_deals {st : State} {c : Card} {i : Nat}
    (hget : st.stock.cards[i]? = some c) (hrank : c.rank.toIdx = st.heights c.suit) :
    ({ st with stock := { st.stock with cursor := i + 1 } }).apply (Move.deckStack c)
      = some { st with
        stock := (st.stock.drawTo i).removeAt i,
        heights := fun s => if s = c.suit then st.heights s + 1 else st.heights s } := by
  have hprev : ({ st with stock := { st.stock with cursor := i + 1 } } : State).stock.prev
      = some c := by
    show (Cycle.prev { st.stock with cursor := i + 1 }) = some c
    show (if i + 1 = 0 then none else st.stock.cards[i + 1 - 1]?) = some c
    rw [if_neg (by omega : ¬ (i + 1 = 0))]
    have hi : i + 1 - 1 = i := by omega
    rw [hi]
    exact hget
  have e1 : (({ st with stock := { st.stock with cursor := i + 1 } } : State).stock.cursor - 1)
      = i := by
    show i + 1 - 1 = i
    omega
  have e2 : ({ st with stock := { st.stock with cursor := i + 1 } } : State).stock
      = { st.stock with cursor := i + 1 } := rfl
  have e3 : st.stock.drawTo i = { st.stock with cursor := i + 1 } := rfl
  refine (apply_deckStack_iff).mpr ⟨hprev, hrank, ?_⟩
  show { st with
    stock := (st.stock.drawTo i).removeAt i,
    heights := fun s => if s = c.suit then st.heights s + 1 else st.heights s }
     = { st with
    stock := (({ st with stock := { st.stock with cursor := i + 1 } } : State).stock).removeAt
        ((({ st with stock := { st.stock with cursor := i + 1 } } : State).stock.cursor - 1)),
    heights := fun s => if s = c.suit
      then ({ st with stock := { st.stock with cursor := i + 1 } } : State).heights s + 1
      else ({ st with stock := { st.stock with cursor := i + 1 } } : State).heights s }
  rw [e1, e2, e3]

/-- `applyDrawStackTo`'s shape (the stack landing needs no canPlace:
its rank guard is `deckStack`'s own). -/
theorem applyDrawStackTo_shape {st : State} {c : Card} {st' : State} :
    st.applyDrawStackTo c = some st' ↔
      ∃ i, st.reachablePos c = some i ∧ c.rank.toIdx = st.heights c.suit ∧
        st' = { st with
          stock := (st.stock.drawTo i).removeAt i,
          heights := fun s => if s = c.suit then st.heights s + 1 else st.heights s } := by
  constructor
  · intro h
    simp only [State.applyDrawStackTo] at h
    cases hpos : st.reachablePos c with
    | none => rw [hpos] at h; simp at h
    | some i =>
      rw [hpos] at h
      have h' : (if c.rank.toIdx = st.heights c.suit then
          some { st with
            stock := (st.stock.drawTo i).removeAt i,
            heights := fun s => if s = c.suit then st.heights s + 1 else st.heights s }
          else none) = some st' := h
      by_cases hrk : c.rank.toIdx = st.heights c.suit
      · rw [if_pos hrk, Option.some.injEq] at h'
        exact ⟨i, rfl, hrk, h'.symm⟩
      · rw [if_neg hrk] at h'; simp at h'
  · intro ⟨i, hpos, hrk, hst⟩
    rw [hst]
    simp only [State.applyDrawStackTo, hpos, if_pos hrk]

/-- The ← direction's core, shared by both jump-soundness theorems:
a deck move after `k` deals implies the guard — the dealt card sits at
an accessible position, and the splice agrees with the jump's. -/
theorem dealIter_prev_reachable {st : State} (hwf : st.WF) {c : Card} {k : Nat}
    (hprev : (Cycle.dealIter st.drawStep k st.stock).prev = some c) :
    ∃ i, st.reachablePos c = some i ∧
      (Cycle.dealIter st.drawStep k st.stock).removeAt
          ((Cycle.dealIter st.drawStep k st.stock).cursor - 1)
        = (st.stock.drawTo i).removeAt i := by
  have hs : 0 < st.drawStep := hwf.step_pos
  have hcards : (Cycle.dealIter st.drawStep k st.stock).cards = st.stock.cards :=
    Cycle.dealIter_cards _ _ _
  have hκle : (Cycle.dealIter st.drawStep k st.stock).cursor ≤ st.stock.cards.length :=
    dealIter_cursor_le _ _ _ hwf.cursor_le
  simp only [Cycle.prev] at hprev
  split at hprev
  · exact absurd hprev (by simp)
  · rename_i hκ0
    have hκne : (Cycle.dealIter st.drawStep k st.stock).cursor ≠ 0 := hκ0
    rw [hcards] at hprev
    have hmem : (Cycle.dealIter st.drawStep k st.stock).cursor - 1
        ∈ Pace.maskPos st.stock st.drawStep hs := by
      obtain (⟨m, hm⟩ | ⟨j, hj⟩) :=
        dealIter_orbit _ k st.stock.cards st.stock.cursor hwf.cursor_le
      · exact dealIter_mask hs hwf.cursor_le hκle hκne (Or.inl ⟨m, hm⟩)
      · exact dealIter_mask hs hwf.cursor_le hκle hκne (Or.inr ⟨j, hj⟩)
    have hpos : st.stock.posOf c
        = some ((Cycle.dealIter st.drawStep k st.stock).cursor - 1) := by
      cases hp : st.stock.posOf c with
      | none =>
          exfalso
          exact Cycle.posOf_mem (List.mem_iff_getElem?.mpr ⟨_, hprev⟩) hp
      | some i₀ =>
          have hget₂ : st.stock.cards[i₀]? = some c := posOf_get _ _ _ hp
          have hi₀ : i₀ < st.stock.cards.length := Cycle.posOf_lt hp
          have hκm1 : (Cycle.dealIter st.drawStep k st.stock).cursor - 1
              < st.stock.cards.length := (List.getElem?_eq_some_iff.mp hprev).1
          have heq : (Cycle.dealIter st.drawStep k st.stock).cursor - 1 = i₀ :=
            hwf.stock_wf.1 _ _ hκm1 hi₀ (hprev.trans hget₂.symm)
          exact congrArg some heq.symm
    refine ⟨(Cycle.dealIter st.drawStep k st.stock).cursor - 1,
      reachablePos_intro hs hpos hmem, ?_⟩
    show ({ cards := Cycle.removeIdx (Cycle.dealIter st.drawStep k st.stock).cards
              ((Cycle.dealIter st.drawStep k st.stock).cursor - 1),
            cursor := if (Cycle.dealIter st.drawStep k st.stock).cursor - 1
                < (Cycle.dealIter st.drawStep k st.stock).cursor
              then (Cycle.dealIter st.drawStep k st.stock).cursor - 1
              else (Cycle.dealIter st.drawStep k st.stock).cursor } : Cycle Card)
      = (st.stock.drawTo ((Cycle.dealIter st.drawStep k st.stock).cursor - 1)).removeAt
          ((Cycle.dealIter st.drawStep k st.stock).cursor - 1)
    rw [hcards, if_pos (by omega : (Cycle.dealIter st.drawStep k st.stock).cursor - 1
        < (Cycle.dealIter st.drawStep k st.stock).cursor), removeAt_drawTo]

/-- **The jump-soundness theorem**: the tableau-outcome Draw
commitment equals dealing until `c` is the waste top, then playing it
with the physical deck move — the reachable-position guard is exactly
the reachability of that deal sequence.

STATEMENT REPAIR (2026-09-13, the Wave-9 alert — the same hole as
Macro's `commitApplies` repair, witness there): the → direction needed
`st.canPlace c b = true` — `applyDrawTo`'s own guard (accessible
position + free base) does not check the landing rule, so without the
conjunct the theorem admitted Draw-commitment landings no play can
produce (♠7 pile-0's sole visible card, ♥5 the last stock card at the
pass-end cursor, base `inr ♠7`: the jump succeeds, `canSitOn ♥5 ♠7` is
false, so no `deckPile` ever reaches the successor).  With the guard:
→ the mask gives the deal count (`dealReach_maskPos`), then
`deckPile_after_deals`; ← the orbit lands in the mask
(`dealIter_prev_reachable`: `dealIter_mask` + the duplicate-freeness
pin). -/
theorem applyDrawTo_eq_dealPlay {st : State} (hwf : st.WF) {c : Card} {b : Base}
    (hcan : st.canPlace c b = true) {st'' : State} :
    st.applyDrawTo c b = some st'' ↔
      ∃ k st₁, st.run (List.replicate k Move.draw) = some st₁ ∧
        st₁.apply (Move.deckPile c b) = some st'' := by
  constructor
  · intro h
    obtain ⟨i, bd, hr, hatt, hst''⟩ := applyDrawTo_eq h
    have hs : 0 < st.drawStep := hwf.step_pos
    have hpos : st.stock.posOf c = some i := reachablePos_posOf hr
    have hmem := reachablePos_mask hs hr
    have hlt : i < st.stock.cards.length := Cycle.posOf_lt hpos
    obtain ⟨kk, hkk⟩ := dealReach_maskPos hs hlt hmem
    refine ⟨kk, { st with stock := Cycle.dealIter st.drawStep kk st.stock }, ?_, ?_⟩
    · rw [run_dealIter]
    · show ({ st with stock := Cycle.dealIter st.drawStep kk st.stock } : State).apply
          (Move.deckPile c b) = some st''
      rw [hkk]
      have hdp := deckPile_after_deals (posOf_get _ _ _ hpos) hcan hatt
      rw [hdp, removeAt_drawTo, hst'']
  · rintro ⟨k, st₁, hrun, hdp⟩
    rw [run_dealIter] at hrun
    have hst₁ : { st with stock := Cycle.dealIter st.drawStep k st.stock } = st₁ :=
      Option.some.inj hrun
    subst hst₁
    rw [apply_deckPile_iff] at hdp
    obtain ⟨hprev, -, bd, hatt, hst''⟩ := hdp
    obtain ⟨i, hrep, hstock⟩ := dealIter_prev_reachable hwf hprev
    have hatt' : st.board.attach b c = some bd := hatt
    have hXstock : ({ st with stock := Cycle.dealIter st.drawStep k st.stock } : State).stock
        = Cycle.dealIter st.drawStep k st.stock := rfl
    rw [hXstock] at hst''
    rw [hstock] at hst''
    rw [hst'']
    simp only [State.applyDrawTo, hrep, hatt']

/-- The stack-outcome twin: the safe-stack commitment equals dealing
to `c`, then the physical `deckStack` — no repair needed (the rank
guard is `deckStack`'s own). -/
theorem applyDrawStackTo_eq_dealPlay {st : State} (hwf : st.WF) {c : Card}
    {st'' : State} :
    st.applyDrawStackTo c = some st'' ↔
      ∃ k st₁, st.run (List.replicate k Move.draw) = some st₁ ∧
        st₁.apply (Move.deckStack c) = some st'' := by
  constructor
  · intro h
    obtain ⟨i, hr, hrk, hst''⟩ := (applyDrawStackTo_shape).mp h
    have hs : 0 < st.drawStep := hwf.step_pos
    have hpos : st.stock.posOf c = some i := reachablePos_posOf hr
    have hmem := reachablePos_mask hs hr
    have hlt : i < st.stock.cards.length := Cycle.posOf_lt hpos
    obtain ⟨kk, hkk⟩ := dealReach_maskPos hs hlt hmem
    refine ⟨kk, { st with stock := Cycle.dealIter st.drawStep kk st.stock }, ?_, ?_⟩
    · rw [run_dealIter]
    · show ({ st with stock := Cycle.dealIter st.drawStep kk st.stock } : State).apply
          (Move.deckStack c) = some st''
      rw [hkk]
      have hdp := deckStack_after_deals (posOf_get _ _ _ hpos) hrk
      rw [hdp, hst'']
  · rintro ⟨k, st₁, hrun, hds⟩
    rw [run_dealIter] at hrun
    have hst₁ : { st with stock := Cycle.dealIter st.drawStep k st.stock } = st₁ :=
      Option.some.inj hrun
    subst hst₁
    rw [apply_deckStack_iff] at hds
    obtain ⟨hprev, hrk, hst''⟩ := hds
    obtain ⟨i, hrep, hstock⟩ := dealIter_prev_reachable hwf hprev
    have hrk' : c.rank.toIdx = st.heights c.suit := hrk
    have hXstock : ({ st with stock := Cycle.dealIter st.drawStep k st.stock } : State).stock
        = Cycle.dealIter st.drawStep k st.stock := rfl
    rw [hXstock] at hst''
    rw [hstock] at hst''
    rw [hst'']
    simp only [State.applyDrawStackTo, hrep, if_pos hrk']
