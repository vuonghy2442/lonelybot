import Orig.Fate

/-!
# Orig — the twin swap and the twin quotient

The twin relabeling: every card's suit becomes its same-color twin
(hearts ↔ diamonds, spades ↔ clubs).  It is an involution on the
game — it conjugates the fit rules, the searches, the draw, and
`step` move for move, so every winning play maps to a winning play.

The theorems:

* `State.twin_step` — the conjugation: a move and its twin move
  agree step for step under the relabeling;
* `twin_fate` — the twin swap theorem in solvability:
  `WinFrom s ↔ WinFrom (twinMap s)`; `sameFate_twin` restates it in
  the futures vocabulary;
* the quotient reading — `twinSetoid` identifies each position
  with its swap, `WinFromQ` is solvability descended to the
  quotient (well-defined by `twin_fate`), and `twin_quotient` is
  the resulting theorem: swap-related positions have the same
  verdict.

This is the generator instance of the symmetry family (any
color-preserving suit permutation is expected to work the same
way; the schema is a later chapter's ticket).
-/

/-! ## The relabeling -/

/-- The twin relabeling on cards. -/
def Card.twin (c : Card) : Card := ⟨c.suit.twin, c.rank⟩

@[simp] theorem Card.twin_rank (c : Card) : c.twin.rank = c.rank := rfl

@[simp] theorem Card.twin_suit (c : Card) : c.twin.suit = c.suit.twin := rfl

@[simp] theorem Card.twin_twin (c : Card) : c.twin.twin = c := by
  rcases c with ⟨s, r⟩
  simp [Card.twin, Suit.twin_twin]

theorem Suit.twin_inj {s s' : Suit} (h : s.twin = s'.twin) : s = s' := by
  have := congrArg Suit.twin h
  simpa using this

theorem Card.twin_inj {a b : Card} (h : a.twin = b.twin) : a = b := by
  rcases a with ⟨s, r⟩
  rcases b with ⟨s', r'⟩
  simp only [Card.twin] at h
  injection h with hs hr
  subst hr
  have hst : s = s' := Suit.twin_inj hs
  subst hst
  rfl

theorem Suit.twin_mem_all (s : Suit) : s.twin ∈ Suit.all := by
  cases s <;> simp [Suit.twin, Suit.all]

@[simp] theorem decide_twin_eq (c z : Card) : decide (c.twin = z.twin) = decide (c = z) := by
  by_cases h : c = z
  · subst h; simp
  · have h' : c.twin ≠ z.twin := fun hcon => h (Card.twin_inj hcon)
    have h1 : decide (c = z) = false := by
      cases hdec : decide (c = z) with
      | true => exact absurd (of_decide_eq_true hdec) h
      | false => rfl
    have h2 : decide (c.twin = z.twin) = false := by
      cases hdec : decide (c.twin = z.twin) with
      | true => exact absurd (of_decide_eq_true hdec) h'
      | false => rfl
    rw [h2, h1]

theorem canSitOn_twin_left (c b : Card) : canSitOn c.twin b = canSitOn c b := by
  rcases c with ⟨s, r⟩
  rcases b with ⟨s', r'⟩
  cases s <;> cases s' <;> rfl

theorem canSitOn_twin_twin (c b : Card) : canSitOn c.twin b.twin = canSitOn c b := by
  rcases c with ⟨s, r⟩
  rcases b with ⟨s', r'⟩
  cases s <;> cases s' <;> rfl

/-- The twin relabeling on a pile. -/
def Pile.twinMap (p : Pile) : Pile :=
  ⟨p.hidden.map Card.twin, p.faceUp.map Card.twin⟩

@[simp] theorem Pile.twinMap_hidden (p : Pile) :
    p.twinMap.hidden = p.hidden.map Card.twin := rfl

@[simp] theorem Pile.twinMap_faceUp (p : Pile) :
    p.twinMap.faceUp = p.faceUp.map Card.twin := rfl

theorem Pile.isEmpty_twinMap (p : Pile) : p.twinMap.isEmpty = p.isEmpty := by
  rcases p with ⟨h, f⟩
  cases h <;> cases f <;> rfl

/-- The twin relabeling on a base: anchors stay, cards flip. -/
def Base.twinMap (b : Base) : Base := Sum.map id Card.twin b

/-- The twin relabeling on a move. -/
def Move.twinMove : Move → Move
  | .draw => .draw
  | .wasteToFound c => .wasteToFound c.twin
  | .wasteToTab c b => .wasteToTab c.twin b.twinMap
  | .tabToFound c => .tabToFound c.twin
  | .foundToTab c b => .foundToTab c.twin b.twinMap
  | .tabToTab c b => .tabToTab c.twin b.twinMap

/-- The twin relabeling on positions: every zone twin-maps, the
anchors stay, the draw step is untouched. -/
def State.twinMap (st : State) : State where
  found := fun s => (st.found s.twin).map Card.twin
  piles := fun a => (st.piles a).twinMap
  stock := st.stock.map Card.twin
  waste := st.waste.map Card.twin
  drawStep := st.drawStep

@[simp] theorem State.twinMap_found (st : State) (s : Suit) :
    st.twinMap.found s = (st.found s.twin).map Card.twin := rfl

@[simp] theorem State.twinMap_piles (st : State) (a : Anchor) :
    st.twinMap.piles a = (st.piles a).twinMap := rfl

@[simp] theorem State.twinMap_stock (st : State) :
    st.twinMap.stock = st.stock.map Card.twin := rfl

@[simp] theorem State.twinMap_waste (st : State) :
    st.twinMap.waste = st.waste.map Card.twin := rfl

@[simp] theorem State.twinMap_drawStep (st : State) :
    st.twinMap.drawStep = st.drawStep := rfl

private theorem twinMap_found_apply (st : State) (c : Card) :
    st.twinMap.found c.twin.suit = (st.found c.suit).map Card.twin := by
  rw [State.twinMap_found]
  have h : (Card.twin c).suit.twin = c.suit := by
    rw [Card.twin_suit, Suit.twin_twin]
  rw [h]

/-! ## The conjugation kit -/

theorem firstWhere_congr {α : Type} {p q : α → Bool} (h : ∀ x, p x = q x) :
    ∀ {l : List α}, firstWhere p l = firstWhere q l := by
  intro l
  induction l with
  | nil => rfl
  | cons x t ih =>
      rw [firstWhere, firstWhere, h x]
      split
      · rfl
      · exact ih

private theorem map_twin_twin (l : List Card) :
    (l.map Card.twin).map Card.twin = l := by
  induction l with
  | nil => rfl
  | cons x t ih => simp [List.map_cons, ih, Card.twin_twin]

private theorem lastOf_map (l : List Card) :
    lastOf (l.map Card.twin) = (lastOf l).map Card.twin := by
  induction l with
  | nil => rfl
  | cons x t ih =>
      cases t with
      | nil => rfl
      | cons y t' =>
          simp only [lastOf, lastOf]
          exact ih

private theorem chop_map (l : List Card) :
    chop (l.map Card.twin) = (chop l).map Card.twin := by
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

private theorem below_map (c : Card) (l : List Card) :
    (below c l).map Card.twin = below c.twin (l.map Card.twin) := by
  induction l with
  | nil => rfl
  | cons x t ih =>
      by_cases h : x = c
      · subst h
        simp [below]
      · by_cases h' : x.twin = c.twin
        · exact absurd (Card.twin_inj h') h
        · rw [below, List.map_cons, below,
              show (if x = c then [] else x :: below c t) = x :: below c t from by
                simp [show ¬(x = c) from h],
              show (if x.twin = c.twin then []
                  else x.twin :: below c.twin (List.map Card.twin t)) =
                  x.twin :: below c.twin (List.map Card.twin t) from by
                simp [show ¬(x.twin = c.twin) from h'],
              List.map_cons, ih]

private theorem fromCard_map (c : Card) (l : List Card) :
    (fromCard c l).map Card.twin = fromCard c.twin (l.map Card.twin) := by
  induction l with
  | nil => rfl
  | cons x t ih =>
      by_cases h : x = c
      · subst h
        simp [fromCard]
      · by_cases h' : x.twin = c.twin
        · exact absurd (Card.twin_inj h') h
        · rw [fromCard, List.map_cons, fromCard,
              show (if x = c then x :: t else fromCard c t) = fromCard c t from by
                simp [show ¬(x = c) from h],
              show (if x.twin = c.twin then x.twin :: List.map Card.twin t
                  else fromCard c.twin (List.map Card.twin t)) =
                  fromCard c.twin (List.map Card.twin t) from by
                simp [show ¬(x.twin = c.twin) from h'],
              ih]

private theorem fromCard_ne_nil_of_mem {c : Card} :
    ∀ {l : List Card}, c ∈ l → fromCard c l ≠ [] := by
  intro l
  induction l with
  | nil => intro h; cases h
  | cons x t ih =>
      intro hmem
      by_cases hx : x = c
      · rw [fromCard, ite_eq_left hx]
        intro hcon
        exact absurd hcon (by simp)
      · rw [fromCard, ite_eq_right hx]
        refine ih ?_
        have hmem' : c = x ∨ c ∈ t := by simpa using hmem
        rcases hmem' with h | h
        · exact absurd h.symm hx
        · exact h

private theorem map_rev (l : List Card) :
    (l.map Card.twin).reverse = l.reverse.map Card.twin := by
  induction l with
  | nil => rfl
  | cons x t ih =>
      rw [List.map_cons, List.reverse_cons, List.reverse_cons, List.map_append, ih]
      rfl

private theorem dealUpTo_twin (k : Nat) (l : List Card) :
    State.dealUpTo k (l.map Card.twin) =
      ((State.dealUpTo k l).1.map Card.twin, (State.dealUpTo k l).2.map Card.twin) := by
  induction k generalizing l with
  | zero => rfl
  | succ n ih =>
      cases l with
      | nil => rfl
      | cons x t =>
          show (x.twin :: (State.dealUpTo n (List.map Card.twin t)).1,
              (State.dealUpTo n (List.map Card.twin t)).2) =
            (x.twin :: ((State.dealUpTo n t).1).map Card.twin,
              ((State.dealUpTo n t).2).map Card.twin)
          rw [ih]

private theorem mem_map_twin (c : Card) (l : List Card) :
    c.twin ∈ l.map Card.twin ↔ c ∈ l := by
  simp only [List.mem_map]
  constructor
  · rintro ⟨d, hd, heq⟩
    have : d = c := Card.twin_inj heq
    exact this ▸ hd
  · intro hmem
    exact ⟨c, hmem, rfl⟩

private theorem decide_map_eq {x : Option Card} {c : Card} :
    decide (x.map Card.twin = some c.twin) = decide (x = some c) := by
  cases x with
  | none => rfl
  | some d =>
      by_cases h : d = c
      · subst h; simp
      · simp [h]

/-! ## The state-level conjugations -/

@[simp] theorem State.topOf_twinMap (st : State) (a : Anchor) :
    st.twinMap.topOf a = (st.topOf a).map Card.twin := by
  show lastOf (Pile.twinMap (st.piles a)).faceUp = (lastOf (st.piles a).faceUp).map Card.twin
  exact lastOf_map _

@[simp] theorem State.foundHeight_twinMap (st : State) (s : Suit) :
    st.twinMap.foundHeight s = st.foundHeight s.twin := by
  simp [State.foundHeight, List.length_map]

@[simp] theorem State.foundTop_twinMap (st : State) (s : Suit) :
    st.twinMap.foundTop s = (st.foundTop s.twin).map Card.twin := by
  show lastOf ((st.found s.twin).map Card.twin) = (lastOf (st.found s.twin)).map Card.twin
  exact lastOf_map _

@[simp] theorem State.wasteIs_twinMap (st : State) (c : Card) :
    st.twinMap.wasteIs c.twin = st.wasteIs c := by
  cases h : st.waste with
  | nil => simp [State.wasteIs, State.twinMap_waste, h, List.map_nil]
  | cons x t => simp [State.wasteIs, State.twinMap_waste, h, List.map_cons, decide_twin_eq]

@[simp] theorem State.nextUp_twinMap (st : State) (c : Card) :
    st.twinMap.nextUp c.twin = st.nextUp c := by
  show decide ((Card.twin c).rank.toIdx =
        (State.twinMap st).foundHeight (Card.twin c).suit) =
       decide (c.rank.toIdx = st.foundHeight c.suit)
  rw [State.foundHeight_twinMap, Card.twin_suit, Suit.twin_twin]
  rfl

@[simp] theorem State.pileOfTop_twinMap (st : State) (z : Card) :
    st.twinMap.pileOfTop z.twin = st.pileOfTop z := by
  simp only [State.pileOfTop]
  refine firstWhere_congr fun a => ?_
  rw [State.topOf_twinMap, decide_map_eq]

@[simp] theorem State.pileHolding_twinMap (st : State) (c : Card) :
    st.twinMap.pileHolding c.twin = st.pileHolding c := by
  simp only [State.pileHolding, State.twinMap, Pile.twinMap]
  refine firstWhere_congr fun a => ?_
  show decide (Card.twin c ∈ (st.piles a).faceUp.map Card.twin)
      = decide (c ∈ (st.piles a).faceUp)
  simp [mem_map_twin]

private theorem pileHolding_mem {st : State} {c : Card} {a : Anchor}
    (h : st.pileHolding c = some a) : c ∈ (st.piles a).faceUp :=
  of_decide_eq_true (firstWhere_sound (p := fun a' => decide (c ∈ (st.piles a').faceUp)) h)

@[ simp] theorem State.canPlace_twinMap (st : State) (c : Card) (b : Base) :
    st.twinMap.canPlace c.twin b.twinMap = st.canPlace c b := by
  cases b <;> simp [State.canPlace, Base.twinMap, State.twinMap_piles,
    Pile.isEmpty_twinMap, canSitOn_twin_twin, State.pileOfTop_twinMap] <;> (try rfl)

/-! ## The relabeling is an involution -/

private theorem pile_twinMap_twinMap (p : Pile) : p.twinMap.twinMap = p := by
  apply Pile.ext
  · exact map_twin_twin p.hidden
  · exact map_twin_twin p.faceUp

theorem State.twinMap_twinMap (st : State) : st.twinMap.twinMap = st := by
  apply State.ext
  · funext s
    show ((st.found (Suit.twin (Suit.twin s))).map Card.twin).map Card.twin = st.found s
    rw [map_twin_twin]
    simp
  · funext a
    exact pile_twinMap_twinMap (st.piles a)
  · exact map_twin_twin st.stock
  · exact map_twin_twin st.waste
  · rfl

/-! ## Record updates under the relabeling -/

private theorem twinMap_wasteUpd (st : State) (ws : List Card) :
    State.twinMap { st with waste := ws } =
      { st.twinMap with waste := ws.map Card.twin } := by
  simp only [State.twinMap, Pile.twinMap]

private theorem twinMap_dealUpd2 (st : State) (s w : List Card) :
    State.twinMap (State.mk st.found st.piles s w st.drawStep) =
      State.mk st.twinMap.found st.twinMap.piles (s.map Card.twin) (w.map Card.twin)
        st.twinMap.drawStep := by
  apply State.ext
  · funext σ
    rfl
  · funext a
    rfl
  · rfl
  · rfl
  · rfl

private theorem twinMap_dealUpd (st : State) (s w : List Card) :
    State.twinMap { st with stock := s, waste := w } =
      { st.twinMap with stock := s.map Card.twin, waste := w.map Card.twin } := by
  simp only [State.twinMap, Pile.twinMap]

theorem State.twinMap_setPile (st : State) (a : Anchor) (p : Pile) :
    State.twinMap (st.setPile a p) = st.twinMap.setPile a p.twinMap := by
  apply State.ext
  · rfl
  · funext a'
    show Pile.twinMap (if a' = a then p else st.piles a') =
        if a' = a then p.twinMap else (st.piles a').twinMap
    by_cases h : a' = a
    · rw [ite_eq_left h, ite_eq_left h]
    · rw [ite_eq_right h, ite_eq_right h]
  · rfl
  · rfl
  · rfl

theorem State.twinMap_setFound (st : State) (s : Suit) (l : List Card) :
    State.twinMap (st.setFound s l) = st.twinMap.setFound s.twin (l.map Card.twin) := by
  apply State.ext
  · funext s'
    show (if s'.twin = s then l else st.found s'.twin).map Card.twin =
        if s' = s.twin then l.map Card.twin else (State.twinMap st).found s'
    by_cases h : s'.twin = s
    · have h' : s' = s.twin := by rw [← Suit.twin_twin s', h]
      rw [ite_eq_left h, ite_eq_left h']
    · have h' : s' ≠ s.twin := by
        intro hc
        apply h
        rw [hc]
        exact Suit.twin_twin s
      rw [ite_eq_right h, ite_eq_right h']
      exact (State.twinMap_found st s').symm
  · rfl
  · rfl
  · rfl
  · rfl

theorem State.twinMap_putCard (st : State) (c : Card) (b : Base) :
    State.twinMap (st.putCard c b) = st.twinMap.putCard c.twin b.twinMap := by
  cases b with
  | inl a =>
      rw [show st.putCard c (.inl a) = st.setPile a ⟨[], [c]⟩ from by
          simp only [State.putCard]]
      rw [State.twinMap_setPile]
      rfl
  | inr z =>
      cases h : st.pileOfTop z with
      | none =>
          have hL : st.putCard c (Sum.inr z) = st := by simp only [State.putCard, h]
          have hR : st.twinMap.putCard c.twin (Base.twinMap (Sum.inr z)) = st.twinMap := by
            have hb : Base.twinMap (Sum.inr z) = Sum.inr (Card.twin z) := rfl
            rw [hb]
            simp only [State.putCard, State.pileOfTop_twinMap, h]
          rw [hL, hR]
      | some k =>
          have hL : st.putCard c (Sum.inr z) =
              st.setPile k { st.piles k with faceUp := (st.piles k).faceUp ++ [c] } := by
            simp only [State.putCard, h]
          have hR : st.twinMap.putCard c.twin (Base.twinMap (Sum.inr z)) =
              st.twinMap.setPile k
                { (st.twinMap.piles k) with
                  faceUp := (st.twinMap.piles k).faceUp ++ [Card.twin c] } := by
            have hb : Base.twinMap (Sum.inr z) = Sum.inr (Card.twin z) := rfl
            rw [hb]
            simp only [State.putCard, State.pileOfTop_twinMap, h, State.twinMap_piles]
          rw [hL, State.twinMap_setPile, hR]
          apply State.ext
          · rfl
          · funext a'
            show (if a' = k
                  then Pile.twinMap { st.piles k with faceUp := (st.piles k).faceUp ++ [c] }
                  else (st.twinMap.piles a')) =
                (if a' = k
                  then { (st.twinMap.piles k) with
                    faceUp := (st.twinMap.piles k).faceUp ++ [Card.twin c] }
                  else (st.twinMap.piles a'))
            by_cases hk : a' = k
            · subst hk
              simp only []
              apply Pile.ext
              · exact Pile.twinMap_hidden _
              · show ((st.piles a').faceUp ++ [c]).map Card.twin =
                  (st.piles a').faceUp.map Card.twin ++ [Card.twin c]
                rw [List.map_append]
                rfl
            · simp only [ite_eq_right hk]
          · rfl
          · rfl
          · rfl

theorem State.twinMap_putRun (st : State) (run : List Card) (b : Base) :
    State.twinMap (st.putRun run b) = st.twinMap.putRun (run.map Card.twin) b.twinMap := by
  cases b with
  | inl a =>
      rw [show st.putRun run (.inl a) = st.setPile a ⟨[], run⟩ from by
          simp only [State.putRun]]
      rw [State.twinMap_setPile]
      rfl
  | inr z =>
      cases h : st.pileOfTop z with
      | none =>
          have hL : st.putRun run (Sum.inr z) = st := by simp only [State.putRun, h]
          have hR : st.twinMap.putRun (run.map Card.twin) (Base.twinMap (Sum.inr z))
              = st.twinMap := by
            have hb : Base.twinMap (Sum.inr z) = Sum.inr (Card.twin z) := rfl
            rw [hb]
            simp only [State.putRun, State.pileOfTop_twinMap, h]
          rw [hL, hR]
      | some k =>
          have hL : st.putRun run (Sum.inr z) =
              st.setPile k { st.piles k with faceUp := (st.piles k).faceUp ++ run } := by
            simp only [State.putRun, h]
          have hR : st.twinMap.putRun (run.map Card.twin) (Base.twinMap (Sum.inr z)) =
              st.twinMap.setPile k
                { (st.twinMap.piles k) with
                  faceUp := (st.twinMap.piles k).faceUp ++ run.map Card.twin } := by
            have hb : Base.twinMap (Sum.inr z) = Sum.inr (Card.twin z) := rfl
            rw [hb]
            simp only [State.putRun, State.pileOfTop_twinMap, h, State.twinMap_piles]
          rw [hL, State.twinMap_setPile, hR]
          apply State.ext
          · rfl
          · funext a'
            show (if a' = k
                  then Pile.twinMap { st.piles k with faceUp := (st.piles k).faceUp ++ run }
                  else (st.twinMap.piles a')) =
                (if a' = k
                  then { (st.twinMap.piles k) with
                    faceUp := (st.twinMap.piles k).faceUp ++ run.map Card.twin }
                  else (st.twinMap.piles a'))
            by_cases hk : a' = k
            · subst hk
              simp only [ite_true]
              apply Pile.ext
              · exact Pile.twinMap_hidden _
              · show ((st.piles a').faceUp ++ run).map Card.twin =
                  (st.twinMap.piles a').faceUp ++ run.map Card.twin
                rw [show st.twinMap.piles a' = Pile.twinMap (st.piles a') from rfl]
                simp only [Pile.twinMap_faceUp, List.map_append]
            · simp only [ite_eq_right hk]
          · rfl
          · rfl
          · rfl

theorem Pile.twinMap_afterRunRemoved (p : Pile) (pre : List Card) :
    (Pile.afterRunRemoved p pre).twinMap = Pile.afterRunRemoved p.twinMap (pre.map Card.twin) := by
  cases pre with
  | nil =>
      rcases p with ⟨h, f⟩
      cases h <;> rfl
  | cons y t => rfl

private theorem option_map_some {α β : Type} (f : α → β) (x : α) :
    (some x).map f = some (f x) := rfl

private theorem option_map_none {α β : Type} (f : α → β) :
    (none : Option α).map f = none := rfl


theorem State.recycle_twinMap (st : State) :
    st.recycle.twinMap = (st.twinMap).recycle := by
  cases hs : st.stock with
  | nil =>
      cases hw : st.waste with
      | nil =>
          rw [show st.recycle = st from by simp only [State.recycle, hs, hw],
              show st.twinMap.recycle = st.twinMap from by
                simp only [State.recycle, State.twinMap_stock, State.twinMap_waste, hs, hw,
                  List.map_nil, List.map_nil]]
      | cons x t =>
          rw [show st.recycle = { st with stock := (x :: t).reverse, waste := [] } from by
              simp only [State.recycle, hs, hw]]
          rw [twinMap_dealUpd, List.map_nil, ← map_rev, List.map_cons,
              show (State.twinMap st).recycle =
                { st.twinMap with
                  stock := ((Card.twin x) :: (t.map Card.twin)).reverse, waste := [] } from by
              simp only [State.recycle, State.twinMap_stock, State.twinMap_waste, hs, hw,
                List.map_cons, List.map_nil]]
  | cons y s =>
      rw [show st.recycle = st from by simp only [State.recycle, hs],
          show st.twinMap.recycle = st.twinMap from by
            simp only [State.recycle, State.twinMap_stock, hs, List.map_cons]]

theorem State.dealStock_twinMap (st : State) :
    st.dealStock.map State.twinMap = (st.twinMap).dealStock := by
  cases hs : st.stock with
  | nil =>
      rw [show st.dealStock = none from by simp only [State.dealStock, hs],
         show (State.twinMap st).dealStock = none from by
           simp only [State.dealStock, State.twinMap_stock, hs, List.map_nil],
         option_map_none]
  | cons y s =>
      have hL : st.dealStock = Option.some (State.mk st.found st.piles
          (State.dealUpTo st.drawStep (y :: s)).2
          ((State.dealUpTo st.drawStep (y :: s)).1.reverse ++ st.waste) st.drawStep) := by
        simp only [State.dealStock, hs]
      have hR : (State.twinMap st).dealStock = Option.some (State.mk st.twinMap.found
          st.twinMap.piles (((State.dealUpTo st.drawStep (y :: s)).2).map Card.twin)
          ((((State.dealUpTo st.drawStep (y :: s)).1).map Card.twin).reverse
            ++ st.waste.map Card.twin) st.twinMap.drawStep) := by
        simp only [State.dealStock, State.twinMap_stock, State.twinMap_waste,
          State.twinMap_drawStep, hs, List.map_cons]
        rw [← List.map_cons, dealUpTo_twin, map_rev]
      rw [hL, hR, option_map_some, Option.some.injEq, twinMap_dealUpd2, List.map_append,
        ← map_rev]

theorem State.stepDraw_twinMap (st : State) :
    st.stepDraw.map State.twinMap = (st.twinMap).stepDraw := by
  have h := State.dealStock_twinMap st.recycle
  rw [State.recycle_twinMap st] at h
  exact h

/-- The conjugation: a move at `st` corresponds step for step to
its twin move at the twin position. -/
theorem State.twin_step (st : State) (m : Move) :
    (st.step m).map State.twinMap = (st.twinMap).step m.twinMove := by
  cases m with
  | draw => exact st.stepDraw_twinMap
  | wasteToFound c =>
      show (st.step (Move.wasteToFound c)).map State.twinMap =
        (st.twinMap).step (Move.wasteToFound (Card.twin c))
      by_cases hg : (st.wasteIs c && st.nextUp c) = true
      · cases hwl : st.waste with
        | nil =>
            rw [State.wasteIs_nil hwl] at hg
            exact absurd hg (by simp)
        | cons x t =>
            rw [show st.step (.wasteToFound c) =
                  some { st.setFound c.suit (st.found c.suit ++ [c]) with waste := t } from by
                simp only [State.step, hwl, hg, ite_true]]
            rw [show (State.twinMap st).step (Move.wasteToFound (Card.twin c)) =
                  some { st.twinMap.setFound (Card.twin c).suit
                      ((st.found c.suit).map Card.twin ++ [Card.twin c])
                    with waste := t.map Card.twin } from by
                simp only [State.step, State.wasteIs_twinMap, State.nextUp_twinMap, State.twinMap_waste, hwl, List.map_cons, hg, ite_true]
                rw [twinMap_found_apply]]
            rw [option_map_some, Option.some.injEq]
            rw [twinMap_wasteUpd, State.twinMap_setFound, Card.twin_suit, List.map_append]
            rfl
      · have hf : (st.wasteIs c && st.nextUp c) = false := by
          cases hg2 : st.wasteIs c && st.nextUp c with
          | true => exact absurd hg2 hg
          | false => rfl
        rw [show st.step (.wasteToFound c) = none from by simp [State.step, hf],
           show (State.twinMap st).step (Move.wasteToFound (Card.twin c)) = none from by
             simp [State.step, State.wasteIs_twinMap, State.nextUp_twinMap, hf],
           option_map_none]
  | wasteToTab c b =>
      show (st.step (Move.wasteToTab c b)).map State.twinMap =
        (st.twinMap).step (Move.wasteToTab (Card.twin c) b.twinMap)
      by_cases hg : (st.wasteIs c && st.canPlace c b) = true
      · cases hwl : st.waste with
        | nil =>
            rw [State.wasteIs_nil hwl] at hg
            exact absurd hg (by simp)
        | cons x t =>
            rw [show st.step (.wasteToTab c b) = some { st.putCard c b with waste := t } from by
                simp only [State.step, hwl, hg, ite_true]]
            rw [show (State.twinMap st).step (Move.wasteToTab (Card.twin c) b.twinMap) =
                  some { st.twinMap.putCard (Card.twin c) b.twinMap with
                    waste := t.map Card.twin } from by
                simp only [State.step, State.wasteIs_twinMap, State.canPlace_twinMap, State.twinMap_waste, hwl, List.map_cons, hg, ite_true]]
            rw [option_map_some, Option.some.injEq]
            rw [twinMap_wasteUpd, State.twinMap_putCard]
      · have hf : (st.wasteIs c && st.canPlace c b) = false := by
          cases hg2 : st.wasteIs c && st.canPlace c b with
          | true => exact absurd hg2 hg
          | false => rfl
        rw [show st.step (.wasteToTab c b) = none from by simp [State.step, hf],
           show (State.twinMap st).step (Move.wasteToTab (Card.twin c) b.twinMap) = none from by
             simp [State.step, State.wasteIs_twinMap, State.canPlace_twinMap, hf],
           option_map_none]
  | tabToFound c =>
      show (st.step (Move.tabToFound c)).map State.twinMap =
        (st.twinMap).step (Move.tabToFound (Card.twin c))
      by_cases hu : st.nextUp c = true
      · cases hp : st.pileOfTop c with
        | none =>
            rw [show st.step (.tabToFound c) = none from by
                  simp only [State.step, hu, hp, ite_true],
               show (State.twinMap st).step (Move.tabToFound (Card.twin c)) = none from by
                 simp only [State.step, State.nextUp_twinMap, State.pileOfTop_twinMap, hu, hp, ite_true],
               option_map_none]
        | some a =>
            rw [show st.step (.tabToFound c) =
                  some { st.setFound c.suit (st.found c.suit ++ [c]) with
                    piles := fun a' =>
                      if a' = a then Pile.afterRunRemoved (st.piles a) (chop (st.piles a).faceUp)
                      else st.piles a' } from by
                simp only [State.step, hu, hp, ite_true]]
            rw [show (State.twinMap st).step (Move.tabToFound (Card.twin c)) =
                  some { st.twinMap.setFound (Card.twin c).suit
                      ((st.found c.suit).map Card.twin ++ [Card.twin c]) with
                    piles := fun a' =>
                      if a' = a then Pile.afterRunRemoved (Pile.twinMap (st.piles a))
                          (chop ((st.piles a).faceUp.map Card.twin))
                      else (st.piles a').twinMap } from by
                simp only [State.step, State.nextUp_twinMap, State.pileOfTop_twinMap, hu, hp, ite_true]
                rw [twinMap_found_apply, State.twinMap_piles, Pile.twinMap_faceUp]
                rfl]
            rw [option_map_some, Option.some.injEq]
            apply State.ext
            · funext σ
              simp only [State.twinMap, State.setFound]
              by_cases hσ : σ.twin = c.suit
              · have h' : σ = c.suit.twin := by
                  have := congrArg Suit.twin hσ
                  rwa [Suit.twin_twin σ] at this
                simp [h', Card.twin_suit, List.map_append]
              · have h' : σ ≠ c.suit.twin := by
                  intro hc
                  apply hσ
                  rw [hc]
                  exact (Suit.twin_twin c.suit)
                simp [hσ, h', Card.twin_suit]
            · funext a''
              by_cases hA : a'' = a
              · simp [hA, Pile.twinMap_afterRunRemoved, ← chop_map]
              · simp [hA]
            · rfl
            · rfl
            · rfl
      · rw [show st.step (.tabToFound c) = none from by
            simp [State.step, hu],
         show (State.twinMap st).step (Move.tabToFound (Card.twin c)) = none from by
            simp [State.step, State.nextUp_twinMap, hu],
         option_map_none]
  | foundToTab c b =>
      show (st.step (Move.foundToTab c b)).map State.twinMap =
        (st.twinMap).step (Move.foundToTab (Card.twin c) b.twinMap)
      cases ht : st.foundTop c.suit with
      | none =>
          rw [show st.step (.foundToTab c b) = none from by
                simp [State.step, ht],
             show (State.twinMap st).step (Move.foundToTab (Card.twin c) b.twinMap) = none from by
                simp [State.step, State.foundTop_twinMap, Card.twin_suit, Suit.twin_twin, ht],
             option_map_none]
      | some c' =>
          by_cases hc : c' = c
          · rw [hc] at ht
            by_cases hb : st.canPlace c b = true
            · rw [show st.step (.foundToTab c b) =
                    some ((st.setFound c.suit (chop (st.found c.suit))).putCard c b) from by
                  simp [State.step, ht, hb]]
              rw [show (State.twinMap st).step (Move.foundToTab (Card.twin c) b.twinMap) =
                    some ((st.twinMap.setFound (Card.twin c).suit
                      (chop ((st.found c.suit).map Card.twin))).putCard c.twin b.twinMap) from by
                  simp [State.step, State.foundTop_twinMap, Card.twin_suit, Suit.twin_twin,
                    ht, State.canPlace_twinMap, hb]]
              rw [option_map_some, Option.some.injEq]
              rw [State.twinMap_putCard, State.twinMap_setFound, chop_map, Card.twin_suit]
            · rw [show st.step (.foundToTab c b) = none from by
                  simp [State.step, ht, hb],
                 show (State.twinMap st).step (Move.foundToTab (Card.twin c) b.twinMap) = none from by
                  simp [State.step, State.foundTop_twinMap, Card.twin_suit, Suit.twin_twin,
                    ht, State.canPlace_twinMap, hb],
                 option_map_none]
          · rw [show st.step (.foundToTab c b) = none from by
                simp [State.step, ht, hc],
             show (State.twinMap st).step (Move.foundToTab (Card.twin c) b.twinMap) = none from by
                simp [State.step, State.foundTop_twinMap, Card.twin_suit, Suit.twin_twin,
                  ht, State.canPlace_twinMap, hc],
             option_map_none]
  | tabToTab c b =>
      show (st.step (Move.tabToTab c b)).map State.twinMap =
        (st.twinMap).step (Move.tabToTab (Card.twin c) b.twinMap)
      cases hh : st.pileHolding c with
      | none =>
          rw [show st.step (.tabToTab c b) = none from by
                simp only [State.step, hh],
             show (State.twinMap st).step (Move.tabToTab (Card.twin c) b.twinMap) = none from by
                simp [State.step, State.pileHolding_twinMap, hh],
             option_map_none]
      | some a =>
          have hmem : c ∈ (st.piles a).faceUp := pileHolding_mem hh
          by_cases hcp : (st.canPlace c b) = true
          · have hne : fromCard c (st.piles a).faceUp ≠ [] := fromCard_ne_nil_of_mem hmem
            cases hfcr : fromCard c (st.piles a).faceUp with
            | cons w wt =>
                rw [show st.step (.tabToTab c b) =
                      some ((st.setPile a (Pile.afterRunRemoved (st.piles a)
                        (below c (st.piles a).faceUp))).putRun (w :: wt) b) from by
                      simp only [State.step, hh, hcp, hfcr, ite_true]]
                rw [show (State.twinMap st).step (Move.tabToTab (Card.twin c) b.twinMap) =
                      some ((st.twinMap.setPile a (Pile.afterRunRemoved
                          (Pile.twinMap (st.piles a))
                          (below (Card.twin c) ((st.piles a).faceUp.map Card.twin)))).putRun
                        (fromCard (Card.twin c) ((st.piles a).faceUp.map Card.twin))
                        b.twinMap) from by
                      simp only [State.step, State.pileHolding_twinMap, State.canPlace_twinMap,
                        hh, hcp, State.twinMap_piles, Pile.twinMap_faceUp, ite_true]
                      rw [(fromCard_map c ((st.piles a).faceUp)).symm, hfcr, List.map_cons]]
                rw [option_map_some, Option.some.injEq]
                rw [State.twinMap_putRun, State.twinMap_setPile,
                  Pile.twinMap_afterRunRemoved, below_map, ← hfcr, fromCard_map]
                first
                | rfl
                | (skip)
            | nil => exact absurd hfcr hne
          · rw [show st.step (.tabToTab c b) = none from by
                simp [State.step, hh, hcp],
             show (State.twinMap st).step (Move.tabToTab (Card.twin c) b.twinMap) = none from by
                simp [State.step, State.pileHolding_twinMap, State.canPlace_twinMap, hh, hcp],
             option_map_none]

private theorem bool_eq_of_true_iff {a b : Bool} (h : a = true ↔ b = true) : a = b := by
  cases a with
  | true =>
      cases b with
      | true => rfl
      | false => exact absurd (h.mp rfl) (by simp)
  | false =>
      cases b with
      | true => exact absurd (h.mpr rfl) (by simp)
      | false => rfl

theorem State.isWin_twinMap (st : State) : st.twinMap.isWin = st.isWin := by
  have allT : ∀ st' : State, st'.isWin = true ↔ ∀ s ∈ Suit.all, (st'.found s).length = 13 := by
    intro st'
    rw [State.isWin, List.all_eq_true]
    constructor
    · intro hall s hs
      have := hall s hs
      simpa [decide_eq_true_eq] using this
    · intro hall s hs
      simp [hall s hs]
  have hw : st.twinMap.isWin = true ↔ st.isWin = true := by
    rw [allT st.twinMap, allT st]
    constructor
    · rintro hall s _
      have hh := hall s.twin (Suit.twin_mem_all s)
      rwa [State.twinMap_found, List.length_map, Suit.twin_twin] at hh
    · rintro hall s _
      have hh := hall s.twin (Suit.twin_mem_all s)
      rwa [State.twinMap_found, List.length_map]
  exact bool_eq_of_true_iff hw

/-! ## The theorems -/

theorem twin_run (s : State) : ∀ (play : List Move) (w : State),
    s.run play = some w →
    (State.twinMap s).run (play.map Move.twinMove) = some (State.twinMap w) := by
  intro play
  induction play generalizing s with
  | nil =>
      intro w h
      injection h with h'
      subst h'
      rfl
  | cons m rest ih =>
      intro w h
      obtain ⟨s₁, hstep, hrest⟩ := State.run_cons h
      have hrun' : (State.twinMap s).step m.twinMove = some (State.twinMap s₁) := by
        rw [← State.twin_step s m, hstep]
        rfl
      show (match (State.twinMap s).step m.twinMove with
        | some st' => st'.run (List.map Move.twinMove rest)
        | none => none) = some (State.twinMap w)
      rw [hrun']
      exact ih s₁ w hrest

/-- The twin swap theorem in solvability: relabeling every card by
its suit twin preserves the verdict. -/
theorem twin_fate (s : State) : WinFrom s ↔ WinFrom (State.twinMap s) := by
  constructor
  · rintro ⟨play, w, hrun, hwin⟩
    rw [← State.isWin_twinMap] at hwin
    exact ⟨play.map Move.twinMove, State.twinMap w, twin_run s play w hrun, hwin⟩
  · rintro ⟨play, w, hrun, hwin⟩
    rw [← State.isWin_twinMap] at hwin
    refine ⟨play.map Move.twinMove, State.twinMap w, ?_, hwin⟩
    have hr := twin_run (State.twinMap s) play w hrun
    rwa [State.twinMap_twinMap s] at hr

/-- The futures reading of `twin_fate`. -/
theorem sameFate_twin (s : State) : sameFate s (s.twinMap) := twin_fate s

/-! ## The twin quotient -/

/-- Positions identified up to the twin swap. -/
instance twinSetoid : Setoid State where
  r a b := a = b ∨ b = State.twinMap a
  iseqv := by
    constructor
    · intro a
      exact Or.inl rfl
    · rintro a b (rfl | h)
      · exact Or.inl rfl
      · exact Or.inr (by
          have hh := congrArg State.twinMap h
          rw [State.twinMap_twinMap a] at hh
          exact hh.symm)
    · rintro a b c (r1 | r2) (s1 | s2)
      · exact Or.inl (r1.trans s1)
      · exact Or.inr (by rw [r1]; exact s2)
      · exact Or.inr (by rw [← s1]; exact r2)
      · refine Or.inl ?_
        rw [s2, r2, State.twinMap_twinMap a]

/-- Positions modulo the twin swap. -/
abbrev TwinQuotient := Quotient twinSetoid

/-- The twin quotient theorem: swap-related positions have the same
verdict — so the quotient carries a well-defined solvability. -/
def WinFromQ (q : TwinQuotient) : Prop :=
  Quotient.lift WinFrom (by
    rintro a b (rfl | h)
    · exact rfl
    · subst h
      exact propext (twin_fate a)) q

theorem twin_quotient (a b : State) (h : a ≈ b) : WinFrom a ↔ WinFrom b := by
  rcases h with rfl | h
  · exact Iff.rfl
  · subst h
    exact twin_fate a
