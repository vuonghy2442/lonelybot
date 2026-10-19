import Orig2.RevSteps
import Orig2.TwinRelabel
import Orig2.StepWF
import Orig2.SeatMateStack

/-!
# Orig2.TwinEquivariance — the both-seated twin-pair relabeling is a step equivalence

This scratch card proves the rider-free, both-seated equivariance subcase of
`fiber_transfer_corrected`: when both `x` and `x.twin` sit face up on the
tableau and neither is covered (rider-free), relabeling every card by the
value transposition `x ↔ x.twin` conjugates every legal move that does not
raise or pull the pair.

No existing file is modified; the development is axiom-clean.
-/

/-! ## §1. The move and base relabelings -/

/-- Relabel the card face of a base. -/
def Base.relabelTwin (x : Card) : Base → Base
  | .inl a => .inl a
  | .inr z => .inr (Card.relabelTwin x z)

/-- Relabel every card value of a move. -/
def Move.relabelTwin (x : Card) : Move → Move
  | .draw => .draw
  | .wasteToFound c => .wasteToFound (Card.relabelTwin x c)
  | .wasteToTab c b => .wasteToTab (Card.relabelTwin x c) (Base.relabelTwin x b)
  | .tabToFound c => .tabToFound (Card.relabelTwin x c)
  | .foundToTab c b => .foundToTab (Card.relabelTwin x c) (Base.relabelTwin x b)
  | .tabToTab c b => .tabToTab (Card.relabelTwin x c) (Base.relabelTwin x b)

@[simp] theorem Base.relabelTwin_inl (x : Card) (a : Anchor) :
    Base.relabelTwin x (Sum.inl a) = Sum.inl a := rfl

@[simp] theorem Base.relabelTwin_inr (x z : Card) :
    Base.relabelTwin x (Sum.inr z) = Sum.inr (Card.relabelTwin x z) := rfl

@[simp] theorem Base.relabelTwin_involutive (x : Card) (b : Base) :
    Base.relabelTwin x (Base.relabelTwin x b) = b := by
  cases b with
  | inl a => rfl
  | inr z => simp [card_relabelTwin_involutive]

@[simp] theorem Move.relabelTwin_involutive (x : Card) (m : Move) :
    Move.relabelTwin x (Move.relabelTwin x m) = m := by
  cases m with
  | draw => rfl
  | wasteToFound c => simp [Move.relabelTwin, card_relabelTwin_involutive]
  | wasteToTab c b => simp [Move.relabelTwin, card_relabelTwin_involutive,
      Base.relabelTwin_involutive]
  | tabToFound c => simp [Move.relabelTwin, card_relabelTwin_involutive]
  | foundToTab c b => simp [Move.relabelTwin, card_relabelTwin_involutive,
      Base.relabelTwin_involutive]
  | tabToTab c b => simp [Move.relabelTwin, card_relabelTwin_involutive,
      Base.relabelTwin_involutive]

/-! ## §2. The card-level arithmetic -/

/-- The pair transposition preserves ranks. -/
theorem Card.relabelTwin_rank (x c : Card) :
    (Card.relabelTwin x c).rank = c.rank := by
  by_cases hc : c = x
  · subst hc
    rw [card_relabelTwin_self]
    rfl
  · by_cases hct : c = x.twin
    · subst hct
      rw [card_relabelTwin_twin]
      rfl
    · rw [card_relabelTwin_ne hc hct]

/-- The pair transposition preserves suit colours. -/
theorem Card.relabelTwin_color (x c : Card) :
    (Card.relabelTwin x c).suit.color = c.suit.color := by
  by_cases hc : c = x
  · rw [hc, card_relabelTwin_self]
    exact Suit.color_twin x.suit
  · by_cases hct : c = x.twin
    · rw [hct, card_relabelTwin_twin]
      exact (Suit.color_twin x.suit).symm
    · rw [card_relabelTwin_ne hc hct]

/-- Twin-card injectivity. -/
theorem card_twin_inj {a b : Card} (h : a.twin = b.twin) : a = b := by
  have := congrArg Card.twin h
  simpa [card_twin_twin] using this

/-- The pair transposition commutes with the twin involution. -/
theorem Card.relabelTwin_twin_comm (x c : Card) :
    (Card.relabelTwin x c).twin = Card.relabelTwin x c.twin := by
  by_cases hc : c = x
  · rw [hc, card_relabelTwin_self, card_twin_twin, card_relabelTwin_twin]
  · by_cases hct : c = x.twin
    · rw [hct, card_relabelTwin_twin, card_twin_twin, card_relabelTwin_self]
    · have htc : c.twin ≠ x := by
        intro hcon
        exact hct (by rw [← card_twin_twin c, hcon])
      have httc : c.twin ≠ x.twin := by
        intro hcon
        exact hc (card_twin_inj hcon)
      rw [card_relabelTwin_ne hc hct, card_relabelTwin_ne htc httc]

/-- The placement fit is blind to the pair transposition. -/
theorem canSitOn_relabelTwin (x c b : Card) :
    canSitOn (Card.relabelTwin x c) (Card.relabelTwin x b) = canSitOn c b := by
  unfold canSitOn
  rw [Card.relabelTwin_rank, Card.relabelTwin_color, Card.relabelTwin_rank,
    Card.relabelTwin_color]

/-- A card fixed by the transposition is off the pair. -/
theorem card_relabelTwin_fixed {x c : Card} (h : Card.relabelTwin x c = c) :
    c ≠ x := by
  intro hc
  rw [hc, card_relabelTwin_self] at h
  exact (card_twin_ne x) h

/-! ## §3. List and pile kit -/

/-- `List.map` by an involution is an involution. -/
theorem list_map_relabelTwin_comp (x : Card) :
    ∀ l : List Card, (l.map (Card.relabelTwin x)).map (Card.relabelTwin x) = l
  | [] => rfl
  | c :: t => by
      simp only [List.map_cons]
      rw [card_relabelTwin_involutive, list_map_relabelTwin_comp x t]

/-- Membership through the involution. -/
theorem mem_map_relabelTwin (x c : Card) (l : List Card) :
    c ∈ l.map (Card.relabelTwin x) ↔ Card.relabelTwin x c ∈ l := by
  constructor
  · intro h
    obtain ⟨d, hd, hdc⟩ := List.mem_map.mp h
    rw [← hdc, card_relabelTwin_involutive]
    exact hd
  · intro h
    exact List.mem_map.mpr ⟨Card.relabelTwin x c, h, card_relabelTwin_involutive x c⟩

/-- `chop` commutes with the transposition. -/
theorem chop_map_relabelTwin (x : Card) :
    ∀ l : List Card, chop (l.map (Card.relabelTwin x)) = (chop l).map (Card.relabelTwin x)
  | [] => rfl
  | [_] => rfl
  | c :: d :: t => by
      show Card.relabelTwin x c :: chop ((d :: t).map (Card.relabelTwin x)) =
        Card.relabelTwin x c :: (chop (d :: t)).map (Card.relabelTwin x)
      rw [chop_map_relabelTwin x (d :: t)]

/-- `lastOf` commutes with the transposition. -/
theorem lastOf_map_relabelTwin (x : Card) :
    ∀ l : List Card, lastOf (l.map (Card.relabelTwin x)) = (lastOf l).map (Card.relabelTwin x)
  | [] => rfl
  | [_] => rfl
  | c :: d :: t => by
      exact lastOf_map_relabelTwin x (d :: t)

/-- `below` commutes with the transposition. -/
theorem below_map_relabelTwin (x c : Card) :
    ∀ l : List Card,
      below (Card.relabelTwin x c) (l.map (Card.relabelTwin x)) =
        (below c l).map (Card.relabelTwin x)
  | [] => rfl
  | d :: t => by
      rw [List.map_cons, below_cons, below_cons]
      by_cases hdc : Card.relabelTwin x d = Card.relabelTwin x c
      · have hd : d = c := by
          have := congrArg (Card.relabelTwin x) hdc
          simpa [card_relabelTwin_involutive] using this
        rw [ite_eq_left hdc, ite_eq_left hd]
        rfl
      · have hd : d ≠ c := by
          intro hcon
          apply hdc
          rw [hcon]
        rw [ite_eq_right hdc, ite_eq_right hd, List.map_cons,
          below_map_relabelTwin x c t]

/-- `fromCard` commutes with the transposition. -/
theorem fromCard_map_relabelTwin (x c : Card) :
    ∀ l : List Card,
      fromCard (Card.relabelTwin x c) (l.map (Card.relabelTwin x)) =
        (fromCard c l).map (Card.relabelTwin x)
  | [] => rfl
  | d :: t => by
      rw [List.map_cons, fromCard, fromCard]
      by_cases hdc : Card.relabelTwin x d = Card.relabelTwin x c
      · have hd : d = c := by
          have := congrArg (Card.relabelTwin x) hdc
          simpa [card_relabelTwin_involutive] using this
        rw [ite_eq_left hdc, ite_eq_left hd]
        rfl
      · have hd : d ≠ c := by
          intro hcon
          apply hdc
          rw [hcon]
        rw [ite_eq_right hdc, ite_eq_right hd,
          fromCard_map_relabelTwin x c t]

/-- A face-up member heads a nonempty `fromCard`. -/
theorem fromCard_ne_nil_of_mem_relabel {c : Card} :
    ∀ {l : List Card}, c ∈ l → fromCard c l ≠ [] := by
  intro l
  induction l with
  | nil => intro h; cases h
  | cons d t ih =>
      intro hmem
      by_cases hdc : d = c
      · rw [fromCard, ite_eq_left hdc]
        exact fun hcon => absurd hcon (by simp)
      · rw [fromCard, ite_eq_right hdc]
        refine ih ?_
        rcases List.mem_cons.mp hmem with h | h
        · exact absurd h.symm hdc
        · exact h

/-! ## §4. The pile relabeling -/

namespace Pile

/-- Relabel every card value in a pile. -/
def relabelTwin (x : Card) (p : Pile) : Pile :=
  { hidden := p.hidden.map (Card.relabelTwin x)
    faceUp := p.faceUp.map (Card.relabelTwin x) }

@[simp] theorem relabelTwin_hidden (x : Card) (p : Pile) :
    (p.relabelTwin x).hidden = p.hidden.map (Card.relabelTwin x) := rfl

@[simp] theorem relabelTwin_faceUp (x : Card) (p : Pile) :
    (p.relabelTwin x).faceUp = p.faceUp.map (Card.relabelTwin x) := rfl

/-- Emptiness is blind to the transposition. -/
theorem isEmpty_relabelTwin (x : Card) (p : Pile) :
    (p.relabelTwin x).isEmpty = p.isEmpty := by
  rcases p with ⟨h, f⟩
  cases h <;> cases f <;> rfl

/-- Revealing the top hidden card commutes with the transposition. -/
theorem revealTop_relabelTwin (x : Card) (p : Pile) :
    (p.relabelTwin x).revealTop = (p.revealTop).relabelTwin x := by
  rcases p with ⟨h, f⟩
  cases h with
  | nil => rfl
  | cons c t =>
      show ({ hidden := t.map (Card.relabelTwin x),
              faceUp := f.map (Card.relabelTwin x) ++ [Card.relabelTwin x c] } : Pile) =
        ({ hidden := t, faceUp := f ++ [c] } : Pile).relabelTwin x
      apply Pile.ext
      · rfl
      · simp only [relabelTwin_faceUp, List.map_append, List.map_cons, List.map_nil]

/-- Removing a run commutes with the transposition. -/
theorem afterRunRemoved_relabelTwin (x : Card) (p : Pile) (pre : List Card) :
    (p.relabelTwin x).afterRunRemoved (pre.map (Card.relabelTwin x)) =
      (p.afterRunRemoved pre).relabelTwin x := by
  cases pre with
  | nil =>
      rcases p with ⟨h, f⟩
      cases h <;> rfl
  | cons y t => rfl

end Pile

@[simp] theorem state_relabelTwin_piles_eq (x : Card) (st : State) (a : Anchor) :
    (State.relabelTwin x st).piles a = (st.piles a).relabelTwin x := rfl

/-! ## §5. Search equivariance -/

/-- Pointwise predicate agreement transports a `firstWhere` search. -/
theorem firstWhere_congr_relabel {α : Type} {p q : α → Bool}
    (h : ∀ a, p a = q a) : ∀ l : List α, firstWhere p l = firstWhere q l
  | [] => rfl
  | a :: t => by
      show (match p a with
            | true => some a
            | false => firstWhere p t) =
           (match q a with
            | true => some a
            | false => firstWhere q t)
      rw [h a]
      cases q a with
      | true => rfl
      | false => exact firstWhere_congr_relabel h t

/-- Option-map equality at the transposition. -/
theorem decide_option_map_relabelTwin (x z : Card) (o : Option Card) :
    decide (o.map (Card.relabelTwin x) = some z) =
      decide (o = some (Card.relabelTwin x z)) := by
  cases o with
  | none => rfl
  | some d =>
      dsimp only [Option.map]
      simp only [Option.some.injEq]
      have hiff : (Card.relabelTwin x d = z) ↔ (d = Card.relabelTwin x z) := by
        constructor
        · intro h
          rw [← h, card_relabelTwin_involutive]
        · intro h
          rw [h, card_relabelTwin_involutive]
      by_cases h : Card.relabelTwin x d = z
      · have h2 : d = Card.relabelTwin x z := hiff.mp h
        rw [decide_eq_true h, decide_eq_true h2]
      · have h2 : d ≠ Card.relabelTwin x z := fun h2 => h (hiff.mpr h2)
        rw [decide_eq_false h, decide_eq_false h2]

/-- The pile-top read transports through the transposition. -/
theorem topOf_relabelTwin (x : Card) (st : State) (a : Anchor) :
    (State.relabelTwin x st).topOf a = (st.topOf a).map (Card.relabelTwin x) := by
  show lastOf ((st.piles a).faceUp.map (Card.relabelTwin x)) =
    (lastOf (st.piles a).faceUp).map (Card.relabelTwin x)
  exact lastOf_map_relabelTwin x _

/-- The top search transports through the transposition. -/
theorem pileOfTop_relabelTwin (x : Card) (st : State) (z : Card) :
    (State.relabelTwin x st).pileOfTop (Card.relabelTwin x z) = st.pileOfTop z := by
  unfold State.pileOfTop
  refine firstWhere_congr_relabel (fun a => ?_) Anchor.all
  rw [topOf_relabelTwin, decide_option_map_relabelTwin x (Card.relabelTwin x z),
    card_relabelTwin_involutive]

/-- A mapped membership reads back the original card. -/
theorem mem_map_relabelTwin_self (x c : Card) (l : List Card) :
    Card.relabelTwin x c ∈ l.map (Card.relabelTwin x) ↔ c ∈ l := by
  rw [mem_map_relabelTwin x (Card.relabelTwin x c) l, card_relabelTwin_involutive]

/-- The holding search transports through the transposition. -/
theorem pileHolding_relabelTwin (x : Card) (st : State) (c : Card) :
    (State.relabelTwin x st).pileHolding (Card.relabelTwin x c) = st.pileHolding c := by
  unfold State.pileHolding
  refine firstWhere_congr_relabel (fun a => ?_) Anchor.all
  show decide (Card.relabelTwin x c ∈ (st.piles a).faceUp.map (Card.relabelTwin x)) =
    decide (c ∈ (st.piles a).faceUp)
  by_cases h : Card.relabelTwin x c ∈ (st.piles a).faceUp.map (Card.relabelTwin x)
  · have h' : c ∈ (st.piles a).faceUp :=
      (mem_map_relabelTwin_self x c (st.piles a).faceUp).mp h
    rw [decide_eq_true h, decide_eq_true h']
  · have h' : c ∉ (st.piles a).faceUp := fun hh =>
      h ((mem_map_relabelTwin_self x c (st.piles a).faceUp).mpr hh)
    rw [decide_eq_false h, decide_eq_false h']

/-- The waste-top guard transports through the transposition. -/
theorem wasteIs_relabelTwin (x : Card) (st : State) (c : Card) :
    (State.relabelTwin x st).wasteIs (Card.relabelTwin x c) = st.wasteIs c := by
  unfold State.wasteIs
  rw [state_relabelTwin_waste]
  cases st.waste with
  | nil => rfl
  | cons d t =>
      simp only [List.map_cons]
      have hdec : decide (Card.relabelTwin x d = Card.relabelTwin x c) = decide (d = c) := by
        by_cases hdc : d = c
        · rw [decide_eq_true hdc, decide_eq_true (by rw [hdc])]
        · have hne : Card.relabelTwin x d ≠ Card.relabelTwin x c :=
            fun hcon => hdc (card_relabelTwin_injective x hcon)
          rw [decide_eq_false hdc, decide_eq_false hne]
      rw [hdec]

/-- The foundation-top read transports through the transposition. -/
theorem foundTop_relabelTwin (x : Card) (st : State) (s : Suit) :
    (State.relabelTwin x st).foundTop s =
      (st.foundTop s).map (Card.relabelTwin x) := by
  show lastOf ((st.found s).map (Card.relabelTwin x)) =
    (lastOf (st.found s)).map (Card.relabelTwin x)
  exact lastOf_map_relabelTwin x _

/-- The foundation-height read is invariant. -/
theorem foundHeight_relabelTwin (x : Card) (st : State) (s : Suit) :
    (State.relabelTwin x st).foundHeight s = st.foundHeight s := by
  unfold State.foundHeight
  rw [state_relabelTwin_found, List.length_map]

/-- The foundation-advance guard is invariant. -/
theorem nextUp_relabelTwin (x : Card) (st : State) (c : Card) :
    (State.relabelTwin x st).nextUp c = st.nextUp c := by
  unfold State.nextUp
  rw [foundHeight_relabelTwin]

/-- Placement legality transports through the transposition. -/
theorem canPlace_relabelTwin (x : Card) (st : State) (c : Card) (b : Base) :
    (State.relabelTwin x st).canPlace (Card.relabelTwin x c) (Base.relabelTwin x b) =
      st.canPlace c b := by
  cases b with
  | inl a =>
      simp only [State.canPlace, Base.relabelTwin_inl, state_relabelTwin_piles_eq,
        Pile.isEmpty_relabelTwin, Card.relabelTwin_rank]
  | inr z =>
      show (match (State.relabelTwin x st).pileOfTop (Card.relabelTwin x z) with
            | some _ => canSitOn (Card.relabelTwin x c) (Card.relabelTwin x z)
            | none => false) =
        (match st.pileOfTop z with
         | some _ => canSitOn c z
         | none => false)
      rw [pileOfTop_relabelTwin]
      cases st.pileOfTop z with
      | none => rfl
      | some k => rw [canSitOn_relabelTwin]

/-! ## §6. Update commutation -/

@[simp] theorem state_relabelTwin_with_stock (x : Card) (st : State) (l : List Card) :
    State.relabelTwin x { st with stock := l } =
      { State.relabelTwin x st with stock := l.map (Card.relabelTwin x) } := rfl

@[simp] theorem state_relabelTwin_with_waste (x : Card) (st : State) (l : List Card) :
    State.relabelTwin x { st with waste := l } =
      { State.relabelTwin x st with waste := l.map (Card.relabelTwin x) } := rfl

@[simp] theorem state_relabelTwin_with_drawStep (x : Card) (st : State) (n : Nat) :
    State.relabelTwin x { st with drawStep := n } =
      { State.relabelTwin x st with drawStep := n } := rfl

/-- A foundation write commutes with the transposition. -/
theorem setFound_relabelTwin (x : Card) (st : State) (s : Suit) (l : List Card) :
    State.relabelTwin x (st.setFound s l) =
      (State.relabelTwin x st).setFound s (l.map (Card.relabelTwin x)) := by
  apply State.ext
  · funext s'
    show (if s' = s then l else st.found s').map (Card.relabelTwin x) =
      if s' = s then l.map (Card.relabelTwin x) else (st.found s').map (Card.relabelTwin x)
    by_cases h : s' = s
    · rw [ite_eq_left h, ite_eq_left h]
    · rw [ite_eq_right h, ite_eq_right h]
  · rfl
  · rfl
  · rfl
  · rfl

/-- A pile write commutes with the transposition. -/
theorem setPile_relabelTwin (x : Card) (st : State) (a : Anchor) (p : Pile) :
    State.relabelTwin x (st.setPile a p) =
      (State.relabelTwin x st).setPile a (p.relabelTwin x) := by
  apply State.ext
  · rfl
  · funext a'
    show (if a' = a then p else st.piles a').relabelTwin x =
      if a' = a then p.relabelTwin x else (st.piles a').relabelTwin x
    by_cases h : a' = a
    · rw [ite_eq_left h, ite_eq_left h]
    · rw [ite_eq_right h, ite_eq_right h]
  · rfl
  · rfl
  · rfl

/-- `putCard` commutes with the transposition. -/
theorem putCard_relabelTwin (x : Card) (st : State) (c : Card) (b : Base) :
    State.relabelTwin x (st.putCard c b) =
      (State.relabelTwin x st).putCard (Card.relabelTwin x c) (Base.relabelTwin x b) := by
  cases b with
  | inl a =>
      rw [putCard_eq_inl, show Base.relabelTwin x (Sum.inl a) = Sum.inl a from rfl,
        putCard_eq_inl, setPile_relabelTwin]
      rfl
  | inr z =>
      rw [show Base.relabelTwin x (Sum.inr z) = Sum.inr (Card.relabelTwin x z) from rfl]
      cases h : st.pileOfTop z with
      | none =>
          have hL : st.putCard c (Sum.inr z) = st := by
            simp only [State.putCard, h]
          have hR : (State.relabelTwin x st).putCard (Card.relabelTwin x c)
              (Sum.inr (Card.relabelTwin x z)) = State.relabelTwin x st := by
            simp only [State.putCard, pileOfTop_relabelTwin, h]
          rw [hL, hR]
      | some k =>
          have hL : st.putCard c (Sum.inr z) =
              st.setPile k { st.piles k with faceUp := (st.piles k).faceUp ++ [c] } :=
            putCard_inr_eq h
          have hR : (State.relabelTwin x st).putCard (Card.relabelTwin x c)
              (Sum.inr (Card.relabelTwin x z)) =
              (State.relabelTwin x st).setPile k
                { (State.relabelTwin x st).piles k with
                  faceUp := ((State.relabelTwin x st).piles k).faceUp ++ [Card.relabelTwin x c] } :=
            putCard_inr_eq (by rw [pileOfTop_relabelTwin]; exact h)
          rw [hL, hR, setPile_relabelTwin]
          congr 1
          apply Pile.ext
          · rfl
          · simp only [state_relabelTwin_piles_eq, Pile.relabelTwin_faceUp, List.map_append,
              List.map_cons, List.map_nil]

/-- `putRun` commutes with the transposition. -/
theorem putRun_relabelTwin (x : Card) (st : State) (run : List Card) (b : Base) :
    State.relabelTwin x (st.putRun run b) =
      (State.relabelTwin x st).putRun (run.map (Card.relabelTwin x)) (Base.relabelTwin x b) := by
  cases b with
  | inl a =>
      rw [putRun_eq_inl, show Base.relabelTwin x (Sum.inl a) = Sum.inl a from rfl,
        putRun_eq_inl, setPile_relabelTwin]
      rfl
  | inr z =>
      rw [show Base.relabelTwin x (Sum.inr z) = Sum.inr (Card.relabelTwin x z) from rfl]
      cases h : st.pileOfTop z with
      | none =>
          have hL : st.putRun run (Sum.inr z) = st := by
            simp only [State.putRun, h]
          have hR : (State.relabelTwin x st).putRun (run.map (Card.relabelTwin x))
              (Sum.inr (Card.relabelTwin x z)) = State.relabelTwin x st := by
            simp only [State.putRun, pileOfTop_relabelTwin, h]
          rw [hL, hR]
      | some k =>
          have hL : st.putRun run (Sum.inr z) =
              st.setPile k { st.piles k with faceUp := (st.piles k).faceUp ++ run } :=
            putRun_inr_eq h
          have hR : (State.relabelTwin x st).putRun (run.map (Card.relabelTwin x))
              (Sum.inr (Card.relabelTwin x z)) =
              (State.relabelTwin x st).setPile k
                { (State.relabelTwin x st).piles k with
                  faceUp := ((State.relabelTwin x st).piles k).faceUp ++ run.map (Card.relabelTwin x) } :=
            putRun_inr_eq (by rw [pileOfTop_relabelTwin]; exact h)
          rw [hL, hR, setPile_relabelTwin]
          congr 1
          apply Pile.ext
          · rfl
          · simp only [state_relabelTwin_piles_eq, Pile.relabelTwin_faceUp, List.map_append]

/-- The pile-removal update with a mapped prefix. -/
theorem afterRunRemoved_piles_relabelTwin (x : Card) (st : State) (a : Anchor)
    (pre : List Card) :
    ((State.relabelTwin x st).piles a).afterRunRemoved (pre.map (Card.relabelTwin x)) =
      ((st.piles a).afterRunRemoved pre).relabelTwin x :=
  Pile.afterRunRemoved_relabelTwin x (st.piles a) pre
/-! ## §7. The pair sits outside every non-tableau zone -/

/-- A seated card lies face up in some pile. -/
private theorem mem_faceUp_of_seat_relabel {st : State} {c : Card} {b : Base}
    (h : seatOf st c = some b) : ∃ a, c ∈ (st.piles a).faceUp := by
  unfold seatOf at h
  cases hh : st.pileHolding c with
  | none =>
      rw [hh] at h
      exact absurd h (by simp)
  | some a => exact ⟨a, pileHolding_mem hh⟩

/-- A face-up card is absent from every hidden deck, the stock, the waste,
and every foundation (the `off_zones_of_seat` restatement). -/
private theorem off_zones_of_seat_relabel {st : State} (hwf : st.WF) {c : Card}
    (hse : ∃ b, seatOf st c = some b) :
    (∀ a, c ∉ (st.piles a).hidden) ∧ c ∉ st.stock ∧ c ∉ st.waste ∧
      ∀ s, c ∉ st.found s := by
  obtain ⟨b, hb⟩ := hse
  obtain ⟨a, hmem⟩ := mem_faceUp_of_seat_relabel hb
  obtain ⟨hother, hown, hstock, hwaste, hfound⟩ := mem_faceUp_only hwf hmem
  refine ⟨?_, hstock, hwaste, hfound⟩
  intro a'
  by_cases ha : a' = a
  · subst ha
    exact hown
  · exact (hother a' ha).1

/-- A list all of whose entries are fixed by `f` is unchanged by `List.map f`. -/
private theorem map_eq_self_generic {α : Type} (f : α → α) :
    ∀ {l : List α}, (∀ a ∈ l, f a = a) → l.map f = l
  | [], _ => rfl
  | a :: t, h => by
      rw [List.map_cons, h a (by simp)]
      exact congrArg (a :: ·) (map_eq_self_generic f (fun b hb => h b (by simp [hb])))

/-- At a both-seated `WF` state the foundations are untouched by the pair
transposition. -/
theorem state_relabelTwin_found_eq {st : State} {x : Card} (hwf : st.WF)
    (hx : ∃ b, seatOf st x = some b) (hxt : ∃ b, seatOf st x.twin = some b)
    (s : Suit) :
    (State.relabelTwin x st).found s = st.found s := by
  obtain ⟨-, -, -, hxfo⟩ := off_zones_of_seat_relabel hwf hx
  obtain ⟨-, -, -, hxtfo⟩ := off_zones_of_seat_relabel hwf hxt
  simp only [state_relabelTwin_found]
  exact map_eq_self_generic (Card.relabelTwin x) (fun c hc =>
    card_relabelTwin_ne (fun h => hxfo s (h ▸ hc)) (fun h => hxtfo s (h ▸ hc)))

/-- At a both-seated `WF` state the hidden decks are untouched. -/
theorem state_relabelTwin_hidden_eq {st : State} {x : Card} (hwf : st.WF)
    (hx : ∃ b, seatOf st x = some b) (hxt : ∃ b, seatOf st x.twin = some b)
    (a : Anchor) :
    ((State.relabelTwin x st).piles a).hidden = (st.piles a).hidden := by
  obtain ⟨hxhid, -, -, -⟩ := off_zones_of_seat_relabel hwf hx
  obtain ⟨hxthid, -, -, -⟩ := off_zones_of_seat_relabel hwf hxt
  simp only [state_relabelTwin_piles_hidden]
  exact map_eq_self_generic (Card.relabelTwin x) (fun c hc =>
    card_relabelTwin_ne (fun h => hxhid a (h ▸ hc)) (fun h => hxthid a (h ▸ hc)))

/-- At a both-seated `WF` state the stock is untouched. -/
theorem state_relabelTwin_stock_eq {st : State} {x : Card} (hwf : st.WF)
    (hx : ∃ b, seatOf st x = some b) (hxt : ∃ b, seatOf st x.twin = some b) :
    (State.relabelTwin x st).stock = st.stock := by
  obtain ⟨-, hxst, -, -⟩ := off_zones_of_seat_relabel hwf hx
  obtain ⟨-, hxtst, -, -⟩ := off_zones_of_seat_relabel hwf hxt
  simp only [state_relabelTwin_stock]
  exact map_eq_self_generic (Card.relabelTwin x) (fun c hc =>
    card_relabelTwin_ne (fun h => hxst (h ▸ hc)) (fun h => hxtst (h ▸ hc)))

/-- At a both-seated `WF` state the waste is untouched. -/
theorem state_relabelTwin_waste_eq {st : State} {x : Card} (hwf : st.WF)
    (hx : ∃ b, seatOf st x = some b) (hxt : ∃ b, seatOf st x.twin = some b) :
    (State.relabelTwin x st).waste = st.waste := by
  obtain ⟨-, -, hxwa, -⟩ := off_zones_of_seat_relabel hwf hx
  obtain ⟨-, -, hxtwa, -⟩ := off_zones_of_seat_relabel hwf hxt
  simp only [state_relabelTwin_waste]
  exact map_eq_self_generic (Card.relabelTwin x) (fun c hc =>
    card_relabelTwin_ne (fun h => hxwa (h ▸ hc)) (fun h => hxtwa (h ▸ hc)))
/-! ## §8. The draw pipeline -/

/-- Dealing commutes with any card map. -/
theorem dealUpTo_map_relabel (x : Card) (k : Nat) (l : List Card) :
    State.dealUpTo k (l.map (Card.relabelTwin x)) =
      ((State.dealUpTo k l).1.map (Card.relabelTwin x),
       (State.dealUpTo k l).2.map (Card.relabelTwin x)) := by
  induction k generalizing l with
  | zero => rfl
  | succ n ih =>
      cases l with
      | nil => rfl
      | cons c cs =>
          show (Card.relabelTwin x c ::
              (State.dealUpTo n (cs.map (Card.relabelTwin x))).1,
            (State.dealUpTo n (cs.map (Card.relabelTwin x))).2) =
            (Card.relabelTwin x c :: ((State.dealUpTo n cs).1.map (Card.relabelTwin x)),
             (State.dealUpTo n cs).2.map (Card.relabelTwin x))
          rw [ih]

/-- Recycling commutes with the transposition, given that the source's
stock and waste are fixed by it. -/
theorem recycle_relabelTwin (x : Card) (st : State)
    (hstock : (State.relabelTwin x st).stock = st.stock)
    (hwaste : (State.relabelTwin x st).waste = st.waste) :
    State.recycle (State.relabelTwin x st) =
      State.relabelTwin x (State.recycle st) := by
  have hwmap : st.waste.map (Card.relabelTwin x) = st.waste := by
    rw [← state_relabelTwin_waste]
    exact hwaste
  unfold State.recycle
  rw [hstock, hwaste]
  cases hs : st.stock with
  | nil =>
      cases hw : st.waste with
      | nil => rfl
      | cons w ws =>
          apply State.ext
          · rfl
          · rfl
          · show (w :: ws).reverse = ((w :: ws).reverse).map (Card.relabelTwin x)
            have hwfix : (w :: ws).map (Card.relabelTwin x) = w :: ws := by
              rw [← hw]
              exact hwmap
            rw [List.map_reverse, hwfix]
          · rfl
          · rfl
  | cons s ss => rfl

/-- Dealing from a fixed stock/waste commutes with the transposition. -/
theorem dealStock_relabelTwin (x : Card) (u : State)
    (hfound : ∀ s, (State.relabelTwin x u).found s = u.found s)
    (hstock : (State.relabelTwin x u).stock = u.stock)
    (hwaste : (State.relabelTwin x u).waste = u.waste)
    (hdraw : (State.relabelTwin x u).drawStep = u.drawStep) :
    State.dealStock (State.relabelTwin x u) =
      (State.dealStock u).map (State.relabelTwin x) := by
  have hstockfix : u.stock.map (Card.relabelTwin x) = u.stock := by
    rw [← state_relabelTwin_stock]
    exact hstock
  have hwastefix : u.waste.map (Card.relabelTwin x) = u.waste := by
    rw [← state_relabelTwin_waste]
    exact hwaste
  cases hs : u.stock with
  | nil =>
      have hsn : (State.relabelTwin x u).stock = [] := by rw [hstock, hs]
      rw [show State.dealStock (State.relabelTwin x u) = none by
            simp only [State.dealStock, hsn],
        show State.dealStock u = none by simp only [State.dealStock, hs]]
      rfl
  | cons c cs =>
      have hsn : (State.relabelTwin x u).stock = c :: cs := by rw [hstock, hs]
      have hsnne : (State.relabelTwin x u).stock ≠ [] := by rw [hsn]; simp
      have hune : u.stock ≠ [] := by rw [hs]; simp
      rw [dealStock_eq_of_ne_nil (State.relabelTwin x u) hsnne,
        dealStock_eq_of_ne_nil u hune, hdraw, hsn, hs,
        Option.map_some, Option.some.injEq]
      have hdeal := dealUpTo_map_relabel x u.drawStep (c :: cs)
      have hcfix : (c :: cs).map (Card.relabelTwin x) = c :: cs := by
        rw [← hs]
        exact hstockfix
      rw [hcfix] at hdeal
      have h1 : (State.dealUpTo u.drawStep (c :: cs)).1 =
          (State.dealUpTo u.drawStep (c :: cs)).1.map (Card.relabelTwin x) := by
        have := congrArg Prod.fst hdeal
        simpa using this
      have h2 : (State.dealUpTo u.drawStep (c :: cs)).2 =
          (State.dealUpTo u.drawStep (c :: cs)).2.map (Card.relabelTwin x) := by
        have := congrArg Prod.snd hdeal
        simpa using this
      have hrev : ((State.dealUpTo u.drawStep (c :: cs)).1.reverse).map
          (Card.relabelTwin x) =
          (State.dealUpTo u.drawStep (c :: cs)).1.reverse := by
        rw [List.map_reverse, ← h1]
      have hfs : ∀ s, (u.found s).map (Card.relabelTwin x) = u.found s := by
        intro s
        rw [← state_relabelTwin_found]
        exact hfound s
      apply State.ext
      · funext s
        show (State.relabelTwin x u).found s =
          (u.found s).map (Card.relabelTwin x)
        rw [hfs, hfound]
      · funext a
        rfl
      · show (State.dealUpTo u.drawStep (c :: cs)).2 =
          ((State.dealUpTo u.drawStep (c :: cs)).2).map (Card.relabelTwin x)
        exact h2
      · show (State.dealUpTo u.drawStep (c :: cs)).1.reverse ++
            (State.relabelTwin x u).waste =
          ((State.dealUpTo u.drawStep (c :: cs)).1.reverse ++ u.waste).map
            (Card.relabelTwin x)
        rw [List.map_append, hrev, hwastefix, hwaste]
      · rfl
/-! ## §9. The draw step -/

/-- Recycling keeps the foundations. -/
private theorem recycle_found_relabel (st : State) (s : Suit) :
    (State.recycle st).found s = st.found s := by
  by_cases hs : st.stock = []
  · by_cases hw : st.waste = []
    · rw [recycle_allEmpty _ hs hw]
    · rw [recycle_nil _ hs hw]
  · rw [recycle_keep _ hs]

/-- Recycling keeps the draw step. -/
private theorem recycle_drawStep_relabel (st : State) :
    (State.recycle st).drawStep = st.drawStep := by
  by_cases hs : st.stock = []
  · by_cases hw : st.waste = []
    · rw [recycle_allEmpty _ hs hw]
    · rw [recycle_nil _ hs hw]
  · rw [recycle_keep _ hs]

/-- Recycling keeps a transposition-fixed stock fixed. -/
private theorem recycle_stock_fix (x : Card) (st : State)
    (hstockfix : st.stock.map (Card.relabelTwin x) = st.stock)
    (hwastefix : st.waste.map (Card.relabelTwin x) = st.waste) :
    (State.recycle st).stock.map (Card.relabelTwin x) = (State.recycle st).stock := by
  by_cases hs : st.stock = []
  · by_cases hw : st.waste = []
    · rw [recycle_allEmpty _ hs hw]
      exact hstockfix
    · rw [recycle_nil _ hs hw]
      show (st.waste.reverse).map (Card.relabelTwin x) = st.waste.reverse
      rw [List.map_reverse, hwastefix]
  · rw [recycle_keep _ hs]
    exact hstockfix

/-- Recycling keeps a transposition-fixed waste fixed. -/
private theorem recycle_waste_fix (x : Card) (st : State)
    (hwastefix : st.waste.map (Card.relabelTwin x) = st.waste) :
    (State.recycle st).waste.map (Card.relabelTwin x) = (State.recycle st).waste := by
  by_cases hs : st.stock = []
  · by_cases hw : st.waste = []
    · rw [recycle_allEmpty _ hs hw]
      exact hwastefix
    · rw [recycle_nil _ hs hw]
      rfl
  · rw [recycle_keep _ hs]
    exact hwastefix
/-- The draw step commutes with the transposition at a both-seated `WF` state. -/
theorem stepDraw_relabelTwin {st st' : State} {x : Card} (hwf : st.WF)
    (hx : ∃ b, seatOf st x = some b) (hxt : ∃ b, seatOf st x.twin = some b)
    (hstep : st.stepDraw = some st') :
    (State.relabelTwin x st).stepDraw = some (State.relabelTwin x st') := by
  have hfound := state_relabelTwin_found_eq hwf hx hxt
  have hstock := state_relabelTwin_stock_eq hwf hx hxt
  have hwaste := state_relabelTwin_waste_eq hwf hx hxt
  have hstockfix : st.stock.map (Card.relabelTwin x) = st.stock := by
    rw [← state_relabelTwin_stock]
    exact hstock
  have hwastefix : st.waste.map (Card.relabelTwin x) = st.waste := by
    rw [← state_relabelTwin_waste]
    exact hwaste
  have hfs : ∀ s, (st.found s).map (Card.relabelTwin x) = st.found s := by
    intro s
    rw [← state_relabelTwin_found]
    exact hfound s
  have hrec := recycle_relabelTwin x st hstock hwaste
  have hstep' : State.dealStock (State.recycle st) = some st' := hstep
  rw [show (State.relabelTwin x st).stepDraw =
        State.dealStock (State.recycle (State.relabelTwin x st)) from rfl, hrec]
  rw [dealStock_relabelTwin x (State.recycle st)
    (fun s => by
      rw [state_relabelTwin_found, recycle_found_relabel]
      exact hfs s)
    (by
      rw [state_relabelTwin_stock]
      exact recycle_stock_fix x st hstockfix hwastefix)
    (by
      rw [state_relabelTwin_waste]
      exact recycle_waste_fix x st hwastefix)
    (by
      rw [state_relabelTwin_drawStep, recycle_drawStep_relabel])]
  rw [hstep', Option.map_some]

/-! ## §10. The excluded pair-foundation letters -/

/-- The four pair-foundation moves excluded from the equivariance play:
raising either twin, or pulling either twin. -/
def NotFoundPair (x : Card) (m : Move) : Prop :=
  m ≠ Move.tabToFound x ∧ m ≠ Move.tabToFound x.twin ∧
    (∀ b, m ≠ Move.foundToTab x b) ∧ (∀ b, m ≠ Move.foundToTab x.twin b)

/-- A list all of whose cards are off the pair is fixed by the transposition. -/
private theorem map_eq_self_off (x : Card) {l : List Card}
    (h : ∀ c ∈ l, c ≠ x ∧ c ≠ x.twin) : l.map (Card.relabelTwin x) = l :=
  map_eq_self_generic (Card.relabelTwin x) (fun c hc =>
    card_relabelTwin_ne (h c hc).1 (h c hc).2)

/-- The step commutation at a move that does not raise or pull either twin. -/
theorem step_comm_of_not_foundPair {st st' : State} {x : Card} {m : Move}
    (hwf : st.WF)
    (hx : ∃ b, seatOf st x = some b)
    (hxt : ∃ b, seatOf st x.twin = some b)
    (hstep : State.step st m = some st')
    (hno : NotFoundPair x m) :
    State.step (State.relabelTwin x st) (Move.relabelTwin x m) = some (State.relabelTwin x st') := by
  obtain ⟨hxhid, hxst, hxwa, hxfo⟩ := off_zones_of_seat_relabel hwf hx
  obtain ⟨hxthid, hxtst, hxtwa, hxtfo⟩ := off_zones_of_seat_relabel hwf hxt
  have hfound := state_relabelTwin_found_eq hwf hx hxt
  have hhidden := state_relabelTwin_hidden_eq hwf hx hxt
  have hstock := state_relabelTwin_stock_eq hwf hx hxt
  have hwaste := state_relabelTwin_waste_eq hwf hx hxt
  have hstockfix : st.stock.map (Card.relabelTwin x) = st.stock := by
    rw [← state_relabelTwin_stock]
    exact hstock
  have hwastefix : st.waste.map (Card.relabelTwin x) = st.waste := by
    rw [← state_relabelTwin_waste]
    exact hwaste
  have hfs : ∀ s, (st.found s).map (Card.relabelTwin x) = st.found s := by
    intro s
    rw [← state_relabelTwin_found]
    exact hfound s
  cases m with
  | draw => exact stepDraw_relabelTwin hwf hx hxt hstep
  | wasteToFound c =>
      obtain ⟨hguard, xh, xs, hw, hs⟩ := step_wasteToFound_inv hstep
      rw [Bool.and_eq_true] at hguard
      obtain ⟨hwis, hnext⟩ := hguard
      have hxc : xh = c := State.wasteIs_head_eq hw hwis
      have hw' : st.waste = c :: xs := by rw [hw, hxc]
      have hxsmem : ∀ y ∈ xs, y ∈ st.waste := by
        intro y hy
        rw [hw']
        exact List.mem_cons_of_mem c hy
      have hxsfix : xs.map (Card.relabelTwin x) = xs :=
        map_eq_self_off x (fun y hy => ⟨
          fun hyx => hxwa (by rw [← hyx]; exact hxsmem y hy),
          fun hyt => hxtwa (by rw [← hyt]; exact hxsmem y hy)⟩)
      have hcx : c ≠ x := fun h => hxwa (by rw [hw', h]; simp)
      have hct : c ≠ x.twin := fun h => hxtwa (by rw [hw', h]; simp)
      have hτc : Card.relabelTwin x c = c := card_relabelTwin_ne hcx hct
      have hnextτ : (State.relabelTwin x st).nextUp (Card.relabelTwin x c) = true := by
        rw [hτc, nextUp_relabelTwin]
        exact hnext
      have hwisτ : (State.relabelTwin x st).wasteIs (Card.relabelTwin x c) = true := by
        rw [wasteIs_relabelTwin]
        exact hwis
      have hwasteτ : (State.relabelTwin x st).waste = Card.relabelTwin x c :: xs := by
        rw [hwaste, hw', hτc]
      change State.step (State.relabelTwin x st) (Move.wasteToFound (Card.relabelTwin x c)) =
        some (State.relabelTwin x st')
      rw [show State.step (State.relabelTwin x st) (Move.wasteToFound (Card.relabelTwin x c)) =
            some { (State.relabelTwin x st).setFound (Card.relabelTwin x c).suit
                     ((State.relabelTwin x st).found (Card.relabelTwin x c).suit ++
                       [Card.relabelTwin x c]) with waste := xs } by
            simp only [State.step]
            rw [hwasteτ]
            simp [hwisτ, hnextτ]]
      rw [hτc]
      apply congrArg some
      rw [hs]
      dsimp only
      apply State.ext
      · funext s'
        by_cases h : s' = c.suit
        · subst h
          show ((State.relabelTwin x st).setFound c.suit
              ((State.relabelTwin x st).found c.suit ++ [c])).found c.suit =
            ((st.setFound c.suit (st.found c.suit ++ [c])).found c.suit).map
              (Card.relabelTwin x)
          simp only [setFound_found_self, List.map_append, List.map_cons, List.map_nil,
            hfs, hτc, state_relabelTwin_found]
        · show ((State.relabelTwin x st).setFound c.suit
              ((State.relabelTwin x st).found c.suit ++ [c])).found s' =
            ((st.setFound c.suit (st.found c.suit ++ [c])).found s').map
              (Card.relabelTwin x)
          rw [setFound_found_ne h, setFound_found_ne h, state_relabelTwin_found]
      · funext a'
        rfl
      · rfl
      · show xs = xs.map (Card.relabelTwin x)
        exact hxsfix.symm
      · rfl
  | wasteToTab c b =>
      obtain ⟨hguard, xh, xs, hw, hs⟩ := step_wasteToTab_inv hstep
      rw [Bool.and_eq_true] at hguard
      obtain ⟨hwis, hcp⟩ := hguard
      have hxc : xh = c := State.wasteIs_head_eq hw hwis
      have hw' : st.waste = c :: xs := by rw [hw, hxc]
      have hxsmem : ∀ y ∈ xs, y ∈ st.waste := by
        intro y hy
        rw [hw']
        exact List.mem_cons_of_mem c hy
      have hxsfix : xs.map (Card.relabelTwin x) = xs :=
        map_eq_self_off x (fun y hy => ⟨
          fun hyx => hxwa (by rw [← hyx]; exact hxsmem y hy),
          fun hyt => hxtwa (by rw [← hyt]; exact hxsmem y hy)⟩)
      have hcx : c ≠ x := fun h => hxwa (by rw [hw', h]; simp)
      have hct : c ≠ x.twin := fun h => hxtwa (by rw [hw', h]; simp)
      have hτc : Card.relabelTwin x c = c := card_relabelTwin_ne hcx hct
      have hwisτ : (State.relabelTwin x st).wasteIs (Card.relabelTwin x c) = true := by
        rw [wasteIs_relabelTwin]
        exact hwis
      have hcpτ : (State.relabelTwin x st).canPlace (Card.relabelTwin x c)
          (Base.relabelTwin x b) = true := by
        rw [canPlace_relabelTwin]
        exact hcp
      have hwasteτ : (State.relabelTwin x st).waste = Card.relabelTwin x c :: xs := by
        rw [hwaste, hw', hτc]
      change State.step (State.relabelTwin x st)
          (Move.wasteToTab (Card.relabelTwin x c) (Base.relabelTwin x b)) =
        some (State.relabelTwin x st')
      rw [show State.step (State.relabelTwin x st)
            (Move.wasteToTab (Card.relabelTwin x c) (Base.relabelTwin x b)) =
            some { (State.relabelTwin x st).putCard (Card.relabelTwin x c)
                     (Base.relabelTwin x b) with waste := xs } by
            simp only [State.step]
            rw [hwasteτ]
            simp [hwisτ, hcpτ]]
      rw [hτc]
      apply congrArg some
      rw [hs]
      dsimp only
      apply State.ext
      · funext s'
        show ((State.relabelTwin x st).putCard c (Base.relabelTwin x b)).found s' =
          ((st.putCard c b).found s').map (Card.relabelTwin x)
        rw [putCard_found (State.relabelTwin x st) c (Base.relabelTwin x b),
          putCard_found st c b]
        rfl
      · funext a'
        show ((State.relabelTwin x st).putCard c (Base.relabelTwin x b)).piles a' =
          ((st.putCard c b).piles a').relabelTwin x
        have hp := congrArg State.piles (putCard_relabelTwin x st c b)
        rw [hτc] at hp
        exact (congrFun hp a').symm
      · show ((State.relabelTwin x st).putCard c (Base.relabelTwin x b)).stock =
          (st.putCard c b).stock.map (Card.relabelTwin x)
        rw [putCard_stock (State.relabelTwin x st) c (Base.relabelTwin x b),
          putCard_stock st c b]
        rfl
      · show xs = xs.map (Card.relabelTwin x)
        exact hxsfix.symm
      · show ((State.relabelTwin x st).putCard c (Base.relabelTwin x b)).drawStep =
          (st.putCard c b).drawStep
        rw [putCard_drawStep (State.relabelTwin x st) c (Base.relabelTwin x b),
          putCard_drawStep st c b]
        rfl
  | tabToFound c =>
      obtain ⟨hnext, ain, hp, hs⟩ := step_tabToFound_inv hstep
      have hcx : c ≠ x := fun h => hno.1 (by rw [h])
      have hct : c ≠ x.twin := fun h => hno.2.1 (by rw [h])
      have hτc : Card.relabelTwin x c = c := card_relabelTwin_ne hcx hct
      have hnextτ : (State.relabelTwin x st).nextUp (Card.relabelTwin x c) = true := by
        rw [hτc, nextUp_relabelTwin]
        exact hnext
      have hpτ : (State.relabelTwin x st).pileOfTop (Card.relabelTwin x c) = some ain := by
        rw [pileOfTop_relabelTwin]
        exact hp
      change State.step (State.relabelTwin x st) (Move.tabToFound (Card.relabelTwin x c)) =
        some (State.relabelTwin x st')
      rw [show State.step (State.relabelTwin x st) (Move.tabToFound (Card.relabelTwin x c)) =
            some { (State.relabelTwin x st).setFound (Card.relabelTwin x c).suit
                     ((State.relabelTwin x st).found (Card.relabelTwin x c).suit ++
                       [Card.relabelTwin x c]) with
                   piles := fun a' => if a' = ain then
                       Pile.afterRunRemoved ((State.relabelTwin x st).piles ain)
                         (chop ((State.relabelTwin x st).piles ain).faceUp)
                     else (State.relabelTwin x st).piles a' } by
            simp only [State.step]
            rw [hnextτ, hpτ]
            simp]
      rw [hτc]
      apply congrArg some
      rw [hs]
      dsimp only
      apply State.ext
      · funext s'
        by_cases h : s' = c.suit
        · subst h
          show ((State.relabelTwin x st).setFound c.suit
              ((State.relabelTwin x st).found c.suit ++ [c])).found c.suit =
            ((st.setFound c.suit (st.found c.suit ++ [c])).found c.suit).map
              (Card.relabelTwin x)
          simp only [setFound_found_self, List.map_append, List.map_cons, List.map_nil,
            hfs, hτc, state_relabelTwin_found]
        · show ((State.relabelTwin x st).setFound c.suit
              ((State.relabelTwin x st).found c.suit ++ [c])).found s' =
            ((st.setFound c.suit (st.found c.suit ++ [c])).found s').map
              (Card.relabelTwin x)
          rw [setFound_found_ne h, setFound_found_ne h, state_relabelTwin_found]
      · funext a'
        show (if a' = ain then
            Pile.afterRunRemoved ((State.relabelTwin x st).piles ain)
              (chop ((State.relabelTwin x st).piles ain).faceUp)
          else (State.relabelTwin x st).piles a') =
          (if a' = ain then
            Pile.afterRunRemoved (st.piles ain) (chop (st.piles ain).faceUp)
          else st.piles a').relabelTwin x
        by_cases h : a' = ain
        · rw [← h]
          rw [ite_eq_left rfl, ite_eq_left rfl, state_relabelTwin_piles_eq,
            Pile.relabelTwin_faceUp, chop_map_relabelTwin]
          exact Pile.afterRunRemoved_relabelTwin x (st.piles a')
            (chop (st.piles a').faceUp)
        · rw [ite_eq_right h, ite_eq_right h, state_relabelTwin_piles_eq]
      · rfl
      · rfl
      · rfl
  | foundToTab c b =>
      obtain ⟨c', htop, hc'c, hcp, hs⟩ := step_foundToTab_inv hstep
      have hcx : c ≠ x := fun h => hno.2.2.1 b (by rw [h])
      have hct : c ≠ x.twin := fun h => hno.2.2.2 b (by rw [h])
      have hτc : Card.relabelTwin x c = c := card_relabelTwin_ne hcx hct
      have htopτ : (State.relabelTwin x st).foundTop c.suit = some c := by
        rw [foundTop_relabelTwin, htop, hc'c, Option.map_some, hτc]
      have hcpτ : (State.relabelTwin x st).canPlace c (Base.relabelTwin x b) = true := by
        rw [← hτc, canPlace_relabelTwin]
        exact hcp
      change State.step (State.relabelTwin x st)
          (Move.foundToTab (Card.relabelTwin x c) (Base.relabelTwin x b)) =
        some (State.relabelTwin x st')
      rw [show State.step (State.relabelTwin x st)
            (Move.foundToTab (Card.relabelTwin x c) (Base.relabelTwin x b)) =
            some (((State.relabelTwin x st).setFound c.suit
              (chop ((State.relabelTwin x st).found c.suit))).putCard c
                (Base.relabelTwin x b)) by
            simp only [State.step]
            rw [hτc, htopτ, hcpτ]
            simp]
      rw [hs]
      change some (((State.relabelTwin x st).setFound c.suit
          (chop ((State.relabelTwin x st).found c.suit))).putCard c
            (Base.relabelTwin x b)) =
        some (State.relabelTwin x
          ((st.setFound c.suit (chop (st.found c.suit))).putCard c b))
      rw [putCard_relabelTwin, setFound_relabelTwin, hτc]
      rw [show chop ((State.relabelTwin x st).found c.suit) =
          (chop (st.found c.suit)).map (Card.relabelTwin x) by
        rw [show (State.relabelTwin x st).found c.suit =
            (st.found c.suit).map (Card.relabelTwin x) from rfl]
        rw [chop_map_relabelTwin]]
  | tabToTab c b =>
      obtain ⟨a, hh, hcp, hne, hs⟩ := step_tabToTab_inv hstep
      have hhτ : (State.relabelTwin x st).pileHolding (Card.relabelTwin x c) = some a := by
        rw [pileHolding_relabelTwin]
        exact hh
      have hcpτ : (State.relabelTwin x st).canPlace (Card.relabelTwin x c)
          (Base.relabelTwin x b) = true := by
        rw [canPlace_relabelTwin]
        exact hcp
      change State.step (State.relabelTwin x st)
          (Move.tabToTab (Card.relabelTwin x c) (Base.relabelTwin x b)) =
        some (State.relabelTwin x st')
      rw [show State.step (State.relabelTwin x st)
            (Move.tabToTab (Card.relabelTwin x c) (Base.relabelTwin x b)) =
            some (((State.relabelTwin x st).setPile a
              (Pile.afterRunRemoved ((State.relabelTwin x st).piles a)
                (below (Card.relabelTwin x c)
                  ((State.relabelTwin x st).piles a).faceUp))).putRun
                (fromCard (Card.relabelTwin x c)
                  ((State.relabelTwin x st).piles a).faceUp)
                (Base.relabelTwin x b)) by
            simp only [State.step]
            rw [hhτ, hcpτ]
            dsimp only
            have hfc : fromCard (Card.relabelTwin x c)
                ((State.relabelTwin x st).piles a).faceUp =
                (fromCard c (st.piles a).faceUp).map (Card.relabelTwin x) := by
              rw [show ((State.relabelTwin x st).piles a).faceUp =
                  (st.piles a).faceUp.map (Card.relabelTwin x) from rfl]
              exact fromCard_map_relabelTwin x c (st.piles a).faceUp
            cases hfr : fromCard c (st.piles a).faceUp with
            | nil => exact absurd hfr hne
            | cons w wt =>
                have hrun : fromCard (Card.relabelTwin x c)
                    ((State.relabelTwin x st).piles a).faceUp =
                    (w :: wt).map (Card.relabelTwin x) := by
                  rw [hfc, hfr]
                rw [hrun, List.map_cons]
                simp]
      apply congrArg some
      rw [hs]
      rw [state_relabelTwin_piles_eq, Pile.relabelTwin_faceUp,
        putRun_relabelTwin, setPile_relabelTwin, below_map_relabelTwin,
        ← Pile.afterRunRemoved_relabelTwin]
      rw [fromCard_map_relabelTwin x c (st.piles a).faceUp]

/-! ## §12. `WF` transport and the reversibility shape -/

/-- The zones list is mapped by the transposition. -/
theorem zones_relabelTwin (x : Card) (st : State) :
    (State.relabelTwin x st).zones =
      st.zones.map (List.map (Card.relabelTwin x)) := by
  simp only [State.zones, State.relabelTwin, List.map_map, List.map_append,
    List.map_cons, List.map_nil, Function.comp_def]

/-- Filtering a mapped list by a mapped value. -/
theorem filter_map_relabelTwin (x c : Card) :
    ∀ l : List Card,
      ((l.map (Card.relabelTwin x)).filter
          (fun y => decide (y = Card.relabelTwin x c))).length =
        (l.filter (fun y => decide (y = c))).length
  | [] => rfl
  | y :: t => by
      rw [List.map_cons, List.filter_cons, List.filter_cons]
      by_cases hyc : y = c
      · have hτ : Card.relabelTwin x y = Card.relabelTwin x c := by rw [hyc]
        rw [decide_eq_true hyc, decide_eq_true hτ, ite_eq_left rfl, ite_eq_left rfl,
          List.length_cons, List.length_cons, filter_map_relabelTwin x c t]
      · have hτ : Card.relabelTwin x y ≠ Card.relabelTwin x c :=
          fun h => hyc (card_relabelTwin_injective x h)
        rw [decide_eq_false hyc, decide_eq_false hτ]
        exact filter_map_relabelTwin x c t

/-- The card count transports through the transposition. -/
theorem cardCount_relabelTwin (x : Card) (st : State) (c : Card) :
    (State.relabelTwin x st).cardCount (Card.relabelTwin x c) = st.cardCount c := by
  unfold State.cardCount
  rw [zones_relabelTwin, flatMap_map_id_relabel, filter_map_relabelTwin]

/-- Face-up legality is invariant under the transposition. -/
theorem runOK_map_relabelTwin (x : Card) :
    ∀ l : List Card, runOK (l.map (Card.relabelTwin x)) = runOK l
  | [] => rfl
  | [_] => rfl
  | a :: b :: t => by
      show (canSitOn (Card.relabelTwin x b) (Card.relabelTwin x a) &&
          runOK ((b :: t).map (Card.relabelTwin x))) =
        (canSitOn b a && runOK (b :: t))
      rw [canSitOn_relabelTwin, runOK_map_relabelTwin x (b :: t)]

/-- A both-seated `WF` state stays `WF` after the transposition. -/
theorem wf_relabelTwin {st : State} {x : Card} (hwf : st.WF)
    (hx : ∃ b, seatOf st x = some b) (hxt : ∃ b, seatOf st x.twin = some b) :
    (State.relabelTwin x st).WF := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s
    rw [state_relabelTwin_found_eq hwf hx hxt s]
    exact hwf.1 s
  · intro a
    rw [state_relabelTwin_piles_eq, Pile.relabelTwin_faceUp,
      runOK_map_relabelTwin x]
    exact hwf.2.1 a
  · intro c hc
    have h := cardCount_relabelTwin x st (Card.relabelTwin x c)
    rw [card_relabelTwin_involutive] at h
    rw [h]
    exact hwf.2.2.1 (Card.relabelTwin x c) (Card.mem_universe _)
  · simpa [state_relabelTwin_drawStep] using hwf.2.2.2
/-- The draw shape is invariant under the transposition. -/
theorem drawR_relabelTwin (x : Card) (st : State) :
    drawR (State.relabelTwin x st) = drawR st := by
  unfold drawR
  cases hs : st.stock with
  | nil =>
      cases hw : st.waste with
      | nil => simp [state_relabelTwin_stock, hs, state_relabelTwin_waste, hw]
      | cons w ws =>
          simp [state_relabelTwin_stock, hs, state_relabelTwin_waste, hw]
  | cons s ss =>
      cases hw : st.waste with
      | nil => simp [state_relabelTwin_stock, hs, state_relabelTwin_waste, hw]
      | cons w ws =>
          simp [state_relabelTwin_stock, hs, state_relabelTwin_waste, hw,
            state_relabelTwin_drawStep]

/-- The raise shape is invariant when the pair transposition fixes the mover. -/
theorem tabToFoundR_relabelTwin {st : State} {x c : Card} (hwf : st.WF)
    (hx : ∃ b, seatOf st x = some b) (hxt : ∃ b, seatOf st x.twin = some b)
    (hτc : Card.relabelTwin x c = c) :
    tabToFoundR (State.relabelTwin x st) (Card.relabelTwin x c) =
      tabToFoundR st c := by
  have hnext : (State.relabelTwin x st).nextUp (Card.relabelTwin x c) =
      st.nextUp c := by rw [hτc, nextUp_relabelTwin]
  have hpile : (State.relabelTwin x st).pileOfTop (Card.relabelTwin x c) =
      st.pileOfTop c := pileOfTop_relabelTwin x st c
  unfold tabToFoundR
  rw [hnext, hpile]
  cases st.nextUp c with
  | false => rfl
  | true =>
      dsimp only
      cases hp : st.pileOfTop c with
      | none => rfl
      | some a =>
          dsimp only
          have hhidden := state_relabelTwin_hidden_eq hwf hx hxt a
          have hchop : chop ((State.relabelTwin x st).piles a).faceUp =
              (chop (st.piles a).faceUp).map (Card.relabelTwin x) := by
            rw [state_relabelTwin_piles_eq, Pile.relabelTwin_faceUp,
              chop_map_relabelTwin]
          rw [hchop]
          cases hc : chop (st.piles a).faceUp with
          | nil =>
              simp only [List.map_nil]
              rw [hhidden, hτc]
          | cons d ds =>
              simp only [List.map_cons]

/-- The pull shape is invariant when the pair transposition fixes the mover. -/
theorem foundToTabR_relabelTwin {st : State} {x c : Card} {b : Base}
    (hτc : Card.relabelTwin x c = c) :
    foundToTabR (State.relabelTwin x st) (Card.relabelTwin x c)
        (Base.relabelTwin x b) = foundToTabR st c b := by
  unfold foundToTabR
  rw [hτc, foundTop_relabelTwin]
  cases ht : st.foundTop c.suit with
  | none => rfl
  | some c' =>
      simp only [Option.map_some]
      by_cases hcc' : c' = c
      · have hmap : Card.relabelTwin x c' = c := by rw [hcc', hτc]
        rw [ite_eq_left hcc', ite_eq_left hmap]
        have hcan : (State.relabelTwin x st).canPlace c (Base.relabelTwin x b) =
            st.canPlace c b := by
          calc
            (State.relabelTwin x st).canPlace c (Base.relabelTwin x b) =
                (State.relabelTwin x st).canPlace (Card.relabelTwin x c)
                  (Base.relabelTwin x b) := by rw [hτc]
            _ = st.canPlace c b := canPlace_relabelTwin x st c b
        exact hcan
      · have hmap : Card.relabelTwin x c' ≠ c := by
          intro h
          have h' : Card.relabelTwin x c' = Card.relabelTwin x c := by rw [h, hτc]
          exact hcc' (card_relabelTwin_injective x h')
        simp only [ite_eq_right hcc', ite_eq_right hmap]

/-- The slide shape is invariant under the transposition. -/
theorem tabToTabR_relabelTwin {st : State} {x c : Card} {b : Base}
    (hwf : st.WF) (hx : ∃ bx, seatOf st x = some bx)
    (hxt : ∃ bx, seatOf st x.twin = some bx) :
    tabToTabR (State.relabelTwin x st) (Card.relabelTwin x c)
        (Base.relabelTwin x b) = tabToTabR st c b := by
  unfold tabToTabR
  rw [pileHolding_relabelTwin, canPlace_relabelTwin]
  cases hh : st.pileHolding c with
  | none => rfl
  | some a =>
      dsimp only
      have hbelow : below (Card.relabelTwin x c)
          ((State.relabelTwin x st).piles a).faceUp =
          (below c (st.piles a).faceUp).map (Card.relabelTwin x) := by
        rw [state_relabelTwin_piles_eq, Pile.relabelTwin_faceUp,
          below_map_relabelTwin]
      rw [hbelow]
      cases hcp : st.canPlace c b with
      | false => rfl
      | true =>
          dsimp only
          cases hb : below c (st.piles a).faceUp with
          | nil =>
              simp only [List.map_nil]
              rw [state_relabelTwin_hidden_eq hwf hx hxt a,
                Card.relabelTwin_rank]
          | cons d ds =>
              simp only [List.map_cons]
/-- The reversibility oracle commutes with the pair transposition at a
both-seated `WF` state, provided the letter is not a pair-foundation move. -/
theorem reversibleOf_relabelTwin {st : State} {x : Card} {m : Move}
    (hwf : st.WF)
    (hx : ∃ b, seatOf st x = some b) (hxt : ∃ b, seatOf st x.twin = some b)
    (hno : NotFoundPair x m) :
    reversibleOf (State.relabelTwin x st) (Move.relabelTwin x m) =
      reversibleOf st m := by
  cases m with
  | draw =>
      simp only [Move.relabelTwin, reversibleOf]
      exact drawR_relabelTwin x st
  | wasteToFound c =>
      simp only [Move.relabelTwin, reversibleOf]
  | wasteToTab c b =>
      simp only [Move.relabelTwin, reversibleOf]
  | tabToFound c =>
      have hcx : c ≠ x := fun h => hno.1 (by rw [h])
      have hct : c ≠ x.twin := fun h => hno.2.1 (by rw [h])
      have hτc : Card.relabelTwin x c = c := card_relabelTwin_ne hcx hct
      simp only [Move.relabelTwin, reversibleOf]
      exact tabToFoundR_relabelTwin hwf hx hxt hτc
  | foundToTab c b =>
      have hcx : c ≠ x := fun h => hno.2.2.1 b (by rw [h])
      have hct : c ≠ x.twin := fun h => hno.2.2.2 b (by rw [h])
      have hτc : Card.relabelTwin x c = c := card_relabelTwin_ne hcx hct
      simp only [Move.relabelTwin, reversibleOf]
      exact foundToTabR_relabelTwin hτc
  | tabToTab c b =>
      simp only [Move.relabelTwin, reversibleOf]
      exact tabToTabR_relabelTwin hwf hx hxt

/-- Reversibility of a non-pair-foundation letter transports through the
pair transposition. -/
theorem reversibleAtW_relabelTwin {st : State} {x : Card} {m : Move}
    (hwf : st.WF)
    (hx : ∃ b, seatOf st x = some b) (hxt : ∃ b, seatOf st x.twin = some b)
    (hno : NotFoundPair x m) (hrev : reversibleAtW st m) :
    reversibleAtW (State.relabelTwin x st) (Move.relabelTwin x m) := by
  have hwfτ : (State.relabelTwin x st).WF := wf_relabelTwin hwf hx hxt
  have hof : reversibleOf st m = true :=
    (reversibleOf_iff_reversibleAtW hwf m).mpr hrev
  have hofτ : reversibleOf (State.relabelTwin x st) (Move.relabelTwin x m) = true := by
    rw [reversibleOf_relabelTwin hwf hx hxt hno]
    exact hof
  exact (reversibleOf_iff_reversibleAtW hwfτ (Move.relabelTwin x m)).mp hofτ
/-! ## §13. The both-seated play transfer -/

/-- A witness shuffle has a legal returning play. -/
theorem shufflePlayW_back_run {st w : State} {play : List Move}
    (h : ShufflePlayW st play w) : ∃ back, w.run back = some st := by
  induction h with
  | nil s => exact ⟨[], rfl⟩
  | @cons st s1 W m ρ hrev hstep hrest ih =>
      obtain ⟨s1', ret, hstep', hret⟩ := hrev
      have hs1 : s1' = s1 := by
        rw [hstep] at hstep'
        exact (Option.some.inj hstep').symm
      obtain ⟨back, hback⟩ := ih
      rw [hs1] at hret
      exact ⟨back ++ ret, run_append W back ret s1 st hback hret⟩

/-- A legal run is a span at the trivial letter. -/
theorem run_steps_true {a b : State} {play : List Move}
    (h : a.run play = some b) :
    Steps (StepOf (fun (_ : State) (_ : Move) => True)) a b := by
  induction play generalizing a with
  | nil =>
      simp only [State.run] at h
      injection h with hab
      rw [hab]
      exact Steps.refl b
  | cons m ms ih =>
      obtain ⟨s1, hstep, hrest⟩ := State.run_cons h
      exact Steps.cons ⟨m, trivial, hstep⟩ (ih hrest)

/-- A span at the reversible letter realizes to a witness shuffle. -/
theorem revSteps_true_to_shuffle {a b : State} :
    Steps (RevStep (fun (_ : State) (_ : Move) => True)) a b →
      ∃ play, ShufflePlayW a play b
  | .refl _ => ⟨[], Walk.nil _⟩
  | .cons h t => by
      obtain ⟨m, -, hstep, hrev⟩ := h
      obtain ⟨rest, hwalk⟩ := revSteps_true_to_shuffle t
      exact ⟨m :: rest, Walk.cons hrev hstep hwalk⟩

/-- A one-way witness shuffle is a two-way reversible equivalence. -/
theorem shufflePlayW_revEqW {st w : State} {play : List Move}
    (h : ShufflePlayW st play w) : RevEqW st w := by
  obtain ⟨back, hback⟩ := shufflePlayW_back_run h
  have hfwd : st.run play = some w := Walk_run _ h
  have hSf := run_steps_true hfwd
  have hSb := run_steps_true hback
  obtain ⟨rAB, rBA⟩ :=
    (rev_steps_iff (fun (_ : State) (_ : Move) => True) st w).mp ⟨hSf, hSb⟩
  obtain ⟨σ, hσ⟩ := revSteps_true_to_shuffle rAB
  obtain ⟨τ, hτ⟩ := revSteps_true_to_shuffle rBA
  exact ⟨σ, hσ, τ, hτ⟩

/-- Relabeling a pair-avoiding witness shuffle gives a witness shuffle. -/
theorem shufflePlayW_relabel_of_no_pair {st w : State} {x : Card} {play : List Move}
    (hplay : ShufflePlayW st play w)
    (hwf : st.WF)
    (hx : ∃ b, seatOf st x = some b)
    (hxt : ∃ b, seatOf st x.twin = some b)
    (hno : ∀ m ∈ play, NotFoundPair x m) :
    ShufflePlayW (State.relabelTwin x st)
      (play.map (Move.relabelTwin x)) (State.relabelTwin x w) := by
  revert hwf hx hxt hno
  induction hplay with
  | nil s =>
      intro _ _ _ _
      exact Walk.nil (State.relabelTwin x s)
  | @cons st s1 W m ρ hrev hstep hrest ih =>
      intro hwf hx hxt hno
      have hm : NotFoundPair x m := hno m (by simp)
      have hx1 : ∃ b, seatOf s1 x = some b := by
        cases hse : seatOf s1 x with
        | some b => exact ⟨b, rfl⟩
        | none =>
            exfalso
            have hmem : Move.tabToFound x ∈ [m] :=
              tabToFound_of_seat_none (st := st) (w := s1) (c := x) hwf hx hse
                (play := [m]) (Walk.cons hrev hstep (Walk.nil s1))
            have hmx : Move.tabToFound x = m := by simpa using hmem
            exact (hno (Move.tabToFound x) (by rw [hmx]; exact List.mem_cons_self)).1 rfl
      have hxt1 : ∃ b, seatOf s1 x.twin = some b := by
        cases hse : seatOf s1 x.twin with
        | some b => exact ⟨b, rfl⟩
        | none =>
            exfalso
            have hmem : Move.tabToFound x.twin ∈ [m] :=
              tabToFound_of_seat_none (st := st) (w := s1) (c := x.twin) hwf hxt hse
                (play := [m]) (Walk.cons hrev hstep (Walk.nil s1))
            have hmx : Move.tabToFound x.twin = m := by simpa using hmem
            exact (hno (Move.tabToFound x.twin)
              (by rw [hmx]; exact List.mem_cons_self)).2.1 rfl
      change ShufflePlayW (State.relabelTwin x st)
        (Move.relabelTwin x m :: ρ.map (Move.relabelTwin x)) (State.relabelTwin x W)
      exact Walk.cons
        (reversibleAtW_relabelTwin hwf hx hxt hm hrev)
        (step_comm_of_not_foundPair hwf hx hxt hstep hm)
        (ih (step_wf hwf hstep) hx1 hxt1
          (fun a ha => hno a (List.mem_cons_of_mem m ha)))

/-- The both-seated pair relabeling transports the orbit along a pair-avoiding
witness shuffle. -/
theorem sameOrbit_relabel_of_play {st w : State} {x : Card} {play : List Move}
    (hwf : st.WF)
    (hx : ∃ b, seatOf st x = some b)
    (hxt : ∃ b, seatOf st x.twin = some b)
    (hplay : ShufflePlayW st play w)
    (hno : ∀ m ∈ play, NotFoundPair x m) :
    sameOrbitSetoid.r (State.relabelTwin x st) (State.relabelTwin x w) := by
  have hrel : ShufflePlayW (State.relabelTwin x st)
      (play.map (Move.relabelTwin x)) (State.relabelTwin x w) :=
    shufflePlayW_relabel_of_no_pair hplay hwf hx hxt hno
  exact RevEqW_symm (shufflePlayW_revEqW hrel)

/-- The rider-free, both-seated play-transfer corollary. -/
theorem swappableIn_transfer_seated_riderFree
    {s s' : State} {x : Card} {play : List Move}
    (hwf : s.WF) (hwf' : s'.WF)
    (hx : ∃ b, seatOf s x = some b) (hxt : ∃ b, seatOf s x.twin = some b)
    (hx' : ∃ b, seatOf s' x = some b) (hxt' : ∃ b, seatOf s' x.twin = some b)
    (_hrx : ∀ y, y ≠ x → seatOf s y ≠ some (Sum.inr x))
    (_hrt : ∀ y, y ≠ x.twin → seatOf s y ≠ some (Sum.inr x.twin))
    (hrx' : ∀ y, y ≠ x → seatOf s' y ≠ some (Sum.inr x))
    (hrt' : ∀ y, y ≠ x.twin → seatOf s' y ≠ some (Sum.inr x.twin))
    (hswap : sameOrbitSetoid.r s (State.relabelTwin x s))
    (hplay : ShufflePlayW s play s')
    (hno : ∀ m ∈ play, NotFoundPair x m) :
    SwappableIn s' x := by
  have hrel : sameOrbitSetoid.r (State.relabelTwin x s)
      (State.relabelTwin x s') :=
    sameOrbit_relabel_of_play hwf hx hxt hplay hno
  have hback : RevEqW s s' := shufflePlayW_revEqW hplay
  have hchain : RevEqW (State.relabelTwin x s') s' :=
    RevEqW_trans (RevEqW_trans hrel hswap) hback
  refine ⟨State.relabelTwin x s',
    twinPairSwapStrict_relabelTwin hwf' hx' hxt' hrx' hrt', ?_⟩
  exact hchain

#print axioms step_comm_of_not_foundPair
#print axioms sameOrbit_relabel_of_play
#print axioms swappableIn_transfer_seated_riderFree
