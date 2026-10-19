import Orig2.Vocab
import Orig2.Integrity

/-!
# Orig2.TwinRelabel — the state-level twin relabeling

This card defines the value relabeling at the card and state level and
proves its basic laws, then locates it on the chart: at a `WF` state
whose two twin cards both sit face up on the tableau (and therefore
nowhere else), the relabeled position exchanges the pair's `seatOf`
values.  The exact strict twin swap additionally needs both pair seats
to be rider-free (see the counterexample note below).

THE COUNTEREXAMPLE NOTE (why the strict bridge carries rider clauses):
the relabeling rewrites card *values* in place.  A card `y` seated
directly on `x` keeps its position in the pile, so its `seatOf` readout
changes from `inr x` to `inr x.twin`.  The strict letter demands that
every other seat be literally fixed, so the bridge needs the pair's
seats to be rider-free (no card sits directly on either twin).  The
bare twin letter — only the two pair seats exchanged — holds with no
such clause; both forms are below, and the docstrings on the strict
form record the exact counterexample shape.

House compliance: additive card; zero `sorry`; zero
`Classical.choice`; the imports are the registry (`Orig2.Vocab`) and
the shared integrity kit (`Orig2.Integrity`) whose occurrence
uniqueness rows the bridge consumes.
-/

namespace Card

/-- **`Card.relabelTwin x c`** — swap the two values `x` and `x.twin`,
fixing every other card. -/
def relabelTwin (x c : Card) : Card :=
  if c = x then x.twin else if c = x.twin then x else c

end Card

namespace State

/-- **`State.relabelTwin x st`** — apply the card relabeling in every
card-carrying zone; the draw step is untouched. -/
def relabelTwin (x : Card) (st : State) : State :=
  { found := fun s => (st.found s).map (Card.relabelTwin x)
    piles := fun a => { hidden := (st.piles a).hidden.map (Card.relabelTwin x)
                        faceUp := (st.piles a).faceUp.map (Card.relabelTwin x) }
    stock := st.stock.map (Card.relabelTwin x)
    waste := st.waste.map (Card.relabelTwin x)
    drawStep := st.drawStep }

end State

/-! ## §1. The card involution -/

/-- No card is its own twin. -/
theorem card_twin_ne (x : Card) : x.twin ≠ x := by
  obtain ⟨s, r⟩ := x
  cases s <;> simp [Card.twin, Suit.twin]

/-- The twin involution on cards. -/
theorem card_twin_twin (c : Card) : c.twin.twin = c := by
  cases c with
  | mk s r => simp [Card.twin]

/-- The relabeling sends `x` to its twin. -/
@[simp] theorem card_relabelTwin_self (x : Card) :
    Card.relabelTwin x x = x.twin := by
  simp [Card.relabelTwin]

/-- The relabeling sends `x.twin` back to `x`. -/
@[simp] theorem card_relabelTwin_twin (x : Card) :
    Card.relabelTwin x x.twin = x := by
  rw [Card.relabelTwin, ite_eq_right (card_twin_ne x), ite_eq_left rfl]

/-- The relabeling fixes every card off the pair. -/
theorem card_relabelTwin_ne {x c : Card} (hx : c ≠ x) (hxt : c ≠ x.twin) :
    Card.relabelTwin x c = c := by
  rw [Card.relabelTwin, ite_eq_right hx, ite_eq_right hxt]

/-- The relabeling is an involution. -/
@[simp] theorem card_relabelTwin_involutive (x c : Card) :
    Card.relabelTwin x (Card.relabelTwin x c) = c := by
  by_cases hc : c = x
  · subst hc
    rw [card_relabelTwin_self, card_relabelTwin_twin]
  · by_cases hct : c = x.twin
    · subst hct
      rw [card_relabelTwin_twin, card_relabelTwin_self]
    · rw [card_relabelTwin_ne hc hct, card_relabelTwin_ne hc hct]

/-! ## §2. The state relabeling and its projections -/

@[simp] theorem state_relabelTwin_found (x : Card) (st : State) (s : Suit) :
    (State.relabelTwin x st).found s = (st.found s).map (Card.relabelTwin x) :=
  rfl

@[simp] theorem state_relabelTwin_piles (x : Card) (st : State) (a : Anchor) :
    (State.relabelTwin x st).piles a =
      { hidden := (st.piles a).hidden.map (Card.relabelTwin x)
        faceUp := (st.piles a).faceUp.map (Card.relabelTwin x) } :=
  rfl

@[simp] theorem state_relabelTwin_piles_hidden
    (x : Card) (st : State) (a : Anchor) :
    ((State.relabelTwin x st).piles a).hidden =
      (st.piles a).hidden.map (Card.relabelTwin x) :=
  rfl

@[simp] theorem state_relabelTwin_piles_faceUp
    (x : Card) (st : State) (a : Anchor) :
    ((State.relabelTwin x st).piles a).faceUp =
      (st.piles a).faceUp.map (Card.relabelTwin x) :=
  rfl

@[simp] theorem state_relabelTwin_stock (x : Card) (st : State) :
    (State.relabelTwin x st).stock = st.stock.map (Card.relabelTwin x) :=
  rfl

@[simp] theorem state_relabelTwin_waste (x : Card) (st : State) :
    (State.relabelTwin x st).waste = st.waste.map (Card.relabelTwin x) :=
  rfl

@[simp] theorem state_relabelTwin_drawStep (x : Card) (st : State) :
    (State.relabelTwin x st).drawStep = st.drawStep :=
  rfl

/-- A list mapped by an involution is unchanged. -/
private theorem list_map_comp_self {f : Card → Card} (hinv : ∀ c, f (f c) = c) :
    ∀ l : List Card, l.map (f ∘ f) = l
  | [] => rfl
  | c :: t => by
      show f (f c) :: (t.map (f ∘ f)) = c :: t
      rw [hinv c, list_map_comp_self hinv t]

/-- The state relabeling is an involution. -/
theorem state_relabelTwin_involutive (x : Card) (st : State) :
    State.relabelTwin x (State.relabelTwin x st) = st := by
  apply State.ext
  · funext s
    simp only [State.relabelTwin, List.map_map]
    exact list_map_comp_self (card_relabelTwin_involutive x) _
  · funext a
    apply Pile.ext
    · simp only [State.relabelTwin, List.map_map]
      exact list_map_comp_self (card_relabelTwin_involutive x) _
    · simp only [State.relabelTwin, List.map_map]
      exact list_map_comp_self (card_relabelTwin_involutive x) _
  · simp only [State.relabelTwin, List.map_map]
    exact list_map_comp_self (card_relabelTwin_involutive x) _
  · simp only [State.relabelTwin, List.map_map]
    exact list_map_comp_self (card_relabelTwin_involutive x) _
  · rfl

/-! ## §3. The chart kit for the relabeling -/

/-- `firstWhere` respects pointwise predicate agreement. -/
private theorem firstWhere_congr {α : Type} {p q : α → Bool}
    (h : ∀ x, p x = q x) : ∀ l : List α, firstWhere p l = firstWhere q l
  | [] => rfl
  | x :: t => by
      show (match p x with
            | true => some x
            | false => firstWhere p t) =
           (match q x with
            | true => some x
            | false => firstWhere q t)
      rw [h x]
      cases q x with
      | true => rfl
      | false => exact firstWhere_congr h t

/-- Membership in a list mapped by an involution. -/
private theorem mem_map_involution {f : Card → Card} (hinv : ∀ c, f (f c) = c)
    (l : List Card) (c : Card) : c ∈ l.map f ↔ f c ∈ l := by
  constructor
  · intro h
    obtain ⟨d, hd, hdc⟩ := List.mem_map.mp h
    rw [← hdc, hinv d]
    exact hd
  · intro h
    exact List.mem_map.mpr ⟨f c, h, hinv c⟩

/-- The holding search commutes with the relabeling. -/
private theorem pileHolding_relabel (x : Card) (st : State) (c : Card) :
    (State.relabelTwin x st).pileHolding c =
      st.pileHolding (Card.relabelTwin x c) := by
  unfold State.pileHolding
  apply firstWhere_congr
  intro a
  rw [state_relabelTwin_piles_faceUp]
  by_cases h : Card.relabelTwin x c ∈ (st.piles a).faceUp
  · have hc : c ∈ (st.piles a).faceUp.map (Card.relabelTwin x) :=
      (mem_map_involution (card_relabelTwin_involutive x) _ c).mpr h
    rw [decide_eq_true hc, decide_eq_true h]
  · have hc : c ∉ (st.piles a).faceUp.map (Card.relabelTwin x) :=
      fun hmem => h ((mem_map_involution (card_relabelTwin_involutive x) _ c).mp hmem)
    rw [decide_eq_false hc, decide_eq_false h]

/-- `below` commutes with an involution. -/
private theorem below_map_involution {f : Card → Card} (hinv : ∀ c, f (f c) = c) :
    ∀ (l : List Card) (c : Card),
      below c (l.map f) = (below (f c) l).map f
  | [], _ => rfl
  | x :: t, c => by
      rw [List.map_cons, below_cons, below_cons]
      by_cases hfx : f x = c
      · have hx : x = f c := by
          have := congrArg f hfx
          rwa [hinv x] at this
        rw [ite_eq_left hfx, ite_eq_left hx]
        rfl
      · have hx : x ≠ f c := by
          intro hcon
          apply hfx
          rw [hcon, hinv c]
        rw [ite_eq_right hfx, ite_eq_right hx, List.map_cons,
          below_map_involution hinv t c]

/-- `getLast?` is the house `lastOf`. -/
private theorem getLast?_lastOf : ∀ (l : List Card), l.getLast? = lastOf l
  | [] => rfl
  | [_] => rfl
  | _ :: y :: t => getLast?_lastOf (y :: t)

/-- `lastOf` commutes with mapping. -/
private theorem lastOf_map (f : Card → Card) :
    ∀ (l : List Card), lastOf (l.map f) = (lastOf l).map f
  | [] => rfl
  | [_] => rfl
  | x :: y :: t => by
      show lastOf ((f y) :: t.map f) = (lastOf (y :: t)).map f
      exact lastOf_map f (y :: t)

/-- The seat map of the relabeled state: the old seat, with the pair's
value relabeled in the `.inr` parent case. -/
private theorem seatOf_relabel (x : Card) (st : State) (c : Card) :
    seatOf (State.relabelTwin x st) c =
      (match seatOf st (Card.relabelTwin x c) with
       | none => none
       | some (Sum.inl a) => some (Sum.inl a)
       | some (Sum.inr z) => some (Sum.inr (Card.relabelTwin x z))) := by
  unfold seatOf
  rw [pileHolding_relabel]
  cases hs : st.pileHolding (Card.relabelTwin x c) with
  | none => rfl
  | some a =>
      simp only []
      rw [state_relabelTwin_piles_faceUp,
        below_map_involution (card_relabelTwin_involutive x),
        getLast?_lastOf, lastOf_map, getLast?_lastOf]
      cases hz : lastOf (below (Card.relabelTwin x c) (st.piles a).faceUp) with
      | none => simp
      | some z => simp

/-- `below c l ++ fromCard c l = l`. -/
private theorem below_fromCard (c : Card) :
    ∀ (l : List Card), below c l ++ fromCard c l = l
  | [] => rfl
  | x :: t => by
      rw [below_cons, fromCard]
      by_cases hxc : x = c
      · rw [ite_eq_left hxc, ite_eq_left hxc]
        rfl
      · rw [ite_eq_right hxc, ite_eq_right hxc, List.cons_append]
        exact congrArg (x :: ·) (below_fromCard c t)

/-- A member heads the `fromCard` suffix. -/
private theorem fromCard_cons_head {c : Card} :
    ∀ {l : List Card}, c ∈ l → ∃ r, fromCard c l = c :: r
  | [], h => by cases h
  | x :: t, h => by
      by_cases hxc : x = c
      · exact ⟨t, by rw [fromCard, ite_eq_left hxc, hxc]⟩
      · have hmem : c ∈ t := by
          rcases List.mem_cons.mp h with h' | h'
          · exact absurd h'.symm hxc
          · exact h'
        obtain ⟨r, hr⟩ := fromCard_cons_head hmem
        exact ⟨r, by rw [fromCard, ite_eq_right hxc]; exact hr⟩

/-- The `.inr` seat read: a holding pile, a nonempty below-part, and
its last card. -/
private theorem seatOf_inr_data {st : State} {c z : Card}
    (h : seatOf st c = some (Sum.inr z)) :
    ∃ a, st.pileHolding c = some a ∧
      below c (st.piles a).faceUp ≠ [] ∧
      lastOf (below c (st.piles a).faceUp) = some z := by
  unfold seatOf at h
  cases hh : st.pileHolding c with
  | none =>
      rw [hh] at h
      exact absurd h (by simp)
  | some a =>
      simp only [hh] at h
      cases hg : List.getLast? (below c (st.piles a).faceUp) with
      | none =>
          rw [hg] at h
          exact absurd h (by simp)
      | some q =>
          simp only [hg] at h
          have hqz : q = z := Sum.inr.inj (Option.some.inj h)
          subst hqz
          refine ⟨a, rfl, ?_, ?_⟩
          · intro hnil
            rw [hnil] at hg
            simp at hg
          · rw [← getLast?_lastOf]
            exact hg

/-- A card's parent in an `.inr` seat has a different rank. -/
private theorem parent_rank_ne_of_seat {st : State} (hwf : st.WF) {c z : Card}
    (hse : seatOf st c = some (Sum.inr z)) (hrank : z.rank = c.rank) : False := by
  obtain ⟨a, hh, _, hlast⟩ := seatOf_inr_data hse
  have hmem : c ∈ (st.piles a).faceUp := pileHolding_mem hh
  obtain ⟨t, ht⟩ := fromCard_cons_head hmem
  have hsplit : (st.piles a).faceUp =
      below c (st.piles a).faceUp ++ (c :: t) := by
    have h := below_fromCard c (st.piles a).faceUp
    rw [ht] at h
    exact h.symm
  have hrun : runOK (below c (st.piles a).faceUp ++ (c :: t)) = true := by
    rw [← hsplit]
    exact hwf.runOK_of a
  have hzmem : z ∈ below c (st.piles a).faceUp := lastOf_mem hlast
  have hlt := runOK_desc hrun hzmem (by simp : c ∈ c :: t)
  have hidx : z.rank.toIdx = c.rank.toIdx := by rw [hrank]
  omega

/-- The relabeling exchanges `x`'s seat with `x.twin`'s. -/
theorem state_relabelTwin_seat_x {st : State} {x : Card} (hwf : st.WF) :
    seatOf (State.relabelTwin x st) x = seatOf st x.twin := by
  rw [seatOf_relabel, card_relabelTwin_self]
  cases hs : seatOf st x.twin with
  | none => rfl
  | some b =>
      cases b with
      | inl a => rfl
      | inr z =>
          have hzx : z ≠ x := by
            intro hcon
            subst hcon
            exact parent_rank_ne_of_seat hwf hs rfl
          have hzt : z ≠ x.twin := by
            intro hcon
            subst hcon
            exact parent_rank_ne_of_seat hwf hs rfl
          simp only []
          rw [card_relabelTwin_ne hzx hzt]

/-- The relabeling exchanges `x.twin`'s seat with `x`'s. -/
theorem state_relabelTwin_seat_twin {st : State} {x : Card} (hwf : st.WF) :
    seatOf (State.relabelTwin x st) x.twin = seatOf st x := by
  rw [seatOf_relabel, card_relabelTwin_twin]
  cases hs : seatOf st x with
  | none => rfl
  | some b =>
      cases b with
      | inl a => rfl
      | inr z =>
          have hzx : z ≠ x := by
            intro hcon
            subst hcon
            exact parent_rank_ne_of_seat hwf hs rfl
          have hzt : z ≠ x.twin := by
            intro hcon
            subst hcon
            exact parent_rank_ne_of_seat hwf hs rfl
          simp only []
          rw [card_relabelTwin_ne hzx hzt]

/-- With the pair's seats rider-free, the relabeling fixes every other
seat. -/
theorem state_relabelTwin_seat_other {st : State} {x y : Card} (_hwf : st.WF)
    (hyx : y ≠ x) (hyt : y ≠ x.twin)
    (hRx : ∀ z, z ≠ x → seatOf st z ≠ some (Sum.inr x))
    (hRt : ∀ z, z ≠ x.twin → seatOf st z ≠ some (Sum.inr x.twin)) :
    seatOf (State.relabelTwin x st) y = seatOf st y := by
  rw [seatOf_relabel, card_relabelTwin_ne hyx hyt]
  cases hs : seatOf st y with
  | none => rfl
  | some b =>
      cases b with
      | inl a => rfl
      | inr z =>
          have hzx : z ≠ x := by
            intro hcon
            exact hRx y hyx (hcon ▸ hs)
          have hzt : z ≠ x.twin := by
            intro hcon
            exact hRt y hyt (hcon ▸ hs)
          simp only []
          rw [card_relabelTwin_ne hzx hzt]

/-! ## §4. The bridge to the twin letters -/

/-- A list all of whose entries are fixed by `f` is unchanged by
`List.map f`. -/
private theorem map_eq_self {α : Type} (f : α → α) :
    ∀ {l : List α}, (∀ a ∈ l, f a = a) → l.map f = l
  | [], _ => rfl
  | a :: t, h => by
      rw [List.map_cons, h a (by simp)]
      exact congrArg (a :: ·) (map_eq_self f (fun b hb => h b (by simp [hb])))

/-- A seated card is face up somewhere. -/
private theorem mem_faceUp_of_seat {st : State} {c : Card} {b : Base}
    (h : seatOf st c = some b) : ∃ a, c ∈ (st.piles a).faceUp := by
  unfold seatOf at h
  cases hh : st.pileHolding c with
  | none =>
      rw [hh] at h
      exact absurd h (by simp)
  | some a => exact ⟨a, pileHolding_mem hh⟩

/-- A face-up card is absent from every hidden deck, the stock, the
waste, and every foundation (occurrence uniqueness at `WF`). -/
private theorem off_zones_of_seat {st : State} (hwf : st.WF) {c : Card}
    (hse : ∃ b, seatOf st c = some b) :
    (∀ a, c ∉ (st.piles a).hidden) ∧ c ∉ st.stock ∧ c ∉ st.waste ∧
      ∀ s, c ∉ st.found s := by
  obtain ⟨b, hb⟩ := hse
  obtain ⟨a, hmem⟩ := mem_faceUp_of_seat hb
  obtain ⟨hother, hown, hstock, hwaste, hfound⟩ := mem_faceUp_only hwf hmem
  refine ⟨?_, hstock, hwaste, hfound⟩
  intro a'
  by_cases ha : a' = a
  · subst ha
    exact hown
  · exact (hother a' ha).1

/-- The bare twin letter: at any `WF` state the relabeling exchanges
the pair's two seats (no rider clause is needed for the pair seats
alone). -/
theorem twinPairSwap_relabelTwin {st : State} {x : Card} (hwf : st.WF) :
    twinPairSwap st (State.relabelTwin x st) x :=
  ⟨state_relabelTwin_seat_x hwf, state_relabelTwin_seat_twin hwf⟩

/-- The strict twin letter at a rider-free pair: both twins sit face up
on the tableau and nowhere else, and no other card sits directly on
either twin.  The relabeling then realizes the exact strict swap.

RIDER CLAUSES ARE NECESSARY: without them the statement is FALSE.
Take `x = ♠Q`, `x.twin = ♣Q`, a pile `[♠Q, ♥J]` (so `♥J` sits directly
on `♠Q`), and `♣Q` bottoming another pile, with the rest of the deck in
the stock.  The state is `WF`, both twins are seated and nowhere else,
but the relabeled state carries `♥J` on `♣Q`, so
`seatOf v ♥J = some (inr ♣Q) ≠ some (inr ♠Q) = seatOf st ♥J`, and the
all-other-seats clause of `twinPairSwapStrict` fails. -/
theorem twinPairSwapStrict_relabelTwin {st : State} {x : Card}
    (hwf : st.WF)
    (hx : ∃ b, seatOf st x = some b)
    (hxt : ∃ b, seatOf st x.twin = some b)
    (hRx : ∀ y, y ≠ x → seatOf st y ≠ some (Sum.inr x))
    (hRt : ∀ y, y ≠ x.twin → seatOf st y ≠ some (Sum.inr x.twin)) :
    twinPairSwapStrict st (State.relabelTwin x st) x := by
  obtain ⟨hxhid, hxst, hxwa, hxfo⟩ := off_zones_of_seat hwf hx
  obtain ⟨hxthid, hxtst, hxtwa, hxtfo⟩ := off_zones_of_seat hwf hxt
  refine ⟨state_relabelTwin_seat_x hwf,
    state_relabelTwin_seat_twin hwf, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro y hyx hyt
    exact state_relabelTwin_seat_other hwf hyx hyt hRx hRt
  · refine ⟨?_, rfl⟩
    intro a
    simp only [state_relabelTwin_piles_hidden]
    exact (map_eq_self (Card.relabelTwin x) (fun c hc =>
      card_relabelTwin_ne (fun h => hxhid a (h ▸ hc))
        (fun h => hxthid a (h ▸ hc)))).symm
  · intro s
    simp only [state_relabelTwin_found]
    exact (map_eq_self (Card.relabelTwin x) (fun c hc =>
      card_relabelTwin_ne (fun h => hxfo s (h ▸ hc))
        (fun h => hxtfo s (h ▸ hc)))).symm
  · simp only [state_relabelTwin_stock]
    exact (map_eq_self (Card.relabelTwin x) (fun c hc =>
      card_relabelTwin_ne (fun h => hxst (h ▸ hc))
        (fun h => hxtst (h ▸ hc)))).symm
  · simp only [state_relabelTwin_waste]
    exact (map_eq_self (Card.relabelTwin x) (fun c hc =>
      card_relabelTwin_ne (fun h => hxwa (h ▸ hc))
        (fun h => hxtwa (h ▸ hc)))).symm
  · unfold cutOf
    rw [state_relabelTwin_stock]
    simp

/-! ## §5. Audit battery -/

#print axioms card_relabelTwin_self
#print axioms card_relabelTwin_twin
#print axioms card_relabelTwin_ne
#print axioms card_relabelTwin_involutive
#print axioms state_relabelTwin_involutive
#print axioms state_relabelTwin_seat_x
#print axioms state_relabelTwin_seat_twin
#print axioms twinPairSwap_relabelTwin
#print axioms twinPairSwapStrict_relabelTwin
