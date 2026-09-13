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

/-- **The parity lemma** (no_pile §3): `uncovered = present − placed`
counts exactly the free surfaces of the type.  Each below-type card
covers a *distinct* present type-`t` card (matching injectivity), and
covering cards are exactly below-type (edge legality) — so the
difference is the free count.  Their `bm` (`get_bottom_mask`)
computes `uncovered_t > 0`.  TODO: the counting bijection over the
filtered lists. -/
theorem uncovered_eq_freeType {bd : Board} (hleg : bd.legalEdges) (t : Rank × Color) :
    bd.uncovered t = bd.freeType t := sorry

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
tracked masks) belongs to the bridge milestone.  TODO. -/
theorem apply_realizable {st st' : State} (hwf : st.WF) {m : Move}
    (h : st.apply m = some st') :
    Realizable st'.deal st'.depths (fun c => st'.isVis c) := sorry
