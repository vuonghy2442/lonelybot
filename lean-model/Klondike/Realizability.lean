import Klondike.Progress
import Klondike.Kit

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

The finite-cardinality plumbing — `NoDupP`, the bijection count
`length_eq_of_bijection`, the filter splits, the universe's
distinctness — lives in `Klondike.Kit`.  What stays here are the
card-rule lemmas the parity lemma's proof reduces to.
-/

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
