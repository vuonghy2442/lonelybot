import Orig

/-!
# The classification fork exhibits — the wild corners that force the WF gate

Tranche two's design fork, witnessed (FUTURES-ORIG §5.6; the fork
resolution recorded in `Orig.Classify`'s header): the oracle's
shape predicates are WF-gated, and *at wild states no
guard-derived Bool can track the semantic irreversibility
predicate*, which quantifies over whole returning plays.  The
predecessor's two corners, mechanized here as decide-graded wild
records in the witness-archive style:

* **The diadem** (`diadem`): a doubled-king, miscounted-foundation
  corner — a noreveal `.tabToFound ♥Q` off a twin `♠K` seat where
  `canSitOn ♥Q ♠K` holds (the static seat fit reads fine) yet at
  the successor the pile-top search for `♠K` pins the *other*
  copy — the empty-anchor double at `p1`, not the seat `p5` — so
  every static-undo premise of the under row fails there; the
  one-move mirror lands the queen on the wrong pile.  And still,
  a three-move shuttle returns: king up (the *bare* copy, by the
  very misfired search), queen re-seated, king back.  The move is
  reversible — semantically — while the shape/undo analysis
  cannot see it.  The commit-direction exhibit: shapes and static
  premises cannot *imply* irreversibility.

* **The freezer** (`freezer`): a wild-stacked corner whose
  successful noreveal-look `.tabToTab ♥5 (inr ♠6)` — an under row:
  the below part `[♦6]` survives — lands on a fully **frozen**
  successor: complete foundations, empty stock and waste, every
  pile occupied, and a face-up census whose fit matrix is dead
  (the red-red mirror fit `canSitOn ♥5 ♦6` is the only
  rank-correct pairing left, and the color guard kills it).  No
  move fires from the successor, so the move is semantically
  *irreversible* — no play returns — while the under-row shape
  reads *reversible* (`irreversibleOf freezer … = false`).  The
  refutation-direction exhibit: the shape cannot *imply*
  reversibility either — `wk_irreversibleOf_premiseless_false`
  refutes the premiseless universal iff outright.

Together they justify the gate `st.WF` on every classification
row of `Orig.Classify`: at `WF` the premise families discharge
through the conservation invariant instead of being read off
guards.

Verdicts are decide-graded through a private `DecidableEq State`
bridge (dedup-marked: the re-derivation is copied from the
OrigExchange witness archive, whose base predates
`Orig.Integrity`; the step-shape aliases and dead-move machinery
below are likewise local copies in that discipline).  The census
`#eval` battery and the `#print axioms` pins are at the file's
end.
-/

namespace ClassificationFork

/-! ## Cards, foundations, piles -/

/-- Spades. -/
private def S (r : Rank) : Card := ⟨Suit.spade, r⟩
/-- Hearts. -/
private def H (r : Rank) : Card := ⟨Suit.heart, r⟩
/-- Diamonds. -/
private def D (r : Rank) : Card := ⟨Suit.diamond, r⟩
/-- Clubs. -/
private def C (r : Rank) : Card := ⟨Suit.club, r⟩

/-- An occupied, silent guard pile: one hidden card, no face-up. -/
private def gPile (x : Card) : Pile := ⟨[x], []⟩

/-- The empty spectator pile. -/
private def ePile : Pile := ⟨[], []⟩

private def mkFz (found : Suit → List Card) (p : Anchor → Pile) : State :=
  { found := found, piles := p, stock := [], waste := [], drawStep := 1 }

/-! ## The state-equality bridge and step-shape aliases
(DEDUP-marked: local re-derivations in the OrigExchange witness
discipline; see the header). -/

private def decSt (s t : State) : Decidable (s = t) :=
  decidable_of_decidable_of_iff (p :=
    (s.found .spade = t.found .spade ∧ s.found .heart = t.found .heart ∧
     s.found .diamond = t.found .diamond ∧ s.found .club = t.found .club ∧
     s.piles .p0 = t.piles .p0 ∧ s.piles .p1 = t.piles .p1 ∧
     s.piles .p2 = t.piles .p2 ∧ s.piles .p3 = t.piles .p3 ∧
     s.piles .p4 = t.piles .p4 ∧ s.piles .p5 = t.piles .p5 ∧
     s.piles .p6 = t.piles .p6 ∧
     s.stock = t.stock ∧ s.waste = t.waste ∧ s.drawStep = t.drawStep))
    (by
      constructor
      · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩
        apply State.ext
        · funext σ; cases σ <;> assumption
        · funext a; cases a <;> assumption
        · assumption
        · assumption
        · assumption
      · rintro rfl
        exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩)

local instance : DecidableEq State := fun s t => decSt s t

private theorem pileOfTop_some {st : State} {z : Card} {a : Anchor}
    (h : st.pileOfTop z = some a) : st.topOf a = some z := by
  have h' : firstWhere (fun a' => decide (st.topOf a' = some z)) Anchor.all = some a := h
  exact of_decide_eq_true
    (firstWhere_sound (fun a' => decide (st.topOf a' = some z)) h')

private theorem pileHolding_some {st : State} {c : Card} {a : Anchor}
    (h : st.pileHolding c = some a) : c ∈ (st.piles a).faceUp := by
  have h' : firstWhere (fun a' => decide (c ∈ (st.piles a').faceUp)) Anchor.all = some a := h
  exact of_decide_eq_true
    (firstWhere_sound (fun a' => decide (c ∈ (st.piles a').faceUp)) h')

private theorem canPlace_inl_eq (st : State) (c : Card) (a : Anchor) :
    st.canPlace c (.inl a) = ((st.piles a).isEmpty && decide (c.rank = .king)) := rfl

private theorem canPlace_inr_eq (st : State) (c z : Card) :
    st.canPlace c (.inr z) = (match st.pileOfTop z with
      | some _ => canSitOn c z | none => false) := rfl

private theorem step_w2f_eq (st : State) (c : Card) :
    st.step (.wasteToFound c) =
      (if st.wasteIs c && st.nextUp c then
        match st.waste with
        | _ :: ws => some { st.setFound c.suit (st.found c.suit ++ [c]) with waste := ws }
        | [] => none
      else none) := rfl

private theorem step_w2t_eq (st : State) (c : Card) (b : Base) :
    st.step (.wasteToTab c b) =
      (if st.wasteIs c && st.canPlace c b then
        match st.waste with
        | _ :: ws => some { st.putCard c b with waste := ws }
        | [] => none
      else none) := rfl

private theorem step_t2f_eq (st : State) (c : Card) :
    st.step (.tabToFound c) =
      (if st.nextUp c then
        match st.pileOfTop c with
        | none => none
        | some a =>
            some { st.setFound c.suit (st.found c.suit ++ [c]) with
                     piles := fun a' =>
                       if a' = a then
                         Pile.afterRunRemoved (st.piles a) (chop (st.piles a).faceUp)
                       else st.piles a' }
      else none) := rfl

private theorem step_f2t_eq (st : State) (c : Card) (b : Base) :
    st.step (.foundToTab c b) =
      (match st.foundTop c.suit with
      | some c' =>
          if decide (c' = c) && st.canPlace c b then
            some ((st.setFound c.suit (chop (st.found c.suit))).putCard c b)
          else none
      | none => none) := rfl

private theorem step_t2t_eq (st : State) (c : Card) (b : Base) :
    st.step (.tabToTab c b) =
      (match st.pileHolding c with
      | none => none
      | some a =>
          if st.canPlace c b then
            match fromCard c (st.piles a).faceUp with
            | [] => none
            | run =>
                some ((st.setPile a (Pile.afterRunRemoved (st.piles a)
                  (below c (st.piles a).faceUp))).putRun run b)
          else none) := rfl

/-! ## The dead-move machinery (DEDUP-marked local copies, adapted
to the freezer's complete foundations) -/

private theorem draw_dead (st : State) (hs : st.stock = []) (hw : st.waste = []) :
    st.step .draw = none := by
  have hre : st.recycle = st := by simp [State.recycle, hs, hw]
  show State.dealStock st.recycle = none
  rw [hre]
  simp [State.dealStock, hs]

private theorem waste_found_dead (st : State) (hw : st.waste = []) (c : Card) :
    st.step (.wasteToFound c) = none := by
  rw [step_w2f_eq, show st.wasteIs c = false from State.wasteIs_nil hw]
  simp

private theorem waste_tab_dead (st : State) (hw : st.waste = []) (c : Card) (b : Base) :
    st.step (.wasteToTab c b) = none := by
  rw [step_w2t_eq, show st.wasteIs c = false from State.wasteIs_nil hw]
  simp

private theorem rank_toIdx_twelve {r : Rank} (h : r.toIdx = 12) : r = .king := by
  cases r <;> simp_all [Rank.toIdx]

/-- Complete foundations kill every ascend: no card sits at index
13. -/
private theorem nextUp_false_of_full (st : State)
    (hf : ∀ s : Suit, (st.found s).length = 13) (c : Card) :
    st.nextUp c = false := by
  rcases c with ⟨s, r⟩
  rw [State.nextUp]
  rw [decide_eq_false (by
    intro hcon
    -- the anonymous-constructor projection is eaten by defeq at the
    -- `have`; om ω's atomization will not see through it
    have hcon' : r.toIdx = st.foundHeight s := hcon
    have hf13 : st.foundHeight s = 13 := by
      show (st.found s).length = 13
      exact hf s
    have hlt : r.toIdx < 13 := Rank.toIdx_lt r
    omega)]

/-- A king can never be placed onto an occupied board: no empty
seats, and no card sits thirteen. -/
private theorem canPlace_king_false (st : State)
    (hocc : ∀ a : Anchor, ¬ (st.piles a).isEmpty) (c : Card) (hck : c.rank = .king)
    (b : Base) : st.canPlace c b = false := by
  cases b with
  | inl a =>
      rw [canPlace_inl_eq]
      have hio : (st.piles a).isEmpty = false := by
        cases hio : (st.piles a).isEmpty with
        | true => exact (hocc a hio).elim
        | false => rfl
      rw [hio]; simp
  | inr z =>
      rw [canPlace_inr_eq]
      cases hp : st.pileOfTop z with
      | none => rfl
      | some k =>
          show canSitOn c z = false
          cases hfit : canSitOn c z with
          | true =>
              obtain ⟨h1, -⟩ := (canSitOn_eq c z).mp hfit
              have hz := Rank.toIdx_lt z.rank
              rw [hck] at h1
              simp_all [Rank.toIdx]
          | false => rfl

/-- With every foundation complete, the foundation-return arm is
dead: only kings could descend, and no king can be placed. -/
private theorem foundToTab_kings (st : State)
    (hft : ∀ s : Suit, st.foundTop s = some (Card.mk s Rank.king))
    (hocc : ∀ a : Anchor, ¬ (st.piles a).isEmpty)
    (c : Card) (b : Base) : st.step (.foundToTab c b) = none := by
  rw [step_f2t_eq]
  cases hcs : c.suit with
  | spade =>
      rw [hft .spade]
      show (if decide (Card.mk Suit.spade Rank.king = c) && st.canPlace c b then
        some _ else none) = none
      by_cases hck : Card.mk Suit.spade Rank.king = c
      · rw [← hck, canPlace_king_false st hocc _ rfl b]
        rfl
      · have h2 : decide (Card.mk Suit.spade Rank.king = c) = false :=
          decide_eq_false hck
        rw [h2, Bool.false_and]; rfl
  | heart =>
      rw [hft .heart]
      show (if decide (Card.mk Suit.heart Rank.king = c) && st.canPlace c b then
        some _ else none) = none
      by_cases hck : Card.mk Suit.heart Rank.king = c
      · rw [← hck, canPlace_king_false st hocc _ rfl b]
        rfl
      · have h2 : decide (Card.mk Suit.heart Rank.king = c) = false :=
          decide_eq_false hck
        rw [h2, Bool.false_and]; rfl
  | diamond =>
      rw [hft .diamond]
      show (if decide (Card.mk Suit.diamond Rank.king = c) && st.canPlace c b then
        some _ else none) = none
      by_cases hck : Card.mk Suit.diamond Rank.king = c
      · rw [← hck, canPlace_king_false st hocc _ rfl b]
        rfl
      · have h2 : decide (Card.mk Suit.diamond Rank.king = c) = false :=
          decide_eq_false hck
        rw [h2, Bool.false_and]; rfl
  | club =>
      rw [hft .club]
      show (if decide (Card.mk Suit.club Rank.king = c) && st.canPlace c b then
        some _ else none) = none
      by_cases hck : Card.mk Suit.club Rank.king = c
      · rw [← hck, canPlace_king_false st hocc _ rfl b]
        rfl
      · have h2 : decide (Card.mk Suit.club Rank.king = c) = false :=
          decide_eq_false hck
        rw [h2, Bool.false_and]; rfl

/-! ## THE DIAMOND — the doubled-king misfire corner

The foundations miscount: hearts hold `A..J` (the `♥Q` is next
up), spades hold `A..Q` (the `♠K` is next up), diamonds and clubs
sit empty; `♠K` is doubled — a bare copy on the emptied anchor
`p1` and the seat copy under `♥Q` at `p5`.  Conservation is off by
the double (`cardCount ♠K = 2`); `WF` is never claimed. -/

private def dFoundO : Suit → List Card
  | .heart => (Rank.all.take 11).map (Card.mk Suit.heart)
  | .spade => (Rank.all.take 12).map (Card.mk Suit.spade)
  | _ => ([] : List Card)

/-- Hearts at `A..Q` (the queen has ascended at move one). -/
private def dFoundQ : Suit → List Card
  | .heart => (Rank.all.take 12).map (Card.mk Suit.heart)
  | .spade => (Rank.all.take 12).map (Card.mk Suit.spade)
  | _ => ([] : List Card)

/-- Hearts at `A..Q`, spades complete (the doubled king has
ascended at move two). -/
private def dFoundS : Suit → List Card
  | .heart => (Rank.all.take 12).map (Card.mk Suit.heart)
  | .spade => Rank.all.map (Card.mk Suit.spade)
  | _ => ([] : List Card)

/-- Hearts at `A..J`, spades complete (the queen is re-seated at
move three). -/
private def dFoundT : Suit → List Card
  | .heart => (Rank.all.take 11).map (Card.mk Suit.heart)
  | .spade => Rank.all.map (Card.mk Suit.spade)
  | _ => ([] : List Card)

private def dPiles0 : Anchor → Pile
  | .p1 => ⟨[], [S .king]⟩
  | .p5 => ⟨[], [S .king, H .queen]⟩
  | _ => ePile

private def dPiles1 : Anchor → Pile
  | .p1 => ⟨[], [S .king]⟩
  | .p5 => ⟨[], [S .king]⟩
  | _ => ePile

private def dPiles2 : Anchor → Pile
  | .p5 => ⟨[], [S .king]⟩
  | _ => ePile

private def dPiles3 : Anchor → Pile
  | .p5 => ⟨[], [S .king, H .queen]⟩
  | _ => ePile

/-- The one-move mirror's landing: the queen misplaced on the
bare double at `p1`. -/
private def dPilesM : Anchor → Pile
  | .p1 => ⟨[], [S .king, H .queen]⟩
  | .p5 => ⟨[], [S .king]⟩
  | _ => ePile

/-- The diadem corner: `♠K` doubled between an empty anchor and a
queen's seat, foundations miscounted to make both ascents live. -/
def diadem : State := mkFz dFoundO dPiles0

/-- After `tabToFound ♥Q`: the twin king at `p5` surfaces. -/
def diadem₁ : State := mkFz dFoundQ dPiles1

/-- After `tabToFound ♠K` (the bare copy, by the misfired search):
`p1` is empty; spades complete. -/
def diadem₂ : State := mkFz dFoundS dPiles2

/-- After `foundToTab ♥Q (inr ♠K)`: the queen re-seated on the
twin king. -/
def diadem₃ : State := mkFz dFoundT dPiles3

/-- The one-move mirror's actual landing. -/
def diademMirror : State := mkFz dFoundO dPilesM

/-- The disputed move. -/
def dMove : Move := .tabToFound (H .queen)

/-- The three-move shuttle out of the successor. -/
def dShuttle : List Move :=
  [.tabToFound (S .king), .foundToTab (H .queen) (Sum.inr (S .king)),
   .foundToTab (S .king) (Sum.inl Anchor.p1)]

/-- The full four-move returning play. -/
def dPlay : List Move := dMove :: dShuttle

/-! ### The diadem verdicts (decide-graded) -/

/-- The corner is wild: the doubled `♠K` breaks the conservation
count (two in the tableau between `p1`/`p5`, none in a
foundation). -/
theorem diadem_notWF : ¬ diadem.WF := by
  intro hwf
  have hcc := hwf.2.2.1 (S .king) (Card.mem_universe _)
  rw [show diadem.cardCount (S .king) = 2 from by decide] at hcc
  exact absurd hcc (by omega)

/-- The static seat fit holds: this is what a guard-only analysis
sees. -/
theorem diadem_sit : canSitOn (H .queen) (S .king) = true := by decide

theorem diadem_step : diadem.step dMove = some diadem₁ := by decide

/-- The misfire, verbatim: at the successor the pile-top search
for `♠K` pins `p1` — the empty-anchor double — and NOT the source
seat `p5`. -/
theorem diadem_search_misfires :
    diadem₁.pileOfTop (S .king) = some Anchor.p1 ∧
      diadem₁.pileOfTop (S .king) ≠ some Anchor.p5 := by
  refine ⟨by decide, ?_⟩
  decide

/-- The one-move mirror (the `foundToTab` family's candidate undo)
lands the queen on the wrong pile and does not return the origin. -/
theorem diadem_mirror_misfired :
    diadem₁.step (.foundToTab (H .queen) (Sum.inr (S .king))) = some diademMirror ∧
      (diademMirror.piles Anchor.p1).faceUp = [S .king, H .queen] ∧
      (diademMirror.piles Anchor.p5).faceUp = [S .king] ∧
      diademMirror ≠ diadem := by
  refine ⟨by decide, by decide, by decide, ?_⟩
  decide

/-- The shuttle: king up (the bare copy, pinned by the very
misfired search), queen re-seated on the twin king, king back to
the emptied anchor — `diadem` restored exactly. -/
theorem diadem_shuttleReturns : diadem₁.run dShuttle = some diadem := by decide

/-- The full four-move play, for the census. -/
theorem diadem_playReturns : diadem.run dPlay = some diadem := by decide

/-- **VERDICT A (the diadem):** at the wild doubled corner the
under-undo premise family reads dead (the successor search pins
the wrong copy; the one-move mirror misses) while the disputed
move is semantically reversible through the three-move shuttle. -/
theorem diadem_reversibleW : reversibleAtW diadem dMove :=
  ⟨diadem₁, dShuttle, diadem_step, diadem_shuttleReturns⟩

/-- The packed diadem exhibit. -/
theorem exhibit_diadem :
    ¬ diadem.WF ∧
    canSitOn (H .queen) (S .king) = true ∧
    (diadem₁.pileOfTop (S .king) = some Anchor.p1 ∧
      diadem₁.pileOfTop (S .king) ≠ some Anchor.p5) ∧
    reversibleAtW diadem dMove :=
  ⟨diadem_notWF, diadem_sit, diadem_search_misfires, diadem_reversibleW⟩

/-! ## THE FREEZER — the frozen successor corner

Complete foundations, empty stock and waste, five hidden-card
guard piles, and two live piles: the source `[♦6, ♥5]` and the
landing `[♠6]`.  The under-shaped move `tabToTab ♥5 (inr ♠6)`
fires (red on black, rank five on six) and leaves the board
frozen: nothing ascends (complete foundations), nothing descends
(kings cannot be placed — no empty seats, no card sits thirteen),
nothing moves on the tableau (the surviving fit `♥5` on `♦6` dies
red-on-red, and the tops `♦6`/`♥5` rank-block everything else),
and the draw and waste arms are dead on the empty zones. -/

private def fzFound : Suit → List Card := fun s => Rank.all.map (Card.mk s)

private def fzPiles : Anchor → Pile
  | .p0 => gPile (C .two)
  | .p1 => gPile (H .two)
  | .p2 => gPile (D .two)
  | .p3 => ⟨[], [D .six, H .five]⟩
  | .p4 => gPile (C .nine)
  | .p5 => gPile (H .nine)
  | .p6 => ⟨[], [S .six]⟩

private def fzPilesOut : Anchor → Pile
  | .p0 => gPile (C .two)
  | .p1 => gPile (H .two)
  | .p2 => gPile (D .two)
  | .p3 => ⟨[], [D .six]⟩
  | .p4 => gPile (C .nine)
  | .p5 => gPile (H .nine)
  | .p6 => ⟨[], [S .six, H .five]⟩

/-- The freezer corner: wild-stacked (five table cards on top of
four complete foundations — forty-plus phantom duplicates;
`cardCount` off everywhere). -/
def freezer : State := mkFz fzFound fzPiles

/-- The frozen successor. -/
def fzOut : State := mkFz fzFound fzPilesOut

/-- The noreveal-look under-row move. -/
def fzMove : Move := .tabToTab (H .five) (Sum.inr (S .six))

/-! ### The freezer verdicts -/

theorem freezer_step : freezer.step fzMove = some fzOut := by decide

/-- The corner is wild: the `♥5` sits both in the complete heart
foundation and on the landing pile. -/
theorem freezer_notWF : ¬ freezer.WF := by
  intro hwf
  have hcc := hwf.2.2.1 (H .five) (Card.mem_universe _)
  rw [show freezer.cardCount (H .five) = 2 from by decide] at hcc
  exact absurd hcc (by omega)

/-- The oracle's own reading at the wild corner: the under shape
says *reversible*. -/
theorem freezer_oracleReads :
    irreversibleOf freezer fzMove = false := by
  rfl

private theorem fz_foundFull (s : Suit) : (fzOut.found s).length = 13 := by
  cases s <;> rfl

private theorem fz_foundTop (s : Suit) :
    fzOut.foundTop s = some (Card.mk s Rank.king) := by
  cases s <;> rfl

private theorem fz_occ (a : Anchor) : ¬ (fzOut.piles a).isEmpty := by
  cases a <;> decide

private theorem fz_topChar (z : Card) (h : fzOut.pileOfTop z ≠ none) :
    z = D .six ∨ z = H .five := by
  obtain ⟨a, ha⟩ : ∃ a, fzOut.topOf a = some z := by
    cases hp : fzOut.pileOfTop z with
    | none => exact absurd hp h
    | some a => exact ⟨a, pileOfTop_some hp⟩
  cases a with
  | p0 =>
      exact absurd ha (by
        show (fzOut.topOf Anchor.p0) ≠ some z
        intro hc
        nomatch hc)
  | p1 =>
      exact absurd ha (by
        show (fzOut.topOf Anchor.p1) ≠ some z
        intro hc
        nomatch hc)
  | p2 =>
      exact absurd ha (by
        show (fzOut.topOf Anchor.p2) ≠ some z
        intro hc
        nomatch hc)
  | p3 => exact Or.inl (Option.some.inj ha).symm
  | p4 =>
      exact absurd ha (by
        show (fzOut.topOf Anchor.p4) ≠ some z
        intro hc
        nomatch hc)
  | p5 =>
      exact absurd ha (by
        show (fzOut.topOf Anchor.p5) ≠ some z
        intro hc
        nomatch hc)
  | p6 => exact Or.inr (Option.some.inj ha).symm

private theorem fz_faceUp_disj {c : Card} {a : Anchor}
    (h : c ∈ (fzOut.piles a).faceUp) :
    c = D .six ∨ c = S .six ∨ c = H .five := by
  cases a with
  | p0 =>
      simp only [show (fzOut.piles Anchor.p0).faceUp = ([] : List Card) from rfl] at h
      exact absurd h (by simp)
  | p1 =>
      simp only [show (fzOut.piles Anchor.p1).faceUp = ([] : List Card) from rfl] at h
      exact absurd h (by simp)
  | p2 =>
      simp only [show (fzOut.piles Anchor.p2).faceUp = ([] : List Card) from rfl] at h
      exact absurd h (by simp)
  | p3 =>
      simp only [show (fzOut.piles Anchor.p3).faceUp = [D .six] from rfl] at h
      cases h with
      | head => simp
      | tail c3 h3 => cases h3
  | p4 =>
      simp only [show (fzOut.piles Anchor.p4).faceUp = ([] : List Card) from rfl] at h
      exact absurd h (by simp)
  | p5 =>
      simp only [show (fzOut.piles Anchor.p5).faceUp = ([] : List Card) from rfl] at h
      exact absurd h (by simp)
  | p6 =>
      simp only [show (fzOut.piles Anchor.p6).faceUp = [S .six, H .five] from rfl] at h
      cases h with
      | head => simp
      | tail c3 h2 =>
          cases h2 with
          | head => simp
          | tail c4 h3 => cases h3

/-- The fit matrix at the frozen successor is dead: the only
rank-correct pairings are red-on-red. -/
private theorem fz_fit_dead (c z : Card)
    (hc : c = D .six ∨ c = S .six ∨ c = H .five)
    (hz : z = D .six ∨ z = H .five) (hfit : canSitOn c z = true) : False := by
  rcases hc with rfl | rfl | rfl <;> rcases hz with rfl | rfl <;>
    exact absurd hfit (by decide)

/-- **The frozen successor**: no legal move at all fires out of
`fzOut`. -/
theorem fz_frozen (m : Move) : fzOut.step m = none := by
  cases m with
  | draw => exact draw_dead fzOut rfl rfl
  | wasteToFound c => exact waste_found_dead fzOut rfl c
  | wasteToTab c b => exact waste_tab_dead fzOut rfl c b
  | tabToFound c =>
      rw [step_t2f_eq, nextUp_false_of_full fzOut fz_foundFull c]
      rfl
  | foundToTab c b => exact foundToTab_kings fzOut fz_foundTop fz_occ c b
  | tabToTab c b =>
      cases h' : fzOut.step (.tabToTab c b) with
      | none => rfl
      | some t =>
          exfalso
          have hstep : fzOut.step (.tabToTab c b) = some t := h'
          rw [step_t2t_eq] at hstep
          cases hh : fzOut.pileHolding c with
          | none => rw [hh] at hstep; simp at hstep
          | some a =>
              rw [hh] at hstep
              cases hcp : fzOut.canPlace c b with
              | false => rw [hcp] at hstep; simp at hstep
              | true =>
                  rw [hcp] at hstep
                  have hmem : c ∈ (fzOut.piles a).faceUp := pileHolding_some hh
                  cases b with
                  | inl a0 =>
                      rw [canPlace_inl_eq] at hcp
                      have hio : (fzOut.piles a0).isEmpty = false := by
                        cases hio : (fzOut.piles a0).isEmpty with
                        | true => exact (fz_occ a0 hio).elim
                        | false => rfl
                      rw [hio] at hcp; simp at hcp
                  | inr z =>
                      rw [canPlace_inr_eq] at hcp
                      cases hpt : fzOut.pileOfTop z with
                      | none => rw [hpt] at hcp; simp at hcp
                      | some k =>
                          rw [hpt] at hcp
                          exact fz_fit_dead c z (fz_faceUp_disj hmem)
                            (fz_topChar z (by rw [hpt]; simp)) hcp

private theorem fz_out_ne : fzOut ≠ freezer := by decide

/-- No play out of the frozen successor ever returns anything:
each step dies at the first move, and the empty play returns the
frozen board itself. -/
private theorem fz_run_never : ∀ (play : List Move),
    fzOut.run play ≠ some freezer := by
  intro play
  induction play with
  | nil =>
      intro hrun
      have hr0 : fzOut.run [] = some fzOut := rfl
      rw [hr0] at hrun
      exact fz_out_ne (Option.some.inj hrun)
  | cons m rest ih =>
      intro hrun
      obtain ⟨s₁, hstep, -⟩ := State.run_cons hrun
      rw [fz_frozen m] at hstep
      exact absurd hstep (by simp)

/-- **VERDICT B (the freezer):** the successful noreveal-shaped
under-row move lands on a frozen successor, so no play returns:
the move is semantically irreversible while its guard shape reads
reversible. -/
theorem freezer_irreversible : irreversibleAt freezer fzMove := by
  intro s₁ play hstep hrun
  have hs₁ : fzOut = s₁ := Option.some.inj (freezer_step.symm.trans hstep)
  subst hs₁
  exact fz_run_never play hrun

/-- The premiseless universal iff between the semantic predicate
and the assembled Bool oracle is refuted: at the freezer the two
disagree. -/
theorem wk_irreversibleOf_premiseless_false :
    ¬ (∀ st m, irreversibleAt st m ↔ irreversibleOf st m = true) := by
  intro hall
  have h := (hall freezer fzMove).mp freezer_irreversible
  rw [freezer_oracleReads] at h
  exact absurd h (by simp)

/-- The packed freezer exhibit. -/
theorem exhibit_freezer :
    ¬ freezer.WF ∧
    (freezer.step fzMove = some fzOut ∧ irreversibleOf freezer fzMove = false) ∧
    irreversibleAt freezer fzMove ∧
    ¬ (∀ st m, irreversibleAt st m ↔ irreversibleOf st m = true) :=
  ⟨freezer_notWF, ⟨freezer_step, freezer_oracleReads⟩, freezer_irreversible,
    wk_irreversibleOf_premiseless_false⟩

/-! ## The census battery (deterministic `#eval` probes)

DEDUP note: `moveCase`/`allMoves` are local copies of the
OrigExchange witness census helpers. -/

private def moveCase (st : State) (m : Move) : List (Move × State) :=
  match st.step m with
  | some t => [(m, t)]
  | none => []

private def allMoves (st : State) : List (Move × State) :=
  moveCase st .draw
  ++ (Card.universe.flatMap fun c =>
        moveCase st (.wasteToFound c) ++ moveCase st (.tabToFound c))
  ++ ((Card.universe.flatMap fun c => Anchor.all.map fun a => (c, Sum.inl a))
      ++ (Card.universe.flatMap fun c => Card.universe.map fun z => (c, Sum.inr z))
      ).flatMap fun cb =>
        match cb with
        | (c, b) =>
            moveCase st (.wasteToTab c b) ++ moveCase st (.foundToTab c b)
              ++ moveCase st (.tabToTab c b)

/-- info: 0 -/
#guard_msgs in
#eval (allMoves fzOut).length

/-- info: some true -/
#guard_msgs in
#eval (diadem.run dPlay).map (· == diadem)

/-- info: some true -/
#guard_msgs in
#eval (diadem₁.pileOfTop (S .king)).map (· == Anchor.p1)

/-- info: some true -/
#guard_msgs in
#eval (diadem₁.step (.foundToTab (H .queen) (Sum.inr (S .king)))).map (fun s => (s.piles Anchor.p1).faceUp == [S .king, H .queen])

/-- info: 2 -/
#guard_msgs in
#eval diadem.cardCount (S .king)

/-- info: 2 -/
#guard_msgs in
#eval freezer.cardCount (H .five)

/- Axiom pins for the battery. -/
#print axioms ClassificationFork.exhibit_diadem
#print axioms ClassificationFork.diadem_reversibleW
#print axioms ClassificationFork.diadem_search_misfires
#print axioms ClassificationFork.diadem_mirror_misfired
#print axioms ClassificationFork.exhibit_freezer
#print axioms ClassificationFork.fz_frozen
#print axioms ClassificationFork.freezer_irreversible
#print axioms ClassificationFork.freezer_oracleReads
#print axioms ClassificationFork.wk_irreversibleOf_premiseless_false

end ClassificationFork
