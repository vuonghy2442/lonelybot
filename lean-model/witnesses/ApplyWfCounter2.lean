import Klondike.Initial

/-!
# Witness #3 — the landed WF repair does NOT close the reveal arm

The strengthened inr disjunct 1 (`∃ a, topHidden a = some d`) does not
force the sitting card to be deal-adjacent to `d`.  `reveal` leaves the
trigger card on the freshly-revealed card *as a visible-on-visible
edge*; absent adjacency (or `canSitOn`), no disjunct of the new clause
justifies it in the successor.

Witness: standard deal, depths 1 everywhere, board {inr ♥2 ↦ ♠9}
(♠9 sits on pile p1's hidden boundary — legal by disjunct 1 — but ♠9
was dealt in pile p6, not adjacent to ♥2), fresh stock.  Then
`reveal ♠9` is legal and the successor is not WF.
-/

/-- ♥2: pile p1's bottom card. -/
def c2 : Card := ⟨Suit.heart, Rank.two⟩

/-- ♠9: pile p6's bottom card. -/
def s9 : Card := ⟨Suit.spade, Rank.nine⟩

/-- ♠9 visible, sitting on pile p1's hidden boundary ♥2. -/
def bdE : Board where
  topOf := Board.update Board.empty.topOf (Sum.inr c2) (some s9)
  inj := Board.attach_inj Board.empty (Sum.inr c2) s9 (Board.empty_bottomOf s9)

/-- The witness state: boundary at 1 everywhere, fresh stock. -/
def stE : State where
  deal := Deal.standard
  board := bdE
  heights := fun _ => 0
  depths := fun _ => 1
  stock := ⟨Deal.standard.stock, 0⟩
  drawStep := 1

/-- The reveal successor (computed by the kernel). -/
def stE1 : State := (stE.apply (Move.reveal s9)).getD stE

theorem stE_topOf_self : stE.board.topOf (Sum.inr c2) = some s9 :=
  Board.update_self Board.empty.topOf (Sum.inr c2) (some s9)

theorem stE_topOf_ne {b : Base} (h : b ≠ Sum.inr c2) : stE.board.topOf b = none :=
  (Board.update_ne Board.empty.topOf (Sum.inr c2) b (some s9) h).trans (Board.empty_topOf b)

theorem stE_stock_noDup : noDupCards stE.stock.cards := by
  have hl : stE.stock.cards.length = 24 := by decide
  have hall : ∀ i ∈ List.range 24, ∀ j ∈ List.range 24,
      stE.stock.cards[i]? = stE.stock.cards[j]? → i = j := by decide
  intro i j hi hj heq
  rw [hl] at hi hj
  exact hall i (List.mem_range.mpr hi) j (List.mem_range.mpr hj) heq

theorem stE_wf : stE.WF := by
  have hdw : Deal.standard.WF := Deal.ofList_wf Card.universe_length Card.universe_noDup
  refine ⟨hdw, ?_, ?_, ?_, ?_, ?_, ?_, stE_stock_noDup⟩
  · intro a
    have h1 : (stE.deal.piles a).length = a.toIdx + 1 := hdw.1 a
    have h2 : stE.depths a = 1 := rfl
    omega
  · intro b c h
    by_cases hbb : b = Sum.inr c2
    · subst hbb
      have hcs : c = s9 := Option.some.inj (h.symm.trans stE_topOf_self)
      subst hcs
      refine ⟨by decide, Or.inl ⟨Anchor.p1, by decide⟩⟩
    · rw [stE_topOf_ne hbb] at h
      simp at h
  · intro c hc
    by_cases hcc : c = s9
    · subst hcc
      decide
    · have hb : stE.board.bottomOf c = none := by
        rw [Board.bottomOf_eq_none]
        intro b hb2
        by_cases hbb : b = Sum.inr c2
        · subst hbb
          exact hcc (Option.some.inj (hb2.symm.trans stE_topOf_self))
        · rw [stE_topOf_ne hbb] at hb2
          simp at hb2
      simp only [State.isVis] at hc
      rw [hb] at hc
      simp at hc
  · intro c hc
    simp only [State.onFound] at hc
    rw [show stE.heights c.suit = 0 from rfl, decide_eq_true_eq] at hc
    exact absurd hc (by omega)
  · intro s
    have : stE.heights s = 0 := rfl
    omega
  · exact Nat.zero_le _

theorem stE1_not_wf : ¬ stE1.WF := by
  intro hwf
  have h3 := hwf.2.2.1 (Sum.inr c2) s9
    (show stE1.board.topOf (Sum.inr c2) = some s9 from by decide)
  rcases h3.2 with ⟨a₂, ha₂⟩ | ⟨a₂, t, rest, heq⟩ | ⟨-, hcs⟩
  · exact (show ∀ a', stE1.topHidden a' ≠ some c2 from by
      intro a'; cases a' <;> decide) a₂ ha₂
  · have hc2 : c2 ∈ stE1.deal.piles a₂ := by rw [heq]; simp
    have hs9 : s9 ∈ stE1.deal.piles a₂ := by rw [heq]; simp
    cases a₂ with
    | p0 => exact absurd hc2 (by decide)
    | p1 => exact absurd hs9 (by decide)
    | p2 => exact absurd hc2 (by decide)
    | p3 => exact absurd hc2 (by decide)
    | p4 => exact absurd hc2 (by decide)
    | p5 => exact absurd hc2 (by decide)
    | p6 => exact absurd hc2 (by decide)
  · exact absurd hcs (show ¬ (canSitOn s9 c2 = true) from by decide)

theorem apply_wf_still_unsound_reveal :
    ¬ (∀ {st : State}, st.WF → ∀ (m : Move) (st' : State),
        st.apply m = some st' → st'.WF) := by
  intro haw
  have his : (stE.apply (Move.reveal s9)).isSome = true := by decide
  obtain ⟨st', hst'⟩ : ∃ st', stE.apply (Move.reveal s9) = some st' := by
    cases hap : stE.apply (Move.reveal s9) with
    | none => rw [hap] at his; simp at his
    | some s => exact ⟨s, rfl⟩
  have hwf' := haw stE_wf (Move.reveal s9) st' hst'
  have heq : st' = stE1 := by
    show st' = (stE.apply (Move.reveal s9)).getD stE
    rw [hst']
    rfl
  subst heq
  exact stE1_not_wf hwf'

#print axioms apply_wf_still_unsound_reveal

/-!
# Witness #4 — independent residual hole: stock ⊄ deal

WF constrains the deal's stock (`Deal.WF`) and the state's stock's
internal distinctness (`noDupCards st.stock.cards`), but never the
state's stock against the deal's PILES.  A boundary card that sits in
the state's stock becomes visible under `reveal` while remaining in
the stock — `isVis → posOf = none` breaks.

Witness: standard deal, depths 1, board {inr ♥2 ↦ ♥3} (deliberately
deal-adjacent, so the witness isolates this hole), stock ⟨[♥2, ♠9], 1⟩.
`reveal ♥3` is legal; the successor has ♥2 visible with
`posOf ♥2 = some 0`.
-/

/-- ♥3: pile p1's top dealt card (deal-adjacent to ♥2). -/
def c3 : Card := ⟨Suit.heart, Rank.three⟩

/-- The adjacent one-edge board: ♥3 on the hidden boundary ♥2. -/
def bdF : Board where
  topOf := Board.update Board.empty.topOf (Sum.inr c2) (some c3)
  inj := Board.attach_inj Board.empty (Sum.inr c2) c3 (Board.empty_bottomOf c3)

/-- WF witness: the stock carries the boundary card ♥2 itself. -/
def stF : State where
  deal := Deal.standard
  board := bdF
  heights := fun _ => 0
  depths := fun _ => 1
  stock := ⟨[c2, s9], 1⟩
  drawStep := 1

/-- The reveal successor (computed by the kernel). -/
def stF1 : State := (stF.apply (Move.reveal c3)).getD stF

theorem stF_topOf_self : stF.board.topOf (Sum.inr c2) = some c3 :=
  Board.update_self Board.empty.topOf (Sum.inr c2) (some c3)

theorem stF_topOf_ne {b : Base} (h : b ≠ Sum.inr c2) : stF.board.topOf b = none :=
  (Board.update_ne Board.empty.topOf (Sum.inr c2) b (some c3) h).trans (Board.empty_topOf b)

theorem stF_stock_noDup : noDupCards stF.stock.cards := by
  have hall : ∀ i ∈ List.range 2, ∀ j ∈ List.range 2,
      [c2, s9][i]? = [c2, s9][j]? → i = j := by decide
  have hl : stF.stock.cards.length = 2 := rfl
  intro i j hi hj heq
  rw [hl] at hi hj
  exact hall i (List.mem_range.mpr hi) j (List.mem_range.mpr hj) heq

theorem stF_wf : stF.WF := by
  have hdw : Deal.standard.WF := Deal.ofList_wf Card.universe_length Card.universe_noDup
  refine ⟨hdw, ?_, ?_, ?_, ?_, ?_, ?_, stF_stock_noDup⟩
  · intro a
    have h1 : (stF.deal.piles a).length = a.toIdx + 1 := hdw.1 a
    have h2 : stF.depths a = 1 := rfl
    omega
  · intro b c h
    by_cases hbb : b = Sum.inr c2
    · subst hbb
      have hc3 : c = c3 := Option.some.inj (h.symm.trans stF_topOf_self)
      subst hc3
      refine ⟨by decide, Or.inl ⟨Anchor.p1, by decide⟩⟩
    · rw [stF_topOf_ne hbb] at h
      simp at h
  · intro c hc
    by_cases hcc : c = c3
    · subst hcc
      decide
    · have hb : stF.board.bottomOf c = none := by
        rw [Board.bottomOf_eq_none]
        intro b hb2
        by_cases hbb : b = Sum.inr c2
        · subst hbb
          exact hcc (Option.some.inj (hb2.symm.trans stF_topOf_self))
        · rw [stF_topOf_ne hbb] at hb2
          simp at hb2
      simp only [State.isVis] at hc
      rw [hb] at hc
      simp at hc
  · intro c hc
    simp only [State.onFound] at hc
    rw [show stF.heights c.suit = 0 from rfl, decide_eq_true_eq] at hc
    exact absurd hc (by omega)
  · intro s
    have : stF.heights s = 0 := rfl
    omega
  · decide

theorem stF1_not_wf : ¬ stF1.WF := by
  intro hwf
  have h4 := hwf.2.2.2.1 c2 (show stF1.isVis c2 = true from by decide)
  have hne : stF1.stock.posOf c2 ≠ none := by decide
  rw [h4] at hne
  exact hne rfl

theorem apply_wf_still_unsound_stock :
    ¬ (∀ {st : State}, st.WF → ∀ (m : Move) (st' : State),
        st.apply m = some st' → st'.WF) := by
  intro haw
  have his : (stF.apply (Move.reveal c3)).isSome = true := by decide
  obtain ⟨st', hst'⟩ : ∃ st', stF.apply (Move.reveal c3) = some st' := by
    cases hap : stF.apply (Move.reveal c3) with
    | none => rw [hap] at his; simp at his
    | some s => exact ⟨s, rfl⟩
  have hwf' := haw stF_wf (Move.reveal c3) st' hst'
  have heq : st' = stF1 := by
    show st' = (stF.apply (Move.reveal c3)).getD stF
    rw [hst']
    rfl
  subst heq
  exact stF1_not_wf hwf'

#print axioms apply_wf_still_unsound_stock
