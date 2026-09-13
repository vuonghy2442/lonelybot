import Klondike.Initial

/-!
# `apply_wf` counterexample — scratch confirmation

Claim: `State.apply_wf` (Move.lean) is UNSOUND.  The `reveal` move keeps
the trigger card `c` sitting on the revealed card `r` (now *visible*),
but WF's third conjunct only grandfathers edges onto `topHidden`
cards; the boundary has just moved below `r`, so the `c→r` edge is left
requiring `canSitOn c r`, which no guard of `applyReveal` ensures.

Witness: standard deal, fresh stock, empty foundations, boundary at
`a.toIdx` per pile, and the single visible edge `♥3` on the hidden
boundary `♥2` of pile p1 (exactly pile p1's dealt shape).  Then
`reveal ♥3` is legal, and its successor is not WF.
-/

/-- ♥2: pile p1's top hidden card in the standard deal. -/
def c2 : Card := ⟨Suit.heart, Rank.two⟩

/-- ♥3: pile p1's top dealt card in the standard deal. -/
def c3 : Card := ⟨Suit.heart, Rank.three⟩

/-- The one-edge board: ♥3 visible, sitting on the hidden boundary ♥2. -/
def bd1 : Board where
  topOf := Board.update Board.empty.topOf (Sum.inr c2) (some c3)
  inj := Board.attach_inj Board.empty (Sum.inr c2) c3 (Board.empty_bottomOf c3)

/-- The witness state. -/
def st0 : State where
  deal := Deal.standard
  board := bd1
  heights := fun _ => 0
  depths := fun a => a.toIdx
  stock := ⟨Deal.standard.stock, 0⟩
  drawStep := 1

/-- The reveal successor (computed by the kernel). -/
def st1 : State := (st0.apply (Move.reveal c3)).getD st0

theorem st0_topOf_self : st0.board.topOf (Sum.inr c2) = some c3 :=
  Board.update_self Board.empty.topOf (Sum.inr c2) (some c3)

theorem st0_topOf_ne {b : Base} (h : b ≠ Sum.inr c2) : st0.board.topOf b = none :=
  (Board.update_ne Board.empty.topOf (Sum.inr c2) b (some c3) h).trans (Board.empty_topOf b)

theorem st0_wf : st0.WF := by
  have hdw : Deal.standard.WF := Deal.ofList_wf Card.universe_length Card.universe_noDup
  refine ⟨hdw, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a
    have h1 : (st0.deal.piles a).length = a.toIdx + 1 := hdw.1 a
    have h2 : st0.depths a = a.toIdx := rfl
    omega
  · intro b c h
    by_cases hbb : b = Sum.inr c2
    · subst hbb
      have hc3 : c = c3 := Option.some.inj (h.symm.trans st0_topOf_self)
      subst hc3
      refine ⟨by decide, Or.inl ⟨Anchor.p1, by decide⟩⟩
    · rw [st0_topOf_ne hbb] at h
      simp at h
  · intro c hc
    by_cases hcc : c = c3
    · subst hcc
      decide
    · have hb : st0.board.bottomOf c = none := by
        rw [Board.bottomOf_eq_none]
        intro b hb2
        by_cases hbb : b = Sum.inr c2
        · subst hbb
          exact hcc (Option.some.inj (hb2.symm.trans st0_topOf_self))
        · rw [st0_topOf_ne hbb] at hb2
          simp at hb2
      simp only [State.isVis] at hc
      rw [hb] at hc
      simp at hc
  · intro c hc
    simp only [State.onFound] at hc
    rw [show st0.heights c.suit = 0 from rfl, decide_eq_true_eq] at hc
    exact absurd hc (by omega)
  · intro s
    have : st0.heights s = 0 := rfl
    omega
  · exact Nat.zero_le _

theorem st1_not_wf : ¬ st1.WF := by
  intro hwf
  have h3 := hwf.2.2.1 (Sum.inr c2) c3
    (show st1.board.topOf (Sum.inr c2) = some c3 from by decide)
  rcases h3.2 with ⟨a', ha'⟩ | ⟨-, hcs⟩
  · exact (show ∀ a', st1.topHidden a' ≠ some c2 from by
      intro a'; cases a' <;> decide) a' ha'
  · exact absurd hcs (show ¬ (canSitOn c3 c2 = true) from by decide)

theorem apply_wf_unsound :
    ¬ (∀ {st : State}, st.WF → ∀ (m : Move) (st' : State),
        st.apply m = some st' → st'.WF) := by
  intro haw
  have his : (st0.apply (Move.reveal c3)).isSome = true := by decide
  obtain ⟨st', hst'⟩ : ∃ st', st0.apply (Move.reveal c3) = some st' := by
    cases hap : st0.apply (Move.reveal c3) with
    | none => rw [hap] at his; simp at his
    | some s => exact ⟨s, rfl⟩
  have hwf' := haw st0_wf (Move.reveal c3) st' hst'
  have heq : st' = st1 := by
    show st' = (st0.apply (Move.reveal c3)).getD st0
    rw [hst']
    rfl
  subst heq
  exact st1_not_wf hwf'

/-!
## Second hole: `deckPile` on a duplicate cycle

`WF` constrains only the *deal's* stock (`Deal.WF`), never the state's
cycle; a WF state may carry a duplicated card in `st.stock.cards`.
`deckPile` splices out one copy and turns the card visible — the
second copy stays in the cycle, violating WF's `isVis → posOf = none`.
-/

/-- ♥4. -/
def d4 : Card := ⟨Suit.heart, Rank.four⟩

/-- ♠5. -/
def s5 : Card := ⟨Suit.spade, Rank.five⟩

/-- ♥A: pile p0's only card. -/
def hA : Card := ⟨Suit.heart, Rank.ace⟩

/-- ♠5 visible, sitting on pile p0's hidden boundary ♥A. -/
def bdD : Board where
  topOf := Board.update Board.empty.topOf (Sum.inr hA) (some s5)
  inj := Board.attach_inj Board.empty (Sum.inr hA) s5 (Board.empty_bottomOf s5)

/-- WF witness: cycle carries ♥4 twice; cursor past both. -/
def stD : State where
  deal := Deal.standard
  board := bdD
  heights := fun _ => 0
  depths := fun _ => 1
  stock := ⟨[d4, d4], 2⟩
  drawStep := 1

/-- The deckPile successor (computed by the kernel). -/
def stD1 : State := (stD.apply (Move.deckPile d4 (Sum.inr s5))).getD stD

theorem stD_topOf_self : stD.board.topOf (Sum.inr hA) = some s5 :=
  Board.update_self Board.empty.topOf (Sum.inr hA) (some s5)

theorem stD_topOf_ne {b : Base} (h : b ≠ Sum.inr hA) : stD.board.topOf b = none :=
  (Board.update_ne Board.empty.topOf (Sum.inr hA) b (some s5) h).trans (Board.empty_topOf b)

theorem stD_wf : stD.WF := by
  have hdw : Deal.standard.WF := Deal.ofList_wf Card.universe_length Card.universe_noDup
  refine ⟨hdw, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a
    have h1 : (stD.deal.piles a).length = a.toIdx + 1 := hdw.1 a
    have h2 : stD.depths a = 1 := rfl
    omega
  · intro b c h
    by_cases hbb : b = Sum.inr hA
    · subst hbb
      have hc5 : c = s5 := Option.some.inj (h.symm.trans stD_topOf_self)
      subst hc5
      refine ⟨by decide, Or.inl ⟨Anchor.p0, by decide⟩⟩
    · rw [stD_topOf_ne hbb] at h
      simp at h
  · intro c hc
    by_cases hcc : c = s5
    · subst hcc
      decide
    · have hb : stD.board.bottomOf c = none := by
        rw [Board.bottomOf_eq_none]
        intro b hb2
        by_cases hbb : b = Sum.inr hA
        · subst hbb
          exact hcc (Option.some.inj (hb2.symm.trans stD_topOf_self))
        · rw [stD_topOf_ne hbb] at hb2
          simp at hb2
      simp only [State.isVis] at hc
      rw [hb] at hc
      simp at hc
  · intro c hc
    simp only [State.onFound] at hc
    rw [show stD.heights c.suit = 0 from rfl, decide_eq_true_eq] at hc
    exact absurd hc (by omega)
  · intro s
    have : stD.heights s = 0 := rfl
    omega
  · decide

theorem stD1_not_wf : ¬ stD1.WF := by
  intro hwf
  have h4 := hwf.2.2.2.1 d4 (show stD1.isVis d4 = true from by decide)
  have hne : stD1.stock.posOf d4 ≠ none := by decide
  rw [h4] at hne
  exact hne rfl

theorem apply_wf_unsound_deckPile :
    ¬ (∀ {st : State}, st.WF → ∀ (m : Move) (st' : State),
        st.apply m = some st' → st'.WF) := by
  intro haw
  have his : (stD.apply (Move.deckPile d4 (Sum.inr s5))).isSome = true := by decide
  obtain ⟨st', hst'⟩ : ∃ st', stD.apply (Move.deckPile d4 (Sum.inr s5)) = some st' := by
    cases hap : stD.apply (Move.deckPile d4 (Sum.inr s5)) with
    | none => rw [hap] at his; simp at his
    | some s => exact ⟨s, rfl⟩
  have hwf' := haw stD_wf (Move.deckPile d4 (Sum.inr s5)) st' hst'
  have heq : st' = stD1 := by
    show st' = (stD.apply (Move.deckPile d4 (Sum.inr s5))).getD stD
    rw [hst']
    rfl
  subst heq
  exact stD1_not_wf hwf'
#print axioms apply_wf_unsound
#print axioms apply_wf_unsound_deckPile
