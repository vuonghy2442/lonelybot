import Klondike.Initial

/-!
# Witness #5 — the membership conjunct does NOT subsume noDupCards

WF's final conjunct (`∀ c ∈ st.stock.cards, c ∈ st.deal.stock`) sees
where stock cards come from, not how many times: a state stock
listing a deal-stock card TWICE satisfies it.  `deckPile` splices out
one copy and turns the card visible — the second copy stays in the
cycle, breaking `isVis → posOf = none`.

Witness: standard deal, depths 1, board {inr ♠3 ↦ ♠4} (deal-adjacent
edge of pile p5), stock ⟨[♢3, ♢3], 2⟩.  `deckPile ♢3 (inr ♠4)` is
legal; the successor has ♢3 visible with `posOf ♢3 = some 0`.
-/

/-- ♠3: pile p5's bottom card. -/
def s3 : Card := ⟨Suit.spade, Rank.three⟩

/-- ♠4: dealt directly on ♠3. -/
def s4 : Card := ⟨Suit.spade, Rank.four⟩

def s5c : Card := ⟨Suit.spade, Rank.five⟩
def s6c : Card := ⟨Suit.spade, Rank.six⟩
def s7c : Card := ⟨Suit.spade, Rank.seven⟩
def s8c : Card := ⟨Suit.spade, Rank.eight⟩

/-- ♢3: a deal-stock card. -/
def d3 : Card := ⟨Suit.diamond, Rank.three⟩

/-- ♠4 visible, sitting on its dealt parent ♠3. -/
def bd5 : Board where
  topOf := Board.update Board.empty.topOf (Sum.inr s3) (some s4)
  inj := Board.attach_inj Board.empty (Sum.inr s3) s4 (Board.empty_bottomOf s4)

/-- WF witness: the stock lists ♢3 twice (membership holds). -/
def st5 : State where
  deal := Deal.standard
  board := bd5
  heights := fun _ => 0
  depths := fun _ => 1
  stock := ⟨[d3, d3], 2⟩
  drawStep := 1

/-- The deckPile successor (computed by the kernel). -/
def st51 : State := (st5.apply (Move.deckPile d3 (Sum.inr s4))).getD st5

theorem st5_topOf_self : st5.board.topOf (Sum.inr s3) = some s4 :=
  Board.update_self Board.empty.topOf (Sum.inr s3) (some s4)

theorem st5_topOf_ne {b : Base} (h : b ≠ Sum.inr s3) : st5.board.topOf b = none :=
  (Board.update_ne Board.empty.topOf (Sum.inr s3) b (some s4) h).trans (Board.empty_topOf b)

theorem st5_wf : st5.WF := by
  have hdw : Deal.standard.WF := Deal.ofList_wf Card.universe_length Card.universe_noDup
  refine ⟨hdw, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a
    have h1 : (st5.deal.piles a).length = a.toIdx + 1 := hdw.1 a
    have h2 : st5.depths a = 1 := rfl
    omega
  · intro b c h
    by_cases hbb : b = Sum.inr s3
    · subst hbb
      have hcs : c = s4 := Option.some.inj (h.symm.trans st5_topOf_self)
      subst hcs
      refine ⟨by decide, Or.inl ⟨Anchor.p5, [], [s5c, s6c, s7c, s8c], by decide⟩⟩
    · rw [st5_topOf_ne hbb] at h
      simp at h
  · intro c hc
    by_cases hcc : c = s4
    · subst hcc
      decide
    · have hb : st5.board.bottomOf c = none := by
        rw [Board.bottomOf_eq_none]
        intro b hb2
        by_cases hbb : b = Sum.inr s3
        · subst hbb
          exact hcc (Option.some.inj (hb2.symm.trans st5_topOf_self))
        · rw [st5_topOf_ne hbb] at hb2
          simp at hb2
      simp only [State.isVis] at hc
      rw [hb] at hc
      simp at hc
  · intro c hc
    simp only [State.onFound] at hc
    rw [show st5.heights c.suit = 0 from rfl, decide_eq_true_eq] at hc
    exact absurd hc (by omega)
  · intro s
    have : st5.heights s = 0 := rfl
    omega
  · decide
  · intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · decide
    · rcases List.mem_cons.mp hc with rfl | hc
      · decide
      · cases hc

theorem st51_not_wf : ¬ st51.WF := by
  intro hwf
  have h4 := hwf.2.2.2.1 d3 (show st51.isVis d3 = true from by decide)
  have hne : st51.stock.posOf d3 ≠ none := by decide
  rw [h4] at hne
  exact hne rfl

theorem apply_wf_unsound_dup_stock :
    ¬ (∀ {st : State}, st.WF → ∀ (m : Move) (st' : State),
        st.apply m = some st' → st'.WF) := by
  intro haw
  have his : (st5.apply (Move.deckPile d3 (Sum.inr s4))).isSome = true := by decide
  obtain ⟨st', hst'⟩ : ∃ st', st5.apply (Move.deckPile d3 (Sum.inr s4)) = some st' := by
    cases hap : st5.apply (Move.deckPile d3 (Sum.inr s4)) with
    | none => rw [hap] at his; simp at his
    | some s => exact ⟨s, rfl⟩
  have hwf' := haw st5_wf (Move.deckPile d3 (Sum.inr s4)) st' hst'
  have heq : st' = st51 := by
    show st' = (st5.apply (Move.deckPile d3 (Sum.inr s4))).getD st5
    rw [hst']
    rfl
  subst heq
  exact st51_not_wf hwf'

#print axioms apply_wf_unsound_dup_stock
