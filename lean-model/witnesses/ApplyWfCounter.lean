import Klondike.Initial

/-!
# `apply_wf` witnesses #1 & #2 — repaired, now regression anchors

Witness #1 (the reveal arm, 2026-09-13): the trigger card `c` stays
sitting on the revealed card `r` (now *visible*), and the then-current
WF only grandfathered edges onto `topHidden` cards; the boundary had
just moved below `r`, so the `c→r` edge was left requiring
`canSitOn c r`, which no guard of `applyReveal` ensured.  Witness
`st0`: standard deal, fresh stock, empty foundations, boundary at
`a.toIdx` per pile, and the single visible edge `♥3` on the hidden
boundary `♥2` of pile p1 (exactly pile p1's dealt shape).  Then
`reveal ♥3` was legal and the successor was not WF.

Witness #2 (the deckPile arm): WF constrained only the *deal's* stock
(`Deal.WF`), never the state's cycle, so `stD` — the same shape with
the state's stock carrying `♥4` TWICE — was WF, and `deckPile ♥4`
spliced out one copy and turned the card visible while the second copy
stayed in the cycle, breaking `isVis → posOf = none`.

Both holes were closed by the 2026-09-13 WF/board_edges repairs
(FARM_MEMORY), and `apply_wf` is PROVEN — the old
`apply_wf_unsound`/`apply_wf_unsound_deckPile : False` theorems (which
cited the pre-repair shapes) are now false statements and have been
removed.  What remains is the *positive* regression: the old
counterexamples no longer escape the invariant — `st0.WF` holds under
the eleven-conjunct WF and its reveal successor is WF again
(`st1_wf`, via the proven `apply_wf`), while the duplicated cycle is
now rejected outright (`stD_not_wf`, the `noDupCards` half of
`stock_wf`).
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

/-- The witness is WF under the repaired eleven-conjunct invariant:
the `♥3`-on-`♥2` edge is deal-adjacent with `♥2` as pile p1's hidden
boundary (the buried-base clause's first disjunct), and the fresh
deal stock is duplicate-free and a sub-list of itself. -/
theorem st0_wf : st0.WF := by
  have hdw : Deal.standard.WF := Deal.ofList_wf Card.universe_length universe_noDup
  refine ⟨hdw, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a
    have h1 : (st0.deal.piles a).length = a.toIdx + 1 := hdw.1 a
    have h2 : st0.depths a = a.toIdx := rfl
    omega
  · intro b c h
    by_cases hbb : b = Sum.inr c2
    · subst hbb
      have hc3 : c = c3 := Option.some.inj (h.symm.trans st0_topOf_self)
      subst hc3
      refine ⟨(Board.bottomOf_eq _ _ _).mpr h, ?_⟩
      exact Or.inl ⟨Anchor.p1, [], [], by decide, Or.inl ⟨Anchor.p1, by decide⟩⟩
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
  · intro c hc
    have h0 : st0.heights c.suit = 0 := rfl
    omega
  · intro c hc a hca
    have hck : c = c3 := by
      simp only [State.isVis] at hc
      cases hb : st0.board.bottomOf c with
      | none => rw [hb] at hc; simp at hc
      | some b =>
          have htb : st0.board.topOf b = some c := (Board.bottomOf_eq _ _ _).mp hb
          by_cases hbb : b = Sum.inr c2
          · rw [hbb] at htb
            exact Option.some.inj (htb.symm.trans st0_topOf_self)
          · rw [st0_topOf_ne hbb] at htb
            simp at htb
    subst hck
    cases a <;> exact absurd hca (by decide)
  · intro s
    have : st0.heights s = 0 := rfl
    omega
  · exact Nat.zero_le _
  · exact Nat.zero_lt_one
  · refine ⟨?_, ?_⟩
    · intro i j hi hj heq
      have h24 : st0.stock.cards.length = 24 := by decide
      rw [h24] at hi hj
      have hall : ∀ i ∈ List.range 24, ∀ j ∈ List.range 24,
          st0.stock.cards[i]? = st0.stock.cards[j]? → i = j := by decide
      exact hall i (List.mem_range.mpr hi) j (List.mem_range.mpr hj) heq
    · intro c hcm
      exact hcm

/-- The countermodel's premise still holds (by the kernel): `reveal ♥3`
is legal at the witness. -/
theorem st0_apply : st0.apply (Move.reveal c3) = some st1 := by
  have his : (st0.apply (Move.reveal c3)).isSome = true := by decide
  cases h : st0.apply (Move.reveal c3) with
  | none =>
      rw [h] at his
      simp at his
  | some s =>
      have hw : st1 = s := by
        show (st0.apply (Move.reveal c3)).getD st0 = s
        rw [h]
        rfl
      rw [hw]

/-- THE REPAIR HOLDS: the old counterexample's reveal successor is WF.
Under the repaired invariant the `♥3`-on-`♥2` edge is justified by `♥2`
being seated on p1's anchor (`reveal` attaches the boundary before
anything can sit on it — exactly the deal-adjacency base clause). -/
theorem st1_wf : st1.WF :=
  apply_wf st0_wf _ _ st0_apply

/-! ## Witness #2 — the duplicated cycle, now rejected outright -/

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

/-- The old witness: cycle carries ♥4 twice; cursor past both. -/
def stD : State where
  deal := Deal.standard
  board := bdD
  heights := fun _ => 0
  depths := fun _ => 1
  stock := ⟨[d4, d4], 2⟩
  drawStep := 1

/-- The deckPile successor (computed by the kernel; kept as the
countermodel record). -/
def stD1 : State := (stD.apply (Move.deckPile d4 (Sum.inr s5))).getD stD

/-- The old witness is no longer WF: `stock_wf`'s `noDupCards` half
(the conjunct this witness forced, restored 2026-09-13) rejects the
duplicated cycle outright. -/
theorem stD_not_wf : ¬ stD.WF := by
  intro hwf
  have hnd : noDupCards [d4, d4] := hwf.stock_wf.1
  exact absurd (hnd 0 1 (by decide) (by decide) rfl) (by decide)

/-- The countermodel's premise still holds (by the kernel) — only the
WF side of the old refutation is gone. -/
example : (stD.apply (Move.deckPile d4 (Sum.inr s5))).isSome = true := by decide

/-- info: 'st0_wf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms st0_wf

/-- info: 'st1_wf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms st1_wf

/-- info: 'stD_not_wf' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms stD_not_wf
