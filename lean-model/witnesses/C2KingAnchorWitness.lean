import Klondike.C2Streamlined

/-!
# The king-anchor witness — the unstackable landing split

The wave-17 C2 pillar set claimed, among its five play-level
universals, that successors through the same channel pin are
closure-equal (`same_pin_closureEq`), that every `P2Safe`-labeled
successor joins the direct commit's class (`p2_direct_class`), that
sublist-chained accommodations absorb (`crease_chain_absorbed`), and
the main two-option bound itself (`c2_two_option`).  All four are
FALSE in the free model semantics, and this file is the prover-confirmed
countermodel witness in the FARM.md REFUTED-protocol form:

* the state `wState` is WF (standard deal shape, empty board, all
  foundations at 0) and carries the king `♠K` in the stock — a
  **climb-blocked** king: no spade is founded or seated anywhere, so
  no accommodation move ever raises the spade height, and `pileStack
  ♠K` (rung 12, standing height 0) is dead along every closure walk;
* the `Draw(♠K)` commitment has, at `wState`, SEVEN distinct tableau
  successors — one per free anchor — and any two of them are
  closure-SEPARATED: the landed king can never leave its anchor by
  accommodation moves (only `pileStack` ever unseats a card), so no
  pure `pileStack`/`stackPile` play reconciles two different landings;
* `wk_c2_as_stated_false`, `wk_same_pin_as_stated_false`,
  `wk_p2_direct_as_stated_false` and `wk_crease_as_stated_false`
  each negate the as-stated universal in the spelling the library
  carried at the 2026-10-05 wave-12/17 merge, using only constants
  that survive the pillar restructure — the negations are permanent
  regression records.  The four universal claims left the library
  with the C2-closure session; see FARM.md's REFUTED section, and
  `Klondike.C2.commitTableau_class` for the surviving PROVEN half of
  the destination collapse — the stackable-rung regime, where the
  join is the two-move foundation shuttle.

Why the engine corpus never saw this: the engine recorded the
canonicalized (safe-sweep-merged) outcome samples, and a drawn card
that is stackable at its rung — the regime `commitTableau_class`
covers — has every landing swept to the same post-state.  The
climb-blocked stocked king with several free anchors lives outside
that regime; the 200-game corpus happened never to present one with
three landings taken.
-/

open Klondike.C2

namespace KingAnchor

/-- Spades. -/
private def S (r : Rank) : Card := ⟨Suit.spade, r⟩
/-- Hearts. -/
private def H (r : Rank) : Card := ⟨Suit.heart, r⟩
/-- Diamonds. -/
private def D (r : Rank) : Card := ⟨Suit.diamond, r⟩
/-- Clubs. -/
private def C (r : Rank) : Card := ⟨Suit.club, r⟩

/-- The stock slice — the state's cycle cards are the very same
list, which makes `stock_wf`'s membership half reflexivity. -/
private def wStockList : List Card :=
  [S .king, H .king, D .king, C .king] ++
  [C .ace, C .two, C .three, C .four, C .five, C .six, C .seven, C .eight,
   C .nine, C .ten, C .jack, C .queen] ++
  [D .five, D .six, D .seven, D .eight, D .nine, D .ten, D .jack, D .queen]

/-- The witness deal: 28 pile cards (1+2+…+7), 24 stock cards, all 52
distinct.  The pile content is never consulted below — with an empty
board and zero depths the pile cards sit in no zone of the game. -/
private def wDeal : Deal where
  piles := fun a =>
    match a with
    | .p0 => [S .ace]
    | .p1 => [S .two, S .three]
    | .p2 => [S .four, S .five, S .six]
    | .p3 => [S .seven, S .eight, S .nine, S .ten]
    | .p4 => [S .jack, S .queen, H .ace, H .two, H .three]
    | .p5 => [H .four, H .five, H .six, H .seven, H .eight, H .nine]
    | .p6 => [H .ten, H .jack, H .queen, D .ace, D .two, D .three, D .four]
  stock := wStockList

/-- The witness state: pristine — empty board, zero heights, zero
depths, the full spade-blocked stock, draw step 1. -/
private def wState : State where
  deal := wDeal
  board := Board.empty
  heights := fun _ => 0
  depths := fun _ => 0
  stock := ⟨wStockList, 0⟩
  drawStep := 1

/-! ## The state is WF -/

private theorem wDeal_wf : wDeal.WF := by
  refine ⟨fun a => ?_, by decide, ?_⟩
  · cases a <;> decide
  · intro i j hi hj heq
    have hflat : (Anchor.all.flatMap wDeal.piles).length = 28 := by decide
    have hstock : wDeal.stock.length = 24 := by decide
    rw [List.length_append, hflat, hstock] at hi hj
    have hall : ∀ i ∈ List.range 52, ∀ j ∈ List.range 52,
        (Anchor.all.flatMap wDeal.piles ++ wDeal.stock)[i]? =
          (Anchor.all.flatMap wDeal.piles ++ wDeal.stock)[j]? → i = j := by decide
    exact hall i (List.mem_range.mpr hi) j (List.mem_range.mpr hj) heq

private theorem wState_wf : wState.WF := by
  refine State.WF.intro wDeal_wf ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · -- depths_le
    intro a
    show (0 : Nat) ≤ (wDeal.piles a).length
    cases a <;> decide
  · -- board_edges
    intro b _ htop
    have hnone : wState.board.topOf b = none := Board.empty_topOf b
    rw [hnone] at htop
    exact absurd htop (by simp)
  · -- vis_off_cycle
    intro c hc
    have hc' : (wState.board.bottomOf c).isSome = true := hc
    have hn : wState.board.bottomOf c = none := Board.empty_bottomOf c
    rw [hn] at hc'
    simp at hc'
  · -- found_off_cycle
    intro c h
    have h0 : wState.heights c.suit = 0 := rfl
    have hc : decide (c.rank.toIdx < wState.heights c.suit) = true := h
    rw [h0] at hc
    simp at hc
  · -- founds_gone
    intro c hc
    have h0 : wState.heights c.suit = 0 := rfl
    rw [h0] at hc
    exact absurd hc (by omega)
  · -- vis_not_hidden
    intro c hc a hc'
    have hc'' : (wState.board.bottomOf c).isSome = true := hc
    have hn : wState.board.bottomOf c = none := Board.empty_bottomOf c
    rw [hn] at hc''
    simp at hc''
  · -- heights_le
    intro _
    exact Nat.zero_le _
  · -- cursor_le
    show wState.stock.cursor ≤ wState.stock.cards.length
    decide
  · -- step_pos
    exact Nat.zero_lt_one
  · -- stock_wf
    refine ⟨fun i j hi hj heq => ?_, fun _ hc => hc⟩
    have hall : ∀ i ∈ List.range 24, ∀ j ∈ List.range 24,
        wStockList[i]? = wStockList[j]? → i = j := by decide
    exact hall i (List.mem_range.mpr hi) j (List.mem_range.mpr hj) heq

/-! ## The commitment's anchor landings -/

/-- The landing successor on anchor `a` (all seven fire; only `p₀`,
`p₁`, `p₂` are used below). -/
private def wSucc (a : Anchor) : State :=
  (wState.applyDrawTo (S .king) (Sum.inl a)).getD wState

/-- The one-edge board the king's landing builds on the empty board. -/
private def wBoard (a : Anchor) : Board where
  topOf := fun b => if b = Sum.inl a then some (S .king) else none
  inj := by
    intro b₁ b₂ c h₁ h₂
    by_cases h1 : b₁ = Sum.inl a
    · rw [ite_eq_left h1] at h₁
      by_cases h2 : b₂ = Sum.inl a
      · rw [h1, h2]
      · rw [ite_eq_right h2] at h₂
        simp at h₂
    · rw [ite_eq_right h1] at h₁
      simp at h₁

/-- The empty board accepts the king at every anchor. -/
private theorem wAttach (a : Anchor) :
    wState.board.attach (Sum.inl a) (S .king) = some (wBoard a) := by
  have h1 : wState.board.topOf (Sum.inl a) = none := rfl
  have h2 : wState.board.bottomOf (S .king) = none := rfl
  unfold Board.attach
  rw [dite_eq_left h1, dite_eq_left h2]
  refine congrArg some (Board.ext_topOf (funext (fun b' => ?_)))
  by_cases hb : b' = Sum.inl a
  · rw [hb]
    show Board.update Board.empty.topOf (Sum.inl a) (some (S .king))
        (Sum.inl a) = (if Sum.inl a = Sum.inl a then some (S .king) else none)
    rw [Board.update_self, ite_eq_left rfl]
  · show Board.update Board.empty.topOf (Sum.inl a) (some (S .king)) b' =
      (if b' = Sum.inl a then some (S .king) else none)
    rw [Board.update_ne _ _ _ _ hb, ite_eq_right hb]
    exact Board.empty_topOf b'

/-- The stock's head IS the king (position 0). -/
private theorem wPosOf : wState.stock.posOf (S .king) = some 0 := rfl

/-- Every anchor accepts the king's tableau commitment. -/
private theorem wSucc_apply (a : Anchor) :
    wState.applyDrawTo (S .king) (Sum.inl a) = some (wSucc a) := by
  have hreach : wState.reachablePos (S .king) = some 0 := by
    rw [State.reachablePos_step1 wState_wf rfl (S .king)]
    exact wPosOf
  have hto : wState.applyDrawTo (S .king) (Sum.inl a) = some
      { wState with board := wBoard a, stock := (wState.stock.drawTo 0).removeAt 0 } :=
    applyDrawTo_iff.mpr ⟨0, wBoard a, hreach, wAttach a, rfl⟩
  cases h : wState.applyDrawTo (S .king) (Sum.inl a) with
  | none =>
      have := hto
      rw [h] at this
      simp at this
  | some s' =>
      have hw : wSucc a = s' := by
        show (wState.applyDrawTo (S .king) (Sum.inl a)).getD wState = s'
        rw [h]
        rfl
      rw [hw]

/-- The landing state: the spliced stock and the one-edge board. -/
private theorem wS_shape (a : Anchor) :
    wSucc a =
      { wState with board := wBoard a, stock := ⟨Cycle.removeIdx wState.stock.cards 0, 0⟩ } := by
  obtain ⟨i, bd, hpos, hatt, hs⟩ := applyDrawTo_eq (wSucc_apply a)
  have hreach : wState.reachablePos (S .king) = some 0 := by
    rw [State.reachablePos_step1 wState_wf rfl (S .king)]
    exact wPosOf
  have hi : i = 0 := Option.some.inj (hpos.symm.trans hreach)
  have hbd : bd = wBoard a := by
    have hsome : wState.board.attach (Sum.inl a) (S .king) = some bd := hatt
    rw [wAttach a] at hsome
    exact (Option.some.inj hsome).symm
  rw [hi, hbd] at hs
  exact hs

private theorem wS_board (a : Anchor) (b : Base) :
    (wSucc a).board.topOf b =
      (if b = Sum.inl a then some (S .king) else none) := by
  have hsb : (wSucc a).board = wBoard a := by rw [wS_shape]
  rw [hsb]
  rfl

private theorem wS_heights (a : Anchor) :
    (wSucc a).heights = fun _ => 0 := by
  rw [wS_shape]
  rfl

/-- Only the king is seated on the landing state. -/
private theorem wS_bot_none (a : Anchor) {c : Card} (h : c ≠ S .king) :
    (wSucc a).board.bottomOf c = none := by
  refine (Board.bottomOf_eq_none _ c).mpr (fun b hb => ?_)
  have htb := wS_board a b
  rw [htb] at hb
  by_cases hba : b = Sum.inl a
  · rw [ite_eq_left hba] at hb
    exact h (Option.some.inj hb).symm
  · rw [ite_eq_right hba] at hb
    exact absurd hb (by simp)

/-! ## The closure is frozen: every accommodation move is dead -/

private theorem wS_dead_pileStack (a : Anchor) (c : Card) :
    (wSucc a).apply (Move.pileStack c) = none := by
  cases h : (wSucc a).apply (Move.pileStack c) with
  | none => rfl
  | some t =>
      exfalso
      have hips := apply_pileStack_iff.mp h
      obtain ⟨b', hb', hrk', -⟩ := hips.2
      by_cases hck : c = S .king
      · have h0 : (wSucc a).heights c.suit = 0 := by rw [wS_heights]
        rw [h0, hck] at hrk'
        have h12 : (S .king).rank.toIdx = 12 := rfl
        rw [h12] at hrk'
        omega
      · rw [wS_bot_none a hck] at hb'
        exact absurd hb' (by simp)

private theorem wS_dead_stackPile (a : Anchor) (c : Card) (b : Base) :
    (wSucc a).apply (Move.stackPile c b) = none := by
  cases h : (wSucc a).apply (Move.stackPile c b) with
  | none => rfl
  | some t =>
      exfalso
      have hips := apply_stackPile_iff.mp h
      have hrk := hips.1
      have h0 : (wSucc a).heights c.suit = 0 := by rw [wS_heights]
      rw [h0] at hrk
      omega

/-- Every accommodation move at a landing state is dead. -/
private theorem wS_dead (a : Anchor) (m : Move)
    (hm : m.isAccommodation = true) : (wSucc a).apply m = none := by
  cases m with
  | pileStack c => exact wS_dead_pileStack a c
  | stackPile c b => exact wS_dead_stackPile a c b
  | draw => simp [Move.isAccommodation] at hm
  | reveal a' => simp [Move.isAccommodation] at hm
  | deckPile c b => simp [Move.isAccommodation] at hm
  | deckStack c => simp [Move.isAccommodation] at hm
  | pilePile c b => simp [Move.isAccommodation] at hm

/-- The only accommodation-play end state is the state itself. -/
private theorem wS_run (a : Anchor) : ∀ (play : List Move) (t : State),
    (∀ m ∈ play, m.isAccommodation = true) →
    (wSucc a).run play = some t → t = wSucc a := by
  intro play
  induction play with
  | nil => intro t _ hrun; exact (Option.some.inj hrun).symm
  | cons m ms ih =>
      intro t hall hrun
      have hap : (wSucc a).apply m = none :=
        wS_dead a m (hall m (by simp))
      have hrun' : (match (wSucc a).apply m with
        | some st' => st'.run ms | none => none) = some t := hrun
      rw [hap] at hrun'
      exact absurd hrun' (by simp)

/-- **The split**: two different anchor landings of the same commitment
cannot be reconciled by accommodation plays. -/
private theorem wSucc_ne (a a' : Anchor) (h : a ≠ a') :
    wSucc a ≠ wSucc a' := by
  intro heq
  have h1 : (wSucc a).board.topOf (Sum.inl a) = some (S .king) := by
    have htb := wS_board a (Sum.inl a)
    rw [ite_eq_left rfl] at htb
    exact htb
  have h2 : (wSucc a').board.topOf (Sum.inl a) = none := by
    have htb := wS_board a' (Sum.inl a)
    rw [ite_eq_right (fun hh : (Sum.inl a : Base) = Sum.inl a' =>
      h (Sum.inl.inj hh))] at htb
    exact htb
  rw [← heq] at h2
  rw [h1] at h2
  exact absurd h2 (by simp)

private theorem wSucc_not_accomm (a a' : Anchor) (h : a ≠ a') :
    ¬ accommodates (wSucc a) (wSucc a') := by
  intro hacc
  obtain ⟨play, hrun, hall⟩ := hacc
  exact wSucc_ne a a' h (wS_run a play (wSucc a') hall hrun).symm

/-! ## The commitment's macro steps -/

/-- The empty-board king placement (per anchor, a kernel decision). -/
private theorem wCanPlace (a : Anchor) :
    wState.canPlace (S .king) (Sum.inl a) = true := by
  cases a <;> decide

/-- The macro step to each anchor landing (the empty accommodation). -/
theorem wStep (a : Anchor) :
    macroStep wState (MacroMove.drawCommit (S .king)) (wSucc a) := by
  refine ⟨wState, ⟨[], rfl, fun _ hm => by simp at hm⟩, ?_⟩
  exact ⟨Sum.inl a, Or.inl ⟨wCanPlace a, wSucc_apply a⟩⟩

/-- The king is a live hole at the state. -/
theorem wHoleLive : LabelLive wState (S .king) Label.hole :=
  ⟨Anchor.p0, rfl, rfl⟩

/-- The king commits through the hole channel at the root itself. -/
theorem wSuccThrough (a : Anchor) :
    SuccThrough wState (S .king) Label.hole (wSucc a) :=
  ⟨wState, [], rfl, fun _ hm => by simp at hm,
    ⟨Sum.inl a, wCanPlace a, wSucc_apply a⟩, rfl⟩

/-- The hole channel is P2-safe (the four non-stack arms are True). -/
theorem wHoleSafe : P2Safe wState (S .king) Label.hole := trivial

/-! ## The refuted universals (as-stated spellings, negated) -/

/-- **`c2_two_option` as stated is REFUTED**: three pairwise
closure-separated successors of one commitment at a WF state. -/
theorem wk_c2_as_stated_false :
    ¬ (∀ (st : State) (X : Card) (s₁ s₂ s₃ : State), st.WF →
        macroStep st (MacroMove.drawCommit X) s₁ →
        macroStep st (MacroMove.drawCommit X) s₂ →
        macroStep st (MacroMove.drawCommit X) s₃ →
        closureEq s₁ s₂ ∨ closureEq s₁ s₃ ∨ closureEq s₂ s₃) := by
  intro h
  rcases h wState (S .king) (wSucc Anchor.p0) (wSucc Anchor.p1)
    (wSucc Anchor.p2) wState_wf
    (wStep Anchor.p0) (wStep Anchor.p1) (wStep Anchor.p2) with
    q | q | q
  · exact wSucc_not_accomm Anchor.p0 Anchor.p1 (by decide) q.1
  · exact wSucc_not_accomm Anchor.p0 Anchor.p2 (by decide) q.1
  · exact wSucc_not_accomm Anchor.p1 Anchor.p2 (by decide) q.1

/-- **`same_pin_closureEq` as stated is REFUTED**: the hole channel is
live at the root, both successors go through it, and they stay split. -/
theorem wk_same_pin_as_stated_false :
    ¬ (∀ (st : State) (X : Card) (r : Label X) (s s' : State), st.WF →
        LabelLive st X r → SuccThrough st X r s → SuccThrough st X r s' →
        closureEq s s') := by
  intro h
  exact wSucc_not_accomm Anchor.p0 Anchor.p1 (by decide)
    (h wState (S .king) Label.hole (wSucc Anchor.p0) (wSucc Anchor.p1)
      wState_wf wHoleLive (wSuccThrough Anchor.p0) (wSuccThrough Anchor.p1)).1

/-- **`p2_direct_class` as stated is REFUTED**: the hole channel is
P2-safe, the king commits directly to the second anchor, the first
anchor's successor is through the live hole channel, and the class
join fails. -/
theorem wk_p2_direct_as_stated_false :
    ¬ (∀ (st : State) (X : Card) (sd s_p : State) (r : Label X), st.WF →
        commitApplies st (MacroMove.drawCommit X) sd →
        SuccThrough st X r s_p → P2Safe st X r →
        closureEq sd s_p) := by
  intro h
  refine wSucc_not_accomm Anchor.p1 Anchor.p0 (by decide)
    (h wState (S .king) (wSucc Anchor.p1) (wSucc Anchor.p0) Label.hole
      wState_wf ⟨Sum.inl Anchor.p1, Or.inl ⟨wCanPlace Anchor.p1,
        wSucc_apply Anchor.p1⟩⟩ (wSuccThrough Anchor.p0) wHoleSafe).1

/-- **`crease_chain_absorbed` as stated is REFUTED**: with the empty
accommodation on both sides (sublist-reflexive), the two `hole`
channel commits witness all nine premises, and the class join fails. -/
theorem wk_crease_as_stated_false :
    ¬ (∀ (st : State) (X : Card) (r : Label X) (s s' : State)
        (α α' : List Move) (u u' : State), st.WF →
        LabelLive st X r →
        st.run α = some u → (∀ m ∈ α, m.isAccommodation = true) →
        commitArmOf u X r s → LabelSig X r α →
        st.run α' = some u' → (∀ m ∈ α', m.isAccommodation = true) →
        commitArmOf u' X r s' → LabelSig X r α' →
        List.Sublist α α' →
        closureEq s s') := by
  intro h
  have hacc : ∀ m ∈ ([] : List Move), m.isAccommodation = true :=
    fun _ hm => by simp at hm
  refine wSucc_not_accomm Anchor.p0 Anchor.p1 (by decide)
    (h wState (S .king) Label.hole (wSucc Anchor.p0) (wSucc Anchor.p1)
      [] [] wState wState wState_wf wHoleLive
      rfl hacc (⟨Sum.inl Anchor.p0, wCanPlace Anchor.p0,
        wSucc_apply Anchor.p0⟩) rfl
      rfl hacc (⟨Sum.inl Anchor.p1, wCanPlace Anchor.p1,
        wSucc_apply Anchor.p1⟩) rfl
      List.Sublist.slnil).1

end KingAnchor

#print axioms KingAnchor.wk_c2_as_stated_false
#print axioms KingAnchor.wk_same_pin_as_stated_false
#print axioms KingAnchor.wk_p2_direct_as_stated_false
#print axioms KingAnchor.wk_crease_as_stated_false
