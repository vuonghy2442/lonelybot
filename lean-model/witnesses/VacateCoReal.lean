import Klondike.Initial

/-!
# The vacate co-realizability witness — premises + corner exhibits

The farm-vacate-prunable session's regress layer (2026-10-10), for
`vacate_pilePile_prunable_of_hole` (Dominance §5.4b).  The decide-anchored
family of the pristine `uState`/`wState` witnesses, extended to the vacate
row's own shapes:

* **Co-realizability** — the row's premises are inhabited TOGETHER with a
  LEGAL vacate at ONE WF state: `vState` has the non-king `♥5` floor-seated
  on anchor 0 (`depths_zero_of_floor_seated`'s dealt-head exit), the
  visible bare `♠6` as the fitting card target (`canSitOn` lit), anchor 2
  free (the hole), and the vacate `pilePile ♥5 (inr ♠6)` legal.  No
  premise is vacuous and no guard of the staged statement is
  unsatisfiable.

* **The corner's front legs** — the king-consumer family's σ-prefix, at
  the `deckPile ♦K (inl p0)` source: the king landing on the VACATED
  anchor is dead at `vState` (`corner_deadAtRoot`, the occupied seat -
  the datum `hfree` must license) but live at the vacate successor
  (`corner_liveAfterVac`); the replacement prefix — king to the
  pre-existing hole, then the vacate — is legal at every step
  (`corner_holeKing`, `corner_kingHole_then_vacate`).  The row's
  machinery assumption (the σ-corner's front legs) is exhibited, not
  assumed.

* **The corner is NOT a commutation** — the two orders of the same two
  moves reach different states at the vacated seat
  (`corner_composites_diverge`) — the vacated pile carries the king in
  the issued order and stays empty in the swapped order.  This is the
  honest shape behind the staged residue: the tail replay, not the front
  swap, is the open content (the slate-permutation obstruction recorded
  in `vacate_secondMove_residue`'s route note).

The no-hole boundary (why `hfree` is load-bearing, not decoration) is
`witnesses/SuccLabeledWitness.lean`: at the all-anchors-occupied `uState`
the anchored-head unseat route is a genuine macro successor whose hole
channel is dead at the root - the row without a hole is FALSE there.
No countermodel to the staged row itself was found this session; what
this file exhibits is the premises' honesty and the corner's front-half.
-/

namespace VacateCoreal

/-- Hearts. -/
private def H (r : Rank) : Card := ⟨Suit.heart, r⟩
/-- Spades. -/
private def S (r : Rank) : Card := ⟨Suit.spade, r⟩
/-- Diamonds. -/
private def D (r : Rank) : Card := ⟨Suit.diamond, r⟩
/-- Clubs. -/
private def C (r : Rank) : Card := ⟨Suit.club, r⟩

/-! ## The witness deal -/

/-- The deal list: the universe order with `♥5` moved to position 0 (the
single-card pile 0, the vacate's non-king floor head) and `♠6` to
position 1 (pile 1's dealt head - the vacate's fitting card target),
`♦K` to position 28 (the stock's first card, the waste top at cursor 1 -
the king source). -/
private def vl : List Card :=
  [H .five, S .six] ++
  [H .ace, C .ace, C .two, C .three,
   D .two, D .three, D .four, D .five,
   H .two, H .three, H .four, H .six, H .seven,
   D .six, D .seven, D .eight, D .nine, D .ten, D .jack,
   C .four, C .five, C .six, C .seven, C .eight, C .nine, C .ten] ++
  [D .king, C .jack, C .queen, C .king,
   H .eight, H .nine, H .ten, H .jack, H .queen, H .king,
   S .ace, S .two, S .three, S .four, S .five, S .seven,
   S .eight, S .nine, S .ten, S .jack, S .queen, S .king,
   D .ace, D .queen]

private theorem vl_length : vl.length = 52 := by decide

private theorem vl_noDup : noDupCards vl := by
  intro i j hi hj heq
  rw [vl_length] at hi hj
  have hall : ∀ i ∈ List.range 52, ∀ j ∈ List.range 52, vl[i]? = vl[j]? → i = j := by
    decide
  exact hall i (List.mem_range.mpr hi) j (List.mem_range.mpr hj) heq

private def vDeal : Deal := Deal.ofList vl

private theorem vDeal_wf : vDeal.WF := Deal.ofList_wf vl_length vl_noDup

/-! ## The board: two deal-adjacent anchor heads, everything else bare -/

/-- The two seated cards are distinct (the injection law's only live
witness-pair). -/
private theorem heads_ne : (H .five) ≠ (S .six) := by decide

/-- The board function: `♥5` on pile 0's anchor, `♠6` on pile 1's anchor
(both are those piles' dealt heads), nothing anywhere else. -/
private def vTopOf : Base → Option Card := fun b =>
  match b with
  | Sum.inl Anchor.p0 => some (H .five)
  | Sum.inl Anchor.p1 => some (S .six)
  | Sum.inl _ => none
  | Sum.inr _ => none

private theorem vTopOf_some_cases (b : Base) (c : Card) (h : vTopOf b = some c) :
    (b = Sum.inl Anchor.p0 ∧ c = H .five) ∨ (b = Sum.inl Anchor.p1 ∧ c = S .six) := by
  cases b with
  | inl a =>
      cases a with
      | p0 => exact Or.inl ⟨rfl, (Option.some.inj h).symm⟩
      | p1 => exact Or.inr ⟨rfl, (Option.some.inj h).symm⟩
      | p2 => exact absurd h (by simp [vTopOf])
      | p3 => exact absurd h (by simp [vTopOf])
      | p4 => exact absurd h (by simp [vTopOf])
      | p5 => exact absurd h (by simp [vTopOf])
      | p6 => exact absurd h (by simp [vTopOf])
  | inr d => exact absurd h (by simp [vTopOf])

private theorem vBoard_inj : ∀ (b₁ b₂ : Base) (c : Card),
    vTopOf b₁ = some c → vTopOf b₂ = some c → b₁ = b₂ := by
  intro b₁ b₂ c h₁ h₂
  rcases vTopOf_some_cases b₁ c h₁ with ⟨e₁, hc₁⟩ | ⟨e₁, hc₁⟩
  · rcases vTopOf_some_cases b₂ c h₂ with ⟨e₂, hc₂⟩ | ⟨e₂, hc₂⟩
    · exact e₁.trans e₂.symm
    · exact absurd (hc₁.symm.trans hc₂) heads_ne
  · rcases vTopOf_some_cases b₂ c h₂ with ⟨e₂, hc₂⟩ | ⟨e₂, hc₂⟩
    · exact absurd (hc₁.symm.trans hc₂) (fun h => heads_ne h.symm)
    · exact e₁.trans e₂.symm

private def vBoard : Board := ⟨vTopOf, vBoard_inj⟩

/-! ### The vBoard bridges (the projection reads, once) -/

private theorem vBoard_p0 : vBoard.topOf (Sum.inl Anchor.p0) = some (H .five) := rfl
private theorem vBoard_p1 : vBoard.topOf (Sum.inl Anchor.p1) = some (S .six) := rfl

private theorem vBoard_free {a : Anchor} (h : a ≠ Anchor.p0 ∧ a ≠ Anchor.p1) :
    vBoard.topOf (Sum.inl a) = none := by
  cases a with
  | p0 => exact absurd rfl h.1
  | p1 => exact absurd rfl h.2
  | p2 => rfl
  | p3 => rfl
  | p4 => rfl
  | p5 => rfl
  | p6 => rfl

private theorem vBoard_inr (d : Card) : vBoard.topOf (Sum.inr d) = none := rfl

/-! ## The state -/

/-- The stock slice and cursor 1: the waste top `prev` is the first stock
card, `♦K` - the king source for the corner exhibits. -/
private def vStockList : List Card := vl.drop 28

private theorem vStockList_length : vStockList.length = 24 := by decide

/-- The witness state. -/
def vState : State where
  deal := vDeal
  board := vBoard
  heights := fun _ => 0
  depths := fun _ => 0
  stock := ⟨vStockList, 1⟩
  drawStep := 1

/-! ## The state is WF -/

private theorem vState_wf : vState.WF := by
  refine State.WF.intro vDeal_wf ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · -- depths_le
    intro a
    show (0 : Nat) ≤ (vDeal.piles a).length
    cases a <;> decide
  · -- board_edges: the only edges are the two dealt-head seats
    intro b c hb
    have hb' : vBoard.topOf b = some c := hb
    cases b with
    | inl a =>
        by_cases hapi : a = Anchor.p0
        · subst hapi
          rw [vBoard_p0] at hb'
          refine ⟨(Board.bottomOf_eq _ _ _).mpr hb', ?_⟩
          rw [(Option.some.inj hb').symm]
          show (H .five).rank = Rank.king ∨ (vDeal.piles Anchor.p0).head? = some (H .five)
          exact Or.inr rfl
        · by_cases hapi2 : a = Anchor.p1
          · subst hapi2
            rw [vBoard_p1] at hb'
            refine ⟨(Board.bottomOf_eq _ _ _).mpr hb', ?_⟩
            rw [(Option.some.inj hb').symm]
            show (S .six).rank = Rank.king ∨ (vDeal.piles Anchor.p1).head? = some (S .six)
            exact Or.inr rfl
          · rw [vBoard_free ⟨hapi, hapi2⟩] at hb'
            simp at hb'
    | inr d =>
        rw [vBoard_inr] at hb'
        exact absurd hb' (by simp)
  · -- vis_off_cycle: the seated cards are the two heads, never stocked
    intro c hc
    have hc' : (vState.board.bottomOf c).isSome = true := hc
    cases hbot : vState.board.bottomOf c with
    | none => rw [hbot] at hc'; simp at hc'
    | some b =>
        have htb : vBoard.topOf b = some c := (Board.bottomOf_eq _ _ _).mp hbot
        cases b with
        | inl a =>
            by_cases hapi : a = Anchor.p0
            · subst hapi
              rw [vBoard_p0] at htb
              rw [(Option.some.inj htb).symm]
              exact Cycle.posOf_eq_none (show (H .five) ∉ vStockList by decide)
            · by_cases hapi2 : a = Anchor.p1
              · subst hapi2
                rw [vBoard_p1] at htb
                rw [(Option.some.inj htb).symm]
                exact Cycle.posOf_eq_none (show (S .six) ∉ vStockList by decide)
              · rw [vBoard_free ⟨hapi, hapi2⟩] at htb
                exact absurd htb (by simp)
        | inr d =>
            rw [vBoard_inr] at htb
            exact absurd htb (by simp)
  · -- found_off_cycle: vacuous at zero heights
    intro c h
    have h0 : vState.heights c.suit = 0 := rfl
    have hc : decide (c.rank.toIdx < vState.heights c.suit) = true := h
    rw [h0] at hc
    simp at hc
  · -- founds_gone: vacuous at zero heights
    intro c hc
    have h0 : vState.heights c.suit = 0 := rfl
    rw [h0] at hc
    exact absurd hc (by omega)
  · -- vis_not_hidden: depths 0, the hidden slices are empty
    intro c _ a
    show ¬ (c ∈ (vDeal.piles a).take (0 : Nat))
    rw [List.take_zero]
    simp
  · -- heights_le
    intro _
    exact Nat.zero_le _
  · -- cursor_le
    show vState.stock.cursor ≤ vState.stock.cards.length
    decide
  · -- step_pos
    exact Nat.zero_lt_one
  · -- stock_wf
    refine ⟨fun i j hi hj heq => ?_, ?_⟩
    · have hall : ∀ i ∈ List.range 24, ∀ j ∈ List.range 24,
          vStockList[i]? = vStockList[j]? → i = j := by decide
      exact hall i (List.mem_range.mpr hi) j (List.mem_range.mpr hj) heq
    · intro _ hmem
      exact hmem

/-! ## Co-realizability: every premise of the row, plus a legal vacate -/

/-- The non-king floor root: `♥5`, seated on anchor 0 - the anchored
floor card the vacate uproots. -/
theorem co_floor : vState.board.bottomOf (H .five) = some (Sum.inl Anchor.p0) :=
  (Board.bottomOf_eq _ _ _).mpr vBoard_p0

/-- The pre-existing hole: anchor 2's seat is bare - `hfree`'s witness. -/
theorem co_hole : vState.board.topOf (Sum.inl Anchor.p2) = none :=
  vBoard_free ⟨by decide, by decide⟩

theorem co_hfree : ∃ h, vState.board.topOf (Sum.inl h) = none := ⟨Anchor.p2, co_hole⟩

/-- The root is not a king (`hnk`). -/
theorem co_nonking : (H .five).rank ≠ Rank.king := by decide

/-- The target card is visible and bare, and the fit holds (`canSitOn`
lit: `♥5` is one below `♠6`, red under black). -/
theorem co_target_bare : vState.board.topOf (Sum.inr (S .six)) = none :=
  vBoard_inr (S .six)

theorem co_target_vis : vState.isVis (S .six) = true := by
  show (vState.board.bottomOf (S .six)).isSome = true
  have hbot : vState.board.bottomOf (S .six) = some (Sum.inl Anchor.p1) :=
    (Board.bottomOf_eq _ _ _).mpr vBoard_p1
  rw [hbot]
  rfl

theorem co_target_fit : canSitOn (H .five) (S .six) = true := by decide

/-- The vacate itself is legal at the witness state: the whole
premise bundle of `vacate_pilePile_prunable_of_hole` co-realizes with a
legal instance of the pruned move.  (Bool reading: `State` carries no
`DecidableEq`, so every apply-exhibit below reads `.isSome` `.isNone`
- the pristine family's decide-anchored discipline.) -/
theorem co_vacate_live :
    (vState.apply (Move.pilePile (H .five) (Sum.inr (S .six)))).isSome = true := by
  decide

/-- The bundle, packaged. -/
theorem co_realizable_bundle :
    ∃ st : State, st.WF ∧ ∃ c : Card, ∃ a : Anchor, ∃ b : Base,
      c.rank ≠ Rank.king ∧
      st.board.bottomOf c = some (Sum.inl a) ∧
      (∃ h, st.board.topOf (Sum.inl h) = none) ∧
      (st.apply (Move.pilePile c b)).isSome = true :=
  ⟨vState, vState_wf, H .five, Anchor.p0, Sum.inr (S .six),
    co_nonking, co_floor, co_hfree, co_vacate_live⟩

/-! ## The corner's front legs (the σ-prefix machinery, exhibited) -/

/-- The vacate's successor state (extraction by getD; its cells are the
decidable exhibits). -/
def vAfter : State :=
  (vState.apply (Move.pilePile (H .five) (Sum.inr (S .six)))).getD vState

/-- The vacated seat is bare at the successor - the slot the king
family wants. -/
theorem vac_slots_bare : vAfter.board.topOf (Sum.inl Anchor.p0) = none := by
  decide

/-- The vacate still seats the run's root at its card target. -/
theorem vac_target_seated : vAfter.board.topOf (Sum.inr (S .six)) = some (H .five) := by
  decide

/-- The king source: the waste top at cursor 1 is `♦K`; its landing on
the VACATED anchor (`inl p0`) is dead at the root - the seat is
occupied by `♥5` (the king-consumer fact the `hfree` premise must
license). -/
theorem corner_deadAtRoot :
    (vState.apply (Move.deckPile (D .king) (Sum.inl Anchor.p0))).isNone = true := by
  decide

/-- ... and live at the vacate successor: the vacated slot is a real
empty pile (depth 0 - no reveal boundary was created). -/
theorem corner_liveAfterVac :
    (vAfter.apply (Move.deckPile (D .king) (Sum.inl Anchor.p0))).isSome = true := by
  decide

/-- The king landing on the PRE-EXISTING hole is live at the root. -/
theorem corner_holeKing :
    (vState.apply (Move.deckPile (D .king) (Sum.inl Anchor.p2))).isSome = true := by
  decide

/-- The replacement prefix is legal THROUGH: king to the hole, then the
same vacate. -/
theorem corner_kingHole_then_vacate :
    (vState.apply (Move.deckPile (D .king) (Sum.inl Anchor.p2)) >>=
      fun s => s.apply (Move.pilePile (H .five) (Sum.inr (S .six)))).isSome = true := by
  decide

/-- The issued corner pair, for the differential below. -/
theorem corner_vacate_then_king :
    (vState.apply (Move.pilePile (H .five) (Sum.inr (S .six))) >>=
      fun s => s.apply (Move.deckPile (D .king) (Sum.inl Anchor.p0))).isSome = true := by
  decide

/-! ## The corner is not a commutation -/

/-- The issued order's composite: vacate, then king onto the vacated
anchor. -/
private def vWA : State :=
  ((vState.apply (Move.pilePile (H .five) (Sum.inr (S .six))) >>=
    fun s => s.apply (Move.deckPile (D .king) (Sum.inl Anchor.p0)))).getD vState

/-- The swapped order's composite: king onto the pre-existing hole, then
the same vacate. -/
private def vWB : State :=
  ((vState.apply (Move.deckPile (D .king) (Sum.inl Anchor.p2)) >>=
    fun s => s.apply (Move.pilePile (H .five) (Sum.inr (S .six)))).getD vState)

/-- The two orders of the SAME two moves reach DIFFERENT states at the
vacated seat: the king sits on the vacated anchor in the issued order
(`corner_vacate_then_king`), and the vacated anchor stays empty when the
king takes the hole first (`corner_kingHole_then_vacate`).  The front
legs of the σ-corner exist; what does not exist is a plain two-move
swap - the residue's tail-replay obstruction, recorded in
`vacate_secondMove_residue`'s route note. -/
theorem corner_composites_diverge :
    vWA.board.topOf (Sum.inl Anchor.p0) ≠ vWB.board.topOf (Sum.inl Anchor.p0) := by
  decide

end VacateCoreal

