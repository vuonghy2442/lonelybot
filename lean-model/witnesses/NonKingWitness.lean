import Klondike.C2Streamlined

/-!
# The non-king witness — the twin split at unstackable rungs + the
free-float labeling gap

Every wave-18/19/20 refutation of the C2 pillar set lives at KING
commits (`witnesses/C2KingAnchorWitness.lean`'s climb-blocked stocked
king, `witnesses/SuccLabeledWitness.lean`'s anchored-head unseat):
`king_of_canPlace_inl` gives kings the free anchors (up to seven
landings), and the unseat route needs the king to land on a vacated
anchor.  This file is the decide-first probe of the NON-KING side —
the wave-21 ticket — in two sections, both pristine-family witnesses
(zero heights, zero depths, draw step 1, decide-anchored, WF):

## §A — the non-stackable twin collapse splits (`NK`)

`commitTableau_class` (C2Streamlined §9.5) joins a drawn card's two
tableau landings through the two-move foundation shuttle
`[pileStack X; stackPile X b₂]`, PREMISED on the rung
`X.rank.toIdx = u.heights X.suit` — the shuttle's vehicle is X's own
round trip through the foundation.  The king-anchor witness pins the
premise's failure only at KING landings (anchors); here the twin
RECEIVER landings — the destination twins of a NON-king, reached with
ZERO spend through the live `direct` channel at the root — split as
soon as the suit prefix is incomplete:

* the state `nkState` seats the drawn card X = ♠6's two destination
  twins — ♥7 on pile 0's dealt head, ♦7 on pile 1's — as free visible
  tops, with all foundations at 0 (X's spade prefix incomplete:
  5 ≠ 0), X stocked at the first reachable position;
* both twin hosts are placeable: the commitment has the two tableau
  successors `nkS1` (X on ♥7) and `nkS2` (X on ♦7), both through the
  LIVE, zero-spend `direct` channel at the root;
* at each landing state every accommodation move is dead (the landed
  card and the twins are non-aces against foundation height 0, and
  `stackPile` demands rank + 1 = height 0), so the two landings are
  closure-SEPARATED: `nk_split : ¬ closureEq nkS1 nkS2`;
* hence three refutations, the non-king readings of the wave-18
  as-stated universals — `wk_nonking_twinCollapse_rung_false`
  (`commitTableau_class` without its rung premise, restricted to
  non-kings), `wk_nonking_samePin_direct_false` (`same_pin_closureEq`
  restricted to non-kings, via the shared live direct channel), and
  `wk_nonking_p2Direct_false` (`p2_direct_class` restricted to
  non-kings, root commit against the P2-safe direct successor);
* and the honest boundary datum the assembly needs: the count
  SURVIVES here without the rung — `nkSuccessorsExhaustTwo` shows the
  commitment has EXACTLY these two successors (the destination bound:
  anchors demand kings, receivers come in twin pairs), and
  `nkTwoOptionHoldsHere` derives the two-option bound trivially.  The
  two-option count for non-kings is a DESTINATION-COUNT phenomenon,
  not a closure-join phenomenon; the rung premise buys the JOIN
  (`commitTableau_class` at the rung), never the count itself.

## §B — the free-float labeling gap for non-kings (`FF`)

`succ_labeled`'s refutation was an anchor phenomenon ( the unseat
route), believed dead for non-kings.  It survives in a different
shape: a WINDOW-CONTENT gap with no anchor and no king in sight.  The
state `ffState` reuses §A's twin hosts plus a third anchored head —
♥A on pile 2's dealt seat — a free visible ace at foundation height 0
whose one-move promotion `pileStack ♥A` is a legal accommodation
window that touches NOTHING in X's two-type ball:

* the routes' successors `ffWin ♥7` / `ffWin ♦7` (X committed on a
  twin host at the promoted window state, heights ♥ = 1) are genuine
  `macroStep` successors (`ffWinHeart_step`, `ffWinDiamond_step`);
* `ffWin ♥7` is labeled by NOTHING in the five-element channel list
  (`ffSucc_unlabeled`): `hole` dies on the non-king, `borrow` on the
  zero heights (foundation tops need rank + 1 = 0), `dig` on the twin
  never being seated (no receiver is covered), `toStack` on the spade
  freeze (the `SuccLabeledWitness` freeze argument, replayed
  locally), and `direct` — though LIVE at the root (`ffDirectLive`)
  — cannot name it: the direct signature demands the EMPTY window,
  but every root commit keeps heights ♥ = 0 against the route's 1.
  The accommodation played IRRELEVANT content; no minimal-pinning
  atom recorded it;
* hence `wk_nonking_succLabeled_false`: the as-stated `succ_labeled`
  restricted to non-kings is FALSE — the window-content gap is a
  non-king phenomenon too, so `hlab`-type premises cannot be
  discharged by the non-king restriction alone.

And the same root refutes the as-stated COUNT universal restricted to
non-kings (`wk_nonking_c2_false`): THREE pairwise
closure-separated macro successors of one non-king commitment — the
root commit on ♥7 (`ffRoot1`), the window commits on ♥7 and on ♦7.
The window successors are accommodation-dead (`ffWin_stuck`), so they
split from each other (different twin hosts) and from the root commit
(the heart height).  This is why the honest assembly
(`Klondike.C2Streamlined` §16, `c2_two_option_nonKing`) carries the
shared-commit-window datum (one accommodated state u, three
`commitApplies` at u): window NON-uniformity is not merely an
inconvenience — it adds successors the destination bound cannot see.
-/

open Klondike.C2

/-! ## §A — the non-king twin split at the incomplete rung -/

namespace NK

/-- Spades. -/
private def S (r : Rank) : Card := ⟨Suit.spade, r⟩
/-- Hearts. -/
private def H (r : Rank) : Card := ⟨Suit.heart, r⟩
/-- Diamonds. -/
private def D (r : Rank) : Card := ⟨Suit.diamond, r⟩
/-- Clubs. -/
private def C (r : Rank) : Card := ⟨Suit.club, r⟩

/-! ### The board: the two destination twins on dealt head seats -/

/-- The dealt head seated on each anchor's base: the two receiver
twins on piles 0 and 1, nothing (no-seat) elsewhere. -/
private def nkHead : Anchor → Option Card
  | .p0 => some (H .seven)
  | .p1 => some (D .seven)
  | _ => none

private theorem nkHead_none (a : Anchor) (c : Card)
    (h₁ : nkHead a = none) (h₂ : nkHead a = some c) : False := by
  rw [h₂] at h₁
  exact absurd h₁ (by simp)

private theorem nkHead_inj : ∀ (a a' : Anchor) (c : Card),
    nkHead a = some c → nkHead a' = some c → a = a' := by
  intro a a' c h₁ h₂
  cases a with
  | p0 =>
      have h₁' : some (H .seven) = some c := h₁
      cases a' with
      | p0 => rfl
      | p1 =>
          have h₂' : some (D .seven) = some c := h₂
          exact absurd ((Option.some.inj h₁').trans (Option.some.inj h₂').symm)
            (by decide)
      | p2 => exact (nkHead_none Anchor.p2 c rfl h₂).elim
      | p3 => exact (nkHead_none Anchor.p3 c rfl h₂).elim
      | p4 => exact (nkHead_none Anchor.p4 c rfl h₂).elim
      | p5 => exact (nkHead_none Anchor.p5 c rfl h₂).elim
      | p6 => exact (nkHead_none Anchor.p6 c rfl h₂).elim
  | p1 =>
      have h₁' : some (D .seven) = some c := h₁
      cases a' with
      | p0 =>
          have h₂' : some (H .seven) = some c := h₂
          exact absurd ((Option.some.inj h₁').trans (Option.some.inj h₂').symm)
            (by decide)
      | p1 => rfl
      | p2 => exact (nkHead_none Anchor.p2 c rfl h₂).elim
      | p3 => exact (nkHead_none Anchor.p3 c rfl h₂).elim
      | p4 => exact (nkHead_none Anchor.p4 c rfl h₂).elim
      | p5 => exact (nkHead_none Anchor.p5 c rfl h₂).elim
      | p6 => exact (nkHead_none Anchor.p6 c rfl h₂).elim
  | p2 => exact (nkHead_none Anchor.p2 c rfl h₁).elim
  | p3 => exact (nkHead_none Anchor.p3 c rfl h₁).elim
  | p4 => exact (nkHead_none Anchor.p4 c rfl h₁).elim
  | p5 => exact (nkHead_none Anchor.p5 c rfl h₁).elim
  | p6 => exact (nkHead_none Anchor.p6 c rfl h₁).elim

/-- The board function: the two twin heads on their pile anchors. -/
private def nkTopOf : Base → Option Card := fun b =>
  match b with
  | Sum.inl a => nkHead a
  | Sum.inr _ => none

private theorem nkTopOf_inl (a : Anchor) : nkTopOf (Sum.inl a) = nkHead a := rfl
private theorem nkTopOf_inr (d : Card) : nkTopOf (Sum.inr d) = none := rfl

private theorem nkBoard_inj : ∀ (b₁ b₂ : Base) (c : Card),
    nkTopOf b₁ = some c → nkTopOf b₂ = some c → b₁ = b₂ := by
  intro b₁ b₂ c h₁ h₂
  cases b₁ with
  | inl a =>
      cases b₂ with
      | inl a' =>
          rw [nkTopOf_inl] at h₁
          rw [nkTopOf_inl] at h₂
          exact congrArg Sum.inl (nkHead_inj a a' c h₁ h₂)
      | inr d =>
          rw [nkTopOf_inr] at h₂
          exact absurd h₂ (by simp)
  | inr d =>
      rw [nkTopOf_inr] at h₁
      exact absurd h₁ (by simp)

/-- The witness board — the two anchor-head seats, one per twin. -/
private def nkBoard : Board := ⟨nkTopOf, nkBoard_inj⟩

private theorem nkBoard_topOf_inl (a : Anchor) :
    nkBoard.topOf (Sum.inl a) = nkHead a := rfl

private theorem nkBoard_topOf_inr (d : Card) : nkBoard.topOf (Sum.inr d) = none := rfl

/-- Only the two twin hosts are seated anywhere. -/
private theorem nkSeated (c : Card) (h : (nkBoard.bottomOf c).isSome = true) :
    c = H .seven ∨ c = D .seven := by
  obtain ⟨b, hb⟩ : ∃ b, nkBoard.bottomOf c = some b := by
    cases hbot : nkBoard.bottomOf c with
    | none => rw [hbot] at h; simp at h
    | some b => exact ⟨b, rfl⟩
  have htb : nkBoard.topOf b = some c := (Board.bottomOf_eq _ _ _).mp hb
  cases b with
  | inl a =>
      rw [nkBoard_topOf_inl] at htb
      cases a with
      | p0 => exact Or.inl (Option.some.inj htb).symm
      | p1 => exact Or.inr (Option.some.inj htb).symm
      | p2 => rw [show nkHead Anchor.p2 = none from rfl] at htb; simp at htb
      | p3 => rw [show nkHead Anchor.p3 = none from rfl] at htb; simp at htb
      | p4 => rw [show nkHead Anchor.p4 = none from rfl] at htb; simp at htb
      | p5 => rw [show nkHead Anchor.p5 = none from rfl] at htb; simp at htb
      | p6 => rw [show nkHead Anchor.p6 = none from rfl] at htb; simp at htb
  | inr d =>
      rw [nkBoard_topOf_inr] at htb
      exact absurd htb (by simp)

private theorem nkBottomOf_isSome (c : Card) (b : Base)
    (htb : nkBoard.topOf b = some c) : (nkBoard.bottomOf c).isSome = true := by
  rw [(Board.bottomOf_eq nkBoard c b).mpr htb]
  rfl

/-- No spade is seated (in particular the drawn card is not). -/
private theorem nkBottomSix : nkBoard.bottomOf (S .six) = none := by
  refine (Board.bottomOf_eq_none nkBoard (S .six)).mpr (fun b hb => ?_)
  have his := nkBottomOf_isSome (S .six) b hb
  rcases nkSeated (S .six) his with e | e
  · exact absurd e (by decide)
  · exact absurd e (by decide)

/-! ### The state -/

/-- The stock slice: ♠6 at position 0, the clubs and the low red
cards — no seated card is stocked, all 24 distinct. -/
private def nkStockList : List Card :=
  [S .six] ++
  [C .ace, C .two, C .three, C .four, C .five, C .six, C .seven, C .eight,
   C .nine, C .ten, C .jack, C .queen, C .king] ++
  [H .ace, H .two, H .three, H .four, H .five, H .six] ++
  [D .ace, D .two, D .three, D .four]

/-- The witness deal: pile 0 is the heart seven alone, pile 1 the
diamond seven over a filler; the twin hosts are the dealt heads of
their piles (the board_edges deal-adjacency clause), all 52 distinct. -/
private def nkDeal : Deal where
  piles := fun a =>
    match a with
    | .p0 => [H .seven]
    | .p1 => [D .seven, S .ace]
    | .p2 => [S .two, S .three, S .four]
    | .p3 => [S .five, S .seven, S .eight, S .nine]
    | .p4 => [S .ten, S .jack, S .queen, S .king, H .eight]
    | .p5 => [H .nine, H .ten, H .jack, H .queen, H .king, D .five]
    | .p6 => [D .six, D .eight, D .nine, D .ten, D .jack, D .queen, D .king]
  stock := nkStockList

/-- The twin-split state: the two destination twins seated and free,
all foundations at 0, all depths 0, draw step 1, ♠6 drawn first. -/
def nkState : State where
  deal := nkDeal
  board := nkBoard
  heights := fun _ => 0
  depths := fun _ => 0
  stock := ⟨nkStockList, 0⟩
  drawStep := 1

/-! ### The state is WF -/

private theorem nkHeights0 (s : Suit) : nkState.heights s = 0 := rfl

private theorem nkDeal_wf : nkDeal.WF := by
  refine ⟨fun a => ?_, by decide, ?_⟩
  · cases a <;> decide
  · intro i j hi hj heq
    have hflat : (Anchor.all.flatMap nkDeal.piles).length = 28 := by decide
    have hstock : nkDeal.stock.length = 24 := by decide
    rw [List.length_append, hflat, hstock] at hi hj
    have hall : ∀ i ∈ List.range 52, ∀ j ∈ List.range 52,
        (Anchor.all.flatMap nkDeal.piles ++ nkDeal.stock)[i]? =
          (Anchor.all.flatMap nkDeal.piles ++ nkDeal.stock)[j]? → i = j := by decide
    exact hall i (List.mem_range.mpr hi) j (List.mem_range.mpr hj) heq

private theorem nkState_wf : nkState.WF := by
  refine State.WF.intro nkDeal_wf ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · -- depths_le
    intro a
    show (0 : Nat) ≤ (nkDeal.piles a).length
    cases a <;> decide
  · -- board_edges: the only edges are the two dealt-head seats
    intro b c hb
    have hb' : nkBoard.topOf b = some c := hb
    cases b with
    | inl a =>
        rw [nkBoard_topOf_inl] at hb'
        cases a with
        | p0 =>
            have hc : c = H .seven := (Option.some.inj hb').symm
            refine ⟨(Board.bottomOf_eq _ _ _).mpr hb', ?_⟩
            rw [hc]
            show (H .seven).rank = Rank.king ∨
              (nkDeal.piles Anchor.p0).head? = some (H .seven)
            exact Or.inr rfl
        | p1 =>
            have hc : c = D .seven := (Option.some.inj hb').symm
            refine ⟨(Board.bottomOf_eq _ _ _).mpr hb', ?_⟩
            rw [hc]
            show (D .seven).rank = Rank.king ∨
              (nkDeal.piles Anchor.p1).head? = some (D .seven)
            exact Or.inr rfl
        | p2 => rw [show nkHead Anchor.p2 = none from rfl] at hb'; simp at hb'
        | p3 => rw [show nkHead Anchor.p3 = none from rfl] at hb'; simp at hb'
        | p4 => rw [show nkHead Anchor.p4 = none from rfl] at hb'; simp at hb'
        | p5 => rw [show nkHead Anchor.p5 = none from rfl] at hb'; simp at hb'
        | p6 => rw [show nkHead Anchor.p6 = none from rfl] at hb'; simp at hb'
    | inr d =>
        rw [nkBoard_topOf_inr] at hb'
        exact absurd hb' (by simp)
  · -- vis_off_cycle: a seated card is a twin host, never stocked
    intro c hc
    have hc' : (nkState.board.bottomOf c).isSome = true := hc
    rcases nkSeated c hc' with e | e <;> rw [e]
    · exact Cycle.posOf_eq_none (show H .seven ∉ nkStockList by decide)
    · exact Cycle.posOf_eq_none (show D .seven ∉ nkStockList by decide)
  · -- found_off_cycle: the premise is absurd at zero heights
    intro c h
    have hc : decide (c.rank.toIdx < nkState.heights c.suit) = true := h
    rw [nkHeights0] at hc
    simp at hc
  · -- founds_gone: vacuous at zero heights
    intro c hc
    rw [nkHeights0] at hc
    exact absurd hc (by omega)
  · -- vis_not_hidden: depths 0, the hidden slices are empty
    intro c _ a
    show ¬ (c ∈ (nkDeal.piles a).take (0 : Nat))
    rw [List.take_zero]
    simp
  · -- heights_le
    intro _
    exact Nat.zero_le _
  · -- cursor_le
    show nkState.stock.cursor ≤ nkState.stock.cards.length
    decide
  · -- step_pos
    exact Nat.zero_lt_one
  · -- stock_wf
    refine ⟨fun i j hi hj heq => ?_, fun _ hmem => hmem⟩
    have hall : ∀ i ∈ List.range 24, ∀ j ∈ List.range 24,
        nkStockList[i]? = nkStockList[j]? → i = j := by decide
    exact hall i (List.mem_range.mpr hi) j (List.mem_range.mpr hj) heq

/-! ### The twin hosts, the drawn card, the live channels -/

/-- The drawn card is a non-king (its own rank). -/
theorem nkNonKing : (S .six).rank ≠ Rank.king := by decide

/-- The drawn card is reachable at the stock's first position. -/
private theorem nkState_pos : nkState.reachablePos (S .six) = some 0 := by
  rw [State.reachablePos_step1 nkState_wf rfl (S .six)]
  rfl

private theorem nkVisHeart : nkState.isVis (H .seven) = true := by
  show (nkBoard.bottomOf (H .seven)).isSome = true
  rw [(Board.bottomOf_eq nkBoard (H .seven) (Sum.inl Anchor.p0)).mpr
    (nkBoard_topOf_inl Anchor.p0)]
  rfl

private theorem nkVisDiamond : nkState.isVis (D .seven) = true := by
  show (nkBoard.bottomOf (D .seven)).isSome = true
  rw [(Board.bottomOf_eq nkBoard (D .seven) (Sum.inl Anchor.p1)).mpr
    (nkBoard_topOf_inl Anchor.p1)]
  rfl

/-- The twin channel liveness, heart side: DirectLive at the root. -/
theorem nkDirectLive1 : DirectLive nkState (S .six) (H .seven) :=
  ⟨by decide,
    by rw [show nkState.board.topOf (Sum.inr (H .seven)) = none from rfl],
    nkVisHeart⟩

/-- DirectLive at the root, diamond side. -/
theorem nkDirectLive2 : DirectLive nkState (S .six) (D .seven) :=
  ⟨by decide,
    by rw [show nkState.board.topOf (Sum.inr (D .seven)) = none from rfl],
    nkVisDiamond⟩

/-- The drawn card's suit prefix is incomplete — the rung premise
fails: rank 5 against the standing 0. -/
theorem nkRungFails : (S .six).rank.toIdx ≠ nkState.heights (S .six).suit := by decide

/-! ### The two landings -/

/-- The landing successor on the heart twin. -/
def nkS1 : State :=
  (nkState.applyDrawTo (S .six) (Sum.inr (H .seven))).getD nkState

/-- The landing successor on the diamond twin. -/
def nkS2 : State :=
  (nkState.applyDrawTo (S .six) (Sum.inr (D .seven))).getD nkState

private theorem nkCanPlace1 : nkState.canPlace (S .six) (Sum.inr (H .seven)) = true :=
  nkDirectLive1.canPlace

private theorem nkCanPlace2 : nkState.canPlace (S .six) (Sum.inr (D .seven)) = true :=
  nkDirectLive2.canPlace

private theorem nkS1_apply :
    nkState.applyDrawTo (S .six) (Sum.inr (H .seven)) = some nkS1 := by
  have hne : nkBoard.attach (Sum.inr (H .seven)) (S .six) ≠ none :=
    (Board.attach_eq_some_iff _ _ _).mpr
      ⟨by rw [show nkBoard.topOf (Sum.inr (H .seven)) = none from rfl], nkBottomSix⟩
  cases hatt : nkBoard.attach (Sum.inr (H .seven)) (S .six) with
  | none => exact absurd hatt hne
  | some bd =>
      have hto : nkState.applyDrawTo (S .six) (Sum.inr (H .seven)) = some
          { nkState with board := bd, stock := (nkState.stock.drawTo 0).removeAt 0 } :=
        applyDrawTo_iff.mpr ⟨0, bd, nkState_pos, hatt, rfl⟩
      cases h : nkState.applyDrawTo (S .six) (Sum.inr (H .seven)) with
      | none =>
          have h2 := hto
          rw [h] at h2
          simp at h2
      | some s' =>
          have hw : nkS1 = s' := by
            show (nkState.applyDrawTo (S .six) (Sum.inr (H .seven))).getD nkState = s'
            rw [h]
            rfl
          rw [hw]

private theorem nkS2_apply :
    nkState.applyDrawTo (S .six) (Sum.inr (D .seven)) = some nkS2 := by
  have hne : nkBoard.attach (Sum.inr (D .seven)) (S .six) ≠ none :=
    (Board.attach_eq_some_iff _ _ _).mpr
      ⟨by rw [show nkBoard.topOf (Sum.inr (D .seven)) = none from rfl], nkBottomSix⟩
  cases hatt : nkBoard.attach (Sum.inr (D .seven)) (S .six) with
  | none => exact absurd hatt hne
  | some bd =>
      have hto : nkState.applyDrawTo (S .six) (Sum.inr (D .seven)) = some
          { nkState with board := bd, stock := (nkState.stock.drawTo 0).removeAt 0 } :=
        applyDrawTo_iff.mpr ⟨0, bd, nkState_pos, hatt, rfl⟩
      cases h : nkState.applyDrawTo (S .six) (Sum.inr (D .seven)) with
      | none =>
          have h2 := hto
          rw [h] at h2
          simp at h2
      | some s' =>
          have hw : nkS2 = s' := by
            show (nkState.applyDrawTo (S .six) (Sum.inr (D .seven))).getD nkState = s'
            rw [h]
            rfl
          rw [hw]

/-- The heart landing's successor is a tableau commit at the root. -/
theorem nkCommit1 : CommitTableau nkState (S .six) nkS1 :=
  ⟨Sum.inr (H .seven), nkCanPlace1, nkS1_apply⟩

/-- Same, diamond side. -/
theorem nkCommit2 : CommitTableau nkState (S .six) nkS2 :=
  ⟨Sum.inr (D .seven), nkCanPlace2, nkS2_apply⟩

/-- Each landing IS a macro step of the commitment. -/
theorem nkStep1 : macroStep nkState (MacroMove.drawCommit (S .six)) nkS1 :=
  ⟨nkState, ⟨[], rfl, fun _ hm => by simp at hm⟩,
    ⟨Sum.inr (H .seven), Or.inl ⟨nkCanPlace1, nkS1_apply⟩⟩⟩

theorem nkStep2 : macroStep nkState (MacroMove.drawCommit (S .six)) nkS2 :=
  ⟨nkState, ⟨[], rfl, fun _ hm => by simp at hm⟩,
    ⟨Sum.inr (D .seven), Or.inl ⟨nkCanPlace2, nkS2_apply⟩⟩⟩

/-- Both landings go through the live `direct` channel at the root,
with the empty signature window. -/
theorem nkSuccThrough1 : SuccThrough nkState (S .six) Label.direct nkS1 :=
  ⟨nkState, [], rfl, fun _ hm => by simp at hm, nkCommit1, rfl⟩

theorem nkSuccThrough2 : SuccThrough nkState (S .six) Label.direct nkS2 :=
  ⟨nkState, [], rfl, fun _ hm => by simp at hm, nkCommit2, rfl⟩

/-- The direct channel is live at the root. -/
theorem nkDirectLive : LabelLive nkState (S .six) Label.direct :=
  ⟨H .seven, nkDirectLive1⟩

/-! ### The landing states' shape facts -/

private theorem nkS1_heights0 (s : Suit) : nkS1.heights s = 0 := by
  obtain ⟨i, bd, hpos, hatt, hs⟩ := applyDrawTo_eq nkS1_apply
  rw [hs]
  rfl

private theorem nkS2_heights0 (s : Suit) : nkS2.heights s = 0 := by
  obtain ⟨i, bd, hpos, hatt, hs⟩ := applyDrawTo_eq nkS2_apply
  rw [hs]
  rfl

/-- The landed card sits on the heart twin's base. -/
private theorem nkS1_bottomOf_six :
    nkS1.board.bottomOf (S .six) = some (Sum.inr (H .seven)) := by
  obtain ⟨i, bd, hpos, hatt, hs⟩ := applyDrawTo_eq nkS1_apply
  rw [hs]
  exact (Board.bottomOf_eq bd (S .six) (Sum.inr (H .seven))).mpr
    (Board.attach_topOf nkBoard _ _ hatt)

private theorem nkS2_bottomOf_six :
    nkS2.board.bottomOf (S .six) = some (Sum.inr (D .seven)) := by
  obtain ⟨i, bd, hpos, hatt, hs⟩ := applyDrawTo_eq nkS2_apply
  rw [hs]
  exact (Board.bottomOf_eq bd (S .six) (Sum.inr (D .seven))).mpr
    (Board.attach_topOf nkBoard _ _ hatt)

private theorem nkS1_topOf (b : Base) : nkS1.board.topOf b =
    (if b = Sum.inr (H .seven) then some (S .six) else nkBoard.topOf b) := by
  obtain ⟨i, bd, hpos, hatt, hs⟩ := applyDrawTo_eq nkS1_apply
  rw [hs]
  by_cases hbeq : b = Sum.inr (H .seven)
  · rw [hbeq, if_pos rfl]
    exact Board.attach_topOf nkBoard _ _ hatt
  · rw [if_neg hbeq]
    exact Board.attach_topOf_ne nkBoard _ _ hatt hbeq

private theorem nkS2_topOf (b : Base) : nkS2.board.topOf b =
    (if b = Sum.inr (D .seven) then some (S .six) else nkBoard.topOf b) := by
  obtain ⟨i, bd, hpos, hatt, hs⟩ := applyDrawTo_eq nkS2_apply
  rw [hs]
  by_cases hbeq : b = Sum.inr (D .seven)
  · rw [hbeq, if_pos rfl]
    exact Board.attach_topOf nkBoard _ _ hatt
  · rw [if_neg hbeq]
    exact Board.attach_topOf_ne nkBoard _ _ hatt hbeq

/-- Only the landed card and the two twin hosts are seated at the
heart landing. -/
private theorem nkS1_seated (c : Card) (h : (nkS1.board.bottomOf c).isSome = true) :
    c = S .six ∨ c = H .seven ∨ c = D .seven := by
  obtain ⟨b, hb⟩ : ∃ b, nkS1.board.bottomOf c = some b := by
    cases hbot : nkS1.board.bottomOf c with
    | none => rw [hbot] at h; simp at h
    | some b => exact ⟨b, rfl⟩
  have htb : nkS1.board.topOf b = some c := (Board.bottomOf_eq _ _ _).mp hb
  rw [nkS1_topOf] at htb
  by_cases hbeq : b = Sum.inr (H .seven)
  · rw [hbeq, if_pos rfl] at htb
    exact Or.inl (Option.some.inj htb).symm
  · rw [if_neg hbeq] at htb
    have hseat : (nkBoard.bottomOf c).isSome = true :=
      nkBottomOf_isSome c b htb
    rcases nkSeated c hseat with e | e
    · exact Or.inr (Or.inl e)
    · exact Or.inr (Or.inr e)

private theorem nkS2_seated (c : Card) (h : (nkS2.board.bottomOf c).isSome = true) :
    c = S .six ∨ c = H .seven ∨ c = D .seven := by
  obtain ⟨b, hb⟩ : ∃ b, nkS2.board.bottomOf c = some b := by
    cases hbot : nkS2.board.bottomOf c with
    | none => rw [hbot] at h; simp at h
    | some b => exact ⟨b, rfl⟩
  have htb : nkS2.board.topOf b = some c := (Board.bottomOf_eq _ _ _).mp hb
  rw [nkS2_topOf] at htb
  by_cases hbeq : b = Sum.inr (D .seven)
  · rw [hbeq, if_pos rfl] at htb
    exact Or.inl (Option.some.inj htb).symm
  · rw [if_neg hbeq] at htb
    have hseat : (nkBoard.bottomOf c).isSome = true :=
      nkBottomOf_isSome c b htb
    rcases nkSeated c hseat with e | e
    · exact Or.inr (Or.inl e)
    · exact Or.inr (Or.inr e)

/-! ### The closure is frozen at each landing -/

private theorem nkS1_dead_pileStack (c : Card) (t : State)
    (h : nkS1.apply (Move.pileStack c) = some t) : False := by
  rw [apply_pileStack_iff] at h
  obtain ⟨htopfree, b, hb, hrk, hshape⟩ := h
  have his : (nkS1.board.bottomOf c).isSome = true := by rw [hb]; rfl
  rcases nkS1_seated c his with e | e | e
  · rw [e, nkS1_heights0] at hrk
    exact absurd hrk (by decide)
  · rw [e, nkS1_heights0] at hrk
    exact absurd hrk (by decide)
  · rw [e, nkS1_heights0] at hrk
    exact absurd hrk (by decide)

private theorem nkS2_dead_pileStack (c : Card) (t : State)
    (h : nkS2.apply (Move.pileStack c) = some t) : False := by
  rw [apply_pileStack_iff] at h
  obtain ⟨htopfree, b, hb, hrk, hshape⟩ := h
  have his : (nkS2.board.bottomOf c).isSome = true := by rw [hb]; rfl
  rcases nkS2_seated c his with e | e | e
  · rw [e, nkS2_heights0] at hrk
    exact absurd hrk (by decide)
  · rw [e, nkS2_heights0] at hrk
    exact absurd hrk (by decide)
  · rw [e, nkS2_heights0] at hrk
    exact absurd hrk (by decide)

private theorem nkS1_dead_stackPile (c : Card) (b : Base) (t : State)
    (h : nkS1.apply (Move.stackPile c b) = some t) : False := by
  rw [apply_stackPile_iff] at h
  obtain ⟨hg, hcp, bd, hatt, hshape⟩ := h
  rw [nkS1_heights0] at hg
  omega

private theorem nkS2_dead_stackPile (c : Card) (b : Base) (t : State)
    (h : nkS2.apply (Move.stackPile c b) = some t) : False := by
  rw [apply_stackPile_iff] at h
  obtain ⟨hg, hcp, bd, hatt, hshape⟩ := h
  rw [nkS2_heights0] at hg
  omega

private theorem nkS1_dead (m : Move) (hm : m.isAccommodation = true) (t : State)
    (hap : nkS1.apply m = some t) : False := by
  cases m with
  | pileStack c => exact nkS1_dead_pileStack c t hap
  | stackPile c b => exact nkS1_dead_stackPile c b t hap
  | draw => simp [Move.isAccommodation] at hm
  | reveal a => simp [Move.isAccommodation] at hm
  | deckPile c b => simp [Move.isAccommodation] at hm
  | deckStack c => simp [Move.isAccommodation] at hm
  | pilePile c b => simp [Move.isAccommodation] at hm

private theorem nkS2_dead (m : Move) (hm : m.isAccommodation = true) (t : State)
    (hap : nkS2.apply m = some t) : False := by
  cases m with
  | pileStack c => exact nkS2_dead_pileStack c t hap
  | stackPile c b => exact nkS2_dead_stackPile c b t hap
  | draw => simp [Move.isAccommodation] at hm
  | reveal a => simp [Move.isAccommodation] at hm
  | deckPile c b => simp [Move.isAccommodation] at hm
  | deckStack c => simp [Move.isAccommodation] at hm
  | pilePile c b => simp [Move.isAccommodation] at hm

/-- Each landing state is its own accommodation closure. -/
theorem nkS1_stuck (s' : State) (hacc : accommodates nkS1 s') : s' = nkS1 := by
  obtain ⟨play, hrun, hall⟩ := hacc
  induction play generalizing s' with
  | nil => exact (Option.some.inj hrun).symm
  | cons m ms ih =>
      have hm : m.isAccommodation = true := hall m (by simp)
      have hrun' : (match nkS1.apply m with
        | some s'' => s''.run ms | none => none) = some s' := hrun
      cases hap : nkS1.apply m with
      | none => rw [hap] at hrun'; exact absurd hrun' (by simp)
      | some s₁ => rw [hap] at hrun'; exact (nkS1_dead m hm s₁ hap).elim

theorem nkS2_stuck (s' : State) (hacc : accommodates nkS2 s') : s' = nkS2 := by
  obtain ⟨play, hrun, hall⟩ := hacc
  induction play generalizing s' with
  | nil => exact (Option.some.inj hrun).symm
  | cons m ms ih =>
      have hm : m.isAccommodation = true := hall m (by simp)
      have hrun' : (match nkS2.apply m with
        | some s'' => s''.run ms | none => none) = some s' := hrun
      cases hap : nkS2.apply m with
      | none => rw [hap] at hrun'; exact absurd hrun' (by simp)
      | some s₁ => rw [hap] at hrun'; exact (nkS2_dead m hm s₁ hap).elim

/-- **The split**: the two twin landings of one non-king commitment,
through the same zero-spend channel, are closure-SEPARATED. -/
theorem nk_split : ¬ closureEq nkS1 nkS2 := by
  rintro ⟨hfwd, hbwd⟩
  have heq : nkS2 = nkS1 := nkS1_stuck nkS2 hfwd
  have h1 : nkS1.board.bottomOf (S .six) = some (Sum.inr (H .seven)) :=
    nkS1_bottomOf_six
  have h2 : nkS1.board.bottomOf (S .six) = some (Sum.inr (D .seven)) := by
    rw [← heq]
    exact nkS2_bottomOf_six
  exact absurd (Option.some.inj (h1.symm.trans h2)) (by decide)

/-! ### The refuted non-king universals -/

/-- **`commitTableau_class` without its rung premise, restricted to
non-kings, is REFUTED**: two zero-spend tableau commits of a non-king
drawn card at a WF state whose suit prefix is incomplete need not be
closure-equal.  The rung premise is load-bearing on the TWIN side too
(not only at the king-anchor landings of
`witnesses/C2KingAnchorWitness.lean`): the shuttle's vehicle is X's
own foundation round trip, and an incomplete prefix kills it. -/
theorem wk_nonking_twinCollapse_rung_false :
    ¬ (∀ (st : State) (X : Card) (s s' : State), st.WF → X.rank ≠ Rank.king →
        CommitTableau st X s → CommitTableau st X s' → closureEq s s') := by
  intro h
  exact nk_split (h nkState (S .six) nkS1 nkS2 nkState_wf nkNonKing
    nkCommit1 nkCommit2)

/-- **`same_pin_closureEq` restricted to non-kings is REFUTED**: the
`direct` channel is live at the root, both split landings go through
it (empty signature windows), and they stay split. -/
theorem wk_nonking_samePin_direct_false :
    ¬ (∀ (st : State) (X : Card) (r : Label X) (s s' : State), st.WF →
        X.rank ≠ Rank.king → LabelLive st X r → SuccThrough st X r s →
        SuccThrough st X r s' → closureEq s s') := by
  intro h
  exact nk_split (h nkState (S .six) Label.direct nkS1 nkS2 nkState_wf nkNonKing
    nkDirectLive nkSuccThrough1 nkSuccThrough2)

/-- **`p2_direct_class` restricted to non-kings is REFUTED**: the
heart landing is the root commit's own successor, the diamond landing
is a P2-safe direct-channel successor, and the class join fails. -/
theorem wk_nonking_p2Direct_false :
    ¬ (∀ (st : State) (X : Card) (sd s_p : State) (r : Label X), st.WF →
        X.rank ≠ Rank.king → commitApplies st (MacroMove.drawCommit X) sd →
        SuccThrough st X r s_p → P2Safe st X r → closureEq sd s_p) := by
  intro h
  exact nk_split (h nkState (S .six) nkS1 nkS2 Label.direct nkState_wf nkNonKing
    ⟨Sum.inr (H .seven), Or.inl ⟨nkCanPlace1, nkS1_apply⟩⟩ nkSuccThrough2 trivial)

/-! ### The honest boundary datum: the count survives the split

The passage is the destination bound: the two root commits are the
ONLY macro successors of the commitment at `nkState` (every
accommodation is dead at the root too, and no `commitApplies` arm
exists beyond the two twin hosts), so any three successors contain a
repetition — the two-option count holds WITHOUT the rung, while every
closure-join of the two landings fails. -/

private theorem nkRoot_dead_pileStack (c : Card) (t : State)
    (h : nkState.apply (Move.pileStack c) = some t) : False := by
  rw [apply_pileStack_iff] at h
  obtain ⟨htopfree, b, hb, hrk, hshape⟩ := h
  have his : (nkState.board.bottomOf c).isSome = true := by rw [hb]; rfl
  rcases nkSeated c his with e | e
  · rw [e] at hrk
    exact absurd hrk (by decide)
  · rw [e] at hrk
    exact absurd hrk (by decide)

private theorem nkRoot_dead_stackPile (c : Card) (b : Base) (t : State)
    (h : nkState.apply (Move.stackPile c b) = some t) : False := by
  rw [apply_stackPile_iff] at h
  obtain ⟨hg, hcp, bd, hatt, hshape⟩ := h
  rw [show nkState.heights c.suit = 0 from rfl] at hg
  omega

private theorem nkRoot_accommodates_self (u : State)
    (hacc : accommodates nkState u) : u = nkState := by
  obtain ⟨play, hrun, hall⟩ := hacc
  induction play generalizing u with
  | nil => exact (Option.some.inj hrun).symm
  | cons m ms ih =>
      have hm : m.isAccommodation = true := hall m (by simp)
      have hrun' : (match nkState.apply m with
        | some s'' => s''.run ms | none => none) = some u := hrun
      cases hap : nkState.apply m with
      | none => rw [hap] at hrun'; exact absurd hrun' (by simp)
      | some s₁ =>
          exfalso
          cases m with
          | pileStack c => exact nkRoot_dead_pileStack c s₁ hap
          | stackPile c b => exact nkRoot_dead_stackPile c b s₁ hap
          | draw => simp [Move.isAccommodation] at hm
          | reveal a => simp [Move.isAccommodation] at hm
          | deckPile c b => simp [Move.isAccommodation] at hm
          | deckStack c => simp [Move.isAccommodation] at hm
          | pilePile c b => simp [Move.isAccommodation] at hm

/-- **The destination bound, witnessed**: the commitment at `nkState`
has EXACTLY the two twin landings as macro successors — the anchor
arm demands a king, the stack arm the incomplete rung, and the
tableau receivers are the twin pair. -/
theorem nkSuccessorsExhaustTwo (s : State)
    (hstep : macroStep nkState (MacroMove.drawCommit (S .six)) s) :
    s = nkS1 ∨ s = nkS2 := by
  obtain ⟨u, ⟨play, hrun, hall⟩, hcom⟩ := hstep
  have hu : u = nkState := nkRoot_accommodates_self u ⟨play, hrun, hall⟩
  rw [hu] at hcom
  rcases (commitApplies_draw_cases nkState (S .six) s).mp hcom with
    ⟨b, hcp, hto⟩ | hst
  · cases b with
    | inl a => exact absurd (king_of_canPlace_inl hcp) nkNonKing
    | inr d =>
        obtain ⟨htopn, hvis, hfitc⟩ := canPlace_inr_iff.mp hcp
        rcases nkSeated d hvis with e | e
        · left
          rw [e] at hto
          exact (Option.some.inj (nkS1_apply.symm.trans hto)).symm
        · right
          rw [e] at hto
          exact (Option.some.inj (nkS2_apply.symm.trans hto)).symm
  · exfalso
    obtain ⟨i, hpos, hrk, hshape⟩ := applyDrawStackTo_iff.mp hst
    rw [show nkState.heights (S .six).suit = 0 from rfl] at hrk
    exact absurd hrk (by decide)

/-- The two-option count holds at the twin-split state itself — no
rung, no join, no labels: the destination count does the whole work. -/
theorem nkTwoOptionHoldsHere (s₁ s₂ s₃ : State)
    (h₁ : macroStep nkState (MacroMove.drawCommit (S .six)) s₁)
    (h₂ : macroStep nkState (MacroMove.drawCommit (S .six)) s₂)
    (h₃ : macroStep nkState (MacroMove.drawCommit (S .six)) s₃) :
    closureEq s₁ s₂ ∨ closureEq s₁ s₃ ∨ closureEq s₂ s₃ := by
  rcases nkSuccessorsExhaustTwo s₁ h₁ with e₁ | e₁ <;>
    rcases nkSuccessorsExhaustTwo s₂ h₂ with e₂ | e₂ <;>
    rcases nkSuccessorsExhaustTwo s₃ h₃ with e₃ | e₃ <;>
    rw [e₁, e₂, e₃] <;>
    first
      | exact Or.inl (closureEq_refl _)
      | exact Or.inr (Or.inl (closureEq_refl _))
      | exact Or.inr (Or.inr (closureEq_refl _))

end NK

/-! ## §B — the free-float labeling gap for non-kings -/

namespace FF

/-- Spades. -/
private def S (r : Rank) : Card := ⟨Suit.spade, r⟩
/-- Hearts. -/
private def H (r : Rank) : Card := ⟨Suit.heart, r⟩
/-- Diamonds. -/
private def D (r : Rank) : Card := ⟨Suit.diamond, r⟩
/-- Clubs. -/
private def C (r : Rank) : Card := ⟨Suit.club, r⟩

/-- The dealt seats: the two twin hosts (piles 0 and 1) plus the FREE
anchored head ♥A (pile 2) — the free-float window's fuel. -/
private def ffHead : Anchor → Option Card
  | .p0 => some (H .seven)
  | .p1 => some (D .seven)
  | .p2 => some (H .ace)
  | _ => none

private theorem ffHead_none (a : Anchor) (c : Card)
    (h₁ : ffHead a = none) (h₂ : ffHead a = some c) : False := by
  rw [h₂] at h₁
  exact absurd h₁ (by simp)

private theorem ffHead_inj : ∀ (a a' : Anchor) (c : Card),
    ffHead a = some c → ffHead a' = some c → a = a' := by
  intro a a' c h₁ h₂
  cases a with
  | p0 =>
      have h₁' : some (H .seven) = some c := h₁
      cases a' with
      | p0 => rfl
      | p1 =>
          have h₂' : some (D .seven) = some c := h₂
          exact absurd ((Option.some.inj h₁').trans (Option.some.inj h₂').symm)
            (by decide)
      | p2 =>
          have h₂' : some (H .ace) = some c := h₂
          exact absurd ((Option.some.inj h₁').trans (Option.some.inj h₂').symm)
            (by decide)
      | p3 => exact (ffHead_none Anchor.p3 c rfl h₂).elim
      | p4 => exact (ffHead_none Anchor.p4 c rfl h₂).elim
      | p5 => exact (ffHead_none Anchor.p5 c rfl h₂).elim
      | p6 => exact (ffHead_none Anchor.p6 c rfl h₂).elim
  | p1 =>
      have h₁' : some (D .seven) = some c := h₁
      cases a' with
      | p0 =>
          have h₂' : some (H .seven) = some c := h₂
          exact absurd ((Option.some.inj h₁').trans (Option.some.inj h₂').symm)
            (by decide)
      | p1 => rfl
      | p2 =>
          have h₂' : some (H .ace) = some c := h₂
          exact absurd ((Option.some.inj h₁').trans (Option.some.inj h₂').symm)
            (by decide)
      | p3 => exact (ffHead_none Anchor.p3 c rfl h₂).elim
      | p4 => exact (ffHead_none Anchor.p4 c rfl h₂).elim
      | p5 => exact (ffHead_none Anchor.p5 c rfl h₂).elim
      | p6 => exact (ffHead_none Anchor.p6 c rfl h₂).elim
  | p2 =>
      have h₁' : some (H .ace) = some c := h₁
      cases a' with
      | p0 =>
          have h₂' : some (H .seven) = some c := h₂
          exact absurd ((Option.some.inj h₁').trans (Option.some.inj h₂').symm)
            (by decide)
      | p1 =>
          have h₂' : some (D .seven) = some c := h₂
          exact absurd ((Option.some.inj h₁').trans (Option.some.inj h₂').symm)
            (by decide)
      | p2 => rfl
      | p3 => exact (ffHead_none Anchor.p3 c rfl h₂).elim
      | p4 => exact (ffHead_none Anchor.p4 c rfl h₂).elim
      | p5 => exact (ffHead_none Anchor.p5 c rfl h₂).elim
      | p6 => exact (ffHead_none Anchor.p6 c rfl h₂).elim
  | p3 => exact (ffHead_none Anchor.p3 c rfl h₁).elim
  | p4 => exact (ffHead_none Anchor.p4 c rfl h₁).elim
  | p5 => exact (ffHead_none Anchor.p5 c rfl h₁).elim
  | p6 => exact (ffHead_none Anchor.p6 c rfl h₁).elim

private def ffTopOf : Base → Option Card := fun b =>
  match b with
  | Sum.inl a => ffHead a
  | Sum.inr _ => none

private theorem ffTopOf_inl (a : Anchor) : ffTopOf (Sum.inl a) = ffHead a := rfl
private theorem ffTopOf_inr (d : Card) : ffTopOf (Sum.inr d) = none := rfl

private theorem ffBoard_inj : ∀ (b₁ b₂ : Base) (c : Card),
    ffTopOf b₁ = some c → ffTopOf b₂ = some c → b₁ = b₂ := by
  intro b₁ b₂ c h₁ h₂
  cases b₁ with
  | inl a =>
      cases b₂ with
      | inl a' =>
          rw [ffTopOf_inl] at h₁
          rw [ffTopOf_inl] at h₂
          exact congrArg Sum.inl (ffHead_inj a a' c h₁ h₂)
      | inr d =>
          rw [ffTopOf_inr] at h₂
          exact absurd h₂ (by simp)
  | inr d =>
      rw [ffTopOf_inr] at h₁
      exact absurd h₁ (by simp)

private def ffBoard : Board := ⟨ffTopOf, ffBoard_inj⟩

private theorem ffBoard_topOf_inl (a : Anchor) :
    ffBoard.topOf (Sum.inl a) = ffHead a := rfl

private theorem ffBoard_topOf_inr (d : Card) : ffBoard.topOf (Sum.inr d) = none := rfl

/-- Only the three dealt heads are seated anywhere. -/
private theorem ffSeated (c : Card) (h : (ffBoard.bottomOf c).isSome = true) :
    c = H .seven ∨ c = D .seven ∨ c = H .ace := by
  obtain ⟨b, hb⟩ : ∃ b, ffBoard.bottomOf c = some b := by
    cases hbot : ffBoard.bottomOf c with
    | none => rw [hbot] at h; simp at h
    | some b => exact ⟨b, rfl⟩
  have htb : ffBoard.topOf b = some c := (Board.bottomOf_eq _ _ _).mp hb
  cases b with
  | inl a =>
      rw [ffBoard_topOf_inl] at htb
      cases a with
      | p0 => exact Or.inl (Option.some.inj htb).symm
      | p1 => exact Or.inr (Or.inl (Option.some.inj htb).symm)
      | p2 => exact Or.inr (Or.inr (Option.some.inj htb).symm)
      | p3 => rw [show ffHead Anchor.p3 = none from rfl] at htb; simp at htb
      | p4 => rw [show ffHead Anchor.p4 = none from rfl] at htb; simp at htb
      | p5 => rw [show ffHead Anchor.p5 = none from rfl] at htb; simp at htb
      | p6 => rw [show ffHead Anchor.p6 = none from rfl] at htb; simp at htb
  | inr d =>
      rw [ffBoard_topOf_inr] at htb
      exact absurd htb (by simp)

private theorem ffBottomOf_isSome (c : Card) (b : Base)
    (htb : ffBoard.topOf b = some c) : (ffBoard.bottomOf c).isSome = true := by
  rw [(Board.bottomOf_eq ffBoard c b).mpr htb]
  rfl

/-- No spade is seated on the dealt board (the freeze invariant's
base case). -/
private theorem ffSpades_unseated (c : Card) (hcs : c.suit = Suit.spade) :
    ffBoard.bottomOf c = none := by
  refine (Board.bottomOf_eq_none ffBoard c).mpr (fun b hb => ?_)
  have his := ffBottomOf_isSome c b hb
  rcases ffSeated c his with e | e | e <;> rw [e] at hcs <;>
    exact absurd hcs (by decide)

private def ffStockList : List Card :=
  [S .six] ++
  [H .two, H .three, H .four, H .five, H .six] ++
  [D .ace, D .two, D .three, D .four, D .king] ++
  [C .ace, C .two, C .three, C .four, C .five, C .six, C .seven, C .eight,
   C .nine, C .ten, C .jack, C .queen, C .king]

/-- The free-float deal: the twin hosts and the anchored heart ace as
their piles' dealt heads, all 52 distinct, 24 stock cards. -/
private def ffDeal : Deal where
  piles := fun a =>
    match a with
    | .p0 => [H .seven]
    | .p1 => [D .seven, S .ace]
    | .p2 => [H .ace, S .two, S .three]
    | .p3 => [S .four, S .five, S .seven, S .eight]
    | .p4 => [S .nine, S .ten, S .jack, S .queen, S .king]
    | .p5 => [H .eight, H .nine, H .ten, H .jack, H .queen, H .king]
    | .p6 => [D .five, D .six, D .eight, D .nine, D .ten, D .jack, D .queen]
  stock := ffStockList

/-- The free-float state: the three anchored heads seated, zero
heights/depths, draw step 1, ♠6 drawn first. -/
def ffState : State where
  deal := ffDeal
  board := ffBoard
  heights := fun _ => 0
  depths := fun _ => 0
  stock := ⟨ffStockList, 0⟩
  drawStep := 1

private theorem ffHeights0 (s : Suit) : ffState.heights s = 0 := rfl

private theorem ffTopOf_inr_none (d : Card) :
    ffState.board.topOf (Sum.inr d) = none := rfl

private theorem ffDeal_wf : ffDeal.WF := by
  refine ⟨fun a => ?_, by decide, ?_⟩
  · cases a <;> decide
  · intro i j hi hj heq
    have hflat : (Anchor.all.flatMap ffDeal.piles).length = 28 := by decide
    have hstock : ffDeal.stock.length = 24 := by decide
    rw [List.length_append, hflat, hstock] at hi hj
    have hall : ∀ i ∈ List.range 52, ∀ j ∈ List.range 52,
        (Anchor.all.flatMap ffDeal.piles ++ ffDeal.stock)[i]? =
          (Anchor.all.flatMap ffDeal.piles ++ ffDeal.stock)[j]? → i = j := by decide
    exact hall i (List.mem_range.mpr hi) j (List.mem_range.mpr hj) heq

private theorem ffState_wf : ffState.WF := by
  refine State.WF.intro ffDeal_wf ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro a
    show (0 : Nat) ≤ (ffDeal.piles a).length
    cases a <;> decide
  · -- board_edges: the three dealt-head seats
    intro b c hb
    have hb' : ffBoard.topOf b = some c := hb
    cases b with
    | inl a =>
        rw [ffBoard_topOf_inl] at hb'
        cases a with
        | p0 =>
            have hc : c = H .seven := (Option.some.inj hb').symm
            refine ⟨(Board.bottomOf_eq _ _ _).mpr hb', ?_⟩
            rw [hc]
            show (H .seven).rank = Rank.king ∨
              (ffDeal.piles Anchor.p0).head? = some (H .seven)
            exact Or.inr rfl
        | p1 =>
            have hc : c = D .seven := (Option.some.inj hb').symm
            refine ⟨(Board.bottomOf_eq _ _ _).mpr hb', ?_⟩
            rw [hc]
            show (D .seven).rank = Rank.king ∨
              (ffDeal.piles Anchor.p1).head? = some (D .seven)
            exact Or.inr rfl
        | p2 =>
            have hc : c = H .ace := (Option.some.inj hb').symm
            refine ⟨(Board.bottomOf_eq _ _ _).mpr hb', ?_⟩
            rw [hc]
            show (H .ace).rank = Rank.king ∨
              (ffDeal.piles Anchor.p2).head? = some (H .ace)
            exact Or.inr rfl
        | p3 => rw [show ffHead Anchor.p3 = none from rfl] at hb'; simp at hb'
        | p4 => rw [show ffHead Anchor.p4 = none from rfl] at hb'; simp at hb'
        | p5 => rw [show ffHead Anchor.p5 = none from rfl] at hb'; simp at hb'
        | p6 => rw [show ffHead Anchor.p6 = none from rfl] at hb'; simp at hb'
    | inr d =>
        rw [ffBoard_topOf_inr] at hb'
        exact absurd hb' (by simp)
  · -- vis_off_cycle
    intro c hc
    have hc' : (ffState.board.bottomOf c).isSome = true := hc
    rcases ffSeated c hc' with e | e | e <;> rw [e]
    · exact Cycle.posOf_eq_none (show H .seven ∉ ffStockList by decide)
    · exact Cycle.posOf_eq_none (show D .seven ∉ ffStockList by decide)
    · exact Cycle.posOf_eq_none (show H .ace ∉ ffStockList by decide)
  · -- found_off_cycle: the premise is absurd at zero heights
    intro c h
    have hc : decide (c.rank.toIdx < ffState.heights c.suit) = true := h
    rw [ffHeights0] at hc
    simp at hc
  · -- founds_gone: vacuous at zero heights
    intro c hc
    rw [ffHeights0] at hc
    exact absurd hc (by omega)
  · -- vis_not_hidden
    intro c _ a
    show ¬ (c ∈ (ffDeal.piles a).take (0 : Nat))
    rw [List.take_zero]
    simp
  · -- heights_le
    intro _
    exact Nat.zero_le _
  · -- cursor_le
    show ffState.stock.cursor ≤ ffState.stock.cards.length
    decide
  · -- step_pos
    exact Nat.zero_lt_one
  · -- stock_wf
    refine ⟨fun i j hi hj heq => ?_, fun _ hmem => hmem⟩
    have hall : ∀ i ∈ List.range 24, ∀ j ∈ List.range 24,
        ffStockList[i]? = ffStockList[j]? → i = j := by decide
    exact hall i (List.mem_range.mpr hi) j (List.mem_range.mpr hj) heq

theorem ffNonKing : (S .six).rank ≠ Rank.king := by decide

private theorem ffState_pos : ffState.reachablePos (S .six) = some 0 := by
  rw [State.reachablePos_step1 ffState_wf rfl (S .six)]
  rfl

private theorem ffFitHeart : canSitOn (S .six) (H .seven) = true := by decide
private theorem ffFitDiamond : canSitOn (S .six) (D .seven) = true := by decide

/-- The direct channel is LIVE at the free-float root. -/
theorem ffDirectLive : LabelLive ffState (S .six) Label.direct :=
  ⟨H .seven,
    ⟨ffFitHeart,
      by rw [ffTopOf_inr_none],
      by
        show (ffBoard.bottomOf (H .seven)).isSome = true
        rw [(Board.bottomOf_eq ffBoard (H .seven) (Sum.inl Anchor.p0)).mpr
          (ffBoard_topOf_inl Anchor.p0)]
        rfl⟩⟩

/-! ### The spade freeze (the toStack liveness kill) -/

private theorem ffFreeze_step (st : State)
    (h0 : st.heights Suit.spade = 0)
    (hns : ∀ c : Card, c.suit = Suit.spade → st.board.bottomOf c = none)
    (m : Move) (hm : m.isAccommodation = true) (t : State)
    (hap : st.apply m = some t) :
    t.heights Suit.spade = 0 ∧
    ∀ c : Card, c.suit = Suit.spade → t.board.bottomOf c = none := by
  cases m with
  | pileStack c =>
      rw [apply_pileStack_iff] at hap
      obtain ⟨-, b, hbot, -, rfl⟩ := hap
      have hc : c.suit ≠ Suit.spade := by
        intro hcs
        rw [hns c hcs] at hbot
        exact absurd hbot (by simp)
      refine ⟨?_, ?_⟩
      · show (if Suit.spade = c.suit then st.heights Suit.spade + 1
            else st.heights Suit.spade) = 0
        rw [ite_eq_right (Ne.symm hc), h0]
      · intro d hds
        have hdc : d ≠ c := by
          intro hh
          rw [hh] at hds
          exact hc hds
        show (st.board.detach b).bottomOf d = none
        rw [bottomOf_detach_ne ((Board.bottomOf_eq _ _ _).mp hbot) hdc]
        exact hns d hds
  | stackPile c b =>
      rw [apply_stackPile_iff] at hap
      obtain ⟨hg, -, bd, hatt, rfl⟩ := hap
      have hc : c.suit ≠ Suit.spade := by
        intro hcs
        rw [hcs, h0] at hg
        omega
      refine ⟨?_, ?_⟩
      · show (if Suit.spade = c.suit then st.heights Suit.spade - 1
            else st.heights Suit.spade) = 0
        rw [ite_eq_right (Ne.symm hc), h0]
      · intro d hds
        have hdc : d ≠ c := by
          intro hh
          rw [hh] at hds
          exact hc hds
        show bd.bottomOf d = none
        rw [bottomOf_attach_of_ne hatt hdc]
        exact hns d hds
  | draw => simp [Move.isAccommodation] at hm
  | reveal a => simp [Move.isAccommodation] at hm
  | deckPile c b => simp [Move.isAccommodation] at hm
  | deckStack c => simp [Move.isAccommodation] at hm
  | pilePile c b => simp [Move.isAccommodation] at hm

private theorem ffFreeze_run (play : List Move) :
    ∀ (st : State), st.heights Suit.spade = 0 →
    (∀ c : Card, c.suit = Suit.spade → st.board.bottomOf c = none) →
    ∀ (t : State), (∀ m ∈ play, m.isAccommodation = true) →
      st.run play = some t →
      t.heights Suit.spade = 0 ∧
      ∀ c : Card, c.suit = Suit.spade → t.board.bottomOf c = none := by
  induction play with
  | nil =>
      intro st h0 hns t _ hrun
      have ht : st = t := Option.some.inj hrun
      subst ht
      exact ⟨h0, hns⟩
  | cons m ms ih =>
      intro st h0 hns t hall hrun
      have hm : m.isAccommodation = true := hall m (by simp)
      have hrun' : (match st.apply m with
        | some s' => s'.run ms | none => none) = some t := hrun
      cases hap : st.apply m with
      | none =>
          rw [hap] at hrun'
          exact absurd hrun' (by simp)
      | some s₁ =>
          rw [hap] at hrun'
          obtain ⟨h0₁, hns₁⟩ := ffFreeze_step st h0 hns m hm s₁ hap
          exact ih s₁ h0₁ hns₁ t
            (fun m' hm' => hall m' (List.mem_cons_of_mem _ hm')) hrun'

private theorem ffFrozenToStack (r s : State)
    (hacc : accommodates ffState r)
    (hfire : r.applyDrawStackTo (S .six) = some s) : False := by
  obtain ⟨play, hrun, hall⟩ := hacc
  obtain ⟨h0, -⟩ := ffFreeze_run play ffState (ffHeights0 _) ffSpades_unseated r hall hrun
  obtain ⟨i, hpos, hrk, hshape⟩ := applyDrawStackTo_iff.mp hfire
  have hrk2 : (S .six).rank.toIdx = r.heights Suit.spade := hrk
  have h5 : (S .six).rank.toIdx = 5 := rfl
  omega

/-! ### The free-float window and its successors -/

/-- The after-promotion state: the heart ace is gone to the foundation,
anchor 2 bare, heart height 1. -/
private def ffMid : State :=
  { ffState with
    board := ffState.board.detach (Sum.inl Anchor.p2),
    heights := fun s => if s = (H .ace).suit then ffState.heights s + 1
      else ffState.heights s }

/-- The anchored heart ace leaves: the free-float window — one legal
accommodation that no channel atom records. -/
private theorem ffUnseat : ffState.apply (Move.pileStack (H .ace)) = some ffMid := by
  rw [apply_pileStack_iff]
  refine ⟨?_, Sum.inl Anchor.p2,
    (Board.bottomOf_eq ffBoard (H .ace) (Sum.inl Anchor.p2)).mpr
      (ffBoard_topOf_inl Anchor.p2), rfl, rfl⟩
  show ffState.board.topOf (Sum.inr (H .ace)) = none
  rfl

private theorem ffMid_wf : ffMid.WF := apply_wf ffState_wf _ _ ffUnseat

/-- The mid state's heights: hearts at 1, everything else pristine. -/
private theorem ffMid_heights (s : Suit) :
    ffMid.heights s = if s = Suit.heart then 1 else 0 := by
  show (if s = (H .ace).suit then ffState.heights s + 1 else ffState.heights s) =
    (if s = Suit.heart then 1 else 0)
  by_cases hs : s = Suit.heart
  · have hc : (H .ace).suit = Suit.heart := rfl
    rw [hs, hc, if_pos rfl, if_pos rfl]
    rfl
  · rw [ite_eq_right (fun hh => hs (hh.trans (rfl : (H .ace).suit = Suit.heart))),
      ite_eq_right hs]
    rfl

/-- Only the two twin hosts remain seated after the promotion. -/
private theorem ffMid_seated (c : Card) (h : (ffMid.board.bottomOf c).isSome = true) :
    c = H .seven ∨ c = D .seven := by
  obtain ⟨b, hb⟩ : ∃ b, ffMid.board.bottomOf c = some b := by
    cases hbot : ffMid.board.bottomOf c with
    | none => rw [hbot] at h; simp at h
    | some b => exact ⟨b, rfl⟩
  have htb : (ffState.board.detach (Sum.inl Anchor.p2)).topOf b = some c :=
    (Board.bottomOf_eq _ _ _).mp hb
  cases b with
  | inl a =>
      by_cases hap2 : a = Anchor.p2
      · rw [hap2, Board.detach_topOf] at htb
        exact absurd htb (by simp)
      · rw [Board.detach_topOf_ne _ _ _ (fun hh => hap2 (Sum.inl.inj hh))] at htb
        have htb2 : ffBoard.topOf (Sum.inl a) = some c := htb
        rw [ffBoard_topOf_inl] at htb2
        cases a with
        | p0 => exact Or.inl (Option.some.inj htb2).symm
        | p1 => exact Or.inr (Option.some.inj htb2).symm
        | p2 => exact absurd rfl hap2
        | p3 => rw [show ffHead Anchor.p3 = none from rfl] at htb2; simp at htb2
        | p4 => rw [show ffHead Anchor.p4 = none from rfl] at htb2; simp at htb2
        | p5 => rw [show ffHead Anchor.p5 = none from rfl] at htb2; simp at htb2
        | p6 => rw [show ffHead Anchor.p6 = none from rfl] at htb2; simp at htb2
  | inr d =>
      rw [Board.detach_topOf_ne _ _ _ sumInr_ne_sumInl] at htb
      have htb2 : ffBoard.topOf (Sum.inr d) = some c := htb
      rw [ffBoard_topOf_inr] at htb2
      exact absurd htb2 (by simp)

private theorem ffMid_bottomOf_six : ffMid.board.bottomOf (S .six) = none := by
  refine (Board.bottomOf_eq_none _ (S .six)).mpr (fun b hb => ?_)
  have his : (ffMid.board.bottomOf (S .six)).isSome = true := by
    rw [(Board.bottomOf_eq _ (S .six) b).mpr hb]
    rfl
  rcases ffMid_seated (S .six) his with e | e
  · exact absurd e (by decide)
  · exact absurd e (by decide)

private theorem ffMid_pos : ffMid.reachablePos (S .six) = some 0 := by
  rw [State.reachablePos_step1 ffMid_wf rfl (S .six)]
  rfl

/-- The window commit: X lands on the twin receiver `d` (one of the
two hosts) at the promoted state.  Parameterized over the host so the
heart and diamond instances share the machinery. -/
private def ffWin (d : Card) : State :=
  (ffMid.applyDrawTo (S .six) (Sum.inr d)).getD ffMid

private theorem ffMid_canPlace (d : Card) (hfit : canSitOn (S .six) d = true)
    (hvis : ffMid.isVis d = true)
    (htopn : ffMid.board.topOf (Sum.inr d) = none) :
    ffMid.canPlace (S .six) (Sum.inr d) = true :=
  canPlace_inr_iff.mpr ⟨htopn, hvis, hfit⟩

private theorem ffWin_apply (d : Card) (hfit : canSitOn (S .six) d = true)
    (hvis : ffMid.isVis d = true)
    (htopn : ffMid.board.topOf (Sum.inr d) = none) :
    ffMid.applyDrawTo (S .six) (Sum.inr d) = some (ffWin d) := by
  have hne : ffMid.board.attach (Sum.inr d) (S .six) ≠ none :=
    (Board.attach_eq_some_iff _ _ _).mpr ⟨htopn, ffMid_bottomOf_six⟩
  cases hatt : ffMid.board.attach (Sum.inr d) (S .six) with
  | none => exact absurd hatt hne
  | some bd =>
      have hto : ffMid.applyDrawTo (S .six) (Sum.inr d) = some
          { ffMid with board := bd, stock := (ffMid.stock.drawTo 0).removeAt 0 } :=
        applyDrawTo_iff.mpr ⟨0, bd, ffMid_pos, hatt, rfl⟩
      cases h : ffMid.applyDrawTo (S .six) (Sum.inr d) with
      | none =>
          have h2 := hto
          rw [h] at h2
          simp at h2
      | some s' =>
          have hw : ffWin d = s' := by
            show (ffMid.applyDrawTo (S .six) (Sum.inr d)).getD ffMid = s'
            rw [h]
            rfl
          rw [hw]

private theorem ffWin_heights (d : Card) (hfit : canSitOn (S .six) d = true)
    (hvis : ffMid.isVis d = true) (htopn : ffMid.board.topOf (Sum.inr d) = none)
    (s : Suit) : (ffWin d).heights s = if s = Suit.heart then 1 else 0 := by
  obtain ⟨i, bd, hpos, hatt, hs⟩ := applyDrawTo_eq (ffWin_apply d hfit hvis htopn)
  rw [hs]
  exact ffMid_heights s

private theorem ffWin_topOf (d : Card) (hfit : canSitOn (S .six) d = true)
    (hvis : ffMid.isVis d = true) (htopn : ffMid.board.topOf (Sum.inr d) = none)
    (b : Base) : (ffWin d).board.topOf b =
    (if b = Sum.inr d then some (S .six) else ffMid.board.topOf b) := by
  obtain ⟨i, bd, hpos, hatt, hs⟩ := applyDrawTo_eq (ffWin_apply d hfit hvis htopn)
  rw [hs]
  by_cases hbeq : b = Sum.inr d
  · rw [hbeq, if_pos rfl]
    exact Board.attach_topOf ffMid.board _ _ hatt
  · rw [if_neg hbeq]
    exact Board.attach_topOf_ne ffMid.board _ _ hatt hbeq

/-- Only the landed card and the two twin hosts are seated at a window
successor. -/
private theorem ffWin_seated (d : Card) (hfit : canSitOn (S .six) d = true)
    (hvis : ffMid.isVis d = true) (htopn : ffMid.board.topOf (Sum.inr d) = none)
    (c : Card) (h : ((ffWin d).board.bottomOf c).isSome = true) :
    c = S .six ∨ c = H .seven ∨ c = D .seven := by
  obtain ⟨b, hb⟩ : ∃ b, (ffWin d).board.bottomOf c = some b := by
    cases hbot : (ffWin d).board.bottomOf c with
    | none => rw [hbot] at h; simp at h
    | some b => exact ⟨b, rfl⟩
  have htb : (ffWin d).board.topOf b = some c := (Board.bottomOf_eq _ _ _).mp hb
  rw [ffWin_topOf d hfit hvis htopn] at htb
  by_cases hbeq : b = Sum.inr d
  · rw [hbeq, if_pos rfl] at htb
    exact Or.inl (Option.some.inj htb).symm
  · rw [if_neg hbeq] at htb
    have his : (ffMid.board.bottomOf c).isSome = true := by
      rw [(Board.bottomOf_eq ffMid.board c b).mpr htb]
      rfl
    rcases ffMid_seated c his with e | e
    · exact Or.inr (Or.inl e)
    · exact Or.inr (Or.inr e)

/-- The landed card sits exactly on the window commit's base. -/
private theorem ffWin_bottomOf_six (d : Card) (hfit : canSitOn (S .six) d = true)
    (hvis : ffMid.isVis d = true) (htopn : ffMid.board.topOf (Sum.inr d) = none) :
    (ffWin d).board.bottomOf (S .six) = some (Sum.inr d) := by
  obtain ⟨i, bd, hpos, hatt, hs⟩ := applyDrawTo_eq (ffWin_apply d hfit hvis htopn)
  rw [hs]
  exact (Board.bottomOf_eq bd (S .six) (Sum.inr d)).mpr
    (Board.attach_topOf ffMid.board _ _ hatt)

/-! ### The window successors are accommodation-dead -/

private theorem ffWin_dead_pileStack (d : Card) (hfit : canSitOn (S .six) d = true)
    (hvis : ffMid.isVis d = true) (htopn : ffMid.board.topOf (Sum.inr d) = none)
    (c : Card) (t : State)
    (h : (ffWin d).apply (Move.pileStack c) = some t) : False := by
  rw [apply_pileStack_iff] at h
  obtain ⟨htopfree, b, hb, hrk, hshape⟩ := h
  have his : ((ffWin d).board.bottomOf c).isSome = true := by rw [hb]; rfl
  rcases ffWin_seated d hfit hvis htopn c his with e | e | e
  · rw [e] at hrk
    have h5 : (S .six).rank.toIdx = 5 := rfl
    have hs6 : (S .six).suit ≠ Suit.heart := by decide
    rw [ffWin_heights d hfit hvis htopn (S .six).suit, if_neg hs6] at hrk
    omega
  · rw [e] at hrk
    have h6 : (H .seven).rank.toIdx = 6 := rfl
    have hs7 : (H .seven).suit = Suit.heart := rfl
    rw [ffWin_heights d hfit hvis htopn (H .seven).suit, if_pos hs7] at hrk
    omega
  · rw [e] at hrk
    have h6 : (D .seven).rank.toIdx = 6 := rfl
    have hsd : (D .seven).suit ≠ Suit.heart := by decide
    rw [ffWin_heights d hfit hvis htopn (D .seven).suit, if_neg hsd] at hrk
    omega

private theorem ffWin_dead_stackPile (d : Card) (hfit : canSitOn (S .six) d = true)
    (hvis : ffMid.isVis d = true) (htopn : ffMid.board.topOf (Sum.inr d) = none)
    (c : Card) (b : Base) (t : State)
    (h : (ffWin d).apply (Move.stackPile c b) = some t) : False := by
  rw [apply_stackPile_iff] at h
  obtain ⟨hg, hcp, bd, hatt, hshape⟩ := h
  by_cases hsh : c.suit = Suit.heart
  · -- the heart height is 1, so only the heart ACE worries back — and
    -- its worry-back has no fitting base among the seated cards
    rw [hsh, ffWin_heights d hfit hvis htopn Suit.heart, if_pos rfl] at hg
    have hr0 : c.rank.toIdx = 0 := by omega
    cases b with
    | inl a =>
        obtain ⟨htopking, hking⟩ := canPlace_inl_iff.mp hcp
        rw [hking] at hr0
        exact absurd hr0 (by decide)
    | inr d' =>
        obtain ⟨htopvis, hvis', hfit'⟩ := canPlace_inr_iff.mp hcp
        have his : ((ffWin d).board.bottomOf d').isSome = true := hvis'
        obtain ⟨hfit1, -⟩ := (canSitOn_eq c d').mp hfit'
        rw [hr0] at hfit1
        rcases ffWin_seated d hfit hvis htopn d' his with e | e | e
        · rw [e] at hfit1; exact absurd hfit1 (by decide)
        · rw [e] at hfit1; exact absurd hfit1 (by decide)
        · rw [e] at hfit1; exact absurd hfit1 (by decide)
  · rw [ffWin_heights d hfit hvis htopn c.suit, if_neg hsh] at hg
    omega

private theorem ffWin_dead (d : Card) (hfit : canSitOn (S .six) d = true)
    (hvis : ffMid.isVis d = true) (htopn : ffMid.board.topOf (Sum.inr d) = none)
    (m : Move) (hm : m.isAccommodation = true) (t : State)
    (hap : (ffWin d).apply m = some t) : False := by
  cases m with
  | pileStack c => exact ffWin_dead_pileStack d hfit hvis htopn c t hap
  | stackPile c b => exact ffWin_dead_stackPile d hfit hvis htopn c b t hap
  | draw => simp [Move.isAccommodation] at hm
  | reveal a => simp [Move.isAccommodation] at hm
  | deckPile c b => simp [Move.isAccommodation] at hm
  | deckStack c => simp [Move.isAccommodation] at hm
  | pilePile c b => simp [Move.isAccommodation] at hm

/-- **Every window successor is its own accommodation closure** — in
particular the route can never walk back to a root commit. -/
private theorem ffWin_stuck (d : Card) (hfit : canSitOn (S .six) d = true)
    (hvis : ffMid.isVis d = true) (htopn : ffMid.board.topOf (Sum.inr d) = none)
    (t : State) (hacc : accommodates (ffWin d) t) : t = ffWin d := by
  obtain ⟨play, hrun, hall⟩ := hacc
  induction play generalizing t with
  | nil => exact (Option.some.inj hrun).symm
  | cons m ms ih =>
      have hm : m.isAccommodation = true := hall m (by simp)
      have hrun' : (match (ffWin d).apply m with
        | some s'' => s''.run ms | none => none) = some t := hrun
      cases hap : (ffWin d).apply m with
      | none => rw [hap] at hrun'; exact absurd hrun' (by simp)
      | some t₁ =>
          rw [hap] at hrun'
          exact (ffWin_dead d hfit hvis htopn m hm t₁ hap).elim

/-! ### The window commit instances: the two twin hosts -/

private theorem ffHeartVis : ffMid.isVis (H .seven) = true := by
  show ((ffBoard.detach (Sum.inl Anchor.p2)).bottomOf (H .seven)).isSome = true
  rw [bottomOf_detach_ne (ffBoard_topOf_inl Anchor.p2) (by decide)]
  show (ffBoard.bottomOf (H .seven)).isSome = true
  rw [(Board.bottomOf_eq ffBoard (H .seven) (Sum.inl Anchor.p0)).mpr
    (ffBoard_topOf_inl Anchor.p0)]
  rfl

private theorem ffDiamondVis : ffMid.isVis (D .seven) = true := by
  show ((ffBoard.detach (Sum.inl Anchor.p2)).bottomOf (D .seven)).isSome = true
  rw [bottomOf_detach_ne (ffBoard_topOf_inl Anchor.p2) (by decide)]
  show (ffBoard.bottomOf (D .seven)).isSome = true
  rw [(Board.bottomOf_eq ffBoard (D .seven) (Sum.inl Anchor.p1)).mpr
    (ffBoard_topOf_inl Anchor.p1)]
  rfl

private theorem ffMid_topOf_heart :
    ffMid.board.topOf (Sum.inr (H .seven)) = none := by
  show (ffState.board.detach (Sum.inl Anchor.p2)).topOf (Sum.inr (H .seven)) = none
  rw [Board.detach_topOf_ne _ _ _ sumInr_ne_sumInl]
  rfl

private theorem ffMid_topOf_diamond :
    ffMid.board.topOf (Sum.inr (D .seven)) = none := by
  show (ffState.board.detach (Sum.inl Anchor.p2)).topOf (Sum.inr (D .seven)) = none
  rw [Board.detach_topOf_ne _ _ _ sumInr_ne_sumInl]
  rfl

/-- The window route's commitment data, heart side. -/
private theorem ffWinHeart_apply :
    ffMid.applyDrawTo (S .six) (Sum.inr (H .seven)) = some (ffWin (H .seven)) :=
  ffWin_apply (H .seven) ffFitHeart ffHeartVis ffMid_topOf_heart

/-- The window route's commitment data, diamond side. -/
private theorem ffWinDiamond_apply :
    ffMid.applyDrawTo (S .six) (Sum.inr (D .seven)) = some (ffWin (D .seven)) :=
  ffWin_apply (D .seven) ffFitDiamond ffDiamondVis ffMid_topOf_diamond

/-- The window-successor macro steps (the promotion is the window). -/
theorem ffWinHeart_step : macroStep ffState (MacroMove.drawCommit (S .six))
    (ffWin (H .seven)) :=
  ⟨ffMid, ⟨[Move.pileStack (H .ace)], by rw [run_singleton]; exact ffUnseat,
    fun m hm => by
      rcases List.mem_cons.mp hm with rfl | hm
      · rfl
      · exact absurd hm (by simp)⟩,
    ⟨Sum.inr (H .seven), Or.inl
      ⟨ffMid_canPlace (H .seven) ffFitHeart ffHeartVis ffMid_topOf_heart,
        ffWinHeart_apply⟩⟩⟩

theorem ffWinDiamond_step : macroStep ffState (MacroMove.drawCommit (S .six))
    (ffWin (D .seven)) :=
  ⟨ffMid, ⟨[Move.pileStack (H .ace)], by rw [run_singleton]; exact ffUnseat,
    fun m hm => by
      rcases List.mem_cons.mp hm with rfl | hm
      · rfl
      · exact absurd hm (by simp)⟩,
    ⟨Sum.inr (D .seven), Or.inl
      ⟨ffMid_canPlace (D .seven) ffFitDiamond ffDiamondVis ffMid_topOf_diamond,
        ffWinDiamond_apply⟩⟩⟩

/-- The two window successors differ (the landed card sits on
different twin hosts). -/
private theorem ffWinHeart_ne_ffWinDiamond :
    ffWin (H .seven) ≠ ffWin (D .seven) := by
  intro heq
  have h1 := ffWin_bottomOf_six (H .seven) ffFitHeart ffHeartVis ffMid_topOf_heart
  have h2 := ffWin_bottomOf_six (D .seven) ffFitDiamond ffDiamondVis ffMid_topOf_diamond
  rw [← heq] at h2
  exact absurd (Option.some.inj (h1.symm.trans h2)) (by decide)

/-! ### Every channel of the current list fails to label the route -/

/-- The route successor is not a root tableau commit: every root
commit keeps the dealt heart height 0 against the route's 1 (the
window CONTENT the direct signature cannot see). -/
private theorem ffSucc_not_direct :
    ¬ SuccThrough ffState (S .six) Label.direct (ffWin (H .seven)) := by
  rintro ⟨u, α, hrun, -, harm, hsig⟩
  have hα : α = [] := hsig
  rw [hα] at hrun
  rw [(run_nil_elim hrun).symm] at harm
  obtain ⟨b, hcp, hto⟩ := harm
  obtain ⟨i, bd, hpos, hatt, hs⟩ := applyDrawTo_eq hto
  have hkeep : (ffWin (H .seven)).heights Suit.heart = ffState.heights Suit.heart := by
    rw [hs]
  have hroute : (ffWin (H .seven)).heights Suit.heart = 1 := by
    rw [ffWin_heights (H .seven) ffFitHeart ffHeartVis ffMid_topOf_heart Suit.heart]
    exact if_pos rfl
  rw [hroute, show ffState.heights Suit.heart = 0 from rfl] at hkeep
  exact absurd hkeep (by decide)

private theorem ffSucc_unlabeled (r : Label (S .six)) :
    ¬ (LabelLive ffState (S .six) r ∧
       SuccThrough ffState (S .six) r (ffWin (H .seven))) := by
  rintro ⟨hlive, hthru⟩
  cases r with
  | direct => exact ffSucc_not_direct hthru
  | dig =>
      obtain ⟨Y, hd⟩ := hlive
      have hcov : (Option.none : Option Card) = some (S .six).flipSuit :=
        (ffTopOf_inr_none Y).symm.trans hd.hcover
      exact absurd hcov (by simp)
  | borrow p =>
      obtain ⟨hp, hbl⟩ := hlive
      have htop := hbl.htop
      have h0 : ffState.heights p.suit = 0 := rfl
      rw [h0] at htop
      omega
  | hole =>
      obtain ⟨a, ha⟩ := hlive
      exact absurd ha.hK ffNonKing
  | toStack =>
      obtain ⟨r', s', hacc, hfire⟩ := hlive
      exact ffFrozenToStack r' s' hacc hfire

/-- **The as-stated `succ_labeled` restricted to non-king commitments
is REFUTED**: at a WF all-heights-zero state with the `direct`
channel LIVE, the free-float window `[pileStack ♥A]` delivers a macro
successor of the non-king `Draw(♠6)` commitment that no channel of
the current five-element list can name.  The failure is NOT the
anchored-head unseat — it needs no king and no vacated anchor; it is
the window playing content outside the channel atoms' signatures. -/
theorem wk_nonking_succLabeled_false :
    ¬ (∀ (st : State) (X : Card) (s : State), st.WF → X.rank ≠ Rank.king →
        macroStep st (MacroMove.drawCommit X) s →
        ∃ r : Label X, LabelLive st X r ∧ SuccThrough st X r s) := by
  intro h
  obtain ⟨r, hlive, hthru⟩ :=
    h ffState (S .six) (ffWin (H .seven)) ffState_wf ffNonKing ffWinHeart_step
  exact ffSucc_unlabeled r ⟨hlive, hthru⟩

/-! ### The as-stated count universal restricted to non-kings -/

/-- The root commit on the heart twin (heights pristine). -/
private def ffRoot1 : State :=
  (ffState.applyDrawTo (S .six) (Sum.inr (H .seven))).getD ffState

private theorem ffRoot1_apply :
    ffState.applyDrawTo (S .six) (Sum.inr (H .seven)) = some ffRoot1 := by
  have hne : ffBoard.attach (Sum.inr (H .seven)) (S .six) ≠ none :=
    (Board.attach_eq_some_iff _ _ _).mpr
      ⟨ffTopOf_inr_none (H .seven), ffSpades_unseated (S .six) rfl⟩
  cases hatt : ffBoard.attach (Sum.inr (H .seven)) (S .six) with
  | none => exact absurd hatt hne
  | some bd =>
      have hto : ffState.applyDrawTo (S .six) (Sum.inr (H .seven)) = some
          { ffState with board := bd, stock := (ffState.stock.drawTo 0).removeAt 0 } :=
        applyDrawTo_iff.mpr ⟨0, bd, ffState_pos, hatt, rfl⟩
      cases h : ffState.applyDrawTo (S .six) (Sum.inr (H .seven)) with
      | none =>
          have h2 := hto
          rw [h] at h2
          simp at h2
      | some s' =>
          have hw : ffRoot1 = s' := by
            show (ffState.applyDrawTo (S .six) (Sum.inr (H .seven))).getD ffState = s'
            rw [h]
            rfl
          rw [hw]

theorem ffRoot1_step : macroStep ffState (MacroMove.drawCommit (S .six)) ffRoot1 :=
  ⟨ffState, ⟨[], rfl, fun _ hm => by simp at hm⟩,
    ⟨Sum.inr (H .seven), Or.inl
      ⟨canPlace_inr_iff.mpr
        ⟨ffTopOf_inr_none (H .seven),
          by
            show (ffBoard.bottomOf (H .seven)).isSome = true
            rw [(Board.bottomOf_eq ffBoard (H .seven) (Sum.inl Anchor.p0)).mpr
              (ffBoard_topOf_inl Anchor.p0)]
            rfl,
          ffFitHeart⟩,
        ffRoot1_apply⟩⟩⟩

/-- The root commit keeps the dealt heart height. -/
private theorem ffRoot1_heights0 (s : Suit) : ffRoot1.heights s = 0 := by
  obtain ⟨i, bd, hpos, hatt, hs⟩ := applyDrawTo_eq ffRoot1_apply
  rw [hs]
  rfl

/-- The root commit and the window successors differ: the heart
height. -/
private theorem ffRoot1_ne_ffWin (d : Card) (hfit : canSitOn (S .six) d = true)
    (hvis : ffMid.isVis d = true) (htopn : ffMid.board.topOf (Sum.inr d) = none) :
    ffRoot1 ≠ ffWin d := by
  intro heq
  have h1 : ffRoot1.heights Suit.heart = 0 := ffRoot1_heights0 Suit.heart
  have h2 : (ffWin d).heights Suit.heart = 1 := by
    rw [ffWin_heights d hfit hvis htopn Suit.heart]
    exact if_pos rfl
  rw [heq] at h1
  exact absurd (h1.symm.trans h2) (by decide)

/-- **The as-stated `c2_two_option` count universal restricted to
non-kings is REFUTED**: three pairwise closure-separated macro
successors of one non-king commitment at a WF state — the root commit
on the heart twin, and the two window-commit routes. -/
theorem wk_nonking_c2_false :
    ¬ (∀ (st : State) (X : Card) (s₁ s₂ s₃ : State), st.WF → X.rank ≠ Rank.king →
        macroStep st (MacroMove.drawCommit X) s₁ →
        macroStep st (MacroMove.drawCommit X) s₂ →
        macroStep st (MacroMove.drawCommit X) s₃ →
        closureEq s₁ s₂ ∨ closureEq s₁ s₃ ∨ closureEq s₂ s₃) := by
  intro h
  rcases h ffState (S .six) ffRoot1 (ffWin (H .seven)) (ffWin (D .seven))
      ffState_wf ffNonKing ffRoot1_step ffWinHeart_step ffWinDiamond_step with
    q | q | q
  · -- closureEq ffRoot1 (ffWin ♥7): the window successor's closure is
    -- stuck at itself, but the heights differ
    exact ffRoot1_ne_ffWin (H .seven) ffFitHeart ffHeartVis ffMid_topOf_heart
      (ffWin_stuck (H .seven) ffFitHeart ffHeartVis ffMid_topOf_heart ffRoot1 q.2)
  · exact ffRoot1_ne_ffWin (D .seven) ffFitDiamond ffDiamondVis ffMid_topOf_diamond
      (ffWin_stuck (D .seven) ffFitDiamond ffDiamondVis ffMid_topOf_diamond ffRoot1 q.2)
  · exact ffWinHeart_ne_ffWinDiamond
      (ffWin_stuck (D .seven) ffFitDiamond ffDiamondVis ffMid_topOf_diamond
        (ffWin (H .seven)) q.2)

end FF

#print axioms NK.wk_nonking_twinCollapse_rung_false
#print axioms NK.wk_nonking_samePin_direct_false
#print axioms NK.wk_nonking_p2Direct_false
#print axioms NK.nkSuccessorsExhaustTwo
#print axioms NK.nkTwoOptionHoldsHere
#print axioms FF.wk_nonking_succLabeled_false
#print axioms FF.wk_nonking_c2_false
