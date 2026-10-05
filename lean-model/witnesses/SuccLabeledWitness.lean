import Klondike.C2Streamlined

/-!
# The `succ_labeled` witness — the channel-list gap, the anchored-head unseat

Wave-12/17's P0, `succ_labeled`, as the library spelled it:

  *every macro successor of the `Draw(X)` commitment is labeled by some
  channel (`direct`, `dig`, `borrow p`, `hole`, `toStack`) live at the
  commitment's root state.*

Wave-18 left it analytic-only, naming the gap (C2Streamlined §11): the
**anchored-head unseat route** — "a pile head seated on an anchor
leaves by its rank-dig and the king lands on the vacated anchor, which
is `hole`-shaped at the end state but dead at the root (no free anchor
there), so no `LabelLive`-at-`st` channel names it."  This file is the
prover-confirmed countermodel witness (the wave-19 decision datum),
extending the `C2KingAnchorWitness` family — same pristine deal shape
and spade-blocked stock, same decide-anchored discipline:

* the state `uState` is WF (standard deal, zero heights/depths, draw
  step 1) with ALL SEVEN ANCHORS OCCUPIED — each pile's own dealt head
  is seated on its pile's anchor (legal by `board_edges`' deal
  adjacency clause `(uDeal.piles a).head? = some c`), every head a
  non-spade (♥A, ♦2, ♣5, ♣6, ♣7, ♣8, ♣9), and the full spade-blocked
  stock carries ♠K at position 0;
* the accommodation `pileStack ♥A` — pile 0's anchored head is an ace
  at foundation height 0, its "rank-dig" — UNSEATS THROUGH THE ANCHOR'S
  HEAD SEAT, vacating anchor 0, and the `Draw(♠K)` commitment then
  lands the king on the vacated anchor: `uStep` is a genuine
  `macroStep` successor;
* at the root, EVERY channel of the current list is dead (`uLabelLive_false`):
  `direct`/`dig`/`borrow p` die on `receivers_king_nil` (a king has no
  receivers), `hole` dies because no anchor is free, and `toStack` dies
  by the **spade freeze** (`freeze_run`): no spade is visible and all
  heights are 0, and `pileStack`/`stackPile` can neither seat a spade
  (its height would have to already be past its rank) nor raise the
  spade height (only a visible ♠A could start the climb), so along
  every accommodation play the spade height stays 0 and the stack arm
  (`♠K.rank.toIdx = 12 = heights spade`) can never fire;
* hence `wk_succ_labeled_as_stated_false` — the as-stated universal
  (negated in the exact wave-12/17 spelling) is permanently refuted,
  and the hlab premises of the conditional `c2_two_option` must carry
  the route until the channel list decision below lands.

## The missing channel, characterized (for the orchestrator's Label decision)

The unseat route spends the **anchor's seat itself**: the departure of
the dealt head occupying the landing anchor (here the one reversible
`pileStack` of an ace seated at its suit's height — the head's
"rank-dig" to the foundation), i.e. a vacancy that is *created by* the
accommodation rather than presented by the root.  No current Label
covers it: `direct`/`dig`/`borrow p` all pin tableau landings on
receivers (a king has none, and the vacated anchor is not a card), the
`hole` label's liveness is read at the root — `HoleLive` demands
`st.board.topOf (Sum.inl a) = none` already at `st` — so it is dead
exactly when every anchor is occupied, and `toStack` pins the residence
flip (the stack arm's successor, a different state).  One-line
candidate channel: **`anchorHead a` — "the commitment's landing unseated
a dealt anchor head" — live at `st` iff `∃ c, st.board.topOf (Sum.inl a)
= some c ∧ c.rank.toIdx = st.heights c.suit ∧ st.board.topOf (Sum.inr c)
= none` (a removable anchored head), with pinning set `[anchorHead a]`
(the vacated seat), a sixth poset atom alongside `hole`** — the
alternatives (re-scoping `hole`'s liveness to the accommodated state,
or re-stating `succ_labeled` per-route) are strictly wider edits.  The
decision itself belongs to the sibling C2 session which owns
`C2Streamlined`'s channel list; this file only fixes the datum.
-/

open Klondike.C2

namespace SuccLabeled

/-- Spades. -/
private def S (r : Rank) : Card := ⟨Suit.spade, r⟩
/-- Hearts. -/
private def H (r : Rank) : Card := ⟨Suit.heart, r⟩
/-- Diamonds. -/
private def D (r : Rank) : Card := ⟨Suit.diamond, r⟩
/-- Clubs. -/
private def C (r : Rank) : Card := ⟨Suit.club, r⟩

/-! ## The anchored heads -/

/-- The dealt head seated on anchor `a` — pile `a`'s first dealt card,
all non-spade (the freeze premise), all distinct. -/
private def uHead : Anchor → Card
  | .p0 => H .ace
  | .p1 => D .two
  | .p2 => C .five
  | .p3 => C .six
  | .p4 => C .seven
  | .p5 => C .eight
  | .p6 => C .nine

private theorem uHead_ne (a a' : Anchor) (h : uHead a = uHead a') : a = a' := by
  cases a <;> cases a' <;> first
    | rfl
    | exact absurd h (by decide)

private theorem uHead_notSpade (a : Anchor) : (uHead a).suit ≠ Suit.spade := by
  cases a <;> decide

/-! ## The board: every anchor occupied by its dealt head -/

/-- The board function: the head on each anchor's base, nothing on any
card base. -/
private def uTopOf : Base → Option Card := fun b =>
  match b with
  | Sum.inl a => some (uHead a)
  | Sum.inr _ => none

private theorem uTopOf_inl (a : Anchor) : uTopOf (Sum.inl a) = some (uHead a) := rfl
private theorem uTopOf_inr (d : Card) : uTopOf (Sum.inr d) = none := rfl

private theorem uBoard_inj : ∀ (b₁ b₂ : Base) (c : Card),
    uTopOf b₁ = some c → uTopOf b₂ = some c → b₁ = b₂ := by
  intro b₁ b₂ c h₁ h₂
  cases b₁ with
  | inl a₁ =>
      cases b₂ with
      | inl a₂ =>
          rw [uTopOf_inl] at h₁
          rw [uTopOf_inl] at h₂
          have h₃ : uHead a₁ = uHead a₂ :=
            (Option.some.inj h₁).trans (Option.some.inj h₂).symm
          exact congrArg Sum.inl (uHead_ne a₁ a₂ h₃)
      | inr d₂ =>
          rw [uTopOf_inr] at h₂
          exact absurd h₂ (by simp)
  | inr d₁ =>
      rw [uTopOf_inr] at h₁
      exact absurd h₁ (by simp)

/-- The witness board — seven anchor-head edges, one per pile. -/
private def uBoard : Board := ⟨uTopOf, uBoard_inj⟩

private theorem uBoard_topOf_inl (a : Anchor) :
    uBoard.topOf (Sum.inl a) = some (uHead a) := rfl

private theorem uBoard_topOf_inr (d : Card) : uBoard.topOf (Sum.inr d) = none := rfl

/-- No spade is seated anywhere (only the seven non-spade heads are). -/
private theorem uSpades_unseated (c : Card) (hcs : c.suit = Suit.spade) :
    uBoard.bottomOf c = none := by
  refine (Board.bottomOf_eq_none _ _).mpr (fun b hb => ?_)
  cases b with
  | inl a =>
      have hba : uBoard.topOf (Sum.inl a) = some c := hb
      rw [uBoard_topOf_inl] at hba
      have hEq : uHead a = c := Option.some.inj hba
      have hs : (uHead a).suit = Suit.spade := by rw [hEq]; exact hcs
      exact uHead_notSpade a hs
  | inr d =>
      have hba : uBoard.topOf (Sum.inr d) = some c := hb
      rw [uBoard_topOf_inr] at hba
      exact absurd hba (by simp)

/-- Every anchor is occupied — the `hole` channel is dead at the root. -/
private theorem uOccupied (a : Anchor) (hfree : uBoard.topOf (Sum.inl a) = none) :
    False := by
  have hocc : uBoard.topOf (Sum.inl a) = some (uHead a) := uBoard_topOf_inl a
  rw [hocc] at hfree
  simp at hfree

/-! ## The state -/

/-- The stock slice — ♠K at position 0, all suits' high cards, the
state's cycle cards are the very same list. -/
private def uStockList : List Card :=
  [S .king, H .jack, H .queen, H .king] ++
  [D .ace, D .three, D .four, D .five, D .six, D .seven, D .eight,
   D .nine, D .ten, D .jack, D .queen, D .king] ++
  [C .ace, C .two, C .three, C .four, C .ten, C .jack, C .queen, C .king]

/-- The witness deal: 28 pile cards with the seven anchored heads first
in their piles, 24 stock cards, all 52 distinct. -/
private def uDeal : Deal where
  piles := fun a =>
    match a with
    | .p0 => [H .ace]
    | .p1 => [D .two, S .ace]
    | .p2 => [C .five, S .two, S .three]
    | .p3 => [C .six, S .four, S .five, S .six]
    | .p4 => [C .seven, S .seven, S .eight, S .nine, S .ten]
    | .p5 => [C .eight, S .jack, S .queen, H .two, H .three, H .four]
    | .p6 => [C .nine, H .five, H .six, H .seven, H .eight, H .nine, H .ten]
  stock := uStockList

/-- The witness state: the anchored heads on every anchor, pristine
heights/depths, draw step 1, ♠K drawn first. -/
private def uState : State where
  deal := uDeal
  board := uBoard
  heights := fun _ => 0
  depths := fun _ => 0
  stock := ⟨uStockList, 0⟩
  drawStep := 1

/-! ## The state is WF -/

private theorem uDeal_wf : uDeal.WF := by
  refine ⟨fun a => ?_, by decide, ?_⟩
  · cases a <;> decide
  · intro i j hi hj heq
    have hflat : (Anchor.all.flatMap uDeal.piles).length = 28 := by decide
    have hstock : uDeal.stock.length = 24 := by decide
    rw [List.length_append, hflat, hstock] at hi hj
    have hall : ∀ i ∈ List.range 52, ∀ j ∈ List.range 52,
        (Anchor.all.flatMap uDeal.piles ++ uDeal.stock)[i]? =
          (Anchor.all.flatMap uDeal.piles ++ uDeal.stock)[j]? → i = j := by decide
    exact hall i (List.mem_range.mpr hi) j (List.mem_range.mpr hj) heq

private theorem uState_wf : uState.WF := by
  refine State.WF.intro uDeal_wf ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · -- depths_le
    intro a
    show (0 : Nat) ≤ (uDeal.piles a).length
    cases a <;> decide
  · -- board_edges: the only edges are the seven anchor-head seats,
    -- each legal by the dealt-head clause
    intro b c hb
    have hb' : uBoard.topOf b = some c := hb
    cases b with
    | inl a =>
        rw [uBoard_topOf_inl] at hb'
        have hc : c = uHead a := (Option.some.inj hb').symm
        refine ⟨(Board.bottomOf_eq _ _ _).mpr hb', ?_⟩
        rw [hc]
        show (uHead a).rank = Rank.king ∨ (uDeal.piles a).head? = some (uHead a)
        exact Or.inr (by cases a <;> rfl)
    | inr d =>
        rw [uBoard_topOf_inr] at hb'
        exact absurd hb' (by simp)
  · -- vis_off_cycle: a seated card is a dealt head, never stocked
    intro c hc
    have hc' : (uState.board.bottomOf c).isSome = true := hc
    cases hbot : uState.board.bottomOf c with
    | none => rw [hbot] at hc'; simp at hc'
    | some b =>
        have htb : uBoard.topOf b = some c := (Board.bottomOf_eq _ _ _).mp hbot
        cases b with
        | inl a =>
            rw [uBoard_topOf_inl] at htb
            have hEq : c = uHead a := (Option.some.inj htb).symm
            rw [hEq]
            exact Cycle.posOf_eq_none
              (show uHead a ∉ uStockList by cases a <;> decide)
        | inr d =>
            rw [uBoard_topOf_inr] at htb
            exact absurd htb (by simp)
  · -- found_off_cycle: vacuous at zero heights
    intro c h
    have h0 : uState.heights c.suit = 0 := rfl
    have hc : decide (c.rank.toIdx < uState.heights c.suit) = true := h
    rw [h0] at hc
    simp at hc
  · -- founds_gone: vacuous at zero heights
    intro c hc
    have h0 : uState.heights c.suit = 0 := rfl
    rw [h0] at hc
    exact absurd hc (by omega)
  · -- vis_not_hidden: depths 0, the hidden slices are empty
    intro c _ a
    show ¬ (c ∈ (uDeal.piles a).take (0 : Nat))
    rw [List.take_zero]
    simp
  · -- heights_le
    intro _
    exact Nat.zero_le _
  · -- cursor_le
    show uState.stock.cursor ≤ uState.stock.cards.length
    decide
  · -- step_pos
    exact Nat.zero_lt_one
  · -- stock_wf
    refine ⟨fun i j hi hj heq => ?_, fun _ hmem => hmem⟩
    have hall : ∀ i ∈ List.range 24, ∀ j ∈ List.range 24,
        uStockList[i]? = uStockList[j]? → i = j := by decide
    exact hall i (List.mem_range.mpr hi) j (List.mem_range.mpr hj) heq

/-! ## The spade freeze: no accommodation ever raises the spade height

The invariant: spade height 0 and no spade seated.  `pileStack` of a
spade would need a visible ♠A (contradicts the seat half); `stackPile`
of a spade would need its rank-plus-one to be the spade height
(contradicts the 0 half); every other move is not an accommodation.
-/

private theorem uFreeze_step (st : State)
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

/-- The freeze, run level: along any accommodation play from any
invariant state, the spade height stays 0 and no spade gains a seat. -/
private theorem freeze_run (play : List Move) :
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
          obtain ⟨h0₁, hns₁⟩ := uFreeze_step st h0 hns m hm s₁ hap
          exact ih s₁ h0₁ hns₁ t
            (fun m' hm' => hall m' (List.mem_cons_of_mem _ hm')) hrun'

/-- The stack-arm guard extraction: if the safe `Draw(c)` commitment
fired, the card's rank matches its suit's height at that state. -/
private theorem applyDrawStackTo_heights (st : State) (c : Card) (s : State)
    (h : st.applyDrawStackTo c = some s) : c.rank.toIdx = st.heights c.suit := by
  simp only [State.applyDrawStackTo] at h
  cases hp : st.reachablePos c with
  | none => rw [hp] at h; exact absurd h (by simp)
  | some i =>
      rw [hp] at h
      have h' : (if c.rank.toIdx = st.heights c.suit then
          some { st with
            stock := (st.stock.drawTo i).removeAt i,
            heights := fun s => if s = c.suit then st.heights s + 1 else st.heights s }
          else none) = some s := h
      by_cases hrk : c.rank.toIdx = st.heights c.suit
      · rw [ite_eq_left hrk] at h'; exact hrk
      · rw [ite_eq_right hrk] at h'; exact absurd h' (by simp)

/-! ## Every current channel is dead at the root -/

private theorem uKingNoReceivers (p : Card) (h : canSitOn (S .king) p = true) :
    False := receivers_king_nil rfl h

/-- The channel list is empty at `uState`: the king kills the receiver
channels, the occupied anchors kill the hole, the freeze kills the
stack arm. -/
private theorem uLabelLive_false (r : Label (S .king)) :
    ¬ LabelLive uState (S .king) r := by
  intro hlive
  cases r with
  | direct =>
      have hx : ∃ Y, DirectLive uState (S .king) Y := hlive
      obtain ⟨Y, hd⟩ := hx
      exact uKingNoReceivers Y hd.hY
  | dig =>
      have hx : ∃ Y, DigLive uState (S .king) Y := hlive
      obtain ⟨Y, hd⟩ := hx
      exact uKingNoReceivers Y hd.hY
  | borrow p =>
      have hx : ∃ _hp : canSitOn (S .king) p = true, BorrowLive uState (S .king) p :=
        hlive
      obtain ⟨hp, -⟩ := hx
      exact uKingNoReceivers p hp
  | hole =>
      have hx : ∃ a, HoleLive uState (S .king) a := hlive
      obtain ⟨a, ha⟩ := hx
      exact uOccupied a ha.hfree
  | toStack =>
      have hx : ∃ st' s', accommodates uState st' ∧
          st'.applyDrawStackTo (S .king) = some s' := hlive
      obtain ⟨st', s', hacc, hfire⟩ := hx
      obtain ⟨play, hrun, hall⟩ := hacc
      obtain ⟨h0, -⟩ := freeze_run play uState rfl uSpades_unseated st' hall hrun
      have h12 := applyDrawStackTo_heights st' (S .king) s' hfire
      have hsp : (S .king).suit = Suit.spade := rfl
      have hk12 : (S .king).rank.toIdx = 12 := rfl
      rw [hsp] at h12
      omega

/-! ## The unseat route and its (unique) successor -/

/-- The after-unseat state: pile 0's head is gone to the foundation,
anchor 0 is free, the heart height is 1. -/
private def uMid : State :=
  { uState with
    board := uState.board.detach (Sum.inl Anchor.p0),
    heights := fun s => if s = (H .ace).suit then uState.heights s + 1 else uState.heights s }

/-- The anchored head leaves: `pileStack ♥A` fires at the root — the
anchor's head seat is the one the unseat route vacates. -/
private theorem uUnseat : uState.apply (Move.pileStack (H .ace)) = some uMid := by
  rw [apply_pileStack_iff]
  exact ⟨rfl, Sum.inl Anchor.p0, (Board.bottomOf_eq _ _ _).mpr (uBoard_topOf_inl Anchor.p0),
    rfl, rfl⟩

private theorem uMid_wf : uMid.WF := apply_wf uState_wf _ _ uUnseat

private theorem uMid_canPlace :
    uMid.canPlace (S .king) (Sum.inl Anchor.p0) = true := by
  rw [canPlace_inl_iff]
  exact ⟨Board.detach_topOf uState.board (Sum.inl Anchor.p0), rfl⟩

private theorem uMid_bottomOf_king : uMid.board.bottomOf (S .king) = none := by
  have hseat : uState.board.topOf (Sum.inl Anchor.p0) = some (H .ace) :=
    uBoard_topOf_inl Anchor.p0
  have hk : (S .king) ≠ (H .ace) := by decide
  show (uState.board.detach (Sum.inl Anchor.p0)).bottomOf (S .king) = none
  rw [bottomOf_detach_ne hseat hk]
  exact uSpades_unseated (S .king) rfl

private theorem uMid_reach : uMid.reachablePos (S .king) = some 0 := by
  rw [State.reachablePos_step1 uMid_wf rfl (S .king)]
  rfl

/-- The unseat route's successor: the king lands on the vacated anchor. -/
private def uSucc : State :=
  (uMid.applyDrawTo (S .king) (Sum.inl Anchor.p0)).getD uMid

private theorem uSucc_apply :
    uMid.applyDrawTo (S .king) (Sum.inl Anchor.p0) = some uSucc := by
  have hne : uMid.board.attach (Sum.inl Anchor.p0) (S .king) ≠ none :=
    (Board.attach_eq_some_iff _ _ _).mpr
      ⟨Board.detach_topOf uState.board (Sum.inl Anchor.p0), uMid_bottomOf_king⟩
  cases hatt : uMid.board.attach (Sum.inl Anchor.p0) (S .king) with
  | none => exact absurd hatt hne
  | some bd =>
      have hto : uMid.applyDrawTo (S .king) (Sum.inl Anchor.p0) = some
          { uMid with board := bd, stock := (uMid.stock.drawTo 0).removeAt 0 } :=
        applyDrawTo_iff.mpr ⟨0, bd, uMid_reach, hatt, rfl⟩
      cases h : uMid.applyDrawTo (S .king) (Sum.inl Anchor.p0) with
      | none =>
          have := hto
          rw [h] at this
          simp at this
      | some s' =>
          have hw : uSucc = s' := by
            show (uMid.applyDrawTo (S .king) (Sum.inl Anchor.p0)).getD uMid = s'
            rw [h]
            rfl
          rw [hw]

/-- The unseat route IS a macro successor of the commitment. -/
theorem uStep :
    macroStep uState (MacroMove.drawCommit (S .king)) uSucc := by
  refine ⟨uMid, ⟨[Move.pileStack (H .ace)], ?_, ?_⟩,
    ⟨Sum.inl Anchor.p0, Or.inl ⟨uMid_canPlace, uSucc_apply⟩⟩⟩
  · rw [run_singleton]
    exact uUnseat
  · intro m hm
    rcases List.mem_cons.mp hm with rfl | hm
    · rfl
    · exact absurd hm (by simp)

/-! ## The refuted universal -/

/-- **`succ_labeled` as stated (wave-12/17 spelling) is REFUTED**: the
anchored-head unseat route delivers a macro successor of the `Draw(♠K)`
commitment at a WF state while EVERY channel of the current label list
is dead at the root — the successor is labeled by nothing in
`{direct, dig, borrow p, hole, toStack}`. -/
theorem wk_succ_labeled_as_stated_false :
    ¬ (∀ (st : State) (X : Card) (s : State), st.WF →
        macroStep st (MacroMove.drawCommit X) s →
        ∃ r : Label X, LabelLive st X r ∧ SuccThrough st X r s) := by
  intro h
  obtain ⟨r, hlive, _⟩ := h uState (S .king) uSucc uState_wf uStep
  exact uLabelLive_false r hlive

end SuccLabeled

#print axioms SuccLabeled.wk_succ_labeled_as_stated_false
