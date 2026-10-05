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

## The wave-20 addendum (the file's second half)

The question was only half-answered by the pristine `uState`: under
the initialReachable gate the wave-19B row called this universal
RESTORED.  The reachable-corner addendum below revises that: the
route shape occurs at the dealt INITIAL state of an honest deal
(zero-move reachable), so the GATED succ_labeled still fails — and
the same root splits the four gated class universals too
(`wk_succ_labeled_reachable_false` and the four
`wk_*_reachable_false` theorems; the Label-decision input for the
orchestrator is recorded in the addendum's header).
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
heights/depths, draw step 1, ♠K drawn first.  (Public since wave-20:
the reach probe's verdict is stated at it, replacing the replica
spelling.) -/
def uState : State where
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

/-! ## The reversibility objection, settled mechanically (addendum)

The orchestrator's objection: the vacating shuffle is `pileStack ♥A`,
and since only kings re-enter empty anchors while an ace's worry-back
(`stackPile ♥A`) needs a 2-receiver that this board does not provide,
the promotion is irreversible — so under Lemma A/A3's "reversible
window" reading the window must split, the promotion is its OWN commit,
the `Draw(♠K)` root shifts post-♥A, and the successor becomes
`hole`-labeled — collapsing the refutation.  This section settles all
three questions mechanically:

* **Q1**: `uStep_instance` spells the exact commit instance behind
  `uStep` — the window play `[pileStack ♥A]`, the accommodated state
  `uMid`, and the **tableau arm** of `commitApplies`
  (`∃ b, uMid.canPlace (♠K) b = true ∧ uMid.applyDrawTo (♠K) b = some
  uSucc` at `b = Sum.inl p0`) — every guard read at **`uMid`**, the
  post-unseat state — and `uNoRootCommit` shows NO arm of the
  commitment fires at the root `uState` itself (tableau arm: all
  anchors occupied, king without receivers; stack arm: 12 vs the frozen
  spade height 0).  The instance is legal per the definitions exactly as
  written; nothing about it is inferred.
* **Q2**: reversibility is a premise NOWHERE in the `macroStep`
  relation.  `macroStep st k st'' := ∃ st', accommodates st st' ∧
  commitApplies st' k st''` (Macro.lean), `accommodates` is
  `∃ play, st.run play = some st' ∧ ∀ m ∈ play, m.isAccommodation`
  (Theorems.lean:162), and `commitApplies` has no window-content
  premise.  The model's own strongest window gate,
  `playSafeAccomm`/`safeAccommodates` (Theorems.lean:171-180), checks
  only LOCKEDNESS of `pileStack` sources (B4's dead-pile hazard) and is
  consumed only by Kills' closure invariants — never by
  `macroStep`/`commitApplies`.  `uUnseat_safeAccommodates` proves the
  promotion forms a **safe** accommodation window even under that
  strictest gate: the source ♥A sits on anchor p0, not on any hidden
  boundary (`uHead0_unlocked`), so `isLocked ♥A = false`.  And the
  documented A-layer classification is kind-based, not
  context-based (macro_formalization.md §2, Lemma A1: "only `PileStack`
  (unlocked) and `StackPile` are reversible" — matching the engine's
  `reverse_move`, src/state.rs:312-321): an unlocked `pileStack` is a
  shuffle move by KIND, exactly where it fires.
* **Q3**: the witness **survives** — `wk_succ_labeled_as_stated_false`
  is a theorem about the model's `macroStep` as defined, and no
  reversibility premise exists for it to violate.  What the objection
  really identifies is the real finding, now filed: the window relation
  is kind-based while the model's own irreversibility predicate
  `irreversibleAt` (Theorems.lean:138) is context-based, and the two
  disagree at `uState`: `uPromotionPermanent` proves the promotion is
  permanent along the entire accommodation closure (at `uMid` every
  accommodation move is dead — the seat pairs/ranks make every
  `pileStack` and every `stackPile` fail, including the worry-back of
  ♥A, whose only 2-rank receiver ♦2 is the same color — so
  `accommodates uMid s'` forces `s' = uMid`).  The window contains
  commit-shaped content the relation cannot see.  The two repair routes
  for the orchestrator: (a) gate `macroStep`'s windows on
  context-irreversibility (making the promotion its own commit — under
  which reading `uShifted_hole_cover` proves THIS configuration IS
  `hole`-labeled at the shifted root, the five-channel list holding
  there), or (b) keep the kind-based window and add the `anchorHead`
  channel.  Under (a) this file becomes the boundary record of the
  pre-gate semantics; under (b) it stays the standing refutation.
  Either way the witness is never deleted. -/


/-! ### Q1 — the exact instance -/

/-- Q1: behind `uStep` the commitment does NOT fire at the root — both
arms of `commitApplies uState (drawCommit ♠K)` are dead there. -/
private theorem uNoRootCommit :
    ¬ ∃ s, commitApplies uState (MacroMove.drawCommit (S .king)) s := by
  rintro ⟨s, hs⟩
  rcases (commitApplies_draw_cases uState (S .king) s).mp hs with
    ⟨b, hcp, -⟩ | hst
  · cases b with
    | inl a =>
        obtain ⟨hfree, -⟩ := canPlace_inl_iff.mp hcp
        exact uOccupied a hfree
    | inr d =>
        obtain ⟨-, -, hfit⟩ := canPlace_inr_iff.mp hcp
        exact receivers_king_nil rfl hfit
  · have h12 := applyDrawStackTo_heights uState (S .king) s hst
    have hsp : (S .king).suit = Suit.spade := rfl
    rw [hsp] at h12
    have h0 : uState.heights Suit.spade = 0 := rfl
    have hk12 : (S .king).rank.toIdx = 12 := rfl
    omega

/-- Q1: the full instance datum of `uStep` — the window play, the
accommodated state, the tableau arm with its base, ALL read at `uMid`;
and no root instance exists. -/
theorem uStep_instance :
    macroStep uState (MacroMove.drawCommit (S .king)) uSucc ∧
    uState.run [Move.pileStack (H .ace)] = some uMid ∧
    (∃ st', st' = uMid ∧ commitApplies st' (MacroMove.drawCommit (S .king)) uSucc) ∧
    uMid.canPlace (S .king) (Sum.inl Anchor.p0) = true ∧
    uMid.applyDrawTo (S .king) (Sum.inl Anchor.p0) = some uSucc ∧
    ¬ ∃ s, commitApplies uState (MacroMove.drawCommit (S .king)) s :=
  ⟨uStep, by rw [run_singleton]; exact uUnseat,
    ⟨uMid, rfl, ⟨Sum.inl Anchor.p0, Or.inl ⟨uMid_canPlace, uSucc_apply⟩⟩⟩,
    uMid_canPlace, uSucc_apply, uNoRootCommit⟩

/-! ### Q2 — the window gates the model actually has -/

/-- Q2: the unseat's source card is UNLOCKED — its seat is the anchor
`p0`, not a hidden boundary, so the B4 gate does not fire. -/
private theorem uHead0_unlocked : uState.isLocked (H .ace) = false := by
  show (match uState.board.bottomOf (H .ace) with
    | some (Sum.inr r) => uState.pileOfTopHidden r ≠ none
    | _ => false) = false
  rw [show uState.board.bottomOf (H .ace) = some (Sum.inl Anchor.p0) from
    (Board.bottomOf_eq _ _ _).mpr (uBoard_topOf_inl Anchor.p0)]

/-- Q2: the vacating play is a SAFE accommodation even under the
model's strictest window gate (`playSafeAccomm`, the B4 locked-source
condition). -/
theorem uUnseat_safeAccommodates : safeAccommodates uState uMid :=
  ⟨[Move.pileStack (H .ace)], uUnseat,
    (fun m hm => by
      rcases List.mem_cons.mp hm with rfl | hm
      · rfl
      · exact absurd hm (by simp)),
    (fun c heq => by
      have hcc : H .ace = c := by injection heq
      subst hcc
      exact uHead0_unlocked),
    trivial⟩

/-! ### The promotion is permanent along the accommodation closure -/

/-- The mid state's heights pattern: only the heart was bumped. -/
private theorem uMid_heights_heart : uMid.heights Suit.heart = 1 := by
  show (if Suit.heart = (H .ace).suit then uState.heights Suit.heart + 1
      else uState.heights Suit.heart) = 1
  have h0 : uState.heights Suit.heart = 0 := rfl
  by_cases hc : Suit.heart = (H .ace).suit
  · rw [ite_eq_left hc, h0]
  · exact absurd rfl hc

private theorem uMid_heights_ne (s : Suit) (h : s ≠ Suit.heart) :
    uMid.heights s = 0 := by
  show (if s = (H .ace).suit then uState.heights s + 1 else uState.heights s) = 0
  rw [ite_eq_right (fun hh => h (hh.trans (rfl : (H .ace).suit = Suit.heart)))]
  rfl

/-- Every anchored head other than the vacated ♥A sits at a foundation
height 0 while its rank is a two or a five-to-nine — no `pileStack` of
any of them can fire from `uMid`. -/
private theorem uMid_head_heights (a : Anchor) (ha : a ≠ Anchor.p0) :
    uMid.heights (uHead a).suit = 0 := by
  cases a with
  | p0 => exact absurd rfl ha
  | p1 => exact uMid_heights_ne _ (by decide)
  | p2 => exact uMid_heights_ne _ (by decide)
  | p3 => exact uMid_heights_ne _ (by decide)
  | p4 => exact uMid_heights_ne _ (by decide)
  | p5 => exact uMid_heights_ne _ (by decide)
  | p6 => exact uMid_heights_ne _ (by decide)

/-- The only seated cards at `uMid` are the six remaining anchored
heads (the dealt pile heads, minus the promoted ♥A). -/
private theorem uMid_seated (c : Card)
    (h : (uMid.board.bottomOf c).isSome = true) :
    ∃ a : Anchor, a ≠ Anchor.p0 ∧ c = uHead a := by
  obtain ⟨b, hb⟩ : ∃ b, uMid.board.bottomOf c = some b := by
    cases hbot : uMid.board.bottomOf c with
    | none => rw [hbot] at h; simp at h
    | some b => exact ⟨b, rfl⟩
  have htb : (uState.board.detach (Sum.inl Anchor.p0)).topOf b = some c :=
    (Board.bottomOf_eq _ _ _).mp hb
  cases b with
  | inl a =>
      by_cases hap0 : a = Anchor.p0
      · rw [hap0, Board.detach_topOf] at htb
        exact absurd htb (by simp)
      · rw [Board.detach_topOf_ne _ _ _ (fun hh => hap0 (Sum.inl.inj hh))] at htb
        have htb2 : uBoard.topOf (Sum.inl a) = some c := htb
        rw [uBoard_topOf_inl] at htb2
        exact ⟨a, hap0, (Option.some.inj htb2).symm⟩
  | inr d =>
      rw [Board.detach_topOf_ne _ _ _ sumInr_ne_sumInl] at htb
      have htb2 : uBoard.topOf (Sum.inr d) = some c := htb
      rw [uBoard_topOf_inr] at htb2
      exact absurd htb2 (by simp)

private theorem uMid_dead_pileStack (c : Card) (t : State)
    (h : uMid.apply (Move.pileStack c) = some t) : False := by
  rw [apply_pileStack_iff] at h
  obtain ⟨-, b, hbot, hrk, -⟩ := h
  obtain ⟨a, hap0, hcu⟩ := uMid_seated c (by rw [hbot]; exact rfl)
  rw [hcu] at hrk
  rw [uMid_head_heights a hap0] at hrk
  cases a with
  | p0 => exact absurd rfl hap0
  | p1 => exact absurd hrk (by decide)
  | p2 => exact absurd hrk (by decide)
  | p3 => exact absurd hrk (by decide)
  | p4 => exact absurd hrk (by decide)
  | p5 => exact absurd hrk (by decide)
  | p6 => exact absurd hrk (by decide)

private theorem uMid_dead_stackPile (c : Card) (b : Base) (t : State)
    (h : uMid.apply (Move.stackPile c b) = some t) : False := by
  rw [apply_stackPile_iff] at h
  obtain ⟨hg, hcp, -, -, -⟩ := h
  by_cases hsh : c.suit = Suit.heart
  · rw [hsh, uMid_heights_heart] at hg
    cases b with
    | inl a =>
        obtain ⟨-, hking⟩ := canPlace_inl_iff.mp hcp
        rw [hking] at hg
        exact absurd hg (by have hk : (Rank.king).toIdx = 12 := rfl; omega)
    | inr d =>
        obtain ⟨-, hvis, hfit⟩ := canPlace_inr_iff.mp hcp
        obtain ⟨a, hap0, hdh⟩ := uMid_seated d hvis
        rw [hdh] at hfit
        obtain ⟨hgc1, hgc2⟩ := (canSitOn_eq c (uHead a)).mp hfit
        cases a with
        | p0 => exact absurd rfl hap0
        | p1 =>
            have hcol : c.suit.color = (D .two).suit.color := by rw [hsh]; rfl
            exact absurd hcol hgc2
        | p2 => exact absurd (hg.symm.trans hgc1) (by decide)
        | p3 => exact absurd (hg.symm.trans hgc1) (by decide)
        | p4 => exact absurd (hg.symm.trans hgc1) (by decide)
        | p5 => exact absurd (hg.symm.trans hgc1) (by decide)
        | p6 => exact absurd (hg.symm.trans hgc1) (by decide)
  · rw [uMid_heights_ne c.suit hsh] at hg
    omega

/-- The post-promotion state is accommodation-dead: every shuffle move
is illegal from `uMid`. -/
private theorem uMid_dead (m : Move) (hm : m.isAccommodation = true)
    (t : State) (hap : uMid.apply m = some t) : False := by
  cases m with
  | pileStack c => exact uMid_dead_pileStack c t hap
  | stackPile c b => exact uMid_dead_stackPile c b t hap
  | draw => simp [Move.isAccommodation] at hm
  | reveal a => simp [Move.isAccommodation] at hm
  | deckPile c b => simp [Move.isAccommodation] at hm
  | deckStack c => simp [Move.isAccommodation] at hm
  | pilePile c b => simp [Move.isAccommodation] at hm

/-- **The promotion is permanent along the window's own closure**: no
accommodation play from `uMid` ever leaves it — in particular the
worried-back ace can never return to the tableau, by kind the
`stackPile ♥A` inverse the objection names and by every other shuffle
move besides. -/
theorem uPromotionPermanent : ∀ (s' : State), accommodates uMid s' → s' = uMid := by
  rintro s' ⟨play, hrun, hall⟩
  induction play generalizing s' with
  | nil => exact (Option.some.inj hrun).symm
  | cons m ms ih =>
      have hm : m.isAccommodation = true := hall m (by simp)
      have hrun' : (match uMid.apply m with
        | some s'' => s''.run ms | none => none) = some s' := hrun
      cases hap : uMid.apply m with
      | none => rw [hap] at hrun'; exact absurd hrun' (by simp)
      | some s₁ =>
          rw [hap] at hrun'
          exact (uMid_dead m hm s₁ hap).elim

/-! ### (a)-route coverage — the shifted root IS hole-labeled -/

/-- Under the objection's reading (the promotion re-grouped as its own
commit), the successor's root is `uMid` itself, and THERE the five
channels suffice: the hole is live at `uMid` (anchor 0 is free) and the
commitment goes through it with the empty accommodation. -/
theorem uShifted_hole_cover :
    LabelLive uMid (S .king) Label.hole ∧
    SuccThrough uMid (S .king) Label.hole uSucc :=
  ⟨⟨Anchor.p0, rfl, Board.detach_topOf uState.board (Sum.inl Anchor.p0)⟩,
   ⟨uMid, [], rfl, (fun _ hm => by simp at hm),
     ⟨Sum.inl Anchor.p0, uMid_canPlace, uSucc_apply⟩, rfl⟩⟩


/-! ## The reachable-corner addendum (wave-20) — the route shapes live
ON the dealt-reachable fragment

This section is the decide-first outcome of the wave-20 ticket: does
any *dealt-reachable* configuration admit the witness route shape?
`rState` answers YES in the strongest possible form — **the dealt
initial state of an honest 52-card deal**, reached by the EMPTY play:

* the state is `State.initial rDeal 1`, so `rState_reachable` is the
  zero-move reachability exhibit — no countermodel construction, no
  hand-crafted matching; the wave-19B fence (all depths zero, all
  heights zero, empty board) cannot bite, the deal is honest and the
  board is the deal-fold itself;
* ♠K sits at the stock's first reachable slot (`rState_pos`), the
  spade suit is FROZEN (heights 0 and no spade seated at the dealt
  board — every pile's top dealt card is a non-spade,
  `rSpades_unseated`), so the stack channel stays dead along every
  accommodation walk (`rFrozenToStack` — the very same freeze
  argument as §`uState`'s, reused file-locally);
* ♠A hides beneath ♥2 in pile 1 while ♥A — pile 0's single dealt
  card — sits UNCOVERED ON ITS ANCHOR at foundation height 0: the
  one-move promotion `pileStack ♥A` (the anchored head's rank-dig)
  is a legal accommodation window (`rUnseat`), it unseats THROUGH
  THE ANCHOR, and the `Draw(♠K)` commitment then lands the king on
  the vacated anchor (`rStep`) — the anchored-head unseat route,
  live at a REACHABLE root;
* every channel of the current five-element list fails to label that
  successor (`rSucc_unlabeled`): `direct`/`dig`/`borrow p` die on
  `receivers_king_nil`, `toStack` on the freeze, and `hole` — though
  LIVE at the root (six anchors sit free below the dealt seats) —
  cannot name the successor, because the hole signature demands the
  EMPTY window while the promotion successor's heart height is 1
  against every root commit's 0 (`rRoute_not_hole`).

Hence `wk_succ_labeled_reachable_false`: the initialReachable-GATED
`succ_labeled` is refuted, not restored — the wave-19B "RESTORED
under hreach" reading holds only against the pristine family itself.

**AND, BESIDE IT, the same root splits the four class universals'
gated readings too**: with six free anchors and the king
frozen-climb-blocked, three root tableau landings of `Draw(♠K)`
(`rLand p1`, `rLand p2`, `rLand p3`) are pairwise closure-separated
(`rLand_split` — below a landed king the frozen suit can never move:
`pileStack ♠K` needs rung 12 against the frozen 0, no other spade
can ever be seated or founded along the accommodation fragment, and
`stackPile` cannot land on the occupied anchor) — while all three go
through the LIVE, P2-safe `hole` channel at the root with empty
signature windows.  So the naive initialReachable-gated
`c2_two_option` (the ≤2 count), `same_pin_closureEq`,
`p2_direct_class`, and `crease_chain_absorbed` are refuted at
reachable states as well (`wk_c2_reachable_false`,
`wk_same_pin_reachable_false`, `wk_p2_direct_reachable_false`,
`wk_crease_reachable_false`).  What IS proven — where the real
content lives — are the regimes of `Klondike.C2Streamlined` §12.5
(the zero-spend rung derivations) and §15 (the at-most-one-free-anchor
frozen-king corner): at THIS root neither applies (six free anchors),
which is exactly the shape gap the engine-side corpus (seed 26's weak
corners, ONE free anchor) never presents.

**THE LABEL-DECISION INPUT for the orchestrator** (this wave's
ticket item 3; the channel-list edit itself is out of scope here):
the anchored-head unseat route is NOT a countermodel-corner artifact
of the pristine witness family — it occurs at zero-move-reachable
dealt initial states, so the five-channel completeness FAILS on the
fragment the engine actually plays.  The repair options stand, now
with reachability evidence attached: (a) extend the channel list
with the `anchorHead a` atom (the vacated anchor's seat — the route's
minimal enabling pinning; note the label cannot be `hole`: hole
liveness at the root does not cover promotion successors, by the
heights separation in `rRoute_not_hole`), or (b) gate the window
relation (`macroStep`'s `accommodates`) on context-irreversibility —
under that reading the promotion is its own commit (§`uPromotionPermanent`
shows the permanence), the route regroups as [promote ♥A, then
`Draw ♠K`], and the successor IS hole-labeled at the shifted root
(`uShifted_hole_cover`).  The engine-side questions this session
cannot decide in Lean (harness tickets for the orchestrator):
(1) how often played engine games present the frozen-suit
stocked-king-plus-six-free-anchors shape (the corpus sweep; wave-18's
"≥2 free anchors" ticket stays open), and (2) the frequency of
uncovered promoted anchors (any suit's ace or rank-mate head on an
anchor at its foundation height) alongside a frozen drawn king —
the route's real-world urgency calibration. -/

private def rStockList : List Card :=
  [S .king] ++
  [C .ace, C .two, C .three, C .four, C .five, C .six, C .seven,
   C .eight, C .nine, C .ten, C .jack, C .queen, C .king] ++
  [H .king] ++
  [D .ace, D .six, D .seven, D .eight, D .nine, D .ten, D .jack, D .queen, D .king]

/-- The reachable-corner deal: every pile's top dealt card (the last
element) is a non-spade, twelve low spades hide in the buried slices,
♠K heads the stock — 1+2+…+7 pile cards, a 24-card stock, all 52
distinct. -/
private def rDeal : Deal where
  piles := fun a =>
    match a with
    | .p0 => [H .ace]
    | .p1 => [S .ace, H .two]
    | .p2 => [S .two, S .three, H .three]
    | .p3 => [S .four, S .five, S .six, H .four]
    | .p4 => [S .seven, S .eight, S .nine, S .ten, H .five]
    | .p5 => [S .jack, S .queen, H .six, H .seven, H .eight, H .nine]
    | .p6 => [H .ten, H .jack, H .queen, D .two, D .three, D .four, D .five]
  stock := rStockList

/-- The reachable corner: `rDeal`'s dealt initial state at draw step
1 — the empty play away from the deal itself. -/
private def rState : State := State.initial rDeal 1

private theorem rDeal_wf : rDeal.WF := by
  refine ⟨fun a => ?_, by decide, ?_⟩
  · cases a <;> decide
  · intro i j hi hj heq
    have hflat : (Anchor.all.flatMap rDeal.piles).length = 28 := by decide
    have hstock : rDeal.stock.length = 24 := by decide
    rw [List.length_append, hflat, hstock] at hi hj
    have hall : ∀ i ∈ List.range 52, ∀ j ∈ List.range 52,
        (Anchor.all.flatMap rDeal.piles ++ rDeal.stock)[i]? =
          (Anchor.all.flatMap rDeal.piles ++ rDeal.stock)[j]? → i = j := by decide
    exact hall i (List.mem_range.mpr hi) j (List.mem_range.mpr hj) heq

/-- **The zero-move reachability exhibit**: the corner state is dealt,
literally — `initialReachable` by the empty play. -/
theorem rState_reachable : initialReachable rState :=
  ⟨rDeal, 1, [], rDeal_wf, by decide, by rfl⟩

private theorem rState_wf : rState.WF := initial_wf rDeal_wf (by decide)

private theorem rHeights0 (s : Suit) : rState.heights s = 0 := rfl

/-- The drawn king: ♠K at the stock's first reachable position. -/
private theorem rState_pos : rState.reachablePos (S .king) = some 0 := by
  rw [State.reachablePos_step1 rState_wf rfl (S .king)]
  rfl

/-! ### The dealt board facts (kernel-decided where the search is finite;
the freeze by the edge analysis) -/

/-- Pile 0's single dealt card — the ace of hearts — sits directly on
its anchor, uncovered. -/
private theorem rSeat0 : rState.board.topOf (Sum.inl Anchor.p0) = some (H .ace) := by
  decide

private theorem rNoCoverAce : rState.board.topOf (Sum.inr (H .ace)) = none := by
  decide

private theorem rFree1 : rState.board.topOf (Sum.inl Anchor.p1) = none := by decide
private theorem rFree2 : rState.board.topOf (Sum.inl Anchor.p2) = none := by decide
private theorem rFree3 : rState.board.topOf (Sum.inl Anchor.p3) = none := by decide

/-- The piles' dealt tops, exposed for the freeze argument. -/
private theorem rTopLast (a : Anchor) : (rDeal.piles a).getLast? =
    some (match a with
      | .p0 => H .ace
      | .p1 => H .two
      | .p2 => H .three
      | .p3 => H .four
      | .p4 => H .five
      | .p5 => H .nine
      | .p6 => D .five) := by
  cases a <;> rfl

/-- **The freeze at the corner**: no spade is seated on the dealt
board — every seated card is a pile's top dealt card, and all seven
tops are non-spades — so (with all heights 0) the spade suit can never
be founded, ever, along the accommodation fragment. -/
private theorem rSpades_unseated (c : Card) (hcs : c.suit = Suit.spade) :
    rState.board.bottomOf c = none := by
  refine (Board.bottomOf_eq_none _ _).mpr (fun b hb => ?_)
  obtain ⟨a, -, -, hgt⟩ := initialBoard_topOf rDeal b c hb
  cases a
  · rw [rTopLast Anchor.p0] at hgt
    have hc : c = H .ace := (Option.some.inj hgt).symm
    rw [hc] at hcs
    exact absurd hcs (by decide)
  · rw [rTopLast Anchor.p1] at hgt
    have hc : c = H .two := (Option.some.inj hgt).symm
    rw [hc] at hcs
    exact absurd hcs (by decide)
  · rw [rTopLast Anchor.p2] at hgt
    have hc : c = H .three := (Option.some.inj hgt).symm
    rw [hc] at hcs
    exact absurd hcs (by decide)
  · rw [rTopLast Anchor.p3] at hgt
    have hc : c = H .four := (Option.some.inj hgt).symm
    rw [hc] at hcs
    exact absurd hcs (by decide)
  · rw [rTopLast Anchor.p4] at hgt
    have hc : c = H .five := (Option.some.inj hgt).symm
    rw [hc] at hcs
    exact absurd hcs (by decide)
  · rw [rTopLast Anchor.p5] at hgt
    have hc : c = H .nine := (Option.some.inj hgt).symm
    rw [hc] at hcs
    exact absurd hcs (by decide)
  · rw [rTopLast Anchor.p6] at hgt
    have hc : c = D .five := (Option.some.inj hgt).symm
    rw [hc] at hcs
    exact absurd hcs (by decide)

/-! ### The route: the promotion window and the king's landing -/

private def rMid : State :=
  { rState with
    board := rState.board.detach (Sum.inl Anchor.p0),
    heights := fun s => if s = (H .ace).suit then rState.heights s + 1
      else rState.heights s }

/-- The anchored ace leaves — its rank-dig (foundation height 0) is
the unseat route's one-move window. -/
private theorem rUnseat : rState.apply (Move.pileStack (H .ace)) = some rMid := by
  rw [apply_pileStack_iff]
  exact ⟨rNoCoverAce, Sum.inl Anchor.p0, (Board.bottomOf_eq _ _ _).mpr rSeat0, rfl, rfl⟩

private theorem rMid_wf : rMid.WF := apply_wf rState_wf _ _ rUnseat

private theorem rMid_canPlace :
    rMid.canPlace (S .king) (Sum.inl Anchor.p0) = true := by
  rw [canPlace_inl_iff]
  exact ⟨Board.detach_topOf rState.board (Sum.inl Anchor.p0), rfl⟩

/-- The freeze rides the promotion window (the file-local
`freeze_run`): no spade is seated at the landed-king's window state. -/
private theorem rMid_bottomOf_king : rMid.board.bottomOf (S .king) = none := by
  obtain ⟨-, hns⟩ := freeze_run [Move.pileStack (H .ace)] rState (rHeights0 _)
    rSpades_unseated rMid
    (by
      intro m hm
      rcases List.mem_cons.mp hm with rfl | hm
      · rfl
      · exact absurd hm (by simp))
    (by rw [run_singleton]; exact rUnseat)
  exact hns (S .king) rfl

private theorem rMid_pos : rMid.reachablePos (S .king) = some 0 := by
  rw [State.reachablePos_step1 rMid_wf rfl (S .king)]
  rfl

/-- The route's successor: the king on the vacated anchor, heart
height 1 (the promotion's foundation bump). -/
private def rSucc : State :=
  (rMid.applyDrawTo (S .king) (Sum.inl Anchor.p0)).getD rMid

private theorem rSucc_apply :
    rMid.applyDrawTo (S .king) (Sum.inl Anchor.p0) = some rSucc := by
  have hne : rMid.board.attach (Sum.inl Anchor.p0) (S .king) ≠ none :=
    (Board.attach_eq_some_iff _ _ _).mpr ⟨Board.detach_topOf rState.board
      (Sum.inl Anchor.p0), rMid_bottomOf_king⟩
  cases hatt : rMid.board.attach (Sum.inl Anchor.p0) (S .king) with
  | none => exact absurd hatt hne
  | some bd =>
      have hto : rMid.applyDrawTo (S .king) (Sum.inl Anchor.p0) = some
          { rMid with board := bd, stock := (rMid.stock.drawTo 0).removeAt 0 } :=
        applyDrawTo_iff.mpr ⟨0, bd, rMid_pos, hatt, rfl⟩
      cases h : rMid.applyDrawTo (S .king) (Sum.inl Anchor.p0) with
      | none =>
          have h2 := hto
          rw [h] at h2
          exact absurd h2 (by simp)
      | some s' =>
          have hw : rSucc = s' := by
            show (rMid.applyDrawTo (S .king) (Sum.inl Anchor.p0)).getD rMid = s'
            rw [h]
            rfl
          rw [hw]

/-- **The route IS a macro successor of the commitment** — the window
is the promotion, the arm is the tableau landing on the vacated
anchor. -/
theorem rStep : macroStep rState (MacroMove.drawCommit (S .king)) rSucc := by
  refine ⟨rMid, ⟨[Move.pileStack (H .ace)], ?_, ?_⟩,
    ⟨Sum.inl Anchor.p0, Or.inl ⟨rMid_canPlace, rSucc_apply⟩⟩⟩
  · rw [run_singleton]
    exact rUnseat
  · intro m hm
    rcases List.mem_cons.mp hm with rfl | hm
    · rfl
    · exact absurd hm (by simp)

/-! ### Every current channel fails to label the route -/

private theorem rKingNoReceivers (p : Card) (h : canSitOn (S .king) p = true) :
    False := receivers_king_nil rfl h

private theorem rFrozenToStack (r s : State)
    (hacc : accommodates rState r) (hfire : r.applyDrawStackTo (S .king) = some s) :
    False := by
  obtain ⟨play, hrun, hall⟩ := hacc
  obtain ⟨h0, -⟩ := freeze_run play rState (rHeights0 _) rSpades_unseated r hall hrun
  have h12 := applyDrawStackTo_heights r (S .king) s hfire
  have hk12 : (S .king).rank.toIdx = 12 := rfl
  have hsp : (S .king).suit = Suit.spade := rfl
  rw [hsp] at h12
  omega

private theorem rMid_heights_heart : rMid.heights Suit.heart = 1 := by
  show (if Suit.heart = (H .ace).suit then rState.heights Suit.heart + 1
      else rState.heights Suit.heart) = 1
  have h0 : rState.heights Suit.heart = 0 := rfl
  by_cases hc : Suit.heart = (H .ace).suit
  · rw [ite_eq_left hc, h0]
  · exact absurd rfl hc

private theorem rSucc_heights_heart : rSucc.heights Suit.heart = 1 := by
  obtain ⟨i, bd, -, -, hs⟩ := applyDrawTo_eq rSucc_apply
  rw [hs]
  exact rMid_heights_heart

/-- The live hole channel still cannot NAME the route successor: the
hole signature demands the empty window, so the commit would sit at
the root — but every root commit's heart height is the dealt 0, and
the promotion successor's is 1.  (Hole LIVEness is hereby orthogonal
to the route: six free anchors do not save the labeling.) -/
private theorem rRoute_not_hole : ¬ SuccThrough rState (S .king) Label.hole rSucc := by
  rintro ⟨u, α, hrun, -, harm, hsig⟩
  have hα : α = [] := hsig
  rw [hα] at hrun
  rw [(run_nil_elim hrun).symm] at harm
  obtain ⟨b, -, hto⟩ := harm
  obtain ⟨i, bd, -, -, hs⟩ := applyDrawTo_eq hto
  have h1 : rSucc.heights Suit.heart = rState.heights Suit.heart := by
    rw [hs]
  rw [rSucc_heights_heart, rHeights0] at h1
  exact absurd h1 (by decide)

private theorem rSucc_unlabeled (r : Label (S .king)) :
    ¬ (LabelLive rState (S .king) r ∧ SuccThrough rState (S .king) r rSucc) := by
  rintro ⟨hlive, hthru⟩
  cases r with
  | direct =>
      obtain ⟨Y, hd⟩ := hlive
      exact rKingNoReceivers Y hd.hY
  | dig =>
      obtain ⟨Y, hd⟩ := hlive
      exact rKingNoReceivers Y hd.hY
  | borrow p =>
      obtain ⟨hp, -⟩ := hlive
      exact rKingNoReceivers p hp
  | hole => exact rRoute_not_hole hthru
  | toStack =>
      obtain ⟨r', s', hacc, hfire⟩ := hlive
      exact rFrozenToStack r' s' hacc hfire

/-- **The gated `succ_labeled` is REFUTED**: on the dealt-reachable
fragment there is a WF state — the dealt initial state of an honest
deal — whose `Draw(♠K)` commitment has a macro successor (the
anchored-ace promotion route) that NO channel of the current
five-element list labels. -/
theorem wk_succ_labeled_reachable_false :
    ¬ (∀ (st : State) (X : Card) (s : State), initialReachable st → st.WF →
        macroStep st (MacroMove.drawCommit X) s →
        ∃ r : Label X, LabelLive st X r ∧ SuccThrough st X r s) := by
  intro h
  obtain ⟨r, hlive, hthru⟩ :=
    h rState (S .king) rSucc rState_reachable rState_wf rStep
  exact rSucc_unlabeled r ⟨hlive, hthru⟩

/-! ### The four class universals' gated readings fall here too -/

private def rLand (a : Anchor) : State :=
  (rState.applyDrawTo (S .king) (Sum.inl a)).getD rState

private theorem rLand_apply (a : Anchor)
    (hfree : rState.board.topOf (Sum.inl a) = none) :
    rState.applyDrawTo (S .king) (Sum.inl a) = some (rLand a) := by
  have hne : rState.board.attach (Sum.inl a) (S .king) ≠ none :=
    (Board.attach_eq_some_iff _ _ _).mpr ⟨hfree, rSpades_unseated (S .king) rfl⟩
  cases hatt : rState.board.attach (Sum.inl a) (S .king) with
  | none => exact absurd hatt hne
  | some bd =>
      have hto : rState.applyDrawTo (S .king) (Sum.inl a) = some
          { rState with board := bd, stock := (rState.stock.drawTo 0).removeAt 0 } :=
        applyDrawTo_iff.mpr ⟨0, bd, rState_pos, hatt, rfl⟩
      cases h : rState.applyDrawTo (S .king) (Sum.inl a) with
      | none =>
          have h2 := hto
          rw [h] at h2
          exact absurd h2 (by simp)
      | some s' =>
          have hw : rLand a = s' := by
            show (rState.applyDrawTo (S .king) (Sum.inl a)).getD rState = s'
            rw [h]
            rfl
          rw [hw]

private theorem rCanPlace (a : Anchor) (hfree : rState.board.topOf (Sum.inl a) = none) :
    rState.canPlace (S .king) (Sum.inl a) = true :=
  canPlace_inl_iff.mpr ⟨hfree, rfl⟩

private theorem rTableau (a : Anchor) (hfree : rState.board.topOf (Sum.inl a) = none) :
    CommitTableau rState (S .king) (rLand a) :=
  ⟨Sum.inl a, rCanPlace a hfree, rLand_apply a hfree⟩

private theorem rStepLand (a : Anchor) (hfree : rState.board.topOf (Sum.inl a) = none) :
    macroStep rState (MacroMove.drawCommit (S .king)) (rLand a) := by
  refine ⟨rState, ⟨[], rfl, fun _ hm => by simp at hm⟩, ?_⟩
  exact ⟨Sum.inl a, Or.inl ⟨rCanPlace a hfree, rLand_apply a hfree⟩⟩

private theorem rLand_holeThrough (a : Anchor)
    (hfree : rState.board.topOf (Sum.inl a) = none) :
    SuccThrough rState (S .king) Label.hole (rLand a) :=
  ⟨rState, [], rfl, (fun _ hm => by simp at hm), rTableau a hfree, rfl⟩

private theorem rLand_holeLive :
    LabelLive rState (S .king) Label.hole :=
  ⟨Anchor.p1, rfl, rFree1⟩

/-- The landed-king state's shape facts: the spade height still 0, no
spade but the king seated, the king on its anchor's base. -/
private theorem rLand_seated (a : Anchor)
    (hfree : rState.board.topOf (Sum.inl a) = none) :
    (rLand a).heights Suit.spade = 0 ∧
    (∀ c : Card, c.suit = Suit.spade → c ≠ S .king →
      (rLand a).board.bottomOf c = none) ∧
    (rLand a).board.topOf (Sum.inl a) = some (S .king) := by
  obtain ⟨i, bd, -, hatt, hs⟩ := applyDrawTo_eq (rLand_apply a hfree)
  rw [hs]
  refine ⟨rfl, ?_, ?_⟩
  · intro c hcs hcK
    rw [bottomOf_attach_of_ne hatt hcK]
    exact rSpades_unseated c hcs
  · exact Board.attach_topOf _ _ _ hatt

/-- **The frozen seat invariant, one step**: an accommodation move
below a landed frozen-suit king never raises the spade height (only a
seated spade at the rung could found; no non-king spade ever seats,
and the king itself needs rung 12 against 0), never seats a non-king
spade (the only seating move is `stackPile`, which demands
foundedness no spade can reach), and never moves the king (its
unseating `pileStack` is dead; a `stackPile` cannot land on the
occupied anchor). -/
private theorem rFrozen_seat_step (st t : State) (a : Anchor) (m : Move)
    (hm : m.isAccommodation = true) (hap : st.apply m = some t)
    (h0 : st.heights Suit.spade = 0)
    (hns : ∀ c : Card, c.suit = Suit.spade → c ≠ S .king → st.board.bottomOf c = none)
    (hK : st.board.topOf (Sum.inl a) = some (S .king)) :
    t.heights Suit.spade = 0 ∧
    (∀ c : Card, c.suit = Suit.spade → c ≠ S .king → t.board.bottomOf c = none) ∧
    t.board.topOf (Sum.inl a) = some (S .king) := by
  cases m with
  | draw => simp [Move.isAccommodation] at hm
  | reveal a' => simp [Move.isAccommodation] at hm
  | deckPile c b => simp [Move.isAccommodation] at hm
  | deckStack c => simp [Move.isAccommodation] at hm
  | pilePile c b => simp [Move.isAccommodation] at hm
  | pileStack c =>
      rw [apply_pileStack_iff] at hap
      obtain ⟨htopn, b, hbot, hrk, rfl⟩ := hap
      by_cases hcs : c.suit = Suit.spade
      · exfalso
        by_cases hck : c = S .king
        · rw [hck] at hrk
          have h12 : (S .king).rank.toIdx = 12 := rfl
          have hsp : (S .king).suit = Suit.spade := rfl
          rw [hsp] at hrk
          omega
        · have hnone := hns c hcs hck
          rw [hnone] at hbot
          exact absurd hbot (by simp)
      · have hstb : st.board.topOf b = some c := (Board.bottomOf_eq st.board c b).mp hbot
        have hb : b ≠ Sum.inl a := by
          intro hcon
          rw [hcon] at hstb
          have hkc : c = S .king :=
            Option.some.inj (hstb.symm.trans hK)
          exact hcs (by rw [hkc]; rfl)
        refine ⟨by
            show (if Suit.spade = c.suit then st.heights Suit.spade + 1
                else st.heights Suit.spade) = 0
            rw [ite_eq_right (fun hh => hcs hh.symm), h0], ?_, ?_⟩
        · intro c' hc's hc'K
          have hc'c : c' ≠ c := fun hh => hcs (by rw [← hh]; exact hc's)
          rw [bottomOf_detach_ne hstb hc'c]
          exact hns c' hc's hc'K
        · show (st.board.detach b).topOf (Sum.inl a) = some (S .king)
          rw [Board.detach_topOf_ne st.board b (Sum.inl a) (Ne.symm hb)]
          exact hK
  | stackPile c b =>
      rw [apply_stackPile_iff] at hap
      obtain ⟨hg, hcp, bd, hatt, rfl⟩ := hap
      by_cases hcs : c.suit = Suit.spade
      · exfalso
        rw [hcs] at hg
        omega
      · have hb : b ≠ Sum.inl a := by
          intro hcon
          have hse := topOf_of_canPlace hcp
          rw [hcon] at hse
          rw [hK] at hse
          exact absurd hse (by simp)
        refine ⟨by
            show (if Suit.spade = c.suit then st.heights Suit.spade - 1
                else st.heights Suit.spade) = 0
            rw [ite_eq_right (fun hh => hcs hh.symm), h0], ?_, ?_⟩
        · intro c' hc's hc'K
          have hc'c : c' ≠ c := fun hh => hcs (by rw [← hh]; exact hc's)
          rw [bottomOf_attach_of_ne hatt hc'c]
          exact hns c' hc's hc'K
        · show bd.topOf (Sum.inl a) = some (S .king)
          rw [Board.attach_topOf_ne st.board b c hatt (Ne.symm hb)]
          exact hK

/-- The invariant rides every accommodation play from a landed king. -/
private theorem rFrozen_seat_run (a : Anchor) : ∀ (play : List Move)
    (st t : State), (∀ m ∈ play, m.isAccommodation = true) → st.run play = some t →
    st.heights Suit.spade = 0 →
    (∀ c : Card, c.suit = Suit.spade → c ≠ S .king → st.board.bottomOf c = none) →
    st.board.topOf (Sum.inl a) = some (S .king) →
    t.heights Suit.spade = 0 ∧
    (∀ c : Card, c.suit = Suit.spade → c ≠ S .king → t.board.bottomOf c = none) ∧
    t.board.topOf (Sum.inl a) = some (S .king) := by
  intro play
  induction play with
  | nil =>
      intro st t _ hrun h0 hns hK
      have he : st = t := Option.some.inj hrun
      subst he
      exact ⟨h0, hns, hK⟩
  | cons m ms ih =>
      intro st t hall hrun h0 hns hK
      obtain ⟨v, hmstep, hmsrun⟩ := run_cons_elim hrun
      obtain ⟨h0v, hnsv, hKv⟩ := rFrozen_seat_step st v a m
        (hall m (by simp)) hmstep h0 hns hK
      exact ih v t (fun m' hm' => hall m' (List.mem_cons_of_mem _ hm')) hmsrun h0v hnsv hKv

/-- **The split**: two different anchor landings of the same frozen
king cannot be reconciled — any accommodation walk below one landing
keeps the king on ITS anchor (the invariant), while the other
landing's board shows that anchor bare. -/
private theorem rLand_split (a a' : Anchor) (h : a ≠ a')
    (hfree : rState.board.topOf (Sum.inl a) = none)
    (hfree' : rState.board.topOf (Sum.inl a') = none) :
    ¬ accommodates (rLand a) (rLand a') := by
  rintro ⟨play, hrun, hall⟩
  have hbase := rLand_seated a hfree
  obtain ⟨-, -, hKend⟩ := rFrozen_seat_run a play (rLand a) (rLand a') hall hrun
    hbase.1 hbase.2.1 hbase.2.2
  obtain ⟨i, bd, -, hatt, hs⟩ := applyDrawTo_eq (rLand_apply a' hfree')
  have hcon : (rLand a').board.topOf (Sum.inl a) = none := by
    rw [hs]
    show bd.topOf (Sum.inl a) = none
    rw [Board.attach_topOf_ne _ _ _ hatt (fun hh => h (Sum.inl.inj hh))]
    exact hfree
  rw [hKend] at hcon
  exact absurd hcon (by simp)

/-- **The gated `c2_two_option` (the ≤2 count) is REFUTED**: three
pairwise closure-separated macro successors of one commitment at a
dealt-reachable state. -/
theorem wk_c2_reachable_false :
    ¬ (∀ (st : State) (X : Card) (s₁ s₂ s₃ : State), initialReachable st → st.WF →
        macroStep st (MacroMove.drawCommit X) s₁ →
        macroStep st (MacroMove.drawCommit X) s₂ →
        macroStep st (MacroMove.drawCommit X) s₃ →
        closureEq s₁ s₂ ∨ closureEq s₁ s₃ ∨ closureEq s₂ s₃) := by
  intro h
  rcases h rState (S .king) (rLand Anchor.p1) (rLand Anchor.p2) (rLand Anchor.p3)
      rState_reachable rState_wf
      (rStepLand Anchor.p1 rFree1) (rStepLand Anchor.p2 rFree2) (rStepLand Anchor.p3 rFree3) with
    q | q | q
  · exact rLand_split Anchor.p1 Anchor.p2 (by decide) rFree1 rFree2 q.1
  · exact rLand_split Anchor.p1 Anchor.p3 (by decide) rFree1 rFree3 q.1
  · exact rLand_split Anchor.p2 Anchor.p3 (by decide) rFree2 rFree3 q.1

/-- **The gated `same_pin_closureEq` is REFUTED**: the hole channel is
live at the root and both landings go through it (empty signature
windows), and they stay closure-split. -/
theorem wk_same_pin_reachable_false :
    ¬ (∀ (st : State) (X : Card) (r : Label X) (s s' : State), initialReachable st →
        st.WF → LabelLive st X r → SuccThrough st X r s →
        SuccThrough st X r s' → closureEq s s') := by
  intro h
  exact rLand_split Anchor.p1 Anchor.p2 (by decide) rFree1 rFree2
    (h rState (S .king) Label.hole (rLand Anchor.p1) (rLand Anchor.p2)
      rState_reachable rState_wf rLand_holeLive
      (rLand_holeThrough Anchor.p1 rFree1) (rLand_holeThrough Anchor.p2 rFree2)).1

/-- **The gated `p2_direct_class` is REFUTED**: the direct commit on
anchor 1, the safe hole-channel successor on anchor 2, no class join. -/
theorem wk_p2_direct_reachable_false :
    ¬ (∀ (st : State) (X : Card) (sd s_p : State) (r : Label X), initialReachable st →
        st.WF → commitApplies st (MacroMove.drawCommit X) sd →
        SuccThrough st X r s_p → P2Safe st X r →
        closureEq sd s_p) := by
  intro h
  have hsd : commitApplies rState (MacroMove.drawCommit (S .king)) (rLand Anchor.p1) :=
    ⟨Sum.inl Anchor.p1, Or.inl ⟨rCanPlace Anchor.p1 rFree1,
      rLand_apply Anchor.p1 rFree1⟩⟩
  exact rLand_split Anchor.p1 Anchor.p2 (by decide) rFree1 rFree2
    (h rState (S .king) (rLand Anchor.p1) (rLand Anchor.p2) Label.hole
      rState_reachable rState_wf hsd (rLand_holeThrough Anchor.p2 rFree2) trivial).1

/-- **The gated `crease_chain_absorbed` is REFUTED**: both windows
empty (sublist-reflexive), both arms the hole-channel tableau commit
at the root, and the class join fails. -/
theorem wk_crease_reachable_false :
    ¬ (∀ (st : State) (X : Card) (r : Label X) (s s' : State)
        (α α' : List Move) (u u' : State), initialReachable st → st.WF →
        LabelLive st X r →
        st.run α = some u → (∀ m ∈ α, m.isAccommodation = true) →
        commitArmOf u X r s → LabelSig X r α →
        st.run α' = some u' → (∀ m ∈ α', m.isAccommodation = true) →
        commitArmOf u' X r s' → LabelSig X r α' →
        List.Sublist α α' →
        closureEq s s') := by
  intro h
  have hrfl : rState.run [] = some rState := rfl
  have hnul : ∀ m ∈ ([] : List Move), m.isAccommodation = true :=
    fun _ hm => by simp at hm
  exact rLand_split Anchor.p1 Anchor.p2 (by decide) rFree1 rFree2
    (h rState (S .king) Label.hole (rLand Anchor.p1) (rLand Anchor.p2)
      [] [] rState rState rState_reachable rState_wf rLand_holeLive
      hrfl hnul (rTableau Anchor.p1 rFree1) rfl
      hrfl hnul (rTableau Anchor.p2 rFree2) rfl
      List.Sublist.slnil).1
end SuccLabeled

#print axioms SuccLabeled.wk_succ_labeled_as_stated_false
#print axioms SuccLabeled.uStep_instance
#print axioms SuccLabeled.uUnseat_safeAccommodates
#print axioms SuccLabeled.uPromotionPermanent
#print axioms SuccLabeled.uShifted_hole_cover
#print axioms SuccLabeled.rState_reachable
#print axioms SuccLabeled.rStep
#print axioms SuccLabeled.wk_succ_labeled_reachable_false
#print axioms SuccLabeled.wk_c2_reachable_false
#print axioms SuccLabeled.wk_same_pin_reachable_false
#print axioms SuccLabeled.wk_p2_direct_reachable_false
#print axioms SuccLabeled.wk_crease_reachable_false
