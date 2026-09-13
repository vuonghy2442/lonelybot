import Klondike.Move

/-!
# The `solvable_engine_iff` refutation witness

A WF state where the full game wins but the engine (no `pilePile`)
cannot: the reveal-deadlock.  Pile p2 = [♥3 (hidden), ♠5, ♥4]: to
reveal ♥3 the trigger ♠5 must be bare, so ♥4 must leave; ♥4's only
exit besides `pilePile` is `pileStack` (needs hearts' height 3, i.e.
♥3 already stacked); ♥3 can only be stacked after the reveal.  The
full game parks ♥4 on ♣5 (pile p0's bare top) with `pilePile`, then
wins by pure foundation stacking.  The engine is doomed to hearts ≤ 2.
-/

namespace EngineWitness

/-- The witness's card abbreviations. -/
abbrev whA : Card := ⟨Suit.heart, Rank.ace⟩
abbrev wh2 : Card := ⟨Suit.heart, Rank.two⟩
abbrev wh3 : Card := ⟨Suit.heart, Rank.three⟩
abbrev wh4 : Card := ⟨Suit.heart, Rank.four⟩
abbrev wh5 : Card := ⟨Suit.heart, Rank.five⟩
abbrev wh6 : Card := ⟨Suit.heart, Rank.six⟩
abbrev wh7 : Card := ⟨Suit.heart, Rank.seven⟩
abbrev wh8 : Card := ⟨Suit.heart, Rank.eight⟩
abbrev wh9 : Card := ⟨Suit.heart, Rank.nine⟩
abbrev wh10 : Card := ⟨Suit.heart, Rank.ten⟩
abbrev whJ : Card := ⟨Suit.heart, Rank.jack⟩
abbrev whQ : Card := ⟨Suit.heart, Rank.queen⟩
abbrev whK : Card := ⟨Suit.heart, Rank.king⟩

abbrev wsA : Card := ⟨Suit.spade, Rank.ace⟩
abbrev ws2 : Card := ⟨Suit.spade, Rank.two⟩
abbrev ws3 : Card := ⟨Suit.spade, Rank.three⟩
abbrev ws4 : Card := ⟨Suit.spade, Rank.four⟩
abbrev ws5 : Card := ⟨Suit.spade, Rank.five⟩
abbrev ws6 : Card := ⟨Suit.spade, Rank.six⟩
abbrev ws7 : Card := ⟨Suit.spade, Rank.seven⟩
abbrev ws8 : Card := ⟨Suit.spade, Rank.eight⟩
abbrev ws9 : Card := ⟨Suit.spade, Rank.nine⟩
abbrev ws10 : Card := ⟨Suit.spade, Rank.ten⟩
abbrev wsJ : Card := ⟨Suit.spade, Rank.jack⟩
abbrev wsQ : Card := ⟨Suit.spade, Rank.queen⟩
abbrev wsK : Card := ⟨Suit.spade, Rank.king⟩

abbrev wdA : Card := ⟨Suit.diamond, Rank.ace⟩
abbrev wd2 : Card := ⟨Suit.diamond, Rank.two⟩
abbrev wd3 : Card := ⟨Suit.diamond, Rank.three⟩
abbrev wd4 : Card := ⟨Suit.diamond, Rank.four⟩
abbrev wd5 : Card := ⟨Suit.diamond, Rank.five⟩
abbrev wd6 : Card := ⟨Suit.diamond, Rank.six⟩
abbrev wd7 : Card := ⟨Suit.diamond, Rank.seven⟩
abbrev wd8 : Card := ⟨Suit.diamond, Rank.eight⟩
abbrev wd9 : Card := ⟨Suit.diamond, Rank.nine⟩
abbrev wd10 : Card := ⟨Suit.diamond, Rank.ten⟩
abbrev wdJ : Card := ⟨Suit.diamond, Rank.jack⟩
abbrev wdQ : Card := ⟨Suit.diamond, Rank.queen⟩
abbrev wdK : Card := ⟨Suit.diamond, Rank.king⟩

abbrev wcA : Card := ⟨Suit.club, Rank.ace⟩
abbrev wc2 : Card := ⟨Suit.club, Rank.two⟩
abbrev wc3 : Card := ⟨Suit.club, Rank.three⟩
abbrev wc4 : Card := ⟨Suit.club, Rank.four⟩
abbrev wc5 : Card := ⟨Suit.club, Rank.five⟩
abbrev wc6 : Card := ⟨Suit.club, Rank.six⟩
abbrev wc7 : Card := ⟨Suit.club, Rank.seven⟩
abbrev wc8 : Card := ⟨Suit.club, Rank.eight⟩
abbrev wc9 : Card := ⟨Suit.club, Rank.nine⟩
abbrev wc10 : Card := ⟨Suit.club, Rank.ten⟩
abbrev wcJ : Card := ⟨Suit.club, Rank.jack⟩
abbrev wcQ : Card := ⟨Suit.club, Rank.queen⟩
abbrev wcK : Card := ⟨Suit.club, Rank.king⟩

/-- The deal: p2 is the deadlock pile; the others are per-suit
descending runs (peel top-down as foundations climb); the deal's
stock holds the 23 foundation-gone cards plus ♥K (the state's cycle
keeps only ♥K). -/
def wdeal : Deal where
  piles := fun a => match a with
    | Anchor.p0 => [wc5]
    | Anchor.p1 => [wh6, wh5]
    | Anchor.p2 => [wh3, ws5, wh4]
    | Anchor.p3 => [wh10, wh9, wh8, wh7]
    | Anchor.p4 => [wc10, wc9, wc8, wc7, wc6]
    | Anchor.p5 => [wcK, wcQ, wcJ, whQ, whJ, ws6]
    | Anchor.p6 => [wsK, wsQ, wsJ, ws10, ws9, ws8, ws7]
  stock := [wdA, wd2, wd3, wd4, wd5, wd6, wd7, wd8, wd9, wd10, wdJ, wdQ, wdK,
            wsA, ws2, ws3, ws4, wcA, wc2, wc3, wc4, whA, wh2, whK]

/-- The visible matching: 27 edges — each pile's deal-adjacent chain,
with p2's chain rooted at the hidden ♥3 (the trigger edge) and p2's
anchor free (nothing sits on it; ♥3 is the boundary). -/
def wtop : Base → Option Card := fun b => match b with
  | .inl Anchor.p0 => some wc5
  | .inl Anchor.p1 => some wh6
  | .inl Anchor.p2 => none
  | .inl Anchor.p3 => some wh10
  | .inl Anchor.p4 => some wc10
  | .inl Anchor.p5 => some wcK
  | .inl Anchor.p6 => some wsK
  | .inr ⟨⟨Color.red, false⟩, Rank.three⟩ => some ws5
  | .inr ⟨⟨Color.black, false⟩, Rank.five⟩ => some wh4
  | .inr ⟨⟨Color.red, false⟩, Rank.six⟩ => some wh5
  | .inr ⟨⟨Color.red, false⟩, Rank.ten⟩ => some wh9
  | .inr ⟨⟨Color.red, false⟩, Rank.nine⟩ => some wh8
  | .inr ⟨⟨Color.red, false⟩, Rank.eight⟩ => some wh7
  | .inr ⟨⟨Color.black, true⟩, Rank.ten⟩ => some wc9
  | .inr ⟨⟨Color.black, true⟩, Rank.nine⟩ => some wc8
  | .inr ⟨⟨Color.black, true⟩, Rank.eight⟩ => some wc7
  | .inr ⟨⟨Color.black, true⟩, Rank.seven⟩ => some wc6
  | .inr ⟨⟨Color.black, true⟩, Rank.king⟩ => some wcQ
  | .inr ⟨⟨Color.black, true⟩, Rank.queen⟩ => some wcJ
  | .inr ⟨⟨Color.black, true⟩, Rank.jack⟩ => some whQ
  | .inr ⟨⟨Color.red, false⟩, Rank.queen⟩ => some whJ
  | .inr ⟨⟨Color.red, false⟩, Rank.jack⟩ => some ws6
  | .inr ⟨⟨Color.black, false⟩, Rank.king⟩ => some wsQ
  | .inr ⟨⟨Color.black, false⟩, Rank.queen⟩ => some wsJ
  | .inr ⟨⟨Color.black, false⟩, Rank.jack⟩ => some ws10
  | .inr ⟨⟨Color.black, false⟩, Rank.ten⟩ => some ws9
  | .inr ⟨⟨Color.black, false⟩, Rank.nine⟩ => some ws8
  | .inr ⟨⟨Color.black, false⟩, Rank.eight⟩ => some ws7
  | _ => none

/-- The inverse: each seated card's base (the inj proof's workhorse). -/
def wg : Card → Option Base := fun c => match c with
  | ⟨⟨Color.black, true⟩, Rank.five⟩ => some (Sum.inl Anchor.p0)
  | ⟨⟨Color.red, false⟩, Rank.six⟩ => some (Sum.inl Anchor.p1)
  | ⟨⟨Color.red, false⟩, Rank.ten⟩ => some (Sum.inl Anchor.p3)
  | ⟨⟨Color.black, true⟩, Rank.ten⟩ => some (Sum.inl Anchor.p4)
  | ⟨⟨Color.black, true⟩, Rank.king⟩ => some (Sum.inl Anchor.p5)
  | ⟨⟨Color.black, false⟩, Rank.king⟩ => some (Sum.inl Anchor.p6)
  | ⟨⟨Color.black, false⟩, Rank.five⟩ => some (Sum.inr wh3)
  | ⟨⟨Color.red, false⟩, Rank.four⟩ => some (Sum.inr ws5)
  | ⟨⟨Color.red, false⟩, Rank.five⟩ => some (Sum.inr wh6)
  | ⟨⟨Color.red, false⟩, Rank.nine⟩ => some (Sum.inr wh10)
  | ⟨⟨Color.red, false⟩, Rank.eight⟩ => some (Sum.inr wh9)
  | ⟨⟨Color.red, false⟩, Rank.seven⟩ => some (Sum.inr wh8)
  | ⟨⟨Color.black, true⟩, Rank.nine⟩ => some (Sum.inr wc10)
  | ⟨⟨Color.black, true⟩, Rank.eight⟩ => some (Sum.inr wc9)
  | ⟨⟨Color.black, true⟩, Rank.seven⟩ => some (Sum.inr wc8)
  | ⟨⟨Color.black, true⟩, Rank.six⟩ => some (Sum.inr wc7)
  | ⟨⟨Color.black, true⟩, Rank.queen⟩ => some (Sum.inr wcK)
  | ⟨⟨Color.black, true⟩, Rank.jack⟩ => some (Sum.inr wcQ)
  | ⟨⟨Color.red, false⟩, Rank.queen⟩ => some (Sum.inr wcJ)
  | ⟨⟨Color.red, false⟩, Rank.jack⟩ => some (Sum.inr whQ)
  | ⟨⟨Color.black, false⟩, Rank.six⟩ => some (Sum.inr whJ)
  | ⟨⟨Color.black, false⟩, Rank.queen⟩ => some (Sum.inr wsK)
  | ⟨⟨Color.black, false⟩, Rank.jack⟩ => some (Sum.inr wsQ)
  | ⟨⟨Color.black, false⟩, Rank.ten⟩ => some (Sum.inr wsJ)
  | ⟨⟨Color.black, false⟩, Rank.nine⟩ => some (Sum.inr ws10)
  | ⟨⟨Color.black, false⟩, Rank.eight⟩ => some (Sum.inr ws9)
  | ⟨⟨Color.black, false⟩, Rank.seven⟩ => some (Sum.inr ws8)
  | _ => none

/-- The seated card's base, by the inverse. -/
theorem wtop_wg {b : Base} {c : Card} (h : wtop b = some c) : wg c = some b := by
  cases b with
  | inl a =>
      cases a <;> simp only [wtop] at h <;>
        first
        | (subst h; rfl)
        | (injection h with hc; subst hc; rfl)
        | (simp at h)
  | inr d =>
      rcases d with ⟨⟨col, pr⟩, r⟩ <;> cases col <;> cases pr <;> cases r <;>
        simp only [wtop] at h <;>
        first
        | (subst h; rfl)
        | (injection h with hc; subst hc; rfl)
        | (simp at h)

/-- The board, with `inj` via the inverse. -/
def wboard : Board where
  topOf := wtop
  inj := by
    intro b₁ b₂ c h₁ h₂
    have hg₁ : wg c = some b₁ := wtop_wg h₁
    have hg₂ : wg c = some b₂ := wtop_wg h₂
    rw [hg₁] at hg₂
    exact Option.some.inj hg₂

def wstate : State where
  deal := wdeal
  board := wboard
  heights := fun s => match s with
    | ⟨Color.red, false⟩ => 2
    | ⟨Color.black, false⟩ => 4
    | ⟨Color.red, true⟩ => 13
    | ⟨Color.black, true⟩ => 4
  depths := fun a => match a with
    | Anchor.p2 => 1
    | _ => 0
  stock := ⟨[whK], 1⟩
  drawStep := 1

/-- The full game's winning play: park ♥4 on ♣5, reveal ♠5 (♥3 comes
up), then drain every pile top-down as the foundations climb, and
finally stack the lone stock card ♥K. -/
def wplay : List Move :=
  [Move.pilePile wh4 (Sum.inr wc5),
   Move.reveal ws5,
   Move.pileStack ws5, Move.pileStack wh3, Move.pileStack wh4, Move.pileStack wc5,
   Move.pileStack wh5, Move.pileStack wh6, Move.pileStack wh7, Move.pileStack wh8,
   Move.pileStack wh9, Move.pileStack wh10, Move.pileStack ws6,
   Move.pileStack whJ, Move.pileStack whQ,
   Move.pileStack wc6, Move.pileStack wc7, Move.pileStack wc8, Move.pileStack wc9,
   Move.pileStack wc10, Move.pileStack wcJ, Move.pileStack wcQ, Move.pileStack wcK,
   Move.pileStack ws7, Move.pileStack ws8, Move.pileStack ws9, Move.pileStack ws10,
   Move.pileStack wsJ, Move.pileStack wsQ, Move.pileStack wsK,
   Move.deckStack whK]

/-- info: true -/
#guard_msgs in
#eval (wstate.run wplay).isSome

/-- info: true -/
#guard_msgs in
#eval ((wstate.run wplay).getD wstate).isWin

/-- The full game wins: the 31-move play runs to a win (kernel-checked). -/
theorem wstate_solvable : wstate.solvableFrom :=
  ⟨wplay, (wstate.run wplay).getD wstate, by rfl, by rfl⟩

/-! ## The engine's deadlock -/

/-- The invariant along engine plays: hearts stay at height ≤ 2, the
p2 chain (♠5 on the hidden ♥3, ♥4 on ♠5) is frozen, ♥3 never gains a
base, and ♥3 never enters the stock. -/
def Inv (st : State) : Prop :=
  st.heights Suit.heart ≤ 2 ∧
  st.board.topOf (Sum.inr wh3) = some ws5 ∧
  st.board.topOf (Sum.inr ws5) = some wh4 ∧
  st.board.bottomOf wh3 = none ∧
  wh3 ∉ st.stock.cards

theorem wstate_inv : Inv wstate :=
  ⟨by decide, by rfl, by rfl, by decide, by decide⟩

/-- A card with heart suit and numeric rank 2 is exactly ♥3. -/
theorem heart3_of {c : Card} (hs : c.suit = Suit.heart) (hr : c.rank.toIdx = 2) :
    c = wh3 := by
  rcases c with ⟨s, r⟩
  subst hs
  cases r <;> simp_all [Rank.toIdx, wh3]

/-- The waste top is in the cycle. -/
theorem wprev_mem {c : Card} {cy : Cycle Card} (h : cy.prev = some c) : c ∈ cy.cards := by
  simp only [Cycle.prev] at h
  split at h
  · exact absurd h (by simp)
  · exact List.mem_iff_getElem?.mpr ⟨cy.cursor - 1, h⟩

theorem wbase_placed (d : Card) (b₀ : Base) (h : wtop b₀ = some d) :
    (wboard.bottomOf d).isSome = true := by
  rw [(Board.bottomOf_eq wboard d b₀).mpr h]; rfl

theorem wstate_isWin_heights {st : State} (h : st.isWin = true) (s : Suit) :
    st.heights s = 13 :=
  of_decide_eq_true ((List.all_eq_true.mp h) s s.mem_all)

/-- The invariant survives every engine move. -/
theorem inv_apply {st st' : State} (hI : Inv st) {m : Move} (heng : m.isEngine = true)
    (h : st.apply m = some st') : Inv st' := by
  obtain ⟨hH, hT3, hT5, hB3, hS3⟩ := hI
  cases m with
  | draw =>
      rw [apply_draw_iff] at h
      obtain ⟨rfl⟩ := h
      refine ⟨hH, hT3, hT5, hB3, ?_⟩
      show wh3 ∉ (st.stock.dealOnce st.drawStep).cards
      rw [Cycle.dealOnce_cards]
      exact hS3
  | reveal c =>
      rw [apply_reveal_iff] at h
      obtain ⟨ht, r, a, bd, hb, hp, ha, rfl⟩ := h
      obtain ⟨hfree, -⟩ := (Board.attach_eq_some_iff st.board (st.hiddenBase a) r).mp
        (by rw [ha]; simp)
      refine ⟨hH, ?_, ?_, ?_, hS3⟩
      · show bd.topOf (Sum.inr wh3) = some ws5
        by_cases hbb : st.hiddenBase a = Sum.inr wh3
        · rw [hbb] at hfree
          rw [hfree] at hT3
          exact absurd hT3 (by simp)
        · rw [Board.attach_topOf_ne _ _ _ ha (fun hh => hbb hh.symm)]
          exact hT3
      · show bd.topOf (Sum.inr ws5) = some wh4
        by_cases hbb : st.hiddenBase a = Sum.inr ws5
        · rw [hbb] at hfree
          rw [hfree] at hT5
          exact absurd hT5 (by simp)
        · rw [Board.attach_topOf_ne _ _ _ ha (fun hh => hbb hh.symm)]
          exact hT5
      · show bd.bottomOf wh3 = none
        refine (Board.bottomOf_eq_none _ _).mpr (fun b' hb' => ?_)
        by_cases hbb : b' = st.hiddenBase a
        · rw [hbb, Board.attach_topOf _ _ _ ha] at hb'
          rw [Option.some.injEq] at hb'
          -- the revealed card would be ♥3: its trigger is ♠5, which is covered
          rw [hb'] at hb
          rw [show Sum.inr wh3 = Sum.inr wh3 from rfl] at hb
          have hc5 : c = ws5 := by
            have := (Board.bottomOf_eq st.board c (Sum.inr wh3)).mp hb
            rw [hT3] at this
            exact Option.some.inj this.symm
          rw [hc5] at ht
          rw [hT5] at ht
          exact absurd ht (by simp)
        · rw [Board.attach_topOf_ne _ _ _ ha hbb] at hb'
          exact (Board.bottomOf_eq_none _ _).mp hB3 b' hb'
  | deckPile c b =>
      rw [apply_deckPile_iff] at h
      obtain ⟨hp, hcp, bd, hatt, rfl⟩ := h
      obtain ⟨hfree, -⟩ := (Board.attach_eq_some_iff st.board b c).mp (by rw [hatt]; simp)
      have hcne : c ≠ wh3 := fun hcon => hS3 (by rw [← hcon]; exact wprev_mem hp)
      refine ⟨hH, ?_, ?_, ?_, ?_⟩
      · show bd.topOf (Sum.inr wh3) = some ws5
        by_cases hbb : b = Sum.inr wh3
        · rw [hbb] at hfree; rw [hfree] at hT3; exact absurd hT3 (by simp)
        · rw [Board.attach_topOf_ne _ _ _ hatt (fun hh => hbb hh.symm)]; exact hT3
      · show bd.topOf (Sum.inr ws5) = some wh4
        by_cases hbb : b = Sum.inr ws5
        · rw [hbb] at hfree; rw [hfree] at hT5; exact absurd hT5 (by simp)
        · rw [Board.attach_topOf_ne _ _ _ hatt (fun hh => hbb hh.symm)]; exact hT5
      · show bd.bottomOf wh3 = none
        refine (Board.bottomOf_eq_none _ _).mpr (fun b' hb' => ?_)
        by_cases hbb : b' = b
        · rw [hbb, Board.attach_topOf _ _ _ hatt] at hb'
          rw [Option.some.injEq] at hb'
          exact hcne hb'
        · rw [Board.attach_topOf_ne _ _ _ hatt hbb] at hb'
          exact (Board.bottomOf_eq_none _ _).mp hB3 b' hb'
      · show wh3 ∉ (st.stock.removeAt (st.stock.cursor - 1)).cards
        exact fun hmem => hS3 (Cycle.mem_removeIdx _ _ hmem)
  | deckStack c =>
      rw [apply_deckStack_iff] at h
      obtain ⟨hp, hrk, rfl⟩ := h
      refine ⟨?_, hT3, hT5, hB3, ?_⟩
      · by_cases hch : c.suit = Suit.heart
        · show (if Suit.heart = c.suit then st.heights Suit.heart + 1
            else st.heights Suit.heart) ≤ 2
          rw [if_pos (by rw [← hch])]
          have hrk2 : c.rank.toIdx = st.heights Suit.heart := by rw [hrk, hch]
          rcases Nat.lt_or_ge c.rank.toIdx 2 with hlt | hge
          · omega
          · have h2 : c.rank.toIdx = 2 := by omega
            have hc3 : c = wh3 := heart3_of hch h2
            have hmem := wprev_mem hp
            rw [hc3] at hmem
            exact absurd hmem hS3
        · show (if Suit.heart = c.suit then st.heights Suit.heart + 1
            else st.heights Suit.heart) ≤ 2
          rw [if_neg (fun hcon => hch hcon.symm)]
          exact hH
      · show wh3 ∉ (st.stock.removeAt (st.stock.cursor - 1)).cards
        exact fun hmem => hS3 (Cycle.mem_removeIdx _ _ hmem)
  | pileStack c =>
      rw [apply_pileStack_iff] at h
      obtain ⟨ht, b, hb, hrk, rfl⟩ := h
      refine ⟨?_, ?_, ?_, ?_, hS3⟩
      · by_cases hch : c.suit = Suit.heart
        · show (if Suit.heart = c.suit then st.heights Suit.heart + 1
            else st.heights Suit.heart) ≤ 2
          rw [if_pos (by rw [← hch])]
          have hrk2 : c.rank.toIdx = st.heights Suit.heart := by rw [hrk, hch]
          rcases Nat.lt_or_ge c.rank.toIdx 2 with hlt | hge
          · omega
          · have h2 : c.rank.toIdx = 2 := by omega
            have hc3 : c = wh3 := heart3_of hch h2
            rw [hc3] at hb
            exact absurd (hb.symm.trans hB3) (by simp)
        · show (if Suit.heart = c.suit then st.heights Suit.heart + 1
            else st.heights Suit.heart) ≤ 2
          rw [if_neg (fun hcon => hch hcon.symm)]
          exact hH
      · show (st.board.detach b).topOf (Sum.inr wh3) = some ws5
        by_cases hbb : b = Sum.inr wh3
        · rw [hbb] at hb
          have hc5 : c = ws5 := by
            have := (Board.bottomOf_eq st.board c (Sum.inr wh3)).mp hb
            rw [hT3] at this
            exact Option.some.inj this.symm
          rw [hc5] at ht
          rw [hT5] at ht
          exact absurd ht (by simp)
        · rw [Board.detach_topOf_ne _ _ _ (fun hh => hbb hh.symm)]; exact hT3
      · show (st.board.detach b).topOf (Sum.inr ws5) = some wh4
        by_cases hbb : b = Sum.inr ws5
        · rw [hbb] at hb
          have hc4 : c = wh4 := by
            have := (Board.bottomOf_eq st.board c (Sum.inr ws5)).mp hb
            rw [hT5] at this
            exact Option.some.inj this.symm
          rw [hc4] at hrk
          have hrk' : (3 : Nat) = st.heights Suit.heart := hrk
          exact absurd hrk' (by omega)
        · rw [Board.detach_topOf_ne _ _ _ (fun hh => hbb hh.symm)]; exact hT5
      · show (st.board.detach b).bottomOf wh3 = none
        refine (Board.bottomOf_eq_none _ _).mpr (fun b' hb' => ?_)
        by_cases hbb : b' = b
        · rw [hbb, Board.detach_topOf] at hb'
          exact absurd hb' (by simp)
        · rw [Board.detach_topOf_ne _ _ _ hbb] at hb'
          exact (Board.bottomOf_eq_none _ _).mp hB3 b' hb'
  | stackPile c b =>
      rw [apply_stackPile_iff] at h
      obtain ⟨hrk, hcp, bd, hatt, rfl⟩ := h
      obtain ⟨hfree, -⟩ := (Board.attach_eq_some_iff st.board b c).mp (by rw [hatt]; simp)
      have hcne : c ≠ wh3 := by
        intro hcon
        rw [hcon] at hrk
        have : (3 : Nat) = st.heights Suit.heart := hrk
        omega
      refine ⟨?_, ?_, ?_, ?_, hS3⟩
      · by_cases hch : c.suit = Suit.heart
        · show (if Suit.heart = c.suit then st.heights Suit.heart - 1
            else st.heights Suit.heart) ≤ 2
          rw [if_pos (by rw [← hch])]
          omega
        · show (if Suit.heart = c.suit then st.heights Suit.heart - 1
            else st.heights Suit.heart) ≤ 2
          rw [if_neg (fun hcon => hch hcon.symm)]
          exact hH
      · show bd.topOf (Sum.inr wh3) = some ws5
        by_cases hbb : b = Sum.inr wh3
        · rw [hbb] at hfree; rw [hfree] at hT3; exact absurd hT3 (by simp)
        · rw [Board.attach_topOf_ne _ _ _ hatt (fun hh => hbb hh.symm)]; exact hT3
      · show bd.topOf (Sum.inr ws5) = some wh4
        by_cases hbb : b = Sum.inr ws5
        · rw [hbb] at hfree; rw [hfree] at hT5; exact absurd hT5 (by simp)
        · rw [Board.attach_topOf_ne _ _ _ hatt (fun hh => hbb hh.symm)]; exact hT5
      · show bd.bottomOf wh3 = none
        refine (Board.bottomOf_eq_none _ _).mpr (fun b' hb' => ?_)
        by_cases hbb : b' = b
        · rw [hbb, Board.attach_topOf _ _ _ hatt] at hb'
          rw [Option.some.injEq] at hb'
          exact hcne hb'
        · rw [Board.attach_topOf_ne _ _ _ hatt hbb] at hb'
          exact (Board.bottomOf_eq_none _ _).mp hB3 b' hb'
  | pilePile c b => simp [Move.isEngine] at heng

/-- The invariant holds along every engine play from the witness. -/
theorem inv_run : ∀ (play : List Move) (st₀ st : State), Inv st₀ →
    (∀ m ∈ play, m.isEngine = true) → st₀.run play = some st → Inv st := by
  intro play
  induction play with
  | nil =>
      intro st₀ st hI _ h
      have hnil : st₀.run ([] : List Move) = some st₀ := rfl
      rw [hnil] at h
      have he := Option.some.inj h
      rw [he] at hI
      exact hI
  | cons m ms ih =>
      intro st₀ st hI heng h
      simp only [State.run] at h
      cases hap : st₀.apply m with
      | none =>
          rw [hap] at h
          exact absurd h (by simp)
      | some s' =>
          rw [hap] at h
          exact ih s' st (inv_apply hI (heng m (by simp)) hap)
            (fun mm hmm => heng mm (by simp [hmm])) h

/-- The engine cannot win from the witness: hearts are frozen at ≤ 2. -/
theorem wstate_not_engine : ¬ wstate.solvableEngine := by
  intro hsol
  obtain ⟨play, heng, st, hrun, hwin⟩ := hsol
  have hI := inv_run play wstate st wstate_inv heng hrun
  have hH := hI.1
  have h13 := wstate_isWin_heights hwin Suit.heart
  omega

/-! ## The witness is well-formed -/

theorem wdeal_wf : wdeal.WF := by
  refine ⟨?_, ?_, ?_⟩
  · intro a; cases a <;> rfl
  · rfl
  · intro i j hi hj heq
    have h52 : ((Anchor.all.flatMap wdeal.piles) ++ wdeal.stock).length = 52 := by rfl
    rw [h52] at hi hj
    have hall : ∀ i ∈ List.range 52, ∀ j ∈ List.range 52,
        ((Anchor.all.flatMap wdeal.piles) ++ wdeal.stock)[i]? =
        ((Anchor.all.flatMap wdeal.piles) ++ wdeal.stock)[j]? → i = j := by decide
    exact hall i (List.mem_range.mpr hi) j (List.mem_range.mpr hj) heq

/-- A base with no top cannot witness an edge. -/
theorem wtop_none_of {b : Base} {c : Card} (hb : wstate.board.topOf b = some c)
    (h : wstate.board.topOf b = none) : False := by
  rw [h] at hb
  exact absurd hb (by simp)
theorem wstate_board_edges : wstate.board_edges := by
  intro b c hb
  cases b with
  | inl a =>
      cases a with
      | p0 =>
          have hc : c = wc5 :=
            Option.some.inj (hb.symm.trans (show wtop (Sum.inl Anchor.p0) = some wc5 from rfl))
          subst hc
          exact ⟨(Board.bottomOf_eq _ _ _).mpr hb, Or.inr rfl⟩
      | p1 =>
          have hc : c = wh6 :=
            Option.some.inj (hb.symm.trans (show wtop (Sum.inl Anchor.p1) = some wh6 from rfl))
          subst hc
          exact ⟨(Board.bottomOf_eq _ _ _).mpr hb, Or.inr rfl⟩
      | p2 => exact (wtop_none_of hb (by rfl)).elim
      | p3 =>
          have hc : c = wh10 :=
            Option.some.inj (hb.symm.trans (show wtop (Sum.inl Anchor.p3) = some wh10 from rfl))
          subst hc
          exact ⟨(Board.bottomOf_eq _ _ _).mpr hb, Or.inr rfl⟩
      | p4 =>
          have hc : c = wc10 :=
            Option.some.inj (hb.symm.trans (show wtop (Sum.inl Anchor.p4) = some wc10 from rfl))
          subst hc
          exact ⟨(Board.bottomOf_eq _ _ _).mpr hb, Or.inr rfl⟩
      | p5 =>
          have hc : c = wcK :=
            Option.some.inj (hb.symm.trans (show wtop (Sum.inl Anchor.p5) = some wcK from rfl))
          subst hc
          exact ⟨(Board.bottomOf_eq _ _ _).mpr hb, Or.inl rfl⟩
      | p6 =>
          have hc : c = wsK :=
            Option.some.inj (hb.symm.trans (show wtop (Sum.inl Anchor.p6) = some wsK from rfl))
          subst hc
          exact ⟨(Board.bottomOf_eq _ _ _).mpr hb, Or.inl rfl⟩
  | inr d =>
      rcases d with ⟨⟨col, pr⟩, r⟩
      cases col with
      | red =>
          cases pr with
          | false =>
              cases r with
              | three =>
                  have hc : c = ws5 :=
                    Option.some.inj (hb.symm.trans
                      (show wtop (Sum.inr wh3) = some ws5 from rfl))
                  subst hc
                  exact ⟨(Board.bottomOf_eq _ _ _).mpr hb,
                    Or.inl ⟨Anchor.p2, [], [wh4], by rfl, Or.inl ⟨Anchor.p2, by rfl⟩⟩⟩
              | six =>
                  have hc : c = wh5 :=
                    Option.some.inj (hb.symm.trans
                      (show wtop (Sum.inr wh6) = some wh5 from rfl))
                  subst hc
                  exact ⟨(Board.bottomOf_eq _ _ _).mpr hb,
                    Or.inl ⟨Anchor.p1, [], [], by rfl,
                      Or.inr (wbase_placed wh6 (Sum.inl Anchor.p1) (by rfl))⟩⟩
              | ten =>
                  have hc : c = wh9 :=
                    Option.some.inj (hb.symm.trans
                      (show wtop (Sum.inr wh10) = some wh9 from rfl))
                  subst hc
                  exact ⟨(Board.bottomOf_eq _ _ _).mpr hb,
                    Or.inl ⟨Anchor.p3, [], [wh8, wh7], by rfl,
                      Or.inr (wbase_placed wh10 (Sum.inl Anchor.p3) (by rfl))⟩⟩
              | nine =>
                  have hc : c = wh8 :=
                    Option.some.inj (hb.symm.trans
                      (show wtop (Sum.inr wh9) = some wh8 from rfl))
                  subst hc
                  exact ⟨(Board.bottomOf_eq _ _ _).mpr hb,
                    Or.inl ⟨Anchor.p3, [wh10], [wh7], by rfl,
                      Or.inr (wbase_placed wh9 (Sum.inr wh10) (by rfl))⟩⟩
              | eight =>
                  have hc : c = wh7 :=
                    Option.some.inj (hb.symm.trans
                      (show wtop (Sum.inr wh8) = some wh7 from rfl))
                  subst hc
                  exact ⟨(Board.bottomOf_eq _ _ _).mpr hb,
                    Or.inl ⟨Anchor.p3, [wh10, wh9], [], by rfl,
                      Or.inr (wbase_placed wh8 (Sum.inr wh9) (by rfl))⟩⟩
              | queen =>
                  have hc : c = whJ :=
                    Option.some.inj (hb.symm.trans
                      (show wtop (Sum.inr whQ) = some whJ from rfl))
                  subst hc
                  exact ⟨(Board.bottomOf_eq _ _ _).mpr hb,
                    Or.inl ⟨Anchor.p5, [wcK, wcQ, wcJ], [ws6], by rfl,
                      Or.inr (wbase_placed whQ (Sum.inr wcJ) (by rfl))⟩⟩
              | jack =>
                  have hc : c = ws6 :=
                    Option.some.inj (hb.symm.trans
                      (show wtop (Sum.inr whJ) = some ws6 from rfl))
                  subst hc
                  exact ⟨(Board.bottomOf_eq _ _ _).mpr hb,
                    Or.inl ⟨Anchor.p5, [wcK, wcQ, wcJ, whQ], [], by rfl,
                      Or.inr (wbase_placed whJ (Sum.inr whQ) (by rfl))⟩⟩
              | ace | two | four | five | seven | king => exact (wtop_none_of hb (by rfl)).elim
          | true => cases r <;> exact (wtop_none_of hb (by rfl)).elim
      | black =>
          cases pr with
          | false =>
              cases r with
              | five =>
                  have hc : c = wh4 :=
                    Option.some.inj (hb.symm.trans
                      (show wtop (Sum.inr ws5) = some wh4 from rfl))
                  subst hc
                  exact ⟨(Board.bottomOf_eq _ _ _).mpr hb,
                    Or.inl ⟨Anchor.p2, [wh3], [], by rfl,
                      Or.inr (wbase_placed ws5 (Sum.inr wh3) (by rfl))⟩⟩
              | king =>
                  have hc : c = wsQ :=
                    Option.some.inj (hb.symm.trans
                      (show wtop (Sum.inr wsK) = some wsQ from rfl))
                  subst hc
                  exact ⟨(Board.bottomOf_eq _ _ _).mpr hb,
                    Or.inl ⟨Anchor.p6, [], [wsJ, ws10, ws9, ws8, ws7], by rfl,
                      Or.inr (wbase_placed wsK (Sum.inl Anchor.p6) (by rfl))⟩⟩
              | queen =>
                  have hc : c = wsJ :=
                    Option.some.inj (hb.symm.trans
                      (show wtop (Sum.inr wsQ) = some wsJ from rfl))
                  subst hc
                  exact ⟨(Board.bottomOf_eq _ _ _).mpr hb,
                    Or.inl ⟨Anchor.p6, [wsK], [ws10, ws9, ws8, ws7], by rfl,
                      Or.inr (wbase_placed wsQ (Sum.inr wsK) (by rfl))⟩⟩
              | jack =>
                  have hc : c = ws10 :=
                    Option.some.inj (hb.symm.trans
                      (show wtop (Sum.inr wsJ) = some ws10 from rfl))
                  subst hc
                  exact ⟨(Board.bottomOf_eq _ _ _).mpr hb,
                    Or.inl ⟨Anchor.p6, [wsK, wsQ], [ws9, ws8, ws7], by rfl,
                      Or.inr (wbase_placed wsJ (Sum.inr wsQ) (by rfl))⟩⟩
              | ten =>
                  have hc : c = ws9 :=
                    Option.some.inj (hb.symm.trans
                      (show wtop (Sum.inr ws10) = some ws9 from rfl))
                  subst hc
                  exact ⟨(Board.bottomOf_eq _ _ _).mpr hb,
                    Or.inl ⟨Anchor.p6, [wsK, wsQ, wsJ], [ws8, ws7], by rfl,
                      Or.inr (wbase_placed ws10 (Sum.inr wsJ) (by rfl))⟩⟩
              | nine =>
                  have hc : c = ws8 :=
                    Option.some.inj (hb.symm.trans
                      (show wtop (Sum.inr ws9) = some ws8 from rfl))
                  subst hc
                  exact ⟨(Board.bottomOf_eq _ _ _).mpr hb,
                    Or.inl ⟨Anchor.p6, [wsK, wsQ, wsJ, ws10], [ws7], by rfl,
                      Or.inr (wbase_placed ws9 (Sum.inr ws10) (by rfl))⟩⟩
              | eight =>
                  have hc : c = ws7 :=
                    Option.some.inj (hb.symm.trans
                      (show wtop (Sum.inr ws8) = some ws7 from rfl))
                  subst hc
                  exact ⟨(Board.bottomOf_eq _ _ _).mpr hb,
                    Or.inl ⟨Anchor.p6, [wsK, wsQ, wsJ, ws10, ws9], [], by rfl,
                      Or.inr (wbase_placed ws8 (Sum.inr ws9) (by rfl))⟩⟩
              | ace | two | three | four | six | seven => exact (wtop_none_of hb (by rfl)).elim
          | true =>
              cases r with
              | ten =>
                  have hc : c = wc9 :=
                    Option.some.inj (hb.symm.trans
                      (show wtop (Sum.inr wc10) = some wc9 from rfl))
                  subst hc
                  exact ⟨(Board.bottomOf_eq _ _ _).mpr hb,
                    Or.inl ⟨Anchor.p4, [], [wc8, wc7, wc6], by rfl,
                      Or.inr (wbase_placed wc10 (Sum.inl Anchor.p4) (by rfl))⟩⟩
              | nine =>
                  have hc : c = wc8 :=
                    Option.some.inj (hb.symm.trans
                      (show wtop (Sum.inr wc9) = some wc8 from rfl))
                  subst hc
                  exact ⟨(Board.bottomOf_eq _ _ _).mpr hb,
                    Or.inl ⟨Anchor.p4, [wc10], [wc7, wc6], by rfl,
                      Or.inr (wbase_placed wc9 (Sum.inr wc10) (by rfl))⟩⟩
              | eight =>
                  have hc : c = wc7 :=
                    Option.some.inj (hb.symm.trans
                      (show wtop (Sum.inr wc8) = some wc7 from rfl))
                  subst hc
                  exact ⟨(Board.bottomOf_eq _ _ _).mpr hb,
                    Or.inl ⟨Anchor.p4, [wc10, wc9], [wc6], by rfl,
                      Or.inr (wbase_placed wc8 (Sum.inr wc9) (by rfl))⟩⟩
              | seven =>
                  have hc : c = wc6 :=
                    Option.some.inj (hb.symm.trans
                      (show wtop (Sum.inr wc7) = some wc6 from rfl))
                  subst hc
                  exact ⟨(Board.bottomOf_eq _ _ _).mpr hb,
                    Or.inl ⟨Anchor.p4, [wc10, wc9, wc8], [], by rfl,
                      Or.inr (wbase_placed wc7 (Sum.inr wc8) (by rfl))⟩⟩
              | king =>
                  have hc : c = wcQ :=
                    Option.some.inj (hb.symm.trans
                      (show wtop (Sum.inr wcK) = some wcQ from rfl))
                  subst hc
                  exact ⟨(Board.bottomOf_eq _ _ _).mpr hb,
                    Or.inl ⟨Anchor.p5, [], [wcJ, whQ, whJ, ws6], by rfl,
                      Or.inr (wbase_placed wcK (Sum.inl Anchor.p5) (by rfl))⟩⟩
              | queen =>
                  have hc : c = wcJ :=
                    Option.some.inj (hb.symm.trans
                      (show wtop (Sum.inr wcQ) = some wcJ from rfl))
                  subst hc
                  exact ⟨(Board.bottomOf_eq _ _ _).mpr hb,
                    Or.inl ⟨Anchor.p5, [wcK], [whQ, whJ, ws6], by rfl,
                      Or.inr (wbase_placed wcQ (Sum.inr wcK) (by rfl))⟩⟩
              | jack =>
                  have hc : c = whQ :=
                    Option.some.inj (hb.symm.trans
                      (show wtop (Sum.inr wcJ) = some whQ from rfl))
                  subst hc
                  exact ⟨(Board.bottomOf_eq _ _ _).mpr hb,
                    Or.inl ⟨Anchor.p5, [wcK, wcQ], [whJ, ws6], by rfl,
                      Or.inr (wbase_placed wcJ (Sum.inr wcQ) (by rfl))⟩⟩
              | ace | two | three | four | five | six => exact (wtop_none_of hb (by rfl)).elim

/-- Only ♥3 is hidden anywhere in the witness. -/
theorem whidden_only {c : Card} {a : Anchor} (hcm : c ∈ wstate.hidden a) : c = wh3 := by
  cases a <;> simp [State.hidden, wstate, wdeal] at hcm <;> exact hcm

theorem wstate_vis_off_cycle : wstate.vis_off_cycle := by
  intro c hc
  have hex : ∃ b, wtop b = some c := by
    simp only [State.isVis] at hc
    cases hbot : wstate.board.bottomOf c with
    | none =>
        rw [hbot] at hc
        exact absurd hc (by simp)
    | some b => exact ⟨b, (Board.bottomOf_eq _ _ _).mp hbot⟩
  obtain ⟨b, hb⟩ := hex
  have hwg : wg c = some b := wtop_wg hb
  have hne : c ≠ whK := by
    intro hcon
    rw [hcon] at hwg
    have hnone : wg whK = none := by rfl
    rw [hnone] at hwg
    exact absurd hwg (by simp)
  exact Cycle.posOf_eq_none (fun hmem => hne (List.mem_singleton.mp hmem))

theorem wstate_found_off_cycle : wstate.found_off_cycle := by
  intro c hc
  have hne : c ≠ whK := by
    intro hcon
    rw [hcon] at hc
    exact absurd hc (by decide)
  exact Cycle.posOf_eq_none (fun hmem => hne (List.mem_singleton.mp hmem))

theorem wstate_founds_gone : wstate.founds_gone := by
  intro c hc
  rcases c with ⟨⟨col, pr⟩, r⟩ <;> cases col <;> cases pr <;> cases r
  all_goals first
  | exact absurd hc (by decide)
  | refine ⟨by decide, by decide, ?_⟩
    intro a hcm
    have h3 : _ = wh3 := whidden_only hcm
    rw [h3] at hc
    exact absurd hc (by decide)

theorem wstate_vis_not_hidden : wstate.vis_not_hidden := by
  intro c hc a hcm
  have h3 : c = wh3 := whidden_only hcm
  rw [h3] at hc
  exact absurd hc (by decide)

theorem wstate_wf : wstate.WF := by
  refine ⟨wdeal_wf, ?_, wstate_board_edges, wstate_vis_off_cycle, wstate_found_off_cycle,
    wstate_founds_gone, wstate_vis_not_hidden, ?_, ?_, ?_, ?_⟩
  · intro a; cases a <;> decide
  · intro s; rcases s with ⟨col, pr⟩ <;> cases col <;> cases pr <;> decide
  · exact (Nat.le_refl 1 : wstate.cursor_le)
  · exact (Nat.zero_lt_one : wstate.step_pos)
  · refine ⟨?_, ?_⟩
    · intro i j hi hj heq
      have h1 : wstate.stock.cards.length = 1 := by rfl
      rw [h1] at hi hj
      have hall : ∀ i ∈ List.range 1, ∀ j ∈ List.range 1,
          wstate.stock.cards[i]? = wstate.stock.cards[j]? → i = j := by decide
      exact hall i (List.mem_range.mpr hi) j (List.mem_range.mpr hj) heq
    · intro c hcm
      have : c = whK := List.mem_singleton.mp hcm
      rw [this]
      decide

/-! ## The refutation (HISTORICAL)

`solvable_engine_iff` — the no-pile-to-pile iff, DELETED from Move.lean
on 2026-09-13 in the laundering disposal — was refuted by exactly the
facts above: `wstate` is WF (`wstate_wf`) and wins in the full game
(`wstate_solvable`, the 31-move park-reveal-drain play) while the
engine is doomed (`wstate_not_engine` — hearts frozen at ≤ 2, the
reveal-deadlock that only `pilePile` breaks).  The deleted statement
is archived as fenced text in FARM.md's REFUTED section (item 1); its
easy leg survives as the proven `solvable_of_engine` (Move.lean), and
the initial-states repair direction is scaffolded in
Klondike/Restriction.lean.  The former `engine_iff_refuted` corollary
(deriving the negated ∀-form) has been removed so that this file cites
no deleted constant — the countermodel facts stand alone. -/


end EngineWitness
