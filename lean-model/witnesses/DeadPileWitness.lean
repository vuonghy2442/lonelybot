import Klondike.Dominance

/-!
# The dead-pile witness — `safe_pileStack_dominant` is FALSE as staged

`reveal c` seats the hidden boundary card under `c` *while `c` still
sits on it* (`applyReveal` demands `bottomOf c = some (inr r)` with
`r = topHidden a`).  Once `c` leaves the pile without revealing, the
boundary card can never be sat on again (`canPlace` demands a visible
base; `reveal` demands a visible card on the boundary), so it can
never be revealed, never reach the foundation, and `heights` can never
pass its rank: the pile is dead and any state containing it is
unsolvable.

The witness state: ♦K is safe (`safeToStack` computes true), legally
`pileStack`able, and the SOLE visible card of pile p1, sitting on the
hidden boundary ♣K.  The state is WF and three moves from the win
(reveal ♦K; stack ♦K; stack ♣K).  Stacking ♦K first kills ♣K — the
successor is unsolvable — so `dominantAt` fails.
-/

namespace DeadPile

/-- Spades. -/
private def S (r : Rank) : Card := ⟨Suit.spade, r⟩
/-- Hearts. -/
private def H (r : Rank) : Card := ⟨Suit.heart, r⟩
/-- Diamonds. -/
private def D (r : Rank) : Card := ⟨Suit.diamond, r⟩
/-- Clubs. -/
private def C (r : Rank) : Card := ⟨Suit.club, r⟩

/-- The witness deal: all spades and hearts stacked on the foundations
already, ♦A..♦Q and ♣A..♣Q as the deal's stock, and pile p1 holding
exactly the two kings — ♣K hidden under the visible ♦K. -/
private def wDeal : Deal where
  piles := fun a =>
    match a with
    | .p0 => [S .ace]
    | .p1 => [C .king, D .king]
    | .p2 => [H .ace, S .two, H .two]
    | .p3 => [S .three, H .three, S .four, H .four]
    | .p4 => [S .five, H .five, S .six, H .six, S .seven]
    | .p5 => [H .seven, S .eight, H .eight, S .nine, H .nine, S .ten]
    | .p6 => [H .ten, S .jack, H .jack, S .queen, H .queen, S .king, H .king]
  stock := [D .ace, D .two, D .three, D .four, D .five, D .six, D .seven, D .eight,
            D .nine, D .ten, D .jack, D .queen,
            C .ace, C .two, C .three, C .four, C .five, C .six, C .seven, C .eight,
            C .nine, C .ten, C .jack, C .queen]

/-- The only visible card: ♦K, seated on the hidden ♣K. -/
private def wTop : Base → Option Card :=
  fun b => if b = Sum.inr (C .king) then some (D .king) else none

private theorem wTop_some {b : Base} {c : Card} (h : wTop b = some c) :
    c = D .king ∧ b = Sum.inr (C .king) := by
  by_cases hbc : b = Sum.inr (C .king)
  · refine ⟨?_, hbc⟩
    simp only [wTop, if_pos hbc, Option.some.injEq] at h
    exact h.symm
  · simp only [wTop, if_neg hbc] at h
    exact absurd h (by simp)

private theorem wTop_inj : ∀ (b₁ b₂ : Base) (c : Card),
    wTop b₁ = some c → wTop b₂ = some c → b₁ = b₂ := by
  intro b₁ b₂ c h₁ h₂
  rw [(wTop_some h₁).2, (wTop_some h₂).2]

/-- The witness state: ♠/♥ complete (13), ♦/♣ at 12, pile p1 at depth
1, empty stock, draw step 1. -/
private def wState : State where
  deal := wDeal
  board := { topOf := wTop, inj := wTop_inj }
  heights := fun s => if s = Suit.diamond ∨ s = Suit.club then 12 else 13
  depths := fun a => if a = Anchor.p1 then 1 else 0
  stock := ⟨[], 0⟩
  drawStep := 1

/-! ## Small inversion helpers -/

/-- A `canPlace` onto a card base demands that card visible. -/
private theorem canPlace_inr_isVis {st : State} {x c : Card}
    (h : st.canPlace x (Sum.inr c) = true) : st.isVis c = true := by
  have h2 : (decide (st.board.topOf (Sum.inr c) = none) &&
      (st.isVis c && canSitOn x c)) = true := h
  rw [Bool.and_eq_true, Bool.and_eq_true] at h2
  exact h2.2.1

/-- A `canMoveRun` onto a card base demands that card visible. -/
private theorem canMoveRun_inr_isVis {st : State} {x c : Card}
    (h : st.canMoveRun x (Sum.inr c) = true) : st.isVis c = true := by
  have h2 : (st.canPlace x (Sum.inr c) &&
      !(st.board.aboveOf x).contains c) = true := h
  rw [Bool.and_eq_true] at h2
  exact canPlace_inr_isVis h2.1

/-- The waste top is in the stock. -/
private theorem prev_mem {s : State} {x : Card} (hp : s.stock.prev = some x) :
    x ∈ s.stock.cards := by
  simp only [Cycle.prev] at hp
  split at hp
  · exact absurd hp (by simp)
  · exact List.mem_iff_getElem?.mpr ⟨s.stock.cursor - 1, hp⟩

/-- The pile a pileOfTopHidden points at really has `r` as boundary. -/
private theorem pileOfTopHidden_topHidden {s : State} {r : Card} {a : Anchor}
    (hp : s.pileOfTopHidden r = some a) : s.topHidden a = some r :=
  of_decide_eq_true ((findFirst_mem _ _ _ hp).2)

/-- A card base under a boundary belongs to that pile's deal slice. -/
private theorem hiddenBase_piles {s : State} {a : Anchor} {d : Card}
    (h : s.hiddenBase a = Sum.inr d) : d ∈ s.deal.piles a := by
  simp only [State.hiddenBase] at h
  cases hd : ((s.hidden a).reverse.drop 1).head? with
  | none =>
      rw [hd] at h
      exact absurd h (by simp)
  | some d' =>
      have h2 : (Sum.inr d' : Base) = Sum.inr d := by rw [hd] at h; exact h
      have hdd : d' = d := by injection h2
      rw [hdd] at hd
      cases hgt : (s.hidden a).getLast? with
      | none =>
          exfalso
          cases hs : s.hidden a with
          | nil => rw [hs] at hd; simp at hd
          | cons y t => rw [hs] at hgt; simp at hgt
      | some r =>
          obtain ⟨t, rest, hadj⟩ := hidden_parent_dealt hd hgt
          rw [hadj]
          simp

/-! ## The witness is WF -/

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
  refine ⟨wDeal_wf, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a
    cases a <;> decide
  · intro b c htop
    obtain ⟨hc, hb⟩ := wTop_some htop
    subst hc
    subst hb
    refine ⟨(Board.bottomOf_eq _ _ _).mpr htop, ?_⟩
    left
    exact ⟨Anchor.p1, [], [], rfl, Or.inl ⟨Anchor.p1, by decide⟩⟩
  · intro c _
    rfl
  · intro c _
    rfl
  · intro c hc
    have hnd : c ≠ D .king := by
      intro h
      rw [h] at hc
      exact absurd hc (by decide)
    refine ⟨?_, rfl, ?_⟩
    · cases hb : wState.board.bottomOf c with
      | none => simp [State.isVis, hb]
      | some b => exact absurd ((wTop_some ((Board.bottomOf_eq _ _ _).mp hb)).1) hnd
    · intro a hca
      cases a with
      | p1 =>
          have h1 : c ∈ [C .king] := hca
          rcases List.mem_cons.mp h1 with h | h
          · rw [h] at hc
            exact absurd hc (by decide)
          · exact absurd h (by simp)
      | p0 =>
          have h1 : c ∈ ([] : List Card) := hca
          exact nomatch h1
      | p2 =>
          have h1 : c ∈ ([] : List Card) := hca
          exact nomatch h1
      | p3 =>
          have h1 : c ∈ ([] : List Card) := hca
          exact nomatch h1
      | p4 =>
          have h1 : c ∈ ([] : List Card) := hca
          exact nomatch h1
      | p5 =>
          have h1 : c ∈ ([] : List Card) := hca
          exact nomatch h1
      | p6 =>
          have h1 : c ∈ ([] : List Card) := hca
          exact nomatch h1
  · intro c hc a hca
    have hck : c = D .king := by
      cases hb : wState.board.bottomOf c with
      | none => simp [State.isVis, hb] at hc
      | some b => exact (wTop_some ((Board.bottomOf_eq _ _ _).mp hb)).1
    rw [hck] at hca
    cases a with
    | p1 =>
        have h1 : D .king ∈ [C .king] := hca
        rcases List.mem_cons.mp h1 with h | h
        · exact absurd h (by decide)
        · exact absurd h (by simp)
    | p0 =>
        have h1 : D .king ∈ ([] : List Card) := hca
        exact nomatch h1
    | p2 =>
        have h1 : D .king ∈ ([] : List Card) := hca
        exact nomatch h1
    | p3 =>
        have h1 : D .king ∈ ([] : List Card) := hca
        exact nomatch h1
    | p4 =>
        have h1 : D .king ∈ ([] : List Card) := hca
        exact nomatch h1
    | p5 =>
        have h1 : D .king ∈ ([] : List Card) := hca
        exact nomatch h1
    | p6 =>
        have h1 : D .king ∈ ([] : List Card) := hca
        exact nomatch h1
  · intro s
    show (if s = Suit.diamond ∨ s = Suit.club then 12 else 13) ≤ 13
    split <;> omega
  · exact Nat.le_refl 0
  · exact Nat.zero_lt_one
  · refine ⟨fun i j hi _ _ => ?_, fun c hc => ?_⟩
    · exact absurd hi (Nat.not_lt_zero i)
    · exact nomatch (show c ∈ ([] : List Card) from hc)

/-! ## The witness is solvable (three moves) -/

private def wPlay : List Move :=
  [Move.reveal (D .king), Move.pileStack (D .king), Move.pileStack (C .king)]

private def wWin : State := (wState.run wPlay).getD wState

private theorem wRun : wState.run wPlay = some wWin := by
  have his : (wState.run wPlay).isSome = true := by decide
  cases h : wState.run wPlay with
  | none =>
      rw [h] at his
      simp at his
  | some w =>
      have hw : wWin = w := by
        show (wState.run wPlay).getD wState = w
        rw [h]
        rfl
      rw [hw]

private theorem wState_solvable : wState.solvableFrom :=
  ⟨wPlay, wWin, wRun, by decide⟩

/-! ## The dead-pile invariant -/

/-- Pile p1 still has exactly one hidden card (♣K), with nothing on it
and ♣K not visible. -/
private def DeadInv (s : State) : Prop :=
  s.deal = wDeal ∧ s.depths Anchor.p1 = 1 ∧
    s.board.topOf (Sum.inr (C .king)) = none ∧
    s.board.bottomOf (C .king) = none

private theorem deadInv_hidden {s : State} (hi : DeadInv s) :
    s.hidden Anchor.p1 = [C .king] := by
  show (s.deal.piles Anchor.p1).take (s.depths Anchor.p1) = [C .king]
  rw [hi.1, hi.2.1]
  rfl

private theorem deadInv_topHidden {s : State} (hi : DeadInv s) :
    s.topHidden Anchor.p1 = some (C .king) := by
  show (s.hidden Anchor.p1).getLast? = some (C .king)
  rw [deadInv_hidden hi]
  rfl

private theorem deadInv_mem {s : State} (hi : DeadInv s) :
    C .king ∈ s.deal.piles Anchor.p1 := by
  have h1 : C .king ∈ s.hidden Anchor.p1 := by
    rw [deadInv_hidden hi]
    simp
  exact List.take_subset _ _ h1

/-- The invariant survives every move. -/
private theorem deadInv_step {s s' : State} (hwf : s.WF) (hi : DeadInv s) {m : Move}
    (hap : s.apply m = some s') : DeadInv s' := by
  obtain ⟨hdeal, hdep, htop, hbot⟩ := hi
  cases m with
  | draw =>
      rw [apply_draw_iff] at hap
      obtain ⟨rfl⟩ := hap
      exact ⟨hdeal, hdep, htop, hbot⟩
  | reveal x =>
      rw [apply_reveal_iff] at hap
      obtain ⟨-, r, a, bd, hb, hp, hatt, hst⟩ := hap
      rw [hst]
      have hane : a ≠ Anchor.p1 := by
        intro hae
        rw [hae] at hp
        have htr : s.topHidden Anchor.p1 = some r := pileOfTopHidden_topHidden hp
        rw [deadInv_topHidden ⟨hdeal, hdep, htop, hbot⟩] at htr
        have hrCK : C .king = r := Option.some.inj htr
        rw [← hrCK] at hb
        have hcon : s.board.topOf (Sum.inr (C .king)) = some x :=
          (Board.bottomOf_eq _ _ _).mp hb
        rw [htop] at hcon
        exact absurd hcon (by simp)
      refine ⟨hdeal, ?_, ?_, ?_⟩
      · show (if Anchor.p1 = a then s.depths a - 1 else s.depths Anchor.p1) = 1
        rw [if_neg (Ne.symm hane)]
        exact hdep
      · show bd.topOf (Sum.inr (C .king)) = none
        have hbne : Sum.inr (C .king) ≠ s.hiddenBase a := by
          intro hbe
          have hmem : C .king ∈ s.deal.piles a := hiddenBase_piles hbe.symm
          exact hane (Deal.piles_disj hwf.deal_wf hmem
            (deadInv_mem ⟨hdeal, hdep, htop, hbot⟩))
        rw [Board.attach_topOf_ne _ _ _ hatt hbne]
        exact htop
      · show bd.bottomOf (C .king) = none
        refine (Board.bottomOf_eq_none _ _).mpr ?_
        intro b'' hb''
        have hrne : r ≠ C .king := by
          intro hre
          have htr : s.topHidden a = some r := pileOfTopHidden_topHidden hp
          rw [hre] at htr
          have hmem2 : C .king ∈ s.hidden a := mem_of_getLast htr
          have hmem3 : C .king ∈ s.deal.piles a := List.take_subset _ _ hmem2
          exact hane (Deal.piles_disj hwf.deal_wf hmem3
            (deadInv_mem ⟨hdeal, hdep, htop, hbot⟩))
        by_cases hbb : b'' = s.hiddenBase a
        · rw [hbb, Board.attach_topOf _ _ _ hatt] at hb''
          exact hrne (Option.some.inj hb'')
        · rw [Board.attach_topOf_ne _ _ _ hatt hbb] at hb''
          exact ((Board.bottomOf_eq_none _ _).mp hbot) b'' hb''
  | deckPile x b =>
      rw [apply_deckPile_iff] at hap
      obtain ⟨hprev, hcp, bd, hatt, hst⟩ := hap
      rw [hst]
      have hbne : Sum.inr (C .king) ≠ b := by
        intro hbe
        rw [← hbe] at hcp
        have his := canPlace_inr_isVis hcp
        simp only [State.isVis, hbot] at his
        exact absurd his (by decide)
      have hxne : x ≠ C .king := by
        intro hxe
        rw [hxe] at hprev
        have hmem : C .king ∈ s.stock.cards := prev_mem hprev
        exact Deal.piles_stock_disj hwf.deal_wf (deadInv_mem ⟨hdeal, hdep, htop, hbot⟩)
          ((hwf.stock_wf).2 _ hmem)
      refine ⟨hdeal, hdep, ?_, ?_⟩
      · show bd.topOf (Sum.inr (C .king)) = none
        rw [Board.attach_topOf_ne _ _ _ hatt hbne]
        exact htop
      · show bd.bottomOf (C .king) = none
        refine (Board.bottomOf_eq_none _ _).mpr ?_
        intro b'' hb''
        by_cases hbb : b'' = b
        · rw [hbb, Board.attach_topOf _ _ _ hatt] at hb''
          exact hxne (Option.some.inj hb'')
        · rw [Board.attach_topOf_ne _ _ _ hatt hbb] at hb''
          exact ((Board.bottomOf_eq_none _ _).mp hbot) b'' hb''
  | deckStack x =>
      rw [apply_deckStack_iff] at hap
      obtain ⟨-, -, rfl⟩ := hap
      exact ⟨hdeal, hdep, htop, hbot⟩
  | pileStack x =>
      rw [apply_pileStack_iff] at hap
      obtain ⟨-, b, hb, -, rfl⟩ := hap
      refine ⟨hdeal, hdep, ?_, ?_⟩
      · show (s.board.detach b).topOf (Sum.inr (C .king)) = none
        by_cases hbb : b = Sum.inr (C .king)
        · rw [hbb]
          exact Board.detach_topOf _ _
        · rw [Board.detach_topOf_ne _ _ _ (Ne.symm hbb)]
          exact htop
      · show (s.board.detach b).bottomOf (C .king) = none
        refine (Board.bottomOf_eq_none _ _).mpr ?_
        intro b'' hb''
        by_cases hbb : b'' = b
        · rw [hbb, Board.detach_topOf] at hb''
          simp at hb''
        · rw [Board.detach_topOf_ne _ _ _ hbb] at hb''
          exact ((Board.bottomOf_eq_none _ _).mp hbot) b'' hb''
  | stackPile x b =>
      rw [apply_stackPile_iff] at hap
      obtain ⟨hrk, hcp, bd, hatt, rfl⟩ := hap
      have hxne : x ≠ C .king := by
        intro hxe
        rw [hxe] at hrk
        have hlt : (C .king).rank.toIdx < s.heights (C .king).suit := by omega
        exact (hwf.founds_gone (C .king) hlt).2.2 Anchor.p1
          (by rw [deadInv_hidden ⟨hdeal, hdep, htop, hbot⟩]
              simp)
      refine ⟨hdeal, hdep, ?_, ?_⟩
      · show bd.topOf (Sum.inr (C .king)) = none
        have hbne : Sum.inr (C .king) ≠ b := by
          intro hbe
          rw [← hbe] at hcp
          have his := canPlace_inr_isVis hcp
          simp only [State.isVis, hbot] at his
          exact absurd his (by decide)
        rw [Board.attach_topOf_ne _ _ _ hatt hbne]
        exact htop
      · show bd.bottomOf (C .king) = none
        refine (Board.bottomOf_eq_none _ _).mpr ?_
        intro b'' hb''
        by_cases hbb : b'' = b
        · rw [hbb, Board.attach_topOf _ _ _ hatt] at hb''
          exact hxne (Option.some.inj hb'')
        · rw [Board.attach_topOf_ne _ _ _ hatt hbb] at hb''
          exact ((Board.bottomOf_eq_none _ _).mp hbot) b'' hb''
  | pilePile x b =>
      rw [apply_pilePile_iff] at hap
      obtain ⟨b₀, hb₀, hne, hcm, bd, hatt, rfl⟩ := hap
      refine ⟨hdeal, hdep, ?_, ?_⟩
      · show bd.topOf (Sum.inr (C .king)) = none
        have hbne : Sum.inr (C .king) ≠ b := by
          intro hbe
          rw [← hbe] at hcm
          have his := canMoveRun_inr_isVis hcm
          simp only [State.isVis, hbot] at his
          exact absurd his (by decide)
        rw [Board.attach_topOf_ne _ _ _ hatt hbne]
        show (s.board.detach b₀).topOf (Sum.inr (C .king)) = none
        by_cases hbb : b₀ = Sum.inr (C .king)
        · rw [hbb]
          exact Board.detach_topOf _ _
        · rw [Board.detach_topOf_ne _ _ _ (Ne.symm hbb)]
          exact htop
      · show bd.bottomOf (C .king) = none
        refine (Board.bottomOf_eq_none _ _).mpr ?_
        intro b'' hb''
        have hxne : x ≠ C .king := by
          intro hxe
          rw [hxe, hbot] at hb₀
          simp at hb₀
        by_cases hbb : b'' = b
        · rw [hbb, Board.attach_topOf _ _ _ hatt] at hb''
          exact hxne (Option.some.inj hb'')
        · rw [Board.attach_topOf_ne _ _ _ hatt hbb] at hb''
          by_cases hbb₀ : b'' = b₀
          · rw [hbb₀, Board.detach_topOf] at hb''
            simp at hb''
          · rw [Board.detach_topOf_ne _ _ _ hbb₀] at hb''
            exact ((Board.bottomOf_eq_none _ _).mp hbot) b'' hb''

/-- A WF state satisfying the invariant is unsolvable: the win needs
`heights ♣ = 13`, so ♣K foundation-passed, but it stays hidden. -/
private theorem dead_unsolvable {s : State} (hwf : s.WF) (hi : DeadInv s) :
    ¬ s.solvableFrom := by
  intro hsolv
  obtain ⟨play, w, hrun, hwin⟩ := hsolv
  have aux : ∀ (play : List Move) (s w : State),
      s.run play = some w → s.WF → DeadInv s → DeadInv w ∧ w.WF := by
    intro play
    induction play with
    | nil =>
        intro s w hrun hwf hi
        have h' : some s = some w := hrun
        rw [← Option.some.inj h']
        exact ⟨hi, hwf⟩
    | cons m rest ih =>
        intro s w hrun hwf hi
        obtain ⟨s', hap, hrest, -⟩ := run_cons_inv hrun
        exact ih s' w hrest (apply_wf hwf m s' hap) (deadInv_step hwf hi hap)
  obtain ⟨hiw, hwfw⟩ := aux play s w hrun hwf hi
  have hc13 : w.heights Suit.club = 13 :=
    of_decide_eq_true ((List.all_eq_true.mp hwin) Suit.club (Suit.mem_all _))
  have hlt : (C .king).rank.toIdx < w.heights (C .king).suit := by
    show (C .king).rank.toIdx < w.heights Suit.club
    rw [hc13]
    decide
  exact (hwfw.founds_gone (C .king) hlt).2.2 Anchor.p1
    (by rw [deadInv_hidden hiw]; simp)

/-! ## The refutation -/

private def wState1 : State := (wState.apply (Move.pileStack (D .king))).getD wState

private theorem wState_apply :
    wState.apply (Move.pileStack (D .king)) = some wState1 := by
  have his : (wState.apply (Move.pileStack (D .king))).isSome = true := by decide
  cases h : wState.apply (Move.pileStack (D .king)) with
  | none =>
      rw [h] at his
      simp at his
  | some s₁ =>
      have hw : wState1 = s₁ := by
        show (wState.apply (Move.pileStack (D .king))).getD wState = s₁
        rw [h]
        rfl
      rw [hw]

private theorem wState1_DeadInv : DeadInv wState1 :=
  ⟨rfl, rfl, by decide, by decide⟩

theorem wState_not_dominant : ¬ dominantAt wState (Move.pileStack (D .king)) := by
  intro hdom
  obtain ⟨s₁, hap, hsolv₁⟩ := hdom wState_solvable
  have hq : wState1 = s₁ := Option.some.inj (wState_apply.symm.trans hap)
  subst hq
  exact dead_unsolvable (apply_wf wState_wf _ _ wState_apply) wState1_DeadInv hsolv₁

/-- All three hypotheses of the staged theorem hold at the witness. -/
example : safeToStack wState (D .king) = true := by decide

example : wState.legal (Move.pileStack (D .king)) = true := by decide

/-- The winning play's first move is the reveal the dominance loses. -/
example : (wState.apply (Move.reveal (D .king))).isSome = true := by decide

end DeadPile

#print axioms DeadPile.wState_wf
#print axioms DeadPile.wState_solvable
#print axioms DeadPile.deadInv_step
#print axioms DeadPile.dead_unsolvable
#print axioms DeadPile.wState_apply
#print axioms DeadPile.wState1_DeadInv
#print axioms DeadPile.wState_not_dominant
