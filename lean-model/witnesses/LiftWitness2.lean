import Klondike.Bridge

/-!
# LiftWitness2 — `toEngine_lifts` refuted AFTER the buried-base repair

The mirror of the old hole: the model seats `h5` on `hA` **via
deal-adjacency** (base merely *placed*, ranks not canSitOn-compatible),
while the abstract game's witness board re-seats `h5` on `s6` **via
canSitOn** (a genuinely placed, fitting card).  The engine model game
has no re-seating move (`pilePile` banned; the pileStack/stackPile
accommodation is rank-gated), so `hA` is deadlocked under `h5` and the
model can never raise hearts' foundation — while the abstract game
wins freely.  WF holds; the state is even reachable in form (a
revealed deal chain).
-/

/-! ## The cards -/

def hA : Card := ⟨Suit.heart, Rank.ace⟩
def h2 : Card := ⟨Suit.heart, Rank.two⟩
def h3 : Card := ⟨Suit.heart, Rank.three⟩
def h4 : Card := ⟨Suit.heart, Rank.four⟩
def h5 : Card := ⟨Suit.heart, Rank.five⟩
def h6 : Card := ⟨Suit.heart, Rank.six⟩
def h7 : Card := ⟨Suit.heart, Rank.seven⟩
def h8 : Card := ⟨Suit.heart, Rank.eight⟩
def h9 : Card := ⟨Suit.heart, Rank.nine⟩
def h10 : Card := ⟨Suit.heart, Rank.ten⟩
def hJ : Card := ⟨Suit.heart, Rank.jack⟩
def hQ : Card := ⟨Suit.heart, Rank.queen⟩
def hK : Card := ⟨Suit.heart, Rank.king⟩

def sA : Card := ⟨Suit.spade, Rank.ace⟩
def s2 : Card := ⟨Suit.spade, Rank.two⟩
def s3 : Card := ⟨Suit.spade, Rank.three⟩
def s4 : Card := ⟨Suit.spade, Rank.four⟩
def s5 : Card := ⟨Suit.spade, Rank.five⟩
def s6 : Card := ⟨Suit.spade, Rank.six⟩
def s7 : Card := ⟨Suit.spade, Rank.seven⟩
def s8 : Card := ⟨Suit.spade, Rank.eight⟩
def s9 : Card := ⟨Suit.spade, Rank.nine⟩
def s10 : Card := ⟨Suit.spade, Rank.ten⟩
def sJ : Card := ⟨Suit.spade, Rank.jack⟩
def sQ : Card := ⟨Suit.spade, Rank.queen⟩
def sK : Card := ⟨Suit.spade, Rank.king⟩

def dA : Card := ⟨Suit.diamond, Rank.ace⟩
def d2 : Card := ⟨Suit.diamond, Rank.two⟩
def d3 : Card := ⟨Suit.diamond, Rank.three⟩
def d4 : Card := ⟨Suit.diamond, Rank.four⟩
def d5 : Card := ⟨Suit.diamond, Rank.five⟩
def d6 : Card := ⟨Suit.diamond, Rank.six⟩
def d7 : Card := ⟨Suit.diamond, Rank.seven⟩
def d8 : Card := ⟨Suit.diamond, Rank.eight⟩
def d9 : Card := ⟨Suit.diamond, Rank.nine⟩
def d10 : Card := ⟨Suit.diamond, Rank.ten⟩
def dJ : Card := ⟨Suit.diamond, Rank.jack⟩
def dQ : Card := ⟨Suit.diamond, Rank.queen⟩
def dK : Card := ⟨Suit.diamond, Rank.king⟩

def cA : Card := ⟨Suit.club, Rank.ace⟩
def c2 : Card := ⟨Suit.club, Rank.two⟩
def c3 : Card := ⟨Suit.club, Rank.three⟩
def c4 : Card := ⟨Suit.club, Rank.four⟩
def c5 : Card := ⟨Suit.club, Rank.five⟩
def c6 : Card := ⟨Suit.club, Rank.six⟩
def c7 : Card := ⟨Suit.club, Rank.seven⟩
def c8 : Card := ⟨Suit.club, Rank.eight⟩
def c9 : Card := ⟨Suit.club, Rank.nine⟩
def c10 : Card := ⟨Suit.club, Rank.ten⟩
def cJ : Card := ⟨Suit.club, Rank.jack⟩
def cQ : Card := ⟨Suit.club, Rank.queen⟩
def cK : Card := ⟨Suit.club, Rank.king⟩

/-! ## Seat-list boards -/

/-- The board function of a seat list: the first seat at each base. -/
def seatsTop : List (Base × Card) → Base → Option Card :=
  fun S b => ((S.filter (fun p => decide (p.1 = b))).head?).map Prod.snd

theorem seatsTop_mem (S : List (Base × Card)) (b : Base) (c : Card)
    (h : seatsTop S b = some c) : (b, c) ∈ S := by
  simp only [seatsTop] at h
  obtain ⟨p, hp, hps⟩ := Option.map_eq_some_iff.mp h
  cases hfl : S.filter (fun p => decide (p.1 = b)) with
  | nil => rw [hfl] at hp; simp at hp
  | cons q t =>
      rw [hfl] at hp
      simp only [List.head?_cons, Option.some.injEq] at hp
      subst hp
      have hqf : q ∈ S.filter (fun p => decide (p.1 = b)) := by rw [hfl]; simp
      obtain ⟨hqS, hqb⟩ := List.mem_filter.mp hqf
      have hq1 : q.1 = b := of_decide_eq_true hqb
      have hpair : (q.1, q.2) = (b, c) := by rw [hq1, hps]
      exact hpair ▸ hqS

/-- A board from a seat list with no card seated twice. -/
def seatsBoard (S : List (Base × Card))
    (hnd : ∀ p ∈ S, ∀ q ∈ S, p.2 = q.2 → p.1 = q.1) : Board where
  topOf := seatsTop S
  inj := by
    intro b₁ b₂ c h₁ h₂
    exact hnd ⟨b₁, c⟩ (seatsTop_mem S b₁ c h₁) ⟨b₂, c⟩ (seatsTop_mem S b₂ c h₂) rfl

/-! ## The deal -/

/-- The state's stock (17 cards). -/
def ST17 : List Card :=
  [h2, h3, h4, h6, h8, h9, h10, hJ, hQ, hK, s7, s8, s9, s10, sJ, sQ, sK]

/-- The deal: hearts' ace+five in p1 (the deadlock), hearts' seven and
spades' six in p2 (the witness chain), everything else already
foundation-side. -/
def LX : Deal where
  piles := fun a =>
    match a with
    | Anchor.p0 => [dA]
    | Anchor.p1 => [hA, h5]
    | Anchor.p2 => [h7, s6, d5]
    | Anchor.p3 => [d2, d3, d4, d6]
    | Anchor.p4 => [d7, d8, d9, d10, dJ]
    | Anchor.p5 => [dQ, dK, cA, c2, c3, c4]
    | Anchor.p6 => [c5, c6, c7, c8, c9, c10, cJ]
  stock := ST17 ++ [sA, s2, s3, s4, s5, cQ, cK]

theorem LX_wf : LX.WF := by
  refine ⟨?_, ?_, ?_⟩
  · intro a; cases a <;> rfl
  · rfl
  · intro i j hi hj heq
    have hlen : ((Anchor.all.flatMap LX.piles) ++ LX.stock).length = 52 := by rfl
    rw [hlen] at hi hj
    exact (by decide : ∀ i ∈ List.range 52, ∀ j ∈ List.range 52,
      ((Anchor.all.flatMap LX.piles) ++ LX.stock)[i]? =
      ((Anchor.all.flatMap LX.piles) ++ LX.stock)[j]? → i = j) i
      (List.mem_range.mpr hi) j (List.mem_range.mpr hj) heq

/-! ## The model's board and state -/

/-- The model board: `hA` on p1's anchor, `h5` on `hA` (deal-adjacent,
base placed but NOT canSitOn-compatible — the hole), `h7` on p2's
anchor, `s6` on `h7` (deal-adjacent, placed). -/
def BXS : List (Base × Card) :=
  [(Sum.inl Anchor.p1, hA), (Sum.inl Anchor.p2, h7), (Sum.inr hA, h5), (Sum.inr h7, s6)]

def BX : Board := seatsBoard BXS (by decide)

theorem BX_top_p1 : BX.topOf (Sum.inl Anchor.p1) = some hA := by decide
theorem BX_top_p2 : BX.topOf (Sum.inl Anchor.p2) = some h7 := by decide
theorem BX_top_hA : BX.topOf (Sum.inr hA) = some h5 := by decide
theorem BX_top_h7 : BX.topOf (Sum.inr h7) = some s6 := by decide

theorem BX_img (c : Card) : (BX.bottomOf c).isSome = true ↔
    c = hA ∨ c = h5 ∨ c = h7 ∨ c = s6 := by
  constructor
  · intro h
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp h
    have hm := seatsTop_mem BXS b c ((Board.bottomOf_eq BX c b).mp hb)
    simp only [List.mem_cons, List.not_mem_nil, BXS] at hm
    rcases hm with ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ | h
    · exact Or.inl rfl
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inr rfl))
    · exact h.elim
  · intro h
    rcases h with rfl | rfl | rfl | rfl
    · rw [show BX.bottomOf hA = some (Sum.inl Anchor.p1) from
        (Board.bottomOf_eq _ _ _).mpr BX_top_p1]; rfl
    · rw [show BX.bottomOf h5 = some (Sum.inr hA) from
        (Board.bottomOf_eq _ _ _).mpr BX_top_hA]; rfl
    · rw [show BX.bottomOf h7 = some (Sum.inl Anchor.p2) from
        (Board.bottomOf_eq _ _ _).mpr BX_top_p2]; rfl
    · rw [show BX.bottomOf s6 = some (Sum.inr h7) from
        (Board.bottomOf_eq _ _ _).mpr BX_top_h7]; rfl

/-- The witness state: hearts at 0, spades at 5, the rest complete. -/
def stN : State where
  deal := LX
  board := BX
  heights := fun s => if s = Suit.heart then 0 else if s = Suit.spade then 5 else 13
  depths := fun _ => 0
  stock := ⟨ST17, 0⟩
  drawStep := 1

theorem stN_heart : stN.heights Suit.heart = 0 := rfl

theorem stN_stock_aux : ∀ c ∈ ST17, ¬ (c.rank.toIdx < stN.heights c.suit) := by
  intro c hc
  have hall : (ST17.all fun c => !decide (c.rank.toIdx < stN.heights c.suit)) = true := by
    decide
  have hb := (List.all_eq_true.mp hall) c hc
  intro hlt
  rw [decide_eq_true hlt] at hb
  simp at hb

theorem stN_edges : ∀ b c, stN.board.topOf b = some c →
    stN.board.bottomOf c = some b ∧
    (match b with
     | Sum.inl a => c.rank = Rank.king ∨ (stN.deal.piles a).head? = some c
     | Sum.inr d =>
       (∃ a t rest, stN.deal.piles a = t ++ d :: c :: rest ∧
          ((∃ a', stN.topHidden a' = some d) ∨ (stN.board.bottomOf d).isSome = true)) ∨
       ((stN.board.bottomOf d).isSome = true ∧ canSitOn c d = true)) := by
  intro b c hb
  refine ⟨(Board.bottomOf_eq _ _ _).mpr hb, ?_⟩
  have hm : (b, c) ∈ BXS := seatsTop_mem BXS b c hb
  simp only [List.mem_cons, List.not_mem_nil, BXS] at hm
  rcases hm with ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ | h
  · exact Or.inr rfl
  · exact Or.inr rfl
  · refine Or.inl ⟨Anchor.p1, [], [], rfl, Or.inr ?_⟩
    show (BX.bottomOf hA).isSome = true
    rw [show BX.bottomOf hA = some (Sum.inl Anchor.p1) from
      (Board.bottomOf_eq _ _ _).mpr BX_top_p1]
    rfl
  · refine Or.inl ⟨Anchor.p2, [], [d5], rfl, Or.inr ?_⟩
    show (BX.bottomOf h7).isSome = true
    rw [show BX.bottomOf h7 = some (Sum.inl Anchor.p2) from
      (Board.bottomOf_eq _ _ _).mpr BX_top_p2]
    rfl
  · exact h.elim

theorem stN_wf : stN.WF := by
  refine ⟨LX_wf, ?_, stN_edges, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a; exact Nat.zero_le _
  · intro c hv
    rcases (BX_img c).mp hv with rfl | rfl | rfl | rfl <;>
      exact Cycle.posOf_eq_none (by decide)
  · intro c hon
    exact Cycle.posOf_eq_none (fun hmem => stN_stock_aux c hmem (of_decide_eq_true hon))
  · intro c hc
    refine ⟨?_, ?_, ?_⟩
    · cases hv : stN.isVis c with
      | false => rfl
      | true =>
          rcases (BX_img c).mp hv with rfl | rfl | rfl | rfl <;> exact absurd hc (by decide)
    · exact Cycle.posOf_eq_none (fun hmem => stN_stock_aux c hmem hc)
    · intro a
      have h0 : stN.depths a = 0 := rfl
      rw [show stN.hidden a = List.take (stN.depths a) (stN.deal.piles a) from rfl, h0,
        List.take_zero]
      simp
  · intro c _hv a
    have h0 : stN.depths a = 0 := rfl
    rw [show stN.hidden a = List.take (stN.depths a) (stN.deal.piles a) from rfl, h0,
      List.take_zero]
    simp
  · intro s
    rcases s with ⟨col, p⟩
    cases col <;> cases p <;> decide
  · exact Nat.zero_le _
  · exact Nat.zero_lt_one
  · refine ⟨?_, ?_⟩
    · intro i j hi hj heq
      have hi' : i < ST17.length := hi
      have hj' : j < ST17.length := hj
      rw [show ST17.length = 17 from rfl] at hi' hj'
      exact (by decide : ∀ i ∈ List.range 17, ∀ j ∈ List.range 17, ST17[i]? = ST17[j]? → i = j) i
        (List.mem_range.mpr hi') j (List.mem_range.mpr hj') heq
    · intro c hc
      have hall : (ST17.all fun c => decide (c ∈ LX.stock)) = true := by decide
      exact of_decide_eq_true ((List.all_eq_true.mp hall) c hc)

/-! ## The deadlock: no engine play from `stN` ever wins -/

/-- The invariant: along any engine play, hearts' foundation stays at
zero (the ace is buried under its deal-successor `h5`, and `h5` itself
is unpassable before the ace passes), `h5` stays on `hA`, depths stay
zero (no reveals possible), and the ace never enters the stock. -/
theorem stN_inv : ∀ (play : List Move) (st st' : State),
    (∀ m ∈ play, m.isEngine = true) → st.run play = some st' →
    st.heights Suit.heart = 0 → st.board.topOf (Sum.inr hA) = some h5 →
    (∀ a, st.depths a = 0) → hA ∉ st.stock.cards →
    st'.heights Suit.heart = 0 ∧ st'.board.topOf (Sum.inr hA) = some h5 ∧
    (∀ a, st'.depths a = 0) ∧ hA ∉ st'.stock.cards := by
  intro play
  induction play with
  | nil =>
      intro st st' _ h hh ht hd hmem
      have e : st = st' := Option.some.inj h
      subst e
      exact ⟨hh, ht, hd, hmem⟩
  | cons m ms ih =>
      intro st st' heng h hh ht hd hmem
      obtain ⟨s₁, hap, hrest, -⟩ := run_cons_inv h
      have hms : ∀ m' ∈ ms, m'.isEngine = true := fun m' hm' => heng m' (by simp [hm'])
      have hmeng := heng m (by simp)
      cases m with
      | draw =>
          rw [apply_draw_iff] at hap
          subst hap
          refine ih _ st' hms hrest ?_ ?_ ?_ ?_
          · exact hh
          · exact ht
          · exact hd
          · simp only [Cycle.dealOnce_cards]; exact hmem
      | reveal c =>
          rw [apply_reveal_iff] at hap
          obtain ⟨-, r, a, bd, -, hp, -, -⟩ := hap
          obtain ⟨-, hp'⟩ := findFirst_mem _ _ _ hp
          rw [show st.topHidden a = ((st.deal.piles a).take (st.depths a)).getLast? from rfl,
            hd a, List.take_zero] at hp'
          simp at hp'
      | deckPile c b =>
          rw [apply_deckPile_iff] at hap
          obtain ⟨-, hcp, bd, hatt, hst⟩ := hap
          obtain ⟨htop', -⟩ := Bool.and_eq_true_iff.mp hcp
          have hnb : b ≠ Sum.inr hA := by
            intro hbb
            rw [hbb] at htop'
            rw [show st.board.topOf (Sum.inr hA) = some h5 from ht] at htop'
            simp at htop'
          refine ih s₁ st' hms hrest ?_ ?_ ?_ ?_
          · rw [hst]; exact hh
          · rw [hst]; show bd.topOf (Sum.inr hA) = some h5
            rw [Board.attach_topOf_ne _ _ _ hatt (Ne.symm hnb)]
            exact ht
          · rw [hst]; exact hd
          · rw [hst]; intro hcm
            exact hmem (Cycle.mem_removeIdx _ _ hcm)
      | deckStack c =>
          rw [apply_deckStack_iff] at hap
          obtain ⟨hprev, hrk, hst⟩ := hap
          have hns : c.suit ≠ Suit.heart := by
            intro hs
            rw [hs, hh] at hrk
            have hra : c.rank = Rank.ace :=
              Rank.toIdx_inj (hrk.trans (show (0 : Nat) = Rank.ace.toIdx from rfl))
            have hc : c = hA := by
              rcases c with ⟨s, r⟩
              have h1 : s = Suit.heart := hs
              have h2 : r = Rank.ace := hra
              subst h1; subst h2; rfl
            rw [hc] at hprev
            simp only [Cycle.prev] at hprev
            split at hprev
            · simp at hprev
            · exact hmem (List.mem_iff_getElem?.mpr ⟨st.stock.cursor - 1, hprev⟩)
          refine ih s₁ st' hms hrest ?_ ?_ ?_ ?_
          · rw [hst]
            show (if Suit.heart = c.suit then st.heights Suit.heart + 1
              else st.heights Suit.heart) = 0
            rw [if_neg (fun hcc => hns hcc.symm)]
            exact hh
          · rw [hst]; exact ht
          · rw [hst]; exact hd
          · rw [hst]; intro hcm
            exact hmem (Cycle.mem_removeIdx _ _ hcm)
      | pileStack c =>
          rw [apply_pileStack_iff] at hap
          obtain ⟨htop, b, hb, hrk, hst⟩ := hap
          have hns : c.suit ≠ Suit.heart := by
            intro hs
            rw [hs, hh] at hrk
            have hra : c.rank = Rank.ace :=
              Rank.toIdx_inj (hrk.trans (show (0 : Nat) = Rank.ace.toIdx from rfl))
            have hc : c = hA := by
              rcases c with ⟨s, r⟩
              have h1 : s = Suit.heart := hs
              have h2 : r = Rank.ace := hra
              subst h1; subst h2; rfl
            rw [hc] at htop
            rw [show st.board.topOf (Sum.inr hA) = some h5 from ht] at htop
            simp at htop
          have hnb : b ≠ Sum.inr hA := by
            intro hbb
            rw [hbb] at hb
            have htopc : st.board.topOf (Sum.inr hA) = some c :=
              (Board.bottomOf_eq st.board c (Sum.inr hA)).mp hb
            have hc5 : c = h5 := (Option.some.inj (ht.symm.trans htopc)).symm
            exact hns (by rw [hc5]; rfl)
          refine ih s₁ st' hms hrest ?_ ?_ ?_ ?_
          · rw [hst]
            show (if Suit.heart = c.suit then st.heights Suit.heart + 1
              else st.heights Suit.heart) = 0
            rw [if_neg (fun hcc => hns hcc.symm)]
            exact hh
          · rw [hst]; show (st.board.detach b).topOf (Sum.inr hA) = some h5
            rw [Board.detach_topOf_ne _ _ _ (Ne.symm hnb)]
            exact ht
          · rw [hst]; exact hd
          · rw [hst]; exact hmem
      | stackPile c b =>
          rw [apply_stackPile_iff] at hap
          obtain ⟨hrk, hcp, bd, hatt, hst⟩ := hap
          have hns : c.suit ≠ Suit.heart := by
            intro hs
            rw [hs, hh] at hrk
            omega
          obtain ⟨htop', -⟩ := Bool.and_eq_true_iff.mp hcp
          have hnb : b ≠ Sum.inr hA := by
            intro hbb
            rw [hbb] at htop'
            rw [show st.board.topOf (Sum.inr hA) = some h5 from ht] at htop'
            simp at htop'
          refine ih s₁ st' hms hrest ?_ ?_ ?_ ?_
          · rw [hst]
            show (if Suit.heart = c.suit then st.heights Suit.heart - 1
              else st.heights Suit.heart) = 0
            rw [if_neg (fun hcc => hns hcc.symm)]
            exact hh
          · rw [hst]; show bd.topOf (Sum.inr hA) = some h5
            rw [Board.attach_topOf_ne _ _ _ hatt (Ne.symm hnb)]
            exact ht
          · rw [hst]; exact hd
          · rw [hst]; exact hmem
      | pilePile c b => simp [Move.isEngine] at hmeng

theorem stN_notSolvable : ¬ stN.solvableEngine := by
  intro hsol
  obtain ⟨play, heng, st', hrun, hwin⟩ := hsol
  obtain ⟨hh, -, -, -⟩ :=
    stN_inv play stN st' heng hrun stN_heart BX_top_hA (fun _ => rfl) (by decide)
  have hall : (Suit.all.all fun s => decide (st'.heights s = 13)) = true := hwin
  have h13 := of_decide_eq_true ((List.all_eq_true.mp hall) Suit.heart (Suit.mem_all _))
  omega

/-! ## The witness boards (the abstract game's freedom) -/

/-- `WB1`: as the model's board, but `h5` re-seated on `s6` (canSitOn —
`s6` genuinely placed).  Frees `hA` for the abstract `pileStack`. -/
def WB1S : List (Base × Card) :=
  [(Sum.inl Anchor.p1, hA), (Sum.inl Anchor.p2, h7), (Sum.inr h7, s6), (Sum.inr s6, h5)]

def WB1 : Board := seatsBoard WB1S (by decide)

theorem WB1_p1 : WB1.topOf (Sum.inl Anchor.p1) = some hA := by decide
theorem WB1_p2 : WB1.topOf (Sum.inl Anchor.p2) = some h7 := by decide
theorem WB1_h7 : WB1.topOf (Sum.inr h7) = some s6 := by decide
theorem WB1_s6 : WB1.topOf (Sum.inr s6) = some h5 := by decide

/-- `WB2`: `WB1` minus the passed `hA` — realizes the state after the
abstract game has passed `hA`, `h2`, `h3`, `h4`. -/
def WB2S : List (Base × Card) :=
  [(Sum.inl Anchor.p2, h7), (Sum.inr h7, s6), (Sum.inr s6, h5)]

def WB2 : Board := seatsBoard WB2S (by decide)

theorem WB2_p2 : WB2.topOf (Sum.inl Anchor.p2) = some h7 := by decide
theorem WB2_h7 : WB2.topOf (Sum.inr h7) = some s6 := by decide
theorem WB2_s6 : WB2.topOf (Sum.inr s6) = some h5 := by decide

/-- `WB3`: realizes the state after `h5` and `h6` too — `s6` is top. -/
def WB3S : List (Base × Card) := [(Sum.inl Anchor.p2, h7), (Sum.inr h7, s6)]

def WB3 : Board := seatsBoard WB3S (by decide)

theorem WB3_p2 : WB3.topOf (Sum.inl Anchor.p2) = some h7 := by decide
theorem WB3_h7 : WB3.topOf (Sum.inr h7) = some s6 := by decide

/-- `WB4`: realizes the state after `s6` too — `h7` is top. -/
def WB4S : List (Base × Card) := [(Sum.inl Anchor.p2, h7)]

def WB4 : Board := seatsBoard WB4S (by decide)

theorem WB4_p2 : WB4.topOf (Sum.inl Anchor.p2) = some h7 := by decide

theorem seats_img (bd : Board) (cards : List Card)
    (hmem : ∀ b c, bd.topOf b = some c → c ∈ cards)
    (hseat : ∀ c ∈ cards, ∃ b, bd.topOf b = some c) (c : Card) :
    (bd.bottomOf c).isSome = true ↔ c ∈ cards := by
  constructor
  · intro h
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp h
    exact hmem b c ((Board.bottomOf_eq bd c b).mp hb)
  · intro hc
    obtain ⟨b, hb⟩ := hseat c hc
    rw [show bd.bottomOf c = some b from (Board.bottomOf_eq _ _ _).mpr hb]
    rfl

theorem WB1_img (c : Card) : (WB1.bottomOf c).isSome = true ↔ c ∈ [hA, h7, s6, h5] :=
  seats_img WB1 [hA, h7, s6, h5]
    (by
      intro b c h
      have hm := seatsTop_mem WB1S b c h
      simp only [List.mem_cons, List.not_mem_nil, WB1S] at hm
      rcases hm with ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ | h
      · simp
      · simp
      · simp
      · simp
      · exact h.elim)
    (by
      intro c hc
      rcases List.mem_cons.mp hc with rfl | hc
      · exact ⟨_, WB1_p1⟩
      · rcases List.mem_cons.mp hc with rfl | hc
        · exact ⟨_, WB1_p2⟩
        · rcases List.mem_cons.mp hc with rfl | hc
          · exact ⟨_, WB1_h7⟩
          · rcases List.mem_cons.mp hc with rfl | hc
            · exact ⟨_, WB1_s6⟩
            · cases hc) c

theorem WB2_img (c : Card) : (WB2.bottomOf c).isSome = true ↔ c ∈ [h7, s6, h5] :=
  seats_img WB2 [h7, s6, h5]
    (by
      intro b c h
      have hm := seatsTop_mem WB2S b c h
      simp only [List.mem_cons, List.not_mem_nil, WB2S] at hm
      rcases hm with ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ | h
      · simp
      · simp
      · simp
      · exact h.elim)
    (by
      intro c hc
      rcases List.mem_cons.mp hc with rfl | hc
      · exact ⟨_, WB2_p2⟩
      · rcases List.mem_cons.mp hc with rfl | hc
        · exact ⟨_, WB2_h7⟩
        · rcases List.mem_cons.mp hc with rfl | hc
          · exact ⟨_, WB2_s6⟩
          · cases hc) c

theorem WB3_img (c : Card) : (WB3.bottomOf c).isSome = true ↔ c ∈ [h7, s6] :=
  seats_img WB3 [h7, s6]
    (by
      intro b c h
      have hm := seatsTop_mem WB3S b c h
      simp only [List.mem_cons, List.not_mem_nil, WB3S] at hm
      rcases hm with ⟨e1, e2⟩ | ⟨e1, e2⟩ | h
      · simp
      · simp
      · exact h.elim)
    (by
      intro c hc
      rcases List.mem_cons.mp hc with rfl | hc
      · exact ⟨_, WB3_p2⟩
      · rcases List.mem_cons.mp hc with rfl | hc
        · exact ⟨_, WB3_h7⟩
        · cases hc) c

theorem WB4_img (c : Card) : (WB4.bottomOf c).isSome = true ↔ c ∈ [h7] :=
  seats_img WB4 [h7]
    (by
      intro b c h
      have hm := seatsTop_mem WB4S b c h
      simp only [List.mem_cons, List.not_mem_nil, WB4S] at hm
      rcases hm with ⟨e1, e2⟩ | h
      · simp
      · exact h.elim)
    (by
      intro c hc
      rcases List.mem_cons.mp hc with rfl | hc
      · exact ⟨_, WB4_p2⟩
      · cases hc) c

/-! ## Fits for the witness boards (depths are all zero) -/

theorem WB1_fits : WB1.Fits LX (fun _ => 0) := by
  intro b c hb
  have hm : (b, c) ∈ WB1S := seatsTop_mem WB1S b c hb
  simp only [List.mem_cons, List.not_mem_nil, WB1S] at hm
  rcases hm with ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ | h
  · exact Or.inr rfl
  · exact Or.inr rfl
  · refine Or.inl ⟨Anchor.p2, [], [d5], rfl, Or.inr ?_⟩
    show (WB1.bottomOf h7).isSome = true
    rw [show WB1.bottomOf h7 = some (Sum.inl Anchor.p2) from
      (Board.bottomOf_eq _ _ _).mpr WB1_p2]
    rfl
  · refine Or.inr ⟨?_, by decide⟩
    show (WB1.bottomOf s6).isSome = true
    rw [show WB1.bottomOf s6 = some (Sum.inr h7) from
      (Board.bottomOf_eq _ _ _).mpr WB1_h7]
    rfl
  · exact h.elim

theorem WB2_fits : WB2.Fits LX (fun _ => 0) := by
  intro b c hb
  have hm : (b, c) ∈ WB2S := seatsTop_mem WB2S b c hb
  simp only [List.mem_cons, List.not_mem_nil, WB2S] at hm
  rcases hm with ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ | h
  · exact Or.inr rfl
  · refine Or.inl ⟨Anchor.p2, [], [d5], rfl, Or.inr ?_⟩
    show (WB2.bottomOf h7).isSome = true
    rw [show WB2.bottomOf h7 = some (Sum.inl Anchor.p2) from
      (Board.bottomOf_eq _ _ _).mpr WB2_p2]
    rfl
  · refine Or.inr ⟨?_, by decide⟩
    show (WB2.bottomOf s6).isSome = true
    rw [show WB2.bottomOf s6 = some (Sum.inr h7) from
      (Board.bottomOf_eq _ _ _).mpr WB2_h7]
    rfl
  · exact h.elim

theorem WB3_fits : WB3.Fits LX (fun _ => 0) := by
  intro b c hb
  have hm : (b, c) ∈ WB3S := seatsTop_mem WB3S b c hb
  simp only [List.mem_cons, List.not_mem_nil, WB3S] at hm
  rcases hm with ⟨e1, e2⟩ | ⟨e1, e2⟩ | h
  · exact Or.inr rfl
  · refine Or.inl ⟨Anchor.p2, [], [d5], rfl, Or.inr ?_⟩
    show (WB3.bottomOf h7).isSome = true
    rw [show WB3.bottomOf h7 = some (Sum.inl Anchor.p2) from
      (Board.bottomOf_eq _ _ _).mpr WB3_p2]
    rfl
  · exact h.elim

theorem WB4_fits : WB4.Fits LX (fun _ => 0) := by
  intro b c hb
  have hm : (b, c) ∈ WB4S := seatsTop_mem WB4S b c hb
  simp only [List.mem_cons, List.not_mem_nil, WB4S] at hm
  rcases hm with ⟨e1, e2⟩ | h
  · exact Or.inr rfl
  · exact h.elim

/-! ## The abstract state chain -/

def E0 : EState := toEngine stN

def E1 : EState := { E0 with
  vis := fun c' => decide (c' ≠ hA) && E0.vis c',
  heights := fun s => if s = hA.suit then E0.heights s + 1 else E0.heights s }

def E2 : EState := { E1 with
  order := Cycle.removeIdx E1.order 0, offset := 0,
  heights := fun s => if s = h2.suit then E1.heights s + 1 else E1.heights s }

def E3 : EState := { E2 with
  order := Cycle.removeIdx E2.order 0, offset := 0,
  heights := fun s => if s = h3.suit then E2.heights s + 1 else E2.heights s }

def E4 : EState := { E3 with
  order := Cycle.removeIdx E3.order 0, offset := 0,
  heights := fun s => if s = h4.suit then E3.heights s + 1 else E3.heights s }

def E5 : EState := { E4 with
  vis := fun c' => decide (c' ≠ h5) && E4.vis c',
  heights := fun s => if s = h5.suit then E4.heights s + 1 else E4.heights s }

def E6 : EState := { E5 with
  order := Cycle.removeIdx E5.order 0, offset := 0,
  heights := fun s => if s = h6.suit then E5.heights s + 1 else E5.heights s }

def E7 : EState := { E6 with
  vis := fun c' => decide (c' ≠ s6) && E6.vis c',
  heights := fun s => if s = s6.suit then E6.heights s + 1 else E6.heights s }

def E8 : EState := { E7 with
  vis := fun c' => decide (c' ≠ h7) && E7.vis c',
  heights := fun s => if s = h7.suit then E7.heights s + 1 else E7.heights s }

def E9 : EState := { E8 with
  order := Cycle.removeIdx E8.order 0, offset := 0,
  heights := fun s => if s = h8.suit then E8.heights s + 1 else E8.heights s }

def E10 : EState := { E9 with
  order := Cycle.removeIdx E9.order 0, offset := 0,
  heights := fun s => if s = h9.suit then E9.heights s + 1 else E9.heights s }

def E11 : EState := { E10 with
  order := Cycle.removeIdx E10.order 0, offset := 0,
  heights := fun s => if s = h10.suit then E10.heights s + 1 else E10.heights s }

def E12 : EState := { E11 with
  order := Cycle.removeIdx E11.order 0, offset := 0,
  heights := fun s => if s = hJ.suit then E11.heights s + 1 else E11.heights s }

def E13 : EState := { E12 with
  order := Cycle.removeIdx E12.order 0, offset := 0,
  heights := fun s => if s = hQ.suit then E12.heights s + 1 else E12.heights s }

def E14 : EState := { E13 with
  order := Cycle.removeIdx E13.order 0, offset := 0,
  heights := fun s => if s = hK.suit then E13.heights s + 1 else E13.heights s }

def E15 : EState := { E14 with
  order := Cycle.removeIdx E14.order 0, offset := 0,
  heights := fun s => if s = s7.suit then E14.heights s + 1 else E14.heights s }

def E16 : EState := { E15 with
  order := Cycle.removeIdx E15.order 0, offset := 0,
  heights := fun s => if s = s8.suit then E15.heights s + 1 else E15.heights s }

def E17 : EState := { E16 with
  order := Cycle.removeIdx E16.order 0, offset := 0,
  heights := fun s => if s = s9.suit then E16.heights s + 1 else E16.heights s }

def E18 : EState := { E17 with
  order := Cycle.removeIdx E17.order 0, offset := 0,
  heights := fun s => if s = s10.suit then E17.heights s + 1 else E17.heights s }

def E19 : EState := { E18 with
  order := Cycle.removeIdx E18.order 0, offset := 0,
  heights := fun s => if s = sJ.suit then E18.heights s + 1 else E18.heights s }

def E20 : EState := { E19 with
  order := Cycle.removeIdx E19.order 0, offset := 0,
  heights := fun s => if s = sQ.suit then E19.heights s + 1 else E19.heights s }

def E21 : EState := { E20 with
  order := Cycle.removeIdx E20.order 0, offset := 0,
  heights := fun s => if s = sK.suit then E20.heights s + 1 else E20.heights s }

/-! ## The image clauses (witness boards realize the right vis) -/

theorem WB1_vis (c : Card) : (WB1.bottomOf c).isSome = E0.vis c := by
  show (WB1.bottomOf c).isSome = (BX.bottomOf c).isSome
  by_cases hc : c = hA
  · rw [hc]; decide
  · by_cases hc2 : c = h5
    · rw [hc2]; decide
    · by_cases hc3 : c = h7
      · rw [hc3]; decide
      · by_cases hc4 : c = s6
        · rw [hc4]; decide
        · have h1 : (WB1.bottomOf c).isSome = false := by
            cases hb : (WB1.bottomOf c).isSome with
            | false => rfl
            | true =>
                have hmm := (WB1_img c).mp hb
                simp only [List.mem_cons, List.not_mem_nil] at hmm
                rcases hmm with rfl | rfl | rfl | rfl | h
                · exact absurd rfl hc
                · exact absurd rfl hc3
                · exact absurd rfl hc4
                · exact absurd rfl hc2
                · exact h.elim
          have h2 : (BX.bottomOf c).isSome = false := by
            cases hb : (BX.bottomOf c).isSome with
            | false => rfl
            | true => rcases (BX_img c).mp hb with hc' | hc' | hc' | hc'
                      · exact absurd hc' hc
                      · exact absurd hc' hc2
                      · exact absurd hc' hc3
                      · exact absurd hc' hc4
          rw [h1, h2]

theorem WB2_vis (c : Card) : (WB2.bottomOf c).isSome = E4.vis c := by
  show (WB2.bottomOf c).isSome = (decide (c ≠ hA) && (BX.bottomOf c).isSome)
  by_cases hc : c = hA
  · rw [hc]; decide
  · by_cases hc2 : c = h5
    · rw [hc2]; decide
    · by_cases hc3 : c = h7
      · rw [hc3]; decide
      · by_cases hc4 : c = s6
        · rw [hc4]; decide
        · have h1 : (WB2.bottomOf c).isSome = false := by
            cases hb : (WB2.bottomOf c).isSome with
            | false => rfl
            | true =>
                have hmm := (WB2_img c).mp hb
                simp only [List.mem_cons, List.not_mem_nil] at hmm
                rcases hmm with rfl | rfl | rfl | h
                · exact absurd rfl hc3
                · exact absurd rfl hc4
                · exact absurd rfl hc2
                · exact h.elim
          have h2 : (BX.bottomOf c).isSome = false := by
            cases hb : (BX.bottomOf c).isSome with
            | false => rfl
            | true => rcases (BX_img c).mp hb with hc' | hc' | hc' | hc'
                      · exact absurd hc' hc
                      · exact absurd hc' hc2
                      · exact absurd hc' hc3
                      · exact absurd hc' hc4
          rw [h1, h2, Bool.and_false]

theorem WB3_vis (c : Card) : (WB3.bottomOf c).isSome = E6.vis c := by
  show (WB3.bottomOf c).isSome =
    (decide (c ≠ h5) && (decide (c ≠ hA) && (BX.bottomOf c).isSome))
  by_cases hc : c = hA
  · rw [hc]; decide
  · by_cases hc2 : c = h5
    · rw [hc2]; decide
    · by_cases hc3 : c = h7
      · rw [hc3]; decide
      · by_cases hc4 : c = s6
        · rw [hc4]; decide
        · have h1 : (WB3.bottomOf c).isSome = false := by
            cases hb : (WB3.bottomOf c).isSome with
            | false => rfl
            | true =>
                have hmm := (WB3_img c).mp hb
                simp only [List.mem_cons, List.not_mem_nil] at hmm
                rcases hmm with rfl | rfl | h
                · exact absurd rfl hc3
                · exact absurd rfl hc4
                · exact h.elim
          have h2 : (BX.bottomOf c).isSome = false := by
            cases hb : (BX.bottomOf c).isSome with
            | false => rfl
            | true => rcases (BX_img c).mp hb with hc' | hc' | hc' | hc'
                      · exact absurd hc' hc
                      · exact absurd hc' hc2
                      · exact absurd hc' hc3
                      · exact absurd hc' hc4
          rw [h1, h2, Bool.and_false, Bool.and_false]

theorem WB4_vis (c : Card) : (WB4.bottomOf c).isSome = E7.vis c := by
  show (WB4.bottomOf c).isSome =
    (decide (c ≠ s6) && (decide (c ≠ h5) && (decide (c ≠ hA) && (BX.bottomOf c).isSome)))
  by_cases hc : c = hA
  · rw [hc]; decide
  · by_cases hc2 : c = h5
    · rw [hc2]; decide
    · by_cases hc3 : c = h7
      · rw [hc3]; decide
      · by_cases hc4 : c = s6
        · rw [hc4]; decide
        · have h1 : (WB4.bottomOf c).isSome = false := by
            cases hb : (WB4.bottomOf c).isSome with
            | false => rfl
            | true => exact absurd (List.mem_singleton.mp ((WB4_img c).mp hb)) hc3
          have h2 : (BX.bottomOf c).isSome = false := by
            cases hb : (BX.bottomOf c).isSome with
            | false => rfl
            | true => rcases (BX_img c).mp hb with hc' | hc' | hc' | hc'
                      · exact absurd hc' hc
                      · exact absurd hc' hc2
                      · exact absurd hc' hc3
                      · exact absurd hc' hc4
          rw [h1, h2, Bool.and_false, Bool.and_false, Bool.and_false]

theorem E0_real : E0.realizedBy WB1 := ⟨WB1_fits, WB1_vis⟩
theorem E4_real : E4.realizedBy WB2 := ⟨WB2_fits, WB2_vis⟩
theorem E6_real : E6.realizedBy WB3 := ⟨WB3_fits, WB3_vis⟩
theorem E7_real : E7.realizedBy WB4 := ⟨WB4_fits, WB4_vis⟩

/-! ## The line -/

theorem dstep (e : EState) (c : Card) (hrk : c.rank.toIdx = e.heights c.suit)
    (hord : e.order[0]? = some c) :
    eStep e (.deckStack c) { e with
      order := Cycle.removeIdx e.order 0, offset := 0,
      heights := fun s => if s = c.suit then e.heights s + 1 else e.heights s } := by
  simp only [eStep]
  exact ⟨hrk, 0, hord, rfl⟩

theorem pstep (e : EState) (c : Card) (bd : Board)
    (hvis : e.vis c = true) (hrk : c.rank.toIdx = e.heights c.suit)
    (hbd : e.realizedBy bd) (htop : bd.topOf (Sum.inr c) = none) :
    eStep e (.pileStack c) { e with
      vis := fun c' => decide (c' ≠ c) && e.vis c',
      heights := fun s => if s = c.suit then e.heights s + 1 else e.heights s } := by
  simp only [eStep]
  exact ⟨hvis, hrk, bd, hbd, htop, trivial⟩

theorem step1 : eStep E0 (.pileStack hA) E1 :=
  pstep E0 hA WB1 (by rfl) (by rfl) E0_real (by decide)
theorem step2 : eStep E1 (.deckStack h2) E2 := dstep E1 h2 (by rfl) (by rfl)
theorem step3 : eStep E2 (.deckStack h3) E3 := dstep E2 h3 (by rfl) (by rfl)
theorem step4 : eStep E3 (.deckStack h4) E4 := dstep E3 h4 (by rfl) (by rfl)
theorem step5 : eStep E4 (.pileStack h5) E5 :=
  pstep E4 h5 WB2 (by rfl) (by rfl) E4_real (by decide)
theorem step6 : eStep E5 (.deckStack h6) E6 := dstep E5 h6 (by rfl) (by rfl)
theorem step7 : eStep E6 (.pileStack s6) E7 :=
  pstep E6 s6 WB3 (by rfl) (by rfl) E6_real (by decide)
theorem step8 : eStep E7 (.pileStack h7) E8 :=
  pstep E7 h7 WB4 (by rfl) (by rfl) E7_real (by decide)
theorem step9 : eStep E8 (.deckStack h8) E9 := dstep E8 h8 (by rfl) (by rfl)
theorem step10 : eStep E9 (.deckStack h9) E10 := dstep E9 h9 (by rfl) (by rfl)
theorem step11 : eStep E10 (.deckStack h10) E11 := dstep E10 h10 (by rfl) (by rfl)
theorem step12 : eStep E11 (.deckStack hJ) E12 := dstep E11 hJ (by rfl) (by rfl)
theorem step13 : eStep E12 (.deckStack hQ) E13 := dstep E12 hQ (by rfl) (by rfl)
theorem step14 : eStep E13 (.deckStack hK) E14 := dstep E13 hK (by rfl) (by rfl)
theorem step15 : eStep E14 (.deckStack s7) E15 := dstep E14 s7 (by rfl) (by rfl)
theorem step16 : eStep E15 (.deckStack s8) E16 := dstep E15 s8 (by rfl) (by rfl)
theorem step17 : eStep E16 (.deckStack s9) E17 := dstep E16 s9 (by rfl) (by rfl)
theorem step18 : eStep E17 (.deckStack s10) E18 := dstep E17 s10 (by rfl) (by rfl)
theorem step19 : eStep E18 (.deckStack sJ) E19 := dstep E18 sJ (by rfl) (by rfl)
theorem step20 : eStep E19 (.deckStack sQ) E20 := dstep E19 sQ (by rfl) (by rfl)
theorem step21 : eStep E20 (.deckStack sK) E21 := dstep E20 sK (by rfl) (by rfl)

def PLAY : List EMove :=
  [.pileStack hA, .deckStack h2, .deckStack h3, .deckStack h4, .pileStack h5,
   .deckStack h6, .pileStack s6, .pileStack h7, .deckStack h8, .deckStack h9,
   .deckStack h10, .deckStack hJ, .deckStack hQ, .deckStack hK, .deckStack s7,
   .deckStack s8, .deckStack s9, .deckStack s10, .deckStack sJ, .deckStack sQ, .deckStack sK]

theorem line : eRun (toEngine stN) PLAY E21 := by
  have r0 : eRun E21 [] E21 := rfl
  have r1 : eRun E20 [.deckStack sK] E21 := ⟨E21, step21, r0⟩
  have r2 : eRun E19 [.deckStack sQ, .deckStack sK] E21 := ⟨E20, step20, r1⟩
  have r3 : eRun E18 [.deckStack sJ, .deckStack sQ, .deckStack sK] E21 := ⟨E19, step19, r2⟩
  have r4 : eRun E17 [.deckStack s10, .deckStack sJ, .deckStack sQ, .deckStack sK] E21 :=
    ⟨E18, step18, r3⟩
  have r5 : eRun E16 [.deckStack s9, .deckStack s10, .deckStack sJ, .deckStack sQ,
    .deckStack sK] E21 := ⟨E17, step17, r4⟩
  have r6 : eRun E15 [.deckStack s8, .deckStack s9, .deckStack s10, .deckStack sJ,
    .deckStack sQ, .deckStack sK] E21 := ⟨E16, step16, r5⟩
  have r7 : eRun E14 [.deckStack s7, .deckStack s8, .deckStack s9, .deckStack s10,
    .deckStack sJ, .deckStack sQ, .deckStack sK] E21 := ⟨E15, step15, r6⟩
  have r8 : eRun E13 [.deckStack hK, .deckStack s7, .deckStack s8, .deckStack s9,
    .deckStack s10, .deckStack sJ, .deckStack sQ, .deckStack sK] E21 := ⟨E14, step14, r7⟩
  have r9 : eRun E12 [.deckStack hQ, .deckStack hK, .deckStack s7, .deckStack s8,
    .deckStack s9, .deckStack s10, .deckStack sJ, .deckStack sQ, .deckStack sK] E21 :=
    ⟨E13, step13, r8⟩
  have r10 : eRun E11 [.deckStack hJ, .deckStack hQ, .deckStack hK, .deckStack s7,
    .deckStack s8, .deckStack s9, .deckStack s10, .deckStack sJ, .deckStack sQ,
    .deckStack sK] E21 := ⟨E12, step12, r9⟩
  have r11 : eRun E10 [.deckStack h10, .deckStack hJ, .deckStack hQ, .deckStack hK,
    .deckStack s7, .deckStack s8, .deckStack s9, .deckStack s10, .deckStack sJ,
    .deckStack sQ, .deckStack sK] E21 := ⟨E11, step11, r10⟩
  have r12 : eRun E9 [.deckStack h9, .deckStack h10, .deckStack hJ, .deckStack hQ,
    .deckStack hK, .deckStack s7, .deckStack s8, .deckStack s9, .deckStack s10,
    .deckStack sJ, .deckStack sQ, .deckStack sK] E21 := ⟨E10, step10, r11⟩
  have r13 : eRun E8 [.deckStack h8, .deckStack h9, .deckStack h10, .deckStack hJ,
    .deckStack hQ, .deckStack hK, .deckStack s7, .deckStack s8, .deckStack s9,
    .deckStack s10, .deckStack sJ, .deckStack sQ, .deckStack sK] E21 :=
    ⟨E9, step9, r12⟩
  have r14 : eRun E7 [.pileStack h7, .deckStack h8, .deckStack h9, .deckStack h10,
    .deckStack hJ, .deckStack hQ, .deckStack hK, .deckStack s7, .deckStack s8,
    .deckStack s9, .deckStack s10, .deckStack sJ, .deckStack sQ, .deckStack sK] E21 :=
    ⟨E8, step8, r13⟩
  have r15 : eRun E6 [.pileStack s6, .pileStack h7, .deckStack h8, .deckStack h9,
    .deckStack h10, .deckStack hJ, .deckStack hQ, .deckStack hK, .deckStack s7,
    .deckStack s8, .deckStack s9, .deckStack s10, .deckStack sJ, .deckStack sQ,
    .deckStack sK] E21 := ⟨E7, step7, r14⟩
  have r16 : eRun E5 [.deckStack h6, .pileStack s6, .pileStack h7, .deckStack h8,
    .deckStack h9, .deckStack h10, .deckStack hJ, .deckStack hQ, .deckStack hK,
    .deckStack s7, .deckStack s8, .deckStack s9, .deckStack s10, .deckStack sJ,
    .deckStack sQ, .deckStack sK] E21 := ⟨E6, step6, r15⟩
  have r17 : eRun E4 [.pileStack h5, .deckStack h6, .pileStack s6, .pileStack h7,
    .deckStack h8, .deckStack h9, .deckStack h10, .deckStack hJ, .deckStack hQ,
    .deckStack hK, .deckStack s7, .deckStack s8, .deckStack s9, .deckStack s10,
    .deckStack sJ, .deckStack sQ, .deckStack sK] E21 := ⟨E5, step5, r16⟩
  have r18 : eRun E3 [.deckStack h4, .pileStack h5, .deckStack h6, .pileStack s6,
    .pileStack h7, .deckStack h8, .deckStack h9, .deckStack h10, .deckStack hJ,
    .deckStack hQ, .deckStack hK, .deckStack s7, .deckStack s8, .deckStack s9,
    .deckStack s10, .deckStack sJ, .deckStack sQ, .deckStack sK] E21 :=
    ⟨E4, step4, r17⟩
  have r19 : eRun E2 [.deckStack h3, .deckStack h4, .pileStack h5, .deckStack h6,
    .pileStack s6, .pileStack h7, .deckStack h8, .deckStack h9, .deckStack h10,
    .deckStack hJ, .deckStack hQ, .deckStack hK, .deckStack s7, .deckStack s8,
    .deckStack s9, .deckStack s10, .deckStack sJ, .deckStack sQ, .deckStack sK] E21 :=
    ⟨E3, step3, r18⟩
  have r20 : eRun E1 [.deckStack h2, .deckStack h3, .deckStack h4, .pileStack h5,
    .deckStack h6, .pileStack s6, .pileStack h7, .deckStack h8, .deckStack h9,
    .deckStack h10, .deckStack hJ, .deckStack hQ, .deckStack hK, .deckStack s7,
    .deckStack s8, .deckStack s9, .deckStack s10, .deckStack sJ, .deckStack sQ,
    .deckStack sK] E21 := ⟨E2, step2, r19⟩
  have r21 : eRun (toEngine stN) [.pileStack hA, .deckStack h2, .deckStack h3,
    .deckStack h4, .pileStack h5, .deckStack h6, .pileStack s6, .pileStack h7,
    .deckStack h8, .deckStack h9, .deckStack h10, .deckStack hJ, .deckStack hQ,
    .deckStack hK, .deckStack s7, .deckStack s8, .deckStack s9, .deckStack s10,
    .deckStack sJ, .deckStack sQ, .deckStack sK] E21 := ⟨E1, step1, r20⟩
  exact r21

theorem E21_win : E21.isWin = true := by
  have h := List.all_eq_true (l := Suit.all) (p := fun s => decide (E21.heights s = 13))
  refine h.mpr ?_
  intro s _
  rcases s with ⟨col, p⟩
  cases col <;> cases p <;> rfl

/-! ## The refutation (HISTORICAL)

`toEngine_lifts` — the draw-1 lift, DELETED from Bridge.lean on
2026-09-13 in the laundering disposal — was refuted by exactly the
facts above: `stN` is WF (`stN_wf`), draw-1 (`rfl`), the abstract game
wins `PLAY` (`line`, `E21_win`), and the model engine cannot
(`stN_notSolvable`).  The deleted statement is archived as fenced text
in FARM.md's REFUTED section (item 2, together with `engine_iff`,
which falls transitively).  The former `lift_false : False` corollary
cited the deleted constant by design; this file now carries only the
self-contained, axiom-clean countermodel facts. -/

/-- info: 'stN_wf' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms stN_wf

/-- info: 'stN_notSolvable' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms stN_notSolvable

/-- info: 'line' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms line

/-- info: 'E21_win' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms E21_win




