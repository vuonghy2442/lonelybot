import Klondike.Bridge

/-! Scratch: `toEngine_simulates` WITHOUT a WF hypothesis is UNSOUND.

Witness `stS`: a garbage-deal state whose board seats ♥Q on ♥K (same
color — an edge `board_edges` rejects, so the state is not WF), with
♥-height 11 (♥Q next), the other suits complete.

- The MODEL wins in two engine moves: `pileStack ♥Q`, then `pileStack ♥K`.
- The ABSTRACT game is frozen: ♥Q is unseatable in ANY realizing board,
  so `realizedBy` fails for every board and every witness-demanding
  `eStep` guard is false.
- Hence no abstract play at all, and `(toEngine stS).isWin = false`. -/

namespace SimWitness

abbrev heQ : Card := ⟨Suit.heart, Rank.queen⟩
abbrev heK : Card := ⟨Suit.heart, Rank.king⟩

def bdS : Board where
  topOf := fun b =>
    if b = Sum.inr heK then some heQ
    else if b = Sum.inl Anchor.p0 then some heK
    else none
  inj := by
    intro b₁ b₂ c h₁ h₂
    by_cases hb : b₁ = Sum.inr heK
    · subst hb
      rw [if_pos rfl] at h₁
      rw [Option.some.injEq] at h₁
      subst h₁
      by_cases hb₂ : b₂ = Sum.inr heK
      · exact hb₂.symm
      · rw [if_neg hb₂] at h₂
        by_cases hb₃ : b₂ = Sum.inl Anchor.p0
        · subst hb₃
          rw [if_pos rfl] at h₂
          simp at h₂
        · rw [if_neg hb₃] at h₂
          simp at h₂
    · rw [if_neg hb] at h₁
      by_cases hb₃ : b₁ = Sum.inl Anchor.p0
      · subst hb₃
        rw [if_pos rfl] at h₁
        rw [Option.some.injEq] at h₁
        subst h₁
        by_cases hb₂ : b₂ = Sum.inr heK
        · rw [if_pos hb₂] at h₂
          simp at h₂
        · rw [if_neg hb₂] at h₂
          by_cases hb₄ : b₂ = Sum.inl Anchor.p0
          · exact hb₄.symm
          · rw [if_neg hb₄] at h₂
            simp at h₂
      · rw [if_neg hb₃] at h₁
        simp at h₁

def stS : State where
  deal := ⟨fun _ => [], []⟩
  board := bdS
  heights := fun s => if s = Suit.heart then 11 else 13
  depths := fun _ => 0
  stock := ⟨[], 0⟩
  drawStep := 1

/-- The state is not WF (the ♥Q-on-♥K edge is neither deal-adjacent,
`canSitOn`-legal, nor on an anchor). -/
example : ¬ stS.WF := by
  intro hwf
  have h1 : bdS.topOf (Sum.inr heK) = some heQ := by decide
  obtain ⟨-, hdisj⟩ := hwf.board_edges (Sum.inr heK) heQ h1
  rcases hdisj with ⟨a, t, rest, hpiles⟩ | ⟨_, hcs⟩
  · have hp : (stS.deal.piles a) = [] := rfl
    rw [hp] at hpiles
    simp at hpiles
  · have hfalse : canSitOn heQ heK = false := by decide
    rw [hfalse] at hcs
    exact Bool.noConfusion hcs

/-- The model wins: two engine `pileStack`s. -/
theorem stS_model_wins :
    ∃ st', stS.run [Move.pileStack heQ, Move.pileStack heK] = some st' ∧
      st'.isWin = true := by
  refine ⟨_, rfl, rfl⟩

/-- No board realizes the projection: ♥Q is unseatable. -/
theorem stS_unrealizable (bd : Board) : ¬ (toEngine stS).realizedBy bd := by
  rintro ⟨hfits, himg⟩
  -- bd seats ♥Q somewhere (its image must agree with stS's visible set):
  have hvq : (bdS.bottomOf heQ).isSome = true := by
    have h1 : bdS.topOf (Sum.inr heK) = some heQ := by decide
    have h2 : bdS.bottomOf heQ = some (Sum.inr heK) := (Board.bottomOf_eq _ _ _).mpr h1
    rw [h2]
    rfl
  have hq : (bd.bottomOf heQ).isSome = true := by
    have h := himg heQ
    rw [h]
    exact hvq
  simp only [Option.isSome_iff_exists] at hq
  obtain ⟨b, hb⟩ := hq
  have htb : bd.topOf b = some heQ := (Board.bottomOf_eq bd heQ b).mp hb
  have hfit := hfits b heQ htb
  cases b with
  | inl a =>
      rcases hfit with hking | hhead
      · have hr : heQ.rank = Rank.queen := rfl
        rw [hr] at hking
        exact absurd hking (by decide)
      · have hp : ((toEngine stS).deal.piles a) = [] := rfl
        rw [hp] at hhead
        simp at hhead
  | inr d =>
      rcases hfit with ⟨a, t, rest, hpiles⟩ | ⟨hvisd, hcs⟩
      · have hp : ((toEngine stS).deal.piles a) = [] := rfl
        rw [hp] at hpiles
        simp at hpiles
      · -- d visible in stS ⇒ d ∈ {heQ, heK}; neither seats ♥Q
        have hvs : (bdS.bottomOf d).isSome = true := by
          have h := himg d
          show (toEngine stS).vis d = true
          rw [← h]
          exact hvisd
        simp only [Option.isSome_iff_exists] at hvs
        obtain ⟨b', hb'⟩ := hvs
        have htb2 : bdS.topOf b' = some d := (Board.bottomOf_eq bdS d b').mp hb'
        by_cases hbr : b' = Sum.inr heK
        · have h1 : bdS.topOf (Sum.inr heK) = some heQ := by decide
          rw [hbr, h1] at htb2
          have hdq : d = heQ := (Option.some.inj htb2).symm
          have hfalse : canSitOn heQ heQ = false := by decide
          rw [hdq, hfalse] at hcs
          exact Bool.noConfusion hcs
        · by_cases hbr2 : b' = Sum.inl Anchor.p0
          · have h2 : bdS.topOf (Sum.inl Anchor.p0) = some heK := by decide
            rw [hbr2, h2] at htb2
            have hdk : d = heK := (Option.some.inj htb2).symm
            have hfalse : canSitOn heQ heK = false := by decide
            rw [hdk, hfalse] at hcs
            exact Bool.noConfusion hcs
          · have h3 : bdS.topOf b' = none := by
              show (if b' = Sum.inr heK then some heQ
                  else if b' = Sum.inl Anchor.p0 then some heK else none) = none
              rw [if_neg hbr, if_neg hbr2]
            rw [h3] at htb2
            simp at htb2

/-- No abstract move fires at all. -/
theorem stS_no_eStep (m : EMove) (e' : EState) : ¬ eStep (toEngine stS) m e' := by
  cases m with
  | pileStack c =>
      intro h
      simp only [eStep] at h
      obtain ⟨_, _, bd, hbd, _, _⟩ := h
      exact stS_unrealizable bd hbd
  | deckPile c =>
      intro h
      simp only [eStep] at h
      obtain ⟨⟨bd, hbd, _, _⟩, _, _, _⟩ := h
      exact stS_unrealizable bd hbd
  | deckStack c =>
      intro h
      simp only [eStep] at h
      obtain ⟨_, i, hget, _⟩ := h
      have hnone : ((toEngine stS).order)[i]? = none := rfl
      rw [hnone] at hget
      simp at hget
  | stackPile c =>
      intro h
      simp only [eStep] at h
      obtain ⟨_, ⟨bd, hbd, _, _⟩, _⟩ := h
      exact stS_unrealizable bd hbd
  | reveal c =>
      intro h
      simp only [eStep] at h
      obtain ⟨_, bd, _, _, hbd, _, _, _, _⟩ := h
      exact stS_unrealizable bd hbd

/-- Hence no abstract play wins. -/
theorem stS_no_abstract_win :
    ¬ ∃ eplay w, eRun (toEngine stS) eplay w ∧ w.isWin = true := by
  rintro ⟨eplay, w, hrun, hwin⟩
  induction eplay generalizing w with
  | nil =>
      have heq : toEngine stS = w := hrun
      subst heq
      have hfalse : (toEngine stS).isWin = false := rfl
      rw [hfalse] at hwin
      exact Bool.noConfusion hwin
  | cons m ms ih =>
      obtain ⟨e'', hstep, hrest⟩ := hrun
      exact absurd hstep (stS_no_eStep m e'')

/-- The current `toEngine_simulates` statement (no WF hypothesis) is
refuted: model wins, abstract cannot. -/
example :
    ¬ (∀ (st st' : State) (play : List Move),
        (∀ m ∈ play, m.isEngine = true) → st.run play = some st' →
        ∃ eplay w, eRun (toEngine st) eplay w ∧ w.isWin = st'.isWin) := by
  intro h
  obtain ⟨st', hrun, hwin⟩ := stS_model_wins
  have heng : ∀ m ∈ [Move.pileStack heQ, Move.pileStack heK], m.isEngine = true := by
    intro m hm
    simp only [List.mem_cons] at hm
    rcases hm with rfl | hm
    · rfl
    · rcases hm with rfl | hm
      · rfl
      · cases hm
  obtain ⟨eplay, w, hrun', hw⟩ :=
    h stS st' [Move.pileStack heQ, Move.pileStack heK] heng hrun
  apply stS_no_abstract_win
  refine ⟨eplay, w, hrun', ?_⟩
  rw [hw, hwin]

end SimWitness
