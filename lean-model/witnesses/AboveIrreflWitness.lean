import Klondike.Initial

/-!
  Scratch (Wave-4 rescope evidence): `aboveOf_irrefl` as staged
  (WF-only) is FALSE.  Witness `wState`: a WF state whose matching has
  a 2-cycle — `♠6` on `♥5` via deal-adjacency (pile p1 dealt
  `[♥5, ♠6]`), `♥5` on `♠6` via canSitOn (5+1=6, colors differ).
  `aboveOf ♥5 = [♥5, ♠6]` contains `♥5`.
-/

namespace AboveWitness

def h5 : Card := ⟨Suit.heart, Rank.five⟩
def s6 : Card := ⟨Suit.spade, Rank.six⟩

/-- The deal list: universe order with `♥5` and `♠6` moved to
positions 1–2 (so pile p1 is dealt `[♥5, ♠6]`). -/
def wl : List Card :=
  [⟨Suit.heart, Rank.ace⟩, ⟨Suit.heart, Rank.five⟩, ⟨Suit.spade, Rank.six⟩,
   ⟨Suit.heart, Rank.two⟩, ⟨Suit.heart, Rank.three⟩, ⟨Suit.heart, Rank.four⟩,
   ⟨Suit.heart, Rank.six⟩, ⟨Suit.heart, Rank.seven⟩, ⟨Suit.heart, Rank.eight⟩,
   ⟨Suit.heart, Rank.nine⟩, ⟨Suit.heart, Rank.ten⟩, ⟨Suit.heart, Rank.jack⟩,
   ⟨Suit.heart, Rank.queen⟩, ⟨Suit.heart, Rank.king⟩,
   ⟨Suit.spade, Rank.ace⟩, ⟨Suit.spade, Rank.two⟩, ⟨Suit.spade, Rank.three⟩,
   ⟨Suit.spade, Rank.four⟩, ⟨Suit.spade, Rank.five⟩, ⟨Suit.spade, Rank.seven⟩,
   ⟨Suit.spade, Rank.eight⟩, ⟨Suit.spade, Rank.nine⟩, ⟨Suit.spade, Rank.ten⟩,
   ⟨Suit.spade, Rank.jack⟩, ⟨Suit.spade, Rank.queen⟩, ⟨Suit.spade, Rank.king⟩,
   ⟨Suit.diamond, Rank.ace⟩, ⟨Suit.diamond, Rank.two⟩, ⟨Suit.diamond, Rank.three⟩,
   ⟨Suit.diamond, Rank.four⟩, ⟨Suit.diamond, Rank.five⟩, ⟨Suit.diamond, Rank.six⟩,
   ⟨Suit.diamond, Rank.seven⟩, ⟨Suit.diamond, Rank.eight⟩, ⟨Suit.diamond, Rank.nine⟩,
   ⟨Suit.diamond, Rank.ten⟩, ⟨Suit.diamond, Rank.jack⟩, ⟨Suit.diamond, Rank.queen⟩,
   ⟨Suit.diamond, Rank.king⟩,
   ⟨Suit.club, Rank.ace⟩, ⟨Suit.club, Rank.two⟩, ⟨Suit.club, Rank.three⟩,
   ⟨Suit.club, Rank.four⟩, ⟨Suit.club, Rank.five⟩, ⟨Suit.club, Rank.six⟩,
   ⟨Suit.club, Rank.seven⟩, ⟨Suit.club, Rank.eight⟩, ⟨Suit.club, Rank.nine⟩,
   ⟨Suit.club, Rank.ten⟩, ⟨Suit.club, Rank.jack⟩, ⟨Suit.club, Rank.queen⟩,
   ⟨Suit.club, Rank.king⟩]

theorem wl_length : wl.length = 52 := by decide

theorem wl_noDup : noDupCards wl := by
  intro i j hi hj heq
  rw [wl_length] at hi hj
  have hall : ∀ i ∈ List.range 52, ∀ j ∈ List.range 52, wl[i]? = wl[j]? → i = j := by
    decide
  exact hall i (List.mem_range.mpr hi) j (List.mem_range.mpr hj) heq

def wDeal : Deal := Deal.ofList wl

theorem wDeal_WF : wDeal.WF := Deal.ofList_wf wl_length wl_noDup

/-- The 2-cycle board: `♠6` sits on `♥5`, `♥5` sits on `♠6`. -/
def wBoard : Board where
  topOf := fun b =>
    match b with
    | Sum.inl _ => none
    | Sum.inr x => if x = h5 then some s6 else if x = s6 then some h5 else none
  inj := by
    intro b₁ b₂ c h₁ h₂
    cases b₁ with
    | inl a => simp at h₁
    | inr x₁ =>
        cases b₂ with
        | inl a => simp at h₂
        | inr x₂ =>
            have h₁' : (if x₁ = h5 then some s6 else if x₁ = s6 then some h5 else none)
                = some c := h₁
            have h₂' : (if x₂ = h5 then some s6 else if x₂ = s6 then some h5 else none)
                = some c := h₂
            by_cases e₁ : x₁ = h5
            · rw [if_pos e₁] at h₁'
              by_cases e₂ : x₂ = h5
              · rw [if_pos e₂] at h₂'
                rw [Option.some.injEq] at h₁' h₂'
                exact congrArg Sum.inr (e₁.trans e₂.symm)
              · by_cases e₂' : x₂ = s6
                · rw [if_neg e₂, if_pos e₂'] at h₂'
                  rw [Option.some.injEq] at h₁' h₂'
                  exact absurd (h₁'.trans h₂'.symm) (by decide)
                · rw [if_neg e₂, if_neg e₂'] at h₂'; simp at h₂'
            · by_cases e₁' : x₁ = s6
              · rw [if_neg e₁, if_pos e₁'] at h₁'
                by_cases e₂ : x₂ = h5
                · rw [if_pos e₂] at h₂'
                  rw [Option.some.injEq] at h₁' h₂'
                  exact absurd (h₁'.trans h₂'.symm) (by decide)
                · by_cases e₂' : x₂ = s6
                  · rw [if_neg e₂, if_pos e₂'] at h₂'
                    rw [Option.some.injEq] at h₁' h₂'
                    exact congrArg Sum.inr (e₁'.trans e₂'.symm)
                  · rw [if_neg e₂, if_neg e₂'] at h₂'; simp at h₂'
              · rw [if_neg e₁, if_neg e₁'] at h₁'; simp at h₁'

def wState : State where
  deal := wDeal
  board := wBoard
  heights := fun _ => 0
  depths := fun _ => 0
  stock := ⟨[], 0⟩
  drawStep := 1

theorem wState_WF : wState.WF := by
  refine ⟨wDeal_WF, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a
    show (0 : Nat) ≤ (wDeal.piles a).length
    exact Nat.zero_le _
  · intro b c hb
    cases b with
    | inl a => simp [wState, wBoard] at hb
    | inr x =>
        have hb' : (if x = h5 then some s6 else if x = s6 then some h5 else none)
            = some c := hb
        by_cases ex : x = h5
        · rw [if_pos ex, Option.some.injEq] at hb'
          subst hb'
          subst ex
          refine ⟨by decide, ?_⟩
          exact Or.inl ⟨Anchor.p1, [], [], by decide, Or.inr (by decide)⟩
        · by_cases ex' : x = s6
          · rw [if_neg ex, if_pos ex', Option.some.injEq] at hb'
            subst hb'
            subst ex'
            exact ⟨by decide, Or.inr ⟨by decide, by decide⟩⟩
          · rw [if_neg ex, if_neg ex'] at hb'
            simp at hb'
  · intro c _
    show wState.stock.posOf c = none
    rfl
  · intro c hc
    simp only [State.onFound] at hc
    have h0 : wState.heights c.suit = 0 := rfl
    rw [h0] at hc
    exact absurd (of_decide_eq_true hc) (by omega)
  · intro c hc
    have h0 : wState.heights c.suit = 0 := rfl
    rw [h0] at hc
    omega
  · intro c _ a hcm
    have hnil : wState.hidden a = [] := rfl
    rw [hnil] at hcm
    simp at hcm
  · intro s
    show (0 : Nat) ≤ 13
    exact Nat.zero_le 13
  · show (0 : Nat) ≤ ([] : List Card).length
    exact Nat.zero_le _
  · exact Nat.zero_lt_one
  · show noDupCards ([] : List Card) ∧ ∀ c ∈ ([] : List Card), c ∈ wState.deal.stock
    refine ⟨?_, ?_⟩
    · intro i j hi _ _
      simp at hi
    · intro c hc
      simp at hc

/-- The 2-cycle: `aboveOf ♥5` contains `♥5`. -/
theorem w_cycle : h5 ∈ wBoard.aboveOf h5 := by decide

end AboveWitness

/-- info: 'AboveWitness.wState_WF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AboveWitness.wState_WF

/-- info: 'AboveWitness.w_cycle' depends on axioms: [propext] -/
#guard_msgs in
#print axioms AboveWitness.w_cycle
