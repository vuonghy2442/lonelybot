import Orig2.ForkInrExp
import Orig2.ForkPermRefute

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-!
# InrExp2 — the `inr` exposure residual is FALSE: a 3-letter shortest witness

READ-ONLY scratch card (`Temp/`).  No source edit, no commit.  No `sorry`,
no `Classical.choice`, no `native_decide`; axiom battery at the tail.

`BaseEn.InrExposeResidual` (`Orig2/ForkBaseEnabling.lean:269`) — and its head
case `InrExp.InrExpHead` (`Orig2/ForkInrExp.lean:299`) — claim:

> if a play contains `raise c ; γ ; pull c (inr z)` with `γ` read-safe for `c`
> and seat-inert on `inr z`, and `z` is buried at the raise's origin
> (`A.pileOfTop z = none`) but exposed somewhere in the interior, then the play
> strictly shortens.

This is refuted.  The board below has the **3-letter shortest** play

```text
raise J♠ ; slide J♣ onto Q♥ ; pull J♠ onto Q♦
```

* `u`: `p0 = [Q♥, J♠]`, `p1 = [Q♦, J♣]`, all other cards hidden in `p2`,
  foundations ♠A..10, ♥A..9, ♦A..9, ♣A..9, empty stock and waste.
* `raise J♠` empties the *top* of `p0`, exposing `Q♥` (which is exactly the
  pile the interior slide wants as a base);
* `slide J♣ onto Q♥` is legal **only because** `Q♥` was uncovered by the
  raise, and it exposes the pull's base `Q♦`;
* `pull J♠ onto Q♦` lands.

`J♠` is the *only* legal letter at `u`, and after it the foundation ledger
(`♠A..J♠` vs the endpoint's `♠A..10`) forbids every letter but `pull J♠`, which
can only land on `Q♥` — leaving `p0 = [Q♥, J♠] ≠ v.p0 = [Q♥, J♣]`.

The interior letter is `ReadSafe J♠` and `SeatInert (inr Q♦)`, `Q♦` is buried at
`u` and at the raise's image, and exposed at the pre-pull state.  So the
residual's hypotheses all hold while the conclusion (a shorter play) fails.

The obstruction: the exposing slide's **base is the pile the raise emptied** —
`Q♥` does not top any pile at `u`.  Hence the intended replacement
`slide J♣ onto Q♥ ; slide J♠ onto Q♦` (2 letters) is *not a play* at `u`.
-/

namespace InrExpRefute

open MountainKit
open CommuteStep

/-! ## §1. The board -/

/-- The raised card `c`. -/
def cJ : Card := ⟨.spade, .jack⟩
/-- The head of the covering slide `w`. -/
def cZj : Card := ⟨.club, .jack⟩
/-- The covering slide's base — uncovered *by the raise* (`z'`). -/
def cQh : Card := ⟨.heart, .queen⟩
/-- The pull's base `z`. -/
def cQd : Card := ⟨.diamond, .queen⟩

def foundOf : Suit → List Card
  | .spade => Suit.spade.upCards.take 10
  | .heart => Suit.heart.upCards.take 9
  | .diamond => Suit.diamond.upCards.take 9
  | .club => Suit.club.upCards.take 9

def junk : List Card :=
  Card.universe.filter (fun c =>
    decide (c ∉ foundOf .spade ∧ c ∉ foundOf .heart ∧ c ∉ foundOf .diamond ∧
      c ∉ foundOf .club ∧ c ≠ cJ ∧ c ≠ cZj ∧ c ≠ cQh ∧ c ≠ cQd))

def u : State :=
  { found := foundOf
    piles := fun a => match a with
      | .p0 => ⟨[], [cQh, cJ]⟩
      | .p1 => ⟨[], [cQd, cZj]⟩
      | .p2 => ⟨junk, []⟩
      | _ => ⟨[], []⟩
    stock := []
    waste := []
    drawStep := 1 }

def v : State :=
  { found := foundOf
    piles := fun a => match a with
      | .p0 => ⟨[], [cQh, cZj]⟩
      | .p1 => ⟨[], [cQd, cJ]⟩
      | .p2 => ⟨junk, []⟩
      | _ => ⟨[], []⟩
    stock := []
    waste := []
    drawStep := 1 }

/-! ## §2. WF and the two endpoints differ -/

theorem u_wf : u.WF := by
  refine ⟨?_, ?_, ?_, by decide⟩
  · intro s
    cases s with
    | spade => exact ⟨10, rfl⟩
    | heart => exact ⟨9, rfl⟩
    | diamond => exact ⟨9, rfl⟩
    | club => exact ⟨9, rfl⟩
  · intro a
    cases a <;> decide
  · intro c _
    rcases c with ⟨s, r⟩
    cases s <;> cases r <;> decide

theorem u_ne_v : u ≠ v := by
  intro h
  have hp : u.piles .p0 = v.piles .p0 := by rw [h]
  simp [u, v] at hp
  exact absurd hp (by decide)

theorem v_piles_p0 : v.piles .p0 = ⟨[], [cQh, cZj]⟩ := by decide
theorem v_piles_p1 : v.piles .p1 = ⟨[], [cQd, cJ]⟩ := by decide
theorem u_piles_p0 : u.piles .p0 = ⟨[], [cQh, cJ]⟩ := by decide

/-! ## §3. The three letters -/

/-- After `raise J♠`. -/
def s1 : State := raiseSt u cJ .p0

/-- After `slide J♣ onto Q♥`. -/
def s2 : State := slideSt s1 cZj (Sum.inr cQh) .p1

/-- After the final `pull J♠ onto Q♦`. -/
def s3 : State := pullSt s2 cJ (Sum.inr cQd)

theorem u_nextUp_J : u.nextUp cJ = true := by decide
theorem u_pileOfTop_J : u.pileOfTop cJ = some .p0 := by decide

theorem s1_piles_p0 : s1.piles .p0 = ⟨[], [cQh]⟩ := by decide
theorem s1_pileHolding_Zj : s1.pileHolding cZj = some .p1 := by decide
theorem s1_canPlace_Zj : s1.canPlace cZj (Sum.inr cQh) = true := by decide
theorem s1_foundTop_J : s1.foundTop cJ.suit = some cJ := by decide
theorem s1_waste : s1.waste = [] := rfl

theorem s2_foundTop_J : s2.foundTop cJ.suit = some cJ := by decide
theorem s2_canPlace_J : s2.canPlace cJ (Sum.inr cQd) = true := by decide

theorem step_raise : State.step u (Move.tabToFound cJ) = some s1 := by
  rw [step_tabToFound_splice u_nextUp_J u_pileOfTop_J]
  rfl

theorem step_slide : State.step s1 (Move.tabToTab cZj (Sum.inr cQh)) = some s2 := by
  rw [State.step]
  rw [s1_pileHolding_Zj]
  rw [s1_canPlace_Zj]
  rfl

theorem step_pull : State.step s2 (Move.foundToTab cJ (Sum.inr cQd)) = some s3 := by
  rw [step_foundToTab_splice s2_foundTop_J s2_canPlace_J]
  rfl

/-- The three letters land exactly on `v`. -/
theorem s3_eq_v : s3 = v := by
  apply State.ext
  · funext s
    cases s with
    | spade => decide
    | heart => decide
    | diamond => decide
    | club => decide
  · funext a
    cases a <;> decide
  · rfl
  · rfl
  · rfl

/-! ## §4. `canSitOn` case analyses at the four live cards -/

theorem canSitOn_J_cases {z : Card} (h : canSitOn cJ z = true) : z = cQh ∨ z = cQd := by
  rcases z with ⟨s, r⟩
  cases s <;> cases r <;> first | decide | (exact absurd h (by decide))

theorem canSitOn_Zj_cases {z : Card} (h : canSitOn cZj z = true) : z = cQh ∨ z = cQd := by
  rcases z with ⟨s, r⟩
  cases s <;> cases r <;> first | decide | (exact absurd h (by decide))

theorem canSitOn_Qh_cases {z : Card} (h : canSitOn cQh z = true) :
    z = ⟨.spade, .king⟩ ∨ z = ⟨.club, .king⟩ := by
  rcases z with ⟨s, r⟩
  cases s <;> cases r <;> first | decide | (exact absurd h (by decide))

theorem canSitOn_Qd_cases {z : Card} (h : canSitOn cQd z = true) :
    z = ⟨.spade, .king⟩ ∨ z = ⟨.club, .king⟩ := by
  rcases z with ⟨s, r⟩
  cases s <;> cases r <;> first | decide | (exact absurd h (by decide))

/-! ## §5. Nothing is legal at `u` except `raise J♠` -/

theorem u_pileOfTop_Qh : u.pileOfTop cQh = none := by decide
theorem u_pileOfTop_Qd : u.pileOfTop cQd = none := by decide
theorem u_pileOfTop_SK : u.pileOfTop ⟨.spade, .king⟩ = none := by decide
theorem u_pileOfTop_CK : u.pileOfTop ⟨.club, .king⟩ = none := by decide

theorem u_canPlace_J (b : Base) : u.canPlace cJ b = false := by
  cases b with
  | inl a =>
      rw [canPlace_inl_unfold]
      rw [show decide (cJ.rank = Rank.king) = false from by decide, Bool.and_false]
  | inr z =>
      rw [canPlace_inr_eq]
      cases h : u.pileOfTop z with
      | none => rfl
      | some k =>
          cases hs : canSitOn cJ z with
          | false => rfl
          | true =>
              rcases canSitOn_J_cases hs with rfl | rfl
              · rw [u_pileOfTop_Qh] at h; exact absurd h (by simp)
              · rw [u_pileOfTop_Qd] at h; exact absurd h (by simp)

theorem u_canPlace_Zj (b : Base) : u.canPlace cZj b = false := by
  cases b with
  | inl a =>
      rw [canPlace_inl_unfold]
      rw [show decide (cZj.rank = Rank.king) = false from by decide, Bool.and_false]
  | inr z =>
      rw [canPlace_inr_eq]
      cases h : u.pileOfTop z with
      | none => rfl
      | some k =>
          cases hs : canSitOn cZj z with
          | false => rfl
          | true =>
              rcases canSitOn_Zj_cases hs with rfl | rfl
              · rw [u_pileOfTop_Qh] at h; exact absurd h (by simp)
              · rw [u_pileOfTop_Qd] at h; exact absurd h (by simp)

theorem u_canPlace_Qh (b : Base) : u.canPlace cQh b = false := by
  cases b with
  | inl a =>
      rw [canPlace_inl_unfold]
      rw [show decide (cQh.rank = Rank.king) = false from by decide, Bool.and_false]
  | inr z =>
      rw [canPlace_inr_eq]
      cases h : u.pileOfTop z with
      | none => rfl
      | some k =>
          cases hs : canSitOn cQh z with
          | false => rfl
          | true =>
              rcases canSitOn_Qh_cases hs with rfl | rfl
              · rw [u_pileOfTop_SK] at h; exact absurd h (by simp)
              · rw [u_pileOfTop_CK] at h; exact absurd h (by simp)

theorem u_canPlace_Qd (b : Base) : u.canPlace cQd b = false := by
  cases b with
  | inl a =>
      rw [canPlace_inl_unfold]
      rw [show decide (cQd.rank = Rank.king) = false from by decide, Bool.and_false]
  | inr z =>
      rw [canPlace_inr_eq]
      cases h : u.pileOfTop z with
      | none => rfl
      | some k =>
          cases hs : canSitOn cQd z with
          | false => rfl
          | true =>
              rcases canSitOn_Qd_cases hs with rfl | rfl
              · rw [u_pileOfTop_SK] at h; exact absurd h (by simp)
              · rw [u_pileOfTop_CK] at h; exact absurd h (by simp)

theorem u_pileHolding_cases {c : Card} (h : u.pileHolding c ≠ none) :
    c = cQh ∨ c = cJ ∨ c = cQd ∨ c = cZj := by
  cases hh : u.pileHolding c with
  | none => exact absurd hh h
  | some a =>
      have hmem := pileHolding_mem hh
      cases a with
      | p0 =>
          simp [u] at hmem
          rcases hmem with rfl | rfl <;> simp
      | p1 =>
          simp [u] at hmem
          rcases hmem with rfl | rfl <;> simp
      | p2 => simp [u] at hmem
      | p3 => simp [u] at hmem
      | p4 => simp [u] at hmem
      | p5 => simp [u] at hmem
      | p6 => simp [u] at hmem

theorem u_canPlace_false (c : Card) (h : c = cQh ∨ c = cJ ∨ c = cQd ∨ c = cZj)
    (b : Base) : u.canPlace c b = false := by
  rcases h with rfl | rfl | rfl | rfl
  · exact u_canPlace_Qh b
  · exact u_canPlace_J b
  · exact u_canPlace_Qd b
  · exact u_canPlace_Zj b

/-- **NO SLIDE IS LEGAL AT `u`.** -/
theorem u_no_slide (c : Card) (b : Base) : State.step u (Move.tabToTab c b) = none := by
  cases hh : u.pileHolding c with
  | none => simp only [State.step, hh]
  | some a =>
      have hcp := u_canPlace_false c (u_pileHolding_cases (by simp [hh])) b
      simp only [State.step, hh, hcp]
      rfl

/-- **NO DRAW IS LEGAL AT `u`** (empty stock and waste). -/
theorem u_no_draw : State.step u Move.draw = none := rfl

theorem step_waste_none (st : State) (h : st.waste = []) (c : Card) (b : Base) :
    State.step st (Move.wasteToFound c) = none ∧
      State.step st (Move.wasteToTab c b) = none := by
  constructor <;> simp [State.step, State.wasteIs_nil h]

/-- **THE ONLY RAISABLE CARD AT `u` IS `J♠`.** -/
theorem u_raisable_check :
    Card.universe.all (fun c => !(u.nextUp c && (u.pileOfTop c).isSome) || (c == cJ)) = true := by
  decide

theorem u_raisable_J {c : Card} (hnext : u.nextUp c = true) (hpo : u.pileOfTop c ≠ none) :
    c = cJ := by
  have hmem := Card.mem_universe c
  have hall := List.all_eq_true.mp u_raisable_check c hmem
  have hb : (u.nextUp c && (u.pileOfTop c).isSome) = true := by
    rw [hnext]
    cases hp : u.pileOfTop c with
    | none => exact absurd hp hpo
    | some k => rfl
  rw [hb] at hall
  exact beq_iff_eq.mp (by simpa using hall)

/-! ## §6. No single letter takes `u` to `v`, and no pair does either -/

theorem rungAt_v (σ : Suit) : rungAt v σ = rungAt u σ := rfl

theorem rungAt_s1 (σ : Suit) :
    rungAt s1 σ = if σ = cJ.suit then rungAt u σ + 1 else rungAt u σ :=
  rungAt_raiseSt (u := u) (c := cJ) (a := .p0) σ

/-- **NO SINGLE LETTER TAKES `u` TO `v`.** -/
theorem no_one_step (m : Move) : State.step u m ≠ some v := by
  intro h
  cases m with
  | draw => rw [u_no_draw] at h; cases h
  | wasteToFound c =>
      rw [(step_waste_none u rfl c (Sum.inl .p0)).1] at h
      cases h
  | wasteToTab c b =>
      rw [(step_waste_none u rfl c b).2] at h
      cases h
  | tabToTab c b => rw [u_no_slide] at h; cases h
  | tabToFound c =>
      obtain ⟨hnext, a, hpo, hv⟩ := step_tabToFound_inv h
      have hc : c = cJ := u_raisable_J hnext (by simp [hpo])
      subst hc
      have ha : a = .p0 := by rw [u_pileOfTop_J] at hpo; exact (Option.some.inj hpo).symm
      subst ha
      have hp : v.piles .p0 = ⟨[], [cQh]⟩ := by rw [hv]; decide
      rw [v_piles_p0] at hp
      exact absurd hp (by decide)
  | foundToTab c b =>
      obtain ⟨c', hft, hc', hcp, hv⟩ := step_foundToTab_inv h
      have hmem : c ∈ u.found c.suit := by
        unfold State.foundTop at hft
        rw [hc'] at hft
        exact lastOf_mem hft
      have hpos : 0 < rungAt u c.suit := by
        unfold rungAt
        exact List.length_pos_of_mem hmem
      have hgt := rungAt_foundToTab h c.suit
      rw [rungAt_v, ite_eq_left rfl] at hgt
      omega

/-- The pull's landing at `p0` can never be `v`'s `p0`. -/
theorem pull_J_p0_ne (b : Base) :
    ((s1.setFound cJ.suit (chop (s1.found cJ.suit))).putCard cJ b).piles .p0
      ≠ v.piles .p0 := by
  have hT : (s1.setFound cJ.suit (chop (s1.found cJ.suit))).piles .p0
      = ⟨[], [cQh]⟩ := s1_piles_p0
  have htop : ∀ z, (s1.setFound cJ.suit (chop (s1.found cJ.suit))).pileOfTop z
      = s1.pileOfTop z := fun z => rfl
  intro h
  cases b with
  | inl a =>
      rw [putCard_piles_inl] at h
      dsimp only at h
      by_cases ha : a = .p0
      · subst ha
        rw [ite_eq_left rfl] at h
        rw [v_piles_p0] at h
        exact absurd h (by decide)
      · rw [ite_eq_right (fun hh : (.p0 : Anchor) = a => ha hh.symm)] at h
        rw [hT, v_piles_p0] at h
        exact absurd h (by decide)
  | inr z =>
      cases hz : s1.pileOfTop z with
      | none =>
          have hz' : (s1.setFound cJ.suit (chop (s1.found cJ.suit))).pileOfTop z = none := by
            rw [htop z]; exact hz
          rw [show (s1.setFound cJ.suit (chop (s1.found cJ.suit))).putCard cJ (Sum.inr z)
              = (s1.setFound cJ.suit (chop (s1.found cJ.suit))) from by
                simp only [State.putCard, hz']] at h
          rw [hT, v_piles_p0] at h
          exact absurd h (by decide)
      | some k =>
          have hz' : (s1.setFound cJ.suit (chop (s1.found cJ.suit))).pileOfTop z = some k := by
            rw [htop z]; exact hz
          rw [putCard_piles_inr _ _ z k hz'] at h
          dsimp only at h
          by_cases hk : (.p0 : Anchor) = k
          · subst hk
            rw [ite_eq_left rfl] at h
            rw [hT, v_piles_p0] at h
            exact absurd h (by decide)
          · rw [ite_eq_right hk] at h
            rw [hT, v_piles_p0] at h
            exact absurd h (by decide)

/-- **NO PAIR OF LETTERS TAKES `u` TO `v`.** -/
theorem no_two_step (m₁ m₂ : Move) (s : State)
    (h₁ : State.step u m₁ = some s) (h₂ : State.step s m₂ = some v) : False := by
  cases m₁ with
  | draw => rw [u_no_draw] at h₁; cases h₁
  | wasteToFound c =>
      rw [(step_waste_none u rfl c (Sum.inl .p0)).1] at h₁
      cases h₁
  | wasteToTab c b =>
      rw [(step_waste_none u rfl c b).2] at h₁
      cases h₁
  | tabToTab c b => rw [u_no_slide] at h₁; cases h₁
  | foundToTab c b =>
      obtain ⟨c', hft, hc', hcp, hv⟩ := step_foundToTab_inv h₁
      rw [hc'] at hft
      have hmem : c ∈ u.found c.suit := by
        unfold State.foundTop at hft
        exact lastOf_mem hft
      have hpos : 0 < rungAt u c.suit := by
        unfold rungAt
        exact List.length_pos_of_mem hmem
      have hrs : rungAt s c.suit = rungAt u c.suit - 1 := by
        have := rungAt_foundToTab h₁ c.suit
        rwa [ite_eq_left rfl] at this
      cases m₂ with
      | draw =>
          have h := rungAt_draw h₂ c.suit
          rw [rungAt_v, hrs] at h
          omega
      | wasteToFound d =>
          have hw : s.waste = [] := by rw [hv, putCard_waste, setFound_waste]; rfl
          rw [(step_waste_none s hw d (Sum.inl .p0)).1] at h₂
          cases h₂
      | wasteToTab d b₂ =>
          have hw : s.waste = [] := by rw [hv, putCard_waste, setFound_waste]; rfl
          rw [(step_waste_none s hw d b₂).2] at h₂
          cases h₂
      | tabToTab d b₂ =>
          have h := rungAt_tabToTab h₂ c.suit
          rw [rungAt_v, hrs] at h
          omega
      | foundToTab d b₂ =>
          have h := rungAt_foundToTab h₂ c.suit
          rw [rungAt_v, hrs] at h
          by_cases hd : c.suit = d.suit
          · rw [ite_eq_left hd] at h; omega
          · rw [ite_eq_right hd] at h; omega
      | tabToFound d =>
          have h := rungAt_tabToFound h₂ c.suit
          rw [rungAt_v, hrs] at h
          have hds : c.suit = d.suit := by
            by_cases hd : c.suit = d.suit
            · exact hd
            · rw [ite_eq_right hd] at h; omega
          obtain ⟨dnext, hdpo, dv⟩ := (step_tabToFound_inv h₂).2
          have hdtop : v.foundTop c.suit = some d := by
            rw [show v.foundTop c.suit = v.foundTop d.suit from by rw [hds], dv]
            exact (tabToFound_found_trio (st := s) (c := d) (a := dnext) rfl).2.2
          have hctop : v.foundTop c.suit = some c := by
            rw [show v.foundTop c.suit = u.foundTop c.suit from rfl]; exact hft
          have hdc : d = c := Option.some.inj (hdtop.symm.trans hctop)
          rw [hdc] at h₂
          rw [step_tabToFound_of_foundToTab u_wf h₁] at h₂
          exact u_ne_v (Option.some.inj h₂)
  | tabToFound c =>
      obtain ⟨hnext, a, hpo, hs⟩ := step_tabToFound_inv h₁
      have hc : c = cJ := u_raisable_J hnext (by simp [hpo])
      subst hc
      have ha : a = .p0 := by rw [u_pileOfTop_J] at hpo; exact (Option.some.inj hpo).symm
      subst ha
      have hs1 : s = s1 := by rw [hs]; rfl
      subst hs1
      cases m₂ with
      | draw =>
          have h := rungAt_draw h₂ cJ.suit
          rw [rungAt_v, rungAt_s1, ite_eq_left rfl] at h
          omega
      | wasteToFound d =>
          rw [(step_waste_none s1 s1_waste d (Sum.inl .p0)).1] at h₂
          cases h₂
      | wasteToTab d b =>
          rw [(step_waste_none s1 s1_waste d b).2] at h₂
          cases h₂
      | tabToTab d b =>
          have h := rungAt_tabToTab h₂ cJ.suit
          rw [rungAt_v, rungAt_s1, ite_eq_left rfl] at h
          omega
      | tabToFound d =>
          have h := rungAt_tabToFound h₂ cJ.suit
          rw [rungAt_v, rungAt_s1, ite_eq_left rfl] at h
          by_cases hd : cJ.suit = d.suit
          · rw [ite_eq_left hd] at h; omega
          · rw [ite_eq_right hd] at h; omega
      | foundToTab d b =>
          have h := rungAt_foundToTab h₂ cJ.suit
          rw [rungAt_v, rungAt_s1, ite_eq_left rfl] at h
          have hds : cJ.suit = d.suit := by
            by_cases hd : cJ.suit = d.suit
            · exact hd
            · rw [ite_eq_right hd] at h; omega
          obtain ⟨d', hft, hd', hcp, hv⟩ := step_foundToTab_inv h₂
          rw [hd'] at hft
          have hdJ : d = cJ := by
            have h1 : s1.foundTop d.suit = some d := hft
            rw [← hds, s1_foundTop_J] at h1
            exact (Option.some.inj h1).symm
          subst hdJ
          have hpne := pull_J_p0_ne b
          rw [hv] at hpne
          exact hpne rfl

/-! ## §7. Reversibility, the play, and the shortestness bound -/

theorem u_tabToFoundR_J : tabToFoundR u cJ = true := by decide
theorem s1_tabToTabR_Zj : tabToTabR s1 cZj (Sum.inr cQh) = true := by decide
theorem s2_foundToTabR_J : foundToTabR s2 cJ (Sum.inr cQd) = true := by decide

theorem rev_raise : reversibleAtW u (Move.tabToFound cJ) :=
  (tabToFoundR_iff_reversibleAtW u_wf cJ).mp u_tabToFoundR_J

theorem rev_slide : reversibleAtW s1 (Move.tabToTab cZj (Sum.inr cQh)) :=
  (tabToTabR_iff_reversibleAtW (step_wf u_wf step_raise) cZj (Sum.inr cQh)).mp
    s1_tabToTabR_Zj

theorem rev_pull : reversibleAtW s2 (Move.foundToTab cJ (Sum.inr cQd)) :=
  (foundToTabR_iff_reversibleAtW (step_wf (step_wf u_wf step_raise) step_slide) cJ
    (Sum.inr cQd)).mp s2_foundToTabR_J

/-- **THE WITNESS PLAY.** -/
theorem play :
    ShufflePlayW u [Move.tabToFound cJ, Move.tabToTab cZj (Sum.inr cQh),
      Move.foundToTab cJ (Sum.inr cQd)] v :=
  Walk.cons rev_raise step_raise
    (Walk.cons rev_slide step_slide
      (Walk.cons rev_pull (s3_eq_v ▸ step_pull) (Walk.nil v)))

/-- **THE PLAY IS A SHORTEST ONE.** -/
theorem no_short (ρ : List Move) (h : ShufflePlayW u ρ v) : 3 ≤ ρ.length := by
  cases ρ with
  | nil =>
      have hrun := Walk_run _ h
      have huv : u = v := Option.some.inj (show some u = some v from hrun)
      exact absurd huv u_ne_v
  | cons m1 rest =>
      cases rest with
      | nil =>
          exact absurd (Elim.step_of_singleton h) (no_one_step m1)
      | cons m2 rest2 =>
          cases rest2 with
          | nil =>
              obtain ⟨s, -, hs1, hrest⟩ := Bubble.walk_cons_inv h
              obtain ⟨s2', -, hs2, hnil⟩ := Bubble.walk_cons_inv hrest
              cases hnil
              exfalso
              exact no_two_step m1 m2 s hs1 hs2
          | cons _ _ => simp

/-! ## §8. The residual is refuted -/

/-- The interior letter is **read-safe** for the raised card. -/
theorem interior_readSafe : SlideFwd.ReadSafe cJ (Move.tabToTab cZj (Sum.inr cQh)) :=
  ⟨by decide, by decide⟩

/-- The interior letter is **seat-inert** for the pull's base `inr Q♦`. -/
theorem interior_seatInert : MtnPr.SeatInert (Sum.inr cQd) (Move.tabToTab cZj (Sum.inr cQh)) :=
  ⟨by decide, by decide⟩

/-- **THE PULL'S BASE IS BURIED AT THE ORIGIN.** -/
theorem u_buried : u.pileOfTop cQd = none := u_pileOfTop_Qd

/-- **... AND AT THE RAISE'S IMAGE.** -/
theorem s1_buried : s1.pileOfTop cQd = none := by decide

/-- **... AND EXPOSED AT THE PRE-PULL STATE.** -/
theorem s2_exposed : s2.pileOfTop cQd = some .p1 := by decide

/-- **`BaseEn.InrExposeResidual` IS FALSE.** -/
theorem inrExposeResidual_false : ¬ BaseEn.InrExposeResidual := by
  intro hres
  have hshort := hres u v
    [Move.tabToFound cJ, Move.tabToTab cZj (Sum.inr cQh), Move.foundToTab cJ (Sum.inr cQd)]
    [] [Move.tabToTab cZj (Sum.inr cQh)] [] []
    cJ cQd u s2 u_wf play rfl (Walk.nil u)
    (by intro q hq; rw [List.mem_singleton] at hq; subst hq; exact interior_readSafe)
    (by intro q hq; rw [List.mem_singleton] at hq; subst hq; exact interior_seatInert)
    u_buried ⟨.p1, s2_exposed⟩
  obtain ⟨ρ', hplay', hlen⟩ := hshort
  have h3 := no_short ρ' hplay'
  simp only [List.length_cons, List.length_nil] at hlen
  omega

/-- **`InrExp.InrExpHead` IS FALSE TOO** (same board, `γ₁' = []`). -/
theorem inrExpHead_false : ¬ InrExp.InrExpHead := by
  intro hhead
  have hshort := hhead u v
    [Move.tabToFound cJ, Move.tabToTab cZj (Sum.inr cQh), Move.foundToTab cJ (Sum.inr cQd)]
    [] [] []
    cJ cQd u s1 s2 (Move.tabToTab cZj (Sum.inr cQh))
    u_wf play rfl (Walk.nil u) step_raise step_slide
    (by intro r hr; rw [List.mem_singleton] at hr; subst hr; exact interior_readSafe)
    (by intro r hr; rw [List.mem_singleton] at hr; subst hr; exact interior_seatInert)
    s1_buried ⟨.p1, s2_exposed⟩
  obtain ⟨ρ', hplay', hlen⟩ := hshort
  have h3 := no_short ρ' hplay'
  simp only [List.length_cons, List.length_nil] at hlen
  omega

/-! ## §9. The repaired head residual: the gate is necessary and satisfiable

The witness's head letter is a slide onto the pile that the raise *emptied*; at
the raise's origin that base is not yet free, so the head is not even a legal
letter there.  The repair is therefore:

> the head letter must already be legal at the raise's **origin**.

This is a letter-level legality condition (it says nothing about shortening),
it excludes the witness by construction, and both proved head shapes (raise and
slide) satisfy it. -/

/-- **THE REPAIRED HEAD RESIDUAL.**  `InrExpHead` plus: the head letter `q` is
legal at the raise's origin `A` (so the raise is not what enables it). -/
def InrExpHeadGated : Prop :=
  ∀ (u v : State) (ρ pre γ₁' post : List Move) (c z : Card) (A B Aq : State) (q : Move),
    u.WF → ShufflePlayW u ρ v →
    ρ = pre ++ Move.tabToFound c :: (q :: γ₁') ++ Move.foundToTab c (Sum.inr z) :: post →
    ShufflePlayW u pre A →
    State.step A (Move.tabToFound c) = some B →
    State.step B q = some Aq →
    (∀ r ∈ (q :: γ₁'), SlideFwd.ReadSafe c r) →
    (∀ r ∈ (q :: γ₁'), MtnPr.SeatInert (Sum.inr z) r) →
    B.pileOfTop z = none →
    (∃ k, Aq.pileOfTop z = some k) →
    (∃ A0 : State, State.step A q = some A0) →
    ∃ ρ' : List Move, ShufflePlayW u ρ' v ∧ ρ'.length < ρ.length

/-- The gate only *weakens* the residual: the old head residual implies it. -/
theorem headGated_of_head (h : InrExp.InrExpHead) : InrExpHeadGated := by
  intro u v ρ pre γ₁' post c z A B Aq q huwf hplay hρ hpre hstepB hstepq
    hread hseat hBz hAq _
  exact h u v ρ pre γ₁' post c z A B Aq q huwf hplay hρ hpre hstepB hstepq
    hread hseat hBz hAq

/-- **THE WITNESS VIOLATES THE GATE EXACTLY**: its head letter is not legal at
the raise's origin. -/
theorem gate_fails_here :
    ¬ ∃ A0 : State, State.step u (Move.tabToTab cZj (Sum.inr cQh)) = some A0 := by
  rintro ⟨A0, h⟩
  rw [u_no_slide cZj (Sum.inr cQh)] at h
  cases h

/-- **THE GATE IS SATISFIABLE BY THE PROVED RAISING HEAD**: `raise x` is legal
at the origin (so the repaired residual covers
`InrExp.inr_expose_raise_adjacent_shortens`). -/
theorem gate_holds_for_raise {A : State} {x : Card} {p : Anchor}
    (hnext : A.nextUp x = true) (hpo : A.pileOfTop x = some p) :
    ∃ A0 : State, State.step A (Move.tabToFound x) = some A0 :=
  ⟨_, by rw [step_tabToFound_splice hnext hpo]⟩

/-! ## §10. Consequences for the InrExp chain

`InrExp.inrExposeResidual_of_head_deep` consumed `InrExpHead` as its head case.
Since `InrExpHead` is false, that reduction has **no instances**: the `inr`
exposure route to `BaseEnabling` is dead as stated, and so is every downstream
consumer of `BaseEn.InrExposeResidual`.  (`InrExpDeep` is untouched by this
witness — it needs `Aq.pileOfTop z = none`, which fails here — but its sibling
head case is now gone.) -/

/-- **`InrExp.inrExposeResidual_of_head_deep` HAS NO INSTANCES.** -/
theorem inrExposeResidual_of_head_deep_vacuous
    (hhead : InrExp.InrExpHead) (hdeep : InrExp.InrExpDeep) : False :=
  inrExpHead_false hhead

/-- **`InrExp.baseEnabling_inr_of_inrExpose` HAS NO INSTANCES.** -/
theorem baseEnabling_inr_vacuous (h : BaseEn.InrExposeResidual) : False :=
  inrExposeResidual_false h

/-- **`InrExp.sameCardRelocation_of_inl_and_inr` HAS NO INSTANCES** (the `inr`
half is unsatisfiable). -/
theorem sameCardRelocation_of_inl_and_inr_vacuous
    (hinl : ∀ (u v : State) (ρ pre γ post : List Move) (c : Card) (a : Anchor)
        (A B : State),
      u.WF → ShufflePlayW u ρ v →
      ρ = pre ++ Move.tabToFound c :: γ ++ Move.foundToTab c (Sum.inl a) :: post →
      ShufflePlayW u pre A →
      State.step A (Move.tabToFound c) = some B →
      (∀ q ∈ γ, SlideFwd.ReadSafe c q) →
      (∀ q ∈ γ, MtnPr.SeatInert (Sum.inl a) q) →
      B.canPlace c (Sum.inl a) = false →
      ∃ ρ' : List Move, ShufflePlayW u ρ' v ∧ ρ'.length < ρ.length)
    (hinr : BaseEn.InrExposeResidual) : False :=
  inrExposeResidual_false hinr

/-! ## §11. The SAME residual is already refuted by `Orig2/ForkPermRefute.lean`

The campaign's existing witness (`Perm`, `Orig2/ForkPermRefute.lean:62`) is the
*same* 3-letter shape with the *same* mechanism (§3 above), and it also has the
pull's base `5♥` **buried at the raise's origin** (`Perm.u.pileOfTop cB = none`,
`Perm.u_pileOfTop_B`, `:151`) — it is buried under `4♣`, the very card the
interior slides away.  So `InrExposeResidual` / `InrExpHead` were refuted
*already*, by the `Perm` play; this section records it in the kernel.

(The check that was missing in the previous lane: `InrExposeResidual` does
**not** require the pull to be legal at the raise's image — only that `A.pileOfTop
z = none` and that *some* state exposes `z`.  `Perm`'s witness satisfies both,
and `Perm.no_short` rules out the shorter play.) -/

theorem Perm_s₁_buried : Perm.s₁.pileOfTop Perm.cB = none := by decide
theorem Perm_s₂_exposed : Perm.s₂.pileOfTop Perm.cB = some .p1 := by decide

/-- **`InrExp.InrExpHead` WAS ALREADY FALSE**: `Orig2/ForkPermRefute.lean`'s
shortest witness is an instance with `γ₁' = []`. -/
theorem inrExpHead_false_via_Perm : ¬ InrExp.InrExpHead := by
  intro hhead
  have hshort := hhead Perm.u Perm.v
    [Move.tabToFound Perm.cX, Move.tabToTab Perm.cZ (Sum.inr Perm.cY),
      Move.foundToTab Perm.cX (Sum.inr Perm.cB)]
    [] [] [] Perm.cX Perm.cB Perm.u Perm.s₁ Perm.s₂
    (Move.tabToTab Perm.cZ (Sum.inr Perm.cY))
    Perm.u_wf Perm.play rfl (Walk.nil Perm.u) Perm.step_raise Perm.step_slide
    (by
      intro r hr
      rw [List.mem_singleton] at hr
      subst hr
      exact Perm.interior_readSafe)
    (by
      intro r hr
      rw [List.mem_singleton] at hr
      subst hr
      exact Perm.interior_seatInert)
    Perm_s₁_buried ⟨.p1, Perm_s₂_exposed⟩
  obtain ⟨ρ', hplay', hlen⟩ := hshort
  have h3 := Perm.no_short ρ' hplay'
  simp only [List.length_cons, List.length_nil] at hlen
  omega

/-- **`BaseEn.InrExposeResidual` WAS ALREADY FALSE**, same instantiation. -/
theorem inrExposeResidual_false_via_Perm : ¬ BaseEn.InrExposeResidual := by
  intro hres
  have hshort := hres Perm.u Perm.v
    [Move.tabToFound Perm.cX, Move.tabToTab Perm.cZ (Sum.inr Perm.cY),
      Move.foundToTab Perm.cX (Sum.inr Perm.cB)]
    [] [Move.tabToTab Perm.cZ (Sum.inr Perm.cY)] [] []
    Perm.cX Perm.cB Perm.u Perm.s₂
    Perm.u_wf Perm.play rfl (Walk.nil Perm.u)
    (by
      intro q hq
      rw [List.mem_singleton] at hq
      subst hq
      exact Perm.interior_readSafe)
    (by
      intro q hq
      rw [List.mem_singleton] at hq
      subst hq
      exact Perm.interior_seatInert)
    Perm.u_pileOfTop_B ⟨.p1, Perm_s₂_exposed⟩
  obtain ⟨ρ', hplay', hlen⟩ := hshort
  have h3 := Perm.no_short ρ' hplay'
  simp only [List.length_cons, List.length_nil] at hlen
  omega

end InrExpRefute

#print axioms InrExpRefute.u_wf
#print axioms InrExpRefute.no_short
#print axioms InrExpRefute.play
#print axioms InrExpRefute.inrExposeResidual_false
#print axioms InrExpRefute.inrExpHead_false
#print axioms InrExpRefute.headGated_of_head
#print axioms InrExpRefute.gate_fails_here
#print axioms InrExpRefute.gate_holds_for_raise
#print axioms InrExpRefute.inrExposeResidual_of_head_deep_vacuous
#print axioms InrExpRefute.baseEnabling_inr_vacuous
#print axioms InrExpRefute.sameCardRelocation_of_inl_and_inr_vacuous
#print axioms InrExpRefute.inrExpHead_false_via_Perm
#print axioms InrExpRefute.inrExposeResidual_false_via_Perm
