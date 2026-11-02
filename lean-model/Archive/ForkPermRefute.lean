import Orig2.Fork.Local.ForkRelocate

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

/-!
# Perm_Refute — PERMANENCE IS FALSE

READ-ONLY scratch.  No `sorry`, no `Classical.choice`, no `native_decide`.

The campaign's intended

```
theorem permanence :
    u.WF → ShufflePlayW u ρ v → (∀ ρ', ShufflePlayW u ρ' v → ρ.length ≤ ρ'.length) →
    ∀ x : Card, ¬ (Move.tabToFound x ∈ ρ ∧ ∃ b, Move.foundToTab x b ∈ ρ)
```

— "in a shortest witness play no card is both raised and pulled" — is **FALSE**.
A shortest play may relocate a card through the foundation:

* `raise x` puts `x` on the foundation (and uncovers the seat `y` below it);
* the interior exposes the pull's base `β` (in the smallest shape, `x.twin`
  slides onto `y`);
* `pull x` puts `x` down on the exposed base `β`.

Adjacent `raise x ; pull x` always shortens (`MtnPr.adjacent_raise_pull_shortens`),
so three letters is the *minimum* length of a relocation play.  The instance
below is exactly three letters, and **no witness play of length 0, 1 or 2
exists** (§4) — so it is a shortest witness play with a raise-then-pull of the
same card.  (The Python census in `Temp/MtnRef_witness.py` / `MtnRef_Report.md`
reports it as the unique shortest play; uniqueness is measured there, while
`no_short` here proves the lower bound `3 ≤ length` in the kernel.)

```
  x = 4S   x.twin = 4C   y = 5D   beta = 5H
  u :  p0 = [5D, 4S]  p1 = [5H, 4C]   foundations H4 D4 S3 C2, no stock/waste
  play: raise 4S ; slide 4C onto 5D ; pull 4S onto 5H
  v :  p0 = [5D, 4C]  p1 = [5H, 4S]   same foundations
```

Minimality (§4) is proved by the rung ledger, not by search: with no draw and no
slide legal at `u`, the first letter is a raise or a pull; a raise is forced to
be `raise 4S` and then the second letter is forced to be `pull 4S` (whose `p0`
can never match `v`'s); a pull is undone by `step_tabToFound_of_foundToTab`,
returning to `u ≠ v`.

The interior letter `slide 4C → 5D` is both `ReadSafe 4S` and
`SeatInert (inr 5H)` (§5), but the pull is **not** legal at the raise's image.
So the source's named residual `MtnPr.SameCardRelocation`
(`Orig2/Fork/Local/ForkRelocate.lean:545`) is refuted by the same play (§7), and the
readiness clause of `PullKit.SameCardRelocationReady`
(`Orig2/Fork/Local/ForkPullSwaps.lean:721`) is indispensable.

The file also records what *is* true (§7): the **adjacent** pair never occurs in
a shortest play, in either order.  The refutation shows the long-range statement
fails precisely because the interior can *move the seat the pull lands on* — the
pull is not *ready* at the raise's image.
-/

namespace Perm

open MountainKit
open CommuteStep

/-! ## §1. The board -/

/-- The relocated card. -/
def cX : Card := ⟨.spade, .four⟩
/-- Its twin: the card that exposes the pull's base. -/
def cZ : Card := ⟨.club, .four⟩
/-- The card `cX` is raised from. -/
def cY : Card := ⟨.diamond, .five⟩
/-- The card `cX` is pulled onto. -/
def cB : Card := ⟨.heart, .five⟩
/-- The only cards a `cY`/`cB` slide could target (both hidden in `junk`). -/
def cS6 : Card := ⟨.spade, .six⟩
def cC6 : Card := ⟨.club, .six⟩

def foundOf : Suit → List Card
  | .heart => Suit.heart.upCards.take 4
  | .diamond => Suit.diamond.upCards.take 4
  | .spade => Suit.spade.upCards.take 3
  | .club => Suit.club.upCards.take 2

def junk : List Card :=
  Card.universe.filter (fun c =>
    decide (c ∉ foundOf .heart ∧ c ∉ foundOf .diamond ∧ c ∉ foundOf .spade ∧
      c ∉ foundOf .club ∧ c ≠ cX ∧ c ≠ cZ ∧ c ≠ cY ∧ c ≠ cB))

def u : State :=
  { found := foundOf
    piles := fun a => match a with
      | .p0 => ⟨junk, [cY, cX]⟩
      | .p1 => ⟨[], [cB, cZ]⟩
      | _ => ⟨[], []⟩
    stock := []
    waste := []
    drawStep := 1 }

def v : State :=
  { found := foundOf
    piles := fun a => match a with
      | .p0 => ⟨junk, [cY, cZ]⟩
      | .p1 => ⟨[], [cB, cX]⟩
      | _ => ⟨[], []⟩
    stock := []
    waste := []
    drawStep := 1 }

/-! ## WF -/

theorem u_wf : u.WF := by
  refine ⟨?_, ?_, ?_, by decide⟩
  · intro s
    cases s with
    | heart => exact ⟨4, rfl⟩
    | diamond => exact ⟨4, rfl⟩
    | spade => exact ⟨3, rfl⟩
    | club => exact ⟨2, rfl⟩
  · intro a
    cases a <;> decide
  · intro c _
    rcases c with ⟨s, r⟩
    cases s <;> cases r <;> decide

/-! ## canSitOn case analyses -/

theorem canSitOn_X_cases {z : Card} (h : canSitOn cX z = true) : z = cY ∨ z = cB := by
  rcases z with ⟨s, r⟩
  cases s <;> cases r <;> first | decide | (exact absurd h (by decide))

theorem canSitOn_Z_cases {z : Card} (h : canSitOn cZ z = true) : z = cY ∨ z = cB := by
  rcases z with ⟨s, r⟩
  cases s <;> cases r <;> first | decide | (exact absurd h (by decide))

theorem canSitOn_Y_cases {z : Card} (h : canSitOn cY z = true) : z = cS6 ∨ z = cC6 := by
  rcases z with ⟨s, r⟩
  cases s <;> cases r <;> first | decide | (exact absurd h (by decide))

theorem canSitOn_B_cases {z : Card} (h : canSitOn cB z = true) : z = cS6 ∨ z = cC6 := by
  rcases z with ⟨s, r⟩
  cases s <;> cases r <;> first | decide | (exact absurd h (by decide))

/-! ## pileOfTop facts at `u` -/

theorem u_nextUp_X : u.nextUp cX = true := by decide
theorem u_pileOfTop_X : u.pileOfTop cX = some .p0 := by decide
theorem u_pileOfTop_Y : u.pileOfTop cY = none := by decide
theorem u_pileOfTop_B : u.pileOfTop cB = none := by decide
theorem u_pileOfTop_S6 : u.pileOfTop cS6 = none := by decide
theorem u_pileOfTop_C6 : u.pileOfTop cC6 = none := by decide

/-- No slide head of the two live piles can be placed anywhere at `u`. -/
theorem u_canPlace_X (b : Base) : u.canPlace cX b = false := by
  cases b with
  | inl a =>
      rw [canPlace_inl_unfold]
      rw [show decide (cX.rank = Rank.king) = false from by decide, Bool.and_false]
  | inr z =>
      rw [canPlace_inr_eq]
      cases h : u.pileOfTop z with
      | none => rfl
      | some k =>
          cases hs : canSitOn cX z with
          | false => rfl
          | true =>
              rcases canSitOn_X_cases hs with rfl | rfl
              · rw [u_pileOfTop_Y] at h; exact absurd h (by simp)
              · rw [u_pileOfTop_B] at h; exact absurd h (by simp)

theorem u_canPlace_Z (b : Base) : u.canPlace cZ b = false := by
  cases b with
  | inl a =>
      rw [canPlace_inl_unfold]
      rw [show decide (cZ.rank = Rank.king) = false from by decide, Bool.and_false]
  | inr z =>
      rw [canPlace_inr_eq]
      cases h : u.pileOfTop z with
      | none => rfl
      | some k =>
          cases hs : canSitOn cZ z with
          | false => rfl
          | true =>
              rcases canSitOn_Z_cases hs with rfl | rfl
              · rw [u_pileOfTop_Y] at h; exact absurd h (by simp)
              · rw [u_pileOfTop_B] at h; exact absurd h (by simp)

theorem u_canPlace_Y (b : Base) : u.canPlace cY b = false := by
  cases b with
  | inl a =>
      rw [canPlace_inl_unfold]
      rw [show decide (cY.rank = Rank.king) = false from by decide, Bool.and_false]
  | inr z =>
      rw [canPlace_inr_eq]
      cases h : u.pileOfTop z with
      | none => rfl
      | some k =>
          cases hs : canSitOn cY z with
          | false => rfl
          | true =>
              rcases canSitOn_Y_cases hs with rfl | rfl
              · rw [u_pileOfTop_S6] at h; exact absurd h (by simp)
              · rw [u_pileOfTop_C6] at h; exact absurd h (by simp)

theorem u_canPlace_B (b : Base) : u.canPlace cB b = false := by
  cases b with
  | inl a =>
      rw [canPlace_inl_unfold]
      rw [show decide (cB.rank = Rank.king) = false from by decide, Bool.and_false]
  | inr z =>
      rw [canPlace_inr_eq]
      cases h : u.pileOfTop z with
      | none => rfl
      | some k =>
          cases hs : canSitOn cB z with
          | false => rfl
          | true =>
              rcases canSitOn_B_cases hs with rfl | rfl
              · rw [u_pileOfTop_S6] at h; exact absurd h (by simp)
              · rw [u_pileOfTop_C6] at h; exact absurd h (by simp)

/-- The four face-up cards of `u`. -/
theorem u_pileHolding_cases {c : Card} (h : u.pileHolding c ≠ none) :
    c = cX ∨ c = cZ ∨ c = cY ∨ c = cB := by
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

theorem u_canPlace_false (c : Card) (h : c = cX ∨ c = cZ ∨ c = cY ∨ c = cB) (b : Base) :
    u.canPlace c b = false := by
  rcases h with rfl | rfl | rfl | rfl
  · exact u_canPlace_X b
  · exact u_canPlace_Z b
  · exact u_canPlace_Y b
  · exact u_canPlace_B b

/-- **NO SLIDE IS LEGAL AT `u`.** -/
theorem u_no_slide (c : Card) (b : Base) : State.step u (Move.tabToTab c b) = none := by
  cases hh : u.pileHolding c with
  | none =>
      simp only [State.step, hh]
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

/-- **THE ONLY RAISABLE CARD AT `u` IS `cX`.** -/
theorem u_raisable_check :
    Card.universe.all (fun c => !(u.nextUp c && (u.pileOfTop c).isSome) || (c == cX)) = true := by
  decide

theorem u_raisable_X {c : Card} (hnext : u.nextUp c = true) (hpo : u.pileOfTop c ≠ none) :
    c = cX := by
  have hmem := Card.mem_universe c
  have hall := List.all_eq_true.mp u_raisable_check c hmem
  have hb : (u.nextUp c && (u.pileOfTop c).isSome) = true := by
    rw [hnext]
    cases hp : u.pileOfTop c with
    | none => exact absurd hp hpo
    | some k => rfl
  rw [hb] at hall
  exact beq_iff_eq.mp (by simpa using hall)

/-! ## §4. The play's intermediate state and the two-step lower bound -/

/-- After `raise 4S`. -/
def s₁ : State := raiseSt u cX .p0

theorem u_ne_v : u ≠ v := by
  intro h
  have hp : u.piles .p0 = v.piles .p0 := by rw [h]
  simp [u, v] at hp
  exact absurd hp (by decide)

theorem v_piles_p0 : v.piles .p0 = ⟨junk, [cY, cZ]⟩ := by decide
theorem s₁_piles_p0 : s₁.piles .p0 = ⟨junk, [cY]⟩ := by decide
theorem s₁_foundTop_X : s₁.foundTop cX.suit = some cX := by decide
theorem s₁_waste : s₁.waste = [] := rfl

theorem rungAt_v (σ : Suit) : rungAt v σ = rungAt u σ := rfl

theorem rungAt_s₁ (σ : Suit) :
    rungAt s₁ σ = if σ = cX.suit then rungAt u σ + 1 else rungAt u σ :=
  rungAt_raiseSt (u := u) (c := cX) (a := .p0) σ

/-- **NO SINGLE MOVE TAKES `u` TO `v`.** -/
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
      have hc : c = cX := u_raisable_X hnext (by simp [hpo])
      subst hc
      have ha : a = .p0 := by rw [u_pileOfTop_X] at hpo; exact (Option.some.inj hpo).symm
      subst ha
      have hp : v.piles .p0 = ⟨junk, [cY]⟩ := by rw [hv]; decide
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
theorem pull_X_p0_ne (b : Base) :
    ((s₁.setFound cX.suit (chop (s₁.found cX.suit))).putCard cX b).piles .p0
      ≠ v.piles .p0 := by
  have hT : (s₁.setFound cX.suit (chop (s₁.found cX.suit))).piles .p0
      = ⟨junk, [cY]⟩ := s₁_piles_p0
  have htop : ∀ z, (s₁.setFound cX.suit (chop (s₁.found cX.suit))).pileOfTop z
      = s₁.pileOfTop z := fun z => rfl
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
      cases hz : s₁.pileOfTop z with
      | none =>
          have hz' : (s₁.setFound cX.suit (chop (s₁.found cX.suit))).pileOfTop z = none := by
            rw [htop z]; exact hz
          rw [show (s₁.setFound cX.suit (chop (s₁.found cX.suit))).putCard cX (Sum.inr z)
              = (s₁.setFound cX.suit (chop (s₁.found cX.suit))) from by
                simp only [State.putCard, hz']] at h
          rw [hT, v_piles_p0] at h
          exact absurd h (by decide)
      | some k =>
          have hz' : (s₁.setFound cX.suit (chop (s₁.found cX.suit))).pileOfTop z = some k := by
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

/-- **NO TWO MOVES TAKE `u` TO `v`.**  The ledger pins the first letter (no draw,
no slide, no waste; a raise is `raise cX`, a pull is undone), and the raise case
dies on `p0`. -/
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
      have hc : c = cX := u_raisable_X hnext (by simp [hpo])
      subst hc
      have ha : a = .p0 := by rw [u_pileOfTop_X] at hpo; exact (Option.some.inj hpo).symm
      subst ha
      have hs1 : s = s₁ := by rw [hs]; rfl
      subst hs1
      cases m₂ with
      | draw =>
          have h := rungAt_draw h₂ cX.suit
          rw [rungAt_v, rungAt_s₁, ite_eq_left rfl] at h
          omega
      | wasteToFound d =>
          rw [(step_waste_none s₁ s₁_waste d (Sum.inl .p0)).1] at h₂
          cases h₂
      | wasteToTab d b =>
          rw [(step_waste_none s₁ s₁_waste d b).2] at h₂
          cases h₂
      | tabToTab d b =>
          have h := rungAt_tabToTab h₂ cX.suit
          rw [rungAt_v, rungAt_s₁, ite_eq_left rfl] at h
          omega
      | tabToFound d =>
          have h := rungAt_tabToFound h₂ cX.suit
          rw [rungAt_v, rungAt_s₁, ite_eq_left rfl] at h
          by_cases hd : cX.suit = d.suit
          · rw [ite_eq_left hd] at h; omega
          · rw [ite_eq_right hd] at h; omega
      | foundToTab d b =>
          have h := rungAt_foundToTab h₂ cX.suit
          rw [rungAt_v, rungAt_s₁, ite_eq_left rfl] at h
          have hds : cX.suit = d.suit := by
            by_cases hd : cX.suit = d.suit
            · exact hd
            · rw [ite_eq_right hd] at h; omega
          obtain ⟨d', hft, hd', hcp, hv⟩ := step_foundToTab_inv h₂
          rw [hd'] at hft
          have hdX : d = cX := by
            have h1 : s₁.foundTop d.suit = some d := hft
            rw [← hds, s₁_foundTop_X] at h1
            exact (Option.some.inj h1).symm
          subst hdX
          have hpne := pull_X_p0_ne b
          rw [hv] at hpne
          exact hpne rfl

/-! ## §5. The play itself -/

/-- The interior letter is **read-safe** for the raised card. -/
theorem interior_readSafe : SlideFwd.ReadSafe cX (Move.tabToTab cZ (Sum.inr cY)) :=
  ⟨by decide, by decide⟩

/-- The interior letter is **seat-inert** for the pull's base `inr 5H`. -/
theorem interior_seatInert : MtnPr.SeatInert (Sum.inr cB) (Move.tabToTab cZ (Sum.inr cY)) :=
  ⟨by decide, by decide⟩

/-- **THE READINESS FAILURE, IN THIS INSTANCE.**  At the raise's image `s₁` the
pull `4S → 5H` is not legal: `5H` is still covered by `4C`.  (This is
`PullKit.Pullable s₁ cX (inr cB)`, `Orig2/Fork/Local/ForkPullSwaps.lean:51`.) -/
theorem not_pullable_at_image :
    ¬ (s₁.foundTop cX.suit = some cX ∧ s₁.canPlace cX (Sum.inr cB) = true) := by
  rintro ⟨-, hcp⟩
  exact absurd hcp (by decide)
/-- After `slide 4C onto 5D`. -/
def s₂ : State := slideSt s₁ cZ (Sum.inr cY) .p1

/-- After `pull 4S onto 5H` — this must be `v`. -/
def s₃ : State := pullSt s₂ cX (Sum.inr cB)

theorem s₁_pileHolding_Z : s₁.pileHolding cZ = some .p1 := by decide
theorem s₁_canPlace_Z : s₁.canPlace cZ (Sum.inr cY) = true := by decide
theorem s₂_foundTop_X : s₂.foundTop cX.suit = some cX := by decide
theorem s₂_canPlace_X : s₂.canPlace cX (Sum.inr cB) = true := by decide

theorem step_raise : State.step u (Move.tabToFound cX) = some s₁ := by
  rw [step_tabToFound_splice u_nextUp_X u_pileOfTop_X]
  rfl

theorem step_slide : State.step s₁ (Move.tabToTab cZ (Sum.inr cY)) = some s₂ := by
  rw [State.step]
  rw [s₁_pileHolding_Z]
  rw [s₁_canPlace_Z]
  rfl

theorem step_pull : State.step s₂ (Move.foundToTab cX (Sum.inr cB)) = some s₃ := by
  rw [step_foundToTab_splice s₂_foundTop_X s₂_canPlace_X]
  rfl

/-- The three letters land exactly on `v`. -/
theorem s₃_eq_v : s₃ = v := by
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

/-! ## §6. Reversibility of the three letters (the oracle) -/

theorem u_tabToFoundR_X : tabToFoundR u cX = true := by decide
theorem s₁_tabToTabR_Z : tabToTabR s₁ cZ (Sum.inr cY) = true := by decide
theorem s₂_foundToTabR_X : foundToTabR s₂ cX (Sum.inr cB) = true := by decide

theorem rev_raise : reversibleAtW u (Move.tabToFound cX) :=
  (tabToFoundR_iff_reversibleAtW u_wf cX).mp u_tabToFoundR_X

theorem rev_slide : reversibleAtW s₁ (Move.tabToTab cZ (Sum.inr cY)) :=
  (tabToTabR_iff_reversibleAtW (step_wf u_wf step_raise) cZ (Sum.inr cY)).mp
    s₁_tabToTabR_Z

theorem rev_pull : reversibleAtW s₂ (Move.foundToTab cX (Sum.inr cB)) :=
  (foundToTabR_iff_reversibleAtW (step_wf (step_wf u_wf step_raise) step_slide) cX
    (Sum.inr cB)).mp s₂_foundToTabR_X

/-- **THE WITNESS PLAY.** -/
theorem play :
    ShufflePlayW u [Move.tabToFound cX, Move.tabToTab cZ (Sum.inr cY),
      Move.foundToTab cX (Sum.inr cB)] v :=
  Walk.cons rev_raise step_raise
    (Walk.cons rev_slide step_slide
      (Walk.cons rev_pull (s₃_eq_v ▸ step_pull) (Walk.nil v)))

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
              obtain ⟨s2, -, hs2, hnil⟩ := Bubble.walk_cons_inv hrest
              cases hnil
              exfalso
              exact no_two_step m1 m2 s hs1 hs2
          | cons _ _ => simp

/-- **PERMANENCE IS FALSE.**  The universally quantified statement the campaign
wants does not hold: the 3-letter play above is shortest and raises, then pulls,
`cX`. -/
theorem permanence_false :
    ¬ (∀ (u v : State) (ρ : List Move), u.WF → ShufflePlayW u ρ v →
        (∀ ρ' : List Move, ShufflePlayW u ρ' v → ρ.length ≤ ρ'.length) →
        ∀ x : Card,
          ¬ (Move.tabToFound x ∈ ρ ∧ ∃ b : Base, Move.foundToTab x b ∈ ρ)) := by
  intro h
  have hmin : ∀ ρ' : List Move, ShufflePlayW u ρ' v →
      [Move.tabToFound cX, Move.tabToTab cZ (Sum.inr cY),
        Move.foundToTab cX (Sum.inr cB)].length ≤ ρ'.length :=
    fun ρ' h' => by simpa using no_short ρ' h'
  have hx := h u v _ u_wf play hmin cX
  exact hx ⟨by simp, Sum.inr cB, by simp⟩

/-- **THE PAYOFF FAILS TOO.**  The campaign's intended consequence — "the raised
cards are exactly the cards founded at `v` but not at `u`" — fails in the same
instance: `cX` is raised AND pulled, yet is founded at neither endpoint. -/
theorem raised_pulled_not_founded :
    Move.tabToFound cX ∈
        [Move.tabToFound cX, Move.tabToTab cZ (Sum.inr cY),
          Move.foundToTab cX (Sum.inr cB)] ∧
      (∃ b : Base, Move.foundToTab cX b ∈
        [Move.tabToFound cX, Move.tabToTab cZ (Sum.inr cY),
          Move.foundToTab cX (Sum.inr cB)]) ∧
      cX ∉ v.found cX.suit ∧ cX ∉ u.found cX.suit := by
  refine ⟨by simp, ⟨Sum.inr cB, by simp⟩, ?_, ?_⟩ <;> decide

/-- **THE NAMED RESIDUAL `MtnPr.SameCardRelocation` IS FALSE.**  Its hypotheses
(`ReadSafe` for the raised card, `SeatInert` for the pull's base) are *both*
satisfied by the 3-letter play of §1, yet no shorter play exists.  The missing
hypothesis is readiness at the raise's image (see `not_pullable_at_image`). -/
theorem sameCardRelocation_false : ¬ MtnPr.SameCardRelocation := by
  intro h
  obtain ⟨ρ', hρ', hlen⟩ :=
    h u v [Move.tabToFound cX, Move.tabToTab cZ (Sum.inr cY),
        Move.foundToTab cX (Sum.inr cB)]
      [] [Move.tabToTab cZ (Sum.inr cY)] [] cX (Sum.inr cB)
      u_wf play rfl
      (by
        intro q hq
        simp only [List.mem_singleton] at hq
        subst hq
        exact interior_readSafe)
      (by
        intro q hq
        simp only [List.mem_singleton] at hq
        subst hq
        exact interior_seatInert)
  have h3 := no_short ρ' hρ'
  have hlen3 : ρ'.length < 3 := by simpa using hlen
  omega

/-! ## §7. What *is* true: the adjacent pair never occurs in a shortest play -/

/-- **ADJACENT `raise x ; pull x` IS IMPOSSIBLE** in a shortest witness play
(`MtnPr.noAdjacentRaisePull_of_minimal`). -/
theorem noAdjacentRaisePull_of_minimal
    {u v : State} {ρ : List Move} {x : Card} {b : Base}
    (huwf : u.WF) (hplay : ShufflePlayW u ρ v)
    (hmin : ∀ ρ' : List Move, ShufflePlayW u ρ' v → ρ.length ≤ ρ'.length) :
    ¬ ∃ (pre tail : List Move),
      ρ = pre ++ Move.tabToFound x :: Move.foundToTab x b :: tail :=
  MtnPr.noAdjacentRaisePull_of_minimal huwf hplay hmin

/-- **ADJACENT `pull x ; raise x` IS IMPOSSIBLE** in a shortest witness play:
the pair is an identity pair (`LiveKit.pull_raise_identity_pair`). -/
theorem noAdjacentPullRaise_of_minimal
    {u v : State} {ρ : List Move} {x : Card} {b : Base}
    (huwf : u.WF) (hplay : ShufflePlayW u ρ v)
    (hmin : ∀ ρ' : List Move, ShufflePlayW u ρ' v → ρ.length ≤ ρ'.length) :
    ¬ ∃ (pre tail : List Move),
      ρ = pre ++ Move.foundToTab x b :: Move.tabToFound x :: tail := by
  rintro ⟨pre, tail, heq⟩
  obtain ⟨A, hpre, hrest⟩ :=
    ValleyElim.ShufflePlayW_split hplay pre
      (Move.foundToTab x b :: Move.tabToFound x :: tail) heq
  obtain ⟨B, -, hstep, -⟩ := Bubble.walk_cons_inv hrest
  have hAwf : A.WF := SatDifferCensus.ShufflePlayW.wf_end hpre huwf
  obtain ⟨ρ', hρ', hlen⟩ :=
    LiveKit.pull_raise_pair_shortens hplay heq hpre hAwf hstep
  exact absurd (hmin ρ' hρ') (Nat.not_le.mpr hlen)

end Perm

/-! ## §8. Battery -/

#print axioms Perm.u_wf
#print axioms Perm.step_raise
#print axioms Perm.step_slide
#print axioms Perm.step_pull
#print axioms Perm.s₃_eq_v
#print axioms Perm.rev_raise
#print axioms Perm.rev_slide
#print axioms Perm.rev_pull
#print axioms Perm.play
#print axioms Perm.no_one_step
#print axioms Perm.pull_X_p0_ne
#print axioms Perm.no_two_step
#print axioms Perm.no_short
#print axioms Perm.permanence_false
#print axioms Perm.raised_pulled_not_founded
#print axioms Perm.interior_readSafe
#print axioms Perm.interior_seatInert
#print axioms Perm.not_pullable_at_image
#print axioms Perm.sameCardRelocation_false
#print axioms Perm.noAdjacentRaisePull_of_minimal
#print axioms Perm.noAdjacentPullRaise_of_minimal




