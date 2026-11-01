import Orig2.ForkMeetCover
import Orig2.ForkValley
import Orig2.ForkNoSelf
import Orig2.ForkFace1
import Orig2.Cover

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-!
# NonComp — the non-comparability of saturated rung vectors

READ-ONLY scratch card (`Temp/`); no `Orig2/` edit; nothing committed.
Zero `sorry`, zero `Classical.choice`, zero `native_decide`; axiom battery at
the tail.

## The target, stated precisely

The load-bearing open claim of the fork/meet lane (`Temp/Meet_Report.md` §4,
`MEETFULL_bad = 0`): *two differing `SSaturated` states of one
`sameOrbitSetoid` class never have comparable rung vectors.*

§1 fixes the shape.  The right form is the **pointwise-`≤` negation pair**

```text
NC G H  :=  (¬ ∀ σ, rungAt G σ ≤ rungAt H σ) ∧ (¬ ∀ σ, rungAt H σ ≤ rungAt G σ)
```

and `nc_iff_both_signs` proves it *equivalent* to the difference vector having
both signs (`∃σ, rungAt H σ < rungAt G σ` **and** `∃τ, rungAt G τ < rungAt H τ`)
— for the four-suit enumeration, with every `by_cases` a constructive
`Nat.decLe`, so no classical input enters.  A support/ledger form is *weaker*
(the meet of the lane is the componentwise minimum of the full vector, and the
report's `7/13` "full-vector meet is false" rows are exactly the failure of a
support-only reading).

`NC` is thus one `Rises` per direction, and a global `NC` is the same content
as the global one-sided claim `RisesOfSat` (`nc_of_rises` / `rises_of_nc`):
**the whole campaign content is one-sided** — a saturated state never weakly
dominates a differing saturated class-mate.

## What is PROVED here

* §2 **equal rung sums** (`nc_of_sum_eq`): a componentwise `≤` with equal sums
  is an equality, so the differing equal-sum stratum is automatically
  incomparable.
* §3 **the mechanism lemmas**, all unconditional:
  - `not_canRaise_of_ssaturated` — no vanilla raise at a saturated state;
  - `pull_landing_not_ssaturated` — no witness pull lands on a saturated state;
  - `fit_above_twin` — **the twin-base lemma**: if `c` sits on `x` and also
    fits on `z`, then `z = x` or `z = x.twin`.  Consequently
    (`slide_base_of_above_twin`) the only landing that accepts the card
    directly above a face-up `x` is `x.twin`; exposing `x` in one slide is a
    twin move;
  - `not_top_of_supported_of_ssaturated` — at a saturated state a next-up
    *supported* card is never the pile top;
  - `no_rise_from_zero` — **THE ZERO-RUNG THEOREM**: a saturated `WF` state
    with `rungAt G σ = 0` has `rungAt H σ = 0` at *every* same-orbit `H` (the
    rank-`0` frontier card can never be raised: a raise needs a card beneath
    it, and nothing can ever be put beneath an ace).
* §4 the **residual** `FrontierPrice` — an inequality over the rung vector,
  gated at the *exposure event* (the frontier card founded at `H`) — with
  `nc_of_frontierPrice`.  §5 fixes the exact remaining state of the art:
  the twin-drop sharpening is **FALSE** (certified counterexample pair
  `(5,0,4,2) → (6,0,2,5)` in `Temp/NC_Report.md`), so the price is only
  guaranteed *somewhere*, not on the twin suit.
-/

namespace NonComp

/-! ## §1. The shape of the statement -/

/-- **`LeVec G H`** — the pointwise-`≤` order on rung vectors. -/
def LeVec (G H : State) : Prop := ∀ σ : Suit, rungAt G σ ≤ rungAt H σ

/-- **`Rises G H`** — some suit's rung is strictly larger at `H` than at `G`. -/
def Rises (G H : State) : Prop := ∃ σ : Suit, rungAt G σ < rungAt H σ

/-- **`NC G H`** — THE TARGET: neither rung vector dominates the other. -/
def NC (G H : State) : Prop := ¬ LeVec G H ∧ ¬ LeVec H G

/-- `NC` is symmetric by construction. -/
theorem nc_comm {G H : State} (h : NC G H) : NC H G := ⟨h.2, h.1⟩

theorem leVec_refl (G : State) : LeVec G G := fun _ => Nat.le_refl _

theorem leVec_trans {G H K : State} (h₁ : LeVec G H) (h₂ : LeVec H K) :
    LeVec G K := fun σ => Nat.le_trans (h₁ σ) (h₂ σ)

/-- The negation of `LeVec` is a strict rise in the opposite direction.  Read
off the four-way `Suit` enumeration; every `by_cases` is the constructive
`Nat.decLe`. -/
theorem not_leVec_iff_rises (G H : State) : ¬ LeVec G H ↔ Rises H G := by
  constructor
  · intro h
    by_cases h1 : rungAt G .spade ≤ rungAt H .spade
    · by_cases h2 : rungAt G .heart ≤ rungAt H .heart
      · by_cases h3 : rungAt G .diamond ≤ rungAt H .diamond
        · by_cases h4 : rungAt G .club ≤ rungAt H .club
          · exact absurd (fun σ => by cases σ <;> assumption) h
          · exact ⟨.club, Nat.lt_of_not_le h4⟩
        · exact ⟨.diamond, Nat.lt_of_not_le h3⟩
      · exact ⟨.heart, Nat.lt_of_not_le h2⟩
    · exact ⟨.spade, Nat.lt_of_not_le h1⟩
  · rintro ⟨σ, hσ⟩ hle
    exact Nat.not_le.mpr hσ (hle σ)

/-- **THE BOTH-SIGNS FORM.**  `NC` says the difference vector has a strict rise
in each direction. -/
theorem nc_iff_both_signs (G H : State) : NC G H ↔ (Rises G H ∧ Rises H G) := by
  unfold NC Rises
  rw [not_leVec_iff_rises, not_leVec_iff_rises]
  exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩

/-- `NC` forces the rung vectors to differ. -/
theorem rungDiffers_of_nc {G H : State} (h : NC G H) :
    MountainGate.RungDiffers G H := by
  obtain ⟨⟨σ, hσ⟩, -⟩ := (nc_iff_both_signs G H).mp h
  exact ⟨σ, Nat.ne_of_lt hσ⟩

/-- **THE ONE-SIDED FORM** — the whole content of the target, in one direction. -/
def RisesOfSat : Prop :=
  ∀ (G H : State), G.WF → H.WF → SSaturated G → SSaturated H →
    sameOrbitSetoid.r G H → MountainGate.RungDiffers G H → Rises G H

/-- The one-sided statement gives `NC` (apply it in both directions). -/
theorem nc_of_rises (h : RisesOfSat) {G H : State}
    (hG : G.WF) (hH : H.WF) (hsG : SSaturated G) (hsH : SSaturated H)
    (hcls : sameOrbitSetoid.r G H) (hd : MountainGate.RungDiffers G H) :
    NC G H := by
  refine (nc_iff_both_signs G H).mpr ⟨?_, ?_⟩
  · exact h G H hG hH hsG hsH hcls hd
  · exact h H G hH hG hsH hsG (sameOrbitSetoid.iseqv.symm hcls)
      (by obtain ⟨σ, hσ⟩ := hd; exact ⟨σ, Ne.symm hσ⟩)

/-- The reverse: `NC` for all pairs gives the one-sided statement. -/
theorem rises_of_nc (h : ∀ (G H : State), G.WF → H.WF → SSaturated G →
    SSaturated H → sameOrbitSetoid.r G H → MountainGate.RungDiffers G H →
    NC G H) : RisesOfSat := by
  intro G H hG hH hsG hsH hcls hd
  exact ((nc_iff_both_signs G H).mp (h G H hG hH hsG hsH hcls hd)).1

/-- **THE TARGET, IN FULL**: the statement the lane needs. -/
def NonComparability : Prop :=
  ∀ (G H : State), G.WF → H.WF → SSaturated G → SSaturated H →
    sameOrbitSetoid.r G H → MountainGate.RungDiffers G H → NC G H

/-- `NC` is exactly `¬ LeVec` in both orders. -/
theorem nc_of_not_leVec_both {G H : State} (h1 : ¬ LeVec G H) (h2 : ¬ LeVec H G) :
    NC G H := ⟨h1, h2⟩

theorem not_leVec_left_of_nc {G H : State} (h : NC G H) : ¬ LeVec G H := h.1

/-! ## §2. The equal-sum stratum (unconditional) -/

/-- The rung sum, unfolded over the four suits. -/
def rungSum (st : State) : Nat :=
  rungAt st .spade + rungAt st .heart + rungAt st .diamond + rungAt st .club

theorem rungSum_le_of_leVec {G H : State} (h : LeVec G H) :
    rungSum G ≤ rungSum H := by
  have s := h .spade
  have he := h .heart
  have d := h .diamond
  have c := h .club
  unfold rungSum
  omega

/-- A componentwise `≤` between equal-sum vectors is an equality, suit by suit. -/
theorem eq_of_leVec_of_sum_le {G H : State} (h : LeVec G H)
    (hs : rungSum H ≤ rungSum G) : ∀ σ, rungAt G σ = rungAt H σ := by
  have htotal : rungSum H = rungSum G :=
    Nat.le_antisymm hs (rungSum_le_of_leVec h)
  have hs' := h .spade
  have hh' := h .heart
  have hd' := h .diamond
  have hc' := h .club
  unfold rungSum at htotal
  intro σ
  cases σ <;> omega

/-- **`NC` ON THE EQUAL-SUM STRATUM** — a differing pair with equal rung sums is
incomparable, outright. -/
theorem nc_of_sum_eq {G H : State} (hd : MountainGate.RungDiffers G H)
    (hsum : rungSum G = rungSum H) : NC G H := by
  obtain ⟨σ₀, hσ₀⟩ := hd
  constructor
  · intro hle
    exact hσ₀ (eq_of_leVec_of_sum_le hle (by omega) σ₀)
  · intro hle
    exact hσ₀ (eq_of_leVec_of_sum_le hle (by omega) σ₀).symm

/-! ## §3. The mechanism lemmas (unconditional) -/

/-- **NO VANILLA RAISE AT A SATURATED STATE.** -/
theorem not_canRaise_of_ssaturated {st : State} (hs : SSaturated st) (c : Card) :
    ¬ CanRaise st c :=
  fun hc => hs c (CanRaiseS.now c hc)

/-- **NO WITNESS PULL LANDS ON A SATURATED STATE.**  The pulled card is vanilla
live at its landing (`ForkValley.pull_card_canRaise`). -/
theorem pull_landing_not_ssaturated {st w : State} (hwf : st.WF) {c : Card}
    {b : Base} (hstep : State.step st (Move.foundToTab c b) = some w) :
    ¬ SSaturated w :=
  fun hs => not_canRaise_of_ssaturated hs c (ValleyStep.pull_card_canRaise hwf hstep)

/-- Suits of one colour are equal or twins. -/
theorem suit_eq_or_twin_of_color_eq {s t : Suit} (h : s.color = t.color) :
    s = t ∨ s = t.twin := by
  cases s <;> cases t <;> simp_all [Suit.color, Suit.twin]

/-- Two colours differing from one third are equal. -/
theorem color_eq_of_ne_ne {a b d : Color} (h1 : a ≠ b) (h2 : a ≠ d) : b = d := by
  cases a <;> cases b <;> cases d <;> simp_all

/-- **`fit_above_twin` — THE TWIN-BASE LEMMA.**  If a card `c` sits on `x`
(`canSitOn c x`) and also fits on a card `z` (`canSitOn c z`), then `z` is `x`
or `x`'s twin.  Rank and colour arithmetic only — no `WF`, no saturation. -/
theorem fit_above_twin {x c z : Card} (hx : canSitOn c x = true)
    (hz : canSitOn c z = true) : z = x ∨ z = x.twin := by
  obtain ⟨hr1, hc1⟩ := (canSitOn_eq c x).mp hx
  obtain ⟨hr2, hc2⟩ := (canSitOn_eq c z).mp hz
  have hidx : z.rank.toIdx = x.rank.toIdx := by omega
  have hrank : z.rank = x.rank := Rank.toIdx_inj hidx
  have hcol : z.suit.color = x.suit.color := color_eq_of_ne_ne hc2 hc1
  rcases suit_eq_or_twin_of_color_eq hcol with h | h
  · left
    cases x with
    | mk xs xr =>
      cases z with
      | mk zs zr =>
        simp only at h hrank
        subst h
        subst hrank
        rfl
  · right
    cases x with
    | mk xs xr =>
      cases z with
      | mk zs zr =>
        simp only at h hrank
        subst h
        subst hrank
        rfl

/-- The card directly above `x` is not a king (its rank is `x.rank - 1`). -/
theorem not_king_of_above {x c : Card} (h : canSitOn c x = true) :
    c.rank ≠ Rank.king := by
  intro hk
  have h1 := (canSitOn_eq c x).mp h |>.1
  rw [hk] at h1
  have h12 : (Rank.king).toIdx = 12 := rfl
  rw [h12] at h1
  have hlt := Rank.toIdx_lt x.rank
  omega

/-- `lastOf` ignores a prefix. -/
theorem lastOf_append_cons_eq (L : List Card) (y : Card) (M : List Card) :
    lastOf (L ++ y :: M) = lastOf (y :: M) := by
  induction L with
  | nil => rfl
  | cons w ws ih =>
      rw [List.cons_append]
      cases ws with
      | nil => rfl
      | cons w' ws' =>
          exact ih

/-- A duplicate-free list's last element is not the head when the tail is
nonempty. -/
theorem lastOf_cons_ne_of_notmem {y : Card} {M : List Card} (hnot : y ∉ M)
    (hM : M ≠ []) : lastOf (y :: M) ≠ some y := by
  cases M with
  | nil => exact absurd rfl hM
  | cons m M' =>
      intro hlast
      have hmem : y ∈ m :: M' := lastOf_mem hlast
      rcases List.mem_cons.mp hmem with heq | hin
      · exact hnot (by rw [heq]; exact List.mem_cons_self ..)
      · exact hnot (List.mem_cons_of_mem m hin)

/-- **`lastOf` OF A RUN WITH SOMETHING ABOVE `x` IS NOT `x`.** -/
theorem lastOf_append_cons_ne {L : List Card} {y : Card} {M : List Card}
    (hnot : y ∉ M) (hM : M ≠ []) : lastOf (L ++ y :: M) ≠ some y := by
  rw [lastOf_append_cons_eq]
  exact lastOf_cons_ne_of_notmem hnot hM

/-- If a face-up run is `P ++ x :: c :: R`, then `x` is not the top of any pile
(`c` sits above it, and cards are in at most one pile). -/
theorem not_top_of_above {st : State} (hwf : st.WF) {x c : Card} {a : Anchor}
    {P R : List Card} (hfu : (st.piles a).faceUp = P ++ x :: c :: R) :
    ¬ ∃ k : Anchor, st.topOf k = some x := by
  rintro ⟨k, htop⟩
  have hxmem : x ∈ (st.piles a).faceUp := by
    rw [hfu]
    exact List.mem_append.mpr (Or.inr (List.mem_cons_self ..))
  have hnd : (P ++ x :: c :: R).Nodup := by
    rw [← hfu]; exact runOK_nodup (hwf.runOK_of a)
  have hxR : x ∉ c :: R := by
    have hnd2 : (x :: c :: R).Nodup := (List.nodup_append.mp hnd).2.1
    exact (List.nodup_cons.mp hnd2).1
  have hR : c :: R ≠ [] := by simp
  have hne : lastOf (P ++ x :: c :: R) ≠ some x :=
    lastOf_append_cons_ne hxR hR
  have hk : k = a := by
    have hmem : x ∈ (st.piles k).faceUp := Pile.mem_of_top htop
    by_cases hka : k = a
    · exact hka
    · exact absurd hmem (mem_faceUp_unique hwf hxmem k hka).1
  subst hk
  have hlast : lastOf (st.piles k).faceUp = some x := htop
  rw [hfu] at hlast
  exact hne hlast

/-- **THE TWIN-BASE COROLLARY.**  If the face-up run is `P ++ x :: c :: R` (so
`c` sits directly on `x`), then every base `c` can be slid onto is `x.twin`:
the `inl` branch needs a king (impossible, `c` sits on `x`), and the `inr`
branch forces rank/colour `= x`, which is excluded because `x` is not a top. -/
theorem slide_base_of_above_twin {st : State} (hwf : st.WF) {x c : Card}
    {a : Anchor} {P R : List Card} {b : Base}
    (hfu : (st.piles a).faceUp = P ++ x :: c :: R)
    (hplace : st.canPlace c b = true) :
    b = Sum.inr x.twin := by
  have hok : runOK (P ++ x :: c :: R) = true := by
    rw [← hfu]; exact hwf.runOK_of a
  have hfit : canSitOn c x = true := CrossSuitF1.canSitOn_of_runOK_append P hok
  have hnk : c.rank ≠ Rank.king := not_king_of_above hfit
  have hnottop : ¬ ∃ k : Anchor, st.topOf k = some x := not_top_of_above hwf hfu
  cases b with
  | inl k =>
      exact absurd (CrossSuitF1.canPlace_inl_true_iff.mp hplace).2 hnk
  | inr z =>
      obtain ⟨-, hcz⟩ := CrossSuitF1.canPlace_inr_true_iff.mp hplace
      rcases fit_above_twin hfit hcz with h | h
      · -- `z = x` is impossible: `z` is a pile top, `x` is not
        exfalso
        subst h
        obtain ⟨k, hk⟩ := Option.ne_none_iff_exists'.mp
          (CrossSuitF1.canPlace_inr_true_iff.mp hplace).1
        exact hnottop ⟨k, (pileOfTop_eq_some_iff hwf).mp hk⟩
      · exact congrArg Sum.inr h

/-- A card that is next-up and supported at a saturated `WF` state is never a
pile top (a supported top has a nonempty chop beneath it). -/
theorem not_top_of_supported_of_ssaturated {st : State} (hwf : st.WF)
    (hs : SSaturated st) {x : Card} (hsup : ThirdHigh.Supported st x)
    (hnext : st.nextUp x = true) :
    ¬ ∃ a : Anchor, st.topOf a = some x := by
  rintro ⟨a, htop⟩
  obtain ⟨z, hz⟩ := hsup
  unfold seatOf at hz
  cases hp : st.pileHolding x with
  | none => rw [hp] at hz; exact absurd hz (by simp)
  | some a' =>
      simp only [hp] at hz
      have hmem : x ∈ (st.piles a').faceUp :=
        (pileHolding_eq_some_iff hwf).mp hp
      have hbelowne : below x (st.piles a').faceUp ≠ [] := by
        intro hnil
        rw [hnil] at hz
        exact absurd hz (by simp)
      have haa : a' = a := by
        by_cases h : a' = a
        · exact h
        · have htopmem : x ∈ (st.piles a).faceUp := Pile.mem_of_top htop
          exact absurd htopmem (mem_faceUp_unique hwf hmem a (Ne.symm h)).1
      subst haa
      have hlast : lastOf (st.piles a').faceUp = some x := htop
      have hne : (st.piles a').faceUp.Nodup := runOK_nodup (hwf.runOK_of a')
      have hchop : chop (st.piles a').faceUp ≠ [] := by
        rw [← NoSelfKit.below_eq_chop_of_last hne hlast]
        exact hbelowne
      have htop' : st.pileOfTop x = some a' :=
        (pileOfTop_eq_some_iff hwf).mpr htop
      exact not_canRaise_of_ssaturated hs x ⟨hnext, a', htop', Or.inl hchop⟩

/-! ## §4. The zero-rung theorem -/

/-- **AN ACE IS THE TOP OF ITS PILE.**  Nothing can sit on an ace in a legal
(`runOK`) face-up run. -/
theorem ace_top_of_mem {st : State} (hwf : st.WF) {a : Anchor} {x : Card}
    (hx : x.rank = Rank.ace) (hmem : x ∈ (st.piles a).faceUp) :
    st.topOf a = some x := by
  obtain ⟨P, R, hPxR⟩ := List.mem_iff_append.mp hmem
  have hok : runOK (P ++ x :: R) = true := by
    rw [← hPxR]; exact hwf.runOK_of a
  cases R with
  | nil =>
      show lastOf (st.piles a).faceUp = some x
      rw [hPxR]
      exact lastOf_snoc
  | cons c R' =>
      exfalso
      have hfit : canSitOn c x = true := CrossSuitF1.canSitOn_of_runOK_append P hok
      have h1 := (canSitOn_eq c x).mp hfit |>.1
      rw [hx] at h1
      have h0 : (Rank.ace).toIdx = 0 := rfl
      rw [h0] at h1
      omega

/-- **A SUPPORTED FACE-UP ACE IS VANILLA-RAISABLE** (given it is next-up): the
card beneath it is the giveback seat. -/
theorem canRaise_of_supported_ace {st : State} (hwf : st.WF) {x : Card}
    (hx : x.rank = Rank.ace) (hnext : st.nextUp x = true)
    (hsup : ThirdHigh.Supported st x) : CanRaise st x := by
  obtain ⟨z, hz⟩ := hsup
  unfold seatOf at hz
  have hp : st.pileHolding x ≠ none := by
    intro h
    rw [h] at hz
    exact absurd hz (by simp)
  obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.mp hp
  simp only [ha] at hz
  have hbelow : below x (st.piles a).faceUp ≠ [] := by
    intro hnil
    rw [hnil] at hz
    exact absurd hz (by simp)
  have hmem : x ∈ (st.piles a).faceUp :=
    (pileHolding_eq_some_iff hwf).mp ha
  have htop : st.topOf a = some x := ace_top_of_mem hwf hx hmem
  have htop' : st.pileOfTop x = some a :=
    (pileOfTop_eq_some_iff hwf).mpr htop
  have hchop : chop (st.piles a).faceUp ≠ [] := by
    rw [← NoSelfKit.below_eq_chop_of_last
      (runOK_nodup (hwf.runOK_of a)) htop]
    exact hbelow
  exact ⟨hnext, a, htop', Or.inl hchop⟩

/-- **THE ZERO-RUNG THEOREM.**  A saturated `WF` state with `rungAt G σ = 0` has
`rungAt H σ = 0` at every same-orbit `H` — the ace of `σ` can never be raised.

Proof: were `H`'s `σ`-foundation nonempty, the ace `x` is founded at `H` and
unfounded at `G`; the exodus transit (`supported_of_forked_transit`, along the
witness play `H → G`) makes `x` supported at `G`; a supported ace is its pile's
top with a card beneath it, so it is vanilla-raisable — against saturation. -/
theorem no_rise_from_zero {G H : State} (hG : G.WF) (hH : H.WF)
    (hsG : SSaturated G) (hcls : sameOrbitSetoid.r G H) (σ : Suit)
    (h0 : rungAt G σ = 0) : rungAt H σ = 0 := by
  apply Nat.le_zero.mp
  apply Nat.not_lt.mp
  intro hpos
  let x : Card := ⟨σ, Rank.ace⟩
  have hxrank : x.rank = Rank.ace := rfl
  have hxidx : x.rank.toIdx = 0 := rfl
  have hxH : x ∈ H.found x.suit := by
    apply FoundKit.mem_found_of_rung hH
    show x.rank.toIdx < rungAt H x.suit
    rw [hxidx]
    exact hpos
  have hxG : x ∉ G.found x.suit := by
    intro hm
    have h := FoundKit.mem_found_rank_lt hG hm
    rw [hxidx, h0] at h
    exact Nat.lt_irrefl 0 h
  obtain ⟨play, hplay, -⟩ := hcls
  have hnk : x.rank ≠ Rank.king := by
    show Rank.ace ≠ Rank.king
    decide
  have hsup : ThirdHigh.Supported G x :=
    ThirdHigh.supported_of_forked_transit hH hplay hnk hxH hxG
  have hnext : G.nextUp x = true := by
    unfold State.nextUp State.foundHeight
    rw [hxidx]
    show decide (0 = rungAt G σ) = true
    rw [h0]
    rfl
  exact not_canRaise_of_ssaturated hsG x (canRaise_of_supported_ace hG hxrank hnext hsup)

/-- **`NC` FROM A ZERO RUNG ON ONE SIDE.**  If `rungAt G σ = 0 < rungAt H σ` then
`NC G H` — no saturation of `H` is needed. -/
theorem nc_of_zero_side {G H : State} (hG : G.WF) (hH : H.WF)
    (hsG : SSaturated G) (hcls : sameOrbitSetoid.r G H) {σ : Suit}
    (h0 : rungAt G σ = 0) (hpos : 0 < rungAt H σ) : NC G H := by
  have hzero : rungAt H σ = 0 := no_rise_from_zero hG hH hsG hcls σ h0
  constructor
  · intro hle
    have := hle σ
    omega
  · intro hle
    have := hle σ
    omega

/-! ## §5. The residual: the exposure form of the price -/

/-- **`FrontierPrice` — THE EXACT RESIDUAL.**  If the `σ`-frontier card of a
saturated `G` is founded at a same-orbit `H` (that is exactly
`rungAt G σ < rungAt H σ`), then `H`'s rung vector is strictly below `G`'s in
some suit.  This is an inequality over the rung vector, gated at the *exposure
event*, not a restatement of the pointwise negation. -/
def FrontierPrice : Prop :=
  ∀ (G H : State) (σ : Suit), G.WF → H.WF → SSaturated G →
    sameOrbitSetoid.r G H → rungAt G σ < rungAt H σ →
    ∃ τ : Suit, rungAt H τ < rungAt G τ

/-- **`FrontierPrice` gives the target.** -/
theorem nc_of_frontierPrice (h : FrontierPrice) : NonComparability := by
  intro G H hG hH hsG hsH hcls hd
  have hnot : ¬ LeVec G H := by
    intro hle
    obtain ⟨σ, hσ⟩ := hd
    rcases Nat.lt_or_gt_of_ne hσ with hlt | hlt
    · obtain ⟨τ, hτ⟩ := h G H σ hG hH hsG hcls hlt
      exact Nat.not_le.mpr hτ (hle τ)
    · exact Nat.not_le.mpr hlt (hle σ)
  have hnot' : ¬ LeVec H G := by
    intro hle
    obtain ⟨σ, hσ⟩ := hd
    rcases Nat.lt_or_gt_of_ne hσ with hlt | hlt
    · exact Nat.not_le.mpr hlt (hle σ)
    · obtain ⟨τ, hτ⟩ := h H G σ hH hG hsH
        (sameOrbitSetoid.iseqv.symm hcls) hlt
      exact Nat.not_le.mpr hτ (hle τ)
  exact ⟨hnot, hnot'⟩

/-- **THE EXPOSURE HALF (PROVED).**  If the `σ`-frontier of `G` is founded at a
same-orbit `H`, then it is *supported* at `G` (it sits on a card).  This is the
`ThirdHigh` exodus transit read at the frontier card; it is the first step of
the residual, and the residual's remaining content is precisely "the price of
that exposure is still visible at `H`". -/
theorem frontier_supported_of_rise {G H : State} {σ : Suit}
    (hG : G.WF) (hH : H.WF) (hcls : sameOrbitSetoid.r G H)
    (h13 : rungAt G σ < 13) (hrise : rungAt G σ < rungAt H σ)
    (hnk : (⟨σ, FoundKit.Rk (rungAt G σ)⟩ : Card).rank ≠ Rank.king) :
    ThirdHigh.Supported G ⟨σ, FoundKit.Rk (rungAt G σ)⟩ := by
  have hidx : (⟨σ, FoundKit.Rk (rungAt G σ)⟩ : Card).rank.toIdx = rungAt G σ :=
    FoundKit.Rk_toIdx _ h13
  have hxH : (⟨σ, FoundKit.Rk (rungAt G σ)⟩ : Card) ∈ H.found σ := by
    apply FoundKit.mem_found_of_rung hH
    show (⟨σ, FoundKit.Rk (rungAt G σ)⟩ : Card).rank.toIdx <
      rungAt H (⟨σ, FoundKit.Rk (rungAt G σ)⟩ : Card).suit
    rw [hidx]
    exact hrise
  have hxG : (⟨σ, FoundKit.Rk (rungAt G σ)⟩ : Card) ∉ G.found σ := by
    intro hm
    have h := FoundKit.mem_found_rank_lt hG hm
    rw [hidx] at h
    exact Nat.lt_irrefl _ h
  obtain ⟨play, hplay, -⟩ := hcls
  exact ThirdHigh.supported_of_forked_transit hH hplay hnk hxH hxG

/-- **A COVERED FRONTIER IS NEVER A TOP AT A SATURATED STATE** — the second
step of the residual, read at the frontier card. -/
theorem frontier_not_top_of_saturated {G : State} (hG : G.WF)
    (hs : SSaturated G) {σ : Suit} (h13 : rungAt G σ < 13)
    (hsup : ThirdHigh.Supported G ⟨σ, FoundKit.Rk (rungAt G σ)⟩) :
    ¬ ∃ a : Anchor, G.topOf a = some ⟨σ, FoundKit.Rk (rungAt G σ)⟩ := by
  have hidx : (⟨σ, FoundKit.Rk (rungAt G σ)⟩ : Card).rank.toIdx = rungAt G σ :=
    FoundKit.Rk_toIdx _ h13
  apply not_top_of_supported_of_ssaturated hG hs hsup
  unfold State.nextUp State.foundHeight
  rw [hidx]
  show decide (rungAt G σ = rungAt G σ) = true
  exact decide_eq_true rfl

/-! ## §6. The twin-drop sharpening (stated, and FALSE) -/

/-- **`TwinDrop` — the sharpened conjecture: the price is paid on the twin suit.**

*FALSE* — certified by the explicit saturated same-orbit pair
`(5,0,4,2) → (6,0,2,5)` (`Temp/NC_dump4.py`, `Temp/NC_Report.md` §4): the
hearts rise `5 → 6` while the diamonds (its twin) stay at `0`.  The price is
paid on *spades* (`4 → 2`).  Kept as a `def` because `nc_of_twinDrop` is the
inference the lane would like to have, and the refutation fixes where the
kernel content cannot be. -/
def TwinDrop : Prop :=
  ∀ (G H : State) (σ : Suit), G.WF → H.WF → SSaturated G → SSaturated H →
    sameOrbitSetoid.r G H → rungAt G σ < rungAt H σ →
    rungAt H σ.twin < rungAt G σ.twin

/-- **`TwinCap` — THE SURVIVING SHARPENING CANDIDATE.**  A rise in `σ` caps the
*twin* column at `H` by the level the rise started from:

```text
rungAt G σ < rungAt H σ  →  rungAt H σ.twin ≤ rungAt G σ.
```

Unlike `TwinDrop` this is **consistent** with the `(5,0,4,2) → (6,0,2,5)`
certificate (the hearts rise `5 → 6`, and the diamonds `0 ≤ 5`).  Measured
6 369 / 6 369 rises over the two seven-family sweep seeds
(`Temp/NC_cap_sweep.py`), 0 violations.  It does **not** by itself give `NC`
(it caps a column; it does not force a drop) — it is recorded as the sharpening
the next attempt should target, with its proved consequence
`twinCap_excludes_both_rises`. -/
def TwinCap : Prop :=
  ∀ (G H : State) (σ : Suit), G.WF → H.WF → SSaturated G → SSaturated H →
    sameOrbitSetoid.r G H → rungAt G σ < rungAt H σ →
    rungAt H σ.twin ≤ rungAt G σ

/-- **A PROVED CONSEQUENCE OF `TwinCap`**: the two twins of a colour pair can
never both rise (the two caps cross). -/
theorem twinCap_excludes_both_rises (h : TwinCap) {G H : State}
    (hG : G.WF) (hH : H.WF) (hsG : SSaturated G) (hsH : SSaturated H)
    (hcls : sameOrbitSetoid.r G H) {σ : Suit}
    (h1 : rungAt G σ < rungAt H σ)
    (h2 : rungAt G σ.twin < rungAt H σ.twin) : False := by
  have hc1 := h G H σ hG hH hsG hsH hcls h1
  have hc2 := h G H σ.twin hG hH hsG hsH hcls h2
  rw [Suit.twin_twin] at hc2
  omega

/-- **`NC` FROM `TwinDrop`** (one rise plus one twin drop). -/
theorem nc_of_twinDrop (h : TwinDrop) : NonComparability := by
  intro G H hG hH hsG hsH hcls hd
  constructor
  · intro hle
    obtain ⟨σ, hσ⟩ := hd
    rcases Nat.lt_or_gt_of_ne hσ with hlt | hlt
    · exact Nat.not_le.mpr (h G H σ hG hH hsG hsH hcls hlt) (hle σ.twin)
    · exact Nat.not_le.mpr hlt (hle σ)
  · intro hle
    obtain ⟨σ, hσ⟩ := hd
    rcases Nat.lt_or_gt_of_ne hσ with hlt | hlt
    · exact Nat.not_le.mpr hlt (hle σ)
    · exact Nat.not_le.mpr (h H G σ hH hG hsH hsG
        (sameOrbitSetoid.iseqv.symm hcls) hlt) (hle σ.twin)

/-! ## §7. What the target does (and does not) give the lane

Two consequences, both unconditional:

* `meet_strictly_below_both` — `NC` forces the componentwise meet to be strictly
  below **each** endpoint in some suit.  So a comparable pair is exactly a pair
  whose meet position *is* an endpoint's position;
* `not_forkState_of_same_position_saturated` — a `Position` that carries a
  saturated state carries **no** `forkState` (via
  `MeetCoverTwo.forkState_of_same_position`).  Hence a comparable pair would
  break `ForkAtMeet` outright: this is the precise sense in which
  `MEETFULL_bad = 0` *is* the statement that no comparable pair occurred.

The converse direction is NOT formal: `NC` constrains the *two endpoints*, while
`PairMeetTight` needs the fork rank to be attained by at least one endpoint
(`pairMeetTight_iff_not_both_above`); nothing in `NC` mentions the fork state
`F`, which is **not** saturated and is outside the target's scope.  §8 records
that as the residual `PairMeetTight` really is. -/

/-- **`NC` PUTS THE MEET STRICTLY BELOW EACH ENDPOINT.** -/
theorem meet_strictly_below_both {G H : State} (h : NC G H) :
    (∃ σ, min (rungAt G σ) (rungAt H σ) < rungAt G σ) ∧
      (∃ σ, min (rungAt G σ) (rungAt H σ) < rungAt H σ) := by
  obtain ⟨⟨σ, hσ⟩, ⟨τ, hτ⟩⟩ := (nc_iff_both_signs G H).mp h
  refine ⟨⟨τ, ?_⟩, ⟨σ, ?_⟩⟩
  · have h2 : min (rungAt G τ) (rungAt H τ) = rungAt H τ :=
      Nat.min_eq_right (a := rungAt G τ) (b := rungAt H τ) (Nat.le_of_lt hτ)
    rw [h2]; exact hτ
  · have h2 : min (rungAt G σ) (rungAt H σ) = rungAt G σ :=
      Nat.min_eq_left (a := rungAt G σ) (b := rungAt H σ) (Nat.le_of_lt hσ)
    rw [h2]; exact hσ

/-- A saturated state is never a fork state. -/
theorem not_forkState_of_ssaturated {G : State} (hs : SSaturated G) :
    ¬ forkState G := by
  rintro ⟨x, hx⟩
  exact (LedgerKit.not_ssaturated_of_fork hx) hs

/-- **A SATURATED STATE NEVER SITS AT A FORK'S `Position`.**  At the Position of
a `forkState`, every same-position member is a `forkState`
(`MeetCoverTwo.forkState_of_same_position`); a saturated member is not. -/
theorem not_saturated_at_fork_position {F G : State} (hF : F.WF) (hG : G.WF)
    {x : Card} (hx : ForkWitness F x) (hsG : SSaturated G)
    (hpos : (Quotient.mk orbitRungSetoid ⟨G, hG⟩ : Position) =
      (Quotient.mk orbitRungSetoid ⟨F, hF⟩)) : False :=
  not_forkState_of_ssaturated hsG
    (MeetCoverTwo.forkState_of_same_position hF hx hpos)

/-! ## §8. The exact open obligation of MEET-PAIR, restated -/

/-- **`PairMeetTight` WITHOUT `min`**: the fork rank is attained on each pair
suit by **at least one** endpoint — equivalently, the two endpoints are never
both strictly above the fork rank in one pair suit.

This is `ForkFib.PairMeetTight` with the `min` rewritten (`min a b ≤ k ↔
a ≤ k ∨ b ≤ k`).  It is the one geometric claim of the lane that non-comparability
does **not** supply (see the §7 note); `PairFloorLocal` supplies the other
half. -/
def PairMeetTight' : Prop :=
  ∀ (F G H : State) (x : Card), F.WF → G.WF → H.WF →
    sameOrbitSetoid.r F G → sameOrbitSetoid.r F H →
    ForkWitness F x → SSaturated G → SSaturated H →
    (∃ σ : Suit, rungAt G σ ≠ rungAt H σ) →
    (rungAt G x.suit ≤ x.rank.toIdx ∨ rungAt H x.suit ≤ x.rank.toIdx) ∧
      (rungAt G x.twin.suit ≤ x.rank.toIdx ∨
        rungAt H x.twin.suit ≤ x.rank.toIdx)

/-- The two spellings agree (pure `Nat` `min` arithmetic, four suits). -/
theorem pairMeetTight'_iff :
    PairMeetTight' ↔ ForkFib.PairMeetTight := by
  constructor
  · intro h F G H x hF hG hH hFG hFH hx hsG hsH hd
    obtain ⟨h1, h2⟩ := h F G H x hF hG hH hFG hFH hx hsG hsH hd
    exact ⟨by omega, by omega⟩
  · intro h F G H x hF hG hH hFG hFH hx hsG hsH hd
    obtain ⟨h1, h2⟩ := h F G H x hF hG hH hFG hFH hx hsG hsH hd
    exact ⟨by omega, by omega⟩

end NonComp

/-! ## Axiom battery -/

#print axioms NonComp.nc_iff_both_signs
#print axioms NonComp.not_leVec_iff_rises
#print axioms NonComp.nc_of_rises
#print axioms NonComp.rises_of_nc
#print axioms NonComp.rungDiffers_of_nc
#print axioms NonComp.rungSum_le_of_leVec
#print axioms NonComp.eq_of_leVec_of_sum_le
#print axioms NonComp.nc_of_sum_eq
#print axioms NonComp.not_canRaise_of_ssaturated
#print axioms NonComp.pull_landing_not_ssaturated
#print axioms NonComp.suit_eq_or_twin_of_color_eq
#print axioms NonComp.fit_above_twin
#print axioms NonComp.not_king_of_above
#print axioms NonComp.lastOf_append_cons_ne
#print axioms NonComp.slide_base_of_above_twin
#print axioms NonComp.not_top_of_supported_of_ssaturated
#print axioms NonComp.ace_top_of_mem
#print axioms NonComp.canRaise_of_supported_ace
#print axioms NonComp.no_rise_from_zero
#print axioms NonComp.nc_of_zero_side
#print axioms NonComp.nc_of_frontierPrice
#print axioms NonComp.frontier_supported_of_rise
#print axioms NonComp.frontier_not_top_of_saturated
#print axioms NonComp.nc_of_twinDrop
#print axioms NonComp.twinCap_excludes_both_rises
#print axioms NonComp.TwinCap
#print axioms NonComp.meet_strictly_below_both
#print axioms NonComp.not_forkState_of_ssaturated
#print axioms NonComp.not_saturated_at_fork_position
#print axioms NonComp.pairMeetTight'_iff
#print axioms NonComp.NonComparability
#print axioms NonComp.TwinDrop
#print axioms NonComp.PairMeetTight'
#print axioms NonComp.FrontierPrice
