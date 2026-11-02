import Orig2.Fork.ForkLandingLocal
import Orig2.Fork.ForkMountain
import Orig2.Fork.ForkLedger
import Orig2.Fork.ForkSplitResidual

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

/-!
# Orig2/ForkThirdLive — the rank fingerprint of a third-suit live card

READ-ONLY scratch (no source touched, no commit).  Zero `sorry`, zero
`Classical.choice`, zero `native_decide`; battery at the tail.

## What is proved here

1. `rank_eq_rungAt_of_canRaiseS` — **THE NARROWING**.  At `WF`, every
   `CanRaiseS` card is the *frontier* card of its own suit: `e.rank.toIdx =
   rungAt st e.suit`.  (Immediate from the flat characterization's `nextUp`
   clause, `LandKit.canRaiseS_below_form`; no cargo induction.)

2. `third_frontier_at_split` — at a genuine valley split, a third-suit live
   card `e` at the pull's landing `B` is the frontier card of its suit at
   `A'` (before the pull), at `B` (after the pull) and at the valley bottom
   `F`: the pull does not touch a third suit's rung and the free tail
   `B → F` does not touch any rung.

3. `pull_card_frontier_at_split` — the same fingerprint for the pulled card
   `c` at `B` and `F`.  With (2) this makes the brief's rank dichotomy
   `rank(e) = rank(c)` vs `rank(e) ≠ rank(c)` a comparison of *rungs*.

4. `third_alive_at_F` — a third-suit live card at the landing is S-live at
   the bottom too (the free tail transports the license).

5. `card_eq_of_suit_rank` / `unique_third_frontier` — a suit has at most one
   card at a given rank, so at the bottom the third-suit frontier card is
   *unique*: any other card of the same suit and rank is `e`.

6. `no_sigma_letter_of_final_rung_eq` — **THE RUNG-FROZEN CASE IS LETTER-FREE**:
   if the third suit's rung is the same at the bottom and at the far
   endpoint, then the whole right leg (the pull-free mountain leg) carries
   no letter of that suit.  (Ledger + `IsPull`-freeness.)  This is the
   sharpest reduction of case (a) available without minimality data.

7. `third_rung_le_of_raise_free` etc. — the mountain inequalities restated
   for a third suit at a split.
-/

namespace ThirdLive

open ValleyElim
open Bubble

/-! ## §0. Card geometry -/

/-- A card is its suit and its rank: equal suit and equal rank give the
same card.  (No `WF` needed; `Card` is a two-field structure.) -/
theorem card_eq_of_suit_rank {a b : Card} (hs : a.suit = b.suit)
    (hr : a.rank = b.rank) : a = b := by
  cases a with
  | mk as ar =>
    cases b with
    | mk bs br =>
      simp only [Card.mk.injEq] at hs hr ⊢
      exact ⟨hs, hr⟩

/-- The twin keeps the rank. -/
theorem twin_rank_eq (c : Card) : c.twin.rank = c.rank := Card.twin_rank c

/-! ## §1. The rank fingerprint -/

/-- **THE NARROWING.**  At a `WF` state, an S-live card is the next card of
its suit: its rank index equals its suit's current rung. -/
theorem rank_eq_rungAt_of_canRaiseS {st : State} (hwf : st.WF) {e : Card}
    (he : CanRaiseS st e) : e.rank.toIdx = rungAt st e.suit := by
  have hnext := ((LandKit.canRaiseS_below_form hwf).mp he).1
  have h := of_decide_eq_true hnext
  simpa [State.nextUp, State.foundHeight, rungAt] using h

/-- The same fingerprint read as `nextUp`. -/
theorem nextUp_of_canRaiseS {st : State} (hwf : st.WF) {e : Card}
    (he : CanRaiseS st e) : st.nextUp e = true :=
  ((LandKit.canRaiseS_below_form hwf).mp he).1

/-- **Uniqueness of the suit-rank card.**  There is only one card of a given
suit and rank, so a live card `e` is determined by its suit and rank. -/
theorem eq_of_suit_eq_rank_toIdx_eq {a b : Card} (hs : a.suit = b.suit)
    (hr : a.rank.toIdx = b.rank.toIdx) : a = b :=
  card_eq_of_suit_rank hs (Rank.toIdx_inj hr)

/-! ## §2. The pull crossing at a split -/

/-- The pull of `c` fixes every suit's rung except `c.suit`. -/
theorem rungAt_of_pull_of_ne {A B : State} {c : Card} {b : Base}
    (hstep : State.step A (Move.foundToTab c b) = some B) {σ : Suit}
    (hσ : σ ≠ c.suit) : rungAt B σ = rungAt A σ := by
  rw [rungAt_foundToTab hstep σ, ite_eq_right hσ]

/-- A free play fixes every rung (restated at a single suit). -/
theorem rungAt_of_free_play {B F : State} {post : List Move}
    (hplay : ShufflePlayW B post F) (hfree : ∀ m ∈ post, FreeMove m) (σ : Suit) :
    rungAt F σ = rungAt B σ :=
  rungAt_eq_of_free_play hplay hfree σ

/-- **THE THIRD-SUIT FRONTIER AT A SPLIT.**  A third-suit card `e` that is
S-live at the pull's landing `B` (and is neither `c` nor `c.twin`) is the
frontier card of its own suit at `A'`, at `B` and at the bottom `F`: the
pull leaves a third suit's rung alone and the free tail `B → F` leaves every
rung alone. -/
theorem third_frontier_at_split
    {u v : State} {ρ : List Move} {F : State} {left right : List Move}
    {c d : Card} {b : Base} {pre post tail : List Move}
    (h : SplitKit.SplitHyp u v ρ F left right c d b pre post tail)
    {A' B : State} (hpre : ShufflePlayW u pre A')
    (hstep : State.step A' (Move.foundToTab c b) = some B)
    {e : Card} (he : CanRaiseS B e) (hec : e ≠ c) (het : e ≠ c.twin)
    (hsuit : e.suit ≠ c.suit) :
    e.rank.toIdx = rungAt B e.suit ∧ e.rank.toIdx = rungAt A' e.suit ∧
      e.rank.toIdx = rungAt F e.suit := by
  have hk := h
  obtain ⟨huwf, -, -, -, -, -, -, hleft, hright, hshape, hfree, hrt⟩ := h
  have hA' : A'.WF := SatDifferCensus.ShufflePlayW.wf_end hpre huwf
  have hB : B.WF := step_wf hA' hstep
  obtain ⟨hpost, -⟩ := Landing.post_play_of_landing hk hpre hstep
  have hBrank : e.rank.toIdx = rungAt B e.suit :=
    rank_eq_rungAt_of_canRaiseS hB he
  have hliveA : CanRaiseS A' e := by
    rcases LandKit.local_dichotomy hA' hstep he hec with htw | hA
    · exact absurd htw het
    · exact hA
  have hArank : e.rank.toIdx = rungAt A' e.suit :=
    rank_eq_rungAt_of_canRaiseS hA' hliveA
  have hAB : rungAt B e.suit = rungAt A' e.suit :=
    rungAt_of_pull_of_ne hstep (fun hce => hsuit hce)
  have hBF : rungAt F e.suit = rungAt B e.suit :=
    rungAt_of_free_play hpost hfree e.suit
  exact ⟨hBrank, by rw [hBrank, hAB], by rw [hBrank, hBF]⟩

/-- **THE PULLED CARD'S FRONTIER AT A SPLIT.**  The pulled card `c` is the
frontier card of `c.suit` at the landing `B` and at the bottom `F`: the pull
lowers its suit's rung by exactly one and the free tail fixes it. -/
theorem pull_card_frontier_at_split
    {u v : State} {ρ : List Move} {F : State} {left right : List Move}
    {c d : Card} {b : Base} {pre post tail : List Move}
    (h : SplitKit.SplitHyp u v ρ F left right c d b pre post tail)
    {A' B : State} (hpre : ShufflePlayW u pre A')
    (hstep : State.step A' (Move.foundToTab c b) = some B) :
    c.rank.toIdx = rungAt B c.suit ∧ c.rank.toIdx = rungAt F c.suit := by
  have hk := h
  obtain ⟨huwf, -, -, -, -, -, -, hleft, hright, hshape, hfree, hrt⟩ := h
  have hA' : A'.WF := SatDifferCensus.ShufflePlayW.wf_end hpre huwf
  have hB : B.WF := step_wf hA' hstep
  obtain ⟨hpost, -⟩ := Landing.post_play_of_landing hk hpre hstep
  obtain ⟨c', htop, hc', hcp, heq⟩ := step_foundToTab_inv hstep
  have htop' : A'.foundTop c.suit = some c := by
    rw [hc'] at htop
    exact htop
  have hidx : c.rank.toIdx + 1 = rungAt A' c.suit :=
    SatDifferCensus.foundTop_rank_succ hA' htop'
  have hpull : rungAt B c.suit = rungAt A' c.suit - 1 := by
    rw [rungAt_foundToTab hstep c.suit, ite_eq_left rfl]
  have hBrank : c.rank.toIdx = rungAt B c.suit := by rw [hpull]; omega
  have hBF : rungAt F c.suit = rungAt B c.suit :=
    rungAt_of_free_play hpost hfree c.suit
  exact ⟨hBrank, by rw [hBrank, hBF]⟩

/-- **A THIRD-SUIT LIVE CARD IS LIVE AT THE BOTTOM TOO.**  The free tail
`B → F` transports the S-license in both directions. -/
theorem third_alive_at_F
    {u v : State} {ρ : List Move} {F : State} {left right : List Move}
    {c d : Card} {b : Base} {pre post tail : List Move}
    (h : SplitKit.SplitHyp u v ρ F left right c d b pre post tail)
    {A' B : State} (hpre : ShufflePlayW u pre A')
    (hstep : State.step A' (Move.foundToTab c b) = some B)
    {e : Card} (he : CanRaiseS B e) : CanRaiseS F e := by
  have hk := h
  obtain ⟨huwf, -, -, -, -, -, -, hleft, hright, hshape, hfree, hrt⟩ := h
  obtain ⟨hpost, hB⟩ := Landing.post_play_of_landing hk hpre hstep
  exact (Mech.canRaiseS_landing_iff hB hpost hfree e).mp he

/-- The uniqueness of the third-suit frontier card at the bottom: any card of
`e`'s suit whose rank index equals `e`'s rank index *is* `e`. -/
theorem unique_frontier_of_rank_eq {f e : Card}
    (hs : f.suit = e.suit) (hr : f.rank.toIdx = e.rank.toIdx) : f = e :=
  eq_of_suit_eq_rank_toIdx_eq hs hr

/-! ## §3. The pull-free leg carries no letter of a frozen suit -/

/-- `raisesOf right σ = 0` and `pullsOf right σ = 0` iff the play contains no
`σ` pull and no `σ` raise. -/
theorem no_sigma_letter_of_no_sigma_counts {right : List Move} {σ : Suit}
    (hp : pullsOf right σ = 0) (hr : raisesOf right σ = 0) :
    ∀ m ∈ right,
      (∀ (c' : Card) (b' : Base), m = Move.foundToTab c' b' → c'.suit ≠ σ) ∧
      (∀ c' : Card, m = Move.tabToFound c' → c'.suit ≠ σ) := by
  intro m hm
  refine ⟨?_, ?_⟩
  · intro c' b' hmb hcs
    have : 0 < pullsOf right σ :=
      LedgerKit.pullsOf_pos_iff.mpr ⟨c', b', hcs, by rw [← hmb]; exact hm⟩
    omega
  · intro c' hmb hcs
    have : 0 < raisesOf right σ :=
      LedgerKit.raisesOf_pos_iff.mpr ⟨c', hcs, by rw [← hmb]; exact hm⟩
    omega

/-- **THE RUNG-FROZEN CASE IS LETTER-FREE.**  If the right leg is pull-free
and the suit's rung is the same at the bottom `F` and the far endpoint `v`,
then the right leg contains no letter of that suit at all.  (The ledger
splits the rung change into the counting of `σ` pulls and raises; pull-freeness
kills the raises by balance.) -/
theorem no_sigma_letter_of_final_rung_eq {F v : State} {right : List Move}
    {σ : Suit} (hplay : ShufflePlayW F right v)
    (hnoPull : ∀ m ∈ right, ¬ IsPull m) (hrung : rungAt v σ = rungAt F σ) :
    ∀ m ∈ right,
      (∀ (c' : Card) (b' : Base), m = Move.foundToTab c' b' → c'.suit ≠ σ) ∧
      (∀ c' : Card, m = Move.tabToFound c' → c'.suit ≠ σ) := by
  have hled := LedgerKit.rungAt_ledger (u := F) (v := v) (ρ := right) (σ := σ) hplay
  -- no `σ`-pull can occur, so `pullsOf = 0`
  have hp0 : pullsOf right σ = 0 := by
    cases hp : pullsOf right σ with
    | zero => rfl
    | succ k =>
        have hpos : 0 < pullsOf right σ := by rw [hp]; omega
        obtain ⟨c', b', hcs, hmem⟩ := LedgerKit.pullsOf_pos_iff.mp hpos
        exact absurd ⟨c', b', rfl⟩ (hnoPull _ hmem)
  -- hence `raisesOf = 0` by the ledger
  have hr0 : raisesOf right σ = 0 := by omega
  exact no_sigma_letter_of_no_sigma_counts hp0 hr0

/-! ## §4. The mountain inequalities at a split -/

/-- **THE FAR ENDPOINT'S RUNG IS ABOVE THE BOTTOM'S** on a pull-free leg. -/
theorem rungAt_le_of_split_right
    {u v F : State} {left right : List Move} {σ : Suit}
    (hleft : ShufflePlayW u left F) (hright : ShufflePlayW F right v)
    (hnoRaise : ∀ m ∈ left, ¬ IsRaise m)
    (hnoPull : ∀ m ∈ right, ¬ IsPull m) :
    rungAt F σ ≤ rungAt u σ ∧ rungAt F σ ≤ rungAt v σ :=
  MountainKit.mountain_bottom_le hleft hright hnoRaise hnoPull

/-- The valley bottom is below both endpoints at every third suit, once the
split is a mountain split. -/
theorem split_bottom_le
    {u v F : State} {left right : List Move}
    (hleft : ShufflePlayW u left F) (hright : ShufflePlayW F right v)
    (hms : MountainKit.MountainSplit left right) (σ : Suit) :
    rungAt F σ ≤ rungAt u σ ∧ rungAt F σ ≤ rungAt v σ :=
  MountainKit.mountain_bottom_le_vec hleft hright hms σ

end ThirdLive

#print axioms ThirdLive.card_eq_of_suit_rank
#print axioms ThirdLive.rank_eq_rungAt_of_canRaiseS
#print axioms ThirdLive.nextUp_of_canRaiseS
#print axioms ThirdLive.eq_of_suit_eq_rank_toIdx_eq
#print axioms ThirdLive.rungAt_of_pull_of_ne
#print axioms ThirdLive.rungAt_of_free_play
#print axioms ThirdLive.third_frontier_at_split
#print axioms ThirdLive.pull_card_frontier_at_split
#print axioms ThirdLive.third_alive_at_F
#print axioms ThirdLive.unique_frontier_of_rank_eq
#print axioms ThirdLive.no_sigma_letter_of_no_sigma_counts
#print axioms ThirdLive.no_sigma_letter_of_final_rung_eq
#print axioms ThirdLive.rungAt_le_of_split_right
#print axioms ThirdLive.split_bottom_le
