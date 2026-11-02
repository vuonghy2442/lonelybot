import Orig2.ForkOffWindow
import Orig2.ForkFace2
import Orig2.ForkTwinBarrier

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-!
# Extract_MultiSlide — the MULTI-SLIDE prepared-seat extraction

READ-ONLY scratch card (`Temp/`).  No source edit, no commit.  Zero `sorry`,
zero `Classical.choice`, zero `nativeDecide`; axiom battery at the tail.

## What is proved

`Orig2/ForkOffWindow.lean` closes the prepared seat when the free window is a
**single** letter: the exposing slide is pinned to

```text
slide d.twin : z → z.twin      (OffWindow.slide_expose_base_eq_twin)
pull  d      : foundation → z
```

This card removes the single-letter hypothesis.  The window `γ` between the
raise's image `B` and the pull's origin `P` contains arbitrarily many free
letters; the extraction is done at the **letter grade**:

* §1 `slide_off_seat_twin_swap` — the kernel arithmetic with the pull removed
  from the hypothesis list: whenever a slide at a `WF` state moves the card
  `x` sitting *directly on* `z` (run `front ++ z :: x :: rest`), and `d` is a
  card of `z`'s fitting class that lives on the foundation, then
  `x = d.twin` **and** the slide's base is exactly `Sum.inr z.twin`.  The
  pull appears only as the *source* of two scalar data (`d`'s fit on `z`,
  `d`'s foundation membership), so it may fire arbitrarily far downstream.
* §2 `exposure_shape` — a reversible slide that turns `z` from "not a pile
  top" into "a pile top" must move the run sitting directly on `z`; the run
  shape `front ++ z :: x :: rest` is *extracted* from the slide data.
* §3 `exposure_letter_is_twin_swap` — **the ∀ form.**  Every seat-exposing
  letter of every free window is the twin swap `d.twin : z → z.twin`.
* §4 `slide_change_dichotomy` — every letter that changes `pileOfTop z` is
  (a) an exposure, (b) a *relocation* of `z` from one pile top to another, or
  (c) a burial of `z`.  (b) is the honest residual: the twin calculus does
  not exclude it.
* §5 `exists_exposure` — a free window that starts covered and ends exposed
  contains an exposure letter (cut at the first one).
* §6 `corridor_prepared_seat_twin_swap` — the corridor-level form
  (deliverable (a)): in the prepared-seat face the window carries a letter
  `tabToTab d.twin (inr z.twin)` whose origin runs `front ++ z :: d.twin :: rest`,
  with **no** single-slide hypothesis, and that letter is exactly the one that
  flips `canPlace d (inr z)` from `false` to `true`.
* §7 the honest remainder: the **relocation** branch (a slide that carries the
  already-exposed `z` from one pile top to another) and the saturation lock — the
  twin swap is *legal* (`twin_exchange_legal`), the rung pin is *entailed*
  (`TwinLink.mate_raise_rungAt`), so the twin calculus alone does not contradict
  `NoWindowPreparedSeat`.
* §8 the **literal last-touch split**: `TopConst` (the "seat-constant play"
  inductive) + `last_seat_change` (strong recursion on the length) — the window
  factors as `γ₁ ++ q :: γ₂` with `q` the last seat change and `TopConst z R γ₂ P`.
  `last_change_prepared_seat` then classifies `q`: the twin swap, or a
  **relocation** of the already exposed `z` (never a burial).
* §9 `corridor_last_change_dichotomy` — the two above at the corridor.
-/

namespace Extract

/-! ## §1. The kernel arithmetic, pull-free

`OffWindow.slide_expose_card_twin` takes the pull as the *immediately next*
letter.  Nothing in its arithmetic uses that adjacency: the pull is only the
source of (i) `d`'s fit on `z` (`canSitOn` is state-free) and (ii) `d`'s
foundation membership.  Both are supplied below as scalar hypotheses, so the
slide may be followed by an arbitrary window. -/

/-- **THE TWIN IDENTITY, PULL-FREE.**  If `x` sits directly on `z` (a `WF`
run), and `d` is a card of `z`'s fitting class founded on `d.suit`, then the
slide of `x` moves exactly `d.twin`. -/
theorem slide_off_seat_card_twin
    {B C : State} {a : Anchor} {front rest : List Card} {x z d : Card} {y : Base}
    (hBwf : B.WF)
    (hface : (B.piles a).faceUp = front ++ z :: x :: rest)
    (hslide : State.step B (Move.tabToTab x y) = some C)
    (hdz : d.rank.toIdx + 1 = z.rank.toIdx)
    (hdc : d.suit.color ≠ z.suit.color)
    (hdf : d ∈ B.found d.suit) :
    x = d.twin := by
  have hxmem : x ∈ (B.piles a).faceUp := by rw [hface]; simp
  have hxzone : x ∈ pileZone B a := List.mem_append_right _ hxmem
  have hne : x ≠ d := fun hxd => wf_pile_found_ne hBwf (hxd ▸ hxzone) hdf
  have hrok : runOK (B.piles a).faceUp = true := hBwf.runOK_of a
  rw [hface] at hrok
  have hxz := SeedKit.runOK_adjacent_fit z x front rest hrok
  obtain ⟨hxzr, hxzc⟩ := (canSitOn_eq x z).mp hxz
  exact OffWindow.twin_of_two_fits hxzr hxzc hdz hdc hne

/-- **THE BASE IDENTITY, PULL-FREE.**  If in addition the slide lands on
`inr w` with `w ≠ z`, then `w = z.twin` — the same two-card class argument as
`OffWindow.slide_expose_base_twin`, with the pull's data supplied scalarly. -/
theorem slide_off_seat_base_twin
    {B C : State} {a : Anchor} {front rest : List Card} {x z d w : Card} {y : Base}
    (hBwf : B.WF)
    (hface : (B.piles a).faceUp = front ++ z :: x :: rest)
    (hslide : State.step B (Move.tabToTab x y) = some C)
    (hdz : d.rank.toIdx + 1 = z.rank.toIdx)
    (hdc : d.suit.color ≠ z.suit.color)
    (hdf : d ∈ B.found d.suit)
    (hy : y = Sum.inr w) (hwz : w ≠ z) :
    w = z.twin := by
  have hxt : x = d.twin := slide_off_seat_card_twin hBwf hface hslide hdz hdc hdf
  have hxmem : x ∈ (B.piles a).faceUp := by rw [hface]; simp
  have hxzone : x ∈ pileZone B a := List.mem_append_right _ hxmem
  have hne : x ≠ d := fun hxd => wf_pile_found_ne hBwf (hxd ▸ hxzone) hdf
  have hrok : runOK (B.piles a).faceUp = true := hBwf.runOK_of a
  rw [hface] at hrok
  have hxz := SeedKit.runOK_adjacent_fit z x front rest hrok
  obtain ⟨hxzr, hxzc⟩ := (canSitOn_eq x z).mp hxz
  have hcpS : B.canPlace x y = true := OffWindow.slide_canPlace hslide
  rw [hy] at hcpS
  obtain ⟨_k2, -, hxw⟩ := canPlace_inr hcpS
  obtain ⟨hxwr, hxwc⟩ := (canSitOn_eq x w).mp hxw
  exact OffWindow.twin_base_of_fits hxzr hxzc hdz hdc hne hxwr hxwc hwz

/-- **THE EMPTY-PILE BASE DIES, PULL-FREE.**  A slide of `z`'s cover can never
land on an empty pile: that would make the cover a king, hence `d` a king,
hence `z.rank = 13`. -/
theorem slide_off_seat_base_not_inl
    {B C : State} {a : Anchor} {front rest : List Card} {x z d : Card} {y : Base}
    (hBwf : B.WF)
    (hface : (B.piles a).faceUp = front ++ z :: x :: rest)
    (hslide : State.step B (Move.tabToTab x y) = some C)
    (hdz : d.rank.toIdx + 1 = z.rank.toIdx)
    (hdc : d.suit.color ≠ z.suit.color)
    (hdf : d ∈ B.found d.suit)
    (hinl : ∃ a', y = Sum.inl a') : False := by
  have hxt : x = d.twin := slide_off_seat_card_twin hBwf hface hslide hdz hdc hdf
  have hcpS := OffWindow.slide_canPlace hslide
  obtain ⟨a', rfl⟩ := hinl
  obtain ⟨-, hpk⟩ := canPlace_inl hcpS
  have hdk : d.rank = Rank.king := by
    have : d.twin.rank = Rank.king := by rw [← hxt]; exact hpk
    simpa [Card.twin] using this
  have h13 : z.rank.toIdx = 13 := by
    rw [hdk] at hdz
    have : Rank.king.toIdx = 12 := rfl
    omega
  have hlt := Rank.toIdx_lt z.rank
  omega

/-- **THE MULTI-SLIDE TWIN SWAP.**  The exposing slide of the seat `z` is
exactly `d.twin : z → z.twin`.  No hypothesis relates the slide to the pull
positionally: only `d`'s fit on `z` and `d`'s foundation membership enter. -/
theorem slide_off_seat_twin_swap
    {B C : State} {a : Anchor} {front rest : List Card} {x z d : Card} {y : Base}
    (hBwf : B.WF)
    (hface : (B.piles a).faceUp = front ++ z :: x :: rest)
    (hslide : State.step B (Move.tabToTab x y) = some C)
    (hdz : d.rank.toIdx + 1 = z.rank.toIdx)
    (hdc : d.suit.color ≠ z.suit.color)
    (hdf : d ∈ B.found d.suit) :
    x = d.twin ∧ y = Sum.inr z.twin := by
  have hxt : x = d.twin :=
    slide_off_seat_card_twin hBwf hface hslide hdz hdc hdf
  refine ⟨hxt, ?_⟩
  cases y with
  | inl a' =>
      exact absurd ⟨a', rfl⟩
        (slide_off_seat_base_not_inl hBwf hface hslide hdz hdc hdf)
  | inr w =>
      have hwz : w ≠ z := by
        intro hwz
        subst w
        have hcp : B.canPlace x (Sum.inr z) = true := by
          simpa using OffWindow.slide_canPlace hslide
        obtain ⟨k, hk, -⟩ := canPlace_inr hcp
        have htopk : (B.piles k).top = some z := (pileOfTop_eq_some_iff hBwf).1 hk
        have hzmem : z ∈ (B.piles a).faceUp := by rw [hface]; simp
        have hka : k = a := by
          by_cases hka : k = a
          · exact hka
          · exfalso
            exact ((mem_faceUp_only hBwf hzmem).1 k hka).2 (Pile.mem_of_top htopk)
        have htopa : (B.piles a).top = some z := by rwa [hka] at htopk
        have hnd : (front ++ z :: x :: rest).Nodup := by
          simpa [hface] using runOK_nodup (hBwf.runOK_of a)
        have hnd2 : (z :: x :: rest).Nodup := (List.nodup_append.mp hnd).2.1
        have hznot : z ∉ x :: rest := (List.nodup_cons.mp hnd2).1
        have hlast : lastOf (B.piles a).faceUp = some z := htopa
        rw [hface] at hlast
        have hstep : lastOf (front ++ z :: x :: rest) = lastOf (z :: x :: rest) :=
          CommuteStep.lastOf_append_of_ne_nil (by simp)
        rw [hstep] at hlast
        have : lastOf (x :: rest) = some z := hlast
        exact hznot (lastOf_mem this)
      exact congrArg Sum.inr
        (slide_off_seat_base_twin hBwf hface hslide hdz hdc hdf rfl hwz)

/-! ## §2. The exposing letter's run shape

A slide that turns `z` from *covered* (`pileOfTop z = none`) into *exposed*
(`pileOfTop z = some k`) must be moving the run that sits directly on `z`.
The slide's own data (`CommuteStep.slide_data`) pins the source and target
piles; the exposure is then pure pile arithmetic. -/

/-- **EXPOSURE EXTRACTS THE COVER.**  A reversible slide at a `WF` state that
uncovers `z` moves a run whose bottom card sits directly above `z`. -/
theorem exposure_shape
    {st s' : State} {x z : Card} {y : Base} {k : Anchor}
    (hwf : st.WF) (hrev : reversibleAtW st (Move.tabToTab x y))
    (hstep : State.step st (Move.tabToTab x y) = some s')
    (hnone : st.pileOfTop z = none)
    (hexp : s'.pileOfTop z = some k) :
    ∃ (a : Anchor) (front rest : List Card),
      st.pileHolding x = some a ∧ (st.piles a).faceUp = front ++ z :: x :: rest := by
  obtain ⟨a, kk, hhold, hcp, hkk, hka, -, hrunv, hcell⟩ :=
    CommuteStep.slide_data hwf hrev
  have hs' : s' = CommuteStep.slideSt st x y a := by
    obtain ⟨a', hh, -, -, hs⟩ := CommuteStep.step_tabToTab_slideSt hstep
    have haa : a' = a := by
      rw [hhold] at hh
      exact Option.some.inj hh.symm
    rw [hs, haa]
  -- `k` must be the source pile
  have hk : k = a := by
    by_cases h1 : k = a
    · exact h1
    · exfalso
      have htop : (s'.piles k).top = some z :=
        (pileOfTop_eq_some_iff (step_wf hwf hstep)).1 hexp
      by_cases h2 : k = kk
      · -- the target: `z` would then be the source's own old top
        rw [hs', h2, CommuteStep.slideSt_piles_target hwf hcp hkk hka hcell] at htop
        have hlastrun :
            lastOf ((st.piles kk).faceUp ++ fromCard x (st.piles a).faceUp) = some z := htop
        have hrunlast : lastOf (fromCard x (st.piles a).faceUp) = some z := by
          rw [CommuteStep.lastOf_append_of_ne_nil hrunv] at hlastrun
          exact hlastrun
        have hfalast : lastOf (st.piles a).faceUp = some z := by
          rw [← CommuteStep.below_fromCard_split (c := x) (st.piles a).faceUp,
            CommuteStep.lastOf_append_of_ne_nil hrunv]
          exact hrunlast
        exact (CrossSuitF1.pileOfTop_ne_none_of_topOf hfalast) hnone
      · -- a third pile: unchanged
        rw [hs', CommuteStep.slideSt_piles_other hwf hcp hkk hka hcell h1 h2] at htop
        exact (CrossSuitF1.pileOfTop_ne_none_of_topOf htop) hnone
  subst k
  -- the source pile's new top is `z`: it reads `front ++ [z]`
  have htop : (s'.piles a).top = some z :=
    (pileOfTop_eq_some_iff (step_wf hwf hstep)).1 hexp
  rw [hs', CommuteStep.slideSt_piles_source hwf hcp hkk hka hcell] at htop
  have hbelow : lastOf (below x (st.piles a).faceUp) = some z := htop
  obtain ⟨front, hfront⟩ := lastOf_eq_snoc hbelow
  have hxmem : x ∈ (st.piles a).faceUp := pileHolding_mem hhold
  obtain ⟨rest, hrest⟩ := fromCard_eq_head_of_mem hxmem
  refine ⟨a, front, rest, hhold, ?_⟩
  rw [← CommuteStep.below_fromCard_split (c := x) (st.piles a).faceUp, hfront, hrest]
  simp

/-! ## §3. Every exposing letter is the twin swap (the `∀` form of the window) -/

/-- **THE EXPOSING LETTER IS THE TWIN SWAP.**  At a `WF` state, a reversible
letter that uncovers `z` is a slide of `d.twin` and lands on `z.twin` — and `d`
is any card that (i) fits under `z` and (ii) lives on the foundation.  There is
**no** hypothesis placing the pull next to the slide. -/
theorem exposure_letter_is_twin_swap
    {st s' : State} {x z d : Card} {y : Base} {k : Anchor}
    (hwf : st.WF) (hrev : reversibleAtW st (Move.tabToTab x y))
    (hstep : State.step st (Move.tabToTab x y) = some s')
    (hnone : st.pileOfTop z = none) (hexp : s'.pileOfTop z = some k)
    (hdz : d.rank.toIdx + 1 = z.rank.toIdx) (hdc : d.suit.color ≠ z.suit.color)
    (hdf : d ∈ st.found d.suit) :
    x = d.twin ∧ y = Sum.inr z.twin := by
  obtain ⟨a, front, rest, hhold, hface⟩ := exposure_shape hwf hrev hstep hnone hexp
  exact slide_off_seat_twin_swap hwf hface hstep hdz hdc hdf

/-! ## §4. The exact letter dichotomy

Every free letter is a draw or a slide.  Draws leave the piles alone, and a
slide changes `pileOfTop z` in exactly three ways: it **exposes** `z` (source
pile), **relocates** it (target pile → source pile: `z` was the source's top and
rides the run), or **buries** it (`z` was the target's top).  Anything else is
unchanged.  On a window that starts covered and ends exposed, only the first
two can be the last change. -/

/-- **THE LETTER DICHOTOMY.**  A reversible slide at a `WF` state that changes
`pileOfTop z` does one of three things, and the exposure branch *extracts the
cover*: the moved run reads `front ++ z :: x :: rest`. -/
theorem slide_change_dichotomy
    {st s' : State} {x z : Card} {y : Base}
    (hwf : st.WF) (hrev : reversibleAtW st (Move.tabToTab x y))
    (hstep : State.step st (Move.tabToTab x y) = some s')
    (hch : s'.pileOfTop z ≠ st.pileOfTop z) :
    (st.pileOfTop z = none ∧
        ∃ (a : Anchor) (front rest : List Card) (k : Anchor),
          s'.pileOfTop z = some k ∧ st.pileHolding x = some a ∧
          (st.piles a).faceUp = front ++ z :: x :: rest)
    ∨ (∃ a k : Anchor, st.pileOfTop z = some a ∧ s'.pileOfTop z = some k)
    ∨ (∃ k : Anchor, st.pileOfTop z = some k ∧ s'.pileOfTop z = none) := by
  obtain ⟨a0, kt, hhold, hcp, hkt, hka, -, hrunv, hcell⟩ :=
    CommuteStep.slide_data hwf hrev
  have hs' : s' = CommuteStep.slideSt st x y a0 := by
    obtain ⟨a', hh, -, -, hs⟩ := CommuteStep.step_tabToTab_slideSt hstep
    have haa : a' = a0 := by
      rw [hhold] at hh
      exact Option.some.inj hh.symm
    rw [hs, haa]
  by_cases hnone : st.pileOfTop z = none
  · have hne : s'.pileOfTop z ≠ none := by rw [hnone] at hch; exact hch
    obtain ⟨k, hk⟩ := option_some_of_ne_none hne
    obtain ⟨a, front, rest, hhold', hface⟩ := exposure_shape hwf hrev hstep hnone hk
    exact Or.inl ⟨hnone, a, front, rest, k, hk, hhold', hface⟩
  · obtain ⟨m, hm⟩ := option_some_of_ne_none hnone
    by_cases h1 : m = a0
    · have htopa0 : st.pileOfTop z = some a0 := by rw [hm, h1]
      have hsrc : s'.pileOfTop z = some kt := by
        rw [hs']
        exact CommuteStep.slideSt_pileOfTop_source hwf hcp hkt hka hrunv hcell htopa0
      exact Or.inr (Or.inl ⟨a0, kt, htopa0, hsrc⟩)
    · by_cases h2 : m = kt
      · have htopkt : st.pileOfTop z = some kt := by rw [hm, h2]
        have htgt : s'.pileOfTop z = none := by
          rw [hs']
          exact CommuteStep.slideSt_pileOfTop_target hwf hcp hkt hka hrunv hcell htopkt
        exact Or.inr (Or.inr ⟨kt, htopkt, htgt⟩)
      · exfalso
        have hthird : s'.pileOfTop z = some m := by
          rw [hs']
          exact CommuteStep.slideSt_pileOfTop_third hwf hcp hkt hka hrunv hcell hm h1 h2
        rw [hthird] at hch
        exact hch hm.symm

/-- **A DRAW DOES NOT TOUCH THE SEAT.** -/
theorem draw_pileOfTop {st s' : State} {z : Card}
    (hstep : State.step st Move.draw = some s') :
    s'.pileOfTop z = st.pileOfTop z :=
  CommuteStep.pileOfTop_congr_piles (stepDraw_piles hstep) z

/-- **THE WINDOW'S CHANGE DICHOTOMY, AT EVERY FREE LETTER.**  Every letter of a
free window either leaves `pileOfTop z` alone or is one of the three shapes of
`slide_change_dichotomy` (at a free letter: a slide).  This is the exact `∀`
over the window's letters.  With the window starting *covered* and ending
*exposed*, the burial clause is never the last change (the value after the last
change is the final value), so the last touching letter is an **exposure** or a
**relocation** of the already-exposed `z`. -/
theorem free_letter_change
    {S T : State} {z : Card} {m : Move}
    (hSwf : S.WF) (hm : ValleyElim.FreeMove m)
    (hrev : reversibleAtW S m) (hstep : State.step S m = some T)
    (hch : T.pileOfTop z ≠ S.pileOfTop z) :
    (S.pileOfTop z = none ∧
        ∃ (a : Anchor) (front rest : List Card) (k : Anchor) (x : Card) (y : Base),
          T.pileOfTop z = some k ∧ m = Move.tabToTab x y ∧
          (S.piles a).faceUp = front ++ z :: x :: rest)
    ∨ (∃ a k : Anchor, S.pileOfTop z = some a ∧ T.pileOfTop z = some k)
    ∨ (∃ k : Anchor, S.pileOfTop z = some k ∧ T.pileOfTop z = none) := by
  rcases hm with rfl | ⟨x, y, rfl⟩
  · exfalso
    exact hch (draw_pileOfTop hstep)
  · rcases slide_change_dichotomy hSwf hrev hstep hch with
      ⟨h, a, front, rest, k, hk, hhold, hface⟩ | h | h
    · exact Or.inl ⟨h, a, front, rest, k, x, y, hk, rfl, hface⟩
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)

/-! ## §5. The window always contains an exposure letter -/

/-- **EXISTENCE OF THE EXPOSING LETTER.**  A free window that starts with `z`
covered and ends with `z` exposed splits as `γ₁ ++ q :: γ₂` at the **first**
letter `q` that exposes `z`; `q` is a slide of the run sitting directly on `z`. -/
theorem exists_exposure :
    ∀ (γ : List Move) {B P : State} {z : Card},
      ShufflePlayW B γ P → Canon.FreeOnly γ → B.WF →
      B.pileOfTop z = none → P.pileOfTop z ≠ none →
      ∃ (γ₁ γ₂ : List Move) (q : Move) (Q R : State) (k : Anchor) (a : Anchor)
        (front rest : List Card) (x : Card) (y : Base),
        γ = γ₁ ++ q :: γ₂ ∧ ShufflePlayW B γ₁ Q ∧ State.step Q q = some R ∧
        ShufflePlayW R γ₂ P ∧ Q.pileOfTop z = none ∧ R.pileOfTop z = some k ∧
        q = Move.tabToTab x y ∧ reversibleAtW Q q ∧
        (Q.piles a).faceUp = front ++ z :: x :: rest := by
  intro γ
  induction γ with
  | nil =>
      intro B P z hplay hfree hwf hnone hsome
      cases hplay
      exact absurd hnone hsome
  | cons m t ih =>
      intro B P z hplay hfree hwf hnone hsome
      obtain ⟨S1, hrev, hstep, hrest⟩ := Bubble.walk_cons_inv hplay
      have hwf1 : S1.WF := step_wf hwf hstep
      have hfree' : Canon.FreeOnly t := fun q hq => hfree q (List.mem_cons_of_mem m hq)
      by_cases hcase : S1.pileOfTop z = none
      · obtain ⟨γ₁, γ₂, q, Q, R, k, a, front, rest, x, y,
          heq, hp, hs, hr, hQ, hR, hq, hrevQ, hface⟩ :=
          ih hrest hfree' hwf1 hcase hsome
        refine ⟨m :: γ₁, γ₂, q, Q, R, k, a, front, rest, x, y,
          ?_, ?_, hs, hr, hQ, hR, hq, hrevQ, hface⟩
        · rw [heq]; rfl
        · exact Walk.cons hrev hstep hp
      · -- the first letter is the exposure
        have hexp : S1.pileOfTop z ≠ none := hcase
        rcases hfree m (List.mem_cons_self ..) with rfl | ⟨x, y, rfl⟩
        · exfalso
          exact hexp ((draw_pileOfTop hstep).trans hnone)
        · obtain ⟨k, hk⟩ := option_some_of_ne_none hexp
          obtain ⟨a, front, rest, hhold, hface⟩ := exposure_shape hwf hrev hstep hnone hk
          exact ⟨[], t, Move.tabToTab x y, B, S1, k, a, front, rest, x, y,
            rfl, Walk.nil B, hstep, hrest, hnone, hk, rfl, hrev, hface⟩

/-! ## §6. The corridor: the prepared seat's window carries the twin swap

This is the multi-slide form of `OffWindow.corridor_single_slide_twin`.  The
window `γ` is arbitrary (`Canon.FreeOnly`, any length); the pull is at the
*window's end*, not next to the slide.  The output names the exposing letter
**inside** `γ` as `tabToTab d.twin (inr z.twin)`, with the run shape at its
origin and the seat-readiness flip `canPlace = false → true`. -/

/-- **THE MULTI-SLIDE TWIN SWAP ON THE CORRIDOR.**  In the prepared-seat face
(`¬ Pullable B d (inr z)`, pull fires at the window's end), the free window
contains a letter that is **exactly** the twin exchange
`d.twin : z → z.twin`, and that letter is the one that makes the seat accept
`d`.  No single-slide hypothesis anywhere. -/
theorem corridor_prepared_seat_twin_swap
    {u v : State} {ρ pre γ tail : List Move} {c d : Card} {A B P₀ Pv : State} {z : Card}
    (huwf : u.WF) (hplay : ShufflePlayW u ρ v)
    (heq : ρ = pre ++ (Move.tabToFound c :: (γ ++ (Move.foundToTab d (Sum.inr z) :: tail))))
    (hfree : Canon.FreeOnly γ)
    (hpre : ShufflePlayW u pre A) (hstepR : State.step A (Move.tabToFound c) = some B)
    (hγ : ShufflePlayW B γ P₀)
    (hpull : State.step P₀ (Move.foundToTab d (Sum.inr z)) = some Pv)
    (hnp : ¬ PullKit.Pullable B d (Sum.inr z)) :
    ∃ (γ₁ γ₂ : List Move) (Q R : State) (a : Anchor) (front rest : List Card),
      γ = γ₁ ++ Move.tabToTab d.twin (Sum.inr z.twin) :: γ₂ ∧
      ShufflePlayW B γ₁ Q ∧
      State.step Q (Move.tabToTab d.twin (Sum.inr z.twin)) = some R ∧
      ShufflePlayW R γ₂ P₀ ∧
      (Q.piles a).faceUp = front ++ z :: d.twin :: rest ∧
      Q.canPlace d (Sum.inr z) = false ∧
      R.canPlace d (Sum.inr z) = true ∧
      Q.canPlace d.twin (Sum.inr z.twin) = true ∧
      ¬ PullKit.Pullable Q d (Sum.inr z) ∧
      PullKit.Pullable R d (Sum.inr z) := by
  have hAwf : A.WF := SatDifferCensus.ShufflePlayW.wf_end hpre huwf
  have hBwf : B.WF := step_wf hAwf hstepR
  have hpullP : PullKit.Pullable P₀ d (Sum.inr z) := CrossSuitPart.pullable_of_step hpull
  have hnone : B.pileOfTop z = none :=
    OffWindow.pileOfTop_none_of_window_not_pullable hγ hfree hnp hpullP
  obtain ⟨kd, hkd, hsit⟩ := canPlace_inr hpullP.2
  have hsome : P₀.pileOfTop z ≠ none := by rw [hkd]; simp
  obtain ⟨hdz, hdc⟩ := (canSitOn_eq d z).mp hsit
  obtain ⟨c', htop0, hc', -, -⟩ := step_foundToTab_inv hpull
  have hdfP : d ∈ P₀.found d.suit := by
    rw [hc'] at htop0
    exact lastOf_mem htop0
  have hfoundEq : P₀.found d.suit = B.found d.suit :=
    CrossSuit.found_eq_of_avoids hγ
      (fun m hm => CrossSuitF1.avoidsSuit_of_free (hfree m hm))
  have hdfB : d ∈ B.found d.suit := by rw [← hfoundEq]; exact hdfP
  obtain ⟨γ₁, γ₂, q, Q, R, k, a, front, rest, x, y,
    heqγ, hQplay, hstepQ, hRplay, hQnone, hRsome, hq, hrevQ, hface⟩ :=
    exists_exposure γ hγ hfree hBwf hnone hsome
  have hQwf : Q.WF := SatDifferCensus.ShufflePlayW.wf_end hQplay hBwf
  have hfree₁ : Canon.FreeOnly γ₁ := by
    intro q' hq'
    exact hfree q' (by rw [heqγ]; exact List.mem_append_left _ hq')
  have hfoundQ : Q.found d.suit = B.found d.suit :=
    CrossSuit.found_eq_of_avoids hQplay
      (fun m hm => CrossSuitF1.avoidsSuit_of_free (hfree₁ m hm))
  have hdfQ : d ∈ Q.found d.suit := by rw [hfoundQ]; exact hdfB
  have hx := exposure_letter_is_twin_swap (x := x) (y := y) (k := k) hQwf
    (by rw [← hq]; exact hrevQ) (by rw [← hq]; exact hstepQ) hQnone hRsome hdz hdc hdfQ
  obtain ⟨hx1, hx2⟩ := hx
  have hstep' : State.step Q (Move.tabToTab d.twin (Sum.inr z.twin)) = some R := by
    rw [← hx1, ← hx2, ← hq]
    exact hstepQ
  have hcpQ : Q.canPlace d (Sum.inr z) = false := by
    rw [canPlace_inr_eq, hQnone]
  have hcpR : R.canPlace d (Sum.inr z) = true := by
    rw [canPlace_inr_located hRsome, hsit]
  have hcpQ' : Q.canPlace d.twin (Sum.inr z.twin) = true :=
    OffWindow.slide_canPlace hstep'
  have hfree₂ : Canon.FreeOnly γ₂ := by
    intro q' hq'
    exact hfree q' (by
      rw [heqγ]
      exact List.mem_append_right _ (List.mem_cons_of_mem q hq'))
  -- the foundation top of `d.suit` is `d` at the pull's origin and is preserved
  have hftR : R.foundTop d.suit = some d := by
    have h1 : R.foundTop d.suit = P₀.foundTop d.suit :=
      CrossSuitPart.foundTop_free_window d.suit hRplay hfree₂
    rw [h1, htop0, hc']
  refine ⟨γ₁, γ₂, Q, R, a, front, rest, ?_, hQplay, hstep', hRplay, ?_, hcpQ, hcpR,
    hcpQ', ?_, ?_⟩
  · rw [heqγ, hq, hx1, hx2]
  · rw [hface, hx1]
  · intro h
    have h2 := h.2
    rw [hcpQ] at h2
    exact absurd h2 (by simp)
  · exact ⟨hftR, hcpR⟩

/-! ## §7. The honest remainder

What §6 does **not** say (and §8 does, in the `TopConst` form): that the twin swap
is the *last* letter of the window.  After the exposure, `z` is a pile top, and a
later free slide may

* **relocate** `z` (move the run ending at `z` onto another pile top) —
  `pileOfTop z` changes from `some a` to `some k`, or
* **bury** `z` again (slide a card onto `z`), which forces yet another exposure
  later because the window ends exposed.

So the exact residual over the window is the **trichotomy** of
`free_letter_change`, with the exposure branch *closed* by §3, and the
observation that no burial can be the last change (`burial_has_later_exposure`).
The relocation branch is a genuine, legal alternative: it is the twin calculus'
blind spot. -/

/-- **A BURIAL IS NEVER THE LAST CHANGE.**  If a letter of the window leaves `z`
covered while the window ends exposed, some *later* letter exposes `z` — and by
§3 that later letter is again the twin swap.  So a seat change after an
exposure is either a relocation or is itself a new exposure. -/
theorem burial_has_later_exposure
    {B P S T : State} {γ γ₁ γ₂ : List Move} {z : Card} {m : Move}
    (hBwf : B.WF) (hfree : Canon.FreeOnly γ)
    (heq : γ = γ₁ ++ m :: γ₂)
    (hplay₁ : ShufflePlayW B γ₁ S) (hstep : State.step S m = some T)
    (hplay₂ : ShufflePlayW T γ₂ P)
    (hbury : T.pileOfTop z = none) (hP : P.pileOfTop z ≠ none) :
    ∃ (γ₃ γ₄ : List Move) (q : Move) (Q R : State) (k : Anchor) (a : Anchor)
      (front rest : List Card) (x : Card) (y : Base),
      γ₂ = γ₃ ++ q :: γ₄ ∧ ShufflePlayW T γ₃ Q ∧ State.step Q q = some R ∧
      ShufflePlayW R γ₄ P ∧ Q.pileOfTop z = none ∧ R.pileOfTop z = some k ∧
      q = Move.tabToTab x y ∧ reversibleAtW Q q ∧
      (Q.piles a).faceUp = front ++ z :: x :: rest := by
  have hSwf : S.WF := SatDifferCensus.ShufflePlayW.wf_end hplay₁ hBwf
  have hTwf : T.WF := step_wf hSwf hstep
  have hfree₂ : Canon.FreeOnly γ₂ := by
    intro q' hq'
    have hmem : q' ∈ γ₁ ++ m :: γ₂ :=
      List.mem_append_right _ (List.mem_cons_of_mem m hq')
    exact hfree q' (by rw [heq]; exact hmem)
  exact exists_exposure γ₂ hplay₂ hfree₂ hTwf hbury hP

/-- **THE COVER OF THE PREPARED SEAT IS ALWAYS `d.twin`.**  The mirror of
`exposure_letter_is_twin_swap`: a reversible letter that *buries* the exposed
seat `z` slides the stack whose bottom card is `d.twin` back onto `z`.  So the
whole window's seat traffic is the twin card toggling on and off `z`. -/
theorem burial_letter_cover
    {S T : State} {x z d : Card} {y : Base} {k : Anchor}
    (hSwf : S.WF) (hrev : reversibleAtW S (Move.tabToTab x y))
    (hstep : State.step S (Move.tabToTab x y) = some T)
    (hexp : S.pileOfTop z = some k) (hbury : T.pileOfTop z = none)
    (hdz : d.rank.toIdx + 1 = z.rank.toIdx) (hdc : d.suit.color ≠ z.suit.color)
    (hdf : d ∈ S.found d.suit) :
    x = d.twin ∧ y = Sum.inr z := by
  obtain ⟨a0, kt, hhold, hcp, hkt, hka, -, hrunv, hcell⟩ :=
    CommuteStep.slide_data hSwf hrev
  have hs' : T = CommuteStep.slideSt S x y a0 := by
    obtain ⟨a', hh, -, -, hs⟩ := CommuteStep.step_tabToTab_slideSt hstep
    have haa : a' = a0 := by
      rw [hhold] at hh
      exact Option.some.inj hh.symm
    rw [hs, haa]
  -- `z` tops the *target* pile at `S`
  have hk : k = kt := by
    by_cases h1 : k = a0
    · exfalso
      have htopa0 : S.pileOfTop z = some a0 := by rw [hexp, h1]
      have hsrc : T.pileOfTop z = some kt := by
        rw [hs']
        exact CommuteStep.slideSt_pileOfTop_source hSwf hcp hkt hka hrunv hcell htopa0
      rw [hsrc] at hbury
      exact absurd hbury (by simp)
    · by_cases h2 : k = kt
      · exact h2
      · exfalso
        have hthird : T.pileOfTop z = some k := by
          rw [hs']
          exact CommuteStep.slideSt_pileOfTop_third hSwf hcp hkt hka hrunv hcell hexp h1 h2
        rw [hthird] at hbury
        exact absurd hbury (by simp)
  -- the base is the card `z` itself
  have hy : y = Sum.inr z := by
    cases y with
    | inl a' =>
        exfalso
        have hka' : kt = a' := (Option.some.inj hkt).symm
        have hemp : (S.piles a').isEmpty = true := (canPlace_inl hcp).1
        have htop : (S.piles kt).top = some z :=
          (pileOfTop_eq_some_iff hSwf).1 (by rw [hexp, hk])
        have hzmem' : z ∈ (S.piles kt).faceUp := Pile.mem_of_top htop
        have hzmem : z ∈ (S.piles a').faceUp := by rw [← hka']; exact hzmem'
        have hfalse := Pile.isEmpty_eq_false_of_mem hzmem
        rw [hfalse] at hemp
        exact absurd hemp (by simp)
    | inr w =>
        have hkw : S.pileOfTop w = some kt := hkt
        have htopz : (S.piles kt).top = some z :=
          (pileOfTop_eq_some_iff hSwf).1 (by rw [hexp, hk])
        have htopw : (S.piles kt).top = some w :=
          (pileOfTop_eq_some_iff hSwf).1 hkw
        have hzw : z = w := Option.some.inj (htopz.symm.trans htopw)
        rw [hzw]
  -- the mover fits on `z` and is not the founded card `d`
  have hcpz : S.canPlace x (Sum.inr z) = true := by rw [← hy]; exact hcp
  obtain ⟨-, -, hsit⟩ := canPlace_inr hcpz
  obtain ⟨hxzr, hxzc⟩ := (canSitOn_eq x z).mp hsit
  have hxmem : x ∈ (S.piles a0).faceUp := pileHolding_mem hhold
  have hxzone : x ∈ pileZone S a0 := List.mem_append_right _ hxmem
  have hne : x ≠ d := fun hxd => wf_pile_found_ne hSwf (hxd ▸ hxzone) hdf
  exact ⟨OffWindow.twin_of_two_fits hxzr hxzc hdz hdc hne, hy⟩

/-- **THE SEAT-CHANGE LETTER.**  Every free letter that changes the seat `z` is
one of exactly three things: the twin swap `d.twin : z → z.twin` (exposure), the
twin cover `d.twin : · → z` (burial, the mirror of the swap), or a **relocation**
of the already-exposed `z` onto another pile top.  The first two are kernel
identities; the third is the extraction residual. -/
theorem seat_change_letter
    {S T : State} {x z d : Card} {y : Base}
    (hSwf : S.WF) (hrev : reversibleAtW S (Move.tabToTab x y))
    (hstep : State.step S (Move.tabToTab x y) = some T)
    (hdz : d.rank.toIdx + 1 = z.rank.toIdx) (hdc : d.suit.color ≠ z.suit.color)
    (hdf : d ∈ S.found d.suit)
    (hch : T.pileOfTop z ≠ S.pileOfTop z) :
    (∃ k : Anchor, S.pileOfTop z = none ∧ T.pileOfTop z = some k ∧
        x = d.twin ∧ y = Sum.inr z.twin)
    ∨ (S.pileOfTop z ≠ none ∧ T.pileOfTop z = none ∧ x = d.twin ∧ y = Sum.inr z)
    ∨ (∃ a k : Anchor, S.pileOfTop z = some a ∧ T.pileOfTop z = some k) := by
  rcases slide_change_dichotomy hSwf hrev hstep hch with
    ⟨hS, a, front, rest, k, hT, hhold, hface⟩ | ⟨a, k, hSa, hTk⟩ | ⟨k, hSk, hT⟩
  · refine Or.inl ⟨k, hS, hT, ?_, ?_⟩
    · exact slide_off_seat_card_twin hSwf hface hstep hdz hdc hdf
    · exact (slide_off_seat_twin_swap hSwf hface hstep hdz hdc hdf).2
  · exact Or.inr (Or.inr ⟨a, k, hSa, hTk⟩)
  · obtain ⟨hx, hy⟩ := burial_letter_cover hSwf hrev hstep hSk hT hdz hdc hdf
    exact Or.inr (Or.inl ⟨by rw [hSk]; simp, hT, hx, hy⟩)

/-! ## §8. The literal split at the LAST touching letter

The class of free letters that keep `pileOfTop z` constant is closed under
appending a letter, so the "constant suffix" of the window is itself an
inductive object.  This makes the last-change split (task item 1) kernel-cheap:
peel the last letter; if it preserves the seat, recurse; otherwise it *is* the
last change and the suffix is empty. -/

/-- A play that keeps `pileOfTop z` constant at every letter. -/
inductive TopConst (z : Card) : State → List Move → State → Prop where
  | nil (st : State) : TopConst z st [] st
  | cons {st s1 W : State} {m : Move} {ρ : List Move}
      (hstep : State.step st m = some s1)
      (hkeep : s1.pileOfTop z = st.pileOfTop z)
      (hrest : TopConst z s1 ρ W) : TopConst z st (m :: ρ) W

/-- A constant play ends where it started. -/
theorem TopConst.value_eq {st W : State} {ρ : List Move} {z : Card}
    (h : TopConst z st ρ W) : W.pileOfTop z = st.pileOfTop z := by
  induction h with
  | nil st => rfl
  | cons hstep hkeep hrest ih => rw [ih, hkeep]

/-- A constant play stays constant when one preserving letter is appended. -/
theorem TopConst.append {st W : State} {ρ : List Move} {z : Card} {m : Move} {W' : State}
    (h : TopConst z st ρ W) (hstep : State.step W m = some W')
    (hkeep : W'.pileOfTop z = W.pileOfTop z) : TopConst z st (ρ ++ [m]) W' := by
  induction h with
  | nil st => exact TopConst.cons hstep hkeep (TopConst.nil W')
  | cons hstep0 hkeep0 hrest ih =>
      exact TopConst.cons hstep0 hkeep0 (ih hstep hkeep)

/-- **THE LAST-CHANGE SPLIT, BY STRONG RECURSION ON THE LENGTH.** -/
theorem last_change_aux (n : Nat) :
    ∀ (B P : State) (γ : List Move) {z : Card},
      γ.length = n → B.WF → ShufflePlayW B γ P → Canon.FreeOnly γ →
      B.pileOfTop z ≠ P.pileOfTop z →
      ∃ (γ₁ γ₂ : List Move) (q : Move) (Q R : State),
        γ = γ₁ ++ q :: γ₂ ∧ ShufflePlayW B γ₁ Q ∧ State.step Q q = some R ∧
        ShufflePlayW R γ₂ P ∧ reversibleAtW Q q ∧
        Q.pileOfTop z ≠ R.pileOfTop z ∧ TopConst z R γ₂ P := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
      intro B P γ z hlen hBwf hγ hfree hch
      rcases List.eq_nil_or_concat γ with hnil | ⟨γ', m, hcat⟩
      · subst hnil
        cases hγ
        exact absurd rfl hch
      · rw [List.concat_eq_append] at hcat
        have hγ' : ShufflePlayW B (γ' ++ [m]) P := hcat ▸ hγ
        have hfree' : Canon.FreeOnly (γ' ++ [m]) := hcat ▸ hfree
        obtain ⟨S, hplay0, hplay1⟩ := ValleyElim.ShufflePlayW_split hγ' γ' [m] rfl
        obtain ⟨T, hrevm, hstepm, hrest⟩ := Bubble.walk_cons_inv hplay1
        cases hrest
        by_cases hpres : S.pileOfTop z = P.pileOfTop z
        · have hch0 : B.pileOfTop z ≠ S.pileOfTop z := fun h => hch (h.trans hpres)
          have hlen' : γ'.length < n := by
            have h2 : (γ' ++ [m]).length = n := by rw [← hcat]; exact hlen
            rw [List.length_append, List.length_singleton] at h2
            omega
          have hfree0 : Canon.FreeOnly γ' :=
            fun x hx => hfree' x (List.mem_append_left _ hx)
          obtain ⟨γ₁, γ₂, q, Q, R, heq, hQplay, hstepQ, hRplay, hrevQ, hQR, htconst⟩ :=
            ih γ'.length hlen' B S γ' rfl hBwf hplay0 hfree0 hch0
          refine ⟨γ₁, γ₂ ++ [m], q, Q, R, ?_, hQplay, hstepQ, ?_, hrevQ, hQR, ?_⟩
          · rw [hcat, heq]
            simp only [List.cons_append, List.append_assoc]
          · exact ShufflePlayW_append hRplay (Walk.cons hrevm hstepm (Walk.nil P))
          · exact TopConst.append htconst hstepm hpres.symm
        · refine ⟨γ', [], m, S, P, ?_, hplay0, hstepm, Walk.nil P, hrevm, hpres,
            TopConst.nil P⟩
          exact hcat

/-- **THE SPLIT AT THE LAST TOUCHING LETTER.**  A free window that changes
`pileOfTop z` factors as `γ₁ ++ q :: γ₂` where `q` changes the seat and **every
letter of `γ₂` leaves it unchanged** (`TopConst z R γ₂ P`). -/
theorem last_seat_change
    {B P : State} {γ : List Move} {z : Card}
    (hBwf : B.WF) (hγ : ShufflePlayW B γ P) (hfree : Canon.FreeOnly γ)
    (hch : B.pileOfTop z ≠ P.pileOfTop z) :
    ∃ (γ₁ γ₂ : List Move) (q : Move) (Q R : State),
      γ = γ₁ ++ q :: γ₂ ∧ ShufflePlayW B γ₁ Q ∧ State.step Q q = some R ∧
      ShufflePlayW R γ₂ P ∧ reversibleAtW Q q ∧
      Q.pileOfTop z ≠ R.pileOfTop z ∧ TopConst z R γ₂ P :=
  last_change_aux γ.length B P γ rfl hBwf hγ hfree hch

/-- **THE PREPARED SEAT'S LAST CHANGE IS THE TWIN SWAP OR A RELOCATION.**  With
the window's endpoints covered/exposed, the last touching letter is never a
burial (the suffix would have to end covered), so it is either the twin swap
`d.twin : z → z.twin` — *with its run shape at the letter's origin* — or a
relocation of the already-exposed `z` onto another pile top. -/
theorem last_change_prepared_seat
    {B P : State} {γ : List Move} {z d : Card}
    (hBwf : B.WF) (hγ : ShufflePlayW B γ P) (hfree : Canon.FreeOnly γ)
    (hdz : d.rank.toIdx + 1 = z.rank.toIdx) (hdc : d.suit.color ≠ z.suit.color)
    (hdf : d ∈ B.found d.suit)
    (hnone : B.pileOfTop z = none) (hP : P.pileOfTop z ≠ none) :
    (∃ (γ₁ γ₂ : List Move) (Q R : State) (a : Anchor) (front rest : List Card),
        γ = γ₁ ++ Move.tabToTab d.twin (Sum.inr z.twin) :: γ₂ ∧
        ShufflePlayW B γ₁ Q ∧
        State.step Q (Move.tabToTab d.twin (Sum.inr z.twin)) = some R ∧
        ShufflePlayW R γ₂ P ∧
        (Q.piles a).faceUp = front ++ z :: d.twin :: rest ∧
        TopConst z R γ₂ P)
    ∨ (∃ (γ₁ γ₂ : List Move) (Q R : State) (a k : Anchor) (x : Card) (y : Base),
        γ = γ₁ ++ Move.tabToTab x y :: γ₂ ∧
        ShufflePlayW B γ₁ Q ∧
        State.step Q (Move.tabToTab x y) = some R ∧
        ShufflePlayW R γ₂ P ∧
        Q.pileOfTop z = some a ∧ R.pileOfTop z = some k ∧
        TopConst z R γ₂ P) := by
  have hch : B.pileOfTop z ≠ P.pileOfTop z := by
    intro h
    rw [h] at hnone
    exact hP hnone
  obtain ⟨γ₁, γ₂, q, Q, R, heq, hQplay, hstepQ, hRplay, hrevQ, hQR, htconst⟩ :=
    last_seat_change hBwf hγ hfree hch
  have hRval : R.pileOfTop z = P.pileOfTop z := htconst.value_eq.symm
  have hRsome : R.pileOfTop z ≠ none := by rw [hRval]; exact hP
  have hQwf : Q.WF := SatDifferCensus.ShufflePlayW.wf_end hQplay hBwf
  have hqmem : q ∈ γ := by rw [heq]; exact List.mem_append_right _ (List.mem_cons_self ..)
  have hqfree : ValleyElim.FreeMove q := hfree q hqmem
  -- the foundation of `d` is untouched across the prefix
  have hfree₁ : Canon.FreeOnly γ₁ := by
    intro q' hq'
    exact hfree q' (by rw [heq]; exact List.mem_append_left _ hq')
  have hfoundQ : Q.found d.suit = B.found d.suit :=
    CrossSuit.found_eq_of_avoids hQplay
      (fun m hm => CrossSuitF1.avoidsSuit_of_free (hfree₁ m hm))
  have hdfQ : d ∈ Q.found d.suit := by rw [hfoundQ]; exact hdf
  rcases hqfree with hdraw | ⟨x, y, rfl⟩
  · -- a draw cannot be a change
    exfalso
    have hkeep : R.pileOfTop z = Q.pileOfTop z := by
      rw [hdraw] at hstepQ
      exact draw_pileOfTop hstepQ
    exact hQR hkeep.symm
  · rcases slide_change_dichotomy hQwf hrevQ hstepQ (fun h => hQR h.symm) with
      h | h | h
    · obtain ⟨hQnone, a, front, rest, k, hRk, hhold, hface⟩ := h
      -- exposure: the twin swap
      have hx := exposure_letter_is_twin_swap (x := x) (y := y) (k := k) hQwf
        hrevQ hstepQ hQnone hRk hdz hdc hdfQ
      obtain ⟨hx1, hx2⟩ := hx
      refine Or.inl ⟨γ₁, γ₂, Q, R, a, front, rest, ?_, hQplay, ?_, hRplay, ?_, htconst⟩
      · rw [heq, hx1, hx2]
      · rw [← hstepQ, ← hx1, ← hx2]
      · rw [hface, hx1]
    · obtain ⟨a, k, hQa, hRk⟩ := h
      -- relocation: the named residual
      refine Or.inr ⟨γ₁, γ₂, Q, R, a, k, x, y, ?_, hQplay, hstepQ, hRplay, hQa, hRk, htconst⟩
      rw [heq]
    · obtain ⟨k, hQk, hRnone⟩ := h
      -- burial: impossible, the suffix ends exposed
      exact absurd hRsome (fun h => h hRnone)

/-! ## §9. The capstone: the corridor's last touching letter

Combining §8 with the corridor's seat data (`z` covered at the raise's image,
exposed at the pull's origin, `d` founded, `d`'s fit state-free). -/

/-- **THE CORRIDOR'S LAST TOUCHING LETTER.**  In the prepared-seat face the
window's last seat change is the kernel-identified twin swap
`d.twin : z → z.twin` — with its run shape at the letter's origin and a
seat-constant suffix — **or** a relocation of the already exposed `z`, which is
the exact extraction residual (a `∀` over the window, not a restatement of the
face). -/
theorem corridor_last_change_dichotomy
    {u v : State} {ρ pre γ tail : List Move} {c d : Card} {A B P₀ Pv : State} {z : Card}
    (huwf : u.WF) (hplay : ShufflePlayW u ρ v)
    (heq : ρ = pre ++ (Move.tabToFound c :: (γ ++ (Move.foundToTab d (Sum.inr z) :: tail))))
    (hfree : Canon.FreeOnly γ)
    (hpre : ShufflePlayW u pre A) (hstepR : State.step A (Move.tabToFound c) = some B)
    (hγ : ShufflePlayW B γ P₀)
    (hpull : State.step P₀ (Move.foundToTab d (Sum.inr z)) = some Pv)
    (hnp : ¬ PullKit.Pullable B d (Sum.inr z)) :
    (∃ (γ₁ γ₂ : List Move) (Q R : State) (a : Anchor) (front rest : List Card),
        γ = γ₁ ++ Move.tabToTab d.twin (Sum.inr z.twin) :: γ₂ ∧
        ShufflePlayW B γ₁ Q ∧
        State.step Q (Move.tabToTab d.twin (Sum.inr z.twin)) = some R ∧
        ShufflePlayW R γ₂ P₀ ∧
        (Q.piles a).faceUp = front ++ z :: d.twin :: rest ∧
        TopConst z R γ₂ P₀)
    ∨ (∃ (γ₁ γ₂ : List Move) (Q R : State) (a k : Anchor) (x : Card) (y : Base),
        γ = γ₁ ++ Move.tabToTab x y :: γ₂ ∧
        ShufflePlayW B γ₁ Q ∧
        State.step Q (Move.tabToTab x y) = some R ∧
        ShufflePlayW R γ₂ P₀ ∧
        Q.pileOfTop z = some a ∧ R.pileOfTop z = some k ∧
        TopConst z R γ₂ P₀) := by
  have hAwf : A.WF := SatDifferCensus.ShufflePlayW.wf_end hpre huwf
  have hBwf : B.WF := step_wf hAwf hstepR
  have hpullP : PullKit.Pullable P₀ d (Sum.inr z) := CrossSuitPart.pullable_of_step hpull
  have hnone : B.pileOfTop z = none :=
    OffWindow.pileOfTop_none_of_window_not_pullable hγ hfree hnp hpullP
  obtain ⟨kd, hkd, hsit⟩ := canPlace_inr hpullP.2
  have hsome : P₀.pileOfTop z ≠ none := by rw [hkd]; simp
  obtain ⟨hdz, hdc⟩ := (canSitOn_eq d z).mp hsit
  obtain ⟨c', htop0, hc', -, -⟩ := step_foundToTab_inv hpull
  have hdfP : d ∈ P₀.found d.suit := by
    rw [hc'] at htop0
    exact lastOf_mem htop0
  have hfoundEq : P₀.found d.suit = B.found d.suit :=
    CrossSuit.found_eq_of_avoids hγ
      (fun m hm => CrossSuitF1.avoidsSuit_of_free (hfree m hm))
  have hdfB : d ∈ B.found d.suit := by rw [← hfoundEq]; exact hdfP
  exact last_change_prepared_seat hBwf hγ hfree hdz hdc hdfB hnone hsome

end Extract

/-! ## §10. Axiom battery

Expected: every row `[]`, `[propext]` or `[propext, Quot.sound]`; no `sorryAx`,
no `Classical.choice`, no `Lean.ofReduceBool`. -/

#print axioms Extract.slide_off_seat_card_twin
#print axioms Extract.slide_off_seat_base_twin
#print axioms Extract.slide_off_seat_base_not_inl
#print axioms Extract.slide_off_seat_twin_swap
#print axioms Extract.exposure_shape
#print axioms Extract.exposure_letter_is_twin_swap
#print axioms Extract.slide_change_dichotomy
#print axioms Extract.draw_pileOfTop
#print axioms Extract.free_letter_change
#print axioms Extract.exists_exposure
#print axioms Extract.corridor_prepared_seat_twin_swap
#print axioms Extract.burial_has_later_exposure
#print axioms Extract.burial_letter_cover
#print axioms Extract.seat_change_letter
#print axioms Extract.TopConst.value_eq
#print axioms Extract.TopConst.append
#print axioms Extract.last_change_aux
#print axioms Extract.last_seat_change
#print axioms Extract.last_change_prepared_seat
#print axioms Extract.corridor_last_change_dichotomy

#check @Extract.TopConst
#check @Extract.last_seat_change
#check @Extract.corridor_last_change_dichotomy








