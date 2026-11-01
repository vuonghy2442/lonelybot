import Orig2.ForkBoth

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-!
# Temp/BP — the `pre ≠ []` lanes of the block decomposition

READ-ONLY scratch card.  No source file is modified; nothing is committed.
Zero `sorry`, zero `Classical.choice`, zero `native_decide`; the axiom
battery is at the tail.

## Headline

1. **THE COVER TRANSFERS BACK OVER THE FREE TAIL — AND THE PAIR IS
   ALWAYS THE SPLIT'S OWN TWIN PAIR.**

   `Both.bottomNotBothRaisableNil` proved the `pre = []` corner.  This card
   proves that the *whole* corner is pinned to ONE local fact at the
   **pre-split state** `A'` (the state just before the split's pull):

       both twins raisable at F  ⟹  `CanRaise A' c.twin`
                                   (`pull_origin_twin_raisable`)

   Concretely, with `TwinLivePair F x` the S-live card `c` (green,
   `splitHyp_green`) is one of the pair — **so `{x, x.twin} = {c, c.twin}`
   always, for every `pre`** — and then three steps:

   * `raisable_at_landing`: at the pull landing `B`, `c.twin` is *vanilla*
     raisable.  If it were covered, the cover card `e` fits `c.twin`, and
     `Both.seat_inv_play` (`e`'s seat only ever lies on `c`/`c.twin`) makes
     one of the twins covered at `F`.  This is the `pre = []` mechanism,
     now run on the *free tail only*, so it is `pre`-blind.
   * `canRaise_twin_prev_of_pull`: `c.twin`'s vanilla raisability transfers
     back across the pull of `c` — the pull edits `c`'s suit only and
     `c.twin` cannot be the pile top the pull writes.  (No saturation is
     used; this is the pull-edit arithmetic of `Both.top_case_false`.)

2. **BOTH `pre ≠ []` LANES REDUCE TO ONE RESIDUAL.**

   `PullOriginTwinBlocked` (`§5`): at the state just before a valley split's
   pull, the pulled card's twin is not vanilla-raisable.  It is a rank/seat
   statement at `A'`; it mentions neither the bottom, the raise card, nor
   raisability at `F`.  Both named lanes follow from it
   (`bottomNotBothPullPre_of_originBlock`, `bottomNotBothFreePre_of_originBlock`),
   and so does the `pre = []` lane
   (`bottomNotBothRaisableNil_of_originBlock`) — as a cross-check of the
   reduction, not as a replacement of `Both.bottomNotBothRaisableNil`.

3. **THE RESIDUAL IS PROVED ON FREE PREFIXES** — including `pre = []`.
   `not_canRaise_origin_of_freePre`: a free prefix transports the
   S-licence back to the saturated origin, where `CanRaise A' c.twin` would
   be a contradiction.  Hence the residual's only live content is the
   *pull-headed* prefix.

4. **ON A RAISE-FREE PREFIX THE RESIDUAL IS A CARD STATEMENT**
   (`§9`).  `exists_prePull_of_canRaise_origin`:
   `CanRaise A' c.twin` forces the prefix to pull `c` or `c.twin`; so
   `NoTwinPullInPre` ("the prefix pulls neither `c` nor `c.twin`") implies
   the residual there (`originBlock_of_noTwinPull`).  With the campaign's
   mechanism `d = c.twin`, that card statement is *literally*
   `PinRight.NoPrePullRaise` (`prePullPair_iff_twinPull`), so this lane of
   the block decomposition meets the tree's existing named frontier.

5. **Consumers**: `BottomNotBothRaisableNil` + residual give the global
   `Pin.BottomNotBothRaisable` (`bottomNotBoth_of_originBlock`) and the
   campaign chain (`satDifferForkWF_of_originBlock`).

Census (`Temp/BP_probe2.py`, 22 fresh random classes, **2700 splits** —
1320 pull-headed, 1212 free-headed, 168 `nil`): the residual's conclusion
`CanRaise A' c.twin` is **false at every split**; `both = 0` as before.  The
residual is therefore sharp (the `gAce` gadget violates it at a *non-split*,
`originTwinBlocked_not_local`) and never violated on the census.
-/

namespace BP

open SplitKit

/-! ## §1. The seat map across a pull -/

/-- `pileHolding` is a pointwise membership read. -/
theorem pileHolding_congr_mem {u v : State} {d : Card}
    (h : ∀ j, (d ∈ (u.piles j).faceUp ↔ d ∈ (v.piles j).faceUp)) :
    u.pileHolding d = v.pileHolding d := by
  show firstWhere (fun a => decide (d ∈ (u.piles a).faceUp)) Anchor.all =
    firstWhere (fun a => decide (d ∈ (v.piles a).faceUp)) Anchor.all
  refine firstWhere_congr_local (fun a => ?_) Anchor.all
  by_cases hh : d ∈ (u.piles a).faceUp
  · rw [decide_eq_true hh, decide_eq_true ((h a).mp hh)]
  · rw [decide_false_of_not hh, decide_false_of_not (fun hc => hh ((h a).mpr hc))]

/-- `seatOf` reads off the holding pile and that pile's `below`-list. -/
theorem seatOf_congr_hold {u v : State} {d : Card}
    (hhold : u.pileHolding d = v.pileHolding d)
    (hbelow : ∀ a, u.pileHolding d = some a →
      below d (u.piles a).faceUp = below d (v.piles a).faceUp) :
    seatOf u d = seatOf v d := by
  rw [tfc_seatOf_eq, tfc_seatOf_eq, hhold]
  cases hh : v.pileHolding d with
  | none => rfl
  | some a =>
      show (match (below d (u.piles a).faceUp).getLast? with
          | none => some (Sum.inl a)
          | some z => some (Sum.inr z)) =
        (match (below d (v.piles a).faceUp).getLast? with
          | none => some (Sum.inl a)
          | some z => some (Sum.inr z))
      rw [hbelow a (by rw [hhold]; exact hh)]

/-- A placement keeps the seat of every card other than its mover. -/
theorem seatOf_putCard_of_ne {st : State} {c d : Card} {b : Base}
    (hcp : st.canPlace c b = true) (hd : d ≠ c) :
    seatOf (st.putCard c b) d = seatOf st d := by
  have main : seatOf st d = seatOf (st.putCard c b) d := by
    cases b with
    | inl a0 =>
        obtain ⟨hemp, -⟩ := canPlace_inl hcp
        obtain ⟨-, hfa⟩ := (Pile.isEmpty_eq _).mp hemp
        rw [putCard_eq_inl]
        refine seatOf_congr_hold (u := st) (v := st.setPile a0 ⟨[], [c]⟩) ?_ ?_
        · refine pileHolding_congr_mem (u := st) (v := st.setPile a0 ⟨[], [c]⟩)
            (fun j => ?_)
          by_cases hja : j = a0
          · rw [hja, setPile_piles_self, hfa]
            exact ⟨fun h => False.elim (absurd h List.not_mem_nil), fun h => False.elim (hd (List.mem_singleton.mp h))⟩
          · rw [setPile_piles_ne hja]
        · intro a hhold
          by_cases haa : a = a0
          · rw [haa] at hhold ⊢
            have h1 : d ∈ (st.piles a0).faceUp := pileHolding_mem hhold
            exact False.elim (absurd h1 (by rw [hfa]; exact List.not_mem_nil))
          · rw [setPile_piles_ne haa]
    | inr z =>
        obtain ⟨k, hk, hfit⟩ := canPlace_inr hcp
        rw [putCard_inr_eq hk]
        refine seatOf_congr_hold (u := st)
          (v := st.setPile k { st.piles k with
            faceUp := (st.piles k).faceUp ++ [c] }) ?_ ?_
        · refine pileHolding_congr_mem (u := st)
            (v := st.setPile k { st.piles k with
              faceUp := (st.piles k).faceUp ++ [c] }) (fun j => ?_)
          by_cases hjk : j = k
          · rw [hjk, setPile_piles_self]
            refine ⟨List.mem_append_left _ , ?_⟩
            intro h
            rcases List.mem_append.mp h with h' | h'
            · exact h'
            · rw [List.mem_singleton] at h'
              exact False.elim (absurd h' hd)
          · rw [setPile_piles_ne hjk]
        · intro a hhold
          by_cases hak : a = k
          · have h1 : d ∈ (st.piles a).faceUp := pileHolding_mem hhold
            rw [hak] at h1 ⊢
            rw [setPile_piles_self]
            exact (tfc_below_mem_append_left (c := d) (A := (st.piles k).faceUp)
              (B := [c]) h1).symm
          · rw [setPile_piles_ne hak]
  exact main.symm

/-- **A PULL KEEPS THE SEAT OF EVERY OTHER CARD VERBATIM.**  A pull appends
(via `putCard`) its own card to one pile's face-up run — or seats it on an
empty pile — so no other card changes pile and no other card's `below`-list
changes. -/
theorem seatOf_pull_of_ne {A' B : State} {c d : Card} {b : Base}
    (hstep : State.step A' (Move.foundToTab c b) = some B) (hd : d ≠ c) :
    seatOf B d = seatOf A' d := by
  obtain ⟨c', htop, hc'c, hcp, heq⟩ := step_foundToTab_inv hstep
  rw [heq]
  have hcp' : (A'.setFound c.suit (chop (A'.found c.suit))).canPlace c b = true :=
    hcp
  rw [seatOf_putCard_of_ne hcp' hd]
  exact seatOf_congr_piles rfl d

/-! ## §2. The cover transfers back over the free tail -/

/-- **A PAIR MEMBER S-LIVE AT THE LANDING IS VANILLA-RAISABLE THERE.**  If both
twins of a pair are vanilla-raisable at the bottom `F` and `y` (a member) is
S-live at the pull landing `B`, then `y` is vanilla-raisable at `B` already:
a cover at `B` would fit `y`, and the seat invariant
(`Both.seat_inv_play`, twin-blind) keeps the cover card on `{y, y.twin}`
down the free tail — so one twin would be covered at `F`. -/
theorem raisable_at_landing {B F : State} {post : List Move} {y : Card}
    (hB : B.WF) (hF : F.WF) (hpost : ShufflePlayW B post F)
    (hfree : ∀ m ∈ post, ValleyElim.FreeMove m)
    (hS : CanRaiseS B y) (hy : CanRaise F y) (hyt : CanRaise F y.twin) :
    CanRaise B y := by
  rcases canRaise_or_covered hB hS with hcan | ⟨e, hseat⟩
  · exact hcan
  · exfalso
    have hfit0 : canSitOn e y = true := LiveKit.canSitOn_of_seat hB hseat
    have hfit : canSitOn e y.twin.twin = true := by
      rw [card_twin_twin]; exact hfit0
    have hnk : e.rank ≠ Rank.king := Both.rank_ne_king_of_fit hfit
    have hinv :=
      Both.seat_inv_play (d := e) (c := y.twin) hfit hnk hpost hB
        (Or.inl (by rw [card_twin_twin]; exact hseat)) hfree
    rw [card_twin_twin] at hinv
    rcases hinv with hs | hs
    · exact not_canRaise_of_covered hF ⟨e, hs⟩ hy
    · exact not_canRaise_of_covered hF ⟨e, hs⟩ hyt

/-! ## §3. The pull's own twin: vanilla raisability transfers back -/

/-- **THE PULLED CARD'S TWIN KEEPS ITS VANILLA LICENCE BACKWARDS.**  The pull
of `c` touches only `c`'s suit's foundation and appends `c` to one pile; the
suit, the pile top and the seat of `c.twin` are untouched.  (The
`pre = []` `Both.top_case_false` is this row plus saturation.) -/
theorem canRaise_twin_prev_of_pull {A' B : State} {c : Card} {b : Base}
    (hA' : A'.WF) (hstep : State.step A' (Move.foundToTab c b) = some B)
    (hcan : CanRaise B c.twin) : CanRaise A' c.twin := by
  obtain ⟨hnextB, a, hpodB, hseatB⟩ := hcan
  have htopB : lastOf (B.piles a).faceUp = some c.twin := (pileOfTop_top hpodB).2
  have hnextA : A'.nextUp c.twin = true :=
    Both.nextUp_of_step_pull_ne_suit hstep (Suit.twin_ne c.suit) hnextB
  have hface := Both.pull_faceUp_cases hstep a
  have hhid := Both.pull_hidden_eq hstep a
  rcases hface with hface | hface
  · refine ⟨hnextA, a, ?_, ?_⟩
    · exact (pileOfTop_eq_some_iff hA').mpr (by
        show lastOf (A'.piles a).faceUp = some c.twin
        rw [← hface]; exact htopB)
    · rcases hseatB with h | ⟨hh, hk⟩
      · exact Or.inl (by rw [← hface]; exact h)
      · exact Or.inr ⟨by rw [← hhid]; exact hh, hk⟩
  · exfalso
    have hlast : lastOf (B.piles a).faceUp = some c := by
      rw [hface]
      exact lastOf_snoc
    exact _root_.card_twin_ne c (Option.some.inj (htopB.symm.trans hlast))

/-! ## §4. The descent step: the corner is pinned at the pre-split state -/

/-- **THE PULL ORIGIN CARRIES A RAISABLE TWIN.**  At a split whose bottom has a
both-raisable live pair, the state `A'` just before the split's pull has
`c.twin` vanilla-raisable.  (Existential form: `A'`, `B` are the ones the
split's own pull exposes.) -/
theorem pull_origin_twin_raisable_exists
    {u v : State} {ρ : List Move} {F : State} {left right : List Move}
    {c d : Card} {b : Base} {pre post tail : List Move}
    (h : SplitHyp u v ρ F left right c d b pre post tail) {x : Card}
    (hl : TwinLivePair F x) (hcx : CanRaise F x) (hct : CanRaise F x.twin) :
    ∃ A' B : State, ShufflePlayW u pre A' ∧
      State.step A' (Move.foundToTab c b) = some B ∧ CanRaise A' c.twin := by
  obtain ⟨hF, hSc, -, -⟩ := splitHyp_green h
  obtain ⟨A', B, hpre, hrev, hstep, hpost, hA', hB, hcanB, hfree⟩ :=
    TailHead.split_pull_landing h
  -- the pair IS the split's twin pair
  have hcanFc : CanRaise F c := by
    rcases (hl c).mp hSc with h1 | h1
    · rw [h1]; exact hcx
    · rw [h1]; exact hct
  have hcanFt : CanRaise F c.twin := by
    rcases (hl c).mp hSc with h1 | h1
    · rw [h1]; exact hct
    · rw [h1, card_twin_twin]; exact hcx
  have hcanBt : CanRaise B c.twin :=
    raisable_at_landing hB hF hpost hfree
      ((Bridge.canRaiseS_of_free_play_iff hpost hfree hB c.twin).mpr
        (CanRaiseS.now c.twin hcanFt))
      hcanFt (by rw [card_twin_twin]; exact hcanFc)
  exact ⟨A', B, hpre, hstep, canRaise_twin_prev_of_pull hA' hstep hcanBt⟩

/-- **THE DESCENT STEP (named form).**  Same content, read at a chosen `A'`
reached by the split's prefix `pre`. -/
theorem pull_origin_twin_raisable
    {u v : State} {ρ : List Move} {F : State} {left right : List Move}
    {c d : Card} {b : Base} {pre post tail : List Move}
    (h : SplitHyp u v ρ F left right c d b pre post tail) {x : Card}
    (hl : TwinLivePair F x) (hcx : CanRaise F x) (hct : CanRaise F x.twin)
    {A' B : State} (hpre : ShufflePlayW u pre A')
    (hstep : State.step A' (Move.foundToTab c b) = some B) :
    CanRaise A' c.twin := by
  obtain ⟨A0, B0, hpre0, hstep0, hcan0⟩ :=
    pull_origin_twin_raisable_exists h hl hcx hct
  have hA : A0 = A' := Option.some.inj
    ((Walk_run (fun st m => reversibleAtW st m) hpre0).symm.trans
      (Walk_run (fun st m => reversibleAtW st m) hpre))
  subst hA
  rw [hstep0] at hstep
  have hB : B0 = B := Option.some.inj hstep
  subst hB
  exact hcan0

/-! ## §5. The residual, and both `pre ≠ []` lanes -/

/-- **`PullOriginTwinBlocked` — THE RESIDUAL.**  At the state `A'` just before
a valley split's pull `pull c b`, the pulled card's twin is not
vanilla-raisable.  A local rank/seat statement at the pre-split state (the
pull is legal there, so `c` tops `c`'s foundation; the clause says `c.twin` is
not next-up-and-pile-topped-and-seated).  It mentions neither the bottom `F`,
nor the raise card `d`, nor raisability at `F`. -/
def PullOriginTwinBlocked : Prop :=
  ∀ (u v : State) (ρ : List Move) (F : State) (left right : List Move)
    (c d : Card) (b : Base) (pre post tail : List Move),
    SplitHyp u v ρ F left right c d b pre post tail →
    ∀ (A' B : State), ShufflePlayW u pre A' →
      State.step A' (Move.foundToTab c b) = some B →
      ¬ CanRaise A' c.twin

/-- **THE PULL-HEADED LANE FROM THE RESIDUAL.** -/
theorem bottomNotBothPullPre_of_originBlock (hres : PullOriginTwinBlocked) :
    Both.BottomNotBothPullPre := by
  intro u v ρ F left right c d b pre post tail h _ x hF hl hboth
  obtain ⟨hcx, hct⟩ := hboth
  obtain ⟨A', B, hpre, hstep, hcan⟩ :=
    pull_origin_twin_raisable_exists h hl hcx hct
  exact hres u v ρ F left right c d b pre post tail h A' B hpre hstep hcan

/-- **THE FREE-HEADED LANE FROM THE RESIDUAL.** -/
theorem bottomNotBothFreePre_of_originBlock (hres : PullOriginTwinBlocked) :
    Both.BottomNotBothFreePre := by
  intro u v ρ F left right c d b pre post tail h _ x hF hl hboth
  obtain ⟨hcx, hct⟩ := hboth
  obtain ⟨A', B, hpre, hstep, hcan⟩ :=
    pull_origin_twin_raisable_exists h hl hcx hct
  exact hres u v ρ F left right c d b pre post tail h A' B hpre hstep hcan

/-- **THE `pre = []` LANE FROM THE RESIDUAL** — the cross-check that the
descent step already contains the whole `pre = []` corner (no seat arithmetic
over the free tail of the split's own pull is needed at `pre = []`: the origin
`u` is saturated). -/
theorem bottomNotBothRaisableNil_of_originBlock (hres : PullOriginTwinBlocked) :
    Both.BottomNotBothRaisableNil := by
  intro u v ρ F left right c d b post tail h x hF hl hboth
  obtain ⟨hcx, hct⟩ := hboth
  obtain ⟨A', B, hpre, hstep, hcan⟩ :=
    pull_origin_twin_raisable_exists h hl hcx hct
  cases hpre
  exact absurd (CanRaiseS.now c.twin hcan)
    (h.2.1 c.twin)

/-- **THE GLOBAL STATEMENT FROM `nilPre` + THE RESIDUAL.** -/
theorem bottomNotBoth_of_originBlock (hres : PullOriginTwinBlocked) :
    Pin.BottomNotBothRaisable :=
  Both.bottomNotBoth_of_parts Both.bottomNotBothRaisableNil
    (bottomNotBothPullPre_of_originBlock hres)
    (bottomNotBothFreePre_of_originBlock hres)

/-- **THE CAMPAIGN CHAIN FROM THE RESIDUAL.** -/
theorem satDifferForkWF_of_originBlock (hres : PullOriginTwinBlocked)
    (hl : SplitLivePair) (hmin : ValleyElim.ShortestPlayExists) :
    SatDifferForkWF :=
  Both.satDifferForkWF_of_parts Both.bottomNotBothRaisableNil
    (bottomNotBothPullPre_of_originBlock hres)
    (bottomNotBothFreePre_of_originBlock hres) hl hmin

/-! ## §6. The residual is proved on free prefixes -/

/-- **FREE PREFIXES SATISFY THE RESIDUAL.**  A free prefix transports the
S-licence in both directions (`Bridge.canRaiseS_of_free_play_iff`), so
`CanRaise A' c.twin` at the pre-split state would be S-liveness at the
saturated origin `u`.  In particular the residual's only live content is the
*pull-headed* prefix. -/
theorem not_canRaise_origin_of_freePre
    {u v : State} {ρ : List Move} {F : State} {left right : List Move}
    {c d : Card} {b : Base} {pre post tail : List Move}
    (h : SplitHyp u v ρ F left right c d b pre post tail)
    (hfreepre : ∀ m ∈ pre, ValleyElim.FreeMove m)
    {A' B : State} (hpre : ShufflePlayW u pre A')
    (hstep : State.step A' (Move.foundToTab c b) = some B) :
    ¬ CanRaise A' c.twin := by
  obtain ⟨huwf, hsu, -, -, -, -, -, -, -, -, -, -⟩ := h
  intro hcan
  exact hsu c.twin
    ((Bridge.canRaiseS_of_free_play_iff hpre hfreepre huwf c.twin).mpr
      (CanRaiseS.now c.twin hcan))

/-- The residual restricted to free prefixes (a theorem, so the free-prefix
half of both `pre ≠ []` lanes is closed). -/
def PullOriginTwinBlockedFreePre : Prop :=
  ∀ (u v : State) (ρ : List Move) (F : State) (left right : List Move)
    (c d : Card) (b : Base) (pre post tail : List Move),
    SplitHyp u v ρ F left right c d b pre post tail →
    (∀ m ∈ pre, ValleyElim.FreeMove m) →
    ∀ (A' B : State), ShufflePlayW u pre A' →
      State.step A' (Move.foundToTab c b) = some B →
      ¬ CanRaise A' c.twin

theorem pullOriginTwinBlockedFreePre : PullOriginTwinBlockedFreePre :=
  fun u v ρ F left right c d b pre post tail h hfree A' B hpre hstep =>
    not_canRaise_origin_of_freePre h hfree hpre hstep

/-! ## §7. The residual is a SPLIT-level statement, not a pull-level one -/

/-- **THE RESIDUAL IS NOT ABOUT PULL LETTERS ALONE.**  At the `gAce`
gadget's pre-pull state `gAceMid` the pull `AD → 2C` fires and the pulled
card's twin `AH` IS vanilla-raisable (`Both.gAceMid_canRaise_AH`).  So
`PullOriginTwinBlocked` cannot be strengthened to "every legal pull": it is
genuinely a statement about *valley splits* of shortest witness plays.  (The
gadget is outside the split gate because `gAce` has no legal free letter —
`Both.gAce_not_nil_bottom`,
`Pin.gAceMid_not_saturated`.) -/
theorem originTwinBlocked_not_local :
    ∃ B, State.step Pin.gAceMid (Move.foundToTab Pin.AD (Sum.inr Pin.C2)) = some B ∧
      CanRaise Pin.gAceMid Pin.AD.twin := by
  obtain ⟨B, hstep, -, -, -⟩ := Pin.gAceMid_landing_both
  exact ⟨B, hstep, Both.gAceMid_canRaise_AH⟩

end BP

/-! ## §8. A card-level form of the residual at a one-pull prefix -/

namespace BP

open SplitKit

/-- **AT A ONE-PULL PREFIX THE RESIDUAL IS `c ≠ z.twin`.**  If the split's
prefix is the single pull `pull z bz`, then `c.twin` raisable at the pre-split
state `A'` (which IS the landing of `pull z bz`) forces `c = z.twin`: the
split's pull card is the twin of the head pull's card.  The three exclusions:

* `c.twin = z` gives card equality outright;
* `c.twin = z.twin` gives `c = z`, but `z` is on the tableau at `A'` while the
  split's pull needs `c` on the foundation (`wf_pile_found_ne`);
* `c.twin` S-live at the saturated origin `u` is impossible.

This is the `gAce` configuration (`pull z ; pull z.twin`), so the residual's
remaining content at `|pre| = 1` is exactly the gadget's card pattern — plus
the (unused here) split structure that excludes it. -/
theorem single_pull_origin_card
    {u v : State} {ρ : List Move} {F : State} {left right : List Move}
    {c d : Card} {b : Base} {post tail : List Move} {z : Card} {bz : Base}
    (h : SplitHyp u v ρ F left right c d b [Move.foundToTab z bz] post tail)
    {B : State} (hstepZ : State.step u (Move.foundToTab z bz) = some B)
    (hcan : CanRaise B c.twin) : c = z.twin := by
  obtain ⟨A', B2, hpre, hrev, hstepC, hpost, hA', hB2, hcanB, hfree⟩ :=
    TailHead.split_pull_landing h
  have huwf : u.WF := h.1
  have hsu : SSaturated u := h.2.1
  -- `A'` IS the landing of the head pull
  have hstepZA : State.step u (Move.foundToTab z bz) = some A' := by
    cases hpre with
    | cons hrevZ hstepZ' hnil => cases hnil; exact hstepZ'
  have hBA : B = A' := Option.some.inj (hstepZ.symm.trans hstepZA)
  subst hBA
  rcases LandKit.canRaiseS_pull_creation huwf hstepZA
    (CanRaiseS.now c.twin hcan) with h1 | h1 | h1
  · simpa [card_twin_twin] using congrArg Card.twin h1
  · -- `c = z`: impossible, the head pull put `z` on the tableau, the split's
    -- pull needs `c` on the foundation
    exfalso
    have hcz : c = z := by
      simpa [card_twin_twin] using congrArg Card.twin h1
    obtain ⟨c', htop, hc'c, hcp, heq⟩ := step_foundToTab_inv hstepC
    have hcfound : c ∈ B.found c.suit := by
      have htop' : B.foundTop c.suit = some c := by
        rw [hc'c] at htop
        exact htop
      exact lastOf_mem htop'
    have hseat : seatOf B c ≠ none := by
      intro hnone
      have hz : seatOf B z = some bz := Bridge.seatOf_mover_of_pull huwf hstepZA
      rw [← hcz] at hz
      rw [hnone] at hz
      exact absurd hz (by simp)
    have hhold : B.pileHolding c ≠ none := fun hh => hseat (tfc_seatOf_none hh)
    obtain ⟨a, ha⟩ := option_some_of_ne_none hhold
    have hmem : c ∈ (B.piles a).faceUp := pileHolding_mem ha
    exact wf_pile_found_ne hA'
      (by simpa [pileZone] using List.mem_append_right _ hmem) hcfound
  · exact absurd h1 (hsu c.twin)

/-! ## §9. The residual on a raise-free prefix is a CARD statement -/

/-- **ON A RAISE-FREE PREFIX, A RAISABLE TWIN AT `A'` IS A PREFIX PULL OF `c`
OR `c.twin`.**  `PinRight.live_subset_pulls_of_raiseFree` applied to the
prefix, then the twin arithmetic. -/
theorem exists_prePull_of_canRaise_origin
    {u v : State} {ρ : List Move} {F : State} {left right : List Move}
    {c d : Card} {b : Base} {pre post tail : List Move}
    (h : SplitHyp u v ρ F left right c d b pre post tail)
    (hnor : ∀ m ∈ pre, ¬ Bubble.IsRaise m)
    {A' B : State} (hpre : ShufflePlayW u pre A')
    (hstep : State.step A' (Move.foundToTab c b) = some B)
    (hcan : CanRaise A' c.twin) :
    ∃ (z : Card) (bz : Base), Move.foundToTab z bz ∈ pre ∧ (z = c ∨ z = c.twin) := by
  have huwf : u.WF := h.1
  have hsu : SSaturated u := h.2.1
  obtain ⟨z, bz, hmem, hz⟩ :=
    PinRight.live_subset_pulls_of_raiseFree hpre huwf hsu hnor
      (CanRaiseS.now c.twin hcan)
  refine ⟨z, bz, hmem, ?_⟩
  rcases hz with h1 | h1
  · exact Or.inr h1.symm
  · refine Or.inl ?_
    have h2 := congrArg Card.twin h1
    simpa [card_twin_twin] using h2.symm

/-- **`NoTwinPullInPre` — the residual in card vocabulary.**  A split's
raise-free prefix never pulls the split's pull card `c` or its twin
`c.twin`.  No rung, no licence, no bottom coordinate. -/
def NoTwinPullInPre : Prop :=
  ∀ (u v : State) (ρ : List Move) (F : State) (left right : List Move)
    (c d : Card) (b : Base) (pre post tail : List Move),
    SplitHyp u v ρ F left right c d b pre post tail →
    (∀ m ∈ pre, ¬ Bubble.IsRaise m) →
    ¬ ∃ (z : Card) (bz : Base),
      Move.foundToTab z bz ∈ pre ∧ (z = c ∨ z = c.twin)

/-- **THE RESIDUAL ON RAISE-FREE PREFIXES, FROM THE CARD STATEMENT.** -/
theorem originBlock_of_noTwinPull (h : NoTwinPullInPre) :
    ∀ (u v : State) (ρ : List Move) (F : State) (left right : List Move)
      (c d : Card) (b : Base) (pre post tail : List Move),
      SplitHyp u v ρ F left right c d b pre post tail →
      (∀ m ∈ pre, ¬ Bubble.IsRaise m) →
      ∀ (A' B : State), ShufflePlayW u pre A' →
        State.step A' (Move.foundToTab c b) = some B → ¬ CanRaise A' c.twin := by
  intro u v ρ F left right c d b pre post tail hs hnor A' B hpre hstep hcan
  exact h u v ρ F left right c d b pre post tail hs hnor
    (exists_prePull_of_canRaise_origin hs hnor hpre hstep hcan)

/-- **THE RESIDUAL'S CARD CONTENT IS THE TREE'S `NoPrePullRaise`.**  With the
campaign's mechanism `d = c.twin` (`SplitTwin`), "the raise card is no
`PrePullPair` of the prefix" (`PinRight.NoPrePullRaise`) is exactly "the
prefix pulls neither `c` nor `c.twin`". -/
theorem prePullPair_iff_twinPull {pre : List Move} {c d : Card} (hd : d = c.twin) :
    PinRight.PrePullPair pre d ↔
      ∃ (z : Card) (bz : Base),
        Move.foundToTab z bz ∈ pre ∧ (z = c ∨ z = c.twin) := by
  constructor
  · rintro ⟨z, bz, hmem, hdz | hdz⟩
    · exact ⟨z, bz, hmem, Or.inr (by rw [← hdz]; exact hd)⟩
    · refine ⟨z, bz, hmem, Or.inl ?_⟩
      have h1 : c.twin = z.twin := hd.symm.trans hdz
      have h2 := congrArg Card.twin h1
      simpa [card_twin_twin] using h2.symm
  · rintro ⟨z, bz, hmem, hzc | hzc⟩
    · exact ⟨z, bz, hmem, Or.inr (by rw [hd, hzc])⟩
    · exact ⟨z, bz, hmem, Or.inl (by rw [hd, hzc])⟩

end BP

/-! ## §7. Axiom battery -/

#print axioms BP.pileHolding_congr_mem
#print axioms BP.seatOf_congr_hold
#print axioms BP.seatOf_pull_of_ne
#print axioms BP.raisable_at_landing
#print axioms BP.canRaise_twin_prev_of_pull
#print axioms BP.pull_origin_twin_raisable_exists
#print axioms BP.pull_origin_twin_raisable
#print axioms BP.bottomNotBothPullPre_of_originBlock
#print axioms BP.bottomNotBothFreePre_of_originBlock
#print axioms BP.bottomNotBothRaisableNil_of_originBlock
#print axioms BP.bottomNotBoth_of_originBlock
#print axioms BP.satDifferForkWF_of_originBlock
#print axioms BP.not_canRaise_origin_of_freePre
#print axioms BP.pullOriginTwinBlockedFreePre
#print axioms BP.originTwinBlocked_not_local
#print axioms BP.single_pull_origin_card
#print axioms BP.exists_prePull_of_canRaise_origin
#print axioms BP.originBlock_of_noTwinPull
#print axioms BP.prePullPair_iff_twinPull




